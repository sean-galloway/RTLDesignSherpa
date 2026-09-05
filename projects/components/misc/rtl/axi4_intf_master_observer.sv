// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axi4_intf_master_observer
// Purpose: Inline AXI-interface observer -- a pass-through meter for any AXI4
//          master interface, with its own APB configuration.
//
// Was named axi4_dma_observer, which was a misnomer: the header already said
// "DMA-agnostic" and nothing in it is DMA-specific. It observes an AXI
// interface, and aggregates AXIS and CORE monbus traffic alongside. The name
// mattered once the block moved to projects/components/misc/ to be shared --
// a block called *_dma_observer does not read as something a memory
// controller would reach for.
//
//   Drop in between an AXI4-master DMA (any number of read / write
//   master ports) and the fabric. Each (read, write) port pair gets
//   wrapped by axi4_master_rd_mon / axi4_master_wr_mon in pass-through
//   mode. All N monbus streams are merged by monbus_arbiter and fed
//   into monbus_axil4_axi4_group, exposing:
//
//     - s_axil_*  : slave-read port for the host CPU's IRQ drain
//                   (3-beat-per-record slicing)
//     - m_axi_*   : AXI4-burst master-write port for bulk-trace
//                   capture to a memory ring
//     - irq_out   : asserted whenever the err FIFO has any entries
//
//   The DMA under test is not modified -- the observer sits inline
//   on its AXI external pins. Same clock domain on both sides.
//
//   Each tap (axi4_master_{rd,wr}_mon) is a pure observer: it watches
//   its AXI4 bus and emits a monbus packet on every event match. All
//   filtering of which packets ultimately reach the err FIFO or the
//   write FIFO is done by the central monbus_group filter (one set of
//   cfg_<proto>_*_mask + cfg_<proto>_err_select inputs at the observer
//   top, fed directly into u_group). The per-leaf cfg_axi_*_mask
//   inputs on each tap are tied to 0 ("don't pre-filter at the leaf")
//   so the central filter is the single point of control.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_intf_master_observer
    import monitor_common_pkg::*;
#(
    // ---------- Tap counts ----------
    parameter int NUM_RD_PORTS       = 1,
    parameter int NUM_WR_PORTS       = 1,

    // ---------- DMA-side AXI widths (shared by all tap ports) ----------
    parameter int ADDR_WIDTH         = 32,
    parameter int DATA_WIDTH         = 128,
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXI_USER_WIDTH     = 1,

    // ---------- Observer dump-port (m_axi_*) sizing ----------
    parameter int OBS_AXI_ID_WIDTH   = 4,        // master-write id for dumps
    parameter int MAX_BURST_BEATS    = 64,       // 1..256 (256 is AXI4 max)

    // ---------- Group config ----------
    parameter int FIFO_DEPTH_ERR        = 64,
    parameter int FIFO_DEPTH_WRITE      = 96,    // beats
    parameter int FLUSH_TIMEOUT_CYCLES  = 1024,
    parameter int USE_COMPRESSION       = 0,

    // ---- Monbus egress: which dump master this instance exposes ----------
    // 0 = monbus_axil4_axi4_group -> AXI4 burst master (m_axi_*), for a
    //     memory-ring dump.
    // 1 = monbus_axil4_axil4_group -> AXIL write master (m_axil_*), which is
    //     what the STREAM harness's tally path consumes.
    // BOTH port sets are always declared so the module's port list does not
    // change with the parameter; the unused set is driven to zero. A port
    // list that moved with a parameter would make every instantiation
    // parameter-order-sensitive, which is a worse trap than a few tied
    // outputs.
    parameter bit EGRESS_AXIL           = 1'b0,

    // ---------- Per-leaf monitor config ----------
    parameter int MAX_TRANSACTIONS      = 64,

    // ---- Transaction-table banking (see axi_monitor_trans_mgr) -----------
    // MAX_TRANSACTIONS is the TOTAL slots; the CAM is generated NUM_BANKS
    // times at MAX_TRANSACTIONS/NUM_BANKS each, because timing scales with
    // the depth of ONE cam, not the total (16 deep measured WNS +1.018 ns,
    // 40 deep -25.183 ns). Banking is by ID, so per-ID concurrency is
    // capped by the BANK depth:
    //     MAX_TRANSACTIONS/NUM_BANKS >= (IDs per bank) * (outstanding per ID)
    // 8 channels x 8 outstanding over 4 banks => 64/4 = 16 per bank.
    parameter int NUM_BANKS             = 4,
    // Required when a WRITE monitor is banked -- the WID-less select is not
    // ID-matched otherwise and double-counts across banks. The trans_mgr
    // refuses to elaborate without it.
    parameter bit USE_WDATA_ORDER_Q     = 1'b1,
    // Monitor timer LUT frequency, in MHz. counter_freq_invariant divides BY
    // this to produce the 1 us tick that every monitor timeout is expressed
    // in, so it MUST track the real aclk: a table built for 100 running on a
    // 90 MHz clock stretches every timeout by 11% with no other symptom.
    // The *_mon wrapper maps it onto both CFI bounds, so every LUT entry is
    // this frequency and the tick is exact for any cfg_freq_sel.
    parameter int ACLK_MHZ              = 100,
    // CFI LUT bounds. Unlike the *_mon default (MIN==MAX==ACLK_MHZ, one
    // degenerate entry), the observers carry a REAL range so cfg_freq_sel
    // actually selects. LINEAR gives freq[i] = MIN + (MAX-MIN)*i/(N-1);
    // 60..135 over 16 entries is exactly 60+5i, so 80/90/100/120 all land
    // on integer indices (4/6/8/12) and stay tick-exact.
    parameter int CFI_MIN_FREQ_MHZ      = 60,
    parameter int CFI_MAX_FREQ_MHZ      = 135,
    // Drives cfg_monitor_enable on the embedded axi4_master_{rd,wr}_mon taps.
    //
    // This was hardwired to 1'b1, and that is what made the observer a
    // THROTTLE: those wrappers gate the command channel on
    //   ready = core_ready & (block_ready | ~cfg_monitor_enable)
    // so an enabled tap backpressures the DMA at MAX_TRANSACTIONS. In a perf
    // build that is self-defeating -- the instrument becomes the bottleneck and
    // reports its own limit as the DMA's throughput.
    //
    // Set 0 for measurement-only builds: no blocking, no CAM pressure, and the
    // latency histograms and bus meters (which live OUTSIDE this gate) keep
    // counting. Set 1 when the error/completion monbus stream is wanted, and
    // size MAX_TRANSACTIONS for the real concurrency if you do.
    parameter bit ENABLE_MON_TAPS       = 1'b1,

    // ---- Track a SLICE of the channels on a shared bus ---------------------
    // Four of these can snoop one 8-channel bus in parallel, each owning two
    // channels, so each transaction table needs 2 x outstanding = 16 entries
    // instead of the 72 a single observer would need. 16 is the size measured
    // at WNS +1.018 ns; 40 was already at -25.183 ns, so one big table is not
    // an option here.
    //
    // ONE instance, N taps, ONE APB config window.
    //
    // The taps are already a generate loop over NUM_RD_PORTS/NUM_WR_PORTS and
    // every meter/histogram output is an array indexed by tap, all behind a
    // single s_apb_* slave. So four "observers" on a shared bus are four TAPS
    // in one instance -- not four instances. Four instances would each need
    // their own bridge slave window (obs_apb is one 4 KB port at 0x0019_0000),
    // which means regenerating the bridge and re-laying-out an address map the
    // host tools hardcode. Four taps need none of that.
    //
    // NUM_CHANNELS is PER TAP. Tap gi owns
    //   [CH_BASE + gi*NUM_CHANNELS, CH_BASE + (gi+1)*NUM_CHANNELS)
    // so NUM_RD_PORTS=4, NUM_CHANNELS=2 covers 8 channels of one bus with four
    // 16-entry tables instead of one 72-entry table.
    //
    // CH_BASE is the first channel (= first AXI ID) the instance owns overall.
    // Defaults keep the whole-bus behavior.
    //
    // Two separate things have to happen, and doing only the first is the trap:
    //   1. the transaction tables must not allocate for other IDs
    //      -> observer-local only. This must NOT reach axi_monitor_base:
    //         that module is shared by every monitor in the repo, including
    //         stream_core's in-core ones, and a filter there changes blocks
    //         that have nothing to do with slicing an observer across a bus.
    //   2. the latency histograms index by cmd_id[CW-1:0], so with
    //      NUM_CHANNELS=2 (CW=1) channels 0,2,4,6 would all alias onto slot 0.
    //      Narrowing NUM_CHANNELS alone does NOT select two channels, it folds
    //      eight into two. The id must be REBASED before it is used as an
    //      index -- see obs_rd_hist_id below.
    // Explicit, not inferred from CH_BASE: instance 0 of a four-way split has
    // CH_BASE=0 and still must filter, so "CH_BASE != 0" would silently leave
    // that one instance tracking the whole bus.
    parameter bit ENABLE_ID_SLICE       = 1'b0,
    parameter int CH_BASE               = 0,

    parameter logic [7:0] UNIT_ID       = 8'h10, // distinguishes this observer's packets

    // ---------- Per-tap monitor cone enables ----------
    // Default = perf-only, the FPGA-trimmed footprint that fits the xc7a100t
    // (each non-perf cone pulls in a transaction CAM + reporter and dominates
    // the observer's LUT cost -- see commit f4b1a732). Instances that need the
    // completion/error monbus dump path (e.g. the standalone observer unit
    // test) override the relevant enable to 1'b1. Synthesized characterization
    // instances keep the perf-only defaults, so the FPGA footprint is unchanged.
    // Address-range checker depth. 0 compiles the checker OUT of the monitors,
    // which is why ADDR_MATCH packets were unreachable regardless of config.
    // The ADDR_RANGE* registers exist either way; OBS_CAPS0 reports the truth.
    // APB config window width, VISIBLE at the top on purpose. The regblock's
    // own cpuif width is NOT a second knob: it is DERIVED below from the
    // generated package, so it tracks the register map automatically. A
    // hand-written cast here is what made every register at or above 0x080
    // silently alias onto a low one -- see CPUIF_ADDR_WIDTH.
    parameter int APB_ADDR_WIDTH             = 12,
    parameter int N_ADDR_RANGES              = 0,
    // Per-range flavour, forwarded to the monitors' address checker: a bit
    // SET makes that range ERROR-flavoured, so a MISS emits
    // Error/ADDR_RANGE (0x0D); a bit CLEAR leaves it DEBUG, so a HIT emits
    // AddrMatch (0x01). N_ADDR_RANGES was forwarded and this was not, so
    // every range silently took the all-DEBUG default and Error/ADDR_RANGE
    // was unreachable no matter how the ranges were programmed.
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]
                  ADDR_RANGE_IS_ERROR        = '0,
    parameter bit TAP_ENABLE_ERROR_LOGIC     = 1'b0,
    parameter bit TAP_ENABLE_TIMEOUT_LOGIC   = 1'b0,
    parameter bit TAP_ENABLE_COMPL_LOGIC     = 1'b0,
    parameter bit TAP_ENABLE_THRESHOLD_LOGIC = 1'b0,
    parameter bit TAP_ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit TAP_ENABLE_DEBUG_LOGIC     = 1'b0,

    // ---------- axi_bus_meter integration ----------
    parameter bit ENABLE_BUS_METER      = 1'b1,  // 0 = omit meters, tie outputs to 0
    // 1 = derive write per-channel attribution from awid via an internal AW->W
    // order tracker (no obs_wr_active_ch_* sideband needed; valid when AW leads
    // W, the common case). 0 = use the explicit obs_wr_active_ch_* sideband.
    parameter bit WR_CH_FROM_AWID       = 1'b0,
    parameter int NUM_CHANNELS          = 1,     // 1 = aggregate only (no per-channel buckets)
    parameter int CW                    = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,

    // ---------- axi_perf_latency_hist integration (RFC Stage E option 2 / E.3) ----------
    parameter bit ENABLE_LATENCY_HIST   = 1'b1,  // 0 = omit histograms, tie outputs to 0
    parameter int HIST_NUM_BINS         = 16,    // log2 latency bins: bin b = [2^b, 2^(b+1))
    parameter int HIST_MAX_OUTSTANDING  = 8,     // per-channel timestamp FIFO depth
    parameter int HIST_BINW             = (HIST_NUM_BINS > 1) ? $clog2(HIST_NUM_BINS) : 1
) (
    input  logic                                                aclk,
    input  logic                                                aresetn,

    // ---- APB configuration slave ------------------------------------------
    // The observer owns its configuration rather than taking 29 cfg_* ports
    // that the harness tied off. Same chain stream_top_ch8 uses:
    //   flat APB -> apb4_slave -> peakrdl_to_cmdrsp -> obs_regs_top
    // This is what lets ONE harness source serve both builds: the harness no
    // longer has to know this block's internals to instantiate it.
    input  logic                          s_apb_psel,
    input  logic                          s_apb_penable,
    output logic                          s_apb_pready,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_paddr,
    input  logic                          s_apb_pwrite,
    input  logic [31:0]                   s_apb_pwdata,
    input  logic [3:0]                    s_apb_pstrb,
    output logic [31:0]                   s_apb_prdata,
    output logic                          s_apb_pslverr,
    // Synchronous clear for ALL CAMs in the observer: the compressor template
    // CAM (+ stats) in the monbus group and every tap's transaction CAM. Pulse
    // when idle to reset compression stats / unstick stale entries.
    input  logic                                                cam_clear,

    // ================================================================
    // OBSERVED AXI4 READ PORTS -- INPUTS ONLY.
    //
    // This block OBSERVES. Every AXI4 signal below is an input, including
    // both halves of each handshake, because a snoop watches the wire and
    // needs valid AND ready to know a beat happened. Nothing here is
    // driven back onto the observed bus, so attaching this block cannot
    // change the transaction stream it is measuring.
    // See vault/handbook/design/observers-do-not-drive.md.
    // ================================================================
    input  logic [NUM_RD_PORTS-1:0][AXI_ID_WIDTH-1:0]       obs_rd_arid,
    input  logic [NUM_RD_PORTS-1:0][ADDR_WIDTH-1:0]         obs_rd_araddr,
    input  logic [NUM_RD_PORTS-1:0][7:0]                    obs_rd_arlen,
    input  logic [NUM_RD_PORTS-1:0][2:0]                    obs_rd_arsize,
    input  logic [NUM_RD_PORTS-1:0][1:0]                    obs_rd_arburst,
    input  logic [NUM_RD_PORTS-1:0]                         obs_rd_arlock,
    input  logic [NUM_RD_PORTS-1:0][3:0]                    obs_rd_arcache,
    input  logic [NUM_RD_PORTS-1:0][2:0]                    obs_rd_arprot,
    input  logic [NUM_RD_PORTS-1:0][3:0]                    obs_rd_arqos,
    input  logic [NUM_RD_PORTS-1:0][3:0]                    obs_rd_arregion,
    input  logic [NUM_RD_PORTS-1:0][AXI_USER_WIDTH-1:0]     obs_rd_aruser,
    input  logic [NUM_RD_PORTS-1:0]                         obs_rd_arvalid,
    input  logic [NUM_RD_PORTS-1:0]                         obs_rd_arready,
    // R channel
    input  logic [NUM_RD_PORTS-1:0][AXI_ID_WIDTH-1:0]       obs_rd_rid,
    input  logic [NUM_RD_PORTS-1:0][DATA_WIDTH-1:0]         obs_rd_rdata,
    input  logic [NUM_RD_PORTS-1:0][1:0]                    obs_rd_rresp,
    input  logic [NUM_RD_PORTS-1:0]                         obs_rd_rlast,
    input  logic [NUM_RD_PORTS-1:0][AXI_USER_WIDTH-1:0]     obs_rd_ruser,
    input  logic [NUM_RD_PORTS-1:0]                         obs_rd_rvalid,
    input  logic [NUM_RD_PORTS-1:0]                         obs_rd_rready,

    // ================================================================
    // OBSERVED AXI4 WRITE PORTS -- INPUTS ONLY (same rule as above).
    // ================================================================
    input  logic [NUM_WR_PORTS-1:0][AXI_ID_WIDTH-1:0]       obs_wr_awid,
    input  logic [NUM_WR_PORTS-1:0][ADDR_WIDTH-1:0]         obs_wr_awaddr,
    input  logic [NUM_WR_PORTS-1:0][7:0]                    obs_wr_awlen,
    input  logic [NUM_WR_PORTS-1:0][2:0]                    obs_wr_awsize,
    input  logic [NUM_WR_PORTS-1:0][1:0]                    obs_wr_awburst,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_awlock,
    input  logic [NUM_WR_PORTS-1:0][3:0]                    obs_wr_awcache,
    input  logic [NUM_WR_PORTS-1:0][2:0]                    obs_wr_awprot,
    input  logic [NUM_WR_PORTS-1:0][3:0]                    obs_wr_awqos,
    input  logic [NUM_WR_PORTS-1:0][3:0]                    obs_wr_awregion,
    input  logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]     obs_wr_awuser,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_awvalid,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_awready,
    // W channel
    input  logic [NUM_WR_PORTS-1:0][DATA_WIDTH-1:0]         obs_wr_wdata,
    input  logic [NUM_WR_PORTS-1:0][DATA_WIDTH/8-1:0]       obs_wr_wstrb,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_wlast,
    input  logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]     obs_wr_wuser,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_wvalid,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_wready,
    // B channel
    input  logic [NUM_WR_PORTS-1:0][AXI_ID_WIDTH-1:0]       obs_wr_bid,
    input  logic [NUM_WR_PORTS-1:0][1:0]                    obs_wr_bresp,
    input  logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]     obs_wr_buser,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_bvalid,
    input  logic [NUM_WR_PORTS-1:0]                         obs_wr_bready,

    // ================================================================
    // Observability outputs
    // ================================================================

    // CPU-side err FIFO drain (AXIL slave-read)
    input  logic                                                s_axil_arvalid,
    output logic                                                s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]                               s_axil_araddr,
    input  logic [2:0]                                          s_axil_arprot,
    output logic                                                s_axil_rvalid,
    input  logic                                                s_axil_rready,
    output logic [63:0]                                         s_axil_rdata,
    output logic [1:0]                                          s_axil_rresp,

    // Bulk-trace dump (AXI4 burst master-write)
    output logic [OBS_AXI_ID_WIDTH-1:0]                         m_axi_awid,
    output logic [ADDR_WIDTH-1:0]                               m_axi_awaddr,
    output logic [7:0]                                          m_axi_awlen,
    output logic [2:0]                                          m_axi_awsize,
    output logic [1:0]                                          m_axi_awburst,
    output logic                                                m_axi_awlock,
    output logic [3:0]                                          m_axi_awcache,
    output logic [2:0]                                          m_axi_awprot,
    output logic [3:0]                                          m_axi_awqos,
    output logic [3:0]                                          m_axi_awregion,
    output logic                                                m_axi_awuser,
    output logic                                                m_axi_awvalid,
    input  logic                                                m_axi_awready,
    output logic [63:0]                                         m_axi_wdata,
    output logic [7:0]                                          m_axi_wstrb,
    output logic                                                m_axi_wlast,
    output logic                                                m_axi_wuser,
    output logic                                                m_axi_wvalid,
    input  logic                                                m_axi_wready,
    input  logic [OBS_AXI_ID_WIDTH-1:0]                         m_axi_bid,
    input  logic [1:0]                                          m_axi_bresp,
    input  logic                                                m_axi_buser,
    input  logic                                                m_axi_bvalid,
    output logic                                                m_axi_bready,

    // ---- AXIL dump master (EGRESS_AXIL=1). Zero when unused. ----------
    output logic                                                m_axil_awvalid,
    input  logic                                                m_axil_awready,
    output logic [ADDR_WIDTH-1:0]                               m_axil_awaddr,
    output logic [2:0]                                          m_axil_awprot,
    output logic                                                m_axil_wvalid,
    input  logic                                                m_axil_wready,
    output logic [63:0]                                         m_axil_wdata,
    output logic [7:0]                                          m_axil_wstrb,
    input  logic                                                m_axil_bvalid,
    output logic                                                m_axil_bready,
    input  logic [1:0]                                          m_axil_bresp,

    // IRQ
    output logic                                                irq_out,

    // ================================================================
    // Runtime config (drives the monbus_group's central filter)
    // ================================================================
    //
    // The taps (axi4_master_{rd,wr}_mon) observe their AXI4 buses and
    // emit a monbus packet on every match. Filtering of what reaches
    // the err FIFO / write FIFO happens **here**, inside monbus_group:
    //   cfg_<proto>_pkt_mask[i]        = 1 -> drop packets where pkt_type==i
    //   cfg_<proto>_err_select[i]      = 1 -> route those packets to err FIFO
    //                                          instead of write FIFO
    //   cfg_<proto>_<event>_mask[i]    = 1 -> drop on event_code==i within
    //                                          the named event class
    //
    // A monbus packet's protocol field selects which set the filter
    // applies. The taps in this observer always emit protocol=AXI, so
    // the AXIS / CORE sets only do work for an upstream caller that
    // arbitrates this observer's monbus together with an AXIS or CORE
    // monitor source -- but they're real filter inputs either way.

    // ----- AXI -----

    // ================================================================
    // axi_bus_meter inputs (optional; safe to tie off if ENABLE_BUS_METER=0)
    // ================================================================

    // One-cycle synchronous pulse clears all bucket counters and overflow
    // stickies. Held-high also works (the meter's accumulators stay
    // pinned at 0).
    input  logic                                                i_meter_clear,
    // Hold high to pause every bucket counter (the measurement window
    // closes). Held low for free-running measurement.
    input  logic                                                i_meter_freeze,

    // ---------- Read-side rid -> channel-id mapping ----------
    //
    // Runtime signal-list mapping. For each rd port and each logical
    // channel index `ch` in [0..NUM_CHANNELS-1]:
    //   cfg_rd_rid_per_channel[port][ch]        = rid value channel `ch` uses
    //   cfg_rd_rid_per_channel_valid[port][ch]  = 1 if that entry is in use
    // The bus-meter for that port matches the current rid against this
    // table; the first valid match's `ch` index becomes i_channel_id.
    // No match (or all-invalid) -> the cycle is not attributed (aggregate
    // counters still tick).
    input  logic [AXI_ID_WIDTH-1:0] cfg_rd_rid_per_channel       [NUM_RD_PORTS][NUM_CHANNELS],
    input  logic                    cfg_rd_rid_per_channel_valid [NUM_RD_PORTS][NUM_CHANNELS],

    // ---------- Write-side channel-active sideband (optional) ----------
    //
    // AXI4 W beats carry no AXI ID; per-channel attribution needs a
    // sideband from the DMA's W-phase FSM. STREAM's axi_write_engine
    // exposes o_active_channel_id / o_active_channel_valid that wires
    // directly here. DMAs without this output: tie both to 0 (aggregate
    // counters still tick; per-channel buckets stay at 0).
    input  logic [CW-1:0]           obs_wr_active_ch_id          [NUM_WR_PORTS],
    input  logic                    obs_wr_active_ch_valid       [NUM_WR_PORTS]

    // ================================================================
    // axi_bus_meter outputs (one set per monitored port)
    // ================================================================
    // Read-side meters
    // Write-side meters

    // ================================================================
    // axi_perf_latency_hist (RFC Stage E.3) — per-port latency histograms
    // ================================================================
    // Indexed readout: the selectors below are shared across all ports
    // (drive one {metric, bin}, read each port's count/total separately).
    // Reads expose two metrics (i_hist_metric: 0 = AR->first-R, 1 = AR->RLAST);
    // writes expose one metric (AW->B; i_hist_metric is ignored for writes).
    // o_*_hist_total is the per-metric transaction count (== burst count).
    // Frozen/cleared in lockstep with the meters (i_meter_clear/i_meter_freeze).

    // Sticky: a latency-timestamp FIFO was full when a command arrived, so at
    // least one sample was lost and the histogram totals READ LOW.
    //
    // This is a STATUS bit, not backpressure. Throttling the command channel
    // would keep the totals exact while changing the traffic being measured
    // which for a performance observer is the worse error -- the instrument
    // must not become the bottleneck. So the observer is sized to track
    // everything the DMA can initiate (NUM_CHANNELS x per-channel outstanding)
    // and this flag exists to say when that sizing is WRONG. Zero means the
    // numbers are trustworthy; one means they undercount and the design is
    // mis-parameterized. Without it, undersizing is indistinguishable from a
    // slower DMA.
);

    // Telemetry, formerly ~27 OUTPUT PORTS. Read through this block's own
    // regblock (OBS_STAT_SEL/OBS_STAT_DATA, OBS_FIFO_STAT, OBS_STICKY,
    // OBS_COMP_STAT*) instead. Fanning them out cost the integrator a
    // tie-off per pin, and a forgotten one is silent.
    logic                        err_fifo_full ;
    logic                        write_fifo_full ;
    logic [15:0]                 err_fifo_count ;
    logic [15:0]                 write_fifo_count ;
    logic [31:0]                 rd_meter_agg_productive [NUM_RD_PORTS];
    logic [31:0]                 rd_meter_agg_backpressure [NUM_RD_PORTS];
    logic [31:0]                 rd_meter_agg_starvation [NUM_RD_PORTS];
    logic [31:0]                 rd_meter_agg_idle [NUM_RD_PORTS];
    logic [15:0]                 rd_meter_ch_productive [NUM_RD_PORTS][NUM_CHANNELS];
    logic [15:0]                 rd_meter_ch_backpressure [NUM_RD_PORTS][NUM_CHANNELS];
    logic [15:0]                 rd_meter_ch_starvation [NUM_RD_PORTS][NUM_CHANNELS];
    logic [15:0]                 rd_meter_ch_idle [NUM_RD_PORTS][NUM_CHANNELS];
    logic [NUM_CHANNELS*4-1:0]   rd_meter_ch_overflow [NUM_RD_PORTS];
    logic [31:0]                 wr_meter_agg_productive [NUM_WR_PORTS];
    logic [31:0]                 wr_meter_agg_backpressure [NUM_WR_PORTS];
    logic [31:0]                 wr_meter_agg_starvation [NUM_WR_PORTS];
    logic [31:0]                 wr_meter_agg_idle [NUM_WR_PORTS];
    logic [15:0]                 wr_meter_ch_productive [NUM_WR_PORTS][NUM_CHANNELS];
    logic [15:0]                 wr_meter_ch_backpressure [NUM_WR_PORTS][NUM_CHANNELS];
    logic [15:0]                 wr_meter_ch_starvation [NUM_WR_PORTS][NUM_CHANNELS];
    logic [15:0]                 wr_meter_ch_idle [NUM_WR_PORTS][NUM_CHANNELS];
    logic [NUM_CHANNELS*4-1:0]   wr_meter_ch_overflow [NUM_WR_PORTS];
    logic [31:0]                 rd_hist_count [NUM_RD_PORTS];
    logic [31:0]                 rd_hist_total [NUM_RD_PORTS];
    logic [31:0]                 wr_hist_count [NUM_WR_PORTS];
    logic [31:0]                 wr_hist_total [NUM_WR_PORTS];
    logic                        o_hist_sample_lost ;



    // Per-tap monitor backpressure. Not a bus signal -- nothing here
    // reaches the observed interface -- but a tap whose table is full
    // stops tracking, so this is the honesty flag for the coverage
    // numbers. See vault/Tasks/amba (AMBA-MONTRACK).
    logic [NUM_RD_PORTS-1:0] obs_rd_block_ready;
    logic [NUM_WR_PORTS-1:0] obs_wr_block_ready;
    // =======================================================================
    // Configuration: APB -> cmd/rsp -> passthrough regblock
    // Same chain as stream_top_ch8 and dma_slave_monitors. No cmdrsp_router:
    // one target behind this APB.
    // =======================================================================
    logic                w_cmd_valid, w_cmd_ready, w_cmd_pwrite;
    logic [11:0]         w_cmd_paddr;
    logic [31:0]         w_cmd_pwdata;
    logic [3:0]          w_cmd_pstrb;
    logic [2:0]          w_cmd_pprot;
    logic                w_rsp_valid, w_rsp_ready, w_rsp_pslverr;
    logic [31:0]         w_rsp_prdata;

    // Regblock cpuif address width, DERIVED from the generated package so it
    // cannot drift from the register map. PeakRDL sizes
    // OBS_REGS_TOP_MIN_ADDR_WIDTH from the RDL span; when a register is added
    // past the current top this widens on its own.
    //
    // It was hardcoded 7'(...) against an 8-bit port. That does not error --
    // it ALIASES: 0x0D0 wraps to 0x50, 0x080 onto AXI_PKT_MASK, 0x084 onto
    // AXI_MASK1, all returning a plausible wrong value. OBS_COMP_STAT0/1 were
    // unreadable from the day they were added and nobody could tell.
    localparam int CPUIF_ADDR_WIDTH = obs_regs_top_pkg::OBS_REGS_TOP_MIN_ADDR_WIDTH;

    apb4_slave #(.ADDR_WIDTH(APB_ADDR_WIDTH), .DATA_WIDTH(32)) u_obs_apb (
        .pclk(aclk), .presetn(aresetn),
        .s_apb_PSEL(s_apb_psel),     .s_apb_PENABLE(s_apb_penable),
        .s_apb_PREADY(s_apb_pready), .s_apb_PADDR(s_apb_paddr),
        .s_apb_PWRITE(s_apb_pwrite), .s_apb_PWDATA(s_apb_pwdata),
        .s_apb_PSTRB(s_apb_pstrb),   .s_apb_PPROT(3'b000),
        .s_apb_PRDATA(s_apb_prdata), .s_apb_PSLVERR(s_apb_pslverr),
        .cmd_valid(w_cmd_valid),   .cmd_ready(w_cmd_ready),
        .cmd_pwrite(w_cmd_pwrite), .cmd_paddr(w_cmd_paddr),
        .cmd_pwdata(w_cmd_pwdata), .cmd_pstrb(w_cmd_pstrb), .cmd_pprot(w_cmd_pprot),
        .rsp_valid(w_rsp_valid),   .rsp_ready(w_rsp_ready),
        .rsp_prdata(w_rsp_prdata), .rsp_pslverr(w_rsp_pslverr)
    );

    logic        w_rb_req, w_rb_req_is_wr, w_rb_stall_wr, w_rb_stall_rd;
    logic        w_rb_rd_ack, w_rb_rd_err, w_rb_wr_ack, w_rb_wr_err;
    logic [APB_ADDR_WIDTH-1:0] w_rb_addr;
    logic [31:0] w_rb_wr_data, w_rb_wr_biten, w_rb_rd_data;

    peakrdl_to_cmdrsp #(.ADDR_WIDTH(APB_ADDR_WIDTH), .DATA_WIDTH(32)) u_obs_adapter (
        .aclk(aclk), .aresetn(aresetn),
        .cmd_valid(w_cmd_valid),   .cmd_ready(w_cmd_ready),
        .cmd_pwrite(w_cmd_pwrite), .cmd_paddr(w_cmd_paddr),
        .cmd_pwdata(w_cmd_pwdata), .cmd_pstrb(w_cmd_pstrb),
        .rsp_valid(w_rsp_valid),   .rsp_ready(w_rsp_ready),
        .rsp_prdata(w_rsp_prdata), .rsp_pslverr(w_rsp_pslverr),
        .regblk_req(w_rb_req),               .regblk_req_is_wr(w_rb_req_is_wr),
        .regblk_addr(w_rb_addr),             .regblk_wr_data(w_rb_wr_data),
        .regblk_wr_biten(w_rb_wr_biten),
        .regblk_req_stall_wr(w_rb_stall_wr), .regblk_req_stall_rd(w_rb_stall_rd),
        .regblk_rd_ack(w_rb_rd_ack),         .regblk_rd_err(w_rb_rd_err),
        .regblk_rd_data(w_rb_rd_data),
        .regblk_wr_ack(w_rb_wr_ack),         .regblk_wr_err(w_rb_wr_err)
    );

    obs_regs_top_pkg::obs_regs_top__out_t hwif;
    // Hardware->software side of the regblock: the telemetry readback.
    // Populated by the OBS_STAT_SEL mux below; zeroed here so every field
    // has exactly one driver and an unpopulated metric reads as 0 rather
    // than X.
    obs_regs_top_pkg::obs_regs_top__in_t hwif_i;

    obs_regs_top u_obs_regs (
        .clk(aclk), .rst(~aresetn),
        .s_cpuif_req(w_rb_req),               .s_cpuif_req_is_wr(w_rb_req_is_wr),
        .s_cpuif_addr(CPUIF_ADDR_WIDTH'(w_rb_addr)),         .s_cpuif_wr_data(w_rb_wr_data),
        .s_cpuif_wr_biten(w_rb_wr_biten),
        .s_cpuif_req_stall_wr(w_rb_stall_wr), .s_cpuif_req_stall_rd(w_rb_stall_rd),
        .s_cpuif_rd_ack(w_rb_rd_ack),         .s_cpuif_rd_err(w_rb_rd_err),
        .s_cpuif_rd_data(w_rb_rd_data),
        .s_cpuif_wr_ack(w_rb_wr_ack),         .s_cpuif_wr_err(w_rb_wr_err),
        .hwif_in(hwif_i),
        .hwif_out(hwif)
    );

    // Local aliases so the body below reads exactly as it did when these were
    // ports -- the config moved, the logic did not.
    logic [15:0] cfg_axi_pkt_mask, cfg_axi_err_select, cfg_axi_error_mask;
    logic [15:0] cfg_axi_timeout_mask, cfg_axi_compl_mask, cfg_axi_thresh_mask;
    logic [15:0] cfg_axi_perf_mask, cfg_axi_addr_mask, cfg_axi_debug_mask;
    logic [15:0] cfg_axis_pkt_mask, cfg_axis_err_select, cfg_axis_error_mask;
    logic [15:0] cfg_axis_timeout_mask, cfg_axis_compl_mask, cfg_axis_channel_mask;
    logic [15:0] cfg_axis_credit_mask, cfg_axis_stream_mask;
    logic [15:0] cfg_core_pkt_mask, cfg_core_err_select, cfg_core_error_mask;
    logic [15:0] cfg_core_timeout_mask, cfg_core_compl_mask, cfg_core_thresh_mask;
    logic [15:0] cfg_core_perf_mask, cfg_core_debug_mask;
    logic [15:0] cfg_flush_watermark;
    logic        cfg_compress_en;
    logic [3:0]  cfg_freq_sel;
    // Monitor tap config -- was 26 constants hardcoded at the instantiations
    // below, reachable from nowhere. Same alias style as the masks above; now
    // fed by MON_CTRL / MON_TIMEOUT / MON_LATENCY / MON_WINDOW / ADDR_RANGE*.
    localparam int OBS_ADDR_RANGES_MAX = 4;

    // The APB window must be able to address the whole regblock. If a future
    // register pushes the map past the window this stops the build instead of
    // aliasing silently, which is the failure this whole block just had.
    initial begin
        if (APB_ADDR_WIDTH < CPUIF_ADDR_WIDTH)
            $error("APB_ADDR_WIDTH=%0d cannot address the %0d-bit regblock map",
                   APB_ADDR_WIDTH, CPUIF_ADDR_WIDTH);
    end
    localparam int NAR = (N_ADDR_RANGES > 0) ? N_ADDR_RANGES : 1;
    logic        cfg_monitor_enable_w, cfg_error_enable_w, cfg_timeout_enable_w;
    logic        cfg_compl_enable_w, cfg_threshold_enable_w, cfg_perf_enable_w;
    logic        cfg_debug_enable_w, cfg_addr_check_enable_w;
    logic [15:0] cfg_timeout_cycles_w;
    logic [31:0] cfg_latency_threshold_w;
    logic [2:0]  cfg_start_event_sel_w, cfg_end_event_sel_w;
    logic        cfg_start_trigger_w, cfg_end_trigger_w, cfg_window_force_close_w;
    logic [OBS_ADDR_RANGES_MAX-1:0][31:0] w_range_low, w_range_high;
    logic [NAR-1:0]                       cfg_addr_range_enable_w;
    logic [NAR-1:0][ADDR_WIDTH-1:0]       cfg_addr_range_low_w, cfg_addr_range_high_w;

    // Build-time LUT index for ACLK_MHZ, inverting the LINEAR mapping
    // freq[i] = MIN + (MAX-MIN)*i/(N-1) with N=16.
    localparam int CFI_ENTRIES    = 16;
    localparam int ACLK_FREQ_SEL  =
        ((ACLK_MHZ - CFI_MIN_FREQ_MHZ) * (CFI_ENTRIES - 1))
        / (CFI_MAX_FREQ_MHZ - CFI_MIN_FREQ_MHZ);

    // The derived index is only tick-exact if ACLK_MHZ lands ON a LUT entry.
    // Off-grid, the timer divides by a neighbouring frequency and every
    // monitor timeout skews -- silently. Fail elaboration instead.
    initial begin
        if (ACLK_MHZ < CFI_MIN_FREQ_MHZ || ACLK_MHZ > CFI_MAX_FREQ_MHZ)
            $error("ACLK_MHZ=%0d outside the observer CFI LUT range %0d..%0d",
                   ACLK_MHZ, CFI_MIN_FREQ_MHZ, CFI_MAX_FREQ_MHZ);
        else if (CFI_MIN_FREQ_MHZ
                 + ((CFI_MAX_FREQ_MHZ - CFI_MIN_FREQ_MHZ) * ACLK_FREQ_SEL)
                   / (CFI_ENTRIES - 1) != ACLK_MHZ)
            $error("ACLK_MHZ=%0d is not on the CFI LUT grid (%0d..%0d/%0d entries); the 1 us tick would be inexact",
                   ACLK_MHZ, CFI_MIN_FREQ_MHZ, CFI_MAX_FREQ_MHZ, CFI_ENTRIES);
    end
    logic [ADDR_WIDTH-1:0] cfg_base_addr, cfg_limit_addr;

    assign cfg_axi_pkt_mask      = hwif.OBS.AXI_PKT_MASK.PKT_MASK.value;
    assign cfg_axi_err_select    = hwif.OBS.AXI_PKT_MASK.ERR_SELECT.value;
    assign cfg_axi_error_mask    = hwif.OBS.AXI_MASK1.ERROR_MASK.value;
    assign cfg_axi_timeout_mask  = hwif.OBS.AXI_MASK1.TIMEOUT_MASK.value;
    assign cfg_axi_compl_mask    = hwif.OBS.AXI_MASK2.COMPL_MASK.value;
    assign cfg_axi_thresh_mask   = hwif.OBS.AXI_MASK2.THRESH_MASK.value;
    assign cfg_axi_perf_mask     = hwif.OBS.AXI_MASK3.PERF_MASK.value;
    assign cfg_axi_addr_mask     = hwif.OBS.AXI_MASK3.ADDR_MASK.value;
    assign cfg_axi_debug_mask    = hwif.OBS.AXI_MASK4.DEBUG_MASK.value;
    assign cfg_axis_pkt_mask     = hwif.OBS.AXIS_PKT_MASK.PKT_MASK.value;
    assign cfg_axis_err_select   = hwif.OBS.AXIS_PKT_MASK.ERR_SELECT.value;
    assign cfg_axis_error_mask   = hwif.OBS.AXIS_MASK1.ERROR_MASK.value;
    assign cfg_axis_timeout_mask = hwif.OBS.AXIS_MASK1.TIMEOUT_MASK.value;
    assign cfg_axis_compl_mask   = hwif.OBS.AXIS_MASK2.COMPL_MASK.value;
    assign cfg_axis_channel_mask = hwif.OBS.AXIS_MASK2.CHANNEL_MASK.value;
    assign cfg_axis_credit_mask  = hwif.OBS.AXIS_MASK3.CREDIT_MASK.value;
    assign cfg_axis_stream_mask  = hwif.OBS.AXIS_MASK3.STREAM_MASK.value;
    assign cfg_core_pkt_mask     = hwif.OBS.CORE_PKT_MASK.PKT_MASK.value;
    assign cfg_core_err_select   = hwif.OBS.CORE_PKT_MASK.ERR_SELECT.value;
    assign cfg_core_error_mask   = hwif.OBS.CORE_MASK1.ERROR_MASK.value;
    assign cfg_core_timeout_mask = hwif.OBS.CORE_MASK1.TIMEOUT_MASK.value;
    assign cfg_core_compl_mask   = hwif.OBS.CORE_MASK2.COMPL_MASK.value;
    assign cfg_core_thresh_mask  = hwif.OBS.CORE_MASK2.THRESH_MASK.value;
    assign cfg_core_perf_mask    = hwif.OBS.CORE_MASK3.PERF_MASK.value;
    assign cfg_core_debug_mask   = hwif.OBS.CORE_MASK3.DEBUG_MASK.value;
    assign cfg_flush_watermark   = hwif.OBS.OBS_CTRL.FLUSH_WATERMARK.value;
    assign cfg_compress_en       = hwif.OBS.OBS_CTRL.COMPRESS_EN.value;
    // Monitor timer LUT index. At reset FREQ_SEL_OVR=0 selects the index
    // DERIVED from ACLK_MHZ, so the 1 us tick is correct for whatever clock
    // this was built at -- a CSR reset value alone could not do that without
    // silently disagreeing with the clock on any non-default build. Software
    // sets FREQ_SEL_OVR to take manual control.
    assign cfg_freq_sel          = hwif.OBS.OBS_CTRL.FREQ_SEL_OVR.value
                                 ? hwif.OBS.OBS_CTRL.FREQ_SEL.value
                                 : ACLK_FREQ_SEL[3:0];
    assign cfg_base_addr         = ADDR_WIDTH'(hwif.OBS.OBS_BASE_ADDR.VALUE.value);
    assign cfg_limit_addr        = ADDR_WIDTH'(hwif.OBS.OBS_LIMIT_ADDR.VALUE.value);

    // ---- Monitor tap runtime config (MON_CTRL / MON_TIMEOUT / MON_LATENCY / MON_WINDOW)
    // MONITOR_EN is ANDed with the build-time arm: a tap that was not armed
    // cannot be armed from software, and a cone that was not built cannot be
    // switched on at all -- OBS_CAPS0 is how software finds that out.
    assign cfg_monitor_enable_w     = ENABLE_MON_TAPS & hwif.OBS.MON_CTRL.MONITOR_EN.value;
    assign cfg_error_enable_w       = hwif.OBS.MON_CTRL.ERROR_EN.value;
    assign cfg_timeout_enable_w     = hwif.OBS.MON_CTRL.TIMEOUT_EN.value;
    assign cfg_compl_enable_w       = hwif.OBS.MON_CTRL.COMPL_EN.value;
    assign cfg_threshold_enable_w   = hwif.OBS.MON_CTRL.THRESHOLD_EN.value;
    assign cfg_perf_enable_w        = hwif.OBS.MON_CTRL.PERF_EN.value;
    assign cfg_debug_enable_w       = hwif.OBS.MON_CTRL.DEBUG_EN.value;
    assign cfg_addr_check_enable_w  = hwif.OBS.MON_CTRL.ADDR_CHECK_EN.value;
    assign cfg_timeout_cycles_w     = hwif.OBS.MON_TIMEOUT.TIMEOUT_CYCLES.value;
    assign cfg_latency_threshold_w  = hwif.OBS.MON_LATENCY.VALUE.value;
    assign cfg_start_event_sel_w    = hwif.OBS.MON_WINDOW.START_EVENT_SEL.value;
    assign cfg_end_event_sel_w      = hwif.OBS.MON_WINDOW.END_EVENT_SEL.value;
    assign cfg_start_trigger_w      = hwif.OBS.MON_WINDOW.START_TRIGGER.value;
    assign cfg_end_trigger_w        = hwif.OBS.MON_WINDOW.END_TRIGGER.value;
    assign cfg_window_force_close_w = hwif.OBS.MON_WINDOW.FORCE_CLOSE.value;

    // ---- Address-range checker. Four register pairs exist on every instance so
    // the map is one shape everywhere; only the first N_ADDR_RANGES are wired,
    // and N_ADDR_RANGES=0 compiles the checker out of the monitors entirely.
    assign w_range_low[0]  = hwif.OBS.ADDR_RANGE0_LOW.VALUE.value;
    assign w_range_high[0] = hwif.OBS.ADDR_RANGE0_HIGH.VALUE.value;
    assign w_range_low[1]  = hwif.OBS.ADDR_RANGE1_LOW.VALUE.value;
    assign w_range_high[1] = hwif.OBS.ADDR_RANGE1_HIGH.VALUE.value;
    assign w_range_low[2]  = hwif.OBS.ADDR_RANGE2_LOW.VALUE.value;
    assign w_range_high[2] = hwif.OBS.ADDR_RANGE2_HIGH.VALUE.value;
    assign w_range_low[3]  = hwif.OBS.ADDR_RANGE3_LOW.VALUE.value;
    assign w_range_high[3] = hwif.OBS.ADDR_RANGE3_HIGH.VALUE.value;

    // genvar, not a for-loop in always_comb: a VARIABLE index into a struct
    // field (hwif.OBS.ADDR_RANGE_CTRL.RANGE_EN.value[r]) put the struct port
    // copy into Verilator's nba_comb scheduling and it then miscompiled the
    // whole hwif_in copy -- `cannot convert ...__in_t to CData` out of g++,
    // with lint clean because lint never runs C++ codegen. Constant indices
    // keep it a plain continuous drive.
    generate
        for (genvar r = 0; r < NAR; r++) begin : g_addr_range
            assign cfg_addr_range_enable_w[r] = hwif.OBS.ADDR_RANGE_CTRL.RANGE_EN.value[r];
            assign cfg_addr_range_low_w[r]    = ADDR_WIDTH'(w_range_low[r]);
            assign cfg_addr_range_high_w[r]   = ADDR_WIDTH'(w_range_high[r]);
        end
    endgenerate

    // Capabilities: what this instance was BUILT with. Read these before
    // concluding anything from a zero counter -- an absent cone reports nothing
    // no matter how it is configured, which looks exactly like a dead datapath.
    // Packed rather than fielded; see the CAPS PACKING note in obs_regs.rdl.
    assign hwif_i.OBS.OBS_CAPS0.VALUE.next = {
        16'h0,                          // [31:16] reserved
        4'(N_ADDR_RANGES),              // [15:12]
        1'b0,                           // [11]    reserved
        ENABLE_ID_SLICE,                // [10]
        EGRESS_AXIL,                    // [9]
        (USE_COMPRESSION != 0),         // [8]
        ENABLE_BUS_METER,               // [7]
        ENABLE_MON_TAPS,                // [6]
        TAP_ENABLE_DEBUG_LOGIC,         // [5]
        TAP_ENABLE_PERF_LOGIC,          // [4]
        TAP_ENABLE_THRESHOLD_LOGIC,     // [3]
        TAP_ENABLE_COMPL_LOGIC,         // [2]
        TAP_ENABLE_TIMEOUT_LOGIC,       // [1]
        TAP_ENABLE_ERROR_LOGIC          // [0]
    };
    assign hwif_i.OBS.OBS_CAPS1.VALUE.next = {
        8'(CH_BASE), 8'(NUM_CHANNELS), 8'(NUM_WR_PORTS), 8'(NUM_RD_PORTS)
    };
    assign hwif_i.OBS.OBS_CAPS2.VALUE.next = {
        8'(ADDR_WIDTH), 8'(NUM_BANKS), 16'(MAX_TRANSACTIONS)
    };


    // =================================================================
    // Local parameters / derived sizes
    // =================================================================
    localparam int NUM_MON_SOURCES = NUM_RD_PORTS + NUM_WR_PORTS;

    // Sanity: monbus_arbiter requires at least one client.
    initial begin
        if (NUM_MON_SOURCES < 1) begin
            $error("axi4_intf_master_observer: NUM_RD_PORTS + NUM_WR_PORTS must be >= 1");
        end
    end

    // =================================================================
    // Free-running timestamp (driven out by monbus_group, looped back
    // into every leaf monitor as i_mon_time)
    // =================================================================
    monbus_timestamp_t                              mon_time_w;

    // =================================================================
    // Per-source monbus streams + arbiter inputs (unpacked arrays as
    // monbus_arbiter expects)
    // =================================================================
    logic                                           mon_valid    [NUM_MON_SOURCES];
    logic                                           mon_ready    [NUM_MON_SOURCES];
    monitor_packet_t                                mon_packet   [NUM_MON_SOURCES];
    monbus_timestamp_t                              mon_ts       [NUM_MON_SOURCES];

    // =================================================================
    // Read-port monitors
    // =================================================================
    genvar gi;
    generate
        for (gi = 0; gi < NUM_RD_PORTS; gi = gi + 1) begin : gen_rd_mon
            axi4_master_rd_mon #(
                .AXI_ID_WIDTH    (AXI_ID_WIDTH),
                .AXI_ADDR_WIDTH  (ADDR_WIDTH),
                .AXI_DATA_WIDTH  (DATA_WIDTH),
                .AXI_USER_WIDTH  (AXI_USER_WIDTH),
                .USE_MONITOR     (1'b1),
                .UNIT_ID         (UNIT_ID),
                .AGENT_ID        ({8'h00, 4'h0, gi[3:0]}),  // RD ports: [3:0]=index, [7:4]=0
                .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
                .ACLK_MHZ        (ACLK_MHZ),
                .CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
                .CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
                .NUM_BANKS       (NUM_BANKS),
                .USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q),
                // Own only this instance's channels: without this every
                // parallel snooper allocates for ALL traffic and the split
                // buys nothing.
                // Observer tap cone enables (default perf-only -- see the
                // TAP_ENABLE_* parameter block for why). Overridable per-instance
                // so the dump-path unit test can enable completions.
                .N_ADDR_RANGES          (N_ADDR_RANGES),
                .ADDR_RANGE_IS_ERROR     (ADDR_RANGE_IS_ERROR),
                .ENABLE_ERROR_LOGIC     (TAP_ENABLE_ERROR_LOGIC),
                .ENABLE_TIMEOUT_LOGIC   (TAP_ENABLE_TIMEOUT_LOGIC),
                .ENABLE_COMPL_LOGIC     (TAP_ENABLE_COMPL_LOGIC),
                .ENABLE_THRESHOLD_LOGIC (TAP_ENABLE_THRESHOLD_LOGIC),
                .ENABLE_PERF_LOGIC      (TAP_ENABLE_PERF_LOGIC),
                .ENABLE_DEBUG_LOGIC     (TAP_ENABLE_DEBUG_LOGIC)
            ) u_rd_mon (
                .aclk    (aclk),
                .aresetn (aresetn),
                .cam_clear (cam_clear),

                // fub side = DMA-facing (pass-through input from DMA)
                .fub_axi_arid(obs_rd_arid[gi]),
                .fub_axi_araddr(obs_rd_araddr[gi]),
                .fub_axi_arlen(obs_rd_arlen[gi]),
                .fub_axi_arsize(obs_rd_arsize[gi]),
                .fub_axi_arburst(obs_rd_arburst[gi]),
                .fub_axi_arlock(obs_rd_arlock[gi]),
                .fub_axi_arcache(obs_rd_arcache[gi]),
                .fub_axi_arprot(obs_rd_arprot[gi]),
                .fub_axi_arqos(obs_rd_arqos[gi]),
                .fub_axi_arregion(obs_rd_arregion[gi]),
                .fub_axi_aruser(obs_rd_aruser[gi]),
                .fub_axi_arvalid(obs_rd_arvalid[gi]),
                .fub_axi_arready(),
                .fub_axi_rid(),
                .fub_axi_rdata(),
                .fub_axi_rresp(),
                .fub_axi_rlast(),
                .fub_axi_ruser(),
                .fub_axi_rvalid(),
                .fub_axi_rready(obs_rd_rready[gi]),

                // m_axi side = fabric-facing
                .m_axi_arid(),
                .m_axi_araddr(),
                .m_axi_arlen(),
                .m_axi_arsize(),
                .m_axi_arburst(),
                .m_axi_arlock(),
                .m_axi_arcache(),
                .m_axi_arprot(),
                .m_axi_arqos(),
                .m_axi_arregion(),
                .m_axi_aruser(),
                .m_axi_arvalid(),
                .m_axi_arready(obs_rd_arready[gi]),
                .m_axi_rid(obs_rd_rid[gi]),
                .m_axi_rdata(obs_rd_rdata[gi]),
                .m_axi_rresp(obs_rd_rresp[gi]),
                .m_axi_rlast(obs_rd_rlast[gi]),
                .m_axi_ruser(obs_rd_ruser[gi]),
                .m_axi_rvalid(obs_rd_rvalid[gi]),
                .m_axi_rready(),

                // Monitor enables (all-on default; expose later if needed)
                .debug_block_ready    (obs_rd_block_ready[gi]),
                .cfg_monitor_enable   (cfg_monitor_enable_w),
                .cfg_error_enable     (cfg_error_enable_w),
                .cfg_timeout_enable   (cfg_timeout_enable_w),
                .cfg_perf_enable      (cfg_perf_enable_w),
                .cfg_compl_enable     (cfg_compl_enable_w),
                .cfg_threshold_enable (cfg_threshold_enable_w),
                .cfg_debug_enable     (cfg_debug_enable_w),
                .cfg_timeout_cycles   (cfg_timeout_cycles_w),
                .cfg_freq_sel         (cfg_freq_sel),
                .cfg_latency_threshold(cfg_latency_threshold_w),

                // Leaf filter masks tied to "let everything through";
                // the monbus_group's central filter does the real work.
                .cfg_axi_pkt_mask    (16'h0000),
                .cfg_axi_err_select  (16'h0000),
                .cfg_axi_error_mask  (16'h0000),
                .cfg_axi_timeout_mask(16'h0000),
                .cfg_axi_compl_mask  (16'h0000),
                .cfg_axi_thresh_mask (16'h0000),
                .cfg_axi_perf_mask   (16'h0000),
                .cfg_axi_addr_mask   (16'h0000),
                .cfg_axi_debug_mask  (16'h0000),

                // Address-range / perf-window: disabled in v1
                .cfg_addr_check_enable (cfg_addr_check_enable_w),
                .cfg_addr_range_enable (cfg_addr_range_enable_w),
                .cfg_addr_range_low    (cfg_addr_range_low_w),
                .cfg_addr_range_high   (cfg_addr_range_high_w),
                .cfg_start_event_sel   (cfg_start_event_sel_w),
                .cfg_end_event_sel     (cfg_end_event_sel_w),
                .cfg_start_trigger     (cfg_start_trigger_w),
                .cfg_end_trigger       (cfg_end_trigger_w),
                .cfg_window_force_close(cfg_window_force_close_w),

                // Free-running timestamp loop-back
                .i_mon_time      (mon_time_w),

                // Monbus output -> arbiter slot
                .monbus_valid    (mon_valid[gi]),
                .monbus_ready    (mon_ready[gi]),
                .monbus_packet   (mon_packet[gi]),
                .monbus_timestamp(mon_ts[gi]),

                /* verilator lint_off PINCONNECTEMPTY */
                .busy                  (),
                .active_transactions   (),
                .error_count           (),
                .transaction_count     (),
                .window_active         (),
                .window_cycles         (),
                .perf_prod_cycles      (),
                .perf_bp_cycles        (),
                .perf_starv_cycles     (),
                .perf_idle_cycles      (),
                .perf_beat_count       (),
                .perf_byte_count       (),
                .perf_burst_count      (),
                .cfg_conflict_error    ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        end
    endgenerate

    // =================================================================
    // Write-port monitors
    // =================================================================
    generate
        for (gi = 0; gi < NUM_WR_PORTS; gi = gi + 1) begin : gen_wr_mon
            axi4_master_wr_mon #(
                .AXI_ID_WIDTH    (AXI_ID_WIDTH),
                .AXI_ADDR_WIDTH  (ADDR_WIDTH),
                .AXI_DATA_WIDTH  (DATA_WIDTH),
                .AXI_USER_WIDTH  (AXI_USER_WIDTH),
                .USE_MONITOR     (1'b1),
                .UNIT_ID         (UNIT_ID),
                .AGENT_ID        ({8'h00, 4'h1, gi[3:0]}),  // WR ports: [3:0]=idx, [7:4]=1
                .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
                .ACLK_MHZ        (ACLK_MHZ),
                .CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
                .CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
                .NUM_BANKS       (NUM_BANKS),
                .USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q),
                // Own only this instance's channels: without this every
                // parallel snooper allocates for ALL traffic and the split
                // buys nothing.
                // Observer tap cone enables (default perf-only -- see the
                // TAP_ENABLE_* parameter block). Overridable per-instance so the
                // dump-path unit test can enable completions.
                .N_ADDR_RANGES          (N_ADDR_RANGES),
                .ADDR_RANGE_IS_ERROR     (ADDR_RANGE_IS_ERROR),
                .ENABLE_ERROR_LOGIC     (TAP_ENABLE_ERROR_LOGIC),
                .ENABLE_TIMEOUT_LOGIC   (TAP_ENABLE_TIMEOUT_LOGIC),
                .ENABLE_COMPL_LOGIC     (TAP_ENABLE_COMPL_LOGIC),
                .ENABLE_THRESHOLD_LOGIC (TAP_ENABLE_THRESHOLD_LOGIC),
                .ENABLE_PERF_LOGIC      (TAP_ENABLE_PERF_LOGIC),
                .ENABLE_DEBUG_LOGIC     (TAP_ENABLE_DEBUG_LOGIC)
            ) u_wr_mon (
                .aclk    (aclk),
                .aresetn (aresetn),
                .cam_clear (cam_clear),

                .fub_axi_awid(obs_wr_awid[gi]),
                .fub_axi_awaddr(obs_wr_awaddr[gi]),
                .fub_axi_awlen(obs_wr_awlen[gi]),
                .fub_axi_awsize(obs_wr_awsize[gi]),
                .fub_axi_awburst(obs_wr_awburst[gi]),
                .fub_axi_awlock(obs_wr_awlock[gi]),
                .fub_axi_awcache(obs_wr_awcache[gi]),
                .fub_axi_awprot(obs_wr_awprot[gi]),
                .fub_axi_awqos(obs_wr_awqos[gi]),
                .fub_axi_awregion(obs_wr_awregion[gi]),
                .fub_axi_awuser(obs_wr_awuser[gi]),
                .fub_axi_awvalid(obs_wr_awvalid[gi]),
                .fub_axi_awready(),
                .fub_axi_wdata(obs_wr_wdata[gi]),
                .fub_axi_wstrb(obs_wr_wstrb[gi]),
                .fub_axi_wlast(obs_wr_wlast[gi]),
                .fub_axi_wuser(obs_wr_wuser[gi]),
                .fub_axi_wvalid(obs_wr_wvalid[gi]),
                .fub_axi_wready(),
                .fub_axi_bid(),
                .fub_axi_bresp(),
                .fub_axi_buser(),
                .fub_axi_bvalid(),
                .fub_axi_bready(obs_wr_bready[gi]),

                .m_axi_awid(),
                .m_axi_awaddr(),
                .m_axi_awlen(),
                .m_axi_awsize(),
                .m_axi_awburst(),
                .m_axi_awlock(),
                .m_axi_awcache(),
                .m_axi_awprot(),
                .m_axi_awqos(),
                .m_axi_awregion(),
                .m_axi_awuser(),
                .m_axi_awvalid(),
                .m_axi_awready(obs_wr_awready[gi]),
                .m_axi_wdata(),
                .m_axi_wstrb(),
                .m_axi_wlast(),
                .m_axi_wuser(),
                .m_axi_wvalid(),
                .m_axi_wready(obs_wr_wready[gi]),
                .m_axi_bid(obs_wr_bid[gi]),
                .m_axi_bresp(obs_wr_bresp[gi]),
                .m_axi_buser(obs_wr_buser[gi]),
                .m_axi_bvalid(obs_wr_bvalid[gi]),
                .m_axi_bready(),

                .debug_block_ready    (obs_wr_block_ready[gi]),
                .cfg_monitor_enable   (cfg_monitor_enable_w),
                .cfg_error_enable     (cfg_error_enable_w),
                .cfg_timeout_enable   (cfg_timeout_enable_w),
                .cfg_perf_enable      (cfg_perf_enable_w),
                .cfg_compl_enable     (cfg_compl_enable_w),
                .cfg_threshold_enable (cfg_threshold_enable_w),
                .cfg_debug_enable     (cfg_debug_enable_w),
                .cfg_timeout_cycles   (cfg_timeout_cycles_w),
                .cfg_freq_sel         (cfg_freq_sel),
                .cfg_latency_threshold(cfg_latency_threshold_w),

                .cfg_axi_pkt_mask    (16'h0000),
                .cfg_axi_err_select  (16'h0000),
                .cfg_axi_error_mask  (16'h0000),
                .cfg_axi_timeout_mask(16'h0000),
                .cfg_axi_compl_mask  (16'h0000),
                .cfg_axi_thresh_mask (16'h0000),
                .cfg_axi_perf_mask   (16'h0000),
                .cfg_axi_addr_mask   (16'h0000),
                .cfg_axi_debug_mask  (16'h0000),

                .cfg_addr_check_enable (cfg_addr_check_enable_w),
                .cfg_addr_range_enable (cfg_addr_range_enable_w),
                .cfg_addr_range_low    (cfg_addr_range_low_w),
                .cfg_addr_range_high   (cfg_addr_range_high_w),
                .cfg_start_event_sel   (cfg_start_event_sel_w),
                .cfg_end_event_sel     (cfg_end_event_sel_w),
                .cfg_start_trigger     (cfg_start_trigger_w),
                .cfg_end_trigger       (cfg_end_trigger_w),
                .cfg_window_force_close(cfg_window_force_close_w),

                .i_mon_time      (mon_time_w),

                .monbus_valid    (mon_valid[NUM_RD_PORTS + gi]),
                .monbus_ready    (mon_ready[NUM_RD_PORTS + gi]),
                .monbus_packet   (mon_packet[NUM_RD_PORTS + gi]),
                .monbus_timestamp(mon_ts[NUM_RD_PORTS + gi]),

                /* verilator lint_off PINCONNECTEMPTY */
                .busy                  (),
                .active_transactions   (),
                .error_count           (),
                .transaction_count     (),
                .window_active         (),
                .window_cycles         (),
                .perf_prod_cycles      (),
                .perf_bp_cycles        (),
                .perf_starv_cycles     (),
                .perf_idle_cycles      (),
                .perf_beat_count       (),
                .perf_byte_count       (),
                .perf_burst_count      (),
                .cfg_conflict_error    ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        end
    endgenerate

    // =================================================================
    // Aggregate all monbus sources via monbus_arbiter
    // =================================================================
    logic                arb_monbus_valid;
    logic                arb_monbus_ready;
    monitor_packet_t     arb_monbus_packet;
    monbus_timestamp_t   arb_monbus_timestamp;

    monbus_arbiter #(
        .CLIENTS            (NUM_MON_SOURCES),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_arbiter (
        .axi_aclk            (aclk),
        .axi_aresetn         (aresetn),
        .block_arb           (1'b0),
        .monbus_valid_in     (mon_valid),
        .monbus_ready_in     (mon_ready),
        .monbus_packet_in    (mon_packet),
        .monbus_timestamp_in (mon_ts),
        .monbus_valid        (arb_monbus_valid),
        .monbus_ready        (arb_monbus_ready),
        .monbus_packet       (arb_monbus_packet),
        .monbus_timestamp    (arb_monbus_timestamp),
        /* verilator lint_off PINCONNECTEMPTY */
        .grant_valid         (),
        .grant               (),
        .grant_id            (),
        .last_grant          ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // =================================================================
    // Output stage: monbus_axil4_axi4_group
    //   - AXIL slave-read for CPU IRQ drain
    //   - AXI4 burst master-write for memory-ring dump
    // =================================================================
    // Compressor telemetry, captured from the monbus group rather than
    // left unconnected -- it is readable through OBS_COMP_STAT* now.
    logic [15:0] w_comp_stat_tier1_a;
    logic [15:0] w_comp_stat_tier1_b;
    logic [15:0] w_comp_stat_tier1_c;
    logic [15:0] w_comp_stat_tier0;
    logic [15:0] w_comp_stat_cam_miss;
    logic [15:0] w_comp_stat_delta_ts_ovf;
    logic [15:0] w_comp_stat_event_data_ovf;
    logic [15:0] w_comp_stat_ed_delta_ovf;

    // Histogram selection comes from this block's OWN register now, not
    // from input ports the integrator had to drive. That is what makes
    // OBS_STAT_SEL.BIN mean something: select the bin and read it back
    // through one register pair instead of wiggling a port.
    logic                 w_hist_metric_sel;
    logic [HIST_BINW-1:0] w_hist_bin_sel;
    // HIST_METRIC, not IS_WRITE: IS_WRITE picks the read- or write-side
    // histogram ARRAY, while this picks WHICH LATENCY METRIC that
    // histogram reports. Driving it from IS_WRITE left half the
    // histogram unreachable.
    assign w_hist_metric_sel = hwif.OBS.OBS_STAT_SEL.HIST_METRIC.value;
    assign w_hist_bin_sel    = HIST_BINW'(hwif.OBS.OBS_STAT_SEL.BIN.value);

    // Egress select. Exactly one group is built; the other port set is
    // tied off so an unused egress reads as idle rather than floating.
    generate
    if (EGRESS_AXIL) begin : g_egress_axil
        assign m_axi_awid = '0; assign m_axi_awaddr = '0;
        assign m_axi_awlen = '0; assign m_axi_awsize = '0;
        assign m_axi_awburst = '0; assign m_axi_awlock = 1'b0;
        assign m_axi_awcache = '0; assign m_axi_awprot = '0;
        assign m_axi_awqos = '0; assign m_axi_awregion = '0;
        assign m_axi_awuser = '0; assign m_axi_awvalid = 1'b0;
        assign m_axi_wdata = '0; assign m_axi_wstrb = '0;
        assign m_axi_wlast = 1'b0; assign m_axi_wuser = '0;
        assign m_axi_wvalid = 1'b0; assign m_axi_bready = 1'b0;
    monbus_axil4_axil4_group #(
            .FIFO_DEPTH_ERR        (FIFO_DEPTH_ERR),
            .FIFO_DEPTH_WRITE      (FIFO_DEPTH_WRITE),
            .ADDR_WIDTH            (ADDR_WIDTH),
            .FLUSH_TIMEOUT_CYCLES  (FLUSH_TIMEOUT_CYCLES),
            .USE_COMPRESSION       (USE_COMPRESSION)
        ) u_group (
            .axi_aclk         (aclk),
            .axi_aresetn      (aresetn),
            .cam_clear        (cam_clear),
    
            .monbus_valid     (arb_monbus_valid),
            .monbus_ready     (arb_monbus_ready),
            .monbus_packet    (arb_monbus_packet),
            .monbus_timestamp (arb_monbus_timestamp),
    
            .mon_time_out     (mon_time_w),
    
            // AXIL slave-read
            .s_axil_arvalid   (s_axil_arvalid),
            .s_axil_arready   (s_axil_arready),
            .s_axil_araddr    (s_axil_araddr),
            .s_axil_arprot    (s_axil_arprot),
            .s_axil_rvalid    (s_axil_rvalid),
            .s_axil_rready    (s_axil_rready),
            .s_axil_rdata     (s_axil_rdata),
            .s_axil_rresp     (s_axil_rresp),
    
            // AXI4 master-write
    
            .m_axil_awvalid   (m_axil_awvalid),
            .m_axil_awready   (m_axil_awready),
            .m_axil_awaddr    (m_axil_awaddr),
            .m_axil_awprot    (m_axil_awprot),
            .m_axil_wvalid    (m_axil_wvalid),
            .m_axil_wready    (m_axil_wready),
            .m_axil_wdata     (m_axil_wdata),
            .m_axil_wstrb     (m_axil_wstrb),
            .m_axil_bvalid    (m_axil_bvalid),
            .m_axil_bready    (m_axil_bready),
            .m_axil_bresp     (m_axil_bresp),
    
            .irq_out          (irq_out),
    
            // Address window + filter masks (caller-driven)
            .cfg_base_addr        (cfg_base_addr),
            .cfg_limit_addr       (cfg_limit_addr),
            .cfg_flush_watermark  (cfg_flush_watermark),
            .cfg_compress_en      (cfg_compress_en),
    
            .cfg_axi_pkt_mask     (cfg_axi_pkt_mask),
            .cfg_axi_err_select   (cfg_axi_err_select),
            .cfg_axi_error_mask   (cfg_axi_error_mask),
            .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
            .cfg_axi_compl_mask   (cfg_axi_compl_mask),
            .cfg_axi_thresh_mask  (cfg_axi_thresh_mask),
            .cfg_axi_perf_mask    (cfg_axi_perf_mask),
            .cfg_axi_addr_mask    (cfg_axi_addr_mask),
            .cfg_axi_debug_mask   (cfg_axi_debug_mask),
    
            // AXIS / CORE protocol masks: this observer doesn't generate
            // AXIS or CORE packets, so tie all to 0 (no filtering).
            .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
            .cfg_axis_err_select   (cfg_axis_err_select),
            .cfg_axis_error_mask   (cfg_axis_error_mask),
            .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
            .cfg_axis_compl_mask   (cfg_axis_compl_mask),
            .cfg_axis_credit_mask  (cfg_axis_credit_mask),
            .cfg_axis_channel_mask (cfg_axis_channel_mask),
            .cfg_axis_stream_mask  (cfg_axis_stream_mask),
            .cfg_core_pkt_mask     (cfg_core_pkt_mask),
            .cfg_core_err_select   (cfg_core_err_select),
            .cfg_core_error_mask   (cfg_core_error_mask),
            .cfg_core_timeout_mask (cfg_core_timeout_mask),
            .cfg_core_compl_mask   (cfg_core_compl_mask),
            .cfg_core_thresh_mask  (cfg_core_thresh_mask),
            .cfg_core_perf_mask    (cfg_core_perf_mask),
            .cfg_core_debug_mask   (cfg_core_debug_mask),
    
            .err_fifo_full      (err_fifo_full),
            .write_fifo_full    (write_fifo_full),
            .err_fifo_count     (err_fifo_count),
            .write_fifo_count   (write_fifo_count),
    
            /* verilator lint_off PINCONNECTEMPTY */
            .mon_compressor_stat_tier1_a        (w_comp_stat_tier1_a),
            .mon_compressor_stat_tier1_b        (w_comp_stat_tier1_b),
            .mon_compressor_stat_tier1_c        (w_comp_stat_tier1_c),
            .mon_compressor_stat_tier0          (),
            .mon_compressor_stat_cam_miss       (),
            .mon_compressor_stat_delta_ts_ovf   (),
            .mon_compressor_stat_event_data_ovf (),
            .mon_compressor_stat_ed_delta_ovf   ()
            /* verilator lint_on PINCONNECTEMPTY */
        );
    end else begin : g_egress_axi4
        assign m_axil_awvalid = 1'b0; assign m_axil_awaddr = '0;
        assign m_axil_awprot = '0; assign m_axil_wvalid = 1'b0;
        assign m_axil_wdata = '0; assign m_axil_wstrb = '0;
        assign m_axil_bready = 1'b0;
    monbus_axil4_axi4_group #(
            .FIFO_DEPTH_ERR        (FIFO_DEPTH_ERR),
            .FIFO_DEPTH_WRITE      (FIFO_DEPTH_WRITE),
            .ADDR_WIDTH            (ADDR_WIDTH),
            .AXI_ID_WIDTH          (OBS_AXI_ID_WIDTH),
            .AXI_USER_WIDTH        (1),
            .MAX_BURST_BEATS       (MAX_BURST_BEATS),
            .FLUSH_TIMEOUT_CYCLES  (FLUSH_TIMEOUT_CYCLES),
            .USE_COMPRESSION       (USE_COMPRESSION)
        ) u_group (
            .axi_aclk         (aclk),
            .axi_aresetn      (aresetn),
            .cam_clear        (cam_clear),
    
            .monbus_valid     (arb_monbus_valid),
            .monbus_ready     (arb_monbus_ready),
            .monbus_packet    (arb_monbus_packet),
            .monbus_timestamp (arb_monbus_timestamp),
    
            .mon_time_out     (mon_time_w),
    
            // AXIL slave-read
            .s_axil_arvalid   (s_axil_arvalid),
            .s_axil_arready   (s_axil_arready),
            .s_axil_araddr    (s_axil_araddr),
            .s_axil_arprot    (s_axil_arprot),
            .s_axil_rvalid    (s_axil_rvalid),
            .s_axil_rready    (s_axil_rready),
            .s_axil_rdata     (s_axil_rdata),
            .s_axil_rresp     (s_axil_rresp),
    
            // AXI4 master-write
            .m_axi_awid       (m_axi_awid),
            .m_axi_awaddr     (m_axi_awaddr),
            .m_axi_awlen      (m_axi_awlen),
            .m_axi_awsize     (m_axi_awsize),
            .m_axi_awburst    (m_axi_awburst),
            .m_axi_awlock     (m_axi_awlock),
            .m_axi_awcache    (m_axi_awcache),
            .m_axi_awprot     (m_axi_awprot),
            .m_axi_awqos      (m_axi_awqos),
            .m_axi_awregion   (m_axi_awregion),
            .m_axi_awuser     (m_axi_awuser),
            .m_axi_awvalid    (m_axi_awvalid),
            .m_axi_awready    (m_axi_awready),
            .m_axi_wdata      (m_axi_wdata),
            .m_axi_wstrb      (m_axi_wstrb),
            .m_axi_wlast      (m_axi_wlast),
            .m_axi_wuser      (m_axi_wuser),
            .m_axi_wvalid     (m_axi_wvalid),
            .m_axi_wready     (m_axi_wready),
            .m_axi_bid        (m_axi_bid),
            .m_axi_bresp      (m_axi_bresp),
            .m_axi_buser      (m_axi_buser),
            .m_axi_bvalid     (m_axi_bvalid),
            .m_axi_bready     (m_axi_bready),
    
            .irq_out          (irq_out),
    
            // Address window + filter masks (caller-driven)
            .cfg_base_addr        (cfg_base_addr),
            .cfg_limit_addr       (cfg_limit_addr),
            .cfg_flush_watermark  (cfg_flush_watermark),
            .cfg_compress_en      (cfg_compress_en),
    
            .cfg_axi_pkt_mask     (cfg_axi_pkt_mask),
            .cfg_axi_err_select   (cfg_axi_err_select),
            .cfg_axi_error_mask   (cfg_axi_error_mask),
            .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
            .cfg_axi_compl_mask   (cfg_axi_compl_mask),
            .cfg_axi_thresh_mask  (cfg_axi_thresh_mask),
            .cfg_axi_perf_mask    (cfg_axi_perf_mask),
            .cfg_axi_addr_mask    (cfg_axi_addr_mask),
            .cfg_axi_debug_mask   (cfg_axi_debug_mask),
    
            // AXIS / CORE protocol masks: this observer doesn't generate
            // AXIS or CORE packets, so tie all to 0 (no filtering).
            .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
            .cfg_axis_err_select   (cfg_axis_err_select),
            .cfg_axis_error_mask   (cfg_axis_error_mask),
            .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
            .cfg_axis_compl_mask   (cfg_axis_compl_mask),
            .cfg_axis_credit_mask  (cfg_axis_credit_mask),
            .cfg_axis_channel_mask (cfg_axis_channel_mask),
            .cfg_axis_stream_mask  (cfg_axis_stream_mask),
            .cfg_core_pkt_mask     (cfg_core_pkt_mask),
            .cfg_core_err_select   (cfg_core_err_select),
            .cfg_core_error_mask   (cfg_core_error_mask),
            .cfg_core_timeout_mask (cfg_core_timeout_mask),
            .cfg_core_compl_mask   (cfg_core_compl_mask),
            .cfg_core_thresh_mask  (cfg_core_thresh_mask),
            .cfg_core_perf_mask    (cfg_core_perf_mask),
            .cfg_core_debug_mask   (cfg_core_debug_mask),
    
            .err_fifo_full      (err_fifo_full),
            .write_fifo_full    (write_fifo_full),
            .err_fifo_count     (err_fifo_count),
            .write_fifo_count   (write_fifo_count),
    
            /* verilator lint_off PINCONNECTEMPTY */
            .mon_compressor_stat_tier1_a        (w_comp_stat_tier1_a),
            .mon_compressor_stat_tier1_b        (w_comp_stat_tier1_b),
            .mon_compressor_stat_tier1_c        (w_comp_stat_tier1_c),
            .mon_compressor_stat_tier0          (),
            .mon_compressor_stat_cam_miss       (),
            .mon_compressor_stat_delta_ts_ovf   (),
            .mon_compressor_stat_event_data_ovf (),
            .mon_compressor_stat_ed_delta_ovf   ()
            /* verilator lint_on PINCONNECTEMPTY */
        );
    end
    endgenerate


    // =================================================================
    // axi_bus_meter per-port instantiations
    //
    //   - One meter per rd port (snoops the fabric-side R handshake).
    //     i_channel_id comes from a priority-encoded rid lookup against
    //     cfg_rd_rid_per_channel[port][*]. i_channel_valid = rvalid AND
    //     (any entry matched).
    //
    //   - One meter per wr port (snoops the fabric-side W handshake).
    //     i_channel_id / i_channel_valid come straight from the optional
    //     DMA sideband inputs.
    //
    //   - ENABLE_BUS_METER=0 skips instantiation; all meter outputs tied
    //     to 0.
    // =================================================================
    genvar mi, ci;
    generate
        if (ENABLE_BUS_METER) begin : gen_meters

            // ---------- Read-side meters ----------
            for (mi = 0; mi < NUM_RD_PORTS; mi = mi + 1) begin : gen_rd_meter
                // rid -> channel-id priority-encoded lookup
                logic [CW-1:0]           rd_ch_id;
                logic                    rd_ch_match;
                logic [NUM_CHANNELS-1:0] rd_hit_mask;

                always_comb begin
                    for (int c = 0; c < NUM_CHANNELS; c = c + 1) begin
                        rd_hit_mask[c] = cfg_rd_rid_per_channel_valid[mi][c]
                                      && (obs_rd_rid[mi] == cfg_rd_rid_per_channel[mi][c]);
                    end
                    // Priority-encode: lowest-index matching channel wins
                    rd_ch_id    = '0;
                    rd_ch_match = 1'b0;
                    for (int c = 0; c < NUM_CHANNELS; c = c + 1) begin
                        if (!rd_ch_match && rd_hit_mask[c]) begin
                            rd_ch_id    = c[CW-1:0];
                            rd_ch_match = 1'b1;
                        end
                    end
                end

                axi_bus_meter #(
                    .NUM_CHANNELS (NUM_CHANNELS)
                ) u_rd_meter (
                    .aclk             (aclk),
                    .aresetn          (aresetn),
                    .i_clear          (i_meter_clear),
                    .i_freeze         (i_meter_freeze),
                    // Snoop the fabric-side R handshake. (Equivalent to
                    // dma-side post-skid since the wrappers don't drop
                    // beats.)
                    .i_valid          (obs_rd_rvalid[mi]),
                    .i_ready          (obs_rd_rready[mi]),
                    // rid is only meaningful when rvalid; gate the channel
                    // attribution accordingly. rd_ch_match additionally
                    // requires a matching entry in the rid->ch map.
                    .i_channel_id     (rd_ch_id),
                    .i_channel_valid  (obs_rd_rvalid[mi] && rd_ch_match),
                    .o_agg_productive   (rd_meter_agg_productive[mi]),
                    .o_agg_backpressure (rd_meter_agg_backpressure[mi]),
                    .o_agg_starvation   (rd_meter_agg_starvation[mi]),
                    .o_agg_idle         (rd_meter_agg_idle[mi]),
                    .o_ch_productive    (rd_meter_ch_productive[mi]),
                    .o_ch_backpressure  (rd_meter_ch_backpressure[mi]),
                    .o_ch_starvation    (rd_meter_ch_starvation[mi]),
                    .o_ch_idle          (rd_meter_ch_idle[mi]),
                    .o_ch_overflow      (rd_meter_ch_overflow[mi])
                );
            end

            // ---------- Write-side meters ----------
            for (mi = 0; mi < NUM_WR_PORTS; mi = mi + 1) begin : gen_wr_meter
                // Write per-channel attribution source.
                //   WR_CH_FROM_AWID=1: AXI4 W beats carry no WID, but W bursts
                //   follow AW-issue order -- so reconstruct the in-flight W
                //   burst's channel from awid with an AW->W order tracker
                //   (push awid's channel at AW-accept, head = current burst's
                //   channel, pop at WLAST). STREAM drives awid = channel, so no
                //   DMA sideband is needed. Correct when AW leads/accompanies W.
                //   WR_CH_FROM_AWID=0: use the explicit obs_wr_active_ch_* sideband.
                logic [CW-1:0]  wr_ch_id;
                logic           wr_ch_valid;

                if (WR_CH_FROM_AWID) begin : g_awid_track
                    localparam int AWQ_PTRW = (MAX_TRANSACTIONS > 1) ? $clog2(MAX_TRANSACTIONS) : 1;
                    logic [CW-1:0]     awq_mem [MAX_TRANSACTIONS];
                    logic [AWQ_PTRW:0] awq_wptr, awq_rptr;
                    logic              awq_empty, awq_full, awq_push, awq_pop;

                    assign awq_empty = (awq_wptr == awq_rptr);
                    assign awq_full  = (awq_wptr[AWQ_PTRW-1:0] == awq_rptr[AWQ_PTRW-1:0])
                                    && (awq_wptr[AWQ_PTRW]     != awq_rptr[AWQ_PTRW]);
                    assign awq_push  = obs_wr_awvalid[mi] && obs_wr_awready[mi] && !awq_full;
                    assign awq_pop   = obs_wr_wvalid[mi]  && obs_wr_wready[mi]
                                    && obs_wr_wlast[mi]   && !awq_empty;

                    `ALWAYS_FF_RST(aclk, aresetn,
                        if (`RST_ASSERTED(aresetn)) begin
                            awq_wptr <= '0;
                            awq_rptr <= '0;
                        end else begin
                            if (awq_push) begin
                                awq_mem[awq_wptr[AWQ_PTRW-1:0]] <= obs_wr_awid[mi][CW-1:0];
                                awq_wptr <= awq_wptr + 1'b1;
                            end
                            if (awq_pop) awq_rptr <= awq_rptr + 1'b1;
                        end
                    )
                    assign wr_ch_id    = awq_mem[awq_rptr[AWQ_PTRW-1:0]];
                    assign wr_ch_valid = !awq_empty;
                end else begin : g_sideband
                    assign wr_ch_id    = obs_wr_active_ch_id[mi];
                    assign wr_ch_valid = obs_wr_active_ch_valid[mi];
                end

                axi_bus_meter #(
                    .NUM_CHANNELS (NUM_CHANNELS)
                ) u_wr_meter (
                    .aclk             (aclk),
                    .aresetn          (aresetn),
                    .i_clear          (i_meter_clear),
                    .i_freeze         (i_meter_freeze),
                    .i_valid          (obs_wr_wvalid[mi]),
                    .i_ready          (obs_wr_wready[mi]),
                    .i_channel_id     (wr_ch_id),
                    .i_channel_valid  (wr_ch_valid),
                    .o_agg_productive   (wr_meter_agg_productive[mi]),
                    .o_agg_backpressure (wr_meter_agg_backpressure[mi]),
                    .o_agg_starvation   (wr_meter_agg_starvation[mi]),
                    .o_agg_idle         (wr_meter_agg_idle[mi]),
                    .o_ch_productive    (wr_meter_ch_productive[mi]),
                    .o_ch_backpressure  (wr_meter_ch_backpressure[mi]),
                    .o_ch_starvation    (wr_meter_ch_starvation[mi]),
                    .o_ch_idle          (wr_meter_ch_idle[mi]),
                    .o_ch_overflow      (wr_meter_ch_overflow[mi])
                );
            end

        end else begin : gen_no_meters
            // ENABLE_BUS_METER=0: tie every meter output to 0.
            for (mi = 0; mi < NUM_RD_PORTS; mi = mi + 1) begin : gen_rd_tieoff
                assign rd_meter_agg_productive[mi]   = '0;
                assign rd_meter_agg_backpressure[mi] = '0;
                assign rd_meter_agg_starvation[mi]   = '0;
                assign rd_meter_agg_idle[mi]         = '0;
                assign rd_meter_ch_overflow[mi]      = '0;
                for (ci = 0; ci < NUM_CHANNELS; ci = ci + 1) begin : gen_rd_ch_tie
                    assign rd_meter_ch_productive[mi][ci]   = '0;
                    assign rd_meter_ch_backpressure[mi][ci] = '0;
                    assign rd_meter_ch_starvation[mi][ci]   = '0;
                    assign rd_meter_ch_idle[mi][ci]         = '0;
                end
            end
            for (mi = 0; mi < NUM_WR_PORTS; mi = mi + 1) begin : gen_wr_tieoff
                assign wr_meter_agg_productive[mi]   = '0;
                assign wr_meter_agg_backpressure[mi] = '0;
                assign wr_meter_agg_starvation[mi]   = '0;
                assign wr_meter_agg_idle[mi]         = '0;
                assign wr_meter_ch_overflow[mi]      = '0;
                for (ci = 0; ci < NUM_CHANNELS; ci = ci + 1) begin : gen_wr_ch_tie
                    assign wr_meter_ch_productive[mi][ci]   = '0;
                    assign wr_meter_ch_backpressure[mi][ci] = '0;
                    assign wr_meter_ch_starvation[mi][ci]   = '0;
                    assign wr_meter_ch_idle[mi][ci]         = '0;
                end
            end
        end
    endgenerate

    // =================================================================
    // axi_perf_latency_hist per-port instantiations (RFC Stage E.3)
    //
    //   - One read histogram per rd port: AR->first-R + AR->RLAST, binned
    //     into HIST_NUM_BINS log2 bins (two metrics, select via i_hist_metric).
    //   - One write histogram per wr port: AW->B (one metric).
    //   Fed from the fabric-side handshakes (same side the meters snoop, no
    //   beats dropped through the pass-through wrappers); windowed in lockstep
    //   with the meters via i_meter_clear / i_meter_freeze. The in-core STREAM
    //   path drives those from its first-DMA-activity perf-window controller
    //   (the arm-gap fix); an observer-based harness drives them the same way.
    //   ENABLE_LATENCY_HIST=0 skips instantiation and ties outputs to 0.
    // =================================================================
    logic [NUM_RD_PORTS-1:0] rd_hist_block;
    logic [NUM_WR_PORTS-1:0] wr_hist_block;

    // Sticky across the whole measurement window; cleared with the meters so a
    // fresh window starts trustworthy.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      o_hist_sample_lost <= 1'b0;
        else if (i_meter_clear)          o_hist_sample_lost <= 1'b0;
        else if (|rd_hist_block | |wr_hist_block)
                                         o_hist_sample_lost <= 1'b1;
    )

    // Map a bus-wide AXI ID onto this instance's local channel index.
    //
    // axi_perf_latency_hist indexes with cmd_id[CW-1:0], and CW comes from
    // NUM_CHANNELS. For a 2-channel slice CW=1, so ids 0,2,4,6 would all land
    // on slot 0 -- eight channels folded into two rather than two selected.
    // Subtracting CH_BASE first makes the low bits mean what the histogram
    // assumes they mean. Out-of-slice ids are filtered upstream, so their
    // rebased value is never accumulated.
    // `port` is the tap index: each tap's histogram indexes 0..NUM_CHANNELS-1,
    // so the bus-wide id must have that tap's own base subtracted, not a single
    // instance-wide one.
    function automatic logic [AXI_ID_WIDTH-1:0] obs_rebase_id(
            input logic [AXI_ID_WIDTH-1:0] id, input int port);
        obs_rebase_id = ENABLE_ID_SLICE
            ? (id - AXI_ID_WIDTH'(CH_BASE + port * NUM_CHANNELS)) : id;
    endfunction

    genvar hi;
    generate
        if (ENABLE_LATENCY_HIST) begin : gen_hist
            // ---------- Read-side histograms (AR->first-R, AR->RLAST) ----------
            for (hi = 0; hi < NUM_RD_PORTS; hi = hi + 1) begin : gen_rd_hist
                axi_perf_latency_hist #(
                    .ID_WIDTH        (AXI_ID_WIDTH),
                    .NUM_CHANNELS    (NUM_CHANNELS),
                    .MAX_OUTSTANDING (HIST_MAX_OUTSTANDING),
                    .NUM_BINS        (HIST_NUM_BINS),
                    .IS_READ         (1'b1)
                ) u_rd_lat_hist (
                    .aclk         (aclk),
                    .aresetn      (aresetn),
                    .i_clear      (i_meter_clear),
                    .i_freeze     (i_meter_freeze),
                    .cmd_valid    (obs_rd_arvalid[hi]),
                    .cmd_ready    (obs_rd_arready[hi]),
                    .cmd_id       (obs_rebase_id(obs_rd_arid[hi], hi)),
                    .data_valid   (obs_rd_rvalid[hi]),
                    .data_ready   (obs_rd_rready[hi]),
                    .data_last    (obs_rd_rlast[hi]),
                    .data_id      (obs_rebase_id(obs_rd_rid[hi], hi)),
                    .resp_valid   (1'b0),
                    .resp_ready   (1'b0),
                    .resp_id      ('0),
                    .i_hist_metric   (w_hist_metric_sel),
                    .i_hist_bin      (w_hist_bin_sel),
                    .o_hist_count (rd_hist_count[hi]),
                    .o_hist_total (rd_hist_total[hi]),
                    .o_cmd_block  (rd_hist_block[hi])
                );
            end
            // ---------- Write-side histograms (AW->B) ----------
            for (hi = 0; hi < NUM_WR_PORTS; hi = hi + 1) begin : gen_wr_hist
                axi_perf_latency_hist #(
                    .ID_WIDTH        (AXI_ID_WIDTH),
                    .NUM_CHANNELS    (NUM_CHANNELS),
                    .MAX_OUTSTANDING (HIST_MAX_OUTSTANDING),
                    .NUM_BINS        (HIST_NUM_BINS),
                    .IS_READ         (1'b0)
                ) u_wr_lat_hist (
                    .aclk         (aclk),
                    .aresetn      (aresetn),
                    .i_clear      (i_meter_clear),
                    .i_freeze     (i_meter_freeze),
                    .cmd_valid    (obs_wr_awvalid[hi]),
                    .cmd_ready    (obs_wr_awready[hi]),
                    .cmd_id       (obs_rebase_id(obs_wr_awid[hi], hi)),
                    .data_valid   (1'b0),
                    .data_ready   (1'b0),
                    .data_last    (1'b0),
                    .data_id      ('0),
                    .resp_valid   (obs_wr_bvalid[hi]),
                    .resp_ready   (obs_wr_bready[hi]),
                    .resp_id      (obs_rebase_id(obs_wr_bid[hi], hi)),
                    .i_hist_metric   (w_hist_metric_sel),
                    .i_hist_bin      (w_hist_bin_sel),
                    .o_hist_count (wr_hist_count[hi]),
                    .o_hist_total (wr_hist_total[hi]),
                    .o_cmd_block  (wr_hist_block[hi])
                );
            end
        end else begin : gen_no_hist
            for (hi = 0; hi < NUM_RD_PORTS; hi = hi + 1) begin : gen_rd_hist_tie
                assign rd_hist_count[hi] = '0;
                assign rd_hist_total[hi] = '0;
                assign rd_hist_block[hi] = 1'b0;   // no histogram -> nothing to protect
            end
            for (hi = 0; hi < NUM_WR_PORTS; hi = hi + 1) begin : gen_wr_hist_tie
                assign wr_hist_count[hi] = '0;
                assign wr_hist_total[hi] = '0;
                assign wr_hist_block[hi] = 1'b0;   // no histogram -> nothing to protect
            end
        end
    endgenerate


    // =========================================================================
    // Telemetry readback mux (OBS_STAT_SEL -> OBS_STAT_DATA)
    //
    // These counters used to leave the block as ~70 output ports, which meant
    // every integrator tied off 70 pins and a forgotten one was a silent
    // break. They are read through this block's OWN regblock now, the same way
    // its configuration already was.
    //
    // Metrics this instance does not build (meters and histograms are
    // parameter-gated) read as 0 -- their source nets are tied to '0 by the
    // gating generate, so no special case is needed here.
    // =========================================================================
    logic [31:0] w_stat_data;
    always_comb begin
        automatic int unsigned ti = hwif.OBS.OBS_STAT_SEL.TAP.value;
        automatic int unsigned ci = hwif.OBS.OBS_STAT_SEL.CHANNEL.value;
        automatic logic        iw = hwif.OBS.OBS_STAT_SEL.IS_WRITE.value;
        w_stat_data = 32'h0;
        case (hwif.OBS.OBS_STAT_SEL.METRIC.value)
            8'd0: if (!iw) begin if (ti < NUM_RD_PORTS) w_stat_data = rd_meter_agg_productive[ti]; end
                  else      begin if (ti < NUM_WR_PORTS) w_stat_data = wr_meter_agg_productive[ti]; end
            8'd1: if (!iw) begin if (ti < NUM_RD_PORTS) w_stat_data = rd_meter_agg_backpressure[ti]; end
                  else      begin if (ti < NUM_WR_PORTS) w_stat_data = wr_meter_agg_backpressure[ti]; end
            8'd2: if (!iw) begin if (ti < NUM_RD_PORTS) w_stat_data = rd_meter_agg_starvation[ti]; end
                  else      begin if (ti < NUM_WR_PORTS) w_stat_data = wr_meter_agg_starvation[ti]; end
            8'd3: if (!iw) begin if (ti < NUM_RD_PORTS) w_stat_data = rd_meter_agg_idle[ti]; end
                  else      begin if (ti < NUM_WR_PORTS) w_stat_data = wr_meter_agg_idle[ti]; end
            // Per-channel meter buckets. CHANNEL selects within the tap; the
            // arrays are [tap][channel] and 16-bit, zero-extended here.
            8'd4: if (!iw) begin if (ti < NUM_RD_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(rd_meter_ch_productive[ti][ci]); end
                  else      begin if (ti < NUM_WR_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(wr_meter_ch_productive[ti][ci]); end
            8'd5: if (!iw) begin if (ti < NUM_RD_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(rd_meter_ch_backpressure[ti][ci]); end
                  else      begin if (ti < NUM_WR_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(wr_meter_ch_backpressure[ti][ci]); end
            8'd6: if (!iw) begin if (ti < NUM_RD_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(rd_meter_ch_starvation[ti][ci]); end
                  else      begin if (ti < NUM_WR_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(wr_meter_ch_starvation[ti][ci]); end
            8'd7: if (!iw) begin if (ti < NUM_RD_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(rd_meter_ch_idle[ti][ci]); end
                  else      begin if (ti < NUM_WR_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(wr_meter_ch_idle[ti][ci]); end
            8'd8: if (!iw) begin if (ti < NUM_RD_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(rd_meter_ch_overflow[ti][ci]); end
                  else      begin if (ti < NUM_WR_PORTS && ci < NUM_CHANNELS) w_stat_data = 32'(wr_meter_ch_overflow[ti][ci]); end
            // Latency histogram TOTAL (== burst count for the metric currently
            // selected on i_hist_metric).
            8'd10: if (!iw) begin if (ti < NUM_RD_PORTS) w_stat_data = rd_hist_total[ti]; end
                   else      begin if (ti < NUM_WR_PORTS) w_stat_data = wr_hist_total[ti]; end
            // Histogram BIN. Readable now that the bin selector is driven
            // from OBS_STAT_SEL.BIN rather than from an input port.
            8'd9: if (!iw) begin if (ti < NUM_RD_PORTS) w_stat_data = rd_hist_count[ti]; end
                  else      begin if (ti < NUM_WR_PORTS) w_stat_data = wr_hist_count[ti]; end
            default: w_stat_data = 32'h0;
        endcase
    end

    // Continuous per-field drive rather than `hwif_i = '0` plus overrides:
    // The generated hwif struct has no operator= in the simulator's C++
    // backend, so a struct-wide assignment elaborates in SV and then fails at
    // model-compile time -- lint alone does not catch it.
    // Every hw=w field in obs_regs is driven below, so nothing floats.
    assign hwif_i.OBS.OBS_STAT_DATA.VALUE.next  = w_stat_data;
    assign hwif_i.OBS.OBS_FIFO_STAT.ERR_COUNT.next   = 16'(err_fifo_count);
    assign hwif_i.OBS.OBS_FIFO_STAT.WRITE_COUNT.next = 15'(write_fifo_count);
    assign hwif_i.OBS.OBS_FIFO_STAT.ANY_FULL.next    = err_fifo_full | write_fifo_full;
    assign hwif_i.OBS.OBS_STICKY.HIST_SAMPLE_LOST.next = o_hist_sample_lost;
    assign hwif_i.OBS.OBS_STICKY.TAP_BLOCKED.next      = (|obs_rd_block_ready) | (|obs_wr_block_ready);
    assign hwif_i.OBS.OBS_COMP_STAT0.TIER1.next    = 16'(w_comp_stat_tier1_a);
    assign hwif_i.OBS.OBS_COMP_STAT0.TIER0.next    = 16'(w_comp_stat_tier0);
    assign hwif_i.OBS.OBS_COMP_STAT1.CAM_MISS.next = 16'(w_comp_stat_cam_miss);
    assign hwif_i.OBS.OBS_COMP_STAT1.OVERFLOW.next = 16'(w_comp_stat_event_data_ovf);

endmodule : axi4_intf_master_observer
