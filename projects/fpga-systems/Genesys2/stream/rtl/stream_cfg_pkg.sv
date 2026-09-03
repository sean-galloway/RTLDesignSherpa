// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Package: stream_char_cfg_pkg
// Purpose: THE configuration of the STREAM characterization environment.
//          One source, read by the board top and by every cosim.
//
// Why a package:
//   The interesting characterization parameters (engine outstanding-queue
//   depths, response-delay queue capacities, harness memory sizing) are
//   plumbed all the way down from stream_genesys2_top → stream_harness →
//   stream_top_ch8 → stream_core. Centralising them here gives one file to
//   edit per config instead of hunting through three modules.
//
// Why it is now the WHOLE geometry and not just two knobs:
//   It used to carry four parameters, of which the board top read two. Every
//   other value was written out by hand in three more places -- the board top,
//   build-mon's cosim, build-perf's cosim -- and all three disagreed, with
//   each other and with this file. Measured 2026-08-25:
//
//     param                  board   build-mon   build-perf   this pkg
//     AR/AW_MAX_OUTSTANDING     2         2          16          8 (unread)
//     RESP_DELAY_R_CAPACITY   256       512         512        256
//     RESP_DELAY_B_CAPACITY    16       512          32         16
//     SRAM_DEPTH              256       512         512          -
//     DESC_RAM_ENTRIES        256      2048         128          -
//     DEBUG_SRAM_WORDS       4096     65536        4096          -
//
//   build-perf was therefore characterizing an engine with 8x the outstanding
//   depth the board builds, which is why sim throughput never predicted board
//   throughput. A default that silently differs from silicon is worse than no
//   default: it produces green runs that mean nothing.
//
//   So: these are the values, the RTL defaults FROM here, and a cosim that
//   wants to deviate must say so at its instantiation, in the open, with a
//   reason. Divergence is opt-in and visible instead of ambient.
//
// How to sweep a parameter for a build campaign:
//   Keep one variant package per config and swap which one is in the filelist
//   -- e.g. stream_char_cfg_pkg_deep.sv (AR=AW=16). Each defines the SAME
//   package name with different values; the Makefile/filelist picks one.
//   Alternatively override at the stream_genesys2_top / stream_harness
//   instantiation for a one-off experiment.
//
// One build, not two:
//   USE_AXI_MONITORS used to be per-BUILD flavor (build-mon 1, build-perf 0)
//   and lived in each Makefile. It is common geometry now: there is a single
//   board configuration -- all monitors on, AR/AW monitor CAMs banked -- so
//   that what runs on the bench and what runs in the cosim cannot be two
//   different designs. DATA_MON_CONE_MODE stays a Vivado generic because the
//   cone set is a campaign choice, not geometry, and the harness already
//   defaults it to 2 (all cones).

`timescale 1ns / 1ps

package stream_char_cfg_pkg;

    // -------------------------------------------------------------------------
    // Datapath geometry
    // -------------------------------------------------------------------------
    parameter int CFG_DATA_WIDTH   = 128;
    parameter int CFG_ADDR_WIDTH   = 32;
    parameter int CFG_NUM_CHANNELS = 8;

    // -------------------------------------------------------------------------
    // STREAM engine outstanding queues ("side-Qs")
    // -------------------------------------------------------------------------
    // Maximum number of in-flight read/write bursts per engine. These set
    // the depth of stream_core's AR/AW reorder/tracking queues. They are
    // the primary lever for measuring how much memory latency the engines
    // can hide via multi-outstanding pipelining.
    //
    // Little's Law: a sustained transfer hides L cycles of round-trip
    // memory latency when AR_MAX_OUTSTANDING × burst_len >= L.
    //   AR=8, burst=16 → covers 128 cycles before throughput degrades.
    //
    // 8 is the design point. The board top used to hardcode 2 to keep the
    // in-core monitor CAMs small enough to close timing with every packet
    // class compiled in; that traded away the engine's latency hiding to buy
    // monitor area, and it did it silently, in a module nobody diffed against
    // this file.
    //
    // That trade is retired, not merely re-argued: the monitor CAM is banked
    // now (CFG_MON_NUM_BANKS), so the 72-slot table at 8 outstanding is 4
    // shallow cams rather than one deep one, and the timing objection that
    // forced 2 no longer applies. The engine keeps its latency hiding and the
    // monitors keep their table.
    parameter int CFG_AR_MAX_OUTSTANDING = 8;
    parameter int CFG_AW_MAX_OUTSTANDING = 8;

    // -------------------------------------------------------------------------
    // axi_response_delay queue capacities (slave-side memory model)
    // -------------------------------------------------------------------------
    // CAPACITY is the maximum number of beats / BRESPs the pipelined delay
    // block holds in flight. Must be >= engine outstanding × max_burst on
    // the R side, >= engine outstanding on the B side. Power-of-2.
    //   R: 8 outstanding × 16 max_burst = 128 <= 256  OK
    //   B: 8 outstanding                      <=  16  OK
    // These two and CFG_A?_MAX_OUTSTANDING move together -- raising the
    // outstanding depth without raising R invites the modeled memory to
    // back-pressure and mask the very throughput the campaign is measuring.
    parameter int CFG_RESP_DELAY_R_CAPACITY = 256;
    parameter int CFG_RESP_DELAY_B_CAPACITY = 16;

    // -------------------------------------------------------------------------
    // Harness memory sizing
    // -------------------------------------------------------------------------
    // Sized for the Genesys 2 build. The cosim inherits these so it exercises
    // the same memories as silicon; a test that needs deeper descriptor chains
    // or a longer trace capture overrides at its own instantiation.
    parameter int CFG_SRAM_DEPTH       =  256;
    parameter int CFG_DESC_RAM_ENTRIES =  256;   //  256 × 256 b =   8 KB (LUTRAM)
    parameter int CFG_DEBUG_SRAM_WORDS = 4096;   // 4096 ×  32 b =  16 KB (~4 BRAM)

    // -------------------------------------------------------------------------
    // In-core AXI monitors (the AR/AW datapath monitors in stream_core)
    // -------------------------------------------------------------------------
    // ONE build. Monitors are ON, and their CAMs are BANKED. There is no
    // monitors-off flavor to keep in step, because carrying two board
    // configurations to test one design is how sim and silicon end up
    // measuring different things -- see [[one-source-config]].
    parameter int CFG_USE_AXI_MONITORS = 1;

    // Observer taps, INDEPENDENT of CFG_USE_AXI_MONITORS on purpose.
    //
    // With both on the design needs 217,761 LUTs against 203,800 on the
    // xc7k325t -- it does not fit and the placer never runs. So the three
    // builds pick ONE instrument each, via their own Makefile generics
    // (USE_AXI_MONITORS / OBS_ENABLE_MON_TAPS); these are only the defaults:
    //
    //   build-perf : monitors 0, taps 0   -- clean throughput, no instrument
    //   build-obs  : monitors 0, taps 1   -- observers are the vehicle
    //   build-mon  : monitors 1, taps 0   -- in-core stream monitors
    //
    // These MUST stay separate knobs. Deriving the taps from USE_AXI_MONITORS
    // means turning the in-core monitors off for area silently disarms the
    // observers too -- the welding stream_harness.sv already warns about.
    parameter bit CFG_OBS_ENABLE_MON_TAPS = 1'b0;

    // Banked monitor CAM. stream_core sizes the table as
    //     MAX(16, NUM_CHANNELS * Ax_MAX_OUTSTANDING + MON_TRANS_MARGIN)
    // which at 8 channels x 8 outstanding + 8 margin is 72 slots. Timing
    // scales with the depth of ONE cam, not the total (16 deep measured at
    // WNS +1.018 ns, 40 deep at -25.183 ns), so 72 as one flat cam does not
    // close and 72 as 4 x 18 does. Same reasoning, same bank count as the
    // observers below -- the observers were banked for this years before the
    // in-core monitors could be, because stream_core had no NUM_BANKS to pass.
    //
    // Keep, as for the observers:
    //     table / CFG_MON_NUM_BANKS >= IDs-per-bank x outstanding-per-ID
    // 8 channels over 4 banks = 2 IDs/bank x 8 outstanding = 16 <= 18. OK.
    // Raising CFG_AR/AW_MAX_OUTSTANDING deepens the table, so re-check this
    // inequality when you touch either.
    // 8, not 4. At AR/AW=8 the table is 72 slots, so 4 banks is 18 deep and
    // the routed build came in at WNS -4.150 ns with every top failing-path
    // hotspot inside trans_mgr/g_cam_bank -- the CAM is the critical path,
    // and CAM timing scales with the depth of ONE bank (16 deep measured
    // +1.018 ns, 40 deep -25.183 ns). 8 banks makes it 9 deep, under the
    // depth that measured positive.
    //
    // The constraint still holds: table/banks >= IDs-per-bank x
    // outstanding-per-ID, i.e. 9 >= (8ch/8banks) x 8 = 8.
    //
    // This spends AREA to buy TIME, which is the right direction here --
    // measurement-only observers freed ~50k LUTs, so the build sits at 73.9%
    // with a quarter of the device unused, while timing is the thing short.
    parameter int CFG_MON_NUM_BANKS = 8;

    // -------------------------------------------------------------------------
    // Observer transaction-table sizing
    // -------------------------------------------------------------------------
    // OBS_MAX_TRANSACTIONS is the TOTAL slots per tap; the CAM is generated
    // OBS_NUM_BANKS times at OBS_MAX_TRANSACTIONS/OBS_NUM_BANKS each, because
    // timing scales with the depth of ONE cam, not the total (16 deep measured
    // at WNS +1.018 ns, 40 deep at -25.183 ns -- so 64 as one flat CAM will
    // not close, while 64 as 4×16 is four CAMs at a depth that does).
    // Banking is by ID, so per-ID concurrency is capped by the BANK depth:
    //     OBS_MAX_TRANSACTIONS/OBS_NUM_BANKS >= IDs-per-bank × outstanding-per-ID
    // 8 channels × 8 outstanding over 4 banks => 64/4 = 16 per bank.
    parameter int CFG_OBS_MAX_TRANSACTIONS  = 64;
    parameter int CFG_OBS_NUM_BANKS         = 4;
    // Mandatory once a WRITE monitor is banked: the WID-less select is not
    // ID-matched, and trans_mgr refuses to elaborate without this.
    parameter bit CFG_OBS_USE_WDATA_ORDER_Q = 1'b1;

    // -------------------------------------------------------------------------
    // Addressing / MonBus
    // -------------------------------------------------------------------------
    // TASK-101 extended (row/col-major) addressing. On, so both legacy
    // contiguous and extended descriptors run in every build.
    parameter int CFG_USE_ROW_COL_MAJOR_ADDRESSING = 1;

    // Agent-resolved tally legal-set size, for BOTH tally memories.
    parameter int CFG_MON_N_PROFILE = 64;

    // Per-channel completion/error MonBus emitters (descriptor_engine /
    // scheduler). OFF for area: the board has never built them, so a cosim
    // running with them on is exercising agents 16-23 and 48-55 that do not
    // exist in silicon. Monitor-coverage tests override to 1 deliberately.
    parameter bit CFG_GEN_MON = 1'b0;

    // MonBus bulk-trace compression, and half-beat packing on the compressed
    // path (two 30-bit slots per 64-bit beat). Both on for this project.
    parameter int CFG_USE_MON_COMPRESSION = 1;
    parameter int CFG_USE_MON_HALFBEAT    = 1;

endpackage : stream_char_cfg_pkg
