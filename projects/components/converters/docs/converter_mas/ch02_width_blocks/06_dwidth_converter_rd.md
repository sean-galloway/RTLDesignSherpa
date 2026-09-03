<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# 2.6 axi4_dwidth_converter_rd

The **axi4_dwidth_converter_rd** module is the complete AXI4 read path — AR and R channels with burst length adjustment and burst-aware RLAST generation.

## 2.6.1 Overview

The read converter combines the generic `axi_data_dnsize` with AXI4 protocol handling:

1. **Address Channel (AR)**: Passes through with burst length adjustment
2. **Read Data Channel (R)**: Uses `axi_data_dnsize` for data splitting
3. **Burst Tracking**: Generates correct RLAST based on original ARLEN
4. **Response Broadcasting**: Propagates RRESP to all narrow beats

## 2.6.2 Block Diagram

### Figure 2.7: Read Converter Architecture

![Read Converter Architecture](../assets/mermaid/dwidth_converter_rd.png)

## 2.6.3 Interface Specification

### Parameters

| Parameter | Type | Default | Description |
| --- | --- | --- | --- |
| S_AXI_DATA_WIDTH | int | 32 | Slave-side data width |
| M_AXI_DATA_WIDTH | int | 128 | Master-side data width |
| AXI_ID_WIDTH | int | 8 | Transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | Address width |
| AXI_USER_WIDTH | int | 1 | User-signal width |
| SKID_DEPTH_AR | int | 2 | AR skid buffer depth |
| SKID_DEPTH_R | int | 4 | R skid buffer depth |

: Table 2.17: Read Converter Parameters

### Ports

```systemverilog
module axi4_dwidth_converter_rd #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 128,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

    // Skid buffer packed widths
    localparam int AR_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH,
    localparam int R_WIDTH  = S_AXI_DATA_WIDTH + 2 + AXI_USER_WIDTH + 1 + AXI_ID_WIDTH
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI Read Interface
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [S_AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    //==========================================================================
    // Master AXI Read Interface
    //==========================================================================

    // Read Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // Read Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_rid,
    input  logic [M_AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready
);
```

## 2.6.4 Burst Length Conversion

### Ratio Calculation

Same as write converter:

```systemverilog
// Direction-aware, same as the write converter (2.5.4)
localparam int RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH)
                       ? (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH)
                       : (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
localparam int RATIO_LOG2 = $clog2(RATIO);

// upsize: New ARLEN = ceil((start_lane + ARLEN + 1) / RATIO) - 1
// (round UP; the start lane counts for mid-word bursts, see 2.6.5)
// downsize: split into master bursts of <= 256 beats (see 2.6.5)
```

### Examples

| S_DATA | M_DATA | Ratio | S_ARLEN | S_beats | M_ARLEN | M_beats |
| --- | --- | --- | --- | --- | --- | --- |
| 64 | 512 | 8 | 7 | 8 | 0 | 1 |
| 64 | 512 | 8 | 15 | 16 | 1 | 2 |
| 64 | 512 | 8 | 31 | 32 | 3 | 4 |

: Table 2.18: Read Burst Length Conversion

## 2.6.5 Address Channel Handling

### AR Passthrough with Adjustment

Same two directions as the write converter (see 2.5.4 for why the upsize
divide rounds up):

```systemverilog
// narrow -> wide (upsize): beats combine, round up; the start lane
// counts toward the wide total for mid-word bursts
assign m_axi_arlen  = 8'(((w_ar_lane + 10'(int_arlen) + 10'(WIDTH_RATIO))
                          / 10'(WIDTH_RATIO)) - 10'd1);

// wide -> narrow (downsize): each wide beat becomes RATIO narrow beats,
// and the product can exceed both AWLEN's 8 bits and the 256-beat legal
// maximum -- so one slave burst is SPLIT into master bursts of <= 256
// beats (same mechanism as the write converter, see 2.5.5)
assign m_axi_arlen  = 8'(w_this_beats - 9'd1);  // min(remaining, 256)

// size is the master's own full width, not a shift of ARSIZE
assign m_axi_arsize = MASTER_SIZE[2:0];
```

For a split read the slave must still see ONE burst: each master burst
returns its own RLAST, and every one except the final master burst's is
masked out of the upsize, whose accumulation simply continues across the
boundary. The masking is safe by construction — 256 narrow beats is a
whole number of wide beats at every ratio, so a masked boundary can never
land mid-accumulation. A one-bit flag queue, pushed per issued AR and
popped per master RLAST, says which burst is final.

On the UPSIZE path the issued address is aligned down to the master
data width — the slave returns whole wide words — and mid-word INCR
starts are handled by the R slicer: the burst-length FIFO carries the
start lane alongside the narrow length, `m_axi_arlen` counts it
(`ceil((start_lane + narrow_beats) / RATIO)` wide beats), and
`axi_data_dnsize` slices the burst's FIRST wide word from that lane,
so the narrow master receives the bytes it actually addressed. Later
wide words slice from lane 0. FIXED/WRAP keep the wide-aligned
requirement (asserted in simulation). The downsize path issues narrow
accesses and passes the address through the splitter unmodified apart
from the per-burst advance:

```systemverilog
localparam int ALIGN_BITS = $clog2(M_STRB_WIDTH);
assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH-1:ALIGN_BITS],
                         {ALIGN_BITS{1'b0}}};
assign m_axi_araddr   = aligned_araddr;
```

### Burst-Length FIFO

Only the wide→narrow R data path needs one — that is the converter's
**UPSIZE** mode (S narrower than M: wide master read data sliced down to
narrow slave beats through `axi_data_dnsize`). The downsize block
ignores a `burst_start` pulse while a burst is active and keeps no length
queue of its own, so framing only the first burst would collapse N read
bursts into one — bursts 2..N would drain with `narrow_last` never
asserting. A small queue holds one narrow ARLEN per outstanding burst:
its head feeds the downsize, and it pops as each narrow burst completes,
so every burst is framed however they overlap.

It is an inline circular buffer rather than a `fifo_sync` instance,
deliberately: this converter is widely instantiated and a submodule here
would add a filelist dependency to every consumer. It stores the narrow
length AND the burst's start lane (mid-word INCR starts, CONV-006) —
ID is carried on the AXI channels, not through this queue — and
AR is back-pressured when full, so it cannot overflow.

```systemverilog
            localparam int BLEN_FIFO_DEPTH = 16;
            localparam int BLEN_AW         = $clog2(BLEN_FIFO_DEPTH);

            localparam int R_LANE_W = $clog2(WIDTH_RATIO);
            logic [7:0]          blen_mem      [BLEN_FIFO_DEPTH];
            logic [R_LANE_W-1:0] blen_lane_mem [BLEN_FIFO_DEPTH];  // start lane
            logic [BLEN_AW:0]    blen_wptr, blen_rptr;   // extra MSB for full/empty
            logic               w_blen_push, w_blen_pop;

            // AR accepted -> enqueue its narrow length. A slave-side (narrow)
            // burst completes on its last-beat handshake -> dequeue.
            assign w_blen_push = int_ar_valid && int_ar_ready;
            assign w_blen_pop  = int_r_valid && int_r_ready && int_rlast;
```

The narrow→wide R data path (the converter's DOWNSIZE mode) needs no
such queue; its generate branch ties the shared handshake wires off
inert.

## 2.6.6 Read Data Channel

### Downsize Instance

```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH      (M_AXI_DATA_WIDTH),
    .NARROW_WIDTH    (S_AXI_DATA_WIDTH),
    .WIDE_SB_WIDTH   (2),          // RRESP
    .NARROW_SB_WIDTH (2),
    .SB_BROADCAST    (1),          // Broadcast RRESP
    .TRACK_BURSTS    (1),
    .BURST_LEN_WIDTH (8)
) u_r_dnsize (
    .aclk            (aclk),
    .aresetn         (aresetn),
    // burst framing is MANDATORY with TRACK_BURSTS(1): burst_len is in
    // NARROW beats - 1, and burst_start is LEVEL-HELD while the length
    // FIFO is non-empty (the dnsize samples it only when idle, which is
    // what frames every overlapping burst); leaving them off silently
    // produces framing with no LAST (see 2.3.9)
    .burst_len       (w_blen_rd_data),
    .burst_start     (w_blen_rd_valid),
    .start_lane      (w_blen_rd_lane[$clog2(WIDTH_RATIO)-1:0]),
    .wide_valid      (m_axi_rvalid),
    .wide_ready      (m_axi_rready),
    .wide_data       (m_axi_rdata),
    .wide_sideband   (m_axi_rresp),
    .wide_last       (m_axi_rlast),
    .narrow_valid    (int_r_valid),
    .narrow_ready    (int_r_ready),
    .narrow_data     (int_rdata),
    .narrow_sideband (int_rresp),
    .narrow_last     (int_rlast)
);
```

## 2.6.7 RLAST Generation

There is no local RLAST tracker in the converter. The downsize block
generates `narrow_last` itself in TRACK_BURSTS mode, framed by the
burst-length FIFO of 2.6.5: each accepted AR pushes its narrow-beat
length, the FIFO head drives `burst_len`/`burst_start`, and the dnsize
counts narrow beats against it — `int_rlast` comes out of the dnsize
and passes to `s_axi_rlast` through the R skid.

(An earlier revision showed a standalone counter loading
`(arlen + 1) * RATIO - 1`, the same xRATIO framing 2.3.4 calls out as
the classic mis-framing bug. No such multiply exists anywhere in the
converter: in UPSIZE mode the slave side is already narrow, so the
ARLEN pushed into the FIFO is already in narrow-beat units —
`blen_mem[...] <= int_arlen;` stores it unchanged.)

## 2.6.8 RID Handling

### ID Passthrough

RID is sampled from the master side and HELD:

```systemverilog
// from the RTL: latch rid/ruser on every master R handshake; AXI4
// keeps RID constant across a transaction's beats, so "most recent
// rid" is correct for whatever aggregated beat is being emitted
`ALWAYS_FF_RST(aclk, aresetn,
    ... else if (m_axi_rvalid && m_axi_rready) begin
        r_rid_held   <= m_axi_rid;
        r_ruser_held <= m_axi_ruser;
    end
)
assign int_rid = r_rid_held;
```

### Ordering Constraint (applies to both directions)

**The master-side slave must return responses in AR/AW issue order across ALL
IDs.** Neither converter carries a transaction ID through its data path, so
neither can attribute an out-of-order completion to the burst it belongs to.

Read side: the burst-length queue holds `{narrow ARLEN, start lane}` and
nothing else, and `s_axi_rid` is a single register latched on every master R
handshake. If a slave returns ID1's data before ID0's, ID1's beats are counted
against ID0's queue head, `s_axi_rlast` fires at the wrong boundary, one
aggregated wide beat can mix two transactions, and `s_axi_rid` is whichever ID
handshaked most recently.

Write side: the split queue is popped by `split_b_pop = m_axi_bvalid &&
m_axi_bready` -- any arriving B pops the head, whatever its ID -- and
`m_axi_bready = split_b_final ? int_b_ready : 1'b1` swallows a non-final
response unconditionally. A B that arrives out of order is folded into the
wrong burst's accumulator: the burst it actually belonged to never gets its
response (the master hangs), the other burst's response is built from the
wrong beats, and every later burst's framing is shifted by one.

AXI4 permits both behaviours. A slave may complete different-ID transactions
out of order and may interleave read data across IDs, and a multi-ported DDR
controller normally does. Satisfying "one outstanding transaction per ID" is
**not** sufficient -- two IDs with one transaction each meet that and still
break the fold.

Safe configurations are: an in-order master-side slave, or a single ID
outstanding at a time. Nothing in the RTL enforces or detects a violation, so
a breach corrupts data silently rather than failing (tracked as CONV-001).

## 2.6.9 Resource Utilization

### Typical Resources (64→512 UPSIZE, ratio 8, ID=4)

The burst-length FIFO exists only in the converter's UPSIZE mode (see
2.6.5), so the configuration here is upsize — an earlier revision
labeled this table 512→64 (DOWNSIZE), a mode in which that FIFO is
tied off and does not exist. Hand estimates, not synthesis results,
except the FIFO, which is counted from its declarations.

```
AR skid buffer:      ~150 flip-flops
R dnsize data path:  ~600 flip-flops, ~50 LUTs  (single-buffer slicer)
Burst-length FIFO:   186 flip-flops
                     (16 x 8b length + 16 x 3b start lane + two 5b pointers)
Control logic:       ~80 LUTs

Total: ~940 flip-flops, ~130 LUTs (sum of the lines above)
```

There is no separate "burst tracker" block — 2.6.7 explains RLAST
comes from the dnsize's own counter, framed by the FIFO. The R data
path is the single-buffer `axi_data_dnsize` — the only implementation;
its ping-pong `DUAL_BUFFER` variant was removed, see 2.3.8.

## 2.6.10 Timing

### Latency

| Path | Latency |
| --- | --- |
| AR passthrough | 1-2 cycles (skid) |
| First R beat | 1 cycle (load buffer) |
| Subsequent R beats | 1 beat/cycle |

: Table 2.20: Read Converter Latency

### Throughput

- AR channel: 1 transaction/cycle
- R channel: the downsize accepts its next wide beat during the last narrow beat — 0.992 beats/cycle measured in simple mode (TRACK_BURSTS=1 pays one bubble per burst boundary and measures ~0.93; see 2.3)

## 2.6.11 Usage Example

```systemverilog
axi4_dwidth_converter_rd #(
    .S_AXI_DATA_WIDTH (128),
    .M_AXI_DATA_WIDTH (32),
    .AXI_ID_WIDTH     (8),
    .AXI_ADDR_WIDTH   (32),
    .SKID_DEPTH_AR    (2),
    .SKID_DEPTH_R     (4)
) u_conv (
    .aclk             (aclk),
    .aresetn          (aresetn),
    // slave side: s_axi_ar*/... (full AXI4 channel set)
    .s_axi_arvalid   (cpu_arvalid),
    .s_axi_arready   (cpu_arready),
    // ...
    // master side: m_axi_* toward the narrow fabric
    .m_axi_arvalid   (mem_arvalid),
    .m_axi_arready   (mem_arready)
    // ...
);
```

All channel ports carry the `s_axi_`/`m_axi_` prefix; the full list is
the module header. Skid depths are per channel — there is no single
`SKID_DEPTH`.

---

**Next:** [Protocol Conversion Overview](../ch03_protocol_blocks/01_overview.md)
