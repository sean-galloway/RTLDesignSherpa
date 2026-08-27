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

# 2.5 axi4_dwidth_converter_wr

The **axi4_dwidth_converter_wr** module is the complete AXI4 write path — AW, W, and B channels with burst length adjustment for the new width.

## 2.5.1 Overview

The write converter combines the generic `axi_data_upsize` with AXI4 protocol handling:

1. **Address Channel (AW)**: Passes through with burst length adjustment
2. **Write Data Channel (W)**: Uses `axi_data_upsize` for data packing
3. **Response Channel (B)**: Passes through unchanged
4. **Burst Length Adjustment**: Converts AWLEN based on width ratio

## 2.5.2 Block Diagram

### Figure 2.6: Write Converter Architecture

![Write Converter Architecture](../assets/mermaid/dwidth_converter_wr.png)

## 2.5.3 Interface Specification

### Parameters

| Parameter | Type | Default | Description |
| --- | --- | --- | --- |
| S_AXI_DATA_WIDTH | int | 32 | Slave-side data width |
| M_AXI_DATA_WIDTH | int | 128 | Master-side data width |
| AXI_ID_WIDTH | int | 8 | Transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | Address width |
| AXI_USER_WIDTH | int | 1 | User-signal width |
| SKID_DEPTH_AW | int | 2 | AW skid buffer depth |
| SKID_DEPTH_W | int | 4 | W skid buffer depth |
| SKID_DEPTH_B | int | 2 | B skid buffer depth |

: Table 2.14: Write Converter Parameters

### Ports

```systemverilog
module axi4_dwidth_converter_wr #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 128,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

    // Skid buffer packed widths
    localparam int AW_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH,
    localparam int W_WIDTH  = S_AXI_DATA_WIDTH + S_STRB_WIDTH + 1 + AXI_USER_WIDTH,
    localparam int B_WIDTH  = AXI_ID_WIDTH + 2 + AXI_USER_WIDTH
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI Write Interface
    //==========================================================================

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write Data Channel
    input  logic [S_AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [S_STRB_WIDTH-1:0]     s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI Write Interface
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // Write Data Channel
    output logic [M_AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [M_STRB_WIDTH-1:0]     m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready
);
```

## 2.5.4 Burst Length Conversion

### Ratio Calculation

```systemverilog
// Direction-aware: wider / narrower (a plain M/S divide evaluates to
// 0 in DOWNSIZE mode and $clog2(0) is illegal)
localparam int RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH)
                       ? (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH)
                       : (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
localparam int RATIO_LOG2 = $clog2(RATIO);

// upsize: New AWLEN = ceil((AWLEN + 1) / RATIO) - 1  (round UP --
// a floor divide underflows on non-multiples, see 2.5.5)
// downsize: split into master bursts of <= 256 beats (see 2.5.5)
```

### Examples

| S_DATA | M_DATA | Ratio | S_AWLEN | S_beats | M_AWLEN | M_beats |
| --- | --- | --- | --- | --- | --- | --- |
| 64 | 512 | 8 | 7 | 8 | 0 | 1 |
| 64 | 512 | 8 | 15 | 16 | 1 | 2 |
| 64 | 256 | 4 | 3 | 4 | 0 | 1 |
| 64 | 256 | 4 | 7 | 8 | 1 | 2 |

: Table 2.15: Burst Length Conversion Examples

### Non-Aligned Bursts

When the burst length is not a multiple of the ratio:

```
S_AWLEN = 5 (6 beats), RATIO = 8
M_AWLEN = 0 (1 beat)

The 6 narrow beats pack into 1 wide beat.
Remaining 2 positions have WSTRB = 0 (no write).
```

## 2.5.5 Address Channel Handling

### AW Passthrough with Adjustment

The rewrite differs by direction, so the RTL has two generate branches.

**Narrow → wide (upsize).** Beats combine, so the count divides — and it
must round UP, because a burst that is not a whole multiple of the ratio
still needs a final partial wide beat:

```systemverilog
assign m_axi_awlen = ((int_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
```

**Wide → narrow (downsize).** Each wide beat becomes RATIO narrow ones
— and the product does not fit a burst. AXI4 allows 256 beats, so a
full-length slave burst needs up to `256 * WIDTH_RATIO` narrow beats,
which is neither expressible in the 8-bit AWLEN nor a legal burst. One
slave burst is therefore **split** into as many master bursts of <= 256
beats as it takes:

```systemverilog
// remaining-beat counter, 9 + $clog2(WIDTH_RATIO) bits -- 8 is exactly
// what a multiply-into-AWLEN overflows
r_split_remaining <= (CNTW'(int_awlen) + CNTW'(1)) * CNTW'(WIDTH_RATIO);
...
assign m_axi_awlen = 8'(w_this_beats - 9'd1);   // w_this_beats = min(remaining, 256)
```

Each issued master burst is recorded in a split queue — its beat count
frames that burst's WLAST on the W path, and a final-burst flag drives
the B fold (several master responses collapse into one slave response,
worst case wins). The address advances by `256 * M_STRB_WIDTH` per burst
for INCR and holds for FIXED; WRAP never reaches a split, since AXI4
caps it at 16 beats and `16 * RATIO <= 256` for every supported ratio.
The slave's AW is consumed only when its final master burst has been
issued.

Rounding up is the whole point of the `+ WIDTH_RATIO` term. A floor
divide underflows: AWLEN=5 (6 beats) at RATIO=8 gives `(6 >> 3) - 1`,
which is -1 — 8'hFF, a 256-beat burst — where the correct answer is 0,
one wide beat.

**Size** is not derived from the incoming AWSIZE. Both branches drive the
master side at its own full width:

```systemverilog
assign m_axi_awsize = MASTER_SIZE[2:0];
```

Neither converter checks address alignment on the downsize path. The
read converter aligns the address it issues on its UPSIZE path only —
a wide access cannot start mid-word (see 2.6.5).

**Upsize INCR bursts may start mid-wide-word.** The AXI-correct
behavior: the first wide beat carries the narrow data in the byte
lanes the ADDRESS selects, with WSTRB covering only those lanes
(leading lanes byte-disabled, not clobbered). Three pieces cooperate:

- `m_axi_awlen` counts the lane offset:
  `ceil((start_lane + narrow_beats) / RATIO)` wide beats. AWADDR
  passes through unchanged — unaligned is legal AXI; the first beat
  is partial within its size container.
- an AW-lane queue (same inline pattern as the read converter's
  burst-length FIFO) records each accepted AW's start lane; W beats
  are held off until their AW is queued (the packer's lane comes from
  AWADDR), and the entry pops on the NARROW side's last beat — the
  head must track the burst the CURRENT narrow beat belongs to, and a
  wide-side pop raced back-to-back bursts.
- `axi_data_upsize` takes a `start_lane` input: the first narrow beat
  of a burst lands at that lane (data AND WSTRB shifted, leading
  slots '0); later wide groups of the burst start at lane 0.

FIXED and WRAP keep the wide-aligned requirement (asserted in
simulation) — their lane semantics through the packer are not
defined.

### Skid Buffer for AW

The channel buffers are `gaxi_skid_buffer` (there is no
`axi_skid_buffer`), and they carry the UNMODIFIED slave fields — the
length rewrite happens after the skid, in the splitter:

```systemverilog
gaxi_skid_buffer #(
    .DEPTH(SKID_DEPTH_AW),
    .DATA_WIDTH(AW_WIDTH)
) aw_skid (
    .axi_aclk   (aclk),
    .axi_aresetn(aresetn),
    .wr_valid   (s_axi_awvalid),
    .wr_ready   (s_axi_awready),
    .wr_data    ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize,
                  s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot,
                  s_axi_awqos, s_axi_awregion, s_axi_awuser}),
    .rd_valid   (int_aw_valid),
    .rd_ready   (int_aw_ready),
    .rd_data    (int_aw_data),
    .count      (),
    .rd_count   ()
);
```

## 2.5.6 Write Data Channel

### Upsize Instance

```systemverilog
axi_data_upsize #(
    .NARROW_WIDTH    (S_AXI_DATA_WIDTH),
    .WIDE_WIDTH      (M_AXI_DATA_WIDTH),
    .NARROW_SB_WIDTH (S_STRB_WIDTH),   // WSTRB
    .WIDE_SB_WIDTH   (M_STRB_WIDTH),
    .SB_OR_MODE      (0)               // Concatenate WSTRB
) u_w_upsize (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .narrow_valid    (int_w_valid),
    .narrow_ready    (int_w_ready),
    .narrow_data     (int_wdata),
    .narrow_sideband (int_wstrb),
    .narrow_last     (int_wlast),
    .wide_valid      (m_axi_wvalid),
    .wide_ready      (m_axi_wready),
    .wide_data       (m_axi_wdata),
    .wide_sideband   (m_axi_wstrb),
    .wide_last       (m_axi_wlast)
);
```

## 2.5.7 Response Channel

### B Channel

Upsize passes the response through unchanged. Downsize cannot: a split
slave burst receives several master responses, and the slave expects
ONE. Non-final responses are consumed immediately and folded worst-case-
wins; the final one carries the folded result (see 2.5.5). The
passthrough below is the UPSIZE branch:

```systemverilog
// gen_b_pass (upsize)
assign s_bvalid = m_bvalid;
assign m_bready = s_bready;
assign s_bid    = m_bid;
assign s_bresp  = m_bresp;
```

### Response Ordering

Responses return in order because:
- Single outstanding transaction per ID
- Upsize doesn't reorder data
- B response generated after all W beats accepted

## 2.5.8 AW/W Synchronization

### Challenge

AXI4 allows AW to arrive before, with, or after W data. The converter must handle all cases:

1. **AW before W**: Normal pipelining
2. **W before AW**: Data buffered until AW arrives
3. **Interleaved**: Multiple transactions in flight

### Solution

The **upsize** path carries an AW-lane queue (see 2.5.5): each
accepted AW pushes its start lane, and W beats are held off until
their AW is queued — the packer's lane placement comes from AWADDR,
so W genuinely cannot run ahead of its address. The entry pops on the
narrow side's last beat.

The **downsize** path does carry one — the split queue of 2.5.5. Each
issued master burst pushes `{final-burst flag, beat count}`; the beat
count frames that burst's WLAST on the W path and the flag drives the
B fold. AW runs ahead of W, which is precisely why that AW-derived
information must be queued.

Compare the read converter, which needs a queue in its UPSIZE mode: its
downsize block has no length queue of its own, so overlapping read
bursts would lose their framing without an external ARLEN queue.

## 2.5.9 Resource Utilization

### Typical Resources (64→512, ID=4, ADDR=64)

```
AW skid buffer:     ~200 flip-flops
W upsize:           ~600 flip-flops, ~60 LUTs
B skid buffer:      ~20 flip-flops
Control logic:      ~100 LUTs

Total: ~820 flip-flops, ~160 LUTs

Hand estimates, not synthesis results. AW-derived storage: the
downsize split queue, or the upsize AW-lane queue (16 x lane-width
entries + two 5-bit pointers) -- see 2.5.5 for both.
```

## 2.5.10 Timing

### Latency

| Path | Latency |
| --- | --- |
| AW passthrough | 1-2 cycles (skid) |
| W upsize | N cycles (accumulation) |
| B passthrough | 1 cycle (skid) |

: Table 2.16: Write Converter Latency

### Throughput

- AW channel: 1 transaction/cycle
- W channel: 100% (upsize is 100%)
- B channel: 1 response/cycle

## 2.5.11 Usage Example

```systemverilog
axi4_dwidth_converter_wr #(
    .S_AXI_DATA_WIDTH (128),   // slave wide
    .M_AXI_DATA_WIDTH (32),    // master narrow (downsize)
    .AXI_ID_WIDTH     (8),
    .AXI_ADDR_WIDTH   (32),
    .SKID_DEPTH_AW    (2),
    .SKID_DEPTH_W     (4),
    .SKID_DEPTH_B     (2)
) u_conv (
    .aclk             (aclk),
    .aresetn          (aresetn),
    // slave side: s_axi_aw*/... (full AXI4 channel set)
    .s_axi_awvalid   (cpu_awvalid),
    .s_axi_awready   (cpu_awready),
    // ...
    // master side: m_axi_* toward the narrow fabric
    .m_axi_awvalid   (mem_awvalid),
    .m_axi_awready   (mem_awready)
    // ...
);
```

All channel ports carry the `s_axi_`/`m_axi_` prefix; the full list is
the module header. Skid depths are per channel — there is no single
`SKID_DEPTH`.

---

**Next:** [axi4_dwidth_converter_rd](06_dwidth_converter_rd.md)
