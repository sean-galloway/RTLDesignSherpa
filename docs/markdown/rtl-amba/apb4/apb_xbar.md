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

# apb_xbar_thin

A fully parameterized M×S APB crossbar switch providing full connectivity between
multiple APB masters and slaves with weighted round-robin arbitration and
runtime-programmable address decoding.

**Module:** `apb_xbar_thin.sv`
**Location:** `projects/components/apb_xbar/rtl/`
**Status:** ✅ Production Ready

---

## Naming Note

Earlier revisions of this document described a module named `apb_xbar` with
separate `MST_THRESHOLDS` and `SLV_THRESHOLDS` inputs, an internal `DEPTH`
parameter, `apb4_slave`/`apb4_master` stub conversion, side queues, and a 3-cycle
minimum latency.

**No such module exists.** The parameterized crossbar in this repository is
`apb_xbar_thin`, and it has a materially different architecture -- it is
combinational and does no protocol conversion at all. This document has been
rewritten against the actual RTL.

The other family, the fixed-configuration generated crossbars (`apb_xbar_1to1`,
`apb_xbar_2to1`, `apb_xbar_1to4`, `apb_xbar_2to4`), *does* use `apb4_slave` +
`apb4_master` conversion and is specified separately in
[apb_crossbar.md](apb_crossbar.md).

### Choosing Between the Two Families

| | `apb_xbar_thin` | Generated crossbars |
|---|---|---|
| Topology | Any M×S, set by parameter | Fixed per generated file |
| Address map | Runtime inputs, per-slave base/limit/enable | Compile-time, uniform 64 KB regions |
| Arbitration | Weighted round-robin | Plain round-robin |
| Protocol conversion | None -- combinational passthrough | APB → cmd/rsp → APB |
| Buffering | None | Skid buffers on both sides |
| Added latency | Zero cycles | Multiple cycles (see [apb_crossbar.md](apb_crossbar.md)) |
| Combinational path | Master APB to slave APB, and `PREADY`/`PRDATA` back | Broken by registers |
| Best for | Sparse or reprogrammable maps, latency-critical paths | Timing closure at higher frequency |

The word "thin" is the operative one: this module adds no pipeline stages, which
makes it the lowest-latency choice and the hardest one to close timing on.

---

## Module Declaration

```systemverilog
module apb_xbar_thin #(
    // Number of APB masters (from the master)
    parameter int M = 2,
    // Number of APB slaves (to the dest)
    parameter int S = 4,
    // Address width
    parameter int ADDR_WIDTH = 32,
    // Data width
    parameter int DATA_WIDTH = 32,
    // Strobe width
    parameter int STRB_WIDTH = DATA_WIDTH/8,
    parameter int MAX_THRESH = 16,
    // local abbreviations
    parameter int DW    = DATA_WIDTH,
    parameter int AW    = ADDR_WIDTH,
    parameter int SW    = STRB_WIDTH,
    parameter int MTW   = $clog2(MAX_THRESH),
    parameter int MXMTW = M * MTW
) (
    input  logic                         pclk,
    input  logic                         presetn,

    // Slave enable for addr decoding
    input  logic [S-1:0]                 SLAVE_ENABLE,
    // Slave address base
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_BASE,
    // Slave address limit
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_LIMIT,
    // Thresholds for the Weighted Round Robin Arbiter
    input  logic [MXMTW-1:0]             THRESHOLDS,

    // Master interfaces - These are from the APB master
    input  logic [M-1:0]                 m_apb_psel,
    input  logic [M-1:0]                 m_apb_penable,
    input  logic [M-1:0]                 m_apb_pwrite,
    input  logic [M-1:0][2:0]            m_apb_pprot,
    input  logic [M-1:0][ADDR_WIDTH-1:0] m_apb_paddr,
    input  logic [M-1:0][DATA_WIDTH-1:0] m_apb_pwdata,
    input  logic [M-1:0][STRB_WIDTH-1:0] m_apb_pstrb,
    output logic [M-1:0]                 m_apb_pready,
    output logic [M-1:0][DATA_WIDTH-1:0] m_apb_prdata,
    output logic [M-1:0]                 m_apb_pslverr,

    // Slave interfaces - these are to the APB destinations
    output logic [S-1:0]                 s_apb_psel,
    output logic [S-1:0]                 s_apb_penable,
    output logic [S-1:0]                 s_apb_pwrite,
    output logic [S-1:0][2:0]            s_apb_pprot,
    output logic [S-1:0][ADDR_WIDTH-1:0] s_apb_paddr,
    output logic [S-1:0][DATA_WIDTH-1:0] s_apb_pwdata,
    output logic [S-1:0][STRB_WIDTH-1:0] s_apb_pstrb,
    input  logic [S-1:0]                 s_apb_pready,
    input  logic [S-1:0][DATA_WIDTH-1:0] s_apb_prdata,
    input  logic [S-1:0]                 s_apb_pslverr
);
```

Note the port naming convention: lowercase (`m_apb_psel`, not `m_apb_PSEL`),
unlike `apb4_slave` / `apb4_master` and the generated crossbars.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| M | int | 2 | Number of APB masters (input side) |
| S | int | 4 | Number of APB slaves (output side) |
| ADDR_WIDTH | int | 32 | APB address bus width |
| DATA_WIDTH | int | 32 | APB data bus width |
| STRB_WIDTH | int | DATA_WIDTH/8 | APB write strobe width (derived) |
| MAX_THRESH | int | 16 | Sizes the per-master threshold field: `MTW = $clog2(MAX_THRESH)` |

**There is no `DEPTH` parameter.** The module contains no buffers.

**`MAX_THRESH` only sizes the field.** The arbiter is instantiated with
`MAX_LEVELS(16)` hardcoded, so changing `MAX_THRESH` changes the width of
`THRESHOLDS` without changing the arbiter's internal credit range. Leave it at
the default of 16 unless you have also reviewed
`rtl/common/arbiter_round_robin_weighted.sv`.

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| pclk | 1 | Input | APB clock |
| presetn | 1 | Input | APB active-low reset |

### Configuration Interface

All configuration is by **input signal**, not parameter, so the address map can
be reprogrammed at runtime.

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| SLAVE_ENABLE | S | Input | Per-slave enable bit; a disabled slave never matches |
| SLAVE_ADDR_BASE | S × ADDR_WIDTH | Input | Inclusive base address for each slave |
| SLAVE_ADDR_LIMIT | S × ADDR_WIDTH | Input | Inclusive limit address for each slave |
| THRESHOLDS | M × MTW | Input | Per-**master** arbitration weights |

**`THRESHOLDS` is a single per-master vector shared by every slave arbiter.**
There is no separate `MST_THRESHOLDS`/`SLV_THRESHOLDS` pair and no way to weight
masters differently on different slaves -- the same vector is wired to all `S`
arbiter instances.

### Master Interfaces (Input Side)

These are the crossbar's upstream ports; the crossbar behaves as an APB *slave*
on them. They are named `m_apb_*` because they connect to external APB masters.

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_apb_psel | M | Input | Master select signals |
| m_apb_penable | M | Input | Master enable signals |
| m_apb_pwrite | M | Input | Master write/read indicators |
| m_apb_pprot | M × 3 | Input | Master protection attributes |
| m_apb_paddr | M × ADDR_WIDTH | Input | Master addresses |
| m_apb_pwdata | M × DATA_WIDTH | Input | Master write data |
| m_apb_pstrb | M × STRB_WIDTH | Input | Master write strobes |
| m_apb_pready | M | Output | Ready returned to each master |
| m_apb_prdata | M × DATA_WIDTH | Output | Read data returned to each master |
| m_apb_pslverr | M | Output | Error returned to each master |

### Slave Interfaces (Output Side)

These are the crossbar's downstream ports; the crossbar behaves as an APB
*master* on them. They are named `s_apb_*` because they connect to external APB
slaves.

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_apb_psel | S | Output | Slave select signals |
| s_apb_penable | S | Output | Slave enable signals |
| s_apb_pwrite | S | Output | Slave write/read indicators |
| s_apb_pprot | S × 3 | Output | Slave protection attributes |
| s_apb_paddr | S × ADDR_WIDTH | Output | Slave addresses |
| s_apb_pwdata | S × DATA_WIDTH | Output | Slave write data |
| s_apb_pstrb | S × STRB_WIDTH | Output | Slave write strobes |
| s_apb_pready | S | Input | Ready from each slave |
| s_apb_prdata | S × DATA_WIDTH | Input | Read data from each slave |
| s_apb_pslverr | S | Input | Error from each slave |

### A Note on the `m_`/`s_` Prefixes

This convention is the opposite of the AMBA interconnect convention, in which an
interconnect's *slave* port faces an upstream master and its *master* port faces
a downstream slave. Here the prefix names **what is attached**, not what the
crossbar acts as:

- `m_apb_*` = the ports that external **m**asters attach to (crossbar acts as slave)
- `s_apb_*` = the ports that external **s**laves attach to (crossbar acts as master)

The port directions in the tables above are unambiguous; use them, not the
prefix, when wiring.

---

## Architecture

### Crossbar Topology

The crossbar provides full connectivity between all masters and slaves:

```
Master 0 ──┐
Master 1 ──┼── Crossbar ──┬── Slave 0
Master 2 ──┘    Switch    ├── Slave 1
   ...                    ├── Slave 2
                          └── ...
```

### Key Components

1. **Address Decoders** (S instances): combinational per-slave, per-master range match
2. **Weighted Round-Robin Arbiters** (S instances): one `arbiter_round_robin_weighted` per slave
3. **Grant-ACK Registers** (S × M flops): the only sequential logic in the datapath
4. **Slave-side Multiplexers** (S instances): select the granted master's APB signals
5. **Master-side Demultiplexers** (M instances): return `PREADY`/`PRDATA`/`PSLVERR` from the granted slave

There are no stubs, no command queues, no side queues, and no response FIFOs.

### Data Flow

```
APB Masters → Address Decode → Per-Slave Arbitration → Slave Mux → APB Slaves

APB Slaves → Master Demux (by grant) → APB Masters
```

Both directions are combinational. The only registers are the per-slave,
per-master grant-ACK flops.

---

## Functionality

### Address Decoding

Each slave is assigned an address range defined by:

- **SLAVE_ADDR_BASE[s]**: inclusive starting address for slave s
- **SLAVE_ADDR_LIMIT[s]**: inclusive ending address for slave s
- **SLAVE_ENABLE[s]**: enable bit for slave s

Address matching is fully combinational and evaluated for every (slave, master)
pair:

```systemverilog
master_sel[s][m] = m_apb_psel[m] && SLAVE_ENABLE[s] &&
                   (m_apb_paddr[m] >= SLAVE_ADDR_BASE[s]) &&
                   (m_apb_paddr[m] <= SLAVE_ADDR_LIMIT[s]);
```

Because base and limit are independent runtime inputs, sparse and non-uniform
maps are supported -- unlike the generated crossbars, which use fixed uniform
64 KB regions.

**Overlapping ranges are not detected.** If two enabled slaves both match an
address, both arbiters will see a request and both slaves will be selected. The
master-side demultiplexer then returns whichever match it encounters last in its
loop. Ensure the programmed ranges are disjoint.

### Weighted Round-Robin Arbitration with ACK Mode

Each slave has an independent arbiter:

```systemverilog
arbiter_round_robin_weighted #(
    .MAX_LEVELS  (16),
    .CLIENTS     (M),
    .WAIT_GNT_ACK(1)
) arbiter_inst (
    .max_thresh  (THRESHOLDS),
    .request     (master_sel[s]),
    .grant_valid (arb_gnt_valid[s]),
    .grant       (arb_gnt[s]),
    .grant_id    (arb_gnt_id[s]),
    .grant_ack   (arb_gnt_ack[s])
);
```

- **`WAIT_GNT_ACK=1`**: the grant is held until acknowledged, so it persists for
  the whole APB transfer and the transaction is atomic.
- **Grant ACK** is registered and asserted the cycle after the transfer
  completes on that slave:

  ```systemverilog
  arb_gnt_ack[s][m] <= arb_gnt[s][m] && s_apb_pready[s] &&
                       s_apb_psel[s]  && s_apb_penable[s];
  ```

- **Weighting**: `THRESHOLDS` gives each master a credit allowance, so a
  higher-weighted master wins more often across a rotation while still being
  starvation-free.

---

## Timing Characteristics

### Latency

`apb_xbar_thin` adds **zero cycles** of latency. The master's `PSEL`, `PENABLE`,
`PADDR`, `PWDATA`, `PSTRB` and `PPROT` reach the selected slave combinationally,
and `PREADY`, `PRDATA` and `PSLVERR` return combinationally. An uncontended
transfer completes in exactly the downstream slave's own transfer time.

The cost is timing, not cycles:

| Path | Description |
|------|-------------|
| Master `PADDR` → decode → arbiter request → grant → slave mux → `s_apb_paddr` | Forward combinational path |
| `s_apb_pready` → master demux (indexed by grant) → `m_apb_pready` | Return combinational path |

Both paths scale with M and S. On FPGA targets this is normally the critical path
of any design instantiating a large `apb_xbar_thin`. If timing does not close,
use a generated crossbar from [apb_crossbar.md](apb_crossbar.md), which breaks
these paths with registers, or register the crossbar's boundaries externally.

### Arbitration Turnaround

Because `grant_ack` is registered, the arbiter releases a grant one cycle after
the transfer completes. Back-to-back transfers from *different* masters to the
same slave therefore see one dead cycle between them. Transfers to *different*
slaves proceed fully in parallel.

### Throughput

| Metric | Value | Conditions |
|--------|-------|------------|
| Added latency | 0 cycles | Any configuration |
| Concurrent transfers | Up to min(M, S) | Distinct slaves, no address conflict |
| Same-slave turnaround | 1 dead cycle | Master change; registered grant ACK |

No synthesis frequency or area figures are published for this module -- none have
been measured in this repository.

---

## Usage Example

### 3 Masters, 4 Slaves with a Sparse Address Map

```systemverilog
localparam int M = 3;
localparam int S = 4;

logic [S-1:0]             slave_enable;
logic [S-1:0][31:0]       slave_base;
logic [S-1:0][31:0]       slave_limit;
logic [M-1:0][3:0]        thresholds;

always_comb begin
    // Sparse, non-uniform map -- ranges need not be contiguous or equal-sized
    slave_enable = 4'b1111;

    slave_base[0]  = 32'h4000_0000;  slave_limit[0] = 32'h4000_0FFF;  //  4 KB
    slave_base[1]  = 32'h4001_0000;  slave_limit[1] = 32'h4001_FFFF;  // 64 KB
    slave_base[2]  = 32'h5000_0000;  slave_limit[2] = 32'h500F_FFFF;  //  1 MB
    slave_base[3]  = 32'h6000_0000;  slave_limit[3] = 32'h6000_00FF;  // 256 B

    // Per-master weights: master 0 gets the largest share
    thresholds[0] = 4'hC;
    thresholds[1] = 4'h4;
    thresholds[2] = 4'h4;
end

apb_xbar_thin #(
    .M          (M),
    .S          (S),
    .ADDR_WIDTH (32),
    .DATA_WIDTH (32),
    .MAX_THRESH (16)
) u_xbar (
    .pclk             (apb_clk),
    .presetn          (apb_resetn),

    .SLAVE_ENABLE     (slave_enable),
    .SLAVE_ADDR_BASE  (slave_base),
    .SLAVE_ADDR_LIMIT (slave_limit),
    .THRESHOLDS       (thresholds),

    // Upstream: external APB masters
    .m_apb_psel       (mst_psel),
    .m_apb_penable    (mst_penable),
    .m_apb_pwrite     (mst_pwrite),
    .m_apb_pprot      (mst_pprot),
    .m_apb_paddr      (mst_paddr),
    .m_apb_pwdata     (mst_pwdata),
    .m_apb_pstrb      (mst_pstrb),
    .m_apb_pready     (mst_pready),
    .m_apb_prdata     (mst_prdata),
    .m_apb_pslverr    (mst_pslverr),

    // Downstream: external APB slaves
    .s_apb_psel       (slv_psel),
    .s_apb_penable    (slv_penable),
    .s_apb_pwrite     (slv_pwrite),
    .s_apb_pprot      (slv_pprot),
    .s_apb_paddr      (slv_paddr),
    .s_apb_pwdata     (slv_pwdata),
    .s_apb_pstrb      (slv_pstrb),
    .s_apb_pready     (slv_pready),
    .s_apb_prdata     (slv_prdata),
    .s_apb_pslverr    (slv_pslverr)
);
```

### Runtime Address Map Reprogramming

Because `SLAVE_ADDR_BASE`, `SLAVE_ADDR_LIMIT` and `SLAVE_ENABLE` are inputs, a
control register block can rewrite the map at runtime:

```systemverilog
always_ff @(posedge apb_clk or negedge apb_resetn) begin
    if (!apb_resetn) begin
        slave_enable <= '0;                 // decode nothing until programmed
    end else if (cfg_write) begin
        case (cfg_addr)
            12'h000: slave_base[0]  <= cfg_wdata;
            12'h004: slave_limit[0] <= cfg_wdata;
            12'h008: slave_enable   <= cfg_wdata[S-1:0];
            // ... one base/limit pair per slave
            default: ;                      // no change
        endcase
    end
end
```

**Reprogram only while idle.** The decode is combinational with no shadowing, so
changing a base or limit mid-transfer can re-decode a transaction that has
already been granted, moving `PSEL` to a different slave partway through and
breaking the transfer. Quiesce all masters, or hold `SLAVE_ENABLE` low, before
rewriting the map.

---

## Known Limitations

### Unmapped Addresses Stall the Bus

There is no default slave and no decode-error response. If no enabled slave
matches, `master_sel[s][m]` is low for every `s`, no arbiter raises a grant, and
the master-side demultiplexer leaves `m_apb_pready[m]` at its default of `1'b0`.
`PREADY` is never asserted and **the transfer hangs indefinitely.** There is no
timeout.

This is the same limitation as the generated crossbars -- see
[apb_crossbar.md](apb_crossbar.md).

**Mitigation:** hold `SLAVE_ENABLE` such that the programmed ranges cover every
address a master can emit, or place an address filter with an error slave
upstream of the crossbar.

### Other Limitations

| Limitation | Detail |
|------------|--------|
| Overlapping ranges | Not detected; multiple slaves may be selected simultaneously |
| `MAX_THRESH` | Sizes `THRESHOLDS` only; the arbiter's `MAX_LEVELS` is hardcoded to 16 |
| Shared weights | One `THRESHOLDS` vector drives all `S` arbiters; per-slave weighting is not possible |
| Combinational paths | Forward and return paths both scale with M and S; usually the design's critical path |
| No monitoring | No `monbus` instrumentation, transaction counters, or timeout detection |

---

## Synthesis Considerations

### Area

Area is dominated by the address comparators and the multiplexers:

| Structure | Scaling |
|-----------|---------|
| Address comparators | O(M × S × ADDR_WIDTH) -- two comparators per pair |
| Arbiters | O(S) instances, each O(M) |
| Grant-ACK registers | O(M × S) flops |
| Slave-side muxes | O(S × M × (ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 6)) |
| Master-side demuxes | O(M × S × (DATA_WIDTH + 2)) |

The `M × S` terms dominate quickly. A large configuration (say M=6, S=12 at
DATA_WIDTH=64) is substantially more logic than the numbers of masters and slaves
suggest; budget for it before committing to a topology.

### Timing

- Register the crossbar's boundaries externally if the combinational paths do not close
- Reduce M and S to the minimum required -- both forward and return paths scale with them
- Consider a hierarchy of small crossbars instead of one large one
- If timing still fails, switch to a generated crossbar, which is registered by construction

---

## Verification

### Formal

SymbiYosys proofs are checked in at `formal/apb_xbar/apb_xbar_thin/`, with
`prove` and `cover` tasks.

### Simulation

`apb_xbar_thin` has no dedicated CocoTB testbench. The four generated variants in
`projects/components/apb_xbar/dv/tests/` do, but they exercise the *other*
architecture and provide no coverage of this module. Weigh that when selecting
between the two families.

### Suggested Coverage

- All M×S path combinations
- Address decoding at every range boundary (base, base-1, limit, limit+1)
- `SLAVE_ENABLE` masking
- Arbitration fairness and weighting under sustained contention
- Grant persistence across a slave's wait states
- Reset behaviour with a transfer in flight

---

## Related Modules

- **apb_xbar_1to1 / 2to1 / 1to4 / 2to4**: fixed-configuration generated crossbars ([apb_crossbar.md](apb_crossbar.md))
- **apb4_master**: APB master, used by the generated crossbars ([apb4_master.md](apb4_master.md))
- **apb4_slave**: APB slave, used by the generated crossbars ([apb4_slave.md](apb4_slave.md))
- **arbiter_round_robin_weighted**: the per-slave arbiter instantiated here
- **arbiter_round_robin**: plain round-robin used by the generated crossbars
- **apb4_monitor**: APB protocol monitoring ([apb4_monitor.md](../apb/apb4_monitor.md))

**Dependencies:**

- `rtl/common/arbiter_round_robin_weighted.sv`
- `rtl/common/arbiter_priority_encoder.sv` (arbiter dependency)

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to APB Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
