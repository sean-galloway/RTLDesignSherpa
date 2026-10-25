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

# gaxi_age_fifo_sync

**Module:** `gaxi_age_fifo_sync.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** New (2026-10-25)

---

## Overview

`gaxi_fifo_sync` with an age beside every entry. The writer hands over an age with the data; a shared `age_dec` strobe walks every valid entry's `age_cnt` one step toward zero, where it stops. Each entry also carries an `age_thresh` flop that, for every valid entry, is 1 exactly when its `age_cnt` is 0. The read side gets the head's `age_cnt`, the head's `age_thresh`, and `youngest`, the largest `age_cnt` still live in the queue.

The shape comes from a scheduler with N per-bank queues. Each new entry is written with an age one above the largest `youngest` across the N queues, or equal to it when `age_dec` is high in the same cycle, and every queue sees `age_dec` whenever any queue retires an entry. An entry's `age_cnt` is then how many retirements it still has to wait through before nothing in the pool is older than it, and `rd_age_thresh` tells the scheduler that a queue's head has waited that long.

### Key Features

- **Same FIFO underneath:** `counter_bin` pointers and `fifo_control` flags as `gaxi_fifo_sync`; any `DEPTH >= 2`
- **Ages and thresh flags in flops, data in memory:** every valid age updates in the same cycle, so the age column cannot live in a RAM
- **Saturating decrement:** an `age_cnt` at zero stays at zero
- **`age_thresh` from the next state:** it rises at the edge where `age_cnt` reaches 0 (`age_cnt == 1` with `age_dec`, or a write of age 0), so the head's flag is a flop, not a compare off the counter
- **`youngest` is a max tree:** ceil(log2(DEPTH)) comparators deep, over the valid entries only; it does not depend on the writer keeping any age discipline
- **Mux read only:** the age outputs are combinational off the registers and change the cycle after the edge that updated them

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `DATA_WIDTH` | int | 4 | Width of `wr_data` / `rd_data` |
| `AGE_WIDTH` | int | 8 | Width of the age counters |
| `DEPTH` | int | 4 | Entries. Any value >= 2; power of two optimal. `DEPTH=1` does not elaborate |
| `DW`, `AGEW`, `D`, `AW` | int | derived | Shorthands; do not override |

---

## Ports

```systemverilog
module gaxi_age_fifo_sync #(
    parameter int DATA_WIDTH = 4,
    parameter int AGE_WIDTH  = 8,
    parameter int DEPTH      = 4,
    parameter int DW   = DATA_WIDTH,
    parameter int AGEW = AGE_WIDTH,
    parameter int D    = DEPTH,
    parameter int AW   = $clog2(DEPTH)
) (
    input  logic            axi_aclk,
    input  logic            axi_aresetn,
    input  logic            age_dec,  // step every valid age toward 0
    input  logic            wr_valid,
    output logic            wr_ready,       // not full
    input  logic [DW-1:0]   wr_data,
    input  logic [AGEW-1:0] wr_data_age,
    input  logic            rd_ready,
    output logic [AW:0]     count,
    output logic [AGEW-1:0] youngest,       // largest age among valid entries
    output logic            rd_valid,       // not empty
    output logic [DW-1:0]   rd_data,
    output logic [AGEW-1:0] rd_data_age,
    output logic            rd_age_thresh   // head age has saturated at 0
);
```

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | Clock |
| `axi_aresetn` | input | 1 | Async active-low reset |
| `age_dec` | input | 1 | Strobe: every valid entry's `age_cnt` steps toward 0 at this edge |
| `wr_valid` | input | 1 | Write handshake |
| `wr_ready` | output | 1 | Not full |
| `wr_data` | input | `[DW-1:0]` | Entry payload |
| `wr_data_age` | input | `[AGEW-1:0]` | Age stored with the entry, as given; the writer applies the `age_dec` term |
| `rd_ready` | input | 1 | Read handshake |
| `count` | output | `[AW:0]` | Occupancy. Off the next pointers, so it already includes this cycle's handshakes (as `gaxi_fifo_sync` mux mode) |
| `youngest` | output | `[AGEW-1:0]` | Largest age among the valid entries; 0 when empty |
| `rd_valid` | output | 1 | Not empty |
| `rd_data` | output | `[DW-1:0]` | Head payload |
| `rd_data_age` | output | `[AGEW-1:0]` | Head `age_cnt`; meaningful only while `rd_valid` (a retired slot's stale age shows otherwise) |
| `rd_age_thresh` | output | 1 | `rd_valid` and the head's `age_thresh` flop (its `age_cnt` is 0) |

---

## Functional Description

### Age lifecycle

1. **Write.** The entry takes `wr_data_age` exactly; its `age_thresh` is set if that age is 0. The writer owns the same-cycle term: `youngest + 1`, or `youngest` when `age_dec` is high, because the arriving entry is in the pool at the same edge as that retirement and has one fewer to wait for.
2. **Wait.** Each `age_dec` edge subtracts one from every entry that was valid before it and whose `age_cnt` is above zero. Zero holds. The edge that takes an `age_cnt` from 1 to 0 also sets that entry's `age_thresh` (`age_thresh_d = age_cnt == 1 && age_dec`), so flag and counter agree on every cycle: for every valid entry `age_thresh == (age_cnt == 0)`.
3. **Head.** `rd_data_age` is the head's `age_cnt` and `rd_age_thresh` is the head's `age_thresh` gated by `rd_valid`.
4. **Read.** The slot's valid bit clears; its age and flag are left in place and overwritten by the next write to that slot.

A write and a read in one cycle always touch different slots (the same slot would need full and empty at once), so neither disturbs the other's age.

**Why the writer's `age_dec` term matters.** The RTL review (2026-10-25) ran a writer that always presents `youngest + 1`, with `age_dec` on every retirement, under continuous write+retire on one queue: occupancy stayed at one while the head's age climbed by one per cycle, wrapped at `2**AGE_WIDTH`, and the wrapped entry would have jumped ahead of genuinely older entries in other queues. Each write that coincides with a retire was landing one above where it belonged. With the term (`youngest` when `age_dec` is high) an entry's `age_cnt` is exactly its rank plus one under that discipline; the testbench's pool phases check that on every cycle, and the same test with the term switched off fails within a dozen cycles.

### Valid mask and `youngest`

A valid bit is kept per slot (set on write, cleared on read) rather than derived from the pointers, so the mask is exact at a non-power-of-two `DEPTH` and the max tree needs no pointer arithmetic. The tree pads `DEPTH` up to a power of two with zero leaves, masks invalid slots to zero, and reduces pairwise. Each level of the tree is a separate array in its own generate scope: a single array holding every level is a combinational loop to Verilator (`UNOPTFLAT`) even though no node feeds itself.

If the writer keeps the one-above-the-pool discipline, the ages inside one queue are non-decreasing from head to tail and `youngest` is simply the tail's age. The tree is kept so the output is right under any writer; at the depths bank queues use (4 to 8) it is two or three comparator levels, four at `DEPTH=11`.

### Architecture

The write side drops `wr_data` into the memory array and `wr_data_age` into the age flop at the write address, and sets that slot's valid bit. The two `counter_bin` pointers and `fifo_control` are the `gaxi_fifo_sync` skeleton unchanged. The read side muxes the head's data and age off the read address; `youngest` is the max tree over the masked age column.

---

## Timing Characteristics

| Path | Latency |
|------|---------|
| Write to `rd_valid` | 1 cycle |
| `age_dec` to `rd_data_age` / `youngest` / `rd_age_thresh` | 1 cycle (register update, mux read) |
| `age_dec` with a write in the same cycle | the arriving entry stores `wr_data_age` as given; the writer presents `youngest`, not `youngest + 1` |
| Throughput | 1 entry per cycle on each side |

---

## Usage Example

Two bank queues sharing one age pool. Each write carries one above the larger `youngest`, or that `youngest` itself when a retirement is happening in the same cycle; each queue is decremented whenever either queue retires an entry.

```systemverilog
logic [AGEW-1:0] w_youngest [2];
logic            w_rd_fire  [2];
logic [AGEW-1:0] w_pool_youngest;
logic            w_any_retire;

assign w_pool_youngest = (w_youngest[0] > w_youngest[1]) ? w_youngest[0] : w_youngest[1];
assign w_any_retire    = w_rd_fire[0] | w_rd_fire[1];

for (genvar b = 0; b < 2; b++) begin : g_bank
    gaxi_age_fifo_sync #(
        .DATA_WIDTH (CMD_W),
        .AGE_WIDTH  (AGEW),
        .DEPTH      (4)
    ) u_bank_q (
        .axi_aclk      (clk),
        .axi_aresetn   (rst_n),
        .age_dec (w_any_retire),
        .wr_valid      (w_push_valid[b]),
        .wr_ready      (w_push_ready[b]),
        .wr_data       (w_push_cmd[b]),
        .wr_data_age   (w_any_retire ? w_pool_youngest : w_pool_youngest + 1'b1),
        .rd_ready      (w_pick[b]),
        .count         (),
        .youngest      (w_youngest[b]),
        .rd_valid      (w_head_valid[b]),
        .rd_data       (w_head_cmd[b]),
        .rd_data_age   (w_head_age[b]),
        .rd_age_thresh (w_head_oldest[b])
    );
    assign w_rd_fire[b] = w_head_valid[b] & w_pick[b];
end
```

---

## Design Notes

**`count` leads by a cycle.** It is `fifo_control`'s combinational count off the next pointers, the same as `gaxi_fifo_sync` with `REGISTERED=0`: while a write is being accepted, `count` already shows it. `wr_ready` and `rd_valid` are registered flags and do not lead. The testbench models exactly this.

**The writer rule ties at zero.** If `youngest` is 0 (an entry already saturated, which out-of-order retirement makes common) and `age_dec` is high, the writer presents 0 and the new entry lands level with the saturated one rather than behind it. Saturation already produces ties at 0, so the scheduler has to break them regardless; a writer that wants the new entry strictly behind uses `youngest + 1 - (age_dec && youngest != 0)`. The test's rank check models in-order retirement, where `youngest` is never 0 while the queue is occupied, so it does not exercise this case.

**`wr_data_age` saturates at the writer.** The FIFO stores whatever it is given; a writer computing `youngest + 1` must clamp at `2**AGE_WIDTH - 1` itself (the example above does not, so it needs `AGE_WIDTH` wide enough for the pool).

**No `REGISTERED` mode.** A registered head copy would need its own decrement path to stay in step with the age column. Add one if a consumer needs it; do not register `rd_data` alone.

---

## Related Modules

- [gaxi_fifo_sync](gaxi_fifo_sync.md) - The FIFO this extends; same pointers, flags and storage
- [gaxi_drop_fifo_sync](gaxi_drop_fifo_sync.md) - The other `gaxi_fifo_sync` variant, drop instead of age
- [GAXI Index](index.md)

---

## Testing

`val/amba/test_gaxi_age_fifo_sync.py` is the runner (grid and `run()` only). The test is `GaxiAgeFifoTB.run_suite` in `bin/TBClasses/gaxi/gaxi_age_fifo.py`, which drives both ports through `bin/TBClasses/gaxi/gaxi_age_bfm.py`: `GaxiAgeMaster` and `GaxiAgeSlave` are the framework GAXI master and slave bound to the age-carrying ports (multi-signal mode, age as a second field), and `GaxiAgePoolDriver` is the one-queue mirror of the N-bank wrapper (the retire strobe and the live writer rule). It runs under FlexConfigGen timing profiles and strobes `age_dec` randomly or on each read. A reference model is advanced every cycle from the sampled inputs and every output is compared against it every cycle, so ages, `youngest`, `rd_age_thresh`, `count` and `wr_ready` are checked between handshakes as well as at them. Hold phases fill the FIFO with reads parked and strobe past the largest age so every entry is seen saturating. Pool phases mirror the one-queue wrapper, `wr_data_age = youngest + 1` (or `youngest` with `age_dec`) driven live and `age_dec` on each retirement, with bursts so writes coincide with retirements, and check that every entry's age equals its rank plus one; that check fails within a dozen cycles when the writer's `age_dec` term is removed (`POOL_WRITER_DEC_TERM=0`), which is the mutation that justifies it. The verdict carries counts: writes, reads, decrements, saturated-head cycles, full cycles, same-cycle write+read and decrement-in-write cycles must all be non-zero.

```bash
REG_LEVEL=GATE pytest val/amba/test_gaxi_age_fifo_sync.py -v   # 1 cell
REG_LEVEL=FUNC pytest val/amba/test_gaxi_age_fifo_sync.py -v   # 4 cells, depths 4/5/8
REG_LEVEL=FULL pytest val/amba/test_gaxi_age_fifo_sync.py -v   # 48 cells
```

---

**Version:** 1.0
**Last Updated:** 2026-10-25

## References

- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022, Issue H, 2020, sec. A3.2.1 "Handshake process" - the valid/ready contract on both ports.
- Rixner, S. et al. "Memory Access Scheduling." *ISCA*, 2000 - the oldest-first tie-break the age column exists to serve.

---

## Navigation

- **[← Back to GAXI Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
