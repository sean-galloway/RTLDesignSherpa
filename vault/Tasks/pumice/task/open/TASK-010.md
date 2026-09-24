# TASK-010: no generator config can show RBL a win, and the harness is what blocks it

**Status:** open 2026-09-24  **Priority:** P3 — characterization capability, no
correctness impact

Raised by Sean 2026-09-24 off the [[TASK-002]] pair sweep: *"explore if it is
possible with the current generators to show benefit for rbl_static. RBL-static
doesn't sound good though, I would expect RBL to have some dynamic capabilities
to it."*

## Answer: not with the harness as written, and the hardware is not the reason

RBL (`pumice_rbl_table`, modes 6/7) keeps a per-row miss counter and
auto-precharges rows it classifies as low-locality. **Its target workload is
per-row locality VARIATION** -- some rows hot and worth holding open, others
one-shot and worth closing immediately. Against a uniform pattern there is
nothing to discriminate, so a per-row predictor cannot beat a global policy:
whatever the right answer is, it is the same answer for every row, and open
page already gives it.

Every workload measured so far is uniform. `measure_concurrent` builds all
generator programs from ONE `Scenario` (`_prog(idx)`, pumice_char.py): stride,
wrap, burst_len, gap and id_mode are shared, and the only per-generator
difference is `start_addr`. So N generators run the same pattern at different
offsets -- which is more traffic, not more VARIETY.

**The hardware already supports what is needed.** `program_wr_engine` /
`program_rd_engine` take `gen=N` and a full per-generator stride/wrap/burst
config, and chargen_regs carries sixteen independent generator config blocks on
a 0x40 stride. Nothing in the RTL or the driver prevents generator 0 streaming
one row while generator 1 walks rows. Only `_prog()` collapsing to a single
Scenario does.

**The generator RTL does NOT need changing, and one generator can never do it.**
`dma_address_gen` is a 2D affine engine:

    addr = base + (index_0 * stride_0 & wrap_0) + (index_1 * stride_1 & wrap_1)

That is the right primitive. But affine is UNIFORM ACROSS ROWS by construction:
if `wrap_0` confines the inner index inside a row, every row receives exactly
the same number of accesses. No setting of the four knobs makes some rows hot
and others one-shot, so the discriminating workload cannot come from a cleverer
single program -- it has to come from TWO generators programmed differently
(one confined inside a row, one striding across rows). The hardware already
allows that; only the host collapses it.

**What to do:** let `measure_concurrent` take a per-generator Scenario override
(a list, defaulting to the single scenario it has now), then build the
discriminating workload: one generator with high row locality against one
thrashing, on disjoint banks via `placement="banks"`. That is the first
workload on which RBL could beat plain open page, and the first on which its
failure would mean something.

## Sean's read on static-vs-dynamic is supported by the data already taken

A fixed threshold cannot adapt to a workload whose locality changes, and the
pair sweep shows exactly that asymmetry -- `col_major_interleaved`, concurrent
1w+1r, three reps:

| mode | MB/s | hit% | ACT/txn |
|---|---|---|---|
| plain open_page | 98.3 | 81.3% | 3.00 |
| `rbl_dyn` (mode 7, hill-climbs) | 97.8 | 81.0% | 3.03 |
| `rbl_static` (mode 6, fixed) | **55.8** | **44.0%** | **8.96** |

**Only the STATIC variant regresses.** rbl_dyn is within noise of plain open
page on the same workload, because its per-epoch threshold hill-climb walks the
threshold away from the value that was mispredicting. The dynamic capability is
what keeps it out of trouble; the static one has no way back once its fixed
threshold is wrong for the traffic.

So mode 6 is arguably not worth showing a win for -- the question to settle is
whether it earns its place at all beside mode 7, which costs the same table and
adapts. That is a cheaper question than building a workload to flatter it, and
it should be answered first.
