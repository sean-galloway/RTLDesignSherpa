# 2.13 Run Address Generator (stream_run_addr_gen)

`stream_run_addr_gen` produces the address sequence the scheduler consumes for
an extended (TASK-101) descriptor. It wraps one `dma_address_gen` plus a base
FIFO, and exists only when the scheduler is built with
`USE_ROW_COL_MAJOR_ADDRESSING != 0` -- the generate block is elided otherwise,
so a build without extended addressing carries none of this logic.

The scheduler instantiates **two** of them, one per direction. That is what
lets a transpose read with bursts down the contiguous side while writing
single beats down the strided side, or the reverse.

## 2.13.1 The Two Modes

Mode is per direction, selected by `cfg_per_beat`.

**Run-contiguous** (`cfg_per_beat = 0`, `stride_0 == beat_size`). The transfer
is a set of runs of `inner_count` contiguous beats, and the AXI engine bursts
within a run. One base is emitted per run:

    run_base(k) = base + k * stride_1

Linear copies, 2-D tiled contiguous copies, circular buffers and reverse copies
all land here.

**Per-beat 2-D** (`cfg_per_beat = 1`, `stride_0 != beat_size`). There is no
contiguous run to burst, so every beat gets its own address and the AXI side
issues single beats:

    addr(b) = base + i0*stride_0 + i1*stride_1
    i0 = b % inner_count   (inner, fastest)
    i1 = b / inner_count

Transpose and arbitrary scatter/gather use this. The scheduler drives
`sched_*_beats = 1` for a direction in this mode.

## 2.13.2 Position 0 Is Not Emitted

The generator emits **positions 1..N-1 only**. Position 0 -- run 0 or beat 0 --
is the descriptor's own address, which the scheduler already holds and loads
directly, so re-deriving it here would be redundant work on the arbitration
path. On `start` the covered-beat counter is preloaded to account for it
(`r_gen_beats <= 1` in per-beat mode, `inner_count` in run mode), and
generation stops once the covered count reaches `cfg_total_beats`.

A consumer that expects the first address on this interface will be off by one
run. The first address comes from the descriptor.

`cfg_inner_count = 0` is treated as 1 rather than rejected, so a descriptor
that leaves the field clear degrades to one beat per run instead of stalling.

## 2.13.3 Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 64 | Address width |
| `STRIDE_WIDTH` | 32 | Signed byte stride width; strides are signed, which is what makes reverse copies work |
| `INDEX_WIDTH` | 16 | Dimension index and `inner_count` width |
| `FIFO_DEPTH` | 4 | Address prefetch depth |
| `BEATS_WIDTH` | 32 | Total-beats and inner-count counter width |

: stream_run_addr_gen Parameters

The scheduler instantiates it with `STRIDE_WIDTH` and `INDEX_WIDTH` taken from
`STREAM_ADDRGEN_STRIDE_WIDTH` / `STREAM_ADDRGEN_INDEX_WIDTH`, and pins
`FIFO_DEPTH = 4`, `BEATS_WIDTH = 32`.

## 2.13.4 Ports

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `clk` | 1 | Input | Clock |
| `rst_n` | 1 | Input | Active-low reset |
| `start` | 1 | Input | New extended descriptor: sample the `cfg_*` inputs and re-arm generation |
| `cfg_per_beat` | 1 | Input | 1 = per-beat 2-D, 0 = run-contiguous |
| `cfg_base_addr` | ADDR_WIDTH | Input | Beat/run 0 base, i.e. the descriptor's src or dst address |
| `cfg_stride_0` | STRIDE_WIDTH | Input | Inner (index_0) byte stride, signed |
| `cfg_stride_1` | STRIDE_WIDTH | Input | Outer (index_1) byte stride, signed |
| `cfg_wrap_mask_0` | ADDR_WIDTH | Input | Inner wrap mask; 0 = no wrap |
| `cfg_wrap_mask_1` | ADDR_WIDTH | Input | Outer wrap mask; 0 = no wrap |
| `cfg_inner_count` | INDEX_WIDTH | Input | index_0 extent; 0 is treated as 1 |
| `cfg_total_beats` | BEATS_WIDTH | Input | Descriptor length in beats |
| `o_base_valid` | 1 | Output | An address is available |
| `i_base_ready` | 1 | Input | Scheduler accepts the address |
| `o_base_addr` | ADDR_WIDTH | Output | Next run base, or next beat address in per-beat mode |

: stream_run_addr_gen Ports

All `cfg_*` inputs are sampled on `start` and held for the descriptor; changing
them mid-transfer has no effect.
