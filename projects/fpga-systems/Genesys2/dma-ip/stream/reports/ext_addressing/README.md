# STREAM Extended-Addressing Characterization

_**Template — measured in cocotb simulation at reduced tile sizes.** Regenerate from a board sweep (`stream_ext_char.py`) for real numbers._

Characterization of STREAM's TASK-101 `dma_address_gen` addressing (`USE_ROW_COL_MAJOR_ADDRESSING=1`) across the four read/write traversal combinations. Separate from the legacy (contiguous) characterization.

## Addressing modes

`row` = row-major = contiguous inner dimension (`stride_0 = beat_size`) so the AXI engine **bursts**. `col` = column-major = strided inner (`stride_0 = row_pitch`) so each beat is its own **single-beat** AXI transaction (`arlen/awlen = 0`). Read and write are independent, giving four combinations:

| Mode | Meaning |
|------|---------|
| row/row | 2D-tiled contiguous copy (read burst, write burst) |
| row/col | transpose (read rows burst, write columns single-beat) |
| col/row | transpose mirror (read columns single-beat, write rows burst) |
| col/col | column-major copy (read single-beat, write single-beat) |

## Method

Each (mode, size) runs one extended descriptor over a WxH tile through the named `Stream` host API, with the RD/WR datapath perf windows open. Throughput is `byte_count / bucket_total x clk` (bucket_total = PROD+BP+STARV+IDLE, the closed-window length); utilization is the productive fraction. The read/write **data** stream is identical across modes (only addresses differ), so the differences are purely the addressing cost. Clock: 100 MHz.

## Throughput vs. size

### 8 x 8 tile (64 beats)

| Mode | RD GB/s | WR GB/s | RD util | WR util | RD avg burst | WR avg burst | status |
|------|--------:|--------:|--------:|--------:|-------------:|-------------:|:------:|
| row/row | 1.552 | 1.403 | 0.97 | 0.88 | 8.0 | 8.0 | ok |
| row/col | 1.552 | 0.264 | 0.97 | 0.16 | 8.0 | 1.0 | ok |
| col/row | 0.322 | 0.335 | 0.20 | 0.21 | 1.0 | 8.0 | ok |
| col/col | 0.322 | 0.264 | 0.20 | 0.16 | 1.0 | 1.0 | ok |

### 16 x 16 tile (256 beats)

| Mode | RD GB/s | WR GB/s | RD util | WR util | RD avg burst | WR avg burst | status |
|------|--------:|--------:|--------:|--------:|-------------:|-------------:|:------:|
| row/row | 1.588 | 1.540 | 0.99 | 0.96 | 16.0 | 16.0 | ok |
| row/col | 1.588 | 0.266 | 0.99 | 0.17 | 16.0 | 1.0 | ok |
| col/row | 0.321 | 0.939 | 0.20 | 0.59 | 1.0 | 16.0 | ok |
| col/col | 0.321 | 0.266 | 0.20 | 0.17 | 1.0 | 1.0 | ok |

## Findings

- **Burst vs. single-beat** is the dominant effect: `row` directions sustain full-burst throughput; `col` directions are single-beat and run far lower (no burst amortization of AR/AW latency).
- **`row/row`** is the efficient contiguous 2D copy; **`col/col`** is the worst case (both sides single-beat).
- **Transpose** (`row/col`, `col/row`) shows the asymmetry: the burst side keeps up while the strided side is single-beat, so aggregate throughput is gated by the strided direction.
- `avg burst` beats/transaction quantifies it directly: ~16 (the configured max) for burst directions, 1 for single-beat.

