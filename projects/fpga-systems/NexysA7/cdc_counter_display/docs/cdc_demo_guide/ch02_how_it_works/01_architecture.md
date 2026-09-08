# How It Works

## Top-level structure (`cdc_demo_top`)

The board top instantiates, from UART inward:

1. **`uart_axil_bridge`** — decodes the ASCII `W <addr> <data>` / `R <addr>`
   protocol into single-beat AXI4-Lite. `CLKS_PER_BIT` is derived from
   `SYS_CLK_HZ / 115200`.
2. **`cdc_demo_harness`** — the AXI4-Lite CSR slave (Chapter 5). Stores per-counter
   config, exposes CDC'd status, and generates single-cycle pulses (`CFG_LOAD`,
   `HOST_PRESS`).
3. **Clocking tree** — an `MMCME2_BASE` produces four co-prime divided clocks;
   per counter a `BUFGMUX_CTRL` tree glitchlessly selects one of five sources.
4. **Four `cdc_counter_domain` instances** — the counters and their CDC paths.
5. **Display** — `DISP_SELECT` picks which counter's value drives the 7-seg.

## Clocking and the four source clocks

The MMCM synthesizes four **mutually asynchronous** clocks from the 100 MHz
reference using pairwise co-prime divisors, plus a per-counter sys_clk-derived
divided clock:

| `clock_select` | Source | Frequency |
|:---:|--------|-----------|
| 0 | MMCM CLKOUT0 (÷11) | 72.7 MHz |
| 1 | MMCM CLKOUT1 (÷29) | 27.6 MHz |
| 2 | MMCM CLKOUT2 (÷67) | 11.9 MHz |
| 3 | MMCM CLKOUT3 (÷128) | 6.25 MHz |
| 4 | `clock_divider` (uses `div_pickoff`) | `sys_clk / 2^(pickoff+1)` |

: Per-counter clock sources

The co-prime divisors `{11, 29, 67, 128}` mean no two outputs share an edge
alignment for a very long time — for CDC purposes, truly asynchronous. The
divided-clock branch (select 4) keeps a slow, visibly-counting rate available for
the "watch it count" demo; `div_pickoff = 23` gives roughly 6 Hz.

## One counter domain (`cdc_counter_domain`)

Each counter lives entirely in its `ctr_clk[i]` domain and crosses two ways:

- **sys_clk → ctr_clk (config in):** `INIT` / `INCREMENT` as quasi-static 2-FF
  synchronized buses; `CFG_LOAD` / `HOST_PRESS` as single-shot pulses through a
  `sync_pulse` module.
- **ctr_clk → sys_clk (status out):** `VALUE`, `PRESS_COUNT`, `CTR_CLK_TICKS`
  crossed back for readback. **The `VALUE` path is where `CDC_MODE` selects the
  crossing strategy** — this is the heart of the demo.

On each `ctr_clk` edge the counter loads `INIT` on a `CFG_LOAD` pulse, otherwise
advances by `INCREMENT` when a press event occurs. A press event is a debounced
button, a `HOST_PRESS` pulse, or — when `AUTO_INC = 1` — every `ctr_clk` edge.

## The five CDC modes (`CDC_MODE`)

| Mode | Name | Primitive | Safe? |
|:---:|------|-----------|:---:|
| 0 | NO-CDC | raw flop per bit | No (multi-bit skew at fast clocks) |
| 1 | STRETCH | `cdc_open_loop` (pulse stretch + sync) | Up to a tuned cliff (~25 MHz) |
| 2 | SYNC-FIFO | `fifo_async` (Gray pointers) | Yes |
| 3 | TWO-PHASE | `cdc_2_phase_handshake` | Yes |
| 4 | FOUR-PHASE | `cdc_4_phase_handshake` | Yes |

: The five CDC modes for the VALUE readback path

**Mode 0 (NO-CDC)** samples the multi-bit value with plain flops — at a fast
source clock the bits arrive skewed and the host reads transient garbage. That is
the intended failure. In Verilator (no metastability model) mode 0 reads the true
value deterministically, which is why the simulation asserts on mode 0 for exact
values (Chapter 6) but the *board* shows scramble at speed.

## Display

`DISP_SELECT` chooses which counter's 16-bit `VALUE` drives the 7-segment
digits; the upper digits show the selected counter's `CDC_MODE` and clock-select
so the operator can read the current configuration off the board.
