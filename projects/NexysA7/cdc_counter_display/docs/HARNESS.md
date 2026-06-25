# CDC Demo Harness — CSR Map and Wiring

**Status:** Phase 2 design (preserves the existing phase-1 `cdc_counter_display_top` as a standalone build).
**Top module:** `cdc_demo_top`
**Bus:** Single UART link (115200 8N1) → `uart_axil_bridge` → 32-bit AXI4-Lite into `cdc_demo_harness`
**Address space:** 12 bits / 4 KB (only the documented offsets are decoded; reads to undocumented offsets return 0)

---

## Block diagram

```
            ┌──────────────────────────────────────────────────────────────┐
            │  Nexys A7-100T  (sys_clk = 100 MHz from on-board oscillator) │
            │                                                              │
   USB ── UART ── uart_axil_bridge ── AXIL ── cdc_demo_harness             │
                                                │                          │
                                                ├── per-counter cfg/ctl    │
                                                │   (sys_clk domain)       │
                                                │                          │
                                                ▼                          │
                                       ┌─────────────────────────┐         │
                                       │ cdc_counter_domain × 4  │         │
   BTNC ─ btn_in[0] ─────────────────► │  ┌──── ctr_clk[i] ────┐ │         │
   BTNU ─ btn_in[1] ─────────────────► │  │ clock_divider      │ │         │
   BTND ─ btn_in[2] ─────────────────► │  │ debounce           │ │         │
   BTNL ─ btn_in[3] ─────────────────► │  │ counter (val+presses)│         │
                                       │  └────────────────────┘ │         │
                                       │   bin2gray + sync       │         │
                                       │   gray2bin (→ sys_clk)  │         │
                                       └─────────────────────────┘         │
                                                │                          │
                                                ▼                          │
                                       display_mux ── hex_to_7seg ── 7-seg │
                                                │                          │
   LEDs[7:0] ◄────────── alive/heartbeat/UART activity per counter         │
   BTNR ─ CPU_RESETN / soft-reset                                          │
            └──────────────────────────────────────────────────────────────┘
```

Each counter lives in its own divided-clock domain. The divisor is host-settable per counter via CSR, so the user can sweep through clock ratios (1:N, 1:7, 1:13, …) to demonstrate where CDC matters and where naive crossings happen to "just work."

---

## Button → counter mapping

| Button | Counter | Default divisor (`sys_clk / N`) | Default rate |
|---|---|---|---|
| BTNC | 0 | 10,000,000 | 10 Hz |
| BTNU | 1 | 2,500,000  | 40 Hz |
| BTND | 2 | 625,000    | 160 Hz |
| BTNL | 3 | 156,250    | 640 Hz |
| BTNR | (system soft-reset, via `CTRL[0]`) | — | — |

All divisors are runtime-settable via CSR — the defaults above are just what the bitstream comes up with.

---

## CSR map

All registers are 32 bits, word-addressable (4-byte stride). Writes to read-only fields are silently ignored. Reads from write-only fields return 0.

### Global registers (0x000–0x03F)

| Offset | Access | Field | Bits | Default | Purpose |
|---|---|---|---|---|---|
| 0x000 | R  | `BUILD_ID`        | [31:0] | `0x4344_4331` ("CDC1") | Bitstream identifier — host reads first to verify it's talking to the right design |
| 0x004 | R  | `STATUS`          | [31:0] | live | Bit 0..3: counter[i] `alive_pulse` toggled in last ~1 s window. Bit 4: UART RX activity. Bit 5: UART TX activity. Bit 6: any CSR written since reset. Bit 31: reset deasserted. |
| 0x008 | RW | `CTRL`            | [31:0] | 0 | Bit 0: soft reset (write 1, auto-clears after 1 sys_clk). Bit 1: freeze all counters. Bit 2: ignore physical buttons (host-press only). Bits 31:3 reserved. |
| 0x00C | RW | `DISP_SELECT`     | [1:0]  | 0 | Which counter's `VALUE` is shown on the 7-seg digits. |
| 0x010 | RW | `SCRATCH`         | [31:0] | 0 | Read-write scratch register — host uses this for link sanity (write 0xDEAD_BEEF, read back). |

### Per-counter registers

Counter `i` (i ∈ {0,1,2,3}) lives at base `0x040 + i * 0x40`. The same field layout repeats for each:

| Offset (+base) | Access | Field | Bits | Default | Purpose |
|---|---|---|---|---|---|
| +0x00 | RW | `DIVISOR`      | [31:0] | see table above | Clock divisor: `ctr_clk[i] = sys_clk / DIVISOR`. Minimum 2; values below 2 are clamped. Changing this on-the-fly retunes the counter's domain frequency (handy for sweeping CDC ratios). |
| +0x04 | RW | `INIT`         | [7:0]  | 0 | Initial value for the counter. Loaded into the counter by writing `CFG_LOAD`. |
| +0x08 | RW | `INCREMENT`    | [7:0]  | 1+i (so {1,2,3,4}) | Amount the counter advances per debounced button press (or per `HOST_PRESS`). |
| +0x0C | W  | `CFG_LOAD`     | [0]    | — | Pulse: write any value → load `INIT` into the counter on the next `ctr_clk[i]` edge. |
| +0x10 | W  | `HOST_PRESS`   | [0]    | — | Pulse: write any value → inject one virtual button press (subject to debounce in the counter domain so the host can't escape the per-counter clock). |
| +0x14 | R  | `VALUE`        | [15:0] | live | Current counter value, CDC'd from `ctr_clk[i]` to sys_clk. Path depends on `CDC_MODE`. Now 16 bits to drive a 4-digit hex display. |
| +0x18 | R  | `PRESS_COUNT`  | [15:0] | live | Number of debounced button presses (physical + host-injected + auto-inc edges) seen since last reset. Always uses proper Gray-coded CDC. |
| +0x1C | R  | `CTR_CLK_TICKS`| [31:0] | live | Free-running tick counter incrementing on `ctr_clk[i]` and synchronized into sys_clk. |
| +0x20 | RW | `CDC_MODE`     | [2:0]  | 0 | **CDC strategy for `VALUE` readback:** `0`=NO-CDC (raw flop per bit — multi-bit skew at fast clocks); `1`=STRETCH (`cdc_open_loop`, STRETCH_CYCLES=1, SYNC_STAGES=3 — tuned cliff at ~20–25 MHz `ctr_clk`); `2`=SYNC-FIFO (`fifo_async`, depth 16 — Gray-pointer, always safe); `3`=TWO-PHASE (`cdc_2_phase_handshake`); `4`=FOUR-PHASE (`cdc_4_phase_handshake`). Modes 5–7 fall through to NO-CDC. See [`RUNBOOK.md`](RUNBOOK.md) for the mode×pickoff lookup table. |
| +0x24 | RW | `AUTO_INC`     | [0]    | 0 | 0 = increment only on debounced button press or `HOST_PRESS`; 1 = increment every `ctr_clk` edge (lets you crank the source clock without UART bottleneck so you can sweep clock speed and watch broken CDC fail). |

### Address map summary

| Range | Bytes | Function |
|---|---|---|
| 0x000–0x03F | 64  | Global control/status |
| 0x040–0x07F | 64  | Counter 0 |
| 0x080–0x0BF | 64  | Counter 1 |
| 0x0C0–0x0FF | 64  | Counter 2 |
| 0x100–0x13F | 64  | Counter 3 |
| 0x140–0xFFF | —   | Reserved (reads return 0, writes ignored) |

---

## Reset behavior

| Source | Effect |
|---|---|
| `CPU_RESETN` (board button BTNR or pin) | Full sys_clk-domain reset; harness CSRs return to defaults; counter domains are held in reset until `ctr_clk[i]` first toggles. |
| `CTRL[0] = 1` (soft reset) | Same effect as `CPU_RESETN`, originating from CSR. Self-clearing after one sys_clk cycle. |
| `CFG_LOAD` (per-counter) | Counter `i` only — loads `INIT[i]` into the counter on next `ctr_clk[i]`. Does not touch press count, divisor, or other counters. |

---

## CDC primitives used

| Crossing | Direction | Primitive | Notes |
|---|---|---|---|
| CSR cfg signals (`INIT`, `INCREMENT`, `DIVISOR`) | sys_clk → ctr_clk[i] | Quasi-static, 2-flop bit synchronizer per bit. Host must not write these faster than the slowest counter clock period (worst case ~100 ms at div=10M). | Cfg "load" is gated by a `CFG_LOAD` pulse so partial-write hazards don't matter. |
| `CFG_LOAD`, `HOST_PRESS` | sys_clk → ctr_clk[i] | `cdc_open_loop` (pulse stretcher + 2-FF sync + edge detect on dst) | Single-shot pulses. |
| `VALUE`, `PRESS_COUNT`, `CTR_CLK_TICKS` | ctr_clk[i] → sys_clk | `bin2gray` → 2-FF sync → `gray2bin` | Standard Gray-coded async sample. Value is monotonic-counter so Gray pointer technique is valid. |
| `alive_pulse` | ctr_clk[i] → sys_clk | `cdc_open_loop` (toggle on press, sync, edge detect, drive a 1-second one-shot for `STATUS[i]`) | LED-friendly heartbeat. |

XDC: each `ctr_clk[i]` is declared as a `create_generated_clock` derived from sys_clk via the divisor; CDC paths get `set_max_delay -datapath_only` constrained to one source-clock period.

---

## Host script

See [`host/run_cdc_demo.py`](../host/run_cdc_demo.py). Quick overview:

```bash
# Build + program (one-time, ~5 min)
make build-demo
make program-demo

# Run a quick smoke test (BUILD_ID, scratch, all 4 counters defaults)
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 smoke

# Sweep counter 0's divisor and show how VALUE updates
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 sweep --counter 0 --divisors 1000,10000,100000

# Inject 1000 host-press events to counter 2 and verify VALUE = INIT + 1000*INCREMENT
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 press --counter 2 --count 1000

# Real-time monitor of all 4 counters' VALUE/PRESS_COUNT
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 monitor
```

---

## What this enables

- **Live CDC demo on real silicon.** Press the four buttons, host watches VALUE/PRESS_COUNT update across the CDC. With `CDC_MODE=0` (Gray-coded sync) the reads are always coherent regardless of clock speed.
- **Watch CDC actually break.** Put one counter in `CDC_MODE=1` (no CDC, raw cross), set `AUTO_INC=1`, then sweep its `PICKOFF` from slow → fast. The 7-seg digit for that counter stays clean at slow speeds (the "lucky" case from `CDC_DEMO_TODO.md` §4), then visibly flickers and shows garbage at fast speeds (multi-bit bus skew). Other counters in `CDC_MODE=0` stay clean throughout — side-by-side comparison on one board.
- **Sweep clock-ratio space.** Host can set arbitrary pickoff values per counter; combined with `AUTO_INC=1` this exercises the full source-clock range with no UART bottleneck.
- **Headless characterization.** No physical button presses needed — the host can either inject thousands of synthetic presses via `HOST_PRESS` or flip `AUTO_INC=1` to drive the counter at line rate.
- **Same UART + AXIL pattern as `stream_characterization` / `timing_characterization`.** One bitstream, one TTY, one Python runner. Familiar wiring.

### The headline "watch it fail" demo

```
# All four counters start in proper CDC mode, slow clock, button-driven.
# That's the default after reset — nothing to do.

# Pick counter 2 for the demo. Switch it to broken-CDC + auto-increment.
host_write(ctr2.CDC_MODE, 1)        # NO CDC
host_write(ctr2.AUTO_INC, 1)        # Every ctr_clk edge advances counter

host_write(ctr2.PICKOFF, 23)        # ~6 Hz   → display: 00 01 02 03 ... clean
host_write(ctr2.PICKOFF, 19)        # ~95 Hz  → still clean (faster but legible)
host_write(ctr2.PICKOFF, 15)        # ~1.5 kHz → still clean (display refresh averages)
host_write(ctr2.PICKOFF, 11)        # ~24 kHz → still clean (~lucky)
host_write(ctr2.PICKOFF, 7)         # ~390 kHz → flicker starts
host_write(ctr2.PICKOFF, 3)         # ~6 MHz   → visible garbage
host_write(ctr2.PICKOFF, 0)         # ~50 MHz  → total scramble

# Set DISP_SELECT to 2 to put the broken counter on the 7-seg.
# Compare against counter 0 or 1 (still in proper CDC mode) — those
# stay clean at any pickoff.
```

