# CDC Demo — Board Runbook

**Bitstream:** `cdc_demo_top` (phase-2 build, `make build-demo`)
**Board:** Digilent Nexys A7-100T
**Last updated:** 2026-06-25

This is the operator's guide — what each button and switch does, what each
display digit means, and how to drive the headline "watch CDC break" demo
from the board alone (no laptop required, though one is supported via UART).

For the CSR map and host-script reference see [`HARNESS.md`](HARNESS.md).
For the CDC primitive taxonomy and the "why it sometimes works anyway"
pitfalls, see [`CDC_DEMO_TODO.md`](CDC_DEMO_TODO.md).

---

## At a glance

```
      ┌──────────────────────────────────────────────────────────────┐
      │                       7-segment display                      │
      │   ┌──────┐ ┌──────┐ ┌──────────────────────────────────┐    │
      │   │ Mode │ │ Pick │ │      16-bit Counter Value        │    │
      │   │  00  │ │  17  │ │              CAFE                 │    │
      │   │ AN76 │ │ AN54 │ │             AN3210                │    │
      │   └──────┘ └──────┘ └──────────────────────────────────┘    │
      │                                                              │
      │   ┌─────────────┐                                            │
      │   │    LEDs     │                                            │
      │   │ ●●●○ ○○○● = sel-counter LED[3:0] · alive[4] · rx[5] ·    │
      │   │              tx[6] · ok[7]                               │
      │   └─────────────┘                                            │
      │                                                              │
      │       ┌─────────┐                                            │
      │       │ Buttons │   BTNU = pickoff UP (faster)               │
      │       │   ◯     │   BTND = pickoff DOWN (slower)             │
      │       │ ◯ ● ◯   │   BTNL = cycle CDC mode                    │
      │       │   ◯     │   BTNC = inject press (host-equivalent)    │
      │       └─────────┘   BTNR = system reset                      │
      │                                                              │
      │     ┌────────────────┐                                       │
      │     │ Slide switches │                                       │
      │     │ SW[1:0] = which counter is selected (0-3)              │
      │     │ SW[15] = AUTO_INC for selected counter (1 = on)        │
      │     │ SW[2..14] = reserved                                   │
      │     └────────────────┘                                       │
      └──────────────────────────────────────────────────────────────┘
```

---

## Switches

| Switch | Function |
|---|---|
| **SW[1:0]** | **Selected counter index (0–3).** Picks which counter the display, LEDs, BTNC, BTNU/D, and BTNL act on. |
| **SW[15]** | **`AUTO_INC` for the selected counter.** 1 = counter increments every `ctr_clk` edge (lets you crank the source clock without manually pressing BTNC). 0 = counter only advances on debounced button press or `HOST_PRESS`. |
| SW[14:2] | Reserved. |

> Flipping SW[1:0] re-targets every other control. The on-display values
> (mode label, pickoff, counter value) and the alive LED change to reflect
> the newly-selected counter. Each counter's state is preserved — it
> doesn't reset when you switch away.

---

## Push buttons

| Button | Action | Notes |
|---|---|---|
| **BTNR** / `CPU_RESETN` | **System reset.** | Active-low. Returns all CSRs to defaults; all 4 counters re-initialize. |
| **BTNC** (center) | **Inject a press** for the selected counter. | Equivalent to writing `HOST_PRESS` from the host. Counter advances by `INCREMENT` (default 1+ctr_idx). |
| **BTNU** (up) | **Step pickoff UP** (decrement value → higher frequency). | Each press divides the source-clock period in half. Clamps at pickoff = 0 (= sys_clk/2 = 50 MHz). Hold doesn't repeat — release and press again. |
| **BTND** (down) | **Step pickoff DOWN** (increment value → lower frequency). | Each press doubles the source-clock period. Clamps at pickoff = 31 (≈ 0.05 Hz, basically never tickling). |
| **BTNL** (left) | **Cycle CDC mode** for the selected counter. | Cycles 0 → 1 → 2 → 3 → 0 (PROPER → BROKEN-RAW → BROKEN-2FF → HANDSHAKE-4PHASE). Mode label on AN[7:6] updates. |

All buttons are edge-detected in the system-clock domain after a 2-flop
synchronizer; there's no software-side debounce, so light bounces may
result in occasional double presses (more pedagogically honest anyway —
buttons are noisy).

---

## 7-segment display

Eight digits, left-to-right = AN[7]…AN[0]. Active-low cathodes (segment lit = 0).

| Digits | Field | Meaning |
|---|---|---|
| **AN[7:6]** | **CDC mode number (hex)** | Two hex digits — the current `CDC_MODE` value for the selected counter (`00`–`03` today; the design has room for up to `FF`). See the mode legend below. |
| **AN[5:4]** | **Pickoff (hex)** | Current `PICKOFF` value for the selected counter, `00`–`1F`. Lower = faster ctr_clk. |
| **AN[3:0]** | **Counter value (hex)** | Low-to-high 4 hex digits of the 16-bit `VALUE` register of the selected counter, post-CDC. This is the thing that flickers when CDC breaks. |

### Mode legend (the five CDC strategies)

| Display (AN[7:6]) | Mode # | Name | Underlying RTL module | Expected behavior |
|---|---|---|---|---|
| **`00`** | 0 | **NO-CDC** | (raw flop per bit, no module, `ASYNC_REG="FALSE"`) | Clean at slow pickoff. Visibly flickers/scrambles at fast pickoff. The textbook "no CDC" failure. |
| **`01`** | 1 | **STRETCH** | [`cdc_open_loop`](../../../../rtl/amba/shared/cdc_open_loop.sv) with `STRETCH_CYCLES=1`, `SYNC_STAGES=3` | Source pulse-stretches data+valid for 1 ctr_clk; dst synchronizes through 3 flops. **Tuned to work up to ~20–25 MHz `ctr_clk`, lose values above** (dst misses pulses that don't outlast the synchronizer chain). |
| **`02`** | 2 | **SYNC FIFO** | [`fifo_async`](../../../../rtl/common/fifo_async.sv), depth 16, Gray-pointer | Push every press in ctr_clk, pop continuously in sys_clk. Gray-coded pointer CDC is always safe — clean across the whole pickoff range. The "robust" reference path. |
| **`03`** | 3 | **2-PHASE** | [`cdc_2_phase_handshake`](../../../../rtl/amba/shared/cdc_2_phase_handshake.sv) | Toggle (NRZ) handshake; periodic snapshots every 256 ctr_clk. Never garbage; value lags by the handshake round-trip. Faster than 4-phase. |
| **`04`** | 4 | **4-PHASE** | [`cdc_4_phase_handshake`](../../../../rtl/amba/shared/cdc_4_phase_handshake.sv) | RTZ req/ack handshake; periodic snapshots every 256 ctr_clk. Most conservative, slowest. Same "safe but lagged" character as `03`. |

Press **BTNL** to cycle: `00 → 01 → 02 → 03 → 04 → 00 → …`. The 3-bit field has room for 8 modes; values 5–7 are reserved (writing them via CSR falls through to NO-CDC behavior).

### Pickoff → frequency cheat sheet

`ctr_clk = sys_clk / 2^(pickoff + 1)` with `sys_clk = 100 MHz`.

| Pickoff (hex) | `ctr_clk` | Notes |
|---|---|---|
| `17` (23) | ~6 Hz       | Default for counter 0. Very visible counting. |
| `13` (19) | ~95 Hz      | Default for counter 1. |
| `0F` (15) | ~1.5 kHz    | Default for counter 2. |
| `0B` (11) | ~24 kHz     | Default for counter 3. |
| `07` (7)  | ~390 kHz    | Where mode `01` (broken-raw) starts to flicker visibly. |
| `03` (3)  | ~6.25 MHz   | Mode `01` shows obvious scramble; mode `02` still clean. |
| `02` (2)  | 12.5 MHz    | Mode `02` (broken-2FF) still safe. **Below the "data-stretch" cliff.** |
| `01` (1)  | 25 MHz      | **The cliff.** Mode `02` starts to break here — multi-bit skew is now likely between sys_clk samples. Closest power-of-2 pickoff to the ~20 MHz threshold. |
| `00` (0)  | 50 MHz      | Mode `01` is total garbage; mode `02` is also scrambled; mode `03` (handshake) lags by ≥1 wrap; only mode `00` (proper) stays clean. |

### Mode × pickoff expected-behavior lookup table

What you *should* see on AN[3:0] (the 16-bit value digits) at each combination. **"Clean" = monotonic count tracking the source; "drops" = source values are lost (display lags or freezes on stale values); "lag" = correct values but updated slowly / behind reality; "garbage" = mid-transition hybrid values that were never on the source side.**

| Pickoff (`ctr_clk`)  | `00` NO-CDC | `01` STRETCH | `02` SYNC FIFO | `03` 2-PHASE | `04` 4-PHASE |
|---|---|---|---|---|---|
| `17` (6 Hz)          | clean | clean | clean | clean | clean |
| `13` (95 Hz)         | clean | clean | clean | clean | clean |
| `0F` (1.5 kHz)       | clean | clean | clean | clean | clean |
| `0B` (24 kHz)        | mostly clean (rare glitch on multi-bit transitions) | clean | clean | clean | clean |
| `07` (390 kHz)       | **flicker** (rightmost digits) | clean | clean | clean | clean |
| `03` (6.25 MHz)      | **scramble** | clean | clean | clean | clean |
| `02` (12.5 MHz)      | **garbage** | clean — **safely below the cliff** | clean | clean | clean |
| `01` (25 MHz)        | **garbage** | **borderline** — at the design cliff (stretch ≈ sync depth) | clean | clean | clean |
| `00` (50 MHz)        | **total garbage** | **fails** — most values dropped; display freezes on a stale snapshot | clean (read side outpaces writes — FIFO never fills) | lag (snapshot every 256 ctr_clk = 5 µs; counter wraps every 1.3 ms) | lag (same snapshot rate; longer round trip per snapshot) |

**How to read this table:**

- **Mode `00` (NO-CDC)** is the dramatic failure case. The cliff is around pickoff `07`–`09` (~200 kHz–~800 kHz). The whole point of this mode is to **see** what no CDC looks like.
- **Mode `01` (STRETCH)** is the "data-stretch" mode tuned for ~20 MHz. With `STRETCH_CYCLES=1` and `SYNC_STAGES=3`, the destination needs ≥ 30 ns to see the valid pulse. At ctr_clk = 25 MHz (40 ns period) the pulse just barely makes it; at 50 MHz (20 ns) it doesn't — destination misses pulses, source values are lost, and the display freezes on whatever last got through. **Works ≤ 20–25 MHz, fails above.** That's the configured cliff.
- **Mode `02` (SYNC FIFO)** is the textbook robust path. Gray-coded pointer CDC inside `fifo_async`. The read side (sys_clk = 100 MHz) is faster than the write side, so the FIFO never fills. Clean across the whole pickoff range.
- **Mode `03` (2-PHASE)** and **Mode `04` (4-PHASE)** never show garbage. The handshake holds source data stable across the crossing. The visible difference vs SYNC FIFO is **lag**: snapshots only every 256 ctr_clk cycles. At slow ctr_clk you'll see clear stepwise updates as the snapshot rate matches the counter rate; at fast ctr_clk the display value lags reality by many counter increments.

> **Why mode 1's cliff is "~20 MHz" rather than an exact number:** with power-of-2 dividers the closest pickoffs are `01` (25 MHz, borderline) and `02` (12.5 MHz, safe). The design's actual physical cliff is at ctr_clk ≈ sys_clk / (SYNC_STAGES + 1) = 100 / 4 = 25 MHz. If you need an exactly-20-MHz cliff (e.g., for a specific lab demonstration), I can add a non-power-of-2 `/5` divider — say the word.

---

## LEDs

| LED | Meaning |
|---|---|
| LED[0..3] | **Selected counter, one-hot.** Only one is on at a time (matches SW[1:0]). |
| LED[4]    | **Alive pulse** for the selected counter. Toggles on each press event in `ctr_clk`. Slow pickoff → visible flashing; fast pickoff → blurred. |
| LED[5]    | **UART RX activity** (stretched). Lights when host sends a CSR write/read. |
| LED[6]    | **UART TX activity** (stretched). Lights when FPGA responds. |
| LED[7]    | **System OK.** Always on after reset deasserts. |

---

## Standalone demo (no laptop)

Follow this exactly — no UART, no host script. Just the board.

1. **Power on / reset.** Press BTNR (CPU_RESETN). After release: LED[0] on (counter 0 selected), LED[7] on (system OK), display shows `00 17 0000` (mode 0 = PROPER, pickoff 0x17, value 0).
2. **Watch a clean count.** Hit BTNC a few times. The `0000` increments by 1 each press: `0000 → 0001 → 0002 …`. Alive LED[4] blinks per press.
3. **Switch to counter 2.** Flip SW[1:0] to `10`. Display now shows counter 2's state: `00 0F 0000`. LED[2] lights, LED[0] dark.
4. **Cycle to broken-CDC.** Press BTNL once. Mode display changes `00 → 01` (PROPER → BROKEN-RAW). The counter value is still 0000, no flicker yet (the counter isn't transitioning).
5. **Turn on AUTO_INC.** Flip SW[15] up. Now counter 2 advances every `ctr_clk` edge. At pickoff `0F` (~1.5 kHz), the rightmost digits are spinning fast, mid-digits slower — but you can still read them. No flicker.
6. **Crank the clock.** Press BTNU four times. Each press cuts the period in half. After 4 presses: pickoff goes `0F → 0E → 0D → 0C → 0B` (~24 kHz). Display still readable (this is the "lucky" case — no Gray but the transitions are slow enough that sys_clk samples land between bit flips).
7. **Keep cranking.** Press BTNU four more times: pickoff `0B → 07` (~390 kHz). **The rightmost digits start to flicker.** Some moments you see one value, the next a totally different one — the broken raw CDC is sampling mid-transition values.
8. **Go to the limit.** Press BTNU until pickoff = `00` (~50 MHz). The display is now total garbage on AN[3:0] — values that were never on the source side. AN[5:4] shows `00` cleanly because that's static state, not crossed. AN[7:6] shows `01` cleanly for the same reason.
9. **Compare to other modes.** Press BTNL to cycle through `01 → 02 → 03 → 00`:
   - **`02` (BROKEN-2FF)**: still scrambled (sync flops don't fix multi-bit skew).
   - **`03` (HANDSHAKE)**: stops flickering, but the displayed value lags visibly — the handshake delivers snapshots, not every tick.
   - **`00` (PROPER)**: clean monotonic count again, even at 50 MHz. **This is the entire point of the demo.**
10. **Compare side-by-side.** Without changing counter 2, flip SW[1:0] to `00` (counter 0). Display jumps to counter 0's state: `00 17 xxxx` — still nicely ticking at 6 Hz with proper CDC. Switch back to `10`: counter 2 is still scrambled in mode `01` (or behaving however you left it). Each counter's state persists; the switches just steer which one drives the display.
11. **Reset to clean.** Press BTNR — everything back to defaults.

**Recommended teaching script** (~3 minutes): step through 1–9 narrating each cycle of BTNL ("now we're using gray-coded sync — watch it never break") and BTNU ("now we're at a megahertz — bytes are racing across the boundary").

---

## Host-driven demo (UART)

When a laptop is connected, the same controls are available via CSR. See [`HARNESS.md`](HARNESS.md) for the register map and [`host/run_cdc_demo.py`](../host/run_cdc_demo.py) for the runner.

```bash
make program-demo                              # one-time flash
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 smoke         # link check
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 watch-fail    # the headline demo, scripted
python3 host/run_cdc_demo.py --port /dev/ttyUSB1 monitor       # live view of all 4 counters
```

The host script does the whole BTNU/BTNL sequence above as `watch-fail`,
sampling VALUE 10× at each pickoff and printing variance. Useful when you
want quantitative data instead of "I saw it flicker."

---

## Common questions

**Q: I pressed BTNU and pickoff didn't change.**
A: You may be at the minimum (0x00). Hit BTND a few times to bring it back.

**Q: The display shows the right mode label but the value is 0000 and not moving.**
A: AUTO_INC is off and you haven't pressed BTNC. Either flip SW[15] up or press BTNC.

**Q: AN[3:0] is mostly garbage but every few seconds I see what looks like an "actual" value.**
A: Expected for broken-CDC at fast clocks — the 7-seg refresh occasionally lands on a moment when the source counter is between two stable values, but most samples are mid-transition. Pedagogically: "intermittent correctness" is the worst kind of bug, exactly what unsynchronized CDC produces.

**Q: I flipped SW[15] (AUTO_INC) but nothing changed.**
A: SW[15] only takes effect on the **selected** counter (the one indicated by SW[1:0] and LED[0..3]). To AUTO_INC a different counter, flip SW[1:0] first, then SW[15].

**Q: Does BTNL affect all counters or just the selected one?**
A: Just the selected one. Each counter's `CDC_MODE` is independent — you can have counter 0 in PROPER, counter 1 in HS, counter 2 in br, counter 3 in S2, all running simultaneously. The display shows whichever one SW[1:0] selects.

**Q: I want counter 2 broken AND counter 0 in proper mode side-by-side. Can I see both?**
A: Not simultaneously (the display only shows one counter at a time), but the *behavior* runs in parallel — both counters are alive and ticking. Toggle SW[1:0] back and forth to compare. (LEDs[0..3] update too, so you can tell which is on the display.)
