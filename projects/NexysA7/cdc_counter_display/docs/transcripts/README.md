# CDC Demo — YouTube Tutorial Scripts

Six-episode walkthrough of `cdc_demo_top`, ~90 seconds each, intended for an established RTL engineer audience. Tone: dry, slightly snarky, informative — "amused expert," not "angry youtuber."

**Total runtime:** ~9 minutes across 6 episodes.

---

## Episodes

| # | Title | Runtime | File |
|---|---|---|---|
| 1 | Your sim passed. Your silicon's lying. | ~75 s | [`episode_1_your_sim_lies.md`](episode_1_your_sim_lies.md) |
| 2 | Meet the demo board | ~90 s | [`episode_2_meet_the_board.md`](episode_2_meet_the_board.md) |
| 3 | Mode 0: No CDC. Why does it ever work? | ~90 s | [`episode_3_no_cdc.md`](episode_3_no_cdc.md) |
| 4 | Mode 1: The 20-megahertz lie | ~90 s | [`episode_4_stretch_20mhz_lie.md`](episode_4_stretch_20mhz_lie.md) |
| 5 | Modes 2, 3, 4: How to do it for real | ~105 s | [`episode_5_safe_modes.md`](episode_5_safe_modes.md) |
| 6 | Try it yourself | ~75 s | [`episode_6_try_it_yourself.md`](episode_6_try_it_yourself.md) |

---

## Recording setup

- Nexys A7-100T programmed with `cdc_demo_top.bit` (`make program-demo`).
- USB-UART optional but useful for episode 5 (not needed for board-only flow).
- Top-down camera on the board for B-roll; voice-over over a clean screen capture of the 7-seg + LEDs.

**Notation key used in each script:**
- `[CAM]` — camera shot direction
- `[VO]` — voice-over text
- `[BTN]` — board action to perform
- `[OVERLAY]` — on-screen text overlay

---

## Production notes

- **Pacing.** Engineering humor for engineers. Trust the viewer; don't over-explain. ~150 spoken words per minute is the sweet spot for an established RTL engineer audience.
- **Snark dosage.** Dry expert calling out common mistakes, not insulting the viewer. If a joke needs a laugh track, cut it.
- **B-roll.** Real board, real flicker. Don't fake the failures with mocked screen captures — get the real glitch on real silicon. The audience will notice.
- **Captions.** Hardcode the mode numbers (`00`, `01`, `02`, `03`, `04`) and pickoff values as on-screen overlays whenever you push a button. Viewers will pause and try to recreate the sequence.
- **Episode 3 → 4 transition.** Don't reset between them. Continue from "mode 0, pickoff 0, garbage" → cycle to mode 1 with a single BTNL press. The dramatic moment is the display turning readable on one button press.
- **Episode 6 length.** Keep it tight. Once you've said "github.com" you've delivered the value — wrap quickly.

---

## Optional bonus episodes

If the series goes well, candidates for follow-ups:

- **Why your CDC report lies.** Vivado / Lattice CDC checkers flag Gray-coded crossings as suspect. They aren't. Walk through how to read the report and which warnings to dismiss.
- **Async FIFOs aren't actually async.** Show the Gray-pointer trick under the hood. `fifo_async.sv` as the teaching example.
- **Reset is also a CDC.** Run a contrived demo where the reset bridge fails and the whole design wedges. `reset_sync.sv` as the fix.
- **How to write a CDC test that actually catches bugs.** Metastability injector in cocotb. Gate-level sim with SDF back-annotation.

---

## Cross-references

- [`../RUNBOOK.md`](../RUNBOOK.md) — operator's guide for the board (the live demo cheat sheet the videos walk through)
- [`../HARNESS.md`](../HARNESS.md) — CSR map for the host runner
- [`../CDC_DEMO_TODO.md`](../CDC_DEMO_TODO.md) — taxonomy of CDC failure modes (background reading)
