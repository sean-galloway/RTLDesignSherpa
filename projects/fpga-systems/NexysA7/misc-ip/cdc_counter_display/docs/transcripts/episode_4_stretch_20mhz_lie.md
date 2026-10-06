# Episode 4: "Mode 1: The 20-megahertz lie"

**Runtime target:** ~90 seconds
**Word count:** ~215 spoken
**Goal:** Show "tuned to work" as a design anti-pattern. The cliff is the lesson.

**Continuity note:** This episode picks up directly from episode 3 — do NOT reset between them. The dramatic moment is a single BTNL press visually rescuing the garbage from ep 3.

---

**[CAM: board, ctr2, mode 00, clock-select 00 (72.7 MHz MMCM), display garbage]**
**[VO]** We left counter two with mode zero and the seventy-two megahertz MMCM clock — total garbage. Watch what happens when we switch CDC strategies without changing anything else.

**[BTN: BTNL once]**
**[CAM: display mode field shows `01`, value clean again]**
**[VO]** Mode one. The display is suddenly readable. We replaced the raw flop with a *data-stretch* CDC — the source holds the data and a valid pulse for one source-clock period, the destination synchronizes through three flops.

**[OVERLAY: "STRETCH_CYCLES = 1, SYNC_STAGES = 3"]**

**[VO]** Wait. Same seventy-two megahertz clock. Why does mode one work and mode zero didn't? Look at the value — it's not zero, it's actually counting. It's just clean.

**[VO]** That's because stretch holds the source data stable across a pulse. Multi-bit skew can't happen if the data isn't transitioning during the destination sample window. As long as the stretch is *long enough*.

**[BTN: BTND once — clock-select 01 (MMCM 27.6 MHz)]**
**[OVERLAY: "Slower MMCM output (27.6 MHz)"]**
**[VO]** Slower clock. Bulletproof.

**[BTN: BTND once — clock-select 02 (MMCM 11.9 MHz)]**
**[VO]** Slower again. Fine.

**[BTN: BTND twice → clock-select 04 (divided), then BTNU repeatedly to fast divided]**
**[VO]** Switch back to the divided-clock branch. Slow. Crank the divided pickoff up until it's running at twenty-five megahertz.

**[CAM: display still clean]**
**[VO]** Still clean. We're at the design's cliff — three sync flops at sys-clock need thirty nanoseconds to settle, and a source pulse at twenty-five megahertz lasts forty. Just enough.

**[BTN: BTNU back to MMCM idx 0 — 72.7 MHz]**
**[CAM: display freezes on a stale value]**
**[VO]** And we're back at seventy-two megahertz. Each source pulse is fourteen nanoseconds. The synchronizer needs thirty. Most pulses get lost. Look at the display — it's *frozen*. Not garbage like mode zero — frozen. The display shows whichever value last successfully made it across.

**[OVERLAY: "Works at 25 MHz. Lies at 72."]**

**[VO]** Engineers love this kind of design. "I tuned the stretch constants so it meets timing." Sure. Until the silicon vendor changes corner libraries, or someone increases the clock, or the chip warms up. Then your customers find out.

**[OVERLAY: "Next: three ways to actually fix it."]**
