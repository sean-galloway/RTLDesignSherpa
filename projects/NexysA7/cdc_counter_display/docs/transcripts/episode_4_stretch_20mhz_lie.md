# Episode 4: "Mode 1: The 20-megahertz lie"

**Runtime target:** ~90 seconds
**Word count:** ~215 spoken
**Goal:** Show "tuned to work" as a design anti-pattern. The cliff is the lesson.

**Continuity note:** This episode picks up directly from episode 3 — do NOT reset between them. The dramatic moment is a single BTNL press visually rescuing the garbage from ep 3.

---

**[CAM: board reset, ctr2 selected, mode 0, pickoff 0]**
**[VO]** We left counter two with mode zero and the clock at fifty megahertz — total garbage. Watch what happens when we switch CDC strategies without changing anything else.

**[BTN: BTNL once]**
**[CAM: display mode field shows `01`, value clean again]**
**[VO]** Mode one. The display is suddenly readable. We replaced the raw flop with a *data-stretch* CDC — the source holds the data and a valid pulse for one source-clock period, the destination synchronizes through three flops.

**[OVERLAY: "STRETCH_CYCLES = 1, SYNC_STAGES = 3"]**

**[VO]** This works because three sync flops at sys-clock — that's about thirty nanoseconds — need the source signal to stay stable for at least that long. At the right clock ratio, it does.

**[BTN: BTND a few times — slow the clock back down]**
**[VO]** Slower clocks: bulletproof.

**[BTN: BTNU rapid back up]**
**[OVERLAY: pickoff ticking up: 02 → 01]**
**[VO]** Faster. Twelve point five megahertz — fine. Twenty-five megahertz — borderline.

**[BTN: BTNU one more — pickoff `00`]**
**[CAM: display freezes on a stale value]**
**[VO]** Fifty megahertz. The display has *frozen*. Not garbage — frozen. The source counter is doing its thing, but the destination synchronizer can't see the valid pulses any more. Each pulse is twenty nanoseconds. The synchronizer needs thirty. Most pulses get lost. The display shows whichever value last made it across.

**[OVERLAY: "Works at 20 MHz. Lies at 50."]**

**[VO]** Engineers love this kind of design. "I tuned the stretch constants so it meets timing." Sure. Until the silicon vendor changes corner libraries, or someone increases the clock, or the chip warms up. Then your customers find out.

**[OVERLAY: "Next: three ways to actually fix it."]**
