# Episode 3: "Mode 0: No CDC. Why does it ever work?"

**Runtime target:** ~90 seconds
**Word count:** ~220 spoken
**Goal:** The dramatic demo. Show the cliff where naive CDC goes from "fine" to "garbage."

---

**[CAM: board, counter 2 selected, mode 00, clock-select 04 (divided), display shows `00 04 0000`]**
**[VO]** Mode zero. No CDC. We just route the source counter directly through a single sys-clock flop per bit. No synchronizer. No Gray coding. Vivado would normally yell at us; we explicitly told it to shut up with an `ASYNC_REG=FALSE` attribute. This is the worst CDC you could write.

**[BTN: flip SW[15] up — AUTO_INC on]**
**[OVERLAY: "Source clock 6 Hz (divided), AUTO_INC = on"]**
**[VO]** Auto-increment on. Counter ticks every source clock. Six hertz — slow enough to count along.

**[CAM: display showing slow, visible counting]**
**[VO]** This is the trap. At slow source clocks, "no CDC" looks fine. The data is stable across many sys-clock samples, transitions are rare, you got lucky.

**[BTN: BTNU once — clock-select 04 → 03 → MMCM 6.25 MHz]**
**[OVERLAY: "Now: MMCM /128 = 6.25 MHz — truly async to sys_clk"]**
**[VO]** Switch to the MMCM bank. Six and a quarter megahertz. And this clock is *not* an integer divide of sys-clock — it comes out of an MMCM with a co-prime divisor, so the phase relationship drifts every cycle. *Real* async.

**[CAM: display starting to flicker on mid-digits]**
**[VO]** And the mid-digits are already lying. You're seeing values that don't exist on the source side. Multi-bit skew — different bits of the counter cross with slightly different delays, and the destination reads the hybrid.

**[BTN: BTNU again — clock-select 02, MMCM 11.9 MHz]**
**[CAM: display flickering harder]**
**[VO]** Twelve megahertz, still co-prime async. Worse.

**[BTN: BTNU again — clock-select 01, MMCM 27.6 MHz]**
**[CAM: display total garbage]**
**[VO]** Twenty-eight. Total garbage on the right four digits. The actual counter on the source side is incrementing cleanly. The display has no idea.

**[BTN: BTNU again — clock-select 00, MMCM 72.7 MHz]**
**[CAM: display rolling random hex]**
**[VO]** Seventy-three megahertz. Now we're just watching noise.

**[OVERLAY: "Same RTL. Same flop. Different clock, async to sys_clk."]**

**[VO]** Here's the kicker: your RTL sim of this would have passed at seventy-three megahertz too. Because your sim doesn't model the part of physics that breaks here.

**[OVERLAY: "Next: the mode that almost saves you."]**
