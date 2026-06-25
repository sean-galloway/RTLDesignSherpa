# Episode 3: "Mode 0: No CDC. Why does it ever work?"

**Runtime target:** ~90 seconds
**Word count:** ~220 spoken
**Goal:** The dramatic demo. Show the cliff where naive CDC goes from "fine" to "garbage."

---

**[CAM: board reset, display shows `00 17 0000`]**
**[VO]** Mode zero. No CDC. We just route the source counter directly through a single sys-clock flop per bit. No synchronizer. No Gray coding. Vivado would normally yell at us; we explicitly told it to shut up with an `ASYNC_REG=FALSE` attribute. This is the worst CDC you could write.

**[BTN: flip SW[15] up — AUTO_INC on]**
**[VO]** Auto-increment on. Counter ticks every source clock. At pickoff 17 hex — that's six hertz — you can count along.

**[BTN: BTNU, slow taps]**
**[VO]** Crank the clock. Each press doubles it. Ninety-five hertz. Fifteen-hundred. Twenty-four thousand. *Still* clean.

**[CAM: display showing rapid but legible counting]**
**[VO]** This is the trap. At slow source clocks, "no CDC" looks fine. The data is stable across many sys-clock samples, transitions are rare, you got lucky.

**[BTN: BTNU rapid taps]**
**[OVERLAY: pickoff dropping 0F → 0B → 07]**
**[VO]** Three-ninety kilohertz... and now the rightmost digit is dancing.

**[BTN: BTNU more]**
**[CAM: display flickering hard]**
**[VO]** Six megahertz. The mid-digits are starting to lie. You're seeing values that don't exist on the source side. This is multi-bit skew — different bits of the counter cross with slightly different delays, and the destination reads the hybrid.

**[BTN: BTNU until pickoff `00`]**
**[CAM: display total garbage]**
**[VO]** Fifty megahertz. The display is now random hex digits. The actual counter on the source side is incrementing cleanly. The display has no idea.

**[OVERLAY: "Same RTL. Same flop. Different clock."]**

**[VO]** Here's the kicker: your RTL sim of this would have passed at fifty megahertz too. Because your sim doesn't model the part of physics that breaks here.

**[OVERLAY: "Next: the mode that almost saves you."]**
