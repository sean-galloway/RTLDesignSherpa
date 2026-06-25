# Episode 1: "Your sim passed. Your silicon's lying."

**Runtime target:** ~75 seconds
**Word count:** ~180 spoken
**Goal:** Hook the engineer who thinks "I tested it, it works." Set up the whole series by establishing the problem.

---

**[CAM: close-up of waveform viewer showing a passing CDC test, all green]**
**[VO]** Your CDC test passed. Every cycle. Every assertion. Green across the board.

**[CAM: cut to oscilloscope or board, glitching]**
**[VO]** Here's the part nobody warned you about: your RTL simulator does not model metastability. At all. A flop that catches a signal mid-flight in your sim just picks the new value, cleanly. Same flop on real silicon hovers at an analog intermediate voltage for an undefined amount of time, then resolves to *whatever*.

**[OVERLAY: "RTL sim ≠ silicon."]**

**[VO]** And it gets worse. Run two flops in parallel sampling the same multi-bit bus across clock domains — half the bits resolve to the new value, half stay on the old. Your destination reads a number that was *never on the source side.*

**[OVERLAY: "Multi-bit skew. The fun one."]**

**[VO]** Over the next five videos I'm going to show you this happening on a real FPGA. Not a slide. Real silicon, real numbers flickering on a real 7-segment display. Plus four different ways to fix it and one way that pretends to fix it.

**[CAM: board powered on, 7-seg showing scrambled garbage on right four digits]**
**[VO]** If you've ever shipped a design that "worked on the bench and failed in the field" — yeah. This is probably what happened.

**[OVERLAY: "Next: meet the board."]**
