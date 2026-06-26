# Episode 5: "Modes 2, 3, 4: How to do it for real"

**Runtime target:** ~105 seconds
**Word count:** ~250 spoken
**Goal:** The "correct" answers. Show all three working at 50 MHz, contrast their tradeoffs.

---

**[CAM: board, ctr2, clock-select 00 (72.7 MHz MMCM), mode 1 frozen]**
**[VO]** Three strategies that actually work. Same seventy-two megahertz MMCM clock — truly asynchronous to sys-clock — that broke modes zero and one.

**[BTN: BTNL — mode 02]**
**[CAM: display shows `02 00 xxxx` updating smoothly through 0000..FFFF]**
**[VO]** Mode two: asynchronous FIFO. Push every counter update on the source side, pop continuously on the destination side. The FIFO uses Gray-coded pointers internally, so the read-write comparison never sees a multi-bit skew. Display tracks the source perfectly, even at seventy-two megahertz against a hundred-megahertz consumer.

**[OVERLAY: "fifo_async — Gray pointers, no drama"]**

**[VO]** This has been the right answer since the mid-nineties. We just keep rediscovering it.

**[BTN: BTNL — mode 03]**
**[CAM: display shows `03 00`, values still legible but updating in obvious chunks]**
**[VO]** Mode three: two-phase handshake. A toggle protocol. Source snapshots the counter every two-hundred-fifty-six source clocks, raises a request line. Destination synchronizes the toggle, latches the data, sends an acknowledge back. Source drops the request. Two transitions per round-trip — that's the "two-phase" part.

**[OVERLAY: "cdc_2_phase_handshake — periodic snapshot, never garbage"]**

**[VO]** It never shows wrong values. But you can *see* the lag — the display updates in steps, not smoothly. That's the cost.

**[BTN: BTNL — mode 04]**
**[CAM: display shows `04 00`, similar stepwise updates]**
**[VO]** Mode four: four-phase handshake. Same idea, but the source holds the data through both an acknowledge and an acknowledge-deasserted phase. Twice the transitions per round-trip, more conservative, slightly slower.

**[OVERLAY: "cdc_4_phase_handshake — same safety, classic protocol"]**

**[VO]** When do you pick which? FIFO if you have bursty streaming data and bandwidth matters. Handshake if you only need occasional config updates and you want the simplest formal proof. Two-phase if throughput matters; four-phase if your reviewer demands the classic textbook waveform.

**[OVERLAY: "All three: 72 MHz async. Clean. Different tradeoffs."]**

**[VO]** Three different answers, all of them correct. Don't roll your own.

**[OVERLAY: "Next: build it yourself."]**
