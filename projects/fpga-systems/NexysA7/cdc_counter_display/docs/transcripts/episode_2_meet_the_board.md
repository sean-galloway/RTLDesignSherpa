# Episode 2: "Meet the demo board"

**Runtime target:** ~90 seconds
**Word count:** ~210 spoken
**Goal:** Orient the viewer. What the board does, what each control means. Keep it pacey.

---

**[CAM: top-down of Nexys A7]**
**[VO]** This is a Digilent Nexys A7-100T. Artix-7 FPGA, 100 megahertz clock, eight 7-segment digits, five push buttons, sixteen slide switches, eight LEDs. Standard university board. Costs about three hundred bucks.

**[CAM: overlay highlighting display sections]**
**[VO]** On the display, left-to-right: two digits for the CDC mode number, two digits for the clock-select index, four digits for a 16-bit counter value. The whole demo runs four independent counters in parallel. Each counter has its own clock and its own CDC strategy.

**[CAM: zoom on board, MMCM area on chip die diagram]**
**[VO]** About those clocks. There's a single MMCM on the FPGA generating four outputs at co-prime divisors — eleven, twenty-nine, sixty-seven, one-twenty-eight. They're *truly asynchronous* to each other. Plus a fifth source: a plain sys-clock divider for slow-counting-by-eye demos. Per counter, a glitchless BUFGMUX clock-multiplexer picks one. You switch on the fly.

**[OVERLAY: "5 clocks per counter. Glitchless mux. Truly async between MMCM outputs."]**

**[CAM: switches close-up]**
**[VO]** SW one and zero pick which counter you're looking at — zero through three. SW fifteen turns on auto-increment for the selected counter, so you don't have to mash a button to drive transitions.

**[CAM: buttons close-up, narrating each as it's pointed at]**
**[BTN: BTNC]** **[VO]** Center button: inject a press into the selected counter.
**[BTN: BTNU]** **[VO]** Up button: clock goes *faster*. Walks the clock-select index down toward the seventy-two megahertz MMCM output.
**[BTN: BTND]** **[VO]** Down button: clock goes *slower*. Eventually back to the divided-clock branch.
**[BTN: BTNL]** **[VO]** Left button: cycle CDC mode. Zero through four. We'll get to all of them.
**[BTN: BTNR]** **[VO]** Right button is reset, in case you panic.

**[CAM: LEDs close-up]**
**[VO]** LEDs zero through three light up one-hot to show the selected counter. The rest are activity indicators — alive pulse, UART traffic, system OK and MMCM locked.

**[CAM: full board, settled]**
**[VO]** No laptop required. Everything I'm about to show you, you can drive from the board alone. The UART is for when you want to script it. Next video — let's break something.

**[OVERLAY: "Next: mode zero. No CDC. Why does it ever work?"]**
