# Episode 2: "Meet the demo board"

**Runtime target:** ~90 seconds
**Word count:** ~210 spoken
**Goal:** Orient the viewer. What the board does, what each control means. Keep it pacey.

---

**[CAM: top-down of Nexys A7]**
**[VO]** This is a Digilent Nexys A7-100T. Artix-7 FPGA, 100 megahertz clock, eight 7-segment digits, five push buttons, sixteen slide switches, eight LEDs. Standard university board. Costs about three hundred bucks.

**[CAM: overlay highlighting display sections]**
**[VO]** On the display, left-to-right: two digits for the CDC mode number, two digits for the clock pickoff, four digits for a 16-bit counter value. The whole demo runs four independent counters in parallel. Each counter has its own divided clock and its own CDC strategy.

**[CAM: switches close-up]**
**[VO]** SW one and zero pick which counter you're looking at — zero through three. SW fifteen turns on auto-increment for the selected counter, so you don't have to mash a button to drive transitions.

**[CAM: buttons close-up, narrating each as it's pointed at]**
**[BTN: BTNC]** **[VO]** Center button: inject a press into the selected counter.
**[BTN: BTNU]** **[VO]** Up button: clock goes *faster*. Cuts the period in half each press.
**[BTN: BTND]** **[VO]** Down button: clock goes *slower*.
**[BTN: BTNL]** **[VO]** Left button: cycle CDC mode. Zero through four. We'll get to all of them.
**[BTN: BTNR]** **[VO]** Right button is reset, in case you panic.

**[CAM: LEDs close-up]**
**[VO]** LEDs zero through three light up one-hot to show the selected counter. The rest are activity indicators — alive pulse, UART traffic, system OK.

**[CAM: full board, settled]**
**[VO]** No laptop required. Everything I'm about to show you, you can drive from the board alone. The UART is for when you want to script it. Next video — let's break something.

**[OVERLAY: "Next: mode zero. No CDC. Why does it ever work?"]**
