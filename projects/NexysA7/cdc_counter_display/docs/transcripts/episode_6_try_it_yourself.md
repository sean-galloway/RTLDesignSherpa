# Episode 6: "Try it yourself"

**Runtime target:** ~75 seconds
**Word count:** ~180 spoken
**Goal:** Conversion. Get them to clone the repo and run it.

---

**[CAM: terminal showing git clone running]**
**[VO]** Everything I just showed you is open-source. RTL, constraints, host scripts, simulation, documentation. Link in the description.

**[OVERLAY: "github.com/sean-galloway/RTLDesignSherpa"]**

**[CAM: tree view of projects/NexysA7/cdc_counter_display/]**
**[VO]** It lives under `projects/NexysA7/cdc_counter_display/`. There are two builds in there — a simple button-driven phase one and the full UART-harness phase two we've been driving.

**[CAM: terminal showing `make build-demo` and `make program-demo`]**
**[VO]** If you have a Nexys A7 and Vivado, `make build-demo`, then `make program-demo`. Five to ten minutes for the bitstream, plus however long Xilinx takes to convince your USB cable to work.

**[CAM: opening docs/RUNBOOK.md]**
**[VO]** Read `docs/RUNBOOK.md` first. It's the operator's guide — every button, every switch, what each digit on the display means, and a step-by-step "watch CDC break" script you can follow live.

**[CAM: opening docs/HARNESS.md]**
**[VO]** `docs/HARNESS.md` has the full CSR map if you want to drive it from a Python script over UART. There's a runner included — `host/run_cdc_demo.py` — with a `watch-fail` subcommand that does the whole sweep automatically and prints the variance per pickoff. Quantitative proof, not just "I saw it flicker."

**[CAM: board running mode 2 at the 72.7 MHz MMCM clock, cleanly]**
**[VO]** Pick a counter. Set it to broken mode. Walk the clock select up into the MMCM bank — truly async, co-prime divisors — and watch something break. Then switch CDC modes until it stops. That's the lab.

**[OVERLAY: "Don't roll your own CDC. Use the primitives. Read the runbook."]**

**[VO]** See you next series.
