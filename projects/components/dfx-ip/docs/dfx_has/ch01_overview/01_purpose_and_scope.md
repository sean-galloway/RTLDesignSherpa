# Purpose and Scope

## Purpose

Give every board and testbench in the house the same minimal debug port
from the outside: a JTAG cable (or a cocotb BFM driving the same four
pins) that can **observe** what happened, **poke** configuration, and —
only where a processor justifies it — **override** execution.

DFX-IP exists because today the house has the observation half of that
port and nothing else: `*_monlite` taps report hits, misses, counters, and
state transitions without perturbing the measured paths, but there is no
supported way to reach *in* — no register poke, no core halt. Any agent
or developer poking a running system today does it through testbench
hierarchy, which dies at FPGA bring-up.

## Scope

**In scope (this line):**

- `jtag-tap` — the IEEE 1149.1 transport and its TCK domain.
- `jtag-axil-agent` — the config plane: AXIL4 read/write master driven
  from JTAG. One agent serves every component on the fabric.
- `riscv-debug` — the override plane: RISC-V Debug Specification debug
  module (DTM/DM, abstract commands, program buffer) coupled to a core's
  debug mode. Built for the falcon rungs and hive-serv's cores.
- The access model governing which plane each consumer needs (ch02).

**Explicitly out of scope:**

- The observation plane — monlite/MonBus already exists house-wide and
  keeps its own specs.
- In-band software debug stubs, trace encoders (these are core/family
  concerns; the override plane gives them their transport).
- The test plane (scan/BIST) — reserved as future HAS chapters.

## Design posture

Education-first, same as the rest of the house: every block is small
enough to read cold, formally verified where the house pattern applies,
and dogfooded — the config plane's own AXIL transactions are observed
through monlite taps like any other master's.
