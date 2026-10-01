# Overview

`projects/fpga-systems/bin/` is the shared host-side layer that every board flow
in this repository imports by bare module name. It answers four questions that
every flow used to answer for itself:

1. Which serial port is my board on?
2. How do I read and write its registers?
3. What order do my test steps run in, and what did the previous one produce?
4. Which FPGA am I about to program, and is anyone else using it?

Before this layer existed, each flow grew its own answer. Four near-identical
`autodetect_port()` functions globbed `/dev/ttyUSB*`; seven copies of
`program_fpga.tcl` each hardcoded a JTAG serial and invented their own
environment variable to override it. Those copies did not drift because anyone
was careless -- they drifted because nothing made them one thing.

## What this book covers

The shared layer, the conventions that govern code built on it, and the path
from a host program down to a register write landing on silicon.

| Chapter | Subject |
| --- | --- |
| 2 | The UART flow: port discovery, probes, the link, the wire protocol |
| 3 | Sequences: the model, the context, the runner |
| 4 | Boards: the registry, programming, locking, identity |
| 5 | Naming and layout conventions, and how paths are resolved |
| 6 | Standing up a new flow |

## What this book does not cover

- **Method.** How to run a regression, how to write a testbench, how to debug a
  board. That lives in `vault/handbook/`, which is the repository's memory.
  Where this book touches a method note it links to it rather than restating it;
  a second copy is how documentation rots.
- **The RTL on the other side of the UART.** The FPGA-side bridge that turns the
  ASCII protocol into AXI4-Lite transactions is specified with the RTL.
- **Per-area flows.** What pumice's `seq_char` measures, or what the stream
  monitor campaign proves, belongs to those areas.

## The one property worth protecting

Everything in this layer is arranged so that **the same host code runs against
the FPGA and against a simulation**. The byte stream is identical; only the
object carrying the bytes differs.

That is not an elegance argument. A harness whose sim path and silicon path are
different code has two chances to be wrong and no way to tell which one is. When
a board result and a sim result disagree here, the disagreement is about the
design, because nothing else differs.

Chapter 2 explains the mechanism (an injected byte channel), and Chapter 3
explains the rule that keeps it true (a sequence never opens its own port).
