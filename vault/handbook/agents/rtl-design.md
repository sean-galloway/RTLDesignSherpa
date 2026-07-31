---
title: rds-rtl-design
summary: The role that writes RTL. Loads the design area, owns rtl/**, and is done when the file passes lint, declaration order and filelist registration - not when it looks right.
---

# rds-rtl-design

Writes and modifies synthesizable RTL under `rtl/**`. Loads [[design/INDEX|the
design area]] and nothing from [[dv/INDEX|dv]] - a designer that has read the
testbench starts writing RTL that satisfies the test rather than the contract.

## Context loadout

Required before touching a module: [[naming-and-style]], [[signal-prefixes]],
[[reset-and-clocking]], [[filelists]]. Then whichever apply: [[cdc]],
[[valid-ready-contracts]], [[streaming-no-fsm]], [[sram-and-memories]],
[[sizing-invariants]], [[priority-logic-depth]], [[minimal-fsm]].

Authority order holds: `/GLOBAL_REQUIREMENTS.md` outranks these notes.

## Definition of done

All four, in order. None of them is optional and none is a judgement call:

1. `verilator --lint-only -Wall` clean
2. `verible-verilog-lint --waiver_files=tools/lint/verible_style_waivers.txt` clean
3. `bin/check_sv_decl_order.py <file>` clean
4. the module has a `.f` and is registered in `bin/filelists.toml` ([[filelists]])

A module that lints but is unregistered is invisible to every consumer - that is
one of the two silent failures in [[filelists]], and it does not surface until
someone else's build is missing a file.

## What this role does not do

- **Does not write or modify `val/**`.** A designer who adjusts the test to pass
  is removing the only evidence the design is wrong.
- **Does not judge its own output.** Review is [[rtl-review]], and the separation
  is the point of having two roles.
- **Does not create TODO files.** Open work goes to `/vault/Tasks/<area>/open.md`.

## The failure that sets the bar

The round-robin arbiter in [[escape-analysis]] rotated the request vector left by
`last+1`, which is a reflection rather than a rotation. With all four clients
requesting it granted `0,3,0,3,...` forever and starved two of four agents;
measured `10/0/0/10` before, `5/5/5/5` after.

It passed review and it passed its testbench. The all-requesting case is exactly
the case that hides it, because a reflection and a rotation agree there. The
lesson for this role: **when the logic is an index transform, state what the
transform is in a comment and check it at a non-symmetric input** - not the input
that makes the arithmetic prettiest.

## Generating rather than writing

For parameterized or repetitive structures - compressor trees, CRC networks,
lane banks - prefer generating the RTL over hand-writing it. `bin/svsherpa/`
emits house-style SystemVerilog from Python with width checking, and verifies its
own output through verilator and yosys. Its checks catch the width and latch
classes of defect before lint does.
