---
title: projects/fpga-systems/rtl
summary: mem_char_framework - shared memory-characterization harness RTL (char generator, delay engine, harness CSR) used by pumice and scoria
repo: projects/fpga-systems/rtl
---

# projects/fpga-systems/rtl

**Code:** [`projects/fpga-systems/rtl/`](../../../../../projects/fpga-systems/rtl)

mem_char_framework - shared memory-characterization harness RTL (char
generator, delay engine, harness CSR) used by pumice and scoria

## What lives here

Knowledge notes about `projects/fpga-systems/rtl` - design intent, gotchas, decisions and
their rationale. Not a duplicate of the code and not a substitute for it.

Method and practice belong in [the handbook](../../../../../vault/handbook/INDEX.md); work items belong in
[vault/Tasks/](../../../../../vault/Tasks/INDEX.md). This page is for *this area's* durable context: why it is
shaped the way it is, and what bit someone once.

## Who depends on it

The framework is shared, not orphaned: `NexysA7/pumice/ddr2_char_framework`
and its characterization host scripts import the tbclasses from here, and
`Genesys2/scoria/host/check_regnames.py` reads the same register maps. Any
move has to repoint those references in the same commit.

## Notes

_None yet._
