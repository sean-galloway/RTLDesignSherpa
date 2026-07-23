---
title: RDS-DV three axes
summary: BFM, sequence and randomization are ORTHOGONAL - pick each independently. Where the authoritative RDS-DV docs live for each.
---

# The three orthogonal axes

Every RDS-DV testbench composes three independent choices. They are frequently
conflated, and conflating them is how tests end up under-stressing the DUT:

| Axis | Question it answers | Independent of |
|---|---|---|
| **BFM** | *Who* drives and monitors the wires? | what traffic, what timing |
| **Sequence** | *What* transactions are sent? | who drives them, how fast |
| **Randomization** | *When* - the delay/timing shape | who drives, what is sent |

Pick each one deliberately. A GAXI master (BFM) can run a walking-ones pattern
(sequence) at `backtoback` timing (randomization), or the same pattern under
`heavy_pause` - all four combinations are valid and they test different things.
Changing one does not imply changing another.

The most common mistake is treating "I used the framework BFM" as sufficient.
The BFM axis says nothing about coverage; a correct BFM sending an
under-stressed sequence at a gappy delay profile is a weak test that looks
rigorous. See the case study in [[randomization]].

## The docs are good - use them, do not re-derive

RDS-DV ships per-family documentation and it is the authority. Do not
reverse-engineer the API from source, and do not restate it here (it rots).

    https://sean-galloway.github.io/RTLDesignSherpa-DV/
    <RDS-DV>/docs/components/<family>/

Naming is consistent, one file per axis:

    components_<family>_overview.md        what the family is
    components_<family>_interfaces.md      BFM axis
    components_<family>_sequence.md        sequence axis
    components_<family>_randomization.md   randomization axis
    components_<family>_packet.md          packet/field layout
    components_<family>_compliance.md      protocol checking

Coverage is uneven, so check before assuming a page exists. As of 2026-07-23:

| Family | interfaces | sequence | randomization |
|---|---|---|---|
| axi4 | yes | yes | yes |
| axi5, axil4 | yes | - | - |
| apb, fifo, gaxi | - | yes | - |
| shared | - | - | yes (`flex_config_gen`, `flex_randomizer`, `randomization_config`) |
| apb5, axis4/5, dfi, smbus, uart, wavedrom | - | - | - |

`axi4` is the most completely documented family and the best model to read when
a page you want is missing elsewhere. `docs/components/shared/` covers the
cross-protocol machinery.

## Axis 1 - BFM

Never hand-roll a driver, monitor or decoder. Factory map, decision tree and
the trap list: [[bfm-usage]].

## Axis 2 - Sequence

Sequence classes exist for `apb`, `axi4`, `fifo`, `gaxi` (`APBSequence`,
`AXI4Sequence` + `AXI4Burst`, `FIFOSequence`, `GAXISequence`). They carry a lot
of ready-made traffic generators - walking ones/zeros, incrementing data,
dependency chains, corner cases, capacity and stress patterns, and for AXI4
memory-aware ones like row-hit bursts, row-miss pairs and bank spray.

Read the family's `_sequence.md` before writing a loop that pokes transactions
by hand: the pattern you need almost certainly exists, and the canned ones have
been debugged. AXI4 executes via a single `run_axi4_sequence(seq, ...)`.

Families without a sequence class (axis4/5, axil4, dfi, smbus, uart) are driven
directly through their components.

## Axis 3 - Randomization

Delay/timing shape. 19 named profiles in `FlexConfigGen.DEFAULT_PROFILES`;
`backtoback` is the saturating one. Which layer to use, the profile table, and
the rule that random traffic does NOT prove fairness: [[randomization]].

Related: [[tb-structure]], [[test-runner]], [[seeds-and-determinism]].
