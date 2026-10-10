# ISSUE-010: one extra AXI ID bit doubles the arbiter's pick cone

> **Migrated from `PUMICE-033`** on 2026-09-27, when this area's flat
> `dropped.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-033` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.



**Status:** DROPPED 2026-09-23 — the premise does not arise.

Sean 2026-09-23: "drop; ID's are always 8-bits or less."

The task existed because AXI_ID_WIDTH 8 -> 9 doubled the arbiter's pick cone and
cost 75 MHz closure ([[project_ddr2_char_board_timing_regression]]). If the ID
is 8 bits or fewer by construction, the 9-bit case is not a configuration this
controller has to support, so there is no constraint to characterise and no
cone to shrink. The measured timing finding stays valid history -- it is why the
board build pins 8 -- it just is not open work.

<details><summary>Original entry</summary>

**[archived heading] PUMICE-033 — one extra AXI ID bit doubles the arbiter's pick cone**
**[archived] Status:** open 2026-09-14  **Priority:** P1 — it is a hard constraint on where pumice can be used

**The finding: `AXI_ID_WIDTH` 8 -> 9 takes the arbiter's
`r_rd_pop -> r_wr_col_q` path from 13 logic levels to 26, and 75 MHz from
+1.100 ns to -6.602 ns.** Measured at SYNTHESIS, before placement, so it is the
netlist and not congestion. Same RTL, same constraints, same clocks, same
synth settings; the only difference is the parameter.

| ID width | logic levels | data path delay | post-route slack |
|---|---|---|---|
| 8 | 13 | 11.09 ns | +1.100 |
| 9 | 26 | 20.21 ns | -6.602 |

**Why it matters beyond this board.** BRIDGE-016 made fabric IDs
`{master index, master id}`, so ANY multi-master fabric in this repo hands its
slave more ID bits than a single master drives. pumice cannot currently absorb
that. It is usable behind one master, or behind a fabric that keeps the index
inside the master's own width -- which is what the char harness now does, by
putting the generator index in the top bits of the 8-bit id rather than on top
of it (7baf98780). That works and costs 1 bit of id space per doubling of
masters, but it is a workaround in the CONSUMER, not a fix in pumice.

**Where to look.** `pumice_cmd_arbiter.sv`: the pick is
`NUM_ENTRIES`-wide and ID comparisons are replicated across every entry, so an
extra bit multiplies by the entry count rather than adding to it. `qos_top` at
:818 is the same shape. The fix is presumably to compare a narrowed key, or to
pipeline the pick a stage further, not to widen everything and hope.

**How this was found**, because the route to it was wrong twice and the method
is the reusable part: the regression was first blamed on removing the data
bridges, on the read-return-ring depth, on constraints, on placement directives
and on hierarchy flattening -- each ruled out with its own build. Sean rejected
the bridge explanation on the grounds that generators behind a bridge and
generators without one look identical to pumice, which is correct and is what
forced the measurement that found it. **Logic levels at the synthesis
checkpoint are the discriminator**: if they differ between two builds, the cause
is RTL or parameters and can never be placement.

```
open_checkpoint <run>/synth_1/<top>.dcp
report_timing -to [get_pins -hier -filter {NAME =~ *u_arbiter/r_wr_col_q_reg*/D}] \
              -max_paths 1 -path_type full
```

**Definition of done:** pumice closes 75 MHz with `AXI_ID_WIDTH = 9`, or the
constraint is documented as permanent in the HAS with the id-space workaround
named as the supported pattern.

---


</details>

---
