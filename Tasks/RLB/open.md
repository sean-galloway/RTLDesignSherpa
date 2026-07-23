# RLB — Open (accepted, not started)

---

## RLB-003 — Fix remaining MAS register documentation (4 blocks)
**Status:** open 2026-07-22

The four `documentation` issues whose problems are targeted (wrong reset values,
undocumented bits, wrong port lists) rather than wholesale-wrong maps. Same
method as RLB-002: rewrite the MAS register chapter against the RTL decode,
independently re-verify offsets with `rlb-doc-review` (or scratchpad copy of)
`verify_regmap.sh` before committing, commit scoped to each block's docs,
reference the issue.

- **gpio** — issue #43. Undocumented GPIO_CONTROL[1] INT_ENABLE (per MAS, irq
  can never assert); 4 omitted registers (RAW_INT 0x24, OUTPUT_SET/CLR/TGL
  0x28/2C/30); wrong reset values on CONTROL/INT_POLARITY.
- **hpet** — issue #45. HPET_ID vendor/revision hardcoded (params dead) + field
  errors. (NOTE: the review's hpet criticals C1-C3 are RTL bugs → RLB-004.)
- **ioapic** — issue #47. Register-map/field corrections (mostly High; the C1
  double-delivery is an RTL bug → RLB-004).
- **pit_8254** — issue #51. PIT_STATUS reset value wrong (doc 0x00303030,
  actual 0x00404040); wrong top-level port list, wrong PADDR width (12b not
  32b), undocumented PPROT, wrong reset port name (pit_resetn not pit_rst_n);
  SLVERR-on-unmapped behavior doesn't exist (errors tied off, 0x20 aliasing).

## RLB-005 — Clean up rtc wavedrom README third register-map copy
**Status:** open 2026-07-22

`docs/rtc_mas/assets/wavedrom/timing/README.md` still holds a THIRD,
contradictory register map (TIME_LO@0x00, REG_A/B/C, UIP/rate-select) that the
rtc fix (RLB-002) left as out-of-scope. Correct it to the real map or regenerate
the wavedrom assets. (pic_8259 and pm_acpi wavedrom READMEs were already fixed in
their commits.)
