# RLB — Open (accepted, not started)

---

_Nothing open._

## RLB-017 — pit_regmap.py contradicts its own RDL on 14 fields
**Status:** open 2026-09-24  **Priority:** High

Found by the `.rdl` regen gate ([[TASK-089]]). `rtl/pit_8254/pit_regmap.py`
was produced by the SUPERSEDED `bin/peakrdl_to_regmap.py` -- its banner still
says so -- and it disagrees with a fresh `bin/peakrdl_generate.py --regmap`
run on 14 fields across 7 registers:

| field | committed | RDL / PeakRDL |
|---|---|---|
| COUNTER0/1/2_DATA.reserved | `sw='rw'` | `sw='r'` |
| PIT_CONFIG.reserved, PIT_CONTROL.reserved, PIT_STATUS.reserved, RESERVED_0C.reserved | `sw='rw'` | `sw='r'` |
| PIT_CONTROL.bcd / counter_select / mode / rw_mode | `sw='rw'` | `sw='wo'` |
| PIT_STATUS.counter0/1/2_status | `sw='rw'` | `sw='r'` |

The RDL is unambiguous: every reserved field is `sw = r; hw = na;`.

**This is not cosmetic.** `bin/TBClasses/apb/register_map.py` derives its
writable mask from `sw` (`0xFFFF_FFFF if reg.get('sw') == 'rw' else 0`, and
`if f.get('sw') not in ('rw','w')`). A walk driven by this map writes
read-only reserved bits and treats four write-only PIT_CONTROL fields as
read-write, reading them back for comparison. `pit_helper.py` consumes it.

Fix is to regenerate via `bin/peakrdl_generate.py --regmap-output
rtl/pit_8254/pit_regmap.py` and add the entry to `bin/check_rdl_regen.py`.
But regenerating CHANGES DV BEHAVIOUR, so capture `test_apb4_pit_8254.py`
before and after and explain any delta -- do not assume a pass means nothing
moved. The other three RLB regmaps already reproduce cleanly.
