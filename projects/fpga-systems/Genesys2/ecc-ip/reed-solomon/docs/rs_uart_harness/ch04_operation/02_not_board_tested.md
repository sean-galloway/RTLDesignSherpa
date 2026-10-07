# What Is Deliberately Not Board-Tested

A few things are intentionally left in simulation or are still open:

- The 2026-10-05 board battery ran the four single-decoder images. The
  dual-decoder comparator with `ENABLE_COMPARE=1` is the sim/DV domain; it
  caught real harness bugs (dropped/duplicated beats under skewed drains)
  without costing a bitstream.
- The erasure `f = 2t` boundary is a known open bug, filed as
  `vault/Tasks/projects/components/ecc-ip/reed-solomon/task/open/TASK-005.md`.
  `f = t` corrects and `f = 2t + 1` refuses on the board; `f = 2t` is flagged
  uncorrectable even though the design intent says it should correct.
- The component DV matrix — 195 cells per `TASK-001.md` — exercises the codec
  in ways the board harness does not replicate.
- The board validates two profiles: RS(252,236) t=8, S=4 on the Genesys 2, and
  the small RS(64,56) t=4 on the Nexys A7 (`RS_PROFILE=small`, issue #83);
  profiles outside those two are covered in simulation and component DV.
- The 2026-10-05 million-block soak is statistical, not exhaustive; its
  counters, the 2-of-74,240 mis-decodes, and the bounded-rate pass criterion
  are reported in the Board Validation Report.
