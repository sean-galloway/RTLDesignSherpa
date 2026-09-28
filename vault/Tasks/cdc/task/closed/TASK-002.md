# TASK-002: a TB class lived inside test_fifo_async_wavedrom.py

> Migrated 2026-09-27 from `vault/Tasks/cdc/closed.md` as **CDC-004** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-16 — pure move, proven.

`FifoAsyncWaveDromTB` now lives at `bin/TBClasses/cdc/fifo_async_wavedrom_tb.py`,
beside the siblings it should always have sat with
(`counter_johnson_wavedrom_tb`, `counter_bingray_wavedrom_tb`). The test file
drops from 526 to 286 lines; imports split 6 to the TB, 15 staying with the
wrapper; the single consumer was rewired to import it.

**Correction to this task as filed:** the class is **237 lines (66-302)**, not
349. The original figure came from a boundary scan that overshot; the 241-line
diff reconciles with 237 plus the import-block tidy.

**How "changed nothing" was proven, because the obvious gate does not work.**
Byte-identical wavedrom JSON is NOT available: `get_wavejson_dir` documents
that "Wavedrom output is NOT deterministic -- two consecutive runs of the same
test produce different waveform lengths", and it writes to a GITIGNORED
`WAVES/staged/<module>/`, never to the committed diagrams. Measured directly:
two identical pre-move runs differed in bytes on all three files, with wave
lengths 55 vs 66 and 55 vs 61 — while the file set and all 12 signal names per
file stayed stable.

So the gate became: (1) the moved class body diffs **byte-identical** against
the extracted original — it does, the diff is empty; (2) `TEST_LEVEL=full`
passes 3/3; (3) staged output matches the pre-move baseline on file set and
signal names. All three hold.

Note `TEST_LEVEL` gates how many scenarios emit — `gate` emits two of three —
so this was baselined and validated at `full`, or a third of the output would
never have been exercised.

---
