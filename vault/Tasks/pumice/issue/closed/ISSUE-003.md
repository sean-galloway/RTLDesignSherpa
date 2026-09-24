# ISSUE-003: SCHED_WR_WM.wr_batch_max may clobber the whole register on write
> **Was `PUMICE-047` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** RESOLVED 2026-09-24 — the clobber premise is DISPROVEN and the real
cause is different: the knob is wired and writable, it is simply UNREACHABLE at
the shipped watermarks. Residue re-filed as [[TASK-008]]. (was: open
2026-09-23, P2)

**1. There is no clobber.** `csr_write_field` is biten-masked and correct. The
gen_replica test now reads the WHOLE SCHED_WR_WM word back and decodes all
three fields, instead of re-reading the one field it just wrote -- which is the
check the task correctly said was missing, since a per-field readback re-reads
exactly the bit a whole-register write would have got right. With
`wr_batch_max` programmed, `wr_high_wm`/`wr_low_wm` read back intact and all
FOUR gen_replica cells pass (91 s). The 4 cells that broke during the original
investigation were the stale DV regmap, fixed in aea7238c5: it predated
`16eda8ed7`, so `wr_batch_max` did not exist in it and `RSVD` still spanned
`31:16`.

**2. Why the original mutation "passed in 43s" — it could not have failed.**
The drain has THREE exits and the cap is only one of them
(`pumice_cmd_arbiter.sv:1094-1120`):

    w_batch_done                   -> yield, and set r_rd_owed (hysteresis)
    w_wr_occ <= sched_wr_low_wm_i  -> drained down, stop
    sched_wr_high_wm_i == 0        -> batching disabled

The occupancy exit is independent of the cap, so at the watermarks the repro
uses (hi=8 / lo=4) a drain ends after about FOUR writes -- and a cap of 16 is
never reached. `wr_batch_max` can only bind when it is smaller than
`(wr_high_wm - wr_low_wm)`. Setting it to 0 at hi=8/lo=4 therefore changes
nothing observable, which is exactly the reported "PASSED in 43 s". That is an
unreachable knob, not a decorative one and not a clobber.

Measured at the top level (gen_replica gap=15, batching on): hi=8/lo=4 gives
the same result at batch_max 16 and 0; widening to hi=8/lo=0 makes the setting
visible (11.5 s at 0 vs 17.6 s at 1).

**3. The knob is wired**, verified port by port: CSR ->
`pumice_top.sv:257` -> `pumice_core.sv:518` -> `pumice_mem_cmd_scheduler.sv:482`
-> `pumice_cmd_arbiter.sv:1094`.

**Do (unchanged, and now correctly scoped):** the mutation the task asked for is
still worth having, but it has to run where the cap can bind -- `batch_max <
(hi - lo)` -- or it proves nothing. Tracked as [[TASK-008]] with what a
first attempt got wrong.

<details><summary>Original entry</summary>

**[archived] Status:** open 2026-09-23  **Priority:** P2 — an untrusted knob on
a fix that is otherwise verified

`wr_batch_max[23:16]` was added to SCHED_WR_WM (`16eda8ed7`) and the default
path works: the bounded drain is live at reset 16 and the concurrent_rw repro
passes through it. What is NOT proven is the knob.

Writing the field via `tb.csr_write_field("SCHED_WR_WM","wr_batch_max",0)`
behaved as if it wrote the WHOLE register: `wr_batch_max=0` should leave
batching enabled but unbounded (reproducing the starvation), and instead the
cell PASSED in 43s — the signature of batching being disabled outright, i.e.
`wr_high_wm` going to 0 as collateral. The same edit broke 4 `gen_replica`
cells, consistent with one cause.

The readback assert did not catch it because it reads the same field it wrote.

**[archived] Do:** check `csr_write_field`'s read-modify-write against a
multi-field register, then re-run the mutation — `wr_batch_max=0` MUST fail the
repro (~347s timeout) or the knob is decorative. Until then do not tune this
field on silicon.

</details>

**2026-09-23 — STRONG CANDIDATE ROOT CAUSE FOUND, and it is not
`csr_write_field`.** Found while regenerating registers for [[TASK-002]]:
`dv/tbclasses/pumice_regmap.py` is a SECOND generated copy of the pumice
regmap, and it had never been regenerated after `16eda8ed7` added the field.
It is the map the component TBs load (`pumice_top_csr_tb.py:132`,
`pumice_top_tb.py:57`), and in the stale copy:

- `wr_batch_max` **did not exist at all**;
- `RSVD` spanned **31:16**, i.e. straight across the new field's bits;
- the register default read `0x00000102` instead of `0x00100102`.

Any read-modify-write seeded from that map therefore writes ZEROS over
`[23:16]`, which is exactly the "wrote the whole register" signature the task
describes — no defect in `csr_write_field` required. The stale copy is
regenerated and both in-tree maps now agree (`wr_batch_max` present,
`RSVD` 31:24, default `0x00100102`).

This is a CANDIDATE, not a closure: the task's own mutation is still the test.
Re-run it against the corrected map — `wr_batch_max=0` must fail the repro at
~347 s. If it now does, this was the cause and 047 closes; if it still passes,
the clobber is real and lives elsewhere.

**Correction (same day):** this is NOT an orphan the tooling cannot reach, and
the first write-up here called it one. `bin/peakrdl_generate.py` regenerates
the regmap, and `--regmap-output` targets a non-default path, so the DV copy is
fully generable -- the failure was simply that nobody passed it after
`16eda8ed7`. pumice's RDL has TWO generated destinations and the regen command
has to name both:

```
# TWO invocations. --regmap-output REPLACES the default regmap, it does not
# add a second one, so one run can only ever produce one of these files.
P=projects/components/memory-controllers/pumice-ddr2-lpddr2

# 1. regblock + docs + the regs/generated regmap
python3 bin/peakrdl_generate.py $P/rtl/macro/pumice_csr.rdl \
    -o $P/regs/generated --no-html

# 2. the DV-facing regmap the component TBs load
python3 bin/peakrdl_generate.py $P/rtl/macro/pumice_csr.rdl \
    -o $P/regs/generated --no-html \
    --regmap-output $P/dv/tbclasses/pumice_regmap.py
```

(Verified: the file committed in aea7238c5 is byte-identical to what that
command produces -- the content was right, the method was a hand-copy.)

---
