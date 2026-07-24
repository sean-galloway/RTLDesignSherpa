<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — closed (complete)

_None._

---

### TOOL-009: Python version mismatch breaks EVERY Verilator build on this box
**Priority:** P0 — blocks all simulation, and blocks TOOL-008 validation
**Status:** ✅ Closed 2026-07-23 — fixed and verified green (see Resolution)
**Owner:** Sean (decide the fix) / Claude (apply)

**Symptom:** every test fails at link time with
`undefined reference to Vtop::Vtop(char const*)`. Not an RTL or testbench
problem, and **not** caused by the TOOL-008 Makefile rewrite — it reproduces
under raw `pytest` with no make involved at all.

**The chain, each link verified by execution:**

1. `/usr/bin/python3` is a symlink to **python3.10** (3.10.12).
2. The venv was built from `/usr/bin/python3.11`, which on this box is
   **3.11.0rc1** — a release candidate, not a release (`venv/pyvenv.cfg`).
3. `cocotb_test/simulator.py:215` sets `PYTHONHOME = sysconfig prefix` for the
   simulator subprocess. Inside a venv that is the **venv** prefix (3.11).
4. Verilator's `share/verilator/include/verilated.mk:20` hardcodes
   `PYTHON3 = /usr/bin/python3` — baked in when Verilator was configured, so it
   is **3.10**.
5. Building `Vtop__ALL.cpp` runs that 3.10 interpreter with `PYTHONHOME`
   pointing at a 3.11 stdlib. It dies:
   `AssertionError: SRE module mismatch` (from `import re`).
6. The recipe is `... $^ > $@`, so the shell has **already truncated**
   `Vtop__ALL.cpp` before the interpreter fails. Result: a **zero-byte**
   amalgamation.
7. Empty `.cpp` -> 824-byte `Vtop__ALL.o` -> archive with no `Vtop` symbols ->
   the link errors above.

**Proof of the fix:** `make -f Vtop.mk PYTHON3=<venv>/bin/python3 Vtop__ALL.cpp`
produces a correct 522-byte file, and `test_amba_clock_gate_ctrl` then
**passes**. Nothing else was changed.

**Why it looks like a flaky/stale-build problem and is not.** `--reruns 3` and
xdist retries re-enter the same broken build dir and fail identically — the
five `*_results.xml` files in one `local_sim_build/` dir are that. `clean-all`
does not help: a fresh dir reproduces it 2/2. Do not chase this as a stale
artifact; see [[running-regressions]].

**Fix options, in preference order:**
- [ ] **Rebuild the venv on the interpreter `/usr/bin/python3` resolves to**
      (3.10.12), so `PYTHONHOME` and Verilator's hardcoded `PYTHON3` agree.
      Robust, survives a Verilator reinstall, no root needed. Confirm nothing
      in the stack actually requires 3.11 first.
- [ ] Or repoint `/usr/bin/python3` at 3.11 — needs root and changes system
      behaviour for everything else on the box.
- [ ] Or patch `verilated.mk:20` to `PYTHON3 ?= /usr/bin/python3` and export
      `PYTHON3` from `env_python` (make lets the environment win over `?=`).
      Cheapest, but it edits a file under `~/tools` that a Verilator reinstall
      silently reverts — if chosen, `bin/install_tools.sh` must apply it.

**Do not build a venv on a release candidate.** 3.11.0rc1 should not be the
base for anything; whichever option is chosen, pin a released interpreter.
Belongs with TOOL-004 — this is exactly the class of gap "validate the
bootstrap on a genuinely clean box" exists to catch, and the rebuilt
workstation shipped it.

**Resolution (2026-07-23):** rebuilt the venv on `/usr/bin/python3` (3.10.12) so
it matches the interpreter Verilator hardcodes. Three pins required Python
>=3.11 and now carry environment markers so one `requirements.txt` serves both
this Jammy box and Sean's 3.11 server:

| pin | >=3.11 | <3.11 |
|---|---|---|
| numpy | 2.3.4 | 2.2.6 |
| contourpy | 1.3.3 | 1.3.2 |
| Pint | 0.25 | 0.24.4 |

**Why 3.10 and not 3.11 on this box:** Ubuntu 22.04 (Jammy) ships python3.11
only as `3.11.0~rc1-1~22.04` — a release candidate. `/usr/bin/python3` is 3.10
and is what Verilator baked in. Sean's server is a later Ubuntu where
`/usr/bin/python3` already is 3.11+, which is why this never bit there. The bug
was never "3.11 is broken", it was the venv and Verilator disagreeing.

**numpy downgrade risk, assessed not assumed:** numpy is imported by exactly
one module in RDS-DV (= the `cocotb-framework` package),
`components/shared/memory_model.py`, and only via API stable since numpy 1.x
(`frombuffer`, `zeros`, `arange`, `append`, `any`, `sum`, `flatnonzero`,
`count_nonzero`, boolean masks). 2.3.4 -> 2.2.6 is a minor step inside 2.x, so
none of the 1.x->2.x breakage applies. Verified by running MemoryModel
write/read/access-map/expand under 2.2.6. The repo's other 17 numpy users are
`bin/dma_model/` analysis and plotting scripts, not the simulation path.

**Verified green after the fix:** `test_amba_clock_gate_ctrl` 1 passed, and
`make 'run-apb5_master*-gate'` -> 3 files / 9 passed at 7 workers, both through
the new TOOL-008 Makefile.
