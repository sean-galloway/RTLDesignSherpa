# TASK-022: the FPGA flow lock is keyed on the build directory, so two areas can drive one board

**Priority:** P1
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-30 (found by the scoria session; confirmed by rapids)

`make/fpga_flow.mk` serialises Vivado with a lock keyed on the **build
directory**:

    :82  BUILD_LOCK    ?= $(SELF_DIR)/.vivado-build.lock
    :84  VIVADO_LOCKED  = flock -n --conflict-exit-code $(LOCK_EXIT) $(BUILD_LOCK) $(VIVADO_BATCH)

That is deliberate and correct for what it guards -- its own comment at :77 says
so: "build-mon and build-perf own separate fpga/build trees and may run at the
same time; two of the same target may not."

**But a physical board is contended by its JTAG/UART serial, not by a build
directory.** `Genesys2/scoria/build-litedram` and `Genesys2/rapids/flows-rapids`
take two DIFFERENT locks and both proceed against one Genesys 2.

## Verified 2026-09-30, reading the makefile rather than trusting the report

- `VIVADO_LOCKED` is used 5 times, wrapping the four Vivado batch targets
  (project :418, synth :424, build :432, ila :441).
- **The hardware-touching rule is not among them.** `tcl-$(1)` at :258-262 --
  the rule that resolves `FPGA_JTAG_SERIAL` precisely so "a tcl that touches
  hardware can pin its target instead of taking whatever is first on the chain"
  -- invokes `$(VIVADO_BATCH)`, **not** `$(VIVADO_LOCKED)`. So the path that
  programs the board is unguarded even by the build-directory lock. This is
  worse than the original report, which said program/run were unguarded; the
  serial-pinned tcl path is too.
- `run-$(1)` (:268) and `run:` (:454) invoke `$(PYTHON) $(RUN_SCRIPT)` with no
  lock of any kind.
- There is no `program` target in this file at all.
- `FPGA_JTAG_SERIAL` appears twice, both times to TARGET hardware, never as a
  lock key. Nothing in the file is keyed on a board.
- **17 Makefiles inherit `fpga_flow.mk`** -- that is the blast radius of any fix.

## The near miss that surfaced it

scoria programmed the Genesys 2 repeatedly for the LiteDRAM board proof and held
`/dev/ttyUSB0` until 09:34:51. A rapids byte-perf characterization started on the
same board at 09:40:04 (`run_characterization.py --byte-perf`, 8 channels).
**Five minutes apart.**

No harm, and that was checked rather than assumed:
`rapids_byte_perf_prelim_20260930.json` carries `rapids_byte.bit` with its
sha256, 308 measured rows, `pass:True`, `perf_valid:True`, `errors:[]`,
`golden_mismatch:False`.

## Why this is P1: the failure is SILENT

A harness records the sha256 of the bitstream **it programmed**, not what is
actually on the device. A third party reprogramming mid-run leaves a results
file that looks entirely valid -- no error, no timeout, no golden mismatch --
while measuring someone else's design. Had those five minutes overlapped, that
is what would have been published as rapids byte-perf data.

Every other failure mode in this area announces itself. This one produces
numbers.

## Acceptance

- The board-touching paths (`tcl-*`, `run`, `run-*`, and any future `program`)
  take a lock keyed on the **board** -- the JTAG serial from the board registry,
  or the tty -- not on the build directory.
- The build-directory lock STAYS for Vivado builds. It is right for its purpose
  and `build-mon` / `build-perf` concurrency is deliberate; this is an
  additional lock, not a replacement.
- A harness reads the device ID back **from the device** at start and end and
  records it beside the bitstream sha256, so a mid-run swap is detectable after
  the fact rather than invisible. (rapids is adopting this for their final run
  independently of the lock.)
- All 17 inheriting Makefiles verified unbroken.

## Interim mitigation, in use now

Before programming a shared board, `fuser /dev/ttyUSB*` plus a `ps` for another
area's host script. `make ports` gives you the serial but says nothing about who
is holding it.

## Hazards

- This changes shared flow tooling that 17 Makefiles inherit. Do it when no
  characterization is live.
- On 2026-09-30 three sessions were live and **all three declined to take it**
  for that reason -- scoria (who found it, and was mid board-proof), rapids (who
  had a live 8-channel run on the board), and this session. That is the right
  instinct, not procrastination: a lock change landed under a running
  characterization is how you corrupt the run you were trying to protect.
- At filing time a rapids characterization was live on `/dev/ttyUSB0`
  (PID 3551976, `--byte-perf --channels 8 --resume`).

## References

- `make/fpga_flow.mk` :77-98 (the lock and its rationale), :258-262 (`tcl-$(1)`),
  :268 (`run-$(1)`), :454 (`run:`)
- `vault/handbook/agents/multi-agent-worktree.md` (1db6a139b) -- scoria's
  write-up of the mechanism
- [[TASK-020]], [[TASK-021]] -- the other open tooling items
