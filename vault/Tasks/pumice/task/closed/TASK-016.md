# TASK-016: nothing checks the DDR2 initialization sequence for JEDEC legality

**Status:** CLOSED 2026-09-27 -- implemented as
`test_init_sequencer.py::ddr2_init_command_stream`, registered at GATE.
**Priority:** was P1, RAISED FROM P2 by Sean, 2026-09-27:
*"this should be the highest priority!!!"*

## What was built

Two checks, because the two halves fail differently:

**1. The command ORDER and CONTENT, against JESD79-2F section 3.3.** The
existing walk watched the six mode-register SHADOW STROBES, which cannot see
the `PRECHARGE ALL` and the two `REFRESH` commands JEDEC interleaves between
them, nor their position relative to the MR writes. The new check replays the
issued command stream:

    PREA -> MRS(2) -> MRS(3) -> MRS(1) -> MRS(0)+DLL
         -> PREA -> REF -> REF -> MRS(0) -> MRS(1) -> MRS(1)

**2. That the sequencer HONOURS ITS OWN WAIT REGISTERS.** This cannot be asked
by comparing against datasheet numbers -- no simulation can afford them; 200 us
of tINIT at 100 MHz is 20,000 cycles before the sequence even starts, which is
exactly why every environment zeroed the waits and why the hole existed. So it
is asked DIFFERENTIALLY: run the same sequence at two wait settings and require
every gap to grow by exactly the amount ITS OWN register grew. That needs no
model of the FSM's fixed per-state overhead, and it catches the failure that
matters -- a wait wired to nothing looks identical to a wait set to zero.

## Both checks were PROVEN to fire

Mutation-tested against the RTL, restored byte-identical after each (verified
with `cmp`):

| mutation | result |
|---|---|
| swap EMRS(2)/EMRS(3) -- the actual historical defect, fixed in 64fb2137 | FAILS with a readable diff of got vs want |
| wire the post-REFRESH gap to `t_mrd_wait` instead of `t_rfc_wait` | FAILS: "gap after REF is gated by t_rfc_wait: raising it by 5 changed the gap by 3" |

## Two defects found in the test itself while building it

* `run_once` constructed a SECOND `InitTB`, which re-opened the TB's log file
  (truncating the evidence the first run had written) and started a second
  clock driver on the same `mc_clk`. The test passed anyway -- that was luck.
  It now reuses one TB via `InitTB.restart()`.
* The wrapper set no `LOG_PATH`, so a passing run printed what it had verified
  to a stdout pytest swallows. Both evidence lines are now persisted.

## What is NOT covered, deliberately

The waits are still shortened, so the DATASHEET budgets (tINIT, tDLLK, tRFC at
their real values) are not exercised anywhere. Item 3 of the original plan -- a
single slow cell at realistic waits -- was not built. The differential check
proves the sequencer uses the registers it is given; it does not prove anyone
programs the right values into them. That is a separate, smaller gap.

The original P2 reasoning ("init runs once per power-up and currently works on
the board, so this is a coverage hole rather than a known defect") is the wrong
frame. Init is the one sequence whose output every later measurement depends on
and which nothing checks: a wrong MR0 ships the wrong burst length or CAS
latency into every subsequent result, and the failure presents as a data or
timing problem somewhere else entirely. "It currently works on the board" is an
observation about one part at one frequency, not evidence the sequence is
correct -- and this controller is about to be the basis of a DDR3/LPDDR3
successor whose init sequence differs in exactly the places that are hardest to
eyeball. An unverified sequence is the worst thing to port.

## What is missing

The scheduler-layer matrix
(`dv/tests/macro/test_pumice_sched_matrix.py`) replays every issued command
through a full JEDEC checker across 12 operating points -- but it **excludes the
initialization sequence**, explicitly and with a comment saying so.

The exclusion is necessary, not lazy. `PumiceMemCmdSchedulerTB._drive_idle()`
programs `t_init_wait_i = t_dll_wait_i = t_mrd_wait_i = t_rp_wait_i =
t_rfc_wait_i = 0`, because the real values are hundreds of microseconds of
power-up delay (200 us of stable clock, 200 CK of DLL lock) that no simulation
can wait out -- 200 us at 200 MHz is 40,000 aclk cycles per test. With those
waits zeroed, the init command spacing is deliberately not JEDEC-legal, so
replaying it through a legality checker reports the shortening rather than a
defect. At `ddr2_800_cl6_bl4` the first mission-mode ACT lands 21 cycles after
init's last REF against tRFC=26, which is exactly that artefact.

So the init sequence is the one part of the command stream that **no automated
check covers at any level**, at any operating point.

## Why it matters

* The init sequencer was already found incomplete once -- it issued only 4 MR
  writes -- and the MRS ORDER was wrong until 64fb2137 (EMRS3 before EMRS2;
  benign only because MR2/MR3 are 0 on this part). Both were found by reading
  the RTL against the spec, not by a test.
* Init is where a wrong value is most expensive and least visible: a bad MR0
  ships the wrong burst length or CAS latency into every subsequent
  measurement, and the failure looks like a data or timing problem somewhere
  else entirely.
* It is also the part that changes most when the family changes. A DDR3/LPDDR3
  successor has a different init sequence (ZQ calibration, different MR set,
  different waits), and porting an unverified sequence means porting whatever
  is wrong with it.

## Shape of the fix

The waits cannot be real, so the check has to be expressed in terms of the
PROGRAMMED waits rather than the datasheet ones:

1. Assert the init sequence's **command ORDER and CONTENT** against JESD79-2
   independently of timing: PREA, REF, REF, then MRS writes in the JEDEC order
   (EMRS2, EMRS3, EMRS1, MRS with DLL reset, PREA, REF, REF, MRS without DLL
   reset, EMRS1 OCD default/exit). Order and content are timing-free and are
   where both historical defects lived.
2. Assert each inter-command gap against the value the test PROGRAMMED into the
   corresponding `t_*_wait_i`, not against the datasheet -- i.e. that the
   sequencer honours its own configuration. That is checkable at any wait value
   including small ones, and it is what would catch a sequencer that ignores a
   wait register.
3. Run (1) and (2) at one REALISTIC wait setting as a single slow cell, so the
   datasheet path is exercised somewhere even if not in every test.

Item 2 is the one with teeth and the cheapest; do it first.

## Where it goes

`dv/tests/macro/` beside the matrix, reusing
`tbclasses/pumice_cmd_stream_checker.py` for the state model and adding an
order/content oracle. The checker already skips `OP_MRS` for legality, so it
needs an MRS-aware sibling rather than a change.

Related: [pumice BUG-003](../../bug/closed/BUG-003.md) (the defect whose hunt
produced the matrix this gap was found in),
[pumice TASK-015](../closed/TASK-015.md) (reset-parity and telemetry invariants -- the same
"nothing checks this layer" shape).

**A note on the link form, and its cost.** These are area-qualified PATHS, not
bare `[[BUG-003]]`. There are four `BUG-003.md` files in this vault (pumice,
rapids, stream, tooling) and four each of TASK-013 and TASK-015, so a bare
wikilink is ambiguous repo-wide -- resolving `[[BUG-003]]` from this directory
landed on `tooling/bug/open/BUG-003.md`. Seven bare `[[BUG-003]]` and fourteen
bare `[[TASK-013]]` links already exist in this area and are a separate cleanup;
new text should not add to them.

The cost is that a path ENCODES THE OTHER ITEM'S STATE, so it breaks when only
one of the two items changes state. That happened immediately: this file was
written in `open/` with a sibling link `TASK-015.md`, then moved to `closed/`
while TASK-015 stayed open, and the tree-wide link ratchet went red for every
session until it was repointed at `../closed/TASK-015.md`. A peer session hit the
red gate and reported it. **Any `git mv` between state directories can do this,
in either direction** -- moving this file, or moving the target. The ratchet is
the backstop, so the failure is loud rather than silent; just expect to fix
cross-state links as part of any state change, and grep the moved file's links
from its NEW directory before committing.
