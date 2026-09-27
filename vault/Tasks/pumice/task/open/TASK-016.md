# TASK-016: nothing checks the DDR2 initialization sequence for JEDEC legality

**Status:** open 2026-09-27. **Priority:** P2 -- init runs once per power-up and
currently works on the board, so this is a coverage hole rather than a known
defect. It is filed because the hole was found by accident and would otherwise
be forgotten.

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
[pumice TASK-015](TASK-015.md) (reset-parity and telemetry invariants -- the same
"nothing checks this layer" shape).

**A note on the link form.** These are area-qualified PATHS, not bare
`[[BUG-003]]`. There are four `BUG-003.md` files in this vault (pumice, rapids,
stream, tooling) and four each of TASK-013 and TASK-015, so a bare wikilink is
ambiguous repo-wide -- resolving `[[BUG-003]]` from this directory landed on
`tooling/bug/open/BUG-003.md`. Seven bare `[[BUG-003]]` and fourteen bare
`[[TASK-013]]` links already exist in this area's files and are a separate
cleanup; new text should not add to them.
