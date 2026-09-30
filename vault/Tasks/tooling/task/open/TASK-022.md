# TASK-022: the FPGA flow lock is keyed on the build directory, so two areas can drive one board

**Priority:** P1
**Status:** open -- the LOCK landed 2026-09-30; the device-ID readback has not
**Owner:** TBD
**Filed:** 2026-09-30 (found by the scoria session; confirmed by rapids)

## Landed 2026-09-30: the board-keyed lock

`projects/fpga-systems/bin/board_lock.sh` -- a command PREFIX, deliberately the
same shape as `VIVADO_LOCKED` so it composes inside the `define`/`eval` rules
without quoting games. It resolves the board's JTAG serial from the registry
(falling back to the `BOARD` name), takes `flock -n` on
`$RDS_BOARD_LOCK_DIR/rds-board-<key>.lock` (default `/tmp`), and `exec`s the
payload. fd 9 survives the exec and an flock lives on the open file description,
so **the payload holds the board for its whole life** and the kernel releases it
when the payload dies -- no stale lock, no PID file needing the liveness check
that has failed this repo before.

Wired into the five board-touching targets:

| Target | File |
| --- | --- |
| `program` | `fpga_board.mk` |
| `tcl-*` | `fpga_flow.mk:262` |
| `run-*` | `fpga_flow.mk:269` |
| `seq-*` | `fpga_flow.mk:282` |
| `run` | `fpga_flow.mk:457` |

`seq-*` was not in the original acceptance list and was found by grepping for
every recipe that passes `--board`/`--baud`; it goes through the same runner.
`seq-list` is deliberately NOT locked -- it only lists sequences, and locking it
would block on a live run for nothing.

Verified: all 13 board-path Makefiles parse; the prefix appears in the expanded
recipe; with the lock held `make program` exits 98 with a hint naming the board
and key, and succeeds once free. The end-to-end test used `VIVADO=/bin/true` so a
wiring failure could not have reached hardware. board_lock.sh itself has 7
standalone checks including the one that matters -- `fuser` showing the *payload*
(not the script) holding the lock -- and non-zero payload exits passing through
rather than being masked as success.

### Still open

- **The device-ID readback.** `fpga_board.py` has subcommands
  `list / info / ports / serial / program` and **no way to read an ID back from
  the device**, so this needs new CLI capability rather than a make change. It is
  the complement to the lock, not a duplicate: a lock prevents collision, a
  readback detects one that happened anyway. It belongs in `fpga_board.mk`'s
  `program` path so all consumers inherit it rather than each harness
  reimplementing it.
- **A DIRECT script invocation bypasses the make lock -- PARTLY CLOSED.** The
  make lock guards `make program` and friends; a hand-launched runner takes no
  lock and is invisible to anyone else's check. The near miss itself was
  `run_characterization.py --byte-perf --port /dev/ttyUSB0`, launched that way.
  - **Closed for scoria (69ed1be27).** `DDR3CharDriver` opens a UART in its
    constructor, so it had the identical hole; it now takes the lock itself via
    `Genesys2/scoria/host/board_lock.py`. Only the HARDWARE path locks -- an
    injected bridge (cocotb channel or mock) holds nothing, because locking the
    sim path would exclude real board runs for no reason and teach people to
    route around the lock. Same reasoning as leaving `host-*` alone.
  - **Closed for rapids too (e2e185eb7).** `board_guard.py` wraps the lock and
    the identity readback, and is wired into `run_characterization.py`,
    `run_sink_once.py` and `dump_status.py`. It imports scoria's `board_lock.py`
    from its home rather than copying it, so there is still one key derivation
    and one exit code. Only the real-serial-port path uses it; the UART sim
    campaign injects its transport and never reaches it.
  - So the direct-invocation hole is closed for both board areas. What remains is
    below, and it is a defect in the lock itself rather than in its adoption.

- **PROVEN DEFECT: taking the lock inside a runner launched under make
  deadlocks against its own lock.** `board_lock.sh` execs the payload with fd 9
  still holding the flock; the payload then opens the same file and takes a
  SECOND flock on a different descriptor, which the kernel refuses. Demonstrated
  directly:

        board_lock.sh --board genesys2 -- python3 -c "with BoardLock('genesys2'): ..."
        -> BoardBusy

  - **rapids is protected, scoria is not.** rapids' `board_guard._inherited_fd()`
    walks `/proc/self/fd` for a descriptor on the lock path and tries to re-lock
    it -- which succeeds only if this process tree already owns the lock, so a
    descriptor merely open on the file does not count. `board_lock.py` itself has
    **no** inherited-fd handling, so `DDR3CharDriver` takes `BoardLock` in its
    constructor and will fail with 98 against itself the moment it is launched
    through a make target. It works today only because it is launched directly.
  - **The fix belongs in `BoardLock.__enter__`**, not in each wrapper -- promote
    rapids' detection into the shared module so every consumer inherits it. The
    same argument that put the readback in the `program` path rather than
    per-harness.
  - **The interop test does not cover this**, which is why it passed while the
    defect existed. A nested case (`board_lock.sh` wrapping a payload that takes
    the Python lock) belongs in
    `projects/fpga-systems/bin/test_board_lock_interop.py` alongside the fix.
  - A lock that refuses its own holder gets "fixed" by someone deleting the lock,
    which is why this is the live item rather than a footnote.

- **The readback exists for rapids only.** `board_guard.py` runs
  `jtag_readback.tcl` through vivado and compares the target serial to the
  registry at start and end. That is the right behaviour, but it lives in the
  rapids flow -- `fpga_board.py` still has no readback subcommand, so the other
  board consumers do not inherit it. Putting it in the `program` path remains
  unbuilt.
- **The two lock implementations are now PINNED by a CI test.** Two
  implementations of one key with nothing asserting they agree is worse than no
  lock -- both sides acquire and each believes it owns the board, with no error
  on either. `projects/fpga-systems/bin/test_board_lock_interop.py` (11 tests,
  in a directory CI already runs) asserts the derivations agree for five board
  names, that the busy exit code is 98 on both sides, mutual exclusion in both
  directions, release, and per-board independence.
  - Mutation-tested for teeth, and two of three mutations initially passed:
    changing the filename prefix was caught, but dropping `-` from the
    sanitisation class was not (no case exercised a hyphen -- both real serials
    are alphanumeric), and changing the lock-dir DEFAULT was not (every test sets
    `RDS_BOARD_LOCK_DIR` explicitly so it never touches the real lock). Both
    holes are closed; all three mutations now fail the suite.
  - The suite never takes the real board lock -- it redirects
    `RDS_BOARD_LOCK_DIR` at a `tmp_path`, and the default-directory test compares
    derivations without acquiring. A test that could stall a live
    characterization would be worse than the bug.
- **`host-*` is deliberately NOT locked.** `host-$(1)` runs
  `host_$(1).py $(ARGS)` with no `--board`/`--baud`, and those directories mix
  real board programs with pure post-processing (`host_perf_json_to_csv.py`). The
  makefile cannot tell them apart, and locking analysis scripts would block
  legitimate concurrent work -- which teaches people to route around the lock.
  Deciding this needs a per-program fact the flow does not have. Named here so it
  is a known gap rather than an oversight.

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
- `FPGA_JTAG_SERIAL` appears twice, both times to TARGET hardware, never as a
  lock key. Nothing in `fpga_flow.mk` is keyed on a board.

## Correction (2026-09-30, from scoria): `program` lives elsewhere and is worse

An earlier revision of this task said "there is no `program` target" -- true of
`fpga_flow.mk`, and misleading. **It is in `make/fpga_board.mk`**, which
`fpga_flow.mk` includes at :241. That is the target that flashed the Genesys 2
during the near miss.

    :58  program:   ## Flash BITSTREAM onto BOARD over JTAG (falls back to HOLD)
                    $(PYTHON) $(FPGA_BOARD_CLI) --board $(BOARD) program ...

**`grep -cE 'flock|LOCKED|\.lock|LOCK' make/fpga_board.mk` returns 0.** So
`program` is not merely missing a board-keyed lock -- it is outside EVERY lock in
the flow, the build-directory one included. Two hardware-touching paths, in two
different files, neither guarded.

**And the consumer set is wider than one file.** `fpga_board.mk` has THREE direct
consumers that never include `fpga_flow.mk`, so they never see even the
build-directory lock:

    projects/fpga-systems/Genesys2/rapids/flows-rapids/Makefile          <-- the near miss
    projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/Makefile
    projects/asic-trials/timing_characterization/fpga/Makefile

The rapids flow that was mid-characterization is one of them. **Acceptance
criteria written against `fpga_flow.mk` alone would leave the path that caused the
near miss untouched, and three board-touching areas outside the fix entirely.**

## Blast radius: 13 Makefiles. Re-derive it, do not inherit it

This figure has been measured three times and been **wrong twice** -- 17 (mine)
and 16 (scoria's), both of which counted MENTIONS rather than includes. It is
exactly the kind of number that gets copied into a plan unchecked, so the
commands are here:

    # mentions -- NOT the answer (16); six are comments saying the per-build
    # Makefile includes fpga_flow.mk, one of which was written the same morning
    grep -rl 'fpga_flow\.mk' --include='Makefile' projects/ | wc -l

    # actual includers
    grep -rlE '^[[:space:]]*(-?include)[[:space:]].*fpga_flow\.mk'  --include='Makefile' projects/   # 10
    grep -rlE '^[[:space:]]*(-?include)[[:space:]].*fpga_board\.mk' --include='Makefile' projects/   # 3

| Set | Count |
| --- | --- |
| include `fpga_flow.mk` | 10 |
| include `fpga_board.mk` directly | 3 |
| overlap | **0** |
| **distinct Makefiles on a board path** | **13** |

`Genesys2/stream/stream.mk` is a fragment, not a consumer: its three includers
(`build-mon`, `build-obs`, `build-perf`) are all already in the `fpga_flow.mk`
set, so it adds a path and no consumer. Verified independently rather than taken
from either previous count.

## The file already argues this, one step short of the conclusion

`fpga_board.mk` :52-54, immediately above `program:`:

> It says WHICH file it is programming, every time. Silently programming a
> different bitstream than the one you just built is a worse failure than
> refusing: it is how a board result gets attributed to the wrong design.

That is the same failure as concurrent reprogramming with a different cause, and
the file stops right before extending it. Whoever takes this is not introducing a
principle -- they are finishing one the tooling already makes.

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

- **The lock belongs in `make/fpga_board.mk`, not `fpga_flow.mk`.** That is the
  file every board-touching path reaches -- `program` is defined there, and three
  areas include it directly without `fpga_flow.mk`. A lock added to
  `fpga_flow.mk` would miss all of them.
- The board-touching paths -- `program` (`fpga_board.mk:58`), plus `tcl-*`,
  `run`, `run-*` in `fpga_flow.mk` -- take a lock keyed on the **board**: the
  JTAG serial from the board registry, or the tty. Not on the build directory.
- The build-directory lock STAYS for Vivado builds. It is right for its purpose
  and `build-mon` / `build-perf` concurrency is deliberate; this is an
  additional lock, not a replacement.
- The device ID is read back **from the device** at start and end and recorded
  beside the bitstream sha256, so a mid-run swap is detectable after the fact
  rather than invisible. A sha256 of what you programmed cannot detect a third
  party; a device ID read at both ends can. **Put it in `fpga_board.mk`'s
  `program` path rather than per-harness**, so every consumer inherits it
  (scoria's suggestion, and it is the right level). rapids is adopting the
  readback for their final run independently of the lock.
- All **13** board-path Makefiles verified unbroken -- the 10 that include
  `fpga_flow.mk` and the 3 that include `fpga_board.mk` directly. Re-derive that
  set with the greps above rather than trusting the number.

## Interim mitigation, in use now

Before programming a shared board, `fuser /dev/ttyUSB*` plus a `ps` for another
area's host script. `make ports` gives you the serial but says nothing about who
is holding it.

## Hazards

- This changes shared flow tooling on the board path of 13 Makefiles. Do it when
  no characterization is live.
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
