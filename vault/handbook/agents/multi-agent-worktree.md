---
title: Multi-agent shared worktree discipline
summary: One working tree, several agents - the seven ways uncommitted state crosses agent boundaries, and the staged-set check that actually holds.
---

# Multi-agent shared worktree discipline

Several agents share one checkout of this repo. Every incident below reached
either main or another agent's run before being caught. The common shape:
**uncommitted state is not private, and the index is shared.**

The incidents, each a different leak path:

1. **Your experiment rides someone else's commit.** A broken TBBase guard sat
   uncommitted; the math agent's `git add` swept it into da911640 and pushed
   it - live on main for twenty minutes under someone else's message
   (2026-08-08).
2. **Someone else's staged DELETIONS ride yours.** Another agent staged an
   apb4->apbx page move (2 adds + 2 deletes). A prefix-grep stowaway check
   caught the adds but not the deletes - deletions do not match the paths you
   grep FOR - and 058b3ae0 shipped the delete-half of their rename. Repaired
   in aa21bdb0 (2026-08-13).
3. **Shared collateral roots get rebuilt mid-round.** `build_review_bundle.py`
   is rm-rf-by-design; a second agent's rebuild deleted the first's hand-built
   `_meta` unit mid-humanize-round (2026-07-31). One bundle root per agent, or
   serialize.
4. **A shared-file edit breaks every consumer at once.** An uncommitted edit
   to `tbbase.py` doubled a decorator and broke all 118 TBs that call
   `convert_to_int` - and the victim spent the longest stretch assuming the
   failure was their own change (2026-08-06).
5. **Your STAGED set rides someone else's commit - including RTL.** A staged
   round-14 integration (an acceptance-fence RTL fix + TB scenario + 7 doc
   pages) was swept wholesale into the converters session's 426e2fb8, whose
   message describes none of it - a shared-RTL behavior change shipped under
   a test-work title. Same week, the reverse: a diagnostic probe rode that
   session's 40e5e116. Both directions of incident 1/2, now with staged (not
   just worktree) state. Provenance repaired with an empty commit carrying
   the intended message (1de8ad18, 2026-08-23). The fix is symmetrical:
   pathspec'd commits + the staged-SET check catch it on the committer's
   side; there is NO defense on the victim's side except committing fast.
6. **A peer's staged work fails YOUR pre-commit gate.** The inverse of 1/2/5:
   nothing of theirs contaminates your commit, but you cannot commit at all.
   The pumice session was mid-MOVE of two `.f` files into a registered
   directory (its TASK-032 part 1). While that move sat staged-but-uncommitted
   the files existed on disk outside any registered dir, so the RLB session's
   four unrelated commit attempts were blocked by the filelist ratchet with
   `unregistered_filelists 0 -> 2` - a blind spot belonging to neither the
   commit nor its author. It cleared the instant the owner committed
   (11281e91d) and the identical commit then landed unchanged (570f7f742,
   2026-09-28). The gate was RIGHT: the files genuinely were unregistered at
   that moment. Incident 4's lesson generalises - the victim again spent the
   longest stretch assuming the failure was their own.
7. **Their commit is validated by YOUR uncommitted tooling, and HEAD ends up
   failing its own gate.** The subtlest one, and the inverse of 6. A pre-commit
   hook runs the WORKING TREE's checker, not the committed one. On 2026-09-28
   an uncommitted change to `check_task_ids.py` (stop counting the reserved
   -000 templates) sat in the tree alongside 86 edited INDEX counts. The amba
   session then committed one of those INDEX files as a side effect of a
   pathspec commit -- their message is about formal proofs and says nothing
   about counting -- and it PASSED, because the hook used the uncommitted
   checker. For the minutes until the tooling change landed, HEAD paired the
   OLD checker with a NEW count (3 against 4 files on disk): a tree that fails
   the gate it ships. Nobody would have seen it except by checking out that
   commit alone.
   The lesson is not "commit tooling first" -- it is that a green hook proves
   the WORKTREE is consistent, never that HEAD is. When a tooling change and
   the data it governs must move together, they belong in ONE commit; when a
   peer's commit touches a file your uncommitted tooling governs, check what
   actually landed.

The rules:

- **Verify the staged SET, not staged paths.** Before every commit:
  `git diff --cached --name-status`, compare against your intended list BOTH
  ways - anything staged you did not list (adds, and especially deletions and
  renames) gets `git restore --staged` first. A prefix grep over
  `--name-only` misses deletions by construction.
- **The check must GATE, not report.** 2026-09-01: the reverse check ran, found
  two of another agent's renames, printed `UNEXPECTED` - and the commit went
  through and pushed, because it was written as
  `grep ... && echo UNEXPECTED || echo clean` with `git commit` as the NEXT
  statement. A guard that prints is decoration. Make it `exit 1`, or chain it
  with `&&` so a failure actually stops the commit. Two agents hit this same
  shape on the same day.
- **Adopting a rename is never safe, and check HEAD not the worktree.** Git's
  rename detection pairs a deletion with an addition already in the index and
  carries them into your commit. But a rename is usually a rename PLUS a code
  change, and detection can only ever carry the rename half - the half that
  makes the tree coherent is by definition not in the index. So the adopted
  commit is broken by construction.
  Worse, you cannot see it from your worktree: the owner's uncommitted fix is
  sitting right there, so a consistency grep over the working tree comes back
  clean. It did, and main was still unbuildable - 4 filelists referencing paths
  that no longer existed, plus 2 live instantiations. Check what you are about
  to ship, not what you can see:

      git show HEAD:<path>          # or: git stash list / git worktree
      git grep <symbol> HEAD        # the tree as it will land, not as it looks

  Recovery is fix-forward by the OWNER (they hold the other half), not a revert
  by the adopter.
- **Commit and push promptly.** Uncommitted work in this tree has a measured
  half-life. If it must stay uncommitted (another agent's in-flight restore,
  say), it is at risk every minute - flag it to the owner.
- **Never leave a broken experiment uncommitted while others work.** Mutation
  checks restore from a kept copy in the same breath (`cp` out, mutate, run,
  `cp` back) - never across a boundary where another agent might add/commit.
- **One collateral root per agent** for anything rebuilt wholesale (review
  bundles, generated trees), or explicit serialization.
- When a suite breaks unexpectedly, **check `git status` on shared
  infrastructure before debugging your own change** - incident 4's cost was
  mostly misattribution time.
- **A gate failure naming files you did not touch is a peer's in-flight work.**
  Wait for their commit, then retry unchanged. NEVER `--no-verify` (CI runs the
  same check and cannot be bypassed), never register their files, never raise
  the baseline - all three ship a real blind spot so that YOUR unrelated commit
  can pass. Two diagnostic traps cost an hour on incident 6, both worth knowing:
  the hook runs `filelist_registry.py --blindspots --ratchet`, while its own
  error text tells you to run plain `--blindspots`, which PASSES - the same
  second, opposite answers, which reads as a contradiction and is not one. And
  `--ratchet` reads `bin/blindspots_baseline.json`, whereas
  `bin/filelist_placement_baseline.json` is a DIFFERENT check's baseline, so
  diffing its bytes proves nothing about the ratchet. Read `.git/hooks/pre-commit`
  for the command it actually runs before theorising about why it disagrees with
  you. See [[filelists]].
- **A pathspec derived from `--name-only` drops the deletion half of a rename.**
  2026-09-30: 20 files were `git mv`d, then committed with
  `git commit -- $(git diff --cached --name-only)`. Rename detection prints ONE
  entry per rename -- the new name -- so the 20 deletions were never in the
  pathspec, and `git commit -- <paths>` takes everything outside the pathspec
  from HEAD. The tree that landed carried BOTH copies: two definitions of
  `char_engine_block`, `harness_csr` and the rest. The worktree was right the
  whole time, which is why every lint and gate in that commit passed -- they
  ran against the worktree, not the tree being written. Use `--no-renames` when
  deriving a pathspec from a staged set that contains moves.
- **Simulating a clean checkout without a `.git` makes ignore-aware gates lie.**
  2026-09-30: CI reported ONE broken filelist ref; reproducing with
  `git archive HEAD | tar -x` reported THREE, so CI was judged incomplete. It
  was not. `filelist_registry._git_ignored()` skips gitignored paths on purpose
  ("Reporting them as broken would make the gate permanently red for a
  condition no commit can fix"), and it implements that with `git check-ignore`
  -- which fails for every path in a tree with no `.git`. Nothing counted as
  ignored, so two legitimately-absent generated files surfaced as broken.
  Use a real clone or worktree at that commit, never an archive extraction, for
  anything whose answer depends on ignore rules.
  The tell was there and worth memorising: the same run also failed
  `nexys_ddr2_char`, an area the commit never touched. **Two areas failing
  where one commit landed is almost always the method, not the tree.**
- **The Vivado build lock does NOT protect the BOARD.** `make/fpga_flow.mk`
  locks per BUILD DIRECTORY -- deliberately, and correctly, so build-mon and
  build-perf can run at once while two of the same target cannot. But a
  physical board is contended by JTAG/UART SERIAL, not by build directory, so
  two areas targeting one board take two different locks and both proceed.
  It is worse than "program and run are unguarded", and the specifics matter
  because the two hardware-touching paths sit in DIFFERENT files:
  `program` lives in `make/fpga_board.mk` (included at fpga_flow.mk:241), and
  that file contains no lock of any kind; and `tcl-$(1)` at fpga_flow.mk:262
  -- the one rule written to pin FPGA_JTAG_SERIAL so "a tcl that touches
  hardware can pin its target instead of taking whatever is first on the
  chain" -- invokes `$(VIVADO_BATCH)`, not `$(VIVADO_LOCKED)`. So the two
  rules that exist to touch specific hardware are the two outside the lock,
  while VIVADO_LOCKED wraps only project/synth/build/ila (:418 :424 :432
  :441). FPGA_JTAG_SERIAL is resolved for targeting and never used as a lock
  key.
  And for three areas "wrong granularity" understates it -- there is no lock
  in the path at all. fpga_board.mk has THREE consumers that never include
  fpga_flow.mk: Genesys2/rapids/flows-rapids (the near miss itself),
  Genesys2/rapids_beats/flows-rapids-beats, and
  asic-trials/timing_characterization/fpga. So the flow that was mid-
  characterization was never partially protected; a lock added to
  fpga_flow.mk would miss those three AND the program path, i.e. it would miss
  the incident it was written for. The lock belongs in fpga_board.mk, the one
  file every board-touching path reaches -- as does the device-ID readback
  (a sha256 of what you programmed cannot detect a third party; a device ID
  read at start and end can).
  Consumer count, measured three times and wrong twice: 13 Makefiles, 10 via
  fpga_flow.mk and 3 via fpga_board.mk only. Earlier answers of 17 and 16 were
  MENTION counts -- `grep -l fpga_flow.mk` matches six area-dispatcher
  Makefiles whose only reference is a COMMENT saying the per-build Makefile
  includes it -- one of them written by the session that then quoted the
  number -- and Genesys2/stream/stream.mk is a fragment included by three
  Makefiles already counted, not a consumer. Grep for `include.*fpga_flow\.mk`,
  not for the filename: a blast-radius figure is the one number a fix's
  acceptance criteria will inherit unchecked.
  fpga_board.mk already argues the principle one level short of the
  conclusion: "Silently programming a different bitstream than the one you
  just built is a worse failure than refusing: it is how a board result gets
  attributed to the wrong design." Concurrent access is the same failure with
  a different cause, and the file stops before extending it there.
  Near miss, 2026-09-30: `Genesys2/scoria/build-litedram` programmed the
  Genesys 2 and held /dev/ttyUSB0 until 09:34:51; `Genesys2/rapids/flows-rapids`
  started an 8-channel byte-perf characterization on the SAME board at
  09:40:04. Five minutes apart, by luck, not by design.
  The failure it would have produced is the bad kind: the peer's harness
  records the sha256 of the bitstream IT programmed, so a third party
  reprogramming mid-run yields a results file that looks valid and is measuring
  someone else's design.
  RESOLVED by tooling TASK-022: `program`, `run-*`, `seq-*`, `tcl-*` and `run`
  take a board-keyed lock (board_lock.sh, keyed on the JTAG serial), and
  BoardLock does the same from Python for runners invoked directly. That lock
  is the only check worth relying on, because it keys on the BOARD rather than
  on either of its interfaces.
  The interim manual check first recorded here was HALF WRONG, and it is kept
  as a warning about the shape: `fuser /dev/ttyUSB*` finds UART users and
  cannot find JTAG users AT ALL. Measured -- the Genesys 2's JTAG serial
  200300B818A0 has no tty node whatsoever; only its separate FT232R UART
  (AU05X8RM) appears under /dev/ttyUSB*. So a `vivado -mode batch` driving the
  board returns nothing from fuser, and the check would have missed the
  PROGRAMMING half of the very near miss it was written for. A check that
  covers one interface of a two-interface device reads as a clean bill of
  health. A manual fallback needs `pgrep -af 'vivado|hw_server'` beside the
  fuser, and even then it races.
- **`git show --stat` elides leading paths; it is not evidence about a path.**
  2026-09-30: a peer read `.../rtl/verilator_xilinx_stubs.sv | 17 +++` from
  `--stat`, filled the `...` in from what the rest of the commit was about, and
  reported a file at a path that did not exist -- which cost the owner real
  effort to disprove. `--stat` truncates to fit a column. Use `--name-only` or
  `--name-status` for anything path-shaped; `--name-status` also distinguishes
  M from A, which was the other half of that error (a modification read as an
  addition).
