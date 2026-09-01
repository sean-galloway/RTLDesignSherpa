---
title: Multi-agent shared worktree discipline
summary: One working tree, several agents - the four ways uncommitted state crosses agent boundaries, and the staged-set check that actually holds.
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
