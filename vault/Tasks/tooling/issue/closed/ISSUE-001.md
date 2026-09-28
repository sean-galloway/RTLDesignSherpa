# ISSUE-001: Triage the 18 Dependabot vulnerabilities on the default branch

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-006** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Closed 2026-09-23 -- nothing to triage. The headline was stale.

Measured via `gh api /repos/sean-galloway/RTLDesignSherpa/dependabot/alerts
--paginate`: **74 alerts, all 74 in state `fixed`, zero open, zero by severity.**
All pip ecosystem, against `requirements.txt` (85 pins). Earliest fixed
2023-09-29, most recent 2026-09-16.

So the three checkboxes below have no subject: there is nothing to classify,
nothing safe-to-bump outstanding, and no accepted risk to record. The entry's own
closing note -- "check whether any are already fixed by the current pins before
doing work" -- was the right instinct and is the answer.

The push banner quoting "18 vulnerabilities (14 high, 4 moderate)" is what a
stale local view of an alert list looks like; the API is the authority.
**Owner:** TBD

Every push prints: *"GitHub found 18 vulnerabilities on
sean-galloway/RTLDesignSherpa's default branch (14 high, 4 moderate)."* It has
been printing that all session and is tracked nowhere, which is how a warning
becomes wallpaper.

- [ ] Read the Dependabot alerts and classify: real exposure vs transitive dev
      dependency that never runs on untrusted input.
- [ ] Bump what is safe to bump; `requirements.txt` is pinned, so each bump is
      a deliberate edit and needs a regression run behind it.
- [ ] Record anything deliberately not fixed, with the reason. An accepted risk
      that is written down is fine; an unread alert is not.

Note the alerts are against `main`, and the working branch has moved on — check
whether any are already fixed by the current pins before doing work.

---

---
