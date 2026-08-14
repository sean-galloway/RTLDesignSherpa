---
title: Agent roles
summary: The five repo-resident agent roles, what each may touch, and the stub that makes it discoverable. Roles are scoped to this repo, never to the machine.
---

# Agent roles

Five roles, defined here and signposted from `.claude/agents/`. Same split as
[[skills]]: the **stub** is the discoverable file, the **note** is the method.

A role earns its own definition when it differs on one of four axes. Job title is
not one of them:

1. **Context loadout** - which handbook area it reads. A DV agent that loads the
   design area is paying for context it will not use.
2. **Write scope** - which paths it may modify, and whether it may modify anything.
3. **Definition of done** - the check that ends the task, not a feeling.
4. **Authorship** - whether it is allowed to have written the thing it is judging.

Axis 4 is the one that pays. A reviewer that reviews its own output confirms its
own assumptions; the finding it cannot see is the one it made.

## The roles

| Stub | Note | Loads | Writes | Done when |
|------|------|-------|--------|-----------|
| [rds-rtl-design](../../../.claude/agents/rds-rtl-design.md) | [[rtl-design]] | [[design/INDEX\|design]] | `rtl/**` | lint + decl-order + filelist clean |
| [rds-rtl-review](../../../.claude/agents/rds-rtl-review.md) | [[rtl-review]] | [[design/INDEX\|design]] | nothing | every finding triaged doc-fix vs RTL-fix |
| [rds-dv](../../../.claude/agents/rds-dv.md) | [[dv-author]] | [[dv/INDEX\|dv]] | `val/**` | test fails on broken RTL, passes on fixed |
| [rds-regress](../../../.claude/agents/rds-regress.md) | [[regress-triage]] | [[dv/INDEX\|dv]] | logs, quarantine | clean rebuild reproduces the verdict |
| [rds-formal](../../../.claude/agents/rds-formal.md) | [[formal-prove]] | [[formal]] | `formal/**` | proven, or cex explained in engineering terms |

## Why not an org chart

The obvious taxonomy - architect, micro-architect, designer, dv-lead, dv - copies
a human team. Human roles split on headcount, accountability and career ladder,
none of which an agent has. Two of those splits actively cost:

- **A lead that delegates is a hop that loses information.** Every summarization
  boundary drops detail, and a supervising agent adds one without doing work.
  Orchestration belongs to the session driving the roles, not to a role.
- **Architect vs micro-architect is a phase, not a role.** Deciding which blocks
  exist and deciding pipeline depth happen at different times with the same
  context. That is one planning pass, run before implementation.

## Naming

The stubs are prefixed `rds-` because **agent already means something here**: in
[[escape-analysis]] the round-robin arbiter starved "two of four agents" - bus
clients, not models. Unprefixed role names would make both the prose and every
future grep ambiguous.

## House rules for roles

- The stub carries only the non-negotiables - the rules that being wrong about
  is unrecoverable. Method lives in the note.
- A role that may write is never the role that judges that write.
- Never invent a project-local TODO file. Tasks go to `/vault/Tasks/<area>/`;
  this is the rule agents break most (see the [[skills]] row for `tasks`).
- Scope is per repo: these live in `<repo>/.claude/agents/`, never in
  `~/.claude/agents/`, which would apply them to unrelated work.

## Shared worktree

- [[multi-agent-worktree]] - several agents, one checkout: the four measured
  leak paths for uncommitted state (swept experiments, staged deletions
  riding foreign commits, rm-rf'd shared collateral roots, shared-file
  breakage) and the staged-SET check that actually holds.
