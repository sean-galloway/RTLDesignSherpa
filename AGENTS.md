# RTLDesignSherpa — standing agent instructions

This file is the front door for every coding agent that reads `AGENTS.md`:
Kimi Code, Qwen, Nemotron, or anything else. Claude Code comes in through
`CLAUDE.md`; you come in here. Both doors lead to the same place, the vault,
and the same rules apply to you as to Claude.

This file is a **signpost**. It states the non-negotiables and names the note
that holds each one. The method lives in the note, not here. If a rule below
and its note ever disagree, the note is right and this file is stale.

## Read first, every session

1. **`vault/handbook/INDEX.md`** is the single source of truth for every
   method in this repo: design rules (`design/`), verification (`dv/`), FPGA
   process (`fpga/`), documentation (`authoring/`), agent roles (`agents/`).
   Each rule is recorded with the failure that taught it. Read the area index
   for the work in front of you, then the notes it names.
2. **`/GLOBAL_REQUIREMENTS.md`** is the enforcement authority. It wins over
   everything else, including the handbook, on any conflict.
3. **`/CLAUDE.md` applies to you too.** It is named for one tool but it is the
   repo-wide guide: the generated-file regeneration rule (Rule #0), the
   generated-directory rule (Rule #0.1), testbench placement, and naming and
   reset conventions. Read it.
4. **Area files beside the code** hold area facts and traps: any
   `CLAUDE.md` or `AGENTS.md` under `rtl/<subsystem>/` or
   `projects/components/<name>/` (for example
   `projects/components/mem-ctrl-ip/AGENTS.md`). Read the ones on the path
   you are working in.
5. **Skills are readable by you.** `.claude/skills/<name>/SKILL.md` is plain
   Markdown, and `vault/handbook/skills.md` maps every skill to its canonical
   note. When a task matches a skill's description (writing a test, running a
   regression, adding RTL, drawing a diagram), read the note it names before
   starting.

## Where things go

- **A durable lesson goes into the handbook note it belongs to.** If no note
  fits, create one and add it to that area's `INDEX.md`. Never park a lesson
  in this file, a `CLAUDE.md`, a skill, or a README beside the code. A second
  copy is how documentation rots: the copy nobody edits is the one the next
  session reads. (`vault/handbook/authoring/doc-placement.md`)
- **Work items go in `vault/tracking/<area>/`**, never a `TASKS.md` or
  `TODO.md` next to code. Pick the lane (`task/` planned work, `bug/` a
  defect with expected and observed behaviour, `issue/` undiagnosed), take
  the ID from the lane's `INDEX.md` or `bin/check_task_ids.py --next <lane
  path>`, write one file per item, and change state with `git mv`. Cite an ID
  with its area ("pumice BUG-009"). `vault/tracking/INDEX.md` is the
  authority; the `tasks` skill still describes the retired flat pages.
- **Context about one area** (why this block is the way it is) goes in
  `vault/repo-wide-projects/<same path as the code>/INDEX.md`.

## Non-negotiables

Each of these has cost real work. The note named is where the reason lives.

- **Commit messages carry no attribution trailers.** No `Co-Authored-By:`,
  no `Assisted-by:`, no session links, no "generated with" line, for any
  model or harness. If your harness adds one by default, remove it.
  (`/GLOBAL_REQUIREMENTS.md` 6.1, `vault/handbook/authoring/commit-messages.md`)
- **The working tree is shared with other agents.** Work on `main` and never
  create a branch; commit with `git commit -F <msgfile> -- <paths>`, never a
  bare `git commit`; never `git commit --amend`; verify the staged set before
  committing. (`vault/handbook/agents/multi-agent-worktree.md`)
- **Before any test: `source env_python`, then
  `make clean-all && make run-all-{gate,func,full}-parallel`.** Never a bare
  `pytest`. A sub-second pass is a stale build, not a pass.
  (`vault/handbook/dv/running-regressions.md`)
- **Never hand-edit generated code.** Change the generator, delete all
  output, regenerate all. Register blocks go through
  `bin/peakrdl_generate.py`. (`/CLAUDE.md` Rule #0,
  `vault/handbook/design/generated-rtl-discipline.md`)
- **RTL:** no assertions in synthesizable RTL
  (`design/no-assertions-in-rtl.md`); every module has a `.f` filelist
  registered in `bin/filelists.toml` (`design/filelists.md`); reset macros
  per `/GLOBAL_REQUIREMENTS.md` 1.1; `r_` means flopped and `w_` means
  combinational (`design/signal-prefixes.md`).
- **DV:** use the RDS-DV BFMs, never a hand-rolled driver or monitor
  (`dv/bfm-usage.md`); test structure and levels per the `test-patterns`
  skill.
- **Docs:** no emoji anywhere. A voice or copy-edit pass never changes a code
  block, signal name, number or heading.
  (`vault/handbook/authoring/humanization-voice.md`)

## Roles

`vault/handbook/agents/INDEX.md` defines the repo's agent roles (RTL design,
RTL review, DV, regression triage, formal), each with a write scope and a
definition of done. When you are asked to take one of those roles, read its
note first. **A role that may write is never the role that judges that
write**, whichever model fills it.

## Block diagrams: house style is BINDING (highest priority for all doc/diagram work)

Every block / microarchitecture diagram in this repo — HAS/MAS books,
README figures, vault notes, fpga docs, anything — MUST follow the diagram
house style, fixed by the owner's reference (the classic DDR-MC course
diagram), and is drawn in graphviz `dot`. The canonical rules live in the
handbook:

`vault/handbook/authoring/block-diagrams.md`

The reference implementation is the family whole-unit diagram
(`common_has/assets/graphviz/01_whole_unit.png`) — mirror it.

Non-negotiables (rationale + recipes in the handbook note):

- **Three flows traceable at a glance**: command top-down the center;
  write data on its own route; read data back UP its own route (the
  spatial loop). Flows never share an arrow.
- **The scheduler is the flat wide-edge-up trapezium**
  (`shape=invtrapezium` — plain `trapezium` renders as an upside-down
  mux). Every arrow into it carries a transaction-class label (`WR / RMW`,
  `RD`, `REF / ZQ`, `timer window`); the command output leaves the narrow
  edge with a heavier pen (`penwidth=1.8`).
- **Every arrow labeled with what it carries.** Sideband/optional: dashed,
  short, labeled. Same-rank (horizontal) edge labels use `xlabel` — plain
  labels get overdrawn by node fills.
- **One boundary bar per diagram** (PHY at unit scale, layer edge at layer
  scale). No long same-rank edges. Never two parallel edges between one
  node pair for two classes (one edge, combined label). Never multiple
  mixed-direction crossings on one node pair — use the point-node scaffold
  pattern (handbook note).
- **Render, then READ THE RENDERED PNG AT FULL RESOLUTION and trace the
  three flows before committing.** Never commit an unseen diagram; if a
  flow cannot be traced with a finger, fix the ranks — not the colors.
