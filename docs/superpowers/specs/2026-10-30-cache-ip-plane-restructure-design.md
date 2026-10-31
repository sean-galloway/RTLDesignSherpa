# cache-ip plane restructure (amber/jet TASK-002) — design

**Date:** 2026-10-30
**Status:** approved in chat (scope + both sub-decisions), pending written-spec review
**Tasks:** `vault/tracking/projects/components/cache-ip/amber-mesi-l1/task/open/TASK-002.md`,
`vault/tracking/projects/components/cache-ip/jet-mesi-l1/task/open/TASK-002.md`

## Intent

Restructure the amber and jet RTL into **planes** per the mem-ctrl doctrine
(`mem-ctrl-ip/common-ip/docs/common_has/ch03_dfi_generations/01_dfi_planes.md`):
one named block per protocol generation — the protocol generation is a family
boundary, not a parameter — with revision-independent logic extracted once as
shared FUBs underneath. The goal is a **fabric plane seam** clean enough that a
future CHI plane can replace the ACE plane without touching the coherence core.

Owner rulings (2026-10-30):

- **Full three-plane split.** CPU plane, coherence core plane, and fabric plane
  are separate modules everywhere; `l1_snoop_resp` and the CPU frontend move
  OUT of the cores. (Chosen over the fabric-plane-only minimal cut.)
- **`l1_core` stays as the aggregate** (CPU plane + coherence core plane) so
  `test_l1_core`, its formal harness, and the existing docs keep a stable
  target. Tops compose planes directly, not `l1_core`.
- **CHI swap demonstration is a black-box stub** — a seam-faithful module with
  the full core-facing contract and a CHI channel pin skeleton, tied off,
  proven by elaboration. No dependency on the WIP `rtl/amba/chi/` blocks.

Non-negotiable: **zero functional change.** Full amber + jet + common-ip DV and
the formal harnesses re-run green; filelist registry and link ratchets clean.

## Current state (as found)

- **amber**: `l1_core` (common-ip) fuses `l1_cpu_frontend` + `l1_control` (+the
  `l1_victim`/`l1_pending_fill_bypass` leaves) + arrays + `l1_repl` +
  `l1_fill`/`l1_drain` + `l1_snoop_resp` + `l1_monlite`. The tops add the
  fabric: `amber_top` (pair rig) wraps it with plain `axi4_master_rd/wr_monlite`
  and exports the `coh_req` launch sideband; `amber_ace_top` (onyx rig) wraps it
  with `axi4ace_master_rd/wr_monlite` + `amber_ace_issue` and consumes `coh_req`
  internally. Both tops already carry the ACE snoop channels (AC in, CR/CD out)
  because the responder lives inside `l1_core`.
- **jet**: no `jet_core` exists — `jet_top` (1660 lines) composes everything at
  top level: `l1_cpu_frontend`, `jet_control`, `jet_mshr`, `jet_wb_buffer`,
  `jet_rsp_seq`, arrays, `l1_repl`, `l1_fill`/`l1_drain`, `l1_snoop_resp`,
  `l1_monlite`, `jet_monlite`, the plain transports, and the MonBus merge.
  `jet_ace_top` is the same composition with ACE transports + `jet_ace_issue`.
- `amber_ace_issue` / `jet_ace_issue` are structural mirrors (~73 diff lines,
  almost all comments and names; jet v1 never emits EVICT/MAKE_UNIQUE so its
  AW-only generator is present but unexercised).
- The seams are already clean named bundles:
  - CPU seam: `fe_req_valid/addr/we/be/wdata` + `ctrl_req_ready` (in),
    `ctrl_rsp_valid/data` (out).
  - Fabric (snoop) seam: `ctrl_snoop_req/ready/safe/type/addr`,
    `ctrl_crresp`, `ctrl_cddata/cdlast/cdvalid/cdready`.
  - Engine seam: `fub_axi_*` fill (AR/R) and drain (AW/W/B) pins + launch
    class + `coh_req` event pulses.
  - jet extra: `sn_want` (AC-pending throttle) — computed from AC pin
    handshakes, consumed by `jet_control`'s J6 throttle.

## The planes

### CPU plane

- `l1_cpu_plane` (common-ip): `l1_cpu_frontend`, alone. Ports = GAXI
  `cpu_req_wr_*`/`cpu_rsp_rd_*` outside; the CPU seam inside.
- `jet_cpu_plane` (jet-mesi-l1): `l1_cpu_frontend` + `jet_rsp_seq`, with
  `jet_rsp_seq`'s wiring to the control seam preserved exactly as in
  today's `jet_top`.

### Coherence core plane

- `l1_coh_core` (common-ip): `l1_control` (+leaves), `l1_tag_array`,
  `l1_data_array`, `l1_repl`, `l1_fill`, `l1_drain`, `l1_monlite`.
  Ports: CPU seam, fabric (snoop) seam, engine seam, `init_busy`,
  `ctrl_state`, the MonBus tap pair.
- `jet_coh_core` (jet-mesi-l1): `jet_control`, `jet_mshr`, `jet_wb_buffer`,
  the shared arrays/repl/fill/drain, `l1_monlite` + `jet_monlite`.
  Ports: the same seams plus jet's MSHR/WB snoop-bypass signals and the
  `sn_want` throttle input.

### Fabric planes (common-ip)

One named module per protocol generation; each instantiates the shared FUB
`l1_snoop_resp` (moved out of the cores) for the AC/CD/CR boundary:

- `l1_axi4_plane` — pair-rig flavor: `axi4_master_rd_monlite` /
  `axi4_master_wr_monlite`, `coh_req_*` exported as pins for the pair fabric,
  snoop channels straight to the top pins.
- `l1_ace_plane` — onyx-rig flavor: `axi4ace_master_rd/wr_monlite` (auto
  RACK/WACK) + `l1_ace_issue` (the merged amber/jet block — one shared FUB;
  jet's unused AW-only path stays, documented) and `coh_req_*` consumed
  internally as issue events.
- jet's `sn_want` AC-pending counter moves into both planes (it samples AC
  pin handshakes — fabric-side knowledge), exported as one seam bit.

### Tops (thin plane selections)

- `amber_top` = `l1_cpu_plane` + `l1_coh_core` + `l1_axi4_plane` + MonBus
  merge (D-7 arbiter stays a top-level observation concern).
- `amber_ace_top` = `l1_cpu_plane` + `l1_coh_core` + `l1_ace_plane` + merge.
- `jet_top` / `jet_ace_top` = the same shape with `jet_cpu_plane` /
  `jet_coh_core`.
- `amber_pair_fabric` / `jet_pair_fabric` are rig-level compositions, not
  planes: unchanged.
- `l1_core` remains as the CPU+coh aggregate module (now internally
  `l1_cpu_plane` + `l1_coh_core`) for the existing core DV/formal targets.

### The seam contract document

`common-ip/docs/l1_fabric_contract.md` — the core-facing fabric contract a
CHI plane implements, written once for both IPs:

- snoop in: `ctrl_snoop_req/addr/type` → `ready`/`safe` back;
- snoop out: `ctrl_crresp`, `ctrl_cd*` (data beats to the fabric);
- engine out: `fub_axi_*` fill/drain bursts + launch class + `coh_req`
  events (axi4 plane: exported; ace plane: consumed);
- feedback: `sn_want` (fabric → core throttle), one bit;
- rules: one outstanding coherence transaction class per direction (v1),
  response ordering, the launch-event mux discipline (fill launch wins the
  slot, WRITE_BACK replays — today's jet_top logic, moving into the planes
  verbatim).

### CHI swap demonstration

`l1_chi_plane_stub.sv` (common-ip): the full core-facing seam port list on
one side, a CHI channel pin skeleton (RXREQ/RXSNP/TXREQ/TXRSP/TXDAT/RXDAT
group names, tied off) on the other. A lint/elab-only filelist +
`filelist_registry` entry proves elaboration; a short section in the
contract doc records what a real CHI plane would add (CHI snoop semantics
differ from ACE — the seam is the contract, not the pinout).

## DV / formal impact

- Hierarchy taps that name `u_frontend` / `u_snoop` inside `l1_core` or the
  jet tops shift one level (`u_cpu.u_frontend`, plane paths). Affected:
  `test_l1_core` harness, jet core/pair-rig TBs, any formal harness binds.
  The plan phase inventories every tap before the move.
- `test_l1_cpu_frontend` / `test_l1_control` harnesses compose FUBs directly
  — unaffected.
- New unit smoke tests: none required by doctrine (the planes are pure
  re-composition of already-tested FUBs); each plane gets a filelist +
  registry entry, and the tops' existing suites are the regression proof.
- `l1_core`'s ACE snoop pins move to the fabric planes; `test_l1_core`'s
  snoop stimulus retargets to the fabric seam bundle (or the snoop portion
  moves to a plane-level test — decided in the plan).

## Forward reservations (RV32A, jet J8–J10 ruled 2026-10-30)

Zero functional change still holds — no op field or sideband is built in
this task. But the seams this task freezes are where jet's RV32A rows land
later, so the restructure must not paint them into a corner:

- **J8 (AMO cache-side ALU):** the CPU-plane request payload will gain an
  op field (LD / ST / nine word AMOs). The seam contract doc
  (`l1_fabric_contract.md` and the CPU-plane port list in the plan) records
  the field as reserved; the packed `cpu_req_wr_data` layout keeps MSB room
  for it.
- **J9 (LR/SC sideband):** the CPU plane will export a one-line
  "snoop service touched line X" notice toward the core. The seam doc
  records the notice as reserved; nothing is wired in this task.
- **J10 (aq/rl):** ruled no-cache-hardware; noted here only so the seam
  review doesn't reopen it.

## Done when (per the task files)

- amber and jet RTL compile as `<cpu plane>` + `<coh core>` + fabric plane,
  tops reduced to thin selections.
- `l1_fabric_contract.md` written (the CHI seam).
- Full amber + jet + common-ip DV and the formal harnesses re-run green with
  zero functional change; `filelist_registry` + link ratchets clean.
- `l1_chi_plane_stub` elaborates.

## Risks

- `jet_top`/`jet_ace_top` are ~1700 lines each of composition; the
  `jet_coh_core` extraction is mechanical but voluminous — done by
  move-don't-edit, with the existing jet core/pair-rig suites as the net.
- Hierarchy-path taps in TBs/formal are the expected breakage class; the
  inventory-then-move order keeps it mechanical.
- The `l1_ace_issue` merge must preserve amber's exercised AW-only path and
  jet's documented-not-exercised one — one parameterized block, identity
  proven by both ace_top suites.
