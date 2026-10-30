<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# The shared core contract (`l1_*`)

Everything in `rtl/` here is the protocol-stable MESI L1 core that amber
and jet both compile against. The rule (from the [README](../README.md)):
a consumer that modifies a block here inherits the obligation to re-run
the whole verification baseline — proofs and golden-model parity — not
assume it.

**Naming:** modules and files carry the neutral `l1_*` prefix. Package
constants and typedef names keep their `AMBER_*` heritage (e.g.
`AMBER_STATE_M`, `amber_repl_t`) — renaming those is a repo-wide sweep
and is its own task; treat the prefix as history, not ownership.

## Geometry and encodings (`rtl/includes/l1_pkg.sv`)

- Defaults: `AMBER_ADDR_WIDTH=32`, `AMBER_SETS=128`, `AMBER_WAYS=4`,
  `AMBER_LINE_BYTES=64`, `AMBER_BUS_WIDTH=64` (amber HAS Table 5.0);
  modules take these as parameter defaults, elaboration may override.
  Derived: `AMBER_FILL_BEATS = LINE_BYTES / (BUS_WIDTH/8)` (8 at
  defaults), tag/set/offset widths.
- MESI state on 3 bits (`AMBER_STATE_I/S/E/M` + reserved O); the legal
  {line state × snoop type} → {CRRESP, next state} decode (amber HAS
  Table 3.0) lives here as `amber_snoop_crresp()` /
  `amber_snoop_next_state()` — **the package is the single authority**;
  RTL, TBs, and the golden model all consume these functions.
- Policy enum: LRU / tree-PLRU / FIFO / RANDOM (`amber_repl_t`); LRU is
  the bound default.
- Fill classes, ACE snoop/ARSNOOP encodings, CRRESP bit positions
  (DT/ERR/PD/IS/WU), MonBus event codes.
- Elaboration-time range checks are a house idiom in the *modules*
  (`initial $error` blocks), not the package.

## The FUBs and their contracts

| Module | Responsibility | Key invariants | Lowest-level checkout |
|---|---|---|---|
| `l1_tag_array` | per-way {tag, state} store; 1 sync write port (one-hot way) + 2 combinational lookup ports (A=CPU/fill, B=snoop) | no reset port — validity is the init walk; read-around-write timing is contractual | `dv/tests/test_l1_tag_array.py` |
| `l1_data_array` | line store, LINE_BYTES split into FILL_BEATS beats; 2R+1W | combinational reads; single write port | `test_l1_data_array.py` |
| `l1_repl` | victim selection, per-set policy state | LRU/FIFO/RANDOM match cache_sim exactly (parity grid); PLRU self-checked | `test_l1_repl.py` |
| `l1_fill` | AXI4 read-master fill sequencing (single ID, `fub_axi_*` upstream of `axi4_master_rd`) | fill data returns in AR issue order; `fill_done` one cycle after RLAST; PassDirty latched from RRESP | `test_l1_fill_drain.py` |
| `l1_drain` | AXI4 write-master drain sequencing (upstream of `axi4_master_wr`) | consumes the victim-shaped head (`drain_start`/`victim_addr`/`victim_data`/`drain_done`); samples start only when idle | `test_l1_fill_drain.py` |
| `l1_victim` | depth-1 dirty-victim register | never loaded while valid (the load guard is the safety net) | `test_l1_victim.py` + `test_l1_control.py` (integration) |
| `l1_pending_fill_bypass` | pending-fill register: answers snoops at the post-fill state | never answers at the Invalid row; CD only for landed beats (PF_GUARD) | `test_l1_pending_fill_bypass.py` + `test_l1_control.py` (integration) |
| `l1_snoop_kmap` | combinational {state, snoop} → {CRRESP, next} decode leaf | implements the package functions' table literally | `test_l1_snoop_kmap.py` |
| `l1_snoop_resp` | ACE AC/CD/CR snoop responder (wraps the house snoop slave) | CR only after CDLAST; one closed response at a time; address held from the accept cycle | `test_l1_snoop_resp.py` |
| `l1_cpu_frontend` | GAXI slave: request latch + response staging FIFO | pulse-style `req_valid` (consumers that hold-until-accept need the D-6 skid); response staging room is the backpressure point | `test_l1_cpu_frontend.py` |
| `l1_monlite` | drop-and-count MonBus observer (128-bit packets) | never stalls the observed path; overflow counts drops | `test_l1_monlite.py` |
| `l1_control` | the blocking-pipeline control FSM (one transaction at a time: LOOKUP→…→REPLAY) | sticky CTRL_ERROR on illegal state; pend-effect semantics below | `test_l1_control.py` |
| `l1_core` (`rtl/top/`) | structural composition of all the above | memory side is the raw `fub_axi_*` pins (transports are a rig-top concern) | `test_l1_core.py` |

## Cross-cutting contracts

1. **Reset/init:** memories carry no reset; a hardware init walk writes
   `STATE_I` to all ways post-reset (formal assumes all-Invalid).
2. **Response staging (D-6):** the front end's response FIFO is the only
   response backpressure point; R-beat staging decouples fill return.
3. **Pending-fill semantics:** a snoop on a line being filled is answered
   at the *post-fill* reference state, PF_GUARD-gated; the deferred effect
   is applied after the install at commit. **Repeat-snoop resolution
   (BUG-004):** when an effect is armed, a further snoop's effect resolves
   its next state against the *armed* state (`effective = armed ?
   armed_state : post_fill`) — never against the bare post-fill reference
   (armed-S then ReadOnce must stay S; resolving against M would commit I
   and silently drop a merged store). The grant-cycle CRRESP still answers
   at the post-fill row.
4. **Victim/drain:** the dirty victim's address is held until BRESP; a
   snoop hitting the in-flight writeback is served from the victim
   register (SINK_WB_ACK), never "not present".
5. **Snoop port shape:** ACE AC/CD/CR per the family's
   [ACE definition](../../References/AMBA_ACE_Interface_Definition.md)
   (onyx D7); CR after CDLAST.

## Golden model, DV, formal

- Golden: [`../dv/golden/l1_fsm_oracle.py`](../dv/golden/l1_fsm_oracle.py) —
  the gem5-derived (`MESI_Two_Level-L1cache.sm`), timing-free per-line
  coherence model, with [`gem5_mapping_notes.md`](../dv/golden/gem5_mapping_notes.md)
  recording the divergence rulings; [`cache_sim_harness.py`](../dv/golden/cache_sim_harness.py)
  bridges the JS cache_sim policy golden ([`../dv/traces/`](../dv/traces/)
  corpus).
- DV: the unit grid above (`../dv/tests/`, `SEED=… REG_LEVEL=… python3 -m pytest`),
  oracle lockstep in `test_l1_control.py` / `test_l1_core.py`.
- Formal: `formal/amber/` covers the blocking control layer at the tiny
  16-set/2-way geometry (amber D9 scope); jet's own harness lives in
  `formal/jet/`.
