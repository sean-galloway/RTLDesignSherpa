# TASK-004: AXI5-Lite and APB5 as MASTER protocols

> Migrated 2026-09-27 from `vault/Tasks/bridge/closed.md` as **BRIDGE-014** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-11. Every protocol value the generator accepts on a
slave port is now legal on a master port: `axil`, `axil5`, `apb`, `apb5`
requesters, each with a fixture in the batch. Originally: open 2026-09-10
(filed at Sean's request when BRIDGE-002 closed). The second half of the
original entry, a native-AXI5 fabric, is split out as [[BRIDGE-018]] (open).
**Priority:** P3 at filing; done because it was the last open bridge item
with a defined scope.

**What existed.** An AXI4-Lite master branch: the top exposed only the Lite
signal set, tied the AXI4 extras (`AxLEN=0`, INCR, `WLAST=1`, placeholder ID)
into the ordinary `axi4_slave_*` wrapper, and took the wide-slave aligner
toward wider slaves. No fixture in the batch had a non-AXI4 master, so that
branch -- and the TB template's APB-master branch -- had never been generated
or simulated. The template called `APBMaster.read/write`, which did not exist
(only the APB5 subclass had them).

**What was built.**

- **`axil5` master.** The Lite promotion plus the whole AXI5-Lite sideband on
  the boundary from the one shared table (`axil5_sideband.py`), directions
  flipped for a requester. `exclusive` -> `awlock`/`arlock` and `user` -> the
  1-bit USER fields join the Lite surface and reach the adapter's AXI4 face;
  every other group is terminated at the top (inputs reduced into an
  `_unused_<master>_axil5_sb` wire, outputs driven `'0`).
  `validate_axil5_features` now covers masters ("no AXI4 destination").
- **`apb` / `apb5` master.** New converters: `apb_cmdrsp_to_axi4` (APB
  cmd/rsp -> one single-beat AXI4 transaction; AW and W each held to their
  own handshake; R drained to RLAST; SLVERR and DECERR fold to PSLVERR) and
  the wrappers `apb4_to_axi4` / `apb5_to_axi4` over `rtl/amba`'s
  `apb{4,5}_slave`. APB5 maps `PAUSER`/`PWUSER` onto AXI USER by size cast;
  `PWAKEUP` is an input (requester-driven) and terminated; parity off. The
  master adapter puts the converter on an internal `apbx_axi_*` face and
  feeds the same `axi4_slave_{wr,rd}` (or `_mon`) wrapper an AXI4 master
  gets, so decode, width adaptation, the aligner and the response mux are
  untouched. Converter tests: `test_apb{4,5}_to_axi4.py`, 12 cells FULL.
- **Validator.** Lite masters `id_width = 0`; APB masters `addr_width = 32`
  (the requester addresses the whole fabric; an APB slave port's PADDR is a
  window offset). The loader accepts `axi5_features` on `axil5` masters.
- **TB template.** `axil5` masters get `AXIL5Master{Read,Write}` with every
  sideband group enabled; `apb5` masters `APB5Master` at 1-bit USER widths;
  `master_read`/`master_write` unwrap the APB transaction and raise
  `AxiResponseError(resp=2)` on `PSLVERR`. RDS-DV: `APBMaster.write/read`
  added (the APB4 base class; APB5 overrides them).
- **Fixtures.** `bridge_2x2_lite_req` (AXI4-Lite + AXI5-Lite masters, 64b
  AXI4 + AXI5-Lite slaves) and `bridge_2x3_apb_req` (APB4 + APB5 masters,
  AXI4 + AXI5-Lite + APB4 slaves), both `no` and `mon`; 30 fixtures in the
  batch. Directed sign-off: `test_bridge_2x2_lite_req_sideband.py` (user/lock
  end to end and absent from the AXI4-Lite master's traffic; terminated
  groups at 0; both halves of a 64-bit row from both Lite masters; two
  ID-less masters in flight at one slave) and `test_bridge_2x3_apb_req_paths.py`
  (PSLVERR for unmapped with the port working after; PPROT at the AXI4
  slave; the APB5 USER bit at the AXI5-Lite slave and 0 from the APB4 master;
  APB in / APB out from both requesters interleaved).

**Known limit, pre-existing and documented.** Response-side USER
(`buser`/`ruser`, and so `PBUSER`/`PRUSER`) reads 0 at any master port: the
master adapters tie `fub_axi_{b,r}user` (PRD). The converters carry it; the
fabric does not.

**Docs.** Converters MAS ch03 `12_apb_to_axi4.md` (+ overview table, index);
bridge HAS (key features, protocol support master-boundary table, AMBA5
interfaces: AXI5-Lite and APB5 master surfaces, interop rows, APB requester
ports) and MAS (protocol conversion 2.7.2/2.7.15/2.7.16, AMBA5 boundary
section + anchors, test strategy rows); PRD; handbook
`generated-rtl-discipline.md` ("a protocol branch with no fixture in the
batch is dead code").

---
