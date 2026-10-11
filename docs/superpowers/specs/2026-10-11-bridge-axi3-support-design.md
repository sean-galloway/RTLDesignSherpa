# Bridge AXI3 Port Support — Design Spec

**Date:** 2026-10-11
**Status:** Design dialogue 2026-10-11 approved by user (with batch-suite validation amendment), spec reviewed
**IP:** `projects/components/fabric-gen-ip/bridge/` (AXI4 full crossbar generator)
**Dependencies:** AXI3 converter suite (`projects/components/utility-ip/converters/rtl`, spec `2026-10-10-axi3-converters-design.md`); RDS-DV AXI3 BFMs (`RTLDesignSherpa-DV#87`)
**Tracking:** GitHub `sean-galloway/RTLDesignSherpa#97`

## 1. Goal

Let the bridge generator accept `protocol = "axi3"` on master (ingress) and
slave (egress) ports. AXI3 exists only on the external pins; proven
`axi3_to_axi4` / `axi4_to_axi3` converters translate to the internal AXI4
`fub_axi_*` world at the boundary. The verified crossbar core — arbiters,
W-destination FIFOs, CAM response routing, width adaptation — is untouched.

Deliverables: validator + generator changes, conditional filelist includes,
extended cocotb DV, lint-clean generated SV for AXI3 configs, PRD/HAS/MAS
protocol rows, references-store citation.

## 2. Why

DE10-Standard campaign: the Cyclone V HPS FPGA-facing ports are AXI3 hard
silicon, and Intel collateral in the fabric-comparison leg speaks AXI3. The
Intel leg gets AXI4↔AXI3 adaptation from Platform Designer; the Bridge leg
needs its own. Boundary converters — the same price-of-entry pattern as the
converter suite itself. General value: any AXI3 master or slave endpoint can
now attach to a generated bridge without hand-built shims.

## 3. Decisions (locked in design dialogue 2026-10-11)

1. **Architecture: boundary conversion, AXI4 core untouched.** Rejected
   alternatives: native AXI3 threaded through all generator templates (forks
   the datapath, doubles validation, discards the converter suite); documented
   external shim (not support — configs/filelists/TVs can't express it).
2. **Config surface.** `config_validator.py:71` `valid_protocols` gains
   `'axi3'` for masters and slaves. `protocol = "axi3"` composes with the
   existing per-port knobs (widths, priorities, pipeline stages).
3. **Master side (ingress).** `adapter_generator.py` treats `axi3` as a
   front-end protocol like `apb`/`wb4`: emits the AXI3 signal set (4-bit
   AW/ARLEN, `WID`, 2-bit `LOCK`, no QoS/REGION) and instantiates
   `axi3_to_axi4` between the external port and the existing AXI4 slave
   timing wrapper. Internal `fub_axi_*` stays AXI4 (8-bit LEN, no WID).
4. **Slave side (egress).** `slave_adapter_generator.py` mirrors: the
   crossbar-facing `axi4_master_*` wrapper drives `axi4_to_axi3`, then the
   external AXI3 slave port. Bridge-ID tracking pops on the crossbar-side
   AXI4 handshake, identical to the APB/AXIL paths.
5. **Widths.** Converters are same-width only, so they sit at the port's own
   width; mismatches against the fabric ride the bridge's existing
   `axi4_dwidth_converter_*` on the internal AXI4 side. Mismatched AXI3 ports
   compose for free — no new width logic, no same-width restriction.
6. **Filelists.** `bridge_generator.py` adds
   `-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4.f`
   when any master is AXI3 and
   `-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_axi3.f`
   when any slave is AXI3 — using the fixed `$REPO_ROOT` pattern from the
   bridge generate scripts (not the still-broken generic variant, tooling
   TASK-030).
7. **No new error paths.** DECERR/SLVERR flow exactly as today. The only
   additions are config-time validation errors (section 5).

## 4. Boundary semantics

- **WID:** present on the external master-side port, stripped by the
  converter; the bridge never uses it. **Constraint (inherited from the
  converter contract): an AXI3 master must not interleave W data across IDs —
  one ID until WLAST, then the next.** Assertion-checked in the converter;
  documented in the HAS as a master-side obligation. The known customer
  (Cyclone V `h2f_axi_master`) does not interleave.
- **LOCK:** 2-bit external. Mapping is the converter's documented one
  (`00`→normal, `10`→exclusive, `01`→locked→normal + note). The bridge
  generates no locked or exclusive transfers itself.
- **QoS/REGION:** absent on AXI3 pins; not configurable.
- **Burst length:** AXI3 masters present ≤16-beat bursts (4-bit LEN),
  upgraded trivially. On egress, bridge masters presenting >16-beat bursts
  are chopped by `axi4_to_axi3`'s address regeneration (INCR/FIXED; WRAP
  deferred per the converter spec) — transparent to the bridge.
- **Ordering/response merge:** converter-internal, already DV'd (168 tests
  at converter landing + bridge suite after).

## 5. Validation rules (config time, `config_validator.py`)

- `id_width > 0` required for AXI3 masters (same check AXI4 masters get).
- Port data width must be in the converter-supported set {32, 64, 128, 256}.
- `axi5_features` on an AXI3 port is rejected (extends the existing
  non-AXI5 rejection at `config_loader.py:205`).
- CDC enabled on an AXI3 port is rejected in v1.

## 6. Non-goals (v1)

Native AXI3 structs; AXI3↔AXI3 passthrough optimization; locked/exclusive
generation; CDC on AXI3 ports; write-interleave acceptance at the boundary;
any change to the converter RTL itself.

## 7. Verification — bridge batch suite

The bridge validation flow is batch-driven: `bin/bridge_batch.csv` lists
`(name, toml, connectivity.csv, output_dir, output_tb, output_test)`; each
TOML under `bin/test_configs/` defines the masters/slaves (per-port
`protocol`, widths, channels, address ranges) with a same-named
`*_connectivity.csv` master×slave matrix, and the batch tool generates the
RTL (`rtl/generated/`), TB classes (`dv/tbclasses/`), and test suite
(`dv/tests/`). AXI3 validation enters this flow as new batch entries — the
same pattern the AXI5 family used (`bridge_2x2_axi5` and siblings).

Four new bridges, per user direction, AMBA3 on both masters and slaves
across the set:

1. **`bridge_1x2_axi3`** — 1 AXI3 master (rw) → 1 AXI3 slave + 1 AXI4
   slave, same width. Smoke build; AXI3→AXI3 end-to-end through the
   crossbar plus the AXI3-master/AXI4-slave composition in one fixture.
2. **`bridge_2x2_axi3_masters`** — 2 AXI3 masters (one width-mismatched to
   the 64-bit fabric, e.g. 32-bit port) → 2 AXI4 slaves. Ingress focus;
   exercises internal width adaptation behind the converter and AXI3
   arbitration through the crossbar.
3. **`bridge_2x2_axi3_slaves`** — AXI4 master + AXI-Lite master → 2 AXI3
   slaves. Egress focus; the AXIL→AXI3 path crosses two protocol
   boundaries in one hop.
4. **`bridge_mix_e`** — extends the hetero family (`bridge_mix_a`-`d`):
   AXI3 + AXI4 + APB masters × AXI3 + AXI4 + APB slaves, with contention
   between converter-fronted and native ports under one arbiter.

Each entry gets: TOML + connectivity CSV under `bin/test_configs/`, a batch
row in `bin/bridge_batch.csv`, generated RTL passing
`bin/check_sv_decl_order.py` + `make verible`, and a generated cocotb test
driven by the RDS-DV AXI3 BFMs (`PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src`
locally; CI BFM availability flagged to the plan). Test content follows
the generated-suite conventions the batch tool already emits for AXI5/APB
front ends; no hand-written AXI3-only test is required for v1 beyond what
the generator produces.

Negative validation tests (new `test_configs/test_illegal_*.toml`, same
pattern as `test_illegal_apb_wr.toml`): validator rejects AXI3 master with
`id_width = 0`, AXI3 port width outside {32,64,128,256},
`axi5_features` on an AXI3 port, CDC enabled on an AXI3 port.

## 8. Docs

- `PRD.md` + bridge HAS/MAS gain `axi3` protocol rows; revision bumps happen
  at build time through the generate scripts, never by hand.
- `bridge/references/README.md` gains the AXI3 protocol authority next to the
  existing ARM IHI 0022E entry (AMBA AXI3, ARM IHI 0022 family).
- Converter-sourced constraints (no W interleaving, WRAP chop deferral,
  lock mapping) are restated in the HAS integration chapter by reference,
  not copied.

## 9. Files touched

| File | Change |
| --- | --- |
| `bin/bridge_pkg/config_validator.py` | `axi3` in `valid_protocols`; AXI3 validation rules |
| `bin/bridge_pkg/config_loader.py` | extend `axi5_features` rejection to AXI3 |
| `bin/bridge_pkg/components/bridge_module_generator.py` | AXI3 port emission (master + slave branches) |
| `bin/bridge_pkg/generators/adapter_generator.py` | AXI3 front end + `axi3_to_axi4` instance |
| `bin/bridge_pkg/generators/slave_adapter_generator.py` | AXI3 converter path |
| `bin/bridge_generator.py` | conditional converter filelist includes |
| `bin/bridge_batch.csv` | 4 new AXI3 bridge rows |
| `bin/test_configs/bridge_1x2_axi3.{toml,csv}` | smoke: AXI3 master × (AXI3 + AXI4) slaves |
| `bin/test_configs/bridge_2x2_axi3_masters.{toml,csv}` | ingress: 2 AXI3 masters, one width-mismatched |
| `bin/test_configs/bridge_2x2_axi3_slaves.{toml,csv}` | egress: AXI4+AXIL masters × 2 AXI3 slaves |
| `bin/test_configs/bridge_mix_e.{toml,csv}` | hetero: AXI3+AXI4+APB × AXI3+AXI4+APB |
| `bin/test_configs/test_illegal_axi3_*.toml` | negative validation fixtures |
| `dv/` (bridge, generated) | AXI3 TB classes + tests via the batch tool |
| `PRD.md`, `docs/bridge_has/`, `docs/bridge_mas/`, `references/README.md` | protocol rows, constraints, citation |

