# Bridge AXI3 Port Support — Design Spec

**Date:** 2026-10-11
**Status:** Design dialogue 2026-10-11 approved by user, pending written-spec review
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

## 7. Verification

Bridge cocotb suite (`dv/` under the bridge IP) extended with AXI3 configs,
driven by the RDS-DV AXI3 BFMs (`PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src`
locally; CI BFM availability flagged to the plan):

1. AXI3 master × AXI4 slave, same width.
2. AXI4 master × AXI3 slave, same width.
3. AXI3 master × AXI3 slave.
4. AXI3 mixed into an existing APB/AXIL config (protocol heterogeneity).
5. Width-mismatched AXI3 port (rides internal dwidth adaptation).

Gates on every generated config: `bin/check_sv_decl_order.py` +
`make verible`. Negative tests: validator rejects id_width=0, width outside
{32,64,128,256}, axi5_features-on-axi3, CDC-on-axi3.

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
| `dv/` (bridge) | AXI3 test configs + tests |
| `PRD.md`, `docs/bridge_has/`, `docs/bridge_mas/`, `references/README.md` | protocol rows, constraints, citation |
