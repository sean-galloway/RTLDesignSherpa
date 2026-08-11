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

# AMBA5 Boundary and Native Sideband

How AXI5/APB5 ports ride the AXI4 fabric (BRIDGE-002 phases A5-1 through
A5-3). One spec table drives every generator:
`bin/bridge_pkg/sideband.py::SIDEBAND_FIELDS` maps each feature to its
per-channel struct fields, widths, and wrapper port bases — package,
adapter, crossbar, and slave-adapter emission all iterate it in the same
order, so struct layout and wiring cannot drift apart.

## Boundary Wrappers

- AXI5 **master** port → `axi5_slave_{wr,rd}[_mon]` at the master adapter
  (the bridge is a slave to the external master).
- AXI5 **slave** port → `axi5_master_{wr,rd}[_mon]` at the slave adapter.
- Both families carry every feature signal through their skid path,
  gated by `ENABLE_<FEATURE>` parameters; the generator binds every pin
  (enabled features connect through, the rest tie/open).

## Native Sideband Through the Structs (A5-2)

The per-bridge `_pkg` channel structs gain feature fields as the **union**
of features on any AXI5 port. Pure-AXI4 bridges emit no fields, so their
RTL stays byte-identical — the zero-drift invariant.

- **Master adapter:** packs its own enabled fields from the wrapper's
  `fub_axi_*` sideband on the **direct (width-matched) arm only**;
  converter arms pack `'0` — per-beat and per-transaction sideband cannot
  traverse the dwidth-converter IP. Because non-qualifying sources are
  guaranteed `'0`, the crossbar forwards request fields unconditionally.
- **Crossbar:** explodes struct fields into discrete
  `<slave>_axi_<sig>` nets for feature-enabled AXI5 slaves; response
  fields (`b.trace`, `r.trace`, `r.poison`) mux from qualifying slaves
  and default `'0` (they must be driven for every master since union
  fields exist in every struct).
- **Slave adapter:** rides `xbar_<slave>_axi_<sig>` nets into the
  wrapper via the component's `native_sideband` flag, which stops
  terminating enabled features' fub ports (fall-through to the
  connector prefix).

The struct field for AWUNIQUE/ARUNIQUE is named `uniq` (`unique` is an SV
keyword).

## Connectivity Gating (poison, atomic)

`AXI5_CONNECTIVITY_GATED_FEATURES` in the validator: these features are
legal only when **every** connected path is AXI5-both-ends,
feature-enabled, and width-matched — otherwise a config error naming the
offending pair. Droppable sideband that terminates mid-path is legal but
prints a generation-time warning per (master, slave, feature).

## Atomic Filter (A5-3a)

An atomic-enabled master's wr path inserts `axi5_atomic_filter`
between the boundary wrapper and the fabric:

```
axi5_slave_wr ── pref_axi_* ── axi5_atomic_filter ── fub_axi_* ── width paths / structs
                 (payload pass-through assigns around the filter)
```

Handshakes (AW/W/B) and the B payload (`bid`/`bresp`) go **through** the
filter; all other payload gets `pref → fub` pass-through assigns. Store-
class ATOP and plain writes forward; read-return classes are swallowed
(W burst consumed) and answered with a local DECERR B. See the module doc:
`docs/markdown/rtl-amba/axi5/axi5_atomic_filter.md`. Read-return atomics
proper (A5-3b) need a per-ID tracker shared across a port's split wr/rd
paths and are deferred until a consumer exists.

## APB5 Slaves (A5-3c)

`protocol = "apb5"` reuses the entire APB4 path with two deltas: the
slave adapter instantiates `axi4_to_apb5_shim` (a sideband wrapper over
the APB4 shim — see the converters MAS), and the external surface adds
`PAUSER/PWUSER` out (driven `'0`) and `PWAKEUP/PRUSER/PBUSER` in
(terminated). The generated TB drives the port with the APB4 BFM: APB5
keeps the APB4 transfer protocol.

## Verification Anchors

- Generator unit tests: `bin/tests/test_generator_pkg.py` (feature
  gating, poison/atomic connectivity rules, generation smoke).
- Sideband **values** end-to-end:
  `dv/tests/test_bridge_1x2_{rd,wr}_axi5n_sideband.py`.
- Atomics: `dv/tests/test_bridge_1x2_wr_axi5a_atomics.py` and
  `val/amba/test_axi5_atomic_filter.py`.
- AXI5 compliance at the boundary:
  `dv/tests/test_bridge_1x2_rd_axi5_bfm5.py` (AXI5 BFM +
  AXI5ComplianceChecker, zero violations).
