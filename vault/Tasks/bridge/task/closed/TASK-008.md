# TASK-008: Wishbone B4 as a bridge protocol, both sides

> Migrated 2026-09-27 from `vault/Tasks/bridge/closed.md` as **BRIDGE-019** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-11, same day. `protocol = "wb4"` is legal on
slave ports (the bridge is the Wishbone requester) and master ports (the
bridge is the completer), B4 pipelined, with a fixture in the batch and a
directed sign-off. Originally: open 2026-09-11 (Sean: "can you add wb4 to
the mix? This is new design").
**Priority:** P2.

**Converters (new).** `axi4_to_wb4` = `axi4_to_axil4_{wr,rd}` + `axil4_to_wb4`
(one Wishbone transfer per AXI4 beat, in order; ACK -> OKAY, ERR -> SLVERR,
RTY -> RTY_RESP) and `wb4_to_axi4` = `wb4_to_axil4` + the single-beat AXI4
promotion (constant ID, AxLEN 0, full-width AxSIZE, INCR, WLAST 1; SLVERR
and DECERR terminate ERR; RTY never generated). Own closure filelists. Tests
`test_axi4_to_wb4.py` (bursts of 1..16 beats become exactly N transfers in
address order, WSTRB -> SEL against a byte shadow, ERR/RTY windows fold to
SLVERR with the port working after, fixed/stalling/slow completer profiles,
pipelined and classic) and `test_wb4_to_axi4.py` (single-beat shape at every
handshake, SEL -> WSTRB, round trip, out-of-range SLVERR -> ERR, slow
completer, both modes): 12 cells FULL.

**Generator.** `bridge_pkg/wb4_signals.py` is the one table (thirteen
signals, who drives them) the bridge top, both adapters and the instance
component read. Slave adapter: `_generate_wb4_converter` through the new
`Axi4ToWb4Shim` component (a subclass of the APB shim component: same
channel wiring, BRIDGE-011 not-full gate, `converter_*` intercepts, the
`axi4_master_*_mon` sandwich in the monitored variant). Master adapter: the
BRIDGE-014 front-end path generalised (`FRONT_END_MODULES`, `wbx_axi_*`
face), `wb4_to_axi4` in front of the ordinary timing wrapper, the wide-slave
aligner toward wider slaves. Validator: rw only, 8/16/32/64-bit, id_width 0,
master addr_width 32. Filelists pull the converters' closures.

**DV.** RDS-DV: `WB4Slave` gained `base_addr` and the shared out-of-range
contract (a bounds miss used to raise inside the sampling loop and kill the
BFM; now ERR, nothing written, the OOR pattern) and joined the structural
unit test; `WB4Master.write/read` helpers. TB template: `WB4Slave` per
completer port (window-relative memory, ACK-only fixed profile,
`set_slave_response_delay` swaps the termination latency), `WB4Master` per
requester port, `master_read/master_write` turn ERR/RTY into
`AxiResponseError(resp=2)`. The shared `bridge_arbitration` helper learned
`master_wb` (it discovered masters by container name, saw one, skipped both
phases -- and its zero-work guard is what failed the test instead of passing
it).

**Fixture.** `bridge_2x2_wb4`: a Wishbone requester and an AXI4 requester,
a 64-bit AXI4 memory and a 32-bit Wishbone completer, `no` and `mon`; 31
fixtures in the batch, 47 variants lint clean. Directed
`test_bridge_2x2_wb4_paths.py`: error folding both ways with recovery
(unmapped from the Wishbone requester -> ERR; the AXI4 requester past the
Wishbone completer's memory -> SLVERR), SEL lanes at the Wishbone completer
and in the 64-bit memory through the aligner, AXI4 bursts of 2..8 beats
becoming exactly one transfer per beat in order with the read burst
returning the memory, and both requesters in flight at the Wishbone
completer with a slowed termination. Bridge FULL regression 330/330.

**Not built, by decision.** Classic (B4 standard) mode from the TOML -- the
converters have the parameter, nothing selects it; registered-feedback
bursts (`CTI`/`BTE` carried, driven CLASSIC/LINEAR, never generated); LOCK
and the TGA/TGC/TGD tags (not in the `rtl/amba/wb4` family either).

**Docs.** Converters MAS ch03 `13_axi4_to_wb4`, `14_wb4_to_axi4` (+ overview,
index); bridge HAS `ch04_interfaces/06_wb4_interface.md` (+ index, key
features, protocol-support tables) and MAS (protocol conversion 2.7.2,
2.7.16 "Wishbone B4 at Either Boundary", 2.7.17 Wishbone no longer future,
test strategy); PRD; PDFs v1.4; handbook `dv/bfm-usage` (WB4Slave OOR case)
and `design/generated-rtl-discipline` (the arbitration helper). Related:
[[BRIDGE-014]].

---
