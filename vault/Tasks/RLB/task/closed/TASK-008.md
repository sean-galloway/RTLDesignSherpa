# TASK-008: IOAPIC features deferred past the #48 fix

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-008** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-09-14

Every feature this entry tracked is built. Four of them ship as COMPANION
modules, which is what kept apb4_ioapic's delivery-channel interface intact
(Sean's 2026-09-11 decision): payload + valid/ready + status, so a bridge can
carry that shape onto a bus. `apb4_ioapic.f` references none of the four.

- **Logical destination mode** — FIXED 4bce6badc. The IOAPIC forwards the
  field and the mode; the local APICs match.
- **Round-robin arbitration** — `IOAPICARBCFG.rr_enable`, IOWIN selector 0x03.
- **LowestPriority, delegated** — the IOAPIC half landed 2026-09-11
  (`irq_out_retry`); the arbitration half ships as `ioapic_lowest_pri_arb`
  (7a4096b24), formal prove+cover PASS, system-context tested fab087467.
- **Multi-IOAPIC routing** — `ioapic_deliv_merge` (e0c77afc9), N channels
  merged round-robin with each message tagged by source id so an EOI routes
  back to the IOAPIC holding that pin's Remote IRR. Tested 72484a498.
- **MSI** — `ioapic_msi_emit` (4e60ac88b) plus programmable address and data
  (1bf991778: IOAPICMSIADDR/IOAPICMSIDATA at selectors 0x04/0x05) and seam
  tests (b274ccb6b). I had filed MSI as BLOCKED on "an APB slave has no
  initiator port"; Sean: *"Isn't msi just a write to an address"*. He was
  right — the emitting is the companion's job and the block stayed a slave.
- **Boot interrupt** — `ioapic_boot_intx` (21f071b93), gated on an enable bit
  AND the RTE mask, with the pin-to-legacy-IRQ map specified in rlb_top
  (identity for pins 0-7, no reroute above). This entry had carried a
  category error for weeks, mine: it described INIT-SIPI-SIPI, which is a
  local APIC's AP-startup IPI. The real feature is chipset INTx rerouting.

**One design question survives the close, already ruled on.** `deliv_retry` is
inert while the MSI write is posted: the delivery handshake closes when the
write is QUEUED (deliv_ready is the master's cmd_ready) and PSLVERR returns
strictly later, while ioapic_core samples retry AT the handshake. Measured --
handshakes=1, retry_asserts=1, retry_at_handshake=0. Sean: *"Silently drop is
bad. We at least need to count when that happens."* So drops are counted in
IOAPICMSIDROP (c9a3f0d40), in pclk with a gray-coded crossing; a counter in
ioapic_core read 0 in both CDC cells, which MED-9 caught.

**Verified at close:** 75 passed / 0 failed at REG_LEVEL=FULL (63 when the
arc began), formal 10/10 prove+cover through the retro_legacy_blocks
aggregator, and every new claim mutation-checked.

---
