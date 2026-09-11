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

# APB SMBus Specification - Table of Contents

**Component:** APB System Management Bus (SMBus) Controller
**Version:** 1.2
**Last Updated:** 2026-09-10
**Status:** RTL Functional - SMBus 2.0 master AND target, both implemented and
regression-clean. RLB-011 is closed; what remains unbuilt is SMBALERT#, Host
Notify and ARP

---

## Overview

> Status (2026-09-09): Only the Chapter 1 overview and the Chapter 5 register map exist
> in this tree today. The remaining chapters listed below are planned but not yet
> written; they are shown without links.

Chapter 1 describes the block as built: the module decomposition, the
open-drain contract, the timing sets, the timeout and bus recovery, the abort
discipline, the transaction table and the clock crossing. Chapter 5 is the
register map with every field as the RDL describes it, the FIFO contract and
the programming sequences. Ground truth is `rtl/smbus/README.md` and
`rtl/smbus/peakrdl/smbus_regs.rdl`; where this book and those disagree, the
RTL tree wins.

### Block Diagram

![SMBus Block Diagram](assets/svg/smbus_top.png)

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-01 | RTL Design Sherpa | Initial specification |
| 1.1 | 2026-09-09 | RTL Design Sherpa | Issue #58 fixes: master engine rewritten as a transaction sequencer (smbus_core with smbus_trans_decode, smbus_flow_rules, smbus_abort_track, smbus_byte_fifos, smbus_int_status, smbus_pec) over a bit-level PHY (smbus_bit_phy) that alone owns SCL/SDA, open-drain by construction; command/data/PEC bytes transmitted and the repeated START issued on every read with a command code; standard- and fast-mode timing sets from one divider with clock stretching on every SCL release and a bus-free wait before START; SCL-low timeout (0 = disabled) covering every waiting state with I2C bus recovery (nine standard-mode clocks then STOP) on expiry; every exit a real STOP or a reported release with busy=0 coinciding with both lines released; PEC generated on writes and checked on reads over both address bytes; sticky W1C INT_STATUS with set-wins and a registered smb_interrupt pin, crossed through glitch_free_n_dff_arn when CDC_ENABLE=1; SMBUS_DATA / SMBUS_PEC / SMBUS_BLOCK_COUNT hardware-written only on a result; TX FIFO push from write data; per-type data byte counts; soft_reset and fast_mode acted on; two-cycle strobe contract; strict fifteen-register decode with PSLVERR; complete/bus_error/timeout_error truth table (complete never set alongside an error); recovery clocks as full standard-mode bits with the two no-recovery timeout exits; stall counter armed only while this master owns a primitive, worst case five SMBUS_TIMEOUT windows to busy=0; RX overrun = first byte that does not fit is not stored and NAKed; TX FIFO push gated on the data lane's PSTRB; SCL/SDA two-flop synchronized as asynchronous pads in both builds; FIFO_DEPTH 2..63; recovery inside a normal STOP reports complete=1 (invisible to software); SMBUS_PEC holds the transmitted (write) or received (read) PEC byte; bus-free wait unbounded with SMBUS_TIMEOUT=0 (lone stop aborts it); master-side Block Write count clamp with the register reading back what was written; SMBUS_DATA written by every received byte; soft_reset/fifo_reset as synchronous clears; no reset synchronizer (integrator delivers synchronized presetn/smbus_resetn); FIFO levels/flags consistent by construction, strobes clear both FIFOs over their window with nothing accepted, fifo_reset mid-receive discards what was received, empty RX_FIFO read returns the stale head, level range 0..FIFO_DEPTH; RESET_ACTIVE_HIGH build unusable until COMMON-026 / RLB-012. The former "Known RTL deviations" list is retired |
| 1.2 | 2026-09-10 | RTL Design Sherpa | RLB-011 closed. Target (slave) mode: a separate `smbus_slave_engine` because the master owns the clock and a target does not, so every target action is a response to an edge somebody else produced. Address match with the general call behind `SMBUS_SLAVE_CTRL.gc_en`; an ACK policy that NAKs the own address when software says it is busy (`nack_all`) and NAKs a data byte when the RX FIFO is full, because a silently dropped byte leaves the master writing into a target that is not listening; RX and TX paths through the shared FIFOs; optional clock stretching while software fills the queue (`stretch_en`), 0xFF when it is off; the target's own PEC, which never counts bytes because a correct trailing PEC drives a CRC-8 to zero on a write and the running value IS the byte to send on a read; three new interrupt sources (slave_rx, slave_tx, slave_done). Both engines only ever pull down, so the pins are the wired-AND of their releases and the merge needs no ownership mux; a master START is refused while the target is ANSWERING rather than whenever the bus looks busy, because SDA held low under a high SCL looks exactly like a START that never ends and claiming the wire for that would block bus recovery. Multi-master arbitration: every transmitted bit read back, a 1 that reads as 0 releases both lines within the bit and reports arb_lost without framing a STOP. Quick Command has both directions, each its own transaction type. Two new registers (SMBUS_SLAVE_CTRL, SMBUS_SLAVE_STATUS) take the map to seventeen and the decode to seven address bits, moving the first alias of SMBUS_CONTROL from 0x040 to 0x080. RESET_ACTIVE_HIGH is usable now: COMMON-026 and RLB-012 are both fixed |

---

## Navigation

### Chapter 1: Overview
- [01_overview.md](ch01_overview/01_overview.md) - Component overview
- 02_architecture.md - Architecture *(planned, not yet written)*

### Chapter 2: Blocks
- 00_overview.md - Block hierarchy *(planned, not yet written)*

### Chapter 3: Interfaces
- 00_overview.md - Interface summary *(planned, not yet written)*

### Chapter 4: Programming Model
- 00_overview.md - Programming overview *(planned, not yet written)*

### Chapter 5: Registers
- [01_register_map.md](ch05_registers/01_register_map.md) - Register map
