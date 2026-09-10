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
**Version:** 1.1
**Last Updated:** 2026-09-09
**Status:** RTL Functional - SMBus 2.0 master implemented and regression-clean
after the GitHub #58 rewrite; slave mode, multi-master arbitration and
read-direction Quick Command are not implemented (RLB-011)

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
| 1.1 | 2026-09-09 | RTL Design Sherpa | Issue #58 fixes: master engine rewritten as a transaction sequencer (smbus_core with smbus_trans_decode, smbus_flow_rules, smbus_abort_track, smbus_byte_fifos, smbus_int_status, smbus_pec) over a bit-level PHY (smbus_bit_phy) that alone owns SCL/SDA, open-drain by construction; command/data/PEC bytes transmitted and the repeated START issued on every read with a command code; standard- and fast-mode timing sets from one divider with clock stretching on every SCL release and a bus-free wait before START; SCL-low timeout (0 = disabled) covering every waiting state with I2C bus recovery (nine standard-mode clocks then STOP) on expiry; every exit a real STOP or a reported release with busy=0 coinciding with both lines released; PEC generated on writes and checked on reads over both address bytes; sticky W1C INT_STATUS with set-wins and a registered smb_interrupt pin, crossed through glitch_free_n_dff_arn when CDC_ENABLE=1; SMBUS_DATA / SMBUS_PEC / SMBUS_BLOCK_COUNT hardware-written only on a result; TX FIFO push from write data; per-type data byte counts; soft_reset and fast_mode acted on; two-cycle strobe contract; strict fifteen-register decode with PSLVERR; complete/bus_error/timeout_error truth table (complete never set alongside an error); recovery clocks as full standard-mode bits with the two no-recovery timeout exits; stall counter armed only while this master owns a primitive, worst case five SMBUS_TIMEOUT windows to busy=0; RX overrun = first byte that does not fit is not stored and NAKed; TX FIFO push gated on the data lane's PSTRB; SCL/SDA two-flop synchronized as asynchronous pads in both builds; FIFO_DEPTH 2..63; recovery inside a normal STOP reports complete=1 (invisible to software); SMBUS_PEC holds the transmitted (write) or received (read) PEC byte; bus-free wait unbounded with SMBUS_TIMEOUT=0 (lone stop aborts it); master-side Block Write count clamp with the register reading back what was written; SMBUS_DATA written by every received byte; soft_reset/fifo_reset as synchronous clears; no reset synchronizer (integrator delivers synchronized presetn/smbus_resetn); FIFO levels/flags consistent by construction, strobes clear both FIFOs over their window with nothing accepted, fifo_reset mid-receive discards what was received, empty RX_FIFO read returns the stale head, level range 0..FIFO_DEPTH; RESET_ACTIVE_HIGH build unusable until COMMON-026 / RLB-012. The former "Known RTL deviations" list is retired; remaining limitations (slave stub, no arbitration, write-only Quick Command, start ignored with master_en clear) are RLB-011 |

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
