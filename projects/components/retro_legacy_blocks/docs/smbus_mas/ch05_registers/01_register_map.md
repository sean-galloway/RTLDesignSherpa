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

# APB SMBus - Register Map

## Overview

The register map below is generated from `rdl/smbus/smbus_regs.rdl`
and matches the decode in `rtl/smbus/smbus_config_regs.sv`. Field
descriptions are quoted from the RDL, which is the single source of truth for
the fields; the contracts behind them (timing, timeout, FIFOs, interrupts) are
from `rtl/smbus/README.md`.

**Strict decode.** Only the seventeen mapped registers decode. Every other
address in the 4 KB window is dropped: no internal strobe fires, the read
returns 0, and the access is acknowledged locally with `PSLVERR`. The
generated block sees seven address bits, so without the strict decode every
unmapped address would alias onto a real register 128 bytes below it (0x080
would write `SMBUS_CONTROL`). It was six bits and 0x040 until the two target
registers pushed the top of the map past 0x03F. The drop is acknowledged combinationally and
locally because the adapter holds its request until it is acknowledged; a
dropped access that is never acknowledged hangs the bus.

Access legend: RW = read/write, RO = read-only, WO = write-only,
W1C = write-1-to-clear, AC = self-clearing (hardware clears the bit after the
action).

### Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x00 | SMBUS_CONTROL | RW | 0x00000000 | Global control (enable, mode, PEC, resets) |
| 0x04 | SMBUS_STATUS | RO | 0x00000000 | Status flags and FSM state |
| 0x08 | SMBUS_COMMAND | RW | 0x00000000 | Transaction type, command byte, start/stop |
| 0x0C | SMBUS_SLAVE_ADDR | RW | 0x00000000 | Target slave address (master mode) |
| 0x10 | SMBUS_DATA | RW | 0x00000000 | Single data byte, both directions |
| 0x14 | SMBUS_TX_FIFO | WO | 0x00000000 | Transmit FIFO write port |
| 0x18 | SMBUS_RX_FIFO | RO | - | Receive FIFO read port (read pops) |
| 0x1C | SMBUS_FIFO_STATUS | RO | 0x00008080 (live) | TX/RX FIFO levels and flags (post-reset both FIFOs empty: tx_empty bit 7, rx_empty bit 15) |
| 0x20 | SMBUS_CLK_DIV | RW | 0x000000F9 | SCL clock divider |
| 0x24 | SMBUS_TIMEOUT | RW | 0x002625A0 | SCL-low limit in clocks, 0 = disabled; worst case to busy=0 is five windows |
| 0x28 | SMBUS_OWN_ADDR | RW | 0x00000000 | The address this target answers, and its enable |
| 0x2C | SMBUS_INT_ENABLE | RW | 0x00000000 | Interrupt enable mask |
| 0x30 | SMBUS_INT_STATUS | W1C | 0x00000000 | Sticky interrupt status; reads 0 out of reset |
| 0x34 | SMBUS_PEC | RW | 0x00000000 | PEC value (CRC-8) |
| 0x38 | SMBUS_BLOCK_COUNT | RW | 0x00000000 | Block transfer byte count |
| 0x3C | SMBUS_SLAVE_CTRL | RW | 0x00000000 | Target policy: general call, NAK-all, PEC, clock stretching |
| 0x40 | SMBUS_SLAVE_STATUS | RO | 0x00000000 | Target direction, stretching, PEC verdict and running value |

---

## Functional Description

Every register, in offset order, with field-level tables. The access legend
above applies throughout.

### SMBUS_CONTROL (0x00)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | master_en | RW | 0 | Enable master mode (0=disabled, 1=enabled). `SMBUS_COMMAND.start` is ignored unless this is already set |
| 1 | slave_en | RW | 0 | Enable target mode. With `SMBUS_OWN_ADDR.addr_en` this arms the target engine; see SMBUS_SLAVE_CTRL for its policy |
| 2 | pec_en | RW | 0 | Enable Packet Error Checking (0=disabled, 1=enabled). Sampled when the transaction starts |
| 3 | fast_mode | RW | 0 | 0 = 100 kHz standard-mode timing, 1 = 400 kHz fast-mode timing. Selects the whole timing set, not just a frequency (see below) |
| 4 | fifo_reset | RW/AC | 0 | Reset TX/RX FIFOs (write 1, auto-clears). A synchronous clear of the two byte buffers only, leaving the engine alone |
| 5 | soft_reset | RW/AC | 0 | Write 1 to synchronously restart the master engine, the bit PHY, the PEC accumulator and both FIFOs, and to clear the sticky status: a synchronous clear, not an asynchronous reset. Self-clearing: it always reads back 0; as the hardware sees it the strobe is two `pclk` cycles wide (the bridge holds its request), and every consumer acts once across that window. The register file is not touched |
| 31:6 | Reserved | RO | 0 | Reads 0 |

**fast_mode**, from the RDL: "Selects the whole timing SET, not just a
frequency, and the set is ASYMMETRIC because a symmetric period cannot meet
fast mode at all: tLOW >= 1.3 us and tHIGH >= 0.6 us do not both fit in two
equal halves of 2.5 us. The SCL period is eight base units either way; in
standard mode the unit is (SMBUS_CLK_DIV+1)/2 and the low and high phases
take four units each, in fast mode the unit is (SMBUS_CLK_DIV+1)/8 and the low
phase takes five units to the high phase's three. tHD;STA and tSU;STA shrink
from four units to two; tSU;STO and tBUF stay at five units in BOTH modes,
because their fast-mode minimums are not proportionally smaller." The
achieved-versus-required table is Table 1.2 in Chapter 1. Bus recovery clocks
always use standard-mode timing whatever this bit says.

**soft_reset**, from the RDL: "The REGISTER FILE IS NOT TOUCHED - software
keeps everything it programmed and only the engine starts over. Use it to
recover a wedged bus without reconfiguring the block." The PHY releases both
lines as it aborts.

**Strobe width.** `soft_reset`, `fifo_reset`, `SMBUS_COMMAND.start` and
`SMBUS_COMMAND.stop` are all self-clearing strobes that are two `pclk` cycles
wide as the hardware sees them, because the cmd/rsp bridge holds its request
for two cycles. Every consumer is written to act once across that window:
`start` is only taken in the idle state, an abort is blocked once the error
state is entered, and the two reset strobes are level clears where a second
cycle changes nothing.

---

### SMBUS_STATUS (0x04)

Read-only. Software writes to this register are dropped (no PSLVERR). The
error bits and `complete` are result flags: hardware clears all of them when
the next `start` is accepted and sets them as the transaction runs, so they
hold the outcome of the last transaction until a new one begins. The sticky,
W1C event bits are in SMBUS_INT_STATUS (0x30).

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | busy | RO | Transaction in progress (0=idle, 1=busy). High from the accepted START request until the FSM is back in idle, whether the transaction succeeded or not. Dropping to 0 always coincides with both lines released |
| 1 | bus_error | RO | Bus error: a transfer was aborted for a reason other than a NAK or a PEC mismatch - `SMBUS_COMMAND.stop` written alone, a TX FIFO underrun, an RX FIFO overrun, or bus recovery that could not free SDA within nine clocks. Set together with `timeout_error` it means recovery was attempted, failed, and the bus was released without a STOP |
| 2 | timeout_error | RO | A bus timeout: SCL was held low - by this master or by anyone else - for longer than SMBUS_TIMEOUT. The transaction was aborted and the bus released. When this bit is set, recovery clocks were issued: every timeout abort runs I2C bus recovery (up to nine SCL pulses with SDA released, standard-mode timing) before its STOP. If SDA was still low after nine clocks, `bus_error` is set as well and no STOP was generated |
| 3 | pec_error | RO | PEC mismatch detected: on a read with `pec_en`, the slave's PEC byte differed from the running CRC. `complete` is not set |
| 4 | arb_lost | RO | Multi-master arbitration lost: a transmitted 1 read back as 0. Both lines are released within the bit and the sequencer idles WITHOUT framing a STOP, because the winner's transfer is still in progress |
| 5 | nak_received | RO | NAK received from slave, at any byte: address, command, data or PEC. A NAK aborts the transaction through a STOP and counts as an error for `error_int`, but does not set `bus_error` |
| 6 | slave_addressed | RO | This device is addressed as a target and in a transfer. A LEVEL, true until the STOP; the sticky version is `SMBUS_INT_STATUS.slave_addr_int` |
| 7 | complete | RO | Transaction completed successfully: the transaction finished and the bus was released with a STOP. Never set alongside any error; it is computed from the next-state error terms, including the ones raised on the very edge the STOP completes, so a transaction that did not terminate the bus cannot report success |
| 11:8 | fsm_state | RO | Current state machine state (for debugging); the encoding is ABI, see below |
| 31:12 | Reserved | RO | Reads 0 |

#### What the status bits mean together

| `complete` | `bus_error` | `timeout_error` | Meaning |
|---|---|---|---|
| 1 | 0 | 0 | the transaction finished and the bus was released with a STOP. This includes a STOP that found SDA held low, escalated into recovery and recovered: recovery inside a normal STOP is invisible to software |
| 0 | 0 | 1 | a timeout; the bus was released. Recovery either was not applicable (nothing framed, or the STOP itself timed out) or ran and succeeded, and a STOP was generated |
| 0 | 1 | 1 | a timeout, recovery was attempted and failed: SDA was still low after nine clocks, both lines were released and no STOP reached the wire |
| 0 | 1 | 0 | aborted without a timeout: `COMMAND.stop` alone, a TX underrun, an RX overrun, or a STOP whose recovery failed |
| 0 | x | x | with `nak_received` or `pec_error`: the slave did not acknowledge, or the PEC did not match |

Recovery does not run on two timeout exits: a timeout in the final STOP
itself (the PHY has already released both lines to report it), and a timeout
before anything of ours was framed unless SDA is the line being held and SCL
is quiet (if SCL is also low somebody else is mid-transfer, and pulsing SCL
would clock their bits). A stuck SDA on an otherwise quiet bus is recovered
even though no START went out. Recovery clocks are full standard-mode bits
(tLOW 5000 ns, tHIGH 5000 ns at the default divider) in both modes.

#### fsm_state encoding

| Value | State | Value | State |
|-------|-------|-------|-------|
| 0x0 | IDLE | 0x8 | DATA_RD |
| 0x1 | START | 0x9 | DATA_RD_ACK |
| 0x2 | ADDR | 0xA | PEC_WR |
| 0x3 | ADDR_ACK | 0xB | PEC_WR_ACK |
| 0x4 | CMD | 0xC | PEC_RD |
| 0x5 | CMD_ACK | 0xD | STOP |
| 0x6 | DATA_WR | 0xE | ERROR |
| 0x7 | DATA_WR_ACK | 0xF | RESTART |

ERROR is the state every abort passes through; it issues the STOP (bus
recovery first if SDA is stuck), releases both lines and returns to IDLE on
its own. Software never has to act to leave it.

---

### SMBUS_COMMAND (0x08)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 3:0 | trans_type | RW | 0 | Transaction type (see Transaction Types) |
| 7:4 | Reserved | RO | 0 | Reads 0 |
| 15:8 | cmd_code | RW | 0 | SMBus command byte (for transactions that use it) |
| 16 | start | RW/AC | 0 | Write 1 to launch the transaction described by the rest of this register. Self-clearing. It is ignored unless `SMBUS_CONTROL.master_en` is already set - the write is accepted and silently discarded, `SMBUS_STATUS.busy` never rises and no error is reported, so software must enable master mode before starting |
| 17 | stop | RW/AC | 0 | Written together with `start` it is a no-op: every transaction ends with a STOP anyway. Written alone while `SMBUS_STATUS.busy` is set it is an abort - the transaction stops, a real STOP is generated on the wire, both lines are released, `busy` drops and `SMBUS_STATUS.bus_error` is set. Self-clearing |
| 31:18 | Reserved | RO | 0 | Reads 0 |

`trans_type`, `cmd_code`, `SMBUS_SLAVE_ADDR`, `SMBUS_CONTROL.pec_en` and the
transaction's data byte count are sampled when `start` is accepted; changing
them while `busy` is set does not affect the running transaction.

#### Transaction Types

`trans_type` is a 4-bit field. Block Write and Block Read are separate
encodings. `[PEC]` is present only when `pec_en` is set; `(N)` marks the byte
the master NAKs.

| trans_type | Description | On the wire | Data bytes |
|------------|-------------|-------------|------------|
| 0 | Quick Command | `S, Addr+W, P` | 0 |
| 1 | Send Byte | `S, Addr+W, Data, [PEC], P` | 1 |
| 2 | Receive Byte | `S, Addr+R, Data(N), [PEC], P` | 1 |
| 3 | Write Byte | `S, Addr+W, Cmd, Data, [PEC], P` | 1 |
| 4 | Read Byte | `S, Addr+W, Cmd, Sr, Addr+R, Data(N), [PEC], P` | 1 |
| 5 | Write Word | `S, Addr+W, Cmd, DataLo, DataHi, [PEC], P` | 2 |
| 6 | Read Word | `S, Addr+W, Cmd, Sr, Addr+R, DataLo(A), DataHi(N), [PEC], P` | 2 |
| 7 | Block Write | `S, Addr+W, Cmd, Count, Data x Count, [PEC], P` | BLOCK_COUNT |
| 8 | Block Read | `S, Addr+W, Cmd, Sr, Addr+R, Count, Data x Count(N), [PEC], P` | Count, from the slave |
| 9 | Block Write-Block Read Process Call | Block Write then `Sr, Addr+R, Count, Data x Count(N), [PEC], P` | both |

Every read that carries a command code has a repeated START. The data byte
count is per transaction type: `SMBUS_BLOCK_COUNT` governs the block
transfers and nothing else. Values 10 to 15 are not transaction types; they
decode with no command byte, no data and write direction, so they go out as a
Quick Command.

---

### SMBUS_SLAVE_ADDR (0x0C)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 6:0 | slave_addr | RW | 0 | Target slave address, 7 bits. The R/W direction is not in this field - it comes from `SMBUS_COMMAND.trans_type`, and the controller appends it when it puts the address byte on the wire (twice, for a read with a command code) |
| 31:7 | Reserved | RO | 0 | Reads 0 |

There is no writable R/W bit at bit 7; writes to bit 7 are ignored and it
reads back 0. Quick Command has both directions, and each is its own
transaction type rather than a direction bit: type 0x0 sends the address with
R/W = 0 and type 0xA with R/W = 1. The R/W bit IS the payload of a quick
command, so a shared direction bit would mean nothing for the other nine
types.

---

### SMBUS_DATA (0x10)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 7:0 | data | RW | 0 | Data byte. Software writes it for Send Byte / Write Byte; hardware writes it with every received data byte, so after a Receive Byte / Read Byte it holds that byte and after a Read Word / Block Read it holds the last byte received (the RX FIFO has them in order). The hardware path is qualified with `we` so it only lands when there is a received byte |
| 31:8 | Reserved | RO | 0 | Reads 0 |

A software-written byte therefore survives until a read replaces it; a
write-then-read returns what software wrote. A one-byte read lands here as
well as in the RX FIFO, so reading a single byte needs no FIFO access at all.

---

### SMBUS_TX_FIFO (0x14)

Write-only port into the transmit FIFO (`FIFO_DEPTH` bytes, 32 by default).
Each write pushes one byte. Reads return 0.

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 7:0 | tx_data | WO | 0 | Write data byte to TX FIFO |
| 31:8 | Reserved | RO | 0 | Reads 0 |

The push takes its byte from the write data of the access that causes it, on
a single-cycle edge, so back-to-back writes each push exactly once and the
byte pushed is the byte written. The byte enable is part of the decode: a
write to this register with the data byte lane disabled (`PSTRB[0]=0`) is not
a FIFO push at all, rather than a push of 0x00. A write while the FIFO is
full is dropped by `fifo_sync`; check `SMBUS_FIFO_STATUS.tx_full` first.

---

### SMBUS_RX_FIFO (0x18)

Read-only port from the receive FIFO (`FIFO_DEPTH` bytes, 32 by default).
Each read pops one byte. A read with the FIFO empty returns the stale head
byte, not 0; check `SMBUS_FIFO_STATUS.rx_empty` (or the level) first.

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 7:0 | rx_data | RO | Read data byte from RX FIFO |
| 31:8 | Reserved | RO | Reads 0 |

---

### SMBUS_FIFO_STATUS (0x1C)

Read-only FIFO level and flag register.

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 5:0 | tx_level | RO | Number of bytes in TX FIFO (0..`FIFO_DEPTH`, 0-32 at the default depth) |
| 6 | tx_full | RO | TX FIFO full flag |
| 7 | tx_empty | RO | TX FIFO empty flag |
| 13:8 | rx_level | RO | Number of bytes in RX FIFO (0..`FIFO_DEPTH`, 0-32 at the default depth) |
| 14 | rx_full | RO | RX FIFO full flag |
| 15 | rx_empty | RO | RX FIFO empty flag |
| 31:16 | Reserved | RO | Reads 0 |

---

### SMBUS_CLK_DIV (0x20)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 15:0 | clk_div | RW | 0x00F9 (249) | SCL clock divider |
| 31:16 | Reserved | RO | 0 | Reads 0 |

From the RDL: "STANDARD MODE: SCL = sys_clk / (4 * (div + 1)) - the default
249 gives 100 kHz at 100 MHz. FAST MODE (SMBUS_CONTROL.fast_mode=1) is four
times faster from the SAME divider: SCL = sys_clk / ((div + 1)), i.e. 8 units
of (div+1)/8 clocks - 249 gives 390.6 kHz at 100 MHz. Both unit divides round
UP, so a small divider cannot silently shorten the period."

---

### SMBUS_TIMEOUT (0x24)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 23:0 | timeout | RW | 0x2625A0 (2,500,000) | Bus timeout in core clock cycles. It measures how long SCL is low on the bus - either this master pulling it down or the line still reading low after we let go - so it catches a stretching slave, a short and a wedged master alike. It is counted only while this master owns a primitive; an idle bus held low by somebody else does not arm it. 0 disables the check entirely; it must never mean "expire immediately". Default 2500000 is ~25 ms at 100 MHz |
| 31:24 | Reserved | RO | 0 | Reads 0 |

Expiry aborts the transaction, reports `SMBUS_STATUS.timeout_error`, runs bus
recovery (with the two exceptions under SMBUS_STATUS), releases the bus and
returns the FSM to idle. The window also bounds the bus-free wait before a
START, and every state that can wait on SCL is covered, the final STOP
included. With the timeout disabled (0) the bus-free wait is unbounded: on a
bus that never frees, `busy` stays 1 in the start state until software
writes `SMBUS_COMMAND.stop`, which aborts cleanly with a lone STOP.

**Worst case from "SCL wedges" to `busy=0` is five times this value** (about
125 ms at the default): one window for the primitive that stalls, then four
for the abort's STOP, which is deliberately more patient. Size the value with
the multiplier in mind.

---

### SMBUS_OWN_ADDR (0x28)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 6:0 | own_addr | RW | 0 | 7-bit own slave address |
| 7 | addr_en | RW | 0 | Enable own address matching (slave mode) |
| 31:8 | Reserved | RO | 0 | Reads 0 |

`addr_en` is what makes the target answer an address at all: with it clear
the compare is disabled and the engine responds to nothing, whatever
`SMBUS_CONTROL.slave_en` says.

---

### SMBUS_INT_ENABLE (0x2C)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | complete_en | RW | 0 | Enable interrupt on transaction complete |
| 1 | error_en | RW | 0 | Enable interrupt on bus error (any of `bus_error`, `timeout_error`, `pec_error`, `nak_received`) |
| 2 | tx_thresh_en | RW | 0 | Enable the TX threshold interrupt. The threshold is fixed at empty: the condition is `tx_fifo_empty`, not a programmable level |
| 3 | rx_thresh_en | RW | 0 | Enable the RX threshold interrupt. The threshold is fixed at non-empty: the condition is `!rx_fifo_empty`, not a programmable level |
| 4 | slave_addr_en | RW | 0 | Enable interrupt when addressed as a target |
| 5 | slave_rx_en | RW | 0 | Enable interrupt when the target takes a byte off the bus into the RX FIFO |
| 6 | slave_tx_en | RW | 0 | Enable interrupt when the target needs a byte to transmit and the TX FIFO is empty. With `SMBUS_SLAVE_CTRL.stretch_en` set the bus is being held while this is true, so software is on the clock |
| 7 | slave_done_en | RW | 0 | Enable interrupt when a transfer addressed to this target ends at the STOP. `SMBUS_SLAVE_STATUS.pec_error` is valid from that moment |
| 31:8 | Reserved | RO | 0 | Reads 0 |

There is no programmable threshold register; the two threshold bits are
edge-set on the fixed conditions above.

---

### SMBUS_INT_STATUS (0x30)

From the RDL: "Interrupt status flags (write 1 to clear). Every bit is sticky:
set by the RISING EDGE of its condition and cleared only by a W1C write, with
SET WINNING over a simultaneous clear. The smb_interrupt pin is
(SMBUS_INT_STATUS & SMBUS_INT_ENABLE) != 0, registered - so clearing a bit
here is what deasserts the pin."

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | complete_int | W1C | 0 | Transaction completed: rising edge of `SMBUS_STATUS.complete` |
| 1 | error_int | W1C | 0 | Bus error occurred: rising edge of any of `bus_error`, `timeout_error`, `pec_error`, `nak_received` |
| 2 | tx_thresh_int | W1C | 0 | TX FIFO became empty (the threshold is fixed at empty). Sticky: set on the edge of the condition, cleared only by writing 1. It is not a live level |
| 3 | rx_thresh_int | W1C | 0 | RX FIFO became non-empty (the threshold is fixed at non-empty). Sticky: set on the edge of the condition, cleared only by writing 1 |
| 4 | slave_addr_int | W1C | 0 | Addressed as a target: rising edge of `SMBUS_STATUS.slave_addressed` |
| 5 | slave_rx_int | W1C | 0 | The target took a byte off the bus into the RX FIFO |
| 6 | slave_tx_int | W1C | 0 | The target needs a byte to transmit and the TX FIFO is empty |
| 7 | slave_done_int | W1C | 0 | A transfer addressed to this target ended at the STOP |
| 31:8 | Reserved | RO | 0 | Reads 0 |

The sticky bits live in hardware (`smbus_int_status`); the generated field is
a live mirror of them. The W1C is decoded in `smbus_config_regs` as
`wr_data & wr_biten` at this register's address, on the rising edge of the
held request: a byte-strobed write clears only bits in the bytes it wrote,
and the two-cycle request clears once. Writing 0 to a bit leaves it alone.

The register reads 0 out of reset: the edge detector is armed one cycle after
reset so a condition that is already true at time zero (an empty TX FIFO)
does not set a bit with no access having taken place.

`smb_interrupt` is one register stage behind the masked status
(`CDC_ENABLE=0`), or the masked status through a three-flop level
synchronizer onto `pclk` plus one register stage (`CDC_ENABLE=1`).
`soft_reset` clears the sticky status.

---

### SMBUS_PEC (0x34)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 7:0 | pec | RW | 0 | PEC value (CRC-8, polynomial 0x07). Hardware writes the computed PEC of the transaction that just finished, and only then (`we`), so a software-written value survives until a transaction replaces it. After a transfer it holds the transmitted PEC byte (writes) or the received PEC byte (reads); the computed CRC is not exposed, so on a PEC error the register shows the slave's byte and the comparison result is `SMBUS_STATUS.pec_error` |
| 31:8 | Reserved | RO | 0 | Reads 0 |

The CRC covers every byte that was actually on the wire, in wire order,
including both address bytes. The received PEC byte is never folded into the
CRC; it is the thing being checked. Software does not need to program this
register for a transaction; hardware computes the PEC itself.

---

### SMBUS_BLOCK_COUNT (0x38)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 5:0 | block_count | RW | 0 | Block transfer byte count (1-32). Software programs it for Block Write; for Block Read the count comes from the slave, and hardware writes it back here (`we`) clamped both ways: a count of 0 becomes 1, and a count longer than the FIFO depth becomes the depth, so software knows how many bytes to drain. It governs the block transfers only - a Write Byte sends one data byte whatever this holds |
| 31:6 | Reserved | RO | 0 | Reads 0 |

For a Block Write the count byte on the wire is this value and the payload is
`block_count` bytes from the TX FIFO. The SMBus-legal range is 1-32; the
master-side clamp sends a programmed 0 as 1 and anything above `FIFO_DEPTH`
as `FIFO_DEPTH`, while the register reads back what software wrote. A count
larger than the number of staged bytes is a TX underrun (see The FIFO
Contract). For a Block Read, a slave-supplied count of
0 is clamped to 1 and one larger than `FIFO_DEPTH` is clamped to the depth,
and the clamped value is what lands here. Block Process Call shares this
register between its write and read halves.

---

### SMBUS_SLAVE_CTRL (0x3C)

Target-mode policy. `SMBUS_CONTROL.slave_en` turns the engine on and
`SMBUS_OWN_ADDR` says which address it answers; these are the choices that
have no obvious right answer.

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | gc_en | RW | 0 | Answer the general call address 0x00 as well as the own address. The general call is a write by definition, so a read to 0x00 is not a match |
| 1 | nack_all | RW | 0 | Software is busy: NAK this target's own address instead of answering it. A NAK is the only way a target can say "not now" without holding the bus, which is what the alternative -- stretching the clock until software catches up -- does to every other device on the wire |
| 2 | pec_en | RW | 0 | Maintain a CRC-8 over every byte of a transfer addressed to this target, the address bytes included. See the note below |
| 3 | stretch_en | RW | 0 | Hold SCL low while a read waits for software to put a byte in the TX FIFO. With this clear an empty FIFO sends 0xFF instead, which is what an unprogrammed target on a real bus looks like and keeps a slow CPU from wedging the whole bus |
| 31:4 | Reserved | RO | 0 | Reads 0 |

**The target PEC never counts bytes.** A target does not know how long a
transfer is; the protocol does, and the protocol lives in software. CRC-8
removes the need to know. On a **write** the running value covers the address
byte and every data byte, and a correct trailing PEC byte drives it to
**zero**, so "PEC good" is "the running value is zero at the STOP". On a
**read**, when the TX FIFO runs dry the byte sent IS the running CRC, which is
exactly the PEC the master is waiting for; software sets the length by how
many bytes it queues.

---

### SMBUS_SLAVE_STATUS (0x40)

What the target engine is doing. Read-only: every bit is a live view of the
engine, and the sticky versions software can poll at leisure are in
SMBUS_INT_STATUS.

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | rd_not_wr | RO | 0 | Direction of the transfer in progress: 1 = the master is reading from this target, 0 = writing to it |
| 1 | stretching | RO | 0 | The engine is holding SCL low, waiting for software to put a byte in the TX FIFO |
| 2 | pec_error | RO | 0 | The last WRITE transfer addressed to this target ended with a running CRC that was not zero, which means the master's PEC byte did not match. Valid from the STOP; cleared at the next START |
| 7:3 | Reserved | RO | 0 | Reads 0 |
| 15:8 | pec_value | RO | 0 | The running CRC-8. Zero after a correct write PEC; the byte that will be sent when a read runs out of queued data |
| 31:16 | Reserved | RO | 0 | Reads 0 |

---

## The FIFO Contract

**Load and pop.** A transmitted byte is loaded from the TX FIFO and popped in
the same cycle; the FIFO's read data is its combinational head, so the value
captured on the edge that pops is the byte being loaded. Write Word and Block
Write take their data from the TX FIFO in order; Send Byte and Write Byte
take it from `SMBUS_DATA` and generate no FIFO traffic; a Block Write's first
transmitted byte after the command is the count.

**TX underrun** (`SMBUS_BLOCK_COUNT` larger than the number of staged
bytes): after the last staged byte the master stops, sets `error_int`, and
fabricates nothing. A byte nobody asked to send is worse on a shared bus than
a short transfer. `SMBUS_STATUS.bus_error` is set; the abort runs through the
error state and a STOP.

**RX overrun** (a block read longer than the free space in the RX FIFO): the
master checks `rx_fifo_full` before storing each data byte, the last one
included. The first byte that does not fit is not stored, is NAKed, and ends
the transfer with `bus_error` and `error_int`; the RX FIFO holds exactly what
fit and `complete` stays 0. Checking after the store would be useless: a full
`fifo_sync` drops the write silently.

**Block-count clamp.** A slave-supplied block count of 0, or one larger than
the FIFO depth, is clamped to 1 and to the depth respectively. The
over-length test looks at the whole byte: a count of 0x40 has all-zero low
six bits, so testing a truncated field first would read 64 as 0.

**Three things empty the FIFOs**, and all three mean the same thing to both:
`presetn`/`smbus_resetn`, `SMBUS_CONTROL.soft_reset`, and
`SMBUS_CONTROL.fifo_reset`. The two strobes clear both FIFOs over the
strobe window, and nothing is accepted into them during that window. A
`fifo_reset` landing during an active receive discards the bytes received so
far, including one landing in the clear window; the transfer itself still
completes or aborts normally.

**Levels and flags are consistent at every cycle by construction:**
`tx_level`/`rx_level` and the empty/full flags are derived from the same
counter, so software never sees a level that disagrees with its flag. The
level range is 0..`FIFO_DEPTH`, not 0..32.

**An `SMBUS_RX_FIFO` read with the FIFO empty returns the stale head byte,
not 0.** Read the level or `rx_empty` before popping.

---

## Programming Sequences

Common setup, once:

1. `SMBUS_CLK_DIV` and `SMBUS_TIMEOUT` (0 disables the timeout).
2. `SMBUS_CONTROL`: set `master_en`, and `pec_en` / `fast_mode` if wanted.
   `start` is ignored unless `master_en` is already set, so this write must
   precede the command.
3. `SMBUS_INT_ENABLE` if interrupts are wanted; otherwise poll.

Per transaction, then wait for `SMBUS_STATUS.busy` to fall (or `complete_int`
/ `error_int`) and read the error bits together with `complete`:

| Transaction | Before `start` | `SMBUS_COMMAND` | After `busy` falls |
|-------------|----------------|-----------------|--------------------|
| Quick Command (0) | `SMBUS_SLAVE_ADDR` | `trans_type=0`, `start` | check `nak_received` |
| Send Byte (1) | `SMBUS_SLAVE_ADDR`, `SMBUS_DATA` | `trans_type=1`, `start` | - |
| Receive Byte (2) | `SMBUS_SLAVE_ADDR` | `trans_type=2`, `start` | read `SMBUS_DATA` (or pop `SMBUS_RX_FIFO`) |
| Write Byte (3) | `SMBUS_SLAVE_ADDR`, `SMBUS_DATA` | `trans_type=3`, `cmd_code`, `start` | - |
| Read Byte (4) | `SMBUS_SLAVE_ADDR` | `trans_type=4`, `cmd_code`, `start` | read `SMBUS_DATA` (or pop `SMBUS_RX_FIFO`) |
| Write Word (5) | `SMBUS_SLAVE_ADDR`; push low byte then high byte to `SMBUS_TX_FIFO` | `trans_type=5`, `cmd_code`, `start` | - |
| Read Word (6) | `SMBUS_SLAVE_ADDR` | `trans_type=6`, `cmd_code`, `start` | pop `SMBUS_RX_FIFO` twice: low byte, then high byte |
| Block Write (7) | `SMBUS_SLAVE_ADDR`; push N bytes to `SMBUS_TX_FIFO`; `SMBUS_BLOCK_COUNT=N` | `trans_type=7`, `cmd_code`, `start` | - |
| Block Read (8) | `SMBUS_SLAVE_ADDR` | `trans_type=8`, `cmd_code`, `start` | read `SMBUS_BLOCK_COUNT` for the (clamped) count, then pop that many bytes from `SMBUS_RX_FIFO` |
| Block Process Call (9) | as Block Write | `trans_type=9`, `cmd_code`, `start` | as Block Read; `SMBUS_BLOCK_COUNT` now holds the slave's count |

With `pec_en` set, hardware appends the PEC on writes and checks it on reads;
`SMBUS_PEC` holds the transmitted or compared value afterwards and
`pec_error` reports a mismatch. Nothing extra is programmed.

**Recovering from an error.** Nothing is required: every error path issues a
STOP (bus recovery first if SDA is stuck), releases both lines and returns to
idle by itself. Read the error bits together (the truth table under
SMBUS_STATUS says whether a STOP reached the wire), drain or `fifo_reset` the
FIFOs as needed, and start the next transaction. Allow up to five
`SMBUS_TIMEOUT` windows for `busy` to fall after a wedged SCL. `SMBUS_COMMAND.stop` written alone
aborts a transaction that software no longer wants; `soft_reset` restarts the
engine without touching the register file if something else has gone wrong.

**Interrupt service.** Read `SMBUS_INT_STATUS`, act, then write 1 to the bits
handled. The pin deasserts (one or a few `pclk` later, per `CDC_ENABLE`) once
no enabled bit remains set; an event that arrives in the same cycle as the
clear is kept.

---

## Remaining limitations

- A `start` written while `master_en` is clear is silently discarded and not
  reported.
- Block Process Call shares `SMBUS_BLOCK_COUNT` between its two halves.
- SMBALERT# and Host Notify are not implemented, and with them the Alert
  Response Address a target would answer.
- ARP is not implemented; `SMBUS_OWN_ADDR` is a fixed address software
  programs.
- No reset synchronizer is instantiated; `presetn` / `smbus_resetn` must
  arrive already synchronized (asynchronous assert, synchronous deassert).

## History

The byte engine (command, data and PEC bytes after the address; the repeated
START on every read with a command code), SCL generation reaching the pin
open-drain, clock stretching, the SCL-low timeout with 0 = disabled and bus
recovery, the sticky W1C interrupt status and the registered interrupt pin,
the hardware-write-on-result `SMBUS_DATA` / `SMBUS_PEC` / `SMBUS_BLOCK_COUNT`
fields, the TX FIFO push from write data, per-type data byte counts, PEC
generation and checking, `soft_reset` and `fast_mode`, and the strict decode
were all fixed on 2026-09-09 under GitHub issue #58.

---

## Navigation

**Back to:** [SMBus Specification Index](../smbus_mas_index.md)
