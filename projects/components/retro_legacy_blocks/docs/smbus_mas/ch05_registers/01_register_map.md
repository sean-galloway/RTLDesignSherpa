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

The register map below is generated from `rtl/smbus/peakrdl/smbus_regs.rdl` and matches
the decode in `rtl/smbus/smbus_regs.sv`. The register block decodes 6 address bits, so
only offsets 0x00-0x3F are valid; higher offsets alias back onto this range. Undefined
offsets read as 0, drop writes, and do not assert PSLVERR.

Access legend: RW = read/write, RO = read-only, WO = write-only, W1C = write-1-to-clear,
AC = self-clearing (hardware clears the bit after the action completes).

## Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x00 | SMBUS_CONTROL | RW | 0x00000000 | Global control (enable, mode, PEC, resets) |
| 0x04 | SMBUS_STATUS | RO | 0x00000000 | Status flags and FSM state |
| 0x08 | SMBUS_COMMAND | RW | 0x00000000 | Transaction type, command byte, start/stop |
| 0x0C | SMBUS_SLAVE_ADDR | RW | 0x00000000 | Target slave address (master mode) |
| 0x10 | SMBUS_DATA | RW | 0x00000000 | Single data byte |
| 0x14 | SMBUS_TX_FIFO | WO | 0x00000000 | Transmit FIFO write port |
| 0x18 | SMBUS_RX_FIFO | RO | - | Receive FIFO read port (read pops) |
| 0x1C | SMBUS_FIFO_STATUS | RO | 0x00008080 (live) | TX/RX FIFO levels and flags (post-reset both FIFOs empty: tx_empty bit 7, rx_empty bit 15) |
| 0x20 | SMBUS_CLK_DIV | RW | 0x000000F9 | SCL clock divider |
| 0x24 | SMBUS_TIMEOUT | RW | 0x002625A0 | Timeout threshold (clocks) |
| 0x28 | SMBUS_OWN_ADDR | RW | 0x00000000 | Own slave address (slave mode) |
| 0x2C | SMBUS_INT_ENABLE | RW | 0x00000000 | Interrupt enable mask |
| 0x30 | SMBUS_INT_STATUS | W1C | 0x00000004 (live) | Interrupt status -- non-functional, see its section (#58); reads 0x4 post-reset because tx-empty is mirrored live |
| 0x34 | SMBUS_PEC | RW | 0x00000000 | PEC value (CRC-8) |
| 0x38 | SMBUS_BLOCK_COUNT | RW | 0x00000000 | Block transfer byte count |

---

## SMBUS_CONTROL (0x00)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | master_en | RW | 0 | Enable master mode |
| 1 | slave_en | RW | 0 | Enable slave mode |
| 2 | pec_en | RW | 0 | Enable Packet Error Checking |
| 3 | fast_mode | RW | 0 | Clock speed select: 0=standard, 1=fast |
| 4 | fifo_reset | RW/AC | 0 | Reset TX/RX FIFOs (write 1, auto-clears) |
| 5 | soft_reset | RW/AC | 0 | Soft reset controller (write 1, auto-clears) |
| 31:6 | Reserved | RO | 0 | Reads 0 |

Note: `soft_reset` and `fast_mode` are accepted by the register block but are not currently
consumed by `smbus_core` (soft reset resets nothing; SCL frequency depends solely on
`clk_div`). See Implementation Limitations below.

---

## SMBUS_STATUS (0x04)

Read-only. Software writes to this register are dropped (no PSLVERR).
SMBUS_INT_STATUS (0x30) is nominally the sticky, clearable flag set -- but
see its section: in the current RTL it is NOT sticky (#58).

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | busy | RO | Transaction in progress |
| 1 | bus_error | RO | Bus error detected (e.g. NAK). Live level of the M_ERROR state -- self-clears when the FSM leaves it; polling can miss it |
| 2 | timeout_error | RO | Transaction timeout (see limitation below) |
| 3 | pec_error | RO | PEC mismatch (see limitation below) |
| 4 | arb_lost | RO | Multi-master arbitration lost (see limitation below) |
| 5 | nak_received | RO | NAK received from slave. Transient level covering only the address/command ACK phases -- data/PEC-phase NAKs do not set it, and it self-clears as the FSM advances |
| 6 | slave_addressed | RO | Addressed as slave (see limitation below) |
| 7 | complete | RO | Transaction completed |
| 11:8 | fsm_state | RO | Current FSM state (debug) |
| 31:12 | Reserved | RO | Reads 0 |

---

## SMBUS_COMMAND (0x08)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 3:0 | trans_type | RW | 0 | Transaction type (see Transaction Types) |
| 7:4 | Reserved | RO | 0 | Reads 0 |
| 15:8 | cmd_code | RW | 0 | SMBus command byte |
| 16 | start | RW/AC | 0 | Start transaction (write 1, auto-clears) |
| 17 | stop | RW/AC | 0 | Force stop/abort transaction (write 1, auto-clears) |
| 31:18 | Reserved | RO | 0 | Reads 0 |

### Transaction Types

`trans_type` is a 4-bit field. Block Write and Block Read are separate encodings.

| trans_type | Description |
|------------|-------------|
| 0 | Quick Command |
| 1 | Send Byte |
| 2 | Receive Byte |
| 3 | Write Byte |
| 4 | Read Byte |
| 5 | Write Word |
| 6 | Read Word |
| 7 | Block Write |
| 8 | Block Read |
| 9 | Block Write-Block Read Process Call |

---

## SMBUS_SLAVE_ADDR (0x0C)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 6:0 | slave_addr | RW | 0 | 7-bit target slave address |
| 31:7 | Reserved | RO | 0 | Reads 0 |

The transfer direction (R/W) is derived from `trans_type`, not from an address bit. There
is no writable R/W bit at bit 7; writes to bit 7 are ignored and it reads back 0.

---

## SMBUS_DATA (0x10)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 7:0 | data | RW | 0 | Single data byte for Send/Receive/Write/Read Byte-Word. NON-FUNCTIONAL as a command staging register (#58): the field is reloaded from the core shift register every non-write cycle, so a software-written byte survives exactly one clock -- write-then-read returns live core data, and the staged TX byte can never actually be programmed |
| 31:8 | Reserved | RO | 0 | Reads 0 |

---

## SMBUS_TX_FIFO (0x14)

Write-only port into the 32-byte transmit FIFO. Each write pushes one byte. Reads return 0.

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 7:0 | tx_data | WO | 0 | Byte pushed into the TX FIFO |
| 31:8 | Reserved | RO | 0 | Reads 0 |

---

## SMBUS_RX_FIFO (0x18)

Read-only port from the 32-byte receive FIFO. Each read pops one byte.

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 7:0 | rx_data | RO | Byte popped from the RX FIFO |
| 31:8 | Reserved | RO | Reads 0 |

---

## SMBUS_FIFO_STATUS (0x1C)

Read-only FIFO level and flag register.

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 5:0 | tx_level | RO | TX FIFO occupancy (0-32) |
| 6 | tx_full | RO | TX FIFO full |
| 7 | tx_empty | RO | TX FIFO empty |
| 13:8 | rx_level | RO | RX FIFO occupancy (0-32) |
| 14 | rx_full | RO | RX FIFO full |
| 15 | rx_empty | RO | RX FIFO empty |
| 31:16 | Reserved | RO | Reads 0 |

---

## SMBUS_CLK_DIV (0x20)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 15:0 | clk_div | RW | 0x00F9 (249) | SCL clock divider |
| 31:16 | Reserved | RO | 0 | Reads 0 |

SCL toggles every `clk_div + 1` system-clock cycles, so
f_SCL = f_clk / (2 * (clk_div + 1)). The reset value of 249 yields 100 kHz at f_clk = 50 MHz
(200 kHz at f_clk = 100 MHz).

---

## SMBUS_TIMEOUT (0x24)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 23:0 | timeout | RW | 0x2625A0 (2,500,000) | Timeout threshold in system-clock cycles |
| 31:24 | Reserved | RO | 0 | Reads 0 |

The reset value corresponds to ~25 ms at f_clk = 100 MHz. See Implementation
Limitations below: the timeout counter's enable (r_timeout_en) is UNDRIVEN,
so the counter never counts and, at any nonzero threshold, timeout_error
never sets. EXCEPTION: writing SMBUS_TIMEOUT = 0 makes the comparison
(0 >= 0) permanently true and wedges the master FSM in M_ERROR with
timeout_error set -- do not program 0 (#58).

---

## SMBUS_OWN_ADDR (0x28)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 6:0 | own_addr | RW | 0 | 7-bit own slave address |
| 7 | addr_en | RW | 0 | Enable own-address matching (slave mode) |
| 31:8 | Reserved | RO | 0 | Reads 0 |

---

## SMBUS_INT_ENABLE (0x2C)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | complete_en | RW | 0 | Interrupt on transaction complete |
| 1 | error_en | RW | 0 | Interrupt on bus error |
| 2 | tx_thresh_en | RW | 0 | Interrupt while TX FIFO is EMPTY (no programmable threshold exists) |
| 3 | rx_thresh_en | RW | 0 | Interrupt while RX FIFO is NON-EMPTY (no programmable threshold exists) |
| 4 | slave_addr_en | RW | 0 | Interrupt when addressed as slave |
| 31:5 | Reserved | RO | 0 | Reads 0 |

---

## SMBUS_INT_STATUS (0x30)

Nominally W1C, but NON-FUNCTIONAL as an interrupt-status register in the
current RTL (#58): every bit is reloaded from hardware each cycle, so
complete_int/error_int are one-cycle self-clearing pulses (polling will
routinely miss them), the 'threshold' bits just mirror live FIFO flags,
and a W1C write has no lasting effect. The smb_interrupt pin is driven
from RAW status ORs and never consumes this register, so clearing it
cannot deassert the pin.

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | complete_int | W1C | 0 | Transaction completed |
| 1 | error_int | W1C | 0 | Bus error occurred |
| 2 | tx_thresh_int | W1C | 0 | Mirrors TX-FIFO-empty (live level, not latched) |
| 3 | rx_thresh_int | W1C | 0 | Mirrors RX-FIFO-non-empty (live level, not latched) |
| 4 | slave_addr_int | W1C | 0 | Device addressed as slave |
| 31:5 | Reserved | RO | 0 | Reads 0 |

---

## SMBUS_PEC (0x34)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 7:0 | pec | RW | 0 | Current/expected PEC value (CRC-8, polynomial 0x07). Same clobber defect as SMBUS_DATA (#58): reloaded from the CRC accumulator every non-write cycle (held 0 by the near-permanent PEC clear), so an expected-PEC value cannot be programmed |
| 31:8 | Reserved | RO | 0 | Reads 0 |

---

## SMBUS_BLOCK_COUNT (0x38)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 5:0 | block_count | RW | 0 | Byte count for block transfers. SMBus-legal range is 1-32, but the field accepts 0-63 with no range check |
| 31:6 | Reserved | RO | 0 | Reads 0 |

Note: `block_count` describes the INTENDED byte accounting; in the current
RTL the byte-transfer engine never leaves the address phase (the ACK
handler pre-marks the bit counter complete, so command/data/PEC bytes are
never bit-banged and the block-write FIFO load is unreachable -- #58), so
no multi-byte semantics are reachable on the wire. Also note r_bytes_total
is loaded from block_count for ALL transaction types, not just block
transfers -- at the reset value 0, Write/Read Word degenerate to one data
byte. The SMBus count byte is not placed on / consumed from the wire.

---

## Implementation Limitations

The register interface above matches the RTL, but several protocol features implied by these
registers are not fully realized in the current `smbus_core` logic. These are noted so the
register map does not promise behavior the hardware does not yet deliver:

- **Timeout detection is inactive.** The timeout counter enable is never driven, so
  SMBUS_TIMEOUT has no effect and `SMBUS_STATUS.timeout_error` cannot set.
- **SCL is not toggled during a transfer and is driven push-pull.** The generated SCL clock
  is not connected to the pin during bit phases, and the master does not use open-drain
  signaling, so clock stretching and multi-master arbitration are not supported.
- **PEC is not functional.** PEC generation does not accumulate valid transmitted data and
  received PEC is never compared, so `SMBUS_STATUS.pec_error` cannot set.
- **Hardwired status bits.** `arb_lost`, `pec_error`, and `slave_addressed` in SMBUS_STATUS
  are tied to 0. Slave mode (SMBUS_OWN_ADDR, `slave_addr_int`) is a stub and does not ACK,
  receive, or transmit.
- **Dead control bits.** `SMBUS_CONTROL.soft_reset` and `SMBUS_CONTROL.fast_mode` are
  accepted but not acted upon by the core.

For the authoritative, tracked status of these items see
`rtl/smbus/IMPLEMENTATION_STATUS.md` and `rtl/smbus/TODO.md`.

---

**Back to:** [SMBus Specification Index](../smbus_mas_index.md)
