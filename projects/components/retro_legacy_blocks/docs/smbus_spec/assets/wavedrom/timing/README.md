# SMBus Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for SMBus (System Management Bus) operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `smbus_byte_write.json` | Byte Write | START + address + W bit + slave ACK |
| `smbus_byte_read.json` | Byte Read | Slave drives data, master samples, ACK/NACK |
| `smbus_clock_stretch.json` | Clock Stretch | Slave holds SCL low when busy |
| `smbus_arbitration.json` | Arbitration | Multi-master arbitration via SDA comparison |
| `smbus_pec.json` | PEC | Packet Error Check CRC-8 calculation |

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### SMBus Pins (External)
- `scl` - Serial clock (open-drain, active low)
- `sda` - Serial data (open-drain, bidirectional)
- `smbalert_n` - SMBus alert (optional)

### SMBus Core (Internal)
- **State Machine:** `r_state`, `r_bit_count`, `start_cond`, `stop_cond`
- **TX Path:** `r_shift_reg`, `sda_out`, `tx_data_valid`
- **RX Path:** `r_rx_data`, `rx_data_valid`, `r_shift_reg`
- **Clock:** `scl_master`, `scl_slave`, `stretch_scl`, `wait_scl_high`
- **Arbitration:** `sda_a_out`, `sda_b_out`, `arb_lost`
- **PEC:** `pec_enable`, `r_pec_accum`, `pec_match`, `pec_error`

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Scenarios Explained

### 1. Byte Write
Shows START condition (SDA falling while SCL high), followed by 7-bit address and R/W bit (W=0 for write). Slave with matching address responds with ACK by pulling SDA low during 9th clock.

### 2. Byte Read
Shows slave-to-master data transfer. Slave drives 8 data bits, master samples each on SCL rising edge. Master sends ACK (SDA low) for more data, or NACK (SDA high) for last byte.

### 3. Clock Stretching
Shows slave flow control mechanism. When slave needs processing time, it holds SCL low after master releases it. Master detects stretched clock and waits. Transfer resumes when slave releases SCL.

### 4. Multi-Master Arbitration
Shows collision resolution when two masters start simultaneously. Both monitor SDA while transmitting. Master driving 1 but reading 0 (due to other master's 0) loses arbitration and backs off. Wired-AND ensures 0 wins.

### 5. Packet Error Check (PEC)
Shows CRC-8 error detection. PEC byte calculated over address, command, and data bytes using polynomial x^8+x^2+x+1. Transmitted after data, verified by receiver. Detects bit errors in transfer.

## SMBus Protocol Reference

### Transaction Types
| Protocol | Format |
|----------|--------|
| Quick Command | S + Addr + R/W + A + P |
| Send Byte | S + Addr + W + A + Data + A + P |
| Receive Byte | S + Addr + R + A + Data + N + P |
| Write Byte | S + Addr + W + A + Cmd + A + Data + A + P |
| Read Byte | S + Addr + W + A + Cmd + A + Sr + Addr + R + A + Data + N + P |
| Write Word | S + Addr + W + A + Cmd + A + DataL + A + DataH + A + P |
| Read Word | S + Addr + W + A + Cmd + A + Sr + Addr + R + A + DataL + A + DataH + N + P |
| Block Write | S + Addr + W + A + Cmd + A + Count + A + Data[0..N] + P |
| Block Read | S + Addr + W + A + Cmd + A + Sr + Addr + R + A + Count + A + Data[0..N] + P |

Legend: S=Start, Sr=Repeated Start, A=ACK, N=NACK, P=Stop

### Timing Parameters (100 kHz Standard Mode)
| Parameter | Min | Max | Unit |
|-----------|-----|-----|------|
| f_SCL | - | 100 | kHz |
| t_HD:STA | 4.0 | - | us |
| t_LOW | 4.7 | - | us |
| t_HIGH | 4.0 | - | us |
| t_SU:STA | 4.7 | - | us |
| t_HD:DAT | 0 | - | us |
| t_SU:DAT | 250 | - | ns |
| t_SU:STO | 4.0 | - | us |

## References

- **SMBus RTL:** `rtl/smbus/apb_smbus.sv`
- **SMBus Testbench:** `dv/tbclasses/smbus/smbus_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/smbus.py`
- **SMBus Spec:** System Management Bus (SMBus) Specification Version 3.0
