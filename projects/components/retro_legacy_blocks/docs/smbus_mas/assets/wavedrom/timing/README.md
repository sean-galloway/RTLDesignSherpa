# SMBus Timing Diagrams - WaveDrom JSON Files

## Overview

This directory contains WaveDrom timing diagrams for SMBus (System Management Bus) operational scenarios.

### Files

| File | Scenario | Description |
|------|----------|-------------|
| `smbus_byte_write.json` | Byte Write | START + address + W bit + slave ACK |
| `smbus_byte_read.json` | Byte Read | Slave drives data, master samples, ACK/NACK |
| `smbus_clock_stretch.json` | Clock Stretch | Slave holds SCL low when busy |
| `smbus_arbitration.json` | Arbitration | Multi-master arbitration via SDA comparison (protocol only; not implemented in this block, RLB-011) |
| `smbus_pec.json` | PEC | Packet Error Check CRC-8 calculation |
| `smbus_timeout_recovery.json` | Timeout + recovery | The measured timeout abort: slave stuck in its ACK, timeout expiry, three recovery clocks, STOP |

## Ports

Waveform captions are only useful if the signal names are real. These are,
from the external pins down to the core internals the traces refer to.

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA`, `s_apb_PSLVERR` - Data signals

### SMBus Pins (External)
Real ports on apb4_smbus: `smb_scl_i/o/t` and `smb_sda_i/o/t` (split
input/output/tristate-enable, 1=input). The PHY is open-drain by
construction: `smb_scl_o == smb_scl_t` and `smb_sda_o == smb_sda_t`, so the
block only ever drives a 0 and a 1 is always a release. There is no
`smbalert_n` pin. The `scl`/`sda` traces in the diagrams are the composed
wire view.

### SMBus Core (Internal)
Real signal names in the RTL:
- **Sequencer (smbus_core.sv):** `r_master_state` (the SMBUS_STATUS.fsm_state
  encoding), `r_bit_counter`, `r_byte_counter`, `r_bytes_total`,
  `r_shift_reg`, `r_tx_byte`, `r_ack_bit`, `r_busy`, `r_bus_error`,
  `r_timeout_error`, `r_pec_error`, `r_nak_received`, `r_complete`
- **PHY (smbus_bit_phy.sv):** `op`/`op_req`/`op_done` (the primitive
  interface), `abort_req`/`abort_recover`, `phy_timeout`, `recover_failed`,
  `sda_sync`. SCL and SDA are driven only from this module; the `busy`,
  `timeout_error` and `bus_error` traces in the recovery diagram are the
  SMBUS_STATUS bits.
- **PEC:** `pec_value` (the live running CRC in smbus_core, read by the DV
  suite) and `w_pec_out` (the smbus_pec output); the accumulator is cleared
  once at the START and fed the byte value at byte-complete time.
- **Interrupts:** `int_status` (the sticky bits in smbus_int_status) and
  `smb_interrupt` (registered, `(INT_STATUS & INT_ENABLE) != 0`).
(Names like scl_master/stretch_scl/pec_match/r_scl_gen from older captions do
not exist in the RTL.)

## Timing

The protocol formats the diagrams follow, and the timing budget they are drawn
against.

### Transaction Types
`S` = START, `Sr` = repeated START, `P` = STOP, `A` = ACK, `N` = NAK.
`[PEC]` is present only when `SMBUS_CONTROL.pec_en` is set.

| Code | Protocol | On the wire |
|------|----------|-------------|
| 0x0 | Quick Command | `S, Addr+W, A, P` |
| 0x1 | Send Byte | `S, Addr+W, A, Data, A, [PEC, A], P` |
| 0x2 | Receive Byte | `S, Addr+R, A, Data, N, [PEC, N], P` |
| 0x3 | Write Byte | `S, Addr+W, A, Cmd, A, Data, A, [PEC, A], P` |
| 0x4 | Read Byte | `S, Addr+W, A, Cmd, A, Sr, Addr+R, A, Data, N, [PEC, N], P` |
| 0x5 | Write Word | `S, Addr+W, A, Cmd, A, DataLo, A, DataHi, A, [PEC, A], P` |
| 0x6 | Read Word | `S, Addr+W, A, Cmd, A, Sr, Addr+R, A, DataLo, A, DataHi, N, [PEC, N], P` |
| 0x7 | Block Write | `S, Addr+W, A, Cmd, A, Count, A, Data x Count (A each), [PEC, A], P` |
| 0x8 | Block Read | `S, Addr+W, A, Cmd, A, Sr, Addr+R, A, Count, A, Data x Count (last N), [PEC, N], P` |
| 0x9 | Block Proc Call | Block Write then `Sr, Addr+R, A, Count, A, Data x Count (last N), [PEC, N], P` |

With PEC on a read, the last data byte is ACKed and the PEC byte is the one
NAKed. Quick Command is always write-direction.

### Timing Parameters

Achieved at the RDL default (`SMBUS_CLK_DIV = 249`, 100 MHz core clock),
against the SMBus 2.0 / I2C minimums. One SCL period is eight base units:
`(CLK_DIV+1)/2` clocks in standard mode, `(CLK_DIV+1)/8` in fast mode, both
rounded up.

| Parameter | Standard achieved | Min | Fast achieved | Min | Unit |
|-----------|-------------------|-----|---------------|-----|------|
| f_SCL | 100.0 | (max 100) | 390.6 | (max 400) | kHz |
| t_LOW | 5000 | 4700 | 1600 | 1300 | ns |
| t_HIGH | 5000 | 4000 | 960 | 600 | ns |
| t_HD:STA | 5000 | 4000 | 640 | 600 | ns |
| t_SU:STA | 5000 | 4700 | 640 | 600 | ns |
| t_SU:STO | 6250 | 4000 | 1600 | 600 | ns |
| t_BUF | 6250 | 4700 | 1600 | 1300 | ns |

Fast mode is asymmetric: the low phase is 5/8 of the period and the high
phase 3/8. Recovery clocks are full standard-mode bits (tLOW 5000 ns, tHIGH
5000 ns at the default divider) in both modes.

## Waveforms

What each scenario shows, and the mechanism behind it.

### 1. Byte Write
Shows START condition (SDA falling while SCL high, after the bus-free wait),
followed by 7-bit address and R/W bit (W=0 for write). Slave with matching
address responds with ACK by pulling SDA low during 9th clock.

### 2. Byte Read
Shows slave-to-master data transfer. Slave drives 8 data bits, master
samples each on SCL rising edge. Master sends ACK (SDA low) for more data, or
NACK (SDA high) for last byte.

### 3. Clock Stretching
Shows slave flow control mechanism. When slave needs processing time, it
holds SCL low after master releases it. The PHY holds its unit counter at
zero until the synchronized SCL input reads high, so the phase extends.
Transfer resumes when slave releases SCL; a stretch longer than
`SMBUS_TIMEOUT` is a timeout (diagram 6).

### 4. Multi-Master Arbitration
Shows collision resolution when two masters start simultaneously. Both
monitor SDA while transmitting. Master driving 1 but reading 0 (due to other
master's 0) loses arbitration and backs off. Wired-AND ensures 0 wins. This
block does not implement arbitration (`arb_lost` tied 0, RLB-011); the
diagram is the protocol mechanism.

### 5. Packet Error Check (PEC)
Shows CRC-8 error detection. PEC byte calculated over every byte on the wire,
both address bytes included, using polynomial x^8+x^2+x+1. Transmitted after
data on a write; received, NAKed and compared on a read. A mismatch sets
`SMBUS_STATUS.pec_error`.

### 6. Timeout Abort with Bus Recovery
The measured sequence from `rtl/smbus/README.md` (slave stuck in its ACK
after a 15 us stretch, `SMBUS_TIMEOUT` = 5 us): START at 0.965 us; timeout
expiry at ~5 us, where the PHY abandons the ACK bit and releases both lines;
recovery clocks at 17.805, 17.945 and 18.085 us, SDA reading high at the end
of the third; STOP setup at 18.225 us; STOP at 18.345 us. Ends with `busy=0`,
`timeout_error=1`, `bus_error=0` and both lines released. Drawn to phase, not
to scale.

## Usage Example

Render the JSON files to SVG and PNG with wavedrom-cli and rsvg-convert:

```bash
for f in *.json; do
    wavedrom-cli -i "$f" -s "${f%.json}.svg"
    rsvg-convert -w 4960 --background-color=white "${f%.json}.svg" -o "${f%.json}.png"
done
```

## References

- **SMBus RTL:** `rtl/smbus/apb4_smbus.sv`, `rtl/smbus/smbus_core.sv`,
  `rtl/smbus/smbus_bit_phy.sv`; contracts in `rtl/smbus/README.md`
- **SMBus Testbench:** `dv/tbclasses/smbus/smbus_tb.py`
- **Constraint Class:** none yet for the SMBus (see
  `bin/TBClasses/wavedrom_user/hpet.py` and `apb.py` for examples); these
  diagrams are hand-written JSON
- **SMBus Spec:** System Management Bus (SMBus) Specification Version 2.0
