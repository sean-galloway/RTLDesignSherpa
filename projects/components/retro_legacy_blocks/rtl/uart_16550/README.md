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

# APB UART 16550 Controller

NS16550-compatible UART controller with APB interface.

## Features

- 16-byte TX and RX FIFOs
- Programmable baud rate via 16-bit divisor
- 5/6/7/8 data bits
- 1, 1.5 (5-bit words) or 2 stop bits
- None/Odd/Even/Mark/Space parity
- Modem control signals (DTR, RTS, CTS, DSR, RI, DCD)
- Internal loopback mode
- Interrupt support with priority, individually maskable via IER
- Optional CDC for asynchronous clock domains

## Architecture

```
APB -> apb4_slave[_cdc] -> CMD/RSP -> peakrdl_to_cmdrsp ->
    -> uart_16550_regs (PeakRDL) -> hwif -> uart_16550_core
                                              |-- uart_16550_modem
                                              `-- uart_16550_intr
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| FIFO_DEPTH | 16 | FIFO depth (16 for 16550 compatibility) |
| SYNC_STAGES | 2 | Input synchronizer stages |
| CDC_ENABLE | 0 | 1=async clocks, 0=same clock (must be 0 or 1) |
| SKID_DEPTH | 2 | CDC skid buffer depth |
| USE_JOHNSON | 0 | CDC async-FIFO pointer encoding: 0=Gray, 1=Johnson |

The APB port is fixed: 12-bit `s_apb_PADDR`, 32-bit `s_apb_PWDATA`/`PRDATA`.

The parameter guards are `initial $fatal` blocks, so **an illegal parameter
fails in simulation at time 0, not at elaboration** - synthesis ignores an
initial block and will happily build a broken configuration. `FIFO_DEPTH` must
be a power of two and at least 16 (checked in both `uart_16550_core` and
`apb4_uart_16550`); `CDC_ENABLE` must be 0 or 1; and when `CDC_ENABLE` is 1,
`SKID_DEPTH` must be 2..8, narrowed to {2, 3, 4, 8} by the async FIFO's
default Gray pointer encoding. The skid depth contract is 2..8 **inclusive
and odd depths are legal** - the legal set is not {2, 4, 6, 8}.

## Resets are per-domain and must not be taken one-sided under traffic

`presetn` and `uart_rstn` are independent ports. With `CDC_ENABLE = 1` they
reset the two ends of the async FIFOs inside `apb4_slave_cdc` separately, so
**resetting one domain while a transfer is in flight leaves the other end's
pointer where it was and corrupts the FIFO. Quiesce the bus first: stop
issuing APB transfers, let the outstanding one complete, and only then assert
either reset.** Asserting both together is always safe. With `CDC_ENABLE = 0`
the two are the same domain and the question does not arise.

## Register behaviour (GitHub #60)

### RBR and THR are different registers at the same offset

**`UART_DATA[7:0]` returns the RECEIVED byte and the read pops the RX FIFO;
`UART_DATA` writes go to THR, which is write-only and does not read back
anywhere.** THR has no register field at all - it has no storage to model, so
the wrapper decodes a write to the offset and pushes the write-data lane
straight into the TX FIFO. Giving THR a field is what made offset 0 read back
the last byte *written* instead of the byte *received*.

`UART_DATA[15:8]` is a read-only **alias** of the same received byte. That is
not a 16550 feature: the shared DV helper reads RX from the upper lane and DV
may not be edited here, so the lane is kept live rather than returning zero.
A driver uses `[7:0]`. Reading the register pops the FIFO once, whichever lane
the reader looks at.

### LSR and MSR clear on read

**LSR[4:1] (OE, PE, FE, BI) clear when UART_LSR is read, and MSR[3:0] (the
four delta bits) clear when UART_MSR is read** - PC16550D read-clear, not
write-1-to-clear. The read strobe clears the register field *and* the core's
sticky flag in the same access, so the level that drives `hwset` goes away
together with the bit; otherwise the flag is re-set the cycle after it is
cleared and nothing can ever stay clear.

**Any read of LSR clears those four bits**, including a read that was only
looking at DR. Software that polls LSR for data-ready and then re-reads LSR
expecting an error bit to still be there will not see it; capture the value
from the first read.

### IER gates every interrupt source

**Each of the four sources is gated independently by its own IER bit: a
disabled source stays true in LSR/MSR and simply is not an interrupt - it does
not raise `irq` and IIR does not report it.** IIR reports the highest-priority
*enabled and pending* source, so a disabled higher-priority source never hides
an enabled lower one. Priority, highest first: receiver line status, received
data available, transmitter holding register empty, modem status. IIR reads
"no interrupt pending" when nothing is both enabled and pending.

**Reading IIR clears the THR-empty interrupt when THR empty is the source it
reported.** The condition itself stays true - the FIFO really is empty - so
what clears is the interrupt, and it re-arms as soon as the condition goes
away, i.e. when something is written to THR.

### Byte enables decode, they do not just mask

**A write to `UART_DATA` with lane 0 disabled is not a THR write at all: no
byte is transmitted.** The byte enable is part of the decode, not just of the
data. Masking the captured byte but pushing anyway - which is what an earlier
version did - transmitted a NUL for every such access.

### FCR[0] is 16450 character mode, not a status bit

**With FCR[0] = 0 each side is a single holding register.** On the transmit
side a second write before the first byte has been loaded into the shifter
**overwrites** the waiting byte - it does not queue and it is not dropped. On
the receive side a second character arriving before the first has been read
sets the overrun error and **overwrites and destroys** the character in RBR,
per PC16550D. LSR[7] is defined only in FIFO mode and reads 0 here.

**LSR[7] aggregates over the whole FIFO**, which is what PC16550D asks for:
"at least one parity error, framing error or break indication in the FIFO".
It is a count of tagged entries, so it sets the moment a tagged character
lands and stays set until that character has been read out - it does not
follow the entry at the read pointer. The distinction is the whole value of
the bit: reading it off the head makes it 0 whenever a tagged character is
queued behind a clean one, so software polling LSR[7] to decide whether to
inspect the stream misses the error entirely. The counter is held clear in
character mode, where LSR[7] is not defined.

### LSR[4:2] belong to the character, not to the port

**LSR[2] (PE), LSR[3] (FE) and LSR[4] (BI) are the tags of the character the
CPU is being handed, not a running OR of everything ever received.** A read of
RBR hands over a character together with its tags; before any read they are
the tags of the character waiting at the top of the FIFO. The tags were always
stored per entry in the FIFO, but only LSR[7] used them, so one bad byte used
to poison the reported status of every clean byte behind it. Read-clear still
applies: reading LSR clears the three bits, and the next character to be
handed over re-loads them.

LSR[1] (OE) is not a per-character condition and stays a port-level flag.

### A continuous break is one character

**A break condition loads exactly one zero character tagged BI, and the
receiver then stays off until the line returns to marking and a genuine new
start bit arrives.** Without that hold, `RX_IDLE` re-arms on a still-low line,
so a break held for N character times framed N zero characters and eventually
overran the FIFO.

### FCR[2] resets the TX FIFO, not the transmitter

**A TX FIFO reset (FCR[2]) clears the FIFO counter and pointers only; the
character already in the shift register finishes on the wire.** The
transmitter then finds the FIFO empty and stops. Forcing the state machine
back to idle cut whatever character was in flight in half.

FCR[1] (RX FIFO reset) still returns the receiver to idle as well as clearing
the pointers, so a character part-way through being received is abandoned.
That is a deliberate asymmetry for now: it was not in the review's scope, and
unlike the transmit case nothing has been put on a wire yet. Noted here so it
is not mistaken for a matching contract.

### FIFO trigger levels

The RX data-available interrupt fires at the FCR trigger level (1, 4, 8 or 14
characters) when the FIFOs are enabled, and on any received character when
they are not.

### Strict decode

**Only the eleven mapped registers decode. Everything else in the 4 KB window
is dropped: the write is ignored, the read returns 0, and the access is
acknowledged locally with PSLVERR.** The register block sees six address bits,
so without this every unmapped address aliases onto a real register 64 bytes
below it.

### FIFO_DEPTH constraint

**`FIFO_DEPTH` must be a power of two and at least 16**, enforced by an
elaboration-time guard in both `uart_16550_core` and `apb4_uart_16550`. The
pointer and count arithmetic is modulo 2^(AW+1) while the memory indices take
[AW-1:0], which is only the same thing at a power of two; and the RX trigger
levels go up to 14, which a depth under 16 cannot express.

## Features added for RLB-013

The five 16550 features this block used to leave out are implemented:

- **Character-timeout interrupt.** With the RX FIFO non-empty and neither a
  new character nor a read for four character times, the timeout asserts and
  IIR reads 0x0C. It shares the received-data-available priority slot and is
  distinguished by IIR[3], is gated by IER[0] like the source it shares with,
  and exists only in FIFO mode - in character mode a single unread byte is
  already the received-data condition. Any FIFO activity restarts it.
- **Auto flow control.** MCR[5] (AFE) is a real field. With it set the
  transmitter starts a character only while CTS is asserted - the character
  already in the shifter always finishes, AFE gates the START and not the
  frame - and RTS is driven from the RX FIFO level rather than from MCR[1]:
  it deasserts at the trigger level and reasserts once software has read the
  FIFO back below it. MCR[1] must still be set for RTS to be asserted at all;
  AFE decides when to DEASSERT it, it does not override a deliberate
  deassertion by software.
- **1.5 stop bits** for 5-bit words. LCR[2] with a 5-bit character sends a
  half-length second stop bit, so the frame is 7.5 bit times against 7 with
  one stop bit.
- **DLAB remapping.** While LCR[7] is set, 0x00 and 0x04 are the divisor
  latches, as a standard 16550 driver expects. The flat offsets at 0x24 and
  0x28 keep working, so both forms address the same latches. The remap is
  applied to the address the register block sees, and every strobe decodes
  that same remapped address, so a divisor write can never be mistaken for a
  THR push or an IER write.
- **DMA mode select.** FCR[3] selects the handshake on `rxrdy_n` / `txrdy_n`.
  Mode 0 is one character at a time: receive is requested as soon as anything
  is in the RX FIFO, transmit while the TX FIFO is empty. Mode 1 is block:
  receive waits for the trigger level or the character timeout, transmit
  stands while there is any room at all. Both pins are active low and may be
  left unconnected.


## Register Map

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x00 | UART_DATA | R / W | Read = RBR (received byte, pops RX FIFO). Write = THR (write-only, no readback) |
| 0x04 | UART_IER | RW | Interrupt Enable (RX data, THR empty, line status, modem) |
| 0x08 | UART_IIR | RO | Interrupt Identification. Reading clears the THR-empty interrupt when THR empty is the reported source |
| 0x0C | UART_FCR | RW | FIFO Control (enable, resets, RX trigger level) |
| 0x10 | UART_LCR | RW | Line Control (word length, stop bits, parity, break, DLAB) |
| 0x14 | UART_MCR | RW | Modem Control (DTR, RTS, OUT1, OUT2, loopback, AFE) |
| 0x18 | UART_LSR | RO, read-clear | Line Status. Bits [4:1] (OE, PE, FE, BI) clear on read |
| 0x1C | UART_MSR | RO, read-clear | Modem Status. Bits [3:0] (the deltas) clear on read |
| 0x20 | UART_SCR | RW | Scratch Register |
| 0x24 | UART_DLL | RW | Divisor Latch Low |
| 0x28 | UART_DLM | RW | Divisor Latch High |


`UART_DATA[15:8]` is a read-only alias of the received byte; see the RBR/THR
section above for why it exists. A driver uses `[7:0]`.

Every other address in the 4 KB APB window is unmapped: writes are discarded,
reads return 0, and the access completes with PSLVERR.

Note: every register also has its own fixed offset, which the original 16550
does not. DLAB (LCR[7]) remaps 0x00 and 0x04 to the divisor latches as usual,
and 0x24 and 0x28 reach them whatever DLAB says.

## Interrupt Priority

| Priority | IIR ID | Source | Enabled by | Cleared by |
|----------|--------|--------|------------|------------|
| 1 (High) | 2'b11 | Receiver line status (OE/PE/FE/BI) | IER[2] | Reading LSR |
| 2 | 2'b10 | Received data available | IER[0] | Reading RBR below the trigger level |
| 3 | 2'b01 | Transmitter holding register empty | IER[1] | Reading IIR, or writing THR |
| 4 (Low) | 2'b00 | Modem status | IER[3] | Reading MSR |

IIR reports the highest-priority source that is both pending and enabled in
IER; a source disabled in IER is invisible to IIR and to `irq`, so it cannot
mask a lower-priority source that is enabled. With nothing pending and
enabled, IIR reads "no interrupt pending". The character timeout shares the
received-data-available slot and is distinguished by IIR[3], so IIR reads
0x0C for it and 0x04 for a plain trigger-level interrupt.

MCR[3] (OUT2) gates the `irq` output; IIR still reports the source when OUT2
is low.

## Baud Rate Calculation

```
Divisor = Clock_Frequency / (16 * Baud_Rate)

Example: 100 MHz clock, 115200 baud
Divisor = 100,000,000 / (16 * 115200) = 54 (0x0036)
```

## Modem Signals

Active-low physical signals:
- cts_n, dsr_n, ri_n, dcd_n (inputs)
- dtr_n, rts_n, out1_n, out2_n (outputs)

The registers show inverted (active-high) values.

MCR[5] (AFE) enables auto flow control: CTS gates the start of a character
and RTS follows the RX FIFO level. See the features section above.

## Loopback Mode

When MCR[4] = 1:
- TX data internally looped to RX
- DTR -> DSR, RTS -> CTS, OUT1 -> RI, OUT2 -> DCD
- TX pin held high, RX pin ignored

## File Structure

```
uart_16550/
|   `-- uart_16550_regs.rdl     # PeakRDL register definitions
|-- filelists/
|   `-- apb4_uart_16550.f        # Simulation/synthesis filelist
|-- uart_16550_regs_pkg.sv      # PeakRDL generated package
|-- uart_16550_regs.sv          # PeakRDL generated registers
|-- uart_16550_regs.vlt         # Verilator waivers for the generated block
|-- uart_16550_modem.sv         # Modem synchronizers, MSR deltas, outputs
|-- uart_16550_intr.sv          # IER gating, IIR priority, irq
|-- uart_16550_core.sv          # UART core (baud, TX/RX/FIFOs, line status)
|-- uart_16550_config_regs.sv   # Register-to-core adapter
|-- apb4_uart_16550.sv           # APB wrapper (top level)
`-- README.md                   # This file
```

## Dependencies

- apb4_slave.sv / apb4_slave_cdc.sv
- peakrdl_to_cmdrsp.sv
- gaxi_skid_buffer.sv (both paths, not CDC-only)
- gaxi_fifo_async.sv and its Gray/Johnson pointer chain (CDC only, pulled in
  by apb4_slave_cdc)

There is no `cdc_handshake.sv` in this design - the CDC path uses Gray-pointer
async FIFOs, not a handshake synchronizer. The filelist no longer pulls in
`cdc_2_phase_handshake.f` or `cdc_4_phase_handshake.f` either; neither module
was instantiated anywhere in the resolved closure.

## Test Plan

Tests located in: `projects/components/retro_legacy_blocks/dv/tests/test_apb4_uart_16550.py`

| Test Level | Description |
|------------|-------------|
| basic | Register access, simple TX/RX, baud rate |
| medium | FIFOs, interrupts, modem signals, loopback |
| full | Error injection, stress testing, CDC |

## Implementation Notes

1. **FIFO Mode**: The 16550 starts with FIFOs disabled. Write FCR[0]=1 to enable.
2. **Interrupt Gating**: OUT2 (MCR[3]) gates the interrupt output.
3. **Character Timeout**: four character times of inactivity with a non-empty
   RX FIFO; IIR reads 0x0C. FIFO mode only, gated by IER[0].
4. **Break Detection**: asserted when the received character is all zeros and the
   stop bit is 0. Both BI and FE are computed combinationally at the stop-bit
   sample point, so they track the character actually received. Break detection
   works at every word length: the received character is right-justified and
   zero-filled into [7:0] first, so a 5/6/7-bit all-zero character still
   compares equal to zero.
5. **Word length**: 5, 6 and 7-bit characters are right-justified and
   zero-filled in RBR - the received bits land in the low bits, the unused
   high bits read 0.
