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

<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## smbus_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x3C

<p>System Management Bus controller, MASTER MODE. Slave mode is a
stub: the register surface exists and can be programmed, but no
slave FSM runs and this block never answers as a target
(ledger RLB-011).</p>

|Offset|    Identifier   |              Name             |
|------|-----------------|-------------------------------|
| 0x00 |  SMBUS_CONTROL  |     SMBus Control Register    |
| 0x04 |   SMBUS_STATUS  |     SMBus Status Register     |
| 0x08 |  SMBUS_COMMAND  |     SMBus Command Register    |
| 0x0C | SMBUS_SLAVE_ADDR|  SMBus Slave Address Register |
| 0x10 |    SMBUS_DATA   |      SMBus Data Register      |
| 0x14 |  SMBUS_TX_FIFO  |     SMBus TX FIFO Register    |
| 0x18 |  SMBUS_RX_FIFO  |     SMBus RX FIFO Register    |
| 0x1C |SMBUS_FIFO_STATUS|   SMBus FIFO Status Register  |
| 0x20 |  SMBUS_CLK_DIV  |  SMBus Clock Divider Register |
| 0x24 |  SMBUS_TIMEOUT  |     SMBus Timeout Register    |
| 0x28 |  SMBUS_OWN_ADDR |   SMBus Own Address Register  |
| 0x2C | SMBUS_INT_ENABLE|SMBus Interrupt Enable Register|
| 0x30 | SMBUS_INT_STATUS|SMBus Interrupt Status Register|
| 0x34 |    SMBUS_PEC    |       SMBus PEC Register      |
| 0x38 |SMBUS_BLOCK_COUNT|   SMBus Block Count Register  |

### SMBUS_CONTROL register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Global SMBus configuration and control</p>

|Bits|Identifier|Access|Reset|     Name    |
|----|----------|------|-----|-------------|
|  0 | master_en|  rw  | 0x0 |Master Enable|
|  1 | slave_en |  rw  | 0x0 | Slave Enable|
|  2 |  pec_en  |  rw  | 0x0 |  PEC Enable |
|  3 | fast_mode|  rw  | 0x0 |  Fast Mode  |
|  4 |fifo_reset|  rw  | 0x0 |  FIFO Reset |
|  5 |soft_reset|  rw  | 0x0 |  Soft Reset |
|31:6| reserved |   r  | 0x0 |   Reserved  |

#### master_en field

<p>Enable master mode (0=disabled, 1=enabled)</p>

#### slave_en field

<p>Enable slave mode (0=disabled, 1=enabled)</p>

#### pec_en field

<p>Enable Packet Error Checking (0=disabled, 1=enabled)</p>

#### fast_mode field

<p>0 = 100 kHz standard-mode timing, 1 = 400 kHz fast-mode
timing. Selects the whole timing SET, not just a frequency,
and the set is ASYMMETRIC because a symmetric period cannot
meet fast mode at all: tLOW &gt;= 1.3 us and tHIGH &gt;= 0.6 us
do not both fit in two equal halves of 2.5 us. The SCL
period is eight base units either way; in standard mode the
unit is (SMBUS_CLK_DIV+1)/2 and the low and high phases take
four units each, in fast mode the unit is
(SMBUS_CLK_DIV+1)/8 and the low phase takes five units to
the high phase's three. tHD;STA and tSU;STA shrink from four
units to two; tSU;STO and tBUF stay at five units in BOTH
modes, because their fast-mode minimums are not
proportionally smaller. See rtl/smbus/README.md for the
achieved-versus-required table.</p>

#### fifo_reset field

<p>Write 1 to clear BOTH byte FIFOs. SELF-CLEARING; always
reads back 0. As the hardware sees it the strobe is TWO
pclk cycles wide (the bridge holds its request), and the
FIFOs clear over a window one cycle longer than that
rather than on a single edge - so a second strobe cycle
simply extends the window and is harmless. NOTHING IS
WRITTEN TO OR READ FROM EITHER FIFO WHILE THE WINDOW IS
OPEN, and the level and the empty/full flags are forced to
empty for its whole duration, so software never sees a
level that disagrees with the flags. A byte being received
when the window opens IS DISCARDED with the rest - an empty
FIFO is what was asked for - and the transfer in flight
still completes or aborts normally. THE ENGINE IS NOT
TOUCHED: use soft_reset for that.</p>

#### soft_reset field

<p>STROBE WIDTH: this field, SMBUS_CONTROL.fifo_reset and
SMBUS_COMMAND.start/stop are all self-clearing strobes
that are TWO pclk cycles wide as the hardware sees them,
because the cmd/rsp bridge holds its request for two
cycles. Every consumer is written to act ONCE across that
window - start is only taken in the idle state, an abort
is blocked once the error state is entered, and the two
reset strobes are level clears where a second cycle
changes nothing.
Write 1 to synchronously restart the master engine, the
bit PHY, the PEC accumulator and both FIFOs, and to clear
the sticky status. SELF-CLEARING: it always reads back 0.
Strobe width and the FIFO clear window are as described
for fifo_reset. The REGISTER FILE IS NOT TOUCHED -
software keeps everything it programmed and only the
engine starts over. Use it to recover a wedged bus without
reconfiguring the block.</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_STATUS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>SMBus controller status flags</p>

| Bits|   Identifier  |Access|Reset|        Name        |
|-----|---------------|------|-----|--------------------|
|  0  |      busy     |   r  |  —  |        Busy        |
|  1  |   bus_error   |   r  |  —  |      Bus Error     |
|  2  | timeout_error |   r  |  —  |    Timeout Error   |
|  3  |   pec_error   |   r  |  —  |      PEC Error     |
|  4  |    arb_lost   |   r  |  —  |  Arbitration Lost  |
|  5  |  nak_received |   r  |  —  |    NAK Received    |
|  6  |slave_addressed|   r  |  —  |   Slave Addressed  |
|  7  |    complete   |   r  |  —  |Transaction Complete|
| 11:8|   fsm_state   |   r  |  —  |      FSM State     |
|31:12|    reserved   |   r  | 0x0 |      Reserved      |

#### busy field

<p>Transaction in progress (0=idle, 1=busy)</p>

#### bus_error field

<p>Bus error: a transfer was aborted for a reason other than
a NAK or a PEC mismatch - SMBUS_COMMAND.stop written alone,
a TX FIFO underrun, an RX FIFO overrun, or bus recovery
that could not free SDA within nine clocks. Set together
with timeout_error it means recovery was attempted, failed,
and the bus was released without a STOP.</p>

#### timeout_error field

<p>A bus timeout: SCL was held low - by this master or by
anyone else - for longer than SMBUS_TIMEOUT. The
transaction was aborted and the bus released. A timeout
abort runs I2C bus recovery (up to nine full standard-mode
SCL pulses with SDA released) before its STOP, so a slave
stuck part-way through a byte is clocked out of it and the
transfer is terminated properly rather than merely
abandoned - with two exceptions that release and report
without clocking: a timeout inside the final STOP, and a
timeout before anything was framed unless SDA is stuck low
on a quiet SCL (a low SCL there means a foreign transfer,
which must not be clocked). If SDA was still low after
nine clocks, bus_error is set as well and no STOP was
generated; timeout_error alone means the bus was released
and, where recovery applied, a STOP was generated.</p>

#### pec_error field

<p>PEC mismatch detected</p>

#### arb_lost field

<p>Multi-master arbitration lost. TIED LOW: arbitration is
not implemented, so this bit never sets (ledger RLB-011).</p>

#### nak_received field

<p>NAK received from slave</p>

#### slave_addressed field

<p>Addressed as a slave. TIED LOW: slave mode is a stub, so
this bit never sets (ledger RLB-011).</p>

#### complete field

<p>The transaction finished AND terminated the bus with a
STOP, with no error of any kind. It is NEVER set alongside
bus_error, timeout_error, pec_error or nak_received, so
reading it alone is enough to know the transfer succeeded.
It is also set for a STOP that escalated to bus recovery
and recovered - the nine clocks freed SDA and a real STOP
went out - so a successful recovery is invisible to
software; there is no bit that reports it.</p>

#### fsm_state field

<p>Current state machine state (for debugging)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_COMMAND register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Transaction command and control</p>

| Bits|Identifier|Access|Reset|      Name      |
|-----|----------|------|-----|----------------|
| 3:0 |trans_type|  rw  | 0x0 |Transaction Type|
| 15:8| cmd_code |  rw  | 0x0 |  Command Code  |
|  16 |   start  |  rw  | 0x0 |      Start     |
|  17 |   stop   |  rw  | 0x0 |      Stop      |
|31:18| reserved |   r  | 0x0 |    Reserved    |

#### trans_type field

<p>Transaction type: 0=Quick (write direction), 1=SendByte,
2=RecvByte, 3=WriteByte, 4=ReadByte, 5=WriteWord,
6=ReadWord, 7=BlockWrite, 8=BlockRead, 9=BlockProc,
A=Quick (read direction). The R/W bit IS the payload
of a quick command, so both directions have their own
code rather than a direction bit that would mean
nothing for the other types.</p>

#### cmd_code field

<p>SMBus command byte (for transactions that use it)</p>

#### start field

<p>Write 1 to launch the transaction described by the rest of
this register. SELF-CLEARING. It is IGNORED unless
SMBUS_CONTROL.master_en is already set - the write is
accepted and silently discarded, SMBUS_STATUS.busy never
rises and no error is reported, so software must enable
master mode before starting.</p>

#### stop field

<p>Written TOGETHER with start it is a no-op: every
transaction ends with a STOP anyway. Written ALONE while
SMBUS_STATUS.busy is set it is an ABORT - the transaction
stops, a real STOP is generated on the wire, both lines
are released, busy drops and SMBUS_STATUS.bus_error is
set. SELF-CLEARING.</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_SLAVE_ADDR register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Target slave address for master transactions</p>

|Bits|Identifier|Access|Reset|     Name    |
|----|----------|------|-----|-------------|
| 6:0|slave_addr|  rw  | 0x0 |Slave Address|
|31:7| reserved |   r  | 0x0 |   Reserved  |

#### slave_addr field

<p>Target slave address, 7 bits. The R/W direction is NOT in
this field - it comes from SMBUS_COMMAND.trans_type, and
the controller appends it when it puts the address byte on
the wire (twice, for a read with a command code).</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_DATA register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Single byte data for simple transactions</p>

|Bits|Identifier|Access|Reset|   Name  |
|----|----------|------|-----|---------|
| 7:0|   data   |  rw  | 0x0 |Data Byte|
|31:8| reserved |   r  | 0x0 | Reserved|

#### data field

<p>Data byte. Software writes it for Send Byte / Write Byte;
hardware writes it with the received byte after a Receive
Byte / Read Byte. The hardware path is qualified with <code>we</code>
so it only lands when there IS a received byte - without
that, the field is overwritten from the live shift
register every clock and no software write survives to the
data phase (GitHub #58 item 6).</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_TX_FIFO register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Transmit FIFO write port for block transactions</p>

|Bits|Identifier|Access|Reset|  Name  |
|----|----------|------|-----|--------|
| 7:0|  tx_data |   w  | 0x0 | TX Data|
|31:8| reserved |   r  | 0x0 |Reserved|

#### tx_data field

<p>Write data byte to TX FIFO</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_RX_FIFO register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>Receive FIFO read port for block transactions</p>

|Bits|Identifier|Access|Reset|  Name  |
|----|----------|------|-----|--------|
| 7:0|  rx_data |   r  |  —  | RX Data|
|31:8| reserved |   r  | 0x0 |Reserved|

#### rx_data field

<p>Read the next byte from the RX FIFO. READING IT EMPTY
RETURNS THE STALE HEAD - the last byte that was there - and
does not move the pointer. IF NOTHING WAS EVER WRITTEN THE
VALUE IS UNDEFINED: the FIFO memory has no reset in any
MEM_STYLE, so it is whatever the RAM initialises to on an
FPGA and genuinely undefined on an ASIC. Check
SMBUS_FIFO_STATUS.rx_level first; it and rx_empty always
agree in the active-low build (see SMBUS_FIFO_STATUS).</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_FIFO_STATUS register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>TX/RX FIFO levels and status flags. IN THE ACTIVE-LOW RESET
BUILD - the only one currently usable - LEVEL AND FLAGS ARE
CONSISTENT BY CONSTRUCTION at every cycle: a level of 0 always
reads back as empty and a full FIFO always reads back at the
depth, including across a fifo_reset or soft_reset, where all
three are driven from one source for the whole clear window and
nothing is accepted into or out of the FIFO. Built with
RESET_ACTIVE_HIGH the FIFO storage never leaves reset
(COMMON-026, tracked here as RLB-012), so the level counts past
the depth against a permanently empty memory and none of this
holds - that build is not usable until COMMON-026 lands.</p>

| Bits|Identifier|Access|Reset|     Name    |
|-----|----------|------|-----|-------------|
| 5:0 | tx_level |   r  |  —  |TX FIFO Level|
|  6  |  tx_full |   r  |  —  | TX FIFO Full|
|  7  | tx_empty |   r  |  —  |TX FIFO Empty|
| 13:8| rx_level |   r  |  —  |RX FIFO Level|
|  14 |  rx_full |   r  |  —  | RX FIFO Full|
|  15 | rx_empty |   r  |  —  |RX FIFO Empty|
|31:16| reserved |   r  | 0x0 |   Reserved  |

#### tx_level field

<p>Bytes in the TX FIFO, 0 to FIFO_DEPTH (the parameter,
2..63; 32 by default). The field is six bits regardless.</p>

#### tx_full field

<p>TX FIFO full flag</p>

#### tx_empty field

<p>TX FIFO empty flag</p>

#### rx_level field

<p>Bytes in the RX FIFO, 0 to FIFO_DEPTH (the parameter,
2..63; 32 by default). The field is six bits regardless.</p>

#### rx_full field

<p>RX FIFO full flag</p>

#### rx_empty field

<p>RX FIFO empty flag</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_CLK_DIV register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>Clock divider for SCL generation</p>

| Bits|Identifier|Access|Reset|     Name    |
|-----|----------|------|-----|-------------|
| 15:0|  clk_div |  rw  | 0xF9|Clock Divider|
|31:16| reserved |   r  | 0x0 |   Reserved  |

#### clk_div field

<p>SCL clock divider. STANDARD MODE:
SCL = sys_clk / (4 * (div + 1)) - the default 249 gives
100 kHz at 100 MHz. FAST MODE (SMBUS_CONTROL.fast_mode=1)
is four times faster from the SAME divider:
SCL = sys_clk / ((div + 1)), i.e. 8 units of
(div+1)/8 clocks - 249 gives 390.6 kHz at 100 MHz. Both
unit divides round UP, so a small divider cannot silently
shorten the period.</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_TIMEOUT register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>Timeout threshold configuration</p>

| Bits|Identifier|Access|  Reset |     Name    |
|-----|----------|------|--------|-------------|
| 23:0|  timeout |  rw  |0x2625A0|Timeout Value|
|31:24| reserved |   r  |   0x0  |   Reserved  |

#### timeout field

<p>Bus timeout in core clock cycles. IT MEASURES HOW LONG
SCL IS LOW ON THE BUS - either this master pulling it down
or the line still reading low after we let go - so it
catches a stretching slave, a short and a wedged master
alike. It is counted only while this master owns a
primitive; an idle bus held low by somebody else does not
arm it. 0 DISABLES the check entirely; it must never mean
'expire immediately'. Default 2500000 is ~25 ms at 100 MHz.
WORST CASE FROM 'SCL WEDGES' TO busy=0 IS FIVE TIMES THIS
VALUE (~125 ms at the default): one window for the
primitive that stalls, then four for the abort's STOP,
which is deliberately more patient.</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_OWN_ADDR register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Own slave address (for slave mode operation)</p>

|Bits|Identifier|Access|Reset|     Name     |
|----|----------|------|-----|--------------|
| 6:0| own_addr |  rw  | 0x0 |  Own Address |
|  7 |  addr_en |  rw  | 0x0 |Address Enable|
|31:8| reserved |   r  | 0x0 |   Reserved   |

#### own_addr field

<p>7-bit own slave address</p>

#### addr_en field

<p>Enable own address matching (slave mode)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_INT_ENABLE register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>Interrupt enable mask</p>

|Bits|  Identifier |Access|Reset|            Name           |
|----|-------------|------|-----|---------------------------|
|  0 | complete_en |  rw  | 0x0 |Transaction Complete Enable|
|  1 |   error_en  |  rw  | 0x0 |   Error Interrupt Enable  |
|  2 | tx_thresh_en|  rw  | 0x0 |  TX FIFO Threshold Enable |
|  3 | rx_thresh_en|  rw  | 0x0 |  RX FIFO Threshold Enable |
|  4 |slave_addr_en|  rw  | 0x0 |   Slave Addressed Enable  |
|31:5|   reserved  |   r  | 0x0 |          Reserved         |

#### complete_en field

<p>Enable interrupt on transaction complete</p>

#### error_en field

<p>Enable interrupt on bus error</p>

#### tx_thresh_en field

<p>Enable the TX threshold interrupt. THE THRESHOLD IS FIXED
AT EMPTY: the condition is tx_fifo_empty, not a
programmable level.</p>

#### rx_thresh_en field

<p>Enable the RX threshold interrupt. THE THRESHOLD IS FIXED
AT NON-EMPTY: the condition is !rx_fifo_empty, not a
programmable level.</p>

#### slave_addr_en field

<p>Enable interrupt when addressed as slave</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_INT_STATUS register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>Interrupt status flags (write 1 to clear). Every bit is
sticky: set by the RISING EDGE of its condition and cleared only
by a W1C write, with SET WINNING over a simultaneous clear. The
smb_interrupt pin is (SMBUS_INT_STATUS &amp; SMBUS_INT_ENABLE) != 0,
registered - so clearing a bit here is what deasserts the pin.</p>

|Bits|  Identifier  |  Access |Reset|        Name        |
|----|--------------|---------|-----|--------------------|
|  0 | complete_int |rw, woclr| 0x0 |Transaction Complete|
|  1 |   error_int  |rw, woclr| 0x0 |   Error Interrupt  |
|  2 | tx_thresh_int|rw, woclr| 0x0 |  TX FIFO Threshold |
|  3 | rx_thresh_int|rw, woclr| 0x0 |  RX FIFO Threshold |
|  4 |slave_addr_int|rw, woclr| 0x0 |   Slave Addressed  |
|31:5|   reserved   |    r    | 0x0 |      Reserved      |

#### complete_int field

<p>Transaction completed (W1C)</p>

#### error_int field

<p>Bus error occurred (W1C)</p>

#### tx_thresh_int field

<p>TX FIFO became EMPTY (the threshold is fixed at empty),
W1C. STICKY: set on the
edge of the condition, cleared only by writing 1. It is
not a live level - a W1C bit that re-asserts itself on the
next clock cannot be cleared at all (GitHub #58 qc1).</p>

#### rx_thresh_int field

<p>RX FIFO became NON-EMPTY (the threshold is fixed at
non-empty), W1C. STICKY: set on the
edge of the condition, cleared only by writing 1.</p>

#### slave_addr_int field

<p>Device addressed as slave (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_PEC register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>Packet Error Checking value</p>

|Bits|Identifier|Access|Reset|   Name  |
|----|----------|------|-----|---------|
| 7:0|    pec   |  rw  | 0x0 |PEC Value|
|31:8| reserved |   r  | 0x0 | Reserved|

#### pec field

<p>PEC value (CRC-8, polynomial 0x07). Hardware writes the
computed PEC of the transaction that just finished, and
only then (<code>we</code>), so a software-written value survives
until a transaction replaces it. Reading it after a
transfer gives THE BYTE THAT WAS ON THE WIRE: the PEC
this master transmitted on a write, and the PEC byte the
SLAVE SENT on a read - the useful one when they disagree,
because it is the evidence. The running CRC the master
computed is not exposed; the comparison result is
SMBUS_STATUS.pec_error.</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_BLOCK_COUNT register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>Block transfer byte count</p>

|Bits| Identifier|Access|Reset|    Name   |
|----|-----------|------|-----|-----------|
| 5:0|block_count|  rw  | 0x0 |Block Count|
|31:6|  reserved |   r  | 0x0 |  Reserved |

#### block_count field

<p>Block transfer byte count (1-32). Software programs it for
Block Write; for Block Read the COUNT COMES FROM THE
SLAVE, and hardware writes it back here (<code>we</code>) CLAMPED
BOTH WAYS: a count of 0 becomes 1, and a count longer than
the FIFO depth becomes the depth, so software knows how
many bytes to drain.
A software-supplied Block Write count is clamped the same
way when the transfer is sized, but is NOT written back:
this register reads back exactly what software wrote even
if the transfer used a different number. It governs the
BLOCK transfers only - a Write Byte sends one data byte
whatever this holds (GitHub #58 item 10).</p>

#### reserved field

<p>Reserved bits</p>
