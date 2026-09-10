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

# SMBus 2.0 Controller

APB4-attached SMBus 2.0 master. All ten transaction types, packet error
checking, clock stretching, a bus timeout, and a strict register decode.

**Status:** master implemented and regression-clean. **Slave mode is a stub**
(see "What a real slave would need"). Multi-master arbitration is not
implemented (see "What arbitration would need").

## Module structure

```
apb4_smbus                 APB4 attach, clocking, the interrupt pin
+- apb4_slave / apb4_slave_cdc   APB4 -> cmd/rsp (CDC_ENABLE picks which)
+- smbus_config_regs       strict decode, PeakRDL block, W1C decode, FIFO ports
|  +- peakrdl_to_cmdrsp    cmd/rsp -> PeakRDL passthrough
|  +- smbus_regs           generated register block
+- smbus_core              TRANSACTION SEQUENCER
   +- smbus_bit_phy        BIT-LEVEL PHY: every SCL and SDA movement
   +- smbus_trans_decode   the transaction table, as combinational logic
   +- smbus_flow_rules     what happens next: byte states, ACK policy, the
   |                       TX FIFO load/pop discipline, FIFO exhaustion
   +- smbus_byte_fifos     TX/RX byte buffers and their three reset sources
   |  +- simple_fifo x2 -> fifo_sync
   +- smbus_int_status     sticky, edge-set, W1C-cleared interrupt bits
   +- smbus_pec            CRC-8, polynomial 0x07
```

The split that matters is `smbus_core` / `smbus_bit_phy`. **The sequencer owns
the transaction and the PHY owns the wire; the sequencer never sees a clock
period and the PHY never sees a transaction.** They meet at five primitives -
START, repeated START, STOP, transmit one bit, receive one bit - each answered
with a single-cycle `op_done`. Bit timing folded into a transaction FSM is bit
timing nobody can review, which is how this block shipped with SCL assigned in
two states out of sixteen and frozen low after the first START.

## Clock domains

`CDC_ENABLE` picks the attach, and it is the only thing that changes:

- **`CDC_ENABLE=0`** - one clock domain. `apb4_slave` converts APB to cmd/rsp
  and the register block and the whole master engine run on `pclk`; nothing
  crosses.
- **`CDC_ENABLE=1`** - `pclk` and `smbus_clk` are independent. `apb4_slave_cdc`
  carries the register accesses across, and the register block and the master
  engine run on `smbus_clk`. Exactly one other thing crosses: the masked
  interrupt vector, `(SMBUS_INT_STATUS & SMBUS_INT_ENABLE)`, which is a level
  and goes through `glitch_free_n_dff_arn`, the house level synchronizer, with
  its destination side on `presetn`. Never a hand-rolled flop pair.

**`presetn` and `smbus_resetn` must arrive already synchronized** - asserted
asynchronously, de-asserted synchronously to their own clock. This block
instantiates no reset synchronizer, and `rst_n` now feeds a flop whose output
lands on an asynchronous reset net inside `simple_fifo`, so a reset released
asynchronously can put that flop and the FIFO it gates on opposite sides of the
same edge. Every other RLB block assumes the same of its resets; delivering
them is the integrator's job.

**SCL and SDA are asynchronous in BOTH builds** - they come from pads, and no
amount of same-clock design makes a pad synchronous. `smbus_bit_phy` puts two
flops on each of them and nothing in the block looks at a raw pin. That is the
crossing that always exists, and it is easy to talk yourself out of because the
bus is slow; slow is not synchronous.

## Transaction table

`S` = START, `Sr` = repeated START, `P` = STOP, `A` = master ACKs,
`N` = master NAKs. `[PEC]` is present only when `SMBUS_CONTROL.pec_en` is set.

| Code | Type | On the wire | Data bytes |
|------|------|-------------|------------|
| 0x0 | Quick Command | `S, Addr+W, P` | 0 |
| 0x1 | Send Byte | `S, Addr+W, Data, [PEC], P` | 1 |
| 0x2 | Receive Byte | `S, Addr+R, Data(N), [PEC], P` | 1 |
| 0x3 | Write Byte | `S, Addr+W, Cmd, Data, [PEC], P` | 1 |
| 0x4 | Read Byte | `S, Addr+W, Cmd, Sr, Addr+R, Data(N), [PEC], P` | 1 |
| 0x5 | Write Word | `S, Addr+W, Cmd, DataLo, DataHi, [PEC], P` | 2 |
| 0x6 | Read Word | `S, Addr+W, Cmd, Sr, Addr+R, DataLo(A), DataHi(N), [PEC], P` | 2 |
| 0x7 | Block Write | `S, Addr+W, Cmd, Count, Data x Count, [PEC], P` | Count |
| 0x8 | Block Read | `S, Addr+W, Cmd, Sr, Addr+R, Count, Data x Count(N), [PEC], P` | Count, from the slave |
| 0x9 | Block Proc Call | Block Write then `Sr, Addr+R, Count, Data x Count(N), [PEC], P` | both |

**Every read that carries a command code has a repeated START.** The slave is
addressed for WRITE to receive the command byte, then `Sr` and addressed again
for READ. Only Receive Byte, which has no command code, addresses for read
straight away. Sending `Addr+R` first delivers the command byte into a slave
that is already talking.

**The data byte count is per transaction type.** `SMBUS_BLOCK_COUNT` governs
the block transfers and nothing else: a Write Byte sends exactly one data byte
whatever `BLOCK_COUNT` happens to hold from a previous transfer.

### Where the data comes from

It is deliberately not one place:

| Transaction | Transmitted data | Received data |
|---|---|---|
| Send Byte, Write Byte | `SMBUS_DATA` | - |
| Write Word, Block Write | TX FIFO, in order | - |
| Block Write count byte | `SMBUS_BLOCK_COUNT` | - |
| Receive Byte, Read Byte | - | RX FIFO **and** `SMBUS_DATA` |
| Read Word, Block Read | - | RX FIFO, in order - **and `SMBUS_DATA`, which every received data byte overwrites**, so after a multi-byte read it holds the LAST byte |
| Block Read count byte | - | from the slave, clamped (0 becomes 1, longer than the FIFO depth becomes the depth) and written back to `SMBUS_BLOCK_COUNT` |

A one-byte read lands in `SMBUS_DATA` as well as the FIFO so that reading a
single byte needs no FIFO access at all.

## The open-drain contract

SMBus is a wired-AND bus: a device may pull a line LOW or RELEASE it, and may
never drive it high. With this port convention (`smb_*_o` = value, `smb_*_t` =
1 means released) that contract collapses to one statement, which is how the
PHY implements it:

```
smb_scl_o == smb_scl_t    and    smb_sda_o == smb_sda_t
```

Driving is only ever driving a 0 and a 1 is always a release, so "actively
driving a 1 on an open-drain line" is structurally impossible rather than
something a reviewer has to re-check state by state.

## Bit timing, fast mode and clock stretching

One SCL period is eight base units. In **standard mode** the unit is
`(CLK_DIV + 1) / 2` clocks, so `SCL = clk / (4 x (CLK_DIV + 1))` - 249 gives
100 kHz from a 100 MHz clock. In **fast mode** the unit is `(CLK_DIV + 1) / 8`,
so the same divider runs four times faster: `SCL = clk / (CLK_DIV + 1)`, and
249 gives 390.6 kHz. Both unit divides **round up**, so a small divider cannot
silently shorten the period.

`SMBUS_CONTROL.fast_mode` selects the **whole 400 kHz timing set, not just a
frequency**, and the set is **asymmetric**. A symmetric period cannot meet
fast mode at all: tLOW >= 1.3 us and tHIGH >= 0.6 us do not both fit in two
equal halves of a 2.5 us period at the ratio standard mode uses. In fast mode
the low phase takes 5/8 of the period and the high phase 3/8.

Everything is counted in base units of `(CLK_DIV+1)/2` clocks in standard mode
and `(CLK_DIV+1)/8` in fast mode, eight units to the SCL period, **rounded up**
so a small divider does not silently shorten the period.

Achieved at the RDL default (`CLK_DIV = 249`, 100 MHz core clock), against the
SMBus 2.0 / I2C minimums - every figure is a minimum the block clears, not a
target it sits on:

| | standard achieved | required | fast achieved | required |
|---|---|---|---|---|
| SCL period | 10.00 us (100.0 kHz) | - | 2.56 us (390.6 kHz) | - |
| tLOW | 5000 ns | >= 4700 | 1600 ns | >= 1300 |
| tHIGH | 5000 ns | >= 4000 | 960 ns | >= 600 |
| tHD;STA | 5000 ns | >= 4000 | 640 ns | >= 600 |
| tSU;STA | 5000 ns | >= 4700 | 640 ns | >= 600 |
| tSU;STO | 6250 ns | >= 4000 | 1600 ns | >= 600 |
| tBUF | 6250 ns | >= 4700 | 1600 ns | >= 1300 |

**A START waits for the bus to be free.** Before pulling SDA down the master
waits for SCL and SDA to be sampled high together and then holds tBUF. A
master that pulls SDA low under a low SCL has not generated a START at all -
it has put a data bit on somebody else's transfer. The wait is bounded by
`SMBUS_TIMEOUT` - **when it is non-zero**. With `SMBUS_TIMEOUT = 0` the
timeout is disabled everywhere, including here, so a bus that never goes free
leaves `busy` set in the START state indefinitely; the way out is
`SMBUS_COMMAND.stop`, which aborts and releases. That is the price of
disabling the timeout, and it is the only place the block will wait forever.

**Clock stretching is honoured on every release of SCL.** After letting SCL go,
the PHY holds its quarter counter at zero until the synchronized SCL input
actually reads high, so a slave holding SCL down extends the high phase instead
of being clocked through. That applies to data bits, ACK bits, the repeated
START and the STOP alike.

## Timeout

**SCL low for longer than `SMBUS_TIMEOUT` clocks aborts the transaction,
reports `SMBUS_STATUS.timeout_error`, releases the bus and returns the FSM to
idle.** "Low" means low on the bus - either this master is pulling it down or
the line still reads low after we let go - so it covers a slave stretching
forever, a short, and a wedged master.

**`SMBUS_TIMEOUT = 0` disables the timeout.** It must never mean "expire
immediately"; with the comparator this block used to have, 0 forced an error
the instant any transaction started.

The timeout also covers the START's bus-free wait, and **every state that can
wait on SCL is timeout-covered, including the final STOP**. A slave stretching
through the STOP used to hang busy forever precisely because that state was
excluded.

**On expiry the PHY abandons the primitive: it releases both lines and
reports.** Releasing is the only exit that always exists - a STOP cannot be
generated at all while another device is holding SCL down, so the alternative
to giving up is hanging.

## Bus recovery

A STOP needs SDA to rise while SCL is high. If another device is holding SDA
down - a slave stuck part-way through a byte, which is what a timeout usually
means - the master cannot generate one, and simply releasing leaves every other
device watching a transfer that was never terminated.

**Whenever the master needs to issue a STOP and finds SDA held low when it goes
to release it, and on a timeout abort (the two exceptions below aside), it
performs I2C bus recovery**: with
SDA released it pulses SCL up to nine times, open-drain and stretch-aware,
sampling SDA at the end of each high phase and stopping as soon as SDA reads
high; then it generates a proper STOP - SDA low while SCL is low, SCL high, SDA
high. Nine is the I2C limit: it is one more clock than a byte, so a device
stuck anywhere inside one has been clocked out of it.

**Recovery clocks are full standard-mode bits, whatever `fast_mode` says** -
tLOW 5000 ns and tHIGH 5000 ns at the default divider, against the 4.7 us /
4.0 us standard-mode minimums. The device being recovered is by definition not
keeping up, so the slowest legal clock is the one most likely to shake it
loose, and a recovery "clock" that is only a fraction of a bit low is not
standard-mode timing whatever its unit count says.

**Recovery is bounded by the same stall-window discipline as everything else.**
If SDA is still low after nine clocks the master releases both lines, reports
`SMBUS_STATUS.bus_error` (and `timeout_error` as well if a timeout is what
started it), and returns to idle. `busy` dropping still coincides with both
lines released, and the abort tracker is still the single authority on when the
sequencer may leave the error state.

**Recovery does not run on two exits**, and the RDL says so too:

- a timeout in the final `STOP` itself - the PHY has already released both
  lines to report it, so re-driving them would be the only way to get it wrong;
- a timeout before anything of ours was framed, unless SDA is the line being
  held and SCL is quiet. If SCL is also low somebody else is mid-transfer, and
  pulsing SCL would clock **their** bits. **A stuck SDA on an otherwise quiet
  bus is recovered even though no START ever went out** - a bus found stuck at
  power-on is exactly what the nine clocks are for.

### What the status bits mean together

| `complete` | `bus_error` | `timeout_error` | meaning |
|---|---|---|---|
| 1 | 0 | 0 | the transaction finished and the bus was released with a STOP |
| 0 | 0 | 1 | a timeout; the bus was released. Recovery either was not applicable (nothing framed, or the STOP itself timed out) or ran and succeeded, and a STOP was generated |
| 0 | 1 | 1 | a timeout, recovery was attempted and **failed** - SDA was still low after nine clocks, both lines were released and **no STOP reached the wire** |
| 0 | 1 | 0 | aborted without a timeout - `COMMAND.stop` alone, a TX underrun, an RX overrun, or a STOP whose recovery failed |
| 1 | 0 | 0 | ... **including a STOP that escalated to bus recovery and recovered**: the nine clocks freed SDA, a real STOP went out, and the transaction succeeded. Recovery on this path is invisible to software - there is no bit that says it happened |
| 0 | x | x | with `nak_received` or `pec_error`: the slave did not acknowledge, or the PEC did not match |

**`complete` is never set alongside any error.** It is computed from the
next-state error terms, including the ones raised on the very edge the STOP
completes, so a transaction that did not terminate the bus cannot report
success. A failed recovery raising `bus_error` on that same edge used to leave
`complete=1` and `bus_error=1` together with nothing on the wire.

Measured, against a slave stuck in its ACK after a 15 us stretch with
`SMBUS_TIMEOUT` at 5 us:

| time | event |
|---|---|
| 0.965 us | START |
| ~5 us | timeout expires; PHY abandons the ACK bit, releases both lines, reports |
| 17.805 us | recovery clock 0 - SCL rises, SDA still low |
| 17.945 us | recovery clock 1 - SCL rises, SDA still low |
| 18.085 us | recovery clock 2 - SCL rises, **SDA reads high**: the slave let go |
| 18.225 us | SCL high with SDA driven low - the STOP setup |
| 18.345 us | **STOP** |

ending with `busy=0`, `timeout_error=1`, `bus_error=0` and both lines
released.

A normal bit's low phase is 5/8 of the period, orders of magnitude under any
legal SMBus timeout, so the check never fires on healthy traffic. **The counter
only runs while this master owns a primitive** - an idle bus held low by
somebody else does not arm it, and the report is consumed once, by the
sequencer that acts on it.

**Worst case from "SCL wedges" to `busy` = 0 is five timeout windows** - about
125 ms at the default `SMBUS_TIMEOUT`. One window for the primitive that
stalls, then four for the abort's STOP, which gets `WINDOWS_STOP = 3` (four
windows) against `WINDOWS_NORMAL = 0` (one). That 4:1 ratio is the deliberate
patience described above; size `SMBUS_TIMEOUT` with the multiplier in mind.

## Busy, completion and recovery

**`SMBUS_STATUS.busy` is high from the accepted START request until the FSM is
back in idle, whether the transaction succeeded or not, so busy dropping is the
single "the bus is yours again" signal.**

**Every exit runs through a STOP, and error recovery never waits for
software.** A NAK anywhere - address, command, data or PEC - a PEC mismatch, a
FIFO underrun or overrun, or a bus timeout all go to the error state, which
issues a STOP, releases both lines and returns to idle on its own. Software
does not have to write `SMBUS_COMMAND.stop` to un-wedge the block.

**`busy` dropping to 0 always coincides with both lines released**, on every
path, including the ones where the STOP itself could not be generated. That is
what makes busy usable as the single "the bus is yours again" signal: an abort
that leaves SCL driven low while reporting itself finished is worse than no
abort at all.

An abort - `SMBUS_COMMAND.stop` alone, or a timeout - **terminates the
primitive that is running**, at a point where moving the lines is safe, and
then generates the STOP. A single-cycle STOP request issued into a PHY that
only accepts requests while idle is dropped, which is how an abort mid-bit
used to leave SCL low and busy stuck until a soft reset.

`SMBUS_COMMAND.stop` written **together with** start is the ordinary case and
is accepted as a no-op, because every transaction ends with a STOP anyway.
Written **alone while busy** it is an abort: the transaction stops, the bus is
released and `bus_error` is reported.

`SMBUS_STATUS.complete` means the transaction finished **and terminated the
bus with a STOP**, with no error of any kind - see the truth table above. It is
never set alongside `bus_error`, `timeout_error`, `pec_error` or
`nak_received`, so reading it alone is enough to know the transfer succeeded.

## PEC

**The CRC-8 (polynomial 0x07) covers every byte that was actually on the wire,
in wire order, including both address bytes - the `Addr+W` after the START and
the `Addr+R` after the repeated START.** It is cleared once, when the START is
issued, and never held in clear afterwards.

The engine is fed the byte VALUE at byte-complete time, from a register that
does not shift. Sampling the shift register instead reads 0x00 for every
transmitted byte, because eight zeros have been shifted in by the time the last
bit is on the wire.

On a **write**, the computed PEC is transmitted after the last data byte. On a
**read**, the master ACKs the last data byte instead of NAKing it, receives the
slave's PEC byte, NAKs that, and compares it against the running CRC; a
mismatch sets `SMBUS_STATUS.pec_error`. **The received PEC byte is never folded
into the CRC - it is the thing being checked.**

`SMBUS_PEC` shows **the byte that was on the wire**: on a write, the PEC this
master transmitted; on a read, the PEC byte the **slave sent** - which is the
useful one when they disagree, because it is the evidence. The running CRC the
master computed is not exposed. Hardware writes the field only at the end of a
transaction, so a software-written value survives until a transfer replaces
it.

## Interrupts

**`smb_interrupt` is `(SMBUS_INT_STATUS & SMBUS_INT_ENABLE) != 0`, registered.**
Not the live status: a pin built from live status cannot be deasserted by
software at all, only by the underlying condition going away, which with a
level-sensitive interrupt controller upstream is an interrupt storm.

**Every `SMBUS_INT_STATUS` bit is sticky: set by the RISING EDGE of its
condition and cleared only by a write-1-to-clear, with SET WINNING over a
simultaneous clear.** That includes the two FIFO threshold bits - their
description says W1C, and a W1C bit that is really a live level cannot be
cleared at all. Set winning matters because an event arriving in the same cycle
software clears the previous one must not be lost: an extra interrupt costs a
wasted read, a lost one is a hang.

A NAK counts as an error for `error_int`. It has its own status bit, but it is
still a transaction that failed, and software that enabled the error interrupt
and never hears about a NAK has to poll.

The sticky bits live in hardware (`smbus_int_status.sv`); the generated
register field is a live mirror of them, and the W1C is decoded in
`smbus_config_regs` from `wr_data & wr_biten` at the register's own address, on
the rising edge of the held request.

With `CDC_ENABLE=1` the masked vector crosses from `smbus_clk` to `pclk`
through `glitch_free_n_dff_arn` - the house level synchronizer - never a
hand-rolled flop pair. It is a level and is quasi-static between events, and
the source is sticky, so no interrupt can be manufactured or lost by the
crossing.

## Soft reset and FIFO reset

**`SMBUS_CONTROL.soft_reset` is a self-clearing strobe that synchronously
restarts the master engine, the bit PHY, the PEC accumulator, both FIFOs and
the sticky status, and does NOT touch the register file.** It always reads back
0. Software keeps everything it programmed and only the engine starts over,
which is what makes it useful for recovering a wedged bus without
reconfiguring the block. The PHY releases both lines as it aborts - stopping
mid-primitive while still driving would wedge the bus for every other device.

**`SMBUS_CONTROL.fifo_reset` clears the two byte buffers only**, leaving the
engine alone. It is likewise self-clearing.

**Every self-clearing strobe is two `pclk` cycles wide as the hardware sees
it** - `soft_reset`, `fifo_reset`, `COMMAND.start` and `COMMAND.stop` - because
the cmd/rsp bridge holds its request for two cycles. Every consumer acts
**once** across that window: `start` is only taken in the idle state, an abort
is blocked once the error state has been entered, and the two reset strobes are
level clears where a second cycle simply extends the clear window and is
harmless, because nothing is accepted into or out of a FIFO while it is open.

## The FIFO contract

**In the active-low reset build, the level and the flags are consistent by
construction at every cycle.** A level of 0 always reads back as `empty`, and a
full FIFO always reads back at the depth - including across a `fifo_reset` or
`soft_reset`, where the level, `empty` and `full` are all driven from one
source for the whole clear window and nothing is written to or read from the
FIFO while it is open. Software can drain with `while (rx_level) pop;` and know
it terminates.

**That is an active-low-build guarantee only.** Built with
`RESET_ACTIVE_HIGH` the FIFO storage never leaves reset, because `rtl/common`'s
`fifo_control.sv` and `counter_bin.sv` hardcode active-low in their bodies
(**COMMON-026**, tracked for this block as **RLB-012**). The wrapper's own
count then runs past the depth against a permanently empty memory, `empty`
never falls, and the drain loop above does not terminate. No care inside this
block can reconcile that; the active-high build is not usable until COMMON-026
lands.

**A `SMBUS_RX_FIFO` read with the FIFO empty returns the stale head** - the
last byte that was there - and does not move the pointer. **If nothing was ever
written the value is undefined**: the FIFO memory has no reset in any
`MEM_STYLE`, so it is whatever the RAM initialises to on an FPGA (0x00 in
simulation by default, 0x11 under `+verilator+rand+reset+2`) and genuinely
undefined on an ASIC. Check `rx_level` first.

**A `fifo_reset` landing during an active receive discards the byte in flight
along with the rest.** Software asked for an empty FIFO and gets one; the
transfer itself still completes or aborts through the normal paths.

**A transmitted byte is loaded from the TX FIFO and popped in the same cycle.**
The FIFO's read data is its combinational head, so the value captured on the
edge that pops is the byte being loaded. Loading without popping sends the same
byte twice; popping a cycle later puts every load one pop behind the pointer.

**TX underrun** - `SMBUS_BLOCK_COUNT` larger than the number of staged bytes:
after the last staged byte the master **stops, sets `error_int`, and fabricates
nothing**. A byte nobody asked to send is worse on a shared bus than a short
transfer.

**RX overrun** - a block read longer than the free space in the RX FIFO. The
master checks `rx_fifo_full` **before storing each data byte, the last one
included**. The first byte that does not fit is **not stored**, is **NAKed**,
and ends the transfer with `bus_error` and `error_int`; the RX FIFO holds
exactly what fit and `complete` stays 0. Checking after the store is useless:
a full `fifo_sync` drops the write silently.

Block counts are clamped on **both** sides. A slave-supplied Block Read count
of 0 becomes 1 and one larger than the FIFO depth becomes the depth, and the
clamped value is written back to `SMBUS_BLOCK_COUNT`. A software-supplied
**Block Write** count is clamped the same way when the transfer is sized, but
the register is **not** written back: `SMBUS_BLOCK_COUNT` reads back exactly
what software wrote, even if the transfer used a different number. Read the
count you programmed as your own record, not as what went out. The over-length test looks at the
**whole byte**: a count of 0x40 has all-zero low six bits, so testing a
truncated field first reads 64 as 0.

## Register decode

**Only the fifteen mapped registers decode. Every other address in the 4 KB
window is dropped: no internal strobe fires, the read returns 0, and the access
is acknowledged locally with `PSLVERR`.** The generated block sees six address
bits, so without the strict decode every unmapped address aliases onto a real
register 64 bytes below it - 0x040 would write `SMBUS_CONTROL`.

The drop is acknowledged combinationally and locally, in the same shape the
register block uses, because the adapter holds its request until it is
acknowledged; a dropped access that is never acknowledged hangs the bus.

## Register map

| Offset | Register | Type | Notes |
|--------|----------|------|-------|
| 0x000 | SMBUS_CONTROL | RW | master/slave/PEC enables, fast_mode, fifo_reset, soft_reset |
| 0x004 | SMBUS_STATUS | RO | busy, errors, FSM state |
| 0x008 | SMBUS_COMMAND | RW | transaction type, command code, start, stop |
| 0x00C | SMBUS_SLAVE_ADDR | RW | target address |
| 0x010 | SMBUS_DATA | RW | single data byte, both directions |
| 0x014 | SMBUS_TX_FIFO | WO | TX FIFO write port |
| 0x018 | SMBUS_RX_FIFO | RO | RX FIFO read port |
| 0x01C | SMBUS_FIFO_STATUS | RO | levels and flags |
| 0x020 | SMBUS_CLK_DIV | RW | SCL divider |
| 0x024 | SMBUS_TIMEOUT | RW | SCL-low limit, 0 = disabled |
| 0x028 | SMBUS_OWN_ADDR | RW | slave address (stub) |
| 0x02C | SMBUS_INT_ENABLE | RW | interrupt mask |
| 0x030 | SMBUS_INT_STATUS | RW1C | sticky interrupt status |
| 0x034 | SMBUS_PEC | RW | PEC value |
| 0x038 | SMBUS_BLOCK_COUNT | RW | block length |

Field detail is not restated here - `peakrdl/smbus_regs.rdl` is the single
source of truth, and a second copy is what rots.

## Programming a transaction

1. `SMBUS_CONTROL`: set `master_en`, and `pec_en` / `fast_mode` if wanted.
2. `SMBUS_CLK_DIV` and `SMBUS_TIMEOUT`.
3. Load the data: `SMBUS_DATA` for a one-byte write, or `SMBUS_TX_FIFO` plus
   `SMBUS_BLOCK_COUNT` for a block write, or `SMBUS_TX_FIFO` twice for a word.
4. `SMBUS_SLAVE_ADDR`.
5. `SMBUS_COMMAND`: transaction type, command code, and `start`. **`start` is
   ignored unless `master_en` is already set** - the write is accepted and
   silently discarded, `busy` never rises and no error is reported. Enable
   master mode first.
6. Wait for `busy` to fall, then read the error bits. On a read, drain the RX
   FIFO (or read `SMBUS_DATA` for a single byte); for a block read, read
   `SMBUS_BLOCK_COUNT` first to learn how many bytes the slave sent.

## Known limitations

### What a real slave would need

The slave FSM is a stub. `cfg_slave_en`, `SMBUS_OWN_ADDR` and its enable are
kept in the register map so software can see what exists, but no slave FSM
runs and the block never claims the bus as a target.
`SMBUS_STATUS.slave_addressed` is tied low **deliberately**: a stub that
occasionally asserted would let the slave path clear the PEC accumulator or
drive SDA underneath a master transaction, which is the one thing a stub must
not do.

Implementing it needs, at minimum:

- **Passive bus monitoring** - START and STOP detection from the synchronized
  SCL/SDA inputs, independent of the master's own PHY, since the slave is
  clocked by someone else.
- **A receive path clocked by the incoming SCL**, not by the divider: the PHY
  as written generates SCL, and a slave has to follow it.
- **Address comparison** against `SMBUS_OWN_ADDR` plus the general-call address,
  and ACK generation inside the ninth bit.
- **Clock stretching as a producer** - holding SCL low while software is
  fetching the response byte, which needs a way for the sequencer to request a
  stretch rather than only tolerate one.
- **A second PEC accumulator, or arbitration for the one that exists**, since a
  slave transaction can begin while a master transaction is queued.
- **Ownership arbitration between the master and slave paths for SDA**, with a
  rule for what happens when software starts a master transaction while the
  block is being addressed as a target.
- **Alert Response Address (ARA) handling** if SMBALERT# is ever wired.

### What arbitration would need

Multi-master arbitration is not implemented and
`SMBUS_STATUS.arb_lost` is tied low. It needs:

- **Per-bit readback**: while transmitting a 1 (line released), sample SDA in
  the high phase; if it reads 0 another master is driving and arbitration is
  lost. The PHY already synchronizes SDA, so the sample point exists.
- **Immediate withdrawal** on loss - stop driving SDA and SCL within the same
  bit, without generating a STOP, because the winning master's transfer is
  still in progress.
- **Bus-free detection** (tBUF after a STOP) before attempting a START, which
  the PHY does not currently enforce.
- **A retry policy** in the sequencer, and a decision about whether a lost
  transaction is re-issued by hardware or reported to software.
- **Slave-path interaction**: a master that loses arbitration may immediately be
  addressed as a slave by the winner.

### Other

- Block Process Call is implemented as a block write followed by a repeated
  START and a block read; the two halves share `SMBUS_BLOCK_COUNT`.
- **Quick Command is always issued with R/W = 0 (write).** The read-direction
  Quick Command, which some devices use as a one-bit command, is not
  implemented; there is no register bit to select the direction.
- **A `start` written while `master_en` is clear is silently discarded** (see
  above). It is not reported as an error, so software that forgets to enable
  master mode sees a transaction that simply never happens.
- A slave-supplied block length of 0, or one larger than the FIFO depth, is
  clamped rather than honoured.
- SMBALERT# and the Host Notify protocol are not implemented.

## References

### SMBus Specification
- **SMBus 2.0:** System Management Bus Specification Version 2.0
- **I2C:** I²C-bus specification and user manual UM10204

### Project References
- **RTC Implementation:** `projects/components/retro_legacy_blocks/rtl/rtc/`
- **CDC rules:** `vault/handbook/design/cdc.md`
- **FIFO Infrastructure:** `rtl/common/fifo_sync.sv`
- **APB Infrastructure:** `rtl/amba/apb4/apb4_slave.sv`

### Related Tools
- **PeakRDL:** Register definition and generation framework
- **Cocotb:** Python-based verification framework

## Verification

`projects/components/retro_legacy_blocks/dv/tests/test_apb4_smbus.py`, run with

```bash
source env_python
cd projects/components/retro_legacy_blocks/dv/tests
make clean-all && make run-apb4_smbus-full
```

Six rows: `CDC_ENABLE` 0 and 1, each at gate, func and full. The suite covers
register access, every transaction type's programming, the FIFOs, the PEC, the
interrupt semantics, the timeout and the strict decode.

## License

MIT License - See LICENSE file for details

## Authors

- **Initial Implementation:** sean galloway (2024-2025)
- **Architecture:** Following RTLDesignSherpa methodology

---

**Last Updated:** 2026-09-09
**Status:** master implemented and regression-clean; slave mode and
multi-master arbitration are not implemented (see Known Limitations).
