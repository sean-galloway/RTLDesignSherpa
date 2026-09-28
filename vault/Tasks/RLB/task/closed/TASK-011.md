# TASK-011: SMBus features deferred past the #58 fix

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-011** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3. Raised 2026-09-10 while fixing issue #58 (master engine
rewrite). None of these is a defect in the master path; each is a feature
the block advertises in its RDL/MAS header but has never implemented.
**Status:** closed 2026-09-14. DONE. Arbitration and the read-direction quick command landed
2026-09-10 in 6978cf935, and target mode the same day.

- ~~**Slave mode.** `SMBUS_OWN_ADDR` and `slave_addr_int` exist; the slave FSM
  is a stub that never ACKs. The rewrite keeps it inert (it cannot touch SDA,
  the PEC accumulator or the master sequencer). A real slave needs: address
  match on the bus-sampled address byte (incl. general call / ARP if
  wanted), an ACK/NAK policy, an RX path into the RX FIFO with its own
  interrupt, a TX path from the TX FIFO for reads addressed to us with
  clock stretching while software fills it, PEC check/generate on the slave
  side, and arbitration with the master half for the shared pins (one
  engine on the wire at a time).~~ FIXED: `smbus_slave_engine.sv` is a
  separate module because the master owns the clock and a target does not --
  every target action is a response to an edge somebody else produced. It
  does address match (own address plus the general call behind
  `SMBUS_SLAVE_CTRL.gc_en`), an ACK policy (NAK the address when software
  says it is busy, NAK a data byte when the RX FIFO is full), the RX path
  into the shared RX FIFO, the TX path out of the shared TX FIFO with
  optional clock stretching while software fills it, its own PEC accumulator,
  and three new interrupt sources. ARP is still not implemented and is now
  recorded as a limitation rather than as deferred work.

  Two design points worth keeping. The target PEC NEVER COUNTS BYTES: a
  correct trailing PEC drives a CRC-8 to zero, so a write is checked by
  testing the running value at the STOP, and a read sends the running value
  once the queue is dry. And the ownership claim is "our target is
  ANSWERING", not "the bus is busy" -- claiming the wire for every observed
  START also claims it for a stuck one, since SDA held low under a high SCL
  looks exactly like a START that never ends, and the master could then never
  run the bus recovery that exists to clear it. That was caught by the
  existing GH58-R3-6 recovery test going red on the first, broader rule.

- **The framework's SMBusMaster BFM cannot see a clock stretch.** It releases
  SCL and then waits a fixed delay, so a stretching target is clocked straight
  through. The RLB smbus TB carries its own `ExternalSMBusMaster` that waits
  for SCL to actually read high, because slave mode is the feature stretching
  exists for. Worth fixing in RDS-DV so every block gets it.
- ~~Multi-master arbitration.~~ FIXED 6978cf935: every transmitted bit is
  read back in the SCL-high phase, and a 1 that reads as 0 means another
  master won. On loss both lines are released within the bit and the
  sequencer reports `arb_lost` and idles WITHOUT framing a STOP, because the
  winner's transfer is still in progress. Retry is software's.
- ~~Quick Command with R/W=1.~~ FIXED 6978cf935: transaction type 0xA is the
  read-direction form. The R/W bit IS the payload of a quick command, so each
  direction has its own code rather than a direction bit that would mean
  nothing for the other nine types.

---
