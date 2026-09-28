# TASK-012: UART 16550 features deferred past the #60 fix

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-013** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3. Raised 2026-09-10 while fixing issue #60. None of these was
a defect; each was a 16550 feature this block advertised in its register map
but had never implemented.
**Status:** closed 2026-09-14. DONE 2026-09-10, commit 3d6bd04e0. All five landed together with
the MAS flip. Kept here as the record of what they were.

- **Character-timeout interrupt.** `int_timeout` is tied to 0, so IIR never
  reads 0x0C and there is no four-character-time timeout. Software polling a
  partially filled RX FIFO below the trigger level has no interrupt to wait
  for. Needs a receive idle counter in the baud-tick domain, the IIR encoding
  (already reserved) and the read-side clear.
- **Auto flow control (AFE).** MCR[5] does not exist; CTS does not gate TX and
  RTS is not driven from the RX FIFO level. Needs both halves plus the
  threshold rule.
- **1.5 stop bits** for 5-bit words (LCR[2] with a 5-bit character produces one
  stop bit today).
- **DLAB remapping.** The map is flat: DLL/DLM have their own offsets and DLAB
  is a stored bit that remaps nothing. Legal for this block and documented, but
  it is not what a driver written against a standard 16550 expects.
- **DMA mode select.** FCR[3] is stored and never read.


---
