# A transaction monitor keys its table by what the protocol lets the other side reuse

A passive monitor that tracks transactions in a slot table has to answer one
question per incoming message: which slot is this for? The naive answer, "the
slot whose request ID matches", is wrong whenever the protocol lets the
requester reuse that ID before the slot's debts are paid. It also silently
leaks slots whenever a legal flow finishes with a message the table did not
list as a completion.

## The failure that taught it

The first `chi_monitor_lite` (amba TASK-050, 2026-10-30) keyed every message
toward the requester by TxnID and every message from it by DBID, allocated
every request with one completion debt, and retired a slot when the debts it
knew about were zero. An RTL review against IHI 0050 H found seven ways a
common, spec-legal flow broke it before a single test ran:

- B2.5 lets the requester reuse a TxnID after CompDBIDResp while the write
  data (keyed by DBID) is still owed. A read reusing it then matched the old
  write slot, overwrote its DBID with the read's, and the write data arrived
  as four orphan errors with the slot stuck forever.
- A plain Comp carries the DBID a CompAck will use (B2.4.3), but only the
  DBID-class responses captured it. Every coherent store miss (CleanUnique with
  ExpCompAck) leaked a slot.
- Comp and DBIDResp have no stated order, so a Comp first retired the write
  before its DBID response and data.
- WriteNoSnpZero gets a DBID response and no data; PrefetchTgt gets nothing;
  CompStashDone and CompPersist are completions; SnpDVMOp is two flits with
  one TxnID and one response.

Each of these is a slot that never retires or retires early, and in a table
of eight that is a monitor that goes blind after eight transactions and then
reports everything as TABLE_FULL and orphans.

## How to apply

- Read the ID-reuse rule of the protocol first (CHI B2.4.2 / B2.5, AXI's
  per-ID ordering, ACE's snoop ordering). A match on an ID must be gated by
  "this slot still owes something addressed by that ID", so a reused ID lands
  on the new slot and the old one stays reachable only by its other key.
- Enumerate the debts per opcode class at allocation (completion, DBID
  response, read data, write data, CompAck) from the spec's flow tables, not
  from the common case. Every opcode that gets no response, or a different
  completion opcode, needs its own line.
- Any message that may legally land after the slot retired (ReadReceipt
  after the data) must not be an orphan.
- Capture the secondary key from every message that may carry it, latest
  wins, and arm it only when something will come back under it, or an unused
  field aliases a live key (a read's DBID of 0 against a write's DBID 0).
- Have the table reviewed against the spec BEFORE the testbench is written:
  the tests that followed were built from the same reading of the spec as
  the RTL and would have agreed with it. The review is cheaper than the TB
  and found what the TB would have encoded.

Related: [[new-monbus-protocol]], [[registered-status-outputs]], [[observers-do-not-drive]].
