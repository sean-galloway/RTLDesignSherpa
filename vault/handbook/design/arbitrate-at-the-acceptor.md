---
title: Arbitrate where the request is accepted
summary: A round-robin pick that feeds a queue in front of a slow slave stops being round-robin; each master's share then follows its outstanding count.
---

# Arbitrate where the request is accepted

- **Make the pick at the point that accepts the request, with nothing
  queued after it.** An arbiter that grants into a FIFO, skid or register
  stage ahead of the slave decides who goes next whenever a stage slot
  frees, not when the slave can take a request. Behind a slave that holds
  READY low, the stage stays full of requests that have already won, and the
  master that always has one waiting takes every freed slot. A master with
  few transactions in flight is between requests at those moments, so its
  share tracks its outstanding count instead of the round-robin. Fair
  arbitration needs the losers' requests to still be waiting when the
  slave accepts: per-master request slots in front of the pick, the pick
  straight onto the slave-side nets.
- **A slave that accepts the address only once its data is in is the case
  that exposes it.** LiteDRAM takes an AW only after that burst's W is in
  its buffer, so every AW handshake waits a burst. A BFM memory that accepts
  AW at once hides the effect entirely: in simulation both fabrics gave the
  same share, on the board they did not.
- **A fix measured in one bench is not a fix in another bench's report.**
  Re-run every benchmark that reported the symptom, and record the result
  there, before the report goes out again.
- *Case (2026-10-16 .. 21, bridge / fabric benchmark W3): two writers into
  the Genesys 2 DDR3, the injector limited to 2 outstanding, got 40% through
  the generated bridge and 50% through the AXI Crossbar. The bridge's
  arbiter fed the DDR adapter's 2-deep AW skid. Bridge commit 73467609f
  (2026-10-17) moved the pick to the slave pins from per-master slots, and
  the bridge's perf suite went 0.34 -> 0.50 against a slave taking two at a
  time -- but the benchmark kept reporting 40% as an open root cause for
  four days because nobody re-ran it. A board bisect (leg A rebuilt from each
  commit's own tree: 40.0% at c98ed071e, 50.0% at 73467609f) settled it; the
  first guess, the BUG-020 W bypass three days later, was wrong.*
