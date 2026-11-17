---
title: In a shift queue, write the push after the pop's shift
summary: A small FIFO kept as a shift register pops by shifting every entry down and pushes by writing entry [count]; when both happen in one cycle the shift loop also assigns the entry the push is writing, and whichever nonblocking assignment comes LAST in the block wins. Put the push after the shift, index it by count minus pop, and pin the same-cycle case in a test. jet_prime_pair_fabric snoop queues, 2026-11-16.
---

# In a shift queue, write the push after the pop's shift

**Rule:** a queue kept as a shift register has two writers of the same
element in the same `always_ff`: the pop (a loop that shifts every entry
down one place) and the push (one write at the tail). When a push and a
pop coincide, the pop's loop assigns `q[count-1]` too -- with the value
from `q[count]`, which is stale -- and the push's write to that same index
must be the LATER nonblocking assignment in the block or it is lost. Write
the push **after** the shift loop, index it with `count - pop` (the tail
after the shift), and update `count` with `count + push - pop`. Then write
the test that pushes and pops in the same cycle; a queue that only ever
sees one or the other never shows the bug.

The same rule covers every "shift then write" structure: a snoop-order
FIFO, an issued-but-unanswered list, a scoreboard that compacts on retire.
If the push lives in a different `if` block from the pop -- say the push
in the grant block near the top of the `always_ff` and the pop in the
channel block further down -- the code reads correctly and simulates
wrong, because the file order of two unrelated-looking blocks decides
which assignment lands.

## The failure that taught it (jet_prime_pair_fabric, 2026-11-16)

The pipelined pair fabric keeps two shift queues per peer: the slots
awaiting an AC (pushed at the grant, popped at the AC handshake) and the
ACs accepted but not yet answered (pushed at the AC handshake, popped at
the CR). Both pushes were written in the block that produced them, above
the shift loops. The first gate cell deadlocked in the deep-pipelined
scenario: seven transactions live with no snoop queued or outstanding and
a memory beat held forever with no verdict. A grant in the cycle of an AC
handshake lost its snoop (the shift overwrote the pushed slot, so that
transaction was never snooped and never completed), and an AC handshake
in the cycle of a CR mis-paired the next verdict with the wrong slot. The
hang trace said the structure: `snq 0/0 sni 0/0 live [...]`. Moving both
pushes below their shift loops cleared it; the gate suite then passed
without another RTL change.

**Reviewer's tell:** a shift-register queue whose push and pop are in
different `if` blocks, or whose push indexes `q[count]` rather than
`q[count - pop]`.

Related: [[credit-tokens-count-every-event]] (the counter form of the
same same-cycle pairing), [[always-comb-block-fusion]].
