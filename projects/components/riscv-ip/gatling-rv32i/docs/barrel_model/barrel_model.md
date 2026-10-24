# The Barrel Model: Why Four Contexts

**Version:** 0.1
**Date:** 2026-10-22
**Purpose:** The study chapter behind gatling (PRD 8.1): what kestrel's single
cycle costs, why cutting it into stages does not help one instruction stream,
and how four interleaved streams make the cut free.

---

## 1. The cost of one cycle

kestrel executes an RV32I instruction in one clock: the program counter, the
register-file read, the ALU, the data memory and the register write are one
combinational path. That is the teaching point of kestrel and it is also its
price. On the Nexys A7 the path that bounds the clock runs from the
instruction block RAM, through the register read and the ALU add, into the
data memory's address (kestrel MAS, "Board result"):

| kestrel, Nexys A7-100T | Value |
|---|---|
| Worst path at 100 MHz (IMPL=explore) | 11.6 ns |
| Clock closed | 75 MHz (+0.156 ns) |
| CPI | 1.039 (1.00 plus a cycle per load) |
| Throughput | 72.2 MIPS |
| LUTs | 1,899 |

: Table 1.1: kestrel's single cycle on the Nexys A7

Every instruction pays for the longest one. A shift, an add and a load all
wait the 11.6 ns that a load-address calculation needs.

## 2. The obvious fix, and why it does not pay for one stream

Cut the path into stages and clock it faster. Four stages -- fetch, decode,
execute, write back -- each hold a quarter of the work, so the clock could
rise toward four times kestrel's.

For one instruction stream the gain mostly evaporates. The next instruction
depends on this one: its operands may be this instruction's result (a data
hazard), and its address may be this instruction's branch target (a control
hazard). A pipelined single-stream core needs forwarding paths, hazard
detection, stall logic and branch prediction or flushes to keep the stages
busy (P&H §4.8-4.9; H&P6 App. C) -- the falcon-suite ladder above kestrel
exists to teach exactly that.
Without them, the simplest correct multi-cycle machine runs one instruction
at a time through all four stages: a CPI of 4 at up to four times the clock,
which is roughly where it started.

## 3. The interleave

gatling keeps the four stages and removes the dependence instead: the stages
are fed from FOUR independent instruction streams, one per hardware context,
taken in strict rotation.

This is fine-grained multithreading in the textbook sense -- switch threads
every cycle, in round-robin order (H&P6 §3.11; P&H §6.4; H&H §7.7.7) -- and
it is older than the pipelining vocabulary used to describe it. Thornton's
CDC 6600 ran ten peripheral processors through one shared execution unit
this way in 1964 (papers, entry 16; H&P6 App. M.5); the Denelcor HEP used it
to hide pipeline and memory latency with no forwarding and no caches (papers,
entries 17 and 18); the Tera MTA pushed it to 128 streams (papers, entry
19); Sun's Niagara brought it back as a four-thread core (papers, entry 20).
The textbooks present the interleave as a way to *hide* stalls. gatling uses
it to *remove* hazards, which is what happens when the number of streams is
fixed equal to the number of stages:

```
cycle     t     t+1   t+2   t+3   t+4   t+5
F        c0    c1    c2    c3    c0    c1
D              c0    c1    c2    c3    c0
X                    c0    c1    c2    c3
W                          c0    c1    c2
```

Every cycle each stage holds a different context. Context c0's next
instruction is fetched at t+4, after its current one has written its PC (end
of X, t+2) and its register (end of W, t+3). So:

- no data hazard -- a context never reads a register that an instruction of
  its own still in flight is about to write;
- no control hazard -- a branch resolves before that context's next fetch,
  so there is nothing to predict and nothing to flush;
- no forwarding, no stalls, no interlocks for the base ISA.

Each context still takes four cycles per instruction (CPI 4), but four of
them retire one instruction each per four cycles: the core retires one
instruction per clock. The multi-cycle cut costs nothing when there are four
streams to fill it -- the kestrel to merlin lesson inverted: instead of
pipeline stages hiding latency for one stream, contexts hide it for each
other.

## 4. What the four stages buy in memory

Each stage is one block-RAM latency long, and that is not a coincidence the
design has to work around; it is what the design uses:

| Memory | Address presented | Data used |
|---|---|---|
| Instruction RAM | F | D |
| Register file (block RAM) | D | X |
| Data RAM (load) | X | W |

: Table 4.1: every memory latency is exactly one stage

kestrel has to hold the core for a cycle on every load (`mem_wait`) because
its block RAM answers a cycle late. gatling has no wait signal at all.

## 5. What it costs

- Four PCs and four register files instead of one -- the "cheap
  replication" (PRD 4.1). Harris and Harris make the same point:
  multithreading "replicates only the PC and register file, not the
  execution units and memories" (H&H §7.7.7). The register files are one
  128-entry block RAM (two copies for two read ports), not 4,096 flops.
- One datapath: decode, immediates and ALU are kestrel's, unchanged.
- A context is a quarter of the machine. A single program runs at a quarter
  of the clock rate -- the fine-grained trade as Hennessy and Patterson
  state it, multithreaded throughput bought with single-thread latency
  (H&P6 §3.11), and what Jordan measured on the HEP (papers, entry 18).
  The barrel pays off only when there are four things to do -- which, for
  a tetrad of four cells, is the point.

## 6. Measured

On the same Nexys A7-100T (gatling board README, "Board result"; MAS
chapter 7):

| | kestrel | gatling |
|---|---|---|
| Worst path | 11.6 ns (the whole instruction) | 9.4 ns (the X stage) |
| Clock | 75 MHz | 100 MHz |
| Programs at once | 1 | 4 |
| CPI per program | 1.039 | 4.004 |
| Peak throughput | 72.2 MIPS | 100 MIPS |
| LUTs | 1,899 | 2,281 |

: Table 6.1: The single cycle against the barrel

Four harts cost 20% more logic and run 39% more instructions per second in
total, with every instruction taking the same four clocks. The clock did not
rise fourfold: the X stage -- register read through ALU or branch to the next
PC -- is still most of kestrel's instruction, and routing is half of the
worst path (52%) on this part. The remaining stages have slack to give, which is where a
deeper rotation would go, as the HEP's eight-stage pipeline and Tera's 128
streams did (papers, entries 17 and 19).

## 7. Sources

Citations follow the suite's conventions (kestrel study book, chapter 1,
"Conventions"): the ISA by section of the pinned manual, papers by entry in
`references/microarchitecture-papers.md`, textbooks by edition and section.

| Key | Source |
|---|---|
| H&P6 | J. L. Hennessy and D. A. Patterson, *Computer Architecture: A Quantitative Approach*, 6th ed., Morgan Kaufmann, 2019. §3.11 "Multithreading: Exploiting Thread-Level Parallelism to Improve Uniprocessor Throughput"; Appendix C "Pipelining: Basic and Intermediate Concepts"; Appendix M.5 "The Development of Pipelining and Instruction-Level Parallelism" |
| P&H | D. A. Patterson and J. L. Hennessy, *Computer Organization and Design, RISC-V Edition*, 2nd ed., Morgan Kaufmann, 2021. §4.8 "Data Hazards: Forwarding versus Stalling"; §4.9 "Control Hazards"; §6.4 "Hardware Multithreading" |
| H&H | S. L. Harris and D. M. Harris, *Digital Design and Computer Architecture, RISC-V Edition*, Morgan Kaufmann, 2022. §7.7.7 "Multithreading" |
| papers, entries 16-20 | Thornton 1964 (CDC 6600); Smith 1978 and Jordan 1983 (HEP); Alverson et al. 1992 (Tera MTA); Kongetira et al. 2005 (Niagara) |
| kestrel MAS | Chapter 7, "Board result": the kestrel column of Tables 1.1 and 6.1 |

: Table 7.1: Sources cited in this chapter
