# TASK-006: RISC-V SoC on pumice, running memory-controller stress benchmarks

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/open.md` as **NEXYS-006** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** Medium
**Status:** [ ] Open (2026-08-31)
**Source:** Sean, 2026-08-31 — "Is there a riscv cpu we could drop in and run
real benchmarks?", clarified: "By benchmark, I mean a program specific to
stress in MC's."

**Goal:** Put a cached RISC-V core in front of pumice on the Nexys A7 and run
programs written to stress a memory controller, so pumice is exercised by real
software-generated traffic and can be compared against LiteDRAM on the same
board with the same binaries.

**Why this is worth doing even though the generator array exists.** The
generators ([[NEXYS-004]]) are the better *instrument*: bank, stride, burst
length, direction mix and outstanding depth are all dialed exactly. What they
are not is *evidence that real software works*. The counter-argument to a CPU
— that a cache hierarchy sits between the program and the DRAM and obscures
the pattern — does not apply to this class of benchmark, because an MC-stress
program is specifically built to defeat caches and prefetchers. When the
working set is several times the last-level cache and the access pattern is
either streaming or random, the traffic arriving at the controller IS the
traffic the program asked for. That is the whole design intent of these
benchmarks, and it is what makes them usable here.

**The core must have a data cache that does line fills.** This is the one
hard constraint and it eliminates most small cores. A cacheless core
(PicoRV32, Ibex in its default configuration) issues single-word accesses, so
the controller sees single-beat traffic: bank-parallel scheduling, paging
policy and the read-return path are all barely engaged, and the measurement
degrades into a core-latency test. The requirement is AXI burst traffic from
cache line refill and writeback.

**Proven path, and it is cheap.** LiteX + VexRiscv already runs on this exact
board with LiteDRAM — that is the build which proved board, PHY, pins and DRAM
all good ([[project_litedram_ref_proves_board]], 128 MiB @ 300 MT/s memtest,
recipe in `/tmp/nexys_ddr2_memtest.py` + `litex-venv310`). Swapping LiteDRAM
for pumice behind the same port yields the CPU SoC *and* the long-wanted
pumice-vs-LiteDRAM A/B in one move, with identical binaries on both sides —
which is the only way that comparison is honest.

Area is not the obstacle. VexRiscv with 4 KB I$/D$ is roughly 3-5k LUTs
against the XC7A100T's 63400. For scale: the 8+8 generator array cost ~48k
LUTs and did not fit (66470 LUTs; placement short 1469 slices), which is why
the harness is 4+4. A CPU is far cheaper than the array it would sit beside.

**The benchmarks — MC-stress, not CPU benchmarks.** CoreMark, Dhrystone and
Embench are cache-resident and measure the core; they say essentially nothing
about a memory controller and are explicitly out of scope. The set worth
porting, each chosen for a different controller behaviour:

- **STREAM** (copy / scale / add / triad) — sequential read+write bandwidth
  with a working set several times the cache. The canonical bandwidth number,
  and directly comparable against published figures. Exercises page hits and
  the write path.
- **GUPS / HPC-Challenge RandomAccess** — random single-word updates across
  the whole 128 MiB. Maximum row/bank thrash and the worst case for page
  policy; this is the benchmark that should separate the Axis-2 paging modes
  ([[TASK-002]]) if anything does.
- **Pointer chase** (lmbench `lat_mem_rd` style) — dependent-load latency as a
  function of working-set size. Walks the cache hierarchy and then exposes
  tRCD/CL and the read-return path directly; a latency curve is the natural
  companion to a bandwidth number.
- **TinyMemBench** — small, portable C, gives bandwidth and latency together;
  the cheapest thing to stand up first on bare metal.
- **A read/write mix loop** — the software analogue of NEXYS-004's mix sweep,
  so tWTR/tRTW turnaround is paid by real traffic and the two curves can be
  laid over each other.

**What this does NOT replace.** The generator array stays. It isolates
scheduler behaviour in a way no program can, because it can hold every
variable but one fixed. This task adds realism and a comparison baseline; it
does not retire the instrument.

**Open questions to settle before starting:**
1. **Coexist or replace?** Does the CPU SoC live alongside the char harness in
   one bitstream (area and timing pressure on a part that is already tight) or
   as its own separate build sharing pumice? Separate build is the obvious
   first answer, but then the perf counters and the observer slot need to be
   reachable from it.
2. **Where does code live?** BRAM for text/stack with DDR2 as the benchmark
   arena keeps the measurement clean — instruction fetch traffic would
   otherwise contaminate every number. Recommend BRAM for code.
3. **Bare metal or Linux?** Bare metal is enough for all five benchmarks and
   avoids MMU configuration, page-cache effects and a much larger core. Linux
   only if the goal shifts to "boots an OS", which is a different claim.
4. **Which cache line size and outstanding depth**, since these set the burst
   shape pumice actually sees and therefore how comparable the numbers are to
   the generator sweeps.

**Deliverables:** the SoC build under `projects/fpga-systems/NexysA7/pumice/`,
a bare-metal BSP, the ported benchmark set, and a results table against
LiteDRAM on the same board with the same binaries.

---
