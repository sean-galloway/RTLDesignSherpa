# TASK-005: bus error handling -- load/store access faults on AXI SLVERR / DECERR

**Priority:** P3
**Status:** closed 2026-11-27 (filed 2026-11-25; owner: "add a task for the future for error handling"; started 2026-11-27 with the owner's four decisions below; the WB deviation accepted by the owner 2026-11-27: "yes, commit 5")
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im TASK-002)

## Why

PRD §3 and §4.3 planned load and store access faults on an AXI error
response. They were never built: `peregrine_uc_axi` ignores `rresp` /
`bresp`, the I$ ignores `rresp`, amber does not report an error on its CPU
port, and the core has no cause 5 / 7 path. The PRD was amended to the
RTL on 2026-11-25; this task is the future work.

## What

- Load access fault (cause 5) and store/AMO access fault (cause 7), with
  `mtval` = the faulting address, taken precisely at MEM like the other
  synchronous traps (§4.3).
- Sources: the uncached port (`rresp` / `bresp` of SLVERR or DECERR) and
  the D$. The D$ needs amber to return an error on its CPU response for a
  fill or write-back that failed: a cache-ip change, to be filed against
  cache-ip/amber-mesi-l1 when this task starts, with its own decision on
  what a failed write-back of a dirty line means.
- Decide whether an instruction access fault (cause 1) on an I$ fill error
  is in scope; PRD P6 left it out.
- RVFI reports the trap with its cause; the shadow CSR model and spike
  lockstep (which needs a way to see the same error) learn it.

## Done when

- A directed test drives error responses on each source and checks the
  trap, `mepc`, `mcause` and `mtval`; a mutant dropping each source is
  caught.
- PRD §3 and §4.3 are amended back to "built"; the HAS/MAS trap chapters
  describe it.
- peregrine FULL, amber FULL and the formal suites are green.

## Owner decisions (2026-11-27)

1. Load access fault (5) and store/AMO access fault (7), `mtval` = the
   faulting address, precise; sources the uncached port and amber fills.
2. Instruction access fault (1) in scope (PRD P6 changes): a failed I$
   refill installs nothing; the fetch traps precisely, `mtval` = its PC.
3. A failed write-back of a dirty line: amber drops the line, latches its
   address in a sticky status and raises an interrupt (imprecise).
   Built as platform interrupt 16 (`mip.16` / `mie.16`) plus the custom CSR
   `mbuserr` (0x7C0): read {line address[31:2], overflow, valid}, any
   write clears.
4. The uncached window a parameter (`UC_BASE` / `UC_MASK`), defaults
   unchanged.

## As built (2026-11-27)

- **Where the D-side fault is taken.** The response, and so the error,
  arrives in WB (the registered-read contract). An error response holds
  the core one more cycle and does not free the port (`w_rsp_ok`); it is
  captured on the held side (`r_have_err` / `r_mem_err`) and presented as
  `dmem_fault`; WB retires as the trap beat and MEM's instruction is
  killed. Precise, but taken at WB rather than MEM: the one deviation from
  decision 1's "at MEM", for the reason above (holding every access in MEM
  would cost every hit a cycle). MEM's data request is blocked by the
  wrapper, not in the core, to keep the fault off the 75 MHz accept cone
  (gating it in the core cost one LUT level: `MUL_DSP=1` +0.329 -> +0.015).
- **I$**: `S_FAULT`; `fetch_fault` for every fetch from the failed line;
  the set's valid bit cleared; invalidate taken in `S_FAULT`.
- **amber**: cache-ip/amber-mesi-l1 TASK-008 (`BUS_ERR_EN=1`).
- **OKAY behaviour unchanged**: clint / smc / io / irq / irq_lock, both
  stall variants (seed 1), identical tohost / beats / cycles to HEAD
  (`ef73a6e3f`'s tree, archived), and amber_latency unchanged.
- **DV**: `test_peregrine_buserr` (`buserr_sync.s` in spike lockstep with
  tval locked; `buserr_wb.s`); the shadow trap-CSR model (`csr_shadow.py`);
  the request count includes access faults; the I$ unit test gained four
  fault phases. Spike sees the same faults on addresses it leaves
  unmapped (TB error windows by address bits 27:24).
- **Mutants** (each caught, each reverted byte-identical): uc read error,
  uc write error, amber fill error, I$ fill error, amber write-back error,
  core ignores irq 16, error response frees the port, WB fault does not
  kill MEM, wrapper presents MEM's request in the fault cycle.
- **Gates**: peregrine FULL 94/94, amber FULL 127/127, common-ip FULL
  255/255, no reruns; formal below; OOC below.
- **PRD** §3 / §4.3 / P6 / P7 amended to "built". Board rigs: none
  instantiate peregrine; the amber, jet and ref Genesys2 rigs keep
  `BUS_ERR_EN` / `RSP_ERR_EN` at their default 0.
- **Owner ruling (2026-11-27)**: D-side access faults are taken at WB,
  precise, as built above; spike has no `mbuserr`, so `buserr_wb.s` is
  checked by the program, the trace rules and the shadow model, not lockstep.
- **Formal** (final RTL): `top_props` prove (BMC 28) PASS and cover 14/14
  (new: the D-side queue requires an error-answered access to retire as a
  5 / 7 trap of the right kind and an OKAY one never to; the fetch property
  admits the insn-0 beat of a faulted fetch; RRESP / BRESP, amber's error
  bit and wb_err status free); `core_props` prove + cover PASS;
  riscv-formal 52/52 on both `MUL_DSP` builds; amber_control prove, live,
  cover PASS. The first top_props run failed `ap_i_fetch_word` on an
  interrupt taken on a faulted fetch (insn 0, refetched after `mret`):
  correct behaviour, property narrowed.
- **OOC** xc7a100t-1, 13.333 ns, 0.2 ns uncertainty (same script on HEAD
  and on the change): `MUL_DSP=0` +0.270 (HEAD +0.375), `MUL_DSP=1`
  +0.320 (HEAD +0.329); 15 levels as on HEAD; 4,943 LUT / 3,058 FF.
