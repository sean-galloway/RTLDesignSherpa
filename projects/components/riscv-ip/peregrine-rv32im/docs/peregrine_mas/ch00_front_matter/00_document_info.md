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

# Document Information

## PEREGRINE-RV32IM Micro-Architecture Specification

**Document Number:** PEREGRINE-MAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Micro-Architecture Specification (MAS) describes the internal implementation of the peregrine-rv32im core as built by riscv-ip/peregrine-rv32im TASK-001: every block, the pipeline-register records, and the cycle rules for prediction, traps, the M unit, the D side and `fence.i`. Its center is the predictor, trap and M-unit chapters (PRD §7).

**Target Audience:**
- RTL designers modifying the core or reusing its blocks (gyrfalcon reuses the predictor, trap machinery, L1s and fabric)
- Verification engineers writing directed tests and formal properties
- Readers comparing peregrine against merlin

**Companion Documents:**
- PEREGRINE-RV32IM Hardware Architecture Specification (HAS) - External view: ISA, ports, contracts, performance

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | PEREGRINE HAS v0.1 | Hardware Architecture Specification (companion) |
| [REF-2] | peregrine PRD 0.2 (`projects/components/riscv-ip/peregrine-rv32im/PRD.md`) | Requirements; decision rows cited as "P<n>" |
| [REF-3] | RISC-V Instruction Set Manual, Volumes I and II | ISA and privileged authority |
| [REF-4] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI field semantics |
| [REF-5] | amber MAS (`projects/components/cache-ip/amber-mesi-l1/`) | The D\$: CPU port, clean-all, AXI4 master |
| [REF-6] | riscv-ip/peregrine-rv32im TASK-001 (`vault/tracking/projects/components/riscv-ip/peregrine-rv32im/task/closed/TASK-001.md`) | Build record: decisions, measurements, mutants |
| [REF-7] | MERLIN MAS v0.1 | The five-stage pipeline peregrine extends |
| [REF-8] | Patterson and Hennessy, *Computer Organization and Design*, RISC-V edition (COD) | Fig 4.65 (2-bit predictor), §3.3-3.4 (multiply, divide), §5.4 (memory stalls) |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| Bubble | A pipeline record with `valid = 0`; its payload is stale and is never read |
| Commit point | MEM: traps, `mret`, `fence.i`, CSR writes and stores take effect here |
| Control field | A pipeline-register field that resets and flushes (`valid`, `rd_wen`, ...) |
| Early response | A D-side response that arrives while the core is held, captured by the wrapper |
| Hold | `mem_wait` high: no state element in the core updates |
| Hold-in-EX | An M instruction stays in EX until the M unit is done; the front end stalls |
| Payload | A pipeline-register field with no reset or flush, read only under `valid` |
| Redirect | A change of the fetch PC away from the predicted path: EX (mispredict) or MEM (trap, `mret`, `fence.i`) |
| `_nw` | "No wait": a signal computed as if `mem_wait` were low, for consumers that apply `mem_wait` themselves |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-11-25 | seang | Initial MAS for the RTL at the close of TASK-001 (stages 1-7): blocks, package records, pipeline cycle, hazards, the predictor and its write rule, traps and the interrupt rules, the M unit, the D-side request / hold / capture rules from stage 7, `fence.i`, RVFI, the verification hooks and configuration. Port and parameter tables are generated from the RTL by `gen_port_tables.py`. |

: Document Revision History

---

**Last Updated:** 2026-11-25
