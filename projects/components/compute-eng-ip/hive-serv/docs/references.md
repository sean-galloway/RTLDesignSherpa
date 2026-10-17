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

# HIVE Reference Library

Compiled 2026-10-13 from the owner-calibre hardware catalogue (marked **[lib]**)
plus the specifications, papers, and open-source projects the hive_spec
drafts cited and the repo already relies on. Annotations say what each
reference is *for* in HIVE terms.

## 1. Network-on-Chip and interconnect (the fabric domain)

| Reference | In library | Serves HIVE as |
|---|---|---|
| Dally & Towles, *Principles and Practices of Interconnection Networks* (Morgan Kaufmann, 2003) **[lib]** | yes | Routing algorithms, credit/on-off flow control, VC design — the theory under delta's routing and the cell 3-D QoS fabric; cited by the original hive spec as the foundational text |
| Duato, Yalamanchili & Ni, *Interconnection Networks* (Morgan Kaufmann) **[lib]** | yes | Deadlock-freedom theory for dimension-ordered / VC routing — the formal basis of delta's "2 VCs make XY deadlock-free" claim and of cell's future 3-D routing rules |
| *Networks on Chip* (Morgan Kaufmann) **[lib]** | yes | NoC survey-level background: topologies, switching, NoC design space |
| Ni & McKinley, "A Survey of Wormhole Routing Techniques in Direct Networks" (IEEE Computer, 1993) | paper | Wormhole vs store-and-forward, router microarchitecture |
| Kwon et al., "MAERI" (ASPLOS 2018) | paper | Reconfigurable-interconnect motivation for topology switching (HIVE's virtual contexts; cell's CGRA lineage) |
| Ogras & Marculescu, "Analytical Modeling of NoC Performance" (IEEE TCAD 2006) | paper | Validation approach for HIVE's SimPy performance models (predict within ±10%) |
| Jiang et al., Booksim 2.0 | tool | NoC simulation methodology reference |

## 2. Packet and network processors (HIVE-C's real job)

| Reference | In library | Serves HIVE as |
|---|---|---|
| Franklin, Crowley, Hadimioglu & Onufryk, *Network Processor Design: Issues and Practices* (Morgan Kaufmann) **[lib]** | yes | **The closest analog to HIVE-C in the library**: programmable control of packet flows. Queueing disciplines (deficit round-robin, VOQ), flow classification, and pipeline organization for packet processing map directly onto the descriptor scheduler (HAS §5.2) and the SERV injection paths |
| ProNoC / OpenSMART (open-source NoC generators) | tool | Router/NI worked examples; regeneration-discipline precedent for delta |

## 3. RISC-V and processor architecture

| Reference | In library | Serves HIVE as |
|---|---|---|
| Hennessy & Patterson, *Computer Architecture: A Quantitative Approach* **[lib]** | yes | Performance analysis, memory hierarchy, interconnect design |
| Hennessy & Patterson, *Computer Organization and Design, RISC-V Edition* **[lib]** | yes | ISA + pipelining grounding for the falcon-ladder context HIVE's cores come from |
| Harris & Harris, *Digital Design and Computer Architecture, RISC-V Edition* **[lib]** | yes | The pedagogical line kestrel/merlin descend from — the ladder HIVE borrows its cores from |
| Shen & Lipasti, *Modern Processor Design: Fundamentals of Superscalar Processors* **[lib]** | yes | The peregrine→gyrfalcon material; background for the CORE_FLAVOR experiment (a more capable RV in the master socket) |
| Zhang, *RISC-V Architecture and DSP Processor Design* **[lib]** | yes | End-to-end RISC-V SoC integration example |
| Ledin, *Modern Computer Architecture and Organization* **[lib]** | yes | Survey-level architecture reference |
| RISC-V Unprivileged + Privileged ISA specifications (riscv.org) | spec | ISA authority (RV32IM master, RV32I SERV) |
| VexRiscv (github.com/SpinalHDL/VexRiscv) · SERV (github.com/olofk/serv) | code | The imported cores themselves; `vendor/vexriscv`, `vendor/serv` carry pinned copies |

## 4. SoC integration and memory systems

| Reference | In library | Serves HIVE as |
|---|---|---|
| Maaref, *Architecting and Building High-Speed SoCs* **[lib]** | yes | FPGA SoC bring-up practice — HIVE+RAPIDS+delta integration on the NexysA7 PoC |
| Chinnakonda, *Designing a Multiprocessor Cache Subsystem* **[lib]** | yes | Shared-memory + coherency background (RAPIDS/amber side of the compute system) |
| Mohammad, *Embedded Memory Design for Multi-Core and SoC* **[lib]** | yes | On-chip memory organization — HIVE-C's tightly-coupled 32 KB I/D, SERV 2 KB memories |
| ARM AMBA specs: AXI4 (IHI 0022), AXI4-Stream (IHI 0051A) | spec | The interface contracts (AXIS-only rule, AXIL registers) |

## 5. Modeling and verification

| Reference | In library | Serves HIVE as |
|---|---|---|
| Bailey & Martin, *ESL Models and their Application* **[lib]** | yes | Transaction-level modeling discipline for the control plane — the HAS §7 SimPy models should read like this book's methodology |
| Salemi, *Python for RTL Verification* **[lib]** | yes | The cocotb+pyuvm stack the hive dv suites are built on |
| Salemi, *The UVM Primer*; Cooper, *Getting Started with UVM* **[lib]** | yes | Verification methodology background |
| cocotb docs · rds-dv (cocotb-framework) | tool/docs | The actual framework under `hive-serv/dv/tests` |

## 6. FPGA platform practice

| Reference | In library | Serves HIVE as |
|---|---|---|
| Chu, *FPGA Prototyping by SystemVerilog Examples* **[lib]** | yes | The repo's SystemVerilog idiom in book form |
| Merrick, *Getting Started with FPGAs* **[lib]** | yes | Board-level orientation for the NexysA7 PoC |
| Deschamps, Sutter & Cantó, *Guide to FPGA Implementation of Arithmetic Functions* **[lib]** | yes | Arithmetic implementation options (math-area synergy) |
| Woods et al., *FPGA-based Implementation of Signal Processing Systems* **[lib]** | yes | Pipelined-streaming design on FPGAs — the data-path style RAPIDS/cell follow |
| Roy, *Advanced Digital System Design* **[lib]** | yes | General advanced RTL practice |
| Vivado / Quartus tool docs; NexysA7 100T, Genesys2, DE10 Standard | tools | The PoC/production platforms from the HAS |

## Ideas the library suggests for HIVE (explored 2026-10-13)

Explored in depth with owner input — see
[design-notes/kick-flow-fifo-deadlock-tlm.md](design-notes/kick-flow-fifo-deadlock-tlm.md)
(kick-vs-pacing separation, FIFO sizing framework, deadlock obligations,
TLM measurability). In brief:

1. **Descriptor scheduling as network-processor queueing** (Franklin et al.):
   the HAS §5.2 four-level scheduler is a classic NP queueing problem — deficit
   round-robin within levels and virtual output queues per RAPIDS channel are
   proven disciplines worth stealing when the scheduler firms up.
2. **Credit-flow-control analysis** (Dally & Towles ch. on flow control) for
   the SERV injection FIFO depths — MAS §1.2's depth-2/4 choices are currently
   by rule of thumb; the book gives the analysis to justify or revise them.
3. **Deadlock-freedom proof obligations** (Duato) as delta grows from crossbar
   toward cell's 3-D QoS-routed fabric — write the routing-function
   restrictions before the fabric, not after a deadlock shows up in sim.
4. **TLM discipline for the SimPy models** (Bailey & Martin): model the
   control plane at transaction level (descriptor = transaction) so the ±10%
   model-vs-RTL validation target in the HAS is measurable.

---

**Maintenance**: new references land here and get linked from the HAS
document-info REF table and the PRD §14; the calibre library is the owner's —
`[lib]` rows were confirmed present 2026-10-13.
