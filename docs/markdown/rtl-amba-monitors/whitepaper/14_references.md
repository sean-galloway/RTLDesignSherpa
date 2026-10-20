# References

Ocelus is an original design of this repository. The papers and standards
below are related work for comparison, not sources of the design; protocol
specifications define the rules the monitors observe. Where a local PDF
exists it is indexed in `rtl/amba/references/README.md`; the handbook's
citation convention keeps the papers in that central store and the
per-chapter usage notes here.

## Interconnect monitoring (the closest relatives)

- Ciordas, C., Basten, T., Rădulescu, A., Goossens, K., van Meerbergen, J.
  "An Event-Based Monitoring Service for Networks on Chip." *ACM Trans.
  Design Automation of Electronic Systems*, 10(4):702-723, Oct. 2005. DOI:
  [10.1145/1109118.1109126](https://doi.org/10.1145/1109118.1109126) —
  probes, events and monitoring traffic on the interconnect; reconfigurable
  probes with a run-time programming model; probe area at 17-24% of NoC
  area, the number Ocelus' lite posture undercuts (chapters 2, 8, 10).
- Ciordas, C., Goossens, K., Basten, T., Rădulescu, A., Boon, A.
  "Transaction Monitoring in Networks on Chip: The On-Chip Run-Time
  Perspective." *Proc. IEEE Int. Symp. Industrial Embedded Systems
  (IES 2006)*, pp. 1-10, Oct. 2006. DOI:
  [10.1109/IES.2006.357464](https://doi.org/10.1109/IES.2006.357464) —
  transaction monitors attached to interconnect links; transaction
  monitoring at about 5% of NoC area (chapters 5, 10).
- Goossens, K., Vermeulen, B., van Steeden, R., Bennebroek, M.
  "Transaction-Based Communication-Centric Debug." *Proc. 1st Int. Symp.
  Networks-on-Chip (NOCS 2007)*, pp. 95-106, May 2007. DOI:
  [10.1109/NOCS.2007.46](https://doi.org/10.1109/NOCS.2007.46) — monitors
  plus a dedicated event-distribution interconnect; monitor placement for
  communication-centric debug; monitors plus event interconnect at 4.5% of
  NoC area (chapters 2, 5, 10).
- Fiorin, L., Palermo, G., Silvano, C. "MPSoCs Run-Time Monitoring through
  Networks-on-Chip." *Proc. Design, Automation & Test in Europe
  (DATE 2009)*, pp. 558-561, Apr. 2009. DOI:
  [10.1109/DATE.2009.5090726](https://doi.org/10.1109/DATE.2009.5090726) —
  probes in the network interfaces feeding a central collector (chapters 2,
  5).

## Debug and trace standards

- IEEE-ISTO 5001-2003. *The Nexus 5001 Forum Standard for a Global Embedded
  Processor Debug Interface*, Version 2.0, IEEE Industry Standards and
  Technology Organization, Dec. 2003 (defining non-peer standard) — a
  message-based trace standard (typed messages, source IDs, timestamps):
  §5.2 SRC field ~ `unit_id`/`agent_id` (chapter 4), §4.11 absolute vs
  relative timestamps (chapter 6), §4.4.3/§4.5.3 lost trace reported rather
  than stalling ~ the lite's refuse and drop counts (chapters 3, 8).
  Local PDF: `rtl/amba/references/DebugTraceInterfaceStandard__IeeeIsto2003.pdf`.
- IEEE-ISTO 5001-2012. *The Nexus 5001 Forum Standard Embedded Processor
  Debug Interfaces*, Version 3.0, Apr. 2012 — later revision; watchpoint-
  gated trace is its Class 4 compliance level. Forum dissolved Sept. 2020
  with the standard left openly available (chapter 13).
- RISC-V International. *N-Trace Specification* (riscv-nexus-trace) —
  instruction trace for RISC-V cores; a strict subset of IEEE-5001 Nexus
  messaging, and the complement to Ocelus on a RISC-V SoC: N-Trace watches
  the processors, Ocelus watches the system they run on (chapter 13).

## Debug-infrastructure surveys and tracers

- Hopkins, A.B.T., McDonald-Maier, K.D. "Debug Support for Complex Systems
  On-Chip: A Review." *IEE Proc. Computers and Digital Techniques*,
  153(4):197-207, 2006. DOI:
  [10.1049/ip-cdt:20050194](https://doi.org/10.1049/ip-cdt:20050194) —
  on-chip trace buffers versus trace ports (chapter 7).
- Abramovici, M., Bradley, P., Dwarakanath, K., Levin, P., Memmi, G.,
  Miller, D. "A Reconfigurable Design-for-Debug Infrastructure for SoCs."
  *Proc. 43rd Design Automation Conf. (DAC 2006)*, pp. 7-12, July 2006.
  DOI: [10.1145/1146909.1146916](https://doi.org/10.1145/1146909.1146916) —
  programmable triggers in a debug fabric (chapter 8).
- Yang, F.-C., Lin, Y., Kao, C.-F., Huang, I.-J. "An On-Chip AHB Bus Tracer
  With Real-Time Compression and Dynamic Multiresolution Supports for SoC."
  *IEEE Trans. VLSI Systems*, 19(4):571-584, Apr. 2011. DOI:
  [10.1109/TVLSI.2009.2039811](https://doi.org/10.1109/TVLSI.2009.2039811) —
  a bus tracer recording into an on-chip circular buffer (chapter 7).

## Time and ordering

- Lamport, L. "Time, Clocks, and the Ordering of Events in a Distributed
  System." *Communications of the ACM*, 21(7):558-565, July 1978. DOI:
  [10.1145/359545.359563](https://doi.org/10.1145/359545.359563) —
  ordering events across groups that share no clock (chapter 6). Local PDF:
  `rtl/amba/references/LogicalClocksEventOrdering__Lamport1978.pdf`.
- IEEE Std 1588-2008. *IEEE Standard for a Precision Clock Synchronization
  Protocol for Networked Measurement and Control Systems*, July 2008. DOI:
  [10.1109/IEEESTD.2008.4579760](https://doi.org/10.1109/IEEESTD.2008.4579760) —
  the precision time protocol named as an external time source
  (chapter 6).

## Structures the design converges with

- Tamir, Y., Frazier, G.L. "High-Performance Multi-Queue Buffers for VLSI
  Communication Switches." *Proc. 15th Annual Int. Symp. Computer
  Architecture (ISCA 1988)*, pp. 343-354, May 1988. DOI:
  [10.1109/ISCA.1988.5245](https://doi.org/10.1109/ISCA.1988.5245) — a
  comparable structure to the lite monitor's per-ID linked lists in a
  shared slot pool (chapter 3). Local PDF:
  `rtl/amba/references/LinkedListMultiQueueBuffer__Tamir1988.pdf`.
- Pagiamtzis, K., Sheikholeslami, A. "Content-Addressable Memory (CAM)
  Circuits and Architectures: A Tutorial and Survey." *IEEE J. Solid-State
  Circuits*, 41(3):712-727, Mar. 2006. DOI:
  [10.1109/JSSC.2005.864128](https://doi.org/10.1109/JSSC.2005.864128) —
  the CAM behind the full monitor's table (chapter 3). Local PDF:
  `rtl/common/references/ContentAddressableMemory__Pagiamtzis2006.pdf`.
- Gupta, P., McKeown, N. "Designing and Implementing a Fast Crossbar
  Scheduler." *IEEE Micro*, 19(1):20-28, Jan./Feb. 1999. DOI:
  [10.1109/40.748793](https://doi.org/10.1109/40.748793) — the round-robin
  arbiter core of the aggregation tree (chapter 9).
- Katevenis, M., Sidiropoulos, S., Courcoubetis, C. "Weighted Round-Robin
  Cell Multiplexing in a General-Purpose ATM Switch Chip." *IEEE J.
  Selected Areas in Communications*, 9(8):1265-1279, Oct. 1991. DOI:
  [10.1109/49.105173](https://doi.org/10.1109/49.105173) — interleaved
  weighted round robin, the weighted aggregation option (chapter 9).
- Dally, W.J., Towles, B. *Principles and Practices of Interconnection
  Networks*, Morgan Kaufmann, 2004, ch. 18 "Arbitration", §18.4.2 and
  §18.4.4 — textbook treatment of the arbiter cores (secondary source)
  (chapter 9).
