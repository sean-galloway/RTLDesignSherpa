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

# Peer-Paper Reference Archive for `mem-ctrl-ip`

Seminal peer-reviewed (and, where noted, canonical non-peer) references for the
memory-controller family implemented across the `mem-ctrl-ip` suite. The archive
exists so that anyone reading or extending the RTL can go straight to the
original source of each technique rather than a textbook retelling.

## Acquisition Policy

Only legitimately open-access copies are archived:

- arXiv preprints and open conference/journal versions
- Author or lab homepages (e.g. John Owens at UC Davis, Onur Mutlu at ETH/CMU,
  Lizy John at UT Austin, José Martínez at Cornell)
- University course/lab mirrors that host licensed reprints
- Institutional repositories (MIT DSpace) and preservation archives (Internet Archive)
- Standards bodies (Open Compute Project specification)

Every downloaded PDF was opened and its first page verified to be the cited
paper — HTML error pages and mislabeled files were rejected. Papers that exist
only behind a paywall are listed as **citation only** with a DOI link; nothing
was obtained from sketchy sources.

File naming: `<Topic>__<FirstAuthor><Year>.pdf`.

## Technique → Module / Book Section → Reference Index

### Scheduler pick, ordering, and QoS

| Technique | Where it appears in `mem-ctrl-ip` | Reference | Local PDF |
|-----------|-----------------------------------|-----------|-----------|
| FR-FCFS memory access scheduling (row-hit-first, oldest-then-bank scheduling) | `mc_cmd_arbiter` / `pumice_cmd_arbiter` pick core; [common MAS ch04](../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md), [pumice MAS 07](../research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/ch02_blocks/07_scheduler.md) | S. Rixner, W. J. Dally, U. J. Kapasi, P. Mattson, J. D. Owens, "Memory Access Scheduling," *Proc. 27th Int. Symp. Computer Architecture (ISCA)*, pp. 128–138, June 2000. DOI: [10.1145/339647.339668](https://doi.org/10.1145/339647.339668) | `MemoryAccessScheduling__Rixner2000.pdf` |
| History-based page-policy / access-history predictor | Retired HAPPY predictor; page-policy engine discussion in [pumice MAS 08](../research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/ch02_blocks/08_page_policy.md) | I. Hur, C. Lin, "Adaptive History-Based Memory Schedulers," *Proc. 37th IEEE/ACM Int. Symp. Microarchitecture (MICRO-37)*, pp. 343–354, Dec. 2004. DOI: [10.1109/MICRO.2004.4](https://doi.org/10.1109/MICRO.2004.4) | `AdaptiveHistoryBasedSchedulers__Hur2004.pdf` |
| Reinforcement-learning-based memory scheduling | Design ancestry behind adaptive page-policy knobs; [pumice MAS 08](../research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/ch02_blocks/08_page_policy.md) | E. İpek, O. Mutlu, J. F. Martínez, R. Caruana, "Self-Optimizing Memory Controllers: A Reinforcement Learning Approach," *Proc. 35th Int. Symp. Computer Architecture (ISCA)*, pp. 39–50, June 2008. DOI: [10.1109/ISCA.2008.21](https://doi.org/10.1109/ISCA.2008.21) | `SelfOptimizingMemoryControllers__Ipek2008.pdf` |
| Stall-time fair / age-aware anti-starvation scheduling | `mc_cmd_arbiter` QoS/age logic; [common MAS ch04](../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | O. Mutlu, T. Moscibroda, "Stall-Time Fair Memory Access Scheduling for Chip Multiprocessors," *Proc. 40th IEEE/ACM Int. Symp. Microarchitecture (MICRO)*, pp. 146–158, Dec. 2007. DOI: [10.1109/MICRO.2007.21](https://doi.org/10.1109/MICRO.2007.21) | `StallTimeFairMemoryScheduling__Mutlu2007.pdf` |

: Scheduler and pick references

### Refresh elasticity and retention

| Technique | Where it appears in `mem-ctrl-ip` | Reference | Local PDF |
|-----------|-----------------------------------|-----------|-----------|
| Demand-aware elastic refresh (postpone/pull-in within JEDEC ±8 tREFI credits) | `scoria_refresh_ctrl` Mode A/B credit logic; scoria design requirements §3.4 | J. Stuecheli, D. Kaseridis, H. C. Hunter, L. K. John, "Elastic Refresh: Techniques to Mitigate Refresh Penalties in High Density Memory," *Proc. 43rd IEEE/ACM Int. Symp. Microarchitecture (MICRO)*, pp. 375–384, Dec. 2010. DOI: [10.1109/MICRO.2010.22](https://doi.org/10.1109/MICRO.2010.22) | `ElasticRefresh__Stuecheli2010.pdf` |
| Retention-aware refresh (variable rate by row retention bins) | Deferred scoria research item (RAIDR) | J. Liu, B. Jaiyen, R. Veras, O. Mutlu, "RAIDR: Retention-Aware Intelligent DRAM Refresh," *Proc. 39th Int. Symp. Computer Architecture (ISCA)*, pp. 1–12, June 2012. DOI: [10.1145/2366231.2337161](https://doi.org/10.1145/2366231.2337161) | citation only (not the elastic postpone/pull-in mechanism; recorded as related work) |
| Statistical-population refresh for caches | Not implemented in the family | P. G. Emma, W. R. Reohr, M. Meterelliyoz, "Rethinking Refresh: Increasing Availability and Reducing Power in DRAM for Cache Applications," *IEEE Micro* 28(6):47–56, Nov./Dec. 2008. DOI: [10.1109/MM.2008.93](https://doi.org/10.1109/MM.2008.93) | citation only (not the elastic postpone/pull-in mechanism; recorded as related work) |

: Refresh references

### Storage / CAM / descriptor-seam ancestry

| Technique | Where it appears in `mem-ctrl-ip` | Reference | Status |
|-----------|-----------------------------------|-----------|--------|
| CAM scoreboard + issue-window view of schedulable entries | `mc_wr_data_cam`, `mc_rd_cmd_cam`, unified prospect pool; [common MAS ch03](../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md), [common MAS ch04](../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | R. M. Tomasulo, "An Efficient Algorithm for Exploiting Multiple Arithmetic Units," *IBM J. Res. & Develop.* 11(1):25–33, Jan. 1967. DOI: [10.1147/rd.111.0025](https://doi.org/10.1147/rd.111.0025) — conceptual convergence: the reservation-station / common-data-bus idea behind the CAM scoreboard + issue window. | `MultipleArithmeticUnits__Tomasulo1967.pdf` |
| In-order ticket + reorder buffer (read-return ring) | `mc_rd_return_ring`; [common MAS ch02](../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | J. E. Smith, A. R. Pleszkun, "Implementation of Precise Interrupts in Pipelined Processors," *IEEE Trans. Computers* C-37(5):562–573, May 1988. DOI: [10.1109/12.4607](https://doi.org/10.1109/12.4607) — conceptual convergence: the reorder-buffer / in-order-completion idea behind the ticketed read-return ring. | citation only (IEEE paywalled) |
| Write-to-read forwarding / snarfing and memory-system basics | `mc_wr_data_cam` snarf path; [common MAS ch03](../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md) | B. Jacob, S. W. Ng, D. T. Wang, *Memory Systems: Cache, DRAM, Disk*, Morgan Kaufmann, 2007. ISBN 978-0-12-379751-3. Publisher: [elsevier.com](https://www.elsevier.com/books/memory-systems/jacob/978-0-12-379751-3) — canonical text covering wr2rd forwarding / snarf semantics. | citation only (book; publisher link) |

: Storage-plane references

### Counter / predictor machinery

| Technique | Where it appears in `mem-ctrl-ip` | Reference | Status |
|-----------|-----------------------------------|-----------|--------|
| Saturating-counter branch-prediction machinery (page-policy counters) | Saturating page-policy/adaptation counters; [pumice MAS 08](../research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/ch02_blocks/08_page_policy.md) | J. E. Smith, "A Study of Branch Prediction Strategies," *Proc. 8th Ann. Symp. Computer Architecture (ISCA)*, pp. 135–148, May 1981. DOI: [10.1145/285930.285980](https://doi.org/10.1145/285930.285980) — the saturating-counter machinery behind the page-policy counters. | citation only (ACM paywalled) |

: Counter machinery references

## Notes

- **Elastic refresh provenance.** The scoria Modes A/B elastic-refresh design
  (demand-aware postpone / pull-in within the JEDEC ±8 tREFI credit window)
  converges most closely with Stuecheli et al. 2010, which explicitly schedules
  refresh around DRAM idle periods using the same postpone/pull-in elasticity.
  The candidate papers *Rethinking Refresh* (Emma, Reohr, Meterelliyoz,
  *IEEE Micro* 2008) and *RAIDR* (Liu, Jaiyen, Veras, Mutlu, ISCA 2012) were
  evaluated and found not to match this specific mechanism: *Rethinking Refresh*
  targets cache refresh using statistical retention populations, and *RAIDR*
  classifies rows by retention time to refresh them at different rates. Both are
  recorded here as citation-only cross-references for readers who want the
  broader refresh literature, but Stuecheli 2010 is the paper that backs the
  elastic postpone/pull-in behavior.
- **Tomasulo convergence.** The local CAM scoreboard + issue-window / pick core
  is conceptually descended from Tomasulo's reservation-station / common-data-bus
  formulation; the citation is marked as conceptual convergence.
- **Smith & Pleszkun convergence.** The ticketed read-return ring enforces
  in-order completion relative to AR allocation; the reorder-buffer idea is
  attributed to Smith & Pleszkun 1988 as conceptual convergence.
- **Citation-only entries** were verified against publisher records and
  authoritative bibliographies but could not be obtained from any legitimate
  open source at archive time; follow the DOI links for the paywalled versions.

*Archive compiled 2026-10-10. 6 PDFs, ~5.3 MB.*
