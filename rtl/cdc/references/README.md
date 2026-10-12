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


# Peer-Paper Reference Archive for `rtl/cdc`

Seminal peer-reviewed (and, where noted, canonical non-peer) references for every
design technique implemented across the `rtl/cdc` SystemVerilog library
(15 modules). The archive exists so that anyone reading or extending the RTL can
go straight to the original source of each technique rather than a textbook
retelling. The companion archive for the arithmetic library is
[`rtl/math/references/README.md`](../../math/references/README.md).

## Acquisition Policy

Only legitimately open-access copies are archived:

- Author or lab homepages (author-hosted copies of IEEE/ACM papers)
- Author-published practitioner papers (SNUG papers released by their authors), retrieved
  from the Internet Archive where the original host no longer serves them
- Patent offices (Google Patents copies of U.S. patents)
- Institutional repositories, university technical reports, and preservation archives
  (Internet Archive)

Every downloaded file was opened and its first page verified to be the cited
document; HTML error pages and mislabeled files were rejected. Papers that exist
only behind a paywall are listed as **citation only** with a DOI link. Textbook
treatments are cited by book, author and chapter only and are never archived.
Vendor application notes are deliberately not used as references.

File naming: `<Technique>__<FirstAuthor><Year>.pdf`.

## Technique → Module(s) → Reference Index

### Metastability and synchronizers

The flop-chain synchronizer is pre-literature practice; the citations below are the papers that established why it is needed (Chaney & Molnar), how its failure rate scales (Veendrick), and the modern peer-reviewed treatment of the whole design space (Ginosar).

| Technique | Module(s) in `rtl/cdc` | Reference | Local PDF / Status |
|-----------|------------------------|-----------|--------------------|
| Metastability in synchronizer flip-flops (why an unbounded settling time exists at all) | `glitch_free_n_dff_arn.sv`, `cdc_synchronizer.sv`, and every synchronizer chain in the area | T. J. Chaney, C. E. Molnar, "Anomalous Behavior of Synchronizer and Arbiter Circuits," *IEEE Trans. Computers* C-22(4):421–422, Apr. 1973. DOI: [10.1109/T-C.1973.223730](https://doi.org/10.1109/T-C.1973.223730) | citation only (IEEE paywalled) |
| Exponential MTBF model for flop synchronizers (`MTBF = e^(t_res/tau) / (T0 * f_clk * f_data)`, the basis of the `FLOP_COUNT` / `N_FLOP_CROSS` / `SYNC_STAGES` depth trade) | `glitch_free_n_dff_arn.sv` (`FLOP_COUNT`), `cdc_synchronizer.sv`, `fifo_async.sv` / `gaxi_fifo_async.sv` (`N_FLOP_CROSS`), `sync_pulse.sv`, `cdc_2_phase_handshake.sv`, `cdc_4_phase_handshake.sv` (`SYNC_STAGES`), `reset_sync.sv` (`N`) | H. J. M. Veendrick, "The Behaviour of Flip-Flops Used as Synchronizers and Prediction of Their Failure Rate," *IEEE J. Solid-State Circuits* 15(2):169–176, Apr. 1980. DOI: [10.1109/JSSC.1980.1051359](https://doi.org/10.1109/JSSC.1980.1051359). Survey: L. Kleeman, A. Cantoni, "Metastable Behavior in Digital Systems," *IEEE Design & Test of Computers* 4(6):4–19, Dec. 1987. DOI: [10.1109/MDT.1987.295189](https://doi.org/10.1109/MDT.1987.295189) | citation only (both IEEE paywalled) |
| N-flop synchronizer for single bits and quasi-static buses; two-clock FIFO and req/ack synchronizers in context | `glitch_free_n_dff_arn.sv`, `cdc_synchronizer.sv` | R. Ginosar, "Metastability and Synchronizers: A Tutorial," *IEEE Design & Test of Computers* 28(5):23–35, Sept./Oct. 2011. DOI: [10.1109/MDT.2011.113](https://doi.org/10.1109/MDT.2011.113) (author's copy, Technion) | `MetastabilitySynchronizers__Ginosar2011.pdf` |
| Synchronizer misuse catalogue: four-phase req/ack synchronizer, toggle pulse synchronizer, global reset synchronizer, and the "optimizations" that break them | `cdc_4_phase_handshake.sv`, `sync_pulse.sv`, `reset_sync.sv`, `glitch_free_n_dff_arn.sv` | R. Ginosar, "Fourteen Ways to Fool Your Synchronizer," *Proc. 9th IEEE Int. Symp. Asynchronous Circuits and Systems (ASYNC 2003)*, pp. 89–96, May 2003. DOI: [10.1109/ASYNC.2003.1199169](https://doi.org/10.1109/ASYNC.2003.1199169) (author's copy, Technion) | `SynchronizerPitfalls__Ginosar2003.pdf` |
| One-clock-domain-per-synchronizer-module partitioning; two-flop synchronizer guidelines for RTL | `cdc_synchronizer.sv` (thin wrapper so every crossing is a named module), `glitch_free_n_dff_arn.sv` | C. E. Cummings, "Synthesis and Scripting Techniques for Designing Multi-Asynchronous Clock Designs," *SNUG San Jose*, 2001 (rev. 1.2) — canonical non-peer practitioner paper. | `MultiAsyncClockDesign__Cummings2001.pdf` |

: Metastability and synchronizer references

### Gray and Johnson codes

| Technique | Module(s) in `rtl/cdc` | Reference | Local PDF / Status |
|-----------|------------------------|-----------|--------------------|
| Reflected binary (Gray) code; XOR conversion binary-to-Gray and prefix-XOR Gray-to-binary | `bin2gray.sv`, `gray2bin.sv`, the inline `bin2gray` inside `counter_bingray.sv` | F. Gray, "Pulse Code Communication," U.S. Patent 2,632,058, filed Nov. 13, 1947, issued Mar. 17, 1953 (Bell Telephone Laboratories). [Google Patents](https://patents.google.com/patent/US2632058A/en) — the patent is the defining document; there is no earlier peer paper. | `GrayCode__Gray1953.pdf` |
| Twisted-ring (Johnson) counter: `WIDTH` flops, inverted MSB fed back to the LSB, `2*WIDTH` states, one bit changes per step | `counter_johnson.sv` | No defensible peer origin — standard technique. The name is conventionally credited to R. R. Johnson, whose U.S. Patent 3,030,581, "Electronic Counter" (issued Apr. 17, 1962; continuation of a 1953 application titled "Shifting Register Counters"; Hughes Aircraft) covers a family of shift-register counters with feedback. Its worked embodiment is a scale-of-15 counter, not the 2N twisted ring, so it is cited for provenance of the name only. | no paper (standard technique) |
| Johnson-code to binary decode by leading/trailing-one position | `johnson2bin.sv` (uses `leading_one_trailing_one` from `rtl/common`) | No peer paper — repo construction on a standard code. | no paper (standard technique) |

: Gray and Johnson code references

### Asynchronous FIFOs

| Technique | Module(s) in `rtl/cdc` | Reference | Local PDF / Status |
|-----------|------------------------|-----------|--------------------|
| Async FIFO with (AW+1)-bit Gray pointers synchronized into the opposite domain before full/empty is computed | `fifo_async.sv` (`USE_JOHNSON=0`), `gaxi_fifo_async.sv` (`USE_JOHNSON=0`), `gaxi_skid_buffer_async.sv` (via `gaxi_fifo_async`) | C. E. Cummings, "Simulation and Synthesis Techniques for Asynchronous FIFO Design," *SNUG San Jose*, 2002 (rev. 1.2; "FIFO Style #1") — canonical non-peer defining document for this FIFO structure. Peer-reviewed treatment of the two-clock FIFO synchronizer: Ginosar 2011 (above). | `AsyncFifoGrayPointers__Cummings2002.pdf` |
| Dual-register binary + Gray pointer counter (binary addresses memory, Gray crosses the boundary, both updated in one flop stage) | `counter_bingray.sv` | Cummings 2002 (above), "Gray code counter - Style #2". | see `AsyncFifoGrayPointers__Cummings2002.pdf` |
| Synchronized Gray pointer converted back to binary before full/empty and almost-full/almost-empty compare | `fifo_async.sv`, `gaxi_fifo_async.sv` (`gray2bin` then `fifo_control`) | Cummings 2002 (above), section on almost-full/almost-empty via Gray-to-binary conversion of the synchronized pointer. The RTL generalizes that to all four flags; Cummings' own model compares full/empty directly in Gray. | see `AsyncFifoGrayPointers__Cummings2002.pdf` |
| Johnson-coded pointers for arbitrary (non-power-of-2) FIFO depth | `fifo_async.sv`, `gaxi_fifo_async.sv`, `gaxi_skid_buffer_async.sv` (`USE_JOHNSON=1`; `JCW = DEPTH` flops give the `2*DEPTH` states the (AW+1)-bit wrap needs) | No peer paper known for this combination. It rests on the single-bit-change property of the twisted-ring code (above) and the Gray-pointer FIFO structure of Cummings 2002, which notes that useful Gray counters need power-of-2 sequences. | no paper (repo practice on standard techniques) |
| Skid buffer ahead of an async FIFO | `gaxi_skid_buffer_async.sv` | No peer paper — standard valid/ready register-slice technique. | no paper (standard technique) |

: Asynchronous FIFO references

### Handshakes, pulse transfer, open-loop transfer, and reset

| Technique | Module(s) in `rtl/cdc` | Reference | Local PDF / Status |
|-----------|------------------------|-----------|--------------------|
| Two-phase (transition / NRZ) request-acknowledge signalling | `cdc_2_phase_handshake.sv` | I. E. Sutherland, "Micropipelines," *Communications of the ACM* 32(6):720–738, June 1989 (1988 Turing Award lecture). DOI: [10.1145/63526.63532](https://doi.org/10.1145/63526.63532) — the classic statement of transition signalling. Synchronous-domain form (toggle request with ack feedback): Cummings 2008 (below), section 5.6.2-5.6.3. | citation only (publisher marks it free to read at dl.acm.org, but the PDF sits behind a bot-check and could not be fetched) |
| Four-phase (return-to-zero) req/ack handshake with source-held data | `cdc_4_phase_handshake.sv` | No single origin — standard technique. Peer-reviewed synchronizer treatment: Ginosar 2003 (four-phase handshake and push synchronizer figures) and Ginosar 2011 (round-trip req/ack). | no paper (standard technique); see `SynchronizerPitfalls__Ginosar2003.pdf` |
| Toggle pulse synchronizer (toggle in source, sync, XOR edge-detect in destination) | `sync_pulse.sv`, the toggle request path in `cdc_2_phase_handshake.sv` | Ginosar 2003 ("Pulse Synchronizer"); C. E. Cummings, "Clock Domain Crossing (CDC) Design & Verification Techniques Using SystemVerilog," *SNUG Boston*, 2008 (rev. 1.0), section 5.6 ("MCP formulation toggle-pulse generation") — canonical non-peer practitioner paper. | `ClockDomainCrossing__Cummings2008.pdf`, `SynchronizerPitfalls__Ginosar2003.pdf` |
| Open-loop transfer: stretched valid + quasi-static data held for the synchronizer to sample (the "1.5x receiving period" rule and its multi-bit extension) | `cdc_open_loop.sv` | Cummings 2008 (above), section 4.4 "Open-loop solution - sampling signals with synchronizers" and section 5.6 (multi-cycle path formulation). | `ClockDomainCrossing__Cummings2008.pdf` |
| Reset synchronizer: asynchronous assertion, synchronous de-assertion through an N-flop chain | `reset_sync.sv` (`ASYNC_ASSERT=1`; `ASYNC_ASSERT=0` is the fully synchronous variant) | C. E. Cummings, D. Mills, S. Golson, "Asynchronous & Synchronous Reset Design Techniques - Part Deux," *SNUG Boston*, 2003 (rev. 1.3), section 7 "Reset synchronizer" — canonical non-peer defining document. Peer-reviewed: Ginosar 2003, "Global Reset Synchronizer". | `ResetSynchronizer__Cummings2003.pdf` |

: Handshake, pulse, open-loop, and reset references

### Textbook treatments

Secondary sources from the owner's textbook library. Citation only (book,
author, chapter); the seminal papers in the tables above remain the primary
citations.

| Book | What it backs | Citation |
|------|---------------|----------|
| *Digital Design and Computer Architecture, RISC-V Edition* | Metastability, resolution time and the MTBF equation (sec. 3.5.4, 3.5.6); the two-flop synchronizer and its failure probability (sec. 3.5.5). Backs `glitch_free_n_dff_arn`, `cdc_synchronizer`, and the synchronizer chains inside `sync_pulse`, `reset_sync` and the handshakes. | S. L. Harris, D. Harris, Morgan Kaufmann, 2022, ch. 3 "Sequential Logic Design", sec. 3.5 "Timing of Sequential Logic" |
| *Guide to FPGA Implementation of Arithmetic Functions* | Metastability causes and MTBF (sec. 5.2.3, 5.2.3.2), mitigation (5.2.3.3); interfacing clock domains (5.3.5), req/ack handshake signaling (5.3.5.2), asynchronous FIFO with Gray pointers (5.3.5.3). | J.-P. Deschamps, G. D. Sutter, E. Cantó, Springer, LNEE vol. 149, 2012, ch. 5 "Electronic Aspects of Digital Design". DOI: [10.1007/978-94-007-2987-2](https://doi.org/10.1007/978-94-007-2987-2) |
| *Advanced Digital System Design* | Binary/Gray conversion circuits (sec. 3.11) for `bin2gray` / `gray2bin`; shift-register counters including the Johnson counter (sec. 4.9) for `counter_johnson` / `johnson2bin`. | S. Roy, Springer, 2024, ch. 3 "Basic Combinational Circuits" and ch. 4 "Basic Sequential Circuits" |

: Textbook treatments

## Notes

- **`glitch_free_n_dff_arn` is a synchronizer, not a clock switch.** Despite the name, the module is a plain N-stage flop chain with asynchronous reset; it does not implement glitch-free clock multiplexing. The synchronizer citations above apply; no clock-switching reference is needed.
- **Johnson counter provenance.** The twisted-ring counter is universally called a Johnson counter, but the only primary document found (Johnson's 1962 patent, filed 1953) illustrates a different shift-register counter. It is cited for the name only and the technique is marked standard.
- **Gray-pointer compare domain.** `fifo_async` converts each synchronized Gray pointer back to binary and lets `fifo_control` compute full, empty, almost-full and almost-empty in binary. Cummings 2002 compares full/empty in Gray and uses the binary conversion only for the almost flags; the RTL's choice trades a `gray2bin` per side for one comparison scheme.
- **Cummings papers** are canonical non-peer SNUG papers. Sunburst Design's site now redirects to a library page without direct PDF links; the archived copies are the author-published revisions retrieved from the Internet Archive's captures of `sunburst-design.com/papers/`. FIFO1 rev. 1.2 is archived; a rev. 1.3 (Nov. 2005) is listed by the current host. Cummings & Alfke's companion FIFO2 paper (asynchronous pointer comparison) is not cited because no module here uses that scheme.
- **Chaney & Molnar 1973** has a copy hosted on the Computer History Museum's IBM 1401 restoration site; it was not archived because the reprint rights are unclear.
- **`sync_pulse` page correction.** Its References previously attributed "Synthesis and Scripting Techniques for Designing Multi-Asynchronous Clock Designs" to a vendor white paper; that title is Cummings, SNUG 2001, and is now cited as such. An "IEEE 1800-2017 ... Clock Domain Crossing" entry was dropped: the LRM has no CDC clause.
- Citation-only entries were checked against Crossref records (authors, title, volume, issue, pages, year).

*Archive compiled 2026-10-12. 7 files, 4.8 MB.*
