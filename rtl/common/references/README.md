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


# Peer-Paper Reference Archive for `rtl/common`

Seminal peer-reviewed (and, where noted, canonical non-peer) references for every
design technique implemented across the `rtl/common` SystemVerilog library
(50 modules). The archive exists so that anyone reading or extending the RTL can
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

### Arbiters and request shaping

The arbiter family shares one round-robin core (`arbiter_round_robin`) wrapped for
weighted, deficit, and single-client use, plus an independent matrix pair and a
free-standing token-bucket shaper that sits in front of any of them.

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Deficit round robin (quantum per round, cost charged per grant, remainder carried as deficit) | `arbiter_deficit_round_robin.sv` | M. Shreedhar, G. Varghese, "Efficient Fair Queuing Using Deficit Round-Robin," *IEEE/ACM Trans. Networking* 4(3):375–385, June 1996. DOI: [10.1109/90.502236](https://doi.org/10.1109/90.502236). Conference version: *Proc. ACM SIGCOMM '95*, pp. 231–242, DOI: [10.1145/217382.217453](https://doi.org/10.1145/217382.217453). | `DeficitRoundRobin__Shreedhar1996.pdf` (journal version) |
| Weighted round robin, interleaved per-weight service with global credit replenish | `arbiter_round_robin_weighted.sv`; credit semantics also in `arbiter_matrix_weighted.sv` | M. Katevenis, S. Sidiropoulos, C. Courcoubetis, "Weighted Round-Robin Cell Multiplexing in a General-Purpose ATM Switch Chip," *IEEE J. Selected Areas in Communications* 9(8):1265–1279, Oct. 1991. DOI: [10.1109/49.105173](https://doi.org/10.1109/49.105173). | citation only (IEEE paywalled; author preprint is PostScript only at [archvlsi.ics.forth.gr](http://archvlsi.ics.forth.gr/muqpro/wrr_cam_kate_jsac91.ps), not convertible cleanly) |
| Round-robin by masked + unmasked fixed-priority encoders (programmable priority encoder) | `arbiter_round_robin.sv`, `arbiter_round_robin_simple.sv`, `arbiter_round_robin_simple_ack.sv`, `arbiter_priority_encoder.sv` (the dual-input encoder) | P. Gupta, N. McKeown, "Designing and Implementing a Fast Crossbar Scheduler," *IEEE Micro* 19(1):20–28, Jan.–Feb. 1999. DOI: [10.1109/40.748793](https://doi.org/10.1109/40.748793). | citation only (IEEE paywalled; no open copy found) |
| Fixed-priority arbitration (lowest index wins) | `arbiter_priority_encoder.sv` | No paper (standard technique). Dally & Towles §18.3 (below). | no paper (standard technique) |
| Grant held until ACK; one-client degenerate arbiter | `WAIT_GNT_ACK=1` mode of the family, `arbiter_round_robin_simple_ack.sv`, `arbiter_single_client.sv` | No paper (standard technique). Dally & Towles §18.4.3 "Grant-Hold Circuit" (below). | no paper (standard technique) |
| Matrix (least-recently-served) arbiter, upper-triangle state | `arbiter_matrix.sv`, `arbiter_matrix_weighted.sv` | No defensible single peer origin; the canonical treatment is Dally & Towles §18.5 (below). | no paper (standard technique) |
| Token-bucket rate shaping (rate *r*, burst cap *b*) | `arbiter_token_bucket.sv` | Leaky-bucket origin: J. Turner, "New Directions in Communications (or Which Way to the Information Age?)," *IEEE Communications Magazine* 24(10):8–15, Oct. 1986. DOI: [10.1109/MCOM.1986.1092946](https://doi.org/10.1109/MCOM.1986.1092946). Defining (r, b) token-bucket specification: S. Shenker, J. Wroclawski, "General Characterization Parameters for Integrated Service Network Elements," RFC 2215, IETF, Sept. 1997, [rfc-editor.org/rfc/rfc2215](https://www.rfc-editor.org/rfc/rfc2215) (standards document, not a peer paper). | citation only (Turner paywalled; RFC open online) |

: Arbiter and request-shaping references

### Associative storage and sorting

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Binary CAM (parallel compare of every entry against the key) | `cam_tag.sv` | K. Pagiamtzis, A. Sheikholeslami, "Content-Addressable Memory (CAM) Circuits and Architectures: A Tutorial and Survey," *IEEE J. Solid-State Circuits* 41(3):712–727, Mar. 2006. DOI: [10.1109/JSSC.2005.864128](https://doi.org/10.1109/JSSC.2005.864128). | `ContentAddressableMemory__Pagiamtzis2006.pdf` |
| Odd-even transposition sort (alternating odd/even neighbor compare-exchange, N passes for N values) | `sort.sv` (NUM_VALS pipelined stages, descending order) | A. N. Habermann, "Parallel Neighbor-Sort (or the Glory of the Induction Principle)," Tech. Report, Carnegie-Mellon University, Computer Science Dept., Aug. 1972 (DTIC AD-759 248). DOI: [10.1184/R1/6608258.v1](https://doi.org/10.1184/R1/6608258.v1). | `OddEvenTranspositionSort__Habermann1972.pdf` |

: Associative storage and sorting references

### FIFOs and FIFO pointer counters

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Full/empty from pointers one bit wider than the address (empty: equal; full: differ only in the wrap bit) | `fifo_sync.sv`, `fifo_control.sv` (async-FIFO flag logic on binary pointers after the crossing), `counter_bin.sv` and `counter_bin_load.sv` (the MSB-inverting wrap counters that produce those pointers) | C. E. Cummings, "Simulation and Synthesis Techniques for Asynchronous FIFO Design," *SNUG San Jose* 2002 (rev. 1.2) — canonical non-peer source, FIFO style #1. | shared with `rtl/cdc`: [`../../cdc/references/AsyncFifoGrayPointers__Cummings2002.pdf`](../../cdc/references/AsyncFifoGrayPointers__Cummings2002.pdf) |
| Non-power-of-2 wrap (clear low bits, invert MSB at MAX-1); load/add for drop and flush | `counter_bin.sv`, `counter_bin_load.sv` | No paper — repo practice built on the Cummings wrap-bit test above. | no paper (repo practice) |

: FIFO and pointer-counter references

### Clocking, clock gating, and power management

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Latch-based glitch-free clock gate (latch transparent while clock low, then AND) | `icg.sv`; instantiated by `clock_gate_ctrl.sv` | L. Benini, G. De Micheli, "Automatic Synthesis of Low-Power Gated-Clock Finite-State Machines," *IEEE Trans. CAD* 15(6):630–643, June 1996. DOI: [10.1109/43.503933](https://doi.org/10.1109/43.503933) (Fig. 1(b), Sec. II give exactly this cell). Earlier: L. Benini, P. Siegel, G. De Micheli, "Saving Power by Synthesizing Gated Clocks for Sequential Circuits," *IEEE Design & Test of Computers* 11(4):32–41, 1994. DOI: [10.1109/54.329451](https://doi.org/10.1109/54.329451). | `LatchBasedClockGating__Benini1996.pdf` (De Micheli's EPFL archive; scanned, verified visually); 1994 paper citation only |
| Fixed-timeout idle shutdown (gate after N idle cycles, wake on activity) | `clock_gate_ctrl.sv` | L. Benini, A. Bogliolo, G. De Micheli, "A Survey of Design Techniques for System-Level Dynamic Power Management," *IEEE Trans. VLSI Systems* 8(3):299–316, June 2000. DOI: [10.1109/92.845896](https://doi.org/10.1109/92.845896). | `DynamicPowerManagementTimeout__Benini2000.pdf` |
| Power-of-2 clock division by counter-bit pickoff | `clock_divider.sv` | No paper (standard technique). | no paper (standard technique) |
| LUT-selected prescaler producing a fixed 1 us tick | `counter_freq_invariant.sv` | No paper (standard technique). | no paper (standard technique) |
| Periodic one-cycle pulse from a modulo counter | `clock_pulse.sv`, `counter.sv` | No paper (standard technique). | no paper (standard technique) |
| Counter-compare pulse-width modulation | `pwm.sv` | No paper (standard technique). | no paper (standard technique) |

: Clocking and power-management references

### Counters and input conditioning

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Binary up counter with match/load/clear | `counter.sv`, `counter_load_clear.sv` | No paper (standard technique). | no paper (standard technique) |
| One-hot ring (shift-register) counter | `counter_ring.sv` | No paper (standard technique). | no paper (standard technique) |
| Contact debounce by N consecutive equal samples on a sample tick | `debounce.sv` | J. Ganssle, "A Guide to Debouncing," Ganssle Group, Aug. 2004 (rev. 4, Mar. 2014), [ganssle.com/debouncing.htm](https://www.ganssle.com/debouncing.htm) — canonical non-peer measurement study (independent consultant, not a vendor note). | citation only (web article) |

: Counter and input-conditioning references

### Data integrity: CRC, checksum, parity, SECDED

The CRC engine is the bit-serial CRC shift register unrolled eight times per
byte (`dataint_crc_xor_shift_cascade`) and chained once per byte lane, with the
polynomial, seed, reflection and final XOR all runtime inputs. The SECDED pair
is an extended Hamming code (parity at power-of-two positions plus one overall
parity bit), not a Hsiao odd-weight-column code.

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Cyclic redundancy codes (polynomial division over GF(2), shift-register realization) | `dataint_crc_xor_shift.sv`, `dataint_crc_xor_shift_cascade.sv`, `dataint_crc.sv` | W. W. Peterson, D. T. Brown, "Cyclic Codes for Error Detection," *Proc. IRE* 49(1):228–235, Jan. 1961. DOI: [10.1109/JRPROC.1961.287814](https://doi.org/10.1109/JRPROC.1961.287814) | citation only (IEEE paywalled) |
| Byte-parallel CRC (k bits per clock from the serial recurrence) | `dataint_crc_xor_shift_cascade.sv` (8 bits/stage), `dataint_crc.sv` (`DATA_WIDTH/8` stages per cycle, `cascade_sel` for partial words) | G. Albertengo, R. Sisto, "Parallel CRC Generation," *IEEE Micro* 10(5):63–71, Oct. 1990. DOI: [10.1109/40.60527](https://doi.org/10.1109/40.60527); G. Campobello, G. Patanè, M. Russo, "Parallel CRC Realization," *IEEE Trans. Computers* 52(10):1312–1319, Oct. 2003. DOI: [10.1109/TC.2003.1234528](https://doi.org/10.1109/TC.2003.1234528). The RTL unrolls the serial step directly rather than precomputing the state-transition matrix these papers derive (see Notes). | citation only (both IEEE paywalled) |
| CRC parameter model (WIDTH, POLY, INIT, REFIN, REFOUT, XOROUT) | `dataint_crc.sv` | R. N. Williams, "A Painless Guide to CRC Error Detection Algorithms," v3, Rocksoft Pty Ltd, Aug. 1993 (non-peer; the defining document of the parameterized CRC model used by every CRC catalogue). | `CrcParameterModel__Williams1993.txt` (author grants verbatim redistribution) |
| CRC polynomial selection / Hamming-distance tradeoffs | `dataint_crc.sv` (runtime `POLY`) | P. Koopman, T. Chakravarty, "Cyclic Redundancy Code (CRC) Polynomial Selection for Embedded Networks," *Proc. Int. Conf. Dependable Systems and Networks (DSN 2004)*, pp. 145–154, 2004. DOI: [10.1109/DSN.2004.1311885](https://doi.org/10.1109/DSN.2004.1311885) | `CrcPolynomialSelection__Koopman2004.pdf` (author preprint, CMU) |
| Two's-complement modular-sum checksum | `dataint_checksum.sv` (`r_count <= r_count + data`, carries out of `WIDTH` discarded) | T. C. Maxino, P. J. Koopman, "The Effectiveness of Checksums for Embedded Control Networks," *IEEE Trans. Dependable and Secure Computing* 6(1):59–72, Jan.–Mar. 2009. DOI: [10.1109/TDSC.2007.70216](https://doi.org/10.1109/TDSC.2007.70216) — evaluates this exact variant against one's-complement, Fletcher, Adler and CRC. The summation itself has no single origin. Stronger alternative not implemented here: J. G. Fletcher, "An Arithmetic Checksum for Serial Transmissions," *IEEE Trans. Communications* 30(1):247–252, Jan. 1982. DOI: [10.1109/TCOM.1982.1095369](https://doi.org/10.1109/TCOM.1982.1095369) (citation only). | `ChecksumEffectiveness__Maxino2009.pdf` (author copy, CMU) |
| Per-chunk even/odd parity | `dataint_parity.sv` | No paper (standard technique). The single parity check is the d = 2 starting point of Hamming 1950 (below). | no paper (standard technique) |
| Hamming SEC code + overall parity bit (extended Hamming SECDED) | `dataint_ecc_hamming_encode_secded.sv`, `dataint_ecc_hamming_decode_secded.sv` | R. W. Hamming, "Error Detecting and Error Correcting Codes," *Bell System Technical Journal* 29(2):147–160, Apr. 1950. DOI: [10.1002/j.1538-7305.1950.tb00463.x](https://doi.org/10.1002/j.1538-7305.1950.tb00463.x) — defines both the power-of-two parity positions and the extra overall parity bit that raises distance from 3 to 4 (SECDED). | `HammingCode__Hamming1950.pdf` (Internet Archive BSTJ scan) |
| Hsiao odd-weight-column SECDED (alternative, NOT used) | none (contrast for the two SECDED modules) | M. Y. Hsiao, "A Class of Optimal Minimum Odd-weight-column SEC-DED Codes," *IBM J. Res. & Develop.* 14(4):395–401, July 1970. DOI: [10.1147/rd.144.0395](https://doi.org/10.1147/rd.144.0395) | citation only (IBM JRD paywalled) |

: Data-integrity references (rtl/common)

### Shift registers, LFSRs, and shifters

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Maximal-length LFSR theory (primitive feedback polynomials, period 2^n - 1) | `shifter_lfsr.sv`, `shifter_lfsr_fibonacci.sv`, `shifter_lfsr_galois.sv` | No single peer paper; the canonical treatment is Golomb's book (see Textbook treatments). | no paper (standard technique) |
| Fibonacci (external XOR) vs Galois (internal XOR) LFSR forms | `shifter_lfsr_fibonacci.sv` (feedback into MSB), `shifter_lfsr_galois.sv` (tap mask applied when the shifted-out LSB is 1), `shifter_lfsr.sv` (XNOR feedback, left shift) | No paper (standard technique); both forms realize the same characteristic polynomial (Golomb). | no paper (standard technique) |
| Maximal-length tap tables | tap tables in the headers of all three LFSR modules (n = 3..168) | R. Ward, T. C. A. Molteno, "Table of Linear Feedback Shift Registers," Electronics Technical Report No. 2012-1, Dept. of Physics, University of Otago, 2012 (non-peer technical report; minimum-tap maximal designs for all n <= 786, usable to cross-check the in-RTL tables). | `LfsrTapTable__Ward2012.pdf` (author copy, Otago) |
| Barrel shifter (logical/arithmetic shift, rotate) | `shifter_barrel.sv` (rotate by fixed-slice selection from `{data,data}`; logical/arithmetic shifts left to the synthesizer's `>>`, `<<`, `>>>`) | M. R. Pillmeier, M. J. Schulte, E. G. Walters III, "Design Alternatives for Barrel Shifters," *Proc. SPIE* 4791 (Advanced Signal Processing Algorithms, Architectures, and Implementations XII), pp. 436–447, Dec. 2002. DOI: [10.1117/12.452034](https://doi.org/10.1117/12.452034) — compares mux-based, data-reversal and mask-based shift/rotate structures. | citation only (SPIE paywalled) |
| Universal (bidirectional, parallel-load) shift register | `shifter_universal.sv` | No paper (standard technique; the classic 4-mode hold/right/left/load register). | no paper (standard technique) |
| Width gearbox / beat packer (chunk-in, variable-beat-out shift-and-compensate) | `shifter_beat_pack.sv` | No paper (standard technique). | no paper (standard technique) |

: Shift register, LFSR, and shifter references (rtl/common)

### Bit-scan, encode/decode, and display utilities

| Technique | Module(s) in `rtl/common` | Reference | Local PDF / Status |
|-----------|---------------------------|-----------|--------------------|
| Leading-zero count / leading-one detection | `count_leading_zeros.sv`, `find_last_set.sv`, `leading_one_trailing_one.sv` (leading side) | V. G. Oklobdzija, "An Algorithmic and Novel Design of a Leading Zero Detector Circuit: Comparison with Logic Synthesis," *IEEE Trans. VLSI Systems* 2(1):124–128, Mar. 1994. DOI: [10.1109/92.273153](https://doi.org/10.1109/92.273153) — the hierarchical LZD tree. These modules are written as a priority scan and leave the structure to synthesis, the exact baseline the paper compares against. | `LeadingZeroDetector__Oklobdzija1994.pdf` (author's lab page) |
| Trailing-zero count / find-first-set | `count_trailing_zeros.sv`, `find_first_set.sv`, `leading_one_trailing_one.sv` (trailing side) | No separate paper; the mirror image of the LZD (Oklobdzija 1994 applies with the input reversed). | no paper (standard technique) |
| Priority encoder (highest set bit wins), with enable | `encoder.sv`, `encoder_priority_enable.sv` | No paper (standard technique). | no paper (standard technique) |
| Binary-to-one-hot decoder | `decoder.sv` | No paper (standard technique). | no paper (standard technique) |
| Binary-to-BCD by shift-and-add-3 ("double dabble"), sequential FSM | `bin_to_bcd.sv` (one shift per binary bit, +3 to every BCD digit >= 5 between shifts) | J. F. Couleur, "BIDEC -- A Binary-to-Decimal or Decimal-to-Binary Converter," *IRE Trans. Electronic Computers* EC-7(4):313–316, Dec. 1958. DOI: [10.1109/TEC.1958.5222665](https://doi.org/10.1109/TEC.1958.5222665) — the publication usually cited as the origin of the shift-and-add-3 method (see Notes). | citation only (IEEE paywalled) |
| Hex to seven-segment decode (active-low segments) | `hex_to_7seg.sv` | No paper (standard technique). | no paper (standard technique) |
| Bit reversal | `reverse_vector.sv` | No paper (standard technique). | no paper (standard technique) |

: Bit-scan, encoding, and utility references (rtl/common)

### Textbook treatments

Secondary sources from the owner's textbook library. Citation only (book,
author, chapter); the seminal papers in the tables above remain the primary
citations.

| Book | What it backs | Citation |
|------|---------------|----------|
| Dally & Towles, *Principles and Practices of Interconnection Networks* | Fixed-priority, round-robin, grant-hold, weighted RR and matrix arbiters | W. J. Dally, B. Towles, Morgan Kaufmann, 2004, ch. 18 "Arbitration": §18.3 Fixed Priority Arbiter, §18.4.2 Round-Robin Arbiter, §18.4.3 Grant-Hold Circuit, §18.4.4 Weighted Round-Robin Arbiter, §18.5 Matrix Arbiter |
| Sasao, *Memory-Based Logic Synthesis* | CAM organization (`cam_tag`) | T. Sasao, Springer, ch. 2 "Basic Elements", §2.3 "Content Addressable Memory" |
| Merrick, *Getting Started with FPGAs* | FIFO full/empty and almost-full/empty flags (`fifo_sync`, `fifo_control`); switch debouncing (`debounce`) | R. Merrick, No Starch Press, ch. 6 "Common FPGA Modules" ("FIFO: First In, First Out"); ch. 5 "Testing Your Code with Simulation" ("Project #4: Debouncing a Switch") |
| Roy, *Advanced Digital System Design* | Synchronous and loadable counters, ring counters, clock dividers, logic-level clock disable | S. Roy, Springer, ch. 4 "Basic Sequential Circuits": §4.6 Synchronous Counter Design, §4.7.1 Loadable Up Counter, §4.9 Shift Register Counters, §4.11 Clock Divider Circuits, §4.11.4 Programmable Clock Divider Circuit; ch. 15 "Low-Power Digital System Design", §15.5.5 Logic Level Power Down |
| LaMeres, *Introduction to Logic Circuits & Logic Design with Verilog* | Switch debouncing; toggle-flop clock division | B. J. LaMeres, Springer, ch. 7 "Sequential Logic Design": §7.3.3 Switch Debouncing, §7.3.1 Toggle Flop Clock Divider |
| Harris & Harris, *Digital Design and Computer Architecture, RISC-V Edition* | PWM peripheral (`pwm`) | D. M. Harris, S. L. Harris, Morgan Kaufmann, ch. e9 "Embedded I/O Systems", §9.3 (PWM) |
| *Error Correction Coding* | Sec. 1.9 Hamming Codes; ch. 3 Linear Block Codes (Sec. 3.6 Binary Hamming Codes, Sec. 3.9 Modifications to Linear Codes -- the extended Hamming code with an overall parity check, i.e. the SECDED pair); ch. 4 Cyclic Codes, Rings, and Polynomials (Sec. 4.9 Some Hardware Background, Sec. 4.10 Cyclic Encoding, Sec. 4.13 Binary CRC Codes, Appendix 4.A Linear Feedback Shift Registers) | T. K. Moon, *Error Correction Coding*, 2nd ed., John Wiley & Sons, 2021. |
| *Principles and Practices of Interconnection Networks* | ch. 21 Error Control, Sec. 21.3 Link Level Error Control (CRC as the link-level detection code) | W. J. Dally, B. Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann (Elsevier), 2004. |
| *Advanced Digital System Design* | ch. 3 Basic Combinational Circuits: Sec. 3.8 Decoders, Sec. 3.9 Encoders, Sec. 3.12.1 Binary to BCD Conversion (shift-and-add-3), Sec. 3.13 Parity Generators/Checkers; ch. 4 Basic Sequential Circuits, Sec. 4.5 Pseudo Noise Sequence Generator (LFSR); ch. 12 Floating Point Architectures, Sec. 12.4 Leading Zero Counter | S. Roy, *Advanced Digital System Design*, Springer Nature Switzerland, 2024. |
| *FPGA Prototyping by SystemVerilog Examples* | ch. 3 RT-Level Combinational Circuit: Sec. 3.10.1 Hexadecimal digit to seven-segment LED decoder, Sec. 3.10.3 Barrel shifter, Sec. 3.12.1-3.12.2 Multi-function / Parameterized barrel shifter, Sec. 3.12.3 Dual-priority encoder | P. P. Chu, *FPGA Prototyping by SystemVerilog Examples*, Xilinx MicroBlaze MCS SoC ed., John Wiley & Sons, 2018. |
| *Digital Design and Computer Architecture, RISC-V Edition* | Sec. 2.8.2 Decoders; Sec. 5.2.5 Shifters and Rotators; Sec. 5.4.2 Shift Registers | S. L. Harris, D. Harris, *Digital Design and Computer Architecture, RISC-V Edition*, Morgan Kaufmann (Elsevier), 2022. |
| *Introduction to Logic Circuits & Logic Design with Verilog* | ch. 6 MSI Logic: Sec. 6.1.1 One-Hot Decoder, Sec. 6.1.2 7-Segment Display Decoder, Sec. 6.2.1 One-Hot Binary Encoder; ch. 7 Sequential Logic Design, Sec. 7.3.4 Shift Registers | B. J. LaMeres, *Introduction to Logic Circuits & Logic Design with Verilog*, 2nd ed., Springer Nature Switzerland, 2019. |
| *Getting Started with FPGAs* | ch. 6 Common FPGA Modules, "The Shift Register" (incl. "Creating a Linear Feedback Shift Register") | R. Merrick, *Getting Started with FPGAs*, No Starch Press, 2024. |
| *Shift Register Sequences* (not in the owner's library) | Maximal-length LFSR theory, primitive polynomials, equivalence of the Fibonacci and Galois forms | S. W. Golomb, *Shift Register Sequences*, Holden-Day, San Francisco, 1967; rev. ed. Aegean Park Press, 1982. |

: Textbook treatments

## Notes

- The round-robin, weighted, deficit and single-client arbiters are all wrappers around one `arbiter_round_robin` core; the Gupta & McKeown cite covers the core's masked/unmasked encoder pair, and the WRR/DRR cites cover only the credit layer each wrapper adds.
- `arbiter_round_robin_weighted` spends credits interleaved (one grant per client per pass while credits last), which is the Katevenis 1991 interleaved WRR, not the burst-per-client form. `arbiter_matrix_weighted` is the burst form (a winner keeps the top slot until its credits run out); it borrows the credit idea, so its WRR cite is for the weighting semantics only.
- The matrix arbiter has no single peer-reviewed origin that could be verified; Dally & Towles is cited as the canonical treatment rather than inventing one. The existing page cite "ch. 17 §18.5" was corrected to ch. 18 (Arbitration); §18.5 is right.
- `sort.sv` is odd-even transposition sort (verified in the RTL: alternating (0,1),(2,3)... and (1,2),(3,4)... compare-exchange passes, NUM_VALS stages), not Batcher's odd-even merge, so Batcher 1968 is deliberately not cited. The Habermann report carries a CMU copyright-notice cover page; DTIC marks it approved for public release, and the archived copy is from CMU's own repository (KiltHub).
- `fifo_control` is named for async FIFOs but computes flags from binary pointers that were already converted and synchronized elsewhere; the Gray-pointer crossing itself belongs to the `rtl/cdc` archive. Only the wrap-bit full/empty test is cited here.
- `icg.sv` carries a source comment naming a low-power methodology book; that comment was left as is (no .sv edits). Benini & De Micheli 1996 was checked on its scanned page 2: Fig. 1(b) shows the latch "L" transparent while the global clock is low feeding an AND gate, which is the exact `always_latch` + `assign gclk = en_out && clk` structure.
- The Turner 1986 paper is the usual origin cited for the leaky bucket; the token-bucket (r, b) form the module implements is defined in RFC 2215. GCRA (ITU-T I.371) is equivalent but was not cited because the module is specified in token-bucket terms.
- **Parallel CRC structure.** Albertengo & Sisto and Campobello et al. derive a k-bit-per-clock CRC by precomputing powers of the shift register's state-transition matrix for a *fixed* polynomial. `dataint_crc` takes `POLY` as a runtime input, so no matrix can be precomputed; it instead chains eight copies of the serial step (`dataint_crc_xor_shift`) per byte and lets synthesis flatten the XOR network. The two papers are cited as the lineage of byte-parallel CRC, not as the construction the RTL uses.
- **REFIN/REFOUT/XOROUT.** Williams 1993 is not peer reviewed but is the document that defined this parameter model (the "Rocksoft model"); there is no earlier peer source for it. It is archived as the author's original plain-text release, which carries an explicit verbatim-redistribution grant.
- **Checksum variant.** `dataint_checksum` is a plain two's-complement sum truncated to `WIDTH` bits. It is not the one's-complement Internet checksum and not Fletcher's checksum. Maxino & Koopman 2009 measure this variant as weaker than one's-complement addition and Fletcher for the same width; that is the evidence base if the module is ever upgraded.
- **SECDED is Hamming, not Hsiao.** The encoder places check bits at positions 2^i and appends an overall parity bit, exactly as Hamming 1950 Sec. 5-6 describes. Hsiao 1970 is listed only as the well-known alternative (fewer XOR inputs, balanced rows) that these modules do not implement.
- **LFSR tap table provenance.** The n = 3..168 tap table in the RTL headers is the long-circulated minimum-tap table whose first publication is a vendor application note; per the acquisition policy that note is not cited. Ward & Molteno 2012 independently generate maximal tap sets up to n = 786 and agree with the in-RTL entries spot-checked (n = 4: 4,3; n = 8: 8,6,5,4). Fibonacci tap numbers in `shifter_lfsr_fibonacci.sv` are deliberately different from the Galois/XNOR columns (the header explains why); do not cross-check that module against Ward & Molteno directly.
- **Double dabble attribution.** Couleur 1958 is verified against the Crossref record but was not read (paywalled); the attribution of the shift-and-add-3 method to it is the conventional one, not independently confirmed from the paper text.
- **Bit-scan modules.** CLZ, CTZ, find-first/last-set, and both encoders are behavioral priority loops. Oklobdzija 1994 is archived because it is the standard reference for the structured alternative and explicitly benchmarks it against synthesized behavioral descriptions like these.
- **Pillmeier et al. pages.** Crossref gives first page 436; the end page 447 is from the Penn State research-portal record.

*Archive compiled 2026-10-12. 10 PDFs + 1 plain-text guide, 6.6 MB; the Cummings 2002 FIFO paper is shared with `rtl/cdc/references/`.*
