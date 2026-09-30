# Reed-Solomon References

Curated 2026-09-29 for the stand-up of this component. Each stored PDF lists
its source URL and licence; documents that may not be redistributed are
linked and cited only. The PDFs were fetched from the URLs shown on that date
(sizes and page counts as downloaded). Reading order for someone new to RS is
the first table, top to bottom.

## Stored here

| File | What it is | Why it is here | Source / licence |
|---|---|---|---|
| `BBC_RD_WHP031_Clarke_2002_Reed-Solomon_Error_Correction.pdf` (47 pp) | C.K.P. Clarke, *Reed-Solomon error correction*, BBC R&D White Paper WHP 031, July 2002 | the best short engineering treatment: GF(2^8) arithmetic, encoder LFSR, syndromes, Berlekamp-Massey and Euclid side by side, Chien and Forney, with worked numbers for RS(255,239) / RS(204,188). Read this first. | https://downloads.bbc.co.uk/rd/pubs/whp/whp-pdf-files/WHP031.pdf -- (c) BBC 2002, distributed free by BBC R&D; stored for offline reading, as the repo does for vendor datasheets |
| `NASA_TM-102162_Geisel_1990_Tutorial_on_Reed-Solomon_Error_Correction_Coding.pdf` (144 pp) | W. A. Geisel, *Tutorial on Reed-Solomon Error Correction Coding*, NASA Technical Memorandum 102162, Lyndon B. Johnson Space Center, 1990 | the long-form tutorial: finite fields from scratch, a complete worked RS(15,9) example through decoding, and the classic decoder algorithms. The reference for anyone building the GF layer. | https://ntrs.nasa.gov/citations/19900019023 -- US Government work, public domain |
| `CCSDS_131.0-B-5_TM_Synchronization_and_Channel_Coding.pdf` (100 pp) | CCSDS 131.0-B-5, *TM Synchronization and Channel Coding*, Recommended Standard (Blue Book) | section 4 is the normative RS(255,223) / RS(255,239) spec: field, dual-basis representation, generator polynomial, interleaving, virtual fill. The candidate profile for a space-link consumer. | https://public.ccsds.org/Pubs/131x0b5.pdf -- CCSDS standards are published for free public use |
| `CCSDS_130.1-G-3_TM_Sync_and_Channel_Coding_Summary_of_Concept_and_Rationale.pdf` | CCSDS 130.1-G-3, *TM Synchronization and Channel Coding -- Summary of Concept and Rationale*, Informational Report (Green Book) | why the Blue Book chose what it chose: performance curves, the dual basis, interleaving depth, concatenation with the convolutional code | https://public.ccsds.org/Pubs/130x1g3e1.pdf -- as above |
| `Plank_1997_CS-96-332_Tutorial_on_Reed-Solomon_Coding_for_RAID.pdf` (19 pp) | J. S. Plank, *A Tutorial on Reed-Solomon Coding for Fault-Tolerance in RAID-like Systems*, UT Knoxville TR CS-96-332, 1996/97 (Software -- Practice & Experience 27(9), 1997) | the erasure-only use of RS: Vandermonde generator, GF(2^w) tables, recovering lost devices. The profile for a storage consumer (PRD D5). | https://web.eecs.utk.edu/~jplank/plank/papers/CS-96-332.pdf -- author's copy from his site |
| `Plank_Ding_2003_CS-03-504_Correction_to_the_1997_Tutorial.pdf` (6 pp) | J. S. Plank and Y. Ding, *Note: Correction to the 1997 Tutorial on Reed-Solomon Coding*, TR CS-03-504, 2003 | the 1997 tutorial's Vandermonde construction is wrong for some sizes; this is the fix. Never read one without the other. | https://web.eecs.utk.edu/~jplank/plank/papers/CS-03-504.pdf -- as above |

## Standards that name an RS code (linked, not stored)

| Standard | Code | Where | Access |
|---|---|---|---|
| ETSI EN 300 429 V1.2.1 (DVB-C) | RS(204,188), t = 8, shortened RS(255,239), GF(2^8) with x^8 + x^4 + x^3 + x^2 + 1; scrambler x^15 + x^14 + 1 seeded 100101010000000 | direct PDF: https://www.etsi.org/deliver/etsi_en/300400_300499/300429/01.02.01_60/en_300429v010201p.pdf ; directory: https://www.etsi.org/deliver/etsi_en/300400_300499/300429/ ; search page: https://www.etsi.org/standards#page=1&search=300%20429 | ETSI standards are free to download (the search page asks for a one-time form); redistribution restricted, so not stored here |
| ETSI EN 300 744 V1.6.2 (DVB-T) | same outer code and scrambler as DVB-C | direct PDF: https://www.etsi.org/deliver/etsi_en/300700_300799/300744/01.06.02_60/en_300744v010602p.pdf ; directory: https://www.etsi.org/deliver/etsi_en/300700_300799/300744/ | as above |
| IEEE 802.3 Clause 91 (RS-FEC for 100GBASE-R) and Clause 108 / 119 | RS(528,514) and RS(544,514) over GF(2^10) | https://standards.ieee.org/ieee/802.3/ (IEEE GET Program, free with an account) | free with login, no redistribution |
| ISO/IEC 10149 / ECMA-130 (CD-ROM) | cross-interleaved RS (CIRC), RS(32,28) and RS(28,24) | https://ecma-international.org/publications-and-standards/standards/ecma-130/ | ECMA-130 is a free download |

## The classic papers (cited; paywalled or in books)

1. I. S. Reed and G. Solomon, "Polynomial Codes over Certain Finite Fields", *J. SIAM* 8(2), 300-304, 1960. The code.
2. W. W. Peterson, "Encoding and Error-Correction Procedures for the Bose-Chaudhuri Codes", *IRE Trans. IT* 6, 1960; D. Gorenstein and N. Zierler, "A Class of Error-Correcting Codes in p^m Symbols", *J. SIAM* 9, 1961. The first algebraic decoder (PGZ).
3. R. T. Chien, "Cyclic Decoding Procedures for Bose-Chaudhuri-Hocquenghem Codes", *IEEE Trans. IT* 10, 357-363, 1964. The root search.
4. G. D. Forney, "On Decoding BCH Codes", *IEEE Trans. IT* 11, 549-557, 1965. The error-value formula.
5. E. R. Berlekamp, *Algebraic Coding Theory*, McGraw-Hill 1968 (rev. ed. World Scientific 2015); J. L. Massey, "Shift-Register Synthesis and BCH Decoding", *IEEE Trans. IT* 15, 122-127, 1969. The Berlekamp-Massey algorithm.
6. Y. Sugiyama, M. Kasahara, S. Hirasawa, T. Namekawa, "A Method for Solving Key Equation for Decoding Goppa Codes", *Information and Control* 27, 87-99, 1975. The Euclidean alternative -- the one most hardware decoders use.
7. D. V. Sarwate and N. R. Shanbhag, "High-Speed Architectures for Reed-Solomon Decoders", *IEEE Trans. VLSI Systems* 9(5), 641-655, 2001. The reformulated inversionless BM (riBM / RiBM) that hardware BM decoders are built on.
8. H. Lee, "High-Speed VLSI Architecture for Parallel Reed-Solomon Decoder", *IEEE Trans. VLSI Systems* 11(2), 288-294, 2003. Parallel Chien / Forney for multi-symbol-per-cycle throughput (PRD D6).
9. S. B. Wicker and V. K. Bhargava (eds.), *Reed-Solomon Codes and Their Applications*, IEEE Press 1994. The applications survey (CD, deep space, storage).
10. S. Lin and D. J. Costello, *Error Control Coding*, 2nd ed., Prentice Hall 2004, ch. 6-7; R. E. Blahut, *Algebraic Codes for Data Transmission*, Cambridge 2003; T. K. Moon, *Error Correction Coding*, Wiley 2005, ch. 5-6 (Moon includes GF arithmetic implementations). Textbook treatments.
11. B. Sklar, "Reed-Solomon Codes", supplementary chapter to *Digital Communications*, Prentice Hall -- a widely mirrored tutorial PDF; find it by title.
12. H. M. Shao, T. K. Truong, L. J. Deutsch, J. H. Yuen, I. S. Reed, "A VLSI Design of a Pipeline Reed-Solomon Decoder", *IEEE Trans. Computers* C-34(5), 393-403, 1985. The modified (inversionless, cross-multiplying) Euclidean array that hardware Euclid solvers descend from -- the `KES_ALGO = "EUCLID"` branch.
13. J. H. Baek and M. H. Sunwoo, "New Degree Computationless Modified Euclid Algorithm and Architecture for Reed-Solomon Decoder", *IEEE Trans. VLSI Systems* 14(8), 915-920, 2006. Removes the degree counters from the Euclidean PE; the variant to reach for if the Euclid branch's control path limits clock.

## Open-access reading (arXiv; theory, not hardware -- for background only)

- S. V. Fedorenko, "A simple algorithm for decoding both errors and erasures of Reed-Solomon codes", arXiv:0904.2861 (2009).
- C. Senger, V. R. Sidorenko et al., "Adaptive Single-Trial Error/Erasure Decoding of Reed-Solomon Codes", arXiv:1104.0576 (2011).
- M. Bras-Amoros, "A Decoding Approach to Reed-Solomon Codes from Their Definition", arXiv:1706.03504 (2017) -- a compact algebraic view worth reading after the BBC paper.
- C. Sen, S. Yesil et al., "FPGA Implementation of Erasure-Only Reed Solomon Decoders for Hybrid-ARQ Systems", arXiv:1603.09062 (2016) -- the one hardware paper in the set.
- The rest of arXiv's RS literature (list decoding, folded / linearized RS, sum-rank metric) is out of scope per PRD section 6.

## Open-source implementations (for the reuse survey and the golden model)

| What | Where | Licence | Use |
|---|---|---|---|
| `reedsolo` (Python) | https://github.com/tomerfiliba-org/reedsolomon | MIT | DV golden model: encode/decode with configurable primitive polynomial, `fcr`, `c_exp`; erasures supported |
| `galois` (Python, NumPy) | https://github.com/mhostetter/galois | MIT | GF(2^m) arithmetic and `galois.ReedSolomon` with explicit field/generator control; good for checking tables the RTL generates |
| libfec (Phil Karn) | https://github.com/quiet/libfec | LGPL-2.1 | the reference C implementation many systems use (CCSDS and general RS); read for the dual-basis conversion |
| rscode (Henry Minsky) | https://github.com/hqm/rscode | GPL-3.0 | small readable C RS(255,k) encoder/decoder |
| freecores `reed_solomon_decoder` | https://github.com/freecores/reed_solomon_decoder | (OpenCores, check) | Verilog RS(204,188) decoder, the DVB profile |
| freecores `rs_decoder_31_19_6`, `rs_dec_enc` | https://github.com/freecores/ | (OpenCores, check) | Verilog RS(31,19) decoder; encoder/decoder pair |
| wyvernSemi `eccExamples` | https://github.com/wyvernSemi/eccExamples | GPL-3.0 | Hamming and RS examples in Verilog with explanation |
| RedFlag2017 `rs-codec`, winsonbook `Reed-Solomon-` | GitHub | none stated | Verilog encoder/decoder pairs; structure only |

Licences differ; GPL code is read for structure and never copied into this
MIT-licensed repo. The Python libraries are test dependencies, not RTL.
