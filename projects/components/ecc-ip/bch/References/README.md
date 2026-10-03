# Binary BCH References

Curated 2026-10-03 for the stand-up of this component, mirroring the
reed-solomon component's reference set. Each stored PDF lists its source URL
and licence; documents that may not be redistributed are linked and cited
only. The PDFs were fetched from the URLs shown on that date (sizes and page
counts as downloaded). Reading order for someone new to BCH is the first
table, top to bottom.

## Stored here

| File | What it is | Why it is here | Source / licence |
|---|---|---|---|
| `Massey_1969_IT-15_Shift-Register_Synthesis_and_BCH_Decoding.pdf` (6 pp) | J. L. Massey, "Shift-Register Synthesis and BCH Decoding", *IEEE Trans. Information Theory* IT-15(1), 122-127, Jan 1969 | the key-equation paper: Berlekamp's iterative decoder recast as shortest-LFSR synthesis, the algorithm every hardware BCH/RS decoder still runs. Six pages; read this first. | https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf -- author's copy in the publication archive of Massey's home institution (ETH Zürich); stored for offline reading |
| `Massey_1965_IT-11_Step-by-Step_Decoding_of_the_BCH_Codes.pdf` (6 pp) | J. L. Massey, "Step-by-Step Decoding of the Bose-Chaudhuri-Hocquenghem Codes", *IEEE Trans. Information Theory* IT-11(4), 580-585, Oct 1965 | the no-key-equation alternative: correct syndromes one error position at a time. Minimal control hardware; the candidate to beat at small t, and the reason the PRD's solver decision (D11) lists PGZ/step-by-step alongside BM and Euclid. | https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI407.pdf -- as above |
| `CCSDS_231.0-B-4_TC_Synchronization_and_Channel_Coding.pdf` (52 pp) | CCSDS 231.0-B-4, *TC Synchronization and Channel Coding*, Recommended Standard (Blue Book), July 2021 | the one free standard whose channel coding IS a BCH code: section 3 specifies the (63,56) modified BCH code (figure 3-2 gives the generator), decoded in error-correcting or error-detecting mode, concatenated with the convolutional code inside the CLTU. The candidate profile for a telecommand consumer, and a fully worked generator example. | https://ccsds.org/Pubs/231x0b4e1.pdf -- CCSDS standards are published for free public use |
| `Guruswami_Rudra_Sudan_Essential_Coding_Theory_draft_2025.pdf` (566 pp) | V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, compiled draft of Aug 26, 2025 | the long-form theory reference: finite fields, cyclic codes, the BCH bound, BCH and Reed-Solomon codes and their decoding (Peterson-Gorenstein-Zierler, Berlekamp-Massey, and beyond), with the modern view RS textbook chapters lack. Replaces a stack of paywalled textbooks for our purposes. | https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf -- authors' draft under CC BY-NC-ND 3.0; stored unaltered for offline reading; the no-derivatives clause means read it, never excerpt it |
| `Cai_Ghose_Haratsch_Luo_Mutlu_2017_ProcIEEE_Error_Characterization_Mitigation_Recovery_Flash_SSDs.pdf` (35 pp) | Y. Cai, S. Ghose, E. F. Haratsch, Y. Luo, O. Mutlu, "Error Characterization, Mitigation, and Recovery in Flash-Memory-Based Solid-State Drives", *Proceedings of the IEEE* 105(9), 1666-1704, 2017 | the memory-consumer rationale: measured raw-bit error rates of MLC/TLC NAND and why controllers carry strong ECC. This is the consumer RS PRD section 1 points at for the binary BCH component ("multi-bit memory failures"). | https://arxiv.org/pdf/1706.08642 -- arXiv copy (same content as the journal version) |
| `Nabipour_et_al_2023_arXiv_BCH_Codes_for_Multilevel_NOR_and_NAND_Flash.pdf` (21 pp) | S. Nabipour and J. Javidan, "Enhancing Data Storage Reliability and Error Correction in Multilevel NOR and NAND Flash Memories through Optimal Design of BCH Codes", arXiv:2307.08084, 2023 | the profile-angle paper: how (m, t) are chosen against cell level, page size and required UBER for NOR/NAND parts -- the input to the PRD's candidate-profiles section for a flash consumer. | https://arxiv.org/pdf/2307.08084 -- arXiv |

## Standards that name a BCH code (linked, not stored)

| Standard | Code | Where | Access |
|---|---|---|---|
| ETSI EN 302 755 (DVB-T2) | binary BCH outer code concatenated with the LDPC inner code | https://www.etsi.org/deliver/etsi_en/302700_302799/302755/ | ETSI standards are free to download; redistribution restricted, so not stored (as for the DVB standards in the reed-solomon References) |
| ETSI EN 302 307 (DVB-S2) | BCH + LDPC (the first mass-deployment LDPC system; BCH cleans the LDPC floor) | https://www.etsi.org/deliver/etsi_en/302300_302399/302307/ | as above |
| ETSI EN 302 769 (DVB-C2) | BCH + LDPC | https://www.etsi.org/deliver/etsi_en/302700_302799/302769/ | as above |
| CCSDS 231.0-B-4 (TC) | (63,56) modified BCH | stored above | -- |
| NAND geometry (JEDEC / ONFI) | not a code: the page + spare-out area sizes that flash BCH profiles are dimensioned around | JEDEC documents are access-controlled; the page/spare numbers needed to size a profile are quoted in the Cai and Nabipour papers stored above | paywalled / free-with-login |

## The classic papers (cited; paywalled or in books)

1. A. Hocquenghem, "Codes correcteurs d'erreurs", *Chiffres* 2, 147-156, 1959. The code, first.
2. R. C. Bose and D. K. Ray-Chaudhuri, "On a Class of Error Correcting Binary Group Codes", *Information and Control* 3, 68-79, 1960. The code, independently.
3. W. W. Peterson, "Encoding and Error-Correction Procedures for the Bose-Chaudhuri Codes", *IRE Trans. IT* 6, 459-470, 1960. The first decoder; direct matrix solve over the syndromes.
4. D. Gorenstein and N. Zierler, "A Class of Error-Correcting Codes in p^m Symbols", *J. SIAM* 9, 207-214, 1961. Generalizes to GF(q); with Peterson gives the PGZ decoder.
5. R. T. Chien, "Cyclic Decoding Procedures for Bose-Chaudhuri-Hocquenghem Codes", *IEEE Trans. IT* 10, 357-363, 1964. The root search that finds the error positions; the hardware search every decoder still schedules.
6. G. D. Forney Jr., "On Decoding BCH Codes", *IEEE Trans. IT* 11, 549-557, 1965. The error-VALUE formula. For binary BCH every error value is 1, so Forney collapses to a bare bit flip -- the architectural difference from the RS component, where Forney is a full stage.
7. E. R. Berlekamp, *Algebraic Coding Theory*, McGraw-Hill 1968. The iterative decoder the hardware literature calls BM.
8. J. L. Massey 1969 (stored above).
9. Y. Sugiyama, M. Kasahara, S. Hirasawa, T. Namekawa, "A Method for Solving Key Equation for Decoding Goppa Codes", *Information and Control* 27, 87-99, 1975. The Euclidean alternative (the reed-solomon component's `KES_ALGO = "EUCLID"` branch uses its RS form).
10. R. E. Blahut, "Transform Techniques for Error Control Codes", *IBM J. Res. Develop.* 23(3), 299-315, 1979. The spectral (Fourier-over-GF) view of syndrome decoding. IBM's copyright notice permits verbatim copying with the notice attached, but no verified source URL was found on the curation date -- cited, DOI 10.1147/rd.233.0299.
11. S. Lin and D. J. Costello, *Error Control Coding*, 2nd ed., Prentice Hall 2004; R. E. Blahut, *Theory and Practice of Error Control Codes*, Addison-Wesley 1983; T. K. Moon, *Error Correction Coding*, Wiley 2005. Textbook treatments; Lin & Costello's binary-BCH chapter is where the evenness shortcut (S_2j = S_j^2, so only t odd syndromes are independent) is derived.

## Open-access reading (arXiv; theory and surveys -- background)

- Y. Cai et al., "Errors in Flash-Memory-Based Solid-State Drives", arXiv:1711.11427 (2017) -- the longer companion to the stored Proc. IEEE survey.
- The list-decoding literature for BCH/RS (Guruswami-Sudan and beyond) is out of scope per PRD section 6, as it is for the reed-solomon component.

## Open-source implementations (for the reuse survey and the golden model)

| What | Where | Licence | Use |
|---|---|---|---|
| `galois` (Python, NumPy) | https://github.com/mhostetter/galois | MIT | GF(2^m) arithmetic and `galois.BCH` with explicit primitive-polynomial control: encode, decode, syndromes. The DV golden-model candidate -- the `reedsolo` package the reed-solomon DV uses is RS-only and does not do BCH |
| AFF3CT | https://github.com/aff3ct/aff3ct | MIT | C++/MATLAB ECC simulator with BCH among its codes; a second independent implementation to cross-check the golden model |
| `python-bchlib` | https://github.com/jkent/python-bchlib | MIT (verify before use) | small libbch binding; candidate for quick model experiments |
| Verilog/VHDL BCH cores (OpenCores, GitHub) | search "BCH decoder" | varies | several NAND-flash-oriented decoders exist; read for structure only -- GPL code is never copied into this MIT-licensed repo |

Licences differ; GPL code is read for structure and never copied into this
MIT-licensed repo. The Python libraries are test dependencies, not RTL.
