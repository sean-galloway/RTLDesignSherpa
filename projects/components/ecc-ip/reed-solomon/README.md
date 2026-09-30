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

# Reed-Solomon Codec Component

**Status:** Stood up 2026-09-29 -- references gathered, PRD in draft, no RTL yet
**Tracker:** `vault/Tasks/projects/components/ecc-ip/reed-solomon/` (TASK-001 is the stand-up)

## What this is

A Reed-Solomon encoder / decoder component: GF(2^m) arithmetic, systematic
encoding, syndrome computation, key-equation solving (Berlekamp-Massey or
Euclidean), Chien search and Forney evaluation, behind a valid/ready
streaming interface in the house style. It lives here rather than in
`rtl/common` because a codec brings a configuration surface, a DV area with a
golden model and a spec of its own (Sean, 2026-08-09, when COMMON-009 was
dropped).

## What is here today

| Path | What |
|---|---|
| [`PRD.md`](PRD.md) | requirements draft: the decisions that pick the code (m, t, shortening, encoder-only vs full decoder, throughput, BCH in or out) and the candidate profiles from the standards in `References/` |
| [`References/`](References/README.md) | the papers and standards, with source and licence for each: the NASA tutorial, the CCSDS blue and green books, the BBC white paper, Plank's RAID tutorial and its correction; plus a cited list of the classic papers and the open-source implementations worth a reuse survey |
| [`CLAUDE.md`](CLAUDE.md) | area facts for a session working here |
| [`docs/reed_solomon_has/`](docs/reed_solomon_has/reed_solomon_has_index.md) | the Hardware Architecture Specification, v0.1 (draft): 23 chapters on use cases, context, block diagram, data flow, the two solvers, the valid/ready core ports, the AXIS and AXI4 adapters, registers, throughput/latency/resource estimates, parameters (open PRD items marked TBD), candidate profiles, verification and synthesis plan; built by `docs/generate_has_pdf.sh` into [`docs/Reed_Solomon_HAS_v0.1.pdf`](docs/Reed_Solomon_HAS_v0.1.pdf) |
| [`docs/rs_fub_catalog.md`](docs/rs_fub_catalog.md) | every FUB bottom-up: Level 0 leaves that instantiate nothing, then each level listing ALL the blocks it instantiates with counts; bill of materials for the reference profile |
| [`docs/rs_architecture_sketch.md`](docs/rs_architecture_sketch.md) | rough block diagram: the FUBs of the encoder and decoder in a line or two each, the repo blocks each is built from (and which are deliberately not used), and cell counts for the reference profile |

RTL (`rtl/` + `rtl/filelists/`), DV (`dv/tbclasses/`, `dv/tests/`) and the
MAS (`docs/reed_solomon_mas/`) are created when the PRD's decisions are made, not before --
placeholder collateral is the copy nobody finishes.

## Where to start

1. Read the PRD's decision table and pick a consumer. The three candidate
   profiles (CCSDS RS(255,223), DVB RS(204,188), 802.3 RS(544,514)) fix
   every parameter between them.
2. Read `References/README.md` in the order it suggests: BBC WHP031 for the
   arithmetic and the decoder in 47 pages, then the NASA tutorial for depth,
   then the standard you are implementing.
3. Reuse survey before any RTL, per the root CLAUDE.md: `rtl/common/dataint_ecc_*`
   for the house ECC interface conventions, `rtl/common/math_*` for the
   arithmetic primitives; the GF layer is new ground.
