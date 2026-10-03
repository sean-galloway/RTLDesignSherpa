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

# Use Cases

The codec is an endpoint block (chapter 2.3). Its use cases are the endpoints
a Sherpa design has or may grow, each matched to one of the PRD's candidate
profiles. None is yet a committed consumer -- that is PRD decision D10 -- so
this chapter is the menu the first consumer chooses from.

## Memory controller ECC

A memory controller encodes on its write path and decodes on its read path.
Both cores sit inside the controller's own datapath behind its scheduler,
which already delimits bursts and so provides the block boundary. The BCH code
protects a page of bits plus the spare area that holds the parity; t is
chosen from the device's raw bit-error rate and page geometry (the Cai survey
and the Nabipour paper size this). This is the expected first consumer (PRD
D10 direction) and the use case that argues most strongly for the bare
valid/ready core.

## CCSDS telecommand link

The CCSDS 231.0-B-4 standard specifies a (63,56) modified BCH code, t = 1,
concatenated with a convolutional code inside the Command Link Transmission
Unit. It is a small, fully worked example: the generator is given in figure
3-2 of the standard, the field is GF(2^6), and the correction is a single bit
anywhere in the 63-bit command frame. It is the natural first RTL profile for
bring-up even if no consumer adopts it.

## DVB outer-code link

DVB-T2, DVB-S2 and DVB-C2 use a binary BCH code as the outer stage of an
LDPC concatenation. The BCH block cleans the LDPC error floor. This use case
matters only if a broadcast consumer appears; the relevant standards are
linked, not stored, in `References/`.

## Standalone codec on a fabric port

The core wrapped in AXI-Stream at both ends, inserted where a stream already
has block boundaries (TLAST) and room for the parity -- a framer's output,
a DMA's stream port. This is the AXIS/AXIS adapter pairing and the simplest
way to bring the block up in a system.

## Memory-to-memory job engine

The core wrapped in an AXI4 read engine and an AXI4 write engine, driven by
jobs from its register block or a descriptor stream: encode this buffer into
that one, or decode. A DMA with a transform. This is the AXI4/AXI4 pairing
and the natural test vehicle for larger profiles.

| Use case | Profile | Adapter pairing | Erasures | Notes |
|---|---|---|---|---|
| Memory controller ECC | m = 13-16, t per page model | none (bare cores) | optional (D5 TBD) | the expected first consumer |
| CCSDS telecommand | (63,56), m = 6, t = 1 | none, or AXIS/AXIS | no | natural first RTL profile |
| DVB outer-code link | m, t per standard | none, or AXIS/AXIS | no | only if a broadcast consumer appears |
| Standalone stream codec | any | AXIS/AXIS | optional | bring-up vehicle |
| Memory-to-memory job | any | AXI4/AXI4 | optional | test vehicle for large profiles |

: Table 2.1: Use cases and the profile and adapters each implies
