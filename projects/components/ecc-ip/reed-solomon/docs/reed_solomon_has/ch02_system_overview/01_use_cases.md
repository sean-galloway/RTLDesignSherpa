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
which already delimits bursts and so provides the block boundary. Symbols of
8 bits map a byte-wide device failure to one correctable symbol; t is chosen
from the device's failure model. This is the shape the pumice / scoria /
andesite family would take if it adopted RS over its present SECDED, and it
is the use case that argues most strongly for the bare valid/ready core.

## Serial link forward error correction

A transmitter encodes each frame and a receiver decodes it; the scrambler
sits outside the encoder on the line side. Two profiles come straight from
standards in `References/`: DVB's RS(204,188) over GF(2^8) and the CCSDS
RS(255,223) telemetry code with its dual-basis symbol representation. The
802.3 RS-FEC codes over GF(2^10) are the high-rate end of this use case and
drive the multi-symbol-per-beat option.

## Storage erasure coding

A controller writes parity across devices and reconstructs a lost device on
read. This is the erasure-only use of RS (Plank 1997): known-bad positions,
no Chien search, any n <= 2^m - 1. It exercises the erasure input (PRD D5)
and the AXI4 job adapter (memory-to-memory), and it is the one use case that
may want an encoder without a full decoder.

## Standalone codec on a fabric port

The core wrapped in AXI-Stream at both ends, inserted where a stream already
has block boundaries (TLAST) and room for the parity -- a framer's output,
a DMA's stream port. This is the AXIS/AXIS adapter pairing and the simplest
way to bring the block up in a system.

## Memory-to-memory job engine

The core wrapped in an AXI4 read engine and an AXI4 write engine, driven by
jobs from its register block or a descriptor stream: encode this buffer into
that one, or decode. A DMA with a transform. This is the AXI4/AXI4 pairing
and the natural test vehicle for the erasure use case.

| Use case | Profile | Adapter pairing | Erasures | Notes |
|---|---|---|---|---|
| Memory controller ECC | m = 8, t per device model | none (bare cores) | optional | the shape the core was designed for |
| Serial link FEC | DVB RS(204,188) or CCSDS RS(255,223) | none, or AXIS/AXIS | no | scrambler on the line side |
| High-rate link FEC | 802.3 RS(544,514), m = 10 | none | no | needs SYMBOLS_PER_BEAT > 1 |
| Storage erasure coding | m = 8 or 16, erasure-only | AXI4/AXI4 | yes, primary | Plank's construction |
| Standalone stream codec | any | AXIS/AXIS | optional | bring-up vehicle |
| Memory-to-memory job | any | AXI4/AXI4 | optional | test vehicle for erasures |

: Table 2.1: Use cases and the profile and adapters each implies
