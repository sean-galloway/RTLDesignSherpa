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

# Throughput

All throughput numbers are **TBD**. The PRD requires (R5) that no number be
claimed before it is measured in an out-of-context synthesis fixture per the
repository's practice.

## Sustained rate candidates (PRD D6)

The syndrome pass is the throughput cost: n bit positions are accumulated
against t GF MACs. Three architectures are candidates.

| Architecture | Bits per cycle | Cost | Best fit |
|---|---|---|---|
| Bit-serial syndrome pass | 1 | t parallel GF MACs, one per odd syndrome; Chien walks one position per cycle | smallest area; low clock-rate targets |
| Page-parallel unrolled syndrome tree | n / latency | unrolled GF reduction tree over the whole block; large combinational or deeply pipelined | highest throughput; large area |
| Symbol-parallel beats with per-beat serial bits | B per beat | B-bit input slice, each bit serially updates the t MACs; Chien evaluates B positions per cycle | balance; matches a byte/word memory datapath |

: Table 5.1: Throughput architecture candidates

The rate contract -- the relationship between the consumer's clock, the
block size n, the bits per beat B, and the sustained blocks per second --
must be written down once D6 decides. Until then the only honest statement
is that the core consumes one beat per cycle when not back-pressured, and
the number of bits per beat is itself open (PRD D9).

## Measured placeholder

No synthesis or simulation fixture exists. The table below will be replaced
by measured cycles per block after the first RTL and the out-of-context
fixture run.

| Profile | Architecture | Bits/cycle | Cycles per block |
|---|---|---|---|
| CCSDS (63,56) | TBD | TBD | TBD |
| NAND flash shortened | TBD | TBD | TBD |
| DVB-T2/S2/C2 | TBD | TBD | TBD |

: Table 5.1a: Measured cycles per block (placeholder)
