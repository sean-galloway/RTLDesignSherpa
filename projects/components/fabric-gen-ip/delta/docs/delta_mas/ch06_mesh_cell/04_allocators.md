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

# Allocators

> **IMPLEMENTED:** This chapter describes the `delta_mesh_cell` allocators as built. The design is per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

The cell reuses the house arbiters rather than inventing new allocation hardware. The two allocator stages are VC allocation and switch allocation.

| Allocator | House block | Role |
|---|---|---|
| VC allocation | `arbiter_matrix` | For each output port, pick one requesting input VC that has a free downstream VC |
| Switch allocation | Round-robin or iSLIP-style | For each output port, pick one input flit that already won a VC |

: Allocator mapping

## VC Allocation

VC allocation is a many-to-one pick per output port: several input VCs request the same downstream VC, and the arbiter grants at most one. The `arbiter_matrix` is Dally & Towles' recommended choice for small input counts [P19: §18.5]. It keeps state in a priority matrix, provides fairness, and is small enough to place one per output port without exploding area. The grant is one-hot per output.

> **Design note:** A separable allocator would allocate VC and switch in one combined stage. That saves a cycle but at the cost of more hardware and lower saturation throughput. The two-stage separable approach is the conservative starting point; combined allocation is deferred until measurements justify it.

## Switch Allocation

Switch allocation picks which input port drives each output port. The baseline is a round-robin arbiter per output. An iSLIP-style allocator is selectable at generation; iSLIP's iterative accept/reject loop reaches 100% throughput under uniform traffic, while a one-pass separable allocator saturates around 66% [P19: §19.3, §19.7]. The choice is a throughput-vs-area knob.

## One-Hot Grant Assertions

Every allocator grant is asserted to be one-hot (or zero-hot). Under `ifdef FORMAL`, a `$onehot0` assertion checks each output's grant vector. This is the same discipline as the flat crossbar: a multi-hot grant means two inputs would collide on the same output.

## Multicast Allocation

Multicast entries use a multi-hot output port mask. The cell does not allocate all outputs at once; instead it incrementally serves whichever masked outputs are free each cycle and releases the input only after all requested outputs have been served [P18: §17.2][P19: exercises]. Until then the head flit stays at the front of its input VC and the body flits behind it cannot advance. That serialization is the price of source-side replication within one cell.

## Conservative Output-VC Reallocation

When a downstream VC drains, the cell waits for the returning credit before assigning that VC to a new packet. Conservative reallocation prevents a subtle failure: if a VC were reassigned before the credit returned, the new packet could establish a dependency that the original deadlock analysis did not cover [P16]. Waiting one round trip is cheap insurance.

## References

- Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004 — matrix arbiters, separable and iSLIP allocators, and multicast allocation [P16][P18][P19].
