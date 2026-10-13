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

# APBX Crossbar

The APB crossbar family. It sits in its own directory rather than under
`apb4/` or `apb5/` because it is not tied to either: every port carries an
independent version, so one fabric can be all-APB4, all-APB5, or a mix.

> **The component's own books are the source of truth.** This page is a
> pointer, deliberately thin — it carries no parameter tables, timing
> numbers or variant inventories, because a second copy of those only
> drifts. A 971-line `apbx_xbar_variants.md` used to live here and did
> exactly that: it was still documenting decode misses as bus hangs and
> `BASE_ADDR` as needing span alignment months after both were fixed.
> Retired 2026-08-28.

| Book | Covers |
|------|--------|
| [Micro-Architecture Spec (MAS)](../../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/docs/lattice_mas/lattice_mas_index.md) | Architecture, address decode and arbitration, the RTL generator |
| [Hardware Architecture Spec (HAS)](../../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/docs/lattice_has/) | Use cases, interfaces, performance, integration |
| [Component README](../../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/README.md) | Quick start, variant list, generation |

## One architecture

Every crossbar here is generator output with the same shape: APB → cmd/rsp
→ APB across registered skid buffers, with the topology, per-slave window
size and per-port APB version all **baked in at generation time**. Changing
any of them means regenerating, not re-elaborating — the boundary IP
instantiated on each port differs, so the version choice is structural
rather than a parameter mask.

A second family once lived here: `apbx_xbar_thin`, a hand-written
combinational M×S core with weighted round-robin and runtime-programmable
windows. It was retired and deleted on 2026-08-27.

## Where the code lives

The RTL, generator, and testbenches are in the component area, not under
`rtl/amba/`:

```
projects/components/fabric-gen-ip/lattice-apbx-xbar/
 bin/                    generator + convenience driver
    apbx_xbar_generator.py
    generate_xbars.py
 rtl/                    generator output (regenerate, do not hand-edit)
    apbx_xbar_{1to1,2to1,1to4,2to4,2to2_mixed}.sv
    filelists/
    wrappers/           hand-written testbench scaffolding
 dv/tests/               CocoTB testbenches
```

Formal proofs are separate again, under `formal/apbx_xbar/`.

## Related

- [../apb4/README.md](../apb4/README.md) — the APB4 primitives an all-APB4 build is made of
- [../apb5/README.md](../apb5/README.md) — the APB5 primitives used on APB5 ports

## References

- Arm. *AMBA APB Protocol Specification*, Version 2.0, ARM IHI 0024C, Apr. 2010. [developer.arm.com/documentation/ihi0024/c](https://developer.arm.com/documentation/ihi0024/c/) — the APB4 ports of the generated crossbars. Citation only.
- Arm. *AMBA APB Protocol Specification*, ARM IHI 0024E, Feb. 2023 (APB5 first published in Issue D, Apr. 2021). [developer.arm.com/documentation/ihi0024/e](https://developer.arm.com/documentation/ihi0024/e/) — the APB5 ports. Citation only.
- Gupta, P., McKeown, N. "Designing and Implementing a Fast Crossbar Scheduler." *IEEE Micro*, 19(1), Jan.-Feb. 1999. DOI: [10.1109/40.748793](https://doi.org/10.1109/40.748793) — the masked/unmasked priority-encoder round-robin core (`arbiter_round_robin`) the generator instantiates per slave port; indexed in `rtl/common/references/README.md`.
- Dally, W.J., Towles, B. *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004, ch. 22 "Buses", §22.1 "Bus Basics" and §22.2 "Bus Arbitration" — textbook treatment of the shared-bus model (secondary source).
- Indexed in `rtl/amba/references/README.md`

## Navigation

- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
