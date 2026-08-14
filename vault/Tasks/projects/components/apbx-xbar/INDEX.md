# apbx-xbar — task rollup

APB crossbar family (`projects/components/apbx-xbar/`): the parameterized
`apbx_xbar_thin` core plus the generated fixed-configuration variants. Every
port independently speaks APB4 or APB5.

| State | Count |
|---|---|
| [open](open.md) | 2 |
| [closed](closed.md) | 1 |

## Open shortlist

- **APBX-002** — formal coverage for the version gating. The proofs run the
  all-APB4 configuration only, so the feature APBX-001 added is verified in
  simulation but not formally. Cheap to do: the masks are parameters on the
  thin core, so a harness can be instantiated per configuration.
- **APBX-003** — APB5 parity across the fabric. Blocked on a decision, not
  effort: whether the crossbar re-generates parity per boundary or passes it
  end-to-end is a protection-domain question that should be settled before RTL.

## Reading order

[closed.md](closed.md) APBX-001 is the whole story of the APB4→APBX
generalization and records why mixing needs no converters. Both open items
were split out of it at close.

Docs: [docs/markdown/rtl-amba/apbx/](../../../../../docs/markdown/rtl-amba/apbx/README.md)
