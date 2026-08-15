# apbx-xbar — task rollup

APB crossbar family (`projects/components/apbx-xbar/`): the parameterized
`apbx_xbar_thin` core plus the generated fixed-configuration variants. Every
port independently speaks APB4 or APB5.

| State | Count |
|---|---|
| [open](open.md) | 1 |
| [closed](closed.md) | 2 |

## Open shortlist

- **APBX-003** — APB5 parity across the fabric. Blocked on a decision, not
  effort: whether the crossbar re-generates parity per boundary or passes it
  end-to-end is a protection-domain question that should be settled before RTL.

## Reading order

[closed.md](closed.md) APBX-001 is the whole story of the APB4→APBX
generalization and records why mixing needs no converters; APBX-002 then
proved the version gating formally. APBX-003 is all that remains, and it
is blocked on a decision rather than on effort.

Docs: [docs/markdown/rtl-amba/apbx/](../../../../../docs/markdown/rtl-amba/apbx/README.md)
