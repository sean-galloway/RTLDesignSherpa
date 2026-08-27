# apbx-xbar — task rollup

APB crossbar family (`projects/components/apbx-xbar/`): the parameterized
`apbx_xbar_thin` core plus the generated fixed-configuration variants. Every
port independently speaks APB4 or APB5.

| State | Count |
|---|---|
| [open](open.md) | 0 |
| [closed](closed.md) | 5 |

## Open shortlist

*(APBX-004/005 closed 2026-08-27: raw-address decode rotated the slave map
for non-span-aligned BASE_ADDR; out-of-range accesses wedged the master
instead of returning PSLVERR. Both found by qc round_7 — the first
correctness round on the APB crossbar books — RED-tested and fixed.)*

Nothing open. APBX-001 (generalize to APB4/APB5/mixed), APBX-002 (formal
proof of the version gating) and APBX-003 (parity) are all closed.

## Reading order

[closed.md](closed.md) APBX-001 is the whole story of the APB4→APBX
generalization and records why mixing needs no converters; APBX-002 proved
the version gating formally; APBX-003 added parity and records why the
thin core and the generated variants necessarily protect different spans.

Docs: [docs/markdown/rtl-amba/apbx/](../../../../../docs/markdown/rtl-amba/apbx/README.md)
