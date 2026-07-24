# Common RTL Library

The ~55 technology-agnostic building blocks in `rtl/common/` — counters,
arbiters, FIFOs, CDC, data integrity, clock/reset utilities.

This is a pointer, by design: a standalone guide does not live in the RTL tree,
so it does not rot out of sync with a second copy.

- **Per-module docs:** [docs/markdown/RTLCommon/](../../docs/markdown/RTLCommon/index.md)
- **Quick-start guide** (browse, integrate, pitfalls, commands):
  [docs/markdown/RTLCommon/quickstart.md](../../docs/markdown/RTLCommon/quickstart.md)
- **Arithmetic** (`math_*`) moved out to [`rtl/math/`](../math/) —
  docs are the [RTLMath](../../docs/markdown/RTLMath/index.md) book
- **Agent guidance for this subsystem:** [`CLAUDE.md`](CLAUDE.md)
- **Requirements/practice:** the [vault](../../vault/INDEX.md) — handbook (method)
  and Tasks (work)
