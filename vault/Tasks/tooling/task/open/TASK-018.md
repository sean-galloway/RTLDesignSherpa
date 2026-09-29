# TASK-018: two formal areas have no entry point, so `make formal` skips them

**Priority:** P3 — the proofs exist and pass; they simply never run unattended,
which is how a proof stops noticing it has broken.
**Status:** open 2026-09-28
**Owner:** TBD
**Found by:** opening `formal/pumice/` and wiring it in — the same check showed
two areas already unwired.
**Related:** the `formal/Makefile` comment that warns about exactly this: "2026-09-11:
`make formal` ran neither, so ninety task directories had no entry point and
nobody noticed twelve flat files drifting from their RTL."

## The gap

`formal/Makefile`'s `formal:` target lists `formal-rtl formal-converters
formal-stream formal-rapids formal-rlb formal-pumice`. Measured against what
exists under `formal/`:

| Area | Proofs (`*/*.sby`) | Has a `formal-*` target? |
|---|---:|---|
| amba | 64 | yes (via `formal-rtl`) |
| common | 222 | yes (via `formal-rtl`) |
| cdc | 12 | yes (via `formal-rtl`) |
| converters | 18 | yes |
| stream | 16 | yes |
| rapids | 11 | yes |
| retro_legacy_blocks | 5 | yes (`formal-rlb`) |
| pumice | 11 | yes (added 2026-09-28) |
| **apbx_xbar** | **5** | **no** |
| **bridge** | **1** | **no** |
| apb_xbar | 0 | n/a — holds no proof |

So 6 proofs are unreachable from `make formal`. They are not broken; nothing runs
them, which is worse, because a proof nobody runs reports nothing when the RTL
moves underneath it.

## Fix

Two targets modelled on `formal-rlb`, and **added to the `formal:` list in the
same edit** — that is the discipline the existing comments in that file keep
insisting on, because both previous omissions were added-but-not-listed:

```make
.PHONY: formal-apbx-xbar
formal-apbx-xbar:
	$(MAKE) -C apbx_xbar prove-all

.PHONY: formal-bridge-formal
formal-bridge-formal:
	$(MAKE) -C bridge prove-all
```

Note `formal-bridge` is already taken in that file by a different target — check
before naming.

Then confirm both areas have an area-level `Makefile` with `prove-all` /
`cover-all` (copy `formal/cdc/Makefile`, which discovers modules via
`$(wildcard */*.sby)` rather than a hand-kept list), and re-measure:

    python3 bin/formal_status.py --areas apbx_xbar bridge

## Done when

`make formal` reaches every directory under `formal/` that holds a `.sby`, and
`bin/formal_status.py` with no `--areas` argument (it discovers them as of
2026-09-28) reports the same area count that `ls formal/` shows holds proofs.
