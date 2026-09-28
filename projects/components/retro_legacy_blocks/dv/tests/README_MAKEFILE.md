# Running the RLB tests

The target list is generated, so ask the Makefile rather than a page that can
drift:

```bash
source env_python      # required first
make help              # every target, the worker count, and the grammar
make list              # every discovered test root
```

`make help` prints the real grammar
(`run-<all|testglob>-<gate|func|full>[-serial|-parallel][-waves]`) and the
current worker count, both derived from `make/tests.mk`. This page used to
restate them and had already drifted -- it claimed 8 threads where the area
runs 48 workers -- which is why it is a pointer now.

**Always `make clean-all` first.** A stale build reports green for the old
design. The reasoning, and the failures that taught it, are in
[[running-regressions]] (`vault/handbook/dv/running-regressions.md`), which is
canonical for method.

- **Area facts** (blocks, address map, traps): [`../../CLAUDE.md`](../../CLAUDE.md)
- **Test structure** (Pattern B, the three TB methods): the `test-patterns` skill
