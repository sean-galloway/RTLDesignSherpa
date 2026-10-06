# What Is Deliberately Not Board-Tested

Some things are out of scope, and it is worth saying so plainly.

- BCH has no erasure path in this harness: the injector's `out_erasure` is
  tied off and `cfg_mark_erasure` is held low.
- The board validates only the `BCH(4224,4120) t=8` profile; smaller profiles
  like `(63,57) t=1` are covered in simulation and component DV, not on the
  board.
- The component DV matrix exercises the codec in ways the board harness does
  not replicate.
- The 2026-10-05 million-block soak is statistical, not exhaustive; its
  counters and the bounded mis-decode criterion are reported in the Board
  Validation Report.
