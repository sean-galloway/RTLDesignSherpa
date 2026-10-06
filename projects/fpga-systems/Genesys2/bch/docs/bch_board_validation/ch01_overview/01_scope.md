# Scope and Claims

## What this book is

This report is the board's statement about the BCH(4224,4120) t=8 codec. The
Genesys 2 harness runs the same campaigns in cocotb simulation and on real
silicon, so when the board passes we have evidence that simulation matches
hardware at 100 MHz with real I/O, real clocks, and real register traffic.

## What is claimed

The soak run demonstrates that the codec, as built into the `genesys2_axis`
bitstream, corrects up to the design boundary and flags everything past it:

- 1,000,000 blocks were decoded.
- 0 blocks were silently mis-decoded.
- 74,560 blocks carried more than t=8 errors; every one was reported as
  uncorrectable.
- 3,119,679 bits were corrected across the run.

That is a statistical, not exhaustive, proof that the decoder's correction and
uncorrectable verdicts hold under continuous random traffic on the board.

## What is not claimed

This book does not replace the component DV matrix. It does not prove every
possible error pattern, every smaller BCH profile, or every corner of the AXI4
flavour at million-block depth. It also does not cover erasure decoding; the
BCH harness has no erasure path by design. The limits in Chapter 5 say exactly
what is left outside the board evidence.
