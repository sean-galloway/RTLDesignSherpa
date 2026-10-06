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

# The Parameters n, k, t, m

Every BCH code boils down to a handful of integers. Here's what each one means, how they fit together, and where they show up in the RTL.

## n: block length

$n$ is the number of bits in one coded block. For a primitive BCH code it reaches the full length of the field:

$$n_{\text{full}} = 2^m - 1$$

Most real profiles are shortened: the configured $n$ is smaller than $2^m - 1$, and the missing high-order bits are treated as zero during syndrome computation and Chien search. The algebra doesn't change—only the position offsets and the assumption of leading zeros do. The package computes the full-field size in `bch_order` and the configured size is the parameter `N_BITS` (`rtl/fub/bch_pkg.sv:50-52`, `rtl/fub/bch_pkg.sv:37`).

## m: field dimension

The code lives in $\mathrm{GF}(2^m)$. Each nonzero field element is a power of a primitive element $\alpha$, and every element is stored as an $m$-bit vector. The primitive polynomial $p(x)$ of degree $m$ is encoded as `PRIM_POLY`; bit $m$ is the leading term and is implicit. The default profile uses $m = 6$ and $p(x) = x^6 + x + 1$ (`PRIM_POLY = 0x43`) (`rtl/fub/bch_pkg.sv:34-35`).

## k: message length

$k$ is the number of data bits carried inside one $n$-bit block. It isn't an independent parameter; it's fixed by the degree of the generator polynomial:

$$k = n - \deg(g)$$

The encoder core exposes `K_BITS` as exactly this difference (`rtl/macro/bch_encoder_core.sv:71`, `rtl/macro/bch_decoder_core.sv:87`).

## t: correctable bit errors

$t$ is the guaranteed number of bit flips the decoder can fix. The generator has $2t$ consecutive roots:

$$g(\alpha^b) = g(\alpha^{b+1}) = \dots = g(\alpha^{b+2t-1}) = 0$$

The first root $b$ is `FIRST_ROOT`. When $b = 1$ the code is narrow-sense, the usual textbook case. When $b = 0$ the consecutive range includes $\alpha^0 = 1$, so $g(x)$ gains an $(x+1)$ factor and can detect an extra odd-weight error pattern. The designed minimum distance is

$$d \ge 2t + 1$$

This is the BCH bound; the design chooses the roots and therefore $t$ (`rtl/fub/bch_pkg.sv:56-59`).

## deg g: parity bits

The degree of the generator is the number of parity bits appended to each block:

$$\deg(g) = n - k$$

The degree counts the distinct conjugates of the consecutive roots $\alpha^b \dots \alpha^{b+2t-1}$. Each cyclotomic coset modulo $2^m - 1$ contributes its size once, so the degree is bounded by

$$\deg(g) \le m \cdot t$$

For many profiles the bound is loose; for the Genesys 2 profile below it's tight: $\deg(g) = 13 \cdot 8 = 104$. The package computes the degree without expanding the whole polynomial when possible (`rtl/fub/bch_pkg.sv:62-83`).

## Parameters in the RTL

| Symbol | RTL parameter | Meaning |
|--------|---------------|---------|
| $m$    | `FIELD_DIM`   | Dimension of $\mathrm{GF}(2^m)$ |
| $p(x)$ | `PRIM_POLY`   | Primitive polynomial of degree $m$ |
| $t$    | `T_BITS`      | Correctable bit errors |
| $n$    | `N_BITS`      | Configured codeword length |
| $b$    | `FIRST_ROOT`  | First consecutive root of $g(x)$ |
| $k$    | `K_BITS`      | Derived as $n - \deg(g)$ |
| $B$    | `BITS_PER_BEAT` | Bits per AXI-Stream/AXI4 beat |
: Table 7.10: RTL parameter names for the BCH code variables

`BITS_PER_BEAT` is bits per beat, not symbols. The AXI-Stream wrapper defaults it to 8 (`rtl/top/bch_encoder_axis4.sv:48-69`) and the AXI4 wrapper defaults the bus width to 8 (`rtl/top/bch_encoder_axi4.sv:39-56`).

## Table of built profiles

| Profile | $m$ | `PRIM_POLY` | $t$ | $b$ | $n$ | $k$ | $\deg(g)$ | $g$ (hex) |
|---------|-----|-------------|-----|-----|-----|-----|-----------|-----------|
| CCSDS TC narrow-sense | 6 | `0x43` | 1 | 1 | 63 | 57 | 6 | `0x43` |
| CCSDS TC modified | 6 | `0x43` | 1 | 0 | 63 | 56 | 7 | `0xC5` |
| Mid-size sanity | 6 | `0x43` | 2 | 1 | 63 | 51 | 12 | `0x1539` |
| Genesys 2 board | 13 | `0x201B` | 8 | 1 | 4224 | 4120 | 104 | (see package) |
: Table 7.11: Built BCH profiles

The Genesys 2 board loopback design runs the shortened profile BCH$(4224, 4120)$ with $t = 8$ (`projects/fpga-systems/Genesys2/ecc-ip/bch/build-loop/rtl/bch_loop_cfg_pkg.sv:26-31`). The $m = 13$ primitive polynomial is $p(x) = x^{13} + x^4 + x^3 + x + 1$ (`0x201B`). The degree lands exactly at $m \cdot t = 104$, so the parity budget is fully used.

## Choosing the parameters: a worked example

Say a 512-byte sector has to survive up to 8 bit flips. The data payload is $512 \cdot 8 = 4096$ bits.

1. Pick the field. $m = 12$ gives $n_{\text{full}} = 4095$, which isn't enough room for both data and parity. $m = 13$ gives $n_{\text{full}} = 8191$, comfortably larger than 4096.
2. Pick $t$. With $t = 8$ the BCH bound promises correction of up to 8 bit errors. The parity budget is at most $m \cdot t = 104$ bits.
3. Choose the block length. A 4096-bit payload plus a 128-bit spare region gives $n = 4224$.
4. Check the degree. For $m = 13$, $t = 8$, $b = 1$, the generator degree is exactly 104, so $k = 4224 - 104 = 4120$. The 4096 data bits plus 24 unused bits in the data region are carried as the $k$ message bits.

That's the Genesys 2 profile in Table 7.11.
