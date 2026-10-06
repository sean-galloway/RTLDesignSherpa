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

A Reed-Solomon code boils down to four integers. Change any of them and you change the field table, the generator polynomial, the block length, or the parity count. This section names the four, gives the exact relations between them, and points at the RTL parameter for each.

## m: the symbol width

$m$ is the bit width of one symbol. It's also the exponent in the field size:

$$|\mathrm{GF}(2^m)| = 2^m.$$

The nonzero elements are $2^m - 1$. In the RTL this is `SYMBOL_WIDTH`, default 8, so one symbol is one byte (`rtl/macro/rs_encoder_core.sv:66`). Picking $m$ also caps the block length: $n \leq 2^m - 1$.

## n: the block length

$n$ is the number of symbols in one codeword. A full-length Reed-Solomon code has

$$n = 2^m - 1.$$

The RTL parameter is `N_SYMBOLS`, default $255$ when $m = 8$ (`rtl/macro/rs_encoder_core.sv:69`). Anything smaller is a shortened code. You get it by taking the full RS$(2^m-1, 2^m-1-2t)$ code and assuming the first $(2^m-1 - n)$ data symbols are zero. There's no zero-fill hardware — the encoder and decoder just change `N_SYMBOLS` (`rtl/macro/rs_encoder_core.sv:55-57,69`). The Chien search absorbs the shortening offset in its starting value (`rtl/fub/chien_search.sv:30-31`).

## k: the user data length

$k$ is the number of user data symbols per block. It's derived from $n$ and $t$:

$$k = n - 2t.$$

In the RTL `K_SYMBOLS` is computed as `N_SYMBOLS - 2*T_SYMBOLS` (`rtl/macro/rs_encoder_core.sv:74`). So the parity count is exactly $n - k = 2t$. That's a defining difference from binary BCH, where $n - k \leq mt$. BCH can use fewer parity symbols for the same $t$ because it only corrects single bits; RS has to correct an entire $m$-bit symbol. The BCH math-to-pseudocode page uses the same riBM module and is at `../../../../bch/docs/bch_has/ch07_understanding_the_math/05_every_stage_math_to_pseudocode.md`.

## t: the error-correction capability

$t$ is how many symbol errors the decoder is guaranteed to fix. It costs $2t$ parity symbols, so $n - k = 2t$, and the designed minimum distance is

$$d = 2t + 1.$$

The generator polynomial has $2t$ consecutive roots:

$$g(x) = \prod_{i=0}^{2t-1} \left(x - \alpha^{b+i}\right).$$

`T_SYMBOLS` is the RTL name, default 8 (`rtl/macro/rs_encoder_core.sv:68`), and the LFSR taps enforce those $2t$ roots (`rtl/fub/gf/gf_lfsr_encoder.sv:107-108`).

## b: the first-root offset

$b$ shifts the generator's root set from $\alpha^0, \alpha^1, \ldots$ to $\alpha^b, \alpha^{b+1}, \ldots$. It doesn't change $n$, $k$, $t$, or the correction power — it only changes the parity-check matrix. The RTL default is `FIRST_ROOT = 0` (`rtl/macro/rs_encoder_core.sv:70`). Section 7.3's worked example uses narrow-sense $b = 1$, so its roots are $\alpha^1, \alpha^2, \alpha^3, \alpha^4$.

## S: symbols per beat

$S$ is how many symbols travel in one clock cycle. It's set by the bus width:

$$S = \frac{\mathtt{DATA\_WIDTH}}{\mathtt{SYMBOL\_WIDTH}}.$$

The AXI-Stream wrapper defaults to one symbol per beat (`rtl/top/rs_encoder_axis4.sv:49,56`). The AXI4 job wrapper defaults to a 32-bit bus, so with $m = 8$ you get $S = 4$ (`rtl/top/rs_encoder_axi4.sv:52,59`). The encoder and decoder unroll their per-symbol steps across those $S$ lanes and use `i_count` to select the partial-beat result (`rtl/fub/gf/gf_lfsr_encoder.sv:158-169`). The number of beats per block is $\lceil k/S \rceil$ and $\lceil n/S \rceil$ (`rtl/top/rs_encoder_axi4.sv:125-131`).

## Parameter summary

Table 7.16 collects the six names and their RTL defaults.

| Symbol | RTL parameter | Meaning | Default (m=8) |
|---|---|---|---|
| $m$ | `SYMBOL_WIDTH` | bits per symbol | 8 |
| $n$ | `N_SYMBOLS` | symbols per codeword | 255 (or shortened) |
| $k$ | `K_SYMBOLS` | user data symbols | $n - 2t$ |
| $t$ | `T_SYMBOLS` | correctable symbol errors | 8 |
| $b$ | `FIRST_ROOT` | exponent of first generator root | 0 |
| $S$ | `SYMBOLS_PER_BEAT` | symbols per clock beat | bus dependent |
: Table 7.16: Reed-Solomon parameters and their RTL names

## Built profiles

Table 7.17 shows the two shipped parameter sets: the unconstrained library default and the Genesys 2 board harness.

| Profile | $(n,k)$ | $t$ | $m$ | $b$ | $S$ | Notes |
|---|---|---|---|---|---|---|
| Library default | $(255,239)$ | 8 | 8 | 0 | 1 | Full-length code (`rtl/macro/rs_encoder_core.sv:66-70`) |
| Genesys 2 board | $(252,236)$ | 8 | 8 | 0 | 4 | RS$(255,239)$ shortened by 3 symbols so $n$ and $k$ are multiples of the 32-bit beat (`projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/build-loop/rtl/rs_loop_cfg_pkg.sv:10-13,26-37`) |
: Table 7.17: Two shipped Reed-Solomon profiles

The board configuration is explicit about why it shortens: a 32-bit AXI-Stream pattern checker compares whole beats, so every beat must be full (`rs_loop_cfg_pkg.sv:10-13`). Setting `N_SYMBOLS = 252` achieves that with no extra hardware.

## Exact relations

Table 7.18 lists the equations that tie the parameters together.

| Relation | Equation | Why it matters |
|---|---|---|
| Field order | $|\mathrm{GF}(2^m)| = 2^m$ | Every symbol fits in an $m$-bit register. |
| Full length | $n \leq 2^m - 1$ | Alpha has multiplicative order $2^m - 1$. |
| Parity count | $n - k = 2t$ | Exactly $2t$ parity symbols for RS; BCH can use fewer. |
| Designed distance | $d = 2t + 1$ | Guarantees correction of up to $t$ symbol errors. |
| Symbols per beat | $S = \mathtt{DATA\_WIDTH}/\mathtt{SYMBOL\_WIDTH}$ | Sets the datapath width and beat count. |
: Table 7.18: Parameter equations

## Choosing the parameters: a worked example

Suppose the channel corrupts at most one byte in every thirty, the datapath is 32 bits wide, and you want to correct 8 symbols. Then $m = 8$ gives one symbol per byte and $S = 32/8 = 4$. With $t = 8$, the full code is RS$(255,239)$. Because the consumer needs whole 32-bit beats, shorten it by 3 symbols to RS$(252,236)$. The parity count is still $n - k = 16 = 2t$, and the designed distance is still $d = 17$. The only RTL changes are `N_SYMBOLS = 252` and the bus width; the LFSR, syndrome cells, solver, Chien search, and Forney evaluator stay exactly the same.
