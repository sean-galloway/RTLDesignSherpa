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

A Reed-Solomon code is fixed by four integers. Every one of them appears as an RTL parameter, and changing any of them changes the field table, the generator polynomial, the block length, or the number of parity symbols. This section names each parameter, gives the exact relations between them, and shows how they are set in the hardware.

## m: the symbol width

$m$ is the number of bits in one symbol. It is the exponent in the field size:

$$|\mathrm{GF}(2^m)| = 2^m.$$

The nonzero elements are $2^m - 1$. In the RTL this is `SYMBOL_WIDTH`, default 8, so one symbol is one byte (`rtl/macro/rs_encoder_core.sv:66`). The choice of $m$ also fixes the largest possible block length: $n \leq 2^m - 1$.

## n: the block length

$n$ is the number of symbols in one codeword. For a "full" Reed-Solomon code

$$n = 2^m - 1.$$

The RTL parameter is `N_SYMBOLS`, default $255$ when $m = 8$ (`rtl/macro/rs_encoder_core.sv:69`). Any smaller value is a shortened code. A shortened RS$(n,k)$ code is obtained by taking the full RS$(2^m-1, 2^m-1-2t)$ code and assuming the first $(2^m-1 - n)$ data symbols are zero. The encoder and decoder simply change `N_SYMBOLS`; there is no zero-fill hardware (`rtl/macro/rs_encoder_core.sv:55-57,69`). The shortening offset is absorbed by the Chien-search starting value (`rtl/fub/chien_search.sv:30-31`).

## k: the user data length

$k$ is the number of user data symbols per block. It is derived from $n$ and $t$:

$$k = n - 2t.$$

In the RTL `K_SYMBOLS` is computed as `N_SYMBOLS - 2*T_SYMBOLS` (`rtl/macro/rs_encoder_core.sv:74`). The number of parity symbols is therefore exactly $n - k = 2t$. This is a defining difference from binary BCH, where $n - k \leq mt$. BCH can use fewer parity symbols for the same $t$ because each error is only one bit, whereas Reed-Solomon must correct an entire $m$-bit symbol. The BCH math-to-pseudocode page uses the same riBM module and is at `../../../../bch/docs/bch_has/ch07_understanding_the_math/05_every_stage_math_to_pseudocode.md`.

## t: the error-correction capability

$t$ is the number of symbol errors the decoder is guaranteed to correct. The code adds $2t$ parity symbols, so $n - k = 2t$. The designed minimum distance is

$$d = 2t + 1.$$

The generator polynomial has $2t$ consecutive roots:

$$g(x) = \prod_{i=0}^{2t-1} \left(x - \alpha^{b+i}\right).$$

`T_SYMBOLS` is the RTL name, default 8 (`rtl/macro/rs_encoder_core.sv:68`), and the $2t$ roots are enforced by the LFSR taps (`rtl/fub/gf/gf_lfsr_encoder.sv:107-108`).

## b: the first-root offset

$b$ shifts the set of generator roots from $\alpha^0, \alpha^1, \ldots$ to $\alpha^b, \alpha^{b+1}, \ldots$. It does not change $n$, $k$, $t$, or the correction capability; it only changes the parity-check matrix. The RTL default is `FIRST_ROOT = 0` (`rtl/macro/rs_encoder_core.sv:70`). Section 7.3's worked example uses narrow-sense $b = 1$, so its roots are $\alpha^1, \alpha^2, \alpha^3, \alpha^4$.

## S: symbols per beat

$S$ is how many symbols travel in one clock cycle. It is set by the bus width:

$$S = \frac{\mathtt{DATA\_WIDTH}}{\mathtt{SYMBOL\_WIDTH}}.$$

The AXI-Stream wrapper defaults to `DATA_WIDTH = SYMBOL_WIDTH`, so $S = 1$ (`rtl/top/rs_encoder_axis4.sv:49,56`). The AXI4 job wrapper defaults to a 32-bit bus, so with $m = 8$ the default is $S = 4$ (`rtl/top/rs_encoder_axi4.sv:52,59`). The encoder and decoder unroll their per-symbol steps across $S$ lanes and select the partial-beat result with an `i_count` mux (`rtl/fub/gf/gf_lfsr_encoder.sv:158-169`). The number of beats per block is $\lceil k/S \rceil$ and $\lceil n/S \rceil$ (`rtl/top/rs_encoder_axi4.sv:125-131`).

## Parameter summary

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

The library ships with two common parameter sets. The first is the unconstrained default. The second is the Genesys 2 board loopback harness, which shortens the default code so that $n$ and $k$ are multiples of the 4-symbol beat.

| Profile | $(n,k)$ | $t$ | $m$ | $b$ | $S$ | Notes |
|---|---|---|---|---|---|---|
| Library default | $(255,239)$ | 8 | 8 | 0 | 1 | Full-length code (`rtl/macro/rs_encoder_core.sv:66-70`) |
| Genesys 2 board | $(252,236)$ | 8 | 8 | 0 | 4 | RS$(255,239)$ shortened by 3 symbols so $n$ and $k$ are multiples of the 32-bit beat (`projects/fpga-systems/Genesys2/reed-solomon/build-loop/rtl/rs_loop_cfg_pkg.sv:10-13,26-37`) |
: Table 7.17: Two shipped Reed-Solomon profiles

The shortening rationale is explicit in the board configuration: a 32-bit AXI-Stream pattern checker compares whole beats, so every beat must be full (`rs_loop_cfg_pkg.sv:10-13`). Setting `N_SYMBOLS = 252` achieves that with no extra hardware.

## Exact relations

| Relation | Equation | Why it matters |
|---|---|---|
| Field order | $|\mathrm{GF}(2^m)| = 2^m$ | Every symbol fits in an $m$-bit register. |
| Full length | $n \leq 2^m - 1$ | Alpha has multiplicative order $2^m - 1$. |
| Parity count | $n - k = 2t$ | Exactly $2t$ parity symbols for RS; BCH can use fewer. |
| Designed distance | $d = 2t + 1$ | Guarantees correction of up to $t$ symbol errors. |
| Symbols per beat | $S = \mathtt{DATA\_WIDTH}/\mathtt{SYMBOL\_WIDTH}$ | Sets the datapath width and beat count. |
: Table 7.18: Parameter equations

## Choosing the parameters: a worked example

Suppose the channel can corrupt at most one byte in every thirty, the datapath is 32 bits wide, and the desired correction is 8 symbols. Then $m = 8$ gives one symbol per byte and $S = 32/8 = 4$. With $t = 8$, the full code is RS$(255,239)$. Because the consumer needs whole 32-bit beats, shorten it by 3 symbols to RS$(252,236)$. The parity count is still $n - k = 16 = 2t$, and the designed distance is still $d = 17$. The only RTL changes are `N_SYMBOLS = 252` and the bus width; the LFSR, syndrome cells, solver, Chien search, and Forney evaluator are unchanged.
