# Address modes of the characterization injectors

Both pattern generators (`axi4_master_wr_injector`, `axi4_master_rd_crc_check`)
take their addresses from a two-dimensional strided generator
(`dma_address_gen`):

    offset_0 = (index_0 * stride_0) & wrap_mask_0      (no wrap when the mask is 0)
    offset_1 = (index_1 * stride_1) & wrap_mask_1
    address  = start_addr + offset_0 + offset_1

Until TASK-049 (2026-10-23) the injectors fed the transaction counter straight
into `index_0` and held `index_1` at 0, so every family the hosts know
(`incremental`, `row_major`, `col_major`, `col_major_interleaved`) is a
one-dimensional walk, and a hit/miss MIX inside one thread could not be
expressed at all. Two fields in `AXI_ATTR` shape the index first.

## `idx1_shift` (`AXI_ATTR[27:24]`)

`idx1_shift = k` feeds the low k bits of the transaction index to `index_0`
and the rest to `index_1`; 0 is the legacy walk. The second dimension is
therefore live without a second injector:

| pattern | stride_0 / wrap_mask_0 | k | stride_1 / wrap_mask_1 |
|---|---|---|---|
| two rows of one bank, a burst to each in turn (`row_thrash`) | one row (same bank) / 0 | 1 | one burst / page - 1 |
| four rows round-robin | one row / 4 rows - 1 | 2 | one burst / page - 1 |
| bank-interleaved inside a row | one bank / all banks - 1 | log2(banks) | one burst / page - 1 |

`row_thrash` is the textbook row-buffer-conflict stream. With 2-beat bursts at
the board geometry eight bursts sit in a 16-entry window: a row-hit scheduler
serves the four A hits, then the four B hits (two activates); an oldest-first
per-bank picker alternates the rows (eight). It is the single-thread case of
the `mixed` family (TASK-046), which builds the same conflict from two threads.

## `addr_lfsr` (`AXI_ATTR[28]`)

`addr_lfsr = 1` replaces the transaction counter with a maximal 16-bit
Fibonacci LFSR (x^16 + x^15 + x^13 + x^4 + 1), seeded from `LFSR_SEED` with
bit 0 forced so it never sits in the all-zero state. Each address path (AW and
W, AR and R) steps its own copy on its own request accept, so the k-th request
of each path reads the k-th value and the paths stay in lockstep; a reader
programmed with the writer's seed reads exactly what was written, in the
writer's order. The `random` family walks bursts inside a region of two rows
across all banks (`stride_0` = one burst, `wrap_mask_0` = region - 1), so every
burst is a random bank and one of two rows.

Addresses REPEAT under the LFSR. Only the address-hash data mode (`data_mode`
1, the proxies' default) validates then: the LFSR data mode is a function of
the beat count, and a second write to the same address would overwrite the
data the reader expects.

`hammer_en` wins over both fields and keeps its meaning (index_0 = counter LSB,
index_1 = 0); see `rowhammer_methodology.md`.

## Where the families are programmed

`projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/perf_mixed_family.py`
holds `family_programs` (`row_thrash`, `random`) and the concurrent `mixed`
family; both perf proxies (`test_ddr2_char_perf.py` for pumice,
`test_granite_char_perf.py` for granite) import it, so the two cores are
measured with identical programs. The host (`ddr2_char.py`) exposes
`idx1_shift` / `addr_lfsr` on `program_wr_engine` / `program_rd_engine`; the
names live in `pumice_char.py` (`WINDOW_FAMILIES`). Measurements: mem-ctrl
recovery Phase 3 report, sections 5.6 and 5.8.
