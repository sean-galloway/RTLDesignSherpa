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

# CSR obs_* readout layout

Status: v2 plan (the CSR slave that exposes these words is F1, scheduled
for the next milestone). The aggregator packing lives inside the two
top-level macros today: `command_scheduler_macro.obs_words_o[6:0]` and
`axi_frontend_macro.obs_words_o[1:0]`. F1 will route them to APB via a
read-only register block.

---

## Tally

For NUM_RANKS=1, NUM_BANKS=8 (current production config):

| Source            | obs signals                                   | Total bits |
|-------------------|-----------------------------------------------|-----------:|
| global_timers     | faw_nz, trrd_nz, twtr_nz, trtw_nz, tccd_nz    |          5 |
| xbank_timers      | act/rdwr/pre/rc/ras counter NZ + ap_pending   |         48 |
| refresh_ctrl      | refi_cnt, drain_remaining, bank_rotor, grants |         39 |
| powerdown_ctrl    | state, idle_cnt, grants_pde, grants_sr        |         51 |
| axi_intake        | wr/rd_completions, aw/ar_meta_writes          |         64 |
| **total**         |                                               |    **207** |

207 bits → 7 words from command_scheduler_macro + 2 words from
axi_frontend_macro = **9 32-bit CSR read-only registers**. No mux
needed — direct readout fits cleanly.

---

## Layout

### command_scheduler_macro.obs_words_o (7 × 32 bits)

| Word | [31:24]            | [23:16]            | [15:8]            | [7:0]            |
|-----:|--------------------|--------------------|-------------------|------------------|
| 0    | pad9 \| drain_rem(4) \| bank_rotor(BA_W)   ||| refi_cnt[15:0]   |
| 1    | reserved (16)                              ||  refi_grants_total[15:0] ||
| 2    | reserved (13) \| pdn_idle_cnt[15:0] \| pdn_state(3)         ||||
| 3    | pdn_grants_sr[15:0]                    ||  pdn_grants_pde[15:0] ||
| 4    | reserved(16) \| ap_pending[7:0] \| {tccd,trtw,twtr,trrd[0],faw[0],3'b0} ||||
| 5    | rc_nz[7:0]         | pre_nz[7:0]        | rdwr_nz[7:0]      | act_nz[7:0]      |
| 6    | reserved (24)                              ||| ras_nz[7:0]      |

Notes:
- Word 0 padding scales: `pad_width = 12 - $clog2(NUM_BANKS)`. For
  NUM_BANKS=8 → 9 pad bits.
- Words 4..6 hard-wire rank index 0. Multi-rank (NUM_RANKS>1) needs
  additional words — extend obs_words_o length and replicate words 4..6
  per rank.

### axi_frontend_macro.obs_words_o (2 × 32 bits)

| Word | [31:16]                    | [15:0]                  |
|-----:|----------------------------|-------------------------|
| 0    | rd_completions[15:0]       | wr_completions[15:0]    |
| 1    | ar_meta_writes[15:0]       | aw_meta_writes[15:0]    |

---

## F1 (CSR slave) plan

When F1 lands, it should:

1. Concatenate the two macros' obs_words_o into a flat 9-word array at
   the top-level (`obs_words[8:0][31:0]` = `{intake_obs, cmd_obs}`).
2. Expose those 9 words at offsets `OBS_BASE + 4*N` (N=0..8) in the
   APB register map. All read-only.
3. The `cmd_obs` word indices map 1:1 to the table above; `intake_obs`
   words become CSR offsets 7..8.

The CSR base addresses follow the stream component's methodology
(per the saved planning memory). No new mux logic needed — direct flop
fanout from each FUB through the obs_words pack into the APB read
multiplexer is enough.

---

## Adding new obs_* signals

When a new FUB sprouts an obs_* output:

1. Wire it from the FUB instance up to one of the two aggregator
   macros (command_scheduler or axi_frontend, depending on where it
   lives).
2. Find an existing reserved bit slot in the table above (most words
   have 13–24 spare bits).
3. Update the always_comb packing in that macro and update this doc.
4. If no slot fits, add a new word — extend `obs_words_o` length and
   update F1 to expose the extra register.
