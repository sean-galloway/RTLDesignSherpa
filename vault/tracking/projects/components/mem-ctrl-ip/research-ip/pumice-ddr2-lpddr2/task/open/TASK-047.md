# TASK-047: dual issue on DFI 1:2 -- a row command beside the column in one DFI word

> Source: owner, 2026-10-23 ("Do 1/2/3"), item 3 of the FR-FCFS parity
> work: after bank preparation (TASK-045) the one remaining structural
> difference between this controller and the textbook FR-FCFS setting is
> that the command slot and the data slot are the same slot. Related:
> TASK-045 (bank preparation, the policy half), the reverted 2026-07
> bank-parallel scheduler (`4eeb37f9`, a different design on the
> pre-recovery FSM scheduler; its board failure was the open-page read
> return path, not dual issue as such), Phase 3 report section 3
> (the arbiter cone is the 75 MHz critical path at +0.001 ns).

**Priority:** P3 (research; bounded gain, real timing risk)
**Status:** open -- design study done, not started
**Owner:** TBD

## Why

At the board point (BL4 on x16, DFI 1:2, one command per 75 MHz sys clock)
one column command per cycle saturates the data bus, so every ACT and PRE
costs a column slot. TASK-045 made the FR-FCFS core spend those slots at
the right moment (inside the column's dead time, bank prepared before its
columns arrive); it does not make them free. Per 8-column row on a bank
walk that is 1 slot in 9 (11 percent, 533 of 600 MB/s); on a row-hit
stream it is nothing. The textbook controller does not pay it because its
command bus has slack. On DFI 1:2 the PHY accepts a command on EACH of the
two phases of a DFI word, i.e. two commands per sys clock; the controller
uses one (phase 0, the other phase NOP: `mc_xddr2_cmd_formatter` "v1
places the issued command on phase 0"). Putting the row command on the
other phase restores the slack.

## Ceiling (measured inputs)

| shape | slots per row now (TASK-045) | with dual issue | gain |
|---|---|---|---|
| col_interleave, 8 columns per row, AP close | 9 | 8 | 11 percent (up to 600 from ~533) |
| col_interleave with explicit PRE (predictor not armed) | 10 | 8 | 20 percent |
| col_major (same bank) | 13 rd / 15 wr (JEDEC floor) | unchanged | 0 -- the floor is tRP + tRCD, not slots |
| incremental / row_major | ~1.03 (ACT per row of 256+ columns) | ~1.00 | < 3 percent |

So the gain is bounded to the bank-walk families and to what the page
policy leaves as explicit PREs; a mixed workload with many short rows is
the case that benefits.

## Design

1. **Two output lanes in `mc_cmd_arbiter`:** the pick comb already keeps
   the classes in separate pre-pick registers (`*_col_f`, `*_act_f`,
   `*_pre_f`), so a second output register holding a ROW command
   (ACT or PRE) can be filled in the same cycle as the column register
   whenever both classes are ready for different banks. The fire stage
   checks each lane against its own bank's live readiness
   (`w_out_safe` per lane). The two lanes never target the same bank in
   one word.
2. **Command FIFO entry carries two commands** (`mc_common_pkg`'s command
   struct gets a second, optional, row-command half, or the plane pushes a
   2-wide word). `mc_scheduler_plane`'s CMD_DELAY token path is per word,
   unchanged.
3. **Phase placement:** row command on phase 0, column on phase 1 of the
   same word. Then a column that follows an ACT to the SAME bank is never
   in the same word (the bank timers have not counted the ACT yet, so the
   column is not ready), and tRCD/tRP measured in whole sys clocks from the
   word stays conservative by construction. Columns moving to phase 1
   shifts the DFI data phase by one CK: `rd_phase_i` / `wr_phase_i` are
   runtime (the bring-up tuple was taken at phase 0), so the PHY alignment
   has to be re-measured on the board (`t_rddata_en`, `t_phy_wrlat`).
4. **Bank timers take two events per cycle** (`mc_bank_timers` has one
   `evt_*` set; add a second, or OR the two lanes' events into per-bank
   strobes since the lanes are to different banks). `mc_global_timers`:
   tRRD / tFAW count ACTs; two ACTs never share a word (one lane is a
   column), so one ACT per cycle still holds. tCCD is per column; one
   column per word.
5. **Command history checker and the DFI slave model** need to accept two
   commands per DFI word (the checker's "need N cycles" reads whole words;
   a phase-1 column after a phase-0 ACT on another bank is legal).
6. **Formal:** the arbiter proof's single-output invariants become per lane
   plus "lanes are to different banks".

## Risk

- **Timing is the gate.** The FR-FCFS arbiter cone IS the 75 MHz critical
  path (+0.001 ns on the committed text, Phase 3 report 3.2). A second
  pick in the same cycle adds a second pick mux and a second fire check in
  parallel (not in series) -- the row lane's inputs are the existing
  `*_act_f` / `*_pre_f` registers -- but the output-register load logic
  and the FIFO push width grow. Must be built OOC first at the board
  generics (report 5.3 flow) before any board build. The 75 MHz floor is
  not negotiable (owner).
- **Board PHY alignment** with columns on phase 1 (above). A sim-green
  dual issue that misaligns the data phase on silicon would repeat the
  2026-07 story; the ILA-first bring-up applies.
- **BANK_PICK parity:** the per-bank core would need the same second lane
  to keep the two cores comparable; otherwise the product core falls behind
  the research core by the bank-walk gain above.

## Not this task

- A 1:4 DFI (four phases) -- the board is 1:2 at 75 MHz.
- Issuing two COLUMNS per word (BL4 on DFI 1:2 is one column per word by
  data-bus width; `N_SUBCMD` already handles the BL4-at-1:4 case).

## Done when

- OOC at board generics closes 75 MHz with the second lane; the board build
  keeps a positive WNS.
- Bench (`test_pumice_core_bankprep.py`): col_interleave 8 slots per row
  both directions; proxy col_interleave at eight threads within 2 percent
  of the streaming families.
- Both geometries' pumice regression, granite, common-ip, formal, lint; the
  DFI slave model and the history checker updated and their unit tests
  passing; the HAS/MAS DFI chapter updated.
