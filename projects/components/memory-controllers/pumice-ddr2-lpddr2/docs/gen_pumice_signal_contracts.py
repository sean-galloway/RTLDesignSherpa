#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate pumice_signal_contracts.xlsx -- the ONE pumice signal-contract and
K-map workbook.

Merged 2026-09-10 from four workbooks that had drifted apart:

    docs/pumice_signal_contracts.xlsx        (grid K-maps + AXI/scheduler contracts)
    design/kmaps/pumice_cmd_path_kmap.xlsx   (command-path decision tables)
    design/kmaps/pumice_data_path_kmap.xlsx  (data-path decision tables)
    design/kmaps/pumice_write_path_kmap.xlsx (write drain/commit detail)

They overlapped on the arbiter and the bank timers while each held material the
others did not, and they were emitted by three generators in two directories,
so nobody could say which one was current. One file, one generator, one place
to look.

Two kinds of page live here, and the difference matters:

  * DECISION TABLES (CMD_DECISION, WR_DRAIN, ...) are the SPEC. One row per
    decision case in priority order, with the effect spelled out. Spec-first:
    RTL is written to match these, not the other way round. Some carry an
    explicit "broken today" note where the RTL does not yet match.
  * COMPUTED K-MAPS (K-maps arbiter / bank timer / refresh+top) are the
    AS-BUILT evidence. Every cell is evaluated from a python mirror of the
    exact RTL expression, file:line cited, so grid and RTL agree by
    construction; the inspection note says what a healthy map looks like so a
    bad edit shows on sight. Cells are computed, never drawn.

Regenerate from scratch (idempotent -- the old flow LOADED the workbook and
appended rows, so re-running it silently duplicated them; the committed
Scheduler sheet had accumulated 8 duplicate rows that way):

    python3 docs/gen_pumice_signal_contracts.py

Coverage is not yet complete against vault/handbook/design/signal-contracts-and-kmaps.md
-- see PUMICE-KMAP for what is still missing (axis equations and implicants on
the grid pages).
"""
from __future__ import annotations
import os

import openpyxl
from openpyxl import Workbook
from openpyxl.styles import Alignment, Border, Font, PatternFill, Side

HERE = os.path.dirname(os.path.abspath(__file__))
XLSX = os.path.join(HERE, "pumice_signal_contracts.xlsx")

# shared styling for the index + carried contract sheets
IX_TITLE = Font(bold=True, size=13)
IX_HDR = Font(bold=True, color="FFFFFF")
IX_HDR_FILL = PatternFill("solid", fgColor="374151")
IX_NOTE = Font(italic=True, color="6B7280")
IX_WRAP = Alignment(horizontal="left", vertical="top", wrap_text=True)
IX_THIN = Border(*[Side(style="thin", color="D1D5DB")] * 4)

CONTRACT_SHEETS = {'AXI to CAMs': [['pumice_axi4_ifc — AXI <-> CAM signal contracts',
                  None,
                  None,
                  None,
                  None,
                  None,
                  None,
                  None],
                 ['Legal behavior of every signal at the AXI-to-CAM boundary (board x16 cfg: '
                  'AXI=64b, DRAM_BEAT=32b, DEVICE=16b, DFI_RATE=2, ROW=13, COL=10). Red rows = '
                  'current on-board read-corruption suspects (device-word de-interleave). AXI4 '
                  'VALID/READY rule applies to all channels.',
                  None,
                  None,
                  None,
                  None,
                  None,
                  None,
                  None],
                 [None, None, None, None, None, None, None, None],
                 ['Group / Channel',
                  'Signal',
                  'Width (x16 cfg)',
                  'Dir',
                  'Driver',
                  'Legal / Correct behavior (contract)',
                  'Key invariant — assertable check',
                  'Notes / bug-suspect'],
                 ['AW (write addr)',
                  's_axi_awvalid',
                  '1',
                  'in',
                  'master',
                  'VALID for a new write cmd; holds until awready. AXI4 handshake: VALID must NOT '
                  'wait for READY; once VALID=1 it stays 1 with STABLE payload until VALID&&READY; '
                  'READY may wait for VALID; transfer occurs on the cycle VALID&&READY.',
                  'awvalid stable; no drop before awready',
                  None],
                 ['AW',
                  's_axi_awready',
                  '1',
                  'out',
                  'wr CAM',
                  'High only when a CAM entry is free to allocate. Backpressure when CAM full.',
                  'awready=0 => CAM full; never accept when NUM valid==NUM_ENTRIES',
                  None],
                 ['AW',
                  's_axi_awaddr',
                  'AW',
                  'in',
                  'master',
                  'Byte address; decoded to {rank,bank,row,col} via bank_lsb/hash. Aligned to '
                  'awsize.',
                  'decoded bank<NUM_BANKS, row<2^ROW, col<2^COL; col LSBs = byte offset',
                  None],
                 ['AW',
                  's_axi_awlen',
                  '8',
                  'in',
                  'master',
                  'Burst beats-1 (AXI). Split into DRAM bursts of DRAM_BL by the intake.',
                  'awlen+1 beats produced on B/■; split count = ceil((awlen+1)/beats_per_DRAM_cmd)',
                  None],
                 ['AW',
                  's_axi_awsize',
                  '3',
                  'in',
                  'master',
                  'Bytes/beat = 2^awsize; must equal AXI_DATA/8 for full-width (=8 for 64b).',
                  '2^awsize <= AXI_DATA/8',
                  None],
                 ['AW',
                  's_axi_awburst',
                  '2',
                  'in',
                  'master',
                  'INCR(01) expected; WRAP/FIXED per config.',
                  'awburst==INCR for linear DRAM mapping',
                  None],
                 ['AW',
                  's_axi_awid/awuser',
                  'IW/UW',
                  'in',
                  'master',
                  'ID/user carried to matching B response.',
                  'bid==awid of the same transaction; in-order per ID',
                  None],
                 ['W (write data)',
                  's_axi_wvalid/wready',
                  '1',
                  'in/out',
                  'master / wr CAM',
                  'One beat/cycle; wready when the CAM data slot can accept. AXI4 handshake: VALID '
                  'must NOT wait for READY; once VALID=1 it stays 1 with STABLE payload until '
                  'VALID&&READY; READY may wait for VALID; transfer occurs on the cycle '
                  'VALID&&READY.',
                  'beats accepted == awlen+1 before wlast',
                  None],
                 ['W',
                  's_axi_wdata',
                  'DW=64',
                  'in',
                  'master',
                  'Write payload, little-endian byte order.',
                  'byte i of wdata -> DRAM byte at (col_byte+i)',
                  None],
                 ['W',
                  's_axi_wstrb',
                  'SW=8',
                  'in',
                  'master',
                  'Per-byte write enable; DFI mask = ~wstrb.',
                  'dfi_wrdata_mask == ~wstrb for the mapped bytes',
                  None],
                 ['W',
                  's_axi_wlast',
                  '1',
                  'in',
                  'master',
                  'Marks final beat of the write burst.',
                  'exactly one wlast per awlen+1 beats; triggers B',
                  None],
                 ['B (write resp)',
                  's_axi_bvalid/bready',
                  '1',
                  'out/in',
                  'wr CAM / master',
                  'B raised after the write is COMMITTED (data safely queued to DFI), one per AW.',
                  'one B per AW; bvalid only after wlast accepted AND wr_commit done',
                  None],
                 ['B',
                  's_axi_bresp',
                  '2',
                  'out',
                  'wr CAM',
                  'OKAY(00) normal.',
                  'bresp==OKAY unless error',
                  None],
                 ['AR (read addr)',
                  's_axi_arvalid/arready',
                  '1',
                  'in/out',
                  'master / rd CAM',
                  'VALID for a new read; arready when a rd-CAM entry is free. AXI4 handshake: '
                  'VALID must NOT wait for READY; once VALID=1 it stays 1 with STABLE payload '
                  'until VALID&&READY; READY may wait for VALID; transfer occurs on the cycle '
                  'VALID&&READY.',
                  'arready=0 => rd CAM full',
                  None],
                 ['AR',
                  's_axi_araddr/arlen/arsize',
                  'AW/8/3',
                  'in',
                  'master',
                  'Same decode + split rules as AW.',
                  'decoded bank/row/col in range; split to DRAM_BL reads',
                  None],
                 ['AR',
                  's_axi_arid/aruser',
                  'IW/UW',
                  'in',
                  'master',
                  'Carried to matching R beats.',
                  'rid==arid; R beats in AR order per ID (rd_in_order)',
                  None],
                 ['R (read data)',
                  's_axi_rvalid/rready',
                  '1',
                  'out/in',
                  'rd CAM / master',
                  'One R beat/cycle as read data returns; rvalid gated by rd_dfi_ret_valid. AXI4 '
                  'handshake: VALID must NOT wait for READY; once VALID=1 it stays 1 with STABLE '
                  'payload until VALID&&READY; READY may wait for VALID; transfer occurs on the '
                  'cycle VALID&&READY.',
                  'beats emitted == arlen+1; exactly one rlast',
                  None],
                 ['R',
                  's_axi_rdata',
                  'DW=64',
                  'out',
                  'rd CAM',
                  'DRAM read data re-assembled to AXI beat order. For x16: each 64b DFI word = 2 '
                  'phases x 2 device-words(16b); the 4 device-words of a BL4 read must appear in '
                  'ASCENDING DDR-beat/address order: {p0.dw0,p0.dw1,p1.dw0,p1.dw1}.',
                  'rdata[beat k] == golden(addr + k*bytes); device-word order matches write order',
                  'RESOLVED 2026-07-22: the on-board device-word/shift story was host config + '
                  'measurement (see #39 close-out) — read path clean at the bring-up tuple '
                  '(wrlat=1/rden=6/rdly=7). Remaining integrity issue = runtime config axes, #42.'],
                 ['R',
                  's_axi_rlast',
                  '1',
                  'out',
                  'rd CAM',
                  'Marks final beat of the read burst.',
                  'one rlast per arlen+1 beats',
                  None],
                 ['R',
                  's_axi_rresp',
                  '2',
                  'out',
                  'rd CAM',
                  'OKAY(00) normal.',
                  'rresp==OKAY unless error',
                  None],
                 ['Config',
                  'bank_lsb_i',
                  '5',
                  'in',
                  'CSR',
                  'Bank field LSB position in the address stack.',
                  'stable during traffic; retire scheme mux',
                  None],
                 ['Config',
                  'hash_en_i/hash_seed_i',
                  '1/8',
                  'in',
                  'CSR',
                  'XOR-hash bank select enable + seed.',
                  'stable during traffic',
                  None],
                 ['wr CAM->sched',
                  'wr_sch_valid_o',
                  'NUM_ENTRIES',
                  'out',
                  'wr CAM',
                  'Bit i=1 => CAM entry i holds a pending write awaiting schedule.',
                  'valid[i] set on alloc, cleared on wr_commit of slot i',
                  None],
                 ['wr CAM->sched',
                  'wr_sch_bank_o/row_o/col_o',
                  'N*BKW / N*ROW / N*COL',
                  'out',
                  'wr CAM',
                  'Per-entry decoded target; REGISTERED, stable while valid[i]=1.',
                  '{bank,row,col}[i] stable from alloc to commit; == decoded awaddr',
                  None],
                 ['wr CAM->sched',
                  'wr_sch_older_o',
                  'N*N',
                  'out',
                  'wr CAM',
                  'Age matrix: older[i*N+j]=1 => entry i inserted before j. Set on INSERT only.',
                  'antisymmetric: older[i,j] ^ older[j,i] for valid i!=j; picker uses '
                  'argmax-oldest',
                  None],
                 ['wr commit',
                  'wr_commit_valid_i',
                  '1',
                  'in',
                  'scheduler',
                  'Scheduler asserts to commit/drain the write at slot.',
                  'valid only for a currently-valid slot',
                  None],
                 ['wr commit',
                  'wr_commit_ready_o',
                  '1',
                  'out',
                  'wr CAM',
                  "CAM ready to drain that slot's data to DFI.",
                  'commit occurs on valid&&ready; frees entry after last data beat',
                  None],
                 ['wr commit',
                  'wr_commit_slot_i',
                  'PTRW',
                  'in',
                  'scheduler',
                  'CAM entry index to commit.',
                  'slot < NUM_ENTRIES and valid[slot]=1',
                  None],
                 ['wr drain->DFI',
                  'wr_cm_rd_valid_o/ready_i',
                  '1',
                  'out/in',
                  'wr CAM / DFI',
                  'Committed write data streamed one DFI-word/cycle to the DFI layer.',
                  'words emitted == DRAM_BL/DFI_RATE per DRAM cmd; one last per burst',
                  None],
                 ['wr drain->DFI',
                  'wr_cm_rd_data_o/strb_o/last_o',
                  'DW/SW/1',
                  'out',
                  'wr CAM',
                  'DFI-word data + strobe; last marks final word of the committed burst.',
                  'data order == ascending device-word/beat (mirror of the read contract)',
                  None],
                 ['rd CAM->sched',
                  'rd_sch_valid_o',
                  'NUM_ENTRIES',
                  'out',
                  'rd CAM',
                  'Bit i=1 => pending read entry i.',
                  'set on alloc, cleared on rd_issue of slot i',
                  None],
                 ['rd CAM->sched',
                  'rd_sch_bank_o/row_o/col_o',
                  'N*BKW/N*ROW/N*COL',
                  'out',
                  'rd CAM',
                  'Per-entry decoded target; REGISTERED, stable while valid[i]=1.',
                  '{bank,row,col}[i] stable alloc->issue; == decoded araddr',
                  None],
                 ['rd CAM->sched',
                  'rd_sch_older_o',
                  'N*N',
                  'out',
                  'rd CAM',
                  'Age matrix (same rule as wr).',
                  'antisymmetric; oldest-first issue when rd_in_order',
                  None],
                 ['rd issue',
                  'rd_issue_valid_i/ready_o/slot_i',
                  '1/1/PTRW',
                  'in/out/in',
                  'scheduler / rd CAM',
                  'Scheduler issues the read at slot; CAM marks it in-flight to DFI.',
                  'issue on valid&&ready; slot valid; entry retires on rd_dfi_ret last',
                  None],
                 ['rd return<-DFI',
                  'rd_dfi_ret_valid_i/ready_o',
                  '1',
                  'in/out',
                  'DFI / rd CAM',
                  'DFI layer returns read data words; CAM re-splits to AXI R beats.',
                  'one word/cycle; total words == issued reads * DRAM_BL/DFI_RATE',
                  'RESOLVED 2026-07-22: the on-board device-word/shift story was host config + '
                  'measurement (see #39 close-out) — read path clean at the bring-up tuple '
                  '(wrlat=1/rden=6/rdly=7). Remaining integrity issue = runtime config axes, #42.'],
                 ['rd return<-DFI',
                  'rd_dfi_ret_data_i',
                  'DW=64',
                  'in',
                  'DFI',
                  'One DFI read word (2 phases x 2 x16 device-words) from the aligner.',
                  'must be de-interleaved to ascending device-word order before R',
                  '*** ILA: raw word OK at DFI boundary; corruption is in the split to R ***'],
                 ['rd return<-DFI',
                  'rd_dfi_ret_resp_i/last_i',
                  '2/1',
                  'in',
                  'DFI',
                  'Response + last-word marker.',
                  'last aligns with the final DFI word of the AXI burst',
                  None],
                 ['status',
                  'busy_o',
                  '1',
                  'out',
                  'ifc',
                  'High while any AXI txn is in flight.',
                  'busy=0 => all CAMs empty, no pending B/R',
                  None]],
 'Scheduler both dirs': [['pumice_mem_cmd_scheduler — upstream (<-CAMs) + downstream (->DFI)',
                          None,
                          None,
                          None,
                          None,
                          None,
                          None,
                          None],
                         ['Upstream: consume per-entry CAM vectors, drive commit/issue. '
                          'Downstream: abstract DRAM command stream to the DFI layer. Timing CSRs '
                          'define the legal command spacing (tCCD=2 => the DQ bubble the '
                          'delay-line serializers must honor).',
                          None,
                          None,
                          None,
                          None,
                          None,
                          None,
                          None],
                         [None, None, None, None, None, None, None, None],
                         ['Group / Channel',
                          'Signal',
                          'Width (x16 cfg)',
                          'Dir',
                          'Driver',
                          'Legal / Correct behavior (contract)',
                          'Key invariant — assertable check',
                          'Notes / bug-suspect'],
                         ['UP: sched<-CAM (wr)',
                          'wr_sch_valid_i',
                          'NUM_ENTRIES',
                          'in',
                          'wr CAM',
                          'Per-entry pending-write bitmap the picker arbitrates over.',
                          'combinational read; a set bit MUST have stable bank/row/col',
                          None],
                         ['UP: sched<-CAM (wr)',
                          'wr_sch_bank_i/row_i/col_i',
                          'N*BKW/N*ROW/N*COL',
                          'in',
                          'wr CAM',
                          'Registered per-entry targets used for bank-parallel activate + column '
                          'pick.',
                          'picker only uses fields of currently-valid entries',
                          None],
                         ['UP: sched<-CAM (wr)',
                          'wr_sch_older_i',
                          'N*N',
                          'in',
                          'wr CAM',
                          'Age matrix for oldest-first tie-break.',
                          'argmax-oldest = masked AND older-than-all-masked (1-bit compares)',
                          None],
                         ['UP: sched->CAM (wr)',
                          'wr_commit_valid_o/ready_i/slot_o',
                          '1/1/PTRW',
                          'out/in/out',
                          'scheduler',
                          'Scheduler commits the chosen write slot; gated by CAM ready '
                          '(backpressure).',
                          'commit only on valid&&ready; never commit a non-valid slot; +1 commit '
                          'latency vs pick',
                          'goldens updated for +1 write-commit latency (task #99)'],
                         ['UP: sched<-CAM (rd)',
                          'rd_sch_valid_i / bank_i/row_i/col_i / older_i',
                          'N / N*.. / N*N',
                          'in',
                          'rd CAM',
                          'Mirror of the write vectors for the read picker.',
                          'same stability + antisymmetry rules',
                          None],
                         ['UP: sched->CAM (rd)',
                          'rd_issue_valid_o/ready_i/slot_o',
                          '1/1/PTRW',
                          'out/in/out',
                          'scheduler',
                          'Scheduler issues the chosen read; gated by rd_issue_ready.',
                          'issue only on valid&&ready; rd_in_order => strictly oldest first',
                          'read column mask gated on rd_issue_ready (stale-DRAM fix)'],
                         ['DOWN: sched->DFI',
                          'cmd_valid_o/cmd_ready_i',
                          '1',
                          'out/in',
                          'scheduler / DFI',
                          'One abstract DRAM command per handshake; DFI backpressures via '
                          'cmd_ready.',
                          'VALID stable w/ stable payload until ready; no command dropped under '
                          'backpressure',
                          'arbiter output register: +1 latency, throttles columns to tCCD cadence'],
                         ['DOWN: sched->DFI',
                          'cmd_op_o',
                          'dram_op_e',
                          'out',
                          'scheduler',
                          'ACT / RD / WR / PRE / REF / (RDA/WRA auto-precharge) / MRS / init ops.',
                          'ACT precedes RD/WR to a bank; PRE before re-ACT of a new row; REF '
                          'honored at t_refi',
                          None],
                         ['DOWN: sched->DFI',
                          'cmd_bank_o/cmd_row_o/cmd_col_o',
                          'BKW/ROW/COL',
                          'out',
                          'scheduler',
                          'Target of the command. RD/WR carry col; ACT carries row; PRE carries '
                          'bank.',
                          "RD/WR col only valid if that bank's open row == cmd_row (page hit) or "
                          'just-activated',
                          None],
                         ['DOWN: sched->DFI',
                          'cmd_ap_o',
                          '1',
                          'out',
                          'scheduler',
                          'Auto-precharge flag (RDA/WRA).',
                          'ap set => bank auto-precharges after the access (no explicit PRE)',
                          None],
                         ['DOWN: sched->DFI',
                          'cmd_rank_o',
                          'RKW',
                          'out',
                          'scheduler',
                          'Rank select (1 rank on this board).',
                          'rank < NUM_RANKS',
                          None],
                         ['Timing cfg',
                          't_rcd/t_rp/t_ras/t_rc',
                          '8 each',
                          'in',
                          'CSR',
                          'ACT->RD/WR (tRCD), PRE->ACT (tRP), ACT->PRE (tRAS), ACT->ACT same bank '
                          '(tRC).',
                          'scheduler must not emit RD/WR to a bank < tRCD after its ACT, etc.',
                          None],
                         ['Timing cfg',
                          't_wr/t_rtp/t_wtr/t_rtw/t_ccd',
                          '8 each',
                          'in',
                          'CSR',
                          'Write-recovery, read-to-precharge, write-to-read, read-to-write, '
                          'col-to-col (tCCD).',
                          'consecutive RD/RD or WR/WR to open pages spaced >= tCCD (=2) => the DQ '
                          'bubble the aligner/serializer MUST honor (see delay-line fix)',
                          'tCCD=2 is the read/write pacing'],
                         ['Timing cfg',
                          't_faw/t_rrd',
                          '8 each',
                          'in',
                          'CSR',
                          'Four-activate window; ACT-to-ACT diff bank.',
                          '<=4 ACTs per tFAW; ACTs spaced >= tRRD',
                          None],
                         ['Timing cfg',
                          't_refi/refresh_burst',
                          '16/4',
                          'in',
                          'CSR',
                          'Refresh interval; refreshes per burst.',
                          'REF emitted every t_refi; REF only under w_ref_safe (rows closed + '
                          'nothing in flight/guarded + prior tRFC elapsed); drain REFs tRFC-spaced',
                          None],
                         ['Init',
                          'dfi_init_start_o/dfi_init_complete_i/init_done_o',
                          '1 each',
                          'out/in/out',
                          'sched / DFI',
                          'JEDEC init FSM: start -> PHY calibrates -> complete -> MR programming '
                          '-> init_done.',
                          'no user RD/WR accepted until init_done; MR writes in JEDEC order',
                          'genuine FSM (stateful) — correct use'],
                         ['Init timing',
                          't_init_wait/t_dll_wait/t_mrd_wait/t_rp_wait/t_rfc_wait',
                          '16/16/8/8/8',
                          'in',
                          'CSR',
                          'JEDEC init waits: tINIT, tDLLK, tMRD, tRP, tRFC.',
                          'each init step waits its programmed count',
                          None],
                         ['Mode shadow->DFI',
                          'cl_o/cwl_o/bl_o',
                          '4 each',
                          'out',
                          'scheduler',
                          'CAS latency / CAS write latency / burst length shadow from the MR '
                          'writes. RTL reset = BL8 (MR0.VAL 0x0433); the Nexys board '
                          'runtime-programs BL4 (0x0432).',
                          'CL/CWL match MR0/MR2; BL matches MR0 (BL4 on this board) — the DFI read '
                          'window uses these',
                          'BL/CL feed the read de-interleave depth; verify against MR programmed'],
                         ['status',
                          'busy_o',
                          '1',
                          'out',
                          'scheduler',
                          'High while any command in flight or banks open.',
                          'busy=0 => idle, all banks precharged',
                          None],
                         ['Refresh iface',
                          'refresh_req_i / refresh_drain_i',
                          '1/1',
                          'in',
                          'refresh_ctrl',
                          'Owed-refresh request (pending>0) and burst-drain hold.',
                          'req high => arbiter priority-2 branch; columns/ACTs starve by design '
                          'while high',
                          None],
                         ['Refresh iface',
                          'refresh_grant_o',
                          '1',
                          'out',
                          'scheduler',
                          'Pulsed when the REF command FIRES (w_fire_out && r_grant).',
                          'one grant per issued REF; decrements pending + drain quota',
                          None],
                         ['Timing cfg',
                          't_rfc_i',
                          '16',
                          'in',
                          'CSR (TIMINGS_RFC_REFI.tRFC)',
                          'Mission-mode REF->ACT/REF recovery, MC cycles (reset 16). Loaded into '
                          "the arbiter's r_rfc_cnt on each fired REF.",
                          'no ACT or REF while r_rfc_cnt != 0 (w_rfc_busy) — audited by the '
                          "history checker's positional tRFC check",
                          'added 2026-07-21: previously enforced by NOTHING in mission mode'],
                         ['DV hooks',
                          'CMD_HISTORY_EN / HIST_T_*',
                          'param',
                          '-',
                          'generate',
                          'In-scheduler command-history scoreboard (audit-only shift registers on '
                          'the ISSUED stream; $fatal assertions, sim-only).',
                          'default 0 = zero cost; -GCMD_HISTORY_EN=1 + --assert in DV',
                          'moved into the scheduler 2026-07-22 (was a TB bind)']]}


def build_index(wb):
    """What is in this workbook and what each page is evidence OF."""
    ws = wb.create_sheet("INDEX")
    ws.cell(1, 1, "pumice signal contracts + K-maps").font = IX_TITLE
    ws.cell(2, 1, "One workbook. Generated by docs/gen_pumice_signal_contracts.py "
                  "-- edit the generator, never the sheet.").font = IX_NOTE
    for c, (name, w) in enumerate(
            (("sheet", 30), ("kind", 16), ("what it is evidence of", 96)), 1):
        cell = ws.cell(4, c, name)
        cell.font = IX_HDR; cell.fill = IX_HDR_FILL; cell.border = IX_THIN
        ws.column_dimensions[cell.column_letter].width = w
    rows = [
        ("AXI to CAMs", "contract", "AXI4 slave port -> wr/rd CAM signal contract: width, direction, "
         "owner, meaning, invariant."),
        ("Scheduler both dirs", "contract", "Scheduler interface both directions, including the refresh "
         "interface, t_rfc_i and the DV history-checker hooks."),
        ("READ_PATH_ADMIT", "contract", "AR admit cadence and reads-in-flight. The two limits that held "
         "board read bandwidth at 48.6% of peak until 2026-09-10."),
        ("CMD_DECISION", "spec table", "Per-bank FR-FCFS command decision in priority order."),
        ("AP_DECISION", "spec table", "Auto-precharge / page-policy decision."),
        ("TIMING_GATES", "spec table", "JEDEC timing gate legend: which counter blocks which command."),
        ("FORWARD_STATE", "spec table", "Forward (shadow) bank state the arbiter must schedule against."),
        ("WR_DRAIN", "spec table", "WR command -> dfi_wrdata presentation."),
        ("WR_COMMIT_B", "spec table", "Write commit and B-response gating (agg/last)."),
        ("RD_RETURN", "spec table", "Read return path and AR-order reassembly."),
        ("SAME_BANK_OUTSTANDING", "spec table", "Per-bank outstanding tracker."),
        ("RETURN_TAGGING", "spec table", "Return tagging: how a short/bad return is prevented from wedging."),
        ("DRAIN_HANDSHAKE", "spec table", "Arbiter commit -> drain FIFO -> DFI wr_fire."),
        ("CM_RD_STALL_CANDIDATES", "spec table", "Why the DFI stops accepting writes (the same-bank WR wedge)."),
        ("SERIALIZER_OWED", "spec table", "Serializer owed-beats accounting."),
        ("B_CONSOLIDATION", "spec table", "One B per host burst across split sub-commands."),
        ("K-maps arbiter", "computed", "w_ref_safe, w_rd_turn_block, w_out_ready, w_rfc_busy -- "
         "evaluated from the RTL expression, file:line cited."),
        ("K-maps bank timer", "computed", "w_ap_fire."),
        ("K-maps refresh+top", "computed", "w_grant_accept, w_drain_active."),
    ]
    for r, vals in enumerate(rows, 5):
        for c, v in enumerate(vals, 1):
            cell = ws.cell(r, c, v)
            cell.alignment = IX_WRAP; cell.border = IX_THIN
    return ws


def build_contract_sheets(wb):
    """The two hand-authored contract tables, carried verbatim.

    These are DATA, not derived: they were authored in the workbook and the old
    generator only patched cells in place, so they existed nowhere else. They
    live here as literals now, deduplicated (the append-on-every-run flow had
    left repeated rows behind).
    """
    for name, rows in CONTRACT_SHEETS.items():
        ws = wb.create_sheet(name)
        for r, vals in enumerate(rows, 1):
            for c, v in enumerate(vals, 1):
                if v is None:
                    continue
                cell = ws.cell(r, c, v)
                cell.alignment = IX_WRAP; cell.border = IX_THIN
                if r == 1:
                    cell.font = IX_HDR; cell.fill = IX_HDR_FILL
        for c, w in enumerate((16, 34, 8, 8, 22, 52, 52, 46), 1):
            ws.column_dimensions[ws.cell(1, c).column_letter].width = w
    return wb


def build_read_path_sheet(wb):
    """AR admit cadence + reads in flight -- the two read-side rate limits.

    Added 2026-09-10 because neither was written down anywhere and both cost
    board bandwidth for months. A sufficiency argument on the admit cone would
    have forced the question "what is the DRAM read rate at THIS geometry?",
    which is the question that was never asked.
    """
    ws = wb.create_sheet("READ_PATH_ADMIT")
    r = 1
    ws.cell(r, 1, "read path: AR admit cadence and reads in flight").font = IX_TITLE; r += 1
    ws.cell(r, 1, "One admitted sub-command is exactly ONE DRAM burst. Sustained read "
                  "bandwidth = admit rate x burst bytes, capped by reads-in-flight / "
                  "round-trip. Board 2026-09-10: 75 MHz, BL4 on x16, 32-bit beat -> one "
                  "burst is ONE AXI beat and 8 bytes, peak 600 MB/s.").font = IX_NOTE
    r += 2

    def _sec(title, cols, widths, rows):
        nonlocal r
        ws.cell(r, 1, title).font = Font(bold=True); r += 1
        for c, name in enumerate(cols, 1):
            cell = ws.cell(r, c, name)
            cell.font = IX_HDR; cell.fill = IX_HDR_FILL; cell.border = IX_THIN
            ws.column_dimensions[cell.column_letter].width = max(
                widths[c - 1], ws.column_dimensions[cell.column_letter].width or 0)
        r += 1
        for vals in rows:
            for c, v in enumerate(vals, 1):
                cell = ws.cell(r, c, v)
                cell.alignment = IX_WRAP; cell.border = IX_THIN
            r += 1
        r += 1

    _sec("TERM LIST", ("term", "defining expression", "citation"), (26, 60, 44), [
        ("fub_arvalid/arready", "AR skid-buffer head handshake",
         "pumice_rd_intake.sv (axi4_slave_rd instance)"),
        ("snarf_probe_*", "address presented to the wr CAM for RAW lookup",
         "pumice_rd_intake.sv snarf_probe_* assigns"),
        ("snarf_hit_i (w_hit)", "REGISTERED hit; belongs to whatever was probed LAST cycle",
         "pumice_wr_data_cam.sv (r_sp_* probe registers -> snarf_hit_o)"),
        ("r_s_valid", "AR staged for admit; its probe went out last cycle",
         "pumice_rd_intake.sv admit stage"),
        ("w_can_admit", "w_ord_wr_ready && (w_hit ? 1 : ar_push_ready_i)",
         "pumice_rd_intake.sv"),
        ("w_admit", "r_s_valid && w_can_admit", "pumice_rd_intake.sv"),
        ("RD_RET_DEPTH", "read return ring ticket count (reads in flight)",
         "pumice_rd_return_ring.sv, pumice_top.sv parameter"),
    ])

    _sec("INVARIANTS -- why only these terms", ("invariant", "why it holds"), (58, 78), [
        ("The hit on snarf_hit_i always belongs to the AR probed one cycle earlier.",
         "The probe is registered inside the wr CAM to pipeline the cross-module route. "
         "Admit must therefore lag probe by exactly one cycle -- that is a fact about "
         "the CAM, not a choice."),
        ("An AR held in the stage is re-probed every cycle it is held.",
         "The probe is re-pointed at the stage while it cannot admit, so the compare "
         "that admits is never more than one cycle old. A LATCHED hit would go stale "
         "against writes entering the wr CAM behind it -- the RAW case the probe exists for."),
        ("One admitted sub-command is one DRAM burst.",
         "pumice_axi_burst_chopper splits each AR into single-burst sub-commands; "
         "ar_push is both the rd CAM insert and the ring alloc."),
        ("Sustained reads <= RD_RET_DEPTH / (ticket alloc -> R drain).",
         "Little's law on the ring. The board's PHY read latency is ~49 MC cycles, so "
         "32 tickets bound reads at ~0.78 of the DRAM rate regardless of the admit rate."),
    ])

    _sec("DECISION TABLE -- admit cadence under an AR backlog",
         ("case", "r_s_valid", "w_can_admit", "fub_arvalid", "=> action", "next-cycle probe", "effect"),
         (7, 11, 13, 12, 22, 22, 60), [
        ("1", "0", "-", "1", "load stage", "skid head", "fill: stage takes the head, its probe goes out this cycle"),
        ("2", "1", "1", "1", "ADMIT + reload", "new skid head", "steady state -- one sub-command per cycle"),
        ("3", "1", "1", "0", "ADMIT, stage empties", "none", "backlog drained"),
        ("4", "1", "0", "-", "hold", "the STAGE", "downstream full; re-probe keeps the hit live"),
        ("5", "0", "-", "0", "idle", "none", "no AR"),
    ])

    _sec("BROKEN UNTIL 2026-09-10 -- and what it cost",
         ("what", "detail"), (30, 110), [
        ("the defect", "A single r_armed bit on the skid head marked 'the registered probe belongs "
         "to this AR'. It was CLEARED by its own admit and could only be re-set the next "
         "cycle, so case 2 above was impossible: admits capped at one every TWO cycles."),
        ("why it was invisible", "0.5 sub-cmd/cycle x beats-per-burst is the beat rate. The core "
         "testbench runs BL8 with a 64-bit beat and device == beat, so one burst is FOUR beats "
         "and half-rate admission still fed 2 beats/cycle. The board gets ONE beat per burst."),
        ("board cost", "0.5 x 8 B x 75 MHz = 300 MB/s ceiling; measured 291.7 (97% of it) against "
         "570 for writes, which have no such stage. LiteDRAM read 579 on the same board and PHY."),
        ("second limit", "RD_RET_DEPTH was 32 and ddr2_char_macro never passed the parameter, so "
         "every board build ran the default. At ~49 cycles of read latency that caps reads near "
         "0.78 of the DRAM rate -- exactly where the admit fix left them (470.9 MB/s)."),
        ("after both fixes", "read 571.3 MB/s at ring 64 = write parity (570.2) and 95% of peak. "
         "Timing improved (+0.285 vs +0.039 ns). PUMICE-025."),
        ("guard", "dv/tests/top/test_pumice_core_dfi.py::perf_intake_admit_rate conditions on "
         "'could this intake have admitted', so it is geometry-independent, with the write "
         "intake as the control."),
    ])
    return ws


KM_HDR = Font(bold=True, color="FFFFFF")
KM_HDR_FILL = PatternFill("solid", fgColor="374151")
KM_TITLE = Font(bold=True, size=13)
KM_NOTE = Font(italic=True, color="6B7280")
KM_CENTER = Alignment(horizontal="center", vertical="center")
KM_WRAP = Alignment(horizontal="left", vertical="top", wrap_text=True)
KM_THIN = Border(*[Side(style="thin", color="D1D5DB")] * 4)
# command -> fill (semantic colour so the decision reads at a glance)
KM_CMDFILL = {
    "NOP":  "E5E7EB", "ACT":  "BFDBFE", "PRE":  "FDE68A", "PREA": "FCD34D",
    "RD":   "BBF7D0", "RDA":  "86EFAC", "WR":   "FBCFE8", "WRA":  "F9A8D4",
    "REF":  "FCA5A5", "REFPB":"FECACA",
}


def _km_hdr_row(ws, row, cols, widths=None):
    for c, name in enumerate(cols, 1):
        cell = ws.cell(row=row, column=c, value=name)
        cell.font = KM_HDR; cell.fill = KM_HDR_FILL; cell.alignment = KM_CENTER
        cell.border = KM_THIN
    if widths:
        for c, w in enumerate(widths, 1):
            ws.column_dimensions[ws.cell(row=1, column=c).column_letter].width = w


def _km_row(ws, row, vals, cmd_col=None):
    for c, v in enumerate(vals, 1):
        cell = ws.cell(row=row, column=c, value=v)
        cell.alignment = KM_CENTER if len(str(v)) < 14 else KM_WRAP
        cell.border = KM_THIN
        if cmd_col and c == cmd_col and v in KM_CMDFILL:
            cell.fill = PatternFill("solid", fgColor=KM_CMDFILL[v])
            cell.font = Font(bold=True)


def _km_title(ws, text, sub=None):
    ws.cell(row=1, column=1, value=text).font = KM_TITLE
    if sub:
        ws.cell(row=2, column=1, value=sub).font = KM_NOTE
    return 4  # first data row


# ---------------------------------------------------------------------------
# CMD-PATH workbook
# ---------------------------------------------------------------------------
def cmd_path_sheets(wb):

    # --- Sheet 1: the per-bank FR-FCFS command decision -------------------
    ws = wb.create_sheet("CMD_DECISION")
    r = _km_title(ws,
        "pumice per-bank command decision (FR-FCFS) -- IDEAL",
        "One row = one decision case, in PRIORITY order (top wins). Evaluated "
        "per candidate bank every aclk; the picker emits the highest-priority "
        "ready command across banks, ONE per cycle. '-' = don't-care. Issue "
        "rate is gated ONLY by DRAM timers -- never by pick-pipeline occupancy.")
    cols = ["prio", "refresh_due", "row_active", "row_hit", "col_pending",
            "act_ready\n(tRC/tRP)", "rdwr_ready\n(tRCD)", "pre_ready\n(tRAS)",
            "tCCD_ok", "tRRD/tFAW_ok", "turn_ok\n(tWTR/tRTW)", "=> CMD",
            "why / effect"]
    _km_hdr_row(ws, r, cols,
             widths=[5,11,10,8,11,11,10,10,8,12,11,8,46]); r += 1
    CMD = len(cols)  # cmd column index for fill
    rows = [
        [1,"Y","-","-","-","-","-","Y","-","-","-","REF",
         "refresh due AND all banks precharge-safe -> REFab (see PRE_ALL row)"],
        [2,"Y","Y","-","-","-","-","Y","-","-","-","PRE",
         "refresh due but a row is still open -> precharge it first (all banks), THEN REF"],
        [3,"N","Y","Y","Y","-","Y","-","Y","-","Y","RD/WR",
         "PAGE HIT: row open, column ready, tCCD+turnaround met -> issue column. "
         "The throughput path: back-to-back at tCCD, NO occupancy stall."],
        [4,"N","N","-","Y","Y","-","-","-","Y","-","ACT",
         "PAGE EMPTY: activate the requested row. tRRD/tFAW gate cross-bank ACT rate, "
         "not the column stream."],
        [5,"N","Y","N","Y","-","-","Y","-","-","-","PRE",
         "PAGE CONFLICT: row open but wrong row -> precharge (tRAS met) to reopen"],
        [6,"N","Y","Y","Y","-","N","-","-","-","-","NOP",
         "hit but tRCD not yet met (just ACTed) -> wait; do NOT block other banks"],
        [7,"N","-","-","N","-","-","-","-","-","-","NOP",
         "no pending column for this bank -> idle (page stays OPEN in open-page policy)"],
        [8,"N","Y","Y","Y","-","Y","-","N","-","-","NOP",
         "column ready but tCCD not met -> the ONLY legal reason to space same-bank "
         "columns; == tCCD, not pipeline depth"],
    ]
    for x in rows:
        _km_row(ws, r, x, cmd_col=CMD); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="RTL STATUS 2026-09-10: LARGELY CLOSED. The arbiter used to AND a blanket "
                        "!w_col_inflight_bank (pick-pipeline occupancy) into rows 3/6/8, forcing "
                        "one same-bank column per ~pipeline-depth instead of per tCCD. It is now "
                        "AP-GATED -- !(f_ap(b) && w_col_inflight_bank[b]) -- so a non-AP column is "
                        "gated only by the DRAM timers above, as this table asks. Narrowed rather "
                        "than removed on purpose: an AP column closes the row behind it, and a "
                        "second same-bank column picked against the stale open-row image would be "
                        "issued to a closing row. Remaining gap: AP columns are still one-per-bank "
                        "in flight. (pumice_cmd_arbiter.sv:589,605)").font = KM_NOTE

    # --- Sheet 2: auto-precharge (AP) bit / page policy ------------------
    ws = wb.create_sheet("AP_DECISION")
    r = _km_title(ws, "column auto-precharge (RD->RDA / WR->WRA) -- page policy",
               "Decides the A10 auto-precharge bit on a column command. Sets "
               "whether the row stays open (streaming) or self-closes.")
    cols = ["page_policy", "last_col_to_page", "page_timeout_fired", "=> AP bit",
            "=> emitted op", "effect"]
    _km_hdr_row(ws, r, cols, widths=[13,16,17,9,13,40]); r += 1
    for x in [
        ["OPEN","N","N","0","RD / WR","row stays open -> next hit streams at tCCD"],
        ["OPEN","-","Y","1","RDA / WRA","idle/timeout close (fixed_open/adapt_time)"],
        ["CLOSE","-","-","1","RDA / WRA","every access self-precharges; next access re-ACTs"],
        ["OPEN","Y","N","0","RD / WR","open policy never AP on last col; explicit PRE closes"],
    ]:
        _km_row(ws, r, x, cmd_col=5); r += 1

    # --- Sheet 3: timing-gate legend ------------------------------------
    ws = wb.create_sheet("TIMING_GATES")
    r = _km_title(ws, "timing gates -> DDR2-300 values (controller/aclk cycles)",
               "Each gate is a registered timer output the decision consumes. "
               "These are the ONLY things allowed to throttle issue rate.")
    cols = ["gate signal", "DDR2 param", "cyc @75MHz", "gates which command", "meaning"]
    _km_hdr_row(ws, r, cols, widths=[22,14,11,20,44]); r += 1
    for x in [
        ["bank_act_ready_i","tRC / tRP","6 / 3","ACT","row-cycle / precharge done -> may ACT"],
        ["bank_rdwr_ready_i","tRCD","3","RD / WR","ACT-to-column met -> may issue column"],
        ["bank_pre_ready_i","tRAS / tRTP","4 / 2","PRE","min row-open / read-to-precharge met"],
        ["tccd_ok_i","tCCD","2 (BL4)","RD / WR","column-to-column; THE same-bank spacing"],
        ["twtr_ok_i","tWTR","2","RD after WR","write-to-read turnaround"],
        ["trtw_ok_i","tRTW","2","WR after RD","read-to-write turnaround"],
        ["trrd_ok_i","tRRD","2","ACT","activate-to-activate (cross-bank)"],
        ["tfaw_ok_i","tFAW","6","ACT","<=4 ACTs per rolling window (cross-bank)"],
        ["(rd data)","CL + t_rddata_en","3 + 6","-","RD-to-rddata_valid latency (return path)"],
        ["(wr data)","CWL / t_phy_wrlat","2 / 0","-","WR-to-wrdata_en latency (drain path)"],
    ]:
        _km_row(ws, r, x); r += 1

    # --- Sheet 4: forward-state overlay (the real deadlock fix) ----------
    ws = wb.create_sheet("FORWARD_STATE")
    r = _km_title(ws,
        "forward-state classification -- delete !w_col_inflight_bank safely",
        "The arbiter picks against a 1-3 cyc STALE registered bank image "
        "(r_bank_row_active etc.). Instead of blocking a same-bank column while "
        "one is in the pipe, OVERLAY the in-flight op's pending effect so the "
        "next same-bank column is classified against POST-op state. Then same-"
        "bank columns pipeline at tCCD with no stale-image race.")
    cols = ["in-flight op to bank b", "registered image says", "forwarded (ideal) says",
            "2nd same-bank column decision", "note"]
    _km_hdr_row(ws, r, cols, widths=[22,20,22,24,34]); r += 1
    for x in [
        ["RD/WR (column, open row)","row_active=1 (stale ok)","row stays open",
         "issue next column @tCCD","the streaming case -- was blocked, now flows"],
        ["ACT (just opened)","row_active still 0","row_active=1, tRCD pending",
         "NOP until tRCD, then column","no false column on a not-yet-open row"],
        ["PRE / AP-close","row_active still 1","row closing -> 0",
         "do NOT issue column; re-ACT","kills the wrong/closed-row bad read"],
        ["refresh-drain PRE","row_active still 1","row closing -> 0",
         "hold column until re-ACT","same race source as PRE"],
    ]:
        _km_row(ws, r, x); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="Signals already present to build the overlay: r_bank (in-flight "
                  "bank), w_inflight_col, w_inflight_preact, w_col_inflight_guard, "
                  "r_ap_closing. Keep the per-ENTRY double-issue mask "
                  "Signals already present to build the overlay: r_bank (in-flight bank), "
                        "w_inflight_col, w_inflight_preact, w_col_inflight_guard, r_ap_closing. "
                        "Keep the per-ENTRY double-issue mask (w_rd/wr_col_inflight_ent). RTL "
                        "STATUS 2026-09-10: the per-BANK occupancy mask was NOT removed as this "
                        "line originally demanded -- it was AP-gated, which is the better answer. "
                        "It guards a real stale-image hazard (r_ap_closing bridges the window the "
                        "pipeline span alone cannot), so removing it outright would reopen that "
                        "hole. Non-AP columns now see no per-bank restriction.").font = KM_NOTE


# ---------------------------------------------------------------------------
# DATA-PATH workbook
# ---------------------------------------------------------------------------
def data_path_sheets(wb):

    # --- Sheet 1: write-data drain (dfi_wrdata presentation) -------------
    ws = wb.create_sheet("WR_DRAIN")
    r = _km_title(ws,
        "write-data drain: WR command -> dfi_wrdata -- IDEAL",
        "Cycle-relative to the WR/WRA column ISSUE. write_latency=0 "
        "(pre-pull, board tuple). One WR moves BL4 = 2 DFI words (DFI_RATE=2). "
        "Must sustain one WR every tCCD with NO drain bubble.")
    cols = ["cyc since WR", "dfi_wrdata_en", "dfi_wrdata (source)", "dfi_wrdata_mask",
            "wr_cam action", "note"]
    _km_hdr_row(ws, r, cols, widths=[13,15,26,18,20,34]); r += 1
    for x in [
        ["0 (WR issued)","1","wr_cam[slot] word0","strobe0","pop word0","concurrent w/ cmd (wrlat=0)"],
        ["1","1","wr_cam[slot] word1","strobe1","pop word1 -> free slot","BL4/RATE2 = 2 words"],
        ["2","1 (next WR)","wr_cam[slot2] word0","strobe0","next burst","tCCD=2 -> back-to-back, no gap"],
        ["...","1","...","...","stream","drain FIFO never empties while cmds flow"],
    ]:
        _km_row(ws, r, x); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="INVARIANT: dfi_wrdata_en high every cycle a WR is in flight; "
                  "wr_commit_ready_i (drain-FIFO room) must cover >= (tCCD * max "
                  "same-bank outstanding) so the arbiter never stalls the column "
                  "stream on drain-FIFO backpressure.").font = KM_NOTE

    # --- Sheet 2: B-response gating -------------------------------------
    ws = wb.create_sheet("WR_COMMIT_B")
    r = _km_title(ws, "write B-response gating (split/aggregate)",
               "One AXI AW may split into >1 DRAM WR (chopper). B returns ONCE, "
               "on the LAST sub-burst's commit. Must not assume in-order same-bank "
               "commit.")
    cols = ["sub-burst", "agg (more to come)", "last", "commit_done", "=> B_valid", "note"]
    _km_hdr_row(ws, r, cols, widths=[11,18,8,13,11,40]); r += 1
    for x in [
        ["0 of N","1","0","1","0","gate B: !(agg && !last)"],
        ["k of N","1","0","1","0","hold B until last"],
        ["N of N","0","1","1","1","emit single B for the whole AXI burst"],
        ["single","0","1","1","1","N=1 fast path"],
    ]:
        _km_row(ws, r, x, cmd_col=5); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="IDEAL: B-gate keyed on the CAM entry's own agg/last, NOT on a "
                  "IDEAL: B-gate keyed on the CAM entry's own agg/last, NOT on a per-bank "
                        "single-outstanding flag, so two same-bank writes in flight each retire "
                        "independently. RTL STATUS 2026-09-10: IMPLEMENTED. commit_done_valid_o is "
                        "strobed from the drain head's CARRIED agg/slast tag (w_cm_fire && "
                        "w_hd_blast && (!w_hd_agg || w_hd_slast)); no per-bank outstanding flag "
                        "exists in the write CAM at all. (pumice_wr_data_cam.sv:624-627)").font = KM_NOTE

    # --- Sheet 3: read-data return -------------------------------------
    ws = wb.create_sheet("RD_RETURN")
    r = _km_title(ws,
        "read-data return: RD command -> dfi_rddata -> AXI R -- IDEAL",
        "Cycle-relative to RD/RDA issue. t_rddata_en=6, CL adds to first "
        "rddata_valid. Aligner captures dfi_rddata on dfi_rddata_valid and "
        "returns in AR order. Must hold MANY same-bank reads outstanding.")
    cols = ["cyc since RD", "dfi_rddata_en", "dfi_rddata_valid (PHY)", "aligner",
            "s_axi_rvalid", "note"]
    _km_hdr_row(ws, r, cols, widths=[13,15,22,22,14,34]); r += 1
    for x in [
        ["0 (RD issued)","assert @ t_rddata_en","0","arm capture","0","enable window opens later"],
        ["t_rddata_en (6)","1","0->1","capture word0","0->1","first beat; fill latency (not a bubble)"],
        ["+1","1","1","capture word1, push R","1","BL4/RATE2 = 2 words -> 2 R beats"],
        ["+tCCD (next RD)","1","1","capture next burst","1","STREAM: rvalid stays high, back-to-back"],
        ["gap (no cmd)","0","0","idle","0","only when no RD was issued tCCD ago"],
    ]:
        _km_row(ws, r, x); r += 1

    # --- Sheet 4: same-bank outstanding tracker (the deadlock fix) ------
    ws = wb.create_sheet("SAME_BANK_OUTSTANDING")
    r = _km_title(ws,
        "per-bank outstanding-column tracker -- the DEADLOCK FIX",
        "RTL STATUS 2026-09-10: the one-column-per-bank restriction now applies "
              "ONLY to auto-precharge columns (the mask is AP-gated). Non-AP columns are "
              "gated by tCCD and the per-entry double-issue mask alone, which is what "
              "this row asked for. IDEAL for the AP case is still a small per-bank "
              "counter permitting up to RETURN_DEPTH columns rather than one.")
    cols = ["outstanding", "new_col_issued", "completion", "tCCD_ok", "can_issue",
            "outstanding_next", "note"]
    _km_hdr_row(ws, r, cols, widths=[12,15,12,9,10,16,40]); r += 1
    for x in [
        ["0","-","-","Y","YES","1 (on issue)","first column to an open row"],
        ["1..D-1","N","N","Y","YES","+1 (on issue)","pipeline more same-bank cols -> streaming"],
        ["1..D","N","Y","-","-","-1 (on completion)","completion (B / R-last) frees a slot"],
        ["D (full)","-","-","Y","NO","hold","only stall: return path at capacity, NOT pipeline"],
        ["any","N","N","N","NO","hold","tCCD not met -> legal DRAM spacing"],
    ]:
        _km_row(ws, r, x, cmd_col=5); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="RETURN_DEPTH (D) must be >= ceil((t_rddata_en + CL) / tCCD) so "
                  "the pipe stays full across the read round-trip: with "
                  "t_rddata_en=6, CL=3, tCCD=2 -> D >= 5. Reads: rd issue-order "
                  "FIFO + aligner MAX_OUTSTANDING must both be >= D. Writes: "
                  "wr drain FIFO + independent per-entry B-gating.").font = KM_NOTE

    # --- Sheet 5: tag-based recoverable returns (defense in depth) -------
    ws = wb.create_sheet("RETURN_TAGGING")
    r = _km_title(ws,
        "tag-based, recoverable read return -- fail-safe not fail-wedge",
        "RTL STATUS 2026-09-10: PARTLY ADDRESSED, hazard STANDS. "
              "pumice_rd_return_ring now allocates a ticket per read at admit (AR order) "
              "and drains from the ring head, which decoupled CAM occupancy from the "
              "return. But the RETURN itself is still POSITIONAL: a returning beat lands "
              "in the issue_q HEAD's slot because DRAM carries no tag back, and there is "
              "still no length check, so a short or lost burst still desyncs every later "
              "read. IDEAL unchanged: carry a read TAG end to end and length-check. "
              "(pumice_rd_return_ring.sv:122-134)")
    cols = ["mechanism today", "failure it causes", "ideal (tagged)", "recovers?"]
    _km_hdr_row(ws, r, cols, widths=[30,30,30,10]); r += 1
    for x in [
        ["return fill = issue-FIFO head (positional)","wrong data -> slot mismatch",
         "match return to slot by TAG/id","YES"],
        ["AR-drain gated on oldest r_ready","one stuck read wedges all younger",
         "drain any ready slot; watchdog the stuck one","YES"],
        ["aligner fixed BL_WORDS, no id","short burst desyncs all later reads",
         "per-read length watchdog + tag","YES"],
        ["dfi_rddata_valid no backpressure","beat into full FIFO is LOST",
         "size RD_FIFO >= D*BL_WORDS; assert never-full","N/A"],
    ]:
        _km_row(ws, r, x, cmd_col=4); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="Priority: the forward-state overlay (cmd kmap) removes the "
                  "CAUSE (no bad read is issued); tagging removes the "
                  "CONSEQUENCE (a bad/short return cannot permanently wedge). "
                  "Ship the overlay first; tagging is defense in depth.").font = KM_NOTE




WP_HDR = Font(bold=True, color="FFFFFF"); WP_HDR_FILL = PatternFill("solid", fgColor="374151")
WP_TITLE = Font(bold=True, size=13); WP_NOTE = Font(italic=True, color="6B7280")
WP_CEN = Alignment(horizontal="center", vertical="center")
WP_WRAP = Alignment(horizontal="left", vertical="top", wrap_text=True)
WP_THIN = Border(*[Side(style="thin", color="D1D5DB")] * 4)
WP_OK, WP_BAD = PatternFill("solid", fgColor="BBF7D0"), PatternFill("solid", fgColor="FCA5A5")


def _wp_hdr(ws, r, cols, w):
    for c, n in enumerate(cols, 1):
        x = ws.cell(row=r, column=c, value=n); x.font = WP_HDR; x.fill = WP_HDR_FILL
        x.alignment = WP_CEN; x.border = WP_THIN
    for c, wi in enumerate(w, 1):
        ws.column_dimensions[ws.cell(row=1, column=c).column_letter].width = wi


def _wp_row(ws, r, vals, flag=None):
    for c, v in enumerate(vals, 1):
        x = ws.cell(row=r, column=c, value=v)
        x.alignment = WP_CEN if len(str(v)) < 16 else WP_WRAP; x.border = WP_THIN
        if flag and c == flag[0]:
            x.fill = WP_OK if flag[1] else WP_BAD
            x.font = Font(bold=True)


def _wp_t(ws, t, s):
    ws.cell(row=1, column=1, value=t).font = WP_TITLE
    ws.cell(row=2, column=1, value=s).font = WP_NOTE
    return 4


def write_path_sheets(wb):

    # 1) drain handshake -----------------------------------------------------
    ws = wb.create_sheet("DRAIN_HANDSHAKE")
    r = _wp_t(ws, "write drain: arbiter commit -> drain FIFO -> DFI wr_fire -- IDEAL",
           "The arbiter marks a WR slot scheduled and enqueues it in u_drain_q "
           "(DEPTH=8); the drain read-engine streams cm_rd to the DFI at its own "
           "pace. commit_ready (=drain-FIFO room) gates the arbiter's WR issue. "
           "For same-bank WR streaming the drain MUST keep pace with commit.")
    _wp_hdr(ws, r, ["commit_valid\n(arb WR)", "drain FIFO\nroom (=commit_ready)",
                 "cm_rd_valid\n(drain->DFI)", "cm_rd_ready\n(DFI accepts)",
                 "=> action", "drain FIFO next", "note"],
         [12, 16, 14, 14, 16, 14, 34]); r += 1
    for x, ok in [
        (["1", "1", "-", "-", "ENQUEUE slot", "+1", "arbiter commits a WR"], True),
        (["-", "-", "1", "1", "DRAIN 1 slot -> wr_fire", "-1", "DFI takes it @tCCD"], True),
        (["1", "1", "1", "1", "enqueue + drain (net 0)", "steady", "STREAMING: paced by tCCD"], True),
        (["1", "0", "-", "0", "STALL: FIFO full, drain blocked", "8 (full)", "commit_ready low -> arbiter WR stalls => the wedge if drain never resumes"], False),
    ]:
        _wp_row(ws, r, x, flag=(5, ok)); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="WEDGE CONDITION: drain FIFO fills (8) AND cm_rd_ready stays 0 "
                  "-> commit_ready=0 -> arbiter stops issuing WR -> gen_wr_done "
                  "never asserts. So the fix question is: WHY does cm_rd_ready "
                  "(DFI accepting writes) stall under same-bank WR concurrency? "
                  "Candidates below.").font = WP_NOTE

    # 2) why cm_rd_ready stalls (the diagnostic) ----------------------------
    ws = wb.create_sheet("CM_RD_STALL_CANDIDATES")
    r = _wp_t(ws, "why the DFI stops accepting writes (cm_rd_ready=0) -- to MEASURE",
           "The drain streams cm_rd only while the DFI cmd path fires WR "
           "commands (wr_fire). Enumerate what can hold wr_fire off under "
           "same-bank WR concurrency; the waveform measurement confirms which.")
    _wp_hdr(ws, r, ["candidate", "mechanism (file)", "same-bank trigger", "confirm by"],
         [30, 34, 30, 26]); r += 1
    for x in [
        ["DFI cmd FIFO full", "shared u_cmd_fifo, in-order (mem_cmd_scheduler)",
         "WR cmds queue faster than DFI drains", "cmd-FIFO count in waves"],
        ["tCCD/bank gate at DFI", "dfi_cmd_path w_col_ok / col pacing",
         "same-bank WR spaced by tCCD -> drain paced", "dfi wr_fire spacing"],
        ["serializer owed vs wrdata desync", "dfi_wr_serializer positional r_owed",
         "wr_fire without matching wrdata (or vice versa)", "r_owed vs wd_valid"],
        ["wrdata CDC FIFO empty/full", "pumice_dfi_cdc wrdata FIFO",
         "wrdata not keeping pace with wr_fire", "cdc wrdata occupancy"],
        ["B-consolidation backpressure", "commit_done agg/slast gating",
         "a split burst's B never completes -> slot not evicted", "commit_done/agg/slast"],
    ]:
        _wp_row(ws, r, x); r += 1

    # 3) serializer owed/drive ----------------------------------------------
    ws = wb.create_sheet("SERIALIZER_OWED")
    r = _wp_t(ws, "dfi_wr_serializer: matured-burst owed accounting -- IDEAL",
           "r_owed += wr_fire (a WR cmd matured); w_drive=(owed!=0)&&wd_valid; "
           "drives 1 wrdata word/cycle; -1 on the burst's last word. POSITIONAL: "
           "the Nth wr_fire binds the Nth wrdata burst -- correct only while "
           "issue order == drain order (true today; NO tag to recover if not).")
    _wp_hdr(ws, r, ["r_owed", "wr_fire (mature)", "wd_valid", "=> w_drive",
                 "dfi_wrdata_en", "r_owed next", "note"],
         [10, 15, 10, 10, 14, 12, 34]); r += 1
    for x, ok in [
        (["0", "0", "-", "0", "0", "0", "idle -- no matured WR"], True),
        (["0", "1", "1", "1", "1", "0 or +", "matures + drives same cycle"], True),
        (["1", "0", "1", "1", "1", "-1 on last", "draining an owed burst"], True),
        (["1", "-", "0", "0", "0", "hold", "owed but wrdata not ready -> BUBBLE (wrdata CDC underrun)"], False),
        (["N", "1/cyc", "1", "1", "1", "steady", "STREAM: 1 wr_fire/tCCD, 1 word/cyc, no bubble"], True),
    ]:
        _wp_row(ws, r, x, flag=(4, ok)); r += 1

    # 4) B consolidation -----------------------------------------------------
    ws = wb.create_sheet("B_CONSOLIDATION")
    r = _wp_t(ws, "one B per host burst -- commit_done (agg/slast/blast)",
           "commit_done_valid = w_cm_fire && w_hd_blast && (!w_hd_agg || "
           "w_hd_slast): B strobes on the LAST beat of the LAST sub-burst. A "
           "split burst holds B until its final sub drains. Slot evicts on drain "
           "last -- so a never-draining sub never evicts, never frees the FIFO.")
    _wp_hdr(ws, r, ["w_cm_fire", "w_hd_blast\n(beat last)", "w_hd_agg\n(split)",
                 "w_hd_slast\n(sub last)", "=> B (commit_done)", "note"],
         [11, 12, 10, 12, 18, 36]); r += 1
    for x, ok in [
        (["1", "1", "0", "-", "1", "non-split burst -> B now"], True),
        (["1", "1", "1", "0", "0", "mid sub of a split -> hold B, evict slot"], True),
        (["1", "1", "1", "1", "1", "final sub -> single B for the host burst"], True),
        (["0", "-", "-", "-", "0", "no drain fire -> slot stuck -> FIFO fills => wedge"], False),
    ]:
        _wp_row(ws, r, x, flag=(5, ok)); r += 1


SC_GREEN = PatternFill("solid", fgColor="C6EFCE")
SC_GREY = PatternFill("solid", fgColor="F2F2F2")
SC_DC = PatternFill("solid", fgColor="FDE68A")   # unreachable -> don't-care
SC_TITLE = Font(bold=True, size=12)
SC_HDR = Font(bold=True)
SC_MONO = Font(name="Consolas", size=10)
SC_WRAP = Alignment(wrap_text=True, vertical="top")
SC_CENTER = Alignment(horizontal="center", vertical="center")
SC_THIN = Border(*[Side(style="thin")] * 4)

SC_GRAY2 = [(0, 0), (0, 1), (1, 1), (1, 0)]  # gray-code order of 2 bits


def _sc_glabel(bits):
    return "".join(str(b) for b in bits)


class ScKmapWriter:
    def __init__(self, ws):
        self.ws = ws
        self.row = 1

    def sheet_intro(self, title, lines):
        ws = self.ws
        ws.cell(self.row, 1, title).font = SC_TITLE
        self.row += 1
        for ln in lines:
            c = ws.cell(self.row, 1, ln)
            c.alignment = SC_WRAP
            self.row += 1
        self.row += 1

    def kmap(self, name, source, expr, varnames, fn, check, values=None,
             relations=None):
        """One K-map block. varnames: MSB-first list (2..6). fn(*bits)->0/1
        (or a short string when `values` mapping is wanted). Pages over
        varnames[4:].

        `relations` is the SUFFICIENCY half of the map: a list of
        (text, reachable_predicate, citation). A cell whose bits fail ANY
        predicate cannot occur in hardware, so it is emitted as an explicit
        don't-care X rather than as a 0 -- a 0 there would claim the logic
        was checked in a state it can never be in, and a later edit that
        makes the state reachable would not show up. Every relation carries
        the RTL that makes it true; an uncited relation is an assumption
        wearing a proof's clothes.
        """
        ws = self.ws
        ws.cell(self.row, 1, name).font = SC_TITLE
        ws.cell(self.row, 4, source).font = SC_MONO
        self.row += 1
        c = ws.cell(self.row, 1, expr)
        c.font = SC_MONO
        c.alignment = SC_WRAP
        self.row += 1
        n = len(varnames)
        rowv = varnames[0:min(2, n)]                  # grid row variables
        colv = varnames[min(2, n):min(4, n)]          # grid col variables
        pagev = varnames[4:]                          # page variables
        ws.cell(self.row, 1,
                f"rows = {'/'.join(rowv)}   cols = {'/'.join(colv)}"
                + (f"   pages = {'/'.join(pagev)}" if pagev else ""))
        self.row += 1

        # ---- relations: why whole regions of the grid are skipped ----------
        rels = relations or []
        if rels:
            c = ws.cell(self.row, 1,
                        "RELATIONS between axis signals (these make cells "
                        "UNREACHABLE -- shown as X, a don't-care, never as 0):")
            c.font = SC_HDR; c.alignment = SC_WRAP
            self.row += 1
            for text, _pred, cite in rels:
                c = ws.cell(self.row, 1, "    " + text)
                c.alignment = SC_WRAP
                ws.cell(self.row, 4, cite).font = SC_MONO
                self.row += 1
        else:
            c = ws.cell(self.row, 1,
                        "RELATIONS: none stated -- every combination is treated "
                        "as reachable. If two of these axes are in fact related, "
                        "the map is over-claiming (PUMICE-KMAP).")
            c.font = Font(italic=True, color="B45309"); c.alignment = SC_WRAP
            self.row += 1

        def _reachable(bits):
            return all(bool(pred(*bits)) for _t, pred, _c in rels)

        ws.cell(self.row, 1, f"CHECK BY INSPECTION: {check}").alignment = SC_WRAP
        ws.cell(self.row, 1).font = Font(italic=True)
        self.row += 2

        rows = SC_GRAY2 if len(rowv) == 2 else ([(0,), (1,)] if len(rowv) == 1
                                             else [()])
        cols = SC_GRAY2 if len(colv) == 2 else ([(0,), (1,)] if len(colv) == 1
                                             else [()])
        pages = [()]
        for _ in pagev:
            pages = [p + (b,) for p in pages for b in (0, 1)]

        n_dc = 0
        n_tot = len(rows) * len(cols) * len(pages)
        for page in pages:
            base = self.row
            if pagev:
                lbl = ", ".join(f"{v}={b}" for v, b in zip(pagev, page))
                ws.cell(base, 1, f"[{lbl}]").font = SC_HDR
                base += 1
            # column headers
            for j, cb in enumerate(cols):
                cc = ws.cell(base, 2 + j, _sc_glabel(cb) or "-")
                cc.font = SC_HDR
                cc.alignment = SC_CENTER
            for i, rb in enumerate(rows):
                rc = ws.cell(base + 1 + i, 1, _sc_glabel(rb) or "-")
                rc.font = SC_HDR
                rc.alignment = SC_CENTER
                for j, cb in enumerate(cols):
                    bits = tuple(rb) + tuple(cb) + tuple(page)
                    cell = ws.cell(base + 1 + i, 2 + j)
                    if not _reachable(bits):
                        cell.value = "X"
                        cell.fill = SC_DC
                        cell.font = Font(italic=True)
                        n_dc += 1
                    else:
                        v = fn(*bits)
                        if values:                    # multi-valued map
                            cell.value = values.get(v, str(v))
                            benign = str(v) in ("0", "-", "wait", "hold", "IDLE")
                            cell.fill = SC_GREY if benign else SC_GREEN
                        else:
                            cell.value = int(bool(v))
                            cell.fill = SC_GREEN if v else SC_GREY
                    cell.alignment = SC_CENTER
                    cell.border = SC_THIN
            self.row = base + 1 + len(rows) + 1
        if rels:
            c = ws.cell(self.row, 1,
                        f"cells: {n_tot - n_dc} reachable, {n_dc} don't-care "
                        f"(X) of {n_tot}. Read the CHECK over the reachable "
                        f"cells only.")
            c.font = Font(italic=True); c.alignment = SC_WRAP
            self.row += 1
        self.row += 1

    def table(self, name, source, headers, rows, note=""):
        ws = self.ws
        ws.cell(self.row, 1, name).font = SC_TITLE
        ws.cell(self.row, 4, source).font = SC_MONO
        self.row += 1
        if note:
            c = ws.cell(self.row, 1, note)
            c.alignment = SC_WRAP
            c.font = Font(italic=True)
            self.row += 1
        for j, h in enumerate(headers):
            c = ws.cell(self.row, 1 + j, h)
            c.font = SC_HDR
            c.border = SC_THIN
        self.row += 1
        for r in rows:
            for j, v in enumerate(r):
                c = ws.cell(self.row, 1 + j, v)
                c.border = SC_THIN
                c.alignment = SC_WRAP
            self.row += 1
        self.row += 2


def build_arbiter_sheet(wb):
    if "K-maps arbiter" in wb.sheetnames:
        del wb["K-maps arbiter"]
    ws = wb.create_sheet("K-maps arbiter")
    for col, w in zip("ABCDEFGH", (26, 9, 9, 9, 9, 9, 9, 9)):
        ws.column_dimensions[col].width = w
    km = ScKmapWriter(ws)
    km.sheet_intro(
        "pumice_cmd_arbiter — decision K-maps (rtl/fub/pumice_cmd_arbiter.sv)",
        ["Each grid is computed from a python mirror of the exact RTL "
         "expression. Variables are the 1-bit conditions feeding the decision "
         "(counter==0 flags etc.). Gray order 00 01 11 10; >4 vars page into "
         "multiple grids.",
         "Healthy shapes are stated per map — a regression that opens an "
         "illegal cell is visible by inspection."])

    # 1. w_ref_safe (guards collapsed to one flag: guard0|guard1 nonzero)
    km.kmap(
        "w_ref_safe", "pumice_cmd_arbiter.sv (refresh pick gate)",
        "w_ref_safe = !w_any_active && !w_inflight_preact && (r_guard0=='0) && "
        "(r_guard1=='0) && !w_rfc_busy   [guards collapsed: guards_nz = "
        "|r_guard0 | |r_guard1]",
        ["any_active", "inflight_preact", "guards_nz", "rfc_busy"],
        lambda a, i, g, r: (not a) and (not i) and (not g) and (not r),
        "EXACTLY ONE 1-cell, at all-zeros. Any additional 1 is a hole that "
        "lets REFab collide with an open/opening row or violate tRFC "
        "(the silicon row-corruption bug class).")

    # 2. refresh branch action (multi-valued)
    km.kmap(
        "refresh-branch action (given refresh_req_i||refresh_drain_i)",
        "pumice_cmd_arbiter.sv (priority 2)",
        "if (any_active) { if (rfsh_pre_found) PRE else wait } "
        "else if (ref_safe) REF else wait",
        ["any_active", "rfsh_pre_found", "ref_safe"],
        lambda a, f, s: ("PRE" if (a and f) else
                         ("REF" if ((not a) and s) else "wait")),
        "REF appears ONLY where any_active=0 AND ref_safe=1. PRE only where "
        "any_active=1 AND pre_found=1. Everything else waits (the branch "
        "never falls through to column/ACT picks).",
        values={})

    # 3. column masks (6 vars -> 4 pages)
    km.kmap(
        "rd_col_m[e]  (given rd_sch_valid_i[e] && rd_issue_ready)",
        "pumice_cmd_arbiter.sv (classify + direction guard)",
        "rd_col_m = rhit && bank_rdwr_ready && tccd_ok && twtr_ok && "
        "rd_issue_ready && !w_inflight_col && !w_rd_turn_block   "
        "[rd_issue_ready factored out as the enabling condition]",
        ["rhit", "rdwr_ready", "tccd_ok", "twtr_ok",
         "inflight_col", "rd_turn_block"],
        lambda h, r, c, w, f, t: h and r and c and w and (not f) and (not t),
        "1s ONLY on the page [inflight_col=0, rd_turn_block=0], single "
        "all-ones cell. ANY 1 on an rd_turn_block=1 page = a RD issued into "
        "a write burst's DQ occupancy on the stale flopped twtr_ok — the "
        "471/471 concurrent-soak corruption (issue #42).")
    km.kmap(
        "wr_col_m[e]  (given wr_sch_valid_i[e] && wr_commit_ready)",
        "pumice_cmd_arbiter.sv (classify + direction guard)",
        "wr_col_m = whit && bank_rdwr_ready && tccd_ok && trtw_ok && "
        "wr_commit_ready && !w_inflight_col && !w_wr_turn_block   "
        "[wr_commit_ready factored out as the enabling condition]",
        ["whit", "rdwr_ready", "tccd_ok", "trtw_ok",
         "inflight_col", "wr_turn_block"],
        lambda h, r, c, t, f, b: h and r and c and t and (not f) and (not b),
        "Mirror of rd_col_m: 1s only on [inflight_col=0, wr_turn_block=0].")
    km.kmap(
        "w_rd_turn_block / w_wr_turn_block",
        "pumice_cmd_arbiter.sv (direction-turnaround guard)",
        "w_rd_turn_block = r_wrfire0 || r_wrfire1 ; "
        "w_wr_turn_block = r_rdfire0 || r_rdfire1   (fire-shift of the "
        "OPPOSITE direction; covers the 2 cycles until the flopped "
        "twtr/trtw ok reflects the fired column)",
        ["oppfire0", "oppfire1"],
        lambda f0, f1: f0 or f1,
        "Zero ONLY at (0,0). The guard is direction-CROSSED: a fired WR "
        "blocks RD picks and vice versa; same-direction pacing stays with "
        "tCCD. If either 1-cell reads 0, the turnaround hole is back.")

    # 4. activate masks (6 vars)
    km.kmap(
        "rd_act_m[e] / wr_act_m[e]  (given sch_valid[e])",
        "pumice_cmd_arbiter.sv (classify + tRFC gate)",
        "act_m = !bank_row_active && !w_guarded[bank] && bank_act_ready && "
        "tfaw_ok && trrd_ok && !w_rfc_busy",
        ["row_active", "guarded", "act_ready", "tfaw_ok",
         "trrd_ok", "rfc_busy"],
        lambda ra, g, ar, tf, tr, rb:
            (not ra) and (not g) and ar and tf and tr and (not rb),
        "1s ONLY on the page [trrd_ok=1, rfc_busy=0], single cell "
        "(row_active=0, guarded=0, act_ready=1, tfaw_ok=1). ANY 1 on an "
        "rfc_busy=1 page = ACT during refresh recovery — the silicon "
        "row-corruption bug the tRFC counter closes.")

    # 5. precharge masks (4 vars, clean single grid)
    km.kmap(
        "rd_pre_m[e] / wr_pre_m[e]  (given sch_valid[e])",
        "pumice_cmd_arbiter.sv (classify)",
        "pre_m = bank_row_active && !w_guarded[bank] && !hit && "
        "bank_pre_ready",
        ["row_active", "guarded", "hit", "pre_ready"],
        lambda ra, g, h, p: ra and (not g) and (not h) and p,
        "Single 1-cell at (1,0,0,1): only an open bank on the WRONG row, "
        "un-guarded and tRAS/tRTP/tWR-clear, may precharge. A 1 with "
        "guarded=1 = the registered-readiness staleness hazard.",
        relations=[
            ("hit => row_active. A row HIT is defined as 'this bank has a row "
             "open AND it is the requested one', so a hit with no open row is "
             "not a state the hardware can be in -- it is a contradiction in "
             "the term itself, not a case the logic happens to avoid.",
             lambda ra, g, h, p: (not h) or ra,
             "pumice_cmd_arbiter.sv:562-565 (rhit/whit = r_bank_row_active[b] && row==open_row)"),
            ("pre_ready => row_active. safe_pre_o is ANDed with r_row_valid, "
             "so tRAS/tRTP/tWR clearance is only ever reported for a bank that "
             "has a row to precharge.",
             lambda ra, g, h, p: (not p) or ra,
             "bank_timer.sv:138 (safe_pre_o = r_row_valid && (r_ras=='0) && (r_preblk=='0) && !r_ap_pending)"),
        ])

    # 6. per-bank guard
    km.kmap(
        "w_guarded[b]",
        "pumice_cmd_arbiter.sv (guard fold)",
        "w_guarded[b] = r_guard0[b] | r_guard1[b] | ((w_inflight_preact || "
        "w_inflight_col) && (r_bank == b))   [bank_match = r_bank==b]",
        ["guard0", "guard1", "inflight_rowop_or_col", "bank_match"],
        lambda g0, g1, i, m: g0 or g1 or (i and m),
        "Zero ONLY when both guard stages are clear AND no in-flight "
        "row-affecting/column op targets this bank. Columns are included "
        "(tRTP/tWR registration lag) — if the (0,0,1,1) cell ever reads 0, "
        "the column-guard extension was lost.")

    # 7. output stage
    km.kmap(
        "w_out_ready / w_fire_out",
        "pumice_cmd_arbiter.sv (output register)",
        "w_out_ready = !r_pick_valid || cmd_ready_i ; "
        "w_fire_out = r_pick_valid && cmd_ready_i",
        ["pick_valid", "cmd_ready"],
        lambda p, c: ("rdy+fire" if (p and c) else
                      ("rdy" if not p else "hold")),
        "hold ONLY at (1,0) — a full cmd FIFO holds the decision; "
        "fire ONLY at (1,1). Guards/commits/grants strobe on fire alone.",
        values={})

    # 8. priority order table
    km.table(
        "pick priority (strict, first match wins)",
        "pumice_cmd_arbiter.sv (always_comb pick)",
        ["#", "condition", "action", "note"],
        [(1, "!init_done_i && init_cmd_valid_i", "forward init op",
          "MRS/PRE/REF from init_sequencer verbatim"),
         (2, "refresh_req_i || refresh_drain_i", "refresh branch",
          "see refresh-branch K-map; never falls through while pending"),
         (3, "rd_col_f", "RD/RDA row-hit", "read priority over write"),
         (4, "wr_col_f", "WR/WRA row-hit", ""),
         (5, "rd_act_f", "ACT for oldest pending read", "bank-parallel"),
         (6, "wr_act_f", "ACT for oldest pending write", ""),
         (7, "rd_pre_f", "PRE wrong-row bank (read)", ""),
         (8, "wr_pre_f", "PRE wrong-row bank (write)", "")],
        note="Strict if/else cascade — exactly one action per cycle; refresh "
             "starves columns by design while req is high (liveness relies "
             "on tREFI >> refresh service time).")

    # 9. tRFC counter rule
    km.table(
        "r_rfc_cnt next-value", "pumice_cmd_arbiter.sv (tRFC counter)",
        ["w_fire_out && r_grant (REF fired)", "r_rfc_cnt != 0", "next"],
        [("1", "x", "t_rfc_i (load)"),
         ("0", "1", "r_rfc_cnt - 1"),
         ("0", "0", "0 (idle)")],
        note="w_rfc_busy = (r_rfc_cnt != 0). Load wins over decrement; "
             "blocks ACT picks and further REFs (drain REFs are tRFC-spaced).")
    return ws


def build_bank_timer_sheet(wb):
    if "K-maps bank timer" in wb.sheetnames:
        del wb["K-maps bank timer"]
    ws = wb.create_sheet("K-maps bank timer")
    for col, w in zip("ABCDEFGH", (26, 9, 9, 9, 9, 9, 9, 9)):
        ws.column_dimensions[col].width = w
    km = ScKmapWriter(ws)
    km.sheet_intro(
        "bank_timer — safe-signal K-maps (rtl/fub/bank_timer.sv)",
        ["Flags: rv=r_row_valid, ap=r_ap_pending, X0=(timer X == 0). "
         "safe_* are pure combinational ANDs over these — one register stage "
         "(the counters) behind, which is why the arbiter carries the 2-cycle "
         "guard."])

    km.kmap(
        "safe_act_o", "bank_timer.sv:133",
        "safe_act = !r_row_valid && (r_rp == 0) && (r_rc == 0)",
        ["row_valid", "rp==0", "rc==0"],
        lambda rv, rp0, rc0: (not rv) and rp0 and rc0,
        "Single 1-cell at (0,1,1): closed row, tRP and tRC elapsed. Any 1 "
        "with row_valid=1 would re-ACT an open bank.")
    km.kmap(
        "safe_rd_o / safe_wr_o", "bank_timer.sv:135-136",
        "safe_rd = safe_wr = r_row_valid && (r_rcd == 0) && !r_ap_pending",
        ["row_valid", "rcd==0", "ap_pending"],
        lambda rv, rcd0, ap: rv and rcd0 and (not ap),
        "Single 1-cell at (1,1,0). ap_pending=1 must kill columns — the row "
        "is committed to auto-close.")
    km.kmap(
        "safe_pre_o", "bank_timer.sv:138",
        "safe_pre = r_row_valid && (r_ras == 0) && (r_preblk == 0) && "
        "!r_ap_pending",
        ["row_valid", "ras==0", "preblk==0", "ap_pending"],
        lambda rv, ras0, pb0, ap: rv and ras0 and pb0 and (not ap),
        "Single 1-cell at (1,1,1,0): tRAS AND tRTP/tWR both elapsed, no "
        "auto-PRE in flight. preblk covers the read-to-PRE / write-recovery "
        "window the arbiter cannot see per-command.")
    km.kmap(
        "w_ap_fire (internal auto-precharge)", "bank_timer.sv:88",
        "w_ap_fire = r_ap_pending && (r_preblk == 0) && (r_ras == 0)",
        ["ap_pending", "preblk==0", "ras==0"],
        lambda ap, pb0, ras0: ap and pb0 and ras0,
        "Single 1-cell at (1,1,1). Fires exactly once: it clears ap_pending "
        "and row_valid and loads tRP the same edge.")
    km.kmap(
        "state_o (observability only)", "bank_timer.sv:144-147",
        "rv ? (rcd_nz ? ACTIVATING : ACTIVE) : (rp_nz ? PRECHARGING : IDLE)",
        ["row_valid", "rcd_nz", "rp_nz"],
        lambda rv, rcd, rp: ("ACTIVATING" if (rv and rcd) else
                             "ACTIVE" if rv else
                             "PRECHG" if rp else "IDLE"),
        "Pure decode of the flags; no downstream logic may depend on it.",
        values={},
        relations=[
            ("rcd_nz => row_valid. The ACT edge loads tRCD and sets row_valid "
             "together, and nothing else loads tRCD, so a bank counting tRCD "
             "always has its row marked open.",
             lambda rv, rcd, rp: (not rcd) or rv,
             "bank_timer.sv:96 (set_act_i -> r_rcd) + :116 (r_row_valid <= 1)"),
            ("rp_nz => !row_valid. The PRE edge (explicit or auto) loads tRP "
             "and clears row_valid together.",
             lambda rv, rcd, rp: (not rp) or (not rv),
             "bank_timer.sv:106 (set_pre_i||w_ap_fire -> r_rp) + :120-123 (r_row_valid <= 0)"),
            ("Therefore rcd_nz and rp_nz are MUTUALLY EXCLUSIVE -- a bank "
             "cannot be inside tRCD and tRP at once. That single relation "
             "removes a quarter of this grid; drawing 0s there would assert "
             "the decode had been checked in a state the timers forbid.",
             lambda rv, rcd, rp: not (rcd and rp),
             "bank_timer.sv:96,106,116,120-123"),
        ])
    km.table(
        "row_valid / ap_pending next-state priority", "bank_timer.sv:115-127",
        ["set_act", "set_pre", "w_ap_fire", "set_rd||set_wr",
         "row_valid'", "ap_pending'"],
        [("1", "x", "x", "x", "1 (row=row_i)", "0"),
         ("0", "1", "x", "x", "0", "0"),
         ("0", "0", "1", "x", "0", "0"),
         ("0", "0", "0", "1", "unchanged", "set_ap_i"),
         ("0", "0", "0", "0", "unchanged", "unchanged")],
        note="Strict priority ACT > PRE > auto-PRE > column. The arbiter "
             "never issues ACT and PRE to one bank in one cycle "
             "(single-issue), so rows 1-2 cannot conflict in practice.")
    return ws


def build_refresh_sheet(wb):
    if "K-maps refresh+top" in wb.sheetnames:
        del wb["K-maps refresh+top"]
    ws = wb.create_sheet("K-maps refresh+top")
    for col, w in zip("ABCDEFGH", (26, 9, 9, 9, 9, 9, 9, 9)):
        ws.column_dimensions[col].width = w
    km = ScKmapWriter(ws)
    km.sheet_intro(
        "refresh_ctrl + scheduler top — K-maps (rtl/fub/refresh_ctrl.sv, "
        "rtl/macro/pumice_mem_cmd_scheduler.sv)",
        ["Flags: pend_nz=(r_pending>0), rem_nz=(r_burst_remaining>0), "
         "expired=(r_refi_cnt==0)."])

    km.kmap(
        "w_grant_accept", "refresh_ctrl.sv:79",
        "w_grant_accept = refresh_grant_i && (r_pending > 0)",
        ["grant", "pend_nz"],
        lambda g, p: g and p,
        "Single 1-cell at (1,1): a grant with nothing pending is swallowed "
        "(the accumulator never goes negative).")
    km.kmap(
        "refresh_drain_active", "refresh_ctrl.sv:126",
        "w_drain_active = (r_burst_remaining > 0) && (r_pending > 0)",
        ["rem_nz", "pend_nz"],
        lambda r, p: r and p,
        "Single 1-cell at (1,1); holding the arbiter in the refresh branch "
        "requires BOTH quota and owed refreshes.")
    km.table(
        "r_pending next-value", "refresh_ctrl.sv:98-108",
        ["enable && expired", "w_grant_accept", "next"],
        [("1", "0", "min(pending+1, 8)  (postpone cap)"),
         ("0", "1", "pending-1"),
         ("1", "1", "pending (net zero)"),
         ("0", "0", "pending")],
        note="refresh_req_o (registered) = pending>0. Saturation at 8 = a "
             "JEDEC retention violation looming — the arbiter must be "
             "serving REFs.")
    km.kmap(
        "busy_o", "pumice_mem_cmd_scheduler.sv",
        "busy = !init_done || refresh_req || w_cmd_rd_valid || "
        "(|w_bank_row_active[0])",
        ["init_done", "refresh_req", "cmd_rd_valid", "any_row_active"],
        lambda i, r, v, a: (not i) or r or v or a,
        "Zero ONLY at (1,0,0,0): init complete, no refresh owed, cmd FIFO "
        "empty, all rows closed. 15 of 16 cells are 1 — busy is the "
        "OR-reduce of everything in flight.")
    return ws




def main():
    wb = Workbook()
    wb.remove(wb.active)
    build_index(wb)
    build_contract_sheets(wb)
    build_read_path_sheet(wb)
    cmd_path_sheets(wb)
    data_path_sheets(wb)
    write_path_sheets(wb)
    build_arbiter_sheet(wb)
    build_bank_timer_sheet(wb)
    build_refresh_sheet(wb)
    wb.save(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print("  ", name)


if __name__ == "__main__":
    main()
