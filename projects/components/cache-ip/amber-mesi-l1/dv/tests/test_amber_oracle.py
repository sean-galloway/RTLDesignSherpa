"""
amber_fsm_oracle test runner

Two halves, one file:

1. Pure-pytest, table-driven: every reachable cell of the gem5-derived FSM
   oracle's transition table is asserted here, row by row, against
   hand-cited gem5 Ruby transitions. Each row's ``cite`` names the gem5 file
   and the transition line in ``projects/components/cache-ip/References/
   gem5-ruby-protocols/MESI_Two_Level-L1cache.sm`` (line numbers as of the
   2026-10 checkout; the mapping/collapse rationale per group lives in
   ``dv/golden/gem5_mapping_notes.md``). Reserved/illegal encodings and
   unreachable cells must raise ``AmberOracleError``.

2. cocotb, pkg-pin: drives the landed ``amber_snoop_kmap`` leaf (the module
   wrapper over the ``amber_pkg`` Table 3.0 decode functions, compiled via
   ``amber_snoop_kmap.f`` -> ``amber_pkg.f``) and scores the SystemVerilog
   decode against the ORACLE itself, so oracle CRRESP / next-state ==
   amber_pkg.amber_snoop_crresp / amber_snoop_next_state is pinned from day
   one. The TB class follows the amber_snoop_kmap unit suite conventions.

Oracle states: the four stable MESI states I/S/E/M plus the six gem5 TBE
transients IS/IM/SM/IS_I/M_I/SINK_WB_ACK (DECISION D-11: they collapse onto
amber's blocking CTRL transient states; PF_* prefetch and LLSC_* states are
out of scope). Oracle events: cpu rd/wr, the six IHI0022 snoops, fill done,
drain done.

Author: RTL Design Sherpa
Created: 2026-10-07
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    AmberOracleError,
    STATES,
    EVENTS,
    step,
)
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_oracle_tb import AmberOracleTB

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'

# ---------------------------------------------------------------------------
# CRRESP wire-order constants ({WU[4],IS[3],PD[2],Err[1],DT[0]}), the same
# packing the amber_pkg functions return. HAS Table 3.0 rows.
# ---------------------------------------------------------------------------
CR_NONE = 0b00000
CR_M_RS = 0b01101   # DT+PD+IS: dirty out, downgrade, shared
CR_M_RO = 0b00101   # DT+PD:    dirty out, invalidate (ReadOnce/ReadUnique)
CR_E_RS = 0b11001   # DT+IS+WU: clean out, downgrade, was unique
CR_E_RU = 0b10001   # DT+WU:    clean out, invalidate
CR_E_CS = 0b11000   # IS+WU:    no transfer, stays Exclusive per Table 3.0
CR_S_RS = 0b01000   # IS:       no transfer, shared

MISS_REQ_READ_SHARED  = 'READ_SHARED'   # cpu read miss   (gem5 GETS)
MISS_REQ_READ_UNIQUE  = 'READ_UNIQUE'   # cpu write miss  (gem5 GETX)
MISS_REQ_CLEAN_UNIQUE = 'CLEAN_UNIQUE'  # S-line upgrade  (gem5 UPGRADE)

SM = 'MESI_Two_Level-L1cache.sm'


def _build_table():
    """Every reachable oracle cell, one row per (state, event[, qualifier]).

    Row fields: state, event, fill (pending-transaction install state), the
    expected step() result (next_state / result / req / pending), the
    pkg-decode reference state + expected CRRESP for snoop rows, and the
    gem5 citation. ``in_pending`` seeds the post-commit effect register for
    rows that only make sense on the second half of a two-step sequence.
    """
    rows = []

    def add(state, event, fill=None, in_pending=None, exp_next=None,
            exp_result=None, exp_req=None, ref=None, exp_crresp=None,
            exp_pending=None, cite=''):
        rows.append({
            'state': state, 'event': event, 'fill': fill,
            'in_pending': in_pending, 'exp_next': exp_next,
            'exp_result': exp_result, 'exp_req': exp_req, 'ref': ref,
            'exp_crresp': exp_crresp, 'exp_pending': exp_pending,
            'cite': cite,
        })

    # =====================================================================
    # Invalid -- the only stable state with a cpu-miss edge out.
    # gem5: transition({NP,I}, Load, IS)  .sm:1106 (a_issueGETS .sm:586)
    # gem5: transition({NP,I}, Store, IM) .sm:1174 (b_issueGETX .sm:657)
    # gem5: transition({NP,I}, Inv)       .sm:1216 (fi_sendInvAck .sm:810)
    # No Fwd_GETS/GETX transition leaves I (.sm:470-493: the L2 only
    # forwards to tracked sharers), so in amber's broadcast domain the
    # invalid line answers the safe no-transfer decode per HAS Table 3.0.
    # =====================================================================
    add('I', 'CPU_RD', exp_next='IS', exp_result='MISS',
        exp_req=MISS_REQ_READ_SHARED, cite=f'{SM}:1106 Load->IS')
    add('I', 'CPU_WR', exp_next='IM', exp_result='MISS',
        exp_req=MISS_REQ_READ_UNIQUE, cite=f'{SM}:1174 Store->IM')
    for sn in ('SNOOP_READ_SHARED', 'SNOOP_READ_ONCE', 'SNOOP_READ_UNIQUE',
               'SNOOP_CLEAN_SHARED'):
        add('I', sn, exp_next='I', exp_result='RESPOND', ref='I',
            exp_crresp=CR_NONE,
            cite=f'{SM}:470-493 no Fwd_* from I; {SM}:1216 (Inv); HAS T3.0 I row')
    for sn in ('SNOOP_CLEAN_INVALID', 'SNOOP_MAKE_INVALID'):
        add('I', sn, exp_next='I', exp_result='RESPOND', ref='I',
            exp_crresp=CR_NONE, cite=f'{SM}:1216 ({{NP,I}}, Inv)')

    # =====================================================================
    # Shared
    # gem5: transition({S,E,M}, Load)     .sm:1222 (h_load_hit .sm:873)
    # gem5: transition(S, Store, SM)      .sm:1244 (c_issueUPGRADE .sm:695)
    # gem5: transition(S, Inv, I)         .sm:1256 (fi_sendInvAck)
    # No S x Fwd_GETS/GETX transition exists: the directory serves peer GETS
    # itself and invalidates sharers with Inv, so Fwd_GETX ~ amber
    # READ_UNIQUE maps onto the sharer-invalidate transition.
    # =====================================================================
    add('S', 'CPU_RD', exp_next='S', exp_result='HIT', cite=f'{SM}:1222 Load hit')
    add('S', 'CPU_WR', exp_next='SM', exp_result='MISS',
        exp_req=MISS_REQ_CLEAN_UNIQUE, cite=f'{SM}:1244 Store->SM (UPGRADE)')
    add('S', 'SNOOP_READ_SHARED', exp_next='S', exp_result='RESPOND', ref='S',
        exp_crresp=CR_S_RS,
        cite=f'{SM}:1256 family; no S x Fwd_GETS in .sm; HAS T3.0 S row')
    add('S', 'SNOOP_READ_ONCE', exp_next='S', exp_result='RESPOND', ref='S',
        exp_crresp=CR_S_RS,
        cite=f'{SM}:1256 family; no S x Fwd_GETS in .sm; HAS T3.0 S row')
    add('S', 'SNOOP_READ_UNIQUE', exp_next='I', exp_result='RESPOND', ref='S',
        exp_crresp=CR_NONE, cite=f'{SM}:1256 (S, Inv, I) sharer invalidate')
    add('S', 'SNOOP_CLEAN_SHARED', exp_next='S', exp_result='RESPOND', ref='S',
        exp_crresp=CR_NONE,
        cite=f'{SM}: none (no clean probe in dir. protocol); HAS T3.0 S row')
    add('S', 'SNOOP_CLEAN_INVALID', exp_next='I', exp_result='RESPOND', ref='S',
        exp_crresp=CR_NONE, cite=f'{SM}:1256 (S, Inv, I)')
    add('S', 'SNOOP_MAKE_INVALID', exp_next='I', exp_result='RESPOND', ref='S',
        exp_crresp=CR_NONE, cite=f'{SM}:1256 (S, Inv, I)')

    # =====================================================================
    # Exclusive
    # gem5: transition(E, Store, M)                 .sm:1264 (hh_store_hit)
    # gem5: transition(E, Fwd_GETX, I)              .sm:1286 (d_sendDataToRequestor)
    # gem5: transition(E, {Fwd_GETS,INSTR}, S)      .sm:1292 (d + d2_sendDataToL2)
    # gem5: transition(E, Inv, I)  "don't send data" .sm:1279
    # =====================================================================
    add('E', 'CPU_RD', exp_next='E', exp_result='HIT', cite=f'{SM}:1222 Load hit')
    add('E', 'CPU_WR', exp_next='M', exp_result='HIT', cite=f'{SM}:1264 Store hit -> M')
    add('E', 'SNOOP_READ_SHARED', exp_next='S', exp_result='RESPOND', ref='E',
        exp_crresp=CR_E_RS, cite=f'{SM}:1292 (E, {{Fwd_GETS,INSTR}}, S)')
    add('E', 'SNOOP_READ_ONCE', exp_next='S', exp_result='RESPOND', ref='E',
        exp_crresp=CR_E_RS, cite=f'{SM}:1292 (Fwd_GET_INSTR analog)')
    add('E', 'SNOOP_READ_UNIQUE', exp_next='I', exp_result='RESPOND', ref='E',
        exp_crresp=CR_E_RU, cite=f'{SM}:1286 (E, Fwd_GETX, I)')
    add('E', 'SNOOP_CLEAN_SHARED', exp_next='E', exp_result='RESPOND', ref='E',
        exp_crresp=CR_E_CS,
        cite=f'{SM}: none (no clean probe); HAS T3.0 E row (stays E, IS+WU)')
    add('E', 'SNOOP_CLEAN_INVALID', exp_next='I', exp_result='RESPOND', ref='E',
        exp_crresp=CR_NONE, cite=f'{SM}:1279 (E, Inv, I) no data')
    add('E', 'SNOOP_MAKE_INVALID', exp_next='I', exp_result='RESPOND', ref='E',
        exp_crresp=CR_NONE, cite=f'{SM}:1279 (E, Inv, I) no data')

    # =====================================================================
    # Modified
    # gem5: transition(M, Store, M)            .sm:1264
    # gem5: transition(M, Fwd_GETX, I)         .sm:1332 (d_sendDataToRequestor)
    # gem5: transition(M, {Fwd_GETS,INSTR}, S) .sm:1338 (d + d2)
    # gem5: transition(M, Inv, I)              .sm:1321 (f_sendDataToL2)
    # Divergences pinned by HAS Table 3.0 (the binding snoop-decode
    # authority): ReadOnce invalidates where gem5 keeps the GET_INSTR
    # sharer (M -> S at .sm:1338); CleanShared/ MakeInvalid have no gem5
    # Inv counterpart (gem5 has one Inv flavor that writes dirty data back).
    # =====================================================================
    add('M', 'CPU_RD', exp_next='M', exp_result='HIT', cite=f'{SM}:1222 Load hit')
    add('M', 'CPU_WR', exp_next='M', exp_result='HIT', cite=f'{SM}:1264 Store hit')
    add('M', 'SNOOP_READ_SHARED', exp_next='S', exp_result='RESPOND', ref='M',
        exp_crresp=CR_M_RS, cite=f'{SM}:1338 (M, {{Fwd_GETS,INSTR}}, S)')
    add('M', 'SNOOP_READ_ONCE', exp_next='I', exp_result='RESPOND', ref='M',
        exp_crresp=CR_M_RO,
        cite=f'{SM}:1338 analog; HAS T3.0 M row (ReadOnce -> Invalid; DIVERGES from gem5 S)')
    add('M', 'SNOOP_READ_UNIQUE', exp_next='I', exp_result='RESPOND', ref='M',
        exp_crresp=CR_M_RO, cite=f'{SM}:1332 (M, Fwd_GETX, I)')
    add('M', 'SNOOP_CLEAN_SHARED', exp_next='S', exp_result='RESPOND', ref='M',
        exp_crresp=CR_M_RS,
        cite=f'{SM}: none; analog .sm:1338; HAS T3.0 M row (downgrade S, dirty out)')
    add('M', 'SNOOP_CLEAN_INVALID', exp_next='I', exp_result='RESPOND', ref='M',
        exp_crresp=CR_M_RS,
        cite=f'{SM}:1321 (M, Inv, I) f_sendDataToL2; pkg adds IS per family matrix')
    add('M', 'SNOOP_MAKE_INVALID', exp_next='I', exp_result='RESPOND', ref='M',
        exp_crresp=CR_NONE,
        cite=f'{SM}:1321 analog; HAS T3.0 M row (IHI0022 forbids DT; DIVERGES from gem5 writeback)')

    # =====================================================================
    # IS -- read-miss fill in flight. fill = the install state the fill
    # will commit (S from shared data, E from exclusive data).
    # gem5: cpu access stalls  .sm:1072 (z_stallAndWaitMandatoryQueue .sm:988)
    # gem5: {IS,IS_I} x Inv -> IS_I .sm:1364 (fi_sendInvAck)
    # gem5: IS x Data_all_Acks/DataS_fromL1 -> S .sm:1374/.sm:1404
    # gem5: IS x Data_Exclusive -> E            .sm:1456
    # Snoop-during-fill answers come from the pending-fill bypass at the
    # POST-FILL state (MAS ch02/02); the snoop's own state effect is applied
    # after the fill commits (MAS ch02/02 "Snoop vs Fill Ordering"), which
    # is the amber realization of the gem5 IS_I race resolution.
    # =====================================================================
    add('IS', 'CPU_RD', exp_next='IS', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('IS', 'CPU_WR', exp_next='IS', exp_result='STALL', cite=f'{SM}:1072 stall')
    for pf, cr_rs, cr_cs in (('S', CR_S_RS, CR_NONE), ('E', CR_E_RS, CR_E_CS)):
        add('IS', 'SNOOP_READ_SHARED', fill=pf, exp_next='IS',
            exp_result='RESPOND', ref=pf, exp_crresp=cr_rs,
            exp_pending=('S' if pf == 'E' else None),
            cite=f'{SM}: none (no Fwd to non-sharer); MAS ch02/02 pf answers post-fill state')
        add('IS', 'SNOOP_READ_ONCE', fill=pf, exp_next='IS',
            exp_result='RESPOND', ref=pf,
            exp_crresp=CR_E_RS if pf == 'E' else CR_S_RS,
            exp_pending=('S' if pf == 'E' else None),
            cite=f'{SM}: none; MAS ch02/02; HAS T3.0 {pf} row')
        add('IS', 'SNOOP_READ_UNIQUE', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf,
            exp_crresp=CR_E_RU if pf == 'E' else CR_NONE,
            cite=f'{SM}:1364 ({{IS,IS_I}}, Inv, IS_I); commits I per .sm:1390')
        add('IS', 'SNOOP_CLEAN_SHARED', fill=pf, exp_next='IS',
            exp_result='RESPOND', ref=pf, exp_crresp=cr_cs,
            cite=f'{SM}: none; HAS T3.0 {pf} row')
        add('IS', 'SNOOP_CLEAN_INVALID', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf, exp_crresp=CR_NONE,
            cite=f'{SM}:1364 ({{IS,IS_I}}, Inv, IS_I)')
        add('IS', 'SNOOP_MAKE_INVALID', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf, exp_crresp=CR_NONE,
            cite=f'{SM}:1364 ({{IS,IS_I}}, Inv, IS_I)')
    add('IS', 'FILL_DONE', fill='S', exp_next='S', exp_result='COMMIT',
        cite=f'{SM}:1374/1404 (IS, Data*_all/DataS_fromL1, S)')
    add('IS', 'FILL_DONE', fill='E', exp_next='E', exp_result='COMMIT',
        cite=f'{SM}:1456 (IS, Data_Exclusive, E)')
    add('IS', 'FILL_DONE', fill='E', in_pending='S', exp_next='S',
        exp_result='COMMIT',
        cite='MAS ch02/02 post-commit downgrade; gem5 analog .sm:1292 (E->S)')

    # =====================================================================
    # IS_I -- read fill in flight that an invalidating snoop already
    # claimed: fill data still commits, the line installs Invalid.
    # gem5: IS_I x Data_all_Acks -> I .sm:1390 (u_writeDataToL1Cache!)
    # gem5: IS_I x Data_Exclusive -> I .sm:1438
    # gem5: {IS,IS_I} x Inv -> IS_I  .sm:1364 (repeat invalidations stick)
    # =====================================================================
    add('IS_I', 'CPU_RD', exp_next='IS_I', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('IS_I', 'CPU_WR', exp_next='IS_I', exp_result='STALL', cite=f'{SM}:1072 stall')
    for pf in ('S', 'E'):
        add('IS_I', 'SNOOP_READ_SHARED', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf,
            exp_crresp=CR_E_RS if pf == 'E' else CR_S_RS,
            cite=f'{SM}:1364 (stays IS_I); MAS ch02/02 pf answers post-fill state')
        add('IS_I', 'SNOOP_READ_ONCE', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf,
            exp_crresp=CR_E_RS if pf == 'E' else CR_S_RS,
            cite=f'{SM}:1364; HAS T3.0 {pf} row')
        add('IS_I', 'SNOOP_READ_UNIQUE', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf,
            exp_crresp=CR_E_RU if pf == 'E' else CR_NONE,
            cite=f'{SM}:1364; HAS T3.0 {pf} row')
        add('IS_I', 'SNOOP_CLEAN_SHARED', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf,
            exp_crresp=CR_E_CS if pf == 'E' else CR_NONE,
            cite=f'{SM}:1364; HAS T3.0 {pf} row')
        add('IS_I', 'SNOOP_CLEAN_INVALID', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf, exp_crresp=CR_NONE,
            cite=f'{SM}:1364 ({{IS,IS_I}}, Inv, IS_I)')
        add('IS_I', 'SNOOP_MAKE_INVALID', fill=pf, exp_next='IS_I',
            exp_result='RESPOND', ref=pf, exp_crresp=CR_NONE,
            cite=f'{SM}:1364 ({{IS,IS_I}}, Inv, IS_I)')
    add('IS_I', 'FILL_DONE', fill='S', exp_next='I', exp_result='COMMIT',
        cite=f'{SM}:1390 (IS_I, Data_all_Acks, I) data committed, state I')
    add('IS_I', 'FILL_DONE', fill='E', exp_next='I', exp_result='COMMIT',
        cite=f'{SM}:1438 (IS_I, Data_Exclusive, E) DIVERGES: gem5 installs E; '
             f'amber commits I (divergence 8, invalidation-sticks)')

    # =====================================================================
    # IM -- write-miss fill in flight (installs M, write merges on replay
    # per DECISION D-4). The pending register carries the snoop's
    # post-commit effect (HAS ch02/02): downgrade-to-S or invalidate-to-I
    # applied at fill commit. Invalidating snoops DIVERGE from gem5
    # (IM x Inv -> IM, .sm:1475, ends M under directory serialization):
    # amber's broadcast fabric applies the invalidation, so the line ends
    # I -- the gem5 IS_I data-committed-as-Invalid pattern (.sm:1390).
    # gem5: IM x Data_all_Acks -> M .sm:1497 (hhx_store_hit)
    # =====================================================================
    add('IM', 'CPU_RD', exp_next='IM', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('IM', 'CPU_WR', exp_next='IM', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('IM', 'SNOOP_READ_SHARED', exp_next='IM', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RS, exp_pending='S',
        cite=f'{SM}: none; MAS ch02/02 post-commit M->S; composes with S x CPU_WR->SM (.sm:1244)')
    add('IM', 'SNOOP_READ_ONCE', exp_next='IM', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RO, exp_pending='I',
        cite=f'{SM}: none; HAS T3.0 M row applied post-commit')
    add('IM', 'SNOOP_READ_UNIQUE', exp_next='IM', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RO, exp_pending='I',
        cite=f'{SM}:1475 (IM, Inv, IM) DIVERGES: dir. ends M; amber commits I (.sm:1390 pattern)')
    add('IM', 'SNOOP_CLEAN_SHARED', exp_next='IM', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RS, exp_pending='S',
        cite=f'{SM}: none; HAS T3.0 M row applied post-commit')
    add('IM', 'SNOOP_CLEAN_INVALID', exp_next='IM', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RS, exp_pending='I',
        cite=f'{SM}:1475 analog DIVERGES (as RU); HAS T3.0 M row post-commit')
    add('IM', 'SNOOP_MAKE_INVALID', exp_next='IM', exp_result='RESPOND',
        ref='M', exp_crresp=CR_NONE, exp_pending='I',
        cite=f'{SM}:1475 analog DIVERGES; IHI0022 forbids DT')
    add('IM', 'FILL_DONE', exp_next='M', exp_result='COMMIT',
        cite=f'{SM}:1497 (IM, Data_all_Acks, M)')
    add('IM', 'FILL_DONE', in_pending='S', exp_next='S', exp_result='COMMIT',
        cite='MAS ch02/02 post-commit downgrade; gem5 ordering-equivalent (.sm:1338 after .sm:1497)')
    add('IM', 'FILL_DONE', in_pending='I', exp_next='I', exp_result='COMMIT',
        cite=f'{SM}:1390 pattern: fill data committed, line installs Invalid')

    # =====================================================================
    # SM -- upgrade (CleanUnique) in flight; the S line stays installed,
    # so snoops answer from S. An exclusive-domain snoop kills the
    # upgrade: convert to a full exclusive fetch.
    # gem5: transition(SM, Inv, IM) .sm:1526 (fi_sendInvAck)
    # gem5: transition(SM, Ack_all, M) .sm:1537 (hhx_store_hit)
    # =====================================================================
    add('SM', 'CPU_RD', exp_next='SM', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('SM', 'CPU_WR', exp_next='SM', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('SM', 'SNOOP_READ_SHARED', exp_next='SM', exp_result='RESPOND',
        ref='S', exp_crresp=CR_S_RS,
        cite=f'{SM}: none; upgrade unaffected by shared-domain read')
    add('SM', 'SNOOP_READ_ONCE', exp_next='SM', exp_result='RESPOND',
        ref='S', exp_crresp=CR_S_RS, cite=f'{SM}: none; HAS T3.0 S row')
    add('SM', 'SNOOP_READ_UNIQUE', exp_next='IM', exp_result='RESPOND',
        ref='S', exp_crresp=CR_NONE,
        cite=f'{SM}:1526 (SM, Inv, IM) upgrade lost -> exclusive fetch')
    add('SM', 'SNOOP_CLEAN_SHARED', exp_next='SM', exp_result='RESPOND',
        ref='S', exp_crresp=CR_NONE, cite=f'{SM}: none; HAS T3.0 S row')
    add('SM', 'SNOOP_CLEAN_INVALID', exp_next='IM', exp_result='RESPOND',
        ref='S', exp_crresp=CR_NONE, cite=f'{SM}:1526 (SM, Inv, IM)')
    add('SM', 'SNOOP_MAKE_INVALID', exp_next='IM', exp_result='RESPOND',
        ref='S', exp_crresp=CR_NONE, cite=f'{SM}:1526 (SM, Inv, IM)')
    add('SM', 'FILL_DONE', exp_next='M', exp_result='COMMIT',
        cite=f'{SM}:1537 (SM, Ack_all, M) upgrade completes')

    # =====================================================================
    # M_I -- this line was Modified, chosen as victim, dirty data staged
    # in the victim buffer, writeback (drain) in flight; the tag is gone.
    # gem5: transition({E,M}, Repl, M_I) .sm:1271/.sm:1308 (g_issuePUTX)
    # gem5: transition(M_I, Fwd_GETX, SINK_WB_ACK) .sm:1352 (dt from TBE)
    # gem5: transition(M_I, {{Fwd_GETS,INSTR}}, SINK_WB_ACK) .sm:1357 (dt+d2t)
    # gem5: transition(M_I, Inv, SINK_WB_ACK) .sm:1327 (ft_sendDataToL2)
    # gem5: transition(M_I, WB_Ack, I) .sm:1315
    # MakeInvalid has no gem5 analog (single Inv flavor); IHI0022 forbids
    # DT -- the victim drain already ordered to memory is not canceled.
    # =====================================================================
    add('M_I', 'CPU_RD', exp_next='M_I', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('M_I', 'CPU_WR', exp_next='M_I', exp_result='STALL', cite=f'{SM}:1072 stall')
    add('M_I', 'SNOOP_READ_SHARED', exp_next='SINK_WB_ACK', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RS,
        cite=f'{SM}:1357 (M_I, {{Fwd_GETS,INSTR}}, SINK_WB_ACK)')
    add('M_I', 'SNOOP_READ_ONCE', exp_next='SINK_WB_ACK', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RO,
        cite=f'{SM}:1357 analog; HAS T3.0 M row (RO -> Invalid; line already out)')
    add('M_I', 'SNOOP_READ_UNIQUE', exp_next='SINK_WB_ACK', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RO, cite=f'{SM}:1352 (M_I, Fwd_GETX, SINK_WB_ACK)')
    add('M_I', 'SNOOP_CLEAN_SHARED', exp_next='SINK_WB_ACK', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RS,
        cite=f'{SM}: none; ft analog .sm:1327 (dirty drains, stays out)')
    add('M_I', 'SNOOP_CLEAN_INVALID', exp_next='SINK_WB_ACK', exp_result='RESPOND',
        ref='M', exp_crresp=CR_M_RS, cite=f'{SM}:1327 (M_I, Inv, SINK_WB_ACK)')
    add('M_I', 'SNOOP_MAKE_INVALID', exp_next='SINK_WB_ACK', exp_result='RESPOND',
        ref='M', exp_crresp=CR_NONE,
        cite=f'{SM}:1327 analog; IHI0022 forbids DT; drain not canceled')
    add('M_I', 'DRAIN_DONE', exp_next='I', exp_result='COMMIT',
        cite=f'{SM}:1315 (M_I, WB_Ack, I)')

    # =====================================================================
    # SINK_WB_ACK -- a snoop already hit the in-flight victim; only the
    # WB ack remains. gem5 defines Inv here (.sm:1562); Fwd_* repeats are
    # an amber derivation -- the victim buffer still holds the line and
    # re-serves it until the WB ack lands.
    # gem5: transition(SINK_WB_ACK, WB_Ack, I) .sm:1567
    # =====================================================================
    add('SINK_WB_ACK', 'CPU_RD', exp_next='SINK_WB_ACK', exp_result='STALL',
        cite=f'{SM}:1072 stall')
    add('SINK_WB_ACK', 'CPU_WR', exp_next='SINK_WB_ACK', exp_result='STALL',
        cite=f'{SM}:1072 stall')
    add('SINK_WB_ACK', 'SNOOP_READ_SHARED', exp_next='SINK_WB_ACK',
        exp_result='RESPOND', ref='M', exp_crresp=CR_M_RS,
        cite=f'{SM}: none (no Fwd_* from SINK_WB_ACK); victim buffer re-serves; '
             f'.sm:1562 Inv is ack-only, cited as CONTRAST not support')
    add('SINK_WB_ACK', 'SNOOP_READ_ONCE', exp_next='SINK_WB_ACK',
        exp_result='RESPOND', ref='M', exp_crresp=CR_M_RO,
        cite=f'{SM}: none; HAS T3.0 M row; contrast .sm:1562')
    add('SINK_WB_ACK', 'SNOOP_READ_UNIQUE', exp_next='SINK_WB_ACK',
        exp_result='RESPOND', ref='M', exp_crresp=CR_M_RO,
        cite=f'{SM}: none; HAS T3.0 M row; contrast .sm:1562')
    add('SINK_WB_ACK', 'SNOOP_CLEAN_SHARED', exp_next='SINK_WB_ACK',
        exp_result='RESPOND', ref='M', exp_crresp=CR_M_RS,
        cite=f'{SM}: none; HAS T3.0 M row; contrast .sm:1562')
    add('SINK_WB_ACK', 'SNOOP_CLEAN_INVALID', exp_next='SINK_WB_ACK',
        exp_result='RESPOND', ref='M', exp_crresp=CR_M_RS,
        cite=f'{SM}:1562 (SINK_WB_ACK, Inv) CONTRAST: gem5 acks only '
             f'(fi_sendInvAck -- its WB already delivered the data); amber '
             f're-serves DT+PD+IS from the victim buffer (derivation)')
    add('SINK_WB_ACK', 'SNOOP_MAKE_INVALID', exp_next='SINK_WB_ACK',
        exp_result='RESPOND', ref='M', exp_crresp=CR_NONE,
        cite=f'{SM}:1562 as CONTRAST (ack-only); IHI0022 forbids DT')
    add('SINK_WB_ACK', 'DRAIN_DONE', exp_next='I', exp_result='COMMIT',
        cite=f'{SM}:1567 (SINK_WB_ACK, WB_Ack, I)')

    return rows


TABLE = _build_table()

# (state, event) cells that must raise: no legal transition exists. From
# the stable states no transaction is ever outstanding; transients hold at
# most one transaction, and its completion event is the other one.
UNREACHABLE_CELLS = [
    ('I', 'FILL_DONE'), ('I', 'DRAIN_DONE'),
    ('S', 'FILL_DONE'), ('S', 'DRAIN_DONE'),
    ('E', 'FILL_DONE'), ('E', 'DRAIN_DONE'),
    ('M', 'FILL_DONE'), ('M', 'DRAIN_DONE'),
    ('IS', 'DRAIN_DONE'), ('IS_I', 'DRAIN_DONE'),
    ('IM', 'DRAIN_DONE'), ('SM', 'DRAIN_DONE'),
    ('M_I', 'FILL_DONE'), ('SINK_WB_ACK', 'FILL_DONE'),
]

RESERVED_STATE_NAMES = ['O', 'RSV5', 'RSV6', 'RSV7']


# ---------------------------------------------------------------------------
# Pure-pytest half: oracle vs the hand-cited table
# ---------------------------------------------------------------------------
def _row_id(row):
    parts = [row['state'], row['event']]
    if row['fill']:
        parts.append(f"fill={row['fill']}")
    if row['in_pending']:
        parts.append(f"in_pending={row['in_pending']}")
    return '+'.join(parts)


@pytest.mark.parametrize('row', TABLE, ids=[_row_id(r) for r in TABLE])
def test_oracle_matches_table(row):
    """Every reachable cell: oracle.step() == the hand-cited gem5 row."""
    res = step(row['state'], row['event'], fill=row['fill'],
               pending=row['in_pending'])
    assert res.next_state == row['exp_next'], \
        f"{_row_id(row)}: next {res.next_state} != {row['exp_next']} [{row['cite']}]"
    assert res.result == row['exp_result'], \
        f"{_row_id(row)}: result {res.result} != {row['exp_result']} [{row['cite']}]"
    assert res.req == row['exp_req'], \
        f"{_row_id(row)}: req {res.req} != {row['exp_req']} [{row['cite']}]"
    assert res.crresp == row['exp_crresp'], \
        f"{_row_id(row)}: crresp 0b{res.crresp or 0:05b} != " \
        f"0b{(row['exp_crresp'] or 0):05b} [{row['cite']}]"
    assert res.pending == row['exp_pending'], \
        f"{_row_id(row)}: pending {res.pending} != {row['exp_pending']} [{row['cite']}]"


def test_oracle_table_inventory():
    """The table covers the reachable (state, event) domain exactly."""
    reachable = {(s, e) for s in STATES for e in EVENTS} - set(UNREACHABLE_CELLS)
    covered = {(r['state'], r['event']) for r in TABLE}
    assert covered == reachable, \
        f"missing {sorted(reachable - covered)} extra {sorted(covered - reachable)}"
    # Every one of the ten amber events fires from at least one state, and
    # every state answers at least one event.
    assert {e for _, e in covered} == set(EVENTS)
    assert {s for s, _ in covered} == set(STATES)


@pytest.mark.parametrize('state,event', UNREACHABLE_CELLS,
                         ids=[f'{s}+{e}' for s, e in UNREACHABLE_CELLS])
def test_oracle_unreachable_cells_raise(state, event):
    """Cells with no legal transition must raise, never guess."""
    with pytest.raises(AmberOracleError):
        step(state, event)


@pytest.mark.parametrize('state', RESERVED_STATE_NAMES)
def test_oracle_reserved_state_encodings_raise(state):
    """Reserved line-state encodings (incl. MOESI O) land in ERROR."""
    with pytest.raises(AmberOracleError):
        step(state, 'SNOOP_READ_SHARED')
    with pytest.raises(AmberOracleError):
        step(state, 'CPU_RD')


def test_oracle_reserved_snoop_encodings_raise():
    """Snoop codes 6/7 are not IHI0022 encodings; the oracle refuses them."""
    for bad in ('SNOOP_RESERVED_6', 'SNOOP_RESERVED_7', 6, 7):
        with pytest.raises(AmberOracleError):
            step('I', bad)


def test_oracle_unknown_event_raises():
    with pytest.raises(AmberOracleError):
        step('I', 'BOGUS_EVENT')


def test_oracle_pending_composition():
    """A second snoop during IM recomputes the post-commit effect against
    the pending state, not the install state: RS then RU ends Invalid
    (S then invalidate), never back at Shared."""
    res = step('IM', 'SNOOP_READ_SHARED')
    assert res.pending == 'S'
    res = step('IM', 'SNOOP_READ_UNIQUE', pending=res.pending)
    assert res.pending == 'I'
    res = step('IM', 'FILL_DONE', pending=res.pending)
    assert (res.next_state, res.result) == ('I', 'COMMIT')


# ---------------------------------------------------------------------------
# cocotb half: oracle vs the landed pkg decode (amber_snoop_kmap)
# ---------------------------------------------------------------------------
@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_amber_oracle_pkg_pin(dut):
    tb = AmberOracleTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run(TABLE)
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_oracle pkg-pin: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_amber_oracle_pkg_pin(request, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amber': 'projects/components/cache-ip/amber-mesi-l1/rtl/fub',
    })
    dut_name = "amber_snoop_kmap"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f'{FILELIST_DIR}/amber_snoop_kmap.f')

    test_name_plus_params = f"test_amber_oracle_pkg_pin_{test_level}"
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO')

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*60}\nRunning {test_name_plus_params}\nLog: {log_path}\n{'='*60}")
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_amber_oracle_pkg_pin",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"PASS {test_name_plus_params}")
    except Exception as e:
        print(f"FAIL {test_name_plus_params}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise
