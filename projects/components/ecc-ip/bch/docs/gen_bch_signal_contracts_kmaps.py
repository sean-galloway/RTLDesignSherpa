#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate bch_signal_contracts.xlsx for the BCH MAS v0.1.

Modeled on projects/components/dma-ip/stream/docs/gen_signal_contracts_kmaps.py.

Post-RTL (TASK-003 close, 2026-10-08): every citation points at the landed
RTL file:line and `verify_citations` gates the workbook against RTL drift --
a rerun after an RTL edit fails loudly instead of publishing a stale map.
Each kmap's `rtl_sop` is the landed expression as written, so the rendered
verdict (IDENTICAL / DIFFERS) is the derived minimal cover diffed against
the silicon-intended logic. Where implementation moved a qualifier between
blocks relative to the pre-RTL MAS (the flip-gating factoring), the map
follows the RTL and the note says where the other half lives.

Builds, from scratch (rerunnable / idempotent):
  * CONTRACT sheet -- core valid/ready signal contract table
  * K-MAP sheet -- decision tables for the key combinational qualifiers
    of the landed encoder, syndrome unit, Chien search, and decoder core
  * posture sheet -- the MAS -> RTL citation migration record

Rerun after MAS or RTL changes:
    python3 docs/gen_bch_signal_contracts_kmaps.py
"""
import os
import sys

import openpyxl
from openpyxl.styles import Font

from kmaps.citations import verify_citations
from kmaps.styles import (CENTER, DCFILL, GRAY2, GREEN, GREY, HDR, MONO,
                          THIN, TITLE, WRAP)
from kmaps.writer import (CONTRACT_HDRS, KmapWriter, contract_sheet,
                          new_kmap_sheet)

HERE = os.path.dirname(os.path.abspath(__file__))
XLSX = os.path.join(HERE, "bch_signal_contracts.xlsx")
REPO = os.path.abspath(os.path.join(HERE, *(".." for _ in range(5))))

# ---------------------------------------------------------------------------
# RTL paths (citations point here; the MAS pages remain the methodology
# authority and are recorded on the posture sheet)
# ---------------------------------------------------------------------------
ENC = "projects/components/ecc-ip/bch/rtl/macro/bch_encoder_core.sv"
SYN = "projects/components/ecc-ip/bch/rtl/fub/bch_syndrome_unit.sv"
CHN = "projects/components/ecc-ip/bch/rtl/fub/bch_chien_search.sv"
DEC = "projects/components/ecc-ip/bch/rtl/macro/bch_decoder_core.sv"
SIG = "projects/components/ecc-ip/bch/docs/bch_mas/ch03_interfaces/01_core_signals.md"

CITES = [
    # encoder qualifiers
    (ENC, 225, "w_beat_is_parity = (r_bit_count + CNT_W'(B)"),
    (ENC, 226, "r_drain || ((r_bit_count >= CNT_W'(K))"),
    (ENC, 227, "w_parity_phase && ((r_parity_count"),
    (ENC, 228, "in_last && ((r_data_count + CNT_W'(w_in_count))"),
    # encoder datapath / handshake
    (ENC, 206, "= !r_drain && w_skid_wr_ready"),
    (ENC, 244, "{w_enc_out_last, w_par_keep, w_parity_bits}"),
    (ENC, 247, "{1'b0, in_keep, in_data}"),
    (ENC, 308, "assign {out_last, out_keep, out_data} = w_skid_rd_data;"),

    # syndrome qualifiers
    (SYN, 156, "(r_bit_count + CNT_W'(w_in_count) == CNT_W'(N))"),
    (SYN, 157, "w_syndrome_done = w_last_bit && in_valid && in_ready"),
    (SYN, 162, "out_no_error = (out_syndromes == '0)"),

    # Chien search qualifiers
    (CHN, 206, "w_root[u] = (sum == '0);"),
    (CHN, 212, "w_pos_valid[u] = (CNT_W'(r_position)"),
    (CHN, 230, "out_flip_en    = w_root & w_pos_valid"),

    # decoder framing / verdict / release
    (DEC, 336, "in_valid && !in_last && (w_rx_bit_next >= CNT_W'(N))"),
    (DEC, 337, "w_in_fire && ((in_last && (w_rx_bit_next != CNT_W'(N)))"),
    (DEC, 370, "((r_state == IDLE)"),
    (DEC, 396, "assign w_verdict_correctable = !r_more_than_t"),
    (DEC, 399, "(!ENABLE_RECHECK || w_rechk_out_no_error)"),
    (DEC, 413, "r_flip[r_release_idx] & {B{r_release_apply}}"),
    (DEC, 579, "r_flip[r_chien_beat_count] <= w_chien_out_flip_en"),
    (DEC, 592, "r_release_apply  <= 1'b1;"),

    # signal contract page posture (reset convention authority)
    (SIG, 32, "All core logic uses **synchronous active-low reset**"),
]


def build_core_signal_contract(wb):
    rows = [
        ("Encoder intake", "in_valid", "1", "in", "upstream",
         "a beat of data bits is offered", "stable until in_ready high",
         f"{ENC}:77"),
        ("Encoder intake", "in_ready", "1", "out", "encoder core",
         "core takes the beat this cycle",
         "low only while the parity-shift DRAIN state drains the skid",
         f"{ENC}:206"),
        ("Encoder intake", "in_data", "BITS_PER_BEAT", "in", "upstream",
         "data bits, low-aligned", "partial final beat qualified by in_keep",
         f"{ENC}:79"),
        ("Encoder intake", "in_keep", "BITS_PER_BEAT", "in", "upstream",
         "present-bit mask, low-aligned", "partial only on block final beat",
         f"{ENC}:80"),
        ("Encoder intake", "in_last", "1", "in", "upstream",
         "this beat carries the K_BITS-th data bit", "sole block boundary",
         f"{ENC}:81"),
        ("Encoder outlet", "out_valid", "1", "out", "encoder core",
         "a beat of coded bits is offered", "data beats then parity beats",
         f"{ENC}:83"),
        ("Encoder outlet", "out_data", "BITS_PER_BEAT", "out", "encoder core",
         "data while !w_parity_phase, parity while w_parity_phase",
         "systematic: data passes through unchanged",
         f"{ENC}:244, {ENC}:247, {ENC}:308"),
        ("Encoder outlet", "out_last", "1", "out", "encoder core",
         "this beat carries the N_BITS-th coded bit",
         "raises only in parity phase at final parity count",
         f"{ENC}:227"),
        ("Encoder outlet", "frame_err", "1", "out", "encoder core",
         "pulse: block ended with other than K_BITS data bits",
         "in_last && ((r_data_count + w_in_count) != K)",
         f"{ENC}:228"),
        ("Decoder intake", "in_valid/in_ready", "1/1", "in/out", "decoder core",
         "valid/ready for received bits",
         "ready drops outside SYND and once the block is ending; over-N blocks are still accepted so the sender can reach in_last (issue #90)",
         f"{DEC}:95, {DEC}:96, {DEC}:370"),
        ("Decoder intake", "in_last", "1", "in", "upstream",
         "this beat carries the N_BITS-th received bit", "sole block boundary",
         f"{DEC}:99"),
        ("Decoder outlet", "out_valid", "1", "out", "decoder core",
         "corrected data block is offered", "high only in RELEASE, per beat",
         f"{DEC}:411"),
        ("Decoder outlet", "out_data", "BITS_PER_BEAT", "out", "decoder core",
         "corrected data bits; parity lanes dropped",
         "uncorrectable block leaves as received (r_release_apply = 0)",
         f"{DEC}:413"),
        ("Decoder outlet", "out_last", "1", "out", "decoder core",
         "this beat carries the K_BITS-th data bit", "marks block end",
         f"{DEC}:414"),
        ("Decoder status", "out_status_ok", "1", "out", "decoder core",
         "block had no errors", "held for every beat of the block",
         f"{SYN}:162, {DEC}:417"),
        ("Decoder status", "out_status_corrected", "$clog2(T_BITS+1)", "out", "decoder core",
         "bits corrected (0 .. T_BITS)", "the Chien root count of a correctable block",
         f"{CHN}:231, {DEC}:418"),
        ("Decoder status", "out_status_uncorrectable", "1", "out", "decoder core",
         "correction failed; data pass through unchanged",
         "!w_verdict_correctable out of CHIEN/RECHECK",
         f"{DEC}:396, {DEC}:419"),
        ("Decoder status", "out_status_frame_err", "1", "out", "decoder core",
         "block length was not N_BITS (short, long, or over-N runaway)",
         "held for every beat of the block; issue #90 released the over-N prefix as frame_err",
         f"{DEC}:337, {DEC}:420"),
    ]
    contract_sheet(
        wb, "Core signals",
        "BCH core valid/ready signal contract (cites landed RTL)",
        "The core presents the house valid/ready contract at both ends. "
        "Widths and reset values are parametric; behavior cites the landed "
        "RTL file:line and the citation gate fails the build on drift. "
        f"Sources: {ENC}, {SYN}, {CHN}, {DEC}, {SIG}.",
        rows)


def build_bch_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps BCH qualifiers")
    km.sheet_intro(
        "BCH codec - decision K-maps (citations point at landed RTL)",
        ["Each table is computed from a Python mirror of the landed expression",
         "and every citation is gated: verify_citations fails the build if the",
         "RTL moves under a quoted line. Each map's rtl_sop is the RTL as",
         "written, so the VERDICT line is the derived minimal cover diffed",
         "against the silicon-intended logic (IDENTICAL, or DIFFERS with the",
         "reconciliation cases spelled out)."])

    km.kmap(
        "w_parity_phase", f"{ENC}:226",
        "w_parity_phase = r_drain || ((r_bit_count >= K_BITS) && w_beat_is_parity)",
        [("r_drain", "r_drain -- the parity shift-out state", f"{ENC}:32"),
         ("bit_ge_k", "r_bit_count >= K_BITS", f"{ENC}:226"),
         ("beat_is_parity",
          "w_beat_is_parity = (r_bit_count + BITS_PER_BEAT - 1) >= K_BITS",
          f"{ENC}:225")],
        lambda d, k, b: d or (k and b),
        "1s on the whole r_drain=1 page plus the single (0,1,1) cell: parity "
        "is selected during the DRAIN state, or once the data phase has ended "
        "AND the current output beat carries at least one parity bit.",
        depends_only_on=(
            "these three. K_BITS and BITS_PER_BEAT are elaboration-time constants; "
            "r_bit_count and r_drain are the only runtime state. w_beat_is_parity "
            "is a full-B lookahead (the RTL comment at the cite says so), which is "
            "why the phase can rise a beat early without emitting parity early: "
            "the payload mux (the DRAIN/output-select block) still gates what "
            "leaves. The pre-RTL MAS had no r_drain term -- the encoder shifts "
            "parity out of the skid buffer after in_last, and the drain state "
            "forces the phase for those beats."),
        rtl_sop="r_drain | bit_ge_k & beat_is_parity")

    km.kmap(
        "w_enc_out_last", f"{ENC}:227",
        "w_enc_out_last = w_parity_phase && ((r_parity_count + w_par_beat_len - 1) == N_BITS - K_BITS - 1)",
        [("parity_phase", "w_parity_phase", f"{ENC}:226"),
         ("last_parity",
          "r_parity_count + w_par_beat_len - 1 == N_BITS - K_BITS - 1",
          f"{ENC}:227")],
        lambda p, l: p and l,
        "Single 1-cell at (1,1): the final coded bit leaves only during the "
        "parity phase on the beat whose last parity bit is the N_BITS-th "
        "coded bit. r_parity_count + w_par_beat_len is the lookahead end of "
        "the current beat, the beat-granular twin of the MAS's per-bit count.",
        depends_only_on=(
            "these two. The bit counter value and the parity count are the only "
            "runtime state; N_BITS and K_BITS are elaboration constants. The "
            "output beat payload does not gate out_last."),
        rtl_sop="parity_phase & last_parity")

    km.kmap(
        "w_frame_err (encoder)", f"{ENC}:228",
        "w_frame_err = in_last && ((r_data_count + w_in_count) != K_BITS)",
        [("in_last", "in_last", f"{ENC}:228"),
         ("wrong_length", "r_data_count + w_in_count != K_BITS", f"{ENC}:228")],
        lambda i, w: i and w,
        "Single 1-cell at (1,1): a block boundary that does not coincide with "
        "the K_BITS-th data bit is a framing error.",
        depends_only_on=(
            "these two. K_BITS is an elaboration constant; r_data_count is the "
            "accepted-data count and w_in_count the presenting beat's keep "
            "count, so the check sees the would-be block total on the boundary "
            "cycle. No other encoder signal can create or suppress a frame "
            "error."),
        rtl_sop="in_last & wrong_length")

    km.kmap(
        "w_syndrome_done", f"{SYN}:157",
        "w_syndrome_done = w_last_bit && in_valid && in_ready",
        [("last_bit", "w_last_bit = (r_bit_count + w_in_count == N_BITS)", f"{SYN}:156"),
         ("in_valid", "in_valid", f"{SYN}:157"),
         ("in_ready", "in_ready", f"{SYN}:157")],
        lambda l, v, r: l and v and r,
        "Single 1-cell at (1,1,1): the syndrome unit completes only on the "
        "cycle the final bit is accepted. A last-bit cycle without a handshake "
        "does not complete the syndromes, and the decoder core only consumes "
        "the result once the block boundary has arrived (its "
        "w_synd_result_valid waits for in_last).",
        depends_only_on=(
            "these three. N_BITS is an elaboration constant; the bit counter, "
            "the offered valid, and the accepted ready are the only runtime "
            "inputs. The syndrome lane values do not gate completion."),
        rtl_sop="last_bit & in_valid & in_ready")

    km.kmap(
        "out_no_error", f"{SYN}:162",
        "out_no_error = (out_syndromes == '0)   -- S_1 == 0 && S_3 == 0 && ... && S_2t-1 == 0",
        [("S_1_zero", "S_1 == 0", f"{SYN}:162"),
         ("S_rest_zero", "(S_3 == 0) && ... && (S_2t-1 == 0)", f"{SYN}:162")],
        lambda s1, sr: s1 and sr,
        "Single 1-cell at (1,1): all odd syndromes zero means the block has no "
        "detectable errors and the decoder bypasses solve and Chien. The RTL "
        "compares the whole packed syndrome vector in one expression; the two "
        "axes are a factoring of that comparison (S_1 and the rest), not two "
        "separate hardware terms.",
        depends_only_on=(
            "these two (a factoring of the t odd syndromes into S_1 and the rest). "
            "The evenness shortcut means even syndromes are derived, not stored. "
            "No block-boundary or status signal gates the no-error decode; the "
            "register is stable from completion per the fub header."),
        rtl_sop="S_1_zero & S_rest_zero")

    km.kmap(
        "w_verdict_correctable", f"{DEC}:396",
        "w_verdict_correctable = !r_more_than_t && (root_count == r_lambda_degree) && (!ENABLE_RECHECK || w_rechk_out_no_error)",
        [("not_more_than_t", "!r_more_than_t -- solver degree within t", f"{DEC}:396"),
         ("root_count_match", "root_count == r_lambda_degree", f"{DEC}:397"),
         ("recheck_ok", "!ENABLE_RECHECK || w_rechk_out_no_error", f"{DEC}:399")],
        lambda m, r, c: m and r and c,
        "Single 1-cell at (1,1,1): a block is correctable only when the solver "
        "degree is within t, every root of Lambda was found, and the re-check "
        "syndromes of the corrected buffer are all zero. The map holds "
        "ENABLE_RECHECK = 1 (the default); with it 0 the recheck_ok axis is "
        "the constant 1 and the map collapses to the first two axes.",
        depends_only_on=(
            "these three. r_more_than_t and r_lambda_degree come from the solver "
            "(captured at SOLVE done), the root count is the Chien total -- the "
            "CHIEN/RECHECK mux in the RTL selects the live count in CHIEN and the "
            "value captured at the last beat in RECHECK, the same value at the "
            "decision points. The original syndromes influence the verdict only "
            "through these three terms."),
        rtl_sop="not_more_than_t & root_count_match & recheck_ok")

    km.kmap(
        "out_flip_en (Chien)", f"{CHN}:230",
        "out_flip_en[i] = w_root[i] && w_pos_valid[i]",
        [("root", "w_root[i] = (Lambda(alpha^-i) == 0)", f"{CHN}:206"),
         ("pos_valid", "w_pos_valid[i] = (r_position + i) < N_BITS", f"{CHN}:212")],
        lambda r, p: r and p,
        "Single 1-cell at (1,1): a flip is flagged only at a root position "
        "inside the block length. Beyond n (a shortened code's tail beats) the "
        "lanes are masked off so the root count and the flip mask cannot leak "
        "into padding.",
        depends_only_on=(
            "these two, per lane. The pre-RTL design folded the correctable and "
            "pass-through gating into this signal; the landed core separates "
            "concerns -- this is the raw per-beat flip map, the verdict gating "
            "is registered per block as r_release_apply (decoder core) and "
            "applied on the way out. Binary codes flip, never scale: there is "
            "no Forney stage and no magnitude."),
        rtl_sop="root & pos_valid")

    km.kmap(
        "out_data correction gating", f"{DEC}:413",
        "out_data = r_buf[r_release_idx] ^ (r_flip[r_release_idx] & {B{r_release_apply}})",
        [("flip", "r_flip[r_release_idx] -- the Chien beat map, registered during CHIEN", f"{DEC}:579"),
         ("apply", "r_release_apply -- w_verdict_correctable registered at decision", f"{DEC}:592")],
        lambda f, a: f and a,
        "Single 1-cell at (1,1): a buffered bit changes only where the Chien "
        "search flagged a root AND the final verdict says correctable. Every "
        "other combination leaves the buffer bit-for-bit -- that is the "
        "uncorrectable / frame-err pass-through (the core header's 'never "
        "silently pass a failed block' property).",
        depends_only_on=(
            "these two. r_flip was captured per beat while the Chien search "
            "walked the block; r_release_apply is the registered verdict, so "
            "the gating cannot change mid-release. The release index and keep "
            "logic select which buffered beat and lanes leave, not whether the "
            "correction applies."),
        rtl_sop="flip & apply")


# ---------------------------------------------------------------------------
# Citation migration record
# ---------------------------------------------------------------------------
def build_posture_sheet(wb):
    km = new_kmap_sheet(wb, "Citation posture")
    km.sheet_intro(
        "Citation posture (post-RTL)",
        ["Migrated 2026-10-08 with the TASK-003 close: every workbook citation",
         "moved from the pre-RTL MAS pages to the landed RTL file:line. The",
         "verify_citations gate at build time fails the generator if any RTL",
         "edit moves a quoted line, so the workbook cannot drift stale.",
         "Kmap verdicts render IDENTICAL / DIFFERS from the rtl_sop diff; all",
         "eight maps of the landed design render IDENTICAL (the RTL is already",
         "minimal for every mapped qualifier)."])
    km.table(
        "Citation migration record", "MAS pages -> RTL files (done 2026-10-08)",
        ["MAS page", "pre-RTL citation target", "RTL target since migration"],
        [("Encoder core", "docs/bch_mas/ch02_blocks/01_encoder.md", "rtl/macro/bch_encoder_core.sv"),
         ("Syndrome unit", "docs/bch_mas/ch02_blocks/02_syndrome_unit.md", "rtl/fub/bch_syndrome_unit.sv"),
         ("Chien search", "docs/bch_mas/ch02_blocks/04_chien_search.md", "rtl/fub/bch_chien_search.sv"),
         ("Decoder core", "docs/bch_mas/ch02_blocks/05_decoder_core.md", "rtl/macro/bch_decoder_core.sv"),
         ("Core signals", "docs/bch_mas/ch03_interfaces/01_core_signals.md", "both core .sv files (reset posture stays with the MAS page)")],
        note="The MAS pages remain the methodology authority; the workbook cites silicon.")


def main():
    verify_citations(CITES, REPO)
    wb = openpyxl.Workbook()
    del wb[wb.sheetnames[0]]           # drop the default sheet

    build_core_signal_contract(wb)
    build_bch_kmaps(wb)
    build_posture_sheet(wb)

    wb.save(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print("  ", name)


if __name__ == "__main__":
    main()
