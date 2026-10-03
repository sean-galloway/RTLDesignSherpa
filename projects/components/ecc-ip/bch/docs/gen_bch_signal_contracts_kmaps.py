#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate bch_signal_contracts.xlsx for the BCH MAS v0.1.

Modeled on projects/components/dma-ip/stream/docs/gen_signal_contracts_kmaps.py.

At MAS v0.1 there is no RTL, so the citations point at the MAS pages where
the intended expressions are written verbatim. When RTL lands, the citations
are re-pointed at the corresponding .sv file:line and the generator's citation
gate will catch drift.

Builds, from scratch (rerunnable / idempotent):
  * CONTRACT sheet -- core valid/ready signal contract table
  * K-MAP sheet -- decision tables for the key combinational qualifiers
    documented in the MAS block pages

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
# MAS paths (citations point here until RTL exists)
# ---------------------------------------------------------------------------
ENC = "projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/01_encoder.md"
SYN = "projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/02_syndrome_unit.md"
CHN = "projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/04_chien_search.md"
DEC = "projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/05_decoder_core.md"
SIG = "projects/components/ecc-ip/bch/docs/bch_mas/ch03_interfaces/01_core_signals.md"

CITES = [
    # encoder qualifiers
    (ENC, 109, "w_parity_phase = (r_bit_count >= K_BITS) && w_beat_is_parity"),
    (ENC, 116, "w_beat_is_parity = (r_bit_count + BITS_PER_BEAT - 1) >= K_BITS"),
    (ENC, 129, "w_enc_out_last = w_parity_phase && (r_parity_count == N_BITS - K_BITS - 1)"),
    (ENC, 164, "  w_frame_err = in_last && (r_bit_count != K_BITS - 1)"),

    # syndrome qualifiers
    (SYN, 109, "w_no_error = (S_1 == 0) && (S_3 == 0) && ... && (S_2t-1 == 0)"),
    (SYN, 121, "w_syndrome_done = (r_bit_count == N_BITS - 1) && in_valid && in_ready"),

    # Chien / decoder qualifiers
    (CHN, 102, "w_flip_en[i] = w_root[i] && w_correctable && !w_release_passthrough"),
    (CHN, 115, "w_correctable = (r_root_count == r_lambda_degree) && (r_lambda_degree <= T_BITS)"),
    (DEC, 91, "w_release_passthrough = w_uncorrectable || w_frame_err"),
    (DEC, 126, "w_uncorrectable = !w_correctable || (w_recheck_enabled && !w_recheck_zero)"),
    (DEC, 127, "w_correctable = (r_root_count == r_lambda_degree) && (r_lambda_degree <= T_BITS)"),

    # signal contract page posture
    (SIG, 32, "All core logic uses **synchronous active-low reset**"),
]


def build_core_signal_contract(wb):
    rows = [
        ("Encoder intake", "in_valid", "1", "in", "upstream",
         "a beat of data bits is offered", "stable until in_ready high",
         f"{ENC}:interface table"),
        ("Encoder intake", "in_ready", "1", "out", "encoder core",
         "core takes the beat this cycle", "combinational !r_valid || m_ready",
         f"{ENC}:interface table"),
        ("Encoder intake", "in_data", "BITS_PER_BEAT", "in", "upstream",
         "data bits, low-aligned", "partial final beat qualified by in_keep",
         f"{ENC}:interface table"),
        ("Encoder intake", "in_keep", "BITS_PER_BEAT", "in", "upstream",
         "present-bit mask, low-aligned", "partial only on block final beat",
         f"{ENC}:interface table"),
        ("Encoder intake", "in_last", "1", "in", "upstream",
         "this beat carries the K_BITS-th data bit", "sole block boundary",
         f"{ENC}:interface table"),
        ("Encoder outlet", "out_valid", "1", "out", "encoder core",
         "a beat of coded bits is offered", "data beats then parity beats",
         f"{ENC}:interface table"),
        ("Encoder outlet", "out_data", "BITS_PER_BEAT", "out", "encoder core",
         "data while !w_parity_phase, parity while w_parity_phase",
         "systematic: data passes through unchanged",
         f"{ENC}:109"),
        ("Encoder outlet", "out_last", "1", "out", "encoder core",
         "this beat carries the N_BITS-th coded bit",
         "raises only in parity phase at final parity count",
         f"{ENC}:129"),
        ("Encoder outlet", "frame_err", "1", "out", "encoder core",
         "pulse: block ended with other than K_BITS data bits",
         "in_last && (r_bit_count != K_BITS - 1)",
         f"{ENC}:164"),
        ("Decoder intake", "in_valid/in_ready", "1/1", "in/out", "decoder core",
         "valid/ready for received bits", "ready drops when buffer full",
         f"{DEC}:interface table"),
        ("Decoder intake", "in_last", "1", "in", "upstream",
         "this beat carries the N_BITS-th received bit", "sole block boundary",
         f"{DEC}:interface table"),
        ("Decoder outlet", "out_valid", "1", "out", "decoder core",
         "corrected data block is offered", "high only after verdict final",
         f"{DEC}:interface table"),
        ("Decoder outlet", "out_data", "BITS_PER_BEAT", "out", "decoder core",
         "corrected data bits; parity lanes dropped", "uncorrectable block leaves as received",
         f"{DEC}:91"),
        ("Decoder outlet", "out_last", "1", "out", "decoder core",
         "this beat carries the K_BITS-th data bit", "marks block end",
         f"{DEC}:interface table"),
        ("Decoder status", "out_status_ok", "1", "out", "decoder core",
         "block had no errors", "held for every beat of the block",
         f"{SYN}:109"),
        ("Decoder status", "out_status_corrected", "$clog2(T_BITS+1)", "out", "decoder core",
         "bits corrected (0 .. T_BITS)", "held for every beat of the block",
         f"{CHN}:115"),
        ("Decoder status", "out_status_uncorrectable", "1", "out", "decoder core",
         "correction failed; data pass through unchanged",
         "!w_correctable or recheck non-zero",
         f"{DEC}:126"),
        ("Decoder status", "out_status_frame_err", "1", "out", "decoder core",
         "block length was not N_BITS", "held for every beat of the block",
         f"{DEC}:interface table"),
    ]
    contract_sheet(
        wb, "Core signals",
        "BCH core valid/ready signal contract (pre-RTL, cites MAS pages)",
        "The core presents the house valid/ready contract at both ends. "
        "Widths and reset values are parametric; behavior is tied to the "
        "MAS block pages. Sources: "
        f"{ENC}, {SYN}, {CHN}, {DEC}, {SIG}.",
        rows)


def build_bch_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps BCH qualifiers")
    km.sheet_intro(
        "BCH codec - decision K-maps (pre-RTL, citations point at MAS pages)",
        ["Each table is computed from a Python mirror of the intended expression",
         "cited in the MAS. The verdict is NOT CHECKED because no RTL exists yet.",
         "When RTL lands, the citations are re-pointed at .sv file:line and the",
         "verdict becomes meaningful."])

    km.kmap(
        "w_parity_phase", f"{ENC}:109",
        "w_parity_phase = (r_bit_count >= K_BITS) && w_beat_is_parity",
        [("bit_ge_k", "r_bit_count >= K_BITS", f"{ENC}:109"),
         ("beat_is_parity",
          "w_beat_is_parity = (r_bit_count + BITS_PER_BEAT - 1) >= K_BITS",
          f"{ENC}:116")],
        lambda k, b: k and b,
        "Single 1-cell at (1,1): parity is selected only after the data phase "
        "ends AND the current output beat carries at least one parity bit.",
        depends_only_on=(
            "these two. K_BITS and BITS_PER_BEAT are elaboration-time constants; "
            "the bit counter is the only runtime variable feeding both terms. "
            "The mux data/parity payload does not gate the phase select."),
        rtl_sop="bit_ge_k & beat_is_parity")

    km.kmap(
        "w_enc_out_last", f"{ENC}:129",
        "w_enc_out_last = w_parity_phase && (r_parity_count == N_BITS - K_BITS - 1)",
        [("parity_phase", "w_parity_phase", f"{ENC}:109"),
         ("last_parity",
          "r_parity_count == N_BITS - K_BITS - 1",
          f"{ENC}:129")],
        lambda p, l: p and l,
        "Single 1-cell at (1,1): the final coded bit leaves only during the "
        "parity phase when the last parity symbol is being emitted.",
        depends_only_on=(
            "these two. The bit counter value and the parity count are the only "
            "runtime state; N_BITS and K_BITS are elaboration constants. The "
            "output beat payload does not gate out_last."),
        rtl_sop="parity_phase & last_parity")

    km.kmap(
        "w_frame_err (encoder)", f"{ENC}:164",
        "w_frame_err = in_last && (r_bit_count != K_BITS - 1)",
        [("in_last", "in_last", f"{ENC}:164"),
         ("wrong_length", "r_bit_count != K_BITS - 1", f"{ENC}:164")],
        lambda i, w: i and w,
        "Single 1-cell at (1,1): a block boundary that does not coincide with "
        "the K_BITS-th data bit is a framing error (R1/R2).",
        depends_only_on=(
            "these two. K_BITS is an elaboration constant; the bit counter and "
            "the in_last flag are the runtime inputs. No other encoder signal "
            "can create or suppress a frame error."),
        rtl_sop="in_last & wrong_length")

    km.kmap(
        "w_syndrome_done", f"{SYN}:121",
        "w_syndrome_done = (r_bit_count == N_BITS - 1) && in_valid && in_ready",
        [("last_bit", "r_bit_count == N_BITS - 1", f"{SYN}:121"),
         ("in_valid", "in_valid", f"{SYN}:121"),
         ("in_ready", "in_ready", f"{SYN}:121")],
        lambda l, v, r: l and v and r,
        "Single 1-cell at (1,1,1): the syndrome unit completes only on the "
        "cycle the final bit is accepted. A last-bit cycle without a handshake "
        "does not complete the syndromes.",
        depends_only_on=(
            "these three. N_BITS is an elaboration constant; the bit counter, "
            "the offered valid, and the accepted ready are the only runtime "
            "inputs. The syndrome lane values do not gate completion."),
        rtl_sop="last_bit & in_valid & in_ready")

    km.kmap(
        "w_no_error", f"{SYN}:109",
        "w_no_error = (S_1 == 0) && (S_3 == 0) && ... && (S_2t-1 == 0)",
        [("S_1_zero", "S_1 == 0", f"{SYN}:109"),
         ("S_rest_zero", "(S_3 == 0) && ... && (S_2t-1 == 0)", f"{SYN}:109")],
        lambda s1, sr: s1 and sr,
        "Single 1-cell at (1,1): all odd syndromes zero means the block has no "
        "detectable errors and the decoder can bypass solve and Chien.",
        depends_only_on=(
            "these two (a factoring of the t odd syndromes into S_1 and the rest). "
            "The evenness shortcut means even syndromes are derived, not inputs. "
            "No block-boundary or status signal gates the no-error decode."),
        rtl_sop="S_1_zero & S_rest_zero")

    km.kmap(
        "w_correctable", f"{DEC}:127",
        "w_correctable = (r_root_count == r_lambda_degree) && (r_lambda_degree <= T_BITS)",
        [("root_count_match", "r_root_count == r_lambda_degree", f"{DEC}:127"),
         ("degree_ok", "r_lambda_degree <= T_BITS", f"{DEC}:127")],
        lambda m, d: m and d,
        "Single 1-cell at (1,1): a block is correctable only when every root of "
        "Lambda is found (root count equals degree) and the degree is within "
        "the code's correction capability.",
        depends_only_on=(
            "these two. T_BITS is an elaboration constant; the root count and "
            "locator degree are produced by the Chien search and the solver. "
            "The original syndromes influence the result only through those two "
            "values."),
        rtl_sop="root_count_match & degree_ok")

    km.kmap(
        "w_flip_en[i]", f"{CHN}:102",
        "w_flip_en[i] = w_root[i] && w_correctable && !w_release_passthrough",
        [("root", "w_root[i] = (Lambda(alpha^-i) == 0)", f"{CHN}:102"),
         ("correctable", "w_correctable", f"{DEC}:127"),
         ("not_passthrough", "!w_release_passthrough", f"{DEC}:91")],
        lambda r, c, p: r and c and (not p),
        "Single 1-cell at (1,1,1): a bit is flipped only at a root position, "
        "in a correctable block, when the block is not being passed through "
        "unchanged.",
        depends_only_on=(
            "these three. The root flag is per-position; correctable and "
            "release_passthrough are per-block qualifiers. No error value is "
            "computed — binary codes always flip."),
        rtl_sop="root & correctable & !not_passthrough")

    km.kmap(
        "w_release_passthrough", f"{DEC}:91",
        "w_release_passthrough = w_uncorrectable || w_frame_err",
        [("uncorrectable", "w_uncorrectable", f"{DEC}:126"),
         ("frame_err", "w_frame_err", f"{ENC}:164 / decoder analog")],
        lambda u, f: u or f,
        "1s everywhere except (0,0): an uncorrectable block or a frame-error "
        "block leaves the buffer exactly as received (R2).",
        depends_only_on=(
            "these two. The pass-through decision is per-block; the Chien "
            "position and the individual root flags do not gate it. A block can "
            "be both uncorrectable and frame-erroneous, and the result is the "
            "same."),
        rtl_sop="uncorrectable | frame_err")


# ---------------------------------------------------------------------------
# Pre-RTL contract posture sheet
# ---------------------------------------------------------------------------
def build_posture_sheet(wb):
    km = new_kmap_sheet(wb, "Contract posture")
    km.sheet_intro(
        "Pre-RTL citation posture",
        ["The workbook cites the MAS pages where the intended expressions are",
         "written verbatim. When RTL lands, every MAS citation is re-pointed at",
         "the relevant .sv file:line and verify_citations will catch drift."])
    km.table(
        "Citation migration plan", "MAS pages -> RTL files",
        ["MAS page", "current citation target", "future RTL target"],
        [("Encoder core", ENC, "rtl/bch_encoder_core.sv"),
         ("Syndrome unit", SYN, "rtl/bch_syndrome_unit.sv"),
         ("Chien search", CHN, "rtl/bch_chien_search.sv"),
         ("Decoder core", DEC, "rtl/bch_decoder_core.sv"),
         ("Core signals", SIG, "rtl/bch_encoder_core.sv / rtl/bch_decoder_core.sv")],
        note="All verdicts render NOT CHECKED until the RTL citations land.")


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
