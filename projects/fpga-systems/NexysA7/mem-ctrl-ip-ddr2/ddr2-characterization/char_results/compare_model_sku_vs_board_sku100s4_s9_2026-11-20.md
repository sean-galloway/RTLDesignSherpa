# The SKU model beside the board: granite sku100s4_2026-11-19

Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);
delta = (model - board) / board per direction, and the cell is IN when both directions land within
the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).
A cell with several board runs (`--board-also`) is read BY MODE: runs within the tolerance of each
other are one mode (`xN` = runs in it), every board mode needs a model run within tolerance (several
`--model` CSVs are the model's GO phases, labelled by their `GO offset`), and a model run in a mode
the board never showed is OUT; the delta column then carries one delta per board mode.

| board preset | scenario | board wr / rd | model wr / rd | delta wr / rd | tol | verdict |
|---|---|---|---|---|---|---|
| defaults | incremental_bl4 | 775 / 776 | 778 / 781 | +0.4 / +0.7 % | 2 % | IN |
| defaults | incremental_bl8 | 775 / 776 | 778 / 781 | +0.4 / +0.7 % | 2 % | IN |
| defaults | incremental_bl16 | 775 / 776 | 778 / 781 | +0.4 / +0.7 % | 2 % | IN |
| defaults | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| defaults | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| defaults | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| defaults | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| defaults | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_interleaved_bl4 | 765 / 762 | 771 / 771 | +0.9 / +1.2 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 768 / 767 | 771 / 771 | +0.4 / +0.6 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 776 / 775 | +0.5 / +0.7 % | 3 % | IN |
| defaults | mixed_bl8 | 272 / 273 (union 545) | 274 / 274 (union 547) | +0.4 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 768 / 766 | 771 / 771 | +0.4 / +0.7 % | 3 % | IN |
| defaults | random_bl8 | 723 / 750 | 726 / 744 | +0.4 / -0.8 % | 5 % | IN |
| open_page | incremental_bl4 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| open_page | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 767 / 767 | 775 / 775 | +1.1 / +1.1 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 770 / 770 | 775 / 777 | +0.7 / +0.9 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 776 / 779 | +0.5 / +0.8 % | 3 % | IN |
| open_page | mixed_bl8 | 311 / 522 (union 622) | 274 / 274 (union 547) | -12.0 % (union) | 10 % | OUT |
| open_page | row_thrash_bl8 | 770 / 770 | 775 / 777 | +0.7 / +0.9 % | 3 % | IN |
| open_page | random_bl8 | 728 / 757 | 731 / 752 | +0.4 / -0.6 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 387 / 387 | 388 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 387 / 387 | 388 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl8 | 387 / 387 | 389 / 389 | +0.5 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_bl4 | 283 / 388 | 283 / 389 | +0.1 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_bl8 | 388 / 388 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 387 / 387 | 389 / 389 | +0.3 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 243 / 317 | 246 / 322 | +1.4 / +1.4 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl8 | 387 / 387 | 389 / 389 | +0.4 / +0.5 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 387 / 387 | 388 / 389 | +0.4 / +0.4 % | 10 % | IN |
| close_page | incremental_bl4 | 82 / 92 | 82 / 93 | +0.1 / +0.3 % | 15 % | IN |
| close_page | incremental_bl8 | 82 / 92 | 82 / 93 | +0.1 / +0.3 % | 15 % | IN |
| close_page | incremental_bl16 | 82 / 92 | 82 / 93 | +0.1 / +0.3 % | 15 % | IN |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.1 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.2 / +0.1 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 386 / 387 | 388 / 389 | +0.3 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 250 / 361 | 254 / 334 | +1.8 / -7.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 171 / 238 | 172 / 239 | +0.6 / +0.6 % | 15 % | IN |
| close_page | mixed_bl8 | 56 / 59 (union 112) | 56 / 57 (union 113) | +0.1 % (union) | 15 % | IN |
| close_page | row_thrash_bl8 | 238 / 314 | 242 / 316 | +1.9 / +0.6 % | 15 % | IN |
| close_page | random_bl8 | 203 / 258 | 205 / 258 | +0.9 / -0.1 % | 15 % | IN |

56 cells in tolerance, 1 out. Largest deltas: open_page mixed_bl8 (12.0 %), close_page col_major_interleaved_bl8 (7.4 %), close_page row_thrash_bl8 (1.9 %), bank_interleave col_major_interleaved_bl4 (1.4 %), defaults col_major_interleaved_bl4 (1.2 %), open_page col_major_interleaved_bl4 (1.1 %).
