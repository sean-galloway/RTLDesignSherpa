# The SKU model beside the board: granite sku100bug004b_2026-11-18

Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);
delta = (model - board) / board per direction, and the cell is IN when both directions land within
the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).

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
| defaults | col_major_interleaved_bl4 | 765 / 762 | 777 / 780 | +1.7 / +2.3 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 768 / 767 | 777 / 780 | +1.2 / +1.6 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 777 / 779 | +0.6 / +1.2 % | 3 % | IN |
| defaults | mixed_bl8 | 269 / 269 (union 537) | 290 / 290 (union 580) | +8.0 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 768 / 766 | 777 / 779 | +1.2 / +1.7 % | 3 % | IN |
| defaults | random_bl8 | 719 / 739 | 734 / 749 | +2.0 / +1.4 % | 5 % | IN |
| open_page | incremental_bl4 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| open_page | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 767 / 767 | 777 / 780 | +1.4 / +1.6 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 770 / 770 | 777 / 780 | +0.9 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 777 / 779 | +0.6 / +0.8 % | 3 % | IN |
| open_page | mixed_bl8 | 272 / 273 (union 545) | 290 / 290 (union 580) | +6.6 % (union) | 10 % | IN |
| open_page | row_thrash_bl8 | 770 / 770 | 777 / 779 | +0.9 / +1.2 % | 3 % | IN |
| open_page | random_bl8 | 726 / 745 | 734 / 749 | +1.1 / +0.5 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 387 / 387 | 389 / 389 | +0.6 / +0.6 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 387 / 387 | 389 / 389 | +0.6 / +0.6 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 387 / 387 | 389 / 389 | +0.5 / +0.7 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 387 / 387 | 389 / 389 | +0.5 / +0.5 % | 10 % | IN |
| bank_interleave | row_major_bl8 | 387 / 387 | 389 / 389 | +0.5 / +0.6 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 387 / 387 | 389 / 389 | +0.5 / +0.6 % | 10 % | IN |
| bank_interleave | col_major_bl4 | 258 / 351 | 283 / 389 | +9.7 / +10.9 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 387 / 387 | 389 / 389 | +0.5 / +0.5 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 387 / 387 | 389 / 389 | +0.5 / +0.5 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 242 / 253 | 246 / 281 | +1.8 / +11.3 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 387 / 387 | 389 / 389 | +0.5 / +0.5 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 387 / 387 | 389 / 389 | +0.5 / +0.5 % | 10 % | IN |
| close_page | incremental_bl4 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | incremental_bl8 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | incremental_bl16 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.1 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.2 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 379 / 387 | 389 / 389 | +2.7 / +0.6 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 251 / 328 | 275 / 309 | +9.6 / -5.9 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 171 / 240 | 184 / 240 | +7.4 / -0.2 % | 15 % | IN |
| close_page | mixed_bl8 | 56 / 56 (union 111) | 58 / 75 (union 116) | +4.3 % (union) | 15 % | IN |
| close_page | row_thrash_bl8 | 246 / 251 | 249 / 271 | +1.5 / +7.8 % | 15 % | IN |
| close_page | random_bl8 | 204 / 234 | 217 / 244 | +6.4 / +4.7 % | 15 % | IN |

55 cells in tolerance, 2 out. Largest deltas: bank_interleave col_major_interleaved_bl4 (11.3 %), bank_interleave col_major_bl4 (10.9 %), close_page col_major_interleaved_bl8 (9.6 %), defaults mixed_bl8 (8.0 %), close_page row_thrash_bl8 (7.8 %), close_page col_major_interleaved_bl16 (7.4 %).
