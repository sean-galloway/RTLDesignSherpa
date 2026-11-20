# The SKU model beside the board: granite sku100s4_2026-11-19

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
| defaults | col_major_interleaved_bl4 | 765 / 762 | 775 / 775 | +1.4 / +1.8 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 768 / 767 | 775 / 777 | +1.0 / +1.4 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 776 / 779 | +0.5 / +1.2 % | 3 % | IN |
| defaults | mixed_bl8 | 272 / 273 (union 545) | 277 / 277 (union 554) | +1.7 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 768 / 766 | 775 / 777 | +1.0 / +1.5 % | 3 % | IN |
| defaults | random_bl8 | 723 / 750 | 730 / 752 | +1.0 / +0.4 % | 5 % | IN |
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
| open_page | mixed_bl8 | 311 / 522 (union 622) | 277 / 277 (union 554) | -10.9 % (union) | 10 % | OUT |
| open_page | row_thrash_bl8 | 770 / 770 | 775 / 777 | +0.7 / +0.9 % | 3 % | IN |
| open_page | random_bl8 | 728 / 757 | 730 / 752 | +0.2 / -0.6 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl8 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_bl4 | 283 / 388 | 283 / 389 | +0.1 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_bl8 | 388 / 388 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 243 / 317 | 246 / 322 | +1.4 / +1.4 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl8 | 387 / 387 | 389 / 389 | +0.5 / +0.5 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 387 / 387 | 389 / 389 | +0.4 / +0.3 % | 10 % | IN |
| close_page | incremental_bl4 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | incremental_bl8 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | incremental_bl16 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.1 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.2 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 386 / 387 | 388 / 389 | +0.5 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 250 / 361 | 287 / 334 | +14.9 / -7.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 171 / 238 | 208 / 239 | +21.3 / +0.6 % | 15 % | OUT |
| close_page | mixed_bl8 | 56 / 59 (union 112) | 58 / 75 (union 117) | +3.6 % (union) | 15 % | IN |
| close_page | row_thrash_bl8 | 238 / 314 | 249 / 316 | +4.7 / +0.6 % | 15 % | IN |
| close_page | random_bl8 | 203 / 258 | 218 / 258 | +7.5 / -0.1 % | 15 % | IN |

55 cells in tolerance, 2 out. Largest deltas: close_page col_major_interleaved_bl16 (21.3 %), close_page col_major_interleaved_bl8 (14.9 %), open_page mixed_bl8 (10.9 %), close_page random_bl8 (7.5 %), close_page row_thrash_bl8 (4.7 %), close_page mixed_bl8 (3.6 %).
