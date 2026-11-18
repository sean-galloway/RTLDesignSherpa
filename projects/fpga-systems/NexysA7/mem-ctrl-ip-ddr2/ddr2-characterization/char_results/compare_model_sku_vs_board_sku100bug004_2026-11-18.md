# The SKU model beside the board: granite sku100bug004_2026-11-18

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
| defaults | col_major_interleaved_bl8 | 768 / 767 | 777 / 780 | +1.2 / +1.6 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 777 / 779 | +0.6 / +1.2 % | 3 % | IN |
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
| open_page | col_major_interleaved_bl8 | 770 / 770 | 777 / 780 | +0.8 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 777 / 779 | +0.6 / +0.8 % | 3 % | IN |
| bank_interleave | incremental_bl4 | 387 / 387 | 388 / 388 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 387 / 386 | 388 / 388 | +0.3 / +0.5 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 387 / 386 | 377 / 377 | -2.7 / -2.4 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 387 / 387 | 389 / 389 | +0.4 / +0.5 % | 10 % | IN |
| bank_interleave | row_major_bl8 | 387 / 387 | 389 / 389 | +0.4 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 387 / 387 | 389 / 389 | +0.4 / +0.5 % | 10 % | IN |
| bank_interleave | col_major_bl4 | 258 / 351 | 333 / 333 | +29.1 / -5.0 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 387 / 387 | 333 / 333 | -13.9 / -13.9 % | 10 % | OUT |
| bank_interleave | col_major_bl16 | 387 / 387 | 356 / 356 | -8.2 / -8.1 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 242 / 254 | 246 / 279 | +1.9 / +9.9 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl8 | 387 / 387 | 371 / 371 | -4.1 / -4.1 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 387 / 387 | 347 / 347 | -10.3 / -10.3 % | 10 % | OUT |
| close_page | incremental_bl4 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | incremental_bl8 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | incremental_bl16 | 82 / 92 | 83 / 93 | +1.5 / +0.3 % | 15 % | IN |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.1 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.2 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 379 / 387 | 370 / 370 | -2.3 / -4.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 251 / 328 | 287 / 320 | +14.5 / -2.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 171 / 240 | 184 / 217 | +7.5 / -9.7 % | 15 % | IN |

45 cells in tolerance, 3 out. Largest deltas: bank_interleave col_major_bl4 (29.1 %), close_page col_major_interleaved_bl8 (14.5 %), bank_interleave col_major_bl8 (13.9 %), bank_interleave col_major_interleaved_bl16 (10.3 %), bank_interleave col_major_interleaved_bl4 (9.9 %), close_page col_major_interleaved_bl16 (9.7 %).
