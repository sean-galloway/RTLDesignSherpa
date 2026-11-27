# The SKU model beside the board: granite sku100rpap_2026-11-22

Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);
delta = (model - board) / board per direction, and the cell is IN when both directions land within
the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).
A cell with several board runs (`--board-also`) is read BY MODE: runs within the tolerance of each
other are one mode (`xN` = runs in it), every board mode needs a model run within tolerance (several
`--model` CSVs are the model's GO phases, labelled by their `GO offset`), and a model run in a mode
the board never showed is OUT; the delta column then carries one delta per board mode.

| board preset | scenario | board wr / rd | model wr / rd | delta wr / rd | tol | verdict |
|---|---|---|---|---|---|---|
| defaults | incremental_bl4 | 776 / 777 | 776 / 777 | -0.0 / +0.0 % | 2 % | IN |
| defaults | incremental_bl8 | 777 / 777 | 776 / 777 | -0.0 / +0.0 % | 2 % | IN |
| defaults | incremental_bl16 | 777 / 777 | 776 / 777 | -0.0 / +0.0 % | 2 % | IN |
| defaults | row_major_bl4 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| defaults | row_major_bl8 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| defaults | row_major_bl16 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| defaults | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_bl8 | 446 / 520 | 444 / 521 | -0.3 / +0.3 % | 5 % | IN |
| defaults | col_major_bl16 | 565 / 623 | 566 / 624 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_interleaved_bl4 | 768 / 766 | 769 / 767 | +0.1 / +0.1 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 770 / 770 | 771 / 771 | +0.1 / +0.1 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 776 / 774 | 775 / 775 | -0.0 / +0.0 % | 3 % | IN |
| defaults | mixed_bl8 | 277 / 276 (union 553) x3 | 280 / 280 (union 560) | +1.3 % (union, by mode) | 10 % | IN |
| defaults | row_thrash_bl8 | 770 / 770 x3 | 771 / 771 | +0.1 / +0.1 % (by mode) | 3 % | IN |
| defaults | random_bl8 | 729 / 754 x3 | 728 / 745 | -0.2 / -1.3 % (by mode) | 5 % | IN |
| open_page | incremental_bl4 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| open_page | incremental_bl8 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| open_page | incremental_bl16 | 777 / 779 | 776 / 779 | -0.1 / -0.0 % | 2 % | IN |
| open_page | row_major_bl4 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| open_page | row_major_bl8 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| open_page | row_major_bl16 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| open_page | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 446 / 520 | 444 / 521 | -0.3 / +0.3 % | 5 % | IN |
| open_page | col_major_bl16 | 565 / 623 | 566 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 773 / 770 | 771 / 771 | -0.2 / +0.1 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 774 / 774 | 775 / 774 | +0.0 / -0.0 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 776 / 777 | 775 / 777 | -0.0 / -0.0 % | 3 % | IN |
| open_page | mixed_bl8 | 280 / 280 (union 559) x3 | 302 / 579 (union 604) | +8.0 % (union, by mode) | 10 % | IN |
| open_page | row_thrash_bl8 | 774 / 774 x3 | 775 / 774 | +0.0 / -0.0 % (by mode) | 3 % | IN |
| open_page | random_bl8 | 736 / 761 x3 | 735 / 753 | -0.2 / -1.1 % (by mode) | 5 % | IN |
| bank_interleave | incremental_bl4 | 583 / 566 | 532 / 575 | -8.7 / +1.7 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 582 / 583 | 524 / 573 | -9.9 / -1.7 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 583 / 583 | 521 / 573 | -10.7 / -1.7 % | 10 % | OUT |
| bank_interleave | row_major_bl4 | 580 / 583 | 518 / 569 | -10.7 / -2.4 % | 10 % | OUT |
| bank_interleave | row_major_bl8 | 582 / 566 | 517 / 569 | -11.2 / +0.6 % | 10 % | OUT |
| bank_interleave | row_major_bl16 | 583 / 566 | 517 / 569 | -11.3 / +0.5 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 445 / 516 | 443 / 517 | -0.3 / +0.1 % | 10 % | IN |
| bank_interleave | col_major_bl8 | 582 / 583 | 526 / 582 | -9.7 / -0.2 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 583 / 583 | 581 / 580 | -0.4 / -0.5 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 356 / 361 | 354 / 361 | -0.3 / +0.1 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl8 | 583 / 583 | 574 / 552 | -1.5 / -5.2 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 583 / 565 | 581 / 547 | -0.3 / -3.3 % | 10 % | IN |
| close_page | incremental_bl4 | 92 / 93 | 92 / 93 | -0.0 / -0.2 % | 15 % | IN |
| close_page | incremental_bl8 | 92 / 93 | 92 / 93 | -0.0 / -0.2 % | 15 % | IN |
| close_page | incremental_bl16 | 92 / 93 | 92 / 93 | -0.1 / -0.0 % | 15 % | IN |
| close_page | row_major_bl4 | 87 / 87 | 87 / 87 | -0.0 / -0.0 % | 15 % | IN |
| close_page | row_major_bl8 | 87 / 87 | 87 / 87 | -0.0 / -0.0 % | 15 % | IN |
| close_page | row_major_bl16 | 87 / 87 | 87 / 87 | -0.0 / -0.0 % | 15 % | IN |
| close_page | col_major_bl4 | 92 / 95 | 92 / 95 | +0.3 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 89 / 91 | 90 / 91 | +0.2 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 88 / 89 | 88 / 89 | -0.0 / -0.0 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 534 / 574 | 560 / 585 | +4.9 / +1.9 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 344 / 402 | 345 / 388 | +0.1 / -3.3 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 232 / 246 | 230 / 240 | -0.7 / -2.3 % | 15 % | IN |
| close_page | mixed_bl8 | 73 / 121 (union 146) x3 | 73 / 122 (union 146) | +0.2 % (union, by mode) | 15 % | IN |
| close_page | row_thrash_bl8 | 344 / 354 x3 | 345 / 354 | +0.3 / -0.1 % (by mode) | 15 % | IN |
| close_page | random_bl8 | 270 / 283 x3 | 271 / 281 | +0.6 / -0.5 % (by mode) | 15 % | IN |

53 cells in tolerance, 4 out. Largest deltas: bank_interleave row_major_bl16 (11.3 %), bank_interleave row_major_bl8 (11.2 %), bank_interleave row_major_bl4 (10.7 %), bank_interleave incremental_bl16 (10.7 %), bank_interleave incremental_bl8 (9.9 %), bank_interleave col_major_bl8 (9.7 %).
