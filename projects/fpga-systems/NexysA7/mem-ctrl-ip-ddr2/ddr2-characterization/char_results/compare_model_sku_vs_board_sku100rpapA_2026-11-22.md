# The SKU model beside the board: granite sku100rpapA_2026-11-22

Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);
delta = (model - board) / board per direction, and the cell is IN when both directions land within
the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).
A cell with several board runs (`--board-also`) is read BY MODE: runs within the tolerance of each
other are one mode (`xN` = runs in it), every board mode needs a model run within tolerance (several
`--model` CSVs are the model's GO phases, labelled by their `GO offset`), and a model run in a mode
the board never showed is OUT; the delta column then carries one delta per board mode.

| board preset | scenario | board wr / rd | model wr / rd | delta wr / rd | tol | verdict |
|---|---|---|---|---|---|---|
| defaults | incremental_bl4 | 776 / 777 | 780 / 783 | +0.4 / +0.7 % | 2 % | IN |
| defaults | incremental_bl8 | 776 / 777 | 780 / 783 | +0.4 / +0.7 % | 2 % | IN |
| defaults | incremental_bl16 | 777 / 777 | 779 / 783 | +0.4 / +0.7 % | 2 % | IN |
| defaults | row_major_bl4 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| defaults | row_major_bl8 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| defaults | row_major_bl16 | 777 / 779 | 779 / 783 | +0.3 / +0.4 % | 2 % | IN |
| defaults | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_bl8 | 446 / 520 | 448 / 521 | +0.5 / +0.3 % | 5 % | IN |
| defaults | col_major_bl16 | 565 / 623 | 568 / 627 | +0.5 / +0.6 % | 5 % | IN |
| defaults | col_major_interleaved_bl4 | 768 / 766 | 775 / 775 | +0.9 / +1.2 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 770 / 770 | 777 / 779 | +0.8 / +1.2 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 776 / 774 | 779 / 779 | +0.5 / +0.7 % | 3 % | IN |
| defaults | mixed_bl8 | 277 / 276 (union 553) x3 | 310 / 571 (union 619); 309 / 560 (union 618) [GO 480] | +11.8 % (union, by mode) | 10 % | OUT |
| defaults | row_thrash_bl8 | 770 / 772 x3 | 777 / 779 | +0.8 / +1.0 % (by mode) | 3 % | IN |
| defaults | random_bl8 | 729 / 754 x3 | 733 / 751 | +0.5 / -0.4 % (by mode) | 5 % | IN |
| open_page | incremental_bl4 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 777 / 779 | 779 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 777 / 779 | 779 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 446 / 520 | 448 / 521 | +0.5 / +0.3 % | 5 % | IN |
| open_page | col_major_bl16 | 565 / 623 | 568 / 627 | +0.5 / +0.6 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 773 / 770 | 780 / 780 | +0.9 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 774 / 774 | 780 / 781 | +0.7 / +0.9 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 776 / 777 | 779 / 782 | +0.5 / +0.6 % | 3 % | IN |
| open_page | mixed_bl8 | 280 / 280 (union 559) x3 | 308 / 521 (union 617); 309 / 525 (union 617) [GO 480] | +10.2 % (union, by mode) | 10 % | OUT |
| open_page | row_thrash_bl8 | 774 / 774 x3 | 779 / 781 | +0.7 / +0.9 % (by mode) | 3 % | IN |
| open_page | random_bl8 | 736 / 761 x3 | 739 / 758 | +0.4 / -0.4 % (by mode) | 5 % | IN |
| bank_interleave | incremental_bl4 | 518 / 582 | 585 / 585 | +12.8 / +0.4 % | 10 % | OUT |
| bank_interleave | incremental_bl8 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 519 / 582 | 585 / 585 | +12.7 / +0.4 % | 10 % | OUT |
| bank_interleave | row_major_bl8 | 582 / 566 | 585 / 585 | +0.5 / +3.4 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | col_major_bl4 | 442 / 516 | 446 / 520 | +0.8 / +0.7 % | 10 % | IN |
| bank_interleave | col_major_bl8 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 356 / 361 | 355 / 402 | -0.1 / +11.5 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 583 / 583 | 585 / 585 | +0.4 / +0.3 % | 10 % | IN |
| close_page | incremental_bl4 | 92 / 93 | 93 / 105 | +0.1 / +12.9 % | 15 % | IN |
| close_page | incremental_bl8 | 92 / 93 | 93 / 105 | +0.1 / +12.9 % | 15 % | IN |
| close_page | incremental_bl16 | 92 / 93 | 93 / 105 | +0.1 / +12.9 % | 15 % | IN |
| close_page | row_major_bl4 | 87 / 87 | 87 / 97 | +0.1 / +11.9 % | 15 % | IN |
| close_page | row_major_bl8 | 87 / 87 | 87 / 97 | +0.1 / +11.9 % | 15 % | IN |
| close_page | row_major_bl16 | 87 / 87 | 87 / 97 | +0.1 / +11.9 % | 15 % | IN |
| close_page | col_major_bl4 | 92 / 95 | 92 / 105 | +0.5 / +10.6 % | 15 % | IN |
| close_page | col_major_bl8 | 89 / 91 | 90 / 101 | +0.5 / +11.5 % | 15 % | IN |
| close_page | col_major_bl16 | 88 / 89 | 89 / 100 | +0.3 / +12.2 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 534 / 574 | 550 / 582 | +3.0 / +1.3 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 344 / 400 | 349 / 416 | +1.3 / +3.8 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 232 / 246 | 232 / 267 | +0.1 / +8.5 % | 15 % | IN |
| close_page | mixed_bl8 | 73 / 121 (union 146) x3 | 73 / 121 (union 146) | +0.2 % (union, by mode) | 15 % | IN |
| close_page | row_thrash_bl8 | 344 / 354 x3 | 349 / 395 | +1.3 / +11.5 % (by mode) | 15 % | IN |
| close_page | random_bl8 | 270 / 283 x3 | 272 / 311 | +1.0 / +10.0 % (by mode) | 15 % | IN |

52 cells in tolerance, 5 out. Largest deltas: close_page incremental_bl8 (12.9 %), close_page incremental_bl16 (12.9 %), close_page incremental_bl4 (12.9 %), bank_interleave incremental_bl4 (12.8 %), bank_interleave row_major_bl4 (12.7 %), close_page col_major_bl16 (12.2 %).
