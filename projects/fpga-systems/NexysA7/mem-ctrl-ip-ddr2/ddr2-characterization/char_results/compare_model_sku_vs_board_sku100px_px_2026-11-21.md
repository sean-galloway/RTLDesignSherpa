# The SKU model beside the board: granite sku100px_2026-11-21

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
| defaults | col_major_bl8 | 446 / 520 | 448 / 521 | +0.5 / +0.1 % | 5 % | IN |
| defaults | col_major_bl16 | 565 / 623 | 568 / 627 | +0.5 / +0.6 % | 5 % | IN |
| defaults | col_major_interleaved_bl4 | 768 / 766 | 775 / 775 | +0.9 / +1.2 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 770 / 770 | 777 / 779 | +0.8 / +1.2 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 776 / 774 | 779 / 779 | +0.5 / +0.7 % | 3 % | IN |
| defaults | mixed_bl8 | 277 / 276 (union 553) | 310 / 571 (union 619) | +12.0 % (union) | 10 % | OUT |
| defaults | row_thrash_bl8 | 770 / 772 | 777 / 779 | +0.8 / +1.0 % | 3 % | IN |
| defaults | random_bl8 | 729 / 754 | 733 / 751 | +0.5 / -0.4 % | 5 % | IN |
| open_page | incremental_bl4 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 777 / 779 | 779 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 777 / 779 | 780 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 777 / 779 | 779 / 783 | +0.3 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 446 / 520 | 448 / 521 | +0.5 / +0.1 % | 5 % | IN |
| open_page | col_major_bl16 | 565 / 623 | 568 / 627 | +0.5 / +0.6 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 773 / 770 | 780 / 780 | +0.9 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 774 / 774 | 780 / 781 | +0.7 / +0.9 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 776 / 777 | 779 / 782 | +0.5 / +0.6 % | 3 % | IN |
| open_page | mixed_bl8 | 280 / 280 (union 559) x1 | 308 / 521 (union 617); 309 / 525 (union 617) [GO 480] | +10.2 % (union, by mode) | 10 % | OUT |
| open_page | row_thrash_bl8 | 774 / 774 | 779 / 781 | +0.7 / +0.9 % | 3 % | IN |
| open_page | random_bl8 | 736 / 761 | 739 / 758 | +0.4 / -0.4 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 582 / 583 | 585 / 585 | +0.5 / +0.3 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 582 / 566 | 585 / 585 | +0.5 / +3.4 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 583 / 565 | 585 / 585 | +0.3 / +3.4 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 583 / 582 | 585 / 585 | +0.3 / +0.4 % | 10 % | IN |
| bank_interleave | row_major_bl8 | 583 / 566 | 585 / 585 | +0.3 / +3.3 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 521 / 583 | 585 / 585 | +12.2 / +0.3 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 442 / 442 | 446 / 520 | +0.8 / +17.5 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 577 / 583 | 585 / 585 | +1.3 / +0.3 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 356 / 356 | 355 / 402 | -0.1 / +13.1 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 583 / 566 | 585 / 585 | +0.3 / +3.4 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 583 / 583 | 585 / 585 | +0.3 / +0.3 % | 10 % | IN |
| close_page | incremental_bl4 | 92 / 93 | 93 / 105 | +0.1 / +12.9 % | 15 % | IN |
| close_page | incremental_bl8 | 92 / 93 | 93 / 105 | +0.1 / +13.0 % | 15 % | IN |
| close_page | incremental_bl16 | 92 / 93 | 93 / 105 | +0.1 / +12.9 % | 15 % | IN |
| close_page | row_major_bl4 | 87 / 87 | 87 / 97 | +0.1 / +11.9 % | 15 % | IN |
| close_page | row_major_bl8 | 87 / 87 | 87 / 97 | +0.1 / +11.9 % | 15 % | IN |
| close_page | row_major_bl16 | 87 / 87 | 87 / 97 | +0.1 / +11.9 % | 15 % | IN |
| close_page | col_major_bl4 | 92 / 92 | 92 / 105 | +0.5 / +14.0 % | 15 % | IN |
| close_page | col_major_bl8 | 89 / 89 | 90 / 101 | +0.5 / +13.2 % | 15 % | IN |
| close_page | col_major_bl16 | 88 / 88 | 89 / 100 | +0.3 / +13.2 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 534 / 574 | 550 / 582 | +3.0 / +1.3 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 344 / 402 | 349 / 416 | +1.3 / +3.5 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 232 / 246 | 232 / 267 | +0.1 / +8.5 % | 15 % | IN |
| close_page | mixed_bl8 | 60 / 66 (union 120) | 73 / 121 (union 146) | +21.5 % (union) | 15 % | OUT |
| close_page | row_thrash_bl8 | 344 / 351 | 349 / 395 | +1.3 / +12.3 % | 15 % | IN |
| close_page | random_bl8 | 270 / 281 | 272 / 311 | +1.0 / +10.7 % | 15 % | IN |

51 cells in tolerance, 6 out. Largest deltas: close_page mixed_bl8 (21.5 %), bank_interleave col_major_bl4 (17.5 %), close_page col_major_bl4 (14.0 %), close_page col_major_bl8 (13.2 %), close_page col_major_bl16 (13.2 %), bank_interleave col_major_interleaved_bl4 (13.1 %).
