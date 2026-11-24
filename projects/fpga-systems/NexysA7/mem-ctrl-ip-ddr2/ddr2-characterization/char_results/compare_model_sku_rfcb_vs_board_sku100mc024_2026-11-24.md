# The SKU model beside the board: granite sku100mc024_2026-11-24

Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);
delta = (model - board) / board per direction, and the cell is IN when both directions land within
the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).
A cell with several board runs (`--board-also`) is read BY MODE: runs within the tolerance of each
other are one mode (`xN` = runs in it), every board mode needs a model run within tolerance (several
`--model` CSVs are the model's GO phases, labelled by their `GO offset`), and a model run in a mode
the board never showed is OUT; the delta column then carries one delta per board mode.

| board preset | scenario | board wr / rd | model wr / rd | delta wr / rd | tol | verdict |
|---|---|---|---|---|---|---|
| defaults | incremental_bl4 | 776 / 777 | 776 / 780 | -0.0 / +0.3 % | 2 % | IN |
| defaults | incremental_bl8 | 777 / 777 | 776 / 780 | -0.0 / +0.3 % | 2 % | IN |
| defaults | incremental_bl16 | 777 / 777 | 776 / 779 | -0.0 / +0.3 % | 2 % | IN |
| defaults | row_major_bl4 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| defaults | row_major_bl8 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| defaults | row_major_bl16 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| defaults | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_bl8 | 446 / 520 | 444 / 521 | -0.3 / +0.3 % | 5 % | IN |
| defaults | col_major_bl16 | 565 / 623 | 566 / 624 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_interleaved_bl4 | 768 / 766 | 773 / 771 | +0.6 / +0.7 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 770 / 770 | 774 / 775 | +0.5 / +0.7 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 776 / 774 | 776 / 777 | +0.1 / +0.3 % | 3 % | IN |
| defaults | mixed_bl8 | 277 / 276 (union 553) x3 | 278 / 278 (union 555) | +0.5 % (union, by mode) | 10 % | IN |
| defaults | row_thrash_bl8 | 770 / 772 x3 | 774 / 775 | +0.5 / +0.4 % (by mode) | 3 % | IN |
| defaults | random_bl8 | 729 / 754 x3 | 730 / 748 | +0.1 / -0.8 % (by mode) | 5 % | IN |
| open_page | incremental_bl4 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| open_page | incremental_bl8 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| open_page | incremental_bl16 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| open_page | row_major_bl4 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| open_page | row_major_bl8 | 777 / 779 | 776 / 780 | -0.1 / +0.0 % | 2 % | IN |
| open_page | row_major_bl16 | 777 / 779 | 776 / 779 | -0.1 / +0.0 % | 2 % | IN |
| open_page | col_major_bl4 | 311 / 389 | 312 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 446 / 520 | 444 / 521 | -0.3 / +0.3 % | 5 % | IN |
| open_page | col_major_bl16 | 565 / 623 | 566 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 773 / 770 | 775 / 775 | +0.4 / +0.7 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 774 / 774 | 776 / 780 | +0.2 / +0.7 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 776 / 777 | 776 / 779 | +0.1 / +0.3 % | 3 % | IN |
| open_page | mixed_bl8 | 280 / 280 (union 559) x3 | 291 / 366 (union 581) | +3.9 % (union, by mode) | 10 % | IN |
| open_page | row_thrash_bl8 | 774 / 774 x3 | 776 / 779 | +0.2 / +0.7 % (by mode) | 3 % | IN |
| open_page | random_bl8 | 736 / 761 x3 | 737 / 755 | +0.0 / -0.8 % (by mode) | 5 % | IN |
| bank_interleave | incremental_bl4 | 581 / 582 | 576 / 580 | -0.7 / -0.3 % | 10 % | IN |
| bank_interleave | incremental_bl8 | 583 / 583 | 579 / 581 | -0.7 / -0.3 % | 10 % | IN |
| bank_interleave | incremental_bl16 | 582 / 583 | 580 / 581 | -0.4 / -0.3 % | 10 % | IN |
| bank_interleave | row_major_bl4 | 581 / 583 | 581 / 579 | -0.0 / -0.6 % | 10 % | IN |
| bank_interleave | row_major_bl8 | 582 / 583 | 582 / 579 | -0.0 / -0.7 % | 10 % | IN |
| bank_interleave | row_major_bl16 | 517 / 583 | 582 / 578 | +12.6 / -0.8 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 442 / 518 | 443 / 517 | +0.1 / -0.3 % | 10 % | IN |
| bank_interleave | col_major_bl8 | 583 / 583 | 582 / 582 | -0.1 / -0.2 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 583 / 583 | 591 / 582 | +1.4 / -0.2 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl4 | 356 / 361 | 354 / 394 | -0.3 / +9.4 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl8 | 583 / 583 | 580 / 582 | -0.6 / -0.2 % | 10 % | IN |
| bank_interleave | col_major_interleaved_bl16 | 583 / 583 | 581 / 581 | -0.3 / -0.3 % | 10 % | IN |
| close_page | incremental_bl4 | 92 / 93 | 92 / 104 | -0.0 / +12.4 % | 15 % | IN |
| close_page | incremental_bl8 | 92 / 93 | 92 / 104 | -0.0 / +12.4 % | 15 % | IN |
| close_page | incremental_bl16 | 92 / 93 | 92 / 104 | -0.0 / +12.4 % | 15 % | IN |
| close_page | row_major_bl4 | 87 / 87 | 87 / 98 | -0.0 / +12.5 % | 15 % | IN |
| close_page | row_major_bl8 | 87 / 87 | 87 / 98 | -0.0 / +12.5 % | 15 % | IN |
| close_page | row_major_bl16 | 87 / 87 | 87 / 98 | -0.0 / +12.5 % | 15 % | IN |
| close_page | col_major_bl4 | 92 / 95 | 92 / 105 | +0.3 / +10.3 % | 15 % | IN |
| close_page | col_major_bl8 | 89 / 91 | 90 / 101 | +0.2 / +11.3 % | 15 % | IN |
| close_page | col_major_bl16 | 88 / 89 | 88 / 100 | -0.0 / +11.7 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 534 / 574 | 539 / 579 | +0.9 / +0.9 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 344 / 400 | 345 / 415 | +0.1 / +3.6 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 232 / 246 | 230 / 266 | -1.1 / +8.1 % | 15 % | IN |
| close_page | mixed_bl8 | 73 / 121 (union 146) x3 | 73 / 121 (union 146) | -0.2 % (union, by mode) | 15 % | IN |
| close_page | row_thrash_bl8 | 344 / 354 x3 | 345 / 390 | +0.1 / +10.1 % (by mode) | 15 % | IN |
| close_page | random_bl8 | 270 / 283 x3 | 271 / 310 | +0.6 / +9.6 % (by mode) | 15 % | IN |

56 cells in tolerance, 1 out. Largest deltas: bank_interleave row_major_bl16 (12.6 %), close_page row_major_bl8 (12.5 %), close_page row_major_bl4 (12.5 %), close_page row_major_bl16 (12.5 %), close_page incremental_bl8 (12.4 %), close_page incremental_bl16 (12.4 %).
