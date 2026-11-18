# The SKU model beside the board: granite sku100def_2026-11-16

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
| defaults | col_major_interleaved_bl4 | 765 / 763 | 775 / 775 | +1.4 / +1.6 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 768 / 768 | 777 / 780 | +1.1 / +1.5 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 777 / 779 | +0.6 / +1.2 % | 3 % | IN |
| defaults | mixed_bl8 | 272 / 272 (union 543) | 284 / 284 (union 569) | +4.7 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 770 / 770 | 777 / 779 | +0.8 / +1.2 % | 3 % | IN |
| defaults | random_bl8 | 718 / 740 | 734 / 749 | +2.1 / +1.2 % | 5 % | IN |
| open_page | incremental_bl4 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| open_page | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 768 / 768 | 775 / 775 | +0.9 / +1.0 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 770 / 770 | 777 / 780 | +0.8 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 777 / 779 | +0.6 / +0.8 % | 3 % | IN |
| open_page | mixed_bl8 | 272 / 272 (union 545) | 284 / 284 (union 569) | +4.5 % (union) | 10 % | IN |
| open_page | row_thrash_bl8 | 770 / 770 | 777 / 779 | +0.8 / +1.2 % | 3 % | IN |
| open_page | random_bl8 | 726 / 746 | 734 / 749 | +1.1 / +0.3 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 238 / 233 | 388 / 388 | +63.1 / +66.4 % | 10 % | OUT |
| bank_interleave | incremental_bl8 | 234 / 233 | 388 / 388 | +66.2 / +66.8 % | 10 % | OUT |
| bank_interleave | incremental_bl16 | 238 / 233 | 377 / 377 | +58.2 / +61.5 % | 10 % | OUT |
| bank_interleave | row_major_bl4 | 238 / 233 | 389 / 389 | +63.4 / +67.1 % | 10 % | OUT |
| bank_interleave | row_major_bl8 | 238 / 232 | 389 / 389 | +63.3 / +67.5 % | 10 % | OUT |
| bank_interleave | row_major_bl16 | 238 / 232 | 389 / 389 | +63.3 / +67.5 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 195 / 239 | 333 / 333 | +71.3 / +39.2 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 237 / 235 | 333 / 333 | +40.6 / +41.6 % | 10 % | OUT |
| bank_interleave | col_major_bl16 | 238 / 234 | 356 / 356 | +49.4 / +52.1 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl4 | 195 / 222 | 246 / 279 | +26.6 / +25.7 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 238 / 234 | 371 / 371 | +56.1 / +58.8 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl16 | 238 / 235 | 347 / 347 | +45.9 / +48.0 % | 10 % | OUT |
| close_page | incremental_bl4 | 82 / 92 | 83 / 93 | +1.6 / +0.3 % | 15 % | IN |
| close_page | incremental_bl8 | 82 / 92 | 83 / 93 | +1.6 / +0.3 % | 15 % | IN |
| close_page | incremental_bl16 | 82 / 92 | 83 / 93 | +1.6 / +0.3 % | 15 % | IN |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.1 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.2 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 235 / 232 | 370 / 370 | +57.5 / +59.7 % | 15 % | OUT |
| close_page | col_major_interleaved_bl8 | 213 / 219 | 287 / 320 | +34.8 / +46.4 % | 15 % | OUT |
| close_page | col_major_interleaved_bl16 | 180 / 240 | 184 / 217 | +2.2 / -9.7 % | 15 % | IN |
| close_page | mixed_bl8 | 73 / 152 (union 145) | 54 / 54 (union 107) | -26.2 % (union) | 15 % | OUT |
| close_page | row_thrash_bl8 | 208 / 197 | 250 / 275 | +20.6 / +39.7 % | 15 % | OUT |
| close_page | random_bl8 | 188 / 207 | 217 / 240 | +15.3 / +16.0 % | 15 % | OUT |

40 cells in tolerance, 17 out. Largest deltas: bank_interleave col_major_bl4 (71.3 %), bank_interleave row_major_bl16 (67.5 %), bank_interleave row_major_bl8 (67.5 %), bank_interleave row_major_bl4 (67.1 %), bank_interleave incremental_bl8 (66.8 %), bank_interleave incremental_bl4 (66.4 %).
