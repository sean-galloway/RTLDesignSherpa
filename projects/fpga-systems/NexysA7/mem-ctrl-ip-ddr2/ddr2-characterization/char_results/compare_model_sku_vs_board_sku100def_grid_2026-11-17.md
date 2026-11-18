# The SKU model beside the board: granite sku100def_2026-11-16

Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);
delta = (model - board) / board per direction, and the cell is IN when both directions land within
the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).

| board preset | scenario | board wr / rd | model wr / rd | delta wr / rd | tol | verdict |
|---|---|---|---|---|---|---|
| defaults | incremental_bl4 | 775 / 776 | 778 / 782 | +0.4 / +0.7 % | 2 % | IN |
| defaults | incremental_bl8 | 775 / 776 | 778 / 782 | +0.4 / +0.7 % | 2 % | IN |
| defaults | incremental_bl16 | 775 / 776 | 778 / 782 | +0.4 / +0.7 % | 2 % | IN |
| defaults | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| defaults | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| defaults | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| defaults | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| defaults | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| defaults | col_major_interleaved_bl4 | 765 / 763 | 777 / 780 | +1.6 / +2.1 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 768 / 768 | 778 / 780 | +1.3 / +1.5 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 778 / 780 | +0.7 / +1.2 % | 3 % | IN |
| defaults | mixed_bl8 | 272 / 272 (union 543) | 286 / 286 (union 573) | +5.5 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 770 / 770 | 778 / 779 | +1.0 / +1.2 % | 3 % | IN |
| defaults | random_bl8 | 718 / 740 | 749 / 767 | +4.3 / +3.6 % | 5 % | IN |
| open_page | incremental_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| open_page | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 768 / 768 | 777 / 780 | +1.1 / +1.5 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 770 / 770 | 778 / 780 | +1.0 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 778 / 780 | +0.7 / +0.8 % | 3 % | IN |
| open_page | mixed_bl8 | 272 / 272 (union 545) | 286 / 286 (union 573) | +5.2 % (union) | 10 % | IN |
| open_page | row_thrash_bl8 | 770 / 770 | 778 / 779 | +1.0 / +1.2 % | 3 % | IN |
| open_page | random_bl8 | 726 / 746 | 749 / 767 | +3.2 / +2.8 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 238 / 233 | 389 / 389 | +63.3 / +66.6 % | 10 % | OUT |
| bank_interleave | incremental_bl8 | 234 / 233 | 389 / 389 | +66.4 / +67.0 % | 10 % | OUT |
| bank_interleave | incremental_bl16 | 238 / 233 | 389 / 389 | +63.4 / +66.7 % | 10 % | OUT |
| bank_interleave | row_major_bl4 | 238 / 233 | 389 / 389 | +63.4 / +67.1 % | 10 % | OUT |
| bank_interleave | row_major_bl8 | 238 / 232 | 389 / 389 | +63.3 / +67.5 % | 10 % | OUT |
| bank_interleave | row_major_bl16 | 238 / 232 | 389 / 389 | +63.3 / +67.5 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 195 / 239 | 389 / 389 | +99.7 / +62.4 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 237 / 235 | 389 / 389 | +63.9 / +65.2 % | 10 % | OUT |
| bank_interleave | col_major_bl16 | 238 / 234 | 389 / 389 | +63.3 / +66.3 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl4 | 195 / 222 | 389 / 389 | +99.7 / +75.1 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 238 / 234 | 389 / 389 | +63.4 / +66.2 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl16 | 238 / 235 | 389 / 389 | +63.4 / +65.7 % | 10 % | OUT |
| close_page | incremental_bl4 | 82 / 92 | 104 / 119 | +26.8 / +28.9 % | 15 % | OUT |
| close_page | incremental_bl8 | 82 / 92 | 104 / 119 | +26.8 / +28.9 % | 15 % | OUT |
| close_page | incremental_bl16 | 82 / 92 | 104 / 119 | +26.8 / +28.9 % | 15 % | OUT |
| close_page | row_major_bl4 | 78 / 87 | 98 / 112 | +24.9 / +28.6 % | 15 % | OUT |
| close_page | row_major_bl8 | 78 / 87 | 98 / 112 | +24.9 / +28.6 % | 15 % | OUT |
| close_page | row_major_bl16 | 78 / 87 | 98 / 112 | +24.9 / +28.6 % | 15 % | OUT |
| close_page | col_major_bl4 | 82 / 92 | 98 / 112 | +18.7 / +21.4 % | 15 % | OUT |
| close_page | col_major_bl8 | 80 / 90 | 98 / 112 | +21.8 / +24.9 % | 15 % | OUT |
| close_page | col_major_bl16 | 79 / 88 | 98 / 112 | +23.5 / +27.1 % | 15 % | OUT |
| close_page | col_major_interleaved_bl4 | 235 / 232 | 389 / 389 | +65.3 / +67.7 % | 15 % | OUT |
| close_page | col_major_interleaved_bl8 | 213 / 219 | 389 / 389 | +82.5 / +77.9 % | 15 % | OUT |
| close_page | col_major_interleaved_bl16 | 180 / 240 | 271 / 290 | +50.5 / +20.6 % | 15 % | OUT |
| close_page | mixed_bl8 | 73 / 152 (union 145) | 66 / 66 (union 133) | -8.6 % (union) | 15 % | IN |
| close_page | row_thrash_bl8 | 208 / 197 | 377 / 389 | +81.8 / +97.6 % | 15 % | OUT |
| close_page | random_bl8 | 188 / 207 | 303 / 315 | +61.0 / +52.7 % | 15 % | OUT |

31 cells in tolerance, 26 out. Largest deltas: bank_interleave col_major_interleaved_bl4 (99.7 %), bank_interleave col_major_bl4 (99.7 %), close_page row_thrash_bl8 (97.6 %), close_page col_major_interleaved_bl8 (82.5 %), close_page col_major_interleaved_bl4 (67.7 %), bank_interleave row_major_bl16 (67.5 %).
