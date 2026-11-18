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
| defaults | col_major_interleaved_bl8 | 768 / 768 | 776 / 780 | +1.1 / +1.5 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 776 / 779 | +0.6 / +1.2 % | 3 % | IN |
| defaults | mixed_bl8 | 272 / 272 (union 543) | 277 / 277 (union 554) | +2.0 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 770 / 770 | 775 / 779 | +0.7 / +1.2 % | 3 % | IN |
| defaults | random_bl8 | 718 / 740 | 733 / 748 | +2.0 / +1.1 % | 5 % | IN |
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
| open_page | col_major_interleaved_bl8 | 770 / 770 | 776 / 780 | +0.8 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 776 / 779 | +0.5 / +0.8 % | 3 % | IN |
| open_page | mixed_bl8 | 272 / 272 (union 545) | 277 / 277 (union 554) | +1.7 % (union) | 10 % | IN |
| open_page | row_thrash_bl8 | 770 / 770 | 775 / 779 | +0.7 / +1.2 % | 3 % | IN |
| open_page | random_bl8 | 726 / 746 | 733 / 748 | +1.0 / +0.3 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 238 / 233 | 200 / 202 | -15.9 / -13.5 % | 10 % | OUT |
| bank_interleave | incremental_bl8 | 234 / 233 | 199 / 202 | -15.0 / -13.2 % | 10 % | OUT |
| bank_interleave | incremental_bl16 | 238 / 233 | 198 / 201 | -16.9 / -13.8 % | 10 % | OUT |
| bank_interleave | row_major_bl4 | 238 / 233 | 197 / 202 | -17.2 / -13.1 % | 10 % | OUT |
| bank_interleave | row_major_bl8 | 238 / 232 | 197 / 202 | -17.2 / -12.9 % | 10 % | OUT |
| bank_interleave | row_major_bl16 | 238 / 232 | 197 / 202 | -17.3 / -12.9 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 195 / 239 | 240 / 195 | +23.4 / -18.6 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 237 / 235 | 240 / 244 | +1.4 / +3.5 % | 10 % | IN |
| bank_interleave | col_major_bl16 | 238 / 234 | 214 / 217 | -10.1 / -7.3 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl4 | 195 / 222 | 195 / 195 | +0.1 / -12.2 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 238 / 234 | 203 / 202 | -14.8 / -13.6 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl16 | 238 / 235 | 203 / 202 | -14.9 / -13.7 % | 10 % | OUT |
| close_page | incremental_bl4 | 82 / 92 | 83 / 93 | +1.6 / +0.3 % | 15 % | IN |
| close_page | incremental_bl8 | 82 / 92 | 83 / 93 | +1.6 / +0.3 % | 15 % | IN |
| close_page | incremental_bl16 | 82 / 92 | 83 / 93 | +1.6 / +0.3 % | 15 % | IN |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.1 % | 15 % | IN |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.1 / +0.1 % | 15 % | IN |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.2 / +0.4 % | 15 % | IN |
| close_page | col_major_interleaved_bl4 | 235 / 232 | 201 / 200 | -14.7 / -13.7 % | 15 % | IN |
| close_page | col_major_interleaved_bl8 | 213 / 219 | 196 / 197 | -7.9 / -9.9 % | 15 % | IN |
| close_page | col_major_interleaved_bl16 | 180 / 240 | 175 / 176 | -2.7 / -26.9 % | 15 % | OUT |
| close_page | mixed_bl8 | 73 / 152 (union 145) | 72 / 131 (union 143) | -1.3 % (union) | 15 % | IN |
| close_page | row_thrash_bl8 | 208 / 197 | 196 / 194 | -5.6 / -1.2 % | 15 % | IN |
| close_page | random_bl8 | 188 / 207 | 179 / 183 | -4.9 / -11.2 % | 15 % | IN |

45 cells in tolerance, 12 out. Largest deltas: close_page col_major_interleaved_bl16 (26.9 %), bank_interleave col_major_bl4 (23.4 %), bank_interleave row_major_bl16 (17.3 %), bank_interleave row_major_bl8 (17.2 %), bank_interleave row_major_bl4 (17.2 %), bank_interleave incremental_bl16 (16.9 %).
