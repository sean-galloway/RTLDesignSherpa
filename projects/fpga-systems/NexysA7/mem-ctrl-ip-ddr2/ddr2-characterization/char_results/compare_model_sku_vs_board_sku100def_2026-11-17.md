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
| defaults | col_major_interleaved_bl4 | 765 / 763 | 776 / 777 | +1.5 / +1.8 % | 3 % | IN |
| defaults | col_major_interleaved_bl8 | 768 / 768 | 778 / 780 | +1.3 / +1.5 % | 3 % | IN |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 778 / 780 | +0.8 / +1.2 % | 3 % | IN |
| defaults | mixed_bl8 | 272 / 272 (union 543) | 296 / 417 (union 592) | +8.9 % (union) | 10 % | IN |
| defaults | row_thrash_bl8 | 770 / 770 | 778 / 779 | +1.0 / +1.2 % | 3 % | IN |
| defaults | random_bl8 | 718 / 740 | 747 / 767 | +4.0 / +3.6 % | 5 % | IN |
| open_page | incremental_bl4 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl8 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | incremental_bl16 | 775 / 778 | 778 / 781 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl4 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl8 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | row_major_bl16 | 775 / 778 | 778 / 782 | +0.4 / +0.4 % | 2 % | IN |
| open_page | col_major_bl4 | 283 / 389 | 283 / 390 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_bl8 | 416 / 520 | 418 / 520 | +0.6 / -0.1 % | 5 % | IN |
| open_page | col_major_bl16 | 541 / 623 | 542 / 624 | +0.1 / +0.1 % | 5 % | IN |
| open_page | col_major_interleaved_bl4 | 768 / 768 | 776 / 777 | +1.0 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl8 | 770 / 770 | 778 / 780 | +1.0 / +1.2 % | 3 % | IN |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 778 / 780 | +0.8 / +0.8 % | 3 % | IN |
| open_page | mixed_bl8 | 272 / 272 (union 545) | 296 / 417 (union 592) | +8.6 % (union) | 10 % | IN |
| open_page | row_thrash_bl8 | 770 / 770 | 778 / 779 | +1.0 / +1.2 % | 3 % | IN |
| open_page | random_bl8 | 726 / 746 | 747 / 767 | +3.0 / +2.8 % | 5 % | IN |
| bank_interleave | incremental_bl4 | 238 / 233 | 778 / 781 | +226.7 / +234.5 % | 10 % | OUT |
| bank_interleave | incremental_bl8 | 234 / 233 | 778 / 781 | +233.0 / +235.4 % | 10 % | OUT |
| bank_interleave | incremental_bl16 | 238 / 233 | 778 / 781 | +226.8 / +234.8 % | 10 % | OUT |
| bank_interleave | row_major_bl4 | 238 / 233 | 777 / 781 | +226.7 / +235.7 % | 10 % | OUT |
| bank_interleave | row_major_bl8 | 238 / 232 | 777 / 781 | +226.6 / +236.5 % | 10 % | OUT |
| bank_interleave | row_major_bl16 | 238 / 232 | 777 / 781 | +226.6 / +236.6 % | 10 % | OUT |
| bank_interleave | col_major_bl4 | 195 / 239 | 312 / 312 | +60.2 / +30.2 % | 10 % | OUT |
| bank_interleave | col_major_bl8 | 237 / 235 | 312 / 312 | +31.5 / +32.5 % | 10 % | OUT |
| bank_interleave | col_major_bl16 | 238 / 234 | 519 / 519 | +118.1 / +122.0 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl4 | 195 / 222 | 777 / 780 | +299.1 / +251.2 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl8 | 238 / 234 | 774 / 776 | +225.1 / +231.7 % | 10 % | OUT |
| bank_interleave | col_major_interleaved_bl16 | 238 / 235 | 775 / 779 | +225.9 / +232.1 % | 10 % | OUT |
| close_page | incremental_bl4 | 82 / 92 | 104 / 119 | +27.3 / +29.0 % | 15 % | OUT |
| close_page | incremental_bl8 | 82 / 92 | 104 / 119 | +27.3 / +29.0 % | 15 % | OUT |
| close_page | incremental_bl16 | 82 / 92 | 104 / 119 | +27.3 / +29.0 % | 15 % | OUT |
| close_page | row_major_bl4 | 78 / 87 | 98 / 112 | +24.9 / +28.6 % | 15 % | OUT |
| close_page | row_major_bl8 | 78 / 87 | 98 / 112 | +24.9 / +28.6 % | 15 % | OUT |
| close_page | row_major_bl16 | 78 / 87 | 98 / 112 | +24.9 / +28.6 % | 15 % | OUT |
| close_page | col_major_bl4 | 82 / 92 | 98 / 112 | +18.7 / +21.4 % | 15 % | OUT |
| close_page | col_major_bl8 | 80 / 90 | 98 / 112 | +21.8 / +24.9 % | 15 % | OUT |
| close_page | col_major_bl16 | 79 / 88 | 98 / 112 | +23.5 / +27.1 % | 15 % | OUT |
| close_page | col_major_interleaved_bl4 | 235 / 232 | 312 / 312 | +32.6 / +34.5 % | 15 % | OUT |
| close_page | col_major_interleaved_bl8 | 213 / 219 | 312 / 312 | +46.3 / +42.7 % | 15 % | OUT |
| close_page | col_major_interleaved_bl16 | 180 / 240 | 289 / 312 | +60.2 / +29.7 % | 15 % | OUT |
| close_page | mixed_bl8 | 73 / 152 (union 145) | 95 / 95 (union 190) | +31.1 % (union) | 15 % | OUT |
| close_page | row_thrash_bl8 | 208 / 197 | 312 / 312 | +50.2 / +58.5 % | 15 % | OUT |
| close_page | random_bl8 | 188 / 207 | 281 / 293 | +49.5 / +41.7 % | 15 % | OUT |

30 cells in tolerance, 27 out. Largest deltas: bank_interleave col_major_interleaved_bl4 (299.1 %), bank_interleave row_major_bl16 (236.6 %), bank_interleave row_major_bl8 (236.5 %), bank_interleave row_major_bl4 (235.7 %), bank_interleave incremental_bl8 (235.4 %), bank_interleave incremental_bl16 (234.8 %).
