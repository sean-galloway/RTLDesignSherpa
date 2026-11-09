
### every  (72 granite cells, 17 LiteDRAM cells; mismatched beats: 0)

| scenario | granite bank_interleave | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|---|
| incremental_bl4 | 258 / 258 | 80 / 89 | 772 / 773 | 772 / 775 | 746 / 756 | 775 / 756 = 1.03x | win |
| incremental_bl8 | 258 / 258 | 80 / 89 | 772 / 773 | 772 / 775 | 746 / 756 | 775 / 756 = 1.03x | win |
| incremental_bl16 | 258 / 258 | 80 / 89 | 772 / 773 | 772 / 775 | 746 / 756 | 775 / 756 = 1.03x | win |
| row_major_bl4 | 258 / 258 | 78 / 87 | 775 / 778 | 775 / 778 | 766 / 776 | 778 / 776 = 1.00x | tie |
| row_major_bl8 | 258 / 258 | 78 / 87 | 775 / 778 | 775 / 778 | 766 / 776 | 778 / 776 = 1.00x | tie |
| row_major_bl16 | 258 / 258 | 78 / 87 | 775 / 778 | 775 / 778 | 766 / 776 | 778 / 776 = 1.00x | tie |
| col_major_bl4 | 258 / 258 | 82 / 92 | 283 / 389 | 283 / 389 | 279 / 388 | 389 / 388 = 1.00x | tie |
| col_major_bl8 | 258 / 258 | 80 / 90 | 416 / 520 | 416 / 520 | 409 / 518 | 520 / 518 = 1.01x | tie |
| col_major_bl16 | 258 / 258 | 79 / 88 | 541 / 623 | 541 / 623 | 534 / 621 | 623 / 621 = 1.00x | tie |
| col_major_interleaved_bl4 | 258 / 258 | 236 / 259 | 617 / 615 | 615 / 619 | 241 / 246 | 619 / 246 = 2.52x | win |
| col_major_interleaved_bl8 | 258 / 258 | 175 / 229 | 684 / 686 | 688 / 688 | 368 / 372 | 688 / 372 = 1.85x | win |
| col_major_interleaved_bl16 | 258 / 258 | 121 / 160 | 721 / 729 | 729 / 730 | 500 / 507 | 730 / 507 = 1.44x | win |
| col_major_bl8_multiid | 258 / 258 | 80 / 90 | 416 / 520 | 416 / 520 | 409 / 518 | 520 / 518 = 1.01x | tie |
| col_major_bl8_gap | 258 / 258 | 80 / 90 | 376 / 400 | 376 / 400 | 376 / 400 | 400 / 400 = 1.00x | tie |
| incremental_bl8_multiid | 258 / 258 | 80 / 89 | 772 / 773 | 772 / 775 | 746 / 756 | 775 / 756 = 1.03x | win |
| row_major_bl8_multiid | 258 / 258 | 78 / 87 | 775 / 778 | 775 / 778 | 766 / 776 | 778 / 776 = 1.00x | tie |
| col_major_interleaved_bl8_multiid | 258 / 258 | 175 / 229 | 684 / 688 | 688 / 688 | 368 / 372 | 688 / 372 = 1.85x | win |

granite ahead on 8 of 17 scenarios (best preset vs LiteDRAM, max of write / read)

### windows  (9 granite cells, 3 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| mixed_bl8 | 48 / 48 | 251 / 283 | 263 / 330 | 159 / 159 | 330 / 159 = 2.07x | win |
| row_thrash_bl8 | 175 / 229 | 688 / 688 | 688 / 688 | 364 / 368 | 688 / 368 = 1.87x | win |
| random_bl8 | 149 / 190 | 628 / 657 | 635 / 661 | 383 / 397 | 661 / 397 = 1.66x | win |

granite ahead on 3 of 3 scenarios (best preset vs LiteDRAM, max of write / read)

### half_threads  (48 granite cells, 16 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair_thr1 | 40 / 44 | 386 / 387 | 387 / 388 | 324 / 383 | 388 / 383 = 1.01x | tie |
| half_pair_thr2 | 66 / 87 | 385 / 385 | 385 / 386 | 95 / 96 | 386 / 96 = 4.00x | win |
| half_pair_thr3 | 97 / 129 | 382 / 383 | 339 / 383 | 95 / 96 | 383 / 96 = 3.99x | win |
| half_pair_thr4 | 129 / 129 | 380 / 380 | 287 / 334 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_pair_thr5 | 129 / 129 | 380 / 380 | 286 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_pair_thr6 | 129 / 129 | 380 / 380 | 287 / 334 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_pair_thr7 | 129 / 129 | 380 / 380 | 286 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_pair_thr8 | 129 / 129 | 380 / 380 | 288 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_oct_thr1 | 40 / 44 | 387 / 387 | 387 / 388 | 324 / 383 | 388 / 383 = 1.01x | tie |
| half_oct_thr2 | 66 / 87 | 384 / 385 | 385 / 386 | 95 / 96 | 386 / 96 = 4.00x | win |
| half_oct_thr3 | 97 / 129 | 382 / 382 | 349 / 383 | 95 / 96 | 383 / 96 = 3.99x | win |
| half_oct_thr4 | 129 / 129 | 380 / 380 | 286 / 334 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_oct_thr5 | 129 / 129 | 380 / 380 | 286 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_oct_thr6 | 129 / 129 | 380 / 380 | 287 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_oct_thr7 | 129 / 129 | 380 / 380 | 286 / 334 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_oct_thr8 | 129 / 129 | 380 / 380 | 286 / 334 | 94 / 95 | 380 / 95 = 3.98x | win |

granite ahead on 14 of 16 scenarios (best preset vs LiteDRAM, max of write / read)

### half_burst  (12 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair | 40 / 44 | 387 / 387 | 387 / 388 | 324 / 383 | 388 / 383 = 1.01x | tie |
| half_oct | 40 / 44 | 386 / 387 | 386 / 388 | 324 / 383 | 388 / 383 = 1.01x | tie |
| half_pair_sweep | 40 / 44 | 73 / 89 | 73 / 89 | 73 / 89 | 89 / 89 = 1.00x | tie |
| half_oct_sweep | 40 / 44 | 73 / 89 | 73 / 89 | 73 / 89 | 89 / 89 = 1.00x | tie |

granite ahead on 0 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

### half_burst8  (12 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair | 129 / 129 | 380 / 380 | 287 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_oct | 129 / 129 | 380 / 380 | 286 / 333 | 94 / 95 | 380 / 95 = 3.98x | win |
| half_pair_sweep | 129 / 129 | 285 / 345 | 273 / 301 | 94 / 95 | 345 / 95 = 3.61x | win |
| half_oct_sweep | 129 / 129 | 285 / 344 | 272 / 301 | 94 / 95 | 344 / 95 = 3.61x | win |

granite ahead on 4 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

### half_gap  (24 granite cells, 8 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair_gap0 | 39 / 44 | 374 / 373 | 382 / 379 | 323 / 378 | 382 / 378 = 1.01x | tie |
| half_pair_gap1 | 39 / 44 | 133 / 197 | 133 / 197 | 133 / 197 | 197 / 197 = 1.00x | tie |
| half_pair_gap2 | 39 / 44 | 100 / 132 | 99 / 132 | 100 / 132 | 132 / 132 = 1.00x | tie |
| half_pair_gap3 | 39 / 44 | 80 / 99 | 80 / 99 | 80 / 99 | 99 / 99 = 1.00x | tie |
| half_pair_gap4 | 39 / 44 | 66 / 80 | 66 / 80 | 67 / 80 | 80 / 80 = 1.00x | tie |
| half_pair_gap5 | 39 / 44 | 57 / 66 | 57 / 66 | 57 / 66 | 66 / 66 = 1.00x | tie |
| half_pair_gap6 | 39 / 44 | 50 / 57 | 50 / 57 | 50 / 57 | 57 / 57 = 1.00x | tie |
| half_pair_gap7 | 39 / 44 | 44 / 50 | 44 / 50 | 44 / 50 | 50 / 50 = 1.00x | tie |

granite ahead on 0 of 8 scenarios (best preset vs LiteDRAM, max of write / read)

### concurrent  (8 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|
| incremental_bl8 | 369 / 369 | 370 / 370 | 167 / 167 | 370 / 167 = 2.21x | win |
| row_major_bl8 | 370 / 370 | 370 / 370 | 192 / 192 | 370 / 192 = 1.92x | win |
| col_major_bl8 | 226 / 226 | 226 / 226 | 167 / 167 | 226 / 167 = 1.36x | win |
| col_major_interleaved_bl8 | 317 / 317 | 318 / 318 | 164 / 164 | 318 / 164 = 1.94x | win |

granite ahead on 4 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

### multigen  (8 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|
| incremental_bl8 | 192 / 383 | 192 / 383 | 126 / 252 | 383 / 252 = 1.52x | win |
| row_major_bl8 | 250 / 499 | 232 / 464 | 142 / 284 | 499 / 284 = 1.76x | win |
| col_major_bl8 | 158 / 316 | 158 / 316 | 126 / 252 | 316 / 252 = 1.25x | win |
| col_major_interleaved_bl8 | 129 / 257 | 126 / 253 | 110 / 220 | 257 / 220 = 1.17x | win |

granite ahead on 4 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

**Tally over 60 shared cells: 37 win, 23 tie, 0 lose** (tie = within 2 percent)
