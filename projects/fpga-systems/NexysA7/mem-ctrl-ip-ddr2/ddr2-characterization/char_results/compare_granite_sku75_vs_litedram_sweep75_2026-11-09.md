
### every  (72 granite cells, 17 LiteDRAM cells; mismatched beats: 0)

| scenario | granite bank_interleave | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|---|
| incremental_bl4 | 193 / 193 | 60 / 75 | 576 / 577 | 576 / 579 | 554 / 564 | 579 / 564 = 1.03x | win |
| incremental_bl8 | 193 / 193 | 60 / 75 | 576 / 577 | 576 / 579 | 554 / 564 | 579 / 564 = 1.03x | win |
| incremental_bl16 | 193 / 193 | 60 / 75 | 576 / 577 | 576 / 579 | 554 / 564 | 579 / 564 = 1.03x | win |
| row_major_bl4 | 193 / 193 | 58 / 73 | 578 / 582 | 578 / 582 | 569 / 579 | 582 / 579 = 1.00x | tie |
| row_major_bl8 | 193 / 193 | 58 / 73 | 578 / 582 | 578 / 582 | 569 / 580 | 582 / 580 = 1.00x | tie |
| row_major_bl16 | 193 / 193 | 58 / 73 | 578 / 582 | 578 / 582 | 569 / 580 | 582 / 580 = 1.00x | tie |
| col_major_bl4 | 192 / 193 | 61 / 78 | 213 / 291 | 213 / 291 | 208 / 290 | 291 / 290 = 1.00x | tie |
| col_major_bl8 | 193 / 193 | 60 / 76 | 311 / 389 | 311 / 389 | 304 / 386 | 389 / 386 = 1.01x | tie |
| col_major_bl16 | 193 / 193 | 59 / 74 | 404 / 467 | 404 / 467 | 396 / 464 | 467 / 464 = 1.01x | tie |
| col_major_interleaved_bl4 | 193 / 193 | 175 / 193 | 455 / 459 | 461 / 459 | 180 / 184 | 461 / 184 = 2.50x | win |
| col_major_interleaved_bl8 | 193 / 193 | 131 / 172 | 508 / 513 | 512 / 513 | 277 / 280 | 513 / 280 = 1.83x | win |
| col_major_interleaved_bl16 | 193 / 193 | 91 / 133 | 541 / 543 | 541 / 545 | 377 / 380 | 545 / 380 = 1.43x | win |
| col_major_bl8_multiid | 193 / 193 | 60 / 76 | 311 / 389 | 311 / 389 | 304 / 386 | 389 / 386 = 1.01x | tie |
| col_major_bl8_gap | 193 / 193 | 60 / 76 | 282 / 300 | 282 / 300 | 282 / 300 | 300 / 300 = 1.00x | tie |
| incremental_bl8_multiid | 193 / 193 | 60 / 75 | 576 / 577 | 576 / 579 | 554 / 564 | 579 / 564 = 1.03x | win |
| row_major_bl8_multiid | 193 / 193 | 58 / 73 | 578 / 582 | 578 / 582 | 569 / 579 | 582 / 579 = 1.00x | tie |
| col_major_interleaved_bl8_multiid | 193 / 193 | 131 / 172 | 508 / 513 | 512 / 513 | 277 / 280 | 513 / 280 = 1.83x | win |

granite ahead on 8 of 17 scenarios (best preset vs LiteDRAM, max of write / read)

### windows  (9 granite cells, 3 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| mixed_bl8 | 42 / 50 | 217 / 351 | 219 / 354 | 119 / 119 | 354 / 119 = 2.98x | win |
| row_thrash_bl8 | 131 / 172 | 508 / 513 | 512 / 513 | 271 / 278 | 513 / 278 = 1.84x | win |
| random_bl8 | 112 / 152 | 469 / 490 | 474 / 493 | 286 / 298 | 493 / 298 = 1.66x | win |

granite ahead on 3 of 3 scenarios (best preset vs LiteDRAM, max of write / read)

### half_threads  (48 granite cells, 16 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair_thr1 | 30 / 37 | 288 / 289 | 288 / 290 | 243 / 286 | 290 / 286 = 1.01x | tie |
| half_pair_thr2 | 49 / 73 | 287 / 287 | 287 / 288 | 71 / 72 | 288 / 72 = 4.00x | win |
| half_pair_thr3 | 73 / 97 | 284 / 285 | 256 / 285 | 70 / 71 | 285 / 71 = 3.99x | win |
| half_pair_thr4 | 96 / 96 | 282 / 282 | 215 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_pair_thr5 | 96 / 96 | 282 / 282 | 214 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_pair_thr6 | 96 / 96 | 282 / 282 | 215 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_pair_thr7 | 96 / 96 | 282 / 282 | 215 / 250 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_pair_thr8 | 96 / 96 | 282 / 282 | 215 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_oct_thr1 | 30 / 37 | 288 / 289 | 288 / 290 | 243 / 286 | 290 / 286 = 1.01x | tie |
| half_oct_thr2 | 49 / 73 | 286 / 287 | 287 / 288 | 71 / 72 | 288 / 72 = 4.00x | win |
| half_oct_thr3 | 73 / 97 | 284 / 285 | 256 / 285 | 70 / 71 | 285 / 71 = 3.99x | win |
| half_oct_thr4 | 96 / 96 | 282 / 282 | 215 / 250 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_oct_thr5 | 96 / 96 | 282 / 282 | 214 / 250 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_oct_thr6 | 96 / 96 | 282 / 282 | 214 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_oct_thr7 | 96 / 96 | 282 / 282 | 215 / 250 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_oct_thr8 | 96 / 96 | 282 / 282 | 214 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |

granite ahead on 14 of 16 scenarios (best preset vs LiteDRAM, max of write / read)

### half_burst  (12 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair | 30 / 37 | 288 / 289 | 288 / 290 | 243 / 286 | 290 / 286 = 1.02x | tie |
| half_oct | 30 / 37 | 288 / 289 | 288 / 290 | 243 / 286 | 290 / 286 = 1.02x | tie |
| half_pair_sweep | 30 / 37 | 55 / 67 | 55 / 67 | 55 / 67 | 67 / 67 = 1.00x | tie |
| half_oct_sweep | 30 / 37 | 55 / 67 | 55 / 67 | 55 / 67 | 67 / 67 = 1.00x | tie |

granite ahead on 0 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

### half_burst8  (12 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair | 96 / 96 | 282 / 282 | 215 / 249 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_oct | 96 / 96 | 282 / 282 | 215 / 250 | 70 / 71 | 282 / 71 = 3.98x | win |
| half_pair_sweep | 96 / 96 | 213 / 258 | 203 / 227 | 70 / 71 | 258 / 71 = 3.63x | win |
| half_oct_sweep | 96 / 96 | 213 / 258 | 203 / 228 | 70 / 71 | 258 / 71 = 3.63x | win |

granite ahead on 4 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

### half_gap  (24 granite cells, 8 LiteDRAM cells; mismatched beats: 0)

| scenario | granite close_page | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|---|
| half_pair_gap0 | 29 / 37 | 282 / 281 | 287 / 285 | 242 / 280 | 287 / 280 = 1.03x | win |
| half_pair_gap1 | 29 / 37 | 99 / 148 | 99 / 148 | 99 / 148 | 148 / 148 = 1.00x | tie |
| half_pair_gap2 | 29 / 37 | 75 / 99 | 75 / 99 | 75 / 99 | 99 / 99 = 1.00x | tie |
| half_pair_gap3 | 29 / 37 | 60 / 75 | 60 / 75 | 60 / 75 | 75 / 75 = 1.00x | tie |
| half_pair_gap4 | 29 / 37 | 50 / 60 | 50 / 60 | 50 / 60 | 60 / 60 = 1.00x | tie |
| half_pair_gap5 | 29 / 37 | 43 / 50 | 43 / 50 | 43 / 50 | 50 / 50 = 1.00x | tie |
| half_pair_gap6 | 29 / 37 | 37 / 43 | 37 / 43 | 37 / 43 | 43 / 43 = 1.00x | tie |
| half_pair_gap7 | 29 / 37 | 33 / 37 | 33 / 37 | 33 / 37 | 37 / 37 = 1.00x | tie |

granite ahead on 1 of 8 scenarios (best preset vs LiteDRAM, max of write / read)

### concurrent  (8 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|
| incremental_bl8 | 281 / 281 | 281 / 281 | 124 / 124 | 281 / 124 = 2.27x | win |
| row_major_bl8 | 276 / 276 | 276 / 276 | 143 / 143 | 276 / 143 = 1.93x | win |
| col_major_bl8 | 169 / 169 | 169 / 169 | 124 / 124 | 169 / 124 = 1.36x | win |
| col_major_interleaved_bl8 | 237 / 237 | 237 / 237 | 123 / 123 | 237 / 123 = 1.93x | win |

granite ahead on 4 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

### multigen  (8 granite cells, 4 LiteDRAM cells; mismatched beats: 0)

| scenario | granite defaults | granite open_page | LiteDRAM | granite best / LiteDRAM | verdict |
|---|---|---|---|---|---|
| incremental_bl8 | 144 / 287 | 144 / 287 | 93 / 186 | 287 / 186 = 1.54x | win |
| row_major_bl8 | 186 / 371 | 174 / 348 | 106 / 211 | 371 / 211 = 1.76x | win |
| col_major_bl8 | 118 / 236 | 118 / 236 | 94 / 187 | 236 / 187 = 1.26x | win |
| col_major_interleaved_bl8 | 90 / 180 | 90 / 180 | 82 / 164 | 180 / 164 = 1.10x | win |

granite ahead on 4 of 4 scenarios (best preset vs LiteDRAM, max of write / read)

**Tally over 60 shared cells: 38 win, 22 tie, 0 lose** (tie = within 2 percent)
