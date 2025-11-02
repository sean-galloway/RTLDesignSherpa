# Appendix A: Tile Coordinate Mapping

## A.1 Tile ID to (Column, Row) Mapping

```
Tile ID to (Column, Row) mapping:

ID   Col  Row  |  ID   Col  Row
-----|----------|---------------
 0    0    0   |   8    0    2
 1    1    0   |   9    1    2
 2    2    0   |  10    2    2
 3    3    0   |  11    3    2
 4    0    1   |  12    0    3
 5    1    1   |  13    1    3
 6    2    1   |  14    2    3
 7    3    1   |  15    3    3

Virtual tiles:
16   0    4  (RAPIDS - south of tile 12)
17   3   -1  (HIVE-C - north of tile 3)
```

## A.2 Coordinate Extraction

```verilog
// Extract coordinates from tile ID
column = tile_id[1:0];  // Bits [1:0]
row    = tile_id[3:2];  // Bits [3:2]

// Example: Tile 10
// ID = 10 = 4'b1010
// column = 2'b10 = 2
// row    = 2'b10 = 2
// Coordinates: (2, 2)
```

## A.3 Reverse Mapping (Coordinates to ID)

```verilog
tile_id = {row[1:0], column[1:0]};

// Example: (column=3, row=1)
// tile_id = {2'b01, 2'b11} = 4'b0111 = 7
```

## A.4 Physical Layout

```
         Column
       0   1   2   3
     +---+---+---+---+
  0  | 0 | 1 | 2 | 3 |  Row 0
     +---+---+---+---+
  1  | 4 | 5 | 6 | 7 |  Row 1
     +---+---+---+---+
  2  | 8 | 9 |10 |11 |  Row 2
     +---+---+---+---+
  3  |12 |13 |14 |15 |  Row 3
     +---+---+---+---+
```

## A.5 Manhattan Distance Calculation

```verilog
function [3:0] manhattan_distance(
    input [3:0] src_tile,
    input [3:0] dst_tile
);
    logic [1:0] src_x, src_y;
    logic [1:0] dst_x, dst_y;
    logic [1:0] delta_x, delta_y;
    
    src_x = src_tile[1:0];
    src_y = src_tile[3:2];
    dst_x = dst_tile[1:0];
    dst_y = dst_tile[3:2];
    
    delta_x = (dst_x > src_x) ? (dst_x - src_x) : (src_x - dst_x);
    delta_y = (dst_y > src_y) ? (dst_y - src_y) : (src_y - dst_y);
    
    return delta_x + delta_y;  // Hops required
endfunction

// Example: Tile 0 -> Tile 15
// (0,0) -> (3,3)
// delta_x = 3, delta_y = 3
// distance = 6 hops
```

---

**Back to:** [Index](delta_index.md)
