<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Data Flow

## Transaction Flow Overview

### Write Transaction Flow

1. **Master issues AW** - Address and control information
2. **Bridge decodes address** - Determines target slave
3. **Arbitration** - Grants access if multiple masters contend
4. **AW forwarded to slave** - With extended ID (Bridge ID prepended)
5. **Master sends W data** - Following the granted AW
6. **W forwarded to slave** - Using same grant
7. **Slave returns B response** - With extended ID
8. **Bridge routes B to master** - Using ID to find originator

### Read Transaction Flow

1. **Master issues AR** - Address and control information
2. **Bridge decodes address** - Determines target slave
3. **Arbitration** - Grants access if multiple masters contend
4. **AR forwarded to slave** - With extended ID
5. **Slave returns R data** - Potentially multiple beats
6. **Bridge routes R to master** - Using ID to find originator

## Channel Independence

### AXI4 Channel Separation

Each AXI4 channel operates independently:

| Channel | Direction | Contents | Arbitration |
|---------|-----------|----------|-------------|
| AW | Master to Slave | Write address | Per-slave |
| W | Master to Slave | Write data | Follows AW grant |
| B | Slave to Master | Write response | ID-based routing |
| AR | Master to Slave | Read address | Per-slave |
| R | Slave to Master | Read data | ID-based routing |

: Table 3.2: AXI4 Channel Summary

### Parallel Operation

- Read and write transactions can proceed simultaneously
- Different masters can access different slaves in parallel
- Same slave serializes access via arbitration

## ID Extension

### Bridge ID (BID) Concept

```
Original Master ID: [ID_WIDTH-1:0]
Extended ID: [BID | Original ID]
BID Width: clog2(NUM_MASTERS)
```

### Example: 4 Masters, 4-bit ID

```
Master 0 ID = 4'b0101
Extended ID = 6'b00_0101  (BID=00, prepended)

Master 3 ID = 4'b1100
Extended ID = 6'b11_1100  (BID=11, prepended)
```

### ID Flow

```
Master 0: ID=5 --[Extend]--> Slave: ID=0x05 --[Response]--> B.ID=0x05 --[Extract]--> Master 0
Master 1: ID=5 --[Extend]--> Slave: ID=0x15 --[Response]--> B.ID=0x15 --[Extract]--> Master 1
```

## Response Routing

### B Channel (Write Response)

1. Slave issues B with extended ID
2. Bridge extracts BID from upper bits
3. BID determines destination master
4. Original ID (lower bits) returned to master

### R Channel (Read Data)

1. Slave issues R with extended ID
2. Bridge extracts BID from upper bits
3. BID determines destination master
4. Original ID (lower bits) returned to master
5. RLAST indicates final beat

## Out-of-Order Support

### Transaction Interleaving

Bridge supports out-of-order completion:

- Different IDs can complete in any order
- Same ID must complete in order (AXI4 rule)
- ID tracking tables manage outstanding transactions

### Example Sequence

```
Time 0: Master 0 issues AR (ID=1) to Slave 0
Time 1: Master 0 issues AR (ID=2) to Slave 1
Time 2: Slave 1 returns R (ID=2) - fast slave
Time 3: Slave 0 returns R (ID=1) - slow slave

Result: ID=2 response arrives before ID=1 - valid OOO
```
