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

# amber_repl: Replacement Policy Engine

**Module:** `amber_repl.sv`
**Location:** `projects/components/cache-ip/amber-mesi-l1/rtl/fub/`
**Status:** Pre-RTL micro-architecture contract

---

## Overview

`amber_repl` selects the victim way on a cache miss. The policy is an elaboration parameter `REPL_POLICY` with supported values `lru`, `tree_plru`, `fifo`, and `random`. LRU is the default; tree-PLRU is the timing-tight fallback.

---

## Interface

| Signal | Direction | Width | Meaning |
|--------|-----------|-------|---------|
| `repl_req` | input | 1 | Request a victim way this cycle. |
| `repl_set` | input | `SET_INDEX_WIDTH` | Set index for the access. |
| `repl_hit_way` | input | `WAY_WIDTH` | Way that hit (for update). |
| `repl_hit` | input | 1 | A hit occurred; update policy state. |
| `repl_victim_way` | output | `WAY_WIDTH` | Selected victim way. |
| `repl_update` | input | 1 | A miss install occurred; update policy state for `repl_set`. |

`repl_hit` and `repl_update` are mutually exclusive in the blocking pipeline: a cycle is either a hit service or a miss install, never both.

---

## LRU (True LRU)

True LRU maintains a recency stack per set. For `WAYS` ways, each set stores `WAYS*(WAYS-1)/2` ordering bits. On every hit or install, the accessed way is moved to the most-recent position and the other ways are shifted down. The victim is the least-recent way.

This matches `cache_sim` exactly and is the golden reference for policy parity.

### Implementation

Use a per-set array of `WAYS` rank values. The rank value is `0` for most-recent, `WAYS-1` for least-recent. On access:

```systemverilog
for (int w = 0; w < WAYS; w++) begin
    if (w == accessed_way)
        rank[set][w] = 0;
    else if (rank[set][w] < old_rank_of_accessed_way)
        rank[set][w] += 1;
end
```

The victim way is the one with `rank[set][w] == WAYS-1`.

---

## FIFO

Each set maintains a FIFO queue of way indices. On a miss, the head of the queue is the victim; the installed way is pushed to the tail. On a hit, the queue is unchanged (FIFO does not recency-stack).

This matches `cache_sim` exactly.

---

## RANDOM

Each set contains a small LFSR. On a replacement request, the LFSR value is truncated to `WAY_WIDTH` bits to select the victim way. The LFSR advances every replacement request. The seed is parameterizable for repeatable tests.

This matches `cache_sim` exactly when the same LFSR polynomial and seed are used.

---

## Tree-PLRU

Tree-PLRU is carried as the timing-tight fallback per PRD D7. It uses `WAYS-1` bits per set arranged as a binary tree. On each access, the tree bits point away from the accessed way. On a replacement request, the tree bits are followed to find the victim.

Tree-PLRU does **not** have a `cache_sim` golden model today. It is cross-checked by RTL self-checks and is recorded as a future `cache_sim` extension. This is an honest caveat, not a hidden assumption.

---

## Policy Selection

The policy is selected at elaboration time:

```systemverilog
generate
    if (REPL_POLICY == "lru") begin : gen_lru
        // true LRU rank array
    end else if (REPL_POLICY == "fifo") begin : gen_fifo
        // FIFO queue array
    end else if (REPL_POLICY == "random") begin : gen_random
        // LFSR per set
    end else if (REPL_POLICY == "tree_plru") begin : gen_tree_plru
        // binary tree PLRU
    end
endgenerate
```

Only one policy is instantiated per build. This keeps area predictable and matches the `cache_sim` per-policy parity model.

---

**Last Updated:** 2026-10-06
