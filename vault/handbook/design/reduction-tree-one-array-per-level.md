---
title: Reduction tree, one array per level
summary: A combinational reduction tree kept in ONE unpacked array is a combinational loop to Verilator (UNOPTFLAT); give each level its own array in its own generate scope.
---

# Reduction tree: one array per level

A heap-indexed tree is the natural way to write a max/min/or reduction over
N inputs: leaves at `N-1 .. 2N-2`, node `n = f(node[2n+1], node[2n+2])`, root
at 0, all in one `logic [W-1:0] w_node [2*N-1]`. It is legal SystemVerilog,
every node is driven once, and no node depends on itself.

Verilator still refuses it:

    %Warning-UNOPTFLAT: Signal unoptimizable: Circular combinational logic: 'w_node'

It schedules an unpacked array as ONE variable. An `assign` that reads
`w_node[...]` and writes `w_node[...]` is, to the scheduler, `w_node` feeding
`w_node`, whatever the indices. Under the cocotb build (`-Wall`, warnings
fatal) the test never compiles. `--lint-only` alone does NOT show it
(gaxi_age_fifo_sync, 2026-10-25: clean lint at four parameter points, then
UNOPTFLAT on the first simulation build).

The fix that needs no metacomment and no waiver: one array per level, each in
its own named generate scope, the next level reading the previous one by a
constant hierarchical index.

```systemverilog
logic [W-1:0] w_leaf [NP];                       // level 0, padded to 2^k
for (genvar lvl = 0; lvl < NLVL; lvl++) begin : g_lvl
    localparam int N_OUT = NP >> (lvl + 1);
    logic [W-1:0] w_max [N_OUT];
    for (genvar k = 0; k < N_OUT; k++) begin : g_node
        logic [W-1:0] w_a, w_b;
        if (lvl == 0) begin : g_from_leaf
            assign w_a = w_leaf[2*k];  assign w_b = w_leaf[2*k+1];
        end else begin : g_from_lvl
            assign w_a = g_lvl[lvl-1].w_max[2*k];  assign w_b = g_lvl[lvl-1].w_max[2*k+1];
        end
        assign w_max[k] = (w_a > w_b) ? w_a : w_b;
    end
end
assign result = g_lvl[NLVL-1].w_max[0];          // guard NLVL == 0 with a generate if
```

Each level is a distinct variable, so the dependency graph is a DAG again.
Verilator and Vivado both take constant-index references into a generate
array. `/* verilator split_var */` on the single array also works but is a
tool-specific comment doing the job a structural fix does for every tool.

The same rule reaches any "array that feeds itself by index": a carry chain
written as `w_c[i+1] = f(w_c[i])` in one array, a prefix sum, a priority
scan. See [[variable-part-select-is-a-shifter]] for the other way an indexed
array surprises you, and [[priority-logic-depth]] for why the tree is wanted
in the first place.
