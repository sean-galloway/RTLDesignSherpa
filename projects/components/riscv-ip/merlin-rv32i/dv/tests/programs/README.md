# merlin-rv32i test programs

The hex images in this directory exercise the merlin 5-stage RV32I core.

Copied from the kestrel-rv32i test suite:

- `focus.hex` — back-to-back dependent ALU operations and x0 discard.
- `rv32ui_ops.hex` — one vector per OP/OP-IMM operation plus LUI/AUIPC.
- `ls_basic.hex` — naturally aligned byte/half/word loads and stores.

Task-3 regression programs:

- `load_after_alu.hex` — a `lw` whose MEM predecessor is a non-memory ALU op.
- `load_use_distances.hex` — load-use consumers at distances 1/2/3 (distance 1 costs one bubble).
- `mem_wait_in_wb.hex` — `mem_wait` parks a load in WB while a follower sits in MEM.

Task-4 directed hazard suite (`hazard_*.hex`):

- `hazard_forward_matrix.hex` — forwarding from EX/MEM and MEM/WB into both ALU operands.
- `hazard_branch_after_alu.hex` — taken/not-taken branches using immediately-preceding ALU results.
- `hazard_store_data_forward.hex` — ALU result forwarded into a `sw` rs2, verified by a later `lw`.
- `hazard_flush_during_loaduse.hex` — taken branch after a load-use stall flushes the consumer's successor.
- `hazard_jalr_forward.hex` — `jalr` target forwarded from a preceding ALU op and from a load result.
- `hazard_branch_flush_backtoback.hex` — two taken branches back-to-back.

Source (kestrel programs): `projects/components/riscv-ip/kestrel-rv32i/dv/tests/programs/`
