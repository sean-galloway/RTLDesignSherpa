# merlin-rv32i test programs

The hex images in this directory are copied from the kestrel-rv32i test
suite and exercise the same RV32I subset:

- `focus.hex` — back-to-back dependent ALU operations and x0 discard.
- `rv32ui_ops.hex` — one vector per OP/OP-IMM operation plus LUI/AUIPC.
- `ls_basic.hex` — naturally aligned byte/half/word loads and stores.

Source: `projects/components/riscv-ip/kestrel-rv32i/dv/tests/programs/`
