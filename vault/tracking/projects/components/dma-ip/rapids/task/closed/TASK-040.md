# TASK-040: autonomous descriptor chaining in the descriptor engine

> Migrated 2026-11-07 from `projects/components/dma-ip/rapids/TASKS.md` as **TASK-011**.

**Priority:** P1
**Status:** CLOSED 2026-07-02 -- arrived with the beats RTL resync from STREAM (516f68164); tested by `test_descriptor_chaining`.
**Owner:** sean galloway

The descriptor engine follows `next_descriptor_ptr` itself instead of waiting
for an APB kick per descriptor.

- `rtl/fub_beats/descriptor_engine_beats.sv`: header "Autonomous Descriptor
  Fetch Engine with Chaining Support"; `channel_idle` input; descriptor-address
  FIFO; `w_should_chain` / `w_next_addr_valid`; `cfg_addr0/1_base/limit`
  range checks; APB-in-progress gate. The pre-beats `rtl/fub/descriptor_engine.sv`
  carries the same.
- Test: `test_descriptor_chaining` in `dv/tbclasses/descriptor_engine_tb.py`,
  run from `dv/tests/fub_beats/test_descriptor_engine_beats.py`.
