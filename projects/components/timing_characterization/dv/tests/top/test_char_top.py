"""
Test runner for char_top timing characterization top-level wrapper.

Verifies that the configurable char_top module operates correctly with
various feature-enable combinations. The test replicates the 32-bit
Galois LFSR in Python so it can predict the exact inputs each FUB
receives and validate functional correctness cycle-by-cycle.

Validated outputs (functional correctness, not just toggle):
  - carry_chain:      o_carry == registered(a + b)
  - multiplier_tree:  o_mult  == registered(a * b)
  - inverter_chain:   o_inverter == polarity(lfsr[0]) based on chain length
  - gray_counter:     o_gray_code == o_gray_bin ^ (o_gray_bin >> 1)

Toggle-checked outputs (tree structure too complex to replicate exactly):
  - nand_chain, xor_tree, mux_tree: must produce >1 distinct value

Disabled-output checks:
  - All disabled features must hold at 0
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import (
    TimingCharTB, lfsr_step, lfsr_sequence, bit,
)


# =========================================================================
# CocoTB test functions
# =========================================================================

@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_char_top(dut):
    """Integration test: validate functional correctness of enabled FUBs."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    # ------------------------------------------------------------------
    # Read feature-enable and sizing parameters from DUT
    # ------------------------------------------------------------------
    en_nand      = int(dut.EN_NAND_TREE.value)
    en_inverter  = int(dut.EN_INVERTER_CHAIN.value)
    en_xor       = int(dut.EN_XOR_TREE.value)
    en_carry     = int(dut.EN_CARRY_CHAIN.value)
    en_mult      = int(dut.EN_MULTIPLIER.value)
    en_mux       = int(dut.EN_MUX_TREE.value)
    en_queue     = int(dut.EN_QUEUE_DEPTH.value)
    en_clk_div   = int(dut.EN_CLK_DIVIDER.value)
    en_gray      = int(dut.EN_GRAY_COUNTER.value)

    carry_width  = int(dut.CARRY_WIDTH.value)
    mult_width   = int(dut.MULT_WIDTH.value)
    inv_count    = int(dut.INVERTER_COUNT.value)
    gray_width   = int(dut.GRAY_WIDTH.value)

    dut._log.info(
        f"Config: nand={en_nand} inv={en_inverter} xor={en_xor} carry={en_carry} "
        f"mult={en_mult} mux={en_mux} queue={en_queue} clkdiv={en_clk_div} gray={en_gray}"
    )
    dut._log.info(
        f"Sizing: carry_w={carry_width} mult_w={mult_width} inv_cnt={inv_count} gray_w={gray_width}"
    )

    # ------------------------------------------------------------------
    # Seed the LFSR and build the Python reference model
    # ------------------------------------------------------------------
    lfsr_seed = 0xCAFE_BABE
    dut.i_seed_valid.value = 1
    dut.i_seed_data.value = lfsr_seed
    await RisingEdge(dut.clk)
    dut.i_seed_valid.value = 0

    # After seed_valid, the LFSR loads the seed on that rising edge.
    # On the next rising edge it starts stepping.
    # Build a long enough LFSR trace for the entire test.
    # lfsr_states[0] = seed (loaded at seed edge)
    # lfsr_states[1] = first step (available on the NEXT rising edge)
    total_cycles = 300
    lfsr_states = lfsr_sequence(lfsr_seed, total_cycles + 10)

    # Let the pipeline flush: we need a few cycles before outputs are valid.
    # Pipeline: LFSR -> input_flop (1 cycle) -> comb -> output_flop (1 cycle) = 2 cycles
    settle_cycles = 20
    await ClockCycles(dut.clk, settle_cycles)

    # ------------------------------------------------------------------
    # Phase 1: Functional validation of carry_chain and multiplier_tree
    # ------------------------------------------------------------------
    # These are the easiest to validate because their function is just
    # addition / multiplication of the LFSR-derived inputs.
    #
    # In char_top, the LFSR bits are mapped to carry/mult inputs:
    #   carry_a[b] = r_lfsr[b % 32]
    #   carry_b[b] = r_lfsr[(b + 16) % 32]
    #   mult_a[b]  = r_lfsr[b % 32]
    #   mult_b[b]  = r_lfsr[(b + 16) % 32]
    #
    # The pipeline is: LFSR updates -> input flop captures LFSR -> comb -> output flop
    # So output at cycle T reflects LFSR at cycle T-2.

    carry_mask = (1 << (carry_width + 1)) - 1  # carry output is WIDTH+1 bits
    mult_mask  = (1 << (2 * mult_width)) - 1

    carry_mismatches = 0
    mult_mismatches = 0
    inv_mismatches = 0
    gray_mismatches = 0
    check_count = 200

    # Sets for toggle checks on tree-based outputs
    nand_vals = set()
    xor_vals = set()
    mux_vals = set()
    queue_data_vals = set()
    queue_valid_vals = set()
    clk_div_vals = set()

    for cyc in range(check_count):
        await RisingEdge(dut.clk)

        # The output at this rising edge reflects the LFSR state from 3 edges ago:
        #   Edge N:   r_lfsr updates (LFSR state N)
        #   Edge N+1: r_input_a/b captures combinational from r_lfsr (state N)
        #   Edge N+2: r_out_flops captures sum/product of r_input_a/b
        # So output sampled after await RisingEdge at cycle (settle+cyc+1)
        # reflects lfsr_states[settle+cyc+1-3] = lfsr_states[settle+cyc-2].
        lfsr_idx = settle_cycles + cyc - 2
        if lfsr_idx < 0 or lfsr_idx >= len(lfsr_states):
            continue
        lfsr_val = lfsr_states[lfsr_idx]

        # --- Carry chain validation ---
        if en_carry:
            # Build expected inputs from LFSR
            carry_a = 0
            carry_b = 0
            for b in range(carry_width):
                carry_a |= (bit(lfsr_val, b % 32) << b)
                carry_b |= (bit(lfsr_val, (b + 16) % 32) << b)

            expected_carry = (carry_a + carry_b) & carry_mask
            actual_carry = int(dut.o_carry.value) & carry_mask

            if actual_carry != expected_carry:
                carry_mismatches += 1
                if carry_mismatches <= 3:
                    dut._log.warning(
                        f"carry mismatch cyc={cyc}: a=0x{carry_a:x} b=0x{carry_b:x} "
                        f"exp=0x{expected_carry:x} got=0x{actual_carry:x} lfsr=0x{lfsr_val:08x}"
                    )

        # --- Multiplier validation ---
        if en_mult:
            mult_a = 0
            mult_b = 0
            for b in range(mult_width):
                mult_a |= (bit(lfsr_val, b % 32) << b)
                mult_b |= (bit(lfsr_val, (b + 16) % 32) << b)

            expected_mult = (mult_a * mult_b) & mult_mask
            actual_mult = int(dut.o_mult.value) & mult_mask

            if actual_mult != expected_mult:
                mult_mismatches += 1
                if mult_mismatches <= 3:
                    dut._log.warning(
                        f"mult mismatch cyc={cyc}: a=0x{mult_a:x} b=0x{mult_b:x} "
                        f"exp=0x{expected_mult:x} got=0x{actual_mult:x}"
                    )

        # --- Inverter chain validation ---
        if en_inverter:
            inv_input = bit(lfsr_val, 0)
            # Even number of inverters = same polarity, odd = inverted
            if inv_count % 2 == 0:
                expected_inv = inv_input
            else:
                expected_inv = 1 - inv_input

            actual_inv = int(dut.o_inverter.value) & 1
            if actual_inv != expected_inv:
                inv_mismatches += 1
                if inv_mismatches <= 3:
                    dut._log.warning(
                        f"inv mismatch cyc={cyc}: input={inv_input} inv_cnt={inv_count} "
                        f"exp={expected_inv} got={actual_inv}"
                    )

        # --- Gray counter validation ---
        # gray_counter_chain has its own internal counter, not driven by LFSR
        # directly. But we CAN validate that gray = bin ^ (bin >> 1).
        if en_gray:
            actual_bin  = int(dut.o_gray_bin.value) & ((1 << gray_width) - 1)
            actual_gray = int(dut.o_gray_code.value) & ((1 << gray_width) - 1)
            expected_gray = actual_bin ^ (actual_bin >> 1)
            if actual_gray != expected_gray:
                gray_mismatches += 1
                if gray_mismatches <= 3:
                    dut._log.warning(
                        f"gray mismatch cyc={cyc}: bin=0x{actual_bin:x} "
                        f"exp_gray=0x{expected_gray:x} got=0x{actual_gray:x}"
                    )

        # --- Toggle collection for tree-based outputs ---
        if en_nand:
            nand_vals.add(int(dut.o_nand.value))
        if en_xor:
            xor_vals.add(int(dut.o_xor.value))
        if en_mux:
            mux_vals.add(int(dut.o_mux.value))
        if en_queue:
            queue_data_vals.add(int(dut.o_queue_data.value))
            queue_valid_vals.add(int(dut.o_queue_valid.value))
        if en_clk_div:
            clk_div_vals.add(int(dut.o_clk_div.value))

    # ------------------------------------------------------------------
    # Phase 2: Report results
    # ------------------------------------------------------------------
    errors = []

    # Functional checks
    if en_carry:
        if carry_mismatches > 0:
            errors.append(f"carry_chain: {carry_mismatches}/{check_count} mismatches")
            dut._log.error(f"FAIL: carry_chain {carry_mismatches} mismatches")
        else:
            dut._log.info(f"PASS: carry_chain {check_count} cycles verified")

    if en_mult:
        if mult_mismatches > 0:
            errors.append(f"multiplier: {mult_mismatches}/{check_count} mismatches")
            dut._log.error(f"FAIL: multiplier {mult_mismatches} mismatches")
        else:
            dut._log.info(f"PASS: multiplier {check_count} cycles verified")

    if en_inverter:
        if inv_mismatches > 0:
            errors.append(f"inverter_chain: {inv_mismatches}/{check_count} mismatches")
            dut._log.error(f"FAIL: inverter_chain {inv_mismatches} mismatches")
        else:
            dut._log.info(f"PASS: inverter_chain {check_count} cycles verified")

    if en_gray:
        if gray_mismatches > 0:
            errors.append(f"gray_counter: {gray_mismatches}/{check_count} mismatches")
            dut._log.error(f"FAIL: gray_counter {gray_mismatches} mismatches")
        else:
            dut._log.info(f"PASS: gray_counter {check_count} cycles verified (gray == bin ^ bin>>1)")

    # Toggle checks for tree-based and complex outputs
    def check_toggle(name, enabled, val_set):
        if enabled:
            if len(val_set) <= 1:
                errors.append(f"{name}: ENABLED but output stuck at {val_set}")
                dut._log.error(f"FAIL: {name} enabled but stuck at {val_set}")
            else:
                dut._log.info(f"PASS: {name} toggled, saw {len(val_set)} distinct values")
        else:
            pass  # disabled checks done below

    check_toggle("o_nand", en_nand, nand_vals)
    check_toggle("o_xor",  en_xor,  xor_vals)
    check_toggle("o_mux",  en_mux,  mux_vals)
    check_toggle("o_clk_div", en_clk_div, clk_div_vals)

    # Queue: check data flows through
    if en_queue:
        if len(queue_data_vals) <= 1 and len(queue_valid_vals) <= 1:
            errors.append("o_queue: ENABLED but both data and valid stuck")
            dut._log.error("FAIL: queue enabled but all outputs stuck")
        else:
            dut._log.info(
                f"PASS: queue toggled, data={len(queue_data_vals)} vals, "
                f"valid={len(queue_valid_vals)} vals"
            )

    # ------------------------------------------------------------------
    # Phase 3: Disabled-feature checks
    # ------------------------------------------------------------------
    # Sample a few more cycles and verify disabled outputs are zero
    disabled_errors = []
    for _ in range(20):
        await RisingEdge(dut.clk)

        if not en_nand and int(dut.o_nand.value) != 0:
            disabled_errors.append("o_nand non-zero while disabled")
        if not en_inverter and int(dut.o_inverter.value) != 0:
            disabled_errors.append("o_inverter non-zero while disabled")
        if not en_xor and int(dut.o_xor.value) != 0:
            disabled_errors.append("o_xor non-zero while disabled")
        if not en_carry and int(dut.o_carry.value) != 0:
            disabled_errors.append("o_carry non-zero while disabled")
        if not en_mult and int(dut.o_mult.value) != 0:
            disabled_errors.append("o_mult non-zero while disabled")
        if not en_mux and int(dut.o_mux.value) != 0:
            disabled_errors.append("o_mux non-zero while disabled")
        if not en_queue:
            if int(dut.o_queue_data.value) != 0 or int(dut.o_queue_valid.value) != 0:
                disabled_errors.append("o_queue non-zero while disabled")
        if not en_clk_div and int(dut.o_clk_div.value) != 0:
            disabled_errors.append("o_clk_div non-zero while disabled")
        if not en_gray:
            if int(dut.o_gray_bin.value) != 0 or int(dut.o_gray_code.value) != 0:
                disabled_errors.append("o_gray non-zero while disabled")

    if disabled_errors:
        # Deduplicate
        unique_disabled = sorted(set(disabled_errors))
        for e in unique_disabled:
            errors.append(f"disabled: {e}")
            dut._log.error(f"FAIL: {e}")
    else:
        dut._log.info("PASS: all disabled outputs held at 0")

    # ------------------------------------------------------------------
    # Final verdict
    # ------------------------------------------------------------------
    assert len(errors) == 0, (
        f"char_top had {len(errors)} error(s):\n" + "\n".join(errors)
    )
    dut._log.info(f"char_top integration test PASSED ({check_count} cycles validated)")


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_char_top_lfsr_seed(dut):
    """Test that LFSR seeding produces deterministic outputs."""
    tb = TimingCharTB(dut)
    await tb.setup_clocks_and_reset()

    en_carry = int(dut.EN_CARRY_CHAIN.value)
    en_mult  = int(dut.EN_MULTIPLIER.value)

    # -- Run 1: seed and capture --
    dut.i_seed_valid.value = 1
    dut.i_seed_data.value = 0x1234_5678
    await RisingEdge(dut.clk)
    dut.i_seed_valid.value = 0

    await ClockCycles(dut.clk, 80)
    snap1_carry = int(dut.o_carry.value) if en_carry else 0
    snap1_mult  = int(dut.o_mult.value)  if en_mult  else 0

    # -- Run 2: re-seed with same value and capture --
    dut.i_seed_valid.value = 1
    dut.i_seed_data.value = 0x1234_5678
    await RisingEdge(dut.clk)
    dut.i_seed_valid.value = 0

    await ClockCycles(dut.clk, 80)
    snap2_carry = int(dut.o_carry.value) if en_carry else 0
    snap2_mult  = int(dut.o_mult.value)  if en_mult  else 0

    errors = []
    if en_carry and snap1_carry != snap2_carry:
        errors.append(
            f"carry non-deterministic: first=0x{snap1_carry:x} second=0x{snap2_carry:x}"
        )
    if en_mult and snap1_mult != snap2_mult:
        errors.append(
            f"mult non-deterministic: first=0x{snap1_mult:x} second=0x{snap2_mult:x}"
        )

    if not en_carry and not en_mult:
        dut._log.info("LFSR seed test skipped (carry and mult both disabled)")
    else:
        assert len(errors) == 0, "LFSR seed non-deterministic:\n" + "\n".join(errors)
        dut._log.info(
            f"LFSR seed determinism PASSED "
            f"(carry=0x{snap1_carry:x}, mult=0x{snap1_mult:x})"
        )


# =========================================================================
# Test configurations
# =========================================================================

ALL_ENABLES = [
    'EN_NAND_TREE', 'EN_INVERTER_CHAIN', 'EN_XOR_TREE', 'EN_CARRY_CHAIN',
    'EN_MULTIPLIER', 'EN_MUX_TREE', 'EN_QUEUE_DEPTH', 'EN_CLK_DIVIDER',
    'EN_GRAY_COUNTER',
]


def _make_config(tag, enabled_features, **extra_params):
    """Build a parameter dict with feature enables and sizing overrides."""
    params = {en: (1 if en in enabled_features else 0) for en in ALL_ENABLES}
    params.update({
        'NAND_LEVELS': 3,
        'INVERTER_COUNT': 16,
        'XOR_LEVELS': 3,
        'MUX_LEVELS': 3,
        'NUM_FLOPS': 64,
        'CARRY_WIDTH': 8,
        'MULT_WIDTH': 8,
        'MULT_TYPE': 0,
        'GRAY_WIDTH': 8,
        'FIFO_DATA_WIDTH': 8,
        'FIFO_DEPTH': 4,
        'CLK_DIV_STAGES': 2,
        'CLK_DIV_CW': 8,
        'CLK_DIV_PICKOFF': 1,
    })
    params.update(extra_params)
    return (tag, params)


def generate_char_top_configs():
    """Generate test configurations with a good mix of enable combinations."""
    configs = []

    # --- Full integration: all 9 features enabled ---
    configs.append(_make_config(
        'all_enabled',
        ALL_ENABLES,
    ))

    # --- Trees only: nand + xor + mux ---
    configs.append(_make_config(
        'trees_only',
        ['EN_NAND_TREE', 'EN_XOR_TREE', 'EN_MUX_TREE'],
    ))

    # --- Datapath only: carry + multiplier ---
    configs.append(_make_config(
        'datapath_only',
        ['EN_CARRY_CHAIN', 'EN_MULTIPLIER'],
    ))

    # --- Counters + clock: gray counter + clock divider ---
    configs.append(_make_config(
        'counters_clk',
        ['EN_GRAY_COUNTER', 'EN_CLK_DIVIDER'],
    ))

    # --- Single: NAND tree alone ---
    configs.append(_make_config(
        'nand_only',
        ['EN_NAND_TREE'],
    ))

    # --- Single: queue depth alone ---
    configs.append(_make_config(
        'queue_only',
        ['EN_QUEUE_DEPTH'],
    ))

    # --- Mixed odd set: inverter + carry + gray ---
    configs.append(_make_config(
        'inv_carry_gray',
        ['EN_INVERTER_CHAIN', 'EN_CARRY_CHAIN', 'EN_GRAY_COUNTER'],
    ))

    # --- All except multiplier (avoids DSP, fast compile) ---
    configs.append(_make_config(
        'all_except_mult',
        [e for e in ALL_ENABLES if e != 'EN_MULTIPLIER'],
    ))

    # --- All except queue (no FIFO, purely combinational focus) ---
    configs.append(_make_config(
        'all_except_queue',
        [e for e in ALL_ENABLES if e != 'EN_QUEUE_DEPTH'],
    ))

    # --- Mux + multiplier + queue (data-heavy) ---
    configs.append(_make_config(
        'data_heavy',
        ['EN_MUX_TREE', 'EN_MULTIPLIER', 'EN_QUEUE_DEPTH'],
    ))

    return configs


char_top_configs = generate_char_top_configs()


# =========================================================================
# Pytest wrappers
# =========================================================================

@pytest.mark.parametrize(
    "tag, rtl_params",
    char_top_configs,
    ids=[c[0] for c in char_top_configs],
)
def test_char_top(request, tag, rtl_params, test_level):
    """Pytest wrapper for char_top integration test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_top': '../../../../rtl/top',
    })

    dut_name = "char_top"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    test_name_plus_params = f"test_{dut_name}_{tag}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name_plus_params}.xml'),
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
    }

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "-Wno-TIMESCALEMOD", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_char_top",
            parameters=rtl_params,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"char_top [{tag}] test failed: {e}")
        print(f"Logs: {log_path}")
        raise


@pytest.mark.parametrize(
    "tag, rtl_params",
    [char_top_configs[0]],  # Only run LFSR seed test on all_enabled config
    ids=["all_enabled"],
)
def test_char_top_lfsr_seed(request, tag, rtl_params, test_level):
    """Pytest wrapper for char_top LFSR seed determinism test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_top': '../../../../rtl/top',
    })

    dut_name = "char_top"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/timing_characterization/rtl/filelists/char_top.f'
    )

    test_name_plus_params = f"test_{dut_name}_lfsr_seed_{tag}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name_plus_params}.xml'),
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
    }

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "-Wno-TIMESCALEMOD", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_char_top_lfsr_seed",
            parameters=rtl_params,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"char_top LFSR seed [{tag}] test failed: {e}")
        print(f"Logs: {log_path}")
        raise
