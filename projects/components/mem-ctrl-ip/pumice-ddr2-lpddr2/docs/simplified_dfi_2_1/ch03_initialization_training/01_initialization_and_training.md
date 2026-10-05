# Initialization and Training

## Reset and initialization

DFI 2.1 does not dictate a full power-on reset sequence for the MC or the PHY.
It only defines when the PHY is ready to accept DFI traffic: when
`dfi_init_complete` asserts. Until then, command and status signals must be
held at their default values.

### Signals held at default until init_complete

The following signals must not change from their default until
`dfi_init_complete` asserts:

- `dfi_address` (except the LPDDR2 NOP requirement)
- `dfi_bank`, `dfi_cas_n`, `dfi_ras_n`, `dfi_we_n`
- `dfi_cke`, `dfi_cs_n`, `dfi_odt`, `dfi_reset_n`
- `dfi_wrdata_en`, `dfi_rddata_en`
- `dfi_rddata_dnv`, `dfi_rddata_valid`
- `dfi_ctrlupd_ack`, `dfi_ctrlupd_req`
- `dfi_phyupd_req`, `dfi_phyupd_ack`
- `dfi_dram_clk_disable`
- `dfi_parity_error`, `dfi_parity_in`
- `dfi_rdlvl_req`, `dfi_rdlvl_gate_req`, `dfi_rdlvl_en`, `dfi_rdlvl_gate_en`
- `dfi_rdlvl_load`, `dfi_wrlvl_en`, `dfi_wrlvl_load`, `dfi_wrlvl_req`, `dfi_wrlvl_strobe`
- `dfi_lp_ack`, `dfi_lp_req`

Signals with no meaningful default, such as `dfi_wrdata`, `dfi_wrdata_mask`,
`dfi_rddata`, `dfi_phyupd_type`, and the per-slice delay/response signals, do
not need a defined value during initialization.

### LPDDR2 special rule

For LPDDR2 the `dfi_address` bus must carry a NOP command until
`dfi_init_complete` asserts. The `dfi_bank`, `dfi_cas_n`, `dfi_ras_n`, and
`dfi_we_n` signals are unused and must remain at constant idle values.

### init_start handshake

`dfi_init_start` is optional. When used, it has two purposes:

1. At initialization it tells the PHY that `dfi_data_byte_disable` and/or
   `dfi_freq_ratio` are valid.
2. During normal operation it requests a frequency change.

If the PHY depends on the disable or ratio settings, it waits for
`dfi_init_start` before asserting `dfi_init_complete`. If not, it may assert
`dfi_init_complete` earlier. Either way, init is complete only when both
`dfi_init_start` and `dfi_init_complete` are high for at least one DFI clock.

### End-of-init ctrlupd_req

The MC must assert `dfi_ctrlupd_req` at the end of initialization, after all
required training, to indicate that initialization is complete. This is the
first update window the PHY sees.

### Initialization timing parameters

| Parameter | Meaning |
| --- | --- |
| tinit_complete | Maximum cycles from `dfi_init_start` de-assertion to `dfi_init_complete` re-assertion during frequency change. |
| tinit_start | Maximum cycles for PHY to de-assert `dfi_init_complete` after a frequency change request. |
: Initialization timing parameters

## Training operations

DFI 2.1 supports read leveling and write leveling. Read leveling is used by
both DDR3 and LPDDR2 systems; write leveling is DDR3-specific. The interface is
optional overall, but if a PHY declares support for a training operation, the
MC must support all three defined modes.

### Read leveling

Read leveling has two parts:

- Data eye training: centers the read DQS strobe in the DQ data eye.
- Gate training: places the DQS gate at the correct point in the read preamble.

For DDR3 both operations are used. For LPDDR2 the response signal
`dfi_rdlvl_resp` is used only for gate training in MC Evaluation mode; data eye
training is not supported via that path for LPDDR2.

### Write leveling

Write leveling aligns the write DQS to the memory clock. It is only relevant
for DDR3. The MC either evaluates the result itself and adjusts
`dfi_wrlvl_delay_X`, or it lets the PHY evaluate and set the delay internally.

### Responsibility modes

| Mode | MC role | PHY role |
| --- | --- | --- |
| MC Evaluation | Enables logic, reads response, writes delay values, pulses load | Provides sampled results |
| PHY Evaluation | Enables logic and waits for completion | Evaluates and sets delays |
| PHY Independent | None | Performs training autonomously |
: Training responsibility modes

The MC must be able to operate in all three modes, even though a given PHY
only supports one.

### Training is not required at init

The DFI specification does not require any training before `dfi_init_complete`
asserts. The PHY must guarantee the integrity of the address and control path
before declaring init complete, but it may perform training later under its own
control or at the MC's request.

**Source:** DFI Specification v2.1.1 sections 3.5, 3.6, 4.1, 4.10
