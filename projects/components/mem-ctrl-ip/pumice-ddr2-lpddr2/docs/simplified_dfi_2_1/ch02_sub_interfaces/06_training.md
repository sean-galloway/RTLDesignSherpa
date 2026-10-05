# Training Interface

DFI 2.1 provides a training interface for read leveling and write leveling.
Read leveling covers both data eye training and gate training. Write leveling
is specific to DDR3. The interface is optional overall, but once a PHY declares
support for a training operation, the MC must support all three defined modes
for that operation.

## Training support modes

Each training capability is announced by a 2-bit mode signal:

| Encoding | Mode |
| --- | --- |
| 2'b00 | Not supported |
| 2'b01 | MC Evaluation: MC enables logic, reads results, adjusts delays |
| 2'b10 | PHY Evaluation: MC enables logic, PHY evaluates and sets delays |
| 2'b11 | PHY Independent: PHY performs training without MC involvement |
: Training mode encodings

The MC must be able to operate with any of these modes; the PHY typically
supports only one.

## Read leveling signals

| Signal | Direction | What it does |
| --- | --- | --- |
| dfi_rdlvl_req | PHY -> MC | PHY asks to run data eye training. |
| dfi_rdlvl_gate_req | PHY -> MC | PHY asks to run gate training. |
| dfi_rdlvl_mode | PHY -> MC | Announces data eye training support mode. |
| dfi_rdlvl_gate_mode | PHY -> MC | Announces gate training support mode. |
| dfi_rdlvl_en | MC -> PHY | Enables data eye training; also acknowledges `dfi_rdlvl_req`. |
| dfi_rdlvl_gate_en | MC -> PHY | Enables gate training; also acknowledges `dfi_rdlvl_gate_req`. |
| dfi_rdlvl_cs_n | MC -> PHY | Chip select active during read leveling. |
| dfi_rdlvl_edge | MC -> PHY | Selects positive or negative DQS edge for training. |
| dfi_rdlvl_delay_X | MC -> PHY | Per-slice delay value for data eye training. |
| dfi_rdlvl_gate_delay_X | MC -> PHY | Per-slice delay value for gate training. |
| dfi_rdlvl_load | MC -> PHY | One-cycle pulse when delay values have been updated. |
| dfi_rdlvl_resp | PHY -> MC | Training result or completion indication. |
: Read leveling signals

For LPDDR2, `dfi_rdlvl_resp` is used only for gate training in MC Evaluation
mode, not for data eye training. For DDR3 it carries sampled DQ level or gate
value.

## Write leveling signals

| Signal | Direction | What it does |
| --- | --- | --- |
| dfi_wrlvl_req | PHY -> MC | PHY asks to run write leveling. |
| dfi_wrlvl_mode | PHY -> MC | Announces write leveling support mode. |
| dfi_wrlvl_en | MC -> PHY | Enables write leveling; also acknowledges `dfi_wrlvl_req`. |
| dfi_wrlvl_cs_n | MC -> PHY | Chip select active during write leveling. |
| dfi_wrlvl_delay_X | MC -> PHY | Per-slice write DQS delay value. |
| dfi_wrlvl_load | MC -> PHY | One-cycle pulse when delay values have been updated. |
| dfi_wrlvl_strobe | MC -> PHY | Triggers the PHY write leveling strobe. |
| dfi_wrlvl_resp | PHY -> MC | Completion or sampled DQ result. |
: Write leveling signals

Write leveling is a DDR3-specific function. A system that does not support
DDR3 write leveling does not need these signals.

## Key timing parameters

| Parameter | Meaning |
| --- | --- |
| trdlvl_resp / twrlvl_resp | Maximum cycles from request to MC enable assertion. |
| trdlvl_en / twrlvl_en | Minimum cycles from enable to first load or command. |
| trdlvl_load / twrlvl_load | Minimum cycles from delay update to next load. |
| trdlvl_dll / twrlvl_dll | Minimum cycles from load to next read or strobe. |
| trdlvl_resplat / twrlvl_resplat | Maximum cycles from command/strobe to valid response. |
| trdlvl_max / twrlvl_max | Maximum cycles the MC waits for a PHY Evaluation response. |
| trdlvl_rr | Minimum command-to-command delay for read leveling reads. |
| twrlvl_ww | Minimum strobe-to-strobe delay for write leveling. |
: Training timing parameters

**Source:** DFI Specification v2.1.1 sections 3.6, 4.10
