# VCD2Wavedrom2

## Overview

`VCD2Wavedrom2` is a Python script for converting VCD (Value Change Dump) files to WaveDrom JSON format. It provides a range of features to process VCD files, group waveforms into buses, automatically configure waveform settings, and generate WaveDrom-compatible JSON data.

## Features

- Converts VCD files to WaveDrom format.
- Supports automatic configuration based on VCD file content.
- Groups waveforms into buses.
- Homogenizes waveforms by adding missing samples.
- Provides options for manual configuration through command-line arguments.
- Parses GTKWave save files for advanced signal grouping.

## Usage

```sh
vcd2wavedrom2.py [-h] -i INPUT [-o OUTPUT] [-c CONFIGFILE]
[-r SAMPLERATE] [-t MAXTIME] [-f OFFSET] [-z HSCALE]
[--top] [-m MAKECONFIG] [-g GTKW]
```

### Arguments

- `-i, --input`: Path to the input VCD file.
- `-o, --output`: Path for the output Wavedrom JSON file.
- `-c, --config`: Path to a JSON configuration file.
- `-r, --samplerate`: Sample rate of WaveDrom.
- `-t, --maxtime`: Maximum length of time for WaveDrom.
- `-f, --offset`: Time offset from the start of the VCD.
- `-z, --hscale`: Horizontal scale for WaveDrom.
- `--top`: Flag to only output top-level signals.
- `-m, --makeconfig`: Generate a configuration file from the VCD file.
- `-g, --gtkw`: Path to a GTKWave save file for signal grouping.

#### --config Usage

Use the --config option to create a base line config.json file from the vcd. This will include all of the signals and will correctly associate the clocks and will assign the sample time to the slowest clock. Once this json file is created, it can be pared down and adjusted as needed.

#### GTKW Usage

If you need to have hierarchical labels on the left hand side of the wavedrom, create dump.gtkw like this:

```python
fifo_async.i_wr_clk
-Write Port
fifo_async.i_write
@22
--Write Data
fifo_async.i_wr_data[7:0]
@28
fifo_async.ow_wr_full
@29
&&
fifo_async.ow_wr_almost_full
```

The -Write Port creates the first level of title. The --Write Data is the second level within -Write Port. The && takes the hierarch back to the top and ow_wr_almost_full does not have any label associated with it.

## Methods

### `__init__(self, config)`

Initializes the VCD2Wavedrom2 instance with configuration settings.

### `replacevalue(self, wave, strval)`

Replaces the value of a waveform based on configuration settings.

### `group_buses(self, vcd_dict, slots)`

Groups waveforms into buses based on naming conventions.

### `auto_config_waves(self, vcd_dict)`

Automatically configures waveform settings based on the VCD file.

### `homogenize_waves(self, vcd_dict, timescale)`

Homogenizes waveforms by adding missing samples and adjusting the time scale.

### `includewave(self, wave)`

Checks if a waveform should be included based on configuration settings.

### `clockvalue(self, wave, digit)`

Returns the clock value for a waveform digit based on configuration settings.

### `samplenow(self, tick)`

Checks if a sample should be taken at the given tick based on configuration settings.

### `appendconfig(self, wave)`

Appends additional configuration settings to a waveform.

### `find_max_time_in_vcd(vcd)`

Finds the maximum time value in the VCD file.

### `generate_config(self, output_config_file)`

Generates a configuration file based on the VCD file.

### `parse_gtkw_file(self, gtkw_file)`

Parses a GTKWave save file and returns the structure of groups and signals.

### `build_wave_drom_structure(self, result_structure, signal_rec_dict)`

Builds the WaveDrom structure based on the group structure and signal records.

### `dump_wavedrom(self, vcd_dict, vcd_dict_types, timescale, result_structure)`

Dumps the WaveDrom JSON structure based on the VCD data and configuration settings.

### `execute(self, auto, group_structure)`

Executes the VCD to WaveDrom conversion process.

## Example Usage

Run the script from the command line with the desired options. For example:

```sh
# Step 0: cd to the area with the simulation
# Step 1: Create the config file
python3 $REPO_ROOT/bin/vcd2wavedrom2.py -i dump.vcd -m config.json

# Step 2: Generate the wavedrom file
python3 $REPO_ROOT/bin/vcd2wavedrom2.py -i dump.vcd -g debug.gtkw -c config.json  -o wavedrom.json
```

---

[Back to Scripts Index](index.md)
