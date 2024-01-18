#!/usr/bin/python3

import contextlib
import sys
import os
import argparse
import json
import re
from collections import defaultdict
import pprint
pp = pprint.PrettyPrinter(indent=4)

from vcdvcd.vcdvcd import VCDVCD

from math import floor, ceil

import pint
import pstats
import cProfile


# pint examples
# # Initialize pint's unit registry
# ureg = pint.UnitRegistry()

# # Timescale string
# timescale = "1ps"

# # Parse the timescale string into a pint Quantity object
# timescale_quantity = ureg(timescale)

# # Extract the magnitude
# magnitude = timescale_quantity.magnitude

# # Extract the unit
# unit = timescale_quantity.units

# # Print the extracted magnitude and unit
# print(f"Magnitude: {magnitude}, Unit: {unit}")


def convert_timescale_to_new_units(value, current_timescale, new_unit, new_base):
    ureg = pint.UnitRegistry()

    # Extract the unit part from the current timescale
    current_unit = re.findall(r'[a-zA-Z]+', current_timescale)[0]

    # Convert the value to the current timescale unit
    value_in_current_units = value * ureg(current_unit)

    return f'{round(value_in_current_units.to(ureg(new_unit)).magnitude)}{new_base}'


def calculate_sampling_points(vcd_timescale, target_interval, maxtime):
    ureg = pint.UnitRegistry()

    # Convert timescale, interval, and maxtime to seconds
    timescale_sec = ureg(vcd_timescale).to(ureg.second).magnitude
    interval_sec = ureg(target_interval).to(ureg.second).magnitude
    maxtime_sec = ureg(maxtime).to(ureg.second).magnitude

    # Calculate the number of sample points
    num_points = int(maxtime_sec / interval_sec)

    return [int(i * interval_sec / timescale_sec) for i in range(num_points + 1)]


class VCD2Wavedrom2:
    '''usage: vcd2wavedrom2.py [-h] -i INPUT [-o OUTPUT] [-c CONFIGFILE] [-r SAMPLERATE] [-t MAXTIME] [-f OFFSET] [-z HSCALE] [--top] [-m CONFIGFILE] [-g FILE] [-n NAME] [-l]

    Transform VCD to wavedrom

    options:
    -h, --help        show this help message and exit
    -i INPUT, --input INPUT
                    Input VCD file
    -o OUTPUT, --output OUTPUT
                    Output Wavedrom file
    -c CONFIGFILE, --config CONFIGFILE
                    Config file
    -r SAMPLERATE, --samplerate SAMPLERATE
                    Sample rate of wavedrom
    -t MAXTIME, --maxtime MAXTIME
                    Length of time for wavedrom
    -f OFFSET, --offset OFFSET
                    Time offset from start of VCD
    -z HSCALE, --hscale HSCALE
                    Horizontal scale
    --top             Only output the top level signals
    -m CONFIGFILE, --makeconfig CONFIGFILE
                    Generate config file from VCD file
    -g FILE, --gtkw FILE  Path to gtkw file for signal grouping
    -n NAME, --name NAME  The title for the waveform
    -l, --line        Enable or disable line option

    Converts VCD (Value Change Dump) files to WaveDrom JSON format.
    
    **Methods**
    
    - `__init__(self, config)`: Initializes the VCD2Wavedrom2 instance with the given configuration.
    - `replacevalue(self, wave, strval)`: Replaces the value of a waveform based on the configuration settings.
    - `extract_bus_names_and_widths(self, vcd_dict)`: Extracts bus names and widths from the VCD dictionary.
    - `create_hex_from_bits(self, buses, buswidth, vcd_dict, slots)`: Creates hexadecimal values from bus bits.
    - `update_bus_waveform(self, bus, strval)`: Updates the waveform of a bus with a new value.
    - `group_buses(self, vcd_dict, slots)`: Groups the waveforms into buses based on the bus naming conventions.
    - `homogenize_waves(self, vcd_dict, timescale)`: Homogenizes the waveforms by adding missing samples and adjusting the time scale.
    - `includewave(self, wave)`: Checks if a waveform should be included based on the configuration settings.
    - `clockvalue(self, wave, digit)`: Returns the clock value for a waveform digit based on the configuration settings.
    - `samplenow(self, tick)`: Checks if a sample should be taken at the given tick based on the configuration settings.
    - `appendconfig(self, wave)`: Appends additional configuration settings to a waveform.
    - `find_max_time_in_vcd(vcd)`: Finds the maximum time value in the VCD file.
    - `generate_config(self, output_config_file)`: Generates a configuration file based on the VCD file.
    - `parse_gtkw_file(self, gtkw_file)`: Parses a GTKWave save file and returns the structure of groups and signals.
    - `build_wave_drom_structure(self, result_structure, signal_rec_dict, max_cycles)`: Builds the WaveDrom structure based on the group structure and signal records.
    - `remove_grouped_signals(self, buses, vcd_dict)`: Removes signals that have been grouped into buses from the VCD dictionary.
    - `create_signal_records(self, vcd_dict, vcd_dict_types)`: Creates waveform records for the remaining signals in the VCD dictionary.
    - `create_waveform_record(self, wave, waveform_data, vcd_dict_types)`: Creates a waveform record for a single signal.
    - `determine_phase(self, signal_suffix)`: Determines the phase based on the signal suffix.
    - `process_signal_value(self, signal_rec, j, isbus, lastval, wave_type)`: Processes a value of the waveform.
    - `finalize_wave_drom_structure(self, result_structure, signal_rec_dict)`: Finalizes the WaveDrom structure by determining max cycles and applying configuration.
    - `dump_wavedrom(self, vcd_dict, vcd_dict_types, timescale, result_structure)`: Dumps the WaveDrom JSON structure based on the VCD data and configuration settings.
    - `execute(self, group_structure)`: Executes the VCD to WaveDrom conversion process.
    '''
    busregex = re.compile(r'(.+)(\[|\()(\d+)(\]|\))')
    busregex2 = re.compile(r'(.+)\[(\d):(\d)\]')
    config = {}
    bit_open = None
    bit_close = None


    def __init__(self, config):
        self.config = config


    def replacevalue(self, wave, strval):
        """
        Replaces the value of a waveform based on the configuration settings.
    
        Args:
            wave (str): The name of the waveform.
            strval (str): The original value of the waveform.
    
        Returns:
            str: The replaced value of the waveform, if a replacement is defined in the configuration settings. Otherwise, returns the original value.
    
        """
    
        if 'replace' in self.config and \
                        wave in self.config['replace'] and strval in self.config['replace'][wave]:
            return self.config['replace'][wave][strval]
        return strval


    def extract_bus_names_and_widths(self, vcd_dict):
        buses = {}
        buswidth = {}

        for wave in vcd_dict:
            result = self.busregex.match(wave)
            if result is not None and len(result.groups()) == 4:
                name = result.group(1)
                pos = int(result.group(3))
                self.bit_open = result.group(2)
                self.bit_close = ']' if self.bit_open == '[' else ')'
                if name not in buses:
                    buses[name] = {
                        'name': name,
                        'wave': '',
                        'data': []
                    }
                buswidth[name] = max(buswidth.get(name, 0), pos)
        
        return buses, buswidth


    def create_hex_from_bits(self, buses, buswidth, vcd_dict, slots):
        for wave in buses:
            for slot_idx in range(slots):
                slot = slots[slot_idx]
                if not self.samplenow(slot):
                    continue
                byte, strval = 0, ''
                for bit in range(buswidth[wave] + 1):
                    if bit % 8 == 0 and bit != 0:
                        strval = format(byte, 'X') + strval
                        byte = 0
                    val = vcd_dict[wave + self.bit_open + str(bit) + self.bit_close][slot_idx][1]
                    if val not in ['0', '1']:
                        byte = -1
                        break
                    byte += (2 ** (bit % 8)) * int(val)
                strval = format(byte, 'X') + strval
                self.update_bus_waveform(buses[wave], strval)
        return buses


    def update_bus_waveform(self, bus, strval):
        if strval == -1:
            bus['wave'] += 'x'
        else:
            strval = self.replacevalue(bus['name'], strval)
            if bus['data'] and bus['data'][-1] == strval:
                bus['wave'] += '.'
            else:
                bus['wave'] += '='
                bus['data'].append(strval)


    def group_buses(self, vcd_dict, slots):
        buses, buswidth = self.extract_bus_names_and_widths(vcd_dict)
        return self.create_hex_from_bits(buses, buswidth, vcd_dict, slots)




    def homogenize_waves(self, vcd_dict, sample_points):
        """
        Homogenizes the waveforms by adding missing samples and adjusting the time scale.

        Args:
            vcd_dict (dict): The dictionary containing the VCD waveforms.
            sample_points List[(int)]: The times in the vcd timescale format to sample the data.

        Returns:
            dict: The homogenized waveforms.
        """

        homogenized_dict = {}

        for wave, values in vcd_dict.items():
            homogenized_values = []
            last_val = 'x'
            val_idx = 0
            for point in sample_points:
                while val_idx < len(values) and values[val_idx][0] < point:
                    last_val = values[val_idx][1]
                    val_idx += 1
                homogenized_values.append((point, last_val))

            homogenized_dict[wave] = homogenized_values

        return homogenized_dict


    def includewave(self, wave):
        """
        Checks if a waveform should be included based on the configuration settings.
    
        Args:
            wave (str): The name of the waveform.
    
        Returns:
            bool: True if the waveform should be included, False otherwise.
    
        """
    
        if '__top__' in self.config['filter'] or ('top' in self.config and self.config['top']):
            return wave.count('.') <= 1
        elif '__all__' in self.config['filter'] or wave in self.config['filter']:
            return True
        return False


    def samplenow(self, tick):
        """
        Checks if a sample should be taken at the given tick based on the configuration settings.

        Args:
            tick (int): The tick value from the sample_points list
            common_units (str): Common unit to which all values are converted.

        Returns:
            bool: True if a sample should be taken at the tick, False otherwise.
        """
        # Convert offset, and samplerate to common units, these must be the same units as tick
        offset_in_common = self.config['offset_in_common']
        samplerate_in_common = self.config['samplerate_in_common']
        maxtime_in_common = self.config["maxtime_in_common"]
        # Perform the check
        return (tick - offset_in_common) >= 0 and \
                (tick- offset_in_common) % samplerate_in_common == 0 and \
                (tick < maxtime_in_common)


    def appendconfig(self, wave):
        """
        Appends additional configuration settings to a waveform.
    
        Args:
            wave (dict): The waveform dictionary.
    
        Returns:
            None
    
        """

        wavename = wave['name']
        if wavename in self.config['signal']:
            wave.update(self.config['signal'][wavename])


    @staticmethod
    def find_max_time_in_vcd(vcd):
        """
        Finds the maximum time value in the VCD file.
    
        Args:
            vcd (dict): The VCD data.
    
        Returns:
            int: The maximum time value found in the VCD file.
    
        """

        max_time = 0
        for signal in vcd:
            # Skip special keys like '$end'
            if signal.startswith('$'):
                continue

            # Iterate through time-value pairs and find the max time
            for tv_pair in vcd[signal].tv:
                time = tv_pair[0]  # The time is the first element in the pair
                max_time = max(max_time, time)

        return max_time

    @staticmethod
    def group_and_sort_signals(signals, hierarchy_list):
        # List to hold signals with their hierarchy depth
        signals_with_depth = []

        for signal in signals:
            if len(hierarchy_list) == 0:
                # If no hierarchies are provided, use hierarchy depth 0 for all signals
                signals_with_depth.append((0, signal))
            else:
                for hierarchy in hierarchy_list:
                    if hierarchy in signal:
                        # Determine hierarchy depth by counting the number of periods in the signal
                        hierarchy_depth = signal.count('.')
                        signals_with_depth.append((hierarchy_depth, signal))
                        break  # Break if the signal matches one of the hierarchies

        # Sort the signals first by hierarchy depth, then alphabetically
        signals_with_depth.sort(key=lambda x: (x[0], x[1]))

        # Extract sorted signals
        return [signal for depth, signal in signals_with_depth]


    def generate_config(self, output_config_file):
        # sourcery skip: low-code-quality
        """
        Generates a configuration file based on the VCD file.
    
        Args:
            output_config_file (str): The path to the output configuration file.
    
        Returns:
            None
    
        """

        # Load VCD file
        vcd = VCDVCD(vcd_string=self.config['input_text'])
        timescale = f"{int(vcd.timescale['magnitude'])}{vcd.timescale['unit']}"
        base_unit = vcd.timescale['unit']
        vcd = vcd.data
        # Initialize variables
        signals = set()
        clocks = set()
        slowest_clock_rate = float('inf')
        max_time = 0
        clock_periods = {}
    
        # Extract signals, clocks, and max time from VCD
        for signal in vcd:
            if signal != '$end':
                for sig in vcd[signal].references:
                    # signals.add(vcd[signal].references[0])
                    if '$' in sig:
                        continue
                    signals.add(sig)
    
                    # Identify clocks and determine slowest clock rate
                    if sig.endswith('clk'):
                        clocks.add(sig)
                        tv_pairs = vcd[signal].tv
                        if len(tv_pairs) > 1:
                            clock_period = tv_pairs[1][0] - tv_pairs[0][0]
                            slowest_clock_rate = min(slowest_clock_rate, clock_period)
                            full_clock_period = f'{2*clock_period}{base_unit}'
                            if sig not in clock_periods:
                                clock_periods[sig] = full_clock_period
    
                # Update max time
                last_tv_pair = vcd[signal].tv[-1]
                max_time = max(max_time, last_tv_pair[0])

        # Adjust sample rate based on slowest clock (if clocks were found)
        sample_rate = slowest_clock_rate if clocks else 1

        # Get the final list of sorted and grouped signals
        signals_final = self.group_and_sort_signals(signals, self.config['hierarchy_list'])
        clocks_final = self.group_and_sort_signals(list(clocks), self.config['hierarchy_list'])
        new_unit = '1ns'
        new_base = 'ns'
        # Convert samplerate and maxtime to the new unit
        samplerate_conv = convert_timescale_to_new_units(sample_rate, timescale, new_unit, new_base)
        maxtime_conv = convert_timescale_to_new_units(max_time, timescale, new_unit, new_base)
        if self.config['maxtime']:
            maxtime_conv = self.config['maxtime']
        clocks = [{'name': name, 'char': 'p', 'period': clock_periods[name]} for name in clocks_final]

        # Generate configuration dictionary
        config = {
            "signal": {},
            "filter": list(signals_final),
            "name": "The waveform title",
            "tock": 1,
            "replace": {},
            "offset": self.config['offset'],
            "samplerate": f'{samplerate_conv}',
            "clocks": clocks,
            "maxtime": f'{maxtime_conv}'
        }
    
        # Write configuration to file
        with open(output_config_file, 'w') as outfile:
            json.dump(config, outfile, indent=4)
    

    def parse_gtkw_file(self, gtkw_file):
        """
        Parses a GTKWave save file and returns the structure of groups and signals.
    
        Args:
            gtkw_file (str): The path to the GTKWave save file.
    
        Returns:
            list: A list representing the structure of groups and signals, where each group contains a label, signals, and level.
    
        """
    
        result_structure = []
        current_group = None
    
        with open(gtkw_file, 'r') as file:
            for line in file:
                line = line.strip()
                if line.startswith('@') or line.startswith('*') or line.startswith('['):
                    continue  # Skip markers and settings
    
                if line.startswith('&'):
                    # End current group and move up in the hierarchy
                    if current_group is not None:
                        result_structure.append(current_group)
                        current_group = None
                    continue
    
                if line.startswith('-'):
                    # New group
                    if current_group:
                        # Finish the current group before starting a new one
                        result_structure.append(current_group)
                    level = line.count('-')  # Determine the depth based on the number of '-'
                    label = line[level:].strip()
                    current_group = {'label': label, 'signals': [], 'level': level}
                else:
                    # Signal
                    if current_group is None:
                        # Standalone signal, create a default group for it
                        current_group = {'label': None, 'signals': [], 'level': 0}
                    current_group['signals'].append(line)
    
            # Append the last group if it exists
            if current_group:
                result_structure.append(current_group)
    
        return result_structure

    def build_wave_drom_structure(self, result_structure, signal_rec_dict, max_cycles):
        """
        Builds the WaveDrom structure based on the group structure and signal records.
    
        Args:
            result_structure (list): The structure of groups and signals.
            signal_rec_dict (dict): The dictionary containing the signal records.
    
        Returns:
            dict: The WaveDrom structure representing the grouped signals.
    
        """
        cycles_string =  ' '.join(str(i) for i in range(1, max_cycles+1))
        header = '' 
        # wave_drom_structure = { 'head':{'text':self.config['name'], 'tock':self.config['tock']}, 'signal': [{'name':'Cycles', 'wave':'='*max_cycles, 'data':cycles_string }], 'config':{'hscale': 1}}
        wave_drom_structure = { 'head':{'text':self.config['name'], 'tock':self.config['tock']}, 'signal': [], 'config':{'hscale': self.config['hscale']}}


        def process_group(group, wave_drom_list):
            """
            Processes a group and adds its signals to the WaveDrom list.
        
            Args:
                group (dict): The group dictionary.
                wave_drom_list (list): The WaveDrom list to add the group's signals to.
        
            Returns:
                None
        
            """

            group_signals = group['signals']
            level = group['level']
    
            # Create a list for the current group's content
            current_group_content = []
    
            # Add signals to the current group's content
            for signal in group_signals:
                current_group_content.append(signal_rec_dict.get(signal, {'name': signal, 'wave': 'x'}))
    
            # For subgroups (level > 0), add the group label and its content as a nested list
            if level > 0:
                wave_drom_list.append([group['label'], *current_group_content])
            else:
                # For top-level groups, just add the group's content without the label
                wave_drom_list.extend(current_group_content)
    
        for group in result_structure:
            if group['label'] is None:  # Standalone signals
                for signal in group['signals']:
                    wave_drom_structure['signal'].append(signal_rec_dict.get(signal, {'name': signal, 'wave': 'x'}))
            else:
                # Create a list for the new group content
                new_group_content = []
                process_group(group, new_group_content)
    
                # Add the new group to the WaveDrom structure
                if new_group_content:
                    if group['level'] == 0:
                        wave_drom_structure['signal'].append([group['label'], *new_group_content])
                    else:
                        wave_drom_structure['signal'].extend(new_group_content)
    
        return wave_drom_structure

    def remove_grouped_signals(self, buses, vcd_dict):
        """Removes signals that have been grouped into buses from vcd_dict.

        Args:
            buses (dict): The dictionary of buses.
            vcd_dict (dict): The dictionary containing the VCD waveforms.
        """
        for bus in buses:
            pattern = re.compile((((f"^{re.escape(bus)}" + "\\") + self.bit_open) + ".*"))
            vcd_dict_keys = list(vcd_dict.keys())  # Create a static list of keys to iterate over
            for wave in vcd_dict_keys:
                if pattern.match(wave) is not None:
                    del vcd_dict[wave]


    def create_signal_records(self, vcd_dict, vcd_dict_types, sample_points):
        """Creates waveform records for the remaining signals in vcd_dict."""
        signal_rec_dict = {}
        for wave in vcd_dict:
            if not self.includewave(wave):
                continue
            signal_rec = self.create_waveform_record(wave, vcd_dict[wave], vcd_dict_types, sample_points)
            signal_rec_dict[wave] = signal_rec
        return signal_rec_dict


    def find_closest_data_point(self, sample_points, waveform_data):
        sorted_waveform_data = sorted(waveform_data, key=lambda x: x[0])
        closest_point = None

        for sample_point in sample_points:
            if not self.samplenow(sample_point):
                continue
            for data_point in sorted_waveform_data:
                if data_point[0] <= sample_point:
                    closest_point = data_point
                else:
                    break
            yield closest_point


    def wave_is_a_clock(self, wave):
        for clock_record in self.config['clocks']:
            name = clock_record['name']
            if name == wave:
                period_wd = clock_record['period_wd']
                char = clock_record['char']
                return (True, period_wd, char)
        return (False, 0, ' ')


    def create_waveform_record(self, wave, waveform_data, vcd_dict_types, sample_points):
        # sourcery skip: extract-method
        """Creates a waveform record for a single signal."""
        signal_suffix = wave.split('.')[-1]
        phase = self.determine_phase(signal_suffix)
        signal_rec = {'name': wave, 'wave': '', 'data': [], 'phase': phase}
        (clock_signal, period_wd, char) = self.wave_is_a_clock(wave)

        if clock_signal:
            offset_in_common = self.config['offset_in_common']
            samplerate_in_common = self.config['samplerate_in_common']
            maxtime_in_common = self.config["maxtime_in_common"]
            repeat_count = int(((maxtime_in_common-offset_in_common)/samplerate_in_common)/period_wd)
            signal_rec['wave'] = char*repeat_count
            signal_rec['period'] = period_wd
        else:
            lastval = ''
            isbus = self.busregex2.match(wave) is not None or vcd_dict_types[wave] == 'bus'
            lastval = ''
            for j in self.find_closest_data_point(sample_points, waveform_data):
                if not self.samplenow(j[0]):
                    continue
                digit, value = self.process_signal_value(signal_rec, j, isbus, lastval, wave)
                signal_rec['wave'] += digit
                lastval = j[1]
        return signal_rec


    def determine_phase(self, signal):
        """Determines the phase based on the signal suffix."""
        if signal.endswith('clk'):
            return 0
        elif signal.startswith(('i_', 'r_', 'o_')):
            return 0.8
        elif signal.startswith(('w_', 'iw_', 'ow_')):
            return -0.3
        return 0 # 0.5


    def process_signal_value(self, signal_rec, j, isbus, lastval, wave_type):
        """Processes a value of the waveform."""
        digit = '.'
        value = None
        with contextlib.suppress(Exception):
            value = int(j[1])
            value = format(int(j[1], 2), 'X')
        if value is None:
            with contextlib.suppress(Exception):
                value = float(j[1])
                value = "{:.3e}".format(float(j[1]))
        if value is None:
            value = j[1]
        if isbus or wave_type == 'string':
            if lastval != j[1]:
                digit = '='
                if 'x' not in j[1]:
                    signal_rec['data'].append(value)
                else:
                    digit = 'x'
        else:
            j = (j[0],j[1])
            if lastval != j[1]:
                digit = j[1]
        lastval = j[1]

        return digit, value


    def finalize_wave_drom_structure(self, result_structure, signal_rec_dict):
        """Finalizes the WaveDrom structure by determining max cycles and applying configuration.
    
        Args:
            result_structure (list): The structure of groups and signals.
            signal_rec_dict (dict): Dictionary of signal records.
    
        Returns:
            dict: The finalized WaveDrom structure.
        """
        max_cycles = max(len(signal_rec['wave']) for signal_rec in signal_rec_dict.values())
        drom = self.build_wave_drom_structure(result_structure, signal_rec_dict, max_cycles)

        if 'hscale' in self.config:
            drom['config']['hscale'] = self.config['hscale']

        return drom

    def dump_wavedrom(self, vcd_dict, vcd_dict_types, sample_points, result_structure):
        """
        Dumps the WaveDrom JSON structure based on the VCD data and configuration settings.
    
        Args:
            vcd_dict (dict): The dictionary containing the VCD waveforms.
            vcd_dict_types (dict): The dictionary containing the VCD waveform types.
            sample_points List[(int)]: The times in the vcd timescale format to sample the data.
            result_structure (list): The structure of groups and signals.
    
        Returns:
            dict: The WaveDrom JSON structure representing the waveforms.
    
        """

        slots = len(sample_points)
        buses = self.group_buses(vcd_dict, slots)
        """
        Replace old signals that were grouped
        """
        self.remove_grouped_signals(buses, vcd_dict)
        """
        Create waveforms for the rest of the signals
        """
        signal_rec_dict = self.create_signal_records(vcd_dict, vcd_dict_types, sample_points)
        """
        Insert buses waveforms
        """
        for bus in buses:
            if not self.includewave(bus):
                continue
            signal_rec_dict[bus] = buses[bus]
        """
        Order per config and add extra user parameters
        """
        return self.finalize_wave_drom_structure(result_structure, signal_rec_dict)


    def execute(self, group_structure):
        """
        Executes the VCD to WaveDrom conversion process.
    
        Args:
            group_structure (list): The structure of groups and signals.
    
        Returns:
            dict: The WaveDrom JSON structure representing the waveforms.
    
        """

        vcd = VCDVCD(vcd_string=self.config['input_text'])
        timescale = f"{int(vcd.timescale['magnitude'])}{vcd.timescale['unit']}"
        self.config['timescale'] = timescale
        ts_unit = f"{vcd.timescale['unit']}"
        self.config['ts_unit'] = ts_unit

        # get the sample rate and maxtime in the vcd timescale format
        ureg = pint.UnitRegistry()
        self.config['offset_in_common'] = int(ureg(self.config['offset']).to(ureg(ts_unit)).magnitude)
        samplerate = self.config.get('samplerate', self.config['timescale'])
        self.config['samplerate_in_common'] = int(ureg(samplerate).to(ureg(ts_unit)).magnitude)
        self.config['maxtime_in_common'] = int(ureg(self.config['maxtime']).to(ureg(ts_unit)).magnitude)
        for clock_record in self.config['clocks']:
            period_in_common = int(ureg(clock_record['period']).to(ureg(ts_unit)).magnitude)
            clock_record['period_in_common'] = period_in_common        
            clock_record['period_wd'] = period_in_common/self.config['samplerate_in_common']

        vcd_dict = {}
        vcd_dict_types = {}
        vcd = vcd.data
        max_time = self.find_max_time_in_vcd(vcd)
        
        if max_time < self.config['maxtime_in_common']:
            print(f'Error maxtime is greater than that found in the vcd file; setting to max value {max_time}')
            self.config["maxtime_in_common"] = max_time
        for i in vcd:
            if i != '$end':
                for j in range(len(vcd[i].references)):
                    if int(vcd[i].size) > 1:
                        vcd_dict_types[vcd[i].references[j]] = 'bus'
                    else:
                        vcd_dict_types[vcd[i].references[j]] = 'signal'
                    vcd_dict[vcd[i].references[j]] = [list(tv) for tv in vcd[i].tv]

        # Example usage
        target_interval = self.config['samplerate']

        # Calculate the sample points
        sample_points = calculate_sampling_points(timescale, target_interval, f'{max_time}{ts_unit}')
        # pp.pprint(f'{sample_points=}')
        vcd_dict_homogenized = self.homogenize_waves(vcd_dict, sample_points)
        # pp.pprint(f'{vcd_dict_homogenized=}')
        return self.dump_wavedrom(vcd_dict_homogenized, vcd_dict_types, sample_points, group_structure)

def main(argv):
    """
    The main entry point of the VCD to WaveDrom conversion process.

    Args:
        argv (list): The command line arguments.
            -i, --input: Input VCD file
            -o, --output: Output Wavedrom file
            -c, --config: Config file
            -r, --samplerate: Sample rate of wavedrom
            -t, --maxtime: Length of time for wavedrom
            -f, --offset: Time offset from start of VCD
            -z, --hscale: Horizontal scale
            --top: Only output the top level signals
            -m, --makeconfig: Generate config file from VCD file
            -g, --gtkw: Path to gtkw file for signal grouping
            -n, --name: name of waveform

    Returns:
        None

    """

    parser = argparse.ArgumentParser(description='Transform VCD to wavedrom')
    parser.add_argument('-i', '--input', dest='input', help="Input VCD file", required=True)
    parser.add_argument('-o', '--output', dest='output', help="Output Wavedrom file")
    parser.add_argument('-c', '--config', dest='configfile', help="Config file")
    parser.add_argument('-r', '--samplerate', dest='samplerate', type=int, help="Sample rate of wavedrom")
    parser.add_argument('-t', '--maxtime', dest='maxtime', help="Length of time for wavedrom in the form of Xxs, e.g., 1230ns")
    parser.add_argument('-f', '--offset', dest='offset', help="Time offset from start of VCD in the form of Xxs, e.g., 1000ns")
    parser.add_argument('-z', '--hscale', dest='hscale', type=int, help="Horizontal scale")
    parser.add_argument('--top', dest='top', action="store_true", default=False, help="Only output the top level signals")
    parser.add_argument('-m', '--makeconfig', dest='makeconfig', help="Generate config file from VCD file", metavar='CONFIGFILE')
    parser.add_argument('-g', '--gtkw', dest='gtkw', help="Path to gtkw file for signal grouping", metavar='FILE')
    parser.add_argument('-n', '--name', dest='name', help="The title for the waveform")
    parser.add_argument('-hl', '--hierarchy-list', dest='hierarchy_list', nargs='+', help="Hierarchy list", metavar='HIERARCHY')
    # Add the -p and --profile options
    parser.add_argument('-p', '--profile', type=str, help='Path to the profile file')

    args = parser.parse_args(argv)
    args.input = os.path.abspath(os.path.join(os.getcwd(), args.input))

    # Create a profiler object
    profiler = cProfile.Profile()

    config = {}

    if args.configfile:
        with open(args.configfile) as json_file:
            config |= json.load(json_file)

    config['input'] = args.input
    try:
        with open(args.input, 'r') as f:
            config['input_text'] = f.read()
    except FileNotFoundError:
        print(f'ERROR: File {args.input} not found!')
        exit(1)

    config['output'] = args.output
    config['top'] = args.top
    if args.samplerate is not None:
        config['samplerate'] = args.samplerate
    if args.maxtime is not None:
        config['maxtime'] = args.maxtime
    if args.offset is not None:
        config['offset'] = args.offset
    config['hscale'] = args.hscale if args.hscale is not None else 1
    if args.name is not None:
        config['name'] = args.name
    if args.hierarchy_list:
        config['hierarchy_list'] = args.hierarchy_list
    elif 'hierarchy_list' not in config:
        config['hierarchy_list'] = []

    if args.makeconfig:
        config['offset'] = args.offset if args.offset is not None else "5ns"
        vcd = VCD2Wavedrom2(config)
        vcd.generate_config(args.makeconfig)
        exit(1)

    # Run the main function with profiling ================================>
    profiler.enable()

    vcd = VCD2Wavedrom2(config)
    result_structure = vcd.parse_gtkw_file(args.gtkw) if args.gtkw else [{'label':None, 'signals':config['filter'], 'level':0}]
    drom = vcd.execute(result_structure)
    # Print the result
    if config['output'] is not None:
        f = open(config['output'], 'w')
        f.write(json.dumps(drom, indent=4))
    else:
        print(json.dumps(drom, indent=4))

    # Stop the profiler ================================>
    profiler.disable()

    if args.profile:
        with open(args.profile, 'w') as profile_file:
            # Create a pstats.Stats object from the saved data
            stats = pstats.Stats(profiler, stream=profile_file)
            # Sort the stats by which takes the most time and save to the same file
            stats.strip_dirs().sort_stats('cumulative').print_stats()

if __name__ == '__main__':
    main(sys.argv[1:])
