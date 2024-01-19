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

cmn_unit = '1ns'
cmn_base = 'ns'

def convert_timescale_to_cmn_units(value, current_timescale, cmn_unit, cmn_base):
    """
    Converts a value from one timescale to another.

    Args:
        value: The value to be converted.
        current_timescale: The current timescale of the value (e.g., 'ns', 'us', 'ms').
        cmn_unit: The unit of the new timescale (e.g., 'ps', 'ns', 'us').
        cmn_base: The base value of the new timescale (e.g., 's', 'ms', 'us').

    Returns:
        str: The converted value in the new timescale with the specified base.

    """
    ureg = pint.UnitRegistry()

    # Extract the unit part from the current timescale
    current_unit = re.findall(r'[a-zA-Z]+', current_timescale)[0]

    # Convert the value to the current timescale unit
    value_in_current_units = value * ureg(current_unit)

    return f'{round(value_in_current_units.to(ureg(cmn_unit)).magnitude)}{cmn_base}'


def calculate_sampling_points(vcd_timescale, target_interval, endtime):
    """
    Calculates the sampling points for a given VCD timescale, target interval, and end time.

    Args:
        vcd_timescale: The timescale of the VCD file (e.g., '1ns', '10ps').
        target_interval: The desired interval between sampling points (e.g., '100ps', '1ns').
        endtime: The end time of the waveform (e.g., '1us', '10ms').

    Returns:
        list: A list of sampling points, represented as integers.

    """
    ureg = pint.UnitRegistry()

    # Convert timescale, interval, and endtime to seconds
    timescale_sec = ureg(vcd_timescale).to(ureg.second).magnitude
    interval_sec = ureg(target_interval).to(ureg.second).magnitude
    endtime_sec = ureg(endtime).to(ureg.second).magnitude

    # Calculate the number of sample points
    num_points = int(endtime_sec / interval_sec)

    return [int(i * interval_sec / timescale_sec) for i in range(num_points + 1)]


class VCD2Wavedrom2:
    """
    A class for converting VCD (Value Change Dump) files to WaveDrom JSON format.

    Args:
        config (dict): The configuration settings for the conversion.

    """
    busregex = re.compile(r'(.+?)(?:\[\d+(:\d+)?\]|\(\d+\))$')
    busregex2 = re.compile(r'(.+)\[(\d):(\d)\]')
    config = {}
    bit_open = None
    bit_close = None


    def __init__(self, config):
        """
        Initializes the VCD2Wavedrom2 object with the provided configuration settings.

        Args:
            config (dict): The configuration settings for the conversion.

        Returns:
            None

        """
        self.config = config


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
        """
        Groups and sorts the signals based on the provided hierarchy list.

        Args:
            signals (list): The list of signals to be grouped and sorted.
            hierarchy_list (list): The list of hierarchy names to group the signals.

        Returns:
            list: The sorted and grouped list of signals.

        """
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


    def samplenow(self, tick, sample_window):
        """
        Checks if a sample should be taken at the given tick based on the configuration settings.

        Args:
            tick (int): The tick value from the sample_points list.
            sample_window (str): The sample window to check.

        Returns:
            bool: True if a sample should be taken at the tick, False otherwise.

        """
        # Convert starttime, and samplerate to common units, these must be the same units as tick
        samplerate_in_common = self.config['samplerate_in_common']
        starttime_in_common = self.config['starttime_in_common'][sample_window]
        endtime_in_common = self.config["endtime_in_common"][sample_window]
        # Perform the check
        return (tick - starttime_in_common) >= 0 and \
                (tick- starttime_in_common) % samplerate_in_common == 0 and \
                (tick < endtime_in_common)


    def loop_and_find_sigs_clks(self, vcd, signals, clocks, clock_periods, timescale, base_unit, cmn_unit, cmn_base):
        """
        Loops through the VCD data and extracts signals, clocks, and the maximum time.

        Args:
            vcd (dict): The VCD data.
            signals (set): The set to store the extracted signals.
            clocks (set): The set to store the extracted clocks.
            clock_periods (dict): The dictionary to store the clock periods.
            timescale (str): The timescale of the VCD file.
            base_unit (str): The base unit of the timescale.
            cmn_unit (str): The common unit to convert the clock period to.
            cmn_base (str): The base unit of the common unit.

        Returns:
            tuple: A tuple containing the maximum time value found in the VCD data and the fastest clock period.

        """
        max_time = 0
        fastest_clock_period = float('inf')
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
                            fastest_clock_period = min(fastest_clock_period, clock_period)
                            cmn_clock_period = convert_timescale_to_cmn_units(2*fastest_clock_period, timescale, cmn_unit, cmn_base)
                            if sig not in clock_periods:
                                clock_periods[sig] = cmn_clock_period

                # Update max time
                last_tv_pair = vcd[signal].tv[-1]
                max_time = max(max_time, last_tv_pair[0])
        return (max_time, fastest_clock_period)


    def generate_config(self, output_config_file):
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
        clock_periods = {}

        (max_time, fastest_clock_period) = self.loop_and_find_sigs_clks(vcd, signals, clocks, clock_periods, timescale, base_unit, cmn_unit, cmn_base)

        # Adjust sample rate based on slowest clock (if clocks were found)
        sample_rate = fastest_clock_period * self.config['both'] if clocks else 1
        print(f'{fastest_clock_period=} {self.config["both"]=}')

        # Get the final list of sorted and grouped signals
        signals_final = self.group_and_sort_signals(signals, self.config['hierarchy_list'])
        clocks_final = self.group_and_sort_signals(list(clocks), self.config['hierarchy_list'])

        # Convert samplerate and endtime to the new unit
        samplerate_conv = convert_timescale_to_cmn_units(sample_rate, timescale, cmn_unit, cmn_base)
        endtime_conv = convert_timescale_to_cmn_units(max_time, timescale, cmn_unit, cmn_base)
        if 'endtime' in self.config:
            endtime_conv = self.config['endtime']
        name = self.config['name'] if 'name' in self.config else "The waveform title"
        clocks = [{'name': name, 'char': 'p', 'period': clock_periods[name]} for name in clocks_final]

        # Generate configuration dictionary
        config = {
            "signal": {},
            "filter": list(signals_final),
            "name": f'{name}',
            "tock": 1,
            "replace": {},
            "samplerate": f'{samplerate_conv}',
            "clocks": clocks,
            "starttime": f"[{self.config['starttime']}]",
            "endtime": f'[{endtime_conv}]',
            "phase_clk": 0,
            "phase_reg": 0,
            "phase_wir": 0
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

        # Initialize with a dummy root group to handle ungrouped signals and groups
        group_structure = {'label': None, 'signals': [], 'level': 0, 'subgroups': []}
        group_stack = [group_structure]

        with open(gtkw_file, 'r') as file:
            for line in file:
                line = line.strip()
                if line.startswith('@') or line.startswith('*') or line.startswith('['):
                    continue  # Skip markers and settings

                if line.startswith('-'):
                    # Determine the level of hierarchy
                    level = line.count('-')
                    label = line[level:].strip()
                    new_group = {'label': label, 'signals': [], 'level': level, 'subgroups': []}

                    # Pop groups from the stack until we're at the correct level
                    while group_stack and group_stack[-1]['level'] >= level:
                        group_stack.pop()

                    # Append the new group to its parent
                    group_stack[-1]['subgroups'].append(new_group)

                    # Push the new group onto the stack
                    group_stack.append(new_group)

                elif line:
                    # Add signals to the group at the top of the stack
                    group_stack[-1]['signals'].append(line)

        return [group_structure]  # Return the entire structure including the dummy root group


    def build_wave_drom_structure(self, group_structure, signal_rec_dict):
        """
        Builds the WaveDrom structure based on the group structure and signal records.

        Args:
            group_structure (list): The structure of groups and signals.
            signal_rec_dict (dict): The dictionary of signal records.

        Returns:
            dict: The WaveDrom structure representing the waveforms.

        """
        wave_drom_structure = {
            'head': {'text': self.config['name'], 'tock': self.config['tock']},
            'signal': [],
            'config': {'hscale': self.config['hscale']}
        }

        def process_group(group):
            """
            Processes a group in the group structure and returns the corresponding content.
            This is used for adding hierarchical labels to wavedrom drawings.

            Args:
                group (dict): The group to be processed.

            Returns:
                list: The content of the group, including signals and subgroups.

            """
            group_content = []
            
            for signal in group['signals']:
                signal_data = signal_rec_dict.get(signal, {'name': signal, 'wave': 'x'})
                group_content.append(signal_data)

            for subgroup in group.get('subgroups', []):
                subgroup_content = process_group(subgroup)
                if subgroup_content:
                    if subgroup['label']:
                        # If subgroup has a label, prepend it to the list
                        subgroup_content = [subgroup['label'], *subgroup_content]
                    group_content.append(subgroup_content)

            return group_content

        for group in group_structure:
            group_content = process_group(group)
            if group['label']:
                # If the group has a label, prepend it to the list
                group_content = [group['label'], *group_content]
            wave_drom_structure['signal'].extend(group_content)

        return wave_drom_structure


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
        """
        Finds the closest data point for each sample point in the waveform data.

        Args:
            sample_points (list): The times in the VCD timescale format to sample the data.
            waveform_data (list): The waveform data.

        Yields:
            tuple: The closest data point for each sample point.

        """
        sorted_waveform_data = sorted(waveform_data, key=lambda x: x[0])
        closest_point = None

        for sample_point in sample_points:
            # Determine the sample window for the current sample point
            sample_window = next((i for i, (start, end) in enumerate(zip(self.config['starttime_in_common'], self.config['endtime_in_common'])) 
                                if start <= sample_point < end), None)

            # If sample_window is None, it means sample_point doesn't fall into any window
            if sample_window is None or not self.samplenow(sample_point, sample_window):
                continue

            for data_point in sorted_waveform_data:
                if data_point[0] <= sample_point:
                    closest_point = data_point
                else:
                    break
            yield closest_point


    def wave_is_a_clock(self, wave):
        """
        Checks if a waveform is a clock signal based on the configuration settings.

        Args:
            wave (str): The name of the waveform.

        Returns:
            tuple: A tuple containing a boolean indicating if the waveform is a clock, the period in waveform digits, and the character representation of the waveform.

        """
        for clock_record in self.config['clocks']:
            name = clock_record['name']
            if name == wave:
                period_wd = clock_record['period_wd']
                char = clock_record['char']
                return (True, period_wd, char)
        return (False, 0, ' ')


    def process_clk_signal(self, wave, phase, period_wd, char):
        """
        Processes a clock signal and creates a waveform record.

        Args:
            wave (str): The name of the waveform.
            phase (int): The phase value of the waveform.
            period_wd (str): The period of the waveform in waveform digits.
            char (str): The character representation of the waveform.

        Returns:
            dict: The waveform record for the clock signal.

        """
        signal_rec = {
            'name': wave,
            'wave': '',
            'data': [],
            'phase': phase,
            'period': period_wd,
        }
        samplerate_in_common = self.config['samplerate_in_common']
        wave_fragments = []

        for sample_window in range(len(self.config['starttime'])):
            starttime_in_common = self.config['starttime_in_common'][sample_window]
            endtime_in_common = self.config["endtime_in_common"][sample_window]
            repeat_count = int((endtime_in_common - starttime_in_common) / samplerate_in_common / period_wd)

            # Append the wave fragment to the list
            wave_fragments.append(char * repeat_count + "|")

        # Join the list into a string and remove the last character
        signal_rec['wave'] = ''.join(wave_fragments)[:-1]
        return signal_rec


    def process_signal(self, wave, phase, waveform_data, vcd_dict_types, sample_points):
        """
        Processes a signal and creates a waveform record.

        Args:
            wave (str): The name of the waveform.
            phase (int): The phase value of the waveform.
            waveform_data (list): The waveform data.
            vcd_dict_types (dict): The dictionary containing the VCD waveform types.
            sample_points (list): The times in the VCD timescale format to sample the data.

        Returns:
            dict: The waveform record for the signal.

        """
        signal_rec = {'name': wave, 'wave': '', 'data': [], 'phase': phase}
        lastval = ''
        isbus = self.busregex2.match(wave) is not None or vcd_dict_types[wave] == 'bus'
        prev_sample_window = None

        for sample_point in sample_points:
            sample_window = next(
                (
                    i
                    for i, (start, end) in enumerate(
                        zip(
                            self.config['starttime_in_common'],
                            self.config['endtime_in_common'],
                        )
                    )
                    if start <= sample_point < end
                ),
                None,
            )
            if sample_window is None:
                continue

            # Append '|' if transitioning to a new sample window
            if sample_window != prev_sample_window and prev_sample_window is not None:
                signal_rec['wave'] += '|'
                # print(f'Moving to a new window: {sample_window}')

            # Update the previous sample window
            prev_sample_window = sample_window

            if closest_data_point := next(
                self.find_closest_data_point([sample_point], waveform_data),
                None,
            ):
                digit, value = self.process_signal_value(signal_rec, closest_data_point, isbus, lastval, wave)
                signal_rec['wave'] += digit
                lastval = closest_data_point[1]
        return signal_rec


    def create_waveform_record(self, wave, waveform_data, vcd_dict_types, sample_points):
        """
        Creates a waveform record for a single signal.

        Args:
            wave (str): The name of the waveform.
            waveform_data (list): The waveform data.
            vcd_dict_types (dict): The dictionary containing the VCD waveform types.
            sample_points (list): The times in the VCD timescale format to sample the data.

        Returns:
            dict: The waveform record for the signal.

        """
        signal_suffix = wave.split('.')[-1]
        phase = self.determine_phase(signal_suffix)
        
        (clock_signal, period_wd, char) = self.wave_is_a_clock(wave)

        if clock_signal:
            signal_rec = self.process_clk_signal(wave, phase, period_wd, char)
        else:
            signal_rec = self.process_signal(wave, phase, waveform_data, vcd_dict_types, sample_points)

        return signal_rec


    def determine_phase(self, signal):
        """Determines the phase based on the signal suffix."""
        if signal.endswith('clk'):
            return self.config["phase_clk"]
        elif signal.startswith(('i_', 'r_', 'o_')):
            return self.config["phase_reg"]
        elif signal.startswith(('w_', 'iw_', 'ow_')):
            return self.config["phase_wir"]
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


    def finalize_wave_drom_structure(self, group_structure, signal_rec_dict):
        """Finalizes the WaveDrom structure by determining max cycles and applying configuration.
    
        Args:
            group_structure (list): The structure of groups and signals.
            signal_rec_dict (dict): Dictionary of signal records.
    
        Returns:
            dict: The finalized WaveDrom structure.
        """
        drom = self.build_wave_drom_structure(group_structure, signal_rec_dict)

        if 'hscale' in self.config:
            drom['config']['hscale'] = self.config['hscale']

        return drom

    def dump_wavedrom(self, vcd_dict, vcd_dict_types, sample_points, group_structure):
        """
        Dumps the WaveDrom JSON structure based on the VCD data and configuration settings.
    
        Args:
            vcd_dict (dict): The dictionary containing the VCD waveforms.
            vcd_dict_types (dict): The dictionary containing the VCD waveform types.
            sample_points List[(int)]: The times in the vcd timescale format to sample the data.
            group_structure (list): The structure of groups and signals.
    
        Returns:
            dict: The WaveDrom JSON structure representing the waveforms.
    
        """

        """
        Create waveforms for the signals
        """
        signal_rec_dict = self.create_signal_records(vcd_dict, vcd_dict_types, sample_points)
        """
        Order per config and add extra user parameters
        """
        return self.finalize_wave_drom_structure(group_structure, signal_rec_dict)


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

        # get the sample rate and endtime in the vcd timescale format
        ureg = pint.UnitRegistry()
        samplerate = self.config.get('samplerate', self.config['timescale'])
        self.config['samplerate_in_common'] = int(ureg(samplerate).to(ureg(ts_unit)).magnitude)

        if len(self.config['starttime']) != len(self.config['endtime']):
            print('Error: the number of start times does not equal the number of end times... exiting.')
            exit(1)
        # Loop over and normalize the start and end time periods
        self.config['starttime_in_common'] = []
        self.config['endtime_in_common'] = []
        for starttime, endtime in zip(self.config['starttime'], self.config['endtime']):
            self.config['starttime_in_common'].append(int(ureg(starttime).to(ureg(ts_unit)).magnitude))
            self.config['endtime_in_common'].append(int(ureg(endtime).to(ureg(ts_unit)).magnitude))

        for clock_record in self.config['clocks']:
            period_in_common = int(ureg(clock_record['period']).to(ureg(ts_unit)).magnitude)
            clock_record['period_in_common'] = period_in_common        
            clock_record['period_wd'] = period_in_common/self.config['samplerate_in_common']

        vcd_dict = {}
        vcd_dict_types = {}
        vcd = vcd.data
        max_time = self.find_max_time_in_vcd(vcd)
        
        updated_endtime_list = [min(value, max_time) for value in self.config['endtime_in_common']]
        self.config['endtime_in_common'] = updated_endtime_list
        
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
            -s, --starttime: Time starttime from start of VCD
            -e, --endtime: Length of time for wavedrom
            -z, --hscale: Horizontal scale
            -t, --top: Only output the top level signals
            -b, --both: sample on both edges of the clock
            -m, --makeconfig: Generate config file from VCD file
            -g, --gtkw: Path to gtkw file for signal grouping
            -n, --name: name of waveform
            -hl, --hierarchy-list: used for creating the original config file. 
                    It will take one or more options to filter the signals on

    Returns:
        None

    """

    parser = argparse.ArgumentParser(description='Transform VCD to wavedrom')
    parser.add_argument('-i', '--input', dest='input', help="Input VCD file", required=True)
    parser.add_argument('-o', '--output', dest='output', help="Output Wavedrom file")
    parser.add_argument('-c', '--config', dest='configfile', help="Config file")
    parser.add_argument('-r', '--samplerate', dest='samplerate', type=int, help="Sample rate of wavedrom")
    parser.add_argument('-s', '--starttime', dest='starttime', nargs='+', help="List of start times from the VCD in the form of Xxs, e.g., 1000ns")
    parser.add_argument('-e', '--endtime', dest='endtime', nargs='+', help="List of end times from the VCD in the form of Xxs, e.g., 1230ns")
    parser.add_argument('-z', '--hscale', dest='hscale', type=int, help="Horizontal scale")
    parser.add_argument('-t', '--top', dest='top', action="store_true", default=False, help="Only output the top level signals")
    parser.add_argument('-b', '--both', dest='both', action="store_true", default=False, help="Sample the data on both edges fo the clocks")
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
    if args.endtime is not None:
        config['endtime'] = args.endtime
    if args.starttime is not None:
        config['starttime'] = args.starttime
    config['hscale'] = args.hscale if args.hscale is not None else 1
    if args.name is not None:
        config['name'] = args.name
    if args.hierarchy_list:
        config['hierarchy_list'] = args.hierarchy_list
    elif 'hierarchy_list' not in config:
        config['hierarchy_list'] = []
    config['both'] = 1 if args.both is True else 2
    if args.makeconfig:
        config['starttime'] = args.starttime if args.starttime is not None else "5ns"
        vcd = VCD2Wavedrom2(config)
        vcd.generate_config(args.makeconfig)
        exit(1)

    # Run the main function with profiling ================================>
    profiler.enable()

    vcd = VCD2Wavedrom2(config)
    group_structure = vcd.parse_gtkw_file(args.gtkw) if args.gtkw else [{'label':None, 'signals':config['filter'], 'level':0}]
    drom = vcd.execute(group_structure)
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
