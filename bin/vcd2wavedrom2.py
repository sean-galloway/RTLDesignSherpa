#!/usr/bin/python3

import contextlib
import sys
import os
import argparse
import json
import re
import pprint
pp = pprint.PrettyPrinter(indent=4)

from vcdvcd.vcdvcd import VCDVCD

from math import floor, ceil

class VCD2Wavedrom2:
    """
    Converts VCD (Value Change Dump) files to WaveDrom JSON format.

    Args:
        config (dict): The configuration settings for the conversion.

    Methods:
        __init__(self, config):
            Initializes the VCD2Wavedrom2 instance with the given configuration.

        replacevalue(self, wave, strval):
            Replaces the value of a waveform based on the configuration settings.

        group_buses(self, vcd_dict, slots):
            Groups the waveforms into buses based on the bus naming conventions.

        auto_config_waves(self, vcd_dict):
            Automatically configures the waveform settings based on the VCD file.

        homogenize_waves(self, vcd_dict, timescale):
            Homogenizes the waveforms by adding missing samples and adjusting the time scale.

        includewave(self, wave):
            Checks if a waveform should be included based on the configuration settings.

        clockvalue(self, wave, digit):
            Returns the clock value for a waveform digit based on the configuration settings.

        samplenow(self, tick):
            Checks if a sample should be taken at the given tick based on the configuration settings.

        appendconfig(self, wave):
            Appends additional configuration settings to a waveform.

        find_max_time_in_vcd(vcd):
            Finds the maximum time value in the VCD file.

        generate_config(self, output_config_file):
            Generates a configuration file based on the VCD file.

        parse_gtkw_file(self, gtkw_file):
            Parses a GTKWave save file and returns the structure of groups and signals.

        build_wave_drom_structure(self, result_structure, signal_rec_dict):
            Builds the WaveDrom structure based on the group structure and signal records.

        dump_wavedrom(self, vcd_dict, vcd_dict_types, timescale, result_structure):
            Dumps the WaveDrom JSON structure based on the VCD data and configuration settings.

        execute(self, auto, group_structure):
            Executes the VCD to WaveDrom conversion process.

    """

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
            for slot in range(slots):
                if not self.samplenow(slot):
                    continue
                byte, strval = 0, ''
                for bit in range(buswidth[wave] + 1):
                    if bit % 8 == 0 and bit != 0:
                        strval = format(byte, 'X') + strval
                        byte = 0
                    val = vcd_dict[wave + self.bit_open + str(bit) + self.bit_close][slot][1]
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


    def auto_config_waves(self, vcd_dict):    # sourcery skip: low-code-quality
        """
        Automatically configures the waveform settings based on the VCD file.
    
        Args:
            vcd_dict (dict): The dictionary containing the VCD waveforms.
    
        Returns:
            int: A value indicating the success of the configuration process.
    
        Raises:
            ValueError: If a waveform is empty.
    
        Warning:
            This method will overwrite all information from the configuration file if any.
            It works best with full synchronous signals.
    
        """

        startTime = -1
        syncTime = -1
        endTime = -1
        minDiffTime = -1

        """
        Warning: will overwrite all information from config file if any
        Works best with full synchronous signals
        """

        self.config['filter'] = ['__all__']
        self.config['clocks'] = []
        self.config['signal'] = []

        for wave in vcd_dict:
            wave_points = vcd_dict[wave]
            if len(wave_points) == 0:
                raise ValueError(f"Signal {wave} is empty!")
            wave_first_point = wave_points[0]
            wave_first_time = wave_first_point[0]
            if (startTime < 0) or (wave_first_time < startTime):
                startTime = wave_first_time

            if (len(wave_points) > 1) and ((syncTime < 0) or (wave_points[1][0] < syncTime)):
                syncTime = wave_points[1][0]

            for wave_point in wave_points:
                if (endTime < 0) or (wave_point[0] > endTime):
                    endTime = wave_point[0]

            for tidx in range(2, len(wave_points)):
                tmpDiff = wave_points[tidx][0] - wave_points[tidx - 1][0]
                if (
                    wave_points[tidx - 1][0] >= startTime
                    and (minDiffTime < 0 or tmpDiff < minDiffTime)
                    and tmpDiff > 0
                ):
                    minDiffTime = tmpDiff

        # Corner case
        if minDiffTime < 0:
            for tidx in range(1, len(wave_points)):
                tmpDiff = wave_points[tidx][0] - wave_points[tidx - 1][0]
                if wave_points[tidx - 1][0] >= startTime and ((minDiffTime < 0 or tmpDiff < minDiffTime) and tmpDiff > 0):
                    minDiffTime = tmpDiff

        # 1st loop to refine minDiffTime for async design or multiple async clocks
        tmpRatio = 1
        tmpReal = 0
        for wave in vcd_dict:
            wave_points = vcd_dict[wave]
            for wave_point in wave_points:
                tmpReal = (wave_point[0] - syncTime) / minDiffTime / tmpRatio
                if abs(tmpReal - round(tmpReal)) > 0.25 and tmpRatio < 4:
                    tmpRatio = tmpRatio * 2

        minDiffTime = minDiffTime / tmpRatio
        startTime = syncTime - \
                                ceil((syncTime - startTime) / minDiffTime) * minDiffTime

        # 2nd loop to apply rounding
        tmpReal = 0
        for wave in vcd_dict:
            wave_points = vcd_dict[wave]
            for wave_point in wave_points:
                tmpReal = (wave_point[0] - startTime) / minDiffTime
                wave_point[0] = round(tmpReal)
            wave_points[0][0] = 0

        if 'maxtime' in self.config and self.config['maxtime'] is not None:
            self.config['maxtime'] = min(
                ceil((endTime - startTime) / minDiffTime), self.config['maxtime'])
        else:
            self.config['maxtime'] = ceil((endTime - startTime) / minDiffTime)

        return 1


    def homogenize_waves(self, vcd_dict, timescale):
        """
        Homogenizes the waveforms by adding missing samples and adjusting the time scale.
    
        Args:
            vcd_dict (dict): The dictionary containing the VCD waveforms.
            timescale (int): The time scale for the waveforms.
    
        Returns:
            None
    
        """
    
        slots = int(self.config['maxtime']/timescale) + 1
        for isig, wave in enumerate(vcd_dict):
            lastval = 'x'
            for tidx, t in enumerate(range(0, self.config['maxtime'] + timescale, timescale)):
                newtime = vcd_dict[wave][tidx][0] if len(vcd_dict[wave]) > tidx else t + 1
                if newtime != t:
                    for ito_padd, padd in enumerate(range(t, newtime, timescale)):
                        vcd_dict[wave].insert(tidx+ito_padd, (padd, lastval))
                else:
                    lastval = vcd_dict[wave][tidx][1]
            vcd_dict[wave] = vcd_dict[wave][:slots]


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


    def clockvalue(self, wave, digit):
        """
        Returns the clock value for a waveform digit based on the configuration settings.
    
        Args:
            wave (str): The name of the waveform.
            digit (str): The waveform digit.
    
        Returns:
            str: The clock value if the waveform is a clock and the digit is '1'. Otherwise, returns the original digit.
    
        """
    
        return 'P' if wave in self.config['clocks'] and digit == '1' else digit


    def samplenow(self, tick):
        """
        Checks if a sample should be taken at the given tick based on the configuration settings.
    
        Args:
            tick (int): The tick value.
    
        Returns:
            bool: True if a sample should be taken at the tick, False otherwise.
    
        """

        offset = self.config['offset'] if 'offset' in self.config else 0
        samplerate = self.config['samplerate'] if 'samplerate' in self.config else 1
        return (tick - offset) >= 0 and (tick - offset) % samplerate <= 0


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
        vcd = vcd.data
        # Initialize variables
        signals = set()
        clocks = set()
        slowest_clock_rate = float('inf')
        max_time = 0
    
        # Extract signals, clocks, and max time from VCD
        for signal in vcd:
            if signal != '$end':
                signals.add(vcd[signal].references[0])
    
                # Identify clocks and determine slowest clock rate
                if 'clk' in vcd[signal].references[0]:
                    clocks.add(vcd[signal].references[0])
                    tv_pairs = vcd[signal].tv
                    if len(tv_pairs) > 1:
                        clock_period = tv_pairs[1][0] - tv_pairs[0][0]
                        slowest_clock_rate = min(slowest_clock_rate, clock_period)
    
                # Update max time
                last_tv_pair = vcd[signal].tv[-1]
                max_time = max(max_time, last_tv_pair[0])
    
        # Adjust sample rate based on slowest clock (if clocks were found)
        sample_rate = slowest_clock_rate if clocks else 1
    
        # Generate configuration dictionary
        config = {
            "signal": {},
            "filter": list(signals),
            "replace": {},
            "offset": 5,
            "samplerate": sample_rate,
            "clocks": list(clocks),
            "maxtime": max_time
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
        wave_drom_structure = {'signal': [{'name':'Cycles', 'wave':'='*max_cycles, 'data':cycles_string }], 'config':{'hscale': 1}}
    
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


    
    def create_signal_records(self, vcd_dict, vcd_dict_types):
        """Creates waveform records for the remaining signals in vcd_dict."""
        signal_rec_dict = {}
        for wave in vcd_dict:
            if not self.includewave(wave):
                continue
            signal_rec = self.create_waveform_record(wave, vcd_dict[wave], vcd_dict_types)
            signal_rec_dict[wave] = signal_rec
        return signal_rec_dict
    
    
    def create_waveform_record(self, wave, waveform_data, vcd_dict_types):
        """Creates a waveform record for a single signal."""
        signal_suffix = wave.split('.')[-1]
        phase = self.determine_phase(signal_suffix)
        signal_rec = {'name': wave, 'wave': '', 'data': [], 'phase': phase}
    
        lastval = ''
        isbus = self.busregex2.match(wave) is not None or vcd_dict_types[wave] == 'bus'
        lastval = ''
        for j in waveform_data:
            if not self.samplenow(j[0]):
                continue
            digit, value = self.process_signal_value(signal_rec, j, isbus, lastval, wave)
            signal_rec['wave'] += digit
            lastval = j[1]
        return signal_rec


    def determine_phase(self, signal_suffix):
        """Determines the phase based on the signal suffix."""
        if signal_suffix.startswith(('i_', 'r_', 'o_')):
            return 0.2
        elif signal_suffix.startswith(('w_', 'iw_', 'ow_')):
            return 0.8
        elif 'clk' in signal_suffix:
            return 0
        return 0.5


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
            j = (j[0], self.clockvalue(wave_type, j[1]))
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

    def dump_wavedrom(self, vcd_dict, vcd_dict_types, timescale, result_structure):
        """
        Dumps the WaveDrom JSON structure based on the VCD data and configuration settings.
    
        Args:
            vcd_dict (dict): The dictionary containing the VCD waveforms.
            vcd_dict_types (dict): The dictionary containing the VCD waveform types.
            timescale (int): The time scale for the waveforms.
            result_structure (list): The structure of groups and signals.
    
        Returns:
            dict: The WaveDrom JSON structure representing the waveforms.
    
        """

        slots = int(self.config['maxtime']/timescale)
        buses = self.group_buses(vcd_dict, slots)
        """
        Replace old signals that were grouped
        """
        self.remove_grouped_signals(buses, vcd_dict)

        """
        Create waveforms for the rest of the signals
        """
        signal_rec_dict = self.create_signal_records(vcd_dict, vcd_dict_types)

        """
        Insert buses waveforms
        """
        for bus in buses:
            if not self.includewave(bus):
                continue
            signal_rec_dict[bus] = buses[bus]
            # drom['signal'].append(buses[bus])

        """
        Order per config and add extra user parameters
        """
        # pp.pprint(f'Pre:{signal_rec_dict=}')
        return self.finalize_wave_drom_structure(result_structure, signal_rec_dict)


    def execute(self, auto, group_structure):
        """
        Executes the VCD to WaveDrom conversion process.
    
        Args:
            auto (bool): Flag indicating whether to automatically configure the waveform settings.
            group_structure (list): The structure of groups and signals.
    
        Returns:
            dict: The WaveDrom JSON structure representing the waveforms.
    
        """

        vcd = VCDVCD(vcd_string=self.config['input_text'])
        timescale = int(vcd.timescale['magnitude'])
        vcd_dict = {}
        vcd_dict_types = {}
        vcd = vcd.data
        max_time = self.find_max_time_in_vcd(vcd)
        if 'maxtime' in self.config and max_time < self.config["maxtime"]:
            print(f'Error maxtime is greater than that found in the vcd file; setting to max value {max_time}')
            self.config["maxtime"] = max_time
        for i in vcd:
            if i != '$end':
                if int(vcd[i].size) > 1:
                    vcd_dict_types[vcd[i].references[0]] = 'bus'
                else:
                    vcd_dict_types[vcd[i].references[0]] = 'signal'
                vcd_dict[vcd[i].references[0]] = [list(tv) for tv in vcd[i].tv]

        if auto:
            timescale = self.auto_config_waves(vcd_dict)

        self.homogenize_waves(vcd_dict, timescale)
        return self.dump_wavedrom(vcd_dict, vcd_dict_types, timescale, group_structure)


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
    parser.add_argument('-t', '--maxtime', dest='maxtime', type=int, help="Length of time for wavedrom")
    parser.add_argument('-f', '--offset', dest='offset', type=int, help="Time offset from start of VCD")
    parser.add_argument('-z', '--hscale', dest='hscale', type=int, help="Horizontal scale")
    parser.add_argument('--top', dest='top', action="store_true", default=False, help="Only output the top level signals")
    parser.add_argument('-m', '--makeconfig', dest='makeconfig', help="Generate config file from VCD file", metavar='CONFIGFILE')
    parser.add_argument('-g', '--gtkw', dest='gtkw', help="Path to gtkw file for signal grouping", metavar='FILE')
# TODO: need to add these in
    parser.add_argument('-n', '--name', dest='name', help="The title for the waveform")
    parser.add_argument('-l', '--line', action='store_true', help='Enable or disable line option')


    args = parser.parse_args(argv)
    args.input = os.path.abspath(os.path.join(os.getcwd(), args.input))

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
    if args.hscale is not None:
        config['hscale'] = args.hscale

    if args.makeconfig:
        vcd = VCD2Wavedrom2(config)
        vcd.generate_config(args.makeconfig)
        exit(1)

    vcd = VCD2Wavedrom2(config)
    result_structure = vcd.parse_gtkw_file(args.gtkw) if args.gtkw else [{'label':None, 'signals':config['filter'], 'level':0}]
    drom = vcd.execute(args.configfile is None, result_structure)
    # Print the result
    if config['output'] is not None:
        f = open(config['output'], 'w')
        f.write(json.dumps(drom, indent=4))
    else:
        print(json.dumps(drom, indent=4))

if __name__ == '__main__':
    main(sys.argv[1:])
