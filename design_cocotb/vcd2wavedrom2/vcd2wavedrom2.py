from v2wconfig import V2WConfig
import sys
import contextlib
import json
import re
import pprint
pp = pprint.PrettyPrinter(indent=4)
import pstats
import cProfile


class VCD2Wavedrom2:
    busregex = re.compile(r'(.+)\[(\d):(\d)\]')


    def __init__(self, argv):
        self.v2wconfig = V2WConfig(argv)
        self.config = self.v2wconfig.config
        self.enum_dict = self.v2wconfig.enum_dict
        self.converter = self.v2wconfig.converter
        self.vcd = self.v2wconfig.vcd


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
                (tick - starttime_in_common) % samplerate_in_common == 0 and \
                (tick < endtime_in_common)


    def parse_gtkw_file(self, gtkw_file):
        """
        Parses a GTKWave save file and returns the structure of groups and signals.

        Args:
            gtkw_file (str): The path to the GTKWave save file.

        Returns:
            list: A list representing the structure of groups and signals, where each group contains a label, signals, and level.
        """
        group_structure = {'label': None, 'signals': [], 'level': 0, 'subgroups': []}
        group_stack = [group_structure]

        with open(gtkw_file, 'r') as file:
            for line in file:
                line = line.strip()
                if line.startswith('@') or line.startswith('*') or line.startswith('['):
                    continue  # Skip markers and settings

                if line.startswith('-+'):
                    up_levels = line.count('+')
                    while up_levels > 0 and len(group_stack) > 1:
                        group_stack.pop()
                        up_levels -= 1
                    group = group_stack[-1]

                elif line.startswith('-'):
                    level = line.count('-')
                    label = line[level:].strip()
                    new_group = {'label': label, 'signals': [], 'level': level, 'subgroups': []}

                    while group_stack and group_stack[-1]['level'] >= level:
                        group_stack.pop()

                    group_stack[-1]['subgroups'].append(new_group)
                    group_stack.append(new_group)


                elif line:
                    group_stack[-1]['signals'].append(line)

        return [group_structure]



    def build_wave_drom_structure(self, group_structure, signal_rec_dict):
        """
        Builds the WaveDrom structure based on the group structure and signal records.

        Args:
            group_structure (list): The structure of groups and signals.
            signal_rec_dict (dict): The dictionary of signal records.

        Returns:
            dict: The WaveDrom structure representing the waveforms.

        """
        hscale = 1 if 'hscale' not in self.config else self.config['hscale']
        wave_drom_structure = {
            'head': {'text': self.config['name'], 'tock': self.config['tock']},
            'signal': [],
            'config': {'hscale': hscale}
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
        isbus = self.busregex.match(wave) is not None or vcd_dict_types[wave] == 'bus'
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

        return (
            self.process_clk_signal(wave, phase, period_wd, char)
            if clock_signal
            else self.process_signal(
                wave, phase, waveform_data, vcd_dict_types, sample_points
            )
        )


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
                value_replace = value
                sig = signal_rec['name']
                if sig in self.enum_dict:
                    # pp.pprint(f'{self.enum_dict[sig]=}')
                    value_str = str(value)
                    if value_str in self.enum_dict[sig]:
                        value_replace = self.enum_dict[sig][value_str]
                    else:
                        print(f'Error: tried to replace enum signal ({sig}) for value ({value_str}), but it is not in the list')
                if 'x' not in j[1]:
                    signal_rec['data'].append(value_replace)
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

        vcd = self.v2wconfig.vcd
        timescale = f"{int(vcd.timescale['magnitude'])}{vcd.timescale['unit']}"
        self.config['timescale'] = timescale
        ts_unit = f"{vcd.timescale['unit']}"
        self.config['ts_unit'] = ts_unit

        # get the sample rate and endtime in the vcd timescale format
        ureg = self.converter.ureg
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
        # print(f'{target_interval=}')

        # Calculate the sample points
        # pp.pprint(f"{self.config['starttime']}")
        # pp.pprint(f"{self.config['endtime']}")
        sample_points = self.converter.calculate_sampling_points(
            timescale, target_interval, self.config['starttime'], self.config['endtime'])
        # pp.pprint(f'{sample_points=}')
        vcd_dict_homogenized = self.homogenize_waves(vcd_dict, sample_points)
        # pp.pprint(f'{vcd_dict_homogenized=}')
        return self.dump_wavedrom(
            vcd_dict_homogenized, vcd_dict_types, sample_points, group_structure)

def main(argv):

    # Create a profiler object
    profiler = cProfile.Profile()

    # Run the main function with profiling ================================>
    profiler.enable()

    vcd = VCD2Wavedrom2(argv)
    # pp.pprint(f'{vcd.config=}')
    group_structure = vcd.parse_gtkw_file(vcd.config['gtkw']) if 'gtkw' in vcd.config else [{'label':None, 'signals':vcd.config['filter'], 'level':0}]
    # pp.pprint(f'{group_structure=}')
    drom = vcd.execute(group_structure)
    # Print the result
    if vcd.config['output'] is not None:
        f = open(vcd.config['output'], 'w')
        f.write(json.dumps(drom, indent=4))
    else:
        print(json.dumps(drom, indent=4))

    # Stop the profiler ================================>
    profiler.disable()

    if 'profile' in vcd.config:
        with open(vcd.config['profile'], 'w') as profile_file:
            # Create a pstats.Stats object from the saved data
            stats = pstats.Stats(profiler, stream=profile_file)
            # Sort the stats by which takes the most time and save to the same file
            stats.strip_dirs().sort_stats('cumulative').print_stats()

if __name__ == '__main__':
    main(sys.argv[1:])
