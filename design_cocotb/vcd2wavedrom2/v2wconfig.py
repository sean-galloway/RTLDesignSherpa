import os
import subprocess
import argparse
import json
from vcdvcd.vcdvcd import VCDVCD
from v2wconvert import V2WConvert


class V2WConfig:

    def __init__(self, argv):
        self.config = {}
        self.enum_dict = {}
        self.converter = V2WConvert()
        self.vcd = None
        self.argparse(argv)


    def group_and_sort_signals(self, signals):
        """
        Groups and sorts the signals based on the provided hierarchy list.

        Args:
            signals (list): The list of signals to be grouped and sorted.
            hierarchy_list (list): The list of hierarchy names to group the signals.

        Returns:
            list: The sorted and grouped list of signals.

        """
        hierarchy_list = self.config['hierarchy_list']
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


    def argparse(self, argv):
        '''
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
        '''

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
        parser.add_argument('-p', '--profile', type=str, help='Path to the profile file')

        args = parser.parse_args(argv)
        args.input = os.path.abspath(os.path.join(os.getcwd(), args.input))

        if args.configfile:
            with open(args.configfile) as json_file:
                self.config |= json.load(json_file)
            if 'enum_list' in self.config and len(self.config['enum_list']) > 0:
                self.enum_dict = {item['name']: item['enum'] for item in self.config['enum_list']}

        self.config['input'] = args.input
        try:
            with open(args.input, 'r') as f:
                self.config['input_text'] = f.read()
        except FileNotFoundError:
            print(f'ERROR: File {args.input} not found!')
            exit(1)

        self.config['output'] = args.output
        self.config['top'] = args.top
        if args.samplerate is not None:
            self.config['samplerate'] = args.samplerate
        if args.endtime is not None:
            self.config['endtime'] = args.endtime
        if args.starttime is not None:
            self.config['starttime'] = args.starttime
        if args.hscale is not None:
            self.config['hscale'] = args.hscale
        if args.gtkw:
            self.config['gtkw'] = args.gtkw
        if args.name is not None:
            self.config['name'] = args.name
        if args.hierarchy_list:
            self.config['hierarchy_list'] = args.hierarchy_list
        elif 'hierarchy_list' not in self.config:
            self.config['hierarchy_list'] = []
        self.config['both'] = 1 if args.both is True else 2
        # Load VCD file
        self.vcd = VCDVCD(vcd_string=self.config['input_text'])
        # Make the config if needed
        if args.makeconfig:
            self.config['makeconfig'] = args.makeconfig
            self.generate_config()
            exit(1)
        if args.profile:
            self.config['profile'] = args.profile


    def generate_config(self):
        """
        Generates a configuration file based on the VCD file.

        Args:
            output_config_file (str): The path to the output configuration file.

        Returns:
            None

        """

        timescale = f"{int(self.vcd.timescale['magnitude'])}{self.vcd.timescale['unit']}"
        base_unit = self.vcd.timescale['unit']
        vcd = self.vcd.data
        # Initialize variables
        signals = set()
        clocks = set()
        clock_periods = {}

        (max_time, fastest_clock_period) = self.loop_and_find_sigs_clks(
            vcd, signals, clocks, clock_periods, timescale, base_unit,
            self.converter.cmn_unit, self.converter.cmn_base)

        # Adjust sample rate based on slowest clock (if clocks were found)
        sample_rate = fastest_clock_period * self.config['both'] if clocks else 1
        # print(f'{fastest_clock_period=} {self.config["both"]=}')

        # Get the final list of sorted and grouped signals
        signals_final = self.group_and_sort_signals(signals)
        clocks_final = self.group_and_sort_signals(list(clocks))

        # Convert samplerate and endtime to the new unit
        samplerate_conv = self.converter.convert_timescale_to_cmn_units(
            sample_rate, timescale, self.converter.cmn_unit, self.converter.cmn_base)
        if samplerate_conv == '0ns':
            samplerate_conv = '10ns'
        endtime_conv = self.converter.convert_timescale_to_cmn_units(
            max_time, timescale, self.converter.cmn_unit, self.converter.cmn_base)
        if 'starttime' in self.config:
            starttime_list = self.config['starttime']
        else:
            starttime_list = ["5ns"]
        if 'endtime' in self.config:
            endtime_list = self.config['endtime']
        else:
            endtime_list = [endtime_conv]

        name = self.config['name'] if 'name' in self.config else "The waveform title"
        clocks = [{'name': name, 'char': 'p', 'period': clock_periods[name]} for name in clocks_final]
        hscale = 1 if 'hscale' not in self.config else self.config['hscale']

        # Generate configuration dictionary
        config = {
            "filter": list(signals_final),
            "name": f'{name}',
            "tock": 1,
            "samplerate": f'{samplerate_conv}',
            "hscale": hscale,
            "clocks": clocks,
            "starttime": starttime_list,
            "endtime": endtime_list,
            "phase_clk": 0,
            "phase_reg": 0,
            "phase_wir": 0,
            "enum_list": []
        }

        # Write configuration to file
        with open(self.config['makeconfig'], 'w') as outfile:
            json.dump(config, outfile, indent=4)


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
                            cmn_clock_period = self.converter.convert_timescale_to_cmn_units(
                                2*clock_period, timescale, cmn_unit, cmn_base)
                            if sig not in clock_periods:
                                clock_periods[sig] = cmn_clock_period

                # Update max time
                last_tv_pair = vcd[signal].tv[-1]
                max_time = max(max_time, last_tv_pair[0])
        return (max_time, fastest_clock_period)

