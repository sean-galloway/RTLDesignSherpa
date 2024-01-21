import pint
import re


class V2WConvert:

    # The common unit for human readable items
    cmn_unit = '1ns'
    cmn_base = 'ns'

    def __init__(self):
        self.ureg = pint.UnitRegistry()


    def convert_timescale_to_cmn_units(self, value, current_timescale, cmn_unit, cmn_base):
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
        ureg = self.ureg

        # Extract the unit part from the current timescale
        current_unit = re.findall(r'[a-zA-Z]+', current_timescale)[0]

        # Convert the value to the current timescale unit
        value_in_current_units = value * ureg(current_unit)

        return f'{round(value_in_current_units.to(ureg(cmn_unit)).magnitude)}{cmn_base}'


    def calculate_sampling_points(self, vcd_timescale, target_interval, starttime_windows, endtime_windows):
        """
        Calculates the sampling points for given VCD timescale and target interval, only within specified time windows.

        Args:
            vcd_timescale: The timescale of the VCD file (e.g., '1ns', '10ps').
            target_interval: The desired interval between sampling points (e.g., '100ps', '1ns').
            starttime_windows: List of start times for sampling windows.
            endtime_windows: List of end times for sampling windows.

        Returns:
            list: A list of unique and sorted sampling points, represented as integers.
        """
        interval_ts = self._convert_to_magnitude(target_interval, vcd_timescale)

        sampling_points = set()

        for start_time, end_time in zip(starttime_windows, endtime_windows):
            start_ts = self._convert_to_magnitude(start_time, vcd_timescale)
            # add one more on so that the range works
            end_ts = self._convert_to_magnitude(end_time, vcd_timescale) + interval_ts

            window_points = list(range(start_ts, end_ts, interval_ts))
            sampling_points.update(window_points)

        return sorted(sampling_points)

    
    def _convert_to_magnitude(self, time_base, units):
        """
        Converts a time base to magnitude in the specified units.

        Args:
            time_base: The time base to be converted.
            units: The units to convert the time base to.

        Returns:
            int: The magnitude of the time base in the specified units.

        """
        ureg = self.ureg
        return round(ureg(time_base).to(ureg(units)).magnitude)
