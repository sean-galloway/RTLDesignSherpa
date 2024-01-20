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


    def calculate_sampling_points(self, vcd_timescale, target_interval, endtime):
        """
        Calculates the sampling points for a given VCD timescale, target interval, and end time.

        Args:
            vcd_timescale: The timescale of the VCD file (e.g., '1ns', '10ps').
            target_interval: The desired interval between sampling points (e.g., '100ps', '1ns').
            endtime: The end time of the waveform (e.g., '1us', '10ms').

        Returns:
            list: A list of sampling points, represented as integers.

        """
        # Convert timescale, interval, and endtime to seconds
        timescale_sec = self._convert_to_magnitude(vcd_timescale, '1s')
        interval_sec = self._convert_to_magnitude(target_interval, '1s')
        endtime_sec = self._convert_to_magnitude(endtime, '1s')
        # Calculate the number of sample points
        num_points = int(endtime_sec / interval_sec)

        return [int(i * interval_sec / timescale_sec) for i in range(num_points + 1)]

    
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
        return ureg(time_base).to(ureg(units)).magnitude
