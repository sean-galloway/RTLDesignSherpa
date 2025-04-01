"""APB Cycle and Transaction Classes with enhanced formatting"""

import copy
import random
from cocotb_coverage.crv import Randomized
from ..flex_randomizer import FlexRandomizer

# Define the PWRITE mapping
pwrite = ['READ', 'WRITE']

class APBCycle:
    """Enhanced APB Cycle class with improved formatting and comparison"""

    def __init__(self, start_time=0, count=0, direction='unknown', pwrite=0,
                    paddr=0, pwdata=0, prdata=0, pstrb=0, pprot=0, pslverr=0):
        # Timing information
        self.start_time = start_time
        self.end_time = 0
        self.count = count

        # Direction and control
        self.direction = direction
        self.pwrite = pwrite

        # Address and data
        self.paddr = paddr
        self.pwdata = pwdata
        self.prdata = prdata

        # Additional control
        self.pstrb = pstrb
        self.pprot = pprot
        self.pslverr = pslverr

        # Fields to skip during comparison
        self.skip_compare_fields = ['start_time', 'end_time', 'count']

    def __eq__(self, other):
        """
        Compare APB cycles, skipping fields in skip_compare_fields

        Args:
            other: Another APBCycle to compare with

        Returns:
            True if all non-skipped fields match, False otherwise
        """
        if not isinstance(other, APBCycle):
            return NotImplemented

        # Compare the relevant data field based on direction
        if self.direction == 'WRITE':
            data_self = self.pwdata
            data_other = other.pwdata
        else:
            data_self = self.prdata
            data_other = other.prdata

        # Basic checks for key fields
        if (self.direction != other.direction or
            self.paddr != other.paddr or
            data_self != data_other or
            self.pprot != other.pprot or
            self.pslverr != other.pslverr):
            return False

        # For writes, also check strobes
        if self.direction == 'WRITE' and self.pstrb != other.pstrb:
            return False

        return True

    def _format_field(self, field_name, value, format_spec=None):
        """
        Format a field value with appropriate formatting

        Args:
            field_name: Name of the field to format
            value: Value to format
            format_spec: Optional format specification dictionary

        Returns:
            Formatted string representation of the value
        """
        # Default format specifications if none provided
        if format_spec is None:
            format_spec = {
                'addr': {'format': 'hex', 'width': 8},
                'data': {'format': 'hex', 'width': 8},
                'strb': {'format': 'bin', 'width': 4},
                'prot': {'format': 'hex', 'width': 2},
                'write': {'format': 'dec', 'width': 1},
                'slverr': {'format': 'dec', 'width': 1},
                'default': {'format': 'hex', 'width': 8}
            }

        # Determine field type and get format specification
        field_type = None
        if 'addr' in field_name:
            field_type = 'addr'
        elif 'data' in field_name:
            field_type = 'data'
        elif 'strb' in field_name:
            field_type = 'strb'
        elif 'prot' in field_name:
            field_type = 'prot'
        elif 'write' in field_name:
            field_type = 'write'
        elif 'slverr' in field_name:
            field_type = 'slverr'
        else:
            field_type = 'default'

        # Get format specification for this field type
        spec = format_spec.get(field_type, format_spec['default'])
        fmt = spec.get('format', 'hex')
        width = spec.get('width', 8)

        # Check for undefined values
        if value == -1:
            return "X/Z"  # Indicate undefined value

        # Format based on specified format
        if fmt == 'bin':
            return f"0b{value:0{width}b}"
        elif fmt == 'dec':
            return f"{value:{width}d}"
        else:  # hex is default
            return f"0x{value:0{width}X}"

    def __str__(self):
        """
        Provide a detailed string representation of the APB cycle

        Returns:
            Formatted string with all fields
        """
        result = [
            "APB Cycle:",
            f"  Direction:  {self.direction}",
            f"  Address:    {self._format_field('paddr', self.paddr)}",
        ]

        # Data fields based on direction
        if self.direction == 'WRITE':
            result.append(f"  Write Data: {self._format_field('pwdata', self.pwdata)}")
            result.append(f"  Strobes:    {self._format_field('pstrb', self.pstrb)}")
        else:
            result.append(f"  Read Data:  {self._format_field('prdata', self.prdata)}")

        # Control fields
        result.append(f"  Protection: {self._format_field('pprot', self.pprot)}")
        result.append(f"  Slave Err:  {self._format_field('pslverr', self.pslverr)}")

        # Timing information
        if self.start_time > 0:
            result.append(f"  Start Time: {self.start_time} ns")
        if self.end_time > 0:
            result.extend(
                (
                    f"  End Time:   {self.end_time} ns",
                    f"  Duration:   {self.end_time - self.start_time} ns",
                )
            )
        # Transaction count
        result.append(f"  Count:      {self.count}")

        return "\n".join(result)

    def formatted(self, addr_width=32, data_width=32, strb_width=4, compact=False):
        """
        Return a formatted string representation with configurable widths

        Args:
            addr_width: Address width in bits
            data_width: Data width in bits
            strb_width: Strobe width in bits
            compact: If True, return a compact one-line representation

        Returns:
            Formatted string representation
        """
        # Format specs based on provided widths
        format_spec = {
            'addr': {'format': 'hex', 'width': addr_width // 4},
            'data': {'format': 'hex', 'width': data_width // 4},
            'strb': {'format': 'bin', 'width': strb_width},
            'prot': {'format': 'hex', 'width': 2},
            'write': {'format': 'dec', 'width': 1},
            'slverr': {'format': 'dec', 'width': 1},
            'default': {'format': 'hex', 'width': 8}
        }

        if compact:
            return self._format_helper_compact(format_spec)
            # Detailed multi-line representation
        result = [
            "APB Cycle:",
            f"  Time:       {self.start_time}"
            f"  Direction:  {self.direction}",
            f"  Address:    {self._format_field('paddr', self.paddr, format_spec)}",
        ]
        if self.direction == 'WRITE':
            result.append(f"  Write Data: {self._format_field('pwdata', self.pwdata, format_spec)}")
            result.append(f"  Strobes:    {self._format_field('pstrb', self.pstrb, format_spec)}")
        else:
            result.append(f"  Read Data:  {self._format_field('prdata', self.prdata, format_spec)}")

        result.append(f"  Protection: {self._format_field('pprot', self.pprot, format_spec)}")
        result.append(f"  Slave Err:  {self._format_field('pslverr', self.pslverr, format_spec)}")

        if self.start_time > 0:
            result.append(f"  Start Time: {self.start_time} ns")
        if self.end_time > 0:
            result.extend(
                (
                    f"  End Time:   {self.end_time} ns",
                    f"  Duration:   {self.end_time - self.start_time} ns",
                )
            )
        result.append(f"  Count:      {self.count}")

        return "\n".join(result)

    def _format_helper_compact(self, format_spec):
        # Compact one-line representation
        fields = [
            f"time={self.start_time}",
            f"dir={self.direction}",
            f"addr={self._format_field('paddr', self.paddr, format_spec)}",
        ]
        if self.direction == 'WRITE':
            fields.append(f"wdata={self._format_field('pwdata', self.pwdata, format_spec)}")
            fields.append(f"strb={self._format_field('pstrb', self.pstrb, format_spec)}")
        else:
            fields.append(f"rdata={self._format_field('prdata', self.prdata, format_spec)}")

        fields.append(f"prot={self._format_field('pprot', self.pprot, format_spec)}")

        if self.pslverr:
            fields.append(f"err={self.pslverr}")

        return f"APBCycle({', '.join(fields)})"


class APBTransaction(Randomized):
    """Enhanced APB Transaction class with improved formatting and configuration"""

    def __init__(self, data_width=32, addr_width=32, strb_width=4, constraints=None, **kwargs):
        """
        Initialize APB Transaction

        Args:
            data_width: Data width in bits
            addr_width: Address width in bits
            strb_width: Strobe width in bits
            constraints: Optional constraints dictionary or FlexRandomizer
            **kwargs: Initial values for fields
        """
        super().__init__()

        # Store configuration
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.addr_mask = (strb_width - 1)
        self.count = 0

        # Setup randomizer
        if constraints is None:
            addr_min_hi = (4 * self.strb_width) - 1
            addr_max_lo = (4 * self.strb_width)
            addr_max_hi = (32 * self.strb_width) - 1

            if isinstance(constraints, dict):
                # Use directly if dictionary
                self.randomizer = FlexRandomizer(constraints)
            else:
                # Default constraints
                self.randomizer = FlexRandomizer({
                    'pwrite': ([(0, 0), (1, 1)], [1, 1]),
                    'paddr': ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)], [4, 1]),
                    'pstrb': ([(15, 15), (0, 14)], [4, 1]),
                    'pprot': ([(0, 0), (1, 7)], [4, 1])
                })
        elif isinstance(constraints, FlexRandomizer):
            # Use provided FlexRandomizer
            self.randomizer = constraints
        else:
            # Try to convert to FlexRandomizer
            self.randomizer = FlexRandomizer(constraints)

        # Initialize field values
        self.direction = 'unknown'
        self.pwrite = kwargs.get('pwrite', 0)
        self.paddr = kwargs.get('paddr', 0)
        self.pstrb = kwargs.get('pstrb', 0)
        self.pprot = kwargs.get('pprot', 0)

        # Create APB Cycle
        self.cycle = APBCycle(
            start_time=kwargs.get('start_time', 0),
            count=kwargs.get('count', 0),
            direction=self.direction,
            pwrite=self.pwrite,
            paddr=self.paddr,
            pwdata=kwargs.get('pwdata', 0),
            prdata=kwargs.get('prdata', 0),
            pstrb=self.pstrb,
            pprot=self.pprot,
            pslverr=kwargs.get('pslverr', 0)
        )

        # Add randomized signals with full ranges
        self.add_rand("pwrite", [0, 1])
        self.add_rand("paddr", list(range(2**12)))
        self.add_rand("pstrb", list(range(2**strb_width)))
        self.add_rand("pprot", list(range(8)))

    def next(self):
        """
        Generate next transaction using randomizer

        Returns:
            APBCycle: Generated cycle
        """
        self.randomize()
        value_dict = self.randomizer.next()

        # Copy values to fields
        self.pwrite = value_dict['pwrite']
        self.paddr = value_dict['paddr'] & ~self.addr_mask
        self.pstrb = value_dict['pstrb']
        self.pprot = value_dict['pprot']
        self.direction = pwrite[self.pwrite]

        # Update cycle
        self.cycle.pwrite = self.pwrite
        self.cycle.direction = self.direction
        self.cycle.paddr = self.paddr
        self.cycle.pstrb = self.pstrb
        self.cycle.pprot = self.pprot
        self.cycle.pwdata = random.randint(0, (1 << self.data_width) - 1)

        # Return a copy of the cycle
        self.log.debug(f"Transaction pprot set to {self.pprot}")
        return copy.copy(self.cycle)

    def set_constrained_random(self):
        """
        Set fields using constrained randomization

        Returns:
            self for chaining
        """
        self.next()
        return self

    def __str__(self):
        """
        String representation using cycle's formatting

        Returns:
            Formatted string
        """
        return f"APB Transaction:\n{self.cycle.formatted(self.addr_width, self.data_width, self.strb_width)}"

    def formatted(self, compact=False):
        """
        Return a formatted representation

        Args:
            compact: If True, return a compact one-line representation

        Returns:
            Formatted string
        """
        if compact:
            return f"APBTransaction({self.cycle.formatted(self.addr_width, self.data_width, self.strb_width, compact=True)})"
        else:
            return self.__str__()
