'''Generic Memory Model Class used by the various components - NumPy version'''
import numpy as np

class MemoryModel:

    def __init__(self, num_lines, bytes_per_line, log, preset_values=None, debug=None):
        self.num_lines = num_lines
        self.bytes_per_line = bytes_per_line
        self.size = num_lines * bytes_per_line
        self.log = log
        self.debug = debug

        if preset_values:
            if len(preset_values) != self.size:
                raise ValueError("Preset values length must match the total memory size")
            # Convert bytearray to numpy array
            self.mem = np.frombuffer(bytearray(preset_values), dtype=np.uint8).copy()
            self.preset_values = np.frombuffer(bytearray(preset_values), dtype=np.uint8).copy()
        else:
            self.mem = np.zeros(self.size, dtype=np.uint8)
            self.preset_values = np.zeros(self.size, dtype=np.uint8)


    def write(self, address, data, strobe):
        if not isinstance(data, bytearray):
            raise TypeError("Data must be a bytearray")

        start = address
        data_len = len(data)
        end = start + len(data)

        # Check for memory overflow
        if end > self.size:
            raise ValueError("Write exceeds memory bounds")

        # Ensure the data and strobe lengths match
        if data_len * 8 < strobe.bit_length():
            raise ValueError("Data length does not match strobe length")

        # Format the address and data as hexadecimal for debugging
        hex_address = f"0x{address:08X}"
        hex_data = [f"0x{byte:02X}" for byte in data]

        self.log.debug(f"Writing to memory: address={hex_address}, data={hex_data}, strobe={strobe:08b}")

        # Convert bytearray to numpy array
        data_np = np.frombuffer(data, dtype=np.uint8)

        # Create a mask array from the strobe
        mask = np.zeros(data_len, dtype=bool)
        for i in range(data_len):
            if strobe & (1 << i):
                mask[i] = True
                if self.debug:
                    self.log.debug(f"Writing byte: mem[{start+i:08X}] = {data_np[i]:02X}")

        # Apply the masked write operation in one vectorized operation
        if np.any(mask):
            indices = np.arange(start, start + data_len)[mask]
            self.mem[indices] = data_np[mask]


    def read(self, address, length):
        line = address // self.bytes_per_line
        offset = address % self.bytes_per_line
        # Convert back to bytearray to maintain API compatibility
        return bytearray(self.mem[line * self.bytes_per_line + offset:line * self.bytes_per_line + offset + length])


    def reset(self, to_preset=False):
        if to_preset:
            self.mem = self.preset_values.copy()
        else:
            self.mem = np.zeros(self.size, dtype=np.uint8)


    def expand(self, additional_lines):
        additional_size = additional_lines * self.bytes_per_line
        # Use numpy's append for more efficient expansion
        self.mem = np.append(self.mem, np.zeros(additional_size, dtype=np.uint8))
        self.preset_values = np.append(self.preset_values, np.zeros(additional_size, dtype=np.uint8))
        self.num_lines += additional_lines
        self.size += additional_size


    def dump(self):
        mem_dump = "-" * 60 + '\n'
        for i in range(self.num_lines):
            addr = i * self.bytes_per_line
            # Slice the numpy array and convert to bytes for consistent behavior
            line_data = bytes(self.mem[addr:addr + self.bytes_per_line])
            value = int.from_bytes(line_data, byteorder='little')
            mem_dump += f"Register {i:4}: Address 0x{addr:08X} - Value 0x{value:0{self.bytes_per_line * 2}X}\n"
        mem_dump += "-" * 60 + '\n'
        return '\n'+mem_dump


    def integer_to_bytearray(self, value, byte_length=None):
        # Ensure value is a valid integer
        if not isinstance(value, int):
            raise TypeError("Value must be an integer")

        if value < 0:
            raise ValueError("Negative integers are not supported for conversion")

        # Calculate byte_length if not provided
        if byte_length is None:
            byte_length = (value.bit_length() + 7) // 8

        # Check if the value can fit into the specified byte_length
        max_value = (1 << (byte_length * 8)) - 1  # Maximum value for the given byte_length
        if value > max_value:
            raise OverflowError(
                f"Value {value} is too large to fit into {byte_length} bytes. "
                f"Maximum allowed value is {max_value}."
            )

        # Perform the conversion
        return bytearray(value.to_bytes(byte_length, byteorder='little'))


    def bytearray_to_integer(self, byte_array):
        return int.from_bytes(byte_array, byteorder='little')
