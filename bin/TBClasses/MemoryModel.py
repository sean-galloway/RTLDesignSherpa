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
            self.mem = bytearray(preset_values)
            self.preset_values = bytearray(preset_values)
        else:
            self.mem = bytearray(self.size)
            self.preset_values = bytearray(self.size)


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

        # Write data to memory based on strobe
        for i in range(data_len):
            target_address = start + i
            if strobe & (1 << i):
                self.mem[target_address] = data[i]
                self.log.debug(f"Writing byte: mem[{target_address:08X}] = {data[i]:02X}")


    def read(self, address, length):
        line = address // self.bytes_per_line
        offset = address % self.bytes_per_line
        return self.mem[line * self.bytes_per_line + offset:line * self.bytes_per_line + offset + length]


    def reset(self, to_preset=False):
        self.mem = bytearray(self.preset_values) if to_preset else bytearray(self.size)


    def expand(self, additional_lines):
        additional_size = additional_lines * self.bytes_per_line
        self.mem.extend([0] * additional_size)
        self.preset_values.extend([0] * additional_size)
        self.num_lines += additional_lines
        self.size += additional_size


    def dump(self):
        mem_dump = "-" * 60 + '\n'
        for i in range(self.num_lines):
            addr = i * self.bytes_per_line
            line_data = self.mem[addr:addr + self.bytes_per_line]
            value = int.from_bytes(line_data, byteorder='little')
            mem_dump += f"Register {i:4}: Address 0x{addr:08X} - Value 0x{value:0{self.bytes_per_line * 2}X}\n"
        mem_dump += "-" * 60 + '\n'
        return '\n'+mem_dump


    def integer_to_bytearray(self, value, byte_length=None):
        if byte_length is None:
            byte_length = (value.bit_length() + 7) // 8
        return bytearray(value.to_bytes(byte_length, byteorder='little'))


    def bytearray_to_integer(self, byte_array):
        return int.from_bytes(byte_array, byteorder='little')
