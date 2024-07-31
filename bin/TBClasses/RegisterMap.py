from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.handle import SimHandleBase
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.drivers import BusDriver
from cocotb.utils import get_sim_time
from cocotb.queue import Queue
from cocotb.result import TestFailure
from cocotb_coverage.crv import Randomized
from APB import APBCycle
import importlib.util
from typing import List, Dict
import pprint


class RegisterMap:
    def __init__(self, filename, apb_data_width, apb_addr_width, start_address, log):
        self.log = log
        self.filename = filename
        raw_dict = self._load_registers(filename)
        self.registers = self._process_registers(raw_dict)
        self.log.debug(f'Dumping {filename} registers:\n%s', pprint.pformat(self.registers))
        self.log.debug(pprint.pprint(self.registers))
        self.current_state = self._initialize_state()
        self.write_storage = {}
        self.apb_data_width = apb_data_width
        self.apb_addr_width = apb_addr_width
        self.start_address = start_address
        self.addr_mask = (1 << apb_addr_width) - 1
        self.data_mask = (1 << apb_data_width) - 1
        self.bytes_per_word = apb_data_width // 8


    def _load_registers(self, filename):
        spec = importlib.util.spec_from_file_location("register_dict", filename)
        register_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(register_module)
        
        # Assuming the dictionary in the file is named 'top_block'
        return register_module.top_block


    def _process_registers(self, raw_dict):
        def recursive_search(d):
            if isinstance(d, dict):
                if 'type' in d:
                    yield d
                for v in d.values():
                    yield from recursive_search(v)
            elif isinstance(d, list):
                for item in d:
                    yield from recursive_search(item)

        processed_registers = {}
        for item in recursive_search(raw_dict):
            if item['type'] == 'reg':
                reg_name = item.get('name', '')
                self.log.debug(f'processing: {reg_name}')
                if reg_name:
                    processed_registers[reg_name] = item

        return processed_registers


    def _initialize_state(self):
        state = {}
        self.log.debug(f'Init: {self.filename}')
        for reg_name, reg_info in self.registers.items():
            self.log.debug(f'Loop: {reg_name}')
            if 'count' in reg_info:
                state[reg_name] = [int(reg_info['default'], 16)] * int(reg_info['count'])
            else:
                state[reg_name] = int(reg_info['default'], 16)
        return state


    def get_register_field_map(self):
        register_field_map = {}
        for register_name, register_info in self.registers.items():
            fields = [field for field in register_info.keys() if register_info[field]['type'] == 'field']
            register_field_map[register_name] = fields
        return register_field_map


    def get_register_offset_map(self):
        return {reg_name: int(reg_info['offset'], 16) for reg_name, reg_info in self.registers.items()}


    def get_combined_register_map(self):
        field_map = self.get_register_field_map()
        offset_map = self.get_register_offset_map()
        return {
            reg: {'fields': field_map[reg], 'offset': offset}
            for reg, offset in offset_map.items()
        }


    def write(self, register, field, value):
        if register not in self.registers:
            raise ValueError(f"Register {register} not found")
        if field not in self.registers[register]:
            raise ValueError(f"Field {field} not found in register {register}")
        
        reg_info = self.registers[register]
        field_info = reg_info[field]
        
        mask = self._create_mask(field_info['offset'])
        field_width = self._get_field_width(field_info['offset'])
        
        num_words = (field_width + self.apb_data_width - 1) // self.apb_data_width
        
        if 'count' in reg_info:
            if register not in self.write_storage:
                self.write_storage[register] = [None] * int(reg_info['count'])
            for i in range(int(reg_info['count'])):
                if self.write_storage[register][i] is None:
                    self.write_storage[register][i] = self.current_state[register][i]
                for j in range(num_words):
                    word_mask = mask & self.data_mask
                    word_value = (value >> (j * self.apb_data_width)) & self.data_mask
                    self.write_storage[register][i+j] = (self.write_storage[register][i+j] & ~word_mask) | (word_value & word_mask)
                    mask >>= self.apb_data_width
        else:
            if register not in self.write_storage:
                self.write_storage[register] = [self.current_state[register]] * num_words
            for j in range(num_words):
                word_mask = mask & self.data_mask
                word_value = (value >> (j * self.apb_data_width)) & self.data_mask
                self.write_storage[register][j] = (self.write_storage[register][j] & ~word_mask) | (word_value & word_mask)
                mask >>= self.apb_data_width


    def _create_mask(self, offset):
        if ':' not in offset:
            return 1 << int(offset)
        high, low = map(int, offset.split(':'))
        return ((1 << (high - low + 1)) - 1) << low


    def _get_field_width(self, offset):
        if ':' not in offset:
            return 1
        high, low = map(int, offset.split(':'))
        return high - low + 1


    def generate_apb_cycles(self) -> List[APBCycle]:
        apb_cycles = []
        for register, value in self.write_storage.items():
            reg_info = self.registers[register]
            base_address = (self.start_address + int(reg_info['address'], 16)) & self.addr_mask
            for i, v in enumerate(value):
                if (
                    isinstance(value, list)
                    and v is not None
                    or not isinstance(value, list)
                ):
                    address = (base_address + i * self.bytes_per_word) & self.addr_mask
                    apb_cycles.append(APBCycle(
                        start_time=0,  # You might want to set this appropriately
                        count=i,
                        direction='WRITE',
                        pwrite=1,
                        paddr=address,
                        pwdata=v,
                        pstrb=(1 << (self.bytes_per_word)) - 1,  # Full write strobe
                        prdata=0,
                        pprot=0,
                        pslverr=0
                    ))
        self._update_current_state()
        self.write_storage.clear()

        return apb_cycles


    def _update_current_state(self):
        for register, value in self.write_storage.items():
            if isinstance(self.current_state[register], list):
                for i, v in enumerate(value):
                    if v is not None:
                        self.current_state[register][i] = v
            else:
                self.current_state[register] = value[0]  # Take the first word for non-array registers


    def generate_read_transactions(self) -> List[APBCycle]:
        # sourcery skip: low-code-quality
        read_transactions = []
        for register, info in self.registers.items():
            address = (self.start_address + int(info['address'], 16)) & self.addr_mask
            size = int(info['size'])
            count = int(info.get('count', '1'))
            
            for i in range(count):
                expected_data = ''
                for j in range(0, size * 8, self.apb_data_width):
                    word_address = (address + (i * size) + (j // 8)) & self.addr_mask
                    word_expected = ''
                    
                    for field_name, field_info in info.items():
                        if isinstance(field_info, dict) and field_info.get('type') == 'field':
                            field_offset = self._parse_offset(field_info['offset'])
                            field_width = field_offset[1] - field_offset[0] + 1
                            field_value = ''
                            
                            if 'ro' in field_info.get('sw', '').lower() or 'rw' in field_info.get('sw', '').lower():
                                field_value = format(int(field_info['default'], 16), f'0{field_width}b')
                            else:
                                field_value = 'X' * field_width
                            
                            start = max(0, field_offset[0] - j)
                            end = min(self.apb_data_width, field_offset[1] - j + 1)
                            if start < self.apb_data_width and end > 0:
                                word_expected = (word_expected.ljust(start, '0') + 
                                                    field_value[max(0, j - field_offset[0]):min(field_width, j + self.apb_data_width - field_offset[0])] + 
                                                    word_expected[end:].ljust(self.apb_data_width, '0'))
                    
                    expected_data += word_expected.ljust(self.apb_data_width, '0')
                    
                    read_transactions.append(APBCycle(
                        start_time=0,
                        count=i,
                        direction='READ',
                        pwrite=0,
                        paddr=word_address,
                        pwdata=0,
                        pstrb=0,
                        prdata=int(word_expected.replace('X', '0'), 2),
                        pprot=0,
                        pslverr=0
                    ))
        
        return read_transactions


    def generate_write_even_transactions(self) -> List[APBCycle]:
        return self._generate_write_transactions(even=True)


    def generate_write_odd_transactions(self) -> List[APBCycle]:
        return self._generate_write_transactions(even=False)


    def _generate_write_transactions(self, even: bool) -> List[APBCycle]:
        # sourcery skip: low-code-quality
        write_transactions = []
        for register, info in self.registers.items():
            # Check if the register is writable
            if 'rw' not in info.get('sw', '').lower():
                continue  # Skip this register if it's not writable
    
            address = (self.start_address + int(info['address'], 16)) & self.addr_mask
            size = int(info['size'])
            count = int(info.get('count', '1'))
            
            for i in range(count):
                for j in range(0, size * 8, self.apb_data_width):
                    word_address = (address + (i * size) + (j // 8)) & self.addr_mask
                    word_data = 0
                    word_mask = 0
                    
                    # Generate data and mask based on field writeability
                    for field_name, field_info in info.items():
                        if isinstance(field_info, dict) and field_info.get('type') == 'field' and 'rw' in field_info.get('sw', '').lower():
                            field_offset = self._parse_offset(field_info['offset'])
                            for bit in range(field_offset[0], field_offset[1] + 1):
                                if (bit % 2 == 0 and even) or (bit % 2 == 1 and not even):
                                    word_data |= (1 << (bit % self.apb_data_width))
                                word_mask |= (1 << (bit % self.apb_data_width))
                    
                    if word_mask:  # Only create a transaction if there are writable bits
                        write_transactions.append(APBCycle(
                            start_time=0,
                            count=i,
                            direction='WRITE',
                            pwrite=1,
                            paddr=word_address,
                            pwdata=word_data,
                            pstrb=word_mask & ((1 << (self.apb_data_width // 8)) - 1),
                            prdata=0,
                            pprot=0,
                            pslverr=0
                        ))
        
        return write_transactions
    

    def compare_transactions(self, expected: List[APBCycle], found: List[APBCycle], title: str) -> List[Dict]:
        miscompares = []
        for exp, fnd in zip(expected, found):
            if exp.paddr != fnd.paddr:
                continue  # Skip if addresses don't match

            exp_bits = format(exp.prdata, f'0{self.apb_data_width}b')
            fnd_bits = format(fnd.prdata, f'0{self.apb_data_width}b')

            for register, info in self.registers.items():
                reg_address = (self.start_address + int(info['address'], 16)) & self.addr_mask
                if reg_address == exp.paddr:
                    for field_name, field_info in info.items():
                        if isinstance(field_info, dict) and field_info.get('type') == 'field':
                            field_offset = self._parse_offset(field_info['offset'])
                            start = field_offset[0] % self.apb_data_width
                            end = min(field_offset[1] % self.apb_data_width + 1, self.apb_data_width)
                            
                            exp_field = exp_bits[start:end]
                            fnd_field = fnd_bits[start:end]
                            
                            if 'X' not in exp_field and exp_field != fnd_field:
                                miscompares.append({
                                    'title': title,
                                    'register': register,
                                    'field': field_name,
                                    'address': f'0x{exp.paddr:X}',
                                    'expected': exp_field,
                                    'found': fnd_field,
                                    'bit_positions': f'{start}-{end-1}'
                                })

        return miscompares


    def _parse_offset(self, offset):
        if ':' in offset:
            high, low = map(int, offset.split(':'))
            return (low, high)
        else:
            bit = int(offset)
            return (bit, bit)


# Usage example:
# reg_map = RegisterMap('registers.json', apb_data_width=32, apb_addr_width=24, start_address=0x7F0000)
# reg_map.write('descr_map', 'descr_data', 0xFFFFFFFFFFFFFFFF)  # 64-bit write
# apb_cycles = reg_map.generate_apb_cycles()
