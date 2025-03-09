from dataclasses import dataclass
from rtl_generators.verilog.verilog_parser import ParserHelper
from typing import Tuple


@dataclass
class SignalRecord:
    ''' DataClass for holding the info for a single signal'''
    interface: bool
    sig_type: str
    direction: str
    name: str
    packed: str
    unpacked: str
    compilerDirectiveSig: str
    compilerDirective: str
    drivers: int
    receivers: int


class Signal(object):
    '''The class maintains a list of signal records and performs all of the basic operations on them'''

    def __init__(self, signal_str=''):
        self.sigrec_list: list(SignalRecord) = []
        if len(signal_str) > 0:
            sigrec_list = ParserHelper.parsePortsList(signal_str)
            self._convert_sigrec_list(sigrec_list)


    def __repr__(self):
        return self.sigrec_list

    def _found_name(self, name: str) -> Tuple[bool, int]:  # sourcery skip: use-next
        for idx, sigrec in enumerate(self.sigrec_list):
            if sigrec.name == name:
                return True, idx
        return False, -1


    def _convert_sigrec_list(self, rec_list):
        for rec in rec_list:
            sigrec = Signal._convert_sigrec(rec)
            found, idx = self._found_name(sigrec.name)
            if found:
                current = self.sigrec_list[idx]
                packed_merge = ParserHelper.arrayMerge(current.packed, sigrec.packed)
                unpacked_merge = ParserHelper.arrayMerge(current.unpacked, sigrec.unpacked)
                current.packed = packed_merge
                current.unpacked = unpacked_merge
            else:
                self.sigrec_list.append(sigrec)


    @staticmethod
    def _convert_sigrec(rec) -> SignalRecord:
        return SignalRecord(rec['interface'],
                            rec['type'],
                            rec['direction'],
                            rec['name'],
                            rec['packed'],
                            rec['unpacked'],
                            rec['compilerDirectiveSig'],
                            rec['compilerDirective'],
                            rec['drivers'],
                            rec['receivers'])


    def add_port_string(self, signal_str):
        signal_str = ParserHelper.cleanString(signal_str)
        sigrec_list = ParserHelper.parsePortsList(signal_str)
        self._convert_sigrec_list(sigrec_list)
        return self.sigrec_list


    def __get_max_lengths(self):
        max_dir = 0 
        max_type = 0
        max_packed = 0
        max_name = 0
        for sigrec in self.sigrec_list:  # Iterate through the list
            if len(sigrec.direction) > max_dir:
                max_dir = len(sigrec.direction)
            if len(sigrec.sig_type) > max_type:
                max_type = len(sigrec.sig_type)
            if len(sigrec.packed) > max_packed:
                max_packed = len(sigrec.packed)
            if len(sigrec.name) > max_name:
                max_name = len(sigrec.name)
        return (max_dir, max_type, max_packed, max_name)


    def create_wire_string(self) -> str:
        (_, max_type, max_packed, max_name) = self.__get_max_lengths()

        wire_str = ''
        for sigrec in self.sigrec_list:  # Iterate through the list
            sig_type = ParserHelper.padRight(sigrec.sig_type, max_type)
            packed = ParserHelper.padRight(sigrec.packed, max_packed)
            if len(sigrec.unpacked) == 0:
                name = sigrec.name
                wire_str += f'{sig_type} {packed} {name};\n'
            else:
                name = ParserHelper.padRight(sigrec.name, max_name)
                wire_str += f'{sig_type} {packed} {name} {sigrec.unpacked};\n'

        return wire_str


    def create_port_string(self) -> str:
        (max_dir, max_type, max_packed, max_name) = self.__get_max_lengths()

        comma = ','
        port_str = ''
        last = len(self.sigrec_list)
        for idx, sigrec in enumerate(self.sigrec_list):
            if idx == last -1:
                comma = ''
            sig_dir = ParserHelper.padRight(sigrec.direction, max_dir)
            sig_type = ParserHelper.padRight(sigrec.sig_type, max_type)
            packed = ParserHelper.padRight(sigrec.packed, max_packed)
            if len(sigrec.unpacked) == 0:
                name = sigrec.name
                port_str += f'    {sig_dir} {sig_type} {packed} {name}{comma}\n'
            else:
                name = ParserHelper.padRight(sigrec.name, max_name)
                port_str += f'    {sig_dir} {sig_type} {packed} {name} {sigrec.unpacked}{comma}\n'

        return port_str
            