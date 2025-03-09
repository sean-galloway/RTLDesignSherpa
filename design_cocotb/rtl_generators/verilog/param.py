from dataclasses import dataclass
from rtl_generators.verilog.verilog_parser import ParserHelper
from typing import Tuple


@dataclass
class ParameterRecord:
    ''' DataClass for the Parameters that could be on a parsed module'''
    sig_type: str
    name: str
    value: str
    packed: str
    unpacked: str
    compilerDirectiveSig: str
    compilerDirective: str


class Param(object):
    '''The class maintains a list of parameter records and performs all of the basic operations on them'''

    def __init__(self, signal_str=''):
        self.paramrec_list: list(ParameterRecord) = []
        if len(signal_str) > 0:
            paramrec_list = ParserHelper.parseParametersList(signal_str)
            self._convert_paramrec_list(paramrec_list)


    def __repr__(self):
        return self.paramrec_list


    def _found_name(self, name: str) -> Tuple[bool, int]:  # sourcery skip: use-next
        for idx, paramrec in enumerate(self.paramrec_list):
            if paramrec.name == name:
                return True, idx
        return False, -1


    def _convert_paramrec_list(self, rec_list):
        for rec in rec_list:
            paramrec = self._convert_paramrec(rec)
            found, idx = self._found_name(paramrec.name)
            if found:
                current = self.paramrec_list[idx]
                packed_merge = ParserHelper.arrayMerge(current.packed, paramrec.packed)
                unpacked_merge = ParserHelper.arrayMerge(current.unpacked, paramrec.unpacked)
                current.packed = packed_merge
                current.unpacked = unpacked_merge
            else:
                self.paramrec_list.append(paramrec)


    @staticmethod
    def _convert_paramrec(rec) -> ParameterRecord:
        return ParameterRecord(rec['type'],
                            rec['name'],
                            rec['value'],
                            rec['packed'],
                            rec['unpacked'],
                            rec['compilerDirectiveSig'],
                            rec['compilerDirective'])


    def __get_max_lengths(self):
        max_type = 0
        max_packed = 0
        max_name = 0
        for paramrec in self.paramrec_list:  # Iterate through the list
            if len(paramrec.sig_type) > max_type:
                max_type = len(paramrec.sig_type)
            if len(paramrec.packed) > max_packed:
                max_packed = len(paramrec.packed)
            if len(paramrec.name) > max_name:
                max_name = len(paramrec.name)
        return (max_type, max_packed, max_name)



    def set_param_value(self, param, value):
        for paramrec in self.paramrec_list:
            if paramrec.name == param:
                paramrec.value = value
                break


    def add_param_string(self, signal_str):
        signal_str = ParserHelper.cleanString(signal_str)
        paramrec_list = ParserHelper.parseParametersList(signal_str)
        self._convert_paramrec_list(paramrec_list)
        return self.paramrec_list


    def create_param_string(self) -> str:
        (max_type, max_packed, max_name) = self.__get_max_lengths()
        param_str = ''
        comma = ',\n'
        last = len(self.paramrec_list)
        for idx, paramrec in enumerate(self.paramrec_list):
            if idx == last -1:
                comma = ''
            sig_type = ParserHelper.padRight(paramrec.sig_type, max_type)
            packed = ParserHelper.padRight(paramrec.packed, max_packed)            
            if len(paramrec.unpacked) == 0:
                name = paramrec.name
                param_str += f'parameter {sig_type} {packed} {name} = {paramrec.value}{comma}'
            else:
                name = ParserHelper.padRight(paramrec.name, max_name)
                param_str += f'parameter {sig_type} {packed} {name} {paramrec.unpacked}  = {paramrec.value}{comma}'

        return param_str

    def create_param_instance(self) -> str:
        ret_list = [
            f'.{paramrec.name}({paramrec.value})'
            for paramrec in self.paramrec_list
        ]
        return ','.join(ret_list)
            