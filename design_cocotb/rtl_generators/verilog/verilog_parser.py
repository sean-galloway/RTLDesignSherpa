from __future__ import print_function
import re


class ParserHelper:

    @staticmethod
    def processSignalFreeform(strVal, pDir, pType='logic'):
        '''returns a list of signal records from a string of free form code
        '''
        #  massage the assignment into a list
        strValSub = re.sub(r'\{', r' ', strVal)
        strValSub = re.sub(r'\}', r' ', strValSub)
        strValSub = re.sub(r'\(', r' ', strValSub)
        strValSub = re.sub(r'\)', r' ', strValSub)
        strValSub = re.sub(r' \: ', r' ', strValSub)
        strValSub = re.sub(r'\&', r' ', strValSub)
        strValSub = re.sub(r'\?', r' ', strValSub)
        strValSub = re.sub(r'\^', r' ', strValSub)
        strValSub = re.sub(r'\|', r' ', strValSub)
        strValSub = re.sub(r'\!', r' ', strValSub)
        strValSub = re.sub(r'\s', r',', strValSub)
        portList = []

        sigList = re.split(',', strValSub)
        for strSig in sigList:
            if len(strSig) > 0 and not re.match(r".*'.*", strSig):
                portRec = ParserHelper.processSignal(strSig, pDir, pType)
                portList.append(portRec)

        return portList

    @staticmethod
    def processSignal(strVal, pDir, pType='logic'):
        '''returns a signal record from a text signal
        '''
        strValSub = re.sub(r'\s', r'', strVal)
        strValSub = re.sub(r'\n', r'', strValSub)
        pName = ParserHelper.removeArrays(strValSub)
        pPackedArrays = ParserHelper.getArrays(strVal)
        return {
            'interface': False,
            'type': pType,
            'direction': pDir,
            'name': pName,
            'packed': pPackedArrays,
            'unpacked': '',
            'compilerDirectiveSig': '',
            'compilerDirective': '',
            'drivers': 0,
            'receivers': 0,
        }

    @staticmethod
    def isNumber(strVal):
        '''returns true if the value is a number
        '''
        try:
            float(strVal)
            return True
        except ValueError:
            return False

    @staticmethod
    def getLeftRight(strVal):
        '''Grabs the left/right values from an array like left:right.
        if the array is a single value like: 15, then it returns 15, 15
        '''
        strVal = re.sub(r'\[', '', strVal)
        strVal = re.sub(r'\]', '', strVal)
        if match := re.match(r'(.*):(.*)', strVal):
            leftStr = match[1]
            rightStr = match[2]
        else:
            leftStr = strVal
            rightStr = strVal
        return (leftStr, rightStr)

    @staticmethod
    def getMax(strValA, strValB):
        '''returns the maximum value of the two
        if either aren't numeric, that wins
        '''
        if not ParserHelper.isNumber(strValA):
            return strValA
        elif not ParserHelper.isNumber(strValB):
            return strValB
        else:
            return strValA if float(strValA) > float(strValB) else strValB

    @staticmethod
    def getMin(strValA, strValB):
        '''returns the minimum value of the two
        if either aren't numeric, that wins
        '''
        if not ParserHelper.isNumber(strValA):
            return strValA
        elif not ParserHelper.isNumber(strValB):
            return strValB
        else:
            return strValB if float(strValA) > float(strValB) else strValA

    @staticmethod
    def arrayMerge(strValA, strValB, strName=''):
        """Takes two arrays and returns the Max left and Min right component.
        examples:
            strValA        strValB        return
            [15:0]        [31:16]        [31:0]
            [15]          [0]            [15:0]
            [P-1:0]       [10:0]        [P-1:0]
        """
        a = re.sub(r'\[', r'', strValA)
        b = re.sub(r'\[', r'', strValB)
        a = re.sub(r']', r',', a)
        b = re.sub(r']', r',', b)
        aList = re.split(r',', a)
        bList = re.split(r',', b)
        mergeStr = ''

        if len(aList) != len(bList):
            raise ValueError(f'Array Mismatch in signal {strName}: {strValA}, {strValB}')

        for i in range(len(aList)):
            if len(aList[i]) == 0:
                continue
            (la, ra) = ParserHelper.getLeftRight(aList[i])
            (lb, rb) = ParserHelper.getLeftRight(bList[i])
            maxStr = ParserHelper.getMax(la, lb)
            minStr = ParserHelper.getMin(ra, rb)
            mergeStr += f'[{maxStr}:{minStr}]'

        return mergeStr

    @staticmethod
    def isRange(strVal):
        """Returns True if the string is a SystemVerilog range.
        """
        return re.search(r'\[.*\]', strVal) is not None

    @staticmethod
    def isInterface(strVal):
        """Returns True if the strVal describes an interface with a
        module port definition.
        """

        if len(strVal) == 0:
            return False

        x = re.split(r' ', strVal)[0]

        return x not in ["input", "output", "inout", "ref", "wire"]

    @staticmethod
    def getArrays(strVal):
        """Returns arrays range(s).
        """
        # add @ around ranges to split by space
        strVal = re.sub(r'[ ]*\[', r'@[', strVal)
        lval = re.split(r'@', strVal)

        return ''.join(l for l in lval if ParserHelper.isRange(l))

    @staticmethod
    def removeArrays(strVal):
        """Returns a string without range(s).
        """
        # add @ around ranges to split by space
        strVal = re.sub(r'[ ]*\[', r'@[', strVal)
        lval = re.split(r'@', strVal)

        return '' if type(lval) is None else lval[0]


    @staticmethod
    def padRight(strVal,maxLen):
        return strVal + ' '*(maxLen-len(strVal))

    @staticmethod
    def getNameAndType(strVal):
        """Returns name and type of a string like:
             - "int [31:0] GEN [31:0]" =>
                   ('int [31:0]', 'GEN [31:0]')

             - "output logic name" =>
                   ('output logic', 'name')

             - "interface.slave name" =>
                   ('interface.slave', 'name')
         """
        strVal = strVal.lstrip()
        strVal = strVal.rstrip()
        x = re.split(' ', strVal)

        pName = ''
        for _ in range(len(x)):
            v = x.pop()
            if ParserHelper.isRange(v):
                pName = v + pName
            else:
                x.append(v)
                break

        if len(x) != 0:
            pName = x.pop() + pName

        pType = ' '.join(x) if len(x) != 0 else ''
        return pType, pName

    @staticmethod
    def removeMultiLineComments(strVal):
        state = 0
        strnew = ''
        L = len(strVal)

        for i in range(L):
            if i < (L - 1) and (strVal[i] == '/' and strVal[i + 1] == '*'):
                state = 1

            if i > 1 and (strVal[i - 2] == '*' and strVal[i - 1] == '/'):
                state = 0

            if state == 0:
                strnew += strVal[i]
        return strnew


    @staticmethod
    def cleanString(string: str) -> str:
        # remove one line comments
        x = re.sub(r'//.*[\n\r]', r'\n', string)
        # remove multi-line comments
        x = ParserHelper.removeMultiLineComments(x)
        # Convert compiler directives to tags here...
        x = re.sub(r'`(.*)\n', r'<CompilerDirective:\1>,', x)
        # flatten the string module
        x = re.sub(r'[ \n\r\t]+', r' ', x)
        # remove everything before module
        x = re.sub(r'(^|.*[ ])module ', r'module ', x)
        # remove everything after the end of the module declaration
        x = re.sub(r'\);.*$', r');', x)
        # prepare the string to be parsed
        x = re.sub(r'[ ]*>', '>', x)
        x = re.sub(r'[ ]*=[ ]*', '=', x)
        x = re.sub(r'[ ]*\([ ]*', '(', x)
        x = re.sub(r'[ ]*\)[ ]*', ')', x)
        x = re.sub(r'[ ]*\[[ ]*', ' [', x)
        x = re.sub(r'[ ]*\][ ]*', '] ', x)
        x = re.sub(r'[ ]*,[ ]*', ',', x)
        x = re.sub(r'[ ]*;[ ]*', ';', x)
        x = re.sub(r'[ ]*\);', ');', x)
        x = re.sub(r'[ ]*\)\(', ')(', x)
        return x


    @staticmethod
    def parsePortsList(portStr):  # sourcery skip: low-code-quality
        """Returns a list of dictionaries with port direction,
        isInterface, packed array range(s), unpacked array range(s),
        type and name.
        """
        # get Parameter block without parenthesis
        x = portStr

        ports = re.split(',', x)
        portsList = []
        pTypePrev = ''
        pCompilerDirectiveSig = []

        for p in ports:
            pType = ''
            pName = ''
            pIsInterface = ''
            pPackedArrays = ''
            pUnpackedArrays = ''
            pCompilerDirective = ''
            pDir = ''
            pType = ''

            if re.match('<CompilerDirective:.*?>', p):

                p = re.sub(r'<CompilerDirective:(.*?)>', r'\1', p)
                pCompilerDirective = p

                if re.match('(ifdef)|(ifndef)', p) or re.match('else', p):

                    pCompilerDirectiveSig.append(p)

                elif re.match('endif', p):

                    done = False
                    while not done:
                        temp = pCompilerDirectiveSig.pop()
                        if re.match('(ifdef)|(ifndef)', temp):
                            done = True

            else:
                # Extract type and name
                pType, pName = ParserHelper.getNameAndType(p)

                # if pType is empty, it must be taken from the previous
                # port.
                if pType == '':
                    pType = pTypePrev
                else:
                    pTypePrev = pType

                pPackedArrays = ParserHelper.getArrays(pType)
                pUnpackedArrays = ParserHelper.getArrays(pName)

                pType = ParserHelper.removeArrays(pType)
                pName = ParserHelper.removeArrays(pName)

                if ParserHelper.isInterface(pType):
                    pIsInterface = True
                    # extract the identifier after the dot* (within
                    # interface port type)
                    pDir = re.sub(r'.*\.([a-zA-Z_][a-zA-Z_0-9]*).*',
                                  r'\1',
                                  pType)

                    # remove the dot and the following identifier
                    pType = re.sub(r'(.*)\.[a-zA-Z_][a-zA-Z_0-9]*[ ]*(.*)',
                                   r'\1 \2',
                                   pType)

                    pType = re.sub(r'[ ]*$', '', pType)

                else:
                    pIsInterface = False
                    # extract direction
                    pDir = re.sub(r'([a-zA-Z_][a-zA-Z_0-9]*)[ ]*.*', r'\1',
                                  pType)
                    # extract type
                    pType = re.sub(r'[a-zA-Z_][a-zA-Z_0-9]*[ ]*(.*)', r'\1',
                                   pType)

            if len(pType) == 0 and pDir != "inout":
                pType = 'logic'

            portRec = {'interface': pIsInterface,
                       'type': pType,
                       'direction': pDir,
                       'name': pName,
                       'packed': pPackedArrays,
                       'unpacked': pUnpackedArrays,
                       'compilerDirectiveSig': ','.join(pCompilerDirectiveSig),
                       'compilerDirective': pCompilerDirective,
                       'drivers': 0,
                       'receivers': 0}
            portsList.append(portRec)

        return portsList


    @staticmethod
    def parseParametersList(paramStr):  # sourcery skip: low-code-quality
        """Returns a list of dictionaries with parameter type,
        name and value.
        """

        # get Parameter block without parenthesis
        x = paramStr

        # remove parameter
        x = re.sub(r'[ ]*parameter[ ]*', r'', x)

        # protect comma in quotes
        in_quotes_re = re.compile('("[^"]+")')
        x = in_quotes_re.sub(lambda match: match.group().replace(",", "\x00"), x)

        # Split parameters list
        params = re.split(',', x)

        parametersList = []
        pCompilerDirectiveSig = []

        for p in params:
            pCompilerDirective = ''
            pType = ''
            pName = ''
            pValue = ''
            pPackedArrays = ''
            pUnpackedArrays = ''
            pCompilerDirective = ''

            if re.match('<CompilerDirective:.*?>', p):
                p = re.sub(r'<CompilerDirective:(.*?)>', r'\1', p)
                pCompilerDirective = p
                if re.match('(ifdef)|(ifndef)', p) or re.match('else', p):
                    pCompilerDirectiveSig.append(p)
                elif re.match('endif', p):
                    done = False
                    while not done:
                        temp = pCompilerDirectiveSig.pop()
                        if re.match('(ifdef)|(ifndef)', temp):
                            done = True
                else:
                    raise ValueError(f"Unknown Compiler directive: {p}")
            else:
                # Restore comma in quotes
                x = re.sub("\x00", ",", p)

                # Extract param default value
                x = re.split('=', x)
                pValue = x[1] if len(x) > 1 else ''
                x = x[0]

                # Extract type and name
                pType, pName = ParserHelper.getNameAndType(x)

                pPackedArrays = ParserHelper.getArrays(pType)
                pUnpackedArrays = ParserHelper.getArrays(pName)

                pType = ParserHelper.removeArrays(pType)
                pName = ParserHelper.removeArrays(pName)

            if pCompilerDirective == '' and pType == '' and pName == '' and \
               pValue == '' and pPackedArrays == '' and pUnpackedArrays == '':
                continue

            parametersList.append({'type': pType,
                                   'name': pName,
                                   'value': pValue,
                                   'packed': pPackedArrays,
                                   'unpacked': pUnpackedArrays,
                                   'compilerDirectiveSig':
                                   ','.join(pCompilerDirectiveSig),
                                   'compilerDirective': pCompilerDirective})

        return parametersList

class Parser:
    def __parseBlock(self, strVal):
        i = 0
        k = 0
        condition = True

        while condition:
            if strVal[i] == '(':
                k = k + 1
            elif strVal[i] == ')':
                k = k - 1

            i = i + 1

            if k <= 0:
                condition = False

        return (strVal[:i], strVal[i:])

    def __parseImportList(self):
        """Returns a list of import packages"""
        return []


    def __init__(self, moduleString):
        # remove one line comments
        x = re.sub(r'//.*[\n\r]', r'\n', moduleString)

        # remove multi-line comments
        x = ParserHelper.removeMultiLineComments(x)

        # Convert compiler directives to tags here...
        x = re.sub(r'`(.*)\n', r'<CompilerDirective:\1>,', x)

        # flatten the string module
        x = re.sub(r'[ \n\r\t]+', r' ', x)

        # remove everything before module
        x = re.sub(r'(^|.*[ ])module ', r'module ', x)

        # remove everything after the end of the module declaration
        x = re.sub(r'\);.*$', r');', x)

        # prepare the string to be parsed
        x = re.sub(r'[ ]*>', '>', x)
        x = re.sub(r'[ ]*=[ ]*', '=', x)
        x = re.sub(r'[ ]*\([ ]*', '(', x)
        x = re.sub(r'[ ]*\)[ ]*', ')', x)
        x = re.sub(r'[ ]*\[[ ]*', ' [', x)
        x = re.sub(r'[ ]*\][ ]*', '] ', x)
        x = re.sub(r'[ ]*,[ ]*', ',', x)
        x = re.sub(r'[ ]*;[ ]*', ';', x)
        x = re.sub(r'[ ]*\);', ');', x)
        x = re.sub(r'[ ]*\)\(', ')(', x)

        # parse moduleName
        searches = re.search('(?<=module )[a-zA-Z_][a-zA-Z_0-9]*', x)
        self.moduleNameStr = searches[0]

        # remove module + moduleName
        x = re.sub(r'.*module [a-zA-Z_][a-zA-Z_0-9]*[ ]*', '', x)

        # search and remove optional header import
        self.importList = []
        searches = re.search('(?<=import )[0-9a-zA-Z_,:\*]*', x)
        if searches is not None:
            self.importList = re.split(',', searches[0])
            x = re.sub(r'import [0-9a-zA-Z_,:\*]*;', '', x)

        # Check if there is parameters
        if x[0] == "#":
            # remove pound
            x = re.sub(r'#[ ]*', '', x)
            (self.parametersStr, x) = self.__parseBlock(x)

        else:
            self.parametersStr = ''

        # Retrieve ports list
        (self.portsStr, x) = self.__parseBlock(x)

        # Check again if there is parameters
        if x[0] == "#" and self.parametersStr != '':
            # remove pound
            x = re.sub(r'#[ ]*', '', x)
            (self.parametersStr, x) = self.__parseBlock(x)

        x = self.parametersStr[1:-1]
        self.parametersList = ParserHelper.parseParametersList(x)
        x = self.portsStr[1:-1]
        self.portsList = ParserHelper.parsePortsList(x)

    def getModuleName(self):
        """Returns the module name.
        """
        return self.moduleNameStr

    def getParametersList(self):
        """Returns the parsed parameters list.
        """
        return self.parametersList

    def getPortsList(self):
        """Returns the parsed ports list.
        """
        return self.portsList

    def getImportList(self):
        """Returns the parsed import package list.
        """
        return self.importList
