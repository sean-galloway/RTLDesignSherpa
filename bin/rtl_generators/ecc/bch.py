import math
from rtl_generators.verilog.module import Module

class BCH(Module):
    module_str = 'bch_codec'
    param_str = 'parameter int DATA_WIDTH=8, parameter int NUM_ERRORS=1'
    port_str = '''
    input  [DATA_WIDTH-1:0]    i_data,
    input                      i_encode,
    input                      i_decode,
    output [DATA_WIDTH-1:0]    ow_encoded_data,
    output [DATA_WIDTH-1:0]    ow_decoded_data,
    output                     ow_error_detected
    '''

    def __init__(self, data_width, num_errors):
        Module.__init__(self, module_name=self.module_str)
        self.data_width = data_width
        self.num_errors = num_errors
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.params.set_param_value('DATA_WIDTH', self.data_width)
        self.params.set_param_value('NUM_ERRORS', self.num_errors)
        self.module_name = f'{self.module_name}_{str(self.data_width).zfill(3)}_{str(self.num_errors)}'
        
        # Initialize gf_exp and gf_log arrays
        self.gf_exp = [0] * (2 ** self.data_width)
        self.gf_log = [0] * (2 ** self.data_width)
        self.init_gf_tables()


    def init_gf_tables(self):
        # Initialize the Galois Field exponentiation and logarithm tables
        self.gf_exp[0] = 1
        for i in range(1, 2 ** self.data_width - 1):
            self.gf_exp[i] = (self.gf_exp[i - 1] << 1) ^ ((self.gf_exp[i - 1] >> (self.data_width - 1)) * 0x11D)
        for i in range(1, 2 ** self.data_width):
            self.gf_log[self.gf_exp[i]] = i


    def gf_multiply(self, poly1, poly2):
        result = [0] * (len(poly1) + len(poly2) - 1)
        for i in range(len(poly1)):
            for j in range(len(poly2)):
                result[i + j] ^= self.gf_exp[(self.gf_log[poly1[i]] + self.gf_log[poly2[j]]) % (2 ** self.data_width - 1)]
        while len(result) > 0 and result[0] == 0:
            result.pop(0)
        return result


    def list_to_binary(self, lst):
        return ''.join(str(x) for x in lst)


    def generate_gf_exp_table(self):
        self.comment('Galois Field exponentiation table')
        # Generate the Galois Field exponentiation table
        gf_exp = [0] * (2 ** self.data_width)
        gf_exp[0] = 1
        for i in range(1, 2 ** self.data_width - 1):
            gf_exp[i] = (gf_exp[i - 1] << 1) ^ ((gf_exp[i - 1] >> (self.data_width - 1)) * 0x11D)
        self.instruction(f'reg [{self.data_width-1}:0] gf_exp[0:{2**self.data_width-1}];')
        for i in range(2 ** self.data_width):
            self.instruction(f'initial gf_exp[{i}] = {self.data_width}\'d{gf_exp[i]};')
        self.instruction('')


    def generate_gf_log_table(self):
        self.comment('Galois Field logarithm table')
        # Generate the Galois Field logarithm table
        gf_log = [0] * (2 ** self.data_width)
        for i in range(1, 2 ** self.data_width):
            gf_log[self.gf_exp[i]] = i
        self.instruction(f'reg [{self.data_width-1}:0] gf_log[0:{2**self.data_width-1}];')
        for i in range(2 ** self.data_width):
            self.instruction(f'initial gf_log[{i}] = {self.data_width}\'d{gf_log[i]};')
        self.instruction('')


    def generate_generator_poly(self):
        self.comment('Generator polynomial for the BCH code')
        # Generate the generator polynomial for the BCH code
        generator_poly = [1]
        for i in range(1, 2 * self.num_errors + 1):
            poly = [1]
            for j in range(i):
                poly = self.gf_multiply(poly, [1, gf_exp[j]])
            generator_poly = self.gf_multiply(generator_poly, poly)
        self.instruction(f'reg [{len(generator_poly)-1}:0] generator_poly;')
        self.instruction(f'initial generator_poly = {len(generator_poly)}\'b{self.list_to_binary(generator_poly)};')
        self.instruction('')


    def generate_encoder(self):
        self.comment('BCH Encoder')
        # Generate Verilog code for the BCH encoder
        self.instruction('reg [DATA_WIDTH-1:0] encoded_data;')
        self.instruction('encoded_data = i_data;')
        self.instruction('for (int i = 0; i < DATA_WIDTH; i++) begin')
        self.instruction('    if (encoded_data[DATA_WIDTH-1] == 1\'b1) begin')
        self.instruction('        encoded_data = encoded_data << 1;')
        self.instruction('        encoded_data = encoded_data ^ generator_poly;')
        self.instruction('    end else begin')
        self.instruction('        encoded_data = encoded_data << 1;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('ow_encoded_data = encoded_data;')
        self.instruction('')


    def generate_decoder(self):
        self.comment('BCH Decoder')
        # Generate Verilog code for the BCH decoder
        self.instruction('reg [DATA_WIDTH-1:0] decoded_data;')
        self.instruction('decoded_data = i_data;')
        self.instruction('reg [NUM_ERRORS*DATA_WIDTH-1:0] syndromes;')
        self.instruction('syndromes = {NUM_ERRORS*DATA_WIDTH{1\'b0}};')
        self.generate_syndrome_calculation()
        self.generate_berlekamp_massey()
        self.generate_chien_search()
        self.instruction('ow_decoded_data = decoded_data;')
        self.instruction('')


    def generate_syndrome_calculation(self):
        self.comment('Syndrome Calculation')
        # Generate Verilog code for syndrome calculation
        for i in range(self.num_errors):
            self.instruction(f'syndromes[{(i+1)*self.data_width-1}:{i*self.data_width}] = gf_exp[gf_log[decoded_data] + {i+1}];')
        self.instruction('')


    def generate_berlekamp_massey(self):
        self.comment('Berlekamp-Massey Algorithm')
        # Generate Verilog code for the Berlekamp-Massey algorithm
        self.instruction('reg [DATA_WIDTH-1:0] lambda[NUM_ERRORS+1];')
        self.instruction('reg [DATA_WIDTH-1:0] discrepancy;')
        self.instruction('reg [DATA_WIDTH-1:0] lambda_prev[NUM_ERRORS+1];')
        self.instruction('reg [DATA_WIDTH-1:0] lambda_temp[NUM_ERRORS+1];')
        self.instruction('reg [DATA_WIDTH-1:0] error_locator[NUM_ERRORS+1];')
        self.instruction('integer i, j, L, N;')
        self.instruction('')
        self.instruction('// Initialize variables')
        self.instruction('L = 0;')
        self.instruction('for (i = 0; i <= NUM_ERRORS; i = i + 1) begin')
        self.instruction('    lambda[i] = (i == 0) ? 1 : 0;')
        self.instruction('    lambda_prev[i] = (i == 0) ? 1 : 0;')
        self.instruction('end')
        self.instruction('')
        self.instruction('// Iterate through syndromes')
        self.instruction('for (N = 0; N < NUM_ERRORS; N = N + 1) begin')
        self.instruction('    // Calculate discrepancy')
        self.instruction('    discrepancy = syndromes[N];')
        self.instruction('    for (i = 1; i <= L; i = i + 1) begin')
        self.instruction('        discrepancy = discrepancy ^ gf_multiply(lambda[i], syndromes[N-i]);')
        self.instruction('    end')
        self.instruction('')
        self.instruction('    // Update lambda if discrepancy is non-zero')
        self.instruction('    if (discrepancy != 0) begin')
        self.instruction('        // Save previous lambda')
        self.instruction('        for (i = 0; i <= NUM_ERRORS; i = i + 1) begin')
        self.instruction('            lambda_temp[i] = lambda[i];')
        self.instruction('        end')
        self.instruction('')
        self.instruction('        // Update lambda')
        self.instruction('        for (i = 0; i <= NUM_ERRORS; i = i + 1) begin')
        self.instruction('            lambda[i] = lambda[i] ^ gf_multiply(discrepancy, lambda_prev[i]);')
        self.instruction('        end')
        self.instruction('')
        self.instruction('        // Update lambda_prev if L < N/2')
        self.instruction('        if (2*L <= N) begin')
        self.instruction('            L = N + 1 - L;')
        self.instruction('            for (i = 0; i <= NUM_ERRORS; i = i + 1) begin')
        self.instruction('                lambda_prev[i] = lambda_temp[i];')
        self.instruction('            end')
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction('// Assign error locator polynomial')
        self.instruction('for (i = 0; i <= NUM_ERRORS; i = i + 1) begin')
        self.instruction('    error_locator[i] = lambda[i];')
        self.instruction('end')
        self.instruction('')


    def generate_chien_search(self):
        self.comment('Chien Search')
        # Generate Verilog code for the Chien search
        self.instruction('reg [DATA_WIDTH-1:0] alpha_powers[2*NUM_ERRORS];')
        self.instruction('reg [DATA_WIDTH-1:0] error_eval;')
        self.instruction('reg [DATA_WIDTH-1:0] error_locations[NUM_ERRORS];')
        self.instruction('integer num_errors_found;')
        self.instruction('integer i, j;')
        self.instruction('')
        self.instruction('// Initialize alpha powers')
        self.instruction('for (i = 0; i < 2*NUM_ERRORS; i = i + 1) begin')
        self.instruction('    alpha_powers[i] = gf_exp[i+1];')
        self.instruction('end')
        self.instruction('')
        self.instruction('// Chien search')
        self.instruction('num_errors_found = 0;')
        self.instruction('for (i = 0; i < DATA_WIDTH; i = i + 1) begin')
        self.instruction('    error_eval = 1;')
        self.instruction('    for (j = 0; j <= NUM_ERRORS; j = j + 1) begin')
        self.instruction('        error_eval = error_eval ^ gf_multiply(error_locator[j], alpha_powers[j]);')
        self.instruction('    end')
        self.instruction('    if (error_eval == 0) begin')
        self.instruction('        error_locations[num_errors_found] = DATA_WIDTH - 1 - i;')
        self.instruction('        num_errors_found = num_errors_found + 1;')
        self.instruction('        if (num_errors_found == NUM_ERRORS) begin')
        self.instruction('            break;')
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('    for (j = 0; j < 2*NUM_ERRORS; j = j + 1) begin')
        self.instruction('        alpha_powers[j] = gf_multiply(alpha_powers[j], gf_exp[j+1]);')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction('// Correct errors')
        self.instruction('if (num_errors_found > 0) begin')
        self.instruction('    for (i = 0; i < num_errors_found; i = i + 1) begin')
        self.instruction('        decoded_data[error_locations[i]] = decoded_data[error_locations[i]] ^ 1;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction('// Set error detection flag')
        self.instruction('ow_error_detected = (num_errors_found > 0) ? 1 : 0;')
        self.instruction('')


    def verilog(self, file_path):  # sourcery skip: extract-duplicate-method
        self.start()

        self.generate_gf_exp_table()
        self.generate_gf_log_table()
        self.generate_generator_poly()

        self.instruction('always_comb begin')
        self.instruction('    if (i_encode) begin')
        self.generate_encoder()
        self.instruction('    end')
        self.instruction('    else if (i_decode) begin')
        self.generate_decoder()
        self.instruction('    end')
        self.instruction('    else begin')
        self.instruction('        ow_encoded_data = {DATA_WIDTH{1\'b0}};')
        self.instruction('        ow_decoded_data = {DATA_WIDTH{1\'b0}};')
        self.instruction('        ow_error_detected = 1\'b0;')
        self.instruction('    end')
        self.instruction('end')

        self.end()

        self.write(file_path, f'{self.module_name}.sv')


class BCH_enc(BCH):
    module_str = 'bch_encoder'
    param_str = 'parameter int DATA_WIDTH=8, parameter int NUM_ERRORS=1'
    port_str = '''
    input  [DATA_WIDTH-1:0]    i_data,
    output [DATA_WIDTH-1:0]    ow_encoded_data
    '''


    def __init__(self, data_width, num_errors):
        super().__init__(data_width, num_errors)
        self.module_name = f'bch_encoder_{str(self.data_width).zfill(3)}_{str(self.num_errors)}'
        self.ports.clear()
        self.ports.add_port_string(self.port_str)


    def verilog(self, file_path):
        self.start()

        self.generate_gf_exp_table()
        self.generate_generator_poly()

        self.instruction('always_comb begin')
        self.generate_encoder()
        self.instruction('end')

        self.end()

        self.write(file_path, f'{self.module_name}.sv')


class BCH_dec(BCH):
    module_str = 'bch_decoder'
    param_str = 'parameter int DATA_WIDTH=8, parameter int NUM_ERRORS=1'
    port_str = '''
    input  [DATA_WIDTH-1:0]    i_data,
    output [DATA_WIDTH-1:0]    ow_decoded_data,
    output                     ow_error_detected
    '''


    def __init__(self, data_width, num_errors):
        super().__init__(data_width, num_errors)
        self.module_name = f'bch_decoder_{str(self.data_width).zfill(3)}_{str(self.num_errors)}'
        self.ports.clear()
        self.ports.add_port_string(self.port_str)


    def verilog(self, file_path):
        self.start()

        self.generate_gf_exp_table()
        self.generate_gf_log_table()

        self.instruction('always_comb begin')
        self.generate_decoder()
        self.instruction('end')

        self.end()

        self.write(file_path, f'{self.module_name}.sv')


'''
To determine the number of ECC bits required for a given data bus width and the desired number of correctable errors (1, 2, or 3 bit repair) in a BCH code, you can use the following formulas:

For 1-bit error correction:
    Number of ECC bits = m
    Where m is the smallest positive integer that satisfies: 2^m >= n + 1
    n is the total number of bits (data bits + ECC bits)
For 2-bit error correction:
    Number of ECC bits = m
    Where m is the smallest positive integer that satisfies: 2^m >= n + 1
    n is the total number of bits (data bits + ECC bits)
For 3-bit error correction:
    Number of ECC bits = m
    Where m is the smallest positive integer that satisfies: 2^m >= n + 1
    n is the total number of bits (data bits + ECC bits)

| Data Width | 1-bit Correction | 2-bit Correction | 3-bit Correction |
|------------|------------------|------------------|------------------|
| 8          | 4                | 4                | 5                |
| 16         | 5                | 5                | 6                |
| 24         | 5                | 5                | 6                |
| 32         | 6                | 6                | 7                |
| 40         | 6                | 6                | 7                |
| 48         | 6                | 6                | 7                |
| 56         | 6                | 6                | 7                |
| 64         | 7                | 7                | 8                |
| 72         | 7                | 7                | 8                |
| 80         | 7                | 7                | 8                |
| 88         | 7                | 7                | 8                |
| 96         | 7                | 7                | 8                |
| 104        | 7                | 7                | 8                |
| 112        | 7                | 7                | 8                |
| 120        | 7                | 7                | 8                |
| 128        | 8                | 8                | 9                |
| 136        | 8                | 8                | 9                |
| 144        | 8                | 8                | 9                |
| 152        | 8                | 8                | 9                |
| 160        | 8                | 8                | 9                |
| 168        | 8                | 8                | 9                |
| 176        | 8                | 8                | 9                |
| 184        | 8                | 8                | 9                |
| 192        | 8                | 8                | 9                |
| 200        | 8                | 8                | 9                |
| 208        | 8                | 8                | 9                |
| 216        | 8                | 8                | 9                |
| 224        | 8                | 8                | 9                |
| 232        | 8                | 8                | 9                |
| 240        | 8                | 8                | 9                |
| 248        | 8                | 8                | 9                |
| 256        | 9                | 9                | 10               |

'''