#@PydevCodeAnalysisIgnore


tstParam01 = """
    parameter add_extra_instr  = 1,  //use extra instructions 
    parameter string add_select_instr = "M144k, auto",  //use select instructions
    parameter shorten_pipeline = 3  //shorte pipeline
"""
param_add_param_string_01_gold = """[   ParameterRecord(sig_type='',
                    name='add_extra_instr',
                    value='1',
                    packed='',
                    unpacked='',
                    compilerDirectiveSig='',
                    compilerDirective=''),
    ParameterRecord(sig_type='string',
                    name='add_select_instr',
                    value='"M144k,auto"',
                    packed='',
                    unpacked='',
                    compilerDirectiveSig='',
                    compilerDirective=''),
    ParameterRecord(sig_type='',
                    name='shorten_pipeline',
                    value='3 ',
                    packed='',
                    unpacked='',
                    compilerDirectiveSig='',
                    compilerDirective='')]
"""
param_create_param_string_01_gold = """parameter         add_extra_instr = 1,
parameter string  add_select_instr = "M144k,auto",
parameter         shorten_pipeline = 3 
"""

tstSignal01 = """
    input         clk, enable, is_signed,
    input         enacc, sub_nadd, selacc, resetrs0,
    input [31:0]  rs0, rs1, imm,
    input         mulmux, selop0, selop1,
    input [1:0] [(shorten_pipeline-1)*4:0]  selshift[(add_extra_instr-1):0],
    input [1:0]   cmode,
    input [2:0]   opcode1, opcode2,
    output        out_en,
    output [31:0] out
"""

signal_create_port_string_01_gold = """input  logic                                 clk,
input  logic                                 enable,
input  logic                                 is_signed,
input  logic                                 enacc,
input  logic                                 sub_nadd,
input  logic                                 selacc,
input  logic                                 resetrs0,
input  logic [31:0]                          rs0,
input  logic [31:0]                          rs1,
input  logic [31:0]                          imm,
input  logic                                 mulmux,
input  logic                                 selop0,
input  logic                                 selop1,
input  logic [1:0][(shorten_pipeline-1)*4:0] selshift  [(add_extra_instr-1):0],
input  logic [1:0]                           cmode,
input  logic [2:0]                           opcode1,
input  logic [2:0]                           opcode2,
output logic                                 out_en,
output logic [31:0]                          out
"""

signal_create_wire_string_01_gold = """logic                                 clk;
logic                                 enable;
logic                                 is_signed;
logic                                 enacc;
logic                                 sub_nadd;
logic                                 selacc;
logic                                 resetrs0;
logic [31:0]                          rs0;
logic [31:0]                          rs1;
logic [31:0]                          imm;
logic                                 mulmux;
logic                                 selop0;
logic                                 selop1;
logic [1:0][(shorten_pipeline-1)*4:0] selshift  [(add_extra_instr-1):0];
logic [1:0]                           cmode;
logic [2:0]                           opcode1;
logic [2:0]                           opcode2;
logic                                 out_en;
logic [31:0]                          out;
"""

signal_add_port_string_01_gold = """[   SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='clk',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='enable',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='is_signed',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='enacc',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='sub_nadd',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selacc',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='resetrs0',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='rs0',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='rs1',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='imm',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='mulmux',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selop0',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selop1',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selshift',
                 packed='[1:0][(shorten_pipeline-1)*4:0]',
                 unpacked='[(add_extra_instr-1):0]',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='cmode',
                 packed='[1:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='opcode1',
                 packed='[2:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='opcode2',
                 packed='[2:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='output',
                 name='out_en',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='output',
                 name='out',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0)]
"""


tstSimpleModuleName = 'simple'
tstSimpleModule = """
module simple
#(parameter add_extra_instr  = 1,  //use extra instructions (rotl, ...)
  parameter string add_select_instr = "M144k, auto",  //use select instructions
  parameter shorten_pipeline = 3)  //remove two cycles latency

 (input         clk, enable, is_signed,
  input         enacc, sub_nadd, selacc, resetrs0,
  input [31:0]  rs0, rs1, imm,
  input         mulmux, selop0, selop1,
  input [1:0] [(shorten_pipeline-1)*4:0]  selshift[(add_extra_instr-1):0],
  input [1:0]   cmode,
  input [2:0]   opcode1, opcode2,
  output        out_en,
  output [31:0] out);
    """

tstSimpleModuleInstStr = """
// *******************
// simple:smpl::
// *******************
simple
   #(
      .add_extra_instr  (1),
      .add_select_instr ("M144k,auto"),
      .shorten_pipeline (3)
   )
   i_simple_smpl
   (
      .clk       (clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (imm),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""
tstSimpleModuleInstStrSkipParams = """
// *******************
// simple:smpl::
// *******************
simple i_simple_smpl
   (
      .clk       (clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (imm),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""
tstSimpleModuleInstStrSignalOverride2 = """
// *******************
// simple:smpl::clk=h_clk,imm=s_imm[63:32],
// *******************
simple
   #(
      .add_extra_instr  (1),
      .add_select_instr ("M144k,auto"),
      .shorten_pipeline (3)
   )
   i_simple_smpl
   (
      .clk       (h_clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (s_imm[63:32]),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""

tstSimpleModuleInstStrSignalOverride = """
// *******************
// simple:smpl::.clk(h_clk),.imm(s_imm[63:32])
// *******************
simple
   #(
      .add_extra_instr  (1),
      .add_select_instr ("M144k,auto"),
      .shorten_pipeline (3)
   )
   i_simple_smpl
   (
      .clk       (h_clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (s_imm[63:32]),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""

tstSimpleFileMapping = """
// *******************
// gen_pmparkvalue:park::
// *******************
gen_pmparkvalue i_gen_pmparkvalue_park
   (
      .gpmclk          (gpmclk),
      .pmrst_b         (pmrst_b),
      .pm_active       (pm_active),
      .pm_asc          (pm_asc),
      .pm_state        (pm_state),
      .scr_pm_rollpark (scr_pm_rollpark),
      .pmsignal        (pm_park)
   );
"""

tstSimpleModuleInstStrSignalOverride3 = """
// *******************
// simple:smpl::.clk(m_clk),.imm(s_imm[63:32])
// *******************
simple
   #(
      .add_extra_instr  (1),
      .add_select_instr ("M144k,auto"),
      .shorten_pipeline (3)
   )
   i_simple_smpl
   (
      .clk       (m_clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (s_imm[63:32]),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""

tstSimpleModuleInstStrParamOverride2 = """
// *******************
// simple:smpl:add_extra_instr=3'b001,.shorten_pipeline(0),:
// *******************
simple
   #(
      .add_extra_instr  (3'b001),
      .add_select_instr ("M144k,auto"),
      .shorten_pipeline (0)
   )
   i_simple_smpl
   (
      .clk       (clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (imm),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""

tstSimpleModuleInstStrParamOverride1 = """
// *******************
// simple:smpl:.add_extra_instr(3'b001),.shorten_pipeline(0),:
// *******************
simple
   #(
      .add_extra_instr  (3'b001),
      .add_select_instr ("M144k,auto"),
      .shorten_pipeline (0)
   )
   i_simple_smpl
   (
      .clk       (clk),
      .enable    (enable),
      .is_signed (is_signed),
      .enacc     (enacc),
      .sub_nadd  (sub_nadd),
      .selacc    (selacc),
      .resetrs0  (resetrs0),
      .rs0       (rs0),
      .rs1       (rs1),
      .imm       (imm),
      .mulmux    (mulmux),
      .selop0    (selop0),
      .selop1    (selop1),
      .selshift  (selshift),
      .cmode     (cmode),
      .opcode1   (opcode1),
      .opcode2   (opcode2),
      .out_en    (out_en),
      .out       (out)
   );
"""

tstGenCtrl = {'name': 'gen_cgctrl',
 'parameters': [{'compilerDirective': '',
                 'compilerDirectiveSig': '',
                 'name': 'CLKGATE_MAXCNT',
                 'packed': '',
                 'type': '',
                 'unpacked': '',
                 'value': '6'}],
 'ports': [{'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'input',
            'drivers': 0,
            'interface': False,
            'name': 'clk',
            'packed': '',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'input',
            'drivers': 0,
            'interface': False,
            'name': 'rst_b',
            'packed': '',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'input',
            'drivers': 0,
            'interface': False,
            'name': 'cmd_f',
            'packed': '',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'input',
            'drivers': 0,
            'interface': False,
            'name': 'scr_clkgate_maxcntr',
            'packed': '[CLKGATE_MAXCNT-1:0]',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'output',
            'drivers': 0,
            'interface': False,
            'name': 'cg_wrptren',
            'packed': '',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'output',
            'drivers': 0,
            'interface': False,
            'name': 'cgfsm_clken',
            'packed': '',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'output',
            'drivers': 0,
            'interface': False,
            'name': 'cgwaitcnt_nxt',
            'packed': '[CLKGATE_MAXCNT-1:0]',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''},
           {'compilerDirective': '',
            'compilerDirectiveSig': '',
            'direction': 'output',
            'drivers': 0,
            'interface': False,
            'name': 'cgfsm_ps_visa',
            'packed': '[1:0]',
            'receivers': 0,
            'type': 'logic',
            'unpacked': ''}]}
tstSimpleParams = [{'compilerDirective': '',
                    'compilerDirectiveSig': '',
                    'name': 'add_extra_instr',
                    'packed': '',
                    'type': '',
                    'unpacked': '',
                    'value': '1'},
                   {'compilerDirective': '',
                    'compilerDirectiveSig': '',
                    'name': 'add_select_instr',
                    'packed': '',
                    'type': 'string',
                    'unpacked': '',
                    'value': '"M144k,auto"'},
                   {'compilerDirective': '',
                    'compilerDirectiveSig': '',
                    'name': 'shorten_pipeline',
                    'packed': '',
                    'type': '',
                    'unpacked': '',
                    'value': '3'}]

tstSimplePorts = [
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'clk',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'enable',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'is_signed',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'enacc',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'sub_nadd',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'selacc',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'resetrs0',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'rs0',
  'packed': '[31:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'rs1',
  'packed': '[31:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'imm',
  'packed': '[31:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'mulmux',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'selop0',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'selop1',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'selshift',
  'packed': '[1:0][(shorten_pipeline-1)*4:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': '[(add_extra_instr-1):0]'},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'cmode',
  'packed': '[1:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'opcode1',
  'packed': '[2:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'opcode2',
  'packed': '[2:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'output',
  'drivers': 0,
  'interface': False,
  'name': 'out_en',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'output',
  'drivers': 0,
  'interface': False,
  'name': 'out',
  'packed': '[31:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''}]
tstCompilerDirectiveModuleName = 'mymod'
tstCompilerDirectiveModule = """
/* multi line
`ifdef COMMENTED OUT
`endif
*/
module mymod
#
(
   /* Multi line
    * comments
`ifdef COMMENT
`endif
    */
   parameter GEN1= 48,
   parameter GEN2 = 45,
   parameter GEN3_WIDTH   = $clog2(VALUE),
`ifdef MYDEF1
   parameter GEN4 = 6,
`else
   parameter GEN4 = 5,
`endif

   // COMMENTS
   // comment
   parameter [31:0] DEFAULT_VAL_A = 32'b0,
 `ifndef MYDEF2
   parameter int [31:0] DEFAULT_VAL_B = 32'b0,
`else
   parameter int [31:0] DEFAULT_VAL_B = 32'b1,
    `ifdef MYDEF3
       parameter int [31:0] DEFAULT_VAL_D = 32'b1,
    `endif
`endif

   parameter [31:0] DEFAULT_VAL_C [1:0]
)(
   // yet another comment
   input logic          reset_n,
`ifdef MYDEF2
   input logic          clock,
`else
   input logic [1:0]    clock,
`endif

   input logic [$clog2(GEN3_WIDTH+1)-1:0]    test,
   /** test **/
   //yet another comment
   input pkg::typedef   clock2,
   /*
    test 1
   */
   // Rx ports
`ifndef MYDEF3
   myinterface.master     m_master,
   myinterface.slave      s_slave,
`else
   myinterface.master     m_masterB,
   myinterface.slave      s_slaveB,
    `ifndef MYDEF                        // not really legal comment...
        input  logic        my_signal,   // junk comment
    `endif
`endif
   output logic [28:0]  [$clog2(GEN1):0]m_big_array[1:0] [2:0],

   /*
     test 2
   */
   output logic [15:0]  m_simple_array,

   /* test 3
    */
   output logic [15:0]  m_simple_array3
);
"""

tstCompilerDirectiveModuleStr = """
// *******************
// mymod:smpl_cd::
// *******************
mymod
   #(
      .GEN1          (48),
      .GEN2          (45),
      .GEN3_WIDTH    ($clog2 (VALUE)),
`ifdef MYDEF1
      .GEN4          (6),
`else
      .GEN4          (5),
`endif
      .DEFAULT_VAL_A (32'b0),
`ifndef MYDEF2
      .DEFAULT_VAL_B (32'b0),
`else
      .DEFAULT_VAL_B (32'b1),
   `ifdef MYDEF3
      .DEFAULT_VAL_D (32'b1),
   `endif
`endif
      .DEFAULT_VAL_C ()
   )
   i_mymod_smpl_cd
   (
      .reset_n         (reset_n),
`ifdef MYDEF2
      .clock           (clock),
`else
      .clock           (clock),
`endif
      .test            (test),
      .clock2          (clock2),
`ifndef MYDEF3
      .m_master        (m_master),
      .s_slave         (s_slave),
`else
      .m_masterB       (m_masterB),
      .s_slaveB        (s_slaveB),
   `ifndef MYDEF
      .my_signal       (my_signal),
   `endif
`endif
      .m_big_array     (m_big_array),
      .m_simple_array  (m_simple_array),
      .m_simple_array3 (m_simple_array3)
   );
"""

tstCompilerDirectiveParams = [
              {'compilerDirective': '',
               'compilerDirectiveSig': '',
               'name': 'GEN1',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': '48'},
              {'compilerDirective': '',
               'compilerDirectiveSig': '',
               'name': 'GEN2',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': '45'},
              {'compilerDirective': '',
               'compilerDirectiveSig': '',
               'name': 'GEN3_WIDTH',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': '$clog2(VALUE)'},
              {'compilerDirective': 'ifdef MYDEF1',
               'compilerDirectiveSig': 'ifdef MYDEF1',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': 'ifdef MYDEF1',
               'name': 'GEN4',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': '6'},
              {'compilerDirective': 'else',
               'compilerDirectiveSig': 'ifdef MYDEF1,else',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': 'ifdef MYDEF1,else',
               'name': 'GEN4',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': '5'},
              {'compilerDirective': 'endif',
               'compilerDirectiveSig': '',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': '',
               'name': 'DEFAULT_VAL_A',
               'packed': '[31:0]',
               'type': '',
               'unpacked': '',
               'value': "32'b0"},
              {'compilerDirective': 'ifndef MYDEF2',
               'compilerDirectiveSig': 'ifndef MYDEF2',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': 'ifndef MYDEF2',
               'name': 'DEFAULT_VAL_B',
               'packed': '[31:0]',
               'type': 'int',
               'unpacked': '',
               'value': "32'b0"},
              {'compilerDirective': 'else',
               'compilerDirectiveSig': 'ifndef MYDEF2,else',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': 'ifndef MYDEF2,else',
               'name': 'DEFAULT_VAL_B',
               'packed': '[31:0]',
               'type': 'int',
               'unpacked': '',
               'value': "32'b1"},
              {'compilerDirective': 'ifdef MYDEF3',
               'compilerDirectiveSig': 'ifndef MYDEF2,else,ifdef MYDEF3',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': 'ifndef MYDEF2,else,ifdef MYDEF3',
               'name': 'DEFAULT_VAL_D',
               'packed': '[31:0]',
               'type': 'int',
               'unpacked': '',
               'value': "32'b1"},
              {'compilerDirective': 'endif',
               'compilerDirectiveSig': 'ifndef MYDEF2,else',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': 'endif',
               'compilerDirectiveSig': '',
               'name': '',
               'packed': '',
               'type': '',
               'unpacked': '',
               'value': ''},
              {'compilerDirective': '',
               'compilerDirectiveSig': '',
               'name': 'DEFAULT_VAL_C',
               'packed': '[31:0]',
               'type': '',
               'unpacked': '[1:0]',
               'value': ''}]

tstCompilerDirectivePorts = [{'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'reset_n',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': 'ifdef MYDEF2',
  'compilerDirectiveSig': 'ifdef MYDEF2',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifdef MYDEF2',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'clock',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': 'else',
  'compilerDirectiveSig': 'ifdef MYDEF2,else',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifdef MYDEF2,else',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'clock',
  'packed': '[1:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': 'endif',
  'compilerDirectiveSig': '',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'test',
  'packed': '[$clog2(GEN3_WIDTH+1)-1:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'clock2',
  'packed': '',
  'receivers': 0,
  'type': 'pkg::typedef',
  'unpacked': ''},
 {'compilerDirective': 'ifndef MYDEF3',
  'compilerDirectiveSig': 'ifndef MYDEF3',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifndef MYDEF3',
  'direction': 'master',
  'drivers': 0,
  'interface': True,
  'name': 'm_master',
  'packed': '',
  'receivers': 0,
  'type': 'myinterface',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifndef MYDEF3',
  'direction': 'slave',
  'drivers': 0,
  'interface': True,
  'name': 's_slave',
  'packed': '',
  'receivers': 0,
  'type': 'myinterface',
  'unpacked': ''},
 {'compilerDirective': 'else',
  'compilerDirectiveSig': 'ifndef MYDEF3,else',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifndef MYDEF3,else',
  'direction': 'master',
  'drivers': 0,
  'interface': True,
  'name': 'm_masterB',
  'packed': '',
  'receivers': 0,
  'type': 'myinterface',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifndef MYDEF3,else',
  'direction': 'slave',
  'drivers': 0,
  'interface': True,
  'name': 's_slaveB',
  'packed': '',
  'receivers': 0,
  'type': 'myinterface',
  'unpacked': ''},
 {'compilerDirective': 'ifndef MYDEF',
  'compilerDirectiveSig': 'ifndef MYDEF3,else,ifndef MYDEF',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': 'ifndef MYDEF3,else,ifndef MYDEF',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'my_signal',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': 'endif',
  'compilerDirectiveSig': 'ifndef MYDEF3,else',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': 'endif',
  'compilerDirectiveSig': '',
  'direction': '',
  'drivers': 0,
  'interface': '',
  'name': '',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'output',
  'drivers': 0,
  'interface': False,
  'name': 'm_big_array',
  'packed': '[28:0][$clog2(GEN1):0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': '[1:0][2:0]'},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'output',
  'drivers': 0,
  'interface': False,
  'name': 'm_simple_array',
  'packed': '[15:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'output',
  'drivers': 0,
  'interface': False,
  'name': 'm_simple_array3',
  'packed': '[15:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''}]




tstBadCompilerDirectiveModule = """
`include memip
`include ctech_macros

/* multi line
`ifdef COMMENTED OUT
`endif
*/
module mymod
#
(
   /* Multi line
    * comments
`ifdef COMMENT
`endif
`ifwdef BAD_DIRECTIVE_COMMENTED_OUT
`endif
    */
   parameter GEN1= 48,
`ifwdef BAD_DIRECTIVE
   parameter GEN2 = 45,
`endif
   parameter GEN3_WIDTH   = $clog2(VALUE),
`ifdef MYDEF1
   parameter GEN4 = 6,
`else
   parameter GEN4 = 5,
`endif

   // COMMENTS
   // comment
   parameter [31:0] DEFAULT_VAL_A = 32'b0,
 `ifndef MYDEF2
   parameter int [31:0] DEFAULT_VAL_B = 32'b0,
`else
   parameter int [31:0] DEFAULT_VAL_B = 32'b1,
    `ifdef MYDEF3
       parameter int [31:0] DEFAULT_VAL_D = 32'b1,
    `endif
`endif

   parameter [31:0] DEFAULT_VAL_C [1:0]
)(
   // yet another comment
   input logic          reset_n,
`ifdef MYDEF2
   input logic          clock,
`else
   input logic [1:0]    clock,
`endif

   input logic [$clog2(GEN3_WIDTH+1)-1:0]    test,
   /** test **/
   //yet another comment
   input pkg::typedef   clock2,
   /*
    test 1
   */
   // Rx ports
`ifndef MYDEF3
   myinterface.master     m_master,
   myinterface.slave      s_slave,
`else
   myinterface.master     m_masterB,
   myinterface.slave      s_slaveB,
    `ifndef MYDEF                        // not really legal comment...
        input  logic        my_signal,   // junk comment
    `endif
`endif
   output logic [28:0]  [$clog2(GEN1):0]m_big_array[1:0] [2:0],

   /*
     test 2
   */
   output logic [15:0]  m_simple_array,

   /* test 3
    */
   output logic [15:0]  m_simple_array3
);
"""

tstSimpleFileParameters = []

tstSimpleFilePorts = [
{'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'gpmclk',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'pmrst_b',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'pm_active',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'pm_asc',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'pm_state',
  'packed': '[4:0]',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'drivers': 0,
  'interface': False,
  'name': 'scr_pm_rollpark',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'output',
  'drivers': 0,
  'interface': False,
  'name': 'pmsignal',
  'packed': '',
  'receivers': 0,
  'type': 'logic',
  'unpacked': ''}]

tstSignalMapRulesDict = [
                              {'instance': 'gen_pm.*',
                               'instanceName': '.*',
                               'name': 'pmsignal',
                               'parentName': '.*',
                               'pattern': 'pmsignal',
                               'replace': '"pm_"+instName'},
                              {'instance': 'gen_pm.*',
                               'instanceName': '.*',
                               'name': 'pmstagger',
                               'parentName': '.*',
                               'pattern': 'pmstagger',
                               'replace': '"pm_"+instName'},
                              {'instance': 'gen_pm.*',
                               'instanceName': '.*',
                               'name': 'clkack',
                               'parentName': '.*',
                               'pattern': '.*',
                               'replace': 'instName'},
                              {'instance': 'gen_pm.*',
                               'instanceName': '.*',
                               'name': 'scr_.*',
                               'parentName': '.*',
                               'pattern': 'pmsig',
                               'replace': 'instName'}]

tstSignalMapRulesDict2 = [
                            {'instance': 'gen_pm.*',
                             'instanceName': '.*',
                             'name': 'pmsignal',
                             'parentName': '.*',
                             'pattern': 'pmsignal',
                             'replace': '"pm_"+instName'},
                            {'instance': 'gen_pm.*',
                             'instanceName': '.*',
                             'name': 'pmstagger',
                             'parentName': '.*',
                             'pattern': 'pmstagger',
                             'replace': '"pm_"+instName+"staggering"'},
                            {'instance': 'gen_pm.*',
                             'instanceName': '.*',
                             'name': 'clkack',
                             'parentName': '.*',
                             'pattern': '.*',
                             'replace': 'instName'},
                            {'instance': 'gen_pm.*',
                             'instanceName': '.*',
                             'name': 'scr_.*',
                             'parentName': '.*',
                             'pattern': 'pmsig',
                             'replace': 'instName'}]

tstBuilderRootModules = [
 {'keepLocal': 'gpmclk,pm_active,pm_asc,pm_dsc,pm_count,pm_hdcount,pmrst_b,pm_idle,pm_start_count,pm_state,pm_spid_pm_ack, mia_rst_b_pre,mptu_0p125clk_div_unbuf,mptu_0p25clk_div_unbuf,mptu_0p25clk_unbuf,mptu_0p5clk_div_unbuf,mptu_0p5clk_unbuf,mptu_1p0clk_clkenable,mptu_rst_scan_b,',
  'modName': 'dfi_pmu',
  'modParams': ''},
 {'keepLocal': 'mptu_0p125clk_div_unbuf,mptu_0p25clk_div_unbuf,mptu_0p25clk_unbuf,mptu_0p5clk_div_unbuf,mptu_0p5clk_unbuf,mptu_1p0clk_clkenable,mptu_rst_scan_b',
  'modName': 'dfi_pmu_clockgen',
  'modParams': 'CLKGATE_MAXCNT=6'},
 {'keepLocal': '', 'modName': 'dfi_pmu_intr', 'modParams': ''},
 {'keepLocal': 'pm_mptu_clkenable,pm_mia_clkenable,pm_iosfsb_clkenable,cfg_addr,agt_rdata_in,agt_resp_in,agt_rdcmd_get,agt_wrcmd_get,agt_wrdat_get,agt_idle,agt_addr,agt_be,agt_beb,agt_cmgq_get,agt_rd_en,agt_wr_en,agt_rd_en_q,agt_wr_en_q,agt_wdata_out,agt_regif_valid,agt_regif_opcode,scr_stpreq_prepm0_cnt,scr_dfi_rst_b_assert_state,, scr_pmst_pm0_dsc_cnt,scr_pmst_pm1_asc_cnt,scr_pmst_pm1_dsc_cnt,scr_pmst_pm2_asc_cnt,scr_pmst_pm2_dsc_cnt,scr_pmst_pm3_asc_cnt,scr_pmst_pm3_dsc_cnt,scr_pmst_pm4_asc_cnt,scr_pmst_pm4_dsc_cnt,scr_pmst_pm5_asc_cnt,scr_pmst_prepm0_dsc_cnt,agt_wdata_out,dcr_irq,dcr_irq24,dcr_irq25,dcr_irq26,dcr_irq27,dcr_irq28,dcr_irq29,dcr_irq30,dcr_irq31,scr_dfi_rst_b_assert_cnt,scr_dfi_rst_b_deassert_cnt,scr_dfi_rst_b_prepm0_cnt,scr_dficlk_clkreq_assert_cnt,scr_dficlk_clkreq_deassert_cnt,scr_dficlk_clkreq_prepm0_cnt,scr_hclk_clkreq_assert_cnt,scr_hclk_clkreq_deassert_cnt,scr_hclk_clkreq_prepm0_cnt,scr_hclk_rst_b_assert_cnt,scr_hclk_rst_b_deassert_cnt,scr_hclk_rst_b_prepm0_cnt,scr_hpet_rst_b_assert_cnt,scr_hpet_rst_b_deassert_cnt,scr_hpet_rst_b_prepm0_cnt,scr_hpetclk_clkreq_assert_cnt,scr_hpetclk_clkreq_deassert_cnt,scr_hpetclk_clkreq_prepm0_cnt,scr_iosfsb_clkenable_assert_cnt,scr_iosfsb_clkenable_deassert_cnt,scr_iosfsb_clkenable_prepm0_cnt,scr_iosfsb_rst_b_assert_cnt,scr_iosfsb_rst_b_deassert_cnt,scr_iosfsb_rst_b_prepm0_cnt,scr_mia_clkenable_assert_cnt,scr_mia_clkenable_deassert_cnt,scr_mia_clkenable_prepm0_cnt,scr_mia_rst_b_assert_cnt,scr_mia_rst_b_deassert_cnt,scr_mia_rst_b_prepm0_cnt,scr_mptu_clkenable_assert_cnt,scr_mptu_clkenable_deassert_cnt,scr_mptu_clkenable_prepm0_cnt,scr_mptu_rst_b_assert_cnt,scr_mptu_rst_b_deassert_cnt,scr_mptu_rst_b_prepm0_cnt,scr_pm_hvm_delay,scr_rtcclk_clkreq_assert_cnt,scr_rtcclk_clkreq_deassert_cnt,scr_rtcclk_clkreq_prepm0_cnt,scr_stpreq_assert_cnt,scr_stpreq_deassert_cnt,scr_stpreq_prepm0_cntscr_dfi_rst_b_assert_state,scr_dfi_rst_b_deassert_state,scr_dficlk_clkreq_assert_state,scr_dficlk_clkreq_deassert_state,scr_hclk_clkreq_assert_state,scr_hclk_clkreq_deassert_state,scr_hclk_rst_b_assert_state,scr_hclk_rst_b_deassert_state,, scr_hpet_rst_b_assert_state,scr_hpet_rst_b_deassert_state,scr_hpetclk_clkreq_assert_state,scr_hpetclk_clkreq_deassert_state,scr_hvm_pmmsg,scr_iosfsb_clkenable_assert_state,scr_iosfsb_clkenable_deassert_state,scr_iosfsb_rst_b_assert_state,scr_iosfsb_rst_b_deassert_state,scr_mia_clkenable_assert_state,scr_mia_clkenable_deassert_state,scr_mia_rst_b_assert_state,scr_mia_rst_b_deassert_state,scr_mptu_clkenable_assert_state,scr_mptu_clkenable_deassert_state,scr_mptu_rst_b_assert_state,scr_mptu_rst_b_deassert_state,scr_pm_sw_msg,scr_rtcclk_clkreq_assert_state,scr_rtcclk_clkreq_deassert_state,scr_stpreq_assert_state,scr_stpreq_deassert_state,pm_cfg_status,scr_ahb_cgmaxcntr,dcr_ahb_dyncgdis,dcr_pm_clkgateen,dcr_pm_hvm_req,dcr_pm_pmrst_b,dcr_pm_sw_req,o_regif_read_miss,o_regif_read_valid,o_regif_write_valid,pm_hvm_req_clear,pm_pmclk_clkreq,pm_sw_ack,pm_sw_req_clear,scr_dfi_rst_b_assert_ascxdscb,scr_dfi_rst_b_deassert_ascxdscb,scr_dfi_rst_b_override_en,scr_dfi_rst_b_override_value,scr_dficlk_clkreq_assert_ascxdscb,scr_dficlk_clkreq_deassert_ascxdscb,scr_dficlk_clkreq_override_en,scr_dficlk_clkreq_override_value,scr_hclk_clkreq_assert_ascxdscb,scr_hclk_clkreq_deassert_ascxdscb,scr_hclk_clkreq_override_en,scr_hclk_clkreq_override_value,scr_hclk_rst_b_assert_ascxdscb,scr_hclk_rst_b_deassert_ascxdscb,scr_hclk_rst_b_override_en,scr_hclk_rst_b_override_value,scr_hpet_rst_b_assert_ascxdscb,scr_hpet_rst_b_deassert_ascxdscb,scr_hpet_rst_b_override_en,scr_hpet_rst_b_override_value,scr_hpetclk_clkreq_assert_ascxdscb,scr_hpetclk_clkreq_deassert_ascxdscb,, scr_hpetclk_clkreq_override_en,scr_hpetclk_clkreq_override_value,scr_iosfsb_clkenable_assert_ascxdscb,scr_iosfsb_clkenable_deassert_ascxdscb,scr_iosfsb_clkenable_override_en,scr_iosfsb_clkenable_override_value,scr_iosfsb_rst_b_assert_ascxdscb,scr_iosfsb_rst_b_deassert_ascxdscb,scr_iosfsb_rst_b_override_en,scr_iosfsb_rst_b_override_value,scr_mia_clkenable_assert_ascxdscb,scr_mia_clkenable_deassert_ascxdscb,scr_mia_clkenable_override_en,scr_mia_clkenable_override_value,scr_mia_rst_b,scr_mia_rst_b_assert_ascxdscb,scr_mia_rst_b_deassert_ascxdscb,scr_mia_rst_b_override_en,scr_mia_rst_b_override_value,scr_mptu_clkenable_assert_ascxdscb,scr_mptu_clkenable_deassert_ascxdscb,scr_mptu_clkenable_override_en,scr_mptu_clkenable_override_value,scr_mptu_rst_b_assert_ascxdscb,scr_mptu_rst_b_deassert_ascxdscb,scr_mptu_rst_b_override_en,scr_mptu_rst_b_override_value,scr_pmclk_clkreq,scr_rtcclk_clkreq_assert_ascxdscb,scr_rtcclk_clkreq_deassert_ascxdscb,scr_rtcclk_clkreq_override_en,scr_rtcclk_clkreq_override_value,scr_stpreq_assert_ascxdscb,scr_stpreq_deassert_ascxdscb,scr_stpreq_override_en,scr_stpreq_override_value,, mptu_0p125clk_div_unbuf,mptu_0p25clk_div_unbuf,mptu_0p25clk_unbuf,mptu_0p5clk_div_unbuf,mptu_0p5clk_unbuf,mptu_1p0clk_clkenable,mptu_rst_scan_b,',
  'modName': 'dfi_slv_pmu',
  'modParams': 'ADDRWD=32,DATAWD=32,CLKGATE_MAXCNT=6'}]

tstBuilderDict = {
 'dfi_pmu': [{'instName': 'gen_pm',
              'instance': 'gen_pm',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ".criclk(hclk),.crirst_b(pm_mainrst_b),.spid_pm_clk(dfi_hclk),.spid_pmclk_ack(idfi_hclk_clkack),.pm_init_complete('0),.scr_spidclksel(2'b10),.ispid_powergood_rst_n(pm_mainrst_b),.spid_pm_req('0),.spid_pm_msg('0),.scr_pmst_pm5_dsc_cnt('0),.scr_pmst_pm6_asc_cnt('0),.scr_pmst_pm6_dsc_cnt('0),.scr_pmst_pm7_asc_cnt('0),.scr_pmst_pm7_dsc_cnt('0),.scr_pmst_pm8_asc_cnt('0),.scr_pmst_pm8_dsc_cnt('0),.scr_pmst_pm9_asc_cnt('0),.scr_pmst_pm9_dsc_cnt('0),.scr_pmst_pmA_asc_cnt('0),.scr_pmst_pmA_dsc_cnt('0),.scr_pmst_pmB_asc_cnt('0),.scr_pmst_pmB_dsc_cnt('0),.scr_pmst_pmC_asc_cnt('0),.scr_pmst_pmC_dsc_cnt('0),.scr_pmst_pmD_asc_cnt('0),.scr_pmst_pmD_dsc_cnt('0),.scr_pmst_pmE_asc_cnt('0),.scr_pmst_pmE_dsc_cnt('0), .pm_stall(local_pmstall)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_prepm0_cnt[3:0], '1, gpmclk, pmrst_b)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_assert_cnt [3:0], '1, gpmclk, pmrst_b)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_assert_state[4:0] , '1, gpmclk, pmrst_b)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_assert_ascxdscb, '1, gpmclk, pmrst_b)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_deassert_cnt [3:0], '1, gpmclk, pmrst_b)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_deassert_state[4:0] , '1, gpmclk, pmrst_b)"},
             {'instName': '',
              'instance': 'MMEM_ASYNC_RSTB_MSFF',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': "(local_dfx_pmsig_deassert_ascxdscb, '1, gpmclk, pmrst_b)"},
             {'instName': 'dficlk_clkreq',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''},
             {'instName': 'idfi_dficlk_clkack',
              'instance': 'gen_pmclkackstall',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ".pmstall(local_dficlk_stall),.clkreq(pm_dficlk_clkreq),.scr_pmsig_stall_enable('1)"},
             {'instName': 'hclk_clkreq',
              'instance': 'gen_pmsignalpst',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''},
             {'instName': 'idfi_hclk_clkack',
              'instance': 'gen_pmclkackstall',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ".pmstall(local_hclk_stall),.clkreq(pm_hclk_clkreq),.scr_pmsig_stall_enable('1)"},
             {'instName': 'hpetclk_clkreq',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''},
             {'instName': 'idfi_hpetclk_clkack',
              'instance': 'gen_pmclkackstall',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ".pmstall(local_hpetclk_stall),.clkreq(pm_hpetclk_clkreq),.scr_pmsig_stall_enable('1)"},
             {'instName': 'rtcclk_clkreq',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''},
             {'instName': 'idfi_rtcclk_clkack',
              'instance': 'gen_pmclkackstall',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ".pmstall(local_rtcclk_stall),.clkreq(pm_rtcclk_clkreq),.scr_pmsig_stall_enable('1)"},
             {'instName': 'gen_pmstallor',
              'instance': 'gen_pmstallor',
              'modName': 'dfi_pmu',
              'params': '.WIDTH(5)',
              'signalOverrides': '.pmstalls_in({local_stpreq_stall, local_dficlk_stall, local_hclk_stall, local_hpetclk_stall, local_rtcclk_stall}), .pmstall(local_pmstall)'},
             {'instName': 'dfi_rst_b',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_dfi_rst_b)'},
             {'instName': 'mia_rst_b_pre',
              'instance': 'always_comb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': 'local_mia_rst_b && scr_mia_rst_b'},
             {'instName': 'mia_rst_b',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_mia_rst_b)'},
             {'instName': 'iosfsb_rst_b',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_iosfsb_rst_b)'},
             {'instName': 'hclk_rst_b',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_hclk_rst_b)'},
             {'instName': 'mptu_rst_b',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_mptu_rst_b)'},
             {'instName': 'hpet_rst_b',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_hpet_rst_b)'},
             {'instName': 'stpreq',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.pmsignal(local_stpreq)'},
             {'instName': 'pm_stpreqnn',
              'instance': 'always_comb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '! local_stpreq'},
             {'instName': 'mia_stopgnt',
              'instance': 'gen_pmclkackstall',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ".pmstall(local_stpreq_stall),.clkreq(local_stpreq),.scr_pmsig_stall_enable('1)"},
             {'instName': 'pm_mainrst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(dfi_rstb), .clk_in(dfi_hclk), .sync_rst_n(pm_mainrst_b)'},
             {'instName': 'pm_crirst_b',
              'instance': 'always_comb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': 'pm_mainrst_b'},
             {'instName': 'dfi_rst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(local_dfi_rst_b), .clk_in(dfi_clk), .sync_rst_n(pm_dfirst_b)'},
             {'instName': 'mia_rst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(mia_rst_b_pre), .clk_in(dfi_hclk), .sync_rst_n(pm_miarst_b)'},
             {'instName': 'local_miarst',
              'instance': 'always_comb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '! pm_miarst_b'},
             {'instName': 'miarst',
              'instance': 'ctech_segddr3_clock_buf',
              'modName': 'dfi_pmu',
              'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
              'signalOverrides': '(.ck(local_miarst), .o(pm_miarst))'},
             {'instName': 'iosfsb_rst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(local_iosfsb_rst_b), .clk_in(dfi_hclk), .sync_rst_n(pm_iosfsbrst_b)'},
             {'instName': 'hclk_rst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(local_hclk_rst_b), .clk_in(dfi_hclk), .sync_rst_n(pm_hclkrst_b)'},
             {'instName': 'mptu_rst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(local_mptu_rst_b), .clk_in(dfi_clk), .sync_rst_n(pm_mpturst_b)'},
             {'instName': 'hpet_rst_b',
              'instance': 'gen_resetsync',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': '.async_rst_n(local_hpet_rst_b), .clk_in(dfi_hpet_clk), .sync_rst_n(pm_hpetrst_b)'},
             {'instName': 'mia_clkenable',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''},
             {'instName': 'mptu_clkenable',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''},
             {'instName': 'iosfsb_clkenable',
              'instance': 'gen_pmsignalrstb',
              'modName': 'dfi_pmu',
              'params': '',
              'signalOverrides': ''}],
 'dfi_pmu_clockgen': [{'instName': 'local_ahb_cmd_f',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'dcr_ahb_dyncgdis | !ahb_idle | ahb_busy | ahb_inprogress | dcr_pm_sw_req | dcr_pm_hvm_req'},
                      {'instName': 'ahb_dyn_cgctrl',
                       'instance': 'gen_cgctrl',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '.clk(hclk), .rst_b(pm_hclkrst_b), .cmd_f(local_ahb_cmd_f), .scr_clkgate_maxcntr(scr_ahb_cgmaxcntr), .cgfsm_clken(local_ahb_clkenable),.cgwaitcnt_nxt(local_cgwaitcnt_nxt),.cgfsm_ps_visa(local_cgfsm_ps_visa),.cg_wrptren(local_cg_wrptren)'},
                      {'instName': 'local_dfi_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_dficlk_clkreq'},
                      {'instName': 'dficlk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_clk),  .en(local_dfi_clkenable), .te(fscan_clkungate), .enclk      (local_gdficlk))'},
                      {'instName': 'dficlk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_gdficlk), .o(dficlk))'},
                      {'instName': 'mptu_1p0clk_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_mptu_clkenable'},
                      {'instName': 'mptu_1p0clk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_clk),  .en(mptu_1p0clk_clkenable), .te(fscan_clkungate), .enclk(local_mptu_1p0clk))'},
                      {'instName': 'mptu_1p0clk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_mptu_1p0clk), .o(mptu_1p0clk))'},
                      {'instName': 'i_mptu_rst_mux',
                       'instance': 'ctech_segddr3_mux_2to1',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '( .d1(fscan_clkgenctrl), .d2(pm_mpturst_b), .s(fscan_clkenctrlen), .o(mptu_rst_scan_b))'},
                      {'instName': 'mptu_divider',
                       'instance': 'gen_cntbaseclkdivider',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .mio2xclk(local_mptu_1p0clk), .cntfloprst_b(mptu_rst_scan_b), .divrst_b(mptu_rst_scan_b), .ref1xclk(mptu_0p5clk_div_unbuf), .ref0p5xclk(mptu_0p25clk_div_unbuf), .ref0p25xclk(mptu_0p125clk_div_unbuf))'},
                      {'instName': 'mptu_0p5',
                       'instance': 'ctech_segddr3_clock_mux',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '( .d1(fscan_postclk), .d2(mptu_0p5clk_div_unbuf), .s(fscan_clkenctrlen), .o(mptu_0p5clk_unbuf))'},
                      {'instName': 'mptu_0p25',
                       'instance': 'ctech_segddr3_clock_mux',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '( .d1(fscan_postclk), .d2(mptu_0p25clk_div_unbuf), .s(fscan_clkenctrlen), .o(mptu_0p25clk_unbuf))'},
                      {'instName': 'mptu_0p5clk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(mptu_0p5clk_unbuf), .o(mptu_0p5clk))'},
                      {'instName': 'mptu_0p25clk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(mptu_0p25clk_unbuf), .o(mptu_0p25clk))'},
                      {'instName': 'local_hpet_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_hpetclk_clkreq'},
                      {'instName': 'hpetclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_hpet_clk),  .en(local_hpet_clkenable), .te(fscan_clkungate), .enclk(local_hpetclk))'},
                      {'instName': 'hpetclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_hpetclk), .o(hpetclk))'},
                      {'instName': 'local_rtc_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_rtcclk_clkreq'},
                      {'instName': 'rtcclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_rtc_clk),  .en(local_rtc_clkenable), .te(fscan_clkungate), .enclk(local_rtcclk))'},
                      {'instName': 'rtcclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_rtcclk), .o(rtcclk))'},
                      {'instName': 'local_h_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_hclk_clkreq'},
                      {'instName': 'hclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_hclk),  .en(local_h_clkenable), .te(fscan_clkungate), .enclk(local_hclk))'},
                      {'instName': 'hclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_hclk), .o(hclk))'},
                      {'instName': 'gated_local_h_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | local_ahb_clkenable'},
                      {'instName': 'gated_hclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_hclk),  .en(gated_local_h_clkenable), .te(fscan_clkungate), .enclk(local_gated_hclk))'},
                      {'instName': 'gated_hclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_gated_hclk), .o(gated_hclk))'},
                      {'instName': 'gated_mialocal_h_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_mia_clkenable'},
                      {'instName': 'mia_hclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_hclk),  .en(gated_mialocal_h_clkenable), .te(fscan_clkungate), .enclk(local_gated_mia_hclk))'},
                      {'instName': 'mia_hclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_gated_mia_hclk), .o(mia_hclk))'},
                      {'instName': 'gated_mptulocal_h_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_mptu_clkenable'},
                      {'instName': 'mptu_hclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_hclk),  .en(gated_mptulocal_h_clkenable), .te(fscan_clkungate), .enclk(local_gated_mptu_hclk))'},
                      {'instName': 'mptu_hclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_gated_mptu_hclk), .o(mptu_hclk))'},
                      {'instName': 'gated_iosfsblocal_h_clkenable',
                       'instance': 'always_comb',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': 'scan_mode | pm_iosfsb_clkenable'},
                      {'instName': 'iosfsb_hclk',
                       'instance': 'ctech_segddr3_clock_gate',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '',
                       'signalOverrides': '( .clk(dfi_hclk),  .en(gated_iosfsblocal_h_clkenable), .te(fscan_clkungate), .enclk(local_gated_iosfsb_hclk))'},
                      {'instName': 'iosfsb_hclk',
                       'instance': 'ctech_segddr3_clock_buf',
                       'modName': 'dfi_pmu_clockgen',
                       'params': '.CTECH_SDATTR("dt"),.CTECH_FREQ("hf")',
                       'signalOverrides': '(.ck(local_gated_iosfsb_hclk), .o(iosfsb_hclk))'}],
 'dfi_pmu_intr': [{'instName': 'pm_irq[0]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'MMT_Legacy_En ? MMT0_Int00 : dcr_irq[0]'},
                  {'instName': 'pm_irq[1]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[1]'},
                  {'instName': 'pm_irq[2]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[2]'},
                  {'instName': 'pm_irq[3]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[3]'},
                  {'instName': 'pm_irq[4]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[4]'},
                  {'instName': 'pm_irq[5]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[5]'},
                  {'instName': 'pm_irq[6]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[6]'},
                  {'instName': 'pm_irq[7]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[7]'},
                  {'instName': 'pm_irq[8]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'MMT_Legacy_En ? MMT1_Int08 : dcr_irq[8]'},
                  {'instName': 'pm_irq[9]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[9]'},
                  {'instName': 'pm_irq[10]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[10]'},
                  {'instName': 'pm_irq[11]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[11]'},
                  {'instName': 'pm_irq[12]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[12]'},
                  {'instName': 'pm_irq[13]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[13]'},
                  {'instName': 'pm_irq[14]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[14]'},
                  {'instName': 'pm_irq[15]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[15]'},
                  {'instName': 'pm_irq[16]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[16]'},
                  {'instName': 'pm_irq[17]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[17]'},
                  {'instName': 'pm_irq[18]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[18]'},
                  {'instName': 'pm_irq[19]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[19]'},
                  {'instName': 'pm_irq[20]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[20] | MMT0_Int20 | MMT1_Int20 | MMT2_Int20'},
                  {'instName': 'pm_irq[21]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[21] | MMT0_Int21 | MMT1_Int21 | MMT2_Int21'},
                  {'instName': 'pm_irq[22]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[22] | MMT0_Int22 | MMT1_Int22 | MMT2_Int22'},
                  {'instName': 'pm_irq[23]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[23] | MMT0_Int23 | MMT1_Int23 | MMT2_Int23'},
                  {'instName': 'pm_irq[24]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[24]'},
                  {'instName': 'pm_irq[25]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[25]'},
                  {'instName': 'pm_irq[26]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[26]'},
                  {'instName': 'pm_irq[27]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[27]'},
                  {'instName': 'pm_irq[28]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[28]'},
                  {'instName': 'pm_irq[29]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[29]'},
                  {'instName': 'pm_irq[30]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[30]'},
                  {'instName': 'pm_irq[31]',
                   'instance': 'always_comb',
                   'modName': 'dfi_pmu_intr',
                   'params': '',
                   'signalOverrides': 'dcr_irq[31]'}],
 'dfi_slv_pmu': [{'instName': 'pmu',
                  'instance': 'dfi_ahb_slvctrl',
                  'modName': 'dfi_slv_pmu',
                  'params': '.ADDRWD(ADDRWD),.DATAWD(DATAWD)',
                  'signalOverrides': '.hclk(gated_hclk), .hrstb(pm_hclkrst_b)'},
                 {'instName': 'pmu',
                  'instance': 'dfi_pmu',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': ''},
                 {'instName': 'pmu',
                  'instance': 'dfi_pmu_intr',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': ''},
                 {'instName': 'pmu',
                  'instance': 'dfi_pmu_clockgen',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': ''},
                 {'instName': 'cfg_addr[31:0]',
                  'instance': 'always_comb',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': 'agt_addr[31:0]'},
                 {'instName': 'pmu',
                  'instance': 'dfi_pmucfg',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': '.criclk(gated_hclk), .crirst_b(pm_crirst_b), .cfg_wbe(agt_be), .cfg_wdata(agt_wdata_out), .read_data(agt_rdata_in), .xstopgrant(mia_stopgnt), .dcr_mia_allow_access(dcr_minia_allow_access), .i_regif_opcode(agt_regif_opcode), .i_regif_valid(agt_regif_valid), .pmclk_ack(idfi_hclk_clkack)'},
                 {'instName': 'agt_resp_in',
                  'instance': 'always_comb',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': "1'b0"},
                 {'instName': 'agt_idle',
                  'instance': 'always_comb',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': "1'b0"},
                 {'instName': 'agt_wrdat_get',
                  'instance': 'always_comb',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': 'agt_wr_en_q'},
                 {'instName': 'agt_wrcmd_get',
                  'instance': 'always_comb',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': 'agt_wr_en'},
                 {'instName': 'agt_rdcmd_get',
                  'instance': 'always_comb',
                  'modName': 'dfi_slv_pmu',
                  'params': '',
                  'signalOverrides': 'agt_rd_en'}]}

tstGenList = ['fmibuffer', 'gen_cgctrl', 'ctech_segddr3_clock_gate', 'gen_pmsignalpst', 
              'gen_pmstallor', 'gen_pmparkvalue', 'ctech_segddr3_mux_2to1', 
              'ctech_segddr3_clock_mux', 'gen_pmclkackstall', 
              'ctech_segddr3_clock_buf', 'gen_pmsignalrstb', 
              'gen_cntbaseclkdivider', 'dfi_pmucfg', 'gen_pminitcomplete', 
              'gen_resetsync', 'gen_pmclkrst', 'gen_pm', 'gen_pmpwronstagger', 
              'gen_pmcfgoverride', 'gen_pmweaklock', 'dfi_ahb_slvctrl']

tstProcessSig1 = {'compilerDirective': '',
 'compilerDirectiveSig': '',
 'direction': 'input',
 'drivers': 0,
 'interface': False,
 'name': 'strVal',
 'packed': '',
 'receivers': 0,
 'type': 'logic',
 'unpacked': ''}

tstProcessSig2 = {
                     'compilerDirective': '',
                     'compilerDirectiveSig': '',
                     'direction': 'input',
                     'interface': False,
                     'name': 'strVal',
                     'packed': '[15]',
                     'type': 'logic', 
                     'receivers': 0,
                     'drivers': 0,
                     'unpacked': ''
                }

tstProcessSig3 = {
                     'compilerDirective': '',
                     'compilerDirectiveSig': '',
                     'direction': 'output',
                     'interface': False,
                     'name': 'strVal2',
                     'packed': '[15:0][7:4]',
                     'type': 'logic',
                     'receivers': 0,
                     'drivers': 0,
                     'unpacked': ''
                }

tstProcessSigFree1 = [{'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'MMT_Legacy_En',
  'packed': '',
  'type': 'logic',
  'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'MMT0_Int00',
  'packed': '',
  'type': 'logic',  
  'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'dcr_irq',
  'packed': '[0]',
  'type': 'logic',
  'receivers': 0,
  'drivers': 0,
  'unpacked': ''}]

tstProcessSigFree2 = [{'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'dcr_irq',
  'packed': '[20]',
  'type': 'logic',
  'receivers': 0,
  'drivers': 0,  
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'MMT0_Int20',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'MMT1_Int20',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'MMT2_Int20',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''}]

tstProcessSigFree3 = [{'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'dcr_ahb_dyncgdis',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'ahb_idle',
  'packed': '',
   'receivers': 0,
  'drivers': 0, 
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'ahb_busy',
  'packed': '',
    'receivers': 0,
  'drivers': 0,
  'type': 'logic',
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'ahb_inprogress',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'dcr_pm_sw_req',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'dcr_pm_hvm_req',
  'packed': '',
  'type': 'logic',
   'receivers': 0,
  'drivers': 0, 
  'unpacked': ''}]

tstProcessSigFree4 = [{'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'muxSel',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'sigA',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''},
 {'compilerDirective': '',
  'compilerDirectiveSig': '',
  'direction': 'input',
  'interface': False,
  'name': 'sigB',
  'packed': '',
  'type': 'logic',
    'receivers': 0,
  'drivers': 0,
  'unpacked': ''}]

tstBuildStr1 = '''
// ************************************************************************
// Company            : Intel Corporation, Folsom, CA
// Module Name        : dfi_pmu_intr
// File Name          : dfi_pmu_intr.sv
// Author             : builder.py
// ************************************************************************
// Confidentiality Information
// ************************************************************************

// ------------------------
// Include File Definitions
// ------------------------
`include "mmem_macros.sv"

module dfi_pmu_intr
(
        output  logic              [31:0] pm_irq,
        input   logic                     MMT0_Int00,
        input   logic              [31:0] dcr_irq,
        input   logic                     MMT1_Int08,
        input   logic                     MMT0_Int20,
        input   logic                     MMT1_Int20,
        input   logic                     MMT2_Int20,
        input   logic                     MMT0_Int21,
        input   logic                     MMT1_Int21,
        input   logic                     MMT2_Int21,
        input   logic                     MMT0_Int22,
        input   logic                     MMT1_Int22,
        input   logic                     MMT2_Int22,
        input   logic                     MMT0_Int23,
        input   logic                     MMT1_Int23,
        input   logic                     MMT2_Int23);

// Local Signals
logic                     MMT_Legacy_En;

// *******************
// always_comb: pm_irq[0]
// *******************
always_comb pm_irq[0]                                         = MMT_Legacy_En ? MMT0_Int00 : dcr_irq[0];

// *******************
// always_comb: pm_irq[1]
// *******************
always_comb pm_irq[1]                                         = dcr_irq[1];

// *******************
// always_comb: pm_irq[2]
// *******************
always_comb pm_irq[2]                                         = dcr_irq[2];

// *******************
// always_comb: pm_irq[3]
// *******************
always_comb pm_irq[3]                                         = dcr_irq[3];

// *******************
// always_comb: pm_irq[4]
// *******************
always_comb pm_irq[4]                                         = dcr_irq[4];

// *******************
// always_comb: pm_irq[5]
// *******************
always_comb pm_irq[5]                                         = dcr_irq[5];

// *******************
// always_comb: pm_irq[6]
// *******************
always_comb pm_irq[6]                                         = dcr_irq[6];

// *******************
// always_comb: pm_irq[7]
// *******************
always_comb pm_irq[7]                                         = dcr_irq[7];

// *******************
// always_comb: pm_irq[8]
// *******************
always_comb pm_irq[8]                                         = MMT_Legacy_En ? MMT1_Int08 : dcr_irq[8];

// *******************
// always_comb: pm_irq[9]
// *******************
always_comb pm_irq[9]                                         = dcr_irq[9];

// *******************
// always_comb: pm_irq[10]
// *******************
always_comb pm_irq[10]                                        = dcr_irq[10];

// *******************
// always_comb: pm_irq[11]
// *******************
always_comb pm_irq[11]                                        = dcr_irq[11];

// *******************
// always_comb: pm_irq[12]
// *******************
always_comb pm_irq[12]                                        = dcr_irq[12];

// *******************
// always_comb: pm_irq[13]
// *******************
always_comb pm_irq[13]                                        = dcr_irq[13];

// *******************
// always_comb: pm_irq[14]
// *******************
always_comb pm_irq[14]                                        = dcr_irq[14];

// *******************
// always_comb: pm_irq[15]
// *******************
always_comb pm_irq[15]                                        = dcr_irq[15];

// *******************
// always_comb: pm_irq[16]
// *******************
always_comb pm_irq[16]                                        = dcr_irq[16];

// *******************
// always_comb: pm_irq[17]
// *******************
always_comb pm_irq[17]                                        = dcr_irq[17];

// *******************
// always_comb: pm_irq[18]
// *******************
always_comb pm_irq[18]                                        = dcr_irq[18];

// *******************
// always_comb: pm_irq[19]
// *******************
always_comb pm_irq[19]                                        = dcr_irq[19];

// *******************
// always_comb: pm_irq[20]
// *******************
always_comb pm_irq[20]                                        = dcr_irq[20] | MMT0_Int20 | MMT1_Int20 | MMT2_Int20;

// *******************
// always_comb: pm_irq[21]
// *******************
always_comb pm_irq[21]                                        = dcr_irq[21] | MMT0_Int21 | MMT1_Int21 | MMT2_Int21;

// *******************
// always_comb: pm_irq[22]
// *******************
always_comb pm_irq[22]                                        = dcr_irq[22] | MMT0_Int22 | MMT1_Int22 | MMT2_Int22;

// *******************
// always_comb: pm_irq[23]
// *******************
always_comb pm_irq[23]                                        = dcr_irq[23] | MMT0_Int23 | MMT1_Int23 | MMT2_Int23;

// *******************
// always_comb: pm_irq[24]
// *******************
always_comb pm_irq[24]                                        = dcr_irq[24];

// *******************
// always_comb: pm_irq[25]
// *******************
always_comb pm_irq[25]                                        = dcr_irq[25];

// *******************
// always_comb: pm_irq[26]
// *******************
always_comb pm_irq[26]                                        = dcr_irq[26];

// *******************
// always_comb: pm_irq[27]
// *******************
always_comb pm_irq[27]                                        = dcr_irq[27];

// *******************
// always_comb: pm_irq[28]
// *******************
always_comb pm_irq[28]                                        = dcr_irq[28];

// *******************
// always_comb: pm_irq[29]
// *******************
always_comb pm_irq[29]                                        = dcr_irq[29];

// *******************
// always_comb: pm_irq[30]
// *******************
always_comb pm_irq[30]                                        = dcr_irq[30];

// *******************
// always_comb: pm_irq[31]
// *******************
always_comb pm_irq[31]                                        = dcr_irq[31];

// *******************
// always_comb: MMT_Legacy_En
// *******************
always_comb MMT_Legacy_En                                     = 1'b1;



endmodule'''

tstBuildStr2 = '''
// ************************************************************************
// Company            : Intel Corporation, Folsom, CA
// Module Name        : dfi_mmem
// File Name          : dfi_mmem.sv
// Author             : builder.py
// ************************************************************************
// Confidentiality Information
// ************************************************************************

// ------------------------
// Include File Definitions
// ------------------------
`include "mmem_macros.sv"

module dfi_mmem
(
        input   logic                     gpmclk);

// Local Signals
logic               [3:0] local_dfx_pmsig_prepmA_cnt;
logic                     pmrst_b;
logic               [3:0] local_dfx_pmsig_prepm0_cnt;
logic               [3:0] local_dfx_pmsig_assert_cnt;
logic               [4:0] local_dfx_pmsig_assert_state;
logic                     local_dfx_pmsig_assert_ascxdscb;
logic               [3:0] local_dfx_pmsig_deassert_cnt;
logic               [4:0] local_dfx_pmsig_deassert_state;
logic                     local_dfx_pmsig_deassert_ascxdscb;

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_prepmA_cnt[3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_prepm0_cnt[3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_assert_cnt [3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_assert_state[4:0] , '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_assert_ascxdscb, '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_deassert_cnt [3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_deassert_state[4:0] , '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_deassert_ascxdscb, '1, gpmclk, pmrst_b)



endmodule'''

tstBuildStr3 = '''
// ************************************************************************
// Company            : Intel Corporation, Folsom, CA
// Module Name        : dfi_pmu
// File Name          : dfi_pmu.sv
// Author             : builder.py
// ************************************************************************
// Confidentiality Information
// ************************************************************************

// ------------------------
// Include File Definitions
// ------------------------
`include "mmem_macros.sv"

module dfi_pmu
#( parameter
    CLKGATE_MAXCNT=6
 )
(
        input   logic                     hclk,
        input   logic                     pm_mainrst_b,
        input   logic                     dfi_hclk,
        input   logic                     idfi_hclk_clkack,
        input   logic                     dcr_pm_pmrst_b,
        input   logic                     dcr_pm_clkgateen,
        input   logic                     scr_pmclk_clkreq,
        input   logic              [15:0] scr_pmst_prepm0_dsc_cnt,
        input   logic              [15:0] scr_pmst_pm0_dsc_cnt,
        input   logic              [15:0] scr_pmst_pm1_dsc_cnt,
        input   logic              [15:0] scr_pmst_pm1_asc_cnt,
        input   logic              [15:0] scr_pmst_pm2_dsc_cnt,
        input   logic              [15:0] scr_pmst_pm2_asc_cnt,
        input   logic              [15:0] scr_pmst_pm3_dsc_cnt,
        input   logic              [15:0] scr_pmst_pm3_asc_cnt,
        input   logic              [15:0] scr_pmst_pm4_dsc_cnt,
        input   logic              [15:0] scr_pmst_pm4_asc_cnt,
        input   logic              [15:0] scr_pmst_pm5_asc_cnt,
        input   logic               [3:0] scr_pm_hvm_delay,
        input   logic                     dcr_pm_sw_req,
        input   logic               [4:0] scr_pm_sw_msg,
        input   logic               [4:0] scr_hvm_pmmsg,
        input   logic                     dcr_pm_hvm_req,
        input   logic                     fscan_clkungate,
        input   logic                     spid_dfxrefclk,
        input   logic                     fscan_rstbypen,
        input   logic                     fscan_byprst_b,
        input   logic                     dfx_rst_b_ovren,
        input   logic                     dfx_rst_b_ovrval,
        input   logic                     iddr_fscan_mode,
        input   logic                     dt_dfx_pmclk_bypen,
        input   logic                     dt_dfx_pmrst_b_ovren,
        input   logic                     dt_dfx_pmrst_b_ovrval,
        input   logic                     dt_dfx_pm_req_block,
        output  logic                     pm_sw_req_clear,
        output  logic                     pm_sw_ack,
        output  logic                     pm_hvm_req_clear,
        output  logic               [5:0] pm_cfg_status,
        output  logic                     pm_pmclk_clkreq,
        input   logic               [3:0] scr_dficlk_clkreq_prepm0_cnt,
        input   logic               [3:0] scr_dficlk_clkreq_assert_cnt,
        input   logic               [4:0] scr_dficlk_clkreq_assert_state,
        input   logic                     scr_dficlk_clkreq_assert_ascxdscb,
        input   logic               [3:0] scr_dficlk_clkreq_deassert_cnt,
        input   logic               [4:0] scr_dficlk_clkreq_deassert_state,
        input   logic                     scr_dficlk_clkreq_deassert_ascxdscb,
        input   logic                     scr_dficlk_clkreq_override_en,
        input   logic                     scr_dficlk_clkreq_override_value,
        input   logic                     fscan_mode_atspeed,
        output  logic                     pm_dficlk_clkreq,
        input   logic                     idfi_dficlk_clkack,
        input   logic               [3:0] scr_hclk_clkreq_prepm0_cnt,
        input   logic               [3:0] scr_hclk_clkreq_assert_cnt,
        input   logic               [4:0] scr_hclk_clkreq_assert_state,
        input   logic                     scr_hclk_clkreq_assert_ascxdscb,
        input   logic               [3:0] scr_hclk_clkreq_deassert_cnt,
        input   logic               [4:0] scr_hclk_clkreq_deassert_state,
        input   logic                     scr_hclk_clkreq_deassert_ascxdscb,
        input   logic                     scr_hclk_clkreq_override_en,
        input   logic                     scr_hclk_clkreq_override_value,
        output  logic                     pm_hclk_clkreq,
        input   logic               [3:0] scr_hpetclk_clkreq_prepm0_cnt,
        input   logic               [3:0] scr_hpetclk_clkreq_assert_cnt,
        input   logic               [4:0] scr_hpetclk_clkreq_assert_state,
        input   logic                     scr_hpetclk_clkreq_assert_ascxdscb,
        input   logic               [3:0] scr_hpetclk_clkreq_deassert_cnt,
        input   logic               [4:0] scr_hpetclk_clkreq_deassert_state,
        input   logic                     scr_hpetclk_clkreq_deassert_ascxdscb,
        input   logic                     scr_hpetclk_clkreq_override_en,
        input   logic                     scr_hpetclk_clkreq_override_value,
        output  logic                     pm_hpetclk_clkreq,
        input   logic                     idfi_hpetclk_clkack,
        input   logic               [3:0] scr_rtcclk_clkreq_prepm0_cnt,
        input   logic               [3:0] scr_rtcclk_clkreq_assert_cnt,
        input   logic               [4:0] scr_rtcclk_clkreq_assert_state,
        input   logic                     scr_rtcclk_clkreq_assert_ascxdscb,
        input   logic               [3:0] scr_rtcclk_clkreq_deassert_cnt,
        input   logic               [4:0] scr_rtcclk_clkreq_deassert_state,
        input   logic                     scr_rtcclk_clkreq_deassert_ascxdscb,
        input   logic                     scr_rtcclk_clkreq_override_en,
        input   logic                     scr_rtcclk_clkreq_override_value,
        output  logic                     pm_rtcclk_clkreq,
        input   logic                     idfi_rtcclk_clkack,
        input   logic               [3:0] scr_dfi_rst_b_prepm0_cnt,
        input   logic               [3:0] scr_dfi_rst_b_assert_cnt,
        input   logic               [4:0] scr_dfi_rst_b_assert_state,
        input   logic                     scr_dfi_rst_b_assert_ascxdscb,
        input   logic               [3:0] scr_dfi_rst_b_deassert_cnt,
        input   logic               [4:0] scr_dfi_rst_b_deassert_state,
        input   logic                     scr_dfi_rst_b_deassert_ascxdscb,
        input   logic                     scr_dfi_rst_b_override_en,
        input   logic                     scr_dfi_rst_b_override_value,
        input   logic                     scr_mia_rst_b);

// Local Signals
logic                     local_pmstall;
logic                     pmrst_b;
logic                     gpmclk;
logic                     pm_spid_pm_ack;
logic                     pm_idle;
logic                     pm_active;
logic                     pm_asc;
logic                     pm_dsc;
logic               [3:0] pm_count;
logic              [15:0] pm_hdcount;
logic               [4:0] pm_state;
logic               [3:0] local_dfx_pmsig_prepm0_cnt;
logic               [3:0] local_dfx_pmsig_assert_cnt;
logic               [4:0] local_dfx_pmsig_assert_state;
logic                     local_dfx_pmsig_assert_ascxdscb;
logic               [3:0] local_dfx_pmsig_deassert_cnt;
logic               [4:0] local_dfx_pmsig_deassert_state;
logic                     local_dfx_pmsig_deassert_ascxdscb;
logic                     local_dficlk_stall;
logic                     local_hclk_stall;
logic                     local_hpetclk_stall;
logic                     local_rtcclk_stall;
logic                     local_stpreq_stall;
logic                     local_dfi_rst_b;
logic                     mia_rst_b_pre;
logic                     local_mia_rst_b;


// *******************
// gen_pm:gen_pm::.criclk(hclk),.crirst_b(pm_mainrst_b),.spid_pm_clk(dfi_hclk),.spid_pmclk_ack(idfi_hclk_clkack),.pm_init_complete('0),.scr_spidclksel(2'b10),.ispid_powergood_rst_n(pm_mainrst_b),.spid_pm_req('0),.spid_pm_msg('0),.scr_pmst_pm5_dsc_cnt('0),.scr_pmst_pm6_asc_cnt('0),.scr_pmst_pm6_dsc_cnt('0),.scr_pmst_pm7_asc_cnt('0),.scr_pmst_pm7_dsc_cnt('0),.scr_pmst_pm8_asc_cnt('0),.scr_pmst_pm8_dsc_cnt('0),.scr_pmst_pm9_asc_cnt('0),.scr_pmst_pm9_dsc_cnt('0),.scr_pmst_pmA_asc_cnt('0),.scr_pmst_pmA_dsc_cnt('0),.scr_pmst_pmB_asc_cnt('0),.scr_pmst_pmB_dsc_cnt('0),.scr_pmst_pmC_asc_cnt('0),.scr_pmst_pmC_dsc_cnt('0),.scr_pmst_pmD_asc_cnt('0),.scr_pmst_pmD_dsc_cnt('0),.scr_pmst_pmE_asc_cnt('0),.scr_pmst_pmE_dsc_cnt('0),.pm_stall(local_pmstall)
// *******************
gen_pm i_gen_pm_gen_pm
   (
      .criclk                  (hclk),
      .crirst_b                (pm_mainrst_b),
      .spid_pm_clk             (dfi_hclk),
      .spid_pmclk_ack          (idfi_hclk_clkack),
      .ispid_powergood_rst_n   (pm_mainrst_b),
      .spid_pm_req             ('0),
      .spid_pm_msg             ('0),
      .pm_stall                (local_pmstall),
      .pm_init_complete        ('0),
      .dcr_pm_pmrst_b          (dcr_pm_pmrst_b),
      .dcr_pm_clkgateen        (dcr_pm_clkgateen),
      .scr_pmclk_clkreq        (scr_pmclk_clkreq),
      .scr_spidclksel          (2'b10),
      .scr_pmst_prepm0_dsc_cnt (scr_pmst_prepm0_dsc_cnt),
      .scr_pmst_pm0_dsc_cnt    (scr_pmst_pm0_dsc_cnt),
      .scr_pmst_pm1_dsc_cnt    (scr_pmst_pm1_dsc_cnt),
      .scr_pmst_pm1_asc_cnt    (scr_pmst_pm1_asc_cnt),
      .scr_pmst_pm2_dsc_cnt    (scr_pmst_pm2_dsc_cnt),
      .scr_pmst_pm2_asc_cnt    (scr_pmst_pm2_asc_cnt),
      .scr_pmst_pm3_dsc_cnt    (scr_pmst_pm3_dsc_cnt),
      .scr_pmst_pm3_asc_cnt    (scr_pmst_pm3_asc_cnt),
      .scr_pmst_pm4_dsc_cnt    (scr_pmst_pm4_dsc_cnt),
      .scr_pmst_pm4_asc_cnt    (scr_pmst_pm4_asc_cnt),
      .scr_pmst_pm5_dsc_cnt    ('0),
      .scr_pmst_pm5_asc_cnt    (scr_pmst_pm5_asc_cnt),
      .scr_pmst_pm6_dsc_cnt    ('0),
      .scr_pmst_pm6_asc_cnt    ('0),
      .scr_pmst_pm7_dsc_cnt    ('0),
      .scr_pmst_pm7_asc_cnt    ('0),
      .scr_pmst_pm8_dsc_cnt    ('0),
      .scr_pmst_pm8_asc_cnt    ('0),
      .scr_pmst_pm9_dsc_cnt    ('0),
      .scr_pmst_pm9_asc_cnt    ('0),
      .scr_pmst_pmA_dsc_cnt    ('0),
      .scr_pmst_pmA_asc_cnt    ('0),
      .scr_pmst_pmB_dsc_cnt    ('0),
      .scr_pmst_pmB_asc_cnt    ('0),
      .scr_pmst_pmC_dsc_cnt    ('0),
      .scr_pmst_pmC_asc_cnt    ('0),
      .scr_pmst_pmD_dsc_cnt    ('0),
      .scr_pmst_pmD_asc_cnt    ('0),
      .scr_pmst_pmE_dsc_cnt    ('0),
      .scr_pmst_pmE_asc_cnt    ('0),
      .scr_pm_hvm_delay        (scr_pm_hvm_delay),
      .dcr_pm_sw_req           (dcr_pm_sw_req),
      .scr_pm_sw_msg           (scr_pm_sw_msg),
      .scr_hvm_pmmsg           (scr_hvm_pmmsg),
      .dcr_pm_hvm_req          (dcr_pm_hvm_req),
      .fscan_clkungate         (fscan_clkungate),
      .spid_dfxrefclk          (spid_dfxrefclk),
      .fscan_rstbypen          (fscan_rstbypen),
      .fscan_byprst_b          (fscan_byprst_b),
      .dfx_rst_b_ovren         (dfx_rst_b_ovren),
      .dfx_rst_b_ovrval        (dfx_rst_b_ovrval),
      .iddr_fscan_mode         (iddr_fscan_mode),
      .dt_dfx_pmclk_bypen      (dt_dfx_pmclk_bypen),
      .dt_dfx_pmrst_b_ovren    (dt_dfx_pmrst_b_ovren),
      .dt_dfx_pmrst_b_ovrval   (dt_dfx_pmrst_b_ovrval),
      .dt_dfx_pm_req_block     (dt_dfx_pm_req_block),
      .pmrst_b                 (pmrst_b),
      .gpmclk                  (gpmclk),
      .pm_sw_req_clear         (pm_sw_req_clear),
      .pm_sw_ack               (pm_sw_ack),
      .pm_hvm_req_clear        (pm_hvm_req_clear),
      .pm_spid_pm_ack          (pm_spid_pm_ack),
      .pm_idle                 (pm_idle),
      .pm_active               (pm_active),
      .pm_asc                  (pm_asc),
      .pm_dsc                  (pm_dsc),
      .pm_count                (pm_count),
      .pm_hdcount              (pm_hdcount),
      .pm_state                (pm_state),
      .pm_cfg_status           (pm_cfg_status),
      .pm_pmclk_clkreq         (pm_pmclk_clkreq)
   );

// *******************
// gen_pmsignalrstb:dficlk_clkreq::
// *******************
gen_pmsignalrstb i_gen_pmsignalrstb_dficlk_clkreq
   (
      .gpmclk                            (gpmclk),
      .pmrst_b                           (pmrst_b),
      .pm_active                         (pm_active),
      .pm_asc                            (pm_asc),
      .pm_dsc                            (pm_dsc),
      .pm_count                          (pm_count),
      .pm_state                          (pm_state),
      .scr_pmsig_prepm0_cnt              (scr_dficlk_clkreq_prepm0_cnt),
      .scr_pmsig_assert_cnt              (scr_dficlk_clkreq_assert_cnt),
      .scr_pmsig_assert_state            (scr_dficlk_clkreq_assert_state),
      .scr_pmsig_assert_ascxdscb         (scr_dficlk_clkreq_assert_ascxdscb),
      .scr_pmsig_deassert_cnt            (scr_dficlk_clkreq_deassert_cnt),
      .scr_pmsig_deassert_state          (scr_dficlk_clkreq_deassert_state),
      .scr_pmsig_deassert_ascxdscb       (scr_dficlk_clkreq_deassert_ascxdscb),
      .scr_pmsig_override_en             (scr_dficlk_clkreq_override_en),
      .scr_pmsig_override_value          (scr_dficlk_clkreq_override_value),
      .fscan_mode_atspeed                (fscan_mode_atspeed),
      .local_dfx_pmsig_prepm0_cnt        (local_dfx_pmsig_prepm0_cnt),
      .local_dfx_pmsig_assert_cnt        (local_dfx_pmsig_assert_cnt),
      .local_dfx_pmsig_assert_state      (local_dfx_pmsig_assert_state),
      .local_dfx_pmsig_assert_ascxdscb   (local_dfx_pmsig_assert_ascxdscb),
      .local_dfx_pmsig_deassert_cnt      (local_dfx_pmsig_deassert_cnt),
      .local_dfx_pmsig_deassert_state    (local_dfx_pmsig_deassert_state),
      .local_dfx_pmsig_deassert_ascxdscb (local_dfx_pmsig_deassert_ascxdscb),
      .pmsignal                          (pm_dficlk_clkreq)
   );

// *******************
// gen_pmclkackstall:idfi_dficlk_clkack::.pmstall(local_dficlk_stall),.clkreq(pm_dficlk_clkreq),.scr_pmsig_stall_enable('1)
// *******************
gen_pmclkackstall i_gen_pmclkackstall_idfi_dficlk_clkack
   (
      .gpmclk                 (gpmclk),
      .pmrst_b                (pmrst_b),
      .scr_pmsig_stall_enable ('1),
      .clkack                 (idfi_dficlk_clkack),
      .clkreq                 (pm_dficlk_clkreq),
      .pmstall                (local_dficlk_stall)
   );

// *******************
// gen_pmsignalpst:hclk_clkreq::
// *******************
gen_pmsignalpst i_gen_pmsignalpst_hclk_clkreq
   (
      .gpmclk                            (gpmclk),
      .pmrst_b                           (pmrst_b),
      .pm_active                         (pm_active),
      .pm_asc                            (pm_asc),
      .pm_dsc                            (pm_dsc),
      .pm_count                          (pm_count),
      .pm_state                          (pm_state),
      .scr_pmsig_prepm0_cnt              (scr_hclk_clkreq_prepm0_cnt),
      .scr_pmsig_assert_cnt              (scr_hclk_clkreq_assert_cnt),
      .scr_pmsig_assert_state            (scr_hclk_clkreq_assert_state),
      .scr_pmsig_assert_ascxdscb         (scr_hclk_clkreq_assert_ascxdscb),
      .scr_pmsig_deassert_cnt            (scr_hclk_clkreq_deassert_cnt),
      .scr_pmsig_deassert_state          (scr_hclk_clkreq_deassert_state),
      .scr_pmsig_deassert_ascxdscb       (scr_hclk_clkreq_deassert_ascxdscb),
      .scr_pmsig_override_en             (scr_hclk_clkreq_override_en),
      .scr_pmsig_override_value          (scr_hclk_clkreq_override_value),
      .fscan_mode_atspeed                (fscan_mode_atspeed),
      .local_dfx_pmsig_prepm0_cnt        (local_dfx_pmsig_prepm0_cnt),
      .local_dfx_pmsig_assert_cnt        (local_dfx_pmsig_assert_cnt),
      .local_dfx_pmsig_assert_state      (local_dfx_pmsig_assert_state),
      .local_dfx_pmsig_assert_ascxdscb   (local_dfx_pmsig_assert_ascxdscb),
      .local_dfx_pmsig_deassert_cnt      (local_dfx_pmsig_deassert_cnt),
      .local_dfx_pmsig_deassert_state    (local_dfx_pmsig_deassert_state),
      .local_dfx_pmsig_deassert_ascxdscb (local_dfx_pmsig_deassert_ascxdscb),
      .pmsignal                          (pm_hclk_clkreq)
   );

// *******************
// gen_pmclkackstall:idfi_hclk_clkack::.pmstall(local_hclk_stall),.clkreq(pm_hclk_clkreq),.scr_pmsig_stall_enable('1)
// *******************
gen_pmclkackstall i_gen_pmclkackstall_idfi_hclk_clkack
   (
      .gpmclk                 (gpmclk),
      .pmrst_b                (pmrst_b),
      .scr_pmsig_stall_enable ('1),
      .clkack                 (idfi_hclk_clkack),
      .clkreq                 (pm_hclk_clkreq),
      .pmstall                (local_hclk_stall)
   );

// *******************
// gen_pmsignalrstb:hpetclk_clkreq::
// *******************
gen_pmsignalrstb i_gen_pmsignalrstb_hpetclk_clkreq
   (
      .gpmclk                            (gpmclk),
      .pmrst_b                           (pmrst_b),
      .pm_active                         (pm_active),
      .pm_asc                            (pm_asc),
      .pm_dsc                            (pm_dsc),
      .pm_count                          (pm_count),
      .pm_state                          (pm_state),
      .scr_pmsig_prepm0_cnt              (scr_hpetclk_clkreq_prepm0_cnt),
      .scr_pmsig_assert_cnt              (scr_hpetclk_clkreq_assert_cnt),
      .scr_pmsig_assert_state            (scr_hpetclk_clkreq_assert_state),
      .scr_pmsig_assert_ascxdscb         (scr_hpetclk_clkreq_assert_ascxdscb),
      .scr_pmsig_deassert_cnt            (scr_hpetclk_clkreq_deassert_cnt),
      .scr_pmsig_deassert_state          (scr_hpetclk_clkreq_deassert_state),
      .scr_pmsig_deassert_ascxdscb       (scr_hpetclk_clkreq_deassert_ascxdscb),
      .scr_pmsig_override_en             (scr_hpetclk_clkreq_override_en),
      .scr_pmsig_override_value          (scr_hpetclk_clkreq_override_value),
      .fscan_mode_atspeed                (fscan_mode_atspeed),
      .local_dfx_pmsig_prepm0_cnt        (local_dfx_pmsig_prepm0_cnt),
      .local_dfx_pmsig_assert_cnt        (local_dfx_pmsig_assert_cnt),
      .local_dfx_pmsig_assert_state      (local_dfx_pmsig_assert_state),
      .local_dfx_pmsig_assert_ascxdscb   (local_dfx_pmsig_assert_ascxdscb),
      .local_dfx_pmsig_deassert_cnt      (local_dfx_pmsig_deassert_cnt),
      .local_dfx_pmsig_deassert_state    (local_dfx_pmsig_deassert_state),
      .local_dfx_pmsig_deassert_ascxdscb (local_dfx_pmsig_deassert_ascxdscb),
      .pmsignal                          (pm_hpetclk_clkreq)
   );

// *******************
// gen_pmclkackstall:idfi_hpetclk_clkack::.pmstall(local_hpetclk_stall),.clkreq(pm_hpetclk_clkreq),.scr_pmsig_stall_enable('1)
// *******************
gen_pmclkackstall i_gen_pmclkackstall_idfi_hpetclk_clkack
   (
      .gpmclk                 (gpmclk),
      .pmrst_b                (pmrst_b),
      .scr_pmsig_stall_enable ('1),
      .clkack                 (idfi_hpetclk_clkack),
      .clkreq                 (pm_hpetclk_clkreq),
      .pmstall                (local_hpetclk_stall)
   );

// *******************
// gen_pmsignalrstb:rtcclk_clkreq::
// *******************
gen_pmsignalrstb i_gen_pmsignalrstb_rtcclk_clkreq
   (
      .gpmclk                            (gpmclk),
      .pmrst_b                           (pmrst_b),
      .pm_active                         (pm_active),
      .pm_asc                            (pm_asc),
      .pm_dsc                            (pm_dsc),
      .pm_count                          (pm_count),
      .pm_state                          (pm_state),
      .scr_pmsig_prepm0_cnt              (scr_rtcclk_clkreq_prepm0_cnt),
      .scr_pmsig_assert_cnt              (scr_rtcclk_clkreq_assert_cnt),
      .scr_pmsig_assert_state            (scr_rtcclk_clkreq_assert_state),
      .scr_pmsig_assert_ascxdscb         (scr_rtcclk_clkreq_assert_ascxdscb),
      .scr_pmsig_deassert_cnt            (scr_rtcclk_clkreq_deassert_cnt),
      .scr_pmsig_deassert_state          (scr_rtcclk_clkreq_deassert_state),
      .scr_pmsig_deassert_ascxdscb       (scr_rtcclk_clkreq_deassert_ascxdscb),
      .scr_pmsig_override_en             (scr_rtcclk_clkreq_override_en),
      .scr_pmsig_override_value          (scr_rtcclk_clkreq_override_value),
      .fscan_mode_atspeed                (fscan_mode_atspeed),
      .local_dfx_pmsig_prepm0_cnt        (local_dfx_pmsig_prepm0_cnt),
      .local_dfx_pmsig_assert_cnt        (local_dfx_pmsig_assert_cnt),
      .local_dfx_pmsig_assert_state      (local_dfx_pmsig_assert_state),
      .local_dfx_pmsig_assert_ascxdscb   (local_dfx_pmsig_assert_ascxdscb),
      .local_dfx_pmsig_deassert_cnt      (local_dfx_pmsig_deassert_cnt),
      .local_dfx_pmsig_deassert_state    (local_dfx_pmsig_deassert_state),
      .local_dfx_pmsig_deassert_ascxdscb (local_dfx_pmsig_deassert_ascxdscb),
      .pmsignal                          (pm_rtcclk_clkreq)
   );

// *******************
// gen_pmclkackstall:idfi_rtcclk_clkack::.pmstall(local_rtcclk_stall),.clkreq(pm_rtcclk_clkreq),.scr_pmsig_stall_enable('1)
// *******************
gen_pmclkackstall i_gen_pmclkackstall_idfi_rtcclk_clkack
   (
      .gpmclk                 (gpmclk),
      .pmrst_b                (pmrst_b),
      .scr_pmsig_stall_enable ('1),
      .clkack                 (idfi_rtcclk_clkack),
      .clkreq                 (pm_rtcclk_clkreq),
      .pmstall                (local_rtcclk_stall)
   );

// *******************
// gen_pmstallor:gen_pmstallor:.WIDTH(5):.pmstalls_in({local_stpreq_stall,local_dficlk_stall,local_hclk_stall,local_hpetclk_stall,local_rtcclk_stall}),.pmstall(local_pmstall)
// *******************
gen_pmstallor
   #(
      .WIDTH (5)
   )
   i_gen_pmstallor_gen_pmstallor
   (
      .pmstalls_in ({local_stpreq_stall,local_dficlk_stall,local_hclk_stall,local_hpetclk_stall,local_rtcclk_stall}),
      .pmstall     (local_pmstall)
   );

// *******************
// gen_pmsignalrstb:dfi_rst_b::.pmsignal(local_dfi_rst_b)
// *******************
gen_pmsignalrstb i_gen_pmsignalrstb_dfi_rst_b
   (
      .gpmclk                            (gpmclk),
      .pmrst_b                           (pmrst_b),
      .pm_active                         (pm_active),
      .pm_asc                            (pm_asc),
      .pm_dsc                            (pm_dsc),
      .pm_count                          (pm_count),
      .pm_state                          (pm_state),
      .scr_pmsig_prepm0_cnt              (scr_dfi_rst_b_prepm0_cnt),
      .scr_pmsig_assert_cnt              (scr_dfi_rst_b_assert_cnt),
      .scr_pmsig_assert_state            (scr_dfi_rst_b_assert_state),
      .scr_pmsig_assert_ascxdscb         (scr_dfi_rst_b_assert_ascxdscb),
      .scr_pmsig_deassert_cnt            (scr_dfi_rst_b_deassert_cnt),
      .scr_pmsig_deassert_state          (scr_dfi_rst_b_deassert_state),
      .scr_pmsig_deassert_ascxdscb       (scr_dfi_rst_b_deassert_ascxdscb),
      .scr_pmsig_override_en             (scr_dfi_rst_b_override_en),
      .scr_pmsig_override_value          (scr_dfi_rst_b_override_value),
      .fscan_mode_atspeed                (fscan_mode_atspeed),
      .local_dfx_pmsig_prepm0_cnt        (local_dfx_pmsig_prepm0_cnt),
      .local_dfx_pmsig_assert_cnt        (local_dfx_pmsig_assert_cnt),
      .local_dfx_pmsig_assert_state      (local_dfx_pmsig_assert_state),
      .local_dfx_pmsig_assert_ascxdscb   (local_dfx_pmsig_assert_ascxdscb),
      .local_dfx_pmsig_deassert_cnt      (local_dfx_pmsig_deassert_cnt),
      .local_dfx_pmsig_deassert_state    (local_dfx_pmsig_deassert_state),
      .local_dfx_pmsig_deassert_ascxdscb (local_dfx_pmsig_deassert_ascxdscb),
      .pmsignal                          (local_dfi_rst_b)
   );
// *******************
// always_comb: mia_rst_b_pre
// *******************
always_comb mia_rst_b_pre                                     = local_mia_rst_b && scr_mia_rst_b;

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_prepm0_cnt[3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_assert_cnt [3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_assert_state[4:0] , '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_assert_ascxdscb, '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_deassert_cnt [3:0], '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_deassert_state[4:0] , '1, gpmclk, pmrst_b)

// *******************
// MMEM: MMEM_ASYNC_RSTB_MSFF
// *******************
`MMEM_ASYNC_RSTB_MSFF          (local_dfx_pmsig_deassert_ascxdscb, '1, gpmclk, pmrst_b)



endmodule'''


test_signal_add_port_string_01 = """[   SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='clk',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='enable',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='is_signed',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='enacc',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='sub_nadd',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selacc',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='resetrs0',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='rs0',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='rs1',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='imm',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='mulmux',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selop0',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selop1',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='selshift',
                 packed='[1:0][(shorten_pipeline-1)*4:0]',
                 unpacked='[(add_extra_instr-1):0]',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='cmode',
                 packed='[1:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='opcode1',
                 packed='[2:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='input',
                 name='opcode2',
                 packed='[2:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='output',
                 name='out_en',
                 packed='',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0),
    SignalRecord(interface=False,
                 sig_type='logic',
                 direction='output',
                 name='out',
                 packed='[31:0]',
                 unpacked='',
                 compilerDirectiveSig='',
                 compilerDirective='',
                 drivers=0,
                 receivers=0)]

"""
