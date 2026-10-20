import sys
from vcdvcd import VCDVCD

VCD = '/tmp/char_close_page_min.vcd'

OP = {0:'NOP',1:'ACT',2:'RD',3:'RDA',4:'WR',5:'WRA',6:'PRE',7:'PREA',8:'REF',9:'REFPB',10:'MRS',11:'ZQCS',12:'ZQCL'}

BASE = 'ddr2_char_uart_tb_top.u_dut.u_dut.u_ctrl.u_core.u_core'
SP   = f'{BASE}.u_sched_plane'
ARB  = f'{SP}.u_arbiter'
BT   = f'{SP}.u_bank_timers.g_rank[0]'

sigs = [
    f'{SP}.cmd_valid_o',
    f'{SP}.cmd_op_o[4:0]',
    f'{SP}.cmd_bank_o[2:0]',
    f'{SP}.cmd_row_o[12:0]',
    f'{SP}.cmd_col_o[9:0]',
    f'{SP}.cmd_ready_i',
    f'{ARB}.r_pick_valid',
    f'{ARB}.r_op[4:0]',
    f'{ARB}.r_bank[2:0]',
    f'{ARB}.r_do_act',
    f'{ARB}.r_do_rd',
    f'{ARB}.r_do_wr',
    f'{ARB}.r_do_pre',
    f'{ARB}.w_fire_out',
    f'{ARB}.w_out_safe',
    f'{ARB}.w_out_reject',
    f'{ARB}.w_out_hold',
    f'{ARB}.w_pick_class[1:0]',
    f'{ARB}.w_valid',
    f'{ARB}.w_op[4:0]',
    f'{ARB}.w_bank[2:0]',
    f'{ARB}.w_do_act',
    f'{ARB}.w_do_rd',
    f'{ARB}.w_do_wr',
    f'{ARB}.w_do_pre',
    f'{ARB}.r_bank_row_active[0][7:0]',
    f'{ARB}.r_bank_pre_ready[0][7:0]',
    f'{ARB}.r_bank_act_ready[0][7:0]',
    f'{ARB}.r_bank_rdwr_ready[0][7:0]',
    f'{ARB}.rd_col_m[7:0]',
    f'{ARB}.rd_act_m[7:0]',
    f'{ARB}.rd_pre_m[7:0]',
    f'{ARB}.wr_col_m[7:0]',
    f'{ARB}.wr_act_m[7:0]',
    f'{ARB}.wr_pre_m[7:0]',
    f'{ARB}.pool_valid[15:0]',
    f'{ARB}.w_tccd_fwd_ok',
    f'{ARB}.r_tccd_fwd[7:0]',
    f'{ARB}.w_act_gate_live',
    f'{ARB}.w_rd_turn_live',
    f'{ARB}.w_wr_turn_live',
    f'{ARB}.w_guarded[7:0]',
    f'{ARB}.w_prepick_guard[7:0]',
    f'{ARB}.w_col_inflight_bank[7:0]',
    f'{ARB}.w_c_col',
    f'{ARB}.w_c_act',
    f'{ARB}.w_c_pre',
    f'{ARB}.w_sel_rd_col_f',
    f'{ARB}.w_sel_rd_act_f',
    f'{ARB}.w_sel_rd_pre_f',
    f'{ARB}.w_sel_wr_col_f',
    f'{ARB}.w_sel_wr_act_f',
    f'{ARB}.w_sel_wr_pre_f',
    f'{ARB}.rd_col_f',
    f'{ARB}.rd_act_f',
    f'{ARB}.rd_pre_f',
    f'{ARB}.wr_col_f',
    f'{ARB}.wr_act_f',
    f'{ARB}.wr_pre_f',
    f'{ARB}.stall_bp_o[31:0]',
    f'{ARB}.stall_refresh_o[31:0]',
    f'{ARB}.stall_turnaround_o[31:0]',
    f'{ARB}.stall_tccd_o[31:0]',
    f'{ARB}.stall_actlimit_o[31:0]',
    f'{ARB}.stall_banktimer_o[31:0]',
    f'{ARB}.stall_noreq_o[31:0]',
    f'{ARB}.stall_zq_o[31:0]',
]
for b in range(8):
    sigs += [
        f'{BT}.g_bank[{b}].u_bt.r_rcd[7:0]',
        f'{BT}.g_bank[{b}].u_bt.r_ras[7:0]',
        f'{BT}.g_bank[{b}].u_bt.r_rc[7:0]',
        f'{BT}.g_bank[{b}].u_bt.r_rp[7:0]',
        f'{BT}.g_bank[{b}].u_bt.r_preblk[7:0]',
        f'{BT}.g_bank[{b}].u_bt.safe_act_o',
        f'{BT}.g_bank[{b}].u_bt.safe_pre_o',
        f'{BT}.g_bank[{b}].u_bt.safe_rd_o',
        f'{BT}.g_bank[{b}].u_bt.row_valid_o',
    ]

print('loading VCD signals...', file=sys.stderr)
vc = VCDVCD(VCD, signals=sigs, store_tvs=True)
print('loaded', file=sys.stderr)

def tv(name):
    return [(int(t), int(v,2)) for t,v in vc[name].tv]

def val_at(name, t):
    d = vc[name].tv
    idx = 0
    for i in range(len(d)):
        if int(d[i][0]) <= t:
            idx = i
        else:
            break
    return int(d[idx][1], 2) if d else 0

op_tv = tv(f'{SP}.cmd_op_o[4:0]')
valid_tv = tv(f'{SP}.cmd_valid_o')
bank_tv = tv(f'{SP}.cmd_bank_o[2:0]')
row_tv  = tv(f'{SP}.cmd_row_o[12:0]')
col_tv  = tv(f'{SP}.cmd_col_o[9:0]')

fires = []
for t,v in valid_tv:
    if not v:
        continue
    op = val_at(f'{SP}.cmd_op_o[4:0]', t)
    b = val_at(f'{SP}.cmd_bank_o[2:0]', t)
    r = val_at(f'{SP}.cmd_row_o[12:0]', t)
    c = val_at(f'{SP}.cmd_col_o[9:0]', t)
    fires.append((t, op, b, r, c))

print(f'total cmd fires: {len(fires)}', file=sys.stderr)
# show non-init/refresh fires
for f in fires:
    if f[1] in (1,2,3,4,5,6,7):
        print(f[0], OP.get(f[1],f'OP{f[1]}'), f'b{f[2]}', f'r{f[3]}', f'c{f[4]}')
