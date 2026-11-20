#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <deque>

#include "ramulator/base/param.h"
#include "ramulator/controller/controller_base.h"
#include "ramulator/controller/refresh/i_refresh_manager.h"
#include "ramulator/controller/rowpolicy/i_row_policy.h"
#include "ramulator/dram/dram_spec.h"

namespace Ramulator {

// The granite FPGA SKU as a Ramulator controller (memory-controllers MC-018,
// the pick pipeline MC-021).
//
// Not a policy: the shape of granite_core at 225094132 / 593fb5331 -- the
// bank-FIFO store under the bank-pick core (mc_bank_fifo_store + mc_bank_pick)
// -- as far as a cycle-approximate model can carry it. Every term below names
// the RTL term it stands for; the write-up lists the ones it does not carry.
//
//   * One command slot per MC cycle. The controller ticks at CK; the main slot
//     is every slot_ticks-th tick (2: DFI 1:2, the column on phase 0) and the
//     only command the other tick may carry is the row lane's (below). The
//     timing preset is the host's MC-cycle derivation in CK (DDR2 preset
//     DDR2_GRANITE_SKU100), so a constraint measured between two main-slot
//     commands rounds exactly as the RTL's MC-cycle counters do.
//   * The store: one FIFO per (direction, bank) inside a pool of
//     read_buffer_size / write_buffer_size entries (BANK_FIFO_DEPTH 0 = pool
//     admission only); a bank queue may not grow past bank_cap_mixed while the
//     other direction holds entries (BANK_CAP_MIXED, checked at every push as
//     the store does: the beats behind a refused one wait in order); one
//     entry = one BL4 column = one AXI beat. An accepted beat is a head record
//     admit_lag MC cycles later (the push -> bank FIFO -> head record path, 3;
//     ISSUE-004 measured 4 to the REQUEST, whose register is the pipeline's
//     below). The head of each queue is the pick's candidate.
//     peek_depth > 1 lets a bank whose head is a row conflict offer the oldest
//     row hit among its first peek_depth entries instead (MC-016's model of a
//     real lookahead; 1 = the shipped strict FIFO).
//   * THE PICK PIPELINE (mc_bank_pick's three stages, MC-021). Measured in the
//     proxy at 100 MHz (model_knob_grid_2026-11-17.md section 3): a command
//     the next-op hint did not pre-arm fires two MC cycles after its timer
//     opens, ACT -> ACT is t_rrd + 1, two slots go empty after a close-page
//     column pair, the hinted column lands at tRCD. None of that is a lag
//     term; it is the pipeline, so the model carries the pipeline:
//       - DECODE -> REQUEST REGISTER: each pair's head is classified (row hit
//         -> COL; open row + miss -> PRE, withheld while the OTHER direction's
//         head hits the row unless this direction owns the bus with its batch
//         not done, DIR_OWNS_ROWS; closed -> ACT) against the BANK's timer
//         with the lookahead pick_la (the request is raised when the timer
//         opens within pick_la slots, safe_*_la), and lands in a register the
//         select reads NEXT slot. The ACT after an auto-precharge: a head
//         that MISSES the closing row takes the decode's miss branch, whose
//         act lookahead carries the self-close extrapolation (mc_bank_timer
//         LA_AP, on for the bank-pick core) and is armed up to pick_la ahead
//         -- the SKU's drain close; a head that HITS the closing row (close
//         page, the next column of the same row) is classified as a column
//         and blocked until the row image closes, and its ACT is then
//         requested only once its timer is open -- the measured two-slot
//         hop (ap_act_la = true prices the RTL change that would arm it).
//         Rank-level terms (RD <-> WR turnaround, tRRD / tFAW, tCCD) are the
//         fire's (req_bank_timing; ISSUE-004). The row HIT is the head
//         record's flag, classified in the storage plane against the bank
//         timers' REGISTERED row image (one cycle stale by contract) and
//         registered into the record: a bank's heads are classified as hits
//         from hit_lag slots after its ACT (2), so the column request shows
//         at ACT + 3 where the hinted column fires at ACT + 2. Measured on
//         the proxy 72 / 72 (MC-021 step 4, 2026-11-19); the model had read
//         the hit live (ACT + 2), which let a column whose hint a hold had
//         discarded fire at ACT + 3 instead of the RTL's ACT + 5, and the
//         RTL's bank then missed its tRC slot in the four-bank rotation
//         (bank_interleave col_major_bl4: 389 against the board's 351 MB/s).
//       - SELECT -> WINNER REGISTER: from the request registers less the
//         self-stale mask (a pair whose picked / held / fired command cannot
//         be its next request -- a row command, or a column with no same-row
//         entry behind it -- is masked for the fire slot and the slot after;
//         a streaming column is never masked). A rotor from the pair past
//         the effective winner; after a row command columns first, after a
//         column row commands first (the alternation, `alternate`), a
//         rideable row (the lane's candidate set) counting as "after a row".
//         Within the columns: the next-op hint's column, the holding
//         direction's columns, the other direction's when xdir_ok (the holder
//         has no column pending and is not inside its idle hold, DIR_HOLD_IDLE,
//         or its batch is done, DIR_BATCH_MAX), then the hint, then rows;
//         within the rows the hint's row command, then the preferred
//         direction's row commands (the holder's until the batch is done),
//         then the hint, then columns. The winner register loads the HELD
//         winner (a valid, applicable winner whose bank timer opens within
//         pick_la and did not fire, w_hold_next; a column of the other
//         direction yields once the holder has a column pending), else the
//         short-hop SPECULATION on it (a hop shorter than the pipe, t <
//         pick_la, loads the same pair's next class), else the fresh pick.
//       - FIRE: the winner against the LIVE head (its class must still apply:
//         a stale pick costs the slot and is released) and the live timers;
//         an ACT's rank-level ok (tRRD / tFAW) is REGISTERED in
//         mc_global_timers, so the fire sees those two as they stood
//         rank_ok_lag slots earlier. A fire raises the next-op HINT for its
//         pair (ACT -> COL at tRCD, PRE -> ACT at tRP, a last-of-row column
//         without auto-precharge -> PRE at tWR / tRTP) when the hop's timer
//         is within pick_la: the hint is a request of its own class the
//         select reads next slot, so the hinted command fires the slot its
//         timer opens. The direction register (MC-017 form) follows a column
//         of the other direction, flips on "drained" or on the batch cap.
//   * The row lane (DUAL_ISSUE, MC-014): a second winner register, ROW
//     commands only, picked from the same request registers (a row request
//     on a bank with no column request, ACT before PRE, the rotor) and fired
//     beside a main-slot COLUMN fire only, never to the main winner's bank,
//     with the same registered rank ok; it holds while its class applies and
//     its bank opens within the pipe, and its pair is masked from the main
//     select while it holds with a column pending somewhere, the slot after
//     its load and the slot after its fire. It fires on the odd tick
//     (row_phase 1) but is TIMED AT ITS SLOT: the RTL's bank and rank
//     timers are MC-cycle counters that start at the fire's cycle whatever
//     its DFI phase, so a lane ACT in cycle n and a main ACT in cycle n + 2
//     are t_rrd apart to the RTL (3 CK on the wire, which the host's phase
//     margin allows for). The model therefore checks the lane's timing at
//     the slot tick and stamps the DRAM with the slot tick; timing it at the
//     odd tick cost the lane -> main ACT hop one CK, every third ACT under a
//     close-page interleave (bank_interleave col_major bl8: 333 against the
//     board's 387 MB/s; MC-021 step 3, 2026-11-19). lane: 0 off, 1 PRE
//     only, 2 ACT only, 3 either (the SKU).
//   * Auto-precharge (CLOSE_ON_DRAIN): a column closes its row when the entry
//     behind it in its bank queue is not the same row (the store's header
//     bit); page_close makes every column close (the board's close_page).
//     ap_stale = true masks an auto-precharging column's pair as a row
//     command's (the RTL question: the select skipping the stale column
//     class after a close-page column pair). ap_fire_stale (true, the RTL
//     since MC-021 step 4) masks the pair of a column that FIRED with
//     auto-precharge for the slot after its fire, as a row command's pair is;
//     false is the RTL before step 4, which masked only a fired pair whose
//     queue emptied, so the fired pair's leftover column request was live
//     again the cycle after and the rotor, starting past the fired pair,
//     handed it the select before the real column -- a wasted slot, and the
//     pair's fresh ACT request masked from the lane for a cycle (the four-bank
//     close-page rotation at 2.17 cycles per beat for 2.0).
//   * Refresh: the AllBank manager demands REFab every nREFI; while it is
//     pending nothing else fires (the demand block), the open rows close
//     (PREab, where the RTL drains per-bank PREs) and REFab follows.
//   * Not carried (the error bars): the pop shadow (the fire reads the live
//     head, which is the shadow's effect), the write-data fill and the sink /
//     return-ring back-pressure, the age overlay (HAS_AGE with age_thresh 0
//     is inert on the SKU), the hybrid page predictor of the board's
//     `defaults` (modelled as open_page), per-bank refresh PREs, the AXI
//     combiner, and the read-return / host path latency.
class GraniteSKUController : public ControllerBase {
  RAMULATOR_REGISTER_IMPLEMENTATION_DERIVED(IController, GraniteSKUController, ControllerBase, "GraniteSKU")

  // ---- knobs (the SKU's values are the defaults) ----
  int m_slot_ticks = 2;
  int m_bank_cap_mixed = 6;
  bool m_cap_per_beat = true;   // the cap on every beat (the store's push check w_rd_cap_ok / w_wr_cap_ok), not once per AXI burst
  int m_admit_lag = 3;          // MC cycles from a beat's acceptance to its head record (push -> FIFO -> record; the request register is the pipe's)
  bool m_req_bank_timing = true;  // a request needs the BANK's timers only; rank-level terms gate the fire (the RTL decode)
  int m_pick_la = 2;            // LA: the decode's lookahead and the hint's reach, in slots (0 = every hop pays the pipe)
  int m_rank_ok_lag = 0;        // the ACT's rank-level ok seen this many slots late (1 = the N+1 global timers before memory-controllers BUG-004, 2026-11-18)
  bool m_ap_act_la = false;     // the lookahead reaches the ACT of a same-row head after an auto-precharge (measured: no; the RTL question)
  bool m_ap_stale = false;      // an auto-precharging column's pair is self-stale after its pick (the RTL question)
  int m_hit_lag = 2;            // slots after a bank's ACT before the decode sees its heads as row hits (registered row image -> record -> request; 1 = the hit read live)
  int m_wr_fill_lag = 2;        // slots after a WRITE beat lands in its bank queue before it is a head record: the store's write record needs the
                                //   entry's data fill and the fill-done register (h.vld = has0 && r_wr_fdone), the read record only the queue
                                //   (measured: a beat entering an empty write queue is the pick's request 3 cycles after the queue count shows
                                //   it, a read beat 1; memory-controllers MC-021 step 6, 2026-11-19). It binds where a bank's queue runs empty
                                //   between bursts -- the close-page interleaved cells -- and sets the new bank's phase against the others'
  bool m_ap_fire_stale = true;  // the pair of a column that fired with auto-precharge is masked the slot after its fire (the RTL since MC-021 step 4; false = the RTL before, whose leftover column request won the select)
  int m_dir_batch_max = 255;
  int m_dir_hold_idle = 8;
  bool m_dir_owns_rows = true;
  int m_lane = 3;
  bool m_close_on_drain = true;
  bool m_alternate = true;
  bool m_page_close = false;
  int m_peek_depth = 1;
  bool m_debug = false;      // print the slot state and the pick between debug_from and debug_to (CK)
  int m_debug_from = 0;
  int m_debug_to = 0;
  int m_stuck = 0;           // consecutive slots with queued requests and no command: the deadlock detector

  // ---- command ids and MC-cycle hop timers ----
  int m_cmd_act = -1, m_cmd_prepb = -1, m_cmd_rd = -1, m_cmd_wr = -1, m_cmd_rda = -1, m_cmd_wra = -1;
  int m_row_level = -1;
  int m_num_banks = 0;
  int m_t_rcd = 0, m_t_rp = 0, m_t_wr = 0, m_t_rtp = 0, m_t_ccd = 0;   // MC cycles (the host's derivation)
  int m_nRRD = 0, m_nFAW = 0;                                          // CK (the registered rank view)
  int m_la_short = 0;                                                   // LA - 1: a hop this short is the speculation's

  // ---- op classes carried through the pipe ----
  enum Cls { CL_NONE = 0, CL_ACT = 1, CL_COL = 2, CL_PRE = 3 };
  struct Win { bool vld = false; int pair = 0; int cls = CL_NONE; };
  enum Src { SRC_NONE = 0, SRC_HINT, SRC_CDIR, SRC_COL, SRC_ROW };

  // ---- registers ----
  std::vector<bool> m_req;    // [pair] the request register (decoded last slot)
  std::vector<int> m_cls;     // [pair] its class
  std::vector<bool> m_stale;  // [pair] the self-stale mask this slot
  Win m_win;                  // the effective winner the fire stage serves
  Win m_lane_w;               // the row lane's winner
  Win m_hint;                 // the next-op hint (one slot)
  int m_rotor = 0;
  bool m_last_was_row = false;
  bool m_dir = false;         // false = reads hold the bus, true = writes
  int m_batch = 0;            // the holder's columns in this hold
  bool m_batch_done = false;  // registered compare on the next batch value, as the RTL
  bool m_dir_flip = false;    // the direction turned last slot (the leftover rule)
  int m_idle = 0;             // slots since the holder last fired
  bool m_col_more[2] = {false, false};   // a column of this direction fired last slot with a same-row entry behind
  std::vector<bool> m_bank_ap;           // [bank] closed by an auto-precharge (the un-armed ACT hop)
  std::vector<int> m_bank_ap_row;        // [bank] the row that auto-precharge closed
  std::deque<Clk_t> m_act_clks;          // the last ACT issue slots (tRRD / tFAW as the registered ok sees them)
  std::vector<Clk_t> m_bank_act_clk;     // [bank] the slot of the bank's last ACT (the record's hit flag, hit_lag)
  // the lane's fire, waiting for the odd tick
  bool m_lane_pending = false;
  int m_lane_cmd = -1;
  AddrVec_t m_lane_addr;

  // ---- per-slot work ----
  struct Head {
    bool vld = false;
    ReqBuffer::iterator it;
    ReqBuffer* buf = nullptr;
    int cmd = -1;
    bool is_col = false;
    bool behind_vld = false;
    bool behind_same_row = false;
  };
  std::vector<Head> m_heads;      // [2*bank + dir]
  std::vector<Head> m_oldest;     // the strict FIFO head (for the courtesy term when a peek substitutes)

  // ---- stats ----
  size_t s_slots = 0;
  size_t s_main_col = 0;
  size_t s_main_row = 0;
  size_t s_main_maint = 0;
  size_t s_lane_act = 0;
  size_t s_lane_pre = 0;
  size_t s_lane_dropped = 0;
  size_t s_lane_holds = 0;
  size_t s_ap_cols = 0;
  size_t s_dir_flips = 0;
  size_t s_dir_flips_fire = 0;
  size_t s_dir_flips_drain = 0;
  size_t s_dir_flips_cap = 0;
  size_t s_zero_col_turns = 0;
  size_t s_rd_turns = 0;
  size_t s_wr_turns = 0;
  size_t s_cap_refused = 0;
  size_t s_win_holds = 0;     // main slots the winner held on a live timer (class applies, bank opens within the pipe)
  size_t s_rank_ok_holds = 0; // ... of which only the registered rank ok was closed
  size_t s_stale_picks = 0;   // main slots the winner's class no longer applied (a stale pick, released)
  size_t s_hint_picks = 0;    // winners loaded from the hint
  size_t s_spec_loads = 0;    // winners loaded from the short-hop speculation
  size_t s_empty_slots = 0;   // main slots with no winner at all
  size_t s_max_read_latency = 0;
  size_t s_max_write_wait = 0;
  size_t s_hold_slots[2] = {0, 0};   // main slots while reads / writes hold the register
  size_t s_cols[2] = {0, 0};         // read / write columns fired
  size_t s_rows[2] = {0, 0};         // read / write row commands fired from the main slot
  size_t s_xdir_cols = 0;            // columns of the non-holding direction (the register follows each one)

 public:
  void init() override {
    init_base();
    RAMULATOR_PARSE_PARAM(m_slot_ticks, int, "slot_ticks").default_val(2);
    RAMULATOR_PARSE_PARAM(m_bank_cap_mixed, int, "bank_cap_mixed").default_val(6);
    RAMULATOR_PARSE_PARAM(m_cap_per_beat, bool, "cap_per_beat").default_val(true);
    RAMULATOR_PARSE_PARAM(m_admit_lag, int, "admit_lag").default_val(3);
    RAMULATOR_PARSE_PARAM(m_req_bank_timing, bool, "req_bank_timing").default_val(true);
    RAMULATOR_PARSE_PARAM(m_pick_la, int, "pick_la").default_val(2);
    RAMULATOR_PARSE_PARAM(m_rank_ok_lag, int, "rank_ok_lag").default_val(0);
    RAMULATOR_PARSE_PARAM(m_ap_act_la, bool, "ap_act_la").default_val(false);
    RAMULATOR_PARSE_PARAM(m_ap_stale, bool, "ap_stale").default_val(false);
    RAMULATOR_PARSE_PARAM(m_hit_lag, int, "hit_lag").default_val(2);
    RAMULATOR_PARSE_PARAM(m_wr_fill_lag, int, "wr_fill_lag").default_val(2);
    RAMULATOR_PARSE_PARAM(m_ap_fire_stale, bool, "ap_fire_stale").default_val(true);
    RAMULATOR_PARSE_PARAM(m_dir_batch_max, int, "dir_batch_max").default_val(255);
    RAMULATOR_PARSE_PARAM(m_dir_hold_idle, int, "dir_hold_idle").default_val(8);
    RAMULATOR_PARSE_PARAM(m_dir_owns_rows, bool, "dir_owns_rows").default_val(true);
    RAMULATOR_PARSE_PARAM(m_lane, int, "lane").default_val(3);
    RAMULATOR_PARSE_PARAM(m_close_on_drain, bool, "close_on_drain").default_val(true);
    RAMULATOR_PARSE_PARAM(m_alternate, bool, "alternate").default_val(true);
    RAMULATOR_PARSE_PARAM(m_page_close, bool, "page_close").default_val(false);
    RAMULATOR_PARSE_PARAM(m_peek_depth, int, "peek_depth").default_val(1);
    RAMULATOR_PARSE_PARAM(m_debug, bool, "debug").default_val(false);
    RAMULATOR_PARSE_PARAM(m_debug_from, int, "debug_from").default_val(0);
    RAMULATOR_PARSE_PARAM(m_debug_to, int, "debug_to").default_val(0);
    if (m_slot_ticks < 1) throw std::runtime_error("GraniteSKU: slot_ticks must be >= 1");
    if (m_lane < 0 || m_lane > 3) throw std::runtime_error("GraniteSKU: lane must be 0..3");
    if (m_peek_depth < 1) throw std::runtime_error("GraniteSKU: peek_depth must be >= 1");
    if (m_dir_batch_max < 0 || m_dir_batch_max > 255) throw std::runtime_error("GraniteSKU: dir_batch_max is 0..255");
    if (m_admit_lag < 0) throw std::runtime_error("GraniteSKU: admit_lag must be >= 0");
    if (m_pick_la < 0) throw std::runtime_error("GraniteSKU: pick_la must be >= 0");
    if (m_rank_ok_lag < 0) throw std::runtime_error("GraniteSKU: rank_ok_lag must be >= 0");
    if (m_hit_lag < 0) throw std::runtime_error("GraniteSKU: hit_lag must be >= 0");
    if (m_wr_fill_lag < 0) throw std::runtime_error("GraniteSKU: wr_fill_lag must be >= 0");
    const auto& spec = *m_device.m_spec;
    m_cmd_act = spec.get_command_id("ACT");
    m_cmd_prepb = spec.get_command_id("PREpb");
    m_cmd_rd = spec.get_command_id("RD");
    m_cmd_wr = spec.get_command_id("WR");
    m_cmd_rda = spec.get_command_id("RDA");
    m_cmd_wra = spec.get_command_id("WRA");
    m_row_level = spec.get_level_id("Row");
    m_num_banks = static_cast<int>(m_device.m_bank_nodes.size());
    // the host's MC-cycle hop timers from the preset's CK values (ceil, as the host derives them)
    auto mc = [&](int ck) { return (ck + m_slot_ticks - 1) / m_slot_ticks; };
    const int nBL = spec.get_timing_value("nBL");
    m_t_rcd = mc(spec.get_timing_value("nRCD"));
    m_t_rp = mc(spec.get_timing_value("nRP"));
    m_t_wr = mc(spec.get_timing_value("nCWL") + nBL + spec.get_timing_value("nWR"));
    m_t_rtp = mc(nBL + spec.get_timing_value("nRTP") - 2);
    m_t_ccd = mc(spec.get_timing_value("nCCD"));
    m_nRRD = spec.get_timing_value("nRRD");
    m_nFAW = spec.get_timing_value("nFAW");
    m_la_short = m_pick_la > 0 ? m_pick_la - 1 : 0;
    const int np = 2 * m_num_banks;
    m_heads.assign(np, Head{});
    m_oldest.assign(np, Head{});
    m_req.assign(np, false);
    m_cls.assign(np, CL_NONE);
    m_stale.assign(np, false);
    m_bank_ap.assign(m_num_banks, false);
    m_bank_ap_row.assign(m_num_banks, -1);
    m_bank_act_clk.assign(m_num_banks, static_cast<Clk_t>(-(1 << 30)));
  }

  void setup(IFrontEnd* frontend, IMemorySystem* memory_system) override {
    setup_base(frontend, memory_system);
    m_stats.add("sku_slots", s_slots);
    m_stats.add("sku_main_col", s_main_col);
    m_stats.add("sku_main_row", s_main_row);
    m_stats.add("sku_main_maint", s_main_maint);
    m_stats.add("sku_lane_act", s_lane_act);
    m_stats.add("sku_lane_pre", s_lane_pre);
    m_stats.add("sku_lane_dropped", s_lane_dropped);
    m_stats.add("sku_lane_holds", s_lane_holds);
    m_stats.add("sku_ap_cols", s_ap_cols);
    m_stats.add("sku_dir_flips", s_dir_flips);
    m_stats.add("sku_dir_flips_fire", s_dir_flips_fire);
    m_stats.add("sku_dir_flips_drain", s_dir_flips_drain);
    m_stats.add("sku_dir_flips_cap", s_dir_flips_cap);
    m_stats.add("sku_zero_col_turns", s_zero_col_turns);
    m_stats.add("sku_rd_turns", s_rd_turns);
    m_stats.add("sku_wr_turns", s_wr_turns);
    m_stats.add("sku_cap_refused", s_cap_refused);
    m_stats.add("sku_win_holds", s_win_holds);
    m_stats.add("sku_rank_ok_holds", s_rank_ok_holds);
    m_stats.add("sku_stale_picks", s_stale_picks);
    m_stats.add("sku_hint_picks", s_hint_picks);
    m_stats.add("sku_spec_loads", s_spec_loads);
    m_stats.add("sku_empty_slots", s_empty_slots);
    m_stats.add("sku_max_read_latency", s_max_read_latency);
    m_stats.add("sku_max_write_wait", s_max_write_wait);
    m_stats.add("sku_rd_hold_slots", s_hold_slots[0]);
    m_stats.add("sku_wr_hold_slots", s_hold_slots[1]);
    m_stats.add("sku_rd_cols", s_cols[0]);
    m_stats.add("sku_wr_cols", s_cols[1]);
    m_stats.add("sku_rd_rows", s_rows[0]);
    m_stats.add("sku_wr_rows", s_rows[1]);
    m_stats.add("sku_xdir_cols", s_xdir_cols);
  }

  // Admission (the AXI intakes): the request lands in its direction's pool if there is room, and --
  // BANK_CAP_MIXED -- not while its bank queue already holds bank_cap_mixed entries with the other
  // direction holding any. The RTL applies that cap when it takes the AW / AR, i.e. once per AXI
  // BURST, and the burst's remaining beats then enter as the pool has room; the trace carries beats,
  // so a beat contiguous with the last one admitted in its direction (the same burst) is exempt and
  // the cap falls on the first beat of a new burst. No write coalescing and no read forwarding: the
  // board does neither (the controller this inherits from does both, and a wrapped walk trips them),
  // so this is the base's send without those two paths.
  Addr_t m_last_admitted[2] = {-1, -1};
  // Accepted beats on their way to being head records (the store's push -> bank FIFO -> head record
  // path, admit_lag MC cycles): they hold their pool slot and count for the bank cap from the
  // acceptance, and the decode sees them admit_lag slots later (memory-controllers ISSUE-004: with no
  // lag the holder's next burst on a shared bank is always present at its auto-precharge and wins the
  // bank's ACT; the RTL's arrives cycles after the pop and the waiting direction's ACT rides instead).
  struct Staged { Clk_t ready; Request req; };
  std::deque<Staged> m_staged[2];

  bool send(Request& req) override {
    if (req.type_id != Request::Type::Read && req.type_id != Request::Type::Write) {
      throw std::runtime_error("GraniteSKU only accepts Read (0) and Write (1) requests");
    }
    m_addr_mapper->apply(req);
    req.addr_vec[0] = m_channel_id;
    req.final_command = m_device.m_spec->supported_requests[req.type_id];
    const bool is_wr = req.type_id == Request::Type::Write;
    ReqBuffer& own = is_wr ? m_write_buffer : m_read_buffer;
    ReqBuffer& other = is_wr ? m_read_buffer : m_write_buffer;
    const int d = is_wr ? 1 : 0;
    const bool continues_burst = m_last_admitted[d] >= 0 && req.addr == m_last_admitted[d] + m_device.m_spec->get_tx_bytes();
    const int od = 1 - d;
    const size_t other_held = other.size() + m_staged[od].size();
    if (m_bank_cap_mixed > 0 && other_held > 0 && (m_cap_per_beat || !continues_burst)) {
      const int bank = m_device.get_flat_bank_id(req.addr_vec);
      int n = 0;
      for (auto& r : own.buffer) {
        if (m_device.get_flat_bank_id(r.addr_vec) == bank) n++;
      }
      for (auto& st : m_staged[d]) {
        if (m_device.get_flat_bank_id(st.req.addr_vec) == bank) n++;
      }
      if (n >= m_bank_cap_mixed) {
        s_cap_refused++;
        return false;
      }
    }
    if (own.size() + m_staged[d].size() >= own.max_size) {
      return false;
    }
    req.arrive = m_clk;
    req.id = m_next_req_id;
    if (m_admit_lag > 0) {
      m_staged[d].push_back({m_clk + static_cast<Clk_t>(m_admit_lag) * m_slot_ticks, req});
    } else if (!own.enqueue(req)) {
      req.arrive = -1;
      return false;
    }
    m_next_req_id++;
    m_last_admitted[d] = req.addr;
    if (dbg()) std::cout << "[sku] clk " << m_clk << " admit " << (is_wr ? "wr" : "rd") << " bank " << m_device.get_flat_bank_id(req.addr_vec)
                         << " row " << req.addr_vec[m_row_level] << (m_admit_lag > 0 ? " staged" : "") << std::endl;
    if (is_wr) s_num_write_reqs++; else s_num_read_reqs++;
    return true;
  }

  void tick() override {
    tick_prologue();
    m_refresh->tick();
    const bool main_slot = (m_clk % m_slot_ticks) == 0;
    if (!main_slot) {
      fire_lane();
      return;
    }
    m_lane_pending = false;
    s_slots++;
    for (int d = 0; d < 2; d++) {
      ReqBuffer& buf = d ? m_write_buffer : m_read_buffer;
      while (!m_staged[d].empty() && m_staged[d].front().ready <= m_clk) {
        if (!buf.enqueue(m_staged[d].front().req)) {
          throw std::runtime_error("GraniteSKU: a staged beat found no pool slot (the admission reserved one)");
        }
        m_staged[d].pop_front();
      }
    }
    if (dbg()) {
      std::cout << "[sku] clk " << m_clk << " dir " << m_dir << " batch " << m_batch << " idle " << m_idle
                << " rd " << m_read_buffer.size() << " wr " << m_write_buffer.size()
                << " prio " << m_priority_buffer.size() << " pending " << m_pending.size() << std::endl;
    }
    // refresh demanded: drain (PREab) then grant; the demand block holds every demand fire this slot
    bool fire_allowed = true;
    const bool ref_pending = m_priority_buffer.size() > 0;
    if (ref_pending) {
      Candidate cand = pick_priority_if();
      if (cand.valid) {
        issue(cand.it, *cand.buffer);
        s_main_maint++;
        if (dbg()) std::cout << "[sku] clk " << m_clk << " maint cmd " << cand.it->command << std::endl;
      }
      fire_allowed = false;
    }
    schedule_slot(fire_allowed, ref_pending);
  }

 private:
  bool dbg() const { return m_debug && m_clk >= m_debug_from && m_clk < m_debug_to; }
  static int pair_of(int bank, bool dir) { return 2 * bank + (dir ? 1 : 0); }
  static bool dir_of(int pair) { return (pair & 1) != 0; }
  static int bank_of(int pair) { return pair >> 1; }
  static const char* cls_name(int c) { return c == CL_ACT ? "ACT" : c == CL_COL ? "COL" : c == CL_PRE ? "PRE" : "-"; }

  int row_of(const Request& r) const { return r.addr_vec[m_row_level]; }
  int cls_of_cmd(int cmd) const {
    if (cmd == m_cmd_act) return CL_ACT;
    if (cmd == m_cmd_prepb) return CL_PRE;
    return CL_COL;
  }

  // ---- the store's view: one head per (direction, bank) ----
  void build_heads() {
    std::fill(m_heads.begin(), m_heads.end(), Head{});
    std::fill(m_oldest.begin(), m_oldest.end(), Head{});
    const auto& meta = m_device.m_spec->command_meta;
    for (int d = 0; d < 2; d++) {
      ReqBuffer& buf = d ? m_write_buffer : m_read_buffer;
      // pass 1: the strict FIFO head and the entry behind it, in arrival order
      std::vector<int> depth(m_num_banks, 0);
      std::vector<bool> unfilled(m_num_banks, false);
      for (auto it = buf.begin(); it != buf.end(); ++it) {
        const int bank = m_device.get_flat_bank_id(it->addr_vec);
        const int p = pair_of(bank, d);
        Head& h = m_oldest[p];
        if (unfilled[bank]) continue;
        if (!h.vld) {
          // a write beat is a head record only once its data fill and the fill-done register are behind it
          // (wr_fill_lag slots after it lands); until then its pair has no head -- the queue is in order
          if (d == 1 && m_wr_fill_lag > 0 &&
              m_clk < it->arrive + static_cast<Clk_t>(m_admit_lag + m_wr_fill_lag) * m_slot_ticks) {
            unfilled[bank] = true;
            continue;
          }
          h.vld = true;
          h.it = it;
          h.buf = &buf;
        } else if (depth[bank] == 1) {
          h.behind_vld = true;
          h.behind_same_row = row_of(*it) == row_of(*h.it);
        }
        depth[bank]++;
      }
      for (int bank = 0; bank < m_num_banks; bank++) {
        const int p = pair_of(bank, d);
        Head& h = m_oldest[p];
        if (!h.vld) continue;
        h.cmd = get_preq_command(h.it->final_command, h.it->addr_vec);
        h.is_col = meta[h.cmd].is_accessing;
        m_heads[p] = h;
      }
      // pass 2 (peek_depth > 1): a bank whose head is a row conflict offers the
      // oldest row hit among its first peek_depth entries, if no older entry in
      // that window carries the same address.
      if (m_peek_depth > 1) {
        std::vector<int> seen(m_num_banks, 0);
        std::vector<bool> done(m_num_banks, false);
        for (auto it = buf.begin(); it != buf.end(); ++it) {
          const int bank = m_device.get_flat_bank_id(it->addr_vec);
          const int p = pair_of(bank, d);
          seen[bank]++;
          if (seen[bank] == 1 || seen[bank] > m_peek_depth || done[bank]) continue;
          Head& head = m_heads[p];
          if (!meta[head.cmd].is_closing) {
            done[bank] = true;  // a hit, or an ACT on a closed bank: nothing behind it is a hit
            continue;
          }
          const int c = get_preq_command(it->final_command, it->addr_vec);
          if (!meta[c].is_accessing) continue;
          bool blocked = false;
          int k = 0;
          for (auto jt = buf.begin(); jt != it && k < m_peek_depth; ++jt) {
            if (m_device.get_flat_bank_id(jt->addr_vec) != bank) continue;
            k++;
            if (jt->addr == it->addr) { blocked = true; break; }
          }
          if (blocked) continue;
          Head sub = head;
          sub.it = it;
          sub.cmd = c;
          sub.is_col = true;
          sub.behind_vld = true;
          sub.behind_same_row = false;
          m_heads[p] = sub;
          done[bank] = true;
        }
      }
    }
  }

  // ---- timers ----
  // the bank node's own timers (the RTL's per-bank bank_*_ready); rank / channel terms are the fire's
  bool bank_ready_at(int cmd, const AddrVec_t& av, Clk_t clk) {
    return m_device.m_bank_nodes[m_device.get_flat_bank_id(av)]->check_timing(cmd, av, clk);
  }
  // the decode's timer: the bank's (or every timer, req_bank_timing off), open within `la` slots
  bool decode_timer(int cmd, const AddrVec_t& av, int la) {
    const Clk_t at = m_clk + static_cast<Clk_t>(la) * m_slot_ticks;
    return m_req_bank_timing ? bank_ready_at(cmd, av, at) : m_device.check_timing(cmd, av, at);
  }
  // the lookahead the hold reads (bank_*_ready_la): the bank opens within the pipe depth
  bool bank_la_ok(int cmd, const AddrVec_t& av) { return bank_ready_at(cmd, av, m_clk + static_cast<Clk_t>(m_pick_la) * m_slot_ticks); }
  // the registered rank ok for an ACT (mc_global_timers): tRRD / tFAW as they stood rank_ok_lag slots before this slot
  bool rank_ok_registered() const {
    if (m_rank_ok_lag == 0 || m_act_clks.empty()) return true;
    const Clk_t at = m_clk - static_cast<Clk_t>(m_rank_ok_lag) * m_slot_ticks;
    if (m_act_clks.back() + m_nRRD > at) return false;
    if (m_act_clks.size() >= 4 && m_act_clks[m_act_clks.size() - 4] + m_nFAW > at) return false;
    return true;
  }
  void note_act(Clk_t slot) {
    m_act_clks.push_back(slot);
    while (m_act_clks.size() > 4) m_act_clks.pop_front();
  }
  // the record's hit flag: a bank's heads read as row hits from hit_lag slots after its ACT (the bank timers'
  // registered row image, one cycle stale, registered into the head record; the request register is the decode's)
  bool hit_visible(int bank) const {
    return m_clk - m_bank_act_clk[bank] >= static_cast<Clk_t>(m_hit_lag) * m_slot_ticks;
  }

  // round robin from the pair after `from`: the lowest set bit at or above it, else the lowest
  int rr_pick(const std::vector<bool>& set, int from) const {
    const int np = 2 * m_num_banks;
    for (int p = from; p < np; p++) if (set[p]) return p;
    for (int p = 0; p < from; p++) if (set[p]) return p;
    return -1;
  }
  static bool any_of(const std::vector<bool>& v) {
    for (bool b : v) if (b) return true;
    return false;
  }

  // ---- DECODE: next slot's request registers, from this slot's heads and timers ----
  void decode(bool ref_pending, std::vector<bool>& req_nxt, std::vector<int>& cls_nxt) {
    const int np = 2 * m_num_banks;
    for (int p = 0; p < np; p++) {
      req_nxt[p] = false;
      cls_nxt[p] = CL_NONE;
      const Head& h = m_heads[p];
      if (!h.vld) continue;
      const bool d = dir_of(p);
      if (h.is_col) {
        // a hit the record does not show yet is no request at all (the ACT's hinted column fires without one)
        if (hit_visible(bank_of(p)) && decode_timer(h.cmd, h.it->addr_vec, m_pick_la)) { req_nxt[p] = true; cls_nxt[p] = CL_COL; }
      } else if (h.cmd == m_cmd_prepb) {
        // the PRE courtesy: the other direction's head hitting the open row holds the close,
        // unless this direction owns the bus and its batch is not done
        const Head& o = m_oldest[p ^ 1];
        const bool other_hit = o.vld && o.is_col;
        const bool courtesy = !other_hit || (m_dir_owns_rows && d == m_dir && !m_batch_done);
        if (courtesy && decode_timer(h.cmd, h.it->addr_vec, m_pick_la)) { req_nxt[p] = true; cls_nxt[p] = CL_PRE; }
      } else if (h.cmd == m_cmd_act) {
        if (ref_pending) continue;
        // the ACT after an auto-precharge: armed for a head that misses the closed row (the decode's miss
        // branch, LA_AP), requested at the timer for a head of the same row (measured), unless ap_act_la
        const int b = bank_of(p);
        const bool same_row = m_bank_ap[b] && m_bank_ap_row[b] == row_of(*h.it);
        const int la = (same_row && !m_ap_act_la) ? 0 : m_pick_la;
        if (decode_timer(h.cmd, h.it->addr_vec, la)) { req_nxt[p] = true; cls_nxt[p] = CL_ACT; }
      }
    }
  }

  void schedule_slot(bool fire_allowed, bool ref_pending) {
    const int np = 2 * m_num_banks;
    build_heads();
    std::vector<bool> req_nxt(np, false);
    std::vector<int> cls_nxt(np, CL_NONE);
    decode(ref_pending, req_nxt, cls_nxt);

    // ---- the registered request sets the select reads ----
    std::vector<bool> req_ok(np, false), req_col(np, false), req_col_dir(np, false), req_row(np, false);
    bool col_pend[2] = {m_col_more[0], m_col_more[1]}, col_any[2] = {false, false}, row_any[2] = {false, false};
    bool oth_req_any = false;
    const int cur = m_dir ? 1 : 0;
    for (int p = 0; p < np; p++) {
      const int d = dir_of(p) ? 1 : 0;
      const bool is_col = m_cls[p] == CL_COL;
      req_ok[p] = m_req[p] && !m_stale[p];
      req_col[p] = req_ok[p] && is_col;
      req_col_dir[p] = req_col[p] && d == cur;
      req_row[p] = req_ok[p] && !is_col;
      if (m_req[p] && is_col) col_pend[d] = true;        // pending: registered, the stale mask not applied
      if (req_col[p]) col_any[d] = true;
      if (req_row[p]) row_any[d] = true;
      if (m_req[p] && d != cur) oth_req_any = true;
    }
    bool cur_queued = false;
    for (int p = 0; p < np; p++) if (m_heads[p].vld && (dir_of(p) ? 1 : 0) == cur) cur_queued = true;
    const bool hold_idle = m_dir_hold_idle > 0 && cur_queued && m_idle < m_dir_hold_idle;
    const bool xdir_ok = !(col_pend[cur] || hold_idle) || m_batch_done;
    // the row preference: the holder's row commands until the batch is done, then the other's; the test
    // reads the registered requests (an empty preferred class falls through to any row request)
    const int pref_dir = m_batch_done ? 1 - cur : cur;
    bool row_pref_any = false;
    for (int p = 0; p < np; p++) if (m_req[p] && m_cls[p] != CL_COL && (dir_of(p) ? 1 : 0) == pref_dir) row_pref_any = true;
    std::vector<bool> req_row_pref(np, false);
    for (int p = 0; p < np; p++) req_row_pref[p] = req_row[p] && (!row_pref_any || (dir_of(p) ? 1 : 0) == pref_dir);
    // the lane's candidate set: row requests on banks with no column request pending (registers only)
    const bool lane_on = m_lane != 0 && m_slot_ticks >= 2;
    std::vector<bool> lane_cand(np, false);
    bool lane_col_cur = false, lane_col_oth = false;
    if (lane_on) {
      std::vector<bool> bank_busy(m_num_banks, false);
      for (int p = 0; p < np; p++) if (req_ok[p] && m_cls[p] == CL_COL) bank_busy[bank_of(p)] = true;
      for (int p = 0; p < np; p++) {
        if (!req_ok[p]) continue;
        if (m_cls[p] == CL_COL) {
          if ((dir_of(p) ? 1 : 0) == cur) lane_col_cur = true; else lane_col_oth = true;
          continue;
        }
        if (bank_busy[bank_of(p)]) continue;
        if ((m_cls[p] == CL_ACT && (m_lane & 2)) || (m_cls[p] == CL_PRE && (m_lane & 1))) lane_cand[p] = true;
      }
    }
    const bool ride = any_of(lane_cand);
    const bool lane_any_col_ok = lane_col_cur || (lane_col_oth && xdir_ok);
    // the hint is a request of its own class
    const bool hint_is_col = m_hint.cls == CL_COL;
    const int hint_dir = m_hint.vld ? (dir_of(m_hint.pair) ? 1 : 0) : -1;
    const bool hint_ok = m_hint.vld && !(m_batch_done && hint_dir == cur && oth_req_any) &&
                         (!hint_is_col || hint_dir == cur || xdir_ok);

    // ---- FIRE: the winner against the live head and the live timers ----
    const Win W = m_win;
    bool class_ok = false, timers_live = false, timer_ok = false, la_ok = false;
    int live_cmd = -1;
    if (W.vld) {
      const Head& h = m_heads[W.pair];
      if (h.vld) {
        class_ok = (W.cls == CL_COL && h.is_col) || (W.cls == CL_ACT && h.cmd == m_cmd_act && !ref_pending) ||
                   (W.cls == CL_PRE && h.cmd == m_cmd_prepb);
      }
      if (class_ok) {
        live_cmd = h.cmd;
        timers_live = check_timing(h.cmd, h.it->addr_vec);
        timer_ok = timers_live && (h.cmd != m_cmd_act || rank_ok_registered());
        la_ok = bank_la_ok(h.cmd, h.it->addr_vec);
      }
    }
    const bool dmd_fire = fire_allowed && W.vld && class_ok && timer_ok;
    const bool win_xdir_col = W.vld && W.cls == CL_COL && (dir_of(W.pair) ? 1 : 0) != cur && col_pend[cur] && !m_batch_done;
    const bool hold_next = W.vld && class_ok && la_ok && !dmd_fire && !win_xdir_col;
    // the fired candidate's flags, read before the pop
    const bool fired_col = dmd_fire && W.cls == CL_COL;
    const int fired_pair = dmd_fire ? W.pair : -1;
    const int fired_bank = dmd_fire ? bank_of(W.pair) : -1;
    const int fired_dir = dmd_fire ? (dir_of(W.pair) ? 1 : 0) : -1;
    bool w_bsr = false, w_bempty = true, w_hit = false, other_pair_hit = false;
    if (W.vld) {
      const Head& h = m_heads[W.pair];
      w_bsr = h.vld && h.behind_same_row;
      w_bempty = !h.vld || !h.behind_vld;
      w_hit = h.vld && h.is_col;
      const Head& o = m_heads[W.pair ^ 1];
      other_pair_hit = o.vld && o.is_col;
    }
    const bool w_ap_policy = m_page_close || (m_close_on_drain && !w_bsr);
    bool fired_ap = false;
    int fired_cmd = -1;   // the command as issued (the AP variant when it closes)
    if (dmd_fire) {
      const Head& h = m_heads[W.pair];
      fired_cmd = h.cmd;
      if (fired_col && w_ap_policy) {
        const int apc = h.cmd == m_cmd_rd ? m_cmd_rda : m_cmd_wra;
        if (check_timing(apc, h.it->addr_vec)) { fired_cmd = apc; fired_ap = true; }
      }
    }
    // the stats of the fire stage
    s_hold_slots[cur]++;
    if (W.vld && !class_ok) s_stale_picks++;
    else if (fire_allowed && W.vld && class_ok && !dmd_fire) { if (timers_live) s_rank_ok_holds++; else s_win_holds++; }
    else if (!W.vld) s_empty_slots++;

    // ---- the next-op hint from this fire ----
    Win hint_nxt{};
    if (dmd_fire) {
      int t = 255, cls = CL_NONE;
      if (W.cls == CL_ACT) { t = m_t_rcd; cls = CL_COL; }
      else if (W.cls == CL_PRE) { t = m_t_rp; cls = CL_ACT; }
      else if (!fired_ap && !w_bsr && !w_bempty && !other_pair_hit) { t = fired_dir ? m_t_wr : m_t_rtp; cls = CL_PRE; }
      if (cls != CL_NONE && t <= m_pick_la && !(m_pick_la > 0 && t <= m_la_short)) hint_nxt = Win{true, W.pair, cls};
    }
    // ---- the short-hop speculation on the winner (registers only) ----
    Win spec{};
    if (m_pick_la > 0 && W.vld) {
      bool other_req = false;
      for (int p = 0; p < np; p++) if (p != W.pair && req_ok[p]) other_req = true;
      const int t_col_pre = dir_of(W.pair) ? m_t_wr : m_t_rtp;
      if (W.cls == CL_ACT && m_t_rcd <= m_la_short) spec = Win{true, W.pair, CL_COL};
      else if (W.cls == CL_PRE && m_t_rp <= m_la_short) spec = Win{true, W.pair, CL_ACT};
      else if (W.cls == CL_COL && !w_ap_policy && !w_bsr && !w_bempty && !other_pair_hit && t_col_pre <= m_la_short)
        spec = Win{true, W.pair, CL_PRE};
      else if (W.cls == CL_COL && w_bsr && w_hit && !w_ap_policy && m_t_ccd <= m_la_short && !other_req)
        spec = Win{true, W.pair, CL_COL};
    }

    // ---- SELECT: next slot's fresh pick ----
    const int rotor_eff = W.vld ? (W.pair + 1) % np : m_rotor;
    const bool columns_first = !m_alternate || m_last_was_row || ride;
    const std::vector<bool>* sel = nullptr;
    std::vector<bool> hint_vec(np, false);
    if (m_hint.vld) hint_vec[m_hint.pair] = true;
    int src = SRC_NONE;
    if (columns_first) {
      if (hint_ok && hint_is_col)            { sel = &hint_vec; src = SRC_HINT; }
      else if (any_of(req_col_dir))          { sel = &req_col_dir; src = SRC_CDIR; }
      else if (any_of(req_col) && xdir_ok)   { sel = &req_col; src = SRC_COL; }
      else if (hint_ok)                      { sel = &hint_vec; src = SRC_HINT; }
      else                                   { sel = &req_row_pref; src = SRC_ROW; }
    } else {
      if (hint_ok && !hint_is_col)           { sel = &hint_vec; src = SRC_HINT; }
      else if (any_of(req_row))              { sel = &req_row_pref; src = SRC_ROW; }
      else if (hint_ok)                      { sel = &hint_vec; src = SRC_HINT; }
      else if (any_of(req_col_dir))          { sel = &req_col_dir; src = SRC_CDIR; }
      else if (xdir_ok)                      { sel = &req_col; src = SRC_COL; }
    }
    int pick_pair = sel ? rr_pick(*sel, rotor_eff) : -1;
    const bool pick_vld = pick_pair >= 0;
    int pick_cls = CL_NONE;
    if (pick_vld) {
      pick_cls = src == SRC_ROW ? m_cls[pick_pair] : src == SRC_HINT ? m_hint.cls : CL_COL;
      if (hint_ok && *sel == hint_vec) pick_cls = m_hint.cls;
    }
    // the lane's pick: ACT before PRE, the rotor inside the class
    int lane_pick = -1;
    if (lane_on) {
      std::vector<bool> act_set(np, false), pre_set(np, false);
      bool any_act = false;
      for (int p = 0; p < np; p++) {
        if (!lane_cand[p]) continue;
        if (m_cls[p] == CL_ACT) { act_set[p] = true; any_act = true; } else pre_set[p] = true;
      }
      lane_pick = rr_pick(any_act ? act_set : pre_set, rotor_eff);
    }

    // ---- the lane's fire: beside this slot's column fire, never to the main winner's bank ----
    const Win L = m_lane_w;
    bool l_class_ok = false, l_timer_ok = false, l_la_ok = false;
    const bool l_clash = W.vld && L.vld && bank_of(L.pair) == bank_of(W.pair);
    if (lane_on && L.vld) {
      const Head& h = m_heads[L.pair];
      if (h.vld) {
        l_class_ok = (L.cls == CL_ACT && h.cmd == m_cmd_act && !ref_pending) || (L.cls == CL_PRE && h.cmd == m_cmd_prepb);
      }
      if (l_class_ok) {
        // at the slot tick, not the odd tick it fires on: the RTL's counters see the cycle, not the phase
        l_timer_ok = m_device.check_timing(h.cmd, h.it->addr_vec, m_clk) && (h.cmd != m_cmd_act || rank_ok_registered());
        l_la_ok = bank_la_ok(h.cmd, h.it->addr_vec);
      }
    }
    const bool l_ok = lane_on && L.vld && l_class_ok && !l_clash;
    const bool l_fire = l_ok && l_timer_ok && fired_col;
    const bool l_hold = l_ok && !l_fire && l_la_ok;
    Win lane_hint{};
    if (l_fire) {
      const Head& h = m_heads[L.pair];
      m_lane_pending = true;
      m_lane_cmd = h.cmd;
      m_lane_addr = h.it->addr_vec;
      if (!h.it->is_stat_updated) { ReqBuffer::iterator it = h.it; update_request_stats(it); }
      if (L.cls == CL_ACT) {
        note_act(m_clk);
        m_bank_ap[bank_of(L.pair)] = false;
        m_bank_act_clk[bank_of(L.pair)] = m_clk;
        if (m_t_rcd <= m_pick_la && !(m_pick_la > 0 && m_t_rcd <= m_la_short)) lane_hint = Win{true, L.pair, CL_COL};
      } else if (m_t_rp <= m_pick_la && !(m_pick_la > 0 && m_t_rp <= m_la_short)) {
        lane_hint = Win{true, L.pair, CL_ACT};
      }
    } else if (l_hold) {
      s_lane_holds++;
    }

    if (dbg()) {
      std::cout << "[sku]   depth";
      for (int b = 0; b < m_num_banks; b++) {
        int n[2] = {0, 0};
        for (int d = 0; d < 2; d++) for (auto& r : (d ? m_write_buffer : m_read_buffer).buffer) if (m_device.get_flat_bank_id(r.addr_vec) == b) n[d]++;
        std::cout << " " << n[0] << "/" << n[1];
      }
      std::cout << " staged " << m_staged[0].size() << "/" << m_staged[1].size() << std::endl;
      std::cout << "[sku]   req:";
      for (int p = 0; p < np; p++) if (m_req[p]) std::cout << " p" << p << cls_name(m_cls[p]) << (m_stale[p] ? "*" : "");
      std::cout << " | win " << (W.vld ? std::to_string(W.pair) + cls_name(W.cls) : "-")
                << (W.vld ? (class_ok ? (dmd_fire ? " FIRE" : hold_next ? " hold" : " wait") : " stale") : "")
                << " | pick " << (pick_vld ? std::to_string(pick_pair) + cls_name(pick_cls) : "-") << " src " << src
                << (spec.vld ? " spec" : "") << " colfirst " << columns_first << " ride " << ride
                << " | lane " << (L.vld ? std::to_string(L.pair) + cls_name(L.cls) : "-")
                << (l_fire ? " FIRE" : l_hold ? " hold" : "") << " lpick " << lane_pick
                << " | hint " << (m_hint.vld ? std::to_string(m_hint.pair) + cls_name(m_hint.cls) : "-") << std::endl;
    }

    // ---- next state: the winner, the stale mask, the lane, the hint ----
    Win win_nxt;
    if (hold_next) win_nxt = W;
    else if (spec.vld) { win_nxt = spec; s_spec_loads++; }
    else { win_nxt = Win{pick_vld, pick_vld ? pick_pair : 0, pick_cls}; if (pick_vld && src == SRC_HINT) s_hint_picks++; }
    std::vector<bool> stale_nxt(np, false);
    auto stale_if = [&](int p, int cls) {
      const Head& h = m_heads[p];
      const bool bsr = h.vld && h.behind_same_row;
      const bool ap = m_ap_stale && cls == CL_COL && (m_page_close || (m_close_on_drain && !bsr));
      return cls != CL_COL || !bsr || ap;
    };
    if (hold_next) { if (stale_if(W.pair, W.cls)) stale_nxt[W.pair] = true; }
    else if (spec.vld) { if (stale_if(W.pair, spec.cls)) stale_nxt[W.pair] = true; }
    else if (pick_vld && stale_if(pick_pair, pick_cls)) stale_nxt[pick_pair] = true;
    if (fired_col && (w_bempty || (m_ap_fire_stale && fired_ap))) stale_nxt[fired_pair] = true;
    Win lane_nxt{};
    if (l_hold) {
      lane_nxt = L;
      if (lane_any_col_ok) stale_nxt[L.pair] = true;
    } else if (lane_pick >= 0) {
      lane_nxt = Win{true, lane_pick, m_cls[lane_pick]};
      stale_nxt[lane_pick] = true;
    }
    if (l_fire) stale_nxt[L.pair] = true;
    const Win hint_reg = hint_nxt.vld ? hint_nxt : lane_hint;

    // ---- the direction register ----
    bool dir_nxt = m_dir;
    int batch_nxt = m_batch;
    int cause = -1;
    const bool win_row_cur = W.vld && W.cls != CL_COL && (dir_of(W.pair) ? 1 : 0) == cur;
    if (fired_col && fired_dir != cur && m_dir_flip) {
      // the leftover fires: the pick made before the flip; the direction and its batch stand
    } else if (fired_col && fired_dir != cur) {
      dir_nxt = fired_dir == 1; batch_nxt = 1; cause = 0;
    } else if (!col_pend[cur] && col_any[1 - cur] && !hold_idle && !(row_any[cur] || win_row_cur)) {
      dir_nxt = !m_dir; batch_nxt = 0; cause = 1;
    } else if (m_batch_done && col_any[1 - cur]) {
      dir_nxt = !m_dir; batch_nxt = 0; cause = 2;
    } else if (fired_col && m_batch < 255) {
      batch_nxt = m_batch + 1;
    }
    const bool flip = dir_nxt != m_dir;
    if (flip) {
      if (m_debug) {
        std::cout << "[sku] clk " << m_clk << " FLIP cause " << cause << " from dir " << m_dir << " batch " << m_batch
                  << " rd " << m_read_buffer.size() << " wr " << m_write_buffer.size() << std::endl;
      }
      s_dir_flips++;
      if (cause == 0) s_dir_flips_fire++;
      else if (cause == 1) s_dir_flips_drain++;
      else s_dir_flips_cap++;
      if (m_batch == 0) s_zero_col_turns++;
      if (m_dir) s_wr_turns++; else s_rd_turns++;
    }

    // ---- the fire itself (pops the head: nothing above reads the heads after this) ----
    if (dmd_fire) {
      Head& h = m_heads[W.pair];
      h.it->command = fired_cmd;
      if (fired_col) {
        if (fired_ap) { h.it->final_command = fired_cmd; s_ap_cols++; }
        s_main_col++;
        s_cols[fired_dir]++;
        if (fired_dir != cur) s_xdir_cols++;
        m_bank_ap[fired_bank] = fired_ap;
        if (fired_ap) m_bank_ap_row[fired_bank] = row_of(*h.it);
      } else {
        s_main_row++;
        s_rows[fired_dir]++;
        if (W.cls == CL_ACT) { note_act(m_clk); m_bank_ap[fired_bank] = false; m_bank_act_clk[fired_bank] = m_clk; }
      }
      if (dbg()) std::cout << "[sku]   fire p" << W.pair << " cmd " << fired_cmd << (fired_ap ? " AP" : "") << std::endl;
      issue(h.it, *h.buf);
    }

    // ---- commit the registers ----
    m_req = req_nxt;
    m_cls = cls_nxt;
    m_stale = stale_nxt;
    m_win = win_nxt;
    m_lane_w = lane_nxt;
    m_hint = hint_reg;
    if (dmd_fire) { m_last_was_row = !fired_col; m_rotor = (fired_pair + 1) % np; }
    m_col_more[0] = fired_col && fired_dir == 0 && w_bsr;
    m_col_more[1] = fired_col && fired_dir == 1 && w_bsr;
    m_dir = dir_nxt;
    m_dir_flip = flip;
    m_batch = batch_nxt;
    m_batch_done = m_dir_batch_max != 0 && batch_nxt >= m_dir_batch_max;
    bump_idle(flip || (dmd_fire && fired_dir == cur));
    // deadlock detector: queued requests and no command for 4096 slots is a modelling error, not a stall
    if (dmd_fire || (m_read_buffer.size() + m_write_buffer.size() + m_staged[0].size() + m_staged[1].size()) == 0) {
      m_stuck = 0;
    } else if (++m_stuck > 4096) {
      std::string msg = "GraniteSKU: no command for 4096 slots with requests queued at clk " + std::to_string(m_clk) +
                        " (dir " + std::to_string(m_dir) + " batch " + std::to_string(m_batch) + " idle " +
                        std::to_string(m_idle) + " last_was_row " + std::to_string(m_last_was_row) + " win " +
                        (m_win.vld ? std::to_string(m_win.pair) + cls_name(m_win.cls) : "-") + ") req:";
      for (int p = 0; p < np; p++) if (m_req[p]) msg += " p" + std::to_string(p) + cls_name(m_cls[p]) + (m_stale[p] ? "*" : "");
      msg += " heads:";
      for (int p = 0; p < np; p++) if (m_heads[p].vld) msg += " p" + std::to_string(p) + "(cmd " + std::to_string(m_heads[p].cmd) + ")";
      throw std::runtime_error(msg);
    }
  }

  void bump_idle(bool reset) {
    if (reset) m_idle = 0;
    else if (m_idle < 255) m_idle++;
  }

  // the lane's command on the odd tick, timed at its slot (the pick checked the slot tick; the main
  // column that fired beside it cannot close an ACT's or a PRE's timers, so the re-check is a guard).
  // The DRAM is stamped with the slot tick: the RTL's per-cycle counters start there, and every hop
  // from this command (tRRD / tFAW to the next ACT, tRCD to its column, tRP after a PRE) is then the
  // RTL's count of MC cycles, as the main slot's commands already are.
  void fire_lane() {
    if (!m_lane_pending) return;
    m_lane_pending = false;
    const Clk_t slot_clk = m_clk - (m_clk % m_slot_ticks);
    if (!check_timing(m_lane_cmd, m_lane_addr)) {
      s_lane_dropped++;
      return;
    }
    m_device.issue_command(m_lane_cmd, m_lane_addr, slot_clk);
    if (dbg()) std::cout << "[sku] clk " << m_clk << " lane cmd " << m_lane_cmd << " bank " << m_device.get_flat_bank_id(m_lane_addr) << std::endl;
    if (m_lane_cmd == m_cmd_act) s_lane_act++; else s_lane_pre++;
  }

  // issue the request's current command; retire it if that was its last
  void issue(ReqBuffer::iterator it, ReqBuffer& buffer) {
    if (!it->is_stat_updated) update_request_stats(it);
    m_device.issue_command(it->command, it->addr_vec, m_clk);
    if (it->command == it->final_command) {
      if (it->type_id == Request::Type::Read) {
        const size_t lat = static_cast<size_t>(m_clk + m_device.m_spec->read_latency - it->arrive);
        if (lat > s_max_read_latency) s_max_read_latency = lat;
      } else if (it->type_id == Request::Type::Write) {
        const size_t wait = static_cast<size_t>(m_clk - it->arrive);
        if (wait > s_max_write_wait) s_max_write_wait = wait;
      }
      retire_request(it, buffer);
    }
  }
};

}  // namespace Ramulator
