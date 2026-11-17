#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "ramulator/base/param.h"
#include "ramulator/controller/controller_base.h"
#include "ramulator/controller/refresh/i_refresh_manager.h"
#include "ramulator/controller/rowpolicy/i_row_policy.h"
#include "ramulator/dram/dram_spec.h"

namespace Ramulator {

// The granite FPGA SKU as a Ramulator controller (memory-controllers MC-018).
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
//     other direction holds entries (BANK_CAP_MIXED); one entry = one BL4
//     column = one AXI beat. The head of each queue is the pick's candidate.
//     peek_depth > 1 lets a bank whose head is a row conflict offer the oldest
//     row hit among its first peek_depth entries instead (MC-016's model of a
//     real lookahead; 1 = the shipped strict FIFO).
//   * DECODE per head: row hit -> column; open row + miss -> PRE, withheld
//     while the OTHER direction's head on the bank hits the open row unless
//     this direction holds the bus and its batch is not done (DIR_OWNS_ROWS);
//     closed -> ACT, blocked while a refresh is demanded.
//   * SELECT: a rotor over pairs p = 2*bank + dir from the last winner; after
//     a row command columns first, after a column row commands first (the
//     alternation, `alternate`), the row lane turning "a row can ride" into
//     "after a row". Columns of the direction holding the register first,
//     the other direction's only when xdir_ok: the holder has no pending
//     column and is not inside its idle hold (DIR_HOLD_IDLE), or its batch is
//     done (DIR_BATCH_MAX). Row commands prefer the holder's until the batch
//     is done, then the other direction's; an empty preferred class falls
//     through to any row request (the lane-off form of the lane, MC-017).
//   * The direction register (MC-017 form): follows a column of the other
//     direction; flips on "drained" (no pending column of the holder, a ready
//     column of the other, no row request or row winner of the holder, not
//     inside the idle hold) or on the batch cap with a ready column waiting;
//     counts the holder's columns otherwise.
//   * The row lane (DUAL_ISSUE, MC-014): beside a main-slot COLUMN, one ACT or
//     PRE to a bank with no pending column request, not the column's bank,
//     ACT before PRE, the rotor inside the class; it fires on the odd tick
//     (row_phase 1) if its timing holds there, else it is dropped (the RTL
//     holds and re-presents; the decode re-offers it here next slot).
//     lane: 0 off, 1 PRE only, 2 ACT only, 3 either (the SKU).
//   * Auto-precharge (CLOSE_ON_DRAIN): a column closes its row when the entry
//     behind it in its bank queue is not the same row (the store's header
//     bit); page_close makes every column close (the board's close_page).
//   * Refresh: the AllBank manager demands REFab every nREFI; while it is
//     pending nothing else issues, the open rows close (PREab, where the RTL
//     drains per-bank PREs) and REFab follows -- the drain-then-grant shape.
//   * Not carried (the error bars): the two-stage decode -> fire pipeline and
//     its lookahead / next-op hint, the pop shadow, the write-data fill and
//     the sink / return-ring back-pressure, the age overlay (HAS_AGE with
//     age_thresh 0 is inert on the SKU), the hybrid page predictor of the
//     board's `defaults` (modelled as open_page: the two differ by < 1
//     percent on every 2026-11-16 cell), per-bank refresh PREs, the AXI
//     combiner, and the read-return / host path latency.
class GraniteSKUController : public ControllerBase {
  RAMULATOR_REGISTER_IMPLEMENTATION_DERIVED(IController, GraniteSKUController, ControllerBase, "GraniteSKU")

  // ---- knobs (the SKU's values are the defaults) ----
  int m_slot_ticks = 2;
  int m_bank_cap_mixed = 6;
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

  // ---- command ids ----
  int m_cmd_act = -1, m_cmd_prepb = -1, m_cmd_rd = -1, m_cmd_wr = -1, m_cmd_rda = -1, m_cmd_wra = -1;
  int m_row_level = -1;
  int m_num_banks = 0;

  // ---- registers ----
  bool m_dir = false;        // false = reads hold the bus, true = writes
  int m_batch = 0;           // the holder's columns in this hold
  bool m_batch_done = false; // registered compare on the next batch value, as the RTL
  int m_idle = 0;            // slots since the holder last fired
  bool m_last_was_row = false;
  int m_rotor = -1;          // last winning pair
  // the lane's pick, waiting for the odd tick
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
    bool behind_same_row = false;
    bool req = false;   // ready and allowed this slot
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
  size_t s_ap_cols = 0;
  size_t s_dir_flips = 0;
  size_t s_dir_flips_fire = 0;
  size_t s_dir_flips_drain = 0;
  size_t s_dir_flips_cap = 0;
  size_t s_zero_col_turns = 0;
  size_t s_rd_turns = 0;
  size_t s_wr_turns = 0;
  size_t s_cap_refused = 0;
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
    const auto& spec = *m_device.m_spec;
    m_cmd_act = spec.get_command_id("ACT");
    m_cmd_prepb = spec.get_command_id("PREpb");
    m_cmd_rd = spec.get_command_id("RD");
    m_cmd_wr = spec.get_command_id("WR");
    m_cmd_rda = spec.get_command_id("RDA");
    m_cmd_wra = spec.get_command_id("WRA");
    m_row_level = spec.get_level_id("Row");
    m_num_banks = static_cast<int>(m_device.m_bank_nodes.size());
    m_heads.assign(2 * m_num_banks, Head{});
    m_oldest.assign(2 * m_num_banks, Head{});
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
    m_stats.add("sku_ap_cols", s_ap_cols);
    m_stats.add("sku_dir_flips", s_dir_flips);
    m_stats.add("sku_dir_flips_fire", s_dir_flips_fire);
    m_stats.add("sku_dir_flips_drain", s_dir_flips_drain);
    m_stats.add("sku_dir_flips_cap", s_dir_flips_cap);
    m_stats.add("sku_zero_col_turns", s_zero_col_turns);
    m_stats.add("sku_rd_turns", s_rd_turns);
    m_stats.add("sku_wr_turns", s_wr_turns);
    m_stats.add("sku_cap_refused", s_cap_refused);
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
    if (m_bank_cap_mixed > 0 && other.size() > 0 && !continues_burst) {
      const int bank = m_device.get_flat_bank_id(req.addr_vec);
      int n = 0;
      for (auto& r : own.buffer) {
        if (m_device.get_flat_bank_id(r.addr_vec) == bank) n++;
      }
      if (n >= m_bank_cap_mixed) {
        s_cap_refused++;
        return false;
      }
    }
    req.arrive = m_clk;
    req.id = m_next_req_id;
    if (!own.enqueue(req)) {
      req.arrive = -1;
      return false;
    }
    m_next_req_id++;
    m_last_admitted[d] = req.addr;
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
    if (m_debug && m_clk >= m_debug_from && m_clk < m_debug_to) {
      std::cout << "[sku] clk " << m_clk << " dir " << m_dir << " batch " << m_batch << " idle " << m_idle
                << " rd " << m_read_buffer.size() << " wr " << m_write_buffer.size()
                << " prio " << m_priority_buffer.size() << " pending " << m_pending.size() << std::endl;
    }
    if (m_priority_buffer.size() > 0) {
      // refresh demanded: drain (PREab) then grant; nothing else this slot
      Candidate cand = pick_priority_if();
      if (cand.valid) {
        issue(cand.it, *cand.buffer);
        s_main_maint++;
        if (m_debug && m_clk >= m_debug_from && m_clk < m_debug_to) {
          std::cout << "[sku] clk " << m_clk << " maint cmd " << cand.it->command << std::endl;
        }
      }
      bump_idle(false);
      return;
    }
    schedule_slot();
  }

 private:
  static int pair_of(int bank, bool dir) { return 2 * bank + (dir ? 1 : 0); }
  static bool dir_of(int pair) { return (pair & 1) != 0; }
  static int bank_of(int pair) { return pair >> 1; }

  int row_of(const Request& r) const { return r.addr_vec[m_row_level]; }

  // ---- the store's view: one head per (direction, bank) ----
  void build_heads() {
    std::fill(m_heads.begin(), m_heads.end(), Head{});
    std::fill(m_oldest.begin(), m_oldest.end(), Head{});
    const auto& meta = m_device.m_spec->command_meta;
    for (int d = 0; d < 2; d++) {
      ReqBuffer& buf = d ? m_write_buffer : m_read_buffer;
      // pass 1: the strict FIFO head and the entry behind it, in arrival order
      std::vector<int> depth(m_num_banks, 0);
      for (auto it = buf.begin(); it != buf.end(); ++it) {
        const int bank = m_device.get_flat_bank_id(it->addr_vec);
        const int p = pair_of(bank, d);
        Head& h = m_oldest[p];
        if (!h.vld) {
          h.vld = true;
          h.it = it;
          h.buf = &buf;
        } else if (depth[bank] == 1) {
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
          sub.behind_same_row = false;
          m_heads[p] = sub;
          done[bank] = true;
        }
      }
    }
  }

  // ---- DECODE: which heads request this slot ----
  void decode(bool ref_pending) {
    for (int p = 0; p < 2 * m_num_banks; p++) {
      Head& h = m_heads[p];
      if (!h.vld) continue;
      const bool d = dir_of(p);
      bool ok = check_timing(h.cmd, h.it->addr_vec);
      if (h.cmd == m_cmd_act) {
        ok = ok && !ref_pending;
      } else if (h.cmd == m_cmd_prepb) {
        // the PRE courtesy: the other direction's head hitting the open row holds the close,
        // unless this direction owns the bus and its batch is not done
        const Head& o = m_oldest[p ^ 1];
        const bool other_hit = o.vld && o.is_col;
        ok = ok && (!other_hit || (m_dir_owns_rows && d == m_dir && !m_batch_done));
      }
      h.req = ok;
    }
  }

  // round robin from the pair after the last winner
  int rotor_pick(const std::vector<bool>& set) const {
    const int np = 2 * m_num_banks;
    for (int k = 1; k <= np; k++) {
      const int p = (m_rotor + k) % np;
      if (set[p]) return p;
    }
    return -1;
  }

  void schedule_slot() {
    const int np = 2 * m_num_banks;
    build_heads();
    decode(false);

    // the direction terms (MC-017 form)
    bool col_pend[2] = {false, false}, col_any[2] = {false, false}, row_any[2] = {false, false};
    for (int p = 0; p < np; p++) {
      const Head& h = m_heads[p];
      if (!h.vld) continue;
      const int d = dir_of(p) ? 1 : 0;
      if (h.is_col) {
        col_pend[d] = true;
        if (h.req) col_any[d] = true;
      } else if (h.req) {
        row_any[d] = true;
      }
    }
    const int cur = m_dir ? 1 : 0;
    const bool cur_queued = (m_dir ? m_write_buffer : m_read_buffer).size() > 0;
    const bool hold_idle = m_dir_hold_idle > 0 && cur_queued && m_idle < m_dir_hold_idle;
    const bool xdir_ok = !(col_pend[cur] || hold_idle) || m_batch_done;

    // class sets
    std::vector<bool> col_dir(np, false), col_all(np, false), row_pref(np, false), row_all(np, false);
    const bool pref_dir = m_batch_done ? !m_dir : m_dir;
    bool any_col_dir = false, any_col_all = false, any_row_pref = false, any_row_all = false;
    for (int p = 0; p < np; p++) {
      const Head& h = m_heads[p];
      if (!h.vld || !h.req) continue;
      if (h.is_col) {
        col_all[p] = true;
        any_col_all = true;
        if (dir_of(p) == m_dir) { col_dir[p] = true; any_col_dir = true; }
      } else {
        row_all[p] = true;
        any_row_all = true;
        if (dir_of(p) == pref_dir) { row_pref[p] = true; any_row_pref = true; }
      }
    }
    const std::vector<bool>& rows = any_row_pref ? row_pref : row_all;
    const bool any_rows = any_row_pref || any_row_all;

    // the lane's candidates: row requests on banks with no PENDING column request
    std::vector<bool> lane_act(np, false), lane_pre(np, false);
    bool any_lane_act = false, any_lane_pre = false;
    const bool lane_on = m_lane != 0 && m_slot_ticks >= 2;
    if (lane_on) {
      for (int p = 0; p < np; p++) {
        const Head& h = m_heads[p];
        if (!h.vld || !h.req || h.is_col) continue;
        const int b = bank_of(p);
        const bool busy = (m_heads[pair_of(b, false)].vld && m_heads[pair_of(b, false)].is_col) ||
                          (m_heads[pair_of(b, true)].vld && m_heads[pair_of(b, true)].is_col);
        if (busy) continue;
        if (h.cmd == m_cmd_act && (m_lane & 2)) { lane_act[p] = true; any_lane_act = true; }
        if (h.cmd == m_cmd_prepb && (m_lane & 1)) { lane_pre[p] = true; any_lane_pre = true; }
      }
    }
    const bool ride = any_lane_act || any_lane_pre;

    // SELECT
    int win = -1;
    const bool columns_first = !m_alternate || m_last_was_row || ride;
    if (columns_first) {
      if (any_col_dir) win = rotor_pick(col_dir);
      else if (any_col_all && xdir_ok) win = rotor_pick(col_all);
      else if (any_rows) win = rotor_pick(rows);
    } else {
      if (any_rows) win = rotor_pick(rows);
      else if (any_col_dir) win = rotor_pick(col_dir);
      else if (any_col_all && xdir_ok) win = rotor_pick(col_all);
    }

    bool fired = false, fired_col = false, fired_dir = false;
    int fired_bank = -1;
    s_hold_slots[m_dir ? 1 : 0]++;
    if (m_debug && m_clk >= m_debug_from && m_clk < m_debug_to) {
      std::cout << "[sku]   heads:";
      for (int p = 0; p < np; p++) {
        const Head& h = m_heads[p];
        if (h.vld) std::cout << " p" << p << "(cmd " << h.cmd << (h.req ? " rdy" : " wait") << ")";
      }
      std::cout << " win " << win << " ride " << ride << " colfirst " << columns_first << std::endl;
    }
    if (win >= 0) {
      Head& h = m_heads[win];
      fired = true;
      fired_col = h.is_col;
      fired_dir = dir_of(win);
      fired_bank = bank_of(win);
      if (fired_col) {
        const bool ap = m_page_close || (m_close_on_drain && !h.behind_same_row);
        if (ap) {
          const int apc = h.cmd == m_cmd_rd ? m_cmd_rda : m_cmd_wra;
          if (check_timing(apc, h.it->addr_vec)) {
            h.it->command = apc;
            h.it->final_command = apc;
            s_ap_cols++;
          } else {
            h.it->command = h.cmd;
          }
        } else {
          h.it->command = h.cmd;
        }
        s_main_col++;
        s_cols[fired_dir ? 1 : 0]++;
        if (fired_dir != m_dir) s_xdir_cols++;
      } else {
        h.it->command = h.cmd;
        s_main_row++;
        s_rows[fired_dir ? 1 : 0]++;
      }
      m_rotor = win;
      issue(h.it, *h.buf);
    }

    // the lane, beside a column, not the column's bank
    if (fired && fired_col && ride) {
      const std::vector<bool>& set = any_lane_act ? lane_act : lane_pre;
      std::vector<bool> masked = set;
      masked[pair_of(fired_bank, false)] = false;
      masked[pair_of(fired_bank, true)] = false;
      bool any = false;
      for (bool b : masked) any = any || b;
      if (any) {
        const int lp = rotor_pick(masked);
        const Head& lh = m_heads[lp];
        m_lane_pending = true;
        m_lane_cmd = lh.cmd;
        m_lane_addr = lh.it->addr_vec;
        if (!lh.it->is_stat_updated) {
          ReqBuffer::iterator it = lh.it;
          update_request_stats(it);
        }
      }
    }

    // the direction register
    const bool oth_col_any = col_any[1 - cur];
    bool flip = false;
    int cause = -1;
    if (fired_col && fired_dir != m_dir) {
      flip = true; cause = 0;
    } else if (!col_pend[cur] && oth_col_any && !hold_idle &&
               !(row_any[cur] || (fired && !fired_col && fired_dir == m_dir))) {
      flip = true; cause = 1;
    } else if (m_batch_done && oth_col_any) {
      flip = true; cause = 2;
    }
    int batch_nxt = m_batch;
    if (flip) {
      s_dir_flips++;
      if (cause == 0) s_dir_flips_fire++;
      else if (cause == 1) s_dir_flips_drain++;
      else s_dir_flips_cap++;
      if (m_batch == 0) s_zero_col_turns++;
      if (m_dir) s_wr_turns++; else s_rd_turns++;
      m_dir = !m_dir;
      batch_nxt = cause == 0 ? 1 : 0;
    } else if (fired_col && m_batch < 255) {
      batch_nxt = m_batch + 1;
    }
    m_batch = batch_nxt;
    m_batch_done = m_dir_batch_max != 0 && batch_nxt >= m_dir_batch_max;
    bump_idle(flip || (fired && fired_dir == m_dir));
    if (fired) m_last_was_row = !fired_col;
    // deadlock detector: queued requests and no command for 4096 slots is a modelling error, not a stall
    if (fired || (m_read_buffer.size() + m_write_buffer.size()) == 0) {
      m_stuck = 0;
    } else if (++m_stuck > 4096) {
      std::string msg = "GraniteSKU: no command for 4096 slots with requests queued at clk " + std::to_string(m_clk) +
                        " (dir " + std::to_string(m_dir) + " batch " + std::to_string(m_batch) + " idle " +
                        std::to_string(m_idle) + " last_was_row " + std::to_string(m_last_was_row) + ") heads:";
      for (int p = 0; p < np; p++) {
        const Head& h = m_heads[p];
        if (h.vld) msg += " p" + std::to_string(p) + "(cmd " + std::to_string(h.cmd) + (h.req ? " rdy" : " wait") + ")";
      }
      throw std::runtime_error(msg);
    }
  }

  void bump_idle(bool reset) {
    if (reset) m_idle = 0;
    else if (m_idle < 255) m_idle++;
  }

  void fire_lane() {
    if (!m_lane_pending) return;
    m_lane_pending = false;
    if (!check_timing(m_lane_cmd, m_lane_addr)) {
      s_lane_dropped++;
      return;
    }
    m_device.issue_command(m_lane_cmd, m_lane_addr, m_clk);
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
