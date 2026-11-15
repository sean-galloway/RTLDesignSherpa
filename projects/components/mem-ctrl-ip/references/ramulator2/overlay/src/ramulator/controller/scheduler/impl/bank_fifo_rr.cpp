#include <stdexcept>
#include <vector>

#include "ramulator/base/param.h"
#include "ramulator/controller/controller_base.h"
#include "ramulator/controller/scheduler/i_scheduler.h"

namespace Ramulator {

// Per-bank FIFO queues with a round-robin pick across banks (memory-controllers
// MC-013 item 4). The pooled FR-FCFS scheduler is pumice's CAM; this one is the
// shape of granite's bank-FIFO store under its bank-pick core:
//   * within a bank, requests issue in arrival order -- a row conflict at the
//     head blocks the row hits queued behind it (no intra-bank reordering);
//   * across banks, the heads whose next command is timing-ready are offered
//     round robin from the bank after the last pick, so no bank starves and no
//     bank is favoured by arrival time;
//   * column_first: among the ready heads a column command (RD / WR / RDA / WRA)
//     wins over a row command, as the pick core's select does; off, the first
//     ready head in rotor order wins whatever its command;
//   * with no ready head the oldest head is returned, as FR-FCFS does: the
//     controller re-checks timing and issues nothing this cycle;
//   * peek_depth (MC-016): a bank whose head is a row CONFLICT (its next
//     command closes the open row) offers instead the oldest row hit among its
//     first peek_depth entries, if one exists and no older entry in that window
//     carries the same address. 1 is the strict FIFO above; 2 is the shape of
//     granite's two-head record if the pick could fire the second record on
//     its own hit (it cannot today: the second record is read only in the pop
//     shadow, see mc_bank_fifo_store); the queue depth is the per-bank
//     pooled hit-first bound. A head that is a miss on a closed bank keeps
//     its place: nothing behind it can be a hit.
class BankFIFORRScheduler : public IScheduler, public Implementation {
  RAMULATOR_REGISTER_IMPLEMENTATION(IScheduler, BankFIFORRScheduler, "BankFIFO-RR")

  ControllerBase* m_ctrl = nullptr;
  bool m_column_first = false;
  int m_peek_depth = 1;
  int m_last_bank = -1;
  std::vector<ReqBuffer::iterator> m_heads;
  std::vector<bool> m_has_head;
  // the first peek_depth entries of each bank's FIFO, oldest first
  std::vector<std::vector<ReqBuffer::iterator>> m_window;

  void init() override {
    RAMULATOR_PARSE_PARAM(m_column_first, bool, "column_first").default_val(false);
    RAMULATOR_PARSE_PARAM(m_peek_depth, int, "peek_depth").default_val(1);
    if (m_peek_depth < 1) {
      throw std::runtime_error("BankFIFO-RR: peek_depth must be >= 1");
    }
    m_ctrl = cast_parent<ControllerBase>();
    const size_t num_banks = m_ctrl->m_device.m_bank_nodes.size();
    m_heads.resize(num_banks);
    m_has_head.assign(num_banks, false);
    m_window.assign(num_banks, {});
    for (auto& w : m_window) {
      w.reserve(m_peek_depth);
    }
  }

  // Keep `it` in the bank's window if it is among the peek_depth oldest.
  void offer_to_window(std::vector<ReqBuffer::iterator>& w, ReqBuffer::iterator it) {
    size_t pos = w.size();
    while (pos > 0 && it->arrive < w[pos - 1]->arrive) {
      pos--;
    }
    if (pos >= static_cast<size_t>(m_peek_depth)) {
      return;
    }
    if (w.size() < static_cast<size_t>(m_peek_depth)) {
      w.push_back(it);
    }
    for (size_t k = w.size() - 1; k > pos; k--) {
      w[k] = w[k - 1];
    }
    w[pos] = it;
  }

  // The head the bank offers: its oldest entry, unless that is a row conflict
  // and a younger entry in the window is a row hit with no same-address entry
  // ahead of it in the window.
  ReqBuffer::iterator bank_head(const std::vector<ReqBuffer::iterator>& w) {
    auto head = w[0];
    if (w.size() < 2) {
      return head;
    }
    const auto& meta = m_ctrl->m_device.m_spec->command_meta;
    if (!meta[head->command].is_closing) {
      return head;  // a hit, or an ACT on a closed bank: nothing behind it is a hit
    }
    for (size_t k = 1; k < w.size(); k++) {
      if (!meta[w[k]->command].is_accessing) {
        continue;
      }
      bool blocked = false;
      for (size_t j = 0; j < k; j++) {
        if (w[j]->addr == w[k]->addr) {
          blocked = true;
          break;
        }
      }
      if (!blocked) {
        return w[k];
      }
    }
    return head;
  }

  ReqBuffer::iterator get_best_request(ReqBuffer& buffer, RequestFilterRef filter) override {
    if (buffer.size() == 0) {
      return buffer.end();
    }
    const int num_banks = static_cast<int>(m_heads.size());
    std::fill(m_has_head.begin(), m_has_head.end(), false);
    for (auto& w : m_window) {
      w.clear();
    }

    // Pass 1: the first peek_depth entries of every bank's FIFO, oldest first
    // (peek_depth 1: the head alone).
    for (auto it = buffer.begin(); it != buffer.end(); it++) {
      it->command = m_ctrl->get_preq_command(it->final_command, it->addr_vec);
      if (filter && !filter(*it)) {
        continue;
      }
      const int bank = m_ctrl->m_device.get_flat_bank_id(it->addr_vec);
      if (bank < 0 || bank >= num_banks) {
        continue;
      }
      offer_to_window(m_window[bank], it);
    }
    for (int bank = 0; bank < num_banks; bank++) {
      if (!m_window[bank].empty()) {
        m_heads[bank] = bank_head(m_window[bank]);
        m_has_head[bank] = true;
      }
    }

    // Pass 2: rotor over the heads from the bank after the last pick.
    auto oldest = buffer.end();
    auto ready_row = buffer.end();
    int ready_row_bank = -1;
    for (int k = 1; k <= num_banks; k++) {
      const int bank = (m_last_bank + k) % num_banks;
      if (!m_has_head[bank]) {
        continue;
      }
      auto head = m_heads[bank];
      if (oldest == buffer.end() || head->arrive < oldest->arrive) {
        oldest = head;
      }
      if (!m_ctrl->check_timing(head->command, head->addr_vec)) {
        continue;
      }
      const bool is_column = m_ctrl->m_device.m_spec->command_meta[head->command].is_accessing;
      if (!m_column_first || is_column) {
        m_last_bank = bank;
        return head;
      }
      if (ready_row == buffer.end()) {
        ready_row = head;
        ready_row_bank = bank;
      }
    }
    if (ready_row != buffer.end()) {
      m_last_bank = ready_row_bank;
      return ready_row;
    }
    return oldest;
  }
};

}  // namespace Ramulator
