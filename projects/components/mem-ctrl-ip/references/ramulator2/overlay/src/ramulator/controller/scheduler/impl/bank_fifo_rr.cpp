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
//     controller re-checks timing and issues nothing this cycle.
class BankFIFORRScheduler : public IScheduler, public Implementation {
  RAMULATOR_REGISTER_IMPLEMENTATION(IScheduler, BankFIFORRScheduler, "BankFIFO-RR")

  ControllerBase* m_ctrl = nullptr;
  bool m_column_first = false;
  int m_last_bank = -1;
  std::vector<ReqBuffer::iterator> m_heads;
  std::vector<bool> m_has_head;

  void init() override {
    RAMULATOR_PARSE_PARAM(m_column_first, bool, "column_first").default_val(false);
    m_ctrl = cast_parent<ControllerBase>();
    const size_t num_banks = m_ctrl->m_device.m_bank_nodes.size();
    m_heads.resize(num_banks);
    m_has_head.assign(num_banks, false);
  }

  ReqBuffer::iterator get_best_request(ReqBuffer& buffer, RequestFilterRef filter) override {
    if (buffer.size() == 0) {
      return buffer.end();
    }
    const int num_banks = static_cast<int>(m_heads.size());
    std::fill(m_has_head.begin(), m_has_head.end(), false);

    // Pass 1: the head of every bank's FIFO = its oldest eligible request.
    for (auto it = buffer.begin(); it != buffer.end(); it++) {
      it->command = m_ctrl->get_preq_command(it->final_command, it->addr_vec);
      if (filter && !filter(*it)) {
        continue;
      }
      const int bank = m_ctrl->m_device.get_flat_bank_id(it->addr_vec);
      if (bank < 0 || bank >= num_banks) {
        continue;
      }
      if (!m_has_head[bank] || it->arrive < m_heads[bank]->arrive) {
        m_heads[bank] = it;
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
