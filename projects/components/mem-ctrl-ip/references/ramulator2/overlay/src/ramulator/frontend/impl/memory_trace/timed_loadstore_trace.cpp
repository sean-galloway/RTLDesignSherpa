#include <filesystem>
#include <fmt/format.h>
#include <fstream>
#include <string>
#include <vector>

#include "ramulator/base/param.h"
#include "ramulator/frontend/i_frontend.h"

namespace Ramulator {

namespace fs = std::filesystem;

// Replays a timestamped load/store trace ONCE and waits for every request to
// complete (memory-controllers MC-012). The stock LoadStoreTrace replays
// cyclically and finishes when its last line has been SENT, so a run on a
// finite trace stops with requests still queued and the cycle count short.
//
// One request per line; '#' starts a comment, blank lines are skipped:
//   <tick> <LD|ST> <addr>
// tick is the frontend cycle (this frontend's clock, clock_ratio ticks of the
// base clock) at or after which the request may be sent; ticks must not
// decrease down the file. addr is a byte address, decimal or 0x hex. At most
// max_per_tick requests are sent per tick (default 1: one bus beat per cycle,
// the shape of an AXI injector whose data bus moves one transaction per clock).
// split_directions (memory-controllers MC-018): the loads and the stores are
// two independent in-order streams, each offering up to max_per_tick per tick
// and each stalling on its own -- the shape of an AXI port with a write channel
// and a read channel (a refused store no longer holds the load behind it). In
// this mode a direction's ticks are re-stamped with its own beat order (the
// file's ticks describe the shared port; each channel moves one beat per tick).
// Off, the file is one in-order stream.
//
// Stats: num_sent / num_completed (reads and writes separately), cycles (the
// tick at which the last completion arrived), first_send_tick, stall_ticks
// (ticks on which a due request was refused by the memory system),
// max_outstanding (the deepest the frontend's in-flight count got), and per
// direction the first send tick and the last completion tick
// (read_first_send_tick / read_last_complete_tick, write_...): the window a
// board timer measures (first beat in to last response out) for that direction.
class TimedLoadStoreTrace : public IFrontEnd, public Implementation {
  RAMULATOR_REGISTER_IMPLEMENTATION(IFrontEnd, TimedLoadStoreTrace, "TimedLoadStoreTrace")

 private:
  struct Entry {
    Clk_t tick;
    bool is_write;
    Addr_t addr;
  };
  std::vector<Entry> m_trace;
  size_t m_next = 0;
  size_t m_outstanding = 0;
  // split_directions: the trace indexed per direction ([0] loads, [1] stores) and a cursor each
  std::vector<size_t> m_by_dir[2];
  size_t m_next_dir[2] = {0, 0};

  std::string m_trace_path;
  int m_max_per_tick = 1;
  bool m_split = false;
  // start_tick: no request is offered before this frontend tick (the GO against the memory system's
  // refresh phase; memory-controllers MC-021 item 3: the board's mixed open-page cell has two modes and
  // the refresh counter's phase at GO picks one)
  int m_start_tick = 0;

  size_t s_reads_sent = 0;
  size_t s_writes_sent = 0;
  size_t s_reads_completed = 0;
  size_t s_writes_completed = 0;
  size_t s_cycles = 0;
  size_t s_first_send_tick = 0;
  size_t s_stall_ticks = 0;
  size_t s_max_outstanding = 0;
  bool m_sent_any = false;
  size_t s_first_send[2] = {0, 0};      // [0] read, [1] write
  size_t s_last_complete[2] = {0, 0};
  bool m_sent_type[2] = {false, false};

 public:
  void init() override {
    RAMULATOR_PARSE_PARAM(m_clock_ratio, unsigned int, "clock_ratio").required();
    RAMULATOR_PARSE_PARAM(m_trace_path, std::string, "path").required();
    RAMULATOR_PARSE_PARAM(m_max_per_tick, int, "max_per_tick").default_val(1);
    RAMULATOR_PARSE_PARAM(m_split, bool, "split_directions").default_val(false);
    RAMULATOR_PARSE_PARAM(m_start_tick, int, "start_tick").default_val(0);
    if (m_max_per_tick < 1) {
      throw std::runtime_error("TimedLoadStoreTrace: max_per_tick must be >= 1");
    }

    m_logger.info(fmt::format("Loading trace file {} ...", m_trace_path));
    init_trace(m_trace_path);
    m_logger.info(fmt::format("Loaded {} requests.", m_trace.size()));
    if (m_split) {
      // Each direction is its own in-order stream paced by its own channel, so its ticks are
      // its own beat order: a combined file's ticks (a captured port's accept order, both
      // directions interleaved) would otherwise pace each channel at half rate whenever one
      // direction runs alone (memory-controllers ISSUE-004).
      for (size_t i = 0; i < m_trace.size(); i++) {
        const int d = m_trace[i].is_write ? 1 : 0;
        m_trace[i].tick = static_cast<Clk_t>(m_by_dir[d].size());
        m_by_dir[d].push_back(i);
      }
    }

    m_stats.add("num_reads_sent", s_reads_sent);
    m_stats.add("num_writes_sent", s_writes_sent);
    m_stats.add("num_reads_completed", s_reads_completed);
    m_stats.add("num_writes_completed", s_writes_completed);
    m_stats.add("cycles", s_cycles);
    m_stats.add("first_send_tick", s_first_send_tick);
    m_stats.add("stall_ticks", s_stall_ticks);
    m_stats.add("max_outstanding", s_max_outstanding);
    m_stats.add("read_first_send_tick", s_first_send[0]);
    m_stats.add("read_last_complete_tick", s_last_complete[0]);
    m_stats.add("write_first_send_tick", s_first_send[1]);
    m_stats.add("write_last_complete_tick", s_last_complete[1]);
  };

  void tick() override {
    m_clk++;
    if (m_clk < static_cast<size_t>(m_start_tick)) return;
    if (!m_split) {
      int sent_this_tick = 0;
      while (m_next < m_trace.size() && sent_this_tick < m_max_per_tick) {
        const Entry& e = m_trace[m_next];
        if (e.tick > static_cast<Clk_t>(m_clk)) {
          break;
        }
        if (!try_send(e)) {
          s_stall_ticks++;
          break;
        }
        m_next++;
        sent_this_tick++;
      }
      return;
    }
    bool stalled = false;
    for (int d = 0; d < 2; d++) {
      int sent_this_tick = 0;
      while (m_next_dir[d] < m_by_dir[d].size() && sent_this_tick < m_max_per_tick) {
        const Entry& e = m_trace[m_by_dir[d][m_next_dir[d]]];
        if (e.tick > static_cast<Clk_t>(m_clk)) {
          break;
        }
        if (!try_send(e)) {
          stalled = true;
          break;
        }
        m_next_dir[d]++;
        sent_this_tick++;
      }
    }
    if (stalled) {
      s_stall_ticks++;
    }
  };

  // Offer one entry to the memory system; true if it was accepted.
  bool try_send(const Entry& e) {
    Request req(e.addr, e.is_write ? Request::Type::Write : Request::Type::Read);
    req.size_bytes = m_memory_system->get_tx_bytes();
    req.callback = [this](Request& done) {
      m_outstanding--;
      if (done.type_id == Request::Type::Write) {
        s_writes_completed++;
        s_last_complete[1] = m_clk;
      } else {
        s_reads_completed++;
        s_last_complete[0] = m_clk;
      }
      record_end();
    };
    // Counted before sending: a coalesced write or a forwarded read may
    // complete inside send().
    m_outstanding++;
    if (!m_memory_system->send(req)) {
      m_outstanding--;
      return false;
    }
    if (e.is_write) {
      s_writes_sent++;
    } else {
      s_reads_sent++;
    }
    if (!m_sent_any) {
      m_sent_any = true;
      s_first_send_tick = m_clk;
    }
    if (!m_sent_type[e.is_write]) {
      m_sent_type[e.is_write] = true;
      s_first_send[e.is_write] = m_clk;
    }
    if (m_outstanding > s_max_outstanding) {
      s_max_outstanding = m_outstanding;
    }
    record_end();
    return true;
  }

  bool is_finished() override {
    const bool drained = m_split ? (m_next_dir[0] >= m_by_dir[0].size() && m_next_dir[1] >= m_by_dir[1].size())
                                 : m_next >= m_trace.size();
    return drained && m_outstanding == 0;
  };

 private:
  void record_end() {
    if (is_finished()) {
      s_cycles = m_clk;
    }
  }

  static Addr_t parse_addr(const std::string& tok) {
    if (tok.compare(0, 2, "0x") == 0 || tok.compare(0, 2, "0X") == 0) {
      return std::stoll(tok.substr(2), nullptr, 16);
    }
    return std::stoll(tok);
  }

  void init_trace(const std::string& file_path_str) {
    fs::path trace_path(file_path_str);
    if (!fs::exists(trace_path)) {
      throw std::runtime_error(fmt::format("Trace {} does not exist!", file_path_str));
    }
    std::ifstream trace_file(trace_path);
    if (!trace_file.is_open()) {
      throw std::runtime_error(fmt::format("Trace {} cannot be opened!", file_path_str));
    }

    std::string line;
    int line_num = 0;
    Clk_t last_tick = 0;
    while (std::getline(trace_file, line)) {
      line_num++;
      line = line.substr(0, line.find('#'));
      std::vector<std::string> tokens;
      tokenize(tokens, line, " ");
      std::erase(tokens, "");
      if (tokens.empty()) {
        continue;
      }
      if (tokens.size() != 3) {
        throw std::runtime_error(
            fmt::format("Trace {} line {}: expected '<tick> <LD|ST> <addr>'", file_path_str, line_num));
      }
      Clk_t tick = std::stoll(tokens[0]);
      if (tick < last_tick) {
        throw std::runtime_error(
            fmt::format("Trace {} line {}: tick {} is earlier than the previous line's {}", file_path_str,
                        line_num, tick, last_tick));
      }
      last_tick = tick;
      bool is_write;
      if (tokens[1] == "LD") {
        is_write = false;
      } else if (tokens[1] == "ST") {
        is_write = true;
      } else {
        throw std::runtime_error(
            fmt::format("Trace {} line {}: unknown type '{}' (expected LD or ST)", file_path_str, line_num, tokens[1]));
      }
      m_trace.push_back({tick, is_write, parse_addr(tokens[2])});
    }
    trace_file.close();
  };
};

}  // namespace Ramulator
