# 🧠 AXI Stream for Dummies

> *A plain-English guide to understanding AXI4-Stream — the simplest, most elegant way to move data through an FPGA or SoC.*

---

## 🧩 What Is AXI Stream?

AXI4-Stream (or **AXIS**) is a **unidirectional data channel** used to **stream** data from one block (the *source*) to another (the *sink*).
Think of it as a **conveyor belt** moving packets or words of data — one piece at a time — when both sides agree it’s okay to send.

Unlike full AXI (which handles addresses and memory reads/writes), AXI Stream only moves **data**, not addresses.

---

## 🧭 The Core Idea

The protocol uses a **ready/valid handshake** between sender and receiver.

| Signal                               | Direction      | Meaning                                        |
| :----------------------------------- | :------------- | :--------------------------------------------- |
| **TVALID**                           | Master → Slave | “I have valid data for you.”                   |
| **TREADY**                           | Slave → Master | “I’m ready to receive data.”                   |
| **TDATA**                            | Master → Slave | The actual data being transferred.             |
| *(optional)* **TLAST**               | Master → Slave | Marks the **end of a packet**.                 |
| *(optional)* **TKEEP**               | Master → Slave | Byte-level valid mask (e.g. for 64-bit buses). |
| *(optional)* **TID / TDEST / TUSER** | Master → Slave | Metadata or routing info.                      |

---

## 🤝 The Handshake

Data only transfers when **both** `TVALID` and `TREADY` are **high** at the same clock cycle.

```
          ______       ______       ______
clk  ____|      |_____|      |_____|      |____
            |<-- one cycle -->|
TVALID  ----====----====----====----====----====
TREADY  --------====--------====--------====----
TDATA   === DATA0 === DATA1 === DATA2 === DATA3

Transfer occurs only when both TVALID and TREADY are high at the same time.
```

---

## 🚀 How It Works (Simplified)

Let’s use an analogy:

* **Master (Source)** = A vending machine putting snacks on a conveyor.
* **Slave (Sink)** = You, picking up snacks when your hands are free.

**Rules:**

1. The vending machine (`TVALID`) only puts a snack out when it’s ready.
2. You (`TREADY`) only grab a snack when your hands are free.
3. A snack (`TDATA`) is officially transferred when both happen simultaneously.

---

## 🧰 Example: 4-Beat Stream Transfer

| Cycle | TVALID | TREADY | Transfer? | TDATA            |
| :---- | :----- | :----- | :-------- | :--------------- |
| 1     | 1      | 0      | ❌         | (Master waiting) |
| 2     | 1      | 1      | ✅         | Word 0           |
| 3     | 1      | 1      | ✅         | Word 1           |
| 4     | 1      | 0      | ❌         | (Slave stalled)  |
| 5     | 1      | 1      | ✅         | Word 2           |

---

## 🧠 Why Use AXI Stream?

* **No addressing overhead** → perfect for **high-speed data paths**
* **Decoupled flow control** → each side can pause independently
* **Pipeline-friendly** → chain multiple modules together easily
* **Flexible widths** → 8 bits to 1024 bits or more
* **Standardized** → works with DMA, FIFOs, filters, and AXI interconnects

---

## 🏗️ Common AXI Stream Modules

| Module Type                    | Function                                          |
| :----------------------------- | :------------------------------------------------ |
| **AXI DMA**                    | Moves data between memory and streams             |
| **FIFO**                       | Buffers stream data                               |
| **Data Converter**             | Changes width, rate, or format                    |
| **AXIS Switch / Interconnect** | Routes streams between multiple sources and sinks |
| **AXIS Register Slice**        | Adds pipeline stages for timing                   |

---

## 🔧 Minimal Verilog Example

```verilog
always @(posedge clk) begin
    if (reset) begin
        tvalid <= 0;
    end else begin
        if (tready && tvalid) begin
            // Data accepted, move to next
            tdata  <= next_data;
            tvalid <= more_data;
        end else if (!tvalid && more_data) begin
            // Load first data
            tdata  <= next_data;
            tvalid <= 1'b1;
        end
    end
end
```

---

## 💡 Tips for New Designers

* Always **register your outputs** (`TVALID`, `TDATA`, etc.).
* Avoid combinational loops between `TREADY` and `TVALID`.
* When debugging, plot both `TREADY` and `TVALID` in your waveform — transfers happen only when both are 1.
* Use `TLAST` to mark packet or frame boundaries.

---

## 🧩 Quick Summary

| Concept        | TL;DR                                                     |
| :------------- | :-------------------------------------------------------- |
| Handshake      | `TVALID && TREADY`                                        |
| Flow control   | Independent in both directions                            |
| Purpose        | Fast, address-less data movement                          |
| Typical use    | DMA → Processing Block → Memory                           |
| Think of it as | A **conveyor belt** with a **“ready” light** on both ends |

---

## 🧮 Bonus: Packet Flow Diagram

```
  [DMA Source] ---> [AXIS FIFO] ---> [Filter] ---> [Sink]
         |               |               |
        TVALID          TVALID          TVALID
        TREADY <-------- TREADY <-------- TREADY
```

---

# 🎓 For the Slightly Smarter Dummies

Let’s go a level deeper.

---

## 🧾 TLAST: Packet Boundaries

`TLAST` marks the **end of a frame or packet**. Think of it as the **"end of sentence"** in your stream.

* Useful for video lines, Ethernet frames, or DMA bursts.
* Typically asserted for one beat at the end of each packet.

```verilog
// Example: assert TLAST at the end of every 1024-beat packet
assign tlast = (beat_count == 1023);
```

---

## 🧮 TKEEP: Byte Masking

`TKEEP` is a **byte-valid mask** for each beat. It lets you mark which bytes in `TDATA` are valid.

For example, in a 64-bit bus (8 bytes wide):

| TKEEP   | Meaning               |
| :------ | :-------------------- |
| `8'hFF` | All 8 bytes valid     |
| `8'h0F` | Lower 4 bytes valid   |
| `8'h01` | Only first byte valid |

Use this for variable-length packets that don’t fill the full data word.

---

## 🗂️ TUSER, TID, and TDEST

| Signal    | Purpose                                                 |
| :-------- | :------------------------------------------------------ |
| **TUSER** | User-defined metadata (e.g., error flags, control bits) |
| **TID**   | Identifies stream source (like a tag)                   |
| **TDEST** | Destination tag for routing or switching                |

These are optional and can be ignored if you don’t need them, but they make AXI Stream **super flexible** in large systems.

---

## 🛠️ Multi-Beat Transfer Example

Example of a 3-beat packet with `TKEEP` and `TLAST`:

| Beat | TDATA              | TKEEP | TLAST |
| :--- | :----------------- | :---- | :---- |
| 0    | 0xDEADBEEFCAFEBABE | 0xFF  | 0     |
| 1    | 0x1234567890ABCDEF | 0xFF  | 0     |
| 2    | 0x0BADF00D00000000 | 0x0F  | 1     |

This shows that only the lower 4 bytes are valid in the final beat.

---

## ⚙️ Practical Design Tips

* **Register slice everything.** AXIS can stall anytime; use register slices for timing closure.
* **Add FIFOs** between clock domains or whenever you need backpressure decoupling.
* **Always handle TLAST.** Even if you don’t need packets *yet*, your DMA will.
* **Simulate with stalls.** Randomize `TREADY` in testbenches to ensure your module handles backpressure correctly.

---

## 📈 Common Patterns

| Pattern                | Description                         |
| :--------------------- | :---------------------------------- |
| **Stream FIFO**        | Absorbs backpressure, stores bursts |
| **Width Converter**    | Converts 32-bit → 64-bit, etc.      |
| **Protocol Converter** | Adapts AXIS to AXI Memory-Mapped    |
| **Broadcaster**        | Duplicates data to multiple sinks   |
| **Arbiter/Mux**        | Selects among multiple sources      |

---

## 🔬 Example System: From Memory to DSP

```
   [DDR Memory]
       |
   [AXI DMA MM2S]
       |
   [AXIS FIFO]
       |
   [DSP Filter]
       |
   [AXI DMA S2MM]
       |
   [DDR Memory]
```

Each block follows the same handshake — data flows when everyone agrees.

---

## 🧩 Debug Checklist

* ✅ Is TVALID ever asserted?
* ✅ Does TREADY toggle or stay stuck low?
* ✅ Are transfers happening (`TVALID && TREADY`)?
* ✅ Is TLAST asserted correctly at packet boundaries?
* ✅ Are you respecting TKEEP on partial packets?

If you fail any of these, your stream isn’t flowing.

---

## 💬 In a Sentence

> AXI Stream is just data moving one beat at a time, when both sides agree, wrapped in a handshake polite enough to make hardware engineers sleep at night.

---

## 🧩 Quick Reference Summary

| Signal     | Width                     | Purpose                |
| :--------- | :------------------------ | :--------------------- |
| **TDATA**  | Variable                  | Data payload           |
| **TVALID** | 1 bit                     | Master: Data valid     |
| **TREADY** | 1 bit                     | Slave: Ready to accept |
| **TLAST**  | 1 bit                     | Marks end of packet    |
| **TKEEP**  | 1 byte per 8 bits of data | Byte mask              |
| **TUSER**  | Custom                    | User-defined info      |
| **TID**    | Custom                    | Stream ID              |
| **TDEST**  | Custom                    | Destination tag        |

---

## 🏁 Closing Thought

Once you understand `TVALID` + `TREADY`, everything else in AXI Stream is optional frosting.
It’s designed to be modular, scalable, and as close to plug-and-play as hardware gets.

> *In short: if AXI Memory Mapped is the post office, AXI Stream is a conveyor belt in a factory.*

---

# 📦 Packing TLAST/TKEEP/TUSER into the FIFO Payload

If you pack `TLAST`, `TKEEP`, and `TUSER` **with** `TDATA` into the FIFO (your current approach), you keep the FIFO protocol‑agnostic and preserve packet semantics. Below is a tight pattern that scales and keeps synthesis happy.

## ✅ Recommended Bundle Typedef

```systemverilog
// Parameterize everything so the FIFO stays neutral
parameter int DATA_W = 64;          // AXIS data width
parameter int KEEP_W = DATA_W/8;    // One byte per keep bit
parameter int USER_W = 4;           // Whatever you need; can be 0

// Sideband+payload packed into one vector for FIFO
typedef struct packed {
  logic                 last;        // TLAST
  logic [KEEP_W-1:0]    keep;        // TKEEP
  logic [USER_W-1:0]    user;        // TUSER (flags, errors, route hints, etc.)
  logic [DATA_W-1:0]    data;        // TDATA
} axis_pkt_t;

localparam int FIFO_W = $bits(axis_pkt_t);
```

**Why:**

* Keeps the FIFO **agnostic** (it sees just `FIFO_W` bits).
* Maintains **packet atomicity** (data + sideband move together).
* Avoids lockstep FIFOs and the drift bugs they can cause.

## 🔌 AXIS ⇄ FIFO Wiring (Ingress/Egress)

```systemverilog
// Ingress (AXIS slave → FIFO write)
axis_pkt_t wr_pkt;
assign wr_pkt.data = s_axis_tdata;
assign wr_pkt.keep = s_axis_tkeep;
assign wr_pkt.user = s_axis_tuser;
assign wr_pkt.last = s_axis_tlast;

assign wr_valid      = s_axis_tvalid;
assign s_axis_tready = wr_ready;
assign wr_data       = wr_pkt; // packed to vector by the tool

// Egress (FIFO read → AXIS master)
axis_pkt_t rd_pkt;
assign rd_pkt = rd_data; // unpack struct from vector

assign m_axis_tdata  = rd_pkt.data;
assign m_axis_tkeep  = rd_pkt.keep;
assign m_axis_tuser  = rd_pkt.user;
assign m_axis_tlast  = rd_pkt.last;

assign m_axis_tvalid = rd_valid;
assign rd_ready      = m_axis_tready;
```

## 🧪 Packet-Integrity SVAs (drop‑in)

```systemverilog
// 1) TLAST only when VALID (no ghost last)
property p_last_implies_valid; @(posedge clk) disable iff (!rst_n)
  (m_axis_tlast) |-> m_axis_tvalid; endproperty
assert property (p_last_implies_valid);

// 2) KEEP must be a prefix mask on TLAST beat (optional rule)
function automatic bit is_prefix_mask (logic [KEEP_W-1:0] k);
  logic seen0; seen0 = 0;
  for (int i = KEEP_W-1; i >= 0; i--) begin
    if (!k[i]) seen0 = 1; else if (seen0 && k[i]) return 0; // hole after zero
  end
  return 1;
endfunction

property p_keep_prefix_on_last; @(posedge clk) disable iff (!rst_n)
  (m_axis_tvalid && m_axis_tready && m_axis_tlast) |-> is_prefix_mask(m_axis_tkeep);
endproperty
assert property (p_keep_prefix_on_last);

// 3) No data loss across FIFO: write count equals read count per packet
// (Use your FIFO's count/last observation to build stronger invariants as needed)
```

## 🧠 Design Notes

* **Atomicity:** Packing guarantees `TLAST` travels with its data; you never split “end‑of‑packet” from the payload beat that owns it.
* **Width changes:** If you introduce a width converter before/after the FIFO, re‑emit `KEEP` accordingly; on the final beat enforce the prefix‑mask rule.
* **USER bits:** Treat `user` as opaque. Define its bitfields in the wrapper (e.g., `{err, sof, eom, route[1:0]}`) and keep the FIFO unaware.
* **Registered vs mux read:** Use your FIFO’s `REGISTERED=1` for timing closure across partitions; keep `=0` for absolute minimum latency. Throughput is still 1 beat/clk.
* **Watermarks:** Drive upstream `TREADY=0` when `almost_full` to avoid bubble‑y on/off toggling; optionally gate downstream `rd_ready` until occupancy exceeds a low watermark to drain in larger bursts.

## 🧯 Corner Cases Checklist

* Partial last beat: `TLAST=1` with `KEEP!=all_ones` is legal; consumers must honor `KEEP` when storing.
* Empty packets: usually **disallow** (no beats with `TLAST` but zero data). Add an assertion if your system forbids zero‑length frames.
* Back‑to‑back packets: ensure `TLAST` can assert on cycle N and a new packet can start on cycle N+1 without a bubble (FIFO design allows it).
* Underflow/overflow: deassert `wr_ready` on full; deassert `m_axis_tvalid` on empty. Never drop beats silently—add error flags if overflow is possible in your environment.
  ``
