# Claude Code Guide: BCH Error Correction

**Version:** 0.1
**Last Updated:** 2025-10-29
**Purpose:** AI-specific guidance for BCH component development

---

## Quick Context

**What:** Configurable BCH (Bose-Chaudhuri-Hocquenghem) error correction encoder/decoder
**Status:** 📋 Future Project - Structure Created
**Your Role:** Help users develop BCH RTL, verification, and reference models

**📖 Complete Documentation:**
- `projects/components/bch/PRD.md` - Complete requirements and specifications
- `projects/components/bch/README.md` - Overview and architecture
- `projects/components/bch/TASKS.md` - Development task tracking

---

## Critical Rules for BCH Development

### Rule #0: BCH is Complex - Start Simple

**⚠️ DO NOT try to implement a full decoder immediately ⚠️**

**Correct Development Order:**
1. ✅ **Start:** BCH(7,4,1) encoder (simplest possible)
2. ✅ **Next:** BCH(15,11,1) encoder
3. ✅ **Then:** BCH(511,493,2) encoder (production target)
4. ✅ **After encoder works:** Start on decoder for BCH(7,4,1)
5. ✅ **Finally:** Scale up decoder complexity

**Why This Matters:**
- BCH encoder is MUCH simpler than decoder (~1 week vs ~8 weeks)
- Small codes allow manual verification
- Reference model is essential before RTL
- Galois field arithmetic needs extensive testing

### Rule #1: Reference Model First - MANDATORY

**⚠️ NEVER write BCH RTL without a working reference model ⚠️**

**Required Tools:**
```python
# Install Galois library for Python
pip install galois numpy

# Create reference model first
import galois
import numpy as np

# Example: BCH(7,4,1) encoder
GF = galois.GF(2)
n, k = 7, 4
bch = galois.BCH(n, k)

# Encode message
message = GF([1, 0, 1, 1])
codeword = bch.encode(message)
print(f"Codeword: {codeword}")

# Decode with errors
received = codeword.copy()
received[0] ^= 1  # Inject 1 error
decoded = bch.decode(received)
print(f"Decoded: {decoded}")
```

**Why This Matters:**
- BCH math is complex - easy to get wrong
- Reference model catches algorithm bugs immediately
- Test vectors come from reference model
- All RTL MUST match reference model output

### Rule #2: Galois Field Arithmetic - Foundation

**⚠️ Get GF arithmetic right FIRST ⚠️**

**Required GF Modules (create these before encoder/decoder):**

```systemverilog
// GF(2^m) addition (just XOR)
module gf_add #(parameter int M = 4) (
    input  logic [M-1:0] a,
    input  logic [M-1:0] b,
    output logic [M-1:0] sum
);
    assign sum = a ^ b;  // GF addition is XOR
endmodule

// GF(2^m) multiplication (complex)
module gf_mult #(
    parameter int M = 4,
    parameter logic [M:0] PRIM_POLY = 5'b10011  // x^4 + x + 1
) (
    input  logic [M-1:0] a,
    input  logic [M-1:0] b,
    output logic [M-1:0] product
);
    // Implementation options:
    // 1. Lookup table (fast, large for M>8)
    // 2. Shift-and-add (slow, small area)
    // 3. Karatsuba (balanced)
endmodule

// GF(2^m) inverse (needed for Berlekamp-Massey)
module gf_inv #(
    parameter int M = 4,
    parameter logic [M:0] PRIM_POLY = 5'b10011
) (
    input  logic [M-1:0] a,
    output logic [M-1:0] inv
);
    // Implementation: Fermat's little theorem
    // a^(-1) = a^(2^M - 2) in GF(2^M)
endmodule
```

**Test Strategy:**
- Exhaustive test for M ≤ 8 (256 elements)
- Random test for M > 8 (100,000+ operations)
- Cross-check with Galois library

### Rule #3: Encoder Development Pattern

**Correct Encoder Implementation Flow:**

**Step 1: Understand Generator Polynomial**
```python
# Generate g(x) for BCH(n, k, t)
import galois
bch = galois.BCH(n=7, k=4)
g = bch.generator_poly
print(f"Generator polynomial: {g}")
# Example output: Poly(x^3 + x + 1, GF(2))
```

**Step 2: LFSR-Based Encoder**
```systemverilog
// BCH encoder using LFSR
module bch_encoder #(
    parameter int N = 7,    // Codeword length
    parameter int K = 4,    // Message length
    parameter int PARITY = N - K  // 3
) (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       data_in,    // 1 bit per cycle (serial)
    input  logic       data_valid,
    output logic       parity_out,
    output logic       parity_valid
);
    // LFSR taps from generator polynomial
    // g(x) = x^3 + x + 1 → taps at positions [3,1,0]

    logic [PARITY-1:0] lfsr;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            lfsr <= '0;
        end else if (data_valid) begin
            // LFSR shift with feedback
            // Feedback = lfsr[PARITY-1] XOR data_in
            logic feedback = lfsr[PARITY-1] ^ data_in;
            lfsr <= {lfsr[PARITY-2:0], 1'b0} ^ ({PARITY{feedback}} & TAPS);
        end
    )
endmodule
```

**Step 3: Test with Reference Model**
```python
# Generate test vectors
for i in range(2**k):
    message = GF([(i >> j) & 1 for j in range(k)])
    codeword = bch.encode(message)
    # Export to testbench
```

### Rule #4: Decoder is MUCH Harder

**Decoder Complexity Breakdown:**

| Module | Complexity | Effort | Verification Effort |
|--------|------------|--------|---------------------|
| Syndrome Calculator | Medium | 1 week | 2 days |
| Berlekamp-Massey | High | 3 weeks | 1 week |
| Chien Search | Medium | 1 week | 3 days |
| Error Correction | Low | 2 days | 1 day |
| Integration | Medium | 1 week | 2 weeks |

**Total Decoder Effort:** ~8 weeks (vs. ~1 week for encoder)

**Decoder Development Order:**
1. Syndrome calculator (test extensively!)
2. Berlekamp-Massey (implement, verify against reference)
3. Chien search (parallel vs. serial trade-off)
4. Error correction (simple XOR)
5. Integration and system test

### Rule #5: Common BCH Pitfalls

**❌ Pitfall 1: Wrong Primitive Polynomial**
```systemverilog
// WRONG: Using x^4 + x^3 + 1 (not primitive!)
parameter PRIM_POLY = 5'b11001;

// CORRECT: x^4 + x + 1 (primitive for GF(2^4))
parameter PRIM_POLY = 5'b10011;
```

**How to avoid:** Use standard primitive polynomials from tables, verify with reference model.

**❌ Pitfall 2: Syndrome Bit Ordering**
```systemverilog
// WRONG: LSB-first when should be MSB-first
assign syndrome = {received[0], received[1], ...};

// CORRECT: Match reference model bit ordering
assign syndrome = {received[n-1], received[n-2], ..., received[0]};
```

**How to avoid:** Test with single-bit errors at known positions.

**❌ Pitfall 3: Berlekamp-Massey Not Converging**
```systemverilog
// WRONG: Fixed iteration count
for (int i = 0; i < T; i++) begin
    // Algorithm needs up to 2*T iterations!
end

// CORRECT: Up to 2*T iterations
for (int i = 0; i < 2*T; i++) begin
    // Berlekamp-Massey iteration
end
```

**How to avoid:** Study algorithm carefully, verify convergence with reference model.

**❌ Pitfall 4: Chien Search Off-By-One**
```systemverilog
// WRONG: Searching wrong positions
for (int i = 0; i < n; i++) begin
    // Need to search n positions, starting from α^0
end

// CORRECT: Proper position mapping
for (int i = 0; i < n; i++) begin
    // Evaluate σ(α^(-i)) for i=0 to n-1
end
```

**How to avoid:** Test with single error at position 0, position n-1, and middle.

---

## Development Workflow

### Starting a New BCH Configuration

**1. Choose Configuration:**
```
Start with: BCH(7,4,1)     - Simplest (tutorial)
Then:       BCH(15,11,1)   - Still simple
Then:       BCH(31,26,1)   - Moderate
Production: BCH(511,493,2) - Real-world target
```

**2. Create Reference Model:**
```bash
cd bin/
python3 bch_model.py --create --n 7 --k 4 --t 1
python3 bch_model.py --test-vectors --output test_vectors.txt
```

**3. Implement Encoder:**
```bash
cd rtl/encoder/
# Create bch_encoder.sv
# Test with test_vectors.txt
```

**4. Verify Encoder:**
```bash
cd dv/tests/
pytest test_bch_encoder.py -v --n=7 --k=4 --t=1
```

**5. Implement Decoder (much later):**
```bash
# Only after encoder is 100% working for multiple configurations!
cd rtl/decoder/
# Start with syndrome calculator
# Then Berlekamp-Massey
# Then Chien search
# Then error correction
```

### Creating Test Vectors

**Use Reference Model:**
```python
# bin/bch_model.py
import galois
import numpy as np

def generate_test_vectors(n, k, t):
    """Generate comprehensive test vectors"""
    bch = galois.BCH(n, k)
    vectors = []

    # 1. All possible messages (if k small)
    if k <= 10:
        for i in range(2**k):
            msg = galois.GF(2)([(i >> j) & 1 for j in range(k)])
            codeword = bch.encode(msg)
            vectors.append((msg, codeword))

    # 2. Error injection tests
    msg = galois.GF(2).Random(k)
    codeword = bch.encode(msg)

    # No errors
    vectors.append((codeword, msg, 0, True))

    # 1 error at each position
    for pos in range(n):
        received = codeword.copy()
        received[pos] ^= 1
        vectors.append((received, msg, 1, True))

    # t errors (max correctable)
    for trial in range(100):
        received = codeword.copy()
        errors = np.random.choice(n, t, replace=False)
        for pos in errors:
            received[pos] ^= 1
        vectors.append((received, msg, t, True))

    # t+1 errors (uncorrectable)
    for trial in range(100):
        received = codeword.copy()
        errors = np.random.choice(n, t+1, replace=False)
        for pos in errors:
            received[pos] ^= 1
        vectors.append((received, None, t+1, False))

    return vectors
```

---

## Testing Strategy

### Encoder Testing

**Level 1: Correctness**
```python
@pytest.mark.parametrize("n,k,t", [(7,4,1), (15,11,1), (31,26,1)])
def test_encoder_correctness(n, k, t):
    """Encoder output matches reference model"""
    # All possible inputs (if k small)
    # Or random sampling (if k large)
```

**Level 2: Backpressure**
```python
def test_encoder_backpressure():
    """Encoder handles valid/ready correctly"""
    # Random backpressure patterns
    # Ensure no data loss/corruption
```

**Level 3: Performance**
```python
def test_encoder_throughput():
    """Measure actual throughput"""
    # Should achieve 1 bit/cycle for serial
    # Should achieve N bits/cycle for parallel
```

### Decoder Testing

**Level 1: Error-Free**
```python
def test_decoder_no_errors():
    """Decoder correctly decodes error-free codewords"""
    # Fast path should be taken
    # error_free flag should assert
```

**Level 2: Correctable Errors**
```python
@pytest.mark.parametrize("num_errors", range(1, t+1))
def test_decoder_correctable(num_errors):
    """Decoder corrects up to t errors"""
    # Random error injection
    # 10,000+ trials per error count
    # Verify 100% correction success
```

**Level 3: Uncorrectable Errors**
```python
def test_decoder_uncorrectable():
    """Decoder flags uncorrectable errors (>t errors)"""
    # Inject t+1, t+2, ..., n errors
    # Verify uncorrectable flag asserts
    # Verify decoder does not falsely correct
```

**Level 4: Statistical Validation**
```python
def test_decoder_statistical():
    """Statistical validation of error correction"""
    # 100,000+ random trials
    # Verify error distribution matches theory
    # Measure false correction rate (should be ~0)
```

---

## Performance Optimization Tips

### Encoder Optimization

**Tip 1: Parallel LFSR**
```systemverilog
// Serial LFSR: 1 bit/cycle
// Parallel LFSR: N bits/cycle (more complex)
module bch_encoder_parallel #(parameter int PARALLEL = 8);
    // Multiple feedback paths
    // More complex tap configuration
```

**Tip 2: Pipeline**
```systemverilog
// Add pipeline stages to meet timing
// Trade latency for throughput
```

### Decoder Optimization

**Tip 1: Parallel Syndrome**
```systemverilog
// Calculate all 2t syndromes in parallel
// Requires 2t multipliers (area cost)
```

**Tip 2: Parallel Chien Search**
```systemverilog
// Evaluate σ(x) at multiple points in parallel
// Reduces latency from n cycles to n/P cycles
```

**Tip 3: Fast Path for Error-Free**
```systemverilog
// Detect all-zero syndrome quickly
// Bypass Berlekamp-Massey and Chien search
// Significant power/latency savings
```

---

## Common User Questions

### Q: "Should I use Berlekamp-Massey or Euclidean algorithm?"

**A:** Berlekamp-Massey is preferred for hardware:
- More regular structure
- Easier to pipeline
- Lower latency (2t iterations vs. O(t^2))
- Industry standard for BCH decoders

Euclidean algorithm is better for software (easier to understand).

### Q: "How do I choose GF multiplier implementation?"

**A:** Trade-offs:

| Implementation | Area | Speed | Use Case |
|----------------|------|-------|----------|
| Lookup Table | Large (2^(2M) bits) | 1 cycle | M ≤ 8 |
| Shift-and-Add | Small | M cycles | Low throughput |
| Parallel Mult | Medium | 1-2 cycles | Balanced |

**Recommendation:** LUT for M ≤ 8, parallel mult for M > 8.

### Q: "What BCH configuration should I target?"

**A:** Depends on application:

- **Flash memory:** BCH(511,493,2), BCH(1023,1013,2)
- **Communications:** BCH(127,120,1), BCH(255,247,1)
- **Optical storage:** BCH(2047,2007,5)
- **Learning/testing:** BCH(7,4,1), BCH(15,11,1)

Start with small codes for development, scale to production config.

### Q: "How long does BCH take to develop?"

**A:** Realistic estimates:

- **Encoder only:** 2-3 weeks (with testing)
- **Decoder only:** 8-10 weeks (complex!)
- **Full codec:** 12-14 weeks
- **Multiple configs:** +2 weeks per config
- **Optimization:** +4-6 weeks

**Total for production-ready BCH:** 6 months

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Starting with Decoder

```
WRONG Order: Decoder → Encoder
RIGHT Order: Encoder → Small Decoder → Large Decoder
```

**Why:** Encoder is 10x simpler and validates your understanding of BCH math.

### ❌ Anti-Pattern 2: No Reference Model

```
WRONG: Write RTL directly from theory
RIGHT: Reference model → Test vectors → RTL
```

**Why:** BCH math is complex, easy to get wrong, reference model catches errors immediately.

### ❌ Anti-Pattern 3: Large Config First

```
WRONG: Start with BCH(8191, 8171, 2)
RIGHT: BCH(7,4,1) → BCH(15,11,1) → BCH(511,493,2)
```

**Why:** Small codes allow manual verification and faster debug cycles.

### ❌ Anti-Pattern 4: Insufficient Testing

```
WRONG: 100 test vectors
RIGHT: 100,000+ test vectors with statistical validation
```

**Why:** BCH has large state space, corner cases are subtle, need statistical confidence.

---

## Quick Commands

```bash
# Create BCH reference model
cd bin/
python3 bch_model.py --n 7 --k 4 --t 1

# Generate test vectors
python3 bch_model.py --test-vectors --output ../dv/tests/vectors.txt

# Run encoder tests
cd dv/tests/
pytest test_bch_encoder.py -v

# Run decoder tests (when ready)
pytest test_bch_decoder.py -v --n=7 --k=4 --t=1

# Performance characterization
pytest test_bch_performance.py -v --report
```

---

## Remember

1. 📚 **Reference Model First** - Python/Galois before RTL
2. 🔢 **GF Arithmetic** - Test exhaustively, foundation of everything
3. 📈 **Start Small** - BCH(7,4,1) then scale up
4. 🔧 **Encoder First** - Much simpler than decoder
5. 🧪 **Statistical Testing** - 100,000+ random trials required
6. ⏱️ **Be Patient** - Decoder is complex (8+ weeks effort)
7. 📖 **Study Theory** - Lin & Costello book is essential
8. ✅ **Verify Everything** - BCH math is unforgiving

---

## Resources

**Essential Reading:**
- Lin & Costello, *Error Control Coding* - Chapter 6 (BCH codes)
- Blahut, *Algebraic Codes* - Chapter 7 (Cyclic codes)
- Wicker, *Error Control Systems* - Chapter 8 (BCH decoding)

**Python Libraries:**
- Galois: https://github.com/mhostetter/galois
- NumPy: https://numpy.org/

**Online Calculators:**
- BCH Parameters: http://www.eccpage.com/
- Primitive Polynomials: http://www.partow.net/programming/polynomials/

---

**Version:** 0.1 (Planning Phase)
**Last Updated:** 2025-10-29
**Maintained By:** RTL Design Sherpa Project
