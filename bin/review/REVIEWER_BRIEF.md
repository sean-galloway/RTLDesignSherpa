# RTL Design Sherpa -- documentation review brief

You are reviewing the technical documentation of an open-source RTL library
(SystemVerilog, FPGA and ASIC targets) before it is publicly announced. The
author wants it accurate and honest, not flattering.

## What you have

Each directory under `books/` is one self-contained review unit:

- `DOCS.md` -- every documentation page in that book, concatenated. Each page is
  preceded by an HTML comment giving its real source path.
- `RTL.sv` -- the SystemVerilog for the modules those pages document, concatenated
  the same way. **This is ground truth.** Where a document and the RTL disagree,
  the document is wrong.
- `DOCS_WITH_NO_MODULE.md` -- present only in some books. Pages for which no
  matching module was found. Some are legitimately not module pages (guides,
  overviews). Others may document modules that were never written. Check.

| book | title | docs | modules | approx size |
|------|-------|------|---------|-------------|
| `axis4` | RTL AMBA AXI4-Stream | 6 | 4 | ~10k |
| `axil4` | RTL AMBA AXI4-Lite | 10 | 8 | ~13k |
| `axis5` | RTL AMBA AXI5-Stream | 5 | 4 | ~13k |
| `apb5` | RTL AMBA APB5 | 9 | 8 | ~18k |
| `apb` | RTL AMBA APB4 | 11 | 8 | ~24k |
| `axi5` | RTL AMBA AXI5 | 9 | 8 | ~30k |
| `cdc` | RTL Clock Domain Crossing | 11 | 10 | ~34k |
| `axi4` | RTL AMBA AXI4 | 19 | 16 | ~40k |
| `shared` | RTL AMBA Shared Infrastructure | 38 | 32 | ~111k |
| `math` | RTL Math Library | 28 | 31 | ~123k |
| `common` | RTL Common Library | 57 | 56 | ~133k |
| `monitor` | RTL AMBA Monitor Subsystem | 59 | 57 | ~190k |

Review one book per session. `monitor`, `common`, `shared` and `math` are large;
split them if you need to.

## What we want

Ranked roughly by value:

1. **Claims the RTL does not support.** A documented parameter, port, or feature
   that does not exist. A stated capability the logic does not implement. These are
   the most damaging defects because a reader acts on them.
2. **Numbers that are wrong.** Widths, depths, latencies, encodings, bit ranges,
   throughput, area. Recompute rather than trusting the prose. A previous review
   round found a throughput figure off by 8x and a whole family of parameters
   documented as log2 exponents when they are literal counts.
3. **Internal contradictions.** Two pages disagreeing, or a page disagreeing with
   itself between prose and a table or code example.
4. **Code examples that would not compile** -- wrong port names, ports that do not
   exist, illegal parameter values.
5. **Unsupported or unmeasured claims** presented as fact: "production ready",
   "zero latency", frequency and power numbers with no synthesis behind them.
6. **Gaps** -- a module with no usable description, a parameter no page explains.

## Rules

**Verify every claim against `RTL.sv` before reporting it.** This is the single
most important instruction. A previous reviewer worked from rendered PDFs and
roughly half its findings were extraction artifacts that did not exist in the
source -- garbled identifiers like `AXIIDWIDIF` and `fubaxlwvalid`, LaTeX
fragments like `\mathsf{...}`, and sentences that appeared truncated at page
breaks but are complete. You have the real source, so that class of error should
not appear. If something looks like mangled text, it is almost certainly your own
rendering, not a defect: skip it.

**Cite precisely.** Give the source path from the file banner plus a short quote of
the exact text. Do not cite page numbers.

**Say what you checked and how.** For a numeric finding, show the recomputation.

**Distinguish confidence.** Mark each finding as CONFIRMED (you verified it against
the RTL and can point at the contradicting line) or SUSPECTED (it looks wrong but
you could not confirm from the material provided). Do not pad the list -- a short
list of confirmed defects is far more useful than a long mixed one.

**Do not report style preferences** -- heading conventions, tone, British vs
American spelling, the presence of status markers -- unless they actively mislead.

**Flag RTL bugs separately.** If while checking a doc claim you conclude the RTL
itself is wrong, say so under a distinct heading. Those are valuable and rare.

## Output format

For each finding:

```
[CONFIRMED|SUSPECTED] <one-line summary>
  File:     <path from the banner>
  Says:     "<exact quote>"
  Actually: <what the RTL does, with the line or signal that proves it>
  Impact:   <what a reader would get wrong>
```

Then a short section `POSSIBLE RTL BUGS` if you found any, and a closing paragraph
on the book's overall accuracy.

## Known-weak areas, already identified

You do not need to rediscover these; only report them if you find *new* detail:

- Several `*_mon_cg` monitor wrappers (AXI4 and AXI4-Lite) contain no clock-gating
  logic while exposing gating status outputs. Already documented as a known gap.
- Timing and frequency tables throughout are unsourced estimates; the multiplier
  ones in particular were written against an earlier implementation.
- Timing diagrams are placeholders in several AMBA books.
- "Production Ready" status markers are under review by the author.
