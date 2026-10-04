// content.js -- CDC drill question bank and scenario generators.
//
// Pure functions, no DOM. Dual-environment header: the same bytes run in the
// browser (window.CDCD) and under node (module.exports). All randomness flows
// through the rng parameter; generators never call Math.random().
//
// Two modes:
//   spot  -- multi-select "pick every illegal element" (exact-set scoring)
//   picker -- single-select "pick the right synchronizer" (one correct, three
//             plausible distractors)
var CDCD = (typeof window !== 'undefined' ? window : globalThis).CDCD ||
           ((typeof window !== 'undefined' ? window : globalThis).CDCD = {});

(function (CDCD) {
  'use strict';

  // -- helpers ---------------------------------------------------------------

  function isAscii(s) {
    return typeof s === 'string' && /^[\x00-\x7F]*$/.test(s);
  }

  function checkAscii(value, path, errors) {
    if (typeof value === 'string') {
      if (!isAscii(value)) {
        errors.push('non-ASCII string at ' + path);
      }
    } else if (Array.isArray(value)) {
      for (var i = 0; i < value.length; i++) {
        checkAscii(value[i], path + '[' + i + ']', errors);
      }
    } else if (value && typeof value === 'object') {
      for (var k in value) {
        if (Object.prototype.hasOwnProperty.call(value, k)) {
          checkAscii(value[k], path + '.' + k, errors);
        }
      }
    }
  }

  function uniqueStrings(arr) {
    var seen = {};
    var out = [];
    for (var i = 0; i < arr.length; i++) {
      if (!seen[arr[i]]) {
        seen[arr[i]] = true;
        out.push(arr[i]);
      }
    }
    return out;
  }

  // Random naming helpers so wording varies by seed.
  function clkName(rng, prefix) {
    var names = ['clk_a', 'clk_b', 'clk_tx', 'clk_rx', 'clk_fast', 'clk_slow',
                 'clk_core', 'clk_io', 'clk_pclk', 'clk_sclk'];
    return prefix || CDCD.rpick(rng, names);
  }

  function pairNames(rng) {
    var pairs = [
      ['clk_a', 'clk_b'],
      ['clk_tx', 'clk_rx'],
      ['clk_fast', 'clk_slow'],
      ['clk_core', 'clk_io'],
      ['clk_pclk', 'clk_sclk']
    ];
    return CDCD.rpick(rng, pairs);
  }

  function signalName(rng) {
    var names = ['data', 'cmd', 'status', 'flag', 'req', 'ack', 'pulse',
                 'event', 'valid', 'ctrl', 'addr', 'count', 'enable'];
    return CDCD.rpick(rng, names);
  }

  function busName(rng) {
    var names = ['data_bus', 'addr_bus', 'ctrl_bus', 'word_bus', 'pkt_bus',
                 'cfg_bus', 'status_bus'];
    return CDCD.rpick(rng, names);
  }

  function bitWidth(rng) {
    return CDCD.rint(rng, 4, 32);
  }

  function moduleName(rng) {
    var names = ['block_a', 'block_b', 'tx_core', 'rx_core', 'ctrl_unit',
                 'io_pad', 'arbiter', 'sequencer', 'decoder'];
    return CDCD.rpick(rng, names);
  }

  // -- option statement templates --------------------------------------------

  var OPT = {
    multi_2flop: 'A multi-bit data bus is crossed using only a plain 2-flop synchronizer',
    pulse_level: 'A single-cycle pulse is sent level-style into a 2-flop synchronizer',
    recomb: 'Combinational logic recombines two independently synchronized bits',
    async_reset_deassert: 'An asynchronous reset deassertion is not synchronized to the receiving clock',
    fifo_no_gray: 'FIFO read/write pointers cross between clocks without Gray-code encoding',
    reconvergent_bus: 'Reconvergent synchronized bits are used together as a parallel bus',
    unregistered_src: 'A combinational source signal crosses without first being registered',
    sync_to_combo: 'A synchronizer output drives combinational logic before a receiving flop',
    fast_level: 'A level signal changes faster than the receiving clock can sample it',
    level_as_pulse: 'A level signal is fed into a pulse-toggle synchronizer',
    handshake_stream: 'A request/acknowledge handshake moves a high-throughput data stream',
    fifo_pulse: 'An asynchronous FIFO is used to move a single-cycle pulse',
    reset_one_flop: 'A reset synchronizer uses only one flop stage',
    bundled_singles: 'Unrelated single-bit signals are bundled and treated as a coherent bus',
    mux_glitch: 'A clock-mux select crosses without a glitch-free synchronizer',
    feedback_loop: 'A signal crosses clocks and feeds back into its own source domain',
    branched_meta: 'The output of a synchronizer is branched to multiple flops in parallel',
    single_flop: 'A safety-critical crossing uses only a single synchronizer flop',
    two_flop_level: 'A single-bit level signal crosses through a 2-flop synchronizer',
    gray_fifo: 'FIFO pointers cross as Gray-coded values through 2-flop synchronizers',
    pulse_toggle_ok: 'A single-cycle pulse crosses through a pulse-toggle synchronizer',
    req_ack_ok: 'A command word crosses through a req/ack handshake',
    sync_reset_deassert: 'The asynchronous reset deassertion is synchronized to the receiving clock'
  };

  // -- spot scenario generators ----------------------------------------------

  function makeSpot(id, tier, stem, diagram, options, explanation) {
    return {
      id: id,
      mode: 'spot',
      tier: tier,
      stem: stem,
      diagram: diagram || '',
      options: options,
      explanation: explanation
    };
  }

  function opt(text, correct, explanation) {
    return { text: text, correct: correct, explanation: explanation };
  }

  var spotGenerators = [
    {
      id: 'multi_bit_2flop',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var bus = busName(rng);
        var w = bitWidth(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = 'In ' + mA + ' (' + src + '), a ' + w + '-bit ' + bus +
          ' is sampled by a plain 2-flop chain before reaching ' + mB +
          ' (' + dst + '). The bus can change every ' + src + ' cycle.';
        var diagram =
          mA + '  ' + src + '        ' + dst + '  ' + mB + '\n' +
          '    [' + bus + '[' + (w - 1) + ':0]] ----> [2ff] ----> [sample]\n' +
          '         multi-bit value         single bit-by-bit sync';
        var options = [
          opt(OPT.multi_2flop, true,
            'Correct. Each bit of the ' + w + '-bit bus is synchronized ' +
            'independently, so bits may settle at different ' + dst +
            ' cycles. The destination can sample an incoherent value.'),
          opt(OPT.two_flop_level, false,
            'A single-bit level signal would be fine with a 2-flop chain, ' +
            'but that is not what is crossing here.'),
          opt(OPT.gray_fifo, false,
            'Gray-coded pointers are a legal way to cross FIFO addresses, ' +
            'but this scenario moves a data bus, not FIFO pointers.'),
          opt(OPT.async_reset_deassert, false,
            'Reset synchronization is a different concern; no asynchronous ' +
            'reset crossing is described here.')
        ];
        var expl = 'A multi-bit value that changes coherently in the source ' +
          'domain must not be reconstructed bit-by-bit by independent 2-flop ' +
          'synchronizers. Use an async FIFO, a handshake, or a gray-code ' +
          'if the value is a counter/pointer.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'pulse_as_level',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') creates a single-cycle ' + sig +
          ' pulse and routes it through two flops clocked by ' + dst +
          ' before ' + mB + ' acts on it.';
        var diagram =
          src + '  |__|      ' + dst + '  _|___|\n' +
          '      pulse  ----> [2ff] ---->  level sample\n' +
          'The pulse may land between ' + dst + ' rising edges.';
        var options = [
          opt(OPT.pulse_level, true,
            'Correct. The pulse is narrower than the destination clock ' +
            'period; it can be missed entirely or latched as a level and ' +
            'act twice.'),
          opt(OPT.fast_level, false,
            'The signal is not a sustained level that changes too fast; ' +
            'it is a one-cycle pulse.'),
          opt(OPT.pulse_toggle_ok, false,
            'A pulse-toggle synchronizer is the right structure for a pulse, ' +
            'but the circuit here uses a plain 2-flop chain.'),
          opt(OPT.handshake_stream, false,
            'A handshake moves data with explicit acknowledgment, not a ' +
            'single-cycle event.')
        ];
        var expl = 'A single-cycle pulse in the source clock is not a level. ' +
          'A plain 2-flop chain may miss it or stretch it. Convert the pulse ' +
          'to a toggle (pulse-toggle synchronizer) or use a handshake/FIFO.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'recombinant_bits',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var a = signalName(rng);
        var b = signalName(rng);
        var out = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var gate = CDCD.rpick(rng, ['AND', 'OR', 'XOR']);
        var stem = mA + ' sends two unrelated single-bit signals ' + a +
          ' and ' + b + ' from ' + src + ' into separate 2-flop ' +
          'synchronizers in ' + mB + ' (' + dst + '). A ' + gate +
          ' gate combines the synchronized versions into ' + out + '.';
        var diagram =
          '   ' + src + '        ' + dst + '\n' +
          '   ' + a + ' ---> [2ff] ---+\n' +
          '                          [' + gate + '] ---> ' + out + '\n' +
          '   ' + b + ' ---> [2ff] ---+';
        var options = [
          opt(OPT.recomb, true,
            'Correct. ' + a + ' and ' + b + ' may metastabilize and settle ' +
            'in different ' + dst + ' cycles, so the ' + gate +
            ' gate can produce a glitch or wrong value.'),
          opt(OPT.two_flop_level, false,
            'Either bit alone is fine as a level, but combining them after ' +
            'synchronization is the problem.'),
          opt(OPT.reconvergent_bus, false,
            'This is two single bits, not a parallel bus of synchronized bits.'),
          opt(OPT.sync_to_combo, false,
            'The synchronizer outputs do drive combinational logic, which is ' +
            'related, but the specific hazard is recombination of two ' +
            'separately synchronized bits.')
        ];
        var expl = 'When two independently synchronized bits are recombined, ' +
          'they can settle on different destination cycles. The combinational ' +
          'output can glitch or be wrong. Move the function to the source ' +
          'domain, use a handshake, or synchronize a pre-computed result.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'async_reset_deassert',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var rstClk = pair[0];
        var dstClk = pair[1];
        var rst = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' generates an active-low asynchronous reset ' + rst +
          ' in ' + rstClk + ' domain and distributes it to flops in ' + mB +
          ' (' + dstClk + '). The deassertion edge is not synchronized.';
        var diagram =
          rstClk + '  ' + rst + ' __________/```````````````\n' +
          dstClk + '              [no sync]  --> async deassert';
        var options = [
          opt(OPT.async_reset_deassert, true,
            'Correct. The falling edge of ' + rst +
            ' is asynchronous, so it can violate recovery/removal timing of ' +
            dstClk + ' flops and cause metastability.'),
          opt(OPT.sync_reset_deassert, false,
            'Synchronizing the deassertion edge is exactly the fix, not the ' +
            'violation.'),
          opt(OPT.single_flop, false,
            'The problem is not the number of sync stages on a data signal; ' +
            'it is the reset deassertion edge.'),
          opt(OPT.fifo_no_gray, false,
            'FIFO pointers are unrelated to reset distribution.')
        ];
        var expl = 'Asynchronous reset assertion is usually safe, but the ' +
          'deassertion edge must be synchronized to the receiving clock to ' +
          'avoid recovery/removal violations. Use a reset synchronizer ' +
          '(async assert, synced deassert).';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'fifo_pointer_not_gray',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var wrClk = pair[0];
        var rdClk = pair[1];
        var depth = 1 << CDCD.rint(rng, 3, 5);
        var ptrBits = CDCD.rint(rng, 4, 6);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' builds a ' + depth + '-entry async FIFO in ' +
          wrClk + '/' + rdClk + '. The ' + ptrBits +
          '-bit write pointer is sent to the read side using binary encoding ' +
          'through a 2-flop chain.';
        var diagram =
          'wr_ptr[' + (ptrBits - 1) + ':0] (binary) ----> [2ff] ----> rd side\n' +
          '   multiple bits can flip on one increment';
        var options = [
          opt(OPT.fifo_no_gray, true,
            'Correct. A binary pointer can have multiple bit transitions on ' +
            'one increment; the 2-flop chain may sample a wrong intermediate ' +
            'value, corrupting FIFO fullness.'),
          opt(OPT.gray_fifo, false,
            'Gray-coded pointers are the standard solution; only one bit ' +
            'changes at a time.'),
          opt(OPT.multi_2flop, false,
            'The issue is not that the bus is multi-bit, but that the ' +
            'encoding allows multi-bit transitions.'),
          opt(OPT.handshake_stream, false,
            'A handshake is an alternative CDC structure, not the flaw in ' +
            'this FIFO pointer path.')
        ];
        var expl = 'FIFO address pointers must cross as Gray-code values ' +
          '(or through a handshake) so only one bit changes per increment. ' +
          'Binary pointers can be sampled in an intermediate state and report ' +
          'a wildly wrong fill level.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'reconvergent_bus',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var bus = busName(rng);
        var w = bitWidth(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' sends a ' + w + '-bit ' + bus + ' from ' + src +
          ' to ' + dst + ' by synchronizing each bit through its own 2-flop ' +
          'chain. ' + mB + ' reassembles the synchronized bits back into a ' +
          w + '-bit bus and decodes it as a code word.';
        var diagram =
          bus + '[' + (w - 1) + ':0] ----> [' + w + ' x 2ff] ----> ' + bus +
          '_sync[' + (w - 1) + ':0]\n' +
          'Each bit has independent metastasis settling time.';
        var options = [
          opt(OPT.reconvergent_bus, true,
            'Correct. The ' + w +
            ' bits may settle in different destination cycles, so the bus ' +
            'value sampled by ' + mB + ' can be transiently wrong.'),
          opt(OPT.recomb, false,
            'The bits are used as a bus, not recombined through random ' +
            'combinational logic.'),
          opt(OPT.gray_fifo, false,
            'Gray coding applies to sequential counts, not arbitrary data buses.'),
          opt(OPT.bundled_singles, false,
            'The bits here are meant to be a bus, not unrelated single-bit ' +
            'signals mistakenly bundled.')
        ];
        var expl = 'A parallel bus whose bits are synchronized independently ' +
          'will reconverge at different times. The destination can see ' +
          'impossible transitions. Use a FIFO, a handshake with a valid flag, ' +
          'or keep the bus in one clock domain.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'unregistered_source',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') drives ' + sig +
          ' from combinational logic directly into a 2-flop synchronizer ' +
          'feeding ' + mB + ' (' + dst + '). The combinational output can ' +
          'glitch whenever any input changes.';
        var diagram =
          'comb logic -> ' + sig + ' -> [2ff ' + dst + '] -> ' + mB + '\n' +
          '        glitches may cross the clock boundary';
        var options = [
          opt(OPT.unregistered_src, true,
            'Correct. Combinational glitches in ' + src +
            ' can be sampled by the destination as false transitions.'),
          opt(OPT.sync_to_combo, false,
            'The synchronizer output is not driving combinational logic here; ' +
            'the source side is combinational.'),
          opt(OPT.two_flop_level, false,
            'A registered source level would be fine, but this source is not ' +
            'registered.'),
          opt(OPT.pulse_level, false,
            'The signal is not described as a single-cycle pulse.')
        ];
        var expl = 'Always register a signal in its source clock domain before ' +
          'sending it across a clock boundary. Unregistered combinational ' +
          'outputs can glitch and create spurious destination events.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'sync_to_combinational',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var gate = CDCD.rpick(rng, ['AND', 'OR', 'XOR']);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = 'A single-bit ' + sig + ' from ' + mA + ' (' + src +
          ') passes through a 2-flop synchronizer into ' + mB + ' (' + dst +
          '). The synchronized ' + sig + '_sync is immediately combined in a ' +
          gate + ' gate with a local ' + dst + ' signal before reaching a flop.';
        var diagram =
          src + ' ' + sig + ' -> [2ff ' + dst + '] -> ' + sig +
          '_sync ---+\n' +
          '                                 [' + gate + '] -> flop\n' +
          '              local ' + dst + ' signal --------+';
        var options = [
          opt(OPT.sync_to_combo, true,
            'Correct. If ' + sig +
            '_sync is metastable, it propagates through the ' + gate +
            ' gate and can corrupt the local signal or create a glitch.'),
          opt(OPT.recomb, false,
            'Only one bit is synchronized here, not two independently ' +
            'synchronized bits being recombined.'),
          opt(OPT.unregistered_src, false,
            'The source side is not described as combinational.'),
          opt(OPT.branched_meta, false,
            'The synchronized signal is not branched to multiple flops; it ' +
            'drives combinational logic.')
        ];
        var expl = 'A synchronizer output should always go directly into a ' +
          'capturing flop. Feeding it into combinational logic lets ' +
          'metastability propagate and can glitch downstream logic. Register ' +
          'the sync output first, then use it.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'fast_level_signal',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var ratio = CDCD.rint(rng, 2, 5);
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') toggles a level signal ' + sig +
          ' every ' + src + ' cycle. ' + dst + ' runs ' + ratio +
          'x slower. ' + sig + ' is sampled by a plain 2-flop chain in ' + mB +
          ' (' + dst + '). Some transitions are lost.';
        var diagram =
          src + '  _|_|_|_|_|_|_|_|_  (toggle every cycle)\n' +
          dst + '  ____/    \\____      (samples too slowly)';
        var options = [
          opt(OPT.fast_level, true,
            'Correct. ' + sig + ' changes faster than ' + dst +
            ' can sample, so the destination misses events and cannot ' +
            'reconstruct the source sequence.'),
          opt(OPT.pulse_level, false,
            'The signal is a level, not a single-cycle pulse.'),
          opt(OPT.two_flop_level, false,
            'A 2-flop chain is fine for a level that changes slower than the ' +
            'destination sample rate; here it changes faster.'),
          opt(OPT.single_flop, false,
            'The problem is not the number of synchronizer stages but the ' +
            'source toggle rate relative to the destination clock.')
        ];
        var expl = 'A level signal that changes faster than the destination ' +
          'clock can reliably sample will lose information. Either slow the ' +
          'source event rate, speed up the destination, or use a handshake or ' +
          'FIFO that can absorb the bursts.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'level_into_pulse_toggle',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') keeps a control signal ' + sig +
          ' high for several ' + src + ' cycles to request a mode change. ' +
          'The signal is fed into a pulse-toggle synchronizer in ' + mB +
          ' (' + dst + '). ' + mB +
          ' sees one pulse every time ' + sig + ' toggles.';
        var diagram =
          src + '  ________/````````\\______   level=1 for many cycles\n' +
          dst + '            [pulse-toggle] -> one pulse per toggle\n' +
          'A held level will be re-interpreted as repeated events.';
        var options = [
          opt(OPT.level_as_pulse, true,
            'Correct. A pulse-toggle synchronizer converts each 0->1 and ' +
            '1->0 transition into a pulse. A sustained level will produce ' +
            'pulses continuously or be misinterpreted.'),
          opt(OPT.pulse_toggle_ok, false,
            'A pulse-toggle synchronizer is correct for single-cycle pulses, ' +
            'not for level signals.'),
          opt(OPT.two_flop_level, false,
            'A plain 2-flop chain is the right structure for this level ' +
            'signal, but the circuit uses a pulse-toggle synchronizer.'),
          opt(OPT.handshake_stream, false,
            'A handshake would be overkill for a simple mode-level, and it ' +
            'is not what is implemented.')
        ];
        var expl = 'Pulse-toggle synchronizers are designed for events ' +
          '(pulses/toggles), not for level semantics. A level should cross ' +
          'through a 2-flop synchronizer and be interpreted as a level in the ' +
          'destination domain.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'handshake_for_stream',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var word = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var bw = CDCD.rint(rng, 16, 64);
        var stem = mA + ' (' + src + ') streams a continuous ' + bw +
          '-bit ' + word + ' word every ' + src + ' cycle to ' + mB +
          ' (' + dst + ') using a 4-phase req/ack handshake. The throughput ' +
          'requirement is one word per destination cycle.';
        var diagram =
          src + '  word0 word1 word2 word3 ...\n' +
          '       req ~~~~> ' + dst + '\n' +
          '       <~~~~ ack (2-cycle round trip)\n' +
          'Throughput is limited by ack latency.';
        var options = [
          opt(OPT.handshake_stream, true,
            'Correct. A req/ack handshake pays a round-trip latency per word, ' +
            'so it cannot sustain one word per ' + dst + ' cycle.'),
          opt(OPT.fifo_pulse, false,
            'An async FIFO is not the right structure for a single pulse, but ' +
            'it is exactly right for this stream.'),
          opt(OPT.req_ack_ok, false,
            'A handshake is correct for occasional commands, not for a ' +
            'sustained word-per-cycle stream.'),
          opt(OPT.multi_2flop, false,
            'A 2-flop chain cannot carry a multi-bit data word coherently.')
        ];
        var expl = 'Handshakes are latency-tolerant and lossless but have ' +
          'low throughput because each word needs a round trip. For sustained ' +
          'streaming, use an asynchronous FIFO.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'fifo_for_single_pulse',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') needs to notify ' + mB + ' (' + dst +
          ') about a single-cycle ' + sig +
          ' event. It instantiates an 8-entry async FIFO, pushes one entry on ' +
          sig + ', and expects ' + mB + ' to pop it.';
        var diagram =
          src + ' pulse ' + sig + ' -> [wr_en] async FIFO [rd_en] -> ' + dst + '\n' +
          'One pulse becomes one FIFO transaction with several cycles latency.';
        var options = [
          opt(OPT.fifo_pulse, true,
            'Correct. An async FIFO adds pointer sync latency and area for a ' +
            'single-bit event. A pulse-toggle synchronizer is simpler and ' +
            'faster.'),
          opt(OPT.pulse_toggle_ok, false,
            'A pulse-toggle synchronizer is the right structure here.'),
          opt(OPT.two_flop_level, false,
            'The signal is a pulse, not a level.'),
          opt(OPT.handshake_stream, false,
            'A handshake would also be overkill for a single event.')
        ];
        var expl = 'Async FIFOs are for moving data or event streams across ' +
          'clocks. A single event is best handled by a pulse-toggle ' +
          'synchronizer.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'reset_sync_one_flop',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var rst = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' distributes an asynchronous reset ' + rst +
          ' from ' + src + ' to ' + mB + ' (' + dst +
          '). The deassertion edge goes through exactly one flop on ' + dst +
          ' before reaching the destination flops.';
        var diagram =
          src + ' ' + rst + ' async assert ----> [1ff ' + dst +
          '] ----> ' + mB + ' flops\n' +
          'Only one flop provides poor MTBF.';
        var options = [
          opt(OPT.reset_one_flop, true,
            'Correct. A single flop stage gives very low MTBF because the ' +
            'first flop can be metastable on deassertion.'),
          opt(OPT.async_reset_deassert, false,
            'The deassertion is synchronized, just inadequately.'),
          opt(OPT.single_flop, false,
            'This option is too generic; the specific issue is reset ' +
            'synchronization, not a generic data crossing.'),
          opt(OPT.branched_meta, false,
            'The reset is not branched from a synchronizer output to multiple ' +
            'flops in the problematic way described.')
        ];
        var expl = 'Reset synchronizers need at least two flop stages on the ' +
          'destination clock to achieve acceptable MTBF. Asynchronous assert ' +
          'is fine, but deassertion must be synchronized with sufficient ' +
          'stages.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'bundled_unrelated_bits',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var a = signalName(rng);
        var b = signalName(rng);
        var c = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') has three unrelated single-bit ' +
          'signals ' + a + ', ' + b + ', ' + c +
          '. To save wires they are packed into a 3-bit vector, sent through ' +
          'a 2-flop synchronizer, and unpacked in ' + mB + ' (' + dst +
          ') where code interprets the vector as a state encoding.';
        var diagram =
          '{' + a + ',' + b + ',' + c + '} -> [2ff ' + dst + '] -> ' +
          '{' + a + '_s,' + b + '_s,' + c + '_s}\n' +
          'Bits are independent but decoded as a coherent code.';
        var options = [
          opt(OPT.bundled_singles, true,
            'Correct. The three bits have no guaranteed timing relationship ' +
            'and may settle independently, producing invalid state encodings.'),
          opt(OPT.reconvergent_bus, false,
            'These are unrelated singles, not a naturally parallel bus.'),
          opt(OPT.recomb, false,
            'The bits are not recombined through logic; they are decoded as a ' +
            'vector, but the root issue is bundling unrelated signals.'),
          opt(OPT.multi_2flop, false,
            'A multi-bit coherent bus also needs more than 2-flop sync, but ' +
            'this scenario is specifically about unrelated single bits.')
        ];
        var expl = 'Unrelated single-bit signals should be synchronized ' +
          'individually or treated as separate events. Packing them into a ' +
          'vector and synchronizing the vector as if it were a coherent bus ' +
          'can create invalid states in the destination.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'clock_mux_glitch',
      tier: 3,
      generate: function (rng) {
        var pair = pairNames(rng);
        var clkA = pair[0];
        var clkB = pair[1];
        var sel = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' selects between ' + clkA + ' and ' + clkB +
          ' with a plain combinational mux. The select signal ' + sel +
          ' is generated in ' + clkA + ' domain and sampled by a single flop ' +
          'in the clocked path before driving the mux.';
        var diagram =
          clkA + ' ' + sel + ' -> [1ff] -> mux sel\n' +
          '         glitches on sel create runt pulses on the output clock';
        var options = [
          opt(OPT.mux_glitch, true,
            'Correct. A combinational mux select can glitch during ' +
            'transition, producing runt clock pulses and violating minimum ' +
            'pulse width.'),
          opt(OPT.unregistered_src, false,
            'The select is registered, but the mux itself is not glitch-free.'),
          opt(OPT.async_reset_deassert, false,
            'No reset crossing is described here.'),
          opt(OPT.single_flop, false,
            'The issue is not synchronizer stage count on a data signal; it ' +
            'is a clock-mux hazard.')
        ];
        var expl = 'Clock muxing requires a glitch-free circuit. A plain ' +
          'combinational mux with a select that can change asynchronously ' +
          'relative to the clocks will produce runt pulses. Use a glitch-free ' +
          'clock mux or synchronize the select properly.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'cross_clock_feedback',
      tier: 3,
      generate: function (rng) {
        var pair = pairNames(rng);
        var clkA = pair[0];
        var clkB = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + clkA + ') sends ' + sig + ' to ' + mB +
          ' (' + clkB + '). ' + mB + ' combines ' + sig +
          '_sync with a local signal and sends the result directly back to ' +
          mA + ' where it is used in combinational logic that drives ' + sig +
          ' again.';
        var diagram =
          clkA + ' ' + sig + ' -> [2ff] -> ' + clkB + ' ' + sig +
          '_sync -> comb -> return\n' +
          'The loop spans both clock domains with no register break.';
        var options = [
          opt(OPT.feedback_loop, true,
            'Correct. The path from ' + clkA + ' to ' + clkB +
            ' and back to ' + clkA + ' has no clocked boundary, so timing ' +
            'closure is impossible.'),
          opt(OPT.sync_to_combo, false,
            'The synchronized signal does drive combinational logic, but the ' +
            'deeper problem is the cross-clock feedback loop.'),
          opt(OPT.recomb, false,
            'There is no recombination of two independently synchronized bits.'),
          opt(OPT.unregistered_src, false,
            'The source may be registered; the problem is the feedback path.')
        ];
        var expl = 'A signal that crosses to another clock domain and feeds ' +
          'back into its own source domain creates an asynchronous loop. ' +
          'Register the returning signal in its own domain and treat it as an ' +
          'independent input, or restructure the architecture.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'branched_metastable',
      tier: 3,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var n = CDCD.rint(rng, 2, 4);
        var stem = mA + ' (' + src + ') sends ' + sig + ' to ' + mB +
          ' (' + dst + '). The output of the first synchronizer flop fans out ' +
          'to ' + n + ' destination flops in parallel, each capturing the ' +
          'signal independently.';
        var diagram =
          src + ' ' + sig + ' -> [2ff] -> sync_out --+---> flop1\n' +
          '                              |---> flop2\n' +
          '                              +---> flop' + n;
        var options = [
          opt(OPT.branched_meta, true,
            'Correct. If sync_out is metastable, the parallel destination ' +
            'flops can resolve to different values, breaking consistency.'),
          opt(OPT.sync_to_combo, false,
            'The sync output drives flops, not combinational logic.'),
          opt(OPT.reconvergent_bus, false,
            'The same bit is branched, not multiple bits of a bus.'),
          opt(OPT.single_flop, false,
            'The synchronizer has two stages, but the issue is the fan-out of ' +
            'the first stage output.')
        ];
        var expl = 'A synchronizer output should fan out only to a single ' +
          'capturing flop. Branching it to multiple flops lets each path ' +
          'resolve metastability independently, so downstream logic can see ' +
          'inconsistent values. Add a single capturing flop before fan-out.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'single_flop_safety',
      tier: 3,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') sends a safety-critical interrupt ' +
          sig + ' to ' + mB + ' (' + dst +
          '). The design uses a single flop synchronizer to minimize latency.';
        var diagram =
          src + ' ' + sig + ' -> [1ff ' + dst + '] -> ' + mB + '\n' +
          'Only one stage means poor MTBF.';
        var options = [
          opt(OPT.single_flop, true,
            'Correct. A single flop gives unacceptably low MTBF for a ' +
            'safety-critical crossing.'),
          opt(OPT.reset_one_flop, false,
            'This is a data/control crossing, not a reset synchronizer.'),
          opt(OPT.fast_level, false,
            'The signal rate is not stated to exceed the destination sample ' +
            'rate; the issue is stage count.'),
          opt(OPT.two_flop_level, false,
            'A 2-flop chain would be the normal minimum for this level signal.')
        ];
        var expl = 'Safety-critical clock-domain crossings need sufficient ' +
          'synchronizer stages to meet the target MTBF. A single flop is ' +
          'almost never acceptable. Add stages or use a higher reliability ' +
          'CDC structure.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    },
    {
      id: 'double_violation_stream',
      tier: 3,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var bus = busName(rng);
        var w = bitWidth(rng);
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') streams a continuous ' + w + '-bit ' +
          bus + ' to ' + mB + ' (' + dst +
          ') using a 2-flop chain per bit. A separate single-cycle ' + sig +
          ' pulse is sent through the same 2-flop chain as if it were a level.';
        var diagram =
          bus + '[' + (w - 1) + ':0] -> [' + w + ' x 2ff] -> ' + mB + '\n' +
          sig + ' pulse        -> [2ff]      -> may be missed';
        var options = [
          opt(OPT.multi_2flop, true,
            'Correct. The ' + w + '-bit ' + bus +
            ' is synchronized bit-by-bit, which can sample incoherent values.'),
          opt(OPT.pulse_level, true,
            'Correct. The single-cycle ' + sig +
            ' pulse may be missed or stretched by the destination clock.'),
          opt(OPT.handshake_stream, false,
            'A handshake would be a fix for the data path, but it is not a ' +
            'violation present in the scenario.'),
          opt(OPT.fifo_pulse, false,
            'Using an async FIFO for the pulse would be overkill, not a ' +
            'violation.'),
          opt(OPT.gray_fifo, false,
            'Gray coding applies to FIFO pointers, not this data bus.')
        ];
        var expl = 'This scenario has two independent CDC mistakes: a ' +
          'multi-bit data bus synchronized as independent bits, and a pulse ' +
          'treated as a level. Both must be fixed, typically with an async ' +
          'FIFO for the stream and a pulse-toggle synchronizer for the event.';
        return makeSpot(this.id, this.tier, stem, diagram, options, expl);
      }
    }
  ];

  // -- picker scenario generators --------------------------------------------

  function makePicker(id, tier, stem, options, explanation) {
    return {
      id: id,
      mode: 'picker',
      tier: tier,
      stem: stem,
      options: options,
      explanation: explanation
    };
  }

  function pickerOpt(text, correct, explanation) {
    return { text: text, correct: correct, explanation: explanation };
  }

  var SYNC_2FLOP = 'Plain 2-flop synchronizer';
  var SYNC_PULSE = 'Pulse-toggle synchronizer';
  var SYNC_HANDSHAKE = 'Request/acknowledge handshake';
  var SYNC_FIFO = 'Asynchronous FIFO';
  var SYNC_RESET = 'Reset synchronizer (async assert, synced deassert)';

  var pickerGenerators = [
    {
      id: 'single_bit_level',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var period = CDCD.rint(rng, 4, 20);
        var stem = mA + ' (' + src + ') asserts a status flag ' + sig +
          ' that stays high for at least ' + period + ' ' + dst +
          ' cycles before it may deassert. ' + mB + ' (' + dst +
          ') just needs to know whether ' + sig + ' is currently 1.';
        var options = [
          pickerOpt(SYNC_2FLOP, true,
            'Correct. A level that is stable for many destination cycles can ' +
            'be safely sampled by a 2-flop synchronizer.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer converts edges to pulses and is ' +
            'meant for events, not for reading a steady level.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake adds unnecessary latency and area for a simple status flag.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO is overkill for a single-bit level.')
        ];
        var expl = 'For a single-bit level signal that is stable for many ' +
          'destination cycles, a plain 2-flop synchronizer is the standard, ' +
          'minimal solution.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'single_cycle_pulse',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var sig = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') generates a single-cycle ' + sig +
          ' pulse to tell ' + mB + ' (' + dst +
          ') that one item is ready. The destination must see exactly one ' +
          'event per source pulse and must not miss any pulses.';
        var options = [
          pickerOpt(SYNC_PULSE, true,
            'Correct. A pulse-toggle synchronizer converts each single-cycle ' +
            'pulse into a toggle, safely crosses it, and converts it back to ' +
            'a single destination pulse.'),
          pickerOpt(SYNC_2FLOP, false,
            'A plain 2-flop chain may miss a pulse narrower than the ' +
            'destination clock period or sample it as a level.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO works but adds latency and area for a single event.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake guarantees delivery but is overkill and slower for ' +
            'a single event.')
        ];
        var expl = 'Single-cycle pulses should cross through a pulse-toggle ' +
          'synchronizer so each source event produces exactly one destination ' +
          'event without loss.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'multibit_simultaneous_bus',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var bus = busName(rng);
        var w = bitWidth(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') produces a ' + w + '-bit ' + bus +
          ' whose bits all change together on the same ' + src +
          ' cycle. ' + mB + ' (' + dst +
          ') must capture the entire word coherently.';
        var options = [
          pickerOpt(SYNC_FIFO, true,
            'Correct. An async FIFO moves complete data words across clock ' +
            'domains using Gray-coded pointers and a valid/data protocol.'),
          pickerOpt(SYNC_2FLOP, false,
            'Synchronizing each bit independently can sample an incoherent word.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer carries one event, not a multi-bit word.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake can move a word but is lower throughput than a FIFO ' +
            'and adds round-trip latency.')
        ];
        var expl = 'A multi-bit bus that must be captured coherently needs an ' +
          'async FIFO (or a req/ack handshake if throughput is low). Plain ' +
          '2-flop sync on each bit risks sampling a corrupted value.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'req_ack_command',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var cmd = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var w = CDCD.rint(rng, 4, 16);
        var stem = mA + ' (' + src + ') occasionally sends a ' + w +
          '-bit command ' + cmd + ' to ' + mB + ' (' + dst +
          '). Commands are rare but must never be lost or reordered. ' + mB +
          ' may take several ' + dst + ' cycles to act.';
        var options = [
          pickerOpt(SYNC_HANDSHAKE, true,
            'Correct. A req/ack handshake guarantees lossless, ordered ' +
            'delivery of occasional command words.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO also works but adds area; a handshake is simpler ' +
            'for rare commands.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain cannot safely move a multi-bit command word.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer carries events, not data words.')
        ];
        var expl = 'For infrequent command or control words that must be ' +
          'delivered reliably, a req/ack handshake is the natural choice. ' +
          'It gives explicit acknowledgment and preserves ordering.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'high_throughput_stream',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var word = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var w = CDCD.rint(rng, 16, 64);
        var stem = mA + ' (' + src + ') produces a sustained stream of ' + w +
          '-bit ' + word + ' words at roughly one word per ' + src +
          ' cycle. ' + mB + ' (' + dst +
          ') consumes them at the same average rate but on a different clock.';
        var options = [
          pickerOpt(SYNC_FIFO, true,
            'Correct. An async FIFO absorbs the clock-rate mismatch and ' +
            'supports sustained one-word-per-cycle throughput.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake needs a round trip per word and cannot sustain ' +
            'word-per-cycle throughput.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain cannot move a multi-bit data word coherently.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer carries single events, not data streams.')
        ];
        var expl = 'High-throughput streaming across clocks needs buffering. ' +
          'An async FIFO provides the throughput and elasticity that a ' +
          'handshake cannot.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'latency_tolerant_lossless',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var pkt = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var w = CDCD.rint(rng, 32, 128);
        var stem = mA + ' (' + src + ') sends variable-length ' + w +
          '-bit ' + pkt + ' packets to ' + mB + ' (' + dst +
          '). Packets must arrive without loss or duplication. Latency of a ' +
          'few tens of cycles is acceptable.';
        var options = [
          pickerOpt(SYNC_FIFO, true,
            'Correct. An async FIFO buffers packets and absorbs rate mismatch ' +
            'while preserving every word.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer cannot carry packet data.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain cannot move wide packet words coherently.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake is lossless but cannot sustain packet throughput; ' +
            'a FIFO is the standard packet-CDC structure.')
        ];
        var expl = 'When losslessness matters and latency can be tolerated, ' +
          'an async FIFO is the right structure. It decouples the clocks and ' +
          'guarantees every word crosses.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'power_of_two_queue',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var q = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var depth = 1 << CDCD.rint(rng, 3, 6);
        var w = CDCD.rint(rng, 8, 32);
        var stem = mA + ' (' + src + ') writes ' + w + '-bit ' + q +
          ' entries into a queue of depth ' + depth +
          ' (a power of two). ' + mB + ' (' + dst +
          ') reads them independently on a different clock.';
        var options = [
          pickerOpt(SYNC_FIFO, true,
            'Correct. An async FIFO is exactly a queue that crosses clock ' +
            'domains; power-of-two depth simplifies Gray-code pointer sync.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake is not a queue and cannot buffer ' + depth +
            ' entries.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain cannot store or move queue entries.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer is for events, not queued data.')
        ];
        var expl = 'A power-of-two deep queue that is written and read by ' +
          'different clocks is an asynchronous FIFO. The depth choice makes ' +
          'Gray-code pointer synchronization straightforward.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'infrequent_status_flag',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var flag = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') raises a level ' + flag +
          ' when a long operation is complete. The flag changes at most once ' +
          'every several ' + dst + ' cycles. ' + mB + ' (' + dst +
          ') polls ' + flag + ' to decide when to proceed.';
        var options = [
          pickerOpt(SYNC_2FLOP, true,
            'Correct. A slowly changing level is the canonical use case for ' +
            'a 2-flop synchronizer.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer would turn the level edge into a ' +
            'pulse, which is not what polling wants.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO is unnecessary area for one status bit.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake is overkill for a one-way status flag with no data.')
        ];
        var expl = 'Slowly changing single-bit status flags are safely moved ' +
          'with a 2-flop synchronizer. The destination polls the synchronized ' +
          'level and acts when it sees the change.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'reset_deassertion',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var rst = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') generates an asynchronous reset ' +
          rst + ' that must reach flops in ' + mB + ' (' + dst +
          '). The reset must assert immediately but release cleanly in ' +
          dst + '.';
        var options = [
          pickerOpt(SYNC_RESET, true,
            'Correct. A reset synchronizer asserts asynchronously and ' +
            'synchronizes the deassertion edge to the destination clock.'),
          pickerOpt(SYNC_2FLOP, false,
            'A plain 2-flop synchronizer does not provide asynchronous ' +
            'assertion; the reset would not act immediately.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake is not a reset distribution mechanism.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO does not distribute resets.')
        ];
        var expl = 'Asynchronous reset distribution across clocks needs a ' +
          'reset synchronizer: assert asynchronously for immediate effect, ' +
          'but synchronize the deassertion to the receiving clock to avoid ' +
          'recovery/removal violations.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'slow_control_bus',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var cfg = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var w = CDCD.rint(rng, 4, 16);
        var stem = mA + ' (' + src + ') occasionally updates a ' + w +
          '-bit configuration ' + cfg + ' register in ' + mB + ' (' + dst +
          '). Updates are rare and must be atomic; ' + mB +
          ' acknowledges each update.';
        var options = [
          pickerOpt(SYNC_HANDSHAKE, true,
            'Correct. A handshake atomically transfers a multi-bit control ' +
            'word and gives explicit acknowledgment.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain cannot guarantee atomic capture of a multi-bit ' +
            'control word.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO works but is heavier than needed for rare updates.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer cannot carry data.')
        ];
        var expl = 'For rare, atomic multi-bit control writes, a req/ack ' +
          'handshake is a clean solution. It ensures the whole word arrives ' +
          'together and is acknowledged.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'burst_events',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var evt = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var n = CDCD.rint(rng, 3, 8);
        var stem = mA + ' (' + src + ') can produce back-to-back single-cycle ' +
          evt + ' events, up to ' + n +
          ' events in a burst. ' + mB + ' (' + dst +
          ') must receive every event in order.';
        var options = [
          pickerOpt(SYNC_FIFO, true,
            'Correct. An async FIFO preserves ordering and can absorb a ' +
            'burst of events without loss.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer cannot queue bursts; back-to-back ' +
            'pulses may collide if the destination is slower.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain can miss pulses and has no buffering.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake preserves ordering but adds a round trip per event; ' +
            'a FIFO handles bursts more efficiently.')
        ];
        var expl = 'Bursts of events need buffering. An async FIFO queues the ' +
          'events and lets the destination drain them at its own rate while ' +
          'preserving order.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'single_event_no_order',
      tier: 1,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var evt = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var stem = mA + ' (' + src + ') produces isolated single-cycle ' + evt +
          ' events. ' + mB + ' (' + dst +
          ') only needs to know that one event happened; there is no data and ' +
          'no ordering requirement.';
        var options = [
          pickerOpt(SYNC_PULSE, true,
            'Correct. A pulse-toggle synchronizer is the minimal structure ' +
            'for isolated single-cycle events.'),
          pickerOpt(SYNC_2FLOP, false,
            'A 2-flop chain can miss a pulse that is narrower than the ' +
            'destination clock period.'),
          pickerOpt(SYNC_FIFO, false,
            'An async FIFO is overkill for a single event with no data.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A handshake adds latency and complexity for a simple event.')
        ];
        var expl = 'When only the existence of an event matters and there is ' +
          'no data or ordering, a pulse-toggle synchronizer is the right ' +
          'choice.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'small_count_value',
      tier: 3,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var cnt = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var max = CDCD.rint(rng, 7, 15);
        var stem = mA + ' (' + src + ') maintains a 4-bit counter ' + cnt +
          ' that increments at most once per ' + src +
          ' cycle and saturates at ' + max +
          '. ' + mB + ' (' + dst +
          ') needs the exact counter value atomically, but only when ' + mA +
          ' says it is valid.';
        var options = [
          pickerOpt(SYNC_HANDSHAKE, true,
            'Correct. A handshake can transfer the multi-bit counter value ' +
            'atomically with a valid signal.'),
          pickerOpt(SYNC_2FLOP, false,
            'Synchronizing each counter bit independently can capture a ' +
            'corrupted intermediate value.'),
          pickerOpt(SYNC_FIFO, false,
            'A FIFO works but is heavier than a handshake for one slow ' +
            'counter sample.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer cannot carry a count value.')
        ];
        var expl = 'A multi-bit counter value that must be sampled atomically ' +
          'should cross through a handshake (or FIFO), not independent ' +
          '2-flop chains.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    },
    {
      id: 'periodic_heartbeat',
      tier: 2,
      generate: function (rng) {
        var pair = pairNames(rng);
        var src = pair[0];
        var dst = pair[1];
        var hb = signalName(rng);
        var mA = moduleName(rng);
        var mB = moduleName(rng);
        var period = CDCD.rint(rng, 8, 32);
        var stem = mA + ' (' + src + ') toggles a ' + hb +
          ' signal every ' + period + ' ' + src +
          ' cycles as a keep-alive. ' + mB + ' (' + dst +
          ') samples it and declares failure if it does not see a toggle for ' +
          'a long time.';
        var options = [
          pickerOpt(SYNC_2FLOP, true,
            'Correct. A slow toggle is just a level in disguise; a 2-flop ' +
            'synchronizer lets the destination see the new level safely.'),
          pickerOpt(SYNC_PULSE, false,
            'A pulse-toggle synchronizer would produce a pulse on every edge ' +
            'but is unnecessary here; the destination only cares about level.'),
          pickerOpt(SYNC_HANDSHAKE, false,
            'A heartbeat needs no acknowledgment.'),
          pickerOpt(SYNC_FIFO, false,
            'A single-bit heartbeat does not need a FIFO.')
        ];
        var expl = 'A periodic heartbeat is a slowly toggling level. A plain ' +
          '2-flop synchronizer is sufficient because the destination only ' +
          'needs to detect that the level has changed.';
        return makePicker(this.id, this.tier, stem, options, expl);
      }
    }
  ];

  // -- public API ------------------------------------------------------------

  function findGenerator(generators, id) {
    for (var i = 0; i < generators.length; i++) {
      if (generators[i].id === id) {
        return generators[i];
      }
    }
    return null;
  }

  function generateSpot(id, rng) {
    var gen = findGenerator(spotGenerators, id);
    if (!gen) {
      throw new Error('unknown spot generator: ' + id);
    }
    return gen.generate(rng);
  }

  function generatePicker(id, rng) {
    var gen = findGenerator(pickerGenerators, id);
    if (!gen) {
      throw new Error('unknown picker generator: ' + id);
    }
    return gen.generate(rng);
  }

  function generateAllQuestions(rng, tiers) {
    var enabled = tiers || { 1: true, 2: true, 3: true };
    var out = [];
    for (var i = 0; i < spotGenerators.length; i++) {
      var g = spotGenerators[i];
      if (enabled[g.tier]) {
        out.push(g.generate(rng));
      }
    }
    for (var j = 0; j < pickerGenerators.length; j++) {
      var h = pickerGenerators[j];
      if (enabled[h.tier]) {
        out.push(h.generate(rng));
      }
    }
    return out;
  }

  function generateSpotQuestions(rng, tiers) {
    var enabled = tiers || { 1: true, 2: true, 3: true };
    var out = [];
    for (var i = 0; i < spotGenerators.length; i++) {
      var g = spotGenerators[i];
      if (enabled[g.tier]) {
        out.push(g.generate(rng));
      }
    }
    return out;
  }

  function generatePickerQuestions(rng, tiers) {
    var enabled = tiers || { 1: true, 2: true, 3: true };
    var out = [];
    for (var j = 0; j < pickerGenerators.length; j++) {
      var h = pickerGenerators[j];
      if (enabled[h.tier]) {
        out.push(h.generate(rng));
      }
    }
    return out;
  }

  // validateQuestion(q) -> {ok, errors[]}
  // Enforces the content contract: answers/options distinct, plausible,
  // correct first convention where applicable, explanation present, ASCII only.
  function validateQuestion(q) {
    var errors = [];
    if (!q || typeof q !== 'object') {
      return { ok: false, errors: ['question is not an object'] };
    }
    if (q.mode !== 'spot' && q.mode !== 'picker') {
      errors.push('mode must be spot or picker');
    }
    if (q.tier !== 1 && q.tier !== 2 && q.tier !== 3) {
      errors.push('tier must be 1, 2, or 3');
    }
    if (!q.stem || typeof q.stem !== 'string') {
      errors.push('stem missing');
    }
    if (!Array.isArray(q.options) || q.options.length < 2) {
      errors.push('options must be an array of length >= 2');
    }
    if (!q.explanation || typeof q.explanation !== 'string') {
      errors.push('explanation missing');
    }

    var opts = q.options || [];
    var texts = [];
    var correctCount = 0;
    for (var k = 0; k < opts.length; k++) {
      var o = opts[k];
      if (!o || typeof o !== 'object') {
        errors.push('option[' + k + '] not an object');
        continue;
      }
      if (!o.text || typeof o.text !== 'string') {
        errors.push('option[' + k + '] text missing');
      } else {
        texts.push(o.text);
      }
      if (!o.explanation || typeof o.explanation !== 'string') {
        errors.push('option[' + k + '] explanation missing');
      }
      if (o.correct === true) {
        correctCount++;
      }
    }

    var unique = uniqueStrings(texts);
    if (unique.length !== texts.length) {
      errors.push('option texts are not all distinct');
    }

    if (q.mode === 'spot') {
      if (correctCount < 1) {
        errors.push('spot question needs at least one correct option');
      }
      if (opts.length - correctCount < 1) {
        errors.push('spot question needs at least one incorrect option');
      }
    } else {
      if (correctCount !== 1) {
        errors.push('picker question needs exactly one correct option');
      }
      if (opts.length < 4) {
        errors.push('picker question needs at least 4 options');
      }
    }

    // Correct-first convention: all correct options should precede incorrect
    // options in the source array so shuffling never has to know semantics.
    var seenIncorrect = false;
    for (var m = 0; m < opts.length; m++) {
      if (opts[m].correct) {
        if (seenIncorrect) {
          errors.push('correct option follows incorrect option (correct-first violated)');
          break;
        }
      } else {
        seenIncorrect = true;
      }
    }

    checkAscii(q, 'question', errors);

    return { ok: errors.length === 0, errors: errors };
  }

  CDCD.spotGenerators = spotGenerators;
  CDCD.pickerGenerators = pickerGenerators;
  CDCD.generateSpot = generateSpot;
  CDCD.generatePicker = generatePicker;
  CDCD.generateAllQuestions = generateAllQuestions;
  CDCD.generateSpotQuestions = generateSpotQuestions;
  CDCD.generatePickerQuestions = generatePickerQuestions;
  CDCD.validateQuestion = validateQuestion;
  CDCD.isAscii = isAscii;
})(CDCD);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CDCD;
}
