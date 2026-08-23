"""
Testbench for axi_data_dnsize module
Tests wide→narrow splitter using proper GAXI components
"""

import os
import sys
import cocotb
from CocoTBFramework.components.shared.flex_config_gen import quick_config
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class AXIDataDnsizeTB(TBBase):
    """
    Testbench class for axi_data_dnsize module using proper GAXI components.

    Architecture:
    - GAXIMaster for wide input (drives valid/data/sideband/last, receives ready)
    - GAXISlave for narrow output (drives ready, receives valid/data/sideband/last)
    - Queue-based verification using ._recvQ
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Extract parameters from DUT
        try:
            self.wide_width = int(dut.WIDE_WIDTH.value)
            self.narrow_width = int(dut.NARROW_WIDTH.value)
            self.wide_sb_width = int(dut.WIDE_SB_WIDTH.value) if hasattr(dut, 'WIDE_SB_WIDTH') else 0
            self.narrow_sb_width = int(dut.NARROW_SB_WIDTH.value) if hasattr(dut, 'NARROW_SB_WIDTH') else 0
            self.sb_broadcast = bool(int(dut.SB_BROADCAST.value)) if hasattr(dut, 'SB_BROADCAST') else True
            self.track_bursts = bool(int(dut.TRACK_BURSTS.value)) if hasattr(dut, 'TRACK_BURSTS') else False
            self.width_ratio = self.wide_width // self.narrow_width
        except:
            # Fallback if parameters not accessible
            self.wide_width = 128
            self.narrow_width = 32
            self.wide_sb_width = 2
            self.narrow_sb_width = 2
            self.sb_broadcast = True
            self.track_bursts = False
            self.width_ratio = 4

        # Initialize GAXI components
        self._init_gaxi_components()

        self.log.info(f"Initialized AXI Data Dnsize TB: {self.wide_width}→{self.narrow_width}, "
                      f"ratio={self.width_ratio}, sb_mode={'broadcast' if self.sb_broadcast else 'slice'}, "
                      f"track_bursts={self.track_bursts}")

    def _init_gaxi_components(self):
        """Initialize GAXI master and slave components"""

        # Wide input - GAXIMaster drives the converter input
        wide_field_config = FieldConfig()
        wide_field_config.add_field(FieldDefinition(name='data', bits=self.wide_width, default=0))
        if self.wide_sb_width > 0:
            wide_field_config.add_field(FieldDefinition(name='sideband', bits=self.wide_sb_width, default=0))
        wide_field_config.add_field(FieldDefinition(name='last', bits=1, default=0))

        self.wide_master = GAXIMaster(
            dut=self.dut,
            title="WIDE_IN",
            prefix="wide_",
            clock=self.clk,
            field_config=wide_field_config,
            pkt_prefix="",
            multi_sig=True,
            log=self.log
        )

        # Narrow output - GAXISlave monitors the converter output
        narrow_field_config = FieldConfig()
        narrow_field_config.add_field(FieldDefinition(name='data', bits=self.narrow_width, default=0))
        if self.narrow_sb_width > 0:
            narrow_field_config.add_field(FieldDefinition(name='sideband', bits=self.narrow_sb_width, default=0))
        narrow_field_config.add_field(FieldDefinition(name='last', bits=1, default=0))

        self.narrow_slave = GAXISlave(
            dut=self.dut,
            title="NARROW_OUT",
            prefix="narrow_",
            clock=self.clk,
            field_config=narrow_field_config,
            pkt_prefix="",
            multi_sig=True,
            log=self.log
        )

    # =========================================================================
    # MANDATORY METHODS - Required by TBBase
    # =========================================================================

    async def setup_clocks_and_reset(self, period_ns=10):
        """Complete initialization - start clocks and perform reset"""
        # Start clock
        # recorded so cycle-counting measurements do not hardcode it
        self.clk_period_ns = period_ns
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')

        # Initialize burst tracking signals if needed
        if self.track_bursts:
            self.dut.burst_len.value = 0
            self.dut.burst_start.value = 0

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 2)

        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    # =========================================================================
    # TEST UTILITY METHODS
    # =========================================================================

    async def start_burst(self, burst_len):
        """
        Start a new burst (only if TRACK_BURSTS=1)

        Args:
            burst_len: Burst length (encoded as beats-1)
        """
        if self.track_bursts:
            self.dut.burst_len.value = burst_len
            self.dut.burst_start.value = 1
            await self.wait_clocks(self.clk_name, 1)
            self.dut.burst_start.value = 0

    async def send_wide_beat(self, data, sideband=0, last=False):
        """
        Send a wide beat using GAXI master

        Args:
            data: Data value
            sideband: Sideband value (WSTRB or RRESP)
            last: Assert wide_last
        """
        # Create packet with generic field names
        pkt_dict = {
            'data': data,
            'last': 1 if last else 0
        }
        if self.wide_sb_width > 0:
            pkt_dict['sideband'] = sideband

        wide_pkt = self.wide_master.create_packet(**pkt_dict)
        await self.wide_master.send(wide_pkt)

    def get_narrow_beats(self, count=None, clear=False):
        """
        Get narrow beats from slave receive queue

        Args:
            count: Number of beats to retrieve (None = all)
            clear: Clear queue after retrieval

        Returns:
            List of (data, sideband, last) tuples
        """
        beats = []
        queue_len = len(self.narrow_slave._recvQ)

        if count is None:
            count = queue_len

        for i in range(min(count, queue_len)):
            pkt = self.narrow_slave._recvQ[i] if not clear else self.narrow_slave._recvQ.popleft()
            data = getattr(pkt, 'data', 0)
            sideband = getattr(pkt, 'sideband', 0) if self.narrow_sb_width > 0 else 0
            last = bool(getattr(pkt, 'last', 0))
            beats.append((data, sideband, last))

        return beats

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================


    async def measure_throughput(self, wide_beats=16, label=""):
        """Measure sustained narrow-side throughput with no backpressure.

        The book's central performance claim is that single-buffer mode
        costs one gap cycle per wide beat (N/(N+1), "80%"), and that dual
        buffer exists to recover it. The RTL says otherwise: simple mode
        asserts `wide_ready` DURING the last narrow beat
        (`!r_wide_buffered || (narrow_ready && w_last_narrow_beat)`), so the
        next wide beat lands with no bubble. A claim about cycles should be
        measured, not read off the source, so this counts them.

        Returns beats-per-cycle over the steady-state window: 1.0 means a
        narrow beat every cycle, which is the most the narrow side can carry.
        """
        tag = f"[{label}] " if label else ""

        # TRACK_BURSTS mode is deliberately NOT measured here. Its replace
        # condition (`mid_burst_replace`) needs a framed burst, and driving
        # one long enough to measure leaves the module mid-burst for the
        # scenario that follows -- it corrupted the burst-tracking test when
        # tried. Characterizing that mode needs its own scenario.
        if getattr(self, 'track_bursts', False):
            self.log.info(f"{tag}skipped: TRACK_BURSTS needs framed bursts, "
                          f"see the note in measure_throughput")
            return None

        self.get_narrow_beats(clear=True)

        # Drive both sides with the shared 'backtoback' profile. With the
        # default randomizers this measures the testbench's own pacing
        # rather than the DUT -- the first run of this came back at 13-24%,
        # which says nothing about the converter. Saved and restored so the
        # other scenarios keep their randomized behaviour.
        saved = (getattr(self.wide_master, 'randomizer', None),
                 getattr(self.narrow_slave, 'randomizer', None))
        b2b = quick_config(profiles=['backtoback'],
                           fields=['valid_delay', 'ready_delay']).build()
        self.wide_master.set_randomizer(b2b['backtoback'])
        self.narrow_slave.set_randomizer(b2b['backtoback'])

        # QUEUE every beat first, then time the drain. `send()` waits for
        # completion and then an extra clock edge, so sending in a loop puts
        # a bubble between beats that belongs to the harness, not the DUT --
        # measuring that way produced ~1 lost cycle per wide beat, which is
        # exactly the effect under investigation. _driver_send() enqueues
        # without waiting, so the master can present beats back to back.
        for i in range(wide_beats):
            pkt_dict = {'data': 0xA5A50000 + i,
                        'last': 1 if i == wide_beats - 1 else 0}
            if self.wide_sb_width > 0:
                pkt_dict['sideband'] = 0
            await self.wide_master._driver_send(
                self.wide_master.create_packet(**pkt_dict), sync=True)
        start = get_sim_time('ns')
        # let the tail drain
        expect = wide_beats * self.width_ratio
        for _ in range(expect * 4 + 100):
            if len(self.get_narrow_beats()) >= expect:
                break
            await self.wait_clocks(self.clk_name, 1)
        end = get_sim_time('ns')

        if saved[0] is not None:
            self.wide_master.set_randomizer(saved[0])
        if saved[1] is not None:
            self.narrow_slave.set_randomizer(saved[1])

        got = len(self.get_narrow_beats())
        cycles = (end - start) / self.clk_period_ns
        if got < expect:
            self.log.error(f"@ {end}ns: {tag}only {got}/{expect} narrow beats "
                           f"arrived; cannot measure throughput")
            self.stats['errors'] = self.stats.get('errors', 0) + 1
            return None
        rate = got / cycles if cycles else 0
        self.log.info(f"@ {end}ns: {tag}{got} narrow beats in {cycles:.0f} "
                      f"cycles = {rate:.3f} beats/cycle "
                      f"({100.0 * rate:.1f}% of the narrow-side maximum)")
        return rate


    async def measure_burst_throughput(self, bursts=8, wide_per_burst=8,
                                       label=""):
        """Throughput in TRACK_BURSTS mode, where the cost is per BURST.

        The replace condition here is `mid_burst_replace`, which requires a
        burst to be active AND more beats to remain:

            mid_burst_replace = r_burst_active
                                && (r_beat_ptr == WIDTH_RATIO-1)
                                && ((r_slave_beat_count + 1) < r_slave_total_beats)

        The final beat of a burst is excluded, so the module gives up a
        cycle at each burst BOUNDARY -- not at each wide beat, which is what
        the book used to claim. Expected steady state is therefore
        N/(N+1) per burst, where N is the burst's narrow-beat count.

        Each burst is framed and drained completely before the next starts,
        so nothing is left mid-burst for the scenario that follows -- an
        earlier attempt that framed one long burst and let the drain time
        out corrupted the burst-tracking test.
        """
        tag = f"[{label}] " if label else ""
        if not self.track_bursts:
            return None

        saved = (getattr(self.wide_master, 'randomizer', None),
                 getattr(self.narrow_slave, 'randomizer', None))
        b2b = quick_config(profiles=['backtoback'],
                           fields=['valid_delay', 'ready_delay']).build()
        self.wide_master.set_randomizer(b2b['backtoback'])
        self.narrow_slave.set_randomizer(b2b['backtoback'])

        per_burst = wide_per_burst * self.width_ratio
        total_beats = total_cycles = 0
        ok = True
        try:
            for _ in range(bursts):
                self.get_narrow_beats(clear=True)
                await self.start_burst(per_burst - 1)   # narrow-beat framing
                await self.wait_clocks(self.clk_name, 2)

                for i in range(wide_per_burst):
                    pkt = {'data': 0xB0B00000 + i,
                           'last': 1 if i == wide_per_burst - 1 else 0}
                    if self.wide_sb_width > 0:
                        pkt['sideband'] = 0
                    await self.wide_master._driver_send(
                        self.wide_master.create_packet(**pkt), sync=True)

                start = get_sim_time('ns')
                for _ in range(per_burst * 4 + 100):
                    if len(self.get_narrow_beats()) >= per_burst:
                        break
                    await self.wait_clocks(self.clk_name, 1)
                cycles = (get_sim_time('ns') - start) / self.clk_period_ns

                got = len(self.get_narrow_beats())
                if got < per_burst:
                    self.log.error(f"@ {get_sim_time('ns')}ns: {tag}burst "
                                   f"drained {got}/{per_burst}")
                    ok = False
                    break
                total_beats += got
                total_cycles += cycles
                # fully drained before the next burst is framed
                self.get_narrow_beats(clear=True)
                await self.wait_clocks(self.clk_name, 5)
        finally:
            if saved[0] is not None:
                self.wide_master.set_randomizer(saved[0])
            if saved[1] is not None:
                self.narrow_slave.set_randomizer(saved[1])
            await self.wait_clocks(self.clk_name, 10)

        if not ok or not total_cycles:
            self.stats['errors'] = self.stats.get('errors', 0) + 1
            return None
        rate = total_beats / total_cycles
        ideal = per_burst / (per_burst + 1)
        self.log.info(f"@ {get_sim_time('ns')}ns: {tag}{bursts} bursts x "
                      f"{per_burst} narrow beats: {total_beats} beats in "
                      f"{total_cycles:.0f} cycles = {rate:.3f} beats/cycle "
                      f"(one bubble per burst predicts {ideal:.3f})")
        return rate

    async def test_basic_splitting(self, num_transactions=10):
        """
        Test basic splitting: send 1 wide beat,
        expect WIDTH_RATIO narrow beats with correct data slices
        """
        self.log.info(f"Starting basic splitting test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            # Generate wide beat data
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            wide_sideband = random.randint(0, (1 << self.wide_sb_width) - 1) if self.wide_sb_width > 0 else 0

            # Send wide beat using GAXI master
            await self.send_wide_beat(wide_data, wide_sideband, last=False)

            # Poll for the beats rather than waiting a fixed window: the
            # narrow side's ready is randomized, so ratio+5 is a race.
            for _ in range(self.width_ratio * 8 + 100):
                if len(self.get_narrow_beats()) >= self.width_ratio:
                    break
                await self.wait_clocks(self.clk_name, 1)

            # Verify we received WIDTH_RATIO narrow beats
            narrow_beats = self.get_narrow_beats(count=self.width_ratio, clear=True)

            if len(narrow_beats) != self.width_ratio:
                self.log.error(f"Transaction {txn}: Expected {self.width_ratio} narrow beats, got {len(narrow_beats)}")
                return False

            # Verify each narrow beat
            for i, (narrow_data, narrow_sideband, narrow_last) in enumerate(narrow_beats):
                # Extract expected narrow data slice
                expected_data = (wide_data >> (i * self.narrow_width)) & ((1 << self.narrow_width) - 1)

                if narrow_data != expected_data:
                    self.log.error(f"Transaction {txn}, beat {i}: Data mismatch - "
                                   f"expected 0x{expected_data:x}, got 0x{narrow_data:x}")
                    return False

                # Verify sideband
                if self.narrow_sb_width > 0:
                    if self.sb_broadcast:
                        # Broadcast mode: all narrow beats get same sideband
                        expected_sb = wide_sideband
                    else:
                        # Slice mode: extract appropriate slice
                        expected_sb = (wide_sideband >> (i * self.narrow_sb_width)) & ((1 << self.narrow_sb_width) - 1)

                    if narrow_sideband != expected_sb:
                        self.log.error(f"Transaction {txn}, beat {i}: Sideband mismatch - "
                                       f"expected 0x{expected_sb:x}, got 0x{narrow_sideband:x}")
                        return False

        self.log.info(f"✓ Basic splitting test PASSED ({num_transactions} transactions)")
        return True

    async def test_last_propagation(self, num_transactions=5):
        """
        Test that wide_last propagates to last narrow beat
        (only for simple mode, not burst tracking mode)
        """
        if self.track_bursts:
            # Skip this test in burst tracking mode
            self.log.info("Skipping LAST propagation test (burst tracking mode)")
            return True

        self.log.info(f"Starting LAST propagation test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            wide_sideband = random.randint(0, (1 << self.wide_sb_width) - 1) if self.wide_sb_width > 0 else 0

            # Send wide beat with LAST asserted
            await self.send_wide_beat(wide_data, wide_sideband, last=True)

            # Wait for narrow beats
            # Poll for this transaction's full set before reading. On a
            # fixed window the previous transaction's tail is still in the
            # queue, so beat 0 here is really the last beat of the one
            # before -- which is exactly the "expected False, got True"
            # LAST mismatch this used to report.
            for _ in range(self.width_ratio * 8 + 100):
                if len(self.get_narrow_beats()) >= self.width_ratio:
                    break
                await self.wait_clocks(self.clk_name, 1)

            # Get narrow beats
            narrow_beats = self.get_narrow_beats(count=self.width_ratio, clear=True)

            # Check only the last narrow beat has LAST asserted
            for i, (_, _, narrow_last) in enumerate(narrow_beats):
                expected_last = (i == self.width_ratio - 1)
                if narrow_last != expected_last:
                    self.log.error(f"Transaction {txn}, beat {i}: LAST mismatch - "
                                   f"expected {expected_last}, got {narrow_last}")
                    return False

        self.log.info(f"✓ LAST propagation test PASSED ({num_transactions} transactions)")
        return True

    async def test_burst_tracking(self, num_bursts=15):
        """Test burst tracking mode for correct LAST generation"""
        if not self.track_bursts:
            self.log.info("Skipping burst tracking test (simple mode)")
            return True

        self.log.info(f"Starting burst tracking test ({num_bursts} bursts)")
        # CONV-002 intermittency probe: fingerprint the RNG stream. If two
        # same-seed runs print different values here, draws diverged UPSTREAM;
        # if the fingerprint matches but lengths differ, something concurrent
        # is stealing draws mid-scenario.
        import hashlib as _hl
        self.log.info(f"RNG fingerprint at burst_tracking entry: "
                      f"{_hl.md5(repr(random.getstate()).encode()).hexdigest()[:12]}")
        _drawn_lengths = []

        for burst_id in range(num_bursts):
            # Random burst length (1-16 beats, encoded as 0-15)
            burst_len_encoded = random.randint(0, 15)
            _drawn_lengths.append(burst_len_encoded)
            burst_len_beats = burst_len_encoded + 1

            # Empty the queue before framing. Polling for N beats below only
            # proves N ARRIVED, not that they belong to THIS burst -- residue
            # from the previous one satisfies the count early and shifts every
            # index, which reads as a LAST in the wrong place.
            self.get_narrow_beats(clear=True)

            # Start burst
            # burst_len is NARROW beats - 1. In TRACK_BURSTS mode narrow_last
            # is driven ONLY by (r_slave_beat_count + 1 >= r_slave_total_beats),
            # and r_slave_beat_count increments on every narrow beat sent, so
            # framing this in wide beats makes LAST fire WIDTH_RATIO times early.
            await self.start_burst(burst_len_beats * self.width_ratio - 1)
            await self.wait_clocks(self.clk_name, 2)

            # Send burst_len_beats wide beats
            for beat in range(burst_len_beats):
                wide_data = random.randint(0, (1 << self.wide_width) - 1)
                is_last_wide_beat = (beat == burst_len_beats - 1)
                await self.send_wide_beat(wide_data, 0, last=is_last_wide_beat)

            # Wait for all narrow beats
            total_narrow_beats = burst_len_beats * self.width_ratio
            # Poll for this burst's full set. On a fixed window the previous
            # burst's tail is still queued and burst N reads it as its own
            # beat 0 -- which is the "beat 3: expected False, got True" this
            # reported, beat 3 being the previous burst's final beat at
            # ratio 4. The counter itself is correct: see
            # test_burst_len_drives_last, which drives a framed burst with
            # wide_last held low and gets LAST exactly where burst_len says.
            for _ in range(total_narrow_beats * 8 + 200):
                if len(self.get_narrow_beats()) >= total_narrow_beats:
                    break
                await self.wait_clocks(self.clk_name, 1)

            # Let the burst close before the next iteration frames one. The
            # RTL latches burst_len only when a burst is NOT already active
            # (`burst_start && !r_burst_active`), so a start_burst issued
            # while the previous burst is still draining is silently dropped
            # and the next burst inherits the OLD length -- LAST then lands
            # WIDTH_RATIO beats early. Intermittent by nature: it depends on
            # whether the drain had finished, which is why only some random
            # length sequences showed it.
            await self.wait_clocks(self.clk_name, 10)

            # Verify LAST only on final narrow beat
            narrow_beats = self.get_narrow_beats(count=total_narrow_beats, clear=True)

            for i, (_, _, narrow_last) in enumerate(narrow_beats):
                expected_last = (i == total_narrow_beats - 1)
                if narrow_last != expected_last:
                    self.log.error(f"Burst {burst_id}, beat {i}: LAST mismatch - "
                                   f"expected {expected_last}, got {narrow_last}")
                    return False

        self.log.info(f"✓ Burst tracking test PASSED ({num_bursts} bursts); "
                      f"lengths={_drawn_lengths}")
        return True


    async def test_burst_len_drives_last(self, wide_beats=4):
        """narrow_last must come from burst_len, not from wide_last.

        test_burst_tracking asserts `wide_last` on the final wide beat AND
        frames the burst, so a correct narrow_last proves nothing about the
        counter -- the passthrough alone produces it. Framing that test in
        wide beats instead of narrow (a WIDTH_RATIO error) changes nothing
        it observes; it passes either way.

        This drives the burst WITHOUT wide_last, so the only thing that can
        terminate it is `r_slave_beat_count` reaching `r_slave_total_beats`.
        """
        if not self.track_bursts:
            return True

        total_narrow = wide_beats * self.width_ratio
        self.get_narrow_beats(clear=True)
        await self.start_burst(total_narrow - 1)
        await self.wait_clocks(self.clk_name, 2)

        for i in range(wide_beats):
            pkt = {'data': 0xC0DE0000 + i, 'last': 0}       # deliberately no last
            if self.wide_sb_width > 0:
                pkt['sideband'] = 0
            await self.send_wide_beat(pkt['data'], pkt.get('sideband', 0),
                                      last=False)

        # Poll, do not assume: a fixed window here would report a slow
        # drain as a lost beat.
        for _ in range(total_narrow * 8 + 200):
            if len(self.get_narrow_beats()) >= total_narrow:
                break
            await self.wait_clocks(self.clk_name, 1)
        beats = self.get_narrow_beats(clear=True)
        if len(beats) < total_narrow:
            self.log.error(f"@ {get_sim_time('ns')}ns: burst_len-driven LAST: "
                           f"only {len(beats)}/{total_narrow} narrow beats")
            self.stats['errors'] = self.stats.get('errors', 0) + 1
            return False

        lasts = [i for i, (_, _, lst) in enumerate(beats[:total_narrow]) if lst]
        if lasts == [total_narrow - 1]:
            self.log.info(f"@ {get_sim_time('ns')}ns: burst_len-driven LAST "
                          f"asserted on narrow beat {total_narrow - 1}, with "
                          f"no wide_last -- the counter drives it")
            return True
        self.log.error(f"@ {get_sim_time('ns')}ns: burst_len-driven LAST: "
                       f"expected LAST only on beat {total_narrow - 1}, got "
                       f"it on {lasts} -- narrow_last is not coming from "
                       f"burst_len")
        self.stats['errors'] = self.stats.get('errors', 0) + 1
        return False

    async def test_backpressure(self, num_transactions=10):
        """Test backpressure handling"""
        self.log.info(f"Starting backpressure test ({num_transactions} transactions)")

        for txn in range(num_transactions):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)

            # Send wide beat
            await self.send_wide_beat(wide_data, 0, last=False)

            # Random backpressure on narrow output
            for _ in range(self.width_ratio):
                if random.random() < 0.3:  # 30% chance of backpressure
                    await self.wait_clocks(self.clk_name, random.randint(1, 5))

            # Wait for transaction to complete
            await self.wait_clocks(self.clk_name, self.width_ratio + 10)

        # Verify we got all expected beats. Poll for the tail: the per-
        # transaction wait above is a fixed window and this scenario is
        # deliberately slowing the narrow side, so the last transaction can
        # still be draining when the loop ends.
        expected_total = num_transactions * self.width_ratio
        for _ in range(expected_total * 4 + 200):
            if len(self.narrow_slave._recvQ) >= expected_total:
                break
            await self.wait_clocks(self.clk_name, 1)
        actual_total = len(self.narrow_slave._recvQ)

        if actual_total != expected_total:
            self.log.error(f"Backpressure test: Expected {expected_total} beats, got {actual_total}")
            return False

        self.log.info(f"✓ Backpressure test PASSED ({num_transactions} transactions)")
        return True

    async def test_continuous_streaming(self, num_wide_beats=30):
        """Test continuous streaming without gaps"""
        self.log.info(f"Starting continuous streaming test ({num_wide_beats} wide beats)")

        # Send multiple wide beats back-to-back
        for beat in range(num_wide_beats):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            await self.send_wide_beat(wide_data, 0, last=False)

        # Wait for all narrow beats to complete
        expected_narrow_beats = num_wide_beats * self.width_ratio
        await self.wait_clocks(self.clk_name, expected_narrow_beats + 20)

        # Verify count
        actual_narrow_beats = len(self.narrow_slave._recvQ)
        if actual_narrow_beats != expected_narrow_beats:
            self.log.error(f"Continuous streaming: Expected {expected_narrow_beats} beats, got {actual_narrow_beats}")
            return False

        self.log.info(f"✓ Continuous streaming test PASSED ({num_wide_beats} wide beats)")
        return True
