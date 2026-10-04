// model.js -- pure CRC engine for crc_calc.
//
// Implements the standard generalized CRC algorithm with the same parameter
// semantics as rtl/common/dataint_crc.sv:
//   CRC_POLY   -> POLY        (non-reflected polynomial)
//   CRC_INIT   -> POLY_INIT   (seed loaded into the shift register)
//   CRC_REFIN  -> REFIN       (reflect each input byte before shifting)
//   CRC_REFOUT -> REFOUT      (reflect the final register before XOROUT)
//   CRC_XOROUT -> XOROUT      (final XOR mask)
//   width      -> CRC_WIDTH   (polynomial width, 8/16/32)
//
// Pure functions, no DOM. The same file runs in the browser (CRCX namespace)
// and under node (module.exports).
var CRCX = (typeof window !== 'undefined' ? window : globalThis).CRCX ||
           ((typeof window !== 'undefined' ? window : globalThis).CRCX = {});

(function (CRCX) {
  'use strict';

  // Unsigned 32-bit normalization. JavaScript bitwise operators yield signed
  // 32-bit integers, so every arithmetic step that may touch the high bit is
  // forced back into the unsigned range with >>> 0.
  function u32(x) { return (x >>> 0); }

  function crcMask(width) {
    if (width >= 32) { return 0xFFFFFFFF; }
    return (1 << width) - 1;
  }

  // Reflect the low `width` bits of v. width <= 32.
  function reflectBits(v, width) {
    var r = 0;
    var i;
    for (i = 0; i < width; i += 1) {
      r = u32((r << 1) | ((v >>> i) & 1));
    }
    return u32(r & crcMask(width));
  }

  // Standard parameterized CRC. bytes is an array of integer octets.
  // Returns {result, perByteSteps:[{byte, registerAfter, bitSteps:[{bit, registerAfter, xorApplied}]}]}.
  function computeCRC(params, bytes) {
    var width = params.width;
    var poly = u32(params.CRC_POLY);
    var init = u32(params.CRC_INIT);
    var refin = !!params.CRC_REFIN;
    var refout = !!params.CRC_REFOUT;
    var xorout = u32(params.CRC_XOROUT);
    var mask = crcMask(width);
    var reg = u32(init & mask);
    var perByteSteps = [];
    var i, j, b, top;

    for (i = 0; i < bytes.length; i += 1) {
      b = bytes[i] & 0xFF;
      if (refin) {
        b = reflectBits(b, 8);
      }
      reg = u32((reg ^ u32(b << (width - 8))) & mask);

      var bitSteps = [];
      for (j = 0; j < 8; j += 1) {
        top = (reg >>> (width - 1)) & 1;
        reg = u32(reg << 1);
        if (top) {
          reg = u32(reg ^ poly);
        }
        reg = u32(reg & mask);
        bitSteps.push({bit: j, registerAfter: reg, xorApplied: !!top});
      }
      perByteSteps.push({byte: bytes[i] & 0xFF, registerAfter: reg, bitSteps: bitSteps});
    }

    if (refout) {
      reg = reflectBits(reg, width);
    }
    reg = u32((reg ^ xorout) & mask);

    return {result: reg, perByteSteps: perByteSteps};
  }

  var PRESETS = [
    {
      name: 'CRC-8',
      params: {CRC_POLY: 0x07, CRC_INIT: 0x00, CRC_REFIN: false,
               CRC_REFOUT: false, CRC_XOROUT: 0x00, width: 8},
      check: 0xF4,
      note: 'SMBus, PMBus; classic MSB-first CRC-8.'
    },
    {
      name: 'CRC-16/CCITT-FALSE',
      params: {CRC_POLY: 0x1021, CRC_INIT: 0xFFFF, CRC_REFIN: false,
               CRC_REFOUT: false, CRC_XOROUT: 0x0000, width: 16},
      check: 0x29B1,
      note: 'CCITT-FALSE; MSB-first, init all ones.'
    },
    {
      name: 'CRC-16/ARC',
      params: {CRC_POLY: 0x8005, CRC_INIT: 0x0000, CRC_REFIN: true,
               CRC_REFOUT: true, CRC_XOROUT: 0x0000, width: 16},
      check: 0xBB3D,
      note: 'ARC, LHA, FLAC; LSB-first.'
    },
    {
      name: 'CRC-32',
      params: {CRC_POLY: 0x04C11DB7, CRC_INIT: 0xFFFFFFFF, CRC_REFIN: true,
               CRC_REFOUT: true, CRC_XOROUT: 0xFFFFFFFF, width: 32},
      check: 0xCBF43926,
      note: 'IEEE 802.3/Ethernet; LSB-first with inverted init/xorout.'
    }
  ];

  CRCX.reflectBits = reflectBits;
  CRCX.computeCRC = computeCRC;
  CRCX.PRESETS = PRESETS;
})(CRCX);

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CRCX;
}
