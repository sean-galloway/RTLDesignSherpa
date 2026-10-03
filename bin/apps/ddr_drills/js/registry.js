// registry.js -- DDRD namespace root, pack registry, pack schema validation.
// Dual-environment: plain <script> tag in the browser (window.DDRD),
// require()-able in node unchanged (globalThis.DDRD). ES modules are banned
// so the app works from file:// (module fetches are CORS-blocked there).
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});

(function (DDRD) {
  'use strict';

  var packs = {};

  function isAscii(s) {
    return typeof s === 'string' && /^[\x00-\x7F]*$/.test(s);
  }

  function checkAsciiStrings(value, path, errors) {
    if (typeof value === 'string') {
      if (!isAscii(value)) {
        errors.push('non-ASCII string at ' + path);
      }
    } else if (Array.isArray(value)) {
      for (var i = 0; i < value.length; i++) {
        checkAsciiStrings(value[i], path + '[' + i + ']', errors);
      }
    } else if (value && typeof value === 'object') {
      for (var k in value) {
        if (Object.prototype.hasOwnProperty.call(value, k)) {
          checkAsciiStrings(value[k], path + '.' + k, errors);
        }
      }
    }
  }

  // validatePack(pack) -> {ok, errors[]}
  // Enforces the pack registration schema (see notes/design.md). Structural
  // checks only; content correctness (JEDEC citations) is an authoring
  // concern, not a registry concern.
  function validatePack(pack) {
    var errors = [];

    if (!pack || typeof pack !== 'object') {
      return { ok: false, errors: ['pack is not an object'] };
    }
    if (!isAscii(pack.id || '')) {
      errors.push('id missing or non-ASCII');
    }
    if (!isAscii(pack.name || '')) {
      errors.push('name missing or non-ASCII');
    }

    var topo = pack.topology;
    if (!topo || typeof topo !== 'object') {
      errors.push('topology missing');
    } else {
      if (typeof topo.banks !== 'number' || topo.banks < 1) {
        errors.push('topology.banks must be a positive number');
      }
      if (typeof topo.rows !== 'number' || topo.rows < 1) {
        errors.push('topology.rows must be a positive number');
      }
      if (typeof topo.cols !== 'number' || topo.cols < 1) {
        errors.push('topology.cols must be a positive number');
      }
      if (topo.hasBankGroups) {
        if (typeof topo.groups !== 'number' || typeof topo.banksPerGroup !== 'number') {
          errors.push('topology.groups and topology.banksPerGroup required when hasBankGroups');
        } else if (topo.groups * topo.banksPerGroup !== topo.banks) {
          errors.push('topology: banks != groups * banksPerGroup');
        }
      }
      if (typeof topo.sids !== 'number' || topo.sids < 0) {
        errors.push('topology.sids must be a number >= 0 (0 = no stack IDs)');
      }
    }

    if (!Array.isArray(pack.commands) || pack.commands.length === 0) {
      errors.push('commands must be a non-empty array');
    }

    var qb = pack.questionBank || [];
    if (!Array.isArray(qb)) {
      errors.push('questionBank must be an array');
      qb = [];
    }
    for (var i = 0; i < qb.length; i++) {
      var q = qb[i];
      if (!isAscii(q.q || '')) {
        errors.push('questionBank[' + i + '].q missing or non-ASCII');
      }
      if (!Array.isArray(q.answers) || q.answers.length < 2) {
        errors.push('questionBank[' + i + '] needs >= 2 answers (correct first)');
      }
      if (!isAscii(q.explanation || '')) {
        errors.push('questionBank[' + i + '].explanation missing or non-ASCII');
      }
    }

    var tp = pack.timingParams || [];
    if (!Array.isArray(tp)) {
      errors.push('timingParams must be an array');
      tp = [];
    }
    for (var j = 0; j < tp.length; j++) {
      var p = tp[j];
      if (!isAscii(p.symbol || '')) {
        errors.push('timingParams[' + j + '].symbol missing or non-ASCII');
      }
      if (!Array.isArray(p.appliesTo) || p.appliesTo.length < 1) {
        errors.push('timingParams[' + j + '] needs >= 1 appliesTo rule');
      }
    }

    checkAsciiStrings(pack, 'pack', errors);

    return { ok: errors.length === 0, errors: errors };
  }

  // registerPack(pack) -- validates and registers; throws on schema errors
  // or duplicate id. Pack files are IIFEs ending in DDRD.registerPack({...}).
  function registerPack(pack) {
    var result = validatePack(pack);
    if (!result.ok) {
      throw new Error('invalid pack "' + (pack && pack.id) + '": ' +
                      result.errors.join('; '));
    }
    if (packs[pack.id]) {
      throw new Error('duplicate pack id: ' + pack.id);
    }
    packs[pack.id] = pack;
    return pack;
  }

  function listPacks() {
    var out = [];
    for (var id in packs) {
      if (Object.prototype.hasOwnProperty.call(packs, id)) {
        out.push(packs[id]);
      }
    }
    return out;
  }

  function getPack(id) {
    return packs[id] || null;
  }

  // Test hook: clears the registry. Not used by pack files.
  function _resetPacks() {
    packs = {};
  }

  DDRD.validatePack = validatePack;
  DDRD.registerPack = registerPack;
  DDRD.listPacks = listPacks;
  DDRD.getPack = getPack;
  DDRD._resetPacks = _resetPacks;
})(DDRD);
