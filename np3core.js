/* np3core.js —— NP2/NP3 → NCP 内核（浏览器端，纯静态，无后端）
 *
 * 这是 np3core.py 的逐函数移植：格式解析、机身曲线预补偿、标定图反解、库匹配。
 * 所有计算都在浏览器里完成，文件不上传。
 *
 * 三个必须记住的事实：
 *   1. NP3 文件里没有曲线，只有一个 2 字节的「底子编号」；
 *   2. 机身执行的是 C(H(x))，写文件前必须把目标曲线用 H⁻¹ 预补偿；
 *   3. NCP 的 LUT 满量程是 32767，不是 255。
 */
(function (global) {
  'use strict';

  /* ---------------------------------------------------------- 常量 */

  var OUT_MAX = 32767;            // NCP 曲线满量程（15 位）
  var HDR_LEN = 64;               // 曲线记录头部
  var MAX_PTS = 20;               // 控制点上限
  var REC2_LEN = 578;             // 64 + 257×2
  var HDR_PREFIX = [0x49, 0x30, 0x00, 0xFF, 0x00, 0xFF, 0x01, 0x00];

  var SL_ZERO = 0x80, SL_NA = 0xFF, SL_CURVE = 0x01;
  var MONO_BASE = 0x064D, COLOR_BASE = 0x0001;

  var SAT_STEP = 1.13;            // 饱和度每档 → 彩度 ×1.13（实拍标定）
  var HUE_STEP = 3.5;             // 色相每档 → 3.5°

  var NP_BASE_NAME = {
    0x0801: 'DREAM', 0x0802: 'MORNING', 0x0803: 'POP', 0x0804: 'SUNDAY',
    0x0805: 'SOMBER', 0x0806: 'DRAMA', 0x0807: 'SILENCE', 0x0808: 'BLEACH',
    0x0809: 'MELANCHOLIC', 0x080A: 'PURE', 0x080B: 'DENIM', 0x080C: 'TOY',
    0x080D: 'SEPIA', 0x080E: 'BLUE', 0x080F: 'RED', 0x0810: 'PINK',
    0x0811: 'CHARCOAL', 0x0812: 'GRAPHITE', 0x0813: 'BINARY', 0x0814: 'CARBON',
    0x028E: 'FLAT', 0x02CF: 'AUTO',
    0x0001: 'STANDARD', 0x03C2: 'NEUTRAL', 0x00C3: 'VIVID',
    0x0486: 'PORTRAIT', 0x04C7: 'LANDSCAPE', 0x064D: 'MONOCHROME'
  };

  var CN_NAME = {
    'DREAM': '梦幻', 'MORNING': '清晨', 'POP': '流行', 'SUNDAY': '星期天',
    'SOMBER': '低沉', 'DRAMA': '戏剧', 'SILENCE': '静寂', 'BLEACH': '漂白',
    'MELANCHOLIC': '忧郁', 'PURE': '纯净', 'DENIM': '牛仔布', 'TOY': '玩具',
    'SEPIA': '棕褐色', 'BLUE': '蓝色', 'RED': '红色', 'PINK': '粉色',
    'CHARCOAL': '木炭', 'GRAPHITE': '石墨', 'BINARY': '双色', 'CARBON': '黑碳',
    'FLAT': '平面', 'FLAT_MONOCHROME': '平面单色', 'DEEPTONE_MONOCHROME': '深色调单色',
    'RICH_TONE_PORTRAIT': '丰富色调人像', 'FLEXIBLE_COLOR': '灵活颜色',
    'LANDSCAPE': '风景', 'MONOCHROME': '单色', 'NEUTRAL': '自然',
    'STANDARD': '标准', 'VIVID': '鲜艳', 'AUTO': '自动'
  };

  var TONING = ['黑白', '棕褐', '青蓝', '红', '黄', '绿', '蓝绿', '蓝', '紫蓝', '红紫'];
  var TONING_HUE = [null, 72, 250, 32, 92, 142, 200, 268, 300, 348];

  /* ---------------------------------------------------------- 小工具 */

  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }

  // Python 的 round() 是「四舍六入五取偶」，和 JS 的 Math.round（五入向上）不一样。
  // 两者在一些 .5 边界上会差 1 个 15 位单位，文件就对不上 —— 所以照 Python 的来。
  function pyRound(x) {
    var f = Math.floor(x), d = x - f;
    if (d > 0.5) return f + 1;
    if (d < 0.5) return f;
    return (f % 2 === 0) ? f : f + 1;
  }

  // numpy.interp 的标量版（xp 必须升序）
  function interp(x, xp, fp) {
    var n = xp.length;
    if (x <= xp[0]) return fp[0];
    if (x >= xp[n - 1]) return fp[n - 1];
    var lo = 0, hi = n - 1;
    while (hi - lo > 1) {
      var m = (lo + hi) >> 1;
      if (xp[m] <= x) lo = m; else hi = m;
    }
    var d = xp[hi] - xp[lo];
    if (d === 0) return fp[lo];
    return fp[lo] + (fp[hi] - fp[lo]) * (x - xp[lo]) / d;
  }

  function median(arr) {
    if (!arr.length) return 0;
    var a = Float64Array.from(arr).sort();
    var n = a.length;
    return (n % 2) ? a[(n - 1) >> 1] : (a[n / 2 - 1] + a[n / 2]) / 2;
  }

  function bytesToLatin1(u8) {
    var s = '', i, n = u8.length;
    for (i = 0; i < n; i += 4096) {
      s += String.fromCharCode.apply(null, u8.subarray(i, Math.min(i + 4096, n)));
    }
    return s;
  }

  function base64ToBytes(b64) {
    var bin = atob(b64);
    var out = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }

  function bytesToBase64(u8) {
    return btoa(bytesToLatin1(u8));
  }

  /* ---------------------------------------------------------- 文件格式 */

  // 读 NP2/NP3 的 TLV 卡片链。卡类型 = 卡号 << 8。
  function parseNP(u8) {
    var dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    var cards = {}, off = 4;
    while (off + 8 <= u8.length) {
      var t = dv.getUint32(off);
      if (t === 0) break;
      var ln = dv.getUint32(off + 4);
      if (ln > u8.length - off - 8) break;
      cards[t >>> 8] = u8.subarray(off + 8, off + 8 + ln);
      off += 8 + ln;
    }

    var nameRaw = cards[2] || new Uint8Array(0);
    var s = '', i;
    for (i = 0; i < nameRaw.length; i++) {
      if (nameRaw[i] === 0) break;
      s += String.fromCharCode(nameRaw[i]);
    }
    var name = s;
    var base = 0;
    var c3 = cards[3];
    if (c3 && c3.length >= 2) base = (c3[0] << 8) | c3[1];

    var keys = [['sharp', 6], ['clarity', 7], ['contrast', 8], ['brightness', 9],
                ['saturation', 10], ['hue', 11], ['filter', 12], ['tone', 13],
                ['tone_strength', 14], ['effect_level', 21], ['quick_sharp', 22]];
    var vals = {};
    for (i = 0; i < keys.length; i++) vals[keys[i][0]] = cardNum(cards[keys[i][1]]);

    var nCards = 0;
    for (var k in cards) if (Object.prototype.hasOwnProperty.call(cards, k)) nCards++;

    return { name: name || '(无名字)', base: base, params: vals,
             n_cards: nCards, size: u8.length };
  }

  // 2 字节参数卡：值 = (字节0 − 0x80) × 字节1 / 16；字节1 = 0 是枚举
  function cardNum(data) {
    if (!data || data.length < 2) return null;
    var v = data[0], st = data[1];
    if (v === 0xFF) return null;
    if (st === 0) return v - 0x80;
    return (v - 0x80) * st / 16.0;
  }

  // 读 NCP：记录 1 = 36 字节配置，记录 2 = 578 字节曲线
  function readNCP(u8) {
    if (!(u8[0] === 0x4E && u8[1] === 0x43 && u8[2] === 0x50 && u8[3] === 0)) {
      throw new Error('不是 NCP 文件（前 4 字节应为 NCP\\0）');
    }
    var dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    var off = 4, prof = null, lut = null;
    while (off + 8 <= u8.length) {
      var t = dv.getUint32(off), ln = dv.getUint32(off + 4);
      if (t === 0) break;
      var data = u8.subarray(off + 8, off + 8 + ln);
      if (t === 1 && data.length >= 36) {
        prof = data;
      } else if (t === 2 && data.length >= REC2_LEN) {
        lut = new Float64Array(257);
        var dv2 = new DataView(data.buffer, data.byteOffset, data.byteLength);
        for (var i = 0; i < 257; i++) {
          lut[i] = dv2.getUint16(HDR_LEN + i * 2) / OUT_MAX * 255.0;
        }
      }
      off += 8 + ln;
    }
    if (prof === null) throw new Error('NCP 缺少配置记录');

    var nm = '';
    for (var j = 4; j < 24; j++) {
      if (prof[j] === 0) break;
      nm += String.fromCharCode(prof[j]);
    }
    return {
      name: nm,
      base: (prof[24] << 8) | prof[25],
      sliders: [prof[28], prof[29], prof[30], prof[31], prof[32], prof[33], prof[34], prof[35]],
      lut: lut
    };
  }

  function sampleLUT(lut, x) {
    var fi = x / 255.0 * 256.0;
    var i = Math.min(Math.floor(fi), 255);
    return lut[i] + (lut[i + 1] - lut[i]) * (fi - i);
  }

  // 把 LUT 采样成控制点写进 64 字节头。不能均匀撒点：木炭/双色局部极陡。
  function headerFromLUT(lut, npts) {
    npts = Math.max(2, Math.min(npts || MAX_PTS, MAX_PTS));

    function y8(x) {
      return pyRound(clamp(sampleLUT(lut, x) / OUT_MAX * 255.0, 0, 255));
    }

    var xs = [0, 255], ys = [y8(0), y8(255)];
    while (xs.length < npts) {
      var bx = -1, be = 0.0;
      for (var x = 1; x < 255; x++) {
        if (xs.indexOf(x) >= 0) continue;
        var j = 0;
        while (j + 2 < xs.length && xs[j + 1] < x) j++;
        var x0 = xs[j], x1 = xs[j + 1], y0 = ys[j], y1 = ys[j + 1];
        var e = Math.abs((y0 + (y1 - y0) * (x - x0) / (x1 - x0)) - y8(x));
        if (e > be) { bx = x; be = e; }
      }
      if (bx < 0) break;
      var k = 0;
      while (xs[k] < bx) k++;
      xs.splice(k, 0, bx);
      ys.splice(k, 0, y8(bx));
    }
    for (var i = 1; i < ys.length; i++) if (ys[i] < ys[i - 1]) ys[i] = ys[i - 1];

    var h = new Uint8Array(HDR_LEN);
    h.set(HDR_PREFIX, 0);
    h[8] = xs.length;
    for (var p = 0; p < xs.length && 9 + p * 2 + 1 < HDR_LEN; p++) {
      h[9 + p * 2] = xs[p];
      h[10 + p * 2] = ys[p];
    }
    return h;
  }

  // lut 为 null → 52 字节（不带曲线）；否则 638 字节
  function buildNCP(name, base, sliders, lut) {
    var nb = [];
    var up = String(name || '').toUpperCase();
    for (var i = 0; i < up.length && nb.length < 20; i++) {
      var c = up.charCodeAt(i);
      nb.push(c < 128 ? c : 0x3F);
    }

    var prof = new Uint8Array(36);
    prof[0] = 0x30; prof[1] = 0x31; prof[2] = 0x30; prof[3] = 0x30;   // '0100'
    for (var p = 0; p < nb.length; p++) prof[4 + p] = nb[p];
    prof[24] = (base >> 8) & 0xFF;
    prof[25] = base & 0xFF;
    prof[26] = 0; prof[27] = 0xFF;
    for (var s = 0; s < 8; s++) prof[28 + s] = sliders[s] & 0xFF;

    var total = 4 + 8 + 36 + 4 + (lut ? 8 + REC2_LEN : 0);
    var out = new Uint8Array(total);
    var dv = new DataView(out.buffer);
    out.set([0x4E, 0x43, 0x50, 0x00], 0);                 // 'NCP\0'
    dv.setUint32(4, 1); dv.setUint32(8, 36);
    out.set(prof, 12);

    var off = 48;
    if (lut) {
      dv.setUint32(off, 2); dv.setUint32(off + 4, REC2_LEN);
      out.set(headerFromLUT(lut), off + 8);
      var q = off + 8 + HDR_LEN;
      for (var i2 = 0; i2 < 257; i2++) {
        dv.setUint16(q + i2 * 2, clamp(pyRound(lut[i2]), 0, OUT_MAX));
      }
      off += 8 + REC2_LEN;
    }
    dv.setUint32(off, 0);
    return out;
  }

  /* ---------------------------------------------------------- 曲线数学 */

  // 实测的曲线前变换 H：引擎执行的是 C(H(x))
  var _H_PTS = [
    [0, 0], [10, 9.0], [14, 12.0], [18, 14.9], [22, 18.5], [26, 21.9],
    [30, 24.6], [34, 27.9], [38, 31.1], [42, 34.1], [46, 37.2], [50, 40.6],
    [54, 43.8], [58, 46.9], [62, 50.2], [66, 53.6], [70, 56.9], [74, 60.1],
    [78, 63.4], [82, 67.0], [86, 70.3], [90, 73.9], [94, 77.4], [98, 80.9],
    [102, 84.4], [106, 88.3], [110, 92.1], [114, 95.9], [118, 99.9],
    [122, 103.9], [126, 108.3], [130, 112.3], [134, 116.2], [138, 120.1],
    [142, 124.2], [146, 127.4], [150, 132.0], [154, 136.1], [158, 140.6],
    [162, 144.9], [166, 149.5], [170, 154.4], [174, 158.9], [178, 164.0],
    [182, 169.2], [186, 174.1], [190, 179.1], [194, 183.9], [198, 188.3],
    [202, 193.7], [206, 197.6], [210, 202.9], [214, 207.0], [218, 211.9],
    [222, 216.5], [226, 220.9], [230, 225.7], [234, 230.5], [238, 235.0],
    [242, 239.7], [246, 243.9], [250, 248.6], [255, 255.0]
  ];

  var _HX = _H_PTS.map(function (p) { return p[0]; });
  var _HY = (function () {
    var y = _H_PTS.map(function (p) { return p[1]; });
    var n = y.length, ys = y.slice();
    for (var i = 1; i < n - 1; i++) ys[i] = (y[i - 1] + y[i] + y[i + 1]) / 3.0;
    ys[0] = 0; ys[n - 1] = 255;
    var acc = -Infinity;
    for (var j = 0; j < n; j++) { acc = Math.max(acc, ys[j]); ys[j] = clamp(acc, 0, 255); }
    return ys;
  })();

  var _HY_KEEP = (function () {
    var out = [0];
    for (var i = 1; i < _HY.length; i++) if (_HY[i] - _HY[i - 1] > 1e-9) out.push(i);
    return out;
  })();
  var _HY_KEEP_Y = _HY_KEEP.map(function (i) { return _HY[i]; });
  var _HY_KEEP_X = _HY_KEEP.map(function (i) { return _HX[i]; });

  function H(x) { return interp(clamp(x, 0, 255), _HX, _HY); }
  function Hinv(v) { return interp(clamp(v, 0, 255), _HY_KEEP_Y, _HY_KEEP_X); }

  // 把「想要的亮度曲线」换成「该写进文件的 257 点 LUT」
  function precompensate(curve, outMax) {
    outMax = outMax || OUT_MAX;
    var t = [];
    for (var i = 0; i < curve.length; i++) t.push(clamp(curve[i], 0, 255));
    if (t.length === 256) t.push(t[255]);
    if (t.length !== 257) {
      var src = t.slice();
      t = [];
      for (var k = 0; k < 257; k++) {
        t.push(src[Math.max(0, Math.min(src.length - 1, Math.round(k * (src.length - 1) / 256)))]);
      }
    }
    var xp = [], fp = [];
    for (var j = 0; j < 257; j++) { xp.push(j); fp.push(t[j]); }

    var out = new Array(257), acc = -Infinity;
    for (var y = 0; y < 257; y++) {
      var c = clamp(interp(Hinv(y), xp, fp), 0, 255);
      if (c > acc) acc = c;
      out[y] = pyRound(acc / 255.0 * outMax);
    }
    return out;
  }

  function makeNCP(name, base, sliders, curve) {
    return buildNCP(name, base, sliders, precompensate(curve, OUT_MAX));
  }

  function slidersFor(mono, o) {
    o = o || {};
    var sharp = o.sharp == null ? 0x83 : o.sharp;
    var filt = o.filt == null ? 0x80 : o.filt;
    var contrast = o.contrast == null ? SL_CURVE : o.contrast;
    var brightness = o.brightness == null ? SL_CURVE : o.brightness;
    if (mono) {
      var tone = o.tone == null ? 0 : o.tone;
      var k = o.k == null ? 0.0 : o.k;
      var tb = o.toneByte == null ? ((tone >= 0 && tone <= 9) ? SL_ZERO + tone : SL_NA) : o.toneByte;
      var kb = SL_NA;
      if (tone >= 0 && tone <= 9) {
        var ks = 0.5 + k * 0.5;
        kb = SL_ZERO + pyRound(clamp(ks, 0, 1) * 4);
      }
      return [sharp, contrast, brightness, SL_NA, SL_NA, filt, tb, kb];
    }
    return [sharp, contrast, brightness, SL_ZERO + (o.n || 0), SL_ZERO + (o.m || 0), filt, SL_NA, SL_NA];
  }

  // 生成后自检
  function checkNCP(u8) {
    var prob = [];
    if (!(u8[0] === 0x4E && u8[1] === 0x43 && u8[2] === 0x50 && u8[3] === 0)) prob.push('缺少 NCP 标识');
    if ([44, 52, 630, 638].indexOf(u8.length) < 0) prob.push('长度 ' + u8.length + ' 不是已知的 52/638 之一');
    var d;
    try { d = readNCP(u8); } catch (e) { return prob.concat(['读回失败：' + e.message]); }
    if (d.lut) {
      if (d.lut.length !== 257) prob.push('LUT 点数不是 257');
      for (var i = 1; i < d.lut.length; i++) {
        if (d.lut[i] - d.lut[i - 1] < -1e-6) { prob.push('LUT 不单调（机身重算曲线时会抖）'); break; }
      }
      if (d.lut[0] < 0 || d.lut[256] > 255) prob.push('LUT 超出 0..255');
    }
    return prob;
  }

  /* ---------------------------------------------------------- 图像 */

  // {w, h, data: Float64Array(w*h*3)}  RGB 0..255
  function lumIdx(d, j) { return 0.299 * d[j] + 0.587 * d[j + 1] + 0.114 * d[j + 2]; }

  function isMonochrome(img) {
    var d = img.data, n = img.w * img.h, s = 0;
    for (var i = 0; i < n; i++) {
      var j = i * 3;
      var mx = Math.max(d[j], d[j + 1], d[j + 2]);
      var mn = Math.min(d[j], d[j + 1], d[j + 2]);
      s += mx - mn;
    }
    return s / n < 6.0;
  }

  /* ---------------------------------------------------------- 标定图 */

  var TW = 2048, TH = 1024;
  var RAMP_Y0 = 96, RAMP_Y1 = 300;
  var PATCH_Y0 = 352, PATCH_H = 300, PATCH_W = 128;

  var PATCHES = [
    [115, 82, 68], [194, 150, 130], [98, 122, 157], [87, 108, 67],
    [133, 128, 177], [103, 189, 170], [214, 126, 44], [80, 91, 166],
    [193, 90, 99], [94, 60, 108], [157, 188, 64], [224, 163, 46],
    [56, 61, 150], [70, 148, 73], [175, 54, 60], [231, 199, 31],
    [187, 86, 149], [8, 133, 161], [243, 243, 242], [200, 200, 200],
    [160, 160, 160], [122, 122, 121], [85, 85, 85], [52, 52, 52],
    [215, 175, 145], [120, 150, 200], [90, 170, 120], [240, 140, 90],
    [150, 100, 200], [60, 200, 190], [250, 120, 160], [110, 110, 110]
  ];

  // 灰阶条：每级取中间 4 像素平均（JPEG 的 8×8 块会跨级渗色）
  function rampValues(img) {
    if (img.h !== TH || img.w !== TW) return null;
    var out = new Float64Array(256), d = img.data;
    for (var i = 0; i < 256; i++) {
      var x0 = i * 8 + 2, s = 0, c = 0;
      for (var y = RAMP_Y0 + 20; y < RAMP_Y1 - 20; y++) {
        for (var x = x0; x < x0 + 4; x++) { s += lumIdx(d, (y * TW + x) * 3); c++; }
      }
      out[i] = s / c;
    }
    return out;
  }

  function patchValues(img) {
    var res = [], d = img.data;
    for (var i = 0; i < PATCHES.length; i++) {
      var r = Math.floor(i / 16), q = i % 16;
      var y0 = PATCH_Y0 + r * PATCH_H + 40;
      var x0 = q * PATCH_W + 20;
      var sr = 0, sg = 0, sb = 0, c = 0;
      for (var y = y0; y < y0 + PATCH_H - 80; y++) {
        for (var x = x0; x < x0 + PATCH_W - 40; x++) {
          var j = (y * TW + x) * 3;
          sr += d[j]; sg += d[j + 1]; sb += d[j + 2]; c++;
        }
      }
      res.push([PATCHES[i], [sr / c, sg / c, sb / c]]);
    }
    return res;
  }

  function guessToning(img, yStart) {
    var d = img.data, w = img.w, h = img.h;
    var sa = 0, sb = 0, c = 0;
    for (var y = yStart; y < h; y++) {
      for (var x = 0; x < w; x++) {
        var j = (y * w + x) * 3;
        var L = lumIdx(d, j);
        sa += (d[j] - L) - (d[j + 1] - L);
        sb += (d[j + 1] - L) - (d[j + 2] - L);
        c++;
      }
    }
    var a = sa / c, b = sb / c;
    var amp = Math.hypot(a, b);
    if (amp < 2.5) return { tone: 0, k: 0.0 };
    var hue = (Math.atan2(b, a) * 180 / Math.PI + 360) % 360;
    var best = 0, bd = 1e9;
    for (var i = 0; i < TONING_HUE.length; i++) {
      var hh = TONING_HUE[i];
      if (hh === null) continue;
      var dd = Math.abs((hue - hh + 180) % 360 - 180);
      if (dd < bd) { best = i; bd = dd; }
    }
    return { tone: best, k: clamp(amp / 9.0, 0, 1) };
  }

  // 从「用该 NP3 导出的标定图」直接解出曲线与色度
  function solveFromTarget(img) {
    var ramp = rampValues(img);
    if (ramp === null) {
      throw new Error('这张图不是本程序生成的标定图（尺寸应为 ' + TW + '×' + TH +
                      '，实际 ' + img.w + '×' + img.h + '）。导出时不要改尺寸。');
    }
    var curve = new Array(256), acc = -Infinity;
    for (var i = 0; i < 256; i++) { acc = Math.max(acc, clamp(ramp[i], 0, 255)); curve[i] = acc; }

    var patches = patchValues(img);
    var ratios = [], hues = [];
    for (var p = 0; p < patches.length; p++) {
      var ci = patches[p][0].slice(), co = patches[p][1].slice();
      var li = lumIdx(ci, 0), lo = lumIdx(co, 0);
      for (var c = 0; c < 3; c++) { ci[c] -= li; co[c] -= lo; }
      var ni = Math.hypot(ci[0], ci[1], ci[2]);
      var no = Math.hypot(co[0], co[1], co[2]);
      if (ni < 18) continue;
      ratios.push(no / ni);
      var ai = Math.atan2(ci[1] - ci[2], ci[0] - ci[1]) * 180 / Math.PI;
      var ao = Math.atan2(co[1] - co[2], co[0] - co[1]) * 180 / Math.PI;
      hues.push((ao - ai + 180) % 360 - 180);
    }

    var rmed = ratios.length ? median(ratios) : 1.0;
    var mono = ratios.length ? (rmed < 0.18) : false;
    var dhue = hues.length ? median(hues) : 0.0;

    var n = 0, m = 0;
    if (!mono) {
      n = pyRound(Math.log(Math.max(rmed, 1e-3)) / Math.log(SAT_STEP));
      m = pyRound(-dhue / HUE_STEP);
      n = Math.max(-3, Math.min(3, n));
      m = Math.max(-3, Math.min(3, m));
    }

    var tone = 0, k = 0.0;
    if (mono) {
      var g = guessToning(img, PATCH_Y0);
      tone = g.tone; k = g.k;
    }

    return { curve: curve, mono: mono, n: n, m: m, tone: tone, k: k,
             ratio: rmed, dhue: dhue, n_patch: ratios.length };
  }

  /* ---------------------------------------------------------- 标定库 */

  function Library() {
    this.byName = {};
    this.byBase = {};
    this.entries = [];
  }

  Library.prototype.addRaw = function (raw, kind, baseNP, label, slot) {
    var d = readNCP(raw);
    var e = {
      raw: raw, name: d.name, base: d.base, sliders: d.sliders, lut: d.lut,
      kind: kind, slot: slot || 0, cn: CN_NAME[d.name] || '',
      label: label || '', base_np: baseNP || 0, size: raw.length
    };
    var self = this;
    if (kind === 'custom') {
      this.byBase[baseNP] = e;
      this.byName[(label || d.name).toUpperCase()] = e;
    } else {
      if (!(d.name in this.byName)) this.byName[d.name] = e;
      Object.keys(NP_BASE_NAME).forEach(function (b) {
        if (NP_BASE_NAME[b] === d.name && !((+b) in self.byBase)) self.byBase[+b] = e;
      });
    }
    return e;
  };

  // 只认底子编号，不因为名字相同就命中
  Library.prototype.lookup = function (name, base) {
    if (base) {
      var e = this.byBase[base];
      return e ? [e, '标定库 · 底子 ' + ('0000' + base.toString(16).toUpperCase()).slice(-4)]
               : [null, null];
    }
    var k = String(name || '').toUpperCase();
    if (k in this.byName) return [this.byName[k], '标定库 · 名字（无底子编号）'];
    return [null, null];
  };

  Library.prototype.list = function () {
    var seen = {}, out = [], self = this;
    Object.keys(this.byName).sort(function (a, b) {
      return (self.byName[a].slot || 99) - (self.byName[b].slot || 99);
    }).forEach(function (k) {
      var e = self.byName[k];
      var key = e.name + '|' + e.base;
      if (seen[key]) return;
      seen[key] = 1;
      out.push({ name: e.name, cn: e.cn, base: e.base, base_np: e.base_np,
                 slot: e.slot, kind: e.kind, label: e.label });
    });
    return out;
  };

  /* ---------------------------------------------------------- 导出接口 */

  global.NP3 = {
    OUT_MAX: OUT_MAX, MONO_BASE: MONO_BASE, COLOR_BASE: COLOR_BASE,
    CN_NAME: CN_NAME, TONING: TONING, TW: TW, TH: TH,
    parseNP: parseNP, readNCP: readNCP, buildNCP: buildNCP, makeNCP: makeNCP,
    checkNCP: checkNCP, slidersFor: slidersFor, precompensate: precompensate,
    H: H, Hinv: Hinv, headerFromLUT: headerFromLUT, sampleLUT: sampleLUT,
    solveFromTarget: solveFromTarget, isMonochrome: isMonochrome,
    guessToning: guessToning, Library: Library, interp: interp, median: median,
    base64ToBytes: base64ToBytes, bytesToBase64: bytesToBase64,
    lum: lumIdx, patchValues: patchValues, rampValues: rampValues
  };
})(typeof window !== 'undefined' ? window : globalThis);
