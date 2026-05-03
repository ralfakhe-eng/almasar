/**
 * qr-barcode.js — مكتبة QR Code + Barcode مكتوبة من الصفر
 * تعمل بدون إنترنت ، بدون مكتبات خارجية
 * المسار السريع v2.1
 */

// ══════════════════════════════════════════
// QR CODE — خوارزمية كاملة
// ══════════════════════════════════════════
(function(global) {

  // جدول Galois Field
  var GF = (function() {
    var EXP = new Array(512), LOG = new Array(256);
    EXP[0] = 1;
    for (var i = 1; i < 256; i++) {
      var v = EXP[i-1] << 1;
      if (v >= 256) v ^= 0x11d;
      EXP[i] = v;
      EXP[i+255] = v;
    }
    for (var i = 1; i < 256; i++) LOG[EXP[i]] = i;
    return {
      mul: function(a, b) { return a === 0 || b === 0 ? 0 : EXP[LOG[a] + LOG[b]]; },
      EXP: EXP, LOG: LOG
    };
  })();

  // حساب polynomial للتصحيح
  function rsGeneratorPoly(degree) {
    var p = [1];
    for (var i = 0; i < degree; i++) {
      var next = [1, GF.EXP[i]];
      var r = new Array(p.length + next.length - 1).fill(0);
      for (var j = 0; j < p.length; j++)
        for (var k = 0; k < next.length; k++)
          r[j+k] ^= GF.mul(p[j], next[k]);
      p = r;
    }
    return p;
  }

  function rsEncode(data, nblock) {
    var gen = rsGeneratorPoly(nblock);
    var res = new Array(nblock).fill(0);
    for (var i = 0; i < data.length; i++) {
      var c = data[i] ^ res.shift();
      res.push(0);
      if (c !== 0) for (var j = 0; j < gen.length - 1; j++)
        res[j] ^= GF.mul(gen[j], c);
    }
    return res;
  }

  // معلومات الإصدارات (version 1-5، مستوى M)
  var VERSION_INFO = [
    null,
    { cap: 14, ecLen: 10, blocks: [[1,26,14]] },  // v1
    { cap: 26, ecLen: 16, blocks: [[1,44,28]] },  // v2
    { cap: 42, ecLen: 26, blocks: [[1,70,44]] },  // v3
    { cap: 62, ecLen: 18, blocks: [[2,50,32]] },  // v4
    { cap: 84, ecLen: 24, blocks: [[2,67,43]] },  // v5
  ];

  function selectVersion(len) {
    for (var v = 1; v <= 5; v++)
      if (VERSION_INFO[v].cap >= len) return v;
    return 5;
  }

  // Penalty scores
  function penalty(matrix, n) {
    var score = 0;
    // Rule 1: 5+ consecutive
    for (var i = 0; i < n; i++) {
      var hRun = 1, vRun = 1;
      for (var j = 1; j < n; j++) {
        if (matrix[i][j] === matrix[i][j-1]) { hRun++; if (hRun === 5) score += 3; else if (hRun > 5) score++; } else hRun = 1;
        if (matrix[j][i] === matrix[j-1][i]) { vRun++; if (vRun === 5) score += 3; else if (vRun > 5) score++; } else vRun = 1;
      }
    }
    // Rule 2: 2x2 blocks
    for (var i = 0; i < n-1; i++)
      for (var j = 0; j < n-1; j++)
        if (matrix[i][j]===matrix[i][j+1] && matrix[i][j]===matrix[i+1][j] && matrix[i][j]===matrix[i+1][j+1]) score += 3;
    return score;
  }

  function applyMask(matrix, mask, n) {
    var m = matrix.map(function(r){return r.slice();});
    var fns = [
      function(i,j){return (i+j)%2===0;},
      function(i,j){return i%2===0;},
      function(i,j){return j%3===0;},
      function(i,j){return (i+j)%3===0;},
      function(i,j){return (Math.floor(i/2)+Math.floor(j/3))%2===0;},
      function(i,j){return i*j%2+i*j%3===0;},
      function(i,j){return (i*j%2+i*j%3)%2===0;},
      function(i,j){return (i*j%3+(i+j)%2)%2===0;}
    ];
    for (var i = 0; i < n; i++)
      for (var j = 0; j < n; j++)
        if (m[i][j] !== null && fns[mask](i,j)) m[i][j] ^= 1;
    return m;
  }

  function placeFinderPattern(matrix, r, c) {
    for (var dr = -1; dr <= 7; dr++)
      for (var dc = -1; dc <= 7; dc++) {
        var row = r+dr, col = c+dc;
        if (row < 0 || col < 0 || row >= matrix.length || col >= matrix.length) continue;
        var inBox = dr>=0&&dr<=6&&dc>=0&&dc<=6;
        var onBorder = dr===0||dr===6||dc===0||dc===6;
        var inInner = dr>=2&&dr<=4&&dc>=2&&dc<=4;
        matrix[row][col] = inBox ? (onBorder||inInner ? 1 : 0) : 0;
      }
  }

  function placeTimingPattern(matrix, n) {
    for (var i = 8; i < n-8; i++) {
      if (matrix[6][i] === null) matrix[6][i] = i%2===0?1:0;
      if (matrix[i][6] === null) matrix[i][6] = i%2===0?1:0;
    }
  }

  function formatInfo(ecLevel, mask) {
    // ecLevel: 0=M,1=L,2=H,3=Q → bits: M=00,L=01,H=10,Q=11
    var ecBits = [1,0,3,2][ecLevel]; // M→01
    var data = (ecBits << 3) | mask;
    var rem = data;
    for (var i = 0; i < 10; i++) rem = ((rem << 1) ^ (((rem >> 9) & 1) ? 0x537 : 0)) & 0x3FF;
    var full = ((data << 10) | rem) ^ 0x5412;
    return full;
  }

  function placeFormatInfo(matrix, n, fi) {
    var seq1 = [0,1,2,3,4,5,7,8,8,8,8,8,8,7,6,5,4,3,2,1,0];
    // row 8, cols
    for (var i = 0; i < 6; i++) matrix[8][i] = (fi>>(14-i))&1;
    matrix[8][7] = (fi>>8)&1; matrix[8][8] = (fi>>7)&1; matrix[8][9] = (fi>>6)&1;
    for (var i = 0; i < 7; i++) matrix[8][n-7+i] = (fi>>(5-i))&1;
    // col 8
    for (var i = 0; i < 6; i++) matrix[i][8] = (fi>>(14-i+8))&1||0;
    matrix[7][8]=(fi>>6)&1; matrix[8][8]=(fi>>7)&1;
    matrix[n-7][8]=1; // dark module
    for (var i = 0; i < 7; i++) matrix[n-6+i][8] = (fi>>(i))&1;
  }

  function encodeData(text, version) {
    var bits = [];
    function pushBits(val, len) { for(var i=len-1;i>=0;i--) bits.push((val>>i)&1); }
    // Byte mode
    pushBits(0b0100, 4);
    pushBits(text.length, 8);
    for (var i = 0; i < text.length; i++) pushBits(text.charCodeAt(i), 8);
    // Terminator
    for (var i = 0; i < 4 && bits.length < VERSION_INFO[version].cap*8; i++) bits.push(0);
    while (bits.length % 8 !== 0) bits.push(0);
    var pads = [0xEC, 0x11], pi = 0;
    while (bits.length < VERSION_INFO[version].cap*8) { pushBits(pads[pi%2], 8); pi++; }
    return bits;
  }

  function bitsToBytes(bits) {
    var bytes = [];
    for (var i = 0; i < bits.length; i += 8) {
      var b = 0;
      for (var j = 0; j < 8; j++) b = (b<<1)|(bits[i+j]||0);
      bytes.push(b);
    }
    return bytes;
  }

  function generateQR(text) {
    var version = selectVersion(text.length);
    var n = 4*version+17;
    var info = VERSION_INFO[version];

    // إنشاء المصفوفة
    var matrix = [];
    for (var i = 0; i < n; i++) { matrix.push([]); for (var j = 0; j < n; j++) matrix[i].push(null); }

    // Finder patterns
    placeFinderPattern(matrix, 0, 0);
    placeFinderPattern(matrix, n-7, 0);
    placeFinderPattern(matrix, 0, n-7);
    placeTimingPattern(matrix, n);
    matrix[n-8][8] = 1; // dark module

    // الترميز
    var dataBits = encodeData(text, version);
    var dataBytes = bitsToBytes(dataBits);

    // تصحيح الأخطاء
    var allData = [], allEC = [];
    info.blocks.forEach(function(blk) {
      var count=blk[0], total=blk[1], data=blk[2];
      for (var b=0; b<count; b++) {
        var slice = dataBytes.splice(0, data);
        allData.push(slice);
        allEC.push(rsEncode(slice, total-data));
      }
    });

    // دمج البيانات
    var finalBytes = [];
    var maxLen = Math.max.apply(null, allData.map(function(d){return d.length;}));
    for (var i=0; i<maxLen; i++) allData.forEach(function(d){if(i<d.length)finalBytes.push(d[i]);});
    var maxEC = Math.max.apply(null, allEC.map(function(d){return d.length;}));
    for (var i=0; i<maxEC; i++) allEC.forEach(function(d){if(i<d.length)finalBytes.push(d[i]);});

    // تحويل لبتات
    var finalBits = [];
    finalBytes.forEach(function(b){for(var i=7;i>=0;i--)finalBits.push((b>>i)&1);});
    while (finalBits.length < n*n) finalBits.push(0);

    // وضع البيانات في المصفوفة
    var bitIdx = 0;
    var col = n-1;
    while (col > 0) {
      if (col === 6) col--;
      for (var row = 0; row < n; row++) {
        var r = (Math.floor((n-1-col)/2)%2===0) ? n-1-row : row;
        for (var dc = 0; dc < 2; dc++) {
          var c = col - dc;
          if (matrix[r][c] === null) { matrix[r][c] = finalBits[bitIdx++]||0; }
        }
      }
      col -= 2;
    }

    // اختيار أفضل mask
    var bestMask = 0, bestScore = Infinity;
    for (var m=0; m<8; m++) {
      var masked = applyMask(matrix, m, n);
      var sc = penalty(masked, n);
      if (sc < bestScore) { bestScore=sc; bestMask=m; }
    }

    var finalMatrix = applyMask(matrix, bestMask, n);
    // وضع format info
    var fi = formatInfo(0, bestMask);
    placeFormatInfo(finalMatrix, n, fi);

    return finalMatrix;
  }

  // رسم QR على Canvas
  function drawQROnCanvas(canvas, text, size, darkColor, lightColor) {
    darkColor = darkColor || '#000000';
    lightColor = lightColor || '#ffffff';
    try {
      var matrix = generateQR(text);
      var n = matrix.length;
      var cell = Math.floor(size / (n + 2)); // مع هامش
      var offset = Math.floor((size - cell * n) / 2);
      var ctx = canvas.getContext('2d');
      ctx.fillStyle = lightColor;
      ctx.fillRect(0, 0, size, size);
      ctx.fillStyle = darkColor;
      for (var i = 0; i < n; i++)
        for (var j = 0; j < n; j++)
          if (matrix[i][j]) ctx.fillRect(offset+j*cell, offset+i*cell, cell, cell);
      return true;
    } catch(e) {
      console.warn('QR error:', e);
      return false;
    }
  }

  // ══════════════════════════════════════════
  // BARCODE Code 128 — خوارزمية كاملة
  // ══════════════════════════════════════════

  // جدول Code 128B
  var C128 = [
    '11011001100','11001101100','11001100110','10010011000','10010001100',
    '10001001100','10011001000','10011000100','10001100100','11001001000',
    '11001000100','11000100100','10110011100','10011011100','10011001110',
    '10111001100','10011101100','10011100110','11001110010','11001011100',
    '11001001110','11011100100','11001110100','11101101110','11101001100',
    '11100101100','11100100110','11101100100','11100110100','11100110010',
    '11011011000','11011000110','11000110110','10100011000','10001011000',
    '10001000110','10110001000','10001101000','10001100010','11010001000',
    '11000101000','11000100010','10110111000','10110001110','10001101110',
    '10111011000','10111000110','10001110110','11101110110','11010001110',
    '11000101110','11011101000','11011100010','11011101110','11101011000',
    '11101000110','11100010110','11101101000','11101100010','11100011010',
    '11101111010','11001000010','11110001010','10100110000','10100001100',
    '10010110000','10010000110','10000101100','10000100110','10110010000',
    '10110000100','10011010000','10011000010','10000110100','10000110010',
    '11000010010','11001010000','11110111010','11000010100','10001111010',
    '10100111100','10010111100','10010011110','10111100100','10011110100',
    '10011110010','11110100100','11110010100','11110010010','11011011110',
    '11011110110','11110110110','10101111000','10100011110','10001011110',
    '10111101000','10111100010','11110101000','11110100010','10111011110',
    '10111101110','11101011110','11110101110','11010000100','11010010000',
    '11010011100','1100011101011'
  ];

  var START_B = C128[104];
  var STOP    = C128[106];

  function encodeCode128(text) {
    var bars = [START_B];
    var checksum = 104; // START B value
    for (var i = 0; i < text.length; i++) {
      var code = text.charCodeAt(i) - 32;
      if (code < 0 || code > 94) code = 0;
      bars.push(C128[code]);
      checksum += (i+1) * code;
    }
    bars.push(C128[checksum % 103]);
    bars.push(STOP);
    return bars.join('');
  }

  function drawBarcodeOnCanvas(canvas, text, options) {
    options = options || {};
    var darkColor  = options.darkColor  || '#000000';
    var lightColor = options.lightColor || '#ffffff';
    var height     = options.height     || canvas.height;
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = lightColor;
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    try {
      var pattern = encodeCode128(text);
      var quietZone = 10;
      var availWidth = canvas.width - quietZone * 2;
      var barW = availWidth / pattern.length;
      var x = quietZone;
      ctx.fillStyle = darkColor;
      for (var i = 0; i < pattern.length; i++) {
        if (pattern[i] === '1') ctx.fillRect(Math.round(x), 0, Math.max(1, Math.round(barW)), height - 14);
        x += barW;
      }
      // النص تحت الباركود
      ctx.fillStyle = darkColor;
      ctx.font = '9px monospace';
      ctx.textAlign = 'center';
      ctx.fillText(text, canvas.width/2, height - 2);
      return true;
    } catch(e) {
      console.warn('Barcode error:', e);
      return false;
    }
  }

  // ══ API العام ══
  global.AlMasarQR = {
    // رسم QR على canvas
    drawQR: function(canvas, text, options) {
      options = options || {};
      return drawQROnCanvas(
        canvas, text,
        options.size || canvas.width,
        options.darkColor || '#1d4ed8',
        options.lightColor || '#ffffff'
      );
    },
    // رسم باركود على canvas
    drawBarcode: function(canvas, text, options) {
      return drawBarcodeOnCanvas(canvas, text, options || {});
    },
    // رسم QR + باركود معاً في div
    drawBoth: function(container, text, options) {
      options = options || {};
      var qrSize  = options.qrSize  || 100;
      var barW    = options.barWidth  || 180;
      var barH    = options.barHeight || 50;

      container.style.display    = 'flex';
      container.style.alignItems = 'center';
      container.style.gap        = '8px';

      // QR
      var qrWrap = document.createElement('div');
      qrWrap.style.textAlign = 'center';
      var qrCanvas = document.createElement('canvas');
      qrCanvas.width  = qrSize;
      qrCanvas.height = qrSize;
      qrCanvas.style.border = '2px solid #1d4ed8';
      qrCanvas.style.borderRadius = '4px';
      qrCanvas.style.display = 'block';
      var qrLabel = document.createElement('div');
      qrLabel.style.cssText = 'font-size:8px;color:#64748b;margin-top:2px;font-family:monospace;';
      qrLabel.textContent = 'QR';
      qrWrap.appendChild(qrCanvas);
      qrWrap.appendChild(qrLabel);
      drawQROnCanvas(qrCanvas, text, qrSize, options.darkColor||'#1d4ed8', '#ffffff');

      // Barcode
      var barWrap = document.createElement('div');
      barWrap.style.textAlign = 'center';
      var barCanvas = document.createElement('canvas');
      barCanvas.width  = barW;
      barCanvas.height = barH;
      barCanvas.style.display = 'block';
      var barLabel = document.createElement('div');
      barLabel.style.cssText = 'font-size:8px;color:#64748b;margin-top:2px;font-family:monospace;';
      barLabel.textContent = 'Barcode';
      barWrap.appendChild(barCanvas);
      barWrap.appendChild(barLabel);
      drawBarcodeOnCanvas(barCanvas, text, { darkColor: options.darkColor||'#1d4ed8', height: barH });

      container.appendChild(qrWrap);
      container.appendChild(barWrap);
    }
  };

})(window);
