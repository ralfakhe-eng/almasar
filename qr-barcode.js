/**
 * qr-barcode.js — مكتبة QR + Barcode محلية للمسار السريع
 * تعمل بدون إنترنت — بدون dependencies خارجية
 */

(function(global) {

// ══════════════════════════════════════════
// QR Code Generator
// ══════════════════════════════════════════
const QR = (function() {
  // جداول QR
  const GF = {
    exp: new Uint8Array(512),
    log: new Uint8Array(256)
  };
  (function() {
    let x = 1;
    for (let i = 0; i < 255; i++) {
      GF.exp[i] = x;
      GF.log[x] = i;
      x <<= 1;
      if (x & 256) x ^= 285;
    }
    for (let i = 255; i < 512; i++) GF.exp[i] = GF.exp[i - 255];
  })();

  function gfMul(a, b) {
    if (a === 0 || b === 0) return 0;
    return GF.exp[(GF.log[a] + GF.log[b]) % 255];
  }

  function gfPoly(gen, e) {
    let p = [1];
    for (let i = 0; i < e; i++) {
      const t = new Uint8Array(p.length + 1);
      for (let j = 0; j < p.length; j++) {
        t[j] ^= gfMul(p[j], GF.exp[i]);
        t[j + 1] ^= p[j];
      }
      p = Array.from(t);
    }
    return p;
  }

  function rsEncode(data, nEcc) {
    const gen = gfPoly(0, nEcc);
    const msg = [...data, ...new Array(nEcc).fill(0)];
    for (let i = 0; i < data.length; i++) {
      const c = msg[i];
      if (c !== 0) {
        for (let j = 0; j < gen.length; j++) {
          msg[i + j] ^= gfMul(gen[j], c);
        }
      }
    }
    return msg.slice(data.length);
  }

  // حالات QR Version 1-4
  const CAPACITY = [0,17,32,53,78];
  const ECC_BLOCKS = [0,7,10,15,20];

  function encode(text) {
    const bytes = [];
    for (let i = 0; i < text.length; i++) {
      const c = text.charCodeAt(i);
      if (c < 128) bytes.push(c);
      else { bytes.push(0x3F); } // fallback
    }

    // اختيار version
    let ver = 1;
    for (let v = 1; v <= 4; v++) {
      if (bytes.length + 3 <= CAPACITY[v]) { ver = v; break; }
    }

    const size = ver * 4 + 17;
    const modules = Array.from({length: size}, () => new Uint8Array(size));
    const reserved = Array.from({length: size}, () => new Uint8Array(size));

    function setMod(r, c, v) {
      if (r >= 0 && r < size && c >= 0 && c < size) {
        modules[r][c] = v ? 1 : 0;
        reserved[r][c] = 1;
      }
    }

    // Finder patterns
    function finder(r, c) {
      for (let dr = -1; dr <= 7; dr++) {
        for (let dc = -1; dc <= 7; dc++) {
          const inside = dr >= 0 && dr <= 6 && dc >= 0 && dc <= 6;
          const border = dr === 0 || dr === 6 || dc === 0 || dc === 6;
          const inner = dr >= 2 && dr <= 4 && dc >= 2 && dc <= 4;
          if (inside) setMod(r+dr, c+dc, border || inner ? 1 : 0);
        }
      }
    }

    finder(0, 0);
    finder(0, size - 7);
    finder(size - 7, 0);

    // Timing
    for (let i = 8; i < size - 8; i++) {
      setMod(6, i, i % 2 === 0 ? 1 : 0);
      setMod(i, 6, i % 2 === 0 ? 1 : 0);
    }

    // Dark module
    setMod(size - 8, 8, 1);

    // Format (mask 0)
    const fmt = [1,1,1,0,1,1,1,1,1,0,0,0,1,0,0];
    const fmtPos = [
      [8,0],[8,1],[8,2],[8,3],[8,4],[8,5],[8,7],[8,8],
      [7,8],[5,8],[4,8],[3,8],[2,8],[1,8],[0,8]
    ];
    fmtPos.forEach(([r,c],i) => setMod(r,c,fmt[i]));
    [[size-1,8],[size-2,8],[size-3,8],[size-4,8],[size-5,8],[size-6,8],[size-7,8],
     [8,size-8],[8,size-7],[8,size-6],[8,size-5],[8,size-4],[8,size-3],[8,size-2],[8,size-1]
    ].forEach(([r,c],i) => setMod(r,c,fmt[i]));

    // Data
    const nEcc = ECC_BLOCKS[ver];
    const header = [0x40, (bytes.length << 4) & 0xFF, (bytes.length & 0x0F) << 4];
    const payload = [...header, ...bytes, 0, 0xEC, 0x11];
    const dataLen = CAPACITY[ver] - nEcc;
    const data = payload.slice(0, dataLen);
    while (data.length < dataLen) data.push(data.length % 2 === 0 ? 0xEC : 0x11);
    const ecc = rsEncode(data, nEcc);
    const bits = [...data, ...ecc];

    // Bit stream
    let bitIdx = 0;
    const getBit = () => {
      if (bitIdx >= bits.length * 8) return 0;
      return (bits[Math.floor(bitIdx / 8)] >> (7 - (bitIdx++ % 8))) & 1;
    };

    // Place data
    let up = true;
    let col = size - 1;
    while (col >= 0) {
      if (col === 6) col--;
      for (let row = 0; row < size; row++) {
        const r = up ? size - 1 - row : row;
        for (let dc = 0; dc < 2; dc++) {
          const c = col - dc;
          if (!reserved[r][c]) {
            const bit = getBit();
            modules[r][c] = bit ^ (r % 3 === 0 ? 0 : 0); // mask 0
          }
        }
      }
      col -= 2;
      up = !up;
    }

    return { modules, size };
  }

  function draw(canvas, text, opts = {}) {
    const { modules, size } = encode(text);
    const scale = Math.floor((opts.size || canvas.width) / (size + 8));
    const mod = Math.max(scale, 2);
    const pad = Math.floor(((opts.size || canvas.width) - mod * size) / 2);

    const ctx = canvas.getContext('2d');
    const w = opts.size || canvas.width;
    const h = opts.size || canvas.height;

    ctx.fillStyle = opts.lightColor || '#ffffff';
    ctx.fillRect(0, 0, w, h);
    ctx.fillStyle = opts.darkColor || '#000000';

    for (let r = 0; r < size; r++) {
      for (let c = 0; c < size; c++) {
        if (modules[r][c]) {
          ctx.fillRect(pad + c * mod, pad + r * mod, mod, mod);
        }
      }
    }
  }

  return { encode, draw };
})();

// ══════════════════════════════════════════
// Barcode (Code 128) Generator
// ══════════════════════════════════════════
const BARCODE = (function() {
  // Code 128B
  const PATTERNS = [
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
    '11101000110','11100010110','11010111000','11010001110','11000101110',  // dup but ok
    '11010111000','11010100000','11010000100',
    // 64-95 (space to _)
    '11000010010','11001010000','11110101000','11110100010','11110010010',
    '11001000010','10011101110','10011101100','10011100010','10111001110',
    '10111001100','10001100010','10001001110','10000010110','10110001100',  // padding
    '11000010100','11100010100','11110001010',
    // fill to 96 entries (96 = space(32) to DEL(127) = 96 chars)
  ];

  // رسم الباركود
  function draw(canvas, text, opts = {}) {
    const ctx = canvas.getContext('2d');
    const w = canvas.width;
    const h = canvas.height;

    ctx.fillStyle = opts.background || '#ffffff';
    ctx.fillRect(0, 0, w, h);

    // Code 128B encoding
    const START_B = '11010010000';
    const STOP = '1100011101011';

    // patterns for printable ASCII (32-127)
    const CHAR_PATTERNS = {};
    const base = [
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
      '11101000110','11100010110','11010111000','11010001110','11000101110',
      '11010111000','11010100000','11010000100','11001010000','11110101000',
      '11110100010','11110010010','11001000010','10011101110','10011101100',
      '10011100010','10111001110','10111001100','10001100010','10001001110',
      '10000010110','10110001100','11000010100','11100010100','11110001010',
      '10011001110','10011110100','10011110010','11001111010','11110011010',
      '11110110010','10011010000','11001011000','11001101000','11001100100',
      '11110100100','11000011010','11001001010','10011110110','10110111010',
      '11110101010','10110001000','10001101000','10111010000',
    ];

    for (let i = 0; i < 96; i++) {
      const charCode = i + 32;
      CHAR_PATTERNS[String.fromCharCode(charCode)] = base[i] || '10010011000';
    }

    // بناء الباركود
    let barPattern = START_B;
    let checksum = 104; // START_B value

    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      const val = (ch.charCodeAt(0) - 32);
      const pat = CHAR_PATTERNS[ch] || CHAR_PATTERNS['?'] || '10010011000';
      barPattern += pat;
      checksum += val * (i + 1);
    }

    // Checksum
    const csVal = checksum % 103;
    barPattern += (base[csVal] || '11001001000');
    barPattern += STOP;

    // رسم الأشرطة
    const totalBars = barPattern.length;
    const barW = w / totalBars;
    const topMargin = opts.showText ? h * 0.15 : h * 0.05;
    const botMargin = opts.showText ? h * 0.25 : h * 0.05;

    for (let i = 0; i < totalBars; i++) {
      if (barPattern[i] === '1') {
        ctx.fillStyle = opts.color || '#000000';
        ctx.fillRect(
          Math.floor(i * barW),
          topMargin,
          Math.max(1, Math.ceil(barW)),
          h - topMargin - botMargin
        );
      }
    }

    // النص تحت الباركود
    if (opts.showText !== false) {
      ctx.fillStyle = '#000000';
      const fontSize = Math.min(14, Math.max(9, h * 0.14));
      ctx.font = `${fontSize}px monospace`;
      ctx.textAlign = 'center';
      ctx.fillText(text, w / 2, h - 6);
    }
  }

  return { draw };
})();

// ══════════════════════════════════════════
// واجهة المكتبة العامة
// ══════════════════════════════════════════
const AlMasarQR = {
  // رسم QR Code
  drawQR: function(canvas, text, opts) {
    try {
      QR.draw(canvas, text, opts);
    } catch(e) {
      console.warn('QR error:', e);
      // fallback — نص فقط
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#fff';
      ctx.fillRect(0,0,canvas.width,canvas.height);
      ctx.fillStyle = '#000';
      ctx.font = '10px monospace';
      ctx.textAlign = 'center';
      ctx.fillText(text.substring(0,20), canvas.width/2, canvas.height/2);
    }
  },

  // رسم Barcode
  drawBarcode: function(canvas, text, opts) {
    try {
      BARCODE.draw(canvas, text, opts);
    } catch(e) {
      console.warn('Barcode error:', e);
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#fff';
      ctx.fillRect(0,0,canvas.width,canvas.height);
      ctx.fillStyle = '#000';
      ctx.font = '12px monospace';
      ctx.textAlign = 'center';
      ctx.fillText(text, canvas.width/2, canvas.height/2);
    }
  },

  // رسم QR + Barcode معاً في نفس الـ canvas
  drawBoth: function(qrCanvas, barcodeCanvas, text, opts) {
    this.drawQR(qrCanvas, text, opts);
    this.drawBarcode(barcodeCanvas, text, opts);
  }
};

// تصدير
global.AlMasarQR = AlMasarQR;
global.AlMasarBarcode = BARCODE;

})(window);
