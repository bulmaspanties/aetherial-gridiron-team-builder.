/*
 * Gridiron Jersey Maker engine.
 *
 * Paints a custom name and number onto the Aetherial Gridiron jersey the way the mod's own build
 * does (tools/build_jersey.py paints, tools/export_set.py squeezes the texture into the
 * atlas, tools/export_penumbra.py fills, recolours, dirties and fits the colour IDs), then
 * packages the textures as a small Penumbra add-on. The data comes from
 * tools/jersey_bake.py: the jersey painted without its name and numbers, in "windows" round
 * the places a name or number can land, plus everything the export does after painting.
 *
 * Works in the browser (global JerseyEngine, needs fflate) and in Node (require).
 */
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory(require("fflate"));
  else root.JerseyEngine = factory(root.fflate);
})(typeof self !== "undefined" ? self : this, function (fflate) {
  "use strict";
  const f32 = Math.fround;

  // ------------------------------------------------------------------ data blobs
  const DTYPES = {
    "|u1": Uint8Array, "|b1": Uint8Array, "|i1": Int8Array, "<u2": Uint16Array, "<i2": Int16Array,
    "<u4": Uint32Array, "<i4": Int32Array, "<f4": Float32Array, "<f8": Float64Array,
  };

  /** A baked blob (jersey_bake.pack): raw-deflated JSON header + arrays. */
  function unpack(bytes) {
    const raw = fflate.inflateSync(bytes);
    const hl = raw[0] | (raw[1] << 8) | (raw[2] << 16) | (raw[3] << 24);
    const head = JSON.parse(new TextDecoder().decode(raw.subarray(8, 8 + hl)));
    const base = 8 + hl;
    const arrays = {};
    for (const a of head.arrays) {
      const s = base + a.offset;
      if (a.enc === "d32") {
        // int32 differences stored byte plane by byte plane; summed back and scaled
        const m = a.nbytes / 4, p = raw.subarray(s, s + a.nbytes);
        const out = new Float64Array(m);
        let acc = 0;
        for (let i = 0; i < m; i++) {
          acc += p[i] | (p[m + i] << 8) | (p[2 * m + i] << 16) | (p[3 * m + i] << 24);
          out[i] = acc / a.scale;
        }
        arrays[a.name] = { data: out, shape: a.shape };
      } else {
        const T = DTYPES[a.dtype];
        const nb = a.nbytes != null ? a.nbytes : a.shape.reduce((p, q) => p * q, 1) * T.BYTES_PER_ELEMENT;
        arrays[a.name] = { data: new T(raw.slice(s, s + nb).buffer), shape: a.shape };
      }
    }
    return { arrays, meta: head.meta };
  }

  // -------------------------------------------------------------- letters and numbers
  // Glyph images as Blender loads them (rows bottom-up): RGB linearised, alpha byte/255.
  // The two lookup tables come from Blender itself (jersey_bake), so this matches exactly.
  function glyphFloat(G, key, lut) {
    const g = G.arrays[key], [h, w] = g.shape, d = g.data;
    const out = new Float32Array(h * w * 4);
    for (let i = 0; i < h * w; i++) {
      out[4 * i] = lut.rgb[d[4 * i]];
      out[4 * i + 1] = lut.rgb[d[4 * i + 1]];
      out[4 * i + 2] = lut.rgb[d[4 * i + 2]];
      out[4 * i + 3] = lut.a[d[4 * i + 3]];
    }
    return { h, w, d: out, ink: G.meta[key].ink };
  }

  const CHAR_OK = /^[A-Z0-9 '.\-]$/;

  /** compose_text: glyphs side by side, trimmed to their ink; out = out*(1-a) + g*a on all four channels. */
  function composeText(G, lut, text, folder, spacing, spaceWidth = 0.45) {
    const glyphs = [];
    for (const ch of text.toUpperCase()) {
      if (ch === " ") { glyphs.push(null); continue; }
      const key = folder + "/" + ch;
      if (!G.arrays[key]) continue;
      glyphs.push(glyphFloat(G, key, lut));
    }
    const real = glyphs.filter(Boolean);
    if (!real.length) return null;
    const h = real[0].h;
    const gap = Math.trunc(h * spacing), space = Math.trunc(h * spaceWidth * 0.5);
    let width = gap * (glyphs.length - 1);
    for (const g of glyphs) width += g ? g.ink[1] - g.ink[0] + 1 : space;
    const out = new Float32Array(h * width * 4);
    let x = 0;
    for (const g of glyphs) {
      if (!g) { x += space + gap; continue; }
      const w = g.ink[1] - g.ink[0] + 1;
      for (let y = 0; y < h; y++) {
        for (let i = 0; i < w; i++) {
          const gi = 4 * (y * g.w + g.ink[0] + i), oi = 4 * (y * width + x + i);
          const a = g.d[gi + 3], ia = f32(1 - a);
          for (let c = 0; c < 4; c++) out[oi + c] = f32(f32(out[oi + c] * ia) + f32(g.d[gi + c] * a));
        }
      }
      x += w + gap;
    }
    return { h, w: width, d: out };
  }

  function erode(m, h, w, n) {
    let cur = m.slice();
    for (let k = 0; k < n; k++) {
      const nxt = new Uint8Array(h * w);
      for (let y = 0; y < h; y++) {
        const yu = (y + 1) % h, yd = (y - 1 + h) % h;
        for (let x = 0; x < w; x++) {
          const i = y * w + x;
          nxt[i] = cur[i] & cur[yu * w + x] & cur[yd * w + x] & cur[y * w + (x + 1) % w] & cur[y * w + (x - 1 + w) % w];
        }
      }
      cur = nxt;
    }
    return cur;
  }

  /** twill: white letters over a gold outline with a dashed stitch just inside each edge. */
  function twill(img) {
    const { h, w, d } = img;
    const out = new Float32Array(d);
    const a = new Uint8Array(h * w), white = new Uint8Array(h * w), gold = new Uint8Array(h * w);
    for (let i = 0; i < h * w; i++) {
      a[i] = d[4 * i + 3] > 0.5 ? 1 : 0;
      white[i] = a[i] && Math.min(d[4 * i], d[4 * i + 1], d[4 * i + 2]) > 0.55 ? 1 : 0;
      gold[i] = a[i] && !white[i] ? 1 : 0;
    }
    const k = Math.max(Math.trunc(h * 0.012), 2);
    const dl = Math.max(Math.trunc(h * 0.016), 3);
    const ew_k = erode(white, h, w, k), ew_k2 = erode(white, h, w, k >> 1);
    const ea_2k = erode(a, h, w, 2 * k), ea_k = erode(a, h, w, k);
    const height = new Float32Array(h * w);
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const i = y * w + x;
        const dash = Math.floor((x + y) / dl) % 2 === 0;
        const rw = white[i] && !ew_k[i] && ew_k2[i] && dash;
        const rg = a[i] && !ea_2k[i] && ea_k[i] && gold[i] && dash;
        if (rw) for (let c = 0; c < 3; c++) out[4 * i + c] = f32(out[4 * i + c] * f32(0.72));
        if (rg) for (let c = 0; c < 3; c++) out[4 * i + c] = f32(out[4 * i + c] * f32(0.70));
        height[i] = white[i] ? 1.0 : gold[i] ? 0.55 : 0.0;
        if (rw || rg) height[i] = f32(height[i] - 0.3);
      }
    }
    return { img: { h, w, d: out }, height };
  }

  /** make_nameplate: a rounded blue strip with a stitched edge and the name in twill. */
  function makeNameplate(G, lut, name, blue) {
    const text0 = composeText(G, lut, name, "letters", 0.07);
    if (!text0) return null;
    const th = text0.h, tw = text0.w;
    const h = Math.trunc(th / 0.62), pad = Math.trunc(h * 0.45), w = tw + 2 * pad;
    const img = new Float32Array(h * w * 4);
    const b93 = blue.map((v) => f32(f32(v) * f32(0.93))), b125 = blue.map((v) => f32(f32(v) * f32(1.25)));
    const r = h * 0.18, sd = Math.max(Math.trunc(h * 0.05), 1);
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const i = y * w + x;
        const cx = Math.min(Math.max(x, r), w - 1 - r), cy = Math.min(Math.max(y, r), h - 1 - r);
        const inside = (x - cx) * (x - cx) + (y - cy) * (y - cy) <= r * r;
        const de = Math.min(x, w - 1 - x, y, h - 1 - y);
        const stitch = Math.abs(de - h * 0.07) < h * 0.012 && Math.floor((x + y) / sd) % 2 === 0;
        const c = stitch && inside ? b125 : b93;
        img[4 * i] = c[0]; img[4 * i + 1] = c[1]; img[4 * i + 2] = c[2]; img[4 * i + 3] = inside ? 1 : 0;
      }
    }
    const tt = twill(text0), text = tt.img.d;
    const y0 = (h - th) >> 1, x0 = pad;
    const letters = new Float32Array(h * w), lift = new Float32Array(h * w);
    for (let y = 0; y < th; y++) {
      for (let x = 0; x < tw; x++) {
        const ti = y * tw + x, oi = (y0 + y) * w + x0 + x;
        const a = text[4 * ti + 3], ia = f32(1 - a);
        for (let c = 0; c < 3; c++) img[4 * oi + c] = f32(f32(img[4 * oi + c] * ia) + f32(text[4 * ti + c] * a));
        letters[oi] = a;
        lift[oi] = tt.height[ti];
      }
    }
    return { img: { h, w, d: img }, letters, lift };
  }

  // ------------------------------------------------------------------------ layout
  function widthAt(M, z, front) {
    const L = M.layout;
    let lo = Infinity, hi = -Infinity;
    for (const p of L.torso) {
      if (Math.abs(p[2] - z) < 0.012 && (p[1] < L.cy) === front) {
        if (p[0] < lo) lo = p[0];
        if (p[0] > hi) hi = p[0];
      }
    }
    return hi >= lo ? hi - lo : 0.25;
  }

  function decal(img, center, h, right, up, facing, opts) {
    return Object.assign({ img, center, h, w: h * img.w / img.h, right, up, facing,
                           raise: 0, region: null, extra: null, extraW: 0.6 }, opts);
  }

  /**
   * The name and number decals, placed as make_layout places them (build_jersey.py):
   * nameplate under the back collar, back number below it, front number between the
   * wordmark and the tuck line, both numbers the same size, a small number on each sleeve.
   */
  function layout(M, G, lut, name, number) {
    const L = M.layout, bottom = L.tuck + 0.022, up = [0, 0, 1];
    const decals = [];
    const blue = M.colors.blue;
    let num = null;
    const digits = (number || "").replace(/[^0-9]/g, "");
    if (digits) {
      const t = twill(composeText(G, lut, digits, "digits", 0.02));
      num = { img: t.img, height: t.height };
    }
    const fit = (img, top, bot, maxW) => {
      const aspect = img.w / img.h;
      const h = Math.min((top - bot) * 0.94, maxW / aspect);
      return [h, top - h / 2 - (top - bot - h) * 0.3];
    };
    let frontFit = null;
    if (num) frontFit = fit(num.img, L.front_top, bottom, 0.82 * widthAt(M, (L.front_top + bottom) / 2, true));
    let plateBottom = L.back_neck - 0.03;
    const plate = name ? makeNameplate(G, lut, name, blue) : null;
    if (plate) {
      let ph = 0.044;
      const plateW = ph * plate.img.w / plate.img.h;
      const maxW = 0.62 * widthAt(M, L.back_neck - 0.06, false);
      if (plateW > maxW) ph *= maxW / plateW;
      const zc = L.back_neck - 0.032 - ph / 2;
      decals.push(decal(plate.img, [L.cx, 0, zc], ph, [-1, 0, 0], up, [0, 1, 0],
                        { kind: "plate", raise: 0.45, region: "blue", extra: { h: plate.img.h, w: plate.img.w, d: plate.lift }, extraW: 0.6 }));
      plateBottom = zc - ph / 2;
      const lettersImg = new Float32Array(plate.img.d);
      for (let i = 0; i < plate.img.h * plate.img.w; i++) lettersImg[4 * i + 3] = plate.letters[i];
      decals.push(decal({ h: plate.img.h, w: plate.img.w, d: lettersImg }, [L.cx, 0, zc], ph, [-1, 0, 0], up, [0, 1, 0],
                        { kind: "plate_letters", raise: 0 }));
    }
    if (num) {
      const topB = plateBottom - 0.02;
      const backFit = fit(num.img, topB, bottom, 0.82 * widthAt(M, (topB + bottom) / 2, false));
      const h = Math.min(frontFit[0], backFit[0]);
      for (const [kind, right, facing, t_] of [["front", [1, 0, 0], [0, -1, 0], L.front_top], ["back", [-1, 0, 0], [0, 1, 0], topB]]) {
        const zc = t_ - h / 2 - (t_ - bottom - h) * 0.3;
        decals.push(decal(num.img, [L.cx, 0, zc], h, right, up, facing,
                          { kind, extra: { h: num.img.h, w: num.img.w, d: num.height }, extraW: 1.0 }));
      }
      for (const side of ["sleeve_l", "sleeve_r"]) {
        const s = L.sleeves[side];
        if (!s) continue;
        decals.push(decal(num.img, s.center, s.h, s.right, s.up, s.facing,
                          { kind: side, extra: { h: num.img.h, w: num.img.w, d: num.height }, extraW: 1.0 }));
      }
    }
    return decals;
  }

  // ------------------------------------------------------------------ painting
  /** Bilinear lookup (build_jersey.sample): rows bottom-up, clamped just inside the edge. */
  function sample(img, nch, u, v, out) {
    const iw = img.w, ih = img.h;
    const x = Math.min(Math.max(u * iw - 0.5, 0), iw - 1.001);
    const y = Math.min(Math.max(v * ih - 0.5, 0), ih - 1.001);
    const x0 = Math.trunc(x), y0 = Math.trunc(y), fx = x - x0, fy = y - y0;
    const d = img.d;
    for (let c = 0; c < nch; c++) {
      const i00 = (y0 * iw + x0) * nch + c, i01 = i00 + nch, i10 = i00 + iw * nch, i11 = i10 + nch;
      const top = d[i00] * (1 - fx) + d[i01] * fx, bot = d[i10] * (1 - fx) + d[i11] * fx;
      out[c] = top * (1 - fy) + bot * fy;
    }
    return out;
  }

  const REG = { none: 0, blue: 1, gold: 2, white: 3 };
  const FLAG = { covered: 1, torso: 2, front: 4, back: 8, sleeve_l: 16, sleeve_r: 32, panel: 64, lock: 128 };
  const FACE_BIT = { front: FLAG.front, back: FLAG.back, plate: FLAG.back, plate_letters: FLAG.back,
                     sleeve_l: FLAG.sleeve_l, sleeve_r: FLAG.sleeve_r };

  /**
   * Paint the decals over one window's blank paint (4K, rows bottom-up). Returns per texel
   * linear colour, region and height, and which texels changed. The trim painted after the
   * decals (lock) keeps its colour; heights take the max, as the build does.
   */
  function paintWindow(W, decals) {
    const A = W.arrays;
    const [hs, ws] = A.flags.shape;
    const n = hs * ws;
    const flags = A.flags.data, P = A.P.data, lin = A.lin.data;
    const col = new Float32Array(3 * n);
    for (let c = 0; c < 3; c++) for (let i = 0; i < n; i++) col[3 * i + c] = f32(lin[c * n + i]);
    const reg = Uint8Array.from(A.reg.data);
    const H = new Float32Array(n);
    for (let i = 0; i < n; i++) H[i] = f32(A.H.data[i]);
    const changed = new Uint8Array(n);
    const px = new Float64Array(4), ex = new Float64Array(1);
    for (const d of decals) {
      const bit = FACE_BIT[d.kind];
      const regFixed = d.region ? REG[d.region] : 0;
      for (let i = 0; i < n; i++) {
        const fl = flags[i];
        if (!(fl & bit)) continue;
        const rx = P[i] - d.center[0], ry = P[n + i] - d.center[1], rz = P[2 * n + i] - d.center[2];
        const u = (rx * d.right[0] + ry * d.right[1] + rz * d.right[2]) / d.w + 0.5;
        const v = (rx * d.up[0] + ry * d.up[1] + rz * d.up[2]) / d.h + 0.5;
        if (!(u >= 0 && u < 1 && v >= 0 && v < 1)) continue;
        sample(d.img, 4, u, v, px);
        const a = Math.min(Math.max(px[3], 0), 1);
        let hh = a * d.raise;
        if (d.extra) hh += sample(d.extra, 1, u, v, ex)[0] * d.extraW;
        if (!(fl & FLAG.lock)) {
          for (let c = 0; c < 3; c++) col[3 * i + c] = f32(col[3 * i + c] * (1 - a) + px[c] * a);
          if (a > 0.5) reg[i] = regFixed || (Math.min(px[0], px[1], px[2]) > 0.55 ? REG.white : REG.gold);
          if (a > 0) changed[i] |= 1;
        }
        if (hh > 1e-4) {
          const m = f32(Math.max(H[i], hh));
          if (m !== H[i]) { H[i] = m; changed[i] |= 2; }
        }
      }
    }
    // the build's bleed past island edges: an empty texel copies the texel it copied in the build
    const bleed = A.bleed.data;
    for (let i = 0; i < n; i++) {
      const s = bleed[i];
      if (s >= 0 && changed[s]) {
        col[3 * i] = col[3 * s]; col[3 * i + 1] = col[3 * s + 1]; col[3 * i + 2] = col[3 * s + 2];
        reg[i] = reg[s]; H[i] = H[s]; changed[i] = changed[s];
      }
    }
    return { hs, ws, col, reg, H, changed };
  }

  // sRGB encode and Blender's float -> byte (unit_float_to_uchar_clamp), in float32
  function toByte(v) {
    v = f32(v);
    if (v <= 0) return 0;
    if (v > f32(1 - 0.5 / 255)) return 255;
    return Math.trunc(f32(f32(255 * v) + 0.5));
  }
  function srgbByte(c) {
    c = f32(Math.max(c, 0));
    const s = c <= f32(0.0031308) ? f32(c * f32(12.92)) : f32(f32(f32(1.055) * f32(Math.pow(c, 1 / 2.4))) - f32(0.055));
    return toByte(Math.min(Math.max(s, 0), 1));
  }

  function rintEven(x) {                       // numpy rint: halves to even
    const f = Math.floor(x), d = x - f;
    return d > 0.5 ? f + 1 : d < 0.5 ? f : (f % 2 === 0 ? f : f + 1);
  }

  // ------------------------------------------------------- the fabric normal map
  /** fabric_normal_map's height field at one texel (global coordinates, rows bottom-up). */
  function makeHField(M) {
    const ppm = M.px_per_m;
    const p = Math.max(ppm * 0.0022, 2.0), t = Math.max(ppm * 0.0009, 1.5), q = Math.max(ppm * 0.0035, 2.5);
    const ds = Math.max(ppm * 0.003, 2);
    const TWO_PI = f32(2 * Math.PI), PI = f32(Math.PI), K = f32(1.732);
    const fp = f32(p), ft = f32(t), fq = f32(q);
    const hexOf = (xx, yy, per) => {
      const a = f32(Math.cos(f32(f32(TWO_PI * xx) / per)));
      const b = f32(Math.cos(f32(f32(PI * f32(xx + f32(K * yy))) / per)));
      const c = f32(Math.cos(f32(f32(PI * f32(xx - f32(K * yy))) / per)));
      return f32(f32(f32(a + b) + c) / 3);
    };
    return function (x, y, raised, panel) {
      const xx = f32(x), yy = f32(y);
      const hexv = hexOf(xx, yy, fp);
      const dim = -f32(Math.pow(Math.min(Math.max(f32(f32(hexv - f32(0.55)) / f32(0.45)), 0), 1), 1.5));
      const tw = f32(f32(Math.sin(f32(f32(TWO_PI * f32(xx + yy)) / ft))) * f32(0.25));
      const knit = f32(dim + f32(tw * f32(0.4)));
      const meshv = hexOf(xx, yy, fq);
      const holes = Math.min(Math.max(f32(f32(meshv - f32(0.35)) / f32(0.4)), 0), 1);
      const dashes = Math.floor(f32(xx + yy) / ds) % 2 === 0;
      const stitch = raised > 0.12 && raised < 0.6 && dashes ? 1 : 0;
      const pan = panel ? 1 : 0;
      let h = f32(f32(raised) + f32(f32(knit * f32(0.05)) * (1 - pan)));
      h = f32(h - f32(f32(holes * f32(0.16)) * pan));
      return f32(h - f32(stitch * f32(0.08)));
    };
  }

  // ------------------------------------------------- after painting: what the export does
  /**
   * One window from source paint to the export's 2K inputs. The build saves the paint as
   * bytes (rows bottom-up); export_set squeezes the rows into the atlas (DX rows, swatch
   * strip on top); export_penumbra fills texels between islands (push-pull) and averages
   * 2x2 blocks into the 2K colour IDs' size.
   */
  function exportWindow(M, W, p, opts = {}) {
    const A = W.arrays, n = p.hs * p.ws, hs = p.hs, ws = p.ws;
    const lutA = Float32Array.from(M.lut.a);
    const [sy0] = W.meta.src_rows;
    const [r0, r1, c0, c1] = W.meta.atlas;
    const size = M.size, rowsMain = M.rows_main;
    // --- source bytes
    const colB = new Uint8Array(3 * n), regB = new Uint8Array(3 * n), nrmB = new Uint8Array(2 * n);
    const q1 = A.q1.data, nrm = A.nrm.data, flags = A.flags.data;
    const REGB = [[0, 0, 0], [255, 0, 0], [0, 255, 0], [0, 0, 255]];
    for (let i = 0; i < n; i++) {
      for (let c = 0; c < 3; c++) {
        colB[3 * i + c] = p.changed[i] & 1 ? srgbByte(p.col[3 * i + c]) : q1[c * n + i];
        regB[3 * i + c] = REGB[p.reg[i]][c];
      }
      nrmB[2 * i] = nrm[i]; nrmB[2 * i + 1] = nrm[n + i];
    }
    // normals: recompute where a neighbour's height changed (central differences)
    const hf = makeHField(M), strength = f32(M.px_per_m * 0.0006);
    const need = new Uint8Array(n);
    if (!opts.noNormals) for (let y = 1; y < hs - 1; y++) for (let x = 1; x < ws - 1; x++) {
      const i = y * ws + x;
      if (p.changed[i] & 2) { need[i - 1] = need[i + 1] = need[i - ws] = need[i + ws] = 1; }
    }
    const hcache = new Float32Array(n).fill(NaN);
    const hAt = (i) => {
      let v = hcache[i];
      if (v !== v) {
        const y = (i / ws) | 0, x = i - y * ws;
        v = hcache[i] = hf(c0 + x, sy0 + y, p.H[i], flags[i] & FLAG.panel);
      }
      return v;
    };
    for (let i = 0; i < n; i++) {
      if (!need[i]) continue;
      const gx = f32(f32(hAt(i + 1) - hAt(i - 1)) / 2), gy = f32(f32(hAt(i + ws) - hAt(i - ws)) / 2);
      const nx = f32(-gx * strength), ny = f32(-gy * strength);
      const len = f32(Math.sqrt(f32(f32(f32(nx * nx) + f32(ny * ny)) + 1)));
      nrmB[2 * i] = toByte(f32(f32(f32(nx / len) * 0.5) + 0.5));
      nrmB[2 * i + 1] = toByte(f32(f32(f32(ny / len) * 0.5) + 0.5));
    }
    // --- atlas rows (DX), as export_set.one_material squeezes them
    const ah = r1 - r0, aw = c1 - c0, an = ah * aw;
    const aCol = new Uint8Array(3 * an), aReg = new Uint8Array(3 * an), aNrm = new Uint8Array(2 * an);
    const aOk = new Uint8Array(an);
    for (let r = 0; r < ah; r++) {
      const rb = size - 1 - (r0 + r);
      if (rb >= rowsMain) continue;                        // swatch strip
      const sy = (rb + 0.5) / rowsMain * size - 0.5;
      const y0 = Math.min(Math.max(Math.floor(sy), 0), size - 1), y1 = Math.min(y0 + 1, size - 1);
      const t = sy - y0, l0 = y0 - sy0, l1 = y1 - sy0;
      if (l0 < 0 || l1 >= hs) continue;
      for (let x = 0; x < aw; x++) {
        const o = r * aw + x, s0 = l0 * ws + x, s1 = l1 * ws + x;
        for (let c = 0; c < 3; c++) {
          aCol[3 * o + c] = toByte(lutA[colB[3 * s0 + c]] * (1 - t) + lutA[colB[3 * s1 + c]] * t);
          aReg[3 * o + c] = toByte(lutA[regB[3 * s0 + c]] * (1 - t) + lutA[regB[3 * s1 + c]] * t);
        }
        for (let c = 0; c < 2; c++) aNrm[2 * o + c] = toByte(lutA[nrmB[2 * s0 + c]] * (1 - t) + lutA[nrmB[2 * s1 + c]] * t);
        aOk[o] = 1;
      }
    }
    // --- load_filled: texels whose region isn't a pure colour take the push-pull fill
    const pure = new Uint8Array(an);
    for (let o = 0; o < an; o++) pure[o] = aOk[o] && Math.max(aReg[3 * o], aReg[3 * o + 1], aReg[3 * o + 2]) >= 230 ? 1 : 0;
    const colF = new Float32Array(3 * an), nrmF = new Float32Array(2 * an);
    for (let o = 0; o < 3 * an; o++) colF[o] = lutA[aCol[o]];
    for (let o = 0; o < 2 * an; o++) nrmF[o] = lutA[aNrm[o]];
    const fc = pushPull(colF, pure, ah, aw, 3, M.fill_levels, aOk);
    const fn = opts.noNormals ? { v: nrmF, ok: aOk } : pushPull(nrmF, pure, ah, aw, 2, M.fill_levels, aOk);
    const aNrmOut = new Uint8Array(2 * an);
    for (let o = 0; o < 2 * an; o++) aNrmOut[o] = Math.min(Math.max(rintEven(f32(fn.v[o] * 255)), 0), 255);
    // --- 2K: area average of the filled colour, nearest region, island mask
    const kh = ah >> 1, kw = aw >> 1, kn = kh * kw;
    const kCol = new Float32Array(3 * kn), kReg = new Float32Array(3 * kn), kIsl = new Uint8Array(kn), kOk = new Uint8Array(kn);
    for (let R = 0; R < kh; R++) for (let C = 0; C < kw; C++) {
      const k = R * kw + C, o00 = (2 * R) * aw + 2 * C, o01 = o00 + 1, o10 = o00 + aw, o11 = o10 + 1;
      kOk[k] = fc.ok[o00] && fc.ok[o01] && fc.ok[o10] && fc.ok[o11] ? 1 : 0;
      for (let c = 0; c < 3; c++) {
        const s = f32(f32(f32(fc.v[3 * o00 + c] + fc.v[3 * o01 + c]) + fc.v[3 * o10 + c]) + fc.v[3 * o11 + c]);
        kCol[3 * k + c] = f32(s / 4);
        kReg[3 * k + c] = lutA[aReg[3 * o11 + c]];
      }
      kIsl[k] = pure[o00] + pure[o01] + pure[o10] + pure[o11] >= 3 ? 1 : 0;
    }
    return { ah, aw, aNrm: aNrmOut, aNrmOk: fn.ok, aOut: A.a_out.data, kh, kw, kCol, kReg, kIsl, kOk, kOut: A.k_out.data,
             pos: A.pos2k, cov: A.cov2k ? A.cov2k.data : null, r0, c0, debug: { aCol, aReg, aNrm, aOk, colF: fc.v, nrmB, colB, need } };
  }

  /**
   * fill_background (push-pull) restricted to a window aligned to 2^levels: a texel outside
   * the mask takes the average of its block's masked texels, at the finest block level that
   * has any. ok = 0 where no level up to `levels` has one (the caller keeps the old value).
   */
  function pushPull(vals, mask, h, w, nch, levels, valid) {
    const lv = [{ h, w, c: new Float32Array(nch * h * w), m: new Uint8Array(h * w) }];
    for (let i = 0; i < h * w; i++) {
      if (mask[i]) { lv[0].m[i] = 1; for (let c = 0; c < nch; c++) lv[0].c[nch * i + c] = vals[nch * i + c]; }
    }
    for (let k = 1; k <= levels; k++) {
      const P = lv[k - 1], H2 = P.h >> 1, W2 = P.w >> 1;
      const L = { h: H2, w: W2, c: new Float32Array(nch * H2 * W2), m: new Uint8Array(H2 * W2) };
      for (let y = 0; y < H2; y++) for (let x = 0; x < W2; x++) {
        const a = (2 * y) * P.w + 2 * x, b = a + 1, cc = a + P.w, d = cc + 1;
        const ms = P.m[a] + P.m[b] + P.m[cc] + P.m[d];
        const o = y * W2 + x;
        if (ms > 0) {
          L.m[o] = 1;
          for (let c = 0; c < nch; c++) {
            const s = f32(f32(P.c[nch * a + c] + P.c[nch * b + c]) + f32(P.c[nch * cc + c] + P.c[nch * d + c]));
            L.c[nch * o + c] = f32(s / ms);
          }
        }
      }
      lv.push(L);
    }
    const v = new Float32Array(vals), ok = new Uint8Array(h * w);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const i = y * w + x;
      if (valid && !valid[i]) continue;
      if (mask[i]) { ok[i] = 1; continue; }
      for (let k = 1; k <= levels; k++) {
        const L = lv[k], o = (y >> k) * L.w + (x >> k);
        if (L.m[o]) {
          for (let c = 0; c < nch; c++) v[nch * i + c] = L.c[nch * o + c];
          ok[i] = 1;
          break;
        }
      }
    }
    return { v, ok };
  }

  // ----------------------------------------------------------- noise (grime.py)
  // _hash works on int64 and keeps 16 bits; those come from the low 32 bits of the last
  // product, which need bits 0..44 of the first XOR: done in two 32-bit halves.
  const TWO32 = 4294967296;
  function hashv(ix, iy, iz, seed) {
    const v = [ix * 73856093, iy * 19349663, iz * 83492791, seed * 2654435761];
    let lo = 0, hi = 0;
    for (const x of v) {
      const h = Math.floor(x / TWO32), l = x - h * TWO32;
      lo = (lo ^ l) >>> 0; hi = (hi ^ h) | 0;
    }
    const lo13 = ((lo >>> 13) | (hi << 19)) >>> 0;
    const g = (lo ^ lo13) >>> 0;
    const hh = Math.imul(g, 1274126177) >>> 0;
    return f32(((hh ^ (hh >>> 16)) & 0xFFFF) / 65535);
  }
  function noise3(px, py, pz, scale, seed) {
    const s = f32(scale);
    const qx = f32(px / s), qy = f32(py / s), qz = f32(pz / s);
    const ix = Math.floor(qx), iy = Math.floor(qy), iz = Math.floor(qz);
    let fx = qx - ix, fy = qy - iy, fz = qz - iz;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy); fz = fz * fz * (3 - 2 * fz);
    let out = 0;
    for (let dx = 0; dx < 2; dx++) for (let dy = 0; dy < 2; dy++) for (let dz = 0; dz < 2; dz++) {
      const w = (dx ? fx : 1 - fx) * (dy ? fy : 1 - fy) * (dz ? fz : 1 - fz);
      out = out + w * hashv(ix + dx, iy + dy, iz + dz, seed);
    }
    return out;
  }
  function fbm(px, py, pz, scale, seed, octaves = 4) {
    let tot = 0, amp = 1, norm = 0;
    for (let o = 0; o < octaves; o++) {
      tot = tot + amp * noise3(px, py, pz, scale / 2 ** o, seed + 17 * o);
      norm += amp;
      amp *= 0.5;
    }
    return tot / norm;
  }
  const sstep = (a, b, x) => { const t = Math.min(Math.max(f32(f32(x - a) / f32(b - a)), 0), 1); return f32(f32(t * t) * f32(3 - f32(2 * t))); };
  const blob = (px, py, pz, c, r) => {
    const dx = f32(px - f32(c[0])), dy = f32(py - f32(c[1])), dz = f32(pz - f32(c[2]));
    const d2 = f32(f32(f32(dx * dx) + f32(dy * dy)) + f32(dz * dz));
    return f32(Math.exp(f32(-d2 / f32(r * r))));
  };
  const blob2 = (px, py, c, r) => {
    const dx = f32(px - f32(c[0])), dy = f32(py - f32(c[1]));
    return f32(Math.exp(f32(-f32(f32(dx * dx) + f32(dy * dy)) / f32(r * r))));
  };

  /**
   * grime.apply for the jersey ("body") as per-texel blends: dirty = clip(colour * A + B),
   * for worn, grass and muddy at once (the masks don't depend on team or kit).
   * Returns [A_worn, Bw0, Bw1, Bw2, A_grass, Bg0..2, A_muddy, Bm0..2].
   */
  function makeDirtCoeffs(M) {
    const GR = M.consts.GRIME, lm = M.consts.LANDMARKS;
    const [wornAmt, mudAmt] = GR.SLOT_AMOUNT, grassAmt = GR.GRASS_AMOUNT;
    const knees = lm.knees.map((k) => [k[0], k[1] - 0.05, k[2]]);
    return function (px, py, pz, cov, out) {
      px = f32(px); py = f32(py); pz = f32(pz);
      const z = pz;
      const low = sstep(0.62, 0.06, z);
      let kn = 0, el = 0, hp = 0, sh = 0;
      for (const k of knees) kn += blob(px, py, pz, k, 0.075);
      for (const e of lm.elbows) el += blob(px, py, pz, e, 0.06);
      for (const h of lm.hips) hp += blob(px, py, pz, h, 0.09);
      for (const s of lm.shoulders || []) sh += blob(px, py, pz, s, 0.085);
      const front = sstep(0.02, -0.06, py);
      const torsoLow = sstep(1.18, 0.95, z) * (0.4 + 0.6 * front);
      const big = fbm(px, py, pz, 0.09, 1), mid = fbm(px, py, pz, 0.03, 2), fine = fbm(px, py, pz, 0.008, 3, 3);
      const band = sstep(0.92, 1.02, z) * sstep(1.50, 1.36, z);
      const side = Math.min(Math.max(Math.abs(px) / 0.16, 0), 1) ** 2;
      const back = sstep(-0.02, 0.06, py);
      const streak = fbm(f32(px * f32(0.7)), f32(py * f32(0.7)), f32(pz * f32(2.6)), 0.05, 5);
      const torso = band * (0.75 * front + 0.45 * side + 0.85 * back) * (0.6 + 0.8 * streak) + 0.55 * sh;
      const where = Math.min(Math.max(1.15 * low + 0.9 * kn + 0.45 * el + 0.35 * hp + 0.45 * torsoLow + torso, 0), 1.4);
      const m = where * (0.55 + 0.75 * big) + 0.35 * (mid - 0.5) + 0.18 * (fine - 0.5) - 0.62;
      const mud = Math.min(Math.max(m / 0.25, 0), 1) * cov;
      const grime = Math.min(Math.max(0.25 + 0.55 * where * big + 0.2 * (mid - 0.5), 0), 1) * cov;
      const s = (kn + 0.8 * el + 0.6 * hp) * (0.45 + 0.9 * fbm(px, py, f32(pz * f32(3.0)), 0.04, 4)) - 0.45;
      const grass = Math.min(Math.max(s / 0.3, 0), 1) * cov;
      // worn: out*(1 - 0.9 gr) + 0.9 gr GRIME, then out*(1 - 0.5 gs) + 0.5 gs GRASS
      const gr = 0.42 * wornAmt * grime, gs = 0.7 * wornAmt * grass;
      const Aw = (1 - 0.9 * gr) * (1 - 0.5 * gs);
      out[0] = Aw;
      for (let ch = 0; ch < 3; ch++) out[1 + ch] = 0.9 * gr * GR.GRIME[ch] * (1 - 0.5 * gs) + 0.5 * gs * GR.GRASS[ch];
      // grass: stains
      const along = fbm(f32(px * f32(2.6)), f32(py * f32(2.6)), f32(pz * f32(0.55)), 0.035, 21);
      const across = fbm(f32(px * f32(0.6)), f32(py * f32(0.6)), f32(pz * f32(2.4)), 0.04, 22);
      const spots = fbm(px, py, pz, 0.02, 23);
      let w = 0;
      for (const k of lm.knees) {
        const thigh = sstep(k[2] - 0.06, k[2] - 0.01, z) * sstep(k[2] + 0.30, k[2] + 0.12, z) * blob2(px, py, k, 0.11);
        w += (1.0 * blob(px, py, pz, [k[0], k[1] - 0.05, k[2]], 0.085) + 0.85 * thigh * front) * along * 1.3;
      }
      for (const h of lm.hips) w += 0.8 * blob(px, py, pz, h, 0.10) * along * 1.2;
      for (const e of lm.elbows) w += 0.9 * blob(px, py, pz, e, 0.075) * (0.4 + across);
      const band2 = sstep(0.95, 1.05, z) * sstep(1.48, 1.32, z);
      w += band2 * (0.7 * side + 0.5 * back + 0.35 * front) * across * 1.4;
      let shs = 0;
      for (const s_ of lm.shoulders || []) shs += 0.7 * blob(px, py, pz, s_, 0.09);
      w += shs * across * 1.4;
      const st = Math.min(Math.max((w - 0.38) / 0.28, 0), 1) * (0.75 + 0.25 * spots) * cov;
      const a = Math.min(Math.max(st * grassAmt, 0), 1);
      const edge = Math.min(Math.max(1 - Math.abs(a - 0.35) / 0.35, 0), 1) * 0.5;
      out[4] = Aw * (1 - 0.56 * a);
      for (let ch = 0; ch < 3; ch++) {
        const stain = GR.GRASS_DARK[ch] * (1 - edge) + GR.GRASS_SOIL[ch] * edge;
        out[5 + ch] = out[1 + ch] * (1 - 0.56 * a) + 0.56 * a * stain;
      }
      // muddy
      const mm = Math.min(Math.max(mud * mudAmt, 0), 1);
      const dry = Math.min(Math.max(fbm(px, py, pz, 0.05, 9) * 1.6 - 0.45, 0), 1);
      out[8] = Aw * (1 - 0.92 * mm);
      for (let ch = 0; ch < 3; ch++) {
        const mc = (GR.MUD_WET[ch] * (1 - dry) + GR.MUD_DRY[ch] * dry) * (0.85 + 0.3 * fine);
        out[9 + ch] = out[1 + ch] * (1 - 0.92 * mm) + 0.92 * mm * mc;
      }
      return out;
    };
  }

  /** Per window, once: the dirt blends of every 2K output texel (12 numbers each). */
  function windowDirt(M, X, onProgress) {
    if (X.dirt) return X.dirt;
    const kn = X.kh * X.kw, pos = X.pos.data, f = makeDirtCoeffs(M), tmp = new Float64Array(12);
    const d = new Float32Array(12 * kn);
    for (let k = 0; k < kn; k++) {
      if (!X.kOut[k] || !X.kOk[k]) continue;
      f(pos[k], pos[kn + k], pos[2 * kn + k], X.cov[k], tmp);
      d.set(tmp, 12 * k);
      if (onProgress && (k & 16383) === 0) onProgress(k / kn);
    }
    X.dirt = d;
    return d;
  }

  function camoOf(M, X, k) {
    const kn = X.kh * X.kw;
    if (!X.camo) X.camo = new Int8Array(kn).fill(-1);
    if (X.camo[k] < 0) {
      const pos = X.pos.data;
      X.camo[k] = camoIndex(M, pos[k], pos[kn + k], pos[2 * kn + k]);
    }
    return X.camo[k];
  }

  /** The camo of a team that has one: which grey (export_penumbra.camo). */
  function camoIndex(M, px, py, pz) {
    const cfg = M.consts.CAMO, sc = cfg.scale, seed = cfg.seed;
    px = f32(px); py = f32(py); pz = f32(pz);
    const a = f32(1.37), b = f32(2.11);
    const n1 = fbm(px, py, pz, sc, seed, 3);
    const n2 = fbm(f32(px + a), f32(py + a), f32(pz + a), sc * 0.85, seed + 7, 3);
    const n3 = fbm(f32(px - b), f32(py - b), f32(pz - b), sc * 0.55, seed + 13, 3);
    let i = n1 > 0.53 ? 1 : 0;
    if (n2 > 0.56 && n1 <= 0.53) i = 2;
    if (n3 > 0.62 && n1 <= 0.53) i = 3;
    return i;
  }

  // ------------------------------------------------- team, kit, dirt -> colour IDs
  let teamNames = {};
  const teamName = (t) => teamNames[t] || t.charAt(0).toUpperCase() + t.slice(1);
  const LUMA = [0.2126, 0.7152, 0.0722];
  const lum = (c) => f32(f32(f32(c[0] * f32(LUMA[0])) + f32(c[1] * f32(LUMA[1]))) + f32(c[2] * f32(LUMA[2])));

  function dyeClass(c, colors, thresh) {
    const v = Math.max(c[0], c[1], c[2]), d0 = Math.max(v, 1e-3);
    let cls = 0, best = thresh;
    for (const k of Object.keys(colors).sort()) {
      const r = colors[k], rm = Math.max(r[0], r[1], r[2]);
      const d = Math.hypot(c[0] / d0 - r[0] / rm, c[1] / d0 - r[1] / rm, c[2] / d0 - r[2] / rm);
      if (d < best && v > 0.06) { cls = +k; best = d; }
    }
    return cls;
  }
  const srgbToLinear = (c) => (c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4));

  /**
   * Colour IDs (R = row pair x 17, G = blend) for one team/kit/dirt, for the 2K texels of one
   * window: away kit, team recolour (+ fill between islands), dirt, dye classes, then the
   * nearest family of the variant's fit (the default preset's colour table).
   */
  function variantIds(M, X, team, kit, dirt, variant) {
    const C = M.consts, kn = X.kh * X.kw;
    const theme = (C.THEME || {})[team] || null;
    const dyeColors = C.DYE_COLORS[team];
    const refs = M.away_refs[team];
    const blueRef = refs.slice(0, 3), whiteRef = refs.slice(3, 6), main = refs[6];
    const lb = Math.max(lum(blueRef), 1e-4), lw = Math.max(lum(whiteRef), 1e-4), mn = Math.max(main, 1e-4);
    const AW = C.AWAY_WHITE;
    const pos = X.pos.data, posN = kn;
    const kc = new Float32Array(3 * kn);
    const c = [0, 0, 0];
    for (let k = 0; k < kn; k++) {
      c[0] = X.kCol[3 * k]; c[1] = X.kCol[3 * k + 1]; c[2] = X.kCol[3 * k + 2];
      if (kit === "away") {
        const r0 = X.kReg[3 * k], r1 = X.kReg[3 * k + 1], r2 = X.kReg[3 * k + 2];
        const body = r0 > 0.5 && r1 < 0.5, white = r2 > 0.5 && r0 < 0.5;
        const L = lum(c);
        if (body) {
          const rel = f32(f32(L / lb) / mn);
          if (rel > 0.76 && rel < 0.86) for (let ch = 0; ch < 3; ch++) c[ch] = Math.min(Math.max(blueRef[ch] * Math.min(Math.max(rel / 0.81, 0), 1.1), 0), 1);
          else for (let ch = 0; ch < 3; ch++) c[ch] = Math.min(Math.max(AW[ch] * Math.min(Math.max(rel, 0), 1.05), 0), 1);
        } else if (white) {
          const rw = f32(L / lw);
          for (let ch = 0; ch < 3; ch++) c[ch] = Math.min(Math.max(blueRef[ch] * Math.min(Math.max(rw, 0), 1.1), 0), 1);
        }
      }
      if (theme) themeRecolor(M, theme, c, X, k);
      kc[3 * k] = c[0]; kc[3 * k + 1] = c[1]; kc[3 * k + 2] = c[2];
    }
    let kcol = kc, fillOk = null;
    if (theme) {
      const f = pushPull(kc, X.kIsl, X.kh, X.kw, 3, M.fill_levels, X.kOk);
      kcol = f.v; fillOk = f.ok;          // unresolved (needs a coarser level): keep the base texel
    }
    const dirtOff = { worn: 0, grass: 4, muddy: 8 }[dirt];
    const D = dirtOff != null ? windowDirt(M, X) : null;
    const fit = variant.fit, cent = fit.cent, ccls = fit.cent_cls, rank = fit.rank, fams = fit.fams;
    const ids = new Uint8Array(2 * kn), valid = new Uint8Array(kn);
    const cc = [0, 0, 0], dc = [0, 0, 0];
    for (let k = 0; k < kn; k++) {
      if (!X.kOut[k] || !X.kOk[k] || (fillOk && !fillOk[k])) continue;      // keep the base texel
      cc[0] = kcol[3 * k]; cc[1] = kcol[3 * k + 1]; cc[2] = kcol[3 * k + 2];
      let cls = dyeClass(cc, dyeColors, C.DYE_MATCH);
      let col = cc;
      if (D) {
        const o = 12 * k + dirtOff, A = D[o];
        for (let ch = 0; ch < 3; ch++) dc[ch] = Math.min(Math.max(cc[ch] * A + D[o + 1 + ch], 0), 1);
        const moved = Math.max(Math.abs(dc[0] - cc[0]), Math.abs(dc[1] - cc[1]), Math.abs(dc[2] - cc[2])) > C.DYE_MUD;
        const still = dyeClass(dc, dyeColors, C.DYE_DIRTY_MATCH) === cls;
        if (moved && !still) cls = 0;
        col = dc;
      }
      const mx = Math.max(col[0], col[1], col[2]), mnc = Math.min(col[0], col[1], col[2]);
      const chroma = (mx - mnc) / Math.max(mx, 1e-3);
      const kcls = cls === 0 && chroma > C.NEUTRAL_SAT && mx > 0.08 ? 3 : cls;
      let best = Infinity, lab = -1;
      for (let j = 0; j < cent.length; j++) {
        if (ccls[j] !== kcls) continue;
        const d = (col[0] - cent[j][0]) ** 2 + (col[1] - cent[j][1]) ** 2 + (col[2] - cent[j][2]) ** 2;
        if (d < best) { best = d; lab = j; }
      }
      if (lab < 0) for (let j = 0; j < cent.length; j++) {
        const d = (col[0] - cent[j][0]) ** 2 + (col[1] - cent[j][1]) ** 2 + (col[2] - cent[j][2]) ** 2;
        if (d < best) { best = d; lab = j; }
      }
      const pair = rank[lab], fam = fams[pair];
      let g = 0;
      if (fam && fam.hi - fam.lo >= 1e-4) {
        let t = 0;
        for (let ch = 0; ch < 3; ch++) t += (f32(srgbToLinear(Math.min(Math.max(col[ch], 0), 1))) - fam.mean[ch]) * fam.axis[ch];
        g = Math.min(Math.max((t - fam.lo) / (fam.hi - fam.lo), 0), 1);
      }
      ids[2 * k] = pair * 17;
      ids[2 * k + 1] = rintEven(f32(f32(g) * 255));
      valid[k] = 1;
    }
    ids.valid = valid;
    return ids;
  }

  /** theme_recolor for one pixel: nearest blend of two Moogles colours, recoloured. */
  function themeRecolor(M, theme, c, X, k) {
    const C = M.consts;
    const src = [C.MOOGLES_BLUE, C.MOOGLES_GOLD, [0.965, 0.965, 0.965], [0, 0, 0]];
    const pairs = [[0, 2], [0, 3], [1, 2], [1, 3], [0, 1]];
    let best = 0.07, pick = -1, tsel = 0;
    for (let k = 0; k < pairs.length; k++) {
      const a = src[pairs[k][0]], b = src[pairs[k][1]];
      const d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]], dd = d[0] * d[0] + d[1] * d[1] + d[2] * d[2];
      const t = Math.min(Math.max(((c[0] - a[0]) * d[0] + (c[1] - a[1]) * d[1] + (c[2] - a[2]) * d[2]) / dd, 0), 1);
      const dist = Math.hypot(c[0] - (a[0] + t * d[0]), c[1] - (a[1] + t * d[1]), c[2] - (a[2] + t * d[2]));
      if (dist < best) { best = dist; pick = k; tsel = t; }
    }
    if (pick < 0) return c;
    const [i, j] = pairs[pick];
    const tgt = (q) => q === 0 ? theme.primary : q === 1 ? theme.camo[camoOf(M, X, k)] : src[q];
    const ti = tgt(i), tj = tgt(j);
    for (let ch = 0; ch < 3; ch++) c[ch] = Math.min(Math.max(ti[ch] * (1 - tsel) + tj[ch] * tsel, 0), 1);
    return c;
  }

  // ------------------------------------------------------------- BC7 (mode 6)
  const W4 = [0, 4, 9, 13, 17, 21, 26, 30, 34, 38, 43, 47, 51, 55, 60, 64];
  function palette(x0, x1) {
    const pal = new Int32Array(64);
    for (let k = 0; k < 16; k++) for (let c = 0; c < 4; c++) pal[4 * k + c] = ((64 - W4[k]) * x0[c] + W4[k] * x1[c] + 32) >> 6;
    return pal;
  }
  function quantize(e, p) {
    const c7 = new Int32Array(4), ex = new Int32Array(4);
    for (let c = 0; c < 4; c++) { c7[c] = Math.min(Math.max(rintEven((e[c] - p) / 2), 0), 127); ex[c] = c7[c] * 2 + p; }
    return [c7, ex];
  }
  function bestP(e, wts) {
    let best = null;
    for (let pv = 0; pv < 2; pv++) {
      const [c7, ex] = quantize(e, pv);
      let err = 0;
      for (let c = 0; c < 4; c++) err += (ex[c] - e[c]) ** 2 * wts[c];
      if (!best || err < best[3]) best = [c7, ex, pv, err];
    }
    return best;
  }
  function assign(blk, pal, wts) {
    const idx = new Int32Array(16);
    let err = 0;
    for (let i = 0; i < 16; i++) {
      let bd = Infinity, bk = 0;
      for (let k = 0; k < 16; k++) {
        let d = 0;
        for (let c = 0; c < 4; c++) d += (blk[4 * i + c] - pal[4 * k + c]) ** 2 * wts[c];
        if (d < bd) { bd = d; bk = k; }
      }
      idx[i] = bk; err += bd;
    }
    return [idx, err];
  }
  function refit(blk, idx, e0, e1) {
    let a = 0, b = 0, c = 0;
    const d0 = [0, 0, 0, 0], d1 = [0, 0, 0, 0];
    for (let i = 0; i < 16; i++) {
      const w = W4[idx[i]] / 64;
      a += (1 - w) ** 2; b += (1 - w) * w; c += w * w;
      for (let ch = 0; ch < 4; ch++) { d0[ch] += (1 - w) * blk[4 * i + ch]; d1[ch] += w * blk[4 * i + ch]; }
    }
    const det = a * c - b * b;
    if (!(det > 1e-6)) return [e0.slice(), e1.slice()];
    const n0 = [], n1 = [];
    for (let ch = 0; ch < 4; ch++) {
      n0.push(Math.min(Math.max((c * d0[ch] - b * d1[ch]) / det, 0), 255));
      n1.push(Math.min(Math.max((a * d1[ch] - b * d0[ch]) / det, 0), 255));
    }
    return [n0, n1];
  }
  function pcaEndpoints(blk) {
    const m = [0, 0, 0, 0], mx = [-1, -1, -1, -1], mi = [256, 256, 256, 256];
    for (let i = 0; i < 16; i++) for (let c = 0; c < 4; c++) {
      const v = blk[4 * i + c]; m[c] += v; if (v > mx[c]) mx[c] = v; if (v < mi[c]) mi[c] = v;
    }
    for (let c = 0; c < 4; c++) m[c] /= 16;
    const cov = new Float64Array(16);
    for (let i = 0; i < 16; i++) for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++)
      cov[4 * a + b] += (blk[4 * i + a] - m[a]) * (blk[4 * i + b] - m[b]);
    let r = 0;
    for (let c = 1; c < 4; c++) if (mx[c] - mi[c] > mx[r] - mi[r]) r = c;
    let axis = [0, 0, 0, 0]; axis[r] = 1;
    for (let it = 0; it < 8; it++) {
      const nx = [0, 0, 0, 0];
      for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++) nx[a] += cov[4 * a + b] * axis[b];
      const nrm = Math.hypot(nx[0], nx[1], nx[2], nx[3]);
      if (nrm > 1e-9) axis = nx.map((v) => v / Math.max(nrm, 1e-12));
      else { axis = [0, 0, 0, 0]; axis[r] = 1; }
    }
    let tmin = Infinity, tmax = -Infinity;
    for (let i = 0; i < 16; i++) {
      let t = 0;
      for (let c = 0; c < 4; c++) t += (blk[4 * i + c] - m[c]) * axis[c];
      if (t < tmin) tmin = t; if (t > tmax) tmax = t;
    }
    const e0 = [], e1 = [];
    for (let c = 0; c < 4; c++) {
      e0.push(Math.min(Math.max(m[c] + axis[c] * tmin, 0), 255));
      e1.push(Math.min(Math.max(m[c] + axis[c] * tmax, 0), 255));
    }
    return [e0, e1];
  }
  function encodeGeneric(blk, wts, forceP) {
    let [e0, e1] = pcaEndpoints(blk), best = null;
    for (let it = 0; it < 3; it++) {
      let c0, x0, p0, c1, x1, p1;
      if (forceP == null) { [c0, x0, p0] = bestP(e0, wts); [c1, x1, p1] = bestP(e1, wts); }
      else { p0 = p1 = forceP; [c0, x0] = quantize(e0, p0); [c1, x1] = quantize(e1, p1); }
      const [idx, err] = assign(blk, palette(x0, x1), wts);
      if (!best || err < best[5]) best = [c0, c1, p0, p1, idx, err];
      if (it < 2) [e0, e1] = refit(blk, idx, Array.from(x0), Array.from(x1));
    }
    return best;
  }
  function encodeId(blk) {
    const wts = [256, 1, 0, 0];
    let rmin = 255, rmax = 0;
    for (let i = 0; i < 16; i++) { const r = blk[4 * i]; if (r < rmin) rmin = r; if (r > rmax) rmax = r; }
    let glo = 0, ghi = 0, nlo = 0, nhi = 0, gmin = 255, gmax = 0, bm = 0, am = 0;
    for (let i = 0; i < 16; i++) {
      const r = blk[4 * i], g = blk[4 * i + 1];
      if (r === rmin) { glo += g; nlo++; }
      if (r === rmax) { ghi += g; nhi++; }
      if (g < gmin) gmin = g; if (g > gmax) gmax = g;
      bm += blk[4 * i + 2]; am += blk[4 * i + 3];
    }
    bm /= 16; am /= 16;
    const single = rmin === rmax;
    const gL = single ? gmin : glo / Math.max(nlo, 1), gH = single ? gmax : ghi / Math.max(nhi, 1);
    const tryEnds = (a, b) => {
      const [c0, x0] = quantize([a, gL, bm, am], a & 1);
      const [c1, x1] = quantize([b, gH, bm, am], b & 1);
      const pal = palette(x0, x1);
      const [idx] = assign(blk, pal, wts);
      let worst = 0;
      for (let i = 0; i < 16; i++) worst = Math.max(worst, Math.abs(pal[4 * idx[i]] - blk[4 * i]));
      return { c0, c1, p0: a & 1, p1: b & 1, idx, worst };
    };
    let res = tryEnds(rmin, rmax);
    if (res.worst > 8) {
      const vals = [...new Set(Array.from({ length: 16 }, (_, i) => blk[4 * i]))].sort((x, y) => x - y);
      search:
      for (let a = Math.max(0, vals[0] - 8); a <= Math.min(255, vals[0] + 8); a++) {
        for (let b = Math.max(0, vals[vals.length - 1] - 8); b <= Math.min(255, vals[vals.length - 1] + 8); b++) {
          let ok = true;
          for (const v of vals) {
            let md = Infinity;
            for (let k = 0; k < 16; k++) md = Math.min(md, Math.abs((((64 - W4[k]) * a + W4[k] * b + 32) >> 6) - v));
            if (md > 8) { ok = false; break; }
          }
          if (ok) { res = tryEnds(a, b); break search; }
        }
      }
    }
    return [res.c0, res.c1, res.p0, res.p1, res.idx];
  }
  function packBlock(c0, c1, p0, p1, idx, out, off) {
    if (idx[0] >= 8) {
      [c0, c1] = [c1, c0]; [p0, p1] = [p1, p0];
      idx = idx.map((v) => 15 - v);
    }
    const bits = new Uint8Array(128);
    bits[6] = 1;
    let pos = 7;
    for (let ch = 0; ch < 4; ch++) for (const c of [c0, c1]) { for (let k = 0; k < 7; k++) bits[pos + k] = (c[ch] >> k) & 1; pos += 7; }
    bits[63] = p0; bits[64] = p1;
    pos = 65;
    for (let i = 0; i < 16; i++) { const nb = i === 0 ? 3 : 4; for (let k = 0; k < nb; k++) bits[pos + k] = (idx[i] >> k) & 1; pos += nb; }
    for (let b = 0; b < 16; b++) {
      let v = 0;
      for (let k = 0; k < 8; k++) v |= bits[8 * b + k] << k;
      out[off + b] = v;
    }
  }
  function encodeBlock(blk, mode, out, off) {
    let r;
    if (mode === "id") r = encodeId(blk);
    else if (mode === "normal") r = encodeGeneric(blk, [1, 1, 4, 4], 1);
    else r = encodeGeneric(blk, [1, 1, 1, 1], null);
    packBlock(r[0], r[1], r[2], r[3], r[4], out, off);
  }
  function decodeBlock(d, off, out) {               // 16 px RGBA into out (Int32Array 64)
    const bit = (p) => (d[off + (p >> 3)] >> (p & 7)) & 1;
    const field = (p, n) => { let v = 0; for (let k = 0; k < n; k++) v |= bit(p + k) << k; return v; };
    let pos = 7;
    const e = [[0, 0, 0, 0], [0, 0, 0, 0]];
    for (let ch = 0; ch < 4; ch++) for (let k = 0; k < 2; k++) { e[k][ch] = field(pos, 7); pos += 7; }
    const p0 = bit(63), p1 = bit(64);
    const x0 = e[0].map((v) => v * 2 + p0), x1 = e[1].map((v) => v * 2 + p1);
    const pal = palette(x0, x1);
    pos = 65;
    for (let i = 0; i < 16; i++) {
      const nb = i === 0 ? 3 : 4, k = field(pos, nb); pos += nb;
      for (let c = 0; c < 4; c++) out[4 * i + c] = pal[4 * k + c];
    }
  }

  /** A .tex file (BC7, mode 6): header fields and per-level views. */
  function readTex(bytes) {
    const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    const fmt = dv.getUint32(4, true), w = dv.getUint16(8, true), h = dv.getUint16(10, true), mips = bytes[14];
    const offs = [];
    for (let i = 0; i < 13; i++) offs.push(dv.getUint32(28 + 4 * i, true));
    return { fmt, w, h, mips, offs };
  }
  function decodeLevel(bytes, info, lv) {
    const w = Math.max(1, info.w >> lv), h = Math.max(1, info.h >> lv);
    const bw = Math.max(1, (w + 3) >> 2), bh = Math.max(1, (h + 3) >> 2);
    const img = new Uint8Array(w * h * 4), px = new Int32Array(64);
    for (let by = 0; by < bh; by++) for (let bx = 0; bx < bw; bx++) {
      decodeBlock(bytes, info.offs[lv] + 16 * (by * bw + bx), px);
      for (let i = 0; i < 16; i++) {
        const y = 4 * by + (i >> 2), x = 4 * bx + (i & 3);
        if (y < h && x < w) for (let c = 0; c < 4; c++) img[4 * (y * w + x) + c] = px[4 * i + c];
      }
    }
    return { w, h, img };
  }

  /** One mip level, decoded block by block on demand into a dense image; set() marks blocks. */
  function levelView(bytes, info, lv) {
    const w = Math.max(1, info.w >> lv), h = Math.max(1, info.h >> lv);
    const bw = Math.max(1, (w + 3) >> 2), bh = Math.max(1, (h + 3) >> 2);
    const img = new Uint8Array(4 * w * h), done = new Uint8Array(bw * bh), dirty = new Uint8Array(bw * bh);
    const dirtyList = [], px = new Int32Array(64);
    const need = (b) => {
      if (done[b]) return;
      done[b] = 1;
      decodeBlock(bytes, info.offs[lv] + 16 * b, px);
      const bx = b % bw, by = (b / bw) | 0;
      for (let i = 0; i < 16; i++) {
        const y = 4 * by + (i >> 2), x = 4 * bx + (i & 3);
        if (y < h && x < w) { const o = 4 * (y * w + x); img[o] = px[4 * i]; img[o + 1] = px[4 * i + 1]; img[o + 2] = px[4 * i + 2]; img[o + 3] = px[4 * i + 3]; }
      }
    };
    return {
      w, h, bw, bh, img, dirtyList,
      get(x, y, c) { need((y >> 2) * bw + (x >> 2)); return img[4 * (y * w + x) + c]; },
      set(x, y, r, g, b, a) {
        const blk = (y >> 2) * bw + (x >> 2);
        need(blk);
        const o = 4 * (y * w + x);
        img[o] = r; img[o + 1] = g; img[o + 2] = b; img[o + 3] = a;
        if (!dirty[blk]) { dirty[blk] = 1; dirtyList.push(blk); }
      },
    };
  }

  /**
   * A new .tex: the base texture with level-0 texels replaced (changes: {idx: Int32Array,
   * val: Uint8Array RGBA}), the mips redone where they change (nearest for ID maps, as
   * write_tex does them; 2x2 box with rounding for the others), the wrap guard kept (the top
   * rows repeat the bottom row) and only the touched blocks encoded again.
   */
  function patchTex(base, changes, mode, guard) {
    const info = readTex(base);
    const out = new Uint8Array(base);
    let prev = null, prevList = null;
    for (let lv = 0; lv < info.mips; lv++) {
      const L = levelView(base, info, lv), w = L.w, h = L.h;
      const mark = new Uint8Array(w * h), list = [];
      const add = (i) => { if (!mark[i]) { mark[i] = 1; list.push(i); } };
      if (lv === 0) {
        const { idx, val } = changes;
        for (let j = 0; j < idx.length; j++) {
          const i = idx[j];
          L.set(i % w, (i / w) | 0, val[4 * j], val[4 * j + 1], val[4 * j + 2], val[4 * j + 3]);
          add(i);
        }
      } else {
        const pm = new Uint8Array(w * h), parents = [];
        for (const i of prevList) {
          const x = i % prev.w, y = (i / prev.w) | 0;
          if (mode === "id" && ((x & 1) || (y & 1))) continue;
          const pi = (y >> 1) * w + (x >> 1);
          if ((y >> 1) < h && (x >> 1) < w && !pm[pi]) { pm[pi] = 1; parents.push(pi); }
        }
        for (const i of parents) {
          const x = i % w, y = (i / w) | 0;
          if (mode === "id") {
            L.set(x, y, prev.get(2 * x, 2 * y, 0), prev.get(2 * x, 2 * y, 1), prev.get(2 * x, 2 * y, 2), prev.get(2 * x, 2 * y, 3));
          } else {
            const v = [0, 0, 0, 0];
            for (let c = 0; c < 4; c++) {
              const m = f32(f32(f32(f32(prev.get(2 * x, 2 * y, c) + prev.get(2 * x + 1, 2 * y, c)) + prev.get(2 * x, 2 * y + 1, c))
                                + prev.get(2 * x + 1, 2 * y + 1, c)) / 4);
              v[c] = Math.min(Math.max(Math.floor(f32(m + 0.5)), 0), 255);
            }
            L.set(x, y, v[0], v[1], v[2], v[3]);
          }
          add(i);
        }
      }
      // wrap guard: the top rows repeat the bottom row (ffxiv_write.wrap_guard)
      const g = Math.ceil(h * guard);
      if (guard && g && h > g) {
        for (const i of list.slice()) {
          if (((i / w) | 0) !== h - 1) continue;
          const x = i % w, r = L.get(x, h - 1, 0), gg = L.get(x, h - 1, 1), b = L.get(x, h - 1, 2), a = L.get(x, h - 1, 3);
          for (let y = 0; y < g; y++) { L.set(x, y, r, gg, b, a); add(y * w + x); }
        }
      }
      const blk = new Int32Array(64);
      for (const b of L.dirtyList) {
        const bx = b % L.bw, by = (b / L.bw) | 0;
        for (let i = 0; i < 16; i++) {
          // texels past the edge of a small level repeat the edge, as bc7.encode pads
          const y = Math.min(4 * by + (i >> 2), h - 1), x = Math.min(4 * bx + (i & 3), w - 1);
          for (let c = 0; c < 4; c++) blk[4 * i + c] = L.get(x, y, c);
        }
        if (mode === "id") for (let i = 0; i < 16; i++) blk[4 * i] = Math.min(Math.max(rintEven(blk[4 * i] / 17), 0), 15) * 17;
        encodeBlock(blk, mode, out, info.offs[lv] + 16 * b);
      }
      prev = L; prevList = list;
    }
    return out;
  }

  // ----------------------------------------------------------- the add-on mod
  function slug(s) { return s.replace(/[^A-Za-z0-9]+/g, "_").replace(/^_|_$/g, "") || "jersey"; }

  /** Penumbra add-on (.pmp layout): meta, default and one Single group, files. */
  function buildAddon(M, name, number, made, files) {
    const title = `Gridiron Jersey: ${name || "(no name)"} #${number}`;
    const enc = new TextEncoder();
    const zipFiles = {};
    const meta = {
      FileVersion: 3, Name: title, Author: "Gridiron Jersey Maker", Version: "1.0",
      Description: `Your own name and number on the Aetherial Gridiron jersey. Needs Aetherial Gridiron ${M.mod_version || ""} enabled; give this add-on a higher priority so its jersey wins. Pick the team, kit and dirt in this mod's Jersey group.`,
      Website: "", ModTags: ["Gridiron"],
    };
    zipFiles["meta.json"] = enc.encode(JSON.stringify(meta, null, 2));
    zipFiles["default_mod.json"] = enc.encode(JSON.stringify({ Version: 0, Files: {}, FileSwaps: {}, Manipulations: [] }, null, 2));
    const label = (v) => `${teamName(v.team)} · ${name ? name + " " : ""}#${number} - ${v.kit === "home" ? "Home" : "Away"}${v.dirt === "clean" ? "" : ", " + M.dirt_labels[v.dirt]}`;
    const group = Object.assign({}, M.main_group, {
      Name: "Jersey", Description: "Team, kit and dirt for your custom jersey.", Priority: 0, Type: "Single", DefaultSettings: 0,
      Options: made.map((v) => {
        const fl = {};
        fl[M.mat_path] = `custom\\${v.key}.mtrl`;
        fl[v.id_game] = v.id_game.replace(/\//g, "\\");
        fl[v.n_game] = v.n_game.replace(/\//g, "\\");
        fl[M.mask_custom_game] = M.mask_custom_game.replace(/\//g, "\\");
        return { Name: label(v), Description: "", Files: fl, FileSwaps: {}, Manipulations: [] };
      }),
    });
    zipFiles["group_001_jersey.json"] = enc.encode(JSON.stringify(group, null, 2));
    for (const [path, data] of Object.entries(files)) zipFiles[path] = data;
    const entries = {};
    for (const [k, v] of Object.entries(zipFiles)) entries[k] = [v, { level: k.endsWith(".tex") ? 1 : 6 }];
    return { title, zip: fflate.zipSync(entries) };
  }

  // ------------------------------------------------------------------ all of it
  /**
   * Make the add-on. get(path) -> Promise<Uint8Array> fetches a baked file. opts: name,
   * number, variants (keys like "moogles_home_clean"). progress(fraction, message).
   * Returns { title, zip (Uint8Array), filename }.
   */
  async function generate(M, get, opts, progress = () => {}) {
    teamNames = M.team_names || {};
    const lut = { rgb: Float32Array.from(M.lut.rgb), a: Float32Array.from(M.lut.a) };
    const tick = () => new Promise((r) => setTimeout(r, 0));
    const G = unpack(await get("glyphs.bin"));
    const name = (opts.name || "").toUpperCase(), number = (opts.number || "").replace(/[^0-9]/g, "");
    const decals = layout(M, G, lut, name, number);
    const chosen = M.variants.filter((v) => opts.variants.includes(v.key));
    const teams = [...new Set(chosen.map((v) => v.team))];
    const wins = [];
    for (let i = 0; i < M.windows.length; i++) {
      progress(0.02 + 0.28 * i / M.windows.length, "Painting the name and number");
      await tick();
      const W = unpack(await get(M.windows[i].file));
      const X = exportWindow(M, W, paintWindow(W, decals));
      delete X.debug;
      wins.push(X);
    }
    const files = {};
    const total = teams.length + chosen.length;
    let step = 0;
    for (const team of teams) {
      progress(0.3 + 0.6 * step / total, `Raised stitching (${teamName(team)})`);
      await tick();
      const idx = [], val = [];
      for (const X of wins) {
        for (let r = 0; r < X.ah; r++) for (let x = 0; x < X.aw; x++) {
          const o = r * X.aw + x;
          if (X.aOut[o] && X.aNrmOk[o]) { idx.push((X.r0 + r) * M.size + X.c0 + x); val.push(X.aNrm[2 * o], X.aNrm[2 * o + 1], 255, 255); }
        }
      }
      const changes = { idx: Int32Array.from(idx), val: Uint8Array.from(val) };
      const base = fflate.inflateSync(await get(`base/n_${team}.bin`));
      const v0 = chosen.find((v) => v.team === team);
      files[v0.n_game] = patchTex(base, changes, "normal", M.wrap_guard);
      step++;
    }
    for (const v of chosen) {
      progress(0.3 + 0.6 * step / total, `Colours: ${teamName(v.team)}, ${v.kit}, ${v.dirt}`);
      await tick();
      const idx = [], val = [], K = M.size >> 1;
      for (const X of wins) {
        const ids = variantIds(M, X, v.team, v.kit, v.dirt, v);
        for (let R = 0; R < X.kh; R++) for (let C = 0; C < X.kw; C++) {
          const k = R * X.kw + C;
          if (ids.valid[k]) { idx.push(((X.r0 >> 1) + R) * K + (X.c0 >> 1) + C); val.push(ids[2 * k], ids[2 * k + 1], 0, 255); }
        }
      }
      const changes = { idx: Int32Array.from(idx), val: Uint8Array.from(val) };
      const base = fflate.inflateSync(await get(v.base_id));
      files[v.id_game] = patchTex(base, changes, "id", M.wrap_guard);
      files[`custom/${v.key}.mtrl`] = await get(v.mtrl);
      step++;
    }
    files[M.mask_custom_game] = fflate.inflateSync(await get("base/mask.bin"));
    progress(0.95, "Packing the add-on");
    await tick();
    const out = buildAddon(M, name, number, chosen, files);
    progress(1, "Done");
    return Object.assign(out, { filename: `Gridiron Jersey - ${name ? slug(name) + " " : ""}${number}.zip` });
  }

  return {
    generate, unpack, composeText, twill, makeNameplate, layout, widthAt, sample, paintWindow, exportWindow, pushPull,
    variantIds, themeRecolor, camoIndex, makeDirtCoeffs, windowDirt, fbm, noise3, hashv,
    readTex, decodeLevel, levelView, patchTex, encodeBlock, decodeBlock, buildAddon, slug,
    toByte, srgbByte, rintEven, REG, FLAG, CHAR_OK, f32,
    _internal: { glyphFloat, erode, makeHField },
  };
});
