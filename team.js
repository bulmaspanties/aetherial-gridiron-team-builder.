/*
 * Aetherial Gridiron Team Builder engine.
 *
 * Gives every piece of Aetherial Gridiron a team's own colours, stripes and lettering, the way
 * the mod's export does it (tools/export_penumbra.py: recolour, fill between the UV islands,
 * dirt from tools/grime.py, colour families, colour IDs, materials), and packages the result
 * as a Penumbra add-on. The helmet's shell is redrawn from the build's own formulas
 * (tools/build_helmet.py, make_shell_textures) with the chosen stripes and logo; the other
 * pieces start from the release build painted without logos (tools/team_bake.py).
 *
 * Works in the browser (global TeamEngine; needs fflate and JerseyEngine) and in Node.
 */
(function (root, factory) {
  if (typeof module === "object" && module.exports) {
    module.exports = factory(require("fflate"), require("../jersey_maker/engine.js"));
  } else root.TeamEngine = factory(root.fflate, root.JerseyEngine);
})(typeof self !== "undefined" ? self : this, function (fflate, JE) {
  "use strict";
  const f32 = Math.fround;
  const clamp01 = (v) => (v < 0 ? 0 : v > 1 ? 1 : v);

  // ------------------------------------------------------------------- colour
  const srgbToLin = (c) => (c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4));
  const linToSrgb = (c) => (c <= 0.0031308 ? c * 12.92 : 1.055 * Math.pow(Math.max(c, 0), 1 / 2.4) - 0.055);
  /** Blender's float -> byte (unit_float_to_uchar_clamp), in float32 like Blender. */
  const toByte = (v) => {
    v = f32(v);
    if (!(v > 0)) return 0;
    if (v > f32(1 - 0.5 / 255)) return 255;
    return Math.floor(f32(f32(255 * v) + 0.5));
  };
  const BYTE = new Float32Array(256);                 // byte -> float as Blender reads 8-bit images
  for (let i = 0; i < 256; i++) BYTE[i] = f32(i * f32(1 / 255));
  const LIN = new Float32Array(256);                  // byte -> linear (Blender's sRGB decode)
  for (let i = 0; i < 256; i++) LIN[i] = f32(srgbToLin(BYTE[i]));
  const hexToRgb = (h) => {
    const n = parseInt(h.replace("#", ""), 16);
    return [((n >> 16) & 255) / 255, ((n >> 8) & 255) / 255, (n & 255) / 255];
  };
  const LUMA = [0.2126, 0.7152, 0.0722];

  /** Small seeded random numbers (the exporter's numpy streams can't be reproduced; the
   * colour fit only needs a fixed, well-spread sample). */
  function rng(seed) {
    let a = seed >>> 0;
    return () => {
      a = (a + 0x6D2B79F5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // --------------------------------------------------------------- slot data
  /** A slot's baked blob (team_bake.py) as typed arrays. */
  function slotData(bytes) {
    const { arrays, meta } = JE.unpack(bytes);
    const D = { meta };
    for (const [k, v] of Object.entries(arrays)) D[k] = v.data, D[k + "_shape"] = v.shape;
    return D;
  }

  // ------------------------------------------------------------- texel geometry
  /**
   * grime.position_map: every texel's 3D point on the piece (Blender coordinates), from the
   * garment triangles drawn in UV space, plus coverage; then spread 4 texels into the
   * background so island edges get dirt too. Rows top-first.
   */
  function positionMap(D, size) {
    const P = D.gpos, UV = D.guv, T = D.tri, n = size * size;
    const pos = new Float32Array(3 * n), cov = new Uint8Array(n);
    const nt = T.length / 3;
    for (let t = 0; t < nt; t++) {
      const i0 = T[3 * t], i1 = T[3 * t + 1], i2 = T[3 * t + 2];
      const a0 = f32(UV[2 * i0] * size), a1 = f32(UV[2 * i0 + 1] * size);
      const b0 = f32(UV[2 * i1] * size), b1 = f32(UV[2 * i1 + 1] * size);
      const c0 = f32(UV[2 * i2] * size), c1 = f32(UV[2 * i2 + 1] * size);
      let x0 = Math.floor(Math.min(a0, b0, c0)), y0 = Math.floor(Math.min(a1, b1, c1));
      let x1 = Math.ceil(Math.max(a0, b0, c0)), y1 = Math.ceil(Math.max(a1, b1, c1));
      x0 = Math.max(x0, 0); y0 = Math.max(y0, 0); x1 = Math.min(x1, size); y1 = Math.min(y1, size);
      if (x1 <= x0 || y1 <= y0) continue;
      const e0 = f32(b1 - c1), e1 = f32(c0 - b0), e2 = f32(c1 - a1), e3 = f32(a0 - c0);
      const den = f32(f32(e0 * e3) + f32(e1 * f32(a1 - c1)));
      if (Math.abs(den) < 1e-12) continue;
      // Blender coordinates of the corners: game (x, y, z) -> (x, -z, y)
      const px0 = P[3 * i0], py0 = -P[3 * i0 + 2], pz0 = P[3 * i0 + 1];
      const px1 = P[3 * i1], py1 = -P[3 * i1 + 2], pz1 = P[3 * i1 + 1];
      const px2 = P[3 * i2], py2 = -P[3 * i2 + 2], pz2 = P[3 * i2 + 1];
      for (let gy = y0; gy < y1; gy++) {
        const dy = gy + 0.5 - c1;
        for (let gx = x0; gx < x1; gx++) {
          const dx = gx + 0.5 - c0;
          const w0 = (e0 * dx + e1 * dy) / den, w1 = (e2 * dx + e3 * dy) / den, w2 = 1 - w0 - w1;
          if (w0 < -1e-3 || w1 < -1e-3 || w2 < -1e-3) continue;
          const o = gy * size + gx;
          pos[3 * o] = w0 * px0 + w1 * px1 + w2 * px2;
          pos[3 * o + 1] = w0 * py0 + w1 * py1 + w2 * py2;
          pos[3 * o + 2] = w0 * pz0 + w1 * pz1 + w2 * pz2;
          cov[o] = 1;
        }
      }
    }
    // spread into the empty texels next to islands (np.roll: wraps round the edges)
    const dirs = [[0, 1], [0, -1], [1, 0], [-1, 0]];
    for (let it = 0; it < 4; it++) {
      for (const [ddy, ddx] of dirs) {
        const src = new Uint8Array(cov);
        const add = [];
        for (let y = 0; y < size; y++) {
          const sy = (y - ddy + size) % size;
          for (let x = 0; x < size; x++) {
            const o = y * size + x;
            if (cov[o]) continue;
            const so = sy * size + ((x - ddx + size) % size);
            if (src[so]) add.push(o, so);
          }
        }
        for (let k = 0; k < add.length; k += 2) {
          const o = add[k], so = add[k + 1];
          pos[3 * o] = pos[3 * so]; pos[3 * o + 1] = pos[3 * so + 1]; pos[3 * o + 2] = pos[3 * so + 2];
          cov[o] = 1;
        }
      }
    }
    return { pos, cov, size };
  }

  // -------------------------------------------------------------- the helmet
  /** build_helmet.lower_edge: lowest elevation of the shell at |phi|. */
  function lowerEdge(H, aphi) {
    const fw = H.face_half_width, jc = H.jaw_curve, bh = H.brow_height, jb = H.jaw_bottom, bb = H.back_bottom;
    if (aphi <= fw) return bh;
    if (aphi < fw + jc) return bh + (jb - bh) * Math.sin((aphi - fw) / jc * Math.PI / 2);
    if (aphi < 1.35) return jb;
    if (aphi < 1.9) return jb + (bb - jb) * (aphi - 1.35) / 0.55;
    return bb;
  }

  /** Helmet stripe styles: bands across the shell's centre line, by how far from it a point
   * sits (the build's |n.x| x width). Colours are roles: "a" (main stripe), "b" (pinstripes). */
  const STRIPES = {
    classic: { label: "Stripe + pinstripes", bands: [[0, 0.06, "a"], [0.075, 0.09, "b"]] },
    single: { label: "Single stripe", bands: [[0, 0.06, "a"]] },
    narrow: { label: "Narrow stripe", bands: [[0, 0.03, "a"]] },
    double: { label: "Double stripe", bands: [[0.018, 0.048, "a"]] },
    triple: { label: "Triple stripe", bands: [[0, 0.022, "a"], [0.04, 0.062, "b"]] },
    pins: { label: "Pinstripes only", bands: [[0.06, 0.075, "b"]] },
    wide: { label: "Wide stripe", bands: [[0, 0.11, "a"], [0.11, 0.125, "b"]] },
    none: { label: "None", bands: [] },
  };

  /** Pants side stripe styles: bands by distance from the stripe's centre line down the outside
   * of the leg (m, round the leg), in roles "a" (the stripe colour) and "b" (the piping); the
   * rest is the pants colour. "classic" is the release's own stripe. */
  const PANTS_STRIPES = {
    classic: { label: "Stripe + piping", bands: [[0, 0.010, "a"], [0.010, 0.014, "b"]] },
    wide: { label: "Wide stripe", bands: [[0, 0.017, "a"], [0.017, 0.021, "b"]] },
    narrow: { label: "Narrow stripe", bands: [[0, 0.005, "a"], [0.005, 0.008, "b"]] },
    split: { label: "Split stripe", bands: [[0, 0.0025, "b"], [0.0025, 0.0105, "a"], [0.0105, 0.0135, "b"]] },
    double: { label: "Double stripe", bands: [[0.0035, 0.0115, "a"]] },
    triple: { label: "Triple stripe", bands: [[0, 0.0045, "a"], [0.0075, 0.0125, "b"]] },
    plain: { label: "No stripe", bands: [] },
  };
  /** Sleeve stripe styles: bands by distance from the sleeve hem (m), inside the knit cuff the
   * build raises (the bake's stripes.sleeve_top), in the jersey's "trim" or "numbers" colour;
   * the rest of the cuff is the body colour. "classic" is the release's own stripes. */
  const SLEEVE_STRIPES = {
    classic: { label: "Two stripes", bands: [[0.005, 0.016, "trim"], [0.016, 0.022, "numbers"], [0.022, 0.033, "trim"], [0.033, 0.037, "numbers"]] },
    three: { label: "Three stripes", bands: [[0.005, 0.011, "trim"], [0.011, 0.015, "numbers"], [0.015, 0.021, "trim"], [0.021, 0.025, "numbers"], [0.025, 0.031, "trim"], [0.031, 0.035, "numbers"]] },
    wide: { label: "One wide stripe", bands: [[0.005, 0.029, "trim"], [0.029, 0.034, "numbers"]] },
    split: { label: "Wide + narrow", bands: [[0.004, 0.020, "trim"], [0.024, 0.030, "trim"], [0.030, 0.034, "numbers"]] },
    trim: { label: "Trim at the hem", bands: [[0, 0.008, "trim"]] },
    plain: { label: "No stripes", bands: [] },
  };
  // the families the build paints (export_penumbra's Moogles references) and their region codes
  const FAMILY = { a: "blue", b: "white", main: "gold", body: "blue", trim: "gold", numbers: "white", band: "gold" };
  const FAMILY_REG = { blue: 1, gold: 2, white: 3 };
  /** Sock stripe styles: bands by depth below a line 5 cm above the pants hem (m: 0.05 is the
   * hem; the bake's stripe map for the feet), in the socks' "band" colour; the rest of the sock is
   * as it is. "none" is the release's plain sock. */
  const SOCK_STRIPES = {
    none: { label: "No stripes", bands: [] },
    two: { label: "Two stripes", bands: [[0.070, 0.085, "band"], [0.097, 0.112, "band"]] },
    three: { label: "Three stripes", bands: [[0.066, 0.076, "band"], [0.084, 0.094, "band"], [0.102, 0.112, "band"]] },
    wide: { label: "Wide band", bands: [[0.068, 0.110, "band"]] },
    top: { label: "Band at the top (shorts)", bands: [[0.022, 0.045, "band"]] },
  };
  const PANTS_REACH = Math.max(...Object.values(PANTS_STRIPES).map((s) => Math.max(0, ...s.bands.map((b) => b[1])))) + 0.003;

  /**
   * A stripe style drawn into a piece's logo-free paint (sRGB floats, top row first): every
   * texel in the stripe zone (from the bake's stripe map, `D.stripe`) takes its new family's
   * reference colour (the Moogles blue, gold or white) at its own shading, so the team
   * recolour then gives it the team's colours and the dyes find it. The pants zone is every
   * texel within reach of the side line below the waistband (wider than any style, so a
   * narrower style clears a wider one); the jersey's is the sleeve cuff. Texels that optional
   * parts take a solid colour from (the towel, the tail pieces, the shorts' hem: `meta.locks`)
   * keep theirs. Returns {img, reg} (new arrays), or null for the release's own stripes or when
   * the bake has no stripe map.
   */
  function restripe(C, D, img, size, slot, style) {
    const S = C.stripes, map = D.stripe;
    if (!S || !map || !style || style === "classic" || style === "none") return null;
    const st = (slot === "legs" ? PANTS_STRIPES : slot === "feet" ? SOCK_STRIPES : SLEEVE_STRIPES)[style];
    if (!st) return null;
    const ref = {
      blue: C.moogles_blue.map(srgbToLin), gold: C.moogles_gold.map(srgbToLin), white: [0.965, 0.965, 0.965].map(srgbToLin),
    };
    const B = ref.blue, G = ref.gold, W = ref.white;
    const m = [B[0], G[0], W[0], B[1], G[1], W[1], B[2], G[2], W[2]];
    const det = m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6]) + m[2] * (m[3] * m[7] - m[4] * m[6]);
    const inv = [
      (m[4] * m[8] - m[5] * m[7]) / det, (m[2] * m[7] - m[1] * m[8]) / det, (m[1] * m[5] - m[2] * m[4]) / det,
      (m[5] * m[6] - m[3] * m[8]) / det, (m[0] * m[8] - m[2] * m[6]) / det, (m[2] * m[3] - m[0] * m[5]) / det,
      (m[3] * m[7] - m[4] * m[6]) / det, (m[1] * m[6] - m[0] * m[7]) / det, (m[0] * m[4] - m[1] * m[3]) / det,
    ];
    const n = size * size, strip = Math.ceil(size * C.strip), scale = (slot === "feet" ? S.sock_range || 0.45 : S.range) / 255;
    const locked = new Uint8Array(n), rl = Math.max(1, Math.round(3 * size / 2048));
    for (const [lx, ly] of (D.meta && D.meta.locks) || []) {
      const cx = Math.floor(lx * size), cy = Math.floor(ly * size);
      for (let y = Math.max(cy - rl, 0); y <= Math.min(cy + rl, size - 1); y++)
        for (let x = Math.max(cx - rl, 0); x <= Math.min(cx + rl, size - 1); x++) locked[y * size + x] = 1;
    }
    const out = new Float32Array(img), reg = new Uint8Array(D.reg);
    const nc = D.stripe_shape ? D.stripe_shape[2] : 2;
    const legs = slot === "legs", feet = slot === "feet", top = S.sleeve_top;
    for (let i = strip * size; i < n; i++) {
      if (locked[i]) continue;
      const d = map[nc * i] * scale;
      let fam;
      if (feet) {
        // socks only, and only the texels in a band: the rest keeps its paint (and the dirt fit)
        if (map[nc * i + 1] < 128) continue;
        fam = null;
        for (const [lo, hi, role] of st.bands) if (d >= lo && d < hi) { fam = role; break; }
        if (!fam) continue;
      } else if (legs) {
        if (map[nc * i] === 255 || d >= PANTS_REACH || map[nc * i + 1] * scale < S.waistband) continue;
        fam = "main";
      } else {
        if (map[nc * i] === 255 || d >= top) continue;
        fam = "body";
      }
      if (!feet) for (const [lo, hi, role] of st.bands) if (d >= lo && d < hi) { fam = role; break; }
      const l0 = srgbToLin(img[3 * i]), l1 = srgbToLin(img[3 * i + 1]), l2 = srgbToLin(img[3 * i + 2]);
      const wb = inv[0] * l0 + inv[1] * l1 + inv[2] * l2, wg = inv[3] * l0 + inv[4] * l1 + inv[5] * l2, ww = inv[6] * l0 + inv[7] * l1 + inv[8] * l2;
      if (Math.min(wb, wg, ww) < -0.12) continue;           // not one of the three (mud, skin): as it is
      const shade = Math.max(wb, 0) + Math.max(wg, 0) + Math.max(ww, 0), f = FAMILY[fam], r = ref[f];
      for (let ch = 0; ch < 3; ch++) out[3 * i + ch] = clamp01(linToSrgb(shade * r[ch]));
      reg[i] = FAMILY_REG[f];
    }
    return { img: out, reg };
  }

  /**
   * The helmet's texture at the colour IDs' size (2K, sRGB floats, top row first), as the build
   * paints it (make_shell_textures, 4K: stripes, the logo on both sides, wear), the export
   * squeezes it under the swatch strip and the exporter averages it down (2x2).
   * o: {shell, a, b: linear RGB; style: STRIPES key; logo: {rgba, w, h} (top row first, sRGB
   *     bytes, already in the team's colours) or null; swatches: sRGB 0..1 per swatch}
   */
  function paintHelmet(C, D, o) {
    const H = C.helmet, S = H.size, rows = C.rows_main, out2 = C.id_size;
    const bands = (STRIPES[o.style] || STRIPES.classic).bands.map(([lo, hi, r]) => [lo, hi, o[r]]);
    const sx = H.sx, k2 = S / out2;
    // per column: phi, its sin/cos and the lower edge
    const sinP = new Float64Array(S), cosP = new Float64Array(S), lo = new Float64Array(S);
    for (let i = 0; i < S; i++) {
      const phi = -Math.PI + 2 * Math.PI * ((i + 0.5) / S);
      sinP[i] = Math.sin(phi); cosP[i] = Math.cos(phi); lo[i] = lowerEdge(H, Math.abs(phi));
    }
    // the logo on both sides: centre direction and its two axes
    const sides = [];
    if (o.logo) {
      const [p0, e0] = H.emblem_spot;
      for (const s of [1, -1]) {
        const phi0 = s * p0, el0 = e0;
        const c = [Math.sin(phi0) * Math.cos(el0), -Math.cos(phi0) * Math.cos(el0), Math.sin(el0)];
        const a1 = [Math.cos(phi0), Math.sin(phi0), 0];
        let a2 = [c[1] * a1[2] - c[2] * a1[1], c[2] * a1[0] - c[0] * a1[2], c[0] * a1[1] - c[1] * a1[0]];
        const l = Math.hypot(...a2);
        a2 = a2.map((v) => v / l);
        if (a2[2] < 0) a2 = a2.map((v) => -v);
        sides.push({ c, a1, a2 });
      }
    }
    // logo pixels, linear, rows bottom-up as Blender holds them
    let L = null;
    if (o.logo) {
      const { rgba, w, h } = o.logo;
      L = new Float32Array(4 * w * h);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const si = 4 * ((h - 1 - y) * w + x), di = 4 * (y * w + x);
        L[di] = LIN[rgba[si]]; L[di + 1] = LIN[rgba[si + 1]]; L[di + 2] = LIN[rgba[si + 2]]; L[di + 3] = BYTE[rgba[si + 3]];
      }
    }
    const wear = D.wear, grey = H.wear_grey, mix = H.wear_mix;
    // one shell row (Blender row j from the bottom) as bytes
    const rowCache = new Map();
    const bandByte = bands.map((b) => b[2].map((v) => toByte(linToSrgb(v))));
    const shellByte = o.shell.map((v) => toByte(linToSrgb(v)));
    const col = [0, 0, 0];
    function shellRow(j) {
      if (rowCache.has(j)) return rowCache.get(j);
      const out = new Uint8Array(3 * S);
      const V = Math.pow((j + 0.5) / S, 1.15);
      const wrow = (S - 1 - j) * S;                        // the wear map is stored top row first
      for (let i = 0; i < S; i++) {
        const el = lo[i] + (Math.PI / 2 - lo[i]) * V, ce = Math.cos(el);
        const nx = sinP[i] * ce, ny = -cosP[i] * ce, nz = Math.sin(el);
        const wx = Math.abs(nx) * sx;
        let band = -1;
        for (let b = 0; b < bands.length; b++) if (wx > bands[b][0] && wx < bands[b][1] || (bands[b][0] === 0 && wx < bands[b][1])) band = b;
        let painted = false;
        if (L) {
          for (const sd of sides) {
            if (nx * sd.c[0] + ny * sd.c[1] + nz * sd.c[2] <= 0.5) continue;
            const x = ((nx * sd.a1[0] + ny * sd.a1[1] + nz * sd.a1[2]) / H.emblem_size + 1) / 2;
            const y = ((nx * sd.a2[0] + ny * sd.a2[1] + nz * sd.a2[2]) / H.emblem_size + 1) / 2;
            if (!(x >= 0 && x < 1 && y >= 0 && y < 1)) continue;
            if (!painted) {
              const base = band >= 0 ? bands[band][2] : o.shell;
              col[0] = base[0]; col[1] = base[1]; col[2] = base[2];
              painted = true;
            }
            const li = 4 * (Math.floor(y * o.logo.h) * o.logo.w + Math.floor(x * o.logo.w)), a = L[li + 3];
            for (let ch = 0; ch < 3; ch++) col[ch] = col[ch] * (1 - a) + L[li + ch] * a;
          }
        }
        const wv = wear[wrow + i];
        if (!painted && wv === 0) {
          const b = band >= 0 ? bandByte[band] : shellByte;
          out[3 * i] = b[0]; out[3 * i + 1] = b[1]; out[3 * i + 2] = b[2];
          continue;
        }
        if (!painted) {
          const base = band >= 0 ? bands[band][2] : o.shell;
          col[0] = base[0]; col[1] = base[1]; col[2] = base[2];
        }
        const w = (wv / 65535) * mix;
        for (let ch = 0; ch < 3; ch++) out[3 * i + ch] = toByte(linToSrgb(col[ch] * (1 - w) + grey[ch] * w));
      }
      rowCache.set(j, out);
      if (rowCache.size > 4) rowCache.delete(rowCache.keys().next().value);
      return out;
    }
    // atlas (4K): rows 0..rows-1 from the bottom squeeze the shell (export_set.one_material),
    // the rest is the swatch strip; then 2x2 means at the IDs' size, top row first
    const img = new Float32Array(3 * out2 * out2);
    const atlasRow = new Float32Array(3 * S);
    const sw = o.swatches, nsw = sw.length;
    const swatchRow = new Float32Array(3 * S);
    for (let i = 0; i < nsw; i++) {
      const x0 = Math.floor(S * i / nsw), x1 = Math.floor(S * (i + 1) / nsw);
      const b = sw[i].map((v) => BYTE[toByte(v)]);
      for (let x = x0; x < x1; x++) for (let ch = 0; ch < 3; ch++) swatchRow[3 * x + ch] = b[ch];
    }
    for (let r = 0; r < S; r++) {                       // Blender row r from the bottom
      if (r < rows) {
        const sy = (r + 0.5) / rows * S - 0.5;
        const y0 = Math.min(Math.max(Math.floor(sy), 0), S - 1), y1 = Math.min(y0 + 1, S - 1), t = sy - y0;
        const A = shellRow(y0), B = shellRow(y1);
        for (let x = 0; x < 3 * S; x++) atlasRow[x] = BYTE[toByte(BYTE[A[x]] * (1 - t) + BYTE[B[x]] * t)];
      } else atlasRow.set(swatchRow);
      const R = out2 - 1 - Math.floor(r / k2);            // 2K row, top first
      const wgt = 1 / (k2 * k2);
      for (let X = 0; X < out2; X++) for (let ch = 0; ch < 3; ch++) {
        let s = 0;
        for (let dx = 0; dx < k2; dx++) s += atlasRow[3 * (X * k2 + dx) + ch];
        img[3 * (R * out2 + X) + ch] += s * wgt;
      }
    }
    return img;
  }

  /**
   * The helmet's shell regions at the build's 4K (rows bottom-up): 0 shell, 1 + b stripe band b,
   * 255 logo (where the logo's alpha is over a half), as make_shell_textures keys its regions.
   */
  function helmetKeys(C, style, logo) {
    const H = C.helmet, S = H.size, sx = H.sx;
    const bands = (STRIPES[style] || STRIPES.classic).bands;
    const keys = new Uint8Array(S * S);
    const sinP = new Float64Array(S), cosP = new Float64Array(S), lo = new Float64Array(S);
    for (let i = 0; i < S; i++) {
      const phi = -Math.PI + 2 * Math.PI * ((i + 0.5) / S);
      sinP[i] = Math.sin(phi); cosP[i] = Math.cos(phi); lo[i] = lowerEdge(H, Math.abs(phi));
    }
    const sides = [];
    if (logo) {
      const [p0, e0] = H.emblem_spot;
      for (const s_ of [1, -1]) {
        const phi0 = s_ * p0, c = [Math.sin(phi0) * Math.cos(e0), -Math.cos(phi0) * Math.cos(e0), Math.sin(e0)];
        const a1 = [Math.cos(phi0), Math.sin(phi0), 0];
        let a2 = [c[1] * a1[2] - c[2] * a1[1], c[2] * a1[0] - c[0] * a1[2], c[0] * a1[1] - c[1] * a1[0]];
        const l = Math.hypot(...a2); a2 = a2.map((v) => v / l);
        if (a2[2] < 0) a2 = a2.map((v) => -v);
        sides.push({ c, a1, a2 });
      }
    }
    for (let j = 0; j < S; j++) {
      const V = Math.pow((j + 0.5) / S, 1.15);
      for (let i = 0; i < S; i++) {
        const el = lo[i] + (Math.PI / 2 - lo[i]) * V, ce = Math.cos(el);
        const nx = sinP[i] * ce, ny = -cosP[i] * ce, nz = Math.sin(el), wx = Math.abs(nx) * sx;
        let k = 0;
        for (let b = 0; b < bands.length; b++) if ((bands[b][0] === 0 || wx > bands[b][0]) && wx < bands[b][1]) k = 1 + b;
        for (const sd of sides) {
          if (nx * sd.c[0] + ny * sd.c[1] + nz * sd.c[2] <= 0.5) continue;
          const x = ((nx * sd.a1[0] + ny * sd.a1[1] + nz * sd.a1[2]) / H.emblem_size + 1) / 2;
          const y = ((nx * sd.a2[0] + ny * sd.a2[1] + nz * sd.a2[2]) / H.emblem_size + 1) / 2;
          if (!(x >= 0 && x < 1 && y >= 0 && y < 1)) continue;
          const a = logo.rgba[4 * ((logo.h - 1 - Math.floor(y * logo.h)) * logo.w + Math.floor(x * logo.w)) + 3];
          if (a > 127.5) k = 255;
        }
        keys[j * S + i] = k;
      }
    }
    return keys;
  }
  /** make_shell_textures' normal map from the regions: everything keyed unlike the texel at
   * (row S/2, column 0) is raised a little, softened, minus the scuffs; then the export's
   * squeeze into the atlas. Returns R, G bytes per 4K atlas texel (top row first). */
  function helmetNormalAtlas(C, D, keys) {
    const S = C.helmet.size, n = S * S, ref = keys[(S >> 1) * S];
    let h = new Float32Array(n), t = new Float32Array(n);
    for (let i = 0; i < n; i++) h[i] = keys[i] !== ref ? 0.25 : 0;
    for (let it = 0; it < 3; it++) {
      for (let y = 0; y < S; y++) {
        const yu = ((y + 1) % S) * S, yd = ((y - 1 + S) % S) * S, yr = y * S;
        for (let x = 0; x < S; x++) {
          t[yr + x] = (h[yr + x] + h[yd + x] + h[yu + x] + h[yr + (x + 1) % S] + h[yr + (x - 1 + S) % S]) / 5;
        }
      }
      [h, t] = [t, h];
    }
    const H = C.helmet, seams = H.seams || [];
    if (seams.length) {          // the crown plates' seam channels, as make_shell_textures cuts them
      for (let x = 0; x < S; x++) {
        const phi = -Math.PI + 2 * Math.PI * ((x + 0.5) / S), sp = Math.sin(phi), lo = lowerEdge(H, Math.abs(phi));
        for (let y = 0; y < S; y++) {
          const el = lo + (Math.PI / 2 - lo) * Math.pow((y + 0.5) / S, 1.15);
          let c = Math.min(Math.max((Math.sin(el) - H.seam_from) / 0.10, 0), 1);
          c = c * c * (3 - 2 * c);
          if (c <= 0) continue;
          const ax = Math.abs(sp * Math.cos(el));
          let d = 0;
          for (const e of seams) d += Math.exp(-(((ax - e) / H.seam_width) ** 2));
          h[y * S + x] -= H.seam_depth * c * d;
        }
      }
    }
    const wear = D.wear;
    for (let y = 0; y < S; y++) for (let x = 0; x < S; x++) h[y * S + x] -= (wear[(S - 1 - y) * S + x] / 65535) / 0.55 * 0.15;
    const rg = new Uint8Array(2 * n);
    for (let y = 0; y < S; y++) for (let x = 0; x < S; x++) {
      const i = y * S + x;
      const gy = y === 0 ? h[i + S] - h[i] : y === S - 1 ? h[i] - h[i - S] : (h[i + S] - h[i - S]) / 2;
      const gx = x === 0 ? h[i + 1] - h[i] : x === S - 1 ? h[i] - h[i - 1] : (h[i + 1] - h[i - 1]) / 2;
      const ax = -gx * 6, ay = -gy * 6, len = Math.sqrt(ax * ax + ay * ay + 1);
      rg[2 * i] = toByte(ax / len * 0.5 + 0.5); rg[2 * i + 1] = toByte(ay / len * 0.5 + 0.5);
    }
    // the atlas: Blender row r < rows squeezes the shell rows; top row first
    const rows = C.rows_main, out = new Uint8Array(2 * n);
    for (let r = 0; r < rows; r++) {
      const sy = (r + 0.5) / rows * S - 0.5;
      const y0 = Math.min(Math.max(Math.floor(sy), 0), S - 1), y1 = Math.min(y0 + 1, S - 1), tt = sy - y0;
      const R = S - 1 - r;
      for (let x = 0; x < S; x++) for (let c = 0; c < 2; c++) {
        out[2 * (R * S + x) + c] = toByte(BYTE[rg[2 * (y0 * S + x) + c]] * (1 - tt) + BYTE[rg[2 * (y1 * S + x) + c]] * tt);
      }
    }
    return out;
  }
  /** The helmet's normal map for another stripe style or logo: the release's, with the texels
   * whose lip moved encoded again. null when it's the release's own (the classic stripes). */
  function helmetNormal(C, D, base, style, logo) {
    if (!style || style === "classic") return null;
    const S = C.helmet.size;
    const moogles = { rgba: D.logo_moogles, w: D.logo_moogles_shape[1], h: D.logo_moogles_shape[0] };
    const a = helmetNormalAtlas(C, D, helmetKeys(C, "classic", moogles));
    const b = helmetNormalAtlas(C, D, helmetKeys(C, style, logo));
    const idx = [], val = [];
    for (let i = 0; i < S * S; i++) {
      if (a[2 * i] !== b[2 * i] || a[2 * i + 1] !== b[2 * i + 1]) { idx.push(i); val.push(b[2 * i], b[2 * i + 1], 255, 255); }
    }
    if (!idx.length) return null;
    return JE.patchTex(base, { idx: Int32Array.from(idx), val: Uint8Array.from(val) }, "normal", C.wrap_guard);
  }

  // ---------------------------------------------------------------- recolour
  /**
   * The team's colours on a piece painted in the Moogles colours. Each texel is split into
   * the four colours it's painted from (Moogles blue, gold, white and black: shading is a
   * blend with black, edges a blend of two colours) in linear light, and the same blend is
   * made of the new colours, so shading, edges and logos carry over. Texels well outside
   * those four colours (mud brown, skin pink, red) keep their own colour.
   * map: {blue, gold, white}: each a linear RGB triple or {camo: [4 linear triples]}.
   */
  function makeRecolour(C, map) {
    const B = C.moogles_blue.map(srgbToLin), G = C.moogles_gold.map(srgbToLin), W = [0.965, 0.965, 0.965].map(srgbToLin);
    // inverse of [B G W] (columns): weights from a linear colour
    const m = [B[0], G[0], W[0], B[1], G[1], W[1], B[2], G[2], W[2]];
    const det = m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6]) + m[2] * (m[3] * m[7] - m[4] * m[6]);
    const inv = [
      (m[4] * m[8] - m[5] * m[7]) / det, (m[2] * m[7] - m[1] * m[8]) / det, (m[1] * m[5] - m[2] * m[4]) / det,
      (m[5] * m[6] - m[3] * m[8]) / det, (m[0] * m[8] - m[2] * m[6]) / det, (m[2] * m[3] - m[0] * m[5]) / det,
      (m[3] * m[7] - m[4] * m[6]) / det, (m[1] * m[6] - m[0] * m[7]) / det, (m[0] * m[4] - m[1] * m[3]) / det,
    ];
    const tgt = (t) => (t && t.camo ? { camo: t.camo } : { rgb: t });
    const tb = tgt(map.blue), tg = tgt(map.gold), tw = tgt(map.white || W);
    const usesCamo = !!(tb.camo || tg.camo || tw.camo);
    const OUT = 0.12, FULL = 0.06;           // how far outside the four colours a texel may be
    /** c: sRGB in (0..1), camo: camo index (0..3) for the texel; returns sRGB. */
    function recolour(c, camo, out) {
      const l0 = LIN_F(c[0]), l1 = LIN_F(c[1]), l2 = LIN_F(c[2]);
      const wb = inv[0] * l0 + inv[1] * l1 + inv[2] * l2;
      const wg = inv[3] * l0 + inv[4] * l1 + inv[5] * l2;
      const ww = inv[6] * l0 + inv[7] * l1 + inv[8] * l2;
      const mn = Math.min(wb, wg, ww);
      if (mn < -OUT) { out[0] = c[0]; out[1] = c[1]; out[2] = c[2]; return out; }
      const kb = Math.max(wb, 0), kg = Math.max(wg, 0), kw = Math.max(ww, 0);
      const pb = tb.camo ? tb.camo[camo] : tb.rgb, pg = tg.camo ? tg.camo[camo] : tg.rgb, pw = tw.camo ? tw.camo[camo] : tw.rgb;
      const keep = mn < -FULL ? (-mn - FULL) / (OUT - FULL) : 0;
      for (let ch = 0; ch < 3; ch++) {
        const v = clamp01(linToSrgb(kb * pb[ch] + kg * pg[ch] + kw * pw[ch]));
        out[ch] = keep ? v * (1 - keep) + c[ch] * keep : v;
      }
      return out;
    }
    recolour.usesCamo = usesCamo;
    return recolour;
  }
  const LIN_F = (c) => (c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4));

  // -------------------------------------------------------- fill (push-pull)
  /** export_penumbra.fill_background on a whole image: every texel outside the islands takes
   * the colour of the nearest island (coarser and coarser averages). */
  function fillBackground(img, isl, h, w, nch = 3) {
    const lv = [{ h, w, c: new Float32Array(nch * h * w), m: new Float32Array(h * w) }];
    for (let i = 0; i < h * w; i++) if (isl[i]) { lv[0].m[i] = 1; for (let c = 0; c < nch; c++) lv[0].c[nch * i + c] = img[nch * i + c]; }
    while (Math.min(lv[lv.length - 1].h, lv[lv.length - 1].w) > 1) {
      const P = lv[lv.length - 1], H2 = P.h >> 1, W2 = P.w >> 1;
      const L = { h: H2, w: W2, c: new Float32Array(nch * H2 * W2), m: new Float32Array(H2 * W2) };
      for (let y = 0; y < H2; y++) for (let x = 0; x < W2; x++) {
        const a = 2 * y * P.w + 2 * x, b = a + 1, c2 = a + P.w, d = c2 + 1, o = y * W2 + x;
        const ms = P.m[a] + P.m[b] + P.m[c2] + P.m[d];
        if (ms > 0) {
          L.m[o] = 1;
          for (let c = 0; c < nch; c++) L.c[nch * o + c] = (P.c[nch * a + c] * P.m[a] + P.c[nch * b + c] * P.m[b] + P.c[nch * c2 + c] * P.m[c2] + P.c[nch * d + c] * P.m[d]) / ms;
        }
      }
      lv.push(L);
    }
    let fill = lv[lv.length - 1];
    let fc = fill.c, fh = fill.h, fw = fill.w;
    for (let k = lv.length - 2; k >= 0; k--) {
      const P = lv[k], nc = new Float32Array(nch * P.h * P.w);
      for (let y = 0; y < P.h; y++) for (let x = 0; x < P.w; x++) {
        const o = y * P.w + x;
        if (P.m[o] > 0) { for (let c = 0; c < nch; c++) nc[nch * o + c] = P.c[nch * o + c]; continue; }
        const sy = Math.min(y >> 1, fh - 1), sx = Math.min(x >> 1, fw - 1), so = sy * fw + sx;
        for (let c = 0; c < nch; c++) nc[nch * o + c] = fc[nch * so + c];
      }
      fc = nc; fh = P.h; fw = P.w;
    }
    return fc;
  }

  // -------------------------------------------------------------- noise, dirt
  // grime._hash on int64, done in two 32-bit halves (only the low 16 bits of the result are kept,
  // and they need bits 0..44 of the first XOR)
  const TWO32 = 4294967296;
  const HX = 73856093, HY = 19349663, HZ = 83492791, HS = 2654435761;
  function noise3(px, py, pz, scale, seed) {
    const qx = px / scale, qy = py / scale, qz = pz / scale;
    const ix = Math.floor(qx), iy = Math.floor(qy), iz = Math.floor(qz);
    let fx = qx - ix, fy = qy - iy, fz = qz - iz;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy); fz = fz * fz * (3 - 2 * fz);
    // each corner's int64 products, split into 32-bit halves once per axis
    let v = ix * HX, h = Math.floor(v / TWO32);
    const xh0 = h | 0, xl0 = (v - h * TWO32) | 0;
    v += HX; h = Math.floor(v / TWO32);
    const xh1 = h | 0, xl1 = (v - h * TWO32) | 0;
    v = iy * HY; h = Math.floor(v / TWO32);
    const yh0 = h | 0, yl0 = (v - h * TWO32) | 0;
    v += HY; h = Math.floor(v / TWO32);
    const yh1 = h | 0, yl1 = (v - h * TWO32) | 0;
    v = iz * HZ; h = Math.floor(v / TWO32);
    const zh0 = h | 0, zl0 = (v - h * TWO32) | 0;
    v += HZ; h = Math.floor(v / TWO32);
    const zh1 = h | 0, zl1 = (v - h * TWO32) | 0;
    v = seed * HS; h = Math.floor(v / TWO32);
    const sh = h | 0, sl = (v - h * TWO32) | 0;
    const gx = 1 - fx, gy = 1 - fy, gz = 1 - fz;
    return gx * (gy * (gz * H(xl0 ^ yl0 ^ zl0 ^ sl, xh0 ^ yh0 ^ zh0 ^ sh) + fz * H(xl0 ^ yl0 ^ zl1 ^ sl, xh0 ^ yh0 ^ zh1 ^ sh))
               + fy * (gz * H(xl0 ^ yl1 ^ zl0 ^ sl, xh0 ^ yh1 ^ zh0 ^ sh) + fz * H(xl0 ^ yl1 ^ zl1 ^ sl, xh0 ^ yh1 ^ zh1 ^ sh)))
         + fx * (gy * (gz * H(xl1 ^ yl0 ^ zl0 ^ sl, xh1 ^ yh0 ^ zh0 ^ sh) + fz * H(xl1 ^ yl0 ^ zl1 ^ sl, xh1 ^ yh0 ^ zh1 ^ sh))
               + fy * (gz * H(xl1 ^ yl1 ^ zl0 ^ sl, xh1 ^ yh1 ^ zh0 ^ sh) + fz * H(xl1 ^ yl1 ^ zl1 ^ sl, xh1 ^ yh1 ^ zh1 ^ sh)));
  }
  /** grime._hash's 16 bits from the XOR of the four products (low and high 32 bits). */
  function H(lo, hi) {
    const g = lo ^ ((lo >>> 13) | (hi << 19));
    const hh = Math.imul(g, 1274126177);
    return ((hh ^ (hh >>> 16)) & 0xFFFF) / 65535;
  }
  function fbm(px, py, pz, scale, seed, octaves = 4) {
    let tot = 0, amp = 1, norm = 0;
    for (let o = 0; o < octaves; o++) {
      tot += amp * noise3(px, py, pz, scale / (1 << o), seed + 17 * o);
      norm += amp; amp *= 0.5;
    }
    return tot / norm;
  }
  const sstep = (a, b, x) => { const t = clamp01((x - a) / (b - a)); return t * t * (3 - 2 * t); };
  const blob = (px, py, pz, c, r) => Math.exp(-((px - c[0]) ** 2 + (py - c[1]) ** 2 + (pz - c[2]) ** 2) / (r * r));
  const blob2 = (px, py, c, r) => Math.exp(-((px - c[0]) ** 2 + (py - c[1]) ** 2) / (r * r));

  /**
   * grime.masks and grime.stains for every texel of a slot: mud, grime, grass, fine, stains,
   * dry (the muddy variant's dried share), each 0..1. Only covered texels get dirt.
   */
  function dirtMasks(C, slot, PM, onProgress, want = { grass: true, muddy: true }) {
    const n = PM.size * PM.size, pos = PM.pos, cov = PM.cov, lm = C.landmarks;
    const mud = new Float32Array(n), grime = new Float32Array(n), grass = new Float32Array(n);
    const fine = new Float32Array(n), stains = new Float32Array(n), dry = new Float32Array(n);
    const knees = lm.knees.map((k) => [k[0], k[1] - 0.05, k[2]]);
    const body = slot === "body", legs = slot === "legs", feet = slot === "feet", head = slot === "head", hands = slot === "hands";
    for (let i = 0; i < n; i++) {
      if (!cov[i]) continue;                 // no dirt outside the islands' reach (grime: x cov)
      const px = pos[3 * i], py = pos[3 * i + 1], pz = pos[3 * i + 2];
      const z = pz;
      const low = sstep(0.62, 0.06, z);
      let kn = 0, el = 0, hp = 0;
      for (const k of knees) kn += blob(px, py, pz, k, 0.075);
      for (const e of lm.elbows) el += blob(px, py, pz, e, 0.06);
      for (const h of lm.hips) hp += blob(px, py, pz, h, 0.09);
      const front = sstep(0.02, -0.06, py);
      const torsoLow = sstep(1.18, 0.95, z) * (0.4 + 0.6 * front);
      if (onProgress && (i & 65535) === 0) onProgress(i / n);
      const big = fbm(px, py, pz, 0.09, 1), mid = fbm(px, py, pz, 0.03, 2), fn = want.muddy ? fbm(px, py, pz, 0.008, 3, 3) : 0.5;
      let torso = 0;
      if (body) {
        const band = sstep(0.92, 1.02, z) * sstep(1.50, 1.36, z);
        const side = Math.min(Math.max(Math.abs(px) / 0.16, 0), 1) ** 2;
        const back = sstep(-0.02, 0.06, py);
        let sh = 0;
        for (const s of lm.shoulders || []) sh += blob(px, py, pz, s, 0.085);
        const streak = fbm(px * 0.7, py * 0.7, pz * 2.6, 0.05, 5);
        torso = band * (0.75 * front + 0.45 * side + 0.85 * back) * (0.6 + 0.8 * streak) + 0.55 * sh;
      }
      let seat = 0;
      if (legs) {
        const back = sstep(-0.01, 0.05, py);
        seat = back * sstep(0.62, 0.72, z) * sstep(1.02, 0.92, z) * (0.5 + 0.7 * fbm(px * 0.8, py * 0.8, pz * 2.0, 0.05, 6));
      }
      const where = Math.min(Math.max(1.15 * low + 0.9 * kn + 0.45 * el + 0.35 * hp + 0.45 * torsoLow
        + (hands ? 0.7 : 0) + (head ? 0.25 : 0) + torso + 0.75 * seat, 0), 1.4);
      const m = where * (0.55 + 0.75 * big) + 0.35 * (mid - 0.5) + 0.18 * (fn - 0.5) - 0.62;
      let md = clamp01(m / 0.25);
      if (feet && want.muddy) {
        const sock = sstep(0.11, 0.15, z);
        const spots = clamp01((fbm(px, py, pz, 0.005, 31, 2) - 0.60) / 0.05) * (0.35 + 0.65 * low);
        const smear = sstep(0.24, 0.13, z) * clamp01(0.4 + 0.9 * big + 0.4 * (mid - 0.5));
        md = md * (1 - sock) + clamp01(Math.max(spots, smear)) * sock * 0.9;
      }
      const cv = cov[i] ? 1 : 0;
      mud[i] = md * cv;
      grime[i] = clamp01(0.25 + 0.55 * where * big + 0.2 * (mid - 0.5)) * cv;
      const s = (kn + 0.8 * el + 0.6 * hp) * (0.45 + 0.9 * fbm(px, py, pz * 3.0, 0.04, 4)) - 0.45;
      grass[i] = clamp01(s / 0.3) * cv;
      fine[i] = fn;
      if (want.muddy) {
        let dr = clamp01(fbm(px, py, pz, 0.05, 9) * 1.6 - 0.45);
        if (feet) dr = Math.max(dr, sstep(0.12, 0.20, z) * 0.7);
        dry[i] = dr;
      }
      if (!want.grass) continue;
      // stains (the grass variant)
      const along = fbm(px * 2.6, py * 2.6, pz * 0.55, 0.035, 21);
      const across = fbm(px * 0.6, py * 0.6, pz * 2.4, 0.04, 22);
      const spots = fbm(px, py, pz, 0.02, 23);
      let w = 0;
      for (const k of lm.knees) {
        const thigh = sstep(k[2] - 0.06, k[2] - 0.01, z) * sstep(k[2] + 0.30, k[2] + 0.12, z) * blob2(px, py, k, 0.11);
        w += (1.0 * blob(px, py, pz, [k[0], k[1] - 0.05, k[2]], 0.085) + 0.85 * thigh * front) * along * 1.3;
      }
      for (const h of lm.hips) w += 0.8 * blob(px, py, pz, h, 0.10) * along * 1.2;
      for (const e of lm.elbows) w += 0.9 * blob(px, py, pz, e, 0.075) * (0.4 + across);
      if (body) {
        const side = Math.min(Math.max(Math.abs(px) / 0.16, 0), 1) ** 2;
        const back = sstep(-0.02, 0.06, py);
        const band2 = sstep(0.95, 1.05, z) * sstep(1.48, 1.32, z);
        w += band2 * (0.7 * side + 0.5 * back + 0.35 * front) * across * 1.4;
        let shs = 0;
        for (const s_ of lm.shoulders || []) shs += 0.7 * blob(px, py, pz, s_, 0.09);
        w += shs * across * 1.4;
      }
      if (head) w += 0.6 * sstep(-0.02, 0.05, Math.abs(px) - 0.04) * across;
      if (hands) w += 0.5 * spots;
      if (feet) w += 0.6 * front * sstep(0.12, 0.25, z) * sstep(0.50, 0.38, z) * along;
      stains[i] = clamp01((w - 0.38) / 0.28) * (0.75 + 0.25 * spots) * cv;
    }
    return { mud, grime, grass, fine, stains, dry };
  }

  /** grime.apply: the dirt variant of an sRGB image (a new array; clean = the same image). */
  function applyDirt(C, slot, img, M, variant) {
    if (variant === "clean") return img;
    const G = C.grime, n = img.length / 3;
    const [wornAmt, mudAmt] = G.slot_amount[slot] || [0.8, 0.8];
    const grassAmt = (G.grass_amount && G.grass_amount[slot]) != null ? G.grass_amount[slot] : 0.8;
    const out = new Float32Array(img.length);
    for (let i = 0; i < n; i++) {
      const gr = 0.42 * wornAmt * M.grime[i], gs = 0.7 * wornAmt * M.grass[i];
      for (let ch = 0; ch < 3; ch++) {
        let v = img[3 * i + ch];
        v = v * (1 - gr) + G.GRIME[ch] * gr * 0.9 + v * gr * 0.1;
        v = v * (1 - gs) + (v * 0.5 + G.GRASS[ch] * 0.5) * gs;
        out[3 * i + ch] = v;
      }
      if (variant === "grass") {
        const a = clamp01(M.stains[i] * grassAmt);
        const edge = clamp01(1 - Math.abs(a - 0.35) / 0.35) * 0.5;
        for (let ch = 0; ch < 3; ch++) {
          const stain = G.GRASS_DARK[ch] * (1 - edge) + G.GRASS_SOIL[ch] * edge, v = out[3 * i + ch];
          out[3 * i + ch] = v * (1 - 0.8 * a) + (v * 0.3 + stain * 0.7) * 0.8 * a;
        }
      } else if (variant === "muddy") {
        const mm = clamp01(M.mud[i] * mudAmt), dr = M.dry[i], fk = 0.85 + 0.3 * M.fine[i];
        for (let ch = 0; ch < 3; ch++) {
          const mc = (G.MUD_WET[ch] * (1 - dr) + G.MUD_DRY[ch] * dr) * fk, v = out[3 * i + ch];
          out[3 * i + ch] = v * (1 - 0.92 * mm) + mc * 0.92 * mm;
        }
      }
      for (let ch = 0; ch < 3; ch++) out[3 * i + ch] = clamp01(out[3 * i + ch]);
    }
    return out;
  }

  /** export_penumbra.camo: which camo colour (0 base, 1 dark, 2 light, 3 flecks) per texel. */
  function camoMap(PM, scale, seed) {
    const n = PM.size * PM.size, pos = PM.pos, out = new Uint8Array(n);
    for (let i = 0; i < n; i++) {
      const px = pos[3 * i], py = pos[3 * i + 1], pz = pos[3 * i + 2];
      const n1 = fbm(px, py, pz, scale, seed, 3);
      let k = n1 > 0.53 ? 1 : 0;
      if (n1 <= 0.53) {
        if (fbm(px + 1.37, py + 1.37, pz + 1.37, scale * 0.85, seed + 7, 3) > 0.56) k = 2;
        if (fbm(px - 2.11, py - 2.11, pz - 2.11, scale * 0.55, seed + 13, 3) > 0.62) k = 3;
      }
      out[i] = k;
    }
    return out;
  }

  // ------------------------------------------------------------ dye classes
  /** export_penumbra.dye_classes: 1 / 2 where a texel's hue matches dye 1 / dye 2's colour
   * (colour over its brightest channel), else 0. colors: {1: sRGB, 2: sRGB}. */
  function dyeClasses(img, colors, thresh) {
    const n = img.length / 3, out = new Int8Array(n);
    const refs = Object.keys(colors).sort().map((k) => {
      const r = colors[k], m = Math.max(r[0], r[1], r[2], 1e-6);
      return [+k, r[0] / m, r[1] / m, r[2] / m];
    });
    for (let i = 0; i < n; i++) {
      const c0 = img[3 * i], c1 = img[3 * i + 1], c2 = img[3 * i + 2];
      const v = Math.max(c0, c1, c2);
      if (!(v > 0.06)) continue;
      const d0 = Math.max(v, 1e-3);
      let best = thresh, cls = 0;
      for (const [k, r0, r1, r2] of refs) {
        const d = Math.hypot(c0 / d0 - r0, c1 / d0 - r1, c2 / d0 - r2);
        if (d < best) { best = d; cls = k; }
      }
      out[i] = cls;
    }
    return out;
  }
  /** export_penumbra.dirty_classes: as the clean classes, except where mud covers the colour. */
  function dirtyClasses(C, cleanCls, clean, dirty, colors) {
    const n = cleanCls.length, out = new Int8Array(cleanCls);
    const still = dyeClasses(dirty, colors, C.dye_dirty_match);
    for (let i = 0; i < n; i++) {
      if (!out[i]) continue;
      const moved = Math.max(Math.abs(dirty[3 * i] - clean[3 * i]), Math.abs(dirty[3 * i + 1] - clean[3 * i + 1]),
        Math.abs(dirty[3 * i + 2] - clean[3 * i + 2])) > C.dye_mud;
      if (moved && still[i] !== cleanCls[i]) out[i] = 0;
    }
    return out;
  }

  // --------------------------------------------------------- colour families
  /** export_penumbra.kmeans: k-means++ seeding, 25 rounds. x: Float32Array (3 per point). */
  function kmeans(x, k, rand, iters = 25) {
    const n = x.length / 3;
    const cent = [];
    let j = Math.floor(rand() * n);
    cent.push([x[3 * j], x[3 * j + 1], x[3 * j + 2]]);
    const d = new Float64Array(n).fill(Infinity);
    for (let c = 1; c < k; c++) {
      const p = cent[c - 1];
      let sum = 0;
      for (let i = 0; i < n; i++) {
        const e = (x[3 * i] - p[0]) ** 2 + (x[3 * i + 1] - p[1]) ** 2 + (x[3 * i + 2] - p[2]) ** 2;
        if (e < d[i]) d[i] = e;
        sum += d[i];
      }
      if (!(sum > 0)) break;
      let r = rand() * sum, pick = n - 1;
      for (let i = 0; i < n; i++) { r -= d[i]; if (r <= 0) { pick = i; break; } }
      cent.push([x[3 * pick], x[3 * pick + 1], x[3 * pick + 2]]);
    }
    const kk = cent.length, C = new Float64Array(3 * kk);
    cent.forEach((c, i) => C.set(c, 3 * i));
    const lab = new Int32Array(n), S = new Float64Array(3 * kk), N = new Float64Array(kk);
    for (let it = 0; it < iters; it++) {
      S.fill(0); N.fill(0);
      for (let i = 0; i < n; i++) {
        const a = x[3 * i], b = x[3 * i + 1], c = x[3 * i + 2];
        let bd = Infinity, bj = 0;
        for (let q = 0; q < kk; q++) {
          const e = (a - C[3 * q]) ** 2 + (b - C[3 * q + 1]) ** 2 + (c - C[3 * q + 2]) ** 2;
          if (e < bd) { bd = e; bj = q; }
        }
        lab[i] = bj; S[3 * bj] += a; S[3 * bj + 1] += b; S[3 * bj + 2] += c; N[bj]++;
      }
      for (let q = 0; q < kk; q++) if (N[q]) for (let ch = 0; ch < 3; ch++) C[3 * q + ch] = S[3 * q + ch] / N[q];
    }
    return C;
  }
  function sse(x, C, count) {
    const n = x.length / 3, kk = C.length / 3;
    let tot = 0;
    for (let i = 0; i < n; i++) {
      let bd = Infinity;
      for (let q = 0; q < kk; q++) {
        const e = (x[3 * i] - C[3 * q]) ** 2 + (x[3 * i + 1] - C[3 * q + 1]) ** 2 + (x[3 * i + 2] - C[3 * q + 2]) ** 2;
        if (e < bd) bd = e;
      }
      tot += bd;
    }
    return tot / n * count;
  }
  /** export_penumbra._alloc_kmeans: share the row pairs out between the classes where they
   * cut the colour error most. */
  function allocKmeans(samples, counts, total, rand) {
    const k = {}, cent = {}, err = {}, nxt = {};
    for (const c of Object.keys(samples)) { k[c] = 1; cent[c] = kmeans(samples[c], 1, rand); err[c] = sse(samples[c], cent[c], counts[c]); }
    let used = Object.keys(samples).length;
    while (used < total) {
      for (const c of Object.keys(samples)) {
        if (!(c in nxt) && k[c] < samples[c].length / 3) {
          const ce = kmeans(samples[c], k[c] + 1, rand);
          nxt[c] = [ce, sse(samples[c], ce, counts[c])];
        }
      }
      const keys = Object.keys(nxt);
      if (!keys.length) break;
      let best = keys[0];
      for (const c of keys) if (err[c] - nxt[c][1] > err[best] - nxt[best][1]) best = c;
      [cent[best], err[best]] = nxt[best];
      delete nxt[best];
      k[best]++; used++;
    }
    return cent;
  }
  /** Largest-eigenvalue eigenvector of a symmetric 3x3 matrix (Jacobi rotations). */
  function topEigen(a) {
    const A = a.slice(), V = [1, 0, 0, 0, 1, 0, 0, 0, 1];
    for (let sweep = 0; sweep < 50; sweep++) {
      const off = Math.abs(A[1]) + Math.abs(A[2]) + Math.abs(A[5]);
      if (off < 1e-18) break;
      for (const [p, q] of [[0, 1], [0, 2], [1, 2]]) {
        const apq = A[3 * p + q];
        if (Math.abs(apq) < 1e-30) continue;
        const app = A[3 * p + p], aqq = A[3 * q + q];
        const th = (aqq - app) / (2 * apq);
        const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1));
        const c = 1 / Math.sqrt(t * t + 1), s = t * c;
        for (let r = 0; r < 3; r++) {               // A = J^T A J
          const arp = A[3 * r + p], arq = A[3 * r + q];
          A[3 * r + p] = c * arp - s * arq; A[3 * r + q] = s * arp + c * arq;
        }
        for (let r = 0; r < 3; r++) {
          const apr = A[3 * p + r], aqr = A[3 * q + r];
          A[3 * p + r] = c * apr - s * aqr; A[3 * q + r] = s * apr + c * aqr;
        }
        for (let r = 0; r < 3; r++) {
          const vrp = V[3 * r + p], vrq = V[3 * r + q];
          V[3 * r + p] = c * vrp - s * vrq; V[3 * r + q] = s * vrp + c * vrq;
        }
      }
    }
    let b = 0;
    for (let i = 1; i < 3; i++) if (A[4 * i] > A[4 * b]) b = i;
    return [V[b], V[3 + b], V[6 + b]];
  }
  /** The value at fraction q of the sorted values (numpy percentile, linear). */
  function quantile(v, q) {
    const n = v.length;
    const pos = q * (n - 1), lo = Math.floor(pos), f = pos - lo;
    const a = select(v, lo);
    if (f === 0 || lo + 1 >= n) return a;
    // the next order statistic: the smallest value above position lo (select left it to the right)
    let b = Infinity;
    for (let i = lo + 1; i < n; i++) if (v[i] < b) b = v[i];
    return a + f * (b - a);
  }
  function select(v, k) {                          // k-th smallest, in place (Hoare quickselect)
    let l = 0, r = v.length - 1;
    while (l < r) {
      const piv = v[(l + r) >> 1];
      let i = l, j = r;
      while (i <= j) {
        while (v[i] < piv) i++;
        while (v[j] > piv) j--;
        if (i <= j) { const t = v[i]; v[i] = v[j]; v[j] = t; i++; j--; }
      }
      if (k <= j) r = j; else if (k >= i) l = i; else break;
    }
    return v[k];
  }

  /**
   * export_penumbra.color_table_and_id: the texture's colour families (each family a row
   * pair: its dark and light end along its main axis), and the colour IDs (R = pair x 17,
   * G = the blend). img: sRGB floats; dye: dye class per texel (0/1/2) or null; isl: island
   * mask (the families are fitted to the islands only) or null.
   */
  function colorTableAndId(C, img, size, specular, dye, isl, seed = 1, parts = null) {
    const n = size * size, PAIRS = C.pairs, rand = rng(seed);
    const cls = new Int8Array(n);
    let anyFit = false;
    if (isl) for (let i = 0; i < n; i++) if (isl[i]) { anyFit = true; break; }
    const fit = (i) => !anyFit || isl[i];
    for (let i = 0; i < n; i++) {
      const c0 = img[3 * i], c1 = img[3 * i + 1], c2 = img[3 * i + 2];
      const mx = Math.max(c0, c1, c2), mn = Math.min(c0, c1, c2);
      const chroma = (mx - mn) / Math.max(mx, 1e-3), d = dye ? dye[i] : 0;
      cls[i] = (d === 0 && chroma > C.neutral_sat && mx > 0.08 ? 3 : d) + (parts ? 4 * parts.of[i] : 0);
    }
    // a part with a finish of its own (helmet shell, facemask) never shares a family with another
    const nkeys = parts ? 4 * parts.spec.length : 4, seen = new Uint8Array(nkeys);
    for (let i = 0; i < n; i++) seen[cls[i]] = 1;
    const classes = [...Array(nkeys).keys()].filter((c) => seen[c]);
    const samples = {}, counts = {};
    for (const c of classes) {
      let m = 0;
      for (let i = 0; i < n; i++) if (cls[i] === c && fit(i)) m++;
      const all = m === 0;
      const idx = new Int32Array(all ? cls.reduce((a, v) => a + (v === c), 0) : m);
      let q = 0;
      for (let i = 0; i < n; i++) if (cls[i] === c && (all || fit(i))) idx[q++] = i;
      counts[c] = idx.length;
      const take = Math.min(idx.length, Math.max(20000, Math.floor(300000 * idx.length / n)));
      for (let i = 0; i < take; i++) {                       // partial Fisher-Yates
        const j = i + Math.floor(rand() * (idx.length - i));
        const t = idx[i]; idx[i] = idx[j]; idx[j] = t;
      }
      const x = new Float32Array(3 * take);
      for (let i = 0; i < take; i++) { const o = idx[i]; x[3 * i] = img[3 * o]; x[3 * i + 1] = img[3 * o + 1]; x[3 * i + 2] = img[3 * o + 2]; }
      samples[c] = x;
    }
    const cents = allocKmeans(samples, counts, PAIRS, rand);
    const cent = [], centCls = [];
    for (const c of classes) for (let q = 0; q < cents[c].length / 3; q++) {
      cent.push([cents[c][3 * q], cents[c][3 * q + 1], cents[c][3 * q + 2]]); centCls.push(c);
    }
    // each texel joins the nearest family of its own class
    const lab = new Uint8Array(n);
    const byCls = [...Array(nkeys).keys()].map((c) => cent.map((_, j) => j).filter((j) => centCls[j] === c));
    for (let i = 0; i < n; i++) {
      const c0 = img[3 * i], c1 = img[3 * i + 1], c2 = img[3 * i + 2];
      let list = byCls[cls[i]];
      if (!list.length) list = cent.map((_, j) => j);
      let bd = Infinity, bj = list[0];
      for (const j of list) {
        const e = (c0 - cent[j][0]) ** 2 + (c1 - cent[j][1]) ** 2 + (c2 - cent[j][2]) ** 2;
        if (e < bd) { bd = e; bj = j; }
      }
      lab[i] = bj;
    }
    // dark -> light
    const order = cent.map((_, j) => j).sort((a, b) =>
      (cent[a][0] * LUMA[0] + cent[a][1] * LUMA[1] + cent[a][2] * LUMA[2]) - (cent[b][0] * LUMA[0] + cent[b][1] * LUMA[1] + cent[b][2] * LUMA[2]));
    const rank = new Uint8Array(cent.length);
    order.forEach((j, r) => { rank[j] = r; });
    for (let i = 0; i < n; i++) lab[i] = rank[lab[i]];
    const dyeRow = order.map((j) => (centCls[j] % 4) % 3);
    const specOf = (j) => (parts && j < order.length ? parts.spec[Math.floor(centCls[order[j]] / 4)] : specular);
    // each family: mean, main axis, the 2nd and 98th percentile along it
    const lin = new Float32Array(3 * n);
    for (let i = 0; i < 3 * n; i++) lin[i] = srgbToLin(clamp01(img[i]));
    const nf = cent.length;
    const cntFit = new Float64Array(nf), cntAll = new Float64Array(nf);
    for (let i = 0; i < n; i++) { cntAll[lab[i]]++; if (fit(i)) cntFit[lab[i]]++; }
    const useFit = (j) => cntFit[j] > 0;
    const S = new Float64Array(3 * nf), SS = new Float64Array(9 * nf);
    for (let i = 0; i < n; i++) {
      const j = lab[i];
      if (useFit(j) && !fit(i)) continue;
      const a = lin[3 * i], b = lin[3 * i + 1], c = lin[3 * i + 2];
      S[3 * j] += a; S[3 * j + 1] += b; S[3 * j + 2] += c;
      SS[9 * j] += a * a; SS[9 * j + 1] += a * b; SS[9 * j + 2] += a * c; SS[9 * j + 4] += b * b; SS[9 * j + 5] += b * c; SS[9 * j + 8] += c * c;
    }
    const fams = [];
    for (let j = 0; j < nf; j++) {
      const m = useFit(j) ? cntFit[j] : cntAll[j];
      if (!m) { fams.push(null); continue; }
      const mean = [S[3 * j] / m, S[3 * j + 1] / m, S[3 * j + 2] / m];
      let axis = [1 / Math.sqrt(3), 1 / Math.sqrt(3), 1 / Math.sqrt(3)];
      if (m > 2) {
        const cv = (p, q) => (SS[9 * j + 3 * Math.min(p, q) + Math.max(p, q)] - m * mean[p] * mean[q]) / (m - 1);
        axis = topEigen([cv(0, 0), cv(0, 1), cv(0, 2), cv(1, 0), cv(1, 1), cv(1, 2), cv(2, 0), cv(2, 1), cv(2, 2)]);
      }
      if (axis[0] + axis[1] + axis[2] < 0) axis = axis.map((v) => -v);
      fams.push({ mean, axis, m });
    }
    const T = fams.map((f) => (f ? new Float64Array(f.m) : null)), tn = new Int32Array(nf);
    for (let i = 0; i < n; i++) {
      const j = lab[i], f = fams[j];
      if (useFit(j) && !fit(i)) continue;
      T[j][tn[j]++] = (lin[3 * i] - f.mean[0]) * f.axis[0] + (lin[3 * i + 1] - f.mean[1]) * f.axis[1] + (lin[3 * i + 2] - f.mean[2]) * f.axis[2];
    }
    const rows = [];
    for (let j = 0; j < PAIRS; j++) {
      const f = fams[j];
      if (!f) { rows.push(colorRow([0.5, 0.5, 0.5], specular), colorRow([0.5, 0.5, 0.5], specular)); continue; }
      const sp = specOf(j);
      let lo = quantile(T[j], 0.02), hi = quantile(T[j], 0.98);
      if (hi - lo < 1e-4) lo = hi = 0;
      f.lo = lo; f.hi = hi;
      const a = f.mean.map((v, ch) => clamp01(v + f.axis[ch] * lo)), b = f.mean.map((v, ch) => clamp01(v + f.axis[ch] * hi));
      rows.push(colorRow(a, sp), colorRow(b, sp));
    }
    const ids = new Uint8Array(4 * n);
    let err = 0;
    for (let i = 0; i < n; i++) {
      const j = lab[i], f = fams[j];
      let g = 0;
      if (f && f.hi - f.lo >= 1e-4) {
        const t = (lin[3 * i] - f.mean[0]) * f.axis[0] + (lin[3 * i + 1] - f.mean[1]) * f.axis[1] + (lin[3 * i + 2] - f.mean[2]) * f.axis[2];
        g = clamp01((t - f.lo) / (f.hi - f.lo));
      }
      ids[4 * i] = j * 17;
      ids[4 * i + 1] = JE.rintEven(f32(g) * 255);
      ids[4 * i + 3] = 255;
      if ((i & 15) === 0 && rows[2 * j]) {              // the fit's error, on a sample
        const ra = rows[2 * j], rb = rows[2 * j + 1];
        for (let ch = 0; ch < 3; ch++) {
          const rec = ra[ch] * (1 - g) + rb[ch] * g;
          err += Math.abs(Math.pow(clamp01(rec), 1 / 2.2) - Math.pow(clamp01(lin[3 * i + ch]), 1 / 2.2));
        }
      }
    }
    return { rows, ids, dye: dyeRow, err: err / (3 * Math.ceil(n / 16)), families: fams.length };
  }

  // ------------------------------------------------------ textures, materials
  const ROW_TEMPLATE = [0.014, 0.014, 0.014, 1.5, 0.023, 0.023, 0.023, 1.0, ...new Array(17).fill(0),
    0.008, 1.0, 0.0, 12.0, 0.0, 0.0, 12.0];
  /** ffxiv_write.color_row: a colour-table row (32 floats) with this diffuse (linear) and specular. */
  function colorRow(diffuse, specular = 0.023) {
    const r = ROW_TEMPLATE.slice();
    r[0] = diffuse[0]; r[1] = diffuse[1]; r[2] = diffuse[2];
    r[4] = r[5] = r[6] = specular;
    return r;
  }
  /** float -> IEEE half (round to nearest even, like numpy's astype(float16)). */
  const _f32 = new Float32Array(1), _u32 = new Uint32Array(_f32.buffer);
  function toHalf(v) {
    _f32[0] = v;
    const x = _u32[0], sign = (x >>> 16) & 0x8000;
    let exp = (x >>> 23) & 0xff, mant = x & 0x7fffff;
    if (exp === 0xff) return sign | 0x7c00 | (mant ? 0x200 : 0);
    exp = exp - 127 + 15;
    if (exp >= 31) return sign | 0x7c00;
    if (exp <= 0) {
      if (exp < -10) return sign;
      mant |= 0x800000;
      const shift = 14 - exp;
      let h = mant >>> shift;
      const rem = mant & ((1 << shift) - 1), half = 1 << (shift - 1);
      if (rem > half || (rem === half && (h & 1))) h++;
      return sign | h;
    }
    let h = (exp << 10) | (mant >>> 13);
    const rem = mant & 0x1fff;
    if (rem > 0x1000 || (rem === 0x1000 && (h & 1))) h++;
    return sign | h;
  }
  const DYE_TEMPLATE = 1210, DYE_FLAGS = 0x1;
  const dyeRow = (ch) => (ch ? (DYE_FLAGS | (DYE_TEMPLATE << 16) | ((ch - 1) << 27)) >>> 0 : 0);
  const MTRL_FLAGS = 0x053C, SHADER_FLAGS = 0x0D;
  const MTRL_TAIL = "05cf2cf560ffd2a72302ac2900000400b2bf5a570400040024bb00b508000400f1c15e0c00800f0000000000b6824e8a40830f0001000000d88f5f5640830f00020000000000003f0000803e00000000";
  /** ffxiv_write.write_mtrl: a characterlegacy.shpk material (bytes). textures: (normal, mask, id). */
  function writeMtrl(textures, rows, dye, shaderFlags = SHADER_FLAGS) {
    const enc = new TextEncoder();
    const parts = [], texOffs = [];
    let len = 0;
    const add = (str) => { const b = enc.encode(str + "\0"); parts.push(b); const o = len; len += b.length; return o; };
    for (const t of textures) texOffs.push(add(t));
    const uvOff = add("map1"), csOff = add("colorSet1"), shpkOff = add("characterlegacy.shpk");
    while (len % 4) { parts.push(new Uint8Array(1)); len++; }
    const strings = new Uint8Array(len);
    let p = 0;
    for (const b of parts) { strings.set(b, p); p += b.length; }
    const ct = new Uint8Array(2048 + 128), cv = new DataView(ct.buffer);
    for (let i = 0; i < 32; i++) {
      const r = i < rows.length ? rows[i] : ROW_TEMPLATE;
      for (let k = 0; k < 32; k++) cv.setUint16(2 * (32 * i + k), toHalf(r[k]), true);
    }
    for (let j = 0; j < 16; j++) {
      const v = dye && j < dye.length ? dyeRow(dye[j]) : 0;
      cv.setUint32(2048 + 4 * (2 * j), v, true); cv.setUint32(2048 + 4 * (2 * j + 1), v, true);
    }
    const tail = new Uint8Array(MTRL_TAIL.match(/../g).map((h) => parseInt(h, 16)));
    const headLen = 16 + 4 * textures.length + 4 + 4;
    const total = headLen + strings.length + 4 + ct.length + 8 + 4 + tail.length;
    const out = new Uint8Array(total), dv = new DataView(out.buffer);
    let o = 16;
    for (const t of texOffs) { dv.setUint16(o, t, true); dv.setUint16(o + 2, 0, true); o += 4; }
    dv.setUint16(o, uvOff, true); o += 4;
    dv.setUint16(o, csOff, true); o += 4;
    out.set(strings, o); o += strings.length;
    dv.setUint32(o, MTRL_FLAGS, true); o += 4;
    out.set(ct, o); o += ct.length;
    out.set([0x0c, 0x00, 0x01, 0x00, 0x03, 0x00, 0x03, 0x00], o); o += 8;
    dv.setUint32(o, shaderFlags, true); o += 4;
    out.set(tail, o); o += tail.length;
    dv.setUint32(0, 0x01030000, true);
    dv.setUint16(4, total, true); dv.setUint16(6, ct.length, true); dv.setUint16(8, strings.length, true);
    dv.setUint16(10, shpkOff, true);
    out[12] = textures.length; out[13] = 1; out[14] = 1; out[15] = 4;
    return out;
  }

  /**
   * An ID texture (.tex, BC7): nearest mips down to 4x4, the wrap guard on every level (the
   * top rows repeat the bottom row), as write_tex and tex_compress make them.
   */
  const UNIFORM = new Map();
  function idTex(ids, size, guard, onProgress) {
    const levels = [ids];
    let w = size;
    while (w > 4) {
      const prev = levels[levels.length - 1], w2 = w >> 1, nl = new Uint8Array(4 * w2 * w2);
      for (let y = 0; y < w2; y++) for (let x = 0; x < w2; x++) {
        const s = 4 * (2 * y * w + 2 * x), d = 4 * (y * w2 + x);
        nl[d] = prev[s]; nl[d + 1] = prev[s + 1]; nl[d + 2] = prev[s + 2]; nl[d + 3] = prev[s + 3];
      }
      levels.push(nl); w = w2;
    }
    let total = 80;
    const sizes = levels.map((_, i) => { const lw = size >> i; return lw * lw; });   // BC7: 1 byte per texel
    for (const s_ of sizes) total += s_;
    const out = new Uint8Array(total), dv = new DataView(out.buffer);
    let off = 80, done = 0;
    const blk = new Int32Array(64), allBlocks = sizes.reduce((a, b) => a + b / 16, 0);
    for (let lv = 0; lv < levels.length; lv++) {
      const lw = size >> lv, L = levels[lv];
      const g = Math.ceil(lw * guard);
      const src = (guard && g && lw > g) ? (y) => (y < g ? lw - 1 : y) : (y) => y;
      dv.setUint32(28 + 4 * lv, off, true);
      const bw = lw >> 2;
      for (let by = 0; by < bw; by++) {
        for (let bx = 0; bx < bw; bx++) {
          let same = true;
          for (let i = 0; i < 16; i++) {
            const y = src(4 * by + (i >> 2)), x = 4 * bx + (i & 3), o = 4 * (y * lw + x);
            blk[4 * i] = L[o]; blk[4 * i + 1] = L[o + 1]; blk[4 * i + 2] = L[o + 2]; blk[4 * i + 3] = L[o + 3];
            if (i && (blk[4 * i] !== blk[0] || blk[4 * i + 1] !== blk[1] || blk[4 * i + 2] !== blk[2] || blk[4 * i + 3] !== blk[3])) same = false;
          }
          const at = off + 16 * (by * bw + bx);
          if (same) {                      // one colour: the encoder's answer depends only on it
            const key = (blk[0] << 24 | blk[1] << 16 | blk[2] << 8 | blk[3]) >>> 0;
            let enc = UNIFORM.get(key);
            if (!enc) { enc = new Uint8Array(16); JE.encodeBlock(blk, "id", enc, 0); UNIFORM.set(key, enc); }
            out.set(enc, at);
          } else JE.encodeBlock(blk, "id", out, at);
        }
        done += bw;
        if (onProgress && (by & 31) === 0) onProgress(done / allBlocks);
      }
      off += lw * lw;
    }
    dv.setUint32(0, 0x00800000, true); dv.setUint32(4, 0x6432, true);
    dv.setUint16(8, size, true); dv.setUint16(10, size, true); dv.setUint16(12, 1, true);
    out[14] = levels.length; out[15] = 0;
    dv.setUint32(16, 0, true); dv.setUint32(20, 1, true); dv.setUint32(24, 2, true);
    return out;
  }

  // ---------------------------------------------------------------- the team
  /**
   * A team (what the page's form gives):
   *   name, colors: {primary, secondary, accent} (hex), camo: [4 hex] (the camo's base, dark,
   *   light, flecks), logo: "moogles" | "none" | "custom" (with customLogo),
   *   helmet: {shell, stripe, pinstripe, style, facemask, chinstrap, mouthguard},
   *   jersey: {home: {body, trim, numbers}, away: {...} | null, baseLayer},
   *   gloves: {main, palm, trim}, pants: {home: {main, stripe, piping}, away: {...} | null, leggings},
   *   feet: {socks, band, cleats, accent, detail, studs}, dirt: ["clean", "worn", "grass", "muddy"].
   * Every colour is a hex, a team colour's name ("primary", "secondary", "accent", "white",
   * "black") or "camo".
   */
  const NAMED = { white: "#F6F6F6", black: "#141416", grey: "#8A8C92", silver: "#B3B3B6" };
  function resolve(team, ref) {
    if (ref === "camo") return { camo: team.camo.map((h) => hexToRgb(h).map(srgbToLin)) };
    const hex = (team.colors && team.colors[ref]) || NAMED[ref] || ref;
    return hexToRgb(hex).map(srgbToLin);
  }
  const srgbOf = (lin) => lin.map(linToSrgb);
  /** The team's main mapping (logos and anything not set per piece). */
  const teamMap = (team) => ({ blue: resolve(team, "primary"), gold: resolve(team, "secondary"), white: resolve(team, "white") });
  /** Dye 1 and 2 match the team's primary and secondary colours (not camo, not greys). */
  function dyeColors(team) {
    const out = {};
    for (const [k, ref] of [[1, "primary"], [2, "secondary"]]) {
      const c = resolve(team, ref);
      if (c.camo) continue;
      const sc = srgbOf(c), mx = Math.max(...sc), mn = Math.min(...sc);
      if (mx > 0.06 && (mx - mn) / mx > 0.15) out[k] = sc;
    }
    return out;
  }

  /** export_penumbra.away_refs / away_kit: the away jersey from the home one (Moogles colours):
   * the blue fabric turns white, white lettering and the darker side panels turn blue. */
  function awayKit(C, img, reg, size) {
    const R = C.away_refs, blue = R.blue, white = R.white, AW = C.away_white;
    const lum = (a, b, c) => a * LUMA[0] + b * LUMA[1] + c * LUMA[2];
    const lb = Math.max(lum(...blue), 1e-4), lw = Math.max(lum(...white), 1e-4), mn = Math.max(R.main, 1e-4);
    const strip = Math.ceil(size * 0.06) + 2, out = new Float32Array(img);
    for (let i = strip * size; i < size * size; i++) {
      const code = reg[i];
      if (code !== 1 && code !== 3) continue;
      const L = lum(img[3 * i], img[3 * i + 1], img[3 * i + 2]);
      if (code === 1) {
        const rel = L / lb / mn;
        if (rel > 0.76 && rel < 0.86) for (let ch = 0; ch < 3; ch++) out[3 * i + ch] = clamp01(blue[ch] * Math.min(Math.max(rel / 0.81, 0), 1.1));
        else for (let ch = 0; ch < 3; ch++) out[3 * i + ch] = clamp01(AW[ch] * Math.min(Math.max(rel, 0), 1.05));
      } else {
        const rw = L / lw;
        for (let ch = 0; ch < 3; ch++) out[3 * i + ch] = clamp01(blue[ch] * Math.min(Math.max(rw, 0), 1.1));
      }
    }
    return out;
  }

  /** The jersey's mesh side panels (darker blue fabric, as away_kit finds them) and their usual
   * share of the team blue (to give them a colour of their own at full strength). */
  function panelMask(C, img, reg, size) {
    const R = C.away_refs, lb = Math.max(R.blue[0] * LUMA[0] + R.blue[1] * LUMA[1] + R.blue[2] * LUMA[2], 1e-4);
    const mn = Math.max(R.main, 1e-4), strip = Math.ceil(size * 0.06) + 2;
    const panel = new Uint8Array(size * size), B = C.moogles_blue.map(srgbToLin);
    const ws = [];
    for (let i = strip * size; i < size * size; i++) {
      if (reg[i] !== 1) continue;
      const L = img[3 * i] * LUMA[0] + img[3 * i + 1] * LUMA[1] + img[3 * i + 2] * LUMA[2];
      const rel = L / lb / mn;
      if (rel > 0.76 && rel < 0.86) {
        panel[i] = 1;
        if ((i & 7) === 0) ws.push(srgbToLin(img[3 * i + 2]) / B[2]);
      }
    }
    ws.sort((a, b) => a - b);
    return { panel, typical: ws.length ? ws[ws.length >> 1] : 1 };
  }

  /** Recolour an image (sRGB floats) below the swatch strip; camo from the texel positions. */
  function recolourImage(C, img, size, rec, camo, part) {
    const strip = Math.ceil(size * C.strip), out = new Float32Array(img), c = [0, 0, 0], o = [0, 0, 0];
    for (let i = strip * size; i < size * size; i++) {
      c[0] = img[3 * i]; c[1] = img[3 * i + 1]; c[2] = img[3 * i + 2];
      const r = part ? rec[part[i]] : rec;
      r(c, camo ? camo[i] : 0, o);
      out[3 * i] = o[0]; out[3 * i + 1] = o[1]; out[3 * i + 2] = o[2];
    }
    return out;
  }
  /** The swatch strip of a one-swatch piece (base layer, leggings, studs) in a new colour. */
  function setStrip(C, img, size, srgb) {
    const strip = Math.ceil(size * C.strip);
    for (let i = 0; i < strip * size; i++) { img[3 * i] = srgb[0]; img[3 * i + 1] = srgb[1]; img[3 * i + 2] = srgb[2]; }
  }
  /** Each team's logos (where its build differs from the logo-free one), pasted in at 2K. */
  function pasteLogos(D, img, size, team) {
    const boxes = (D.meta.overlays || {})[team] || [];
    boxes.forEach(([y0, y1, x0, x1], i) => {
      const rgb = D[`ov_${team}_${i}_rgb`], h = (y1 - y0) / 2, w = (x1 - x0) / 2;
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const o = (y0 / 2 + y) * size + x0 / 2 + x, s_ = y * w + x;
        for (let ch = 0; ch < 3; ch++) img[3 * o + ch] = rgb[3 * s_ + ch] / 255;
      }
    });
  }
  const BUILTIN = { moogles: true };
  /** A square logo (RGBA, top row first) as linear premultiplied mips, for sampling at a texel's size. */
  function logoMips(logo) {
    if (logo._mips) return logo._mips;
    let w = logo.w, h = logo.h;
    let cur = new Float32Array(4 * w * h);
    for (let i = 0; i < w * h; i++) {
      const a = logo.rgba[4 * i + 3] / 255;
      for (let c = 0; c < 3; c++) cur[4 * i + c] = srgbToLin(logo.rgba[4 * i + c] / 255) * a;
      cur[4 * i + 3] = a;
    }
    const mips = [{ w, h, d: cur }];
    while (w > 8 && h > 8) {
      const w2 = w >> 1, h2 = h >> 1, nx = new Float32Array(4 * w2 * h2);
      for (let y = 0; y < h2; y++) for (let x = 0; x < w2; x++) for (let c = 0; c < 4; c++) {
        const a = 4 * (2 * y * w + 2 * x) + c;
        nx[4 * (y * w2 + x) + c] = (cur[a] + cur[a + 4] + cur[a + 4 * w] + cur[a + 4 * w + 4]) / 4;
      }
      mips.push({ w: w2, h: h2, d: nx }); cur = nx; w = w2; h = h2;
    }
    Object.defineProperty(logo, "_mips", { value: mips, enumerable: false });
    return mips;
  }
  function sampleLogo(L, u, v, out) {               // bilinear, v from the bottom (as the build's decals)
    const x = Math.min(Math.max(u * L.w - 0.5, 0), L.w - 1.001), y = Math.min(Math.max((1 - v) * L.h - 0.5, 0), L.h - 1.001);
    const x0 = Math.floor(x), y0 = Math.floor(y), fx = x - x0, fy = y - y0;
    for (let c = 0; c < 4; c++) {
      const i = 4 * (y0 * L.w + x0) + c;
      out[c] = (L.d[i] * (1 - fx) + L.d[i + 4] * fx) * (1 - fy) + (L.d[i + 4 * L.w] * (1 - fx) + L.d[i + 4 * L.w + 4] * fx) * fy;
    }
    return out;
  }
  /**
   * An uploaded logo on the piece's logo spots (where its crest goes: backs and palms of the
   * gloves, the pants hip), placed as the build places its crest: each spot maps a texel's 3D
   * point to the logo's square (fitted from a build that painted a coordinate image). Painted
   * over the recoloured piece in the logo's own colours.
   */
  function paintSpots(D, img, size, pm, logo) {
    const spots = (D.meta && D.meta.spots) || [], mips = logoMips(logo), px = [0, 0, 0, 0], K = 2048;
    spots.forEach((sp, i) => {
      const cov = D[`spot_${i}_cov`], [y0, y1, x0, x1] = sp.box, bw = x1 - x0, m = sp.map;
      // the logo's level whose pixels are about one texel here
      const L = mips[Math.min(mips.length - 1, Math.max(0, Math.round(Math.log2(Math.max(1, sp.du * logo.w * K / size)))))];
      const sc = size / K;
      for (let y = Math.floor(y0 * sc); y < Math.ceil(y1 * sc); y++) for (let x = Math.floor(x0 * sc); x < Math.ceil(x1 * sc); x++) {
        const cy = Math.min(Math.floor((y + 0.5) / sc), y1 - 1) - y0, cx = Math.min(Math.floor((x + 0.5) / sc), x1 - 1) - x0;
        if (cy < 0 || cx < 0) continue;
        const k = cov[cy * bw + cx] / 255;
        if (!k) continue;
        const o = y * size + x, P0 = pm.pos[3 * o], P1 = pm.pos[3 * o + 1], P2 = pm.pos[3 * o + 2];
        const u = m[0] * P0 + m[1] * P1 + m[2] * P2 + m[3], v = m[4] * P0 + m[5] * P1 + m[6] * P2 + m[7];
        if (!(u >= 0 && u < 1 && v >= 0 && v < 1)) continue;
        sampleLogo(L, u, v, px);
        const a = px[3] * k;
        if (a <= 0) continue;
        for (let c = 0; c < 3; c++) {
          const base = srgbToLin(img[3 * o + c]);
          img[3 * o + c] = clamp01(linToSrgb(base * (1 - a) + px[c] * k));
        }
      }
    });
  }

  /** A logo image recoloured into the team's colours (sRGB bytes, RGBA). */
  function recolourLogo(C, rgba, rec) {
    const out = new Uint8Array(rgba), c = [0, 0, 0], o = [0, 0, 0];
    for (let i = 0; i < rgba.length / 4; i++) {
      if (!rgba[4 * i + 3]) continue;
      c[0] = rgba[4 * i] / 255; c[1] = rgba[4 * i + 1] / 255; c[2] = rgba[4 * i + 2] / 255;
      rec(c, 0, o);
      for (let ch = 0; ch < 3; ch++) out[4 * i + ch] = Math.round(clamp01(o[ch]) * 255);
    }
    return out;
  }

  /**
   * A piece's looks before dirt: [{kit, label, img}] (sRGB floats at the IDs' size), plus the
   * island mask and position map. needs: {pm: () => position map}.
   */
  function slotKits(C, slot, D, team, ctx) {
    const size = C.id_size, n = size * size, tm = makeRecolour(C, teamMap(team));
    const base = () => { const a = new Float32Array(3 * n); for (let i = 0; i < 3 * n; i++) a[i] = D.base[i] / 255; return a; };
    const camoNeed = (map) => Object.values(map).some((v) => v && v.camo);
    const camo = (map) => (camoNeed(map) ? ctx.camo() : null);
    const kits = [];
    if (slot === "head") {
      const h = team.helmet, H = C.helmet;
      const solid = (ref) => { const c = resolve(team, ref); return c.camo ? c.camo[0] : c; };
      let logo = null;
      if (team.logo === "custom") {
        if (team.customLogo) logo = { rgba: team.customLogo.rgba, w: team.customLogo.w, h: team.customLogo.h };
      } else if (team.logo !== "none") {
        const key = `logo_${team.logo}`, [lh, lw] = D[key + "_shape"];
        logo = { rgba: recolourLogo(C, D[key], tm), w: lw, h: lh };
      }
      const sw = C.swatches.head.map((s_) => s_.rgb.map((v) => v / 255));
      const names = C.swatches.head_names;
      const set = (name, ref) => { const i = names.indexOf(name); if (i >= 0 && ref) sw[i] = srgbOf(solid(ref)); };
      set("GRID_Gold", h.facemask); set("GRID_Rubber", h.chinstrap); set("GRID_Mouthguard", h.mouthguard);
      const img = paintHelmet(C, D, { shell: solid(h.shell), a: solid(h.stripe), b: solid(h.pinstripe), style: h.style, logo, swatches: sw });
      kits.push({ kit: "", label: "", img });
    } else if (slot === "body") {
      const j = team.jersey;
      let canvas = ctx.jerseyCanvas ? ctx.jerseyCanvas() : base(), reg = D.reg;
      const rs = restripe(C, D, canvas, size, "body", j.sleeves);
      if (rs) ({ img: canvas, reg } = rs);
      // the mesh side panels: the darker blue of the fabric (export_penumbra.away_kit's test)
      const { panel, typical } = panelMask(C, canvas, reg, size);
      for (const [kit, cols] of [["home", j.home], ["away", j.away]]) {
        if (!cols) continue;
        // blue fabric, gold trim, white lettering and stripes, each in the kit's colour; the
        // side panels are the fabric's darker shade unless the kit gives them their own colour
        const map = { blue: resolve(team, cols.body), gold: resolve(team, cols.trim), white: resolve(team, cols.numbers) };
        const pref = cols.panels || (kit === "away" ? cols.numbers : cols.body);
        let pmap = map;
        if (pref !== cols.body) {
          const pc = resolve(team, pref);
          pmap = Object.assign({}, map, { blue: pc.camo ? pc : pc.map((v) => v / typical) });
        }
        const img = recolourImage(C, canvas, size, [makeRecolour(C, map), makeRecolour(C, pmap)],
          camoNeed(map) || camoNeed(pmap) ? ctx.camo() : null, panel);
        setStrip(C, img, size, srgbOf(solid1(resolve(team, j.baseLayer || "white"))));
        kits.push({ kit, label: kit === "home" ? "Home" : "Away", img });
      }
    } else if (slot === "hands") {
      const g = team.gloves, img0 = base();
      if (BUILTIN[team.logo] && !ctx.skipLogos) pasteLogos(D, img0, size, team.logo);
      const map = { blue: resolve(team, g.main), gold: resolve(team, g.palm), white: resolve(team, g.trim) };
      const img = recolourImage(C, img0, size, makeRecolour(C, map), camo(map));
      if (team.logo === "custom" && team.customLogo) paintSpots(D, img, size, ctx.pm(), team.customLogo);
      kits.push({ kit: "", label: "", img });
    } else if (slot === "legs") {
      const p = team.pants, rs = restripe(C, D, base(), size, "legs", p.style), img0 = rs ? rs.img : base();
      if (BUILTIN[team.logo] && !ctx.skipLogos) pasteLogos(D, img0, size, team.logo);
      for (const [kit, cols] of [["home", p.home], ["away", p.away]]) {
        if (!cols) continue;
        const map = { gold: resolve(team, cols.main), blue: resolve(team, cols.stripe), white: resolve(team, cols.piping) };
        const img = recolourImage(C, img0, size, makeRecolour(C, map), camo(map));
        if (team.logo === "custom" && team.customLogo) paintSpots(D, img, size, ctx.pm(), team.customLogo);
        setStrip(C, img, size, srgbOf(solid1(resolve(team, p.leggings || "white"))));
        kits.push({ kit, label: kit === "home" ? "Home" : "Away", img });
      }
    } else if (slot === "feet") {
      const f = team.feet, rs = restripe(C, D, base(), size, "feet", f.stripes), img0 = rs ? rs.img : base();
      // socks above the cleat collar, cleats below (by height on the body)
      const pm = ctx.pm(), part = new Uint8Array(n);
      for (let i = 0; i < n; i++) part[i] = pm.pos[3 * i + 2] > 0.13 ? 1 : 0;
      const cleat = { blue: resolve(team, f.cleats), gold: resolve(team, f.accent), white: resolve(team, f.detail) };
      const sock = { white: resolve(team, f.socks), gold: resolve(team, f.band), blue: resolve(team, f.band) };
      const img = recolourImage(C, img0, size, [makeRecolour(C, cleat), makeRecolour(C, sock)],
        camoNeed(cleat) || camoNeed(sock) ? ctx.camo() : null, part);
      setStrip(C, img, size, srgbOf(solid1(resolve(team, f.studs || "#303035"))));
      kits.push({ kit: "", label: "", img });
    }
    return kits;
  }
  const solid1 = (c) => (c.camo ? c.camo[0] : c);

  /** Helmet finishes: the colour table's specular (shine) per part. */
  const FINISH = { matte: 0.03, satin: 0.1, gloss: null, high: 0.4, chrome: 0.85 };
  let _hp = null;
  function helmetParts(C, size, team, base) {
    const h = team.helmet || {}, shell = FINISH[h.finish] ?? base, mask = FINISH[h.maskFinish] ?? base;
    if (shell === base && mask === base) return null;                  // the release's look: one shine
    if (!_hp || _hp.size !== size) {
      const of = new Uint8Array(size * size), strip = Math.ceil(size * C.strip), sw = C.swatches.head, n = sw.length;
      const fm = C.swatches.head_names.indexOf("GRID_Gold");
      for (let y = 0; y < strip; y++) for (let x = 0; x < size; x++) of[y * size + x] = Math.floor(x * n / size) === fm ? 2 : 1;
      _hp = { size, of };
    }
    return { of: _hp.of, spec: [shell, base, mask] };
  }

  /**
   * One piece's add-on files: per kit and dirt, the colour IDs and the material.
   * Returns {options: [{label, files: {gamePath: localPath}}], files: {localPath: bytes}}.
   */
  function makeSlot(C, slot, S, D, team, ctx, progress) {
    const size = C.id_size, n = size * size, tag = ctx.tag;
    const kits = slotKits(C, slot, D, team, ctx);
    const isl = slot === "head" ? null : D.isl;
    const dyes = team.dyes === false ? {} : dyeColors(team);
    const dirt = team.dirt && team.dirt.length ? team.dirt : ["clean"];
    const masks = dirt.some((v) => v !== "clean") ? ctx.masks() : null;
    const options = [], files = {};
    const normal = ctx.normal ? ctx.normal() : null;      // {game, bytes} when the piece needs its own
    if (normal) files[normal.game] = normal.bytes;
    const steps = kits.length * dirt.length;
    let step = 0;
    for (const k of kits) {
      // the background between islands filled again from the recoloured islands
      let clean = k.img;
      if (isl) clean = fillBackground(clean, isl, size, size);
      const cleanCls = Object.keys(dyes).length ? dyeClasses(clean, dyes, C.dye_match) : null;
      for (const v of dirt) {
        progress(step / steps, `${S.label}: ${[k.label, v === "clean" ? "clean" : C.dirt_labels[v]].filter(Boolean).join(", ")}`);
        const img = applyDirt(C, slot, clean, masks, v);
        const cls = cleanCls ? (v === "clean" ? cleanCls : dirtyClasses(C, cleanCls, clean, img, dyes)) : null;
        const fit = colorTableAndId(C, img, size, S.specular, cls, isl, 1 + step, slot === "head" ? helmetParts(C, size, team, S.specular) : null);
        const key = [ctx.player != null ? `p${ctx.player}` : "", k.kit, v].filter(Boolean).join("_");
        const idGame = `${S.tex_base.replace("gridiron_", `gridiron_team_${tag}_`)}_id_${key}.tex`;
        files[idGame] = idTex(fit.ids, size, C.wrap_guard);
        const mtrl = `team/${slot}_${key}.mtrl`;
        files[mtrl] = writeMtrl([normal ? normal.game : S.normal_game, S.mask_game, idGame], fit.rows, fit.dye);
        const fl = { [S.material]: mtrl, [idGame]: idGame };
        if (normal) fl[normal.game] = normal.game;
        const label = [k.label, v === "clean" ? (k.label ? "" : "Clean") : (k.label ? C.dirt_labels[v] : C.dirt_labels[v][0].toUpperCase() + C.dirt_labels[v].slice(1))]
          .filter(Boolean).join(", ");
        options.push({ label: ctx.playerLabel ? `${ctx.playerLabel} · ${label}` : label, files: fl, err: fit.err });
        step++;
      }
    }
    progress(1, `${S.label}: done`);
    return { options, files };
  }

  /** The add-on (Penumbra mod layout): meta, a Single group per piece, the files. */
  function buildAddon(T, team, slots, made) {
    const enc = new TextEncoder(), z = {};
    const title = `Aetherial Gridiron Team: ${team.name || "My Team"}`;
    z["meta.json"] = enc.encode(JSON.stringify({
      FileVersion: 3, Name: title, Author: "Aetherial Gridiron Team Builder", Version: "1.0",
      Description: `${team.name || "Your team"}: team colours on Aetherial Gridiron. Needs Aetherial Gridiron ${T.mod_version || ""} enabled; give this add-on a higher priority. Pick each piece's kit and dirt in this mod's groups.`,
      Website: "", ModTags: ["Gridiron"],
    }, null, 2));
    z["default_mod.json"] = enc.encode(JSON.stringify({ Version: 0, Files: {}, FileSwaps: {}, Manipulations: [] }, null, 2));
    let gi = 1;
    for (const slot of slots) {
      const m = made[slot];
      if (!m) continue;
      const group = {
        Version: 0, Name: T.slots[slot].label.split(",")[0], Description: "Kit and dirt.", Image: "", Page: 0,
        Priority: 0, Type: "Single", DefaultSettings: 0,
        Options: m.options.map((o) => ({
          Name: o.label, Description: "", Priority: 0, FileSwaps: {}, Manipulations: [],
          Files: Object.fromEntries(Object.entries(o.files).map(([g, l]) => [g, l.replace(/\//g, "\\")])),
        })),
      };
      z[`group_${String(gi++).padStart(3, "0")}_${slot}.json`] = enc.encode(JSON.stringify(group, null, 2));
      for (const [path, data] of Object.entries(m.files)) z[path] = data;
    }
    const entries = {};
    for (const [k, v] of Object.entries(z)) entries[k] = [v, { level: k.endsWith(".tex") ? 1 : 6 }];
    return { title, zip: fflate.zipSync(entries) };
  }
  const slug = (s) => (s || "team").replace(/[^A-Za-z0-9]+/g, "_").replace(/^_|_$/g, "").toLowerCase() || "team";

  // ------------------------------------------------------- jersey lettering
  /** An RGBA byte image (rows bottom-up) as Blender's load_rgba gives it: RGB linear, alpha. */
  function imageFloat(rgba, w, h, lut) {
    const d = new Float32Array(4 * w * h);
    for (let i = 0; i < w * h; i++) {
      d[4 * i] = lut.rgb[rgba[4 * i]]; d[4 * i + 1] = lut.rgb[rgba[4 * i + 1]]; d[4 * i + 2] = lut.rgb[rgba[4 * i + 2]];
      d[4 * i + 3] = lut.a[rgba[4 * i + 3]];
    }
    return { h, w, d };
  }
  const jdecal = (img, center, h, right, up, facing, o) => Object.assign({ img, center, h, w: h * img.w / img.h, right, up, facing,
    raise: 0, region: null, extra: null, extraW: 0.6 }, o);

  /**
   * build_jersey.make_layout for a team: the wordmark across the chest (shrunk to fit), the
   * crest at the bottom of the V, the nameplate under the back collar, the numbers front and
   * back (the same size, the front one under the wordmark) and on the sleeves.
   * o: {name, number, wordmark, crest: image (imageFloat) or null}
   */
  function jerseyLayout(JM, G, lut, o) {
    const L = JM.layout, bottom = L.tuck + 0.022, up = [0, 0, 1], decals = [];
    const W = JM.wordmark, word = (o.wordmark || "").toUpperCase().replace(/[^A-Z '.\-]/g, "").trim();
    let frontTop = L.v_tip - 0.03;
    if (word) {
      const img = JE.composeText(G, lut, word, "letters", 0.07);
      if (img) {
        const t = JE.twill(img);
        let wh = W.height;
        const ww = wh * t.img.w / t.img.h;
        const maxW = 0.80 * JE.widthAt(JM, L.v_tip - 0.03 - wh / 2, true);
        if (ww > maxW) wh *= maxW / ww;
        const zc = L.v_tip - W.drop - wh / 2;
        decals.push(jdecal(t.img, [L.cx, 0, zc], wh, [1, 0, 0], up, [0, -1, 0],
          { kind: "wordmark", extra: { h: t.img.h, w: t.img.w, d: t.height }, extraW: 1.0 }));
        frontTop = zc - wh / 2 - W.gap;
      }
    }
    const digits = (o.number || "").replace(/[^0-9]/g, "").slice(0, 2);
    let num = null;
    if (digits) { const t = JE.twill(JE.composeText(G, lut, digits, "digits", 0.02)); num = { img: t.img, height: t.height }; }
    const fit = (img, top, bot, maxW) => {
      const h = Math.min((top - bot) * 0.94, maxW / (img.w / img.h));
      return [h, top - h / 2 - (top - bot - h) * 0.3];
    };
    let frontFit = null;
    if (num) frontFit = fit(num.img, frontTop, bottom, 0.82 * JE.widthAt(JM, (frontTop + bottom) / 2, true));
    let plateBottom = L.back_neck - 0.03;
    const name = (o.name || "").toUpperCase().replace(/[^A-Z '.\-]/g, "").trim().slice(0, JM.max_name);
    const plate = name ? JE.makeNameplate(G, lut, name, JM.colors.blue) : null;
    if (plate) {
      let ph = 0.044;
      const maxW = 0.62 * JE.widthAt(JM, L.back_neck - 0.06, false);
      if (ph * plate.img.w / plate.img.h > maxW) ph *= maxW / (ph * plate.img.w / plate.img.h);
      const zc = L.back_neck - 0.032 - ph / 2;
      decals.push(jdecal(plate.img, [L.cx, 0, zc], ph, [-1, 0, 0], up, [0, 1, 0],
        { kind: "plate", raise: 0.45, region: "blue", extra: { h: plate.img.h, w: plate.img.w, d: plate.lift }, extraW: 0.6 }));
      plateBottom = zc - ph / 2;
      const li = new Float32Array(plate.img.d);
      for (let i = 0; i < plate.img.h * plate.img.w; i++) li[4 * i + 3] = plate.letters[i];
      decals.push(jdecal({ h: plate.img.h, w: plate.img.w, d: li }, [L.cx, 0, zc], ph, [-1, 0, 0], up, [0, 1, 0], { kind: "plate_letters" }));
    }
    if (num) {
      const topB = plateBottom - 0.02;
      const backFit = fit(num.img, topB, bottom, 0.82 * JE.widthAt(JM, (topB + bottom) / 2, false));
      const h = Math.min(frontFit[0], backFit[0]);
      for (const [kind, right, facing, t_] of [["front", [1, 0, 0], [0, -1, 0], frontTop], ["back", [-1, 0, 0], [0, 1, 0], topB]]) {
        const zc = t_ - h / 2 - (t_ - bottom - h) * 0.3;
        decals.push(jdecal(num.img, [L.cx, 0, zc], h, right, up, facing, { kind, extra: { h: num.img.h, w: num.img.w, d: num.height }, extraW: 1.0 }));
      }
      for (const side of ["sleeve_l", "sleeve_r"]) {
        const sl = L.sleeves[side];
        if (sl) decals.push(jdecal(num.img, sl.center, sl.h, sl.right, sl.up, sl.facing, { kind: side, extra: { h: num.img.h, w: num.img.w, d: num.height }, extraW: 1.0 }));
      }
    }
    if (o.crest) {
      const Cr = JM.crest;
      let h = Cr.h;
      if (o.crest.w / o.crest.h > Cr.max_aspect) h *= Cr.max_aspect / (o.crest.w / o.crest.h);
      decals.push(jdecal(o.crest, [L.cx, 0, L.v_tip - Cr.drop], h, [1, 0, 0], up, [0, -1, 0], { kind: "crest", raise: Cr.raise, region: "white" }));
    }
    return decals;
  }

  const JREG = { none: 0, blue: 1, gold: 2, white: 3 };
  const JFLAG = { front: 4, back: 8, sleeve_l: 16, sleeve_r: 32, lock: 128 };
  const JBIT = { front: JFLAG.front, wordmark: JFLAG.front, back: JFLAG.back, plate: JFLAG.back, plate_letters: JFLAG.back,
    sleeve_l: JFLAG.sleeve_l, sleeve_r: JFLAG.sleeve_r };
  /** jersey maker's paintWindow, with the crest (its own, stricter facing test: flags2). */
  function paintJerseyWindow(W, decals) {
    const A = W.arrays, [hs, ws] = A.flags.shape, n = hs * ws;
    const flags = A.flags.data, flags2 = A.flags2.data, P = A.P.data, lin = A.lin.data;
    const col = new Float32Array(3 * n);
    for (let c = 0; c < 3; c++) for (let i = 0; i < n; i++) col[3 * i + c] = f32(lin[c * n + i]);
    const reg = Uint8Array.from(A.reg.data), H = new Float32Array(n), changed = new Uint8Array(n);
    for (let i = 0; i < n; i++) H[i] = f32(A.H.data[i]);
    const px = new Float64Array(4), ex = new Float64Array(1);
    for (const d of decals) {
      const bit = JBIT[d.kind], crest = d.kind === "crest", regFixed = d.region ? JREG[d.region] : 0;
      for (let i = 0; i < n; i++) {
        const fl = flags[i];
        if (crest ? !flags2[i] : !(fl & bit)) continue;
        const rx = P[i] - d.center[0], ry = P[n + i] - d.center[1], rz = P[2 * n + i] - d.center[2];
        const u = (rx * d.right[0] + ry * d.right[1] + rz * d.right[2]) / d.w + 0.5;
        const v = (rx * d.up[0] + ry * d.up[1] + rz * d.up[2]) / d.h + 0.5;
        if (!(u >= 0 && u < 1 && v >= 0 && v < 1)) continue;
        JE.sample(d.img, 4, u, v, px);
        const a = Math.min(Math.max(px[3], 0), 1);
        let hh = a * d.raise;
        if (d.extra) hh += JE.sample(d.extra, 1, u, v, ex)[0] * d.extraW;
        if (!(fl & JFLAG.lock)) {
          for (let c = 0; c < 3; c++) col[3 * i + c] = f32(col[3 * i + c] * (1 - a) + px[c] * a);
          if (a > 0.5) reg[i] = regFixed || (Math.min(px[0], px[1], px[2]) > 0.55 ? JREG.white : JREG.gold);
          if (a > 0) changed[i] |= 1;
        }
        if (hh > 1e-4) {
          const m = f32(Math.max(H[i], hh));
          if (m !== H[i]) { H[i] = m; changed[i] |= 2; }
        }
      }
    }
    const bleed = A.bleed.data;
    for (let i = 0; i < n; i++) {
      const s_ = bleed[i];
      if (s_ >= 0 && changed[s_]) {
        col[3 * i] = col[3 * s_]; col[3 * i + 1] = col[3 * s_ + 1]; col[3 * i + 2] = col[3 * s_ + 2];
        reg[i] = reg[s_]; H[i] = H[s_]; changed[i] = changed[s_];
      }
    }
    return { hs, ws, col, reg, H, changed };
  }

  /**
   * The jersey's lettering: every window painted and taken through the export (squeeze into
   * the atlas, fill, 2K), merged into the bare jersey (sRGB 2K and regions) plus the normal
   * map's changed texels. o: {name, number, wordmark, crest (team logo key or null)}.
   */
  async function jerseyLettering(JM, get, C, D, o, rec, progress, preview = false) {
    const lut = { rgb: Float32Array.from(JM.lut.rgb), a: Float32Array.from(JM.lut.a) };
    const G = o.glyphs || JE.unpack(await get("jersey/glyphs.bin"));     // another typeface: drawn by the page
    let crest = null;
    if (o.crest === "custom" && o.customLogo) {
      const L = o.customLogo, flip = new Uint8Array(L.rgba.length);
      for (let y = 0; y < L.h; y++) flip.set(L.rgba.subarray(4 * (L.h - 1 - y) * L.w, 4 * (L.h - y) * L.w), 4 * y * L.w);
      crest = imageFloat(flip, L.w, L.h, lut);
    } else if (o.crest) {
      const CR = JE.unpack(await get("jersey/crests.bin")), c = CR.arrays[o.crest];
      if (c) crest = imageFloat(recolourLogo(C, c.data, rec), c.shape[1], c.shape[0], lut);
    }
    const decals = jerseyLayout(JM, G, lut, Object.assign({}, o, { crest }));
    const size = C.id_size, n = size * size;
    const canvas = new Float32Array(3 * n), reg = new Uint8Array(D.reg);
    for (let i = 0; i < 3 * n; i++) canvas[i] = D.base[i] / 255;
    const idx = [], val = [];
    for (let wi = 0; wi < JM.windows.length; wi++) {
      progress && progress(wi / JM.windows.length, "Jersey: lettering");
      const W = JE.unpack(await get(JM.windows[wi].file));
      const X = JE.exportWindow(JM, W, paintJerseyWindow(W, decals), { noNormals: preview });
      const [R0, , C0] = W.meta.k2;
      for (let R = 0; R < X.kh; R++) for (let Cc = 0; Cc < X.kw; Cc++) {
        const k = R * X.kw + Cc;
        if (!X.kOut[k] || !X.kOk[k]) continue;
        const t = (R0 + R) * size + C0 + Cc;
        canvas[3 * t] = X.kCol[3 * k]; canvas[3 * t + 1] = X.kCol[3 * k + 1]; canvas[3 * t + 2] = X.kCol[3 * k + 2];
        const r = X.kReg[3 * k] > 0.5, g = X.kReg[3 * k + 1] > 0.5, b = X.kReg[3 * k + 2] > 0.5;
        reg[t] = r && !g && !b ? 1 : g && !r && !b ? 2 : b && !r && !g ? 3 : 0;
      }
      if (!preview) for (let r = 0; r < X.ah; r++) for (let x = 0; x < X.aw; x++) {
        const a = r * X.aw + x;
        if (X.aOut[a] && X.aNrmOk[a]) { idx.push((X.r0 + r) * JM.size + X.c0 + x); val.push(X.aNrm[2 * a], X.aNrm[2 * a + 1], 255, 255); }
      }
    }
    return { canvas, reg, normal: { idx: Int32Array.from(idx), val: Uint8Array.from(val) } };
  }

  // ------------------------------------------------------------- all of it
  const SLOTS = ["head", "body", "hands", "legs", "feet"];
  /**
   * Make a team's add-on. T: team.json; get(path) -> Promise<Uint8Array> (a baked file);
   * team: see slotKits; progress(fraction, message). Returns {title, zip, filename}.
   */
  async function generate(T, get, team, progress = () => {}, opts = {}) {
    const C = T.consts, size = C.id_size, tag = slug(team.name);
    const slots = opts.slots || SLOTS, made = {};
    for (let si = 0; si < slots.length; si++) {
      const slot = slots[si], S = T.slots[slot];
      const sp = (f, msg) => progress((si + f) / slots.length, msg);
      sp(0, `${S.label}: loading`);
      const D = slotData(await get(`${slot}.bin`));
      let letters = null;
      if (slot === "body" && T.jersey) {
        const j = team.jersey || {};
        const pl = opts.player != null && team.roster ? team.roster[opts.player] : j;
        letters = await jerseyLettering(T.jersey, get, C, D,
          { name: pl.name, number: pl.number, wordmark: j.wordmark, crest: j.crest !== false && team.logo !== "none" ? team.logo : null,
            customLogo: team.customLogo, glyphs: opts.glyphs || null },
          makeRecolour(C, teamMap(team)), (f, m) => sp(0.02 * f, m));
        D.reg = letters.reg;
      }
      const normal = await slotNormal(T, slot, D, team, get, tag, Object.assign({}, opts,
        letters ? { jerseyNormal: (base) => JE.patchTex(base, letters.normal, "normal", C.wrap_guard) } : {}));
      const cache = {};
      const player = slot === "body" && opts.player != null && team.roster ? opts.player : null;
      const ctx = {
        tag, player, playerLabel: player != null ? `${team.roster[player].name || ""} ${team.roster[player].number || ""}`.trim() : "",
        pm: () => cache.pm || (cache.pm = positionMap(D, size)),
        masks: () => {
          if (!cache.masks) {
            sp(0.02, `${S.label}: dirt`);
            const d = team.dirt || [];
            cache.masks = dirtMasks(C, slot, ctx.pm(), null, { grass: d.includes("grass"), muddy: d.includes("muddy") });
          }
          return cache.masks;
        },
        camo: () => cache.camo || (cache.camo = camoMap(ctx.pm(), C.camo_scale, C.camo_seed)),
        normal: normal ? () => normal : null,
        jerseyCanvas: letters ? () => letters.canvas : null,
      };
      made[slot] = makeSlot(C, slot, S, D, team, ctx, sp);
      await new Promise((r) => setTimeout(r, 0));
    }
    progress(0.99, "Packing the add-on");
    const out = buildAddon(T, team, slots, made);
    progress(1, "Done");
    return Object.assign(out, { filename: `Aetherial Gridiron Team - ${(team.name || "My Team").replace(/[^A-Za-z0-9 '.-]+/g, "").trim() || "My Team"}.zip`, made });
  }

  /** A piece's own normal map, when its raised logos (or lettering) differ from the release's. */
  async function slotNormal(T, slot, D, team, get, tag, opts) {
    const S = T.slots[slot], C = T.consts;
    const game = `${S.tex_base.replace("gridiron_", `gridiron_team_${tag}_`)}_n${slot === "body" && opts.player != null ? `_p${opts.player}` : ""}.tex`;
    if (slot === "body") {
      const base = fflate.inflateSync(await get("n_blank_body.bin"));
      return { game, bytes: opts.jerseyNormal ? opts.jerseyNormal(base) : base };
    }
    if (slot === "head" && team.helmet && team.helmet.style && team.helmet.style !== "classic") {
      const logo = team.logo === "custom" ? team.customLogo
        : BUILTIN[team.logo] ? { rgba: D[`logo_${team.logo}`], w: D[`logo_${team.logo}_shape`][1], h: D[`logo_${team.logo}_shape`][0] } : null;
      const bytes = helmetNormal(C, D, fflate.inflateSync(await get("n_head.bin")), team.helmet.style, logo);
      return bytes ? { game, bytes } : null;
    }
    if ((slot === "hands" || slot === "legs") && team.logo !== "moogles") {
      const base = fflate.inflateSync(await get(`n_blank_${slot}.bin`));
      if (!BUILTIN[team.logo]) return { game, bytes: base };
      const boxes = (D.meta.overlays || {})[team.logo] || [], W = T.consts.helmet.size;
      const idx = [], val = [];
      boxes.forEach(([y0, y1, x0, x1], i) => {
        const nrm = D[`ov_${team.logo}_${i}_n`], w = x1 - x0;
        for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) {
          const s_ = 2 * ((y - y0) * w + (x - x0));
          idx.push(y * W + x); val.push(nrm[s_], nrm[s_ + 1], 255, 255);
        }
      });
      return { game, bytes: JE.patchTex(base, { idx: Int32Array.from(idx), val: Uint8Array.from(val) }, "normal", C.wrap_guard) };
    }
    return null;
  }

  return {
    f32, toByte, BYTE, LIN, srgbToLin, linToSrgb, hexToRgb, rng, slotData, positionMap, lowerEdge, STRIPES,
    PANTS_STRIPES, SLEEVE_STRIPES, SOCK_STRIPES, restripe,
    paintHelmet, makeRecolour, fillBackground, noise3, fbm, dirtMasks, applyDirt, camoMap, LUMA,
    dyeClasses, dirtyClasses, kmeans, allocKmeans, topEigen, quantile, colorTableAndId, colorRow, toHalf,
    writeMtrl, idTex, ROW_TEMPLATE, resolve, teamMap, dyeColors, awayKit, panelMask, recolourImage, setStrip, pasteLogos,
    recolourLogo, slotKits, makeSlot, buildAddon, slug, generate, slotNormal, SLOTS, paintSpots, logoMips,
    imageFloat, jerseyLayout, paintJerseyWindow, jerseyLettering, helmetKeys, helmetNormalAtlas, helmetNormal,
  };
});
