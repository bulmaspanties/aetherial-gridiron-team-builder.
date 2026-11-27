/*
 * Gridiron Team Builder worker. Two jobs, one per worker instance:
 *  - preview: holds every piece at 1K and recolours it for the 3D view as the form changes;
 *  - make: builds one piece's add-on files (team.js generate, full size).
 * Messages in:  {type: "init"}, {type: "preview", seq, team}, {type: "letters", seq, team},
 *               {type: "make", slot, team}
 * Messages out: ready (geometry), textures, status, progress, made, error.
 * The baked data sits next to this file as base64 text (name.txt): artifacts serve text.
 */
importScripts("fflate.js", "engine.js", "team.js");
const TE = self.TeamEngine, JE = self.JerseyEngine;
const PREVIEW = 1024;
let T = null;
const raw = new Map();

function fromBase64(text) {
  const bin = atob(text.replace(/\s+/g, ""));
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}
async function get(path) {
  if (raw.has(path)) return raw.get(path);
  const r = await fetch(path + ".txt");
  if (!r.ok) throw new Error(`Couldn't load ${path} (${r.status}). Reload the page to try again.`);
  const b = fromBase64(await r.text());
  // keep the small and the often-used; the big normal maps are read once per make
  if (!path.startsWith("n_blank")) raw.set(path, b);
  return b;
}
async function loadT() {
  if (T) return T;
  T = await (await fetch("team.json")).json();
  T.jersey = await (await fetch("jersey/jersey.json")).json();
  return T;
}

// ------------------------------------------------------------------ preview
const P = {};                 // slot -> {D (1K stand-in), full (2K data), pm, camo}
let C1 = null;
let lettered = null;          // the jersey's 2K canvas and regions with the current lettering
let letterKey = "";
const fonts = {};             // typeface key -> glyphs (drawn by the page)

function down2(src, size, nch) {             // 2x2 mean (floats) of a size x size image
  const h = size >> 1, out = new Float32Array(nch * h * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < h; x++) {
    const a = (2 * y * size + 2 * x) * nch, b = a + nch, c = a + size * nch, d = c + nch, o = (y * h + x) * nch;
    for (let k = 0; k < nch; k++) out[o + k] = (src[a + k] + src[b + k] + src[c + k] + src[d + k]) / 4;
  }
  return out;
}
function nearest2(src, size) {
  const h = size >> 1, out = new Uint8Array(h * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < h; x++) out[y * h + x] = src[(2 * y + 1) * size + 2 * x + 1];
  return out;
}
function nearest2n(src, size, nch) {         // nearest 2x2 pick of a size x size image with nch channels
  const h = size >> 1, out = new Uint8Array(nch * h * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < h; x++)
    for (let k = 0; k < nch; k++) out[(y * h + x) * nch + k] = src[((2 * y + 1) * size + 2 * x + 1) * nch + k];
  return out;
}
function bytesOf(f) { const o = new Uint8Array(f.length); for (let i = 0; i < f.length; i++) o[i] = Math.round(Math.min(Math.max(f[i], 0), 1) * 255); return o; }

/** The Moogles-coloured canvas of a piece at 1K, with the team's logos (and the jersey's lettering). */
function previewBase(slot, team) {
  const S = P[slot], full = S.full, C = T.consts, size = C.id_size;
  if (slot === "head") return;
  let img;
  if (slot === "body" && lettered) img = lettered.canvas;
  else {
    img = new Float32Array(3 * size * size);
    for (let i = 0; i < img.length; i++) img[i] = full.base[i] / 255;
    if (team.logo === "moogles" && slot !== "body") TE.pasteLogos(full, img, size, team.logo);
  }
  S.D.base = bytesOf(down2(img, size, 3));
  S.D.reg = nearest2(slot === "body" && lettered ? lettered.reg : full.reg, size);
  S.logo = team.logo;
}

async function init() {
  await loadT();
  const C = T.consts;
  C1 = Object.assign({}, C, { id_size: PREVIEW, helmet: Object.assign({}, C.helmet, { size: PREVIEW }),
    rows_main: Math.round(PREVIEW * (1 - C.strip)) });
  const geometry = {}, transfer = [];
  for (const slot of TE.SLOTS) {
    postMessage({ type: "status", text: `Loading ${T.slots[slot].label.split(",")[0].toLowerCase()}` });
    const full = TE.slotData(await get(`${slot}.bin`));
    const D = { meta: { overlays: {}, spots: full.meta.spots || [], locks: full.meta.locks || [] } };
    if (full.stripe) {                        // the stripe map at 1K, for the stripe styles
      const nch = full.stripe_shape[2];
      D.stripe = nearest2n(full.stripe, C.id_size, nch); D.stripe_shape = [PREVIEW, PREVIEW, nch];
    }
    (full.meta.spots || []).forEach((_, i) => { D[`spot_${i}_cov`] = full[`spot_${i}_cov`]; });
    if (slot === "head") {
      D.wear = new Uint16Array(PREVIEW * PREVIEW);
      D.logo_moogles = full.logo_moogles; D.logo_moogles_shape = full.logo_moogles_shape;
    }
    P[slot] = { D, full, pm: null, camo: null, logo: null };
    const g = { pos: full.gpos.slice(), nrm: full.gnrm.slice(), uv: full.guv.slice(), idx: full.tri.slice() };
    geometry[slot] = g;
    transfer.push(g.pos.buffer, g.nrm.buffer, g.uv.buffer, g.idx.buffer);
  }
  postMessage({ type: "ready", geometry, version: T.mod_version, stripes: C.stripes || null, slots: Object.fromEntries(TE.SLOTS.map((s) => [s, T.slots[s].label])) }, transfer);
}

function preview(team, seq) {
  const out = { type: "textures", seq, slots: {} }, transfer = [];
  for (const slot of TE.SLOTS) {
    const S = P[slot];
    if (slot !== "head" && (S.logo !== team.logo || (slot === "body" && S.letters !== letterKey))) {
      previewBase(slot, team);
      S.letters = letterKey;
    }
    const ctx = {
      tag: "preview", skipLogos: true,
      pm: () => S.pm || (S.pm = TE.positionMap(S.full, PREVIEW)),
      camo: () => S.camo || (S.camo = TE.camoMap(ctx.pm(), T.consts.camo_scale, T.consts.camo_seed)),
      jerseyCanvas: slot === "body" ? () => { const a = new Float32Array(S.D.base.length); for (let i = 0; i < a.length; i++) a[i] = S.D.base[i] / 255; return a; } : null,
    };
    const kits = TE.slotKits(C1, slot, S.D, team, ctx);
    out.slots[slot] = {};
    const dirt = team.previewDirt && team.previewDirt !== "clean" ? team.previewDirt : null;
    if (dirt && !S.masks) {
      postMessage({ type: "status", text: "Working out the dirt" });
      S.masks = TE.dirtMasks(T.consts, slot, ctx.pm());
    }
    for (const k of kits) {
      if (dirt) k.img = TE.applyDirt(T.consts, slot, k.img, S.masks, dirt);
      const n = PREVIEW * PREVIEW, rgba = new Uint8ClampedArray(4 * n);
      for (let i = 0; i < n; i++) {
        rgba[4 * i] = k.img[3 * i] * 255; rgba[4 * i + 1] = k.img[3 * i + 1] * 255; rgba[4 * i + 2] = k.img[3 * i + 2] * 255; rgba[4 * i + 3] = 255;
      }
      out.slots[slot][k.kit || "home"] = rgba;
      transfer.push(rgba.buffer);
    }
  }
  postMessage(out, transfer);
  if (team.previewDirt && team.previewDirt !== "clean") postMessage({ type: "status", text: "" });
}

async function letters(team, seq) {
  const j = team.jersey || {};
  const key = JSON.stringify([j.name, j.number, j.wordmark, j.crest !== false && team.logo !== "none" ? team.logo : null,
    team.colors.primary, team.colors.secondary, team.colors.accent, team.customLogo ? team.customLogo.id : 0, team.font || "block"]);
  if (key === letterKey && lettered) return preview(team, seq);
  postMessage({ type: "status", text: "Lettering the jersey" });
  const S = P.body;
  lettered = await TE.jerseyLettering(T.jersey, get, T.consts, S.full,
    { name: j.name, number: j.number, wordmark: j.wordmark, crest: j.crest !== false && team.logo !== "none" ? team.logo : null,
      customLogo: team.customLogo, glyphs: fonts[team.font] || null },
    TE.makeRecolour(T.consts, TE.teamMap(team)), null, true);
  letterKey = key;
  postMessage({ type: "status", text: "" });
  preview(team, seq);
}

// --------------------------------------------------------------------- make
async function make(slot, team, glyphs, player) {
  await loadT();
  const res = await TE.generate(T, get, team, (f, text) => postMessage({ type: "progress", slot, player, f, text }),
    { slots: [slot], glyphs, player });
  const m = res.made[slot], transfer = [];
  for (const v of Object.values(m.files)) transfer.push(v.buffer);
  postMessage({ type: "made", slot, player, options: m.options.map((o) => ({ label: o.label, files: o.files })), files: m.files }, transfer);
}

self.onmessage = async (e) => {
  const msg = e.data;
  try {
    if (msg.type === "init") await init();
    else if (msg.type === "preview") preview(msg.team, msg.seq);
    else if (msg.type === "letters") await letters(msg.team, msg.seq);
    else if (msg.type === "make") await make(msg.slot, msg.team, msg.glyphs || null, msg.player != null ? msg.player : null);
    else if (msg.type === "font") fonts[msg.key] = msg.glyphs;
  } catch (err) {
    postMessage({ type: "error", during: msg.type, slot: msg.slot, message: String((err && err.message) || err) });
  }
};
