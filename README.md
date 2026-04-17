# Camera Synth — v1.0.0

Live camera → drone synthesizer. Mobile-first PWA.

## Deploy to GitHub Pages

```bash
# 1. Create a new repo on GitHub, e.g. "camera-synth"

# 2. Clone and copy files in
git clone https://github.com/YOUR_USERNAME/camera-synth.git
cd camera-synth
cp -r /path/to/this/folder/* .

# 3. Push
git add .
git commit -m "v1.0.0 — initial"
git push origin main

# 4. Enable GitHub Pages
# GitHub repo → Settings → Pages → Source: Deploy from branch → main / (root)
```

Your app will be live at:
`https://YOUR_USERNAME.github.io/camera-synth/`

## Update version

Edit the `VERSION` constant at the top of `app.js`.
Also bump `CACHE` name in `sw.js` to bust the service worker cache:
```js
const CACHE = "camsynth-v1.0.1";  // increment this
```

## File structure

```
index.html      — PWA shell, loads React + Babel via CDN
app.js          — Full synth engine + UI (edit this)
manifest.json   — PWA manifest
sw.js           — Service worker (offline + cache)
icons/          — App icons (192 + 512px)
```

## Signal flow

```
Camera frame → pixel analysis → wavetable oscillator(s)
  Hue         → filter cutoff (200–8000 Hz)
  Saturation  → filter resonance (Q 0.5–12)
  Luma        → wavetable morph (via pixel row)
  Pitch ribbon → oscillator frequency
  Touch XY    → (coming next)
→ Filter → Reverb → Master → Limiter → Output
```

## Notes

- Camera permission is required — browser will prompt on first load
- AudioContext starts on first "SOUND OFF → ON" tap (browser policy)
- Recording downloads a `.webm` audio file
- Works best in Chrome/Safari on iOS/Android
