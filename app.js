// Camera Synth — v1.0.0
const VERSION = "1.0.0";

const { useState, useEffect, useRef, useCallback } = React;

// ── Constants ────────────────────────────────────────────────────────────────
const SCALES = {
  chromatic:  [0,1,2,3,4,5,6,7,8,9,10,11],
  pentatonic: [0,2,4,7,9],
  major:      [0,2,4,5,7,9,11],
  minor:      [0,2,3,5,7,8,10],
  dorian:     [0,2,3,5,7,9,10],
  phrygian:   [0,1,3,5,7,8,10],
};
const SCALE_NAMES = Object.keys(SCALES);
const VOICE_OPTIONS = [1, 2, 4];
const FPS_OPTIONS   = [5, 10, 20, 30];
const ANALYSIS_RES  = 32;
const NOTE_NAMES    = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];

function midiToHz(midi) {
  return 440 * Math.pow(2, (midi - 69) / 12);
}

function quantizePitch(rawMidi, scale, rootNote) {
  const degrees = SCALES[scale];
  const octave   = Math.floor((rawMidi - rootNote) / 12);
  const semitone = ((rawMidi - rootNote) % 12 + 12) % 12;
  let closest = degrees[0], minDist = 99;
  for (const d of degrees) {
    const dist = Math.abs(d - semitone);
    if (dist < minDist) { minDist = dist; closest = d; }
  }
  return rootNote + octave * 12 + closest;
}

// ── Synth Engine ─────────────────────────────────────────────────────────────
class SynthEngine {
  constructor() {
    this.ctx          = null;
    this.voices       = [];
    this.filterNode   = null;
    this.reverbNode   = null;
    this.reverbGain   = null;
    this.dryGain      = null;
    this.masterGain   = null;
    this.limiterNode  = null;
    this.analyserNode = null;
    this.active       = false;
    this.currentPitchMidi = 60;
    this.wavetableData    = new Float32Array(ANALYSIS_RES).fill(0);
    this.settings = {
      voices: 1, detune: 12,
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72,
      reverbMix: 0.3, fps: 10,
    };
  }

  async init() {
    this.ctx = new (window.AudioContext || window.webkitAudioContext)();
    await this._buildReverb();

    this.filterNode = this.ctx.createBiquadFilter();
    this.filterNode.type = "lowpass";
    this.filterNode.frequency.value = 800;
    this.filterNode.Q.value = 1.5;

    this.dryGain = this.ctx.createGain();
    this.dryGain.gain.value = 1 - this.settings.reverbMix;

    this.reverbGain = this.ctx.createGain();
    this.reverbGain.gain.value = this.settings.reverbMix;

    this.masterGain = this.ctx.createGain();
    this.masterGain.gain.value = 0;

    this.limiterNode = this.ctx.createDynamicsCompressor();
    this.limiterNode.threshold.value = -3;
    this.limiterNode.knee.value      = 0;
    this.limiterNode.ratio.value     = 20;
    this.limiterNode.attack.value    = 0.001;
    this.limiterNode.release.value   = 0.1;

    this.analyserNode = this.ctx.createAnalyser();
    this.analyserNode.fftSize = 2048;

    this.filterNode.connect(this.dryGain);
    this.filterNode.connect(this.reverbNode);
    this.reverbNode.connect(this.reverbGain);
    this.dryGain.connect(this.masterGain);
    this.reverbGain.connect(this.masterGain);
    this.masterGain.connect(this.limiterNode);
    this.limiterNode.connect(this.analyserNode);
    this.analyserNode.connect(this.ctx.destination);

    this._spawnVoices();
  }

  async _buildReverb() {
    const len = this.ctx.sampleRate * 3;
    const buf = this.ctx.createBuffer(2, len, this.ctx.sampleRate);
    for (let c = 0; c < 2; c++) {
      const d = buf.getChannelData(c);
      for (let i = 0; i < len; i++) {
        d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / len, 2);
      }
    }
    this.reverbNode = this.ctx.createConvolver();
    this.reverbNode.buffer = buf;
  }

  _makeWavetable(data) {
    const size = 2048;
    const real = new Float32Array(size / 2);
    const imag = new Float32Array(size / 2);
    for (let i = 0; i < Math.min(data.length, size / 2 - 1); i++) {
      imag[i + 1] = data[i];
      real[i + 1] = 0;
    }
    return this.ctx.createPeriodicWave(real, imag, { disableNormalization: false });
  }

  _spawnVoices() {
    for (const v of this.voices) {
      try { v.osc.stop(); v.osc.disconnect(); v.gain.disconnect(); } catch(e) {}
    }
    this.voices = [];
    const n    = this.settings.voices;
    const wave = this._makeWavetable(this.wavetableData);
    for (let i = 0; i < n; i++) {
      const osc    = this.ctx.createOscillator();
      osc.setPeriodicWave(wave);
      const spread = n === 1 ? 0 : (i / (n - 1) - 0.5) * this.settings.detune * 2;
      osc.detune.value    = spread;
      osc.frequency.value = midiToHz(this.currentPitchMidi);
      const gain = this.ctx.createGain();
      gain.gain.value = 0.6 / n;
      osc.connect(gain);
      gain.connect(this.filterNode);
      osc.start();
      this.voices.push({ osc, gain });
    }
  }

  updateWavetable(data) {
    this.wavetableData = data;
    if (!this.ctx) return;
    const wave = this._makeWavetable(data);
    for (const v of this.voices) {
      try { v.osc.setPeriodicWave(wave); } catch(e) {}
    }
  }

  updatePitch(ribbonX) {
    if (!this.ctx) return;
    const { pitchMin, pitchMax, quantize, scale, rootNote } = this.settings;
    let midi = pitchMin + ribbonX * (pitchMax - pitchMin);
    if (quantize) midi = quantizePitch(Math.round(midi), scale, rootNote);
    this.currentPitchMidi = midi;
    const hz = midiToHz(midi);
    const t  = this.ctx.currentTime;
    for (const v of this.voices) {
      v.osc.frequency.setTargetAtTime(hz, t, 0.05);
    }
  }

  updateFromCamera({ hue, saturation }) {
    if (!this.ctx || !this.filterNode) return;
    const t      = this.ctx.currentTime;
    const cutoff = 200 + hue * 7800;
    this.filterNode.frequency.setTargetAtTime(cutoff, t, 0.1);
    this.filterNode.Q.setTargetAtTime(0.5 + saturation * 11.5, t, 0.1);
  }

  setSoundOn(on) {
    if (!this.ctx) return;
    const t = this.ctx.currentTime;
    if (on) {
      this.ctx.resume();
      this.masterGain.gain.setTargetAtTime(0.85, t, 0.1);
    } else {
      this.masterGain.gain.setTargetAtTime(0, t, 0.05);
    }
    this.active = on;
  }

  panic() {
    if (!this.ctx) return;
    this.masterGain.gain.cancelScheduledValues(this.ctx.currentTime);
    this.masterGain.gain.setValueAtTime(0, this.ctx.currentTime);
    this.active = false;
  }

  getAnalyserData() {
    if (!this.analyserNode) return null;
    const buf = new Float32Array(this.analyserNode.frequencyBinCount);
    this.analyserNode.getFloatTimeDomainData(buf);
    return buf;
  }

  destroy() {
    this.panic();
    for (const v of this.voices) { try { v.osc.stop(); } catch(e) {} }
    if (this.ctx) this.ctx.close();
  }
}

// ── Frame analysis ───────────────────────────────────────────────────────────
function analyseFrame(canvas, ctx2d) {
  const w = canvas.width, h = canvas.height;
  if (!w || !h) return null;
  const { data } = ctx2d.getImageData(0, 0, w, h);
  const total = w * h;

  let sumR = 0, sumG = 0, sumB = 0;
  let comXw = 0, comYw = 0, comW = 0;

  for (let i = 0; i < total; i++) {
    const r = data[i*4]   / 255;
    const g = data[i*4+1] / 255;
    const b = data[i*4+2] / 255;
    const lum = 0.2126*r + 0.7152*g + 0.0722*b;
    sumR += r; sumG += g; sumB += b;
    const x = (i % w) / w;
    const y = Math.floor(i / w) / h;
    comXw += x * lum; comYw += y * lum; comW += lum;
  }

  const avgR = sumR / total, avgG = sumG / total, avgB = sumB / total;
  const luma = 0.2126*avgR + 0.7152*avgG + 0.0722*avgB;

  const max = Math.max(avgR, avgG, avgB);
  const min = Math.min(avgR, avgG, avgB);
  const delta = max - min;
  let hue = 0;
  if (delta > 0) {
    if (max === avgR)      hue = ((avgG - avgB) / delta) % 6;
    else if (max === avgG) hue = (avgB - avgR) / delta + 2;
    else                   hue = (avgR - avgG) / delta + 4;
    hue = ((hue * 60) + 360) % 360;
  }
  const saturation = max === 0 ? 0 : delta / max;
  const comX = comW > 0 ? comXw / comW : 0.5;
  const comY = comW > 0 ? comYw / comW : 0.5;

  const midY = Math.floor(h / 2);
  const wt   = new Float32Array(ANALYSIS_RES);
  for (let i = 0; i < ANALYSIS_RES; i++) {
    const px  = Math.floor((i / ANALYSIS_RES) * w);
    const idx = (midY * w + px) * 4;
    wt[i] = (data[idx] / 127.5 - 1) * 0.8;
  }

  return { luma, hue: hue / 360, saturation, comX, comY, wavetable: wt };
}

// ── App ──────────────────────────────────────────────────────────────────────
function App() {
  const videoRef         = useRef(null);
  const captureCanvasRef = useRef(null);
  const scopeCanvasRef   = useRef(null);
  const ribbonRef        = useRef(null);
  const synthRef         = useRef(null);
  const streamRef        = useRef(null);
  const analysisTimerRef = useRef(null);
  const animFrameRef     = useRef(null);
  const mediaRecorderRef = useRef(null);
  const recordChunksRef  = useRef([]);

  const [soundOn,      setSoundOn]      = useState(false);
  const [recording,    setRecording]    = useState(false);
  const [showScope,    setShowScope]    = useState(true);
  const [showSettings, setShowSettings] = useState(false);
  const [facingMode,   setFacingMode]   = useState("environment");
  const [ribbonX,      setRibbonX]      = useState(0.5);
  const [cameraReady,  setCameraReady]  = useState(false);
  const [cameraError,  setCameraError]  = useState(null);
  const [engineReady,  setEngineReady]  = useState(false);
  const [frameData,    setFrameData]    = useState(null);

  const [settings, setSettings] = useState({
    voices: 1, detune: 12,
    quantize: false, scale: "pentatonic", rootNote: 48,
    pitchMin: 36, pitchMax: 72,
    reverbMix: 0.3, fps: 10,
  });

  // Init synth instance
  useEffect(() => {
    const synth = new SynthEngine();
    synthRef.current = synth;
    return () => { synth.destroy(); };
  }, []);

  // Sync settings → engine
  useEffect(() => {
    if (!synthRef.current) return;
    Object.assign(synthRef.current.settings, settings);
    if (synthRef.current.ctx) synthRef.current._spawnVoices();
  }, [settings]);

  // Camera
  useEffect(() => {
    let active = true;
    setCameraReady(false);
    setCameraError(null);
    async function startCamera() {
      if (streamRef.current) streamRef.current.getTracks().forEach(t => t.stop());
      try {
        const stream = await navigator.mediaDevices.getUserMedia({
          video: { facingMode, width: { ideal: 1280 }, height: { ideal: 720 } },
          audio: false,
        });
        if (!active) { stream.getTracks().forEach(t => t.stop()); return; }
        streamRef.current = stream;
        if (videoRef.current) {
          videoRef.current.srcObject = stream;
          await videoRef.current.play();
          setCameraReady(true);
        }
      } catch(e) {
        if (active) setCameraError(e.name === "NotAllowedError" ? "CAMERA PERMISSION DENIED" : "CAMERA UNAVAILABLE");
      }
    }
    startCamera();
    return () => {
      active = false;
      if (streamRef.current) streamRef.current.getTracks().forEach(t => t.stop());
    };
  }, [facingMode]);

  // Frame analysis loop
  useEffect(() => {
    if (!cameraReady) return;
    const interval = 1000 / settings.fps;
    const run = () => {
      const video  = videoRef.current;
      const canvas = captureCanvasRef.current;
      if (!video || !canvas || video.readyState < 2) return;
      canvas.width  = video.videoWidth  || 320;
      canvas.height = video.videoHeight || 240;
      const ctx2d = canvas.getContext("2d");
      ctx2d.drawImage(video, 0, 0, canvas.width, canvas.height);
      const data = analyseFrame(canvas, ctx2d);
      if (data) {
        setFrameData(data);
        const synth = synthRef.current;
        if (synth?.ctx) {
          synth.updateFromCamera(data);
          synth.updateWavetable(data.wavetable);
        }
      }
    };
    analysisTimerRef.current = setInterval(run, interval);
    return () => clearInterval(analysisTimerRef.current);
  }, [cameraReady, settings.fps]);

  // Scope draw loop
  useEffect(() => {
    const draw = () => {
      animFrameRef.current = requestAnimationFrame(draw);
      if (!showScope) return;
      const canvas = scopeCanvasRef.current;
      if (!canvas) return;
      const ctx = canvas.getContext("2d");
      const W = canvas.width, H = canvas.height;
      ctx.clearRect(0, 0, W, H);
      const waveData = synthRef.current?.getAnalyserData();
      if (!waveData || !soundOn) return;
      ctx.strokeStyle = "rgba(127,255,106,0.65)";
      ctx.lineWidth   = 1.5;
      ctx.shadowColor = "#7fff6a";
      ctx.shadowBlur  = 5;
      ctx.beginPath();
      const slice = W / waveData.length;
      for (let i = 0; i < waveData.length; i++) {
        const x = i * slice;
        const y = H / 2 + waveData[i] * H * 0.4;
        i === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
      }
      ctx.stroke();
    };
    animFrameRef.current = requestAnimationFrame(draw);
    return () => cancelAnimationFrame(animFrameRef.current);
  }, [showScope, soundOn]);

  const handleSoundToggle = useCallback(async () => {
    const synth = synthRef.current;
    if (!synth) return;
    if (!engineReady) {
      await synth.init();
      setEngineReady(true);
    }
    const next = !soundOn;
    synth.setSoundOn(next);
    setSoundOn(next);
  }, [soundOn, engineReady]);

  const handlePanic = useCallback(() => {
    synthRef.current?.panic();
    setSoundOn(false);
  }, []);

  const handleRibbon = useCallback((e) => {
    e.preventDefault();
    const rect = ribbonRef.current?.getBoundingClientRect();
    if (!rect) return;
    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const x = Math.max(0, Math.min(1, (clientX - rect.left) / rect.width));
    setRibbonX(x);
    synthRef.current?.updatePitch(x);
  }, []);

  const handleFlip = useCallback(() => {
    setFacingMode(f => f === "environment" ? "user" : "environment");
  }, []);

  const handleReload = useCallback(() => {
    window.location.reload();
  }, []);

  const handleRecord = useCallback(async () => {
    if (recording) {
      mediaRecorderRef.current?.stop();
      setRecording(false);
    } else {
      const synth = synthRef.current;
      if (!synth?.ctx) return;
      const dest   = synth.ctx.createMediaStreamDestination();
      synth.limiterNode.connect(dest);
      const chunks = [];
      recordChunksRef.current = chunks;
      const mr = new MediaRecorder(dest.stream);
      mr.ondataavailable = e => chunks.push(e.data);
      mr.onstop = () => {
        const blob = new Blob(chunks, { type: "audio/webm" });
        const url  = URL.createObjectURL(blob);
        const a    = document.createElement("a");
        a.href = url; a.download = `camsynth-${Date.now()}.webm`; a.click();
        synth.limiterNode.disconnect(dest);
      };
      mr.start();
      mediaRecorderRef.current = mr;
      setRecording(true);
    }
  }, [recording]);

  const setSetting = (key, val) => setSettings(s => ({ ...s, [key]: val }));

  const pitchRange    = settings.pitchMax - settings.pitchMin;
  const currentMidi   = Math.round(settings.pitchMin + ribbonX * pitchRange);
  const noteName      = NOTE_NAMES[currentMidi % 12] + (Math.floor(currentMidi / 12) - 1);
  const hueColor      = frameData ? `hsl(${Math.round(frameData.hue * 360)},70%,55%)` : "#7fff6a";

  return (
    <div style={{
      display: "flex", flexDirection: "column", alignItems: "center",
      width: "100%", height: "100vh",
      background: "#0a0a0b",
      fontFamily: "'IBM Plex Mono', 'Courier New', monospace",
      color: "#c8c8b4",
      userSelect: "none",
      touchAction: "none",
      overflow: "hidden",
    }}>
      <style>{`
        @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@300;400;500&display=swap');
        * { box-sizing: border-box; }
        .ctrl-btn {
          background: transparent;
          border: 1px solid #222;
          color: #c8c8b4;
          font-family: 'IBM Plex Mono', monospace;
          font-size: 10px;
          letter-spacing: 0.08em;
          padding: 6px 10px;
          cursor: pointer;
          transition: border-color 0.15s, color 0.15s, background 0.15s;
          text-transform: uppercase;
          -webkit-tap-highlight-color: transparent;
        }
        .ctrl-btn:active { background: #111; }
        .ctrl-btn.on  { border-color: #7fff6a; color: #7fff6a; }
        .ctrl-btn.rec { border-color: #ff4444; color: #ff4444; background: rgba(255,68,68,0.08); }
        .ctrl-btn.danger { border-color: #ff4444; color: #ff4444; }
        .ctrl-btn.danger:active { background: rgba(255,68,68,0.1); }
        .seg { background: transparent; border: 1px solid #1e1e1e; color: #555; font-family: 'IBM Plex Mono', monospace; font-size: 9px; padding: 3px 7px; cursor: pointer; transition: all 0.1s; -webkit-tap-highlight-color: transparent; }
        .seg.sel { border-color: #7fff6a; color: #7fff6a; background: rgba(127,255,106,0.06); }
        .srow { display: flex; align-items: center; justify-content: space-between; padding: 7px 0; border-bottom: 1px solid #161616; }
        .srow label { font-size: 9px; letter-spacing: 0.1em; color: #555; text-transform: uppercase; }
        input[type=range] { -webkit-appearance: none; width: 100%; height: 2px; background: #1e1e1e; outline: none; border-radius: 1px; }
        input[type=range]::-webkit-slider-thumb { -webkit-appearance: none; width: 12px; height: 12px; background: #7fff6a; border-radius: 50%; cursor: pointer; }
        input[type=range]::-moz-range-thumb { width: 12px; height: 12px; background: #7fff6a; border-radius: 50%; cursor: pointer; border: none; }
        .luma-track { width: 36px; height: 2px; background: #1a1a1a; border-radius: 1px; overflow: hidden; }
        .luma-fill  { height: 100%; background: #7fff6a; transition: width 0.1s; }
      `}</style>

      {/* ── Header ── */}
      <div style={{
        width: "100%", maxWidth: 480,
        padding: "env(safe-area-inset-top, 10px) 14px 6px",
        paddingTop: "max(env(safe-area-inset-top), 10px)",
        display: "flex", justifyContent: "space-between", alignItems: "center",
        flexShrink: 0,
      }}>
        <div style={{ display: "flex", alignItems: "baseline", gap: 8 }}>
          <span style={{ fontSize: 10, letterSpacing: "0.2em", color: "#333", textTransform: "uppercase" }}>CamSynth</span>
          <span style={{ fontSize: 8, color: "#2a2a2a", letterSpacing: "0.1em" }}>v{VERSION}</span>
        </div>
        <div style={{ display: "flex", gap: 4, alignItems: "center" }}>
          {frameData && (
            <div style={{ display: "flex", gap: 5, alignItems: "center" }}>
              <div className="luma-track">
                <div className="luma-fill" style={{ width: `${(frameData.luma * 100).toFixed(0)}%` }} />
              </div>
              <div style={{ width: 8, height: 8, borderRadius: "50%", background: hueColor, flexShrink: 0, boxShadow: `0 0 4px ${hueColor}` }} />
            </div>
          )}
          <button className="ctrl-btn" onClick={handleFlip}>⇄</button>
          <button className="ctrl-btn" onClick={handleReload} title="Reload app">↺</button>
        </div>
      </div>

      {/* ── Camera window ── */}
      <div style={{
        width: "100%", maxWidth: 480,
        flex: "1 1 0",
        position: "relative",
        background: "#050505",
        overflow: "hidden",
        borderTop: "1px solid #161616",
        borderBottom: "1px solid #161616",
        minHeight: 0,
      }}>
        <video
          ref={videoRef}
          playsInline muted autoPlay
          style={{
            width: "100%", height: "100%", objectFit: "cover", display: "block",
            transform: facingMode === "user" ? "scaleX(-1)" : "none",
          }}
        />

        {/* Oscilloscope overlay */}
        {showScope && (
          <canvas
            ref={scopeCanvasRef}
            width={480} height={100}
            style={{ position: "absolute", bottom: 0, left: 0, width: "100%", height: 70, pointerEvents: "none" }}
          />
        )}

        {/* Frame data HUD */}
        {frameData && (
          <div style={{
            position: "absolute", top: 8, left: 8,
            fontSize: 8, color: "rgba(127,255,106,0.4)",
            letterSpacing: "0.12em", lineHeight: 2,
            pointerEvents: "none",
          }}>
            <div>LMA {(frameData.luma * 100).toFixed(1)}</div>
            <div>HUE {Math.round(frameData.hue * 360)}°</div>
            <div>SAT {(frameData.saturation * 100).toFixed(1)}</div>
            <div>COM {frameData.comX.toFixed(2)}·{frameData.comY.toFixed(2)}</div>
          </div>
        )}

        {/* Camera state messages */}
        {!cameraReady && !cameraError && (
          <div style={{ position: "absolute", inset: 0, display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center", gap: 8 }}>
            <span style={{ color: "#2a2a2a", fontSize: 10, letterSpacing: "0.2em" }}>AWAITING CAMERA</span>
            <span style={{ color: "#1e1e1e", fontSize: 8, letterSpacing: "0.1em" }}>grant permission when prompted</span>
          </div>
        )}
        {cameraError && (
          <div style={{ position: "absolute", inset: 0, display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center", gap: 10 }}>
            <span style={{ color: "#ff4444", fontSize: 10, letterSpacing: "0.15em" }}>{cameraError}</span>
            <button className="ctrl-btn" onClick={handleReload} style={{ fontSize: 9 }}>↺ reload &amp; retry</button>
          </div>
        )}

        <canvas ref={captureCanvasRef} style={{ display: "none" }} />
      </div>

      {/* ── Pitch Ribbon ── */}
      <div style={{ width: "100%", maxWidth: 480, flexShrink: 0 }}>
        <div style={{ display: "flex", alignItems: "center", padding: "3px 14px 2px", gap: 8 }}>
          <span style={{ fontSize: 8, color: "#2a2a2a", letterSpacing: "0.1em" }}>PITCH</span>
          <span style={{ fontSize: 12, color: "#7fff6a", letterSpacing: "0.04em", minWidth: 32 }}>{noteName}</span>
          <span style={{ fontSize: 8, color: "#222", marginLeft: "auto" }}>
            {settings.quantize ? settings.scale : "free"} · {settings.pitchMin}–{settings.pitchMax}
          </span>
        </div>
        <div
          ref={ribbonRef}
          onMouseDown={handleRibbon}
          onMouseMove={e => e.buttons && handleRibbon(e)}
          onTouchStart={handleRibbon}
          onTouchMove={handleRibbon}
          style={{
            height: 40,
            background: "linear-gradient(90deg, #080d08 0%, #111a11 50%, #080d08 100%)",
            borderTop: "1px solid #161e16",
            borderBottom: "1px solid #161e16",
            position: "relative",
            cursor: "crosshair",
          }}
        >
          {Array.from({ length: pitchRange + 1 }, (_, i) => (
            <div key={i} style={{
              position: "absolute",
              left: `${(i / pitchRange) * 100}%`,
              top: i % 12 === 0 ? 0 : "65%",
              width: 1,
              height: i % 12 === 0 ? "100%" : "35%",
              background: i % 12 === 0 ? "#202820" : "#161c16",
            }} />
          ))}
          <div style={{
            position: "absolute",
            left: `${ribbonX * 100}%`,
            top: 0, bottom: 0, width: 2,
            background: "#7fff6a",
            boxShadow: "0 0 10px #7fff6a",
            transform: "translateX(-50%)",
            pointerEvents: "none",
            transition: "left 0.02s",
          }} />
        </div>
      </div>

      {/* ── Controls row ── */}
      <div style={{
        width: "100%", maxWidth: 480,
        padding: "6px 14px",
        display: "flex", gap: 5, alignItems: "center",
        flexShrink: 0,
      }}>
        <button
          className={`ctrl-btn ${soundOn ? "on" : ""}`}
          onClick={handleSoundToggle}
          style={{ flex: 2, fontSize: 11, padding: "10px 0", letterSpacing: "0.1em" }}
        >
          {soundOn ? "◼ ON" : "▶ OFF"}
        </button>
        <button
          className={`ctrl-btn ${recording ? "rec" : ""}`}
          onClick={handleRecord}
          style={{ flex: 1 }}
        >
          {recording ? "● REC" : "○ REC"}
        </button>
        <button
          className={`ctrl-btn ${showScope ? "on" : ""}`}
          onClick={() => setShowScope(s => !s)}
          style={{ flex: 1 }}
        >
          ∿
        </button>
        <button
          className={`ctrl-btn ${showSettings ? "on" : ""}`}
          onClick={() => setShowSettings(s => !s)}
          style={{ flex: 1 }}
        >
          ⚙
        </button>
      </div>

      {/* ── Settings drawer ── */}
      {showSettings && (
        <div style={{
          width: "100%", maxWidth: 480,
          padding: "8px 14px 14px",
          borderTop: "1px solid #161616",
          background: "#0c0c0d",
          overflowY: "auto",
          maxHeight: "30vh",
          flexShrink: 0,
        }}>

          <div className="srow">
            <label>Voices</label>
            <div style={{ display: "flex", gap: 2 }}>
              {VOICE_OPTIONS.map(v => (
                <button key={v} className={`seg ${settings.voices === v ? "sel" : ""}`} onClick={() => setSetting("voices", v)}>{v}</button>
              ))}
            </div>
          </div>

          <div className="srow" style={{ flexDirection: "column", alignItems: "flex-start", gap: 5 }}>
            <div style={{ display: "flex", width: "100%", justifyContent: "space-between" }}>
              <label>Detune</label>
              <span style={{ fontSize: 9, color: "#7fff6a" }}>{settings.detune} ct</span>
            </div>
            <input type="range" min={0} max={50} value={settings.detune} onChange={e => setSetting("detune", +e.target.value)} />
          </div>

          <div className="srow">
            <label>Quantize pitch</label>
            <button className={`seg ${settings.quantize ? "sel" : ""}`} onClick={() => setSetting("quantize", !settings.quantize)}>
              {settings.quantize ? "ON" : "OFF"}
            </button>
          </div>

          {settings.quantize && (
            <div className="srow" style={{ flexDirection: "column", alignItems: "flex-start", gap: 5 }}>
              <label>Scale</label>
              <div style={{ display: "flex", flexWrap: "wrap", gap: 2, marginTop: 1 }}>
                {SCALE_NAMES.map(s => (
                  <button key={s} className={`seg ${settings.scale === s ? "sel" : ""}`} onClick={() => setSetting("scale", s)}>{s}</button>
                ))}
              </div>
            </div>
          )}

          <div className="srow" style={{ flexDirection: "column", alignItems: "flex-start", gap: 5 }}>
            <div style={{ display: "flex", width: "100%", justifyContent: "space-between" }}>
              <label>Pitch range</label>
              <span style={{ fontSize: 9, color: "#7fff6a" }}>
                {NOTE_NAMES[settings.pitchMin % 12]}{Math.floor(settings.pitchMin/12)-1} → {NOTE_NAMES[settings.pitchMax % 12]}{Math.floor(settings.pitchMax/12)-1}
              </span>
            </div>
            <div style={{ display: "flex", gap: 8, width: "100%" }}>
              <input type="range" min={24} max={60} value={settings.pitchMin} onChange={e => setSetting("pitchMin", Math.min(+e.target.value, settings.pitchMax - 4))} />
              <input type="range" min={48} max={84} value={settings.pitchMax} onChange={e => setSetting("pitchMax", Math.max(+e.target.value, settings.pitchMin + 4))} />
            </div>
          </div>

          <div className="srow" style={{ flexDirection: "column", alignItems: "flex-start", gap: 5 }}>
            <div style={{ display: "flex", width: "100%", justifyContent: "space-between" }}>
              <label>Reverb mix</label>
              <span style={{ fontSize: 9, color: "#7fff6a" }}>{Math.round(settings.reverbMix * 100)}%</span>
            </div>
            <input type="range" min={0} max={100} value={Math.round(settings.reverbMix * 100)} onChange={e => setSetting("reverbMix", e.target.value / 100)} />
          </div>

          <div className="srow">
            <label>Analysis rate</label>
            <div style={{ display: "flex", gap: 2 }}>
              {FPS_OPTIONS.map(f => (
                <button key={f} className={`seg ${settings.fps === f ? "sel" : ""}`} onClick={() => setSetting("fps", f)}>{f}fps</button>
              ))}
            </div>
          </div>

          <div style={{ marginTop: 10, display: "flex", gap: 5 }}>
            <button className="ctrl-btn danger" onClick={handlePanic} style={{ flex: 1, padding: "8px 0", letterSpacing: "0.12em" }}>
              ■ PANIC
            </button>
            <button className="ctrl-btn" onClick={handleReload} style={{ flex: 1, padding: "8px 0", letterSpacing: "0.12em" }}>
              ↺ RELOAD
            </button>
          </div>

          <div style={{ marginTop: 10, paddingTop: 8, borderTop: "1px solid #161616", textAlign: "center" }}>
            <span style={{ fontSize: 8, color: "#1e1e1e", letterSpacing: "0.15em" }}>CAMERA SYNTH v{VERSION}</span>
          </div>
        </div>
      )}
    </div>
  );
}

const root = ReactDOM.createRoot(document.getElementById("root"));
root.render(React.createElement(App));
