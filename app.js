// Camera Synth — v1.1.0
var VERSION = "2.6.0";

var useState    = React.useState;
var useEffect   = React.useEffect;
var useRef      = React.useRef;
var useCallback = React.useCallback;

// ── Constants ────────────────────────────────────────────────────────────────
var SCALES = {
  chromatic:  [0,1,2,3,4,5,6,7,8,9,10,11],
  pentatonic: [0,2,4,7,9],
  major:      [0,2,4,5,7,9,11],
  minor:      [0,2,3,5,7,8,10],
  dorian:     [0,2,3,5,7,9,10],
  phrygian:   [0,1,3,5,7,8,10],
};
var SCALE_NAMES   = Object.keys(SCALES);
var VOICE_OPTIONS = [1, 2, 4];
var FPS_OPTIONS   = [5, 10, 20, 30];
var ANALYSIS_RES  = 256;
var NOTE_NAMES    = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];

function midiToHz(midi) {
  return 440 * Math.pow(2, (midi - 69) / 12);
}

function quantizePitch(rawMidi, scale, rootNote) {
  var degrees  = SCALES[scale];
  var octave   = Math.floor((rawMidi - rootNote) / 12);
  var semitone = ((rawMidi - rootNote) % 12 + 12) % 12;
  var closest = degrees[0], minDist = 99;
  for (var i = 0; i < degrees.length; i++) {
    var dist = Math.abs(degrees[i] - semitone);
    if (dist < minDist) { minDist = dist; closest = degrees[i]; }
  }
  return rootNote + octave * 12 + closest;
}

// ── Synth Engine ─────────────────────────────────────────────────────────────
function makeSynthEngine() {
  // Pre-build reverb IR now (before any user gesture) so init() is instant
  var REVERB_IR = (function() {
    var sr  = 44100;
    var len = sr * 2;
    var L   = new Float32Array(len);
    var R   = new Float32Array(len);
    for (var i = 0; i < len; i++) {
      var decay = Math.pow(1 - i / len, 2.5);
      L[i] = (Math.random() * 2 - 1) * decay;
      R[i] = (Math.random() * 2 - 1) * decay;
    }
    return { L: L, R: R, len: len };
  }());

  var eng = {
    ctx: null, voices: [],
    filterNode: null, reverbNode: null, reverbGain: null,
    dryGain: null, masterGain: null, limiterNode: null, analyserNode: null,
    active: false, currentPitchMidi: 60,
    wavetableData:    new Float32Array(ANALYSIS_RES),
    morphedWavetable: new Float32Array(ANALYSIS_RES), // smoothly interpolated
    lastWavetable:    new Float32Array(ANALYSIS_RES), // previous frame
    settings: {
      voices: 1, detune: 12,
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72, reverbMix: 0.3, fps: 10,
    },
  };

  // init() must be called synchronously inside a user gesture on iOS.
  // Keep it minimal — no loops, no allocation, just wire nodes.
  eng.init = function() {
    if (eng.ctx) return; // already initialised
    try {
      var AC  = window.AudioContext || window.webkitAudioContext;
      eng.ctx = new AC();

      // Load pre-built reverb IR into an AudioBuffer at the real sample rate
      var sr  = eng.ctx.sampleRate;
      var len = REVERB_IR.len;
      var buf = eng.ctx.createBuffer(2, len, sr);
      buf.getChannelData(0).set(REVERB_IR.L);
      buf.getChannelData(1).set(REVERB_IR.R);
      eng.reverbNode = eng.ctx.createConvolver();
      eng.reverbNode.buffer = buf;

      eng.filterNode = eng.ctx.createBiquadFilter();
      eng.filterNode.type = "lowpass";
      eng.filterNode.frequency.value = 800;
      eng.filterNode.Q.value = 1.5;

      eng.dryGain = eng.ctx.createGain();
      eng.dryGain.gain.value = 1 - eng.settings.reverbMix;

      eng.reverbGain = eng.ctx.createGain();
      eng.reverbGain.gain.value = eng.settings.reverbMix;

      eng.masterGain = eng.ctx.createGain();
      eng.masterGain.gain.value = 0;

      eng.limiterNode = eng.ctx.createDynamicsCompressor();
      eng.limiterNode.threshold.value = -3;
      eng.limiterNode.knee.value      = 0;
      eng.limiterNode.ratio.value     = 20;
      eng.limiterNode.attack.value    = 0.001;
      eng.limiterNode.release.value   = 0.1;

      eng.analyserNode = eng.ctx.createAnalyser();
      eng.analyserNode.fftSize = 1024;

      eng.filterNode.connect(eng.dryGain);
      eng.filterNode.connect(eng.reverbNode);
      eng.reverbNode.connect(eng.reverbGain);
      eng.dryGain.connect(eng.masterGain);
      eng.reverbGain.connect(eng.masterGain);
      eng.masterGain.connect(eng.limiterNode);
      eng.limiterNode.connect(eng.analyserNode);
      eng.analyserNode.connect(eng.ctx.destination);

      eng.spawnVoices();
    } catch(e) {
      console.error("[CamSynth] init failed", e);
    }
  };

  eng.makeWavetable = function(data) {
    var size = 1024;
    var real = new Float32Array(size / 2);
    var imag = new Float32Array(size / 2);
    var lim  = Math.min(data.length, size / 2 - 1);
    for (var i = 0; i < lim; i++) { imag[i + 1] = data[i]; }
    return eng.ctx.createPeriodicWave(real, imag, { disableNormalization: false });
  };

  eng.spawnVoices = function() {
    for (var i = 0; i < eng.voices.length; i++) {
      try {
        eng.voices[i].osc.stop();
        eng.voices[i].osc.disconnect();
        eng.voices[i].gain.disconnect();
        if (eng.voices[i].panner) eng.voices[i].panner.disconnect();
        if (eng.voices[i].delay)  eng.voices[i].delay.disconnect();
      } catch(e) {}
    }
    eng.voices = [];
    var n = eng.settings.voices;
    var hasData = false;
    for (var k = 0; k < eng.wavetableData.length; k++) {
      if (eng.wavetableData[k] !== 0) { hasData = true; break; }
    }

    for (var i = 0; i < n; i++) {
      var osc = eng.ctx.createOscillator();
      if (hasData) {
        try { osc.setPeriodicWave(eng.makeWavetable(eng.wavetableData)); } catch(e) { osc.type = "sine"; }
      } else {
        osc.type = "sine";
      }
      var spread = n === 1 ? 0 : ((i / (n - 1)) - 0.5) * eng.settings.detune * 2;
      osc.detune.value    = spread;
      osc.frequency.value = midiToHz(eng.currentPitchMidi);

      var gain = eng.ctx.createGain();
      gain.gain.value = 0.55 / n;

      // Pan each voice across stereo field
      var panner = eng.ctx.createStereoPanner();
      panner.pan.value = n === 1 ? 0 : ((i / (n - 1)) * 2 - 1); // -1 to +1

      osc.connect(gain);
      gain.connect(panner);
      panner.connect(eng.filterNode);
      osc.start();
      eng.voices.push({ osc: osc, gain: gain, panner: panner });
    }

    // Single voice: add Haas delay for stereo width
    // A ~20ms delay on one channel creates psychoacoustic width without phase issues
    if (n === 1 && eng.voices.length === 1) {
      var delay = eng.ctx.createDelay(0.05);
      delay.delayTime.value = 0.018; // 18ms Haas delay
      var delayGain = eng.ctx.createGain();
      delayGain.gain.value = 0.6;
      var delayPan = eng.ctx.createStereoPanner();
      delayPan.pan.value = 0.8; // delayed signal panned right
      // Direct signal panned slightly left
      eng.voices[0].panner.pan.value = -0.5;
      // Tap off the voice gain → delay → pan right → filter
      eng.voices[0].gain.connect(delay);
      delay.connect(delayGain);
      delayGain.connect(delayPan);
      delayPan.connect(eng.filterNode);
      eng.voices[0].delay     = delay;
      eng.voices[0].delayGain = delayGain;
      eng.voices[0].delayPan  = delayPan;
    }
  };

  // Smoothly ramp detune on existing voices without respawning
  eng.updateDetune = function(detune) {
    eng.settings.detune = detune;
    if (!eng.ctx || eng.voices.length === 0) return;
    var n = eng.voices.length;
    var t = eng.ctx.currentTime;
    for (var i = 0; i < n; i++) {
      var spread = n === 1 ? 0 : ((i / (n - 1)) - 0.5) * detune * 2;
      eng.voices[i].osc.detune.setTargetAtTime(spread, t, 0.08);
    }
  };

  // Morph speed: how fast we interpolate toward new wavetable (0=instant, 1=never)
  eng.morphAlpha = 0.35; // faster morph = more dynamic response // per-frame lerp factor (~200ms at 10fps)

  eng.updateWavetable = function(data) {
    eng.wavetableData = data;
    if (!eng.ctx) return;
    // Lerp morphedWavetable toward new data
    var alpha = eng.morphAlpha;
    var hasData = false;
    for (var k = 0; k < data.length; k++) {
      eng.morphedWavetable[k] = eng.morphedWavetable[k] * (1 - alpha) + data[k] * alpha;
      if (data[k] !== 0) hasData = true;
    }
    if (!hasData) return;
    try {
      var wave = eng.makeWavetable(eng.morphedWavetable);
      for (var i = 0; i < eng.voices.length; i++) {
        try { eng.voices[i].osc.setPeriodicWave(wave); } catch(e) { eng.voices[i].osc.type = "sine"; }
      }
    } catch(e) {}
  };

  eng.updatePitch = function(rx) {
    if (!eng.ctx) return;
    var s    = eng.settings;
    var midi = s.pitchMin + rx * (s.pitchMax - s.pitchMin);
    if (s.quantize) midi = quantizePitch(Math.round(midi), s.scale, s.rootNote);
    eng.currentPitchMidi = midi;
    var hz = midiToHz(midi);
    var t  = eng.ctx.currentTime;
    for (var i = 0; i < eng.voices.length; i++) {
      eng.voices[i].osc.frequency.setTargetAtTime(hz, t, 0.05);
    }
  };

  eng.updateFromCamera = function(hue, sat) {
    if (!eng.ctx || !eng.filterNode) return;
    var t = eng.ctx.currentTime;
    eng.filterNode.frequency.setTargetAtTime(200 + hue * 7800, t, 0.15);
    eng.filterNode.Q.setTargetAtTime(0.5 + sat * 11.5, t, 0.15);
  };

  eng.setSoundOn = function(on) {
    if (!eng.ctx) return;
    // On iOS, resume() is async. We set gain via value= (not scheduled)
    // so it takes effect as soon as the context actually starts running,
    // regardless of when that happens relative to our call.
    eng.ctx.resume();
    eng.masterGain.gain.cancelScheduledValues(0);
    if (on) {
      // Set directly — works even if ctx is still suspended
      eng.masterGain.gain.value = 0.7;
    } else {
      eng.masterGain.gain.value = 0;
    }
    eng.active = on;
  };

  eng.panic = function() {
    if (!eng.ctx) return;
    eng.masterGain.gain.cancelScheduledValues(eng.ctx.currentTime);
    eng.masterGain.gain.setValueAtTime(0, eng.ctx.currentTime);
    eng.active = false;
  };

  eng.getAnalyserData = function() {
    if (!eng.analyserNode) return null;
    var buf = new Float32Array(eng.analyserNode.frequencyBinCount);
    eng.analyserNode.getFloatTimeDomainData(buf);
    return buf;
  };

  // WAV recording via raw PCM capture
  eng.startRecording = function() {
    if (!eng.ctx) return;
    var bufSize  = 4096;
    var chunks   = [];
    var recorder = eng.ctx.createScriptProcessor(bufSize, 2, 2);
    recorder.onaudioprocess = function(e) {
      var L = new Float32Array(e.inputBuffer.getChannelData(0));
      var R = new Float32Array(e.inputBuffer.getChannelData(1));
      chunks.push({ L: L, R: R });
    };
    eng.limiterNode.connect(recorder);
    recorder.connect(eng.ctx.destination);
    eng._recorder   = recorder;
    eng._recChunks  = chunks;
  };

  eng.stopRecording = function() {
    if (!eng._recorder) return null;
    eng.limiterNode.disconnect(eng._recorder);
    eng._recorder.disconnect();
    var chunks = eng._recChunks;
    eng._recorder  = null;
    eng._recChunks = null;

    // Encode WAV
    var sr      = eng.ctx.sampleRate;
    var nFrames = chunks.reduce(function(s, c) { return s + c.L.length; }, 0);
    var nCh     = 2;
    var bitsPS  = 16;
    var bytesPF = nCh * (bitsPS / 8);
    var dataLen = nFrames * bytesPF;
    var buf     = new ArrayBuffer(44 + dataLen);
    var view    = new DataView(buf);
    function str(off, s) { for (var i=0;i<s.length;i++) view.setUint8(off+i, s.charCodeAt(i)); }
    function u32(off, v) { view.setUint32(off, v, true); }
    function u16(off, v) { view.setUint16(off, v, true); }
    str(0,"RIFF"); u32(4, 36+dataLen); str(8,"WAVE");
    str(12,"fmt "); u32(16,16); u16(20,1); u16(22,nCh);
    u32(24,sr); u32(28,sr*bytesPF); u16(32,bytesPF); u16(34,bitsPS);
    str(36,"data"); u32(40,dataLen);
    var off = 44;
    for (var ci=0; ci<chunks.length; ci++) {
      var L = chunks[ci].L, R = chunks[ci].R;
      for (var fi=0; fi<L.length; fi++) {
        var ls = Math.max(-1,Math.min(1,L[fi]));
        var rs = Math.max(-1,Math.min(1,R[fi]));
        view.setInt16(off,   ls < 0 ? ls*0x8000 : ls*0x7FFF, true); off+=2;
        view.setInt16(off,   rs < 0 ? rs*0x8000 : rs*0x7FFF, true); off+=2;
      }
    }
    return buf;
  };

  // ── Looper ──────────────────────────────────────────────────
  var MAX_LOOP_SECS = 10;
  eng._loopProc      = null;
  eng._loopChunks    = [];
  eng._loopNode      = null;
  eng._loopGain      = null;
  eng._loopRecording = false;

  eng.startLoopRecord = function() {
    if (!eng.ctx) return;
    // Stop any existing loop first
    eng.stopLoop();
    eng._loopRecording = true;
    eng._loopChunks    = [];
    var sr         = eng.ctx.sampleRate;
    var maxSamples = sr * MAX_LOOP_SECS;
    var captured   = 0;
    var bufSize    = 4096;
    var proc = eng.ctx.createScriptProcessor(bufSize, 2, 2);
    proc.onaudioprocess = function(ev) {
      if (!eng._loopRecording) return;
      if (captured >= maxSamples) {
        eng._loopRecording = false;
        return;
      }
      // Copy — don't hold reference to the buffer (it gets reused)
      var L = new Float32Array(ev.inputBuffer.getChannelData(0));
      var R = new Float32Array(ev.inputBuffer.getChannelData(1));
      eng._loopChunks.push({ L: L, R: R });
      captured += L.length;
    };
    eng.limiterNode.connect(proc);
    proc.connect(eng.ctx.destination);
    eng._loopProc = proc;
    console.log("[loop] recording started");
  };

  eng.commitLoop = function() {
    // Stop capturing
    eng._loopRecording = false;
    if (eng._loopProc) {
      try { eng.limiterNode.disconnect(eng._loopProc); eng._loopProc.disconnect(); } catch(ex) {}
      eng._loopProc = null;
    }

    var chunks = eng._loopChunks;
    console.log("[loop] committing, chunks=", chunks.length);
    if (!chunks.length) return false;

    var sr      = eng.ctx.sampleRate;
    var nFrames = chunks.reduce(function(s,c){ return s+c.L.length; }, 0);
    if (nFrames < 512) return false; // too short

    var buf  = eng.ctx.createBuffer(2, nFrames, sr);
    var outL = buf.getChannelData(0);
    var outR = buf.getChannelData(1);
    var off  = 0;
    for (var i = 0; i < chunks.length; i++) {
      outL.set(chunks[i].L, off);
      outR.set(chunks[i].R, off);
      off += chunks[i].L.length;
    }

    // 8ms crossfade at seam
    var fadeLen = Math.min(Math.floor(sr * 0.008), Math.floor(nFrames / 4));
    for (var j = 0; j < fadeLen; j++) {
      var fi = j / fadeLen;
      outL[j] *= fi; outR[j] *= fi;
      outL[nFrames-fadeLen+j] *= (1-fi);
      outR[nFrames-fadeLen+j] *= (1-fi);
    }

    // Mute live synth
    eng.masterGain.gain.value = 0;

    // Play loop
    var lg = eng.ctx.createGain();
    lg.gain.value = 0.85;
    lg.connect(eng.limiterNode);
    var src = eng.ctx.createBufferSource();
    src.buffer = buf;
    src.loop   = true;
    src.connect(lg);
    src.start(0);
    eng._loopNode = src;
    eng._loopGain = lg;
    console.log("[loop] playing, frames=", nFrames, "dur=", (nFrames/sr).toFixed(2)+"s");
    return true;
  };

  eng.stopLoop = function() {
    eng._loopRecording = false;
    if (eng._loopProc) {
      try { eng.limiterNode.disconnect(eng._loopProc); eng._loopProc.disconnect(); } catch(ex) {}
      eng._loopProc = null;
    }
    if (eng._loopNode) {
      try { eng._loopNode.stop(); eng._loopNode.disconnect(); } catch(ex) {}
      eng._loopNode = null;
    }
    if (eng._loopGain) {
      try { eng._loopGain.disconnect(); } catch(ex) {}
      eng._loopGain = null;
    }
    eng._loopChunks = [];
    if (eng.active) eng.masterGain.gain.value = 0.7;
    console.log("[loop] stopped");
  };

  eng.isLooping = function() { return !!eng._loopNode; };

  eng.destroy = function() {
    eng.panic();
    for (var i = 0; i < eng.voices.length; i++) { try { eng.voices[i].osc.stop(); } catch(e) {} }
    if (eng.ctx) eng.ctx.close();
  };

  return eng;
}

// ── Frame analysis ───────────────────────────────────────────────────────────
function analyseFrame(canvas, ctx2d) {
  var w = canvas.width, h = canvas.height;
  if (!w || !h) return null;
  var px    = ctx2d.getImageData(0, 0, w, h).data;
  var total = w * h;
  var sumR = 0, sumG = 0, sumB = 0, comXw = 0, comYw = 0, comW = 0;

  for (var i = 0; i < total; i++) {
    var r   = px[i*4]   / 255;
    var g   = px[i*4+1] / 255;
    var b   = px[i*4+2] / 255;
    var lum = 0.2126*r + 0.7152*g + 0.0722*b;
    sumR += r; sumG += g; sumB += b;
    comXw += (i % w) / w * lum;
    comYw += Math.floor(i / w) / h * lum;
    comW  += lum;
  }

  var avgR = sumR/total, avgG = sumG/total, avgB = sumB/total;
  var luma  = 0.2126*avgR + 0.7152*avgG + 0.0722*avgB;
  var max   = Math.max(avgR,avgG,avgB), min = Math.min(avgR,avgG,avgB), delta = max - min;
  var hue   = 0;
  if (delta > 0) {
    if (max===avgR)      hue = ((avgG-avgB)/delta) % 6;
    else if (max===avgG) hue = (avgB-avgR)/delta + 2;
    else                 hue = (avgR-avgG)/delta + 4;
    hue = ((hue*60)+360) % 360;
  }
  var sat  = max===0 ? 0 : delta/max;
  var comX = comW>0 ? comXw/comW : 0.5;
  var comY = comW>0 ? comYw/comW : 0.5;

  // Raster-scan wavetable: sample ANALYSIS_RES evenly spaced points across
  // the full image in a boustrophedon (snake) pattern — left→right on even rows,
  // right→left on odd rows. Point-sampled to preserve local variance & texture.
  // A small 3x3 neighbourhood average per point gives gentle anti-aliasing
  // without destroying the signal dynamics that make interesting waveforms.
  var wt   = new Float32Array(ANALYSIS_RES);
  var cols = Math.ceil(Math.sqrt(ANALYSIS_RES * (w / h)));
  var rows = Math.ceil(ANALYSIS_RES / cols);
  var idx2 = 0;
  for (var row2 = 0; row2 < rows && idx2 < ANALYSIS_RES; row2++) {
    var rowFrac = (row2 + 0.5) / rows;
    var py2     = Math.floor(rowFrac * h);
    var leftToRight = (row2 % 2 === 0);
    for (var col2 = 0; col2 < cols && idx2 < ANALYSIS_RES; col2++) {
      var c2      = leftToRight ? col2 : (cols - 1 - col2);
      var colFrac = (c2 + 0.5) / cols;
      var px2     = Math.floor(colFrac * w);
      // 3x3 neighbourhood average for gentle AA
      var sum2 = 0, cnt2 = 0;
      for (var dy = -1; dy <= 1; dy++) {
        for (var dx = -1; dx <= 1; dx++) {
          var nx = Math.max(0, Math.min(w-1, px2+dx));
          var ny = Math.max(0, Math.min(h-1, py2+dy));
          var pi = (ny * w + nx) * 4;
          sum2 += 0.2126*(px[pi]/255) + 0.7152*(px[pi+1]/255) + 0.0722*(px[pi+2]/255);
          cnt2++;
        }
      }
      wt[idx2++] = (sum2/cnt2) * 2 - 1; // luma 0..1 → waveform -1..1
    }
  }

  return { luma: luma, hue: hue/360, saturation: sat, comX: comX, comY: comY, wavetable: wt };
}

// ── Helpers ──────────────────────────────────────────────────────────────────
function el(type, props) {
  var args = [type, props || null];
  for (var i = 2; i < arguments.length; i++) args.push(arguments[i]);
  return React.createElement.apply(React, args);
}

function cx() {
  return Array.prototype.slice.call(arguments).filter(Boolean).join(" ");
}

// ── App ──────────────────────────────────────────────────────────────────────
function App() {
  var videoRef         = useRef(null);
  var captureRef       = useRef(null);
  var loopFramesRef    = useRef([]);   // captured video frames for loop
  var loopOverlayRef   = useRef(null); // canvas overlay for video loop playback
  var loopVidTimerRef  = useRef(null); // setInterval for video loop playback
  var loopFrameIdxRef  = useRef(0);
  var scopeRef         = useRef(null);
  var ribbonRef        = useRef(null);
  var synthRef         = useRef(null);
  var streamRef        = useRef(null);
  var timerRef         = useRef(null);
  var rafRef           = useRef(null);
  var mrRef            = useRef(null);
  var chunksRef        = useRef([]);

  var r1  = useState(false);  var soundOn      = r1[0], setSoundOn      = r1[1];
  var r2  = useState(false);  var recording    = r2[0], setRecording    = r2[1];
  var r3  = useState(true);   var showScope    = r3[0], setShowScope    = r3[1];
  var r4  = useState(false);  var showSettings = r4[0], setShowSettings = r4[1];
  var r5  = useState("environment"); var facingMode = r5[0], setFacingMode = r5[1];
  var r6  = useState(0.5);    var ribbonX      = r6[0], setRibbonX      = r6[1];
  var r7  = useState(false);  var camReady     = r7[0], setCamReady     = r7[1];
  var r8  = useState(null);   var camError     = r8[0], setCamError     = r8[1];
  var r9  = useState(false);  var engReady     = r9[0], setEngReady     = r9[1];
  var r12 = useState(true);   var camOn        = r12[0], setCamOn       = r12[1];
  var r13 = useState(false);  var looping      = r13[0], setLooping     = r13[1];
  var r14 = useState(false);  var loopCapturing = r14[0], setLoopCapturing = r14[1];
  var r10 = useState(null);   var frameData    = r10[0], setFrameData   = r10[1];

  var r11 = useState({ voices:1, detune:12, quantize:false, scale:"pentatonic", rootNote:48, pitchMin:36, pitchMax:72, reverbMix:0.3, fps:10, showScales:false });
  var settings = r11[0], setSettings = r11[1];

  function setSetting(k, v) { setSettings(function(s) { var n=Object.assign({},s); n[k]=v; return n; }); }

  useEffect(function() {
    var eng = makeSynthEngine();
    synthRef.current = eng;
    return function() { eng.destroy(); };
  }, []);

  useEffect(function() {
    var eng = synthRef.current;
    if (!eng) return;
    Object.assign(eng.settings, settings);
    if (eng.ctx) eng.spawnVoices();
  }, [settings]);

  useEffect(function() {
    if (!camOn) return;
    var alive = true;
    setCamReady(false); setCamError(null);
    if (streamRef.current) streamRef.current.getTracks().forEach(function(t){t.stop();});

    navigator.mediaDevices.getUserMedia({ video:{ facingMode:facingMode, width:{ideal:1280}, height:{ideal:720} }, audio:false })
      .then(function(stream) {
        if (!alive) { stream.getTracks().forEach(function(t){t.stop();}); return; }
        streamRef.current = stream;
        var v = videoRef.current;
        if (v) {
          v.srcObject = stream;
          v.play().then(function(){ if(alive) setCamReady(true); }).catch(function(){ if(alive) setCamReady(true); });
        }
      })
      .catch(function(e) {
        if (!alive) return;
        setCamError(e.name==="NotAllowedError" ? "CAMERA PERMISSION DENIED" : "CAMERA UNAVAILABLE");
      });

    return function() {
      alive = false;
      if (streamRef.current) streamRef.current.getTracks().forEach(function(t){t.stop();});
    };
  }, [facingMode, camOn]);

  useEffect(function() {
    if (!camReady) return;
    var ms = 1000 / settings.fps;
    timerRef.current = setInterval(function() {
      var v = videoRef.current, c = captureRef.current;
      if (!v || !c || v.readyState < 2) return;
      c.width = v.videoWidth||320; c.height = v.videoHeight||240;
      var ctx2d = c.getContext("2d");
      ctx2d.drawImage(v, 0, 0, c.width, c.height);
      var data = analyseFrame(c, ctx2d);
      if (data) {
        setFrameData(data);
        var eng = synthRef.current;
        if (eng && eng.ctx) { eng.updateFromCamera(data.hue, data.saturation); eng.updateWavetable(data.wavetable); }
        // Capture video frames while loop recording
        if (eng && eng._loopRecording) {
          var MAX_FRAMES = 100;
          if (loopFramesRef.current.length < MAX_FRAMES) {
            loopFramesRef.current.push(ctx2d.getImageData(0, 0, c.width, c.height));
          }
        }
      }
    }, ms);
    return function() { clearInterval(timerRef.current); };
  }, [camReady, settings.fps]);

  useEffect(function() {
    var alive = true;
    function draw() {
      if (!alive) return;
      rafRef.current = requestAnimationFrame(draw);
      if (!showScope) return;
      var canvas = scopeRef.current;
      if (!canvas) return;
      var ctx = canvas.getContext("2d");
      var W = canvas.width, H = canvas.height;
      ctx.clearRect(0,0,W,H);
      var eng = synthRef.current;
      var wd  = eng ? eng.getAnalyserData() : null;
      if (!wd || !soundOn) return;
      // Find peak for normalization — makes scope fill display regardless of amplitude
      var peak = 0.001;
      for (var p=0; p<wd.length; p++) { var a=Math.abs(wd[p]); if(a>peak) peak=a; }
      var scale = Math.min(1/peak, 8); // normalize, cap at 8x to avoid noise blow-up
      ctx.strokeStyle = "rgba(127,255,106,0.85)";
      ctx.lineWidth = 1.5;
      ctx.shadowColor = "#7fff6a"; ctx.shadowBlur = 8;
      ctx.beginPath();
      var sl = W / wd.length;
      for (var i=0; i<wd.length; i++) {
        var x=i*sl, y=H/2+wd[i]*scale*H*0.42;
        if(i===0) ctx.moveTo(x,y); else ctx.lineTo(x,y);
      }
      ctx.stroke();
    }
    rafRef.current = requestAnimationFrame(draw);
    return function() { alive=false; cancelAnimationFrame(rafRef.current); };
  }, [showScope, soundOn]);

  var handleSound = useCallback(function() {
    var eng = synthRef.current;
    if (!eng) return;
    // Both init() and setSoundOn() must run synchronously inside this gesture handler
    if (!eng.ctx) {
      eng.init();
      setEngReady(true);
    }
    var next = !soundOn;
    eng.setSoundOn(next);
    setSoundOn(next);
  }, [soundOn]);

  var handlePanic = useCallback(function() {
    var eng = synthRef.current;
    if (eng) eng.panic();
    setSoundOn(false);
  }, []);

  var handleRibbon = useCallback(function(e) {
    e.preventDefault();
    var rect = ribbonRef.current ? ribbonRef.current.getBoundingClientRect() : null;
    if (!rect) return;
    var cx = e.touches ? e.touches[0].clientX : e.clientX;
    var x  = Math.max(0, Math.min(1, (cx - rect.left) / rect.width));
    setRibbonX(x);
    var eng = synthRef.current;
    if (eng) eng.updatePitch(x);
  }, []);

  var handleFlip   = useCallback(function() { setFacingMode(function(f){return f==="environment"?"user":"environment";}); }, []);

  var loopingRef       = useRef(false);
  var loopCapturingRef = useRef(false);
  var loopPressTimeRef = useRef(0);   // timestamp of press start
  var MIN_LOOP_MS      = 200;         // minimum hold to count as record
  useEffect(function() { loopingRef.current = looping; }, [looping]);
  useEffect(function() { loopCapturingRef.current = loopCapturing; }, [loopCapturing]);

  var handleLoopStart = useCallback(function(e) {
    e.preventDefault();
    e.stopPropagation();
    var eng = synthRef.current;
    if (!eng || !eng.ctx) return;

    // If loop is playing, any press stops it
    if (loopingRef.current) {
      eng.stopLoop();
      setLooping(false);
      setLoopCapturing(false);
      clearInterval(loopVidTimerRef.current);
      loopFramesRef.current = [];
      var ov = loopOverlayRef.current;
      if (ov) ov.getContext("2d").clearRect(0,0,ov.width,ov.height);
      return;
    }

    // Record press time — don't start capturing yet, wait for MIN_LOOP_MS
    loopPressTimeRef.current = Date.now();
    // Ensure sound is on — loop needs audio running
    if (!eng.active) {
      if (!engReady) { eng.init(); setEngReady(true); }
      eng.setSoundOn(true);
      setSoundOn(true);
    }
    // Start engine capture immediately so we don't lose audio frames,
    // but only commit if hold was long enough
    loopFramesRef.current = [];
    eng.startLoopRecord();

    // Show blink only after short delay so quick taps never show it
    setTimeout(function() {
      if (loopCapturingRef.current === false && eng._loopRecording) {
        setLoopCapturing(true);
      }
    }, MIN_LOOP_MS);
  }, []);

  var handleLoopEnd = useCallback(function(e) {
    e.preventDefault();
    e.stopPropagation();
    var eng = synthRef.current;
    if (!eng) return;

    var held = Date.now() - loopPressTimeRef.current;

    // Too short — abort, don't loop
    if (held < MIN_LOOP_MS) {
      eng.stopLoop(); // cleans up proc
      setLoopCapturing(false);
      return;
    }

    if (!eng._loopRecording && !loopCapturingRef.current) return;

    var ok = eng.commitLoop();
    setLoopCapturing(false);

    if (!ok) {
      setLooping(false);
      return;
    }
    setLooping(true);

    // Start video loop
    var frames = loopFramesRef.current;
    if (frames.length > 0) {
      loopFrameIdxRef.current = 0;
      var ov = loopOverlayRef.current;
      clearInterval(loopVidTimerRef.current);
      loopVidTimerRef.current = setInterval(function() {
        if (!ov || !frames.length) return;
        ov.width  = frames[0].width;
        ov.height = frames[0].height;
        ov.getContext("2d").putImageData(frames[loopFrameIdxRef.current % frames.length], 0, 0);
        loopFrameIdxRef.current++;
      }, 100);
    }
  }, []);

  var handleCamToggle = useCallback(function() {
    setCamOn(function(on) {
      var next = !on;
      if (!next) {
        // Stop stream
        if (streamRef.current) streamRef.current.getTracks().forEach(function(t){t.stop();});
        streamRef.current = null;
        setCamReady(false);
      }
      return next;
    });
  }, []);
  var handleReload = useCallback(function() { window.location.reload(); }, []);

  var handleRecord = useCallback(function() {
    var eng = synthRef.current;
    if (recording) {
      // Stop and export WAV
      var wavBuf = eng ? eng.stopRecording() : null;
      if (wavBuf) {
        var blob = new Blob([wavBuf], { type: "audio/wav" });
        var url  = URL.createObjectURL(blob);
        var a    = document.createElement("a");
        a.href = url; a.download = "camsynth-" + Date.now() + ".wav"; a.click();
      }
      setRecording(false);
    } else {
      if (!eng || !eng.ctx) return;
      eng.startRecording();
      setRecording(true);
    }
  }, [recording]);

  var pr       = settings.pitchMax - settings.pitchMin;
  var midMidi  = Math.round(settings.pitchMin + ribbonX * pr);
  var noteName = NOTE_NAMES[midMidi % 12] + (Math.floor(midMidi/12)-1);
  var hueCSS   = frameData ? "hsl("+Math.round(frameData.hue*360)+",65%,52%)" : "#7fff6a";

  return el("div", { style:{ display:"flex", flexDirection:"column", width:"100%", height:"100dvh", background:"#0a0a0b", fontFamily:"'IBM Plex Mono','Courier New',monospace", color:"#c8c8b4", userSelect:"none", touchAction:"none", overflow:"hidden", maxWidth:480, margin:"0 auto" } },

    el("style", null, `
      @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@300;400;500&display=swap');
      *{box-sizing:border-box;}
      .cb{background:transparent;border:1px solid #222;color:#777;font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:.08em;padding:6px 10px;cursor:pointer;text-transform:uppercase;-webkit-tap-highlight-color:transparent;-webkit-touch-callout:none;user-select:none;-webkit-user-select:none;touch-action:manipulation;transition:border-color .15s,color .15s;}
      .sg{-webkit-touch-callout:none;user-select:none;-webkit-user-select:none;}
      .cb:active{background:#111;}
      .cb.on{border-color:#7fff6a;color:#7fff6a;}
      .cb.rec{border-color:#ff4444;color:#ff4444;background:rgba(255,68,68,.08);}
      .cb.dng{border-color:#ff4444;color:#ff4444;}
      @keyframes blink{0%,100%{opacity:1}50%{opacity:0.25}}
      .cb.blink{border-color:#ff4444;color:#ff4444;background:rgba(255,68,68,.08);animation:blink 0.6s infinite;}
      .sg{background:transparent;border:1px solid #1e1e1e;color:#444;font-family:'IBM Plex Mono',monospace;font-size:9px;padding:3px 7px;cursor:pointer;-webkit-tap-highlight-color:transparent;touch-action:manipulation;transition:all .1s;}
      .sg.sel{border-color:#7fff6a;color:#7fff6a;background:rgba(127,255,106,.06);}
      .sr{display:flex;align-items:center;justify-content:space-between;padding:5px 0;border-bottom:1px solid #141414;}
      .sr label{font-size:9px;letter-spacing:.1em;color:#444;text-transform:uppercase;}
      input[type=range]{-webkit-appearance:none;width:100%;height:22px;background:transparent;outline:none;cursor:pointer;margin:0;}
      input[type=range]::-webkit-slider-runnable-track{height:2px;background:#1e1e1e;border-radius:1px;margin-top:10px;}
      input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:20px;height:20px;background:#7fff6a;border-radius:50%;cursor:pointer;margin-top:-9px;}
      input[type=range]::-moz-range-track{height:2px;background:#1e1e1e;border-radius:1px;}
      input[type=range]::-moz-range-thumb{width:20px;height:20px;background:#7fff6a;border-radius:50%;border:none;cursor:pointer;}
    `),

    // Header
    el("div", { style:{ display:"flex", justifyContent:"space-between", alignItems:"center", padding:"10px 14px 6px", paddingTop:"max(env(safe-area-inset-top, 10px), 10px)", flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"baseline", gap:7 } },
        el("span", { style:{ fontSize:10, letterSpacing:"0.2em", color:"#7fff6a", textTransform:"uppercase" } }, "CamSynth"),
        el("span", { style:{ fontSize:8, color:"#888888", letterSpacing:"0.1em" } }, "v"+VERSION)
      ),
      el("div", { style:{ display:"flex", gap:4, alignItems:"center" } },
        frameData && el("div", { style:{ display:"flex", gap:5, alignItems:"center" } },
          el("div", { style:{ width:36, height:2, background:"#1a1a1a", borderRadius:1, overflow:"hidden" } },
            el("div", { style:{ height:"100%", width:(frameData.luma*100).toFixed(0)+"%", background:"#7fff6a", transition:"width 0.1s" } })
          ),
          el("div", { style:{ width:8, height:8, borderRadius:"50%", background:hueCSS, boxShadow:"0 0 5px "+hueCSS, flexShrink:0 } })
        ),
        camOn && el("button", { className:"cb", onClick:handleFlip }, "\u21c4"),
        el("button", { className:"cb", onClick:handleReload }, "\u21ba")
      )
    ),

    // Camera — fixed height, crops rather than expands
    el("div", { style:{ position:"relative", background:"#050505", overflow:"hidden", borderTop:"1px solid #141414", borderBottom:"1px solid #141414", flexShrink:0, height:"44vh" } },
      el("video", { ref:videoRef, playsInline:true, muted:true, autoPlay:true, controls:false, style:{ width:"100%", height:"100%", objectFit:"cover", display:"block", transform:facingMode==="user"?"scaleX(-1)":"none" } }),
      showScope && el("canvas", { ref:scopeRef, width:480, height:80, style:{ position:"absolute", bottom:0, left:0, width:"100%", height:60, pointerEvents:"none" } }),
      frameData && el("div", { style:{ position:"absolute", top:8, left:8, fontSize:8, color:"rgba(127,255,106,0.35)", letterSpacing:"0.1em", lineHeight:2, pointerEvents:"none" } },
        el("div",null,"LMA "+(frameData.luma*100).toFixed(1)),
        el("div",null,"HUE "+Math.round(frameData.hue*360)+"\xb0"),
        el("div",null,"SAT "+(frameData.saturation*100).toFixed(1)),
        el("div",null,"COM "+frameData.comX.toFixed(2)+"\xb7"+frameData.comY.toFixed(2))
      ),
      !camOn && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:8, background:"#050505" } },
        el("span", { style:{ color:"#2a2a2a", fontSize:10, letterSpacing:"0.2em" } }, "CAMERA OFF")
      ),
      camOn && !camReady && !camError && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:8 } },
        el("span", { style:{ color:"#2a2a2a", fontSize:10, letterSpacing:"0.2em" } }, "AWAITING CAMERA"),
        el("span", { style:{ color:"#1e1e1e", fontSize:8, letterSpacing:"0.1em" } }, "grant permission when prompted")
      ),
      camError && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:10 } },
        el("span", { style:{ color:"#ff4444", fontSize:10, letterSpacing:"0.15em" } }, camError),
        el("button", { className:"cb", onClick:handleReload, style:{ fontSize:9 } }, "\u21ba reload & retry")
      ),
      el("canvas", { ref:captureRef, style:{ display:"none" } }),
      el("canvas", { ref:loopOverlayRef, style:{ position:"absolute", inset:0, width:"100%", height:"100%", pointerEvents:"none", display: looping ? "block" : "none" } })
    ),

    // Pitch Ribbon
    el("div", { style:{ flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"center", padding:"3px 14px 2px", gap:8 } },
        el("span", { style:{ fontSize:8, color:"#2a2a2a", letterSpacing:"0.1em" } }, "PITCH"),
        el("span", { style:{ fontSize:13, color:"#7fff6a", letterSpacing:"0.04em", minWidth:34 } }, noteName),
        el("span", { style:{ fontSize:8, color:"#1a1a1a", marginLeft:"auto" } }, settings.quantize ? settings.scale : "free")
      ),
      el("div", {
        ref:ribbonRef,
        onMouseDown:handleRibbon, onMouseMove:function(e){if(e.buttons)handleRibbon(e);},
        onTouchStart:handleRibbon, onTouchMove:handleRibbon,
        style:{ height:44, background:"linear-gradient(90deg,#070c07 0%,#101810 50%,#070c07 100%)", borderTop:"1px solid #141c14", borderBottom:"1px solid #141c14", position:"relative", cursor:"crosshair" }
      },
        Array.from({ length: pr+1 }, function(_,i) {
          return el("div", { key:i, style:{ position:"absolute", left:((i/pr)*100)+"%", top:i%12===0?0:"65%", width:1, height:i%12===0?"100%":"35%", background:i%12===0?"#1c261c":"#141c14" } });
        }),
        el("div", { style:{ position:"absolute", left:(ribbonX*100)+"%", top:0, bottom:0, width:2, background:"#7fff6a", boxShadow:"0 0 10px #7fff6a", transform:"translateX(-50%)", pointerEvents:"none" } })
      )
    ),

    // Controls
    el("div", { style:{ display:"flex", gap:5, padding:"7px 14px", flexShrink:0 } },
      el("button", { className:cx("cb", soundOn&&"on"), onClick:handleSound, style:{ flex:2, fontSize:11, padding:"10px 0", letterSpacing:"0.1em" } }, soundOn ? "\u25fc ON" : "\u25b6 OFF"),
      el("button", {
        className:cx("cb", loopCapturing&&"blink", looping&&"on"),
        onMouseDown:handleLoopStart, onMouseUp:handleLoopEnd,
        onTouchStart:handleLoopStart, onTouchEnd:handleLoopEnd,
        style:{ flex:1, position:"relative", touchAction:"none" }
      }, loopCapturing ? "\u25cf LOOP" : looping ? "\u21ba LOOP" : "\u25cb LOOP"),
      el("button", { className:cx("cb", recording&&"rec"), onClick:handleRecord, style:{ flex:1 } }, recording ? "\u25cf REC" : "\u25cb REC"),
      el("button", { className:cx("cb", camOn&&"on"), onClick:handleCamToggle, style:{ flex:1 } }, "\u25a3 CAM"),
      el("button", { className:cx("cb", showScope&&"on"), onClick:function(){setShowScope(function(s){return !s;});}, style:{ flex:1 } }, "\u223f"),
      el("button", { className:cx("cb", showSettings&&"on"), onClick:function(){setShowSettings(function(s){return !s;});}, style:{ flex:1 } }, "\u2699")
    ),

    // Settings drawer
    showSettings && el("div", { style:{ padding:"8px 14px 14px", borderTop:"1px solid #141414", background:"#0c0c0d", overflowY:"auto", flexShrink:0, maxHeight:"38vh" } },

      el("div", { className:"sr" },
        el("label",null,"Voices"),
        el("div", { style:{display:"flex",gap:2} },
          VOICE_OPTIONS.map(function(v){ return el("button",{key:v,className:cx("sg",settings.voices===v&&"sel"),onClick:function(){setSetting("voices",v);}},v); })
        )
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:3} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label",null,"Detune"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},settings.detune+" ct")
        ),
        el("input",{type:"range",min:0,max:50,value:settings.detune,onChange:function(e){var v=+e.target.value; setSetting("detune",v); var eng=synthRef.current; if(eng) eng.updateDetune(v);}})
      ),

      el("div", { className:"sr" },
        el("label",null,"Scale"),
        el("div", { style:{display:"flex",gap:2,alignItems:"center"} },
          el("span", { style:{fontSize:9,color:"#7fff6a",marginRight:4} }, settings.quantize ? settings.scale : "off"),
          el("button", {
            className:cx("sg", settings.showScales&&"sel"),
            onClick:function(){ setSetting("showScales", !settings.showScales); }
          }, settings.showScales ? "▲" : "▼")
        )
      ),

      settings.showScales && el("div", { style:{paddingBottom:4,borderBottom:"1px solid #141414"} },
        el("div", { style:{display:"flex",flexWrap:"wrap",gap:2,paddingTop:4} },
          el("button", {
            className:cx("sg", !settings.quantize&&"sel"),
            onClick:function(){ setSetting("quantize",false); setSetting("showScales",false); }
          }, "off"),
          SCALE_NAMES.map(function(s){
            return el("button",{
              key:s,
              className:cx("sg", settings.quantize&&settings.scale===s&&"sel"),
              onClick:function(){ setSetting("scale",s); setSetting("quantize",true); setSetting("showScales",false); }
            }, s);
          })
        )
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:3} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label",null,"Pitch range"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}}, NOTE_NAMES[settings.pitchMin%12]+(Math.floor(settings.pitchMin/12)-1)+" \u2192 "+NOTE_NAMES[settings.pitchMax%12]+(Math.floor(settings.pitchMax/12)-1))
        ),
        el("div", { style:{display:"flex",gap:8,width:"100%"} },
          el("input",{type:"range",min:24,max:60,value:settings.pitchMin,onChange:function(e){setSetting("pitchMin",Math.min(+e.target.value,settings.pitchMax-4));}}),
          el("input",{type:"range",min:48,max:84,value:settings.pitchMax,onChange:function(e){setSetting("pitchMax",Math.max(+e.target.value,settings.pitchMin+4));}})
        )
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:3} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label",null,"Reverb mix"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},Math.round(settings.reverbMix*100)+"%")
        ),
        el("input",{type:"range",min:0,max:100,value:Math.round(settings.reverbMix*100),onChange:function(e){setSetting("reverbMix",e.target.value/100);}})
      ),



      el("div", { style:{paddingTop:10,textAlign:"right"} },
        el("span",{style:{fontSize:8,color:"#1e1e1e",letterSpacing:"0.15em"}},"v"+VERSION)
      )
    )
  );
}

ReactDOM.createRoot(document.getElementById("root")).render(React.createElement(App));
