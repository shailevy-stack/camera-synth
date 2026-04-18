// Camera Synth — v3.0.0
var VERSION = "3.0.0";

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
var ANALYSIS_RES  = 256;
var NOTE_NAMES    = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];

// Just intonation intervals for RGB oscillators
var INTERVALS = {
  "unison": 1,
  "octave": 2,
  "fifth":  1.5,
  "maj3":   1.25,
  "min3":   1.2,
};
var INTERVAL_NAMES = Object.keys(INTERVALS);

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

// ── Square wave coefficients (just intonation odd harmonics) ─────────────────
function makeSquareCoeffs(size) {
  var imag = new Float32Array(size);
  var real = new Float32Array(size);
  for (var n = 1; n < size; n += 2) {
    imag[n] = 1 / n; // odd harmonics: 1, 1/3, 1/5, 1/7...
  }
  return { real: real, imag: imag };
}

// ── Shared reverb IR (pre-built before gesture) ───────────────────────────────
var REVERB_IR = (function() {
  var sr  = 44100;
  var len = Math.floor(sr * 3.5); // longer decay
  var L   = new Float32Array(len);
  var R   = new Float32Array(len);

  // Early reflections — sparse spikes at prime-ish intervals
  // give the reverb a sense of space before the tail
  var erTimes = [0.011, 0.017, 0.023, 0.031, 0.041, 0.057, 0.073, 0.089];
  var erGains  = [0.7,   0.5,   0.6,   0.4,   0.45,  0.35,  0.3,   0.25];
  for (var e = 0; e < erTimes.length; e++) {
    var idx = Math.floor(erTimes[e] * sr);
    if (idx < len) {
      L[idx] += erGains[e] * (e % 2 === 0 ? 1 : -1);
      // Offset R slightly for stereo width
      var ridx = Math.min(len-1, idx + Math.floor(sr * 0.0007 * (e+1)));
      R[ridx] += erGains[e] * (e % 2 === 0 ? -1 : 1);
    }
  }

  // Diffuse tail — two independent noise streams for L/R decorrelation
  // Use a slower exponential decay with a pre-delay before the tail
  var preDelay = Math.floor(sr * 0.02); // 20ms pre-delay
  for (var i = preDelay; i < len; i++) {
    var t     = (i - preDelay) / (len - preDelay);
    var decay = Math.pow(1 - t, 1.8) * Math.exp(-t * 2.5);
    // Independent random seeds per channel = decorrelated stereo
    L[i] += (Math.random() * 2 - 1) * decay;
    R[i] += (Math.random() * 2 - 1) * decay;
  }

  // Apply a gentle lowpass to soften the metallic high-freq content
  // Simple one-pole IIR: y[n] = 0.85*y[n-1] + 0.15*x[n]
  var lpL = 0, lpR = 0;
  for (var i = 0; i < len; i++) {
    lpL = 0.85 * lpL + 0.15 * L[i]; L[i] = lpL;
    lpR = 0.85 * lpR + 0.15 * R[i]; R[i] = lpR;
  }

  return { L: L, R: R, len: len };
}());

var SQUARE_COEFFS = makeSquareCoeffs(512);

// ══════════════════════════════════════════════════════════════════════════════
// ENGINE 1 — CamSynth_1
// Image-scanned wavetable, single oscillator bank, comb + lowpass + LFO
// ══════════════════════════════════════════════════════════════════════════════
function makeEngine1() {
  var eng = {
    ctx: null, voices: [],
    combFilters: [], lowpassNode: null,
    reverbNode: null, reverbGain: null,
    dryGain: null, masterGain: null,
    limiterNode: null, analyserNode: null,
    active: false, currentPitchMidi: 60,
    wavetableData:    new Float32Array(ANALYSIS_RES),
    morphedWavetable: new Float32Array(ANALYSIS_RES),
    morphAlpha: 0.35,
    currentLuma: 0.5,
    _lfoNode: null, _lfoGain: null,
    _prevHue: 0, _prevHueTime: 0,
    _loopProc: null, _loopChunks: [], _loopNode: null,
    _loopGain: null, _loopRecording: false,
    _recorder: null, _recChunks: null,
    settings: {
      voices: 1, detune: 12,
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72, reverbMix: 0.3, fps: 10,
      showScales: false,
    },
  };

  eng.init = function() {
    if (eng.ctx) return;
    try {
      var AC  = window.AudioContext || window.webkitAudioContext;
      eng.ctx = new AC();
      var sr  = eng.ctx.sampleRate;
      var buf = eng.ctx.createBuffer(2, REVERB_IR.len, sr);
      buf.getChannelData(0).set(REVERB_IR.L);
      buf.getChannelData(1).set(REVERB_IR.R);
      eng.reverbNode = eng.ctx.createConvolver();
      eng.reverbNode.buffer = buf;

      var N = 8;
      eng.combFilters = [];
      for (var ci = 0; ci < N; ci++) {
        var f = eng.ctx.createBiquadFilter();
        f.type = "peaking";
        f.frequency.value = 200 * (ci + 1);
        f.Q.value = 3;
        f.gain.value = 0;
        eng.combFilters.push(f);
      }
      for (var ci = 0; ci < N - 1; ci++) eng.combFilters[ci].connect(eng.combFilters[ci + 1]);

      eng.lowpassNode = eng.ctx.createBiquadFilter();
      eng.lowpassNode.type = "lowpass";
      eng.lowpassNode.frequency.value = 2000;
      eng.lowpassNode.Q.value = 0.7;
      eng.combFilters[N - 1].connect(eng.lowpassNode);

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

      eng.lowpassNode.connect(eng.dryGain);
      eng.lowpassNode.connect(eng.reverbNode);
      eng.reverbNode.connect(eng.reverbGain);
      eng.dryGain.connect(eng.masterGain);
      eng.reverbGain.connect(eng.masterGain);
      eng.masterGain.connect(eng.limiterNode);
      eng.limiterNode.connect(eng.analyserNode);
      eng.analyserNode.connect(eng.ctx.destination);

      eng.spawnVoices();
    } catch(e) { console.error("[E1] init failed", e); }
  };

  eng.makeWavetable = function(data) {
    var size = 1024;
    var real = new Float32Array(size / 2);
    var imag = new Float32Array(size / 2);
    var lim  = Math.min(data.length, size / 2 - 1);
    for (var i = 0; i < lim; i++) imag[i + 1] = data[i];
    return eng.ctx.createPeriodicWave(real, imag, { disableNormalization: false });
  };

  eng.spawnVoices = function() {
    for (var i = 0; i < eng.voices.length; i++) {
      try { eng.voices[i].osc.stop(); eng.voices[i].osc.disconnect(); eng.voices[i].gain.disconnect(); if (eng.voices[i].panner) eng.voices[i].panner.disconnect(); } catch(e) {}
    }
    eng.voices = [];
    var n = eng.settings.voices;
    for (var i = 0; i < n; i++) {
      var osc = eng.ctx.createOscillator();
      osc.type = "sine";
      osc.detune.value    = n === 1 ? 0 : ((i / (n - 1)) - 0.5) * eng.settings.detune * 2;
      osc.frequency.value = midiToHz(eng.currentPitchMidi);
      var gain = eng.ctx.createGain();
      gain.gain.value = 0.55 / n;
      var panner = eng.ctx.createStereoPanner();
      panner.pan.value = n === 1 ? 0 : ((i / (n - 1)) * 2 - 1);
      osc.connect(gain);
      gain.connect(panner);
      panner.connect(eng.combFilters[0]);
      osc.start();
      eng.voices.push({ osc: osc, gain: gain, panner: panner });
    }
    if (n === 1) {
      var delay = eng.ctx.createDelay(0.05);
      delay.delayTime.value = 0.018;
      var dg = eng.ctx.createGain(); dg.gain.value = 0.6;
      var dp = eng.ctx.createStereoPanner(); dp.pan.value = 0.8;
      eng.voices[0].panner.pan.value = -0.5;
      eng.voices[0].gain.connect(delay);
      delay.connect(dg); dg.connect(dp); dp.connect(eng.combFilters[0]);
      eng.voices[0].delay = delay; eng.voices[0].dg = dg; eng.voices[0].dp = dp;
    }
  };

  eng.updateDetune = function(d) {
    eng.settings.detune = d;
    if (!eng.ctx) return;
    var n = eng.voices.length, t = eng.ctx.currentTime;
    for (var i = 0; i < n; i++) {
      eng.voices[i].osc.detune.setTargetAtTime(n===1?0:((i/(n-1))-0.5)*d*2, t, 0.08);
    }
  };

  eng.updateWavetable = function(data, luma) {
    eng.wavetableData = data;
    if (!eng.ctx) return;
    var lumaGate = (luma !== undefined ? luma : eng.currentLuma);
    lumaGate = lumaGate * lumaGate;
    var alpha = eng.morphAlpha;
    var hasData = false;
    for (var k = 0; k < data.length; k++) {
      eng.morphedWavetable[k] = eng.morphedWavetable[k] * (1 - alpha) + data[k] * alpha;
      if (data[k] !== 0) hasData = true;
    }
    if (!hasData && lumaGate <= 0.01) return;
    var blended = new Float32Array(eng.morphedWavetable.length);
    for (var k = 0; k < blended.length; k++) blended[k] = eng.morphedWavetable[k] * lumaGate;
    try {
      var wave = eng.makeWavetable(blended);
      for (var i = 0; i < eng.voices.length; i++) {
        try { eng.voices[i].osc.setPeriodicWave(wave); } catch(e) {}
      }
    } catch(e) {}
  };

  eng.updatePitch = function(rx) {
    if (!eng.ctx) return;
    var s = eng.settings;
    var midi = s.pitchMin + rx * (s.pitchMax - s.pitchMin);
    if (s.quantize) midi = quantizePitch(Math.round(midi), s.scale, s.rootNote);
    eng.currentPitchMidi = midi;
    var hz = midiToHz(midi), t = eng.ctx.currentTime;
    for (var i = 0; i < eng.voices.length; i++) eng.voices[i].osc.frequency.setTargetAtTime(hz, t, 0.05);
  };

  eng.initLFO = function() {
    if (!eng.ctx || eng._lfoNode) return;
    eng._lfoNode = eng.ctx.createOscillator();
    eng._lfoNode.type = "sine";
    eng._lfoNode.frequency.value = 0.2;
    eng._lfoGain = eng.ctx.createGain();
    eng._lfoGain.gain.value = 0;
    eng._lfoNode.connect(eng._lfoGain);
    eng._lfoGain.connect(eng.lowpassNode.frequency);
    eng._lfoNode.start();
  };

  eng.updateFromCamera = function(luma, hue, chromaContrast, slices) {
    if (!eng.ctx || !eng.combFilters.length) return;
    var t = eng.ctx.currentTime;
    if (!eng._lfoNode) eng.initLFO();
    var fundamental = 80 + luma * 320;
    for (var i = 0; i < eng.combFilters.length; i++) {
      var sliceLum = slices ? slices[i] : luma;
      eng.combFilters[i].frequency.setTargetAtTime(fundamental * (i + 1), t, 0.3);
      eng.combFilters[i].gain.setTargetAtTime((sliceLum - 0.5) * 20, t, 0.3);
      eng.combFilters[i].Q.setTargetAtTime(1.5 + chromaContrast * 8, t, 0.3);
    }
    // Lowpass controlled by filter ribbon
    var now = eng.ctx.currentTime;
    var dt  = now - eng._prevHueTime;
    var hueDelta = 0;
    if (dt > 0 && dt < 2) {
      hueDelta = Math.abs(hue - eng._prevHue);
      if (hueDelta > 0.5) hueDelta = 1 - hueDelta;
      hueDelta = hueDelta / dt;
    }
    eng._prevHue = hue; eng._prevHueTime = now;
    eng._lfoNode.frequency.setTargetAtTime(0.05 + Math.min(hueDelta * 4, 1) * 1.95, t, 0.5);
    // Floor ensures LFO always audible; luma scales depth with scene brightness
    eng._lfoGain.gain.setTargetAtTime((100 + chromaContrast * 500) * luma, t, 0.3);
  };

  eng.setSoundOn = function(on) {
    if (!eng.ctx) return;
    eng.ctx.resume();
    eng.masterGain.gain.cancelScheduledValues(0);
    eng.masterGain.gain.value = on ? 0.7 : 0;
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

  eng.startRecording = function() {
    if (!eng.ctx) return;
    var chunks = [], proc = eng.ctx.createScriptProcessor(4096, 2, 2);
    proc.onaudioprocess = function(e) {
      chunks.push({ L: new Float32Array(e.inputBuffer.getChannelData(0)), R: new Float32Array(e.inputBuffer.getChannelData(1)) });
    };
    eng.limiterNode.connect(proc); proc.connect(eng.ctx.destination);
    eng._recorder = proc; eng._recChunks = chunks;
  };

  eng.stopRecording = function() {
    if (!eng._recorder) return null;
    try { eng.limiterNode.disconnect(eng._recorder); eng._recorder.disconnect(); } catch(e) {}
    var chunks = eng._recChunks; eng._recorder = null; eng._recChunks = null;
    var sr = eng.ctx.sampleRate;
    var nFrames = chunks.reduce(function(s,c){return s+c.L.length;},0);
    var buf = new ArrayBuffer(44 + nFrames * 4);
    var view = new DataView(buf);
    function str(o,s){for(var i=0;i<s.length;i++)view.setUint8(o+i,s.charCodeAt(i));}
    function u32(o,v){view.setUint32(o,v,true);}
    function u16(o,v){view.setUint16(o,v,true);}
    str(0,"RIFF");u32(4,36+nFrames*4);str(8,"WAVE");
    str(12,"fmt ");u32(16,16);u16(20,1);u16(22,2);
    u32(24,sr);u32(28,sr*4);u16(32,4);u16(34,16);
    str(36,"data");u32(40,nFrames*4);
    var off=44;
    for(var ci=0;ci<chunks.length;ci++){
      var L=chunks[ci].L,R=chunks[ci].R;
      for(var fi=0;fi<L.length;fi++){
        var ls=Math.max(-1,Math.min(1,L[fi])),rs=Math.max(-1,Math.min(1,R[fi]));
        view.setInt16(off,ls<0?ls*0x8000:ls*0x7FFF,true);off+=2;
        view.setInt16(off,rs<0?rs*0x8000:rs*0x7FFF,true);off+=2;
      }
    }
    return buf;
  };

  eng.startLoopRecord = function() {
    if (!eng.ctx) return;
    eng.stopLoop();
    eng._loopRecording = true; eng._loopChunks = [];
    var maxSamples = eng.ctx.sampleRate * 10, captured = 0;
    var proc = eng.ctx.createScriptProcessor(4096, 2, 2);
    proc.onaudioprocess = function(ev) {
      if (!eng._loopRecording || captured >= maxSamples) return;
      eng._loopChunks.push({ L: new Float32Array(ev.inputBuffer.getChannelData(0)), R: new Float32Array(ev.inputBuffer.getChannelData(1)) });
      captured += 4096;
    };
    eng.limiterNode.connect(proc); proc.connect(eng.ctx.destination);
    eng._loopProc = proc;
  };

  eng.commitLoop = function() {
    eng._loopRecording = false;
    if (eng._loopProc) { try { eng.limiterNode.disconnect(eng._loopProc); eng._loopProc.disconnect(); } catch(e) {} eng._loopProc = null; }
    var chunks = eng._loopChunks;
    if (!chunks.length) return false;
    var sr = eng.ctx.sampleRate;
    var nFrames = chunks.reduce(function(s,c){return s+c.L.length;},0);
    if (nFrames < 4096) return false;
    var buf = eng.ctx.createBuffer(2, nFrames, sr);
    var oL = buf.getChannelData(0), oR = buf.getChannelData(1), off = 0;
    for (var i = 0; i < chunks.length; i++) { oL.set(chunks[i].L,off); oR.set(chunks[i].R,off); off+=chunks[i].L.length; }
    var fl = Math.min(Math.floor(sr*0.008), Math.floor(nFrames/4));
    for (var j = 0; j < fl; j++) { var t=j/fl; oL[j]*=t;oR[j]*=t; oL[nFrames-fl+j]*=(1-t);oR[nFrames-fl+j]*=(1-t); }
    eng.masterGain.gain.value = 0;
    var lg = eng.ctx.createGain(); lg.gain.value = 0.85; lg.connect(eng.limiterNode);
    var src = eng.ctx.createBufferSource(); src.buffer=buf; src.loop=true; src.connect(lg); src.start(0);
    eng._loopNode = src; eng._loopGain = lg;
    return true;
  };

  eng.stopLoop = function() {
    eng._loopRecording = false;
    if (eng._loopProc) { try{eng.limiterNode.disconnect(eng._loopProc);eng._loopProc.disconnect();}catch(e){} eng._loopProc=null; }
    if (eng._loopNode) { try{eng._loopNode.stop();eng._loopNode.disconnect();}catch(e){} eng._loopNode=null; }
    if (eng._loopGain) { try{eng._loopGain.disconnect();}catch(e){} eng._loopGain=null; }
    eng._loopChunks = [];
    if (eng.active) eng.masterGain.gain.value = 0.7;
  };

  eng.isLooping = function() { return !!eng._loopNode; };

  eng.destroy = function() {
    eng.panic();
    if (eng._lfoNode) { try{eng._lfoNode.stop();}catch(e){} }
    for (var i=0;i<eng.voices.length;i++) { try{eng.voices[i].osc.stop();}catch(e){} }
    for (var i=0;i<eng.combFilters.length;i++) { try{eng.combFilters[i].disconnect();}catch(e){} }
    if (eng.ctx) eng.ctx.close();
  };

  return eng;
}

// ══════════════════════════════════════════════════════════════════════════════
// ENGINE 2 — CamSynth_2
// R/G/B oscillators, sine↔square morph per channel,
// just intonation intervals, per-channel Haas stereo width
// Same comb + lowpass + LFO downstream
// ══════════════════════════════════════════════════════════════════════════════
function makeEngine2() {
  var eng = {
    ctx: null,
    oscR: null, oscG: null, oscB: null,
    combFilters: [], lowpassNode: null,
    reverbNode: null, reverbGain: null,
    dryGain: null, masterGain: null,
    limiterNode: null, analyserNode: null,
    active: false, currentPitchMidi: 60,
    _lfoNode: null, _lfoGain: null,
    _prevHue: 0, _prevHueTime: 0,
    _loopProc: null, _loopChunks: [], _loopNode: null,
    _loopGain: null, _loopRecording: false,
    _recorder: null, _recChunks: null,
    // Adaptive normalization — slow-tracked min/max per relative channel
    _normR: { min: -0.1, max: 0.1 },
    _normG: { min: -0.1, max: 0.1 },
    _normB: { min: -0.1, max: 0.1 },
    _normAlpha: 0.02,      // how fast min/max tracks (per frame)
    _normMinSpread: 0.04,  // minimum spread to avoid noise amplification
    settings: {
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72, reverbMix: 0.3, fps: 10,
      showScales: false,
      intervalR: "octave",   // max interval each osc can sweep
      intervalG: "fifth",
      intervalB: "maj3",
      glide: 200,            // portamento ms (0 = instant, 2000 = slow)
    },
  };

  eng.init = function() {
    if (eng.ctx) return;
    try {
      var AC = window.AudioContext || window.webkitAudioContext;
      eng.ctx = new AC();
      var sr  = eng.ctx.sampleRate;
      var rbuf = eng.ctx.createBuffer(2, REVERB_IR.len, sr);
      rbuf.getChannelData(0).set(REVERB_IR.L);
      rbuf.getChannelData(1).set(REVERB_IR.R);
      eng.reverbNode = eng.ctx.createConvolver();
      eng.reverbNode.buffer = rbuf;

      // Comb + lowpass (identical to engine 1)
      var N = 8; eng.combFilters = [];
      for (var ci = 0; ci < N; ci++) {
        var f = eng.ctx.createBiquadFilter();
        f.type = "peaking"; f.frequency.value = 200*(ci+1); f.Q.value = 3; f.gain.value = 0;
        eng.combFilters.push(f);
      }
      for (var ci = 0; ci < N-1; ci++) eng.combFilters[ci].connect(eng.combFilters[ci+1]);

      eng.lowpassNode = eng.ctx.createBiquadFilter();
      eng.lowpassNode.type = "lowpass";
      eng.lowpassNode.frequency.value = 2000;
      eng.lowpassNode.Q.value = 0.7;
      eng.combFilters[N-1].connect(eng.lowpassNode);

      eng.dryGain = eng.ctx.createGain(); eng.dryGain.gain.value = 1 - eng.settings.reverbMix;
      eng.reverbGain = eng.ctx.createGain(); eng.reverbGain.gain.value = eng.settings.reverbMix;
      eng.masterGain = eng.ctx.createGain(); eng.masterGain.gain.value = 0;

      eng.limiterNode = eng.ctx.createDynamicsCompressor();
      eng.limiterNode.threshold.value = -3; eng.limiterNode.knee.value = 0;
      eng.limiterNode.ratio.value = 20; eng.limiterNode.attack.value = 0.001; eng.limiterNode.release.value = 0.1;

      eng.analyserNode = eng.ctx.createAnalyser(); eng.analyserNode.fftSize = 1024;

      eng.lowpassNode.connect(eng.dryGain);
      eng.lowpassNode.connect(eng.reverbNode);
      eng.reverbNode.connect(eng.reverbGain);
      eng.dryGain.connect(eng.masterGain);
      eng.reverbGain.connect(eng.masterGain);
      eng.masterGain.connect(eng.limiterNode);
      eng.limiterNode.connect(eng.analyserNode);
      eng.analyserNode.connect(eng.ctx.destination);

      eng.spawnOscillators();
    } catch(e) { console.error("[E2] init failed", e); }
  };

  // Build a PeriodicWave that morphs between sine and square
  // morph 0 = pure sine, morph 1 = full square
  eng.makeMorphWave = function(morph) {
    var size = 512;
    var real = new Float32Array(size / 2);
    var imag = new Float32Array(size / 2);
    // Sine: only fundamental
    // Square: odd harmonics 1/n
    // Interpolate each harmonic coefficient
    imag[1] = 1.0; // fundamental always present
    for (var n = 3; n < size/2; n += 2) {
      imag[n] = morph * (1 / n); // blend toward square
    }
    return eng.ctx.createPeriodicWave(real, imag, { disableNormalization: false });
  };

  // Create one RGB oscillator voice
  // Returns { osc, morphGain, haasDelay, haasPan, directPan, gainNode }
  eng.makeOscVoice = function(freq, panPos) {
    var osc = eng.ctx.createOscillator();
    osc.frequency.value = freq;
    osc.setPeriodicWave(eng.makeMorphWave(0)); // start as sine

    var gainNode = eng.ctx.createGain();
    gainNode.gain.value = 0.4; // each channel at 0.4, three sum to ~1.2 — limiter handles it

    // Direct signal — panned to one side
    var directPan = eng.ctx.createStereoPanner();
    directPan.pan.value = panPos * -0.4; // slight pan opposite to haas

    // Haas delay — creates stereo width proportional to channel brightness
    var haasDelay = eng.ctx.createDelay(0.05);
    haasDelay.delayTime.value = 0.015;
    var haasGain = eng.ctx.createGain(); haasGain.gain.value = 0; // start narrow
    var haasPan  = eng.ctx.createStereoPanner();
    haasPan.pan.value = panPos * 0.8; // haas copy panned to opposite side

    osc.connect(gainNode);
    gainNode.connect(directPan);
    directPan.connect(eng.combFilters[0]);
    gainNode.connect(haasDelay);
    haasDelay.connect(haasGain);
    haasGain.connect(haasPan);
    haasPan.connect(eng.combFilters[0]);

    osc.start();
    return { osc: osc, gainNode: gainNode, directPan: directPan, haasDelay: haasDelay, haasGain: haasGain, haasPan: haasPan };
  };

  eng.spawnOscillators = function() {
    // Destroy old
    ['oscR','oscG','oscB'].forEach(function(k) {
      var v = eng[k];
      if (!v) return;
      try { v.osc.stop(); v.osc.disconnect(); v.gainNode.disconnect(); v.directPan.disconnect(); v.haasDelay.disconnect(); v.haasGain.disconnect(); v.haasPan.disconnect(); } catch(e) {}
      eng[k] = null;
    });

    var baseHz = midiToHz(eng.currentPitchMidi);
    var rHz = baseHz * INTERVALS[eng.settings.intervalR];
    var gHz = baseHz * INTERVALS[eng.settings.intervalG];
    var bHz = baseHz * INTERVALS[eng.settings.intervalB];

    // R = left, G = center, B = right
    eng.oscR = eng.makeOscVoice(rHz,  1); // pan direction: 1 = R-panned
    eng.oscG = eng.makeOscVoice(gHz,  0); // center
    eng.oscB = eng.makeOscVoice(bHz, -1); // pan direction: -1 = L-panned
  };

  // Adaptive normalizer — tracks slow min/max and remaps to 0..1
  eng.adaptNorm = function(norm, val) {
    var alpha = eng._normAlpha;
    // Expand min/max slowly toward observed values
    if (val < norm.min) norm.min = norm.min * (1-alpha) + val * alpha * 4; // faster on new extremes
    else                norm.min = norm.min * (1-alpha*0.1) + val * alpha * 0.1; // slow drift up
    if (val > norm.max) norm.max = norm.max * (1-alpha) + val * alpha * 4;
    else                norm.max = norm.max * (1-alpha*0.1) + val * alpha * 0.1; // slow drift down
    // Enforce minimum spread
    var spread = norm.max - norm.min;
    if (spread < eng._normMinSpread) {
      var mid = (norm.max + norm.min) / 2;
      norm.min = mid - eng._normMinSpread / 2;
      norm.max = mid + eng._normMinSpread / 2;
    }
    return Math.max(0, Math.min(1, (val - norm.min) / (norm.max - norm.min)));
  };

  eng.updatePitch = function(rx) {
    if (!eng.ctx) return;
    var s = eng.settings;
    var midi = s.pitchMin + rx * (s.pitchMax - s.pitchMin);
    if (s.quantize) midi = quantizePitch(Math.round(midi), s.scale, s.rootNote);
    eng.currentPitchMidi = midi;
    // Recalculate all oscillator frequencies from current color state
    eng._applyOscFrequencies();
  };

  // Apply frequencies to all three oscillators using current pitch + color offsets
  eng._colorNorm = { r: 0.5, g: 0.5, b: 0.5 }; // last known normalized color
  eng._applyOscFrequencies = function() {
    if (!eng.ctx) return;
    var s       = eng.settings;
    var baseHz  = midiToHz(eng.currentPitchMidi);
    var t       = eng.ctx.currentTime;
    var glideTC = s.glide / 1000 / 3; // convert ms to time constant

    var cn = eng._colorNorm;

    // Each oscillator sweeps from baseHz to baseHz*interval, driven by its color norm
    var rRatio = 1 + (INTERVALS[s.intervalR] - 1) * cn.r;
    var gRatio = 1 + (INTERVALS[s.intervalG] - 1) * cn.g;
    var bRatio = 1 + (INTERVALS[s.intervalB] - 1) * cn.b;

    // Oscillator intervals are free — scale only applies to ribbon pitch

    var glide = glideTC > 0.001 ? glideTC : 0.01;
    if (eng.oscR) eng.oscR.osc.frequency.setTargetAtTime(baseHz * rRatio, t, glide);
    if (eng.oscG) eng.oscG.osc.frequency.setTargetAtTime(baseHz * gRatio, t, glide);
    if (eng.oscB) eng.oscB.osc.frequency.setTargetAtTime(baseHz * bRatio, t, glide);
  };

  eng.updateIntervals = function() {
    eng._applyOscFrequencies();
  };

  eng.updateFromRGB = function(avgR, avgG, avgB, luma) {
    if (!eng.ctx) return;
    var t = eng.ctx.currentTime;

    // Relative color — deviation from luma (camera-normalized mean)
    var relR = avgR - luma;
    var relG = avgG - luma;
    var relB = avgB - luma;

    // Adaptive normalization — remap observed range to 0..1
    var normR = eng.adaptNorm(eng._normR, relR);
    var normG = eng.adaptNorm(eng._normG, relG);
    var normB = eng.adaptNorm(eng._normB, relB);

    // Store for pitch calculation
    eng._colorNorm.r = normR;
    eng._colorNorm.g = normG;
    eng._colorNorm.b = normB;

    // Apply pitch with glide
    eng._applyOscFrequencies();

    // Morph: channel absolute brightness → sine↔square (squared curve)
    // 4th power curve — scene must be very bright to push toward square
    var rMorph = avgR * avgR * avgR * avgR;
    var gMorph = avgG * avgG * avgG * avgG;
    var bMorph = avgB * avgB * avgB * avgB;
    if (eng.oscR) { try { eng.oscR.osc.setPeriodicWave(eng.makeMorphWave(rMorph)); } catch(e) {} }
    if (eng.oscG) { try { eng.oscG.osc.setPeriodicWave(eng.makeMorphWave(gMorph)); } catch(e) {} }
    if (eng.oscB) { try { eng.oscB.osc.setPeriodicWave(eng.makeMorphWave(bMorph)); } catch(e) {} }

    // Haas stereo width: relative color magnitude → width
    // More colorful channel = wider stereo
    var rWidth = Math.min(1, Math.abs(relR) * 8);
    var gWidth = Math.min(1, Math.abs(relG) * 8);
    var bWidth = Math.min(1, Math.abs(relB) * 8);
    if (eng.oscR && eng.oscR.haasGain) eng.oscR.haasGain.gain.setTargetAtTime(rWidth * 0.7, t, 0.2);
    if (eng.oscG && eng.oscG.haasGain) eng.oscG.haasGain.gain.setTargetAtTime(gWidth * 0.7, t, 0.2);
    if (eng.oscB && eng.oscB.haasGain) eng.oscB.haasGain.gain.setTargetAtTime(bWidth * 0.7, t, 0.2);
  };

  eng.initLFO = function() {
    if (!eng.ctx || eng._lfoNode) return;
    eng._lfoNode = eng.ctx.createOscillator();
    eng._lfoNode.type = "sine";
    eng._lfoNode.frequency.value = 0.2;
    eng._lfoGain = eng.ctx.createGain();
    eng._lfoGain.gain.value = 0;
    eng._lfoNode.connect(eng._lfoGain);
    eng._lfoGain.connect(eng.lowpassNode.frequency);
    eng._lfoNode.start();
  };

  eng.updateFromCamera = function(luma, hue, chromaContrast, slices, r, g, b) {
    if (!eng.ctx || !eng.combFilters.length) return;
    var t = eng.ctx.currentTime;
    if (!eng._lfoNode) eng.initLFO();

    // RGB → adaptive pitch + morph + stereo width
    eng.updateFromRGB(r || luma, g || luma, b || luma, luma);

    // Comb: same as engine 1
    var fundamental = 80 + luma * 320;
    for (var i = 0; i < eng.combFilters.length; i++) {
      var sliceLum = slices ? slices[i] : luma;
      eng.combFilters[i].frequency.setTargetAtTime(fundamental*(i+1), t, 0.3);
      eng.combFilters[i].gain.setTargetAtTime((sliceLum-0.5)*20, t, 0.3);
      eng.combFilters[i].Q.setTargetAtTime(1.5+chromaContrast*8, t, 0.3);
    }

    // Lowpass cutoff controlled by filter ribbon (handleLpRibbon)

    // LFO
    var now = eng.ctx.currentTime, dt = now - eng._prevHueTime, hueDelta = 0;
    if (dt > 0 && dt < 2) {
      hueDelta = Math.abs(hue - eng._prevHue);
      if (hueDelta > 0.5) hueDelta = 1 - hueDelta;
      hueDelta = hueDelta / dt;
    }
    eng._prevHue = hue; eng._prevHueTime = now;
    eng._lfoNode.frequency.setTargetAtTime(0.05+Math.min(hueDelta*4,1)*1.95, t, 0.5);
    eng._lfoGain.gain.setTargetAtTime((100 + chromaContrast*500) * luma, t, 0.3);
  };

  eng.setSoundOn = function(on) {
    if (!eng.ctx) return;
    eng.ctx.resume();
    eng.masterGain.gain.cancelScheduledValues(0);
    eng.masterGain.gain.value = on ? 0.7 : 0;
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

  // Loop + recording — identical to engine 1
  eng.startRecording = function() {
    if (!eng.ctx) return;
    var chunks = [], proc = eng.ctx.createScriptProcessor(4096, 2, 2);
    proc.onaudioprocess = function(e) {
      chunks.push({ L: new Float32Array(e.inputBuffer.getChannelData(0)), R: new Float32Array(e.inputBuffer.getChannelData(1)) });
    };
    eng.limiterNode.connect(proc); proc.connect(eng.ctx.destination);
    eng._recorder = proc; eng._recChunks = chunks;
  };

  eng.stopRecording = function() {
    if (!eng._recorder) return null;
    try { eng.limiterNode.disconnect(eng._recorder); eng._recorder.disconnect(); } catch(e) {}
    var chunks = eng._recChunks; eng._recorder = null; eng._recChunks = null;
    var sr = eng.ctx.sampleRate;
    var nFrames = chunks.reduce(function(s,c){return s+c.L.length;},0);
    var buf = new ArrayBuffer(44 + nFrames*4), view = new DataView(buf);
    function str(o,s){for(var i=0;i<s.length;i++)view.setUint8(o+i,s.charCodeAt(i));}
    function u32(o,v){view.setUint32(o,v,true);}
    function u16(o,v){view.setUint16(o,v,true);}
    str(0,"RIFF");u32(4,36+nFrames*4);str(8,"WAVE");
    str(12,"fmt ");u32(16,16);u16(20,1);u16(22,2);
    u32(24,sr);u32(28,sr*4);u16(32,4);u16(34,16);
    str(36,"data");u32(40,nFrames*4);
    var off=44;
    for(var ci=0;ci<chunks.length;ci++){
      var L=chunks[ci].L,R=chunks[ci].R;
      for(var fi=0;fi<L.length;fi++){
        var ls=Math.max(-1,Math.min(1,L[fi])),rs=Math.max(-1,Math.min(1,R[fi]));
        view.setInt16(off,ls<0?ls*0x8000:ls*0x7FFF,true);off+=2;
        view.setInt16(off,rs<0?rs*0x8000:rs*0x7FFF,true);off+=2;
      }
    }
    return buf;
  };

  eng.startLoopRecord = function() {
    if (!eng.ctx) return;
    eng.stopLoop();
    eng._loopRecording=true; eng._loopChunks=[];
    var maxSamples=eng.ctx.sampleRate*10, captured=0;
    var proc=eng.ctx.createScriptProcessor(4096,2,2);
    proc.onaudioprocess=function(ev){
      if(!eng._loopRecording||captured>=maxSamples)return;
      eng._loopChunks.push({L:new Float32Array(ev.inputBuffer.getChannelData(0)),R:new Float32Array(ev.inputBuffer.getChannelData(1))});
      captured+=4096;
    };
    eng.limiterNode.connect(proc);proc.connect(eng.ctx.destination);eng._loopProc=proc;
  };

  eng.commitLoop = function() {
    eng._loopRecording=false;
    if(eng._loopProc){try{eng.limiterNode.disconnect(eng._loopProc);eng._loopProc.disconnect();}catch(e){}eng._loopProc=null;}
    var chunks=eng._loopChunks;
    if(!chunks.length)return false;
    var sr=eng.ctx.sampleRate,nFrames=chunks.reduce(function(s,c){return s+c.L.length;},0);
    if(nFrames<4096)return false;
    var buf=eng.ctx.createBuffer(2,nFrames,sr),oL=buf.getChannelData(0),oR=buf.getChannelData(1),off=0;
    for(var i=0;i<chunks.length;i++){oL.set(chunks[i].L,off);oR.set(chunks[i].R,off);off+=chunks[i].L.length;}
    var fl=Math.min(Math.floor(sr*0.008),Math.floor(nFrames/4));
    for(var j=0;j<fl;j++){var t=j/fl;oL[j]*=t;oR[j]*=t;oL[nFrames-fl+j]*=(1-t);oR[nFrames-fl+j]*=(1-t);}
    eng.masterGain.gain.value=0;
    var lg=eng.ctx.createGain();lg.gain.value=0.85;lg.connect(eng.limiterNode);
    var src=eng.ctx.createBufferSource();src.buffer=buf;src.loop=true;src.connect(lg);src.start(0);
    eng._loopNode=src;eng._loopGain=lg;
    return true;
  };

  eng.stopLoop = function() {
    eng._loopRecording=false;
    if(eng._loopProc){try{eng.limiterNode.disconnect(eng._loopProc);eng._loopProc.disconnect();}catch(e){}eng._loopProc=null;}
    if(eng._loopNode){try{eng._loopNode.stop();eng._loopNode.disconnect();}catch(e){}eng._loopNode=null;}
    if(eng._loopGain){try{eng._loopGain.disconnect();}catch(e){}eng._loopGain=null;}
    eng._loopChunks=[];
    if(eng.active)eng.masterGain.gain.value=0.7;
  };

  eng.isLooping = function() { return !!eng._loopNode; };

  eng.destroy = function() {
    eng.panic();
    if(eng._lfoNode){try{eng._lfoNode.stop();}catch(e){}}
    ['oscR','oscG','oscB'].forEach(function(k){if(eng[k])try{eng[k].osc.stop();}catch(e){} });
    for(var i=0;i<eng.combFilters.length;i++){try{eng.combFilters[i].disconnect();}catch(e){}}
    if(eng.ctx)eng.ctx.close();
  };

  return eng;
}

// ── Frame analysis ────────────────────────────────────────────────────────────
function analyseFrame(canvas, ctx2d) {
  var w = canvas.width, h = canvas.height;
  if (!w || !h) return null;
  var px    = ctx2d.getImageData(0, 0, w, h).data;
  var total = w * h;
  var sumR=0,sumG=0,sumB=0,comXw=0,comYw=0,comW=0;

  for (var i = 0; i < total; i++) {
    var r=px[i*4]/255, g=px[i*4+1]/255, b=px[i*4+2]/255;
    var lum=0.2126*r+0.7152*g+0.0722*b;
    sumR+=r;sumG+=g;sumB+=b;
    comXw+=(i%w)/w*lum; comYw+=Math.floor(i/w)/h*lum; comW+=lum;
  }

  var avgR=sumR/total,avgG=sumG/total,avgB=sumB/total;
  var luma=0.2126*avgR+0.7152*avgG+0.0722*avgB;
  var max=Math.max(avgR,avgG,avgB),min=Math.min(avgR,avgG,avgB),delta=max-min;
  var hue=0;
  if(delta>0){
    if(max===avgR)      hue=((avgG-avgB)/delta)%6;
    else if(max===avgG) hue=(avgB-avgR)/delta+2;
    else                hue=(avgR-avgG)/delta+4;
    hue=((hue*60)+360)%360;
  }
  var sat=max===0?0:delta/max;
  var comX=comW>0?comXw/comW:0.5,comY=comW>0?comYw/comW:0.5;

  // Snake raster wavetable
  var wt=new Float32Array(ANALYSIS_RES);
  var cols=Math.ceil(Math.sqrt(ANALYSIS_RES*(w/h)));
  var rows=Math.ceil(ANALYSIS_RES/cols);
  var idx2=0;
  for(var row2=0;row2<rows&&idx2<ANALYSIS_RES;row2++){
    var rowFrac=(row2+0.5)/rows,py2=Math.floor(rowFrac*h),ltr=(row2%2===0);
    for(var col2=0;col2<cols&&idx2<ANALYSIS_RES;col2++){
      var c2=ltr?col2:(cols-1-col2),colFrac=(c2+0.5)/cols,px2=Math.floor(colFrac*w);
      var sum2=0,cnt2=0;
      for(var dy=-1;dy<=1;dy++)for(var dx=-1;dx<=1;dx++){
        var nx=Math.max(0,Math.min(w-1,px2+dx)),ny=Math.max(0,Math.min(h-1,py2+dy));
        var pi=(ny*w+nx)*4;
        sum2+=0.2126*(px[pi]/255)+0.7152*(px[pi+1]/255)+0.0722*(px[pi+2]/255);
        cnt2++;
      }
      wt[idx2++]=(sum2/cnt2)*2-1;
    }
  }

  // Chroma contrast
  var gridN=4,cellHues=[];
  for(var gy=0;gy<gridN;gy++)for(var gx=0;gx<gridN;gx++){
    var xS=Math.floor(gx*w/gridN),xE=Math.floor((gx+1)*w/gridN);
    var yS=Math.floor(gy*h/gridN),yE=Math.floor((gy+1)*h/gridN);
    var cR=0,cG=0,cB=0,cN=0;
    for(var cy=yS;cy<yE;cy+=4)for(var cx=xS;cx<xE;cx+=4){
      var ci=(cy*w+cx)*4;
      cR+=px[ci]/255;cG+=px[ci+1]/255;cB+=px[ci+2]/255;cN++;
    }
    if(cN>0){cR/=cN;cG/=cN;cB/=cN;}
    var cMax=Math.max(cR,cG,cB),cMin=Math.min(cR,cG,cB),cD=cMax-cMin;
    if(cD>0.05){
      var cHue=0;
      if(cMax===cR)      cHue=((cG-cB)/cD+6)%6;
      else if(cMax===cG) cHue=(cB-cR)/cD+2;
      else               cHue=(cR-cG)/cD+4;
      cellHues.push(cHue/6);
    }
  }
  var chromaContrast=0;
  if(cellHues.length>1){
    var hMean=cellHues.reduce(function(s,v){return s+v;},0)/cellHues.length;
    var hVar=cellHues.reduce(function(s,v){return s+Math.pow(v-hMean,2);},0)/cellHues.length;
    chromaContrast=Math.min(1,hVar*8);
  }

  // 8 vertical slices
  var slices=new Float32Array(8);
  for(var si=0;si<8;si++){
    var sxS=Math.floor(si*w/8),sxE=Math.floor((si+1)*w/8),sSum=0,sCnt=0;
    for(var sy=0;sy<h;sy+=4)for(var sx=sxS;sx<sxE;sx+=4){
      var spi=(sy*w+sx)*4;
      sSum+=0.2126*(px[spi]/255)+0.7152*(px[spi+1]/255)+0.0722*(px[spi+2]/255);
      sCnt++;
    }
    slices[si]=sCnt>0?sSum/sCnt:0.5;
  }

  return { luma:luma, hue:hue/360, saturation:sat, chromaContrast:chromaContrast,
           slices:slices, comX:comX, comY:comY, wavetable:wt,
           avgR:avgR, avgG:avgG, avgB:avgB };
}

// ── Helpers ───────────────────────────────────────────────────────────────────
function el(type, props) {
  var args = [type, props || null];
  for (var i = 2; i < arguments.length; i++) args.push(arguments[i]);
  return React.createElement.apply(React, args);
}
function cx() {
  return Array.prototype.slice.call(arguments).filter(Boolean).join(" ");
}

// ── App ───────────────────────────────────────────────────────────────────────
function App() {
  var videoRef        = useRef(null);
  var captureRef      = useRef(null);
  var loopFramesRef   = useRef([]);
  var loopOverlayRef  = useRef(null);
  var loopVidTimerRef = useRef(null);
  var loopFrameIdxRef = useRef(0);
  var scopeRef        = useRef(null);
  var ribbonRef       = useRef(null);
  var lpRibbonRef     = useRef(null);
  var synthRef        = useRef(null);
  var streamRef       = useRef(null);
  var timerRef        = useRef(null);
  var rafRef          = useRef(null);

  var rs  = useState(false);  var soundOn       = rs[0],  setSoundOn      = rs[1];
  var rr  = useState(false);  var recording     = rr[0],  setRecording    = rr[1];
  var rsc = useState(true);   var showScope     = rsc[0], setShowScope    = rsc[1];
  var rst = useState(false);  var showSettings  = rst[0], setShowSettings = rst[1];
  var radv= useState(false);  var showAdv       = radv[0],setShowAdv      = radv[1];
  var rf  = useState("environment"); var facingMode = rf[0], setFacingMode = rf[1];
  var rx  = useState(0.5);    var ribbonX       = rx[0],  setRibbonX      = rx[1];
  var rlp = useState(0.7);    var lpX           = rlp[0], setLpX          = rlp[1]; // 0=closed 1=open
  var rcr = useState(false);  var camReady      = rcr[0], setCamReady     = rcr[1];
  var rce = useState(null);   var camError      = rce[0], setCamError     = rce[1];
  var rer = useState(false);  var engReady      = rer[0], setEngReady     = rer[1];
  var rco = useState(true);   var camOn         = rco[0], setCamOn        = rco[1];
  var rl  = useState(false);  var looping       = rl[0],  setLooping      = rl[1];
  var rlc = useState(false);  var loopCapturing = rlc[0], setLoopCapturing= rlc[1];
  var rfd = useState(null);   var frameData     = rfd[0], setFrameData    = rfd[1];

  // Which engine is active: "1" or "2"
  var ren = useState("1");    var activeEngine  = ren[0], setActiveEngine  = ren[1];

  // Engine 1 settings
  var rs1 = useState({ voices:1, detune:12, quantize:false, scale:"pentatonic",
    rootNote:48, pitchMin:36, pitchMax:72, reverbMix:0.3, fps:10, showScales:false });
  var settings1 = rs1[0], setSettings1 = rs1[1];

  // Engine 2 settings
  var rs2 = useState({ quantize:false, scale:"pentatonic", rootNote:48,
    pitchMin:36, pitchMax:72, reverbMix:0.3, fps:10, showScales:false,
    intervalR:"octave", intervalG:"fifth", intervalB:"maj3", glide:200 });
  var settings2 = rs2[0], setSettings2 = rs2[1];

  var settings    = activeEngine === "1" ? settings1 : settings2;
  var setSettings = activeEngine === "1" ? setSettings1 : setSettings2;

  function setSetting(k, v) { setSettings(function(s){ var n=Object.assign({},s); n[k]=v; return n; }); }

  // Init both engines, switch between them
  var eng1Ref = useRef(null);
  var eng2Ref = useRef(null);

  useEffect(function() {
    eng1Ref.current = makeEngine1();
    eng2Ref.current = makeEngine2();
    synthRef.current = eng1Ref.current;
    return function() {
      if (eng1Ref.current) eng1Ref.current.destroy();
      if (eng2Ref.current) eng2Ref.current.destroy();
    };
  }, []);

  // Switch engine
  useEffect(function() {
    var prev = synthRef.current;
    var next = activeEngine === "1" ? eng1Ref.current : eng2Ref.current;
    if (!next || next === prev) return;
    // If previous was running, init and start new one
    if (prev && prev.active) {
      prev.setSoundOn(false);
      if (!next.ctx) next.init();
      next.setSoundOn(true);
      setSoundOn(true);
    }
    synthRef.current = next;
  }, [activeEngine]);

  // Sync settings to active engine
  useEffect(function() {
    var eng = synthRef.current;
    if (!eng) return;
    Object.assign(eng.settings, settings);
    if (eng.ctx) {
      if (activeEngine === "1") eng.spawnVoices && eng.spawnVoices();
      else { eng.updateIntervals && eng.updateIntervals(); }
    }
  }, [settings]);

  // Camera
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
        if (v) { v.srcObject=stream; v.play().then(function(){if(alive)setCamReady(true);}).catch(function(){if(alive)setCamReady(true);}); }
      })
      .catch(function(e) {
        if (!alive) return;
        setCamError(e.name==="NotAllowedError"?"CAMERA PERMISSION DENIED":"CAMERA UNAVAILABLE");
      });
    return function() { alive=false; if(streamRef.current)streamRef.current.getTracks().forEach(function(t){t.stop();}); };
  }, [facingMode, camOn]);

  // Analysis loop
  useEffect(function() {
    if (!camReady) return;
    var ms = 1000 / settings.fps;
    timerRef.current = setInterval(function() {
      var v=videoRef.current, c=captureRef.current;
      if (!v||!c||v.readyState<2) return;
      c.width=v.videoWidth||320; c.height=v.videoHeight||240;
      var ctx2d=c.getContext("2d");
      ctx2d.drawImage(v,0,0,c.width,c.height);
      var data=analyseFrame(c,ctx2d);
      if (data) {
        setFrameData(data);
        var eng=synthRef.current;
        if (eng && eng.ctx) {
          if (activeEngine==="1") {
            eng.currentLuma=data.luma;
            eng.updateFromCamera(data.luma,data.hue,data.chromaContrast,data.slices);
            eng.updateWavetable(data.wavetable,data.luma);
          } else {
            eng.updateFromCamera(data.luma,data.hue,data.chromaContrast,data.slices,data.avgR,data.avgG,data.avgB);
          }
        }
        if (eng && eng._loopRecording && loopFramesRef.current.length < 100) {
          loopFramesRef.current.push(ctx2d.getImageData(0,0,c.width,c.height));
        }
      }
    }, ms);
    return function() { clearInterval(timerRef.current); };
  }, [camReady, settings.fps, activeEngine]);

  // Scope
  useEffect(function() {
    var alive=true;
    function draw() {
      if(!alive)return;
      rafRef.current=requestAnimationFrame(draw);
      if(!showScope)return;
      var canvas=scopeRef.current;
      if(!canvas)return;
      var ctx=canvas.getContext("2d"),W=canvas.width,H=canvas.height;
      ctx.clearRect(0,0,W,H);
      var wd=synthRef.current?synthRef.current.getAnalyserData():null;
      if(!wd||!soundOn)return;
      var peak=0.001;
      for(var p=0;p<wd.length;p++){var a=Math.abs(wd[p]);if(a>peak)peak=a;}
      var scale=Math.min(1/peak,8);
      ctx.strokeStyle="rgba(127,255,106,0.85)";ctx.lineWidth=1.5;
      ctx.shadowColor="#7fff6a";ctx.shadowBlur=8;
      ctx.beginPath();
      var sl=W/wd.length;
      for(var i=0;i<wd.length;i++){var x=i*sl,y=H/2+wd[i]*scale*H*0.42;i===0?ctx.moveTo(x,y):ctx.lineTo(x,y);}
      ctx.stroke();
    }
    rafRef.current=requestAnimationFrame(draw);
    return function(){alive=false;cancelAnimationFrame(rafRef.current);};
  }, [showScope,soundOn]);

  var handleSound = useCallback(function() {
    var eng=synthRef.current;
    if(!eng)return;
    if(!eng.ctx){eng.init();setEngReady(true);}
    var next=!soundOn;
    eng.setSoundOn(next);
    setSoundOn(next);
  }, [soundOn]);

  var handleRibbon = useCallback(function(e) {
    e.preventDefault();
    var rect=ribbonRef.current?ribbonRef.current.getBoundingClientRect():null;
    if(!rect)return;
    var cx=e.touches?e.touches[0].clientX:e.clientX;
    var x=Math.max(0,Math.min(1,(cx-rect.left)/rect.width));
    setRibbonX(x);
    if(synthRef.current)synthRef.current.updatePitch(x);
  }, []);

  var handleLpRibbon = useCallback(function(e) {
    e.preventDefault();
    var rect = lpRibbonRef.current ? lpRibbonRef.current.getBoundingClientRect() : null;
    if (!rect) return;
    var cx = e.touches ? e.touches[0].clientX : e.clientX;
    var x  = Math.max(0, Math.min(1, (cx - rect.left) / rect.width));
    setLpX(x);
    var eng = synthRef.current;
    if (!eng || !eng.ctx) return;
    // Map 0..1 → 150Hz..12000Hz (log scale feels more natural)
    var freq = 150 * Math.pow(12000/150, x);
    // Slope: 24dB when closed (low x), morphs to 12dB when open
    // Approximate by changing Q: high Q at low x
    var node = eng.lowpassNode;
    if (!node) return;
    var t = eng.ctx.currentTime;
    node.frequency.setTargetAtTime(freq, t, 0.05);
    // Q: 0.7 (flat/12dB-ish) when open, 2.0 (resonant/steeper) when closed
    node.Q.setTargetAtTime(0.7 + (1 - x) * 1.3, t, 0.05);
  }, []);

  var handleFlip    = useCallback(function(){setFacingMode(function(f){return f==="environment"?"user":"environment";});}, []);
  var handleReload  = useCallback(function(){window.location.reload();}, []);

  var handleLoopDown = function(e) {
    e.preventDefault();
    var eng=synthRef.current;
    if(!eng||!eng.ctx)return;
    if(eng.isLooping()){
      eng.stopLoop();setLooping(false);setLoopCapturing(false);
      clearInterval(loopVidTimerRef.current);loopFramesRef.current=[];
      var ov=loopOverlayRef.current;
      if(ov)ov.getContext("2d").clearRect(0,0,ov.width,ov.height);
      return;
    }
    loopFramesRef.current=[];eng.startLoopRecord();setLoopCapturing(true);
  };

  var handleLoopUp = function(e) {
    e.preventDefault();
    var eng=synthRef.current;
    if(!eng||!eng._loopRecording)return;
    var ok=eng.commitLoop();
    setLoopCapturing(false);
    if(!ok)return;
    setLooping(true);
    var frames=loopFramesRef.current;
    if(frames.length>0){
      loopFrameIdxRef.current=0;clearInterval(loopVidTimerRef.current);
      var ov=loopOverlayRef.current;
      loopVidTimerRef.current=setInterval(function(){
        if(!ov||!frames.length)return;
        ov.width=frames[0].width;ov.height=frames[0].height;
        ov.getContext("2d").putImageData(frames[loopFrameIdxRef.current%frames.length],0,0);
        loopFrameIdxRef.current++;
      },100);
    }
  };

  var handleCamToggle = useCallback(function(){
    setCamOn(function(on){
      var next=!on;
      if(!next){if(streamRef.current)streamRef.current.getTracks().forEach(function(t){t.stop();});streamRef.current=null;setCamReady(false);}
      return next;
    });
  }, []);

  var handleRecord = useCallback(function(){
    var eng=synthRef.current;
    if(recording){
      var wavBuf=eng?eng.stopRecording():null;
      if(wavBuf){var blob=new Blob([wavBuf],{type:"audio/wav"}),url=URL.createObjectURL(blob),a=document.createElement("a");a.href=url;a.download="camsynth-"+Date.now()+".wav";a.click();}
      setRecording(false);
    } else {
      if(!eng||!eng.ctx)return;
      eng.startRecording();setRecording(true);
    }
  }, [recording]);

  var handleEngineSwitch = useCallback(function(id) {
    setActiveEngine(id);
    setShowSettings(false);
  }, []);

  var pr      = settings.pitchMax - settings.pitchMin;
  var midMidi = Math.round(settings.pitchMin + ribbonX * pr);
  var noteName= NOTE_NAMES[midMidi%12]+(Math.floor(midMidi/12)-1);

  // ── MAIN VIEW ────────────────────────────────────────────────────────────────
  var mainView = el("div", { style:{ display:"flex", flexDirection:"column", width:"100%", height:"100%", overflow:"hidden" } },

    // Header
    el("div", { style:{ display:"flex", justifyContent:"space-between", alignItems:"center", padding:"10px 14px 6px", paddingTop:"max(env(safe-area-inset-top,10px),10px)", flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"baseline", gap:7 } },
        el("span", { style:{ fontSize:10, letterSpacing:"0.2em", color:"#7fff6a", textTransform:"uppercase" } }, "CamSynth"),
        el("span", { style:{ fontSize:8, color:"#888", letterSpacing:"0.1em" } }, "v"+VERSION)
      ),
      el("div", { style:{ display:"flex", gap:4, alignItems:"center" } },
        el("button", { className:cx("cb", showAdv&&"on"), onClick:function(){setShowAdv(function(s){return !s;});}, style:{ letterSpacing:"0.12em", padding:"5px 10px" } }, "ADV"),
        camOn && el("button", { className:"cb", onClick:handleFlip }, "\u21c4"),
        el("button", { className:"cb", onClick:handleReload }, "\u21ba")
      )
    ),

    // Camera
    el("div", { style:{ position:"relative", background:"#050505", overflow:"hidden", borderTop:"1px solid #141414", borderBottom:"1px solid #141414", flexShrink:0, height:"42vh" } },
      el("video", { ref:videoRef, playsInline:true, muted:true, autoPlay:true, controls:false, style:{ width:"100%", height:"100%", objectFit:"cover", display:"block", transform:facingMode==="user"?"scaleX(-1)":"none" } }),
      showScope && el("canvas", { ref:scopeRef, width:480, height:80, style:{ position:"absolute", bottom:0, left:0, width:"100%", height:60, pointerEvents:"none" } }),
      frameData && el("div", { style:{ position:"absolute", top:8, left:8, fontSize:8, color:"rgba(127,255,106,0.35)", letterSpacing:"0.1em", lineHeight:2, pointerEvents:"none" } },
        el("div",null,"LMA "+(frameData.luma*100).toFixed(1)),
        el("div",null,"HUE "+Math.round(frameData.hue*360)+"\xb0"),
        el("div",null,"CHR "+(frameData.chromaContrast*100).toFixed(1)),
        activeEngine==="2" && frameData.avgR !== undefined && el("div",null,
          "R "+(((frameData.avgR-frameData.luma)*100)).toFixed(1)+
          " G "+(((frameData.avgG-frameData.luma)*100)).toFixed(1)+
          " B "+(((frameData.avgB-frameData.luma)*100)).toFixed(1)
        )
      ),
      !camOn && el("div", { style:{ position:"absolute", inset:0, display:"flex", alignItems:"center", justifyContent:"center", background:"#050505" } },
        el("span", { style:{ color:"#2a2a2a", fontSize:10, letterSpacing:"0.2em" } }, "CAMERA OFF")
      ),
      camOn && !camReady && !camError && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:8 } },
        el("span", { style:{ color:"#2a2a2a", fontSize:10, letterSpacing:"0.2em" } }, "AWAITING CAMERA"),
        el("span", { style:{ color:"#1e1e1e", fontSize:8 } }, "grant permission when prompted")
      ),
      camError && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:10 } },
        el("span", { style:{ color:"#ff4444", fontSize:10 } }, camError)
      ),
      el("canvas", { ref:captureRef, style:{ display:"none" } }),
      el("canvas", { ref:loopOverlayRef, style:{ position:"absolute", inset:0, width:"100%", height:"100%", pointerEvents:"none", display:looping?"block":"none" } })
    ),

    // Pitch ribbon
    el("div", { style:{ flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"center", padding:"3px 14px 2px", gap:8 } },
        el("span", { style:{ fontSize:8, color:"#2a2a2a", letterSpacing:"0.1em" } }, "PITCH"),
        el("span", { style:{ fontSize:13, color:"#7fff6a", letterSpacing:"0.04em", minWidth:34 } }, noteName),
        el("span", { style:{ fontSize:8, color:"#1a1a1a", marginLeft:"auto" } }, settings.quantize?settings.scale:"free")
      ),
      el("div", { ref:ribbonRef, onMouseDown:handleRibbon, onMouseMove:function(e){if(e.buttons)handleRibbon(e);}, onTouchStart:handleRibbon, onTouchMove:handleRibbon,
        style:{ height:44, background:"linear-gradient(90deg,#070c07 0%,#101810 50%,#070c07 100%)", borderTop:"1px solid #141c14", borderBottom:"1px solid #141c14", position:"relative", cursor:"crosshair" } },
        Array.from({length:pr+1},function(_,i){
          var midi = settings.pitchMin + i;
          var semitone = midi % 12;
          var isOctave = semitone === (settings.rootNote % 12);
          var inScale = !settings.quantize || SCALES[settings.scale].indexOf(((semitone - settings.rootNote%12)+12)%12) >= 0;
          var h = isOctave ? "100%" : inScale ? "55%" : "25%";
          var bg = isOctave ? "#2a4a2a" : inScale ? "#1c321c" : "#0e140e";
          return el("div",{key:i,style:{position:"absolute",left:((i/pr)*100)+"%",top:isOctave?0:"65%",width:isOctave?2:1,height:h,background:bg}});
        }),
        el("div", { style:{ position:"absolute", left:(ribbonX*100)+"%", top:0, bottom:0, width:2, background:"#7fff6a", boxShadow:"0 0 10px #7fff6a", transform:"translateX(-50%)", pointerEvents:"none" } })
      )
    ),

    // Lowpass ribbon
    el("div", { style:{ flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"center", padding:"3px 14px 2px", gap:8 } },
        el("span", { style:{ fontSize:8, color:"#2a2a2a", letterSpacing:"0.1em" } }, "FILTER"),
        el("span", { style:{ fontSize:11, color:"#6bb5ff", letterSpacing:"0.04em", minWidth:60 } },
          (150 * Math.pow(12000/150, lpX)).toFixed(0)+" Hz"
        ),
        el("span", { style:{ fontSize:8, color:"#1a1a1a", marginLeft:"auto" } },
          lpX < 0.3 ? "24db" : lpX < 0.7 ? "18db" : "12db"
        )
      ),
      el("div", {
        ref:lpRibbonRef,
        onMouseDown:handleLpRibbon, onMouseMove:function(e){if(e.buttons)handleLpRibbon(e);},
        onTouchStart:handleLpRibbon, onTouchMove:handleLpRibbon,
        style:{ height:32, position:"relative", cursor:"crosshair",
          background:"linear-gradient(90deg, #050a14 0%, #0a1628 30%, #0d2040 60%, #1a3a6a 80%, #2050a0 100%)",
          borderTop:"1px solid #141c24", borderBottom:"1px solid #141c24" }
      },
        // Frequency markers
        [150,300,600,1200,3000,6000,12000].map(function(f) {
          var pos = Math.log(f/150) / Math.log(12000/150);
          return el("div", { key:f, style:{ position:"absolute", left:(pos*100)+"%", top:0, bottom:0, width:1, background:"rgba(107,181,255,0.15)" } });
        }),
        // Playhead
        el("div", { style:{ position:"absolute", left:(lpX*100)+"%", top:0, bottom:0, width:2,
          background:"#6bb5ff", boxShadow:"0 0 8px #6bb5ff", transform:"translateX(-50%)", pointerEvents:"none" } })
      )
    ),

    // Controls
    el("div", { style:{ display:"flex", gap:5, padding:"7px 14px", flexShrink:0 } },
      el("button", { className:cx("cb",soundOn&&"on"), onClick:handleSound, style:{ flex:2, fontSize:11, padding:"10px 0", letterSpacing:"0.1em" } }, soundOn?"\u25fc ON":"\u25b6 OFF"),
      el("button", { className:cx("cb",loopCapturing&&"blink",looping&&"on"), onPointerDown:handleLoopDown, onPointerUp:handleLoopUp, style:{ flex:1, touchAction:"none" } }, loopCapturing?"\u25cf LOOP":looping?"\u21ba LOOP":"\u25cb LOOP"),
      el("button", { className:cx("cb",recording&&"rec"), onClick:handleRecord, style:{ flex:1 } }, recording?"\u25cf REC":"\u25cb REC"),
      el("button", { className:cx("cb",camOn&&"on"), onClick:handleCamToggle, style:{ flex:1 } }, "\u25a3 CAM"),
      el("button", { className:cx("cb",showScope&&"on"), onClick:function(){setShowScope(function(s){return !s;});}, style:{ flex:1 } }, "\u223f OSC"),
      el("button", { className:cx("cb",showSettings&&"on"), onClick:function(){setShowSettings(function(s){return !s;});setShowAdv(false);}, style:{ flex:1 } }, "\u2699")
    ),

    // Settings drawer — engine 1
    showSettings && activeEngine==="1" && el("div", { style:{ padding:"8px 14px 14px", borderTop:"1px solid #141414", background:"#0c0c0d", overflowY:"auto", flexShrink:0, maxHeight:"42vh" } },
      el("div",{className:"sr"},
        el("label",null,"Voices"),
        el("div",{style:{display:"flex",gap:2}},
          [1,2,4].map(function(v){return el("button",{key:v,className:cx("sg",settings1.voices===v&&"sel"),onClick:function(){setSettings1(function(s){var n=Object.assign({},s);n.voices=v;return n;})}},v);})
        )
      ),
      el("div",{className:"sr",style:{flexDirection:"column",alignItems:"flex-start",gap:3}},
        el("div",{style:{display:"flex",width:"100%",justifyContent:"space-between"}},
          el("label",null,"Detune"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},settings1.detune+" ct")
        ),
        el("input",{type:"range",min:0,max:50,value:settings1.detune,onChange:function(e){var v=+e.target.value;setSettings1(function(s){var n=Object.assign({},s);n.detune=v;return n;});var eng=eng1Ref.current;if(eng)eng.updateDetune(v);}})
      ),
      el("div",{className:"sr"},
        el("label",null,"Scale"),
        el("div",{style:{display:"flex",gap:2,alignItems:"center"}},
          el("span",{style:{fontSize:9,color:"#7fff6a",marginRight:4}},settings1.quantize?settings1.scale:"off"),
          el("button",{className:cx("sg",settings1.showScales&&"sel"),onClick:function(){setSettings1(function(s){var n=Object.assign({},s);n.showScales=!s.showScales;return n;});}},settings1.showScales?"▲":"▼")
        )
      ),
      settings1.showScales && el("div",{style:{paddingBottom:4,borderBottom:"1px solid #141414"}},
        el("div",{style:{display:"flex",flexWrap:"wrap",gap:2,paddingTop:4}},
          el("button",{className:cx("sg",!settings1.quantize&&"sel"),onClick:function(){setSettings1(function(s){var n=Object.assign({},s);n.quantize=false;n.showScales=false;return n;})}},"off"),
          SCALE_NAMES.map(function(s){return el("button",{key:s,className:cx("sg",settings1.quantize&&settings1.scale===s&&"sel"),onClick:function(){setSettings1(function(st){var n=Object.assign({},st);n.scale=s;n.quantize=true;n.showScales=false;return n;})}},s);})
        )
      ),
      el("div",{className:"sr",style:{flexDirection:"column",alignItems:"flex-start",gap:3}},
        el("div",{style:{display:"flex",width:"100%",justifyContent:"space-between"}},
          el("label",null,"Pitch range"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},NOTE_NAMES[settings1.pitchMin%12]+(Math.floor(settings1.pitchMin/12)-1)+" \u2192 "+NOTE_NAMES[settings1.pitchMax%12]+(Math.floor(settings1.pitchMax/12)-1))
        ),
        el("div",{style:{display:"flex",gap:8,width:"100%"}},
          el("input",{type:"range",min:24,max:60,value:settings1.pitchMin,onChange:function(e){setSettings1(function(s){var n=Object.assign({},s);n.pitchMin=Math.min(+e.target.value,s.pitchMax-4);return n;});}}),
          el("input",{type:"range",min:48,max:84,value:settings1.pitchMax,onChange:function(e){setSettings1(function(s){var n=Object.assign({},s);n.pitchMax=Math.max(+e.target.value,s.pitchMin+4);return n;})}})
        )
      ),
      el("div",{className:"sr",style:{flexDirection:"column",alignItems:"flex-start",gap:3}},
        el("div",{style:{display:"flex",width:"100%",justifyContent:"space-between"}},
          el("label",null,"Reverb mix"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},Math.round(settings1.reverbMix*100)+"%")
        ),
        el("input",{type:"range",min:0,max:100,value:Math.round(settings1.reverbMix*100),onChange:function(e){setSettings1(function(s){var n=Object.assign({},s);n.reverbMix=e.target.value/100;return n;})}})
      )
    ),

    // Settings drawer — engine 2
    showSettings && activeEngine==="2" && el("div", { style:{ padding:"8px 14px 14px", borderTop:"1px solid #141414", background:"#0c0c0d", overflowY:"auto", flexShrink:0, maxHeight:"42vh" } },
      el("div",{className:"sr"},
        el("label",null,"Scale"),
        el("div",{style:{display:"flex",gap:2,alignItems:"center"}},
          el("span",{style:{fontSize:9,color:"#7fff6a",marginRight:4}},settings2.quantize?settings2.scale:"off"),
          el("button",{className:cx("sg",settings2.showScales&&"sel"),onClick:function(){setSettings2(function(s){var n=Object.assign({},s);n.showScales=!s.showScales;return n;});}},settings2.showScales?"▲":"▼")
        )
      ),
      settings2.showScales && el("div",{style:{paddingBottom:4,borderBottom:"1px solid #141414"}},
        el("div",{style:{display:"flex",flexWrap:"wrap",gap:2,paddingTop:4}},
          el("button",{className:cx("sg",!settings2.quantize&&"sel"),onClick:function(){setSettings2(function(s){var n=Object.assign({},s);n.quantize=false;n.showScales=false;return n;})}},"off"),
          SCALE_NAMES.map(function(s){return el("button",{key:s,className:cx("sg",settings2.quantize&&settings2.scale===s&&"sel"),onClick:function(){setSettings2(function(st){var n=Object.assign({},st);n.scale=s;n.quantize=true;n.showScales=false;return n;})}},s);})
        )
      ),
      el("div",{className:"sr",style:{flexDirection:"column",alignItems:"flex-start",gap:3}},
        el("div",{style:{display:"flex",width:"100%",justifyContent:"space-between"}},
          el("label",null,"Pitch range"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},NOTE_NAMES[settings2.pitchMin%12]+(Math.floor(settings2.pitchMin/12)-1)+" \u2192 "+NOTE_NAMES[settings2.pitchMax%12]+(Math.floor(settings2.pitchMax/12)-1))
        ),
        el("div",{style:{display:"flex",gap:8,width:"100%"}},
          el("input",{type:"range",min:24,max:60,value:settings2.pitchMin,onChange:function(e){setSettings2(function(s){var n=Object.assign({},s);n.pitchMin=Math.min(+e.target.value,s.pitchMax-4);return n;});}}),
          el("input",{type:"range",min:48,max:84,value:settings2.pitchMax,onChange:function(e){setSettings2(function(s){var n=Object.assign({},s);n.pitchMax=Math.max(+e.target.value,s.pitchMin+4);return n;})}})
        )
      ),
      el("div",{className:"sr",style:{flexDirection:"column",alignItems:"flex-start",gap:3}},
        el("div",{style:{display:"flex",width:"100%",justifyContent:"space-between"}},
          el("label",null,"Reverb mix"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},Math.round(settings2.reverbMix*100)+"%")
        ),
        el("input",{type:"range",min:0,max:100,value:Math.round(settings2.reverbMix*100),onChange:function(e){setSettings2(function(s){var n=Object.assign({},s);n.reverbMix=e.target.value/100;return n;})}})
      ),
      el("div",{className:"sr",style:{flexDirection:"column",alignItems:"flex-start",gap:3}},
        el("div",{style:{display:"flex",width:"100%",justifyContent:"space-between"}},
          el("label",null,"Glide"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},settings2.glide+"ms")
        ),
        el("input",{type:"range",min:0,max:2000,step:10,value:settings2.glide,onChange:function(e){
          var v=+e.target.value;
          setSettings2(function(s){var n=Object.assign({},s);n.glide=v;return n;});
          var eng=eng2Ref.current;if(eng)eng.settings.glide=v;
        }})
      )
    )
  );

  // ── ADVANCED PAGE ─────────────────────────────────────────────────────────────
  var advView = el("div", { style:{ display:"flex", flexDirection:"column", width:"100%", height:"100%", overflow:"hidden" } },

    // Adv header
    el("div", { style:{ display:"flex", justifyContent:"space-between", alignItems:"center", padding:"10px 14px 6px", paddingTop:"max(env(safe-area-inset-top,10px),10px)", flexShrink:0, borderBottom:"1px solid #141414" } },
      el("span", { style:{ fontSize:10, letterSpacing:"0.2em", color:"#7fff6a", textTransform:"uppercase" } }, "Advanced"),
      el("button", { className:"cb on", onClick:function(){setShowAdv(false);}, style:{ letterSpacing:"0.1em" } }, "\u2190 back")
    ),

    // Engine switcher
    el("div", { style:{ padding:"12px 14px 8px", flexShrink:0 } },
      el("div", { style:{ fontSize:8, color:"#444", letterSpacing:"0.15em", textTransform:"uppercase", marginBottom:8 } }, "Preset"),
      el("div", { style:{ display:"flex", gap:6 } },
        el("button", { className:cx("cb", activeEngine==="1"&&"on"), onClick:function(){handleEngineSwitch("1");}, style:{ flex:1, padding:"10px 0", fontSize:10, letterSpacing:"0.08em" } }, "CamSynth\u20091"),
        el("button", { className:cx("cb", activeEngine==="2"&&"on"), onClick:function(){handleEngineSwitch("2");}, style:{ flex:1, padding:"10px 0", fontSize:10, letterSpacing:"0.08em" } }, "CamSynth\u20092")
      )
    ),

    // Engine descriptions
    activeEngine==="1" && el("div", { style:{ padding:"8px 14px 0", flexShrink:0 } },
      el("div", { style:{ fontSize:8, color:"#2a2a2a", lineHeight:2, letterSpacing:"0.08em" } },
        el("div", null, "Image-scanned wavetable oscillator"),
        el("div", null, "Luma-gated sine \u2192 complex waveform morph"),
        el("div", null, "Comb filter topography + lowpass + LFO")
      )
    ),

    // Engine 2 — interval selectors
    activeEngine==="2" && el("div", { style:{ padding:"8px 14px", overflowY:"auto", flexShrink:0 } },
      el("div", { style:{ fontSize:8, color:"#2a2a2a", lineHeight:2, letterSpacing:"0.08em", marginBottom:10 } },
        el("div", null, "3 RGB oscillators — sine \u2194 square morph per channel"),
        el("div", null, "Color relations drive pitch within each interval range"),
        el("div", null, "Stereo width from color deviation")
      ),
      el("div", { style:{ fontSize:8, color:"#444", letterSpacing:"0.15em", textTransform:"uppercase", marginBottom:6 } }, "Interval range per oscillator"),
      ["R","G","B"].map(function(ch) {
        var key = "interval"+ch;
        var color = ch==="R"?"#ff6b6b":ch==="G"?"#7fff6a":"#6bb5ff";
        return el("div", { key:ch, className:"sr", style:{ alignItems:"center" } },
          el("label", { style:{ color:color, minWidth:16 } }, ch),
          el("div", { style:{ display:"flex", gap:2, flexWrap:"wrap" } },
            INTERVAL_NAMES.map(function(n) {
              return el("button", {
                key:n,
                className:cx("sg", settings2[key]===n&&"sel"),
                onClick:function(){
                  setSettings2(function(s){var ns=Object.assign({},s);ns[key]=n;return ns;});
                  var eng=eng2Ref.current;
                  if(eng){eng.settings[key]=n;eng.updateIntervals&&eng.updateIntervals();}
                }
              }, n);
            })
          )
        );
      })
    )
  );

  return el("div", { style:{ display:"flex", flexDirection:"column", width:"100%", height:"100dvh", background:"#0a0a0b", fontFamily:"'IBM Plex Mono','Courier New',monospace", color:"#c8c8b4", userSelect:"none", WebkitUserSelect:"none", WebkitTouchCallout:"none", touchAction:"none", overflow:"hidden", maxWidth:480, margin:"0 auto" } },

    el("style", null, `
      @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@300;400;500&display=swap');
      *{box-sizing:border-box;}
      .cb{background:transparent;border:1px solid #222;color:#777;font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:.08em;padding:6px 10px;cursor:pointer;text-transform:uppercase;-webkit-tap-highlight-color:transparent;-webkit-touch-callout:none;user-select:none;-webkit-user-select:none;touch-action:manipulation;transition:border-color .15s,color .15s;}
      .cb:active{background:#111;}
      .cb.on{border-color:#7fff6a;color:#7fff6a;}
      .cb.rec{border-color:#ff4444;color:#ff4444;background:rgba(255,68,68,.08);}
      .cb.dng{border-color:#ff4444;color:#ff4444;}
      @keyframes blink{0%,100%{opacity:1}50%{opacity:0.25}}
      .cb.blink{border-color:#ff4444;color:#ff4444;background:rgba(255,68,68,.08);animation:blink 0.6s infinite;}
      .sg{background:transparent;border:1px solid #1e1e1e;color:#444;font-family:'IBM Plex Mono',monospace;font-size:9px;padding:3px 7px;cursor:pointer;-webkit-tap-highlight-color:transparent;-webkit-touch-callout:none;user-select:none;-webkit-user-select:none;touch-action:manipulation;transition:all .1s;}
      .sg.sel{border-color:#7fff6a;color:#7fff6a;background:rgba(127,255,106,.06);}
      .sr{display:flex;align-items:center;justify-content:space-between;padding:5px 0;border-bottom:1px solid #141414;}
      .sr label{font-size:9px;letter-spacing:.1em;color:#444;text-transform:uppercase;}
      input[type=range]{-webkit-appearance:none;width:100%;height:22px;background:transparent;outline:none;cursor:pointer;margin:0;}
      input[type=range]::-webkit-slider-runnable-track{height:2px;background:#1e1e1e;border-radius:1px;margin-top:10px;}
      input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:20px;height:20px;background:#7fff6a;border-radius:50%;cursor:pointer;margin-top:-9px;}
      input[type=range]::-moz-range-track{height:2px;background:#1e1e1e;border-radius:1px;}
      input[type=range]::-moz-range-thumb{width:20px;height:20px;background:#7fff6a;border-radius:50%;border:none;cursor:pointer;}
    `),

    el("div", { style:{ position:"relative", width:"100%", flex:1, minHeight:0, display:"flex", flexDirection:"column" } },
      mainView,
      showAdv && el("div", { style:{ position:"absolute", inset:0, background:"#0a0a0b", zIndex:10, display:"flex", flexDirection:"column", overflow:"hidden" } },
        advView
      )
    )
  );
}

ReactDOM.createRoot(document.getElementById("root")).render(React.createElement(App));
