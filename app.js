// Camera Synth — v3.0.0
var VERSION = "3.9.5";

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
  "1×1":    1,
  "1×2":    2,
  "3×2":    1.5,
  "5×4":    1.25,
  "6×5":    1.2,
};
var INTERVAL_NAMES = Object.keys(INTERVALS);

// C:M ratios for FM synthesis per oscillator
var CM_RATIOS = {
  "1:1":    1.0,
  "1:2":    2.0,
  "2:1":    0.5,
  "1:3":    3.0,
  "1:1.5":  1.5,
  "1:√2": 1.4142,
};
var CM_NAMES = Object.keys(CM_RATIOS);
var CM_LABELS = {
  "1:1":    "bell",
  "1:2":    "woody",
  "2:1":    "brassy",
  "1:3":    "complex",
  "1:1.5":  "warm",
  "1:√2": "metallic",
};

// Human-readable labels for ADV page
var INTERVAL_LABELS = {
  "1×1": "unison",
  "1×2": "octave",
  "3×2": "fifth",
  "5×4": "maj 3rd",
  "6×5": "min 3rd",
};

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
    imag[n] = 1 / n;
  }
  return { real: real, imag: imag };
}

// LFO destinations — label: key used to resolve AudioParam in engine
var LFO_DESTS = {
  "filter cutoff":   "lp.freq",
  "filter Q":        "lp.q",
  "FM depth":        "fm.depth",
  "reverb mix":      "reverb.gain",
  "amp":             "master.gain",
  "stereo width":    "haas.gain",
  "R FM depth":      "fm.r",
  "G FM depth":      "fm.g",
  "B FM depth":      "fm.b",
};
var LFO_DEST_NAMES = Object.keys(LFO_DESTS);

var LFO_WAVES = ["sine", "square", "s&h"];

// ── Shared reverb IR (pre-built before gesture) ───────────────────────────────
// Algorithmic reverb replaces convolution IR

var SQUARE_COEFFS = makeSquareCoeffs(512);

// ══════════════════════════════════════════════════════════════════════════════
// ENGINE 1 — CamSynth_1
// Image-scanned wavetable, single oscillator bank, comb + lowpass + LFO
// ══════════════════════════════════════════════════════════════════════════════
function makeEngine1() {
  var eng = {
    ctx: null, voices: [],
    combFilters: [], lowpassNode: null,
    reverbNode: null, reverbGain: null, fxLoCut: null, fxHiCut: null,
    masterGain: null,
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
    // User LFOs
    lfo1: null, lfo2: null,
    settings: {
      voices: 1, detune: 12,
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72, reverbMix: 0.3, fps: 10,
      showScales: false,
      lfo1: { rate:0.5, depth:0, wave:"sine", dest:"filter cutoff", active:false },
      lfo2: { rate:0.2, depth:0, wave:"sine", dest:"filter Q",      active:false },
    },
  };

  eng.init = function() {
    if (eng.ctx) return;
    try {
      var AC  = window.AudioContext || window.webkitAudioContext;
      eng.ctx = new AC();
      var sr  = eng.ctx.sampleRate;
      // Algorithmic reverb (Schroeder)
      // Convolution reverb
      var buf = eng.ctx.createBuffer(2, REVERB_IR.len, eng.ctx.sampleRate);
      buf.getChannelData(0).set(REVERB_IR.L);
      buf.getChannelData(1).set(REVERB_IR.R);
      eng.reverbNode = eng.ctx.createConvolver();
      eng.reverbNode.buffer = buf;
      eng.reverbGain = eng.ctx.createGain(); eng.reverbGain.gain.value = 0;
      eng.dryGain    = eng.ctx.createGain(); eng.dryGain.gain.value = 1;

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
      // Chain first 7 combs in series
      for (var ci = 0; ci < N - 1; ci++) eng.combFilters[ci].connect(eng.combFilters[ci + 1]);
      // High-freq stereo: tap upper combs (4-7) through side panners
      eng.combSidePanL = eng.ctx.createStereoPanner(); eng.combSidePanL.pan.value = -0.6;
      eng.combSidePanR = eng.ctx.createStereoPanner(); eng.combSidePanR.pan.value =  0.6;
      eng.combSideGain = eng.ctx.createGain(); eng.combSideGain.gain.value = 0.5;
      // Upper 4 combs tap into side chain
      for (var ci = 4; ci < N; ci++) {
        eng.combFilters[ci].connect(eng.combSideGain);
      }
      eng.combSideGain.connect(eng.combSidePanL);
      eng.combSideGain.connect(eng.combSidePanR);


      // 4-pole ladder filter (Moog-style approximation)
      // 4 × 1-pole lowpass stages in series + resonance feedback
      eng.ladder = [];
      for (var li = 0; li < 4; li++) {
        var lf = eng.ctx.createBiquadFilter();
        lf.type = "lowpass";
        lf.frequency.value = 2000;
        lf.Q.value = 0.5; // flat 1-pole response per stage
        eng.ladder.push(lf);
      }
      for (var li = 0; li < 3; li++) eng.ladder[li].connect(eng.ladder[li+1]);
      // Resonance feedback: output → feedbackGain → input
      eng.ladderFb = eng.ctx.createGain();
      eng.ladderFb.gain.value = 0;
      // Invert feedback for stability (subtract from input)
      eng.ladderFbInv = eng.ctx.createGain();
      eng.ladderFbInv.gain.value = -1;
      eng.ladder[3].connect(eng.ladderFb);
      eng.ladderFb.connect(eng.ladderFbInv);
      eng.ladderFbInv.connect(eng.ladder[0]);
      // ladder[0] = lowpassNode for compatibility
      eng.lowpassNode  = eng.ladder[0];
      eng.lowpassNode2 = eng.ladder[3]; // output stage
      eng.combFilters[N - 1].connect(eng.lowpassNode);
      eng.combSidePanL.connect(eng.lowpassNode);
      eng.combSidePanR.connect(eng.lowpassNode);

      eng.preReverbGain = eng.ctx.createGain();
      eng.preReverbGain.gain.value = 1.0; // LFO amp modulates this

      eng.seqAmpGain = eng.ctx.createGain();
      eng.seqAmpGain.gain.value = 1.0; // sequencer amp env drives this (1.0 = drone mode)

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

      // ── Tape delay (ping-pong) ──────────────────────────────────────────────────
      // delayL → panL ↘
      //               merge → reverbNode
      // delayR → panR ↗
      // feedback: delayR → fbGain → delayL.input (cross-ping-pong)
      eng.delayL    = eng.ctx.createDelay(4.0);
      eng.delayR    = eng.ctx.createDelay(4.0);
      eng.delayL.delayTime.value = 0.25;
      eng.delayR.delayTime.value = 0.25;
      eng.fbGain    = eng.ctx.createGain();   // feedback amount
      eng.fbGain.gain.value = 0;
      eng.delayWetL = eng.ctx.createStereoPanner(); // ping-pong width
      eng.delayWetR = eng.ctx.createStereoPanner();
      eng.delayWetL.pan.value = -1;
      eng.delayWetR.pan.value =  1;
      eng.delayWet  = eng.ctx.createGain();   // wet mix
      eng.delayWet.gain.value = 0;
      eng.delayDry  = eng.ctx.createGain();   // dry pass-through
      eng.delayDry.gain.value = 1;

      // Ping-pong routing:
      // input → delayL → panL → delayWet
      // input → delayR → panR → delayWet (offset by one step = ping-pong)
      // delayL output → delayR input (cross-feed for ping-pong)
      // delayR output → fbGain → delayL input (feedback loop)
      // seqAmpGain → delayL (for delay processing)
      // seqAmpGain → delayDry connected in chain below
      // crossGain controls L→R feed (same as feedback, so at 0% = single echo only)
      eng.crossGain = eng.ctx.createGain();
      eng.crossGain.gain.value = 0;
      eng.seqAmpGain.connect(eng.delayL);
      eng.delayL.connect(eng.delayWetL);
      eng.delayL.connect(eng.crossGain);    // L→crossGain→R (scalable)
      eng.crossGain.connect(eng.delayR);
      eng.delayR.connect(eng.delayWetR);
      eng.delayR.connect(eng.fbGain);
      eng.fbGain.connect(eng.delayL);
      eng.delayWetL.connect(eng.delayWet);
      eng.delayWetR.connect(eng.delayWet);

      // Signal chain:
      // Signal chain: dry → master direct, wet → diffusion → master
      eng.lowpassNode.connect(eng.preReverbGain);
      eng.preReverbGain.connect(eng.seqAmpGain);
      // Signal chain: seqAmpGain → dry+wet delay → master
      // Diffusion on wet output: each repeat gets all-pass smeared
      // Send routing: dry always full, reverb adds on top
      // Lo/Hi cut sit BEFORE split — always affect delay output
      // delayDry + delayWet → fxLoCut → fxHiCut → masterGain
      //                                           → reverbNode → reverbGain → master
      eng.seqAmpGain.connect(eng.delayDry);
      // dry → master (clean, unfiltered)
      eng.delayDry.connect(eng.masterGain);
      eng.delayWet.connect(eng.masterGain);
      // reverb send: delay → filters → reverb
      eng.fxLoCut = eng.ctx.createBiquadFilter();
      eng.fxLoCut.type = 'highpass'; eng.fxLoCut.frequency.value = 20; eng.fxLoCut.Q.value = 0.5;
      eng.fxHiCut = eng.ctx.createBiquadFilter();
      eng.fxHiCut.type = 'lowpass'; eng.fxHiCut.frequency.value = 20000; eng.fxHiCut.Q.value = 0.5;
      eng.delayDry.connect(eng.fxLoCut);
      eng.delayWet.connect(eng.fxLoCut);
      eng.fxLoCut.connect(eng.fxHiCut);
      eng.fxHiCut.connect(eng.reverbNode);
      eng.reverbNode.connect(eng.reverbGain);
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
    // Reconnect LFOs after voice respawn
    if (eng.lfo1 || eng.lfo2) {
      eng.destroyUserLFOs();
      eng.initUserLFOs();
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

  eng.makeLFOWave = function(shape) {
    // shape: 0=sine, 0.5=triangle, 1=square — all bandlimited via PeriodicWave
    var size = 256;
    var real = new Float32Array(size / 2);
    var imag = new Float32Array(size / 2);
    imag[1] = 1.0; // fundamental always
    for (var n = 3; n < size / 2; n += 2) {
      var sinePart = 0;
      var triPart  = (8 / (Math.PI * Math.PI)) * (1 / (n * n)) * (n % 4 === 1 ? 1 : -1);
      var sqPart   = 1 / n;
      if (shape <= 0.5) {
        // sine → triangle
        var t = shape * 2;
        imag[n] = triPart * t;
      } else {
        // triangle → square
        var t = (shape - 0.5) * 2;
        var triVal = (8 / (Math.PI * Math.PI)) * (1 / (n * n)) * (n % 4 === 1 ? 1 : -1);
        imag[n] = triVal * (1 - t) + sqPart * t;
      }
    }
    return eng.ctx.createPeriodicWave(real, imag, { disableNormalization: false });
  };

  eng.initLFO = function() {
    if (!eng.ctx || eng._lfoNode) return;
    // Base frequency source — ribbon sets this, LFO offsets from it
    if (!eng._lpBase) {
      eng._lpBase = eng.ctx.createConstantSource();
      eng._lpBase.offset.value = 2000; // default
      eng.ladder.forEach(function(lf){ eng._lpBase.connect(lf.frequency); });
      eng._lpBase.start();
    }
    eng._lfoNode = eng.ctx.createOscillator();
    eng._lfoNode.setPeriodicWave(eng.makeLFOWave(0));
    eng._lfoNode.frequency.value = 0.2;
    eng._lfoGain = eng.ctx.createGain();
    eng._lfoGain.gain.value = 0;
    eng._lfoNode.connect(eng._lfoGain);
    // Connect to _lpBase.offset so ribbon and LFO both target same node
    if (eng._lpBase) {
      eng._lfoGain.connect(eng._lpBase.offset);
    } else {
      if (eng.ladder) { eng.ladder.forEach(function(lf){ eng._lfoGain.connect(lf.frequency); }); } else { eng._lfoGain.connect(eng.lowpassNode.frequency); }
    }
    eng._lfoNode.start();
  };

  eng.setLpFreq = function(freq) {
    var safeFreq = Math.max(20, Math.min(20000, freq));
    if (eng._lpBase) {
      eng._lpBase.offset.setTargetAtTime(safeFreq, eng.ctx.currentTime, 0.02);
    } else {
      eng.lowpassNode.frequency.setTargetAtTime(safeFreq, eng.ctx.currentTime, 0.02);
    }
    if (eng.ladder) eng.ladder.forEach(function(lf){ lf.frequency.setTargetAtTime(safeFreq, eng.ctx.currentTime, 0.02); });
    eng._lpBaseValue = safeFreq;
    // Clamp any active LFO gains targeting filter so they can't push below 30Hz
    var maxDepth = safeFreq - 30;
    if (eng._lfoGain && eng._lfoGain.gain.value > maxDepth) {
      eng._lfoGain.gain.setTargetAtTime(maxDepth, eng.ctx.currentTime, 0.02);
    }
    if (eng._lfoOffsets) {
      Object.keys(eng._lfoOffsets).forEach(function(k) {
        if (LFO_DESTS[k] === "lp.freq") {
          var n = eng._lfoOffsets[k];
          if (n && n.gain && n.gain.value > maxDepth) {
            n.gain.setTargetAtTime(maxDepth, eng.ctx.currentTime, 0.02);
          }
        }
      });
    }
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
    var camLfoDepth = Math.min((100 + chromaContrast * 500) * luma, (eng._lpBaseValue||2000) - 30);
    eng._lfoGain.gain.setTargetAtTime(Math.max(0, camLfoDepth), t, 0.3);
  };

  eng.setSoundOn = function(on) {
    if (!eng.ctx) return;
    eng.ctx.resume();
    var t = eng.ctx.currentTime;
    eng.masterGain.gain.cancelScheduledValues(t);
    if (on) {
      eng.masterGain.gain.setValueAtTime(0, t);
      eng.masterGain.gain.linearRampToValueAtTime(0.7, t + 0.08);
      setTimeout(function(){ applyFxToEngine(fxSettings, seqSettings.bpm); }, 100);
    } else {
      eng.masterGain.gain.setValueAtTime(eng.masterGain.gain.value, t);
      eng.masterGain.gain.linearRampToValueAtTime(0, t + 0.08);
    }
    eng.active = on;
    if (on) eng.initUserLFOs();
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


  // ── User LFOs ────────────────────────────────────────────────────────────────
  // Each destination gets a dedicated offset GainNode that sums with the
  // camera/ribbon signal at the AudioParam level — no conflict possible.
  eng._lfoOffsets = {}; // dest key → GainNode already connected to param

  eng._getOrCreateOffset = function(dest) {
    if (eng._lfoOffsets[dest]) return eng._lfoOffsets[dest];
    var d = LFO_DESTS[dest];
    if (!d) return null;
    var param = null;
    if (d === "lp.freq")     param = eng._lpBase ? eng._lpBase.offset : (eng.lowpassNode ? eng.lowpassNode.frequency : null);
    if (d === "lp.q")        param = eng.lowpassNode ? eng.lowpassNode.Q : null; // Note: lowpassNode2.Q set separately
    if (d === "reverb.gain") param = eng.reverbGain ? eng.reverbGain.gain : null;
    if (d === "master.gain") param = eng.preReverbGain ? eng.preReverbGain.gain : null;
    if (d === "haas.gain")   param = (eng.oscR && eng.oscR.haasGain) ? eng.oscR.haasGain.gain : null;
    if (d === "fm.depth")    param = (eng.oscR && eng.oscR.fmIndex) ? eng.oscR.fmIndex.gain : null;
    if (d === "fm.r")        param = (eng.oscR && eng.oscR.fmIndex) ? eng.oscR.fmIndex.gain : null;
    if (d === "fm.g")        param = (eng.oscG && eng.oscG.fmIndex) ? eng.oscG.fmIndex.gain : null;
    if (d === "fm.b")        param = (eng.oscB && eng.oscB.fmIndex) ? eng.oscB.fmIndex.gain : null;
    if (!param) return null;
    // Create a gain node that adds to this param — LFO connects here
    var offset = eng.ctx.createGain();
    offset.gain.value = 1; // pass-through, depth controlled by lfo gain
    offset.connect(param);
    eng._lfoOffsets[dest] = offset;
    return offset;
  };

  eng._makeLFONode = function(cfg) {
    if (!eng.ctx) return null;
    var wave = cfg.wave || "sine";
    var node = { wave: wave, currentDest: null, shTimer: null };
    if (wave === "s&h") {
      // S&H: setInterval fires at rate, picks random value, ramps to it
      var shGain = eng.ctx.createGain();
      shGain.gain.value = 0;
      node.gain = shGain;
      node.osc  = null;
      // timer started in applyUserLFO
    } else {
      var osc = eng.ctx.createOscillator();
      osc.setPeriodicWave(eng.makeLFOWave(wave === "square" ? 1 : 0));
      osc.frequency.value = cfg.rate || 0.5;
      var gain = eng.ctx.createGain();
      gain.gain.value = 0;
      osc.connect(gain);
      osc.start();
      node.osc  = osc;
      node.gain = gain;
    }
    return node;
  };

  eng.initUserLFOs = function() {
    if (!eng.ctx) return;
    var s = eng.settings;
    if (!eng.lfo1) eng.lfo1 = eng._makeLFONode(s.lfo1);
    if (!eng.lfo2) eng.lfo2 = eng._makeLFONode(s.lfo2);
    eng.applyUserLFO("lfo1");
    eng.applyUserLFO("lfo2");
  };

  eng.applyUserLFO = function(key) {
    var node = eng[key];
    var cfg  = eng.settings[key];
    if (!node || !cfg || !eng.ctx) return;
    var t    = eng.ctx.currentTime;
    var wave = cfg.wave || "sine";
    var rate = Math.max(0.01, cfg.rate || 0.5);
    var active = cfg.active && cfg.depth > 0;

    // Update oscillator if not S&H
    if (node.osc) {
      node.osc.frequency.setTargetAtTime(rate, t, 0.1);
      try { node.osc.setPeriodicWave(eng.makeLFOWave(wave === "square" ? 1 : 0)); } catch(e) {}
    }

    // Reconnect to destination if changed
    if (node.currentDest !== cfg.dest) {
      try { node.gain.disconnect(); } catch(e) {}
      node.currentDest = null;
    }
    var offsetNode = active ? eng._getOrCreateOffset(cfg.dest) : null;
    if (offsetNode && node.currentDest !== cfg.dest) {
      node.gain.connect(offsetNode);
      node.currentDest = cfg.dest;
    } else if (!active && node.currentDest) {
      try { node.gain.disconnect(); } catch(e) {}
      node.currentDest = null;
    }

    // Depth scaling per destination
    var depthScale = 1;
    var d = LFO_DESTS[cfg.dest];
    if (d === "lp.freq")     depthScale = 4000; // ±4000Hz max
    if (d === "lp.q")        depthScale = 5;    // ±5 Q
    if (d === "reverb.gain") depthScale = 0.4;
    if (d === "master.gain") depthScale = 0.3;
    if (d === "haas.gain")   depthScale = 0.5;
    if (d && d.indexOf("fm") === 0) depthScale = 200; // FM index offset

    var depth = active ? (cfg.depth || 0) * depthScale : 0;
    node.gain.gain.setTargetAtTime(depth, t, 0.05);

    // S&H timer management
    if (node.shTimer) { clearInterval(node.shTimer); node.shTimer = null; }
    if (wave === "s&h" && active) {
      var intervalMs = Math.max(50, 1000 / rate);
      node.shTimer = setInterval(function() {
        if (!eng.ctx || !node.currentDest) return;
        var rnd = (Math.random() * 2 - 1); // -1..1
        node.gain.gain.setTargetAtTime(rnd * depth, eng.ctx.currentTime, 0.01);
      }, intervalMs);
    }
  };

  eng.destroyUserLFOs = function() {
    ["lfo1","lfo2"].forEach(function(k) {
      var l = eng[k];
      if (!l) return;
      if (l.shTimer) clearInterval(l.shTimer);
      if (l.osc) { try { l.osc.stop(); l.osc.disconnect(); } catch(e) {} }
      try { l.gain.disconnect(); } catch(e) {}
      eng[k] = null;
    });
    // Clean up offset nodes
    Object.keys(eng._lfoOffsets).forEach(function(k) {
      try { eng._lfoOffsets[k].disconnect(); } catch(e) {}
    });
    eng._lfoOffsets = {};
  };

  eng.destroy = function() {
    eng.panic();
    eng.destroyUserLFOs();
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
    reverbNode: null, reverbGain: null, fxLoCut: null, fxHiCut: null,
    masterGain: null,
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
    fmR: null, fmG: null, fmB: null,
    lfo1: null, lfo2: null,
    // FM modulator shape per oscillator (0=sine, 0.5=tri, 1=square)
    fmModShapeR: 0, fmModShapeG: 0, fmModShapeB: 0,
    _crossGains: [],
    _normAlpha: 0.02,      // how fast min/max tracks (per frame)
    _normMinSpread: 0.04,  // minimum spread to avoid noise amplification
    settings: {
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72, reverbMix: 0.3, fps: 10,
      showScales: false,
      intervalR: "1×2",
      intervalG: "3×2",
      intervalB: "5×4",
      glide: 200,
      cmR: "1:1", cmG: "1:1", cmB: "1:1",
      fmDepth: 0.4,
      fmModShape: 0, // global modulator shape (0=sine, 0.5=tri, 1=square)
      lfo1: { rate:0.5, depth:0, wave:"sine", dest:"filter cutoff", active:false },
      lfo2: { rate:0.2, depth:0, wave:"sine", dest:"filter Q",      active:false },
    },
  };

  eng.init = function() {
    if (eng.ctx) return;
    try {
      var AC = window.AudioContext || window.webkitAudioContext;
      eng.ctx = new AC();
      var sr  = eng.ctx.sampleRate;
      // Convolution reverb
      var buf = eng.ctx.createBuffer(2, REVERB_IR.len, eng.ctx.sampleRate);
      buf.getChannelData(0).set(REVERB_IR.L);
      buf.getChannelData(1).set(REVERB_IR.R);
      eng.reverbNode = eng.ctx.createConvolver();
      eng.reverbNode.buffer = buf;
      eng.reverbGain = eng.ctx.createGain(); eng.reverbGain.gain.value = 0;
      eng.dryGain    = eng.ctx.createGain(); eng.dryGain.gain.value = 1;

      // Comb + lowpass (identical to engine 1)
      var N = 8; eng.combFilters = [];
      for (var ci = 0; ci < N; ci++) {
        var f = eng.ctx.createBiquadFilter();
        f.type = "peaking"; f.frequency.value = 200*(ci+1); f.Q.value = 3; f.gain.value = 0;
        eng.combFilters.push(f);
      }
      for (var ci = 0; ci < N-1; ci++) eng.combFilters[ci].connect(eng.combFilters[ci+1]);
      eng.combSidePanL = eng.ctx.createStereoPanner(); eng.combSidePanL.pan.value = -0.6;
      eng.combSidePanR = eng.ctx.createStereoPanner(); eng.combSidePanR.pan.value =  0.6;
      eng.combSideGain = eng.ctx.createGain(); eng.combSideGain.gain.value = 0.5;
      for (var ci = 4; ci < N; ci++) eng.combFilters[ci].connect(eng.combSideGain);
      eng.combSideGain.connect(eng.combSidePanL);
      eng.combSideGain.connect(eng.combSidePanR);


      // 4-pole ladder filter (Moog-style approximation)
      // 4 × 1-pole lowpass stages in series + resonance feedback
      eng.ladder = [];
      for (var li = 0; li < 4; li++) {
        var lf = eng.ctx.createBiquadFilter();
        lf.type = "lowpass";
        lf.frequency.value = 2000;
        lf.Q.value = 0.5; // flat 1-pole response per stage
        eng.ladder.push(lf);
      }
      for (var li = 0; li < 3; li++) eng.ladder[li].connect(eng.ladder[li+1]);
      // Resonance feedback: output → feedbackGain → input
      eng.ladderFb = eng.ctx.createGain();
      eng.ladderFb.gain.value = 0;
      // Invert feedback for stability (subtract from input)
      eng.ladderFbInv = eng.ctx.createGain();
      eng.ladderFbInv.gain.value = -1;
      eng.ladder[3].connect(eng.ladderFb);
      eng.ladderFb.connect(eng.ladderFbInv);
      eng.ladderFbInv.connect(eng.ladder[0]);
      // ladder[0] = lowpassNode for compatibility
      eng.lowpassNode  = eng.ladder[0];
      eng.lowpassNode2 = eng.ladder[3]; // output stage
      eng.combFilters[N-1].connect(eng.lowpassNode);
      eng.combSidePanL.connect(eng.lowpassNode);
      eng.combSidePanR.connect(eng.lowpassNode);

      eng.preReverbGain = eng.ctx.createGain();
      eng.preReverbGain.gain.value = 1.0;

      eng.seqAmpGain = eng.ctx.createGain();
      eng.seqAmpGain.gain.value = 1.0;

      eng.masterGain = eng.ctx.createGain(); eng.masterGain.gain.value = 0;

      eng.limiterNode = eng.ctx.createDynamicsCompressor();
      eng.limiterNode.threshold.value = -3; eng.limiterNode.knee.value = 0;
      eng.limiterNode.ratio.value = 20; eng.limiterNode.attack.value = 0.001; eng.limiterNode.release.value = 0.1;

      eng.analyserNode = eng.ctx.createAnalyser(); eng.analyserNode.fftSize = 1024;

      eng.delayL    = eng.ctx.createDelay(4.0);
      eng.delayR    = eng.ctx.createDelay(4.0);
      eng.delayL.delayTime.value = 0.25;
      eng.delayR.delayTime.value = 0.25;
      eng.fbGain    = eng.ctx.createGain(); eng.fbGain.gain.value = 0;
      eng.delayWetL = eng.ctx.createStereoPanner(); eng.delayWetL.pan.value = -1;
      eng.delayWetR = eng.ctx.createStereoPanner(); eng.delayWetR.pan.value =  1;
      eng.delayWet  = eng.ctx.createGain(); eng.delayWet.gain.value = 0;
      eng.delayDry  = eng.ctx.createGain(); eng.delayDry.gain.value = 1;

      // seqAmpGain → delayL (for delay processing)
      // seqAmpGain → delayDry connected in chain below
      eng.crossGain = eng.ctx.createGain();
      eng.crossGain.gain.value = 0;
      eng.seqAmpGain.connect(eng.delayL);
      eng.delayL.connect(eng.delayWetL);
      eng.delayL.connect(eng.crossGain);
      eng.crossGain.connect(eng.delayR);
      eng.delayR.connect(eng.delayWetR);
      eng.delayR.connect(eng.fbGain);
      eng.fbGain.connect(eng.delayL);
      eng.delayWetL.connect(eng.delayWet);
      eng.delayWetR.connect(eng.delayWet);

      eng.lowpassNode.connect(eng.preReverbGain);
      eng.preReverbGain.connect(eng.seqAmpGain);
      // Signal chain: seqAmpGain → dry+wet delay → master
      // Diffusion on wet output: each repeat gets all-pass smeared
      // Send routing: dry always full, reverb adds on top
      eng.seqAmpGain.connect(eng.delayDry);
      // dry → master (clean, unfiltered)
      eng.delayDry.connect(eng.masterGain);
      eng.delayWet.connect(eng.masterGain);
      // reverb send: delay → filters → reverb
      eng.fxLoCut = eng.ctx.createBiquadFilter();
      eng.fxLoCut.type = 'highpass'; eng.fxLoCut.frequency.value = 20; eng.fxLoCut.Q.value = 0.5;
      eng.fxHiCut = eng.ctx.createBiquadFilter();
      eng.fxHiCut.type = 'lowpass'; eng.fxHiCut.frequency.value = 20000; eng.fxHiCut.Q.value = 0.5;
      eng.delayDry.connect(eng.fxLoCut);
      eng.delayWet.connect(eng.fxLoCut);
      eng.fxLoCut.connect(eng.fxHiCut);
      eng.fxHiCut.connect(eng.reverbNode);
      eng.reverbNode.connect(eng.reverbGain);
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

  // Create one RGB oscillator voice with FM modulator
  // Returns { osc, fmMod, fmIndex, gainNode, directPan, haasDelay, haasGain, haasPan }
  eng.makeOscVoice = function(freq, panPos, cmRatio) {
    // ── FM Modulator (sine) ──
    var fmMod   = eng.ctx.createOscillator();
    fmMod.type  = "sine";
    fmMod.frequency.value = freq * (cmRatio || 1.0);

    // FM index gain — controls depth of frequency modulation
    // index × carrier frequency = max frequency deviation
    var fmIndex = eng.ctx.createGain();
    fmIndex.gain.value = 0; // start with no FM

    fmMod.connect(fmIndex);
    // fmIndex output connects to carrier frequency AudioParam
    // (wired after osc creation below)

    // ── Carrier oscillator ──
    var osc = eng.ctx.createOscillator();
    osc.frequency.value = freq;
    osc.setPeriodicWave(eng.makeMorphWave(0)); // start as sine

    // Wire FM modulator to carrier frequency
    fmIndex.connect(osc.frequency);

    var gainNode = eng.ctx.createGain();
    gainNode.gain.value = 0.35;

    var directPan = eng.ctx.createStereoPanner();
    directPan.pan.value = panPos * -0.4;

    var haasDelay = eng.ctx.createDelay(0.05);
    haasDelay.delayTime.value = 0.015;
    var haasGain = eng.ctx.createGain(); haasGain.gain.value = 0;
    var haasPan  = eng.ctx.createStereoPanner();
    haasPan.pan.value = panPos * 0.8;

    osc.connect(gainNode);
    gainNode.connect(directPan);
    directPan.connect(eng.combFilters[0]);
    gainNode.connect(haasDelay);
    haasDelay.connect(haasGain);
    haasGain.connect(haasPan);
    haasPan.connect(eng.combFilters[0]);

    fmMod.start();
    osc.start();
    return { osc: osc, fmMod: fmMod, fmIndex: fmIndex, gainNode: gainNode,
             directPan: directPan, haasDelay: haasDelay, haasGain: haasGain, haasPan: haasPan };
  };

  eng.spawnOscillators = function() {
    ['oscR','oscG','oscB'].forEach(function(k) {
      var v = eng[k];
      if (!v) return;
      try {
        v.fmMod.stop(); v.fmMod.disconnect();
        v.fmIndex.disconnect();
        v.osc.stop(); v.osc.disconnect();
        v.gainNode.disconnect(); v.directPan.disconnect();
        v.haasDelay.disconnect(); v.haasGain.disconnect(); v.haasPan.disconnect();
      } catch(e) {}
      eng[k] = null;
    });

    var baseHz = midiToHz(eng.currentPitchMidi);
    var s = eng.settings;
    var rHz = baseHz * INTERVALS[s.intervalR];
    var gHz = baseHz * INTERVALS[s.intervalG];
    var bHz = baseHz * INTERVALS[s.intervalB];

    eng.oscR = eng.makeOscVoice(rHz,  1, CM_RATIOS[s.cmR]);
    eng.oscG = eng.makeOscVoice(gHz,  0, CM_RATIOS[s.cmG]);
    eng.oscB = eng.makeOscVoice(bHz, -1, CM_RATIOS[s.cmB]);

    // Wire cross-modulation for current matrix
    eng.wireFmMatrix();

    // Reconnect LFOs to fresh oscillator nodes
    if (eng.lfo1 || eng.lfo2) {
      eng.destroyUserLFOs();
      eng.initUserLFOs();
    }
  };

  // ── FM Matrix cross-modulation wiring ─────────────────────
  // Each matrix adds carrier→frequency connections on top of
  // the internal fmMod→carrier connections (which always exist)
  // Cross-gain depth: scaled by fmDepth setting
  eng.wireFmMatrix = function() {
    var matrix = eng.settings.fmMatrix || "A";

    // Destroy old cross gains
    if (eng._crossGains) {
      eng._crossGains.forEach(function(g) { try { g.disconnect(); } catch(e) {} });
    }
    eng._crossGains = [];
    eng._crossMap = [];

    if (!eng.oscR || !eng.oscG || !eng.oscB) return;

    // Re-connect all voices to audio output first (reset from previous matrix)
    ['oscR','oscG','oscB'].forEach(function(k) {
      var v = eng[k]; if (!v) return;
      try { v.gainNode.disconnect(); } catch(e) {}
      try { v.haasPan.disconnect(); } catch(e) {}
    });
    // Default: all connected to combFilters
    eng.oscR.gainNode.connect(eng.oscR.directPan);
    eng.oscR.directPan.connect(eng.combFilters[0]);
    eng.oscR.gainNode.connect(eng.oscR.haasDelay);
    eng.oscR.haasDelay.connect(eng.oscR.haasGain);
    eng.oscR.haasGain.connect(eng.oscR.haasPan);
    eng.oscR.haasPan.connect(eng.combFilters[0]);

    eng.oscG.gainNode.connect(eng.oscG.directPan);
    eng.oscG.directPan.connect(eng.combFilters[0]);
    eng.oscG.gainNode.connect(eng.oscG.haasDelay);
    eng.oscG.haasDelay.connect(eng.oscG.haasGain);
    eng.oscG.haasGain.connect(eng.oscG.haasPan);
    eng.oscG.haasPan.connect(eng.combFilters[0]);

    eng.oscB.gainNode.connect(eng.oscB.directPan);
    eng.oscB.directPan.connect(eng.combFilters[0]);
    eng.oscB.gainNode.connect(eng.oscB.haasDelay);
    eng.oscB.haasDelay.connect(eng.oscB.haasGain);
    eng.oscB.haasGain.connect(eng.oscB.haasPan);
    eng.oscB.haasPan.connect(eng.combFilters[0]);

    function makeCrossCarrier(srcVoice, destVoice, srcCh) {
      // carrier_src → crossGain → carrier_dest.frequency
      var g = eng.ctx.createGain();
      g.gain.value = 0;
      srcVoice.osc.connect(g);
      g.connect(destVoice.osc.frequency);
      eng._crossGains.push(g);
      eng._crossMap.push({ gain: g, srcCh: srcCh, destVoice: destVoice, useCarrier: true });
    }

    function silence(voice) {
      try { voice.gainNode.disconnect(); } catch(e) {}
      try { voice.haasPan.disconnect(); } catch(e) {}
    }

    function centerPan(voice) {
      // Center direct path only — Haas pan stays for stereo width
      var t = eng.ctx.currentTime;
      voice.directPan.pan.setTargetAtTime(0, t, 0.05);
      // haasPan keeps its original position (±0.8) for Haas-based stereo spread
    }

    if (matrix === "A") {
      // Independent — all audible, no cross connections

    } else if (matrix === "B") {
      silence(eng.oscR);
      silence(eng.oscG);
      centerPan(eng.oscB); // B is soloed — center it
      makeCrossCarrier(eng.oscR, eng.oscG, "r");
      makeCrossCarrier(eng.oscG, eng.oscB, "g");

    } else if (matrix === "D") {
      // G as master modulator: G carrier → R freq and B freq
      silence(eng.oscG);
      makeCrossCarrier(eng.oscG, eng.oscR, "g");
      makeCrossCarrier(eng.oscG, eng.oscB, "g");
    } else if (matrix === "C") {
      silence(eng.oscB);
      silence(eng.oscG);
      centerPan(eng.oscR); // R is soloed — center it
      makeCrossCarrier(eng.oscB, eng.oscG, "b");
      makeCrossCarrier(eng.oscG, eng.oscR, "g");
    }
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

    // Quantize ratio to nearest scale degree if quantize on
    function ratioToQuantized(ratio) {
      var targetHz   = baseHz * ratio;
      var targetMidi = 69 + 12 * Math.log2(targetHz / 440);
      var qMidi      = quantizePitch(Math.round(targetMidi), s.scale, s.rootNote);
      return midiToHz(qMidi) / baseHz;
    }
    if (s.quantize) {
      rRatio = ratioToQuantized(rRatio);
      gRatio = ratioToQuantized(gRatio);
      bRatio = ratioToQuantized(bRatio);
    }

    var glide = glideTC > 0.001 ? glideTC : 0.01;
    if (eng.oscR) {
      eng.oscR.osc.frequency.setTargetAtTime(baseHz * rRatio, t, glide);
      eng.oscR.fmMod.frequency.setTargetAtTime(baseHz * rRatio * CM_RATIOS[s.cmR], t, glide);
    }
    if (eng.oscG) {
      eng.oscG.osc.frequency.setTargetAtTime(baseHz * gRatio, t, glide);
      eng.oscG.fmMod.frequency.setTargetAtTime(baseHz * gRatio * CM_RATIOS[s.cmG], t, glide);
    }
    if (eng.oscB) {
      eng.oscB.osc.frequency.setTargetAtTime(baseHz * bRatio, t, glide);
      eng.oscB.fmMod.frequency.setTargetAtTime(baseHz * bRatio * CM_RATIOS[s.cmB], t, glide);
    }
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
    // Cube curve — balance between too-sine (x⁴) and too-square (x²)
    var rMorph = avgR * avgR * avgR;
    var gMorph = avgG * avgG * avgG;
    var bMorph = avgB * avgB * avgB;
    if (eng.oscR) { try { eng.oscR.osc.setPeriodicWave(eng.makeMorphWave(rMorph)); } catch(e) {} }
    if (eng.oscG) { try { eng.oscG.osc.setPeriodicWave(eng.makeMorphWave(gMorph)); } catch(e) {} }
    if (eng.oscB) { try { eng.oscB.osc.setPeriodicWave(eng.makeMorphWave(bMorph)); } catch(e) {} }
    // FM modulator shape — user controlled, updated from settings
    var fmShape = eng.settings.fmModShape || 0;
    if (fmShape !== eng.fmModShapeR) {
      eng.fmModShapeR = fmShape;
      if (eng.oscR) try { eng.oscR.fmMod.setPeriodicWave(eng.makeLFOWave(fmShape)); } catch(e) {}
      if (eng.oscG) try { eng.oscG.fmMod.setPeriodicWave(eng.makeLFOWave(fmShape)); } catch(e) {}
      if (eng.oscB) try { eng.oscB.fmMod.setPeriodicWave(eng.makeLFOWave(fmShape)); } catch(e) {}
    }

    // Haas stereo width: relative color magnitude → width
    var rWidth = Math.min(1, Math.abs(relR) * 8);
    var gWidth = Math.min(1, Math.abs(relG) * 8);
    var bWidth = Math.min(1, Math.abs(relB) * 8);
    var matrix = eng.settings.fmMatrix || "A";
    if (matrix === "B" || matrix === "C") {
      // Soloed carrier — derive width from combined color deviation of all channels
      var combinedWidth = Math.min(1, (Math.abs(relR) + Math.abs(relG) + Math.abs(relB)) / 3 * 8);
      var soloVoice = matrix === "B" ? eng.oscB : eng.oscR;
      if (soloVoice && soloVoice.haasGain) {
        soloVoice.haasGain.gain.setTargetAtTime(combinedWidth * 0.7, t, 0.2);
      }
    } else {
      if (eng.oscR && eng.oscR.haasGain) eng.oscR.haasGain.gain.setTargetAtTime(rWidth * 0.7, t, 0.2);
      if (eng.oscG && eng.oscG.haasGain) eng.oscG.haasGain.gain.setTargetAtTime(gWidth * 0.7, t, 0.2);
      if (eng.oscB && eng.oscB.haasGain) eng.oscB.haasGain.gain.setTargetAtTime(bWidth * 0.7, t, 0.2);
    }

    // FM index: channel brightness × fmDepth × carrier frequency
    // This scales the frequency deviation with the carrier so it stays
    // musically proportional regardless of pitch
    var fmD = eng.settings.fmDepth || 0.4;
    var baseHz = midiToHz(eng.currentPitchMidi);
    var rCarrHz = baseHz * INTERVALS[eng.settings.intervalR];
    var gCarrHz = baseHz * INTERVALS[eng.settings.intervalG];
    var bCarrHz = baseHz * INTERVALS[eng.settings.intervalB];
    if (eng.oscR && eng.oscR.fmIndex) eng.oscR.fmIndex.gain.setTargetAtTime(avgR * fmD * rCarrHz, t, 0.15);
    if (eng.oscG && eng.oscG.fmIndex) eng.oscG.fmIndex.gain.setTargetAtTime(avgG * fmD * gCarrHz, t, 0.15);
    if (eng.oscB && eng.oscB.fmIndex) eng.oscB.fmIndex.gain.setTargetAtTime(avgB * fmD * bCarrHz, t, 0.15);

    // Update cross-modulation gains dynamically
    if (eng._crossMap && eng._crossMap.length) {
      var avgMap = { r: avgR, g: avgG, b: avgB };
      eng._crossMap.forEach(function(c) {
        var srcAvg = avgMap[c.srcCh] || 0;
        var destHz = c.destVoice.osc.frequency.value;
        // Carrier-as-modulator: scale like FM index — brightness × depth × destHz
        var depth  = srcAvg * fmD * destHz * 0.5; // 0.5 to keep in musical range
        c.gain.gain.setTargetAtTime(depth, t, 0.1);
      });
    }
  };

  eng.makeLFOWave = function(shape) {
    // shape: 0=sine, 0.5=triangle, 1=square — all bandlimited via PeriodicWave
    var size = 256;
    var real = new Float32Array(size / 2);
    var imag = new Float32Array(size / 2);
    imag[1] = 1.0; // fundamental always
    for (var n = 3; n < size / 2; n += 2) {
      var sinePart = 0;
      var triPart  = (8 / (Math.PI * Math.PI)) * (1 / (n * n)) * (n % 4 === 1 ? 1 : -1);
      var sqPart   = 1 / n;
      if (shape <= 0.5) {
        // sine → triangle
        var t = shape * 2;
        imag[n] = triPart * t;
      } else {
        // triangle → square
        var t = (shape - 0.5) * 2;
        var triVal = (8 / (Math.PI * Math.PI)) * (1 / (n * n)) * (n % 4 === 1 ? 1 : -1);
        imag[n] = triVal * (1 - t) + sqPart * t;
      }
    }
    return eng.ctx.createPeriodicWave(real, imag, { disableNormalization: false });
  };

  eng.initLFO = function() {
    if (!eng.ctx || eng._lfoNode) return;
    if (!eng._lpBase) {
      eng._lpBase = eng.ctx.createConstantSource();
      eng._lpBase.offset.value = 2000;
      eng.ladder.forEach(function(lf){ eng._lpBase.connect(lf.frequency); });
      eng._lpBase.start();
    }
    eng._lfoNode = eng.ctx.createOscillator();
    eng._lfoNode.setPeriodicWave(eng.makeLFOWave(0));
    eng._lfoNode.frequency.value = 0.2;
    eng._lfoGain = eng.ctx.createGain();
    eng._lfoGain.gain.value = 0;
    eng._lfoNode.connect(eng._lfoGain);
    if (eng._lpBase) {
      eng._lfoGain.connect(eng._lpBase.offset);
    } else {
      if (eng.ladder) { eng.ladder.forEach(function(lf){ eng._lfoGain.connect(lf.frequency); }); } else { eng._lfoGain.connect(eng.lowpassNode.frequency); }
    }
    eng._lfoNode.start();
  };

  eng.setLpFreq = function(freq) {
    var safeFreq = Math.max(20, Math.min(20000, freq));
    if (eng._lpBase) {
      eng._lpBase.offset.setTargetAtTime(safeFreq, eng.ctx.currentTime, 0.02);
    } else {
      eng.lowpassNode.frequency.setTargetAtTime(safeFreq, eng.ctx.currentTime, 0.02);
    }
    if (eng.ladder) eng.ladder.forEach(function(lf){ lf.frequency.setTargetAtTime(safeFreq, eng.ctx.currentTime, 0.02); });
    eng._lpBaseValue = safeFreq;
    var maxDepth = Math.max(0, safeFreq - 20);
    if (eng._lfoGain && eng._lfoGain.gain.value > maxDepth) {
      eng._lfoGain.gain.setTargetAtTime(maxDepth, eng.ctx.currentTime, 0.02);
    }
    if (eng._lfoOffsets) {
      Object.keys(eng._lfoOffsets).forEach(function(k) {
        if (LFO_DESTS[k] === "lp.freq") {
          var n = eng._lfoOffsets[k];
          if (n && n.gain && n.gain.value > maxDepth) {
            n.gain.setTargetAtTime(maxDepth, eng.ctx.currentTime, 0.02);
          }
        }
      });
    }
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
    var t = eng.ctx.currentTime;
    eng.masterGain.gain.cancelScheduledValues(t);
    if (on) {
      eng.masterGain.gain.setValueAtTime(0, t);
      eng.masterGain.gain.linearRampToValueAtTime(0.7, t + 0.08);
      setTimeout(function(){ applyFxToEngine(fxSettings, seqSettings.bpm); }, 100);
    } else {
      eng.masterGain.gain.setValueAtTime(eng.masterGain.gain.value, t);
      eng.masterGain.gain.linearRampToValueAtTime(0, t + 0.08);
    }
    eng.active = on;
    if (on) eng.initUserLFOs();
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


  // ── User LFOs ────────────────────────────────────────────────────────────────
  // Each destination gets a dedicated offset GainNode that sums with the
  // camera/ribbon signal at the AudioParam level — no conflict possible.
  eng._lfoOffsets = {}; // dest key → GainNode already connected to param

  eng._getOrCreateOffset = function(dest) {
    if (eng._lfoOffsets[dest]) return eng._lfoOffsets[dest];
    var d = LFO_DESTS[dest];
    if (!d) return null;
    var param = null;
    if (d === "lp.freq")     param = eng._lpBase ? eng._lpBase.offset : (eng.lowpassNode ? eng.lowpassNode.frequency : null);
    if (d === "lp.q")        param = eng.lowpassNode ? eng.lowpassNode.Q : null; // Note: lowpassNode2.Q set separately
    if (d === "reverb.gain") param = eng.reverbGain ? eng.reverbGain.gain : null;
    if (d === "master.gain") param = eng.preReverbGain ? eng.preReverbGain.gain : null;
    if (d === "haas.gain")   param = (eng.oscR && eng.oscR.haasGain) ? eng.oscR.haasGain.gain : null;
    if (d === "fm.depth")    param = (eng.oscR && eng.oscR.fmIndex) ? eng.oscR.fmIndex.gain : null;
    if (d === "fm.r")        param = (eng.oscR && eng.oscR.fmIndex) ? eng.oscR.fmIndex.gain : null;
    if (d === "fm.g")        param = (eng.oscG && eng.oscG.fmIndex) ? eng.oscG.fmIndex.gain : null;
    if (d === "fm.b")        param = (eng.oscB && eng.oscB.fmIndex) ? eng.oscB.fmIndex.gain : null;
    if (!param) return null;
    // Create a gain node that adds to this param — LFO connects here
    var offset = eng.ctx.createGain();
    offset.gain.value = 1; // pass-through, depth controlled by lfo gain
    offset.connect(param);
    eng._lfoOffsets[dest] = offset;
    return offset;
  };

  eng._makeLFONode = function(cfg) {
    if (!eng.ctx) return null;
    var wave = cfg.wave || "sine";
    var node = { wave: wave, currentDest: null, shTimer: null };
    if (wave === "s&h") {
      // S&H: setInterval fires at rate, picks random value, ramps to it
      var shGain = eng.ctx.createGain();
      shGain.gain.value = 0;
      node.gain = shGain;
      node.osc  = null;
      // timer started in applyUserLFO
    } else {
      var osc = eng.ctx.createOscillator();
      osc.setPeriodicWave(eng.makeLFOWave(wave === "square" ? 1 : 0));
      osc.frequency.value = cfg.rate || 0.5;
      var gain = eng.ctx.createGain();
      gain.gain.value = 0;
      osc.connect(gain);
      osc.start();
      node.osc  = osc;
      node.gain = gain;
    }
    return node;
  };

  eng.initUserLFOs = function() {
    if (!eng.ctx) return;
    var s = eng.settings;
    if (!eng.lfo1) eng.lfo1 = eng._makeLFONode(s.lfo1);
    if (!eng.lfo2) eng.lfo2 = eng._makeLFONode(s.lfo2);
    eng.applyUserLFO("lfo1");
    eng.applyUserLFO("lfo2");
  };

  eng.applyUserLFO = function(key) {
    var node = eng[key];
    var cfg  = eng.settings[key];
    if (!node || !cfg || !eng.ctx) return;
    var t    = eng.ctx.currentTime;
    var wave = cfg.wave || "sine";
    var rate = Math.max(0.01, cfg.rate || 0.5);
    var active = cfg.active && cfg.depth > 0;

    // Update oscillator if not S&H
    if (node.osc) {
      node.osc.frequency.setTargetAtTime(rate, t, 0.1);
      try { node.osc.setPeriodicWave(eng.makeLFOWave(wave === "square" ? 1 : 0)); } catch(e) {}
    }

    // Reconnect to destination if changed
    if (node.currentDest !== cfg.dest) {
      try { node.gain.disconnect(); } catch(e) {}
      node.currentDest = null;
    }
    var offsetNode = active ? eng._getOrCreateOffset(cfg.dest) : null;
    if (offsetNode && node.currentDest !== cfg.dest) {
      node.gain.connect(offsetNode);
      node.currentDest = cfg.dest;
    } else if (!active && node.currentDest) {
      try { node.gain.disconnect(); } catch(e) {}
      node.currentDest = null;
    }

    // Depth scaling per destination
    var depthScale = 1;
    var d = LFO_DESTS[cfg.dest];
    if (d === "lp.freq")     depthScale = 4000; // ±4000Hz max
    if (d === "lp.q")        depthScale = 5;    // ±5 Q
    if (d === "reverb.gain") depthScale = 0.4;
    if (d === "master.gain") depthScale = 0.3;
    if (d === "haas.gain")   depthScale = 0.5;
    if (d && d.indexOf("fm") === 0) depthScale = 200; // FM index offset

    var depth = active ? (cfg.depth || 0) * depthScale : 0;
    node.gain.gain.setTargetAtTime(depth, t, 0.05);

    // S&H timer management
    if (node.shTimer) { clearInterval(node.shTimer); node.shTimer = null; }
    if (wave === "s&h" && active) {
      var intervalMs = Math.max(50, 1000 / rate);
      node.shTimer = setInterval(function() {
        if (!eng.ctx || !node.currentDest) return;
        var rnd = (Math.random() * 2 - 1); // -1..1
        node.gain.gain.setTargetAtTime(rnd * depth, eng.ctx.currentTime, 0.01);
      }, intervalMs);
    }
  };

  eng.destroyUserLFOs = function() {
    ["lfo1","lfo2"].forEach(function(k) {
      var l = eng[k];
      if (!l) return;
      if (l.shTimer) clearInterval(l.shTimer);
      if (l.osc) { try { l.osc.stop(); l.osc.disconnect(); } catch(e) {} }
      try { l.gain.disconnect(); } catch(e) {}
      eng[k] = null;
    });
    // Clean up offset nodes
    Object.keys(eng._lfoOffsets).forEach(function(k) {
      try { eng._lfoOffsets[k].disconnect(); } catch(e) {}
    });
    eng._lfoOffsets = {};
  };

  eng.destroy = function() {
    eng.panic();
    eng.destroyUserLFOs();
    if(eng._lfoNode){try{eng._lfoNode.stop();}catch(e){}}
    ['oscR','oscG','oscB'].forEach(function(k){
      if(!eng[k])return;
      try{eng[k].fmMod.stop();}catch(e){}
      try{eng[k].osc.stop();}catch(e){}
    });
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


// ══════════════════════════════════════════════════════════════════════════════
// SEQUENCER ENGINE
// Web Audio clock-accurate 1/16 note gate sequencer
// 3 ADSR envelopes: Amp (preReverbGain), Filter (lowpass offset), Free (assignable)
// ══════════════════════════════════════════════════════════════════════════════
function makeSequencer(getEngine) {
  var seq = {
    running: false,
    bpm: 120,
    steps: 16,
    pattern: new Array(16).fill(false),
    currentStep: -1,
    _scheduleAhead: 0.1,   // seconds ahead to schedule
    _lookahead: 25,         // ms between scheduler calls
    _nextStepTime: 0,
    _timerID: null,
    _currentStep: 0,
    // Envelope settings
    envAmp:    { a:10,  h:80,  r:300, enabled:true },  // h=hold % of step

    // Envelope gain nodes (created on first trigger)
    _ampEnvGain:    null,
    _filterEnvGain: null,
  };

  seq.stepDuration = function() {
    // 1/16 note in seconds
    return (60 / seq.bpm) / 4;
  };

  seq._initEnvNodes = function() {
    var eng = getEngine();
    if (!eng || !eng.ctx) return;
    // Amp envelope drives seqAmpGain directly
    seq._ampTarget = eng.seqAmpGain ? eng.seqAmpGain.gain : null;
    if (!seq._ampTarget) console.warn('[SEQ] seqAmpGain missing');
  };

  // _triggerEnv kept for potential future use
  seq._triggerEnv = function(envSettings, gainNode, time, gateOn, depthScale) {};

  seq._scheduleStep = function(stepIndex, time) {
    var eng = getEngine();
    if (!eng || !eng.ctx) return;
    var steps   = seq.steps;
    var gateOn  = seq.pattern[stepIndex % steps];
    var stepDur = seq.stepDuration();

    if (seq._ampTarget) {
      var g = seq._ampTarget;
      if (gateOn) {
        var a        = Math.max(0.002, seq.envAmp.a / 1000);
        var holdSec  = stepDur * Math.max(0, Math.min(1, seq.envAmp.h / 100));
        var r        = Math.max(0.01, Math.min(1.0, seq.envAmp.r / 1000));
        var releaseStart = time + a + holdSec;

        // Always trigger full AHR — consecutive steps pump/breathe based on A time
        // Short A = audible pumping between steps, long A = smooth legato
        g.cancelScheduledValues(time);
        g.setTargetAtTime(0, time, 0.001);              // soft zero at gate time
        g.linearRampToValueAtTime(1.0, time + a);       // attack
        g.setValueAtTime(1.0, releaseStart);            // hold
        g.linearRampToValueAtTime(0, releaseStart + r); // release

      } else {
        // Gate OFF step — ensure silence
        var r = Math.max(0.01, Math.min(1.0, seq.envAmp.r / 1000));
        g.cancelScheduledValues(time);
        g.setTargetAtTime(0, time, r / 3);
      }
    }
  };

  seq._scheduler = function() {
    var eng = getEngine();
    if (!eng || !eng.ctx) return;
    var ctx = eng.ctx;

    while (seq._nextStepTime < ctx.currentTime + seq._scheduleAhead) {
      seq._scheduleStep(seq._currentStep, seq._nextStepTime);
      seq._currentStep = (seq._currentStep + 1) % seq.steps;
      seq._nextStepTime += seq.stepDuration();
    }
  };

  seq.start = function() {
    var eng = getEngine();
    if (!eng || !eng.ctx || seq.running) return;
    seq._initEnvNodes();
    // Set initial amp state
    if (eng.seqAmpGain) {
      eng.seqAmpGain.gain.cancelScheduledValues(eng.ctx.currentTime);
      eng.seqAmpGain.gain.value = seq.envAmp.enabled ? 0 : 1.0;
    }
    seq.running = true;
    seq._currentStep = 0;
    seq._startTime    = eng.ctx.currentTime + 0.05;
    seq._nextStepTime = seq._startTime;
    seq._timerID = setInterval(seq._scheduler, seq._lookahead);
    seq._scheduler();
  };

  seq.stop = function() {
    seq.running = false;
    if (seq._timerID) { clearInterval(seq._timerID); seq._timerID = null; }
    var eng = getEngine();
    if (eng && eng.ctx) {
      var t = eng.ctx.currentTime;

      // Restore seqAmpGain to full open (drone resumes)
      if (eng.seqAmpGain) {
        var r = Math.max(0.05, Math.min(1.0, seq.envAmp.r / 1000));
        eng.seqAmpGain.gain.cancelScheduledValues(t);
        eng.seqAmpGain.gain.setValueAtTime(0, t);
        eng.seqAmpGain.gain.linearRampToValueAtTime(1.0, t + r);
      }
    }
  };

  seq.getCurrentStep = function() {
    if (!seq.running || seq._startTime === undefined) return -1;
    var eng = getEngine();
    if (!eng || !eng.ctx) return -1;
    var elapsed = eng.ctx.currentTime - seq._startTime;
    if (elapsed < 0) return 0;
    return Math.floor(elapsed / seq.stepDuration()) % seq.steps;
  };

  seq.destroy = function() {
    seq.stop();
    seq._ampTarget = null;
  };

  return seq;
}


// ── ADSR vertical ribbon slider component ────────────────────────────────────
function ADSRSlider(props) {
  // props: label, value, min, max, onChange
  var sliderRef = useRef(null);
  var dragRef   = useRef(null);

  function fmtV(v) {
    if (props.label === "H") return v + "%";
    return v < 1000 ? v + "ms" : (v / 1000).toFixed(1) + "s";
  }

  function onPD(e) {
    e.preventDefault(); e.stopPropagation();
    sliderRef.current && sliderRef.current.setPointerCapture(e.pointerId);
    var rect = sliderRef.current ? sliderRef.current.getBoundingClientRect() : { height: 90 };
    dragRef.current = { startY: e.clientY, startVal: props.value, height: Math.max(1, rect.height), range: props.max - props.min };
  }
  function onPM(e) {
    var d = dragRef.current; if (!d) return;
    var nv = Math.max(props.min, Math.min(props.max, d.startVal + (d.startY - e.clientY) / d.height * d.range));
    props.onChange(Math.round(nv));
  }
  function onPU() { dragRef.current = null; }

  var pct    = (props.value - props.min) / (props.max - props.min);
  var topPct = Math.round((1 - pct) * 100);

  return el("div", { style: { flex: 1, display: "flex", flexDirection: "column", alignItems: "center" } },
    el("span", { style: { fontSize: 8, color: "#444", letterSpacing: "0.1em", marginBottom: 3 } }, props.label),
    el("div", {
      ref: sliderRef,
      onPointerDown: onPD, onPointerMove: onPM, onPointerUp: onPU, onPointerCancel: onPU,
      style: { width: "100%", height: 55, position: "relative", borderRadius: 4, cursor: "ns-resize",
        background: "linear-gradient(180deg,rgba(127,255,106,0.12) 0%,rgba(127,255,106,0.02) 100%)",
        border: "1px solid #1a2a1a", userSelect: "none", WebkitUserSelect: "none", touchAction: "none" }
    },
      el("div", { style: { position: "absolute", left: 0, right: 0, top: topPct + "%", height: 2,
        background: "#7fff6a", transform: "translateY(-50%)", pointerEvents: "none", boxShadow: "0 0 4px #7fff6a" }}),
      el("div", { style: { position: "absolute", left: "50%", top: topPct + "%", width: 12, height: 12,
        borderRadius: "50%", background: "#7fff6a", transform: "translate(-50%,-50%)", pointerEvents: "none" }})
    ),
    el("span", { style: { fontSize: 8, color: "#7fff6a", marginTop: 3 } }, fmtV(props.value))
  );
}

// Division time multipliers (fraction of one beat)
var DIV_MULTS = {"1/16":0.25,"1/8":0.5,"1/4":1,"1/2":2,"1/1":4,
  "1/16T":0.1667,"1/8T":0.3333,"1/4T":0.6667,"1/8.":0.75,"1/4.":1.5};






// ── Diffusion — all-pass chain inside delay feedback loop ────────────────────

// Pre-baked reverb IR — generated once at startup, fixed 3s hall character
var REVERB_IR = (function() {
  var sr  = 44100;
  var len = Math.floor(sr * 3.0);
  var L   = new Float32Array(len);
  var R   = new Float32Array(len);
  // Early reflections
  var erT = [0.011,0.017,0.023,0.031,0.041,0.057,0.073,0.089];
  var erG = [0.7,  0.5,  0.6,  0.4,  0.45, 0.35, 0.3,  0.25];
  for (var e=0;e<erT.length;e++) {
    var idx=Math.floor(erT[e]*sr);
    if(idx<len){
      L[idx]+=erG[e]*(e%2===0?1:-1);
      var ridx=Math.min(len-1,idx+Math.floor(sr*0.0007*(e+1)));
      R[ridx]+=erG[e]*(e%2===0?-1:1);
    }
  }
  // Diffuse tail
  var pre=Math.floor(sr*0.02);
  for(var i=pre;i<len;i++){
    var t=(i-pre)/(len-pre);
    var d=Math.pow(1-t,1.8)*Math.exp(-t*2.5);
    L[i]+=(Math.random()*2-1)*d;
    R[i]+=(Math.random()*2-1)*d;
  }
  // Gentle lowpass
  var lpL=0,lpR=0;
  for(var i=0;i<len;i++){
    lpL=0.85*lpL+0.15*L[i]; L[i]=lpL;
    lpR=0.85*lpR+0.15*R[i]; R[i]=lpR;
  }
  return {L:L,R:R,len:len};
}());

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
  var rfx = useState(false);  var showFx        = rfx[0], setShowFx       = rfx[1];
  var rfxs= useState({
    delaySync: true, delayDiv: "1/8", delayTime: 250,
    feedback: 0, width: 0, delayMix: 0,
    reverbMix: 0, fxLoCut: 20, fxHiCut: 20000,
    divMenuOpen: false,
  });
  var fxSettings = rfxs[0], setFxSettings = rfxs[1];
  function setFx(k,v){ setFxSettings(function(s){var n=Object.assign({},s);n[k]=v;return n;}); }
  var rf  = useState("environment"); var facingMode = rf[0], setFacingMode = rf[1];
  var rx  = useState(0.5);    var ribbonX       = rx[0],  setRibbonX      = rx[1];
  var rlp = useState(0.7);    var lpX           = rlp[0], setLpX          = rlp[1]; // 0=closed 1=open
  var rlpq = useState(0.1);  var lpQ           = rlpq[0], setLpQ         = rlpq[1]; // resonance 0..1
  var rcr = useState(false);  var camReady      = rcr[0], setCamReady     = rcr[1];
  var rce = useState(null);   var camError      = rce[0], setCamError     = rce[1];
  var rer = useState(false);  var engReady      = rer[0], setEngReady     = rer[1];
  var rco = useState(true);   var camOn         = rco[0], setCamOn        = rco[1];
  var rl  = useState(false);  var looping       = rl[0],  setLooping      = rl[1];
  var rlc = useState(false);  var loopCapturing = rlc[0], setLoopCapturing= rlc[1];
  var rfd = useState(null);   var frameData     = rfd[0], setFrameData    = rfd[1];
  var frameDataRef = useRef(null); // raw ref for engine — no re-renders
  var hudTimerRef  = useRef(0);   // throttle HUD updates to 4fps

  // Which engine is active: "1" or "2"
  var ren = useState("2");    var activeEngine  = ren[0], setActiveEngine  = ren[1];

  // Engine 1 settings
  var rs1 = useState({ voices:1, detune:12, quantize:false, scale:"pentatonic",
    rootNote:48, pitchMin:36, pitchMax:72, reverbMix:0.3, fps:10, showScales:false });
  var settings1 = rs1[0], setSettings1 = rs1[1];

  // Engine 2 settings
  var rs2 = useState({ quantize:false, scale:"pentatonic", rootNote:48,
    pitchMin:36, pitchMax:72, reverbMix:0.3, fps:10, showScales:false,
    intervalR:"1×2", intervalG:"3×2", intervalB:"5×4", glide:200, fmMatrix:"A",
    cmR:"1:1", cmG:"1:1", cmB:"1:1", fmDepth:0.4, fmModShape:0,
    lfo1:{ rate:0.5, depth:0, wave:"sine", dest:"filter cutoff", active:false },
    lfo2:{ rate:0.2, depth:0, wave:"sine", dest:"filter Q",      active:false } });

  // Shared LFO UI state (same for both engines)
  var rlfo = useState({
    lfo1:{ rate:0.5, depth:0, wave:"sine", dest:"filter cutoff", active:false },
    lfo2:{ rate:0.2, depth:0, wave:"sine", dest:"filter Q",      active:false }
  });
  var lfoState = rlfo[0], setLfoState = rlfo[1];

  function setLfo(which, key, val) {
    setLfoState(function(s) {
      var ns = Object.assign({}, s);
      ns[which] = Object.assign({}, s[which]);
      ns[which][key] = val;
      return ns;
    });
    // Apply to active engine immediately
    var eng = synthRef.current;
    if (eng && eng.settings && eng.settings[which]) {
      eng.settings[which][key] = val;
      if (eng.applyUserLFO) eng.applyUserLFO(which);
    }
  }
  var settings2 = rs2[0], setSettings2 = rs2[1];

  var settings    = activeEngine === "1" ? settings1 : settings2;
  var setSettings = activeEngine === "1" ? setSettings1 : setSettings2;

  function setSetting(k, v) { setSettings(function(s){ var n=Object.assign({},s); n[k]=v; return n; }); }

  // Init both engines, switch between them
  var eng1Ref = useRef(null);
  var eng2Ref = useRef(null);
  var seqRef  = useRef(null);

  // Sequencer UI state
  var rmode = useState("drone"); var seqMode = rmode[0], setSeqMode = rmode[1];
  var rseq  = useState({
    bpm: 120, steps: 16,
    pattern: new Array(16).fill(false),
    envAmp:    { a:10,  h:80,  r:300, enabled:true },  // h=hold % of step

  });
  var seqSettings = rseq[0], setSeqSettings = rseq[1];
  var rplay = useState(false); var seqPlaying = rplay[0], setSeqPlaying = rplay[1];
  var rstep = useState(-1);    var currentStep = rstep[0], setCurrentStep = rstep[1];
  var rshowSeq = useState(false); var showSeq = rshowSeq[0], setShowSeq = rshowSeq[1];

  useEffect(function() {
    eng1Ref.current = makeEngine1();
    eng2Ref.current = makeEngine2();
    seqRef.current  = makeSequencer(function(){ return synthRef.current; });

    // Load last state from localStorage
    try {
      var saved = localStorage.getItem("synesthesia_state");
      if (saved) {
        var state = JSON.parse(saved);
        if (state.engine) {
          var initEng = state.engine === "1" ? eng1Ref.current : eng2Ref.current;
          synthRef.current = initEng;
          setActiveEngine(state.engine);
        } else {
          synthRef.current = eng2Ref.current;
        }
        if (state.settings1) setSettings1(function(s){ return Object.assign({},s,state.settings1); });
        if (state.settings2) setSettings2(function(s){ return Object.assign({},s,state.settings2); });
        if (state.lfoState)  setLfoState(function(s){ return Object.assign({},s,state.lfoState); });
        if (state.lpX !== undefined) setLpX(state.lpX);
        if (state.lpQ !== undefined) setLpQ(state.lpQ);
        if (state.ribbonX !== undefined) setRibbonX(state.ribbonX);
      } else {
        synthRef.current = eng2Ref.current; // default CamSynth_2
      }
    } catch(e) {
      synthRef.current = eng2Ref.current;
    }

    return function() {
      if (eng1Ref.current) eng1Ref.current.destroy();
      if (eng2Ref.current) eng2Ref.current.destroy();
      if (seqRef.current)  seqRef.current.destroy();
    };
  }, []);

  // Save state to localStorage on changes (debounced)
  var saveTimerRef = useRef(null);
  useEffect(function() {
    if (saveTimerRef.current) clearTimeout(saveTimerRef.current);
    saveTimerRef.current = setTimeout(function() {
      try {
        localStorage.setItem("synesthesia_state", JSON.stringify({
          engine: activeEngine, settings1: settings1, settings2: settings2,
          lfoState: lfoState, lpX: lpX, lpQ: lpQ, ribbonX: ribbonX
        }));
      } catch(e) {}
    }, 500);
  }, [activeEngine, settings1, settings2, lfoState, lpX, ribbonX]);

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
        frameDataRef.current = data;
        // Only update React state (HUD) at ~4fps to avoid re-renders
        hudTimerRef.current++;
        if (hudTimerRef.current >= Math.ceil(settings.fps / 4)) {
          hudTimerRef.current = 0;
          setFrameData(data);
        }
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

  // Sequencer step ticker — uses ref to avoid React re-renders on every frame
  var currentStepRef = useRef(-1);
  useEffect(function() {
    if (!seqPlaying) {
      currentStepRef.current = -1;
      // Force one re-render to clear highlights
      setCurrentStep(-1);
      return;
    }
    var alive = true;
    var lastStep = -1;
    function tick() {
      if (!alive) return;
      var s = seqRef.current;
      if (s) {
        var step = s.getCurrentStep();
        if (step !== lastStep) {
          lastStep = step;
          currentStepRef.current = step;
          setCurrentStep(step); // only re-render on step change (~every 125ms at 120bpm)
        }
      }
      requestAnimationFrame(tick);
    }
    tick();
    return function() { alive = false; };
  }, [seqPlaying]);

  // Scope
  useEffect(function() {
    var alive=true;
    function draw() {
      if(!alive)return;
      rafRef.current=requestAnimationFrame(draw);
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
  }, [soundOn]);

  var handleSound = useCallback(function() {
    var eng=synthRef.current;
    if(!eng)return;
    if(!eng.ctx){eng.init();setEngReady(true);}
    var next=!soundOn;
    eng.setSoundOn(next);
    setSoundOn(next);
  }, [soundOn]);

  var ribbonRectRef = useRef(null);
  var handleRibbon = useCallback(function(e) {
    e.preventDefault();
    if (e.type === "touchstart" || e.type === "mousedown") {
      ribbonRectRef.current = ribbonRef.current ? ribbonRef.current.getBoundingClientRect() : null;
    }
    var rect = ribbonRectRef.current;
    if(!rect)return;
    var cx=e.touches?e.touches[0].clientX:e.clientX;
    var x=Math.max(0,Math.min(1,(cx-rect.left)/rect.width));
    setRibbonX(x);
    if(synthRef.current)synthRef.current.updatePitch(x);
  }, []);

  var lpResRef = useRef(null);
  var lpResRectRef = useRef(null);
  var handleLpRes = useCallback(function(e) {
    e.preventDefault();
    if (e.type === "touchstart" || e.type === "mousedown") {
      lpResRectRef.current = lpResRef.current ? lpResRef.current.getBoundingClientRect() : null;
    }
    var rect = lpResRectRef.current;
    if (!rect) return;
    var touch = e.touches ? e.touches[0] : e;
    var x = Math.max(0, Math.min(1, (touch.clientX - rect.left) / rect.width));
    setLpQ(x);
    var eng = synthRef.current;
    if (eng && eng.ladderFb) {
      // Resonance: 0 = flat, ~3.8 = self-oscillation threshold
      var fb = x * 3.6;
      eng.ladderFb.gain.setTargetAtTime(fb, eng.ctx.currentTime, 0.02);
    }
  }, []);

  var lpRibbonRectRef = useRef(null);
  var handleLpRibbon = useCallback(function(e) {
    e.preventDefault();
    if (e.type === "touchstart" || e.type === "mousedown") {
      lpRibbonRectRef.current = lpRibbonRef.current ? lpRibbonRef.current.getBoundingClientRect() : null;
    }
    var rect = lpRibbonRectRef.current;
    if (!rect) return;
    var cx = e.touches ? e.touches[0].clientX : e.clientX;
    var x  = Math.max(0, Math.min(1, (cx - rect.left) / rect.width));
    setLpX(x);
    var eng = synthRef.current;
    if (!eng || !eng.ctx) return;
    // Map 0..1 → 20Hz..12000Hz (log scale)
    var freq = 20 * Math.pow(12000/20, x);
    if (eng.setLpFreq) {
      eng.setLpFreq(freq);
    } else {
      eng.lowpassNode.frequency.setTargetAtTime(freq, eng.ctx.currentTime, 0.05);
    }
    // Q is controlled exclusively by resonance ribbon — never touched here
  }, []);

  var handleFlip    = useCallback(function(){setFacingMode(function(f){return f==="environment"?"user":"environment";});}, []);
  var handleReload  = useCallback(function(){window.location.reload();}, []);

  var handleLoopPress = function(e) {
    e.preventDefault();
    var eng=synthRef.current;
    if(!eng||!eng.ctx)return;

    if(eng.isLooping()){
      // State 3 → back to live
      eng.stopLoop();setLooping(false);setLoopCapturing(false);
      clearInterval(loopVidTimerRef.current);loopFramesRef.current=[];
      var ov=loopOverlayRef.current;
      if(ov)ov.getContext("2d").clearRect(0,0,ov.width,ov.height);
      return;
    }
    if(eng._loopRecording){
      // State 2 → commit → play
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
      return;
    }
    // State 1 → start recording
    loopFramesRef.current=[];eng.startLoopRecord();setLoopCapturing(true);
  };

  function applyFxToEngine(fx, bpm) {
    var eng = synthRef.current;
    if (!eng || !eng.ctx || !eng.delayL) return;
    var t = eng.ctx.currentTime;

    // Delay time
    var delayTimeSec;
    if (fx.delaySync) {
      var beat = 60 / (bpm || 120);
      var mult = DIV_MULTS[fx.delayDiv];
      if (mult === undefined) mult = 0.5;
      delayTimeSec = beat * mult;
    } else {
      delayTimeSec = Math.max(0.001, (fx.delayTime || 250) / 1000);
    }
    eng.delayL.delayTime.setTargetAtTime(delayTimeSec, t, 0.02);
    eng.delayR.delayTime.setTargetAtTime(delayTimeSec, t, 0.02);

    // Feedback — both feedback loop and cross-feed scale together
    var fb = Math.min(0.95, (fx.feedback||0)/100);
    eng.fbGain.gain.setTargetAtTime(fb, t, 0.05);
    if (eng.crossGain) eng.crossGain.gain.setTargetAtTime(fb, t, 0.05);

    // Width: 0 = mono, 100 = hard ping-pong
    var w = (fx.width||0) / 100;
    eng.delayWetL.pan.setTargetAtTime(-w, t, 0.05);
    eng.delayWetR.pan.setTargetAtTime( w, t, 0.05);

    // Delay mix — equal-power crossfade
    var mixAngle = ((fx.delayMix||0)/100) * Math.PI / 2;
    eng.delayWet.gain.setTargetAtTime(Math.sin(mixAngle), t, 0.05);
    eng.delayDry.gain.setTargetAtTime(Math.cos(mixAngle), t, 0.05);


    // Lo/Hi cut on reverb send
    if (eng.fxLoCut) eng.fxLoCut.frequency.setTargetAtTime(Math.max(20, fx.fxLoCut||20), t, 0.05);
    if (eng.fxHiCut) eng.fxHiCut.frequency.setTargetAtTime(Math.min(20000, fx.fxHiCut||20000), t, 0.05);
    // Reverb — send with quadratic curve (stays low, rises sharply at top)
    if (eng.reverbGain) {
      var revLin = (fx.reverbMix !== undefined ? fx.reverbMix : 0);
      var revSend = Math.pow(revLin, 1.3); // soft power curve
      eng.reverbGain.gain.setTargetAtTime(revSend, t, 0.1);
    }
  }

  // Apply FX whenever settings change
  useEffect(function(){
    applyFxToEngine(fxSettings, seqSettings.bpm);
  }, [fxSettings, seqSettings.bpm]);

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
      if(wavBuf){var blob=new Blob([wavBuf],{type:"audio/wav"}),url=URL.createObjectURL(blob),a=document.createElement("a");a.href=url;a.download="synesthesia-"+Date.now()+".wav";a.click();}
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
        el("span", { style:{ fontSize:10, letterSpacing:"0.2em", textTransform:"uppercase" } },
          el("span", { style:{ color:"#7fff6a" } }, "SYNESTHESIA")
        ),
        el("span", { style:{ fontSize:8, color:"#888", letterSpacing:"0.1em" } }, "v"+VERSION)
      ),
      el("div", { style:{ display:"flex", gap:4, alignItems:"center" } },
        el("button", { className:cx("cb", showAdv&&"on"), onClick:function(){setShowAdv(function(s){return !s;});setShowSeq(false);}, style:{ letterSpacing:"0.12em", padding:"5px 10px" } }, "ADV"),
        camOn && el("button", { className:"cb", onClick:handleFlip, style:{fontSize:18,padding:"3px 8px",lineHeight:1} }, "\u21c4"),
        el("button", { className:"cb", onClick:handleReload, style:{fontSize:18,padding:"3px 8px",lineHeight:1} }, "\u21ba")
      )
    ),

    // Camera
    el("div", { style:{ position:"relative", background:"#050505", overflow:"hidden", borderTop:"1px solid #141414", borderBottom:"1px solid #141414", flexShrink:0, height:"42vh" } },
      el("video", { ref:videoRef, playsInline:true, muted:true, autoPlay:true, controls:false, style:{ width:"100%", height:"100%", objectFit:"cover", display:"block", transform:facingMode==="user"?"scaleX(-1)":"none" } }),
      el("canvas", { ref:scopeRef, width:480, height:80, style:{ position:"absolute", bottom:40, left:0, width:"100%", height:50, pointerEvents:"none" } }),
      el("div", { style:{ position:"absolute", bottom:0, left:0, right:0 } },
        el("div", { style:{ display:"flex", alignItems:"center", padding:"1px 14px", gap:8 } },
          el("span", { style:{ fontSize:8, color:"rgba(127,255,106,0.3)", letterSpacing:"0.1em" } }, "PITCH"),
          el("span", { style:{ fontSize:11, color:"#7fff6a", letterSpacing:"0.04em", minWidth:34 } }, noteName),
          el("span", { style:{ fontSize:8, color:"rgba(255,255,255,0.1)", marginLeft:"auto" } }, settings.quantize?settings.scale:"free")
        ),
        el("div", { ref:ribbonRef, onMouseDown:function(e){handleRibbon(e);}, onMouseMove:function(e){if(e.buttons)handleRibbon(e);}, onMouseUp:function(){ribbonRectRef.current=null;}, onTouchStart:function(e){handleRibbon(e);}, onTouchMove:function(e){handleRibbon(e);}, onTouchEnd:function(){ribbonRectRef.current=null;},
          style:{ height:30, background:"rgba(7,12,7,0.85)", borderTop:"1px solid rgba(20,28,20,0.8)", position:"relative", cursor:"crosshair" } },
          Array.from({length:pr+1},function(_,i){
            var midi = settings.pitchMin + i;
            var semitone = midi % 12;
            var isOctave = semitone === (settings.rootNote % 12);
            var inScale = !settings.quantize || SCALES[settings.scale].indexOf(((semitone - settings.rootNote%12)+12)%12) >= 0;
            var tickH = isOctave ? 18 : inScale ? 10 : 5;
            var bg = isOctave ? "rgba(42,74,42,0.9)" : inScale ? "rgba(28,50,28,0.9)" : "rgba(14,20,14,0.9)";
            var topPx = (30 - tickH) / 2;
            return el("div",{key:i,style:{position:"absolute",left:((i/pr)*100)+"%",top:topPx+"px",width:isOctave?2:1,height:tickH+"px",background:bg}});
          }),
          el("div", { style:{ position:"absolute", left:(ribbonX*100)+"%", top:0, bottom:0, width:2, background:"#7fff6a", boxShadow:"0 0 8px #7fff6a", transform:"translateX(-50%)", pointerEvents:"none" } })
        )
      ),
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
      el("canvas", { ref:loopOverlayRef, style:{ position:"absolute", inset:0, width:"100%", height:"100%", pointerEvents:"none", display:looping?"block":"none" } }),
      el("button", { className:cx("cb",recording&&"rec"), onClick:handleRecord,
        style:{ position:"absolute", top:8, right:8, fontSize:9, padding:"4px 8px",
          background:"rgba(10,10,11,0.7)", backdropFilter:"blur(4px)" }
      }, recording?"●":"○")
    ),



    // Filter ribbon (edge to edge)
    el("div", { style:{ flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"center", padding:"2px 14px 1px", gap:8 } },
        el("span", { style:{ fontSize:8, color:"#2a2a2a", letterSpacing:"0.1em" } }, "FILTER"),
        el("span", { style:{ fontSize:11, color:"#6bb5ff", letterSpacing:"0.04em", minWidth:60 } },
          (20 * Math.pow(12000/20, lpX)).toFixed(0)+" Hz"
        ),
        el("span", { style:{ fontSize:8, color:"#1a1a1a", marginLeft:"auto" } }, "24dB")
      ),
      el("div", {
        ref:lpRibbonRef,
        onMouseDown:handleLpRibbon, onMouseMove:function(e){if(e.buttons)handleLpRibbon(e);},
        onMouseUp:function(){lpRibbonRectRef.current=null;},
        onTouchStart:handleLpRibbon, onTouchMove:handleLpRibbon,
        onTouchEnd:function(){lpRibbonRectRef.current=null;},
        style:{ height:32, position:"relative", cursor:"crosshair",
          background:"linear-gradient(90deg, #050a14 0%, #0a1628 30%, #0d2040 60%, #1a3a6a 80%, #2050a0 100%)",
          borderTop:"1px solid #141c24", borderBottom:"1px solid #141c24" }
      },
        [20,60,200,600,2000,6000,12000].map(function(f) {
          var pos = Math.log(f/20) / Math.log(12000/20);
          return el("div", { key:f, style:{ position:"absolute", left:(pos*100)+"%", top:0, bottom:0, width:1, background:"rgba(107,181,255,0.15)" } });
        }),
        el("div", { style:{ position:"absolute", left:(lpX*100)+"%", top:0, bottom:0, width:2,
          background:"#6bb5ff", boxShadow:"0 0 8px #6bb5ff", transform:"translateX(-50%)", pointerEvents:"none" } })
      )
    ),

    // Resonance ribbon (edge to edge)
    el("div", { style:{ flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"center", padding:"2px 14px 1px", gap:8 } },
        el("span", { style:{ fontSize:8, color:"#2a2a2a", letterSpacing:"0.1em" } }, "RES"),
        el("span", { style:{ fontSize:11, color:"#6bb5ff", letterSpacing:"0.04em", minWidth:60 } },
          (lpQ * 3.6).toFixed(2)+" fb"
        )
      ),
      el("div", {
        ref:lpResRef,
        onMouseDown:handleLpRes, onMouseMove:function(e){if(e.buttons)handleLpRes(e);},
        onMouseUp:function(){lpResRectRef.current=null;},
        onTouchStart:handleLpRes, onTouchMove:handleLpRes,
        onTouchEnd:function(){lpResRectRef.current=null;},
        style:{ height:24, position:"relative", cursor:"crosshair",
          background:"linear-gradient(90deg, #050a14 0%, #0d2040 60%, #1a3a8a 100%)",
          borderTop:"1px solid #141c24", borderBottom:"1px solid #141c24" }
      },
        el("div", { style:{ position:"absolute", left:(lpQ*100)+"%", top:0, bottom:0, width:2,
          background:"#6bb5ff", boxShadow:"0 0 8px #6bb5ff", transform:"translateX(-50%)", pointerEvents:"none" } })
      )
    ),

    // Controls
    el("div", { style:{ display:"flex", gap:5, padding:"7px 14px", flexShrink:0 } },
      el("button", { className:cx("cb",soundOn&&"on"), onClick:handleSound, style:{ flex:2, fontSize:11, padding:"10px 0", letterSpacing:"0.1em" } }, soundOn?"\u25fc ON":"\u25b6 OFF"),
      el("button", { className:cx("cb",loopCapturing&&"blink",looping&&"on"), onClick:handleLoopPress, style:{ flex:1, padding:"10px 0" } }, loopCapturing?"\u25cf":looping?"\u21ba":"\u25cb"),
      el("button", { className:cx("cb",camOn&&"on"), onClick:handleCamToggle, style:{ flex:1, padding:"10px 0" } }, "\u25a3"),
      el("button", { className:cx("cb",showFx&&"on"), onClick:function(){setShowFx(function(s){return !s;});setShowSettings(false);setShowSeq(false);}, style:{ flex:1, padding:"10px 0" } }, "FX"),
      el("button", { className:cx("cb",showSeq&&"on"), onClick:function(){
        setShowSeq(function(s){return !s;});
        setShowSettings(false);setShowFx(false);
        // sync seq settings on open
        var sq=seqRef.current;
        if(sq){sq.bpm=seqSettings.bpm;sq.steps=seqSettings.steps;sq.pattern=seqSettings.pattern.slice();}
      }, style:{ flex:1, padding:"10px 0" } }, "SEQ"),
      el("button", { className:cx("cb",showSettings&&"on"), onClick:function(){setShowSettings(function(s){return !s;});setShowSeq(false);setShowFx(false);}, style:{ flex:1 } }, "\u266a")
    ),

    // Settings drawer — engine 1
    showSettings && activeEngine==="1" && el("div", { style:{ padding:"8px 14px 14px", borderTop:"1px solid #141414", background:"#0c0c0d", overflowY:"auto", flexShrink:0, maxHeight:"42vh" } },
      el("div",{className:"sr"},
        el("label",null,"Voices"),
        el("div",{style:{display:"flex",gap:2,alignItems:"center"}},
          [1,2,4].map(function(v){return el("button",{key:v,className:cx("sg",settings1.voices===v&&"sel"),onClick:function(){setSettings1(function(s){var n=Object.assign({},s);n.voices=v;return n;})}},v);}),
          el("span",{style:{fontSize:8,color:"#333",margin:"0 4px 0 8px"}},"DTN"),
          el("input",{type:"range",min:0,max:50,value:settings1.detune,
            onChange:function(e){var v=+e.target.value;setSettings1(function(s){var n=Object.assign({},s);n.detune=v;return n;});var eng=eng1Ref.current;if(eng)eng.updateDetune(v);},
            style:{width:80,flexShrink:0}
          }),
          el("span",{style:{fontSize:9,color:"#7fff6a",minWidth:28,textAlign:"right"}},settings1.detune+"ct")
        )
      ),
      el("div",{className:"sr",style:{paddingTop:3,paddingBottom:3}},
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
      )
    ),
    // Settings drawer — engine 2
    showSettings && activeEngine==="2" && el("div", { style:{ padding:"8px 14px 14px", borderTop:"1px solid #141414", background:"#0c0c0d", overflowY:"auto", flexShrink:0, maxHeight:"42vh" } },
      el("div",{className:"sr",style:{paddingTop:3,paddingBottom:3}},
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
          el("label",null,"Glide"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},settings2.glide+"ms")
        ),
        el("input",{type:"range",min:0,max:2000,step:10,value:settings2.glide,onChange:function(e){
          var v=+e.target.value;
          setSettings2(function(s){var n=Object.assign({},s);n.glide=v;return n;});
          var eng=eng2Ref.current;if(eng)eng.settings.glide=v;
        }})
      )
    ),


    // ── FX inline drawer ──────────────────────────────────────────────────────
    showFx && el("div", { style:{ padding:"8px 14px 10px", borderTop:"1px solid #141414", background:"#0c0c0d", flexShrink:0, position:"relative" } },

      // Row 1: Sync/Free + division + time
      el("div", { style:{ display:"flex", alignItems:"center", gap:6, marginBottom:8 } },
        el("div", { style:{ display:"flex", gap:2 } },
          el("button", { className:cx("sg", fxSettings.delaySync&&"sel"), onClick:function(){ setFx("delaySync",true); } }, "sync"),
          el("button", { className:cx("sg", !fxSettings.delaySync&&"sel"), onClick:function(){ setFx("delaySync",false); } }, "free")
        ),
        fxSettings.delaySync && el("div", { style:{ position:"relative", flex:1 } },
          el("button", { className:"sg sel", onClick:function(){ setFx("divMenuOpen",!fxSettings.divMenuOpen); }, style:{ width:"100%", textAlign:"center" } }, fxSettings.delayDiv+" ▾"),
          fxSettings.divMenuOpen && el("div", { style:{ position:"absolute", bottom:"100%", left:0, right:0, zIndex:20, background:"#0e0e10", border:"1px solid #2a2a2a", borderRadius:4, padding:4, marginBottom:3 } },
            el("div", { style:{ fontSize:7, color:"#555", letterSpacing:"0.1em", marginBottom:3, paddingLeft:2 } }, "STRAIGHT"),
            el("div", { style:{ display:"flex", gap:2, marginBottom:4 } }, ["1/16","1/8","1/4","1/2","1/1"].map(function(d){ return el("button",{ key:d, className:cx("sg",fxSettings.delayDiv===d&&"sel"), onClick:function(){ setFx("delayDiv",d); setFx("divMenuOpen",false); }, style:{flex:1,textAlign:"center",fontSize:8,padding:"3px 0"} }, d); })),
            el("div", { style:{ fontSize:7, color:"#555", letterSpacing:"0.1em", marginBottom:3, paddingLeft:2 } }, "DOTTED"),
            el("div", { style:{ display:"flex", gap:2, marginBottom:4 } }, ["1/8.","1/4."].map(function(d){ return el("button",{ key:d, className:cx("sg",fxSettings.delayDiv===d&&"sel"), onClick:function(){ setFx("delayDiv",d); setFx("divMenuOpen",false); }, style:{flex:1,textAlign:"center",fontSize:8,padding:"3px 0"} }, d); })),
            el("div", { style:{ fontSize:7, color:"#555", letterSpacing:"0.1em", marginBottom:3, paddingLeft:2 } }, "TRIPLET"),
            el("div", { style:{ display:"flex", gap:2 } }, ["1/16T","1/8T","1/4T"].map(function(d){ return el("button",{ key:d, className:cx("sg",fxSettings.delayDiv===d&&"sel"), onClick:function(){ setFx("delayDiv",d); setFx("divMenuOpen",false); }, style:{flex:1,textAlign:"center",fontSize:8,padding:"3px 0"} }, d); }))
          )
        ),
        !fxSettings.delaySync && el("input", { type:"range", min:1, max:3000, value:fxSettings.delayTime, style:{ flex:1 }, onChange:function(e){ setFx("delayTime",+e.target.value); } }),
        el("span", { style:{ fontSize:11, color:"#7fff6a", minWidth:44, textAlign:"right", letterSpacing:"0.04em" } },
          fxSettings.delaySync ? Math.round((60/seqSettings.bpm)*(DIV_MULTS[fxSettings.delayDiv]||0.5)*1000)+"ms" : fxSettings.delayTime+"ms"
        )
      ),

      // 2-column × 3-row grid
      // Left: Delay · Feedback · Width  |  Right: Lo Cut · Hi Cut · Reverb
      el("div", { style:{ display:"grid", gridTemplateColumns:"1fr 1fr", gap:8 } },
        // Left col
        el("div",{style:{display:"flex",flexDirection:"column",gap:2}},
          el("div",{style:{display:"flex",justifyContent:"space-between"}},
            el("span",{style:{fontSize:7,color:"#555",letterSpacing:"0.1em",textTransform:"uppercase"}},"Delay"),
            el("span",{style:{fontSize:8,color:"#7fff6a"}},fxSettings.delayMix+"%")
          ),
          el("input",{type:"range",min:0,max:100,value:fxSettings.delayMix,onChange:function(e){setFx("delayMix",+e.target.value);}})
        ),
        // Right col
        el("div",{style:{display:"flex",flexDirection:"column",gap:2}},
          el("div",{style:{display:"flex",justifyContent:"space-between"}},
            el("span",{style:{fontSize:7,color:"#555",letterSpacing:"0.1em",textTransform:"uppercase"}},"Lo Cut"),
            el("span",{style:{fontSize:8,color:"#7fff6a"}},fxSettings.fxLoCut<=20?"off":fxSettings.fxLoCut+"Hz")
          ),
          el("input",{type:"range",min:20,max:2000,value:fxSettings.fxLoCut,onChange:function(e){setFx("fxLoCut",+e.target.value);}})
        ),
        el("div",{style:{display:"flex",flexDirection:"column",gap:2}},
          el("div",{style:{display:"flex",justifyContent:"space-between"}},
            el("span",{style:{fontSize:7,color:"#555",letterSpacing:"0.1em",textTransform:"uppercase"}},"Feedback"),
            el("span",{style:{fontSize:8,color:"#7fff6a"}},fxSettings.feedback+"%")
          ),
          el("input",{type:"range",min:0,max:95,value:fxSettings.feedback,onChange:function(e){setFx("feedback",+e.target.value);}})
        ),
        el("div",{style:{display:"flex",flexDirection:"column",gap:2}},
          el("div",{style:{display:"flex",justifyContent:"space-between"}},
            el("span",{style:{fontSize:7,color:"#555",letterSpacing:"0.1em",textTransform:"uppercase"}},"Hi Cut"),
            el("span",{style:{fontSize:8,color:"#7fff6a"}},fxSettings.fxHiCut>=20000?"off":(fxSettings.fxHiCut>=1000?(fxSettings.fxHiCut/1000).toFixed(1)+"k":fxSettings.fxHiCut+"Hz"))
          ),
          el("input",{type:"range",min:1000,max:20000,value:fxSettings.fxHiCut,onChange:function(e){setFx("fxHiCut",+e.target.value);}})
        ),
        el("div",{style:{display:"flex",flexDirection:"column",gap:2}},
          el("div",{style:{display:"flex",justifyContent:"space-between"}},
            el("span",{style:{fontSize:7,color:"#555",letterSpacing:"0.1em",textTransform:"uppercase"}},"Width"),
            el("span",{style:{fontSize:8,color:"#7fff6a"}},fxSettings.width+"%")
          ),
          el("input",{type:"range",min:0,max:100,value:fxSettings.width,onChange:function(e){setFx("width",+e.target.value);}})
        ),
        el("div",{style:{display:"flex",flexDirection:"column",gap:2}},
          el("div",{style:{display:"flex",justifyContent:"space-between"}},
            el("span",{style:{fontSize:7,color:"#555",letterSpacing:"0.1em",textTransform:"uppercase"}},"Reverb"),
            el("span",{style:{fontSize:8,color:"#7fff6a"}},Math.round((fxSettings.reverbMix||0)*100)+"%")
          ),
          el("input",{type:"range",min:0,max:100,value:Math.round((fxSettings.reverbMix||0)*100),onChange:function(e){setFx("reverbMix",+e.target.value/100);}})
        )
      )
    ),

    // ── SEQ inline drawer ─────────────────────────────────────────────────────
    showSeq && el("div", { style:{ padding:"6px 14px 8px", borderTop:"1px solid #141414", background:"#0c0c0d", flexShrink:0 } },

      // PLAY + BPM + STEPS — single evenly spaced row
      el("div", { style:{ display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:8, gap:8 } },

        el("button", { className:cx("cb", seqPlaying&&"on"), onClick:function(){
          var s=seqRef.current, eng=synthRef.current;
          if(!s||!eng||!eng.ctx) return;
          if(seqPlaying){ s.stop(); setSeqPlaying(false); }
          else {
            s.bpm=seqSettings.bpm; s.steps=seqSettings.steps;
            s.pattern=seqSettings.pattern.slice();
            s.envAmp=Object.assign({},seqSettings.envAmp);
            s.envAmp.enabled=true;
            s.start(); setSeqPlaying(true);
          }
        }, style:{ padding:"6px 14px", fontSize:10, flexShrink:0 } }, seqPlaying?"◼ STOP":"▶ PLAY"),

        el("div", { style:{ display:"flex", alignItems:"center", gap:4 } },
          el("span", { style:{ fontSize:8, color:"#444", letterSpacing:"0.1em", marginRight:2 } }, "BPM"),
          el("button", { className:"sg", style:{padding:"2px 7px"}, onClick:function(){ setSeqSettings(function(s){ var n=Object.assign({},s); n.bpm=Math.max(40,s.bpm-5); if(seqRef.current)seqRef.current.bpm=n.bpm; return n; }); } }, "-"),
          el("input", { type:"text", inputMode:"numeric",
            defaultValue:seqSettings.bpm, key:"bpm-"+seqSettings.bpm,
            onBlur:function(e){ var v=Math.max(40,Math.min(500,parseInt(e.target.value)||120)); setSeqSettings(function(s){var n=Object.assign({},s);n.bpm=v;if(seqRef.current)seqRef.current.bpm=v;return n;}); },
            onKeyDown:function(e){ if(e.key==="Enter") e.target.blur(); },
            style:{ width:44, background:"transparent", border:"1px solid #222", color:"#7fff6a",
              fontFamily:"'IBM Plex Mono',monospace", fontSize:13, textAlign:"center", padding:"2px 0",
              userSelect:"text", WebkitUserSelect:"text" }
          }),
          el("button", { className:"sg", style:{padding:"2px 7px"}, onClick:function(){ setSeqSettings(function(s){ var n=Object.assign({},s); n.bpm=Math.min(500,s.bpm+5); if(seqRef.current)seqRef.current.bpm=n.bpm; return n; }); } }, "+")
        ),

        el("div", { style:{ display:"flex", alignItems:"center", gap:4 } },
          el("span", { style:{ fontSize:8, color:"#444", letterSpacing:"0.1em", marginRight:2 } }, "STEPS"),
          el("button", { className:"sg", style:{padding:"2px 7px"}, onClick:function(){ setSeqSettings(function(s){ var n=Object.assign({},s); n.steps=Math.max(1,s.steps-1); if(seqRef.current)seqRef.current.steps=n.steps; return n; }); } }, "-"),
          el("span", { style:{ fontSize:13, color:"#7fff6a", minWidth:20, textAlign:"center" } }, seqSettings.steps),
          el("button", { className:"sg", style:{padding:"2px 7px"}, onClick:function(){ setSeqSettings(function(s){ var n=Object.assign({},s); n.steps=Math.min(16,s.steps+1); if(seqRef.current)seqRef.current.steps=n.steps; return n; }); } }, "+")
        )
      ),

      // Step grid
      el("div", { style:{ marginBottom:8 } },
        [0,1].map(function(row){
          var rowSteps=[];
          for(var i=row*8; i<Math.min((row+1)*8,seqSettings.steps); i++) rowSteps.push(i);
          if(!rowSteps.length) return null;
          return el("div", { key:row, style:{ display:"flex", gap:3, marginBottom:3 } },
            rowSteps.map(function(i){
              var isOn=seqSettings.pattern[i];
              var isCur=(i===currentStep)&&seqPlaying;
              return el("div", { key:i,
                onClick:function(){ setSeqSettings(function(s){ var n=Object.assign({},s); n.pattern=s.pattern.slice(); n.pattern[i]=!s.pattern[i]; if(seqRef.current)seqRef.current.pattern=n.pattern.slice(); return n; }); },
                style:{ width:"calc((100% - 21px) / 8)", height:26, flexShrink:0, borderRadius:3, cursor:"pointer",
                  border:isCur?"2px solid #7fff6a":"1px solid #1a3a1a",
                  background:isCur?"#1a4a1a":isOn?"#0d2a0d":"#050805",
                  boxShadow:isCur?"0 0 6px rgba(127,255,106,0.4)":"none" }
              });
            })
          );
        })
      ),

      // AHR — 3 vertical ribbon sliders, half width, left-aligned
      el("div", { style:{ display:"flex", gap:6, width:"50%" } },
        el(ADSRSlider, { key:"A", label:"A", value:seqSettings.envAmp.a, min:1,   max:200,  onChange:function(v){ setSeqSettings(function(s){ var n=Object.assign({},s); n.envAmp=Object.assign({},s.envAmp); n.envAmp.a=v; if(seqRef.current)seqRef.current.envAmp=n.envAmp; return n; }); } }),
        el(ADSRSlider, { key:"H", label:"H", value:seqSettings.envAmp.h, min:0,   max:100,  onChange:function(v){ setSeqSettings(function(s){ var n=Object.assign({},s); n.envAmp=Object.assign({},s.envAmp); n.envAmp.h=v; if(seqRef.current)seqRef.current.envAmp=n.envAmp; return n; }); } }),
        el(ADSRSlider, { key:"R", label:"R", value:seqSettings.envAmp.r, min:10,  max:1000, onChange:function(v){ setSeqSettings(function(s){ var n=Object.assign({},s); n.envAmp=Object.assign({},s.envAmp); n.envAmp.r=v; if(seqRef.current)seqRef.current.envAmp=n.envAmp; return n; }); } })
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

      el("div", { style:{ fontSize:7, color:"#333", letterSpacing:"0.15em", textTransform:"uppercase", marginBottom:6 } }, "FM Matrix"),
      el("div", { style:{ display:"grid", gridTemplateColumns:"1fr 1fr 1fr 1fr", gap:5, marginBottom:14 } },
        [
          { id:"A", svg:"<svg viewBox=\"0 0 72 46\" xmlns=\"http://www.w3.org/2000/svg\" style=\"width:100%;height:100%;display:block\"><rect x=\"8\" y=\"4\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#ff6b6b15\" stroke=\"#ff6b6b\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"14\" y=\"10.8\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"5.5\" font-family=\"monospace\">r</text><line x1=\"14.0\" y1=\"12.0\" x2=\"14.0\" y2=\"16.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"14.0,20.0 12.0,16.0 16.0,16.0\" fill=\"#555\"/><rect x=\"6\" y=\"20\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#ff6b6b22\" stroke=\"#ff6b6b\" stroke-width=\"1.2\"/><text x=\"14\" y=\"28.5\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" >R</text><line x1=\"14\" y1=\"30\" x2=\"14\" y2=\"38\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"10\" y1=\"38\" x2=\"18\" y2=\"38\" stroke=\"#444\" stroke-width=\"1\"/><rect x=\"30\" y=\"4\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#7fff6a15\" stroke=\"#7fff6a\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"36\" y=\"10.8\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"5.5\" font-family=\"monospace\">g</text><line x1=\"36.0\" y1=\"12.0\" x2=\"36.0\" y2=\"16.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"36.0,20.0 34.0,16.0 38.0,16.0\" fill=\"#555\"/><rect x=\"28\" y=\"20\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#7fff6a22\" stroke=\"#7fff6a\" stroke-width=\"1.2\"/><text x=\"36\" y=\"28.5\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" >G</text><line x1=\"36\" y1=\"30\" x2=\"36\" y2=\"38\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"32\" y1=\"38\" x2=\"40\" y2=\"38\" stroke=\"#444\" stroke-width=\"1\"/><rect x=\"52\" y=\"4\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#6bb5ff15\" stroke=\"#6bb5ff\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"58\" y=\"10.8\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"5.5\" font-family=\"monospace\">b</text><line x1=\"58.0\" y1=\"12.0\" x2=\"58.0\" y2=\"16.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"58.0,20.0 56.0,16.0 60.0,16.0\" fill=\"#555\"/><rect x=\"50\" y=\"20\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#6bb5ff22\" stroke=\"#6bb5ff\" stroke-width=\"1.2\"/><text x=\"58\" y=\"28.5\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" >B</text><line x1=\"58\" y1=\"30\" x2=\"58\" y2=\"38\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"54\" y1=\"38\" x2=\"62\" y2=\"38\" stroke=\"#444\" stroke-width=\"1\"/><line x1=\"8\" y1=\"38\" x2=\"64\" y2=\"38\" stroke=\"#444\" stroke-width=\"0.8\"/></svg>" },
          { id:"B", svg:"<svg viewBox=\"0 0 72 46\" xmlns=\"http://www.w3.org/2000/svg\" style=\"width:100%;height:100%;display:block\"><rect x=\"8\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#ff6b6b15\" stroke=\"#ff6b6b\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"14\" y=\"9.8\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"5.5\" font-family=\"monospace\">r</text><line x1=\"14.0\" y1=\"11.0\" x2=\"14.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"14.0,19.0 12.0,15.0 16.0,15.0\" fill=\"#555\"/><rect x=\"6\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#ff6b6b11\" stroke=\"#ff6b6b\" stroke-width=\"0.7\" stroke-dasharray=\"3,1\"/><text x=\"14\" y=\"27.5\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" opacity=\"0.4\">R</text><rect x=\"30\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#7fff6a15\" stroke=\"#7fff6a\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"36\" y=\"9.8\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"5.5\" font-family=\"monospace\">g</text><line x1=\"36.0\" y1=\"11.0\" x2=\"36.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"36.0,19.0 34.0,15.0 38.0,15.0\" fill=\"#555\"/><rect x=\"28\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#7fff6a11\" stroke=\"#7fff6a\" stroke-width=\"0.7\" stroke-dasharray=\"3,1\"/><text x=\"36\" y=\"27.5\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" opacity=\"0.4\">G</text><rect x=\"52\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#6bb5ff15\" stroke=\"#6bb5ff\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"58\" y=\"9.8\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"5.5\" font-family=\"monospace\">b</text><line x1=\"58.0\" y1=\"11.0\" x2=\"58.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"58.0,19.0 56.0,15.0 60.0,15.0\" fill=\"#555\"/><rect x=\"50\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#6bb5ff22\" stroke=\"#6bb5ff\" stroke-width=\"1.2\"/><text x=\"58\" y=\"27.5\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" >B</text><line x1=\"58\" y1=\"29\" x2=\"58\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"54\" y1=\"37\" x2=\"62\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\"/><line x1=\"22.0\" y1=\"24.0\" x2=\"25.2\" y2=\"23.1\" stroke=\"#ff6b6bcc\" stroke-width=\"1.0\"/><polygon points=\"29.0,22.0 25.7,25.0 24.6,21.2\" fill=\"#ff6b6bcc\"/><line x1=\"44.0\" y1=\"24.0\" x2=\"47.2\" y2=\"23.1\" stroke=\"#7fff6acc\" stroke-width=\"1.0\"/><polygon points=\"51.0,22.0 47.7,25.0 46.6,21.2\" fill=\"#7fff6acc\"/><line x1=\"50\" y1=\"37\" x2=\"66\" y2=\"37\" stroke=\"#444\" stroke-width=\"0.8\"/></svg>" },
          { id:"C", svg:"<svg viewBox=\"0 0 72 46\" xmlns=\"http://www.w3.org/2000/svg\" style=\"width:100%;height:100%;display:block\"><rect x=\"8\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#ff6b6b15\" stroke=\"#ff6b6b\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"14\" y=\"9.8\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"5.5\" font-family=\"monospace\">r</text><line x1=\"14.0\" y1=\"11.0\" x2=\"14.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"14.0,19.0 12.0,15.0 16.0,15.0\" fill=\"#555\"/><rect x=\"6\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#ff6b6b22\" stroke=\"#ff6b6b\" stroke-width=\"1.2\"/><text x=\"14\" y=\"27.5\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\">R</text><line x1=\"14\" y1=\"29\" x2=\"14\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"10\" y1=\"37\" x2=\"18\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\"/><rect x=\"30\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#7fff6a15\" stroke=\"#7fff6a\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"36\" y=\"9.8\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"5.5\" font-family=\"monospace\">g</text><line x1=\"36.0\" y1=\"11.0\" x2=\"36.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"36.0,19.0 34.0,15.0 38.0,15.0\" fill=\"#555\"/><rect x=\"28\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#7fff6a11\" stroke=\"#7fff6a\" stroke-width=\"0.7\" stroke-dasharray=\"3,1\"/><text x=\"36\" y=\"27.5\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" opacity=\"0.4\">G</text><rect x=\"52\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#6bb5ff15\" stroke=\"#6bb5ff\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"58\" y=\"9.8\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"5.5\" font-family=\"monospace\">b</text><line x1=\"58.0\" y1=\"11.0\" x2=\"58.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"58.0,19.0 56.0,15.0 60.0,15.0\" fill=\"#555\"/><rect x=\"50\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#6bb5ff11\" stroke=\"#6bb5ff\" stroke-width=\"0.7\" stroke-dasharray=\"3,1\"/><text x=\"58\" y=\"27.5\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" opacity=\"0.4\">B</text><line x1=\"44.0\" y1=\"24.0\" x2=\"44.8\" y2=\"25.6\" stroke=\"#6bb5ffcc\" stroke-width=\"1.0\"/><polygon points=\"43.0,22.0 46.6,24.7 43.0,26.5\" fill=\"#6bb5ffcc\"/><line x1=\"22.0\" y1=\"24.0\" x2=\"22.8\" y2=\"25.6\" stroke=\"#7fff6acc\" stroke-width=\"1.0\"/><polygon points=\"21.0,22.0 24.6,24.7 21.0,26.5\" fill=\"#7fff6acc\"/><line x1=\"8\" y1=\"37\" x2=\"22\" y2=\"37\" stroke=\"#444\" stroke-width=\"0.8\"/></svg>" },
          { id:"D", svg:"<svg viewBox=\"0 0 72 46\" xmlns=\"http://www.w3.org/2000/svg\" style=\"width:100%;height:100%;display:block\"><rect x=\"8\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#ff6b6b15\" stroke=\"#ff6b6b\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"14\" y=\"9.8\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"5.5\" font-family=\"monospace\">r</text><line x1=\"14.0\" y1=\"11.0\" x2=\"14.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"14.0,19.0 12.0,15.0 16.0,15.0\" fill=\"#555\"/><rect x=\"6\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#ff6b6b22\" stroke=\"#ff6b6b\" stroke-width=\"1.2\"/><text x=\"14\" y=\"27.5\" text-anchor=\"middle\" fill=\"#ff6b6b\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" >R</text><line x1=\"14\" y1=\"29\" x2=\"14\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"10\" y1=\"37\" x2=\"18\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\"/><rect x=\"30\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#7fff6a15\" stroke=\"#7fff6a\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"36\" y=\"9.8\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"5.5\" font-family=\"monospace\">g</text><line x1=\"36.0\" y1=\"11.0\" x2=\"36.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"36.0,19.0 34.0,15.0 38.0,15.0\" fill=\"#555\"/><rect x=\"28\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#7fff6a11\" stroke=\"#7fff6a\" stroke-width=\"0.7\" stroke-dasharray=\"3,1\"/><text x=\"36\" y=\"27.5\" text-anchor=\"middle\" fill=\"#7fff6a\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" opacity=\"0.4\">G</text><rect x=\"52\" y=\"3\" width=\"12\" height=\"8\" rx=\"1.5\" fill=\"#6bb5ff15\" stroke=\"#6bb5ff\" stroke-width=\"0.8\" stroke-dasharray=\"2,1\"/><text x=\"58\" y=\"9.8\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"5.5\" font-family=\"monospace\">b</text><line x1=\"58.0\" y1=\"11.0\" x2=\"58.0\" y2=\"15.0\" stroke=\"#555\" stroke-width=\"0.8\"/><polygon points=\"58.0,19.0 56.0,15.0 60.0,15.0\" fill=\"#555\"/><rect x=\"50\" y=\"19\" width=\"16\" height=\"10\" rx=\"2\" fill=\"#6bb5ff22\" stroke=\"#6bb5ff\" stroke-width=\"1.2\"/><text x=\"58\" y=\"27.5\" text-anchor=\"middle\" fill=\"#6bb5ff\" font-size=\"6.5\" font-family=\"monospace\" font-weight=\"bold\" >B</text><line x1=\"58\" y1=\"29\" x2=\"58\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\" stroke-dasharray=\"2,1\"/><line x1=\"54\" y1=\"37\" x2=\"62\" y2=\"37\" stroke=\"#444\" stroke-width=\"1\"/><line x1=\"29.0\" y1=\"24.0\" x2=\"24.9\" y2=\"23.0\" stroke=\"#7fff6acc\" stroke-width=\"1.0\"/><polygon points=\"21.0,22.0 25.4,21.0 24.4,24.9\" fill=\"#7fff6acc\"/><line x1=\"43.0\" y1=\"24.0\" x2=\"47.1\" y2=\"23.0\" stroke=\"#7fff6acc\" stroke-width=\"1.0\"/><polygon points=\"51.0,22.0 47.6,24.9 46.6,21.0\" fill=\"#7fff6acc\"/><line x1=\"8\" y1=\"37\" x2=\"22\" y2=\"37\" stroke=\"#444\" stroke-width=\"0.8\"/><line x1=\"50\" y1=\"37\" x2=\"66\" y2=\"37\" stroke=\"#444\" stroke-width=\"0.8\"/></svg>" },
        ].map(function(m) {
          var active = (settings2.fmMatrix||"A") === m.id;
          return el("div", { key:m.id,
            style:{
              border:"1px solid " + (active?"#7fff6a":"#1e1e1e"),
              borderRadius:3,
              background: active?"rgba(127,255,106,0.04)":"transparent",
              cursor:"pointer",
              height:52,
              overflow:"hidden",
              position:"relative"
            },
            onClick:function(){
              setSettings2(function(s){var n=Object.assign({},s);n.fmMatrix=m.id;return n;});
              var eng=eng2Ref.current;
              if(eng){eng.settings.fmMatrix=m.id;eng.spawnOscillators&&eng.spawnOscillators();}
            }
          },
            el("div", {
              dangerouslySetInnerHTML:{__html: m.svg},
              style:{width:"100%",height:"100%"}
            }),
            el("div",{style:{
              position:"absolute",bottom:2,right:3,
              fontSize:7,color:active?"#7fff6a":"#2a2a2a",
              letterSpacing:"0.08em"
            }},m.id)
          );
        })
      ),
      el("div", { style:{ fontSize:8, color:"#444", letterSpacing:"0.15em", textTransform:"uppercase", marginBottom:6 } }, "Interval range per oscillator"),
      ["R","G","B"].map(function(ch) {
        var iKey = "interval"+ch;
        var cmKey = "cm"+ch;
        var color = ch==="R"?"#ff6b6b":ch==="G"?"#7fff6a":"#6bb5ff";
        var avgVal = frameData ? (ch==="R"?frameData.avgR:ch==="G"?frameData.avgG:frameData.avgB) : 0;
        var bgColor = ch==="R"?"rgba(255,80,80,0.13)":ch==="G"?"rgba(80,255,80,0.10)":"rgba(80,140,255,0.13)";
        return el("div", { key:ch, style:{ borderBottom:"1px solid #141414", paddingBottom:6, marginBottom:4, position:"relative", overflow:"hidden" } },
          el("div", { style:{ position:"absolute", left:0, top:0, bottom:0, width:(avgVal*100)+"%", background:bgColor, pointerEvents:"none", transition:"width 0.15s ease" } }),
          el("div", { className:"sr", style:{ borderBottom:"none", paddingBottom:2, position:"relative" } },
            el("label", { style:{ color:color, minWidth:16, fontSize:9, letterSpacing:"0.1em" } }, ch),
            el("div", { style:{ display:"flex", gap:2, flexWrap:"wrap" } },
              INTERVAL_NAMES.map(function(n) {
                var isSel = settings2[iKey]===n;
                return el("button", {
                  key:n,
                  className:"sg",
                  onClick:function(){
                    setSettings2(function(s){var ns=Object.assign({},s);ns[iKey]=n;return ns;});
                    var eng=eng2Ref.current;
                    if(eng){eng.settings[iKey]=n;eng.updateIntervals&&eng.updateIntervals();}
                  },
                  title: INTERVAL_LABELS[n],
                  style:{
                    borderColor: isSel ? color : color+"44",
                    color: isSel ? color : color+"88",
                    background: isSel ? color+"11" : "transparent"
                  }
                }, n);
              })
            )
          ),
          el("div", { style:{ display:"flex", alignItems:"center", gap:4, paddingLeft:20 } },
            el("span", { style:{ fontSize:8, color:"#333", letterSpacing:"0.08em", minWidth:24 } }, "C:M"),
            el("div", { style:{ display:"flex", gap:2, flexWrap:"wrap" } },
              CM_NAMES.map(function(n) {
                var isSel = settings2[cmKey]===n;
                return el("button", {
                  key:n,
                  className:"sg",
                  onClick:function(){
                    setSettings2(function(s){var ns=Object.assign({},s);ns[cmKey]=n;return ns;});
                    var eng=eng2Ref.current;
                    if(eng){eng.settings[cmKey]=n;eng.spawnOscillators&&eng.spawnOscillators();}
                  },
                  title: CM_LABELS[n],
                  style:{
                    borderColor: isSel ? color : color+"44",
                    color: isSel ? color : color+"88",
                    background: isSel ? color+"11" : "transparent"
                  }
                }, n);
              })
            )
          )
        );
      }),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:3,marginTop:6} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label", null, "FM depth"),
          el("span", { style:{fontSize:9,color:"#7fff6a"} }, ((settings2.fmDepth||0.4)*100).toFixed(0)+"%")
        ),
        el("input", { type:"range", min:0, max:100, value:Math.round((settings2.fmDepth||0.4)*100),
          onChange:function(e){
            var v = e.target.value/100;
            setSettings2(function(s){var ns=Object.assign({},s);ns.fmDepth=v;return ns;});
            var eng=eng2Ref.current;if(eng)eng.settings.fmDepth=v;
          }
        })
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:3,marginTop:6} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label", null, "FM modulator shape"),
          el("span", { style:{fontSize:9,color:"#7fff6a"} },
            (settings2.fmModShape||0) < 0.1 ? "sine" : (settings2.fmModShape||0) < 0.6 ? "triangle" : "square"
          )
        ),
        el("input", { type:"range", min:0, max:100, value:Math.round((settings2.fmModShape||0)*100),
          onChange:function(e){
            var v = e.target.value/100;
            setSettings2(function(s){var ns=Object.assign({},s);ns.fmModShape=v;return ns;});
            var eng=eng2Ref.current;if(eng)eng.settings.fmModShape=v;
          }
        })
      )
    ),

    // ── User LFOs (both engines) ──────────────────────────────────────────────
    el("div", { style:{ padding:"8px 14px 14px", overflowY:"auto" } },
      el("div", { style:{ fontSize:8, color:"#444", letterSpacing:"0.15em", textTransform:"uppercase", marginBottom:8 } }, "LFO"),
      ["lfo1","lfo2"].map(function(which) {
        var cfg   = lfoState[which];
        var label = which === "lfo1" ? "LFO 1" : "LFO 2";
        return el("div", { key:which, style:{ borderBottom:"1px solid #141414", paddingBottom:8, marginBottom:8 } },

          // Header row: label + wave dropdown + dest dropdown + on/off
          el("div", { style:{ display:"flex", gap:4, alignItems:"center", marginBottom:6 } },
            el("span", { style:{ fontSize:9, color:"#7fff6a", letterSpacing:"0.1em", minWidth:34 } }, label),
            el("select", {
              value: cfg.wave || "sine",
              onChange: function(e){ setLfo(which, "wave", e.target.value); },
              style:{ background:"#0a0a0b", border:"1px solid #222", color:"#888", fontFamily:"'IBM Plex Mono',monospace", fontSize:9, padding:"2px 4px", flex:1 }
            },
              LFO_WAVES.map(function(w){ return el("option",{key:w,value:w},w); })
            ),
            el("select", {
              value: cfg.dest,
              onChange: function(e){ setLfo(which, "dest", e.target.value); },
              style:{ background:"#0a0a0b", border:"1px solid #222", color:"#888", fontFamily:"'IBM Plex Mono',monospace", fontSize:9, padding:"2px 4px", flex:2 }
            },
              LFO_DEST_NAMES.filter(function(d){
                var key = LFO_DESTS[d];
                if (activeEngine === "1" && key && key.indexOf("fm") === 0) return false;
                if (activeEngine === "1" && key === "haas.gain") return false;
                return true;
              }).map(function(d){ return el("option",{key:d,value:d},d); })
            ),
            el("button", {
              className:cx("sg", cfg.active&&"sel"),
              onClick:function(){ setLfo(which,"active",!cfg.active); },
              style:{ minWidth:28 }
            }, cfg.active ? "ON" : "OFF")
          ),

          // Rate slider
          el("div", { style:{display:"flex",alignItems:"center",gap:6,marginBottom:3} },
            el("span", { style:{fontSize:8,color:"#444",minWidth:30,letterSpacing:"0.08em"} }, "RATE"),
            el("input", { type:"range", min:0, max:1000, value:Math.round(Math.pow(Math.log((cfg.rate||0.5)/0.01)/Math.log(10000),1/1.5)*1000),
              onChange:function(e){
                var x = e.target.value/1000;
                var hz = 0.01 * Math.pow(10000, Math.pow(x, 1.5));
                setLfo(which,"rate", Math.min(100, Math.max(0.01, hz)));
              },
              style:{flex:1}
            }),
            el("span", { style:{fontSize:8,color:(cfg.rate||0.5)>=20?"#ff9944":"#7fff6a",minWidth:44,textAlign:"right"} },
              (cfg.rate||0.5)>=20 ? (cfg.rate||0.5).toFixed(0)+"Hz‿" : (cfg.rate||0.5).toFixed(2)+"Hz"
            )
          ),

          // Depth slider
          el("div", { style:{display:"flex",alignItems:"center",gap:6} },
            el("span", { style:{fontSize:8,color:"#444",minWidth:30,letterSpacing:"0.08em"} }, "DEPTH"),
            el("input", { type:"range", min:0, max:100, value:Math.round((cfg.depth||0)*100),
              onChange:function(e){ setLfo(which,"depth",e.target.value/100); },
              style:{flex:1}
            }),
            el("span", { style:{fontSize:8,color:"#7fff6a",minWidth:40,textAlign:"right"} }, Math.round((cfg.depth||0)*100)+"%")
          )
        );
      })
    )
  );

  return el("div", { style:{ display:"flex", flexDirection:"column", width:"100%", height:"100dvh", background:"#0a0a0b", fontFamily:"'IBM Plex Mono','Courier New',monospace", color:"#c8c8b4", userSelect:"none", WebkitUserSelect:"none", WebkitTouchCallout:"none", touchAction:"none", overflow:"hidden", maxWidth:480, margin:"0 auto" } },

    el("style", null, `
      @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@300;400;500&display=swap');
      html,body{overscroll-behavior:none;overflow:hidden;}
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
      showAdv && el("div", { style:{ position:"absolute", inset:0, background:"#0a0a0b", zIndex:10, display:"flex", flexDirection:"column", overflow:"hidden", touchAction:"pan-y" } },
        advView
      ),

    )
  );
}

ReactDOM.createRoot(document.getElementById("root")).render(React.createElement(App));