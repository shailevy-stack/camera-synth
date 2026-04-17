// Camera Synth — v1.1.0
var VERSION = "1.1.0";

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
var ANALYSIS_RES  = 32;
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
  var eng = {
    ctx: null, voices: [],
    filterNode: null, reverbNode: null, reverbGain: null,
    dryGain: null, masterGain: null, limiterNode: null, analyserNode: null,
    active: false, currentPitchMidi: 60,
    wavetableData: new Float32Array(ANALYSIS_RES),
    settings: {
      voices: 1, detune: 12,
      quantize: false, scale: "pentatonic", rootNote: 48,
      pitchMin: 36, pitchMax: 72, reverbMix: 0.3, fps: 10,
    },
  };

  eng.init = function(cb) {
    try {
      var AC = window.AudioContext || window.webkitAudioContext;
      eng.ctx = new AC();

      var sr  = eng.ctx.sampleRate;
      var len = sr * 2;
      var buf = eng.ctx.createBuffer(2, len, sr);
      for (var c = 0; c < 2; c++) {
        var d = buf.getChannelData(c);
        for (var i = 0; i < len; i++) {
          d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / len, 2.5);
        }
      }
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
      if (cb) cb(null);
    } catch(e) {
      if (cb) cb(e);
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
      try { eng.voices[i].osc.stop(); eng.voices[i].osc.disconnect(); eng.voices[i].gain.disconnect(); } catch(e) {}
    }
    eng.voices = [];
    var n    = eng.settings.voices;
    var wave = eng.makeWavetable(eng.wavetableData);
    for (var i = 0; i < n; i++) {
      var osc    = eng.ctx.createOscillator();
      osc.setPeriodicWave(wave);
      var spread = n === 1 ? 0 : ((i / (n - 1)) - 0.5) * eng.settings.detune * 2;
      osc.detune.value    = spread;
      osc.frequency.value = midiToHz(eng.currentPitchMidi);
      var gain = eng.ctx.createGain();
      gain.gain.value = 0.55 / n;
      osc.connect(gain);
      gain.connect(eng.filterNode);
      osc.start();
      eng.voices.push({ osc: osc, gain: gain });
    }
  };

  eng.updateWavetable = function(data) {
    eng.wavetableData = data;
    if (!eng.ctx) return;
    var wave = eng.makeWavetable(data);
    for (var i = 0; i < eng.voices.length; i++) {
      try { eng.voices[i].osc.setPeriodicWave(wave); } catch(e) {}
    }
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
    var t = eng.ctx.currentTime;
    if (on) { eng.ctx.resume(); eng.masterGain.gain.setTargetAtTime(0.85, t, 0.15); }
    else     { eng.masterGain.gain.setTargetAtTime(0, t, 0.08); }
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

  var midY = Math.floor(h/2);
  var wt   = new Float32Array(ANALYSIS_RES);
  for (var j = 0; j < ANALYSIS_RES; j++) {
    var wpx = Math.floor((j/ANALYSIS_RES)*w);
    wt[j] = (px[(midY*w+wpx)*4] / 127.5 - 1) * 0.8;
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
  var r10 = useState(null);   var frameData    = r10[0], setFrameData   = r10[1];

  var r11 = useState({ voices:1, detune:12, quantize:false, scale:"pentatonic", rootNote:48, pitchMin:36, pitchMax:72, reverbMix:0.3, fps:10 });
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
  }, [facingMode]);

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
      ctx.strokeStyle = "rgba(127,255,106,0.7)";
      ctx.lineWidth = 1.5;
      ctx.shadowColor = "#7fff6a"; ctx.shadowBlur = 6;
      ctx.beginPath();
      var sl = W / wd.length;
      for (var i=0; i<wd.length; i++) {
        var x=i*sl, y=H/2+wd[i]*H*0.4;
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
    if (!engReady) {
      eng.init(function(err) {
        if (err) { console.error(err); return; }
        setEngReady(true);
        eng.setSoundOn(true);
        setSoundOn(true);
      });
    } else {
      var next = !soundOn;
      eng.setSoundOn(next);
      setSoundOn(next);
    }
  }, [soundOn, engReady]);

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
  var handleReload = useCallback(function() { window.location.reload(); }, []);

  var handleRecord = useCallback(function() {
    var eng = synthRef.current;
    if (recording) {
      if (mrRef.current) mrRef.current.stop();
      setRecording(false);
    } else {
      if (!eng || !eng.ctx) return;
      var dest = eng.ctx.createMediaStreamDestination();
      eng.limiterNode.connect(dest);
      var chunks = [];
      chunksRef.current = chunks;
      var mr = new MediaRecorder(dest.stream);
      mr.ondataavailable = function(e) { chunks.push(e.data); };
      mr.onstop = function() {
        var blob = new Blob(chunks, {type:"audio/webm"});
        var url  = URL.createObjectURL(blob);
        var a    = document.createElement("a");
        a.href=url; a.download="camsynth-"+Date.now()+".webm"; a.click();
        try { eng.limiterNode.disconnect(dest); } catch(e) {}
      };
      mr.start();
      mrRef.current = mr;
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
      .cb{background:transparent;border:1px solid #222;color:#777;font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:.08em;padding:6px 10px;cursor:pointer;text-transform:uppercase;-webkit-tap-highlight-color:transparent;touch-action:manipulation;transition:border-color .15s,color .15s;}
      .cb:active{background:#111;}
      .cb.on{border-color:#7fff6a;color:#7fff6a;}
      .cb.rec{border-color:#ff4444;color:#ff4444;background:rgba(255,68,68,.08);}
      .cb.dng{border-color:#ff4444;color:#ff4444;}
      .sg{background:transparent;border:1px solid #1e1e1e;color:#444;font-family:'IBM Plex Mono',monospace;font-size:9px;padding:3px 7px;cursor:pointer;-webkit-tap-highlight-color:transparent;touch-action:manipulation;transition:all .1s;}
      .sg.sel{border-color:#7fff6a;color:#7fff6a;background:rgba(127,255,106,.06);}
      .sr{display:flex;align-items:center;justify-content:space-between;padding:7px 0;border-bottom:1px solid #141414;}
      .sr label{font-size:9px;letter-spacing:.1em;color:#444;text-transform:uppercase;}
      input[type=range]{-webkit-appearance:none;width:100%;height:2px;background:#1e1e1e;outline:none;border-radius:1px;}
      input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:14px;height:14px;background:#7fff6a;border-radius:50%;cursor:pointer;}
      input[type=range]::-moz-range-thumb{width:14px;height:14px;background:#7fff6a;border-radius:50%;border:none;cursor:pointer;}
    `),

    // Header
    el("div", { style:{ display:"flex", justifyContent:"space-between", alignItems:"center", padding:"10px 14px 6px", flexShrink:0 } },
      el("div", { style:{ display:"flex", alignItems:"baseline", gap:7 } },
        el("span", { style:{ fontSize:10, letterSpacing:"0.2em", color:"#2a2a2a", textTransform:"uppercase" } }, "CamSynth"),
        el("span", { style:{ fontSize:8, color:"#1e1e1e", letterSpacing:"0.1em" } }, "v"+VERSION)
      ),
      el("div", { style:{ display:"flex", gap:4, alignItems:"center" } },
        frameData && el("div", { style:{ display:"flex", gap:5, alignItems:"center" } },
          el("div", { style:{ width:36, height:2, background:"#1a1a1a", borderRadius:1, overflow:"hidden" } },
            el("div", { style:{ height:"100%", width:(frameData.luma*100).toFixed(0)+"%", background:"#7fff6a", transition:"width 0.1s" } })
          ),
          el("div", { style:{ width:8, height:8, borderRadius:"50%", background:hueCSS, boxShadow:"0 0 5px "+hueCSS, flexShrink:0 } })
        ),
        el("button", { className:"cb", onClick:handleFlip }, "\u21c4"),
        el("button", { className:"cb", onClick:handleReload }, "\u21ba")
      )
    ),

    // Camera — fixed height, crops rather than expands
    el("div", { style:{ position:"relative", background:"#050505", overflow:"hidden", borderTop:"1px solid #141414", borderBottom:"1px solid #141414", flexShrink:0, height:"55vh" } },
      el("video", { ref:videoRef, playsInline:true, muted:true, autoPlay:true, style:{ width:"100%", height:"100%", objectFit:"cover", display:"block", transform:facingMode==="user"?"scaleX(-1)":"none" } }),
      showScope && el("canvas", { ref:scopeRef, width:480, height:80, style:{ position:"absolute", bottom:0, left:0, width:"100%", height:60, pointerEvents:"none" } }),
      frameData && el("div", { style:{ position:"absolute", top:8, left:8, fontSize:8, color:"rgba(127,255,106,0.35)", letterSpacing:"0.1em", lineHeight:2, pointerEvents:"none" } },
        el("div",null,"LMA "+(frameData.luma*100).toFixed(1)),
        el("div",null,"HUE "+Math.round(frameData.hue*360)+"\xb0"),
        el("div",null,"SAT "+(frameData.saturation*100).toFixed(1)),
        el("div",null,"COM "+frameData.comX.toFixed(2)+"\xb7"+frameData.comY.toFixed(2))
      ),
      !camReady && !camError && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:8 } },
        el("span", { style:{ color:"#2a2a2a", fontSize:10, letterSpacing:"0.2em" } }, "AWAITING CAMERA"),
        el("span", { style:{ color:"#1e1e1e", fontSize:8, letterSpacing:"0.1em" } }, "grant permission when prompted")
      ),
      camError && el("div", { style:{ position:"absolute", inset:0, display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:10 } },
        el("span", { style:{ color:"#ff4444", fontSize:10, letterSpacing:"0.15em" } }, camError),
        el("button", { className:"cb", onClick:handleReload, style:{ fontSize:9 } }, "\u21ba reload & retry")
      ),
      el("canvas", { ref:captureRef, style:{ display:"none" } })
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
      el("button", { className:cx("cb", recording&&"rec"), onClick:handleRecord, style:{ flex:1 } }, recording ? "\u25cf REC" : "\u25cb REC"),
      el("button", { className:cx("cb", showScope&&"on"), onClick:function(){setShowScope(function(s){return !s;});}, style:{ flex:1 } }, "\u223f"),
      el("button", { className:cx("cb", showSettings&&"on"), onClick:function(){setShowSettings(function(s){return !s;});}, style:{ flex:1 } }, "\u2699")
    ),

    // Settings drawer
    showSettings && el("div", { style:{ padding:"8px 14px 14px", borderTop:"1px solid #141414", background:"#0c0c0d", overflowY:"auto", flexShrink:0, maxHeight:"30vh" } },

      el("div", { className:"sr" },
        el("label",null,"Voices"),
        el("div", { style:{display:"flex",gap:2} },
          VOICE_OPTIONS.map(function(v){ return el("button",{key:v,className:cx("sg",settings.voices===v&&"sel"),onClick:function(){setSetting("voices",v);}},v); })
        )
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:5} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label",null,"Detune"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},settings.detune+" ct")
        ),
        el("input",{type:"range",min:0,max:50,value:settings.detune,onChange:function(e){setSetting("detune",+e.target.value);}})
      ),

      el("div", { className:"sr" },
        el("label",null,"Quantize pitch"),
        el("button",{className:cx("sg",settings.quantize&&"sel"),onClick:function(){setSetting("quantize",!settings.quantize);}}, settings.quantize?"ON":"OFF")
      ),

      settings.quantize && el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:5} },
        el("label",null,"Scale"),
        el("div", { style:{display:"flex",flexWrap:"wrap",gap:2,marginTop:2} },
          SCALE_NAMES.map(function(s){ return el("button",{key:s,className:cx("sg",settings.scale===s&&"sel"),onClick:function(){setSetting("scale",s);}},s); })
        )
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:5} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label",null,"Pitch range"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}}, NOTE_NAMES[settings.pitchMin%12]+(Math.floor(settings.pitchMin/12)-1)+" \u2192 "+NOTE_NAMES[settings.pitchMax%12]+(Math.floor(settings.pitchMax/12)-1))
        ),
        el("div", { style:{display:"flex",gap:8,width:"100%"} },
          el("input",{type:"range",min:24,max:60,value:settings.pitchMin,onChange:function(e){setSetting("pitchMin",Math.min(+e.target.value,settings.pitchMax-4));}}),
          el("input",{type:"range",min:48,max:84,value:settings.pitchMax,onChange:function(e){setSetting("pitchMax",Math.max(+e.target.value,settings.pitchMin+4));}})
        )
      ),

      el("div", { className:"sr", style:{flexDirection:"column",alignItems:"flex-start",gap:5} },
        el("div", { style:{display:"flex",width:"100%",justifyContent:"space-between"} },
          el("label",null,"Reverb mix"),
          el("span",{style:{fontSize:9,color:"#7fff6a"}},Math.round(settings.reverbMix*100)+"%")
        ),
        el("input",{type:"range",min:0,max:100,value:Math.round(settings.reverbMix*100),onChange:function(e){setSetting("reverbMix",e.target.value/100);}})
      ),

      el("div", { className:"sr" },
        el("label",null,"Analysis rate"),
        el("div", { style:{display:"flex",gap:2} },
          FPS_OPTIONS.map(function(f){ return el("button",{key:f,className:cx("sg",settings.fps===f&&"sel"),onClick:function(){setSetting("fps",f);}},f+"fps"); })
        )
      ),

      el("div", { style:{marginTop:10,display:"flex",gap:5} },
        el("button",{className:"cb dng",onClick:handlePanic,style:{flex:1,padding:"9px 0",letterSpacing:"0.1em"}},"\u25a0 PANIC"),
        el("button",{className:"cb",onClick:handleReload,style:{flex:1,padding:"9px 0",letterSpacing:"0.1em"}},"\u21ba RELOAD")
      ),

      el("div", { style:{marginTop:10,textAlign:"center"} },
        el("span",{style:{fontSize:8,color:"#1a1a1a",letterSpacing:"0.15em"}},"CAMERA SYNTH v"+VERSION)
      )
    )
  );
}

ReactDOM.createRoot(document.getElementById("root")).render(React.createElement(App));
