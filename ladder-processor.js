// SYNESTHESIA — Stilson/Smith Moog Ladder Filter
// AudioWorkletProcessor — runs at sample rate
// 4 one-pole lowpass stages + resonance feedback

class LadderProcessor extends AudioWorkletProcessor {
  static get parameterDescriptors() {
    return [
      { name: 'cutoff',    defaultValue: 2000, minValue: 20,  maxValue: 20000, automationRate: 'a-rate' },
      { name: 'resonance', defaultValue: 0,    minValue: 0,   maxValue: 1,     automationRate: 'a-rate' },
    ];
  }

  constructor() {
    super();
    // Two sets of state for stereo (L and R)
    this._sL = [0, 0, 0, 0];
    this._sR = [0, 0, 0, 0];
    this._lastCutoff = -1;
    this._g = 0;
  }

  _coeff(cutoff) {
    var wc = 2 * Math.PI * Math.min(cutoff, sampleRate * 0.45) / sampleRate;
    return wc / (1 + wc);
  }

  _processChannel(inp, out, s, cutoff, res) {
    var cutoffConst = cutoff.length === 1;
    var resConst    = res.length === 1;
    for (var i = 0; i < inp.length; i++) {
      var fc = cutoffConst ? cutoff[0] : cutoff[i];
      var r  = resConst    ? res[0]    : res[i];
      if (fc !== this._lastCutoff) {
        this._g = this._coeff(fc);
        this._lastCutoff = fc;
      }
      var g  = this._g;
      var fb = r * r * 4.0;
      var x  = inp[i] - fb * s[3];
      s[0] += g * (x    - s[0]);
      s[1] += g * (s[0] - s[1]);
      s[2] += g * (s[1] - s[2]);
      s[3] += g * (s[2] - s[3]);
      out[i] = s[3];
    }
  }

  process(inputs, outputs, parameters) {
    var inChans  = inputs[0]  || [];
    var outChans = outputs[0] || [];
    if (!inChans.length || !outChans.length) return true;

    var cutoff = parameters.cutoff;
    var res    = parameters.resonance;

    // Process L channel
    if (inChans[0] && outChans[0]) {
      this._processChannel(inChans[0], outChans[0], this._sL, cutoff, res);
    }
    // Process R channel — if mono input, copy L output to R
    if (outChans[1]) {
      if (inChans[1]) {
        this._processChannel(inChans[1], outChans[1], this._sR, cutoff, res);
      } else if (outChans[0]) {
        // Mono input — copy processed L to R
        outChans[1].set(outChans[0]);
      }
    }

    return true;
  }
}

registerProcessor('ladder-processor', LadderProcessor);
