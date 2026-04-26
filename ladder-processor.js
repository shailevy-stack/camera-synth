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
    this._s = [0, 0, 0, 0]; // filter state
    this._lastCutoff = -1;
    this._g = 0;
  }

  _coeff(cutoff) {
    var wc = 2 * Math.PI * Math.min(cutoff, sampleRate * 0.45) / sampleRate;
    return wc / (1 + wc);
  }

  process(inputs, outputs, parameters) {
    var input  = inputs[0];
    var output = outputs[0];
    if (!input || !input[0] || !output || !output[0]) return true;

    var inp    = input[0];
    var out    = output[0];
    var cutoff = parameters.cutoff;
    var res    = parameters.resonance;
    var s      = this._s;

    var cutoffConst = cutoff.length === 1;
    var resConst    = res.length === 1;

    for (var i = 0; i < inp.length; i++) {
      var fc = cutoffConst ? cutoff[0] : cutoff[i];
      var r  = resConst    ? res[0]    : res[i];

      if (fc !== this._lastCutoff) {
        this._g = this._coeff(fc);
        this._lastCutoff = fc;
      }
      var g = this._g;

      // Feedback: r maps 0..1 → 0..4 (self-oscillation at 4.0)
      // Use curve so resonance peak is audible from ~0.3
      var fb = r * r * 4.0;
      var x  = inp[i] - fb * s[3];

      // 4 cascaded one-pole stages — no soft clip (limiter handles output)
      s[0] += g * (x    - s[0]);
      s[1] += g * (s[0] - s[1]);
      s[2] += g * (s[1] - s[2]);
      s[3] += g * (s[2] - s[3]);

      out[i] = s[3];
    }

    return true;
  }
}

registerProcessor('ladder-processor', LadderProcessor);
