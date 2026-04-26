// SYNESTHESIA — Stilson/Smith Moog Ladder Filter
// AudioWorkletProcessor — runs at sample rate
// 4 one-pole lowpass stages + resonance feedback
// Self-oscillates cleanly above resonance ~0.95

class LadderProcessor extends AudioWorkletProcessor {
  static get parameterDescriptors() {
    return [
      { name: 'cutoff',    defaultValue: 2000, minValue: 20,  maxValue: 20000, automationRate: 'a-rate' },
      { name: 'resonance', defaultValue: 0,    minValue: 0,   maxValue: 1,     automationRate: 'a-rate' },
    ];
  }

  constructor() {
    super();
    // Filter state — 4 one-pole stages
    this._s = [0, 0, 0, 0];
    this._lastCutoff = -1;
    this._g = 0;
    this._sampleRate = sampleRate; // global from AudioWorkletGlobalScope
  }

  // Compute one-pole coefficient from cutoff frequency
  _coeff(cutoff) {
    // Bilinear transform approximation
    var wc = 2 * Math.PI * Math.min(cutoff, this._sampleRate * 0.45) / this._sampleRate;
    var g  = wc / (1 + wc);
    return g;
  }

  process(inputs, outputs, parameters) {
    var input  = inputs[0];
    var output = outputs[0];
    if (!input || !input[0]) return true;

    var inp    = input[0];
    var out    = output[0];
    var cutoff = parameters.cutoff;
    var res    = parameters.resonance;
    var s      = this._s;
    var sr     = this._sampleRate;

    var cutoffIsConst = cutoff.length === 1;
    var resIsConst    = res.length === 1;

    for (var i = 0; i < inp.length; i++) {
      var fc = cutoffIsConst ? cutoff[0] : cutoff[i];
      var r  = resIsConst    ? res[0]    : res[i];

      // Recompute coefficient only if cutoff changed
      if (fc !== this._lastCutoff) {
        this._g = this._coeff(fc);
        this._lastCutoff = fc;
      }
      var g = this._g;

      // Resonance feedback — 4× gain at unity (Stilson/Smith)
      // r in 0..1, self-oscillation at ~1.0
      var feedback = r * 4.0 * s[3];

      // Input with feedback subtracted
      var x = inp[i] - feedback;

      // Soft clip input to prevent harsh clipping (tanh approximation)
      x = x / (1 + Math.abs(x) * 0.5);

      // 4 cascaded one-pole lowpass stages
      s[0] = s[0] + g * (x   - s[0]);
      s[1] = s[1] + g * (s[0] - s[1]);
      s[2] = s[2] + g * (s[1] - s[2]);
      s[3] = s[3] + g * (s[2] - s[3]);

      out[i] = s[3];
    }

    this._s = s;
    return true;
  }
}

registerProcessor('ladder-processor', LadderProcessor);
