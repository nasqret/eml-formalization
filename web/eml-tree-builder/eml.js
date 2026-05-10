// =====================================================================
// EML Tree Builder — interactive compiler for arXiv:2603.21852
//
// Implements the F36 → EL → EML pipeline as a self-contained browser
// app. Mirrors the structural macros from SI §2.1 of the paper, plus
// derived combinators for the unary/binary primitives in Table 1.
//
// Tree representation:  { kind: 'one' }
//                     | { kind: 'var', name: string }
//                     | { kind: 'eml', a: T, b: T }
// =====================================================================

// ---------------------------------------------------------------------
// EML grammar constructors
// ---------------------------------------------------------------------

const EML = {
  one:        ()      => ({ kind: 'one' }),
  var:        (name)  => ({ kind: 'var', name }),
  eml:        (a, b)  => ({ kind: 'eml', a, b }),
};

// Tree-size measure (matches RPN_length in KCounting.lean).
// `realize` nodes are opaque closed-constant sub-trees (π, i, etc.) —
// rendered as single leaves but contributing their real K-count.
function rpnLength(t) {
  if (t.kind === 'one' || t.kind === 'var') return 1;
  if (t.kind === 'realize') return t.k;
  return 1 + rpnLength(t.a) + rpnLength(t.b);
}

function depth(t) {
  if (t.kind === 'one' || t.kind === 'var' || t.kind === 'realize') return 0;
  return 1 + Math.max(depth(t.a), depth(t.b));
}

function leafCount(t) {
  if (t.kind === 'one' || t.kind === 'var' || t.kind === 'realize') return 1;
  return leafCount(t.a) + leafCount(t.b);
}

function emlCount(t) {
  if (t.kind === 'one' || t.kind === 'var' || t.kind === 'realize') return 0;
  return 1 + emlCount(t.a) + emlCount(t.b);
}

function rpnString(t) {
  if (t.kind === 'one') return '1';
  if (t.kind === 'var') return t.name;
  if (t.kind === 'realize') return `⟨${t.name}⟩`;
  return rpnString(t.a) + ' ' + rpnString(t.b) + ' E';
}

// ---------------------------------------------------------------------
// Structural macros (SI §2.1 verbatim)
// ---------------------------------------------------------------------

// exp(z) ↦ eml(z, 1)
const mkExp = (z) => EML.eml(z, EML.one());

// ln(z) ↦ eml(1, exp(eml(1, z))) = eml(1, eml(eml(1, z), 1))
const mkLog = (z) => EML.eml(EML.one(), mkExp(EML.eml(EML.one(), z)));

// x − y ↦ eml(ln(x), exp(y))
const mkSub = (x, y) => EML.eml(mkLog(x), mkExp(y));

// −z ↦ ln(1) − z
const mkNeg = (z) => mkSub(mkLog(EML.one()), z);

// x + y ↦ x − (−y)
const mkAdd = (x, y) => mkSub(x, mkNeg(y));

// 1/z ↦ exp(−ln(z))
const mkInv = (z) => mkExp(mkNeg(mkLog(z)));

// x · y ↦ exp(ln(x) + ln(y))
const mkMul = (x, y) => mkExp(mkAdd(mkLog(x), mkLog(y)));

// x / y ↦ x · (1/y)
const mkDiv = (x, y) => mkMul(x, mkInv(y));

// x² ↦ x · x
const mkSq = (x) => mkMul(x, x);

// x/2 ↦ x · (1/2). For 2 we use 1 + 1.
function mkConstNat(n) {
  if (n === 0) return mkNeg(EML.one()); // 0 = 1 - 1; but mkNeg gives ln(1) - z;
                                         // closer: use ln(1) directly; here 0 = ln(1)
  if (n === 1) return EML.one();
  // n ≥ 2: 1 + 1 + ... + 1
  let acc = EML.one();
  for (let i = 1; i < n; i++) acc = mkAdd(acc, EML.one());
  return acc;
}

const mkZero = () => mkLog(EML.one()); // ln(1) = 0
const mkTwo  = () => mkAdd(EML.one(), EML.one());
const mkHalf = () => mkInv(mkTwo());
const mkE    = () => mkExp(EML.one());
const mkPi   = () => {
  // π = (−L(−1)) (since L(−1) = −iπ in extended-real EML; absolute value
  // in the real-fragment sense gives π). Real-fragment fallback:
  // we cannot truly construct π without complex; document below.
  // For the demo, we return a placeholder eml computing log(−1)-style;
  // the artefact's actual π witness uses the EMLRealizationℂ closure
  // (K = 233 nodes).
  return mkNeg(mkLog(mkNeg(EML.one())));
};
const mkNegOne = () => mkSub(mkZero(), EML.one());

// halve(x) = x / 2
const mkHalve = (x) => mkDiv(x, mkTwo());

// avg(x, y) = (x + y) / 2
const mkAvg = (x, y) => mkHalve(mkAdd(x, y));

// √x ↦ exp((1/2) · log(x))
const mkSqrt = (x) => mkExp(mkMul(mkHalf(), mkLog(x)));

// x^y ↦ exp(y · log(x))
const mkPow = (x, y) => mkExp(mkMul(y, mkLog(x)));

// log_b y = log(y) / log(b)
const mkLogB = (b, y) => mkDiv(mkLog(y), mkLog(b));

// hypot(x, y) = √(x² + y²)
const mkHypot = (x, y) => mkSqrt(mkAdd(mkSq(x), mkSq(y)));

// σ(x) = 1 / (1 + exp(−x))
const mkSigma = (x) => mkInv(mkAdd(EML.one(), mkExp(mkNeg(x))));

// sinh(x) = (exp(x) − exp(−x)) / 2
const mkSinh = (x) => mkHalve(mkSub(mkExp(x), mkExp(mkNeg(x))));

// cosh(x) = (exp(x) + exp(−x)) / 2
const mkCosh = (x) => mkHalve(mkAdd(mkExp(x), mkExp(mkNeg(x))));

// tanh(x) = sinh(x) / cosh(x)
const mkTanh = (x) => mkDiv(mkSinh(x), mkCosh(x));

// arsinh(x) = log(x + √(x² + 1))
const mkArsinh = (x) => mkLog(mkAdd(x, mkSqrt(mkAdd(mkSq(x), EML.one()))));

// arcosh(x) = log(x + √(x² − 1))
const mkArcosh = (x) => mkLog(mkAdd(x, mkSqrt(mkSub(mkSq(x), EML.one()))));

// artanh(x) = (1/2) · log((1 + x) / (1 − x))
const mkArtanh = (x) => mkMul(mkHalf(), mkLog(mkDiv(mkAdd(EML.one(), x),
                                                     mkSub(EML.one(), x))));

// ---------------------------------------------------------------------
// Complex-grammar (EMLTermℂ) macros — same syntactic shape as the real
// grammar (`one`, `var`, `eml`) but interpreted with `Complex.exp` /
// `Complex.log`. The macros mostly mirror the real ones; the
// principal difference is `mkAddℂ`, which uses the explicit 9-node
// "ADDsafe" pattern from `EML/Framework/Complex/Builders/Trig.lean`
// so principal-branch behaviour is tracked correctly.
// ---------------------------------------------------------------------

const mkLogC = (T) =>
  EML.eml(EML.one(), EML.eml(EML.eml(EML.one(), T), EML.one()));
const mkExpC = (T) => EML.eml(T, EML.one());

// 9-node ADDsafe pattern. Verbatim from Builders/Trig.lean line 58–65.
const mkAddC = (A, B) =>
  EML.eml(
    EML.eml(EML.one(),
      EML.eml(EML.eml(EML.one(), EML.eml(A, EML.one())), EML.one())),
    EML.eml(
      EML.eml(
        EML.eml(EML.one(),
          EML.eml(EML.eml(EML.one(), EML.eml(A, EML.eml(A, EML.one()))),
                  EML.one())),
        EML.eml(B, EML.one())
      ),
      EML.one()
    )
  );

const mkSubC = (A, B) => EML.eml(mkLogC(A), mkExpC(B));
const mkMulC = (A, B) => mkExpC(mkAddC(mkLogC(A), mkLogC(B)));
const mkDivC = (A, B) => mkExpC(mkSubC(mkLogC(A), mkLogC(B)));

// ---------------------------------------------------------------------
// Closed-constant atoms. K-counts taken verbatim from
// `EML.Framework.KCounting`. Rendered as single labelled leaves;
// their internal structure (the EMLRealizationℂ packages in the Lean
// repo) is hidden because they would otherwise dominate the canvas.
// ---------------------------------------------------------------------

const iTermC    = { kind: 'realize', name: 'iℂ',  k: 407, projection: '.im' };
const piTermC   = { kind: 'realize', name: 'πℂ',  k: 233, projection: '.re' };
const negITermC = { kind: 'realize', name: '−iℂ', k: 127, projection: '.im' };
const zeroTermC = { kind: 'realize', name: '0ℂ',  k: 7,   projection: '.re' };
const twoTermC  = { kind: 'realize', name: '2ℂ',  k: 19,  projection: '.re' };

// ---------------------------------------------------------------------
// Trig witnesses — verbatim ports from
// `EML.Framework.Complex.{Closures,Builders}.Trig`.
// ---------------------------------------------------------------------

// arctanTermℂ = mkLogℂ (mkAddℂ 1 (mkMulℂ i (var 0)))
// (eval).im = Real.arctan x   for x ∈ (0, π)  [ x ≠ 0 by widening ]
function arctanTermC(varName) {
  return mkLogC(mkAddC(EML.one(), mkMulC(iTermC, EML.var(varName))));
}

// tanCoreTermℂ = mkDivℂ (mkSubℂ E2 1) (mkAddℂ 1 E2)
//   E2 := mkExpℂ (mkMulℂ i (mkMulℂ 2 (var 0)))
// (eval).im = Real.tan x   for x ∈ (0, π/2)
function tanCoreTermC(varName) {
  const twoX = mkMulC(twoTermC, EML.var(varName));
  const I2x  = mkMulC(iTermC, twoX);
  const E2   = mkExpC(I2x);
  return mkDivC(mkSubC(E2, EML.one()), mkAddC(EML.one(), E2));
}

// cosTermℂ = mkExpℂ (mkExpℂ (eml cosLhs cosRhs))
//   cosLhs := eml 1 (eml (eml 1 (eml (mkLogℂ i) 1)) 1)
//   cosRhs := eml (eml (eml 1 (eml (eml 1 (eml (mkLogℂ i) (eml (mkLogℂ i) 1))) 1)) (eml (mkLogℂ x) 1)) 1
// Evaluates to exp(exp(log i + log x)) = exp(i·x); .re = cos x for x > 0.
function cosTermC(varName) {
  const x = EML.var(varName);
  const logI = mkLogC(iTermC);
  const cosLhs = EML.eml(EML.one(),
    EML.eml(EML.eml(EML.one(), EML.eml(logI, EML.one())), EML.one()));
  const cosRhs = EML.eml(
    EML.eml(
      EML.eml(EML.one(),
        EML.eml(EML.eml(EML.one(),
          EML.eml(logI, EML.eml(logI, EML.one()))), EML.one())),
      EML.eml(mkLogC(x), EML.one())),
    EML.one());
  return mkExpC(mkExpC(EML.eml(cosLhs, cosRhs)));
}

// sinTermℂ via the identity sin x = cos(π/2 − x). We substitute
// (π/2 − var 0) for var 0 inside cosTermC, which mirrors Path C′'s
// `cosTermℂ.subst0 halfPiMinusXℂ`. The displayed tree shows the
// substituted construction.
function halfPiC() {
  // π/2 = mkDivℂ π 2
  return mkDivC(piTermC, twoTermC);
}
function sinTermC(varName) {
  // shifted = π/2 − x
  const shifted = mkSubC(halfPiC(), EML.var(varName));
  // Inline a fresh cosTermC with shifted as the variable:
  // we cannot reuse cosTermC(varName) verbatim — we must replace
  // every occurrence of `var varName` with `shifted`. Easier:
  // re-emit the cosTermC body with `shifted` in place of `var x`.
  const logI = mkLogC(iTermC);
  const cosLhs = EML.eml(EML.one(),
    EML.eml(EML.eml(EML.one(), EML.eml(logI, EML.one())), EML.one()));
  const cosRhs = EML.eml(
    EML.eml(
      EML.eml(EML.one(),
        EML.eml(EML.eml(EML.one(),
          EML.eml(logI, EML.eml(logI, EML.one()))), EML.one())),
      EML.eml(mkLogC(shifted), EML.one())),
    EML.one());
  return mkExpC(mkExpC(EML.eml(cosLhs, cosRhs)));
}

// arccosTermℂ uses √(1 − x²) — we build that in the real fragment
// then lift, but in the browser tool we approximate with the complex
// macros directly: arccos x = (Complex.log (x + i·√(1 − x²))) / i,
// projected to .im. We use the formula
//   arccos x = π/2 − arcsin x
//          = π/2 − (1/i) · log(i·x + √(1 − x²))
// For the tree shape we mirror the Lean witness `arccosTermℂ` which
// uses `mkLogℂ (mkAddℂ (var 0) (mkMulℂ i (sqrtOneSubSqTerm var)))`.
// We approximate sqrt via the structural compiler:
function sqrtOneSubSqC(varName) {
  // sqrt(1 - x²) via mkExpℂ((1/2) · log(1 - x²))
  // and 1 - x² via mkSubℂ 1 (mkMulℂ x x).
  const x = EML.var(varName);
  const xSq = mkMulC(x, x);
  const oneMinusXSq = mkSubC(EML.one(), xSq);
  return mkExpC(mkMulC(halfC(), mkLogC(oneMinusXSq)));
}
function halfC() {
  // 1/2 = mkDivℂ 1 2
  return mkDivC(EML.one(), twoTermC);
}

// arcsinTermℂ = mkLogℂ (mkAddℂ (mkMulℂ i x) (sqrt(1 − x²)))
// (eval).im = Real.arcsin x for x ∈ (0, 1)
function arcsinTermC(varName) {
  const x = EML.var(varName);
  const ix = mkMulC(iTermC, x);
  const root = sqrtOneSubSqC(varName);
  return mkLogC(mkAddC(ix, root));
}

// arccosTermℂ = mkLogℂ (mkAddℂ x (mkMulℂ i (sqrt(1 − x²))))
// (eval).im = Real.arccos x for x ∈ (−1, 1)
function arccosTermC(varName) {
  const x = EML.var(varName);
  const root = sqrtOneSubSqC(varName);
  return mkLogC(mkAddC(x, mkMulC(iTermC, root)));
}

// Trig witness table. Each entry: (term_builder, projection, domain note).
const TRIG_WITNESSES = {
  cos: {
    build: cosTermC, proj: '.re',
    note: 'sealed on ℝ ∖ {0}; full natural domain (paper-compatible)'
  },
  sin: {
    build: sinTermC, proj: '.re',
    note: 'sealed on ℝ ∖ {π/2}; via Path C′ identity sin x = cos(π/2 − x)'
  },
  tan: {
    build: tanCoreTermC, proj: '.im',
    note: 'sealed on (-π/2, π/2) ∖ {0}; period-π reduction extends to ' +
          '{x : cos x ≠ 0} (Path C′)'
  },
  arctan: {
    build: arctanTermC, proj: '.im',
    note: 'sealed on (-π, π) ∖ {0}; full real domain via arctan = arcsin(x/√(1+x²)) (Path C′)'
  },
  arcsin: {
    build: arcsinTermC, proj: '.im',
    note: 'sealed on full open (−1, 1)'
  },
  arccos: {
    build: arccosTermC, proj: '.im',
    note: 'sealed on full open (−1, 1)'
  },
};

const TRIG_NAMES = Object.keys(TRIG_WITNESSES);

// ---------------------------------------------------------------------
// Parser — recursive descent for a small math expression grammar
// ---------------------------------------------------------------------

class Tokenizer {
  constructor(input) {
    this.input = input;
    this.pos = 0;
  }
  peek() {
    this.skipWhitespace();
    if (this.pos >= this.input.length) return { type: 'eof' };
    const ch = this.input[this.pos];
    if (/[0-9]/.test(ch)) return this.scanNumber();
    if (/[a-zA-Z_]/.test(ch)) return this.scanIdent();
    if ('+-*/^(),'.includes(ch)) return { type: 'op', value: ch };
    if (ch === '·') return { type: 'op', value: '*' };
    if (ch === '−') return { type: 'op', value: '-' };
    if (ch === '×') return { type: 'op', value: '*' };
    if (ch === '÷') return { type: 'op', value: '/' };
    throw new Error(`Unexpected character '${ch}' at position ${this.pos}`);
  }
  next() {
    const t = this.peek();
    if (t.type !== 'eof') this.pos += t.length || 1;
    return t;
  }
  skipWhitespace() {
    while (this.pos < this.input.length && /\s/.test(this.input[this.pos]))
      this.pos++;
  }
  scanNumber() {
    let start = this.pos;
    while (this.pos < this.input.length &&
           /[0-9.]/.test(this.input[this.pos]))
      this.pos++;
    const text = this.input.slice(start, this.pos);
    const len = text.length;
    this.pos = start; // rewind; next() will advance by len
    return { type: 'num', value: parseFloat(text), length: len };
  }
  scanIdent() {
    let start = this.pos;
    while (this.pos < this.input.length &&
           /[a-zA-Z_0-9]/.test(this.input[this.pos]))
      this.pos++;
    const text = this.input.slice(start, this.pos);
    const len = text.length;
    this.pos = start;
    return { type: 'ident', value: text, length: len };
  }
}

class Parser {
  constructor(input) {
    this.tok = new Tokenizer(input);
  }
  parse() {
    const e = this.expr();
    const t = this.tok.peek();
    if (t.type !== 'eof')
      throw new Error(`Unexpected trailing input at position ${this.tok.pos}`);
    return e;
  }
  // expr := term (('+' | '-') term)*
  expr() {
    let lhs = this.term();
    while (true) {
      const t = this.tok.peek();
      if (t.type === 'op' && (t.value === '+' || t.value === '-')) {
        this.tok.next();
        const rhs = this.term();
        lhs = { type: t.value === '+' ? 'add' : 'sub', left: lhs, right: rhs };
      } else break;
    }
    return lhs;
  }
  // term := factor (('*' | '/') factor)*
  term() {
    let lhs = this.factor();
    while (true) {
      const t = this.tok.peek();
      if (t.type === 'op' && (t.value === '*' || t.value === '/')) {
        this.tok.next();
        const rhs = this.factor();
        lhs = { type: t.value === '*' ? 'mul' : 'div', left: lhs, right: rhs };
      } else break;
    }
    return lhs;
  }
  // factor := unary ('^' factor)?
  factor() {
    const lhs = this.unary();
    const t = this.tok.peek();
    if (t.type === 'op' && t.value === '^') {
      this.tok.next();
      const rhs = this.factor(); // right-associative
      return { type: 'pow', left: lhs, right: rhs };
    }
    return lhs;
  }
  // unary := '-' unary | primary
  unary() {
    const t = this.tok.peek();
    if (t.type === 'op' && t.value === '-') {
      this.tok.next();
      return { type: 'neg', arg: this.unary() };
    }
    return this.primary();
  }
  // primary := number | ident | ident '(' args ')' | '(' expr ')'
  primary() {
    const t = this.tok.next();
    if (t.type === 'num') return { type: 'num', value: t.value };
    if (t.type === 'ident') {
      const after = this.tok.peek();
      if (after.type === 'op' && after.value === '(') {
        this.tok.next();
        const args = this.argList();
        const close = this.tok.next();
        if (close.type !== 'op' || close.value !== ')')
          throw new Error('Expected closing parenthesis');
        return { type: 'call', name: t.value, args };
      }
      return { type: 'name', name: t.value };
    }
    if (t.type === 'op' && t.value === '(') {
      const e = this.expr();
      const close = this.tok.next();
      if (close.type !== 'op' || close.value !== ')')
        throw new Error('Expected closing parenthesis');
      return e;
    }
    throw new Error(`Unexpected token ${JSON.stringify(t)} at position ${this.tok.pos}`);
  }
  argList() {
    const t = this.tok.peek();
    if (t.type === 'op' && t.value === ')') return [];
    const args = [this.expr()];
    while (true) {
      const c = this.tok.peek();
      if (c.type === 'op' && c.value === ',') {
        this.tok.next();
        args.push(this.expr());
      } else break;
    }
    return args;
  }
}

// ---------------------------------------------------------------------
// AST → EMLTerm compiler
// ---------------------------------------------------------------------

const UNARY = {
  exp: mkExp, log: mkLog, ln: mkLog, neg: mkNeg, inv: mkInv,
  sq: mkSq, sqrt: mkSqrt, halve: mkHalve, sigma: mkSigma, sigmoid: mkSigma,
  sinh: mkSinh, cosh: mkCosh, tanh: mkTanh,
  arsinh: mkArsinh, arcosh: mkArcosh, artanh: mkArtanh,
  // aliases for hyperbolic
  asinh: mkArsinh, acosh: mkArcosh, atanh: mkArtanh,
};

const BINARY = {
  hypot: mkHypot, pow: mkPow, logb: mkLogB, log_b: mkLogB,
  avg: mkAvg, mean: mkAvg,
};

const NAMED_CONST = {
  e: mkE, pi: mkPi, π: mkPi, one: () => EML.one(),
  zero: mkZero, two: mkTwo, half: mkHalf, half_const: mkHalf,
  negOne: mkNegOne, neg_one: mkNegOne,
};

function compile(ast) {
  switch (ast.type) {
    case 'num': {
      const n = ast.value;
      if (n === 0) return mkZero();
      if (n === 1) return EML.one();
      if (n === 2) return mkTwo();
      if (n === 0.5) return mkHalf();
      if (Number.isInteger(n) && n > 0) return mkConstNat(n);
      if (Number.isInteger(n) && n < 0) return mkNeg(mkConstNat(-n));
      throw new Error(`Numeric literal ${n} not directly representable; ` +
                       `use named constants (1, 2, 0, π, e) or arithmetic`);
    }
    case 'name': {
      if (NAMED_CONST[ast.name]) return NAMED_CONST[ast.name]();
      // single letter / identifier → variable
      return EML.var(ast.name);
    }
    case 'call': {
      const name = ast.name.toLowerCase();
      if (TRIG_WITNESSES[name]) {
        if (ast.args.length !== 1)
          throw new Error(`${name} expects 1 argument, got ${ast.args.length}`);
        // Trig witnesses are top-level only (the substitution into a
        // surrounding compile would mix complex-grammar witnesses with
        // structural-compiler output in a way the tool doesn't model).
        const arg = ast.args[0];
        if (arg.type !== 'name') {
          throw new Error(
            `${name} witness requires a single variable as argument ` +
            `(e.g. ${name}(x)); got a compound expression. The complex ` +
            `EMLTermℂ witnesses are top-level constructions in the formal ` +
            `artefact too — composition with the real-fragment compiler ` +
            `would happen via Path C′ subst0, which this tool doesn't yet model.`);
        }
        const w = TRIG_WITNESSES[name];
        const tree = w.build(arg.name);
        tree.__trigProjection = w.proj;
        tree.__trigName = name;
        tree.__trigNote = w.note;
        tree.__trigVar = arg.name;
        return tree;
      }
      if (UNARY[name]) {
        if (ast.args.length !== 1)
          throw new Error(`${name} expects 1 argument, got ${ast.args.length}`);
        return UNARY[name](compile(ast.args[0]));
      }
      if (BINARY[name]) {
        if (ast.args.length !== 2)
          throw new Error(`${name} expects 2 arguments, got ${ast.args.length}`);
        return BINARY[name](compile(ast.args[0]), compile(ast.args[1]));
      }
      throw new Error(`Unknown function: ${ast.name}`);
    }
    case 'add': return mkAdd(compile(ast.left), compile(ast.right));
    case 'sub': return mkSub(compile(ast.left), compile(ast.right));
    case 'mul': return mkMul(compile(ast.left), compile(ast.right));
    case 'div': return mkDiv(compile(ast.left), compile(ast.right));
    case 'pow': {
      // x^n for integer n → repeated mul; otherwise general power
      const exp = ast.right;
      if (exp.type === 'num' && Number.isInteger(exp.value) && exp.value >= 1
          && exp.value <= 8) {
        const base = compile(ast.left);
        let acc = base;
        for (let i = 1; i < exp.value; i++) acc = mkMul(acc, base);
        return acc;
      }
      return mkPow(compile(ast.left), compile(ast.right));
    }
    case 'neg': return mkNeg(compile(ast.arg));
    default: throw new Error(`Unknown AST node: ${ast.type}`);
  }
}

class TrigError extends Error {
  constructor(name) {
    super(`Trigonometric primitive '${name}' requires the complex EML grammar (EMLTermℂ). `
        + `In the formal artefact, ${name} is sealed via Euler-bridge witnesses (see `
        + `EML.Framework.Complex.Closures.Trig in the Lean repository). `
        + `This browser tool currently shows the real-fragment compile only.`);
    this.name = 'TrigError';
  }
}

// ---------------------------------------------------------------------
// Sub-expression labelling — what does each node compute?
// ---------------------------------------------------------------------

// Reverse-engineer a high-level label for an EML sub-tree by recognising
// the macro-expansion patterns produced by the compiler above.

function describe(t) {
  if (t.kind === 'one') return '1';
  if (t.kind === 'var') return t.name;
  if (t.kind === 'realize') return `⟨${t.name} : K=${t.k}⟩`;
  // eml(a, 1) = exp(a)
  if (t.b.kind === 'one') return `exp(${describe(t.a)})`;
  // eml(1, eml(eml(1, z), 1)) = log(z)
  if (t.a.kind === 'one' && t.b.kind === 'eml' && t.b.b.kind === 'one' &&
      t.b.a.kind === 'eml' && t.b.a.a.kind === 'one') {
    return `log(${describe(t.b.a.b)})`;
  }
  // Generic case
  return `eml(${describe(t.a)}, ${describe(t.b)})`;
}

// ---------------------------------------------------------------------
// SVG tree renderer
// ---------------------------------------------------------------------

const NODE_R = 14;
const H_GAP = 24;  // horizontal spacing between sibling subtrees
const V_GAP = 60;  // vertical spacing between layers
const PADDING = 30;

// Compute layout: returns [width, height, positionedTree].
// Each node gets x, y coordinates relative to top-left.
function layout(t) {
  // Reingold–Tilford-ish: leaves are at fixed width; internal node x is
  // centroid of children.
  function go(node, depth) {
    if (node.kind === 'one' || node.kind === 'var') {
      return { ...node, x: 0, width: NODE_R * 2 + H_GAP, depth };
    }
    if (node.kind === 'realize') {
      // realize nodes render as wider leaves (label like "iℂ K=407")
      return { ...node, x: 0, width: NODE_R * 4 + H_GAP, depth };
    }
    const aL = go(node.a, depth + 1);
    const bL = go(node.b, depth + 1);
    // shift bL to the right by aL.width
    function shift(n, dx) {
      n.x += dx;
      if (n.kind === 'eml') { shift(n.a, dx); shift(n.b, dx); }
    }
    shift(bL, aL.width);
    const x = (aL.x + bL.x) / 2;
    return {
      ...node,
      a: aL, b: bL,
      x,
      width: aL.width + bL.width,
      depth,
    };
  }
  const positioned = go(t, 0);
  // Set y based on depth
  function setY(n) {
    n.y = PADDING + n.depth * V_GAP;
    if (n.kind === 'eml') { setY(n.a); setY(n.b); }
  }
  setY(positioned);
  // Translate so leftmost x is at PADDING
  function minX(n) {
    if (n.kind === 'one' || n.kind === 'var' || n.kind === 'realize')
      return n.x;
    return Math.min(n.x, minX(n.a), minX(n.b));
  }
  const dx = PADDING + NODE_R - minX(positioned);
  function shift(n, d) {
    n.x += d;
    if (n.kind === 'eml') { shift(n.a, d); shift(n.b, d); }
  }
  shift(positioned, dx);
  function maxX(n) {
    if (n.kind === 'one' || n.kind === 'var' || n.kind === 'realize')
      return n.x;
    return Math.max(n.x, maxX(n.a), maxX(n.b));
  }
  const width = maxX(positioned) + PADDING + NODE_R;
  const height = PADDING * 2 + (depth(t) + 1) * V_GAP;
  return { positioned, width, height };
}

function renderTree(t, container) {
  container.innerHTML = '';
  const { positioned, width, height } = layout(t);
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.id = 'tree-svg';
  svg.setAttribute('width', width);
  svg.setAttribute('height', height);
  svg.setAttribute('viewBox', `0 0 ${width} ${height}`);

  // Edges first (so nodes draw on top)
  function drawEdges(n) {
    if (n.kind !== 'eml') return;
    for (const child of [n.a, n.b]) {
      const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      const x1 = n.x, y1 = n.y, x2 = child.x, y2 = child.y;
      const cy = (y1 + y2) / 2;
      path.setAttribute('d', `M ${x1} ${y1} C ${x1} ${cy}, ${x2} ${cy}, ${x2} ${y2}`);
      path.setAttribute('class', 'edge');
      svg.appendChild(path);
      drawEdges(child);
    }
  }
  drawEdges(positioned);

  // Nodes
  const tooltip = makeTooltip();
  function drawNode(n) {
    const circle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
    circle.setAttribute('cx', n.x);
    circle.setAttribute('cy', n.y);
    circle.setAttribute('r', NODE_R);
    if (n.kind === 'eml') {
      circle.setAttribute('class', 'node-eml');
      circle.addEventListener('mouseenter', () => {
        tooltip.textContent = describe(n);
        tooltip.style.display = 'block';
      });
      circle.addEventListener('mousemove', (e) => {
        tooltip.style.left = (e.pageX + 10) + 'px';
        tooltip.style.top = (e.pageY + 10) + 'px';
      });
      circle.addEventListener('mouseleave', () => {
        tooltip.style.display = 'none';
      });
    } else if (n.kind === 'one') {
      circle.setAttribute('class', 'node-one');
    } else if (n.kind === 'realize') {
      circle.setAttribute('class', 'node-realize');
      circle.setAttribute('r', NODE_R + 4);
      circle.addEventListener('mouseenter', () => {
        tooltip.textContent = `Closed-constant witness ⟨${n.name}⟩ (K=${n.k}); ` +
                              `internal structure hidden — see EMLRealizationℂ in the Lean repo.`;
        tooltip.style.display = 'block';
      });
      circle.addEventListener('mousemove', (e) => {
        tooltip.style.left = (e.pageX + 10) + 'px';
        tooltip.style.top = (e.pageY + 10) + 'px';
      });
      circle.addEventListener('mouseleave', () => {
        tooltip.style.display = 'none';
      });
    } else {
      circle.setAttribute('class', 'node-var');
    }
    svg.appendChild(circle);

    const label = document.createElementNS('http://www.w3.org/2000/svg', 'text');
    label.setAttribute('x', n.x);
    label.setAttribute('y', n.y + 4);
    label.setAttribute('class', 'node-label');
    if (n.kind === 'eml') label.textContent = 'E';
    else if (n.kind === 'one') label.textContent = '1';
    else if (n.kind === 'realize') label.textContent = n.name;
    else label.textContent = n.name;
    svg.appendChild(label);

    if (n.kind === 'eml') { drawNode(n.a); drawNode(n.b); }
  }
  drawNode(positioned);

  container.appendChild(svg);
}

function makeTooltip() {
  let t = document.querySelector('.tooltip');
  if (!t) {
    t = document.createElement('div');
    t.className = 'tooltip';
    t.style.display = 'none';
    document.body.appendChild(t);
  }
  return t;
}

// ---------------------------------------------------------------------
// Main: wire up UI
// ---------------------------------------------------------------------

function compileAndRender(input) {
  const errEl = document.getElementById('error');
  const projEl = document.getElementById('projection');
  errEl.hidden = true;
  errEl.textContent = '';
  if (projEl) projEl.hidden = true;
  try {
    const ast = new Parser(input).parse();
    const tree = compile(ast);
    document.getElementById('k-count').textContent = rpnLength(tree);
    document.getElementById('depth').textContent = depth(tree);
    document.getElementById('leaves').textContent = leafCount(tree);
    document.getElementById('eml-count').textContent = emlCount(tree);
    document.getElementById('rpn-output').textContent = rpnString(tree);
    if (tree.__trigProjection && projEl) {
      projEl.hidden = false;
      projEl.innerHTML =
        `<strong>${tree.__trigName}(${tree.__trigVar}) = ` +
        `(witness.eval ${tree.__trigProjection})</strong>` +
        ` &mdash; ${tree.__trigNote}`;
    }
    renderTree(tree, document.getElementById('tree-container'));
  } catch (err) {
    errEl.hidden = false;
    errEl.textContent = err.message;
    document.getElementById('k-count').textContent = '—';
    document.getElementById('depth').textContent = '—';
    document.getElementById('leaves').textContent = '—';
    document.getElementById('eml-count').textContent = '—';
    document.getElementById('rpn-output').textContent = '—';
    document.getElementById('tree-container').innerHTML = '';
  }
}

document.getElementById('compile').addEventListener('click', () => {
  compileAndRender(document.getElementById('expr').value);
});

document.getElementById('expr').addEventListener('keydown', (e) => {
  if (e.key === 'Enter') {
    compileAndRender(document.getElementById('expr').value);
  }
});

document.querySelectorAll('button.ex').forEach((btn) => {
  btn.addEventListener('click', () => {
    document.getElementById('expr').value = btn.dataset.expr;
    compileAndRender(btn.dataset.expr);
  });
});

// Auto-compile the default on load
compileAndRender(document.getElementById('expr').value);
