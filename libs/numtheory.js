MathVizLibrary(function numtheory(MathViz) {
  const whole = (n, fn) => {
    if (!Number.isInteger(n)) throw MathViz.error(`${fn} expects whole numbers, got ${MathViz.format(n)}.`);
    return n;
  };
  const isprime = n => {
    if (!Number.isInteger(n) || n < 2) return false;
    if (n % 2 === 0) return n === 2;
    for (let d = 3; d * d <= n; d += 2) if (n % d === 0) return false;
    return true;
  };
  const gcd = (a, b) => {
    a = Math.abs(whole(a, 'gcd')); b = Math.abs(whole(b, 'gcd'));
    while (b) [a, b] = [b, a % b];
    return a;
  };
  // Modular power with BigInt, so large exponents don't lose precision.
  const powmod = (a, k, m) => {
    whole(a, 'powmod'); whole(k, 'powmod'); whole(m, 'powmod');
    if (k < 0) throw MathViz.error('powmod needs an exponent ≥ 0.');
    const M = BigInt(m);
    let r = 1n, b = ((BigInt(a) % M) + M) % M, e = BigInt(k);
    while (e > 0n) { if (e & 1n) r = r * b % M; b = b * b % M; e >>= 1n; }
    return Number(r % M);
  };
  const phi = n => {
    whole(n, 'phi');
    let r = n;
    for (let p = 2; p * p <= n; p++) if (n % p === 0) { while (n % p === 0) n /= p; r -= r / p; }
    if (n > 1) r -= r / n;
    return r;
  };
  const primesBetween = (a, b) => {
    const out = [];
    for (let n = Math.max(2, Math.ceil(a)); n <= b; n++) if (isprime(n)) out.push(n);
    return out;
  };

  /* ---------- ways of writing a number (interpret) ---------- */
  const isNum = v => typeof v === 'number' || !!(v && v.__exact);
  const isWhole = v => isNum(v) && Number.isInteger(+v) && Math.abs(+v) >= 1 && Math.abs(+v) <= 1e15;
  const factor = n => {
    const out = [];
    for (let p = 2; p * p <= n; p++) { let k = 0; while (n % p === 0) { n /= p; k++; } if (k) out.push([p, k]); }
    if (n > 1) out.push([n, 1]);
    return out;
  };
  const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
  const sup = k => String(k).split('').map(c => SUP[c]).join('');
  const roman = n => { let s = ''; for (const [v, r] of [[1000, 'M'], [900, 'CM'], [500, 'D'], [400, 'CD'], [100, 'C'], [90, 'XC'], [50, 'L'], [40, 'XL'], [10, 'X'], [9, 'IX'], [5, 'V'], [4, 'IV'], [1, 'I']]) while (n >= v) { s += r; n -= v; } return s; };
  MathViz.represent({
    name: 'factorization', label: 'A product of primes', test: isWhole,
    doc: 'Every whole number ≥ 2 is a product of primes in exactly one way (the fundamental theorem of arithmetic); its divisors are the products of parts of it.',
    render(ctx, v) {
      const n = Math.abs(+v);
      if (n === 1) { ctx.note('1 is the empty product: it has no prime factors, and its only divisor is 1.'); return; }
      const f = factor(n), divs = [];
      for (let d = 1; d * d <= n; d++) if (n % d === 0) { divs.push(d); if (d * d !== n) divs.push(n / d); }
      divs.sort((a, b) => a - b);
      ctx.html(`<p class="big-formula">${+v < 0 ? '−' : ''}${n} = ${f.map(([p, k]) => p + (k > 1 ? sup(k) : '')).join(' · ')}</p>`);
      ctx.note(`${isprime(n) ? `${n} is prime.` : `${divs.length} divisors${divs.length <= 40 ? ': ' + divs.join(', ') : ''}.`} Their number is ${f.map(([, k]) => `(${k} + 1)`).join('·')} = ${divs.length}; φ(${n}) = ${phi(n)} numbers below ${n} are coprime to it.`);
      if (f.length <= 3 && divs.length <= 36 && f.length >= 1) {
        // The divisors as a grid by exponents: a lattice ordered by divisibility.
        const [p, kp] = f[0], [q, kq] = f[1] || [1, 0];
        const fig = ctx.figure({ x: [-0.4, kp + 0.8], y: [-0.4, kq + 0.6], height: 170, xAxis: false, yAxis: false, static: true });
        for (let i = 0; i <= kp; i++) for (let j = 0; j <= kq; j++) {
          if (i < kp) fig.seg(i, j, i + 1, j, { color: 'faint' });
          if (j < kq) fig.seg(i, j, i, j + 1, { color: 'faint' });
        }
        for (let i = 0; i <= kp; i++) for (let j = 0; j <= kq; j++) { fig.points([[i, j]], { color: 'c1', r: 3.5 }); fig.text(i, j, String(p ** i * q ** j), { color: 'ink', align: 'left', dx: 6, dy: -9 }); }
        ctx.note(`The divisors arranged by the powers of ${p}${f[1] ? ` and ${q}` : ''}${f.length > 2 ? ` (times powers of ${f.slice(2).map(x => x[0]).join(', ')})` : ''}: each step multiplies by a prime.`);
      }
    },
  });
  MathViz.represent({
    name: 'bases', label: 'In other bases, and its remainders', test: isWhole,
    doc: 'The same number written with other digits: n = Σ dₖ bᵏ. And what it leaves when divided by small numbers.',
    render(ctx, v) {
      const n = Math.round(+v), a = Math.abs(n), sg = n < 0 ? '−' : '';
      const rows = [[2, 'binary'], [3, 'ternary'], [8, 'octal'], [10, 'decimal'], [16, 'hexadecimal']].map(([b, name]) => [`base ${b} (${name})`, sg + a.toString(b).toUpperCase()]);
      if (a >= 1 && a < 4000) rows.push(['Roman numerals', sg + roman(a)]);
      ctx.table(['', 'written'], rows);
      ctx.table(['m', ...Array.from({ length: 11 }, (_, i) => String(i + 2))], [['n mod m', ...Array.from({ length: 11 }, (_, i) => String(((n % (i + 2)) + i + 2) % (i + 2)))]]);
    },
  });
  // Continued fraction digits of x and the convergents p/q.
  const contfrac = (x, k = 14) => {
    const a = [], conv = [];
    let p0 = 1, q0 = 0, p1 = Math.floor(x), q1 = 1, y = x;
    for (let i = 0; i < k; i++) {
      const ai = Math.floor(y);
      a.push(ai);
      if (i === 0) { p1 = ai; q1 = 1; } else { [p0, p1] = [p1, ai * p1 + p0]; [q0, q1] = [q1, ai * q1 + q0]; }
      conv.push([p1, q1]);
      const r = y - ai;
      if (Math.abs(r) < 1e-12 || !Number.isFinite(1 / r) || q1 > 1e12) break;
      y = 1 / r;
    }
    return { a, conv };
  };
  MathViz.represent({
    name: 'continued_fraction', label: 'A continued fraction', test: v => isNum(v) && Number.isFinite(+v) && !Number.isInteger(+v),
    doc: 'x = a₀ + 1/(a₁ + 1/(a₂ + …)). Cutting it off gives the convergents p/q, the best approximations with denominators that small. Rationals stop; quadratic irrationals repeat; e and π don\'t.',
    render(ctx, v) {
      const x = +v, { a, conv } = contfrac(x);
      ctx.html(`<p class="big-formula">${MathViz.format(v)} = [${a[0]}; ${a.slice(1).join(', ')}${conv.length >= 14 ? ', …' : ''}]</p>`);
      ctx.table(['n', 'aₙ', 'convergent pₙ/qₙ', 'error'], conv.map(([p, q], i) => [String(i), String(a[i]), `${p}/${q}`, MathViz.format(+Math.abs(x - p / q).toPrecision(2))]));
      const errs = conv.map(([p, q], i) => [i, Math.log10(Math.max(1e-17, Math.abs(x - p / q)))]);
      const fig = ctx.figure({ height: 160, xlabel: 'n', ylabel: 'log₁₀ error' });
      fig.curve(errs, { color: 'c1', width: 1.5 });
      fig.points(errs, { color: 'c1', r: 3 });
      ctx.note('Each convergent is closer than any fraction with a smaller denominator, and |x − p/q| < 1/q².');
    },
  });
  MathViz.represent({
    name: 'expansions', label: 'Decimal and binary expansions', test: v => isNum(v) && Number.isFinite(+v) && !Number.isInteger(+v),
    doc: 'The digits of x in base 10 and base 2: a number is rational exactly when its expansion eventually repeats.',
    render(ctx, v) {
      const x = +v, sg = x < 0 ? '−' : '', y = Math.abs(x), ip = Math.floor(y);
      const digits = (b, k) => { let f = y - ip, s = ''; for (let i = 0; i < k; i++) { f *= b; const d = Math.floor(f + 1e-12); s += d.toString(b); f -= d; if (f < 1e-13) break; } return s; };
      const rows = [['decimal', `${sg}${ip}.${digits(10, 15)}`], ['binary', `${sg}${ip.toString(2)}.${digits(2, 48)}`]];
      if (v && v.__exact) rows.unshift(['exact', MathViz.format(v)]);
      ctx.table(['', 'expansion'], rows);
      ctx.note('Only about 16 significant decimal digits are known here (double precision), so a long period can\'t be seen.');
    },
  });

  MathViz.define({
    name: 'numtheory',
    description: 'Whole-number functions (gcd, isprime, powmod, phi and more), the range Primes[a, b], the Ulam spiral view, primes and coprime pairs each defined several ways, and every way of writing a whole number (interpret n).',
    notation: `
# n is prime, four ways: it has exactly two divisors; no number from 2 to √n divides it; Wilson's theorem, (n − 1)! ≡ −1 (mod n); and the built-in test.
# examples: n in 1..18
concept prime(n: Z) where
  two_divisors: len({d in 1..n | n mod d = 0}) = 2
  no_small_divisor: n >= 2 and forall d in 2..floor(sqrt(n)): n mod d != 0
  wilson: n >= 2 and (n - 1)! mod n = n - 1
  builtin: isprime(n)

# a and b are coprime, three ways: gcd(a, b) = 1; 1 is an integer combination ax + by (Bézout); no d ≥ 2 divides both.
# examples: a in 1..10, b in 1..10
concept coprime(a: Z, b: Z) where
  gcd_one: gcd(a, b) = 1
  bezout: exists x in -10..10, y in -10..10: a*x + b*y = 1
  no_common_divisor: forall d in 2..10: not (a mod d = 0 and b mod d = 0)
`,
    functions: {
      isprime, gcd, powmod, phi,
      lcm: (a, b) => Math.abs(a * b) / gcd(a, b),
      divides: (a, b) => whole(b, 'divides') % whole(a, 'divides') === 0,
      binom: (n, k) => {
        whole(n, 'binom'); whole(k, 'binom');
        if (k < 0 || k > n) return 0;
        let r = 1;
        for (let i = 1; i <= Math.min(k, n - k); i++) r = r * (n - i + 1) / i;
        return Math.round(r);
      },
      fib: n => {
        whole(n, 'fib');
        let a = 0, b = 1;
        for (let i = 0; i < n; i++) [a, b] = [b, a + b];
        return a;
      },
      sigma: n => {
        whole(n, 'sigma');
        let s = 0;
        for (let d = 1; d * d <= n; d++) if (n % d === 0) s += d + (d * d === n ? 0 : n / d);
        return s;
      },
    },
    domains: {
      Primes: (a = 2, b = 1000) => MathViz.finite(primesBetween(a, b), { label: `primes in [${a}, ${b}]` }),
    },
    views: {
      ulam: {
        doc: 'ulam(size, p) writes 1, 2, 3, … in a square spiral and marks the numbers where p holds (default: isprime).',
        render(ctx, size = 61, pred = isprime) {
          size = ctx.param('size', { min: 11, max: 201, step: 2, value: size % 2 ? size : size + 1 });
          const n = size, grid = new Array(n * n).fill(0);
          let x = (n - 1) / 2, y = x, k = 1, step = 1, dir = 0;
          const dx = [1, 0, -1, 0], dy = [0, -1, 0, 1];
          grid[y * n + x] = 1;
          while (k < n * n) {
            for (let leg = 0; leg < 2 && k < n * n; leg++) {
              for (let s = 0; s < step && k < n * n; s++) {
                x += dx[dir]; y += dy[dir]; k++;
                if (x >= 0 && x < n && y >= 0 && y < n) grid[y * n + x] = k;
              }
              dir = (dir + 1) % 4;
            }
            step++;
          }
          const fig = ctx.figure({ x: [0, n], y: [0, n], square: true, xAxis: false, yAxis: false });
          let hits = 0;
          fig.raster({
            x: [0, n], y: [0, n], nx: n, ny: n, smooth: false,
            value: (px, py) => {
              const v = grid[Math.floor(n - py) * n + Math.floor(px)];
              const on = v > 0 && pred(v) === true;
              if (on) hits++;
              return on;
            },
            color: (on, theme) => on ? [...theme.rgb('ink'), 235] : null,
          });
          ctx.note(`${hits} of the numbers 1 to ${n * n} are marked. Diagonal streaks come from quadratic polynomials that produce many primes.`);
        },
      },
    },
  });
});
