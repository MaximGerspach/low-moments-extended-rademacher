# Low moments of extended Rademacher sums — Lean 4 formalisation

This repository contains a Lean 4 formalisation of all results of the paper

> Christopher Atherfold, Maxim Gerspach and Jad Hamdan,
> *Low moments of sums of extended Rademacher random multiplicative functions*,

together with the results the paper depends on: Harper's theorems on low moments of random
multiplicative functions (Steinhaus and Rademacher, uniformly in $q$) and the upper bound in Caich's
theorem on short intervals (Rademacher case).

**AI disclosure.** The Lean code in this repository was written by Claude (Anthropic) under the
direction of the authors; see the appendix "Formalisation in Lean 4" of the paper.  Lean's kernel
checks every proof, and the axiom check below confirms that no result depends on anything beyond
the standard axioms.

## Main results

[`RMF/Paper.lean`](RMF/Paper.lean) states every result of the paper in Lean, in the paper's order
and without explicit constants, each proved by the library theorem that establishes it.

Let $X^e$ be the completely multiplicative function whose values at the primes are independent and
uniform on $\{\pm1\}$, $X = \mu^2 X^e$, and $\Lambda = \log\log x$.

| Paper | Statement | Lean (`RMF.Paper.…`) |
|---|---|---|
| Theorem 1.1 | $\mathbb E\big\lvert x^{-1/2}\sum_{n\le x}X^e(n)\big\rvert^{2q} \asymp \Lambda^{-q/2}$, $\Lambda^{3/4}$, $(\log x)^{q(2q-1)}$ for $0\le q<\tfrac12$, $q=\tfrac12$, $\tfrac12<q\le1$ (fixed $q$, $x\ge3$) | `theorem_1_1` |
| Theorem 1.2 | the same for $\sum_{n\le x}X(n)/\sqrt n$ | `theorem_1_2` |
| (1.3) | the bound uniform in $q$, with the matching lower bound | `bound_1_3_extended` |
| (1.3), weighted | the same for $\sum_{n\le x}X(n)/\sqrt n$ | `bound_1_3_weighted` |
| Corollary 1.3 | $\mathbb P\big(\lvert\cdot\rvert > \lambda\Lambda^{-1/4}\big) \ll \min\{\log\lambda,\Lambda\}/\lambda$, for every $x\ge3$ and $\lambda\ge3$ | `corollary_1_3_extended`, `corollary_1_3_weighted` |
| Corollary 1.4 | the non-square parts tend to $-1$ in probability | `corollary_1_4_extended`, `corollary_1_4_weighted` |
| Proposition 1.5 | $\mathbb E\big\lvert\sum_{n\le x}X^e(n)/\sqrt n\big\rvert^{2q}\ll(\log x)^{q(2q+1)}$ for fixed $q\in[0,\tfrac12]$, $x\ge3$; the non-square part divided by $\log x$ tends to $-\tfrac12$ in probability | `proposition_1_5_moments`, `proposition_1_5_limit` |
| Harper, Thm 1 | $\mathbb E\lvert x^{-1/2}\sum_{n\le x}f(n)\rvert^{2q}\asymp(1+(1-q)\sqrt{\log\log x})^{-q}$, Steinhaus, uniformly in $q\in[0,1]$ | `harper_theorem_1` |
| Harper, Thm 2 | the same for Rademacher | `harper_theorem_2` |
| Caich, Thm 1.1 | the upper bound on short intervals, Rademacher | `caich_theorem_1_1` |

## Explicit constants

[`RMF/PaperExplicit.lean`](RMF/PaperExplicit.lean) gives the versions with explicit constants, all
valid for every $x \ge 3$:

| Result | Explicit form | Lean (`RMF.Paper.…`) |
|---|---|---|
| (1.3) | $10^{-10}\,T(q,x) \le \mathbb E\lvert x^{-1/2}\sum_{n\le x}X^e(n)\rvert^{2q} \le 30\,T(q,x)$ | `bound_1_3_extended_explicit` |
| (1.3), weighted | the same for $\sum_{n\le x}X(n)/\sqrt n$, with $25$ in place of $30$ | `bound_1_3_weighted_explicit` |
| Corollary 1.3 | $\le 30e\cdot\min\{\log\lambda,\Lambda\}/\lambda$, respectively $25e\cdot\min\{\log\lambda,\Lambda\}/\lambda$ | `corollary_1_3_extended_explicit`, `corollary_1_3_weighted_explicit` |
| Harper, Thm 1 | the upper bound with constant $20$, Steinhaus, every $x \ge 1$ | `harper_theorem_1_upper_explicit` |

Here $T(q,x) = \min\{\Lambda,(1-2q)^{-1}\}\,\Lambda^{-q/2}$ for $0<q<\tfrac12$, $\Lambda^{3/4}$ for
$q=\tfrac12$, and $(\log x)^{q(2q-1)}\min\{(2q-1)^{-1},\Lambda\}^{3/4}$ for $\tfrac12<q\le1$.

## Checking

Every result above depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; the repository contains no `sorry`.  To check, with
[elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get
lake build
```

`lake build` builds the library and the two files above, and checks the axioms of each result
(`RMF/PaperAxioms.lean`: the build fails if any of them depends on anything beyond the three
standard axioms).  The library contains only what the proofs of these results use.

A first build downloads Mathlib's compiled cache and then compiles about a thousand modules: the
parts of PrimeNumberTheoremAnd that are used, LeanCert, and this library.  This takes several
hours.  Lake runs one compile per processor core, so a machine with many cores needs
correspondingly much memory.  Measured on Windows, a compile needs at most about 6 GB of resident
and 11 GB of committed memory; Linux, where compiles share their imports, needs less.  An
interrupted build resumes where it stopped.

## Dependencies

* [Mathlib](https://github.com/leanprover-community/mathlib4), Lean `v4.32.2`.
* [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (PNT+), pinned
  to commit `7715064`, for sieve estimates and the prime number theorem.  Some of its files contain
  `sorry`s; none of them is used, as the axiom checks show.
* [`RMF/PNTPlus/MediumPNTExplicit.lean`](RMF/PNTPlus/MediumPNTExplicit.lean): an explicit-constant
  version of PNT+'s `MediumPNT`, adapted from PNT+ (Apache 2.0) and included here.

## Layout

| Path | Contents |
|---|---|
| `RMF/Paper.lean`, `RMF/PaperExplicit.lean` | the paper's results, as stated in the paper; their explicit versions |
| `RMF/Harper.lean`, `RMF/HarperRademacher.lean` | Harper's theorems |
| `RMF/RademacherMoments.lean` | Theorems 1.1 and 1.2 |
| `RMF/Weighted/`, `RMF/WeightedExtendedMoments.lean` | weighted and extended sums: reductions, upper bounds, Caich's theorem, the corollaries, Proposition 1.5 |
| `RMF/UniformLower/` | the lower bounds uniform in $q$, with explicit constants |
| `RMF/NumberTheory/` | explicit prime number theory (zero-free region, Chebyshev's $\theta$) |
| `RMF/Probability/`, `RMF/EulerProduct/`, `RMF/Reduction/`, `RMF/Analysis/` | Harper's method: random walks and barriers, random Euler products, the reduction to Euler product integrals, Mellin analysis |

The numerical certificates (the files whose header says "Generated by a script") were produced by
scripts that are not part of this release; Lean checks every certificate itself.

## Licence

Apache 2.0; see [LICENSE](LICENSE).

## Citation

This repository formalises the paper above.  If you use it, please cite the paper rather than the
repository.
