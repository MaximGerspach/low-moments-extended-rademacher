/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import RMF.EulerProduct.RademacherPrimeSum

/-!
# The Rademacher local moment on the real point, with literal constants

`E‖F_y(½)‖^{2q} ≪ (log y)^{q(2q-1)}` is `RMF.exists_moment_half_le`, whose implicit constant is
dominated by the `1/δ³` of `RMF.exists_abs_log_sub_poly_le`, the two-regime glue in the local
expansion: the fine cubic bound holds only for `‖w‖ ≤ δ ≈ 1.5·10⁻⁴`, and the constant is inflated
by `δ^{-3}` so that one statement covers every prime.  Here the primes are split at a threshold
`P₀` instead:

* for `p ≥ P₀` a fine bound applies with its own modest constant, and `∑_{p ≥ P₀} p^{-3/2}` is
  small;
* for `p < P₀` — finitely many — a *crude* bound suffices, provided it costs only a bounded
  factor.

The crude bound is sharp enough to cost almost nothing.  On the real point `w = p^{-1/2}` the local
moment is `½[(1+t)^{2q} + (1-t)^{2q}]`, and as a function of the exponent `2q` that is **convex**,
so on `2q ∈ [1,2]` it lies below its chord:

`½[(1+t)^{2q} + (1-t)^{2q}] ≤ (2-2q)·1 + (2q-1)(1+t²) = 1 + (2q-1)t²`.

The exponent this produces is `2q-1` rather than the truth `q(2q-1)`, and the difference
`(2q-1)(1-q) ≤ ⅛` is what the small primes cost — over `p < P₀` a bounded factor
`exp(⅛·(log log P₀ + O(1)))`, whatever `P₀` is.

The chord bound is Bernoulli's inequality twice: `a^{1+λ} = a·a^λ ≤ a(λa + 1 - λ)`, and
`a^λ ≤ λa + (1-λ)` is weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`).
-/

open MeasureTheory

namespace RMF

/-! ### The chord of `s ↦ a^s` between `s = 1` and `s = 2` -/

/-- **`a^{1+λ} ≤ (1-λ)a + λa²`** for `a ≥ 0` and `λ ∈ [0,1]`: the convex `s ↦ a^s` lies below its
chord on `[1,2]`.  Bernoulli, `a^λ ≤ λa + (1-λ)`, multiplied by `a`. -/
theorem rpow_one_add_le_chord {a l : ℝ} (ha : 0 ≤ a) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    a ^ (1 + l) ≤ (1 - l) * a + l * a ^ 2 := by
  rcases eq_or_lt_of_le ha with rfl | ha0
  · rw [Real.zero_rpow (by linarith)]
    simp
  · have hbern : a ^ l ≤ l * a + (1 - l) := by
      have h := Real.geom_mean_le_arith_mean2_weighted hl0 (by linarith : (0 : ℝ) ≤ 1 - l)
        ha (by norm_num : (0 : ℝ) ≤ 1) (by ring)
      simpa using h
    calc a ^ (1 + l) = a * a ^ l := by rw [Real.rpow_add ha0, Real.rpow_one]
      _ ≤ a * (l * a + (1 - l)) := mul_le_mul_of_nonneg_left hbern ha0.le
      _ = (1 - l) * a + l * a ^ 2 := by ring

/-- **The chord bound on the Rademacher local moment, in closed form**: for `0 ≤ t ≤ 1` and
`½ ≤ q ≤ 1`, `½[(1+t)^{2q} + (1-t)^{2q}] ≤ 1 + (2q-1)t²`.  The endpoints are exact (`1` at `q = ½`,
`1 + t²` at `q = 1`); in between the coefficient `2q-1` exceeds the true `q(2q-1)` by
`(2q-1)(1-q) ≤ ⅛`. -/
theorem rademacher_local_chord {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    ((1 + t) ^ (2 * q) + (1 - t) ^ (2 * q)) / 2 ≤ 1 + (2 * q - 1) * t ^ 2 := by
  have he : (2 : ℝ) * q = 1 + (2 * q - 1) := by ring
  rw [he]
  have h1 := rpow_one_add_le_chord (a := 1 + t) (l := 2 * q - 1)
    (by linarith) (by linarith) (by linarith)
  have h2 := rpow_one_add_le_chord (a := 1 - t) (l := 2 * q - 1)
    (by linarith) (by linarith) (by linarith)
  nlinarith [h1, h2]

/-- **The local moment at a real point** `w = t ∈ [0,1]`, in closed form:
`E‖1 + X t‖^{2q} = ½[(1+t)^{2q} + (1-t)^{2q}]`. -/
theorem integral_norm_one_add_mul_rpow_rademacherLaw_real {t q : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (∫ z, ‖1 + z * (t : ℂ)‖ ^ (2 * q) ∂rademacherLaw)
      = ((1 + t) ^ (2 * q) + (1 - t) ^ (2 * q)) / 2 := by
  have hnorm : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hre : ((t : ℂ)).re = t := Complex.ofReal_re t
  have hplus : 1 + 2 * t + t ^ 2 = (1 + t) ^ 2 := by ring
  have hminus : 1 - 2 * t + t ^ 2 = (1 - t) ^ 2 := by ring
  have hpow : ∀ a : ℝ, 0 ≤ a → (a ^ 2) ^ q = a ^ (2 * q) := by
    intro a ha
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
    norm_num
  rw [integral_norm_one_add_mul_rpow_rademacherLaw, hre, hnorm, hplus, hminus,
    hpow (1 + t) (by linarith), hpow (1 - t) (by linarith)]

/-- **The chord bound on the local moment itself**, at a real point `w = t ∈ [0,1]` and
`½ ≤ q ≤ 1`: `E‖1 + X t‖^{2q} ≤ 1 + (2q-1)t²`.  The small primes are handled with it;
`t = p^{-1/2}` is at most `1/√2 < 1`. -/
theorem integral_norm_one_add_mul_rpow_rademacherLaw_le {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (t : ℂ)‖ ^ (2 * q) ∂rademacherLaw) ≤ 1 + (2 * q - 1) * t ^ 2 := by
  rw [integral_norm_one_add_mul_rpow_rademacherLaw_real ht0 ht1]
  exact rademacher_local_chord ht0 ht1 hq0 hq1

/-! ### The fine bound, with a literal constant

On all but finitely many primes the chord is far too lossy: it gives the exponent `2q-1` instead of
the true coefficient `q(2q-1)`.  The fine bound puts the local moment in closed hyperbolic form,
`½[(1+t)^{2q} + (1-t)^{2q}] = (1-t²)^q·cosh(q·log((1+t)/(1-t)))`, and bounds each factor by an
exponential: `(1-t²)^q ≤ e^{-qt²}` because `log(1-u) ≤ -u`, and `cosh u ≤ e^{u²/2}`
(`Real.cosh_le_exp_half_sq`).  The exponents combine to `q(2q-1)t² + …`, the `-qt²` from the
geometric mean and the `2q²t²` from the hyperbolic cosine: **the main term is a difference**.  The
only quantitative input is `log((1+t)/(1-t)) ≤ 2t + 4t³` on `t ≤ ½`
(`Real.abs_log_sub_add_sum_range_le` at `n = 2`, at `x = t` and `x = -t`). -/

/-- **The local moment in closed hyperbolic form.**  `½[(1+t)^{2q} + (1-t)^{2q}]` is the geometric
mean `(1-t²)^q` times `cosh` of half the log-ratio. -/
theorem rademacher_local_cosh {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((1 + t) ^ (2 * q) + (1 - t) ^ (2 * q)) / 2
      = (1 - t ^ 2) ^ q * Real.cosh (q * Real.log ((1 + t) / (1 - t))) := by
  have hp : (0 : ℝ) < 1 + t := by linarith
  have hm : (0 : ℝ) < 1 - t := by linarith
  have hsq : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hdiv : (0 : ℝ) < (1 + t) / (1 - t) := div_pos hp hm
  have hdiv' : (0 : ℝ) < (1 - t) / (1 + t) := div_pos hm hp
  have hexp : Real.exp (q * Real.log ((1 + t) / (1 - t))) = ((1 + t) / (1 - t)) ^ q := by
    rw [Real.rpow_def_of_pos hdiv, mul_comm]
  have hlogneg : Real.log ((1 - t) / (1 + t)) = -Real.log ((1 + t) / (1 - t)) := by
    rw [Real.log_div hm.ne' hp.ne', Real.log_div hp.ne' hm.ne']
    ring
  have hexpn : Real.exp (-(q * Real.log ((1 + t) / (1 - t)))) = ((1 - t) / (1 + t)) ^ q := by
    rw [Real.rpow_def_of_pos hdiv', hlogneg]
    ring_nf
  have h1 : (1 - t ^ 2) ^ q * ((1 + t) / (1 - t)) ^ q = (1 + t) ^ (2 * q) := by
    rw [← Real.mul_rpow hsq.le hdiv.le,
      show (1 - t ^ 2) * ((1 + t) / (1 - t)) = (1 + t) ^ 2 by field_simp; ring,
      ← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul hp.le]
    norm_num
  have h2 : (1 - t ^ 2) ^ q * ((1 - t) / (1 + t)) ^ q = (1 - t) ^ (2 * q) := by
    rw [← Real.mul_rpow hsq.le hdiv'.le,
      show (1 - t ^ 2) * ((1 - t) / (1 + t)) = (1 - t) ^ 2 by field_simp; ring,
      ← Real.rpow_natCast (1 - t) 2, ← Real.rpow_mul hm.le]
    norm_num
  rw [Real.cosh_eq, hexp, hexpn]
  field_simp
  linarith [h1, h2]

/-- **`log((1+t)/(1-t)) ≤ 2t + 4t³` on `[0, ½]`.**  `Real.abs_log_sub_add_sum_range_le` at `n = 2`,
used at `x = t` and at `x = -t`: the quadratic terms cancel in the difference and the two cubic
remainders add. -/
theorem log_div_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.log ((1 + t) / (1 - t)) ≤ 2 * t + 4 * t ^ 3 := by
  have hm : (0 : ℝ) < 1 - t := by linarith
  have hp : (0 : ℝ) < 1 + t := by linarith
  have habs : |t| = t := abs_of_nonneg ht0
  have habs' : |(-t)| = t := by rw [abs_neg, habs]
  have hlt : |t| < 1 := by rw [habs]; linarith
  have hlt' : |(-t)| < 1 := by rw [habs']; linarith
  have h1 := Real.abs_log_sub_add_sum_range_le hlt 2
  have h2 := Real.abs_log_sub_add_sum_range_le hlt' 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, habs, habs'] at h1 h2
  have hden : t ^ 3 / (1 - t) ≤ 2 * t ^ 3 := by
    rw [div_le_iff₀ hm]
    nlinarith [pow_nonneg ht0 3]
  have hb1 := abs_le.1 h1
  have hb2 := abs_le.1 h2
  rw [Real.log_div hp.ne' hm.ne']
  have hsub : (1 : ℝ) - -t = 1 + t := by ring
  rw [hsub] at hb2
  norm_num at hb1 hb2
  nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hden]

/-- **The fine local bound, with a literal constant.**  For `0 ≤ t ≤ ½` and `0 ≤ q ≤ 1`,

`½[(1+t)^{2q} + (1-t)^{2q}] ≤ exp(q(2q-1)t² + 10t⁴)`.

The main term is exact; `10` is the whole error constant, and `∑_{p≥5} 10/p² < 1`. -/
theorem rademacher_local_fine {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((1 + t) ^ (2 * q) + (1 - t) ^ (2 * q)) / 2
      ≤ Real.exp (q * (2 * q - 1) * t ^ 2 + 10 * t ^ 4) := by
  have hm : (0 : ℝ) < 1 - t := by linarith
  have hsq : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  -- the geometric mean
  have hgm : (1 - t ^ 2) ^ q ≤ Real.exp (-(q * t ^ 2)) := by
    rw [Real.rpow_def_of_pos hsq]
    refine Real.exp_le_exp.2 ?_
    have hlog : Real.log (1 - t ^ 2) ≤ -t ^ 2 := by
      have := Real.log_le_sub_one_of_pos hsq
      linarith
    have := mul_le_mul_of_nonneg_right hlog hq0
    linarith
  -- the hyperbolic cosine
  have hL0 : (0 : ℝ) ≤ Real.log ((1 + t) / (1 - t)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hm]
    linarith
  have hL := log_div_one_sub_le ht0 ht1
  have hLsq : Real.log ((1 + t) / (1 - t)) ^ 2 ≤ (2 * t + 4 * t ^ 3) ^ 2 :=
    pow_le_pow_left₀ hL0 hL 2
  have hu : (q * Real.log ((1 + t) / (1 - t))) ^ 2 ≤ q ^ 2 * (2 * t + 4 * t ^ 3) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hLsq (sq_nonneg q)
  have hcosh : Real.cosh (q * Real.log ((1 + t) / (1 - t)))
      ≤ Real.exp (q ^ 2 * (2 * t + 4 * t ^ 3) ^ 2 / 2) :=
    le_trans (Real.cosh_le_exp_half_sq _) (Real.exp_le_exp.2 (by linarith))
  -- and the two exponents combine
  have hcnn : (0 : ℝ) ≤ Real.cosh (q * Real.log ((1 + t) / (1 - t))) := by
    rw [Real.cosh_eq]
    positivity
  rw [rademacher_local_cosh ht0 (by linarith)]
  calc (1 - t ^ 2) ^ q * Real.cosh (q * Real.log ((1 + t) / (1 - t)))
      ≤ Real.exp (-(q * t ^ 2)) * Real.exp (q ^ 2 * (2 * t + 4 * t ^ 3) ^ 2 / 2) :=
        mul_le_mul hgm hcosh hcnn (Real.exp_pos _).le
    _ = Real.exp (-(q * t ^ 2) + q ^ 2 * (2 * t + 4 * t ^ 3) ^ 2 / 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (q * (2 * q - 1) * t ^ 2 + 10 * t ^ 4) := by
        refine Real.exp_le_exp.2 ?_
        have hq2 : q ^ 2 ≤ 1 := by nlinarith
        have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
        have ht6 : t ^ 6 ≤ t ^ 4 / 4 := by
          nlinarith [mul_nonneg (pow_nonneg ht0 4) (by linarith : (0 : ℝ) ≤ 1 / 4 - t ^ 2)]
        have hkey : 8 * q ^ 2 * t ^ 4 + 8 * q ^ 2 * t ^ 6 ≤ 10 * t ^ 4 := by
          nlinarith [pow_nonneg ht0 4, pow_nonneg ht0 6, sq_nonneg q]
        have hexpand : -(q * t ^ 2) + q ^ 2 * (2 * t + 4 * t ^ 3) ^ 2 / 2
            = q * (2 * q - 1) * t ^ 2 + (8 * q ^ 2 * t ^ 4 + 8 * q ^ 2 * t ^ 6) := by ring
        rw [hexpand]
        linarith

/-! ### The product over the primes

`E‖F_y(½)‖^{2q} = ∏_{p<y} m(p^{-1/2})`, and each factor is bounded by an exponential: the fine
bound for `p ≥ 31` and the chord for the ten primes below `31`, where the chord penalty is smaller
than the fine error (the fine bound itself needs only `t = p^{-1/2} ≤ ½`).  The two errors are
`10∑_{p≥31}p^{-2} ≤ 1/3` and `(2q-1)(1-q)∑_{p<31}1/p ≤ ⅛·(77/50)`, below `3/5` in total. -/

/-- `∑_{m ≤ n < N} n^{-2} ≤ 1/(m−1) − 1/(N−1)`, by telescoping `n^{-2} ≤ (n−1)^{-1} − n^{-1}`. -/
lemma sum_inv_sq_Ico_le_sub {m : ℕ} (hm : 2 ≤ m) : ∀ N : ℕ, m ≤ N →
    ∑ n ∈ Finset.Ico m N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((m : ℝ) - 1) - 1 / ((N : ℝ) - 1) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ M ih =>
    intro hM
    rcases eq_or_lt_of_le hM with h | h
    · subst h
      rw [Finset.Ico_self]
      simp
    · have hMm : m ≤ M := by omega
      have hM2 : 2 ≤ M := le_trans hm hMm
      have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
      rw [Finset.sum_Ico_succ_top hMm]
      have hIH := ih hMm
      have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
      have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
      have hstep : (1 : ℝ) / (M : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / (M : ℝ) := by
        rw [div_sub_div _ _ (ne_of_gt hM1) (ne_of_gt hM0),
          div_le_div_iff₀ (by positivity) (mul_pos hM1 hM0)]
        nlinarith
      push_cast
      rw [show ((M : ℝ) + 1 - 1) = (M : ℝ) by ring]
      linarith

/-- `∑_{m ≤ n < N} n^{-2} ≤ 1/(m−1)`, for every `N`. -/
lemma sum_inv_sq_Ico_le {m : ℕ} (hm : 2 ≤ m) (N : ℕ) :
    ∑ n ∈ Finset.Ico m N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((m : ℝ) - 1) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rcases Nat.lt_or_ge N m with h | h
  · rw [Finset.Ico_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    exact le_of_lt (div_pos one_pos (by linarith))
  · have hN2 : (2 : ℕ) ≤ N := le_trans hm h
    have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have hmain := sum_inv_sq_Ico_le_sub hm N h
    have hpos : (0 : ℝ) < 1 / ((N : ℝ) - 1) := div_pos one_pos (by linarith)
    linarith

/-- `p ^ (-(1/2) : ℂ)` is the real number `p ^ (-1/2)`. -/
lemma cpow_neg_half_eq (p : ℕ) :
    ((p : ℂ) ^ (-(1 / 2 : ℂ))) = (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  norm_num

/-- The square of `p ^ (-1/2)` is `1/p`. -/
lemma rpow_neg_half_sq {p : ℕ} (hp : 0 < p) :
    ((p : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 = ((p : ℝ))⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2) : ℝ)) 2, ← Real.rpow_mul hp0.le,
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]

/-- **The local moment at a prime, chord form.**  `E‖1 + X p^{-1/2}‖^{2q} ≤ 1 + (2q-1)/p`. -/
theorem integral_norm_one_add_prime_le_chord {p : ℕ} (hp : p.Prime) {q : ℝ}
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ 1 + (2 * q - 1) * ((p : ℝ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hsq := rpow_neg_half_sq hp.pos
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    simpa using h
  have ht1 : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 := by nlinarith
  have hkey := integral_norm_one_add_mul_rpow_rademacherLaw_le
    (t := (p : ℝ) ^ (-(1 / 2) : ℝ)) ht0 ht1 hq0 hq1
  rw [hsq] at hkey
  rwa [cpow_neg_half_eq p]

/-- **The local moment at a prime `p ≥ 5`, fine form.**
`E‖1 + X p^{-1/2}‖^{2q} ≤ exp(q(2q-1)/p + 10/p²)`. -/
theorem integral_norm_one_add_prime_le_fine {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * ((p : ℝ))⁻¹ + 10 * (((p : ℝ))⁻¹) ^ 2) := by
  have hp5R : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hsq := rpow_neg_half_sq hp.pos
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hinv : ((p : ℝ))⁻¹ ≤ 1 / 4 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ (p : ℝ))
    simpa using h
  have ht1 : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 2 := by nlinarith
  have hfour : (((p : ℝ)) ^ (-(1 / 2) : ℝ)) ^ 4 = (((p : ℝ))⁻¹) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
  have hkey := rademacher_local_fine (t := (p : ℝ) ^ (-(1 / 2) : ℝ)) ht0 ht1 hq0 hq1
  rw [hfour, hsq] at hkey
  rw [cpow_neg_half_eq p,
    integral_norm_one_add_mul_rpow_rademacherLaw_real ht0 (le_trans ht1 (by norm_num))]
  exact hkey

/-- **The local product, with a literal constant**: for `½ ≤ q ≤ 1`,
`∏_{p < y} E‖1 + X p^{-1/2}‖^{2q} ≤ exp(q(2q-1)·∑_{p<y} 1/p + 3/5)`.  The fine bound on `p ≥ 31`,
the chord on the ten primes below `31`: the errors are `10·∑_{p≥31}p^{-2} ≤ 10/30` and
`(2q-1)(1-q)·∑_{p<31}1/p ≤ ⅛·(77/50)`, and `1/3 + 77/400 < 3/5`. -/
theorem prod_integral_norm_one_add_prime_le {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (y : ℕ) :
    (∏ p ∈ Nat.primesBelow y, ∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow y, ((p : ℝ))⁻¹) + 3 / 5) := by
  classical
  have hnn : ∀ p ∈ Nat.primesBelow y,
      (0 : ℝ) ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw :=
    fun p _ => integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hbound : ∀ p ∈ Nat.primesBelow y,
      (∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
        ≤ Real.exp (if p < 31 then (2 * q - 1) * ((p : ℝ))⁻¹
            else q * (2 * q - 1) * ((p : ℝ))⁻¹ + 10 * (((p : ℝ))⁻¹) ^ 2) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    by_cases h5 : p < 31
    · rw [if_pos h5]
      refine le_trans (integral_norm_one_add_prime_le_chord hprime hq0 hq1) ?_
      have := Real.add_one_le_exp ((2 * q - 1) * ((p : ℝ))⁻¹)
      linarith
    · rw [if_neg h5]
      exact integral_norm_one_add_prime_le_fine hprime (by omega) (by linarith) hq1
  refine le_trans (Finset.prod_le_prod hnn hbound) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  -- split the sum at `p = 31`
  rw [Finset.sum_ite]
  have hsplit : ∑ p ∈ Nat.primesBelow y, ((p : ℝ))⁻¹
      = (∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), ((p : ℝ))⁻¹)
        + ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), ((p : ℝ))⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsmall : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (2 * q - 1) * ((p : ℝ))⁻¹
      = (2 * q - 1) * ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), ((p : ℝ))⁻¹ :=
    (Finset.mul_sum _ _ _).symm
  have hlarge : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
        (q * (2 * q - 1) * ((p : ℝ))⁻¹ + 10 * (((p : ℝ))⁻¹) ^ 2)
      = q * (2 * q - 1) * (∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), ((p : ℝ))⁻¹)
        + 10 * ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the two numerical inputs
  have hsub1 : (Nat.primesBelow y).filter (fun p => p < 31)
      ⊆ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp.1
    have h31 : p < 31 := hp.2
    revert hprime
    interval_cases p <;> decide
  have hS1nn : (0 : ℝ) ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), ((p : ℝ))⁻¹ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hS1 : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), ((p : ℝ))⁻¹ ≤ 77 / 50 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun i _ _ => by positivity) ?_
    norm_num
  have hsub2 : (Nat.primesBelow y).filter (fun p => ¬ p < 31) ⊆ Finset.Ico 31 y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_Ico]
    exact ⟨by omega, (Nat.mem_primesBelow.1 hp.1).1⟩
  have hS2 : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2 ≤ 1 / 30 := by
    calc ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2
        = ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2 :=
          Finset.sum_congr rfl fun p _ => by rw [inv_pow, one_div]
      _ ≤ ∑ n ∈ Finset.Ico 31 y, (1 : ℝ) / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i _ _ => by positivity
      _ ≤ 1 / (((31 : ℕ) : ℝ) - 1) := sum_inv_sq_Ico_le (by norm_num) y
      _ = 1 / 30 := by norm_num
  have hcoef : (2 * q - 1) * (1 - q) ≤ 1 / 8 := by nlinarith [sq_nonneg (4 * q - 3)]
  have hcoef0 : (0 : ℝ) ≤ (2 * q - 1) * (1 - q) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hsmall, hlarge, hsplit]
  nlinarith [hS1, hS1nn, hS2, hcoef, hcoef0,
    mul_le_mul_of_nonneg_right hcoef hS1nn, mul_le_mul_of_nonneg_left hS1 hcoef0]

/-- **The Rademacher Euler product moment on the real critical point, explicitly.**

`E‖F_y(½)‖^{2q} ≤ exp(q(2q-1)·∑_{p<y} 1/p + 3/5)`  for `½ ≤ q ≤ 1`.

The prime sum is left as it stands: what turns it into `(log y)^{q(2q-1)}` is Mertens, and only
there does a constant that is not a small literal enter. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_half_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (y : ℕ) :
    (∫ ω, ‖randomEulerProduct f y (1 / 2) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow y, ((p : ℝ))⁻¹) + 3 / 5) := by
  rw [hf.integral_norm_randomEulerProduct_rpow_of_pos y (by norm_num) (2 * q)]
  exact prod_integral_norm_one_add_prime_le hq0 hq1 y

/-! ### Below the critical exponent

For `q ≤ ½` the chord bound is **false** — at `q = 0` its right-hand side is `1 - t² < 1` while
the local moment is exactly `1` — but nothing sharper is needed there.  `s ↦ s^{2q}` is concave
for `2q ≤ 1`, so the local moment is at most `1`; and `q(2q-1) ≤ 0` means giving the small primes
away for free costs only `q(1-2q)·∑_{p<31}1/p ≤ ⅛·(77/50)`, which is exactly the chord penalty it
replaces.  The fine bound needs only `0 ≤ q`, so the same threshold `31` and the same constant
`3/5` carry over verbatim.

Here `q(2q-1)` is negative, so the resulting bound `E‖F_y(½)‖^{2q} ≪ (log y)^{q(2q-1)}` decays
in `y`. -/

/-- **The local moment is at most `1` below the critical exponent.**  Bernoulli twice:
`(1±t)^{2q} ≤ 1 ± 2qt` for `0 ≤ 2q ≤ 1`, and the two linear terms cancel. -/
theorem rademacher_local_le_one {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ((1 + t) ^ (2 * q) + (1 - t) ^ (2 * q)) / 2 ≤ 1 := by
  have hb : ∀ a : ℝ, 0 ≤ a → a ^ (2 * q) ≤ 2 * q * a + (1 - 2 * q) := by
    intro a ha
    have h := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 2 * q)
      (by linarith : (0 : ℝ) ≤ 1 - 2 * q) ha zero_le_one (by ring)
    simpa using h
  have h1 := hb (1 + t) (by linarith)
  have h2 := hb (1 - t) (by linarith)
  linarith

end RMF
