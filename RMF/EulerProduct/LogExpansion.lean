/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

/-!
# From a local expansion to a prime sum: the model-independent steps

Both random Euler products treated here, Steinhaus and Rademacher, reach their prime sums by the
same route, and only the local computation differs.  This file collects the steps that do not
know which model they serve.

## The route

Write `I_p` for the local moment at the prime `p`, `P_p` for the polynomial in `w = p ^ (-s)`
that is supposed to approximate `log I_p`, and `t = ‖w‖`.

1. *Fine regime.*  Where `t` is small the local expansion gives `I_p = 1 + P_p + O(t ^ 3)`,
   and `log (1 + x) = x + O(x ^ 2)` (`RMF.abs_log_one_add_sub_le`) converts it into
   `log I_p = P_p + O(t ^ 3)` (`RMF.abs_log_sub_poly_le`).
2. *Crude regime.*  Where `t` is not small the expansion is useless, but `t ^ 3` is bounded
   below, so any bound at all suffices.  Trapping `I_p` between `(1 - t) ^ r` and its
   reciprocal gives `|log I_p| = O(1)` (`RMF.abs_log_le_of_rpow_bounds`), and
   `RMF.le_mul_cube_of_two_regime` glues the two regimes into a single `O(t ^ 3)` valid on
   the whole range.  This is what removes any separate treatment of the small primes.
3. *Summation.*  `RMF.abs_log_prod_sub_sum_le` turns a family of local bounds into a bound
   for the logarithm of the product, and `RMF.sum_primesBelow_rpow_le` bounds the resulting
   error sum `∑_{p < y} p ^ (-3 σ)` by a convergent series as soon as `σ > 1/3`.
-/

open Finset

namespace RMF

/-! ### Logarithms -/

/-- `|log (1 + x) - x| ≤ 2 x ^ 2` for `|x| ≤ 1/2`. -/
lemma abs_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  rw [Finset.sum_range_one, abs_neg, show (1 : ℝ) - -x = 1 + x by ring] at h
  norm_num at h
  have h2 : x ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x, abs_nonneg x]
  calc |Real.log (1 + x) - x| = |-x + Real.log (1 + x)| := by congr 1; ring
    _ ≤ x ^ 2 / (1 - |x|) := h
    _ ≤ 2 * x ^ 2 := h2

/-- **The fine regime.**  If a quantity `I` is `1 + P + O(x ^ 3)` with `|P| = O(x ^ 2)` and
`I` close enough to `1`, then `log I = P + O(x ^ 3)`.  This is the step "expand the moment,
then expand the logarithm", isolated so that it is proved in a small context and can serve
either model. -/
lemma abs_log_sub_poly_le {I P x C₀ K : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hC₀ : 0 ≤ C₀)
    (hIP : |I - (1 + P)| ≤ C₀ * x ^ 3) (hP : |P| ≤ K * x ^ 2)
    (hhalf : |I - 1| ≤ 1 / 2) :
    |Real.log I - P| ≤ (2 * (K + C₀) ^ 2 + C₀) * x ^ 3 := by
  have hcube : x ^ 3 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
  have hXP : |(I - 1) - P| ≤ C₀ * x ^ 3 := by
    rw [show I - 1 - P = I - (1 + P) by ring]; exact hIP
  have hXbd : |I - 1| ≤ (K + C₀) * x ^ 2 := by
    have h1 := abs_le.mp hXP
    have h2 := abs_le.mp hP
    rw [abs_le]
    constructor <;> nlinarith
  have hlog : |Real.log I - (I - 1)| ≤ 2 * (I - 1) ^ 2 := by
    rw [show I = 1 + (I - 1) by ring]
    simpa using abs_log_one_add_sub_le hhalf
  have hsq : 2 * (I - 1) ^ 2 ≤ 2 * (K + C₀) ^ 2 * x ^ 3 := by
    have h1 : (I - 1) ^ 2 ≤ ((K + C₀) * x ^ 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hXbd 2
    have h2 : x ^ 4 ≤ x ^ 3 := by nlinarith [pow_nonneg hx 3]
    nlinarith [sq_nonneg (K + C₀)]
  linarith [abs_sub_le (Real.log I) (I - 1) P]

/-- **The crude regime.**  If `I` is trapped between `(1 - t) ^ r` and its reciprocal, with
`t ≤ θ < 1` and `0 ≤ r ≤ R`, then `|log I| ≤ R log ((1 - θ)⁻¹)` — a bound depending on
neither `t` nor `r`.  Both models produce such a pair of bounds. -/
lemma abs_log_le_of_rpow_bounds {I t θ r R : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R) (ht0 : 0 ≤ t)
    (htθ : t ≤ θ) (hθ : θ < 1) (hlow : (1 - t) ^ r ≤ I) (hhigh : I ≤ ((1 - t)⁻¹) ^ r) :
    |Real.log I| ≤ R * Real.log ((1 - θ)⁻¹) := by
  have ht1 : (0 : ℝ) < 1 - t := by linarith
  have hθ1 : (0 : ℝ) < 1 - θ := by linarith
  have hlogt : Real.log (1 - t) = -Real.log ((1 - t)⁻¹) := by rw [Real.log_inv, neg_neg]
  have hL0 : 0 ≤ Real.log ((1 - t)⁻¹) :=
    Real.log_nonneg (one_le_inv_iff₀.mpr ⟨ht1, by linarith⟩)
  have hLL : Real.log ((1 - t)⁻¹) ≤ Real.log ((1 - θ)⁻¹) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hlo : -(r * Real.log ((1 - t)⁻¹)) ≤ Real.log I := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos ht1 r) hlow
    rwa [Real.log_rpow ht1, hlogt, mul_neg] at h
  have hhi : Real.log I ≤ r * Real.log ((1 - t)⁻¹) := by
    have h := Real.log_le_log (lt_of_lt_of_le (Real.rpow_pos_of_pos ht1 r) hlow) hhigh
    rwa [Real.log_rpow (by positivity)] at h
  rw [abs_le]
  constructor <;> nlinarith

/-- **Gluing the two regimes.**  A quantity `E` that is `O(x ^ 3)` for `x ≤ d` and merely
bounded for all `x` is `O(x ^ 3)` throughout, at the cost of `M / d ^ 3` in the constant. -/
lemma le_mul_cube_of_two_regime {x d M C E : ℝ} (hd : 0 < d) (hx : 0 ≤ x) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (hfine : x ≤ d → E ≤ C * x ^ 3) (hcrude : E ≤ M) :
    E ≤ (C + M / d ^ 3) * x ^ 3 := by
  have hMd : 0 ≤ M / d ^ 3 := div_nonneg hM (by positivity)
  by_cases h : x ≤ d
  · have h1 := hfine h
    have h2 : (0 : ℝ) ≤ M / d ^ 3 * x ^ 3 := mul_nonneg hMd (by positivity)
    nlinarith
  · rw [not_le] at h
    have h3 : d ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hd.le h.le 3
    have h4 : M ≤ M / d ^ 3 * x ^ 3 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h5 : (0 : ℝ) ≤ C * x ^ 3 := mul_nonneg hC (by positivity)
    nlinarith

/-- **The local log-expansion.**  If `|I - (1 + P)| ≤ C₀ t³` whenever `t ≤ 1/5`, `|P| ≤ K t²` and
`|log I| ≤ M₀`, then `|log I - P| ≤ C t³` for every `0 ≤ t ≤ 1`, with `C` depending only on `C₀`,
`K` and `M₀`.  Both models reach their prime sums through this statement; only the local
computation supplying the three hypotheses differs. -/
theorem exists_abs_log_sub_poly_le {C₀ K M₀ : ℝ} (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hM₀ : 0 ≤ M₀) :
    ∃ C > 0, ∀ I P t : ℝ, 0 ≤ t → t ≤ 1 →
      (t ≤ 1 / 5 → |I - (1 + P)| ≤ C₀ * t ^ 3) → |P| ≤ K * t ^ 2 → |Real.log I| ≤ M₀ →
      |Real.log I - P| ≤ C * t ^ 3 := by
  set δ : ℝ := min (1 / 5) (1 / (2 * (K + C₀ + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ5 : δ ≤ 1 / 5 := min_le_left _ _
  have hδK : (K + C₀) * δ ≤ 1 / 2 := by
    have h : δ ≤ 1 / (2 * (K + C₀ + 1)) := min_le_right _ _
    calc (K + C₀) * δ ≤ (K + C₀) * (1 / (2 * (K + C₀ + 1))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  refine ⟨2 * (K + C₀) ^ 2 + C₀ + 1 + (M₀ + K) / δ ^ 3, by positivity, ?_⟩
  intro I P t ht0 ht1 hfine hP hcrude
  refine le_mul_cube_of_two_regime hδ0 ht0 (by positivity) (by positivity) ?_ ?_
  · -- fine regime: `I` is within `1/2` of `1`, so the logarithm may be expanded
    intro hsmall
    have hIP := hfine (hsmall.trans hδ5)
    have hhalf : |I - 1| ≤ 1 / 2 := by
      have h1 := abs_le.mp hIP
      have h2 := abs_le.mp hP
      have ht2 : t ^ 2 ≤ δ := by nlinarith [mul_le_mul hsmall hsmall ht0 hδ0.le]
      have hcube : t ^ 3 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
      have hscale : (K + C₀) * t ^ 2 ≤ (K + C₀) * δ :=
        mul_le_mul_of_nonneg_left ht2 (by positivity)
      rw [abs_le]
      constructor <;> nlinarith
    have h := abs_log_sub_poly_le ht0 ht1 hC₀ hIP hP hhalf
    nlinarith [pow_nonneg ht0 3]
  · -- crude regime: the triangle inequality on `|log I| + |P|`
    have hPK : |P| ≤ K :=
      hP.trans (by nlinarith [mul_nonneg hK (by nlinarith : (0 : ℝ) ≤ 1 - t ^ 2)])
    linarith [abs_sub (Real.log I) P]

/-! ### Summation over the primes -/

/-- A family of local estimates `|log I_p - a p| ≤ C b p` sums to an estimate for the
logarithm of the product.  It knows nothing about either law, and is reusable for joint
moments at several points. -/
lemma abs_log_prod_sub_sum_le {S : Finset ℕ} {I a b : ℕ → ℝ} {C : ℝ}
    (hI : ∀ p ∈ S, 0 < I p) (h : ∀ p ∈ S, |Real.log (I p) - a p| ≤ C * b p) :
    |Real.log (∏ p ∈ S, I p) - ∑ p ∈ S, a p| ≤ C * ∑ p ∈ S, b p := by
  rw [Real.log_prod fun p hp => (hI p hp).ne', ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

/-- A negative real power raised to a natural power is again a negative real power. -/
lemma rpow_neg_pow {x : ℝ} (hx : 0 ≤ x) (σ : ℝ) (n : ℕ) :
    (x ^ (-σ)) ^ n = x ^ (-(n : ℝ) * σ) := by
  rw [← Real.rpow_natCast (x ^ (-σ)) n, ← Real.rpow_mul hx]
  ring_nf

/-- The modulus of `p ^ (-s)` at a prime, for `σ₀ ≤ Re s`, is at most `2 ^ (-σ₀) < 1`:
one threshold serves every prime and every point of the half plane. -/
lemma norm_prime_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hs : σ₀ ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-σ₀) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  calc (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The square and cube of `‖p ^ (-s)‖` are again powers of `p`, depending on `s` only
through `Re s`. -/
lemma norm_prime_cpow_neg_pow {p : ℕ} (hp : p.Prime) (s : ℂ) (n : ℕ) :
    ‖(p : ℂ) ^ (-s)‖ ^ n = (p : ℝ) ^ (-(n : ℝ) * s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, rpow_neg_pow (by positivity)]

/-- The square of `‖p ^ (-s)‖`, with the exponent as a numeral. -/
lemma norm_prime_cpow_neg_sq {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
  rw [norm_prime_cpow_neg_pow hp s 2]; norm_num

/-- The cube of `‖p ^ (-s)‖`, with the exponent as a numeral.  This is the shape in which the
cubic error term enters the prime sum. -/
lemma norm_prime_cpow_neg_cube {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ ^ 3 = (p : ℝ) ^ (-3 * s.re) := by
  rw [norm_prime_cpow_neg_pow hp s 3]; norm_num

/-- For `σ ≥ σ₀ > 1/3` the error sum `∑_{p < y} p ^ (-3 σ)` is bounded, uniformly in `y`, by
the convergent series `∑' n, n ^ (-3 σ₀)`. -/
lemma sum_primesBelow_rpow_le {σ σ₀ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hσ : σ₀ ≤ σ) (y : ℕ) :
    ∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-3 * σ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) := by
  have hsummable : Summable fun n : ℕ => (n : ℝ) ^ (-3 * σ₀) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine (Finset.sum_le_sum fun p hp => ?_).trans
    (Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsummable)
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- **The prime sum, assembled.**  Suppose a local quantity `I w` is positive and satisfies
`|log (I w) - P w| ≤ C₁ ‖w‖ ^ 3` for every `‖w‖ ≤ 2 ^ (-σ₀)` — one threshold covering every
prime and every `s` with `σ₀ ≤ Re s`.  Evaluating at `w = p ^ (-s)` for `p < y`, the errors
sum to at most `C₁ ∑' n, n ^ (-3 σ₀)`, a bound independent of both `y` and `s`.  This is the
whole passage from a local estimate to a prime sum; each model supplies only `I`, `P` and the
two hypotheses. -/
theorem abs_log_prod_prime_sub_sum_le {σ₀ C₁ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hC₁ : 0 ≤ C₁)
    {I P : ℂ → ℝ} (hpos : ∀ w : ℂ, ‖w‖ ≤ (2 : ℝ) ^ (-σ₀) → 0 < I w)
    (hloc : ∀ w : ℂ, ‖w‖ ≤ (2 : ℝ) ^ (-σ₀) → |Real.log (I w) - P w| ≤ C₁ * ‖w‖ ^ 3)
    {s : ℂ} (hs : σ₀ ≤ s.re) (y : ℕ) :
    |Real.log (∏ p ∈ Nat.primesBelow y, I ((p : ℂ) ^ (-s)))
        - ∑ p ∈ Nat.primesBelow y, P ((p : ℂ) ^ (-s))|
      ≤ C₁ * ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) := by
  have hnorm : ∀ p ∈ Nat.primesBelow y, ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-σ₀) := fun p hp =>
    norm_prime_cpow_neg_le (Nat.prime_of_mem_primesBelow hp) (by linarith) hs
  refine (abs_log_prod_sub_sum_le
    (I := fun p : ℕ => I ((p : ℂ) ^ (-s))) (a := fun p : ℕ => P ((p : ℂ) ^ (-s)))
    (b := fun p : ℕ => (p : ℝ) ^ (-3 * s.re))
    (fun p hp => hpos _ (hnorm p hp)) fun p hp => ?_).trans
    (mul_le_mul_of_nonneg_left (sum_primesBelow_rpow_le hσ₀ hs y) hC₁)
  have h := hloc _ (hnorm p hp)
  rwa [norm_prime_cpow_neg_cube (Nat.prime_of_mem_primesBelow hp) s] at h

/-! ### Prime powers -/

/-- Conjugating `p ^ (-s)` conjugates the exponent. -/
lemma conj_natCast_cpow_neg {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (starRingEnd ℂ) ((p : ℂ) ^ (-s)) = (p : ℂ) ^ (-(starRingEnd ℂ) s) := by
  have harg : ((p : ℂ)).arg ≠ Real.pi := by
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (p : ℂ) (-(starRingEnd ℂ) s) harg
  rw [Complex.conj_natCast, map_neg, Complex.conj_conj] at h
  exact h.symm

/-- The two-point combination `p ^ (-s₁) · conj (p ^ (-s₂))` is a single prime power, at the
exponent `s₁ + conj s₂`.  Its real part is `σ₁ + σ₂` and its imaginary part is `t₁ - t₂`. -/
lemma natCast_cpow_neg_mul_conj {p : ℕ} (hp : 0 < p) (s₁ s₂ : ℂ) :
    (p : ℂ) ^ (-s₁) * (starRingEnd ℂ) ((p : ℂ) ^ (-s₂))
      = (p : ℂ) ^ (-(s₁ + (starRingEnd ℂ) s₂)) := by
  have hp0 : ((p : ℂ)) ≠ 0 := by
    simpa using hp.ne'
  rw [conj_natCast_cpow_neg hp, ← Complex.cpow_add _ _ hp0]
  ring_nf

/-! ### The local two-point covariances -/

/-- The real part of `p ^ (-s)` is `p^{-σ} cos(t log p)`. -/
lemma re_natCast_cpow_neg {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ((p : ℂ) ^ (-s)).re = (p : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log p) := by
  have hp0 : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · rw [Complex.log_re, Complex.ofReal_re, Complex.norm_natCast]
    · rw [Complex.log_im, Complex.ofReal_im,
        show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring,
        Complex.arg_ofReal_of_nonneg hpR.le]
  rw [Complex.cpow_def_of_ne_zero hp0, hlog, Complex.exp_re]
  have hre : (((Real.log p : ℝ) : ℂ) * -s).re = -(Real.log p * s.re) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, zero_mul, sub_zero]
    ring
  have him : (((Real.log p : ℝ) : ℂ) * -s).im = -(Real.log p * s.im) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, zero_mul, add_zero]
    ring
  rw [hre, him, Real.cos_neg, Real.rpow_def_of_pos hpR]
  ring_nf

/-- **The two-point kernel.**  The real part of `p ^ (-s₁) conj (p ^ (-s₂))` depends on the
two heights only through their difference. -/
lemma re_natCast_cpow_neg_mul_conj {p : ℕ} (hp : 0 < p) (s₁ s₂ : ℂ) :
    ((p : ℂ) ^ (-s₁) * (starRingEnd ℂ) ((p : ℂ) ^ (-s₂))).re
      = (p : ℝ) ^ (-(s₁.re + s₂.re)) * Real.cos ((s₁.im - s₂.im) * Real.log p) := by
  rw [natCast_cpow_neg_mul_conj hp, re_natCast_cpow_neg hp, Complex.add_re, Complex.conj_re,
    Complex.add_im, Complex.conj_im, ← sub_eq_add_neg]

end RMF
