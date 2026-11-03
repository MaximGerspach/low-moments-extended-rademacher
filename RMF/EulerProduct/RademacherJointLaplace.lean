/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.JointLaplace
import RMF.EulerProduct.JointMoments
import RMF.EulerProduct.RademacherLogField
import RMF.EulerProduct.RademacherPrimeSum

/-!
# The joint Laplace transform, for the Rademacher random multiplicative function

`RMF/EulerProduct/JointLaplace.lean` writes the multi-point moment `E ∏_a ‖F_y(s_a)‖^{2q_a}` as a
prime sum and derives the deviation bounds of Hamdan's Lemma B.1 from it.  This module is its
Rademacher counterpart, starting from the two-atom closed form
`RMF.integral_prod_norm_one_add_mul_rpow_rademacherLaw`.

**The two-atom law does the circle integral's work.**  The Steinhaus multi-point moment is an
integral over the circle; here it is the average of the product at `z = 1` and `z = -1`, so each
atom is an explicit exponential and the local bounds reduce to real algebra.

What it does **not** buy is rotation invariance.  The Steinhaus answer is `1 + ‖∑_a q_a w_a‖²`, a
function of the weights through a single modulus; the Rademacher answer keeps the phases, as the
one-point case `RMF.exists_local_expansion_rademacherLaw` does.
-/

open MeasureTheory

namespace RMF

variable {ι : Type*}

/-! ### The local polynomial in trigonometric form

At `w_a = p^{-s_a}` with `Re s_a = σ`, `t_a = Im s_a` and `L = log p`, `‖w_a‖² = p^{-2σ}` and
`Re w_a = p^{-σ} cos(t_a L)`, so

    ∑_a q_a‖w_a‖² - 2∑_a q_a(Re w_a)² + 2(∑_a q_a Re w_a)²
      = p^{-2σ}[ ∑_a q_a - 2∑_a q_a cos²(t_a L) + 2(∑_a q_a cos(t_a L))² ]
      = p^{-2σ}[ 2(∑_a q_a cos(t_a L))² - ∑_a q_a cos(2 t_a L) ]

by `cos²x = (1 + cos 2x)/2`.  **This is not the Steinhaus answer**
`‖∑_a q_a p^{-s_a}‖² = p^{-2σ}∑_{a,b} q_a q_b cos((t_a - t_b)L)`, which sees only the differences
of the heights; here the heights enter individually, through `cos(t_a L)` and `cos(2t_a L)`. -/

/-- **The multi-point local polynomial, in trigonometric form** — the analogue of
`RMF.local_poly_eq`, whose coefficient `q² + q(q-1)cos(2tL)` is the singleton case. -/
lemma local_poly_multi_eq {p : ℕ} (hp : p.Prime) (A : Finset ι) (q : ι → ℝ) (s : ι → ℂ)
    {σ : ℝ} (hs : ∀ a ∈ A, (s a).re = σ) :
    (∑ a ∈ A, q a * ‖(p : ℂ) ^ (-s a)‖ ^ 2)
        - 2 * (∑ a ∈ A, q a * (((p : ℂ) ^ (-s a)).re) ^ 2)
        + 2 * (∑ a ∈ A, q a * (((p : ℂ) ^ (-s a)).re)) ^ 2
      = (p : ℝ) ^ (-2 * σ)
        * (2 * (∑ a ∈ A, q a * Real.cos ((s a).im * Real.log p)) ^ 2
            - ∑ a ∈ A, q a * Real.cos (2 * ((s a).im * Real.log p))) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hsq : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-2 * σ) := by
    rw [rpow_neg_pow hp0]
    norm_num
  have hnorm : ∀ a ∈ A, ‖(p : ℂ) ^ (-s a)‖ ^ 2 = (p : ℝ) ^ (-2 * σ) := fun a ha => by
    rw [norm_prime_cpow_neg_sq hp, hs a ha]
  have hre : ∀ a ∈ A, ((p : ℂ) ^ (-s a)).re
      = (p : ℝ) ^ (-σ) * Real.cos ((s a).im * Real.log p) := fun a ha => by
    rw [re_natCast_cpow_neg hp.pos, hs a ha]
  -- the three sums, each with `p^{-σ}` pulled out
  have h1 : (∑ a ∈ A, q a * ‖(p : ℂ) ^ (-s a)‖ ^ 2)
      = (p : ℝ) ^ (-2 * σ) * ∑ a ∈ A, q a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [hnorm a ha]; ring
  have h2 : (∑ a ∈ A, q a * (((p : ℂ) ^ (-s a)).re) ^ 2)
      = (p : ℝ) ^ (-2 * σ) * ∑ a ∈ A, q a * Real.cos ((s a).im * Real.log p) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hre a ha, mul_pow, ← hsq]
    ring
  have h3 : (∑ a ∈ A, q a * (((p : ℂ) ^ (-s a)).re))
      = (p : ℝ) ^ (-σ) * ∑ a ∈ A, q a * Real.cos ((s a).im * Real.log p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [hre a ha]; ring
  -- `cos² x = (1 + cos 2x)/2` collapses the first two sums
  have h4 : (∑ a ∈ A, q a)
      - 2 * (∑ a ∈ A, q a * Real.cos ((s a).im * Real.log p) ^ 2)
      + (∑ a ∈ A, q a * Real.cos (2 * ((s a).im * Real.log p))) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun a _ => by rw [Real.cos_sq]; ring
  rw [h1, h2, h3, mul_pow, ← hsq]
  linear_combination ((p : ℝ) ^ (-σ)) ^ 2 * h4

/-! ### The pair crude bound, by reflection

The pair local estimate needs a crude bound `|log I| ≤ Λ` in which the **unbounded** `l₂` appears
only as `l₂ d`; a constant `|A|·Q·2log((1-θ)⁻¹)` is useless here, because `Q = max(l₁/2, l₂/2)` and
`l₂ → ∞`.

**It comes for free.**  `RMF.localLogAdd_eq_neg_localLog` says the Rademacher local variable is the
Steinhaus one at the reflected point, `localLogAdd w z = -localLog (-w) z`, so the Rademacher
exponent at `w` is minus `RMF.logExponent` at `-w`; and reflection preserves both `‖w a‖` and
`‖w 1 - w 2‖`.  So `RMF.abs_logExponent_pairWeight_le` — which is where the Steinhaus side does
the work, via `RMF.abs_log_sub_log_le` on the chord `|‖1 - z w₁‖ - ‖1 - z w₂‖| ≤ ‖w₁ - w₂‖` —
transfers verbatim.

This is the same trick `RMF.abs_localLogAdd_le` uses at one point. -/

/-- The Rademacher exponent is minus the Steinhaus one at the reflected weights. -/
lemma two_mul_sum_localLogAdd_eq (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) (z : ℂ) :
    2 * ∑ a ∈ A, q a * localLogAdd (w a) z = -logExponent A q (fun a => -w a) z := by
  have h : ∀ a ∈ A, q a * localLogAdd (w a) z = -(q a * localLog (-w a) z) := fun a _ => by
    rw [localLogAdd_eq_neg_localLog]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib, logExponent]
  ring

/-- **The pair crude bound for the Rademacher exponent.**  The counterpart of
`RMF.abs_logExponent_pairWeight_le`, and equal to it by reflection.

The point is the shape of the right-hand side: the unbounded `l₂` enters only through `l₂ d`, with
`d` the chord `‖w₁ - w₂‖ / θ`.  That is what Hamdan's chaining needs. -/
lemma abs_two_mul_sum_pairWeight_localLogAdd_le {l₁ l₂ θ d : ℝ} {w : Fin 3 → ℂ} {z : ℂ}
    (hz : ‖z‖ = 1) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hθ : θ < 1) (h0 : ‖w 0‖ ≤ θ)
    (h1 : ‖w 1‖ ≤ θ) (h2 : ‖w 2‖ ≤ θ) (h12 : ‖w 1 - w 2‖ ≤ θ * d) :
    |2 * ∑ a, pairWeight l₁ l₂ a * localLogAdd (w a) z|
      ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * (θ / (1 - θ)) := by
  rw [two_mul_sum_localLogAdd_eq, abs_neg]
  have hd : ‖(-w 1) - (-w 2)‖ ≤ θ * d := by
    rw [neg_sub_neg, norm_sub_rev]
    exact h12
  have hn : ∀ a : Fin 3, ‖(-w a)‖ = ‖w a‖ := fun a => norm_neg _
  exact abs_logExponent_pairWeight_le hz hl₁ hl₂ hθ (by rw [hn]; exact h0)
    (by rw [hn]; exact h1) (by rw [hn]; exact h2) hd

/-! ### The fine half, pointwise

`RMF.abs_logExponent_sub_taylorExponent_le_of_moments` is pointwise in `z` and law-free: it
compares the Steinhaus exponent with its degree-two truncation under `‖∑_a q_a w_a^k‖ ≤ M k θ^k`
for `k ≥ 3`, with a constant **linear in `M`**, which the pair case needs.

**It transfers by reflection.**  `∑_a q_a (-w_a)^k = (-1)^k ∑_a q_a w_a^k` has the same norm, so
the moment hypotheses are unchanged, and the Rademacher exponent is minus the Steinhaus one at `-w`
(`RMF.two_mul_sum_localLogAdd_eq`).  The integrated step
`RMF.abs_integral_prod_localIntegrand_sub_le_of_moments` does not transfer (it integrates against
`steinhausLaw`) and is not needed: the Rademacher moment is a two-term average, and the two atoms
are handled directly. -/

/-- **The pointwise fine bound for the Rademacher exponent**, with a constant **linear** in the
moment size `M`.  The counterpart of `RMF.abs_logExponent_sub_taylorExponent_le_of_moments`, and
equal to it by reflection. -/
lemma abs_two_mul_sum_localLogAdd_sub_taylorExponent_le_of_moments {A : Finset ι} {q : ι → ℝ}
    {w : ι → ℂ} {z : ℂ} {θ M : ℝ} (hz : ‖z‖ = 1) (hw : ∀ a ∈ A, ‖w a‖ ≤ θ) (hθ : θ < 1)
    (hθ0 : 0 ≤ θ)
    (hM : ∀ k : ℕ, 3 ≤ k → ‖∑ a ∈ A, (q a : ℂ) * w a ^ k‖ ≤ M * k * θ ^ k) :
    |(2 * ∑ a ∈ A, q a * localLogAdd (w a) z)
        - -taylorExponent A q (fun a => -w a) z| ≤ 2 * (M * θ ^ 3 / (1 - θ)) := by
  have hrefl : ∀ k : ℕ, 3 ≤ k →
      ‖∑ a ∈ A, (q a : ℂ) * (fun a => -w a) a ^ k‖ ≤ M * k * θ ^ k := by
    intro k hk
    have he : (∑ a ∈ A, (q a : ℂ) * (-w a) ^ k)
        = (-1) ^ k * ∑ a ∈ A, (q a : ℂ) * w a ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hn : ‖(∑ a ∈ A, (q a : ℂ) * (-w a) ^ k)‖ = ‖∑ a ∈ A, (q a : ℂ) * w a ^ k‖ := by
      rw [he, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hn]
    exact hM k hk
  have hwn : ∀ a ∈ A, ‖(fun a => -w a) a‖ ≤ θ := fun a ha => by
    rw [norm_neg]
    exact hw a ha
  have h := abs_logExponent_sub_taylorExponent_le_of_moments (A := A) (q := q)
    (w := fun a => -w a) hz hwn hθ hθ0 hrefl
  rw [two_mul_sum_localLogAdd_eq,
    show -logExponent A q (fun a => -w a) z - -taylorExponent A q (fun a => -w a) z
      = -(logExponent A q (fun a => -w a) z - taylorExponent A q (fun a => -w a) z) by ring,
    abs_neg]
  exact h

/-! ### The atoms in exponential form

The two-atom evaluation gives the moment as an average of two products, and the exponent lemmas
above bound `2 ∑_a q_a localLogAdd (w a) z`.  Each product **is** the exponential of that exponent,
at `z = ±1`.

The Steinhaus counterpart is `RMF.prod_norm_inv_one_sub_rpow_eq_exp`; here the proof is direct,
since `RMF.localLogAdd w z` is by definition `log ‖1 + z w‖`.

**What this unlocks.**  The Steinhaus assembly
(`RMF.abs_integral_prod_localIntegrand_sub_le_of_moments`) spends most of its length on
integrability and a.e. reasoning against `steinhausLaw`.  None of that is needed here: the moment
is a two-term average of explicit positive reals, so once each atom is an exponential the
assembly is `RMF.abs_exp_sub_taylor_le` twice and an average. -/

/-- **Each atom is an exponential.**  `∏_a ‖1 + z w_a‖^{2q_a} = exp(2 ∑_a q_a localLogAdd (w a) z)`
for `‖z‖ = 1` and `‖w_a‖ < 1`.  The Rademacher counterpart of
`RMF.prod_norm_inv_one_sub_rpow_eq_exp`. -/
lemma prod_norm_one_add_mul_rpow_eq_exp (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) {z : ℂ}
    (hz : ‖z‖ = 1) (hw : ∀ a ∈ A, ‖w a‖ < 1) :
    (∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a))
      = Real.exp (2 * ∑ a ∈ A, q a * localLogAdd (w a) z) := by
  have hpos : ∀ a ∈ A, (0 : ℝ) < ‖1 + z * w a‖ := by
    intro a ha
    have h := (norm_one_sub_mul_bounds (w := -w a) (z := z) hz).1
    rw [mul_neg, sub_neg_eq_add, norm_neg] at h
    linarith [hw a ha]
  have hterm : ∀ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a)
      = Real.exp (Real.log ‖1 + z * w a‖ * (2 * q a)) := fun a ha =>
    Real.rpow_def_of_pos (hpos a ha) _
  rw [Finset.prod_congr rfl hterm, ← Real.exp_sum]
  simp only [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [localLogAdd]
  ring

/-! ### The main term of the assembly, identified

The assembly bounds each atom `exp(E_ε)` against `1 + T_ε + T_ε²/2` and averages, so its main term
is `1 + (T₊ + T₋)/2 + (T₊² + T₋²)/4` with `T_ε = -taylorExponent A q (-w) ε`.  This is the
phase-sensitive main term `1 + ∑_a q_a‖w_a‖² - 2∑_a q_a(Re w_a)² + 2(∑_a q_a Re w_a)²` up to
`V²/2`.  Writing `S = 2∑_a q_a Re w_a` and `V = ∑_a q_a Re(w_a²)`, and using
`localTaylorTwo w z = Re(zw) + Re(z²w²)/2`:

* at `z = 1`, `T₊ = S - V`; at `z = -1`, `T₋ = -S - V`;
* so `(T₊ + T₋)/2 = -V` and `(T₊² + T₋²)/4 = (S² + V²)/2`;
* and `-V = ∑ q_a‖w_a‖² - 2∑ q_a Re²`, the first two terms of the phase-sensitive main term,
  while `S²/2 = 2(∑ q_a Re w_a)²` is the third; the residual `V²/2` is `O(t⁴)`. -/

/-- `-taylorExponent` at the atom `z = 1`, written out. -/
lemma neg_taylorExponent_neg_one_eq (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    -taylorExponent A q (fun a => -w a) 1
      = 2 * (∑ a ∈ A, q a * (w a).re) - ∑ a ∈ A, q a * (w a ^ 2).re := by
  have hsum : (∑ a ∈ A, q a * localTaylorTwo (-w a) 1)
      = -(∑ a ∈ A, q a * (w a).re) + (∑ a ∈ A, q a * (w a ^ 2).re) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [localTaylorTwo]
    have h1 : ((1 : ℂ) * -w a).re = -(w a).re := by simp
    have h2 : (((1 : ℂ)) ^ 2 * (-w a) ^ 2).re = (w a ^ 2).re := by
      congr 1
      ring
    rw [h1, h2]
    ring
  rw [taylorExponent]
  linarith [hsum]

/-- `-taylorExponent` at the atom `z = -1`, written out. -/
lemma neg_taylorExponent_neg_neg_one_eq (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    -taylorExponent A q (fun a => -w a) (-1)
      = -(2 * (∑ a ∈ A, q a * (w a).re)) - ∑ a ∈ A, q a * (w a ^ 2).re := by
  have hsum : (∑ a ∈ A, q a * localTaylorTwo (-w a) (-1))
      = (∑ a ∈ A, q a * (w a).re) + (∑ a ∈ A, q a * (w a ^ 2).re) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [localTaylorTwo]
    have h1 : (((-1 : ℂ)) * -w a).re = (w a).re := by simp
    have h2 : (((-1 : ℂ)) ^ 2 * (-w a) ^ 2).re = (w a ^ 2).re := by
      congr 1
      ring
    rw [h1, h2]
    ring
  rw [taylorExponent]
  linarith [hsum]

/-- `-∑ q_a Re(w_a²) = ∑ q_a‖w_a‖² - 2∑ q_a (Re w_a)²`, pointwise from
`Re(w²) = Re² - Im²` and `‖w‖² = Re² + Im²`.

This is where the truncation's main term meets the phase-sensitive one. -/
lemma neg_sum_re_sq_eq (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    -∑ a ∈ A, q a * (w a ^ 2).re
      = (∑ a ∈ A, q a * ‖w a‖ ^ 2) - 2 * ∑ a ∈ A, q a * (w a).re ^ 2 := by
  have hre2 : ∀ v : ℂ, (v ^ 2).re = v.re ^ 2 - v.im ^ 2 := fun v => by
    rw [pow_two, Complex.mul_re]
    ring
  have hn : ∀ v : ℂ, ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := fun v => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hre2, hn]
  ring

/-- **The assembly's main term, identified.**  It is *exactly* the phase-sensitive main term
`1 + ∑_a q_a‖w_a‖² - 2∑_a q_a(Re w_a)² + 2(∑_a q_a Re w_a)²` plus `V²/2`, where
`V = ∑_a q_a Re(w_a²)` is `O(t⁴)`. -/
lemma pair_main_term_eq (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    1 + ((-taylorExponent A q (fun a => -w a) 1)
          + (-taylorExponent A q (fun a => -w a) (-1))) / 2
      + ((-taylorExponent A q (fun a => -w a) 1) ^ 2
          + (-taylorExponent A q (fun a => -w a) (-1)) ^ 2) / 4
      = (1 + (∑ a ∈ A, q a * ‖w a‖ ^ 2) - 2 * (∑ a ∈ A, q a * (w a).re ^ 2)
          + 2 * (∑ a ∈ A, q a * (w a).re) ^ 2)
        + (∑ a ∈ A, q a * (w a ^ 2).re) ^ 2 / 2 := by
  rw [neg_taylorExponent_neg_one_eq, neg_taylorExponent_neg_neg_one_eq]
  have hV := neg_sum_re_sq_eq A q w
  linear_combination hV

/-! ### The assembly's engine

What joins the pieces of the pair local bound is **pure real analysis**: two numbers `E₊, E₋`
(the exponents at the two atoms), two truncations `T₊, T₋`, a bound `δ` on each difference, and a
common bound `K ≤ 1`.

`RMF.abs_exp_sub_taylor_le` gives `|e^u - (1 + u + u²/2)| ≤ |u|³`, and swapping `E` for `T` inside
the quadratic costs `|E - T|·|1 + (E+T)/2| ≤ δ(1 + K)`.  Averaging the two atoms preserves the
bound.

Stated with no law and no `Finset` in sight, so it can be applied at `z = 1` and `z = -1` without
re-deriving anything — and so that the estimate is separated from the bookkeeping that feeds it. -/

/-- **The assembly's engine**: if `|E_±|, |T_±| ≤ K ≤ 1` and `|E_± - T_±| ≤ δ`, then
`|(e^{E₊} + e^{E₋})/2 - (1 + (T₊ + T₋)/2 + (T₊² + T₋²)/4)| ≤ K³ + δ(1 + K)`, with the truncation
taken at a different point from the exponent.  Law-free; it replaces the integrability-and-a.e.
half of `RMF.abs_integral_prod_localIntegrand_sub_le_of_moments`. -/
lemma abs_avg_exp_sub_taylor_le {Ep Em Tp Tm δ K : ℝ}
    (hEp : |Ep| ≤ K) (hEm : |Em| ≤ K) (hTp : |Tp| ≤ K) (hTm : |Tm| ≤ K)
    (hK : K ≤ 1) (hdp : |Ep - Tp| ≤ δ) (hdm : |Em - Tm| ≤ δ) :
    |(Real.exp Ep + Real.exp Em) / 2 - (1 + (Tp + Tm) / 2 + (Tp ^ 2 + Tm ^ 2) / 4)|
      ≤ K ^ 3 + δ * (1 + K) := by
  have hkey : ∀ E T : ℝ, |E| ≤ K → |T| ≤ K → |E - T| ≤ δ →
      |Real.exp E - (1 + T + T ^ 2 / 2)| ≤ K ^ 3 + δ * (1 + K) := by
    intro E T hE hT hd
    have h1 : |Real.exp E - (1 + E + E ^ 2 / 2)| ≤ |E| ^ 3 :=
      abs_exp_sub_taylor_le (le_trans hE hK)
    have h2 : |E| ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (abs_nonneg E) hE 3
    have hET : |(E + T) / 2| ≤ K := by
      rw [abs_div, abs_two]
      have h := abs_add_le E T
      linarith
    have h5 : |1 + (E + T) / 2| ≤ 1 + K := by
      have h := abs_add_le (1 : ℝ) ((E + T) / 2)
      rw [abs_one] at h
      linarith
    have h3 : (1 + E + E ^ 2 / 2) - (1 + T + T ^ 2 / 2) = (E - T) * (1 + (E + T) / 2) := by
      ring
    have h4 : |(1 + E + E ^ 2 / 2) - (1 + T + T ^ 2 / 2)| ≤ δ * (1 + K) := by
      rw [h3, abs_mul]
      exact mul_le_mul hd h5 (abs_nonneg _) (le_trans (abs_nonneg _) hd)
    have htri : |Real.exp E - (1 + T + T ^ 2 / 2)|
        ≤ |Real.exp E - (1 + E + E ^ 2 / 2)|
          + |(1 + E + E ^ 2 / 2) - (1 + T + T ^ 2 / 2)| := by
      have h := abs_add_le (Real.exp E - (1 + E + E ^ 2 / 2))
        ((1 + E + E ^ 2 / 2) - (1 + T + T ^ 2 / 2))
      have he : (Real.exp E - (1 + E + E ^ 2 / 2))
          + ((1 + E + E ^ 2 / 2) - (1 + T + T ^ 2 / 2))
          = Real.exp E - (1 + T + T ^ 2 / 2) := by ring
      rwa [he] at h
    linarith
  have hp := hkey Ep Tp hEp hTp hdp
  have hm := hkey Em Tm hEm hTm hdm
  have hid : (Real.exp Ep + Real.exp Em) / 2 - (1 + (Tp + Tm) / 2 + (Tp ^ 2 + Tm ^ 2) / 4)
      = ((Real.exp Ep - (1 + Tp + Tp ^ 2 / 2))
          + (Real.exp Em - (1 + Tm + Tm ^ 2 / 2))) / 2 := by
    ring
  rw [hid, abs_div, abs_two]
  have htri := abs_add_le (Real.exp Ep - (1 + Tp + Tp ^ 2 / 2))
    (Real.exp Em - (1 + Tm + Tm ^ 2 / 2))
  linarith

/-! ### Applying the engine

`RMF.integral_rademacherLaw_eq` applies directly to the norm form, giving `(g 1 + g (-1))/2`, and
`RMF.prod_norm_one_add_mul_rpow_eq_exp` rewrites each atom as an exponential; no closed form in
`(1 ± 2 Re w + ‖w‖²)^q` shape is needed.  The local bound is then `RMF.abs_avg_exp_sub_taylor_le`
transported along `RMF.pair_main_term_eq`, with a constant **linear in the moment size**. -/

/-- **The moment is the average of two exponentials.**  `RMF.integral_rademacherLaw_eq` evaluates
the two atoms and `RMF.prod_norm_one_add_mul_rpow_eq_exp` turns each product into an exponential. -/
lemma integral_prod_norm_one_add_mul_rpow_eq_avg_exp (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ)
    (hw : ∀ a ∈ A, ‖w a‖ < 1) :
    (∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw)
      = (Real.exp (2 * ∑ a ∈ A, q a * localLogAdd (w a) 1)
          + Real.exp (2 * ∑ a ∈ A, q a * localLogAdd (w a) (-1))) / 2 := by
  rw [integral_rademacherLaw_eq,
    prod_norm_one_add_mul_rpow_eq_exp A q w (by simp : ‖(1 : ℂ)‖ = 1) hw,
    prod_norm_one_add_mul_rpow_eq_exp A q w (by simp : ‖(-1 : ℂ)‖ = 1) hw, smul_eq_mul]
  ring

/-- **The local bound with a constant linear in the moment size.**  Given a common bound `K ≤ 1` on
the exponent and on the truncation on the circle, and a bound `δ` on their difference, the moment
is within `K³ + δ(1 + K)` of the phase-sensitive main term plus `V²/2`, `V = ∑_a q_a Re(w_a²)`.
The constant does not grow with the exponents: at `RMF.pairWeight`, `K` and `δ` are
`2(l₁/2 + l₂d/2)θ/(1-θ)` and `2Mθ³/(1-θ)`. -/
theorem abs_integral_prod_sub_main_term_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {δ K : ℝ}
    (hw : ∀ a ∈ A, ‖w a‖ < 1) (hK : K ≤ 1)
    (hE : ∀ z : ℂ, ‖z‖ = 1 → |2 * ∑ a ∈ A, q a * localLogAdd (w a) z| ≤ K)
    (hT : ∀ z : ℂ, ‖z‖ = 1 → |taylorExponent A q (fun a => -w a) z| ≤ K)
    (hd : ∀ z : ℂ, ‖z‖ = 1 → |(2 * ∑ a ∈ A, q a * localLogAdd (w a) z)
        - -taylorExponent A q (fun a => -w a) z| ≤ δ) :
    |(∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw)
        - ((1 + (∑ a ∈ A, q a * ‖w a‖ ^ 2) - 2 * (∑ a ∈ A, q a * (w a).re ^ 2)
              + 2 * (∑ a ∈ A, q a * (w a).re) ^ 2)
            + (∑ a ∈ A, q a * (w a ^ 2).re) ^ 2 / 2)|
      ≤ K ^ 3 + δ * (1 + K) := by
  have h1 : ‖(1 : ℂ)‖ = 1 := by simp
  have hm1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have h := abs_avg_exp_sub_taylor_le
    (Ep := 2 * ∑ a ∈ A, q a * localLogAdd (w a) 1)
    (Em := 2 * ∑ a ∈ A, q a * localLogAdd (w a) (-1))
    (Tp := -taylorExponent A q (fun a => -w a) 1)
    (Tm := -taylorExponent A q (fun a => -w a) (-1))
    (hE 1 h1) (hE (-1) hm1)
    (by rw [abs_neg]; exact hT 1 h1) (by rw [abs_neg]; exact hT (-1) hm1)
    hK (hd 1 h1) (hd (-1) hm1)
  rw [pair_main_term_eq] at h
  rw [integral_prod_norm_one_add_mul_rpow_eq_avg_exp A q w hw]
  exact h

/-! ### The `pairWeight` inputs

`RMF.abs_integral_prod_sub_main_term_le` takes `K`, `δ` and the order-four term `V` as inputs and
asks nothing about the weights.  Instantiating it at `RMF.pairWeight` needs three bounds beyond the
exponent bounds above, all from the law-free `RMF.norm_sum_pairWeight_pow_le`.

`V = ∑_a q_a Re(w_a²)` is a sum of *real parts*, while the moment bound is on `‖∑_a q_a w_a²‖`, a
norm of a *complex sum*.  `Re` is additive and real-linear, so
`∑_a q_a Re(w_a²) = Re(∑_a q_a w_a²)` (`RMF.sum_re_eq_re_sum`) and `Complex.abs_re_le_norm`
finishes. -/

/-- A real-weighted sum of real parts is the real part of the complex-weighted sum. -/
lemma sum_re_eq_re_sum (A : Finset ι) (q : ι → ℝ) (v : ι → ℂ) :
    (∑ a ∈ A, q a * (v a).re) = (∑ a ∈ A, (q a : ℂ) * v a).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The order-four term at `RMF.pairWeight`.**  `|V| ≤ 2M t²` with `M = l₁/2 + l₂d/2`, from the
moment bound at `k = 2` through `RMF.sum_re_eq_re_sum`. -/
lemma abs_sum_pairWeight_re_sq_le {l₁ l₂ t d : ℝ} {w : Fin 3 → ℂ} (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (h0 : ‖w 0‖ ≤ t) (h1 : ‖w 1‖ ≤ t) (h2 : ‖w 2‖ ≤ t)
    (h12 : ‖w 1 - w 2‖ ≤ t * d) :
    |∑ a, pairWeight l₁ l₂ a * (w a ^ 2).re| ≤ (l₁ / 2 + l₂ / 2 * d) * 2 * t ^ 2 := by
  rw [sum_re_eq_re_sum]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  have h := norm_sum_pairWeight_pow_le hl₁ hl₂ h0 h1 h2 h12 (k := 2) (by norm_num)
  push_cast at h
  exact h

/-- **The truncation at `RMF.pairWeight`.**  `|T| ≤ 2Mt + 2Mt²`, from the law-free
`RMF.abs_taylorExponent_le_moments` and the moment bound at `k = 1, 2`.

Stated at the reflected weights `-w`, which is where
`RMF.abs_integral_prod_sub_main_term_le` reads the truncation; reflection changes neither the
moduli nor the chord, so the moment bound applies unchanged. -/
lemma abs_taylorExponent_pairWeight_neg_le {l₁ l₂ t d : ℝ} {w : Fin 3 → ℂ} {z : ℂ}
    (hz : ‖z‖ = 1) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (h0 : ‖w 0‖ ≤ t) (h1 : ‖w 1‖ ≤ t)
    (h2 : ‖w 2‖ ≤ t) (h12 : ‖w 1 - w 2‖ ≤ t * d) :
    |taylorExponent Finset.univ (pairWeight l₁ l₂) (fun a => -w a) z|
      ≤ 2 * ((l₁ / 2 + l₂ / 2 * d) * t) + (l₁ / 2 + l₂ / 2 * d) * 2 * t ^ 2 := by
  refine le_trans (abs_taylorExponent_le_moments hz) ?_
  have hn : ∀ a : Fin 3, ‖(-w a)‖ = ‖w a‖ := fun a => norm_neg _
  have hd : ‖(-w 1) - (-w 2)‖ ≤ t * d := by
    rw [neg_sub_neg, norm_sub_rev]
    exact h12
  have hk1 := norm_sum_pairWeight_pow_le (w := fun a => -w a) hl₁ hl₂
    (by rw [hn]; exact h0) (by rw [hn]; exact h1) (by rw [hn]; exact h2) hd (k := 1) le_rfl
  have hk2 := norm_sum_pairWeight_pow_le (w := fun a => -w a) hl₁ hl₂
    (by rw [hn]; exact h0) (by rw [hn]; exact h1) (by rw [hn]; exact h2) hd (k := 2)
    (by norm_num)
  push_cast at hk1 hk2
  simp only [pow_one] at hk1
  linarith

/-! ### The pair local bound, assembled

Everything is fed into `RMF.abs_integral_prod_sub_main_term_le` at `RMF.pairWeight`, with
`M = l₁/2 + l₂d/2`.  **One `K` serves both bounds**: the exponent is bounded by `2Mθ/(1-θ)`
(`RMF.abs_two_mul_sum_pairWeight_localLogAdd_le`) and the truncation by `2Mθ(1+θ)`
(`RMF.abs_taylorExponent_pairWeight_neg_le`), and `θ(1+θ) ≤ θ/(1-θ)` for every `θ < 1`
(`RMF.taylor_crude_le_exponent_crude`).  `δ = 2Mθ³/(1-θ)` comes from
`RMF.abs_two_mul_sum_localLogAdd_sub_taylorExponent_le_of_moments`, and the order-four term `V²/2`
is paid for by `RMF.abs_sum_pairWeight_re_sq_le`.

The smallness hypothesis `Mθ ≤ (1-θ₀)/8` is the Steinhaus proof's own
(`RMF.exists_abs_log_local_pair_le`, via `d₀ = min((1-θ₀)/8, 1/(4(Cf+1)))`); it gives `K ≤ 1/4`, as
the engine's `K ≤ 1` needs, and `RMF.exists_abs_log_local_pair_rademacherLaw` discharges it.  The
three arithmetic steps are separate lemmas because the tactics time out in the assembled context. -/

/-- **`2Mθ + 2Mθ² ≤ 2Mθ/(1-θ)` for every `θ < 1`**, so one `K` bounds both the exponent and its
truncation in `RMF.abs_integral_prod_sub_main_term_le`; it reduces to `1 - θ² ≤ 1`. -/
lemma taylor_crude_le_exponent_crude {M θ : ℝ} (hM0 : 0 ≤ M) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    2 * (M * θ) + M * 2 * θ ^ 2 ≤ 2 * M * (θ / (1 - θ)) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  rw [show 2 * M * (θ / (1 - θ)) = 2 * M * θ / (1 - θ) by ring, le_div_iff₀ h1θ]
  nlinarith [mul_nonneg (mul_nonneg hM0 hθ0) (mul_nonneg hθ0 hθ0)]

/-- **The smallness hypothesis gives `K ≤ 1/4`.**  `Mθ ≤ (1-θ₀)/8` is the Steinhaus proof's own
hypothesis, carried across; the engine needs only `K ≤ 1`. -/
lemma two_mul_div_one_sub_le_of_small {M θ θ₀ : ℝ} (hM0 : 0 ≤ M) (hθ0 : 0 ≤ θ)
    (hθθ₀ : θ ≤ θ₀) (hθ₀ : θ₀ < 1) (hsmall : M * θ ≤ (1 - θ₀) / 8) :
    2 * M * (θ / (1 - θ)) ≤ 1 / 4 := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  have hmono : θ / (1 - θ) ≤ θ / (1 - θ₀) := by
    rw [div_le_div_iff₀ h1θ h1θ₀]
    nlinarith
  have ha : 2 * M * (θ / (1 - θ)) ≤ 2 * M * (θ / (1 - θ₀)) :=
    mul_le_mul_of_nonneg_left hmono (by linarith)
  have hb : 2 * M * (θ / (1 - θ₀)) = 2 * (M * θ) / (1 - θ₀) := by ring
  rw [hb] at ha
  have hc : 2 * (M * θ) / (1 - θ₀) ≤ 1 / 4 := by
    rw [div_le_iff₀ h1θ₀]
    linarith
  linarith

/-- **The absorption.**  `K³ + δ(1 + K) + V²/2` fits inside `C((1 + M)θ)³` with
`C = 8/(1-θ₀)³ + 4/(1-θ₀) + 2`, a constant depending on `θ₀` alone.

Separated from `RMF.abs_integral_prod_pairWeight_sub_main_term_le` because in the assembled
context `nlinarith` and `field_simp` exhaust the heartbeat limit. -/
lemma cube_absorb {M θ θ₀ V : ℝ} (hM0 : 0 ≤ M) (hθ0 : 0 ≤ θ) (hθθ₀ : θ ≤ θ₀) (hθ₀ : θ₀ < 1)
    (hV : |V| ≤ M * 2 * θ ^ 2) (hsmall : M * θ ≤ (1 - θ₀) / 8) :
    (2 * M * (θ / (1 - θ))) ^ 3
        + 2 * (M * θ ^ 3 / (1 - θ)) * (1 + 2 * M * (θ / (1 - θ))) + V ^ 2 / 2
      ≤ (8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2) * ((1 + M) * θ) ^ 3 := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  have hinv : (0 : ℝ) ≤ (1 - θ₀)⁻¹ := by positivity
  have hθ30 : (0 : ℝ) ≤ θ ^ 3 := pow_nonneg hθ0 3
  have hK4 : 2 * M * (θ / (1 - θ)) ≤ 1 / 4 :=
    two_mul_div_one_sub_le_of_small hM0 hθ0 hθθ₀ hθ₀ hsmall
  have hK0 : (0 : ℝ) ≤ 2 * M * (θ / (1 - θ)) := by positivity
  have hMcube : M ≤ (1 + M) ^ 3 := by nlinarith [mul_nonneg (mul_nonneg hM0 hM0) hM0, sq_nonneg M]
  have hMsq : M ^ 2 ≤ (1 + M) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hM0 hM0) hM0, sq_nonneg M]
  have hmono : θ / (1 - θ) ≤ θ / (1 - θ₀) := by
    rw [div_le_div_iff₀ h1θ h1θ₀]
    nlinarith
  -- the cube
  have hcube : (2 * M * (θ / (1 - θ))) ^ 3 ≤ 8 / (1 - θ₀) ^ 3 * ((1 + M) * θ) ^ 3 := by
    have hstep : 2 * M * (θ / (1 - θ)) ≤ 2 * (1 + M) * θ / (1 - θ₀) := by
      have ha : 2 * M * (θ / (1 - θ)) ≤ 2 * M * (θ / (1 - θ₀)) :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
      have hb : 2 * M * (θ / (1 - θ₀)) = 2 * M * θ * (1 - θ₀)⁻¹ := by ring
      have hc : 2 * (1 + M) * θ / (1 - θ₀) = 2 * (1 + M) * θ * (1 - θ₀)⁻¹ := by ring
      have hd : 2 * M * θ ≤ 2 * (1 + M) * θ := by nlinarith
      have he := mul_le_mul_of_nonneg_right hd hinv
      rw [hb] at ha
      rw [hc]
      linarith
    have h1 := pow_le_pow_left₀ hK0 hstep 3
    have hne : (1 - θ₀) ≠ 0 := ne_of_gt h1θ₀
    have h2 : (2 * (1 + M) * θ / (1 - θ₀)) ^ 3 = 8 / (1 - θ₀) ^ 3 * ((1 + M) * θ) ^ 3 := by
      field_simp
      ring
    rw [h2] at h1
    exact h1
  -- the difference term
  have hδ : 2 * (M * θ ^ 3 / (1 - θ)) * (1 + 2 * M * (θ / (1 - θ)))
      ≤ 4 / (1 - θ₀) * ((1 + M) * θ) ^ 3 := by
    have hd0 : (0 : ℝ) ≤ 2 * (M * θ ^ 3 / (1 - θ)) := by positivity
    have hd1 : M * θ ^ 3 / (1 - θ) ≤ M * θ ^ 3 * (1 - θ₀)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hmono (mul_nonneg hM0 (pow_nonneg hθ0 2))
      have he : M * θ ^ 2 * (θ / (1 - θ)) = M * θ ^ 3 / (1 - θ) := by ring
      have hf : M * θ ^ 2 * (θ / (1 - θ₀)) = M * θ ^ 3 * (1 - θ₀)⁻¹ := by ring
      rw [he, hf] at h
      exact h
    have hstep : 2 * (M * θ ^ 3 / (1 - θ)) * (1 + 2 * M * (θ / (1 - θ)))
        ≤ 2 * (M * θ ^ 3 * (1 - θ₀)⁻¹) * (5 / 4) := by nlinarith
    have hnum : 2 * (M * θ ^ 3) * (5 / 4) ≤ 4 * ((1 + M) ^ 3 * θ ^ 3) := by
      nlinarith [mul_le_mul_of_nonneg_right hMcube hθ30]
    have hfin := mul_le_mul_of_nonneg_right hnum hinv
    have hg : 2 * (M * θ ^ 3 * (1 - θ₀)⁻¹) * (5 / 4) = 2 * (M * θ ^ 3) * (5 / 4) * (1 - θ₀)⁻¹ := by
      ring
    have hh : 4 * ((1 + M) ^ 3 * θ ^ 3) * (1 - θ₀)⁻¹ = 4 / (1 - θ₀) * ((1 + M) * θ) ^ 3 := by
      ring
    rw [hg] at hstep
    rw [hh] at hfin
    linarith
  -- the order-four term
  have hVub : V ^ 2 / 2 ≤ 2 * ((1 + M) * θ) ^ 3 := by
    have hVsq : V ^ 2 ≤ (M * 2 * θ ^ 2) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg V) hV 2
      rwa [sq_abs] at h
    have h1 : (M * 2 * θ ^ 2) ^ 2 = 4 * (M ^ 2 * θ ^ 4) := by ring
    have h2 : θ ^ 4 ≤ θ ^ 3 := by nlinarith
    have h3 : M ^ 2 * θ ^ 4 ≤ (1 + M) ^ 3 * θ ^ 3 := by nlinarith [sq_nonneg M]
    have h4 : ((1 + M) * θ) ^ 3 = (1 + M) ^ 3 * θ ^ 3 := by ring
    rw [h1] at hVsq
    rw [h4]
    linarith
  have hsplit : (8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2) * ((1 + M) * θ) ^ 3
      = 8 / (1 - θ₀) ^ 3 * ((1 + M) * θ) ^ 3 + 4 / (1 - θ₀) * ((1 + M) * θ) ^ 3
        + 2 * ((1 + M) * θ) ^ 3 := by ring
  rw [hsplit]
  linarith

/-- **The pair local bound**: for `M = l₁/2 + l₂d/2` with `Mθ ≤ (1-θ₀)/8`, the Rademacher pair
moment is within `C((1 + M)θ)³` of the phase-sensitive main term, `C` depending only on `θ₀`.  The
counterpart of `RMF.abs_integral_prod_localIntegrand_sub_pair_le`; the unbounded `l₂` enters only
through `M`.  The smallness hypothesis is the Steinhaus proof's own, and is discharged in
`RMF.exists_abs_log_local_pair_rademacherLaw`. -/
theorem abs_integral_prod_pairWeight_sub_main_term_le {l₁ l₂ θ θ₀ d : ℝ} {w : Fin 3 → ℂ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hd : 0 ≤ d) (hθ0 : 0 ≤ θ) (hθθ₀ : θ ≤ θ₀) (hθ₀ : θ₀ < 1)
    (h0 : ‖w 0‖ ≤ θ) (h1 : ‖w 1‖ ≤ θ) (h2 : ‖w 2‖ ≤ θ) (h12 : ‖w 1 - w 2‖ ≤ θ * d)
    (hsmall : (l₁ / 2 + l₂ / 2 * d) * θ ≤ (1 - θ₀) / 8) :
    |(∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw)
        - (1 + (∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
            - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
            + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)|
      ≤ (8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2) * ((1 + (l₁ / 2 + l₂ / 2 * d)) * θ) ^ 3 := by
  set M : ℝ := l₁ / 2 + l₂ / 2 * d with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hθ1 : θ < 1 := lt_of_le_of_lt hθθ₀ hθ₀
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  set K : ℝ := 2 * M * (θ / (1 - θ)) with hKdef
  have hK4 : K ≤ 1 / 4 := two_mul_div_one_sub_le_of_small hM0 hθ0 hθθ₀ hθ₀ hsmall
  have hK1 : K ≤ 1 := by linarith
  have hwle : ∀ a ∈ (Finset.univ : Finset (Fin 3)), ‖w a‖ ≤ θ := by
    intro a _
    fin_cases a <;> assumption
  have hwlt : ∀ a ∈ (Finset.univ : Finset (Fin 3)), ‖w a‖ < 1 := by
    intro a ha
    have h := hwle a ha
    linarith
  have hEb : ∀ z : ℂ, ‖z‖ = 1 →
      |2 * ∑ a, pairWeight l₁ l₂ a * localLogAdd (w a) z| ≤ K := fun z hz =>
    abs_two_mul_sum_pairWeight_localLogAdd_le hz hl₁ hl₂ hθ1 h0 h1 h2 h12
  have hTb : ∀ z : ℂ, ‖z‖ = 1 →
      |taylorExponent Finset.univ (pairWeight l₁ l₂) (fun a => -w a) z| ≤ K := fun z hz =>
    le_trans (abs_taylorExponent_pairWeight_neg_le hz hl₁ hl₂ h0 h1 h2 h12)
      (taylor_crude_le_exponent_crude hM0 hθ0 hθ1)
  have hmom : ∀ k : ℕ, 3 ≤ k →
      ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ k‖ ≤ M * k * θ ^ k := fun k hk =>
    norm_sum_pairWeight_pow_le hl₁ hl₂ h0 h1 h2 h12 (by omega)
  set δ : ℝ := 2 * (M * θ ^ 3 / (1 - θ)) with hδdef
  have hδb : ∀ z : ℂ, ‖z‖ = 1 →
      |(2 * ∑ a, pairWeight l₁ l₂ a * localLogAdd (w a) z)
        - -taylorExponent Finset.univ (pairWeight l₁ l₂) (fun a => -w a) z| ≤ δ := fun z hz =>
    abs_two_mul_sum_localLogAdd_sub_taylorExponent_le_of_moments hz hwle hθ1 hθ0 hmom
  have h47 := abs_integral_prod_sub_main_term_le (A := (Finset.univ : Finset (Fin 3)))
    (q := pairWeight l₁ l₂) (w := w) hwlt hK1 hEb hTb hδb
  have hV := abs_sum_pairWeight_re_sq_le hl₁ hl₂ h0 h1 h2 h12
  have htri : |(∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw)
        - (1 + (∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
            - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
            + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)|
      ≤ (K ^ 3 + δ * (1 + K)) + (∑ a, pairWeight l₁ l₂ a * (w a ^ 2).re) ^ 2 / 2 := by
    set X := ∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw with hX
    set Mn := 1 + (∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
      - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
      + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2 with hMn
    set V := (∑ a, pairWeight l₁ l₂ a * (w a ^ 2).re) ^ 2 / 2 with hVd
    have hh := abs_add_le (X - (Mn + V)) V
    have he : (X - (Mn + V)) + V = X - Mn := by ring
    rw [he] at hh
    have hVabs : |V| = V := abs_of_nonneg (by rw [hVd]; positivity)
    rw [hVabs] at hh
    linarith [h47]
  refine le_trans htri ?_
  exact cube_absorb hM0 hθ0 hθθ₀ hθ₀ hV hsmall

/-! ### Towards the local pair bound: two inputs

The split between the crude and the fine regime lives inside `RMF.exists_abs_log_local_pair_le`,
not in the prime sum: that statement has no smallness hypothesis, and the threshold `d₀` is chosen
inside the proof so that one `C` covers both regimes.  The smallness hypothesis of
`RMF.abs_integral_prod_pairWeight_sub_main_term_le` is discharged the same way below, with the
law-free `RMF.abs_log_sub_poly_le` doing the log step.  Two inputs are needed for it.

**A crude log bound in terms of `M`.**  A constant `|A| Q 2log((1-θ)⁻¹)` with `Q = max_a |q_a|` is
useless for unbounded `l₂`.  The bound driven by the pointwise exponent is short for the Rademacher
law: the moment is the average of two exponentials, so an exponent bounded by `K` at both atoms
traps it between `e^{-K}` and `e^K`.

**The size of the main term**, which is phase-sensitive and has to be computed rather than taken
from the Steinhaus `‖∑ q_a w_a‖²`. -/

/-- **The crude log bound driven by the pointwise exponent.**

It takes whatever bound the caller can prove on the exponent — which at `RMF.pairWeight` is
`2Mθ/(1-θ)`, with `l₂` entering only through `M` — rather than a constant growing with
`max_a |q_a|`. -/
lemma abs_log_integral_prod_rademacherLaw_le_of_bound {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    {K : ℝ} (hw : ∀ a ∈ A, ‖w a‖ < 1)
    (hE : ∀ z : ℂ, ‖z‖ = 1 → |2 * ∑ a ∈ A, q a * localLogAdd (w a) z| ≤ K) :
    |Real.log (∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw)| ≤ K := by
  have h1 : ‖(1 : ℂ)‖ = 1 := by simp
  have hm1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have havg := integral_prod_norm_one_add_mul_rpow_eq_avg_exp A q w hw
  have hp := abs_le.1 (hE 1 h1)
  have hm := abs_le.1 (hE (-1) hm1)
  have hub : (∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw) ≤ Real.exp K := by
    rw [havg]
    have ha := Real.exp_le_exp.2 hp.2
    have hb := Real.exp_le_exp.2 hm.2
    linarith
  have hlb : Real.exp (-K)
      ≤ (∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw) := by
    rw [havg]
    have ha := Real.exp_le_exp.2 hp.1
    have hb := Real.exp_le_exp.2 hm.1
    linarith
  have hpos : (0 : ℝ) < ∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw :=
    lt_of_lt_of_le (Real.exp_pos _) hlb
  rw [abs_le]
  constructor
  · have h := Real.log_le_log (Real.exp_pos (-K)) hlb
    rwa [Real.log_exp] at h
  · have h := Real.log_le_log hpos hub
    rwa [Real.log_exp] at h

/-- A real-weighted `RMF.pairWeight` sum, bounded from the single point and the chord.  The
`l₂`-half is paid for by the chord `D`, never by `|g 1|` and `|g 2|` separately — which is the whole
reason the pair case is finer than the multi-point one. -/
lemma abs_sum_pairWeight_le {l₁ l₂ B D : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) {g : Fin 3 → ℝ}
    (h0 : |g 0| ≤ B) (h12 : |g 1 - g 2| ≤ D) :
    |∑ a, pairWeight l₁ l₂ a * g a| ≤ l₁ / 2 * B + l₂ / 2 * D := by
  rw [sum_pairWeight_mul]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ l₁ / 2),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ l₂ / 2)]
  have ha : l₁ / 2 * |g 0| ≤ l₁ / 2 * B := mul_le_mul_of_nonneg_left h0 (by linarith)
  have hb : l₂ / 2 * |g 1 - g 2| ≤ l₂ / 2 * D := mul_le_mul_of_nonneg_left h12 (by linarith)
  linarith

/-- The chord of a square, from the chord of the base: `|u² - v²| ≤ |u - v| (|u| + |v|)`. -/
lemma abs_sq_sub_sq_le {u v c b : ℝ} (hc : |u - v| ≤ c) (hu : |u| ≤ b) (hv : |v| ≤ b)
    (hb : 0 ≤ b) : |u ^ 2 - v ^ 2| ≤ c * (2 * b) := by
  have he : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
  rw [he, abs_mul]
  have hsum : |u + v| ≤ 2 * b := le_trans (abs_add_le u v) (by linarith)
  have hc0 : (0 : ℝ) ≤ |u - v| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ |u + v| := abs_nonneg _
  nlinarith

/-- The absorption for the main term's size, in a context holding only its own reals.  **No sign
hypotheses**: the difference is `t²(4M² + 6M + 6)`, and that quadratic has negative discriminant,
so the bound holds for every real `M` and `t`. -/
lemma pair_main_term_size_absorb (M t : ℝ) :
    2 * M * t ^ 2 + 2 * (2 * M * t ^ 2) + 2 * (M * t) ^ 2 ≤ 6 * ((1 + M) * t) ^ 2 := by
  nlinarith [sq_nonneg (M * t), sq_nonneg t, sq_nonneg (2 * M * t + 3 * t), sq_nonneg t]

/-- **The size of the Rademacher main term**: `|P| ≤ 6 x²` with `x = (1 + M)t`, for the
phase-sensitive `P = ∑ q_a‖w_a‖² - 2∑ q_a(Re w_a)² + 2(∑ q_a Re w_a)²` at `RMF.pairWeight`; this is
the `K = 6` that `RMF.abs_log_sub_poly_le` asks for.  The first two sums go through
`RMF.abs_sum_pairWeight_le` with the chord from `RMF.abs_sq_sub_sq_le`; the third is
`RMF.sum_re_eq_re_sum` followed by the `k = 1` moment. -/
lemma abs_pair_main_term_le {l₁ l₂ t d : ℝ} {w : Fin 3 → ℂ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hd : 0 ≤ d) (ht0 : 0 ≤ t) (h0 : ‖w 0‖ ≤ t) (h1 : ‖w 1‖ ≤ t) (h2 : ‖w 2‖ ≤ t)
    (h12 : ‖w 1 - w 2‖ ≤ t * d) :
    |(∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2) - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
        + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2|
      ≤ 6 * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 2 := by
  have htd0 : (0 : ℝ) ≤ t * d := mul_nonneg ht0 hd
  have hM0 : (0 : ℝ) ≤ l₁ / 2 + l₂ / 2 * d := by positivity
  -- the squared moduli
  have hn0 : |‖w 0‖ ^ 2| ≤ t ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hn12 : |‖w 1‖ ^ 2 - ‖w 2‖ ^ 2| ≤ t * d * (2 * t) :=
    abs_sq_sub_sq_le (le_trans (abs_norm_sub_norm_le _ _) h12)
      (by rw [abs_of_nonneg (norm_nonneg _)]; exact h1)
      (by rw [abs_of_nonneg (norm_nonneg _)]; exact h2) ht0
  have hA := abs_sum_pairWeight_le (l₁ := l₁) (l₂ := l₂)
    (g := fun a => ‖w a‖ ^ 2) hl₁ hl₂ hn0 hn12
  -- the squared real parts
  have hre : ∀ a : Fin 3, |(w a).re| ≤ ‖w a‖ := fun a => Complex.abs_re_le_norm _
  have hr0 : |(w 0).re ^ 2| ≤ t ^ 2 := by
    rw [abs_of_nonneg (by positivity), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans (hre 0) h0) 2
  have hrsub : |(w 1).re - (w 2).re| ≤ t * d := by
    have he : (w 1).re - (w 2).re = (w 1 - w 2).re := by simp
    rw [he]
    exact le_trans (Complex.abs_re_le_norm _) h12
  have hr12 : |(w 1).re ^ 2 - (w 2).re ^ 2| ≤ t * d * (2 * t) :=
    abs_sq_sub_sq_le hrsub (le_trans (hre 1) h1) (le_trans (hre 2) h2) ht0
  have hB := abs_sum_pairWeight_le (l₁ := l₁) (l₂ := l₂)
    (g := fun a => (w a).re ^ 2) hl₁ hl₂ hr0 hr12
  -- the linear moment
  have hC : |∑ a, pairWeight l₁ l₂ a * (w a).re| ≤ (l₁ / 2 + l₂ / 2 * d) * t := by
    rw [sum_re_eq_re_sum]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    simpa using norm_sum_pairWeight_pow_le hl₁ hl₂ h0 h1 h2 h12 (k := 1) le_rfl
  -- combine
  have hAle : |∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2|
      ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * t ^ 2 := by nlinarith [hA]
  have hBle : |∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2|
      ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * t ^ 2 := by nlinarith [hB]
  have hCsq : (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2
      ≤ ((l₁ / 2 + l₂ / 2 * d) * t) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hC 2
    rwa [sq_abs] at h
  have hCabs : |2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2|
      ≤ 2 * ((l₁ / 2 + l₂ / 2 * d) * t) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hBabs : |2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)|
      ≤ 2 * (2 * (l₁ / 2 + l₂ / 2 * d) * t ^ 2) := by
    rw [abs_mul, abs_two]
    linarith
  have htri := abs_add_le ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
      - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2))
    (2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)
  have htri2 := abs_sub (∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
    (2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2))
  refine le_trans htri ?_
  refine le_trans (add_le_add htri2 le_rfl) ?_
  refine le_trans (add_le_add (add_le_add hAle hBabs) hCabs) ?_
  exact pair_main_term_size_absorb _ _

/-- **`RMF.abs_integral_prod_pairWeight_sub_main_term_le` in the shape `RMF.abs_log_sub_poly_le`
consumes**, `|I - (1 + P)| ≤ C₀ x³`, with `P` the same phase-sensitive combination that
`RMF.abs_pair_main_term_le` bounds by `6x²`.  A `ring` step, stated so that the two line up on the
same `P`. -/
lemma abs_integral_prod_pairWeight_sub_one_add_le {l₁ l₂ θ θ₀ d : ℝ} {w : Fin 3 → ℂ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hd : 0 ≤ d) (hθ0 : 0 ≤ θ) (hθθ₀ : θ ≤ θ₀) (hθ₀ : θ₀ < 1)
    (h0 : ‖w 0‖ ≤ θ) (h1 : ‖w 1‖ ≤ θ) (h2 : ‖w 2‖ ≤ θ) (h12 : ‖w 1 - w 2‖ ≤ θ * d)
    (hsmall : (l₁ / 2 + l₂ / 2 * d) * θ ≤ (1 - θ₀) / 8) :
    |(∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw)
        - (1 + ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
            - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
            + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2))|
      ≤ (8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2) * ((1 + (l₁ / 2 + l₂ / 2 * d)) * θ) ^ 3 := by
  have h := abs_integral_prod_pairWeight_sub_main_term_le hl₁ hl₂ hd hθ0 hθθ₀ hθ₀ h0 h1 h2 h12
    hsmall
  have he : (1 + (∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
      - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
      + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)
      = 1 + ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
          - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
          + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2) := by ring
  rwa [he] at h

/-! ### The local pair bound, with the smallness discharged

Here the smallness hypothesis of `RMF.abs_integral_prod_pairWeight_sub_main_term_le` is discharged,
in the shape of `RMF.exists_abs_log_local_pair_le`: choose a threshold `d₀`, use the fine bound
below it and the crude one above, and let the constant absorb both.  `RMF.abs_log_sub_poly_le` takes
the `K` in `|P| ≤ K x²` as a parameter, and the Rademacher main term has `K = 6`
(`RMF.abs_pair_main_term_le`) where the Steinhaus one has `K = 1`; so the final constant is
`2(6 + Cf)² + Cf + Ctail`, and `Ctail` carries `6/d₀` rather than `1/d₀`.

`d₀` itself is unchanged: with `K = 6` the fine regime gives `|I - 1| ≤ (25/4)x²` where Steinhaus
gets `(5/4)x²`, and `x ≤ d₀ ≤ (1 - θ₀)/8 ≤ 1/8` still gives `25/256 < 1/2`.  The arithmetic is in
three standalone lemmas, because it times out inline. -/

/-- The crude log bound, re-expressed at the fixed abscissa `θ₀` and in terms of `x`. -/
lemma crude_le_of_le_theta {M t θ₀ x : ℝ} (hM0 : 0 ≤ M) (ht0 : 0 ≤ t) (htθ : t ≤ θ₀)
    (hθ₀ : θ₀ < 1) (hMtx : M * t ≤ x) :
    2 * M * (t / (1 - t)) ≤ 2 * x / (1 - θ₀) := by
  have ht1 : t < 1 := lt_of_le_of_lt htθ hθ₀
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  have hmono : t / (1 - t) ≤ t / (1 - θ₀) := by
    rw [div_le_div_iff₀ h1t h1θ₀]
    nlinarith
  have ha : 2 * M * (t / (1 - t)) ≤ 2 * M * (t / (1 - θ₀)) :=
    mul_le_mul_of_nonneg_left hmono (by linarith)
  have hb : 2 * M * (t / (1 - θ₀)) = 2 * (M * t) / (1 - θ₀) := by ring
  have hc : 2 * (M * t) / (1 - θ₀) ≤ 2 * x / (1 - θ₀) := by
    rw [div_le_div_iff₀ h1θ₀ h1θ₀]
    nlinarith
  rw [hb] at ha
  linarith

/-- **The fine regime keeps the moment within `1/2` of one**, which is what
`RMF.abs_log_sub_poly_le` needs before it may take a logarithm.

With `K = 6` this gives `(25/4)x²` where the Steinhaus `K = 1` gives `(5/4)x²`; `x ≤ d₀ ≤ 1/8`
still clears `1/2`, since `25/256 < 1/2`. -/
lemma abs_sub_one_le_half_of_fine {I P x Cf d₀ : ℝ} (hCf0 : 0 ≤ Cf) (hx0 : 0 ≤ x)
    (hxd : x ≤ d₀) (hd₀ : d₀ ≤ 1 / 8) (hCd : Cf * d₀ ≤ 1 / 4)
    (hIP : |I - (1 + P)| ≤ Cf * x ^ 3) (hP : |P| ≤ 6 * x ^ 2) :
    |I - 1| ≤ 1 / 2 := by
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have htri : |I - 1| ≤ Cf * x ^ 3 + 6 * x ^ 2 := by
    have he : I - 1 = (I - (1 + P)) + P := by ring
    rw [he]
    exact le_trans (abs_add_le _ _) (add_le_add hIP hP)
  have hcube : Cf * x ^ 3 ≤ 1 / 4 * x ^ 2 := by
    have h1 : Cf * x ^ 3 = Cf * x * x ^ 2 := by ring
    have h2 : Cf * x ≤ Cf * d₀ := mul_le_mul_of_nonneg_left hxd hCf0
    rw [h1]
    exact mul_le_mul_of_nonneg_right (le_trans h2 hCd) hx2
  have hxle : x ≤ 1 / 8 := le_trans hxd hd₀
  have hx2le : x ^ 2 ≤ 1 / 64 := by nlinarith
  linarith

/-- **The crude regime**: past the threshold, `x³` dominates both `x` and `x²`. -/
lemma crude_dominate {x d₀ θ₀ : ℝ} (hd₀0 : 0 < d₀) (hbig : d₀ < x) (hθ₀ : θ₀ < 1) :
    2 * x / (1 - θ₀) + 6 * x ^ 2 ≤ (2 / ((1 - θ₀) * d₀ ^ 2) + 6 / d₀) * x ^ 3 := by
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  have hx0 : (0 : ℝ) < x := lt_trans hd₀0 hbig
  have hxx : d₀ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hd₀0.le hbig.le 2
  have hA : 2 * x / (1 - θ₀) ≤ 2 / ((1 - θ₀) * d₀ ^ 2) * x ^ 3 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h1θ₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hxx
      (by positivity : (0 : ℝ) ≤ 2 * x * (1 - θ₀))]
  have hB : 6 * x ^ 2 ≤ 6 / d₀ * x ^ 3 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd₀0]
    nlinarith [sq_nonneg x]
  have hsplit : (2 / ((1 - θ₀) * d₀ ^ 2) + 6 / d₀) * x ^ 3
      = 2 / ((1 - θ₀) * d₀ ^ 2) * x ^ 3 + 6 / d₀ * x ^ 3 := by ring
  rw [hsplit]
  linarith

/-- **The local pair bound, uniform over the whole range `t ≤ θ₀`**: the log of the Rademacher pair
moment is its phase-sensitive main term up to `C((1 + M)t)³`, `M = l₁/2 + l₂d/2`, with `C`
depending only on `θ₀` and no smallness hypothesis.  The counterpart of
`RMF.exists_abs_log_local_pair_le`; the main term is not the Steinhaus `‖∑ q_a w_a‖²`, because the
Rademacher law is not rotation-invariant. -/
theorem exists_abs_log_local_pair_rademacherLaw {θ₀ : ℝ} (hθ₀0 : 0 ≤ θ₀) (hθ₀ : θ₀ < 1) :
    ∃ C > 0, ∀ (l₁ l₂ t d : ℝ) (w : Fin 3 → ℂ), 0 ≤ l₁ → 0 ≤ l₂ → 0 ≤ d → 0 ≤ t → t ≤ θ₀ →
      (∀ a, ‖w a‖ ≤ t) → ‖w 1 - w 2‖ ≤ t * d →
        |Real.log (∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw)
            - ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
                - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
                + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)|
          ≤ C * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 := by
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = 8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2 := ⟨_, rfl⟩
  have hCf0 : (0 : ℝ) < Cf := by rw [hCfdef]; positivity
  obtain ⟨d₀, hd₀def⟩ : ∃ d₀ : ℝ, d₀ = min ((1 - θ₀) / 8) (1 / (4 * (Cf + 1))) := ⟨_, rfl⟩
  have hd₀0 : (0 : ℝ) < d₀ := by
    rw [hd₀def]
    exact lt_min (by positivity) (by positivity)
  have hd₀8 : d₀ ≤ (1 - θ₀) / 8 := by rw [hd₀def]; exact min_le_left _ _
  have hd₀le : d₀ ≤ 1 / 8 := le_trans hd₀8 (by linarith)
  have hCd₀ : Cf * d₀ ≤ 1 / 4 := by
    have hd₀C : d₀ ≤ 1 / (4 * (Cf + 1)) := by rw [hd₀def]; exact min_le_right _ _
    have h1 : Cf * d₀ ≤ Cf * (1 / (4 * (Cf + 1))) := mul_le_mul_of_nonneg_left hd₀C hCf0.le
    have h2 : Cf * (1 / (4 * (Cf + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  obtain ⟨Ctail, hCtail⟩ : ∃ Ctail : ℝ, Ctail = 2 / ((1 - θ₀) * d₀ ^ 2) + 6 / d₀ := ⟨_, rfl⟩
  have hCtail0 : (0 : ℝ) ≤ Ctail := by rw [hCtail]; positivity
  refine ⟨2 * (6 + Cf) ^ 2 + Cf + Ctail, by positivity, ?_⟩
  intro l₁ l₂ t d w hl₁ hl₂ hd0 ht0 htθ hw h12
  have ht1 : t < 1 := lt_of_le_of_lt htθ hθ₀
  have hM0 : (0 : ℝ) ≤ l₁ / 2 + l₂ / 2 * d := by positivity
  have hx0 : (0 : ℝ) ≤ (1 + (l₁ / 2 + l₂ / 2 * d)) * t := by positivity
  have hMtx : (l₁ / 2 + l₂ / 2 * d) * t ≤ (1 + (l₁ / 2 + l₂ / 2 * d)) * t := by nlinarith
  have hwlt : ∀ a ∈ (Finset.univ : Finset (Fin 3)), ‖w a‖ < 1 := fun a _ =>
    lt_of_le_of_lt (hw a) ht1
  have hcrude0 : |Real.log (∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂rademacherLaw)| ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * (t / (1 - t)) :=
    abs_log_integral_prod_rademacherLaw_le_of_bound hwlt fun z hz =>
      abs_two_mul_sum_pairWeight_localLogAdd_le hz hl₁ hl₂ ht1 (hw 0) (hw 1) (hw 2) h12
  have hP := abs_pair_main_term_le hl₁ hl₂ hd0 ht0 (hw 0) (hw 1) (hw 2) h12
  rcases le_or_gt ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) d₀ with hfine | hbig
  · have hsmall : (l₁ / 2 + l₂ / 2 * d) * t ≤ (1 - θ₀) / 8 :=
      le_trans hMtx (le_trans hfine hd₀8)
    have hIP := abs_integral_prod_pairWeight_sub_one_add_le hl₁ hl₂ hd0 ht0 htθ hθ₀
      (hw 0) (hw 1) (hw 2) h12 hsmall
    rw [← hCfdef] at hIP
    have hhalf := abs_sub_one_le_half_of_fine hCf0.le hx0 hfine hd₀le hCd₀ hIP hP
    have hx1 : (1 + (l₁ / 2 + l₂ / 2 * d)) * t ≤ 1 := by
      linarith [le_trans hfine hd₀le]
    refine le_trans (abs_log_sub_poly_le hx0 hx1 hCf0.le hIP hP hhalf) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hsplit := abs_sub (Real.log (∫ z, ∏ a,
      ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw))
      ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
        - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
        + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)
    have hcr := crude_le_of_le_theta hM0 ht0 htθ hθ₀ hMtx
    have hdom := crude_dominate hd₀0 hbig hθ₀
    rw [← hCtail] at hdom
    have hfin : Ctail * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3
        ≤ (2 * (6 + Cf) ^ 2 + Cf + Ctail) * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (6 + Cf), hCf0.le]) (by positivity)
    linarith

/-! ### The pair expansion, summed over the primes

`RMF.exists_abs_log_local_pair_rademacherLaw` holds over the whole range `t ≤ θ₀`, so summing it
over the primes needs **no case analysis**: the per-prime error is `C₁((1 + M)p^{-σ})³`, and
the only work is trading the `ℓog p` inside `M` for a slightly larger abscissa.

*Positivity* is immediate: the Rademacher moment is an average of two exponentials
(`RMF.integral_prod_norm_one_add_mul_rpow_pos`), where the Steinhaus side routes through a
pointwise exponent bound.  *The modulus sum collapses*: all three points share `Re = σ`, so the
`l₂` terms of `∑_a q_a ‖w_a‖²` cancel, leaving `(l₁/2)p^{-2σ}`.  The other two sums see the phases
and do not collapse, so the statement keeps the general `∑_a` form. -/

/-- **Positivity of the Rademacher pair moment.**  Immediate from the two-atom form: the moment is
an average of two exponentials.  The Steinhaus counterpart needs a pointwise exponent bound. -/
lemma integral_prod_norm_one_add_mul_rpow_pos {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    (hw : ∀ a ∈ A, ‖w a‖ < 1) :
    0 < ∫ z, ∏ a ∈ A, ‖1 + z * w a‖ ^ (2 * q a) ∂rademacherLaw := by
  rw [integral_prod_norm_one_add_mul_rpow_eq_avg_exp A q w hw]
  positivity

/-- **Trading the `ℓog p` for a slightly larger abscissa**, in a context holding only its own reals.

The bracket `1 + l₁/2 + (l₂ D/2)ℓog p` carries a `ℓog p` that `RMF.sum_primesIco_rpow_le` cannot
see; `RMF.add_mul_log_mul_rpow_neg_le` trades it for `p^{-(σ-δ)}` at the cost of `1/δ`. -/
lemma pair_bracket_le_rpow {p : ℝ} (hp1 : 1 ≤ p) {l₁ l₂ Λ σ σ₁ δ K D : ℝ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hD : 0 ≤ D) (hδ0 : 0 < δ) (hK0 : 0 < K)
    (hl₁Λ : l₁ ≤ Λ) (hl₂Λ : l₂ * D ≤ Λ) (hK : 1 + Λ / 2 + Λ / 2 / δ ≤ K)
    (hσ₁ : σ₁ ≤ σ - δ) :
    (1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p))) * p ^ (-σ) ≤ K * p ^ (-σ₁) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hrw : (1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p)))
      = (1 + l₁ / 2) + l₂ * D / 2 * Real.log p := by ring
  rw [hrw]
  refine le_trans (add_mul_log_mul_rpow_neg_le hp1 (by linarith) (by positivity) hδ0) ?_
  have hcoeff : (1 + l₁ / 2) + l₂ * D / 2 / δ ≤ K := by
    have hb : l₂ * D / 2 / δ ≤ Λ / 2 / δ := by
      rw [div_le_div_iff_of_pos_right hδ0]
      linarith
    linarith
  have hexp : p ^ (-(σ - δ)) ≤ p ^ (-σ₁) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hpos1 : (0 : ℝ) ≤ p ^ (-(σ - δ)) := Real.rpow_nonneg hp0.le _
  calc ((1 + l₁ / 2) + l₂ * D / 2 / δ) * p ^ (-(σ - δ))
      ≤ K * p ^ (-(σ - δ)) := mul_le_mul_of_nonneg_right hcoeff hpos1
    _ ≤ K * p ^ (-σ₁) := mul_le_mul_of_nonneg_left hexp hK0.le

/-- `(p^{-σ₁})³ = p^{-3σ₁}`, so the cubed per-prime error is a single `rpow` the tail bound can
see. -/
lemma rpow_neg_cube_eq {p σ₁ : ℝ} (hp0 : 0 < p) : (p ^ (-σ₁)) ^ 3 = p ^ (-3 * σ₁) := by
  rw [← Real.rpow_natCast (p ^ (-σ₁)) 3, ← Real.rpow_mul hp0.le]
  congr 1
  push_cast
  ring

/-- **The pair expansion over the primes, at an arbitrary family of points.**  For `s : Fin 3 → ℂ`
with `Re s_a = σ ≥ σ₀`, `|Im s₁ - Im s₂| ≤ D`, `l₁ ≤ Λ` and `l₂ D ≤ Λ`, the log of the pair moment
over `p ∈ [y₀, y)` is its phase-sensitive main term up to a constant depending only on `σ₀` and
`Λ`.  `RMF.pairAbscissa` and `RMF.pairAbscissaAt` are instances; `D` bounds the gap rather than
equalling it, since the chaining takes `D` the width of one subinterval. -/
theorem exists_prime_sum_bound_pair_family_rademacherLaw {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀)
    (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (l₁ l₂ σ D : ℝ) (s : Fin 3 → ℂ) (y₀ y : ℕ), 0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ →
      0 ≤ D → (∀ a, (s a).re = σ) → |(s 1).im - (s 2).im| ≤ D → l₂ * D ≤ Λ →
        |Real.log (∏ p ∈ primesIco y₀ y, ∫ z, ∏ a,
              ‖1 + z * (p : ℂ) ^ (-s a)‖ ^ (2 * pairWeight l₁ l₂ a)
              ∂rademacherLaw)
            - ∑ p ∈ primesIco y₀ y,
                ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-s a)‖ ^ 2)
                  - 2 * (∑ a, pairWeight l₁ l₂ a * ((p : ℂ) ^ (-s a)).re ^ 2)
                  + 2 * (∑ a, pairWeight l₁ l₂ a * ((p : ℂ) ^ (-s a)).re) ^ 2)|
          ≤ C := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨C₁, hC₁, hloc⟩ := exists_abs_log_local_pair_rademacherLaw hθ0 hθ
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (σ₀ - 1 / 3) / 2 := ⟨_, rfl⟩
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; linarith
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = (σ₀ + 1 / 3) / 2 := ⟨_, rfl⟩
  have hσ₁1 : 1 / 3 < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁δ : σ₀ - δ = σ₁ := by rw [hδdef, hσ₁def]; ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + Λ / 2 + Λ / 2 / δ := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hT0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₁) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨C₁ * K ^ 3 * (∑' n : ℕ, (n : ℝ) ^ (-3 * σ₁)) + 1, by positivity, ?_⟩
  intro l₁ l₂ σ D s y₀ y hl₁ hl₂ hσ hl₁Λ hD0 hre him hl₂Λ
  have hnorm : ∀ p ∈ primesIco y₀ y, ∀ a : Fin 3,
      ‖((p : ℂ)) ^ (-s a)‖ = (p : ℝ) ^ (-σ) := by
    intro p hp a
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos,
      Complex.neg_re, hre a]
  have hle : ∀ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hincr : ∀ p ∈ primesIco y₀ y,
      ‖(p : ℂ) ^ (-s 1) - (p : ℂ) ^ (-s 2)‖
        ≤ (p : ℝ) ^ (-σ) * (D * Real.log p) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    have hrp : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h := norm_natCast_cpow_neg_sub_le hpp.pos
      (s₁ := s 1) (s₂ := s 2) (σ := σ)
      (hre 1) (hre 2)
    exact le_trans h (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right him hlogp) hrp)
  have hpos : ∀ p ∈ primesIco y₀ y, 0 < ∫ z, ∏ a,
      ‖1 + z * (p : ℂ) ^ (-s a)‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂rademacherLaw := by
    intro p hp
    refine integral_prod_norm_one_add_mul_rpow_pos fun a _ => ?_
    rw [hnorm p hp a]
    exact lt_of_le_of_lt (hle p hp) hθ
  have hterm : ∀ p ∈ primesIco y₀ y,
      |Real.log (∫ z, ∏ a,
            ‖1 + z * (p : ℂ) ^ (-s a)‖ ^ (2 * pairWeight l₁ l₂ a)
            ∂rademacherLaw)
          - ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-s a)‖ ^ 2)
              - 2 * (∑ a, pairWeight l₁ l₂ a
                  * ((p : ℂ) ^ (-s a)).re ^ 2)
              + 2 * (∑ a, pairWeight l₁ l₂ a
                  * ((p : ℂ) ^ (-s a)).re) ^ 2)|
        ≤ C₁ * K ^ 3 * (p : ℝ) ^ (-3 * σ₁) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hp1
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
    have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    have h := hloc l₁ l₂ ((p : ℝ) ^ (-σ)) (D * Real.log p)
      (fun a => (p : ℂ) ^ (-s a)) hl₁ hl₂ (mul_nonneg hD0 hlog0) ht0
      (hle p hp) (fun a => le_of_eq (hnorm p hp a)) (hincr p hp)
    refine le_trans h ?_
    have hxK : (1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p))) * (p : ℝ) ^ (-σ)
        ≤ K * (p : ℝ) ^ (-σ₁) :=
      pair_bracket_le_rpow hp1 hl₁ hl₂ hD0 hδ0 hK0 hl₁Λ hl₂Λ (le_of_eq hKdef.symm)
        (by rw [← hσ₁δ]; linarith)
    have hx0 : (0 : ℝ) ≤ (1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p)))
        * (p : ℝ) ^ (-σ) := by positivity
    have hcubed := pow_le_pow_left₀ hx0 hxK 3
    have hRHS : (K * (p : ℝ) ^ (-σ₁)) ^ 3 = K ^ 3 * (p : ℝ) ^ (-3 * σ₁) := by
      rw [mul_pow, rpow_neg_cube_eq hp0]
    calc C₁ * ((1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p))) * (p : ℝ) ^ (-σ)) ^ 3
        ≤ C₁ * (K * (p : ℝ) ^ (-σ₁)) ^ 3 := mul_le_mul_of_nonneg_left hcubed hC₁.le
      _ = C₁ * K ^ 3 * (p : ℝ) ^ (-3 * σ₁) := by rw [hRHS]; ring
  have hmain := abs_log_prod_sub_sum_le hpos hterm
  refine le_trans hmain ?_
  have hsum : ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * σ₁)
      ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₁) := sum_primesIco_rpow_le hσ₁1 le_rfl y₀ y
  have hC0 : (0 : ℝ) ≤ C₁ * K ^ 3 := by positivity
  nlinarith

/-! ### Integrability of the joint integrand

The Chernoff bound is a Markov inequality, so it needs the integrand integrable, and at a negative
exponent `‖F‖^{2q}` blows up where `‖F‖` is small.  The block product is finite, so the two-sided
bounds of `RMF/EulerProduct/Block.lean` give `∏(1-t) ≤ ‖F‖ ≤ ∏(1+t)` with `t = ‖p^{-s}‖`, where the
completely multiplicative side has `∏(1+t)⁻¹ ≤ ‖F‖ ≤ ∏(1-t)⁻¹`.  Since `(1+t)(1-t) ≤ 1`, the
squarefree upper bound still sits below `∏(1-t)⁻¹`, and `∏(1-t) = (∏(1-t)⁻¹)⁻¹`, so

    |log ‖F‖| ≤ log ∏(1 - ‖p^{-s}‖)⁻¹

holds for both laws, and every consumer sees the same bound. -/

/-- **The walk is bounded on both sides**, with the same bound as
`RMF.IsSteinhausRMF.ae_abs_log_norm_randomEulerProductIco_le`: from the two-sided product bounds
of `RMF/EulerProduct/Block.lean`, via `(1 + t)(1 - t) ≤ 1`. -/
lemma IsRademacherRMF.ae_abs_log_norm_randomEulerProductIco_le {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y₀ y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, |Real.log ‖randomEulerProductIco f y₀ y s ω‖|
      ≤ Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹) := by
  have hLpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖) := by
    refine Finset.prod_pos fun p hp => ?_
    have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    linarith
  have hinv : (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹)
      = (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖))⁻¹ := Finset.prod_inv_distrib _
  have hUpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
    rw [hinv]
    exact inv_pos.2 hLpos
  have hupper : (∏ p ∈ primesIco y₀ y, (1 + ‖(p : ℂ) ^ (-s)‖))
      ≤ ∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
    have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    have h0 : (0 : ℝ) ≤ ‖(p : ℂ) ^ (-s)‖ := norm_nonneg _
    rw [← one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ‖(p : ℂ) ^ (-s)‖)]
    nlinarith
  have hApos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 + ‖(p : ℂ) ^ (-s)‖) := by
    refine Finset.prod_pos fun p hp => ?_
    positivity
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y] with ω hω
  have hlo := le_norm_randomEulerProductIco_sqfree y₀ y hs hω
  have hup := norm_randomEulerProductIco_sqfree_le y₀ y s hω
  have hFpos : (0 : ℝ) < ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ y s ω‖ := lt_of_lt_of_le hLpos hlo
  rw [abs_le]
  constructor
  · have h1 := Real.log_le_log hLpos hlo
    have h2 : Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖))
        = -Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹) := by
      rw [hinv, Real.log_inv, neg_neg]
    rw [h2] at h1
    linarith
  · exact le_trans (Real.log_le_log hFpos hup) (Real.log_le_log hApos hupper)

/-- **The joint integrand is the exponential of a combination of the walks**, almost surely: the
proof of `RMF.IsSteinhausRMF.prod_norm_rpow_ae_eq`, with the non-vanishing
`RMF.IsRademacherRMF.ae_randomEulerProductIco_ne_zero`. -/
lemma IsRademacherRMF.prod_norm_rpow_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    (A : Finset ι) (q : ι → ℝ) (s : ι → ℂ) (y₀ y : ℕ) (hs : ∀ a ∈ A, 0 < (s a).re) :
    (fun ω => ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a))
      =ᵐ[μ] fun ω => Real.exp
        (∑ a ∈ A, 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) := by
  have hall : ∀ᵐ ω ∂μ, ∀ a ∈ A, randomEulerProductIco f y₀ y (s a) ω ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact hf.ae_randomEulerProductIco_ne_zero y₀ y (hs a ha)
  filter_upwards [hall] with ω hω
  exact prod_rpow_eq_exp_sum fun a ha => norm_pos_iff.2 (hω a ha)

/-- **The joint integrand is integrable**, at exponents of either sign.

The Rademacher counterpart of `RMF.IsSteinhausRMF.integrable_prod_norm_rpow`.  One difference:
`RMF.IsRademacherRMF.aemeasurable_randomEulerProductIco` needs no hypothesis on the abscissa, so
`hs` is used here only for the two-sided log bound. -/
lemma IsRademacherRMF.integrable_prod_norm_rpow {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    (A : Finset ι) (q : ι → ℝ) (s : ι → ℂ) (y₀ y : ℕ) {Q : ℝ}
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hQ0 : 0 ≤ Q) (hs : ∀ a ∈ A, 0 < (s a).re) :
    Integrable (fun ω => ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) μ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hmeas : AEStronglyMeasurable
      (fun ω => ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) μ := by
    refine AEStronglyMeasurable.congr ?_ (hf.prod_norm_rpow_ae_eq A q s y₀ y hs).symm
    have hsum : AEMeasurable
        (fun ω => ∑ a ∈ A, 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) μ := by
      have hone : ∀ a ∈ A, AEMeasurable
          (fun ω => 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) μ := by
        intro a _
        exact (Real.measurable_log.comp_aemeasurable
          ((hf.aemeasurable_randomEulerProductIco y₀ y (s a)).norm)).const_mul (2 * q a)
      have h := Finset.aemeasurable_sum (μ := μ) A hone
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp
    exact (Real.measurable_exp.comp_aemeasurable hsum).aestronglyMeasurable
  have hall : ∀ᵐ ω ∂μ, ∀ a ∈ A, |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖|
      ≤ Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact hf.ae_abs_log_norm_randomEulerProductIco_le y₀ y (hs a ha)
  refine (memLp_top_of_bound hmeas
    (Real.exp (2 * Q * ∑ a ∈ A,
      Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹))) ?_).integrable le_top
  filter_upwards [hall, hf.prod_norm_rpow_ae_eq A q s y₀ y hs] with ω h1 h2
  rw [Real.norm_eq_abs, h2, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  have hL := h1 a ha
  have hM0 : (0 : ℝ)
      ≤ Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) :=
    le_trans (abs_nonneg _) hL
  have hqa := hq a ha
  have h3 : q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖
      ≤ Q * Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) := by
    have h4 : q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖
        ≤ |q a| * |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖| := by
      calc q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖
          ≤ |q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖| := le_abs_self _
        _ = |q a| * |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖| := abs_mul _ _
    have h5 : |q a| * |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖|
        ≤ Q * Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) :=
      mul_le_mul hqa hL (abs_nonneg _) hQ0
    linarith
  linarith

/-! ### The pair abscissa at a general base

The Steinhaus chaining moves one Lemma B.2 estimate to every subinterval `[kρ, kρ+ρ)` by rotating,
which the Rademacher law does not permit.  The replacement is to carry the tilt base as a
parameter, as Harper does — his `c(t, t_j - t, p)` keeps the tilt height `t` and the evaluation
height `t_j` separate — and as `RMF.blockOffsetWeight` does one level down.  `RMF.pairAbscissa`
pins the base at `Im s = 0`; `RMF.pairAbscissaAt` frees it, and `RMF.local_poly_multi_eq`, stated
for a general family, gives its main term (`RMF.pair_local_poly_eq_at`).

**What the general base costs.**  With `A = l₁/2` and `c₀ = cos(h₀ log p)`, the terms of
`2(∑ q_a c_a)² - ∑ q_a cos(2t_a L)` carrying `h₀` alone are
`2A²c₀² - A(2c₀² - 1) = 2A(A - 1)c₀² + A`: this is `2A² - A = l₁²/2 - l₁/2` at `c₀ = 1`, and at most
`2A² + A` uniformly in `h₀`.  Only the sign of the linear term flips, in the harmless direction: a
larger coefficient on `∑p^{-2σ}` only weakens the Chernoff bound it feeds. -/

/-- **The pair abscissa at a general base height `h₀`.**  `RMF.pairAbscissa` is the case
`h₀ = 0`. -/
noncomputable def pairAbscissaAt (σ h₀ h₁ h₂ : ℝ) : Fin 3 → ℂ :=
  ![(σ : ℂ) + (h₀ : ℂ) * Complex.I, (σ : ℂ) + (h₁ : ℂ) * Complex.I,
    (σ : ℂ) + (h₂ : ℂ) * Complex.I]

lemma pairAbscissaAt_re (σ h₀ h₁ h₂ : ℝ) (a : Fin 3) :
    (pairAbscissaAt σ h₀ h₁ h₂ a).re = σ := by
  fin_cases a <;> simp [pairAbscissaAt]

lemma pairAbscissaAt_im_zero (σ h₀ h₁ h₂ : ℝ) :
    (pairAbscissaAt σ h₀ h₁ h₂ 0).im = h₀ := by
  simp [pairAbscissaAt]

lemma pairAbscissaAt_im_one (σ h₀ h₁ h₂ : ℝ) :
    (pairAbscissaAt σ h₀ h₁ h₂ 1).im = h₁ := by
  simp [pairAbscissaAt]

lemma pairAbscissaAt_im_two (σ h₀ h₁ h₂ : ℝ) :
    (pairAbscissaAt σ h₀ h₁ h₂ 2).im = h₂ := by
  simp [pairAbscissaAt]

/-- **The pair main term at a general base, in Harper's trigonometric shape.**

`RMF.local_poly_multi_eq` specialised to `RMF.pairWeight` at `RMF.pairAbscissaAt`.  The base height
`h₀` enters through `cos(h₀ℓog p)` and `cos(2h₀ℓog p)`, both `1` at `h₀ = 0`: this is Harper's
`(1 + cos(2tℓog p))` variance factor made visible. -/
lemma pair_local_poly_eq_at {p : ℕ} (hp : p.Prime) (l₁ l₂ σ h₀ h₁ h₂ : ℝ) :
    ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
        - 2 * (∑ a, pairWeight l₁ l₂ a
            * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
        + 2 * (∑ a, pairWeight l₁ l₂ a
            * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2)
      = (p : ℝ) ^ (-2 * σ)
        * (2 * (l₁ / 2 * Real.cos (h₀ * Real.log p)
              + l₂ / 2 * (Real.cos (h₁ * Real.log p) - Real.cos (h₂ * Real.log p))) ^ 2
            - (l₁ / 2 * Real.cos (2 * (h₀ * Real.log p))
                + l₂ / 2 * (Real.cos (2 * (h₁ * Real.log p))
                    - Real.cos (2 * (h₂ * Real.log p))))) := by
  rw [local_poly_multi_eq hp Finset.univ (pairWeight l₁ l₂) (pairAbscissaAt σ h₀ h₁ h₂)
    (fun a _ => pairAbscissaAt_re σ h₀ h₁ h₂ a)]
  congr 1
  rw [sum_pairWeight_mul, sum_pairWeight_mul, pairAbscissaAt_im_zero, pairAbscissaAt_im_one,
    pairAbscissaAt_im_two]

/-! ### The general-base pair bound

The bound that goes with `RMF.pair_local_poly_eq_at`, with the base free rather than pinned at
`Im s = 0`, where `cos(h₀ℓog p) = 1`.  The arithmetic is extracted first (`RMF.base_sq_absorb`,
`RMF.sq_le_two_mul_of_abs_le`, `RMF.pair_trig_at_le`), because inside the prime-indexed goal it
times out.

By the computation of the previous section, the `p^{-2σ}` coefficient becomes `l₁²/2 + l₁/2`
uniformly in `h₀`.  The sign flip is a real cost — at `c₀ = 0` the `h₀` terms are exactly
`A = l₁/2 > 0`, which `l₁²/2 - l₁/2` does not dominate for small `l₁` — but harmless, since a larger
coefficient on `∑p^{-2σ}` only weakens the Chernoff bound it feeds.  The `ℓog p` coefficient is
`2l₂ + l₁l₂ + l₂²`: the base enters the pair terms only through `|c₀| ≤ 1`. -/

/-- The base's contribution, absorbed.  `2A(A - 1)c₀² ≤ 2A²` for `A ≥ 0` and `c₀² ≤ 1`: the two
pieces are `2A²(c₀² - 1) ≤ 0` and `-2Ac₀² ≤ 0`.  Note the bound is **not** `2A² - 2A`; that is
what fails once `A < 1`. -/
lemma base_sq_absorb {A c : ℝ} (hA : 0 ≤ A) (hc : c ^ 2 ≤ 1) :
    2 * A * (A - 1) * c ^ 2 ≤ 2 * A ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hc), mul_nonneg hA (sq_nonneg c)]

/-- A square bounded by a single power of the chord.  Spending one factor of `|d| ≤ 2` and one of
`|d| ≤ T` keeps the `ℓog p` coefficient linear, which is what the prime sum needs. -/
lemma sq_le_two_mul_of_abs_le {d T : ℝ} (h2 : |d| ≤ 2) (hT : |d| ≤ T) : d ^ 2 ≤ 2 * T := by
  nlinarith [sq_abs d, abs_nonneg d, mul_le_mul_of_nonneg_right h2 (abs_nonneg d)]

/-- **The general-base trigonometric bound, as pure arithmetic.**  `c₀` is the base cosine, `d` the
cosine chord, `E` the double-angle chord, `T` the chord bound.

The base is handled by `|c₀| ≤ 1` alone — **no smallness hypothesis on `h₀` is needed**, which is
what makes the chaining able to apply this at every subinterval. -/
lemma pair_trig_at_le {A B c₀ d E T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc₀ : |c₀| ≤ 1)
    (hd2 : |d| ≤ 2) (hdT : |d| ≤ T) (hE : |E| ≤ 2 * T) (hT : 0 ≤ T) :
    2 * (A * c₀ + B * d) ^ 2 - (A * (2 * c₀ ^ 2 - 1) + B * E)
      ≤ 2 * A ^ 2 + A + (4 * B + 4 * A * B + 4 * B ^ 2) * T := by
  have hc₀sq : c₀ ^ 2 ≤ 1 := by
    have h := abs_le.1 hc₀
    nlinarith [h.1, h.2]
  have hcd : c₀ * d ≤ T := by
    have h : |c₀ * d| ≤ 1 * T := by
      rw [abs_mul]
      exact mul_le_mul hc₀ hdT (abs_nonneg d) zero_le_one
    rw [one_mul] at h
    exact le_trans (le_abs_self _) h
  have h1 : 2 * A * (A - 1) * c₀ ^ 2 ≤ 2 * A ^ 2 := base_sq_absorb hA hc₀sq
  have hAB : (0 : ℝ) ≤ 4 * A * B := mul_nonneg (mul_nonneg (by norm_num) hA) hB
  have h2 : 4 * A * B * (c₀ * d) ≤ 4 * A * B * T := mul_le_mul_of_nonneg_left hcd hAB
  have h3 : 2 * B ^ 2 * d ^ 2 ≤ 2 * B ^ 2 * (2 * T) :=
    mul_le_mul_of_nonneg_left (sq_le_two_mul_of_abs_le hd2 hdT) (by positivity)
  have h4 : B * -E ≤ B * (2 * T) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 hE).1]) hB
  nlinarith [h1, h2, h3, h4, mul_nonneg hB hT]

/-- **The main-term bound at one prime, at a general base.**  `RMF.pair_local_poly_eq_at` supplies
the identity, `RMF.pair_trig_at_le` the arithmetic.  The coefficient of `p^{-2σ}` is
`l₁²/2 + l₁/2` and that of `p^{-2σ}ℓog p` is `(2l₂ + l₁l₂ + l₂²)|h₁ - h₂|`, uniformly in `h₀`. -/
lemma pair_main_term_pairAbscissaAt_le {p : ℕ} (hp : p.Prime) {l₁ l₂ σ h₀ h₁ h₂ : ℝ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) :
    ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
        - 2 * (∑ a, pairWeight l₁ l₂ a
            * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
        + 2 * (∑ a, pairWeight l₁ l₂ a
            * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2)
      ≤ (l₁ ^ 2 / 2 + l₁ / 2) * (p : ℝ) ^ (-2 * σ)
        + (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * |h₁ - h₂|
          * ((p : ℝ) ^ (-2 * σ) * Real.log p) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hpR : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hp1
  have hlog0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hpow : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg hpR.le _
  have hT : (0 : ℝ) ≤ |h₁ - h₂| * Real.log (p : ℝ) := mul_nonneg (abs_nonneg _) hlog0
  have hd2 : |Real.cos (h₁ * Real.log (p : ℝ)) - Real.cos (h₂ * Real.log (p : ℝ))| ≤ 2 :=
    le_trans (abs_sub _ _) (by
      linarith [Real.abs_cos_le_one (h₁ * Real.log (p : ℝ)),
        Real.abs_cos_le_one (h₂ * Real.log (p : ℝ))])
  have hdT : |Real.cos (h₁ * Real.log (p : ℝ)) - Real.cos (h₂ * Real.log (p : ℝ))|
      ≤ |h₁ - h₂| * Real.log (p : ℝ) := by
    refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
    rw [show h₁ * Real.log (p : ℝ) - h₂ * Real.log (p : ℝ) = (h₁ - h₂) * Real.log (p : ℝ) by
      ring, abs_mul, abs_of_nonneg hlog0]
  have hE : |Real.cos (2 * (h₁ * Real.log (p : ℝ))) - Real.cos (2 * (h₂ * Real.log (p : ℝ)))|
      ≤ 2 * (|h₁ - h₂| * Real.log (p : ℝ)) := by
    refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
    rw [show 2 * (h₁ * Real.log (p : ℝ)) - 2 * (h₂ * Real.log (p : ℝ))
        = (h₁ - h₂) * (2 * Real.log (p : ℝ)) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.log (p : ℝ))]
    exact le_of_eq (by ring)
  rw [pair_local_poly_eq_at hp l₁ l₂ σ h₀ h₁ h₂, Real.cos_two_mul (h₀ * Real.log (p : ℝ))]
  have hkey := pair_trig_at_le (A := l₁ / 2) (B := l₂ / 2)
    (c₀ := Real.cos (h₀ * Real.log (p : ℝ)))
    (d := Real.cos (h₁ * Real.log (p : ℝ)) - Real.cos (h₂ * Real.log (p : ℝ)))
    (E := Real.cos (2 * (h₁ * Real.log (p : ℝ))) - Real.cos (2 * (h₂ * Real.log (p : ℝ))))
    (T := |h₁ - h₂| * Real.log (p : ℝ)) (by linarith) (by linarith)
    (Real.abs_cos_le_one _) hd2 hdT hE hT
  nlinarith [mul_le_mul_of_nonneg_left hkey hpow]

/-- **The main-term bound at a general base, summed over a block of primes**: over `p ∈ [y₀, y)`,
`∑_p main(p) ≤ (l₁²/2 + l₁/2)∑_p p^{-2σ} + (2l₂ + l₁l₂ + l₂²)|h₁ - h₂| ∑_p p^{-2σ}ℓog p`,
**uniformly in the base `h₀`**; unlike the Steinhaus law, the Rademacher law has no rotation
invariance to reduce a general base to `0`. -/
theorem sum_pair_main_term_pairAbscissaAt_le {l₁ l₂ σ h₀ h₁ h₂ : ℝ} (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (y₀ y : ℕ) :
    (∑ p ∈ primesIco y₀ y,
        ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
          - 2 * (∑ a, pairWeight l₁ l₂ a
              * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
          + 2 * (∑ a, pairWeight l₁ l₂ a
              * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2))
      ≤ (l₁ ^ 2 / 2 + l₁ / 2) * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
        + (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * |h₁ - h₂|
          * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) := by
  refine le_trans (Finset.sum_le_sum fun p hp =>
    pair_main_term_pairAbscissaAt_le (prime_of_mem_primesIco hp) hl₁ hl₂) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ### The joint moment at a general base

All three pieces are instances: the prime sum of
`RMF.exists_prime_sum_bound_pair_family_rademacherLaw`, which never sees the base; the gateway,
which asks only for `0 < σ`; and the assembly, with the bound
`RMF.sum_pair_main_term_pairAbscissaAt_le`. -/

/-- **The gateway at the pair abscissas, at a general base.**  The abscissa hypothesis amounts to
`0 < σ` alone, since all three share a real part (`RMF.pairAbscissaAt_re`) — the base is invisible
here. -/
theorem IsRademacherRMF.integral_prod_norm_randomEulerProductIco_rpow_pair_at {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ)
    (l₁ l₂ σ h₀ h₁ h₂ : ℝ) (hσ : 0 < σ) :
    (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y₁ (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ∏ a, ‖1 + z * (p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖
            ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw :=
  hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y₁ Finset.univ
    (fun a _ => by rw [pairAbscissaAt_re]; exact hσ)

/-- **The pair prime sum at a general base**, an instance of
`RMF.exists_prime_sum_bound_pair_family_rademacherLaw`. -/
theorem exists_pair_prime_sum_bound_at_rademacherLaw {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀)
    (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (l₁ l₂ σ h₀ h₁ h₂ : ℝ) (y₀ y : ℕ), 0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ →
      l₂ * |h₁ - h₂| ≤ Λ →
        |Real.log (∏ p ∈ primesIco y₀ y, ∫ z, ∏ a,
              ‖1 + z * (p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ (2 * pairWeight l₁ l₂ a)
              ∂rademacherLaw)
            - ∑ p ∈ primesIco y₀ y,
                ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
                  - 2 * (∑ a, pairWeight l₁ l₂ a
                      * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
                  + 2 * (∑ a, pairWeight l₁ l₂ a
                      * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2)|
          ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_prime_sum_bound_pair_family_rademacherLaw hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro l₁ l₂ σ h₀ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
  exact h l₁ l₂ σ (|h₁ - h₂|) (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hl₁ hl₂ hσ hl₁Λ
    (abs_nonneg _) (pairAbscissaAt_re σ h₀ h₁ h₂)
    (le_of_eq (by rw [pairAbscissaAt_im_one, pairAbscissaAt_im_two])) hl₂Λ

/-- **The pair joint moment at a general base**: Hamdan's Lemma B.1, Laplace half, with the base
height `h₀` free.  `l₂` is not bounded, only `l₂|h₁ - h₂|` is, and the bound is **uniform in
`h₀`**, which replaces the Steinhaus rotation.  The coefficients are `l₁²/2 + l₁/2` on
`∑_p p^{-2σ}` and `(2l₂ + l₁l₂ + l₂²)|h₁ - h₂|` on `∑_p p^{-2σ}ℓog p`. -/
theorem IsRademacherRMF.exists_log_joint_moment_pair_le_at {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (l₁ l₂ σ h₀ h₁ h₂ : ℝ) (y₀ y : ℕ), 0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ →
        l₂ * |h₁ - h₂| ≤ Λ →
          Real.log (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
                ^ (2 * pairWeight l₁ l₂ a) ∂μ)
            ≤ (l₁ ^ 2 / 2 + l₁ / 2) * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
              + (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * |h₁ - h₂|
                * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
              + C := by
  obtain ⟨C, hC, hbound⟩ := exists_pair_prime_sum_bound_at_rademacherLaw (σ₀ := σ₀) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₁ l₂ σ h₀ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow_pair_at y₀ y l₁ l₂ σ h₀ h₁ h₂
    (by linarith)]
  have h1 := abs_le.1 (hbound l₁ l₂ σ h₀ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ)
  have h2 := sum_pair_main_term_pairAbscissaAt_le (l₁ := l₁) (l₂ := l₂) (σ := σ)
    (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) hl₁ hl₂ y₀ y
  linarith [h1.2]

/-! ### Lemma B.1's Chernoff wrapper at a general base

`RMF.IsRademacherRMF.integrable_prod_norm_rpow` and `RMF.IsRademacherRMF.prod_norm_rpow_ae_eq`
take the family of points as an argument and apply at `RMF.pairAbscissaAt` directly; only the
positivity `RMF.IsRademacherRMF.integral_prod_norm_pair_pos_at` names the family. -/

/-- **Positivity of the pair moment at a general base.**  The base is invisible: all that is used
is the shared real part and the gateway. -/
theorem IsRademacherRMF.integral_prod_norm_pair_pos_at {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {σ₀ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (l₁ l₂ σ h₀ h₁ h₂ : ℝ) (y₀ y : ℕ) (hσ : σ₀ ≤ σ) :
    (0 : ℝ) < ∫ ω, ∏ a,
      ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖ ^ (2 * pairWeight l₁ l₂ a)
        ∂μ := by
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow_pair_at y₀ y l₁ l₂ σ h₀ h₁ h₂
    (by linarith)]
  refine Finset.prod_pos fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  refine integral_prod_norm_one_add_mul_rpow_pos fun a _ => ?_
  rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, pairAbscissaAt_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)

/-- **Hamdan's Lemma B.1 for the Rademacher function, at a general base `h₀`**, exponents free.
With `S = log ‖F‖`, `A = ∑_p p^{-2σ}` and `B = |h₁-h₂| ∑_p p^{-2σ}ℓog p` over `p ∈ [y₀, y)`,
`P(S(σ+ih₀) ≥ V₁, S(σ+ih₁) - S(σ+ih₂) ≥ V₂)` is at most
`exp((l₁²/2 + l₁/2)A + (2l₂ + l₁l₂ + l₂²)B + C - l₁V₁ - l₂V₂)` for `0 ≤ l₁ ≤ Λ`, `l₂ ≥ 0` and
`l₂|h₁-h₂| ≤ Λ`, with `C` independent of `h₀`.  `RMF.IsRademacherRMF.exists_measure_link_le` needs
the free base; the Steinhaus link rotates the primes to base `0`. -/
theorem IsRademacherRMF.exists_measure_le_exp_pair_at {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (l₁ l₂ σ h₀ h₁ h₂ V₁ V₂ : ℝ) (y₀ y : ℕ) (E : Set Ω),
        0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ → l₂ * |h₁ - h₂| ≤ Λ → MeasurableSet E →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 0) ω‖) →
        (∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 1) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 2) ω‖) →
          μ.real E ≤ Real.exp ((l₁ ^ 2 / 2 + l₁ / 2)
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            + (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * |h₁ - h₂|
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
            + C - (l₁ * V₁ + l₂ * V₂)) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsRademacherRMF.exists_log_joint_moment_pair_le_at (Ω := Ω) (σ₀ := σ₀) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₁ l₂ σ h₀ h₁ h₂ V₁ V₂ y₀ y E hl₁ hl₂ hσ hl₁Λ hl₂Λ hE hE₁ hE₂
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissaAt σ h₀ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissaAt_re]
    linarith
  have hq : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      |pairWeight l₁ l₂ a| ≤ l₁ / 2 + l₂ / 2 := fun a _ => abs_pairWeight_le hl₁ hl₂ a
  have hint := hf.integrable_prod_norm_rpow Finset.univ (pairWeight l₁ l₂)
    (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hq (by linarith) hre
  have hIpos := hf.integral_prod_norm_pair_pos_at hσ₀ l₁ l₂ σ h₀ h₁ h₂ y₀ y hσ
  have hW : ∀ ω ∈ E, l₁ * V₁ + l₂ * V₂
      ≤ ∑ a, 2 * pairWeight l₁ l₂ a
        * Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖ := by
    intro ω hω
    rw [sum_two_mul_pairWeight_mul]
    have hA := mul_le_mul_of_nonneg_left (hE₁ ω hω) hl₁
    have hB := mul_le_mul_of_nonneg_left (hE₂ ω hω) hl₂
    linarith
  have hge : ∀ᵐ ω ∂(μ.restrict E), Real.exp (l₁ * V₁ + l₂ * V₂)
      ≤ ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) := by
    filter_upwards [ae_restrict_of_ae (hf.prod_norm_rpow_ae_eq Finset.univ
      (pairWeight l₁ l₂) (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hre), ae_restrict_mem hE] with ω h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (hW ω h2)
  have h1 : μ.real E * Real.exp (l₁ * V₁ + l₂ * V₂)
      ≤ ∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a)) ∂μ := by
    have hc : (∫ _ω in E, Real.exp (l₁ * V₁ + l₂ * V₂) ∂μ)
        = μ.real E * Real.exp (l₁ * V₁ + l₂ * V₂) := by
      rw [setIntegral_const, smul_eq_mul]
    rw [← hc]
    exact integral_mono_ae (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hge
  have h2 : (∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a)) ∂μ)
      ≤ ∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a) ∂μ := by
    refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) _
  have h3 : (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) ∂μ)
      ≤ Real.exp ((l₁ ^ 2 / 2 + l₁ / 2) * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
        + (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * |h₁ - h₂|
          * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) + C) := by
    have h := hbound f μ hf l₁ l₂ σ h₀ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
    have h4 := Real.exp_le_exp.2 h
    rwa [Real.exp_log hIpos] at h4
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  linarith

end RMF
