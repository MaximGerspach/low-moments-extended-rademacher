/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import RMF.EulerProduct.LogExpansion
import RMF.EulerProduct.Moments
import RMF.EulerProduct.JointMoments
import RMF.NumberTheory.PrimeTail
import RMF.EulerProduct.Block

/-!
# Two-point estimates for random Euler products

A one-point estimate controls `E ‖F_y(s)‖ ^ (2 q)` at a single `s`; second-moment and Paley–Zygmund
arguments, and hence Harper's theorem, need the correlation of `F_y(s₁)` and `F_y(s₂)`.

The main result is Harper's (5.1) for the Steinhaus law,
`RMF.exists_abs_log_integral_two_point_le`: for `400 ≤ x ≤ y` and `σ ≥ -1/log y`, with `F` the
Euler product over the primes of `(x, y]`,

`log E[‖F(1/2+σ)‖² ‖F(1/2+σ+it)‖²] = ∑_{x<p≤y} (2 + 2cos(t log p)) p^(-1-2σ) + O(1/(√x log x))`.

Independence over the primes makes the expectation a product of local moments, each of which is
`E ‖(1-zw₁)⁻¹‖² ‖(1-zw₂)⁻¹‖² = 1 + ‖w₁+w₂‖² + O(δ³)` (`RMF.exists_local_two_point_expansion`);
at Harper's weights `‖w₁ + w₂‖²` is exactly the summand of (5.1).
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The local two-point factor

The per-prime ingredient of Harper's (5.1): the joint local moment
`E ‖(1-zw₁)⁻¹‖² ‖(1-zw₂)⁻¹‖²` is `1 + ‖w₁+w₂‖²` up to `O(δ³)`.  This is
`RMF.exists_local_expansion_prod_steinhausLaw` at a two-element index set and `q ≡ 1`; indexing by
`Bool` rather than `Fin 2` keeps the specialisation to two `Fintype` lemmas. -/

/-- **The local two-point moment, to third order**: for `‖w₁‖, ‖w₂‖ ≤ δ ≤ 1/5`,
`E ‖(1-zw₁)⁻¹‖² ‖(1-zw₂)⁻¹‖² = 1 + ‖w₁+w₂‖² + O(δ³)`. -/
theorem exists_local_two_point_expansion :
    ∃ C > 0, ∀ (w₁ w₂ : ℂ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 / 5 → ‖w₁‖ ≤ δ → ‖w₂‖ ≤ δ →
      |(∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw)
        - (1 + ‖w₁ + w₂‖ ^ 2)| ≤ C * δ ^ 3 := by
  obtain ⟨C, hC, h⟩ :=
    exists_local_expansion_prod_steinhausLaw (Q := 1) (by norm_num) (Finset.univ : Finset Bool)
  refine ⟨C, hC, fun w₁ w₂ δ hδ0 hδ5 hw₁ hw₂ => ?_⟩
  have key := h (fun _ => (1 : ℝ)) (fun b => cond b w₂ w₁) δ
    (fun b _ => by norm_num) hδ0 hδ5 (fun b _ => by cases b <;> simp [hw₁, hw₂])
  have hprod : ∀ z : ℂ,
      (∏ b : Bool, ‖(1 - z * cond b w₂ w₁)⁻¹‖ ^ (2 * (1 : ℝ)))
        = ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 := by
    intro z
    rw [Fintype.prod_bool]
    simp only [cond_true, cond_false]
    rw [show (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.rpow_natCast]
    ring
  have hsum : ‖∑ b : Bool, (((1 : ℝ) : ℂ)) * cond b w₂ w₁‖ ^ 2 = ‖w₁ + w₂‖ ^ 2 := by
    rw [Fintype.sum_bool]
    simp only [cond_true, cond_false, Complex.ofReal_one, one_mul]
    rw [add_comm]
  simp only [hprod, hsum] at key
  exact key

/-! ### Positivity of the local two-point moment

`RMF.abs_log_prod_sub_sum_le` — the step that turns the product over primes into a sum of
logarithms — requires each factor to be *strictly positive*.  The expansion above does not supply
that: its error `Cδ³` is not below `1` at `δ = 1/5` for the `C` it produces, so `1 - Cδ³` is no
lower bound at all.

Positivity comes from the integrand instead, where it is immediate.  On the circle
`‖1 - zw‖ ≤ 1 + ‖w‖`, so the integrand is at least `((1+‖w₁‖)(1+‖w₂‖))⁻²` pointwise — a positive
constant, with no smallness of `‖w‖` needed beyond `‖w‖ < 1`. -/

/-- The two-point integrand is measurable.  `z ↦ (1 - zw)⁻¹` is not continuous globally, so this
routes through `RMF.aestronglyMeasurable_localIntegrand`, whose `max` trick repairs that; only the
exponent has to be moved from `rpow` to `Monoid.npow`. -/
lemma aestronglyMeasurable_local_two_point {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    AEStronglyMeasurable
      (fun z : ℂ => ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2) steinhausLaw := by
  have hcast : ∀ w z : ℂ, ‖(1 - z * w)⁻¹‖ ^ (2 : ℝ) = ‖(1 - z * w)⁻¹‖ ^ 2 := fun w z => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact ((aestronglyMeasurable_localIntegrand h₁ 2).congr
      (Filter.Eventually.of_forall (hcast w₁))).mul
    ((aestronglyMeasurable_localIntegrand h₂ 2).congr
      (Filter.Eventually.of_forall (hcast w₂)))

/-- The two-sided pointwise bound on the two-point integrand, valid a.e. because the Steinhaus law
lives on the unit circle. -/
lemma ae_local_two_point_bounds {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    ∀ᵐ z ∂steinhausLaw,
      ((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2
          ≤ ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2
        ∧ ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2
          ≤ ((1 - ‖w₁‖)⁻¹) ^ 2 * ((1 - ‖w₂‖)⁻¹) ^ 2 := by
  filter_upwards [ae_norm_one_sub_mul_bounds w₁, ae_norm_one_sub_mul_bounds w₂]
    with z ⟨hge₁, hle₁⟩ ⟨hge₂, hle₂⟩
  have hp₁ : (0 : ℝ) < 1 - ‖w₁‖ := by linarith
  have hp₂ : (0 : ℝ) < 1 - ‖w₂‖ := by linarith
  have hn₁ : (0 : ℝ) < ‖1 - z * w₁‖ := lt_of_lt_of_le hp₁ hge₁
  have hn₂ : (0 : ℝ) < ‖1 - z * w₂‖ := lt_of_lt_of_le hp₂ hge₂
  simp only [norm_inv]
  exact ⟨mul_le_mul (pow_le_pow_left₀ (by positivity) (inv_anti₀ hn₁ hle₁) 2)
      (pow_le_pow_left₀ (by positivity) (inv_anti₀ hn₂ hle₂) 2) (by positivity) (by positivity),
    mul_le_mul (pow_le_pow_left₀ (by positivity) (inv_anti₀ hp₁ hge₁) 2)
      (pow_le_pow_left₀ (by positivity) (inv_anti₀ hp₂ hge₂) 2) (by positivity) (by positivity)⟩

/-- The two-point integrand is bounded, hence integrable. -/
lemma integrable_local_two_point {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    Integrable (fun z : ℂ => ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2) steinhausLaw :=
  integrable_of_norm_le_steinhausLaw (aestronglyMeasurable_local_two_point h₁ h₂)
    (((1 - ‖w₁‖)⁻¹) ^ 2 * ((1 - ‖w₂‖)⁻¹) ^ 2) <| by
    filter_upwards [ae_local_two_point_bounds h₁ h₂] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz.2

/-- **The local two-point moment is strictly positive.**  This is the hypothesis
`RMF.abs_log_prod_sub_sum_le` needs of every factor, and it is what makes `log ∏ = ∑ log`
available for (5.1). -/
theorem integral_local_two_point_pos {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    0 < ∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw := by
  have hmono := integral_mono_ae
    (integrable_const (((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2))
    (integrable_local_two_point h₁ h₂)
    (by filter_upwards [ae_local_two_point_bounds h₁ h₂] with z hz using hz.1)
  have hconst : (∫ _z : ℂ, ((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2 ∂steinhausLaw)
      = ((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2 := by simp
  rw [hconst] at hmono
  exact lt_of_lt_of_le (by positivity) hmono

/-! ### From the local factor to Harper's (5.1)

`exists_local_two_point_expansion` delivers the local moment as `1 + ‖w₁ + w₂‖²`.  At Harper's
weights that norm is not an opaque quantity: it is exactly the summand of (5.1).  The two lemmas
below are what instantiating the expansion at every prime of a range needs — the closed form of the
main term, and the admissibility bound the expansion demands of its weights. -/

/-- **The local main term of Harper's (5.1), in closed form**: at `w₁ = p^(-s)` and
`w₂ = p^(-(s+it))` with `Re s = 1/2 + σ`, `‖w₁ + w₂‖² = (2 + 2 cos(t log p)) · p^(-1-2σ)`.  The
cosine compares the two points; at `t = 0` it degenerates to `4 p^(-1-2σ)`.  Only `Re s` is
constrained: the cross term sees the difference of the two arguments, which is `-t`. -/
lemma norm_sq_add_prime_cpow_neg (p : Nat.Primes) {s : ℂ} {σ t : ℝ} (hres : s.re = 1 / 2 + σ) :
    ‖((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (-(s + (t : ℂ) * Complex.I))‖ ^ 2
      = (2 + 2 * Real.cos (t * Real.log ((p : ℕ) : ℝ))) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  -- the modulus of either weight, both governed by the same real part
  have hnorm : ∀ u : ℂ, u.re = 1 / 2 + σ →
      ‖((p : ℕ) : ℂ) ^ (-u)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    intro u hu
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hu,
      ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0]
    congr 1
    push_cast
    ring
  have hre₂ : (s + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by simp [hres]
  have him : s.im - (s + (t : ℂ) * Complex.I).im = -t := by simp
  have hcross := re_natCast_cpow_neg_mul_conj (p := (p : ℕ)) p.2.pos s (s + (t : ℂ) * Complex.I)
  rw [hres, hre₂, him, neg_mul, Real.cos_neg,
    show -(1 / 2 + σ + (1 / 2 + σ)) = -1 - 2 * σ by ring] at hcross
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  simp only [Complex.normSq_eq_norm_sq]
  rw [hnorm s hres, hnorm _ hre₂, hcross]
  ring

/-- **Harper's weights are admissible for the local expansion**: for `x ≤ p ≤ y` and
`σ ≥ -1/log y`, `‖p^(-(1/2+σ))‖ ≤ e/√x`.  The factor `e` is where the lower bound on `σ` is spent:
`p^(-σ) = exp(-σ log p) ≤ exp(log p / log y) ≤ e` because `p ≤ y`.  Without it the weight can
exceed `1` as `σ → -∞`, and the expansion, a geometric series in `w`, diverges. -/
lemma norm_prime_cpow_neg_le_of_le (p : Nat.Primes) {x y σ : ℝ} (hx : 0 < x)
    (hxp : x ≤ ((p : ℕ) : ℝ)) (hpy : ((p : ℕ) : ℝ) ≤ y)
    (hσ : -(1 / Real.log y) ≤ σ) :
    ‖((p : ℕ) : ℂ) ^ (-((1 / 2 + σ : ℝ) : ℂ))‖ ≤ Real.exp 1 * x ^ (-(1 / 2 : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (Real.log_pos (by norm_num))
    (Real.log_le_log (by norm_num) (le_trans hp2 hpy))
  -- the tilt factor costs at most `e`
  have htilt : ((p : ℕ) : ℝ) ^ (-σ) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp0]
    refine Real.exp_le_exp.2 ?_
    have h1 : Real.log ((p : ℕ) : ℝ) * (-σ) ≤ Real.log ((p : ℕ) : ℝ) * (1 / Real.log y) :=
      mul_le_mul_of_nonneg_left (by linarith) hlogp
    have h2 : Real.log ((p : ℕ) : ℝ) * (1 / Real.log y) ≤ 1 := by
      rw [mul_one_div, div_le_one hlogy]
      exact Real.log_le_log hp0 hpy
    linarith
  -- and the modulus itself only shrinks as `p` grows
  have hbase : ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx hxp (by norm_num)
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, Complex.ofReal_re,
    show -(1 / 2 + σ) = -(1 / 2 : ℝ) + -σ by ring, Real.rpow_add hp0]
  exact mul_le_mul hbase htilt (Real.rpow_nonneg hp0.le _)
    (Real.rpow_nonneg hx.le _) |>.trans_eq (by ring)

/-- `400^(-1/2) = 1/20`, in the monotone form the weight bounds want. -/
lemma rpow_neg_half_le_of_le {x : ℝ} (hx : 400 ≤ x) : x ^ (-(1 / 2 : ℝ)) ≤ 1 / 20 := by
  have hxr : x ^ (-(1 / 2 : ℝ)) ≤ (400 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
  rwa [show (400 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 20 from by
    rw [Real.rpow_neg (by norm_num), show (400 : ℝ) = 20 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast (20 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
    norm_num] at hxr

/-- **The sharp uniform smallness of Harper's weights at `x ≥ 400`:** `δ ≤ e/20 < 0.136`.

`1/5` is all `exists_local_two_point_expansion` asks, but `1/5` is *not* enough to keep the local
moment within distance `1` of `1` — at `δ = 1/5` the upper bound `(1-δ)^(-4)` is `2.44`. The true
size `e/20` gives `(1-δ)^(-4) ≤ 1.8`, which is what makes the logarithm expandable at Harper's own
threshold rather than only for large `x`. -/
lemma norm_prime_cpow_neg_le_const (p : Nat.Primes) {x y σ : ℝ} (hx : 400 ≤ x)
    (hxp : x ≤ ((p : ℕ) : ℝ)) (hpy : ((p : ℕ) : ℝ) ≤ y)
    (hσ : -(1 / Real.log y) ≤ σ) :
    ‖((p : ℕ) : ℂ) ^ (-((1 / 2 + σ : ℝ) : ℂ))‖ ≤ 0.136 := by
  have hx0 : (0 : ℝ) < x := by linarith
  refine (norm_prime_cpow_neg_le_of_le p hx0 hxp hpy hσ).trans ?_
  have hxr := rpow_neg_half_le_of_le hx
  have hx2 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]

/-! ### The local moment against a uniform weight bound

`RMF.ae_local_two_point_bounds` is stated at the exact norms `‖wᵢ‖`; integrating it and relaxing
to a common `δ` gives the form the per-prime estimate uses, where both weights are the same
size. -/

/-- **The local two-point moment is trapped between `(1+δ)^(-4)` and `(1-δ)^(-4)`.** -/
lemma localMoment_two_point_bounds {w₁ w₂ : ℂ} {δ : ℝ} (hδ : δ < 1)
    (h₁ : ‖w₁‖ ≤ δ) (h₂ : ‖w₂‖ ≤ δ) :
    ((1 + δ)⁻¹) ^ 4 ≤ (∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw)
      ∧ (∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw) ≤ ((1 - δ)⁻¹) ^ 4 := by
  have hδ0 : (0 : ℝ) ≤ δ := le_trans (norm_nonneg _) h₁
  have hn₁ : ‖w₁‖ < 1 := lt_of_le_of_lt h₁ hδ
  have hn₂ : ‖w₂‖ < 1 := lt_of_le_of_lt h₂ hδ
  have hae := ae_local_two_point_bounds hn₁ hn₂
  constructor
  · have hlow := integral_mono_ae
      (integrable_const (((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2))
      (integrable_local_two_point hn₁ hn₂)
      (by filter_upwards [hae] with z hz using hz.1)
    have hconst : (∫ _z : ℂ, ((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2 ∂steinhausLaw)
        = ((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2 := by simp
    rw [hconst] at hlow
    refine le_trans ?_ hlow
    have e₁ : ((1 + δ)⁻¹) ^ 2 ≤ ((1 + ‖w₁‖)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 2
    have e₂ : ((1 + δ)⁻¹) ^ 2 ≤ ((1 + ‖w₂‖)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 2
    calc ((1 + δ)⁻¹) ^ 4 = ((1 + δ)⁻¹) ^ 2 * ((1 + δ)⁻¹) ^ 2 := by ring
      _ ≤ ((1 + ‖w₁‖)⁻¹) ^ 2 * ((1 + ‖w₂‖)⁻¹) ^ 2 :=
          mul_le_mul e₁ e₂ (by positivity) (by positivity)
  · have hup := integral_mono_ae (integrable_local_two_point hn₁ hn₂)
      (integrable_const (((1 - ‖w₁‖)⁻¹) ^ 2 * ((1 - ‖w₂‖)⁻¹) ^ 2))
      (by filter_upwards [hae] with z hz using hz.2)
    have hconst : (∫ _z : ℂ, ((1 - ‖w₁‖)⁻¹) ^ 2 * ((1 - ‖w₂‖)⁻¹) ^ 2 ∂steinhausLaw)
        = ((1 - ‖w₁‖)⁻¹) ^ 2 * ((1 - ‖w₂‖)⁻¹) ^ 2 := by simp
    rw [hconst] at hup
    refine hup.trans ?_
    have e₁ : ((1 - ‖w₁‖)⁻¹) ^ 2 ≤ ((1 - δ)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by linarith) (by linarith)) 2
    have e₂ : ((1 - ‖w₂‖)⁻¹) ^ 2 ≤ ((1 - δ)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by linarith) (by linarith)) 2
    calc ((1 - ‖w₁‖)⁻¹) ^ 2 * ((1 - ‖w₂‖)⁻¹) ^ 2
        ≤ ((1 - δ)⁻¹) ^ 2 * ((1 - δ)⁻¹) ^ 2 := mul_le_mul e₁ e₂ (by positivity) (by positivity)
      _ = ((1 - δ)⁻¹) ^ 4 := by ring

/-- **`|log A - (A - 1)| ≤ |A - 1|²/c` when `|A - 1| ≤ 1 - c`**, the constant governed by the
distance from the edge of the disc of convergence.  Mathlib's `Real.abs_log_sub_add_sum_range_le`
needs only `|A - 1| < 1`, not the `≤ 1/2` of `RMF.abs_log_one_add_sub_le`; that keeps Harper's
threshold `x ≥ 400` usable, where `|A - 1|` is about `0.8`. -/
lemma abs_log_sub_sub_one_le {A c : ℝ} (hc : 0 < c) (h : |A - 1| ≤ 1 - c) :
    |Real.log A - (A - 1)| ≤ |A - 1| ^ 2 / c := by
  have habs : |1 - A| = |A - 1| := abs_sub_comm 1 A
  have hlt : |1 - A| < 1 := by rw [habs]; linarith
  have key := Real.abs_log_sub_add_sum_range_le hlt 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one,
    sub_sub_cancel, Nat.reduceAdd, habs] at key
  rw [show Real.log A - (A - 1) = 1 - A + Real.log A by ring]
  refine key.trans ?_
  gcongr
  linarith [abs_nonneg (A - 1), sq_nonneg |A - 1|]

/-! ### The per-weight logarithmic estimate

Everything above combines into the statement (5.1) actually needs at each prime: the *logarithm*
of the local moment differs from `‖w₁+w₂‖²` by `O(δ³)`.  Splitting the arithmetic off from the
measure theory keeps the numeric margins visible — they are what pins Harper's `x ≥ 400`. -/

/-- The arithmetic of the per-weight estimate, with no measure theory in it.

`A` is the local moment, `M` its main term.  The four numeric inputs are: `M ≤ 4δ²` (the triangle
inequality), the expansion's `|A - (1+M)| ≤ C₀δ³`, and the two-sided `0.55 ≤ A ≤ 1.85` that keeps
`A` inside the disc where `log` is expandable. -/
lemma abs_log_sub_main_le {A M C₀ δ : ℝ} (hC₀ : 0 < C₀) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.136)
    (hM0 : 0 ≤ M) (hM4 : M ≤ 4 * δ ^ 2) (hE : |A - (1 + M)| ≤ C₀ * δ ^ 3)
    (hAlow : 0.55 ≤ A) (hAup : A ≤ 1.85) :
    |Real.log A - M| ≤ (7 * (4 + C₀) ^ 2 + C₀) * δ ^ 3 := by
  have hAabs : |A - 1| ≤ 1 - 0.15 := by
    rw [abs_le]
    constructor <;> linarith
  have hlog := abs_log_sub_sub_one_le (by norm_num : (0 : ℝ) < 0.15) hAabs
  have hδ3 : δ ^ 3 ≤ δ ^ 2 := by nlinarith
  have hA1 : |A - 1| ≤ (4 + C₀) * δ ^ 2 := by
    have hsplit : |A - 1| ≤ |A - (1 + M)| + |M| := by
      rw [show A - 1 = (A - (1 + M)) + M by ring]
      exact abs_add_le _ _
    rw [abs_of_nonneg hM0] at hsplit
    nlinarith [mul_le_mul_of_nonneg_left hδ3 hC₀.le]
  have hsq : |A - 1| ^ 2 ≤ ((4 + C₀) * δ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hA1 2
  have hd4 : δ ^ 4 ≤ 0.136 * δ ^ 3 := by nlinarith [pow_nonneg hδ0 3]
  have hEM : |A - 1 - M| ≤ C₀ * δ ^ 3 := by
    rw [show A - 1 - M = A - (1 + M) by ring]
    exact hE
  have hsum : |Real.log A - M| ≤ |Real.log A - (A - 1)| + |A - 1 - M| := by
    rw [show Real.log A - M = (Real.log A - (A - 1)) + (A - 1 - M) by ring]
    exact abs_add_le _ _
  have hdiv : |A - 1| ^ 2 / 0.15 ≤ 7 * (4 + C₀) ^ 2 * δ ^ 3 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.15)]
    nlinarith [hsq, mul_le_mul_of_nonneg_left hd4 (sq_nonneg (4 + C₀)), pow_nonneg hδ0 3]
  linarith

/-- **The per-weight logarithmic estimate.**  For weights of common size `δ ≤ e/20`,

`log E‖(1-zw₁)⁻¹‖²‖(1-zw₂)⁻¹‖² = ‖w₁+w₂‖² + O(δ³)`.

The threshold is `0.136`, not the expansion's own `1/5`: see `RMF.norm_prime_cpow_neg_le_const`
for why the weaker bound is useless here. -/
theorem exists_abs_log_local_two_point_sub_le :
    ∃ C > 0, ∀ (w₁ w₂ : ℂ) (δ : ℝ), 0 ≤ δ → δ ≤ 0.136 → ‖w₁‖ ≤ δ → ‖w₂‖ ≤ δ →
      |Real.log (∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw)
          - ‖w₁ + w₂‖ ^ 2| ≤ C * δ ^ 3 := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_local_two_point_expansion
  refine ⟨7 * (4 + C₀) ^ 2 + C₀, by positivity, fun w₁ w₂ δ hδ0 hδ h₁ h₂ => ?_⟩
  have hδ1 : δ < 1 := by linarith
  obtain ⟨hlow, hup⟩ := localMoment_two_point_bounds hδ1 h₁ h₂
  refine abs_log_sub_main_le hC₀ hδ0 hδ (by positivity) ?_
    (hexp w₁ w₂ δ hδ0 (by linarith) h₁ h₂) ?_ ?_
  · calc ‖w₁ + w₂‖ ^ 2 ≤ (2 * δ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans (by linarith)) 2
      _ = 4 * δ ^ 2 := by ring
  · refine le_trans ?_ hlow
    have hmono : (1 + δ) ^ 4 ≤ (1.136 : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    rw [inv_pow]
    calc (0.55 : ℝ) ≤ ((1.136 : ℝ) ^ 4)⁻¹ := by norm_num
      _ ≤ ((1 + δ) ^ 4)⁻¹ := inv_anti₀ (by positivity) hmono
  · refine hup.trans ?_
    have hmono : (0.864 : ℝ) ^ 4 ≤ (1 - δ) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    rw [inv_pow]
    calc ((1 - δ) ^ 4)⁻¹ ≤ ((0.864 : ℝ) ^ 4)⁻¹ := inv_anti₀ (by norm_num) hmono
      _ ≤ 1.85 := by norm_num

/-! ### Harper's (5.1): the product over a range of primes

The local moment at Harper's two points gets a name, because it is what both sides of (5.1) are
built from and writing it out inline makes the statements unreadable. -/

/-- **The local two-point moment at `p`**, at the points `1/2+σ` and `1/2+σ+it`:
`E ‖(1 - z p^{-(1/2+σ)})⁻¹‖² ‖(1 - z p^{-(1/2+σ+it)})⁻¹‖²` under the Steinhaus law. -/
noncomputable def localTwoPointMoment (p : ℕ) (σ t : ℝ) : ℝ :=
  ∫ z, ‖(1 - z * (p : ℂ) ^ (-((1 / 2 + σ : ℝ) : ℂ)))⁻¹‖ ^ 2
    * ‖(1 - z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ^ 2 ∂steinhausLaw

/-- The weights at a prime of the range have the common modulus `p^(-(1/2+σ))`, below `e/20`. -/
lemma norm_weights_eq {p : ℕ} (hp : p.Prime) {σ t x y : ℝ} (hx : 400 ≤ x)
    (hxp : x ≤ (p : ℝ)) (hpy : (p : ℝ) ≤ y) (hσ : -(1 / Real.log y) ≤ σ) :
    ‖(p : ℂ) ^ (-((1 / 2 + σ : ℝ) : ℂ))‖ = (p : ℝ) ^ (-(1 / 2 + σ))
      ∧ ‖(p : ℂ) ^ (-(((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ = (p : ℝ) ^ (-(1 / 2 + σ))
      ∧ (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 0.136 := by
  have hnorm : ∀ u : ℂ, u.re = 1 / 2 + σ → ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-(1 / 2 + σ)) := by
    intro u hu
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, hu]
  have h₁ := hnorm _ (by simp : (((1 / 2 + σ : ℝ) : ℂ)).re = 1 / 2 + σ)
  refine ⟨h₁, hnorm _ (by simp), ?_⟩
  rw [← h₁]
  exact norm_prime_cpow_neg_le_const ⟨p, hp⟩ hx hxp hpy hσ

/-- Every factor of (5.1) is strictly positive — the hypothesis `abs_log_prod_sub_sum_le` asks. -/
lemma localTwoPointMoment_pos {p : ℕ} (hp : p.Prime) {σ t x y : ℝ} (hx : 400 ≤ x)
    (hxp : x ≤ (p : ℝ)) (hpy : (p : ℝ) ≤ y) (hσ : -(1 / Real.log y) ≤ σ) :
    0 < localTwoPointMoment p σ t := by
  obtain ⟨h₁, h₂, hsmall⟩ := norm_weights_eq (t := t) hp hx hxp hpy hσ
  exact integral_local_two_point_pos (by rw [h₁]; linarith) (by rw [h₂]; linarith)

/-- **The per-prime form of (5.1).**  At a prime of Harper's range the logarithm of the local
moment is the (5.1) summand up to `O(p^(-3/2-3σ))`, which is exactly the summand of
`RMF.sum_prime_Ioc_rpow_cube_le'`. -/
theorem exists_abs_log_localTwoPointMoment_sub_le :
    ∃ C > 0, ∀ (p : ℕ), p.Prime → ∀ σ t x y : ℝ, 400 ≤ x → x ≤ (p : ℝ) → (p : ℝ) ≤ y →
      -(1 / Real.log y) ≤ σ →
      |Real.log (localTwoPointMoment p σ t)
          - (2 + 2 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C * (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
  obtain ⟨C, hC, h⟩ := exists_abs_log_local_two_point_sub_le
  refine ⟨C, hC, fun p hp σ t x y hx hxp hpy hσ => ?_⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  obtain ⟨h₁, h₂, hsmall⟩ := norm_weights_eq (t := t) hp hx hxp hpy hσ
  have key := h _ _ _ (Real.rpow_nonneg hp0.le _) hsmall h₁.le h₂.le
  rw [norm_sq_add_prime_cpow_neg ⟨p, hp⟩ (by simp : (((1 / 2 + σ : ℝ) : ℂ)).re = 1 / 2 + σ)]
    at key
  have hcube : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 3 = (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 3, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  rwa [hcube] at key

/-- **Harper's (5.1), as a product of local moments**:
`log ∏_{x<p≤y} Aₚ = ∑_{x<p≤y} (2 + 2cos(t log p)) p^(-1-2σ) + O(1/(√x log x))`, for
`400 ≤ x ≤ y` and `σ ≥ -1/log y`.  The radical is on `x` alone, from
`RMF.sum_prime_Ioc_rpow_cube_le'`.  The identification of `∏_p Aₚ` with
`E‖F(1/2+σ)‖²‖F(1/2+σ+it)‖²` is `RMF.IsSteinhausRMF.integral_norm_randomEulerProductIco_sq_mul_sq`
below, assembled in `RMF.exists_abs_log_integral_two_point_le`. -/
theorem exists_abs_log_prod_localTwoPointMoment_le :
    ∃ C > 0, ∀ σ t x y : ℝ, 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      |Real.log (∏ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, localTwoPointMoment p σ t)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + 2 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C / (Real.sqrt x * Real.log x) := by
  obtain ⟨C₁, hC₁, hloc⟩ := exists_abs_log_localTwoPointMoment_sub_le
  refine ⟨C₁ * (Real.exp 3 * (8 * Real.log 4)), by positivity, fun σ t x y hx hxy hσ => ?_⟩
  have hy0 : (0 : ℝ) ≤ y := by linarith
  -- membership of the range gives exactly the two inequalities the per-prime estimate wants
  have hrange : ∀ q ∈ {q ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime q},
      Nat.Prime q ∧ x ≤ (q : ℝ) ∧ (q : ℝ) ≤ y := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    refine ⟨hq.2, ?_, ?_⟩
    · have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq.1.1
      linarith
    · exact le_trans (by exact_mod_cast hq.1.2) (Nat.floor_le hy0)
  refine le_trans (abs_log_prod_sub_sum_le (C := C₁)
    (b := fun q => (q : ℝ) ^ (-(3 / 2) - 3 * σ)) (fun q hq => ?_) (fun q hq => ?_)) ?_
  · obtain ⟨hqp, hxq, hqy⟩ := hrange q hq
    exact localTwoPointMoment_pos hqp hx hxq hqy hσ
  · obtain ⟨hqp, hxq, hqy⟩ := hrange q hq
    exact hloc q hqp σ t x y hx hxq hqy hσ
  · calc C₁ * ∑ q ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime q, (q : ℝ) ^ (-(3 / 2) - 3 * σ)
        ≤ C₁ * (Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x))) :=
          mul_le_mul_of_nonneg_left (sum_prime_Ioc_rpow_cube_le' (by linarith) hxy hσ) hC₁.le
      _ = C₁ * (Real.exp 3 * (8 * Real.log 4)) / (Real.sqrt x * Real.log x) := by ring

/-! ### The expectation behind the product

`∏_p Aₚ` is what (5.1) estimates, but Harper's left-hand side is an *expectation*.  Identifying
the two is the independence step, over a **range** of primes: rewrite the two Euler products a.e.
as products over the range, exchange the two finite products, and factor.  The general form is
`RMF.integral_prod_norm_randomEulerProductIco_rpow_compMult`. -/

/-- **The two-point moment of a block Euler product factors over the primes of the block.** -/
theorem integral_norm_randomEulerProductIco_sq_mul_sq_compMult {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1)
    (y₀ y₁ : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s₂ ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ‖(1 - z * (p : ℂ) ^ (-s₁))⁻¹‖ ^ 2 * ‖(1 - z * (p : ℂ) ^ (-s₂))⁻¹‖ ^ 2 ∂ν := by
  have hae : ∀ᵐ ω ∂μ,
      ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s₂ ω‖ ^ 2
        = ∏ p ∈ primesIco y₀ y₁, ‖(1 - X p ω * (p : ℂ) ^ (-s₁))⁻¹‖ ^ 2
            * ‖(1 - X p ω * (p : ℂ) ^ (-s₂))⁻¹‖ ^ 2 := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX hν y₀ y₁] with ω hω
    rw [randomEulerProductIco_compMult_eq hs₁ hω, randomEulerProductIco_compMult_eq hs₂ hω,
      norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  have hmeas : ∀ p ∈ primesIco y₀ y₁, AEStronglyMeasurable
      (fun z : ℂ => ‖(1 - z * (p : ℂ) ^ (-s₁))⁻¹‖ ^ 2
        * ‖(1 - z * (p : ℂ) ^ (-s₂))⁻¹‖ ^ 2) ν := by
    intro p _
    fun_prop
  rw [integral_congr_ae hae,
    hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp)
      (fun p z => ‖(1 - z * (p : ℂ) ^ (-s₁))⁻¹‖ ^ 2 * ‖(1 - z * (p : ℂ) ^ (-s₂))⁻¹‖ ^ 2) hmeas]

/-- The Steinhaus case: the left-hand side of Harper's (5.1) is `∏_p Aₚ`. -/
theorem IsSteinhausRMF.integral_norm_randomEulerProductIco_sq_mul_sq
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f y₀ y₁ s₂ ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁,
          ∫ z, ‖(1 - z * (p : ℂ) ^ (-s₁))⁻¹‖ ^ 2 * ‖(1 - z * (p : ℂ) ^ (-s₂))⁻¹‖ ^ 2
            ∂steinhausLaw := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact integral_norm_randomEulerProductIco_sq_mul_sq_compMult hX norm_le_one_steinhausLaw
    y₀ y₁ hs₁ hs₂

/-! ### (5.1) -/

/-- At Harper's range the two points already lie to the right of the critical line.

`x ≥ 400` forces `log y > 2`, hence `σ ≥ -1/log y > -1/2`.  So the positivity of `Re s` that the
Euler-product machinery needs is *not* an extra hypothesis — the range supplies it. -/
lemma half_add_pos {x y σ : ℝ} (hx : 400 ≤ x) (hxy : x ≤ y) (hσ : -(1 / Real.log y) ≤ σ) :
    0 < 1 / 2 + σ := by
  have hy400 : (400 : ℝ) ≤ y := le_trans hx hxy
  have hexp2 : Real.exp 2 < 400 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hlogy : (2 : ℝ) < Real.log y :=
    lt_of_lt_of_le ((Real.lt_log_iff_exp_lt (by norm_num)).2 hexp2)
      (Real.log_le_log (by norm_num) hy400)
  have hpos : (0 : ℝ) < Real.log y := by linarith
  have hinv : (0 : ℝ) < 1 / Real.log y := by positivity
  have hid : 1 / Real.log y * Real.log y = 1 := by field_simp
  nlinarith [mul_pos hinv (by linarith : (0 : ℝ) < Real.log y - 2), hid]

/-- **Harper's (5.1).**  For a Steinhaus random multiplicative function, `400 ≤ x ≤ y`, real `t`
and `σ ≥ -1/log y`, with `F` the Euler product over the primes of `(x, y]`,
`log E[‖F(1/2+σ)‖² ‖F(1/2+σ+it)‖²] = ∑_{x<p≤y} (2 + 2cos(t log p)) p^(-1-2σ) + O(1/(√x log x))`,
the constant independent of `f`, `μ`, `σ`, `t`, `x` and `y`.  It is Harper's Lemma 6 at
`u = v = 0`, the case his Key Proposition 5 uses. -/
theorem exists_abs_log_integral_two_point_le :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ σ t x y : ℝ, 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      |Real.log (∫ ω,
            ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
              * ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1)
                  (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + 2 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C / (Real.sqrt x * Real.log x) := by
  obtain ⟨C, hC, h⟩ := exists_abs_log_prod_localTwoPointMoment_le
  refine ⟨C, hC, fun f μ hf σ t x y hx hxy hσ => ?_⟩
  have hre : (0 : ℝ) < 1 / 2 + σ := half_add_pos hx hxy hσ
  have hre₁ : 0 < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hre₂ : 0 < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq _ _ hre₁ hre₂,
    ← filter_prime_Ioc_eq_primesIco]
  simpa only [localTwoPointMoment] using h σ t x y hx hxy hσ

end RMF
