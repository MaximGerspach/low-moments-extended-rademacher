/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.Tilted
import RMF.EulerProduct.TiltedPrimes

/-!
# The two-fold tilt

Harper's two-point argument reweights by `‖F_y(s₁)‖² ‖F_y(s₂)‖²` rather than by a single
`‖F_y(s)‖²`.

**The whole section rests on one observation**: that weight is the product of the two one-fold
weights, so the two-fold tilt is a one-fold tilt *of* a one-fold tilt,

  `tiltedMeasure₂ s₁ s₂ = (tiltedMeasure s₁).tilted (tiltExponent s₂)`,

by `MeasureTheory.tilted_tilted` — note that namespace, not `Measure`.  Everything the one-fold
theory proves is therefore available at the first stage, and only the *perturbation* from the
second stage has to be estimated, which keeps the two-point moment bounds of
`RMF/EulerProduct/TwoPointTiltLaw.lean` from being a rewrite of `RMF/EulerProduct/TiltedLaw.lean`.

Note the normaliser `E‖F(s₁)‖²‖F(s₂)‖²` is a genuinely two-point quantity, but its **finiteness**
is not: `RMF.IsSteinhausRMF.ae_norm_randomEulerProduct_le` bounds `‖F_y(s)‖` by a finite product of
constants, so the weight is a.e. bounded and integrability is free.  Its value is Harper's (5.1)
(`RMF.exists_abs_log_integral_two_point_le`).
-/

open MeasureTheory ProbabilityTheory Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-- **The two-fold tilt exponent**, `2 log‖F_y(s₁)‖ + 2 log‖F_y(s₂)‖`. -/
noncomputable def tiltExponent₂ (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s₁ s₂ : ℂ) (ω : Ω) : ℝ :=
  tiltExponent f y s₁ ω + tiltExponent f y s₂ ω

/-- **The two-fold tilted measure**, reweighted by `‖F_y(s₁)‖² ‖F_y(s₂)‖²`. -/
noncomputable def tiltedMeasure₂ (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s₁ s₂ : ℂ)
    (μ : Measure Ω) : Measure Ω :=
  μ.tilted (tiltExponent₂ f y s₁ s₂)

/-- The one-fold weight is a.e. bounded: `‖F_y(s)‖` is a finite product of constants. -/
lemma IsSteinhausRMF.ae_exp_tiltExponent_le (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, Real.exp (tiltExponent f y s ω)
      ≤ (∏ p ∈ Nat.primesBelow y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹) ^ 2 := by
  filter_upwards [hf.exp_tiltExponent_ae_eq y hs, hf.ae_norm_randomEulerProduct_le y hs]
    with ω h1 h2
  rw [h1]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- **Integrability at the first stage.**  The second weight is a.e. bounded, and
`tiltedMeasure f y s₁ μ` is a probability measure absolutely continuous with respect to `μ`, so
no two-point moment is needed here. -/
theorem IsSteinhausRMF.integrable_exp_tiltExponent_tilted (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    Integrable (fun ω => Real.exp (tiltExponent f y s₂ ω)) (tiltedMeasure f y s₁ μ) := by
  have hP := hf.isProbabilityMeasure_tiltedMeasure y hs₁
  have hac : tiltedMeasure f y s₁ μ ≪ μ := tiltedMeasure_absolutelyContinuous f y s₁ μ
  refine Integrable.mono'
    (integrable_const ((∏ p ∈ Nat.primesBelow y, (1 - ‖(p : ℂ) ^ (-s₂)‖)⁻¹) ^ 2))
    (((hf.integrable_exp_tiltExponent y hs₂).aestronglyMeasurable).mono_ac hac) ?_
  filter_upwards [Filter.Eventually.filter_mono hac.ae_le
    (hf.ae_exp_tiltExponent_le y hs₂)] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact hω

/-- **The two-fold tilt is a tilt of a tilt.**  This is the structural point of the section: the
one-fold theory applies verbatim at the first stage. -/
theorem IsSteinhausRMF.tiltedMeasure₂_eq (hf : IsSteinhausRMF f μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) :
    tiltedMeasure₂ f y s₁ s₂ μ = (tiltedMeasure f y s₁ μ).tilted (tiltExponent f y s₂) := by
  rw [tiltedMeasure₂, tiltedMeasure,
    tilted_tilted (hf.integrable_exp_tiltExponent y hs₁)]
  rfl

/-- **The two-fold tilt is a probability measure.** -/
theorem IsSteinhausRMF.isProbabilityMeasure_tiltedMeasure₂ (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    IsProbabilityMeasure (tiltedMeasure₂ f y s₁ s₂ μ) := by
  have hP := hf.isProbabilityMeasure_tiltedMeasure y hs₁
  rw [hf.tiltedMeasure₂_eq y hs₁]
  exact isProbabilityMeasure_tilted (hf.integrable_exp_tiltExponent_tilted y hs₁ hs₂)

/-! ### The two-fold exponent as a prime sum

The factorisation results consume an exponent of the shape `∑ i ∈ t, g i (X i ω)` — **one** function
per prime.  The two-fold exponent is a sum of two such, so it is again of that shape with
`g p = localTilt s₁ p + localTilt s₂ p`.  Nothing about the two-point structure survives into the
factorisation: it sees a single local weight per prime, as before. -/

/-- The local weight of the two-fold tilt at one prime. -/
noncomputable def localTilt₂ (s₁ s₂ : ℂ) (p : Nat.Primes) (z : ℂ) : ℝ :=
  localTilt s₁ p z + localTilt s₂ p z

lemma localTilt₂_apply (s₁ s₂ : ℂ) (p : Nat.Primes) (z : ℂ) :
    localTilt₂ s₁ s₂ p z = localTilt s₁ p z + localTilt s₂ p z := rfl

lemma measurable_localTilt₂ (s₁ s₂ : ℂ) (p : Nat.Primes) :
    Measurable (localTilt₂ s₁ s₂ p) :=
  (measurable_localTilt s₁ p).add (measurable_localTilt s₂ p)

lemma tiltExponent₂_ae_eq_sum {X : ℕ → Ω → ℂ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    tiltExponent₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂
      =ᵐ[μ] fun ω => ∑ p ∈ primesBelowSub y, localTilt₂ s₁ s₂ p (X (p : ℕ) ω) := by
  filter_upwards [tiltExponent_ae_eq_sum hX y hs₁, tiltExponent_ae_eq_sum hX y hs₂]
    with ω h1 h2
  rw [tiltExponent₂, h1, h2,
    ← sum_primesBelowSub y (fun p => 2 * localLog ((p : ℂ) ^ (-s₁)) (X p ω)),
    ← sum_primesBelowSub y (fun p => 2 * localLog ((p : ℂ) ^ (-s₂)) (X p ω)),
    ← Finset.sum_add_distrib]
  rfl

/-- The two-fold tilted measure in the shape the factorisation results consume. -/
lemma tiltedMeasure₂_eq_tilted_finsetSum {X : ℕ → Ω → ℂ} (hX : IsSteinhausPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ
      = μ.tilted fun ω => ∑ p ∈ primesBelowSub y, localTilt₂ s₁ s₂ p (X (p : ℕ) ω) :=
  tilted_congr (tiltExponent₂_ae_eq_sum hX y hs₁ hs₂)

/-- Each two-fold local weight is integrable: it is the product of two weights each bounded on the
circle, so the bound is the product of the two one-fold bounds. -/
lemma integrable_exp_localTilt₂ {X : ℕ → Ω → ℂ} (hX : IsSteinhausPrimeValues X μ)
    (p : Nat.Primes) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    Integrable (fun ω => Real.exp (localTilt₂ s₁ s₂ p (X (p : ℕ) ω))) μ := by
  have hprob := hX.isProbabilityMeasure
  have hw₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₁
  have hw₂ : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₂
  have hae : ∀ᵐ ω ∂μ, ‖X (p : ℕ) ω‖ = 1 := by
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_steinhausLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  refine (memLp_top_of_bound
    (((measurable_localTilt₂ s₁ s₂ p).comp (hX.measurable (p : ℕ) p.2)).exp.aestronglyMeasurable)
    ((((1 - ‖((p : ℕ) : ℂ) ^ (-s₁)‖)⁻¹) ^ 2) * (((1 - ‖((p : ℕ) : ℂ) ^ (-s₂)‖)⁻¹) ^ 2))
    ?_).integrable le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Function.comp_apply,
    localTilt₂_apply, Real.exp_add]
  exact mul_le_mul (exp_two_localLog_le hω hw₁) (exp_two_localLog_le hω hw₂)
    (Real.exp_nonneg _) (by positivity)

/-- **The values at the primes stay independent under the two-fold tilt.**  Same proof as the
one-fold case: the exponent is still one local weight per prime. -/
theorem IsSteinhausPrimeValues.iIndepFun_tiltedMeasure₂ {X : ℕ → Ω → ℂ}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    iIndepFun (fun p : Nat.Primes => X (p : ℕ))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  rw [tiltedMeasure₂_eq_tilted_finsetSum hX y hs₁ hs₂]
  exact iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
    (X := fun p : Nat.Primes => X (p : ℕ)) (g := localTilt₂ s₁ s₂)
    hX.iIndep (fun p => hX.measurable (p : ℕ) p.2) (measurable_localTilt₂ s₁ s₂)
    (fun p _ => integrable_exp_localTilt₂ hX p hs₁ hs₂)

/-- **The law of `f(p)` under the two-fold tilt.**  For `p < y` it is `steinhausLaw` tilted by
`localTilt₂`, i.e. by the *product* of the two Poisson kernels.

Its moments are estimated in `RMF/EulerProduct/TwoPointTiltLaw.lean`.  Writing it as a tilt of the
one-fold tilted law (`MeasureTheory.tilted_tilted`) lets the one-point local moments of
`RMF/EulerProduct/TiltedLaw.lean` be reused, the second kernel being a perturbation. -/
theorem IsSteinhausPrimeValues.map_tiltedMeasure₂ {X : ℕ → Ω → ℂ}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) :
    (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ).map (X (p : ℕ))
      = steinhausLaw.tilted (localTilt₂ s₁ s₂ p) := by
  rw [tiltedMeasure₂_eq_tilted_finsetSum hX y hs₁ hs₂,
    map_tilted_finsetSum_of_mem (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun q : Nat.Primes => X (q : ℕ)) (g := localTilt₂ s₁ s₂)
      hX.iIndep (fun q => hX.measurable (q : ℕ) q.2) (measurable_localTilt₂ s₁ s₂)
      (fun q _ => integrable_exp_localTilt₂ hX q hs₁ hs₂) hp,
    (hX.hasLaw (p : ℕ) p.2).map_eq]

/-- **The two-fold weight in closed form.**  As in the one-fold case this is only an a.e.
identity, `Real.log 0` being `0`. -/
lemma IsSteinhausRMF.exp_tiltExponent₂_ae_eq (hf : IsSteinhausRMF f μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    (fun ω => Real.exp (tiltExponent₂ f y s₁ s₂ ω))
      =ᵐ[μ] fun ω => ‖randomEulerProduct f y s₁ ω‖ ^ 2 * ‖randomEulerProduct f y s₂ ω‖ ^ 2 := by
  filter_upwards [hf.exp_tiltExponent_ae_eq y hs₁, hf.exp_tiltExponent_ae_eq y hs₂]
    with ω h1 h2
  rw [tiltExponent₂, Real.exp_add, h1, h2]

/-- **The transfer under the two-fold tilt**: the weight is the product `‖F(s₁)‖²‖F(s₂)‖²`, and
the normaliser is its expectation. -/
theorem IsSteinhausRMF.integral_tiltedMeasure₂ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hf : IsSteinhausRMF f μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) (g : Ω → E) :
    (∫ ω, g ω ∂(tiltedMeasure₂ f y s₁ s₂ μ))
      = (∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ)⁻¹
          • ∫ ω, (‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2) • g ω ∂μ := by
  have hZ : (∫ ω, Real.exp (tiltExponent₂ f y s₁ s₂ ω) ∂μ)
      = ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
          * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ :=
    integral_congr_ae (hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂)
  rw [tiltedMeasure₂, integral_tilted, hZ, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂] with ω hω
  rw [hω, div_eq_inv_mul, mul_smul]

/-- The real-valued transfer, in Harper's quotient form. -/
theorem IsSteinhausRMF.integral_tiltedMeasure₂_real (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (g : Ω → ℝ) :
    (∫ ω, g ω ∂(tiltedMeasure₂ f y s₁ s₂ μ))
      = (∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 * g ω ∂μ)
          / ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ := by
  rw [hf.integral_tiltedMeasure₂ y hs₁ hs₂ g, smul_eq_mul, inv_mul_eq_div]
  simp only [smul_eq_mul]

end RMF
