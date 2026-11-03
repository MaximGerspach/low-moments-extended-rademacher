/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTwoPointTiltLaw
import RMF.EulerProduct.RademacherTiltedPrimes
import RMF.EulerProduct.TwoPointTilt

/-!
# The two-fold Rademacher tilt, indexed by the primes

The layer between `RMF/EulerProduct/RademacherTwoPointTiltLaw.lean` — which computes the two-fold
tilted law at a single prime — and the pair block statistics, which need the primes to stay
independent under `RMF.tiltedMeasure₂` and need each one's law to be that tilted local law.

`RMF.tiltedMeasure₂` and `RMF.tiltExponent₂` are generic in the multiplicative function, so no new
definition of the measure is needed; what is needed is the transport, and this file is
`RMF/EulerProduct/TwoPointTilt.lean`'s Steinhaus half rebuilt on
`RMF/EulerProduct/RademacherTiltedPrimes.lean`'s one-fold argument.

Both precedents are followed exactly: the only fact either tilt needs of the law is
`∀ᵐ z ∂ν, ‖z‖ = 1`, here `RMF.norm_eq_one_rademacherLaw`.
Everything else is the generic factorisation machinery of `RMF/Probability/Tilting.lean`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The local weight of the two-fold tilt -/

/-- The local weight of the two-fold Rademacher tilt at one prime,
`2 log‖1 + z p^{-s₁}‖ + 2 log‖1 + z p^{-s₂}‖`.  The counterpart of `RMF.localTilt₂`. -/
noncomputable def localTiltAdd₂ (s₁ s₂ : ℂ) (p : Nat.Primes) (z : ℂ) : ℝ :=
  localTiltAdd s₁ p z + localTiltAdd s₂ p z

lemma localTiltAdd₂_apply (s₁ s₂ : ℂ) (p : Nat.Primes) (z : ℂ) :
    localTiltAdd₂ s₁ s₂ p z = localTiltAdd s₁ p z + localTiltAdd s₂ p z := rfl

lemma measurable_localTiltAdd₂ (s₁ s₂ : ℂ) (p : Nat.Primes) :
    Measurable (localTiltAdd₂ s₁ s₂ p) :=
  (measurable_localTiltAdd s₁ p).add (measurable_localTiltAdd s₂ p)

/-- **The single point where the law enters**, as in the one-fold case: each two-fold local weight
is a product of two weights bounded on the circle. -/
lemma integrable_exp_localTiltAdd₂ {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (p : Nat.Primes) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    Integrable (fun ω => Real.exp (localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω))) μ := by
  have hprob := hX.isProbabilityMeasure
  have hw₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₁
  have hw₂ : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₂
  have hae : ∀ᵐ ω ∂μ, ‖X (p : ℕ) ω‖ = 1 := by
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  refine (memLp_top_of_bound
    (((measurable_localTiltAdd₂ s₁ s₂ p).comp
      (hX.measurable (p : ℕ) p.2)).exp.aestronglyMeasurable)
    ((1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖) ^ 2 * (1 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Function.comp_apply,
    localTiltAdd₂_apply, Real.exp_add]
  exact mul_le_mul (exp_two_localLogAdd_le hω hw₁) (exp_two_localLogAdd_le hω hw₂)
    (Real.exp_nonneg _) (by positivity)

/-! ### The two-fold tilt as a sum over the primes -/

/-- **The two-fold tilt exponent is a sum of functions of the individual values.** -/
lemma tiltExponent₂_ae_eq_sum_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    tiltExponent₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂
      =ᵐ[μ] fun ω => ∑ p ∈ primesBelowSub y, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω) := by
  filter_upwards [tiltExponent_ae_eq_sum_rademacher hX y hs₁,
    tiltExponent_ae_eq_sum_rademacher hX y hs₂] with ω h1 h2
  rw [tiltExponent₂, h1, h2,
    ← sum_primesBelowSub y (fun p => 2 * localLogAdd ((p : ℂ) ^ (-s₁)) (X p ω)),
    ← sum_primesBelowSub y (fun p => 2 * localLogAdd ((p : ℂ) ^ (-s₂)) (X p ω)),
    ← Finset.sum_add_distrib]
  rfl

/-- The two-fold tilted measure in the shape the factorisation results consume. -/
lemma tiltedMeasure₂_eq_tilted_finsetSum_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ
      = μ.tilted fun ω => ∑ p ∈ primesBelowSub y, localTiltAdd₂ s₁ s₂ p (X (p : ℕ) ω) :=
  tilted_congr (tiltExponent₂_ae_eq_sum_rademacher hX y hs₁ hs₂)

/-! ### What the two-fold tilt preserves, and what it changes -/

/-- **The values at distinct primes stay independent under the two-fold tilt.**  Same proof as the
one-fold case: the exponent is still one local weight per prime. -/
theorem iIndepFun_tiltedMeasure₂_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    iIndepFun (fun p : Nat.Primes => X (p : ℕ))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  rw [tiltedMeasure₂_eq_tilted_finsetSum_rademacher hX y hs₁ hs₂]
  exact iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
    (X := fun p : Nat.Primes => X (p : ℕ)) (g := localTiltAdd₂ s₁ s₂)
    hX.iIndep (fun p => hX.measurable (p : ℕ) p.2) (measurable_localTiltAdd₂ s₁ s₂)
    (fun p _ => integrable_exp_localTiltAdd₂ hX p hs₁ hs₂)

/-- **The two-fold tilt weight is integrable**, so the tilt is a probability measure.  The
exponent is a sum of local weights over `primesBelowSub y`, each bounded by a product of two circle
bounds. -/
lemma integrable_exp_tiltExponent₂_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    Integrable (fun ω =>
      Real.exp (tiltExponent₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ ω)) μ := by
  have hprob := hX.isProbabilityMeasure
  have hrmf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hae : ∀ᵐ ω ∂μ, ∀ p ∈ primesBelowSub y, ‖X (p : ℕ) ω‖ = 1 := by
    refine (Filter.eventually_all_finset _).2 fun p _ => ?_
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  have hm : AEStronglyMeasurable (fun ω =>
      Real.exp (tiltExponent₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ ω)) μ :=
    (((hrmf.aemeasurable_logNormEuler y hs₁).const_mul 2).add
      ((hrmf.aemeasurable_logNormEuler y hs₂).const_mul 2)).exp.aestronglyMeasurable
  refine (memLp_top_of_bound hm (∏ p ∈ primesBelowSub y,
    (1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖) ^ 2 * (1 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2) ?_).integrable le_top
  filter_upwards [tiltExponent₂_ae_eq_sum_rademacher hX y hs₁ hs₂, hae] with ω hω hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hω, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
  rw [localTiltAdd₂_apply, Real.exp_add]
  exact mul_le_mul (exp_two_localLogAdd_le (hn p hp) (norm_prime_cpow_neg_lt_one p.2 hs₁))
    (exp_two_localLogAdd_le (hn p hp) (norm_prime_cpow_neg_lt_one p.2 hs₂))
    (Real.exp_nonneg _) (by positivity)

/-- **The two-fold tilt is a probability measure**, in the `IsRademacherPrimeValues` phrasing. -/
theorem isProbabilityMeasure_tiltedMeasure₂_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    IsProbabilityMeasure
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  have hprob := hX.isProbabilityMeasure
  exact isProbabilityMeasure_tilted (integrable_exp_tiltExponent₂_rademacher hX y hs₁ hs₂)

/-- **The local logarithms stay independent under the two-fold tilt**, at arbitrary weights —
which is what the pair Lindeberg telescope consumes. -/
theorem iIndepFun_localLogAdd_tiltedMeasure₂_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) (w : Nat.Primes → ℂ) :
    iIndepFun (fun (p : Nat.Primes) (ω : Ω) => localLogAdd (w p) (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  (iIndepFun_tiltedMeasure₂_rademacher hX y hs₁ hs₂).comp (fun p => localLogAdd (w p))
    (fun p => measurable_localLogAdd (w p))

/-- **The law of `f p` under the two-fold tilt.**  For `p < y` it is `rademacherLaw` tilted by
`RMF.localTiltAdd₂` — the two-atom law whose moments
`RMF/EulerProduct/RademacherTwoPointTiltLaw.lean` computes exactly. -/
theorem map_tiltedMeasure₂_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) :
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ).map (X (p : ℕ))
      = rademacherLaw.tilted (localTiltAdd₂ s₁ s₂ p) := by
  rw [tiltedMeasure₂_eq_tilted_finsetSum_rademacher hX y hs₁ hs₂,
    map_tilted_finsetSum_of_mem (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun q : Nat.Primes => X (q : ℕ)) (g := localTiltAdd₂ s₁ s₂)
      hX.iIndep (fun q => hX.measurable (q : ℕ) q.2) (measurable_localTiltAdd₂ s₁ s₂)
      (fun q _ => integrable_exp_localTiltAdd₂ hX q hs₁ hs₂) hp,
    (hX.hasLaw (p : ℕ) p.2).map_eq]

/-! ### The two-fold tilt in the `RMF.IsRademacherRMF` phrasing

Each of the four statements below is the `RMF.IsRademacherRMF` face of a fact this file proves at
the level of prime values; `RMF.IsRademacherRMF.isProbabilityMeasure_tiltedMeasure₂` is
`RMF.isProbabilityMeasure_tiltedMeasure₂_rademacher` in that phrasing.  That is why they sit here
and not beside their Steinhaus twins in `RMF/EulerProduct/TwoPointTilt.lean`, which does not import
this file. -/

section IsRademacherRMF

variable {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-- **The two-fold weight in closed form.**  As in the one-fold case this is only an a.e.
identity, `Real.log 0` being `0` — and for Rademacher the exceptional set is genuinely reachable,
since `1 + z a` vanishes when `z a = -1`. -/
lemma IsRademacherRMF.exp_tiltExponent₂_ae_eq (hf : IsRademacherRMF f μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    (fun ω => Real.exp (tiltExponent₂ f y s₁ s₂ ω))
      =ᵐ[μ] fun ω => ‖randomEulerProduct f y s₁ ω‖ ^ 2 * ‖randomEulerProduct f y s₂ ω‖ ^ 2 := by
  filter_upwards [hf.exp_tiltExponent_ae_eq y hs₁, hf.exp_tiltExponent_ae_eq y hs₂]
    with ω h1 h2
  rw [tiltExponent₂, Real.exp_add, h1, h2]

/-- **The transfer under the two-fold tilt.**  The weight is the product `‖F(s₁)‖²‖F(s₂)‖²` and
the normaliser is its expectation. -/
theorem IsRademacherRMF.integral_tiltedMeasure₂ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hf : IsRademacherRMF f μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
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
theorem IsRademacherRMF.integral_tiltedMeasure₂_real (hf : IsRademacherRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (g : Ω → ℝ) :
    (∫ ω, g ω ∂(tiltedMeasure₂ f y s₁ s₂ μ))
      = (∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 * g ω ∂μ)
          / ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ := by
  rw [hf.integral_tiltedMeasure₂ y hs₁ hs₂ g, smul_eq_mul, inv_mul_eq_div]
  simp only [smul_eq_mul]

/-- **`P~₂` is a probability measure**, in the `RMF.IsRademacherRMF` phrasing. -/
theorem IsRademacherRMF.isProbabilityMeasure_tiltedMeasure₂ (hf : IsRademacherRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    IsProbabilityMeasure (tiltedMeasure₂ f y s₁ s₂ μ) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂

end IsRademacherRMF

end RMF
