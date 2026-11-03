/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedFirstMoment
import RMF.EulerProduct.RademacherTiltedPrimes

/-!
# The tilt in closed form, for the Rademacher random multiplicative function

`Probability/ChaosFirstMoment.lean` uses exactly three `IsSteinhausRMF` members —
`setIntegral_normSq_eq`, `integral_norm_randomEulerProduct_sq'`, and
`integral_normSq_shiftLine_eq`.  The second already has a Rademacher counterpart
(`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_sq'`); this file supplies the other two.

The tilt facts they rest on are the `RMF.IsRademacherRMF` face of `RMF/EulerProduct/Tilted.lean`,
each beside its Steinhaus twin.

## Why the Rademacher versions are shorter

The Steinhaus Euler product is `∏ (1 - f p·p^{-s})⁻¹`, so the closed form is an a.e. identity
holding on the unimodularity event, and non-vanishing needs the inverted element to stay away from
zero.  The Rademacher product is `∏ (1 + f p·p^{-s})`, and `RMF.eulerProduct_squarefreeExtension`
makes that a **pointwise** identity — no event to carry.  Only non-vanishing still needs
`‖f p‖ ≤ 1`, and it needs it in the same one place.

Positivity of the normalising constant is also easier: `∏ (1 + ‖p^{-s}‖²)` is a product of terms
above `1`, where the Steinhaus `∏ (1 - ‖p^{-s}‖²)⁻¹` needs each `‖p^{-s}‖ < 1` first.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-- **The tilt identity for the Rademacher RMF.**  The restricted second moment of the Euler
product is the tilted measure of the set times the unrestricted second moment — an identity, not an
estimate.  The mirror of `RMF.IsSteinhausRMF.setIntegral_normSq_eq`. -/
lemma IsRademacherRMF.setIntegral_normSq_eq (hf : IsRademacherRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω in A, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
      = (tiltedMeasure f y s μ A).toReal * ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ := by
  have hZ0 : (0 : ℝ) < ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ :=
    hf.integral_norm_randomEulerProduct_sq_pos y s
  have hA0 : (0 : ℝ) ≤ ∫ ω in A, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ :=
    setIntegral_nonneg hA fun _ _ => by positivity
  rw [hf.tiltedMeasure_apply y hs hA, ENNReal.toReal_ofReal (div_nonneg hA0 hZ0.le)]
  field_simp

/-- **The second moment does not see the height.**  `‖p^{-(1/2+σ+it)}‖ = p^{-(1/2+σ)}` for every
`t`, so the product is the same on every horizontal line.  The mirror of
`RMF.IsSteinhausRMF.integral_normSq_shiftLine_eq`. -/
lemma IsRademacherRMF.integral_normSq_shiftLine_eq (hf : IsRademacherRMF f μ) (y : ℕ) {σ : ℝ}
    (t t' : ℝ) :
    (∫ ω, ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2 ∂μ)
      = ∫ ω, ‖randomEulerProduct f y (shiftLine σ t') ω‖ ^ 2 ∂μ := by
  rw [hf.integral_norm_randomEulerProduct_sq y (shiftLine σ t),
    hf.integral_norm_randomEulerProduct_sq y (shiftLine σ t')]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hppos : 0 < p := (Nat.prime_of_mem_primesBelow hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hppos, Complex.norm_natCast_cpow_of_pos hppos,
    Complex.neg_re, Complex.neg_re, re_shiftLine, re_shiftLine]

/-! ### The product integrability behind the `t`-integral

The uncurried indicator is integrable on `Ω × T`, which is what `integral_integral_swap` needs and
what makes the slice means integrable in `t`.  The Steinhaus proof
(`RMF.integrable_uncurry_indicator_normSq`) spends most of its length carrying the unimodularity
event through the product with `Measure.ae_prod_iff_ae_ae`, because there the closed form of the
Euler product holds only on that event.

**On the Rademacher side that whole block disappears.**
`RMF.eulerProduct_squarefreeExtension` is a pointwise identity, so measurability is a `simp only`
away and there is no event to lift to `Ω × T`. -/

/-- **The product integrability behind the `t`-integral**, for the Rademacher RMF: the mirror of
`RMF.integrable_uncurry_indicator_normSq`, without the unimodularity event.  The unused hypothesis
`_hσ0 : 0 < 1/2 + σ` is kept for symmetry with the Steinhaus statement; the Rademacher factors
`1 + Y_p p^{-s}` are bounded on every line. -/
lemma integrable_uncurry_indicator_normSq_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (_hσ0 : 0 < 1 / 2 + σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2})
    {T : Set ℝ} (hTfin : volume T ≠ ⊤) :
    Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) =>
        Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω)
      (ν.prod (volume.restrict T)) := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  -- the closed form is pointwise, so measurability needs no event
  have hpt : ∀ (t : ℝ) (ω : Ω'),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
      = ‖∏ p ∈ Nat.primesBelow y, (1 + Y p ω * ((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))‖ ^ 2 := by
    intro t ω
    congr 2
    rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hmeas' : Measurable fun q : Ω' × ℝ => Set.indicator {q : Ω' × ℝ | q.1 ∈ L q.2}
      (fun q => ‖∏ p ∈ Nat.primesBelow y,
        (1 + Y p q.1 * ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)))‖ ^ 2) q := by
    refine Measurable.indicator ?_ hSmeas
    refine (Finset.measurable_prod _ fun p hp => ?_).norm.pow_const 2
    have h1 : Measurable fun q : Ω' × ℝ => Y p q.1 :=
      (hY.measurable p (Nat.prime_of_mem_primesBelow hp)).comp measurable_fst
    have h2 : Measurable fun q : Ω' × ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      ((continuous_cpow_neg_shiftLine (Nat.prime_of_mem_primesBelow hp).pos σ).measurable).comp
        measurable_snd
    exact (h1.mul h2).const_add 1
  have hAEm : AEStronglyMeasurable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    refine hmeas'.aestronglyMeasurable.congr (Filter.Eventually.of_forall ?_)
    rintro ⟨ω, t⟩
    simp only [Function.uncurry_apply_pair]
    by_cases hmem : ω ∈ L t
    · rw [Set.indicator_of_mem (show (ω, t) ∈ {q : Ω' × ℝ | q.1 ∈ L q.2} from hmem),
        Set.indicator_of_mem hmem]
      exact (hpt t ω).symm
    · rw [Set.indicator_of_notMem (show (ω, t) ∉ {q : Ω' × ℝ | q.1 ∈ L q.2} from hmem),
        Set.indicator_of_notMem hmem]
  -- per-height integrability, and the uniform bound on the slice means
  have hslice : ∀ t : ℝ, Integrable (fun ω => Set.indicator (L t) (g t) ω) ν := fun t =>
    ((hf'.integrable_norm_randomEulerProduct_sq y (shiftLine σ t)).indicator (hLmeas t)).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hnn : ∀ t ω, 0 ≤ Set.indicator (L t) (g t) ω :=
    fun t ω => Set.indicator_nonneg (fun _ _ => by rw [hgdef]; positivity) ω
  have hsliceval : ∀ t : ℝ, (∫ ω, ‖Set.indicator (L t) (g t) ω‖ ∂ν) ≤ ∫ ω, g 0 ω ∂ν := by
    intro t
    have hrw : (fun ω => ‖Set.indicator (L t) (g t) ω‖) = fun ω => Set.indicator (L t) (g t) ω :=
      funext fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ω)]
    rw [hrw, integral_indicator (hLmeas t), hgdef]
    simp only
    rw [hf'.integral_normSq_shiftLine_eq y (σ := σ) 0 t]
    exact setIntegral_le_integral
      (hf'.integrable_norm_randomEulerProduct_sq y (shiftLine σ t))
      (Filter.Eventually.of_forall fun ω => by positivity)
  refine (integrable_prod_iff' hAEm).2 ⟨Filter.Eventually.of_forall hslice, ?_⟩
  refine Integrable.mono' (integrable_const (∫ ω, g 0 ω ∂ν))
    (hAEm.norm.prod_swap).integral_prod_right' ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => by
    rw [Real.norm_eq_abs]; positivity)]
  exact hsliceval t

/-! ### The measurability plumbing, for the additive local factor

The measurability lemmas of `Probability/RestrictedFirstMoment.lean` take an arbitrary
`Y : ℕ → Ω' → ℂ` but hardcode `RMF.localLog`, so the two below are their `RMF.localLogAdd` twins.
`RMF.measurableSet_freeStartBarrier` is stated over an abstract `X : ℕ → Ω' → ℝ` and is reused
verbatim. -/

/-- The additive block sum is jointly measurable in `(ω, t)`.  The mirror of
`RMF.measurable_blockSum_uncurry`; one step shorter, since `localLogAdd` has no leading negation. -/
lemma measurable_blockSumAdd_uncurry {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ))) (σ : ℝ)
    (B : Finset Nat.Primes) :
    Measurable fun q : Ω' × ℝ => ∑ p ∈ B,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1) := by
  refine Finset.measurable_sum _ fun p _ => ?_
  have hrw : (fun q : Ω' × ℝ =>
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1))
      = fun q : Ω' × ℝ => Real.log ‖1 + Y ((p : Nat.Primes) : ℕ) q.1
          * (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)))‖ := rfl
  rw [hrw]
  have h1 : Measurable fun q : Ω' × ℝ => Y ((p : Nat.Primes) : ℕ) q.1 :=
    (hY p).comp measurable_fst
  have h2 : Measurable fun q : Ω' × ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
    ((continuous_cpow_neg_shiftLine (p : Nat.Primes).2.pos σ).measurable).comp measurable_snd
  exact Real.measurable_log.comp ((h1.mul h2).const_add 1).norm

/-- The additive free-start barrier event, uncurried, is measurable.  The mirror of
`RMF.measurableSet_freeStartBarrier_uncurry`.  Its non-uncurried companion
`RMF.measurableSet_freeStartBarrier` is stated over an abstract real walk and is reused verbatim. -/
lemma measurableSet_freeStartBarrierAdd_uncurry {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ))) (σ : ℝ) (θ : ℝ) (r n : ℕ)
    (u v : ℕ → ℝ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r ≤ j → j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (u j) (v j)}} := by
  have hrw : {q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r ≤ j → j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (u j) (v j)}}
      = ⋂ j ∈ Set.Icc r n, {q : Ω' × ℝ | (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1))
            ∈ Set.Icc (u j) (v j)} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc, walk, Finset.sum_apply]
    constructor
    · intro h j hj
      exact h j hj.1 hj.2
    · intro h j hj1 hj2
      exact h j ⟨hj1, hj2⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_
  have hm : Measurable fun q : Ω' × ℝ => ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1) :=
    Finset.measurable_sum _ fun m _ => measurable_blockSumAdd_uncurry hY σ _
  exact hm measurableSet_Icc

end RMF
