/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedFirstMoment
import RMF.EulerProduct.TwoPointTilt
import RMF.Reduction.Periodisation
import RMF.Probability.Chaining
import RMF.Probability.MaximalBarrier
import RMF.EulerProduct.TwoPoint
import RMF.NumberTheory.MertensProduct
import RMF.Probability.BlockComparisonPair

/-!
# Key Proposition 5: the expanded square, the crude range, and Proposition 7

Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654), proof of Key
Proposition 5.  With `X = ∫_T 1_{L(t)}‖F(1/2+σ+it)‖² dt`, expanding the square gives the
identity `RMF.integral_sq_setIntegral_indicator_normSq_eq`,

`E[X²] = ∫_T ∫_T P~₂(L(t) ∩ L(u))·E[‖F_t‖²‖F_u‖²] du dt`,

where `P~₂ = RMF.tiltedMeasure₂` reweights by `‖F_t‖²‖F_u‖²`: a two-point barrier probability,
bounded through Proposition 7, times the two-point moment, which is Harper's (5.1)
(`RMF.exists_abs_log_integral_two_point_le`).

The proof runs through this file, `Ranges.lean` and `Assembly.lean` to
`RMF/Probability/RestrictedSecondMoment.lean`.  This file contains:

* the two-fold tilt as a measure, and the identity above; its Fubini step costs `0 ≤ σ` and no
  moment of `‖F‖⁴`, since `‖F_y(s)‖ ≤ RMF.eulerBound y` on the unimodularity event for
  `Re s ≥ 1/2`;
* Harper's (5.2), the deterministic bound on the barrier event
  (`RMF.normSq_randomEulerProductIco_le_of_mem_barrierEvent`);
* the split index at `e^{1/|t|}` and Harper's `h(n) = -2\log n` (`RMF.harperHf`);
* the low and high factors of the crude range, where both indicators are discarded;
* Harper's `R(t)`, the two drifts of the two-fold tilt above the shift, the regression slope and
  the shear budget;
* Proposition 7 for the Steinhaus RMF, upper bound (`RMF.exists_proposition7_upper_steinhaus`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The two-fold tilt, at the level of measures -/

/-- **Harper's display at two points.**  `P~₂(A)` is the `‖F(s₁)‖²‖F(s₂)‖²`-weighted measure of
`A`, normalised.  The proof is `RMF.IsSteinhausRMF.tiltedMeasure_apply` verbatim, with the
one-fold weight replaced by the two-fold one: the tilt exponent is a sum, so its exponential is
the product, and nothing else changes. -/
theorem IsSteinhausRMF.tiltedMeasure₂_apply (hf : IsSteinhausRMF f μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {A : Set Ω} (hA : MeasurableSet A) :
    tiltedMeasure₂ f y s₁ s₂ μ A
      = ENNReal.ofReal ((∫ ω in A, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ)
          / ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ) := by
  have hZ : (∫ ω, Real.exp (tiltExponent₂ f y s₁ s₂ ω) ∂μ)
      = ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2 * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ :=
    integral_congr_ae (hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂)
  rw [tiltedMeasure₂, tilted_apply_eq_ofReal_integral' _ hA, hZ, ← integral_div]
  refine congrArg ENNReal.ofReal (integral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae (hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂)] with ω hω
  rw [hω]

/-- **The two-fold normaliser is positive**: `0 < E[‖F(s₁)‖²‖F(s₂)‖²]`, as needed to undo the
division in `RMF.IsSteinhausRMF.tiltedMeasure₂_apply`.  Not via (5.1): the two-fold tilt is a
probability measure, so `∫ 1 dP~₂ = 1`, while the transfer identity gives
`E[‖F₁‖²‖F₂‖²]/E[‖F₁‖²‖F₂‖²]`, which would be `0` if the denominator were `0`. -/
theorem IsSteinhausRMF.integral_normSq_mul_normSq_pos (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    0 < ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2 * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ := by
  haveI := hf.isProbabilityMeasure_tiltedMeasure₂ y hs₁ hs₂
  have h := hf.integral_tiltedMeasure₂_real y hs₁ hs₂ (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  have hnn : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
      * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  rcases hnn.lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, div_zero] at h
    exact absurd h one_ne_zero

/-- **The two-point transfer identity**: `∫_A ‖F(s₁)‖²‖F(s₂)‖² = P~₂(A)·E‖F(s₁)‖²‖F(s₂)‖²`.
This is `RMF.IsSteinhausRMF.setIntegral_normSq_eq` at two points: a restricted moment is a
barrier probability times an unrestricted moment, with no loss. -/
theorem IsSteinhausRMF.setIntegral_normSq_mul_normSq_eq (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω in A, ‖randomEulerProduct f y s₁ ω‖ ^ 2 * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ)
      = (tiltedMeasure₂ f y s₁ s₂ μ A).toReal
          * ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ := by
  have hZ0 := hf.integral_normSq_mul_normSq_pos y hs₁ hs₂
  have hA0 : (0 : ℝ) ≤ ∫ ω in A, ‖randomEulerProduct f y s₁ ω‖ ^ 2
      * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ :=
    setIntegral_nonneg hA fun _ _ => by positivity
  rw [hf.tiltedMeasure₂_apply y hs₁ hs₂ hA, ENNReal.toReal_ofReal (div_nonneg hA0 hZ0.le)]
  field_simp

/-- The form the height integrals consume: two indicators at two heights, whose product is the
indicator of the intersection.  `L t ∩ L u` is the event that the walk stays in the tube at both
heights; Proposition 7 bounds its two-fold tilted probability. -/
theorem IsSteinhausRMF.integral_indicator_mul_indicator_normSq_eq (hf : IsSteinhausRMF f μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ ω, Set.indicator A (fun ω => ‖randomEulerProduct f y s₁ ω‖ ^ 2) ω
        * Set.indicator B (fun ω => ‖randomEulerProduct f y s₂ ω‖ ^ 2) ω ∂μ)
      = (tiltedMeasure₂ f y s₁ s₂ μ (A ∩ B)).toReal
          * ∫ ω, ‖randomEulerProduct f y s₁ ω‖ ^ 2
              * ‖randomEulerProduct f y s₂ ω‖ ^ 2 ∂μ := by
  have hprod : ∀ ω : Ω, Set.indicator A (fun ω => ‖randomEulerProduct f y s₁ ω‖ ^ 2) ω
      * Set.indicator B (fun ω => ‖randomEulerProduct f y s₂ ω‖ ^ 2) ω
      = Set.indicator (A ∩ B) (fun ω => ‖randomEulerProduct f y s₁ ω‖ ^ 2
          * ‖randomEulerProduct f y s₂ ω‖ ^ 2) ω :=
    fun ω => (Set.inter_indicator_mul _ _ ω).symm
  simp_rw [hprod]
  rw [integral_indicator (hA.inter hB), hf.setIntegral_normSq_mul_normSq_eq y hs₁ hs₂
    (hA.inter hB)]

/-! ### Exchanging the expectation with the heights

Fubini joins the two-fold tilt to the expansion of the square; the work is integrability on
`Ω × T`.  On the unimodularity event `RMF.norm_randomEulerProduct_le` bounds `‖F_y(s)‖` by the
height-free constant `RMF.eulerBound y = ∏_{p<y}(1-p^{-1/2})⁻¹` whenever `Re s ≥ 1/2`, so the
integrand is a.e. bounded and no moment of `‖F‖⁴` is needed.  `Re s ≥ 1/2` asks `0 ≤ σ`; Key
Proposition 5 has `σ = 4V/\log x > 0`.

The swap is made twice through one lemma on `Ω × T`: first with the bounded weight `ψ = X`, then
with `ψ = 1_{L t}‖F_t‖²`. -/

/-- **The deterministic bound, uniform in the height.**
`RMF.IsSteinhausRMF.ae_norm_randomEulerProduct_le` gives this for one `s` at a time, with an
`s`-dependent null set.  Here the null set is the same
for every height — it is the unimodularity event, which does not see `s` at all — and that is
what lets the bound survive an integral over `t`. -/
lemma ae_forall_norm_randomEulerProduct_shiftLine_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂ν, ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖
        ≤ eulerBound y := by
  filter_upwards [ae_forall_norm_le_one hY norm_le_one_steinhausLaw y] with ω hω t
  exact norm_randomEulerProduct_le hω (by rw [re_shiftLine]; linarith)

/-- The same for the restricted weight `1_{L t}·‖F_t‖²`, which is what the height integral sees. -/
lemma ae_forall_norm_indicator_normSq_shiftLine_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') :
    ∀ᵐ ω ∂ν, ∀ t : ℝ, ‖Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω‖ ≤ eulerBound y ^ 2 := by
  filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_le hY y hσ] with ω hω t
  by_cases hmem : ω ∈ L t
  · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hω t) 2
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    exact sq_nonneg _

/-- **One swap.**  For a weight `ψ` that is a.e. bounded and a.e. strongly measurable in `ω`,
`E[ψ·∫_T 1_{L t}‖F_t‖² dt] = ∫_T E[ψ·1_{L t}‖F_t‖²] dt`.  Both applications of Fubini in
`RMF.integral_sq_setIntegral_indicator_normSq_eq` are this lemma, with `ψ = X` and then
`ψ = 1_{L t}‖F_t‖²`. -/
theorem integral_mul_setIntegral_indicator_normSq_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTfin : volume T ≠ ⊤)
    (ψ : Ω' → ℝ) (hψm : AEStronglyMeasurable ψ ν) {c : ℝ} (hψb : ∀ᵐ ω ∂ν, ‖ψ ω‖ ≤ c) :
    (∫ ω, ψ ω * (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
      = ∫ t in T, ∫ ω, ψ ω * Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω ∂ν := by
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  have hbase := integrable_uncurry_indicator_normSq hY y hσ0 L hLmeas hSmeas hTfin
  have hψprod : AEStronglyMeasurable (fun q : Ω' × ℝ => ψ q.1) (ν.prod (volume.restrict T)) :=
    hψm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hψbprod : ∀ᵐ q ∂(ν.prod (volume.restrict T)), ‖ψ q.1‖ ≤ c :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hψb
  have hInt : Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) => ψ ω * Set.indicator (L t)
      (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
        (shiftLine σ t) ω‖ ^ 2) ω) (ν.prod (volume.restrict T)) :=
    hbase.bdd_mul hψprod hψbprod
  rw [← integral_integral_swap hInt]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (integral_const_mul _ _).symm)

/-- **The second moment of the restricted chaos, expanded**, as in the first step of Harper's proof
of Key Proposition 5:
`E[X²] = ∫_T ∫_T P~₂(L t ∩ L u)·E[‖F_t‖²‖F_u‖²] du dt`, `X = ∫_T 1_{L t}‖F_t‖² dt`,
with `P~₂ = RMF.tiltedMeasure₂` at the two heights.  An identity.  The hypotheses are those of
`RMF.integrable_uncurry_indicator_normSq`, with `0 ≤ σ` in place of `0 < 1/2 + σ`. -/
theorem integral_sq_setIntegral_indicator_normSq_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTfin : volume T ≠ ⊤) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      = ∫ t in T, ∫ u in T,
          (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
            * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ t) ω‖ ^ 2
                * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν := by
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hsre : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; exact hσ0
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hbase := integrable_uncurry_indicator_normSq hY y hσ0 L hLmeas hSmeas hTfin
  have hbnd := ae_forall_norm_indicator_normSq_shiftLine_le hY y hσ L
  -- the outer weight `X`, bounded because the integrand is and `T` has finite measure
  have hXm : AEStronglyMeasurable (fun ω => ∫ t in T, Set.indicator (L t) (g t) ω) ν :=
    hbase.integral_prod_left.aestronglyMeasurable
  have hXb : ∀ᵐ ω ∂ν, ‖∫ t in T, Set.indicator (L t) (g t) ω‖
      ≤ eulerBound y ^ 2 * volume.real T := by
    filter_upwards [hbnd] with ω hω
    exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hTfin)
      fun t _ => hω t
  -- the first swap, peeling the outer copy of `X`
  have hexp : (∫ ω, (∫ t in T, Set.indicator (L t) (g t) ω) ^ 2 ∂ν)
      = ∫ ω, (∫ t in T, Set.indicator (L t) (g t) ω)
          * (∫ t in T, Set.indicator (L t) (g t) ω) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => sq _)
  rw [hexp, integral_mul_setIntegral_indicator_normSq_eq hY y hσ L hLmeas hSmeas hTfin _ hXm hXb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  -- the second swap, at a fixed outer height, then the two-fold tilt
  have hφm : AEStronglyMeasurable (fun ω => Set.indicator (L t) (g t) ω) ν :=
    ((hf'.integrable_norm_randomEulerProduct_sq y (hsre t)).indicator
      (hLmeas t)).aestronglyMeasurable
  have hφb : ∀ᵐ ω ∂ν, ‖Set.indicator (L t) (g t) ω‖ ≤ eulerBound y ^ 2 := by
    filter_upwards [hbnd] with ω hω
    exact hω t
  calc (∫ ω, (∫ u in T, Set.indicator (L u) (g u) ω) * Set.indicator (L t) (g t) ω ∂ν)
      = ∫ ω, Set.indicator (L t) (g t) ω * (∫ u in T, Set.indicator (L u) (g u) ω) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    _ = ∫ u in T, ∫ ω, Set.indicator (L t) (g t) ω * Set.indicator (L u) (g u) ω ∂ν :=
        integral_mul_setIntegral_indicator_normSq_eq hY y hσ L hLmeas hSmeas hTfin _ hφm hφb
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun u =>
        hf'.integral_indicator_mul_indicator_normSq_eq y (hsre t) (hsre u) (hLmeas t) (hLmeas u))

/-! ### Harper's (5.2), the deterministic bound

Harper's event `L(t)` constrains the partial products
`∏_{l=j}^{top}|I_l(1/2+4V/\log x+it)|` from both sides, and (5.2) uses only the upper constraint
at one index, so it holds pointwise on the event; the probabilistic estimates go to the rest, (5.3).

With `hf = RMF.harperHf`, `RMF.barrierEvent`'s upper envelope `v j = a + j - 2\log j` lies below
Harper's, which in upward indexing (`\log\log x_m = m + θ`) reads `a + (m+θ) - 2\log(m+θ)`; the
lower envelopes compare the same way.  So the barrier event is contained in Harper's, and (5.2)
below is stronger than his.

His `l` runs downward (`\log x_l = \log x/e^{l+1}`), the blocks here upward
(`\log x_m = e^{m+θ}`).  With `m = (⌊\log\log x⌋ - B - 2) - l` his split
`l₀ = \max\{⌊\log V⌋+3, ⌊\log(|t|\log x)⌋\}` becomes `j₀ = \min\{n - d, k(t)\}`, with
`d = ⌊\log V⌋+3` and `k(t) ≈ \log(1/|t|) - θ`. -/

/-- **The Euler product over a prime range does not vanish** at a point where the values are
unimodular.  Needed because `RMF.log_norm_randomEulerProductIco_eq` states an identity about
`\log‖F‖`, and turning `\log‖F‖ ≤ c` back into `‖F‖ ≤ e^c` needs `‖F‖ > 0`. -/
lemma norm_randomEulerProductIco_pos {Ω : Type*} {Y : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y, ‖Y p ω‖ ≤ 1) :
    0 < ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω) y₀ y s ω‖ := by
  rw [randomEulerProductIco_compMult_eq hs hω, norm_prod]
  refine Finset.prod_pos fun p hp => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
  rw [norm_inv]
  exact inv_pos.2 (norm_one_sub_mul_pos (hω p hp) hw)

/-- **The walk is the logarithm of the partial Euler product**, in block coordinates.

`RMF.log_norm_randomEulerProductIco_eq` says this for a range of primes and
`RMF.sum_primesIco_eq_sum_blocks` splits that range into blocks; composing them is what lets a
statement about `RMF.barrierEvent` — which speaks of the walk — be read as a statement about the
Euler product, which is what (5.2) needs. -/
lemma log_norm_randomEulerProductIco_eq_walk {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖
      = walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) j ω := by
  rw [log_norm_randomEulerProductIco_eq hs hω, walk_apply]
  exact sum_primesIco_eq_sum_blocks θ j fun p => localLog ((p : ℂ) ^ (-s)) (Y p ω)

/-- **Harper's (5.2), the deterministic bound.**  On the barrier event the partial Euler product
over the blocks below `j` is at most `e^{v j}` — the upper envelope, exponentiated.

Pointwise: no measure, no expectation, no hypothesis beyond membership.  The whole content is that
`RMF.barrierEvent` constrains the walk, the walk *is* `\log‖F‖`, and `\exp` is monotone. -/
theorem norm_randomEulerProductIco_le_of_mem_barrierEvent {Ω : Type*} {Y : ℕ → Ω → ℂ}
    (θ : ℝ) {n j : ℕ} {u v : ℕ → ℝ} {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), ‖Y p ω‖ ≤ 1)
    (hmem : ω ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) n u v)
    (h1 : 1 ≤ j) (hjn : j ≤ n) :
    ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖ ≤ Real.exp (v j) := by
  have hpos := norm_randomEulerProductIco_pos hs hω
  have hlog := log_norm_randomEulerProductIco_eq_walk θ j hs hω
  have hle := (hmem j h1 hjn).2
  calc ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖
      = Real.exp (Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (v j) := Real.exp_le_exp.2 (by rw [hlog]; exact hle)

/-- (5.2) in the squared form the integrand carries. -/
theorem normSq_randomEulerProductIco_le_of_mem_barrierEvent {Ω : Type*} {Y : ℕ → Ω → ℂ}
    (θ : ℝ) {n j : ℕ} {u v : ℕ → ℝ} {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), ‖Y p ω‖ ≤ 1)
    (hmem : ω ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) n u v)
    (h1 : 1 ≤ j) (hjn : j ≤ n) :
    ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖ ^ 2 ≤ Real.exp (v j) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _)
    (norm_randomEulerProductIco_le_of_mem_barrierEvent θ hs hω hmem h1 hjn) 2

/-! ### The split index

Harper splits the primes at `e^{1/|t|}`: below it the Euler products at heights `0` and
`t` nearly agree, above it they decouple.  In upward block indexing his
`l₀ = \max\{⌊\log V⌋+3, ⌊\log(|t|\log x)⌋\}` becomes `RMF.splitIndex`, with two properties:

* `RMF.splitIndex_le`: it stays inside the barrier's range, so (5.2) applies;
* `RMF.log_blockScale_splitIndex_le`: every prime below the split has `\log p ≤ 1/|t|`.

For `|t| > e^{-(θ+1)}` the split index is `0` and the product below it is empty
(`RMF.norm_randomEulerProductIco_self_eq_one`); Harper's (5.2) is vacuous there too.  This is why
`RMF.norm_randomEulerProductIco_le_of_mem_barrierEvent` may assume `1 ≤ j`. -/

/-- **The split index.**  `\min\{m, ⌊\log(1/|t|) - θ⌋\}`, where `m` is the top of the range the
barrier is available on (Harper's `n - d` with `d = ⌊\log V⌋+3`).

The second arm is the translation of Harper's `p ≤ e^{1/|t|}`: the primes below block `j` reach up
to `\log x_j = e^{j+θ}`, so the condition `\log p ≤ 1/|t|` reads `j ≤ \log(1/|t|) - θ`. -/
noncomputable def splitIndex (θ : ℝ) (m : ℕ) (t : ℝ) : ℕ :=
  min m ⌊Real.log (1 / |t|) - θ⌋₊

/-- The split stays inside the range the barrier is stated on. -/
lemma splitIndex_le (θ : ℝ) (m : ℕ) (t : ℝ) : splitIndex θ m t ≤ m := min_le_left _ _

/-- **Harper's `p ≤ e^{1/|t|}`, in block coordinates**: `\log x_{j₀} ≤ 1/|t|` for
`j₀ = RMF.splitIndex θ m t ≥ 1`, which bounds the primes of every block below `j₀`.  `0 ≤ θ` is
needed: at `t = 0` Lean reads `\log(1/|t|)` as `0`, so for `θ ≤ -1` the floor `⌊-θ⌋₊ ≥ 1` would
satisfy the hypothesis while `\exp(j₀+θ) ≤ 0` is false. -/
lemma log_blockScale_splitIndex_le {θ : ℝ} {m : ℕ} {t : ℝ} (hθ : 0 ≤ θ)
    (h1 : 1 ≤ splitIndex θ m t) :
    Real.log (blockScale θ (splitIndex θ m t)) ≤ 1 / |t| := by
  have hfl : 1 ≤ ⌊Real.log (1 / |t|) - θ⌋₊ := le_trans h1 (min_le_right _ _)
  have hnn : (0 : ℝ) ≤ Real.log (1 / |t|) - θ := by
    by_contra hc
    have hz : ⌊Real.log (1 / |t|) - θ⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith [not_le.1 hc])
    omega
  -- `t ≠ 0`: otherwise `\log(1/|t|) = 0` and the floor is `⌊-θ⌋₊ = 0`, contradicting `hfl`
  have ht : t ≠ 0 := by
    intro h0
    rw [h0] at hfl
    simp only [abs_zero, div_zero, Real.log_zero, zero_sub] at hfl
    have hz : ⌊(-θ : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
    omega
  have hle : ((splitIndex θ m t : ℕ) : ℝ) ≤ Real.log (1 / |t|) - θ :=
    le_trans (Nat.cast_le.2 (min_le_right _ _)) (Nat.floor_le hnn)
  rw [log_blockScale]
  calc Real.exp ((splitIndex θ m t : ℝ) + θ)
      ≤ Real.exp (Real.log (1 / |t|)) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / |t| := Real.exp_log (by positivity)

/-- The empty range of primes, `primesIco y y = ∅`, over which the Euler product is `1`
(`RMF.norm_randomEulerProductIco_self_eq_one`).  This is the degenerate case of the split,
and the reason (5.2) needs no separate statement at `j = 0`. -/
lemma primesIco_self (y : ℕ) : primesIco y y = ∅ := Finset.sdiff_self _

@[simp]
lemma norm_randomEulerProductIco_self_eq_one {Ω : Type*} {Y : ℕ → Ω → ℂ} {y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω} :
    ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω) y y s ω‖ = 1 := by
  have hω : ∀ p ∈ primesIco y y, ‖Y p ω‖ ≤ 1 := by simp [primesIco_self]
  rw [randomEulerProductIco_compMult_eq hs hω, primesIco_self, Finset.prod_empty, norm_one]

/-! ### The envelope at the split, and the choice of `hf`

The lower bound for the restricted mean constrains `hf` only by `|hf j| ≤ 10\log j`, which
allows `hf j = +10\log j`, `e^{hf j} = j^{10}`: the `1/\log²(2/|t|)` saving that makes the
`t`-integral of Key Proposition 5 converge would be reversed.  Harper's `h(n) = -2\log n` is
`RMF.harperHf`, admissible by `RMF.abs_harperHf_le`.  A more negative `hf` gives a smaller event,
which costs nothing in Proposition 5's lower bound, since that holds for every admissible `hf`.

With `hf = harperHf` the envelope at the split factors as `e^a·e^{j₀}/j₀²`, so only `e^{j₀}`
branches: `RMF.exp_envelope_splitIndex_le` is `e^a·\min\{e^m, e^{-θ}/|t|\}/j₀²`, Harper's
`\min\{\log x/(VΛ²), 1/(|t|\log²(2/|t|))\}` with the square factored out. -/

/-- **Harper's `h(n) = -2\log n`**, the upper envelope's correction in `L(t)`.  At `j = 0` it
is `0`, `Real.log 0` being `0`. -/
noncomputable def harperHf (j : ℕ) : ℝ := -2 * Real.log j

/-- `RMF.harperHf` is admissible for the lower bound on the restricted mean, whose hypothesis is
`|hf j| ≤ 10\log j`.  This holds for *every* `j`, including `0`. -/
lemma abs_harperHf_le (j : ℕ) : |harperHf j| ≤ 10 * Real.log j := by
  have h := Real.log_natCast_nonneg j
  rw [harperHf, abs_mul, abs_of_nonneg h]
  rw [show |(-2 : ℝ)| = 2 by norm_num]
  linarith

/-- `e^{h(j)} = 1/j²`: the saving, in the form the envelope uses. -/
lemma exp_harperHf {j : ℕ} (hj : 1 ≤ j) : Real.exp (harperHf j) = 1 / (j : ℝ) ^ 2 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have h : harperHf j = -Real.log j + -Real.log j := by rw [harperHf]; ring
  rw [h, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_log hj0]
  field_simp

/-- **The envelope at the split index, both branches at once**:
`e^{a + j₀ + h(j₀)} ≤ e^a·\min\{e^m, e^{-θ}/|t|\}/j₀²`, Harper's (5.2) right-hand side with the
square factored out.  The first arm is his `l₀ = ⌊\log V⌋+3` (`≪ \log x/(VΛ²)`), the second his
`l₀ = ⌊\log(|t|\log x)⌋` (`≪ 1/(|t|\log²(2/|t|))`). -/
lemma exp_envelope_splitIndex_le {θ : ℝ} {m : ℕ} {t : ℝ} (hθ : 0 ≤ θ)
    (h1 : 1 ≤ splitIndex θ m t) (a : ℝ) :
    Real.exp (a + (splitIndex θ m t : ℝ) + harperHf (splitIndex θ m t))
      ≤ Real.exp a * min (Real.exp m) (Real.exp (-θ) / |t|)
          / ((splitIndex θ m t : ℝ)) ^ 2 := by
  set j := splitIndex θ m t with hjdef
  have hj0 : (0 : ℝ) < j := by exact_mod_cast h1
  -- the second arm: `e^{j} ≤ e^{-θ}/|t|`, which is `log_blockScale_splitIndex_le` rearranged
  have harm2 : Real.exp (j : ℝ) ≤ Real.exp (-θ) / |t| := by
    have h := log_blockScale_splitIndex_le (m := m) (t := t) hθ h1
    rw [log_blockScale] at h
    calc Real.exp (j : ℝ) = Real.exp (-θ) * Real.exp ((j : ℝ) + θ) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-θ) * (1 / |t|) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = Real.exp (-θ) / |t| := by ring
  -- the first arm: `j ≤ m`
  have harm1 : Real.exp (j : ℝ) ≤ Real.exp m :=
    Real.exp_le_exp.2 (by exact_mod_cast splitIndex_le θ m t)
  have hmin : Real.exp (j : ℝ) ≤ min (Real.exp m) (Real.exp (-θ) / |t|) := le_min harm1 harm2
  calc Real.exp (a + (j : ℝ) + harperHf j)
      = Real.exp a * Real.exp (j : ℝ) * Real.exp (harperHf j) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ = Real.exp a * Real.exp (j : ℝ) / (j : ℝ) ^ 2 := by
        rw [exp_harperHf h1]; ring
    _ ≤ Real.exp a * min (Real.exp m) (Real.exp (-θ) / |t|) / (j : ℝ) ^ 2 := by
        gcongr

/-! ### Independence across the split

Harper's crude range discards both indicators from (5.3) and factors the remainder.
(5.3)'s denominator carries only the second point, so after cancelling the low primes survive at
height `0` alone, and the integrand is `‖I_low(s₁)‖²·‖I_high(s₁)‖²‖I_high(s₂)‖²`: a one-point
factor below the split, a two-point factor above it.  Each is a product of one function per
prime, so its expectation is a product over primes (`RMF.IsIIDPrimeValues.integral_prod`), with
no separate `IndepFun`. -/

omit [MeasurableSpace Ω] in
/-- **Consecutive ranges multiply.**  The random Euler product's block form, at a point. -/
lemma randomEulerProductIco_mul {Ω : Type*} (f : Ω → ArithmeticFunction ℂ) {y₀ y₁ y₂ : ℕ}
    (h₀ : y₀ ≤ y₁) (h₁ : y₁ ≤ y₂) (s : ℂ) (ω : Ω) :
    randomEulerProductIco f y₀ y₁ s ω * randomEulerProductIco f y₁ y₂ s ω
      = randomEulerProductIco f y₀ y₂ s ω :=
  eulerProductIco_mul _ h₀ h₁ s

/-- **The one-point second moment over a range**:
`E‖F_{[y₀,y₁)}(s)‖² = ∏_{p∈[y₀,y₁)} ∫ ‖(1 - z p^{-s})⁻¹‖² dν(z)`, the `Ico` sibling of
`RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq`; the two-point form is
`RMF.integral_norm_randomEulerProductIco_sq_mul_sq_compMult`. -/
theorem integral_norm_randomEulerProductIco_sq_compMult {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ)
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (y₀ y₁ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, ∫ z, ‖(1 - z * (p : ℂ) ^ (-s))⁻¹‖ ^ 2 ∂ν := by
  have hae : ∀ᵐ ω ∂μ,
      ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2
        = ∏ p ∈ primesIco y₀ y₁, ‖(1 - X p ω * (p : ℂ) ^ (-s))⁻¹‖ ^ 2 := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX hν y₀ y₁] with ω hω
    rw [randomEulerProductIco_compMult_eq hs hω, norm_prod, ← Finset.prod_pow]
  have hmeas : ∀ p ∈ primesIco y₀ y₁,
      AEStronglyMeasurable (fun z : ℂ => ‖(1 - z * (p : ℂ) ^ (-s))⁻¹‖ ^ 2) ν := by
    intro p _
    fun_prop
  rw [integral_congr_ae hae,
    hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp)
      (fun p z => ‖(1 - z * (p : ℂ) ^ (-s))⁻¹‖ ^ 2) hmeas]

/-! ### The low factor in closed form

The crude range reduces to two expectations.  The high one is Harper's (5.1),
`RMF.exists_abs_log_integral_two_point_le`; the low one is a one-point second moment over a range,
the `Ico` form of `RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq`.  Its primed form
`∏_{p∈[y₀,y₁)}(1 - p^{-2σ})⁻¹`, `σ = Re s`, is the one estimated: its logarithm is
`∑ p^{-2σ} + O(1)`, as in Harper's (3.1). -/

/-- **The second moment of the Steinhaus Euler product over a range.**  Each prime of the range
contributes `(1 - ‖p^{-s}‖²)⁻¹`. -/
theorem IsSteinhausRMF.integral_norm_randomEulerProductIco_sq {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, (1 - ‖(p : ℂ) ^ (-s)‖ ^ 2)⁻¹ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  rw [integral_norm_randomEulerProductIco_sq_compMult hX norm_le_one_steinhausLaw y₀ y₁ hs]
  exact Finset.prod_congr rfl fun p hp =>
    integral_norm_inv_one_sub_mul_sq_steinhausLaw
      (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs)

/-- The same as a product of powers: `∏_{p ∈ [y₀,y₁)} (1 - p^{-2σ})⁻¹`, `σ = Re s`, the form of
Harper's (3.1) and the one the crude range's low factor is estimated from. -/
theorem IsSteinhausRMF.integral_norm_randomEulerProductIco_sq' {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-2 * s.re))⁻¹ := by
  rw [hf.integral_norm_randomEulerProductIco_sq y₀ y₁ hs]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (prime_of_mem_primesIco hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity)]
  ring_nf

/-! ### The low factor, bounded

Harper's low-prime expectation is `≪ \min\{\log x/V, 1/|t|\}`.  No tilt-weighted Mertens
estimate is needed: the low range stops at the split, whose first arm is the top of the block
range left by the drop, `\log x_{n-d} = e^{n-d+θ} ≈ \log x/(Ve³)` with `d = ⌊\log V⌋+3`.  The drop
is the `\log x/V` cap, so Mertens' third theorem with `σ ≥ 0`
(`RMF.exists_abs_log_prod_primesBelow_sub_log_log_le`) gives the whole factor, and the two arms
of the `\min` are those of the split index. -/

/-- Each tilted local factor is dominated by the untilted one, for `σ ≥ 0`. -/
lemma one_sub_rpow_inv_le_one_sub_inv_inv {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    (1 - (p : ℝ) ^ (-1 - 2 * σ))⁻¹ ≤ (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hrpow : (p : ℝ) ^ (-1 - 2 * σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hinv : (p : ℝ) ^ (-1 : ℝ) = ((p : ℝ))⁻¹ := by
    rw [Real.rpow_neg_one]
  have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hpos : (0 : ℝ) < 1 - ((p : ℝ))⁻¹ := by linarith
  rw [hinv] at hrpow
  exact inv_anti₀ (by linarith) (by linarith)

/-- Every Mertens factor is at least `1`. -/
lemma one_le_one_sub_inv_inv {p : ℕ} (hp : p.Prime) : (1 : ℝ) ≤ (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hinv0 : (0 : ℝ) < ((p : ℝ))⁻¹ := by positivity
  have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  rw [inv_eq_one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ((p : ℝ))⁻¹)]
  linarith

/-- **The low factor, dominated by Mertens' product**:
`∏_{p∈[y₀,c)}(1 - p^{-1-2σ})⁻¹ ≤ ∏_{p<c}(1 - p^{-1})⁻¹` for `σ ≥ 0`.  Each tilted factor is at
most its untilted one, and the extra factors are `≥ 1`. -/
lemma prod_one_sub_rpow_inv_le {y₀ c : ℕ} (hy : y₀ ≤ c) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∏ p ∈ primesIco y₀ c, (1 - (p : ℝ) ^ (-1 - 2 * σ))⁻¹)
      ≤ ∏ p ∈ Nat.primesBelow c, (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have h0 : ∀ p ∈ primesIco y₀ c, (0 : ℝ) ≤ (1 - (p : ℝ) ^ (-1 - 2 * σ))⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    have hle : (p : ℝ) ^ (-1 - 2 * σ) ≤ ((p : ℝ))⁻¹ := by
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
      have h := Real.rpow_le_rpow_of_exponent_le h1 (by linarith : (-1 - 2 * σ) ≤ (-1 : ℝ))
      rwa [Real.rpow_neg_one] at h
    have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact (inv_pos.2 (by linarith : (0 : ℝ) < 1 - (p : ℝ) ^ (-1 - 2 * σ))).le
  have hstep : (∏ p ∈ primesIco y₀ c, (1 - (p : ℝ) ^ (-1 - 2 * σ))⁻¹)
      ≤ ∏ p ∈ primesIco y₀ c, (1 - ((p : ℝ))⁻¹)⁻¹ :=
    Finset.prod_le_prod h0
      fun p hp => one_sub_rpow_inv_le_one_sub_inv_inv (prime_of_mem_primesIco hp) hσ
  -- extend the range to `[0, c)` by splitting it, the head contributing a factor `≥ 1`
  have hhead : (1 : ℝ) ≤ ∏ p ∈ primesIco 0 y₀, (1 - ((p : ℝ))⁻¹)⁻¹ := by
    calc (1 : ℝ) = ∏ _p ∈ primesIco 0 y₀, (1 : ℝ) := by rw [Finset.prod_const_one]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          fun p hp => one_le_one_sub_inv_inv (prime_of_mem_primesIco hp)
  have htail : (0 : ℝ) ≤ ∏ p ∈ primesIco y₀ c, (1 - ((p : ℝ))⁻¹)⁻¹ :=
    Finset.prod_nonneg fun p hp =>
      le_trans zero_le_one (one_le_one_sub_inv_inv (prime_of_mem_primesIco hp))
  refine le_trans hstep ?_
  rw [← primesIco_zero c, ← primesIco_union (Nat.zero_le y₀) hy,
    Finset.prod_union (disjoint_primesIco 0 y₀ c)]
  exact le_mul_of_one_le_left htail hhead

/-- **The crude range's low factor**: `E‖I_{[y₀,z)}(1/2+σ)‖² ≤ C\log z` for `σ ≥ 0`, with `C`
independent of `f`, `μ`, `y₀`, `z` and `σ`.  At `z = blockScale θ j₀` this is Harper's
`≪ \min\{\log x/V, 1/|t|\}`.  Each tilted factor is at most its untilted one, and Mertens' third
theorem does the rest. -/
theorem exists_integral_norm_randomEulerProductIco_sq_le :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (y₀ : ℕ) (z : ℝ) (s : ℂ) (σ : ℝ), 2 ≤ z → y₀ ≤ ⌊z⌋₊ + 1 → 0 ≤ σ → s.re = 1 / 2 + σ →
        (∫ ω, ‖randomEulerProductIco f y₀ (⌊z⌋₊ + 1) s ω‖ ^ 2 ∂μ) ≤ C * Real.log z := by
  obtain ⟨C₀, hC₀, hmert⟩ := exists_abs_log_prod_primesBelow_sub_log_log_le
  refine ⟨Real.exp C₀, Real.exp_pos _, fun f μ hf y₀ z s σ hz hy hσ hre => ?_⟩
  have hz0 : (0 : ℝ) < z := by linarith
  have hN2 : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hNz : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le hz0.le
  have hN2R : (2 : ℝ) ≤ ((⌊z⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN2
  have hs : 0 < s.re := by rw [hre]; linarith
  rw [hf.integral_norm_randomEulerProductIco_sq' y₀ (⌊z⌋₊ + 1) hs]
  have hexp : (-2 : ℝ) * s.re = -1 - 2 * σ := by rw [hre]; ring
  simp only [hexp]
  refine le_trans (prod_one_sub_rpow_inv_le hy hσ) ?_
  have hpos : (0 : ℝ) < ∏ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹ :=
    Finset.prod_pos fun p hp => lt_of_lt_of_le zero_lt_one
      (one_le_one_sub_inv_inv (Nat.prime_of_mem_primesBelow hp))
  have hlog := (abs_le.1 (hmert ⌊z⌋₊ hN2)).2
  have hlogN : (0 : ℝ) < Real.log ((⌊z⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  calc ∏ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹
      = Real.exp (Real.log (∏ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹)) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log (Real.log ((⌊z⌋₊ : ℕ) : ℝ)) + C₀) := Real.exp_le_exp.2 (by linarith)
    _ = Real.log ((⌊z⌋₊ : ℕ) : ℝ) * Real.exp C₀ := by
        rw [Real.exp_add, Real.exp_log hlogN]
    _ ≤ Real.exp C₀ * Real.log z := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hNz) (Real.exp_pos _).le

/-! ### The high factor: the two prime sums

Harper's (5.1) evaluates the high-prime expectation as
`\exp\{∑_{p\ \text{high}}(2 + 2\cos(t\log p))p^{-1-2σ} + O(1)\}`; the sum splits into a Mertens
part and a cosine part, both over a range (by differencing the `Nat.primesBelow` forms).

The cosine part is `O(1)` because both endpoints lie past `e^{1/τ}`:
`RMF.exists_abs_cos_primesBelow_sub_log_min_le` gives
`∑_{p<N}\cos(τ\log p)/p = \log(\min\{\log N, 1/τ\}/\log 2) + O(1)`, and past `e^{1/τ}` both
minima equal `1/τ`, so the main terms cancel.  The Mertens part keeps its main term
`\log\log N₂ - \log\log N₁`, which exponentiates to `(\max\{1, |t|\log x/V\})²`. -/

/-- **The cosine prime sum over a range above `e^{1/τ}` is `O(1)`.**  Both endpoints past
`e^{1/τ}` make the two main terms equal, so they cancel. -/
theorem exists_abs_cos_primesIco_le :
    ∃ B > 0, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      1 / τ ≤ Real.log N₁ →
      |∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), Real.cos (τ * Real.log p) / p| ≤ B := by
  obtain ⟨B, hB, h⟩ := exists_abs_cos_primesBelow_sub_log_min_le
  refine ⟨2 * B, by positivity, fun τ hτ hτ1 N₁ N₂ hN₁ hN12 hlog => ?_⟩
  have hN₂ : 2 ≤ N₂ := le_trans hN₁ hN12
  have hN₁R : (2 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN₁
  have hN₂R : (2 : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast hN₂
  have hsub : Nat.primesBelow (N₁ + 1) ⊆ Nat.primesBelow (N₂ + 1) := primesBelow_mono (by omega)
  have hsum : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), Real.cos (τ * Real.log p) / p)
      = (∑ p ∈ Nat.primesBelow (N₂ + 1), Real.cos (τ * Real.log p) / p)
        - ∑ p ∈ Nat.primesBelow (N₁ + 1), Real.cos (τ * Real.log p) / p :=
    eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  have hmono : Real.log (N₁ : ℝ) ≤ Real.log (N₂ : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hN12)
  have hmin₁ : min (Real.log (N₁ : ℝ)) (1 / τ) = 1 / τ := min_eq_right hlog
  have hmin₂ : min (Real.log (N₂ : ℝ)) (1 / τ) = 1 / τ := min_eq_right (le_trans hlog hmono)
  have h₁ := h τ hτ hτ1 N₁ hN₁
  have h₂ := h τ hτ hτ1 N₂ hN₂
  rw [hmin₁] at h₁
  rw [hmin₂] at h₂
  rw [hsum, abs_le]
  rw [abs_le] at h₁ h₂
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **Mertens' second theorem over a range.**  The main term is the difference of the two
`\log\log`s, which is what exponentiates to `(\max\{1, |t|\log x/V\})²`. -/
theorem exists_abs_sum_primesIco_inv_sub_le :
    ∃ C > 0, ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      |∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), ((p : ℝ))⁻¹
        - (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ)))| ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  refine ⟨2 * C, by positivity, fun N₁ N₂ hN₁ hN12 => ?_⟩
  have hN₂ : 2 ≤ N₂ := le_trans hN₁ hN12
  have hsub : Nat.primesBelow (N₁ + 1) ⊆ Nat.primesBelow (N₂ + 1) := primesBelow_mono (by omega)
  have hsum : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), ((p : ℝ))⁻¹)
      = (∑ p ∈ Nat.primesBelow (N₂ + 1), ((p : ℝ))⁻¹)
        - ∑ p ∈ Nat.primesBelow (N₁ + 1), ((p : ℝ))⁻¹ :=
    eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  have h₁ := h N₁ hN₁
  have h₂ := h N₂ hN₂
  rw [hsum, abs_le]
  rw [abs_le] at h₁ h₂
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **The (5.1) exponent over the high range, with the tilt discarded**:
`∑_{N₁<p≤N₂}(2 + 2\cos(t\log p))p^{-1-2σ} ≤ 2(\log\log N₂ - \log\log N₁) + D` for `σ ≥ 0` and
`1/|t| ≤ \log N₁`.  `p^{-1-2σ} ≤ p^{-1}` runs the main term to `N₂`, a factor `V²` above Harper's
bound at his data; `RMF.exists_sum_two_add_two_cos_rpow_split_le` keeps the tilt, is sharp, and
uses this lemma below the truncation. -/
theorem exists_sum_two_add_two_cos_rpow_le :
    ∃ D > 0, ∀ (t σ : ℝ), 0 < |t| → |t| ≤ 1 → 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      1 / |t| ≤ Real.log N₁ →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 2 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨B, hB, hcos⟩ := exists_abs_cos_primesIco_le
  obtain ⟨C, hC, hmert⟩ := exists_abs_sum_primesIco_inv_sub_le
  refine ⟨2 * B + 2 * C, by positivity, fun t σ ht ht1 hσ N₁ N₂ hN₁ hN12 hlog => ?_⟩
  -- `cos` is even, so the signed height may be replaced by its modulus
  have habs : ∀ p : ℕ, Real.cos (t * Real.log p) = Real.cos (|t| * Real.log p) := by
    intro p
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  -- discard the tilt: `p^{-1-2σ} ≤ p⁻¹`
  have hterm : ∀ p ∈ primesIco (N₁ + 1) (N₂ + 1),
      (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)
        ≤ 2 * ((p : ℝ))⁻¹ + 2 * (Real.cos (|t| * Real.log p) / p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).two_le
    have hle : (p : ℝ) ^ (-1 - 2 * σ) ≤ ((p : ℝ))⁻¹ := by
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
      have h := Real.rpow_le_rpow_of_exponent_le h1 (by linarith : (-1 - 2 * σ) ≤ (-1 : ℝ))
      rwa [Real.rpow_neg_one] at h
    have hnn : (0 : ℝ) ≤ 2 + 2 * Real.cos (t * Real.log p) := by
      have := Real.neg_one_le_cos (t * Real.log p)
      linarith
    calc (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)
        ≤ (2 + 2 * Real.cos (t * Real.log p)) * ((p : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hle hnn
      _ = 2 * ((p : ℝ))⁻¹ + 2 * (Real.cos (|t| * Real.log p) / p) := by
          rw [habs p, div_eq_mul_inv]
          ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hτ0 : 0 < |t| := ht
  have hc := hcos |t| hτ0 ht1 N₁ N₂ hN₁ hN12 hlog
  have hm := hmert N₁ N₂ hN₁ hN12
  rw [abs_le] at hc hm
  linarith [hc.1, hc.2, hm.1, hm.2]

/-- **Harper's (5.1) exponent, with the tilt kept**:
`∑_{N₁<p≤N₂}(2 + 2\cos(t\log p))p^{-1-2σ} ≤ 2(\log\log M - \log\log N₁) + D` when
`1 ≤ 2σ\log M`: the main term stops at the truncation scale `M`, not at `N₂`.  At Harper's data
(`M = x^{1/V}`, `2σ = 8V/\log x`) exponentiating gives `(\max\{1, |t|\log x/V\})²`, with no `V²`
loss.  The proof splits at `M`: `RMF.exists_sum_two_add_two_cos_rpow_le` below, and the
tilt-thinning tail `RMF.exists_sum_prime_Ioc_rpow_tail_le` above. -/
theorem exists_sum_two_add_two_cos_rpow_split_le :
    ∃ D > 0, ∀ (t σ : ℝ), 0 < |t| → |t| ≤ 1 → 0 ≤ σ → ∀ N₁ M N₂ : ℕ,
      2 ≤ N₁ → N₁ ≤ M → M ≤ N₂ → 1 / |t| ≤ Real.log N₁ → 1 ≤ 2 * σ * Real.log M →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨D₀, hD₀, hlow⟩ := exists_sum_two_add_two_cos_rpow_le
  obtain ⟨C, hC, htail⟩ := exists_sum_prime_Ioc_rpow_tail_le
  refine ⟨D₀ + 4 * C, by positivity, fun t σ ht ht1 hσ N₁ M N₂ hN₁ hNM hMN₂ hlog hM => ?_⟩
  -- split the range at the truncation scale
  have hsplit : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primesIco (N₁ + 1) (M + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        + ∑ p ∈ primesIco (M + 1) (N₂ + 1),
            (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [← primesIco_union (by omega : N₁ + 1 ≤ M + 1) (by omega : M + 1 ≤ N₂ + 1),
      Finset.sum_union (disjoint_primesIco _ _ _)]
  rw [hsplit]
  -- below the truncation the untilted bound applies, with `M` as the right endpoint
  have hbelow := hlow t σ ht ht1 hσ N₁ M hN₁ hNM hlog
  -- above it the tilt makes the entire tail an absolute constant
  have habove : (∑ p ∈ primesIco (M + 1) (N₂ + 1),
      (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)) ≤ 4 * C := by
    have hterm : ∀ p ∈ primesIco (M + 1) (N₂ + 1),
        (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)
          ≤ 4 * (p : ℝ) ^ (-1 - 2 * σ) := by
      intro p _
      have hc := Real.cos_le_one (t * Real.log p)
      have hnn : (0 : ℝ) ≤ (p : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (by positivity) _
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hconv : (∑ p ∈ primesIco (M + 1) (N₂ + 1), (p : ℝ) ^ (-1 - 2 * σ))
        = ∑ p ∈ Finset.Ioc ⌊(M : ℝ)⌋₊ ⌊(N₂ : ℝ)⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ) := by
      rw [Nat.floor_natCast, Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
    have hMR : (2 : ℝ) ≤ (M : ℝ) := by
      have : (2 : ℕ) ≤ M := le_trans hN₁ hNM
      exact_mod_cast this
    have hMN₂R : ((M : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hMN₂
    have hbound := htail (2 * σ) (M : ℝ) (N₂ : ℝ) (by linarith) hMR hMN₂R hM
    rw [hconv] at hsum
    linarith
  linarith

/-- The two-point moment over a range is positive — needed to turn (5.1)'s bound on its
*logarithm* back into a bound on the moment.  Each local factor is positive by
`RMF.integral_local_two_point_pos`, and the moment is their product. -/
lemma IsSteinhausRMF.integral_normSq_mul_normSq_Ico_pos {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y₁ : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    0 < ∫ ω, ‖randomEulerProductIco f y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f y₀ y₁ s₂ ω‖ ^ 2 ∂μ := by
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ y₁ hs₁ hs₂]
  exact Finset.prod_pos fun p hp => integral_local_two_point_pos
    (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₁)
    (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₂)

/-- **The crude range's high factor, over a general law**:
`E‖I_{(N₁,N₂]}(1/2+σ)‖²‖I_{(N₁,N₂]}(1/2+σ+it)‖² ≤ K(\log M/\log N₁)²` when `1/|t| ≤ \log N₁`,
`1 ≤ 2σ\log M` and `400 ≤ N₁`: Harper's `≪ (\max\{1, |t|\log x/V\})²`.  The law enters
only through (5.1) (`H51`), the tilt-kept prime sum (`Hsum`), positivity (`Hpos`) and the cosine
coefficient `cc`: `2` for Steinhaus, `4` for Rademacher. -/
theorem exists_integral_normSq_high_le_of_suppliers
    {P : (Ω → ArithmeticFunction ℂ) → Measure Ω → Prop} {cc : ℝ}
    (H51 : ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ σ t x y : ℝ, 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      |Real.log (∫ ω,
            ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
              * ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1)
                  (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + cc * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ C / (Real.sqrt x * Real.log x))
    (Hsum : ∃ D > 0, ∀ (t σ : ℝ), 0 < |t| → |t| ≤ 1 → 0 ≤ σ → ∀ N₁ M N₂ : ℕ,
      2 ≤ N₁ → N₁ ≤ M → M ≤ N₂ → 1 / |t| ≤ Real.log (N₁ : ℝ) →
      1 ≤ 2 * σ * Real.log (M : ℝ) →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + cc * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D)
    (Hpos : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ (y₀ y₁ : ℕ) {s₁ s₂ : ℂ}, 0 < s₁.re → 0 < s₂.re →
        0 < ∫ ω, ‖randomEulerProductIco f y₀ y₁ s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f y₀ y₁ s₂ ω‖ ^ 2 ∂μ) :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), P f μ →
      ∀ (σ t : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t| → |t| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨C, hC, h51⟩ := H51
  obtain ⟨D, hD, hsum⟩ := Hsum
  refine ⟨Real.exp (D + C), Real.exp_pos _,
    fun f μ hf σ t N₁ M N₂ hσ ht ht1 hN₁ hNM hMN₂ hlog hM => ?_⟩
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hMR : ((N₁ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hNM
  have hN₂R : ((M : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hMN₂
  have hlogM : (1 : ℝ) ≤ Real.log (M : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hMR)
  -- (5.1) at the endpoints of the range
  have hre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hs₁ : (0 : ℝ) < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hs₂ : (0 : ℝ) < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by
        have h1 : (1 : ℝ) ≤ Real.log ((N₂ : ℕ) : ℝ) :=
          le_trans hlogM (Real.log_le_log (by linarith) hN₂R)
        linarith
      positivity
    linarith
  have h := h51 f μ hf σ t ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) (by exact_mod_cast hN₁)
    (le_trans hMR hN₂R) hσ'
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  -- the error term is at most `C`
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ) := by nlinarith
    calc C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C / 1 :=
          div_le_div_of_nonneg_left hC.le (by norm_num) hden
      _ = C := by ring
  -- the prime sum, with the tilt kept
  have hps := hsum t σ ht ht1 hσ N₁ M N₂ (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ)))
    hNM hMN₂ hlog hM
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  -- assemble: `log E ≤ 2(loglog M - loglog N₁) + D + C`
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
        ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ 2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C) := by
    linarith [h.2, hps, herr]
  have hEpos := Hpos f μ hf (N₁ + 1) (N₂ + 1) hs₁ hs₂
  have hconv : Real.exp (2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ)))
      + (D + C)) = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
    have hratio : (0 : ℝ) < Real.log (M : ℝ) / Real.log (N₁ : ℝ) := by
      apply div_pos <;> linarith
    rw [← Real.log_div (by linarith) (by linarith)]
    rw [show (2 : ℝ) * Real.log (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) + (D + C)
        = (Real.log (Real.log (M : ℝ) / Real.log (N₁ : ℝ))
          + Real.log (Real.log (M : ℝ) / Real.log (N₁ : ℝ))) + (D + C) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log hratio]
    ring
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := hconv

/-- **The high factor's two-point bound, for the Steinhaus RMF.**  The
`RMF.exists_integral_normSq_high_le_of_suppliers` instance at `cc = 2`. -/
theorem exists_integral_normSq_high_le :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ t : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t| → |t| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 :=
  exists_integral_normSq_high_le_of_suppliers
    (exists_abs_log_integral_two_point_le (Ω := Ω))
    exists_sum_two_add_two_cos_rpow_split_le
    (fun _ _ hf y₀ y₁ => hf.integral_normSq_mul_normSq_Ico_pos y₀ y₁)

/-! ### Harper's `R(t)`

For `(\log x)^{-1/3} < |t| ≤ 1` the indicators stay, and Harper replaces `L(0)` by a larger event
`R(t)`: with `D(t) = ⌈2\log(1/|t|)⌉ + (B+1)`, comparing `L(0)`'s constraint at
`j = ⌊Λ⌋ - D` with that at general `j` pins the partial products over the remaining blocks from
both sides.  Here that is differencing the barrier at two indices: `RMF.subset_barrierEvent_shift`.

With `u j = -a - Bj`, `v j = a + j + hf j` and shift `r` the shifted tube is
`[-(2a + Br + r + hf r) - Bm, (2a + r + Br) + m + hf(m+r)]`.  At `r ≈ 2\log(1/|t|)` the upper end
carries `|t|^{-2B}` and the lower end `|t|²\log²(2/|t|)`, Harper's two factors, and the level
`a' = 2a + r + Br + |hf r| = 2a + O(\log(2/|t|))` is the `a` he feeds to Proposition 7. -/

omit [MeasurableSpace Ω] in
/-- **The barrier event, shifted.**  `RMF.subset_barrierEvent_shift` with no offset: a walk in the
tube on `[1,n]` has its suffix from `r` in the differenced tube on `[1, n-r]`. -/
theorem barrierEvent_subset_shift {X : ℕ → Ω → ℝ} {n r : ℕ} {u v : ℕ → ℝ}
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    barrierEvent X n u v ⊆ barrierEvent (fun m => X (m + r)) (n - r)
        (fun m => u (m + r) - v r) (fun m => v (m + r) - u r) := by
  refine subset_trans ?_ (subset_barrierEvent_shift (X := X) (Z := fun _ => 0) hrn)
  intro ω hω j hj1 hjn
  simpa using hω j (le_trans hr hj1) hjn

omit [MeasurableSpace Ω] in
/-- **Harper's `R(t)`**: the shifted tube, widened back into the barrier's own shape at level
`a' = 2a + r + Br + |hf r|`, which is `2a + O(\log(2/|t|))` at `r ≈ 2\log(1/|t|)`.
Widening is harmless: `R(t)` is used only for an upper bound on a probability.  No sign condition
on `B` is needed: the slope terms cancel, and the inclusion turns on `hf r ≤ |hf r|`. -/
theorem barrierEvent_subset_harper_shift {X : ℕ → Ω → ℝ} {n r : ℕ} {a B : ℝ} {hf : ℕ → ℝ}
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    barrierEvent X n (fun j => -a - B * j) (fun j => a + j + hf j)
      ⊆ barrierEvent (fun m => X (m + r)) (n - r)
          (fun m => -(2 * a + r + B * r + |hf r|) - B * m)
          (fun m => (2 * a + r + B * r + |hf r|) + m + hf (m + r)) := by
  refine subset_trans (barrierEvent_subset_shift hr hrn) ?_
  intro ω hω m hm1 hmn
  have h := hω m hm1 hmn
  simp only [Set.mem_Icc] at h ⊢
  push_cast at h ⊢
  have hhf : hf r ≤ |hf r| := le_abs_self _
  have habs : (0 : ℝ) ≤ |hf r| := abs_nonneg _
  -- make the only nonlinear term explicit, so `linarith` suffices
  have hexp : B * ((m : ℝ) + (r : ℝ)) = B * (m : ℝ) + B * (r : ℝ) := by ring
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### The cosine drift above the shift

Proposition 7 wants `|∑_{m<j}θ₁ m - j| ≤ C`, a drift of about `1` per block in each
coordinate.  Under the two-fold tilt coordinate one drifts by
`θ₁(m) = ∑_{p∈B_m}p^{-1-2σ} + ∑_{p∈B_m}\cos(t\log p)p^{-1-2σ} = 1 + c_m`, and `c_m ≈ 1` while
block `m` cannot resolve the two heights (`RMF.abs_blockMean₂_le`).  So the drift hypothesis fails
on the full block range and holds only above a shift.

The lemmas below sum `c_m` above a shift `r`.  The block cosine-sum bound
`RMF.exists_abs_cos_prime_sum_block_weight_le` gives `|c_m| ≪ 1/(τe^{m+θ})`, a geometric series,
so `∑_{m≥r}|c_m| ≪ 1/(τe^{r+θ})`: `≪ τe^{-θ}` at `r = ⌈2\log(1/τ)⌉`, and `O(1)` at
`r = ⌈\log(1/τ)⌉`. -/

/-- **`RMF.exists_abs_sum_cos_primeBlockSub_le` with the PNT constant left free.**  The constant
`C` is the `K₁` of `RMF.prop7Window`. -/
theorem le_abs_sum_cos_primeBlockSub_of_weight {C : ℝ} (hC : 0 ≤ C)
    (h28 :
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ σ y₁ y₂ : ℝ, 2 ≤ y₁ → y₁ ≤ y₂ →
        |σ| * Real.log y₂ ≤ 1 →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
        ≤ blockCosineWeightConst C * (1 + 2 * |σ| * Real.log (y₂ / y₁)) / (τ * Real.log y₁)) :
    ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → τ ≤ 1 → 0 ≤ θ →
    |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
      ≤ blockCosineSubConst C / (τ * Real.exp ((m : ℝ) + θ)) := by
  set K₀ : ℝ := blockCosineWeightConst C with hK₀def
  have hK₀ : (0 : ℝ) < K₀ := blockCosineWeightConst_pos hC
  rw [blockCosineSubConst, ← hK₀def]
  intro τ σ θ m hτ hτ1 hθ hσ
  have hXpos : (0 : ℝ) < blockScale θ (m + 1) := blockScale_pos θ (m + 1)
  set y₁ : ℝ := blockScale θ (m + 1) ^ (Real.exp 1)⁻¹ with hy₁def
  have hlogX : Real.log (blockScale θ (m + 1)) = Real.exp (((m : ℝ) + 1) + θ) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hlogy₁ : Real.log y₁ = Real.exp ((m : ℝ) + θ) := by
    rw [hy₁def, Real.log_rpow hXpos, hlogX,
      show ((m : ℝ) + 1) + θ = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    field_simp
  have hy₁pos : (0 : ℝ) < y₁ := Real.rpow_pos_of_pos hXpos _
  have hexp1 : (1 : ℝ) ≤ Real.exp ((m : ℝ) + θ) := by
    rw [Real.one_le_exp_iff]
    positivity
  have hy₁two : (2 : ℝ) ≤ y₁ := by
    have h : Real.exp 1 ≤ y₁ := by
      rw [← Real.exp_log hy₁pos, hlogy₁]
      exact Real.exp_le_exp.2 hexp1
    linarith [Real.exp_one_gt_d9]
  have hy₁y₂ : y₁ ≤ blockScale θ (m + 1) := by
    rw [← Real.exp_log hy₁pos, ← Real.exp_log hXpos, hlogy₁, hlogX]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
  -- rewrite the block sum in the `Ioc`-with-filter form of the block cosine-sum bound
  have hrw : (∑ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [primeBlockSub, harperBlock,
      sum_primesIcoSub _ _ fun q => Real.cos (τ * Real.log (q : ℝ)) / ((q : ℝ)) ^ (1 + 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  refine le_trans (h28 τ hτ hτ1 σ y₁ (blockScale θ (m + 1)) hy₁two hy₁y₂ hσ) ?_
  -- `2|σ|log(y₂/y₁) ≤ 2|σ|log y₂ ≤ 2`, so the numerator is at most `3`
  have hquot : Real.log (blockScale θ (m + 1) / y₁)
      ≤ Real.log (blockScale θ (m + 1)) := by
    rw [Real.log_div hXpos.ne' hy₁pos.ne']
    have : (0 : ℝ) ≤ Real.log y₁ := by rw [hlogy₁]; positivity
    linarith
  have habs : (0 : ℝ) ≤ |σ| := abs_nonneg _
  have hnum : 1 + 2 * |σ| * Real.log (blockScale θ (m + 1) / y₁) ≤ 3 := by
    nlinarith [hσ, hquot, habs]
  have hden : (0 : ℝ) < τ * Real.log y₁ := by
    rw [hlogy₁]
    positivity
  rw [hlogy₁] at hden ⊢
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  linarith [mul_le_mul_of_nonneg_left hnum hK₀.le]

/-- **The block cosine-sum bound over one block, in block coordinates.**  The cosine sum over
`B_m` is `≪ 1/(τ\log x_m)` (`RMF.exists_abs_cos_prime_sum_block_weight_le`), and
`\log x_m = e^{m+θ}`. -/
theorem exists_abs_sum_cos_primeBlockSub_le :
    ∃ K > 0, ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → τ ≤ 1 → 0 ≤ θ →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ K / (τ * Real.exp ((m : ℝ) + θ)) := by
  obtain ⟨C, hC, hpnt⟩ := RS_prime.pnt
  exact ⟨blockCosineSubConst C, blockCosineSubConst_pos hC,
    le_abs_sum_cos_primeBlockSub_of_weight hC
      (le_abs_cos_prime_sum_block_weight_of_block hC
        (le_abs_cos_prime_sum_block_of_pnt hC hpnt))⟩

/-- **The cosine drift above a shift.**  Summing the block bound over `m ≥ r` gives a geometric
series with ratio `1/e`, so the whole excess is `≪ 1/(τ e^{r+θ})`.

This is the lemma Proposition 7's drift hypothesis needs.  At `r = ⌈2\log(1/τ)⌉` the bound is
`≪ τ e^{-θ}`, since `e^{r+θ} ≥ e^θ/τ²` — so the drift constant `C` is not merely absolute but
negligible, and Proposition 7's `(1+2C)` is `≈1`. -/
theorem exists_abs_sum_cos_primeBlockSub_shift_le :
    ∃ K > 0, ∀ (τ σ θ : ℝ) (r j : ℕ), 0 < τ → τ ≤ 1 → 0 ≤ θ →
      (∀ m, m < j → |σ| * Real.log (blockScale θ (m + r + 1)) ≤ 1) →
      |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ K / (τ * Real.exp ((r : ℝ) + θ)) := by
  obtain ⟨K₁, hK₁, hblock⟩ := exists_abs_sum_cos_primeBlockSub_le
  have he0 : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
  have he1 : Real.exp (-1 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  refine ⟨K₁ * (1 - Real.exp (-1 : ℝ))⁻¹, by positivity,
    fun τ σ θ r j hτ hτ1 hθ hσ => ?_⟩
  have hpow : ∀ m : ℕ, Real.exp (-1 : ℝ) ^ m = Real.exp (-(m : ℝ)) := by
    intro m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hstep : ∀ m ∈ Finset.range j,
      |∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ K₁ / (τ * Real.exp ((r : ℝ) + θ)) * Real.exp (-1 : ℝ) ^ m := by
    intro m hm
    have hm' : m < j := Finset.mem_range.1 hm
    refine le_trans (hblock τ σ θ (m + r) hτ hτ1 hθ (hσ m hm')) (le_of_eq ?_)
    have hcast : ((m + r : ℕ) : ℝ) = (m : ℝ) + (r : ℝ) := by push_cast; ring
    rw [hcast, show (m : ℝ) + (r : ℝ) + θ = (m : ℝ) + ((r : ℝ) + θ) by ring, Real.exp_add,
      hpow m]
    have h1 : Real.exp ((m : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
    have h2 : Real.exp ((r : ℝ) + θ) ≠ 0 := (Real.exp_pos _).ne'
    have h3 : Real.exp (-(m : ℝ)) = (Real.exp ((m : ℝ)))⁻¹ := by
      rw [Real.exp_neg]
    rw [h3]
    field_simp
  have hgeo : (∑ m ∈ Finset.range j, Real.exp (-1 : ℝ) ^ m) ≤ (1 - Real.exp (-1 : ℝ))⁻¹ := by
    have hsummable : Summable (fun m : ℕ => Real.exp (-1 : ℝ) ^ m) :=
      summable_geometric_of_lt_one he0.le he1
    calc (∑ m ∈ Finset.range j, Real.exp (-1 : ℝ) ^ m)
        ≤ ∑' m : ℕ, Real.exp (-1 : ℝ) ^ m :=
          hsummable.sum_le_tsum _ (fun m _ => by positivity)
      _ = (1 - Real.exp (-1 : ℝ))⁻¹ := tsum_geometric_of_lt_one he0.le he1
  calc |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
      ≤ ∑ m ∈ Finset.range j, |∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range j,
          K₁ / (τ * Real.exp ((r : ℝ) + θ)) * Real.exp (-1 : ℝ) ^ m := Finset.sum_le_sum hstep
    _ = K₁ / (τ * Real.exp ((r : ℝ) + θ))
          * ∑ m ∈ Finset.range j, Real.exp (-1 : ℝ) ^ m := by rw [← Finset.mul_sum]
    _ ≤ K₁ / (τ * Real.exp ((r : ℝ) + θ)) * (1 - Real.exp (-1 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = K₁ * (1 - Real.exp (-1 : ℝ))⁻¹ / (τ * Real.exp ((r : ℝ) + θ)) := by ring

/-- **The one-fold drift above a shift**: the drift over the blocks `[r, r+j)` is `j + O(1)`, by
differencing `RMF.abs_sum_blockMean_sub_le` at twice its constant.  This is the Mertens half of
Proposition 7's drift hypothesis; Mertens' theorem over the shifted range directly gives only
`[e^{-2}j, e²j]`. -/
theorem abs_sum_blockMean_shift_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {s : ℂ} {θ σ : ℝ} {n r j : ℕ}
    (hθ3 : (5 : ℝ) ≤ θ) (hj : r + j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1) :
    |(∑ m ∈ Finset.range j, blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ (m + r))) - (j : ℝ)|
      ≤ 2 * (4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ))
          + 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ))) := by
  set F : ℕ → ℝ := fun m => blockMean X μ (blockCutoff θ n) s
    (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) with hFdef
  have hsplit : (∑ m ∈ Finset.range j, F (m + r))
      = (∑ m ∈ Finset.range (r + j), F m) - ∑ m ∈ Finset.range r, F m := by
    rw [Finset.sum_range_add, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun m _ => by rw [add_comm]
  have h1 := abs_sum_blockMean_sub_le hX hθ3 hj hres hσ
  have h2 := abs_sum_blockMean_sub_le hX hθ3 (by omega : r ≤ n + 1) hres hσ
  have hcast : ((r + j : ℕ) : ℝ) = (r : ℝ) + (j : ℝ) := by push_cast; ring
  rw [hFdef] at hsplit
  rw [hsplit]
  rw [abs_le] at h1 h2 ⊢
  rw [hcast] at h1
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- **The one-fold and two-fold block means differ by the second main term**:
`blockMean₂ - blockMean = ∑_{p∈B}\mathrm{Re}(w_p\overline{p^{-s₂}}) + O(\text{errors})`.  The two
tilted block-mean estimates share the first main term, so this is their difference.  At Harper's
weights the extra term is `∑_{p∈B}\cos(t\log p)p^{-1-2σ}`, the `c_m` of the cosine drift. -/
theorem abs_blockMean₂_sub_blockMean_sub_re_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMean₂ X μ y s₁ s₂ w B - blockMean X μ y s₁ w B
        - ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re|
      ≤ (∑ p ∈ B, (160 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
            + 120 * ‖w p‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2))
        + ∑ p ∈ B, ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))‖ ^ 2
            * (1 - ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))‖)⁻¹ / 2 := by
  -- both block means are integrals of the block sum
  have hb₂ : blockMean₂ X μ y s₁ s₂ w B
      = ∫ ω, ∑ p ∈ B, localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
    rw [blockMean₂, integral_finsetSum _ fun p hp =>
      integrable_localLog_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp) (hA p hp) (hw p hp)]
  have hb₁ : blockMean X μ y s₁ w B
      = ∫ ω, ∑ p ∈ B, localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s₁ μ) := by
    rw [blockMean, integral_finsetSum _ fun p hp =>
      integrable_localLog_tiltedMeasure hX _ hs₁ (hB hp) (hw p hp)]
  have h₂ := abs_integral_sum_localLog_tiltedMeasure₂_sub_le hX y hs₁ hs₂ hB hA hw
  have h₁ := abs_integral_sum_localLog_tiltedMeasure_sub_le hX y hs₁ hB hw
  rw [← hb₂] at h₂
  rw [← hb₁] at h₁
  -- the pair's main term is the one-point's plus the second copy
  have hsplit : (∑ p ∈ B, ((w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re
        + (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re))
      = (∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re)
        + ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re :=
    Finset.sum_add_distrib
  rw [hsplit] at h₂
  set D₂ := blockMean₂ X μ y s₁ s₂ w B
    - ((∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re)
      + ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re) with hD₂
  set D₁ := blockMean X μ y s₁ w B
    - ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re with hD₁
  have hkey : blockMean₂ X μ y s₁ s₂ w B - blockMean X μ y s₁ w B
      - ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re = D₂ - D₁ := by
    rw [hD₂, hD₁]
    ring
  rw [hkey, sub_eq_add_neg]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_neg]
  exact add_le_add h₂ h₁

/-! ### The same two sums, weighted by the block index

Proposition 7's shear budget is `∑_{m<n}|r_m|(M_m + M_{m+1}) ≤ K`, and the envelope `M` **grows
linearly** in the block index: Proposition 7's envelope hypothesis makes it dominate `Bj + j`.
So what the budget consumes is not `∑|c_m|` and `∑κ_m` but their *index-weighted* forms.

Both are the unweighted argument with `m+1 ≤ 4e^{m/4}` folded in, which costs a quarter of the
geometric ratio and nothing else.  The absolute value is **inside** the sum here, which is no
harder: the per-block bounds are already absolute values.

*Why a quarter and not a half.*  For the cosine sum any exponent below `1` would do.  For `κ` the
unweighted decay is only `e^{-m/2}`, so the weight has to be absorbed at a strictly smaller rate,
and `e^{m/4}` leaves `e^{-m/4}`. -/

/-- `m + 1 ≤ 4e^{m/4}` — the crude bound that absorbs a linear envelope into a geometric tail. -/
lemma nat_add_one_le_four_mul_exp (m : ℕ) : (m : ℝ) + 1 ≤ 4 * Real.exp ((m : ℝ) / 4) := by
  linarith [Real.add_one_le_exp ((m : ℝ) / 4)]

/-- **The block weights, index-weighted and summed above a shift.** -/
lemma sum_blockWeightSize_shift_weighted_le (θ : ℝ) (r j : ℕ) :
    (∑ m ∈ Finset.range j, ((m : ℝ) + 1) * blockWeightSize θ (m + r))
      ≤ 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
        * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by
  have he0 : (0 : ℝ) < Real.exp (-(1 / 4 : ℝ)) := Real.exp_pos _
  have he1 : Real.exp (-(1 / 4 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hpow : ∀ m : ℕ, Real.exp (-(1 / 4 : ℝ)) ^ m = Real.exp (-((m : ℝ) / 4)) := by
    intro m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb : ∀ m ∈ Finset.range j, ((m : ℝ) + 1) * blockWeightSize θ (m + r)
      ≤ 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
        * Real.exp (-(1 / 4 : ℝ)) ^ m := by
    intro m _
    have hk := blockWeightSize_le_exp_neg θ (m + r)
    have hcast : ((m + r : ℕ) : ℝ) = (m : ℝ) + (r : ℝ) := by push_cast; ring
    rw [hcast] at hk
    have hk0 : (0 : ℝ) ≤ blockWeightSize θ (m + r) := (blockWeightSize_pos θ (m + r)).le
    have hexp : Real.exp ((m : ℝ) / 4)
          * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-(((m : ℝ) + (r : ℝ)) / 2)))
        = Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * Real.exp (-((m : ℝ) / 4)) := by
      simp only [← Real.exp_add]
      congr 1
      ring
    calc ((m : ℝ) + 1) * blockWeightSize θ (m + r)
        ≤ (4 * Real.exp ((m : ℝ) / 4))
            * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-(((m : ℝ) + (r : ℝ)) / 2))) :=
          mul_le_mul (nat_add_one_le_four_mul_exp m) hk hk0 (by positivity)
      _ = 4 * (Real.exp ((m : ℝ) / 4)
            * (Real.exp 1 * Real.exp (-(θ / 2))
              * Real.exp (-(((m : ℝ) + (r : ℝ)) / 2)))) := by ring
      _ = 4 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * Real.exp (-((m : ℝ) / 4))) := by rw [hexp]
      _ = 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * Real.exp (-(1 / 4 : ℝ)) ^ m := by rw [hpow m]; ring
  have hgeo : (∑ m ∈ Finset.range j, Real.exp (-(1 / 4 : ℝ)) ^ m)
      ≤ (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by
    have hsummable : Summable (fun m : ℕ => Real.exp (-(1 / 4 : ℝ)) ^ m) :=
      summable_geometric_of_lt_one he0.le he1
    calc (∑ m ∈ Finset.range j, Real.exp (-(1 / 4 : ℝ)) ^ m)
        ≤ ∑' m : ℕ, Real.exp (-(1 / 4 : ℝ)) ^ m :=
          hsummable.sum_le_tsum _ (fun m _ => by positivity)
      _ = (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := tsum_geometric_of_lt_one he0.le he1
  calc (∑ m ∈ Finset.range j, ((m : ℝ) + 1) * blockWeightSize θ (m + r))
      ≤ ∑ m ∈ Finset.range j, 4 * Real.exp 1 * Real.exp (-(θ / 2))
          * Real.exp (-((r : ℝ) / 2)) * Real.exp (-(1 / 4 : ℝ)) ^ m := Finset.sum_le_sum hb
    _ = 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * ∑ m ∈ Finset.range j, Real.exp (-(1 / 4 : ℝ)) ^ m := by rw [← Finset.mul_sum]
    _ ≤ 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)

/-- **The cosine drift above a shift, index-weighted.**  The form Proposition 7's shear budget
consumes: the linear envelope is absorbed into the geometric tail, and the bound is still
`≪ 1/(τ e^{r+θ})`, hence `≪ τe^{-θ}` at `r = ⌈2\log(1/τ)⌉`. -/
theorem exists_abs_sum_cos_primeBlockSub_shift_weighted_le :
    ∃ K > 0, ∀ (τ σ θ : ℝ) (r j : ℕ), 0 < τ → τ ≤ 1 → 0 ≤ θ →
      (∀ m, m < j → |σ| * Real.log (blockScale θ (m + r + 1)) ≤ 1) →
      (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
          |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|)
        ≤ K / (τ * Real.exp ((r : ℝ) + θ)) := by
  obtain ⟨K₁, hK₁, hblock⟩ := exists_abs_sum_cos_primeBlockSub_le
  have he0 : (0 : ℝ) < Real.exp (-(3 / 4 : ℝ)) := Real.exp_pos _
  have he1 : Real.exp (-(3 / 4 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  refine ⟨4 * K₁ * (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹, by positivity,
    fun τ σ θ r j hτ hτ1 hθ hσ => ?_⟩
  have hpow : ∀ m : ℕ, Real.exp (-(3 / 4 : ℝ)) ^ m = Real.exp (-(3 * (m : ℝ) / 4)) := by
    intro m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hden : (0 : ℝ) < τ * Real.exp ((r : ℝ) + θ) := by positivity
  have hstep : ∀ m ∈ Finset.range j, ((m : ℝ) + 1) *
      |∑ p ∈ primeBlockSub θ (m + r),
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
      ≤ 4 * K₁ / (τ * Real.exp ((r : ℝ) + θ)) * Real.exp (-(3 / 4 : ℝ)) ^ m := by
    intro m hm
    have hm' : m < j := Finset.mem_range.1 hm
    have hb := hblock τ σ θ (m + r) hτ hτ1 hθ (hσ m hm')
    have hcast : ((m + r : ℕ) : ℝ) = (m : ℝ) + (r : ℝ) := by push_cast; ring
    rw [hcast] at hb
    have hexp : Real.exp ((m : ℝ) / 4) * Real.exp ((r : ℝ) + θ)
        = Real.exp (-(3 * (m : ℝ) / 4)) * Real.exp ((m : ℝ) + (r : ℝ) + θ) := by
      simp only [← Real.exp_add]
      congr 1
      ring
    have hτ0 : τ ≠ 0 := hτ.ne'
    have hem : Real.exp ((m : ℝ) + (r : ℝ) + θ) ≠ 0 := (Real.exp_pos _).ne'
    have her : Real.exp ((r : ℝ) + θ) ≠ 0 := (Real.exp_pos _).ne'
    calc ((m : ℝ) + 1) *
          |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ (4 * Real.exp ((m : ℝ) / 4)) * (K₁ / (τ * Real.exp ((m : ℝ) + (r : ℝ) + θ))) :=
          mul_le_mul (nat_add_one_le_four_mul_exp m) hb (abs_nonneg _) (by positivity)
      _ = 4 * K₁ * (Real.exp ((m : ℝ) / 4) * Real.exp ((r : ℝ) + θ))
            / (τ * Real.exp ((m : ℝ) + (r : ℝ) + θ) * Real.exp ((r : ℝ) + θ)) := by
          field_simp
      _ = 4 * K₁ * (Real.exp (-(3 * (m : ℝ) / 4)) * Real.exp ((m : ℝ) + (r : ℝ) + θ))
            / (τ * Real.exp ((m : ℝ) + (r : ℝ) + θ) * Real.exp ((r : ℝ) + θ)) := by
          rw [hexp]
      _ = 4 * K₁ / (τ * Real.exp ((r : ℝ) + θ)) * Real.exp (-(3 / 4 : ℝ)) ^ m := by
          rw [hpow m]
          field_simp
  have hgeo : (∑ m ∈ Finset.range j, Real.exp (-(3 / 4 : ℝ)) ^ m)
      ≤ (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := by
    have hsummable : Summable (fun m : ℕ => Real.exp (-(3 / 4 : ℝ)) ^ m) :=
      summable_geometric_of_lt_one he0.le he1
    calc (∑ m ∈ Finset.range j, Real.exp (-(3 / 4 : ℝ)) ^ m)
        ≤ ∑' m : ℕ, Real.exp (-(3 / 4 : ℝ)) ^ m :=
          hsummable.sum_le_tsum _ (fun m _ => by positivity)
      _ = (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := tsum_geometric_of_lt_one he0.le he1
  calc (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
        |∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|)
      ≤ ∑ m ∈ Finset.range j,
          4 * K₁ / (τ * Real.exp ((r : ℝ) + θ)) * Real.exp (-(3 / 4 : ℝ)) ^ m :=
        Finset.sum_le_sum hstep
    _ = 4 * K₁ / (τ * Real.exp ((r : ℝ) + θ))
          * ∑ m ∈ Finset.range j, Real.exp (-(3 / 4 : ℝ)) ^ m := by rw [← Finset.mul_sum]
    _ ≤ 4 * K₁ / (τ * Real.exp ((r : ℝ) + θ)) * (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 4 * K₁ * (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ / (τ * Real.exp ((r : ℝ) + θ)) := by ring

/-! ### The pair drift at Harper's weights

`RMF.abs_blockMean₂_sub_blockMean_sub_re_le` is the bridge at an arbitrary weight; here it is at
Harper's own, `w_p = p^{-s₁}`, where all three moduli coincide and the main term becomes the block
cosine sum.  That is the shape both drift hypotheses of `RMF.proposition7_upper_of_law` consume.

The point of doing it separately is the error.  At a general weight the bridge's error is a sum
of five monomials in `‖w_p‖` and the two moduli; here each is a power of `a_p = ‖p^{-s₁}‖`, so
the error collapses to `801κ_m∑a_p²`, and block Mertens caps `∑a_p²`.  The result is `O(κ_m)`
with an absolute constant, summable over blocks by `RMF.sum_blockWeightSize_shift_le`.

`8 ≤ m + θ` turns `∑a_p² ≤ e²(1 + 60/\log x_m)` into a number: at `\log x_m ≥ e⁹` the correction
is under a percent, and Harper's `θ ≥ 125` gives it at every block. -/

/-- `\log x_m ≥ 7000` at every block Harper uses — `\log x_m = e^{m+1+θ} ≥ e⁹`. -/
lemma log_blockScale_ge {θ : ℝ} {m : ℕ} (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) :
    (7000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
  rw [log_blockScale]
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
    _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
    _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)

/-- **The block's square-weight sum is at most `8`.**  Block Mertens
(`RMF.sum_norm_sq_harperBlock_bounds`) gives `e²(1 + 60/\log x_m)`, and at `8 ≤ m + θ` the
correction is under a percent — `\log x_m ≥ e⁹ > 7000`. -/
lemma sum_norm_sq_primeBlockSub_le {θ σ : ℝ} {m : ℕ} {s : ℂ} (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ)
    (hre : s.re = 1 / 2 + σ) (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ 8 := by
  have hwn : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  obtain ⟨_, hShi⟩ := sum_norm_sq_harperBlock_bounds (blockScale θ (m + 1)) σ
    (fun p => ((p : ℕ) : ℂ) ^ (-s)) hbig hσ hwn
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := log_blockScale_ge hmθ
  have hdiv : (60 : ℝ) / Real.log (blockScale θ (m + 1)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have he2 : Real.exp 2 ≤ 7.39 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [h2]
    nlinarith [h1, h0]
  have hdiv0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by
    have hLpos : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
    positivity
  have hprod : Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1)))
      ≤ 7.39 * (1 + 1 / 100) :=
    mul_le_mul he2 (by linarith) (by linarith) (by norm_num)
  -- `primeBlockSub θ m` is `harperBlock (blockScale θ (m+1))`, but only definitionally
  have hShi' : ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2
      ≤ Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1))) := hShi
  linarith [hShi', hprod]

/-- **The bridge at Harper's weights**: the two-fold drift is the one-fold drift plus the cosine
sum, up to `O(κ_m)`. -/
theorem abs_blockMean₂_sub_blockMean_sub_cos_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    |blockMean₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)
        - blockMean X μ (blockCutoff θ n) s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)
        - ∑ p ∈ primeBlockSub θ m, Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)|
      ≤ 7000 * blockWeightSize θ m := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  have hB := primeBlockSub_subset_primesBelowSub θ hmn
  set κ := blockWeightSize θ m with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ m
  have hκm : κ ≤ 1 / 1000000 := blockWeightSize_le_millionth hm4
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s₁) with hwdef
  have hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre₁
  have hnorm₂ : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ = ‖w p‖ := by
    intro p hp
    have h : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 = ‖w p‖ ^ 2 := by
      rw [norm_sq_prime_cpow_neg p hre₂, hwn p hp]
    calc ‖((p : ℕ) : ℂ) ^ (-s₂)‖ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖w p‖ ^ 2) := by rw [h]
      _ = ‖w p‖ := Real.sqrt_sq (norm_nonneg _)
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := by
    intro p hp
    linarith [hwκ p hp]
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    rw [hnorm₂ p hp]
    have : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖w p‖ := rfl
    rw [this]
    linarith [hwκ p hp]
  have hmain := abs_blockMean₂_sub_blockMean_sub_re_le hX (blockCutoff θ n) hs₁ hs₂ hB hA hw5
  -- the main term is the cosine sum
  have hcos : ∑ p ∈ primeBlockSub θ m,
        (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re
      = ∑ p ∈ primeBlockSub θ m, Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
          / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hwdef, re_natCast_cpow_neg_mul_conj p.2.pos s₁ s₂, hre₁, hre₂,
      Real.rpow_neg (Nat.cast_nonneg _)]
    ring_nf
  rw [hcos] at hmain
  refine hmain.trans ?_
  -- the error, against `801 κ ∑‖w_p‖²`
  set S := ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun p _ => sq_nonneg _
  have herr₁ : ∑ p ∈ primeBlockSub θ m,
        (160 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
          + 120 * ‖w p‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2)
      ≤ 800 * κ * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hn₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖w p‖ := rfl
    rw [hn₁, hnorm₂ p hp]
    have hn0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hcube : ‖w p‖ * ‖w p‖ ^ 2 ≤ κ * ‖w p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hwκ p hp) (sq_nonneg _)
    nlinarith [hn0, hcube]
  have herr₂ : ∑ p ∈ primeBlockSub θ m,
        ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))‖ ^ 2
          * (1 - ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))‖)⁻¹ / 2
      ≤ κ * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hn0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hk := hwκ p hp
    have hnn : ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))‖ = ‖w p‖ ^ 2 := by
      rw [norm_mul, RCLike.norm_conj]
      have : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖w p‖ := rfl
      rw [this, sq]
    rw [hnn]
    have hlt : ‖w p‖ ^ 2 ≤ 1 / 2 := by nlinarith [hn0, hk, hκm]
    have hinv : (1 - ‖w p‖ ^ 2)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hpos : (0 : ℝ) ≤ (‖w p‖ ^ 2) ^ 2 := sq_nonneg _
    have h4 : (‖w p‖ ^ 2) ^ 2 * (1 - ‖w p‖ ^ 2)⁻¹ / 2 ≤ (‖w p‖ ^ 2) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left hinv hpos]
    have haκ : ‖w p‖ ^ 2 ≤ κ ^ 2 := by nlinarith [hn0, hk]
    have hκsq : κ ^ 2 ≤ κ := by nlinarith [hκ0, hκm]
    calc (‖w p‖ ^ 2) ^ 2 * (1 - ‖w p‖ ^ 2)⁻¹ / 2 ≤ (‖w p‖ ^ 2) ^ 2 := h4
      _ = ‖w p‖ ^ 2 * ‖w p‖ ^ 2 := by ring
      _ ≤ κ ^ 2 * ‖w p‖ ^ 2 := mul_le_mul_of_nonneg_right haκ (sq_nonneg _)
      _ ≤ κ * ‖w p‖ ^ 2 := mul_le_mul_of_nonneg_right hκsq (sq_nonneg _)
  have hSb : S ≤ 8 := sum_norm_sq_primeBlockSub_le hmθ hre₁ hσ
  have h800 : 800 * κ * S ≤ 6400 * κ := by nlinarith [hSb, hκ0, hS0]
  have h1 : κ * S ≤ 8 * κ := by nlinarith [hSb, hκ0]
  linarith [herr₁, herr₂, h800, h1, hκ0]

/-- **Proposition 7's first drift hypothesis, at Harper's data**: above the shift the two-fold
drift is `1` per block up to a constant `C` independent of the space and every parameter.  From
`RMF.abs_sum_blockMean_shift_sub_le`, `RMF.exists_abs_sum_cos_primeBlockSub_shift_le`, and the
bridge's error via `RMF.abs_blockMean₂_sub_blockMean_sub_cos_le` and
`RMF.sum_blockWeightSize_shift_le`.  The shift condition `1 ≤ τe^{r+θ}` keeps `C` independent of
`τ`; below the shift the drift is about `2` per block. -/
theorem exists_abs_sum_blockMean₂_shift_sub_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        |(∑ m ∈ Finset.range j, blockMean₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))) - (j : ℝ)| ≤ C := by
  obtain ⟨K, hK, hcos⟩ := exists_abs_sum_cos_primeBlockSub_shift_le
  have he1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  refine ⟨2 * (124 * Real.exp 2 + 4 * Real.exp 2 * Real.exp 2) + K
      + 7000 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹), by positivity, ?_⟩
  intro Ω' _ X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  -- the three families
  set A : ℕ → ℝ := fun m => blockMean₂ X μ (blockCutoff θ n) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) with hA
  set B : ℕ → ℝ := fun m => blockMean X μ (blockCutoff θ n) s₁
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) with hBdef
  set Cf : ℕ → ℝ := fun m => ∑ p ∈ primeBlockSub θ (m + r),
    Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) with hCf
  -- the cosine sum does not see the sign of the height difference
  have hcoseq : ∀ m : ℕ, (∑ p ∈ primeBlockSub θ (m + r),
      Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
      = Cf m := by
    intro m
    rw [hCf]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases (abs_eq hτ0.le).1 hτeq with h | h
    · rw [h]
    · rw [h, show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring,
        Real.cos_neg]
  -- the one-fold drift
  have hmert := abs_sum_blockMean_shift_sub_le hX (by linarith : (5 : ℝ) ≤ θ) hj hre₁ hσ
  have hmert' : |(∑ m ∈ Finset.range j, B m) - (j : ℝ)|
      ≤ 2 * (124 * Real.exp 2 + 4 * Real.exp 2 * Real.exp 2) := by
    refine hmert.trans ?_
    have h1 : Real.exp (-(1 + θ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h2 : Real.exp (-θ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have he2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
    have q1 : Real.exp 2 * Real.exp (-(1 + θ)) ≤ Real.exp 2 * 1 :=
      mul_le_mul_of_nonneg_left h1 he2.le
    have q2 : Real.exp 2 * Real.exp 2 * Real.exp (-θ) ≤ Real.exp 2 * Real.exp 2 * 1 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [q1, q2]
  -- the cosine excess
  have hcosb : |∑ m ∈ Finset.range j, Cf m| ≤ K := by
    have h := hcos τ σ θ r j hτ0 hτ1 hθ0 (fun m hm => hσm (m + r) (by omega))
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hK, hshift]
  -- the bridge's error
  have herr : ∀ m ∈ Finset.range j, |A m - B m - Cf m| ≤ 7000 * blockWeightSize θ (m + r) := by
    intro m hm
    have hm' : m < j := Finset.mem_range.1 hm
    have hmr : m + r ≤ n := by omega
    have hb := abs_blockMean₂_sub_blockMean_sub_cos_le hX
      (show (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ by
        push_cast
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith)
      hmr hre₁ hre₂ (hσm (m + r) hmr)
    rwa [hcoseq m] at hb
  have herrsum : |∑ m ∈ Finset.range j, (A m - B m - Cf m)|
      ≤ 7000 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum herr).trans ?_
    rw [← Finset.mul_sum]
    have hks := sum_blockWeightSize_shift_le θ r j
    have hθb : Real.exp (-(θ / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hrb : Real.exp (-((r : ℝ) / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hinv0 : (0 : ℝ) < (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := by
      have : (0 : ℝ) < 1 - Real.exp (-(1 / 2 : ℝ)) := by linarith
      positivity
    refine mul_le_mul_of_nonneg_left (hks.trans ?_) (by norm_num)
    calc Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹
        ≤ Real.exp 1 * 1 * 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := by gcongr
      _ = Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := by ring
  -- and the identity that puts them together
  have hid : (∑ m ∈ Finset.range j, A m) - (j : ℝ)
      = ((∑ m ∈ Finset.range j, B m) - (j : ℝ)) + (∑ m ∈ Finset.range j, Cf m)
        + ∑ m ∈ Finset.range j, (A m - B m - Cf m) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans (add_le_add hmert' hcosb)) herrsum |>.trans ?_
  linarith

/-! ### The second coordinate, by symmetry

`RMF.tiltExponent₂` is a sum of the two one-fold exponents, so the two-fold tilt does not see the
order of the heights (`RMF.tiltedMeasure₂_comm`).  The second coordinate's drift is the first
coordinate's at the swapped pair, and `RMF.exists_abs_sum_blockMean₂_shift_sub_le` covers it: its
hypotheses are symmetric in `s₁, s₂` up to `|s₁.im - s₂.im| = τ`. -/

/-- **The two-fold tilt is symmetric in its two heights.** -/
lemma tiltedMeasure₂_comm (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s₁ s₂ : ℂ) (μ : Measure Ω) :
    tiltedMeasure₂ f y s₁ s₂ μ = tiltedMeasure₂ f y s₂ s₁ μ := by
  have h : tiltExponent₂ f y s₁ s₂ = tiltExponent₂ f y s₂ s₁ := by
    funext ω
    rw [tiltExponent₂, tiltExponent₂]
    ring
  rw [tiltedMeasure₂, tiltedMeasure₂, h]

/-- **The block mean is symmetric in the two heights**, the weight being held fixed. -/
lemma blockMean₂_comm (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) :
    blockMean₂ X μ y s₁ s₂ w B = blockMean₂ X μ y s₂ s₁ w B := by
  rw [blockMean₂, blockMean₂,
    tiltedMeasure₂_comm (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ]

/-- **Proposition 7's drift, at the second coordinate's weight.**  The same constant, because it
is the same theorem at the swapped pair. -/
theorem exists_abs_sum_blockMean₂_snd_shift_sub_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        |(∑ m ∈ Finset.range j, blockMean₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))) - (j : ℝ)| ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_abs_sum_blockMean₂_shift_sub_le
  refine ⟨C, hC, ?_⟩
  intro Ω' _ X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift
  have hcomm : ∀ m : ℕ, blockMean₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
      = blockMean₂ X μ (blockCutoff θ n) s₂ s₁
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r)) :=
    fun m => blockMean₂_comm X μ (blockCutoff θ n) s₁ s₂ _ _
  simp only [hcomm]
  exact h Ω' X μ hX θ σ τ n r j s₂ s₁ hθ hj hre₂ hre₁ hσ hτ0 hτ1
    (by rw [abs_sub_comm]; exact hτeq) hshift

/-! ### The regression slope

`ρ_m = \mathrm{cov}_m/V_m` is what the realisation calls `r m`, and it is what the *second* drift
and the shear budget both need controlled.  Two facts make it small above the shift: the block
covariance **is** the cosine sum (`RMF.abs_blockMatchedCov_prime_sub_le`), and the block variance
is bounded below by `1/16` (`RMF.blockMatchedVar₂_concrete`, read at the global cutoff through
`RMF.blockStats₂_blockCutoff_eq`).  So `|ρ_m| ≪ |c_m| + κ_m`, and both sum geometrically.

The index-weighted form is stated because the shear budget weights by the envelope; it implies
the unweighted one, the weight being at least `1`. -/

/-- **The block variance bracket, at the global tilt cutoff.**
`RMF.blockMatchedVar₂_concrete` is stated at the block's own cutoff;
`RMF.blockStats₂_blockCutoff_eq` moves it, which is all that separates the single-block
development from the assembly. -/
lemma blockMatchedVar₂_bracket_global {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    {w : Nat.Primes → ℂ} (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    1 / 16 ≤ ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ)
      ∧ ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ≤ 9 / 2 := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  have hVeq := (blockStats₂_blockCutoff_eq hX hs₁ hs₂ (θ := θ) hmn w w).2.1
  obtain ⟨hlo, hhi⟩ := blockMatchedVar₂_concrete hX θ σ m s₁ s₂ w hmθ hre₁ hre₂ hσ hwn
  -- `blockCutoff θ m` is `⌊blockScale θ (m+1)⌋₊ + 1`, but only definitionally
  have hlo' : 1 / 8 ≤ 2 * ((blockMatchedVar₂ X μ (blockCutoff θ m) s₁ s₂ w
      (primeBlockSub θ m) : ℝ≥0) : ℝ) := hlo
  have hhi' : 2 * ((blockMatchedVar₂ X μ (blockCutoff θ m) s₁ s₂ w
      (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9 := hhi
  rw [hVeq]
  constructor <;> linarith

/-- **The block covariance, against the cosine sum and the weight size.**
`RMF.abs_blockMatchedCov_prime_sub_le` with the cube sum evaluated: `∑a_p³ ≤ κ_m∑a_p² ≤ 8κ_m`. -/
theorem abs_blockMatchedCov_prime_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    |blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)|
      ≤ |∑ p ∈ primeBlockSub θ m,
            Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)| / 2
        + 4800 * blockWeightSize θ m := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  set κ := blockWeightSize θ m with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ m
  have hwn : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre₁
  have hcov := abs_blockMatchedCov_prime_sub_le hX hm3 hmn hre₁ hre₂ hσ
  set cov := blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
    (primeBlockSub θ m) with hcovdef
  set Cs := ∑ p ∈ primeBlockSub θ m,
    Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) with hCs
  have hmainform : (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-(1 + 2 * σ))
        * Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / 2) = Cs / 2 := by
    rw [hCs, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  rw [hmainform] at hcov
  have hcube : ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 ≤ 8 * κ := by
    have hS := sum_norm_sq_primeBlockSub_le hmθ hre₁ hσ
    have hstep : ∀ p ∈ primeBlockSub θ m,
        ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 ≤ κ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := by
      intro p hp
      have hb : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ κ :=
        norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
      nlinarith [norm_nonneg (((p : ℕ) : ℂ) ^ (-s₁)), sq_nonneg (‖((p : ℕ) : ℂ) ^ (-s₁)‖)]
    calc ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3
        ≤ ∑ p ∈ primeBlockSub θ m, κ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := Finset.sum_le_sum hstep
      _ = κ * ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ κ * 8 := mul_le_mul_of_nonneg_left hS hκ0.le
      _ = 8 * κ := by ring
  have h1 := abs_add_le (cov - Cs / 2) (Cs / 2)
  rw [sub_add_cancel] at h1
  have h2 : |Cs / 2| = |Cs| / 2 := by
    rw [abs_div]
    norm_num
  rw [h2] at h1
  linarith [hcov, hcube, h1]

/-- **The regression slope of one block**, against the cosine sum and the weight size. -/
theorem abs_pairSlope_block_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    |pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m))|
      ≤ 8 * |∑ p ∈ primeBlockSub θ m,
            Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)|
        + 76800 * blockWeightSize θ m := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  set κ := blockWeightSize θ m with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ m
  have hwn : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre₁
  set V := ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) with hVdef
  have hV : 1 / 16 ≤ V :=
    (blockMatchedVar₂_bracket_global hX hmθ hmn hre₁ hre₂ hσ hwn).1
  have hVpos : (0 : ℝ) < V := by linarith
  -- the covariance is the cosine sum
  have hcov := abs_blockMatchedCov_prime_sub_le hX hm3 hmn hre₁ hre₂ hσ
  set cov := blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
    (primeBlockSub θ m) with hcovdef
  set Cs := ∑ p ∈ primeBlockSub θ m,
    Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) with hCs
  have hmainform : (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-(1 + 2 * σ))
        * Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / 2) = Cs / 2 := by
    rw [hCs, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  rw [hmainform] at hcov
  -- the cube sum against the weight size
  have hcube : ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 ≤ 8 * κ := by
    have hS := sum_norm_sq_primeBlockSub_le hmθ hre₁ hσ
    have hstep : ∀ p ∈ primeBlockSub θ m,
        ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 ≤ κ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := by
      intro p hp
      have hb : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ κ :=
        norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
      nlinarith [norm_nonneg (((p : ℕ) : ℂ) ^ (-s₁)), sq_nonneg (‖((p : ℕ) : ℂ) ^ (-s₁)‖)]
    calc ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3
        ≤ ∑ p ∈ primeBlockSub θ m, κ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := Finset.sum_le_sum hstep
      _ = κ * ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ κ * 8 := mul_le_mul_of_nonneg_left hS hκ0.le
      _ = 8 * κ := by ring
  have hcovb : |cov| ≤ |Cs| / 2 + 4800 * κ :=
    abs_blockMatchedCov_prime_le hX hmθ hmn hre₁ hre₂ hσ
  -- the slope
  have hslope : |pairSlope V cov| ≤ 16 * |cov| := by
    rw [pairSlope, abs_div, abs_of_pos hVpos, div_le_iff₀ hVpos]
    nlinarith [abs_nonneg cov, hV]
  linarith [hslope, hcovb, abs_nonneg Cs]

/-- **The shear budget**: the regression slopes, weighted by `m + 1` and summed above the shift,
are at most `C`, independent of the space and every parameter.  The weight is what Proposition 7's
`∑|r_m|(M_m + M_{m+1}) ≤ K` needs, the envelope being linear in the block index; `C` stays bounded
only because the envelope is chosen free of `a` (`RMF.proposition7_upper_of_law`).  Since
`m + 1 ≥ 1` it also bounds the unweighted sum. -/
theorem exists_sum_abs_pairSlope_shift_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
            |pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|) ≤ C := by
  obtain ⟨K, hK, hcos⟩ := exists_abs_sum_cos_primeBlockSub_shift_weighted_le
  have he1 : Real.exp (-(1 / 4 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  refine ⟨8 * K + 76800 * (4 * Real.exp 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹),
    by positivity, ?_⟩
  intro Ω' _ X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  -- the cosine sum does not see the sign of the height difference
  have hcoseq : ∀ k : ℕ, (∑ p ∈ primeBlockSub θ k,
      Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
      = ∑ p ∈ primeBlockSub θ k,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro k
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases (abs_eq hτ0.le).1 hτeq with h | h
    · rw [h]
    · rw [h, show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring,
        Real.cos_neg]
  -- per block
  have hstep : ∀ m ∈ Finset.range j, ((m : ℝ) + 1) *
      |pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
        (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ (m + r)))|
      ≤ 8 * (((m : ℝ) + 1) * |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)|)
        + 76800 * (((m : ℝ) + 1) * blockWeightSize θ (m + r)) := by
    intro m hm
    have hm' : m < j := Finset.mem_range.1 hm
    have hmr : m + r ≤ n := by omega
    have hb := abs_pairSlope_block_le hX
      (show (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ by
        push_cast
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith)
      hmr hre₁ hre₂ (hσm (m + r) hmr)
    rw [hcoseq (m + r)] at hb
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith [hb, hm1, abs_nonneg (∑ p ∈ primeBlockSub θ (m + r),
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)),
      (blockWeightSize_pos θ (m + r)).le]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the two geometric tails
  have hc := hcos τ σ θ r j hτ0 hτ1 hθ0 (fun m hm => hσm (m + r) (by omega))
  have hcb : (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
      |∑ p ∈ primeBlockSub θ (m + r),
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)|) ≤ K := by
    refine hc.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hK, hshift]
  have hkb : (∑ m ∈ Finset.range j, ((m : ℝ) + 1) * blockWeightSize θ (m + r))
      ≤ 4 * Real.exp 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by
    refine (sum_blockWeightSize_shift_weighted_le θ r j).trans ?_
    have hθb : Real.exp (-(θ / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hrb : Real.exp (-((r : ℝ) / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hinv0 : (0 : ℝ) < (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by
      have : (0 : ℝ) < 1 - Real.exp (-(1 / 4 : ℝ)) := by linarith
      positivity
    calc 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹
        ≤ 4 * Real.exp 1 * 1 * 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by gcongr
      _ = 4 * Real.exp 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by ring
  have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
      |∑ p ∈ primeBlockSub θ (m + r),
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)| :=
    Finset.sum_nonneg fun m _ => by positivity
  linarith [hcb, hkb]

/-- **The two-fold block drift is at most `15`**, at every block Harper uses.
`RMF.abs_blockMean₂_le` with its two corrections evaluated: `κ_m ≤ 10^{-6}` and
`60/\log x_m ≤ 1/100`. -/
lemma abs_blockMean₂_le_fifteen {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ} {w : Nat.Primes → ℂ}
    (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    |blockMean₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ m)| ≤ 15 := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) + θ := by linarith
  refine (abs_blockMean₂_le hX hm4 hmn hre₁ hre₂ hσ hwn).trans ?_
  have hκ0 := (blockWeightSize_pos θ m).le
  have hκm := blockWeightSize_le_millionth hm4
  have hL := log_blockScale_ge hmθ
  have hdiv : (60 : ℝ) / Real.log (blockScale θ (m + 1)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hdiv0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by
    have hLpos : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
    positivity
  have he2 : Real.exp 2 ≤ 7.39 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [h2]
    nlinarith [h1, h0]
  have hprod : Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1))) ≤ 7.39 * (1 + 1 / 100) :=
    mul_le_mul he2 (by linarith) (by linarith) (by norm_num)
  nlinarith [hκ0, hκm, hprod, Real.exp_pos (2 : ℝ), hdiv0]

/-- **Proposition 7's second drift hypothesis, at Harper's data.**  The realisation forces
`θ₂ = m₂ - ρm₁`: the shear carries the first coordinate's drift into the second.  The ingredients
are `RMF.exists_abs_sum_blockMean₂_snd_shift_sub_le` for `∑m₂` and
`RMF.exists_sum_abs_pairSlope_shift_le` for `∑|ρ_m|`, against the crude
`RMF.abs_blockMean₂_le_fifteen` for `m₁`. -/
theorem exists_abs_sum_blockMean₂_regression_shift_sub_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        |(∑ m ∈ Finset.range j,
            (blockMean₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
              - pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
                (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                  (primeBlockSub θ (m + r)))
                * blockMean₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))) - (j : ℝ)|
          ≤ C := by
  obtain ⟨C₁, hC₁, hsnd⟩ := exists_abs_sum_blockMean₂_snd_shift_sub_le
  obtain ⟨C₂, hC₂, hslope⟩ := exists_sum_abs_pairSlope_shift_le
  refine ⟨C₁ + 15 * C₂, by positivity, ?_⟩
  intro Ω' _ X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  set M₂ : ℕ → ℝ := fun m => blockMean₂ X μ (blockCutoff θ n) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r)) with hM₂
  set M₁ : ℕ → ℝ := fun m => blockMean₂ X μ (blockCutoff θ n) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) with hM₁
  set R : ℕ → ℝ := fun m => pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
    (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
      (primeBlockSub θ (m + r))) with hR
  have hid : (∑ m ∈ Finset.range j, (M₂ m - R m * M₁ m)) - (j : ℝ)
      = ((∑ m ∈ Finset.range j, M₂ m) - (j : ℝ)) - ∑ m ∈ Finset.range j, R m * M₁ m := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  refine (abs_sub _ _).trans ?_
  refine add_le_add (hsnd Ω' X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift) ?_
  -- the shear term
  have hbound : ∀ m ∈ Finset.range j, |R m * M₁ m| ≤ 15 * (((m : ℝ) + 1) * |R m|) := by
    intro m hm
    have hm' : m < j := Finset.mem_range.1 hm
    have hmr : m + r ≤ n := by omega
    have hm8 : (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ := by
      push_cast
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hM₁b : |M₁ m| ≤ 15 := abs_blockMean₂_le_fifteen hX hm8 hmr hre₁ hre₂
      (hσm (m + r) hmr) (fun p _ => norm_sq_prime_cpow_neg p hre₁)
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [abs_mul]
    nlinarith [abs_nonneg (R m), abs_nonneg (M₁ m), hM₁b, hm1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (hslope Ω' X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift) (by norm_num)

/-! ### Shifting the block index is shifting `θ`

`blockScale θ j = e^{e^{j+θ}}` sees `j` and `θ` only through `j + θ`, so starting the blocks at
`r` is starting at `0` with offset `θ + r`.  This is how the two-point block comparison
(`RMF.exists_isBoxComparison_steinhaus_of_range`) is applied above the shift: its hypotheses
`hcov` and `henvc`, false at the low blocks where the two heights are still correlated, are asked
for only above it. -/

lemma blockScale_add_nat (θ : ℝ) (r j : ℕ) : blockScale (θ + r) j = blockScale θ (j + r) := by
  rw [blockScale, blockScale]
  congr 2
  push_cast
  ring

lemma primeBlockSub_add_nat (θ : ℝ) (r j : ℕ) :
    primeBlockSub (θ + r) j = primeBlockSub θ (j + r) := by
  rw [primeBlockSub, primeBlockSub, blockScale_add_nat,
    show j + 1 + r = j + r + 1 from by omega]

lemma blockCutoff_add_nat (θ : ℝ) (r n : ℕ) : blockCutoff (θ + r) n = blockCutoff θ (n + r) := by
  rw [blockCutoff, blockCutoff, blockScale_add_nat, show n + 1 + r = n + r + 1 from by omega]

/-! ### The tilt stays at the top; the scale condition drops

The expansion identity tilts at the Euler cutoff, Harper's `⌊x⌋+1`, so the tilt index cannot be
lowered, and there the tilt scale is `|σ|\log x = 4V`, not `≤ 1`: a hypothesis
`|σ|\log(\text{blockScale }θ\,(N+1)) ≤ 1` has no instances at Harper's data.  As on the one-point
side (`RMF.exists_isWindowComparison_steinhaus_of_top`), the barrier stops `d = ⌊\log V⌋+3` blocks
short of the tilt, where `4V/e^d ≤ 4/e³ < 1`.  `RMF.exists_isBoxComparison_steinhaus_of_range`
separates the two indices; the block statistics do not see the cutoff above the block. -/

/-- **The three block statistics do not see the cutoff**, as long as it is above the block — so a
statistic computed at the tilt's index may be read at the barrier's. -/
lemma blockStats₂_shift_cutoff_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {θ : ℝ} {k n N : ℕ} (hkn : k ≤ n) (hnN : n ≤ N) (v w : Nat.Primes → ℂ) :
    blockMean₂ X μ (blockCutoff θ N) s₁ s₂ w (primeBlockSub θ k)
        = blockMean₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ k)
      ∧ ((blockMatchedVar₂ X μ (blockCutoff θ N) s₁ s₂ w (primeBlockSub θ k) : ℝ≥0) : ℝ)
        = ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ k) : ℝ≥0) : ℝ)
      ∧ blockMatchedCov X μ (blockCutoff θ N) s₁ s₂ v w (primeBlockSub θ k)
        = blockMatchedCov X μ (blockCutoff θ n) s₁ s₂ v w (primeBlockSub θ k) := by
  have h1 : primeBlockSub θ k ⊆ primesBelowSub (blockCutoff θ N) :=
    primeBlockSub_subset_primesBelowSub θ (hkn.trans hnN)
  have h2 : primeBlockSub θ k ⊆ primesBelowSub (blockCutoff θ n) :=
    primeBlockSub_subset_primesBelowSub θ hkn
  refine ⟨blockMean₂_congr_cutoff hX hs₁ hs₂ h1 h2 w, ?_,
    blockMatchedCov_congr_cutoff hX hs₁ hs₂ h1 h2 v w⟩
  rw [blockMatchedVar₂_congr_cutoff hX hs₁ hs₂ h1 h2 w]

/-! ### Proposition 7 for the Steinhaus RMF

Every hypothesis of `RMF.proposition7_upper_of_law` is discharged from a named source: the family
and its laws by `RMF.exists_isBoxComparison_steinhaus_of_range` at `θ + r`; the variance brackets
by `RMF.blockMatchedVar₂_concrete`, `RMF.blockStats₂_blockCutoff_eq`, `RMF.pairResidVar_bracket`
and `abs_pairSlope_le_and_cs_of_abs_le`; the drifts by `RMF.exists_abs_sum_blockMean₂_shift_sub_le`
and `RMF.exists_abs_sum_blockMean₂_regression_shift_sub_le`; the shear budget by
`RMF.exists_sum_abs_pairSlope_shift_le` and `RMF.boxEnvelope_spec`; the covariance bound by
`RMF.abs_blockMatchedCov_prime_le`, above the shift.

The comparison's `hcov` (`|\mathrm{cov}_m| ≤ 1/100`) is false at the low blocks, where the
covariance is about `1/2`; applying it at offset `θ + r` asks for it only above the shift.  The
five block parameters are replaced by `(0,0,1,1,0)` above `n`, where the statistics stop being
meaningful and every sum has stopped.  `henvc` stays a hypothesis; `RMF.boxEnvelope_pair_le`
meets it once `RMF.blockOffsetThreshold ≤ θ + r`. -/

/-- **Proposition 7's constant**, `3(R(1+2\max(C_1,C_2))(15 + B + (52+4B)C_3 + 10\log 2))^2` at
`R = result1Const (1/18) (9/2)` and `B = blockSlope 125`: the two drift constants, the shear
constant, and Probability Result 1's own constant at the pair's variance bracket. -/
noncomputable def prop7UpperConst (C₁ C₂ C₃ : ℝ) : ℝ :=
  3 * (result1Const (1 / 18) (9 / 2) * (1 + 2 * max C₁ C₂)
    * (15 + blockSlope 125 + (52 + 4 * blockSlope 125) * C₃ + 10 * Real.log 2)) ^ 2

/-- **Proposition 7's window**, `200K_1 + 1`, with `K_1` the constant of
`RMF.exists_abs_sum_cos_primeBlockSub_le`. -/
noncomputable def prop7Window (K₁ : ℝ) : ℝ := 200 * K₁ + 1

lemma prop7UpperConst_pos {C₁ C₂ C₃ : ℝ} (hC₁ : 0 < C₁) (hC₃ : 0 < C₃) :
    0 < prop7UpperConst C₁ C₂ C₃ := by
  have hB : (0 : ℝ) < blockSlope 125 := blockSlope_pos 125
  have hRC : (1 : ℝ) ≤ result1Const (1 / 18) (9 / 2) := one_le_result1Const _ _
  have hmax : (0 : ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : (0 : ℝ) < 15 + blockSlope 125 + (52 + 4 * blockSlope 125) * C₃ + 10 * Real.log 2 := by
    nlinarith [hB, hC₃, hlog2]
  rw [prop7UpperConst]
  positivity

lemma prop7Window_pos {K₁ : ℝ} (hK₁ : 0 < K₁) : 0 < prop7Window K₁ := by
  rw [prop7Window]
  linarith

/-- **`RMF.exists_proposition7_upper_steinhaus` with its constant and window named.**  The
constant is `RMF.prop7UpperConst C₁ C₂ C₃` in the two drift constants and the shear constant,
and the window is `RMF.prop7Window K₁ = 200K_1 + 1`. -/
theorem le_proposition7_upper_steinhaus_of_parts.{u} {C₁ C₂ C₃ K₁ : ℝ}
    (hC₁ : 0 < C₁) (hC₃ : 0 < C₃) (hK₁ : 0 < K₁)
    (hdrift₁ :
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        |(∑ m ∈ Finset.range j, blockMean₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))) - (j : ℝ)| ≤ C₁)
    (hdrift₂ :
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        |(∑ m ∈ Finset.range j,
            (blockMean₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
              - pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
                (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                  (primeBlockSub θ (m + r)))
                * blockMean₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))) - (j : ℝ)|
          ≤ C₂)
    (hshear :
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
            |pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|) ≤ C₃)
    (hcosblock :
      ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → τ ≤ 1 → 0 ≤ θ →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ K₁ / (τ * Real.exp ((m : ℝ) + θ))) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ →
      ∀ (θ σ τ a : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
        (125 : ℝ) ≤ θ → r + n ≤ N →
        s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → prop7Window K₁ ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < n →
          boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
              + blockWindow m + blockWindow m + 13
            ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
        max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
              (blockCutoff θ N) s₁ s₂ μ)
            (barrierEventPair
              (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
                (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                  localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) n
              (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
              (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
            ≤ prop7UpperConst C₁ C₂ C₃ * min 1 (a / Real.sqrt n) ^ 2 := by
  rw [prop7UpperConst, prop7Window]
  have hB : (0 : ℝ) < blockSlope 125 := blockSlope_pos 125
  have hRC : (1 : ℝ) ≤ result1Const (1 / 18) (9 / 2) := one_le_result1Const _ _
  have hmax : (0 : ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : (0 : ℝ) < result1Const (1 / 18) (9 / 2) * (1 + 2 * max C₁ C₂)
      * (15 + blockSlope 125 + (52 + 4 * blockSlope 125) * C₃ + 10 * Real.log 2) := by
    have h2 : (0 : ℝ)
        < 15 + blockSlope 125 + (52 + 4 * blockSlope 125) * C₃ + 10 * Real.log 2 := by
      nlinarith [hB, hC₃, hlog2]
    exact mul_pos (mul_pos (by linarith) (by linarith)) h2
  intro Ω' _ X μ hX θ σ τ a N r n s₁ s₂ hf hθ hrn hre₁ hre₂ hσtop hτ0 hτ1 hτeq hTsh henvc
    ha hn4 hbig hbig2 hhf
  set B := blockSlope 125 with hBdef
  set M : ℕ → ℝ := boxEnvelope B with hMdef
  set M' : ℕ → ℝ := fun m => M m + M (m + 1) + blockWindow m with hM'def
  obtain ⟨hM0, hMup, hMlin⟩ := boxEnvelope_spec hB a
  have hshift : (1 : ℝ) ≤ τ * Real.exp ((r : ℝ) + θ) := by
    nlinarith [hTsh, hK₁]
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ r + n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 :=
    hsigma_of_top hσtop
  have hm3₀ : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + θ := by
    push_cast
    linarith
  have hsre₁ : 0 < s₁.re := re_pos_of_block hm3₀ hre₁ (hσm 0 (by omega))
  have hsre₂ : 0 < s₂.re := re_pos_of_block hm3₀ hre₂ (hσm 0 (by omega))
  have hrcast : ∀ m : ℕ, (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ := by
    intro m
    push_cast
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  -- the covariance is small above the shift, at every block below the cutoff
  have hcovsmall : ∀ m, m ≤ n →
      |blockMatchedCov X μ (blockCutoff θ (r + n)) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ (m + r))| ≤ 1 / 100 := by
    intro m hm
    have hmn : m + r ≤ r + n := by omega
    have hb := abs_blockMatchedCov_prime_le hX (hrcast m) hmn hre₁ hre₂ (hσm (m + r) hmn)
    have hcos := hcosblock τ σ θ (m + r) hτ0 hτ1 hθ0 (hσm (m + r) hmn)
    have hcoseq : (∑ p ∈ primeBlockSub θ (m + r),
        Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
        = ∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rcases (abs_eq hτ0.le).1 hτeq with h | h
      · rw [h]
      · rw [h, show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    rw [hcoseq] at hb
    -- the cosine part, against the shift threshold
    have hden : (0 : ℝ) < τ * Real.exp (((m + r : ℕ) : ℝ) + θ) := by positivity
    have hmono : τ * Real.exp ((r : ℝ) + θ) ≤ τ * Real.exp (((m + r : ℕ) : ℝ) + θ) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hτ0.le
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hcosb : |∑ p ∈ primeBlockSub θ (m + r),
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)| ≤ 1 / 200 := by
      refine hcos.trans ?_
      rw [div_le_iff₀ hden]
      nlinarith [hTsh, hmono, hK₁]
    have hκm : blockWeightSize θ (m + r) ≤ 1 / 1000000 :=
      blockWeightSize_le_millionth (by linarith [hrcast m])
    linarith [hb, hcosb, hκm]
  -- the two-point comparison above the shift, which is the comparison at offset `θ + r`
  have hθ' : (125 : ℝ) ≤ θ + r := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have hσtop' : |σ| * Real.log (blockScale (θ + r) (n + 1)) ≤ 1 := by
    rw [blockScale_add_nat, show n + 1 + r = n + r + 1 from by omega]
    exact hσm (n + r) (by omega)
  have hcov' : ∀ m, m < n → |blockMatchedCov X μ (blockCutoff (θ + r) (N - r)) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
      (primeBlockSub (θ + r) m)| ≤ 1 / 100 := by
    intro m hm
    rw [blockCutoff_add_nat, primeBlockSub_add_nat, show N - r + r = N from by omega,
      (blockStats₂_shift_cutoff_eq hX hsre₁ hsre₂ (by omega : m + r ≤ r + n)
        (by omega : r + n ≤ N) (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂))).2.2]
    exact hcovsmall m (by omega)
  have henvc' : ∀ m, m < n → M' m + blockWindow m + 13
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1))) := by
    intro m hm
    have h := henvc m hm
    rw [hM'def, hMdef]
    linarith [h]
  obtain ⟨Ω₂, mΩ₂, Q, Nb, hQ, hNbm, hNbi, hNblaw, hcmpAll⟩ :=
    exists_isBoxComparison_steinhaus_of_range (M := M') hX hθ' (by omega : n ≤ N - r)
      hre₁ hre₂ hσtop' hcov' henvc'
  have hcut : blockCutoff (θ + r) (N - r) = blockCutoff θ N := by
    rw [blockCutoff_add_nat, show N - r + r = N from by omega]
  simp only [hcut, primeBlockSub_add_nat] at hNblaw hcmpAll
  -- the five parameters, capped above `n` where the block statistics stop being meaningful
  set m₁ : ℕ → ℝ := fun i => if i < n then blockMean₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) else 0 with hm₁def
  set m₂ : ℕ → ℝ := fun i => if i < n then blockMean₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (i + r)) else 0 with hm₂def
  set V₁ : ℕ → ℝ := fun i => if i < n then ((blockMatchedVar₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) : ℝ≥0) : ℝ) else 1 with hV₁def
  set V₂ : ℕ → ℝ := fun i => if i < n then ((blockMatchedVar₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (i + r)) : ℝ≥0) : ℝ) else 1 with hV₂def
  set cvv : ℕ → ℝ := fun i => if i < n then blockMatchedCov X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
    (primeBlockSub θ (i + r)) else 0 with hcvvdef
  have hwn₁ : ∀ i : ℕ, ∀ p ∈ primeBlockSub θ (i + r),
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun _ p _ => norm_sq_prime_cpow_neg p hre₁
  have hwn₂ : ∀ i : ℕ, ∀ p ∈ primeBlockSub θ (i + r),
      ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun _ p _ => norm_sq_prime_cpow_neg p hre₂
  -- the two variance brackets
  have hbr : ∀ i, i < n → (1 / 16 ≤ V₁ i ∧ V₁ i ≤ 9 / 2) ∧ (1 / 16 ≤ V₂ i ∧ V₂ i ≤ 9 / 2) := by
    intro i hi
    have hir : i + r ≤ r + n := by omega
    have hσi := hσm (i + r) hir
    rw [hV₁def, hV₂def]
    simp only [if_pos hi]
    exact ⟨blockMatchedVar₂_bracket_global hX (hrcast i) hir hre₁ hre₂ hσi (hwn₁ i),
      blockMatchedVar₂_bracket_global hX (hrcast i) hir hre₁ hre₂ hσi (hwn₂ i)⟩
  have hlo₁ : ∀ i, (1 : ℝ) / 18 ≤ V₁ i := by
    intro i
    by_cases hi : i < n
    · linarith [(hbr i hi).1.1]
    · rw [hV₁def]
      simp only [if_neg hi]
      norm_num
  have hhi₁ : ∀ i, V₁ i ≤ 9 / 2 := by
    intro i
    by_cases hi : i < n
    · linarith [(hbr i hi).1.2]
    · rw [hV₁def]
      simp only [if_neg hi]
      norm_num
  have hres₁ : ∀ i, (1 : ℝ) / 18 ≤ pairResidVar (V₁ i) (V₂ i) (cvv i)
      ∧ pairResidVar (V₁ i) (V₂ i) (cvv i) ≤ 9 / 2 := by
    intro i
    by_cases hi : i < n
    · obtain ⟨⟨h₁l, h₁u⟩, ⟨h₂l, h₂u⟩⟩ := hbr i hi
      have hcv : |cvv i| ≤ 1 / 100 := by
        rw [hcvvdef]
        simp only [if_pos hi]
        exact hcovsmall i (by omega)
      have hcs := (abs_pairSlope_le_and_cs_of_abs_le h₁l h₂l hcv).2
      have hb := pairResidVar_bracket (by linarith : (0 : ℝ) < V₁ i) (by linarith)
        (by linarith) hcs
      constructor <;> linarith [hb.1, hb.2]
    · rw [hV₁def, hV₂def, hcvvdef]
      simp only [if_neg hi, pairResidVar]
      norm_num
  -- the two drifts
  have hd₁ : ∀ j, j ≤ n → |(∑ i ∈ Finset.range j, m₁ i) - (j : ℝ)| ≤ max C₁ C₂ := by
    intro j hj
    have hcongr : (∑ i ∈ Finset.range j, m₁ i)
        = ∑ i ∈ Finset.range j, blockMean₂ X μ (blockCutoff θ (r + n)) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i < n := by
        have := Finset.mem_range.1 hi
        omega
      rw [hm₁def]
      simp only [if_pos this]
    rw [hcongr]
    exact le_trans (hdrift₁ Ω' X μ hX θ σ τ (r + n) r j s₁ s₂ hθ (by omega) hre₁ hre₂ hσtop
      hτ0 hτ1 hτeq hshift) (le_max_left _ _)
  have hd₂ : ∀ j, j ≤ n →
      |(∑ i ∈ Finset.range j, (m₂ i - pairSlope (V₁ i) (cvv i) * m₁ i)) - (j : ℝ)|
        ≤ max C₁ C₂ := by
    intro j hj
    have hcongr : (∑ i ∈ Finset.range j, (m₂ i - pairSlope (V₁ i) (cvv i) * m₁ i))
        = ∑ i ∈ Finset.range j,
            (blockMean₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (i + r))
              - pairSlope ((blockMatchedVar₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) : ℝ≥0) : ℝ)
                (blockMatchedCov X μ (blockCutoff θ (r + n)) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                  (primeBlockSub θ (i + r)))
                * blockMean₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r))) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i < n := by
        have := Finset.mem_range.1 hi
        omega
      rw [hm₁def, hm₂def, hV₁def, hcvvdef]
      simp only [if_pos this]
    rw [hcongr]
    exact le_trans (hdrift₂ Ω' X μ hX θ σ τ (r + n) r j s₁ s₂ hθ (by omega) hre₁ hre₂ hσtop
      hτ0 hτ1 hτeq hshift) (le_max_right _ _)
  -- the shear budget
  have hKb : (∑ m ∈ Finset.range n, |pairSlope (V₁ m) (cvv m)| * (M m + M (m + 1)))
      ≤ (52 + 4 * B) * C₃ := by
    have hstep : ∀ m ∈ Finset.range n,
        |pairSlope (V₁ m) (cvv m)| * (M m + M (m + 1))
          ≤ (52 + 4 * B) * (((m : ℝ) + 1) * |pairSlope
              ((blockMatchedVar₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCov X μ (blockCutoff θ (r + n)) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|) := by
      intro m hm
      have hmn : m < n := Finset.mem_range.1 hm
      have hgen : ∀ (x : ℝ) (i : ℕ), 0 ≤ x →
          x * (M i + M (i + 1)) ≤ (52 + 4 * B) * (((i : ℝ) + 1) * x) := by
        intro x i hx
        rw [hMdef]
        nlinarith only [hMlin i, hx]
      rw [hV₁def, hcvvdef]
      simp only [if_pos hmn]
      exact hgen _ m (abs_nonneg _)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hshear Ω' X μ hX θ σ τ (r + n) r n s₁ s₂ hθ (by omega)
      hre₁ hre₂ hσtop hτ0 hτ1 hτeq hshift) (by linarith)
  -- the comparison, at Proposition 7's restart
  have hP : IsProbabilityMeasure (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
      (blockCutoff θ N) s₁ s₂ μ) :=
    hX.isProbabilityMeasure_tiltedMeasure₂ (blockCutoff θ N) hsre₁ hsre₂
  have hcmp : IsBoxComparison (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
      (blockCutoff θ N) s₁ s₂ μ) Q
      (fun m => (fun m' ω => ∑ p ∈ primeBlockSub θ (m' + r),
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (m + ⌊a⌋₊))
      (fun m => Nb (m + ⌊a⌋₊)) (fun m => blockWindow (m + ⌊a⌋₊))
      (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) (1 / 2) := by
    by_cases hk : ⌊a⌋₊ ≤ n
    · have h := hcmpAll ⌊a⌋₊ hk
      rwa [show (2 : ℝ) * (1 / 4) = 1 / 2 from by norm_num] at h
    · rw [show n - ⌊a⌋₊ = 0 from by omega]
      exact isBoxComparison_zero _ _ _ _ (by norm_num)
  have hlawcap : ∀ i, i < n →
      Q.map (Nb i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (cvv i) := by
    intro i hi
    obtain ⟨e₁, ev₁, _⟩ := blockStats₂_shift_cutoff_eq hX hsre₁ hsre₂
      (by omega : i + r ≤ r + n) (by omega : r + n ≤ N)
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
    obtain ⟨e₂, ev₂, ecov⟩ := blockStats₂_shift_cutoff_eq hX hsre₁ hsre₂
      (by omega : i + r ≤ r + n) (by omega : r + n ≤ N)
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
    rw [hm₁def, hm₂def, hV₁def, hV₂def, hcvvdef]
    simp only [if_pos hi]
    rw [← e₁, ← e₂, ← ev₁, ← ev₂, ← ecov]
    exact hNblaw i (by omega)
  -- and Proposition 7
  refine proposition7_upper_of_law (nlaw := n) (m₁ := m₁) (m₂ := m₂) (V₁ := V₁) (V₂ := V₂)
    (cv := cvv) hNbm hNbi hlawcap
    (by norm_num : (0 : ℝ) < 1 / 18) hlo₁ hhi₁ (fun i => (hres₁ i).1) (fun i => (hres₁ i).2)
    (le_max_of_le_left hC₁.le) (by positivity) hB _ hP _ blockWindow M M' n (1 / 2) a hf le_rfl
    (fun m => Finset.measurable_sum _ fun p _ =>
      ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)).prodMk
        ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)))
    hd₁ hd₂ (fun m => blockWindow_pos m) (fun j _ => sum_inv_sq_range_le_two j)
    (fun j => hM0 j) (fun j hj _ => hMup j hj) (fun m _ => le_refl _) hKb (by norm_num) le_rfl
    hcmp ha hn4 hbig hbig2 hhf

/-- **Proposition 7 for the Steinhaus RMF, upper bound** (Harper): above the shift `r`, the
two-point barrier probability under the two-fold tilt is at most `Cst·\min\{1, a/√n\}²`, with
`Cst` and `Tsh` independent of the space and of every other parameter. -/
theorem exists_proposition7_upper_steinhaus :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < n →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
          4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) n
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (a / Real.sqrt n) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁, hdrift₁⟩ := exists_abs_sum_blockMean₂_shift_sub_le
  obtain ⟨C₂, hC₂, hdrift₂⟩ := exists_abs_sum_blockMean₂_regression_shift_sub_le
  obtain ⟨C₃, hC₃, hshear⟩ := exists_sum_abs_pairSlope_shift_le
  obtain ⟨K₁, hK₁, hcosblock⟩ := exists_abs_sum_cos_primeBlockSub_le
  have hmax : (0 : ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
  exact ⟨prop7UpperConst C₁ C₂ C₃, prop7Window K₁,
    prop7UpperConst_pos hC₁ hC₃, prop7Window_pos hK₁,
    le_proposition7_upper_steinhaus_of_parts hC₁ hC₃ hK₁ hdrift₁ hdrift₂ hshear hcosblock⟩

end RMF
