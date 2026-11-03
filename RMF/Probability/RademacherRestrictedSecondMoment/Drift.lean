/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTwoPoint
import RMF.Probability.RademacherFirstMoment
import RMF.Probability.RademacherBlockComparisonPair
import RMF.Probability.RestrictedSecondMoment.Drift
import RMF.Probability.RademacherChaining
import RMF.Reduction.RademacherSteps

/-!
# Key Proposition 5's two-point inputs, for the Rademacher function

The Rademacher counterpart of `RMF/Probability/RestrictedSecondMoment/Drift.lean`, following
Harper's §5.3.  It starts from the exact factorisation

`E[1_{A}·‖F_t‖²‖F_u‖²] = P~₂(A)·E[‖F_t‖²‖F_u‖²]`,  `A = L t ∩ L u`,

with `P~₂` the `‖F(s₁)‖²‖F(s₂)‖²`-tilted probability, and ends with the Rademacher form of Harper's
Proposition 7, the two-point barrier estimate (`RMF.exists_proposition7_upper_rademacher`).

* the two-fold tilt and the factorisation, whose pointwise half is law-free;
* Harper's (5.2), independence across the split, the low factor, and the exponent of his (5.1),
  `2 + 4\cos` for the Rademacher law, at Harper's pair of heights and at a general pair;
* the pair drift over a window, which carries a cosine sum at the sum frequency `t₁ + t₂` besides
  the difference frequency, and its forms with a shift condition at both frequencies;
* the block statistics, the cutoff transfer, and Proposition 7.
-/

set_option linter.style.longFile 2800

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The two-fold tilt, at the level of measures -/

/-- **Harper's display at two points**, for the Rademacher function.  `P~₂(A)` is the
`‖F(s₁)‖²‖F(s₂)‖²`-weighted measure of `A`, normalised. -/
theorem IsRademacherRMF.tiltedMeasure₂_apply (hf : IsRademacherRMF f μ) (y : ℕ) {s₁ s₂ : ℂ}
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

/-- **The normaliser is positive.**  The same argument as the Steinhaus twin, and for the same
reason it is *not* proved from a product formula: the two-fold tilt is already known to be a
probability measure, so integrating `1` against it gives `1`, and the transfer evaluates that same
integral as `E[‖F₁‖²‖F₂‖²]/E[‖F₁‖²‖F₂‖²]` — which would be `0`, not `1`, if the denominator
vanished. -/
theorem IsRademacherRMF.integral_normSq_mul_normSq_pos (hf : IsRademacherRMF f μ) (y : ℕ)
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

/-- **The identity behind the factorisation**, for the Rademacher function:
`∫_A ‖F(s₁)‖²‖F(s₂)‖² = P~₂(A)·E‖F(s₁)‖²‖F(s₂)‖²`.

This is `RMF.IsRademacherRMF.setIntegral_normSq_eq` at two points, and plays the same role: it
lets a *restricted* moment be read as a barrier probability times an *unrestricted* one, with no
loss anywhere. -/
theorem IsRademacherRMF.setIntegral_normSq_mul_normSq_eq (hf : IsRademacherRMF f μ) (y : ℕ)
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

/-- The form the height integrals consume: two indicators at two different heights, whose product
is the indicator of the intersection.  `L t ∩ L u` is the event that the walk stays in the tube at
**both** heights, whose tilted probability the Rademacher form of Harper's Proposition 7 bounds. -/
theorem IsRademacherRMF.integral_indicator_mul_indicator_normSq_eq (hf : IsRademacherRMF f μ)
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

The two halves above are joined by Fubini, and the only real work is integrability on `Ω × T`.

**It costs nothing**, because `RMF.norm_randomEulerProduct_sqfree_le` bounds the squarefree
product by the *deterministic, height-free* `RMF.eulerBound y` — the **same** constant as the
Steinhaus `RMF.norm_randomEulerProduct_le` — on the unimodularity event, for every `s` with
`Re s ≥ 1/2`.  So the integrand is a.e. bounded by a constant and `T` has finite measure, and no
moment of `‖F‖⁴` is needed to see that the swap is legal.

The swap is done **twice through one lemma**, exactly as on the Steinhaus side, so that
`RMF.integrable_uncurry_indicator_normSq_rademacher` is reused rather than reproved on
`Ω × T × T`. -/

/-- **The deterministic bound, uniform in the height.**  The null set is the unimodularity event,
which does not see `s` at all, and that is what lets the bound survive an integral over `t`. -/
lemma ae_forall_norm_randomEulerProduct_shiftLine_sqfree_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂ν, ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖
        ≤ eulerBound y := by
  filter_upwards [ae_forall_norm_le_one hY norm_le_one_rademacherLaw y] with ω hω t
  exact norm_randomEulerProduct_sqfree_le hω (by rw [re_shiftLine]; linarith)

/-- The same for the restricted weight `1_{L t}·‖F_t‖²`, which is what the height integral sees. -/
lemma ae_forall_norm_indicator_normSq_shiftLine_sqfree_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') :
    ∀ᵐ ω ∂ν, ∀ t : ℝ, ‖Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω‖ ≤ eulerBound y ^ 2 := by
  filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_sqfree_le hY y hσ] with ω hω t
  by_cases hmem : ω ∈ L t
  · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hω t) 2
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    exact sq_nonneg _

/-- **One swap.**  For any weight `ψ` bounded and measurable in `ω` alone,
`E[ψ·∫_T 1_{L t}‖F_t‖² dt] = ∫_T E[ψ·1_{L t}‖F_t‖²] dt`.  Both applications of Fubini below are
this lemma, which is what keeps the product space two-dimensional. -/
theorem integral_mul_setIntegral_indicator_normSq_sqfree_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTfin : volume T ≠ ⊤)
    (ψ : Ω' → ℝ) (hψm : AEStronglyMeasurable ψ ν) {c : ℝ} (hψb : ∀ᵐ ω ∂ν, ‖ψ ω‖ ≤ c) :
    (∫ ω, ψ ω * (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
      = ∫ t in T, ∫ ω, ψ ω * Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω ∂ν := by
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  have hbase := integrable_uncurry_indicator_normSq_rademacher hY y hσ0 L hLmeas hSmeas hTfin
  have hψprod : AEStronglyMeasurable (fun q : Ω' × ℝ => ψ q.1) (ν.prod (volume.restrict T)) :=
    hψm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hψbprod : ∀ᵐ q ∂(ν.prod (volume.restrict T)), ‖ψ q.1‖ ≤ c :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hψb
  have hInt : Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) => ψ ω * Set.indicator (L t)
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
        (shiftLine σ t) ω‖ ^ 2) ω) (ν.prod (volume.restrict T)) :=
    hbase.bdd_mul hψprod hψbprod
  rw [← integral_integral_swap hInt]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (integral_const_mul _ _).symm)

/-- **The second moment of the restricted chaos, expanded**, for the Rademacher function:
`E[X²] = ∫_T ∫_T P~₂(L t ∩ L u)·E[‖F_t‖²‖F_u‖²] du dt`,  `X = ∫_T 1_{L t}‖F_t‖² dt`.
An identity: Key Proposition 5 then bounds the barrier probability by the Rademacher form of
Proposition 7 and the two-point moment by Harper's (5.1). -/
theorem integral_sq_setIntegral_indicator_normSq_sqfree_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTfin : volume T ≠ ⊤) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      = ∫ t in T, ∫ u in T,
          (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
            * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ t) ω‖ ^ 2
                * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν := by
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hsre : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; exact hσ0
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hbase := integrable_uncurry_indicator_normSq_rademacher hY y hσ0 L hLmeas hSmeas hTfin
  have hbnd := ae_forall_norm_indicator_normSq_shiftLine_sqfree_le hY y hσ L
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
  rw [hexp, integral_mul_setIntegral_indicator_normSq_sqfree_eq hY y hσ L hLmeas hSmeas hTfin
    _ hXm hXb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  -- the second swap, at a fixed outer height, then the two-fold tilt
  have hφm : AEStronglyMeasurable (fun ω => Set.indicator (L t) (g t) ω) ν :=
    ((hf'.integrable_norm_randomEulerProduct_sq y (shiftLine σ t)).indicator
      (hLmeas t)).aestronglyMeasurable
  have hφb : ∀ᵐ ω ∂ν, ‖Set.indicator (L t) (g t) ω‖ ≤ eulerBound y ^ 2 := by
    filter_upwards [hbnd] with ω hω
    exact hω t
  calc (∫ ω, (∫ u in T, Set.indicator (L u) (g u) ω) * Set.indicator (L t) (g t) ω ∂ν)
      = ∫ ω, Set.indicator (L t) (g t) ω * (∫ u in T, Set.indicator (L u) (g u) ω) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    _ = ∫ u in T, ∫ ω, Set.indicator (L t) (g t) ω * Set.indicator (L u) (g u) ω ∂ν :=
        integral_mul_setIntegral_indicator_normSq_sqfree_eq hY y hσ L hLmeas hSmeas hTfin
          _ hφm hφb
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun u =>
        hf'.integral_indicator_mul_indicator_normSq_eq y (hsre t) (hsre u) (hLmeas t) (hLmeas u))

/-! ### Harper's (5.2), the deterministic bound

Harper's (5.2) uses only the **upper** half of his event `L(t)`, at a single index, so the bound
is *deterministic*: it holds pointwise on the event, with no probability in it.  The index
translation and the containment of this barrier in Harper's are described in the
Steinhaus twin's section docstring and are law-free; only the four statements below mention the
product, and each is its Steinhaus mirror with `RMF.localLogAdd` for `RMF.localLog`.

**The positivity input is different, and it is the one place the two laws diverge here.**  The
Steinhaus product is `∏(1 - X_p p^{-s})⁻¹`, whose factors are visibly nonzero; the Rademacher one
is the polynomial `∏(1 + X_p p^{-s})`, which *could* vanish — and does not, because
`RMF.le_norm_randomEulerProductIco_sqfree` bounds it below by `∏(1 - ‖p^{-s}‖) > 0` at `0 < Re s`.
So the two proofs reach the same conclusion from opposite directions. -/

-- The positivity input is `RMF.norm_randomEulerProductIco_sqfree_pos`, in `RademacherChaining`.

@[simp]
lemma norm_randomEulerProductIco_sqfree_self_eq_one {Ω : Type*} {Y : ℕ → Ω → ℂ} {y : ℕ} {s : ℂ}
    {ω : Ω} :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y y s ω‖ = 1 := by
  rw [randomEulerProductIco_sqfree_eq, primesIco_self, Finset.prod_empty, norm_one]

/-- **The walk is the logarithm of the partial squarefree Euler product**, in block coordinates.
`RMF.log_norm_randomEulerProductIco_sqfree_eq` for a range of primes, and
`RMF.sum_primesIco_eq_sum_blocks` splitting that range into blocks. -/
lemma log_norm_randomEulerProductIco_sqfree_eq_walk {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ) (j : ℕ)
    {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖
      = walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) j ω := by
  rw [log_norm_randomEulerProductIco_sqfree_eq hs hω, walk_apply]
  exact sum_primesIco_eq_sum_blocks θ j fun p => localLogAdd ((p : ℂ) ^ (-s)) (Y p ω)

/-- **Harper's (5.2), the deterministic bound**, for the Rademacher function.  On the barrier
event the partial Euler product over the blocks below `j` is at most `e^{v j}`.

Pointwise: no measure, no expectation, no hypothesis beyond membership. -/
theorem norm_randomEulerProductIco_sqfree_le_of_mem_barrierEvent {Ω : Type*} {Y : ℕ → Ω → ℂ}
    (θ : ℝ) {n j : ℕ} {u v : ℕ → ℝ} {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), ‖Y p ω‖ ≤ 1)
    (hmem : ω ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) n u v)
    (h1 : 1 ≤ j) (hjn : j ≤ n) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖ ≤ Real.exp (v j) := by
  have hpos := norm_randomEulerProductIco_sqfree_pos hs hω
  have hlog := log_norm_randomEulerProductIco_sqfree_eq_walk θ j hs hω
  have hle := (hmem j h1 hjn).2
  calc ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖
      = Real.exp (Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (v j) := Real.exp_le_exp.2 (by rw [hlog]; exact hle)

/-- (5.2) in the squared form the integrand carries. -/
theorem normSq_randomEulerProductIco_sqfree_le_of_mem_barrierEvent {Ω : Type*} {Y : ℕ → Ω → ℂ}
    (θ : ℝ) {n j : ℕ} {u v : ℕ → ℝ} {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1), ‖Y p ω‖ ≤ 1)
    (hmem : ω ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) n u v)
    (h1 : 1 ≤ j) (hjn : j ≤ n) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ j⌋₊ + 1) s ω‖ ^ 2 ≤ Real.exp (v j) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _)
    (norm_randomEulerProductIco_sqfree_le_of_mem_barrierEvent θ hs hω hmem h1 hjn) 2

/-! ### Independence across the split

The factorisations Harper's "using the independence of `f(p)` on distinct primes" (p. 51) stands
for.  Each is `RMF.IsIIDPrimeValues.integral_prod` over a range of primes, and each is the
Steinhaus proof with `RMF.randomEulerProductIco_sqfree_eq` in place of
`RMF.randomEulerProductIco_compMult_eq` — **an unconditional identity where the Steinhaus one
needs `0 < Re s` and unimodularity**, since the squarefree product is a polynomial and the
Steinhaus one is a product of inverses that has to be shown nonzero first.

The two-point one is in `EulerProduct/RademacherTwoPoint.lean`; the split factorisation is here. -/

-- `RMF.integral_norm_randomEulerProductIco_sq_mul_sq_sqfree`, the two-point moment over a range,
-- lives in `EulerProduct/RademacherTwoPoint.lean` beside its Steinhaus twin and the local moment
-- it is paired with; it is used below at the split.

-- `RMF.integral_norm_randomEulerProductIco_sq_sqfree`, the one-point second moment over a range,
-- is in `RademacherChaining`.

/-- **The factorisation across the split**, squarefree case:
`E[‖I_low(s₁)‖²·‖I_high(s₁)‖²‖I_high(s₂)‖²] = E[‖I_low(s₁)‖²]·E[‖I_high(s₁)‖²‖I_high(s₂)‖²]`,
so the low factor is evaluated by Mertens and the high factor by (5.1) separately.
`RMF.IsIIDPrimeValues.integral_prod` over the whole range with a summand that switches at the
cutoff, then `Finset.prod_union`. -/
theorem integral_normSq_split_factor_sqfree {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ)
    {y₀ c y : ℕ} (h₀ : y₀ ≤ c) (h₁ : c ≤ y) (s₁ s₂ : ℂ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ c s₁ ω‖ ^ 2
        * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c y s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c y s₂ ω‖ ^ 2)
        ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ c s₁ ω‖ ^ 2
            ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c y s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c y s₂ ω‖ ^ 2
            ∂μ := by
  classical
  set g : ℕ → ℂ → ℝ := fun p z =>
    ‖1 + z * (p : ℂ) ^ (-s₁)‖ ^ 2 * (if p < c then 1 else ‖1 + z * (p : ℂ) ^ (-s₂)‖ ^ 2)
    with hgdef
  have hae : ∀ ω : Ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ c s₁ ω‖ ^ 2
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c y s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) c y s₂ ω‖ ^ 2)
        = ∏ p ∈ primesIco y₀ y, g p (X p ω) := by
    intro ω
    rw [← primesIco_union h₀ h₁, Finset.prod_union (disjoint_primesIco y₀ c y),
      randomEulerProductIco_sqfree_eq, randomEulerProductIco_sqfree_eq,
      randomEulerProductIco_sqfree_eq, norm_prod, norm_prod, norm_prod,
      ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun p hp => ?_)
      (Finset.prod_congr rfl fun p hp => ?_)
    · rw [hgdef]
      simp only [if_pos (mem_primesIco.1 hp).2.2, mul_one]
    · rw [hgdef]
      simp only [if_neg (not_lt.2 (mem_primesIco.1 hp).2.1)]
  have hmeas : ∀ p ∈ primesIco y₀ y, AEStronglyMeasurable (g p) ν := by
    intro p _
    rw [hgdef]
    by_cases hc : p < c <;> simp only [hc, if_true, if_false] <;> fun_prop
  rw [integral_congr_ae (Filter.Eventually.of_forall hae),
    hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp) g hmeas,
    ← primesIco_union h₀ h₁, Finset.prod_union (disjoint_primesIco y₀ c y),
    integral_norm_randomEulerProductIco_sq_sqfree hX y₀ c s₁,
    integral_norm_randomEulerProductIco_sq_mul_sq_sqfree hX c y s₁ s₂]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun p hp => ?_)
    (Finset.prod_congr rfl fun p hp => ?_)
  · rw [hgdef]
    simp only [if_pos (mem_primesIco.1 hp).2.2, mul_one]
  · rw [hgdef]
    simp only [if_neg (not_lt.2 (mem_primesIco.1 hp).2.1)]

/-! ### The low factor, in closed form and bounded

`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq` already gives the closed form
`∏(1 + ‖p^{-s}‖²)`; below is its `rpow` shape and the bound the split consumes.

**The Rademacher low factor is dominated by the Steinhaus one, factor by factor.**
`(1+u)(1-u) = 1 - u² ≤ 1`, so `1 + u ≤ (1-u)⁻¹` for `0 ≤ u < 1` — and at `u = p^{-1-2σ}` with
`σ ≥ 0` that is exactly the Steinhaus factor.  So `RMF.prod_one_sub_rpow_inv_le` and the Mertens
step behind it are reused **unchanged**, and the constant is the same `e^{C}`: the Rademacher
Euler product is smaller, so the same bound holds a fortiori. -/

/-- The Rademacher closed form as a product of powers: `∏_{p ∈ [y₀,y₁)} (1 + p^{-2σ})`,
`σ = Re s`.  The mirror of `RMF.IsSteinhausRMF.integral_norm_randomEulerProductIco_sq'`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_sq' {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ)
    (s : ℂ) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-2 * s.re)) := by
  rw [hf.integral_norm_randomEulerProductIco_sq y₀ y₁ s]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (prime_of_mem_primesIco hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity)]
  ring_nf

/-- **Each Rademacher local factor is at most its Steinhaus counterpart.**  `1 + u ≤ (1-u)⁻¹`,
because `(1+u)(1-u) = 1 - u² ≤ 1`; the hypothesis `σ ≥ 0` is only there to keep `u ≤ 1/2`. -/
lemma one_add_rpow_le_one_sub_rpow_inv {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    (1 : ℝ) + (p : ℝ) ^ (-1 - 2 * σ) ≤ (1 - (p : ℝ) ^ (-1 - 2 * σ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hu0 : (0 : ℝ) < (p : ℝ) ^ (-1 - 2 * σ) := Real.rpow_pos_of_pos (by linarith) _
  have hle : (p : ℝ) ^ (-1 - 2 * σ) ≤ ((p : ℝ))⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : (-1 - 2 * σ) ≤ (-1 : ℝ))
    rwa [Real.rpow_neg_one] at h
  have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hu : (p : ℝ) ^ (-1 - 2 * σ) ≤ 1 / 2 := le_trans hle hhalf
  rw [inv_eq_one_div,
    le_div_iff₀ (by linarith : (0 : ℝ) < 1 - (p : ℝ) ^ (-1 - 2 * σ))]
  nlinarith [sq_nonneg ((p : ℝ) ^ (-1 - 2 * σ))]

/-- **The Rademacher low factor, dominated by Mertens' product.**  Each factor is at most its
Steinhaus counterpart, and `RMF.prod_one_sub_rpow_inv_le` finishes the range extension. -/
lemma prod_one_add_rpow_le {y₀ c : ℕ} (hy : y₀ ≤ c) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∏ p ∈ primesIco y₀ c, (1 + (p : ℝ) ^ (-1 - 2 * σ)))
      ≤ ∏ p ∈ Nat.primesBelow c, (1 - ((p : ℝ))⁻¹)⁻¹ := by
  refine le_trans (Finset.prod_le_prod (fun p _ => by positivity)
    fun p hp => one_add_rpow_le_one_sub_rpow_inv (prime_of_mem_primesIco hp) hσ) ?_
  exact prod_one_sub_rpow_inv_le hy hσ

/-- **The low factor, for the Rademacher function**: `E‖I_{[y₀,z]}(s)‖² ≤ C\log z` for
`\Re s = 1/2+σ`, `σ ≥ 0`.  Each Rademacher factor is at most its Steinhaus counterpart, so the
Mertens bound applies. -/
theorem exists_integral_norm_randomEulerProductIco_sq_le_rademacher :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (y₀ : ℕ) (z : ℝ) (s : ℂ) (σ : ℝ), 2 ≤ z → y₀ ≤ ⌊z⌋₊ + 1 → 0 ≤ σ → s.re = 1 / 2 + σ →
        (∫ ω, ‖randomEulerProductIco f y₀ (⌊z⌋₊ + 1) s ω‖ ^ 2 ∂μ) ≤ C * Real.log z := by
  obtain ⟨C₀, hC₀, hmert⟩ := exists_abs_log_prod_primesBelow_sub_log_log_le
  refine ⟨Real.exp C₀, Real.exp_pos _, fun f μ hf y₀ z s σ hz hy hσ hre => ?_⟩
  have hz0 : (0 : ℝ) < z := by linarith
  have hN2 : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hNz : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le hz0.le
  have hN2R : (2 : ℝ) ≤ ((⌊z⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN2
  rw [hf.integral_norm_randomEulerProductIco_sq' y₀ (⌊z⌋₊ + 1) s]
  have hexp : (-2 : ℝ) * s.re = -1 - 2 * σ := by rw [hre]; ring
  simp only [hexp]
  refine le_trans (prod_one_add_rpow_le hy hσ) ?_
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

/-! ### The (5.1) exponent, with a 4 on the cosine

The Rademacher exponent is `2 + 4\cos`, while `RMF.exists_sum_two_add_two_cos_rpow_le` and
`RMF.exists_sum_two_add_two_cos_rpow_split_le` state `2 + 2\cos`, so they are proved again here.
Their proof does not carry over: it discards the tilt by `(2+2\cos)p^{-1-2σ} ≤ (2+2\cos)p^{-1}`,
which needs `2 + 2\cos ≥ 0`, and bounding the cosine part of `2 + 4\cos` crudely by `4p^{-1}`
would square the high factor's `(\log M/\log N₁)²`.  So the tilted cosine sum is estimated as it
stands, by `RMF.exists_abs_cos_prime_sum_block_weight_le` (Abel summation against `u^{-2σ}`).  Its
hypothesis `|σ|\log y₂ ≤ 1` puts the split at the truncation scale `e^{1/(2σ)}` rather than at
`M`; above it the tail is an absolute constant (`RMF.exists_sum_prime_Ioc_rpow_tail_le`).  The
main term is the Steinhaus one, `2(\log\log M - \log\log N₁)`, because `1/|t| ≤ \log N₁` makes the
cosine sum `O(1)`. -/

/-- **The tilted cosine prime sum over a range above `e^{1/τ}` is `O(1)`**, while the tilt is
small: `2σ\log N₂ ≤ 1`.  Abel summation against `u^{-2σ}`: this is
`RMF.exists_abs_cos_prime_sum_block_weight_le` with its two parameters at Harper's range. -/
theorem exists_abs_cos_primesIco_weight_le :
    ∃ B > 0, ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      1 / τ ≤ Real.log (N₁ : ℝ) → 2 * σ * Real.log (N₂ : ℝ) ≤ 1 →
      |∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ)| ≤ B := by
  obtain ⟨K, hK, h⟩ := exists_abs_cos_prime_sum_block_weight_le
  refine ⟨2 * K, by positivity, fun τ σ hτ hτ1 hσ N₁ N₂ hN₁ hN12 hlog hσN => ?_⟩
  have hN₁R : (2 : ℝ) ≤ ((N₁ : ℕ) : ℝ) := by exact_mod_cast hN₁
  have hN12R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  have hN₂R : (2 : ℝ) ≤ ((N₂ : ℕ) : ℝ) := le_trans hN₁R hN12R
  have hlogN₁ : (0 : ℝ) < Real.log ((N₁ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogN₂ : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have habs : |σ| = σ := abs_of_nonneg hσ
  have hσ2 : 0 ≤ σ * Real.log ((N₂ : ℕ) : ℝ) := mul_nonneg hσ hlogN₂.le
  have hσ1 : 0 ≤ σ * Real.log ((N₁ : ℕ) : ℝ) := mul_nonneg hσ hlogN₁.le
  have hb := h τ hτ hτ1 σ ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) hN₁R hN12R (by rw [habs]; linarith)
  have hconv : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        Real.cos (τ * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊((N₁ : ℕ) : ℝ)⌋₊ ⌊((N₂ : ℕ) : ℝ)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / (p : ℝ) ^ (1 + 2 * σ) := by
    rw [Nat.floor_natCast, Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).pos
    rw [div_eq_mul_inv, ← Real.rpow_neg hp0.le]
    congr 2
    ring
  rw [hconv]
  refine le_trans hb ?_
  have hden : (1 : ℝ) ≤ τ * Real.log ((N₁ : ℕ) : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hτ).1 hlog
  have hnum : K * (1 + 2 * |σ| * Real.log (((N₂ : ℕ) : ℝ) / ((N₁ : ℕ) : ℝ))) ≤ 2 * K := by
    rw [habs, Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
    have hX : 1 + 2 * σ * (Real.log ((N₂ : ℕ) : ℝ) - Real.log ((N₁ : ℕ) : ℝ)) ≤ 2 := by
      nlinarith
    calc K * (1 + 2 * σ * (Real.log ((N₂ : ℕ) : ℝ) - Real.log ((N₁ : ℕ) : ℝ)))
        ≤ K * 2 := mul_le_mul_of_nonneg_left hX hK.le
      _ = 2 * K := by ring
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < τ * Real.log ((N₁ : ℕ) : ℝ))]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * K)
    (by linarith : (0 : ℝ) ≤ τ * Real.log ((N₁ : ℕ) : ℝ) - 1)]

/-- **The Rademacher (5.1) exponent, below the truncation scale.**
`∑ (2+4\cos(t\log p))\,p^{-1-2σ} ≤ 2(\log\log N₂ - \log\log N₁) + O(1)` once both endpoints are
past `e^{1/|t|}` and the tilt is small (`2σ\log N₂ ≤ 1`).

The main term is `2`, not `4`: the extra cosine contributes only through
`RMF.exists_abs_cos_primesIco_weight_le`, which is `O(1)` in this range. -/
theorem exists_sum_two_add_four_cos_rpow_le :
    ∃ D > 0, ∀ (t σ : ℝ), 0 < |t| → |t| ≤ 1 → 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      1 / |t| ≤ Real.log (N₁ : ℝ) → 2 * σ * Real.log (N₂ : ℝ) ≤ 1 →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 2 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨B, hB, hcos⟩ := exists_abs_cos_primesIco_weight_le
  obtain ⟨C, hC, hmert⟩ := exists_abs_sum_primesIco_inv_sub_le
  refine ⟨4 * B + 2 * C, by positivity, fun t σ ht ht1 hσ N₁ N₂ hN₁ hN12 hlog hσN => ?_⟩
  -- `cos` is even, so the signed height may be replaced by its modulus
  have habs : ∀ p : ℕ, Real.cos (t * Real.log (p : ℝ)) = Real.cos (|t| * Real.log (p : ℝ)) := by
    intro p
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  have hsplit : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
      = 2 * (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), (p : ℝ) ^ (-1 - 2 * σ))
        + 4 * ∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
            Real.cos (|t| * Real.log (p : ℝ)) * (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [habs p]; ring
  -- the main term: the tilt is discarded here, and it is legitimate because the weight is `2 ≥ 0`
  have hmain : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), (p : ℝ) ^ (-1 - 2 * σ))
      ≤ ∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), ((p : ℝ))⁻¹ := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).two_le
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (p : ℝ))
      (by linarith : (-1 - 2 * σ) ≤ (-1 : ℝ))
    rwa [Real.rpow_neg_one] at h
  have hc := hcos |t| σ ht ht1 hσ N₁ N₂ hN₁ hN12 hlog hσN
  have hm := hmert N₁ N₂ hN₁ hN12
  rw [abs_le] at hc hm
  rw [hsplit]
  linarith [hm.1, hm.2, hc.1, hc.2, hmain]

/-- **Harper's (5.1) exponent for the Rademacher law, with the tilt kept**:
`∑_{N₁<p≤N₂} (2+4\cos(t\log p))\,p^{-1-2σ} ≤ 2(\log\log M - \log\log N₁) + O(1)` whenever
`2σ\log M ≥ 1`.  The split is at `e^{1/(2σ)}`: below it `RMF.exists_sum_two_add_four_cos_rpow_le`
applies, above it the tail is an absolute constant (`RMF.exists_sum_prime_Ioc_rpow_tail_le`, with
`2 + 4\cos ≤ 6`).  The Steinhaus proof splits at `M`, since its untilted bound needs no upper
bound on `σ`. -/
theorem exists_sum_two_add_four_cos_rpow_split_le :
    ∃ D > 0, ∀ (t σ : ℝ), 0 < |t| → |t| ≤ 1 → 0 ≤ σ → ∀ N₁ M N₂ : ℕ,
      2 ≤ N₁ → N₁ ≤ M → M ≤ N₂ → 1 / |t| ≤ Real.log (N₁ : ℝ) →
      1 ≤ 2 * σ * Real.log (M : ℝ) →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨D₀, hD₀, hlow⟩ := exists_sum_two_add_four_cos_rpow_le
  obtain ⟨C, hC, htail⟩ := exists_sum_prime_Ioc_rpow_tail_le
  refine ⟨D₀ + 6 * C, by positivity, fun t σ ht ht1 hσ N₁ M N₂ hN₁ hNM hMN₂ hlog hM => ?_⟩
  have hN₁R : (2 : ℝ) ≤ ((N₁ : ℕ) : ℝ) := by exact_mod_cast hN₁
  have hNMR : ((N₁ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hNM
  have hMN₂R : ((M : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hMN₂
  have hlogN₁ : (0 : ℝ) < Real.log ((N₁ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogNM : Real.log ((N₁ : ℕ) : ℝ) ≤ Real.log ((M : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hNMR
  have hloglog : 0 ≤ 2 * (Real.log (Real.log ((M : ℕ) : ℝ))
      - Real.log (Real.log ((N₁ : ℕ) : ℝ))) := by
    have := Real.log_le_log hlogN₁ hlogNM
    linarith
  -- `2 + 4cos ≤ 6`, which is all the cosine contributes above the truncation
  have hsix : ∀ S : Finset ℕ,
      (∑ p ∈ S, (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 6 * ∑ p ∈ S, (p : ℝ) ^ (-1 - 2 * σ) := by
    intro S
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have hc := Real.cos_le_one (t * Real.log (p : ℝ))
    have hnn : (0 : ℝ) ≤ (p : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (by positivity) _
    nlinarith
  rcases le_or_gt 1 (2 * σ * Real.log ((N₁ : ℕ) : ℝ)) with hcase | hcase
  · -- the range already starts past the truncation: the whole sum is an absolute constant
    refine le_trans (hsix _) ?_
    have hconv : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), (p : ℝ) ^ (-1 - 2 * σ))
        = ∑ p ∈ Finset.Ioc ⌊((N₁ : ℕ) : ℝ)⌋₊ ⌊((N₂ : ℕ) : ℝ)⌋₊ with Nat.Prime p,
            (p : ℝ) ^ (-1 - 2 * σ) := by
      rw [Nat.floor_natCast, Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
    rw [hconv]
    have hb := htail (2 * σ) ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) (by linarith) hN₁R
      (le_trans hNMR hMN₂R) hcase
    linarith
  · have hσ0 : 0 < σ := by
      rcases hσ.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hM
        simp only [mul_zero, zero_mul] at hM
        linarith
    have h2σ : (0 : ℝ) < 2 * σ := by linarith
    -- the truncation scale
    have hA : Real.log ((N₁ : ℕ) : ℝ) < 1 / (2 * σ) := by
      rw [lt_div_iff₀ h2σ]
      linarith
    have hB : 1 / (2 * σ) ≤ Real.log ((M : ℕ) : ℝ) := by
      rw [div_le_iff₀ h2σ]
      linarith
    have hN₁y : ((N₁ : ℕ) : ℝ) < Real.exp (1 / (2 * σ)) := by
      rw [← Real.exp_log (show (0 : ℝ) < ((N₁ : ℕ) : ℝ) by linarith)]
      exact Real.exp_lt_exp.2 hA
    have hMy : Real.exp (1 / (2 * σ)) ≤ ((M : ℕ) : ℝ) := by
      rw [← Real.exp_log (show (0 : ℝ) < ((M : ℕ) : ℝ) by linarith)]
      exact Real.exp_le_exp.2 hB
    have hy2 : (2 : ℝ) ≤ Real.exp (1 / (2 * σ)) := by linarith
    have hytilt : 1 ≤ 2 * σ * Real.log (Real.exp (1 / (2 * σ))) := by
      rw [Real.log_exp, mul_one_div, div_self (ne_of_gt h2σ)]
    -- the integer split point
    have hN₁K : N₁ ≤ ⌊Real.exp (1 / (2 * σ))⌋₊ := Nat.le_floor hN₁y.le
    have hKM : ⌊Real.exp (1 / (2 * σ))⌋₊ ≤ M := Nat.floor_le_of_le hMy
    have hKR : (2 : ℝ) ≤ ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) := by
      have : (N₁ : ℝ) ≤ ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN₁K
      linarith
    have hKy : ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ Real.exp (1 / (2 * σ)) :=
      Nat.floor_le (Real.exp_pos _).le
    have hKlog : Real.log ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ 1 / (2 * σ) := by
      have h := Real.log_le_log (by linarith) hKy
      rwa [Real.log_exp] at h
    have hKtilt : 2 * σ * Real.log ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hKlog h2σ.le
      rwa [mul_one_div, div_self (ne_of_gt h2σ)] at h
    -- split the range at the truncation
    have hsum : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
        = (∑ p ∈ primesIco (N₁ + 1) (⌊Real.exp (1 / (2 * σ))⌋₊ + 1),
            (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ))
          + ∑ p ∈ primesIco (⌊Real.exp (1 / (2 * σ))⌋₊ + 1) (N₂ + 1),
              (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ) := by
      rw [← primesIco_union (by omega : N₁ + 1 ≤ ⌊Real.exp (1 / (2 * σ))⌋₊ + 1)
          (by omega : ⌊Real.exp (1 / (2 * σ))⌋₊ + 1 ≤ N₂ + 1),
        Finset.sum_union (disjoint_primesIco _ _ _)]
    rw [hsum]
    -- below the truncation
    have hbelow := hlow t σ ht ht1 hσ N₁ ⌊Real.exp (1 / (2 * σ))⌋₊ hN₁ hN₁K hlog hKtilt
    -- above it, the tail is an absolute constant
    have habove : (∑ p ∈ primesIco (⌊Real.exp (1 / (2 * σ))⌋₊ + 1) (N₂ + 1),
        (2 + 4 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)) ≤ 6 * C := by
      refine le_trans (hsix _) ?_
      have hconv : (∑ p ∈ primesIco (⌊Real.exp (1 / (2 * σ))⌋₊ + 1) (N₂ + 1),
            (p : ℝ) ^ (-1 - 2 * σ))
          = ∑ p ∈ Finset.Ioc ⌊Real.exp (1 / (2 * σ))⌋₊ ⌊((N₂ : ℕ) : ℝ)⌋₊ with Nat.Prime p,
              (p : ℝ) ^ (-1 - 2 * σ) := by
        rw [Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
      rw [hconv]
      have hb := htail (2 * σ) (Real.exp (1 / (2 * σ))) ((N₂ : ℕ) : ℝ) (by linarith) hy2
        (by linarith) hytilt
      linarith
    -- the split point is below `M`, so its `loglog` is too
    have hKlogM : Real.log ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ Real.log ((M : ℕ) : ℝ) := by
      have hle : ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hKM
      exact Real.log_le_log (by linarith) hle
    have hKlogpos : (0 : ℝ) < Real.log ((⌊Real.exp (1 / (2 * σ))⌋₊ : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    have hfin := Real.log_le_log hKlogpos hKlogM
    linarith

/-! ### The same bounds at a general pair of heights

The Steinhaus chain reduces a general pair `(s₁, s₂)` to `(1/2+σ, 1/2+σ+it)` by rotating the
primes, and the Rademacher law is not invariant under that rotation
(`RMF.exists_abs_log_integral_two_point_le_rademacher_at`).  So the exponent bound above is
restated at a general pair, and the high factor is bounded there; the (5.1) exponent then carries
**two** cosines, at the difference frequency `u = t₁-t₂` and the sum frequency `v = t₁+t₂`.

Nothing is lost.  The general-pair weight is the **average** of two reduced weights,
`½(2+4\cos uL) + ½(2+4\cos vL) = 2+2\cos uL+2\cos vL`, so each frequency is handled by the reduced
lemma separately and the two halves recombine with the *same* constant.  The reduced statements
are the case `v = u`, where the two cosines coincide: the `4` there is two cosines colliding, not
a doubling. -/

/-- **Harper's (5.1) exponent for the Rademacher law at a general pair, with the tilt kept.**
The main term stops at the truncation scale `M`, exactly as in the reduced
`RMF.exists_sum_two_add_four_cos_rpow_split_le`, and by the same averaging: the split point
`e^{1/(2σ)}` does not depend on the frequency, so one split serves both. -/
theorem exists_sum_two_add_two_cos_pair_rpow_split_le :
    ∃ D > 0, ∀ (u v σ : ℝ), 0 < |u| → |u| ≤ 1 → 0 < |v| → |v| ≤ 1 → 0 ≤ σ →
      ∀ N₁ M N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ M → M ≤ N₂ →
      1 / |u| ≤ Real.log (N₁ : ℝ) → 1 / |v| ≤ Real.log (N₁ : ℝ) →
      1 ≤ 2 * σ * Real.log (M : ℝ) →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (u * Real.log (p : ℝ)) + 2 * Real.cos (v * Real.log (p : ℝ)))
            * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨D, hD, h⟩ := exists_sum_two_add_four_cos_rpow_split_le
  refine ⟨D, hD, fun u v σ hu hu1 hv hv1 hσ N₁ M N₂ hN₁ hNM hMN₂ hlogu hlogv hM => ?_⟩
  have hU := h u σ hu hu1 hσ N₁ M N₂ hN₁ hNM hMN₂ hlogu hM
  have hV := h v σ hv hv1 hσ N₁ M N₂ hN₁ hNM hMN₂ hlogv hM
  have havg : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        (2 + 2 * Real.cos (u * Real.log (p : ℝ)) + 2 * Real.cos (v * Real.log (p : ℝ)))
          * (p : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
            (2 + 4 * Real.cos (u * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)) / 2
        + (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
            (2 + 4 * Real.cos (v * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [havg]
  linarith

/-- **The high factor at a general pair, for the Rademacher function**:
`E‖I_{(N₁,N₂]}(s₁)‖²‖I_{(N₁,N₂]}(s₂)‖² ≪ (\log M/\log N₁)²`; the sum frequency adds a second
`O(1)` cosine sum to the exponent.  A general pair cannot be reduced to `(1/2+σ, 1/2+σ+it)` by a
change of variable: the Rademacher law is not rotation invariant
(`RMF.exists_abs_log_integral_two_point_le_rademacher_at`). -/
theorem exists_integral_normSq_high_le_rademacher_at :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ : ℝ) (s₁ s₂ : ℂ) (N₁ M N₂ : ℕ), 0 ≤ σ → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        0 < |s₁.im - s₂.im| → |s₁.im - s₂.im| ≤ 1 →
        0 < |s₁.im + s₂.im| → |s₁.im + s₂.im| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |s₁.im - s₂.im| ≤ Real.log (N₁ : ℝ) → 1 / |s₁.im + s₂.im| ≤ Real.log (N₁ : ℝ) →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨C, hC, h51⟩ := exists_abs_log_integral_two_point_le_rademacher_at (Ω := Ω)
  obtain ⟨D, hD, hsum⟩ := exists_sum_two_add_two_cos_pair_rpow_split_le
  refine ⟨Real.exp (D + C), Real.exp_pos _,
    fun f μ hf σ s₁ s₂ N₁ M N₂ hσ hre₁ hre₂ hu hu1 hv hv1 hN₁ hNM hMN₂ hlogu hlogv hM => ?_⟩
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hMR : ((N₁ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hNM
  have hN₂R : ((M : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hMN₂
  have hlogM : (1 : ℝ) ≤ Real.log (M : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hMR)
  have hs₁ : (0 : ℝ) < s₁.re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < s₂.re := by rw [hre₂]; linarith
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by
        have h1 : (1 : ℝ) ≤ Real.log ((N₂ : ℕ) : ℝ) :=
          le_trans hlogM (Real.log_le_log (by linarith) hN₂R)
        linarith
      positivity
    linarith
  have h := h51 f μ hf σ ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) s₁ s₂ (by exact_mod_cast hN₁)
    (le_trans hMR hN₂R) hσ' hre₁ hre₂
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ) := by nlinarith
    calc C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C / 1 :=
          div_le_div_of_nonneg_left hC.le (by norm_num) hden
      _ = C := by ring
  have hps := hsum (s₁.im - s₂.im) (s₁.im + s₂.im) σ hu hu1 hv hv1 hσ N₁ M N₂
    (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ))) hNM hMN₂ hlogu hlogv hM
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ 2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C) := by
    linarith [h.2, hps, herr]
  have hEpos := hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂
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
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) s₂ ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (2 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := hconv

/-! ### The drift over a window, not a prefix

Harper's `R(t)` (p. 52) reads the barrier over blocks `r, r+1, …, r+j-1` rather than `0, …, j-1`,
so Proposition 7's drift hypothesis is needed over a **window**.  `RMF.barrierEvent_subset_shift`
does that for the event; this does it for the drift, and by the same move — a window sum is a
difference of two prefix sums, so the prefix bound applies twice and the constant doubles.

Nothing is lost by the differencing.  The per-block deficit is `O(\min\{e^{m-n},1\})`, geometric
and hence summable, which is what `RMF.abs_sum_blockMeanAdd_sub_le_of_offset` already encapsulates
in the additive constant `RMF.driftConstAdd`; a multiplicative form (`e^{±2}`, giving
`[e^{-2}j, e^{2}j]`) would not survive it. -/

/-- **The Rademacher block drift over a window.**  The twin of
`RMF.abs_sum_blockMean_shift_sub_le`, carried through the offset form because that is the shape
the Rademacher window comparison produces.

The hypotheses are the prefix ones at `r + j`, which is what the two applications need; they imply
the ones at `r` for free. -/
theorem abs_sum_blockMeanAdd_shift_sub_le_of_offset {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {s : ℂ}
    {θ σ Kd : ℝ} {t : ℕ → ℝ} {n r j y : ℕ}
    (hθ14 : (14 : ℝ) ≤ θ) (hj : r + j ≤ n + 1)
    (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1)
    (ht : ∀ m, m < r + j →
      |t m| * Real.log (blockScale θ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3)))
    (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < r + j →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ))) :
    |(∑ m ∈ Finset.range j, blockMeanAdd X μ y s (blockOffsetWeight θ t s)
        (primeBlockSub θ (m + r))) - (j : ℝ)|
      ≤ 2 * driftConstAdd Kd θ := by
  set F : ℕ → ℝ := fun m => blockMeanAdd X μ y s (blockOffsetWeight θ t s) (primeBlockSub θ m)
    with hFdef
  have hsplit : (∑ m ∈ Finset.range j, F (m + r))
      = (∑ m ∈ Finset.range (r + j), F m) - ∑ m ∈ Finset.range r, F m := by
    rw [Finset.sum_range_add, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun m _ => by rw [add_comm]
  have h1 := abs_sum_blockGaussMeanAddAt_sub_le_of_offset (n := n) (y := y) hX hθ14 hj hy hres hσ
    ht hKd hosc
  have h2 := abs_sum_blockGaussMeanAddAt_sub_le_of_offset (n := n) (y := y) hX hθ14
    (by omega : r ≤ n + 1) hy hres hσ (fun m hm => ht m (by omega)) hKd
    (fun m hm => hosc m (by omega))
  rw [sum_blockGaussMeanAddAt_eq X μ θ y n s _ hj] at h1
  rw [sum_blockGaussMeanAddAt_eq X μ θ y n s _ (by omega : r ≤ n + 1)] at h2
  have hcast : ((r + j : ℕ) : ℝ) = (r : ℝ) + (j : ℝ) := by push_cast; ring
  rw [hFdef] at hsplit
  rw [hsplit]
  rw [abs_le] at h1 h2 ⊢
  rw [hcast] at h1
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-! ### The bridge between the one-fold and two-fold drifts

`blockMeanAdd₂ - blockMeanAdd = ∑_{p∈B} 2(\mathrm{Re}\,p^{-s₂})(\mathrm{Re}\,w_p)
  + O(\text{errors})`: both decompositions have the summand
`2(\mathrm{Re}\,p^{-s₁})(\mathrm{Re}\,w_p) - \mathrm{Re}(w_p²)/2`, and the pair form has a second
copy of its first half at `s₂`.

The extra term is not the Steinhaus `∑\mathrm{Re}(w_p\overline{p^{-s₂}})`, which depends on the
height difference alone.  At `w_p = p^{-s₁}`,
`2\cos(t₁\log p)\cos(t₂\log p) = \cos((t₁-t₂)\log p) + \cos((t₁+t₂)\log p)`, so a cosine at the sum
frequency appears; at `t₂ = -t₁` its block sum is `≈ 1`, not small.  A window-drift bound for the
pair therefore needs control of the sum-frequency block sum as well, as the `hosc` hypothesis of
`RMF.abs_sum_blockMeanAdd_sub_le_of_offset` (at `2\Im s + t_m` and `2(\Im s + t_m)`) provides. -/

/-- **The bridge between the one-fold and two-fold Rademacher block drifts.**  The twin of
`RMF.abs_blockMean₂_sub_blockMean_sub_re_le`, with `2(\mathrm{Re}\,p^{-s₂})(\mathrm{Re}\,w_p)` in
place of `\mathrm{Re}(w_p\overline{p^{-s₂}})`. -/
theorem abs_blockMeanAdd₂_sub_blockMeanAdd_sub_re_le {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMeanAdd₂ X μ y s₁ s₂ w B - blockMeanAdd X μ y s₁ w B
        - ∑ p ∈ B, 2 * ((((p : ℕ) : ℂ) ^ (-s₂)).re * (w p).re)|
      ≤ ∑ p ∈ B, (72 * ‖w p‖ ^ 3
          + (6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w p‖
            + 2 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 * ‖w p‖)) := by
  have h₂ := abs_blockMeanAdd₂_sub_sum_le hX y hs₁ hs₂ hB hA hw
  have h₁ := abs_blockMeanAdd_sub_sum_le hX y hs₁ hB hw
  -- the two main terms differ by exactly the extra copy at `s₂`
  have hM : (∑ p ∈ B, (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re) * (w p).re
        - ((w p) ^ 2).re / 2))
      - (∑ p ∈ B, (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re) * (w p).re - ((w p) ^ 2).re / 2))
      = ∑ p ∈ B, 2 * ((((p : ℕ) : ℂ) ^ (-s₂)).re * (w p).re) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hsplit : blockMeanAdd₂ X μ y s₁ s₂ w B - blockMeanAdd X μ y s₁ w B
      - ∑ p ∈ B, 2 * ((((p : ℕ) : ℂ) ^ (-s₂)).re * (w p).re)
      = (blockMeanAdd₂ X μ y s₁ s₂ w B
          - ∑ p ∈ B, (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re) * (w p).re
              - ((w p) ^ 2).re / 2))
        - (blockMeanAdd X μ y s₁ w B
            - ∑ p ∈ B, (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re) * (w p).re - ((w p) ^ 2).re / 2)) := by
    rw [← hM]
    ring
  -- and the two error bounds simply add
  have hE : (∑ p ∈ B, (72 * ‖w p‖ ^ 3
        + (6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w p‖
          + 2 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 * ‖w p‖)))
      = (∑ p ∈ B, (36 * ‖w p‖ ^ 3
            + 6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w p‖))
        + ∑ p ∈ B, (36 * ‖w p‖ ^ 3 + 2 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 * ‖w p‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit, hE, abs_le]
  obtain ⟨a₂, b₂⟩ := abs_le.1 h₂
  obtain ⟨a₁, b₁⟩ := abs_le.1 h₁
  constructor <;> linarith

/-! ### The pair drift at Harper's weights

The bridge above is at an arbitrary weight; here it is at Harper's own, `w_p = p^{-s₁}`, where all
three moduli coincide and the main term becomes a pair of cosine sums.

**Two of them, where the Steinhaus twin has one.**  `RMF.abs_blockMean₂_sub_blockMean_sub_cos_le`
produces only `\cos((t₁-t₂)\log p)`; the identity `2\cos A\cos B = \cos(A-B) + \cos(A+B)` puts a
**sum-frequency** cosine beside it, and that one does not vanish — at `t₂ = -t₁` it is the constant
`1` and its block sum is `≈1`, not small.  Anything downstream must therefore control both, which
is precisely what the `hosc` hypothesis of `RMF.abs_sum_blockMeanAdd_sub_le_of_offset` already
does.

The error collapses as it does on the Steinhaus side: every monomial is a power of the single
number `a_p = ‖p^{-s₁}‖`, so the whole thing is `73κ_m∑a_p²`, and
`RMF.sum_norm_sq_primeBlockSub_le` caps `∑a_p²` at `8`. -/

/-- **The bridge at Harper's weights**: the two-fold Rademacher drift is the one-fold drift plus
the difference-frequency *and* sum-frequency cosine sums, up to `O(κ_m)`. -/
theorem abs_blockMeanAdd₂_sub_blockMeanAdd_sub_cos_le {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {m n : ℕ}
    {s₁ s₂ : ℂ} (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    |blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)
        - blockMeanAdd X μ (blockCutoff θ n) s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)
        - ∑ p ∈ primeBlockSub θ m,
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 600 * blockWeightSize θ m := by
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
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2 := by
    intro p hp
    rw [hnorm₂ p hp]
    have hid : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖w p‖ := rfl
    rw [hid]
    linarith [hwκ p hp]
  have hmain := abs_blockMeanAdd₂_sub_blockMeanAdd_sub_re_le hX (blockCutoff θ n) hs₁ hs₂ hB hA hw5
  -- the main term is the two cosine sums
  have hcos : ∑ p ∈ primeBlockSub θ m, 2 * ((((p : ℕ) : ℂ) ^ (-s₂)).re * (w p).re)
      = ∑ p ∈ primeBlockSub θ m,
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hmul : ((p : ℕ) : ℝ) ^ (-(1 / 2 + σ)) * ((p : ℕ) : ℝ) ^ (-(1 / 2 + σ))
        = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    rw [hwdef, re_natCast_cpow_neg p.2.pos s₂, re_natCast_cpow_neg p.2.pos s₁, hre₁, hre₂,
      show (s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)
          = s₁.im * Real.log ((p : ℕ) : ℝ) - s₂.im * Real.log ((p : ℕ) : ℝ) by ring,
      show (s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)
          = s₁.im * Real.log ((p : ℕ) : ℝ) + s₂.im * Real.log ((p : ℕ) : ℝ) by ring,
      Real.cos_sub, Real.cos_add, ← hmul]
    ring
  rw [hcos] at hmain
  refine hmain.trans ?_
  -- the error, against `73 κ ∑‖w_p‖²`
  set S := ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun p _ => sq_nonneg _
  have herr : ∑ p ∈ primeBlockSub θ m, (72 * ‖w p‖ ^ 3
        + (6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w p‖
          + 2 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 * ‖w p‖))
      ≤ 73 * κ * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hn₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖w p‖ := rfl
    rw [hn₁, hnorm₂ p hp]
    have hn0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hk := hwκ p hp
    have hcube : ‖w p‖ * ‖w p‖ ^ 2 ≤ κ * ‖w p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    have hsq : ‖w p‖ ^ 2 ≤ κ ^ 2 := by nlinarith [hn0, hk]
    have hquart : ‖w p‖ ^ 2 * ‖w p‖ ^ 2 ≤ κ ^ 2 * ‖w p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hκsmall : 50 * κ ^ 2 ≤ κ := by nlinarith [hκ0, hκm]
    nlinarith [hcube, hquart, hκsmall, sq_nonneg (‖w p‖)]
  have hSb : S ≤ 8 := sum_norm_sq_primeBlockSub_le hmθ hre₁ hσ
  nlinarith [herr, hSb, hκ0, hS0]

/-! ### The pair drift over a window, with the sum frequency left in view

The Steinhaus `RMF.exists_abs_sum_blockMean₂_shift_sub_le` concludes `|drift - j| ≤ C` from
the shift condition `1 ≤ τe^{r+θ}` on the height difference.  The Rademacher bridge adds a cosine
sum at the sum frequency `t₁ + t₂`, which that condition does not control: at `t₂ = -t₁` it is
`≈ 1` per block, the pair drift is `≈ 2` per block, and `|drift - j|` grows linearly in `j`.  So
the statement below keeps both cosine sums in its conclusion;
`RMF.exists_abs_sum_sum_cos_pair_shift_le` bounds them under a shift condition at each frequency,
which Harper's heights `[1/3, 1/2]` satisfy.  `hosc` asks only that the block sum at the doubled
height of `s₁` be `O(e^{-m})`, as in `RMF.abs_sum_blockMeanAdd_sub_le_of_offset`;
`RMF.exists_abs_sum_cos_primeBlockSub_harper_le` supplies it on Harper's heights. -/

/-- **The first drift input of Proposition 7, for the Rademacher pair**, with the two cosine sums
left explicit.  The twin of `RMF.exists_abs_sum_blockMean₂_shift_sub_le`, which can absorb its
single cosine sum into the constant. -/
theorem abs_sum_blockMeanAdd₂_shift_sub_sum_cos_le {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {θ σ Kd : ℝ} {n r j : ℕ} {s₁ s₂ : ℂ}
    (hθ : (14 : ℝ) ≤ θ) (hj : r + j ≤ n + 1)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1) (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < r + j →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) :
    |(∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))
        - (j : ℝ)
        - ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 2 * driftConstAdd Kd θ
        + 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  -- the one-fold window drift, at zero offsets
  have hone := abs_sum_blockMeanAdd_shift_sub_le_of_offset (X := X) (μ := μ) (s := s₁) (θ := θ)
    (σ := σ) (Kd := Kd) (t := fun _ => 0) (n := n) (r := r) (j := j) (y := blockCutoff θ n)
    hX hθ hj le_rfl hre₁ hσ
    (fun m _ => by
      simp only [abs_zero, zero_mul]
      positivity)
    hKd
    (fun m hm => by
      have h := hosc m hm
      simp only [add_zero] at *
      linarith [abs_nonneg (∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))])
  rw [blockOffsetWeight_zero] at hone
  -- the bridge, block by block
  have hbridge : ∀ m ∈ Finset.range j,
      |blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))
          - blockMeanAdd X μ (blockCutoff θ n) s₁
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))
          - ∑ p ∈ primeBlockSub θ (m + r),
              (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                  + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
                * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ 600 * blockWeightSize θ (m + r) := by
    intro m hm
    have hmj : m < j := Finset.mem_range.1 hm
    have hmn : m + r ≤ n := by omega
    refine abs_blockMeanAdd₂_sub_blockMeanAdd_sub_cos_le (m := m + r) (n := n) hX ?_ hmn hre₁ hre₂
      (hσm (m + r) hmn)
    have hmr : (0 : ℝ) ≤ ((m + r : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hsum := (Finset.abs_sum_le_sum_abs (fun m =>
      blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))
        - blockMeanAdd X μ (blockCutoff θ n) s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))
        - ∑ p ∈ primeBlockSub θ (m + r),
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) (Finset.range j)).trans
    (Finset.sum_le_sum hbridge)
  have hκ : (∑ m ∈ Finset.range j, 600 * blockWeightSize θ (m + r))
      ≤ 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_blockWeightSize_shift_le θ r j) (by norm_num)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  have hid : (∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))
        - (j : ℝ)
        - ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
      = ((∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))
            - (∑ m ∈ Finset.range j, blockMeanAdd X μ (blockCutoff θ n) s₁
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))
            - ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
                (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                    + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
                  * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        + ((∑ m ∈ Finset.range j, blockMeanAdd X μ (blockCutoff θ n) s₁
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))) - (j : ℝ)) := by
    ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  linarith [hsum, hκ, hone]

/-! ### The block weights

The integrability statements transported to `RMF.tiltedMeasure₂`, such as
`RMF.integrable_localLogAdd_tiltedMeasure₂` and `RMF.integrable_localLogAdd_sq_tiltedMeasure₂`,
ask every block weight to be at most `1/5`. -/

/-- Every block weight in the window is at most `1/5`, which is the hypothesis every transported
integrability statement carries. -/
lemma norm_prime_cpow_neg_le_fifth_of_mem_primeBlockSub {θ σ : ℝ} {m : ℕ} {s : ℂ}
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ) (hre : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := by
  have hκ : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ blockWeightSize θ m :=
    norm_le_of_mem_primeBlockSub hσ hp (norm_sq_prime_cpow_neg p hre)
  linarith [blockWeightSize_le hmθ]

/-! ### The second coordinate's drift

Proposition 7 asks for the drift at *both* weights.  The two-fold tilt is symmetric in its heights
— `RMF.tiltedMeasure₂_comm`, which is law-free and reused verbatim — so the second is the first at
the swapped pair, with the same constant.

The two cosine sums are symmetric too, but not syntactically: `\cos` is even, which handles the
difference frequency, and the sum frequency is symmetric outright.  Stating both forms against the
*same* expression is what lets the two drifts be combined later. -/

/-- **The block mean is symmetric in the two heights**, the weight held fixed.  The twin of
`RMF.blockMean₂_comm`. -/
lemma blockMeanAdd₂_comm {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ)
    (s₁ s₂ : ℂ) (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) :
    blockMeanAdd₂ X μ y s₁ s₂ w B = blockMeanAdd₂ X μ y s₂ s₁ w B := by
  rw [blockMeanAdd₂, blockMeanAdd₂,
    tiltedMeasure₂_comm (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ]

/-- **The pair drift over a window, at the second coordinate's weight.**  The same statement and
the same constant as `RMF.abs_sum_blockMeanAdd₂_shift_sub_sum_cos_le`, at the swapped pair; the
`hosc` hypothesis moves to the doubled height of `s₂`. -/
theorem abs_sum_blockMeanAdd₂_snd_shift_sub_sum_cos_le {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {θ σ Kd : ℝ} {n r j : ℕ} {s₁ s₂ : ℂ}
    (hθ : (14 : ℝ) ≤ θ) (hj : r + j ≤ n + 1)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1) (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < r + j →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) :
    |(∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r)))
        - (j : ℝ)
        - ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 2 * driftConstAdd Kd θ
        + 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
  have hcomm : ∀ m : ℕ, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
      = blockMeanAdd₂ X μ (blockCutoff θ n) s₂ s₁
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r)) :=
    fun m => blockMeanAdd₂_comm X μ (blockCutoff θ n) s₁ s₂ _ _
  simp only [hcomm]
  have h := abs_sum_blockMeanAdd₂_shift_sub_sum_cos_le (s₁ := s₂) (s₂ := s₁) hX hθ hj hre₂ hre₁
    hσ hKd hosc
  have hcos : ∀ m : ℕ, (∑ p ∈ primeBlockSub θ (m + r),
        (Real.cos ((s₂.im - s₁.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₂.im + s₁.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = ∑ p ∈ primeBlockSub θ (m + r),
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    intro m
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show s₂.im - s₁.im = -(s₁.im - s₂.im) by ring, neg_mul, Real.cos_neg,
      show s₂.im + s₁.im = s₁.im + s₂.im by ring]
  simp only [hcos] at h
  exact h

/-! ### The block statistics above the shift

Beyond the drift, Proposition 7 needs the variance bracket and the covariance of the pair.

**The variance needs no transfer.**  The two-fold variance bracket is stated at an arbitrary
cutoff `y` with `primeBlockSub θ m ⊆ primesBelowSub y` as its hypothesis, so the Steinhaus step
through `RMF.blockStats₂_blockCutoff_eq` has no counterpart: `m ≤ n` gives the subset.  The
Rademacher bracket carries a height condition the Steinhaus one does not, `Tsh ≤ 2u.im e^{m+θ}`
and `(2u.im)² ≤ e^{m+θ}`, threaded rather than discharged.

**The covariance carries both frequencies**, exactly as the drift does, and for the same reason:
`\mathrm{Re}(p^{-s₁})\mathrm{Re}(p^{-s₂}) = \tfrac12[\cos((t₁-t₂)\log p) + \cos((t₁+t₂)\log p)]
p^{-1-2σ}`.  On the anti-diagonal the second term is the whole block sum, so the covariance there
is the full variance: at the level of second moments, the two walks are the same walk. -/

/-- **The block covariance, against the two cosine sums and the weight size.**  The twin of
`RMF.abs_blockMatchedCov_prime_le`, with the sum frequency alongside the difference frequency. -/
theorem abs_blockMatchedCovAdd_prime_le {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    |blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)|
      ≤ |∑ p ∈ primeBlockSub θ m,
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        + 100 * blockWeightSize θ m := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  have hB := primeBlockSub_subset_primesBelowSub θ hmn
  set κ := blockWeightSize θ m with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ m
  have hκm : κ ≤ 1 / 1000000 := blockWeightSize_le_millionth hm4
  have hwn : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre₁
  have hnorm₂ : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₂)‖ = ‖((p : ℕ) : ℂ) ^ (-s₁)‖ := by
    intro p hp
    have h : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 = ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := by
      rw [norm_sq_prime_cpow_neg p hre₂, hwn p hp]
    calc ‖((p : ℕ) : ℂ) ^ (-s₂)‖ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2) := by rw [h]
      _ = ‖((p : ℕ) : ℂ) ^ (-s₁)‖ := Real.sqrt_sq (norm_nonneg _)
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by
    intro p hp
    linarith [hwκ p hp]
  have hw5₂ : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    rw [hnorm₂ p hp]
    exact hw5 p hp
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2 := by
    intro p hp
    rw [hnorm₂ p hp]
    linarith [hwκ p hp]
  have hcov := abs_blockMatchedCovAdd_sub_le hX (blockCutoff θ n) hs₁ hs₂ hB hA hw5 hw5₂
  -- the main term is half the sum of the two cosine sums
  have hmainform : (∑ p ∈ primeBlockSub θ m,
        (((p : ℕ) : ℂ) ^ (-s₁)).re * (((p : ℕ) : ℂ) ^ (-s₂)).re)
      = (∑ p ∈ primeBlockSub θ m,
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hmul : ((p : ℕ) : ℝ) ^ (-(1 / 2 + σ)) * ((p : ℕ) : ℝ) ^ (-(1 / 2 + σ))
        = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    rw [re_natCast_cpow_neg p.2.pos s₁, re_natCast_cpow_neg p.2.pos s₂, hre₁, hre₂,
      show (s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)
          = s₁.im * Real.log ((p : ℕ) : ℝ) - s₂.im * Real.log ((p : ℕ) : ℝ) by ring,
      show (s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)
          = s₁.im * Real.log ((p : ℕ) : ℝ) + s₂.im * Real.log ((p : ℕ) : ℝ) by ring,
      Real.cos_sub, Real.cos_add, ← hmul]
    ring
  rw [hmainform] at hcov
  -- the error, against `9κ ∑a_p² ≤ 72κ`
  have herr : (∑ p ∈ primeBlockSub θ m,
        (4 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 3)
          + 36 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2
              * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ * ‖((p : ℕ) : ℂ) ^ (-s₂)‖)))
      ≤ 9 * κ * ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [hnorm₂ p hp]
    have hn0 : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ := norm_nonneg _
    have hk := hwκ p hp
    have hcube : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2
        ≤ κ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    have hsq : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 ≤ κ ^ 2 := by nlinarith
    have hquart : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2
        ≤ κ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hκsmall : 144 * κ ^ 2 ≤ κ := by nlinarith
    nlinarith [hcube, hquart, hκsmall, sq_nonneg ‖((p : ℕ) : ℂ) ^ (-s₁)‖]
  have hS := sum_norm_sq_primeBlockSub_le hmθ hre₁ hσ
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have h72 : 9 * κ * ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 ≤ 72 * κ := by
    nlinarith [hS, hκ0, hS0]
  have h1 := abs_add_le (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m)
      - (∑ p ∈ primeBlockSub θ m,
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) / 2)
    ((∑ p ∈ primeBlockSub θ m,
        (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) / 2)
  rw [sub_add_cancel] at h1
  have h2 : |(∑ p ∈ primeBlockSub θ m,
        (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) / 2|
      = |∑ p ∈ primeBlockSub θ m,
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2 := by
    rw [abs_div]
    norm_num
  rw [h2] at h1
  linarith [hcov, herr, h72, h1]

/-- **The regression slope of one block**, against the two cosine sums and the weight size.  The
twin of `RMF.abs_pairSlope_block_le`.  The variance lower bound is a hypothesis, where the
Steinhaus twin derives it: the Rademacher variance bracket is existential in a height threshold,
so a derived form would carry `Tsh` and two height conditions into every use;
`RMF.box_comparison_blockAdd_of_family` makes the same choice. -/
theorem abs_pairSlopeAdd_block_le {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hV : 1 / 16 ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)) :
    |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m))|
      ≤ 8 * |∑ p ∈ primeBlockSub θ m,
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + 1600 * blockWeightSize θ m := by
  have hVpos : (0 : ℝ) < ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  have hcovb := abs_blockMatchedCovAdd_prime_le hX hmθ hmn hre₁ hre₂ hσ
  have hslope : |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
      (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m))|
      ≤ 16 * |blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| := by
    rw [pairSlope, abs_div, abs_of_pos hVpos, div_le_iff₀ hVpos]
    nlinarith [abs_nonneg (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
      (primeBlockSub θ m)), hV]
  linarith [hslope, hcovb, abs_nonneg (∑ p ∈ primeBlockSub θ m,
    (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
        + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
      * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))]

/-! ### The shear bound, with the sum frequency left in view

Proposition 7 asks for `∑|r_m|(M_m + M_{m+1}) ≤ K`, the envelope being linear in the block index.
Above the shift the difference-frequency cosine sums are `O(1/(τe^{r+θ}))` even against that
weight — `RMF.exists_abs_sum_cos_primeBlockSub_shift_weighted_le` — and the block weights are
geometric, so both are absorbed.

**The sum frequency is not, and this is where the anti-diagonal fails Proposition 7 outright.**
There the two walks are the same walk, so every regression slope is `≈1` and the weighted sum is
`≈j²/2`, not `O(1)`.  So the bound is stated with the sum-frequency term explicit: a caller off
the anti-diagonal bounds it by the same weighted estimate at frequency `|t₁+t₂|`, and a caller on
it sees that it cannot.

The per-block variance bound is a hypothesis, as in `RMF.abs_pairSlopeAdd_block_le`. -/

/-- **The shear bound for the Rademacher pair**, with the sum-frequency term explicit.  The twin
of `RMF.exists_sum_abs_pairSlope_shift_le`. -/
theorem exists_sum_abs_pairSlopeAdd_shift_sub_sum_cos_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsRademacherPrimeValues X μ → ∀ (θ σ τ : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < j → 1 / 16 ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)) →
        (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
            |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|)
          ≤ 8 * (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
              |∑ p ∈ primeBlockSub θ (m + r),
                Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
                  * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|) + C := by
  obtain ⟨K, hK, hcos⟩ := exists_abs_sum_cos_primeBlockSub_shift_weighted_le
  have he1 : Real.exp (-(1 / 4 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hden : (0 : ℝ) < 1 - Real.exp (-(1 / 4 : ℝ)) := by linarith
  have hinv0 : (0 : ℝ) < (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := inv_pos.2 hden
  refine ⟨8 * K + 1600 * (4 * Real.exp 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹), ?_, ?_⟩
  · nlinarith [hK, Real.exp_pos (1 : ℝ), hinv0]
  intro Ω' _ X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift hV
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  -- the two cosine families, the difference one in the shape the weighted estimate wants
  have hsplit : ∀ k : ℕ, (∑ p ∈ primeBlockSub θ k,
        (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primeBlockSub θ k,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
        + ∑ p ∈ primeBlockSub θ k,
            Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    intro k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hinv1 : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) = 1 / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
      rw [one_div, ← Real.rpow_neg hp0.le]
      congr 1
      ring
    have hcosDiff : Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) := by
      rcases (abs_eq hτ0.le).1 hτeq with h | h
      · rw [h]
      · rw [h, show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    rw [hcosDiff, hinv1]
    ring
  -- per block
  have hstep : ∀ m ∈ Finset.range j, ((m : ℝ) + 1) *
      |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
        (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ (m + r)))|
      ≤ 8 * (((m : ℝ) + 1) * |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)|)
        + 8 * (((m : ℝ) + 1) * |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|)
        + 1600 * (((m : ℝ) + 1) * blockWeightSize θ (m + r)) := by
    intro m hm
    have hm' : m < j := Finset.mem_range.1 hm
    have hmr : m + r ≤ n := by omega
    have hb := abs_pairSlopeAdd_block_le hX
      (show (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ by
        push_cast
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith)
      hmr hre₁ hre₂ (hσm (m + r) hmr) (hV m hm')
    rw [hsplit (m + r)] at hb
    have htri := abs_add_le (∑ p ∈ primeBlockSub θ (m + r),
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
      (∑ p ∈ primeBlockSub θ (m + r),
        Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith [hb, htri, hm1, (blockWeightSize_pos θ (m + r)).le,
      abs_nonneg (∑ p ∈ primeBlockSub θ (m + r),
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)),
      abs_nonneg (∑ p ∈ primeBlockSub θ (m + r),
        Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  -- the difference frequency and the block weights, both geometric
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
    calc 4 * Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
            * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹
        ≤ 4 * Real.exp 1 * 1 * 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by gcongr
      _ = 4 * Real.exp 1 * (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by ring
  linarith [hcb, hkb]

/-- **The two-fold Rademacher block drift is at most `40`**, at every block Harper uses:
`RMF.abs_blockMeanAdd₂_le` with `e² ≤ 7.39` and `60/\log x_m ≤ 1/100`, so `5·7.39·1.01 ≤ 37.4`.
The Steinhaus twin `RMF.abs_blockMean₂_le_fifteen` gets `15`, by the doubling that separates
`2 + 4\cos` from `2 + 2\cos`; the bound only enters as a crude factor against `∑|ρ_m|`. -/
lemma abs_blockMeanAdd₂_le_forty {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ}
    {w : Nat.Primes → ℂ} (hmθ : (8 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    |blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ m)| ≤ 40 := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  refine (abs_blockMeanAdd₂_le hX hm3 hmn le_rfl hre₁ hre₂ (by norm_num) le_rfl hσ hwn).trans ?_
  have hL := log_blockScale_ge hmθ
  have hdiv : (60 : ℝ) / Real.log (blockScale θ (m + 1)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hdiv0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by
    have hLpos : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
    positivity
  have he2 : Real.exp (2 * 1) ≤ 7.39 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp (2 * 1) = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [h2]
    nlinarith [h1, h0]
  have hprod : Real.exp (2 * 1) * (1 + 60 / Real.log (blockScale θ (m + 1)))
      ≤ 7.39 * (1 + 1 / 100) :=
    mul_le_mul he2 (by linarith) (by linarith) (by norm_num)
  linarith [hprod]

/-- **The second drift input of Proposition 7, for the Rademacher pair**, with the cosine terms
explicit.  The realisation forces `θ₂ = m₂ - ρm₁`, so the shear carries the first coordinate's
drift into the second: `RMF.abs_sum_blockMeanAdd₂_snd_shift_sub_sum_cos_le` bounds `∑m₂`, and
`RMF.exists_sum_abs_pairSlopeAdd_shift_sub_sum_cos_le` bounds `∑|ρ_m|` against the crude
`RMF.abs_blockMeanAdd₂_le_forty` for `m₁`.  The second sum-frequency term is weighted by the
block index. -/
theorem exists_abs_sum_blockMeanAdd₂_regression_shift_sub_sum_cos_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsRademacherPrimeValues X μ → ∀ (θ σ τ Kd : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 → 0 ≤ Kd →
        (∀ m, m < r + j →
          |∑ p ∈ primeBlockSub θ m,
              Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
            ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < j → 1 / 16 ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)) →
        |(∑ m ∈ Finset.range j,
            (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
              - pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
                (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                  (primeBlockSub θ (m + r)))
                * blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))) - (j : ℝ)|
          ≤ |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
                (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                    + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
                  * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
            + 320 * (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
                |∑ p ∈ primeBlockSub θ (m + r),
                  Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
                    * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|)
            + (2 * driftConstAdd Kd θ
                + 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
                    * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
                + 40 * C) := by
  obtain ⟨C₂, hC₂, hslope⟩ := exists_sum_abs_pairSlopeAdd_shift_sub_sum_cos_le
  refine ⟨C₂, hC₂, ?_⟩
  intro Ω' _ X μ hX θ σ τ Kd n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hKd hosc hτ0 hτ1 hτeq hshift hV
  have hθ14 : (14 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  have hid : (∑ m ∈ Finset.range j,
        (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
          - pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
            (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
              (primeBlockSub θ (m + r)))
            * blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))) - (j : ℝ)
      = ((∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))) - (j : ℝ))
        - ∑ m ∈ Finset.range j,
            pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))
              * blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  refine le_trans (abs_sub _ _) ?_
  have hA : |(∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))) - (j : ℝ)|
      ≤ |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + (2 * driftConstAdd Kd θ
            + 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
                * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)) := by
    -- the second coordinate's drift, with its cosine term put back
    have h := abs_sum_blockMeanAdd₂_snd_shift_sub_sum_cos_le hX hθ14 hj hre₁ hre₂ hσ hKd hosc
    have htri := abs_add_le ((∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))) - (j : ℝ)
        - ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
            (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
                + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    rw [sub_add_cancel] at htri
    have hpos : (0 : ℝ) ≤ 320 * (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
        |∑ p ∈ primeBlockSub θ (m + r),
          Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|) := by
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun m _ => ?_)
      positivity
    have hC₂0 : (0 : ℝ) ≤ 40 * C₂ := by linarith
    linarith [h, htri]
  have hB : |∑ m ∈ Finset.range j,
        pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
          (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ (m + r)))
          * blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))|
      ≤ 320 * (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
          |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|) + 40 * C₂ := by
    -- the shear term
    have hbound : ∀ m ∈ Finset.range j,
        |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
            (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
              (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
              (primeBlockSub θ (m + r)))
          * blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))|
        ≤ 40 * (((m : ℝ) + 1) *
            |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|) := by
      intro m hm
      have hm' : m < j := Finset.mem_range.1 hm
      have hmr : m + r ≤ n := by omega
      have hm8 : (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ := by
        push_cast
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith
      have hM₁b := abs_blockMeanAdd₂_le_forty hX hm8 hmr hre₁ hre₂ (hσm (m + r) hmr)
        (fun p _ => norm_sq_prime_cpow_neg p hre₁)
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      rw [abs_mul]
      nlinarith [abs_nonneg (pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
          (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ (m + r)))),
        abs_nonneg (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))), hM₁b, hm1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hbound).trans ?_
    rw [← Finset.mul_sum]
    have hsl := hslope Ω' X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hshift hV
    linarith [hsl]
  linarith [hA, hB]

/-! ### Discharging the sum frequency, on Harper's range

Every pair estimate above leaves its two cosine sums in view.  Harper restricts the Rademacher
heights to `[1/3, 1/2]` (§5.3), so that the two heights have `2/3 ≤ 2t₁, 2t₂, t₁+t₂ ≤ 1`: the sum
frequency is bounded below as the difference frequency is.  The wrappers below impose the shift
condition at each frequency, which makes both sums `O(1/(\cdot\,e^{r+θ}))` and folds the explicit
terms into the constant.  The condition `1 ≤ νe^{r+θ}` at `ν = |t₁+t₂|` holds with room on
Harper's range and fails on the anti-diagonal. -/

/-- **Both cosine sums at once**, under a shift condition at each frequency. -/
lemma exists_abs_sum_sum_cos_pair_shift_le :
    ∃ K > 0, ∀ (θ σ τ ν : ℝ) (r j : ℕ) (s₁ s₂ : ℂ), 0 ≤ θ →
      (∀ m, m < j → |σ| * Real.log (blockScale θ (m + r + 1)) ≤ 1) →
      0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
      0 < ν → ν ≤ 1 → |s₁.im + s₂.im| = ν → 1 ≤ ν * Real.exp ((r : ℝ) + θ) →
      |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| ≤ K := by
  obtain ⟨K₁, hK₁, hcos⟩ := exists_abs_sum_cos_primeBlockSub_shift_le
  refine ⟨2 * K₁, by positivity, ?_⟩
  intro θ σ τ ν r j s₁ s₂ hθ0 hσm hτ0 hτ1 hτeq hτsh hν0 hν1 hνeq hνsh
  have hsplit : (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
        (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
        + ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
            Real.cos (ν * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hinv1 : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) = 1 / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
      rw [one_div, ← Real.rpow_neg hp0.le]
      congr 1
      ring
    have hcd : Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) := by
      rcases (abs_eq hτ0.le).1 hτeq with h | h
      · rw [h]
      · rw [h, show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    have hcs : Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
        = Real.cos (ν * Real.log ((p : ℕ) : ℝ)) := by
      rcases (abs_eq hν0.le).1 hνeq with h | h
      · rw [h]
      · rw [h, show -ν * Real.log ((p : ℕ) : ℝ) = -(ν * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    rw [hcd, hcs, hinv1]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have b1 : |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)| ≤ K₁ := by
    refine (hcos τ σ θ r j hτ0 hτ1 hθ0 hσm).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hK₁, hτsh]
  have b2 : |∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
      Real.cos (ν * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)| ≤ K₁ := by
    refine (hcos ν σ θ r j hν0 hν1 hθ0 hσm).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hK₁, hνsh]
  linarith

/-- **The pair drift over a window, with a shift condition at both frequencies**: the twin of
`RMF.exists_abs_sum_blockMean₂_shift_sub_le`, the cosine sums absorbed into the constant. -/
theorem exists_abs_sum_blockMeanAdd₂_shift_sub_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsRademacherPrimeValues X μ → ∀ (θ σ τ ν Kd : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 → 0 ≤ Kd →
        (∀ m, m < r + j →
          |∑ p ∈ primeBlockSub θ m,
              Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
            ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        0 < ν → ν ≤ 1 → |s₁.im + s₂.im| = ν → 1 ≤ ν * Real.exp ((r : ℝ) + θ) →
        |(∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))) - (j : ℝ)|
          ≤ 2 * driftConstAdd Kd θ + C := by
  obtain ⟨K, hK, hpair⟩ := exists_abs_sum_sum_cos_pair_shift_le
  have he1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hinv : (0 : ℝ) < (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := inv_pos.2 (by linarith)
  refine ⟨K + 600 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹), ?_, ?_⟩
  · nlinarith [hK, Real.exp_pos (1 : ℝ), hinv]
  intro Ω' _ X μ hX θ σ τ ν Kd n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hKd hosc hτ0 hτ1 hτeq hτsh
    hν0 hν1 hνeq hνsh
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hθ14 : (14 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  have h := abs_sum_blockMeanAdd₂_shift_sub_sum_cos_le hX hθ14 hj hre₁ hre₂ hσ hKd hosc
  have hc := hpair θ σ τ ν r j s₁ s₂ hθ0
    (fun m hm => hσm (m + r) (by omega)) hτ0 hτ1 hτeq hτsh hν0 hν1 hνeq hνsh
  have htri := abs_add_le ((∑ m ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r))) - (j : ℝ)
      - ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
          (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
              + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
            * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ (m + r),
        (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
  rw [sub_add_cancel] at htri
  have hE : 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
      ≤ 600 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
    have hA : Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2)) ≤ Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    linarith [mul_le_mul_of_nonneg_right hA hinv.le]
  linarith [h, hc, htri, hE]

/-- **The sum-frequency cosine sums, weighted by the block index.**  The companion of
`RMF.exists_abs_sum_sum_cos_pair_shift_le` for the shear bound, which weights by the envelope. -/
lemma exists_sum_weighted_abs_cos_sum_shift_le :
    ∃ K > 0, ∀ (θ σ ν : ℝ) (r j : ℕ) (s₁ s₂ : ℂ), 0 ≤ θ →
      (∀ m, m < j → |σ| * Real.log (blockScale θ (m + r + 1)) ≤ 1) →
      0 < ν → ν ≤ 1 → |s₁.im + s₂.im| = ν → 1 ≤ ν * Real.exp ((r : ℝ) + θ) →
      (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
          |∑ p ∈ primeBlockSub θ (m + r),
            Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|) ≤ K := by
  obtain ⟨K₁, hK₁, hcos⟩ := exists_abs_sum_cos_primeBlockSub_shift_weighted_le
  refine ⟨K₁, hK₁, ?_⟩
  intro θ σ ν r j s₁ s₂ hθ0 hσm hν0 hν1 hνeq hνsh
  have hconv : ∀ m : ℕ, (∑ p ∈ primeBlockSub θ (m + r),
        Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = ∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (ν * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro m
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hinv1 : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) = 1 / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
      rw [one_div, ← Real.rpow_neg hp0.le]
      congr 1
      ring
    have hcs : Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
        = Real.cos (ν * Real.log ((p : ℕ) : ℝ)) := by
      rcases (abs_eq hν0.le).1 hνeq with h | h
      · rw [h]
      · rw [h, show -ν * Real.log ((p : ℕ) : ℝ) = -(ν * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    rw [hcs, hinv1]
    ring
  simp only [hconv]
  refine (hcos ν σ θ r j hν0 hν1 hθ0 hσm).trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hK₁, hνsh]

/-- **The shear bound, with a shift condition at both frequencies**: the twin of
`RMF.exists_sum_abs_pairSlope_shift_le`. -/
theorem exists_sum_abs_pairSlopeAdd_shift_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsRademacherPrimeValues X μ → ∀ (θ σ τ ν : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        0 < ν → ν ≤ 1 → |s₁.im + s₂.im| = ν → 1 ≤ ν * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < j → 1 / 16 ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)) →
        (∑ m ∈ Finset.range j, ((m : ℝ) + 1) *
            |pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|) ≤ C := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_sum_abs_pairSlopeAdd_shift_sub_sum_cos_le
  obtain ⟨K, hK, hw⟩ := exists_sum_weighted_abs_cos_sum_shift_le
  refine ⟨8 * K + C₀, by positivity, ?_⟩
  intro Ω' _ X μ hX θ σ τ ν n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hτsh hν0 hν1 hνeq hνsh hV
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  have h := hexp Ω' X μ hX θ σ τ n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hτ0 hτ1 hτeq hτsh hV
  have hwb := hw θ σ ν r j s₁ s₂ hθ0 (fun m hm => hσm (m + r) (by omega)) hν0 hν1 hνeq hνsh
  linarith

/-- **The second drift, with a shift condition at both frequencies**: the twin of
`RMF.exists_abs_sum_blockMean₂_regression_shift_sub_le`. -/
theorem exists_abs_sum_blockMeanAdd₂_regression_shift_sub_le :
    ∃ C > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsRademacherPrimeValues X μ → ∀ (θ σ τ ν Kd : ℝ) (n r j : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → r + j ≤ n + 1 → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (n + 1)) ≤ 1 → 0 ≤ Kd →
        (∀ m, m < r + j →
          |∑ p ∈ primeBlockSub θ m,
              Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
            ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → 1 ≤ τ * Real.exp ((r : ℝ) + θ) →
        0 < ν → ν ≤ 1 → |s₁.im + s₂.im| = ν → 1 ≤ ν * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < j → 1 / 16 ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)) →
        |(∑ m ∈ Finset.range j,
            (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (m + r))
              - pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
                (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                  (primeBlockSub θ (m + r)))
                * blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)))) - (j : ℝ)|
          ≤ 2 * driftConstAdd Kd θ + C := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_abs_sum_blockMeanAdd₂_regression_shift_sub_sum_cos_le
  obtain ⟨K, hK, hpair⟩ := exists_abs_sum_sum_cos_pair_shift_le
  obtain ⟨K', hK', hw⟩ := exists_sum_weighted_abs_cos_sum_shift_le
  have he1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hinv : (0 : ℝ) < (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := inv_pos.2 (by linarith)
  refine ⟨K + 320 * K' + 600 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) + 40 * C₀, ?_, ?_⟩
  · nlinarith [hK, hK', hC₀, Real.exp_pos (1 : ℝ), hinv]
  intro Ω' _ X μ hX θ σ τ ν Kd n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hKd hosc hτ0 hτ1 hτeq hτsh
    hν0 hν1 hνeq hνsh hV
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσ
  have h := hexp Ω' X μ hX θ σ τ Kd n r j s₁ s₂ hθ hj hre₁ hre₂ hσ hKd hosc hτ0 hτ1 hτeq hτsh hV
  have hc := hpair θ σ τ ν r j s₁ s₂ hθ0 (fun m hm => hσm (m + r) (by omega))
    hτ0 hτ1 hτeq hτsh hν0 hν1 hνeq hνsh
  have hwb := hw θ σ ν r j s₁ s₂ hθ0 (fun m hm => hσm (m + r) (by omega)) hν0 hν1 hνeq hνsh
  have hE : 600 * (Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
      ≤ 600 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
    have hA : Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2)) ≤ Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    linarith [mul_le_mul_of_nonneg_right hA hinv.le]
  linarith [h, hc, hwb, hE]

/-- **The block covariance is small above the shift**, at both frequencies: `≤ 1/100` once
`Tsh ≤ τe^{r+θ}` and `Tsh ≤ νe^{r+θ}`.  The form `RMF.exists_isBoxComparison_rademacher_of_range`
asks for. -/
theorem exists_abs_blockMatchedCovAdd_shift_le :
    ∃ Tsh > 0, ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsRademacherPrimeValues X μ → ∀ (θ σ τ ν : ℝ) (n r m : ℕ) (s₁ s₂ : ℂ),
        (125 : ℝ) ≤ θ → m + r ≤ n → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (m + r + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
        0 < ν → ν ≤ 1 → |s₁.im + s₂.im| = ν → Tsh ≤ ν * Real.exp ((r : ℝ) + θ) →
        |blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ (m + r))| ≤ 1 / 100 := by
  obtain ⟨K₁, hK₁, hcosblock⟩ := exists_abs_sum_cos_primeBlockSub_le
  refine ⟨400 * K₁ + 1, by positivity, ?_⟩
  intro Ω' _ X μ hX θ σ τ ν n r m s₁ s₂ hθ hmn hre₁ hre₂ hσ hτ0 hτ1 hτeq hτsh hν0 hν1 hνeq hνsh
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hmθ : (8 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ := by
    push_cast
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have hb := abs_blockMatchedCovAdd_prime_le hX hmθ hmn hre₁ hre₂ hσ
  -- each frequency, at the block's own scale
  have hmono : ∀ f : ℝ, 0 < f → f * Real.exp ((r : ℝ) + θ)
      ≤ f * Real.exp (((m + r : ℕ) : ℝ) + θ) := by
    intro f hf
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hf.le
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hone : ∀ f : ℝ, 0 < f → f ≤ 1 → 400 * K₁ + 1 ≤ f * Real.exp ((r : ℝ) + θ) →
      |∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (f * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ)| ≤ 1 / 400 := by
    intro f hf0 hf1 hfsh
    refine (hcosblock f σ θ (m + r) hf0 hf1 hθ0 hσ).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hK₁, hmono f hf0, hfsh]
  have hbd := hone τ hτ0 hτ1 hτsh
  have hbs := hone ν hν0 hν1 hνsh
  -- the two cosine sums, in the shape the covariance bound carries them
  have hconv : (∑ p ∈ primeBlockSub θ (m + r),
        (Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ)))
          * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primeBlockSub θ (m + r),
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
        + ∑ p ∈ primeBlockSub θ (m + r),
            Real.cos (ν * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hinv1 : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) = 1 / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
      rw [one_div, ← Real.rpow_neg hp0.le]
      congr 1
      ring
    have hcd : Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ))
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) := by
      rcases (abs_eq hτ0.le).1 hτeq with h | h
      · rw [h]
      · rw [h, show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    have hcs : Real.cos ((s₁.im + s₂.im) * Real.log ((p : ℕ) : ℝ))
        = Real.cos (ν * Real.log ((p : ℕ) : ℝ)) := by
      rcases (abs_eq hν0.le).1 hνeq with h | h
      · rw [h]
      · rw [h, show -ν * Real.log ((p : ℕ) : ℝ) = -(ν * Real.log ((p : ℕ) : ℝ)) by ring,
          Real.cos_neg]
    rw [hcd, hcs, hinv1]
    ring
  rw [hconv] at hb
  have htri := abs_add_le (∑ p ∈ primeBlockSub θ (m + r),
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
    (∑ p ∈ primeBlockSub θ (m + r),
      Real.cos (ν * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ))
  have hκm : blockWeightSize θ (m + r) ≤ 1 / 1000000 :=
    blockWeightSize_le_millionth (by linarith)
  linarith [hb, htri, hbd, hbs, hκm]

/-- **The drift constant, free of `θ`.**  Both `θ`-dependent terms of `RMF.driftConstAdd` are at
most `1` for `θ ≥ 0`, so the whole constant is bounded by an expression in `Kd` alone.  That is what
lets a statement quantifying over `θ` still export a constant depending only on `Kd`. -/
lemma driftConstAdd_le {Kd θ : ℝ} (hθ : 0 ≤ θ) :
    driftConstAdd Kd θ
      ≤ 4 * Real.exp 2 + 120 * Real.exp 2 + 4 * blockDriftConst
        + 76 * Real.exp 2 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) + 2 * Kd := by
  have he1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hinv : (0 : ℝ) < (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := inv_pos.2 (by linarith)
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp (-(1 + θ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h2 : Real.exp (-(θ / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [driftConstAdd]
  have hA : 120 * Real.exp 2 * Real.exp (-(1 + θ)) ≤ 120 * Real.exp 2 * 1 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hB : 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
      ≤ 76 * Real.exp 2 * (Real.exp 1 * 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 he.le) hinv.le
  linarith [hA, hB]

/-! ### The cutoff transfer

The drifts pin the cutoff: `RMF.exists_abs_sum_blockMeanAdd₂_shift_sub_le` carries
`|σ|\log(\mathrm{blockScale}\,θ\,(n+1)) ≤ 1` at its own cutoff index `n`, and Proposition 7 has
that hypothesis only up to `r+n`, not up to `N`.  So the block statistics are read at `r+n`, the box
comparison produces its laws at `N`, and the two are identified here, as in the Steinhaus file
(`RMF.blockStats₂_shift_cutoff_eq`): raising the cutoff multiplies the tilt by factors at other
primes, independent of `X p`, so no moment of a single prime moves.  The Rademacher transport
carries integrability rather than measurability, so each statistic's weight must be at most `1/5`,
which `RMF.norm_prime_cpow_neg_le_fifth_of_mem_primeBlockSub` supplies on every block. -/

/-- Any moment of a single `X p` is the same under either cutoff, for the two-fold Rademacher
tilt.  The twin of `RMF.integral_comp_tiltedMeasure₂_congr_cutoff`. -/
lemma integral_comp_tiltedMeasure₂_congr_cutoff_rademacher {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) (hp' : p ∈ primesBelowSub y') {g : ℂ → ℝ}
    (hg : Integrable g (rademacherLaw.tilted fun z =>
      2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z + 2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z)) :
    (∫ ω, g (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      = ∫ ω, g (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y' s₁ s₂ μ) := by
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp hg,
    integral_comp_tiltedMeasure₂_rademacher hX y' hs₁ hs₂ hp' hg]

/-- Hence the two-point Rademacher block drift is cutoff-free. -/
lemma blockMeanAdd₂_congr_cutoff {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) (hB' : B ⊆ primesBelowSub y') {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    blockMeanAdd₂ X μ y s₁ s₂ w B = blockMeanAdd₂ X μ y' s₁ s₂ w B :=
  Finset.sum_congr rfl fun p hp =>
    integral_comp_tiltedMeasure₂_congr_cutoff_rademacher hX hs₁ hs₂ (hB hp) (hB' hp)
      (integrable_localLogAdd_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
        (norm_prime_cpow_neg_lt_one p.2 hs₂) (hw p hp))

/-- And so is the matched variance: both of `RMF.matchingVar`'s arguments are such moments. -/
lemma blockMatchedVarAdd₂_congr_cutoff {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) (hB' : B ⊆ primesBelowSub y') {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    blockMatchedVarAdd₂ X μ y s₁ s₂ w B = blockMatchedVarAdd₂ X μ y' s₁ s₂ w B := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have ha₁ := norm_prime_cpow_neg_lt_one p.2 hs₁
  have ha₂ := norm_prime_cpow_neg_lt_one p.2 hs₂
  rw [integral_comp_tiltedMeasure₂_congr_cutoff_rademacher hX hs₁ hs₂ (hB hp) (hB' hp)
      (integrable_localLogAdd_tilted_pair ha₁ ha₂ (hw p hp)),
    integral_comp_tiltedMeasure₂_congr_cutoff_rademacher
      (g := fun z => localLogAdd (w p) z * localLogAdd (w p) z) hX hs₁ hs₂ (hB hp) (hB' hp)
      (integrable_localLogAdd_mul_tilted_pair ha₁ ha₂ (hw p hp) (hw p hp))]

/-- And so is the covariance — three moments this time, and the mixed one is no different. -/
lemma blockMatchedCovAdd_congr_cutoff {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) (hB' : B ⊆ primesBelowSub y') {v w : Nat.Primes → ℂ}
    (hv : ∀ p ∈ B, ‖v p‖ ≤ 1 / 5) (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    blockMatchedCovAdd X μ y s₁ s₂ v w B = blockMatchedCovAdd X μ y' s₁ s₂ v w B := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have ha₁ := norm_prime_cpow_neg_lt_one p.2 hs₁
  have ha₂ := norm_prime_cpow_neg_lt_one p.2 hs₂
  rw [integral_comp_tiltedMeasure₂_congr_cutoff_rademacher
      (g := fun z => localLogAdd (v p) z * localLogAdd (w p) z) hX hs₁ hs₂ (hB hp) (hB' hp)
      (integrable_localLogAdd_mul_tilted_pair ha₁ ha₂ (hv p hp) (hw p hp)),
    integral_comp_tiltedMeasure₂_congr_cutoff_rademacher hX hs₁ hs₂ (hB hp) (hB' hp)
      (integrable_localLogAdd_tilted_pair ha₁ ha₂ (hv p hp)),
    integral_comp_tiltedMeasure₂_congr_cutoff_rademacher hX hs₁ hs₂ (hB hp) (hB' hp)
      (integrable_localLogAdd_tilted_pair ha₁ ha₂ (hw p hp))]

/-- **The cutoff transfer as Proposition 7 needs it**, for the three statistics at Harper's weights:
block `k` of an `n`-block run may be read at any cutoff above it. -/
lemma blockStatsAdd₂_shift_cutoff_eq {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {k n N : ℕ}
    {s₁ s₂ u₁ u₂ : ℂ} (hkn : k ≤ n) (hnN : n ≤ N) (hkθ : (3 : ℝ) ≤ (k : ℝ) + θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hu₁ : u₁.re = 1 / 2 + σ) (hu₂ : u₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (k + 1)) ≤ 1) :
    blockMeanAdd₂ X μ (blockCutoff θ N) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-u₁))
          (primeBlockSub θ k)
        = blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-u₁))
          (primeBlockSub θ k)
      ∧ ((blockMatchedVarAdd₂ X μ (blockCutoff θ N) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-u₁))
            (primeBlockSub θ k) : ℝ≥0) : ℝ)
        = ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-u₁))
            (primeBlockSub θ k) : ℝ≥0) : ℝ)
      ∧ blockMatchedCovAdd X μ (blockCutoff θ N) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-u₁))
            (fun p => ((p : ℕ) : ℂ) ^ (-u₂)) (primeBlockSub θ k)
        = blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-u₁))
            (fun p => ((p : ℕ) : ℂ) ^ (-u₂)) (primeBlockSub θ k) := by
  have hs₁ : 0 < s₁.re := re_pos_of_block hkθ hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hkθ hre₂ hσ
  have h1 : primeBlockSub θ k ⊆ primesBelowSub (blockCutoff θ N) :=
    primeBlockSub_subset_primesBelowSub θ (hkn.trans hnN)
  have h2 : primeBlockSub θ k ⊆ primesBelowSub (blockCutoff θ n) :=
    primeBlockSub_subset_primesBelowSub θ hkn
  have hw₁ : ∀ p ∈ primeBlockSub θ k, ‖((p : ℕ) : ℂ) ^ (-u₁)‖ ≤ 1 / 5 := fun p hp =>
    norm_prime_cpow_neg_le_fifth_of_mem_primeBlockSub hkθ hu₁ hσ hp
  have hw₂ : ∀ p ∈ primeBlockSub θ k, ‖((p : ℕ) : ℂ) ^ (-u₂)‖ ≤ 1 / 5 := fun p hp =>
    norm_prime_cpow_neg_le_fifth_of_mem_primeBlockSub hkθ hu₂ hσ hp
  refine ⟨blockMeanAdd₂_congr_cutoff hX hs₁ hs₂ h1 h2 hw₁, ?_,
    blockMatchedCovAdd_congr_cutoff hX hs₁ hs₂ h1 h2 hw₁ hw₂⟩
  rw [blockMatchedVarAdd₂_congr_cutoff hX hs₁ hs₂ h1 h2 hw₁]

/-! ### The Rademacher form of Harper's Proposition 7

Harper restricts the Rademacher heights to `[1/3, 1/2]` (§5.3) so that every new Rademacher
frequency cancels; the
statements carry the restriction as a hypothesis, since on the anti-diagonal the sum frequency is
zero.  One threshold suffices, as in the Steinhaus twin: `Tsh ≤ |t₁-t₂|e^{r+θ}` gives the other
three shift conditions when the difference frequency is the smallest of the four, which holds for
`t₁, t₂ > 0`, `t₁ + t₂ ≤ 1`, `|t₁-t₂| ≤ 2t₁, 2t₂`
(`RMF.exists_proposition7_upper_rademacher_of_ratio`).  Harper's range is
`RMF.exists_proposition7_upper_rademacher`, and
`RMF.exists_proposition7_upper_rademacher_window` takes windows `[e^{-(k+1)}, e^{-k}]`.  `Cst`
depends on `Kd`, which is quantified first: the drift bound is `2·driftConstAdd Kd θ + C`, and
`RMF.driftConstAdd_le` removes only the `θ`.  The drifts pin the cutoff to `r+n`, hence
`RMF.blockStatsAdd₂_shift_cutoff_eq`.  The envelope hypothesis carries `36` where the Steinhaus one
has `13`, the constant of `RMF.exists_isBoxComparison_rademacher_of_range`. -/

set_option maxHeartbeats 1000000 in
-- the five capped parameters are elaborated against Proposition 7's twenty-odd hypotheses,
-- which is what raises the limit here, exactly as in `RMF.exists_proposition7_upper_steinhaus`
/-- **The Rademacher form of Harper's Proposition 7, at two heights within a factor `3`**: above
the shift, the two-point barrier probability is at most `Cst·\min\{1, a/√n\}²`, `Cst` depending
only on `Kd` and `Bs`, for heights `t₁ ≠ t₂` with `t₁, t₂ > 0`, `t₁ + t₂ ≤ 1` and
`|t₁ - t₂| ≤ 2t₁, 2t₂`.  These make the difference frequency the smallest of the four the pair
statistics see; `RMF.exists_proposition7_upper_rademacher` is Harper's range `[1/3, 1/2]`. -/
theorem exists_proposition7_upper_rademacher_of_ratio (Kd Bs : ℝ) (hKd : 0 ≤ Kd)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (θ σ η a : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (r + n + 1)) ≤ η →
          0 < s₁.im → 0 < s₂.im → s₁.im + s₂.im ≤ 1 →
          |s₁.im - s₂.im| ≤ 2 * s₁.im → |s₁.im - s₂.im| ≤ 2 * s₂.im → s₁.im ≠ s₂.im →
          Tsh ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < r + n →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < r + n →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < n →
            boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)
                + blockWindow m + blockWindow m + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
          4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) n
                (fun j => -a - Bs * j) (fun j => a + j + hf j)
                (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (a / Real.sqrt n) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁, hdrift₁⟩ := exists_abs_sum_blockMeanAdd₂_shift_sub_le
  obtain ⟨C₂, hC₂, hdrift₂⟩ := exists_abs_sum_blockMeanAdd₂_regression_shift_sub_le
  obtain ⟨C₃, hC₃, hshear⟩ := exists_sum_abs_pairSlopeAdd_shift_le
  obtain ⟨Tc, hTc, hcovb⟩ := exists_abs_blockMatchedCovAdd_shift_le
  obtain ⟨Tv, hTv, hvarb⟩ := exists_blockMatchedVarAdd₂_concrete_top
  have hB : (0 : ℝ) < Bs := lt_of_lt_of_le (blockSlope_pos 125) hBs
  have hRC : (1 : ℝ) ≤ result1Const (1 / 18) (9 / 2) := one_le_result1Const _ _
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hinvpos : (0 : ℝ) < (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := inv_pos.2 (by linarith)
  -- the `θ`-free drift constant
  set DA : ℝ := 4 * Real.exp 2 + 120 * Real.exp 2 + 4 * blockDriftConst
    + 76 * Real.exp 2 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) + 2 * Kd with hDAdef
  have hDA0 : (0 : ℝ) ≤ DA := by
    rw [hDAdef]
    have hbdc : (0 : ℝ) ≤ blockDriftConst := blockDriftConst_nonneg
    have hY : (0 : ℝ) ≤ Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ :=
      mul_nonneg (Real.exp_pos 1).le hinvpos.le
    have hT : (0 : ℝ) ≤ 76 * Real.exp 2 * (Real.exp 1 * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) :=
      mul_nonneg (by positivity) hY
    linarith [Real.exp_pos (2 : ℝ)]
  have hD0 : (0 : ℝ) < 2 * DA + max C₁ C₂ := by
    have : (0 : ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
    linarith
  have hbase : (0 : ℝ) < result1Const (1 / 18) (9 / 2) * (1 + 2 * (2 * DA + max C₁ C₂))
      * (15 + Bs + (52 + 4 * Bs) * C₃ + 10 * Real.log 2) := by
    have h2 : (0 : ℝ)
        < 15 + Bs + (52 + 4 * Bs) * C₃ + 10 * Real.log 2 := by
      nlinarith [hB, hC₃, hlog2]
    exact mul_pos (mul_pos (by linarith) (by linarith)) h2
  refine ⟨3 * (result1Const (1 / 18) (9 / 2) * (1 + 2 * (2 * DA + max C₁ C₂))
      * (15 + Bs + (52 + 4 * Bs) * C₃ + 10 * Real.log 2)) ^ 2,
    max (max Tc Tv) 1, by positivity, by positivity, ?_⟩
  intro Ω' _ X μ hX θ σ η a N r n s₁ s₂ hf hθ hrn hre₁ hre₂ hη0 hη1 hσtop
    him₁0 him₂0 hν1 hdif₁ hdif₂ himne hTsh hosc₁ hosc₂ henvc ha hn4 hbig hbig2 hhf
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hσm : ∀ m, m ≤ r + n → |σ| * Real.log (blockScale θ (m + 1)) ≤ η :=
    hsigma_of_top_of_le hσtop
  have hσm1 : ∀ m, m ≤ r + n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 :=
    fun m hm => le_trans (hσm m hm) (by linarith)
  -- the four frequencies: the difference is at most the sum and each doubled height
  have hτ0 : 0 < |s₁.im - s₂.im| := abs_pos.2 (sub_ne_zero.2 himne)
  have hτν' : |s₁.im - s₂.im| ≤ s₁.im + s₂.im := by
    rw [abs_le]
    constructor <;> linarith
  have hτ1 : |s₁.im - s₂.im| ≤ 1 := by linarith
  have hνeq : |s₁.im + s₂.im| = s₁.im + s₂.im := abs_of_pos (by linarith)
  have hν0 : 0 < s₁.im + s₂.im := by linarith
  have hexp : (0 : ℝ) < Real.exp ((r : ℝ) + θ) := Real.exp_pos _
  have hτν : |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ)
      ≤ (s₁.im + s₂.im) * Real.exp ((r : ℝ) + θ) :=
    mul_le_mul_of_nonneg_right hτν' hexp.le
  have hTsh1 : (1 : ℝ) ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) :=
    le_trans (le_max_right _ _) hTsh
  have hTshν : (1 : ℝ) ≤ (s₁.im + s₂.im) * Real.exp ((r : ℝ) + θ) := by linarith
  have hTc' : Tc ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTsh
  have hTcν : Tc ≤ (s₁.im + s₂.im) * Real.exp ((r : ℝ) + θ) := by linarith
  have hTv' : Tv ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTsh
  have hm3₀ : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + θ := by
    push_cast
    linarith
  have hsre₁ : 0 < s₁.re := re_pos_of_block hm3₀ hre₁ (hσm1 0 (by omega))
  have hsre₂ : 0 < s₂.re := re_pos_of_block hm3₀ hre₂ (hσm1 0 (by omega))
  have hrcast : ∀ m : ℕ, (9 : ℝ) ≤ ((m + r : ℕ) : ℝ) + θ := by
    intro m
    push_cast
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  -- the covariance, at any cutoff above the block
  have hcovsmall : ∀ M : ℕ, ∀ m, m ≤ n → m + r ≤ M →
      |blockMatchedCovAdd X μ (blockCutoff θ M) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ (m + r))| ≤ 1 / 100 := fun M m hm hmM =>
    hcovb Ω' X μ hX θ σ (|s₁.im - s₂.im|) (s₁.im + s₂.im) M r m s₁ s₂ hθ hmM
      hre₁ hre₂ (hσm1 (m + r) (by omega)) hτ0 hτ1 rfl hTc' hν0 hν1 hνeq hTcν
  -- the variance brackets, at any cutoff above the block
  have hvargen : ∀ u : ℂ, u.re = 1 / 2 + σ → 0 < u.im → u.im ≤ 1 →
      |s₁.im - s₂.im| ≤ 2 * u.im →
      ∀ M : ℕ, ∀ m, m ≤ n → m + r ≤ M →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ M) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-u)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ M) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-u)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ) ≤ 9 := by
    intro u hu hul huu hud M m hm hmr
    have hexpm : Real.exp ((r : ℝ) + θ) ≤ Real.exp (((m + r : ℕ) : ℝ) + θ) := by
      refine Real.exp_le_exp.2 ?_
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hsq : (2 * u.im) ^ 2 ≤ Real.exp (((m + r : ℕ) : ℝ) + θ) := by
      have h1 : (2 * u.im) ^ 2 ≤ 4 := by nlinarith only [hul, huu]
      have h2 : (4 : ℝ) ≤ Real.exp (((m + r : ℕ) : ℝ) + θ) := by
        linarith [hrcast m, Real.add_one_le_exp (((m + r : ℕ) : ℝ) + θ)]
      linarith
    have hTvm : Tv ≤ 2 * u.im * Real.exp (((m + r : ℕ) : ℝ) + θ) := by
      have hstep : |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ)
          ≤ 2 * u.im * Real.exp (((m + r : ℕ) : ℝ) + θ) := by
        have ha : |s₁.im - s₂.im| ≤ 2 * u.im := hud
        calc |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ)
            ≤ 2 * u.im * Real.exp ((r : ℝ) + θ) :=
              mul_le_mul_of_nonneg_right ha hexp.le
          _ ≤ 2 * u.im * Real.exp (((m + r : ℕ) : ℝ) + θ) :=
              mul_le_mul_of_nonneg_left hexpm (by linarith)
      linarith
    exact hvarb Ω' X μ hX θ σ η (m + r) (blockCutoff θ M) s₁ s₂ u
      (fun p => ((p : ℕ) : ℂ) ^ (-u)) hsre₁ hsre₂ hre₁ hre₂ hu (hrcast m) hθ0 hη0 hη1
      (hσm (m + r) (by omega)) (by linarith) hsq hTvm (fun _ _ => rfl)
      (primeBlockSub_subset_primesBelowSub θ hmr)
  have hvar₁ := hvargen s₁ hre₁ him₁0 (by linarith) hdif₁
  have hvar₂ := hvargen s₂ hre₂ him₂0 (by linarith) hdif₂
  -- Proposition 7 above the shift is Proposition 7 at offset `θ + r`
  have hθ' : (125 : ℝ) ≤ θ + r := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have hσtop' : |σ| * Real.log (blockScale (θ + r) (n + 1)) ≤ 1 := by
    rw [blockScale_add_nat, show n + 1 + r = n + r + 1 from by omega]
    exact hσm1 (n + r) (by omega)
  have hV₁' : ∀ m, m < n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff (θ + r) (N - r)) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub (θ + r) m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff (θ + r) (N - r)) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub (θ + r) m) : ℝ≥0) : ℝ) ≤ 9 := by
    intro m hm
    rw [blockCutoff_add_nat, primeBlockSub_add_nat, show N - r + r = N from by omega]
    exact hvar₁ N m (by omega) (by omega)
  have hV₂' : ∀ m, m < n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff (θ + r) (N - r)) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub (θ + r) m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff (θ + r) (N - r)) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub (θ + r) m) : ℝ≥0) : ℝ) ≤ 9 := by
    intro m hm
    rw [blockCutoff_add_nat, primeBlockSub_add_nat, show N - r + r = N from by omega]
    exact hvar₂ N m (by omega) (by omega)
  have hcov' : ∀ m, m < n → |blockMatchedCovAdd X μ (blockCutoff (θ + r) (N - r)) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
      (primeBlockSub (θ + r) m)| ≤ 1 / 100 := by
    intro m hm
    rw [blockCutoff_add_nat, primeBlockSub_add_nat, show N - r + r = N from by omega]
    exact hcovsmall N m (by omega) (by omega)
  have henvc' : ∀ m, m < n →
      (boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1) + blockWindow m)
          + blockWindow m + 36
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1))) := by
    intro m hm
    linarith [henvc m hm]
  obtain ⟨Ω₂, mΩ₂, Q, Nb, hQ, hNbm, hNbi, hNblaw, hcmpAll⟩ :=
    exists_isBoxComparison_rademacher_of_range
      (M := fun m => boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)
        + blockWindow m)
      hX hθ' (by omega : n ≤ N - r) hre₁ hre₂ hσtop' hV₁' hV₂' hcov' henvc'
  have hcut : blockCutoff (θ + r) (N - r) = blockCutoff θ N := by
    rw [blockCutoff_add_nat, show N - r + r = N from by omega]
  simp only [hcut, primeBlockSub_add_nat] at hNblaw hcmpAll
  -- the five capped parameters, at the cutoff the drifts are pinned to
  have hVn₁ : ∀ m, m < n → 1 / 16 ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ) := by
    intro m hm
    linarith [(hvar₁ (r + n) m (by omega) (by omega)).1]
  set m₁ : ℕ → ℝ := fun i => if i < n then blockMeanAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) else 0 with hm₁def
  set m₂ : ℕ → ℝ := fun i => if i < n then blockMeanAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (i + r)) else 0 with hm₂def
  set V₁ : ℕ → ℝ := fun i => if i < n then ((blockMatchedVarAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) : ℝ≥0) : ℝ) else 1 with hV₁def
  set V₂ : ℕ → ℝ := fun i => if i < n then ((blockMatchedVarAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (i + r)) : ℝ≥0) : ℝ) else 1 with hV₂def
  set cvv : ℕ → ℝ := fun i => if i < n then blockMatchedCovAdd X μ (blockCutoff θ (r + n)) s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
    (primeBlockSub θ (i + r)) else 0 with hcvvdef
  have hbr : ∀ i, i < n → (1 / 16 ≤ V₁ i ∧ V₁ i ≤ 9 / 2) ∧ (1 / 16 ≤ V₂ i ∧ V₂ i ≤ 9 / 2) := by
    intro i hi
    rw [hV₁def, hV₂def]
    simp only [if_pos hi]
    obtain ⟨a₁, b₁⟩ := hvar₁ (r + n) i (by omega) (by omega)
    obtain ⟨a₂, b₂⟩ := hvar₂ (r + n) i (by omega) (by omega)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
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
        exact hcovsmall (r + n) i (by omega) (by omega)
      have hcs := (abs_pairSlope_le_and_cs_of_abs_le h₁l h₂l hcv).2
      have hb := pairResidVar_bracket (by linarith : (0 : ℝ) < V₁ i) (by linarith)
        (by linarith) hcs
      constructor <;> linarith [hb.1, hb.2]
    · rw [hV₁def, hV₂def, hcvvdef]
      simp only [if_neg hi, pairResidVar]
      norm_num
  -- the two drifts
  have hDAle : driftConstAdd Kd θ ≤ DA := by
    rw [hDAdef]
    exact driftConstAdd_le hθ0
  have hd₁ : ∀ j, j ≤ n → |(∑ i ∈ Finset.range j, m₁ i) - (j : ℝ)|
      ≤ 2 * DA + max C₁ C₂ := by
    intro j hj
    have hcongr : (∑ i ∈ Finset.range j, m₁ i)
        = ∑ i ∈ Finset.range j, blockMeanAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n := by
        have := Finset.mem_range.1 hi
        omega
      rw [hm₁def]
      simp only [if_pos hin]
    rw [hcongr]
    have h := hdrift₁ Ω' X μ hX θ σ (|s₁.im - s₂.im|) (s₁.im + s₂.im) Kd (r + n) r j s₁ s₂
      hθ (by omega) hre₁ hre₂ (hσm1 (r + n) le_rfl) hKd (fun m hm => hosc₁ m (by omega))
      hτ0 hτ1 rfl hTsh1 hν0 hν1 hνeq hTshν
    linarith [le_max_left C₁ C₂]
  have hd₂ : ∀ j, j ≤ n →
      |(∑ i ∈ Finset.range j, (m₂ i - pairSlope (V₁ i) (cvv i) * m₁ i)) - (j : ℝ)|
        ≤ 2 * DA + max C₁ C₂ := by
    intro j hj
    have hcongr : (∑ i ∈ Finset.range j, (m₂ i - pairSlope (V₁ i) (cvv i) * m₁ i))
        = ∑ i ∈ Finset.range j,
            (blockMeanAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ (i + r))
              - pairSlope ((blockMatchedVarAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r)) : ℝ≥0) : ℝ)
                (blockMatchedCovAdd X μ (blockCutoff θ (r + n)) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                  (primeBlockSub θ (i + r)))
                * blockMeanAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                  (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (i + r))) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n := by
        have := Finset.mem_range.1 hi
        omega
      rw [hm₁def, hm₂def, hV₁def, hcvvdef]
      simp only [if_pos hin]
    rw [hcongr]
    have h := hdrift₂ Ω' X μ hX θ σ (|s₁.im - s₂.im|) (s₁.im + s₂.im) Kd (r + n) r j s₁ s₂
      hθ (by omega) hre₁ hre₂ (hσm1 (r + n) le_rfl) hKd (fun m hm => hosc₂ m (by omega))
      hτ0 hτ1 rfl hTsh1 hν0 hν1 hνeq hTshν (fun m hm => hVn₁ m (by omega))
    linarith [le_max_right C₁ C₂]
  -- the shear bound
  obtain ⟨hM0, hMup, hMlin⟩ := boxEnvelope_spec hB a
  have hKb : (∑ m ∈ Finset.range n, |pairSlope (V₁ m) (cvv m)|
        * (boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)))
      ≤ (52 + 4 * Bs) * C₃ := by
    have hstep : ∀ m ∈ Finset.range n,
        |pairSlope (V₁ m) (cvv m)|
            * (boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1))
          ≤ (52 + 4 * Bs) * (((m : ℝ) + 1) * |pairSlope
              ((blockMatchedVarAdd₂ X μ (blockCutoff θ (r + n)) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ (m + r)) : ℝ≥0) : ℝ)
              (blockMatchedCovAdd X μ (blockCutoff θ (r + n)) s₁ s₂
                (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
                (primeBlockSub θ (m + r)))|) := by
      intro m hm
      have hmn : m < n := Finset.mem_range.1 hm
      have hgen : ∀ (x : ℝ) (i : ℕ), 0 ≤ x →
          x * (boxEnvelope (Bs) i + boxEnvelope (Bs) (i + 1))
            ≤ (52 + 4 * Bs) * (((i : ℝ) + 1) * x) := by
        intro x i hx
        nlinarith only [hMlin i, hx]
      rw [hV₁def, hcvvdef]
      simp only [if_pos hmn]
      exact hgen _ m (abs_nonneg _)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact hshear Ω' X μ hX θ σ (|s₁.im - s₂.im|) (s₁.im + s₂.im) (r + n) r n s₁ s₂
      hθ (by omega) hre₁ hre₂ (hσm1 (r + n) le_rfl) hτ0 hτ1 rfl hTsh1 hν0 hν1 hνeq hTshν hVn₁
  -- the comparison, at Proposition 7's restart
  haveI hP : IsProbabilityMeasure (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
      (blockCutoff θ N) s₁ s₂ μ) :=
    isProbabilityMeasure_tiltedMeasure₂_rademacher hX (blockCutoff θ N) hsre₁ hsre₂
  have hcmp : IsBoxComparison (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
      (blockCutoff θ N) s₁ s₂ μ) Q
      (fun m => (fun m' ω => ∑ p ∈ primeBlockSub θ (m' + r),
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (m + ⌊a⌋₊))
      (fun m => Nb (m + ⌊a⌋₊)) (fun m => blockWindow (m + ⌊a⌋₊))
      (fun m => (fun i => boxEnvelope (Bs) i
        + boxEnvelope (Bs) (i + 1) + blockWindow i) (m + ⌊a⌋₊)) (n - ⌊a⌋₊) (1 / 2) := by
    by_cases hk : ⌊a⌋₊ ≤ n
    · have h := hcmpAll ⌊a⌋₊ hk
      rwa [show (2 : ℝ) * (1 / 4) = 1 / 2 from by norm_num] at h
    · rw [show n - ⌊a⌋₊ = 0 from by omega]
      exact isBoxComparison_zero _ _ _ _ (by norm_num)
  have hlawcap : ∀ i, i < n →
      Q.map (Nb i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (cvv i) := by
    intro i hi
    have hkθ : (3 : ℝ) ≤ ((i + r : ℕ) : ℝ) + θ := by linarith [hrcast i]
    obtain ⟨e₁, ev₁, _⟩ := blockStatsAdd₂_shift_cutoff_eq (u₁ := s₁) (u₂ := s₁) hX
      (by omega : i + r ≤ r + n) (by omega : r + n ≤ N) hkθ hre₁ hre₂ hre₁ hre₁
      (hσm1 (i + r) (by omega))
    obtain ⟨e₂, ev₂, _⟩ := blockStatsAdd₂_shift_cutoff_eq (u₁ := s₂) (u₂ := s₂) hX
      (by omega : i + r ≤ r + n) (by omega : r + n ≤ N) hkθ hre₁ hre₂ hre₂ hre₂
      (hσm1 (i + r) (by omega))
    obtain ⟨_, _, ecov⟩ := blockStatsAdd₂_shift_cutoff_eq (u₁ := s₁) (u₂ := s₂) hX
      (by omega : i + r ≤ r + n) (by omega : r + n ≤ N) hkθ hre₁ hre₂ hre₁ hre₂
      (hσm1 (i + r) (by omega))
    rw [hm₁def, hm₂def, hV₁def, hV₂def, hcvvdef]
    simp only [if_pos hi]
    rw [← e₁, ← e₂, ← ev₁, ← ev₂, ← ecov]
    exact hNblaw i (by omega)
  -- and Proposition 7
  refine proposition7_upper_of_law (nlaw := n) (m₁ := m₁) (m₂ := m₂) (V₁ := V₁) (V₂ := V₂)
    (cv := cvv) hNbm hNbi hlawcap
    (by norm_num : (0 : ℝ) < 1 / 18) hlo₁ hhi₁ (fun i => (hres₁ i).1) (fun i => (hres₁ i).2)
    hD0.le (by positivity) hB _ hP _ blockWindow (boxEnvelope (Bs))
    (fun i => boxEnvelope (Bs) i + boxEnvelope (Bs) (i + 1)
      + blockWindow i) n (1 / 2) a hf le_rfl
    (fun m => Finset.measurable_sum _ fun p _ =>
      ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).prodMk
        ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)))
    hd₁ hd₂ (fun m => blockWindow_pos m) (fun j _ => sum_inv_sq_range_le_two j)
    (fun j => hM0 j) (fun j hj _ => hMup j hj) (fun m _ => le_refl _) hKb (by norm_num) le_rfl
    hcmp ha hn4 hbig hbig2 hhf

/-- **The Rademacher form of Harper's Proposition 7**: above the shift and on Harper's heights
`[1/3, 1/2]`, the two-point barrier probability is at most `Cst·\min\{1, a/√n\}²`, `Cst` depending
only on `Kd` and `Bs`.  `RMF.exists_proposition7_upper_rademacher_of_ratio` on `[1/3, 1/2]`, where
the difference frequency is at most `1/6` and each doubled height is at least `2/3`. -/
theorem exists_proposition7_upper_rademacher (Kd Bs : ℝ) (hKd : 0 ≤ Kd)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (θ σ η a : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (r + n + 1)) ≤ η →
          1 / 3 ≤ s₁.im → s₁.im ≤ 1 / 2 → 1 / 3 ≤ s₂.im → s₂.im ≤ 1 / 2 → s₁.im ≠ s₂.im →
          Tsh ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < r + n →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < r + n →
            |∑ p ∈ primeBlockSub θ m,
                Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(m : ℝ)))) →
          (∀ m, m < n →
            boxEnvelope (Bs) m + boxEnvelope (Bs) (m + 1)
                + blockWindow m + blockWindow m + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
          4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) n
                (fun j => -a - Bs * j) (fun j => a + j + hf j)
                (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (a / Real.sqrt n) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, H⟩ := exists_proposition7_upper_rademacher_of_ratio Kd Bs hKd hBs
  refine ⟨Cst, Tsh, hCst, hTsh, ?_⟩
  intro Ω' _ X μ hX θ σ η a N r n s₁ s₂ hf hθ hrn hre₁ hre₂ hη0 hη1 hσtop
    him₁l him₁u him₂l him₂u himne hTsh' hosc₁ hosc₂ henvc ha hn4 hbig hbig2 hhf
  have hd : |s₁.im - s₂.im| ≤ 1 / 6 := by
    rw [abs_le]
    constructor <;> linarith
  exact H Ω' X μ hX θ σ η a N r n s₁ s₂ hf hθ hrn hre₁ hre₂ hη0 hη1 hσtop (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) himne hTsh' hosc₁ hosc₂ henvc ha
    hn4 hbig hbig2 hhf

end RMF
