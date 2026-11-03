/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperScales

/-!
# The restricted first moment of the Steinhaus Euler product

Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654), §5: the lower bound in
Theorem 1 applies Hölder's inequality `E[X^q] ≥ (E X)^{2-q}/(E X²)^{1-q}` to
`X = ∫_T 1_{L(t)}‖F(1/2+σ+it)‖² dt`, where `L(t)` is the barrier event at height `t` and Key
Proposition 5 bounds `E X²`.  This file bounds the restricted mean `E[1_{L(t)}‖F‖²]`, at one height
and integrated over `T`, with `n = RMF.harperBlockCount D x`, `0 ≤ σ` and `|σ|\log x ≤ η ≤ E₀`:

* the `_of_le` forms: at most `A·min{1, a/√(n-r)}·E‖F‖²` for the barrier constrained only on
  `[r, n]`, at slope `RMF.blockSlopeOf E₀ 125`;
* the `_of_top` forms, where the barrier stops `d` blocks short and `E₀ ≤ e^d`, at slope
  `RMF.blockSlope 125`: at least `α·min{1, a/√(n-d)}·E‖F‖²` on `[1, n-d]`, and at most
  `A·min{1, a/√(n-d-r)}·E‖F‖²` on `[r, n-d]`.

At one height the bound is an identity plus Proposition 5: `∫_A ‖F‖² = P'(A)·E‖F‖²`
(`RMF.IsSteinhausRMF.setIntegral_normSq_eq`), and Harper's Proposition 5 bounds `P'(A)` with
constants that do not see `Im s`.  `E‖F(s)‖²` depends only on `Re s`
(`RMF.IsSteinhausRMF.integral_normSq_shiftLine_eq`), so integrating over `t` multiplies by `|T|`.
The swap is Tonelli: `RMF.randomEulerProduct` is a `tsum`, a.e. equal to its closed form on the
unimodularity event, which does not depend on `t`, and the barrier event is jointly measurable
(`RMF.measurableSet_barrierEvent_uncurry`).

The level `a` is left to the consumer: `a = max{a₀, min{√n, 1/(1-q)}}` gives
`min{1, a/√n} ≥ 1/(1 + (1-q)√n)`, the shape the Hölder step needs.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### Joint measurability in `(ω, t)`

The `t`-integral needs Tonelli, and Tonelli needs the integrand measurable in the pair.  The
walk is *plainly* jointly measurable — `localLog` is an honest formula.  The Euler product is
not: `RMF.localFactor` is a `tsum`, equal to `(1 - f(p)p^{-s})⁻¹` only on the event where the
values are unimodular.  That event has full measure and does not depend on `t`, so the
identification lifts to the product measure. -/

/-- The abscissa `1/2 + σ + it`, as a function of the height. -/
noncomputable def shiftLine (σ t : ℝ) : ℂ := ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I

@[simp] lemma re_shiftLine (σ t : ℝ) : (shiftLine σ t).re = 1 / 2 + σ := by
  simp [shiftLine]

lemma continuous_shiftLine (σ : ℝ) : Continuous (shiftLine σ) := by
  unfold shiftLine
  fun_prop

lemma continuous_cpow_neg_shiftLine {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    Continuous fun t : ℝ => ((p : ℂ)) ^ (-(shiftLine σ t)) := by
  have hp0 : ((p : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  exact (continuous_shiftLine σ).neg.const_cpow (Or.inl hp0)

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- The block sum of local logarithms is jointly measurable in `(ω, t)`. -/
lemma measurable_blockSum_uncurry {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ))) (σ : ℝ)
    (B : Finset Nat.Primes) :
    Measurable fun q : Ω' × ℝ => ∑ p ∈ B,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1) := by
  refine Finset.measurable_sum _ fun p _ => ?_
  have hrw : (fun q : Ω' × ℝ =>
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1))
      = fun q : Ω' × ℝ => -Real.log ‖1 - Y ((p : Nat.Primes) : ℕ) q.1
          * (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)))‖ := rfl
  rw [hrw]
  have h1 : Measurable fun q : Ω' × ℝ => Y ((p : Nat.Primes) : ℕ) q.1 :=
    (hY p).comp measurable_fst
  have h2 : Measurable fun q : Ω' × ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
    ((continuous_cpow_neg_shiftLine (p : Nat.Primes).2.pos σ).measurable).comp measurable_snd
  exact (Real.measurable_log.comp ((h1.mul h2).const_sub 1).norm).neg

/-- Hence the barrier event, read as a subset of `Ω' × ℝ`, is measurable. -/
lemma measurableSet_barrierEvent_uncurry {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ))) (σ : ℝ) (θ : ℝ) (n : ℕ)
    (u v : ℕ → ℝ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ barrierEvent
      (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) ω)) n u v} := by
  have hrw : {q : Ω' × ℝ | q.1 ∈ barrierEvent
      (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) ω)) n u v}
      = ⋂ j ∈ Set.Icc 1 n, {q : Ω' × ℝ | (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1))
            ∈ Set.Icc (u j) (v j)} := by
    ext q
    simp only [Set.mem_setOf_eq, barrierEvent, Set.mem_iInter, Set.mem_Icc, walk,
      Finset.sum_apply]
    constructor
    · intro h j hj
      exact h j hj.1 hj.2
    · intro h j hj1 hj2
      exact h j ⟨hj1, hj2⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_
  have hm : Measurable fun q : Ω' × ℝ => ∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1) :=
    Finset.measurable_sum _ fun m _ => measurable_blockSum_uncurry hY σ _
  exact hm measurableSet_Icc

/-- **The free-start barrier event is measurable.**  The same intersection as
`RMF.measurableSet_barrierEvent`, over `[r, n]` rather than `[1, n]`. -/
lemma measurableSet_freeStartBarrier {X : ℕ → Ω' → ℝ} (hX : ∀ m, Measurable (X m)) (r n : ℕ)
    (u v : ℕ → ℝ) :
    MeasurableSet {ω | ∀ j, r ≤ j → j ≤ n → walk X j ω ∈ Set.Icc (u j) (v j)} := by
  have hrw : {ω | ∀ j, r ≤ j → j ≤ n → walk X j ω ∈ Set.Icc (u j) (v j)}
      = ⋂ j ∈ Set.Icc r n, (walk X j) ⁻¹' (Set.Icc (u j) (v j)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    (measurable_walk_of hX j) measurableSet_Icc

/-- And so is its uncurried form on `Ω' × ℝ`. -/
lemma measurableSet_freeStartBarrier_uncurry {Y : ℕ → Ω' → ℂ}
    (hY : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ))) (σ : ℝ) (θ : ℝ) (r n : ℕ)
    (u v : ℕ → ℝ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r ≤ j → j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (u j) (v j)}} := by
  have hrw : {q : Ω' × ℝ | q.1 ∈ {ω | ∀ j, r ≤ j → j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (u j) (v j)}}
      = ⋂ j ∈ Set.Icc r n, {q : Ω' × ℝ | (∑ m ∈ Finset.range j, ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1))
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
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y ((p : Nat.Primes) : ℕ) q.1) :=
    Finset.measurable_sum _ fun m _ => measurable_blockSum_uncurry hY σ _
  exact hm measurableSet_Icc

/-! ### Suprema over the height

Hamdan's Lemma B.2 bounds `P(max_{h ∈ [0,e^{-j}]} S_j(σ+ih) > V)`, and that event has to be
measurable.  On a measurable set of `ω` with continuous sample paths it is: a supremum over a real
interval of a continuous path is a countable supremum over the endpoints and the rationals inside.

Continuity cannot be weakened to "for almost every `ω`", since the identity is one of sets.  The
application intersects with the full-measure set `{ω | ∀ p ∈ B, ‖X p ω‖ ≤ 1}`, on which the path
is continuous for each `ω`, and returns with `RMF.measure_eq_measure_inter_of_compl_null`. -/

/-- If `Gᶜ` is null then every set has the same measure as its trace on `G`.  No measurability of
the set is required — `μ` is an outer measure — which is exactly what lets the supremum event be
handled through its trace on the unimodularity set. -/
lemma measure_eq_measure_inter_of_compl_null {μ : Measure Ω'} {G : Set Ω'} (hG : μ Gᶜ = 0)
    (s : Set Ω') : μ s = μ (G ∩ s) := by
  refine le_antisymm ?_ (measure_mono Set.inter_subset_right)
  calc μ s ≤ μ ((G ∩ s) ∪ Gᶜ) := by
        refine measure_mono fun x hx => ?_
        by_cases h : x ∈ G
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr h
    _ ≤ μ (G ∩ s) + μ Gᶜ := measure_union_le _ _
    _ = μ (G ∩ s) := by rw [hG, add_zero]

/-- **The unimodularity set has full measure**, indexed by a finite set of primes.

The sibling of `RMF.ae_forall_norm_le_one`, which is indexed by `Nat.primesBelow`; the walk's
blocks are `Finset Nat.Primes`.  Together with
`RMF.measure_eq_measure_inter_of_compl_null` this is what moves a bound on the trace of the
supremum event back to the event itself. -/
lemma ae_forall_norm_le_one_finset {X : ℕ → Ω' → ℂ} {ν : Measure ℂ} {μ : Measure Ω'}
    (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (B : Finset Nat.Primes) :
    ∀ᵐ ω ∂μ, ∀ p ∈ B, ‖X ((p : Nat.Primes) : ℕ) ω‖ ≤ 1 := by
  refine (Filter.eventually_all_finset _).2 fun p _ => ?_
  have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
    measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
  exact ((hX.hasLaw ((p : Nat.Primes) : ℕ) p.2).ae_iff hmeasP).2 hν

/-! ### The tilt's defining property, rearranged -/

/-- `∫_A ‖F‖² = P'(A)·E‖F‖²`.  This is `RMF.IsSteinhausRMF.tiltedMeasure_apply` with the
division undone — the whole content of the join, once Proposition 5 supplies `P'(A)`. -/
lemma IsSteinhausRMF.setIntegral_normSq_eq {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω in A, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
      = (tiltedMeasure f y s μ A).toReal * ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ := by
  have hZ0 : (0 : ℝ) < ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ := by
    rw [hf.integral_norm_randomEulerProduct_sq y hs]
    refine Finset.prod_pos fun p hp => ?_
    have h := norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hs
    have h0 : (0 : ℝ) ≤ ‖(p : ℂ) ^ (-s)‖ := norm_nonneg _
    exact inv_pos.2 (by nlinarith)
  have hA0 : (0 : ℝ) ≤ ∫ ω in A, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ :=
    setIntegral_nonneg hA fun _ _ => by positivity
  rw [hf.tiltedMeasure_apply y hs hA, ENNReal.toReal_ofReal (div_nonneg hA0 hZ0.le)]
  field_simp

/-! ### The `t`-integral

The second moment `E‖F(s)‖²` is `∏_{p<y}(1-‖p^{-s}‖²)⁻¹`, and `‖p^{-s}‖ = p^{-Re s}`, so it does
not move with the height.  That is what makes the `t`-integral a multiplication. -/

/-- `E‖F(s)‖²` depends on `s` only through `Re s`, so it is constant along the shifted line. -/
lemma IsSteinhausRMF.integral_normSq_shiftLine_eq {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y : ℕ) {σ : ℝ}
    (hσ : 0 < 1 / 2 + σ) (t t' : ℝ) :
    (∫ ω, ‖randomEulerProduct f y (shiftLine σ t) ω‖ ^ 2 ∂μ)
      = ∫ ω, ‖randomEulerProduct f y (shiftLine σ t') ω‖ ^ 2 ∂μ := by
  have hs : ∀ r : ℝ, 0 < (shiftLine σ r).re := fun r => by rw [re_shiftLine]; exact hσ
  rw [hf.integral_norm_randomEulerProduct_sq y (hs t),
    hf.integral_norm_randomEulerProduct_sq y (hs t')]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hppos : 0 < p := (Nat.prime_of_mem_primesBelow hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hppos, Complex.norm_natCast_cpow_of_pos hppos,
    Complex.neg_re, Complex.neg_re, re_shiftLine, re_shiftLine]

/-! ### A per-height bound, integrated over the height range

The last step of every join in this file and in its Rademacher and `Strong` counterparts: once
`integral_integral_swap` has put the height integral outside, a bound holding at each height
integrates to `|T|` times itself.  `L`, `g` and `K` are arbitrary. -/

/-- **A per-height upper bound integrates over `T`.** -/
theorem integral_indicator_le_of_per_height {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} [SFinite ν] {L : ℝ → Set Ω'} {g : ℝ → Ω' → ℝ}
    {T : Set ℝ} (hT : MeasurableSet T)
    (hTfin : volume T ≠ ⊤) {K : ℝ}
    (hInt : Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)))
    (hper : ∀ t ∈ T, (∫ ω, Set.indicator (L t) (g t) ω ∂ν) ≤ K * ∫ ω, g 0 ω ∂ν) :
    (∫ t in T, ∫ ω, Set.indicator (L t) (g t) ω ∂ν)
      ≤ (volume T).toReal * K * ∫ ω, g 0 ω ∂ν := by
  have hconst : IntegrableOn (fun _ : ℝ => K * ∫ ω, g 0 ω ∂ν) T := integrableOn_const hTfin
  have hmono := setIntegral_mono_on hInt.integral_prod_right hconst hT hper
  rw [setIntegral_const, smul_eq_mul] at hmono
  calc (∫ t in T, ∫ ω, Set.indicator (L t) (g t) ω ∂ν)
      ≤ (volume T).toReal * (K * ∫ ω, g 0 ω ∂ν) := hmono
    _ = (volume T).toReal * K * ∫ ω, g 0 ω ∂ν := by ring

/-- **A per-height lower bound integrates over `T`** --- the mirror of
`RMF.integral_indicator_le_of_per_height`. -/
theorem le_integral_indicator_of_per_height {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} [SFinite ν] {L : ℝ → Set Ω'} {g : ℝ → Ω' → ℝ}
    {T : Set ℝ} (hT : MeasurableSet T)
    (hTfin : volume T ≠ ⊤) {K : ℝ}
    (hInt : Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)))
    (hper : ∀ t ∈ T, K * (∫ ω, g 0 ω ∂ν) ≤ ∫ ω, Set.indicator (L t) (g t) ω ∂ν) :
    (volume T).toReal * K * ∫ ω, g 0 ω ∂ν
      ≤ ∫ t in T, ∫ ω, Set.indicator (L t) (g t) ω ∂ν := by
  have hconst : IntegrableOn (fun _ : ℝ => K * ∫ ω, g 0 ω ∂ν) T := integrableOn_const hTfin
  have hmono := setIntegral_mono_on hconst hInt.integral_prod_right hT hper
  rw [setIntegral_const, smul_eq_mul] at hmono
  calc (volume T).toReal * K * ∫ ω, g 0 ω ∂ν
      = (volume T).toReal * (K * ∫ ω, g 0 ω ∂ν) := by ring
    _ ≤ _ := hmono

/-- **The product integrability behind the `t`-integral.**  The uncurried indicator of `L t`
against `‖F(1/2+σ+it)‖²` is integrable on `Ω' × T`, as `integral_integral_swap` and
`setIntegral_mono_on` need.  `RMF.randomEulerProduct` is measurable in `ω` only a.e.; its closed
form holds on the unimodularity event, which does not depend on `t`, and so lifts to the product
through `Measure.ae_prod_iff_ae_ae`. -/
lemma integrable_uncurry_indicator_normSq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ0 : 0 < 1 / 2 + σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2})
    {T : Set ℝ} (hTfin : volume T ≠ ⊤) :
    Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) =>
        Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω)
      (ν.prod (volume.restrict T)) := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  have hsre : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; exact hσ0
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  -- the Euler product is a.e. the closed form, uniformly in `t`
  have hunit : ∀ᵐ q ∂(ν.prod (volume.restrict T)),
      ∀ p ∈ Nat.primesBelow y, ‖Y p q.1‖ ≤ 1 := by
    refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
    · have hrw : {q : Ω' × ℝ | ∀ p ∈ Nat.primesBelow y, ‖Y p q.1‖ ≤ 1}
          = ⋂ p ∈ Nat.primesBelow y, {q : Ω' × ℝ | ‖Y p q.1‖ ≤ 1} := by
        ext q
        simp
      rw [hrw]
      refine MeasurableSet.biInter (Finset.countable_toSet _) fun p hp => ?_
      exact measurableSet_le
        (((hY.measurable p (Nat.prime_of_mem_primesBelow hp)).comp measurable_fst).norm)
        measurable_const
    · filter_upwards [ae_forall_norm_le_one hY norm_le_one_steinhausLaw y] with ω hω
      exact Filter.Eventually.of_forall fun _ => hω
  have hclosed : (fun q : Ω' × ℝ => Set.indicator (L q.2) (g q.2) q.1)
      =ᵐ[ν.prod (volume.restrict T)] fun q : Ω' × ℝ => Set.indicator {q : Ω' × ℝ | q.1 ∈ L q.2}
        (fun q => ‖∏ p ∈ Nat.primesBelow y,
          (1 - Y p q.1 * ((p : ℂ)) ^ (-(shiftLine σ q.2)))⁻¹‖ ^ 2) q := by
    filter_upwards [hunit] with q hq
    by_cases hmem : q.1 ∈ L q.2
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (by exact hmem : q ∈ _)]
      change ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
        (shiftLine σ q.2) q.1‖ ^ 2 = _
      rw [randomEulerProduct_compMult_eq (hsre q.2) hq]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (by exact hmem : q ∉ _)]
  have hmeas' : Measurable fun q : Ω' × ℝ => Set.indicator {q : Ω' × ℝ | q.1 ∈ L q.2}
      (fun q => ‖∏ p ∈ Nat.primesBelow y,
        (1 - Y p q.1 * ((p : ℂ)) ^ (-(shiftLine σ q.2)))⁻¹‖ ^ 2) q := by
    refine (Measurable.indicator ?_ hSmeas)
    refine (Finset.measurable_prod _ fun p hp => ?_).norm.pow_const 2
    have h1 : Measurable fun q : Ω' × ℝ => Y p q.1 :=
      (hY.measurable p (Nat.prime_of_mem_primesBelow hp)).comp measurable_fst
    have h2 : Measurable fun q : Ω' × ℝ => ((p : ℂ)) ^ (-(shiftLine σ q.2)) :=
      ((continuous_cpow_neg_shiftLine (Nat.prime_of_mem_primesBelow hp).pos σ).measurable).comp
        measurable_snd
    exact ((h1.mul h2).const_sub 1).inv
  have hAEm : AEStronglyMeasurable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) :=
    (hmeas'.aestronglyMeasurable).congr hclosed.symm
  -- per-height integrability, and the uniform bound on the slice means
  have hslice : ∀ t : ℝ, Integrable (fun ω => Set.indicator (L t) (g t) ω) ν := fun t =>
    ((hf'.integrable_norm_randomEulerProduct_sq y (hsre t)).indicator (hLmeas t)).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hnn : ∀ t ω, 0 ≤ Set.indicator (L t) (g t) ω :=
    fun t ω => Set.indicator_nonneg (fun _ _ => by positivity) ω
  have hsliceval : ∀ t : ℝ, (∫ ω, ‖Set.indicator (L t) (g t) ω‖ ∂ν) ≤ ∫ ω, g 0 ω ∂ν := by
    intro t
    have hrw : (fun ω => ‖Set.indicator (L t) (g t) ω‖) = fun ω => Set.indicator (L t) (g t) ω :=
      funext fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ω)]
    rw [hrw, hf'.integral_normSq_shiftLine_eq y hσ0 0 t, integral_indicator (hLmeas t)]
    exact setIntegral_le_integral (hf'.integrable_norm_randomEulerProduct_sq y (hsre t))
      (Filter.Eventually.of_forall fun ω => by positivity)
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    refine (integrable_prod_iff' hAEm).2 ⟨Filter.Eventually.of_forall hslice, ?_⟩
    refine Integrable.mono' (integrable_const (∫ ω, g 0 ω ∂ν))
      (hAEm.norm.prod_swap).integral_prod_right' ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => by
      rw [Real.norm_eq_abs]; positivity)]
    exact hsliceval t
  exact hInt

/-- The `RMF.barrierEvent` instance of `RMF.integrable_uncurry_indicator_normSq`, which is what
the lower half of the join consumes. -/
lemma integrable_uncurry_indicator_barrier_normSq {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y n : ℕ) {ϑ σ : ℝ}
    (hσ0 : 0 < 1 / 2 + σ) (u v : ℕ → ℝ) {T : Set ℝ} (hTfin : volume T ≠ ⊤) :
    Integrable (Function.uncurry fun (ω : Ω') (t : ℝ) =>
        Set.indicator (barrierEvent
            (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
              localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) n u v)
          (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω)
      (ν.prod (volume.restrict T)) := by
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  exact integrable_uncurry_indicator_normSq hY y hσ0
    (fun t => barrierEvent (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) n u v)
    (fun t => measurableSet_barrierEvent (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hYm p)) _ _ _)
    (measurableSet_barrierEvent_uncurry hYm σ _ _ _ _) hTfin

/-! ### The upper half at a general tilt scale

The tilt satisfies `0 ≤ σ` and `|σ|\log x ≤ η ≤ E₀`, and the barrier slope is
`RMF.blockSlopeOf E₀ 125`; every constant may depend on `E₀`.  The joins do not see the tilt; it
enters through the barrier estimate and through the threshold `\log x ≥ 3(E₀+1)`, which gives
`|σ| ≤ 1/3`, hence `Re s > 0`. -/

/-- **The restricted mean from above at one height, at tilt scale `η ≤ E₀`.**  Needs `0 ≤ σ` and
`|σ|\log x ≤ η`; the barrier slope is `RMF.blockSlopeOf E₀ 125`. -/
theorem exists_setIntegral_restricted_normSq_le_of_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (D n₀ : ℕ) (x₀ a₀ A : ℝ), 4 ≤ D ∧ 0 < A ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x → |hf j| ≤ 10 * Real.log j) →
            (∫ ω in {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ)) (a + (j : ℝ) + hf j)},
                ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν)
              ≤ A * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - r))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  obtain ⟨D, n₀, x₀, a₀, A, hD, hA, H⟩ :=
    exists_const_freeStart_barrier_harper_le_of_le E₀ hE₀
  refine ⟨D, n₀, max x₀ (Real.exp (3 * (E₀ + 1))), a₀, A, hD, hA, ?_⟩
  intro Ω' _ Y ν hY x σ η a r s hf hx hres hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra hn₀ hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe3 : Real.exp (3 * (E₀ + 1)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe3
  have hL3 : 3 * (E₀ + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe3
  have hσb : |σ| ≤ 1 / 3 :=
    abs_le_one_third_of_mul_log_le (by linarith) (by linarith) hσ
  have hs : 0 < s.re := by
    rw [hres]
    have h := abs_le.1 hσb
    linarith [h.1]
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hXmeas : ∀ m, Measurable fun ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := fun m =>
    Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)
  have hAm : MeasurableSet {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
        ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ)) (a + (j : ℝ) + hf j)} :=
    measurableSet_freeStartBarrier hXmeas _ _ _ _
  have hprop := H Ω' Y ν hY x σ η a r s hf hxx₀ hres hσ0 hη0 hηE hσ ha ha1 hr1 hrn
    hra hn₀ hhf
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  rw [hf'.setIntegral_normSq_eq (⌊x⌋₊ + 1) hs hAm]
  exact mul_le_mul_of_nonneg_right hprop hZ0

/-- **The restricted mean from above over the heights, at tilt scale `η ≤ E₀`.**  Needs `0 ≤ σ`
and `|σ|\log x ≤ η`; the barrier slope is `RMF.blockSlopeOf E₀ 125`. -/
theorem exists_integral_restricted_normSq_le_of_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (D n₀ : ℕ) (x₀ a₀ A : ℝ), 4 ≤ D ∧ 0 < A ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - r →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, (∫ t in T, Set.indicator {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ)) (a + (j : ℝ) + hf j)}
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
              ≤ (volume T).toReal
                  * (A * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - r)))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  obtain ⟨D, n₀, x₀, a₀, A, hD, hA, H⟩ :=
    exists_setIntegral_restricted_normSq_le_of_le E₀ hE₀
  refine ⟨D, n₀, max x₀ (Real.exp (3 * (E₀ + 1))), a₀, A, hD, hA, ?_⟩
  intro Ω' _ Y ν hY x σ η a r T hf hx hσnn hη0 hηE hσ ha ha1 hr1 hrn hra hn₀ hT hTfin
    hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe3 : Real.exp (3 * (E₀ + 1)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe3
  have hL3 : 3 * (E₀ + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe3
  have hσb : |σ| ≤ 1 / 3 :=
    abs_le_one_third_of_mul_log_le (by linarith) (by linarith) hσ
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by
    have h := abs_le.1 hσb
    linarith [h.1]
  have hsre : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; exact hσ0
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set n : ℕ := harperBlockCount D x with hndef
  set L : ℝ → Set Ω' := fun t => {ω | ∀ j, r ≤ j → j ≤ n →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ)) (a + (j : ℝ) + hf j)} with hLdef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hLmeas : ∀ t, MeasurableSet (L t) := fun t =>
    measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hYm p)) _ _ _ _
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    rw [hLdef, hgdef]
    exact integrable_uncurry_indicator_normSq hY y hσ0
      (fun t => {ω | ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
          ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ)) (a + (j : ℝ) + hf j)})
      (fun t => measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
        (measurable_localLog _).comp (hYm p)) _ _ _ _)
      (measurableSet_freeStartBarrier_uncurry hYm σ _ _ _ _ _) hTfin
  rw [integral_integral_swap hInt]
  have hper : ∀ t ∈ T, (∫ ω, Set.indicator (L t) (g t) ω ∂ν)
      ≤ A * min 1 (a / Real.sqrt ((n : ℝ) - r)) * ∫ ω, g 0 ω ∂ν := by
    intro t _
    have h := H Ω' Y ν hY x σ η a r (shiftLine σ t) hf hxx₀ (re_shiftLine σ t) hσnn hη0
      hηE hσ ha ha1 hr1 hrn hra hn₀ hhf
    rw [hf'.integral_normSq_shiftLine_eq y hσ0 0 t, integral_indicator (hLmeas t)]
    exact h
  exact integral_indicator_le_of_per_height hT hTfin hInt hper

/-! ### Both halves with a drop

The barrier stops `d` blocks short, on `[1, n-d]` or `[r, n-d]`, and the tilt bound is
`η ≤ E₀ ≤ e^d`.  The drop lets `RMF.exists_const_proposition5_harper_of_top` keep the slope
`RMF.blockSlope 125`, so `α` and `A` do not depend on `d` or `E₀`; only `x₀` does.  The joins
themselves do not see the drop. -/
/-- **`RMF.exists_le_setIntegral_restricted_normSq_of_top` with the level left
free.**  Undoing the tilt turns Proposition 5's lower half into a bound on the restricted second
moment; it multiplies by `E‖F‖²` and touches neither the level nor the block offset. -/
theorem le_setIntegral_restricted_normSq_of_harper.{u} {D₀ : ℕ} {a₀ α A : ℝ}
    (H :
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
          |σ| * Real.log x ≤ η → a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ))
                ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - blockSlope 125 * j)
                      (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - blockSlope 125 * j)
                      (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ))) :
    ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (x σ η a : ℝ) (s : ℂ) (hf : ℕ → ℝ),
        x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
        |σ| * Real.log x ≤ η → a₀ ≤ a →
        (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
          α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))
              * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν
            ≤ ∫ ω in barrierEvent
                  (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                  (harperBlockCount D x - d)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j),
                ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  intro D hDD d E₀ hE₀ hEd
  obtain ⟨x₀, H⟩ := H D hDD d
  refine ⟨max x₀ (Real.exp (3 * (E₀ + 1))), ?_⟩
  intro Ω' _ Y ν hY x σ η a s hf hx hres hσ0 hη0 hηE hσ ha hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe3 : Real.exp (3 * (E₀ + 1)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe3
  have hL3 : 3 * (E₀ + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe3
  have hσb : |σ| ≤ 1 / 3 :=
    abs_le_one_third_of_mul_log_le (by linarith) (by linarith) hσ
  have hs : 0 < s.re := by
    rw [hres]
    have h := abs_le.1 hσb
    linarith [h.1]
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  -- the barrier event is measurable
  have hXmeas : ∀ m, Measurable fun ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := fun m =>
    Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)
  have hA : MeasurableSet (barrierEvent
      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
      (harperBlockCount D x - d)
      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)) :=
    measurableSet_barrierEvent hXmeas _ _ _
  -- Proposition 5, and the tilt's defining property
  have hprop :=
    (H Ω' Y ν hY x σ η a s hf hxx₀ hres hσ0 hη0 (le_trans hηE hEd) hσ ha hhf).1
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  rw [hf'.setIntegral_normSq_eq (⌊x⌋₊ + 1) hs hA]
  exact mul_le_mul_of_nonneg_right hprop hZ0

/-- **The restricted mean from below at one height, with a drop `d`.**  Needs `0 ≤ σ` and
`|σ|\log x ≤ η ≤ E₀ ≤ e^d`; the barrier runs on `[1, n - d]` at slope `RMF.blockSlope 125`, for
every `D ≥ D₀`, and only `x₀` depends on `D`, `d` and `E₀`. -/
theorem exists_le_setIntegral_restricted_normSq_of_top :
    ∃ (D₀ : ℕ) (a₀ α : ℝ), 4 ≤ D₀ ∧ 0 < α ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν
              ≤ ∫ ω in barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j),
                  ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  obtain ⟨D₀, a₀, α, A, hD, hα, hA, H⟩ := exists_const_proposition5_harper_of_top
  exact ⟨D₀, a₀, α, hD, hα,
    le_setIntegral_restricted_normSq_of_harper H⟩

/-- **`RMF.exists_le_integral_restricted_normSq_of_top` with the level left
free.**  Averaging the set-integral bound over the window `T` moves neither the level nor the
block offset: the bound is uniform in the line, so the `t`-integral only multiplies it by
`|T|`. -/
theorem le_integral_restricted_normSq_of_setIntegral.{u} {D₀ : ℕ} {a₀ α : ℝ}
    (H :
      ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν
              ≤ ∫ ω in barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j),
                  ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν) :
    ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
        x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → a₀ ≤ a →
        MeasurableSet T → volume T ≠ ⊤ →
        (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
          (volume T).toReal * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
              * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν
            ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                  (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                  (harperBlockCount D x - d)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν := by
  intro D hDD d E₀ hE₀ hEd
  obtain ⟨x₀, H⟩ := H D hDD d E₀ hE₀ hEd
  refine ⟨max x₀ (Real.exp (3 * (E₀ + 1))), ?_⟩
  intro Ω' _ Y ν hY x σ η a T hf hx hσnn hη0 hηE hσ ha hT hTfin hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe3 : Real.exp (3 * (E₀ + 1)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe3
  have hL3 : 3 * (E₀ + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe3
  have hσb : |σ| ≤ 1 / 3 :=
    abs_le_one_third_of_mul_log_le (by linarith) (by linarith) hσ
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by
    have h := abs_le.1 hσb
    linarith [h.1]
  have hsre : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; exact hσ0
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hTfin⟩
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set n : ℕ := harperBlockCount D x - d with hndef
  set L : ℝ → Set Ω' := fun t => barrierEvent
    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) n
    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j) with hLdef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hLmeas : ∀ t, MeasurableSet (L t) := fun t =>
    measurableSet_barrierEvent (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hYm p)) _ _ _
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    rw [hLdef, hgdef]
    exact integrable_uncurry_indicator_barrier_normSq hY y n hσ0 _ _ hTfin
  -- Tonelli, then the per-height bound
  rw [integral_integral_swap hInt]
  have hper : ∀ t ∈ T, α * min 1 (a / Real.sqrt n) * (∫ ω, g 0 ω ∂ν)
      ≤ ∫ ω, Set.indicator (L t) (g t) ω ∂ν := by
    intro t _
    have h := H Ω' Y ν hY x σ η a (shiftLine σ t) hf hxx₀ (re_shiftLine σ t) hσnn hη0
      hηE hσ ha hhf
    rw [hf'.integral_normSq_shiftLine_eq y hσ0 0 t, integral_indicator (hLmeas t)]
    exact h
  exact le_integral_indicator_of_per_height hT hTfin hInt hper

/-- **The restricted mean from below over the heights, with a drop `d`.**  Needs `0 ≤ σ` and
`|σ|\log x ≤ η ≤ E₀ ≤ e^d`; the barrier runs on `[1, n - d]` at slope `RMF.blockSlope 125`, for
every `D ≥ D₀`, and only `x₀` depends on `D`, `d` and `E₀`. -/
theorem exists_le_integral_restricted_normSq_of_top :
    ∃ (D₀ : ℕ) (a₀ α : ℝ), 4 ≤ D₀ ∧ 0 < α ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (volume T).toReal * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν := by
  obtain ⟨D₀, a₀, α, hD, hα, H⟩ := exists_le_setIntegral_restricted_normSq_of_top
  exact ⟨D₀, a₀, α, hD, hα,
    le_integral_restricted_normSq_of_setIntegral H⟩

/-- **The restricted mean from above at one height, with a drop `d`.**  Needs `0 ≤ σ`,
`|σ|\log x ≤ η ≤ E₀ ≤ e^d` and `2d ≤ n - r`; the free-start barrier runs on `[r, n - d]` at slope
`RMF.blockSlope 125`, and only `x₀` depends on `d` and `E₀`. -/
theorem exists_setIntegral_restricted_normSq_le_of_top :
    ∃ (D n₀ : ℕ) (a₀ A : ℝ), 4 ≤ D ∧ 0 < A ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          2 * d ≤ harperBlockCount D x - r → n₀ ≤ harperBlockCount D x - r - d →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω in {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ)) (a + (j : ℝ) + hf j)},
                ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν)
              ≤ A * min 1 (a / Real.sqrt ((((harperBlockCount D x - d : ℕ) : ℝ)) - r))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  obtain ⟨D, n₀, a₀, A, hD, hA, H⟩ := exists_const_freeStart_barrier_harper_le_of_top
  refine ⟨D, n₀, a₀, A, hD, hA, ?_⟩
  intro d E₀ hE₀ hEd
  obtain ⟨x₀, H⟩ := H d E₀ hE₀ hEd
  refine ⟨max x₀ (Real.exp (3 * (E₀ + 1))), ?_⟩
  intro Ω' _ Y ν hY x σ η a r s hf hx hres hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra hdn hn₀
    hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe3 : Real.exp (3 * (E₀ + 1)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe3
  have hL3 : 3 * (E₀ + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe3
  have hσb : |σ| ≤ 1 / 3 :=
    abs_le_one_third_of_mul_log_le (by linarith) (by linarith) hσ
  have hs : 0 < s.re := by
    rw [hres]
    have h := abs_le.1 hσb
    linarith [h.1]
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hXmeas : ∀ m, Measurable fun ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := fun m =>
    Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)
  have hAm : MeasurableSet {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
        ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ)) (a + (j : ℝ) + hf j)} :=
    measurableSet_freeStartBarrier hXmeas _ _ _ _
  have hprop := H Ω' Y ν hY x σ η a r s hf hxx₀ hres hσ0 hη0 hηE hσ ha ha1 hr1 hrn hra
    hdn hn₀ hhf
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  rw [hf'.setIntegral_normSq_eq (⌊x⌋₊ + 1) hs hAm]
  exact mul_le_mul_of_nonneg_right hprop hZ0

/-- **The restricted mean from above over the heights, with a drop `d`.**  Needs `0 ≤ σ`,
`|σ|\log x ≤ η ≤ E₀ ≤ e^d` and `2d ≤ n - r`; the free-start barrier runs on `[r, n - d]` at slope
`RMF.blockSlope 125`, and only `x₀` depends on `d` and `E₀`. -/
theorem exists_integral_restricted_normSq_le_of_top :
    ∃ (D n₀ : ℕ) (a₀ A : ℝ), 4 ≤ D ∧ 0 < A ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          2 * d ≤ harperBlockCount D x - r → n₀ ≤ harperBlockCount D x - r - d →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, (∫ t in T, Set.indicator {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ)) (a + (j : ℝ) + hf j)}
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
              ≤ (volume T).toReal
                  * (A * min 1 (a / Real.sqrt ((((harperBlockCount D x - d : ℕ) : ℝ)) - r)))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  obtain ⟨D, n₀, a₀, A, hD, hA, H⟩ := exists_setIntegral_restricted_normSq_le_of_top
  refine ⟨D, n₀, a₀, A, hD, hA, ?_⟩
  intro d E₀ hE₀ hEd
  obtain ⟨x₀, H⟩ := H d E₀ hE₀ hEd
  refine ⟨max x₀ (Real.exp (3 * (E₀ + 1))), ?_⟩
  intro Ω' _ Y ν hY x σ η a r T hf hx hσnn hη0 hηE hσ ha ha1 hr1 hrn hra hdn hn₀ hT
    hTfin hhf
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe3 : Real.exp (3 * (E₀ + 1)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe3
  have hL3 : 3 * (E₀ + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe3
  have hσb : |σ| ≤ 1 / 3 :=
    abs_le_one_third_of_mul_log_le (by linarith) (by linarith) hσ
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by
    have h := abs_le.1 hσb
    linarith [h.1]
  have hsre : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; exact hσ0
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set n : ℕ := harperBlockCount D x - d with hndef
  set L : ℝ → Set Ω' := fun t => {ω | ∀ j, r ≤ j → j ≤ n →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ)) (a + (j : ℝ) + hf j)} with hLdef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hLmeas : ∀ t, MeasurableSet (L t) := fun t =>
    measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hYm p)) _ _ _ _
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    rw [hLdef, hgdef]
    exact integrable_uncurry_indicator_normSq hY y hσ0
      (fun t => {ω | ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
          ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ)) (a + (j : ℝ) + hf j)})
      (fun t => measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
        (measurable_localLog _).comp (hYm p)) _ _ _ _)
      (measurableSet_freeStartBarrier_uncurry hYm σ _ _ _ _ _) hTfin
  rw [integral_integral_swap hInt]
  have hper : ∀ t ∈ T, (∫ ω, Set.indicator (L t) (g t) ω ∂ν)
      ≤ A * min 1 (a / Real.sqrt ((n : ℝ) - r)) * ∫ ω, g 0 ω ∂ν := by
    intro t _
    have h := H Ω' Y ν hY x σ η a r (shiftLine σ t) hf hxx₀ (re_shiftLine σ t) hσnn hη0
      hηE hσ ha ha1 hr1 hrn hra hdn hn₀ hhf
    rw [hf'.integral_normSq_shiftLine_eq y hσ0 0 t, integral_indicator (hLmeas t)]
    exact h
  exact integral_indicator_le_of_per_height hT hTfin hInt hper

end RMF
