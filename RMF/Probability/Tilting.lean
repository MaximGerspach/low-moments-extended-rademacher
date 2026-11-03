/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Independence.Integration

/-!
# Exponential tilting of an independent family

Harper's Girsanov-type argument tilts the law of a Steinhaus random multiplicative function by
`∏_{p ≤ y} |1 - f(p) p^{-1/2-σ}|^{-2}`: a product, over primes, of a function of the single value
`f p`.  Everything downstream rests on the tilt *factorising* — under the tilted measure the
`f p` are still independent, and the law of each is its own individual tilt.  Mathlib defines
`MeasureTheory.Measure.tilted`, but relates it neither to `ProbabilityTheory.iIndepFun` nor to
`MeasureTheory.Measure.map`, so this file supplies both.

## Main results

* `RMF.map_tilted_comp`: tilting commutes with pushing forward along a map that the tilt factors
  through, `(μ.tilted (f ∘ T)).map T = (μ.map T).tilted f`.
* `RMF.tilted_finsetSum_iInter_preimage`: the tilted measure of a rectangle factorises.
* `RMF.iIndepFun_tilted_finsetSum`: an independent family stays independent under a tilt by a
  finite sum of functions of its individual members.
* `RMF.map_tilted_finsetSum`: and the law of each member becomes its own tilt.

The tilt is indexed by a `Finset t`, not by all of `ι`.  That is what the application needs — the
tilt runs over the primes up to `x ^ (1 / e)` while the family runs over all primes — and it is
also what lets the file avoid product measures, which would force `ι` to be finite.

## Implementation notes

The normalisation is done factor by factor rather than globally: the density is written as
`∏ i ∈ t, exp (g i (X i ω)) / Z i` with `Z i = ∫ ω, exp (g i (X i ω)) ∂μ`, not as
`exp (∑ i ∈ t, g i (X i ω)) / Z`.  The two agree because `Z = ∏ i ∈ t, Z i`
(`RMF.integral_finsetProd_of_iIndepFun`), and the first form makes every factor outside the
rectangle integrate to exactly `1`.  So no `ℝ≥0∞` inverse ever appears inside a `Finset.prod`,
which is where the bookkeeping would otherwise become painful.
-/

namespace RMF

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Products of independent random variables

Two facts that Mathlib states only over a product measure with a `Fintype` index, or only for two
factors.  Both are needed below for a `Finset`-indexed family on an abstract space. -/

section Products

variable {Y : ι → Ω → ℝ}

/-- The expectation of a product of finitely many independent random variables is the product of
their expectations. -/
theorem integral_finsetProd_of_iIndepFun (hY : iIndepFun Y μ) (hYm : ∀ i, Measurable (Y i))
    (s : Finset ι) :
    ∫ ω, (∏ i ∈ s, Y i) ω ∂μ = ∏ i ∈ s, ∫ ω, Y i ω ∂μ := by
  have := hY.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
      rw [Finset.prod_cons, Finset.prod_cons, ← ih]
      exact ((hY.indepFun_finsetProd_of_notMem hYm hj).symm).integral_mul_eq_mul_integral
        (hYm j).aestronglyMeasurable
        (Finset.aestronglyMeasurable_prod _ fun i _ => (hYm i).aestronglyMeasurable)

end Products

/-! ### Tilting and pushforward -/

/-- **Tilting commutes with pushforward** when the tilt factors through the map:
`(ν.tilted (f ∘ T)).map T = (ν.map T).tilted f`.  Mathlib relates `Measure.tilted` to no other
measure operation, so this is proved from the definition. -/
theorem map_tilted_comp {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {ν : Measure α} {T : α → β} {f : β → ℝ} (hT : Measurable T) (hf : Measurable f) :
    (ν.tilted (f ∘ T)).map T = (ν.map T).tilted f := by
  have hZ : ∫ y, exp (f y) ∂ν.map T = ∫ x, exp (f (T x)) ∂ν :=
    integral_map hT.aemeasurable hf.exp.aestronglyMeasurable
  ext s hs
  rw [Measure.map_apply hT hs, tilted_apply' _ _ (hT hs), tilted_apply' _ _ hs, hZ,
    setLIntegral_map hs ((hf.exp.div_const _).ennreal_ofReal) hT]
  rfl

/-! ### The tilt of an independent family -/

section Tilt

variable [DecidableEq ι] {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : ∀ i, Ω → 𝓧 i}
  {g : ∀ i, 𝓧 i → ℝ} {t : Finset ι}

/-- **The tilted measure of a rectangle factorises.**  Tilting an independent family `X` by
`∑ i ∈ t, g i (X i ·)` leaves the coordinates independent, the `i`-th carrying its own tilt (and
no tilt at all when `i ∉ t`).  Every result below is read off from this computation. -/
theorem tilted_finsetSum_iInter_preimage (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (hgm : ∀ i, Measurable (g i))
    (hint : ∀ i ∈ t, Integrable (fun ω ↦ exp (g i (X i ω))) μ)
    (s : Finset ι) {A : ∀ i, Set (𝓧 i)} (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (μ.tilted fun ω ↦ ∑ i ∈ t, g i (X i ω)) (⋂ i ∈ s, X i ⁻¹' A i)
      = ∏ i ∈ s, (μ.tilted fun ω ↦ if i ∈ t then g i (X i ω) else 0) (X i ⁻¹' A i) := by
  have hprob := hX.isProbabilityMeasure
  -- The individual factors and their normalising constants.
  have hYm : ∀ i, Measurable (fun ω ↦ exp (g i (X i ω))) := fun i ↦ ((hgm i).comp (hXm i)).exp
  have hYindep : iIndepFun (fun i ω ↦ exp (g i (X i ω))) μ :=
    hX.comp (fun i x ↦ exp (g i x)) fun i ↦ (hgm i).exp
  have hZpos : ∀ i ∈ t, 0 < ∫ ω, exp (g i (X i ω)) ∂μ := fun i hi ↦ integral_exp_pos (hint i hi)
  -- The total normalisation is the product of the individual ones.
  have hZtot : (∫ ω, exp (∑ i ∈ t, g i (X i ω)) ∂μ) = ∏ i ∈ t, ∫ ω, exp (g i (X i ω)) ∂μ := by
    rw [← integral_finsetProd_of_iIndepFun hYindep hYm t]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    rw [Finset.prod_apply]
    exact Real.exp_sum t fun i ↦ g i (X i ω)
  -- The density, factor by factor, and the integrand of the rectangle.
  set d : ∀ i, 𝓧 i → ℝ≥0∞ := fun i x ↦
    ENNReal.ofReal (exp (g i x) / ∫ ω, exp (g i (X i ω)) ∂μ) with hd
  set h : ∀ i, 𝓧 i → ℝ≥0∞ := fun i x ↦
    (if i ∈ s then (A i).indicator 1 x else 1) * (if i ∈ t then d i x else 1) with hh
  have hdm : ∀ i, Measurable (d i) := fun i ↦ ((hgm i).exp.div_const _).ennreal_ofReal
  have hhm : ∀ i, Measurable (h i) := by
    intro i
    refine Measurable.mul ?_ ?_
    · split_ifs with hi
      · exact measurable_one.indicator (hA i hi)
      · exact measurable_const
    · split_ifs
      · exact hdm i
      · exact measurable_const
  have hmeasRect : MeasurableSet (⋂ i ∈ s, X i ⁻¹' A i) :=
    MeasurableSet.biInter s.countable_toSet fun i hi ↦ (hXm i) (hA i hi)
  -- Step 1: the rectangle's tilted measure is the integral of a product over `s ∪ t`.
  have hstep : ∀ ω, (⋂ i ∈ s, X i ⁻¹' A i).indicator
      (fun ω ↦ ENNReal.ofReal
        (exp (∑ i ∈ t, g i (X i ω)) / ∫ ω, exp (∑ i ∈ t, g i (X i ω)) ∂μ)) ω
      = ∏ i ∈ s ∪ t, h i (X i ω) := by
    intro ω
    have hone : (⋂ i ∈ s, X i ⁻¹' A i).indicator (1 : Ω → ℝ≥0∞) ω
        = ∏ i ∈ s, (A i).indicator (1 : 𝓧 i → ℝ≥0∞) (X i ω) := by
      by_cases hω : ∀ i ∈ s, X i ω ∈ A i
      · rw [Set.indicator_of_mem (by simpa using hω)]
        exact (Finset.prod_eq_one fun i hi ↦ Set.indicator_of_mem (hω i hi) _).symm
      · push Not at hω
        obtain ⟨i, his, hi⟩ := hω
        rw [Set.indicator_of_notMem (by simp only [Set.mem_iInter, not_forall]; exact ⟨i, his, hi⟩)]
        exact (Finset.prod_eq_zero his (Set.indicator_of_notMem hi _)).symm
    have hdens : ENNReal.ofReal
        (exp (∑ i ∈ t, g i (X i ω)) / ∫ ω, exp (∑ i ∈ t, g i (X i ω)) ∂μ)
        = ∏ i ∈ t, d i (X i ω) := by
      rw [hZtot, Real.exp_sum, ← Finset.prod_div_distrib,
        ENNReal.ofReal_prod_of_nonneg fun i hi ↦ le_of_lt (div_pos (exp_pos _) (hZpos i hi))]
    have hsplit : (∏ i ∈ s, (A i).indicator (1 : 𝓧 i → ℝ≥0∞) (X i ω)) * ∏ i ∈ t, d i (X i ω)
        = ∏ i ∈ s ∪ t, h i (X i ω) := by
      rw [hh, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
    calc _ = (⋂ i ∈ s, X i ⁻¹' A i).indicator (1 : Ω → ℝ≥0∞) ω
              * ENNReal.ofReal
                (exp (∑ i ∈ t, g i (X i ω)) / ∫ ω, exp (∑ i ∈ t, g i (X i ω)) ∂μ) := by
          by_cases hω : ω ∈ ⋂ i ∈ s, X i ⁻¹' A i <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      _ = _ := by rw [hone, hdens, hsplit]
  -- Step 2: independence turns that integral into a product of one-dimensional integrals.
  have hfactor : ∀ i, (∫⁻ ω, h i (X i ω) ∂μ)
      = if i ∈ s then (μ.tilted fun ω ↦ if i ∈ t then g i (X i ω) else 0) (X i ⁻¹' A i) else 1 := by
    intro i
    have hpre : ∀ ω, (A i).indicator (1 : 𝓧 i → ℝ≥0∞) (X i ω)
        = (X i ⁻¹' A i).indicator (1 : Ω → ℝ≥0∞) ω := by
      intro ω
      by_cases hω : X i ω ∈ A i <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω, Set.mem_preimage]
    by_cases his : i ∈ s <;> by_cases hit : i ∈ t
    · have hmeas : MeasurableSet (X i ⁻¹' A i) := (hXm i) (hA i his)
      rw [if_pos his]
      simp only [hh, if_pos his, if_pos hit]
      rw [tilted_apply' _ _ hmeas, ← lintegral_indicator hmeas]
      refine lintegral_congr fun ω ↦ ?_
      rw [hpre ω]
      by_cases hω : ω ∈ X i ⁻¹' A i <;>
        simp [hd, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
    · have hmeas : MeasurableSet (X i ⁻¹' A i) := (hXm i) (hA i his)
      rw [if_pos his]
      simp only [hh, if_pos his, if_neg hit, mul_one]
      rw [tilted_const μ 0]
      calc ∫⁻ ω, (A i).indicator (1 : 𝓧 i → ℝ≥0∞) (X i ω) ∂μ
          = ∫⁻ ω, (X i ⁻¹' A i).indicator (1 : Ω → ℝ≥0∞) ω ∂μ := lintegral_congr hpre
        _ = μ (X i ⁻¹' A i) := lintegral_indicator_one hmeas
    · have hone : (μ.tilted fun ω ↦ g i (X i ω)) Set.univ = 1 :=
        @IsProbabilityMeasure.measure_univ _ _ _ (isProbabilityMeasure_tilted (hint i hit))
      rw [if_neg his]
      simp only [hh, if_neg his, if_pos hit, one_mul]
      rw [← hone, tilted_apply' _ _ MeasurableSet.univ, ← setLIntegral_univ]
    · rw [if_neg his]
      simp only [hh, if_neg his, if_neg hit, one_mul]
      simp
  calc (μ.tilted fun ω ↦ ∑ i ∈ t, g i (X i ω)) (⋂ i ∈ s, X i ⁻¹' A i)
      = ∫⁻ ω, ∏ i ∈ s ∪ t, h i (X i ω) ∂μ := by
        rw [tilted_apply' _ _ hmeasRect, ← lintegral_indicator hmeasRect]
        exact lintegral_congr hstep
    _ = ∏ i ∈ s ∪ t, ∫⁻ ω, h i (X i ω) ∂μ :=
        lintegral_prod_eq_prod_lintegral_of_indepFun _ _
          (hX.comp h hhm) fun i ↦ (hhm i).comp (hXm i)
    _ = ∏ i ∈ s ∪ t,
          if i ∈ s then (μ.tilted fun ω ↦ if i ∈ t then g i (X i ω) else 0) (X i ⁻¹' A i) else 1 :=
        Finset.prod_congr rfl fun i _ ↦ hfactor i
    _ = _ := by rw [Finset.prod_ite_mem, Finset.union_inter_cancel_left]

omit [DecidableEq ι] in
/-- **An independent family stays independent under a tilt by a sum of functions of its individual
members.**  This is the Girsanov-type statement Harper's argument turns on, and the piece Mathlib
does not have: `Measure.tilted` is related there to no notion of independence at all. -/
theorem iIndepFun_tilted_finsetSum (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (hgm : ∀ i, Measurable (g i))
    (hint : ∀ i ∈ t, Integrable (fun ω ↦ exp (g i (X i ω))) μ) :
    iIndepFun X (μ.tilted fun ω ↦ ∑ i ∈ t, g i (X i ω)) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S A hA
  rw [tilted_finsetSum_iInter_preimage hX hXm hgm hint S hA]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hsingle := tilted_finsetSum_iInter_preimage hX hXm hgm hint {i} (A := A)
    fun j hj ↦ by rw [Finset.mem_singleton] at hj; exact hj ▸ hA i hi
  simpa using hsingle.symm

/-- **The law of each member under the tilt is its own tilt.**  For `i ∉ t` the law is unchanged,
which is what the `if` records. -/
theorem map_tilted_finsetSum (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (hgm : ∀ i, Measurable (g i))
    (hint : ∀ i ∈ t, Integrable (fun ω ↦ exp (g i (X i ω))) μ) (i : ι) :
    (μ.tilted fun ω ↦ ∑ j ∈ t, g j (X j ω)).map (X i)
      = (μ.map (X i)).tilted (if i ∈ t then g i else 0) := by
  have hgim : Measurable (if i ∈ t then g i else (0 : 𝓧 i → ℝ)) := by
    split_ifs
    · exact hgm i
    · exact measurable_const
  have hcomp : ((if i ∈ t then g i else (0 : 𝓧 i → ℝ)) ∘ X i)
      = fun ω ↦ if i ∈ t then g i (X i ω) else 0 := by
    funext ω
    simp only [Function.comp_apply]
    split_ifs <;> rfl
  ext A hA
  have hsingle := tilted_finsetSum_iInter_preimage hX hXm hgm hint {i}
    (A := Function.update (fun j ↦ (Set.univ : Set (𝓧 j))) i A)
    fun j hj ↦ by
      rw [Finset.mem_singleton] at hj
      subst hj
      rwa [Function.update_self]
  simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton,
    Function.update_self] at hsingle
  rw [Measure.map_apply (hXm i) hA, ← map_tilted_comp (hXm i) hgim,
    Measure.map_apply (hXm i) hA, hcomp]
  exact hsingle

omit [DecidableEq ι] in
/-- The law of a tilted coordinate, when that coordinate is one of the tilted ones. -/
theorem map_tilted_finsetSum_of_mem (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (hgm : ∀ i, Measurable (g i))
    (hint : ∀ i ∈ t, Integrable (fun ω ↦ exp (g i (X i ω))) μ) {i : ι} (hi : i ∈ t) :
    (μ.tilted fun ω ↦ ∑ j ∈ t, g j (X j ω)).map (X i) = (μ.map (X i)).tilted (g i) := by
  classical
  rw [map_tilted_finsetSum hX hXm hgm hint i, if_pos hi]

/-! ### A small tilt perturbs an expectation by little

The two-point block moments need the one-point tilted moments of `EulerProduct/TiltedLaw.lean`
against the **two-fold** tilt.  The second tilt is treated as a perturbation of the first, and
this is the estimate that makes that legitimate.

The identity behind it is `∫ f d(μ.tilted g) - ∫ f dμ = Cov_μ(e^g, f) / E_μ[e^g]`, so a tilt by a
*small* `g` moves any bounded expectation by `O(‖g‖_∞)`.  Nothing here is specific to the
Steinhaus law, which is why it is stated for an arbitrary probability measure. -/

/-- **Tilting by a small exponent perturbs a bounded expectation by little.**  If `|g| ≤ M ≤ 1` and
`|f| ≤ K` almost everywhere, then `|∫ f d(μ.tilted g) - ∫ f dμ| ≤ 4e M K`.  The `4` is `2 + 2`: one
`2` bounds `|e^g - 1|` by `2|g|`, the other bounds `|1 - E[e^g]|` the same way; the `e` is
`1/E[e^g] ≤ e^M ≤ e`. -/
theorem abs_integral_tilted_sub_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g f : Ω → ℝ} {M K : ℝ}
    (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hK0 : 0 ≤ K)
    (hgm : AEStronglyMeasurable g μ) (hfm : AEStronglyMeasurable f μ)
    (hg : ∀ᵐ ω ∂μ, |g ω| ≤ M) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ K) :
    |(∫ ω, f ω ∂(μ.tilted g)) - ∫ ω, f ω ∂μ| ≤ 4 * Real.exp 1 * M * K := by
  have hgem : AEStronglyMeasurable (fun ω => Real.exp (g ω)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hgm
  have hexpbd : ∀ᵐ ω ∂μ, ‖Real.exp (g ω)‖ ≤ Real.exp M := by
    filter_upwards [hg] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.2 (abs_le.1 hω).2
  have hiE : Integrable (fun ω => Real.exp (g ω)) μ :=
    (memLp_top_of_bound hgem (Real.exp M) hexpbd).integrable le_top
  have hiF : Integrable f μ :=
    (memLp_top_of_bound hfm K (by
      filter_upwards [hf] with ω hω
      rwa [Real.norm_eq_abs])).integrable le_top
  have hiEF : Integrable (fun ω => Real.exp (g ω) * f ω) μ :=
    (memLp_top_of_bound (hgem.mul hfm) (Real.exp M * K) (by
      filter_upwards [hexpbd, hf] with ω h1 h2
      change ‖Real.exp (g ω) * f ω‖ ≤ Real.exp M * K
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] at h1
      exact mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_nonneg _))).integrable le_top
  set Z : ℝ := ∫ ω, Real.exp (g ω) ∂μ with hZdef
  have hZlow : Real.exp (-M) ≤ Z := by
    have hconst : (∫ _ω : Ω, Real.exp (-M) ∂μ) = Real.exp (-M) := by simp
    rw [hZdef, ← hconst]
    refine integral_mono_ae (integrable_const _) hiE ?_
    filter_upwards [hg] with ω hω
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hω).1])
  have hZpos : (0 : ℝ) < Z := lt_of_lt_of_le (Real.exp_pos _) hZlow
  have hZone : |Z - 1| ≤ 2 * M := by
    have hone : (∫ _ω : Ω, (1 : ℝ) ∂μ) = 1 := by simp
    have hsub : Z - 1 = ∫ ω, (Real.exp (g ω) - 1) ∂μ := by
      rw [hZdef, integral_sub hiE (integrable_const _), hone]
    rw [hsub]
    have hbd : ∀ᵐ ω ∂μ, ‖Real.exp (g ω) - 1‖ ≤ 2 * M := by
      filter_upwards [hg] with ω hω
      rw [Real.norm_eq_abs]
      exact (Real.abs_exp_sub_one_le (by linarith)).trans (by linarith)
    simpa using norm_integral_le_of_norm_le_const (μ := μ) hbd
  have hdev : ∀ᵐ ω ∂μ, ‖(Real.exp (g ω) - Z) * f ω‖ ≤ 4 * M * K := by
    filter_upwards [hg, hf] with ω hgω hfω
    have h1 : |Real.exp (g ω) - 1| ≤ 2 * M :=
      (Real.abs_exp_sub_one_le (by linarith)).trans (by linarith)
    have h2 : |Real.exp (g ω) - Z| ≤ 4 * M := by
      rw [show Real.exp (g ω) - Z = (Real.exp (g ω) - 1) + (-(Z - 1)) from by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul h2 hfω (abs_nonneg _) (by linarith)).trans_eq (by ring)
  have hiP : Integrable (fun ω => (Real.exp (g ω) - Z) * f ω) μ :=
    (memLp_top_of_bound ((hgem.sub aestronglyMeasurable_const).mul hfm)
      (4 * M * K) hdev).integrable le_top
  -- the transfer, then the covariance form
  have h1 : (∫ ω, f ω ∂(μ.tilted g)) = Z⁻¹ * ∫ ω, Real.exp (g ω) * f ω ∂μ := by
    rw [integral_tilted, ← hZdef]
    have hpt : ∀ ω, (Real.exp (g ω) / Z) • f ω = Z⁻¹ * (Real.exp (g ω) * f ω) := by
      intro ω
      rw [smul_eq_mul, div_eq_inv_mul, mul_assoc]
    simp_rw [hpt]
    exact integral_const_mul _ _
  have h2 : (∫ ω, (Real.exp (g ω) - Z) * f ω ∂μ)
      = (∫ ω, Real.exp (g ω) * f ω ∂μ) - Z * ∫ ω, f ω ∂μ := by
    have hpt : ∀ ω, (Real.exp (g ω) - Z) * f ω = Real.exp (g ω) * f ω - Z * f ω := by
      intro ω
      ring
    simp_rw [hpt]
    rw [integral_sub hiEF (hiF.const_mul Z), integral_const_mul]
  have hsplit : (∫ ω, f ω ∂(μ.tilted g)) - ∫ ω, f ω ∂μ
      = Z⁻¹ * ∫ ω, (Real.exp (g ω) - Z) * f ω ∂μ := by
    rw [h1, h2, mul_sub, ← mul_assoc, inv_mul_cancel₀ hZpos.ne', one_mul]
  rw [hsplit, abs_mul, abs_of_nonneg (inv_nonneg.2 hZpos.le)]
  have hint : |∫ ω, (Real.exp (g ω) - Z) * f ω ∂μ| ≤ 4 * M * K := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ) hdev
  have hZinv : Z⁻¹ ≤ Real.exp 1 := by
    refine (inv_anti₀ (Real.exp_pos (-M)) hZlow).trans ?_
    rw [Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.2 hM1
  have hZi0 : (0 : ℝ) ≤ Z⁻¹ := inv_nonneg.2 hZpos.le
  have hMK : (0 : ℝ) ≤ 4 * M * K := by positivity
  calc Z⁻¹ * |∫ ω, (Real.exp (g ω) - Z) * f ω ∂μ| ≤ Real.exp 1 * (4 * M * K) :=
        mul_le_mul hZinv hint (abs_nonneg _) (Real.exp_pos 1).le
    _ = 4 * Real.exp 1 * M * K := by ring

end Tilt

end RMF
