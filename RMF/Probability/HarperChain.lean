/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ProbabilityResult2
import RMF.Analysis.SmoothIndicator
import RMF.Probability.ProductIndependence
import RMF.Probability.MatchingGaussian

/-!
# The chain to Proposition 5

This file carries Harper's §3.2 — his Lemma 3, Lemma 4, Probability Results 1 and 2, and
Proposition 5 — for an abstract family of real increments on an abstract measure space.

Every step from the per-window comparison to Proposition 5 is proved here.  Lemma 3's *analytic*
content — that the tilted law of a block increment is within `ε` of the Gaussian one on every
window — enters as the hypothesis `IsWindowComparison`, which keeps this file independent of how
it is proved.

It is supplied for the Steinhaus tilt in `RMF/Probability/BlockComparison.lean`:
`RMF.exists_isWindowComparison_steinhaus_of_le` and its variants discharge it, and
`RMF.exists_const_proposition5_steinhaus_of_le` and its variants carry the chain through to the
random multiplicative function.  The arithmetic — the block offset and the envelope — is
`RMF.blockOffsetThreshold` and `RMF.envelope_of_le`.

The Steinhaus specifics — that the increments are the block log-moduli
`log‖I_j(1/2+σ+it_j)‖` and that the measure is the tilt — enter only when Proposition 5 is
instantiated, and none of the probabilistic content depends on them.

## Conventions

**The walk index runs from `0`.**  `RMF.walk X j = ∑_{m < j} X m`, so `walk X 0 = 0` carries no
constraint and Harper's `1 ≤ j ≤ n` becomes `j ∈ Icc 1 n`.  The increments are indexed `0, …, n-1`.

**Windows are half-open.**  `RMF.sliceEvent` uses `Ioc (c m) (c m + w m)`, so distinct integer
grid points give *genuinely* disjoint slices.  Harper's are closed, which would need the tilted
law of each increment to be atomless — true, but never proved in the paper, and the `± 2` slack
absorbs the difference.

**The comparison is stated as a relation between two measures on two spaces.**  Lemma 3 compares
the tilted law of the increments with a Gaussian law; there is no reason for these to live on one
space, and forcing them to would drag in a coupling that nothing needs.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ### The two events -/

/-- **The barrier event**: the partial sums stay between `u j` and `v j` for `1 ≤ j ≤ n`. -/
def barrierEvent (X : ℕ → Ω → ℝ) (n : ℕ) (u v : ℕ → ℝ) : Set Ω :=
  {ω | ∀ j, 1 ≤ j → j ≤ n → walk X j ω ∈ Set.Icc (u j) (v j)}

/-- **The slice**: increment `m` lies in the window of width `w m` with left endpoint `c m`, for
every `m < n`.  Half-open, so distinct grid points give disjoint slices. -/
def sliceEvent (X : ℕ → Ω → ℝ) (w : ℕ → ℝ) (n : ℕ) (c : ℕ → ℝ) : Set Ω :=
  {ω | ∀ m, m < n → X m ω ∈ Set.Ioc (c m) (c m + w m)}

lemma measurable_walk_of {X : ℕ → Ω → ℝ} (hX : ∀ m, Measurable (X m)) (j : ℕ) :
    Measurable (walk X j) := by
  rw [funext (walk_apply X j)]
  exact Finset.measurable_sum _ fun m _ => hX m

lemma measurableSet_barrierEvent {X : ℕ → Ω → ℝ} (hX : ∀ m, Measurable (X m)) (n : ℕ)
    (u v : ℕ → ℝ) : MeasurableSet (barrierEvent X n u v) := by
  have hrw : barrierEvent X n u v
      = ⋂ j ∈ Set.Icc 1 n, (walk X j) ⁻¹' (Set.Icc (u j) (v j)) := by
    ext ω
    simp only [barrierEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    (measurable_walk_of hX j) measurableSet_Icc

omit [MeasurableSpace Ω] in
/-- **The barrier event is monotone in its tube**: raising the floor or lowering the ceiling can
only remove paths. -/
lemma barrierEvent_mono {X : ℕ → Ω → ℝ} {n : ℕ} {u v u' v' : ℕ → ℝ}
    (hu : ∀ j, 1 ≤ j → j ≤ n → u j ≤ u' j) (hv : ∀ j, 1 ≤ j → j ≤ n → v' j ≤ v j) :
    barrierEvent X n u' v' ⊆ barrierEvent X n u v := by
  intro ω hω j hj1 hjn
  have h := Set.mem_Icc.1 (hω j hj1 hjn)
  exact Set.mem_Icc.2 ⟨le_trans (hu j hj1 hjn) h.1, le_trans h.2 (hv j hj1 hjn)⟩

lemma measurableSet_sliceEvent {X : ℕ → Ω → ℝ} (hX : ∀ m, Measurable (X m)) (w : ℕ → ℝ) (n : ℕ)
    (c : ℕ → ℝ) : MeasurableSet (sliceEvent X w n c) := by
  have hrw : sliceEvent X w n c
      = ⋂ m ∈ Set.Iio n, (X m) ⁻¹' (Set.Ioc (c m) (c m + w m)) := by
    ext ω
    simp only [sliceEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iio]
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun m _ => (hX m) measurableSet_Ioc

/-! ### Lemma 3 — the per-window comparison

Harper's Lemma 3: for window left-endpoints `c m` confined by the envelope `M`, the tilted law of
the increments and the Gaussian law assign the same mass to a window tuple, up to a relative error
`ε`.  Lean's increment `m` is Harper's block `m+1` (his are 1-indexed), so in his application
`w m = 1/(m+1)^2`, `M m = (1/40)√(log x_{m+1}) + 2` and `ε m = x_{m+1}^{-1/100}`, compounding to
`x_1^{-1/100}`.

This is stated as a *hypothesis shape*, because Lemma 4 consumes it as one and everything below
is independent of how it is proved — by Esseen smoothing or by Lindeberg replacement.
-/

/-- **Lemma 3's conclusion**, as a relation between two laws: for every tuple `c` with
`|c m| ≤ M m` for `m < n`, `(1-ε)·Q(N ∈ S_c) ≤ P(X ∈ S_c) ≤ (1+ε)·Q(N ∈ S_c)`, where `X ∈ S_c`
means `X m ∈ (c m, c m + w m]` for every `m < n` (`RMF.sliceEvent`). -/
def IsWindowComparison (P : Measure Ω) (Q : Measure Ω') (X : ℕ → Ω → ℝ) (N : ℕ → Ω' → ℝ)
    (w M : ℕ → ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ c : ℕ → ℝ, (∀ m, m < n → |c m| ≤ M m) →
    (1 - ε) * (Q (sliceEvent N w n c)).toReal ≤ (P (sliceEvent X w n c)).toReal ∧
      (P (sliceEvent X w n c)).toReal ≤ (1 + ε) * (Q (sliceEvent N w n c)).toReal

/-- **The empty comparison.**  Over no blocks both slice events are the whole space, so the
comparison holds for any `ε ≥ 0`.  This is the case `n ≤ ⌊a⌋` of the comparison hypothesis of
`RMF.proposition5_upper`, where the suffix it restarts on is empty. -/
lemma isWindowComparison_zero {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (X : ℕ → Ω → ℝ) (N : ℕ → Ω' → ℝ) (w M : ℕ → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) : IsWindowComparison P Q X N w M 0 ε := by
  intro c _
  have hXu : sliceEvent X w 0 c = Set.univ := by
    ext ω
    simp [sliceEvent]
  have hNu : sliceEvent N w 0 c = Set.univ := by
    ext ω
    simp [sliceEvent]
  rw [hXu, hNu, measure_univ, measure_univ, ENNReal.toReal_one]
  constructor <;> linarith

/-- Lemma 3's **per-coordinate** content: for every `c` with `|c| ≤ M`,
`(1-ε)·Q(N ∈ (c, c+w]) ≤ P(X ∈ (c, c+w]) ≤ (1+ε)·Q(N ∈ (c, c+w])`.  This is where the Gaussian
comparison happens; the rest of Lemma 3 is the factorisation below. -/
def IsWindowComparison₁ (P : Measure Ω) (Q : Measure Ω') (X : Ω → ℝ) (N : Ω' → ℝ)
    (w M ε : ℝ) : Prop :=
  ∀ c : ℝ, |c| ≤ M →
    (1 - ε) * (Q {ω | N ω ∈ Set.Ioc c (c + w)}).toReal
        ≤ (P {ω | X ω ∈ Set.Ioc c (c + w)}).toReal ∧
      (P {ω | X ω ∈ Set.Ioc c (c + w)}).toReal
        ≤ (1 + ε) * (Q {ω | N ω ∈ Set.Ioc c (c + w)}).toReal

/-! ### Lemma 3's analytic half, reduced to its three inputs

`IsWindowComparison₁` is a *multiplicative* comparison, and a Lindeberg swap delivers an *additive*
one.  The reduction between them is a three-step move:

* sandwich the indicator between two `C³` windows, `φ⁻ ≤ 1_(c,c+w] ≤ φ⁺`;
* swap each of them, paying an additive `D`;
* pay the *collar* — the mass the Gaussian puts within `δ` of an endpoint — for the gap
  `φ⁺ - φ⁻ ≤ 1_collar`, then divide by a lower bound `q` on the window's own Gaussian mass.

The theorem below takes `D`, `K`, `q` as hypotheses.  They come from the telescope of
`RMF/Analysis/Lindeberg.lean` against the block moments of `RMF/EulerProduct/TiltedMoments.lean`
(`D`), from `RMF.le_measure_Icc_gaussianReal_normalised_of_bounds` (`q`), and from
`RMF.measure_Icc_gaussianReal_le` and `RMF.measure_collar_gaussianReal_le` (`K`). -/

private lemma integrable_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a)
    (h1 : ∀ a, f a ≤ 1) : Integrable f μ := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable ?_
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 a)]
  exact h1 a

private lemma indicator_unit_nonneg {E : Type*} (S : Set E) (x : E) :
    0 ≤ S.indicator (1 : E → ℝ) x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

private lemma indicator_unit_le_one {E : Type*} (S : Set E) (x : E) :
    S.indicator (1 : E → ℝ) x ≤ 1 := by
  by_cases h : x ∈ S <;> simp [Set.indicator, h]

private lemma indicator_unit_comp {α E : Type*} (f : α → E) (S : Set E) :
    (fun a => S.indicator (1 : E → ℝ) (f a)) = (f ⁻¹' S).indicator (1 : α → ℝ) := by
  funext a
  by_cases h : f a ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun hm => h (Set.mem_preimage.mp hm)]

private lemma measurable_indicator_unit {E : Type*} [MeasurableSpace E] {S : Set E}
    (hS : MeasurableSet S) : Measurable (S.indicator (1 : E → ℝ)) :=
  measurable_const.indicator hS

/-! ### The swap-to-comparison bridge, in any dimension

The next theorem is the one-dimensional case of this, and the two-point argument needs the same
step for a *pair* on a box.  Nothing in the argument is one-dimensional: it is the sandwich
`φ⁻ ≤ 1_I ≤ φ⁺`, the collar `φ⁺ - φ⁻ ≤ 1_{Cl}`, an additive swap on each of `φ⁺` and `φ⁻`, and
one division by `q`.  Stating it once over an arbitrary measurable target avoids proving it
twice, and makes plain that the two-point case adds nothing but a different sandwich. -/

/-- **From an additive swap bound to a multiplicative comparison**, over any measurable target.

`RMF.isWindowComparison₁_of_swap` is this at `E = ℝ` with the smoothed interval indicators;
`RMF.le_measure_box_of_swap` is it at `E = ℝ × ℝ` with their products. -/
theorem le_measure_of_swap_sandwich {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {E : Type*} [MeasurableSpace E] {X : Ω → E} {N : Ω' → E}
    (hX : Measurable X) (hN : Measurable N) {φu φl : E → ℝ} {I Cl : Set E} {D K q ε : ℝ}
    (hI : MeasurableSet I) (hCl : MeasurableSet Cl)
    (hφum : Measurable φu) (hφlm : Measurable φl)
    (hφu0 : ∀ z, 0 ≤ φu z) (hφu1 : ∀ z, φu z ≤ 1)
    (hφl0 : ∀ z, 0 ≤ φl z) (hφl1 : ∀ z, φl z ≤ 1)
    (hsandL : ∀ z, φl z ≤ I.indicator (1 : E → ℝ) z)
    (hsandU : ∀ z, I.indicator (1 : E → ℝ) z ≤ φu z)
    (hcol : ∀ z, φu z - φl z ≤ Cl.indicator (1 : E → ℝ) z)
    (hswapU : |(∫ ω, φu (X ω) ∂P) - ∫ ω, φu (N ω) ∂Q| ≤ D)
    (hswapL : |(∫ ω, φl (X ω) ∂P) - ∫ ω, φl (N ω) ∂Q| ≤ D)
    (hcollar : (Q (N ⁻¹' Cl)).toReal ≤ K)
    (hq : 0 < q) (hqlow : q ≤ (Q (N ⁻¹' I)).toReal) (hεq : D + K ≤ ε * q) :
    (1 - ε) * (Q (N ⁻¹' I)).toReal ≤ (P (X ⁻¹' I)).toReal
      ∧ (P (X ⁻¹' I)).toReal ≤ (1 + ε) * (Q (N ⁻¹' I)).toReal := by
  have iPu : Integrable (fun ω => φu (X ω)) P :=
    integrable_of_le_one (hφum.comp hX) (fun _ => hφu0 _) (fun _ => hφu1 _)
  have iPl : Integrable (fun ω => φl (X ω)) P :=
    integrable_of_le_one (hφlm.comp hX) (fun _ => hφl0 _) (fun _ => hφl1 _)
  have iQu : Integrable (fun ω => φu (N ω)) Q :=
    integrable_of_le_one (hφum.comp hN) (fun _ => hφu0 _) (fun _ => hφu1 _)
  have iQl : Integrable (fun ω => φl (N ω)) Q :=
    integrable_of_le_one (hφlm.comp hN) (fun _ => hφl0 _) (fun _ => hφl1 _)
  have iPI : Integrable (fun ω => I.indicator (1 : E → ℝ) (X ω)) P :=
    integrable_of_le_one ((measurable_indicator_unit hI).comp hX)
      (fun _ => indicator_unit_nonneg _ _) (fun _ => indicator_unit_le_one _ _)
  have iQI : Integrable (fun ω => I.indicator (1 : E → ℝ) (N ω)) Q :=
    integrable_of_le_one ((measurable_indicator_unit hI).comp hN)
      (fun _ => indicator_unit_nonneg _ _) (fun _ => indicator_unit_le_one _ _)
  have iQC : Integrable (fun ω => Cl.indicator (1 : E → ℝ) (N ω)) Q :=
    integrable_of_le_one ((measurable_indicator_unit hCl).comp hN)
      (fun _ => indicator_unit_nonneg _ _) (fun _ => indicator_unit_le_one _ _)
  have hindP : (∫ ω, I.indicator (1 : E → ℝ) (X ω) ∂P) = (P (X ⁻¹' I)).toReal := by
    rw [indicator_unit_comp X I, integral_indicator_one (hX hI)]
    rfl
  have hindQI : (∫ ω, I.indicator (1 : E → ℝ) (N ω) ∂Q) = (Q (N ⁻¹' I)).toReal := by
    rw [indicator_unit_comp N I, integral_indicator_one (hN hI)]
    rfl
  have hindQC : (∫ ω, Cl.indicator (1 : E → ℝ) (N ω) ∂Q) = (Q (N ⁻¹' Cl)).toReal := by
    rw [indicator_unit_comp N Cl, integral_indicator_one (hN hCl)]
    rfl
  have hPl : (∫ ω, φl (X ω) ∂P) ≤ (P (X ⁻¹' I)).toReal := by
    rw [← hindP]
    exact integral_mono iPl iPI fun ω => hsandL (X ω)
  have hPu : (P (X ⁻¹' I)).toReal ≤ ∫ ω, φu (X ω) ∂P := by
    rw [← hindP]
    exact integral_mono iPI iPu fun ω => hsandU (X ω)
  have hQu : (∫ ω, φu (N ω) ∂Q) ≤ (Q (N ⁻¹' I)).toReal + (Q (N ⁻¹' Cl)).toReal := by
    rw [← hindQI, ← hindQC, ← integral_add iQI iQC]
    refine integral_mono iQu (iQI.add iQC) fun ω => ?_
    linarith [hsandL (N ω), hcol (N ω)]
  have hQl : (Q (N ⁻¹' I)).toReal - (Q (N ⁻¹' Cl)).toReal ≤ ∫ ω, φl (N ω) ∂Q := by
    rw [← hindQI, ← hindQC, ← integral_sub iQI iQC]
    refine integral_mono (iQI.sub iQC) iQl fun ω => ?_
    linarith [hsandU (N ω), hcol (N ω)]
  have hDU := abs_le.mp hswapU
  have hDL := abs_le.mp hswapL
  have hK0 : 0 ≤ K := le_trans ENNReal.toReal_nonneg hcollar
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hswapU
  have hε0 : 0 ≤ ε := nonneg_of_mul_nonneg_right (by linarith) hq
  have hshift : 0 ≤ ε * ((Q (N ⁻¹' I)).toReal - q) := mul_nonneg hε0 (sub_nonneg.mpr hqlow)
  refine ⟨?_, ?_⟩
  · nlinarith [hQl, hDL.1, hPl, hcollar, hqlow, hshift]
  · nlinarith [hQu, hDU.2, hPu, hcollar, hqlow, hshift]

/-- **From an additive swap bound to a multiplicative window comparison.**  `D` bounds the swap
error on both smoothed windows, `K` the Gaussian mass of the `δ`-collars of the two endpoints, and
`q` the Gaussian window mass from below; then `D + K ≤ εq` gives the comparison with error `ε`, at
the half-open window (`φ⁻` vanishes at its left endpoint).  `δ` enters `D` and `K` with opposite
signs and is left to the caller: `RMF.isWindowComparison₁_of_gaussian_family_of_third_moment`
chooses it. -/
theorem isWindowComparison₁_of_swap {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : Ω → ℝ} {N : Ω' → ℝ}
    (hX : Measurable X) (hN : Measurable N) {δ w M ε D K q : ℝ} (hδ : 0 < δ) (hq : 0 < q)
    (hswapU : ∀ c, |c| ≤ M →
      |(∫ ω, smoothIndicatorUpper δ c (c + w) (X ω) ∂P)
        - ∫ ω, smoothIndicatorUpper δ c (c + w) (N ω) ∂Q| ≤ D)
    (hswapL : ∀ c, |c| ≤ M →
      |(∫ ω, smoothIndicatorLower δ c (c + w) (X ω) ∂P)
        - ∫ ω, smoothIndicatorLower δ c (c + w) (N ω) ∂Q| ≤ D)
    (hcollar : ∀ c, |c| ≤ M →
      (Q (N ⁻¹' (Set.Icc (c - δ) (c + δ) ∪ Set.Icc (c + w - δ) (c + w + δ)))).toReal ≤ K)
    (hlow : ∀ c, |c| ≤ M → q ≤ (Q (N ⁻¹' Set.Ioc c (c + w))).toReal) (hεq : D + K ≤ ε * q) :
    IsWindowComparison₁ P Q X N w M ε := by
  intro c hc
  exact le_measure_of_swap_sandwich hX hN measurableSet_Ioc
    (measurableSet_Icc.union measurableSet_Icc)
    (contDiff_smoothIndicatorUpper δ c (c + w)).continuous.measurable
    (contDiff_smoothIndicatorLower δ c (c + w)).continuous.measurable
    (fun _ => window_nonneg _ _ _ _) (fun _ => smoothIndicatorUpper_le_one _ _ _ _)
    (fun _ => smoothIndicatorLower_nonneg _ _ _ _) (fun _ => window_le_one _ _ _ _)
    (fun z => smoothIndicatorLower_le_indicator_Ioc hδ z)
    (fun z => indicator_Ioc_le_smoothIndicatorUpper hδ z)
    (fun z => smoothIndicatorUpper_sub_lower_le_indicator hδ z)
    (hswapU c hc) (hswapL c hc) (hcollar c hc) hq (hlow c hc) hεq

/-! ### The box comparison

The two-dimensional instance.  Everything that is new is the sandwich — the product windows of
`RMF/Analysis/SmoothIndicator.lean` — and the collar, which is the union `Cl₁×ℝ ∪ ℝ×Cl₂` rather
than a pair of intervals.  The bridge itself is the same theorem. -/

/-- **From an additive swap bound to a multiplicative box comparison** — the multiplicative half
of Lemma 7, and the two-dimensional instance of `RMF.le_measure_of_swap_sandwich`.  `D` bounds the
swap error on both product windows (`RMF.abs_integral_window_pair_sum_sub_le`), `K` the Gaussian
pair's mass on the collar of the box, and `q` the pair's box mass from below
(`RMF.le_measure_box_shifted`).  At Harper's data `q` is `RMF.blockQ₂ = w²/8 · x^{-1/64}` and the
numerical condition is `RMF.blockNum₂_le`. -/
theorem le_measure_box_of_swap {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : Ω → ℝ × ℝ} {N : Ω' → ℝ × ℝ}
    (hX : Measurable X) (hN : Measurable N)
    {δ u₁ v₁ u₂ v₂ D K q ε : ℝ} (hδ : 0 < δ)
    (hswapU : |(∫ ω, smoothIndicatorUpper δ u₁ v₁ (X ω).1
            * smoothIndicatorUpper δ u₂ v₂ (X ω).2 ∂P)
          - ∫ ω, smoothIndicatorUpper δ u₁ v₁ (N ω).1
            * smoothIndicatorUpper δ u₂ v₂ (N ω).2 ∂Q| ≤ D)
    (hswapL : |(∫ ω, smoothIndicatorLower δ u₁ v₁ (X ω).1
            * smoothIndicatorLower δ u₂ v₂ (X ω).2 ∂P)
          - ∫ ω, smoothIndicatorLower δ u₁ v₁ (N ω).1
            * smoothIndicatorLower δ u₂ v₂ (N ω).2 ∂Q| ≤ D)
    (hcollar : (Q (N ⁻¹' (smoothCollar δ u₁ v₁ ×ˢ (Set.univ : Set ℝ)
        ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar δ u₂ v₂))).toReal ≤ K)
    (hq : 0 < q)
    (hqlow : q ≤ (Q (N ⁻¹' (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂))).toReal)
    (hεq : D + K ≤ ε * q) :
    (1 - ε) * (Q (N ⁻¹' (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂))).toReal
        ≤ (P (X ⁻¹' (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂))).toReal
      ∧ (P (X ⁻¹' (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂))).toReal
        ≤ (1 + ε) * (Q (N ⁻¹' (Set.Ioc u₁ v₁ ×ˢ Set.Ioc u₂ v₂))).toReal := by
  have hm₁ : Measurable (smoothIndicatorUpper δ u₁ v₁) :=
    (contDiff_smoothIndicatorUpper δ u₁ v₁).continuous.measurable
  have hm₂ : Measurable (smoothIndicatorUpper δ u₂ v₂) :=
    (contDiff_smoothIndicatorUpper δ u₂ v₂).continuous.measurable
  have hn₁ : Measurable (smoothIndicatorLower δ u₁ v₁) :=
    (contDiff_smoothIndicatorLower δ u₁ v₁).continuous.measurable
  have hn₂ : Measurable (smoothIndicatorLower δ u₂ v₂) :=
    (contDiff_smoothIndicatorLower δ u₂ v₂).continuous.measurable
  have hCl₁ : MeasurableSet (smoothCollar δ u₁ v₁) := measurableSet_Icc.union measurableSet_Icc
  have hCl₂ : MeasurableSet (smoothCollar δ u₂ v₂) := measurableSet_Icc.union measurableSet_Icc
  refine le_measure_of_swap_sandwich hX hN (measurableSet_Ioc.prod measurableSet_Ioc)
    ((hCl₁.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hCl₂))
    ((hm₁.comp measurable_fst).mul (hm₂.comp measurable_snd))
    ((hn₁.comp measurable_fst).mul (hn₂.comp measurable_snd))
    (fun z => mul_nonneg (window_nonneg _ _ _ _) (window_nonneg _ _ _ _)) (fun z => ?_)
    (fun z => mul_nonneg (smoothIndicatorLower_nonneg _ _ _ _)
      (smoothIndicatorLower_nonneg _ _ _ _)) (fun z => ?_)
    (fun z => prod_smoothIndicatorLower_le_indicator hδ z)
    (fun z => indicator_le_prod_smoothIndicatorUpper hδ z)
    (fun z => prod_smoothIndicatorUpper_sub_lower_le_indicator hδ z)
    hswapU hswapL hcollar hq hqlow hεq
  · calc smoothIndicatorUpper δ u₁ v₁ z.1 * smoothIndicatorUpper δ u₂ v₂ z.2 ≤ 1 * 1 :=
          mul_le_mul (smoothIndicatorUpper_le_one _ _ _ _)
            (smoothIndicatorUpper_le_one _ _ _ _) (window_nonneg _ _ _ _) zero_le_one
      _ = 1 := one_mul 1
  · calc smoothIndicatorLower δ u₁ v₁ z.1 * smoothIndicatorLower δ u₂ v₂ z.2 ≤ 1 * 1 :=
          mul_le_mul (window_le_one _ _ _ _) (window_le_one _ _ _ _)
            (smoothIndicatorLower_nonneg _ _ _ _) zero_le_one
      _ = 1 := one_mul 1

/-! ### Lemma 3 for a block, assembled

Everything above and in `ProductIndependence.lean`, `MatchingGaussian.lean` and
`SmoothIndicator.lean` combines into a single statement: an independent family compared with an
independent Gaussian family of the same first two moments satisfies the window comparison, with
`ε` determined by the third moments, the smoothing width, and the Gaussian's own window mass. -/

/-- The window carries three derivatives, so it is admissible for the swap. -/
private lemma window_hasDerivAt_chain (δ a b : ℝ) :
    (∀ x, HasDerivAt (window δ a b) (deriv (window δ a b) x) x) ∧
      (∀ x, HasDerivAt (deriv (window δ a b)) (deriv (deriv (window δ a b)) x) x) ∧
      (∀ x, HasDerivAt (deriv (deriv (window δ a b)))
        (deriv (deriv (deriv (window δ a b))) x) x) :=
  ⟨fun x => (hasDerivAt_window δ a b x).differentiableAt.hasDerivAt,
   fun x => (hasDerivAt_deriv_window δ a b x).differentiableAt.hasDerivAt,
   fun x => (hasDerivAt_deriv2_window δ a b x).differentiableAt.hasDerivAt⟩

/-- **The swap against a window.**  The `M₃` of the telescope is `450/δ³`. -/
theorem abs_integral_window_sum_sub_le {ι : Type*} {s : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ξ : ι → Ω → ℝ} {G : ι → Ω' → ℝ}
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    (hξ₁ : ∀ i ∈ s, Integrable (ξ i) P)
    (hξ₂ : ∀ i ∈ s, Integrable (fun ω => ξ i ω * ξ i ω) P)
    (hG₁ : ∀ i ∈ s, Integrable (G i) Q)
    (hG₂ : ∀ i ∈ s, Integrable (fun ω => G i ω * G i ω) Q)
    (hm₁ : ∀ i ∈ s, ∫ ω, ξ i ω ∂P = ∫ ω, G i ω ∂Q)
    (hm₂ : ∀ i ∈ s, ∫ ω, ξ i ω * ξ i ω ∂P = ∫ ω, G i ω * G i ω ∂Q)
    (hTξ : ∀ i ∈ s, Integrable (fun ω => |ξ i ω| ^ 3) P)
    (hTG : ∀ i ∈ s, Integrable (fun ω => |G i ω| ^ 3) Q)
    {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    |(∫ ω, window δ a b (∑ i ∈ s, ξ i ω) ∂P)
        - ∫ ω, window δ a b (∑ i ∈ s, G i ω) ∂Q|
      ≤ 450 / δ ^ 3 * ∑ i ∈ s, ((∫ ω, |ξ i ω| ^ 3 ∂P) + ∫ ω, |G i ω| ^ 3 ∂Q) := by
  obtain ⟨hd₁, hd₂, hd₃⟩ := window_hasDerivAt_chain δ a b
  exact abs_integral_sum_sub_le hd₁ hd₂ hd₃
    (fun x => by
      rw [abs_of_nonneg (window_nonneg δ a b x)]; exact window_le_one δ a b x)
    (fun x => abs_deriv_window_le hδ a b x)
    (fun x => abs_deriv2_window_le hδ a b x) (fun x => abs_deriv3_window_le hδ a b x)
    hξm hGm hξi hGi hξ₁ hξ₂ hG₁ hG₂ hm₁ hm₂ hTξ hTG

/-- **Lemma 3 for a block.**  An independent family, compared with an independent Gaussian family
of the same first two moments, satisfies the window comparison.  `D` (the swap against the two
smoothed windows) and `K` (the Gaussian collar) are supplied here; the caller gives `q`, a lower
bound on the Gaussian's own window mass, chooses `δ`, and checks `hnum`. -/
theorem isWindowComparison₁_of_gaussian_family {ι : Type*} {s : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ξ : ι → Ω → ℝ} {G : ι → Ω' → ℝ} {m : ι → ℝ} {v : ι → ℝ≥0}
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    (hlaw : ∀ i, Q.map (G i) = gaussianReal (m i) (v i))
    (hξ₁ : ∀ i ∈ s, Integrable (ξ i) P)
    (hξ₂ : ∀ i ∈ s, Integrable (fun ω => ξ i ω * ξ i ω) P)
    (hG₁ : ∀ i ∈ s, Integrable (G i) Q)
    (hG₂ : ∀ i ∈ s, Integrable (fun ω => G i ω * G i ω) Q)
    (hm₁ : ∀ i ∈ s, ∫ ω, ξ i ω ∂P = ∫ ω, G i ω ∂Q)
    (hm₂ : ∀ i ∈ s, ∫ ω, ξ i ω * ξ i ω ∂P = ∫ ω, G i ω * G i ω ∂Q)
    (hTξ : ∀ i ∈ s, Integrable (fun ω => |ξ i ω| ^ 3) P)
    (hTG : ∀ i ∈ s, Integrable (fun ω => |G i ω| ^ 3) Q)
    {δ w M ε q : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hv : (∑ i ∈ s, v i) ≠ 0)
    (hqlow : ∀ c, |c| ≤ M →
      q ≤ (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) (Set.Ioc c (c + w))).toReal)
    (hnum : 450 / δ ^ 3 * (∑ i ∈ s, ((∫ ω, |ξ i ω| ^ 3 ∂P) + ∫ ω, |G i ω| ^ 3 ∂Q))
        + 4 * δ / Real.sqrt (2 * Real.pi * (∑ i ∈ s, v i)) ≤ ε * q) :
    IsWindowComparison₁ P Q (fun ω => ∑ i ∈ s, ξ i ω) (fun ω => ∑ i ∈ s, G i ω) w M ε := by
  have hNm : Measurable (fun ω => ∑ i ∈ s, G i ω) :=
    Finset.measurable_sum s fun i _ => hGm i
  have hXm : Measurable (fun ω => ∑ i ∈ s, ξ i ω) :=
    Finset.measurable_sum s fun i _ => hξm i
  -- the block sum of the Gaussians is Gaussian
  have hsumlaw : Q.map (fun ω => ∑ i ∈ s, G i ω)
      = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) :=
    map_sum_gaussianReal hGm hGi hlaw s
  have htrans : ∀ S : Set ℝ, MeasurableSet S →
      Q ((fun ω => ∑ i ∈ s, G i ω) ⁻¹' S)
        = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) S := by
    intro S hS
    rw [← Measure.map_apply hNm hS, hsumlaw]
  refine isWindowComparison₁_of_swap hXm hNm (D := 450 / δ ^ 3 *
      (∑ i ∈ s, ((∫ ω, |ξ i ω| ^ 3 ∂P) + ∫ ω, |G i ω| ^ 3 ∂Q)))
      (K := 4 * δ / Real.sqrt (2 * Real.pi * (∑ i ∈ s, v i))) hδ hq ?_ ?_ ?_ ?_ hnum
  · -- `D`, on the upper window
    intro c _
    exact abs_integral_window_sum_sub_le hξm hGm hξi hGi hξ₁ hξ₂ hG₁ hG₂ hm₁ hm₂ hTξ hTG hδ _ _
  · -- `D`, on the lower window
    intro c _
    exact abs_integral_window_sum_sub_le hξm hGm hξi hGi hξ₁ hξ₂ hG₁ hG₂ hm₁ hm₂ hTξ hTG hδ _ _
  · -- `K`, the collar
    intro c _
    rw [htrans _ (measurableSet_Icc.union measurableSet_Icc)]
    exact measure_collar_gaussianReal_le _ hv c (c + w) hδ.le
  · -- `q`, from the caller
    intro c hc
    rw [htrans _ measurableSet_Ioc]
    exact hqlow c hc

/-- **The balance `δ = T^{1/4}`.**  At that `δ` the Lindeberg charge `A T/δ³` collapses to
`A T^{1/4}`, whatever the constant `A` — `450` in one dimension, `3600` in two — and the swap error
and the collar error are then of the same order, which is the best `δ` can do. -/
lemma swap_error_at_quarter (A : ℝ) {T : ℝ} (hT : 0 < T) :
    A / (T ^ (1 / 4 : ℝ)) ^ 3 * T = A * T ^ (1 / 4 : ℝ) := by
  have h3 : (T ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = T ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast (T ^ (1 / 4 : ℝ)) 3, ← Real.rpow_mul hT.le]
    norm_num
  have hdiv : T / T ^ (3 / 4 : ℝ) = T ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℝ) = 1 - 3 / 4 by norm_num, Real.rpow_sub hT, Real.rpow_one]
  have hpos : (0 : ℝ) < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hT _
  rw [h3, div_mul_eq_mul_div, mul_comm A T, mul_div_assoc, mul_comm]
  rw [← hdiv]
  ring

/-- **Lemma 3 at one block, with `δ` eliminated** — the form Harper's Lemma 3 is applied in.  At
`δ = T^{1/4}` (`T` bounds the third-moment sum) the condition of
`RMF.isWindowComparison₁_of_gaussian_family` becomes `(450 + 4/√(2πV))·T^{1/4} ≤ εq`.  On a block
`x^{1/e} < p ≤ x`, `T^{1/4} ≍ x^{-1/(8e)} = x^{-0.046}`, against `εq ≥ x^{-1/64}` for Harper's
`ε = x^{-1/100}` and `q ≥ x^{-9/1600}` (`RMF.le_measure_Icc_gaussianReal_normalised_of_bounds`). -/
theorem isWindowComparison₁_of_gaussian_family_of_third_moment {ι : Type*} {s : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ξ : ι → Ω → ℝ} {G : ι → Ω' → ℝ} {m : ι → ℝ} {v : ι → ℝ≥0}
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    (hlaw : ∀ i, Q.map (G i) = gaussianReal (m i) (v i))
    (hξ₁ : ∀ i ∈ s, Integrable (ξ i) P)
    (hξ₂ : ∀ i ∈ s, Integrable (fun ω => ξ i ω * ξ i ω) P)
    (hG₁ : ∀ i ∈ s, Integrable (G i) Q)
    (hG₂ : ∀ i ∈ s, Integrable (fun ω => G i ω * G i ω) Q)
    (hm₁ : ∀ i ∈ s, ∫ ω, ξ i ω ∂P = ∫ ω, G i ω ∂Q)
    (hm₂ : ∀ i ∈ s, ∫ ω, ξ i ω * ξ i ω ∂P = ∫ ω, G i ω * G i ω ∂Q)
    (hTξ : ∀ i ∈ s, Integrable (fun ω => |ξ i ω| ^ 3) P)
    (hTG : ∀ i ∈ s, Integrable (fun ω => |G i ω| ^ 3) Q)
    {T w M ε q : ℝ} (hT : 0 < T) (hq : 0 < q) (hv : (∑ i ∈ s, v i) ≠ 0)
    (hTb : (∑ i ∈ s, ((∫ ω, |ξ i ω| ^ 3 ∂P) + ∫ ω, |G i ω| ^ 3 ∂Q)) ≤ T)
    (hqlow : ∀ c, |c| ≤ M →
      q ≤ (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) (Set.Ioc c (c + w))).toReal)
    (hnum : (450 + 4 / Real.sqrt (2 * Real.pi * (∑ i ∈ s, v i))) * T ^ (1 / 4 : ℝ) ≤ ε * q) :
    IsWindowComparison₁ P Q (fun ω => ∑ i ∈ s, ξ i ω) (fun ω => ∑ i ∈ s, G i ω) w M ε := by
  have hδ : (0 : ℝ) < T ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hT _
  refine isWindowComparison₁_of_gaussian_family hξm hGm hξi hGi hlaw hξ₁ hξ₂ hG₁ hG₂ hm₁ hm₂
    hTξ hTG hδ hq hv hqlow (le_trans ?_ hnum)
  -- the swap error at the balanced `δ`
  have hswap : 450 / (T ^ (1 / 4 : ℝ)) ^ 3
      * (∑ i ∈ s, ((∫ ω, |ξ i ω| ^ 3 ∂P) + ∫ ω, |G i ω| ^ 3 ∂Q))
      ≤ 450 * T ^ (1 / 4 : ℝ) := by
    rw [← swap_error_at_quarter 450 hT]
    exact mul_le_mul_of_nonneg_left hTb (by positivity)
  -- the collar error at the balanced `δ`
  have hcollar : 4 * T ^ (1 / 4 : ℝ) / Real.sqrt (2 * Real.pi * ((∑ i ∈ s, v i : ℝ≥0) : ℝ))
      = 4 / Real.sqrt (2 * Real.pi * ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) * T ^ (1 / 4 : ℝ) := by
    ring
  rw [hcollar, add_mul]
  linarith [hswap]

/-! ### Compounding relative errors

Per-coordinate errors `ε m` with `∑ ε m ≤ E ≤ 1/2` compound into a single `2E`.  Both directions
are Weierstrass product inequalities, and neither is in Mathlib. -/

/-- **Weierstrass, from below.**  `1 - ∑ ε i ≤ ∏ (1 - ε i)` for `0 ≤ ε i ≤ 1`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} (t : Finset ι) {ε : ι → ℝ}
    (h0 : ∀ i ∈ t, 0 ≤ ε i) (h1 : ∀ i ∈ t, ε i ≤ 1) :
    1 - ∑ i ∈ t, ε i ≤ ∏ i ∈ t, (1 - ε i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0a := h0 a (Finset.mem_insert_self a t)
    have h1a := h1 a (Finset.mem_insert_self a t)
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hS : 0 ≤ ∑ i ∈ t, ε i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hstep : (1 - ε a) * (1 - ∑ i ∈ t, ε i) ≤ (1 - ε a) * ∏ i ∈ t, (1 - ε i) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    nlinarith [mul_nonneg h0a hS]

/-- **Weierstrass, from above**, in the form that avoids a division: `(1 - ∑ ε i) · ∏ (1 + ε i) ≤ 1`
for `0 ≤ ε i`.  When `∑ ε i < 1` this says `∏ (1 + ε i) ≤ 1/(1 - ∑ ε i)`. -/
lemma one_sub_sum_mul_prod_one_add_le {ι : Type*} (t : Finset ι) {ε : ι → ℝ}
    (h0 : ∀ i ∈ t, 0 ≤ ε i) :
    (1 - ∑ i ∈ t, ε i) * ∏ i ∈ t, (1 + ε i) ≤ 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0a := h0 a (Finset.mem_insert_self a t)
    have ih' := ih fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hS : 0 ≤ ∑ i ∈ t, ε i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hP : 0 ≤ ∏ i ∈ t, (1 + ε i) :=
      Finset.prod_nonneg fun i hi => by linarith [h0 i (Finset.mem_insert_of_mem hi)]
    nlinarith [mul_nonneg (mul_nonneg h0a h0a) hP, mul_nonneg (mul_nonneg h0a hS) hP]

/-! ### Compounding, in any dimension

The factorisation and the compounding are, like the swap-to-comparison bridge above, statements
about a family of one-coordinate events and nothing else.  Stating them over an arbitrary
measurable target lets the two-point argument reuse them at `ℝ × ℝ`, where the one-coordinate
event is a box rather than a window. -/

/-- A slice over an arbitrary family of target sets: coordinate `m` lands in `I m`, for `m < n`.
`RMF.sliceEvent` is this at `I m = Ioc (c m) (c m + w m)`. -/
def sliceEventOf {β : Type*} (X : ℕ → Ω → β) (n : ℕ) (I : ℕ → Set β) : Set Ω :=
  {ω | ∀ m, m < n → X m ω ∈ I m}

/-- **A slice factorises**, at any target: it is an intersection of one-coordinate events. -/
lemma measure_sliceEventOf_eq_prod {β : Type*} [MeasurableSpace β] {P : Measure Ω}
    {X : ℕ → Ω → β} (hXi : iIndepFun X P) (n : ℕ) {I : ℕ → Set β}
    (hI : ∀ m, MeasurableSet (I m)) :
    P (sliceEventOf X n I) = ∏ m ∈ Finset.range n, P (X m ⁻¹' I m) := by
  have hrw : sliceEventOf X n I = ⋂ m ∈ Finset.range n, X m ⁻¹' I m := by
    ext ω
    simp only [sliceEventOf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
  rw [hrw]
  exact hXi.meas_biInter fun m _ => ⟨I m, hI m, rfl⟩

/-- The same, as a real number. -/
lemma toReal_measure_sliceEventOf_eq_prod {β : Type*} [MeasurableSpace β] {P : Measure Ω}
    {X : ℕ → Ω → β} (hXi : iIndepFun X P) (n : ℕ) {I : ℕ → Set β}
    (hI : ∀ m, MeasurableSet (I m)) :
    (P (sliceEventOf X n I)).toReal = ∏ m ∈ Finset.range n, (P (X m ⁻¹' I m)).toReal := by
  rw [measure_sliceEventOf_eq_prod hXi n hI, ENNReal.toReal_prod]

/-- **The product over blocks**, at any target — Lemma 3's factorisation step and Lemma 7's.
Per-coordinate errors `ε m ≥ 0` with `∑ ε m ≤ E ≤ 1/2` compound into `2E`: `∏(1 - ε) ≥ 1 - ∑ε`
from below, `∏(1 + ε) ≤ 1/(1 - ∑ε) ≤ 1 + 2∑ε` from above.  At `β = ℝ` this is
`RMF.isWindowComparison_of_indep`; at `β = ℝ × ℝ` the independence is
`RMF.IsSteinhausPrimeValues.iIndepFun_tiltedMeasure₂` and the per-block input
`RMF.le_measure_box_of_swap`. -/
theorem le_measure_sliceEventOf_of_indep {β : Type*} [MeasurableSpace β]
    {P : Measure Ω} {Q : Measure Ω'} {X : ℕ → Ω → β} {N : ℕ → Ω' → β} {n : ℕ}
    {I : ℕ → Set β} {ε : ℕ → ℝ} {Eb : ℝ}
    (hXi : iIndepFun X P) (hNi : iIndepFun N Q) (hI : ∀ m, MeasurableSet (I m))
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ Eb) (hE : Eb ≤ 1 / 2)
    (hcmp : ∀ m, m < n →
      (1 - ε m) * (Q (N m ⁻¹' I m)).toReal ≤ (P (X m ⁻¹' I m)).toReal ∧
        (P (X m ⁻¹' I m)).toReal ≤ (1 + ε m) * (Q (N m ⁻¹' I m)).toReal) :
    (1 - 2 * Eb) * (Q (sliceEventOf N n I)).toReal ≤ (P (sliceEventOf X n I)).toReal ∧
      (P (sliceEventOf X n I)).toReal ≤ (1 + 2 * Eb) * (Q (sliceEventOf N n I)).toReal := by
  have hSnn : 0 ≤ ∑ m ∈ Finset.range n, ε m :=
    Finset.sum_nonneg fun m hm => hε0 m (Finset.mem_range.mp hm)
  have hE0 : 0 ≤ Eb := le_trans hSnn hsum
  have hpq : ∀ m ∈ Finset.range n,
      (1 - ε m) * (Q (N m ⁻¹' I m)).toReal ≤ (P (X m ⁻¹' I m)).toReal ∧
        (P (X m ⁻¹' I m)).toReal ≤ (1 + ε m) * (Q (N m ⁻¹' I m)).toReal :=
    fun m hm => hcmp m (Finset.mem_range.mp hm)
  have hεle : ∀ m ∈ Finset.range n, ε m ≤ Eb := fun m hm =>
    le_trans (Finset.single_le_sum (fun i hi => hε0 i (Finset.mem_range.mp hi)) hm) hsum
  have hQnn : 0 ≤ ∏ m ∈ Finset.range n, (Q (N m ⁻¹' I m)).toReal :=
    Finset.prod_nonneg fun m _ => ENNReal.toReal_nonneg
  rw [toReal_measure_sliceEventOf_eq_prod hXi n hI, toReal_measure_sliceEventOf_eq_prod hNi n hI]
  constructor
  · have hlow : 1 - 2 * Eb ≤ ∏ m ∈ Finset.range n, (1 - ε m) := by
      refine le_trans ?_ (one_sub_sum_le_prod_one_sub (Finset.range n)
        (fun m hm => hε0 m (Finset.mem_range.mp hm))
        (fun m hm => le_trans (hεle m hm) (by linarith)))
      linarith
    calc (1 - 2 * Eb) * ∏ m ∈ Finset.range n, (Q (N m ⁻¹' I m)).toReal
        ≤ (∏ m ∈ Finset.range n, (1 - ε m))
            * ∏ m ∈ Finset.range n, (Q (N m ⁻¹' I m)).toReal :=
          mul_le_mul_of_nonneg_right hlow hQnn
      _ = ∏ m ∈ Finset.range n, ((1 - ε m) * (Q (N m ⁻¹' I m)).toReal) :=
          (Finset.prod_mul_distrib).symm
      _ ≤ ∏ m ∈ Finset.range n, (P (X m ⁻¹' I m)).toReal :=
          Finset.prod_le_prod
            (fun m hm => mul_nonneg (by linarith [hεle m hm, hE]) ENNReal.toReal_nonneg)
            (fun m hm => (hpq m hm).1)
  · have hkey := one_sub_sum_mul_prod_one_add_le (Finset.range n)
        fun m hm => hε0 m (Finset.mem_range.mp hm)
    have hPnn : 0 ≤ ∏ m ∈ Finset.range n, (1 + ε m) :=
      Finset.prod_nonneg fun m hm => by linarith [hε0 m (Finset.mem_range.mp hm)]
    have hhigh : (∏ m ∈ Finset.range n, (1 + ε m)) ≤ 1 + 2 * Eb := by
      nlinarith [hkey, hPnn, hSnn, hsum, hE, hE0]
    calc ∏ m ∈ Finset.range n, (P (X m ⁻¹' I m)).toReal
        ≤ ∏ m ∈ Finset.range n, ((1 + ε m) * (Q (N m ⁻¹' I m)).toReal) :=
          Finset.prod_le_prod (fun m _ => ENNReal.toReal_nonneg) (fun m hm => (hpq m hm).2)
      _ = (∏ m ∈ Finset.range n, (1 + ε m))
            * ∏ m ∈ Finset.range n, (Q (N m ⁻¹' I m)).toReal := Finset.prod_mul_distrib
      _ ≤ (1 + 2 * Eb) * ∏ m ∈ Finset.range n, (Q (N m ⁻¹' I m)).toReal :=
          mul_le_mul_of_nonneg_right hhigh hQnn

/-- **Lemma 3, the factorisation step.**  Per-coordinate comparisons `IsWindowComparison₁` with
errors `ε m ≥ 0` and `∑_{m<n} ε m ≤ E ≤ 1/2` give `IsWindowComparison` with error `2E`: by
independence both probabilities factor over `m`.  `E ≤ 1/2` is the caller's form of Harper's
hypothesis that `x_1` is sufficiently large, under which his `∑_j x_j^{-1/100}` is
`≍ x_1^{-1/100}`.  No measurability hypothesis: `iIndepFun` carries it. -/
theorem isWindowComparison_of_indep {P : Measure Ω} {Q : Measure Ω'}
    {X : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {w M : ℕ → ℝ} {n : ℕ}
    {ε : ℕ → ℝ} {E : ℝ}
    (hXi : iIndepFun X P) (hNi : iIndepFun N Q)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2)
    (hcmp : ∀ m, m < n → IsWindowComparison₁ P Q (X m) (N m) (w m) (M m) (ε m)) :
    IsWindowComparison P Q X N w M n (2 * E) := by
  intro c hc
  exact le_measure_sliceEventOf_of_indep hXi hNi (fun _ => measurableSet_Ioc) hε0 hsum hE
    fun m hm => hcmp m hm (c m) (hc m hm)

/-! ### The partition skeleton

Both halves of Lemma 4 — and both halves of its two-point analogue — are one argument: a countable
disjoint family covers the event on one side, each cell is compared with a cell on the other side,
and the images are disjoint and land inside the target.  Nothing in it knows what a window is, or
that the increments are real.

The two multipliers are what let a single statement serve both directions: the upper bound takes
`a = 1`, `b = 1 + ε`, the lower bound `a = 1 - ε`, `b = 1`.  Stating it in `ℝ≥0∞`, where there is
no subtraction, is why no sign hypothesis appears. -/

/-- **Summing a cellwise comparison over a countable partition.**  `S` is covered by the disjoint
cells `F k`, the disjoint `G k` lie inside `T`, and each `F k` is dominated by its `G k` up to the
two multipliers; then `S` is dominated by `T`.  Countability of the index is what turns the
partition into a `tsum`: in Lemma 4 the index is `Fin n → ℤ`, in the two-point version a pair of
those. -/
theorem mul_measure_le_of_cellwise {ι : Type*} [Countable ι] {μ : Measure Ω} {ν : Measure Ω'}
    {S : Set Ω} {T : Set Ω'} {F : ι → Set Ω} {G : ι → Set Ω'} {a b : ℝ≥0∞}
    (hFmeas : ∀ k, MeasurableSet (F k)) (hGmeas : ∀ k, MeasurableSet (G k))
    (hFdisj : Pairwise (Function.onFun Disjoint F))
    (hGdisj : Pairwise (Function.onFun Disjoint G))
    (hcover : S ⊆ ⋃ k, F k) (hsub : (⋃ k, G k) ⊆ T)
    (hcell : ∀ k, a * μ (F k) ≤ b * ν (G k)) :
    a * μ S ≤ b * ν T :=
  calc a * μ S ≤ a * μ (⋃ k, F k) := mul_le_mul_right (measure_mono hcover) a
    _ = a * ∑' k, μ (F k) := by rw [measure_iUnion hFdisj hFmeas]
    _ = ∑' k, a * μ (F k) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' k, b * ν (G k) := ENNReal.tsum_le_tsum hcell
    _ = b * ∑' k, ν (G k) := ENNReal.tsum_mul_left
    _ = b * ν (⋃ k, G k) := by rw [measure_iUnion hGdisj hGmeas]
    _ ≤ b * ν T := mul_le_mul_right (measure_mono hsub) b

/-! ### Lemma 4 — from windows to the barrier

Slicing: chop each coordinate into windows of width `w m`, keep the tuples whose partial sums
respect the barrier, and sum Lemma 3 over that countable grid.  A path in the barrier lies in
exactly one slice, and the partial sums of the window endpoints track the path to within
`∑_m w m ≤ 2` — Harper's `± 2`, for his windows `w m = 1/(m+1)²`.  Lemma 3 enters only as
`IsWindowComparison`.

**`hM0 : 0 ≤ M j` is needed.**  Without it `hMM` at `m = 0` admits a negative `M' 0`; the premise
`|c m| ≤ M' m` of `IsWindowComparison` is then unsatisfiable, and both statements below would
compare two arbitrary measures.  Harper's envelope `M j = (1/80)√(log x_j)` is non-negative.
`hMM : M m + M (m+1) + w m ≤ M' m` is his step from `(1/80)√(log x_j)` at both endpoints of an
increment to `(1/40)√(log x_j)`, plus the grid offset `w m`.  One hypothesis is weaker than his:
`u j ≤ v j` is not assumed (if it fails, both barrier events are empty).

**The slicing has room — and the half-open convention is what buys it.**  Harper's windows are
closed, `r_j ≤ log|I_{l_j}| ≤ r_j + 1/j²`, so they **overlap at their endpoints** and the slices
are not disjoint.  On the Gaussian side that is harmless — each `N_j` has a density — but the
lower bound needs the same step under the *tilted* law, which needs each tilted increment to be
atomless: true, but not proved in the paper.

`RMF.sliceEvent` uses `Ioc`, and the lemmas below show this costs nothing:
`sliceEvent_disjoint_of_le` gives genuinely disjoint slices with no atomlessness,
`abs_walk_sub_walk_le` keeps two paths of one slice within `∑_{m<j} w m`, and the two containments
are what the upper and lower bounds sum over.  Within one slice `|X m - Y m| < w m` *strictly*, so
the half-open choice has more room than Harper's closed windows, not less. -/

omit [MeasurableSpace Ω] in
/-- **Distinct grid points give disjoint slices.**  Half-open windows separated by at least their
own width cannot both contain the same increment.  This is what replaces atomlessness. -/
lemma sliceEvent_disjoint_of_le {X : ℕ → Ω → ℝ} {w : ℕ → ℝ} {n : ℕ} {c c' : ℕ → ℝ} {m : ℕ}
    (hm : m < n) (hsep : w m ≤ |c m - c' m|) :
    Disjoint (sliceEvent X w n c) (sliceEvent X w n c') := by
  rw [Set.disjoint_left]
  intro ω h h'
  have h1 := h m hm
  have h2 := h' m hm
  rw [Set.mem_Ioc] at h1 h2
  rcases le_or_gt (c m) (c' m) with hle | hlt
  · have : w m ≤ c' m - c m := by
      rwa [abs_of_nonpos (by linarith), neg_sub] at hsep
    linarith [h1.2, h2.1]
  · have : w m ≤ c m - c' m := by
      rwa [abs_of_nonneg (by linarith)] at hsep
    linarith [h2.2, h1.1]

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **Two paths in the same slice track each other.**  Their partial sums differ by at most
`∑_{m<j} w m`, which `hwsum` caps at `2`.  This is the whole content of Harper's `± 2`. -/
lemma abs_walk_sub_walk_le {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {w : ℕ → ℝ} {n : ℕ} {c : ℕ → ℝ}
    {ω : Ω} {ω' : Ω'} (hx : ω ∈ sliceEvent X w n c) (hy : ω' ∈ sliceEvent Y w n c)
    {j : ℕ} (hj : j ≤ n) :
    |walk X j ω - walk Y j ω'| ≤ ∑ m ∈ Finset.range j, w m := by
  rw [walk_apply, walk_apply, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hmn : m < n := lt_of_lt_of_le (Finset.mem_range.mp hm) hj
  have h1 := hx m hmn
  have h2 := hy m hmn
  rw [Set.mem_Ioc] at h1 h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith [h1.2, h2.1], by linarith [h2.2, h1.1]⟩

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The containment the upper bound sums over.**  If *one* path of a slice satisfies the barrier,
*every* path of that slice — on either space — satisfies the barrier widened by `2`. -/
lemma sliceEvent_subset_barrierEvent_widen {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {w : ℕ → ℝ}
    {n : ℕ} {c u v : ℕ → ℝ} {ω : Ω}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hx : ω ∈ sliceEvent X w n c) (hb : ω ∈ barrierEvent X n u v) :
    sliceEvent Y w n c ⊆ barrierEvent Y n (fun j => u j - 2) (fun j => v j + 2) := by
  intro ω' hy j hj1 hjn
  have hd := abs_sub_le_iff.mp ((abs_walk_sub_walk_le hx hy hjn).trans (hwsum j hjn))
  have hbj := hb j hj1 hjn
  rw [Set.mem_Icc] at hbj ⊢
  exact ⟨by linarith [hbj.1, hd.1], by linarith [hbj.2, hd.2]⟩

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The containment the lower bound sums over.**  If one path of a slice satisfies the barrier
*narrowed* by `2`, every path of that slice satisfies the barrier itself. -/
lemma sliceEvent_subset_barrierEvent_of_narrow {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {w : ℕ → ℝ}
    {n : ℕ} {c u v : ℕ → ℝ} {ω : Ω}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hx : ω ∈ sliceEvent X w n c)
    (hb : ω ∈ barrierEvent X n (fun j => u j + 2) (fun j => v j - 2)) :
    sliceEvent Y w n c ⊆ barrierEvent Y n u v := by
  intro ω' hy j hj1 hjn
  have hd := abs_sub_le_iff.mp ((abs_walk_sub_walk_le hx hy hjn).trans (hwsum j hjn))
  have hbj := hb j hj1 hjn
  rw [Set.mem_Icc] at hbj ⊢
  simp only at hbj
  exact ⟨by linarith [hbj.1, hd.1], by linarith [hbj.2, hd.2]⟩

/-! ### The grid

Harper slices over `R_j = (1/j²)ℤ ∩ [-…, …]`.  Here the grid is `w m · ℤ` and a tuple of grid
points is a `k : Fin n → ℤ` — a **countable** index set, which is what lets the barrier event be
partitioned and the measures summed.  Indexing by `ℕ → ℤ` would not be countable; only the first
`n` coordinates matter, so `Fin n` is both correct and necessary. -/

/-- The tuple of window left-endpoints named by `k`. -/
noncomputable def gridPoint (w : ℕ → ℝ) (n : ℕ) (k : Fin n → ℤ) (m : ℕ) : ℝ :=
  if h : m < n then w m * (k ⟨m, h⟩ : ℤ) - w m else 0

/-- The window a path actually falls into: `X m ω ∈ (c, c + w m]` with `c` the `⌈·⌉`-grid point. -/
noncomputable def gridIndex (X : ℕ → Ω → ℝ) (w : ℕ → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℤ :=
  fun i => ⌈X i ω / w i⌉

omit [MeasurableSpace Ω] in
/-- Every path lies in the slice its own grid index names. -/
lemma mem_sliceEvent_gridPoint {X : ℕ → Ω → ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : ∀ m, 0 < w m) (ω : Ω) :
    ω ∈ sliceEvent X w n (gridPoint w n (gridIndex X w n ω)) := by
  intro m hm
  simp only [gridPoint, dif_pos hm, gridIndex]
  rw [Set.mem_Ioc]
  have hwm := hw m
  constructor
  · have h := Int.ceil_lt_add_one (X m ω / w m)
    have := (mul_lt_mul_of_pos_left h hwm)
    rw [mul_add, mul_one, mul_div_cancel₀ _ hwm.ne'] at this
    linarith
  · have h := Int.le_ceil (X m ω / w m)
    have := (mul_le_mul_of_nonneg_left h hwm.le)
    rw [mul_div_cancel₀ _ hwm.ne'] at this
    linarith

omit [MeasurableSpace Ω] in
/-- Distinct grid tuples are at least one window apart, hence name disjoint slices. -/
lemma sliceEvent_gridPoint_disjoint {X : ℕ → Ω → ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : ∀ m, 0 < w m)
    {k k' : Fin n → ℤ} (hne : k ≠ k') :
    Disjoint (sliceEvent X w n (gridPoint w n k)) (sliceEvent X w n (gridPoint w n k')) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine sliceEvent_disjoint_of_le (m := (i : ℕ)) i.isLt ?_
  have hwi := hw (i : ℕ)
  simp only [gridPoint, dif_pos i.isLt, Fin.eta]
  have hsub : w (i : ℕ) * (k i : ℝ) - w (i : ℕ) - (w (i : ℕ) * (k' i : ℝ) - w (i : ℕ))
      = w (i : ℕ) * ((k i : ℝ) - (k' i : ℝ)) := by ring
  rw [hsub, abs_mul, abs_of_pos hwi]
  have h1 : (1 : ℝ) ≤ |(k i : ℝ) - (k' i : ℝ)| := by
    have : ((k i - k' i : ℤ) : ℝ) = (k i : ℝ) - (k' i : ℝ) := by push_cast; ring
    rw [← this, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hi)
  nlinarith

omit [MeasurableSpace Ω] in
/-- On the barrier the walk is bounded by the envelope. -/
lemma abs_walk_le_of_mem_barrierEvent {X : ℕ → Ω → ℝ} {n : ℕ} {u v M : ℕ → ℝ}
    (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j) {ω : Ω}
    (hb : ω ∈ barrierEvent X n u v) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    |walk X j ω| ≤ M j := by
  have h := hb j hj1 hjn
  rw [Set.mem_Icc] at h
  obtain ⟨h1, h2⟩ := hM j hj1 hjn
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

omit [MeasurableSpace Ω] in
/-- Hence each increment is bounded by the sum of the envelope at its two endpoints.  This is
Harper's step, and `m = 0` is where `hM0` is used: there `walk 0 = 0`. -/
lemma abs_increment_le_of_mem_barrierEvent {X : ℕ → Ω → ℝ} {n : ℕ} {u v M : ℕ → ℝ}
    (hM0 : ∀ j, 0 ≤ M j) (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j) {ω : Ω}
    (hb : ω ∈ barrierEvent X n u v) {m : ℕ} (hm : m < n) :
    |X m ω| ≤ M m + M (m + 1) := by
  have hsucc : X m ω = walk X (m + 1) ω - walk X m ω := by
    rw [walk_apply, walk_apply, Finset.sum_range_succ]; ring
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · have h0 : walk X 0 ω = 0 := by rw [walk_apply]; simp
    rw [hsucc, h0, sub_zero]
    exact le_trans (abs_walk_le_of_mem_barrierEvent hM hb le_rfl hm) (by linarith [hM0 0])
  · rw [hsucc]
    refine (abs_sub _ _).trans ?_
    have h1 := abs_walk_le_of_mem_barrierEvent hM hb (by omega) hm
    have h2 := abs_walk_le_of_mem_barrierEvent hM hb (by omega : 1 ≤ m) (by omega)
    linarith

omit [MeasurableSpace Ω] in
/-- **The grid point of a barrier path respects `M'`.**  This is what makes `IsWindowComparison`
applicable slice by slice, and it is the step that needs `hM0`. -/
lemma abs_gridPoint_le_of_mem_barrierEvent {X : ℕ → Ω → ℝ} {w M M' u v : ℕ → ℝ} {n : ℕ}
    (hw : ∀ m, 0 < w m) (hM0 : ∀ j, 0 ≤ M j)
    (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) {ω : Ω}
    (hb : ω ∈ barrierEvent X n u v) {m : ℕ} (hm : m < n) :
    |gridPoint w n (gridIndex X w n ω) m| ≤ M' m := by
  have hmem := mem_sliceEvent_gridPoint (X := X) hw ω m hm
  rw [Set.mem_Ioc] at hmem
  have hinc := abs_le.mp (abs_increment_le_of_mem_barrierEvent hM0 hM hb hm)
  have hMMm := hMM m hm
  have hwm := hw m
  rw [abs_le]
  exact ⟨by linarith [hmem.2, hinc.1], by linarith [hmem.1, hinc.2]⟩

/-- **Lemma 4, upper bound.**  The barrier probability under `P` is at most `1 + ε` times the
Gaussian one for the barrier widened by `2`.  The barrier event is partitioned over the countable
grid `w m · ℤ`, indexed by `Fin n → ℤ`; each non-empty slice has its grid point inside `M'`
(`RMF.abs_gridPoint_le_of_mem_barrierEvent`), so `hcmp` applies, and lies in the widened barrier
(`RMF.sliceEvent_subset_barrierEvent_widen`). -/
theorem measure_barrierEvent_le {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {w M M' u v : ℕ → ℝ} {n : ℕ}
    {ε : ℝ}
    (hX : ∀ m, Measurable (X m)) (hN : ∀ m, Measurable (N m))
    (hw : ∀ m, 0 < w m)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j) (hε : 0 ≤ ε)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsWindowComparison P Q X N w M' n ε) :
    (P (barrierEvent X n u v)).toReal
      ≤ (1 + ε) * (Q (barrierEvent N n (fun j => u j - 2) (fun j => v j + 2))).toReal := by
  classical
  set A := barrierEvent X n u v with hAdef
  set Bw := barrierEvent N n (fun j => u j - 2) (fun j => v j + 2) with hBwdef
  set F : (Fin n → ℤ) → Set Ω := fun k => A ∩ sliceEvent X w n (gridPoint w n k) with hFdef
  set G : (Fin n → ℤ) → Set Ω' :=
    fun k => if (F k).Nonempty then sliceEvent N w n (gridPoint w n k) else ∅ with hGdef
  -- measurability
  have hFmeas : ∀ k, MeasurableSet (F k) := fun k =>
    (measurableSet_barrierEvent hX n u v).inter (measurableSet_sliceEvent hX w n _)
  have hGmeas : ∀ k, MeasurableSet (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · simpa only [hGdef, if_pos h] using measurableSet_sliceEvent hN w n (gridPoint w n k)
    · simpa only [hGdef, if_neg h] using MeasurableSet.empty
  -- disjointness, on both sides
  have hFdisj : Pairwise (Function.onFun Disjoint F) := fun k k' hne =>
    (sliceEvent_gridPoint_disjoint hw hne).mono Set.inter_subset_right Set.inter_subset_right
  have hGdisj : Pairwise (Function.onFun Disjoint G) := by
    intro k k' hne
    simp only [hGdef, Function.onFun]
    split_ifs
    · exact sliceEvent_gridPoint_disjoint hw hne
    all_goals simp
  -- the barrier is the disjoint union of its slices
  have hAunion : A = ⋃ k, F k := by
    ext ω
    refine ⟨fun hω => Set.mem_iUnion.mpr ⟨gridIndex X w n ω, hω, mem_sliceEvent_gridPoint hw ω⟩,
      fun h => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact hk.1
  -- transfer of one inequality from `ℝ` to `ℝ≥0∞`
  have hconv : ∀ (s : Set Ω) (t : Set Ω'), (P s).toReal ≤ (1 + ε) * (Q t).toReal →
      P s ≤ ENNReal.ofReal (1 + ε) * Q t := by
    intro s t h
    rw [← ENNReal.ofReal_toReal (measure_ne_top P s), ← ENNReal.ofReal_toReal (measure_ne_top Q t),
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal h
  have hGpos : ∀ k, (F k).Nonempty → G k = sliceEvent N w n (gridPoint w n k) := by
    intro k h
    simp only [hGdef]
    rw [if_pos h]
  -- the slice-by-slice estimate
  have hslice : ∀ k, P (F k) ≤ ENNReal.ofReal (1 + ε) * Q (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωA, hωs⟩ := h
      -- the witness pins `k` down: it lies in its own slice too, and slices are disjoint
      have hkeq : k = gridIndex X w n ω := by
        by_contra hne
        exact Set.disjoint_left.mp (sliceEvent_gridPoint_disjoint (X := X) hw hne) hωs
          (mem_sliceEvent_gridPoint hw ω)
      have henv : ∀ m, m < n → |gridPoint w n k m| ≤ M' m := by
        intro m hm
        rw [hkeq]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hM hMM hωA hm
      have hup := (hcmp (gridPoint w n k) henv).2
      rw [hGpos k ⟨ω, hωA, hωs⟩]
      exact le_trans (measure_mono Set.inter_subset_right) (hconv _ _ hup)
    · have : F k = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [this]
  -- every non-empty slice sits inside the widened barrier
  have hGsub : (⋃ k, G k) ⊆ Bw := by
    refine Set.iUnion_subset fun k => ?_
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωA, hωs⟩ := h
      rw [hGpos k ⟨ω, hωA, hωs⟩]
      exact sliceEvent_subset_barrierEvent_widen hwsum hωs hωA
    · simp only [hGdef, if_neg h]
      exact Set.empty_subset _
  -- assemble in `ℝ≥0∞`
  have key : P A ≤ ENNReal.ofReal (1 + ε) * Q Bw := by
    have h := mul_measure_le_of_cellwise (μ := P) (ν := Q) (S := A) (T := Bw) (a := 1)
      (b := ENNReal.ofReal (1 + ε)) hFmeas hGmeas hFdisj hGdisj hAunion.subset hGsub
      fun k => by rw [one_mul]; exact hslice k
    rwa [one_mul] at h
  -- and transport back to `ℝ`
  have hle := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top Q Bw)) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hle

/-- **Lemma 4, lower bound.**  Harper's proof is "exactly similar", and it is, with the two spaces
exchanging roles: the *narrowed Gaussian* barrier is partitioned, and each slice is pushed back to
`Ω`.  `0 ≤ ε` is not needed — the case `1 - ε ≤ 0` is trivial and `ℝ≥0∞` handles the sign — and
`hM` is weakened to the narrowed barrier before use. -/
theorem le_measure_barrierEvent {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {w M M' u v : ℕ → ℝ} {n : ℕ}
    {ε : ℝ}
    (hX : ∀ m, Measurable (X m)) (hN : ∀ m, Measurable (N m))
    (hw : ∀ m, 0 < w m)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsWindowComparison P Q X N w M' n ε) :
    (1 - ε) * (Q (barrierEvent N n (fun j => u j + 2) (fun j => v j - 2))).toReal
      ≤ (P (barrierEvent X n u v)).toReal := by
  classical
  set A := barrierEvent X n u v with hAdef
  set B := barrierEvent N n (fun j => u j + 2) (fun j => v j - 2) with hBdef
  rcases le_or_gt (1 - ε) 0 with hneg | hpos
  · -- nothing to prove once the factor is non-positive
    nlinarith [ENNReal.toReal_nonneg (a := Q B), ENNReal.toReal_nonneg (a := P A)]
  -- the narrowed barrier still respects the envelope
  have hMnar : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j + 2 ∧ v j - 2 ≤ M j := by
    intro j hj1 hjn
    obtain ⟨h1, h2⟩ := hM j hj1 hjn
    exact ⟨by linarith, by linarith⟩
  set F : (Fin n → ℤ) → Set Ω' := fun k => B ∩ sliceEvent N w n (gridPoint w n k) with hFdef
  set G : (Fin n → ℤ) → Set Ω :=
    fun k => if (F k).Nonempty then sliceEvent X w n (gridPoint w n k) else ∅ with hGdef
  have hFmeas : ∀ k, MeasurableSet (F k) := fun k =>
    (measurableSet_barrierEvent hN n _ _).inter (measurableSet_sliceEvent hN w n _)
  have hGmeas : ∀ k, MeasurableSet (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · simpa only [hGdef, if_pos h] using measurableSet_sliceEvent hX w n (gridPoint w n k)
    · simpa only [hGdef, if_neg h] using MeasurableSet.empty
  have hFdisj : Pairwise (Function.onFun Disjoint F) := fun k k' hne =>
    (sliceEvent_gridPoint_disjoint hw hne).mono Set.inter_subset_right Set.inter_subset_right
  have hGdisj : Pairwise (Function.onFun Disjoint G) := by
    intro k k' hne
    simp only [hGdef, Function.onFun]
    split_ifs
    · exact sliceEvent_gridPoint_disjoint hw hne
    all_goals simp
  have hBunion : B = ⋃ k, F k := by
    ext ω
    refine ⟨fun hω => Set.mem_iUnion.mpr ⟨gridIndex N w n ω, hω, mem_sliceEvent_gridPoint hw ω⟩,
      fun h => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact hk.1
  have hGpos : ∀ k, (F k).Nonempty → G k = sliceEvent X w n (gridPoint w n k) := by
    intro k h
    simp only [hGdef]
    rw [if_pos h]
  have hconv : ∀ (t : Set Ω') (r : Set Ω), (1 - ε) * (Q t).toReal ≤ (P r).toReal →
      ENNReal.ofReal (1 - ε) * Q t ≤ P r := by
    intro t r h
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q t), ← ENNReal.ofReal_toReal (measure_ne_top P r),
      ← ENNReal.ofReal_mul hpos.le]
    exact ENNReal.ofReal_le_ofReal h
  have hslice : ∀ k, ENNReal.ofReal (1 - ε) * Q (F k) ≤ P (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωB, hωs⟩ := h
      have hkeq : k = gridIndex N w n ω := by
        by_contra hne
        exact Set.disjoint_left.mp (sliceEvent_gridPoint_disjoint (X := N) hw hne) hωs
          (mem_sliceEvent_gridPoint hw ω)
      have henv : ∀ m, m < n → |gridPoint w n k m| ≤ M' m := by
        intro m hm
        rw [hkeq]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hMnar hMM hωB hm
      have hlow := (hcmp (gridPoint w n k) henv).1
      rw [hGpos k ⟨ω, hωB, hωs⟩]
      refine le_trans ?_ (hconv _ _ hlow)
      gcongr
      exact Set.inter_subset_right
    · have : F k = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [this]
  have hGsub : (⋃ k, G k) ⊆ A := by
    refine Set.iUnion_subset fun k => ?_
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωB, hωs⟩ := h
      rw [hGpos k ⟨ω, hωB, hωs⟩]
      exact sliceEvent_subset_barrierEvent_of_narrow hwsum hωs hωB
    · simp only [hGdef, if_neg h]
      exact Set.empty_subset _
  have key : ENNReal.ofReal (1 - ε) * Q B ≤ P A := by
    have h := mul_measure_le_of_cellwise (μ := Q) (ν := P) (S := B) (T := A)
      (a := ENNReal.ofReal (1 - ε)) (b := 1) hFmeas hGmeas hFdisj hGdisj hBunion.subset hGsub
      fun k => by rw [one_mul]; exact hslice k
    rwa [one_mul] at h
  have hle := ENNReal.toReal_mono (measure_ne_top P A) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le] at hle

omit [MeasurableSpace Ω'] in
/-- **Removing the drift.**  If `N m = G m + θ m` with `∑_{m < j} θ m = j + O(1)`, the barrier for
`N` becomes the barrier for the centred walk `G`, shifted by `-j`.  This is where Harper's `+ j`
comes from: each block contributes mean `1` under the tilt. -/
theorem barrierEvent_recentre {N G : ℕ → Ω' → ℝ} {θ : ℕ → ℝ} {C : ℝ} {n : ℕ} {u v : ℕ → ℝ}
    (hNG : ∀ m ω, N m ω = G m ω + θ m)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) :
    barrierEvent N n u v
      ⊆ barrierEvent G n (fun j => u j - j - C) (fun j => v j - j + C) := by
  intro ω hω j hj1 hjn
  have hwalk : walk N j ω = walk G j ω + ∑ m ∈ Finset.range j, θ m := by
    rw [walk_apply, walk_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => hNG m ω
  have hb := hω j hj1 hjn
  have hθj := abs_le.1 (hθ j hjn)
  rw [Set.mem_Icc, hwalk] at hb
  rw [Set.mem_Icc]
  constructor <;> simp only <;> linarith [hb.1, hb.2, hθj.1, hθj.2]

omit [MeasurableSpace Ω'] in
/-- **Removing the drift, the other way.**  The reverse inclusion, with the barrier *narrowed* by
`C` instead of widened.  Harper’s Lemma 4 is a two-sided sandwich and Proposition 5’s lower bound
consumes this half; `RMF.barrierEvent_recentre` alone serves only the upper bound. -/
theorem barrierEvent_recentre_subset {N G : ℕ → Ω' → ℝ} {θ : ℕ → ℝ} {C : ℝ} {n : ℕ} {u v : ℕ → ℝ}
    (hNG : ∀ m ω, N m ω = G m ω + θ m)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) :
    barrierEvent G n (fun j => u j - j + C) (fun j => v j - j - C)
      ⊆ barrierEvent N n u v := by
  intro ω hω j hj1 hjn
  have hwalk : walk N j ω = walk G j ω + ∑ m ∈ Finset.range j, θ m := by
    rw [walk_apply, walk_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => hNG m ω
  have hb := hω j hj1 hjn
  have hθj := abs_le.1 (hθ j hjn)
  rw [Set.mem_Icc] at hb
  simp only at hb
  rw [Set.mem_Icc, hwalk]
  constructor <;> linarith [hb.1, hb.2, hθj.1, hθj.2]

/-! ### Probability Results 1 and 2 — the curved barrier

Pure statements about a Gaussian random walk with comparable variances.  They use the flat-barrier
bounds `RMF.IsGaussianWalk.barrierProb_le_of_comparable_mgf` and
`RMF.IsGaussianWalk.barrierConstLow_le_barrierProb` as black boxes; the curved barrier is handled
by a separate induction over the *iterated* logarithm, freezing the barrier at time
`(log_{k+1} n)^{20}`.  A halving recursion cannot do it — it loses a factor `log n` exactly where
it matters.
-/

/-- **Probability Result 2** (Harper).  Adding a lower barrier `g(j) ≤ -B₂j` and capping the upper
one at `min{a, B₂j} + h(j)` does not change the order `min{1, a/√n}`, where
`B₂ = RMF.result2Slope vmin vmax`.

The upper half is `RMF.IsGaussianWalk.measure_bandEvent_le`: one containment and Probability
Result 1, with Result 1's constant.  The lower half is Harper's §A.2,
`RMF.IsGaussianWalk.le_measure_bandEvent_of_result1Lower`.  The size conditions are twice
Result 1's, because Result 1 is applied to a suffix of length `≥ n/2`. -/
theorem probabilityResult2_of_result1Lower {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IsGaussianWalk G v μ) {vmin vmax : ℝ} (hv : VarBracket v vmin
      vmax)
    {R : ℝ} (hR : Result1LowerOn G μ vmin R (result1LowerConst vmin vmax)) :
      ∀ a : ℝ, result2ThresholdOf R ≤ a → ∀ n : ℕ, 1 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        ∀ hf g : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (∀ j, g j ≤ -(result2Slope vmin vmax * j)) →
            result1LowerConst vmin vmax / 2 * min 1 (a / Real.sqrt n)
                ≤ (μ {ω | ∀ j, 1 ≤ j → j ≤ n → g j ≤ walk G j ω ∧
                      walk G j ω ≤ min a (result2Slope vmin vmax * j) + hf j}).toReal ∧
              (μ {ω | ∀ j, 1 ≤ j → j ≤ n → g j ≤ walk G j ω ∧
                    walk G j ω ≤ min a (result2Slope vmin vmax * j) + hf j}).toReal
                ≤ result1Const vmin vmax * min 1 (a / Real.sqrt n) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hlow := h.le_measure_bandEvent_of_result1Lower ⟨hvmin, hlo, hhi⟩ hR
  refine fun a ha n hn hbig hbig2 hf g hhf hg =>
    ⟨hlow a ha n hn hbig hbig2 hf g hhf hg, ?_⟩
  have hlog20 : (0 : ℝ) ≤ Real.log n ^ 20 := by positivity
  have hlog8 : (0 : ℝ) ≤ Real.log n ^ 8 := by positivity
  exact h.measure_bandEvent_le ⟨hvmin, hlo, hhi⟩
    (le_trans (le_result2ThresholdOf R) ha) hn (by linarith) (by linarith)
    (fun j hj1 hjn => le_trans (le_abs_self _) (hhf j hj1 hjn))

/-! ### Absorbing an additive constant into `a`

Lemma 4 widens the barrier by `2` and the drift removal by `C`, so what reaches the Probability
Results is `a ± (2 + C)` rather than `a`.  Both shifts are absorbed by the constants, and these two
lemmas are the whole of that: `min{1, ·/√n}` is not linear, but it is *comparable* to linear on the
range that matters, because `a ≥ 1`. -/

/-- **Shifting `a` up.**  `min{1, (a+c)/√n} ≤ (1+c) min{1, a/√n}` for `a ≥ 1`, `c ≥ 0`. -/
lemma min_one_div_sqrt_add_le {a c : ℝ} {n : ℕ} (ha : 1 ≤ a) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    min 1 ((a + c) / Real.sqrt n) ≤ (1 + c) * min 1 (a / Real.sqrt n) := by
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hs0 : (0 : ℝ) < Real.sqrt n := lt_of_lt_of_le one_pos hs
  have hstep : (a + c) / Real.sqrt n ≤ (1 + c) * (a / Real.sqrt n) := by
    rw [div_le_iff₀ hs0]
    have : (1 + c) * (a / Real.sqrt n) * Real.sqrt n = (1 + c) * a := by
      field_simp
    rw [this]
    nlinarith
  refine le_trans (min_le_min le_rfl hstep) ?_
  exact min_one_mul_le (by linarith)

/-- **Shifting `a` down.**  `½ min{1, a/√n} ≤ min{1, (a-c)/√n}` once `2c ≤ a`. -/
lemma half_min_one_div_sqrt_le {a c : ℝ} {n : ℕ} (hc : 2 * c ≤ a) (hn : 1 ≤ n) :
    1 / 2 * min 1 (a / Real.sqrt n) ≤ min 1 ((a - c) / Real.sqrt n) := by
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hs0 : (0 : ℝ) < Real.sqrt n := lt_of_lt_of_le one_pos hs
  have hhalf : a / Real.sqrt n / 2 ≤ (a - c) / Real.sqrt n := by
    rw [div_div, div_le_div_iff₀ (by positivity) hs0]
    nlinarith
  refine le_trans ?_ (min_le_min le_rfl hhalf)
  rcases le_or_gt 1 (a / Real.sqrt n) with h | h
  · rw [min_eq_left h]
    rcases le_or_gt 1 (a / Real.sqrt n / 2) with h2 | h2
    · rw [min_eq_left h2]; norm_num
    · rw [min_eq_right h2.le]; linarith
  · rw [min_eq_right h.le, min_eq_right (by linarith : a / Real.sqrt n / 2 ≤ 1)]
    linarith

/-! ### Proposition 5: restarting the barrier at time `k`

Proposition 5 is the intermediate goal.  `L m` is the log-modulus of the `m`-th block Euler
product and `P` the tilted measure; the `+ j` in the upper barrier is the drift that Lemma 4
removes.

The upper half of Proposition 5 cannot use the envelope on all of `[1,n]` for the same reason the
lower half could not: `M j ≥ a + Bj` is unaffordable at small `j`, where the window-mass budget
`(1/40)e^{(j+θ)/2}` is still a constant.  At *large* `j` there is no difficulty at all — the budget
grows exponentially in `j` while the requirement grows linearly.

Harper's answer is to discard the first `⌊a⌋` steps.  On the barrier event `S_{⌊a⌋}` is pinned to
`[-a - B⌊a⌋,\, a + ⌊a⌋ + h(⌊a⌋)]`, so the *suffix* walk `S_j - S_{⌊a⌋}` obeys a barrier whose
constant is `O(a)` — and the budget available at index `j > ⌊a⌋` is `e^{(a+θ)/2}`, exponential in
`a`.  Since the bound is only wanted when `a < √n`, discarding `⌊a⌋` of `n` steps is free.

The three ingredients are below.  The suffix walk itself is already available:
`RMF.IsGaussianWalk.shift` makes it a Gaussian walk of the same class, and `RMF.walk_shift`
identifies `S'_i` with `S_{k+i} - S_k`. -/

omit [MeasurableSpace Ω] in
/-- **The barrier, restarted at `k`.**  On the event, `S_k` is pinned between `u k` and `v k`, so
the suffix walk obeys the difference barrier.  Both endpoints lose exactly the width of the pin. -/
lemma barrierEvent_subset_suffix {X : ℕ → Ω → ℝ} {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    {u v : ℕ → ℝ} :
    barrierEvent X n u v
      ⊆ barrierEvent (fun m => X (m + k)) (n - k)
          (fun i => u (k + i) - v k) (fun i => v (k + i) - u k) := by
  intro ω hω i hi1 hin
  have hbk := Set.mem_Icc.1 (hω k hk1 hkn)
  have hbi := Set.mem_Icc.1 (hω (k + i) (by omega) (by omega))
  simp only at hbk hbi ⊢
  rw [Set.mem_Icc, walk_shift]
  exact ⟨by linarith [hbi.1, hbk.2], by linarith [hbi.2, hbk.1]⟩

/-- Splitting a `range (k + j)` sum at `k`, in the `m + k` convention `RMF.walk_shift` uses. -/
lemma sum_range_add_shift {f : ℕ → ℝ} (k j : ℕ) :
    (∑ m ∈ Finset.range (k + j), f m)
      = (∑ m ∈ Finset.range k, f m) + ∑ m ∈ Finset.range j, f (m + k) := by
  rw [Finset.sum_range_add]
  exact congrArg _ (Finset.sum_congr rfl fun m _ => by rw [add_comm])

/-- The window widths still sum to `2` along the suffix — there are fewer of them, and they are
non-negative. -/
lemma sum_shift_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {n k : ℕ} (hkn : k ≤ n)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) :
    ∀ j, j ≤ n - k → ∑ m ∈ Finset.range j, w (m + k) ≤ 2 := by
  intro j hj
  have h1 := hwsum (k + j) (by omega)
  rw [sum_range_add_shift] at h1
  have h2 : (0 : ℝ) ≤ ∑ m ∈ Finset.range k, w m := Finset.sum_nonneg fun m _ => hw m
  linarith

/-- **The window comparison, restarted at `k`.**  `RMF.proposition5_upper` applies Lemma 4 to the
suffix, so it needs Lemma 3's conclusion for the suffix family.  The unshifted `IsWindowComparison`
controls only grid points with `|c m| ≤ M m`, so the first `k` coordinates cannot be marginalised
away; the suffix comparison is rebuilt from the same per-block data, which
`RMF.isWindowComparison_of_indep` uses one coordinate at a time.  The discarded prefix only lowers
the `ε`-budget. -/
theorem isWindowComparison_shift_of_indep {P : Measure Ω} {Q : Measure Ω'}
    {X : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {w M : ℕ → ℝ} {n k : ℕ}
    {ε : ℕ → ℝ} {E : ℝ}
    (hXi : iIndepFun X P) (hNi : iIndepFun N Q) (hkn : k ≤ n)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2)
    (hcmp : ∀ m, m < n → IsWindowComparison₁ P Q (X m) (N m) (w m) (M m) (ε m)) :
    IsWindowComparison P Q (fun m => X (m + k)) (fun m => N (m + k))
      (fun m => w (m + k)) (fun m => M (m + k)) (n - k) (2 * E) := by
  refine isWindowComparison_of_indep (ε := fun m => ε (m + k))
    (hXi.precomp fun x y h => by omega) (hNi.precomp fun x y h => by omega)
    (fun m hm => hε0 _ (by omega)) ?_ hE (fun m hm => hcmp _ (by omega))
  have hsplit := sum_range_add_shift (f := ε) k (n - k)
  rw [show k + (n - k) = n from by omega] at hsplit
  have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.range k, ε m :=
    Finset.sum_nonneg fun m hm => hε0 m (by have := Finset.mem_range.1 hm; omega)
  linarith

/-- **The drift along the suffix.**  Both the prefix and the whole are within `C` of their index,
so their difference is within `2C` of the suffix length.  This is the only place the suffix pays
for the restart, and it pays a constant. -/
lemma drift_shift_le {θ : ℕ → ℝ} {C : ℝ} {n k : ℕ} (hkn : k ≤ n)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) :
    ∀ i, i ≤ n - k → |(∑ m ∈ Finset.range i, θ (m + k)) - i| ≤ 2 * C := by
  intro i hi
  have h1 := hθ (k + i) (by omega)
  have h2 := hθ k (by omega)
  rw [sum_range_add_shift] at h1
  have hcast : (((k + i : ℕ)) : ℝ) = (k : ℝ) + (i : ℝ) := by push_cast; ring
  rw [hcast] at h1
  have := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith [this.1, this.2, h2'.1, h2'.2]

/-- **The log correction, re-indexed.**  Probability Result 1 wants `|h(i)| ≤ 10 log i` at the
*suffix* index, but what the barrier supplies is `10 log (k+i)`.  The two differ by `log k + log 2`,
a constant once `k` is fixed — which is why the suffix threshold is `O(a + log a)` and not worse.

The inequality is `k + i ≤ 2ki`, i.e. `1/i + 1/k ≤ 2`, true for any `k, i ≥ 1`. -/
lemma log_natCast_add_le {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) :
    Real.log ((k : ℝ) + i) ≤ Real.log k + Real.log i + Real.log 2 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hle : (k : ℝ) + i ≤ 2 * ((k : ℝ) * i) := by nlinarith
  calc Real.log ((k : ℝ) + i)
      ≤ Real.log (2 * ((k : ℝ) * i)) := Real.log_le_log (by positivity) hle
    _ = Real.log 2 + (Real.log k + Real.log i) := by
        rw [Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by linarith) (by linarith)]
    _ = Real.log k + Real.log i + Real.log 2 := by ring

/-- **Rescaling the suffix.**  Dropping steps and inflating `a` by a factor `K` costs only a
constant, provided at least half the steps survive: `min{1, Ka/√m} ≤ √2 K min{1, a/√n}` when
`n ≤ 2m`.  This is what keeps the final bound in terms of `n` and not `n - ⌊a⌋`. -/
lemma min_one_div_sqrt_suffix_le {a K : ℝ} {n m : ℕ} (hK : 1 ≤ K) (ha : 0 ≤ a)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ 2 * m) :
    min 1 (K * a / Real.sqrt m) ≤ Real.sqrt 2 * K * min 1 (a / Real.sqrt n) := by
  have hm0 : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hn0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hsn : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt m := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hnm)
  have hstep : K * a / Real.sqrt m ≤ Real.sqrt 2 * K * (a / Real.sqrt n) := by
    rw [div_le_iff₀ hm0]
    have hcalc : Real.sqrt 2 * K * (a / Real.sqrt n) * Real.sqrt m
        = K * a * (Real.sqrt 2 * Real.sqrt m / Real.sqrt n) := by
      field_simp
    rw [hcalc]
    have hge : (1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt m / Real.sqrt n := (one_le_div hn0).2 hsn
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K) ha]
  refine le_trans (min_le_min le_rfl hstep) (min_one_mul_le ?_)
  nlinarith [h2, hK]

/-! ### The Gaussian side at Harper's capped barriers

Probability Result 2 is stated for the *centred* walk `G`, at a barrier of its own shape.  What
Lemma 4 compares against is `N = G + θ`, at that barrier **narrowed by whatever Lemma 4 widened**.
The step between the two — clip the lower barrier so it holds at `j = 0`, check the cap survives
the shift, remove the drift — does not depend on the amount of narrowing, so it is stated once
with the narrowing as a parameter.  `RMF.proposition5_lower` uses it at `narrow = 2`, Lemma 4's
own widening.

The slope carries the narrowing too, `B₂ + narrow + C`: with `a` capped away there is nothing else
left to absorb the widening and the drift. -/

/-- **Probability Result 2, transported to the drifted walk at the capped barriers.** -/
theorem le_measure_barrierEvent_capped_of_result1Lower {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {G N : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo : ∀ i, vmin ≤ (v i : ℝ)) (hvhi : ∀ i, (v i : ℝ) ≤ vmax)
    {R : ℝ} (hR : Result1LowerOn G Q vmin R (result1LowerConst vmin vmax))
    {θ : ℕ → ℝ} {C narrow a : ℝ} {n : ℕ} {hf : ℕ → ℝ}
    (hC : 0 ≤ C) (hnar : 0 ≤ narrow)
    (hNG : ∀ m ω, N m ω = G m ω + θ m)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C)
    (ha : result2ThresholdOf R + narrow + C ≤ a) (hn : 1 ≤ n)
    (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    result1LowerConst vmin vmax / 2 * min 1 ((a - narrow - C) / Real.sqrt n)
      ≤ (Q (barrierEvent N n
            (fun j => -((result2Slope vmin vmax + narrow + C) * j) + narrow)
            (fun j => min a ((result2Slope vmin vmax + narrow + C) * j)
              + j + hf j - narrow))).toReal := by
  have hres2 := probabilityResult2_of_result1Lower hGw ⟨hvmin, hvlo, hvhi⟩ hR
  set B₂ := result2Slope vmin vmax with hB₂d
  -- the lower barrier fed to Result 2, clipped so that `g j ≤ -(B₂ j)` holds at `j = 0`
  have hgeq : ∀ j : ℕ, 1 ≤ j →
      min (-((B₂ + narrow + C) * j) + narrow - j + C) (-(B₂ * j))
        = -((B₂ + narrow + C) * j) + narrow - j + C := by
    intro j hj1
    refine min_eq_left ?_
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    nlinarith [hj1', hC, hnar]
  -- the cap survives the shift
  have hcap : ∀ j : ℕ, 1 ≤ j →
      min (a - narrow - C) (B₂ * j) + narrow + C ≤ min a ((B₂ + narrow + C) * j) := by
    intro j hj1
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    rcases le_total ((B₂ + narrow + C) * j) a with h | h
    · rw [min_eq_right h]
      nlinarith [min_le_right (a - narrow - C) (B₂ * j), hj1', hC, hnar]
    · rw [min_eq_left h]
      linarith [min_le_left (a - narrow - C) (B₂ * j)]
  have hr2 := (hres2 (a - narrow - C) (by linarith) n hn hbig hbig2 hf
    (fun j => min (-((B₂ + narrow + C) * j) + narrow - j + C) (-(B₂ * j))) hhf
    (fun j => min_le_right _ _)).1
  have hsub : {ω | ∀ j, 1 ≤ j → j ≤ n →
        min (-((B₂ + narrow + C) * j) + narrow - j + C) (-(B₂ * j)) ≤ walk G j ω ∧
          walk G j ω ≤ min (a - narrow - C) (B₂ * j) + hf j}
      ⊆ barrierEvent G n (fun j => -((B₂ + narrow + C) * j) + narrow - j + C)
          (fun j => min a ((B₂ + narrow + C) * j) + j + hf j - narrow - j - C) := by
    intro ω hω j hj1 hjn
    obtain ⟨hlo, hhi⟩ := hω j hj1 hjn
    rw [hgeq j hj1] at hlo
    rw [Set.mem_Icc]
    exact ⟨by simp only; linarith, by simp only; linarith [hcap j hj1]⟩
  have hsub2 := barrierEvent_recentre_subset (N := N) (G := G) hNG hθ
    (u := fun j => -((B₂ + narrow + C) * j) + narrow)
    (v := fun j => min a ((B₂ + narrow + C) * j) + j + hf j - narrow)
  exact le_trans hr2
    (ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono (le_trans hsub hsub2)))

/-- **The drifted Gaussian barrier probability from above.**  The mirror of
`RMF.le_measure_barrierEvent_capped_of_result1Lower`, with no cap: capping only keeps `a` out of
the comparison's envelope, and this is a statement about the Gaussian walk alone, so the lower
barrier is dropped and Probability Result 1 does the work.  `s` is the widening applied before
(`2` for Lemma 4, `2 + K` after the shear), and it costs the factor `1 + s + C`. -/
theorem measure_barrierEvent_drift_le_of_threshold {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {G N : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo : ∀ i, vmin ≤ (v i : ℝ)) (hvhi : ∀ i, (v i : ℝ) ≤ vmax)
    {θ : ℕ → ℝ} {C s a : ℝ} {n : ℕ} {hf u v' : ℕ → ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hNG : ∀ m ω, N m ω = G m ω + θ m)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C)
    (hv : ∀ j, 1 ≤ j → j ≤ n → v' j ≤ a + s + j + hf j)
    {R : ℝ} (hR : 1000 ≤ R) (ha : max 1 R ≤ a) (hn : 1 ≤ n)
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    (Q (barrierEvent N n u v')).toReal
      ≤ result1Const vmin vmax * (1 + s + C) * min 1 (a / Real.sqrt n) := by
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haT : R ≤ a := le_trans (le_max_right _ _) ha
  have hr1 := hGw.measure_forall_le_le ⟨hvmin, hvlo, hvhi⟩ (a := a + (s + C)) (by linarith) hn
    hbig hbig2 (fun j hj1 hjn => le_trans (le_abs_self _) (hhf j hj1 hjn))
  have hshift := barrierEvent_recentre (N := N) (G := G) hθ (u := u) (v := v') (hNG := hNG)
  have hsub : barrierEvent N n u v'
      ⊆ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + (s + C) + hf j} := by
    intro ω hω j hj1 hjn
    have h := Set.mem_Icc.1 (hshift hω j hj1 hjn)
    have hvj := hv j hj1 hjn
    simp only at h
    linarith [h.2]
  refine le_trans (le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)) hr1) ?_
  have hmm := min_one_div_sqrt_add_le (a := a) (c := s + C) (n := n) ha1 (by linarith) hn
  have hrc : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) :=
    le_min zero_le_one (div_nonneg (by linarith) (Real.sqrt_nonneg _))
  nlinarith [hmm, hrc, hmin0]

/-! ### The lower bound, with an envelope that does not see `a`

An envelope hypothesis asking `M j` to dominate the barriers **as stated**, which contain `a`, is
not Harper's hypothesis, and it is not satisfiable for the `a` the application needs: `hM` would
force `M 1 ≥ a + 1 + h(1)`, `hMM` then `M' 0 ≥ a`, and the window-mass bound caps `M' 0` at
`(1/40)√(log x₁) + 2` with `log x₁ = e^{1+θ}` a constant.  So `a = O_θ(1)`, while Harper applies
Proposition 5 with `a → ∞`.

Harper's device is to *shrink the event first*: he proves the lower bound for
`-Bj ≤ S_j ≤ min{a, Bj} + j + h(j)`, whose envelope is `Bj + j + h(j)` — no `a` — and then widens
on the observed side, where widening is free.  The cap `min{a, Bj}` is the shape Probability
Result 2 delivers (`RMF.probabilityResult2_of_result1Lower`), and it is kept until after
Lemma 4. -/

/-- **Proposition 5, lower bound** (Harper).  Under the comparison, the walk stays in
`[-a - Bj, a + j + h(j)]` for `1 ≤ j ≤ n` with probability `≥ (c/8)·min{1, a/√n}`, where
`c = RMF.result1LowerConst vmin vmax`.  The envelope `M` has to dominate only the capped barriers
`B'j` and `B'j + j + h(j)` at `B' = result2Slope vmin vmax + 2 + C` (no `a`), and any `B ≥ B'` is
allowed: the slope absorbs Lemma 4's widening and the drift, so `B` can be fixed independently of
`a`, `n` and `x`. -/
theorem proposition5_lower_of_result1Lower {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {G : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo : ∀ i, vmin ≤ (v i : ℝ)) (hvhi : ∀ i, (v i : ℝ) ≤ vmax)
    {R : ℝ} (hR : Result1LowerOn G Q vmin R (result1LowerConst vmin vmax))
    {θ : ℕ → ℝ} {C B : ℝ} (hC : 0 ≤ C)
    (hB : result2Slope vmin vmax + 2 + C ≤ B) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ) (N : ℕ → Ω' → ℝ)
        (w M M' : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        (∀ m, Measurable (L m)) → (∀ m, Measurable (N m)) →
        (∀ m ω, N m ω = G m ω + θ m) →
        (∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) →
        (∀ m, 0 < w m) →
        (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) →
        (∀ j, 0 ≤ M j) →
        -- **the envelope, at Harper's capped barriers**: no `a`
        (∀ j, 1 ≤ j → j ≤ n →
          (result2Slope vmin vmax + 2 + C) * j ≤ M j ∧
            (result2Slope vmin vmax + 2 + C) * j + j + hf j ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        0 ≤ ε → ε ≤ 1 / 2 → IsWindowComparison P Q L N w M' n ε →
        max (max 1 (result2ThresholdOf R + 2 + C)) (4 + 2 * C) ≤ a → 1 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          result1LowerConst vmin vmax / 2 / 4 * min 1 (a / Real.sqrt n)
            ≤ (P (barrierEvent L n
                  (fun j => -a - B * j)
                  (fun j => a + j + hf j))).toReal := by
  have hα₂ : (0 : ℝ) < result1LowerConst vmin vmax / 2 := by
    linarith [result1LowerConst_pos hvmin (lt_of_lt_of_le hvmin ((hvlo 0).trans (hvhi 0)))]
  set B₂ := result2Slope vmin vmax with hB₂d
  set a₀₂ := result2ThresholdOf R with ha₀₂d
  set α₂ := result1LowerConst vmin vmax / 2 with hα₂d
  intro P hP L N w M M' n ε a hf hL hN hNG hθ hw hwsum hM0 hMcap hMM hε0 hε hcmp ha hn hbig
    hbig2 hhf
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha2 : a₀₂ + 2 + C ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha4 : 4 + 2 * C ≤ a := le_trans (le_max_right _ _) ha
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  -- Result 2, transported to the drifted walk at the capped barriers
  have hchain := le_measure_barrierEvent_capped_of_result1Lower hGw hvmin hvlo hvhi hR hC
    (by norm_num : (0 : ℝ) ≤ 2) hNG hθ ha2 hn hbig hbig2 hhf
  rw [← hB₂d, ← hα₂d] at hchain
  -- Lemma 4, lower — at the capped barriers, where the envelope is `a`-free
  have hM' : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ -((B₂ + 2 + C) * j) ∧
      min a ((B₂ + 2 + C) * j) + j + hf j ≤ M j := by
    intro j hj1 hjn
    obtain ⟨h1, h2⟩ := hMcap j hj1 hjn
    exact ⟨by linarith, by linarith [min_le_right a ((B₂ + 2 + C) * j)]⟩
  have h4 := le_measure_barrierEvent hL hN hw hwsum hM0 hM' hMM hcmp
  -- widening back to the stated barrier, on the observed side where it is free
  have hwide : barrierEvent L n (fun j => -((B₂ + 2 + C) * j))
        (fun j => min a ((B₂ + 2 + C) * j) + j + hf j)
      ⊆ barrierEvent L n (fun j => -a - B * j) (fun j => a + j + hf j) := by
    intro ω hω j hj1 hjn
    have hb := Set.mem_Icc.1 (hω j hj1 hjn)
    have hBj : (B₂ + 2 + C) * (j : ℝ) ≤ B * (j : ℝ) :=
      mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg j)
    simp only at hb ⊢
    rw [Set.mem_Icc]
    exact ⟨by linarith [hb.1], by linarith [hb.2, min_le_left a ((B₂ + 2 + C) * (j : ℝ))]⟩
  have hlast : (P (barrierEvent L n (fun j => -((B₂ + 2 + C) * j))
        (fun j => min a ((B₂ + 2 + C) * j) + j + hf j))).toReal
      ≤ (P (barrierEvent L n (fun j => -a - B * j)
            (fun j => a + j + hf j))).toReal :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hwide)
  have hhalf : 1 / 2 * min 1 (a / Real.sqrt n) ≤ min 1 ((a - 2 - C) / Real.sqrt n) := by
    have := half_min_one_div_sqrt_le (a := a) (c := 2 + C) (n := n) (by linarith) hn
    simpa only [show a - (2 + C) = a - 2 - C by ring] using this
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) := le_min zero_le_one (by positivity)
  nlinarith [h4, hchain, hhalf, hlast, hα₂.le, hmin0,
    ENNReal.toReal_nonneg (a := Q (barrierEvent N n (fun j => -((B₂ + 2 + C) * j) + 2)
      (fun j => min a ((B₂ + 2 + C) * j) + j + hf j - 2)))]

/-- **Proposition 5, lower bound**, at Result 1's iterated-logarithm constants. -/
theorem proposition5_lower {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {G : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo : ∀ i, vmin ≤ (v i : ℝ)) (hvhi : ∀ i, (v i : ℝ) ≤ vmax)
    {θ : ℕ → ℝ} {C B : ℝ} (hC : 0 ≤ C)
    (hB : result2Slope vmin vmax + 2 + C ≤ B) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ) (N : ℕ → Ω' → ℝ)
        (w M M' : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        (∀ m, Measurable (L m)) → (∀ m, Measurable (N m)) →
        (∀ m ω, N m ω = G m ω + θ m) →
        (∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) →
        (∀ m, 0 < w m) →
        (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) →
        (∀ j, 0 ≤ M j) →
        -- **the envelope, at Harper's capped barriers**: no `a`
        (∀ j, 1 ≤ j → j ≤ n →
          (result2Slope vmin vmax + 2 + C) * j ≤ M j ∧
            (result2Slope vmin vmax + 2 + C) * j + j + hf j ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        0 ≤ ε → ε ≤ 1 / 2 → IsWindowComparison P Q L N w M' n ε →
        max (max 1 (result2Threshold vmin vmax + 2 + C)) (4 + 2 * C) ≤ a → 1 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          result1LowerConst vmin vmax / 2 / 4 * min 1 (a / Real.sqrt n)
            ≤ (P (barrierEvent L n
                  (fun j => -a - B * j)
                  (fun j => a + j + hf j))).toReal :=
  proposition5_lower_of_result1Lower hGw hvmin hvlo hvhi
    ((result1Lower_iteratedLog vmin vmax).on hGw ⟨hvmin, hvlo, hvhi⟩) hC hB

set_option maxHeartbeats 1000000 in
-- The suffix argument threads a single event through four containments and Probability Result 1;
-- the resulting `isDefEq` checks between the barrier events exceed the default budget.
/-- **Proposition 5, upper bound** (Harper), with the envelope required only above `a`.  The event
is *enlarged* rather than shrunk: on it the walk is pinned at time `⌊a⌋`, so the suffix walk obeys
a barrier with constant `O(a)`, and Lemma 4 is applied to the suffix alone.  The envelope is then
needed only at `j > a`, where the window-mass budget `e^{(j+θ)/2}` is exponential in `a` while the
requirement `(3+B)a + Bj + j + 20 log j` is linear, so a constant `θ` suffices.

Discarding `⌊a⌋` of the `n` steps is free because for `a ≥ √n` the bound is trivial; so the
hypothesis is `4 ≤ n`, not `2⌊a⌋ ≤ n`, which would be unsatisfiable for large `a`. -/
theorem proposition5_upper_of_threshold {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {G : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo : ∀ i, vmin ≤ (v i : ℝ)) (hvhi : ∀ i, (v i : ℝ) ≤ vmax)
    {θ : ℕ → ℝ} {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B) {R : ℝ} (hR : 1000 ≤ R) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ) (N : ℕ → Ω' → ℝ)
        (w M M' : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        (∀ m, Measurable (L m)) → (∀ m, Measurable (N m)) →
        (∀ m ω, N m ω = G m ω + θ m) →
        (∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) →
        (∀ m, 0 < w m) →
        (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) →
        (∀ j, 0 ≤ M j) →
        -- **the envelope, required only above `a`**
        (∀ j : ℕ, a < (j : ℝ) → j ≤ n →
          (3 + B) * a + B * j + j + 20 * Real.log j ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        0 ≤ ε → ε ≤ 1 / 2 →
        -- the comparison, for the suffix that starts at `⌊a⌋`
        IsWindowComparison P Q (fun m => L (m + ⌊a⌋₊)) (fun m => N (m + ⌊a⌋₊))
          (fun m => w (m + ⌊a⌋₊)) (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) ε →
        max 1 R ≤ a → 4 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (P (barrierEvent L n (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
            ≤ 2 * result1Const vmin vmax
                * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2))
              * min 1 (a / Real.sqrt n) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hRC : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  have h2s : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hKpos : (15 : ℝ) ≤ 15 + B + 2 * C + 10 * Real.log 2 := by linarith
  intro P hP L N w M M' n ε a hf hL hN hNG hθ hw hwsum hM0 hMup hMM hε0 hε hcmp ha hn4 hbig
    hbig2 hhf
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haT : R ≤ a := le_trans (le_max_right _ _) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hn1 : 1 ≤ n := by omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn4' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) := le_min zero_le_one (by positivity)
  have hprob : (P (barrierEvent L n (fun j => -a - B * j)
      (fun j => a + j + hf j))).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by norm_num) prob_le_one
  have hSK : (1 : ℝ) ≤ Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2) := by
    nlinarith [h2s, hKpos]
  have hAge : (1 : ℝ) ≤ 2 * result1Const vmin vmax
      * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2)) := by
    nlinarith [hRC, hSK]
  rcases le_or_gt (Real.sqrt n) a with htriv | hsmall
  · -- `a ≥ √n`: the cap is `1` and there is nothing to prove
    have h1 : min 1 (a / Real.sqrt n) = 1 :=
      min_eq_left (by rw [le_div_iff₀ hsn]; linarith)
    rw [h1, mul_one]
    linarith [hprob, hAge]
  · -- `a < √n`: restart at `k = ⌊a⌋`
    set k := ⌊a⌋₊ with hkdef
    have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast ha1)
    have hka : ((⌊a⌋₊ : ℕ) : ℝ) ≤ a := Nat.floor_le ha0
    have hak : a < ((⌊a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
    have hsq : (2 : ℝ) ≤ Real.sqrt n := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), Real.sqrt_nonneg (n : ℝ)]
    have hkn2 : 2 * ⌊a⌋₊ ≤ n := by
      have hr : 2 * ((⌊a⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith)]
      exact_mod_cast hr
    have hkn : ⌊a⌋₊ ≤ n := by omega
    have hnk1 : 1 ≤ n - ⌊a⌋₊ := by omega
    have hklog : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
    have hiR0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    -- the suffix data, re-indexed
    have hLs : ∀ m, Measurable (L (m + k)) := fun m => hL _
    have hNs : ∀ m, Measurable (N (m + k)) := fun m => hN _
    have hws : ∀ m, 0 < w (m + k) := fun m => hw _
    have hwsums := sum_shift_le (fun m => (hw m).le) hkn hwsum
    have hM0s : ∀ j, 0 ≤ M (k + j) := fun j => hM0 _
    have hMMs : ∀ m, m < n - k →
        M (k + m) + M (k + (m + 1)) + w (m + k) ≤ M' (m + k) := by
      intro m hm
      have h := hMM (k + m) (by omega)
      rw [show m + k = k + m from Nat.add_comm m k]
      exact h
    -- the envelope, read at the suffix indices — this is where `hMup`'s `a < j` is used
    have hMs : ∀ i, 1 ≤ i → i ≤ n - k →
        -M (k + i) ≤ (-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k) ∧
          (a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ)) ≤ M (k + i) := by
      intro i hi1 hin
      have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      have hki : a < ((k + i : ℕ) : ℝ) := by push_cast; linarith [hak]
      have hkin : k + i ≤ n := by omega
      have henv := hMup (k + i) hki hkin
      have hlogki : Real.log k ≤ Real.log ((k + i : ℕ) : ℝ) := by
        refine Real.log_le_log (by exact_mod_cast hk1) ?_
        push_cast
        linarith
      have hlogki0 : (0 : ℝ) ≤ Real.log ((k + i : ℕ) : ℝ) := le_trans hklog hlogki
      have habs1 := abs_le.1 (hhf k hk1 hkn)
      have habs2 := abs_le.1 (hhf (k + i) (by omega) hkin)
      have hBa : (0 : ℝ) ≤ B * a := mul_nonneg hB.le ha0
      have hBi : (0 : ℝ) ≤ B * (i : ℝ) := mul_nonneg hB.le (Nat.cast_nonneg i)
      push_cast at henv habs2 hlogki hlogki0 ⊢
      rw [show (3 + B) * a = 3 * a + B * a from by ring,
        show B * ((k : ℝ) + (i : ℝ)) = B * (k : ℝ) + B * (i : ℝ) from by ring] at henv
      exact ⟨by linarith [habs1.2, hlogki], by linarith [habs2.2]⟩
    -- Lemma 4, on the suffix
    have h4 := measure_barrierEvent_le (X := fun m => L (m + k)) (N := fun m => N (m + k))
      (w := fun m => w (m + k)) (M := fun j => M (k + j)) (M' := fun m => M' (m + k))
      (n := n - k)
      (u := fun i => (-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k))
      (v := fun i => (a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ)))
      hLs hNs hws hwsums hM0s hMs hε0 hMMs hcmp
    -- the stated event sits inside the suffix event
    have hP1 : (P (barrierEvent L n (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
        ≤ (P (barrierEvent (fun m => L (m + k)) (n - k)
              (fun i => (-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k))
              (fun i => (a + ((k + i : ℕ) : ℝ) + hf (k + i))
                - (-a - B * (k : ℝ))))).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _)
        (measure_mono (barrierEvent_subset_suffix (X := L) (n := n) (k := k)
          (u := fun j => -a - B * (j : ℝ)) (v := fun j => a + (j : ℝ) + hf j) hk1 hkn))
    -- drift removal along the suffix, at cost `2C`
    have hNGs : ∀ m ω, N (m + k) ω = G (m + k) ω + θ (m + k) := fun m ω => hNG _ _
    have hshift := barrierEvent_recentre (N := fun m => N (m + k)) (G := fun m => G (m + k))
      (θ := fun m => θ (m + k)) (C := 2 * C) (n := n - k) hNGs (drift_shift_le hkn hθ)
      (u := fun i => ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2)
      (v := fun i => ((a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ))) + 2)
    -- drop the lower barrier; the `+ i` cancels against the drift, leaving `a'`
    have hstep2 : barrierEvent (fun m => G (m + k)) (n - k)
          (fun i => (((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2)
            - i - 2 * C)
          (fun i => (((a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ))) + 2)
            - i + 2 * C)
        ⊆ {ω | ∀ i, 1 ≤ i → i ≤ n - k → walk (fun m => G (m + k)) i ω
            ≤ (2 * a + (1 + B) * (k : ℝ) + 10 * Real.log k + 10 * Real.log 2 + 2 + 2 * C)
              + 10 * Real.log i} := by
      intro ω hω i hi1 hin
      have hb := Set.mem_Icc.1 (hω i hi1 hin)
      have habs2 := abs_le.1 (hhf (k + i) (by omega) (by omega))
      have hlog := log_natCast_add_le hk1 hi1
      push_cast at hb habs2
      linarith [hb.2, habs2.2, hlog]
    -- Probability Result 1 on the shifted walk
    have hlogn0 : (0 : ℝ) ≤ Real.log ((n - k : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hnk1)
    have hlognk : Real.log ((n - k : ℕ) : ℝ) ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hnk1) (by exact_mod_cast Nat.sub_le n k)
    have hnkR : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by
      have h : n ≤ 2 * (n - k) := by omega
      exact_mod_cast h
    have hbig' : 2 * Real.log ((n - k : ℕ) : ℝ) ^ 20 ≤ ((n - k : ℕ) : ℝ) := by
      have hp : Real.log ((n - k : ℕ) : ℝ) ^ 20 ≤ Real.log n ^ 20 := by gcongr
      linarith
    have hbig2' : 2 * Real.log ((n - k : ℕ) : ℝ) ^ 8 ≤ ((n - k : ℕ) : ℝ) * vmin := by
      have hp : Real.log ((n - k : ℕ) : ℝ) ^ 8 ≤ Real.log n ^ 8 := by gcongr
      nlinarith only [hp, hbig2, hvmin, hnkR]
    have hlogk_le : Real.log k ≤ a := by
      have h1 : Real.log (k : ℝ) ≤ (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by exact_mod_cast hk1)
      linarith [hka]
    have haT' : R
        ≤ 2 * a + (1 + B) * (k : ℝ) + 10 * Real.log k + 10 * Real.log 2 + 2 + 2 * C := by
      nlinarith only [haT, ha0, hklog, hlog2.le, hiR0, hC,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + B) hiR0]
    have hr1 := (hGw.shift k).measure_forall_le_le ⟨hvmin, fun i => hvlo (i + k),
      fun i => hvhi (i + k)⟩ (le_trans hR haT') hnk1 hbig' hbig2'
      (hf := fun i => 10 * Real.log i) (fun j _ _ => le_rfl)
    -- assemble
    have hQsub : (Q (barrierEvent (fun m => N (m + k)) (n - k)
          (fun i => ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2)
          (fun i => ((a + ((k + i : ℕ) : ℝ) + hf (k + i))
            - (-a - B * (k : ℝ))) + 2))).toReal
        ≤ (Q {ω | ∀ i, 1 ≤ i → i ≤ n - k → walk (fun m => G (m + k)) i ω
            ≤ (2 * a + (1 + B) * (k : ℝ) + 10 * Real.log k + 10 * Real.log 2 + 2 + 2 * C)
              + 10 * Real.log i}).toReal :=
      ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono (le_trans hshift hstep2))
    have hQ1 := le_trans hQsub hr1
    -- `a' ≤ K a`, and the suffix rescaling
    have hKa : 2 * a + (1 + B) * (k : ℝ) + 10 * Real.log k + 10 * Real.log 2 + 2 + 2 * C
        ≤ (15 + B + 2 * C + 10 * Real.log 2) * a := by
      nlinarith only [hka, hlogk_le, ha1, hC, hB.le, hlog2.le, mul_nonneg hB.le ha0]
    have hsk : (0 : ℝ) < Real.sqrt ((n - k : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hnk1)
    have hmono : min 1 ((2 * a + (1 + B) * (k : ℝ) + 10 * Real.log k + 10 * Real.log 2
          + 2 + 2 * C) / Real.sqrt ((n - k : ℕ) : ℝ))
        ≤ min 1 ((15 + B + 2 * C + 10 * Real.log 2) * a
            / Real.sqrt ((n - k : ℕ) : ℝ)) := min_le_min le_rfl (by gcongr)
    have hresc := min_one_div_sqrt_suffix_le (a := a) (K := 15 + B + 2 * C + 10 * Real.log 2)
      (n := n) (m := n - k) (by linarith) ha0 hn1 hnk1 (by omega)
    have hRC0 : (0 : ℝ) < result1Const vmin vmax := by linarith
    have hbase : (0 : ℝ) ≤ result1Const vmin vmax
        * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2) * min 1 (a / Real.sqrt n)) := by
      refine mul_nonneg hRC0.le (mul_nonneg ?_ hmin0)
      nlinarith only [hKpos, Real.sqrt_nonneg 2, h2s]
    have hchain : (P (barrierEvent L n (fun j => -a - B * j)
          (fun j => a + j + hf j))).toReal
        ≤ (1 + ε) * (result1Const vmin vmax
            * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2)
              * min 1 (a / Real.sqrt n))) := by
      refine le_trans hP1 (le_trans h4 ?_)
      refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ 1 + ε)
      exact le_trans hQ1 (mul_le_mul_of_nonneg_left (le_trans hmono hresc) hRC0.le)
    refine le_trans hchain ?_
    have hfin : (1 + ε) * (result1Const vmin vmax
          * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2) * min 1 (a / Real.sqrt n)))
        ≤ 2 * (result1Const vmin vmax
          * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2) * min 1 (a / Real.sqrt n))) := by
      nlinarith only [mul_nonneg (show (0 : ℝ) ≤ 1 - ε by linarith) hbase]
    refine le_trans hfin (le_of_eq ?_)
    ring

/-- **Proposition 5, upper bound**, at Result 1's lower threshold `RMF.result1Threshold`, which
is above the `1000` the suffix needs. -/
theorem proposition5_upper {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {G : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo : ∀ i, vmin ≤ (v i : ℝ)) (hvhi : ∀ i, (v i : ℝ) ≤ vmax)
    {θ : ℕ → ℝ} {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ) (N : ℕ → Ω' → ℝ)
        (w M M' : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        (∀ m, Measurable (L m)) → (∀ m, Measurable (N m)) →
        (∀ m ω, N m ω = G m ω + θ m) →
        (∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C) →
        (∀ m, 0 < w m) →
        (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) →
        (∀ j, 0 ≤ M j) →
        -- **the envelope, required only above `a`**
        (∀ j : ℕ, a < (j : ℝ) → j ≤ n →
          (3 + B) * a + B * j + j + 20 * Real.log j ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        0 ≤ ε → ε ≤ 1 / 2 →
        -- the comparison, for the suffix that starts at `⌊a⌋`
        IsWindowComparison P Q (fun m => L (m + ⌊a⌋₊)) (fun m => N (m + ⌊a⌋₊))
          (fun m => w (m + ⌊a⌋₊)) (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) ε →
        max 1 (result1Threshold vmin vmax) ≤ a → 4 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (P (barrierEvent L n (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
            ≤ 2 * result1Const vmin vmax
                * (Real.sqrt 2 * (15 + B + 2 * C + 10 * Real.log 2))
              * min 1 (a / Real.sqrt n) :=
  proposition5_upper_of_threshold hGw hvmin hvlo hvhi hC hB (thousand_le_result1Threshold vmin vmax)

end RMF
