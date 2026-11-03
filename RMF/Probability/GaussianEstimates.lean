/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The one-dimensional Gaussian

Everything the barrier argument needs to know about `gaussianReal`, collected here so that the
probabilistic development elsewhere never has to compute with densities.

* *the density*, bounded above by `(√(2π v))⁻¹` everywhere (`RMF.gaussianPDFReal_le`) and below
  by `(√(2π v))⁻¹ e^{-c²/2v}` on `[-c, c]` (`RMF.le_gaussianPDFReal_of_abs_le`);
* *anti-concentration*, `P(N(0,v) ∈ [b, b+c]) ≤ c/√(2π v)` (`RMF.measure_Icc_gaussianReal_le`),
  and the matching lower bound on a symmetric interval (`RMF.le_measure_Icc_gaussianReal`);
* *symmetry*, `P(N(0,v) ≥ 0) ≥ 1/2` (`RMF.half_le_gaussianReal_Ici`), the input to the
  reflection argument;
* *scaling*, `N(0,V) = √V · N(0,1)` (`RMF.gaussianReal_map_sqrt_mul`);
* *absolute moments*, `E|N(0,V)|ᵖ = E|N(0,1)|ᵖ · V^(p/2)` (`RMF.integral_abs_pow_gaussianReal`);
* *the tail integral* `E[(N(0,V) - a)⁺] ≤ e^{Vt²/2 - ta}/(et)` for every `t > 0`
  (`RMF.integral_posPart_sub_le_mgf`);
* *a crossing probability*, `P(N(0,V) > y) ≥ ρ` as soon as `y² ≤ V`, for any `ρ ≤ P(N(0,1) > 1)`,
  with no upper bound on `V` (`RMF.le_measure_Ioi_gaussianReal_of`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The density -/

/-- The Gaussian density never exceeds `(√(2π v))⁻¹`. -/
lemma gaussianPDFReal_le (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (√(2 * π * v))⁻¹ := by
  have hexp : rexp (-(x - m) ^ 2 / (2 * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  have hc : (0 : ℝ) ≤ (√(2 * π * v))⁻¹ := by positivity
  calc gaussianPDFReal m v x = (√(2 * π * v))⁻¹ * rexp (-(x - m) ^ 2 / (2 * v)) := rfl
    _ ≤ (√(2 * π * v))⁻¹ * 1 := by gcongr
    _ = (√(2 * π * v))⁻¹ := mul_one _

/-- On `[-c, c]` the centred Gaussian density is at least its value at the endpoints. -/
lemma le_gaussianPDFReal_of_abs_le {v : ℝ≥0} {c x : ℝ} (hx : |x| ≤ c) :
    (√(2 * π * v))⁻¹ * rexp (-c ^ 2 / (2 * v)) ≤ gaussianPDFReal 0 v x := by
  have hxc : x ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hexp : rexp (-c ^ 2 / (2 * v)) ≤ rexp (-(x - 0) ^ 2 / (2 * v)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [sub_zero]
    rcases eq_or_ne v 0 with hv | hv
    · simp [hv]
    · have hv2 : (0 : ℝ) < 2 * (v : ℝ) := by positivity
      gcongr
  calc (√(2 * π * v))⁻¹ * rexp (-c ^ 2 / (2 * v))
      ≤ (√(2 * π * v))⁻¹ * rexp (-(x - 0) ^ 2 / (2 * v)) := by gcongr
    _ = gaussianPDFReal 0 v x := rfl

/-! ### Anti-concentration and symmetry -/

/-- A centred Gaussian of variance `V` is `√V` times a standard one. -/
lemma gaussianReal_map_sqrt_mul (V : ℝ≥0) :
    (gaussianReal 0 1).map (fun z => √(V : ℝ) * z) = gaussianReal 0 V := by
  have hc := gaussianReal_map_const_mul (μ := 0) (v := 1) (√(V : ℝ))
  rw [mul_zero] at hc
  convert hc using 2
  ext
  simp [Real.sq_sqrt V.coe_nonneg]

/-- **A Gaussian puts little mass on a short interval**, in `ℝ≥0∞` form.  An interval of length `c`
carries at most `c` times the maximal density.  The `ℝ≥0∞` statement is the one that survives being
placed inside a `lintegral`, which is what an independent random shift requires. -/
lemma measure_Icc_gaussianReal_le_ofReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (b c : ℝ) :
    gaussianReal m v (Set.Icc b (b + c)) ≤ ENNReal.ofReal (c / √(2 * π * v)) := by
  have hpos : (0 : ℝ) < √(2 * π * v) := by
    have : (0 : ℝ) < (v : ℝ) := by positivity
    positivity
  rw [gaussianReal_apply _ hv]
  calc ∫⁻ x in Set.Icc b (b + c), gaussianPDF m v x
      ≤ ∫⁻ _ in Set.Icc b (b + c), ENNReal.ofReal ((√(2 * π * v))⁻¹) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (gaussianPDFReal_le m v x)
    _ = ENNReal.ofReal ((√(2 * π * v))⁻¹) * volume (Set.Icc b (b + c)) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (c / √(2 * π * v)) := by
        rw [Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **A Gaussian puts little mass on a short interval.**  An interval of length `c` carries at
most `c` times the maximal density. -/
lemma measure_Icc_gaussianReal_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (gaussianReal m v (Set.Icc b (b + c))).toReal ≤ c / √(2 * π * v) := by
  have hpos : (0 : ℝ) < √(2 * π * v) := by
    have : (0 : ℝ) < (v : ℝ) := by positivity
    positivity
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (measure_Icc_gaussianReal_le_ofReal m hv b c)

/-- **The collar of a window.**  The two `δ`-neighbourhoods of the endpoints of `[a, b]` together
carry at most `4δ` times the maximal density.

This is the `K` of `RMF.isWindowComparison₁_of_swap`: it is the price of replacing an indicator by
a `C³` window, and it is the term that pushes *against* the swap error as `δ` varies — the swap
wants `δ` large, the collar wants it small. -/
lemma measure_collar_gaussianReal_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (gaussianReal m v (Set.Icc (a - δ) (a + δ) ∪ Set.Icc (b - δ) (b + δ))).toReal
      ≤ 4 * δ / √(2 * π * v) := by
  have hpos : (0 : ℝ) < √(2 * π * v) := by
    have : (0 : ℝ) < (v : ℝ) := by positivity
    positivity
  have hrwa : Set.Icc (a - δ) (a + δ) = Set.Icc (a - δ) ((a - δ) + 2 * δ) := by
    congr 1; ring
  have hrwb : Set.Icc (b - δ) (b + δ) = Set.Icc (b - δ) ((b - δ) + 2 * δ) := by
    congr 1; ring
  have hA := measure_Icc_gaussianReal_le m hv (a - δ) (c := 2 * δ) (by linarith)
  have hB := measure_Icc_gaussianReal_le m hv (b - δ) (c := 2 * δ) (by linarith)
  rw [← hrwa] at hA
  rw [← hrwb] at hB
  have hle := measure_union_le (μ := gaussianReal m v)
    (Set.Icc (a - δ) (a + δ)) (Set.Icc (b - δ) (b + δ))
  have htop : gaussianReal m v (Set.Icc (a - δ) (a + δ))
      + gaussianReal m v (Set.Icc (b - δ) (b + δ)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  refine le_trans (ENNReal.toReal_mono htop hle) ?_
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have : 2 * δ / √(2 * π * v) + 2 * δ / √(2 * π * v) = 4 * δ / √(2 * π * v) := by ring
  linarith

/-- **Anti-concentration survives an independent shift.**  If `X` is `N(0, V)` and `M` is *any*
measurable variable independent of it, then `X + M` puts at most `c/√(2πV)` on an interval of
length `c`: conditioning on `M` moves the interval but not its length.  Nothing about `M` beyond
independence is used; in Harper's (A2) it is the running maximum of the second half of the walk. -/
lemma measure_add_mem_Icc_le_of_indepFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X M : Ω → ℝ} {V : ℝ≥0} (hV : V ≠ 0)
    (hX : Measurable X) (hM : Measurable M) (hindep : IndepFun X M μ)
    (hlaw : μ.map X = gaussianReal 0 V) (b c : ℝ) :
    μ {ω | X ω + M ω ∈ Set.Icc b (b + c)} ≤ ENNReal.ofReal (c / √(2 * π * V)) := by
  have : IsProbabilityMeasure (μ.map M) := Measure.isProbabilityMeasure_map hM.aemeasurable
  set S : Set (ℝ × ℝ) := {p | p.2 + p.1 ∈ Set.Icc b (b + c)} with hSdef
  have hS : MeasurableSet S := (measurable_snd.add measurable_fst) measurableSet_Icc
  have hset : {ω | X ω + M ω ∈ Set.Icc b (b + c)} = (fun ω => (M ω, X ω)) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply (hM.prodMk hX) hS,
    hindep.symm.map_prod_eq_prod_map_map hM.aemeasurable hX.aemeasurable,
    Measure.prod_apply hS, hlaw]
  calc ∫⁻ m, gaussianReal 0 V (Prod.mk m ⁻¹' S) ∂(μ.map M)
      ≤ ∫⁻ _, ENNReal.ofReal (c / √(2 * π * V)) ∂(μ.map M) := by
        refine lintegral_mono fun m => ?_
        have hslice : Prod.mk m ⁻¹' S = Set.Icc (b - m) ((b - m) + c) := by
          ext x
          simp only [hSdef, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
        rw [hslice]
        exact measure_Icc_gaussianReal_le_ofReal 0 hV _ c
    _ = ENNReal.ofReal (c / √(2 * π * V)) := by simp

/-- The `ℝ≥0∞` form of the window bound, for a half-open interval. -/
lemma measure_Ioc_gaussianReal_le {v : ℝ≥0} (hv : v ≠ 0) (b : ℝ) (c : ℝ) :
    gaussianReal 0 v (Set.Ioc b (b + c)) ≤ ENNReal.ofReal ((√(2 * π * v))⁻¹ * c) := by
  rw [gaussianReal_apply _ hv, ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ x in Set.Ioc b (b + c), gaussianPDF 0 v x
      ≤ ∫⁻ _ in Set.Ioc b (b + c), ENNReal.ofReal ((√(2 * π * v))⁻¹) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (gaussianPDFReal_le 0 v x)
    _ = ENNReal.ofReal ((√(2 * π * v))⁻¹) * ENNReal.ofReal c := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, add_sub_cancel_left]

/-- **A Gaussian puts substantial mass on a window around its mean.** -/
lemma le_measure_Icc_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    ENNReal.ofReal (2 * c * rexp (-c ^ 2 / (2 * v)) / √(2 * π * v))
      ≤ gaussianReal 0 v (Set.Icc (-c) c) := by
  have hpos : (0 : ℝ) < √(2 * π * v) := by
    have : (0 : ℝ) < (v : ℝ) := by positivity
    positivity
  rw [gaussianReal_apply _ hv]
  calc ENNReal.ofReal (2 * c * rexp (-c ^ 2 / (2 * v)) / √(2 * π * v))
      = ENNReal.ofReal ((√(2 * π * v))⁻¹ * rexp (-c ^ 2 / (2 * v))) * ENNReal.ofReal (c - -c) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ∫⁻ _ in Set.Icc (-c) c,
          ENNReal.ofReal ((√(2 * π * v))⁻¹ * rexp (-c ^ 2 / (2 * v))) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    _ ≤ ∫⁻ x in Set.Icc (-c) c, gaussianPDF 0 v x := by
        refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
        exact ENNReal.ofReal_le_ofReal (le_gaussianPDFReal_of_abs_le (abs_le.mpr ⟨hx.1, hx.2⟩))

/-- **A shifted window, from below.**  For `[b, b+h] ⊆ [-c, c]`,
`P(b ≤ N(0,V) ≤ b+h) ≥ h·e^{-c²/2V}/√(2πV)`: over the window the centred density is at least its
value at `±c`.  `RMF.le_measure_Icc_gaussianReal` is the case `b = -c`, `h = 2c`.  This lower bound
turns the additive error of a Lindeberg swap into a multiplicative one; the two-point analogue is
`RMF.le_measure_tilted_box`. -/
lemma le_measure_Icc_gaussianReal_shift {v : ℝ≥0} (hv : v ≠ 0) {b h c : ℝ}
    (hb : -c ≤ b) (hbh : b + h ≤ c) :
    ENNReal.ofReal (h * rexp (-c ^ 2 / (2 * v)) / √(2 * π * v))
      ≤ gaussianReal 0 v (Set.Icc b (b + h)) := by
  have hpos : (0 : ℝ) < √(2 * π * v) := by
    have : (0 : ℝ) < (v : ℝ) := by positivity
    positivity
  rw [gaussianReal_apply _ hv]
  calc ENNReal.ofReal (h * rexp (-c ^ 2 / (2 * v)) / √(2 * π * v))
      = ENNReal.ofReal ((√(2 * π * v))⁻¹ * rexp (-c ^ 2 / (2 * v)))
          * ENNReal.ofReal (b + h - b) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ∫⁻ _ in Set.Icc b (b + h),
          ENNReal.ofReal ((√(2 * π * v))⁻¹ * rexp (-c ^ 2 / (2 * v))) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    _ ≤ ∫⁻ x in Set.Icc b (b + h), gaussianPDF 0 v x := by
        refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
        refine ENNReal.ofReal_le_ofReal (le_gaussianPDFReal_of_abs_le ?_)
        exact abs_le.mpr ⟨le_trans hb hx.1, le_trans hx.2 hbh⟩

/-- **The shifted window at its own envelope.**  `RMF.le_measure_Icc_gaussianReal_shift` at
`c = |b| + h`, the smallest `c` containing the window, with no `c` left to choose.  The
normalisation `≥ h·x^{-9/1600}` is then real arithmetic: under `|b| + h ≤ (1/40)√(log x) + C` and
`e⁻² ≤ 2V ≤ e²` the exponent is at least `-(e²/1600)·log x` up to `O(√(log x))`, and
`(9-e²)/1600` per `log x` absorbs the rest. -/
lemma le_measure_Icc_gaussianReal_envelope {v : ℝ≥0} (hv : v ≠ 0) {b h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (h * rexp (-(|b| + h) ^ 2 / (2 * v)) / √(2 * π * v))
      ≤ gaussianReal 0 v (Set.Icc b (b + h)) :=
  le_measure_Icc_gaussianReal_shift hv
    (by linarith [neg_abs_le b, abs_nonneg b]) (by linarith [le_abs_self b])

/-- **The normalisation, with the envelope's slope `κ` and the exponent `E` as parameters.**
From `c ≤ κ√(log x) + C` and `1/A ≤ 2V ≤ B`, `x^{-E} ≤ e^{-c²/2V}/√(2πV)` once `hthr` holds, by one
completed square, `c² ≤ κ²L + 2κC√L + C²` with `L = log x`.  **`Aκ² < E` is the whole constraint.**
`RMF.rpow_le_exp_neg_sq_div_of_bounds` is the case `κ = 1/40`, `E = 9/1600`, reading `A < 9`;
the two-point box needs the general form, its sheared corner having a slope other than `1/40`. -/
lemma rpow_le_exp_neg_sq_div_of_slope {V c C x A B κ E : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * V) (hV₂ : 2 * V ≤ B) (hx : 1 ≤ x) (hc0 : 0 ≤ c)
    (hc : c ≤ κ * √(Real.log x) + C)
    (hthr : 2 * A * κ * C * √(Real.log x) + A * C ^ 2 + Real.log (π * B) / 2
      ≤ (E - A * κ ^ 2) * Real.log x) :
    x ^ (-E) ≤ rexp (-c ^ 2 / (2 * V)) / √(2 * π * V) := by
  have hL : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have ht : √(Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hL
  have ht0 : (0 : ℝ) ≤ √(Real.log x) := Real.sqrt_nonneg _
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hV0 : (0 : ℝ) < V := by
    have : (0 : ℝ) < 1 / A := by positivity
    linarith
  -- the envelope, squared — no sign on `κ` is needed, the expansion is an identity
  have hcsq : c ^ 2 ≤ κ ^ 2 * Real.log x + 2 * κ * C * √(Real.log x) + C ^ 2 := by
    have := pow_le_pow_left₀ hc0 hc 2
    nlinarith [ht]
  -- the exponent: `1/(2V) ≤ A`
  have hexp : rexp (-(A * c ^ 2)) ≤ rexp (-c ^ 2 / (2 * V)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by linarith)]
    have hsq0 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
    have hinv : (1 : ℝ) ≤ A * (2 * V) := by
      have hmul := mul_le_mul_of_nonneg_left hV₁ hA.le
      rwa [mul_one_div, div_self hA.ne'] at hmul
    nlinarith
  -- the normalisation: `2V ≤ B`
  have hden : √(2 * π * V) ≤ √(π * B) := by
    refine Real.sqrt_le_sqrt ?_
    have hrw : (2 : ℝ) * π * V = π * (2 * V) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hV₂ hpi.le
  have hden0 : (0 : ℝ) < √(2 * π * V) := Real.sqrt_pos.2 (by positivity)
  have hlhs : x ^ (-E) = rexp (-E * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  rw [hlhs, le_div_iff₀ hden0]
  calc rexp (-E * Real.log x) * √(2 * π * V)
      ≤ rexp (-E * Real.log x) * √(π * B) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = rexp (-E * Real.log x + Real.log (π * B) / 2) := by
        have hsp : rexp (Real.log (π * B) / 2) = √(π * B) := by
          rw [← Real.log_sqrt (by positivity), Real.exp_log (Real.sqrt_pos.2 (by positivity))]
        rw [Real.exp_add, hsp]
    _ ≤ rexp (-(A * c ^ 2)) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [hcsq, hA, mul_le_mul_of_nonneg_left hcsq hA.le]
    _ ≤ rexp (-c ^ 2 / (2 * V)) := hexp

/-- **The normalisation, with the variance bounds as parameters.**  Under `1/A ≤ 2V ≤ B` and the
envelope `|b| + h ≤ (1/40)√(log x) + C`, `x^{-9/1600} ≤ e^{-(|b|+h)²/2V}/√(2πV)` once `hthr` holds.
Block Mertens gives `2V` only up to a factor `1 + O(1/log x_j)`, so it can fall just outside
`[e^{-2}, e²]`; here `A` may exceed `e²` as long as `A < 9`, a relative slack of `1 - e²/9 = 0.179`
in the lower bound on `2V`. -/
lemma rpow_le_exp_neg_sq_div_of_bounds {V b h C x A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * V) (hV₂ : 2 * V ≤ B) (hx : 1 ≤ x)
    (hc : |b| + h ≤ 1 / 40 * √(Real.log x) + C) (hc0 : 0 ≤ |b| + h)
    (hthr : A / 20 * C * √(Real.log x) + A * C ^ 2 + Real.log (π * B) / 2
      ≤ (9 - A) / 1600 * Real.log x) :
    x ^ (-(9 : ℝ) / 1600) ≤ rexp (-(|b| + h) ^ 2 / (2 * V)) / √(2 * π * V) := by
  have h := rpow_le_exp_neg_sq_div_of_slope (κ := 1 / 40) (E := 9 / 1600) hA hB hV₁ hV₂ hx
    hc0 hc (by
      rw [show (9 : ℝ) / 1600 - A * (1 / 40 : ℝ) ^ 2 = (9 - A) / 1600 from by ring,
        show 2 * A * (1 / 40 : ℝ) * C = A / 20 * C from by ring]
      exact hthr)
  rw [show (-(9 : ℝ) / 1600) = -((9 : ℝ) / 1600) from by ring]
  exact h

/-- **The window bound, with the variance bounds as parameters.**  Given `1/A ≤ 2v ≤ B`, a window
of width `h` inside Harper's envelope `|b| + h ≤ (1/40)√(log x) + C` carries mass at least
`h·x^{-9/1600}` once `hthr` holds, which has `(9 - A)/1600` per `log x` to spend.  This is the form
block Mertens can discharge; `RMF.rpow_le_exp_neg_sq_div_of_bounds` explains why `A < 9` binds. -/
lemma le_measure_Icc_gaussianReal_normalised_of_bounds {v : ℝ≥0} (hv : v ≠ 0) {b h C x A B : ℝ}
    (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * (v : ℝ)) (hV₂ : 2 * (v : ℝ) ≤ B) (hx : 1 ≤ x)
    (hc : |b| + h ≤ 1 / 40 * √(Real.log x) + C)
    (hthr : A / 20 * C * √(Real.log x) + A * C ^ 2 + Real.log (π * B) / 2
      ≤ (9 - A) / 1600 * Real.log x) :
    ENNReal.ofReal (h * x ^ (-(9 : ℝ) / 1600)) ≤ gaussianReal 0 v (Set.Icc b (b + h)) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (le_measure_Icc_gaussianReal_envelope hv hh)
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hh
  exact rpow_le_exp_neg_sq_div_of_bounds hA hB hV₁ hV₂ hx hc (by linarith [abs_nonneg b]) hthr

/-- **A Gaussian of positive variance has no atoms**, so half-open and closed windows carry the
same mass.  This lets `IsWindowComparison₁`, whose windows are half-open (so that distinct grid
slices are disjoint), be fed by the closed-window bound
`RMF.le_measure_Icc_gaussianReal_normalised_of_bounds`. -/
lemma measure_Ioc_gaussianReal_eq_Icc {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) :
    gaussianReal m v (Set.Ioc a b) = gaussianReal m v (Set.Icc a b) := by
  have hsingle : gaussianReal m v {a} = 0 :=
    gaussianReal_absolutelyContinuous m hv (by simp)
  refine le_antisymm (measure_mono Set.Ioc_subset_Icc_self) ?_
  have hsub : Set.Icc a b ⊆ Set.Ioc a b ∪ {a} := by
    intro z hz
    rcases eq_or_lt_of_le hz.1 with hz' | hz'
    · exact Or.inr (Set.mem_singleton_iff.2 hz'.symm)
    · exact Or.inl ⟨hz', hz.2⟩
  calc gaussianReal m v (Set.Icc a b)
      ≤ gaussianReal m v (Set.Ioc a b ∪ {a}) := measure_mono hsub
    _ ≤ gaussianReal m v (Set.Ioc a b) + gaussianReal m v {a} := measure_union_le _ _
    _ = gaussianReal m v (Set.Ioc a b) := by rw [hsingle, add_zero]

/-- The lower bound on a window, in the half-open form the comparison uses. -/
lemma le_measure_Ioc_gaussianReal_normalised_of_bounds {v : ℝ≥0} (hv : v ≠ 0)
    {b h C x A B : ℝ} (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * (v : ℝ)) (hV₂ : 2 * (v : ℝ) ≤ B) (hx : 1 ≤ x)
    (hc : |b| + h ≤ 1 / 40 * √(Real.log x) + C)
    (hthr : A / 20 * C * √(Real.log x) + A * C ^ 2 + Real.log (π * B) / 2
      ≤ (9 - A) / 1600 * Real.log x) :
    ENNReal.ofReal (h * x ^ (-(9 : ℝ) / 1600)) ≤ gaussianReal 0 v (Set.Ioc b (b + h)) := by
  rw [measure_Ioc_gaussianReal_eq_Icc hv]
  exact le_measure_Icc_gaussianReal_normalised_of_bounds hv hh hA hB hV₁ hV₂ hx hc hthr

/-! ### The window bound at a Gaussian that is not centred

`RMF.le_measure_Ioc_gaussianReal_normalised_of_bounds` is stated at mean `0`, but the Gaussian the
block increment is compared to has mean `blockMean ≈ 1` per block — Harper's drift.  Translating is
elementary, and the only thing it costs is that the envelope has to absorb `|m|`. -/

/-- **Translating a window.**  `N(m, v)` on `(c, c+h]` is `N(0, v)` on `(c-m, c-m+h]`. -/
lemma measure_Ioc_gaussianReal_shift (m : ℝ) (v : ℝ≥0) (c h : ℝ) :
    gaussianReal m v (Set.Ioc c (c + h))
      = gaussianReal 0 v (Set.Ioc (c - m) ((c - m) + h)) := by
  have hmap : gaussianReal m v = (gaussianReal 0 v).map (· + m) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [hmap, Measure.map_apply (by fun_prop) measurableSet_Ioc]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The window bound at a Gaussian that is not centred, in real form** — the shape of the block
comparison's `hqlow`.  Against `RMF.le_measure_Ioc_gaussianReal_normalised_of_bounds` the mean is
`m` and the envelope hypothesis is `M + |m| + h ≤ (1/40)√(log x) + C`, Harper's envelope with the
drift `|m|` added, since `|c - m| ≤ M + |m|`; with `m ≈ 1` per block it is absorbed easily. -/
theorem le_toReal_measure_Ioc_gaussianReal_of_bounds {v : ℝ≥0} (hv : v ≠ 0)
    {m c h C x A B M : ℝ} (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * (v : ℝ)) (hV₂ : 2 * (v : ℝ) ≤ B) (hx : 1 ≤ x)
    (hc : |c| ≤ M) (henv : M + |m| + h ≤ 1 / 40 * √(Real.log x) + C)
    (hthr : A / 20 * C * √(Real.log x) + A * C ^ 2 + Real.log (π * B) / 2
      ≤ (9 - A) / 1600 * Real.log x) :
    h * x ^ (-(9 : ℝ) / 1600) ≤ (gaussianReal m v (Set.Ioc c (c + h))).toReal := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hnn : (0 : ℝ) ≤ h * x ^ (-(9 : ℝ) / 1600) := by positivity
  -- the translated window sits inside the envelope
  have hshift : |c - m| + h ≤ 1 / 40 * √(Real.log x) + C := by
    have : |c - m| ≤ |c| + |m| := by
      simpa using abs_sub (a := c) (b := m)
    linarith
  have hkey := le_measure_Ioc_gaussianReal_normalised_of_bounds hv hh hA hB hV₁ hV₂ hx hshift hthr
  rw [← measure_Ioc_gaussianReal_shift] at hkey
  have hfin : gaussianReal m v (Set.Ioc c (c + h)) ≠ ⊤ := measure_ne_top _ _
  have := ENNReal.toReal_mono hfin hkey
  rwa [ENNReal.toReal_ofReal hnn] at this

/-! ### The same bound with the threshold supplied directly

`RMF.rpow_le_exp_neg_sq_div_of_bounds` reaches its threshold through Harper's envelope
`u ≤ (1/40)√(log x) + C`: it squares that, and so spends `A·log x/1600` on the leading term
whether or not `u` is anywhere near so large.  The surplus `(9 - A)/1600` left afterwards is the
*only* reason `A` has to stay below `9` — which, through `1/A ≤ 2V` and `2V ≥ e^{-2η}`, is what caps
the tilt scale at `η < log 3`.

The lemmas below take the inequality the argument actually uses, `A·u² + log(πB)/2 ≤ τ·log x`, and
are otherwise the same proof with the squaring step deleted.  **There is no cap on `A`.**  In the
block application `u ≈ M + |m_B| + h` with `M ≈ a + Bj`, linear in the block index, against
`log x_j = e^{j+1+θ}` — so a large `A` is paid for in `θ`, and `RMF.thr_direct_of_offset` is where
that price is named. -/

/-- **The Gaussian factor at a directly-supplied threshold.**

`x^{-τ} ≤ e^{-u²/(2V)}/√(2πV)` whenever `A·u² + log(πB)/2 ≤ τ·log x`, given `1/A ≤ 2V ≤ B`.

Two steps and no envelope: `1/(2V) ≤ A` bounds the exponent, `2V ≤ B` the normalisation.  Compare
`RMF.rpow_le_exp_neg_sq_div_of_bounds`, which is this with `u` replaced by a proxy for it. -/
lemma rpow_le_exp_neg_sq_div_of_thr {V u x A B τ : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * V) (hV₂ : 2 * V ≤ B) (hx : 1 ≤ x)
    (hthr : A * u ^ 2 + Real.log (π * B) / 2 ≤ τ * Real.log x) :
    x ^ (-τ) ≤ rexp (-u ^ 2 / (2 * V)) / √(2 * π * V) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hV0 : (0 : ℝ) < V := by
    have : (0 : ℝ) < 1 / A := by positivity
    linarith
  -- the exponent: `1/(2V) ≤ A`
  have hexp : rexp (-(A * u ^ 2)) ≤ rexp (-u ^ 2 / (2 * V)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by linarith)]
    have hsq0 : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
    have hinv : (1 : ℝ) ≤ A * (2 * V) := by
      have hmul := mul_le_mul_of_nonneg_left hV₁ hA.le
      rwa [mul_one_div, div_self hA.ne'] at hmul
    nlinarith
  -- the normalisation: `2V ≤ B`
  have hden : √(2 * π * V) ≤ √(π * B) := by
    refine Real.sqrt_le_sqrt ?_
    have hrw : (2 : ℝ) * π * V = π * (2 * V) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hV₂ hpi.le
  have hden0 : (0 : ℝ) < √(2 * π * V) := Real.sqrt_pos.2 (by positivity)
  have hlhs : x ^ (-τ) = rexp (-τ * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  rw [hlhs, le_div_iff₀ hden0]
  calc rexp (-τ * Real.log x) * √(2 * π * V)
      ≤ rexp (-τ * Real.log x) * √(π * B) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = rexp (-τ * Real.log x + Real.log (π * B) / 2) := by
        have hsp : rexp (Real.log (π * B) / 2) = √(π * B) := by
          rw [← Real.log_sqrt (by positivity), Real.exp_log (Real.sqrt_pos.2 (by positivity))]
        rw [Real.exp_add, hsp]
    _ ≤ rexp (-(A * u ^ 2)) := Real.exp_le_exp.2 (by linarith)
    _ ≤ rexp (-u ^ 2 / (2 * V)) := hexp

/-- **The closed window at a directly-supplied threshold** —
`RMF.le_measure_Icc_gaussianReal_normalised_of_bounds` with the envelope step removed. -/
lemma le_measure_Icc_gaussianReal_normalised_of_thr {v : ℝ≥0} (hv : v ≠ 0) {b h x A B τ : ℝ}
    (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * (v : ℝ)) (hV₂ : 2 * (v : ℝ) ≤ B) (hx : 1 ≤ x)
    (hthr : A * (|b| + h) ^ 2 + Real.log (π * B) / 2 ≤ τ * Real.log x) :
    ENNReal.ofReal (h * x ^ (-τ)) ≤ gaussianReal 0 v (Set.Icc b (b + h)) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (le_measure_Icc_gaussianReal_envelope hv hh)
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hh
  exact rpow_le_exp_neg_sq_div_of_thr hA hB hV₁ hV₂ hx hthr

/-- The same, in the half-open form the window comparison uses. -/
lemma le_measure_Ioc_gaussianReal_normalised_of_thr {v : ℝ≥0} (hv : v ≠ 0) {b h x A B τ : ℝ}
    (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * (v : ℝ)) (hV₂ : 2 * (v : ℝ) ≤ B) (hx : 1 ≤ x)
    (hthr : A * (|b| + h) ^ 2 + Real.log (π * B) / 2 ≤ τ * Real.log x) :
    ENNReal.ofReal (h * x ^ (-τ)) ≤ gaussianReal 0 v (Set.Ioc b (b + h)) := by
  rw [measure_Ioc_gaussianReal_eq_Icc hv]
  exact le_measure_Icc_gaussianReal_normalised_of_thr hv hh hA hB hV₁ hV₂ hx hthr

/-- **The window bound at a directly-supplied threshold, off-centre and in real form** — the shape
the block comparison's `hqlow` asks for, with no envelope in it.

The translation costs `|c - m| ≤ M + |m|` exactly as in
`RMF.le_toReal_measure_Ioc_gaussianReal_of_bounds`; here that is spent inside `hthr` rather than
against a proxy for it, which is the whole difference. -/
theorem le_toReal_measure_Ioc_gaussianReal_of_thr {v : ℝ≥0} (hv : v ≠ 0)
    {m c h x A B M τ : ℝ} (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < B)
    (hV₁ : 1 / A ≤ 2 * (v : ℝ)) (hV₂ : 2 * (v : ℝ) ≤ B) (hx : 1 ≤ x) (hc : |c| ≤ M)
    (hthr : A * (M + |m| + h) ^ 2 + Real.log (π * B) / 2 ≤ τ * Real.log x) :
    h * x ^ (-τ) ≤ (gaussianReal m v (Set.Ioc c (c + h))).toReal := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hnn : (0 : ℝ) ≤ h * x ^ (-τ) := by positivity
  -- the translated window, still inside the threshold
  have hshift : |c - m| + h ≤ M + |m| + h := by
    have : |c - m| ≤ |c| + |m| := by simpa using abs_sub (a := c) (b := m)
    linarith
  have hthr' : A * (|c - m| + h) ^ 2 + Real.log (π * B) / 2 ≤ τ * Real.log x := by
    have hmono : A * (|c - m| + h) ^ 2 ≤ A * (M + |m| + h) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hA.le
      exact pow_le_pow_left₀ (by linarith [abs_nonneg (c - m)]) hshift 2
    linarith
  have hkey := le_measure_Ioc_gaussianReal_normalised_of_thr hv hh hA hB hV₁ hV₂ hx hthr'
  rw [← measure_Ioc_gaussianReal_shift] at hkey
  have hfin : gaussianReal m v (Set.Ioc c (c + h)) ≠ ⊤ := measure_ne_top _ _
  have := ENNReal.toReal_mono hfin hkey
  rwa [ENNReal.toReal_ofReal hnn] at this

/-- **A tilted box contains a product box**, the geometric core of `RMF.le_measure_tilted_box`.
The box `[u,u+h₁] × [v,v+h₂]` is not a product event for `(Z, ρZ + sW)`, but if
`2|ρ|h₁ + sh' ≤ h₂`, every `(z,w) ∈ [u,u+h₁] × [a,a+h']` with `a = (v + |ρ|h₁ - ρu)/s` has
`ρz + sw ∈ [v,v+h₂]`.  The `2|ρ|h₁` is the price of the tilt: `ρ(z-u)` wanders over `±|ρ|h₁`. -/
lemma mem_tilted_box_of_mem_prod {ρ s u h₁ v h₂ h' z w : ℝ} (hs : 0 < s)
    (hh' : 2 * |ρ| * h₁ + s * h' ≤ h₂)
    (hz : z ∈ Set.Icc u (u + h₁))
    (hw : w ∈ Set.Icc ((v + |ρ| * h₁ - ρ * u) / s)
      ((v + |ρ| * h₁ - ρ * u) / s + h')) :
    ρ * z + s * w ∈ Set.Icc v (v + h₂) := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  have hzu : ρ * (z - u) ≤ |ρ| * h₁ := by
    have habs : |ρ * (z - u)| ≤ |ρ| * h₁ := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z - u)]
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ρ)
    exact le_trans (le_abs_self _) habs
  have hzu' : -(|ρ| * h₁) ≤ ρ * (z - u) := by
    have habs : |ρ * (z - u)| ≤ |ρ| * h₁ := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z - u)]
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ρ)
    linarith [neg_abs_le (ρ * (z - u))]
  have hsw1 : v + |ρ| * h₁ - ρ * u ≤ s * w := by
    rw [div_le_iff₀ hs] at hw1
    linarith
  have hsw2 : s * w ≤ v + |ρ| * h₁ - ρ * u + s * h' := by
    have hw2' : w - h' ≤ (v + |ρ| * h₁ - ρ * u) / s := by linarith
    rw [le_div_iff₀ hs] at hw2'
    linarith
  constructor
  · nlinarith
  · nlinarith

/-- **The bivariate box, from below.**  For `Z, W` independent centred Gaussians, the box
`[u,u+h₁] × [v,v+h₂]` has probability under `(Z, ρZ + sW)` at least the product of two shifted
windows: `RMF.mem_tilted_box_of_mem_prod` puts a product box inside it, independence factors that,
and each factor is `RMF.le_measure_Icc_gaussianReal_shift`.  This turns Harper's Lemma 7's additive
swap error into a multiplicative one.  The corners `c₁`, `c₂` are separate: a common one would carry
the sheared corner's `1/s ≈ 4` into the first factor and multiply its exponent by `16`. -/
lemma le_measure_tilted_box {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z W : Ω → ℝ} {V₁ V₂ : ℝ≥0} (hV₁ : V₁ ≠ 0) (hV₂ : V₂ ≠ 0)
    (hZ : μ.map Z = gaussianReal 0 V₁) (hW : μ.map W = gaussianReal 0 V₂)
    (hZm : Measurable Z) (hWm : Measurable W) (hind : IndepFun Z W μ)
    {ρ s u h₁ v h₂ h' c₁ c₂ : ℝ} (hs : 0 < s)
    (hh' : 2 * |ρ| * h₁ + s * h' ≤ h₂)
    (hu : -c₁ ≤ u) (huh : u + h₁ ≤ c₁)
    (ha : -c₂ ≤ (v + |ρ| * h₁ - ρ * u) / s)
    (hah : (v + |ρ| * h₁ - ρ * u) / s + h' ≤ c₂) :
    ENNReal.ofReal (h₁ * rexp (-c₁ ^ 2 / (2 * V₁)) / √(2 * π * V₁))
        * ENNReal.ofReal (h' * rexp (-c₂ ^ 2 / (2 * V₂)) / √(2 * π * V₂))
      ≤ μ {ω | Z ω ∈ Set.Icc u (u + h₁) ∧ ρ * Z ω + s * W ω ∈ Set.Icc v (v + h₂)} := by
  set a : ℝ := (v + |ρ| * h₁ - ρ * u) / s with hadef
  -- the product box sits inside the tilted one
  have hsub : Z ⁻¹' Set.Icc u (u + h₁) ∩ W ⁻¹' Set.Icc a (a + h')
      ⊆ {ω | Z ω ∈ Set.Icc u (u + h₁) ∧ ρ * Z ω + s * W ω ∈ Set.Icc v (v + h₂)} := by
    rintro ω ⟨hz, hw⟩
    exact ⟨hz, mem_tilted_box_of_mem_prod hs hh' hz hw⟩
  refine le_trans ?_ (measure_mono hsub)
  -- independence factors the product box
  rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_Icc measurableSet_Icc]
  have hZI : μ (Z ⁻¹' Set.Icc u (u + h₁)) = gaussianReal 0 V₁ (Set.Icc u (u + h₁)) := by
    rw [← hZ, Measure.map_apply hZm measurableSet_Icc]
  have hWI : μ (W ⁻¹' Set.Icc a (a + h')) = gaussianReal 0 V₂ (Set.Icc a (a + h')) := by
    rw [← hW, Measure.map_apply hWm measurableSet_Icc]
  rw [hZI, hWI]
  exact mul_le_mul' (le_measure_Icc_gaussianReal_shift hV₁ hu huh)
    (le_measure_Icc_gaussianReal_shift hV₂ ha hah)

/-- **The centring bridge.**  `RMF.le_measure_tilted_box` for the pair `(m₁ + Z, m₂ + ρZ + sW)`,
by translating the **box**: `m₁ + Z ∈ [u₁, u₁+h₁]` is `Z ∈ [u₁-m₁, u₁-m₁+h₁]`, and likewise in the
second coordinate, so the means appear only in the corners.  They must not be removed by centring
the family: the tilted block increments have mean `≈ 1` per block, Harper's drift, the `-j` in his
barrier. -/
lemma le_measure_box_shifted {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z W : Ω → ℝ} {V₁ V₂ : ℝ≥0} (hV₁ : V₁ ≠ 0) (hV₂ : V₂ ≠ 0)
    (hZ : μ.map Z = gaussianReal 0 V₁) (hW : μ.map W = gaussianReal 0 V₂)
    (hZm : Measurable Z) (hWm : Measurable W) (hind : IndepFun Z W μ)
    {m₁ m₂ ρ s u₁ h₁ v₁ h₂ h' c₁ c₂ : ℝ} (hs : 0 < s)
    (hh' : 2 * |ρ| * h₁ + s * h' ≤ h₂)
    (hu : -c₁ ≤ u₁ - m₁) (huh : u₁ - m₁ + h₁ ≤ c₁)
    (ha : -c₂ ≤ (v₁ - m₂ + |ρ| * h₁ - ρ * (u₁ - m₁)) / s)
    (hah : (v₁ - m₂ + |ρ| * h₁ - ρ * (u₁ - m₁)) / s + h' ≤ c₂) :
    ENNReal.ofReal (h₁ * rexp (-c₁ ^ 2 / (2 * V₁)) / √(2 * π * V₁))
        * ENNReal.ofReal (h' * rexp (-c₂ ^ 2 / (2 * V₂)) / √(2 * π * V₂))
      ≤ μ {ω | m₁ + Z ω ∈ Set.Icc u₁ (u₁ + h₁)
          ∧ m₂ + (ρ * Z ω + s * W ω) ∈ Set.Icc v₁ (v₁ + h₂)} := by
  refine le_trans
    (le_measure_tilted_box hV₁ hV₂ hZ hW hZm hWm hind hs hh' hu huh ha hah) ?_
  refine measure_mono fun ω hω => ?_
  obtain ⟨h1, h2⟩ := hω
  rw [Set.mem_Icc] at h1 h2
  exact ⟨Set.mem_Icc.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩,
    Set.mem_Icc.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

/-- A centred Gaussian puts at least half its mass on the non-negative half line.  (Exactly a
half when the variance is non-zero; all of it when the variance vanishes.) -/
lemma half_le_gaussianReal_Ici (v : ℝ≥0) : 1 / 2 ≤ gaussianReal 0 v (Set.Ici (0 : ℝ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    simp
  · have hsymm : gaussianReal 0 v (Set.Iic (0 : ℝ)) = gaussianReal 0 v (Set.Ici (0 : ℝ)) := by
      have hmap : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
        rw [gaussianReal_map_neg, neg_zero]
      calc gaussianReal 0 v (Set.Iic (0 : ℝ))
          = ((gaussianReal 0 v).map (fun x : ℝ => -x)) (Set.Ici (0 : ℝ)) := by
            rw [Measure.map_apply measurable_neg measurableSet_Ici]
            congr 1
            ext x
            simp
        _ = gaussianReal 0 v (Set.Ici (0 : ℝ)) := by rw [hmap]
    have hcover : gaussianReal 0 v (Set.Iic (0 : ℝ)) + gaussianReal 0 v (Set.Ici (0 : ℝ))
        = 1 + gaussianReal 0 v {(0 : ℝ)} := by
      rw [← measure_union_add_inter₀ _ (measurableSet_Ici.nullMeasurableSet),
        show Set.Iic (0 : ℝ) ∪ Set.Ici 0 = Set.univ by ext x; simp,
        show Set.Iic (0 : ℝ) ∩ Set.Ici 0 = {(0 : ℝ)} by ext x; simp [le_antisymm_iff],
        measure_univ]
    have hatom : gaussianReal 0 v {(0 : ℝ)} = 0 := by
      rw [gaussianReal_apply _ hv]
      simp
    rw [hatom, add_zero, hsymm] at hcover
    have hne : gaussianReal 0 v (Set.Ici (0 : ℝ)) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.add_halves 1] at hcover
    by_contra hcon
    rw [not_le] at hcon
    have : gaussianReal 0 v (Set.Ici (0 : ℝ)) + gaussianReal 0 v (Set.Ici (0 : ℝ))
        < 1 / 2 + 1 / 2 := ENNReal.add_lt_add hcon hcon
    rw [hcover] at this
    exact lt_irrefl _ this

/-- A centred Gaussian puts at least half its mass on the non-positive half line. -/
lemma half_le_gaussianReal_Iic (v : ℝ≥0) : 1 / 2 ≤ gaussianReal 0 v (Set.Iic (0 : ℝ)) := by
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have hsymm : gaussianReal 0 v (Set.Iic (0 : ℝ)) = gaussianReal 0 v (Set.Ici (0 : ℝ)) := by
    calc gaussianReal 0 v (Set.Iic (0 : ℝ))
        = ((gaussianReal 0 v).map (fun x : ℝ => -x)) (Set.Ici (0 : ℝ)) := by
          rw [Measure.map_apply measurable_neg measurableSet_Ici]
          congr 1
          ext x
          simp
      _ = gaussianReal 0 v (Set.Ici (0 : ℝ)) := by rw [hmap]
  rw [hsymm]
  exact half_le_gaussianReal_Ici v

/-- A centred Gaussian is symmetric: the two tails beyond `±c` have equal mass. -/
lemma gaussianReal_Iio_neg_eq_Ioi (v : ℝ≥0) (c : ℝ) :
    gaussianReal 0 v (Set.Iio (-c)) = gaussianReal 0 v (Set.Ioi c) := by
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  calc gaussianReal 0 v (Set.Iio (-c))
      = ((gaussianReal 0 v).map (fun x : ℝ => -x)) (Set.Ioi c) := by
        rw [Measure.map_apply measurable_neg measurableSet_Ioi]
        congr 1
        ext x
        simp
    _ = gaussianReal 0 v (Set.Ioi c) := by rw [hmap]

/-! ### Absolute moments of a Gaussian -/

/-- The `p`-th absolute moment of a standard Gaussian, `E|N(0,1)|ᵖ`;
`RMF.absMomentConst_three_le` evaluates `p = 3`. -/
noncomputable def absMomentConst (p : ℕ) : ℝ := ∫ z, |z| ^ p ∂(gaussianReal 0 1)

lemma integrable_abs_pow_gaussianReal (V : ℝ≥0) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 V) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := V) (p : ℝ≥0∞) (by simp)).integrable_norm_rpow'
  simpa [Real.rpow_natCast, Real.norm_eq_abs] using h

lemma absMomentConst_nonneg (p : ℕ) : 0 ≤ absMomentConst p :=
  integral_nonneg fun _ => by positivity

/-! ### The second and fourth moments of a standard Gaussian

Mathlib's Gaussian moment API stops at the variance.  What carries past it is
`ProbabilityTheory.iteratedDeriv_mgf_zero`, which turns *any* moment into a derivative of the
moment-generating function at `0`:

`iteratedDeriv n (mgf X μ) 0 = μ[X ^ n]`.

Mathlib's own proof of `variance_fun_id_gaussianReal` is precisely the `n = 2` instance of this;
what follows is the `n = 4` one, by the same method.  The side condition
`0 ∈ interior (integrableExpSet …)` is free — `integrableExpSet_fun_id_gaussianReal` is a `simp`
lemma saying the set is all of `ℝ`.

The mgf of `N(0,1)` is `e^{t²/2}`, with derivatives `q_k(t)e^{t²/2}`, `q_{k+1} = q_k' + t q_k`:
`q_2 = 1+t²`, `q_4 = 3+6t²+t⁴`, `q_6 = 15+45t²+15t⁴+t⁶`, so `E Z² = 1`, `E Z⁴ = 3` and
`E Z⁶ = 15`. -/

private lemma deriv_expHalfSq :
    deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t : ℝ => t * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [_root_.deriv_exp (by fun_prop)]
  simp [mul_comm]

private lemma deriv_q1 :
    deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
      = fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_expHalfSq]
  simp
  ring

private lemma deriv_q2 :
    deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
      = fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_expHalfSq]
  simp
  ring

private lemma deriv_cubic :
    deriv (fun u : ℝ => 3 * u + u ^ 3) = fun u : ℝ => 3 + 3 * u ^ 2 := by
  ext u
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop), deriv_id'']
  simp

private lemma deriv_q3 :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2))
      = fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_expHalfSq, deriv_cubic]
  simp
  ring

private lemma mgf_std_gaussian :
    mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t : ℝ => Real.exp (t ^ 2 / 2) := by
  rw [mgf_fun_id_gaussianReal]
  funext t
  norm_num

private lemma zero_mem_interior_integrableExpSet :
    (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
  simp

/-- `E Z² = 1` for a standard Gaussian — the variance, obtained the same way as the fourth
moment so that the two share their derivative computation. -/
lemma integral_sq_gaussianReal : ∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1)
    zero_mem_interior_integrableExpSet 2
  rw [mgf_std_gaussian, iteratedDeriv_succ, iteratedDeriv_one, deriv_expHalfSq, deriv_q1] at h
  simpa using h.symm

/-- **`E Z⁴ = 3`.**  Mathlib stops at the variance; this is the same computation two derivatives
further, and it is what makes the sharp third-moment bound available. -/
lemma integral_pow_four_gaussianReal : ∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1)
    zero_mem_interior_integrableExpSet 4
  rw [mgf_std_gaussian, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_one, deriv_expHalfSq, deriv_q1, deriv_q2, deriv_q3] at h
  simpa using h.symm

/-- `|z|³ ≤ (z⁴ + z²)/2`, which is `z²(|z|-1)² ≥ 0` — AM–GM between the fourth and second
powers.  Equality at `|z| = 1`, so nothing is lost that matters. -/
lemma abs_cube_le_half (z : ℝ) : |z| ^ 3 ≤ (z ^ 4 + z ^ 2) / 2 := by
  have habs : |z| ^ 2 = z ^ 2 := sq_abs z
  have hcube : |z| ^ 3 = z ^ 2 * |z| := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, habs]
  nlinarith [mul_nonneg (sq_nonneg z) (sq_nonneg (|z| - 1)), habs, hcube, abs_nonneg z,
    sq_nonneg z]

/-- **The third absolute moment of a standard Gaussian, sharply enough.**
`E|Z|³ ≤ (E Z⁴ + E Z²)/2 = (3+1)/2 = 2`, by AM–GM; the true value is `2√(2/π) ≈ 1.596`.
This fixes `RMF.blockThirdConst`, and with it the numerical condition of Harper's Lemma 3. -/
theorem absMomentConst_three_le : absMomentConst 3 ≤ 2 := by
  have hi : Integrable (fun z : ℝ => |z| ^ 3) (gaussianReal 0 1) :=
    integrable_abs_pow_gaussianReal 1 3
  have habs4 : ∀ z : ℝ, |z| ^ 4 = z ^ 4 := fun z => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hi4 : Integrable (fun z : ℝ => z ^ 4) (gaussianReal 0 1) :=
    (integrable_abs_pow_gaussianReal 1 4).congr (Filter.Eventually.of_forall habs4)
  have hi2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) :=
    (integrable_abs_pow_gaussianReal 1 2).congr (Filter.Eventually.of_forall fun z => sq_abs z)
  have hb : Integrable (fun z : ℝ => (z ^ 4 + z ^ 2) / 2) (gaussianReal 0 1) :=
    (hi4.add hi2).div_const 2
  have hmono : absMomentConst 3 ≤ ∫ z, (z ^ 4 + z ^ 2) / 2 ∂(gaussianReal 0 1) := by
    rw [absMomentConst]
    exact integral_mono hi hb abs_cube_le_half
  rw [integral_div, integral_add hi4 hi2, integral_pow_four_gaussianReal,
    integral_sq_gaussianReal] at hmono
  norm_num at hmono
  exact hmono

/-- The absolute moments scale: `E|N(0,V)|ᵖ = E|N(0,1)|ᵖ · V^(p/2)`. -/
lemma integral_abs_pow_gaussianReal (V : ℝ≥0) (p : ℕ) :
    ∫ x, |x| ^ p ∂(gaussianReal 0 V) = absMomentConst p * √(V : ℝ) ^ p := by
  calc ∫ x, |x| ^ p ∂(gaussianReal 0 V)
      = ∫ z, |√(V : ℝ) * z| ^ p ∂(gaussianReal 0 1) := by
        rw [← gaussianReal_map_sqrt_mul V, integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ z, √(V : ℝ) ^ p * |z| ^ p ∂(gaussianReal 0 1) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    _ = absMomentConst p * √(V : ℝ) ^ p := by
        rw [integral_const_mul, absMomentConst, mul_comm]

/-! ### The tail integral

`g a = E[(G - a)⁺]` is finite for a centred Gaussian `G`.
-/

lemma integrable_posPart_sub_gaussianReal (V : ℝ≥0) (a : ℝ) :
    Integrable (fun x : ℝ => max (x - a) 0) (gaussianReal 0 V) := by
  have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 V) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  exact (hid.sub (integrable_const a)).sup (integrable_const 0)

/-! ### A uniform crossing probability

A centred Gaussian whose variance is at least `y²` exceeds `y` with probability bounded below by
an absolute constant: `P(N(0,V) > y) ≥ ρ` whenever `y² ≤ V`, for any `ρ ≤ P(N(0,1) > 1)`, for
instance `ρ = 1/8` (`RMF.le_measure_Ioi_one_gaussianReal_eighth`).

No upper bound on `V` is needed.  `P(N(0,V) > y) = Φ(-y/√V)` increases with `V`, so the worst
case is `V = y²`; scaling by `√V` reduces the claim to the standard Gaussian.  This is what makes a
block of `≍ y²/v₋` steps clear a gap of `y` with probability bounded below, uniformly over the
walks considered.
-/

/-- The mass of `N(0,1)` on `(a, b]`, `0 ≤ a ≤ b`, is at least `b - a` times the density at `b`. -/
lemma le_measure_Ioc_gaussianReal_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal ((b - a) * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
        * rexp (-b ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))))
      ≤ gaussianReal 0 1 (Set.Ioc a b) := by
  have hc0 : 0 ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * rexp (-b ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by
    positivity
  rw [gaussianReal_apply _ one_ne_zero]
  calc ENNReal.ofReal ((b - a) * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
          * rexp (-b ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))))
      = ∫⁻ _ in Set.Ioc a b, ENNReal.ofReal ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
          * rexp (-b ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc,
          ← ENNReal.ofReal_mul hc0, mul_comm]
    _ ≤ ∫⁻ x in Set.Ioc a b, gaussianPDF 0 1 x :=
        setLIntegral_mono' measurableSet_Ioc fun x hx =>
          ENNReal.ofReal_le_ofReal
            (le_gaussianPDFReal_of_abs_le (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩))

/-- A measure of `(a, a + nh]` is the sum over the `n` pieces of length `h`. -/
lemma measure_Ioc_eq_sum_Ioc (ν : Measure ℝ) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ν (Set.Ioc a (a + n * h))
      = ∑ k ∈ Finset.range n, ν (Set.Ioc (a + k * h) (a + (k + 1) * h)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : a ≤ a + n * h := by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hh
      linarith
    have h2 : a + n * h ≤ a + (n + 1) * h := by nlinarith
    rw [← measure_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Set.Ioc_union_Ioc_eq_Ioc h1 h2]
    push_cast
    rfl

/-- **The standard Gaussian exceeds `1` with probability at least `1/8`** (the true value is
`0.1587`): the density on twelve quarter-intervals of `(1, 4]`, each at its right end,
`e^{-(5+k)²/32} ≥ (31/32)^{(5+k)²}`. -/
lemma le_measure_Ioi_one_gaussianReal_eighth :
    ENNReal.ofReal (1 / 8) ≤ gaussianReal 0 1 (Set.Ioi 1) := by
  have hsplit := measure_Ioc_eq_sum_Ioc (gaussianReal 0 1) 1 (h := 1 / 4) (by norm_num) 12
  have hpiece : ∀ k ∈ Finset.range 12,
      ENNReal.ofReal ((1 / 4) * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
        * rexp (-(1 + ((k : ℝ) + 1) * (1 / 4)) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))))
      ≤ gaussianReal 0 1 (Set.Ioc (1 + (k : ℝ) * (1 / 4)) (1 + ((k : ℝ) + 1) * (1 / 4))) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h := le_measure_Ioc_gaussianReal_one (a := 1 + (k : ℝ) * (1 / 4))
      (b := 1 + ((k : ℝ) + 1) * (1 / 4)) (by positivity) (by linarith)
    have hlen : (1 + ((k : ℝ) + 1) * (1 / 4)) - (1 + (k : ℝ) * (1 / 4)) = 1 / 4 := by ring
    rwa [hlen] at h
  -- the densities, numerically
  have hsq : √(2 * π * ((1 : ℝ≥0) : ℝ)) ≤ 2.5067 := by
    rw [NNReal.coe_one, mul_one, show (2.5067 : ℝ) = √(2.5067 ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d4])
  have hsq0 : 0 < √(2 * π * ((1 : ℝ≥0) : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hexp : ∀ k : ℕ, ((31 : ℝ) / 32) ^ ((5 + k) ^ 2)
      ≤ rexp (-(1 + ((k : ℝ) + 1) * (1 / 4)) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by
    intro k
    have h1 : (31 : ℝ) / 32 ≤ rexp (-1 / 32) := by
      have := Real.add_one_le_exp (-1 / 32 : ℝ)
      linarith
    have hpow : ((31 : ℝ) / 32) ^ ((5 + k) ^ 2) ≤ rexp (-1 / 32) ^ ((5 + k) ^ 2) :=
      pow_le_pow_left₀ (by norm_num) h1 _
    refine le_trans hpow (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hterm : ∀ k ∈ Finset.range 12, (1 / 4) * ((1 / 2.5067) * ((31 : ℝ) / 32) ^ ((5 + k) ^ 2))
      ≤ (1 / 4) * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
        * rexp (-(1 + ((k : ℝ) + 1) * (1 / 4)) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))) := by
    intro k _
    have hinv : (1 / 2.5067 : ℝ) ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hsq0 hsq
    gcongr
    exact hexp k
  have hnum : (1 / 8 : ℝ)
      ≤ ∑ k ∈ Finset.range 12, (1 / 4) * ((1 / 2.5067) * ((31 : ℝ) / 32) ^ ((5 + k) ^ 2)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  calc ENNReal.ofReal (1 / 8)
      ≤ ENNReal.ofReal (∑ k ∈ Finset.range 12, (1 / 4) * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
          * rexp (-(1 + ((k : ℝ) + 1) * (1 / 4)) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))) :=
        ENNReal.ofReal_le_ofReal (le_trans hnum (Finset.sum_le_sum hterm))
    _ = ∑ k ∈ Finset.range 12, ENNReal.ofReal ((1 / 4) * ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
          * rexp (-(1 + ((k : ℝ) + 1) * (1 / 4)) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))) :=
        ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity
    _ ≤ ∑ k ∈ Finset.range 12,
          gaussianReal 0 1 (Set.Ioc (1 + (k : ℝ) * (1 / 4)) (1 + ((k : ℝ) + 1) * (1 / 4))) :=
        Finset.sum_le_sum hpiece
    _ = gaussianReal 0 1 (Set.Ioc 1 (1 + (12 : ℕ) * (1 / 4))) := hsplit.symm
    _ ≤ gaussianReal 0 1 (Set.Ioi 1) := measure_mono Set.Ioc_subset_Ioi_self

/-- **The crossing probability, at any lower bound `ρ` for the unit tail.**  Monotonicity in the
variance means only the lower bound `y² ≤ V` is needed. -/
lemma le_measure_Ioi_gaussianReal_of {ρ : ℝ}
    (hρ : ENNReal.ofReal ρ ≤ gaussianReal 0 1 (Set.Ioi 1)) {V : ℝ≥0} {y : ℝ}
    (hy : 0 < y) (hV1 : y ^ 2 ≤ (V : ℝ)) :
    ENNReal.ofReal ρ ≤ gaussianReal 0 V (Set.Ioi y) := by
  have hVpos : (0 : ℝ) < (V : ℝ) := lt_of_lt_of_le (by positivity) hV1
  have hsqV : (0 : ℝ) < √(V : ℝ) := Real.sqrt_pos.2 hVpos
  have hyV : y ≤ √(V : ℝ) := by
    rw [show y = √(y ^ 2) from (Real.sqrt_sq hy.le).symm]
    exact Real.sqrt_le_sqrt hV1
  have hpre : (fun z : ℝ => √(V : ℝ) * z) ⁻¹' Set.Ioi y = Set.Ioi (y / √(V : ℝ)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ioi, div_lt_iff₀ hsqV]
    constructor
    · intro hz; linarith
    · intro hz; linarith
  calc ENNReal.ofReal ρ
      ≤ gaussianReal 0 1 (Set.Ioi 1) := hρ
    _ ≤ gaussianReal 0 1 (Set.Ioi (y / √(V : ℝ))) :=
        measure_mono (Set.Ioi_subset_Ioi (by rw [div_le_one hsqV]; exact hyV))
    _ = gaussianReal 0 V (Set.Ioi y) := by
        rw [← gaussianReal_map_sqrt_mul V, Measure.map_apply (by fun_prop) measurableSet_Ioi,
          hpre]

/-! ### The tail weight of the law of `S_k`

Probability Result 2 integrates `min {1, (a + |u|)/√m}` against the law of `S_k` over the region
`|u| ≥ T`, and needs the answer to decay in `T` fast enough to be summable over `k`.  A single
absolute moment does it — no Gaussian tail asymptotics, no Chernoff bound.
-/

/-- `x ≤ e^{tx}/(e t)` for `t > 0`: `e·y ≤ e^y` at `y = tx`. -/
lemma le_exp_mul_div {t : ℝ} (ht : 0 < t) (x : ℝ) : x ≤ rexp (t * x) / (rexp 1 * t) := by
  rw [le_div_iff₀ (by positivity)]
  have h := Real.add_one_le_exp (t * x - 1)
  rw [Real.exp_sub] at h
  have he : 0 < rexp 1 := Real.exp_pos 1
  have h2 : rexp 1 * (t * x) ≤ rexp (t * x) := by
    have h3 : t * x ≤ rexp (t * x) / rexp 1 := by linarith
    rwa [le_div_iff₀ he, mul_comm] at h3
  linarith

/-- `(x - a)⁺ ≤ e^{t(x-a)}/(e t)` for `t > 0`. -/
lemma posPart_sub_le_exp {t : ℝ} (ht : 0 < t) (x a : ℝ) :
    max (x - a) 0 ≤ rexp (t * (x - a)) / (rexp 1 * t) :=
  max_le (le_exp_mul_div ht _) (by positivity)

/-- **The tail integral by the moment generating function**:
`E[(N(0,V) - a)⁺] ≤ e^{Vt²/2 - ta}/(e t)` for every `t > 0`. -/
lemma integral_posPart_sub_le_mgf (V : ℝ≥0) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x, max (x - a) 0 ∂(gaussianReal 0 V)
      ≤ rexp ((V : ℝ) * t ^ 2 / 2 - t * a) / (rexp 1 * t) := by
  have hmgf : ∫ x, rexp (t * x) ∂(gaussianReal 0 V) = rexp ((V : ℝ) * t ^ 2 / 2) := by
    have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := V)) t
    rw [mgf] at h
    simpa using h
  have hpt : ∀ x : ℝ, rexp (t * (x - a)) / (rexp 1 * t)
      = rexp (-(t * a)) / (rexp 1 * t) * rexp (t * x) := by
    intro x
    rw [mul_sub, sub_eq_add_neg, Real.exp_add]
    ring
  have hint : Integrable (fun x : ℝ => rexp (t * (x - a)) / (rexp 1 * t)) (gaussianReal 0 V) := by
    simp_rw [hpt]
    exact (integrable_exp_mul_gaussianReal t).const_mul _
  calc ∫ x, max (x - a) 0 ∂(gaussianReal 0 V)
      ≤ ∫ x, rexp (t * (x - a)) / (rexp 1 * t) ∂(gaussianReal 0 V) :=
        integral_mono (integrable_posPart_sub_gaussianReal V a) hint
          fun x => posPart_sub_le_exp ht x a
    _ = rexp (-(t * a)) / (rexp 1 * t) * ∫ x, rexp (t * x) ∂(gaussianReal 0 V) := by
        simp_rw [hpt]
        exact integral_const_mul _ _
    _ = rexp ((V : ℝ) * t ^ 2 / 2 - t * a) / (rexp 1 * t) := by
        rw [hmgf, sub_eq_add_neg, Real.exp_add]
        ring

/-- **The tail weight, by an eighth moment.**  On `|u| ≥ T ≥ 1` we have `1 + |u| ≤ 2|u| ≤ 2|u|⁸/T⁷`,
so the tail integral of `1 + |u|` is `≤ 2 C₈ V⁴ / T⁷`.

Eight rather than six is deliberate.  With `T = Bk/2` and `V ≤ k v₊` the bound is `≪ 1/(B⁷k³)`; the
spare `1/k` over what summability needs absorbs the `10 log(k+1)` that the shifted barrier of
Probability Result 2 carries. -/
lemma lintegral_tail_one_add_abs_le (V : ℝ≥0) {T : ℝ} (hT : 1 ≤ T) :
    ∫⁻ u in {u : ℝ | T ≤ |u|}, ENNReal.ofReal (1 + |u|) ∂(gaussianReal 0 V)
      ≤ ENNReal.ofReal (2 * absMomentConst 8 * (V : ℝ) ^ 4 / T ^ 7) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hpt : ∀ u ∈ {u : ℝ | T ≤ |u|},
      ENNReal.ofReal (1 + |u|) ≤ ENNReal.ofReal (2 * |u| ^ 8 / T ^ 7) := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ |u| := le_trans hT hu
    have h7 : T ^ 7 ≤ |u| ^ 7 := pow_le_pow_left₀ hT0.le hu 7
    rw [le_div_iff₀ (by positivity)]
    calc (1 + |u|) * T ^ 7 ≤ (2 * |u|) * |u| ^ 7 :=
          mul_le_mul (by linarith) h7 (by positivity) (by positivity)
      _ = 2 * |u| ^ 8 := by ring
  calc ∫⁻ u in {u : ℝ | T ≤ |u|}, ENNReal.ofReal (1 + |u|) ∂(gaussianReal 0 V)
      ≤ ∫⁻ u in {u : ℝ | T ≤ |u|}, ENNReal.ofReal (2 * |u| ^ 8 / T ^ 7)
          ∂(gaussianReal 0 V) := setLIntegral_mono (by fun_prop) hpt
    _ ≤ ∫⁻ u, ENNReal.ofReal (2 * |u| ^ 8 / T ^ 7) ∂(gaussianReal 0 V) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 * absMomentConst 8 * (V : ℝ) ^ 4 / T ^ 7) := by
        have hint : Integrable (fun u : ℝ => 2 * |u| ^ 8 / T ^ 7) (gaussianReal 0 V) :=
          ((integrable_abs_pow_gaussianReal V 8).const_mul 2).div_const _
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun u => by positivity)]
        congr 1
        rw [integral_div, integral_const_mul, integral_abs_pow_gaussianReal]
        have hV8 : √(V : ℝ) ^ 8 = (V : ℝ) ^ 4 := by
          rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt V.coe_nonneg]
        rw [hV8]
        ring

end RMF
