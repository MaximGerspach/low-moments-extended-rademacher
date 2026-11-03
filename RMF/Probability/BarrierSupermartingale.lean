/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.CurvedBarrierSharp
import RMF.Probability.GaussianEstimates

/-!
# Probability Result 1 at the Gaussian constant

For a Gaussian walk with independent `N(0, v_i)` steps, `v₋ ≤ v_i ≤ v₊`, a barrier `y ≥ 0` and
`c ≥ √(πv₊/2)`, the process `1_{S_j ≤ y ∀ j ≤ k}·κ_{W_N - W_k}(y - S_k + c)` is a
supermartingale, where `κ_V(z) = 2P(N(0, V) ≤ z) - 1` (`RMF.gaussOdd`).  So the walk survives `N`
steps with probability at most `κ_{W_N}(y + c) ≤ (y + c)√(2/(πW_N))`, for every `N`.

* `RMF.gaussOdd`: at most `1`, nonnegative on `[0, ∞)`, odd away from `0`, `κ_V(z)/z`
  nonincreasing, `κ_V(z) ≤ z√(2/(πV))`, and `E κ_{V'}(a - G) = κ_{v+V'}(a)` for `G ~ N(0, v)`;
* `RMF.setIntegral_Ioi_gaussOdd_nonneg`: `E[1_{G > D}κ_{V'}(D + c - G)] ≥ 0`, pairing `g` with
  its reflection about `D + c`, the rest being the overshoot `E(G - D)⁺ ≤ √(πv/2)P(G > D)`;
* `RMF.integral_indicator_Iic_gaussOdd_le`: the one-step inequality;
* `RMF.IsGaussianWalk.integral_survival_gaussOdd_step` and
  `RMF.IsGaussianWalk.measureReal_survival_le_integral_gaussOdd`: the supermartingale;
* `RMF.IsGaussianWalk.measureReal_survival_le_split_sharp`: survival past a split `m < n`;
* `RMF.IsGaussianWalk.measureReal_forall_le_log_le_sharp` and its affine form: Probability
  Result 1 for the barrier `a + β log j` at `K² ≥ 2M/((M-1)πv₋)`, split at `⌊n/M⌋`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-- **The signed Gaussian tube** `κ_V(z) = 2P(N(0, V) ≤ z) - 1`: `P(|N(0, V)| ≤ z)` for `z ≥ 0`,
odd away from `0`. -/
noncomputable def gaussOdd (V : ℝ≥0) (z : ℝ) : ℝ := 2 * (gaussianReal 0 V).real (Set.Iic z) - 1

lemma gaussOdd_le_one (V : ℝ≥0) (z : ℝ) : gaussOdd V z ≤ 1 := by
  have := measureReal_le_one (μ := gaussianReal 0 V) (s := Set.Iic z)
  unfold gaussOdd
  linarith

lemma neg_one_le_gaussOdd (V : ℝ≥0) (z : ℝ) : -1 ≤ gaussOdd V z := by
  have : 0 ≤ (gaussianReal 0 V).real (Set.Iic z) := measureReal_nonneg
  unfold gaussOdd
  linarith

/-- `P(N(0, V) ≤ 0) ≥ 1/2`, in real form. -/
lemma half_le_gaussianReal_real_Iic_zero (V : ℝ≥0) :
    1 / 2 ≤ (gaussianReal 0 V).real (Set.Iic (0 : ℝ)) := by
  have h := half_le_gaussianReal_Iic V
  have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h'
  exact h'

lemma gaussOdd_nonneg (V : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ gaussOdd V z := by
  have h1 := half_le_gaussianReal_real_Iic_zero V
  have h2 : (gaussianReal 0 V).real (Set.Iic (0 : ℝ)) ≤ (gaussianReal 0 V).real (Set.Iic z) :=
    measureReal_mono (Set.Iic_subset_Iic.2 hz)
  unfold gaussOdd
  linarith

/-- At variance `0` the tube is `1` on `[0, ∞)`. -/
lemma gaussOdd_zero_var {z : ℝ} (hz : 0 ≤ z) : gaussOdd 0 z = 1 := by
  unfold gaussOdd
  rw [gaussianReal_zero_var, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_of_mem (show (0 : ℝ) ∈ Set.Iic z from hz)]
  norm_num

/-- **Oddness away from `0`**: `κ_V(-z) = -κ_V(z)` for `z ≠ 0`, by the symmetry of `N(0, V)`; the
atom at `0` when `V = 0` is the only exception. -/
lemma gaussOdd_neg (V : ℝ≥0) {z : ℝ} (hz : z ≠ 0) : gaussOdd V (-z) = -gaussOdd V z := by
  have hsymm : (gaussianReal 0 V).real (Set.Iic (-z)) = (gaussianReal 0 V).real (Set.Ici z) := by
    have hmap : (gaussianReal 0 V).map (fun x : ℝ => -x) = gaussianReal 0 V := by
      rw [gaussianReal_map_neg, neg_zero]
    rw [measureReal_def, measureReal_def]
    congr 1
    calc gaussianReal 0 V (Set.Iic (-z))
        = ((gaussianReal 0 V).map (fun x : ℝ => -x)) (Set.Ici z) := by
          rw [Measure.map_apply measurable_neg measurableSet_Ici]
          congr 1
          ext x
          simp
      _ = gaussianReal 0 V (Set.Ici z) := by rw [hmap]
  have hatom : (gaussianReal 0 V).real {z} = 0 := by
    by_cases hV : V = 0
    · subst hV
      have hz0 : (0 : ℝ) ∉ ({z} : Set ℝ) := fun h => hz (Set.mem_singleton_iff.1 h).symm
      rw [gaussianReal_zero_var, measureReal_def,
        Measure.dirac_apply' _ (measurableSet_singleton z), Set.indicator_of_notMem hz0]
      simp
    · haveI := nullSingletonClass_gaussianReal (μ := 0) hV
      rw [measureReal_def, measure_singleton, ENNReal.toReal_zero]
  have hsplit : (gaussianReal 0 V).real (Set.Ici z) + (gaussianReal 0 V).real (Set.Iic z)
      = 1 + (gaussianReal 0 V).real {z} := by
    have hU : Set.Ici z ∪ Set.Iic z = Set.univ := by
      ext x
      simp
    have hI : Set.Ici z ∩ Set.Iic z = {z} := by
      ext x
      simp [le_antisymm_iff, and_comm]
    have := measureReal_union_add_inter (μ := gaussianReal 0 V) (s := Set.Ici z) measurableSet_Iic
    rw [hU, hI, probReal_univ] at this
    linarith
  unfold gaussOdd
  rw [hsymm]
  linarith

/-- `P(N(0, V) ≤ 0) = 1/2` for `V ≠ 0`. -/
lemma gaussianReal_real_Iic_zero {V : ℝ≥0} (hV : V ≠ 0) :
    (gaussianReal 0 V).real (Set.Iic (0 : ℝ)) = 1 / 2 := by
  haveI := nullSingletonClass_gaussianReal (μ := 0) hV
  have hsymm : (gaussianReal 0 V).real (Set.Iic (0 : ℝ))
      = (gaussianReal 0 V).real (Set.Ici 0) := by
    have hmap : (gaussianReal 0 V).map (fun x : ℝ => -x) = gaussianReal 0 V := by
      rw [gaussianReal_map_neg, neg_zero]
    rw [measureReal_def, measureReal_def]
    congr 1
    calc gaussianReal 0 V (Set.Iic (0 : ℝ))
        = ((gaussianReal 0 V).map (fun x : ℝ => -x)) (Set.Ici 0) := by
          rw [Measure.map_apply measurable_neg measurableSet_Ici]
          congr 1
          ext x
          simp
      _ = gaussianReal 0 V (Set.Ici 0) := by rw [hmap]
  have hU : Set.Ici (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x
    simp
  have hI : Set.Ici (0 : ℝ) ∩ Set.Iic 0 = {0} := by
    ext x
    simp [le_antisymm_iff, and_comm]
  have hsum := measureReal_union_add_inter (μ := gaussianReal 0 V) (s := Set.Ici (0 : ℝ))
    (measurableSet_Iic (a := (0 : ℝ)))
  rw [hU, hI, probReal_univ, measureReal_def (s := {0}), measure_singleton,
    ENNReal.toReal_zero] at hsum
  linarith

/-- The mass of a set is the integral of the density. -/
lemma gaussianReal_real_eq_setIntegral {V : ℝ≥0} (hV : V ≠ 0) (s : Set ℝ) :
    (gaussianReal 0 V).real s = ∫ x in s, gaussianPDFReal 0 V x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hV s,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae_restrict
      (ae_of_all _ fun x => gaussianPDFReal_nonneg 0 V x))]

/-- For `V ≠ 0` and `z ≥ 0`: `κ_V(z) = 2P(0 < N(0, V) ≤ z)`. -/
lemma gaussOdd_eq_two_mul_Ioc {V : ℝ≥0} (hV : V ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    gaussOdd V z = 2 * (gaussianReal 0 V).real (Set.Ioc 0 z) := by
  have hunion : Set.Iic z = Set.Iic 0 ∪ Set.Ioc 0 z := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      by_cases h0 : x ≤ 0
      · exact Or.inl h0
      · exact Or.inr ⟨lt_of_not_ge h0, hx⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioc 0 z) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Iic, Set.mem_Ioc] at hx hx'
    linarith [hx'.1]
  unfold gaussOdd
  rw [hunion, measureReal_union hdisj measurableSet_Ioc, gaussianReal_real_Iic_zero hV]
  ring

/-- The density is antitone on `[0, ∞)`. -/
lemma gaussianPDFReal_antitoneOn (V : ℝ≥0) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 V y ≤ gaussianPDFReal 0 V x := by
  rw [gaussianPDFReal, gaussianPDFReal]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hsq : (x - 0) ^ 2 ≤ (y - 0) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- `(t - s)φ(t) ≤ ∫_{(s, t]} φ ≤ (t - s)φ(s)` for `0 ≤ s ≤ t`. -/
lemma setIntegral_Ioc_gaussianPDFReal_bounds (V : ℝ≥0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (t - s) * gaussianPDFReal 0 V t ≤ ∫ x in Set.Ioc s t, gaussianPDFReal 0 V x
      ∧ ∫ x in Set.Ioc s t, gaussianPDFReal 0 V x ≤ (t - s) * gaussianPDFReal 0 V s := by
  have hint : IntegrableOn (gaussianPDFReal 0 V) (Set.Ioc s t) :=
    (integrable_gaussianPDFReal 0 V).integrableOn
  have hvol : volume.real (Set.Ioc s t) = t - s := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have hfin : volume (Set.Ioc s t) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  constructor
  · have h := setIntegral_mono_on (μ := volume) (s := Set.Ioc s t)
      (f := fun _ => gaussianPDFReal 0 V t) (g := gaussianPDFReal 0 V)
      (integrableOn_const hfin) hint
      measurableSet_Ioc (fun x hx => gaussianPDFReal_antitoneOn V (by linarith [hx.1]) hx.2)
    rwa [setIntegral_const, hvol, smul_eq_mul] at h
  · have h := setIntegral_mono_on (μ := volume) (s := Set.Ioc s t)
      (f := gaussianPDFReal 0 V) (g := fun _ => gaussianPDFReal 0 V s) hint
      (integrableOn_const hfin)
      measurableSet_Ioc (fun x hx => gaussianPDFReal_antitoneOn V hs hx.1.le)
    rwa [setIntegral_const, hvol, smul_eq_mul] at h

/-- **`κ_V(z)/z` is nonincreasing**, below `c`: `z·κ_V(c) ≤ c·κ_V(z)` for `0 ≤ z ≤ c`. -/
lemma mul_gaussOdd_le_of_le (V : ℝ≥0) {z c : ℝ} (hz : 0 ≤ z) (hzc : z ≤ c) :
    z * gaussOdd V c ≤ c * gaussOdd V z := by
  by_cases hV : V = 0
  · subst hV
    rw [gaussOdd_zero_var hz, gaussOdd_zero_var (le_trans hz hzc)]
    linarith
  rw [gaussOdd_eq_two_mul_Ioc hV hz, gaussOdd_eq_two_mul_Ioc hV (le_trans hz hzc),
    gaussianReal_real_eq_setIntegral hV, gaussianReal_real_eq_setIntegral hV]
  have hsplit : ∫ x in Set.Ioc 0 c, gaussianPDFReal 0 V x
      = (∫ x in Set.Ioc 0 z, gaussianPDFReal 0 V x)
        + ∫ x in Set.Ioc z c, gaussianPDFReal 0 V x := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (integrable_gaussianPDFReal 0 V).integrableOn (integrable_gaussianPDFReal 0 V).integrableOn,
      Set.Ioc_union_Ioc_eq_Ioc hz hzc]
  obtain ⟨h1, -⟩ := setIntegral_Ioc_gaussianPDFReal_bounds V le_rfl hz
  obtain ⟨-, h2⟩ := setIntegral_Ioc_gaussianPDFReal_bounds V hz hzc
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ c - z),
    mul_le_mul_of_nonneg_left h2 hz]

/-- **`κ_V(z)/z` is nonincreasing**, above `c`: `c·κ_V(z) ≤ z·κ_V(c)` for `0 ≤ c ≤ z`. -/
lemma mul_gaussOdd_le_of_ge (V : ℝ≥0) {z c : ℝ} (hc : 0 ≤ c) (hcz : c ≤ z) :
    c * gaussOdd V z ≤ z * gaussOdd V c := by
  by_cases hV : V = 0
  · subst hV
    rw [gaussOdd_zero_var hc, gaussOdd_zero_var (le_trans hc hcz)]
    linarith
  rw [gaussOdd_eq_two_mul_Ioc hV hc, gaussOdd_eq_two_mul_Ioc hV (le_trans hc hcz),
    gaussianReal_real_eq_setIntegral hV, gaussianReal_real_eq_setIntegral hV]
  have hsplit : ∫ x in Set.Ioc 0 z, gaussianPDFReal 0 V x
      = (∫ x in Set.Ioc 0 c, gaussianPDFReal 0 V x)
        + ∫ x in Set.Ioc c z, gaussianPDFReal 0 V x := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (integrable_gaussianPDFReal 0 V).integrableOn (integrable_gaussianPDFReal 0 V).integrableOn,
      Set.Ioc_union_Ioc_eq_Ioc hc hcz]
  obtain ⟨h1, -⟩ := setIntegral_Ioc_gaussianPDFReal_bounds V le_rfl hc
  obtain ⟨-, h2⟩ := setIntegral_Ioc_gaussianPDFReal_bounds V hc hcz
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ z - c),
    mul_le_mul_of_nonneg_left h2 hc]

/-- **The tube is at most linear**: `κ_V(z) ≤ z√(2/(πV))` for `z ≥ 0` and `V ≠ 0`. -/
lemma gaussOdd_le_mul_sqrt {V : ℝ≥0} (hV : V ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    gaussOdd V z ≤ z * √(2 / (π * V)) := by
  rw [gaussOdd_eq_two_mul_Ioc hV hz, gaussianReal_real_eq_setIntegral hV]
  obtain ⟨-, h⟩ := setIntegral_Ioc_gaussianPDFReal_bounds V le_rfl hz
  have hmax := gaussianPDFReal_le 0 V 0
  have hV0 : (0 : ℝ) < V := lt_of_le_of_ne V.2 (Ne.symm (by exact_mod_cast hV))
  have hkey : 2 * (√(2 * π * V))⁻¹ = √(2 / (π * V)) := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show (2 : ℝ) / (π * V) = 4 / (2 * π * V) by field_simp; ring,
      Real.sqrt_div' _ (by positivity), h4, div_eq_mul_inv]
  calc 2 * ∫ x in Set.Ioc 0 z, gaussianPDFReal 0 V x
      ≤ 2 * ((z - 0) * gaussianPDFReal 0 V 0) := by linarith
    _ ≤ 2 * (z * (√(2 * π * V))⁻¹) := by
        rw [sub_zero]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax hz) (by norm_num)
    _ = z * √(2 / (π * V)) := by rw [← hkey]; ring

/-- `P(N(0, V) ≤ z)` is monotone in `z`, hence measurable. -/
lemma measurable_gaussianReal_real_Iic (V : ℝ≥0) :
    Measurable fun z : ℝ => (gaussianReal 0 V).real (Set.Iic z) :=
  Monotone.measurable fun _ _ h => measureReal_mono (Set.Iic_subset_Iic.2 h)

lemma measurable_gaussOdd (V : ℝ≥0) : Measurable (gaussOdd V) := by
  unfold gaussOdd
  exact (measurable_const.mul (measurable_gaussianReal_real_Iic V)).sub measurable_const

/-- **The convolution identity**: `E_{g ~ N(0, v)} P(N(0, V') ≤ a - g) = P(N(0, v + V') ≤ a)`. -/
lemma integral_gaussianReal_real_Iic_sub (v V' : ℝ≥0) (a : ℝ) :
    ∫ g, (gaussianReal 0 V').real (Set.Iic (a - g)) ∂(gaussianReal 0 v)
      = (gaussianReal 0 (v + V')).real (Set.Iic a) := by
  have hconv : gaussianReal 0 v ∗ gaussianReal 0 V' = gaussianReal 0 (v + V') := by
    rw [gaussianReal_conv_gaussianReal, add_zero]
  have hlin : (gaussianReal 0 v ∗ gaussianReal 0 V') (Set.Iic a)
      = ∫⁻ g, gaussianReal 0 V' (Set.Iic (a - g)) ∂(gaussianReal 0 v) := by
    have hms : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic a) :=
      measurable_add measurableSet_Iic
    rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Iic,
      Measure.prod_apply hms]
    refine lintegral_congr fun g => ?_
    congr 1
    ext n
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro hn <;> linarith
  have hmeas : Measurable fun g : ℝ => gaussianReal 0 V' (Set.Iic (a - g)) :=
    Antitone.measurable fun _ _ h => measure_mono (Set.Iic_subset_Iic.2 (by linarith))
  rw [measureReal_def, ← hconv, hlin,
    ← integral_toReal hmeas.aemeasurable (ae_of_all _ fun g => measure_lt_top _ _)]
  rfl

lemma integrable_gaussOdd_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (V : ℝ≥0) {f : α → ℝ} (hf : Measurable f) :
    Integrable (fun g => gaussOdd V (f g)) μ :=
  Integrable.of_mem_Icc (-1) 1 ((measurable_gaussOdd V).comp hf).aemeasurable
    (ae_of_all _ fun _ => ⟨neg_one_le_gaussOdd V _, gaussOdd_le_one V _⟩)

/-- **The tube under a Gaussian shift**: `E_{g ~ N(0, v)} κ_{V'}(a - g) = κ_{v+V'}(a)`. -/
lemma integral_gaussOdd_sub (v V' : ℝ≥0) (a : ℝ) :
    ∫ g, gaussOdd V' (a - g) ∂(gaussianReal 0 v) = gaussOdd (v + V') a := by
  have hint : Integrable (fun g => (gaussianReal 0 V').real (Set.Iic (a - g)))
      (gaussianReal 0 v) :=
    Integrable.of_mem_Icc 0 1
      ((measurable_gaussianReal_real_Iic V').comp (measurable_const.sub measurable_id)).aemeasurable
      (ae_of_all _ fun g => ⟨measureReal_nonneg, measureReal_le_one⟩)
  unfold gaussOdd
  rw [integral_sub (hint.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_gaussianReal_real_Iic_sub, integral_const, probReal_univ, one_smul]

/-- **The overshoot against the barrier**: for `D ≥ 0` and `c ≥ √(πv/2)`,
`0 ≤ E[1_{G > D}(D + c - G)]`, `G ~ N(0, v)`: `RMF.lintegral_posPart_sub_le_gaussianReal`. -/
lemma setIntegral_Ioi_add_sub_nonneg (v : ℝ≥0) {D c : ℝ} (hD : 0 ≤ D) (hc : √(π * v / 2) ≤ c) :
    0 ≤ ∫ g in Set.Ioi D, (D + c - g) ∂(gaussianReal 0 v) := by
  have hid : Integrable (fun g : ℝ => g) (gaussianReal 0 v) :=
    (memLp_one_iff_integrable.1 (memLp_id_gaussianReal (μ := 0) (v := v) 1))
  have hpos : Integrable (fun g : ℝ => max (g - D) 0) (gaussianReal 0 v) :=
    (hid.sub (integrable_const D)).pos_part
  -- the positive part equals `g - D` on `(D, ∞)` and vanishes elsewhere
  have hsplit : ∫ g in Set.Ioi D, (D + c - g) ∂(gaussianReal 0 v)
      = c * (gaussianReal 0 v).real (Set.Ioi D) - ∫ g, max (g - D) 0 ∂(gaussianReal 0 v) := by
    have h1 : ∫ g in Set.Ioi D, (D + c - g) ∂(gaussianReal 0 v)
        = ∫ g in Set.Ioi D, (c - max (g - D) 0) ∂(gaussianReal 0 v) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun g hg => ?_
      simp only [Set.mem_Ioi] at hg
      rw [max_eq_left (by linarith)]
      ring
    have h2 : ∫ g in Set.Ioi D, max (g - D) 0 ∂(gaussianReal 0 v)
        = ∫ g, max (g - D) 0 ∂(gaussianReal 0 v) := by
      rw [← integral_indicator measurableSet_Ioi]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      by_cases hg : g ∈ Set.Ioi D
      · rw [Set.indicator_of_mem hg]
      · rw [Set.indicator_of_notMem hg]
        simp only [Set.mem_Ioi, not_lt] at hg
        exact (max_eq_right (by linarith)).symm
    rw [h1, integral_sub (integrable_const c).integrableOn hpos.integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, h2]
  have hlint := lintegral_posPart_sub_le_gaussianReal v hD
  have hreal : ∫ g, max (g - D) 0 ∂(gaussianReal 0 v)
      ≤ √(π * v / 2) * (gaussianReal 0 v).real (Set.Ioi D) := by
    have heq := integral_eq_lintegral_of_nonneg_ae (μ := gaussianReal 0 v)
      (f := fun g : ℝ => max (g - D) 0) (ae_of_all _ fun g => le_max_right _ _)
      hpos.aestronglyMeasurable
    rw [heq]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      hlint
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
  have hP : 0 ≤ (gaussianReal 0 v).real (Set.Ioi D) := measureReal_nonneg
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hc hP]

/-- **The core of the sharp barrier bound**: for `v ≠ 0`, `D ≥ 0`, `c > 0` with `c ≥ √(πv/2)`, and
any `V'`, `E[1_{G > D}κ_{V'}(D + c - G)] ≥ 0`, `G ~ N(0, v)`.  With `a = D + c` and
`λ = κ(c)/c`, the function `h(g) = κ(a - g) - λ(a - g)` is odd about `a`, nonnegative on
`(D, a]` and beyond `a + c`; the density is larger at `g` than at `2a - g` for `D ≤ g ≤ a`, so
the pairing `g ↔ 2a - g` makes `∫_{(D, ∞)} h ≥ 0`, and `λ∫_{(D, ∞)}(a - g) ≥ 0` is the
overshoot. -/
theorem setIntegral_Ioi_gaussOdd_nonneg {v : ℝ≥0} (hv : v ≠ 0) (V' : ℝ≥0) {D c : ℝ}
    (hD : 0 ≤ D) (hc0 : 0 < c) (hc : √(π * v / 2) ≤ c) :
    0 ≤ ∫ g in Set.Ioi D, gaussOdd V' (D + c - g) ∂(gaussianReal 0 v) := by
  set a := D + c with ha
  set lam := gaussOdd V' c / c with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (gaussOdd_nonneg V' hc0.le) hc0.le
  set h : ℝ → ℝ := fun g => gaussOdd V' (a - g) - lam * (a - g) with hh
  have hid : Integrable (fun g : ℝ => g) (gaussianReal 0 v) :=
    (memLp_one_iff_integrable.1 (memLp_id_gaussianReal (μ := 0) (v := v) 1))
  have hlin : Integrable (fun g : ℝ => a - g) (gaussianReal 0 v) := (integrable_const a).sub hid
  have hκ : Integrable (fun g => gaussOdd V' (a - g)) (gaussianReal 0 v) :=
    integrable_gaussOdd_comp V' (measurable_const.sub measurable_id)
  have hhint : Integrable h (gaussianReal 0 v) := hκ.sub (hlin.const_mul lam)
  -- split off the linear part
  have hsplit : ∫ g in Set.Ioi D, gaussOdd V' (a - g) ∂(gaussianReal 0 v)
      = ∫ g in Set.Ioi D, h g ∂(gaussianReal 0 v)
        + lam * ∫ g in Set.Ioi D, (a - g) ∂(gaussianReal 0 v) := by
    rw [← integral_const_mul, ← integral_add hhint.integrableOn
      (hlin.const_mul lam).integrableOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun g _ => ?_
    simp only [hh]
    ring
  have hlinpos : 0 ≤ lam * ∫ g in Set.Ioi D, (a - g) ∂(gaussianReal 0 v) :=
    mul_nonneg hlam0 (setIntegral_Ioi_add_sub_nonneg v hD hc)
  -- the pointwise facts about `h`
  have hle : ∀ g, D ≤ g → g ≤ a → 0 ≤ h g := by
    intro g hg1 hg2
    have hz : 0 ≤ a - g := by linarith
    have hzc : a - g ≤ c := by linarith
    have hm := mul_gaussOdd_le_of_le V' hz hzc
    simp only [hh, hlam]
    rw [div_mul_eq_mul_div, sub_nonneg, div_le_iff₀ hc0]
    linarith
  have hge : ∀ g, a + c ≤ g → 0 ≤ h g := by
    intro g hg
    have hz : c ≤ g - a := by linarith
    have hm := mul_gaussOdd_le_of_ge V' hc0.le hz
    have hodd : gaussOdd V' (a - g) = -gaussOdd V' (g - a) := by
      rw [show a - g = -(g - a) by ring, gaussOdd_neg V' (by linarith)]
    simp only [hh, hlam]
    rw [hodd, div_mul_eq_mul_div]
    have : gaussOdd V' (g - a) ≤ gaussOdd V' c * (a - g) / c * (-1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
      nlinarith
    nlinarith
  have hrefl : ∀ g, g ≠ a → h (2 * a - g) = -h g := by
    intro g hg
    simp only [hh]
    rw [show a - (2 * a - g) = -(a - g) by ring, gaussOdd_neg V' (sub_ne_zero.2 hg.symm)]
    ring
  -- split at `a + c = D + 2c`
  have hDc : D ≤ a + c := by linarith
  have hunion : Set.Ioi D = Set.Ioc D (a + c) ∪ Set.Ioi (a + c) :=
    (Set.Ioc_union_Ioi_eq_Ioi hDc).symm
  have hdisj : Disjoint (Set.Ioc D (a + c)) (Set.Ioi (a + c)) :=
    Set.Ioc_disjoint_Ioi le_rfl
  have hsplit2 : ∫ g in Set.Ioi D, h g ∂(gaussianReal 0 v)
      = ∫ g in Set.Ioc D (a + c), h g ∂(gaussianReal 0 v)
        + ∫ g in Set.Ioi (a + c), h g ∂(gaussianReal 0 v) := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi hhint.integrableOn hhint.integrableOn]
  have htail : 0 ≤ ∫ g in Set.Ioi (a + c), h g ∂(gaussianReal 0 v) :=
    setIntegral_nonneg measurableSet_Ioi fun g hg => hge g (le_of_lt hg)
  -- the finite part, against the density
  set φ : ℝ → ℝ := gaussianPDFReal 0 v with hφ
  have hdens : ∫ g in Set.Ioc D (a + c), h g ∂(gaussianReal 0 v)
      = ∫ g in D..(a + c), φ g * h g := by
    rw [intervalIntegral.integral_of_le hDc, ← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Ioc, integral_gaussianReal_eq_integral_smul hv]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    by_cases hg : g ∈ Set.Ioc D (a + c)
    · simp only [Set.indicator_of_mem hg, smul_eq_mul, hφ]
    · simp only [Set.indicator_of_notMem hg, smul_zero]
  -- bounded measurable functions are interval integrable
  have hhmeas : Measurable h :=
    ((measurable_gaussOdd V').comp (measurable_const.sub measurable_id)).sub
      (measurable_const.mul (measurable_const.sub measurable_id))
  have hbound : ∀ g, D ≤ g → g ≤ a + c → |φ g * h g| ≤ (√(2 * π * v))⁻¹ * (1 + lam * c) := by
    intro g hg1 hg2
    have hφ0 : 0 ≤ φ g := gaussianPDFReal_nonneg 0 v g
    have hφle : φ g ≤ (√(2 * π * v))⁻¹ := gaussianPDFReal_le 0 v g
    have hag : |a - g| ≤ c := by rw [abs_le]; constructor <;> linarith
    have hκ1 : |gaussOdd V' (a - g)| ≤ 1 :=
      abs_le.2 ⟨neg_one_le_gaussOdd V' _, gaussOdd_le_one V' _⟩
    have hh : |h g| ≤ 1 + lam * c := by
      simp only [hh]
      calc |gaussOdd V' (a - g) - lam * (a - g)|
          ≤ |gaussOdd V' (a - g)| + |lam * (a - g)| := abs_sub _ _
        _ ≤ 1 + lam * c := by
          rw [abs_mul, abs_of_nonneg hlam0]
          exact add_le_add hκ1 (mul_le_mul_of_nonneg_left hag hlam0)
    rw [abs_mul, abs_of_nonneg hφ0]
    exact mul_le_mul hφle hh (abs_nonneg _) (by positivity)
  have hIIgen : ∀ (F : ℝ → ℝ) (M p q : ℝ), p ≤ q → Measurable F →
      (∀ g, p ≤ g → g ≤ q → |F g| ≤ M) → IntervalIntegrable F volume p q := by
    intro F M p q hpq hF hFM
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpq]
    refine Measure.integrableOn_of_bounded (M := M)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hF.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun g hg => ?_)
    rw [Real.norm_eq_abs]
    exact hFM g hg.1 hg.2
  have hII : ∀ p q, D ≤ p → p ≤ q → q ≤ a + c →
      IntervalIntegrable (fun g => φ g * h g) volume p q := fun p q hDp hpq hq =>
    hIIgen _ ((√(2 * π * v))⁻¹ * (1 + lam * c)) p q hpq
      ((measurable_gaussianPDFReal 0 v).mul hhmeas)
      fun g hg1 hg2 => hbound g (le_trans hDp hg1) (le_trans hg2 hq)
  have hDa : D ≤ a := by linarith
  have hac : a ≤ a + c := by linarith
  have hadj : ∫ g in D..(a + c), φ g * h g
      = (∫ g in D..a, φ g * h g) + ∫ g in a..(a + c), φ g * h g :=
    (intervalIntegral.integral_add_adjacent_intervals (hII D a le_rfl hDa hac)
      (hII a (a + c) hDa hac le_rfl)).symm
  have hsubst : ∫ g in a..(a + c), φ g * h g = ∫ g in D..a, φ (2 * a - g) * h (2 * a - g) := by
    rw [intervalIntegral.integral_comp_sub_left (fun g => φ g * h g) (2 * a)]
    congr 1 <;> ring
  have hne : ∀ᵐ g ∂(volume : Measure ℝ), g ≠ a := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hpair : ∫ g in D..a, φ (2 * a - g) * h (2 * a - g)
      = ∫ g in D..a, -(φ (2 * a - g) * h g) := by
    refine intervalIntegral.integral_congr_ae (hne.mono fun g hg _ => ?_)
    rw [hrefl g hg]
    ring
  have hfold : ∫ g in D..(a + c), φ g * h g = ∫ g in D..a, (φ g - φ (2 * a - g)) * h g := by
    have hI1 : IntervalIntegrable (fun g => φ g * h g) volume D a := hII D a le_rfl hDa hac
    have hI2 : IntervalIntegrable (fun g => -(φ (2 * a - g) * h g)) volume D a := by
      refine hIIgen _ ((√(2 * π * v))⁻¹ * (1 + lam * c)) D a hDa
        (((measurable_gaussianPDFReal 0 v).comp (measurable_const.sub measurable_id)).mul
          hhmeas).neg fun g hg1 hg2 => ?_
      have hb := hbound g hg1 (by linarith)
      have hφ0 : 0 ≤ φ (2 * a - g) := gaussianPDFReal_nonneg 0 v _
      have hφle : φ (2 * a - g) ≤ (√(2 * π * v))⁻¹ := gaussianPDFReal_le 0 v _
      have hφg0 : 0 ≤ φ g := gaussianPDFReal_nonneg 0 v g
      rw [abs_neg, abs_mul, abs_of_nonneg hφ0]
      rw [abs_mul, abs_of_nonneg hφg0] at hb
      have hag : |a - g| ≤ c := by rw [abs_le]; constructor <;> linarith
      have hκ1 : |gaussOdd V' (a - g)| ≤ 1 :=
        abs_le.2 ⟨neg_one_le_gaussOdd V' _, gaussOdd_le_one V' _⟩
      have hh : |h g| ≤ 1 + lam * c := by
        simp only [hh]
        calc |gaussOdd V' (a - g) - lam * (a - g)|
            ≤ |gaussOdd V' (a - g)| + |lam * (a - g)| := abs_sub _ _
          _ ≤ 1 + lam * c := by
            rw [abs_mul, abs_of_nonneg hlam0]
            exact add_le_add hκ1 (mul_le_mul_of_nonneg_left hag hlam0)
      exact mul_le_mul hφle hh (abs_nonneg _) (by positivity)
    rw [hadj, hsubst, hpair, ← intervalIntegral.integral_add hI1 hI2]
    congr 1
    funext g
    ring
  have hfinite : 0 ≤ ∫ g in D..(a + c), φ g * h g := by
    rw [hfold]
    refine intervalIntegral.integral_nonneg hDa fun g hg => ?_
    have hφ2 : φ (2 * a - g) ≤ φ g :=
      gaussianPDFReal_antitoneOn v (le_trans hD hg.1) (by linarith [hg.2])
    exact mul_nonneg (by linarith) (hle g hg.1 hg.2)
  rw [hsplit, hsplit2, hdens]
  linarith

/-- **The one-step inequality**: for `v ≠ 0`, `D ≥ 0` and `c > 0` with `c ≥ √(πv/2)`,
`E[1_{G ≤ D}κ_{V'}(D + c - G)] ≤ κ_{v+V'}(D + c)`, `G ~ N(0, v)`. -/
theorem integral_indicator_Iic_gaussOdd_le {v : ℝ≥0} (hv : v ≠ 0) (V' : ℝ≥0) {D c : ℝ}
    (hD : 0 ≤ D) (hc0 : 0 < c) (hc : √(π * v / 2) ≤ c) :
    ∫ g, (Set.Iic D).indicator (fun g => gaussOdd V' (D + c - g)) g ∂(gaussianReal 0 v)
      ≤ gaussOdd (v + V') (D + c) := by
  have hint : Integrable (fun g => gaussOdd V' (D + c - g)) (gaussianReal 0 v) :=
    integrable_gaussOdd_comp V' (measurable_const.sub measurable_id)
  have hsplit : ∫ g, gaussOdd V' (D + c - g) ∂(gaussianReal 0 v)
      = ∫ g in Set.Iic D, gaussOdd V' (D + c - g) ∂(gaussianReal 0 v)
        + ∫ g in Set.Ioi D, gaussOdd V' (D + c - g) ∂(gaussianReal 0 v) := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  rw [integral_indicator measurableSet_Iic]
  have h1 := integral_gaussOdd_sub v V' (D + c)
  have h2 := setIntegral_Ioi_gaussOdd_nonneg hv V' hD hc0 hc
  linarith

section Conditional

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **A fibrewise bound, conditionally**: if `R ~ N(0, V)` is independent of `X`, `Φ` and `Ψ` are
measurable and bounded by `1`, and `∫ Φ(x, ·) dN(0, V) ≤ Ψ(x)` for `x ∈ S`, then
`E[1_{X ∈ S}Φ(X, R)] ≤ E[1_{X ∈ S}Ψ(X)]`. -/
lemma integral_indicator_comp_le_of_indepFun {α : Type*} [MeasurableSpace α] {X : Ω → α}
    {R : Ω → ℝ} {S : Set α} {Φ : α × ℝ → ℝ} {Ψ : α → ℝ} {V : ℝ≥0} (hX : Measurable X)
    (hR : Measurable R) (hS : MeasurableSet S) (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hΦb : ∀ p, |Φ p| ≤ 1) (hΨb : ∀ x, |Ψ x| ≤ 1) (hind : IndepFun X R μ)
    (hlaw : μ.map R = gaussianReal 0 V)
    (hle : ∀ x ∈ S, ∫ r, Φ (x, r) ∂(gaussianReal 0 V) ≤ Ψ x) :
    ∫ ω, (X ⁻¹' S).indicator (fun ω => Φ (X ω, R ω)) ω ∂μ
      ≤ ∫ ω, (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω ∂μ := by
  have hprod := hind.map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable
  set F : α × ℝ → ℝ := (Prod.fst ⁻¹' S).indicator Φ with hF
  have hFm : Measurable F := hΦ.indicator (measurable_fst hS)
  have hL : (fun ω => (X ⁻¹' S).indicator (fun ω => Φ (X ω, R ω)) ω)
      = fun ω => F (X ω, R ω) := by
    funext ω
    by_cases hω : X ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ X ⁻¹' S from hω), hF,
        Set.indicator_of_mem (show (X ω, R ω) ∈ Prod.fst ⁻¹' S from hω)]
    · rw [Set.indicator_of_notMem (show ω ∉ X ⁻¹' S from hω), hF,
        Set.indicator_of_notMem (show (X ω, R ω) ∉ Prod.fst ⁻¹' S from hω)]
  set H : α → ℝ := S.indicator Ψ with hH
  have hHm : Measurable H := hΨ.indicator hS
  have hR2 : (fun ω => (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω) = fun ω => H (X ω) := by
    funext ω
    by_cases hω : X ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ X ⁻¹' S from hω), hH, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem (show ω ∉ X ⁻¹' S from hω), hH, Set.indicator_of_notMem hω]
  have hFb : ∀ p, F p ∈ Set.Icc (-1) 1 := by
    intro p
    rw [hF]
    by_cases hp : p ∈ Prod.fst ⁻¹' S
    · rw [Set.indicator_of_mem hp]
      exact abs_le.1 (hΦb p)
    · rw [Set.indicator_of_notMem hp]
      exact ⟨by norm_num, by norm_num⟩
  have hHb : ∀ x, H x ∈ Set.Icc (-1) 1 := by
    intro x
    rw [hH]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact abs_le.1 (hΨb x)
    · rw [Set.indicator_of_notMem hx]
      exact ⟨by norm_num, by norm_num⟩
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hFint : Integrable F ((μ.map X).prod (μ.map R)) :=
    Integrable.of_mem_Icc (-1) 1 hFm.aemeasurable (ae_of_all _ hFb)
  have hHint : Integrable H (μ.map X) :=
    Integrable.of_mem_Icc (-1) 1 hHm.aemeasurable (ae_of_all _ hHb)
  rw [hL, hR2, ← integral_map (hX.prodMk hR).aemeasurable hFm.aestronglyMeasurable, hprod,
    ← integral_map hX.aemeasurable hHm.aestronglyMeasurable, integral_prod F hFint]
  refine integral_mono hFint.integral_prod_left hHint fun x => ?_
  by_cases hx : x ∈ S
  · have hF' : ∀ r, F (x, r) = Φ (x, r) := fun r => by
      rw [hF, Set.indicator_of_mem (show (x, r) ∈ Prod.fst ⁻¹' S from hx)]
    simp only [hF', hH, Set.indicator_of_mem hx, hlaw]
    exact hle x hx
  · have hF' : ∀ r, F (x, r) = 0 := fun r => by
      rw [hF, Set.indicator_of_notMem (show (x, r) ∉ Prod.fst ⁻¹' S from hx)]
    simp only [hF', hH, Set.indicator_of_notMem hx, integral_zero, le_refl]

end Conditional

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **The supermartingale, one step.**  For a barrier with `g(k), g(k+1) ≤ Y`, `v_k ≠ 0` and
`c ≥ √(πv_k/2)`, `c > 0`:
`E[1_{A_{k+1}}κ_{V'}(Y - S_{k+1} + c)] ≤ E[1_{A_k}κ_{v_k+V'}(Y - S_k + c)]`, for every `V'`.
On `A_{k+1}` the step is at most `Y - S_k`; the step is independent of the prefix
(`RMF.integral_indicator_comp_le_of_indepFun`), and the one-step inequality is
`RMF.integral_indicator_Iic_gaussOdd_le`. -/
theorem IsGaussianWalk.integral_survival_gaussOdd_step (h : IsGaussianWalk G v μ) {g : ℕ → ℝ}
    {Y c : ℝ} (V' : ℝ≥0) {k : ℕ} (hgk : g k ≤ Y) (hgk1 : g (k + 1) ≤ Y) (hv : v k ≠ 0)
    (hc0 : 0 < c) (hc : √(π * v k / 2) ≤ c) :
    ∫ ω, (survivalSet G g (k + 1)).indicator
        (fun ω => gaussOdd V' (Y - walk G (k + 1) ω + c)) ω ∂μ
      ≤ ∫ ω, (survivalSet G g k).indicator
        (fun ω => gaussOdd (v k + V') (Y - walk G k ω + c)) ω ∂μ := by
  set X : Ω → ℕ → ℝ := fun ω => prefixSums k fun i => G i ω with hXdef
  have hX : Measurable X :=
    (measurable_prefixSums k).comp (measurable_pi_lambda _ fun i => h.measurable i)
  set S : Set (ℕ → ℝ) := {f | ∀ j ≤ k, f j ≤ g j} with hSdef
  have hS : MeasurableSet S := measurableSet_forall_le_pi g k
  have hA : survivalSet G g k = X ⁻¹' S := survivalSet_eq_preimage G g k
  have hpre : ∀ ω, X ω k = walk G k ω := fun ω => prefixSums_comp G le_rfl ω
  set Φ : (ℕ → ℝ) × ℝ → ℝ := fun p =>
    {q : (ℕ → ℝ) × ℝ | q.2 ≤ Y - q.1 k}.indicator (fun q => gaussOdd V' (Y - q.1 k + c - q.2)) p
    with hΦdef
  have hΦm : Measurable Φ := by
    refine Measurable.indicator ?_ (measurableSet_le measurable_snd
      (measurable_const.sub ((measurable_pi_apply k).comp measurable_fst)))
    exact (measurable_gaussOdd V').comp (((measurable_const.sub
      ((measurable_pi_apply k).comp measurable_fst)).add measurable_const).sub measurable_snd)
  set Ψ : (ℕ → ℝ) → ℝ := fun f => gaussOdd (v k + V') (Y - f k + c) with hΨdef
  have hΨm : Measurable Ψ :=
    (measurable_gaussOdd _).comp ((measurable_const.sub (measurable_pi_apply k)).add
      measurable_const)
  have hΦb : ∀ p, |Φ p| ≤ 1 := by
    intro p
    simp only [hΦdef]
    by_cases hp : p ∈ {q : (ℕ → ℝ) × ℝ | q.2 ≤ Y - q.1 k}
    · rw [Set.indicator_of_mem hp]
      exact abs_le.2 ⟨neg_one_le_gaussOdd _ _, gaussOdd_le_one _ _⟩
    · rw [Set.indicator_of_notMem hp, abs_zero]
      norm_num
  have hΨb : ∀ f, |Ψ f| ≤ 1 := fun f =>
    abs_le.2 ⟨neg_one_le_gaussOdd _ _, gaussOdd_le_one _ _⟩
  have hle : ∀ f ∈ S, ∫ r, Φ (f, r) ∂(gaussianReal 0 (v k)) ≤ Ψ f := by
    intro f hf
    have hD : 0 ≤ Y - f k := by linarith [hf k le_rfl]
    have hstep := integral_indicator_Iic_gaussOdd_le hv V' hD hc0 hc
    have heq : (fun r => Φ (f, r))
        = (Set.Iic (Y - f k)).indicator (fun r => gaussOdd V' (Y - f k + c - r)) := by
      funext r
      simp only [hΦdef]
      by_cases hr : r ≤ Y - f k
      · rw [Set.indicator_of_mem (show (f, r) ∈ {q : (ℕ → ℝ) × ℝ | q.2 ≤ Y - q.1 k} from hr),
          Set.indicator_of_mem (show r ∈ Set.Iic (Y - f k) from hr)]
      · rw [Set.indicator_of_notMem (show (f, r) ∉ {q : (ℕ → ℝ) × ℝ | q.2 ≤ Y - q.1 k} from hr),
          Set.indicator_of_notMem (show r ∉ Set.Iic (Y - f k) from hr)]
    rw [heq]
    exact hstep
  have hcond := integral_indicator_comp_le_of_indepFun hX (h.measurable k) hS hΦm hΨm hΦb hΨb
    (h.indepFun_prefixSums_step k) (h.map_eq k) hle
  -- the pointwise comparison
  have hstepω : ∀ ω, walk G (k + 1) ω = walk G k ω + G k ω := fun ω => by
    rw [walk_succ]
    rfl
  have hA1 : survivalSet G g (k + 1) = survivalSet G g k ∩ {ω | walk G (k + 1) ω ≤ g (k + 1)} :=
    survivalSet_succ G g k
  have hpt : ∀ ω, (survivalSet G g (k + 1)).indicator
      (fun ω => gaussOdd V' (Y - walk G (k + 1) ω + c)) ω
      ≤ (X ⁻¹' S).indicator (fun ω => Φ (X ω, G k ω)) ω := by
    intro ω
    by_cases hω : ω ∈ survivalSet G g k
    · rw [← hA, Set.indicator_of_mem (show ω ∈ survivalSet G g k from hω)]
      simp only [hΦdef]
      by_cases hω1 : ω ∈ survivalSet G g (k + 1)
      · have hle1 : walk G (k + 1) ω ≤ g (k + 1) := by
          rw [hA1] at hω1
          exact hω1.2
        have hmem : (X ω, G k ω) ∈ {q : (ℕ → ℝ) × ℝ | q.2 ≤ Y - q.1 k} := by
          simp only [Set.mem_setOf_eq, hpre]
          linarith [hstepω ω]
        rw [Set.indicator_of_mem hω1, Set.indicator_of_mem hmem]
        simp only [hpre]
        rw [hstepω ω]
        apply le_of_eq
        congr 1
        ring
      · rw [Set.indicator_of_notMem hω1]
        by_cases hmem : (X ω, G k ω) ∈ {q : (ℕ → ℝ) × ℝ | q.2 ≤ Y - q.1 k}
        · rw [Set.indicator_of_mem hmem]
          simp only [Set.mem_setOf_eq, hpre] at hmem
          exact gaussOdd_nonneg _ (by simp only [hpre]; linarith)
        · rw [Set.indicator_of_notMem hmem]
    · have hω1 : ω ∉ survivalSet G g (k + 1) := fun hω1 => hω (by rw [hA1] at hω1; exact hω1.1)
      rw [Set.indicator_of_notMem hω1, ← hA, Set.indicator_of_notMem hω]
  have hint1 : Integrable (fun ω => (survivalSet G g (k + 1)).indicator
      (fun ω => gaussOdd V' (Y - walk G (k + 1) ω + c)) ω) μ :=
    ((integrable_gaussOdd_comp V' ((measurable_const.sub (h.measurable_walk (k + 1))).add
      measurable_const)).indicator (h.measurableSet_survivalSet g (k + 1)))
  have hint2 : Integrable (fun ω => (X ⁻¹' S).indicator (fun ω => Φ (X ω, G k ω)) ω) μ :=
    (Integrable.of_mem_Icc (-1) 1 (hΦm.comp (hX.prodMk (h.measurable k))).aemeasurable
      (ae_of_all _ fun ω => abs_le.1 (hΦb _))).indicator (hX hS)
  have hRHS : (fun ω => (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω)
      = fun ω => (survivalSet G g k).indicator
          (fun ω => gaussOdd (v k + V') (Y - walk G k ω + c)) ω := by
    funext ω
    rw [hA]
    by_cases hω : ω ∈ X ⁻¹' S
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      simp only [hΨdef, hpre]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  calc ∫ ω, (survivalSet G g (k + 1)).indicator
        (fun ω => gaussOdd V' (Y - walk G (k + 1) ω + c)) ω ∂μ
      ≤ ∫ ω, (X ⁻¹' S).indicator (fun ω => Φ (X ω, G k ω)) ω ∂μ := integral_mono hint1 hint2 hpt
    _ ≤ ∫ ω, (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω ∂μ := hcond
    _ = ∫ ω, (survivalSet G g k).indicator
          (fun ω => gaussOdd (v k + V') (Y - walk G k ω + c)) ω ∂μ := by rw [hRHS]

/-- **The supermartingale, iterated**: for `m ≤ n` with `g(j) ≤ Y` on `[m, n]`, nonzero variances
and `c ≥ √(πv_j/2)`, `c > 0`: `P(A_n) ≤ E[1_{A_m}κ_V(Y - S_m + c)]`, `V = ∑_{m ≤ i < n} v_i`.  At
`m = n` the tube is `1` on `A_n`; each step down is
`RMF.IsGaussianWalk.integral_survival_gaussOdd_step`. -/
theorem IsGaussianWalk.measureReal_survival_le_integral_gaussOdd (h : IsGaussianWalk G v μ)
    {g : ℕ → ℝ} {Y c : ℝ} {m n : ℕ} (hmn : m ≤ n) (hg : ∀ j, m ≤ j → j ≤ n → g j ≤ Y)
    (hv : ∀ j, v j ≠ 0) (hc0 : 0 < c) (hc : ∀ j, √(π * v j / 2) ≤ c) :
    μ.real (survivalSet G g n)
      ≤ ∫ ω, (survivalSet G g m).indicator
          (fun ω => gaussOdd (∑ i ∈ Finset.Ico m n, v i) (Y - walk G m ω + c)) ω ∂μ := by
  have key : ∀ d, d ≤ n - m → μ.real (survivalSet G g n)
      ≤ ∫ ω, (survivalSet G g (n - d)).indicator
          (fun ω => gaussOdd (∑ i ∈ Finset.Ico (n - d) n, v i)
            (Y - walk G (n - d) ω + c)) ω ∂μ := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty]
      rw [← integral_indicator_one (h.measurableSet_survivalSet g n)]
      refine le_of_eq (integral_congr_ae (ae_of_all _ fun ω => ?_))
      by_cases hω : ω ∈ survivalSet G g n
      · have hSn : walk G n ω ≤ g n := hω n le_rfl
        have hgn := hg n hmn le_rfl
        rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, gaussOdd_zero_var (by linarith)]
        rfl
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    | succ d ih =>
      intro hd
      have hk : n - (d + 1) + 1 = n - d := by omega
      have hstep := h.integral_survival_gaussOdd_step (g := g) (Y := Y) (c := c)
        (∑ i ∈ Finset.Ico (n - d) n, v i) (k := n - (d + 1))
        (hg _ (by omega) (by omega)) (by rw [hk]; exact hg _ (by omega) (by omega)) (hv _) hc0
        (hc _)
      rw [hk] at hstep
      have hsum : v (n - (d + 1)) + ∑ i ∈ Finset.Ico (n - d) n, v i
          = ∑ i ∈ Finset.Ico (n - (d + 1)) n, v i := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n - (d + 1) < n), hk]
      rw [hsum] at hstep
      exact le_trans (ih (by omega)) hstep
  have := key (n - m) le_rfl
  rwa [Nat.sub_sub_self hmn] at this

/-- **Survival past a split, at the Gaussian constant.**  For a nondecreasing barrier, `m < n`,
variances in `[v₋, v₊]` and `c ≥ √(πv₊/2)`, `c > 0`:
`P(A_n) ≤ √(2/(π(n-m)v₋))·(E[1_{A_m}(g(m) - S_m)] + (g(n) - g(m) + c)P(A_m))`.  The supermartingale
at the constant barrier `g(n)` (`RMF.IsGaussianWalk.measureReal_survival_le_integral_gaussOdd`) and
`κ_V(z) ≤ z√(2/(πV))`. -/
theorem IsGaussianWalk.measureReal_survival_le_split_sharp (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hvb : VarBracket v vmin vmax) {g : ℕ → ℝ} (hg : Monotone g) {m n : ℕ}
    (hmn : m < n) {c : ℝ} (hc0 : 0 < c) (hc : √(π * vmax / 2) ≤ c) :
    μ.real (survivalSet G g n)
      ≤ √(2 / (π * (((n - m : ℕ) : ℝ) * vmin)))
        * (∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ
          + (g n - g m + c) * μ.real (survivalSet G g m)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hvb
  have hv : ∀ j, v j ≠ 0 := fun j h0 => by
    have := hlo j
    rw [h0, NNReal.coe_zero] at this
    linarith
  have hcj : ∀ j, √(π * v j / 2) ≤ c := fun j =>
    le_trans (Real.sqrt_le_sqrt (by nlinarith [hhi j, Real.pi_pos])) hc
  have hsurv := h.measureReal_survival_le_integral_gaussOdd (Y := g n) hmn.le
    (fun j _ hj => hg hj) hv hc0 hcj
  set V : ℝ≥0 := ∑ i ∈ Finset.Ico m n, v i with hVdef
  have hVge : ((n - m : ℕ) : ℝ) * vmin ≤ (V : ℝ) := by
    rw [hVdef, NNReal.coe_sum]
    calc ((n - m : ℕ) : ℝ) * vmin = ∑ _i ∈ Finset.Ico m n, vmin := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.Ico m n, (v i : ℝ) := Finset.sum_le_sum fun i _ => hlo i
  have hnm : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - m by omega)
  have hV0 : (0 : ℝ) < (V : ℝ) := lt_of_lt_of_le (by positivity) hVge
  have hVne : V ≠ 0 := fun h0 => by rw [h0, NNReal.coe_zero] at hV0; exact lt_irrefl _ hV0
  set K := √(2 / (π * (((n - m : ℕ) : ℝ) * vmin))) with hKdef
  have hsq : √(2 / (π * V)) ≤ K :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hVge Real.pi_pos.le))
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hAm := h.measurableSet_survivalSet g m
  have hint_m : Integrable (walk G m) μ := integrable_of_hasLaw_gaussianReal
    (h.measurable_walk m) (h.map_walk m)
  have hpt : ∀ ω, (survivalSet G g m).indicator
      (fun ω => gaussOdd V (g n - walk G m ω + c)) ω
      ≤ K * ((survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω
        + (g n - g m + c) * (survivalSet G g m).indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    by_cases hω : ω ∈ survivalSet G g m
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hSm : walk G m ω ≤ g m := hω m le_rfl
      have hgmn : g m ≤ g n := hg hmn.le
      have hz : 0 ≤ g n - walk G m ω + c := by linarith
      calc gaussOdd V (g n - walk G m ω + c) ≤ (g n - walk G m ω + c) * √(2 / (π * V)) :=
            gaussOdd_le_mul_sqrt hVne hz
        _ ≤ (g n - walk G m ω + c) * K := mul_le_mul_of_nonneg_left hsq hz
        _ = K * (g m - walk G m ω + (g n - g m + c) * 1) := by ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      simp
  have hint1 : Integrable (fun ω => (survivalSet G g m).indicator
      (fun ω => gaussOdd V (g n - walk G m ω + c)) ω) μ :=
    (integrable_gaussOdd_comp V ((measurable_const.sub (h.measurable_walk m)).add
      measurable_const)).indicator hAm
  have hintA : Integrable ((survivalSet G g m).indicator (fun ω => g m - walk G m ω)) μ :=
    ((integrable_const _).sub hint_m).indicator hAm
  have hint1' : Integrable ((survivalSet G g m).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hAm
  have hint2 : Integrable (fun ω => K * ((survivalSet G g m).indicator
      (fun ω => g m - walk G m ω) ω + (g n - g m + c)
        * (survivalSet G g m).indicator (fun _ => (1 : ℝ)) ω)) μ :=
    (hintA.add (hint1'.const_mul _)).const_mul K
  calc μ.real (survivalSet G g n)
      ≤ ∫ ω, (survivalSet G g m).indicator
          (fun ω => gaussOdd V (g n - walk G m ω + c)) ω ∂μ := hsurv
    _ ≤ ∫ ω, K * ((survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω
          + (g n - g m + c) * (survivalSet G g m).indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono hint1 hint2 hpt
    _ = K * (∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ
          + (g n - g m + c) * μ.real (survivalSet G g m)) := by
        have hone : ∫ ω, (survivalSet G g m).indicator (fun _ => (1 : ℝ)) ω ∂μ
            = μ.real (survivalSet G g m) := integral_indicator_one hAm
        rw [integral_const_mul, integral_add hintA (hint1'.const_mul _), integral_const_mul, hone]

end Walk

/-! ### Probability Result 1 at the Gaussian constant -/

section Result1

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- `n/⌊n/M⌋ ≤ 2M` once `⌊n/M⌋ ≥ 1`: `log n - log ⌊n/M⌋ ≤ log(2M)`. -/
lemma log_sub_log_div_le {n M : ℕ} (hM : 1 ≤ M) (hm : 1 ≤ n / M) :
    Real.log n - Real.log ((n / M : ℕ) : ℝ) ≤ Real.log (2 * M) := by
  have hm0 : (0 : ℝ) < ((n / M : ℕ) : ℝ) := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := le_trans hm (Nat.div_le_self n M)
    exact_mod_cast this
  have hlt : n < M * (n / M + 1) := by
    have := Nat.lt_mul_div_succ n (show 0 < M by omega)
    linarith
  have hle : (n : ℝ) ≤ 2 * M * ((n / M : ℕ) : ℝ) := by
    have h2 : n ≤ 2 * M * (n / M) := by nlinarith
    exact_mod_cast h2
  rw [← Real.log_div hn0.ne' hm0.ne']
  exact Real.log_le_log (div_pos hn0 hm0) ((div_le_iff₀ hm0).2 hle)

/-- **Probability Result 1 at the Gaussian constant.**  For a Gaussian walk with variances in
`[v₋, v₊]`, a barrier `a + β log j` with `a, β ≥ 0`, an integer `M ≥ 2`, `c ≥ √(πv₊/2)` positive,
`K > 0` with `2M ≤ K²(M-1)πv₋`, and `U` with `KU ≥ 1` and
`a + √(πv₊/2) + c + β(3 + log 2 + log(2M) + 2 log(KU)) ≤ U`:
`P(S_j ≤ a + β log j ∀ j ≤ n) ≤ KU/√n` for every `n ≥ 1`.  Split at `m = ⌊n/M⌋`
(`RMF.IsGaussianWalk.measureReal_survival_le_split_sharp`): the potential at `m` is optional
stopping with the renewal sum of the barrier, and the barrier rises by at most `β log(2M)`. -/
theorem IsGaussianWalk.measureReal_forall_le_log_le_sharp (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a β K U c : ℝ} {M : ℕ} (ha : 0 ≤ a)
    (hβ : 0 ≤ β) (hK : 0 < K) (hKU : 1 ≤ K * U) (hM : 2 ≤ M) (hc0 : 0 < c)
    (hc : √(π * vmax / 2) ≤ c) (hKM : 2 * (M : ℝ) ≤ K ^ 2 * ((M : ℝ) - 1) * (π * vmin))
    (hU : a + √(π * vmax / 2) + c
      + β * (3 + Real.log 2 + Real.log (2 * M) + 2 * Real.log (K * U)) ≤ U)
    {n : ℕ} (hn : 1 ≤ n) :
    μ.real {ω | ∀ j ≤ n, walk G j ω ≤ a + β * Real.log j} ≤ K * U / √n := by
  have hvb := hv
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  set g : ℕ → ℝ := fun j => a + β * Real.log j with hgdef
  have hU0 : 0 < U := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hg0 : 0 ≤ g 0 := by simp [hgdef, ha]
  have hgmono : Monotone g := by
    intro i j hij
    simp only [hgdef]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [Nat.cast_zero, Real.log_zero, mul_zero, add_zero]
      have : 0 ≤ Real.log (j : ℝ) := Real.log_natCast_nonneg j
      nlinarith
    · have hiR : (0 : ℝ) < i := by exact_mod_cast hi
      have hle : Real.log (i : ℝ) ≤ Real.log (j : ℝ) :=
        Real.log_le_log hiR (by exact_mod_cast hij)
      nlinarith
  have hset : ∀ k, {ω | ∀ j ≤ k, walk G j ω ≤ a + β * Real.log j} = survivalSet G g k :=
    fun k => rfl
  rw [hset]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    by_cases hsmall : √(n : ℝ) ≤ K * U
    · calc μ.real (survivalSet G g n) ≤ 1 := measureReal_le_one
        _ ≤ K * U / √n := by rw [le_div_iff₀ hsn]; linarith
    push Not at hsmall
    have hn2 : 2 ≤ n := by
      have h1 : (1 : ℝ) < √(n : ℝ) := lt_of_le_of_lt hKU hsmall
      have h2 : (1 : ℝ) < n := by
        have := (Real.lt_sqrt zero_le_one).1 h1
        simpa using this
      exact_mod_cast h2
    set m := n / M with hmdef
    have hmn : m < n := Nat.div_lt_self (by omega) (by omega)
    have hsplit := h.measureReal_survival_le_split_sharp hvb hgmono hmn hc0 hc
    -- the potential at `m`
    have hΦ : ∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ
        ≤ a + √(π * vmax / 2) + β * (3 + Real.log 2 + 2 * Real.log (K * U)) := by
      have hopt := h.integral_survival_le hgmono hg0 hhi m
      have hsum : ∑ j ∈ Finset.range m, (g (j + 1) - g j) * μ.real (survivalSet G g j)
          ≤ β * (3 + Real.log 2 + 2 * Real.log (K * U)) := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · rw [hm0, Finset.sum_range_zero]
          have : 0 ≤ Real.log (K * U) := Real.log_nonneg hKU
          have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          positivity
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm0]
        have hfirst : (g (0 + 1) - g 0) * μ.real (survivalSet G g 0) = 0 := by
          simp [hgdef]
        rw [hfirst, zero_add]
        refine le_trans (Finset.sum_le_sum fun j hj => ?_) (sum_log_barrier_le hβ hKU m)
        have hj := Finset.mem_Ico.1 hj
        have hgj : g (j + 1) - g j = β * Real.log ((j + 1 : ℕ) : ℝ) - β * Real.log (j : ℝ) := by
          simp only [hgdef]
          push_cast
          ring
        have hg0j : 0 ≤ g (j + 1) - g j := sub_nonneg.2 (hgmono (Nat.le_succ j))
        rw [← hgj]
        refine mul_le_mul_of_nonneg_left (le_min measureReal_le_one ?_) hg0j
        exact ih j (by omega) (by omega)
      have hD : √(π * vmax / 2) * (1 - μ.real (survivalSet G g m)) ≤ √(π * vmax / 2) := by
        have h1 : 0 ≤ μ.real (survivalSet G g m) := measureReal_nonneg
        nlinarith [Real.sqrt_nonneg (π * vmax / 2)]
      have hg0a : g 0 = a := by simp [hgdef]
      linarith
    -- the rise of the barrier
    have hrise : g n - g m ≤ β * Real.log (2 * M) := by
      simp only [hgdef]
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0]
        simp only [Nat.cast_zero, Real.log_zero, mul_zero, add_zero]
        have hnM : n < M := by
          by_contra hge
          push Not at hge
          have : 1 ≤ n / M := (Nat.one_le_div_iff (by omega)).2 hge
          omega
        have hlog : Real.log (n : ℝ) ≤ Real.log (2 * M) :=
          Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
            (by have : (n : ℝ) ≤ M := by exact_mod_cast hnM.le
                linarith)
        nlinarith
      · have h := log_sub_log_div_le (n := n) (M := M) (by omega) hm0
        nlinarith
    -- the density factor
    have hfac : √(2 / (π * (((n - m : ℕ) : ℝ) * vmin))) ≤ K / √n := by
      have hnm : (n : ℝ) * ((M : ℝ) - 1) ≤ (M : ℝ) * ((n - m : ℕ) : ℝ) := by
        have h1 : M * m ≤ n := Nat.mul_div_le n M
        have h2 : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
          rw [Nat.cast_sub hmn.le]
        rw [h2]
        have h3 : (M : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        nlinarith
      have hnm0 : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - m by omega)
      have hM1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
        have : (2 : ℝ) ≤ M := by exact_mod_cast hM
        linarith
      rw [show K / √(n : ℝ) = √(K ^ 2 / n) by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hK.le]]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast (show 0 < n by omega))]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_le_mul_of_nonneg_left hKM hn0, mul_le_mul_of_nonneg_left hnm
        (by positivity : (0 : ℝ) ≤ K ^ 2 * (π * vmin))]
    have hPm := measureReal_le_one (μ := μ) (s := survivalSet G g m)
    have hPm0 := measureReal_nonneg (μ := μ) (s := survivalSet G g m)
    have hrise0 : 0 ≤ g n - g m + c := by linarith [hgmono hmn.le]
    have hinner : ∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ
        + (g n - g m + c) * μ.real (survivalSet G g m) ≤ U := by
      have h1 : (g n - g m + c) * μ.real (survivalSet G g m) ≤ g n - g m + c := by
        nlinarith
      linarith
    have hinner0 : 0 ≤ ∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ
        + (g n - g m + c) * μ.real (survivalSet G g m) := by
      have h1 : 0 ≤ ∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ := by
        refine integral_nonneg fun ω => ?_
        change (0 : ℝ) ≤ _
        by_cases hω : ω ∈ survivalSet G g m
        · rw [Set.indicator_of_mem hω]
          have := hω m le_rfl
          linarith
        · rw [Set.indicator_of_notMem hω]
      positivity
    calc μ.real (survivalSet G g n)
        ≤ √(2 / (π * (((n - m : ℕ) : ℝ) * vmin)))
          * (∫ ω, (survivalSet G g m).indicator (fun ω => g m - walk G m ω) ω ∂μ
            + (g n - g m + c) * μ.real (survivalSet G g m)) := hsplit
      _ ≤ K / √n * U := mul_le_mul hfac hinner hinner0 (by positivity)
      _ = K * U / √n := by ring

/-- The additive constant of `RMF.IsGaussianWalk.measureReal_forall_le_log_le_affine_sharp`,
`2√(πv₊/2) + β(1 + log 2 + log(2M)) + 2β log(KT)`. -/
noncomputable def result1SharpShift (vmax β K T : ℝ) (M : ℕ) : ℝ :=
  2 * √(π * vmax / 2) + β * (1 + Real.log 2 + Real.log (2 * M)) + 2 * β * Real.log (K * T)

lemma result1SharpShift_nonneg {vmax β K T : ℝ} {M : ℕ} (hβ : 0 ≤ β) (hKT : 1 ≤ K * T)
    (hM : 1 ≤ M) : 0 ≤ result1SharpShift vmax β K T M := by
  have h1 : 0 ≤ √(π * vmax / 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log (2 * M) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                        linarith)
  have h4 : 0 ≤ Real.log (K * T) := Real.log_nonneg hKT
  unfold result1SharpShift
  have h5 : 0 ≤ β * (1 + Real.log 2 + Real.log (2 * M)) := mul_nonneg hβ (by linarith)
  have h6 : 0 ≤ 2 * β * Real.log (K * T) := by positivity
  linarith

/-- **Probability Result 1 at the Gaussian constant, in affine form.**  For `T > 2β`, every level
`ℓ ≥ 0` and `n ≥ 1`, `P(S_j ≤ ℓ + β log j ∀ j ≤ n) ≤ K(ℓ + σ)/((1 - 2β/T)√n)` with
`σ = result1SharpShift v₊ β K T M`, given `2M ≤ K²(M-1)πv₋`, `KT ≥ 1` and `Kσ ≥ 1`.
`RMF.IsGaussianWalk.measureReal_forall_le_log_le_sharp` at `c = √(πv₊/2)` and the level
`U = (ℓ + σ)/(1 - 2β/T)`, with `log(KU) ≤ log(KT) + U/T - 1`. -/
theorem IsGaussianWalk.measureReal_forall_le_log_le_affine_sharp (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {β K T ℓ : ℝ} {M : ℕ} (hβ : 0 ≤ β)
    (hK : 0 < K) (hT : 2 * β < T) (hKT : 1 ≤ K * T) (hM : 2 ≤ M)
    (hKM : 2 * (M : ℝ) ≤ K ^ 2 * ((M : ℝ) - 1) * (π * vmin))
    (hKσ : 1 ≤ K * result1SharpShift vmax β K T M) (hℓ : 0 ≤ ℓ) {n : ℕ} (hn : 1 ≤ n) :
    μ.real {ω | ∀ j ≤ n, walk G j ω ≤ ℓ + β * Real.log j}
      ≤ K * ((ℓ + result1SharpShift vmax β K T M) / (1 - 2 * β / T)) / √(n : ℝ) := by
  have hvb := hv
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hlo 0) (hhi 0))
  set σ := result1SharpShift vmax β K T M with hσdef
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - 2 * β / T := by
    rw [sub_pos, div_lt_one hT0]
    exact hT
  have hden1 : 1 - 2 * β / T ≤ 1 := by
    have : 0 ≤ 2 * β / T := by positivity
    linarith
  have hσ0 : 0 ≤ σ := result1SharpShift_nonneg hβ hKT (by omega)
  set U := (ℓ + σ) / (1 - 2 * β / T) with hUdef
  have hUσ : σ ≤ U := by
    rw [hUdef, le_div_iff₀ hden]
    nlinarith
  have hKU : 1 ≤ K * U := le_trans hKσ (mul_le_mul_of_nonneg_left hUσ hK.le)
  have hU0 : 0 < U := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hc0 : 0 < √(π * vmax / 2) := Real.sqrt_pos.2 (by positivity)
  have hU : ℓ + √(π * vmax / 2) + √(π * vmax / 2)
      + β * (3 + Real.log 2 + Real.log (2 * M) + 2 * Real.log (K * U)) ≤ U := by
    have hlog : Real.log (K * U) ≤ Real.log (K * T) + U / T - 1 := by
      have h1 : Real.log (K * U) = Real.log (K * T) + Real.log (U / T) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      have h2 : Real.log (U / T) ≤ U / T - 1 := Real.log_le_sub_one_of_pos (by positivity)
      linarith
    have hUid : U - 2 * β * (U / T) = ℓ + σ := by
      have hne : T - 2 * β ≠ 0 := (sub_pos.2 hT).ne'
      rw [hUdef]
      field_simp
    have hβlog := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * β)
    rw [hσdef, result1SharpShift] at hUid
    nlinarith [hβlog, hUid]
  exact h.measureReal_forall_le_log_le_sharp hvb (le_trans (le_refl 0) hℓ) hβ hK hKU hM hc0
    le_rfl hKM hU hn

end Result1

end RMF
