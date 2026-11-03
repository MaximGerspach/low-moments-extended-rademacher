/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerDamped
import RMF.Weighted.LineSplit
import RMF.Reduction.RademacherHarperMoment

/-!
# The weighted Rademacher sum at fixed `q < ½`: the order of magnitude

For fixed `0 < q < ½`, `E|S(x)|^{2q} ≍ (log log x)^{-q/2}`, `S(x) = ∑_{n≤x} f(n)/√n`
(`RMF.exists_integral_rpow_weightedRademacherSum_asymp_smallQ`).

The upper bound is `RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp`.  The
lower bound (`RMF.exists_le_integral_rpow_weightedRademacherSum_smallQ_fixed`) is
`RMF.exists_le_integral_rpow_weightedRademacherSum_euler` with `V` a large constant:

* the main term's window `|t| < 1` contains `[-½, ½]`, where Harper's lower bound for the
  Rademacher Euler product (`RMF.exists_le_integral_rpow_chaosShift_rademacher`, itself read off
  `1/3 ≤ t ≤ 1/2`) gives `E[(∫|F|²)^q] ≫ V^{-q} (log x)^q (log log x)^{-q/2}`;
* the subtracted term's integral decreases in the shift (Parseval: the smooth sum vanishes below
  `1`), so at `σ = V/log x` it is at most its value at `σ = 1/log x`, which the small-`q` upper
  bound machinery bounds by `(log x)^q (log log x)^{-q/2}` up to a constant depending on `q`
  (`RMF.exists_const_integral_rpow_lineDiv_floor_le`);
* then `e^{-Vq}` beats `V^{-q}` for `V` large, and `(log x)^{-q}` is negligible.

At `q = ½` the argument breaks down.  The subtracted term is then of the size of the whole
moment, `(log log x)^{3/4}`, and `e^{-Vq}` at a constant `V` cannot absorb it against a window
bound of size `(log log x)^{-1/4}`: every scale `|t| ≍ T` contributes at the boundary, not only
`|t| ≍ 1`, and the lower bound has to see all of them.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The damped line integral decreases in the shift -/

omit [MeasurableSpace Ω] in
/-- **The damped line integral decreases in the shift.**  By Parseval it is
`2π ∫_0^∞ |A(u)|² u^{-1-2σ} du`, and the smooth sum `A` vanishes below `1`, where
`u^{-1-2σ}` would increase with `σ`. -/
lemma integral_lineDiv_le_of_le {X : ℕ → Ω → ℂ} (N : ℕ) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁)
    (hσ : σ₁ ≤ σ₂) (ω : Ω) :
    (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ₂ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ₂ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ₁ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hσ₂ : 0 < σ₂ := lt_of_lt_of_le hσ₁ hσ
  have h₁ := integral_normSq_smoothWeightedSum_eq_line (X := X) N hσ₁ ω
  have h₂ := integral_normSq_smoothWeightedSum_eq_line (X := X) N hσ₂ ω
  have hmono : (∫ u in Set.Ioi (0 : ℝ),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) N u ω‖ ^ 2
          / u ^ (1 + 2 * σ₂))
      ≤ ∫ u in Set.Ioi (0 : ℝ),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) N u ω‖ ^ 2
          / u ^ (1 + 2 * σ₁) := by
    refine setIntegral_mono_on (integrableOn_normSq_smoothWeightedSum N hσ₂ ω)
      (integrableOn_normSq_smoothWeightedSum N hσ₁ ω) measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rcases lt_or_ge u 1 with h | h
    · simp [smoothWeightedSum_eq_zero_of_lt_one _ N h ω]
    · exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hu0 _)
        (Real.rpow_le_rpow_of_exponent_le h (by linarith))
  rw [h₁, h₂] at hmono
  have hpi : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  exact le_of_mul_le_mul_left hmono hpi

/-- **Its `q`-th moment decreases in the shift too.** -/
lemma integral_rpow_lineDiv_le_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {N : ℕ} (hN : 2 ≤ N)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₂) {q : ℝ} (hq0 : 0 ≤ q) :
    (∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ₂ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ₂ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          (N + 1) ((1 / 2 : ℂ) + (σ₁ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ :=
  integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ =>
      Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)
    (integrable_rpow_eulerProductLine_of_two_le hX hN hσ₁ hq0)
    (Filter.Eventually.of_forall fun ω =>
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (integral_lineDiv_le_of_le N hσ₁ hσ ω) hq0)

/-! ### The main term, against Harper's window -/

/-- **The window integral has an integrable `q`-th power**, for `0 < σ ≤ 1`: it is at most
twice the damped line integral (`RMF.half_setIntegral_Ioo_le_integral_div`). -/
lemma integrable_rpow_setIntegral_Ioo_normSq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q) μ := by
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  have hjoint : StronglyMeasurable fun z : Ω × ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1‖ ^ 2 := by
    have h := measurable_randomEulerProduct_sqfree_uncurry (X := X) hX.measurable
      (1 / 2 + σ) (y + 1)
    simp only [← hsline] at h
    exact (h.norm.pow_const 2).stronglyMeasurable
  have hmeas : StronglyMeasurable fun ω : Ω => ∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioo (-1 : ℝ) 1)) hjoint
  refine Integrable.mono'
    ((integrable_rpow_eulerProductLine_of_two_le hX hy hσ0 hq0).const_mul (2 ^ q))
    ((Real.continuous_rpow_const hq0).measurable.comp hmeas.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw (y + 1)] with ω hω
  have hwin := half_setIntegral_Ioo_le_integral_div hσ0 hσ1
    (integrable_line_div_sq_half_add (X := X) (N := y + 1) hσ0 hω)
  have hW0 : (0 : ℝ) ≤ ∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun t _ => sq_nonneg _
  have hJ0 : (0 : ℝ) ≤ ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := integral_nonneg fun t => sq_nonneg _
  change ‖(∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q‖
    ≤ 2 ^ q * (∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hW0 _), ← Real.mul_rpow (by norm_num) hJ0]
  exact Real.rpow_le_rpow hW0 (by linarith) hq0

omit [MeasurableSpace Ω] in
/-- **The window `|t| < 1` contains `RMF.chaosShift`'s `[-½, ½]`.** -/
lemma log_mul_chaosShift_le_setIntegral_Ioo {X : ℕ → Ω → ℂ} {x σ : ℝ} (hx : 1 < x)
    (hσ : 0 ≤ σ) {ω : Ω} (hω : ∀ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), ‖X p ω‖ ≤ 1) :
    Real.log x * chaosShift (fun ω => squarefreeExtension fun p => X p ω) x σ ω
      ≤ ∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := by
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  simp_rw [hsline]
  rw [chaosShift, ← mul_assoc, mul_inv_cancel₀ hlog, one_mul,
    intervalIntegral.integral_of_le (by norm_num)]
  have hbd : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      (⌊x⌋₊ + 1) (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound (⌊x⌋₊ + 1) :=
    fun t => norm_randomEulerProduct_sqfree_le hω
      (by rw [show ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I = shiftLine σ t from rfl,
        re_shiftLine]; linarith)
  have hint := integrableOn_windowOf (σ := 1 / 2 + σ)
    (measurable_randomEulerProduct_sqfree_line (X := X) (N := ⌊x⌋₊ + 1) (ω := ω) (1 / 2 + σ))
    hbd (-1) 1
  refine setIntegral_mono_set (hint.mono_set Set.Ioo_subset_Ioc_self)
    (Filter.Eventually.of_forall fun t => sq_nonneg _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **The main term against `RMF.chaosShift`.**  `(log x)^q E[chaosShift^q] ≤ E[W^q]`, `W` the
window integral of `RMF.exists_le_integral_rpow_weightedRademacherSum_euler`. -/
lemma rpow_log_mul_integral_chaosShift_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x σ q : ℝ} (hx : 2 ≤ x)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hq0 : 0 ≤ q) :
    Real.log x ^ q * ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => X p ω) x σ ω ^ q ∂μ
      ≤ ∫ ω, (∫ t in Set.Ioo (-1 : ℝ) 1,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ := by
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    (integrable_rpow_setIntegral_Ioo_normSq hX hy2 hσ0 hσ1 hq0) ?_
  · exact mul_nonneg (Real.rpow_nonneg hlog0.le _)
      (Real.rpow_nonneg (chaosShift_nonnegOf (inv_nonneg.2 hlog0.le) ω) _)
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊x⌋₊ + 1)] with ω hω
  have h0 := chaosShift_nonnegOf
    (F := fun ω => squarefreeExtension fun p => X p ω) (δ := σ) (inv_nonneg.2 hlog0.le) ω
  rw [← Real.mul_rpow hlog0.le h0]
  exact Real.rpow_le_rpow (mul_nonneg hlog0.le h0)
    (log_mul_chaosShift_le_setIntegral_Ioo (by linarith) hσ0.le hω) hq0

/-! ### The subtracted term: the small-`q` upper bound at `y = ⌊x⌋`

`RMF.exists_const_integral_rpow_lineDiv_le_rademacher_geom` is stated for any `y` and `σ` with
`σ log y ≤ 1`; the upper bound chain uses it at `y = x^{1/(4 log log x)}`.  Here it is needed at
`y = ⌊x⌋` and `σ = 1/log x`, where every condition is easier: `log ⌊x⌋` is within `log 2` of
`log x`. -/

/-- **The parameters at `y = ⌊x⌋` and `σ = 1/log x`.**  The twin of
`RMF.eventually_exists_mesoParams`. -/
theorem eventually_exists_mesoParams_floor (D₀ : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∃ J M : ℕ,
      2 ≤ ⌊x⌋₊ ∧ 0 < 1 / Real.log x ∧ 1 / Real.log x * Real.log (⌊x⌋₊ : ℝ) ≤ 1 ∧
      1 ≤ J ∧ (J : ℝ) ≤ Real.log (Real.log (⌊x⌋₊ : ℝ) - Real.log 2) + 1 ∧
      Real.exp (-(J : ℝ)) * Real.log ((⌊x⌋₊ : ℝ) + 1) ≤ 2 ∧
      1 ≤ M ∧ ((M : ℝ) + 1) ≤ Real.log (Real.log (⌊x⌋₊ : ℝ)) ^ 2 ∧
      Real.log (Real.log x) / 2 ≤ (J : ℝ) ∧ (J : ℝ) ≤ Real.log (Real.log x) + 1 ∧
      Real.log (Real.log x) / 2 ≤ Real.log (Real.log (⌊x⌋₊ : ℝ)) ∧
      (1 / Real.log x * Real.log (⌊x⌋₊ : ℝ))⁻¹ ≤ 8 * Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ (M : ℝ) ∧
      Real.log (Real.log x)
        ≤ 9 * ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ) ∧
      512 ≤ Real.log (Real.log x) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp (512 + 18 * (D₀ : ℝ))))]
    with x hx
  have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  have hlogx : Real.exp (512 + 18 * (D₀ : ℝ)) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hΛD : (512 : ℝ) + 18 * (D₀ : ℝ) ≤ Λ := by
    have h := Real.log_le_log (Real.exp_pos _) hlogx
    rwa [Real.log_exp] at h
  have hΛ : (512 : ℝ) ≤ Λ := by linarith
  have hL513 : (513 : ℝ) ≤ Real.log x := by
    have := Real.add_one_le_exp (512 + 18 * (D₀ : ℝ))
    linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx16 : (16 : ℝ) ≤ x := by
    have h1 : Real.log x + 1 ≤ x := by
      have := Real.add_one_le_exp (Real.log x)
      rwa [Real.exp_log hx0] at this
    linarith
  have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `y = ⌊x⌋`, with `x/2 ≤ y ≤ x`
  set y : ℕ := ⌊x⌋₊ with hydef
  have hyx : (y : ℝ) ≤ x := Nat.floor_le hx0.le
  have hyx2 : x / 2 ≤ (y : ℝ) := by
    have := Nat.lt_floor_add_one x
    rw [← hydef] at this
    linarith
  have hy8 : (8 : ℝ) ≤ (y : ℝ) := by linarith
  have hy2 : 2 ≤ y := by exact_mod_cast (by linarith : (2 : ℝ) ≤ (y : ℝ))
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  -- `log x - log 2 ≤ log y ≤ log x`
  have hlogyx : Real.log (y : ℝ) ≤ Real.log x := Real.log_le_log hy0 hyx
  have hlogy2 : Real.log x - Real.log 2 ≤ Real.log (y : ℝ) := by
    have h := Real.log_le_log (by positivity) hyx2
    rwa [Real.log_div hx0.ne' (by norm_num)] at h
  have hlogy_half : Real.log x / 2 ≤ Real.log (y : ℝ) := by linarith
  have hlogy0 : (0 : ℝ) < Real.log (y : ℝ) := by linarith
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  -- `σ = 1/log x`
  have hσ0 : (0 : ℝ) < 1 / Real.log x := by positivity
  have hσy : 1 / Real.log x * Real.log (y : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hL0]
    exact hlogyx
  have hinv : (1 / Real.log x * Real.log (y : ℝ))⁻¹ = Real.log x / Real.log (y : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, inv_div]
  have h8S : (1 / Real.log x * Real.log (y : ℝ))⁻¹ ≤ 8 * Λ := by
    rw [hinv, div_le_iff₀ hlogy0]
    nlinarith
  -- `Λ - log 2 ≤ log log y ≤ Λ`
  have hLLy : Λ - Real.log 2 ≤ Real.log (Real.log (y : ℝ)) := by
    have h := Real.log_le_log (by positivity) hlogy_half
    rwa [Real.log_div hL0.ne' (by norm_num)] at h
  have hLLyx : Real.log (Real.log (y : ℝ)) ≤ Λ := Real.log_le_log hlogy0 hlogyx
  have hLLhalf : Λ / 2 ≤ Real.log (Real.log (y : ℝ)) := by linarith
  -- `J` and `M`
  obtain ⟨J, hJ1, hJw, hJle, hJlb⟩ := exists_mesoRange_index hy8
  obtain ⟨M, hM1, hM, hMlo⟩ := exists_mesoTail_index (L := Real.log (Real.log (y : ℝ)))
    (by linarith)
  have hJlo : Λ / 2 ≤ (J : ℝ) := by
    have hdiv : Real.log (Real.log (y : ℝ) / 2) = Real.log (Real.log (y : ℝ)) - Real.log 2 :=
      Real.log_div hlogy0.ne' (by norm_num)
    rw [hdiv] at hJlb
    linarith
  have hJhi : (J : ℝ) ≤ Λ + 1 := by
    refine le_trans hJle ?_
    have h1 : Real.log (Real.log (y : ℝ) - Real.log 2) ≤ Real.log (Real.log (y : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hMΛ : Λ ≤ (M : ℝ) := by nlinarith [hMlo, hLLhalf, hΛ]
  -- the barrier depth is comparable to `Λ`
  have hD₀y : (D₀ : ℝ) ≤ Real.log (Real.log (y : ℝ)) := by linarith
  have hcast := cast_harperBlockCount hD₀y
  have hfl : Real.log (Real.log (y : ℝ)) - 1
      ≤ ((⌊Real.log (Real.log (y : ℝ))⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one (Real.log (Real.log (y : ℝ)))]
  have hn : Λ / 2 - 1 - (D₀ : ℝ) ≤ ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  have hm4 : harperBlockCount D₀ (y : ℝ) ≤ 4 * (harperBlockCount D₀ (y : ℝ) / 4) + 3 := by
    omega
  have hm4R : ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ)
      ≤ 4 * ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hm4
  have hbar : Λ ≤ 9 * ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ) := by linarith
  exact ⟨J, M, hy2, hσ0, hσy, hJ1, hJle, hJw, hM1, hM, hJlo, hJhi, hLLhalf, h8S, hMΛ, hbar,
    hΛ⟩

set_option maxHeartbeats 1000000 in
-- the four range comparisons live in one context, as in the `reductionY` twin
/-- **`Z` at `y = ⌊x⌋` and `σ = 1/log x`**:
`E[((log ⌊x⌋)^{-1} ∫_ℝ |F(½+σ+it)|²/|σ+it|² dt)^q] ≪ min{log log x, 1+(q(1-2q))^{-1}}
(log log x)^{-q/2}` for `0 < q < ½`, uniformly in `q`.  The four ranges of
`RMF.exists_const_integral_rpow_lineDiv_le_rademacher_geom`, each against the target as in
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_min`. -/
theorem exists_const_integral_rpow_lineDiv_floor_le :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q < 1 / 2 →
          (∫ ω, ((Real.log (⌊x⌋₊ : ℝ))⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
            ≤ C * (min (Real.log (Real.log x)) (1 + (q * (1 - 2 * q))⁻¹)
                * (Real.log (Real.log x)) ^ (-(q / 2))) := by
  obtain ⟨D₀, yb, A₁, A₂, A₃, A₄, hA₁, hA₂, hA₃, hA₄, HG⟩ :=
    exists_const_integral_rpow_lineDiv_le_rademacher_geom (Ω := Ω)
  obtain ⟨x₂, hev⟩ := Filter.eventually_atTop.1
    ((eventually_exists_mesoParams_floor D₀).and (Filter.eventually_ge_atTop (yb + 1)))
  refine ⟨3 * A₁ + 8 * A₂ + 9 * max 1 A₃ + max 1 A₄, x₂, by positivity, ?_⟩
  intro X μ hX x q hx hq0 hq2
  obtain ⟨⟨J, M, hy2, hσ0, hσy, hJ1, hJle, hJw, hM1, hM, hJlo, hJhi, hLLhalf, h8S, hMΛ, hbar,
    hΛ⟩, hxb⟩ := hev x hx
  have hyb : yb ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hZ := HG X μ hX (1 / Real.log x) q ⌊x⌋₊ J M hyb hy2 hσ0 hσy hq0 hq2 hJ1 hJle hJw hM1 hM
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set α : ℝ := q * (1 - 2 * q) with hαdef
  have hα : (0 : ℝ) < α := by rw [hαdef]; exact mul_pos hq0 (by linarith)
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hlogy0 : (0 : ℝ) < Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hy2
    exact Real.log_pos (by linarith)
  -- (1) the central window
  have hS1 : (1 : ℝ) ≤ (1 / Real.log x * Real.log ((⌊x⌋₊ : ℕ) : ℝ))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    simpa using hσy
  have hErw : (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) ^ (q * (2 * q - 1))
      = Real.exp (-(α * Real.log (Real.log ((⌊x⌋₊ : ℕ) : ℝ)))) := by
    rw [Real.rpow_def_of_pos hlogy0]
    congr 1
    rw [hαdef]
    ring
  have hE : (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) ^ (q * (2 * q - 1)) ≤ Real.exp (-(α * Λ / 2)) := by
    rw [hErw]
    exact Real.exp_le_exp.2 (by nlinarith [hLLhalf, hα])
  have hT1 := central_le_target hA₁ hΛ hα hq0 (by linarith) hS1 h8S
    (Real.rpow_nonneg hlogy0.le _) hE
  -- (2) the mesoscopic range
  have hT2 := meso_le_target (J := J) hA₂ hΛ1 hα hq0 (by linarith) hJlo hJhi
  -- (3) the mid range
  have hbpos : (0 : ℝ) < 1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ) := by
    have := Real.sqrt_nonneg ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)
    linarith
  have hsq9 : Real.sqrt Λ ≤ 9 * (1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)) := by
    have h1 : Real.sqrt Λ
        ≤ Real.sqrt (9 * ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt hbar
    have h2 : Real.sqrt (9 * ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ))
        = 3 * Real.sqrt ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h2] at h1
    linarith
  have hT3 := mid_le_target hA₃ hΛ1 hq0 (by linarith) hbpos hsq9
  -- (4) the tail
  have hT4 := tail_le_target (M := M) hA₄ hΛ1 hq0 (by linarith) hMΛ
  -- assemble
  have hΛq0 : (0 : ℝ) ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hmin1 : (1 : ℝ) ≤ min Λ (1 + α⁻¹) :=
    le_min (by linarith) (by linarith [inv_pos.2 hα])
  have hlift : ∀ c : ℝ, 0 ≤ c →
      c * Λ ^ (-(q / 2)) ≤ c * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
    intro c hc
    have h1 : Λ ^ (-(q / 2)) ≤ min Λ (1 + α⁻¹) * Λ ^ (-(q / 2)) := by nlinarith [hmin1, hΛq0]
    exact mul_le_mul_of_nonneg_left h1 hc
  have hmax3 : (0 : ℝ) ≤ 9 * max 1 A₃ := by linarith [le_max_left (1 : ℝ) A₃]
  have hmax4 : (0 : ℝ) ≤ max 1 A₄ := by linarith [le_max_left (1 : ℝ) A₄]
  have hT3' := hT3.trans (hlift (9 * max 1 A₃) hmax3)
  have hT4' := hT4.trans (hlift (max 1 A₄) hmax4)
  refine le_trans hZ ?_
  have hsum : A₁ * ((1 / Real.log x * Real.log ((⌊x⌋₊ : ℕ) : ℝ))⁻¹) ^ q
          * (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) ^ (q * (2 * q - 1))
        + A₂ * (min (J : ℝ) (1 + (q * (1 - 2 * q))⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q))
        + (A₃ * (1 + (1 - 2 / 3)
            * Real.sqrt ((harperBlockCount D₀ ((⌊x⌋₊ : ℕ) : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ))
            ^ (3 * q / 2)
        + (A₄ / (M : ℝ)) ^ q
      ≤ (3 * A₁ + 8 * A₂ + 9 * max 1 A₃ + max 1 A₄) * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
    linarith [hT1, hT2, hT3', hT4']
  exact hsum

/-! ### Harper's window, with its conditions absorbed -/

/-- **Harper's lower bound for the Rademacher window, eventually in `x`.**
`RMF.exists_le_integral_rpow_chaosShift_rademacher` with its constants collected into one `c`
and its conditions on `x` absorbed: for `V ≥ 1` and `0 < q < 1`, eventually
`c (1+(1-q)√(log log x))^{-q} V^{-q} ≤ E[chaosShift(4V/log x)^q]`. -/
lemma exists_le_integral_rpow_chaosShift_rademacher_eventually :
    ∃ c : ℝ, 0 < c ∧ ∀ V : ℝ, 1 ≤ V → ∀ q : ℝ, 0 < q → q < 1 →
      ∀ᶠ x : ℝ in Filter.atTop, ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω),
        IsRademacherPrimeValues Y ν →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) * V ^ (-q)
            ≤ ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x
                (4 * V / Real.log x) ω ^ q ∂ν := by
  obtain ⟨a₀, α, hα, -, H⟩ := exists_le_integral_rpow_chaosShift_rademacher
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨B, H⟩ := H (a₀ / Real.log 2) (by rw [div_mul_cancel₀ _ hlog2.ne'])
  obtain ⟨E, hE, H⟩ := H B le_rfl Ω
  refine ⟨min α (α ^ (2 : ℝ)) * min 1 (1 / ((6 + 2 / Real.log 2) * E))
      * Real.exp (-(2 * (1 + a₀ / Real.log 2 * Real.log 2)))
      * Real.exp ((B : ℝ) + 73) ^ (-(2 : ℝ)), ?_, ?_⟩
  · have h1 : 0 < min α (α ^ (2 : ℝ)) := lt_min hα (Real.rpow_pos_of_pos hα _)
    have h2 : 0 < min 1 (1 / ((6 + 2 / Real.log 2) * E)) := lt_min one_pos (by positivity)
    exact mul_pos (mul_pos (mul_pos h1 h2) (Real.exp_pos _))
      (Real.rpow_pos_of_pos (Real.exp_pos _) _)
  intro V hV q hq0 hq1
  obtain ⟨Λ₀, x₀, H⟩ := H V hV
  have hLL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_ge_atTop x₀, Filter.eventually_ge_atTop 3,
    hLL.eventually_ge_atTop Λ₀, hLL.eventually_ge_atTop ((B : ℝ) + 2),
    hLL.eventually_ge_atTop (6 * (B : ℝ) + 3 * Real.log V + 49),
    hLL.eventually_ge_atTop (1 / q ^ 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7)),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 * V)]
    with x hx₀ hx3 hΛ₀ hB2 hB6 hq hL hL8
  intro Y ν hY
  have hL0 : 0 < Real.log x := by linarith
  have hσ0 : 0 < 4 * V / Real.log x := by positivity
  have hσ12 : 4 * V / Real.log x ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hσL : 4 * V / Real.log x * Real.log x = 4 * V := div_mul_cancel₀ _ hL0.ne'
  have hsq : 1 ≤ q * Real.sqrt (Real.log (Real.log x)) := by
    have hs : 1 / q ≤ Real.sqrt (Real.log (Real.log x)) := by
      rw [show 1 / q = Real.sqrt ((1 / q) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact hq)
    calc (1 : ℝ) = q * (1 / q) := by field_simp
      _ ≤ q * Real.sqrt (Real.log (Real.log x)) := mul_le_mul_of_nonneg_left hs hq0.le
  have h := H Y ν hY (4 * V / Real.log x) q x hx₀ (by linarith) hx3 hΛ₀ hB2 hB6 hL hσ0 hσ12
    hσL hq0 hq1 hsq
  refine le_trans (le_of_eq ?_) h
  ring

/-! ### Two pieces of arithmetic -/

/-- **The choice of `V`.**  For `r, q > 0`, `V = 2 + 2|log r|/q` has `V ≥ 2` and
`e^{-Vq} ≤ r V^{-q}`: `e^{-Vq/2} ≤ r` by the choice, and `e^{-Vq/2} ≤ V^{-q}` because
`V ≤ e^{V/2}`. -/
lemma exp_neg_mul_le_mul_rpow_neg {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    2 ≤ 2 + 2 * |Real.log r| / q ∧
      Real.exp (-((2 + 2 * |Real.log r| / q) * q))
        ≤ r * (2 + 2 * |Real.log r| / q) ^ (-q) := by
  set V : ℝ := 2 + 2 * |Real.log r| / q with hVdef
  have hV2 : 2 ≤ V := by
    have : 0 ≤ 2 * |Real.log r| / q := by positivity
    linarith
  have hV0 : 0 < V := by linarith
  refine ⟨hV2, ?_⟩
  have hhalf : V * q / 2 = q + |Real.log r| := by
    rw [hVdef]
    field_simp
  -- `e^{-Vq/2} ≤ r`
  have h1 : Real.exp (-(V * q / 2)) ≤ r := by
    calc Real.exp (-(V * q / 2)) ≤ Real.exp (Real.log r) := by
          refine Real.exp_le_exp.2 ?_
          rw [hhalf]
          linarith [neg_abs_le (Real.log r)]
      _ = r := Real.exp_log hr
  -- `e^{-Vq/2} ≤ V^{-q}`, from `log V ≤ V/2`
  have hlogV : Real.log V ≤ V / 2 := by
    rw [Real.log_le_iff_le_exp hV0]
    have h := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ V / 2)
    nlinarith [sq_nonneg (V - 2)]
  have h2 : Real.exp (-(V * q / 2)) ≤ V ^ (-q) := by
    rw [Real.rpow_def_of_pos hV0]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (-(V * q)) = Real.exp (-(V * q / 2)) * Real.exp (-(V * q / 2)) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ r * V ^ (-q) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le hr.le

/-- **The last error term is negligible**: `C L^{-q} ≤ ε (log L)^{-q/2}` once
`L ≥ (C/ε)^{2/q}`, `L > 1`.  At `L = log x`, the smoothing error against the target. -/
lemma mul_rpow_neg_le_mul_log_rpow_neg {C ε q L : ℝ} (hC : 0 < C) (hε : 0 < ε) (hq : 0 < q)
    (hL : 1 < L) (hLC : (C / ε) ^ (2 / q) ≤ L) :
    C * L ^ (-q) ≤ ε * Real.log L ^ (-(q / 2)) := by
  have hL0 : 0 < L := by linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos hL
  have hlogL : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  -- `C L^{-q/2} ≤ ε`
  have hpow : C / ε ≤ L ^ (q / 2) := by
    have h := Real.rpow_le_rpow (by positivity) hLC (by positivity : (0 : ℝ) ≤ q / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / q * (q / 2) = 1 by field_simp,
      Real.rpow_one] at h
  have hLq : 0 < L ^ (q / 2) := Real.rpow_pos_of_pos hL0 _
  have hCL : C * L ^ (-(q / 2)) ≤ ε := by
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, div_le_iff₀ hLq]
    rw [div_le_iff₀ hε] at hpow
    linarith
  -- `L^{-q/2} ≤ (log L)^{-q/2}`
  have hmono : L ^ (-(q / 2)) ≤ Real.log L ^ (-(q / 2)) :=
    Real.rpow_le_rpow_of_nonpos hlogL0 hlogL (by linarith)
  have hsplit : L ^ (-q) = L ^ (-(q / 2)) * L ^ (-(q / 2)) := by
    rw [← Real.rpow_add hL0]
    ring_nf
  rw [hsplit, ← mul_assoc]
  calc C * L ^ (-(q / 2)) * L ^ (-(q / 2)) ≤ ε * L ^ (-(q / 2)) :=
        mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0.le _)
    _ ≤ ε * Real.log L ^ (-(q / 2)) := mul_le_mul_of_nonneg_left hmono hε.le

/-- Harper's denominator against the plain power: `(1+(1-q)√Λ)^{-q} ≥ 2^{-q} Λ^{-q/2}` for
`Λ ≥ 1` and `0 ≤ q ≤ 1`, since `1 + (1-q)√Λ ≤ 2√Λ`. -/
lemma two_rpow_neg_mul_le_target {q Λ : ℝ} (hΛ : 1 ≤ Λ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (2 : ℝ) ^ (-q) * Λ ^ (-(q / 2)) ≤ (1 + (1 - q) * Real.sqrt Λ) ^ (-q) := by
  have hs1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ
  have hbase : 1 + (1 - q) * Real.sqrt Λ ≤ 2 * Real.sqrt Λ := by nlinarith
  have hpos : 0 < 1 + (1 - q) * Real.sqrt Λ := by nlinarith
  have h1 := Real.rpow_le_rpow_of_nonpos hpos hbase (by linarith : -q ≤ 0)
  have h2 : (2 * Real.sqrt Λ) ^ (-q) = (2 : ℝ) ^ (-q) * Λ ^ (-(q / 2)) := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by linarith)]
    ring_nf
  rw [h2] at h1
  exact h1

/-- **The assembly, as arithmetic.**  `ES, EW, EJ, EJ₁, EZ, Ech` are the moment, the window,
the damped line at `V/log x` and at `1/log x`, its normalised form and Harper's chaos integral;
`L = log x`, `Λ = log log x`.  With `V` chosen so that `e^{-Vq} ≤ r V^{-q}`, the main term is
`4ε Λ^{-q/2}`, the subtracted term at most `2ε Λ^{-q/2}` and the error at most `ε Λ^{-q/2}`. -/
lemma smallQ_fixed_assembly {ES EW EJ EJ₁ EZ Ech T L Λ V c₀ C₀ cL K' q : ℝ}
    (hL : 0 < L) (hΛ : 1 ≤ Λ) (hV0 : 0 < V) (hc₀ : 0 < c₀)
    (hC₀ : 0 < C₀) (hcL : 0 < cL) (hK' : 0 < K')
    (h1 : c₀ * L ^ (-q) * EW - C₀ * Real.exp (-(V * q)) * L ^ (-q) * EJ - C₀ * L ^ (-q) ≤ ES)
    (h2 : L ^ q * Ech ≤ EW) (h3 : cL * T * (V / 2) ^ (-q) ≤ Ech)
    (hT : (2 : ℝ) ^ (-q) * Λ ^ (-(q / 2)) ≤ T)
    (h4 : EJ ≤ EJ₁) (h6 : EJ₁ ≤ L ^ q * EZ) (h5 : EZ ≤ K' * Λ ^ (-(q / 2)))
    (hVe : Real.exp (-(V * q)) ≤ c₀ * cL / (2 * C₀ * K') * V ^ (-q))
    (hneg : C₀ * L ^ (-q) ≤ c₀ * cL * V ^ (-q) / 4 * Λ ^ (-(q / 2))) :
    c₀ * cL * V ^ (-q) / 4 * Λ ^ (-(q / 2)) ≤ ES := by
  have hLq : L ^ (-q) * L ^ q = 1 := by
    rw [← Real.rpow_add hL, neg_add_cancel, Real.rpow_zero]
  have hLn0 : 0 ≤ L ^ (-q) := Real.rpow_nonneg hL.le _
  have hΛ0 : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg (by linarith) _
  have hVq : 0 < V ^ (-q) := Real.rpow_pos_of_pos hV0 _
  have h2q : (2 : ℝ) ^ (-q) * 2 ^ q = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have hV2 : (V / 2) ^ (-q) = V ^ (-q) * 2 ^ q := by
    rw [Real.div_rpow hV0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
  have hT0 : 0 ≤ (2 : ℝ) ^ (-q) * Λ ^ (-(q / 2)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hΛ0
  -- the main term: `c₀ L^{-q} EW ≥ c₀ Ech ≥ c₀ cL V^{-q} Λ^{-q/2}`
  have g1 : c₀ * Ech ≤ c₀ * L ^ (-q) * EW := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc₀.le hLn0)
    calc c₀ * Ech = c₀ * L ^ (-q) * (L ^ q * Ech) := by
          rw [show c₀ * L ^ (-q) * (L ^ q * Ech) = c₀ * (L ^ (-q) * L ^ q) * Ech by ring, hLq]
          ring
      _ ≤ c₀ * L ^ (-q) * EW := this
  have g2 : c₀ * cL * V ^ (-q) * Λ ^ (-(q / 2)) ≤ c₀ * Ech := by
    have hT' : cL * ((2 : ℝ) ^ (-q) * Λ ^ (-(q / 2))) * (V / 2) ^ (-q)
        ≤ cL * T * (V / 2) ^ (-q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hcL.le)
        (Real.rpow_nonneg (by linarith) _)
    have heq : cL * ((2 : ℝ) ^ (-q) * Λ ^ (-(q / 2))) * (V / 2) ^ (-q)
        = cL * V ^ (-q) * Λ ^ (-(q / 2)) := by
      rw [hV2]
      calc cL * ((2 : ℝ) ^ (-q) * Λ ^ (-(q / 2))) * (V ^ (-q) * 2 ^ q)
          = cL * V ^ (-q) * Λ ^ (-(q / 2)) * ((2 : ℝ) ^ (-q) * 2 ^ q) := by ring
        _ = cL * V ^ (-q) * Λ ^ (-(q / 2)) := by rw [h2q, mul_one]
    have := mul_le_mul_of_nonneg_left (le_trans (heq ▸ hT') h3) hc₀.le
    calc c₀ * cL * V ^ (-q) * Λ ^ (-(q / 2)) = c₀ * (cL * V ^ (-q) * Λ ^ (-(q / 2))) := by
          ring
      _ ≤ c₀ * Ech := this
  -- the subtracted term: `C₀ e^{-Vq} L^{-q} EJ ≤ C₀ K' e^{-Vq} Λ^{-q/2} ≤ ½ c₀ cL V^{-q} Λ^{-q/2}`
  have hEJ : EJ ≤ L ^ q * (K' * Λ ^ (-(q / 2))) :=
    le_trans h4 (le_trans h6 (mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hL.le _)))
  have he0 : 0 ≤ Real.exp (-(V * q)) := (Real.exp_pos _).le
  have g3 : C₀ * Real.exp (-(V * q)) * L ^ (-q) * EJ
      ≤ c₀ * cL * V ^ (-q) / 2 * Λ ^ (-(q / 2)) := by
    have hstep := mul_le_mul_of_nonneg_left hEJ (mul_nonneg (mul_nonneg hC₀.le he0) hLn0)
    have heq : C₀ * Real.exp (-(V * q)) * L ^ (-q) * (L ^ q * (K' * Λ ^ (-(q / 2))))
        = C₀ * K' * Λ ^ (-(q / 2)) * Real.exp (-(V * q)) := by
      calc C₀ * Real.exp (-(V * q)) * L ^ (-q) * (L ^ q * (K' * Λ ^ (-(q / 2))))
          = C₀ * K' * Λ ^ (-(q / 2)) * Real.exp (-(V * q)) * (L ^ (-q) * L ^ q) := by ring
        _ = C₀ * K' * Λ ^ (-(q / 2)) * Real.exp (-(V * q)) := by rw [hLq, mul_one]
    have hVe' := mul_le_mul_of_nonneg_left hVe
      (mul_nonneg (mul_nonneg hC₀.le hK'.le) hΛ0)
    have heq2 : C₀ * K' * Λ ^ (-(q / 2)) * (c₀ * cL / (2 * C₀ * K') * V ^ (-q))
        = c₀ * cL * V ^ (-q) / 2 * Λ ^ (-(q / 2)) := by
      field_simp
    rw [heq] at hstep
    linarith
  linarith

/-- `E[J^q] ≤ b^q E[(a⁻¹J)^q]` for `0 < a ≤ b` and `J ≥ 0`: the normalisation pulled out. -/
lemma integral_rpow_le_rpow_mul_integral_rpow_inv_mul {μ : Measure Ω} {J : Ω → ℝ}
    {a b q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hq : 0 ≤ q) (hJ : ∀ ω, 0 ≤ J ω) :
    ∫ ω, J ω ^ q ∂μ ≤ b ^ q * ∫ ω, (a⁻¹ * J ω) ^ q ∂μ := by
  have hpt : ∀ ω, J ω ^ q = a ^ q * (a⁻¹ * J ω) ^ q := fun ω => by
    rw [Real.mul_rpow (inv_nonneg.2 ha.le) (hJ ω), Real.inv_rpow ha.le,
      mul_inv_cancel_left₀ (Real.rpow_pos_of_pos ha q).ne']
  calc ∫ ω, J ω ^ q ∂μ = ∫ ω, a ^ q * (a⁻¹ * J ω) ^ q ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = a ^ q * ∫ ω, (a⁻¹ * J ω) ^ q ∂μ := integral_const_mul _ _
    _ ≤ b ^ q * ∫ ω, (a⁻¹ * J ω) ^ q ∂μ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha.le hab hq)
          (integral_nonneg fun ω =>
            Real.rpow_nonneg (mul_nonneg (inv_nonneg.2 ha.le) (hJ ω)) _)

/-! ### The lower bound, and the order of magnitude -/

/-- **The lower bound at fixed `q < ½`**: `c (log log x)^{-q/2} ≤ E|S(x)|^{2q}` for `x ≥ x₀`,
`S(x) = ∑_{n≤x} f(n)/√n`.  `RMF.exists_le_integral_rpow_weightedRademacherSum_euler` at a constant
`V` depending on `q`: the window `|t| < 1` against Harper's
(`RMF.exists_le_integral_rpow_chaosShift_rademacher_eventually`), the subtracted term against the
small-`q` upper bound (`RMF.exists_const_integral_rpow_lineDiv_floor_le`), and `V` chosen by
`RMF.exp_neg_mul_le_mul_rpow_neg`. -/
theorem exists_le_integral_rpow_weightedRademacherSum_smallQ_fixed {q : ℝ} (hq0 : 0 < q)
    (hq2 : q < 1 / 2) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        c * Real.log (Real.log x) ^ (-(q / 2))
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨c₀, C₀, x₁, hc₀, hC₀, hred⟩ :=
    exists_le_integral_rpow_weightedRademacherSum_euler (Ω := Ω)
  obtain ⟨cL, hcL, hch⟩ := exists_le_integral_rpow_chaosShift_rademacher_eventually (Ω := Ω)
  obtain ⟨K, x₃, hK, hup⟩ := exists_const_integral_rpow_lineDiv_floor_le (Ω := Ω)
  have hα : 0 < q * (1 - 2 * q) := mul_pos hq0 (by linarith)
  set K' : ℝ := K * (1 + (q * (1 - 2 * q))⁻¹) with hK'def
  have hK' : 0 < K' := by positivity
  obtain ⟨hV2, hVe⟩ := exp_neg_mul_le_mul_rpow_neg
    (show 0 < c₀ * cL / (2 * C₀ * K') by positivity) hq0
  set V : ℝ := 2 + 2 * |Real.log (c₀ * cL / (2 * C₀ * K'))| / q with hVdef
  have hV0 : 0 < V := by linarith
  set ε : ℝ := c₀ * cL * V ^ (-q) / 4 with hεdef
  have hε : 0 < ε := by positivity
  have hLL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((hch (V / 2) (by linarith) q hq0 (by linarith)).and
      ((Filter.eventually_ge_atTop (max (max x₁ x₃) 2)).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop
            (max (3 * V + 3) ((C₀ / ε) ^ (2 / q)))).and
          (hLL.eventually_ge_atTop 1))))
  refine ⟨ε, x₀, hε, fun X μ hX x hx => ?_⟩
  obtain ⟨hchx, hxm, hLm, hΛ1⟩ := hx₀ x hx
  have hΛ1' : (1 : ℝ) ≤ Real.log (Real.log x) := hΛ1
  haveI := hX.isProbabilityMeasure
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxm
  have hx₃ : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxm
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hxm
  have hlogV : 3 * V + 3 ≤ Real.log x := le_trans (le_max_left _ _) hLm
  have hLC : (C₀ / ε) ^ (2 / q) ≤ Real.log x := le_trans (le_max_right _ _) hLm
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 < Real.log x := by linarith
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hL'0 : 0 < Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hL'L : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
  -- the reduction
  have h1 := hred X μ hX V x q hV0 hx₁ hlogV hq0 hq2.le
  -- the main term, against Harper's window
  have hσ1 : 2 * V / Real.log x ≤ 1 := by
    rw [div_le_one hL0]
    linarith
  have h2 := rpow_log_mul_integral_chaosShift_le hX hx2 (σ := 2 * V / Real.log x)
    (by positivity) hσ1 hq0.le
  have h3 := hchx X μ hX
  rw [show 4 * (V / 2) / Real.log x = 2 * V / Real.log x by ring] at h3
  have hT := two_rpow_neg_mul_le_target hΛ1' hq0.le (by linarith)
  -- the subtracted term
  have h4 := integral_rpow_lineDiv_le_of_le hX hy2 (σ₁ := 1 / Real.log x)
    (σ₂ := V / Real.log x) (by positivity) (div_le_div_of_nonneg_right (by linarith) hL0.le)
    hq0.le
  have h6 := integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
    (J := fun ω => ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
        / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
    hL'0 hL'L hq0.le (fun ω => integral_nonneg fun t => sq_nonneg _)
  have h5 := hup X μ hX x q hx₃ hq0 hq2
  have hmin : K * (min (Real.log (Real.log x)) (1 + (q * (1 - 2 * q))⁻¹)
      * Real.log (Real.log x) ^ (-(q / 2))) ≤ K' * Real.log (Real.log x) ^ (-(q / 2)) := by
    rw [hK'def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (Real.rpow_nonneg (by linarith) _)) hK.le
  have h5' := le_trans h5 hmin
  -- the error term
  have hneg := mul_rpow_neg_le_mul_log_rpow_neg hC₀ hε hq0 hL1 hLC
  exact smallQ_fixed_assembly hL0 hΛ1' hV0 hc₀ hC₀ hcL hK' h1 h2 h3 hT h4 h6 h5' hVe hneg

/-- **The order of magnitude at fixed `q < ½`**: for fixed `0 < q < ½`,
`E|S(x)|^{2q} ≍ (log log x)^{-q/2}`, `S(x) = ∑_{n≤x} f(n)/√n`, for `x ≥ x₀`: the case `0 < q < ½`
of Theorem 1.2 of the paper for the weighted sum.  The lower bound is
`RMF.exists_le_integral_rpow_weightedRademacherSum_smallQ_fixed`, the upper bound
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp` at
`min{log log x, (1-2q)^{-1}} ≤ (1-2q)^{-1}`. -/
theorem exists_integral_rpow_weightedRademacherSum_asymp_smallQ {q : ℝ} (hq0 : 0 < q)
    (hq2 : q < 1 / 2) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
        c * Real.log (Real.log x) ^ (-(q / 2))
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ
          ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ
            ≤ C * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨c, x₁, hc, hlow⟩ := exists_le_integral_rpow_weightedRademacherSum_smallQ_fixed
    (Ω := Ω) hq0 hq2
  obtain ⟨C, x₂, hC, hupp⟩ :=
    exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp (Ω := Ω)
  have h12 : 0 < 1 - 2 * q := by linarith
  refine ⟨c, C * (1 - 2 * q)⁻¹, max (max x₁ x₂) (Real.exp 1), hc, by positivity,
    fun X μ hX x hx => ⟨hlow X μ hX x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      hx), ?_⟩⟩
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hxe)).2 hxe
  refine le_trans (hupp X μ hX x q hx₂ hq0 hq2) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (min_le_right _ _)
    (Real.rpow_nonneg (Real.log_nonneg hlog1) _)) hC.le

end RMF
