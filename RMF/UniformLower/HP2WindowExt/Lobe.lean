/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.Taylor

/-!
# HP2's window integral with the rest: the damped cosine integral, uniformly in its length

For a scale `A > 0`, a frequency `τ ≥ 0` and a damping `σ ≥ 0`, the partial integrals
`I(U) = ∫_A^U cos(τu)e^{-2σu}/u du`, `U ≥ A`, bounded uniformly in `U`.

* **The lobes** (`RMF.integral_cos_mul_exp_div_nonpos_of_sin_eq_one`): past a point `V` with
  `sin(τV) = 1` the weight `e^{-2σu}/u` decreases, so `∫_V^U ≤ 0`; hence `I(U) ≤ I(π/(2τ))` for
  `τA ≤ π/2` and `I(U) ≤ max(0, I(5π/(2τ)))` for `τA ∈ [π/2, 5π/2]`.
* **Monotone in `τ` and `σ` on the first lobe** (`RMF.integral_first_lobe_le_of_le`).
* **The first lobe in numerals**: `∫_t^{π/2} cos(w)e^{-βw}/w dw` by `e^{-x} ≤ 1 - x + x²/2`
  (`RMF.integral_cos_exp_div_le_small`) or by `cos w ≤ 1 - w²/2 + w⁴/24` and the exponential
  integral (`RMF.integral_cos_exp_div_le_large`); the second lobe by the quartic around `2π`
  (`RMF.integral_cos_div_le_lobeP`) and the tent below `|cos|` on `[π/2, 3π/2]`.
* **The cells** (`RMF.IsRestCosBound lo hi B`): `I(U) ≤ B` for every normalised frequency
  `τA ∈ (lo, hi]`, damping `2σA ∈ [1/(100e), 1/100]` and `U ≥ A`; its discharges per cell type.
-/

open MeasureTheory Real

namespace RMF

/-! ### The lobes -/

/-- An interval integral of a nonpositive function is nonpositive. -/
lemma intervalIntegral_nonpos_of_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, f x ≤ 0) : ∫ x in a..b, f x ≤ 0 := by
  have h : 0 ≤ ∫ x in a..b, -f x :=
    intervalIntegral.integral_nonneg hab fun x hx => neg_nonneg.2 (hf x hx)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- **Past a crest the lobes cancel downwards**: for `τ > 0`, `σ ≥ 0`, `0 < V ≤ U` and
`sin(τV) = 1`, `∫_V^U cos(τu)e^{-2σu}/u du ≤ 0` — by parts against `(sin(τu) - 1)/τ ≤ 0` and the
decreasing weight `e^{-2σu}/u`. -/
theorem integral_cos_mul_exp_div_nonpos_of_sin_eq_one {τ σ V U : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hV : 0 < V) (hVU : V ≤ U) (hsin : Real.sin (τ * V) = 1) :
    ∫ u in V..U, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u ≤ 0 := by
  have hpos : ∀ x ∈ Set.uIcc V U, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hVU] at hx
    exact hV.trans_le hx.1
  set g : ℝ → ℝ := fun u => Real.exp (-(2 * σ) * u) / u with hgdef
  set g' : ℝ → ℝ := fun u => -(Real.exp (-(2 * σ) * u) * (2 * σ * u + 1) / u ^ 2) with hg'def
  have hgd : ∀ x ∈ Set.uIcc V U, HasDerivAt g (g' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(2 * σ) * u))
        (Real.exp (-(2 * σ) * x) * (-(2 * σ))) x := by
      have h := ((hasDerivAt_id x).const_mul (-(2 * σ))).exp
      simpa using h
    refine (h1.div (hasDerivAt_id x) hx0).congr_deriv ?_
    simp only [hg'def, id]
    field_simp
    ring
  have hg'c : ContinuousOn g' (Set.uIcc V U) := by
    refine ContinuousOn.neg (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_)
    exact pow_ne_zero 2 (hpos x hx).ne'
  have hvd : ∀ x ∈ Set.uIcc V U,
      HasDerivAt (fun u : ℝ => (Real.sin (τ * u) - 1) / τ) (Real.cos (τ * x)) x := by
    intro x _
    have h := ((((hasDerivAt_id x).const_mul τ).sin).sub_const 1).div_const τ
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hcosc : Continuous fun x : ℝ => Real.cos (τ * x) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgd hvd
    hg'c.intervalIntegrable (hcosc.intervalIntegrable V U)
  have hform : (∫ u in V..U, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      = ∫ x in V..U, g x * Real.cos (τ * x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hgdef]
    ring
  rw [hform, hparts]
  have hgU : 0 ≤ g U := by
    simp only [hgdef]
    exact div_nonneg (Real.exp_pos _).le (hV.le.trans hVU)
  have hend : g U * ((Real.sin (τ * U) - 1) / τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hgU
      (div_nonpos_of_nonpos_of_nonneg (by linarith [Real.sin_le_one (τ * U)]) hτ.le)
  have hstart : g V * ((Real.sin (τ * V) - 1) / τ) = 0 := by rw [hsin]; simp
  have hint : 0 ≤ ∫ x in V..U, g' x * ((Real.sin (τ * x) - 1) / τ) := by
    refine intervalIntegral.integral_nonneg hVU fun x hx => ?_
    have hx0 : 0 < x := hV.trans_le hx.1
    have h1 : g' x ≤ 0 := by
      simp only [hg'def]
      exact neg_nonpos.2 (by positivity)
    have h2 : (Real.sin (τ * x) - 1) / τ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [Real.sin_le_one (τ * x)]) hτ.le
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  linarith

/-- `cos(τu) ≥ 0` where `τu ∈ [0, π/2]`. -/
lemma cos_mul_nonneg_of_le {τ u : ℝ} (h0 : 0 ≤ τ * u) (h1 : τ * u ≤ π / 2) :
    0 ≤ Real.cos (τ * u) :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) h1

/-- **The first lobe bounds every partial integral**: for `τ > 0`, `σ ≥ 0`, `A > 0` with
`τA ≤ π/2` and `U ≥ A`, `∫_A^U cos(τu)e^{-2σu}/u du ≤ ∫_A^{π/(2τ)} cos(τu)e^{-2σu}/u du`. -/
theorem integral_cos_mul_exp_div_le_first_lobe {τ σ A U : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hA : 0 < A) (hAτ : τ * A ≤ π / 2) (hAU : A ≤ U) :
    ∫ u in A..U, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      ≤ ∫ u in A..π / 2 / τ, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u := by
  have hV : A ≤ π / 2 / τ := by rw [le_div_iff₀ hτ]; linarith
  have hτV : τ * (π / 2 / τ) = π / 2 := by field_simp
  rcases le_total U (π / 2 / τ) with h | h
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) hA hAU)
      (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (hA.trans_le hAU) h)
    have hnn : 0 ≤ ∫ u in U..π / 2 / τ, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u := by
      refine intervalIntegral.integral_nonneg h fun u hu => ?_
      have hu0 : 0 < u := (hA.trans_le hAU).trans_le hu.1
      have hc : 0 ≤ Real.cos (τ * u) := cos_mul_nonneg_of_le (by positivity) (by
        have := mul_le_mul_of_nonneg_left hu.2 hτ.le
        linarith)
      positivity
    linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) hA hV)
      (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (hA.trans_le hV) h)
    have hneg := integral_cos_mul_exp_div_nonpos_of_sin_eq_one (σ := σ) hτ hσ
      (hA.trans_le hV) h (by rw [hτV, Real.sin_pi_div_two])
    linarith

/-- **The first lobe is monotone in the frequency and the damping**: for `0 < τ₀ ≤ τ`,
`σ₀ ≤ σ`, `A > 0` and `τA ≤ π/2`,
`∫_A^{π/(2τ)} cos(τu)e^{-2σu}/u du ≤ ∫_A^{π/(2τ₀)} cos(τ₀u)e^{-2σ₀u}/u du` — on the first lobe
`cos(τu) ≤ cos(τ₀u)`, and the longer lobe adds a nonnegative piece. -/
theorem integral_first_lobe_le_of_le {τ τ₀ σ σ₀ A : ℝ} (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ)
    (hσ : σ₀ ≤ σ) (hA : 0 < A) (hAτ : τ * A ≤ π / 2) :
    ∫ u in A..π / 2 / τ, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      ≤ ∫ u in A..π / 2 / τ₀, Real.cos (τ₀ * u) * Real.exp (-(2 * σ₀) * u) / u := by
  have hτ0 : 0 < τ := hτ₀.trans_le hτ
  have hV : A ≤ π / 2 / τ := by rw [le_div_iff₀ hτ0]; linarith
  have hVV : π / 2 / τ ≤ π / 2 / τ₀ :=
    div_le_div_of_nonneg_left (by positivity) hτ₀ hτ
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_cos_mul_exp_div (τ := τ₀) (σ := σ₀) hA hV)
    (intervalIntegrable_cos_mul_exp_div (τ := τ₀) (σ := σ₀) (hA.trans_le hV) hVV)
  have hpt : ∫ u in A..π / 2 / τ, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      ≤ ∫ u in A..π / 2 / τ, Real.cos (τ₀ * u) * Real.exp (-(2 * σ₀) * u) / u := by
    refine intervalIntegral.integral_mono_on hV (intervalIntegrable_cos_mul_exp_div hA hV)
      (intervalIntegrable_cos_mul_exp_div hA hV) fun u hu => ?_
    have hu0 : 0 < u := hA.trans_le hu.1
    have hτu : τ * u ≤ π / 2 := by
      have := mul_le_mul_of_nonneg_left hu.2 hτ0.le
      rwa [mul_div_cancel₀ _ hτ0.ne'] at this
    have hτ₀u : τ₀ * u ≤ τ * u := mul_le_mul_of_nonneg_right hτ hu0.le
    have hc : Real.cos (τ * u) ≤ Real.cos (τ₀ * u) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) hτ₀u
    have hc0 : 0 ≤ Real.cos (τ * u) := cos_mul_nonneg_of_le (by positivity) hτu
    have he : Real.exp (-(2 * σ) * u) ≤ Real.exp (-(2 * σ₀) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h1 : Real.cos (τ * u) * Real.exp (-(2 * σ) * u)
        ≤ Real.cos (τ₀ * u) * Real.exp (-(2 * σ₀) * u) :=
      mul_le_mul hc he (Real.exp_pos _).le (hc0.trans hc)
    exact div_le_div_of_nonneg_right h1 hu0.le
  have hnn : 0 ≤ ∫ u in π / 2 / τ..π / 2 / τ₀,
      Real.cos (τ₀ * u) * Real.exp (-(2 * σ₀) * u) / u := by
    refine intervalIntegral.integral_nonneg hVV fun u hu => ?_
    have hu0 : 0 < u := (hA.trans_le hV).trans_le hu.1
    have hc : 0 ≤ Real.cos (τ₀ * u) := cos_mul_nonneg_of_le (by positivity) (by
      have := mul_le_mul_of_nonneg_left hu.2 hτ₀.le
      rwa [mul_div_cancel₀ _ hτ₀.ne'] at this)
    positivity
  linarith

/-- **The second lobe bounds every partial integral**: for `τ > 0`, `σ ≥ 0`, `A > 0` with
`τA ∈ [π/2, 5π/2]` and `U ≥ A`,
`∫_A^U cos(τu)e^{-2σu}/u du ≤ max(0, ∫_A^{5π/(2τ)} cos(τu)e^{-2σu}/u du)`. -/
theorem integral_cos_mul_exp_div_le_second_lobe {τ σ A U : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hA : 0 < A) (hAτ₁ : π / 2 ≤ τ * A) (hAτ₂ : τ * A ≤ 5 * π / 2) (hAU : A ≤ U) :
    ∫ u in A..U, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      ≤ max 0 (∫ u in A..5 * π / 2 / τ, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) := by
  have hV₂ : A ≤ 5 * π / 2 / τ := by rw [le_div_iff₀ hτ]; linarith
  have hτV₂ : τ * (5 * π / 2 / τ) = π / 2 + 2 * π := by field_simp; ring
  have hU0 : 0 < U := hA.trans_le hAU
  rcases le_total (5 * π / 2 / τ) U with h | h
  · -- past the lobe's crest
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) hA hV₂)
      (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (hA.trans_le hV₂) h)
    have hneg := integral_cos_mul_exp_div_nonpos_of_sin_eq_one (σ := σ) hτ hσ
      (hA.trans_le hV₂) h (by rw [hτV₂, Real.sin_add_two_pi, Real.sin_pi_div_two])
    exact le_max_of_le_right (by linarith)
  · rcases le_total (τ * U) (3 * π / 2) with h' | h'
    · -- the negative half-lobe only
      refine le_max_of_le_left (intervalIntegral_nonpos_of_le hAU fun u hu => ?_)
      have hu0 : 0 < u := hA.trans_le hu.1
      have h1 : π / 2 ≤ τ * u := hAτ₁.trans (mul_le_mul_of_nonneg_left hu.1 hτ.le)
      have h2 : τ * u ≤ π + π / 2 := by
        have := mul_le_mul_of_nonneg_left hu.2 hτ.le
        linarith
      have hc := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc (Real.exp_pos _).le) hu0.le
    · -- the rest of the positive half-lobe is nonnegative
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) hA hAU)
        (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) hU0 h)
      have hnn : 0 ≤ ∫ u in U..5 * π / 2 / τ,
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u := by
        refine intervalIntegral.integral_nonneg h fun u hu => ?_
        have hu0 : 0 < u := hU0.trans_le hu.1
        have h1 : 3 * π / 2 ≤ τ * u := h'.trans (mul_le_mul_of_nonneg_left hu.1 hτ.le)
        have h2 : τ * u ≤ 5 * π / 2 := by
          have := mul_le_mul_of_nonneg_left hu.2 hτ.le
          rwa [mul_div_cancel₀ _ hτ.ne'] at this
        have hc : 0 ≤ Real.cos (τ * u) := by
          rw [← Real.cos_sub_two_pi]
          exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
        positivity
      exact le_max_of_le_right (by linarith)

/-- **The frequency scaled out**: for `τ > 0`,
`∫_A^B cos(τu)e^{-2σu}/u du = ∫_{τA}^{τB} cos(w)e^{-(2σ/τ)w}/w dw`. -/
lemma integral_cos_mul_exp_div_eq_comp {τ σ A B : ℝ} (hτ : 0 < τ) :
    ∫ u in A..B, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      = ∫ w in τ * A..τ * B, Real.cos w * Real.exp (-(2 * σ / τ) * w) / w := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun w => Real.cos w * Real.exp (-(2 * σ / τ) * w) / w) (a := A) (b := B) hτ.ne'
  have e : ∀ u : ℝ, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      = τ * (Real.cos (τ * u) * Real.exp (-(2 * σ / τ) * (τ * u)) / (τ * u)) := by
    intro u
    have hx : -(2 * σ / τ) * (τ * u) = -(2 * σ) * u := by field_simp
    rw [hx]
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu]
    · field_simp
  rw [intervalIntegral.integral_congr fun u _ => e u, intervalIntegral.integral_const_mul, h,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]

/-- **The damping scaled out**: for `c > 0`, `∫_a^b e^{-cu}/u du = ∫_{ca}^{cb} e^{-s}/s ds`. -/
lemma integral_exp_mul_div_eq_comp {c a b : ℝ} (hc : 0 < c) :
    ∫ u in a..b, Real.exp (-c * u) / u = ∫ s in c * a..c * b, Real.exp (-s) / s := by
  have h := intervalIntegral.integral_comp_mul_left (fun s => Real.exp (-s) / s)
    (a := a) (b := b) hc.ne'
  have e : ∀ u : ℝ, Real.exp (-c * u) / u = c * (Real.exp (-(c * u)) / (c * u)) := by
    intro u
    rw [neg_mul]
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu]
    · field_simp
  rw [intervalIntegral.integral_congr fun u _ => e u, intervalIntegral.integral_const_mul, h,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-! ### The first lobe in numerals -/

/-- **The first lobe with a small damping**: for `0 < t ≤ π/2` and `β ≥ 0`,
`∫_t^{π/2} cos(w)e^{-βw}/w dw ≤ log(π/2) - log t - ((π/2)² - t²)/4 + ((π/2)⁴ - t⁴)/96
  - β(1 - sin t) + β²/2·(π/2 - t sin t - cos t)`
(`e^{-x} ≤ 1 - x + x²/2` and `cos w ≤ 1 - w²/2 + w⁴/24`). -/
theorem integral_cos_exp_div_le_small {t β : ℝ} (ht : 0 < t) (htb : t ≤ π / 2) (hβ : 0 ≤ β) :
    ∫ w in t..π / 2, Real.cos w * Real.exp (-β * w) / w
      ≤ Real.log (π / 2) - Real.log t - ((π / 2) ^ 2 - t ^ 2) / 4 + ((π / 2) ^ 4 - t ^ 4) / 96
        - β * (1 - Real.sin t) + β ^ 2 / 2 * (π / 2 - t * Real.sin t - Real.cos t) := by
  have hpos : ∀ w ∈ Set.uIcc t (π / 2), 0 < w := fun w hw => by
    rw [Set.uIcc_of_le htb] at hw
    exact ht.trans_le hw.1
  set F : ℝ → ℝ := fun w => Real.log w - w ^ 2 / 4 + w ^ 4 / 96 - β * Real.sin w
    + β ^ 2 / 2 * (w * Real.sin w + Real.cos w) with hF
  set f : ℝ → ℝ := fun w => w⁻¹ - w / 2 + w ^ 3 / 24 - β * Real.cos w
    + β ^ 2 / 2 * (w * Real.cos w) with hf
  have hd : ∀ w ∈ Set.uIcc t (π / 2), HasDerivAt F (f w) w := by
    intro w hw
    have h1 := Real.hasDerivAt_log (hpos w hw).ne'
    have h2 := (hasDerivAt_pow 2 w).div_const 4
    have h3 := (hasDerivAt_pow 4 w).div_const 96
    have h4 := (Real.hasDerivAt_sin w).const_mul β
    have h5 := (((hasDerivAt_id w).mul (Real.hasDerivAt_sin w)).add
      (Real.hasDerivAt_cos w)).const_mul (β ^ 2 / 2)
    refine ((((h1.sub h2).add h3).sub h4).add h5).congr_deriv ?_
    simp only [hf, id]
    push_cast
    ring
  have hfc : ContinuousOn f (Set.uIcc t (π / 2)) := by
    refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.add (ContinuousOn.sub
      (continuousOn_inv₀.mono fun w hw => (hpos w hw).ne') (by fun_prop)) (by fun_prop))
      (by fun_prop)) (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hfc.intervalIntegrable
  have hle : ∫ w in t..π / 2, Real.cos w * Real.exp (-β * w) / w ≤ ∫ w in t..π / 2, f w := by
    refine intervalIntegral.integral_mono_on htb ?_ hfc.intervalIntegrable fun w hw => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      exact ContinuousOn.div (by fun_prop) continuousOn_id fun w hw => (hpos w hw).ne'
    have hw0 : 0 < w := ht.trans_le hw.1
    have hc0 : 0 ≤ Real.cos w := cos_mul_nonneg_of_le (τ := 1) (by linarith) (by linarith [hw.2])
      |>.trans_eq (by rw [one_mul])
    have he : Real.exp (-β * w) ≤ 1 - β * w + (β * w) ^ 2 / 2 := by
      rw [neg_mul]
      exact exp_neg_le_quad (by positivity)
    have h1 : Real.cos w * Real.exp (-β * w) ≤ Real.cos w * (1 - β * w + (β * w) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left he hc0
    have h2 := cos_le_quartic w
    have key : Real.cos w * Real.exp (-β * w) ≤ f w * w := by
      have e : f w * w = 1 - w ^ 2 / 2 + w ^ 4 / 24 - β * w * Real.cos w
          + β ^ 2 / 2 * w ^ 2 * Real.cos w := by
        simp only [hf]
        field_simp
      have e2 : Real.cos w * (1 - β * w + (β * w) ^ 2 / 2)
          = Real.cos w - β * w * Real.cos w + β ^ 2 / 2 * w ^ 2 * Real.cos w := by ring
      rw [e]
      linarith
    rw [div_le_iff₀ hw0]
    exact key
  rw [hFTC] at hle
  refine hle.trans (le_of_eq ?_)
  simp only [hF]
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- `∫_a^b w e^{-βw} dw = J₁(a) - J₁(b)`, `J₁(w) = e^{-βw}(w/β + 1/β²)`, for `β > 0`. -/
lemma integral_mul_exp_neg_eq {β a b : ℝ} (hβ : 0 < β) :
    ∫ w in a..b, w * Real.exp (-β * w)
      = Real.exp (-β * a) * (a / β + 1 / β ^ 2) - Real.exp (-β * b) * (b / β + 1 / β ^ 2) := by
  have hd : ∀ w ∈ Set.uIcc a b, HasDerivAt
      (fun w => -(Real.exp (-β * w) * (w / β + 1 / β ^ 2))) (w * Real.exp (-β * w)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => Real.exp (-β * w)) (Real.exp (-β * w) * (-β)) w := by
      have h := ((hasDerivAt_id w).const_mul (-β)).exp
      simpa using h
    have h2 : HasDerivAt (fun w : ℝ => w / β + 1 / β ^ 2) (1 / β) w := by
      have h := ((hasDerivAt_id w).div_const β).add_const (1 / β ^ 2)
      simpa using h
    refine (h1.mul h2).neg.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous
    fun w : ℝ => w * Real.exp (-β * w)).intervalIntegrable a b)]
  ring

/-- `∫_a^b w³e^{-βw} dw = J₃(a) - J₃(b)`, `J₃(w) = e^{-βw}(w³/β + 3w²/β² + 6w/β³ + 6/β⁴)`, for
`β > 0`. -/
lemma integral_pow_three_mul_exp_neg_eq {β a b : ℝ} (hβ : 0 < β) :
    ∫ w in a..b, w ^ 3 * Real.exp (-β * w)
      = Real.exp (-β * a) * (a ^ 3 / β + 3 * a ^ 2 / β ^ 2 + 6 * a / β ^ 3 + 6 / β ^ 4)
        - Real.exp (-β * b) * (b ^ 3 / β + 3 * b ^ 2 / β ^ 2 + 6 * b / β ^ 3 + 6 / β ^ 4) := by
  have hd : ∀ w ∈ Set.uIcc a b, HasDerivAt
      (fun w => -(Real.exp (-β * w) * (w ^ 3 / β + 3 * w ^ 2 / β ^ 2 + 6 * w / β ^ 3 + 6 / β ^ 4)))
      (w ^ 3 * Real.exp (-β * w)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => Real.exp (-β * w)) (Real.exp (-β * w) * (-β)) w := by
      have h := ((hasDerivAt_id w).const_mul (-β)).exp
      simpa using h
    have h2 : HasDerivAt (fun w : ℝ => w ^ 3 / β + 3 * w ^ 2 / β ^ 2 + 6 * w / β ^ 3 + 6 / β ^ 4)
        (3 * w ^ 2 / β + 6 * w / β ^ 2 + 6 / β ^ 3) w := by
      have h := ((((hasDerivAt_pow 3 w).div_const β).add
        (((hasDerivAt_pow 2 w).const_mul 3).div_const (β ^ 2))).add
        (((hasDerivAt_id w).const_mul 6).div_const (β ^ 3))).add_const (6 / β ^ 4)
      refine h.congr_deriv ?_
      push_cast
      ring
    refine (h1.mul h2).neg.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous
    fun w : ℝ => w ^ 3 * Real.exp (-β * w)).intervalIntegrable a b)]
  ring

/-- **The first lobe with any damping**: for `0 < t ≤ π/2` and `β > 0`,
`∫_t^{π/2} cos(w)e^{-βw}/w dw ≤ ∫_{βt}^{βπ/2} e^{-s}/s ds - (J₁(t) - J₁(π/2))/2
  + (J₃(t) - J₃(π/2))/24` (`cos w ≤ 1 - w²/2 + w⁴/24`). -/
theorem integral_cos_exp_div_le_large {t β : ℝ} (ht : 0 < t) (htb : t ≤ π / 2) (hβ : 0 < β) :
    ∫ w in t..π / 2, Real.cos w * Real.exp (-β * w) / w
      ≤ (∫ s in β * t..β * (π / 2), Real.exp (-s) / s)
        - (Real.exp (-β * t) * (t / β + 1 / β ^ 2)
          - Real.exp (-β * (π / 2)) * (π / 2 / β + 1 / β ^ 2)) / 2
        + (Real.exp (-β * t) * (t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
          - Real.exp (-β * (π / 2)) * ((π / 2) ^ 3 / β + 3 * (π / 2) ^ 2 / β ^ 2
            + 6 * (π / 2) / β ^ 3 + 6 / β ^ 4)) / 24 := by
  have hpos : ∀ w ∈ Set.uIcc t (π / 2), 0 < w := fun w hw => by
    rw [Set.uIcc_of_le htb] at hw
    exact ht.trans_le hw.1
  have hi0 : IntervalIntegrable (fun w => Real.exp (-β * w) / w) volume t (π / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.div (by fun_prop) continuousOn_id fun w hw => (hpos w hw).ne'
  have hi1 : IntervalIntegrable (fun w => w * Real.exp (-β * w)) volume t (π / 2) :=
    (by fun_prop : Continuous fun w : ℝ => w * Real.exp (-β * w)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun w => w ^ 3 * Real.exp (-β * w)) volume t (π / 2) :=
    (by fun_prop : Continuous fun w : ℝ => w ^ 3 * Real.exp (-β * w)).intervalIntegrable _ _
  have hle : ∫ w in t..π / 2, Real.cos w * Real.exp (-β * w) / w
      ≤ ∫ w in t..π / 2, (Real.exp (-β * w) / w - w * Real.exp (-β * w) / 2
        + w ^ 3 * Real.exp (-β * w) / 24) := by
    refine intervalIntegral.integral_mono_on htb ?_ ((hi0.sub (hi1.div_const 2)).add
      (hi3.div_const 24)) fun w hw => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      exact ContinuousOn.div (by fun_prop) continuousOn_id fun w hw => (hpos w hw).ne'
    have hw0 : 0 < w := ht.trans_le hw.1
    have he := Real.exp_pos (-β * w)
    have h2 := mul_le_mul_of_nonneg_right (cos_le_quartic w) he.le
    have e : Real.exp (-β * w) / w - w * Real.exp (-β * w) / 2 + w ^ 3 * Real.exp (-β * w) / 24
        = (1 - w ^ 2 / 2 + w ^ 4 / 24) * Real.exp (-β * w) / w := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h2 hw0.le
  rw [intervalIntegral.integral_add (hi0.sub (hi1.div_const 2)) (hi3.div_const 24),
    intervalIntegral.integral_sub hi0 (hi1.div_const 2), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_mul_exp_neg_eq hβ,
    integral_pow_three_mul_exp_neg_eq hβ] at hle
  have hsub : ∫ w in t..π / 2, Real.exp (-β * w) / w
      = ∫ s in β * t..β * (π / 2), Real.exp (-s) / s := integral_exp_mul_div_eq_comp hβ
  rw [hsub] at hle
  exact hle

/-! ### The second lobe in numerals -/

/-- **The antiderivative of the quartic around `2π` over `w`**: `lobeP' w = q(w - 2π)/w`,
`q(x) = 1 - x²/2 + x⁴/24`. -/
noncomputable def lobeP (w : ℝ) : ℝ :=
  (1 - (2 * π) ^ 2 / 2 + (2 * π) ^ 4 / 24) * Real.log w + (2 * π - (2 * π) ^ 3 / 6) * w
    + ((2 * π) ^ 2 / 4 - 1 / 2) * w ^ 2 / 2 - 2 * π / 6 * w ^ 3 / 3 + w ^ 4 / 96

/-- **`∫cos(w)/w` by the quartic around `2π`**: for `0 < a ≤ b`,
`∫_a^b cos(w)/w dw ≤ lobeP b - lobeP a` (`cos w = cos(w - 2π) ≤ q(w - 2π)`). -/
theorem integral_cos_div_le_lobeP {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ w in a..b, Real.cos w / w ≤ lobeP b - lobeP a := by
  have hpos : ∀ w ∈ Set.uIcc a b, 0 < w := fun w hw => by
    rw [Set.uIcc_of_le hab] at hw
    exact ha.trans_le hw.1
  set f : ℝ → ℝ := fun w => (1 - (2 * π) ^ 2 / 2 + (2 * π) ^ 4 / 24) * w⁻¹
    + (2 * π - (2 * π) ^ 3 / 6) + ((2 * π) ^ 2 / 4 - 1 / 2) * w - 2 * π / 6 * w ^ 2
    + w ^ 3 / 24 with hf
  have hd : ∀ w ∈ Set.uIcc a b, HasDerivAt lobeP (f w) w := by
    intro w hw
    have h1 := (Real.hasDerivAt_log (hpos w hw).ne').const_mul
      (1 - (2 * π) ^ 2 / 2 + (2 * π) ^ 4 / 24)
    have h2 := (hasDerivAt_id w).const_mul (2 * π - (2 * π) ^ 3 / 6)
    have h3 := ((hasDerivAt_pow 2 w).const_mul ((2 * π) ^ 2 / 4 - 1 / 2)).div_const 2
    have h4 := ((hasDerivAt_pow 3 w).const_mul (2 * π / 6)).div_const 3
    have h5 := (hasDerivAt_pow 4 w).div_const 96
    have h := (((h1.add h2).add h3).sub h4).add h5
    have e : lobeP = fun w => (1 - (2 * π) ^ 2 / 2 + (2 * π) ^ 4 / 24) * Real.log w
        + (2 * π - (2 * π) ^ 3 / 6) * id w + ((2 * π) ^ 2 / 4 - 1 / 2) * w ^ 2 / 2
        - 2 * π / 6 * w ^ 3 / 3 + w ^ 4 / 96 := by
      funext w
      rfl
    rw [e]
    refine h.congr_deriv ?_
    simp only [hf]
    push_cast
    ring
  have hfc : ContinuousOn f (Set.uIcc a b) := by
    refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.add (ContinuousOn.add
      (ContinuousOn.mul continuousOn_const (continuousOn_inv₀.mono fun w hw => (hpos w hw).ne'))
      continuousOn_const) (by fun_prop)) (by fun_prop)) (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hfc.intervalIntegrable
  rw [← hFTC]
  refine intervalIntegral.integral_mono_on hab ?_ hfc.intervalIntegrable fun w hw => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.div (by fun_prop) continuousOn_id fun w hw => (hpos w hw).ne'
  have hw0 : 0 < w := ha.trans_le hw.1
  have hq := cos_le_quartic (w - 2 * π)
  rw [Real.cos_sub_two_pi] at hq
  rw [div_le_iff₀ hw0]
  have e : f w * w = 1 - (w - 2 * π) ^ 2 / 2 + (w - 2 * π) ^ 4 / 24 := by
    simp only [hf]
    field_simp
    ring
  rw [e]
  exact hq

/-- **The negative half-lobe from below `π`, by the tent**: for `π/2 ≤ a ≤ π`,
`∫_a^{3π/2} cos(w)/w dw ≤ log π - log a + 2a/π - 1 - 3 log(3/2)` (`|cos w| ≥ 1 - 2|w - π|/π`). -/
theorem integral_cos_div_le_tent_low {a : ℝ} (ha₁ : π / 2 ≤ a) (ha₂ : a ≤ π) :
    ∫ w in a..3 * π / 2, Real.cos w / w
      ≤ Real.log π - Real.log a + 2 * a / π - 1 - 3 * Real.log (3 / 2) := by
  have hπ := Real.pi_pos
  have ha0 : 0 < a := by linarith
  have hi : ∀ c d : ℝ, 0 < c → c ≤ d → IntervalIntegrable (fun w => Real.cos w / w) volume c d :=
    fun c d hc hcd => ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop)
      continuousOn_id fun w hw => by
        rw [Set.uIcc_of_le hcd] at hw
        exact (hc.trans_le hw.1).ne')
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi a π ha0 ha₂)
    (hi π (3 * π / 2) hπ (by linarith))
  -- on `[a, π]`: `cos w ≤ 1 - 2w/π`
  have h1 : ∫ w in a..π, Real.cos w / w ≤ Real.log π - Real.log a - 2 + 2 * a / π := by
    have hd : ∀ w ∈ Set.uIcc a π, HasDerivAt (fun w => Real.log w - 2 * w / π)
        (w⁻¹ - 2 / π) w := by
      intro w hw
      rw [Set.uIcc_of_le ha₂] at hw
      refine ((Real.hasDerivAt_log (ha0.trans_le hw.1).ne').sub
        (((hasDerivAt_id w).const_mul 2).div_const π)).congr_deriv ?_
      ring
    have hc : ContinuousOn (fun w : ℝ => w⁻¹ - 2 / π) (Set.uIcc a π) :=
      (continuousOn_inv₀.mono fun w hw => by
        rw [Set.uIcc_of_le ha₂] at hw
        exact (ha0.trans_le hw.1).ne').sub continuousOn_const
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
    have hle : ∫ w in a..π, Real.cos w / w ≤ ∫ w in a..π, (w⁻¹ - 2 / π) := by
      refine intervalIntegral.integral_mono_on ha₂ (hi a π ha0 ha₂) hc.intervalIntegrable
        fun w hw => ?_
      have hw0 : 0 < w := ha0.trans_le hw.1
      have ht := Real.one_sub_mul_le_cos (x := π - w) (by linarith [hw.2]) (by linarith [hw.1])
      rw [Real.cos_pi_sub] at ht
      rw [div_le_iff₀ hw0]
      have e : (w⁻¹ - 2 / π) * w = 1 - 2 * w / π := by field_simp
      rw [e]
      have e2 : 1 - 2 / π * (π - w) = -1 + 2 * w / π := by field_simp; ring
      linarith
    rw [hF] at hle
    have e5 : 2 * π / π = 2 := by field_simp
    rw [e5] at hle
    linarith
  -- on `[π, 3π/2]`: `cos w ≤ -3 + 2w/π`
  have h2 : ∫ w in π..3 * π / 2, Real.cos w / w ≤ -3 * Real.log (3 / 2) + 1 := by
    have hd : ∀ w ∈ Set.uIcc π (3 * π / 2), HasDerivAt (fun w => -3 * Real.log w + 2 * w / π)
        (-3 * w⁻¹ + 2 / π) w := by
      intro w hw
      rw [Set.uIcc_of_le (by linarith)] at hw
      refine (((Real.hasDerivAt_log (hπ.trans_le hw.1).ne').const_mul (-3)).add
        (((hasDerivAt_id w).const_mul 2).div_const π)).congr_deriv ?_
      ring
    have hc : ContinuousOn (fun w : ℝ => -3 * w⁻¹ + 2 / π) (Set.uIcc π (3 * π / 2)) :=
      (continuousOn_const.mul (continuousOn_inv₀.mono fun w hw => by
        rw [Set.uIcc_of_le (by linarith)] at hw
        exact (hπ.trans_le hw.1).ne')).add continuousOn_const
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
    have hle : ∫ w in π..3 * π / 2, Real.cos w / w ≤ ∫ w in π..3 * π / 2, (-3 * w⁻¹ + 2 / π) := by
      refine intervalIntegral.integral_mono_on (by linarith) (hi π (3 * π / 2) hπ (by linarith))
        hc.intervalIntegrable fun w hw => ?_
      have hw0 : 0 < w := hπ.trans_le hw.1
      have ht := Real.one_sub_mul_le_cos (x := w - π) (by linarith [hw.1]) (by linarith [hw.2])
      rw [Real.cos_sub_pi] at ht
      rw [div_le_iff₀ hw0]
      have e : (-3 * w⁻¹ + 2 / π) * w = -3 + 2 * w / π := by field_simp
      rw [e]
      have e2 : 1 - 2 / π * (w - π) = 3 - 2 * w / π := by field_simp; ring
      linarith
    rw [hF] at hle
    have hl : Real.log (3 * π / 2) = Real.log (3 / 2) + Real.log π := by
      rw [← Real.log_mul (by norm_num) hπ.ne']
      ring_nf
    have e3 : 2 * (3 * π / 2) / π = 3 := by field_simp
    have e4 : 2 * π / π = 2 := by field_simp
    rw [hl, e3, e4] at hle
    linarith
  linarith

/-- **The negative half-lobe from above `π`, by the tent**: for `π ≤ a ≤ 3π/2`,
`∫_a^{3π/2} cos(w)/w dw ≤ -3(log(3π/2) - log a) + 3 - 2a/π`. -/
theorem integral_cos_div_le_tent_high {a : ℝ} (ha₁ : π ≤ a) (ha₂ : a ≤ 3 * π / 2) :
    ∫ w in a..3 * π / 2, Real.cos w / w
      ≤ -3 * (Real.log (3 * π / 2) - Real.log a) + 3 - 2 * a / π := by
  have hπ := Real.pi_pos
  have ha0 : 0 < a := hπ.trans_le ha₁
  have hd : ∀ w ∈ Set.uIcc a (3 * π / 2), HasDerivAt (fun w => -3 * Real.log w + 2 * w / π)
      (-3 * w⁻¹ + 2 / π) w := by
    intro w hw
    rw [Set.uIcc_of_le ha₂] at hw
    refine (((Real.hasDerivAt_log (ha0.trans_le hw.1).ne').const_mul (-3)).add
      (((hasDerivAt_id w).const_mul 2).div_const π)).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun w : ℝ => -3 * w⁻¹ + 2 / π) (Set.uIcc a (3 * π / 2)) :=
    (continuousOn_const.mul (continuousOn_inv₀.mono fun w hw => by
      rw [Set.uIcc_of_le ha₂] at hw
      exact (ha0.trans_le hw.1).ne')).add continuousOn_const
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have hle : ∫ w in a..3 * π / 2, Real.cos w / w ≤ ∫ w in a..3 * π / 2, (-3 * w⁻¹ + 2 / π) := by
    refine intervalIntegral.integral_mono_on ha₂ ?_ hc.intervalIntegrable fun w hw => ?_
    · exact ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) continuousOn_id
        fun w hw => by
          rw [Set.uIcc_of_le ha₂] at hw
          exact (ha0.trans_le hw.1).ne')
    have hw0 : 0 < w := ha0.trans_le hw.1
    have ht := Real.one_sub_mul_le_cos (x := w - π) (by linarith [hw.1]) (by linarith [hw.2])
    rw [Real.cos_sub_pi] at ht
    rw [div_le_iff₀ hw0]
    have e : (-3 * w⁻¹ + 2 / π) * w = -3 + 2 * w / π := by field_simp
    rw [e]
    have e2 : 1 - 2 / π * (w - π) = 3 - 2 * w / π := by field_simp; ring
    linarith
  rw [hF] at hle
  have e3 : 2 * (3 * π / 2) / π = 3 := by field_simp
  rw [e3] at hle
  linarith

/-! ### The cells -/

/-- **A bound on the rest's damped cosine integral over a range of normalised frequencies**: for
every scale `A > 0`, frequency `τ ≥ 0` with `τA ∈ (lo, hi]`, damping `σ` with
`2σA ∈ [1/(100e), 1/100]` and length `U ≥ A`, `∫_A^U cos(τu)e^{-2σu}/u du ≤ B`. -/
def IsRestCosBound (lo hi B : ℝ) : Prop :=
  ∀ ⦃A τ σ U : ℝ⦄, 0 < A → 0 ≤ τ → lo < τ * A → τ * A ≤ hi →
    1 / (100 * Real.exp 1) ≤ 2 * σ * A → 2 * σ * A ≤ 1 / 100 → A ≤ U →
      ∫ u in A..U, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u ≤ B

lemma IsRestCosBound.mono {lo hi B B' : ℝ} (h : IsRestCosBound lo hi B) (hB : B ≤ B') :
    IsRestCosBound lo hi B' := fun _ _ _ _ hA hτ h₁ h₂ hσ₁ hσ₂ hU =>
  (h hA hτ h₁ h₂ hσ₁ hσ₂ hU).trans hB

/-- Two adjacent ranges with a common bound give the joint range. -/
lemma IsRestCosBound.split {lo m hi B : ℝ} (h₁ : IsRestCosBound lo m B)
    (h₂ : IsRestCosBound m hi B) : IsRestCosBound lo hi B := by
  intro A τ σ U hA hτ hlo hhi hσ₁ hσ₂ hU
  rcases le_or_gt (τ * A) m with h | h
  · exact h₁ hA hτ hlo h hσ₁ hσ₂ hU
  · exact h₂ hA hτ h hhi hσ₁ hσ₂ hU

/-- The damping's lower end gives `σ > 0`. -/
lemma sigma_pos_of_damping {σ A : ℝ} (hA : 0 < A) (h : 1 / (100 * Real.exp 1) ≤ 2 * σ * A) :
    0 < σ := by
  have h0 : 0 < 1 / (100 * Real.exp 1) := by positivity
  by_contra hσ
  have hσ' : σ ≤ 0 := not_lt.1 hσ
  nlinarith

/-- **The saturated cell**: `∫_A^U cos(τu)e^{-2σu}/u du` is at most the exponential integral from
`1/(100e)` for every frequency: `cos ≤ 1` and the damping's lower end. -/
theorem isRestCosBound_sat (lo hi : ℝ) :
    IsRestCosBound lo hi (Real.log 4 - Real.log (1 / (100 * Real.exp 1))
      + einPoly (2 * 9) 4 - einPoly (2 * 9) (1 / (100 * Real.exp 1))
      + Real.exp (-4) * (Real.log (4 + 1) - Real.log 4)) := by
  intro A τ σ U hA _ _ _ hσ₁ _ hU
  set c : ℝ := 1 / (100 * Real.exp 1) / A with hc
  have hc0 : 0 < c := by positivity
  have hcσ : c ≤ 2 * σ := by rw [hc, div_le_iff₀ hA]; linarith
  have hσ0 : 0 ≤ σ := (sigma_pos_of_damping hA hσ₁).le
  have hle : ∫ u in A..U, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u
      ≤ ∫ u in A..U, Real.exp (-c * u) / u := by
    refine intervalIntegral.integral_mono_on hU (intervalIntegrable_cos_mul_exp_div hA hU) ?_
      fun u hu => ?_
    · exact ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) continuousOn_id
        fun w hw => by
          rw [Set.uIcc_of_le hU] at hw
          exact (hA.trans_le hw.1).ne')
    have hu0 : 0 < u := hA.trans_le hu.1
    have he : Real.exp (-(2 * σ) * u) ≤ Real.exp (-c * u) := Real.exp_le_exp.2 (by nlinarith)
    have h1 : Real.cos (τ * u) * Real.exp (-(2 * σ) * u) ≤ Real.exp (-c * u) :=
      (mul_le_of_le_one_left (Real.exp_pos _).le (Real.cos_le_one _)).trans he
    exact div_le_div_of_nonneg_right h1 hu0.le
  rw [integral_exp_mul_div_eq_comp hc0] at hle
  have hcA : c * A = 1 / (100 * Real.exp 1) := by rw [hc]; field_simp
  rw [hcA] at hle
  have hx₁ : (0 : ℝ) < 1 / (100 * Real.exp 1) := by positivity
  have hxc : 1 / (100 * Real.exp 1) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hx : 1 / (100 * Real.exp 1) ≤ c * U := by
    rw [← hcA]
    exact mul_le_mul_of_nonneg_left hU hc0.le
  exact hle.trans (integral_exp_neg_div_le_sat 9 hx₁ hxc hx)

/-- **The first-lobe cells with a small damping**: for `0 < lo`, `hi ≤ π/2` and `B` at least the
small-damping bound at `t = lo`, `β = 1/(100e·lo)` (`RMF.integral_cos_exp_div_le_small`). -/
theorem isRestCosBound_first_small {lo hi B : ℝ} (hlo : 0 < lo) (hhi : hi ≤ π / 2)
    (hB : Real.log (π / 2) - Real.log lo - ((π / 2) ^ 2 - lo ^ 2) / 4 + ((π / 2) ^ 4 - lo ^ 4) / 96
      - 1 / (100 * Real.exp 1) / lo * (1 - Real.sin lo)
      + (1 / (100 * Real.exp 1) / lo) ^ 2 / 2 * (π / 2 - lo * Real.sin lo - Real.cos lo) ≤ B) :
    IsRestCosBound lo hi B := by
  intro A τ σ U hA hτ hl hh hσ₁ _ hU
  have hτ0 : 0 < τ := by
    rcases hτ.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hl
      linarith
  have hσ0 : 0 ≤ σ := (sigma_pos_of_damping hA hσ₁).le
  set τ₀ : ℝ := lo / A with hτ₀
  set σ₀ : ℝ := 1 / (100 * Real.exp 1) / (2 * A) with hσ₀
  have hτ₀0 : 0 < τ₀ := by positivity
  have hτ₀τ : τ₀ ≤ τ := by rw [hτ₀, div_le_iff₀ hA]; linarith
  have hσ₀σ : σ₀ ≤ σ := by rw [hσ₀, div_le_iff₀ (by positivity)]; linarith
  have hAτ : τ * A ≤ π / 2 := hh.trans hhi
  have h1 := integral_cos_mul_exp_div_le_first_lobe hτ0 hσ0 hA hAτ hU
  have h2 := integral_first_lobe_le_of_le hτ₀0 hτ₀τ hσ₀σ hA hAτ
  rw [integral_cos_mul_exp_div_eq_comp hτ₀0] at h2
  have e1 : τ₀ * A = lo := by rw [hτ₀]; field_simp
  have e2 : τ₀ * (π / 2 / τ₀) = π / 2 := by field_simp
  have e3 : 2 * σ₀ / τ₀ = 1 / (100 * Real.exp 1) / lo := by rw [hσ₀, hτ₀]; field_simp
  rw [e1, e2, e3] at h2
  have h3 := integral_cos_exp_div_le_small hlo (hl.le.trans hAτ)
    (β := 1 / (100 * Real.exp 1) / lo) (by positivity)
  linarith

/-- **The first-lobe cells with any damping**: for `0 < lo`, `hi ≤ π/2`, a bound `e` on the
exponential integral from `βlo = 1/(100e)` to `βπ/2`, `β = 1/(100e·lo)`, and `B` at least
`e - (J₁(lo) - J₁(π/2))/2 + (J₃(lo) - J₃(π/2))/24` (`RMF.integral_cos_exp_div_le_large`). -/
theorem isRestCosBound_first_large {lo hi e B : ℝ} (hlo : 0 < lo) (hhi : hi ≤ π / 2)
    (he : ∫ s in 1 / (100 * Real.exp 1) / lo * lo..1 / (100 * Real.exp 1) / lo * (π / 2),
      Real.exp (-s) / s ≤ e)
    (hB : e - (Real.exp (-(1 / (100 * Real.exp 1) / lo) * lo)
          * (lo / (1 / (100 * Real.exp 1) / lo) + 1 / (1 / (100 * Real.exp 1) / lo) ^ 2)
        - Real.exp (-(1 / (100 * Real.exp 1) / lo) * (π / 2))
          * (π / 2 / (1 / (100 * Real.exp 1) / lo) + 1 / (1 / (100 * Real.exp 1) / lo) ^ 2)) / 2
      + (Real.exp (-(1 / (100 * Real.exp 1) / lo) * lo)
          * (lo ^ 3 / (1 / (100 * Real.exp 1) / lo)
            + 3 * lo ^ 2 / (1 / (100 * Real.exp 1) / lo) ^ 2
            + 6 * lo / (1 / (100 * Real.exp 1) / lo) ^ 3 + 6 / (1 / (100 * Real.exp 1) / lo) ^ 4)
        - Real.exp (-(1 / (100 * Real.exp 1) / lo) * (π / 2))
          * ((π / 2) ^ 3 / (1 / (100 * Real.exp 1) / lo)
            + 3 * (π / 2) ^ 2 / (1 / (100 * Real.exp 1) / lo) ^ 2
            + 6 * (π / 2) / (1 / (100 * Real.exp 1) / lo) ^ 3
            + 6 / (1 / (100 * Real.exp 1) / lo) ^ 4)) / 24 ≤ B) :
    IsRestCosBound lo hi B := by
  intro A τ σ U hA hτ hl hh hσ₁ _ hU
  have hτ0 : 0 < τ := by
    rcases hτ.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hl
      linarith
  have hσ0 : 0 ≤ σ := (sigma_pos_of_damping hA hσ₁).le
  set τ₀ : ℝ := lo / A with hτ₀
  set σ₀ : ℝ := 1 / (100 * Real.exp 1) / (2 * A) with hσ₀
  have hτ₀0 : 0 < τ₀ := by positivity
  have hτ₀τ : τ₀ ≤ τ := by rw [hτ₀, div_le_iff₀ hA]; linarith
  have hσ₀σ : σ₀ ≤ σ := by rw [hσ₀, div_le_iff₀ (by positivity)]; linarith
  have hAτ : τ * A ≤ π / 2 := hh.trans hhi
  have h1 := integral_cos_mul_exp_div_le_first_lobe hτ0 hσ0 hA hAτ hU
  have h2 := integral_first_lobe_le_of_le hτ₀0 hτ₀τ hσ₀σ hA hAτ
  rw [integral_cos_mul_exp_div_eq_comp hτ₀0] at h2
  have e1 : τ₀ * A = lo := by rw [hτ₀]; field_simp
  have e2 : τ₀ * (π / 2 / τ₀) = π / 2 := by field_simp
  have e3 : 2 * σ₀ / τ₀ = 1 / (100 * Real.exp 1) / lo := by rw [hσ₀, hτ₀]; field_simp
  rw [e1, e2, e3] at h2
  have h3 := integral_cos_exp_div_le_large hlo (hl.le.trans hAτ) (β := 1 / (100 * Real.exp 1) / lo)
    (by positivity)
  linarith

/-- **The second-lobe cells past `3π/2`**: for `3π/2 ≤ lo`, `hi ≤ 5π/2` and
`B ≥ lobeP(5π/2) - lobeP lo`: the lobe is nonnegative, so the damping only lowers it. -/
theorem isRestCosBound_second_pos {lo hi B : ℝ} (hlo : 3 * π / 2 ≤ lo) (hhi : hi ≤ 5 * π / 2)
    (hB : lobeP (5 * π / 2) - lobeP lo ≤ B) :
    IsRestCosBound lo hi B := by
  intro A τ σ U hA hτ hl hh hσ₁ _ hU
  have hπ := Real.pi_pos
  have hτ0 : 0 < τ := by
    rcases hτ.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hl
      linarith
  have hσ0 : 0 ≤ σ := (sigma_pos_of_damping hA hσ₁).le
  have hlo0 : 0 < lo := by linarith
  have h1 := integral_cos_mul_exp_div_le_second_lobe hτ0 hσ0 hA (by linarith) (hh.trans hhi) hU
  rw [integral_cos_mul_exp_div_eq_comp (A := A) (B := 5 * π / 2 / τ) hτ0] at h1
  have e2 : τ * (5 * π / 2 / τ) = 5 * π / 2 := by field_simp
  rw [e2] at h1
  have hi : ∀ c d : ℝ, 0 < c → c ≤ d →
      IntervalIntegrable (fun w => Real.cos w / w) volume c d :=
    fun c d hc hcd => ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop)
      continuousOn_id fun w hw => by
        rw [Set.uIcc_of_le hcd] at hw
        exact (hc.trans_le hw.1).ne')
  have hcos : ∀ w, 3 * π / 2 ≤ w → w ≤ 5 * π / 2 → 0 ≤ Real.cos w := fun w h₁ h₂ => by
    rw [← Real.cos_sub_two_pi]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hτA : τ * A ≤ 5 * π / 2 := hh.trans hhi
  -- drop the damping, then extend the lobe down to `lo`
  have h2 : ∫ w in τ * A..5 * π / 2, Real.cos w * Real.exp (-(2 * σ / τ) * w) / w
      ≤ ∫ w in τ * A..5 * π / 2, Real.cos w / w := by
    refine intervalIntegral.integral_mono_on hτA ?_ (hi _ _ (by linarith) hτA) fun w hw => ?_
    · exact ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) continuousOn_id
        fun w hw => by
          rw [Set.uIcc_of_le hτA] at hw
          exact (show (0 : ℝ) < τ * A by linarith).trans_le hw.1 |>.ne')
    have hw0 : 0 < w := by linarith [hw.1]
    have hc := hcos w (by linarith [hw.1]) hw.2
    have he : Real.exp (-(2 * σ / τ) * w) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ 2 * σ / τ := by positivity
      nlinarith)
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hc he) hw0.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi lo (τ * A) hlo0 hl.le)
    (hi (τ * A) (5 * π / 2) (by linarith) hτA)
  have h3 : 0 ≤ ∫ w in lo..τ * A, Real.cos w / w :=
    intervalIntegral.integral_nonneg hl.le fun w hw => by
      have hw0 : 0 < w := hlo0.trans_le hw.1
      exact div_nonneg (hcos w (by linarith [hw.1]) (by linarith [hw.2])) hw0.le
  have h4 := integral_cos_div_le_lobeP hlo0 (hl.le.trans hτA)
  have h5 : 0 ≤ ∫ w in lo..5 * π / 2, Real.cos w / w :=
    intervalIntegral.integral_nonneg (hl.le.trans hτA) fun w hw => by
      have hw0 : 0 < w := hlo0.trans_le hw.1
      exact div_nonneg (hcos w (by linarith [hw.1]) hw.2) hw0.le
  refine h1.trans (max_le (by linarith) (by linarith))

/-- **The second-lobe cells before `3π/2`**: for `π/2 ≤ lo`, `hi ≤ 3π/2`, a bound `N` on the
negative half-lobe `∫_{hi}^{3π/2} cos(w)/w dw`, `B ≥ 0` and
`B ≥ e^{-(3π/2)/(100 lo)}N + lobeP(5π/2) - lobeP(3π/2)`: the negative half-lobe at the largest
damping `β ≤ 1/(100 lo)`, the positive one undamped. -/
theorem isRestCosBound_second_neg {lo hi N B : ℝ} (hlo : π / 2 ≤ lo) (hhi : hi ≤ 3 * π / 2)
    (hN : ∫ w in hi..3 * π / 2, Real.cos w / w ≤ N) (hB0 : 0 ≤ B)
    (hB : Real.exp (-(1 / 100 / lo) * (3 * π / 2)) * N
      + (lobeP (5 * π / 2) - lobeP (3 * π / 2)) ≤ B) :
    IsRestCosBound lo hi B := by
  intro A τ σ U hA hτ hl hh hσ₁ hσ₂ hU
  have hπ := Real.pi_pos
  have hlo0 : 0 < lo := by linarith
  have hτ0 : 0 < τ := by
    rcases hτ.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hl
      linarith
  have hσ0 : 0 ≤ σ := (sigma_pos_of_damping hA hσ₁).le
  have hτA : τ * A ≤ 3 * π / 2 := hh.trans hhi
  have hτA0 : 0 < τ * A := by linarith
  have h1 := integral_cos_mul_exp_div_le_second_lobe hτ0 hσ0 hA (by linarith) (by linarith) hU
  rw [integral_cos_mul_exp_div_eq_comp (A := A) (B := 5 * π / 2 / τ) hτ0] at h1
  have e2 : τ * (5 * π / 2 / τ) = 5 * π / 2 := by field_simp
  rw [e2] at h1
  set β : ℝ := 2 * σ / τ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβmax : β ≤ 1 / 100 / lo := by
    rw [hβ, div_le_div_iff₀ hτ0 hlo0]
    have : 2 * σ * lo ≤ 2 * σ * (τ * A) := mul_le_mul_of_nonneg_left hl.le (by positivity)
    nlinarith
  have hi2 : ∀ c d : ℝ, 0 < c → c ≤ d → IntervalIntegrable
      (fun w => Real.cos w * Real.exp (-β * w) / w) volume c d :=
    fun c d hc hcd => ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop)
      continuousOn_id fun w hw => by
        rw [Set.uIcc_of_le hcd] at hw
        exact (hc.trans_le hw.1).ne')
  have hic : ∀ c d : ℝ, 0 < c → c ≤ d →
      IntervalIntegrable (fun w => Real.cos w / w) volume c d :=
    fun c d hc hcd => ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop)
      continuousOn_id fun w hw => by
        rw [Set.uIcc_of_le hcd] at hw
        exact (hc.trans_le hw.1).ne')
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi2 (τ * A) (3 * π / 2) hτA0 hτA) (hi2 (3 * π / 2) (5 * π / 2) (by linarith) (by linarith))
  -- the negative half-lobe
  set c : ℝ := Real.exp (-(1 / 100 / lo) * (3 * π / 2)) with hc
  have hneg : ∫ w in τ * A..3 * π / 2, Real.cos w * Real.exp (-β * w) / w
      ≤ c * ∫ w in τ * A..3 * π / 2, Real.cos w / w := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hτA (hi2 _ _ hτA0 hτA)
      ((hic _ _ hτA0 hτA).const_mul c) fun w hw => ?_
    have hw0 : 0 < w := hτA0.trans_le hw.1
    have hcw : Real.cos w ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hw.1]) (by linarith [hw.2])
    have he : c ≤ Real.exp (-β * w) := Real.exp_le_exp.2 (by
      have h1 : β * w ≤ β * (3 * π / 2) := mul_le_mul_of_nonneg_left hw.2 hβ0
      have h2 : β * (3 * π / 2) ≤ 1 / 100 / lo * (3 * π / 2) :=
        mul_le_mul_of_nonneg_right hβmax (by positivity)
      linarith)
    have : Real.cos w * Real.exp (-β * w) ≤ c * Real.cos w := by
      rw [mul_comm c]
      exact mul_le_mul_of_nonpos_left he hcw
    calc Real.cos w * Real.exp (-β * w) / w ≤ c * Real.cos w / w :=
          div_le_div_of_nonneg_right this hw0.le
      _ = c * (Real.cos w / w) := by ring
  have hext : ∫ w in τ * A..3 * π / 2, Real.cos w / w ≤ ∫ w in hi..3 * π / 2, Real.cos w / w := by
    have hsp := intervalIntegral.integral_add_adjacent_intervals (hic (τ * A) hi hτA0 hh)
      (hic hi (3 * π / 2) (hτA0.trans_le hh) hhi)
    have hnp : ∫ w in τ * A..hi, Real.cos w / w ≤ 0 :=
      intervalIntegral_nonpos_of_le hh fun w hw => by
        have hw0 : 0 < w := hτA0.trans_le hw.1
        exact div_nonpos_of_nonpos_of_nonneg (Real.cos_nonpos_of_pi_div_two_le_of_le
          (by linarith [hw.1]) (by linarith [hw.2])) hw0.le
    linarith
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hnegN : c * ∫ w in τ * A..3 * π / 2, Real.cos w / w ≤ c * N :=
    mul_le_mul_of_nonneg_left (hext.trans hN) hc0
  -- the positive half-lobe
  have hpos : ∫ w in 3 * π / 2..5 * π / 2, Real.cos w * Real.exp (-β * w) / w
      ≤ lobeP (5 * π / 2) - lobeP (3 * π / 2) := by
    refine le_trans ?_ (integral_cos_div_le_lobeP (by linarith) (by linarith))
    refine intervalIntegral.integral_mono_on (by linarith) (hi2 _ _ (by linarith) (by linarith))
      (hic _ _ (by linarith) (by linarith)) fun w hw => ?_
    have hw0 : 0 < w := by linarith [hw.1]
    have hcw : 0 ≤ Real.cos w := by
      rw [← Real.cos_sub_two_pi]
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hw.1]) (by linarith [hw.2])
    have he : Real.exp (-β * w) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hcw he) hw0.le
  refine h1.trans (max_le hB0 ?_)
  have hβe : -(2 * σ / τ) = -β := by rw [hβ]
  rw [hβe]
  linarith

end RMF
