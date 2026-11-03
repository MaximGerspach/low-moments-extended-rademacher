/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UMidRegimeExplicit
import RMF.Reduction.UpperSwitch

/-!
# The first moment below `q = ½`: (U) for `0 < q ≤ 0.49` and every `x ≥ 3`

The bound (U) for `q ≤ 0.49`: `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` for
`S(x) = ∑_{n≤x} f(n)/√n` and `Λ = log log x`
(`RMF.integral_rpow_weightedRademacherSum_le_u_of_le_049`).  For `q ∈ [0.41, 0.49]` the cells of
the middle, Jensen and chaos regimes cover `x ≥ exp(e⁷)`, and (H) (`E|S(x)| ≤ 10Λ^{3/4}`) with
Lyapunov covers `Λ ≤ 7` (`RMF.u_trivial`); below `0.41` Lyapunov descends from `q₀ = 0.41`
(`RMF.u_descent`), by `2q₀ ≤ a log(25/a)` for `a = Λ⁻¹ + 1 - 2q₀` (`RMF.descent_key`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### (U) below `q = 0.49` for every `x ≥ 3` -/

/-- The weighted sum is in every `L^p`: it is bounded by `⌊x⌋` almost surely. -/
lemma memLp_weightedRademacherSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) (p : ℝ≥0∞) :
    MemLp (weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x) p μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hWm : Measurable
      (weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x) :=
    Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _
  exact (memLp_top_of_bound hWm.aestronglyMeasurable _
    (ae_norm_weightedRademacherSum_le hRa x)).mono_exponent le_top

/-- `log log x ≥ 0.094` for `x ≥ 3`. -/
lemma loglog_ge_of_three_le {x : ℝ} (hx : 3 ≤ x) : 94 / 1000 ≤ Real.log (Real.log x) := by
  have h3 : (1 : ℝ) < Real.log 3 := by
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact this
  have hl : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h1 : Real.log (Real.log 3) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by linarith) hl
  have h2 : (94 / 1000 : ℝ) ≤ Real.log (Real.log 3) := by interval_decide (trust := kernel)
  linarith

/-- **(U) from (H) and Lyapunov**: for `x ≥ 3` and `0 < q ≤ ½`,
`E|S(x)|^{2q} ≤ (E|S(x)|)^{2q} ≤ (10Λ^{3/4})^{2q}`
(`RMF.integral_norm_weightedRademacherSum_le_ten_of_three_le`). -/
theorem integral_rpow_le_of_ten {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ (10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (2 * q) := by
  haveI := hX.isProbabilityMeasure
  have h := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := 1 / 2) (q := q) hq0.le hq
    (memLp_weightedRademacherSum hX x _)
  simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at h
  have hH := integral_norm_weightedRademacherSum_le_ten_of_three_le hX hx
  have h0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ∂μ := integral_nonneg fun ω => norm_nonneg _
  calc _ ≤ _ := h
    _ ≤ (10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (q / (1 / 2)) :=
        Real.rpow_le_rpow h0 hH (by positivity)
    _ = (10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (2 * q) := by
        congr 1
        ring

/-- **(U) for `log log x ≤ 7`**: for `3 ≤ x` with `Λ ≤ 7` and `q ∈ [0.41, ½]`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`: by `RMF.integral_rpow_le_of_ten`,
`(10Λ^{3/4})^{2q} = (10Λ)^{2q}Λ^{-q/2}` and `(10Λ)^{2q}(Λ⁻¹ + 1 - 2q) ≤ 22.6`. -/
theorem u_trivial {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : 3 ≤ x) (hΛ : Real.log (Real.log x) ≤ 7) (hq1 : 41 / 100 ≤ q)
    (hq2 : q ≤ 1 / 2) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hq0 : 0 < q := by linarith
  refine le_trans (integral_rpow_le_of_ten hX hx hq0 hq2) ?_
  have hΛ0 := loglog_ge_of_three_le hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛp : 0 < Λ := by linarith
  -- `(10Λ^{3/4})^{2q} = (10Λ)^{2q}·Λ^{-q/2}`
  have e : (10 * Λ ^ (3 / 4 : ℝ)) ^ (2 * q) = (10 * Λ) ^ (2 * q) * Λ ^ (-(q / 2)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hΛp.le _),
      Real.mul_rpow (by norm_num) hΛp.le, ← Real.rpow_mul hΛp.le, mul_assoc,
      ← Real.rpow_add hΛp]
    congr 2
    ring
  rw [e]
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛp; linarith
  have hΛq : 0 < Λ ^ (-(q / 2)) := Real.rpow_pos_of_pos hΛp _
  -- `(10Λ)^{2q}V ≤ 25`
  have hkey : (10 * Λ) ^ (2 * q) * V ≤ 25 := by
    have hΛi : Λ⁻¹ ≤ 1000 / 94 := by
      rw [inv_le_comm₀ hΛp (by norm_num)]
      rw [inv_div]
      exact hΛ0
    rcases le_total (10 * Λ) 1 with h1 | h1
    · have ha : (10 * Λ) ^ (2 * q) ≤ 1 := Real.rpow_le_one (by positivity) h1 (by linarith)
      have hV : V ≤ 1000 / 94 + 18 / 100 := by rw [hVdef]; linarith
      calc (10 * Λ) ^ (2 * q) * V ≤ 1 * V :=
            mul_le_mul_of_nonneg_right ha hV0.le
        _ ≤ 25 := by linarith
    · have ha : (10 * Λ) ^ (2 * q) ≤ 10 * Λ := by
        calc (10 * Λ) ^ (2 * q) ≤ (10 * Λ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ = 10 * Λ := Real.rpow_one _
      have e2 : 10 * Λ * V = 10 + 10 * (1 - 2 * q) * Λ := by
        rw [hVdef]; field_simp
      have h3 : 10 * (1 - 2 * q) * Λ ≤ 10 * (18 / 100) * 7 := by
        have : 1 - 2 * q ≤ 18 / 100 := by linarith
        have h0 : 0 ≤ 1 - 2 * q := by linarith
        have := mul_le_mul this hΛ (by linarith) (by norm_num)
        linarith
      calc (10 * Λ) ^ (2 * q) * V ≤ 10 * Λ * V := mul_le_mul_of_nonneg_right ha hV0.le
        _ ≤ 25 := by rw [e2]; linarith
  calc (10 * Λ) ^ (2 * q) * Λ ^ (-(q / 2)) = (10 * Λ) ^ (2 * q) * V * (V⁻¹ * Λ ^ (-(q / 2))) := by
        field_simp
    _ ≤ 25 * (V⁻¹ * Λ ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_right hkey (mul_nonneg (inv_pos.2 hV0).le hΛq.le)
    _ = 25 * V⁻¹ * Λ ^ (-(q / 2)) := by ring

/-- **The descent's inequality**: `0.82/a ≤ log(25/a)` on `a ∈ [0.18, 10.9]`, on five intervals. -/
lemma descent_key {a : ℝ} (ha1 : 18 / 100 ≤ a) (ha2 : a ≤ 109 / 10) :
    82 / 100 / a ≤ Real.log (25 / a) := by
  have ha0 : 0 < a := by linarith
  have hlog : ∀ c : ℝ, 0 < c → a ≤ 25 / c → Real.log c ≤ Real.log (25 / a) := fun c hc h =>
    Real.log_le_log hc (by rw [le_div_iff₀ ha0]; rw [le_div_iff₀ hc] at h; linarith)
  have hdiv : ∀ b : ℝ, 0 < b → b ≤ a → 82 / 100 / a ≤ 82 / 100 / b := fun b hb h =>
    div_le_div_of_nonneg_left (by norm_num) hb h
  rcases le_total a (1 / 5) with h1 | h1
  · have := hlog 125 (by norm_num) (by linarith)
    have := hdiv (18 / 100) (by norm_num) ha1
    have : (82 / 100 / (18 / 100) : ℝ) ≤ Real.log 125 := by interval_decide (trust := kernel)
    linarith
  rcases le_total a (1 / 4) with h2 | h2
  · have := hlog 100 (by norm_num) (by linarith)
    have := hdiv (1 / 5) (by norm_num) h1
    have : (82 / 100 / (1 / 5) : ℝ) ≤ Real.log 100 := by interval_decide (trust := kernel)
    linarith
  rcases le_total a (2 / 5) with h3 | h3
  · have := hlog (125 / 2) (by norm_num) (by linarith)
    have := hdiv (1 / 4) (by norm_num) h2
    have : (82 / 100 / (1 / 4) : ℝ) ≤ Real.log (125 / 2) := by interval_decide (trust := kernel)
    linarith
  rcases le_total a 1 with h4 | h4
  · have := hlog 25 (by norm_num) (by linarith)
    have := hdiv (2 / 5) (by norm_num) h3
    have : (82 / 100 / (2 / 5) : ℝ) ≤ Real.log 25 := by interval_decide (trust := kernel)
    linarith
  · have := hlog (250 / 109) (by norm_num) (by rw [div_div_eq_mul_div]; linarith)
    have := hdiv 1 (by norm_num) h4
    have : (82 / 100 / 1 : ℝ) ≤ Real.log (250 / 109) := by interval_decide (trust := kernel)
    linarith

set_option maxHeartbeats 1000000 in
-- Lyapunov and the descent's inequality
/-- **The descent below `q₀ = 0.41`**: if `E|S(x)|^{0.82} ≤ 25τ(0.41)` then
`E|S(x)|^{2q} ≤ 25τ(q)` for every `0 < q ≤ 0.41`, `x ≥ 3`, `τ(q) = (Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`.
By Lyapunov `E|S|^{2q} ≤ (E|S|^{0.82})^s`, `s = q/0.41`, the `Λ^{-q/2}` cancel, and with
`a = Λ⁻¹ + 0.18 ∈ [0.18, 10.9]` and `u = 1 - s` the rest is `a + 0.82u ≤ a(25/a)^u`, from
`e^y ≥ 1 + y` and `0.82 ≤ a log(25/a)` (`RMF.descent_key`). -/
theorem u_descent {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q) (hq : q ≤ 41 / 100)
    (h41 : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * (41 / 100 : ℝ)) ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * (41 / 100 : ℝ)))⁻¹
        * Real.log (Real.log x) ^ (-((41 / 100 : ℝ) / 2))) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  have hΛ0 := loglog_ge_of_three_le hx
  have hL := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := 41 / 100) (q := q) hq0.le hq
    (memLp_weightedRademacherSum hX x _)
  set E0 := ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
    ^ (2 * (41 / 100 : ℝ)) ∂μ with hE0def
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛp : 0 < Λ := by linarith
  have hE0 : 0 ≤ E0 := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  set s := q / (41 / 100) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hsdef, div_le_one (by norm_num)]; exact hq
  set u := 1 - s with hudef
  have hu0 : 0 ≤ u := by linarith
  have hqs : q = 41 / 100 * s := by rw [hsdef]; field_simp
  set a := Λ⁻¹ + (1 - 2 * (41 / 100 : ℝ)) with hadef
  have hΛi0 : 0 < Λ⁻¹ := inv_pos.2 hΛp
  have hΛi : Λ⁻¹ ≤ 1000 / 94 := by
    rw [inv_le_comm₀ hΛp (by norm_num), inv_div]
    exact hΛ0
  have ha1 : 18 / 100 ≤ a := by rw [hadef]; linarith
  have ha2 : a ≤ 109 / 10 := by rw [hadef]; linarith
  have ha0 : 0 < a := by linarith
  have hkey := descent_key ha1 ha2
  set Lg := Real.log (25 / a) with hLgdef
  have hkey' : 2 * (41 / 100) ≤ a * Lg := by
    rw [div_le_iff₀ ha0] at hkey
    linarith
  -- `25τ(0.41) = e^{L - (0.41/2)log Λ}`
  have hτ0 : 25 * a⁻¹ * Λ ^ (-((41 / 100 : ℝ) / 2))
      = Real.exp (Lg - 41 / 100 / 2 * Real.log Λ) := by
    rw [Real.exp_sub, hLgdef, Real.exp_log (by positivity), rpow_eq_exp_mul_log hΛp,
      show -((41 / 100 : ℝ) / 2) * Real.log Λ = -(41 / 100 / 2 * Real.log Λ) by ring,
      Real.exp_neg]
    field_simp
  rw [hτ0] at h41
  -- Lyapunov
  have h1 : E0 ^ s ≤ Real.exp (Lg - 41 / 100 / 2 * Real.log Λ) ^ s :=
    Real.rpow_le_rpow hE0 h41 hs0
  rw [← Real.exp_mul] at h1
  -- `a + 0.82u ≤ a e^{uL}`
  have hexp : a + 2 * (41 / 100) * u ≤ a * Real.exp (u * Lg) := by
    have h2 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u * Lg)) ha0.le
    have h3 := mul_le_mul_of_nonneg_left hkey' hu0
    nlinarith
  have hV : Λ⁻¹ + (1 - 2 * q) = a + 2 * (41 / 100) * u := by
    rw [hadef, hudef, hqs]; ring
  rw [hV]
  have hVpos : 0 < a + 2 * (41 / 100) * u := by positivity
  -- `e^{sL} ≤ 25/(a + 0.82u)`
  have hsL : Real.exp (s * Lg) ≤ 25 * (a + 2 * (41 / 100) * u)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hVpos]
    have e1 : Real.exp (s * Lg) = 25 / a * Real.exp (-(u * Lg)) := by
      rw [hudef, show s * Lg = Lg + -((1 - s) * Lg) by ring, Real.exp_add, hLgdef,
        Real.exp_log (by positivity)]
    rw [e1]
    have h4 : 25 / a * Real.exp (-(u * Lg)) * (a * Real.exp (u * Lg)) = 25 := by
      rw [show 25 / a * Real.exp (-(u * Lg)) * (a * Real.exp (u * Lg))
        = 25 / a * a * (Real.exp (-(u * Lg)) * Real.exp (u * Lg)) by ring, ← Real.exp_add,
        show -(u * Lg) + u * Lg = 0 by ring, Real.exp_zero, mul_one]
      field_simp
    calc 25 / a * Real.exp (-(u * Lg)) * (a + 2 * (41 / 100) * u)
        ≤ 25 / a * Real.exp (-(u * Lg)) * (a * Real.exp (u * Lg)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 25 := h4
  have e2 : (Lg - 41 / 100 / 2 * Real.log Λ) * s = s * Lg + -(q / 2) * Real.log Λ := by
    rw [hqs]; ring
  calc _ ≤ E0 ^ (q / (41 / 100)) := hL
    _ = E0 ^ s := rfl
    _ ≤ Real.exp ((Lg - 41 / 100 / 2 * Real.log Λ) * s) := h1
    _ = Real.exp (s * Lg) * Λ ^ (-(q / 2)) := by
        rw [e2, Real.exp_add, rpow_eq_exp_mul_log hΛp]
    _ ≤ 25 * (a + 2 * (41 / 100) * u)⁻¹ * Λ ^ (-(q / 2)) :=
        mul_le_mul_of_nonneg_right hsL (Real.rpow_nonneg hΛp.le _)

/-- `x ≥ exp(e⁷)` from `log log x > 7` and `x ≥ 3`. -/
lemma exp_exp_seven_le_of {x : ℝ} (hx : 3 ≤ x) (hΛ : 7 < Real.log (Real.log x)) :
    Real.exp (Real.exp 7) ≤ x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.exp 7 ≤ Real.log x := (Real.le_log_iff_exp_le hL).1 hΛ.le
  exact (Real.le_log_iff_exp_le hx0).1 h1

/-- **(U) for `0 < q ≤ 0.49` and every `x ≥ 3`**:
`E|∑_{n≤x} f(n)/√n|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, `Λ = log log x`.  For `q ∈ [0.41, 0.49]`:
up to `Λ = 7` by (H) and Lyapunov (`RMF.u_trivial`), beyond by the middle, Jensen and chaos
regimes' cells (`RMF.u_regime_mid_large`); below `q = 0.41` by the descent (`RMF.u_descent`). -/
theorem integral_rpow_weightedRademacherSum_le_u_of_le_049 {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q)
    (hq : q ≤ 49 / 100) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have h41 : ∀ q' : ℝ, 41 / 100 ≤ q' → q' ≤ 49 / 100 →
      (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q') ∂μ)
        ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q'))⁻¹
          * Real.log (Real.log x) ^ (-(q' / 2)) := by
    intro q' h1 h2
    rcases le_or_gt (Real.log (Real.log x)) 7 with hΛ | hΛ
    · exact u_trivial hX hx hΛ h1 (by linarith)
    · exact u_regime_mid_large hX (exp_exp_seven_le_of hx hΛ) h1 h2
  rcases le_or_gt (41 / 100) q with hq1 | hq1
  · exact h41 q hq1 hq
  · exact u_descent hX hx hq0 hq1.le (h41 (41 / 100) le_rfl (by norm_num))

end RMF
