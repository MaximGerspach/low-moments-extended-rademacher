/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.PairWindowData

/-!
# The comparisons at offsets `20` and above

Every Gaussian comparison of the chain is one numerical condition per block: the swap error is at
most `ε_m·q_m`, with `ε_m = RMF.blockEps θ m = e^{-eE/100}`, `E = e^{m+θ}`, and `q_m` the Gaussian
mass of a window or box whose corners lie in the envelope.  The swap side is at most `e^{12-E/8}`
(`RMF.blockNum_lhs_le_exp`), so the condition is `12 + L ≤ 0.0978·E` once `q_m ≥ e^{-L}`
(`1/8 - e/100 = 0.097817…`).  Here the masses carry their dependence on the envelope, the
variance bracket, the determinant and the mean bound explicitly, and the comparisons take those
as parameters with a per-block budget:

* **The masses**: `RMF.windowMassExp` (one dimension, `3 + (M + K + 1)²/(2v₋)`) and
  `RMF.boxMassExp` (two dimensions, `16 + D²/(2v₋) + 2v₊D²/δ`, `D = M + K + 2`, `δ` the
  determinant floor: the sheared corner costs `(1 + |ρ|)²D²/(2s²) ≤ 2v₊D²/δ`).
* **The budget lemmas**: `RMF.blockNumAdd_le_of_budget`, `RMF.blockNum_le_of_budget`,
  `RMF.blockNumAdd₂_le_of_budget` (`13` for `12`: the two-fold third moments cost a factor `2`).
* **The comparisons at `θ ≥ 20`**: `RMF.exists_isGaussianWalk_rademacher_budget` (one dimension,
  HP2's prefix), `RMF.exists_isBoxComparison_rademacher_budget` (one-point tilt, HP1) and
  `RMF.exists_isBoxComparison_rademacher_budget₂` (two-fold tilt, HP2's post part).
* **The budgets of the three applications**, discharged on every block: `RMF.hp2Prefix_budget`
  (envelope `C(m+1)`, `C ≤ 800`), `RMF.hp1_budget` (`C(m+1)`, `C ≤ 58`), with the variances at
  most `1.01` from `RMF.window_block_comparison_inputs_budget`, and `RMF.hp2Post_budget`
  (`C(b+j+1)`, `C ≤ 770`, offset `θ ≥ 20 + b`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The masses, with their dependence explicit -/

/-- **The exponent of the one-dimensional window mass**, `3 + (M + K + 1)²/(2v₋)`
(`RMF.le_toReal_measure_Ioc_gaussianReal_windowMassExp`). -/
noncomputable def windowMassExp (vl K M : ℝ) : ℝ := 3 + (M + K + 1) ^ 2 / (2 * vl)

/-- **The exponent of the det-aware box mass**, `16 + D²/(2v₋) + 2v₊D²/δ` with `D = M + K + 2`
(`RMF.le_toReal_measure_box_gaussianPairLaw_boxMassExp`). -/
noncomputable def boxMassExp (vl vu δ K M : ℝ) : ℝ :=
  16 + (M + K + 2) ^ 2 / (2 * vl) + 2 * vu * (M + K + 2) ^ 2 / δ

/-- **The window mass with its dependence explicit.**  A Gaussian with variance in `[v₋, 10]` and
mean at most `K` puts mass at least `h·e^{-L₁}`, `L₁ = RMF.windowMassExp v₋ K M`, on every window
`(c, c + h]` with `0 ≤ h ≤ 1` and `|c| ≤ M`: `RMF.le_toReal_measure_Ioc_gaussianReal_of_thr` at
`x = e`, with `log(20π)/2 ≤ 3`. -/
theorem le_toReal_measure_Ioc_gaussianReal_windowMassExp {m₀ : ℝ} {v : ℝ≥0} {vl K M h c : ℝ}
    (hvl : 0 < vl) (hvl' : vl ≤ (v : ℝ)) (hvu : (v : ℝ) ≤ 10) (hm : |m₀| ≤ K) (hh : 0 ≤ h)
    (hh1 : h ≤ 1) (hc : |c| ≤ M) :
    h * Real.exp (-windowMassExp vl K M) ≤ (gaussianReal m₀ v (Set.Ioc c (c + h))).toReal := by
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, NNReal.coe_zero] at hvl'
    linarith
  have hx : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hA : (0 : ℝ) < 1 / (2 * vl) := by positivity
  have hthr : 1 / (2 * vl) * (M + |m₀| + h) ^ 2 + Real.log (Real.pi * 20) / 2
      ≤ windowMassExp vl K M * Real.log (Real.exp 1) := by
    rw [Real.log_exp, mul_one, windowMassExp]
    have h1 : (M + |m₀| + h) ^ 2 ≤ (M + K + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith [abs_nonneg m₀, abs_nonneg c]) (by linarith) 2
    have h2 : Real.log (Real.pi * 20) ≤ 6 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have h6 : (63 : ℝ) ≤ Real.exp 6 := by
        simpa using le_exp_natCast_of_le_pow (c := 2) (k := 6) (N := 63) (by norm_num)
          (by linarith [Real.exp_one_gt_d9]) (by norm_num)
      linarith
    have h3 : 1 / (2 * vl) * (M + |m₀| + h) ^ 2 ≤ (M + K + 1) ^ 2 / (2 * vl) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    linarith
  have hmass := le_toReal_measure_Ioc_gaussianReal_of_thr (m := m₀) (c := c) hv hh hA
    (by norm_num : (0 : ℝ) < 20) (by rw [one_div_one_div]; linarith) (by linarith) hx hc hthr
  rwa [Real.exp_one_rpow] at hmass

/-- **The box mass at any correlation, det-aware.**  A Gaussian pair with variances `V₁ ≥ v₋`,
`V₁, V₂ ≤ v₊`, `1/100 ≤ v₋`, `v₊ ≤ 10`, determinant `V₁V₂ − cv² ≥ δ > 0` and means at most `K`
puts mass at least `h²·e^{-L₂}`, `L₂ = RMF.boxMassExp v₋ v₊ δ K M`, on every box of side
`h ≤ 1` with corners at most `M`.  The sheared corner is priced by the determinant:
`(1 + |ρ|)²V₁ ≤ 2(V₁ + V₂) ≤ 4v₊` and `s²V₁ = V₁V₂ − cv² ≥ δ`, so
`((1 + |ρ|)D/s)²/2 ≤ 2v₊D²/δ`; the first coordinate costs `D²/(2v₋)` and the prefactor `e¹⁶`. -/
theorem le_toReal_measure_box_gaussianPairLaw_boxMassExp {m₁ m₂ V₁ V₂ cv : ℝ}
    {vl vu δ K M h c d : ℝ} (hvl : 1 / 100 ≤ vl) (hvu : vu ≤ 10) (hV₁l : vl ≤ V₁)
    (hV₁u : V₁ ≤ vu) (hV₂u : V₂ ≤ vu) (hδ : 0 < δ) (hdet : δ ≤ V₁ * V₂ - cv ^ 2)
    (hm₁ : |m₁| ≤ K) (hm₂ : |m₂| ≤ K) (hh : 0 < h) (hh1 : h ≤ 1) (hc : |c| ≤ M)
    (hd : |d| ≤ M) :
    h ^ 2 * Real.exp (-boxMassExp vl vu δ K M)
      ≤ (gaussianPairLaw m₁ m₂ V₁ V₂ cv (Set.Ioc c (c + h) ×ˢ Set.Ioc d (d + h))).toReal := by
  have hV₁pos : (0 : ℝ) < V₁ := by linarith
  have hvl0 : (0 : ℝ) < vl := by linarith
  have hK0 : 0 ≤ K := (abs_nonneg m₁).trans hm₁
  have hM0 : 0 ≤ M := (abs_nonneg c).trans hc
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = M + K + 2 := ⟨_, rfl⟩
  have hL : boxMassExp vl vu δ K M = 16 + D ^ 2 / (2 * vl) + 2 * vu * D ^ 2 / δ := by
    rw [boxMassExp, hDdef]
  rw [hL]
  have hD2 : 2 ≤ D := by rw [hDdef]; linarith
  have hV₁u' : V₁ ≤ 10 := by linarith
  have hV₂u' : V₂ ≤ 10 := by linarith
  have hcv2 : cv ^ 2 ≤ V₁ * V₂ := by linarith
  have hV₂pos : (0 : ℝ) < V₂ := pos_of_mul_pos_right (by linarith [sq_nonneg cv]) hV₁pos.le
  have hcv : |cv| ≤ 10 := by
    have h100 : V₁ * V₂ ≤ 10 * 10 := mul_le_mul hV₁u' hV₂u' hV₂pos.le (by norm_num)
    have h1 : cv ^ 2 ≤ 10 ^ 2 := by linarith
    have h2 := sq_le_sq.1 h1
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 10)] at h2
  set ρ := pairSlope V₁ cv with hρdef
  set R := pairResidVar V₁ V₂ cv with hRdef
  have hρV₁ : ρ * V₁ = cv := by rw [hρdef, pairSlope]; exact div_mul_cancel₀ cv hV₁pos.ne'
  have hRV : R * V₁ = V₁ * V₂ - cv ^ 2 := by
    rw [hRdef, pairResidVar, sub_mul, div_mul_cancel₀ _ hV₁pos.ne']; ring
  have hR0 : 0 < R := pos_of_mul_pos_left (by rw [hRV]; linarith) hV₁pos.le
  set s := Real.sqrt R with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hR0
  have hss : s ^ 2 = R := Real.sq_sqrt hR0.le
  have hRle : R ≤ V₂ := by
    rw [hRdef, pairResidVar]
    have : 0 ≤ cv ^ 2 / V₁ := div_nonneg (sq_nonneg cv) hV₁pos.le
    linarith
  have hs4 : s ≤ 4 := by
    rw [hsdef]
    calc Real.sqrt R ≤ Real.sqrt (4 ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = 4 := Real.sqrt_sq (by norm_num)
  have hρ0 : 0 ≤ |ρ| := abs_nonneg ρ
  have hρabs : |ρ| * V₁ = |cv| := by rw [← hρV₁, abs_mul, abs_of_pos hV₁pos]
  have hρle : |ρ| ≤ 1000 := le_of_mul_le_mul_right (by linarith) hV₁pos
  -- the sheared corner's price: `(1 + |ρ|)²δ ≤ 4v₊R`
  have hρV : ρ ^ 2 * V₁ ≤ V₂ := by
    have h1 : ρ ^ 2 * V₁ * V₁ = cv ^ 2 := by rw [← hρV₁]; ring
    have h2 : ρ ^ 2 * V₁ * V₁ ≤ V₂ * V₁ := by rw [h1]; linarith
    exact le_of_mul_le_mul_right h2 hV₁pos
  have hρsq : (1 + |ρ|) ^ 2 ≤ 2 + 2 * ρ ^ 2 := by
    linarith [sq_abs ρ, sq_nonneg (|ρ| - 1)]
  have hkey : (1 + |ρ|) ^ 2 * δ ≤ 4 * vu * R := by
    have h1 : (1 + |ρ|) ^ 2 * V₁ ≤ 4 * vu := by
      have := mul_le_mul_of_nonneg_right hρsq hV₁pos.le
      linarith
    have hvu0 : 0 ≤ vu := by linarith
    have h2 : (1 + |ρ|) ^ 2 * δ * V₁ ≤ 4 * vu * R * V₁ := by
      calc (1 + |ρ|) ^ 2 * δ * V₁ = (1 + |ρ|) ^ 2 * V₁ * δ := by ring
        _ ≤ 4 * vu * δ := mul_le_mul_of_nonneg_right h1 hδ.le
        _ ≤ 4 * vu * (V₁ * V₂ - cv ^ 2) := mul_le_mul_of_nonneg_left hdet (by positivity)
        _ = 4 * vu * R * V₁ := by rw [← hRV]; ring
    exact le_of_mul_le_mul_right h2 hV₁pos
  have hC₂sq : ((1 + |ρ|) * D / s) ^ 2 ≤ 4 * vu * D ^ 2 / δ := by
    rw [div_pow, mul_pow, hss, div_le_div_iff₀ hR0 hδ]
    calc (1 + |ρ|) ^ 2 * D ^ 2 * δ = (1 + |ρ|) ^ 2 * δ * D ^ 2 := by ring
      _ ≤ 4 * vu * R * D ^ 2 := mul_le_mul_of_nonneg_right hkey (sq_nonneg D)
      _ = 4 * vu * D ^ 2 * R := by ring
  -- the first window, shrunk so that the shear fits
  obtain ⟨h₁, hh₁def⟩ : ∃ h₁ : ℝ, h₁ = h / (8 * (1 + |ρ|)) := ⟨_, rfl⟩
  have hfac : (0 : ℝ) < 1 + |ρ| := by linarith
  have hh₁0 : 0 < h₁ := by rw [hh₁def]; positivity
  have hh₁mul : h₁ * (8 * (1 + |ρ|)) = h := by
    rw [hh₁def]; exact div_mul_cancel₀ h (by positivity)
  have hh₁8 : h₁ ≤ h / 8 := by linarith [hh₁mul, mul_nonneg hρ0 hh₁0.le]
  have hgeo : 2 * |ρ| * h₁ + h / 4 ≤ h / 2 := by linarith [hh₁mul, hh₁0]
  -- the two corners
  have hC₁ : |c + h / 4 - m₁| + h₁ ≤ D := by
    have h1 : |c + h / 4 - m₁| ≤ |c| + h / 4 + |m₁| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le c, le_abs_self c, neg_abs_le m₁, le_abs_self m₁]
    rw [hDdef]; linarith
  have hC₂ : |d + h / 4 - m₂ + |ρ| * h₁ - ρ * (c + h / 4 - m₁)| / s + h / (4 * s)
      ≤ (1 + |ρ|) * D / s := by
    have hin : |ρ * (c + h / 4 - m₁)| ≤ |ρ| * (M + K + 1) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ hρ0
      rw [abs_le]
      constructor <;> linarith [neg_abs_le c, le_abs_self c, neg_abs_le m₁, le_abs_self m₁]
    have hρh₁ : |ρ| * h₁ ≤ |ρ| * 1 := mul_le_mul_of_nonneg_left (by linarith) hρ0
    have hstep : |d + h / 4 - m₂ + |ρ| * h₁ - ρ * (c + h / 4 - m₁)|
        ≤ |d| + h / 4 + |m₂| + |ρ| * h₁ + |ρ * (c + h / 4 - m₁)| := by
      rw [abs_le]
      constructor <;>
        linarith [neg_abs_le d, le_abs_self d, neg_abs_le m₂, le_abs_self m₂,
          neg_abs_le (ρ * (c + h / 4 - m₁)), le_abs_self (ρ * (c + h / 4 - m₁)),
          mul_nonneg hρ0 hh₁0.le]
    have hnum : |d + h / 4 - m₂ + |ρ| * h₁ - ρ * (c + h / 4 - m₁)| + h / 4
        ≤ (1 + |ρ|) * D := by
      rw [hDdef]
      linarith [hstep, hin, hρh₁, hd, hm₂]
    have hrw : (|d + h / 4 - m₂ + |ρ| * h₁ - ρ * (c + h / 4 - m₁)| + h / 4) / s
        = |d + h / 4 - m₂ + |ρ| * h₁ - ρ * (c + h / 4 - m₁)| / s + h / (4 * s) := by
      rw [add_div, div_div]
    rw [← hrw]
    exact div_le_div_of_nonneg_right hnum hs0.le
  have hbox := le_toReal_measure_box_gaussianPairLaw_corr (m₁ := m₁) (m₂ := m₂) (V₁ := V₁)
    (V₂ := V₂) (c := cv) (ρ₀ := |ρ|) (h := h) (h₁ := h₁) (C₁ := D)
    (C₂ := (1 + |ρ|) * D / s) (c₁ := c) (c₂ := d)
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hV₁pos) hs0 le_rfl hh hh₁0
    (by linarith) hgeo hC₁ hC₂
  rw [Real.coe_toNNReal V₁ hV₁pos.le, ← hRdef, ← hsdef] at hbox
  refine le_trans ?_ hbox
  -- the prefactor: its denominator is at most `e¹⁶`
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hsq1 : Real.sqrt (2 * Real.pi * V₁) ≤ 8 := by
    have hpv : Real.pi * V₁ ≤ 3.15 * 10 := mul_le_mul hpi.le hV₁u' hV₁pos.le (by norm_num)
    calc Real.sqrt (2 * Real.pi * V₁) ≤ Real.sqrt (8 ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 8 := Real.sqrt_sq (by norm_num)
  have hsq2 : Real.sqrt (2 * Real.pi) ≤ 3 := by
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt (3 ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = 3 := Real.sqrt_sq (by norm_num)
  have hsp1 : 0 < Real.sqrt (2 * Real.pi * V₁) := Real.sqrt_pos.2 (by positivity)
  have hsp2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hden0 : 0 < 32 * (1 + |ρ|) * s
      * (Real.sqrt (2 * Real.pi * V₁) * Real.sqrt (2 * Real.pi)) := by positivity
  have hden : 32 * (1 + |ρ|) * s * (Real.sqrt (2 * Real.pi * V₁) * Real.sqrt (2 * Real.pi))
      ≤ Real.exp 16 := by
    have h1 : 32 * (1 + |ρ|) * s ≤ 32 * 1001 * 4 :=
      mul_le_mul (by linarith) hs4 hs0.le (by norm_num)
    have h2 : Real.sqrt (2 * Real.pi * V₁) * Real.sqrt (2 * Real.pi) ≤ 8 * 3 :=
      mul_le_mul hsq1 hsq2 hsp2.le (by norm_num)
    have h3 : 32 * (1 + |ρ|) * s * (Real.sqrt (2 * Real.pi * V₁) * Real.sqrt (2 * Real.pi))
        ≤ 32 * 1001 * 4 * (8 * 3) := mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h16 : (3075072 : ℝ) ≤ Real.exp 16 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 16) (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    linarith
  -- the exponent: `D²/(2V₁) + C₂²/2 ≤ D²/(2v₋) + 2v₊D²/δ`
  have hE₁ : D ^ 2 / (2 * V₁) ≤ D ^ 2 / (2 * vl) :=
    div_le_div_of_nonneg_left (sq_nonneg D) (by positivity) (by linarith)
  have hE₂ : ((1 + |ρ|) * D / s) ^ 2 / 2 ≤ 2 * vu * D ^ 2 / δ := by
    have h1 := div_le_div_of_nonneg_right hC₂sq (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : 4 * vu * D ^ 2 / δ / 2 = 2 * vu * D ^ 2 / δ := by ring
    linarith
  have hexp : Real.exp (-(16 + D ^ 2 / (2 * vl) + 2 * vu * D ^ 2 / δ)) * Real.exp 16
      ≤ Real.exp (-D ^ 2 / (2 * V₁)) * Real.exp (-((1 + |ρ|) * D / s) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hneg : -D ^ 2 / (2 * V₁) = -(D ^ 2 / (2 * V₁)) := by ring
    have hneg' : -((1 + |ρ|) * D / s) ^ 2 / 2 = -(((1 + |ρ|) * D / s) ^ 2 / 2) := by ring
    rw [hneg, hneg']
    linarith
  -- the prefactor's algebra, with `1 + |ρ|` and the two roots as atoms
  have hid : ∀ t A B : ℝ, h / (8 * t) * Real.exp (-D ^ 2 / (2 * V₁)) / A
        * (h / (4 * s) * Real.exp (-((1 + |ρ|) * D / s) ^ 2 / 2) / B)
      = h ^ 2 * (Real.exp (-D ^ 2 / (2 * V₁)) * Real.exp (-((1 + |ρ|) * D / s) ^ 2 / 2))
        / (32 * t * s * (A * B)) := by
    intro t A B
    ring
  rw [hh₁def, hid (1 + |ρ|) (Real.sqrt (2 * Real.pi * V₁)) (Real.sqrt (2 * Real.pi)),
    le_div_iff₀ hden0]
  calc h ^ 2 * Real.exp (-(16 + D ^ 2 / (2 * vl) + 2 * vu * D ^ 2 / δ))
        * (32 * (1 + |ρ|) * s * (Real.sqrt (2 * Real.pi * V₁) * Real.sqrt (2 * Real.pi)))
      ≤ h ^ 2 * Real.exp (-(16 + D ^ 2 / (2 * vl) + 2 * vu * D ^ 2 / δ)) * Real.exp 16 :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ = h ^ 2 * (Real.exp (-(16 + D ^ 2 / (2 * vl) + 2 * vu * D ^ 2 / δ)) * Real.exp 16) := by
        ring
    _ ≤ h ^ 2 * (Real.exp (-D ^ 2 / (2 * V₁)) * Real.exp (-((1 + |ρ|) * D / s) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg h)

/-! ### The budget

With `E = e^{m+θ}`: the swap side is at most `e^{12-E/8}` (`RMF.blockNum_lhs_le_exp`, floor-free),
`ε_m = e^{-eE/100}`, and `e ≤ 2.7183` leaves `1/8 - e/100 ≥ 0.0978`.  So `q ≥ e^{-L}` and
`12 + L ≤ 0.0978·E` give `hnum`. -/

/-- `eE/100 + 0.0978E ≤ E/8` for `E ≥ 0`: the budget's constant `0.0978 ≤ 1/8 - e/100`. -/
lemma exp_one_mul_div_add_budget_le {E : ℝ} (hE : 0 ≤ E) :
    Real.exp 1 * E / 100 + 0.0978 * E ≤ E / 8 := by
  have he : Real.exp 1 * E ≤ 2.7183 * E :=
    mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) hE
  linarith

/-- **The budget, two-dimensional one-point form.**  If `q ≥ e^{-L}` and
`12 + L ≤ 0.0978·e^{m+θ}`, the numerical condition of the one-point box comparison holds at
`ε_m = RMF.blockEps θ m`, for variances at least `1/100` and `m + θ ≥ 0`. -/
lemma blockNum_le_of_budget {θ : ℝ} {m : ℕ} {V₁ V₂ q L : ℝ} (hmθ : 0 ≤ (m : ℝ) + θ)
    (hV₁ : 1 / 100 ≤ V₁) (hV₂ : 1 / 100 ≤ V₂) (hq : Real.exp (-L) ≤ q)
    (hbud : 12 + L ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) ≤ blockEps θ m * q := by
  have hlhs := blockNum_lhs_le_exp (θ := θ) (m := m) hmθ hV₁ hV₂
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp ((m : ℝ) + θ) := ⟨_, rfl⟩
  rw [← hEdef] at hlhs hbud
  have hE0 : 0 ≤ E := by rw [hEdef]; exact (Real.exp_pos _).le
  have hEps : blockEps θ m = Real.exp (-(Real.exp 1 * E / 100)) := by
    rw [blockEps_eq, hEdef, ← Real.exp_add]
    congr 1
    rw [show (1 : ℝ) + ((m : ℝ) + θ) = (m : ℝ) + 1 + θ by ring]
    ring
  have hb := exp_one_mul_div_add_budget_le hE0
  calc (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) ≤ Real.exp (12 - E / 8) := hlhs
    _ ≤ Real.exp (-(Real.exp 1 * E / 100) + -L) := Real.exp_le_exp.2 (by linarith)
    _ = blockEps θ m * Real.exp (-L) := by rw [hEps, Real.exp_add]
    _ ≤ blockEps θ m * q := mul_le_mul_of_nonneg_left hq (blockEps_nonneg θ m)

/-- **The budget, one-dimensional form**: `RMF.blockNum_le_of_budget` at `V₁ = V₂ = V`, whose
left side dominates `(450 + 4/√(2πV))·T^{1/4}`. -/
lemma blockNumAdd_le_of_budget {θ : ℝ} {m : ℕ} {V q L : ℝ} (hmθ : 0 ≤ (m : ℝ) + θ)
    (hV : 1 / 100 ≤ V) (hq : Real.exp (-L) ≤ q)
    (hbud : 12 + L ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    (450 + 4 / Real.sqrt (2 * Real.pi * V)) * blockTAdd θ m ^ (1 / 4 : ℝ) ≤ blockEps θ m * q := by
  refine le_trans ?_ (blockNum_le_of_budget hmθ hV hV hq hbud)
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]; exact Real.exp_pos _
  have hT0 : 0 ≤ blockTAdd θ m := (blockTAdd_pos hlogpos).le
  have hc0 : 0 ≤ 4 / Real.sqrt (2 * Real.pi * V) := by positivity
  have hq' : blockTAdd θ m ^ (1 / 4 : ℝ) ≤ (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hT0 (by linarith) (by norm_num)
  exact mul_le_mul (by linarith) hq' (Real.rpow_nonneg hT0 _) (by positivity)

/-- **The budget, two-dimensional two-fold form**, with `13` for `12`:
`RMF.blockTAdd₂^{1/4} ≤ 2(2·RMF.blockTAdd)^{1/4}` (`RMF.blockTAdd₂_rpow_le`) and `2 ≤ e`. -/
lemma blockNumAdd₂_le_of_budget {θ : ℝ} {m : ℕ} {V₁ V₂ q L : ℝ} (hmθ : 0 ≤ (m : ℝ) + θ)
    (hV₁ : 1 / 100 ≤ V₁) (hV₂ : 1 / 100 ≤ V₂) (hq : Real.exp (-L) ≤ q)
    (hbud : 13 + L ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * blockTAdd₂ θ m ^ (1 / 4 : ℝ) ≤ blockEps θ m * q := by
  have hc0 : (0 : ℝ) ≤ 3600 + 4 / Real.sqrt (2 * Real.pi * V₁)
      + 4 / Real.sqrt (2 * Real.pi * V₂) := by positivity
  have hq2 : Real.exp (-(L + 1)) ≤ q / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hsplit : Real.exp (-(L + 1)) * Real.exp 1 = Real.exp (-L) := by
      rw [← Real.exp_add]; ring_nf
    have hpos : 0 < Real.exp (-(L + 1)) := Real.exp_pos _
    nlinarith
  have h := blockNum_le_of_budget (θ := θ) (m := m) hmθ hV₁ hV₂ hq2 (by linarith)
  calc (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * blockTAdd₂ θ m ^ (1 / 4 : ℝ)
      ≤ (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * (2 * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (blockTAdd₂_rpow_le θ m) hc0
    _ = 2 * ((3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ)) := by ring
    _ ≤ 2 * (blockEps θ m * (q / 2)) := by linarith
    _ = blockEps θ m * q := by ring

/-- `Re s > 0` at offsets `θ ≥ 20`: `log x_r = e^{r+θ} ≥ e²⁰ ≥ 105`. -/
lemma le_log_blockScale_of_twenty_le {θ : ℝ} (hθ : (20 : ℝ) ≤ θ) (r : ℕ) :
    (105 : ℝ) ≤ Real.log (blockScale θ r) := by
  rw [log_blockScale]
  have h1 : (105 : ℝ) ≤ Real.exp 20 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 20)
    linarith
  exact h1.trans (Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) r]))

/-- `e^{-L₁ + log w} = w·e^{-L₁}` for a window `w > 0`: the mass in the budget's form. -/
lemma exp_neg_sub_log_eq {L w : ℝ} (hw : 0 < w) :
    Real.exp (-(L - Real.log w)) = w * Real.exp (-L) := by
  rw [show -(L - Real.log w) = Real.log w + -L by ring, Real.exp_add, Real.exp_log hw]

/-- `e^{-L₂ + 2 log w} = w²·e^{-L₂}` for a window `w > 0`. -/
lemma exp_neg_sub_two_mul_log_eq {L w : ℝ} (hw : 0 < w) :
    Real.exp (-(L - 2 * Real.log w)) = w ^ 2 * Real.exp (-L) := by
  rw [show -(L - 2 * Real.log w) = Real.log (w ^ 2) + -L by rw [Real.log_pow]; push_cast; ring,
    Real.exp_add, Real.exp_log (by positivity)]

/-! ### One dimension, one-point tilt (HP2's prefix) -/

/-- **The window comparison under the one-point tilt at offsets `θ ≥ 20`**, with the windows `w`,
the envelope `M`, the variance floor `v₋ ≥ 1/100` and the mean bound `K` as parameters, and per
block `m < r` the budget `12 + RMF.windowMassExp v₋ K (M m) - log w_m ≤ 0.0978·e^{m+θ}`.  Error
`e^{-100}`. -/
theorem exists_isWindowComparison_rademacher_budget (hX : IsRademacherPrimeValues X μ)
    {θ σ vl K : ℝ} {r y : ℕ} {s u : ℂ} {w M : ℕ → ℝ} (hθ : (20 : ℝ) ≤ θ)
    (hy : ∀ m, m < r → primeBlockSub θ m ⊆ primesBelowSub y)
    (hres : s.re = 1 / 2 + σ) (hu : u.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ r) ≤ 1)
    (hw : ∀ m, m < r → 0 < w m ∧ w m ≤ 1) (hvl : 1 / 100 ≤ vl)
    (hV : ∀ m, m < r →
      vl ≤ ((blockMatchedVarAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-u))
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-u))
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 10)
    (hK : ∀ m, m < r →
      |blockMeanAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-u)) (primeBlockSub θ m)| ≤ K)
    (hbud : ∀ m, m < r → 12 + windowMassExp vl K (M m) - Real.log (w m)
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m) = gaussianReal
        (blockGaussMeanAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) m)
        (blockGaussVarAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) m)) ∧
      ∀ k, k ≤ r → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          localLogAdd (((p : ℕ) : ℂ) ^ (-u)) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => w (m + k)) (fun m => M (m + k)) (r - k)
        (Real.exp (-100)) := by
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hσ : ∀ m, m < r → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := fun m hm =>
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (blockScale_pos θ (m + 1))
      (blockScale_mono θ (by omega))) (abs_nonneg σ)) hσtop
  have hs : 0 < s.re := by
    have h1 : |σ| * 105 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left
      (le_log_blockScale_of_twenty_le hθ r) (abs_nonneg σ)) hσtop
    rw [hres]
    linarith [neg_abs_le σ]
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_primeBlockSubAdd_of_lt hX (w := fun p => ((p : ℕ) : ℂ) ^ (-u))
      (W := w) (M := M) (T := blockTAdd θ)
      (q := fun m => w m * Real.exp (-windowMassExp vl K (M m)))
      (ε := blockEps θ) (E := Real.exp (-100) / 2) hs hy
      (fun m hm p hp => norm_prime_cpow_le_fifth (hm3 m) hu (hσ m hm) hp)
      (fun m hm p hp => norm_prime_cpow_le_fifth (hm3 m) hres (hσ m hm) hp)
      (fun m _ => blockTAdd_pos (by rw [log_blockScale]; exact Real.exp_pos _))
      (fun m hm => mul_pos (hw m hm).1 (Real.exp_pos _))
      (fun m hm h0 => by
        have h := (hV m hm).1
        rw [h0, NNReal.coe_zero] at h
        linarith)
      (fun m hm => blockThirdConstAdd_mul_sum_le (hm3 m) (hσ m hm)
        fun p _ => norm_sq_prime_cpow_neg p hu)
      (fun m hm c hc => le_toReal_measure_Ioc_gaussianReal_windowMassExp (by linarith)
        (hV m hm).1 (hV m hm).2 (hK m hm) (hw m hm).1.le (hw m hm).2 hc)
      (fun m hm => blockNumAdd_le_of_budget (by linarith [hm3 m])
        (hvl.trans (hV m hm).1) (exp_neg_sub_log_eq (hw m hm).1).le
        (by linarith [hbud m hm]))
      (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le_exp (by linarith) r)
      (by linarith [exp_neg_hundred_le_half])
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, fun k hk => ?_⟩
  have h := hcmp k hk
  rwa [show (2 : ℝ) * (Real.exp (-100) / 2) = Real.exp (-100) by ring] at h

/-- **The Gaussian walk of the comparison at offsets `θ ≥ 20`**:
`RMF.exists_isWindowComparison_rademacher_budget` centred, `G m = N m - μ_m`, with `v` the blocks'
matched variances below `r` and `1` from `r` on, so `1/100 ≤ v i ≤ 10` at every index; for HP2's
prefix. -/
theorem exists_isGaussianWalk_rademacher_budget (hX : IsRademacherPrimeValues X μ)
    {θ σ vl K : ℝ} {r y : ℕ} {s u : ℂ} {w M : ℕ → ℝ} (hθ : (20 : ℝ) ≤ θ)
    (hy : ∀ m, m < r → primeBlockSub θ m ⊆ primesBelowSub y)
    (hres : s.re = 1 / 2 + σ) (hu : u.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ r) ≤ 1)
    (hw : ∀ m, m < r → 0 < w m ∧ w m ≤ 1) (hvl : 1 / 100 ≤ vl)
    (hV : ∀ m, m < r →
      vl ≤ ((blockMatchedVarAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-u))
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-u))
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 10)
    (hK : ∀ m, m < r →
      |blockMeanAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-u)) (primeBlockSub θ m)| ≤ K)
    (hbud : ∀ m, m < r → 12 + windowMassExp vl K (M m) - Real.log (w m)
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ) (v : ℕ → ℝ≥0),
      IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
      (∀ m ω, N m ω = G m ω
        + blockGaussMeanAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) m) ∧
      (∀ i, v i = blockGaussVarAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) i) ∧
      (∀ i, 1 / 100 ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 10) ∧
      ∀ k, k ≤ r → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          localLogAdd (((p : ℕ) : ℂ) ^ (-u)) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => w (m + k)) (fun m => M (m + k)) (r - k)
        (Real.exp (-100)) := by
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_rademacher_budget hX hθ hy hres hu hσtop hw hvl hV hK hbud
  have hv : ∀ i, 1 / 100
        ≤ ((blockGaussVarAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) i : ℝ≥0) : ℝ)
      ∧ ((blockGaussVarAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) i : ℝ≥0) : ℝ)
        ≤ 10 := by
    intro i
    by_cases hi : i < r
    · rw [blockGaussVarAddLt_of_lt hi]
      exact ⟨hvl.trans (hV i hi).1, (hV i hi).2⟩
    · rw [blockGaussVarAddLt_of_le (not_lt.1 hi), NNReal.coe_one]
      constructor <;> norm_num
  exact ⟨Ω', mΩ', Q, fun m ω => N m ω
      - blockGaussMeanAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)) m, N,
    blockGaussVarAddLt X μ θ y r s (fun p => ((p : ℕ) : ℂ) ^ (-u)), hQ,
    isGaussianWalk_sub_const hNm hNi hNlaw, hNm, fun m ω => by ring, fun i => rfl,
    fun i => (hv i).1, fun i => (hv i).2, hcmp⟩

/-! ### Two dimensions, one-point tilt (HP1) -/

/-- **The per-block step of the one-point box comparison at offsets `θ ≥ 20`**, with the Gaussian
family supplied: window `0 < W ≤ 1`, corners at most `M`, variances in `[v₋, v₊]`, determinant
`≥ δ > 0`, means at most `K` and the budget
`12 + RMF.boxMassExp v₋ v₊ δ K M - 2 log W ≤ 0.0978·e^{m+θ}`. -/
theorem box_comparison_blockAdd_budget_of_family {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {G : Nat.Primes → Ω' → ℝ × ℝ}
    (hX : IsRademacherPrimeValues X μ) {θ σ W M vl vu δ K : ℝ} {m y : ℕ} {s₁ s₂ : ℂ}
    {S : Finset Nat.Primes} (hθ : (20 : ℝ) ≤ θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hW0 : 0 < W) (hWu : W ≤ 1) (hvl : 1 / 100 ≤ vl) (hvu : vu ≤ 10)
    (hV₁l : vl ≤ ((blockMatchedVarAdd X μ y s₁
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₁u : ((blockMatchedVarAdd X μ y s₁
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hV₂l : vl ≤ ((blockMatchedVarAdd X μ y s₁
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₂u : ((blockMatchedVarAdd X μ y s₁
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hδ : 0 < δ)
    (hdet : δ ≤ ((blockMatchedVarAdd X μ y s₁
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        * ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
      - blockMatchedCovAddT X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m) ^ 2)
    (hK₁ : |blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)| ≤ K)
    (hK₂ : |blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m)| ≤ K)
    (hbud : 12 + boxMassExp vl vu δ K M - 2 * Real.log W ≤ 0.0978 * Real.exp ((m : ℝ) + θ))
    (hBS : primeBlockSub θ m ⊆ S) (hSsub : S ⊆ primesBelowSub y)
    (hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5)
    (hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    (hGm : ∀ p, Measurable (G p)) (hGi : iIndepFun G Q)
    (hmom : ∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        = ∫ ω, quadMonomial j (G p ω) ∂Q)
    (hpair : ∀ p ∈ S, Q.map (G p) = gaussianPairLaw
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)) ^ 2)
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)) ^ 2)
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
          * ∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)))
    (hmarg₁ : ∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
      (matchingVar (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))))
    (hmarg₂ : ∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
      (matchingVar (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))))
    (hlawsum : Q.map (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
        ∑ p ∈ primeBlockSub θ m, (G p ω).2))
      = gaussianPairLaw
          (blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
          (blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
          ((blockMatchedVarAdd X μ y s₁
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVarAdd X μ y s₁
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCovAddT X μ y s₁
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m))) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      (1 - blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal
          ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal
        ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal
          ≤ (1 + blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hB : primeBlockSub θ m ⊆ primesBelowSub y := hBS.trans hSsub
  have hpsd := fun (p : Nat.Primes) (hp : p ∈ primeBlockSub θ m) =>
    psd_of_tiltedMeasure_moments_rademacher hX y hs₁ (hB hp)
      (hvS p (hBS hp)) (hwS p (hBS hp)) rfl rfl rfl rfl rfl
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  have hT0 : (0 : ℝ) < 2 * blockTAdd θ m := by
    have := blockTAdd_pos hlogpos
    linarith
  have hδ' : (0 : ℝ) < (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hmG : ∀ p ∈ primeBlockSub θ m, ∀ j : Fin 5,
      Integrable (fun ω => quadMonomial j (G p ω)) Q := by
    intro p hp j
    have hint : Integrable (fun z : ℝ × ℝ => quadMonomial j z) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_quadMonomial_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2 j
    exact (integrable_map_measure
      ((measurable_quadMonomial j).aestronglyMeasurable) (hGm p).aemeasurable).1 hint
  have hLG : ∀ p ∈ primeBlockSub θ m,
      Integrable (fun ω => windowLindebergBound ((2 * blockTAdd θ m) ^ (1 / 4 : ℝ)) (G p ω))
        Q := by
    intro p hp
    have hint : Integrable
        (fun z : ℝ × ℝ => windowLindebergBound ((2 * blockTAdd θ m) ^ (1 / 4 : ℝ)) z)
        (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_windowLindebergBound_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2 hδ'
    exact (integrable_map_measure
      ((measurable_windowLindebergBound _).aestronglyMeasurable)
      (hGm p).aemeasurable).1 hint
  have hG₁ : ∀ p ∈ primeBlockSub θ m, Integrable (fun ω => |(G p ω).1| ^ 3) Q := by
    intro p hp
    have hint : Integrable (fun z : ℝ × ℝ => |z.1| ^ 3) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_abs_cube_fst_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2
    exact (integrable_map_measure (by fun_prop) (hGm p).aemeasurable).1 hint
  have hG₂ : ∀ p ∈ primeBlockSub θ m, Integrable (fun ω => |(G p ω).2| ^ 3) Q := by
    intro p hp
    have hint : Integrable (fun z : ℝ × ℝ => |z.2| ^ 3) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_abs_cube_snd_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2
    exact (integrable_map_measure (by fun_prop) (hGm p).aemeasurable).1 hint
  have hNm : Measurable (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
      ∑ p ∈ primeBlockSub θ m, (G p ω).2)) :=
    (Finset.measurable_sum _ fun p _ => (hGm p).fst).prodMk
      (Finset.measurable_sum _ fun p _ => (hGm p).snd)
  -- the box mass, through the law (`RMF.le_toReal_measure_box_gaussianPairLaw_boxMassExp`)
  have hqlow : ∀ c' d' : ℝ, |c'| ≤ M → |d'| ≤ M →
      W ^ 2 * Real.exp (-boxMassExp vl vu δ K M)
        ≤ (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
          ∑ p ∈ primeBlockSub θ m, (G p ω).2))
            ⁻¹' (Set.Ioc c' (c' + W) ×ˢ Set.Ioc d' (d' + W)))).toReal := by
    intro c' d' hc' hd'
    rw [← Measure.map_apply hNm (measurableSet_Ioc.prod measurableSet_Ioc), hlawsum]
    exact le_toReal_measure_box_gaussianPairLaw_boxMassExp hvl hvu hV₁l hV₁u hV₂u hδ hdet hK₁
      hK₂ hW0 hWu hc' hd'
  have hPprob := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs₁
  intro c d hc hd
  exact le_measure_box_of_gaussian_pair_of_third_moment
    (ξ := fun p ω => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
      localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (t := primeBlockSub θ m) (T := 2 * blockTAdd θ m) (w := W) (M := M)
    (ε := blockEps θ m) (q := W ^ 2 * Real.exp (-boxMassExp vl vu δ K M))
    (fun p => ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)))
    hGm
    ((iIndepFun_tiltedMeasure_rademacher hX y hs₁).comp
      (fun p z => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun p => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    hGi hT0
    (fun p hp => integrable_quadMonomial_localLogAdd_tiltedMeasure hX _ hs₁ (hB hp)
      (hvS p (hBS hp)) (hwS p (hBS hp)))
    hmG (fun p hp => hmom p (hBS hp))
    (fun p hp => integrable_windowLindebergBound_localLogAdd_tiltedMeasure hX _ hs₁
      (hB hp) (hvS p (hBS hp)) (hwS p (hBS hp)) hδ')
    hLG
    (fun p hp => integrable_abs_cube_localLogAdd_tiltedMeasure hX _ hs₁ (hB hp)
      (hvS p (hBS hp)))
    (fun p hp => integrable_abs_cube_localLogAdd_tiltedMeasure hX _ hs₁ (hB hp)
      (hwS p (hBS hp)))
    hG₁ hG₂
    (sum_third_moment_pair_blockAdd_mixed_le hX hB hm3 hre₁ hre₂ hσ hGm
      (fun p hp => hmarg₁ p (hBS hp)) (fun p hp => hmarg₂ p (hBS hp)))
    -- `positivity` would unfold `blockMatchedVarAdd` to prove `0 ≤ ↑x`; the coercion settles it
    hlawsum (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by linarith [hdet, hδ])
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (by positivity) hqlow
    (blockNum_le_of_budget (by linarith) (by linarith) (by linarith)
      (exp_neg_sub_two_mul_log_eq hW0).le (by linarith [hbud]))
    c d hc hd

/-- **The two-dimensional box comparison under the one-point tilt at offsets `θ ≥ 20`.**

With the windows `w`, the envelope `M`, the variance bracket `[v₋, v₊]` (`1/100 ≤ v₋`,
`v₊ ≤ 10`), the per-block determinant floors `δ m > 0` and the mean bound `K` as parameters, and
per block `m < r` the budget
`12 + RMF.boxMassExp v₋ v₊ (δ m) K (M m) - 2 log w_m ≤ 0.0978·e^{m+θ}`.  One Gaussian family `N`
for every restart `k ≤ r`, error `e^{-100}`. -/
theorem exists_isBoxComparison_rademacher_budget (hX : IsRademacherPrimeValues X μ)
    {θ σ vl vu K : ℝ} {r y : ℕ} {s₁ s₂ : ℂ} {w M δ : ℕ → ℝ} (hθ : (20 : ℝ) ≤ θ)
    (hy : ∀ m, m < r → primeBlockSub θ m ⊆ primesBelowSub y)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ r) ≤ 1)
    (hw : ∀ m, m < r → 0 < w m ∧ w m ≤ 1) (hvl : 1 / 100 ≤ vl) (hvu : vu ≤ 10)
    (hV₁ : ∀ m, m < r →
      vl ≤ ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hV₂ : ∀ m, m < r →
      vl ≤ ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hδ : ∀ m, m < r → 0 < δ m)
    (hdet : ∀ m, m < r →
      δ m ≤ ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd X μ y s₁
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        - blockMatchedCovAddT X μ y s₁
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m) ^ 2)
    (hK : ∀ m, m < r →
      |blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)| ≤ K
        ∧ |blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m)| ≤ K)
    (hbud : ∀ m, m < r → 12 + boxMassExp vl vu (δ m) K (M m) - 2 * Real.log (w m)
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, m < r → Q.map (N m) = gaussianPairLaw
        (blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
        (blockMeanAdd X μ y s₁ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
        ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ((blockMatchedVarAdd X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        (blockMatchedCovAddT X μ y s₁
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m))) ∧
      ∀ k, k ≤ r → IsBoxComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
            localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
        (fun m => N (m + k)) (fun m => w (m + k)) (fun m => M (m + k)) (r - k)
        (Real.exp (-100)) := by
  classical
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hσ : ∀ m, m < r → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := fun m hm =>
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (blockScale_pos θ (m + 1))
      (blockScale_mono θ (by omega))) (abs_nonneg σ)) hσtop
  have hs₁ : 0 < s₁.re := by
    have h1 : |σ| * 105 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left
      (le_log_blockScale_of_twenty_le hθ r) (abs_nonneg σ)) hσtop
    rw [hre₁]
    linarith [neg_abs_le σ]
  -- the primes of the compared blocks, in one set, named opaquely
  obtain ⟨S, hSdef⟩ : ∃ S : Finset Nat.Primes,
      S = (Finset.range r).biUnion (primeBlockSub θ) := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, ∃ m, m < r ∧ p ∈ primeBlockSub θ m := by
    intro p hp
    rw [hSdef, Finset.mem_biUnion] at hp
    obtain ⟨m, hm, hpm⟩ := hp
    exact ⟨m, Finset.mem_range.1 hm, hpm⟩
  have hblockS : ∀ m, m < r → primeBlockSub θ m ⊆ S := by
    intro m hm p hp
    rw [hSdef, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 hm, hp⟩
  have hSsub : S ⊆ primesBelowSub y := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact hy m hm hpm
  have hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact norm_prime_cpow_le_fifth (hm3 m) hre₁ (hσ m hm) hpm
  have hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact norm_prime_cpow_le_fifth (hm3 m) hre₂ (hσ m hm) hpm
  -- one Gaussian family for the whole run
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hmom, hpair, hmarg₁, hmarg₂, hlawS⟩ :=
    exists_gaussian_pair_block_rademacher_mixed hX y hs₁ hSsub hvS hwS
  have hPprob := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs₁
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω, hQ,
    fun m => Finset.measurable_sum _ fun p _ => hGm p,
    iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ),
    fun m hm => hlawS _ (hblockS m hm), ?_⟩
  have hZi := iIndepFun_blockSumPairAdd_tiltedMeasure hX (μ := μ) y hs₁ s₂ θ
  -- each block's two-sided comparison, stated up front
  have hcmp : ∀ m, m < r → ∀ c d : ℝ, |c| ≤ M m → |d| ≤ M m →
      (1 - blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
        ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ (1 + blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal := by
    intro m hm c d hc hd
    have hBS := hblockS m hm
    have hlawsum := hlawS (primeBlockSub θ m) hBS
    rw [sum_pair_eq G (primeBlockSub θ m)] at hlawsum
    rw [sum_pair_eq G (primeBlockSub θ m),
      sum_pair_eq (fun p ω => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (primeBlockSub θ m)]
    exact box_comparison_blockAdd_budget_of_family hX hθ hre₁ hre₂ (hσ m hm) (hw m hm).1
      (hw m hm).2 hvl hvu (hV₁ m hm).1 (hV₁ m hm).2 (hV₂ m hm).1 (hV₂ m hm).2 (hδ m hm)
      (hdet m hm) (hK m hm).1 (hK m hm).2 (hbud m hm) hBS hSsub hvS hwS hGm hGi hmom hpair
      hmarg₁ hmarg₂ hlawsum c d hc hd
  intro k hkn
  -- `Z`, `N` and `w` are given, not inferred, as in the two-fold version
  have h := isBoxComparison_shift_of_indep
    (Z := fun m ω => ∑ p ∈ primeBlockSub θ m,
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (N := fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω)
    (w := w) (M := M) (ε := blockEps θ) (E := Real.exp (-100) / 2) hZi
    (iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ))
    hkn (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le_exp (by linarith) r)
    (by linarith [exp_neg_hundred_le_half]) hcmp
  rwa [show (2 : ℝ) * (Real.exp (-100) / 2) = Real.exp (-100) by ring] at h

/-! ### Two dimensions, two-fold tilt (HP2's post part) -/

/-- **The per-block step of the two-fold box comparison at offsets `θ ≥ 20`**, with the Gaussian
family supplied: window `0 < W ≤ 1`, corners at most `M`, two-fold variances in `[v₋, v₊]`,
determinant `≥ δ > 0`, means at most `K` and the budget
`13 + RMF.boxMassExp v₋ v₊ δ K M - 2 log W ≤ 0.0978·e^{m+θ}`. -/
theorem box_comparison_blockAdd₂_budget_of_family {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {G : Nat.Primes → Ω' → ℝ × ℝ}
    (hX : IsRademacherPrimeValues X μ) {θ σ W M vl vu δ K : ℝ} {m y : ℕ} {s₁ s₂ : ℂ}
    {S : Finset Nat.Primes} (hθ : (20 : ℝ) ≤ θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hW0 : 0 < W) (hWu : W ≤ 1) (hvl : 1 / 100 ≤ vl) (hvu : vu ≤ 10)
    (hV₁l : vl ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₁u : ((blockMatchedVarAdd₂ X μ y s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hV₂l : vl ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₂u : ((blockMatchedVarAdd₂ X μ y s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hδ : 0 < δ)
    (hdet : δ ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        * ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
      - blockMatchedCovAdd X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m) ^ 2)
    (hK₁ : |blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)|
      ≤ K)
    (hK₂ : |blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m)|
      ≤ K)
    (hbud : 13 + boxMassExp vl vu δ K M - 2 * Real.log W ≤ 0.0978 * Real.exp ((m : ℝ) + θ))
    (hBS : primeBlockSub θ m ⊆ S) (hSsub : S ⊆ primesBelowSub y)
    (hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5)
    (hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    (hGm : ∀ p, Measurable (G p)) (hGi : iIndepFun G Q)
    (hmom : ∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        = ∫ ω, quadMonomial j (G p ω) ∂Q)
    (hpair : ∀ p ∈ S, Q.map (G p) = gaussianPairLaw
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2)
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2)
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          * ∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)))
    (hmarg₁ : ∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      (matchingVar (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))))
    (hmarg₂ : ∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      (matchingVar (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))))
    (hlawsum : Q.map (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
        ∑ p ∈ primeBlockSub θ m, (G p ω).2))
      = gaussianPairLaw
          (blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
          (blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
          ((blockMatchedVarAdd₂ X μ y s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVarAdd₂ X μ y s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCovAdd X μ y s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m))) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      (1 - blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal
          ≤ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal
        ∧ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal
          ≤ (1 + blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + W) ×ˢ Set.Ioc d (d + W)))).toReal := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  have hB : primeBlockSub θ m ⊆ primesBelowSub y := hBS.trans hSsub
  have hpsd := fun (p : Nat.Primes) (hp : p ∈ primeBlockSub θ m) =>
    psd_of_tiltedMeasure₂_moments_rademacher hX y hs₁ hs₂ (hB hp)
      (hvS p (hBS hp)) (hwS p (hBS hp)) rfl rfl rfl rfl rfl
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  have hδ' : (0 : ℝ) < blockTAdd₂ θ m ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (blockTAdd₂_pos hlogpos) _
  have hmG : ∀ p ∈ primeBlockSub θ m, ∀ j : Fin 5,
      Integrable (fun ω => quadMonomial j (G p ω)) Q := by
    intro p hp j
    have hint : Integrable (fun z : ℝ × ℝ => quadMonomial j z) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_quadMonomial_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2 j
    exact (integrable_map_measure
      ((measurable_quadMonomial j).aestronglyMeasurable) (hGm p).aemeasurable).1 hint
  have hLG : ∀ p ∈ primeBlockSub θ m,
      Integrable (fun ω => windowLindebergBound (blockTAdd₂ θ m ^ (1 / 4 : ℝ)) (G p ω)) Q := by
    intro p hp
    have hint : Integrable
        (fun z : ℝ × ℝ => windowLindebergBound (blockTAdd₂ θ m ^ (1 / 4 : ℝ)) z)
        (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_windowLindebergBound_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2 hδ'
    exact (integrable_map_measure
      ((measurable_windowLindebergBound _).aestronglyMeasurable)
      (hGm p).aemeasurable).1 hint
  have hG₁ : ∀ p ∈ primeBlockSub θ m, Integrable (fun ω => |(G p ω).1| ^ 3) Q := by
    intro p hp
    have hint : Integrable (fun z : ℝ × ℝ => |z.1| ^ 3) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_abs_cube_fst_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2
    exact (integrable_map_measure (by fun_prop) (hGm p).aemeasurable).1 hint
  have hG₂ : ∀ p ∈ primeBlockSub θ m, Integrable (fun ω => |(G p ω).2| ^ 3) Q := by
    intro p hp
    have hint : Integrable (fun z : ℝ × ℝ => |z.2| ^ 3) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_abs_cube_snd_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2
    exact (integrable_map_measure (by fun_prop) (hGm p).aemeasurable).1 hint
  have hNm : Measurable (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
      ∑ p ∈ primeBlockSub θ m, (G p ω).2)) :=
    (Finset.measurable_sum _ fun p _ => (hGm p).fst).prodMk
      (Finset.measurable_sum _ fun p _ => (hGm p).snd)
  -- the box mass, through the law (`RMF.le_toReal_measure_box_gaussianPairLaw_boxMassExp`)
  have hqlow : ∀ c' d' : ℝ, |c'| ≤ M → |d'| ≤ M →
      W ^ 2 * Real.exp (-boxMassExp vl vu δ K M)
        ≤ (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
          ∑ p ∈ primeBlockSub θ m, (G p ω).2))
            ⁻¹' (Set.Ioc c' (c' + W) ×ˢ Set.Ioc d' (d' + W)))).toReal := by
    intro c' d' hc' hd'
    rw [← Measure.map_apply hNm (measurableSet_Ioc.prod measurableSet_Ioc), hlawsum]
    exact le_toReal_measure_box_gaussianPairLaw_boxMassExp hvl hvu hV₁l hV₁u hV₂u hδ hdet hK₁
      hK₂ hW0 hWu hc' hd'
  have hPprob := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  intro c d hc hd
  exact le_measure_box_of_gaussian_pair_of_third_moment
    (ξ := fun p ω => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
      localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (t := primeBlockSub θ m) (T := blockTAdd₂ θ m) (w := W) (M := M)
    (ε := blockEps θ m) (q := W ^ 2 * Real.exp (-boxMassExp vl vu δ K M))
    (fun p => ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)))
    hGm
    ((iIndepFun_tiltedMeasure₂_rademacher hX y hs₁ hs₂).comp
      (fun p z => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun p => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    hGi (blockTAdd₂_pos hlogpos)
    (fun p hp => integrable_quadMonomial_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hvS p (hBS hp)) (hwS p (hBS hp)))
    hmG (fun p hp => hmom p (hBS hp))
    (fun p hp => integrable_windowLindebergBound_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂
      (hB hp) (hvS p (hBS hp)) (hwS p (hBS hp)) hδ')
    hLG
    (fun p hp => integrable_abs_cube_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hvS p (hBS hp)))
    (fun p hp => integrable_abs_cube_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hwS p (hBS hp)))
    hG₁ hG₂
    (sum_third_moment_pair_blockAdd_le hX hB hm3 hre₁ hre₂ hσ hGm
      (fun p hp => hmarg₁ p (hBS hp)) (fun p hp => hmarg₂ p (hBS hp)))
    -- `positivity` would unfold `blockMatchedVarAdd₂` to prove `0 ≤ ↑x`; the coercion settles it
    hlawsum (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by linarith [hdet, hδ])
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (by positivity) hqlow
    (blockNumAdd₂_le_of_budget (by linarith) (by linarith) (by linarith)
      (exp_neg_sub_two_mul_log_eq hW0).le (by linarith [hbud]))
    c d hc hd

/-- **The two-dimensional box comparison under the two-fold tilt at offsets `θ ≥ 20`.**

With the windows `w`, the envelope `M` (any function, e.g. HP2's linear `C(b + m + 1)` at
`θ = k + b`), the two-fold variance bracket `[v₋, v₊]` (`1/100 ≤ v₋`, `v₊ ≤ 10`), the per-block
determinant floors `δ m > 0` and the mean bound `K` as parameters, and per block `m < r` the
budget `13 + RMF.boxMassExp v₋ v₊ (δ m) K (M m) - 2 log w_m ≤ 0.0978·e^{m+θ}`.  One Gaussian
family `N` for every restart `k ≤ r`, error `e^{-100}`. -/
theorem exists_isBoxComparison_rademacher_budget₂ (hX : IsRademacherPrimeValues X μ)
    {θ σ vl vu K : ℝ} {r y : ℕ} {s₁ s₂ : ℂ} {w M δ : ℕ → ℝ} (hθ : (20 : ℝ) ≤ θ)
    (hy : ∀ m, m < r → primeBlockSub θ m ⊆ primesBelowSub y)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ r) ≤ 1)
    (hw : ∀ m, m < r → 0 < w m ∧ w m ≤ 1) (hvl : 1 / 100 ≤ vl) (hvu : vu ≤ 10)
    (hV₁ : ∀ m, m < r →
      vl ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hV₂ : ∀ m, m < r →
      vl ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ vu)
    (hδ : ∀ m, m < r → 0 < δ m)
    (hdet : ∀ m, m < r →
      δ m ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd₂ X μ y s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        - blockMatchedCovAdd X μ y s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m) ^ 2)
    (hK : ∀ m, m < r →
      |blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m)| ≤ K
        ∧ |blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m)|
          ≤ K)
    (hbud : ∀ m, m < r → 13 + boxMassExp vl vu (δ m) K (M m) - 2 * Real.log (w m)
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, m < r → Q.map (N m) = gaussianPairLaw
        (blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
        (blockMeanAdd₂ X μ y s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
        ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ((blockMatchedVarAdd₂ X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        (blockMatchedCovAdd X μ y s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m))) ∧
      ∀ k, k ≤ r → IsBoxComparison
        (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
            localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
        (fun m => N (m + k)) (fun m => w (m + k)) (fun m => M (m + k)) (r - k)
        (Real.exp (-100)) := by
  classical
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hσ : ∀ m, m < r → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := fun m hm =>
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (blockScale_pos θ (m + 1))
      (blockScale_mono θ (by omega))) (abs_nonneg σ)) hσtop
  have hσ105 : |σ| * 105 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left
    (le_log_blockScale_of_twenty_le hθ r) (abs_nonneg σ)) hσtop
  have hs₁ : 0 < s₁.re := by rw [hre₁]; linarith [neg_abs_le σ]
  have hs₂ : 0 < s₂.re := by rw [hre₂]; linarith [neg_abs_le σ]
  -- the primes of the compared blocks, in one set, named opaquely
  obtain ⟨S, hSdef⟩ : ∃ S : Finset Nat.Primes,
      S = (Finset.range r).biUnion (primeBlockSub θ) := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, ∃ m, m < r ∧ p ∈ primeBlockSub θ m := by
    intro p hp
    rw [hSdef, Finset.mem_biUnion] at hp
    obtain ⟨m, hm, hpm⟩ := hp
    exact ⟨m, Finset.mem_range.1 hm, hpm⟩
  have hblockS : ∀ m, m < r → primeBlockSub θ m ⊆ S := by
    intro m hm p hp
    rw [hSdef, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 hm, hp⟩
  have hSsub : S ⊆ primesBelowSub y := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact hy m hm hpm
  have hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact norm_prime_cpow_le_fifth (hm3 m) hre₁ (hσ m hm) hpm
  have hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact norm_prime_cpow_le_fifth (hm3 m) hre₂ (hσ m hm) hpm
  -- one Gaussian family for the whole run
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hmom, hpair, hmarg₁, hmarg₂, hlawS⟩ :=
    exists_gaussian_pair_block_rademacher hX y hs₁ hs₂ hSsub hvS hwS
  have hPprob := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω, hQ,
    fun m => Finset.measurable_sum _ fun p _ => hGm p,
    iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ),
    fun m hm => hlawS _ (hblockS m hm), ?_⟩
  have hZi := iIndepFun_blockSumPairAdd_tiltedMeasure₂ hX (μ := μ) y hs₁ hs₂ θ
  -- stated up front, as in `RMF.exists_isBoxComparison_rademacher_of_range`
  have hcmp : ∀ m, m < r → ∀ c d : ℝ, |c| ≤ M m → |d| ≤ M m →
      (1 - blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
        ∧ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ (1 + blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal := by
    intro m hm c d hc hd
    have hBS := hblockS m hm
    have hlawsum := hlawS (primeBlockSub θ m) hBS
    rw [sum_pair_eq G (primeBlockSub θ m)] at hlawsum
    rw [sum_pair_eq G (primeBlockSub θ m),
      sum_pair_eq (fun p ω => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (primeBlockSub θ m)]
    exact box_comparison_blockAdd₂_budget_of_family hX hθ hre₁ hre₂ (hσ m hm) (hw m hm).1
      (hw m hm).2 hvl hvu (hV₁ m hm).1 (hV₁ m hm).2 (hV₂ m hm).1 (hV₂ m hm).2 (hδ m hm)
      (hdet m hm) (hK m hm).1 (hK m hm).2 (hbud m hm) hBS hSsub hvS hwS hGm hGi hmom hpair
      hmarg₁ hmarg₂ hlawsum c d hc hd
  intro k hkn
  -- `Z`, `N` and `w` are given, not inferred: left to unification the shift lemma unfolds
  -- `IsBoxComparison` and does not terminate in any heartbeat budget
  have h := isBoxComparison_shift_of_indep
    (Z := fun m ω => ∑ p ∈ primeBlockSub θ m,
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (N := fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω)
    (w := w) (M := M) (ε := blockEps θ) (E := Real.exp (-100) / 2) hZi
    (iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ))
    hkn (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le_exp (by linarith) r)
    (by linarith [exp_neg_hundred_le_half]) hcmp
  rwa [show (2 : ℝ) * (Real.exp (-100) / 2) = Real.exp (-100) by ring] at h

/-! ### The parameter families of HP2's prefix, HP1 and HP2's post part

The budgets on every block, for their windows `e^{-40}/(m+1)²` and linear envelopes.  With
`L(m)` quadratic in `m + 1` and the budget `0.0978·e^{m+θ}`, each family is one numerical check
at its tightest block (`RMF.sq_add_one_mul_exp_le` moves every later block onto it). -/

/-- `(n + 1)²e^{n₀} ≤ (n₀ + 1)²e^n` for `1 ≤ n₀ ≤ n`: for `n ≥ 1`, `((n+2)/(n+1))² ≤ 9/4 ≤ e`. -/
lemma sq_add_one_mul_exp_le {n₀ n : ℕ} (hn₀ : 1 ≤ n₀) (hn : n₀ ≤ n) :
    ((n : ℝ) + 1) ^ 2 * Real.exp n₀ ≤ ((n₀ : ℝ) + 1) ^ 2 * Real.exp n := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hn₀ hn
    have he : (2.25 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hstep : ((n : ℝ) + 1 + 1) ^ 2 ≤ Real.exp 1 * ((n : ℝ) + 1) ^ 2 := by
      have h1 : ((n : ℝ) + 1 + 1) ^ 2 ≤ 2.25 * ((n : ℝ) + 1) ^ 2 := by nlinarith
      have h2 := mul_le_mul_of_nonneg_right he (sq_nonneg ((n : ℝ) + 1))
      linarith
    push_cast
    calc ((n : ℝ) + 1 + 1) ^ 2 * Real.exp n₀
        ≤ Real.exp 1 * ((n : ℝ) + 1) ^ 2 * Real.exp n₀ :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
      _ = Real.exp 1 * (((n : ℝ) + 1) ^ 2 * Real.exp n₀) := by ring
      _ ≤ Real.exp 1 * (((n₀ : ℝ) + 1) ^ 2 * Real.exp n) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = ((n₀ : ℝ) + 1) ^ 2 * Real.exp ((n : ℝ) + 1) := by rw [Real.exp_add]; ring

/-- `(m + 1)²e ≤ 4e^m` for every `m`, with equality at `m = 1`. -/
lemma sq_add_one_mul_exp_one_le (m : ℕ) : ((m : ℝ) + 1) ^ 2 * Real.exp 1 ≤ 4 * Real.exp m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, zero_add, one_pow, one_mul, Real.exp_zero, mul_one]
    linarith [Real.exp_one_lt_d9]
  · have h := sq_add_one_mul_exp_le (n₀ := 1) (n := m) le_rfl hm
    norm_num at h
    linarith

/-- The windows `e^{-40}/(m+1)²` cost at most `40 + 2m` in the exponent. -/
lemma neg_log_exp_neg_forty_mul_blockWindow_le (m : ℕ) :
    -Real.log (Real.exp (-40) * blockWindow m) ≤ 40 + 2 * m := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [Real.log_mul (Real.exp_pos _).ne' (blockWindow_pos m).ne', Real.log_exp, blockWindow,
    one_div, Real.log_inv, Real.log_pow]
  have := Real.log_le_sub_one_of_pos hm1
  push_cast
  linarith

/-- `RMF.windowMassExp` at a larger corner: `L₁ ≤ 3 + D₀²/(2v₋)` for `0 ≤ M + K + 1 ≤ D₀`. -/
lemma windowMassExp_le {vl K M D₀ : ℝ} (hvl : 0 < vl) (hD : 0 ≤ M + K + 1)
    (hD₀ : M + K + 1 ≤ D₀) : windowMassExp vl K M ≤ 3 + D₀ ^ 2 / (2 * vl) := by
  rw [windowMassExp]
  have := div_le_div_of_nonneg_right (pow_le_pow_left₀ hD hD₀ 2) (by positivity : 0 ≤ 2 * vl)
  linarith

/-- `RMF.boxMassExp` at a larger corner and a smaller determinant floor:
`L₂ ≤ 16 + D₀²(1/(2v₋) + 2v₊/δ₀)` for `0 ≤ M + K + 2 ≤ D₀` and `0 < δ₀ ≤ δ`. -/
lemma boxMassExp_le {vl vu δ δ₀ K M D₀ : ℝ} (hvl : 0 < vl) (hvu : 0 ≤ vu) (hδ₀ : 0 < δ₀)
    (hδ : δ₀ ≤ δ) (hD : 0 ≤ M + K + 2) (hD₀ : M + K + 2 ≤ D₀) :
    boxMassExp vl vu δ K M ≤ 16 + D₀ ^ 2 * (1 / (2 * vl) + 2 * vu / δ₀) := by
  have hsq : (M + K + 2) ^ 2 ≤ D₀ ^ 2 := pow_le_pow_left₀ hD hD₀ 2
  have h0 : 0 ≤ 2 * vu * (M + K + 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h1 : (M + K + 2) ^ 2 / (2 * vl) ≤ D₀ ^ 2 * (1 / (2 * vl)) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hsq (by positivity)
  have h2 : 2 * vu * (M + K + 2) ^ 2 / δ ≤ D₀ ^ 2 * (2 * vu / δ₀) := by
    calc 2 * vu * (M + K + 2) ^ 2 / δ ≤ 2 * vu * (M + K + 2) ^ 2 / δ₀ :=
          div_le_div_of_nonneg_left h0 hδ₀ hδ
      _ ≤ 2 * vu * D₀ ^ 2 / δ₀ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by linarith)) hδ₀.le
      _ = D₀ ^ 2 * (2 * vu / δ₀) := by ring
  rw [boxMassExp]
  linarith

/-- **HP2's prefix budget** (one dimension): windows `e^{-40}/(m+1)²`, variance floor `1/100` and
mean bound `1.52` (`RMF.window_block_comparison_inputs_det`, `RMF.abs_window_block_means_le`),
envelope `C(m+1)` with `0 ≤ C ≤ 800`: the budget of `RMF.exists_isGaussianWalk_rademacher_budget`
on every block from `θ ≥ 20`.  The tight block is `m = 1`, where it allows `C ≤ 801.8`. -/
lemma hp2Prefix_budget {θ C : ℝ} (hθ : (20 : ℝ) ≤ θ) (hC0 : 0 ≤ C) (hC : C ≤ 800) (m : ℕ) :
    12 + windowMassExp (1 / 100) 1.52 (C * ((m : ℝ) + 1))
        - Real.log (Real.exp (-40) * blockWindow m)
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hwin := neg_log_exp_neg_forty_mul_blockWindow_le m
  have hL := windowMassExp_le (vl := 1 / 100) (K := 1.52) (M := C * ((m : ℝ) + 1))
    (D₀ := 802.52 * ((m : ℝ) + 1)) (by norm_num) (by positivity) (by nlinarith)
  have hL' : (802.52 * ((m : ℝ) + 1)) ^ 2 / (2 * (1 / 100))
      = 32201917.52 * ((m : ℝ) + 1) ^ 2 := by ring
  -- every block against the tight one: `(m + 1)²e ≤ 4e^m`
  have hX := sq_add_one_mul_exp_one_le m
  have he21 : (1318000000 : ℝ) ≤ Real.exp 21 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 21) (N := 1318000000)
      (by norm_num) (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have hY0 : 0 ≤ Real.exp (m : ℝ) := (Real.exp_pos _).le
  have hE : Real.exp (m : ℝ) * Real.exp 21 ≤ Real.exp ((m : ℝ) + θ) * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hmul : Real.exp (m : ℝ) * 1318000000 ≤ Real.exp (m : ℝ) * Real.exp 21 :=
    mul_le_mul_of_nonneg_left he21 hY0
  have hkey : 32201974.52 * ((m : ℝ) + 1) ^ 2 * Real.exp 1
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ) * Real.exp 1 := by
    nlinarith [hX, hE, hmul]
  have hfin : 32201974.52 * ((m : ℝ) + 1) ^ 2 ≤ 0.0978 * Real.exp ((m : ℝ) + θ) :=
    le_of_mul_le_mul_right hkey (Real.exp_pos 1)
  nlinarith [hL, hL', hwin, hfin]

/-- `windowBlockDet m ≥ 0.12` on every block `m ≥ 2`. -/
lemma windowBlockDet_ge_of_two_le {m : ℕ} (hm : 2 ≤ m) : (0.12 : ℝ) ≤ windowBlockDet m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  rcases j with _ | j
  · norm_num [windowBlockDet]
  · change (0.12 : ℝ) ≤ windowBlockDet (j + 3)
    norm_num [windowBlockDet]

/-- **HP1's per-block inputs for `RMF.exists_isBoxComparison_rademacher_budget`**, at
`s₁ = s_h`, `s₂ = s_0`: for `h ∈ halfWindow k`, `k ≥ 20`, `σ ≥ 0` and `σe^{k+m+1} ≤ 1/200`, both
one-point variances lie in `[1/100, 1.01]` (the closed forms `(S_m + C_m)/2` and `S_m` within
`10⁻²⁰`, `|C_m| ≤ S_m ≤ 1 + 1/150000`), `V₁V₂ − Cov² ≥ windowBlockDet m`
(`RMF.window_block_comparison_inputs_det`) and both means are at most `2.03`
(`RMF.abs_window_block_means_le`). -/
theorem window_block_comparison_inputs_budget (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          ≤ 1.01)
      ∧ (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          ≤ 1.01)
      ∧ windowBlockDet m ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        - blockMatchedCovAddT X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) ^ 2
      ∧ (|blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
            (primeBlockSub k m)| ≤ 2.03
        ∧ |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
            (primeBlockSub k m)| ≤ 2.03) := by
  have hm : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨⟨hV₁l, -⟩, ⟨hV₂l, -⟩, hdet⟩ :=
    window_block_comparison_inputs_det hX y hk hh hσ hσm hB
  obtain ⟨hMh, hMr⟩ := abs_window_block_means_le hX y hk hh hσ hσm hB
  have hV₁ := abs_le.1 (abs_blockMatchedVarAdd_height_sub_le hX y (h := h) hσ hm hB)
  have hV₂ := abs_le.1 (abs_blockMatchedVarAdd_real_sub_le hX y (h := h) hσ hm hB)
  have hS := blockRpowSum_le (θ := (k : ℝ)) (m := m) hσ (by linarith)
  have hC := (abs_le.1 (abs_blockCosSum_le_blockRpowSum (k : ℝ) σ (2 * h) m)).2
  exact ⟨⟨hV₁l, by linarith [hV₁.2]⟩, ⟨hV₂l, by linarith [hV₂.2]⟩, hdet, by linarith, hMr⟩

/-- **HP1's budget** (one-point tilt): windows `e^{-40}/(m+1)²`, variances in `[1/100, 1.01]`,
determinant floors `RMF.windowBlockDet m` and mean bound `2.03`
(`RMF.window_block_comparison_inputs_budget`), envelope `C(m+1)` with `0 ≤ C ≤ 58`: the budget of
`RMF.exists_isBoxComparison_rademacher_budget` on every block from `θ ≥ 20`.  The tight block is
`m = 0` (`δ₀ = 1.67·10⁻⁴`), where it allows `C ≤ 58.47`. -/
lemma hp1_budget {θ C : ℝ} (hθ : (20 : ℝ) ≤ θ) (hC0 : 0 ≤ C) (hC : C ≤ 58) (m : ℕ) :
    12 + boxMassExp (1 / 100) 1.01 (windowBlockDet m) 2.03 (C * ((m : ℝ) + 1))
        - 2 * Real.log (Real.exp (-40) * blockWindow m)
      ≤ 0.0978 * Real.exp ((m : ℝ) + θ) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hwin := neg_log_exp_neg_forty_mul_blockWindow_le m
  have he20 : (485000000 : ℝ) ≤ Real.exp 20 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 20) (N := 485000000)
      (by norm_num) (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have he21 : (1318000000 : ℝ) ≤ Real.exp 21 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 21) (N := 1318000000)
      (by norm_num) (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · -- block `0`: `δ₀ = 1.67·10⁻⁴`, `D ≤ 62.03`
      have hL := boxMassExp_le (vl := 1 / 100) (vu := 1.01) (δ := windowBlockDet 0)
        (δ₀ := 1.67 / 10 ^ 4) (K := 2.03) (M := C * ((0 : ℕ) + 1)) (D₀ := 62.03)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num [windowBlockDet])
        (by push_cast; linarith) (by push_cast; linarith)
      have hB := hL.trans (show (16 : ℝ) + 62.03 ^ 2 * (1 / (2 * (1 / 100))
          + 2 * 1.01 / (1.67 / 10 ^ 4)) ≤ 46733700 by norm_num)
      clear hL
      norm_num at hB hwin ⊢
      have hP : (485000000 : ℝ) ≤ Real.exp θ := he20.trans (Real.exp_le_exp.2 hθ)
      linarith
    · -- block `1`: `δ₁ = 7.76·10⁻⁴`, `D ≤ 120.03`
      have hL := boxMassExp_le (vl := 1 / 100) (vu := 1.01) (δ := windowBlockDet 1)
        (δ₀ := 7.76 / 10 ^ 4) (K := 2.03) (M := C * ((1 : ℕ) + 1)) (D₀ := 120.03)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num [windowBlockDet])
        (by push_cast; linarith) (by push_cast; linarith)
      have hB := hL.trans (show (16 : ℝ) + 120.03 ^ 2 * (1 / (2 * (1 / 100))
          + 2 * 1.01 / (7.76 / 10 ^ 4)) ≤ 38223700 by norm_num)
      clear hL
      norm_num at hB hwin ⊢
      have hP : (1318000000 : ℝ) ≤ Real.exp (1 + θ) :=
        he21.trans (Real.exp_le_exp.2 (by linarith))
      linarith
  · -- blocks `m ≥ 2`: `δ_m ≥ 0.12`, `D ≤ 60(m+1)`, and `(m+1)² ≤ 2e^m`
    have hL := boxMassExp_le (vl := 1 / 100) (vu := 1.01) (δ := windowBlockDet m)
      (δ₀ := 0.12) (K := 2.03) (M := C * ((m : ℝ) + 1)) (D₀ := 60 * ((m : ℝ) + 1))
      (by norm_num) (by norm_num) (by norm_num) (windowBlockDet_ge_of_two_le hm2)
      (by positivity) (by
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        nlinarith)
    have hL' : 16 + (60 * ((m : ℝ) + 1)) ^ 2 * (1 / (2 * (1 / 100)) + 2 * 1.01 / 0.12)
        = 16 + 240600 * ((m : ℝ) + 1) ^ 2 := by ring
    have hX : ((m : ℝ) + 1) ^ 2 ≤ 2 * Real.exp (m : ℝ) := by
      nlinarith [Real.quadratic_le_exp_of_nonneg hm0]
    have hY0 : 0 ≤ Real.exp (m : ℝ) := (Real.exp_pos _).le
    have hE : Real.exp (m : ℝ) * Real.exp 20 ≤ Real.exp ((m : ℝ) + θ) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hmul : Real.exp (m : ℝ) * 485000000 ≤ Real.exp (m : ℝ) * Real.exp 20 :=
      mul_le_mul_of_nonneg_left he20 hY0
    nlinarith [hL, hL', hwin, hX, hE, hmul]

/-- **HP2's post budget** (two-fold tilt): offset `θ ≥ 20 + b` for the post start `b ≥ 2`, windows
`e^{-40}/(j+1)²`, two-fold variances in `[0.3649, 0.6551]`, determinant floors
`RMF.pairBlockDet (j + b)` and mean bound `1.93` (`RMF.pair_block_comparison_inputs_det`,
`RMF.abs_pair_block_means_le` at the absolute block `j + b`), envelope `C(b + j + 1)` with
`0 ≤ C ≤ 770`: the budget of `RMF.exists_isBoxComparison_rademacher_budget₂` on every post block
`j`.  The tight block is `b + j = 2`, where it allows `C ≤ 771.17`. -/
lemma hp2Post_budget {θ C : ℝ} {b : ℕ} (hb : 2 ≤ b) (hθ : 20 + (b : ℝ) ≤ θ) (hC0 : 0 ≤ C)
    (hC : C ≤ 770) (j : ℕ) :
    13 + boxMassExp 0.3649 0.6551 (pairBlockDet (j + b)) 1.93 (C * ((b : ℝ) + j + 1))
        - 2 * Real.log (Real.exp (-40) * blockWindow j)
      ≤ 0.0978 * Real.exp ((j : ℝ) + θ) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hwin := neg_log_exp_neg_forty_mul_blockWindow_le j
  have he22 : (3584800000 : ℝ) ≤ Real.exp 22 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 22) (N := 3584800000)
      (by norm_num) (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  rcases (show j + b = 2 ∨ j + b = 3 ∨ 4 ≤ j + b by omega) with h2 | h3 | h4
  · -- `b + j = 2` (so `j = 0`): `δ = 0.0205`, `D ≤ 2313.93`
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ b = 2 := by omega
    have hL := boxMassExp_le (vl := 0.3649) (vu := 0.6551) (δ := pairBlockDet (0 + 2))
      (δ₀ := 0.0205) (K := 1.93) (M := C * (((2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + 1))
      (D₀ := 2313.93) (by norm_num) (by norm_num) (by norm_num) (by norm_num [pairBlockDet])
      (by push_cast; linarith) (by push_cast; linarith)
    have hB := hL.trans (show (16 : ℝ) + 2313.93 ^ 2 * (1 / (2 * 0.3649)
        + 2 * 0.6551 / 0.0205) ≤ 349540000 by norm_num)
    clear hL
    norm_num at hB hwin ⊢
    have hP : (3584800000 : ℝ) ≤ Real.exp θ :=
      he22.trans (Real.exp_le_exp.2 (by push_cast at hθ; linarith))
    linarith
  · -- `b + j = 3`: `δ = 0.1136`, `D ≤ 3083.93`, against `e^{22}`
    have hjb : (j : ℝ) + b = 3 := by exact_mod_cast h3
    have hj1 : (j : ℝ) ≤ 1 := by linarith
    have hL := boxMassExp_le (vl := 0.3649) (vu := 0.6551) (δ := pairBlockDet (j + b))
      (δ₀ := 0.1136) (K := 1.93) (M := C * ((b : ℝ) + j + 1)) (D₀ := 3083.93)
      (by norm_num) (by norm_num) (by norm_num) (by rw [h3]; norm_num [pairBlockDet])
      (by positivity) (by nlinarith)
    have hθ' : Real.exp 22 ≤ Real.exp ((j : ℝ) + θ) := Real.exp_le_exp.2 (by linarith)
    have hc : (16 : ℝ) + 3083.93 ^ 2 * (1 / (2 * 0.3649) + 2 * 0.6551 / 0.1136)
        ≤ 122722200 := by norm_num
    linarith [hL, hc, hwin, hθ', he22]
  · -- `b + j ≥ 4`: `δ = 0.0131`, `D ≤ 771(n+1)` at `n = b + j`, and `(n+1)²e⁴ ≤ 25e^n`
    set n : ℕ := j + b with hndef
    have hn : ((n : ℕ) : ℝ) = (j : ℝ) + b := by rw [hndef]; push_cast; ring
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast h4
    have hpd : pairBlockDet n = 0.0131 := by
      simp only [pairBlockDet, show n ≠ 2 by omega, show n ≠ 3 by omega, if_false]
    have hL := boxMassExp_le (vl := 0.3649) (vu := 0.6551) (δ := pairBlockDet n)
      (δ₀ := 0.0131) (K := 1.93) (M := C * ((b : ℝ) + j + 1)) (D₀ := 771 * ((n : ℝ) + 1))
      (by norm_num) (by norm_num) (by norm_num) (by rw [hpd]) (by positivity)
      (by rw [hn]; nlinarith)
    have hL' : 16 + (771 * ((n : ℝ) + 1)) ^ 2 * (1 / (2 * 0.3649) + 2 * 0.6551 / 0.0131)
        ≤ 16 + 60267800 * ((n : ℝ) + 1) ^ 2 := by
      have hc : (771 : ℝ) ^ 2 * (1 / (2 * 0.3649) + 2 * 0.6551 / 0.0131) ≤ 60267800 := by
        norm_num
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    have hX := sq_add_one_mul_exp_le (n₀ := 4) (n := n) (by norm_num) h4
    push_cast at hX
    have he24 : (26488000000 : ℝ) ≤ Real.exp 24 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 24) (N := 26488000000)
        (by norm_num) (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    have hY0 : 0 ≤ Real.exp (n : ℝ) := (Real.exp_pos _).le
    have hE : Real.exp (n : ℝ) * Real.exp 24 ≤ Real.exp ((j : ℝ) + θ) * Real.exp 4 := by
      rw [← Real.exp_add, ← Real.exp_add, hn]
      exact Real.exp_le_exp.2 (by linarith)
    have hmul : Real.exp (n : ℝ) * 26488000000 ≤ Real.exp (n : ℝ) * Real.exp 24 :=
      mul_le_mul_of_nonneg_left he24 hY0
    have hjn : (j : ℝ) ≤ n := by rw [hn]; linarith
    have hkey : 60267913 * ((n : ℝ) + 1) ^ 2 * Real.exp 4
        ≤ 0.0978 * Real.exp ((j : ℝ) + θ) * Real.exp 4 := by
      nlinarith [hX, hE, hmul]
    have hfin : 60267913 * ((n : ℝ) + 1) ^ 2 ≤ 0.0978 * Real.exp ((j : ℝ) + θ) :=
      le_of_mul_le_mul_right hkey (Real.exp_pos 4)
    nlinarith [hL, hL', hwin, hfin, hjn]

end RMF
