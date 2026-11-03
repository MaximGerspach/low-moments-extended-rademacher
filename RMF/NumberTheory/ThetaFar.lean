/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.PNTThresholdExplicit

/-!
# The effective prime number theorem far out, at constant `1`

`RMF.thetaMediumConst = 10⁴⁰·20!·200²⁰ ≈ 2.6·10¹⁰⁴` is what it costs to write
`|θ x - x| ≤ 10⁴⁰ x e^{-(1/200)(\log x)^{1/10}}` as `C·x/\log² x` for every `x` past the effective
PNT's threshold: the worst case of `\log² x·e^{-(\log x)^{1/10}/200}`.  Past `\log x ≥ 10⁶⁰` the
same quantity is below `10⁻⁴⁰`, so there `C = 1` (`RMF.abs_theta_sub_le_far`, past
`RMF.thetaFarThreshold = max(RMF.thetaExpThreshold, e^{10⁶⁰})`).
-/

open Real

namespace RMF

/-- **The effective prime number theorem's threshold, pushed to `\log x ≥ 10⁶⁰`**:
`max RMF.thetaExpThreshold e^{10⁶⁰}`. -/
noncomputable def thetaFarThreshold : ℝ := max thetaExpThreshold (Real.exp (10 ^ 60))

/-- `26¹⁰⁰ ≤ e^{2500}`. -/
lemma twenty_six_pow_le_exp : (26 : ℝ) ^ 100 ≤ Real.exp 2500 := by
  have h := Real.add_one_le_exp (25 : ℝ)
  have h2 : (26 : ℝ) ^ 100 ≤ Real.exp 25 ^ 100 := pow_le_pow_left₀ (by norm_num) (by linarith) 100
  rw [← Real.exp_nat_mul] at h2
  norm_num at h2 ⊢
  exact h2

/-- **The effective prime number theorem at constant `1`**: `|θ t - t| ≤ t/\log² t` for every
`t ≥ RMF.thetaFarThreshold`.  Past `\log t ≥ 10⁶⁰`, `10⁴⁰\log² t·e^{-(\log t)^{1/10}/200}` is
below `1`: split the exponential in halves, bound one half against `\log² t` by
`RMF.sq_mul_exp_neg_rpow_tenth_le` and the other by `e^{-2500}`. -/
theorem abs_theta_sub_le_far :
    2 ≤ thetaFarThreshold ∧ ∀ t : ℝ, thetaFarThreshold ≤ t →
      |Chebyshev.theta t - t| ≤ 1 * t / Real.log t ^ 2 := by
  obtain ⟨hT2, hbound⟩ := abs_theta_sub_le_exp_numeral_explicit
  refine ⟨le_trans hT2 (le_max_left _ _), fun t ht => ?_⟩
  have htT : thetaExpThreshold ≤ t := le_trans (le_max_left _ _) ht
  have htE : Real.exp (10 ^ 60) ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos _) htE
  have hL60 : (10 : ℝ) ^ 60 ≤ Real.log t := by
    rw [← Real.log_exp (10 ^ 60)]
    exact Real.log_le_log (Real.exp_pos _) htE
  set L : ℝ := Real.log t with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL60
  -- `u = L^{1/10} ≥ 10⁶`
  have hu : (10 : ℝ) ^ 6 ≤ L ^ ((1 : ℝ) / 10) := by
    have h1 : ((10 : ℝ) ^ 60) ^ ((1 : ℝ) / 10) = 10 ^ 6 := by
      rw [show ((10 : ℝ) ^ 60) = ((10 : ℝ) ^ 6) ^ (10 : ℕ) by norm_num,
        show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hL60 (by norm_num)
  set e₁ : ℝ := Real.exp (-(1 / 400 : ℝ) * L ^ ((1 : ℝ) / 10)) with he₁def
  have he₁0 : 0 ≤ e₁ := (Real.exp_pos _).le
  have hdecay := sq_mul_exp_neg_rpow_tenth_le (c := 1 / 400) (by norm_num) hL0.le
  have hc20 : ((1 : ℝ) / 400) ^ 20 = 1 / 400 ^ (20 : ℕ) := by norm_num
  rw [hc20, div_div_eq_mul_div, div_one, ← he₁def] at hdecay
  have he₁ : e₁ ≤ Real.exp (-2500) := Real.exp_le_exp.2 (by linarith)
  have hsplit : Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)) = e₁ * e₁ := by
    rw [he₁def, ← Real.exp_add]
    congr 1
    ring
  have h26 := twenty_six_pow_le_exp
  have hkey : 10 ^ (40 : ℕ) * (L ^ 2 * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10))) ≤ 1 := by
    rw [hsplit]
    calc 10 ^ (40 : ℕ) * (L ^ 2 * (e₁ * e₁)) = 10 ^ (40 : ℕ) * (L ^ 2 * e₁) * e₁ := by ring
      _ ≤ 10 ^ (40 : ℕ) * (2432902008176640000 * 400 ^ (20 : ℕ)) * Real.exp (-2500) := by
          gcongr
      _ ≤ 26 ^ 100 * Real.exp (-2500) := by
          gcongr
          norm_num
      _ ≤ Real.exp 2500 * Real.exp (-2500) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hb := hbound t htT
  rw [← hLdef] at hb
  rw [le_div_iff₀ (by positivity)]
  calc |Chebyshev.theta t - t| * L ^ 2
      ≤ 10 ^ (40 : ℕ) * (t * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10))) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ = t * (10 ^ (40 : ℕ) * (L ^ 2 * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)))) := by
        ring
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left hkey ht0.le
    _ = 1 * t := by ring

end RMF
