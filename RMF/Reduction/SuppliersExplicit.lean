/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.Suppliers
import RMF.NumberTheory.CosinePrimeSumExplicit

/-!
# The reduction's suppliers with their constants named

Named constants for the statements of `RMF/Reduction/Suppliers.lean` that Harper's theorem uses:
the sieve bound's constant `RMF.roughCountConst = 3`, and Rankin's bound at its constants
(`RMF.exists_smoothCount_le_explicit`, with `RMF.smoothCountExponent`, `RMF.smoothCountDecay = 1/4`
and `RMF.smoothCountConst`).  The numerals are named so that a proof can `set` them without
capturing an unrelated `3` or `1/4`.
-/

namespace RMF

/-- **The constant of the sieve bound**, `3`. -/
noncomputable def roughCountConst : ℝ := 3

/-- **The exponent of `log y` in Rankin's bound**, `6e^{1/4}`. -/
noncomputable def smoothCountExponent : ℝ := 6 * Real.exp (1 / 4)

/-- **The decay constant of Rankin's bound**, `1/4`. -/
noncomputable def smoothCountDecay : ℝ := 1 / 4

/-- **The constant of Rankin's bound**, `exp(6e^{1/4}·primesBelowInvLogLogConst)`. -/
noncomputable def smoothCountConst : ℝ :=
  Real.exp (6 * Real.exp (1 / 4) * primesBelowInvLogLogConst)

/-- **`RMF.exists_smoothCount_le` at its constants**: `A = 6e^{1/4}`, `c = 1/4` and
`C = exp(6e^{1/4}·primesBelowInvLogLogConst)`. -/
theorem exists_smoothCount_le_explicit :
    0 ≤ smoothCountExponent ∧ 0 < smoothCountDecay ∧ 0 < smoothCountConst ∧
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → 2 ≤ x →
        (smoothCount y x : ℝ)
          ≤ smoothCountConst * x * Real.log y ^ smoothCountExponent
            * Real.exp (-smoothCountDecay * Real.log x / Real.log y) := by
  unfold smoothCountConst smoothCountExponent smoothCountDecay
  obtain ⟨hCM0, hM⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le_explicit
  set CM := primesBelowInvLogLogConst with hCMdef
  refine ⟨by positivity, by norm_num, Real.exp_pos _, ?_⟩
  intro y x hy hx
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hl2 : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hyR
  have hLy0 : (0 : ℝ) < Real.log y := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set σ : ℝ := 1 - (1 / 4) / Real.log y with hσdef
  have hquart : (1 / 4 : ℝ) / Real.log y ≤ (1 / 4) / Real.log 2 := by
    gcongr
  have hq2 : (1 / 4 : ℝ) / Real.log 2 < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hσ0 : (1 / 2 : ℝ) < σ := by
    rw [hσdef]
    linarith
  have hσpos : (0 : ℝ) < σ := by linarith
  -- every local factor is well inside the range where `(1-t)⁻¹ ≤ e^{6t}` applies
  have hb : ∀ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-σ) ≤ 9 / 10 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hstep : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hexp : (2 : ℝ) ^ (-σ) = Real.exp (-(σ * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    have hpos : (0 : ℝ) < 1 + σ * Real.log 2 := by nlinarith
    have hinv : Real.exp (-(σ * Real.log 2)) ≤ (1 + σ * Real.log 2)⁻¹ := by
      rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hpos]
      linarith [Real.add_one_le_exp (σ * Real.log 2)]
    have hfin : (1 + σ * Real.log 2)⁻¹ ≤ 9 / 10 := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    rw [hexp] at hstep
    linarith
  -- Rankin, the Euler product, and the exponential bound
  have hmert : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ ≤ Real.log (Real.log y) + CM := by
    have := abs_le.1 (hM y hy)
    linarith [this.2]
  have hchain : (smoothCount y x : ℝ)
      ≤ x ^ σ * Real.exp (6 * (Real.exp (1 / 4) * (Real.log (Real.log y) + CM))) := by
    refine le_trans (smoothCount_le_rpow_mul_tsum y hσpos (by linarith)) ?_
    rw [tsum_smoothNumbers_rpow_eq y hσpos]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
    refine le_trans (prod_inv_one_sub_le_exp hb) (Real.exp_le_exp.2 ?_)
    have hsum := sum_rpow_neg_sigma_le (c := 1 / 4) hy (by norm_num)
    have hcast : ∀ p : ℕ, (p : ℝ) ^ (-(1 - (1 / 4) / Real.log y)) = (p : ℝ) ^ (-σ) := by
      intro p
      rw [hσdef]
    simp only [hcast] at hsum
    have hE : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
    nlinarith [hsum, hmert, hE]
  -- unwind the constants
  have hxs : x ^ σ = x * Real.exp (-(1 / 4) * Real.log x / Real.log y) := by
    rw [Real.rpow_def_of_pos hx0, hσdef,
      show Real.log x * (1 - (1 / 4) / Real.log y)
        = Real.log x + -(1 / 4) * Real.log x / Real.log y by field_simp; ring,
      Real.exp_add, Real.exp_log hx0]
  have hloglog : Real.exp (6 * Real.exp (1 / 4) * Real.log (Real.log y))
      = Real.log y ^ (6 * Real.exp (1 / 4)) := by
    rw [Real.rpow_def_of_pos hLy0]
    congr 1
    ring
  refine le_trans hchain (le_of_eq ?_)
  rw [hxs, show (6 : ℝ) * (Real.exp (1 / 4) * (Real.log (Real.log y) + CM))
      = 6 * Real.exp (1 / 4) * Real.log (Real.log y) + 6 * Real.exp (1 / 4) * CM by ring,
    Real.exp_add, hloglog]
  ring

end RMF
