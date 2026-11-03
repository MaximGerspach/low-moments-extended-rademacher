/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedBounds
import RMF.Weighted.CaichUpper

/-!
# Short intervals: Caich's bound

Below `q = ½` the fractional-part sum of the extended Rademacher reduction is bounded through the
low moments of Rademacher sums over short intervals, `M(x,y) = ∑_{x<n≤x+y} X(n)`
(`RMF.shortIntervalSum`).  These are the subject of R. Caich, *Random multiplicative functions and
typical size of character in short intervals* (arXiv:2402.06426), Theorem 1.1.

`RMF.caich_upper_rademacher` is its Rademacher case, under the name the extended chain uses for
`RMF.integral_rpow_shortIntervalSum_le_caich` (`Weighted/CaichUpper.lean`, where
`RMF.shortIntervalSum` and `RMF.caichTheta` are defined).  Two departures from Caich's
formulation bear on the statement: `1/((1-q)√(log₂x))` is written `(1 + (1-q)√(log₂x))⁻¹`, which
changes the `min` by at most a factor `2` for `q < 1` and is correct at `q = 1`, where the literal
Lean transcription would be false; and "`y ≤ x` large, `θ > 0`" is `x₀ ≤ x`, `2 ≤ y ≤ x`.

`RMF.exists_integral_norm_shortIntervalSum_le` is the case consumed, `q = ½`, in the form
`E|M(s,y)| ≪ √((2√(sy) + 2y)/√(log log s))` for `2 ≤ y ≤ s`:
`θ√(log₂s) = log(s/y)/√(log₂s)`, `(1 + ½√(log₂s))⁻¹ ≤ 2/√(log₂s)`, and `log(s/y) ≤ 2√(s/y)`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! `RMF.shortIntervalSum` and `RMF.caichTheta` are defined in `Weighted/CaichUpper.lean`, beside
the proof of the theorem below. -/

/-- Caich's Theorem 1.1, Rademacher case: `RMF.integral_rpow_shortIntervalSum_le_caich`, under the
name the extended chain uses. -/
theorem caich_upper_rademacher :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x y q : ℝ, x₀ ≤ x → 2 ≤ y → y ≤ x → 0 ≤ q → q ≤ 1 →
          (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x y ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (y * min 1 (caichTheta x y * Real.sqrt (Real.log (Real.log x))
                + (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))⁻¹)) ^ q :=
  integral_rpow_shortIntervalSum_le_caich

/-- **Caich at `q = ½`, in the form consumed.**  There are `C` and `s₀` such that for every
Rademacher `X` and `2 ≤ y ≤ s` with `s ≥ s₀`, `E|M(s,y)| ≤ C·√((2√(sy) + 2y)/√(log log s))`:
`RMF.caich_upper_rademacher` at `q = ½`, the `min` bounded by its second argument,
`θ√(log log s) = log(s/y)/√(log log s)`, `(1 + ½√(log log s))⁻¹ ≤ 2/√(log log s)`, and
`y·log(s/y) ≤ 2√(sy)`. -/
theorem exists_integral_norm_shortIntervalSum_le :
    ∃ C s₀ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ s y : ℝ, s₀ ≤ s → 2 ≤ y → y ≤ s →
        (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
          ≤ C * Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y)
            / Real.sqrt (Real.log (Real.log s))) := by
  obtain ⟨C, hC, x₀, hcaich⟩ := caich_upper_rademacher (Ω := Ω)
  refine ⟨C, max x₀ (Real.exp (Real.exp 1)), hC, ?_⟩
  intro X μ hX s y hs hy2 hys
  have hs₀ : x₀ ≤ s := le_trans (le_max_left _ _) hs
  have hse : Real.exp (Real.exp 1) ≤ s := le_trans (le_max_right _ _) hs
  have hs0 : 0 < s := lt_of_lt_of_le (Real.exp_pos _) hse
  have hy0 : 0 < y := by linarith
  have hlogs : Real.exp 1 ≤ Real.log s := (Real.le_log_iff_exp_le hs0).2 hse
  have hΛ1 : 1 ≤ Real.log (Real.log s) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlogs
    rwa [Real.log_exp] at h
  have h := hcaich X μ hX s y (1 / 2) hs₀ hy2 hys (by norm_num) (by norm_num)
  have hone : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [hone, Real.rpow_one] at h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log s) := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 h ⊢
  have hΛ0 : 0 < Λ := by linarith
  have hsq0 : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  -- `θ√Λ = log(s/y)/√Λ`
  have hθ : caichTheta s y * Real.sqrt Λ = Real.log (s / y) / Real.sqrt Λ := by
    rw [caichTheta, ← hΛ, div_mul_eq_mul_div, div_eq_div_iff hΛ0.ne' hsq0.ne', mul_assoc,
      Real.mul_self_sqrt hΛ0.le]
  -- `(1 + ½√Λ)⁻¹ ≤ 2/√Λ`
  have hinv : (1 + (1 - 1 / 2) * Real.sqrt Λ)⁻¹ ≤ 2 / Real.sqrt Λ := by
    have h2 : (2 : ℝ) / Real.sqrt Λ = (Real.sqrt Λ / 2)⁻¹ := by rw [inv_div]
    rw [h2]
    exact inv_anti₀ (by linarith) (by linarith)
  -- `log(s/y) ≤ 2√(s/y)`
  have hlog : Real.log (s / y) ≤ 2 * Real.sqrt (s / y) := by
    have h1 := Real.log_le_rpow_div (div_nonneg hs0.le hy0.le) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h1
    linarith
  have hlog0 : 0 ≤ Real.log (s / y) := Real.log_nonneg ((one_le_div hy0).2 hys)
  -- `y·√(s/y) = √(sy)`
  have hsy : y * Real.sqrt (s / y) = Real.sqrt (s * y) := by
    nth_rewrite 1 [← Real.sqrt_mul_self hy0.le]
    rw [← Real.sqrt_mul (mul_self_nonneg y)]
    congr 1
    rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ s hy0.ne', mul_comm]
  have hmin0 : 0 ≤ min 1 (caichTheta s y * Real.sqrt Λ + (1 + (1 - 1 / 2) * Real.sqrt Λ)⁻¹) := by
    refine le_min zero_le_one ?_
    rw [hθ]
    exact add_nonneg (div_nonneg hlog0 hsq0.le) (inv_nonneg.2 (by linarith))
  have hkey : y * min 1 (caichTheta s y * Real.sqrt Λ + (1 + (1 - 1 / 2) * Real.sqrt Λ)⁻¹)
      ≤ (2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt Λ := by
    calc y * min 1 (caichTheta s y * Real.sqrt Λ + (1 + (1 - 1 / 2) * Real.sqrt Λ)⁻¹)
        ≤ y * (Real.log (s / y) / Real.sqrt Λ + 2 / Real.sqrt Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ hy0.le
          rw [← hθ]
          exact le_trans (min_le_right _ _) (by linarith)
      _ ≤ y * (2 * Real.sqrt (s / y) / Real.sqrt Λ + 2 / Real.sqrt Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ hy0.le
          have := div_le_div_of_nonneg_right hlog hsq0.le
          linarith
      _ = (2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt Λ := by
          rw [← hsy]
          ring
  calc (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
      ≤ C * (y * min 1 (caichTheta s y * Real.sqrt Λ
          + (1 + (1 - 1 / 2) * Real.sqrt Λ)⁻¹)) ^ (1 / 2 : ℝ) := h
    _ ≤ C * ((2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt Λ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mul_nonneg hy0.le hmin0) hkey (by norm_num)) hC.le
    _ = C * Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt Λ) := by
        rw [Real.sqrt_eq_rpow ((2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt Λ)]

end RMF
