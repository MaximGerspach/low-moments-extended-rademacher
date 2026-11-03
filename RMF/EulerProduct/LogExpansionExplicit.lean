/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.LogExpansion

/-!
# The local log-expansion with its constant named

The explicit twin of `RMF.exists_abs_log_sub_poly_le`: `RMF.logSubPolyConst C₀ K M₀` is
`2(K+C₀)² + C₀ + 1 + (M₀+K)/δ³` with `δ = min{1/5, 1/(2(K+C₀+1))}`.
-/

namespace RMF

/-- **The constant of the local log-expansion**: `2(K+C₀)² + C₀ + 1 + (M₀+K)/δ³` with
`δ = min{1/5, 1/(2(K+C₀+1))}`, the witness of `RMF.exists_abs_log_sub_poly_le`. -/
noncomputable def logSubPolyConst (C₀ K M₀ : ℝ) : ℝ :=
  2 * (K + C₀) ^ 2 + C₀ + 1 + (M₀ + K) / min (1 / 5) (1 / (2 * (K + C₀ + 1))) ^ 3

/-- **`RMF.exists_abs_log_sub_poly_le` at its constant** `RMF.logSubPolyConst`. -/
theorem exists_abs_log_sub_poly_le_explicit {C₀ K M₀ : ℝ} (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hM₀ : 0 ≤ M₀) :
    logSubPolyConst C₀ K M₀ > 0 ∧ ∀ I P t : ℝ, 0 ≤ t → t ≤ 1 →
      (t ≤ 1 / 5 → |I - (1 + P)| ≤ C₀ * t ^ 3) → |P| ≤ K * t ^ 2 → |Real.log I| ≤ M₀ →
      |Real.log I - P| ≤ logSubPolyConst C₀ K M₀ * t ^ 3 := by
  unfold logSubPolyConst
  set δ : ℝ := min (1 / 5) (1 / (2 * (K + C₀ + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ5 : δ ≤ 1 / 5 := min_le_left _ _
  have hδK : (K + C₀) * δ ≤ 1 / 2 := by
    have h : δ ≤ 1 / (2 * (K + C₀ + 1)) := min_le_right _ _
    calc (K + C₀) * δ ≤ (K + C₀) * (1 / (2 * (K + C₀ + 1))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  refine ⟨by positivity, ?_⟩
  intro I P t ht0 ht1 hfine hP hcrude
  refine le_mul_cube_of_two_regime hδ0 ht0 (by positivity) (by positivity) ?_ ?_
  · -- fine regime: `I` is within `1/2` of `1`, so the logarithm may be expanded
    intro hsmall
    have hIP := hfine (hsmall.trans hδ5)
    have hhalf : |I - 1| ≤ 1 / 2 := by
      have h1 := abs_le.mp hIP
      have h2 := abs_le.mp hP
      have ht2 : t ^ 2 ≤ δ := by nlinarith [mul_le_mul hsmall hsmall ht0 hδ0.le]
      have hcube : t ^ 3 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
      have hscale : (K + C₀) * t ^ 2 ≤ (K + C₀) * δ :=
        mul_le_mul_of_nonneg_left ht2 (by positivity)
      rw [abs_le]
      constructor <;> nlinarith
    have h := abs_log_sub_poly_le ht0 ht1 hC₀ hIP hP hhalf
    nlinarith [pow_nonneg ht0 3]
  · -- crude regime: the triangle inequality on `|log I| + |P|`
    have hPK : |P| ≤ K :=
      hP.trans (by nlinarith [mul_nonneg hK (by nlinarith : (0 : ℝ) ≤ 1 - t ^ 2)])
    linarith [abs_sub (Real.log I) P]

end RMF
