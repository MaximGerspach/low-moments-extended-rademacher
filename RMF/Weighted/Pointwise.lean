/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Conditional
import RMF.Weighted.Sieve

/-!
# Assembly, part 1: the smoothing bound at `η = y^(-1/2)`

`RMF.sum_weightedRoughTerm_le_setIntegral` takes four side conditions.  Here they are discharged
at `η = y^(-1/2)`, with `T = [y, x(1+η)]` and `b` the sieve bound of
`RMF.exists_sum_inv_sq_indicator_le_sqrt`:

* `hsub` — roughness puts every `r ∈ S` above `y`, and `r ≤ x`, so `[r, r(1+η)] ⊆ T`;
* `hb` — the sieve, which needs `t ≥ y`, and `t ∈ T` gives exactly that;
* `hint`, `hintT` — both integrands are bounded on `T` (`‖A_y(x/t)‖ ≤ x/y` there) and `T` is
  bounded (`RMF.integrableOn_sieveShape_of_bound`, stated for any function bounded above the
  left end of `T`; the band tail of the truncation bound, `RMF/Weighted/BandTailSmoothing.lean`,
  reuses it).
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The smoothing's integrability conditions against the sieve's shape**, for any function
bounded above `a`.  With `b(t) = C(1+η)²(tη/(1+η)+1)/(t²L)` and `‖G(x/t)‖ ≤ K` for `t ≥ a`, the two
integrands `RMF.sum_inv_mul_normSq_le_setIntegral` asks to be integrable on `T = [a, s]` are
bounded there: the windowed one by `K²/r²`, the principal one by `K²·C(1+η)²(η/a + 1/a²)/L`, since
`tη/(1+η) ≤ tη` and `t ≥ a`.  The head's `RMF.exists_sum_weightedRoughTerm_le_sqrt` uses it at
`G = A_y`, `a = y`, `K = x/y`; the band tail `RMF.blockTailSum` at `K = z#`. -/
theorem integrableOn_sieveShape_of_bound {G : ℝ → ℂ} (hG : Measurable G) {x η a s K C L : ℝ}
    (hη : 0 < η) (ha : 0 < a) (hC : 0 < C) (hL : 0 < L)
    (hK : ∀ t : ℝ, a ≤ t → ‖G (x / t)‖ ≤ K) :
    (∀ r : ℕ, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun t => ‖G (x / t)‖ ^ 2) t)
        (Set.Icc a s) volume)
      ∧ IntegrableOn (fun t => ‖G (x / t)‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L))) (Set.Icc a s) volume := by
  have hden : (0 : ℝ) < 1 + η := by linarith
  have hsq : ∀ t : ℝ, a ≤ t → ‖G (x / t)‖ ^ 2 ≤ K ^ 2 := fun t ht =>
    pow_le_pow_left₀ (norm_nonneg _) (hK t ht) 2
  have hmeasA : Measurable fun t : ℝ => ‖G (x / t)‖ ^ 2 :=
    (hG.comp (measurable_const.div measurable_id)).norm.pow_const 2
  -- the sieve's shape is nonnegative on `t ≥ a`, …
  have hbnn : ∀ t : ℝ, a ≤ t →
      (0 : ℝ) ≤ C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht
    have hnum : (0 : ℝ) ≤ t * η / (1 + η) + 1 := by
      have := div_nonneg (mul_nonneg ht0.le hη.le) hden.le
      linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) hnum)
      (mul_nonneg (sq_nonneg _) hL.le)
  -- … and bounded there, since `tη/(1+η) ≤ tη` and `t ≥ a`
  have hbbnd : ∀ t : ℝ, a ≤ t → C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L)
      ≤ C * (1 + η) ^ 2 * (η / a + 1 / a ^ 2) / L := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht
    have ht0' : t ≠ 0 := ne_of_gt ht0
    have hd : t * η / (1 + η) ≤ t * η := div_le_self (mul_nonneg ht0.le hη.le) (by linarith)
    have h1 : (t * η / (1 + η) + 1) / t ^ 2 ≤ (t * η + 1) / t ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
    have h2 : (t * η + 1) / t ^ 2 = η / t + 1 / t ^ 2 := by
      field_simp
      try ring
    have h3 : η / t ≤ η / a := div_le_div_of_nonneg_left hη.le ha ht
    have h4 : 1 / t ^ 2 ≤ 1 / a ^ 2 :=
      one_div_le_one_div_of_le (pow_pos ha 2) (pow_le_pow_left₀ ha.le ht 2)
    rw [h2] at h1
    have hkey : (t * η / (1 + η) + 1) / t ^ 2 ≤ η / a + 1 / a ^ 2 := by linarith
    have hfac : (0 : ℝ) ≤ C * (1 + η) ^ 2 / L :=
      div_nonneg (mul_nonneg hC.le (sq_nonneg _)) hL.le
    have hfactor : C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L)
        = C * (1 + η) ^ 2 / L * ((t * η / (1 + η) + 1) / t ^ 2) := by
      ring
    rw [hfactor]
    exact le_trans (mul_le_mul_of_nonneg_left hkey hfac) (le_of_eq (by ring))
  refine ⟨fun r => ?_, ?_⟩
  · refine Measure.integrableOn_of_bounded (M := (((r : ℝ)) ^ 2)⁻¹ * K ^ 2)
      measure_Icc_lt_top.ne
      ((hmeasA.indicator measurableSet_Icc).const_mul _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hrinv : (0 : ℝ) ≤ (((r : ℝ)) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hIle : (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
        (fun t => ‖G (x / t)‖ ^ 2) t ≤ K ^ 2 := by
      by_cases hmem : t ∈ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))
      · rw [Set.indicator_of_mem hmem]
        exact hsq t ht.1
      · rw [Set.indicator_of_notMem hmem]
        exact sq_nonneg _
    have hI0 : (0 : ℝ) ≤ (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
        (fun t => ‖G (x / t)‖ ^ 2) t := by
      by_cases hmem : t ∈ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))
      · rw [Set.indicator_of_mem hmem]
        exact sq_nonneg _
      · rw [Set.indicator_of_notMem hmem]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrinv hI0)]
    exact mul_le_mul_of_nonneg_left hIle hrinv
  · have hmeasb : Measurable fun t : ℝ =>
        C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L) := by
      fun_prop
    refine Measure.integrableOn_of_bounded
      (M := K ^ 2 * (C * (1 + η) ^ 2 * (η / a + 1 / a ^ 2) / L))
      measure_Icc_lt_top.ne (hmeasA.mul hmeasb).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hbnn t ht.1))]
    exact mul_le_mul (hsq t ht.1) (hbbnd t ht.1) (hbnn t ht.1) (sq_nonneg _)

/-- **Assembly part 1.**  The rough sum is at most the principal term plus the smoothing error,
at `η = y^(-1/2)`.  The constant `C` is the sieve's, and is passed to
`RMF.exists_setIntegral_normSq_mul_sieve_le`, which quantifies over it. -/
theorem exists_sum_weightedRoughTerm_le_sqrt :
    ∃ C y₀ : ℝ, 0 < C ∧ 0 < y₀ ∧
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → y₀ ≤ (y : ℝ) → (y : ℝ) ≤ x →
      ∀ (Ω' : Type*) (f : Ω' → ArithmeticFunction ℂ) (ω : Ω'), (∀ n, ‖f ω n‖ ≤ 1) →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough y r) → (∀ r ∈ S, 1 < r) → (∀ r ∈ S, (r : ℝ) ≤ x) →
        ∑ r ∈ S, weightedRoughTerm f y x ω r
          ≤ (2 / (1 / Real.sqrt y)) * (∫ t in Set.Icc ((y : ℝ)) (x * (1 + 1 / Real.sqrt y)),
                ‖smoothWeightedSum f y (x / t) ω‖ ^ 2
                  * (C * (1 + 1 / Real.sqrt y) ^ 2
                      * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)
                      / (t ^ 2 * Real.log y)))
            + (1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
                (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
                  ‖smoothWeightedSum f y (x / r) ω
                    - smoothWeightedSum f y (x / t) ω‖ ^ 2)) / ((r : ℝ)) ^ 2 := by
  obtain ⟨C, y₀, hC, hy₀, hsieve⟩ := exists_sum_inv_sq_indicator_le_sqrt
  refine ⟨C, y₀, hC, hy₀, ?_⟩
  intro y x hy2 hy0 hyx Ω' f ω hbnd S hrough hone hSx
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hypos hyx
  have hsq : (0 : ℝ) < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  have hη : (0 : ℝ) < 1 / Real.sqrt (y : ℝ) := div_pos one_pos hsq
  have hden : (0 : ℝ) < 1 + 1 / Real.sqrt (y : ℝ) := by linarith
  have hlogy : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hS : ∀ r ∈ S, 0 < r := fun r hr => lt_trans Nat.zero_lt_one (hone r hr)
  -- On `t ≥ y` the smooth sum is bounded by `⌊x/t⌋₊ ≤ x/y`.
  have hAle : ∀ t : ℝ, (y : ℝ) ≤ t → ‖smoothWeightedSum f y (x / t) ω‖ ≤ x / (y : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hypos ht
    refine le_trans (norm_smoothWeightedSum_le_of_bound hbnd y (x / t)) ?_
    refine le_trans (Nat.floor_le (div_nonneg hxpos.le ht0.le)) ?_
    exact div_le_div_of_nonneg_left hxpos.le hypos ht
  -- `hsub`: roughness puts `r` above `y`, and `r ≤ x` scales up.
  have hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt (y : ℝ)))
      ⊆ Set.Icc ((y : ℝ)) (x * (1 + 1 / Real.sqrt (y : ℝ))) := by
    intro r hr t ht
    have hyr : (y : ℝ) < (r : ℝ) := by
      exact_mod_cast (hrough r hr).lt_of_one_lt (hone r hr)
    exact ⟨le_trans hyr.le ht.1,
      le_trans ht.2 (mul_le_mul_of_nonneg_right (hSx r hr) hden.le)⟩
  -- `hb`: the sieve, at `t ≥ y`.
  have hbT : ∀ t ∈ Set.Icc ((y : ℝ)) (x * (1 + 1 / Real.sqrt (y : ℝ))),
      ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
          * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt (y : ℝ)))).indicator
              (fun _ => (1 : ℝ)) t
        ≤ C * (1 + 1 / Real.sqrt (y : ℝ)) ^ 2
            * (t * (1 / Real.sqrt (y : ℝ)) / (1 + 1 / Real.sqrt (y : ℝ)) + 1)
            / (t ^ 2 * Real.log (y : ℝ)) :=
    fun t ht => hsieve y S hrough hy2 hy0 t ht.1
  -- `hint`, `hintT`: both integrands are bounded on `T`, where `‖A_y(x/t)‖ ≤ x/y`
  obtain ⟨hint, hintT⟩ := integrableOn_sieveShape_of_bound
    (measurable_smoothWeightedSum_truncation f y ω) (s := x * (1 + 1 / Real.sqrt (y : ℝ)))
    hη hypos hC hlogy hAle
  exact sum_weightedRoughTerm_le_setIntegral
    (T := Set.Icc ((y : ℝ)) (x * (1 + 1 / Real.sqrt (y : ℝ))))
    (b := fun t => C * (1 + 1 / Real.sqrt (y : ℝ)) ^ 2
      * (t * (1 / Real.sqrt (y : ℝ)) / (1 + 1 / Real.sqrt (y : ℝ)) + 1)
      / (t ^ 2 * Real.log (y : ℝ)))
    hbnd y hxpos.le hη hS measurableSet_Icc hsub hbT (fun r _ => hint r) hintT

end RMF
