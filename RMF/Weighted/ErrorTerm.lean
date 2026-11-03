/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Conditional
import RMF.Weighted.Sieve

/-!
# Assembly, part 3: the smoothing error becomes `log x/√y + (log y)⁻¹`

`RMF.integral_sum_setIntegral_normSq_sub_le` bounds the error's expectation by
`∑_r 2η(η + (1+η)r/x)/r`.  Multiplying by `1/η` and summing separates the two halves:

* `2η·∑_{r∈S} 1/r`, bounded by `RMF.exists_sum_inv_rough_Ioc_le` — gives `log x/√y` at
  `η = y^{-1/2}`;
* `2(1+η)·#S/x`, bounded by `RMF.exists_roughCount_le` — gives `(log y)⁻¹`.

The threshold `y₀` is taken above `e`, so that `1 ≤ log y ≤ log x`; that is what turns
`1 + log(x/y)` into `2 log x` and absorbs the stray `1/x ≤ 1/log y` from the count.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Assembly part 3.**  The expectation of the smoothing error, at `η = y^{-1/2}`. -/
theorem exists_integral_smoothingError_le :
    ∃ C y₀ : ℝ, 0 < C ∧ 0 < y₀ ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → y₀ ≤ (y : ℝ) → (y : ℝ) ≤ x →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough y r) → (∀ r ∈ S, 1 < r) → (∀ r ∈ S, (r : ℝ) ≤ x) →
        (∫ ω, (1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 ∂μ)
          ≤ C * (Real.log x / Real.sqrt y + (Real.log y)⁻¹) := by
  classical
  obtain ⟨C₁, H₁, hC₁, -, hharm⟩ := exists_sum_inv_rough_Ioc_le
  obtain ⟨C₂, H₂, hC₂, -, hcount⟩ := exists_roughCount_le
  refine ⟨4 * C₁ + (4 + 4 * C₂), max (max H₁ H₂) (Real.exp 1), by linarith,
    lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _), ?_⟩
  intro Ω' _ X μ hX y x hy hy₀ hyx S hrough hone hle
  haveI := hX.isProbabilityMeasure
  -- basic positivity
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hy0
  have hη : (0 : ℝ) < 1 / Real.sqrt (y : ℝ) := one_div_pos.2 hs0
  have hη1 : 1 / Real.sqrt (y : ℝ) ≤ 1 := (div_le_one hs0).2 (Real.one_le_sqrt.2 (by linarith))
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hy0 hyx
  have hS0 : ∀ r ∈ S, 0 < r := fun r hr => lt_trans Nat.zero_lt_one (hone r hr)
  -- logarithms: `y₀ ≥ e` makes both `log y` and `log x` at least `1`
  have hlogy1 : (1 : ℝ) ≤ Real.log (y : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans (le_max_right _ _) hy₀)
    rwa [Real.log_exp] at h
  have hlogy0 : (0 : ℝ) < Real.log (y : ℝ) := lt_of_lt_of_le one_pos hlogy1
  have hlogx1 : (1 : ℝ) ≤ Real.log x := le_trans hlogy1 (Real.log_le_log hy0 hyx)
  have hlogyx : Real.log (y : ℝ) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hy0
    linarith
  -- (A) the harmonic mass of `S`
  have hA : ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ C₁ * (1 + Real.log (x / (y : ℝ))) / Real.log (y : ℝ) := by
    have hsub : S ⊆ {n ∈ Finset.Ioc ⌊(y : ℝ)⌋₊ ⌊x⌋₊ | IsRough y n} := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, Nat.le_floor (hle r hr)⟩, hrough r hr⟩
      rw [Nat.floor_natCast]
      exact (hrough r hr).lt_of_one_lt (hone r hr)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => inv_nonneg.2 (Nat.cast_nonneg i))) ?_
    exact hharm y (y : ℝ) x hy le_rfl
      (le_trans (le_trans (le_max_left H₁ H₂) (le_max_left _ _)) hy₀) hyx
  -- (B) the cardinality of `S`
  have hB : (S.card : ℝ) ≤ 1 + C₂ * x / Real.log (y : ℝ) := by
    have hsub : S ⊆ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n} := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨(hone r hr).le, Nat.le_floor (hle r hr)⟩, hrough r hr⟩
    have hcard : S.card ≤ roughCount y x := Finset.card_le_card hsub
    refine le_trans (by exact_mod_cast hcard) (hcount y x hy
      (le_trans (le_trans (le_max_right H₁ H₂) (le_max_left _ _)) hy₀) hyx)
  -- pull `1/η` out of the integral and insert the conditional bound
  rw [integral_const_mul]
  refine le_trans (mul_le_mul_of_nonneg_left
    (integral_sum_setIntegral_normSq_sub_le hX y hx0 hη hS0)
    (le_of_lt (one_div_pos.2 hη))) ?_
  rw [one_div_one_div]
  -- the summand splits into a harmonic and a counting half
  have hsplit : ∀ r ∈ S, Real.sqrt (y : ℝ) * (2 * (1 / Real.sqrt (y : ℝ)) *
        (1 / Real.sqrt (y : ℝ) + (1 + 1 / Real.sqrt (y : ℝ)) * (r : ℝ) / x) / (r : ℝ))
      = 2 * (1 / Real.sqrt (y : ℝ)) * ((r : ℝ))⁻¹ + 2 * (1 + 1 / Real.sqrt (y : ℝ)) / x := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS0 r hr
    field_simp
    try ring
  have hcong : (∑ r ∈ S, Real.sqrt (y : ℝ) * (2 * (1 / Real.sqrt (y : ℝ)) *
        (1 / Real.sqrt (y : ℝ) + (1 + 1 / Real.sqrt (y : ℝ)) * (r : ℝ) / x) / (r : ℝ)))
      = ∑ r ∈ S, (2 * (1 / Real.sqrt (y : ℝ)) * ((r : ℝ))⁻¹
          + 2 * (1 + 1 / Real.sqrt (y : ℝ)) / x) :=
    Finset.sum_congr rfl hsplit
  rw [Finset.mul_sum, hcong, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  -- half 1: `2η·∑1/r ≤ 4C₁·log x/√y`
  have half1 : 2 * (1 / Real.sqrt (y : ℝ)) * (∑ r ∈ S, ((r : ℝ))⁻¹)
      ≤ 4 * C₁ * (Real.log x / Real.sqrt (y : ℝ)) := by
    have hstep : ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ 2 * C₁ * Real.log x := by
      refine le_trans hA ?_
      rw [div_le_iff₀ hlogy0]
      have hnum : Real.log (x / (y : ℝ)) ≤ Real.log x := by
        rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hy0)]
        linarith
      have h1 : C₁ * (1 + Real.log (x / (y : ℝ))) ≤ C₁ * (2 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith) hC₁.le
      have hpos : (0 : ℝ) ≤ 2 * C₁ * Real.log x :=
        mul_nonneg (mul_nonneg (by norm_num) hC₁.le) (by linarith)
      have h2 : 2 * C₁ * Real.log x ≤ 2 * C₁ * Real.log x * Real.log (y : ℝ) :=
        le_mul_of_one_le_right hpos hlogy1
      linarith
    calc 2 * (1 / Real.sqrt (y : ℝ)) * (∑ r ∈ S, ((r : ℝ))⁻¹)
        ≤ 2 * (1 / Real.sqrt (y : ℝ)) * (2 * C₁ * Real.log x) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 4 * C₁ * (Real.log x / Real.sqrt (y : ℝ)) := by ring
  -- half 2: `2(1+η)·#S/x ≤ (4+4C₂)/log y`
  have half2 : (S.card : ℝ) * (2 * (1 + 1 / Real.sqrt (y : ℝ)) / x)
      ≤ (4 + 4 * C₂) * (Real.log (y : ℝ))⁻¹ := by
    have hwid : 2 * (1 + 1 / Real.sqrt (y : ℝ)) / x ≤ 4 / x := by
      rw [div_le_div_iff₀ hx0 hx0]
      exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
    have hstep1 : (S.card : ℝ) * (2 * (1 + 1 / Real.sqrt (y : ℝ)) / x)
        ≤ (1 + C₂ * x / Real.log (y : ℝ)) * (4 / x) := by
      refine mul_le_mul hB hwid ?_ ?_
      · exact div_nonneg (by linarith) hx0.le
      · exact le_trans (Nat.cast_nonneg S.card) hB
    have hstep2 : (1 + C₂ * x / Real.log (y : ℝ)) * (4 / x)
        = 4 / x + 4 * C₂ / Real.log (y : ℝ) := by
      field_simp
      try ring
    have hstep3 : 4 / x ≤ 4 / Real.log (y : ℝ) := by
      rw [div_le_div_iff₀ hx0 hlogy0]
      exact mul_le_mul_of_nonneg_left hlogyx (by norm_num)
    have hstep4 : 4 / Real.log (y : ℝ) + 4 * C₂ / Real.log (y : ℝ)
        = (4 + 4 * C₂) * (Real.log (y : ℝ))⁻¹ := by
      field_simp
      try ring
    linarith
  -- assemble
  have hp1 : (0 : ℝ) ≤ Real.log x / Real.sqrt (y : ℝ) :=
    div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hp2 : (0 : ℝ) ≤ (Real.log (y : ℝ))⁻¹ := inv_nonneg.2 hlogy0.le
  have h6 : (0 : ℝ) ≤ 4 * C₁ * (Real.log (y : ℝ))⁻¹ := mul_nonneg (by linarith) hp2
  have h7 : (0 : ℝ) ≤ (4 + 4 * C₂) * (Real.log x / Real.sqrt (y : ℝ)) :=
    mul_nonneg (by linarith) hp1
  have hexpand : (4 * C₁ + (4 + 4 * C₂))
        * (Real.log x / Real.sqrt (y : ℝ) + (Real.log (y : ℝ))⁻¹)
      = (4 * C₁ * (Real.log x / Real.sqrt (y : ℝ)) + (4 + 4 * C₂) * (Real.log (y : ℝ))⁻¹)
        + (4 * C₁ * (Real.log (y : ℝ))⁻¹ + (4 + 4 * C₂) * (Real.log x / Real.sqrt (y : ℝ))) := by
    ring
  rw [hexpand]
  linarith

end RMF
