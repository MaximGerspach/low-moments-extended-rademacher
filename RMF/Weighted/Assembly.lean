/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Pointwise
import RMF.Weighted.Principal
import RMF.Weighted.ErrorTerm
import RMF.Weighted.EulerLine

/-!
# Assembly, part 4: combining the principal term and the error

For `0 < q ≤ 1` and `Z = (log y)⁻¹ ∫_ℝ |F_y(½+σ+it)/(σ+it)|² dt`,
`E[(∑_r weightedRoughTerm)^q] ≤ C·(E[Z^q] + (log x/√y + (log y)⁻¹)^q)`, with `C` and `y₀`
absolute (`RMF.exists_integral_rpow_sum_weightedRoughTerm_le`).

The smoothing (`RMF.exists_sum_weightedRoughTerm_le_sqrt`) and the principal term
(`RMF.exists_setIntegral_normSq_mul_sieve_le`) give, for a.e. `ω`,
`∑_r weightedRoughTerm ≤ K·C·Z(ω) + Err(ω)`, and `RMF.exists_integral_smoothingError_le` gives
`E[Err] ≤ C₃·(log x/√y + (log y)⁻¹)`.  Raising to the `q`-th power is subadditive
(`RMF.rpow_sum_le_sum_rpow`), and integrating splits the two.  The principal half is `E[Z^q]`,
integrable by `RMF.integrable_rpow_eulerProductLine`.  The error half is bounded **only in
expectation**, so Jensen (`RMF.integral_rpow_le_rpow_integral_of_bound`) carries it.

**Uniformity in `q`** comes from `RMF.rpow_le_max_one`: `a^q ≤ max 1 a` for `0 < q ≤ 1`, so the
constants `(KC)^q` and `C₃^q` are absorbed into a single `q`-free constant.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`volume.restrict` does not distinguish `Icc` from `Ioc`**: the two sets differ by a null
set.  Stated as an equality of measures, so that it is a first-order rewrite. -/
theorem restrict_Icc_eq_Ioc (a b : ℝ) :
    volume.restrict (Set.Icc a b) = volume.restrict (Set.Ioc a b) :=
  (MeasureTheory.Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))).symm

/-- The `Icc` form of `RMF.integrable_setIntegral_normSq_sub`, which the smoothing error needs. -/
theorem integrable_setIntegral_normSq_sub_Icc {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r s : ℝ}
    (hx : 0 ≤ x) (hr : 0 < r) :
    Integrable (fun ω => ∫ t in Set.Icc r s,
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2)
      μ := by
  simp only [restrict_Icc_eq_Ioc]
  exact integrable_setIntegral_normSq_sub hX y hx hr

/-! ### The smoothing error as a random variable

Both halves of the combination need the error to be integrable and nonnegative. -/

/-- **The smoothing error is integrable.** -/
theorem integrable_smoothingError {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x : ℝ} (hx : 0 ≤ x)
    {S : Finset ℕ} (hone : ∀ r ∈ S, 1 < r) :
    Integrable (fun ω => (1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2) μ := by
  classical
  refine (integrable_finsetSum S fun r hr => ?_).const_mul _
  have hr0 : (0 : ℝ) < r := by exact_mod_cast lt_trans Nat.zero_lt_one (hone r hr)
  exact ((integrable_setIntegral_normSq_sub_Icc hX y hx hr0).const_mul 2).div_const _

omit [MeasurableSpace Ω] in
/-- **The smoothing error is nonnegative.** -/
theorem smoothingError_nonneg {X : ℕ → Ω → ℂ} (y : ℕ) (x : ℝ) (S : Finset ℕ) (ω : Ω) :
    (0 : ℝ) ≤ (1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2 := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => ?_)
  refine div_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
  exact setIntegral_nonneg measurableSet_Icc fun t _ => by positivity

/-- **The error half of the assembly.**  `E[Err^q] ≤ C·(log x/√y + (log y)⁻¹)^q` for `0 ≤ q ≤ 1`:
`RMF.exists_integral_smoothingError_le` bounds the error's *mean*, Jensen carries that to the
`q`-th moment, and `RMF.rpow_le_max_one` makes the constant `q`-free.  The space, the family and
the measure are quantified **inside** the existential, so `C` and `y₀` are absolute, as
`RMF.exists_integral_rpow_weightedRademacherSum_le` needs. -/
theorem exists_integral_rpow_smoothingError_le :
    ∃ C y₀ : ℝ, 0 < C ∧ 0 < y₀ ∧
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → y₀ ≤ (y : ℝ) → (y : ℝ) ≤ x →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough y r) → (∀ r ∈ S, 1 < r) → (∀ r ∈ S, (r : ℝ) ≤ x) →
        (∫ ω, ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2) ^ q ∂μ)
          ≤ C * (Real.log x / Real.sqrt y + (Real.log y)⁻¹) ^ q := by
  classical
  obtain ⟨C₃, y₃, hC₃, hy₃, herr⟩ := exists_integral_smoothingError_le
  refine ⟨max 1 C₃, y₃, lt_of_lt_of_le one_pos (le_max_left 1 C₃), hy₃, ?_⟩
  intro q hq0 hq1 Ω' _ X μ hX y x hy hy₀ hyx S hrough hone hle
  haveI := hX.isProbabilityMeasure
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx0 : (0 : ℝ) ≤ x := le_trans (by linarith) hyx
  refine le_trans (integral_rpow_le_rpow_of_integral_le hq0 hq1
    (Filter.Eventually.of_forall (smoothingError_nonneg (X := X) y x S))
    (integrable_smoothingError hX y hx0 hone)
    (herr Ω' X μ hX y x hy hy₀ hyx S hrough hone hle)) ?_
  have hL : (0 : ℝ) ≤ Real.log x / Real.sqrt y + (Real.log y)⁻¹ := by
    have h1 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ (Real.log y)⁻¹ := inv_nonneg.2 (Real.log_nonneg (by linarith))
    positivity
  rw [Real.mul_rpow hC₃.le hL]
  exact mul_le_mul_of_nonneg_right (rpow_le_max_one hC₃ hq0 hq1) (Real.rpow_nonneg hL q)

/-- **Assembly part 4: the combination.**
`E[(∑_r weightedRoughTerm)^q] ≤ C·(E[Z^q] + (log x/√y + (log y)⁻¹)^q)`, `C` and `y₀` absolute.
Almost everywhere `∑_r weightedRoughTerm ≤ K·C·Z(ω) + Err(ω)`; subadditivity of `t ↦ t^q` splits
the `q`-th power, and `RMF.rpow_le_max_one` absorbs `(K·C)^q` into a `q`-free constant. -/
theorem exists_integral_rpow_sum_weightedRoughTerm_le :
    ∃ C y₀ : ℝ, 0 < C ∧ 0 < y₀ ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (y : ℕ) (σ x : ℝ), 2 ≤ y → y₀ ≤ (y : ℝ) → (y : ℝ) ≤ x → 0 < σ →
        σ * Real.log (x / y) ≤ 1 →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough y r) → (∀ r ∈ S, 1 < r) → (∀ r ∈ S, (r : ℝ) ≤ x) →
        (∫ ω, (∑ r ∈ S, weightedRoughTerm
            (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q ∂μ)
          ≤ C * ((∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
                    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                      / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
              + (Real.log x / Real.sqrt y + (Real.log y)⁻¹) ^ q) := by
  classical
  obtain ⟨C₁, y₁, hC₁, hy₁, hpt⟩ := exists_sum_weightedRoughTerm_le_sqrt
  obtain ⟨K, y₂, hK, hy₂, hprin⟩ := exists_setIntegral_normSq_mul_sieve_le
  obtain ⟨C₄, y₄, hC₄, hy₄, herrq⟩ := exists_integral_rpow_smoothingError_le
  refine ⟨max (max 1 (K * C₁)) C₄, max (max y₁ y₂) y₄,
    lt_of_lt_of_le one_pos (le_trans (le_max_left 1 (K * C₁)) (le_max_left _ _)),
    lt_of_lt_of_le hy₁ (le_trans (le_max_left y₁ y₂) (le_max_left _ _)), ?_⟩
  intro q hq0 hq1 Ω' _ X μ hX y σ x hy hy₀ hyx hσ hσlog S hrough hone hle
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx0 : (0 : ℝ) ≤ x := le_trans (by linarith) hyx
  have hy1' : y₁ ≤ (y : ℝ) := le_trans (le_trans (le_max_left y₁ y₂) (le_max_left _ _)) hy₀
  have hy2' : y₂ ≤ (y : ℝ) := le_trans (le_trans (le_max_right y₁ y₂) (le_max_left _ _)) hy₀
  have hy4' : y₄ ≤ (y : ℝ) := le_trans (le_max_right _ _) hy₀
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by linarith)
  have hKC : (0 : ℝ) < K * C₁ := mul_pos hK hC₁
  have hZ0 : ∀ ω : Ω', (0 : ℝ) ≤ ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :=
    fun ω => mul_nonneg (inv_nonneg.2 hlogy) (integral_nonneg fun t => by positivity)
  -- parts 1 and 2, combined
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hstep : ∀ᵐ ω ∂μ, (∑ r ∈ S, weightedRoughTerm
      (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q
      ≤ (K * C₁) ^ q * (((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q
        + ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2) ^ q := by
    filter_upwards [hbdd, hprin Ω' X μ C₁ hC₁ y σ x hy hy2' hyx hσ hσlog] with ω hb hp
    have h1 := hpt y x hy hy1' hyx Ω'
        (fun ω => squarefreeExtension fun p => X p ω) ω hb S hrough hone hle
    have hsum0 : (0 : ℝ) ≤ ∑ r ∈ S, weightedRoughTerm
        (fun ω => squarefreeExtension fun p => X p ω) y x ω r :=
      Finset.sum_nonneg fun r _ => weightedRoughTerm_nonneg _ _ _ _ _
    have hle2 : (∑ r ∈ S, weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r)
        ≤ K * C₁ * (((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))
          + ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2) := by linarith
    calc (∑ r ∈ S, weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q
        ≤ (K * C₁ * (((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))
            + ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
              (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
                ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                  - smoothWeightedSum
                      (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
                / ((r : ℝ)) ^ 2)) ^ q := Real.rpow_le_rpow hsum0 hle2 hq0.le
      _ ≤ (K * C₁ * (((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))) ^ q
            + ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
              (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
                ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                  - smoothWeightedSum
                      (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
                / ((r : ℝ)) ^ 2) ^ q :=
          Real.rpow_add_le_add_rpow (mul_nonneg hKC.le (hZ0 ω))
            (smoothingError_nonneg (X := X) y x S ω) hq0.le hq1
      _ = (K * C₁) ^ q * (((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q
            + ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
              (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
                ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                  - smoothWeightedSum
                      (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
                / ((r : ℝ)) ^ 2) ^ q := by
          rw [Real.mul_rpow hKC.le (hZ0 ω)]
  -- integrate
  have hI1 := integrable_rpow_sum_weightedRoughTerm hRa y hx0 (fun m hm => (hone m hm).le) hq0.le
  have hIZ : Integrable (fun ω => (K * C₁) ^ q * (((Real.log y)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q) μ :=
    (integrable_rpow_eulerProductLine hX y hσ hq0.le).const_mul _
  have hIE : Integrable (fun ω => ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
          (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
            ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
              - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
            / ((r : ℝ)) ^ 2) ^ q) μ :=
    integrable_rpow_of_integrable (integrable_smoothingError hX y hx0 hone)
      (Filter.Eventually.of_forall (smoothingError_nonneg (X := X) y x S)) hq0.le hq1
  have hZint0 : (0 : ℝ) ≤ ∫ ω, (((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (hZ0 ω) q
  have hL : (0 : ℝ) ≤ Real.log x / Real.sqrt y + (Real.log y)⁻¹ := by
    have h1 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ (Real.log y)⁻¹ := inv_nonneg.2 hlogy
    positivity
  have hLq : (0 : ℝ) ≤ (Real.log x / Real.sqrt y + (Real.log y)⁻¹) ^ q := Real.rpow_nonneg hL q
  calc (∫ ω, (∑ r ∈ S, weightedRoughTerm
      (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q ∂μ)
      ≤ ∫ ω, ((K * C₁) ^ q * (((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q
          + ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2) ^ q) ∂μ := integral_mono_ae hI1 (hIZ.add hIE) hstep
    _ = (K * C₁) ^ q * (∫ ω, (((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q ∂μ)
          + ∫ ω, ((1 / (1 / Real.sqrt y)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2) ^ q ∂μ := by
        rw [integral_add hIZ hIE, integral_const_mul]
    _ ≤ max 1 (K * C₁) * (∫ ω, (((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q ∂μ)
          + C₄ * (Real.log x / Real.sqrt y + (Real.log y)⁻¹) ^ q :=
        add_le_add (mul_le_mul_of_nonneg_right (rpow_le_max_one hKC hq0.le hq1) hZint0)
          (herrq q hq0.le hq1 Ω' X μ hX y x hy hy4' hyx S hrough hone hle)
    _ ≤ max (max 1 (K * C₁)) C₄ * ((∫ ω, (((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q ∂μ)
          + (Real.log x / Real.sqrt y + (Real.log y)⁻¹) ^ q) := by
        have h1 := mul_le_mul_of_nonneg_right (le_max_left (max 1 (K * C₁)) C₄) hZint0
        have h2 := mul_le_mul_of_nonneg_right (le_max_right (max 1 (K * C₁)) C₄) hLq
        nlinarith [h1, h2]

end RMF
