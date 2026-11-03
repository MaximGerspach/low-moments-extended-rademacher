/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.WeightedExtended.Perron
import RMF.Weighted.WeightedExtended.Line
import RMF.Weighted.ExtendedLowerKhintchine
import RMF.Reduction.CoordinateModel
import RMF.Probability.Symmetrisation

/-!
# The weighted extended sum: the moments

The last step of the proof of Proposition 1.5 of the paper.  For `0 < q ≤ ½` and `x ≥ 3`, with
`C` absolute and independent of the probability space
(`RMF.weighted_extended_rademacher_moments_uniform`),

`E|∑_{n≤x} X^e(n)/√n|^{2q} ≤ C(1 + q⁻²)(log x)^{q(2q+1)}`.

For `x ≥ 8`, almost surely `S^e = ½A + B` (`RMF.ae_weightedRademacherSum_compMultExtension_eq`),
`|A| ≤ (e/2π)∫_ℝ ρ|F|` (`RMF.norm_logWeightedSum_le`), so by subadditivity
`E|S^e|^{2q} ≤ ((e/4π)log x)^{2q}E[Y^{2q}] + E|B|^{2q}` with `Y = (log x)⁻¹∫_ℝρ|F|`; then
`RMF.exists_const_integral_rpow_lineAbs_le` and `RMF.integral_rpow_norm_harmonicRemainderSum_le`.
For `3 ≤ x < 8`, `|S^e| ≤ ⌊x⌋ ≤ 8`.  The constant is made independent of the probability space
on the coordinate model
(`RMF.IsIIDPrimeValues.integral_rpow_weightedRademacherSum_compMultExtension_eq`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The sum is measurable and bounded -/

/-- `S^e(x) = ∑_{n≤x} X^e(n)/√n` is measurable. -/
lemma measurable_weightedRademacherSum_compMultExtension {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) :
    Measurable (weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x) :=
  Finset.measurable_sum _ fun n _ => (hX.measurable_compMultExtension n).div_const _

/-- `|S^e(x)| ≤ ⌊x⌋` almost surely, as `|X^e(n)| ≤ 1`. -/
lemma ae_norm_weightedRademacherSum_compMultExtension_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ≤ ⌊x⌋₊ := by
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 ⌊x⌋₊)).2 fun n _ =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n] with ω hω
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ‖compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)‖ ≤ 1 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_one (by positivity)).2 ((hω n hn).trans (Real.one_le_sqrt.2 hn1))
  calc ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ⌊x⌋₊ := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

/-- `|S^e(x)|^r` is integrable for `r ≥ 0`: measurable and bounded by `⌊x⌋^r`. -/
lemma integrable_rpow_norm_weightedRademacherSum_compMultExtension {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω =>
      ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  refine (memLp_top_of_bound ((Real.continuous_rpow_const hr).measurable.comp
    (measurable_weightedRademacherSum_compMultExtension hX x).norm).aestronglyMeasurable
    ((⌊x⌋₊ : ℝ) ^ r) ?_).integrable le_top
  filter_upwards [ae_norm_weightedRademacherSum_compMultExtension_le hX x] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
  exact Real.rpow_le_rpow (norm_nonneg _) hω hr

/-! ### The split, pathwise -/

/-- **The split, pathwise.**  Almost surely, for `x > 1` and `0 ≤ q ≤ ½`,
`|S^e(x)|^{2q} ≤ ((e/4π)log x)^{2q}Y^{2q} + |B(x)|^{2q}`, `Y = (log x)⁻¹∫_ℝρ|F|`: `S^e = ½A + B`
(`RMF.ae_weightedRademacherSum_compMultExtension_eq`), `|A| ≤ (e/2π)∫_ℝρ|F|`
(`RMF.norm_logWeightedSum_le`), and subadditivity of `u ↦ u^{2q}`. -/
lemma ae_rpow_norm_weightedRademacherSum_compMultExtension_le {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 < x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1 / 2) :
    ∀ᵐ ω ∂μ, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q)
      ≤ (Real.exp 1 / (4 * Real.pi) * Real.log x) ^ (2 * q)
          * ((Real.log x)⁻¹ * ∫ t : ℝ, ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine (Real.log x)⁻¹ t) ω‖) ^ (2 * q)
        + ‖harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hLne : Real.log x ≠ 0 := hL0.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  filter_upwards [ae_weightedRademacherSum_compMultExtension_eq hX hx.le] with ω hω
  rw [hω]
  have hA := norm_logWeightedSum_le (X := X) ω hx
  have hI0 : 0 ≤ ∫ t : ℝ, ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
      * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
        (shiftLine (Real.log x)⁻¹ t) ω‖ :=
    integral_nonneg fun t => mul_nonneg (by positivity) (norm_nonneg _)
  generalize logWeightedSum (fun ω => squarefreeExtension fun p => X p ω) x ω = A at hA ⊢
  generalize harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω = B
  generalize (∫ t : ℝ, ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
    * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
      (shiftLine (Real.log x)⁻¹ t) ω‖) = I at hA hI0 ⊢
  have hhalf : ‖1 / 2 * A‖
      ≤ Real.exp 1 / (4 * Real.pi) * Real.log x * ((Real.log x)⁻¹ * I) := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    calc 1 / 2 * ‖A‖ ≤ 1 / 2 * (Real.exp 1 / (2 * Real.pi) * I) :=
          mul_le_mul_of_nonneg_left hA (by norm_num)
      _ = Real.exp 1 / (4 * Real.pi) * Real.log x * ((Real.log x)⁻¹ * I) := by
          field_simp
          ring
  have h2q0 : 0 ≤ 2 * q := by linarith
  have h2q1 : 2 * q ≤ 1 := by linarith
  calc ‖1 / 2 * A + B‖ ^ (2 * q) ≤ (‖1 / 2 * A‖ + ‖B‖) ^ (2 * q) :=
        Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) h2q0
    _ ≤ ‖1 / 2 * A‖ ^ (2 * q) + ‖B‖ ^ (2 * q) :=
        Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) h2q0 h2q1
    _ ≤ (Real.exp 1 / (4 * Real.pi) * Real.log x * ((Real.log x)⁻¹ * I)) ^ (2 * q)
          + ‖B‖ ^ (2 * q) :=
        add_le_add_left (Real.rpow_le_rpow (norm_nonneg _) hhalf h2q0) _
    _ = (Real.exp 1 / (4 * Real.pi) * Real.log x) ^ (2 * q) * ((Real.log x)⁻¹ * I) ^ (2 * q)
          + ‖B‖ ^ (2 * q) := by
        rw [Real.mul_rpow (by positivity) (mul_nonneg (inv_nonneg.2 hL0.le) hI0)]

/-! ### The assembly -/

/-- The assembly's arithmetic, for `L ≥ 1` and `0 < q ≤ ½`: from `Y ≤ C₁(1 + q⁻²)L^{q(2q-1)}` and
`B ≤ (1 + L)^q`, `((e/4π)L)^{2q}Y + B ≤ (C₁ + 8)(1 + q⁻²)L^{q(2q+1)}`. -/
lemma weightedExtended_assembly_le {L q C₁ Y B : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hC₁ : 0 ≤ C₁) (hY : Y ≤ C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q - 1)))
    (hB : B ≤ (1 + L) ^ q) :
    (Real.exp 1 / (4 * Real.pi) * L) ^ (2 * q) * Y + B
      ≤ (C₁ + 8) * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < Real.exp 1 / (4 * Real.pi) := by positivity
  have hc1 : Real.exp 1 / (4 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hcq : (Real.exp 1 / (4 * Real.pi)) ^ (2 * q) ≤ 1 :=
    Real.rpow_le_one hc0.le hc1 (by linarith)
  have hcL : (Real.exp 1 / (4 * Real.pi) * L) ^ (2 * q) ≤ L ^ (2 * q) := by
    rw [Real.mul_rpow hc0.le hL0.le]
    calc (Real.exp 1 / (4 * Real.pi)) ^ (2 * q) * L ^ (2 * q) ≤ 1 * L ^ (2 * q) :=
          mul_le_mul_of_nonneg_right hcq (Real.rpow_nonneg hL0.le _)
      _ = L ^ (2 * q) := one_mul _
  have hu : 1 ≤ 1 + (q ^ 2)⁻¹ := le_add_of_nonneg_right (by positivity)
  have hv : 0 ≤ L ^ (q * (2 * q + 1)) := Real.rpow_nonneg hL0.le _
  have hexp : L ^ (2 * q) * L ^ (q * (2 * q - 1)) = L ^ (q * (2 * q + 1)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hM : 0 ≤ C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q - 1)) :=
    mul_nonneg (mul_nonneg hC₁ (by positivity)) (Real.rpow_nonneg hL0.le _)
  have hA : (Real.exp 1 / (4 * Real.pi) * L) ^ (2 * q) * Y
      ≤ C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) := by
    calc (Real.exp 1 / (4 * Real.pi) * L) ^ (2 * q) * Y
        ≤ (Real.exp 1 / (4 * Real.pi) * L) ^ (2 * q)
          * (C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q - 1))) :=
          mul_le_mul_of_nonneg_left hY (Real.rpow_nonneg (by positivity) _)
      _ ≤ L ^ (2 * q) * (C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q - 1))) :=
          mul_le_mul_of_nonneg_right hcL hM
      _ = C₁ * (1 + (q ^ 2)⁻¹) * (L ^ (2 * q) * L ^ (q * (2 * q - 1))) := by ring
      _ = C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) := by rw [hexp]
  have hB2 : (1 + L) ^ q ≤ 2 * L ^ (q * (2 * q + 1)) := by
    calc (1 + L) ^ q ≤ (2 * L) ^ q := Real.rpow_le_rpow (by positivity) (by linarith) hq0.le
      _ = 2 ^ q * L ^ q := Real.mul_rpow (by norm_num) hL0.le
      _ ≤ 2 * L ^ (q * (2 * q + 1)) :=
          mul_le_mul (Real.rpow_le_self_of_one_le (by norm_num) (by linarith))
            (Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)) (Real.rpow_nonneg hL0.le _)
            (by norm_num)
  have h8 : 2 * L ^ (q * (2 * q + 1)) ≤ 8 * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_right hu hv]
  calc (Real.exp 1 / (4 * Real.pi) * L) ^ (2 * q) * Y + B
      ≤ C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) + 2 * L ^ (q * (2 * q + 1)) :=
        add_le_add hA (hB.trans hB2)
    _ ≤ C₁ * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1))
          + 8 * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) := by linarith
    _ = (C₁ + 8) * (1 + (q ^ 2)⁻¹) * L ^ (q * (2 * q + 1)) := by ring

/-- **The moments of the weighted extended sum, uniformly in `q`, on one probability space.**
For `x ≥ 3` and `0 < q ≤ ½`, `E|S^e(x)|^{2q} ≤ C(1 + q⁻²)(log x)^{q(2q+1)}`: the pathwise split
(`RMF.ae_rpow_norm_weightedRademacherSum_compMultExtension_le`) with
`RMF.exists_const_integral_rpow_lineAbs_le` and `RMF.integral_rpow_norm_harmonicRemainderSum_le`
for `x ≥ 8`, and `|S^e| ≤ 8` below. -/
theorem exists_const_integral_rpow_weightedExtended_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, 3 ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (1 + (q ^ 2)⁻¹) * Real.log x ^ (q * (2 * q + 1)) := by
  obtain ⟨C₁, hC₁, H⟩ := exists_const_integral_rpow_lineAbs_le (Ω := Ω)
  refine ⟨C₁ + 8, by linarith, ?_⟩
  intro X μ hX x q hx3 hq0 hq1
  haveI := hX.isProbabilityMeasure
  have hL1 : 1 < Real.log x := one_lt_log_of_three_le hx3
  have hL0 : 0 < Real.log x := by linarith
  rcases lt_or_ge x 8 with hx8 | hx8
  · -- `3 ≤ x < 8`: `|S^e| ≤ ⌊x⌋ ≤ 8`
    have hu : 1 ≤ 1 + (q ^ 2)⁻¹ := le_add_of_nonneg_right (by positivity)
    have hv : 1 ≤ Real.log x ^ (q * (2 * q + 1)) := Real.one_le_rpow hL1.le (by positivity)
    calc (∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
        ≤ ∫ _ω, (8 : ℝ) ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (norm_nonneg _) _) (integrable_const _) ?_
          filter_upwards [ae_norm_weightedRademacherSum_compMultExtension_le hX x] with ω hω
          have h8 : ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ≤ 8 := hω.trans ((Nat.floor_le (by linarith)).trans hx8.le)
          calc ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                ^ (2 * q) ≤ (8 : ℝ) ^ (2 * q) :=
                Real.rpow_le_rpow (norm_nonneg _) h8 (by linarith)
            _ ≤ (8 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 8 := Real.rpow_one 8
      _ = 8 := by simp
      _ = 8 * 1 * 1 := by ring
      _ ≤ (C₁ + 8) * (1 + (q ^ 2)⁻¹) * Real.log x ^ (q * (2 * q + 1)) :=
          mul_le_mul (mul_le_mul (by linarith) hu zero_le_one (by linarith)) hv zero_le_one
            (mul_nonneg (by linarith) (by positivity))
  · -- `x ≥ 8`: the split
    have hσ : 0 < (Real.log x)⁻¹ := inv_pos.2 hL0
    have hYi := integrable_rpow_integral_weight_norm hX (⌊x⌋₊ + 1) hσ.le
      (ρ := fun t => ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹) (by fun_prop) (fun t => by positivity)
      (integrable_inv_sq_add_sq hσ.ne') hσ.le (r := 2 * q) (by linarith)
    have hBi := integrable_rpow_norm_harmonicRemainderSum hX x (r := 2 * q) (by linarith)
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (norm_nonneg _) _) ((hYi.const_mul _).add hBi)
      (ae_rpow_norm_weightedRademacherSum_compMultExtension_le hX (by linarith) hq0.le
        hq1)).trans ?_
    simp only [Pi.add_apply]
    rw [integral_add (hYi.const_mul _) hBi, integral_const_mul]
    exact weightedExtended_assembly_le hL1.le hq0 hq1 hC₁.le (H X μ hX x q hx8 hq0 hq1)
      (integral_rpow_norm_harmonicRemainderSum_le hX (by linarith) hq0.le (by linarith))

/-! ### Independence of the probability space -/

/-- **`E|∑_{n≤x} f(n)/√n|^r` is the coordinate model's**, for `f` the completely multiplicative
extension of iid values at the primes: the copy of
`RMF.IsIIDPrimeValues.integral_rpow_weightedRademacherSum_squarefreeExtension_eq` for `X^e`. -/
theorem IsIIDPrimeValues.integral_rpow_weightedRademacherSum_compMultExtension_eq
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (x r : ℝ) :
    ∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ r ∂μ
      = ∫ v, ‖weightedRademacherSum (fun v => compMultExtension (primeExtend v)) x v‖ ^ r
          ∂(Measure.infinitePi fun _ : Nat.Primes => ν) := by
  have hm : Measurable fun v : Nat.Primes → ℂ =>
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension (primeExtend v) n / (Real.sqrt n : ℂ)‖ ^ r :=
    (Finset.measurable_sum _ fun n _ =>
      (measurable_compMultExtension_primeExtend n).div_const (Real.sqrt n : ℂ)).norm.pow_const r
  exact hX.integral_comp_primeExtend
    (Ψ := fun g => ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension g n / (Real.sqrt n : ℂ)‖ ^ r)
    (fun h => congrArg
      (fun F : ArithmeticFunction ℂ => ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n / (Real.sqrt n : ℂ)‖ ^ r)
      (compMultExtension_congr_primes h))
    hm.aestronglyMeasurable

/-- **The moments of the weighted extended sum, uniformly in `q`.**  There is an absolute `C`
such that on every probability space, for `x ≥ 3` and `0 < q ≤ ½`,
`E|∑_{n≤x} X^e(n)/√n|^{2q} ≤ C(1 + q⁻²)(log x)^{q(2q+1)}`:
`RMF.exists_const_integral_rpow_weightedExtended_le` on the coordinate model, transferred by
`RMF.IsIIDPrimeValues.integral_rpow_weightedRademacherSum_compMultExtension_eq`.  The factor
`1 + q⁻²` is the windows' geometric sum; Proposition 1.5 fixes `q`. -/
theorem weighted_extended_rademacher_moments_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x q : ℝ, 3 ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (1 + (q ^ 2)⁻¹) * Real.log x ^ (q * (2 * q + 1)) := by
  obtain ⟨C, hC, H⟩ := exists_const_integral_rpow_weightedExtended_le (Ω := Nat.Primes → ℂ)
  refine ⟨C, hC, fun Ω _ X μ hX x q hx hq0 hq1 => ?_⟩
  rw [hX.integral_rpow_weightedRademacherSum_compMultExtension_eq]
  exact H _ _ (isIIDPrimeValues_primeExtend rademacherLaw) x q hx hq0 hq1

end RMF
