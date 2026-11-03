/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FixedQScales
import RMF.Weighted.Fluctuations
import RMF.Weighted.EulerMomentHalfExplicit

/-!
# The three estimates of the fixed-`q` upper bound

The upper bound for fixed `½ < q < 1` bounds the three groups of terms of
`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le` by

* (PF), the Euler product's moments:
  `‖F_{Y k}(½)‖_{2q} ≪ (log Y k)^{(2q-1)/2} ≤ e^{(1-k)(2q-1)/2}(log x)^{(2q-1)/2}`;
* (T1), the block tail bound at `Λ = 2e`: `‖T_{Y(k+1),Yk}(x)‖₂ ≤ C₁^{1/2}`;
* (T0), the tail bound at the bottom layer: `‖T_{YK}(x)‖₂ ≪ (log x)^{(2q-1)/2}`,

and then sums the geometric series `∑_{k≥1} e^{-k(2q-1)/2}`, uniformly in `K`
(`RMF.sum_Ico_pow_le`, `∑_{k=1}^{K-1} r^k ≤ (1-r)⁻¹`).

## Main results

* `RMF.exists_rpow_inv_integral_rpow_norm_weightedRademacherSum_le`: the assembly, for any
  admissible layer count;
* `RMF.exists_integral_rpow_norm_weightedRademacherSum_le`: the bound at fixed `½ < q < 1`;
* `RMF.exists_integral_rpow_norm_weightedRademacherSum_le_uniform_min`: the bound uniform in `q`,
  with `min{3 + log log x, 2 + 2/(2q-1)}`.
-/

open Finset MeasureTheory

namespace RMF

/-! ### The geometric series -/

/-- **`∑_{k=1}^{K-1} r^k ≤ (1-r)⁻¹`, uniformly in `K`.**  What makes the layer sum a constant
depending on `q` alone. -/
lemma sum_Ico_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K, r ^ k ≤ (1 - r)⁻¹ := by
  have hsum : Summable fun k : ℕ => r ^ k :=
    summable_geometric_of_lt_one hr0 hr1
  calc ∑ k ∈ Finset.Ico 1 K, r ^ k ≤ ∑ k ∈ Finset.range K, r ^ k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
        intro k hk
        exact Finset.mem_range.2 (Finset.mem_Ico.1 hk).2
    _ ≤ ∑' k : ℕ, r ^ k := hsum.sum_le_tsum _ fun i _ => by positivity
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-! ### From a moment bound to a norm bound -/

/-- **The `(2q)`-th root of `(PF)`.**  From `A ≤ C·v^{q(2q-1)}` to
`A^{1/(2q)} ≤ C^{1/(2q)}·v^{(2q-1)/2}`; `q(2q-1)/(2q) = (2q-1)/2`. -/
lemma rpow_inv_le_mul_rpow {q C v A : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (hv : 0 ≤ v) (hA : 0 ≤ A)
    (h : A ≤ C * v ^ (q * (2 * q - 1))) :
    A ^ (2 * q)⁻¹ ≤ C ^ (2 * q)⁻¹ * v ^ ((2 * q - 1) / 2) := by
  have h2q : (0 : ℝ) < 2 * q := by linarith
  calc A ^ (2 * q)⁻¹ ≤ (C * v ^ (q * (2 * q - 1))) ^ (2 * q)⁻¹ :=
        Real.rpow_le_rpow hA h (by positivity)
    _ = C ^ (2 * q)⁻¹ * (v ^ (q * (2 * q - 1))) ^ (2 * q)⁻¹ :=
        Real.mul_rpow hC (Real.rpow_nonneg hv _)
    _ = C ^ (2 * q)⁻¹ * v ^ ((2 * q - 1) / 2) := by
        rw [← Real.rpow_mul hv]
        congr 2
        field_simp

/-- **The layer weight.**  `(u (k+1))^{(2q-1)/2} = r^k·(log x)^{(2q-1)/2}` with
`r = e^{-(2q-1)/2}`, the geometric ratio of the layer sum. -/
lemma rpow_fixedQLogScale_succ {q x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    fixedQLogScale x (k + 1) ^ ((2 * q - 1) / 2)
      = (Real.exp (-((2 * q - 1) / 2))) ^ k * (Real.log x) ^ ((2 * q - 1) / 2) := by
  have hL : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hcast : (1 : ℝ) - ((k + 1 : ℕ) : ℝ) = -(k : ℝ) := by push_cast; ring
  rw [fixedQLogScale, hcast, Real.mul_rpow (Real.exp_pos _).le hL]
  congr 1
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-! ### The assembly

The assembly is stated once, with the three quantitative facts about the scales left as
hypotheses — the threshold at every layer, a bound `B` on the bottom layer, and a bound `G` on the
layer sum.  The capped depth below supplies the first two and leaves `G` free. -/

/-- **The assembly.**  For any admissible layer count `K` (every layer above `log 4`, the bottom
layer at most `B·(log x)^{2q-1}`, the layer sum at most `G`),
`‖S(x)‖_{2q} ≤ D·(1+G)·B^{1/2}·(log x)^{(2q-1)/2}` with `D` absolute.  The inputs are (PF)
`RMF.exists_moment_half_le_uniform`, (T1) `RMF.exists_integral_normSq_blockTruncationTail_le` at
`Λ = 2e`, and (T0) `RMF.exists_integral_normSq_truncationTail_le_log`, which has no Rankin factor
`e^{-U}`: the bottom layer can reach `x^{1/e}`, where that factor would be worth nothing. -/
theorem exists_rpow_inv_integral_rpow_norm_weightedRademacherSum_le :
    ∃ D : ℝ, 0 < D ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (q x B G : ℝ) (K : ℕ), 1 / 2 ≤ q → q ≤ 1 → Real.exp 1 ≤ x → 1 ≤ K →
        (∀ k, k ≤ K → Real.log 4 ≤ fixedQLogScale x k) → 1 ≤ B → 0 ≤ G →
        fixedQLogScale x K ≤ B * (Real.log x) ^ (2 * q - 1) →
        (∑ k ∈ Finset.Ico 1 K, (Real.exp (-((2 * q - 1) / 2))) ^ k) ≤ G →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          ≤ D * (1 + G) * B ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2) := by
  obtain ⟨CP, hCP, hPF⟩ := exists_moment_half_le_uniform
  obtain ⟨C0, hC0, hT0⟩ := exists_integral_normSq_truncationTail_le_log
  obtain ⟨C1, hC1, hT1⟩ := exists_integral_normSq_blockTruncationTail_le
    (Λ := 2 * Real.exp 1) (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
  have hC1r : (0 : ℝ) ≤ C1 ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg hC1.le _
  have hC0r : (0 : ℝ) ≤ C0 ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg hC0.le _
  refine ⟨(1 + CP) * (1 + C1 ^ (2 : ℝ)⁻¹) + C0 ^ (2 : ℝ)⁻¹, by nlinarith, ?_⟩
  intro Ω _ X μ hX q x B G K hq0 hq1 hxe hK hthr4 hB hG hUK hsumG
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hqpos : (0 : ℝ) < q := by linarith
  have h2q : (0 : ℝ) < 2 * q := by linarith
  have hγ : (0 : ℝ) ≤ (2 * q - 1) / 2 := by linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hx2 : (2 : ℝ) ≤ x := le_trans (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hLγ : (0 : ℝ) ≤ (Real.log x) ^ ((2 * q - 1) / 2) := Real.rpow_nonneg hL0.le _
  have hBr : (1 : ℝ) ≤ B ^ (2 : ℝ)⁻¹ := by
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hB (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    rwa [Real.one_rpow] at this
  have hYmono : ∀ k, 1 ≤ k → k < K → fixedQScale x (k + 1) ≤ fixedQScale x k :=
    fun k _ _ => fixedQScale_antitone hx1 k
  have hY1 : fixedQScale x 1 = ⌊x⌋₊ := fixedQScale_one x
  have hstruct := rpow_inv_integral_rpow_norm_weightedRademacherSum_le hX (q := q)
    hq0 hq1 hK hYmono hx1 hY1
  -- the leading term, by (PF)
  have hlead : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (fixedQScale x 1 + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ CP ^ (2 * q)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2) := by
    have h2Y : 2 ≤ fixedQScale x 1 := by
      rw [hY1]
      exact Nat.le_floor (by exact_mod_cast hx2)
    have h1Y : (1 : ℝ) ≤ (fixedQScale x 1 : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ fixedQScale x 1)
    have hpf := hPF Ω (fun ω => squarefreeExtension fun p => X p ω) μ hRa q
      hq0 hq1 (fixedQScale x 1) h2Y
    refine le_trans (rpow_inv_le_mul_rpow hqpos hCP.le (Real.log_nonneg h1Y)
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hpf) ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hCP.le _)
    refine Real.rpow_le_rpow (Real.log_nonneg h1Y) ?_ hγ
    have h1 : fixedQLogScale x 1 = Real.log x := by simp [fixedQLogScale]
    have := log_fixedQScale_le hx1 1
    rwa [h1] at this
  -- a layer, by (PF) and (T1)
  have hlayer : ∀ k ∈ Finset.Ico 1 K,
      (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (fixedQScale x (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (fixedQScale x (k + 1)) (fixedQScale x k) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹
        ≤ CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2)
            * (Real.exp (-((2 * q - 1) / 2))) ^ k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.1 hk
    have h2Y : 2 ≤ fixedQScale x (k + 1) := two_le_fixedQScale hx1 (hthr4 (k + 1) (by omega))
    have h1Y : (1 : ℝ) ≤ (fixedQScale x (k + 1) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ fixedQScale x (k + 1))
    have hratio := log_fixedQScale_le_two_mul_exp_mul hx1 (hthr4 (k + 1) (by omega))
    have hT := hT1 Ω X μ hX (fixedQScale x (k + 1)) (fixedQScale x k) h2Y
      (fixedQScale_antitone hx1 k) hratio x (fixedQScale_le hx1 hk1)
    have hTroot : (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
          (fixedQScale x (k + 1)) (fixedQScale x k) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹
        ≤ C1 ^ (2 : ℝ)⁻¹ :=
      Real.rpow_le_rpow (integral_nonneg fun ω => by positivity) hT (by norm_num)
    have hpf := hPF Ω (fun ω => squarefreeExtension fun p => X p ω) μ hRa q
      hq0 hq1 (fixedQScale x (k + 1)) h2Y
    have hEroot := rpow_inv_le_mul_rpow hqpos hCP.le (Real.log_nonneg h1Y)
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hpf
    have hstep : Real.log (fixedQScale x (k + 1)) ^ ((2 * q - 1) / 2)
        ≤ (Real.exp (-((2 * q - 1) / 2))) ^ k * (Real.log x) ^ ((2 * q - 1) / 2) := by
      rw [← rpow_fixedQLogScale_succ (q := q) hx1 k]
      exact Real.rpow_le_rpow (Real.log_nonneg h1Y) (log_fixedQScale_le hx1 (k + 1)) hγ
    have hE : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          (fixedQScale x (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
        ≤ CP ^ (2 * q)⁻¹
            * ((Real.exp (-((2 * q - 1) / 2))) ^ k * (Real.log x) ^ ((2 * q - 1) / 2)) :=
      le_trans hEroot (mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hCP.le _))
    calc (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
              (fixedQScale x (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
            * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
                (fixedQScale x (k + 1)) (fixedQScale x k) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹
        ≤ (CP ^ (2 * q)⁻¹
            * ((Real.exp (-((2 * q - 1) / 2))) ^ k * (Real.log x) ^ ((2 * q - 1) / 2)))
              * C1 ^ (2 : ℝ)⁻¹ :=
          mul_le_mul hE hTroot (Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _)
            (by positivity)
      _ = CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2)
            * (Real.exp (-((2 * q - 1) / 2))) ^ k := by ring
  -- the layer sum
  have hAnn : (0 : ℝ) ≤ CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2) := by
    positivity
  have hsum : (∑ k ∈ Finset.Ico 1 K,
        (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
              (fixedQScale x (k + 1) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (fixedQScale x (k + 1)) (fixedQScale x k) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹)
      ≤ CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G * (Real.log x) ^ ((2 * q - 1) / 2) := by
    calc (∑ k ∈ Finset.Ico 1 K, _)
        ≤ ∑ k ∈ Finset.Ico 1 K,
            CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2)
              * (Real.exp (-((2 * q - 1) / 2))) ^ k := Finset.sum_le_sum hlayer
      _ = CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2)
            * ∑ k ∈ Finset.Ico 1 K, (Real.exp (-((2 * q - 1) / 2))) ^ k :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2) * G :=
          mul_le_mul_of_nonneg_left hsumG hAnn
      _ = CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G * (Real.log x) ^ ((2 * q - 1) / 2) := by ring
  -- the bottom tail, by (T0)
  have hbot : (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω)
        (fixedQScale x K) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹
      ≤ C0 ^ (2 : ℝ)⁻¹ * B ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2) := by
    have h2Y : 2 ≤ fixedQScale x K := two_le_fixedQScale hx1 (hthr4 K le_rfl)
    have hT := hT0 Ω X μ hX (fixedQScale x K) x h2Y (fixedQScale_le hx1 hK)
    have hvle : Real.log (fixedQScale x K) ≤ B * (Real.log x) ^ (2 * q - 1) :=
      le_trans (log_fixedQScale_le hx1 K) hUK
    have hbound : (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω)
          (fixedQScale x K) x ω‖ ^ 2 ∂μ) ≤ C0 * (B * (Real.log x) ^ (2 * q - 1)) :=
      le_trans hT (mul_le_mul_of_nonneg_left hvle hC0.le)
    calc (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω)
            (fixedQScale x K) x ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹
        ≤ (C0 * (B * (Real.log x) ^ (2 * q - 1))) ^ (2 : ℝ)⁻¹ :=
          Real.rpow_le_rpow (integral_nonneg fun ω => by positivity) hbound (by norm_num)
      _ = C0 ^ (2 : ℝ)⁻¹ * (B * (Real.log x) ^ (2 * q - 1)) ^ (2 : ℝ)⁻¹ :=
          Real.mul_rpow hC0.le (by positivity)
      _ = C0 ^ (2 : ℝ)⁻¹ * (B ^ (2 : ℝ)⁻¹ * ((Real.log x) ^ (2 * q - 1)) ^ (2 : ℝ)⁻¹) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hL0.le _)]
      _ = C0 ^ (2 : ℝ)⁻¹ * B ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2) := by
          rw [← Real.rpow_mul hL0.le, show (2 * q - 1) * (2 : ℝ)⁻¹ = (2 * q - 1) / 2 by ring]
          ring
  -- and the three together
  refine le_trans hstruct (le_trans (add_le_add (add_le_add hlead hsum) hbot) ?_)
  have h2qinv : (2 * q)⁻¹ ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * q)
    simpa using h
  have hCPr : CP ^ (2 * q)⁻¹ ≤ 1 + CP :=
    rpow_le_one_add hCP.le (by positivity) h2qinv
  have hCPr0 : (0 : ℝ) ≤ CP ^ (2 * q)⁻¹ := Real.rpow_nonneg hCP.le _
  have hPnn : (0 : ℝ) ≤ CP ^ (2 * q)⁻¹ + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G :=
    add_nonneg hCPr0 (mul_nonneg (mul_nonneg hCPr0 hC1r) hG)
  have hmul1 : CP ^ (2 * q)⁻¹ * (C1 ^ (2 : ℝ)⁻¹ * G) ≤ (1 + CP) * (C1 ^ (2 : ℝ)⁻¹ * G) :=
    mul_le_mul_of_nonneg_right hCPr (mul_nonneg hC1r hG)
  have hpos2 : (0 : ℝ) ≤ (1 + CP) * (C1 ^ (2 : ℝ)⁻¹ + G) :=
    mul_nonneg (by linarith) (by linarith)
  have hstep2 : CP ^ (2 * q)⁻¹ + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G + C0 ^ (2 : ℝ)⁻¹
      ≤ ((1 + CP) * (1 + C1 ^ (2 : ℝ)⁻¹) + C0 ^ (2 : ℝ)⁻¹) * (1 + G) := by
    have hexp : ((1 + CP) * (1 + C1 ^ (2 : ℝ)⁻¹) + C0 ^ (2 : ℝ)⁻¹) * (1 + G)
        = ((1 + CP) + (1 + CP) * (C1 ^ (2 : ℝ)⁻¹ * G) + (1 + CP) * (C1 ^ (2 : ℝ)⁻¹ + G))
          + (C0 ^ (2 : ℝ)⁻¹ + C0 ^ (2 : ℝ)⁻¹ * G) := by ring
    have hc0g : (0 : ℝ) ≤ C0 ^ (2 : ℝ)⁻¹ * G := mul_nonneg hC0r hG
    rw [hexp]
    nlinarith [hCPr, hmul1, hpos2, hc0g]
  have hstep1 : CP ^ (2 * q)⁻¹ + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G
        + C0 ^ (2 : ℝ)⁻¹ * B ^ (2 : ℝ)⁻¹
      ≤ (CP ^ (2 * q)⁻¹ + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G + C0 ^ (2 : ℝ)⁻¹)
          * B ^ (2 : ℝ)⁻¹ := by
    nlinarith [mul_nonneg hPnn (by linarith : (0 : ℝ) ≤ B ^ (2 : ℝ)⁻¹ - 1)]
  have hkey : CP ^ (2 * q)⁻¹ + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G + C0 ^ (2 : ℝ)⁻¹ * B ^ (2 : ℝ)⁻¹
      ≤ ((1 + CP) * (1 + C1 ^ (2 : ℝ)⁻¹) + C0 ^ (2 : ℝ)⁻¹) * (1 + G) * B ^ (2 : ℝ)⁻¹ :=
    le_trans hstep1 (mul_le_mul_of_nonneg_right hstep2 (by linarith))
  calc CP ^ (2 * q)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2)
        + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G * (Real.log x) ^ ((2 * q - 1) / 2)
        + C0 ^ (2 : ℝ)⁻¹ * B ^ (2 : ℝ)⁻¹ * (Real.log x) ^ ((2 * q - 1) / 2)
      = (CP ^ (2 * q)⁻¹ + CP ^ (2 * q)⁻¹ * C1 ^ (2 : ℝ)⁻¹ * G
          + C0 ^ (2 : ℝ)⁻¹ * B ^ (2 : ℝ)⁻¹) * (Real.log x) ^ ((2 * q - 1) / 2) := by ring
    _ ≤ ((1 + CP) * (1 + C1 ^ (2 : ℝ)⁻¹) + C0 ^ (2 : ℝ)⁻¹) * (1 + G) * B ^ (2 : ℝ)⁻¹
          * (Real.log x) ^ ((2 * q - 1) / 2) := mul_le_mul_of_nonneg_right hkey hLγ

/-- `c^t ≤ 1 + c²` for `0 ≤ c` and `t ∈ [1,2]`; the companion of `RMF.rpow_le_one_add` one
exponent up, which makes a constant absolute over `2q ∈ [1,2]`. -/
lemma rpow_le_one_add_rpow_two {c t : ℝ} (hc : 0 ≤ c) (ht0 : 1 ≤ t) (ht1 : t ≤ 2) :
    c ^ t ≤ 1 + c ^ (2 : ℝ) := by
  rcases le_or_gt c 1 with h | h
  · have h1 := Real.rpow_le_one hc h (by linarith)
    have h2 : (0 : ℝ) ≤ c ^ (2 : ℝ) := Real.rpow_nonneg hc _
    linarith
  · have h1 := Real.rpow_le_rpow_of_exponent_le h.le ht1
    linarith

/-- **From a root bound to a moment bound.**  `A^{1/t} ≤ v` gives `A ≤ v^t`, for `t > 0`. -/
lemma rpow_le_rpow_of_rpow_inv_le {A v t : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (h : A ^ t⁻¹ ≤ v) : A ≤ v ^ t := by
  calc A = (A ^ t⁻¹) ^ t := by
        rw [← Real.rpow_mul hA, inv_mul_cancel₀ ht.ne', Real.rpow_one]
    _ ≤ v ^ t := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h ht.le

/-- **The assembly at the capped depth**, with the layer-sum bound `G` still free.
`K = min(⌈2(1-q) log log x⌉₊ + 1, fixedQCap x)`: capping at the last layer with `u k ≥ log 4` keeps
every layer admissible without any condition relating `q` to `x`, so `x₀ = 4` is absolute.  Where
the cap binds, `u K < e·log 4` and the bottom tail is `O(1)`, below `(log x)^{(2q-1)/2} ≥ 1`.  The
uniform bound below is this with `G` the smaller of the two layer-sum bounds. -/
theorem exists_integral_rpow_norm_weightedRademacherSum_le_capped :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ q x G : ℝ, 1 / 2 ≤ q → q ≤ 1 → 4 ≤ x → 0 ≤ G →
        (∑ k ∈ Finset.Ico 1 (min (fixedQLayers q x) (fixedQCap x)),
            (Real.exp (-((2 * q - 1) / 2))) ^ k) ≤ G →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * (1 + G) ^ (2 * q) * (Real.log x) ^ (q * (2 * q - 1)) := by
  obtain ⟨D, hD, hassm⟩ := exists_rpow_inv_integral_rpow_norm_weightedRademacherSum_le
  have hlog4 : (1 : ℝ) ≤ Real.exp 1 * Real.log 4 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    nlinarith [Real.log_two_gt_d9]
  have hB : (0 : ℝ) ≤ (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by linarith) _
  refine ⟨1 + (D * (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹) ^ (2 : ℝ), by positivity, ?_⟩
  intro Ω _ X μ hX q x G hq0 hq1 hx hG hsumG
  have hxe : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hll : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hLq : (1 : ℝ) ≤ (Real.log x) ^ (2 * q - 1) := Real.one_le_rpow hL1 (by linarith)
  have hcap1 : 1 ≤ fixedQCap x := one_le_fixedQCap hx
  have hK : 1 ≤ min (fixedQLayers q x) (fixedQCap x) :=
    le_min (Nat.le_add_left 1 _) hcap1
  have hKcap : min (fixedQLayers q x) (fixedQCap x) ≤ fixedQCap x := min_le_right _ _
  have hthr4 : ∀ k, k ≤ min (fixedQLayers q x) (fixedQCap x) →
      Real.log 4 ≤ fixedQLogScale x k :=
    fun k hk => log_four_le_fixedQLogScale_of_le_cap hx (le_trans hk hKcap)
  have hUK : fixedQLogScale x (min (fixedQLayers q x) (fixedQCap x))
      ≤ Real.exp 1 * Real.log 4 * (Real.log x) ^ (2 * q - 1) := by
    rcases min_choice (fixedQLayers q x) (fixedQCap x) with h | h <;> rw [h]
    · have h1 := fixedQLogScale_layers_le hq1 hxe
      nlinarith [Real.rpow_nonneg hL0.le (2 * q - 1)]
    · have h1 := fixedQLogScale_cap_le hx
      nlinarith
  have hmain := hassm Ω X μ hX q x (Real.exp 1 * Real.log 4) G
    (min (fixedQLayers q x) (fixedQCap x)) hq0 hq1 hxe hK hthr4 hlog4 hG hUK hsumG
  have hEnn : (0 : ℝ) ≤ D * (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹ := by positivity
  have hrew : D * (1 + G) * (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹
      = (D * (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹) * (1 + G) := by ring
  rw [hrew] at hmain
  have hI : (0 : ℝ) ≤ ∫ ω, ‖weightedRademacherSum
      (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have h2q : (0 : ℝ) < 2 * q := by linarith
  refine le_trans (rpow_le_rpow_of_rpow_inv_le hI h2q hmain) ?_
  have hsplit : ((D * (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹) * (1 + G)
        * (Real.log x) ^ ((2 * q - 1) / 2)) ^ (2 * q)
      = (D * (Real.exp 1 * Real.log 4) ^ (2 : ℝ)⁻¹) ^ (2 * q)
        * (1 + G) ^ (2 * q) * (Real.log x) ^ (q * (2 * q - 1)) := by
    rw [Real.mul_rpow (mul_nonneg hEnn (by linarith)) (Real.rpow_nonneg hL0.le _),
      Real.mul_rpow hEnn (by linarith), ← Real.rpow_mul hL0.le]
    congr 2
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hL0.le _)
  exact rpow_le_one_add_rpow_two hEnn (by linarith) (by linarith)

/-- **The layer sum, term by term.**  `∑_{k<K} r^k ≤ log log x + 2`, the bound that survives at
`q = ½`, where the series is not geometric. -/
lemma sum_Ico_exp_le_log_log {q x : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hx : Real.exp 1 ≤ x)
    (K : ℕ) (hKle : K ≤ fixedQLayers q x) :
    (∑ k ∈ Finset.Ico 1 K, (Real.exp (-((2 * q - 1) / 2))) ^ k)
      ≤ Real.log (Real.log x) + 2 := by
  have hr1 : Real.exp (-((2 * q - 1) / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hterm : ∀ k ∈ Finset.Ico 1 K, (Real.exp (-((2 * q - 1) / 2))) ^ k ≤ 1 :=
    fun k _ => pow_le_one₀ (Real.exp_pos _).le hr1
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one, Nat.card_Ico]
  have hcard : ((K - 1 : ℕ) : ℝ) ≤ ((fixedQLayers q x : ℕ) : ℝ) := by
    have : K - 1 ≤ fixedQLayers q x := by omega
    exact_mod_cast this
  exact le_trans hcard (fixedQLayers_le hq0 hq1 hx)

/-- **The layer sum, geometrically.**  `∑_{k<K} r^k ≤ 1 + 2/(2q-1)` for `q > ½`, from
`1 - e^{-γ} ≥ γ/(1+γ)`.  At fixed `q` it is a constant, which gives the fixed-`q` bound. -/
lemma sum_Ico_exp_le_inv {q : ℝ} (hq0 : 1 / 2 < q) (K : ℕ) :
    (∑ k ∈ Finset.Ico 1 K, (Real.exp (-((2 * q - 1) / 2))) ^ k)
      ≤ 1 + 2 / (2 * q - 1) := by
  have hγ : (0 : ℝ) < (2 * q - 1) / 2 := by linarith
  have hr0 : (0 : ℝ) ≤ Real.exp (-((2 * q - 1) / 2)) := (Real.exp_pos _).le
  have hupper : Real.exp (-((2 * q - 1) / 2)) ≤ 1 / (1 + (2 * q - 1) / 2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * q - 1) / 2)])
  have hu : (0 : ℝ) < 1 + (2 * q - 1) / 2 := by linarith
  have hfrac : (0 : ℝ) < (2 * q - 1) / 2 / (1 + (2 * q - 1) / 2) := by positivity
  have hlow : (2 * q - 1) / 2 / (1 + (2 * q - 1) / 2) ≤ 1 - Real.exp (-((2 * q - 1) / 2)) := by
    have h2 : (2 * q - 1) / 2 / (1 + (2 * q - 1) / 2) + 1 / (1 + (2 * q - 1) / 2) = 1 := by
      rw [← add_div, div_eq_one_iff_eq (ne_of_gt hu)]
      ring
    linarith
  have hr1 : Real.exp (-((2 * q - 1) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  refine le_trans (sum_Ico_pow_le hr0 hr1 K) ?_
  have hinv := one_div_le_one_div_of_le hfrac hlow
  rw [one_div_div] at hinv
  calc (1 - Real.exp (-((2 * q - 1) / 2)))⁻¹ = 1 / (1 - Real.exp (-((2 * q - 1) / 2))) :=
        (one_div _).symm
    _ ≤ (1 + (2 * q - 1) / 2) / ((2 * q - 1) / 2) := hinv
    _ = 1 + 2 / (2 * q - 1) := by
        rw [add_div, div_self (ne_of_gt hγ), one_div_div]
        ring

/-- **The upper bound, uniformly in `q`, with the `min`.**  Absolute `C`, and `x₀ = 4`:
`E‖S(x)‖^{2q} ≤ C·min{3 + log log x, 2 + 2/(2q-1)}^{2q}·(log x)^{q(2q-1)}` for `½ < q ≤ 1`, `x ≥ 4`.
At fixed `q` the second branch of the `min` is a constant, so
`RMF.exists_integral_rpow_norm_weightedRademacherSum_le` follows from it, with the explicit
`q`-dependence `C·(2 + 2/(2q-1))^{2q}` and with `x₀ = 4`. -/
theorem exists_integral_rpow_norm_weightedRademacherSum_le_uniform_min :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ q x : ℝ, 1 / 2 < q → q ≤ 1 → 4 ≤ x →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * (min (3 + Real.log (Real.log x)) (2 + 2 / (2 * q - 1))) ^ (2 * q)
              * (Real.log x) ^ (q * (2 * q - 1)) := by
  obtain ⟨C, hC, h⟩ := exists_integral_rpow_norm_weightedRademacherSum_le_capped
  refine ⟨C, hC, ?_⟩
  intro Ω _ X μ hX q x hq0 hq1 hx
  have hxe : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hll : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hq2 : (0 : ℝ) < 2 * q - 1 := by linarith
  have hGnn : (0 : ℝ) ≤ min (Real.log (Real.log x) + 2) (1 + 2 / (2 * q - 1)) :=
    le_min (by linarith) (by positivity)
  have hbound := h Ω X μ hX q x (min (Real.log (Real.log x) + 2) (1 + 2 / (2 * q - 1)))
    (by linarith) hq1 hx hGnn
    (le_min (sum_Ico_exp_le_log_log (by linarith) hq1 hxe _ (min_le_left _ _))
      (sum_Ico_exp_le_inv hq0 _))
  have hrw : (1 : ℝ) + min (Real.log (Real.log x) + 2) (1 + 2 / (2 * q - 1))
      = min (3 + Real.log (Real.log x)) (2 + 2 / (2 * q - 1)) := by
    rw [← min_add_add_left]
    congr 1 <;> ring
  rwa [hrw] at hbound

/-- **The upper bound at fixed `½ < q < 1`**: `E‖S(x)‖^{2q} ≪_q (log x)^{q(2q-1)}`.

A corollary of the uniform bound with the `min`: at fixed `q` the second branch is the constant
`2 + 2/(2q-1)`, so `C` is explicit in `q` given the absolute constant, and `x₀ = 4`. -/
theorem exists_integral_rpow_norm_weightedRademacherSum_le {q : ℝ}
    (hq0 : 1 / 2 < q) (hq1 : q < 1) :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * (Real.log x) ^ (q * (2 * q - 1)) := by
  obtain ⟨C, hC, h⟩ := exists_integral_rpow_norm_weightedRademacherSum_le_uniform_min
  have hq2 : (0 : ℝ) < 2 * q - 1 := by linarith
  have hpos : (0 : ℝ) < 2 + 2 / (2 * q - 1) := by positivity
  refine ⟨C * (2 + 2 / (2 * q - 1)) ^ (2 * q), 4,
    mul_pos hC (Real.rpow_pos_of_pos hpos _), ?_⟩
  intro Ω _ X μ hX x hx
  have hxe : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  refine le_trans (h Ω X μ hX q x hq0 hq1.le hx) ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC.le)
    (Real.rpow_nonneg (by linarith) _)
  exact Real.rpow_le_rpow (le_min (by linarith [Real.log_nonneg hL1]) hpos.le)
    (min_le_right _ _) (by linarith)

end RMF
