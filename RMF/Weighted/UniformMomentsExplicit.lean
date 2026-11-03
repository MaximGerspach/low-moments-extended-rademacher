/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfInterpExplicit
import RMF.Weighted.AboveHalfJensenExplicit
import RMF.Weighted.AboveHalfChaosCellsExplicit
import RMF.Weighted.UHalfQExplicit
import RMF.Weighted.MidNumeralExplicit

/-!
# The uniform upper bounds with the constant `25`

The uniform upper bounds on `E|S(x)|^{2q}`, `Λ = log log x`, with the constant `25` for every
`x ≥ 3` (`RMF.weighted_rademacher_moments_upper_uniform_explicit`): below `½` the bound (U),
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`; at `½` the bound (H), `E|S(x)| ≤ 10Λ^{3/4}`; above
`½` interpolation, the Jensen regime or the chaos regime.
-/

open MeasureTheory

namespace RMF

/-! ### Interpolation near `q = ½` and below `Λ = 11.5` -/

set_option maxHeartbeats 1000000 in
-- three cases, each linear once the tangents are in
/-- **Interpolation gives the constant `25`** where `(2q - 1)Λ ≤ 1` or `Λ ≤ 11.5`: for `½ < q ≤ 1`
and `x ≥ 3`, `Λ = log log x`,
`(10Λ^{3/4})^{2-2q}(1 + log x)^{2q-1} ≤ 25(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}`.  In
exponents, with `δ = 2q - 1`: `log(1 + log x) ≤ Λ + 1/log x`, and for `δΛ > 1` the concave
`(3/4)log δ + 5.75δ(1 - δ)` is below its tangents at `δ₀ = 0.3352`. -/
lemma interp_le_twentyfive {x q : ℝ} (hx : 3 ≤ x) (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (h : (2 * q - 1) * Real.log (Real.log x) ≤ 1 ∨ Real.log (Real.log x) ≤ 23 / 2) :
    (10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ^ (2 - 2 * q) * (1 + Real.log x) ^ (2 * q - 1)
      ≤ 25 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)) := by
  have h3 : (10986 / 10000 : ℝ) ≤ Real.log 3 := by interval_decide (trust := kernel)
  have hL3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  set L := Real.log x with hLdef
  have hL1 : 1 < L := by linarith
  set Λ := Real.log L with hΛdef
  have hΛ0 : 0 < Λ := Real.log_pos hL1
  have hLe : L = Real.exp Λ := (Real.exp_log (by linarith)).symm
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hδ1 : 2 * q - 1 ≤ 1 := by linarith
  have hq : q = (1 + (2 * q - 1)) / 2 := by ring
  set δ := 2 * q - 1 with hδdef
  -- the numerals
  have n10 : Real.log 10 ≤ 2.302586 := by interval_decide (trust := kernel)
  have n25 : 3.218875 ≤ Real.log 25 := by interval_decide (trust := kernel)
  have n7 : Real.log 7 ≤ 1.94592 := by interval_decide (trust := kernel)
  have n115 : Real.log (23 / 2) ≤ 2.44235 := by interval_decide (trust := kernel)
  have nd0 : Real.log (419 / 1250) ≤ -1.093 := by interval_decide (trust := kernel)
  have nd1 : Real.log (9 / 25) ≤ -1.0216 := by interval_decide (trust := kernel)
  have n3 : -2.3645 ≤ Real.log (Real.log (Real.log 3)) := by interval_decide (trust := kernel)
  have ne1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have ne7 : (1096 : ℝ) ≤ Real.exp 7 := by interval_decide (trust := kernel)
  -- `log Λ ≥ -2.3645`
  have hlogΛ : -2.3645 ≤ Real.log Λ := by
    have h1 : Real.log (Real.log 3) ≤ Λ := Real.log_le_log (by linarith) hL3
    have h2 : Real.log (Real.log (Real.log 3)) ≤ Real.log Λ :=
      Real.log_le_log (Real.log_pos (by linarith)) h1
    linarith
  -- `log(1 + L) ≤ Λ + 1/L`
  have hlog1L : Real.log (1 + L) ≤ Λ + 1 / L := by
    have e : 1 + L = L * (1 + 1 / L) := by field_simp; ring
    rw [e, Real.log_mul (by linarith) (by positivity)]
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / L)
    linarith
  have hinvL : 1 / L ≤ 1 / 1.0986 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- both sides as exponentials
  set m := min δ⁻¹ Λ with hmdef
  have hm0 : 0 < m := lt_min (inv_pos.2 hδ0) hΛ0
  have hbase : 0 < 10 * Λ ^ (3 / 4 : ℝ) := by positivity
  rw [show 2 - 2 * q = 1 - δ by rw [hδdef]; ring, Real.rpow_def_of_pos hbase,
    Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 1 + L),
    Real.rpow_def_of_pos (by linarith : 0 < L),
    Real.rpow_def_of_pos hm0, ← Real.exp_add, ← Real.exp_add,
    show (25 : ℝ) = Real.exp (Real.log 25) by rw [Real.exp_log (by norm_num)], ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hΛ0, ← hΛdef, hq]
  have hA : Real.log (1 + L) * δ ≤ (Λ + 1 / L) * δ := mul_le_mul_of_nonneg_right hlog1L hδ0.le
  have hd1 : 0 ≤ 1 - δ := by linarith
  rcases le_or_gt (δ * Λ) 1 with hc | hc
  · -- `δΛ ≤ 1`: `m = Λ`
    have hmΛ : m = Λ := min_eq_right (by
      rw [le_inv_comm₀ hΛ0 hδ0, ← one_div, le_div_iff₀ hΛ0]; linarith)
    rw [hmΛ]
    have h1 := mul_le_mul_of_nonneg_left hlogΛ hδ0.le
    have h2 := mul_le_mul_of_nonneg_left hinvL hδ0.le
    have h3 : δ * Λ * (1 - δ) ≤ 1 := by nlinarith
    nlinarith
  · -- `δΛ > 1`: `m = 1/δ`
    have hmδ : m = δ⁻¹ := min_eq_left (by
      rw [inv_le_comm₀ hδ0 hΛ0, ← one_div, div_le_iff₀ hΛ0]; linarith)
    rw [hmδ, Real.log_inv]
    have hΛ1 : 1 ≤ Λ := by nlinarith
    have hdd : 0 ≤ δ * (1 - δ) := mul_nonneg hδ0.le hd1
    rcases h with h | hΛu
    · linarith
    rcases le_or_gt Λ 7 with h7 | h7
    · -- `Λ ≤ 7`: the tangent at `δ₀ = 9/25`
      have hlΛ : Real.log Λ ≤ Real.log 7 := Real.log_le_log hΛ0 h7
      have hL : Real.exp 1 ≤ L := by rw [hLe]; exact Real.exp_le_exp.2 hΛ1
      have hinv : 1 / L ≤ 1 / 2.718 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      have ht : Real.log δ ≤ Real.log (9 / 25) + δ / (9 / 25) - 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < δ / (9 / 25) by positivity)
        rw [Real.log_div hδ0.ne' (by norm_num)] at this
        linarith
      have e1 := mul_le_mul_of_nonneg_right hlΛ hd1
      have e2 := mul_le_mul_of_nonneg_left hinv hδ0.le
      have e3 : Λ * δ * (1 - δ) ≤ 7 * δ * (1 - δ) := by nlinarith
      have e4 : δ * (1 - δ) ≤ 1 / 4 := by nlinarith [sq_nonneg (δ - 1 / 2)]
      nlinarith
    · -- `7 < Λ ≤ 11.5`: the tangents at `δ₀ = 419/1250`
      have hlΛ : Real.log Λ ≤ Real.log (23 / 2) := Real.log_le_log hΛ0 hΛu
      have hL : Real.exp 7 ≤ L := by rw [hLe]; exact Real.exp_le_exp.2 h7.le
      have hinv : 1 / L ≤ 1 / 1096 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      have ht : Real.log δ ≤ Real.log (419 / 1250) + δ / (419 / 1250) - 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < δ / (419 / 1250) by positivity)
        rw [Real.log_div hδ0.ne' (by norm_num)] at this
        linarith
      have hquad : δ * (1 - δ) ≤ 419 / 1250 * (1 - 419 / 1250)
          + (1 - 2 * (419 / 1250)) * (δ - 419 / 1250) := by nlinarith [sq_nonneg (δ - 419 / 1250)]
      have e1 := mul_le_mul_of_nonneg_right hlΛ hd1
      have e2 := mul_le_mul_of_nonneg_left hinv hδ0.le
      have e3 : Λ * δ * (1 - δ) ≤ 23 / 2 * δ * (1 - δ) := by nlinarith
      nlinarith

/-! ### The theorem -/

/-- **The uniform upper bounds with the constant `25`**: for every `x ≥ 3`, with
`Λ = log log x`,

* `E|S(x)|^{2q} ≤ 25·min(Λ, 1/(1 - 2q))·Λ^{-q/2}` for `0 < q < ½`, from the bound (U)
  (`RMF.integral_rpow_weightedRademacherSum_le_u`);
* `E|S(x)| ≤ 25Λ^{3/4}`, from the bound (H) with `10` in place of `25`
  (`RMF.integral_norm_weightedRademacherSum_le_ten_of_three_le`);
* `E|S(x)|^{2q} ≤ 25(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}` for `½ < q ≤ 1`: interpolation
  where `(2q - 1)Λ ≤ 1` or `Λ ≤ 11.5` (`RMF.interp_le_twentyfive`), else the Jensen regime
  (`RMF.integral_rpow_weightedRademacherSum_le_aboveJensen`, `q ≥ 0.50015`) or the chaos regime
  (`RMF.integral_rpow_weightedRademacherSum_le_aboveChaos`, `q ≤ 0.50015`). -/
theorem weighted_rademacher_moments_upper_uniform_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ 25 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))) ∧
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
          ≤ 25 * Real.log (Real.log x) ^ (3 / 4 : ℝ) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ 25 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) := by
  intro Ω _ X μ hX x hx
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have hlogx : 1 < Real.log x := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hx)
  have hL0 : 0 < Real.log (Real.log x) := Real.log_pos hlogx
  refine ⟨fun q hq0 hq2 => ?_, ?_, fun q hq2 hq1 => ?_⟩
  · -- `0 < q < ½`: (U)
    have hb : 0 < 1 - 2 * q := by linarith
    have hmin : ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        ≤ min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ := by
      refine le_min ?_ (inv_anti₀ hb (le_add_of_nonneg_left (inv_nonneg.2 hL0.le)))
      calc ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ ≤ (Real.log (Real.log x))⁻¹⁻¹ :=
            inv_anti₀ (inv_pos.2 hL0) (le_add_of_nonneg_right hb.le)
        _ = Real.log (Real.log x) := inv_inv _
    have hpow : 0 ≤ Real.log (Real.log x) ^ (-(q / 2)) := Real.rpow_nonneg hL0.le _
    calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
            * Real.log (Real.log x) ^ (-(q / 2)) :=
          integral_rpow_weightedRademacherSum_le_u hX hx hq0 hq2.le
      _ ≤ 25 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
            * Real.log (Real.log x) ^ (-(q / 2))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmin hpow) (by norm_num)
  · -- `q = ½`: (H)
    exact le_trans (integral_norm_weightedRademacherSum_le_ten_of_three_le hX hx)
      (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hL0.le _))
  · -- `½ < q ≤ 1`
    by_cases hA : (2 * q - 1) * Real.log (Real.log x) ≤ 1 ∨ Real.log (Real.log x) ≤ 23 / 2
    · exact le_trans (integral_rpow_weightedRademacherSum_le_interp hX hx hq2.le hq1)
        (interp_le_twentyfive hx hq2 hq1 hA)
    push Not at hA
    obtain ⟨hδΛ, hΛ⟩ := hA
    have hδ : 0 < 2 * q - 1 := by linarith
    have hm : min (2 * q - 1)⁻¹ (Real.log (Real.log x)) = (2 * q - 1)⁻¹ := by
      refine min_eq_left ?_
      rw [inv_le_comm₀ hδ hL0, ← one_div, div_le_iff₀ hL0]
      linarith
    have e : 25 * (Real.log x ^ (q * (2 * q - 1))
          * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
        = 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
      rw [hm, Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
      ring
    rw [e]
    rcases le_or_gt (50015 / 100000) q with hJ | hC
    · exact integral_rpow_weightedRademacherSum_le_aboveJensen hX hJ hq1 hx hΛ.le hδΛ.le
    · exact integral_rpow_weightedRademacherSum_le_aboveChaos hX hq2 hC.le hx hδΛ.le

end RMF
