/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperSieve
import RMF.Reduction.UpperAveragedLeaves

/-!
# Harper's upper bound at the sieve constant: the leaves

The counterpart of `RMF/Reduction/UpperAveragedLeaves.lean` at the sieve constant.  The chaos side
is the same; the reduction constant is `RMF.reductionSieveConst q`, with base
`1.001e^{-γ}/(2π) ≤ 0.08947` (`RMF.sieveConst_div_two_pi_le`, from `γ ≥ 0.577215`) in place of
`3/(2π) ≤ 0.47747`.

* `RMF.tsum_lineWeight_rpow_le_six`: the periodisation sum as six terms and the integral tail;
* `RMF.reductionSieveConst_le_certRSieve`: the reduction constant below its certificate function;
* `RMF.chaosAveragedConst_le_of_end`: the chaos constant on an interval of `q` from two endpoint
  numerals;
* `RMF.upper_sieve_le_of_end`: one interval of the certificate.

The certified numeral is assembled in `RMF/Reduction/UpperSieveNumeral.lean`.
-/

namespace RMF

/-! ### The reduction constant -/

/-- `1.001e^{-γ}/(2π) ≤ 0.08947`, from `γ ≥ 0.577215` (`hγ_lo`) and `π > 3.141592`. -/
lemma sieveConst_div_two_pi_le : sieveConst / (2 * Real.pi) ≤ 8947 / 100000 := by
  have hpi := Real.pi_gt_d6
  have hγ := hγ_lo
  have h : Real.exp (-(577215 / 1000000)) ≤ 5615 / 10000 := by
    interval_decide (trust := kernel)
  have hE : Real.exp (-Real.eulerMascheroniConstant) ≤ 5615 / 10000 :=
    le_trans (Real.exp_le_exp.2 (by norm_num at hγ ⊢; linarith)) h
  unfold sieveConst
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The periodisation sum in six terms**: for `q > 1/2`, `∑_{n ∈ ℤ} w_n^q ≤ 2(e^{q log 4}
+ Σ_{d=1}^5 e^{-q log(1/4 + d²)} + e^{(1-2q) log 5}/(2q - 1))`
(`RMF.tsum_lineWeight_rpow_eq`, `RMF.tsum_quarter_add_sq_rpow_le`). -/
lemma tsum_lineWeight_rpow_le_six {q : ℝ} (hq : 1 / 2 < q) :
    ∑' n : ℤ, lineWeight n ^ q ≤ 2 * (Real.exp (q * Real.log 4)
      + Real.exp (-(q * Real.log (5 / 4))) + Real.exp (-(q * Real.log (17 / 4)))
      + Real.exp (-(q * Real.log (37 / 4))) + Real.exp (-(q * Real.log (65 / 4)))
      + Real.exp (-(q * Real.log (101 / 4)))
      + Real.exp ((1 - 2 * q) * Real.log 5) / (2 * q - 1)) := by
  have e0 : ((1 / 4 + ((0 : ℕ) : ℝ) ^ 2)⁻¹) ^ q = Real.exp (q * Real.log 4) := by
    rw [← rpow_eq_exp_mul_log (x := 4) (by norm_num)]
    norm_num
  have e1 : ((1 / 4 + ((1 : ℕ) : ℝ) ^ 2)⁻¹) ^ q = Real.exp (-(q * Real.log (5 / 4))) := by
    rw [inv_rpow_eq_exp_neg (by positivity)]
    norm_num
  have e2 : ((1 / 4 + ((2 : ℕ) : ℝ) ^ 2)⁻¹) ^ q = Real.exp (-(q * Real.log (17 / 4))) := by
    rw [inv_rpow_eq_exp_neg (by positivity)]
    norm_num
  have e3 : ((1 / 4 + ((3 : ℕ) : ℝ) ^ 2)⁻¹) ^ q = Real.exp (-(q * Real.log (37 / 4))) := by
    rw [inv_rpow_eq_exp_neg (by positivity)]
    norm_num
  have e4 : ((1 / 4 + ((4 : ℕ) : ℝ) ^ 2)⁻¹) ^ q = Real.exp (-(q * Real.log (65 / 4))) := by
    rw [inv_rpow_eq_exp_neg (by positivity)]
    norm_num
  have e5 : ((1 / 4 + ((5 : ℕ) : ℝ) ^ 2)⁻¹) ^ q = Real.exp (-(q * Real.log (101 / 4))) := by
    rw [inv_rpow_eq_exp_neg (by positivity)]
    norm_num
  have hsum : ∑ d ∈ Finset.range 6, ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q
      = Real.exp (q * Real.log 4) + Real.exp (-(q * Real.log (5 / 4)))
        + Real.exp (-(q * Real.log (17 / 4))) + Real.exp (-(q * Real.log (37 / 4)))
        + Real.exp (-(q * Real.log (65 / 4))) + Real.exp (-(q * Real.log (101 / 4))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [e0, e1, e2, e3, e4, e5]
  have htail : (5 : ℝ) ^ (1 - 2 * q) / (2 * q - 1)
      = Real.exp ((1 - 2 * q) * Real.log 5) / (2 * q - 1) := by
    rw [rpow_eq_exp_mul_log (x := 5) (by norm_num)]
  rw [tsum_lineWeight_rpow_eq hq]
  have h := tsum_quarter_add_sq_rpow_le hq
  rw [hsum, htail] at h
  linarith

/-- **The sieve certificate function of the reduction constant**: `e^{q log(8947/10⁵)}`
`·2·(e^{q log 4} + Σ_{d=1}^5 e^{-q log(1/4 + d²)} + e^{(1-2q) log 5}/(2q - 1))`. -/
noncomputable def certRSieve (q : ℝ) : ℝ :=
  Real.exp (q * Real.log (8947 / 100000)) * (2 * (Real.exp (q * Real.log 4)
    + Real.exp (-(q * Real.log (5 / 4))) + Real.exp (-(q * Real.log (17 / 4)))
    + Real.exp (-(q * Real.log (37 / 4))) + Real.exp (-(q * Real.log (65 / 4)))
    + Real.exp (-(q * Real.log (101 / 4)))
    + Real.exp ((1 - 2 * q) * Real.log 5) / (2 * q - 1)))

/-- **The reduction constant below its certificate function**: `reductionSieveConst q ≤
certRSieve q` for `q > 1/2`. -/
lemma reductionSieveConst_le_certRSieve {q : ℝ} (hq : 1 / 2 < q) :
    reductionSieveConst q ≤ certRSieve q := by
  have hq0 : 0 ≤ q := by linarith
  have h1 : (sieveConst / (2 * Real.pi)) ^ q ≤ Real.exp (q * Real.log (8947 / 100000)) := by
    rw [← rpow_eq_exp_mul_log (x := 8947 / 100000) (by norm_num)]
    exact Real.rpow_le_rpow (div_nonneg sieveConst_pos.le (by positivity))
      sieveConst_div_two_pi_le hq0
  unfold reductionSieveConst certRSieve
  exact mul_le_mul h1 (tsum_lineWeight_rpow_le_six hq)
    (tsum_nonneg fun n => Real.rpow_nonneg (lineWeight_nonneg n) q) (Real.exp_pos _).le

/-! ### One interval of `q` -/

/-- **The chaos constant on an interval of `q`**: `RMF.chaosAveragedConst_le_cert` with both
branches at the worse endpoint (`RMF.certD_le_end`). -/
lemma chaosAveragedConst_le_of_end {a b q A lam T κ β LB ℓκ ℓKT cb Ub e j d : ℝ}
    (haq : a ≤ q) (hqb : q ≤ b) (hb1 : b ≤ 1) (hq0 : 0 ≤ q)
    (hA : 0 ≤ A) (hLA : LB - 2 * A ≤ 0) (hlam : 0 < lam) (hT : 4 < T) (hκ : 1 ≤ κ)
    (hβ : 1 / 2 < β) (hβ2 : β ≤ 2) (hLB : 501 / 10 + Real.log (2 * β / (2 * β - 1)) ≤ LB)
    (hℓκ : Real.log κ ≤ ℓκ) (hℓKT : Real.log (11816 / 10000 * T) ≤ ℓKT)
    (hc1 : 1 ≤ (1 + 1 / lam) * (100504 / 100000) * ((1 + 1 / 10000000) * (11816 / 10000)
      * (1 + β / (4 * κ)) / (1 - 2 * β / T) * (17811 / 10000)))
    (hc : (1 + 1 / lam) * (100504 / 100000) * ((1 + 1 / 10000000) * (11816 / 10000)
      * (1 + β / (4 * κ)) / (1 - 2 * β / T) * (17811 / 10000)) ≤ cb)
    (hU : (A + (3 * (1 / 15000) + β * ℓκ + β / κ + β * (693148 / 1000000) + (2 - β) + 45 / 32
      + 2 * (2658681 / 1000000) + β * (1 + 693148 / 1000000 + 3912024 / 1000000)
      + 2 * β * ℓKT)) * (1 - a) ≤ Ub)
    (he : (1 ≤ Ub ∧ e = b) ∨ (0 < Ub ∧ Ub ≤ 1 ∧ e = a))
    (hJ : Real.exp (b * Real.log (17811 / 10000 * (1 + lam))) ≤ j)
    (hD : Real.exp (b * Real.log cb) * (Real.exp (e * Real.log Ub)
        + Real.exp ((1 - b) * (LB - 2 * A))
          * (Real.exp (b * Real.log (Ub + 1)) * (1156519 / 1000000) + 181016 / 1000000))
      + 135336 / 1000000 * Real.exp ((1 - b) * (LB - 2 * A))
        * Real.exp (b * Real.log (17811 / 10000)) ≤ d) :
    chaosAveragedConst (fun _ => A) (fun _ => lam) (fun _ => T) (fun _ => κ) (fun _ => β)
      (1 / 100) (1001 / 1000) 1000000 q ≤ 1001 / 1000 * max j d := by
  have hq1 : q ≤ 1 := le_trans hqb hb1
  have hsb0 : 0 ≤ A + (3 * (1 / 15000) + β * ℓκ + β / κ + β * (693148 / 1000000) + (2 - β)
      + 45 / 32 + 2 * (2658681 / 1000000) + β * (1 + 693148 / 1000000 + 3912024 / 1000000)
      + 2 * β * ℓKT) := by
    have h1 : 0 ≤ ℓκ := le_trans (Real.log_nonneg hκ) hℓκ
    have h2 : 0 ≤ ℓKT := le_trans (Real.log_nonneg (by nlinarith)) hℓKT
    have h3 : 0 ≤ β / κ := div_nonneg (by linarith) (by linarith)
    have h4 : 0 ≤ β * ℓκ := mul_nonneg (by linarith) h1
    have h5 : 0 ≤ 2 * β * ℓKT := mul_nonneg (by linarith) h2
    have h6 : 0 ≤ β * (693148 / 1000000) := mul_nonneg (by linarith) (by norm_num)
    have h7 : 0 ≤ β * (1 + 693148 / 1000000 + 3912024 / 1000000) :=
      mul_nonneg (by linarith) (by norm_num)
    linarith
  have hC := chaosAveragedConst_le_cert (Af := fun _ => A) (lamf := fun _ => lam)
    (Tf := fun _ => T) (κf := fun _ => κ) (βf := fun _ => β) (k := 1001 / 1000) (q := q)
    (U := Ub) (LB := LB) (by norm_num) hq0 hq1 hA hlam hT hκ hβ hβ2 hLB hℓκ hℓKT
    (le_trans (mul_le_mul_of_nonneg_left (by linarith : 1 - q ≤ 1 - a) hsb0) hU)
  have hJq : Real.exp (q * Real.log (17811 / 10000 * (1 + lam))) ≤ j := by
    refine le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqb ?_)) hJ
    exact Real.log_nonneg (by nlinarith)
  have hDq := le_trans (certD_le_end (c := (1 + 1 / lam) * (100504 / 100000)
      * ((1 + 1 / 10000000) * (11816 / 10000) * (1 + β / (4 * κ)) / (1 - 2 * β / T)
        * (17811 / 10000)))
    (U := Ub) (LB := LB) (A := A) (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000)
    (EM2 := 135336 / 1000000) (N := 17811 / 10000) hq0 haq hqb hb1 hc1 hc he hLA (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)) hD
  exact le_trans hC (mul_le_mul_of_nonneg_left (max_le_max hJq hDq) (by norm_num))

/-- **One interval of the sieve certificate.**  At the reduction constant
`RMF.reductionSieveConst`: on `q ∈ [a, b] ⊆ (1/2, 1]`, at constant `A`, `λ`, `T`, `κ`, `β`,
`k·R(q)·chaosAveragedConst(q) + η ≤ B` follows from `R ≤ r` at base `8947/10⁵`, `J ≤ j`, `D ≤ d`
and `k²r·max(j, d) + η ≤ B`. -/
lemma upper_sieve_le_of_end {a b q A lam T κ β LB ℓκ ℓKT ia cb Ub e r j d B : ℝ}
    (ha : 1 / 2 < a) (haq : a ≤ q) (hqb : q ≤ b) (hb1 : b ≤ 1)
    (hA : 0 ≤ A) (hLA : LB - 2 * A ≤ 0) (hlam : 0 < lam) (hT : 4 < T) (hκ : 1 ≤ κ)
    (hβ : 1 / 2 < β) (hβ2 : β ≤ 2) (hLB : 501 / 10 + Real.log (2 * β / (2 * β - 1)) ≤ LB)
    (hℓκ : Real.log κ ≤ ℓκ) (hℓKT : Real.log (11816 / 10000 * T) ≤ ℓKT)
    (hia : (2 * a - 1)⁻¹ ≤ ia)
    (hc1 : 1 ≤ (1 + 1 / lam) * (100504 / 100000) * ((1 + 1 / 10000000) * (11816 / 10000)
      * (1 + β / (4 * κ)) / (1 - 2 * β / T) * (17811 / 10000)))
    (hc : (1 + 1 / lam) * (100504 / 100000) * ((1 + 1 / 10000000) * (11816 / 10000)
      * (1 + β / (4 * κ)) / (1 - 2 * β / T) * (17811 / 10000)) ≤ cb)
    (hU : (A + (3 * (1 / 15000) + β * ℓκ + β / κ + β * (693148 / 1000000) + (2 - β) + 45 / 32
      + 2 * (2658681 / 1000000) + β * (1 + 693148 / 1000000 + 3912024 / 1000000)
      + 2 * β * ℓKT)) * (1 - a) ≤ Ub)
    (he : (1 ≤ Ub ∧ e = b) ∨ (0 < Ub ∧ Ub ≤ 1 ∧ e = a))
    (hR : Real.exp (a * Real.log (8947 / 100000)) * (2 * (Real.exp (b * Real.log 4)
      + Real.exp (-(a * Real.log (5 / 4))) + Real.exp (-(a * Real.log (17 / 4)))
      + Real.exp (-(a * Real.log (37 / 4))) + Real.exp (-(a * Real.log (65 / 4)))
      + Real.exp (-(a * Real.log (101 / 4))) + Real.exp ((1 - 2 * a) * Real.log 5) * ia)) ≤ r)
    (hJ : Real.exp (b * Real.log (17811 / 10000 * (1 + lam))) ≤ j)
    (hD : Real.exp (b * Real.log cb) * (Real.exp (e * Real.log Ub)
        + Real.exp ((1 - b) * (LB - 2 * A))
          * (Real.exp (b * Real.log (Ub + 1)) * (1156519 / 1000000) + 181016 / 1000000))
      + 135336 / 1000000 * Real.exp ((1 - b) * (LB - 2 * A))
        * Real.exp (b * Real.log (17811 / 10000)) ≤ d)
    (hB : 1001 / 1000 * r * (1001 / 1000 * max j d) + 1 / 100 ≤ B) :
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => A) (fun _ => lam)
        (fun _ => T) (fun _ => κ) (fun _ => β) (1 / 100) (1001 / 1000) 1000000 q + 1 / 100 ≤ B := by
  have hq0 : 0 ≤ q := by linarith
  have hden : 0 < 2 * q - 1 := by linarith
  -- the reduction constant
  have hRq : reductionSieveConst q ≤ r := by
    refine le_trans (reductionSieveConst_le_certRSieve (by linarith)) (le_trans ?_ hR)
    have t1 : Real.exp (q * Real.log (8947 / 100000)) ≤ Real.exp (a * Real.log (8947 / 100000)) :=
      Real.exp_le_exp.2
        (mul_le_mul_of_nonpos_right haq (Real.log_nonpos (by norm_num) (by norm_num)))
    have t2 : Real.exp (q * Real.log 4) ≤ Real.exp (b * Real.log 4) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num)))
    have t3 : ∀ x : ℝ, 1 ≤ x → Real.exp (-(q * Real.log x)) ≤ Real.exp (-(a * Real.log x)) :=
      fun x hx =>
        Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right haq (Real.log_nonneg hx)))
    have t4 : Real.exp ((1 - 2 * q) * Real.log 5) ≤ Real.exp ((1 - 2 * a) * Real.log 5) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num)))
    have t5 : (2 * q - 1)⁻¹ ≤ ia := le_trans (inv_anti₀ (by linarith) (by linarith)) hia
    have t45 : Real.exp ((1 - 2 * q) * Real.log 5) / (2 * q - 1)
        ≤ Real.exp ((1 - 2 * a) * Real.log 5) * ia := by
      rw [div_eq_mul_inv]
      exact mul_le_mul t4 t5 (inv_nonneg.2 hden.le) (Real.exp_pos _).le
    have h54 := t3 (5 / 4) (by norm_num)
    have h174 := t3 (17 / 4) (by norm_num)
    have h374 := t3 (37 / 4) (by norm_num)
    have h654 := t3 (65 / 4) (by norm_num)
    have h1014 := t3 (101 / 4) (by norm_num)
    have hsum0 : 0 ≤ 2 * (Real.exp (q * Real.log 4) + Real.exp (-(q * Real.log (5 / 4)))
        + Real.exp (-(q * Real.log (17 / 4))) + Real.exp (-(q * Real.log (37 / 4)))
        + Real.exp (-(q * Real.log (65 / 4))) + Real.exp (-(q * Real.log (101 / 4)))
        + Real.exp ((1 - 2 * q) * Real.log 5) / (2 * q - 1)) := by positivity
    unfold certRSieve
    refine mul_le_mul t1 ?_ hsum0 (Real.exp_pos _).le
    linarith
  -- the chaos constant
  have hCq := chaosAveragedConst_le_of_end haq hqb hb1 hq0 hA hLA hlam hT hκ hβ hβ2 hLB hℓκ hℓKT
    hc1 hc hU he hJ hD
  have hC0 := chaosAveragedConst_nonneg (Af := fun _ => A) (lamf := fun _ => lam)
    (Tf := fun _ => T) (κf := fun _ => κ) (βf := fun _ => β) (δ := 1 / 100) (L₀ := 1000000)
    (q := q)
    (by norm_num : (0 : ℝ) ≤ 1001 / 1000) hlam.le
  have hr0 : 0 ≤ r := le_trans (reductionSieveConst_nonneg q) hRq
  have hmain : 1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => A)
      (fun _ => lam) (fun _ => T) (fun _ => κ) (fun _ => β) (1 / 100) (1001 / 1000) 1000000 q
      ≤ 1001 / 1000 * r * (1001 / 1000 * max j d) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hRq (by norm_num)) hCq hC0 (by positivity)
  linarith

end RMF
