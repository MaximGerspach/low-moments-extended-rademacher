/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfTowerExplicit

/-!
# The Jensen regime's cells above `q = ½`

`RMF.aboveTowerF` at `η' = 0.3`, `ε = 0.1` bounded over a cell `q ∈ [q_l, q_u]`, `Λ ≥ Λ₀`, every
piece at the end of the cell where it is largest, in `exp`/`log` form (the hats `RMF.topHat`,
`RMF.cenHat`, `RMF.bandHat`, `RMF.botHat`, `RMF.winCHat`, `RMF.bandConstHat`), so that a cell's
instance is a list of `interval_decide` checks; and the bottom's nine top windows bounded over a
range of `q` (`RMF.winNoSplitFull_le_cell`, `RMF.winSplitFull_le_cell`).

`RMF.above_cell_jensen`: `E|S(x)|^{2q} ≤ 25(2q-1)^{-3/4}(log x)^{q(2q-1)}` on a cell whose
numerals pass.
-/

open MeasureTheory

namespace RMF

/-! ### Powers over a cell of exponents -/

/-- `x^q ≤ N` for `q ∈ [q_l, q_u]` once `e^{q_l log x} ≤ N` and `e^{q_u log x} ≤ N`. -/
lemma rpow_le_of_exp_log_both {x q ql qu N : ℝ} (hx : 0 < x) (hql : ql ≤ q) (hqu : q ≤ qu)
    (hl : Real.exp (ql * Real.log x) ≤ N) (hu : Real.exp (qu * Real.log x) ≤ N) : x ^ q ≤ N := by
  rw [Real.rpow_def_of_pos hx, mul_comm]
  rcases le_total 0 (Real.log x) with h | h
  · exact le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqu h)) hu
  · exact le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hql h)) hl

/-- `x^q ≤ e^{q_u log x}` for `x ≥ 1`, `q ≤ q_u`. -/
lemma rpow_le_exp_of_one_le {x q qu : ℝ} (hx : 1 ≤ x) (hqu : q ≤ qu) :
    x ^ q ≤ Real.exp (qu * Real.log x) := by
  rw [Real.rpow_def_of_pos (by linarith), mul_comm]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqu (Real.log_nonneg hx))

/-- `x^q ≤ e^{q_l log x}` for `0 < x ≤ 1`, `q_l ≤ q`. -/
lemma rpow_le_exp_of_le_one {x q ql : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) (hql : ql ≤ q) :
    x ^ q ≤ Real.exp (ql * Real.log x) := by
  rw [Real.rpow_def_of_pos hx0, mul_comm]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hql (Real.log_nonpos hx0.le hx))

/-- `a = q(2q-1)` is monotone on `q ≥ ½`. -/
lemma mul_two_mul_sub_one_le {q q' : ℝ} (hq : 1 / 2 ≤ q) (hqq : q ≤ q') :
    q * (2 * q - 1) ≤ q' * (2 * q' - 1) := by nlinarith

lemma inv_pi_le : Real.pi⁻¹ ≤ 0.318311 := by
  have := Real.pi_gt_d6
  rw [inv_le_comm₀ Real.pi_pos (by norm_num)]
  linarith

/-! ### The pieces over a cell -/

/-- `RMF.topPhi` over the cell `[q_l, q_u]`. -/
noncomputable def topHat (ql qu : ℝ) : ℝ :=
  Real.exp ((2 * qu - 1) * (1 / 2) * (0.2732 + (2 - 2 * ql) * (1 / 3))
    + (1 - ql) * Real.log (1.001 * Real.exp (10 / 3))) * 1.0052

lemma topPhi_le_topHat {q ql qu : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) : topPhi q ≤ topHat ql qu := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 ≤ Real.log (1.001 * Real.exp (10 / 3)) := Real.log_nonneg (by
    have := Real.add_one_le_exp (10 / 3 : ℝ); nlinarith)
  rw [topPhi, topHat, pfC1, ← Real.exp_mul, Real.rpow_def_of_pos (by positivity),
    ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by norm_num)
  have e1 : q * (2 * q - 1) * (0.2732 + (2 - 2 * q) / 3) * (2 * q)⁻¹
      = (2 * q - 1) * (1 / 2) * (0.2732 + (2 - 2 * q) * (1 / 3)) := by
    field_simp
  rw [e1, mul_comm (Real.log _) (1 - q)]
  have h1 : 0 ≤ 2 * q - 1 := by linarith
  have h2 : 0 ≤ 0.2732 + (2 - 2 * q) * (1 / 3) := by nlinarith
  have h3 : (2 * q - 1) * (1 / 2) * (0.2732 + (2 - 2 * q) * (1 / 3))
      ≤ (2 * qu - 1) * (1 / 2) * (0.2732 + (2 - 2 * ql) * (1 / 3)) := by
    have : (2 * q - 1) * (1 / 2) ≤ (2 * qu - 1) * (1 / 2) := by linarith
    have : 0.2732 + (2 - 2 * q) * (1 / 3) ≤ 0.2732 + (2 - 2 * ql) * (1 / 3) := by linarith
    exact mul_le_mul (by linarith) (by linarith) h2 (by linarith)
  have h4 : (1 - q) * Real.log (1.001 * Real.exp (10 / 3))
      ≤ (1 - ql) * Real.log (1.001 * Real.exp (10 / 3)) :=
    mul_le_mul_of_nonneg_right (by linarith) hlog
  linarith

/-- `RMF.cenClean` over the cell `[q_l, q_u]`. -/
noncomputable def cenHat (ql qu : ℝ) : ℝ :=
  (1.0062 * ((2 * qu - 1) * (1 + (2 - 2 * qu) * (1 / 3)))) ^ 2
      * (1 + Real.exp (1.0062 * ((2 * qu - 1) * (1 + (2 - 2 * qu) * (1 / 3))))) ^ 2
      * (0.318311 * (1 / 4))
    + 0.5158 * 0.318311 * 1.0002 * (1 + (Real.exp (2 * (1 - ql) * 0.5158) - 1) * (1 / 3))

lemma cenClean_le_cenHat {q ql qu : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) : cenClean q ≤ cenHat ql qu := by
  have hpi := inv_pi_le
  have hpi0 : 0 < Real.pi := Real.pi_pos
  set A := (2 * q - 1) * (1 + (2 - 2 * q) / 3) with hAdef
  set Au := (2 * qu - 1) * (1 + (2 - 2 * qu) * (1 / 3)) with hAudef
  have hA0 : 0 ≤ A := mul_nonneg (by linarith) (by linarith)
  have hAA : A ≤ Au := by rw [hAdef, hAudef]; nlinarith
  have h1 : (1.0062 * A) ^ 2 ≤ (1.0062 * Au) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : (1 + Real.exp (1.0062 * A)) ^ 2 ≤ (1 + Real.exp (1.0062 * Au)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_le_exp.2 (show 1.0062 * A
      ≤ 1.0062 * Au by linarith)]) 2
  have h3 : (1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3)
      ≤ (1 + (Real.exp (2 * (1 - ql) * 0.5158) - 1) * (1 / 3)) := by
    have := Real.exp_le_exp.2 (show 2 * (1 - q) * 0.5158 ≤ 2 * (1 - ql) * 0.5158 by nlinarith)
    linarith
  have h30 : 0 ≤ 1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3 := by
    have := Real.one_le_exp (show 0 ≤ 2 * (1 - q) * 0.5158 by nlinarith)
    linarith
  rw [cenClean, cenHat, ← hAdef, ← hAudef]
  have e1 : (1.0062 * A) ^ 2 * (1 + Real.exp (1.0062 * A)) ^ 2 / (4 * Real.pi)
      = (1.0062 * A) ^ 2 * (1 + Real.exp (1.0062 * A)) ^ 2 * (Real.pi⁻¹ * (1 / 4)) := by
    field_simp
  have e2 : 0.5158 / Real.pi * 1.0002 * (1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3)
      = 0.5158 * Real.pi⁻¹ * 1.0002 * (1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3) := by
    field_simp
  rw [e1, e2]
  have hpi0' : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 hpi0.le
  refine add_le_add ?_ ?_
  · exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity))
      (mul_le_mul_of_nonneg_right hpi (by norm_num)) (by positivity) (by positivity)
  · exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpi (by norm_num))
      (by norm_num)) h3 h30 (by positivity)

/-- `pfC1` over the cell. -/
noncomputable def pfC1Hat (ql qu : ℝ) : ℝ :=
  Real.exp (qu * (2 * qu - 1) * (0.2732 + (2 - 2 * ql) * (1 / 3)))

/-- `pfC2` over the cell. -/
noncomputable def pfC2Hat (ql qu : ℝ) : ℝ :=
  Real.exp (qu * (2 * qu - 1) * (0.2915 + (2 - 2 * ql) * (1 / 3)))

lemma pfC1_le_pfC1Hat {q ql qu : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) : pfC1 q ≤ pfC1Hat ql qu := by
  rw [pfC1, pfC1Hat]
  refine Real.exp_le_exp.2 (mul_le_mul (mul_two_mul_sub_one_le (by linarith) hqu)
    (by linarith) (by linarith) (mul_nonneg (by linarith) (by linarith)))

lemma pfC2_le_pfC2Hat {q ql qu : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) : pfC2 q ≤ pfC2Hat ql qu := by
  rw [pfC2, pfC2Hat]
  refine Real.exp_le_exp.2 (mul_le_mul (mul_two_mul_sub_one_le (by linarith) hqu)
    (by linarith) (by linarith) (mul_nonneg (by linarith) (by linarith)))

/-- `x^q ≤ e^{q_u log X}` for `0 ≤ x ≤ X`, `1 ≤ X`. -/
lemma rpow_le_exp_hi {x X q qu : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hX : 1 ≤ X) (hq : 0 ≤ q)
    (hqu : q ≤ qu) : x ^ q ≤ Real.exp (qu * Real.log X) :=
  le_trans (Real.rpow_le_rpow hx hxX hq) (rpow_le_exp_of_one_le hX hqu)

/-- `x^q ≤ e^{q_l log X}` for `0 ≤ x ≤ X ≤ 1`, `X > 0`. -/
lemma rpow_le_exp_lo {x X q ql : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hX0 : 0 < X) (hX : X ≤ 1)
    (hq : 0 ≤ q) (hql : ql ≤ q) : x ^ q ≤ Real.exp (ql * Real.log X) :=
  le_trans (Real.rpow_le_rpow hx hxX hq) (rpow_le_exp_of_le_one hX0 hX hql)

lemma exp_one_sub_one_le : Real.exp 1 - 1 ≤ 1.7182818286 := by
  have := Real.exp_one_lt_d9; linarith

lemma J0_base_nonneg : 0 ≤ (Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi := by
  have : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact div_nonneg (mul_nonneg this (Real.exp_pos _).le) Real.pi_pos.le

/-- `RMF.bandPhi` at `η' = 0.3` over the cell, `N_c ≥ cen^q`. -/
noncomputable def bandHat (ql qu Nc s : ℝ) : ℝ :=
  Real.exp (-(ql * (2 * ql - 1)) * Real.log s)
      * (pfC2Hat ql qu * (Real.exp (qu * Real.log 2.30043)
        * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13)))
    + Real.exp (-(ql * (2 * ql - 1)) * s * (1 / 3))
      * (pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
        * (Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311))
          + Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)))
        + Real.exp (ql * Real.log 0.0132)))
    + pfC1Hat ql qu * Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181))
      * Real.exp (-(s * (ql * 0.093906 + ql * (2 * ql - 1) * (1 / 3)))
        - 2.718281828 * ql * Real.log s)

lemma coh_le : (1 + 1 / (0.3 : ℝ)) / Real.pi ≤ 1.37935 := by
  have := inv_pi_le
  rw [div_eq_mul_inv]
  nlinarith

/-- **`RMF.bandPhi` over a cell** at `η' = 0.3`, `K_c = 2.30043`, `E_c = 0.0132`: for
`½ < q_l ≤ q ≤ q_u ≤ 1`, `s ≥ 10` and `N_c ≥ cen(q)^q`, `bandPhi(s) ≤ RMF.bandHat q_l q_u N_c s`. -/
lemma bandPhi_le_bandHat {q ql qu Nc s : ℝ} (hql : 1 / 2 < ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) (hs : 10 ≤ s) (hNc : cenClean q ^ q ≤ Nc) :
    bandPhi q 0.3 2.30043 0.0132 s ≤ bandHat ql qu Nc s := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hs0 : 0 < s := by linarith
  have hls : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have ha : ql * (2 * ql - 1) ≤ q * (2 * q - 1) := mul_two_mul_sub_one_le hql.le hq
  have hal0 : 0 ≤ ql * (2 * ql - 1) := mul_nonneg (by linarith) (by linarith)
  have hc1 := pfC1_le_pfC1Hat hql.le hq hqu hqu1
  have hc2 := pfC2_le_pfC2Hat hql.le hq hqu hqu1
  have hc10 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hc20 : 0 ≤ pfC2 q := (Real.exp_pos _).le
  have hK : (2.30043 : ℝ) ^ q ≤ Real.exp (qu * Real.log 2.30043) :=
    rpow_le_exp_of_one_le (by norm_num) hqu
  have hK0 : (0 : ℝ) ≤ 2.30043 ^ q := Real.rpow_nonneg (by norm_num) _
  have hcoh : ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q ≤ Real.exp (qu * Real.log 1.37935) :=
    rpow_le_exp_hi (by positivity) coh_le (by norm_num) hq0 hqu
  have htiny : ((2.30043 : ℝ) * 4e-13) ^ q ≤ Real.exp (ql * Real.log 9.20172e-13) :=
    rpow_le_exp_lo (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq0 hq
  have hη : (1 + (0.3 : ℝ)) ^ q ≤ Real.exp (qu * Real.log 1.3) :=
    rpow_le_exp_hi (by norm_num) (by norm_num : (1 + (0.3 : ℝ)) ≤ 1.3) (by norm_num) hq0 hqu
  have hJ : ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
      ≤ Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311)) := by
    refine rpow_le_exp_lo J0_base_nonneg ?_ (by positivity) ?_ hq0 hq
    · rw [div_eq_mul_inv]
      have h1 := exp_one_sub_one_le
      have h2 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) inv_pi_le
        (inv_nonneg.2 Real.pi_pos.le) (by positivity)
    · have : Real.exp 0.0181 ≤ 1.02 := by interval_decide (trust := kernel)
      nlinarith
  have hF : (Real.exp 0.0181 / Real.pi) ^ q
      ≤ Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)) := by
    refine rpow_le_exp_lo (by positivity) ?_ (by positivity) ?_ hq0 hq
    · rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left inv_pi_le (Real.exp_pos _).le
    · have : Real.exp 0.0181 ≤ 1.02 := by interval_decide (trust := kernel)
      nlinarith
  have hE : (0.0132 : ℝ) ^ q ≤ Real.exp (ql * Real.log 0.0132) :=
    rpow_le_exp_of_le_one (by norm_num) (by norm_num) hq
  have hB : (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
      ≤ Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181)) := by
    refine rpow_le_exp_of_one_le (by
      have := Real.add_one_le_exp (0.0181 : ℝ); nlinarith) ?_
    have := Real.exp_one_lt_d9
    nlinarith
  -- the three terms
  rw [bandPhi, bandHat]
  have hNc0 : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg (le_trans hqu hqu1)) _
  have t1 : (s ^ (-(q * (2 * q - 1))) * (pfC2 q * ((2.30043 : ℝ) ^ q * (cenClean q ^ q
      + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q) + ((2.30043 : ℝ) * 4e-13) ^ q)))
      ≤ Real.exp (-(ql * (2 * ql - 1)) * Real.log s)
        * (pfC2Hat ql qu * (Real.exp (qu * Real.log 2.30043)
          * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13))) := by
    have hs1 : s ^ (-(q * (2 * q - 1))) ≤ Real.exp (-(ql * (2 * ql - 1)) * Real.log s) := by
      rw [Real.rpow_def_of_pos hs0]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    refine mul_le_mul hs1 (mul_le_mul hc2 (add_le_add (mul_le_mul hK (add_le_add hNc hcoh)
      (add_nonneg hNc0 (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le) htiny)
      (by positivity) (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
  have t2 : Real.exp (-(q * (2 * q - 1) * s / 3)) * (pfC1 q * ((2.30043 : ℝ) ^ q
      * (1 + (0.3 : ℝ)) ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + (Real.exp 0.0181 / Real.pi) ^ q) + (0.0132 : ℝ) ^ q))
      ≤ Real.exp (-(ql * (2 * ql - 1)) * s * (1 / 3))
        * (pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
          * (Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311))
            + Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)))
          + Real.exp (ql * Real.log 0.0132))) := by
    have hs1 : Real.exp (-(q * (2 * q - 1) * s / 3))
        ≤ Real.exp (-(ql * (2 * ql - 1)) * s * (1 / 3)) := Real.exp_le_exp.2 (by nlinarith)
    have hJ0 : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q :=
      Real.rpow_nonneg J0_base_nonneg _
    have hF0 : 0 ≤ (Real.exp 0.0181 / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
    have hη0 : 0 ≤ (1 + (0.3 : ℝ)) ^ q := Real.rpow_nonneg (by norm_num) _
    refine mul_le_mul hs1 (mul_le_mul hc1 (add_le_add (mul_le_mul (mul_le_mul hK hη hη0
      (Real.exp_pos _).le) (add_le_add hJ hF) (add_nonneg hJ0 hF0) (by positivity)) hE)
      (by positivity) (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
  have t3 : pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
      * Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3))
        - Real.exp 1 * q * Real.log s)
      ≤ pfC1Hat ql qu * Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181))
        * Real.exp (-(s * (ql * 0.093906 + ql * (2 * ql - 1) * (1 / 3)))
          - 2.718281828 * ql * Real.log s) := by
    have he := Real.exp_one_lt_d9
    have he' := Real.exp_one_gt_d9
    have h1 : ql * 0.093906 + ql * (2 * ql - 1) * (1 / 3)
        ≤ q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3 := by nlinarith
    have h2 : 2.718281828 * ql * Real.log s ≤ Real.exp 1 * q * Real.log s := by
      have : 2.718281828 * ql ≤ Real.exp 1 * q :=
        mul_le_mul (le_trans (by norm_num) he'.le) hq (by linarith) (Real.exp_pos 1).le
      exact mul_le_mul_of_nonneg_right this hls
    have hs1 : Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3))
        - Real.exp 1 * q * Real.log s)
        ≤ Real.exp (-(s * (ql * 0.093906 + ql * (2 * ql - 1) * (1 / 3)))
          - 2.718281828 * ql * Real.log s) := by
      have h3 := mul_le_mul_of_nonneg_left h1 hs0.le
      exact Real.exp_le_exp.2 (by linarith)
    have hH0 : 0 ≤ pfC1Hat ql qu := by rw [pfC1Hat]; positivity
    exact mul_le_mul (mul_le_mul hc1 hB (Real.rpow_nonneg (by positivity) _) hH0)
      hs1 (Real.exp_pos _).le (mul_nonneg hH0 (Real.exp_pos _).le)
  linarith

/-- `RMF.botPhi` at `η' = 0.3` over the cell and `Λ ≥ Λ₀`, `N_c ≥ cen^q`. -/
noncomputable def botHat (ql qu Nc L0 TS : ℝ) : ℝ :=
  Real.exp (-(ql * (2 * ql - 1)) * Real.log (3 * L0))
      * (pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043)
        * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13)))
    + Real.exp (-(L0 * (ql * 0.2817181714 + ql * (2 * ql - 1)))
      - 2.718281828 * ql * Real.log (3 * L0) + 0.2732 * 2.7182818286 * qu)
    + Real.exp (-(ql * (2 * ql - 1)) * L0) * (Real.exp (ql * Real.log 0.0132)
      + Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
        * (TS + Real.exp (ql * Real.log (Real.exp 0.2732 * 0.1591555))))

set_option maxHeartbeats 400000 in
-- three terms, each bounded factor by factor
/-- **`RMF.botPhi` over a cell** at `η' = 0.3`, `K_c = 2.30043`, `E_c = 0.0132`: for
`½ < q_l ≤ q ≤ q_u ≤ 1`, `Λ ≥ Λ₀ ≥ 11.5`, `TS ≥ 0` and `N_c ≥ cen(q)^q`,
`botPhi(Λ, TS) ≤ RMF.botHat q_l q_u N_c Λ₀ TS`. -/
lemma botPhi_le_botHat {q ql qu Nc L0 Λ TS : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) (hL0 : 11.5 ≤ L0) (hΛ : L0 ≤ Λ) (hTS : 0 ≤ TS)
    (hNc : cenClean q ^ q ≤ Nc) :
    botPhi q 0.3 2.30043 0.0132 Λ TS ≤ botHat ql qu Nc L0 TS := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have ha : ql * (2 * ql - 1) ≤ q * (2 * q - 1) := mul_two_mul_sub_one_le hql hq
  have hal0 : 0 ≤ ql * (2 * ql - 1) := mul_nonneg (by linarith) (by linarith)
  have hc1 := pfC1_le_pfC1Hat hql hq hqu hqu1
  have hH0 : 0 ≤ pfC1Hat ql qu := by rw [pfC1Hat]; positivity
  have hK : (2.30043 : ℝ) ^ q ≤ Real.exp (qu * Real.log 2.30043) :=
    rpow_le_exp_of_one_le (by norm_num) hqu
  have hK0 : (0 : ℝ) ≤ 2.30043 ^ q := Real.rpow_nonneg (by norm_num) _
  have hcoh : ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q ≤ Real.exp (qu * Real.log 1.37935) :=
    rpow_le_exp_hi (by positivity) coh_le (by norm_num) hq0 hqu
  have htiny : ((2.30043 : ℝ) * 4e-13) ^ q ≤ Real.exp (ql * Real.log 9.20172e-13) :=
    rpow_le_exp_lo (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq0 hq
  have hη : (1 + (0.3 : ℝ)) ^ q ≤ Real.exp (qu * Real.log 1.3) :=
    rpow_le_exp_hi (by norm_num) (by norm_num : (1 + (0.3 : ℝ)) ≤ 1.3) (by norm_num) hq0 hqu
  have hη0 : 0 ≤ (1 + (0.3 : ℝ)) ^ q := Real.rpow_nonneg (by norm_num) _
  have hE : (0.0132 : ℝ) ^ q ≤ Real.exp (ql * Real.log 0.0132) :=
    rpow_le_exp_of_le_one (by norm_num) (by norm_num) hq
  have hfar : (Real.exp 0.2732 / (2 * Real.pi)) ^ q
      ≤ Real.exp (ql * Real.log (Real.exp 0.2732 * 0.1591555)) := by
    refine rpow_le_exp_lo (by positivity) ?_ (by positivity) ?_ hq0 hq
    · rw [div_eq_mul_inv, mul_inv]
      have := inv_pi_le
      have h2 : (2 : ℝ)⁻¹ * Real.pi⁻¹ ≤ 0.1591555 := by nlinarith
      nlinarith [Real.exp_pos 0.2732, inv_nonneg.2 Real.pi_pos.le]
    · have : Real.exp 0.2732 ≤ 1.32 := by interval_decide (trust := kernel)
      nlinarith
  have hΛ0 : 0 < Λ := by linarith
  have hl3 : Real.log (3 * L0) ≤ Real.log (3 * Λ) := Real.log_le_log (by linarith) (by linarith)
  have hl30 : 0 ≤ Real.log (3 * L0) := Real.log_nonneg (by linarith)
  rw [botPhi, botHat]
  have hNc0 : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg (le_trans hqu hqu1)) _
  have t1 : (3 * Λ) ^ (-(q * (2 * q - 1))) * (pfC1 q * ((2.30043 : ℝ) ^ q * (cenClean q ^ q
      + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q) + ((2.30043 : ℝ) * 4e-13) ^ q))
      ≤ Real.exp (-(ql * (2 * ql - 1)) * Real.log (3 * L0))
        * (pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043)
          * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13))) := by
    have hs1 : (3 * Λ) ^ (-(q * (2 * q - 1)))
        ≤ Real.exp (-(ql * (2 * ql - 1)) * Real.log (3 * L0)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul ha hl3 hl30 (by nlinarith)
      nlinarith
    have hin0 : 0 ≤ (2.30043 : ℝ) ^ q * (cenClean q ^ q
        + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q) + ((2.30043 : ℝ) * 4e-13) ^ q :=
      add_nonneg (mul_nonneg hK0 (add_nonneg hNc0 (Real.rpow_nonneg (by positivity) _)))
        (Real.rpow_nonneg (by norm_num) _)
    refine mul_le_mul hs1 (mul_le_mul hc1 (add_le_add (mul_le_mul hK (add_le_add hNc hcoh)
      (add_nonneg hNc0 (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le) htiny)
      hin0 hH0) (mul_nonneg (Real.exp_pos _).le hin0) (Real.exp_pos _).le
  have t2 : Real.exp (-(Λ * (q * (3 - Real.exp 1) + q * (2 * q - 1)))
      - Real.exp 1 * q * Real.log (3 * Λ) + 0.2732 * (Real.exp 1 * q))
      ≤ Real.exp (-(L0 * (ql * 0.2817181714 + ql * (2 * ql - 1)))
        - 2.718281828 * ql * Real.log (3 * L0) + 0.2732 * 2.7182818286 * qu) := by
    refine Real.exp_le_exp.2 ?_
    have he := Real.exp_one_lt_d9
    have he' := Real.exp_one_gt_d9
    have h1 : ql * 0.2817181714 + ql * (2 * ql - 1) ≤ q * (3 - Real.exp 1) + q * (2 * q - 1) := by
      have : ql * 0.2817181714 ≤ q * (3 - Real.exp 1) :=
        mul_le_mul hq (by linarith) (by norm_num) hq0
      linarith
    have h10 : 0 ≤ ql * 0.2817181714 + ql * (2 * ql - 1) := by nlinarith
    have h2 := mul_le_mul hΛ h1 h10 hΛ0.le
    have h3 : 2.718281828 * ql * Real.log (3 * L0) ≤ Real.exp 1 * q * Real.log (3 * Λ) := by
      have : 2.718281828 * ql ≤ Real.exp 1 * q :=
        mul_le_mul (le_trans (by norm_num) he'.le) hq (by linarith) (Real.exp_pos 1).le
      exact mul_le_mul this hl3 hl30 (by positivity)
    have h4 : 0.2732 * (Real.exp 1 * q) ≤ 0.2732 * 2.7182818286 * qu := by
      have : Real.exp 1 * q ≤ 2.7182818286 * qu := mul_le_mul he.le hqu hq0 (by norm_num)
      linarith
    linarith
  have t3 : Real.exp (-(q * (2 * q - 1) * Λ)) * ((0.0132 : ℝ) ^ q + (2.30043 : ℝ) ^ q
      * (1 + (0.3 : ℝ)) ^ q * (TS + (Real.exp 0.2732 / (2 * Real.pi)) ^ q))
      ≤ Real.exp (-(ql * (2 * ql - 1)) * L0) * (Real.exp (ql * Real.log 0.0132)
        + Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
          * (TS + Real.exp (ql * Real.log (Real.exp 0.2732 * 0.1591555)))) := by
    have hs1 : Real.exp (-(q * (2 * q - 1) * Λ)) ≤ Real.exp (-(ql * (2 * ql - 1)) * L0) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul ha hΛ (by linarith) (by nlinarith)
      linarith
    have hf0 : 0 ≤ (Real.exp 0.2732 / (2 * Real.pi)) ^ q := Real.rpow_nonneg (by positivity) _
    refine mul_le_mul hs1 (add_le_add hE (mul_le_mul (mul_le_mul hK hη hη0 (Real.exp_pos _).le)
      (add_le_add le_rfl hfar) (add_nonneg hTS hf0) (by positivity))) (by positivity)
      (Real.exp_pos _).le
  linarith

/-- `W((1-q)2.33)` over the cell: `1.7182818286 + b·0.63212056 + (e^b - 1 - b)(1-e^{-3})/3`,
`b = (1 - q_l)·2.33`. -/
noncomputable def windowWHat (ql : ℝ) : ℝ :=
  1.7182818286 + (1 - ql) * 2.33 * 0.63212056
    + (Real.exp ((1 - ql) * 2.33) - 1 - (1 - ql) * 2.33) * (1 - Real.exp (-3)) * (1 / 3)

lemma taylorWindowW_le_hat {q ql : ℝ} (hq : ql ≤ q) (hq1 : q ≤ 1) :
    taylorWindowW ((1 - q) * 2.33) ≤ windowWHat ql := by
  have hb : (1 - q) * 2.33 ≤ (1 - ql) * 2.33 := by linarith
  have hb0 : 0 ≤ (1 - ql) * 2.33 := by linarith
  refine le_trans (taylorWindowW_mono hb) ?_
  rw [taylorWindowW, windowWHat]
  have he := Real.exp_one_lt_d9
  have hinv : 0.36787944 ≤ (Real.exp 1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    linarith
  have h3 : (Real.exp 1)⁻¹ ^ 3 = Real.exp (-3) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hq3 : 0 ≤ Real.exp ((1 - ql) * 2.33) - 1 - (1 - ql) * 2.33 := by
    linarith [Real.add_one_le_exp ((1 - ql) * 2.33)]
  rw [h3]
  have : (1 - ql) * 2.33 * (1 - (Real.exp 1)⁻¹) ≤ (1 - ql) * 2.33 * 0.63212056 :=
    mul_le_mul_of_nonneg_left (by linarith) hb0
  nlinarith

/-- `RMF.winConstW` at `η' = 0.3`, `K_c = 2.30043` over the cell. -/
noncomputable def winCHat (ql qu : ℝ) : ℝ :=
  Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3) * pfC1Hat ql qu
    * (Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
      * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)))
    * Real.exp (qu * (2 * qu - 1) * Real.log 1.5)
    * (1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2))

lemma windowWHat_le {ql : ℝ} (hql : 1 / 2 ≤ ql) : windowWHat ql ≤ 3.2 := by
  rw [windowWHat]
  have h1 : Real.exp ((1 - ql) * 2.33) ≤ Real.exp 1.165 := Real.exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp 1.165 ≤ 3.21 := by interval_decide (trust := kernel)
  have h3 : 0 ≤ 1 - Real.exp (-3) := by
    have := Real.exp_le_one_iff.2 (show (-3 : ℝ) ≤ 0 by norm_num); linarith
  have h4 : 1 - Real.exp (-3) ≤ 1 := by linarith [Real.exp_pos (-3)]
  have h5 : 0 ≤ Real.exp ((1 - ql) * 2.33) - 1 - (1 - ql) * 2.33 := by
    linarith [Real.add_one_le_exp ((1 - ql) * 2.33)]
  nlinarith

set_option maxHeartbeats 400000 in
-- six factors, each at its end of the cell
/-- **`RMF.winConstW` over a cell** at `η' = 0.3`, `K_c = 2.30043`. -/
lemma winConstW_le_winCHat {q ql qu : ℝ} (hql : 1 / 2 < ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) : winConstW q 0.3 2.30043 ≤ winCHat ql qu := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have ha : ql * (2 * ql - 1) ≤ q * (2 * q - 1) := mul_two_mul_sub_one_le hql.le hq
  have hal0 : 0 < ql * (2 * ql - 1) := mul_pos (by linarith) (by linarith)
  have hau : q * (2 * q - 1) ≤ qu * (2 * qu - 1) := mul_two_mul_sub_one_le (by linarith) hqu
  have hc1 := pfC1_le_pfC1Hat hql.le hq hqu hqu1
  have hH0 : 0 ≤ pfC1Hat ql qu := by rw [pfC1Hat]; positivity
  have hK : (2.30043 : ℝ) ^ q ≤ Real.exp (qu * Real.log 2.30043) :=
    rpow_le_exp_of_one_le (by norm_num) hqu
  have hη : (1 + (0.3 : ℝ)) ^ q ≤ Real.exp (qu * Real.log 1.3) :=
    rpow_le_exp_hi (by norm_num) (by norm_num : (1 + (0.3 : ℝ)) ≤ 1.3) (by norm_num) hq0 hqu
  -- the window constant
  have hWq := taylorWindowW_le_hat hq (le_trans hqu hqu1)
  have hW0 : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
    taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
  have hWH := windowWHat_le hql.le
  have hω : omegaClean q ≤ Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
      * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)) := by
    rw [omegaClean]
    have hbase : taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498)
        ≤ windowWHat ql * 0.318311 * (1 / 1.498) := by
      rw [div_eq_mul_inv, mul_inv]
      have := inv_pi_le
      have h1 : (1.498 : ℝ)⁻¹ = 1 / 1.498 := by norm_num
      rw [h1]
      have hpi0 : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
      calc taylorWindowW ((1 - q) * 2.33) * (Real.pi⁻¹ * (1 / 1.498))
          ≤ windowWHat ql * (0.318311 * (1 / 1.498)) :=
            mul_le_mul hWq (mul_le_mul_of_nonneg_right this (by norm_num)) (by positivity)
              (by linarith)
        _ = windowWHat ql * 0.318311 * (1 / 1.498) := by ring
    have hWH0 : 0 < windowWHat ql * 0.318311 * (1 / 1.498) := by
      have : 1.7182818286 ≤ windowWHat ql := by
        rw [windowWHat]
        have := Real.add_one_le_exp ((1 - ql) * 2.33)
        have h3 : 0 ≤ 1 - Real.exp (-3) := by
          have := Real.exp_le_one_iff.2 (show (-3 : ℝ) ≤ 0 by norm_num); linarith
        have : 0 ≤ (1 - ql) * 2.33 * 0.63212056 := by nlinarith
        nlinarith
      positivity
    refine mul_le_mul (rpow_le_exp_lo (by positivity) hbase hWH0 (by nlinarith) hq0 hq)
      (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
  -- the geometric factor
  have hgeo : Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1))))
      ≤ 1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2) := by
    set a := q * (2 * q - 1) with hadef
    have ha0 : 0 < a := lt_of_lt_of_le hal0 ha
    have h1 : Real.exp (-a) / (1 - Real.exp (-a)) = 1 / (Real.exp a - 1) := by
      rw [Real.exp_neg]
      have : Real.exp a - 1 ≠ 0 := by
        have := Real.add_one_le_exp a; nlinarith [Real.exp_pos a]
      field_simp
    rw [h1]
    have h2 := Real.quadratic_le_exp_of_nonneg ha0.le
    have h3 : ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2 ≤ a + a ^ 2 / 2 := by
      have := pow_le_pow_left₀ hal0.le ha 2
      linarith
    have h4 : 0 < ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2 := by positivity
    exact one_div_le_one_div_of_le h4 (by linarith)
  have hgeo0 : 0 ≤ Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1)))) := by
    have ha0 : 0 < q * (2 * q - 1) := lt_of_lt_of_le hal0 ha
    exact div_nonneg (Real.exp_pos _).le (by linarith [Real.exp_lt_one_iff.2 (show
      -(q * (2 * q - 1)) < 0 by linarith)])
  have h15 : (3 / 2 : ℝ) ^ (q * (2 * q - 1)) ≤ Real.exp (qu * (2 * qu - 1) * Real.log 1.5) := by
    rw [show (3 / 2 : ℝ) = 1.5 by norm_num]
    exact rpow_le_exp_of_one_le (by norm_num) hau
  rw [winConstW, winCHat]
  have hω0 : 0 ≤ omegaClean q := omegaClean_nonneg (le_trans hqu hqu1)
  have hc10 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hK0 : (0 : ℝ) ≤ 2.30043 ^ q := Real.rpow_nonneg (by norm_num) _
  have hη0 : 0 ≤ (1 + (0.3 : ℝ)) ^ q := Real.rpow_nonneg (by norm_num) _
  have h150 : (0 : ℝ) ≤ (3 / 2) ^ (q * (2 * q - 1)) := Real.rpow_nonneg (by norm_num) _
  refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hK hη hη0
    (Real.exp_pos _).le) hc1 hc10 (by positivity)) hω hω0 (by positivity)) h15 h150
    (by positivity)) hgeo hgeo0 (by positivity)

/-- The tower's tails: for `0 < γ ≤ 1`, `r_4^{-γ}/(1 - 2^{-γ}) ≤ e^{-10⁹γ}/(0.34γ)`. -/
lemma towerR_tail_le {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    towerR 4 ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) ≤ Real.exp (-(γ * 1e9)) / (0.34 * γ) := by
  -- `r_3 ≥ 3·10⁹`
  have hr1 : (28 : ℝ) ≤ towerR 1 := by
    rw [towerR, towerR]; interval_decide (trust := kernel)
  have hr2 : (11000 : ℝ) ≤ towerR 2 := by
    rw [towerR]
    have : Real.exp (28 / 3) ≤ Real.exp (towerR 1 / 3) := Real.exp_le_exp.2 (by linarith)
    have h2 : (11000 : ℝ) ≤ Real.exp (28 / 3) := by interval_decide (trust := kernel)
    linarith
  have hr3 : (3e9 : ℝ) ≤ towerR 3 := by
    rw [towerR]
    have : Real.exp 22 ≤ Real.exp (towerR 2 / 3) := Real.exp_le_exp.2 (by linarith)
    have h2 : (3e9 : ℝ) ≤ Real.exp 22 := by interval_decide (trust := kernel)
    linarith
  have hr4 : towerR 4 ^ (-γ) ≤ Real.exp (-(γ * 1e9)) := by
    rw [towerR, ← Real.exp_mul]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have h2 : 0.34 * γ ≤ 1 - (2 : ℝ) ^ (-γ) := by
    rw [Real.rpow_neg (by norm_num)]
    have h2pos : 0 < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) _
    have h2le : (2 : ℝ) ^ γ ≤ 2 := by
      calc (2 : ℝ) ^ γ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1
        _ = 2 := Real.rpow_one 2
    have hlog : γ * Real.log 2 + 1 ≤ (2 : ℝ) ^ γ := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
      exact Real.add_one_le_exp _
    have hl2 := Real.log_two_gt_d9
    rw [← one_div, show (1 : ℝ) - 1 / 2 ^ γ = (2 ^ γ - 1) / 2 ^ γ by field_simp,
      le_div_iff₀ h2pos]
    nlinarith
  have hden : 0 < 1 - (2 : ℝ) ^ (-γ) := by linarith
  calc towerR 4 ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) ≤ Real.exp (-(γ * 1e9)) / (1 - (2 : ℝ) ^ (-γ)) :=
        div_le_div_of_nonneg_right hr4 hden.le
    _ ≤ Real.exp (-(γ * 1e9)) / (0.34 * γ) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) h2

/-! ### The bottom's top windows over a cell -/

/-- `W(b)` from above: `1.7182818286 + b·0.63212056 + (e^b - 1 - b)(1-e^{-3})/3`. -/
noncomputable def windowWHatB (b : ℝ) : ℝ :=
  1.7182818286 + b * 0.63212056 + (Real.exp b - 1 - b) * (1 - Real.exp (-3)) * (1 / 3)

lemma taylorWindowW_le_hatB {b : ℝ} (hb : 0 ≤ b) : taylorWindowW b ≤ windowWHatB b := by
  rw [taylorWindowW, windowWHatB]
  have he := Real.exp_one_lt_d9
  have hinv : 0.36787944 ≤ (Real.exp 1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    linarith
  have h3 : (Real.exp 1)⁻¹ ^ 3 = Real.exp (-3) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  rw [h3]
  have : b * (1 - (Real.exp 1)⁻¹) ≤ b * 0.63212056 := mul_le_mul_of_nonneg_left (by linarith) hb
  nlinarith

/-- **A top window of the bottom without a split, over a cell**: for `T ≥ T_l > 0`,
`log z ≥ 1000` and `e^{q log c} ≤ N` at `q = q_l, q_u`, `c = 1.7182818286e^{0.2732}·0.318311/T_l`,
`RMF.winNoSplitFull q T z ≤ N`. -/
lemma winNoSplitFull_le_cell {q ql qu T Tl N : ℝ} {z : ℕ} (hql : 0 ≤ ql) (hq : ql ≤ q)
    (hqu : q ≤ qu) (hTl : 0 < Tl) (hT : Tl ≤ T) (hlz : 1000 ≤ Real.log z)
    (hl : Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.2732 * 0.318311 / Tl)) ≤ N)
    (hu : Real.exp (qu * Real.log (1.7182818286 * Real.exp 0.2732 * 0.318311 / Tl)) ≤ N) :
    winNoSplitFull q T z ≤ N := by
  have hq0 : 0 ≤ q := le_trans hql hq
  refine le_trans (winNoSplitFull_le_of_le hq0 hTl hT hlz) ?_
  have hbase : (Real.exp 1 - 1) * Real.exp 0.2732 / (Real.pi * Tl)
      ≤ 1.7182818286 * Real.exp 0.2732 * 0.318311 / Tl := by
    rw [div_le_div_iff₀ (by positivity) hTl]
    have h1 := exp_one_sub_one_le
    have h2 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpi := inv_pi_le
    have hpi' : 1 ≤ 0.318311 * Real.pi := by
      have := Real.pi_gt_d6; nlinarith
    have he := Real.exp_pos 0.2732
    calc (Real.exp 1 - 1) * Real.exp 0.2732 * Tl
        ≤ 1.7182818286 * Real.exp 0.2732 * Tl * (0.318311 * Real.pi) := by
          have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 he.le) hTl.le
          have h4 := mul_le_mul_of_nonneg_left hpi'
            (by positivity : (0 : ℝ) ≤ 1.7182818286 * Real.exp 0.2732 * Tl)
          linarith
      _ = 1.7182818286 * Real.exp 0.2732 * 0.318311 * (Real.pi * Tl) := by ring
  have hb0 : 0 ≤ (Real.exp 1 - 1) * Real.exp 0.2732 / (Real.pi * Tl) := by
    have : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    positivity
  exact le_trans (Real.rpow_le_rpow hb0 hbase hq0)
    (rpow_le_of_exp_log_both (by positivity) hq hqu hl hu)

set_option maxHeartbeats 400000 in
-- the split window's bound, each factor at its end of the cell
/-- **A top window of the bottom with a split, over a cell**: for `u = 3/2/T ∈ [u_l, u_h]`,
`1.2 ≤ u_l`, `u_h ≤ log z`, `log z ≥ 1000`, and `e^{q log I} ≤ N'` at `q = q_l, q_u`,
`I` the split window's inner constant at `q_l`,
`winSplitFull ≤ e^{a_u log u_h}e^{a_u(0.2641 + 9.0028/(u_l - 0.6932) + (2-2q_l)/3)}·N'`. -/
lemma winSplitFull_le_cell {q ql qu T ulo uhi N' : ℝ} {z : ℕ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q)
    (hqu : q ≤ qu) (hqu1 : qu ≤ 1) (hT : 0 < T) (hulo : ulo ≤ 3 / 2 / T) (huhi : 3 / 2 / T ≤ uhi)
    (hulo1 : 1.2 ≤ ulo) (huz : uhi ≤ Real.log z) (hlz : 1000 ≤ Real.log z)
    (hl : Real.exp (ql * Real.log (windowWHatB (2 * (1 - ql) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311
      / (3 / 2 - 3 / 2 / ulo * 0.6932))) ≤ N')
    (hu : Real.exp (qu * Real.log (windowWHatB (2 * (1 - ql) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311
      / (3 / 2 - 3 / 2 / ulo * 0.6932))) ≤ N') :
    winSplitFull q T (splitPt (3 / 2) T 2 z) z
      ≤ Real.exp (qu * (2 * qu - 1) * Real.log uhi)
        * Real.exp (qu * (2 * qu - 1) * (0.2641 + 9.0028 / (ulo - 0.6932) + (2 - 2 * ql) / 3))
        * N' := by
  have hq0 : 0 ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0 (by linarith)
  have hau : q * (2 * q - 1) ≤ qu * (2 * qu - 1) := mul_two_mul_sub_one_le (by linarith) hqu
  refine le_trans (winSplitFull_le_range (le_trans hql hq) (le_trans hqu hqu1) hT hulo huhi
    hulo1 huz hlz) ?_
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have huhi1 : 1 ≤ uhi := by linarith [le_trans hulo huhi]
  have hden : 0 < ulo - 0.6932 := by linarith
  have hinv : 9.0028 / (ulo - Real.log 2) ≤ 9.0028 / (ulo - 0.6932) :=
    div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
  have hinv0 : 0 ≤ 9.0028 / (ulo - Real.log 2) := div_nonneg (by norm_num) (by linarith)
  -- the (PF) factors
  have h1 : uhi ^ (q * (2 * q - 1)) ≤ Real.exp (qu * (2 * qu - 1) * Real.log uhi) :=
    rpow_le_exp_of_one_le huhi1 hau
  have h2 : Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / (ulo - Real.log 2) + (2 - 2 * q) / 3))
      ≤ Real.exp (qu * (2 * qu - 1) * (0.2641 + 9.0028 / (ulo - 0.6932) + (2 - 2 * ql) / 3)) := by
    refine Real.exp_le_exp.2 (mul_le_mul hau (by linarith) (by linarith) (by nlinarith))
  -- the inner factor
  have hulo0 : 0 < ulo := by linarith
  have hS0 : 0 ≤ splitST2 ulo := by rw [splitST2]; positivity
  have hb : 2 * (1 - q) * splitST2 ulo ≤ 2 * (1 - ql) * splitST2 ulo :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  have hb0 : 0 ≤ 2 * (1 - q) * splitST2 ulo :=
    mul_nonneg (by linarith [le_trans hqu hqu1]) hS0
  have hW : taylorWindowW (2 * (1 - q) * splitST2 ulo)
      ≤ windowWHatB (2 * (1 - ql) * splitST2 ulo) :=
    le_trans (taylorWindowW_mono hb) (taylorWindowW_le_hatB (le_trans hb0 hb))
  have hW0 : 0 ≤ taylorWindowW (2 * (1 - q) * splitST2 ulo) := taylorWindowW_nonneg hb0
  have hden1 : 0 < 3 / 2 - 3 / 2 / ulo * 0.6932 := by
    have : 3 / 2 / ulo ≤ 1.25 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  have hden2 : 3 / 2 - 3 / 2 / ulo * 0.6932 ≤ 3 / 2 - 3 / 2 / ulo * Real.log 2 := by
    have : 0 ≤ 3 / 2 / ulo := by positivity
    nlinarith
  have hinner : taylorWindowW (2 * (1 - q) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)
      / (Real.pi * (3 / 2 - 3 / 2 / ulo * Real.log 2))
      ≤ windowWHatB (2 * (1 - ql) * splitST2 ulo)
        * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311
        / (3 / 2 - 3 / 2 / ulo * 0.6932) := by
    have he : Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)
        ≤ Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) := Real.exp_le_exp.2 (by linarith)
    have hpi := inv_pi_le
    rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
    have hpi0 : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
    have hd : (3 / 2 - 3 / 2 / ulo * Real.log 2)⁻¹ ≤ (3 / 2 - 3 / 2 / ulo * 0.6932)⁻¹ :=
      inv_anti₀ hden1 hden2
    have hWb0 : 0 ≤ windowWHatB (2 * (1 - ql) * splitST2 ulo) := le_trans hW0 hW
    calc taylorWindowW (2 * (1 - q) * splitST2 ulo)
          * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)
          * (Real.pi⁻¹ * (3 / 2 - 3 / 2 / ulo * Real.log 2)⁻¹)
        ≤ windowWHatB (2 * (1 - ql) * splitST2 ulo)
          * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091)
          * (0.318311 * (3 / 2 - 3 / 2 / ulo * 0.6932)⁻¹) :=
          mul_le_mul (mul_le_mul hW he (Real.exp_pos _).le hWb0)
            (mul_le_mul hpi hd (inv_nonneg.2 (by linarith)) (by norm_num))
            (mul_nonneg hpi0 (inv_nonneg.2 (by linarith))) (by positivity)
      _ = _ := by ring
  have hin0 : 0 ≤ taylorWindowW (2 * (1 - q) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)
      / (Real.pi * (3 / 2 - 3 / 2 / ulo * Real.log 2)) := by
    have : 0 < 3 / 2 - 3 / 2 / ulo * Real.log 2 := by linarith
    have := Real.pi_pos
    positivity
  have hI0 : 0 < windowWHatB (2 * (1 - ql) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311
      / (3 / 2 - 3 / 2 / ulo * 0.6932) := by
    have : 1.7182818286 ≤ windowWHatB (2 * (1 - ql) * splitST2 ulo) := by
      rw [windowWHatB]
      have hb' : 0 ≤ 2 * (1 - ql) * splitST2 ulo := le_trans hb0 hb
      have := Real.add_one_le_exp (2 * (1 - ql) * splitST2 ulo)
      have h3 : 0 ≤ 1 - Real.exp (-3) := by
        have := Real.exp_le_one_iff.2 (show (-3 : ℝ) ≤ 0 by norm_num); linarith
      nlinarith
    positivity
  have h3 := le_trans (Real.rpow_le_rpow hin0 hinner hq0) (rpow_le_of_exp_log_both hI0 hq hqu hl hu)
  exact mul_le_mul (mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le) h3
    (Real.rpow_nonneg hin0 _) (by positivity)

/-- The constant of `RMF.bandPhi_le_rpow` at `η' = 0.3` over the cell, `N_c ≥ cen^q`. -/
noncomputable def bandConstHat (ql qu Nc : ℝ) : ℝ :=
  pfC2Hat ql qu * (Real.exp (qu * Real.log 2.30043)
      * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13))
  + pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
      * (Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311))
        + Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)))
      + Real.exp (ql * Real.log 0.0132))
  + pfC1Hat ql qu * Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181))

lemma bandConst_le_hat {q ql qu Nc : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) (hNc : cenClean q ^ q ≤ Nc) :
    pfC2 q * ((2.30043 : ℝ) ^ q * (cenClean q ^ q + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q)
        + ((2.30043 : ℝ) * 4e-13) ^ q)
      + pfC1 q * ((2.30043 : ℝ) ^ q * (1 + (0.3 : ℝ)) ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + (0.0132 : ℝ) ^ q)
      + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
      ≤ bandConstHat ql qu Nc := by
  -- `bandPhi` at `s = 1` is exactly this constant up to the three exponentials
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hc1 := pfC1_le_pfC1Hat hql hq hqu hqu1
  have hc2 := pfC2_le_pfC2Hat hql hq hqu hqu1
  have hc10 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hH0 : 0 ≤ pfC1Hat ql qu := by rw [pfC1Hat]; positivity
  have hH20 : 0 ≤ pfC2Hat ql qu := by rw [pfC2Hat]; positivity
  have hK : (2.30043 : ℝ) ^ q ≤ Real.exp (qu * Real.log 2.30043) :=
    rpow_le_exp_of_one_le (by norm_num) hqu
  have hK0 : (0 : ℝ) ≤ 2.30043 ^ q := Real.rpow_nonneg (by norm_num) _
  have hcoh : ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q ≤ Real.exp (qu * Real.log 1.37935) :=
    rpow_le_exp_hi (by positivity) coh_le (by norm_num) hq0 hqu
  have htiny : ((2.30043 : ℝ) * 4e-13) ^ q ≤ Real.exp (ql * Real.log 9.20172e-13) :=
    rpow_le_exp_lo (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq0 hq
  have hη : (1 + (0.3 : ℝ)) ^ q ≤ Real.exp (qu * Real.log 1.3) :=
    rpow_le_exp_hi (by norm_num) (by norm_num : (1 + (0.3 : ℝ)) ≤ 1.3) (by norm_num) hq0 hqu
  have hη0 : 0 ≤ (1 + (0.3 : ℝ)) ^ q := Real.rpow_nonneg (by norm_num) _
  have he102 : Real.exp 0.0181 ≤ 1.02 := by interval_decide (trust := kernel)
  have hJ : ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
      ≤ Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311)) := by
    refine rpow_le_exp_lo J0_base_nonneg ?_ (by positivity) (by nlinarith) hq0 hq
    rw [div_eq_mul_inv]
    have h1 := exp_one_sub_one_le
    have h2 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) inv_pi_le
      (inv_nonneg.2 Real.pi_pos.le) (by positivity)
  have hF : (Real.exp 0.0181 / Real.pi) ^ q
      ≤ Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)) := by
    refine rpow_le_exp_lo (by positivity) ?_ (by positivity) (by nlinarith) hq0 hq
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left inv_pi_le (Real.exp_pos _).le
  have hE : (0.0132 : ℝ) ^ q ≤ Real.exp (ql * Real.log 0.0132) :=
    rpow_le_exp_of_le_one (by norm_num) (by norm_num) hq
  have hB : (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
      ≤ Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181)) := by
    refine rpow_le_exp_of_one_le (by
      have := Real.add_one_le_exp (0.0181 : ℝ); nlinarith) ?_
    have := Real.exp_one_lt_d9
    nlinarith
  have hNc0 : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg (le_trans hqu hqu1)) _
  have hJ0 : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q :=
    Real.rpow_nonneg J0_base_nonneg _
  have hF0 : 0 ≤ (Real.exp 0.0181 / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
  have hin2 : 0 ≤ (2.30043 : ℝ) ^ q * (cenClean q ^ q + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q)
      + ((2.30043 : ℝ) * 4e-13) ^ q :=
    add_nonneg (mul_nonneg hK0 (add_nonneg hNc0 (Real.rpow_nonneg (by positivity) _)))
      (Real.rpow_nonneg (by norm_num) _)
  rw [bandConstHat]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul hc2 (add_le_add (mul_le_mul hK (add_le_add hNc hcoh)
      (add_nonneg hNc0 (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le) htiny)
      hin2 hH20
  · exact mul_le_mul hc1 (add_le_add (mul_le_mul (mul_le_mul hK hη hη0 (Real.exp_pos _).le)
      (add_le_add hJ hF) (add_nonneg hJ0 hF0) (by positivity)) hE)
      (by positivity) hH0
  · exact mul_le_mul hc1 hB (Real.rpow_nonneg (by positivity) _) hH0

lemma towerR_one_ge : (28 : ℝ) ≤ towerR 1 := by
  rw [towerR, towerR]; interval_decide (trust := kernel)

lemma towerR_two_ge : (11300 : ℝ) ≤ towerR 2 := by
  rw [towerR]
  have : Real.exp (28 / 3) ≤ Real.exp (towerR 1 / 3) :=
    Real.exp_le_exp.2 (by linarith [towerR_one_ge])
  have h2 : (11300 : ℝ) ≤ Real.exp (28 / 3) := by interval_decide (trust := kernel)
  linarith

/-- `x^P ≤ N` for `P ∈ [1/(2q_u), 1/(2q_l)]` from the two ends, `x ≤ X`, `X > 0`. -/
lemma rpow_inv_le_of_both {x X q ql qu N : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hX : 0 < X)
    (hql : 0 < ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hl : Real.exp ((2 * qu)⁻¹ * Real.log X) ≤ N) (hu : Real.exp ((2 * ql)⁻¹ * Real.log X) ≤ N) :
    x ^ (2 * q)⁻¹ ≤ N := by
  have hq0 : 0 < q := lt_of_lt_of_le hql hq
  have hP1 : (2 * qu)⁻¹ ≤ (2 * q)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hP2 : (2 * q)⁻¹ ≤ (2 * ql)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  exact le_trans (Real.rpow_le_rpow hx hxX (by positivity))
    (rpow_le_of_exp_log_both hX hP1 hP2 hl hu)

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
-- the Jensen regime's bound, every piece at its end of the cell
/-- **A cell of the Jensen regime above `½`.**  For `½ < q_l ≤ q ≤ q_u ≤ 1`,
`x ≥ 3` with `Λ = log log x ≥ Λ₀ ≥ 11.5`, a bound `TS ≥ 0` on the bottom's nine top windows, and
numerals bounding the pieces of `RMF.aboveTowerF` at `η' = 0.3`, `ε = 0.1` over the cell (each an
`interval_decide` check in the cell's instance) whose total `N` has `N^{2q_u}(2q_u - 1)^{3/4} ≤ 25`:

`E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`. -/
theorem above_cell_jensen {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql qu L0 TS Nc Ntop Nb0 Nb1 Nb2 Nbot Nw Nt : ℝ} (hql : 1 / 2 < ql) (hq : ql ≤ q)
    (hqu : q ≤ qu) (hqu1 : qu ≤ 1) (hL0 : 11.5 ≤ L0) (hx3 : 3 ≤ x)
    (hΛ : L0 ≤ Real.log (Real.log x)) (hTS0 : 0 ≤ TS)
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS)
    (hc1 : Real.exp (ql * Real.log (cenHat ql qu)) ≤ Nc)
    (hc2 : Real.exp (qu * Real.log (cenHat ql qu)) ≤ Nc)
    (htop : topHat ql qu ≤ Ntop)
    (hb0l : Real.exp ((2 * qu)⁻¹ * Real.log (bandHat ql qu Nc 10)) ≤ Nb0)
    (hb0u : Real.exp ((2 * ql)⁻¹ * Real.log (bandHat ql qu Nc 10)) ≤ Nb0)
    (hb1l : Real.exp ((2 * qu)⁻¹ * Real.log (bandHat ql qu Nc 28)) ≤ Nb1)
    (hb1u : Real.exp ((2 * ql)⁻¹ * Real.log (bandHat ql qu Nc 28)) ≤ Nb1)
    (hb2l : Real.exp ((2 * qu)⁻¹ * Real.log (bandHat ql qu Nc 11300)) ≤ Nb2)
    (hb2u : Real.exp ((2 * ql)⁻¹ * Real.log (bandHat ql qu Nc 11300)) ≤ Nb2)
    (hbotl : Real.exp ((2 * qu)⁻¹ * Real.log (botHat ql qu Nc L0 TS)) ≤ Nbot)
    (hbotu : Real.exp ((2 * ql)⁻¹ * Real.log (botHat ql qu Nc L0 TS)) ≤ Nbot)
    (hwl : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) * Real.exp ((2 * qu)⁻¹
      * Real.log (winCHat ql qu * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10))) ≤ Nw)
    (hwu : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) * Real.exp ((2 * ql)⁻¹
      * Real.log (winCHat ql qu * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10))) ≤ Nw)
    (htail : (2 + bandConstHat ql qu Nc + winCHat ql qu)
      * (Real.exp (-(ql * (2 * ql - 1) * (2 * qu)⁻¹ * 1e9))
        / (0.34 * (ql * (2 * ql - 1) * (2 * qu)⁻¹))) ≤ Nt)
    (hF1 : 1 ≤ Ntop + Nb0 + Nb1 + 2 * Nb2 + Nbot + Nw + Nt)
    (hfin : Real.exp (2 * qu * Real.log (Ntop + Nb0 + Nb1 + 2 * Nb2 + Nbot + Nw + Nt))
      * Real.exp (0.75 * Real.log (2 * qu - 1)) ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  set Λ := Real.log (Real.log x) with hΛdef
  set a := q * (2 * q - 1) with hadef
  set P := (2 * q)⁻¹ with hPdef
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := le_trans hqu hqu1
  have hq12 : 1 / 2 < q := lt_of_lt_of_le hql hq
  have ha0 : 0 < a := mul_pos hq0 (by linarith)
  have hal0 : 0 < ql * (2 * ql - 1) := mul_pos (by linarith) (by linarith)
  have hala : ql * (2 * ql - 1) ≤ a := mul_two_mul_sub_one_le hql.le hq
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have hP1 : P ≤ 1 := by rw [hPdef, inv_le_one₀ (by positivity)]; linarith
  have hPl : (2 * qu)⁻¹ ≤ P := inv_anti₀ (by positivity) (by linarith)
  have hPu : P ≤ (2 * ql)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by
    have := Real.exp_le_exp.2 (le_trans hL0 hΛ)
    rw [hΛdef] at this
    by_contra h
    push Not at h
    have h1 : Real.log x ≤ 0 := Real.log_nonpos hx0.le h
    have h2 : Real.log (Real.log x) ≤ 0 := by
      rcases eq_or_lt_of_le h1 with h3 | h3
      · rw [h3, Real.log_zero]
      · exact (Real.log_neg_eq_log (Real.log x)) ▸ Real.log_nonpos (by linarith) (by
          have : -Real.log x ≤ 1 ∨ True := Or.inr trivial
          nlinarith [Real.add_one_le_exp (Real.log x), Real.exp_log hx0])
    linarith)
  -- the tower's bound
  have hmain := integral_rpow_weightedRademacherSum_le_aboveTower hX (η' := 0.3) (ε := 0.1)
    hq12 hq1 (by norm_num) (by norm_num) hx3 (le_trans hL0 hΛ) hTS
  rw [← hΛdef, ← hadef] at hmain
  -- the cell's numerals
  have hKc : (2.0913 : ℝ) * (1 + 0.1) = 2.30043 := by norm_num
  have hEc : (0.0012 : ℝ) * (1 + 1 / 0.1) = 0.0132 := by norm_num
  have hcen : cenClean q ^ q ≤ Nc :=
    le_trans (Real.rpow_le_rpow (cenClean_nonneg hq1) (cenClean_le_cenHat hql.le hq hqu hqu1)
      hq0.le) (rpow_le_of_exp_log_both (by
        have := cenClean_nonneg hq1
        have h := cenClean_le_cenHat hql.le hq hqu hqu1
        have : 0 < cenHat ql qu := by
          rw [cenHat]
          have : 0 ≤ Real.exp (2 * (1 - ql) * 0.5158) - 1 :=
            sub_nonneg.2 (Real.one_le_exp (by nlinarith))
          positivity
        exact this) hq hqu hc1 hc2)
  obtain ⟨hanti, hnn⟩ := bandPhi_antitoneOn (q := q) (η' := 0.3) (Kc := 2.30043) (Ec := 0.0132)
    hq12 hq1 (by norm_num) (by norm_num) (by norm_num)
  have hbandHat_pos : ∀ s, 10 ≤ s → 0 < bandHat ql qu Nc s := by
    intro s hs
    have hNc0 : 0 ≤ Nc := le_trans (Real.exp_pos _).le hc1
    rw [bandHat]
    have : 0 < pfC2Hat ql qu := by rw [pfC2Hat]; positivity
    have : 0 < pfC1Hat ql qu := by rw [pfC1Hat]; positivity
    positivity
  have hband : ∀ s t N, 10 ≤ s → s ≤ t → Real.exp ((2 * qu)⁻¹ * Real.log (bandHat ql qu Nc s)) ≤ N
      → Real.exp ((2 * ql)⁻¹ * Real.log (bandHat ql qu Nc s)) ≤ N
      → bandPhi q 0.3 2.30043 0.0132 t ^ P ≤ N := by
    intro s t N hs hst hl hu
    have ht : 10 ≤ t := le_trans hs hst
    have h1 : bandPhi q 0.3 2.30043 0.0132 t ≤ bandHat ql qu Nc s :=
      le_trans (hanti hs ht hst) (bandPhi_le_bandHat hql hq hqu hqu1 hs hcen)
    exact rpow_inv_le_of_both (hnn t ht) h1 (hbandHat_pos s hs) (by linarith) hq hqu hl hu
  have hr0 : towerR 0 = 10 := rfl
  have hr1 := towerR_one_ge
  have hr2 := towerR_two_ge
  have hr3 : (11300 : ℝ) ≤ towerR 3 := by linarith [towerR_succ_ge 2]
  have hsum : ∑ j ∈ Finset.range 4, bandPhi q 0.3 2.30043 0.0132 (towerR j) ^ P
      ≤ Nb0 + Nb1 + 2 * Nb2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 := hband 10 (towerR 0) Nb0 le_rfl (le_of_eq hr0.symm) hb0l hb0u
    have e1 := hband 28 (towerR 1) Nb1 (by norm_num) hr1 hb1l hb1u
    have e2 := hband 11300 (towerR 2) Nb2 (by norm_num) hr2 hb2l hb2u
    have e3 := hband 11300 (towerR 3) Nb2 (by norm_num) hr3 hb2l hb2u
    linarith
  -- the bottom
  have hbotP : botPhi q 0.3 2.30043 0.0132 Λ TS ^ P ≤ Nbot := by
    have h1 := botPhi_le_botHat hql.le hq hqu hqu1 hL0 hΛ hTS0 hcen
    have h0 : 0 ≤ botPhi q 0.3 2.30043 0.0132 Λ TS :=
      botPhi_nonneg hq1 (by norm_num) (by norm_num) (by norm_num) (by linarith) hTS0
    have hpos : 0 < botHat ql qu Nc L0 TS := by
      have hNc0 : 0 ≤ Nc := le_trans (Real.exp_pos _).le hc1
      have : 0 < pfC1Hat ql qu := by rw [pfC1Hat]; positivity
      rw [botHat]
      positivity
    exact rpow_inv_le_of_both h0 h1 hpos (by linarith) hq hqu hbotl hbotu
  -- the windows
  have hC0 : 0 ≤ winConstW q 0.3 2.30043 := winConstW_nonneg hq12 hq1 (by norm_num) (by norm_num)
  have hwin : 5 ^ (1 - P) * (winConstW q 0.3 2.30043 * 10 ^ (-a)) ^ P ≤ Nw := by
    set Wh := winCHat ql qu * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10) with hWhdef
    have h10 : (10 : ℝ) ^ (-a) ≤ Real.exp (-(ql * (2 * ql - 1)) * Real.log 10) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      refine Real.exp_le_exp.2 ?_
      have : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
      nlinarith
    have hCW := winConstW_le_winCHat hql hq hqu hqu1
    have hx0' : 0 ≤ winConstW q 0.3 2.30043 * 10 ^ (-a) :=
      mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _)
    have hxWh : winConstW q 0.3 2.30043 * 10 ^ (-a) ≤ Wh :=
      mul_le_mul hCW h10 (Real.rpow_nonneg (by norm_num) _) (le_trans hC0 hCW)
    have hWh0 : 0 < Wh := by
      rw [hWhdef]
      refine mul_pos ?_ (Real.exp_pos _)
      rw [winCHat]
      have : 0 < pfC1Hat ql qu := by rw [pfC1Hat]; positivity
      have : 0 < ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2 :=
        add_pos hal0 (by positivity)
      positivity
    have h5 : (5 : ℝ) ^ (1 - P) ≤ Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith)
        (Real.log_nonneg (by norm_num)))
    have hP : (winConstW q 0.3 2.30043 * 10 ^ (-a)) ^ P
        ≤ max (Real.exp ((2 * qu)⁻¹ * Real.log Wh)) (Real.exp ((2 * ql)⁻¹ * Real.log Wh)) :=
      le_trans (Real.rpow_le_rpow hx0' hxWh hP0.le) (rpow_le_of_exp_log_both hWh0 hPl hPu
        (le_max_left _ _) (le_max_right _ _))
    have h50 : 0 ≤ Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) := (Real.exp_pos _).le
    calc (5 : ℝ) ^ (1 - P) * (winConstW q 0.3 2.30043 * 10 ^ (-a)) ^ P
        ≤ Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5)
          * max (Real.exp ((2 * qu)⁻¹ * Real.log Wh)) (Real.exp ((2 * ql)⁻¹ * Real.log Wh)) :=
          mul_le_mul h5 hP (Real.rpow_nonneg hx0' _) h50
      _ ≤ Nw := by
          rcases le_total (Real.exp ((2 * qu)⁻¹ * Real.log Wh))
            (Real.exp ((2 * ql)⁻¹ * Real.log Wh)) with h | h
          · rw [max_eq_right h]; exact hwu
          · rw [max_eq_left h]; exact hwl
  -- the tails
  have hγ0 : 0 < a * P := mul_pos ha0 hP0
  have hγ1 : a * P ≤ 1 := by
    have : a * P = (2 * q - 1) / 2 := by rw [hadef, hPdef]; field_simp
    rw [this]; linarith
  have hqu0 : 0 < (2 * qu)⁻¹ := by
    have : 0 < 2 * qu := by linarith
    positivity
  have hγl : ql * (2 * ql - 1) * (2 * qu)⁻¹ ≤ a * P := mul_le_mul hala hPl hqu0.le ha0.le
  have hγl0 : 0 < ql * (2 * ql - 1) * (2 * qu)⁻¹ := mul_pos hal0 hqu0
  have hτ : towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))
      ≤ Real.exp (-(ql * (2 * ql - 1) * (2 * qu)⁻¹ * 1e9))
        / (0.34 * (ql * (2 * ql - 1) * (2 * qu)⁻¹)) := by
    refine le_trans (towerR_tail_le hγ0 hγ1) ?_
    exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
      (by linarith)
  have hτ0 : 0 ≤ towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))) := by
    have h2 : (2 : ℝ) ^ (-(a * P)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact div_nonneg (Real.rpow_nonneg (by linarith [towerR_ten_le 4]) _) (by linarith)
  have hCb := bandConst_le_hat hql.le hq hqu hqu1 hcen
  have hCbX0 : 0 ≤ pfC2 q * ((2.30043 : ℝ) ^ q * (cenClean q ^ q
        + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q) + ((2.30043 : ℝ) * 4e-13) ^ q)
      + pfC1 q * ((2.30043 : ℝ) ^ q * (1 + (0.3 : ℝ)) ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + (0.0132 : ℝ) ^ q)
      + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q) := by
    have h := bandPhi_le_rpow (q := q) (η' := 0.3) (Kc := 2.30043) (Ec := 0.0132) hq12 hq1
      (by norm_num) (by norm_num) (by norm_num) (le_refl (10 : ℝ))
    have h0 := hnn 10 le_rfl
    have h10 : 0 < (10 : ℝ) ^ (-(q * (2 * q - 1))) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg h10
    linarith
  have htails : (pfC2 q * ((2.30043 : ℝ) ^ q * (cenClean q ^ q
        + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q) + ((2.30043 : ℝ) * 4e-13) ^ q)
      + pfC1 q * ((2.30043 : ℝ) ^ q * (1 + (0.3 : ℝ)) ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + (0.0132 : ℝ) ^ q)
      + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)) ^ P
        * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))
      + winConstW q 0.3 2.30043 ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))
      ≤ Nt := by
    have h1 := rpow_le_one_add hCbX0 hP0.le hP1
    have h2 := rpow_le_one_add hC0 hP0.le hP1
    have hCW := winConstW_le_winCHat hql hq hqu hqu1
    have t1 : ∀ Y : ℝ, Y ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))
        = Y ^ P * (towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))) :=
      fun Y => mul_div_assoc _ _ _
    rw [t1, t1]
    have e1 := mul_le_mul_of_nonneg_right (le_trans h1 (add_le_add le_rfl hCb)) hτ0
    have e2 := mul_le_mul_of_nonneg_right (le_trans h2 (add_le_add le_rfl hCW)) hτ0
    have hsum0 : 0 ≤ 2 + bandConstHat ql qu Nc + winCHat ql qu := by
      have := le_trans hCbX0 hCb
      have := le_trans hC0 hCW
      linarith
    have e3 := mul_le_mul_of_nonneg_left hτ hsum0
    nlinarith
  -- the total
  have hF : aboveTowerF q 0.3 0.1 Λ TS ≤ Ntop + Nb0 + Nb1 + 2 * Nb2 + Nbot + Nw + Nt := by
    rw [aboveTowerF, hKc, hEc, ← hadef, ← hPdef]
    have ht := le_trans (topPhi_le_topHat hql.le hq hqu hqu1) htop
    linarith
  have hF0 : 0 ≤ aboveTowerF q 0.3 0.1 Λ TS := by
    rw [aboveTowerF, hKc, hEc, ← hadef, ← hPdef]
    have : 0 ≤ topPhi q := by
      rw [topPhi]; have : 0 ≤ pfC1 q := (Real.exp_pos _).le; positivity
    have : 0 ≤ ∑ j ∈ Finset.range 4, bandPhi q 0.3 2.30043 0.0132 (towerR j) ^ P :=
      Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hnn _ (towerR_ten_le j)) _
    have : 0 ≤ botPhi q 0.3 2.30043 0.0132 Λ TS ^ P := Real.rpow_nonneg (botPhi_nonneg hq1
      (by norm_num) (by norm_num) (by norm_num) (by linarith) hTS0) _
    have : 0 ≤ 5 ^ (1 - P) * (winConstW q 0.3 2.30043 * 10 ^ (-a)) ^ P :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg
        (mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _)) _)
    have : 0 ≤ (pfC2 q * ((2.30043 : ℝ) ^ q * (cenClean q ^ q
        + ((1 + 1 / (0.3 : ℝ)) / Real.pi) ^ q) + ((2.30043 : ℝ) * 4e-13) ^ q)
      + pfC1 q * ((2.30043 : ℝ) ^ q * (1 + (0.3 : ℝ)) ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + (0.0132 : ℝ) ^ q)
      + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)) ^ P
        * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))) := by
      rw [mul_div_assoc]; exact mul_nonneg (Real.rpow_nonneg hCbX0 _) hτ0
    have : 0 ≤ winConstW q 0.3 2.30043 ^ P * towerR 4 ^ (-(a * P))
        / (1 - (2 : ℝ) ^ (-(a * P))) := by
      rw [mul_div_assoc]; exact mul_nonneg (Real.rpow_nonneg hC0 _) hτ0
    linarith
  -- raise to `2q`
  set N := Ntop + Nb0 + Nb1 + 2 * Nb2 + Nbot + Nw + Nt with hNdef
  have hN0 : 0 < N := by linarith
  have hpow : aboveTowerF q 0.3 0.1 Λ TS ^ (2 * q) ≤ Real.exp (2 * qu * Real.log N) := by
    calc aboveTowerF q 0.3 0.1 Λ TS ^ (2 * q) ≤ N ^ (2 * q) :=
          Real.rpow_le_rpow hF0 hF (by linarith)
      _ ≤ N ^ (2 * qu) := Real.rpow_le_rpow_of_exponent_le hF1 (by linarith)
      _ = Real.exp (2 * qu * Real.log N) := by rw [Real.rpow_def_of_pos hN0, mul_comm]
  have hd : Real.exp (2 * qu * Real.log N) ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
    have hdu : 0 < 2 * qu - 1 := by linarith
    have hdq : 0 < 2 * q - 1 := by linarith
    have h1 : Real.exp (0.75 * Real.log (2 * qu - 1)) = (2 * qu - 1) ^ (3 / 4 : ℝ) := by
      rw [Real.rpow_def_of_pos hdu]; ring_nf
    rw [h1] at hfin
    have h2 : (2 * q - 1) ^ (3 / 4 : ℝ) ≤ (2 * qu - 1) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow hdq.le (by linarith) (by norm_num)
    have h3 : Real.exp (2 * qu * Real.log N) * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ 25 :=
      le_trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hfin
    rw [Real.rpow_neg hdq.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hdq _)]
    exact h3
  calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ Real.log x ^ a * aboveTowerF q 0.3 0.1 Λ TS ^ (2 * q) := hmain
    _ ≤ Real.log x ^ a * (25 * (2 * q - 1) ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans hpow hd) (Real.rpow_nonneg hlx0.le _)
    _ = 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ a := by ring

/-- The split point of the bottom's `k`-th window: `0.75e^{k-1} ≤ 3/2/T_k ≤ 0.75e^k`. -/
lemma bottomT_split_bounds {z : ℕ} (hlz : 1 ≤ Real.log z) (k : ℕ) :
    0.75 * Real.exp ((k : ℝ) - 1) ≤ 3 / 2 / bottomT 1 2 z k
      ∧ 3 / 2 / bottomT 1 2 z k ≤ 0.75 * Real.exp (k : ℝ) := by
  obtain ⟨h1, h2⟩ := bottomT_mem hlz k
  have hT : 0 < bottomT 1 2 z k := lt_of_lt_of_le (by positivity) h1
  constructor
  · rw [le_div_iff₀ hT]
    have : 0.75 * Real.exp ((k : ℝ) - 1) * (2 * Real.exp (1 - k)) = 3 / 2 := by
      rw [show (0.75 : ℝ) * Real.exp ((k : ℝ) - 1) * (2 * Real.exp (1 - k))
        = 1.5 * (Real.exp ((k : ℝ) - 1) * Real.exp (1 - k)) by ring, ← Real.exp_add]
      norm_num
    have h3 := mul_le_mul_of_nonneg_left h2.le (by positivity : (0 : ℝ) ≤ 0.75 *
      Real.exp ((k : ℝ) - 1))
    linarith
  · rw [div_le_iff₀ hT]
    have : 0.75 * Real.exp (k : ℝ) * (2 * Real.exp (-(k : ℝ))) = 3 / 2 := by
      rw [show (0.75 : ℝ) * Real.exp (k : ℝ) * (2 * Real.exp (-(k : ℝ)))
        = 1.5 * (Real.exp (k : ℝ) * Real.exp (-(k : ℝ))) by ring, ← Real.exp_add]
      norm_num
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 0.75 * Real.exp (k : ℝ))
    linarith

lemma exp_mul_log_mono {x y c : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    Real.exp (c * Real.log x) ≤ Real.exp (c * Real.log y) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log hx hxy) hc)

/-- A band's hat from the cell's intermediate numerals. -/
noncomputable def bandHatN (ql nA2 nA1 nBc s : ℝ) : ℝ :=
  Real.exp (-(ql * (2 * ql - 1)) * Real.log s) * nA2
    + Real.exp (-(ql * (2 * ql - 1)) * s * (1 / 3)) * nA1
    + nBc * Real.exp (-(s * (ql * 0.093906 + ql * (2 * ql - 1) * (1 / 3)))
      - 2.718281828 * ql * Real.log s)

/-- The bottom's hat from the cell's intermediate numerals. -/
noncomputable def botHatN (ql qu L0 TS nA2' nE nKE nF : ℝ) : ℝ :=
  Real.exp (-(ql * (2 * ql - 1)) * Real.log (3 * L0)) * nA2'
    + Real.exp (-(L0 * (ql * 0.2817181714 + ql * (2 * ql - 1)))
      - 2.718281828 * ql * Real.log (3 * L0) + 0.2732 * 2.7182818286 * qu)
    + Real.exp (-(ql * (2 * ql - 1)) * L0) * (nE + nKE * (TS + nF))

set_option maxHeartbeats 1000000 in
-- the cell's hats through intermediate numerals, each a small check
/-- **A cell of the Jensen regime, in small checks**: `RMF.above_cell_jensen` with every hat
bounded through intermediate numerals — `n_{C1} ≥ pfC1`, `n_{C2} ≥ pfC2`, the powers of `K_c`,
`coh`, `1.3`, `E_c`, `J₀ + far`, `B`, the bottom's far range, `ω` and `1.5^a` — so that each
check in a cell's instance is a short expression. -/
theorem above_cell_jensen_split {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ)
    {x q ql qu L0 TS nCen Nc nC1 nC2 nK nCoh nTiny nKE nJF nE nB nF nOm n15 nBand0 nBand1 nBand2
      nBot Ntop Nb0 Nb1 Nb2 Nbot Nw Nt : ℝ} (hql : 1 / 2 < ql) (hq : ql ≤ q)
    (hqu : q ≤ qu) (hqu1 : qu ≤ 1) (hL0 : 11.5 ≤ L0) (hx3 : 3 ≤ x)
    (hΛ : L0 ≤ Real.log (Real.log x)) (hTS0 : 0 ≤ TS)
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS)
    (hcen : cenHat ql qu ≤ nCen)
    (hNc1 : Real.exp (ql * Real.log nCen) ≤ Nc) (hNc2 : Real.exp (qu * Real.log nCen) ≤ Nc)
    (hC1 : pfC1Hat ql qu ≤ nC1) (hC2 : pfC2Hat ql qu ≤ nC2)
    (hK : Real.exp (qu * Real.log 2.30043) ≤ nK)
    (hCoh : Real.exp (qu * Real.log 1.37935) ≤ nCoh)
    (hTiny : Real.exp (ql * Real.log 9.20172e-13) ≤ nTiny)
    (hKE : Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3) ≤ nKE)
    (hJF : Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311))
      + Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)) ≤ nJF)
    (hE : Real.exp (ql * Real.log 0.0132) ≤ nE)
    (hB : Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181)) ≤ nB)
    (hF : Real.exp (ql * Real.log (Real.exp 0.2732 * 0.1591555)) ≤ nF)
    (hOm : Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
      * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)) ≤ nOm)
    (h15 : Real.exp (qu * (2 * qu - 1) * Real.log 1.5) ≤ n15)
    (htop : topHat ql qu ≤ Ntop)
    (hband0 : bandHatN ql (nC2 * (nK * (Nc + nCoh) + nTiny)) (nC1 * (nKE * nJF + nE)) (nC1 * nB) 10
      ≤ nBand0)
    (hband1 : bandHatN ql (nC2 * (nK * (Nc + nCoh) + nTiny)) (nC1 * (nKE * nJF + nE)) (nC1 * nB) 28
      ≤ nBand1)
    (hband2 : bandHatN ql (nC2 * (nK * (Nc + nCoh) + nTiny)) (nC1 * (nKE * nJF + nE)) (nC1 * nB)
      11300 ≤ nBand2)
    (hb0l : Real.exp ((2 * qu)⁻¹ * Real.log nBand0) ≤ Nb0)
    (hb0u : Real.exp ((2 * ql)⁻¹ * Real.log nBand0) ≤ Nb0)
    (hb1l : Real.exp ((2 * qu)⁻¹ * Real.log nBand1) ≤ Nb1)
    (hb1u : Real.exp ((2 * ql)⁻¹ * Real.log nBand1) ≤ Nb1)
    (hb2l : Real.exp ((2 * qu)⁻¹ * Real.log nBand2) ≤ Nb2)
    (hb2u : Real.exp ((2 * ql)⁻¹ * Real.log nBand2) ≤ Nb2)
    (hbot : botHatN ql qu L0 TS (nC1 * (nK * (Nc + nCoh) + nTiny)) nE nKE nF ≤ nBot)
    (hbotl : Real.exp ((2 * qu)⁻¹ * Real.log nBot) ≤ Nbot)
    (hbotu : Real.exp ((2 * ql)⁻¹ * Real.log nBot) ≤ Nbot)
    (hwl : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) * Real.exp ((2 * qu)⁻¹
      * Real.log (nKE * nC1 * nOm * n15 * (1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2))
        * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10))) ≤ Nw)
    (hwu : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) * Real.exp ((2 * ql)⁻¹
      * Real.log (nKE * nC1 * nOm * n15 * (1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2))
        * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10))) ≤ Nw)
    (hγ : 100 ≤ ql * (2 * ql - 1) * (2 * qu)⁻¹ * 1e9)
    (htail : (2 + (nC2 * (nK * (Nc + nCoh) + nTiny) + nC1 * (nKE * nJF + nE) + nC1 * nB)
      + nKE * nC1 * nOm * n15 * (1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2)))
      * (Real.exp (-100) * (1 / (0.34 * (ql * (2 * ql - 1) * (2 * qu)⁻¹)))) ≤ Nt)
    (hF1 : 1 ≤ Ntop + Nb0 + Nb1 + 2 * Nb2 + Nbot + Nw + Nt)
    (hfin : Real.exp (2 * qu * Real.log (Ntop + Nb0 + Nb1 + 2 * Nb2 + Nbot + Nw + Nt))
      * Real.exp (0.75 * Real.log (2 * qu - 1)) ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  have hql0 : 0 < ql := by linarith
  have hqu0 : 0 < qu := by linarith
  have hal0 : 0 < ql * (2 * ql - 1) := mul_pos hql0 (by linarith)
  -- positivity of the hats
  have hcen0 : 0 < cenHat ql qu := by
    rw [cenHat]
    have : 0 ≤ Real.exp (2 * (1 - ql) * 0.5158) - 1 :=
      sub_nonneg.2 (Real.one_le_exp (by nlinarith))
    positivity
  have hC10 : 0 < pfC1Hat ql qu := by rw [pfC1Hat]; positivity
  have hC20 : 0 < pfC2Hat ql qu := by rw [pfC2Hat]; positivity
  have hNc0 : 0 ≤ Nc := le_trans (Real.exp_pos _).le hNc1
  -- the hypotheses of `RMF.above_cell_jensen`
  have hc1 : Real.exp (ql * Real.log (cenHat ql qu)) ≤ Nc :=
    le_trans (exp_mul_log_mono hcen0 hcen hql0.le) hNc1
  have hc2 : Real.exp (qu * Real.log (cenHat ql qu)) ≤ Nc :=
    le_trans (exp_mul_log_mono hcen0 hcen hqu0.le) hNc2
  have hA2 : pfC2Hat ql qu * (Real.exp (qu * Real.log 2.30043)
      * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13))
      ≤ nC2 * (nK * (Nc + nCoh) + nTiny) :=
    mul_le_mul hC2 (add_le_add (mul_le_mul hK (add_le_add le_rfl hCoh) (by positivity)
      (le_trans (Real.exp_pos _).le hK)) hTiny) (by positivity) (le_trans hC20.le hC2)
  have hA2' : pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043)
      * (Nc + Real.exp (qu * Real.log 1.37935)) + Real.exp (ql * Real.log 9.20172e-13))
      ≤ nC1 * (nK * (Nc + nCoh) + nTiny) :=
    mul_le_mul hC1 (add_le_add (mul_le_mul hK (add_le_add le_rfl hCoh) (by positivity)
      (le_trans (Real.exp_pos _).le hK)) hTiny) (by positivity) (le_trans hC10.le hC1)
  have hA1 : pfC1Hat ql qu * (Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
      * (Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.0181 * 0.318311))
        + Real.exp (ql * Real.log (Real.exp 0.0181 * 0.318311)))
      + Real.exp (ql * Real.log 0.0132)) ≤ nC1 * (nKE * nJF + nE) :=
    mul_le_mul hC1 (add_le_add (mul_le_mul hKE hJF (by positivity)
      (le_trans (by positivity) hKE)) hE) (by positivity) (le_trans hC10.le hC1)
  have hBc : pfC1Hat ql qu * Real.exp (2.7182818286 * qu * Real.log (1.001 * Real.exp 0.0181))
      ≤ nC1 * nB := mul_le_mul hC1 hB (Real.exp_pos _).le (le_trans hC10.le hC1)
  have hbandN : ∀ s, 10 ≤ s → bandHat ql qu Nc s
      ≤ bandHatN ql (nC2 * (nK * (Nc + nCoh) + nTiny)) (nC1 * (nKE * nJF + nE)) (nC1 * nB) s := by
    intro s _
    rw [bandHat, bandHatN]
    have e1 := mul_le_mul_of_nonneg_left hA2 (Real.exp_pos (-(ql * (2 * ql - 1)) * Real.log s)).le
    have e2 := mul_le_mul_of_nonneg_left hA1
      (Real.exp_pos (-(ql * (2 * ql - 1)) * s * (1 / 3))).le
    have e3 := mul_le_mul_of_nonneg_right hBc (Real.exp_pos (-(s * (ql * 0.093906
      + ql * (2 * ql - 1) * (1 / 3))) - 2.718281828 * ql * Real.log s)).le
    linarith
  have hbandPos : ∀ s, 10 ≤ s → 0 < bandHat ql qu Nc s := by
    intro s _
    rw [bandHat]
    positivity
  have hP : ∀ s N nb, 10 ≤ s → bandHat ql qu Nc s ≤ nb →
      Real.exp ((2 * qu)⁻¹ * Real.log nb) ≤ N → Real.exp ((2 * ql)⁻¹ * Real.log nb) ≤ N →
      Real.exp ((2 * qu)⁻¹ * Real.log (bandHat ql qu Nc s)) ≤ N
        ∧ Real.exp ((2 * ql)⁻¹ * Real.log (bandHat ql qu Nc s)) ≤ N := by
    intro s N nb hs hnb hl hu
    exact ⟨le_trans (exp_mul_log_mono (hbandPos s hs) hnb (by positivity)) hl,
      le_trans (exp_mul_log_mono (hbandPos s hs) hnb (by positivity)) hu⟩
  obtain ⟨hb0l', hb0u'⟩ := hP 10 Nb0 nBand0 le_rfl (le_trans (hbandN 10 le_rfl) hband0) hb0l hb0u
  obtain ⟨hb1l', hb1u'⟩ := hP 28 Nb1 nBand1 (by norm_num)
    (le_trans (hbandN 28 (by norm_num)) hband1) hb1l hb1u
  obtain ⟨hb2l', hb2u'⟩ := hP 11300 Nb2 nBand2 (by norm_num)
    (le_trans (hbandN 11300 (by norm_num)) hband2) hb2l hb2u
  -- the bottom
  have hbotN : botHat ql qu Nc L0 TS ≤ botHatN ql qu L0 TS (nC1 * (nK * (Nc + nCoh) + nTiny))
      nE nKE nF := by
    rw [botHat, botHatN]
    have e1 := mul_le_mul_of_nonneg_left hA2'
      (Real.exp_pos (-(ql * (2 * ql - 1)) * Real.log (3 * L0))).le
    have e3 : Real.exp (-(ql * (2 * ql - 1)) * L0) * (Real.exp (ql * Real.log 0.0132)
        + Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3)
          * (TS + Real.exp (ql * Real.log (Real.exp 0.2732 * 0.1591555))))
        ≤ Real.exp (-(ql * (2 * ql - 1)) * L0) * (nE + nKE * (TS + nF)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add hE (mul_le_mul hKE (add_le_add le_rfl hF)
        (by positivity) (le_trans (by positivity) hKE))) (Real.exp_pos _).le
    linarith
  have hbotPos : 0 < botHat ql qu Nc L0 TS := by rw [botHat]; positivity
  have hbotl' : Real.exp ((2 * qu)⁻¹ * Real.log (botHat ql qu Nc L0 TS)) ≤ Nbot :=
    le_trans (exp_mul_log_mono hbotPos (le_trans hbotN hbot) (by positivity)) hbotl
  have hbotu' : Real.exp ((2 * ql)⁻¹ * Real.log (botHat ql qu Nc L0 TS)) ≤ Nbot :=
    le_trans (exp_mul_log_mono hbotPos (le_trans hbotN hbot) (by positivity)) hbotu
  -- the windows
  have hden : 0 < ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2 := by positivity
  have hWC : winCHat ql qu ≤ nKE * nC1 * nOm * n15
      * (1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2)) := by
    rw [winCHat]
    have hOm0 : 0 ≤ Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
        * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)) := by positivity
    have hKE0 : 0 ≤ Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3) := by
      positivity
    refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul (mul_le_mul hKE hC1 hC10.le
      (le_trans hKE0 hKE)) hOm hOm0 (mul_nonneg (le_trans hKE0 hKE) (le_trans hC10.le hC1)))
      h15 (Real.exp_pos _).le (mul_nonneg (mul_nonneg (le_trans hKE0 hKE)
        (le_trans hC10.le hC1)) (le_trans hOm0 hOm))) (by positivity)
  have hWCpos : 0 < winCHat ql qu := by
    rw [winCHat]
    positivity
  have hwl' : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) * Real.exp ((2 * qu)⁻¹
      * Real.log (winCHat ql qu * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10))) ≤ Nw := by
    refine le_trans (mul_le_mul_of_nonneg_left (exp_mul_log_mono (by positivity)
      (mul_le_mul_of_nonneg_right hWC (Real.exp_pos _).le) (by positivity))
      (Real.exp_pos _).le) hwl
  have hwu' : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 5) * Real.exp ((2 * ql)⁻¹
      * Real.log (winCHat ql qu * Real.exp (-(ql * (2 * ql - 1)) * Real.log 10))) ≤ Nw := by
    refine le_trans (mul_le_mul_of_nonneg_left (exp_mul_log_mono (by positivity)
      (mul_le_mul_of_nonneg_right hWC (Real.exp_pos _).le) (by positivity))
      (Real.exp_pos _).le) hwu
  -- the tails
  have hCb : bandConstHat ql qu Nc
      ≤ nC2 * (nK * (Nc + nCoh) + nTiny) + nC1 * (nKE * nJF + nE) + nC1 * nB := by
    rw [bandConstHat]
    linarith
  have htail' : (2 + bandConstHat ql qu Nc + winCHat ql qu)
      * (Real.exp (-(ql * (2 * ql - 1) * (2 * qu)⁻¹ * 1e9))
        / (0.34 * (ql * (2 * ql - 1) * (2 * qu)⁻¹))) ≤ Nt := by
    rw [div_eq_mul_one_div]
    have hex : Real.exp (-(ql * (2 * ql - 1) * (2 * qu)⁻¹ * 1e9)) ≤ Real.exp (-100) :=
      Real.exp_le_exp.2 (by linarith)
    have hg0 : 0 ≤ 1 / (0.34 * (ql * (2 * ql - 1) * (2 * qu)⁻¹)) := by positivity
    have hCb0 : 0 ≤ bandConstHat ql qu Nc := by
      rw [bandConstHat]
      positivity
    have hle : 2 + bandConstHat ql qu Nc + winCHat ql qu
        ≤ 2 + (nC2 * (nK * (Nc + nCoh) + nTiny) + nC1 * (nKE * nJF + nE) + nC1 * nB)
          + nKE * nC1 * nOm * n15 * (1 / (ql * (2 * ql - 1) + (ql * (2 * ql - 1)) ^ 2 / 2)) := by
      linarith
    refine le_trans (mul_le_mul hle (mul_le_mul_of_nonneg_right hex hg0) (by positivity)
      (le_trans (by linarith) hle)) htail
  exact above_cell_jensen hX hql hq hqu hqu1 hL0 hx3 hΛ hTS0 hTS hc1 hc2 htop hb0l' hb0u' hb1l'
    hb1u' hb2l' hb2u' hbotl' hbotu' hwl' hwu' htail' hF1 hfin

/-- **A top window of the bottom without a split, for a cell's instance**: at the `k`-th height,
from `T_l ≤ 2e^{-k}`, `1/T_l ≤ T_inv` and the two ends. -/
lemma botWin_le_ns {q ql qu Tl Tinv N kr : ℝ} {z : ℕ} (k : ℕ) (hk : (k : ℝ) = kr)
    (hql : 0 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu) (hTl0 : 0 < Tl) (hTl : Tl ≤ 2 * Real.exp (-kr))
    (hTinv : 1 / Tl ≤ Tinv) (hz : 2300 ≤ Real.log z)
    (hl : Real.exp (ql * Real.log (1.7182818286 * Real.exp 0.2732 * 0.318311 * Tinv)) ≤ N)
    (hu : Real.exp (qu * Real.log (1.7182818286 * Real.exp 0.2732 * 0.318311 * Tinv)) ≤ N) :
    min (winNoSplitFull q (bottomT 1 2 z k) z)
      (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z) ≤ N := by
  refine le_trans (min_le_left _ _) ?_
  have hT := (bottomT_mem (z := z) (by linarith) k).1
  rw [hk] at hT
  have hc : 1.7182818286 * Real.exp 0.2732 * 0.318311 / Tl
      ≤ 1.7182818286 * Real.exp 0.2732 * 0.318311 * Tinv := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hTinv (by positivity)
  have hc0 : 0 < 1.7182818286 * Real.exp 0.2732 * 0.318311 / Tl := by positivity
  exact winNoSplitFull_le_cell hql hq hqu hTl0 (le_trans hTl hT) (by linarith)
    (le_trans (exp_mul_log_mono hc0 hc hql) hl)
    (le_trans (exp_mul_log_mono hc0 hc (le_trans hql (le_trans hq hqu))) hu)

/-- **A top window of the bottom with a split, for a cell's instance**: at the `k`-th height,
from `u_l ≤ 0.75e^{k-1}`, `0.75e^k ≤ u_h ≤ 2300`, the inner constant's two ends and the total. -/
lemma botWin_le_sp {q ql qu ulo uhi Np B kr : ℝ} {z : ℕ} (k : ℕ) (hk : (k : ℝ) = kr)
    (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu) (hqu1 : qu ≤ 1)
    (hulo : ulo ≤ 0.75 * Real.exp (kr - 1)) (huhi : 0.75 * Real.exp kr ≤ uhi) (hulo1 : 1.2 ≤ ulo)
    (huz : uhi ≤ 2300) (hz : 2300 ≤ Real.log z)
    (hl : Real.exp (ql * Real.log (windowWHatB (2 * (1 - ql) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311
      * (1 / (3 / 2 - 3 / 2 / ulo * 0.6932)))) ≤ Np)
    (hu : Real.exp (qu * Real.log (windowWHatB (2 * (1 - ql) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311
      * (1 / (3 / 2 - 3 / 2 / ulo * 0.6932)))) ≤ Np)
    (hB : Real.exp (qu * (2 * qu - 1) * Real.log uhi)
      * Real.exp (qu * (2 * qu - 1) * (0.2641 + 9.0028 / (ulo - 0.6932) + (2 - 2 * ql) / 3))
      * Np ≤ B) :
    min (winNoSplitFull q (bottomT 1 2 z k) z)
      (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z) ≤ B := by
  refine le_trans (min_le_right _ _) ?_
  obtain ⟨hs1, hs2⟩ := bottomT_split_bounds (z := z) (by linarith) k
  rw [hk] at hs1 hs2
  have hT : 0 < bottomT 1 2 z k :=
    lt_of_lt_of_le (by positivity) (bottomT_mem (z := z) (by linarith) k).1
  have hdiv : ∀ c : ℝ, windowWHatB (2 * (1 - ql) * splitST2 ulo)
      * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311 / c
      = windowWHatB (2 * (1 - ql) * splitST2 ulo)
        * Real.exp (9.0028 / (ulo - 0.6932) + 0.0091) * 0.318311 * (1 / c) :=
    fun c => div_eq_mul_one_div _ _
  refine le_trans (winSplitFull_le_cell hql hq hqu hqu1 hT (le_trans hulo hs1)
    (le_trans hs2 huhi) hulo1 (by linarith) (by linarith) (by rw [hdiv]; exact hl)
    (by rw [hdiv]; exact hu)) hB

/-- The bottom's nine top windows from their nine bounds. -/
lemma botTopSum_le_nine {q : ℝ} {z : ℕ} {B0 B1 B2 B3 B4 B5 B6 B7 B8 : ℝ}
    (h0 : min (winNoSplitFull q (bottomT 1 2 z 0) z)
      (winSplitFull q (bottomT 1 2 z 0) (splitPt (3 / 2) (bottomT 1 2 z 0) 2 z) z) ≤ B0)
    (h1 : min (winNoSplitFull q (bottomT 1 2 z 1) z)
      (winSplitFull q (bottomT 1 2 z 1) (splitPt (3 / 2) (bottomT 1 2 z 1) 2 z) z) ≤ B1)
    (h2 : min (winNoSplitFull q (bottomT 1 2 z 2) z)
      (winSplitFull q (bottomT 1 2 z 2) (splitPt (3 / 2) (bottomT 1 2 z 2) 2 z) z) ≤ B2)
    (h3 : min (winNoSplitFull q (bottomT 1 2 z 3) z)
      (winSplitFull q (bottomT 1 2 z 3) (splitPt (3 / 2) (bottomT 1 2 z 3) 2 z) z) ≤ B3)
    (h4 : min (winNoSplitFull q (bottomT 1 2 z 4) z)
      (winSplitFull q (bottomT 1 2 z 4) (splitPt (3 / 2) (bottomT 1 2 z 4) 2 z) z) ≤ B4)
    (h5 : min (winNoSplitFull q (bottomT 1 2 z 5) z)
      (winSplitFull q (bottomT 1 2 z 5) (splitPt (3 / 2) (bottomT 1 2 z 5) 2 z) z) ≤ B5)
    (h6 : min (winNoSplitFull q (bottomT 1 2 z 6) z)
      (winSplitFull q (bottomT 1 2 z 6) (splitPt (3 / 2) (bottomT 1 2 z 6) 2 z) z) ≤ B6)
    (h7 : min (winNoSplitFull q (bottomT 1 2 z 7) z)
      (winSplitFull q (bottomT 1 2 z 7) (splitPt (3 / 2) (bottomT 1 2 z 7) 2 z) z) ≤ B7)
    (h8 : min (winNoSplitFull q (bottomT 1 2 z 8) z)
      (winSplitFull q (bottomT 1 2 z 8) (splitPt (3 / 2) (bottomT 1 2 z 8) 2 z) z) ≤ B8) :
    botTopSum q z ≤ B0 + B1 + B2 + B3 + B4 + B5 + B6 + B7 + B8 := by
  rw [botTopSum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

end RMF
