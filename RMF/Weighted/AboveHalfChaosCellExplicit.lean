/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfChaosTransExplicit
import RMF.Weighted.AboveHalfCellsTSExplicit

/-!
# The chaos regime's cells above `q = ½`

For `½ < q < 0.50015` (`δ = 2q - 1 < 3·10⁻⁴`) and `δΛ ≥ 1`,
`RMF.integral_rpow_weightedRademacherSum_le_chaosF` at `η' = 0.3`, `ε = 0.1`, the height
`X = 0.003/a` and the transition `T = A a^{-3/4}·1.545` (`RMF.chaos_transition_num`) gives
`E|S(x)|^{2q} ≤ (log x)^a F^{2q}`; every piece of `F` is bounded in units of `δ^{-3/4}`
(`RMF.chaosF_rpow_le`), over cells of `δ`.
-/

open MeasureTheory

namespace RMF

/-! ### The window constant near `q = ½` -/

/-- **`RMF.omegaClean` over a cell**: `ω(q) ≤ e^{q_l log(W(q_l)·0.318311/1.498)}
e^{0.0185(q_u(2q_u-1) + q_u)}`, `W = RMF.windowWHat` (as in `RMF.winConstW_le_winCHat`). -/
lemma omegaClean_le_hat {q ql qu : ℝ} (hql : 1 / 2 ≤ ql) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 1) :
    omegaClean q ≤ Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
      * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hau : q * (2 * q - 1) ≤ qu * (2 * qu - 1) := mul_two_mul_sub_one_le (by linarith) hqu
  have hWq := taylorWindowW_le_hat hq (le_trans hqu hqu1)
  have hW0 : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
    taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
  have hWH := windowWHat_le hql
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
  exact mul_le_mul (rpow_le_exp_lo (by positivity) hbase hWH0 (by nlinarith) hq0 hq)
    (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le

/-! ### The transition, certified -/

/-- The grid of `u = aN`: `0, 1/50, 1/25, 7/100, 1/10, 3/20, 11/50, 9/25, 3/4, 4`, then `4`. -/
noncomputable def chaosUGrid : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 50
  | 2 => 1 / 25
  | 3 => 7 / 100
  | 4 => 1 / 10
  | 5 => 3 / 20
  | 6 => 11 / 50
  | 7 => 9 / 25
  | 8 => 3 / 4
  | _ => 4

/-- The profile sums' Gamma bound at `a`, `A` (`RMF.profSum_le_gamma`). -/
noncomputable def chaosB (a A : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico (1 : ℕ) 2008, Real.exp (-(a * (m : ℝ)))
    + A * ((1 / a) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)
      - Real.exp (-(a * 1999)) * (4 / 3 * (1999 : ℝ) ^ (3 / 4 : ℝ)))

/-- **The chaos profile's constant at `q ≤ 0.50015`**: at most `6.4233`. -/
lemma chaosAhat_le_num {q : ℝ} (hq0 : 1 / 2 ≤ q) (hqu : q ≤ 50015 / 100000) :
    chaosAhat q ≤ 64233 / 10000 := by
  refine le_trans (chaosAhat_le hq0 hqu (by norm_num)) ?_
  rw [max_mul_of_nonneg _ _ (Real.exp_pos _).le]
  refine max_le ?_ ?_
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

set_option maxHeartbeats 4000000 in
-- nine cells of `u`, each a short numeral check
/-- **The transition, certified**: for `½ < q ≤ 0.50015`, `a = q(2q-1)`,
`a' = a - (2q-1)/1000`, `A = RMF.chaosAhat q` and every `N`,
`profSum(N) + e^{1.001a'}e^{-a'N}B ≤ A a^{-3/4}·1.545`, `B = RMF.chaosB a A`. -/
theorem chaos_transition_num {q : ℝ} (hq0 : 1 / 2 < q) (hqu : q ≤ 50015 / 100000) :
    ∀ N : ℕ, profSum (q * (2 * q - 1)) (chaosAhat q) N
      + Real.exp (1.001 * (q * (2 * q - 1) - (2 * q - 1) / 1000))
        * Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000) * N))
        * chaosB (q * (2 * q - 1)) (chaosAhat q)
      ≤ chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200)) := by
  have hδ : 0 < 2 * q - 1 := by linarith
  have ha : 0 < q * (2 * q - 1) := mul_pos (by linarith) hδ
  have hau : q * (2 * q - 1) ≤ 15005 / 100000000 := by nlinarith
  have hAl := chaosAhat_ge hq0.le (by linarith)
  have hAu := chaosAhat_le_num hq0.le hqu
  have hA0 : 0 ≤ chaosAhat q := by linarith
  have hAt : chaosAhat q ^ 4 ≤ 1710 :=
    le_trans (pow_le_pow_left₀ hA0 hAu 4) (by norm_num)
  have hB : ∀ J, profSum (q * (2 * q - 1)) (chaosAhat q) J
      ≤ chaosB (q * (2 * q - 1)) (chaosAhat q) := fun J => profSum_le_gamma ha hA0 J
  have hBG := profSum_gamma_le (G := 627 / 500) (cu := 17368 / 1000) ha hau hAl
    (by interval_decide (trust := kernel)) (by norm_num) (by interval_decide (trust := kernel))
  refine chaos_transition (au := 15005 / 100000000) (r := 499 / 500) (t₁ := 1710)
    (G := 627 / 500) (ug := chaosUGrid) (n := 9) ha hau ?_ ?_ (by norm_num) (by norm_num) hA0
    (by norm_num) hAt hB hBG (by norm_num) rfl ?_ ?_ ?_ ?_
  · nlinarith
  · nlinarith
  · intro j hj
    interval_cases j <;>
      simp only [chaosUGrid, chaosS, chaosWGrid, Finset.sum_range_succ, Finset.sum_range_zero] <;>
      simp (disch := positivity) only [Real.rpow_def_of_pos] <;>
      interval_decide (trust := kernel)
  · intro j hj
    interval_cases j <;>
      simp only [chaosUGrid, chaosS, chaosWGrid, Finset.sum_range_succ, Finset.sum_range_zero] <;>
      simp (disch := positivity) only [Real.rpow_def_of_pos] <;>
      interval_decide (trust := kernel)
  · simp only [chaosUGrid]
    interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

/-! ### The total against `25δ^{-3/4}` -/

lemma bandConst_nonneg {q η' Kc Ec : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hKc : 0 ≤ Kc) (hEc : 0 ≤ Ec) : 0 ≤ bandConst q η' Kc Ec := by
  have hle : bandPhi q η' Kc Ec 10 ≤ bandConst q η' Kc Ec * (10 : ℝ) ^ (-(q * (2 * q - 1))) :=
    bandPhi_le_rpow hq0 hq1 hη' hKc hEc (le_refl (10 : ℝ))
  have h0 := (bandPhi_antitoneOn hq0 hq1 hη' hKc hEc).2 10 le_rfl
  have h10 : 0 < (10 : ℝ) ^ (-(q * (2 * q - 1))) := Real.rpow_pos_of_pos (by norm_num) _
  by_contra hc
  push Not at hc
  have := mul_neg_of_neg_of_pos hc h10
  linarith

set_option maxHeartbeats 1000000 in
-- the total's pieces, each at its bound
/-- **The chaos regime's total against `25δ^{-3/4}`.**  For `½ < q ≤ q_u < 1`,
`δ = 2q - 1`, `d = δ^{3/4}`, `Λ > 0`, `TS ≥ 0`, `W ≥ 0` and bounds on the pieces of
`RMF.chaosF` at `η' = 0.3`, `ε = 0.1` (the top, the bands' constant, the bottom, `C₁1.5^a`,
`12^{1-P}`; `d`, `Wd`, `(k+2)d`, `91e^{97a}e^{-aΛ}d`, `2(1-P)d` and `δ^{-(3/4)δ}`) whose total
`G = N_top N_d + N₁₂(N_b N_k + N_bot N_d + N_K(N_W + N_t) + N_P) ≥ 1` has `G^{2q_u}N_δ ≤ 25`:
`F^{2q} ≤ 25δ^{-3/4}`. -/
lemma chaosF_rpow_le {q qu Λ TS W Ntop NCb NBot NK N12 Nd NW Nk Ntl NP Ndd : ℝ} {k : ℕ}
    (hq0 : 1 / 2 < q) (hqu : q ≤ qu) (hqu1 : qu < 1) (hΛ : 0 < Λ) (hTS0 : 0 ≤ TS)
    (hW0 : 0 ≤ W) (htop : topPhi q ≤ Ntop) (hCb : bandConst q 0.3 2.30043 0.0132 ≤ NCb)
    (hbot : botPhi q 0.3 2.30043 0.0132 Λ TS ≤ NBot)
    (hK : (2.30043 : ℝ) ^ q * (1 + 0.3) ^ q * pfC1 q * omegaClean q
      * (3 / 2 : ℝ) ^ (q * (2 * q - 1)) ≤ NK)
    (h12 : (12 : ℝ) ^ (1 - (2 * q)⁻¹) ≤ N12) (hd : (2 * q - 1) ^ (3 / 4 : ℝ) ≤ Nd)
    (hW : W * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ NW)
    (hk : ((k : ℝ) + 2) * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ Nk)
    (htl : 91 * Real.exp (97 * (q * (2 * q - 1))) * Real.exp (-(q * (2 * q - 1) * Λ))
      * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ Ntl)
    (hP : 2 * (1 - (2 * q)⁻¹) * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ NP)
    (hdd : (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1))) ≤ Ndd)
    (hG1 : 1 ≤ Ntop * Nd + N12 * (NCb * Nk + NBot * Nd + NK * (NW + Ntl) + NP))
    (hfin : Real.exp (2 * qu * Real.log (Ntop * Nd + N12 * (NCb * Nk + NBot * Nd
      + NK * (NW + Ntl) + NP))) * Ndd ≤ 25) :
    chaosF q 0.3 0.1 Λ TS W k ^ (2 * q) ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
  have hKc : (2.0913 : ℝ) * (1 + 0.1) = 2.30043 := by norm_num
  have hEc : (0.0012 : ℝ) * (1 + 1 / 0.1) = 0.0132 := by norm_num
  have hq1 : q < 1 := lt_of_le_of_lt hqu hqu1
  have hδ : 0 < 2 * q - 1 := by linarith
  have hq0' : 0 < q := by linarith
  set d := (2 * q - 1) ^ (3 / 4 : ℝ) with hddef
  have hd0 : 0 < d := Real.rpow_pos_of_pos hδ _
  -- the pieces are nonnegative
  have htop0 : 0 ≤ topPhi q := by
    rw [topPhi]
    have : 0 ≤ pfC1 q ^ (2 * q)⁻¹ := Real.rpow_nonneg (Real.exp_pos _).le _
    positivity
  have hCb0 : 0 ≤ bandConst q 0.3 2.30043 0.0132 :=
    bandConst_nonneg hq0 hq1.le (by norm_num) (by norm_num) (by norm_num)
  have hbot0 : 0 ≤ botPhi q 0.3 2.30043 0.0132 Λ TS :=
    botPhi_nonneg hq1.le (by norm_num) (by norm_num) (by norm_num) hΛ hTS0
  have hK0 : 0 ≤ (2.30043 : ℝ) ^ q * (1 + 0.3) ^ q * pfC1 q * omegaClean q
      * (3 / 2 : ℝ) ^ (q * (2 * q - 1)) := by
    have := omegaClean_nonneg hq1.le
    have : 0 ≤ pfC1 q := (Real.exp_pos _).le
    have : (0 : ℝ) ≤ 2.30043 ^ q := Real.rpow_nonneg (by norm_num) _
    have : (0 : ℝ) ≤ (1 + 0.3) ^ q := Real.rpow_nonneg (by norm_num) _
    have : (0 : ℝ) ≤ (3 / 2) ^ (q * (2 * q - 1)) := Real.rpow_nonneg (by norm_num) _
    positivity
  have h120 : 0 ≤ (12 : ℝ) ^ (1 - (2 * q)⁻¹) := Real.rpow_nonneg (by norm_num) _
  have hP0 : 0 ≤ 1 - (2 * q)⁻¹ := by
    have : (2 * q)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by positivity)]; linarith
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
  have htl0 : 0 ≤ 91 * Real.exp (97 * (q * (2 * q - 1))) * Real.exp (-(q * (2 * q - 1) * Λ)) :=
    by positivity
  set KK := (2.30043 : ℝ) ^ q * (1 + 0.3) ^ q * pfC1 q * omegaClean q
      * (3 / 2 : ℝ) ^ (q * (2 * q - 1)) with hKKdef
  set E91 := 91 * Real.exp (97 * (q * (2 * q - 1))) * Real.exp (-(q * (2 * q - 1) * Λ))
    with hE91def
  have hF : chaosF q 0.3 0.1 Λ TS W k
      = topPhi q + (12 : ℝ) ^ (1 - (2 * q)⁻¹) * (bandConst q 0.3 2.30043 0.0132 * ((k : ℝ) + 2)
        + botPhi q 0.3 2.30043 0.0132 Λ TS + KK * (W + E91) + 2 * (1 - (2 * q)⁻¹)) := by
    rw [chaosF, hKc, hEc]
  have hbr0 : 0 ≤ bandConst q 0.3 2.30043 0.0132 * ((k : ℝ) + 2)
      + botPhi q 0.3 2.30043 0.0132 Λ TS + KK * (W + E91) + 2 * (1 - (2 * q)⁻¹) := by
    have := mul_nonneg hCb0 hk0
    have := mul_nonneg hK0 (add_nonneg hW0 htl0)
    linarith
  have hF0 : 0 ≤ chaosF q 0.3 0.1 Λ TS W k := by
    rw [hF]; exact add_nonneg htop0 (mul_nonneg h120 hbr0)
  -- the total times `d`
  set G := Ntop * Nd + N12 * (NCb * Nk + NBot * Nd + NK * (NW + Ntl) + NP) with hGdef
  have hFd : chaosF q 0.3 0.1 Λ TS W k * d ≤ G := by
    rw [hF]
    have e : (topPhi q + (12 : ℝ) ^ (1 - (2 * q)⁻¹) * (bandConst q 0.3 2.30043 0.0132
          * ((k : ℝ) + 2) + botPhi q 0.3 2.30043 0.0132 Λ TS + KK * (W + E91)
          + 2 * (1 - (2 * q)⁻¹))) * d
        = topPhi q * d + (12 : ℝ) ^ (1 - (2 * q)⁻¹) * (bandConst q 0.3 2.30043 0.0132
          * (((k : ℝ) + 2) * d) + botPhi q 0.3 2.30043 0.0132 Λ TS * d
          + KK * (W * d + E91 * d) + 2 * (1 - (2 * q)⁻¹) * d) := by ring
    rw [e]
    have hNtop0 : 0 ≤ Ntop := le_trans htop0 htop
    have hNCb0 : 0 ≤ NCb := le_trans hCb0 hCb
    have hNBot0 : 0 ≤ NBot := le_trans hbot0 hbot
    have hNK0 : 0 ≤ NK := le_trans hK0 hK
    have hN120 : 0 ≤ N12 := le_trans h120 h12
    have t1 : topPhi q * d ≤ Ntop * Nd := mul_le_mul htop hd hd0.le hNtop0
    have t2 : bandConst q 0.3 2.30043 0.0132 * (((k : ℝ) + 2) * d) ≤ NCb * Nk :=
      mul_le_mul hCb hk (mul_nonneg hk0 hd0.le) hNCb0
    have t3 : botPhi q 0.3 2.30043 0.0132 Λ TS * d ≤ NBot * Nd :=
      mul_le_mul hbot hd hd0.le hNBot0
    have t4 : KK * (W * d + E91 * d) ≤ NK * (NW + Ntl) :=
      mul_le_mul hK (add_le_add hW htl) (add_nonneg (mul_nonneg hW0 hd0.le)
        (mul_nonneg htl0 hd0.le)) hNK0
    have hin0 : 0 ≤ bandConst q 0.3 2.30043 0.0132 * (((k : ℝ) + 2) * d)
        + botPhi q 0.3 2.30043 0.0132 Λ TS * d + KK * (W * d + E91 * d)
        + 2 * (1 - (2 * q)⁻¹) * d := by
      have := mul_nonneg hCb0 (mul_nonneg hk0 hd0.le)
      have := mul_nonneg hbot0 hd0.le
      have := mul_nonneg hK0 (add_nonneg (mul_nonneg hW0 hd0.le) (mul_nonneg htl0 hd0.le))
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP0) hd0.le
      linarith
    have t5 := mul_le_mul h12 (show bandConst q 0.3 2.30043 0.0132 * (((k : ℝ) + 2) * d)
        + botPhi q 0.3 2.30043 0.0132 Λ TS * d + KK * (W * d + E91 * d)
        + 2 * (1 - (2 * q)⁻¹) * d ≤ NCb * Nk + NBot * Nd + NK * (NW + Ntl) + NP by linarith)
      hin0 hN120
    linarith
  -- the power
  have hG0 : 0 < G := by linarith
  have hpow := Real.rpow_le_rpow (mul_nonneg hF0 hd0.le) hFd (by linarith : (0 : ℝ) ≤ 2 * q)
  rw [Real.mul_rpow hF0 hd0.le] at hpow
  have hGq : G ^ (2 * q) ≤ Real.exp (2 * qu * Real.log G) := by
    rw [Real.rpow_def_of_pos hG0]
    exact Real.exp_le_exp.2 (by nlinarith [Real.log_nonneg hG1])
  have hunit : d ^ (2 * q) * ((2 * q - 1) ^ (-(3 / 4 : ℝ)) * (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1))))
      = 1 := by
    rw [hddef, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    rw [show 3 / 4 * (2 * q) + (-(3 / 4) + -(3 / 4 * (2 * q - 1))) = (0 : ℝ) by ring,
      Real.rpow_zero]
  have hm0 : 0 ≤ (2 * q - 1) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hδ.le _
  have hdd0 : 0 ≤ (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1))) := Real.rpow_nonneg hδ.le _
  calc chaosF q 0.3 0.1 Λ TS W k ^ (2 * q)
      = chaosF q 0.3 0.1 Λ TS W k ^ (2 * q) * d ^ (2 * q)
        * ((2 * q - 1) ^ (-(3 / 4 : ℝ)) * (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1)))) := by
        rw [mul_assoc, hunit, mul_one]
    _ ≤ Real.exp (2 * qu * Real.log G)
        * ((2 * q - 1) ^ (-(3 / 4 : ℝ)) * (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1)))) :=
        mul_le_mul_of_nonneg_right (le_trans hpow hGq) (mul_nonneg hm0 hdd0)
    _ = Real.exp (2 * qu * Real.log G) * (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1)))
        * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by ring
    _ ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hm0
        exact le_trans (mul_le_mul_of_nonneg_left hdd (Real.exp_pos _).le) hfin

/-! ### The windows' bound in units of `δ^{-3/4}` -/

/-- **The Gamma bound in units of `A a^{-3/4}`** at `q ≤ 0.50015`: `B ≤ A a^{-3/4}·1.254`. -/
lemma chaosB_le {q : ℝ} (hq0 : 1 / 2 < q) (hqu : q ≤ 50015 / 100000) :
    chaosB (q * (2 * q - 1)) (chaosAhat q)
      ≤ chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (627 / 500)) := by
  have ha : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hau : q * (2 * q - 1) ≤ 15005 / 100000000 := by nlinarith
  exact profSum_gamma_le (G := 627 / 500) (cu := 17368 / 1000) ha hau
    (chaosAhat_ge hq0.le (by linarith)) (by interval_decide (trust := kernel)) (by norm_num)
    (by interval_decide (trust := kernel))

/-- `(qδ)^{-3/4}δ^{3/4} = q^{-3/4}`. -/
lemma rpow_mul_neg_three_quarters {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    (q * δ) ^ (-(3 / 4 : ℝ)) * δ ^ (3 / 4 : ℝ) = q ^ (-(3 / 4 : ℝ)) := by
  rw [Real.mul_rpow hq.le hδ.le, mul_assoc, ← Real.rpow_add hδ]
  norm_num

/-- `(0.003/(qδ) + 1.001)^{3/4}δ^{3/4} = (0.003/q + 1.001δ)^{3/4}`. -/
lemma height_rpow_mul {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    (0.003 / (q * δ) + 1.001) ^ (3 / 4 : ℝ) * δ ^ (3 / 4 : ℝ)
      = (0.003 / q + 1.001 * δ) ^ (3 / 4 : ℝ) := by
  rw [← Real.mul_rpow (by positivity) hδ.le]
  congr 1
  field_simp

/-- `e^{-t} ≤ 1/t` for `t > 0`. -/
lemma exp_neg_le_inv {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ 1 / t := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le ht (by linarith [Real.add_one_le_exp t])

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 4000000 in
-- the pieces over the cell, each at its end
/-- **The chaos regime's reduction to its pieces.**  For `½ ≤ q_l ≤ q ≤ q_u ≤ 0.50015`,
`½ < q`, `x ≥ 3` with `(2q - 1)log log x ≥ 1`, the chain's parameters at `q` (the height
`X = 0.003/a ≥ 5`, `n₀`, `k`), bounds `M₁`, `M₃`, `N_s` on the short levels' two terms and the
suppression, `N_k` on `(k+2)δ^{3/4}` and `N_δ` on `δ^{-(3/4)δ}`, and numerals bounding the cell's
`q`-pieces, whose total `G` has `G^{2q_u}N_δ ≤ 25`:
`E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`. -/
theorem chaos_cell_core {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql qu L0 Nc Nql Ntop NCb NBot NK N12 Nd NX NW Nsupp M1 M3 Nk Ntl NP Ndd : ℝ}
    {n₀ k : ℕ} (hql : 1 / 2 ≤ ql) (hq0 : 1 / 2 < q) (hq : ql ≤ q) (hqu : q ≤ qu)
    (hqu1 : qu ≤ 50015 / 100000) (hx3 : 3 ≤ x) (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x))
    (hL0 : 11.5 ≤ L0) (hL0u : L0 ≤ 1 / (2 * qu - 1))
    (hXh : 5 ≤ 0.003 / (q * (2 * q - 1)))
    (hn₀ : Real.log (3 * (0.003 / (q * (2 * q - 1)))) < 10 / 3 * 2 ^ n₀)
    (hfar : 1 ≤ (q * (2 * q - 1) - (2 * q - 1) / 1000)
      * (Real.exp (0.003 / (q * (2 * q - 1))) / 3))
    (hk : 1 ≤ 10 / 3 * (q * (2 * q - 1) - (2 * q - 1) / 1000) * 2 ^ k)
    (hmin : min (0.003 / (q * (2 * q - 1)) + 1.001) 2007 * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ M1)
    (hn0d : (n₀ : ℝ) * (Real.log (3 * (0.003 / (q * (2 * q - 1)))) + 1.001)
      * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ M3)
    (hsupp : Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000)
      * (Real.exp (0.003 / (q * (2 * q - 1))) / 3))) ≤ Nsupp)
    (hkd : ((k : ℝ) + 2) * (2 * q - 1) ^ (3 / 4 : ℝ) ≤ Nk)
    (hdd : (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1))) ≤ Ndd)
    (hc1 : Real.exp (ql * Real.log (cenHat ql qu)) ≤ Nc)
    (hc2 : Real.exp (qu * Real.log (cenHat ql qu)) ≤ Nc)
    (htop : topHat ql qu ≤ Ntop) (hCb : bandConstHat ql qu Nc ≤ NCb)
    (hbot : botHat ql qu Nc L0 (129289 / 10000) ≤ NBot)
    (hK : Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3) * pfC1Hat ql qu
      * (Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
        * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)))
      * Real.exp (qu * (2 * qu - 1) * Real.log 1.5) ≤ NK)
    (h12 : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 12) ≤ N12)
    (hd : Real.exp (3 / 4 * Real.log (2 * qu - 1)) ≤ Nd)
    (hNql : Real.exp (-(3 / 4 * Real.log ql)) ≤ Nql)
    (hXn : Real.exp (3 / 4 * Real.log (0.003 / ql + 1.001 * (2 * qu - 1))) ≤ NX)
    (hNW : M1 + 64233 / 10000 * (4 / 3 * NX) + M3 + 64233 / 10000 * (Nql * (309 / 200))
      + 2 * Nsupp * (64233 / 10000 * (Nql * (627 / 500))) ≤ NW)
    (htl : 91 * Real.exp (97 * (qu * (2 * qu - 1))) * Real.exp (-ql) * Nd ≤ Ntl)
    (hP : 2 * (1 - (2 * qu)⁻¹) * Nd ≤ NP)
    (hG1 : 1 ≤ Ntop * Nd + N12 * (NCb * Nk + NBot * Nd + NK * (NW + Ntl) + NP))
    (hfin : Real.exp (2 * qu * Real.log (Ntop * Nd + N12 * (NCb * Nk + NBot * Nd
      + NK * (NW + Ntl) + NP))) * Ndd ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  have hq1 : q < 1 := by linarith
  have hqu1' : qu < 1 := by linarith
  have hq0' : 0 < q := by linarith
  have hql0 : 0 < ql := by linarith
  have hδ : 0 < 2 * q - 1 := by linarith
  have hδu : 0 < 2 * qu - 1 := by linarith
  have hδδ : 2 * q - 1 ≤ 2 * qu - 1 := by linarith
  -- `Λ`
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by
    by_contra hc
    push Not at hc
    nlinarith
  have hΛge : 1 / (2 * qu - 1) ≤ Λ := by
    rw [div_le_iff₀ hδu]
    nlinarith
  have hL0Λ : L0 ≤ Λ := le_trans hL0u hΛge
  have hΛ200 : 200 ≤ Λ := by
    have : (200 : ℝ) ≤ 1 / (2 * qu - 1) := by rw [le_div_iff₀ hδu]; linarith
    linarith
  have ha0 : 0 < q * (2 * q - 1) := mul_pos hq0' hδ
  have hau : q * (2 * q - 1) ≤ qu * (2 * qu - 1) := mul_two_mul_sub_one_le hq0.le hqu
  have hAl := chaosAhat_ge hq0.le hq1
  have hAu := chaosAhat_le_num hq0.le (by linarith)
  have hA0 : 0 ≤ chaosAhat q := by linarith
  -- the assembly
  have hB : ∀ N, profSum (q * (2 * q - 1)) (chaosAhat q) N
      ≤ chaosB (q * (2 * q - 1)) (chaosAhat q) := fun N => profSum_le_gamma ha0 hA0 N
  have main := integral_rpow_weightedRademacherSum_le_chaosF hX (η' := 0.3) (ε := 0.1)
    (Xh := 0.003 / (q * (2 * q - 1))) (n₀ := n₀) (k := k) (TS := 129289 / 10000)
    hq0 hq1 (by norm_num) (by norm_num) hx3 hΛ200 (by norm_num)
    (fun z hz => aboveTS_1 hq0.le (by linarith) z hz) hXh hB hn₀ hfar hk
    (chaos_transition_num hq0 (by linarith))
  refine le_trans main ?_
  rw [mul_comm (25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)))]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Real.log_nonneg (by
    have := Real.add_one_le_exp (Real.log (Real.log x))
    rw [Real.exp_log (Real.log_pos (by linarith))] at this
    linarith)) _)
  -- the pieces over the cell
  have hcen0 : 0 < cenHat ql qu := by
    rw [cenHat]
    have : 0 ≤ Real.exp (2 * (1 - ql) * 0.5158) - 1 :=
      sub_nonneg.2 (Real.one_le_exp (by nlinarith))
    positivity
  have hcen : cenClean q ^ q ≤ Nc :=
    le_trans (Real.rpow_le_rpow (cenClean_nonneg hq1.le)
      (cenClean_le_cenHat hql hq hqu (by linarith)) hq0'.le)
      (rpow_le_of_exp_log_both hcen0 hq hqu hc1 hc2)
  set d := (2 * q - 1) ^ (3 / 4 : ℝ) with hddef
  have hd0 : 0 < d := Real.rpow_pos_of_pos hδ _
  have hdN : d ≤ Nd := by
    refine le_trans ?_ hd
    rw [hddef, Real.rpow_def_of_pos hδ, mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log hδ hδδ) (by norm_num))
  have hql34 : q ^ (-(3 / 4 : ℝ)) ≤ Nql := by
    refine le_trans ?_ hNql
    rw [Real.rpow_def_of_pos hq0']
    exact Real.exp_le_exp.2 (by nlinarith [Real.log_le_log hql0 hq])
  have hql340 : 0 ≤ q ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hq0'.le _
  -- the windows' bound `W d`
  have hW : chainW (q * (2 * q - 1) - (2 * q - 1) / 1000) (chaosAhat q)
      (0.003 / (q * (2 * q - 1))) (chaosB (q * (2 * q - 1)) (chaosAhat q))
      (chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200))) n₀ * d ≤ NW := by
    rw [chainW]
    have t2 : chaosAhat q * (4 / 3 * (0.003 / (q * (2 * q - 1)) + 1.001) ^ (3 / 4 : ℝ)) * d
        ≤ 64233 / 10000 * (4 / 3 * NX) := by
      have e : chaosAhat q * (4 / 3 * (0.003 / (q * (2 * q - 1)) + 1.001) ^ (3 / 4 : ℝ)) * d
          = chaosAhat q * (4 / 3 * (0.003 / q + 1.001 * (2 * q - 1)) ^ (3 / 4 : ℝ)) := by
        rw [← height_rpow_mul hq0' hδ, hddef]; ring
      rw [e]
      have h1 : (0.003 / q + 1.001 * (2 * q - 1)) ^ (3 / 4 : ℝ) ≤ NX := by
        refine le_trans ?_ hXn
        rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
          ?_) (by norm_num))
        have : 0.003 / q ≤ 0.003 / ql := div_le_div_of_nonneg_left (by norm_num) hql0 hq
        linarith
      have h0 : 0 ≤ (0.003 / q + 1.001 * (2 * q - 1)) ^ (3 / 4 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      exact mul_le_mul hAu (by linarith) (by positivity) (by norm_num)
    have t4 : chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200)) * d
        ≤ 64233 / 10000 * (Nql * (309 / 200)) := by
      have e : chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200)) * d
          = chaosAhat q * (q ^ (-(3 / 4 : ℝ)) * (309 / 200)) := by
        rw [← rpow_mul_neg_three_quarters hq0' hδ, hddef]; ring
      rw [e]
      exact mul_le_mul hAu (by linarith) (by positivity) (by norm_num)
    have t5 : 2 * Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000)
          * (Real.exp (0.003 / (q * (2 * q - 1))) / 3)))
        * chaosB (q * (2 * q - 1)) (chaosAhat q) * d
        ≤ 2 * Nsupp * (64233 / 10000 * (Nql * (627 / 500))) := by
      have hBd : chaosB (q * (2 * q - 1)) (chaosAhat q) * d
          ≤ 64233 / 10000 * (Nql * (627 / 500)) := by
        have h1 := mul_le_mul_of_nonneg_right (chaosB_le hq0 (by linarith)) hd0.le
        have e : chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (627 / 500)) * d
            = chaosAhat q * (q ^ (-(3 / 4 : ℝ)) * (627 / 500)) := by
          rw [← rpow_mul_neg_three_quarters hq0' hδ, hddef]; ring
        rw [e] at h1
        exact le_trans h1 (mul_le_mul hAu (by linarith) (by positivity) (by norm_num))
      have hB0 : 0 ≤ chaosB (q * (2 * q - 1)) (chaosAhat q) := le_trans (profSum_nonneg hA0 0)
        (hB 0)
      have hs0 : 0 ≤ Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000)
          * (Real.exp (0.003 / (q * (2 * q - 1))) / 3))) := (Real.exp_pos _).le
      have := mul_le_mul hsupp hBd (mul_nonneg hB0 hd0.le) (le_trans hs0 hsupp)
      nlinarith
    have e : (min (0.003 / (q * (2 * q - 1)) + 1.001) 2007
        + chaosAhat q * (4 / 3 * (0.003 / (q * (2 * q - 1)) + 1.001) ^ (3 / 4 : ℝ))
        + n₀ * (Real.log (3 * (0.003 / (q * (2 * q - 1)))) + 1.001)
        + chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200))
        + 2 * Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000)
          * (Real.exp (0.003 / (q * (2 * q - 1))) / 3)))
          * chaosB (q * (2 * q - 1)) (chaosAhat q)) * d
        = min (0.003 / (q * (2 * q - 1)) + 1.001) 2007 * d
          + chaosAhat q * (4 / 3 * (0.003 / (q * (2 * q - 1)) + 1.001) ^ (3 / 4 : ℝ)) * d
          + n₀ * (Real.log (3 * (0.003 / (q * (2 * q - 1)))) + 1.001) * d
          + chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200)) * d
          + 2 * Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000)
            * (Real.exp (0.003 / (q * (2 * q - 1))) / 3)))
            * chaosB (q * (2 * q - 1)) (chaosAhat q) * d := by ring
    rw [e]
    linarith
  -- the other pieces
  have hW0 : 0 ≤ chainW (q * (2 * q - 1) - (2 * q - 1) / 1000) (chaosAhat q)
      (0.003 / (q * (2 * q - 1))) (chaosB (q * (2 * q - 1)) (chaosAhat q))
      (chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (309 / 200))) n₀ := by
    rw [chainW]
    have h1 : 0 ≤ min (0.003 / (q * (2 * q - 1)) + 1.001) 2007 :=
      le_min (by positivity) (by norm_num)
    have h2 : 0 ≤ Real.log (3 * (0.003 / (q * (2 * q - 1)))) + 1.001 := by
      have : (1 : ℝ) ≤ 3 * (0.003 / (q * (2 * q - 1))) := by linarith
      linarith [Real.log_nonneg this]
    have h3 : 0 ≤ chaosB (q * (2 * q - 1)) (chaosAhat q) :=
      le_trans (profSum_nonneg hA0 0) (hB 0)
    have h4 : 0 ≤ (q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg ha0.le _
    have h5 : 0 ≤ (0.003 / (q * (2 * q - 1)) + 1.001) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have htopq : topPhi q ≤ Ntop := le_trans (topPhi_le_topHat hql hq hqu (by linarith)) htop
  have hCbq : bandConst q 0.3 2.30043 0.0132 ≤ NCb :=
    le_trans (bandConst_le_hat hql hq hqu (by linarith) hcen) hCb
  have hbotq : botPhi q 0.3 2.30043 0.0132 Λ (129289 / 10000) ≤ NBot :=
    le_trans (botPhi_le_botHat hql hq hqu (by linarith) hL0 hL0Λ (by norm_num) hcen) hbot
  have hKq : (2.30043 : ℝ) ^ q * (1 + 0.3) ^ q * pfC1 q * omegaClean q
      * (3 / 2 : ℝ) ^ (q * (2 * q - 1)) ≤ NK := by
    refine le_trans ?_ hK
    have h1 : (2.30043 : ℝ) ^ q ≤ Real.exp (qu * Real.log 2.30043) :=
      rpow_le_exp_of_one_le (by norm_num) hqu
    have h2 : (1 + (0.3 : ℝ)) ^ q ≤ Real.exp (qu * Real.log 1.3) :=
      rpow_le_exp_hi (by norm_num) (by norm_num) (by norm_num) hq0'.le hqu
    have h3 := pfC1_le_pfC1Hat hql hq hqu (by linarith)
    have h4 := omegaClean_le_hat hql hq hqu (by linarith)
    have h5 : (3 / 2 : ℝ) ^ (q * (2 * q - 1)) ≤ Real.exp (qu * (2 * qu - 1) * Real.log 1.5) := by
      rw [show (3 / 2 : ℝ) = 1.5 by norm_num]
      exact rpow_le_exp_of_one_le (by norm_num) hau
    have h10 : (0 : ℝ) ≤ 2.30043 ^ q := Real.rpow_nonneg (by norm_num) _
    have h20 : (0 : ℝ) ≤ (1 + 0.3) ^ q := Real.rpow_nonneg (by norm_num) _
    have h30 : 0 ≤ pfC1 q := (Real.exp_pos _).le
    have h40 := omegaClean_nonneg hq1.le
    have h50 : (0 : ℝ) ≤ (3 / 2) ^ (q * (2 * q - 1)) := Real.rpow_nonneg (by norm_num) _
    have hH0 : 0 ≤ pfC1Hat ql qu := by rw [pfC1Hat]; positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 h20 (Real.exp_pos _).le) h3 h30
      (by positivity)) h4 h40 (by positivity)) h5 h50 (by positivity)
  have h12q : (12 : ℝ) ^ (1 - (2 * q)⁻¹) ≤ N12 := by
    refine le_trans ?_ h12
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by norm_num)))
    have : (2 * qu)⁻¹ ≤ (2 * q)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    linarith
  have htlq : 91 * Real.exp (97 * (q * (2 * q - 1))) * Real.exp (-(q * (2 * q - 1) * Λ)) * d
      ≤ Ntl := by
    refine le_trans ?_ htl
    have h1 : Real.exp (97 * (q * (2 * q - 1))) ≤ Real.exp (97 * (qu * (2 * qu - 1))) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(q * (2 * q - 1) * Λ)) ≤ Real.exp (-ql) := by
      refine Real.exp_le_exp.2 ?_
      have h := mul_le_mul_of_nonneg_left hδΛ hq0'.le
      rw [mul_one, ← mul_assoc] at h
      linarith only [h, hq]
    have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 91))
      h2 (Real.exp_pos _).le (by positivity)) hdN hd0.le (by positivity)
    linarith
  have hPq : 2 * (1 - (2 * q)⁻¹) * d ≤ NP := by
    refine le_trans ?_ hP
    have : (2 * qu)⁻¹ ≤ (2 * q)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    have h0 : 0 ≤ 1 - (2 * q)⁻¹ := by
      have : (2 * q)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by positivity)]; linarith
      linarith
    exact mul_le_mul (by linarith) hdN hd0.le (by
      have : (2 * qu)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by linarith)]; linarith
      linarith)
  exact chaosF_rpow_le hq0 hqu hqu1' hΛ0 (by norm_num) hW0 htopq hCbq hbotq hKq h12q hdN hW hkd
    htlq hPq hdd hG1 hfin

set_option maxHeartbeats 4000000 in
-- the cell's chain parameters from its ends
/-- **A cell of the chaos regime.**  For `½ < q_l ≤ q ≤ q_u ≤ 0.50015`, `x ≥ 3` with
`(2q - 1)log log x ≥ 1`, a height `X_c ≤ 0.003/a_u`, naturals `n₀`, `k` for the chain's short
levels and the bands' count, and numerals bounding the pieces of `RMF.chaosF` over the cell (each an
`interval_decide` check in the cell's instance) whose total `G` has `G^{2q_u}N_δ ≤ 25`:

`E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`. -/
theorem above_cell_chaos {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql qu L0 Xc Nc Nql Ntop NCb NBot NK N12 Nd NMin NX NW Nsupp Ntl NP Ndd : ℝ}
    {n₀ k : ℕ} (hql : 1 / 2 < ql) (hq : ql ≤ q) (hqu : q ≤ qu) (hqu1 : qu ≤ 50015 / 100000)
    (hx3 : 3 ≤ x) (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x))
    (hL0 : 11.5 ≤ L0) (hL0u : L0 ≤ 1 / (2 * qu - 1))
    (hXc : Xc ≤ 0.003 / (qu * (2 * qu - 1))) (hXc5 : 5 ≤ Xc)
    (hfar : 1 ≤ (2 * ql - 1) * (ql - 1 / 1000) * (Real.exp Xc / 3))
    (hn₀ : Real.log (0.009 / (ql * (2 * ql - 1))) < 10 / 3 * 2 ^ n₀)
    (hk : 1 ≤ 10 / 3 * ((2 * ql - 1) * (ql - 1 / 1000)) * 2 ^ k)
    (hc1 : Real.exp (ql * Real.log (cenHat ql qu)) ≤ Nc)
    (hc2 : Real.exp (qu * Real.log (cenHat ql qu)) ≤ Nc)
    (htop : topHat ql qu ≤ Ntop) (hCb : bandConstHat ql qu Nc ≤ NCb)
    (hbot : botHat ql qu Nc L0 (129289 / 10000) ≤ NBot)
    (hK : Real.exp (qu * Real.log 2.30043) * Real.exp (qu * Real.log 1.3) * pfC1Hat ql qu
      * (Real.exp (ql * Real.log (windowWHat ql * 0.318311 * (1 / 1.498)))
        * Real.exp (0.0185 * (qu * (2 * qu - 1) + qu)))
      * Real.exp (qu * (2 * qu - 1) * Real.log 1.5) ≤ NK)
    (h12 : Real.exp ((1 - (2 * qu)⁻¹) * Real.log 12) ≤ N12)
    (hd : Real.exp (3 / 4 * Real.log (2 * qu - 1)) ≤ Nd)
    (hNql : Real.exp (-(3 / 4 * Real.log ql)) ≤ Nql)
    (hmin : min (0.003 / (ql * (2 * ql - 1)) + 1.001) 2007 ≤ NMin)
    (hXn : Real.exp (3 / 4 * Real.log (0.003 / ql + 1.001 * (2 * qu - 1))) ≤ NX)
    (hsupp : 3 / ((2 * ql - 1) * (ql - 1 / 1000) * Real.exp Xc) ≤ Nsupp)
    (hNW : NMin * Nd + 64233 / 10000 * (4 / 3 * NX)
      + n₀ * (Real.log (0.009 / (ql * (2 * ql - 1))) + 1.001) * Nd
      + 64233 / 10000 * (Nql * (309 / 200))
      + 2 * Nsupp * (64233 / 10000 * (Nql * (627 / 500))) ≤ NW)
    (htl : 91 * Real.exp (97 * (qu * (2 * qu - 1))) * Real.exp (-ql) * Nd ≤ Ntl)
    (hP : 2 * (1 - (2 * qu)⁻¹) * Nd ≤ NP)
    (hdd : Real.exp (3 / 4 * (2 * qu - 1) * -Real.log (2 * ql - 1)) ≤ Ndd)
    (hG1 : 1 ≤ Ntop * Nd + N12 * (NCb * ((k + 2) * Nd) + NBot * Nd + NK * (NW + Ntl) + NP))
    (hfin : Real.exp (2 * qu * Real.log (Ntop * Nd + N12 * (NCb * ((k + 2) * Nd) + NBot * Nd
      + NK * (NW + Ntl) + NP))) * Ndd ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  have hq0 : 1 / 2 < q := lt_of_lt_of_le hql hq
  have hq0' : 0 < q := by linarith
  have hql0 : 0 < ql := by linarith
  have hδ : 0 < 2 * q - 1 := by linarith
  have hδl : 0 < 2 * ql - 1 := by linarith
  have hδu : 0 < 2 * qu - 1 := by linarith
  have hδδ : 2 * q - 1 ≤ 2 * qu - 1 := by linarith
  have ha0 : 0 < q * (2 * q - 1) := mul_pos hq0' hδ
  have hal : ql * (2 * ql - 1) ≤ q * (2 * q - 1) := mul_two_mul_sub_one_le hql.le hq
  have hau : q * (2 * q - 1) ≤ qu * (2 * qu - 1) := mul_two_mul_sub_one_le hq0.le hqu
  have hal0 : 0 < ql * (2 * ql - 1) := mul_pos hql0 hδl
  have ha'e : q * (2 * q - 1) - (2 * q - 1) / 1000 = (2 * q - 1) * (q - 1 / 1000) := by ring
  have ha'l : (2 * ql - 1) * (ql - 1 / 1000) ≤ q * (2 * q - 1) - (2 * q - 1) / 1000 := by
    rw [ha'e]; exact mul_le_mul (by linarith) (by linarith) (by linarith) hδ.le
  have ha'l0 : 0 < (2 * ql - 1) * (ql - 1 / 1000) := mul_pos hδl (by linarith)
  have hXh : Xc ≤ 0.003 / (q * (2 * q - 1)) :=
    le_trans hXc (div_le_div_of_nonneg_left (by norm_num) ha0 hau)
  have hXhl : 0.003 / (q * (2 * q - 1)) ≤ 0.003 / (ql * (2 * ql - 1)) :=
    div_le_div_of_nonneg_left (by norm_num) hal0 hal
  have hlog3 : Real.log (3 * (0.003 / (q * (2 * q - 1))))
      ≤ Real.log (0.009 / (ql * (2 * ql - 1))) := by
    rw [show (3 : ℝ) * (0.003 / (q * (2 * q - 1))) = 0.009 / (q * (2 * q - 1)) by ring]
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hal0 hal)
  have hexpX : Real.exp Xc ≤ Real.exp (0.003 / (q * (2 * q - 1))) := Real.exp_le_exp.2 hXh
  have hfar' : 1 ≤ (q * (2 * q - 1) - (2 * q - 1) / 1000)
      * (Real.exp (0.003 / (q * (2 * q - 1))) / 3) :=
    le_trans hfar (mul_le_mul ha'l (by linarith) (by positivity) (by linarith))
  have hk' : 1 ≤ 10 / 3 * (q * (2 * q - 1) - (2 * q - 1) / 1000) * 2 ^ k :=
    le_trans hk (by
      have : (0 : ℝ) < 2 ^ k := by positivity
      nlinarith)
  set d := (2 * q - 1) ^ (3 / 4 : ℝ) with hddef
  have hd0 : 0 < d := Real.rpow_pos_of_pos hδ _
  have hdN : d ≤ Nd := by
    refine le_trans ?_ hd
    rw [hddef, Real.rpow_def_of_pos hδ, mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log hδ hδδ) (by norm_num))
  have hmin' : min (0.003 / (q * (2 * q - 1)) + 1.001) 2007 * d ≤ NMin * Nd := by
    have hmin0 : 0 ≤ min (0.003 / (q * (2 * q - 1)) + 1.001) 2007 :=
      le_min (by positivity) (by norm_num)
    exact mul_le_mul (le_trans (min_le_min (by linarith) le_rfl) hmin) hdN hd0.le
      (le_trans hmin0 (le_trans (min_le_min (by linarith) le_rfl) hmin))
  have hn0d : (n₀ : ℝ) * (Real.log (3 * (0.003 / (q * (2 * q - 1)))) + 1.001) * d
      ≤ n₀ * (Real.log (0.009 / (ql * (2 * ql - 1))) + 1.001) * Nd := by
    have hl3 : 0 ≤ Real.log (3 * (0.003 / (q * (2 * q - 1)))) + 1.001 := by
      have : (1 : ℝ) ≤ 3 * (0.003 / (q * (2 * q - 1))) := by linarith
      linarith [Real.log_nonneg this]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) hdN hd0.le
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  have hsupp' : Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000)
      * (Real.exp (0.003 / (q * (2 * q - 1))) / 3))) ≤ Nsupp := by
    have ht : 0 < (q * (2 * q - 1) - (2 * q - 1) / 1000)
        * (Real.exp (0.003 / (q * (2 * q - 1))) / 3) := by linarith
    refine le_trans (exp_neg_le_inv ht) (le_trans ?_ hsupp)
    rw [div_le_div_iff₀ ht (by positivity)]
    have := mul_le_mul ha'l hexpX (Real.exp_pos _).le (by linarith)
    nlinarith
  have hkd : ((k : ℝ) + 2) * d ≤ (k + 2) * Nd :=
    mul_le_mul_of_nonneg_left hdN (by positivity)
  have hddq : (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1))) ≤ Ndd := by
    refine le_trans ?_ hdd
    rw [Real.rpow_def_of_pos hδ]
    refine Real.exp_le_exp.2 ?_
    have h1 : Real.log (2 * ql - 1) ≤ Real.log (2 * q - 1) := Real.log_le_log hδl (by linarith)
    have h2 : Real.log (2 * q - 1) ≤ 0 := Real.log_nonpos hδ.le (by linarith)
    have h4 : (2 * q - 1) * -Real.log (2 * q - 1) ≤ (2 * qu - 1) * -Real.log (2 * ql - 1) :=
      mul_le_mul hδδ (by linarith) (by linarith) hδu.le
    linarith only [h4]
  exact chaos_cell_core hX hql.le hq0 hq hqu hqu1 hx3 hδΛ hL0 hL0u (le_trans hXc5 hXh)
    (lt_of_le_of_lt hlog3 hn₀) hfar' hk' hmin' hn0d hsupp' hkd hddq hc1 hc2 htop hCb hbot hK
    h12 hd hNql hXn hNW htl hP hG1 hfin

/-! ### The lowest cell, `δ ≤ 2·10⁻⁸` -/

/-- `log y ≤ y^ε/ε` at `ε = 1/8` and `ε = 1/2`. -/
lemma log_le_eight_rpow {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 8 * y ^ (1 / 8 : ℝ) := by
  have := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 8)
  rw [div_eq_mul_inv] at this
  norm_num at this ⊢
  linarith

lemma log_le_two_rpow {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
  have := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 2)
  rw [div_eq_mul_inv] at this
  norm_num at this ⊢
  linarith

/-- **The short levels' count, analytically**: for `y ≥ 1`,
`⌈log y⌉(log y + 1.001) ≤ 128y^{1/4} + 2.004002`. -/
lemma ceil_log_mul_le {y : ℝ} (hy : 1 ≤ y) :
    (⌈Real.log y⌉₊ : ℝ) * (Real.log y + 1.001) ≤ 128 * y ^ (1 / 4 : ℝ) + 2.004002 := by
  have hL0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hn : (⌈Real.log y⌉₊ : ℝ) ≤ Real.log y + 1 := (Nat.ceil_lt_add_one hL0).le
  have h1 := log_le_eight_rpow (by linarith : (0 : ℝ) ≤ y)
  have h8 : (y ^ (1 / 8 : ℝ)) ^ 2 = y ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have h80 : 0 ≤ y ^ (1 / 8 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsq : Real.log y ^ 2 ≤ 64 * y ^ (1 / 4 : ℝ) := by
    rw [← h8]; nlinarith
  calc (⌈Real.log y⌉₊ : ℝ) * (Real.log y + 1.001)
      ≤ (Real.log y + 1) * (Real.log y + 1.001) :=
        mul_le_mul_of_nonneg_right hn (by linarith)
    _ ≤ 2 * Real.log y ^ 2 + 2.004002 := by nlinarith [sq_nonneg (Real.log y - 1.001)]
    _ ≤ 128 * y ^ (1 / 4 : ℝ) + 2.004002 := by linarith

/-- `(c/δ)^{s}δ^{t} = c^s δ^{t-s}` for `c, δ > 0`. -/
lemma div_rpow_mul_rpow {c δ s t : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    (c / δ) ^ s * δ ^ t = c ^ s * δ ^ (t - s) := by
  rw [Real.div_rpow hc.le hδ.le, Real.rpow_sub hδ]
  field_simp

set_option maxHeartbeats 4000000 in
-- the chain's parameters grow with `1/δ`; each is bounded analytically
/-- **The chaos regime's lowest cell**: for `½ < q ≤ ½ + 10⁻⁸`, `x ≥ 3` with
`(2q - 1)log log x ≥ 1`: `E|S(x)|^{2q} ≤ 25(2q - 1)^{-3/4}(log x)^{q(2q-1)}`.  The short levels'
count `n₀ = ⌈log 3X⌉`, the bands' count `k = ⌈log(0.3/a')/log 2⌉` and the suppression
`e^{-a'e^X/3} ≤ 72/(a'X⁴)` are bounded against `δ^{3/4}` by `log y ≤ y^ε/ε`. -/
theorem above_cell_chaos_low {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hq0 : 1 / 2 < q) (hqu : q ≤ 50000001 / 100000000) (hx3 : 3 ≤ x)
    (hδΛ : 1 ≤ (2 * q - 1) * Real.log (Real.log x)) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      ≤ 25 * (2 * q - 1) ^ (-(3 / 4 : ℝ)) * Real.log x ^ (q * (2 * q - 1)) := by
  have hq0' : 0 < q := by linarith
  have hδ : 0 < 2 * q - 1 := by linarith
  have hδ1 : 2 * q - 1 ≤ 2 / 100000000 := by linarith
  have ha0 : 0 < q * (2 * q - 1) := mul_pos hq0' hδ
  have hau : q * (2 * q - 1) ≤ 10000001 / 1000000000000000 := by
    have := mul_two_mul_sub_one_le hq0.le hqu
    linarith
  have ha'e : q * (2 * q - 1) - (2 * q - 1) / 1000 = (2 * q - 1) * (q - 1 / 1000) := by ring
  have ha'a : 998 / 1000 * (q * (2 * q - 1)) ≤ q * (2 * q - 1) - (2 * q - 1) / 1000 := by
    nlinarith
  have ha'δ : 499 / 1000 * (2 * q - 1) ≤ q * (2 * q - 1) - (2 * q - 1) / 1000 := by nlinarith
  have ha'0 : 0 < q * (2 * q - 1) - (2 * q - 1) / 1000 := by nlinarith
  set a := q * (2 * q - 1) with hadef
  set a' := a - (2 * q - 1) / 1000 with ha'def
  set Xh := 0.003 / a with hXhdef
  have hXh5 : 5 ≤ Xh := by rw [hXhdef, le_div_iff₀ ha0]; linarith
  have hXh0 : 0 < Xh := by linarith
  set d := (2 * q - 1) ^ (3 / 4 : ℝ) with hddef
  have hd0 : 0 < d := Real.rpow_pos_of_pos hδ _
  have hdN : d ≤ Real.exp (3 / 4 * Real.log (2 * (50000001 / 100000000) - 1)) := by
    rw [hddef, Real.rpow_def_of_pos hδ, mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log hδ (by linarith))
      (by norm_num))
  -- the short levels: `n₀ = ⌈log 3X⌉`
  have hy1 : 1 ≤ 3 * Xh := by linarith
  have hn₀ : Real.log (3 * Xh) < 10 / 3 * 2 ^ ⌈Real.log (3 * Xh)⌉₊ := by
    have h1 := Nat.le_ceil (Real.log (3 * Xh))
    have h2 : ((⌈Real.log (3 * Xh)⌉₊ : ℕ) : ℝ) < 2 ^ ⌈Real.log (3 * Xh)⌉₊ := by
      exact_mod_cast Nat.lt_two_pow_self
    have h3 : (0 : ℝ) < 2 ^ ⌈Real.log (3 * Xh)⌉₊ := by positivity
    linarith
  have hy14 : (3 * Xh) ^ (1 / 4 : ℝ) * d
      ≤ Real.exp (1 / 4 * Real.log 0.018) * Real.exp (1 / 2 * Real.log (2 / 100000000)) := by
    have hy : 3 * Xh ≤ 0.018 / (2 * q - 1) := by
      rw [hXhdef, hadef, show (3 : ℝ) * (0.003 / (q * (2 * q - 1))) = 0.009 / (q * (2 * q - 1))
        by ring, div_le_div_iff₀ ha0 hδ]
      nlinarith
    have h1 : (3 * Xh) ^ (1 / 4 : ℝ) * d ≤ (0.018 / (2 * q - 1)) ^ (1 / 4 : ℝ) * d :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hy (by norm_num)) hd0.le
    rw [hddef, div_rpow_mul_rpow (by norm_num) hδ] at h1
    refine le_trans h1 ?_
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hδ, mul_comm (Real.log 0.018),
      show (3 / 4 : ℝ) - 1 / 4 = 1 / 2 by norm_num]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hδ hδ1) (by norm_num)
  have hn0d : (⌈Real.log (3 * Xh)⌉₊ : ℝ) * (Real.log (3 * Xh) + 1.001) * d
      ≤ 128 * (Real.exp (1 / 4 * Real.log 0.018) * Real.exp (1 / 2 * Real.log (2 / 100000000)))
        + 2.004002 * Real.exp (3 / 4 * Real.log (2 * (50000001 / 100000000) - 1)) := by
    have h1 := mul_le_mul_of_nonneg_right (ceil_log_mul_le hy1) hd0.le
    have h2 : (128 * (3 * Xh) ^ (1 / 4 : ℝ) + 2.004002) * d
        = 128 * ((3 * Xh) ^ (1 / 4 : ℝ) * d) + 2.004002 * d := by ring
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left hy14 (by norm_num : (0 : ℝ) ≤ 128)
    have := mul_le_mul_of_nonneg_left hdN (by norm_num : (0 : ℝ) ≤ 2.004002)
    linarith
  -- the bands' count: `k = ⌈log(0.3/a')/log 2⌉`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set k := ⌈Real.log (0.3 / a') / Real.log 2⌉₊ with hkdef
  have hk : 1 ≤ 10 / 3 * a' * 2 ^ k := by
    have h1 : Real.log (0.3 / a') ≤ k * Real.log 2 := by
      have := Nat.le_ceil (Real.log (0.3 / a') / Real.log 2)
      rw [← hkdef, div_le_iff₀ hl2] at this
      exact this
    have h2 : 0.3 / a' ≤ 2 ^ k := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 0.3 / a'), show (2 : ℝ) ^ k
        = Real.exp (k * Real.log 2) by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
      exact Real.exp_le_exp.2 h1
    rw [div_le_iff₀ ha'0] at h2
    nlinarith
  have hkd : ((k : ℝ) + 2) * d ≤ 2 * 0.7755 / 0.6931 * Real.exp (1 / 4 * Real.log (2 / 100000000))
      + 3 * Real.exp (3 / 4 * Real.log (2 * (50000001 / 100000000) - 1)) := by
    have hl : 0 ≤ Real.log (0.3 / a') / Real.log 2 := div_nonneg (Real.log_nonneg (by
      rw [le_div_iff₀ ha'0]; linarith)) hl2.le
    have hk1 : (k : ℝ) ≤ Real.log (0.3 / a') / Real.log 2 + 1 := (Nat.ceil_lt_add_one hl).le
    have hlog : Real.log (0.3 / a') ≤ 2 * (0.3 / a') ^ (1 / 2 : ℝ) :=
      log_le_two_rpow (by positivity)
    have hr : (0.3 / a') ^ (1 / 2 : ℝ) ≤ (0.6013 / (2 * q - 1)) ^ (1 / 2 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      rw [div_le_div_iff₀ ha'0 hδ]
      nlinarith
    have hr2 : (0.6013 / (2 * q - 1)) ^ (1 / 2 : ℝ) * d
        ≤ 0.7755 * Real.exp (1 / 4 * Real.log (2 / 100000000)) := by
      rw [hddef, div_rpow_mul_rpow (by norm_num) hδ, show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num]
      refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hδ.le _) (by norm_num)
      · rw [show (0.7755 : ℝ) = (0.7755 ^ 2) ^ (1 / 2 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      · rw [Real.rpow_def_of_pos hδ, mul_comm]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log hδ hδ1)
          (by norm_num))
    have hl2' : 0.6931 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hkk : ((k : ℝ) + 2) ≤ 2 * (0.6013 / (2 * q - 1)) ^ (1 / 2 : ℝ) / 0.6931 + 3 := by
      have h1 : Real.log (0.3 / a') / Real.log 2 ≤ Real.log (0.3 / a') / 0.6931 :=
        div_le_div_of_nonneg_left (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 0.3 / a' by
          rw [le_div_iff₀ ha'0]; linarith)]) (by norm_num) hl2'
      have h2 : Real.log (0.3 / a') / 0.6931 ≤ 2 * (0.6013 / (2 * q - 1)) ^ (1 / 2 : ℝ) / 0.6931 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_right hkk hd0.le
    have e : (2 * (0.6013 / (2 * q - 1)) ^ (1 / 2 : ℝ) / 0.6931 + 3) * d
        = 2 / 0.6931 * ((0.6013 / (2 * q - 1)) ^ (1 / 2 : ℝ) * d) + 3 * d := by ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ 2 / 0.6931)
    have := mul_le_mul_of_nonneg_left hdN (by norm_num : (0 : ℝ) ≤ 3)
    have e2 : 2 / 0.6931 * (0.7755 * Real.exp (1 / 4 * Real.log (2 / 100000000)))
        = 2 * 0.7755 / 0.6931 * Real.exp (1 / 4 * Real.log (2 / 100000000)) := by ring
    linarith
  -- the suppression: `e^{-a'e^X/3} ≤ 72/(a'X⁴)`
  have hX4 : Xh ^ 4 / 24 ≤ Real.exp Xh := by
    have := Real.pow_div_factorial_le_exp Xh hXh0.le 4
    norm_num [Nat.factorial] at this ⊢
    linarith
  have ht : a' * Xh ^ 4 / 72 ≤ a' * (Real.exp Xh / 3) := by
    have := mul_le_mul_of_nonneg_left hX4 ha'0.le
    nlinarith
  have hbig : 1.1e12 ≤ a' * Xh ^ 4 / 72 := by
    have e : a' * Xh ^ 4 / 72 = a' * (0.003 ^ 4 / a ^ 4) / 72 := by
      rw [hXhdef, div_pow]
    rw [e]
    have ha4 : 0 < a ^ 4 := by positivity
    rw [le_div_iff₀ (by norm_num), mul_div_assoc', le_div_iff₀ ha4]
    have ha3 : a ^ 3 ≤ (10000001 / 1000000000000000) ^ 3 := pow_le_pow_left₀ ha0.le hau 3
    have h1 : 998 / 1000 * a * 0.003 ^ 4 ≤ a' * 0.003 ^ 4 :=
      mul_le_mul_of_nonneg_right ha'a (by norm_num)
    have h3 : 1.1e12 * 72 * a ^ 4 ≤ 1.1e12 * 72 * (10000001 / 1000000000000000) ^ 3 * a := by
      have := mul_le_mul_of_nonneg_right ha3 ha0.le
      rw [show a ^ 4 = a ^ 3 * a by ring]
      nlinarith
    have h4 : 1.1e12 * 72 * (10000001 / 1000000000000000 : ℝ) ^ 3 ≤ 998 / 1000 * 0.003 ^ 4 := by
      norm_num
    nlinarith
  have hfar : 1 ≤ a' * (Real.exp Xh / 3) := by linarith
  have hsupp : Real.exp (-(a' * (Real.exp Xh / 3))) ≤ 1 / 1.1e12 := by
    refine le_trans (exp_neg_le_inv (by linarith)) ?_
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- the power `δ^{-(3/4)δ}`
  have hdd : (2 * q - 1) ^ (-(3 / 4 * (2 * q - 1)))
      ≤ Real.exp (3 / 2 * Real.exp (1 / 2 * Real.log (2 / 100000000))) := by
    rw [Real.rpow_def_of_pos hδ]
    refine Real.exp_le_exp.2 ?_
    have h1 : -Real.log (2 * q - 1) ≤ 2 * (2 * q - 1) ^ (-(1 / 2 : ℝ)) := by
      have := log_le_two_rpow (inv_nonneg.2 hδ.le)
      rw [Real.log_inv, Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le] at this
      exact this
    have h2 : (2 * q - 1) * (2 * q - 1) ^ (-(1 / 2 : ℝ)) = (2 * q - 1) ^ (1 / 2 : ℝ) := by
      calc (2 * q - 1) * (2 * q - 1) ^ (-(1 / 2 : ℝ))
          = (2 * q - 1) ^ (1 : ℝ) * (2 * q - 1) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = (2 * q - 1) ^ ((1 : ℝ) + -(1 / 2)) := by rw [Real.rpow_add hδ]
        _ = (2 * q - 1) ^ (1 / 2 : ℝ) := by norm_num
    have h3 : (2 * q - 1) ^ (1 / 2 : ℝ) ≤ Real.exp (1 / 2 * Real.log (2 / 100000000)) := by
      rw [Real.rpow_def_of_pos hδ, mul_comm]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log hδ hδ1)
        (by norm_num))
    have h4 := mul_le_mul_of_nonneg_left h1 hδ.le
    rw [show (2 * q - 1) * (2 * (2 * q - 1) ^ (-(1 / 2 : ℝ)))
      = 2 * ((2 * q - 1) * (2 * q - 1) ^ (-(1 / 2 : ℝ))) by ring, h2] at h4
    nlinarith
  -- the cell's numerals
  refine chaos_cell_core hX (ql := 1 / 2) (qu := 50000001 / 100000000) (L0 := 10000)
    (n₀ := ⌈Real.log (3 * Xh)⌉₊) (k := k) (Nc := 8973 / 20000) (Ntop := 133157 / 25000)
    (NCb := 293993 / 50000) (NBot := 32167 / 1250) (NK := 26859 / 20000) (N12 := 100031 / 100000)
    (Nd := 16823 / 10000000000) (Nql := 16823 / 10000) (NX := 6739 / 312500)
    (M1 := 337739 / 100000000) (M3 := 331791 / 50000000) (Nk := 33281 / 1250000)
    (Nsupp := 1 / 1000000000000) (Ndd := 25013 / 25000) (NW := 3379 / 200)
    (Ntl := 464407 / 5000000000) (NP := 336561 / 5000000000000000000)
    le_rfl hq0 hq0.le hqu (by norm_num) hx3 hδΛ (by norm_num) (by norm_num) hXh5 hn₀ hfar hk ?_ ?_
    (le_trans hsupp (by norm_num)) ?_ ?_
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold cenHat; interval_decide (trust := kernel))
    (by unfold topHat; interval_decide (trust := kernel))
    (by unfold bandConstHat pfC2Hat pfC1Hat; interval_decide (trust := kernel))
    (by unfold botHat pfC1Hat; interval_decide (trust := kernel))
    (by unfold pfC1Hat windowWHat; interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by norm_num) (by interval_decide (trust := kernel)) (by norm_num) (by norm_num)
    (by interval_decide (trust := kernel))
  · refine le_trans (mul_le_mul (min_le_right _ _) (le_trans hdN (show Real.exp (3 / 4
      * Real.log (2 * (50000001 / 100000000) - 1)) ≤ 16823 / 10000000000 by
        interval_decide (trust := kernel))) hd0.le (by norm_num)) (by norm_num)
  · exact le_trans hn0d (by interval_decide (trust := kernel))
  · exact le_trans hkd (by interval_decide (trust := kernel))
  · exact le_trans hdd (by interval_decide (trust := kernel))

end RMF
