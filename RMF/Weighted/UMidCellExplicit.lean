/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UJensenCellExplicit
import RMF.Weighted.MidNumeralExplicit

/-!
# The first moment below `q = ½`: one cell of the middle range

For `7 ≤ Λ = log log x ≤ 110` and `q` in a cell, `RMF.u_cell_mid` reduces
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` to numerals on the middle range's assembly
(`y ≈ x^{1/Λ}`, `C_R ≤ 0.5776`, tail and error `≤ 1`): every window by Jensen
(`RMF.uMeso_mid_le`), and the small pieces and the central window through `w = (1 - 2q)Λ`
(`RMF.uSmall_mid_le`, `C_c(q) ≤ 101.02Λ + 20.4`), with any bound `D` on `(1 + w)e^{-q_l w}` past
`w_l`, since `w` can lie below `1/q - 1` here.  The cells' numerals are in
`RMF/Weighted/UCellsMid*Explicit.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The middle range's pieces at exponent `q` -/

/-- `log log y ≥ Λ - log Λ - 1/100` in the middle range: `log y ≥ a - log 2 ≥ a e^{-1/100}`,
`a = log x/Λ ≥ 145`. -/
lemma midY_loglog_ge_sub {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    Real.log (Real.log x) - Real.log (Real.log (Real.log x)) - 1 / 100
      ≤ Real.log (Real.log (midY x)) := by
  obtain ⟨-, hL, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  have ha145 : 145 ≤ midA x := by linarith
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have he : Real.exp (-(1 / 100)) ≤ 100 / 101 := by
    have h1 := Real.add_one_le_exp (1 / 100 : ℝ)
    have h2 : Real.exp (-(1 / 100)) * Real.exp (1 / 100) = 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 : 0 < Real.exp (-(1 / 100)) := Real.exp_pos _
    nlinarith
  have h1 : midA x * Real.exp (-(1 / 100)) ≤ Real.log (midY x) := by
    have : midA x * Real.exp (-(1 / 100)) ≤ midA x * (100 / 101) :=
      mul_le_mul_of_nonneg_left he (by linarith)
    linarith
  have hpos : 0 < midA x * Real.exp (-(1 / 100)) := mul_pos (by linarith) (Real.exp_pos _)
  have h2 := Real.log_le_log hpos h1
  rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, midA,
    Real.log_div hLpos.ne' hΛ0.ne'] at h2
  linarith

/-- The middle range's window count: `5 ≤ J₀ ≤ Λ + 1`. -/
lemma midJ_bounds {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    5 ≤ midJ x ∧ (midJ x : ℝ) ≤ Real.log (Real.log x) + 1 := by
  obtain ⟨-, hL, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, hlogy_le, hlogy_ge, -, -⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have h23 : 0 < 2 / 3 * Real.log (midY x) := by positivity
  have h4 : 4 ≤ Real.log (2 / 3 * Real.log (midY x)) := by
    rw [Real.le_log_iff_exp_le h23]
    have : Real.exp 4 ≤ 55 := by interval_decide (trust := kernel)
    linarith
  constructor
  · have h := Nat.lt_floor_add_one (Real.log (2 / 3 * Real.log (midY x)))
    have h5 : (4 : ℝ) < (midJ x : ℝ) := by rw [midJ]; push_cast; linarith
    have : 4 < midJ x := by exact_mod_cast h5
    omega
  · have h0 : (0 : ℝ) ≤ Real.log (2 / 3 * Real.log (midY x)) := le_trans (by norm_num) h4
    have hfl := Nat.floor_le h0
    have hla : Real.log (2 / 3 * Real.log (midY x)) ≤ Real.log (midA x) :=
      Real.log_le_log h23 (by linarith)
    have hlog_a : Real.log (midA x)
        = Real.log (Real.log x) - Real.log (Real.log (Real.log x)) := by
      rw [midA, Real.log_div hLpos.ne' hΛ0.ne']
    have hll0 : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg (by linarith)
    rw [midJ]
    push_cast
    linarith

/-- `σ log y ≤ 1/(32Λ)` in the middle range (`log y ≤ log x/Λ`). -/
lemma halfSigma_mul_log_midY_le {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) :
    halfSigma x * Real.log (midY x) ≤ 1 / (32 * Real.log (Real.log x)) := by
  obtain ⟨-, hL, hΛ, -, -, -⟩ := mid_params hx
  obtain ⟨-, -, hlogy_le, -, -, -⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  have hσ0 : 0 ≤ halfSigma x := by rw [halfSigma]; positivity
  calc halfSigma x * Real.log (midY x) ≤ halfSigma x * midA x :=
        mul_le_mul_of_nonneg_left hlogy_le hσ0
    _ = 1 / (32 * Real.log (Real.log x)) := by
        rw [halfSigma, midA]
        field_simp

/-- `σ ≤ 1/30000` in the middle range (`log x ≥ e⁷`). -/
lemma halfSigma_le_mid {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) : halfSigma x ≤ 1 / 30000 := by
  obtain ⟨-, hL, -, -, -, -⟩ := mid_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have h7 : (1000 : ℝ) ≤ Real.exp 7 := by interval_decide (trust := kernel)
  rw [halfSigma, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma log_four_le_mid : Real.log 4 ≤ 14 / 10 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

/-- **The window's (PF) bracket is negative in the middle range**: for `k ≥ 4` with
`(3/2)e^k ≤ log y`. -/
lemma thetaPF_bracket_mid {x : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) {k : ℕ} (hk : 4 ≤ k)
    (hky : 3 / 2 * Real.exp k ≤ Real.log (midY x)) :
    9.0028 / (3 / 2 * Real.exp k)
      + 2 * halfSigma x * (3 / 2 * Real.exp k + 1 / 100 + Real.log 4 + 4) ≤ 3 / 20 := by
  obtain ⟨-, hL, hΛ, -, -, -⟩ := mid_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ0 : 0 ≤ halfSigma x := by rw [halfSigma]; positivity
  have hσy := halfSigma_mul_log_midY_le hx
  have hσ1 := halfSigma_le_mid hx
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have he4 : (54 : ℝ) ≤ Real.exp k := by
    have h : Real.exp 4 ≤ Real.exp k := Real.exp_le_exp.2 hkR
    have h4 : (54 : ℝ) ≤ Real.exp 4 := by interval_decide (trust := kernel)
    linarith
  have h1 : 9.0028 / (3 / 2 * Real.exp k) ≤ 9.0028 / 81 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hl4 := log_four_le_mid
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h16 : 1 / (32 * Real.log (Real.log x)) ≤ 1 / 224 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : 2 * halfSigma x * (3 / 2 * Real.exp k) ≤ 2 / 224 := by
    have := mul_le_mul_of_nonneg_left hky hσ0
    linarith
  have h3 : 2 * halfSigma x * (1 / 100 + Real.log 4 + 4)
      ≤ 2 * (1 / 30000) * (1 / 100 + 14 / 10 + 4) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have e : 2 * halfSigma x * (3 / 2 * Real.exp k + 1 / 100 + Real.log 4 + 4)
      = 2 * halfSigma x * (3 / 2 * Real.exp k) + 2 * halfSigma x * (1 / 100 + Real.log 4 + 4) := by
    ring
  rw [e]
  linarith

/-- (PF) at `y` below `(log y)^{-a}` in the middle range. -/
lemma uPFyAt_mid_le {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    uPFyAt q (midY x) ≤ Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (midY x)))) := by
  unfold uPFyAt
  obtain ⟨-, -, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := midY_facts hx
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have hlogy0 : 0 < Real.log (midY x) := by linarith
  have ha0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have h1 : Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log (midY x) - 3 / 20)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ha0 ?_)
    have : 9.0028 / Real.log (midY x) ≤ 9.0028 / 144 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
    linarith
  have h2 : Real.log (midY x) ^ (q * (2 * q - 1))
      = Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (midY x)))) := by
    rw [rpow_eq_exp_mul_log hlogy0]
    congr 1
    ring
  rw [h2]
  calc _ ≤ 1 * Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (midY x)))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := one_mul _

/-- (PF) at the central window below `(log y)^{-a}` in the middle range. -/
lemma uPFcAt_mid_le {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    uPFcAt q (halfSigma x) (midY x)
      ≤ Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (midY x)))) := by
  unfold uPFcAt
  obtain ⟨-, hL, hΛ, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := midY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have hlogy0 : 0 < Real.log (midY x) := by linarith
  have ha0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have hσ0 : 0 ≤ halfSigma x := by rw [halfSigma]; positivity
  have hσy := halfSigma_mul_log_midY_le hx
  have hσ1 := halfSigma_le_mid hx
  have hl4 := log_four_le_mid
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h16 : 1 / (32 * Real.log (Real.log x)) ≤ 1 / 224 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1 : Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log (midY x)
      + 2 * halfSigma x * (Real.log (midY x) + Real.log 4 + 4) - 3 / 20)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ha0 ?_)
    have t1 : 9.0028 / Real.log (midY x) ≤ 9.0028 / 144 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
    have h3 : 2 * halfSigma x * (Real.log 4 + 4) ≤ 2 * (1 / 30000) * (14 / 10 + 4) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have e : 2 * halfSigma x * (Real.log (midY x) + Real.log 4 + 4)
        = 2 * (halfSigma x * Real.log (midY x)) + 2 * halfSigma x * (Real.log 4 + 4) := by ring
    rw [e]
    linarith
  have h2 : Real.log (midY x) ^ (q * (2 * q - 1))
      = Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (midY x)))) := by
    rw [rpow_eq_exp_mul_log hlogy0]
    congr 1
    ring
  rw [h2]
  calc _ ≤ 1 * Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (midY x)))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := one_mul _

/-- **The middle range's central window at exponent `q`**: `C_c(q) ≤ 101.02Λ + 20.4`
(`RMF.midCen_le` with the exponent `2(1-q)S₂w² ≤ 2S₂w²`: `(4/3)(e^{2.79} - 1) ≤ 20.4`). -/
lemma uCenAt_mid_le {x q : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hq0 : 0 ≤ q) :
    uCenAt q (halfSigma x) (midY x) (midJ x)
      ≤ 10102 / 100 * Real.log (Real.log x) + 2040 / 100 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha, -⟩ := mid_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := midY_facts hx
  have hA := midA_mul hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  have hlypos : 0 < Real.log (midY x) := by linarith
  unfold uCenAt
  rw [add_div]
  -- the first part, as in `RMF.midCen_le`
  have hp1 : Real.pi / halfSigma x / Real.log (midY x)
      ≤ 10102 / 100 * Real.log (Real.log x) := by
    have e1 : Real.pi / halfSigma x = 32 * Real.pi * Real.log x := by
      rw [halfSigma]
      field_simp
    rw [e1, div_le_iff₀ hlypos]
    have hpi := Real.pi_lt_d6
    have h1 := mul_le_mul_of_nonneg_left hlogy_ge hΛpos.le
    have e2 : Real.log (Real.log x) * (midA x - Real.log 2)
        = Real.log x - Real.log (Real.log x) * Real.log 2 := by
      calc Real.log (Real.log x) * (midA x - Real.log 2)
          = midA x * Real.log (Real.log x) - Real.log (Real.log x) * Real.log 2 := by ring
        _ = Real.log x - Real.log (Real.log x) * Real.log 2 := by rw [hA]
    rw [e2] at h1
    have hLΛ : 145 * Real.log (Real.log x) ≤ Real.log x := by
      calc 145 * Real.log (Real.log x) ≤ midA x * Real.log (Real.log x) :=
            mul_le_mul_of_nonneg_right (by linarith) hΛpos.le
        _ = Real.log x := hA
    have hl2Λ : Real.log (Real.log x) * Real.log 2 ≤ Real.log (Real.log x) * (6932 / 10000) :=
      mul_le_mul_of_nonneg_left hl2 hΛpos.le
    nlinarith
  -- the second part, with `2(1 - q) ≤ 2`
  have hwly : Real.exp (-((midJ x : ℕ) : ℝ)) * Real.log (midY x) ≤ 3 / 2 := by
    have h23 : 0 < 2 / 3 * Real.log (midY x) := by positivity
    have hJ : Real.log (2 / 3 * Real.log (midY x)) ≤ ((midJ x : ℕ) : ℝ) := by
      rw [midJ]
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc Real.exp (-((midJ x : ℕ) : ℝ)) * Real.log (midY x)
        ≤ Real.exp (-Real.log (2 / 3 * Real.log (midY x))) * Real.log (midY x) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hlypos.le
      _ = 3 / 2 := by
          rw [Real.exp_neg, Real.exp_log h23]
          field_simp
  have hS : Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34
      ≤ 62 / 100 * Real.log (midY x) ^ 2 := by
    have hy0 : (0 : ℝ) < (midY x : ℝ) := by
      have : (2 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast hy2
      linarith
    have h1 : Real.log ((midY x : ℝ) + 1) ≤ Real.log (midY x) + 1 := by
      have h2 : Real.log ((midY x : ℝ) + 1) ≤ Real.log (2 * (midY x : ℝ)) :=
        Real.log_le_log (by positivity) (by
          have : (1 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast (by omega : 1 ≤ midY x)
          linarith)
      rw [Real.log_mul (by norm_num) hy0.ne'] at h2
      linarith
    have h0 : 0 ≤ Real.log ((midY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (midY x : ℝ) := hy0.le
      linarith)
    have h3 : Real.log ((midY x : ℝ) + 1) ^ 2 ≤ (Real.log (midY x) + 1) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    nlinarith
  set w := Real.exp (-((midJ x : ℕ) : ℝ)) with hwdef
  set ly := Real.log (midY x) with hlydef
  set S₂ := Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34
    with hS₂def
  have hw0 : 0 < w := Real.exp_pos _
  have hS0 : 0 ≤ S₂ := by
    rw [hS₂def]
    have h0 : 0 ≤ Real.log ((midY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (midY x : ℝ) := Nat.cast_nonneg _
      linarith)
    positivity
  have hκ : 2 * (9 / 4 * (S₂ / ly ^ 2)) ≤ 279 / 100 := by
    have : S₂ / ly ^ 2 ≤ 62 / 100 := by
      rw [div_le_iff₀ (by positivity)]
      exact hS
    linarith
  have hwl0 : 0 ≤ w * ly := by positivity
  have hs0 : 0 ≤ (w * ly) ^ 2 / (9 / 4) := by positivity
  have hs1 : (w * ly) ^ 2 / (9 / 4) ≤ 1 := by
    rw [div_le_one (by norm_num)]
    have := pow_le_pow_left₀ hwl0 hwly 2
    linarith [show ((3 : ℝ) / 2) ^ 2 = 9 / 4 by norm_num]
  have hconv := exp_mul_le_one_add_mul (x := 2 * (9 / 4 * (S₂ / ly ^ 2))) hs0 hs1
  have hexp1 : 2 * S₂ * w ^ 2 = (w * ly) ^ 2 / (9 / 4) * (2 * (9 / 4 * (S₂ / ly ^ 2))) := by
    field_simp
  have hek : Real.exp (2 * (9 / 4 * (S₂ / ly ^ 2))) - 1 ≤ 1529 / 100 := by
    have : Real.exp (279 / 100) ≤ 1629 / 100 := by interval_decide (trust := kernel)
    linarith [Real.exp_le_exp.2 hκ]
  have hmono : Real.exp (2 * (1 - q) * S₂ * w ^ 2) ≤ Real.exp (2 * S₂ * w ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ S₂ * w ^ 2 := by positivity
    nlinarith
  have hp2 : 2 * (Real.exp (2 * (1 - q) * S₂ * w ^ 2) - 1) / w / ly ≤ 2040 / 100 := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have h1 : Real.exp (2 * S₂ * w ^ 2) - 1
        ≤ (w * ly) ^ 2 / (9 / 4) * (Real.exp (2 * (9 / 4 * (S₂ / ly ^ 2))) - 1) := by
      rw [hexp1]; linarith
    have h2 : (w * ly) ^ 2 / (9 / 4) * (Real.exp (2 * (9 / 4 * (S₂ / ly ^ 2))) - 1)
        ≤ (w * ly) * (3 / 2) / (9 / 4) * (1529 / 100) := by
      have hsq : (w * ly) ^ 2 ≤ (w * ly) * (3 / 2) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_left hwly hwl0
      calc (w * ly) ^ 2 / (9 / 4) * (Real.exp (2 * (9 / 4 * (S₂ / ly ^ 2))) - 1)
          ≤ (w * ly) ^ 2 / (9 / 4) * (1529 / 100) :=
            mul_le_mul_of_nonneg_left hek hs0
        _ ≤ (w * ly) * (3 / 2) / (9 / 4) * (1529 / 100) := by
            have := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 9 / 4)
            linarith
    linarith
  linarith

/-- **`(1 + w)e^{-cw}` at most its maximum `e^{c-1}/c`** (`t ≤ e^{t-1}` at `t = c(1 + w)`). -/
lemma one_add_mul_exp_neg_le_max {c w : ℝ} (hc : 0 < c) :
    (1 + w) * Real.exp (-(c * w)) ≤ 1 / c * Real.exp (c - 1) := by
  rw [show 1 / c * Real.exp (c - 1) = Real.exp (c - 1) / c by ring, le_div_iff₀ hc]
  have e : c * (1 + w) * Real.exp (-(c * (1 + w))) * Real.exp c
      = (1 + w) * Real.exp (-(c * w)) * c := by
    rw [mul_assoc (c * (1 + w)), ← Real.exp_add, show -(c * (1 + w)) + c = -(c * w) by ring]
    ring
  rw [← e]
  have h3 : c * (1 + w) ≤ Real.exp (c * (1 + w) - 1) := by
    linarith [Real.add_one_le_exp (c * (1 + w) - 1)]
  have h2 : c * (1 + w) * Real.exp (-(c * (1 + w))) ≤ Real.exp (-1) := by
    calc c * (1 + w) * Real.exp (-(c * (1 + w)))
        ≤ Real.exp (c * (1 + w) - 1) * Real.exp (-(c * (1 + w))) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (-1) := by
          rw [← Real.exp_add, show c * (1 + w) - 1 + -(c * (1 + w)) = -1 by ring]
  calc c * (1 + w) * Real.exp (-(c * (1 + w))) * Real.exp c ≤ Real.exp (-1) * Real.exp c :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (c - 1) := by rw [← Real.exp_add, show -1 + c = c - 1 by ring]

/-- **(PF) against `τ⁻¹` through `w`, with any bound `D` on `(1 + w)e^{-q_l w}` past `w_l`**
(`RMF.pf_tau_le` without `w_l ≥ 1/q_l - 1`). -/
lemma pf_tau_le_D {Λ q ql qu Λl wl a₁ c D : ℝ} (hΛl1 : 1 ≤ Λl) (hΛl : Λl ≤ Λ) (hql0 : 0 < ql)
    (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2) (ha₁ : q * (1 - 2 * q) ≤ a₁)
    (hc : 0 ≤ c) (hexp : a₁ + (c + 1 / 2) * qu - 1 ≤ 0) (hwl : wl ≤ (1 - 2 * q) * Λ)
    (hD : ∀ w : ℝ, wl ≤ w → (1 + w) * Real.exp (-(ql * w)) ≤ D) :
    Real.exp (-(q * (1 - 2 * q) * (Λ - Real.log Λ))) * Λ ^ (c * q)
        * ((Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2))
      ≤ D * Λl ^ (a₁ + (c + 1 / 2) * qu - 1) := by
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := by linarith
  set w := (1 - 2 * q) * Λ with hw
  have hw0 : 0 ≤ w := mul_nonneg (by linarith) hΛ0.le
  have e1 : Real.exp (-(q * (1 - 2 * q) * (Λ - Real.log Λ)))
      = Real.exp (-(q * w)) * Λ ^ (q * (1 - 2 * q)) := by
    rw [rpow_eq_exp_mul_log hΛ0, ← Real.exp_add, hw]
    congr 1
    ring
  have e2 : (Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2) = (1 + w) * Λ ^ (q / 2 - 1) := by
    rw [Real.rpow_sub_one hΛ0.ne', hw]
    field_simp
  have e3 : Λ ^ (q * (1 - 2 * q)) * Λ ^ (c * q) * Λ ^ (q / 2 - 1)
      = Λ ^ (q * (1 - 2 * q) + (c + 1 / 2) * q - 1) := by
    rw [← Real.rpow_add hΛ0, ← Real.rpow_add hΛ0]
    congr 1
    ring
  have hmain : Real.exp (-(q * (1 - 2 * q) * (Λ - Real.log Λ))) * Λ ^ (c * q)
        * ((Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2))
      = ((1 + w) * Real.exp (-(q * w))) * Λ ^ (q * (1 - 2 * q) + (c + 1 / 2) * q - 1) := by
    rw [e1, e2, ← e3]
    ring
  rw [hmain]
  have f1 : (1 + w) * Real.exp (-(q * w)) ≤ D :=
    le_trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hqlq hw0))) (by linarith))
      (hD w hwl)
  have hD0 : 0 ≤ D := le_trans (mul_nonneg (by linarith) (Real.exp_pos _).le) f1
  have f2 : Λ ^ (q * (1 - 2 * q) + (c + 1 / 2) * q - 1) ≤ Λl ^ (a₁ + (c + 1 / 2) * qu - 1) := by
    have hle : q * (1 - 2 * q) + (c + 1 / 2) * q - 1 ≤ a₁ + (c + 1 / 2) * qu - 1 := by
      have := mul_le_mul_of_nonneg_left hqqu (by linarith : (0 : ℝ) ≤ c + 1 / 2)
      linarith
    calc Λ ^ (q * (1 - 2 * q) + (c + 1 / 2) * q - 1) ≤ Λ ^ (a₁ + (c + 1 / 2) * qu - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hle
      _ ≤ Λl ^ (a₁ + (c + 1 / 2) * qu - 1) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hΛl hexp
  exact mul_le_mul f1 f2 (Real.rpow_nonneg hΛ0.le _) hD0

/-- **A window's constant at `log y ≥ L_y` from rational bounds**
(`RMF.thetaWindowConstQ_rpow_le_of` at the threshold `L_y`). -/
lemma thetaWindowConstQ_rpow_le_of_log {ql qu ε b c Gb Ly : ℝ} (hLy : 0 < Ly) (hql1 : ql ≤ 1)
    (hqu : 0 ≤ qu) (k : ℕ) (hε : Real.exp (-(k : ℝ)) ≤ ε)
    (hb : 2 * (1 - ql) * ((3 / 2 + ε / 100) ^ 2 / 2 + 15.003 * (3 / 2 * ε + ε ^ 2 / 100)
      + 34 * ε ^ 2) ≤ b)
    (hc : 9.0028 / Ly + 9.0028 * ε / (3 / 2) ≤ c)
    (hG : Real.exp (qu * Real.log (4 / 3 * ((Real.exp 1 - 1) + b * (1 - Real.exp (-1))
      + (Real.exp b - 1 - b) * (1 - Real.exp (-3)) * (1 / 3)) * Real.exp c)) ≤ Gb) :
    ∀ y : ℕ, Ly ≤ Real.log y → thetaWindowConstQ (3 / 2) ql k y ^ qu ≤ Gb := by
  intro y hy
  have hw : thetaWindowExp (3 / 2) k
      ≤ (3 / 2 + ε / 100) ^ 2 / 2 + 15.003 * (3 / 2 * ε + ε ^ 2 / 100) + 34 * ε ^ 2 := by
    unfold thetaWindowExp
    gcongr
  have hb0 : 0 ≤ 2 * (1 - ql) * thetaWindowExp (3 / 2) k :=
    mul_nonneg (by linarith) (thetaWindowExp_nonneg (by norm_num) k)
  have hbb : 2 * (1 - ql) * thetaWindowExp (3 / 2) k ≤ b :=
    le_trans (mul_le_mul_of_nonneg_left hw (by linarith)) hb
  have hW := taylorWindowW_mono hbb
  have hWb0 : 0 ≤ taylorWindowW b := le_trans (taylorWindowW_nonneg hb0) hW
  have e1 : (Real.exp 1)⁻¹ = Real.exp (-1) := (Real.exp_neg 1).symm
  have e3 : (Real.exp 1)⁻¹ ^ 3 = Real.exp (-3) := by
    rw [e1, ← Real.exp_nat_mul]
    norm_num
  have hWb : taylorWindowW b = (Real.exp 1 - 1) + b * (1 - Real.exp (-1))
      + (Real.exp b - 1 - b) * (1 - Real.exp (-3)) * (1 / 3) := by
    unfold taylorWindowW
    rw [e3, e1]
    ring
  have hl : 9.0028 / Real.log y ≤ 9.0028 / Ly :=
    div_le_div_of_nonneg_left (by norm_num) hLy hy
  have hk : 9.0028 * Real.exp (-(k : ℝ)) / (3 / 2) ≤ 9.0028 * ε / (3 / 2) := by gcongr
  have h1 : thetaWindowConstQ (3 / 2) ql k y ≤ 4 / 3 * taylorWindowW b * Real.exp c := by
    unfold thetaWindowConstQ
    rw [show (2 : ℝ) / (3 / 2) = 4 / 3 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hW (by norm_num))
      (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg (by norm_num) hWb0)
  have h0 : 0 ≤ thetaWindowConstQ (3 / 2) ql k y := thetaWindowConstQ_nonneg (by norm_num) hql1 k y
  refine le_trans (Real.rpow_le_rpow h0 h1 hqu) (le_trans (rpow_le_exp_mul_log
    (mul_nonneg (mul_nonneg (by norm_num) hWb0) (Real.exp_pos _).le) qu) ?_)
  rw [hWb]
  exact hG

/-- **A window of the middle range by Jensen**: `b_k ≤ e^{-q(1-2q)k}·((3/2)^{-q(1-2q)}G)` for
`k₁ ≤ k < J₀` and `G_{k₁}(a)^b ≤ G`. -/
lemma midWindow_le {x q a b G : ℝ} (hx : Real.exp (Real.exp 7) ≤ x) (hq0 : 0 ≤ q) (haq : a ≤ q)
    (hqb : q ≤ b) (hb : b ≤ 1 / 2) {k k₁ : ℕ} (hk₁ : k₁ ≤ k) (hk : k ∈ Finset.Ico 4 (midJ x))
    (hG : thetaWindowConstQ (3 / 2) a k₁ (midY x) ^ b ≤ G) :
    thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (midY x) ^ q
      ≤ Real.exp (-(q * (1 - 2 * q) * k)) * ((3 / 2) ^ (-(q * (1 - 2 * q))) * G) := by
  obtain ⟨hy2, -, -, -, -, -⟩ := midY_facts hx
  have hy2R : (2 : ℝ) ≤ (midY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (midY x) := Real.log_pos (by linarith)
  rw [Finset.mem_Ico] at hk
  have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [midJ] at hk; exact hk.2)
  have hPF := thetaPF_le (σ := halfSigma x) (θ := 3 / 2) (by norm_num) hq0 (by linarith) (k := k)
    (thetaPF_bracket_mid hx hk.1 hky)
  have hG1 : 1 ≤ thetaWindowConstQ (3 / 2) q k (midY x) :=
    one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) k (midY x)
  have hGq : thetaWindowConstQ (3 / 2) q k (midY x) ^ q ≤ G := by
    have h1 : thetaWindowConstQ (3 / 2) q k (midY x) ≤ thetaWindowConstQ (3 / 2) a k₁ (midY x) :=
      le_trans (thetaWindowConstQ_anti_q (by norm_num) haq k (midY x))
        (thetaWindowConstQ_anti_k (by norm_num) (by linarith) hk₁ (midY x))
    have h2 : 1 ≤ thetaWindowConstQ (3 / 2) a k₁ (midY x) := le_trans hG1 h1
    calc thetaWindowConstQ (3 / 2) q k (midY x) ^ q
        ≤ thetaWindowConstQ (3 / 2) a k₁ (midY x) ^ q :=
          Real.rpow_le_rpow (by linarith) h1 hq0
      _ ≤ thetaWindowConstQ (3 / 2) a k₁ (midY x) ^ b := Real.rpow_le_rpow_of_exponent_le h2 hqb
      _ ≤ G := hG
  have hGq0 : 0 ≤ thetaWindowConstQ (3 / 2) q k (midY x) ^ q := Real.rpow_nonneg (by linarith) _
  calc thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (midY x) ^ q
      ≤ (3 / 2) ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k)) * G :=
        mul_le_mul hPF hGq hGq0 (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- four groups, each by the same lemma
/-- **The middle range's windows, summed**: every window by Jensen in the groups
`{4}, {5}, {6}, [7, J₀)` (the windows past `J₀` counted as zero when `J₀ < 7`), keeping the
sum's upper end through `aJ₀ ≤ q_u w_u + a₁`. -/
theorem uMeso_mid_le {x q ql qu wu : ℝ} (hx : Real.exp (Real.exp 7) ≤ x)
    (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2)
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ wu) {G₁ G₂ G₃ G₄ : ℝ}
    (hG₁ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 4 y ^ qu ≤ G₁)
    (hG₂ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 5 y ^ qu ≤ G₂)
    (hG₃ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 6 y ^ qu ≤ G₃)
    (hG₄ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 7 y ^ qu ≤ G₄)
    (h12 : G₂ ≤ G₁) (h23 : G₃ ≤ G₂) (h34 : G₄ ≤ G₃) :
    (1 - Real.exp (-(q * (1 - 2 * q))))
        * ∑ k ∈ Finset.Ico 4 (midJ x),
          thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (midY x) ^ q
      ≤ (3 / 2) ^ (-(q * (1 - 2 * q)))
        * (G₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
          - (G₁ - G₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
          - (G₂ - G₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
          - (G₃ - G₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
          - G₄ * Real.exp (-(qu * wu + ql * (1 - 2 * ql)))) := by
  obtain ⟨-, -, hΛ7, -, ha, -⟩ := mid_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := midY_facts hx
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hly : 144 ≤ Real.log (midY x) := by linarith
  obtain ⟨hJ5, hJΛ⟩ := midJ_bounds hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hq0 : 0 < q := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 < a := mul_pos hq0 hv0
  have ha₀ : qu * (1 - 2 * qu) ≤ a := mul_one_sub_two_mul_anti (by linarith) hqqu
  have ha₁ : a ≤ ql * (1 - 2 * ql) := mul_one_sub_two_mul_anti (by linarith) hqlq
  have hG₄0 : 0 ≤ G₄ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) 7 (midY x))) _)
    (hG₄ _ hly)
  have hTH0 : 0 < (3 / 2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  set J := midJ x with hJdef
  set J' := max J 7 with hJ'def
  have hJJ' : J ≤ J' := le_max_left _ _
  have hJ'7 : 7 ≤ J' := le_max_right _ _
  have hJ'Λ : (J' : ℝ) ≤ Λ + 1 := by
    rw [hJ'def]
    rcases le_total J 7 with h | h
    · rw [max_eq_right h]; push_cast; linarith
    · rw [max_eq_left h]; exact hJΛ
  have hT : a * (J' : ℝ) ≤ qu * wu + ql * (1 - 2 * ql) := by
    have h1 : a * (J' : ℝ) ≤ a * (Λ + 1) := mul_le_mul_of_nonneg_left hJ'Λ ha0.le
    have h2 : a * Λ ≤ qu * wu := by
      rw [hadef, mul_assoc]
      exact mul_le_mul hqqu hwu (mul_nonneg hv0.le (by linarith)) (by linarith)
    linarith
  -- the windows, extended by zero past `J₀`
  set wb : ℕ → ℝ := fun k =>
    thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (midY x) ^ q with hwbdef
  set w' : ℕ → ℝ := fun k => if k < J then wb k else 0 with hw'def
  have hsum : ∑ k ∈ Finset.Ico 4 J, wb k = ∑ k ∈ Finset.Ico 4 J', w' k := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : 4 ≤ J) hJJ']
    have h0 : ∑ k ∈ Finset.Ico J J', w' k = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [hw'def]
        simp only
        rw [if_neg (by have := (Finset.mem_Ico.1 hk).1; omega)]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun k hk => by
      rw [hw'def]
      simp only
      rw [if_pos (Finset.mem_Ico.1 hk).2]
  have hw : ∀ (k₁ : ℕ) (G : ℝ),
      (∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql k₁ y ^ qu ≤ G) → 0 ≤ G →
      ∀ k, 4 ≤ k → k₁ ≤ k → w' k ≤ Real.exp (-(a * k)) * ((3 / 2) ^ (-a) * G) := by
    intro k₁ G hG hG0 k hk4 hk₁
    rw [hw'def]
    simp only
    split_ifs with hkJ
    · exact midWindow_le hx hq0.le hqlq hqqu (by linarith) hk₁
        (Finset.mem_Ico.2 ⟨hk4, hkJ⟩) (hG _ hly)
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hTH0.le hG0)
  have hG₃0 : 0 ≤ G₃ := le_trans hG₄0 h34
  have hG₂0 : 0 ≤ G₂ := le_trans hG₃0 h23
  have hG₁0 : 0 ≤ G₁ := le_trans hG₂0 h12
  have h := sum_four_groups_le_top (w := w') ha0 ha₀ ha₁ hJ'7 hT
    (c₁ := (3 / 2) ^ (-a) * G₁) (c₂ := (3 / 2) ^ (-a) * G₂) (c₃ := (3 / 2) ^ (-a) * G₃)
    (c₄ := (3 / 2) ^ (-a) * G₄)
    (mul_le_mul_of_nonneg_left h12 hTH0.le) (mul_le_mul_of_nonneg_left h23 hTH0.le)
    (mul_le_mul_of_nonneg_left h34 hTH0.le) (mul_nonneg hTH0.le hG₄0)
    (fun k hk => hw 4 G₁ hG₁ hG₁0 k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).1)
    (fun k hk => hw 5 G₂ hG₂ hG₂0 k (by have := (Finset.mem_Ico.1 hk).1; omega)
      (Finset.mem_Ico.1 hk).1)
    (fun k hk => hw 6 G₃ hG₃ hG₃0 k (by have := (Finset.mem_Ico.1 hk).1; omega)
      (Finset.mem_Ico.1 hk).1)
    (fun k hk => hw 7 G₄ hG₄ hG₄0 k (by have := (Finset.mem_Ico.1 hk).1; omega)
      (Finset.mem_Ico.1 hk).1)
  rw [← hsum] at h
  refine le_trans h (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
-- five bounds, each by a named lemma
/-- **The small pieces and the central window in the middle range**: for `Λ ∈ [Λ_l, Λ_u]`,
`Λ_l ≥ 7`, `q ∈ [q_l, q_u] ⊆ [0.41, ½)`, `w = (1 - 2q)Λ ≥ w_l` and `(1 + w)e^{-q_l w} ≤ D` past
`w_l`: (PF) at `y` and the central window (`C_c ≤ 105Λ`) through `w`, with
`log log y ≥ Λ - log Λ - 1/100`, and the smooth tail and the reduction's error `≤ 1` each, are
`≤ τ·(De^{a₁/100}(Λ_l^{a₁+q_u/2-1} + C_R'105^{q_u}Λ_l^{a₁+3q_u/2-1})
  + 2(1/Λ_l + 1 - 2q_l)Λ_u^{q_u/2})`, `C_R' = 0.5776^{q_l}`. -/
theorem uSmall_mid_le {x q ql qu Λl Λu wl D : ℝ} (hx : Real.exp (Real.exp 7) ≤ x)
    (hΛl : Λl ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ Λu) (hΛl7 : 7 ≤ Λl)
    (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2)
    (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hD : ∀ w : ℝ, wl ≤ w → (1 + w) * Real.exp (-(ql * w)) ≤ D) :
    uPFyAt q (midY x) + midTail x ^ q
        + smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q * uPFcAt q (halfSigma x) (midY x))
        + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q
      ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ * Real.log (Real.log x) ^ (-(q / 2))
        * (D * Real.exp (ql * (1 - 2 * ql) / 100)
            * (Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl)
              + Real.exp (ql * Real.log (5776 / 10000)) * Real.exp (qu * Real.log 105)
                * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl))
          + 2 * ((1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu))) := by
  obtain ⟨hx0, hL, hΛ7, -, -, -⟩ := mid_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  obtain ⟨hz2, hzy, -⟩ := midZ_facts hx
  obtain ⟨hy2, -, -, hlogy_ge, -, -⟩ := midY_facts hx
  have hll := midY_loglog_ge_sub hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := by linarith
  have hq5 : q ≤ 1 / 2 := by linarith
  have hql0 : 0 < ql := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 ≤ a := mul_nonneg hq0.le (by linarith)
  have ha₁ : a ≤ ql * (1 - 2 * ql) := mul_one_sub_two_mul_anti (by linarith) hqlq
  have ha₁8 : ql * (1 - 2 * ql) ≤ 1 / 8 := by linarith [sq_nonneg (ql - 1 / 4)]
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛ0; linarith
  set R := V * Λ ^ (q / 2) with hRdef
  have hR0 : 0 < R := mul_pos hV0 (Real.rpow_pos_of_pos hΛ0 _)
  have hτ : V⁻¹ * Λ ^ (-(q / 2)) = R⁻¹ := by
    rw [hRdef, mul_inv, Real.rpow_neg hΛ0.le]
  rw [hτ]
  -- the (PF) decay `e^{-a(Λ - log Λ)}e^{a₁/100}`
  set E1 := Real.exp (ql * (1 - 2 * ql) / 100) with hE1
  have hE10 : 0 ≤ E1 := (Real.exp_pos _).le
  have hdec : Real.exp (-(a * Real.log (Real.log (midY x))))
      ≤ Real.exp (-(a * (Λ - Real.log Λ))) * E1 := by
    rw [hE1, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hll ha0
    linarith
  have hPFy := le_trans (uPFyAt_mid_le hx hq0.le hq5) hdec
  have hPFc := le_trans (uPFcAt_mid_le hx hq0.le hq5) hdec
  have hpf0 := pf_tau_le_D (c := 0) (by linarith) hΛl hql0 hqlq hqqu hqu ha₁ le_rfl
    (by linarith) hwl hD
  have hpf1 := pf_tau_le_D (c := 1) (by linarith) hΛl hql0 hqlq hqqu hqu ha₁ zero_le_one
    (by linarith) hwl hD
  rw [zero_mul, Real.rpow_zero, mul_one] at hpf0
  have eΛl0 : Λl ^ (ql * (1 - 2 * ql) + (0 + 1 / 2) * qu - 1)
      = Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl) := by
    rw [rpow_eq_exp_mul_log (by linarith)]; congr 1; ring
  have eΛl1 : Λl ^ (ql * (1 - 2 * ql) + (1 + 1 / 2) * qu - 1)
      = Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl) := by
    rw [rpow_eq_exp_mul_log (by linarith)]; congr 1; ring
  rw [eΛl0] at hpf0
  rw [eΛl1] at hpf1
  -- (PF) at `y`
  have hy : uPFyAt q (midY x) * R
      ≤ E1 * (D * Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl)) := by
    calc uPFyAt q (midY x) * R ≤ Real.exp (-(a * (Λ - Real.log Λ))) * E1 * R :=
          mul_le_mul_of_nonneg_right hPFy hR0.le
      _ = E1 * (Real.exp (-(a * (Λ - Real.log Λ))) * R) := by ring
      _ ≤ E1 * (D * Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl)) :=
          mul_le_mul_of_nonneg_left hpf0 hE10
  -- the central window
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  set CR := smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32) with hCRdef
  have hCR0 : 0 ≤ CR := (smallQReductionConst_pos hz2 hzy hη hε).le
  have hCRq : CR ^ q ≤ Real.exp (ql * Real.log (5776 / 10000)) := by
    calc CR ^ q ≤ (5776 / 10000 : ℝ) ^ q := Real.rpow_le_rpow hCR0 (midCR_le hx) hq0.le
      _ ≤ (5776 / 10000 : ℝ) ^ ql :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hqlq
      _ = Real.exp (ql * Real.log (5776 / 10000)) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  have hl2 : Real.log 2 ≤ 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hlogy : 0 < Real.log (midY x) := by
    obtain ⟨-, -, -, -, ha, -⟩ := mid_params hx
    linarith
  have hC0 : 0 ≤ uCenAt q (halfSigma x) (midY x) (midJ x) := by
    unfold uCenAt
    have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
    have hl : 0 ≤ Real.log ((midY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (midY x : ℝ) := Nat.cast_nonneg _
      linarith)
    have h2 : 0 ≤ Real.exp (2 * (1 - q)
        * (Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34)
        * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2) - 1 := by
      have : 0 ≤ 2 * (1 - q)
          * (Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34)
          * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2 := by
        have : 0 ≤ 1 - q := by linarith
        positivity
      linarith [Real.add_one_le_exp (2 * (1 - q)
        * (Real.log ((midY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((midY x : ℝ) + 1) + 34)
        * Real.exp (-((midJ x : ℕ) : ℝ)) ^ 2)]
    positivity
  have hCen : uCenAt q (halfSigma x) (midY x) (midJ x) ^ q
      ≤ Real.exp (qu * Real.log 105) * Λ ^ (1 * q) := by
    have h1 := uCenAt_mid_le hx hq0.le
    rw [← hΛdef] at h1
    have h105 : uCenAt q (halfSigma x) (midY x) (midJ x) ≤ 105 * Λ := by linarith
    calc uCenAt q (halfSigma x) (midY x) (midJ x) ^ q ≤ (105 * Λ) ^ q :=
          Real.rpow_le_rpow hC0 h105 hq0.le
      _ = (105 : ℝ) ^ q * Λ ^ (1 * q) := by rw [Real.mul_rpow (by norm_num) hΛ0.le, one_mul]
      _ ≤ (105 : ℝ) ^ qu * Λ ^ (1 * q) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hqqu) (Real.rpow_nonneg hΛ0.le _)
      _ = Real.exp (qu * Real.log 105) * Λ ^ (1 * q) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  have hPFc0 : 0 ≤ uPFcAt q (halfSigma x) (midY x) := by
    unfold uPFcAt
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hlogy.le _)
  have hcen : CR ^ q * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q
        * uPFcAt q (halfSigma x) (midY x)) * R
      ≤ D * E1 * (Real.exp (ql * Real.log (5776 / 10000)) * Real.exp (qu * Real.log 105)
        * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl)) := by
    have hCq0 : 0 ≤ uCenAt q (halfSigma x) (midY x) (midJ x) ^ q := Real.rpow_nonneg hC0 q
    have h1 : uCenAt q (halfSigma x) (midY x) (midJ x) ^ q * uPFcAt q (halfSigma x) (midY x)
        ≤ Real.exp (qu * Real.log 105) * Λ ^ (1 * q)
          * (Real.exp (-(a * (Λ - Real.log Λ))) * E1) :=
      mul_le_mul hCen hPFc hPFc0 (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hΛ0.le _))
    have h3 := mul_le_mul_of_nonneg_left hpf1 (Real.exp_pos (qu * Real.log 105)).le
    calc CR ^ q * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q
          * uPFcAt q (halfSigma x) (midY x)) * R
        ≤ Real.exp (ql * Real.log (5776 / 10000))
          * (Real.exp (qu * Real.log 105) * Λ ^ (1 * q)
            * (Real.exp (-(a * (Λ - Real.log Λ))) * E1) * R) := by
          rw [mul_assoc]
          exact mul_le_mul hCRq (mul_le_mul_of_nonneg_right h1 hR0.le)
            (mul_nonneg (mul_nonneg hCq0 hPFc0) hR0.le) (Real.exp_pos _).le
      _ = Real.exp (ql * Real.log (5776 / 10000)) * E1
          * (Real.exp (qu * Real.log 105)
            * (Real.exp (-(a * (Λ - Real.log Λ))) * Λ ^ (1 * q) * R)) := by ring
      _ ≤ Real.exp (ql * Real.log (5776 / 10000)) * E1
          * (Real.exp (qu * Real.log 105)
            * (D * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl))) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (Real.exp_pos _).le hE10)
      _ = _ := by ring
  -- the tail and the error, `≤ 1` each
  have hRu := tauInv_le (by linarith) hΛl hΛu hqlq hqqu (by linarith) hq0.le
  rw [← hVdef, ← hRdef] at hRu
  have hT0 : 0 ≤ midTail x := by
    unfold midTail
    exact Finset.sum_nonneg fun m _ => by positivity
  have hTq : midTail x ^ q ≤ 1 := Real.rpow_le_one hT0 (midTail_le_one hx) hq0.le
  have hE0 : 0 ≤ smallQReductionErr x (midZ x) (halfEta x) (halfEps x) := by
    unfold smallQReductionErr
    have hlogz : 0 < Real.log (midZ x) := Real.log_pos (by
      have : (2 : ℝ) ≤ (midZ x : ℝ) := by exact_mod_cast hz2
      linarith)
    have hL0 : 0 ≤ 1 + Real.log x := by linarith
    positivity
  have hEq : smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q ≤ 1 :=
    Real.rpow_le_one hE0 (midErr_le_one hx) hq0.le
  have hTE : (midTail x ^ q + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q) * R
      ≤ 2 * ((1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu)) := by
    have := mul_le_mul (add_le_add hTq hEq) hRu hR0.le (by norm_num)
    linarith
  -- together
  refine le_inv_mul_of_mul_le hR0 ?_
  have e : (uPFyAt q (midY x) + midTail x ^ q
        + CR ^ q * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q
          * uPFcAt q (halfSigma x) (midY x))
        + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q) * R
      = uPFyAt q (midY x) * R
        + CR ^ q * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q
          * uPFcAt q (halfSigma x) (midY x)) * R
        + (midTail x ^ q + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q) * R := by
    ring
  rw [e]
  linarith [hy, hcen, hTE]

set_option maxHeartbeats 1000000 in
-- the assembly and three bounds, combined linearly
/-- **One cell of the middle range**: for `x ≥ exp(e⁷)` with `Λ = log log x ∈ [Λ_l, Λ_u]`,
`Λ_l ≥ 7`, `q ∈ [q_l, q_u] ⊆ [0.41, ½)`, `w = (1 - 2q)Λ ∈ [w_l, w_u]`, `w_l > 0`, a bound `D` on
`(1 + w)e^{-q_l w}` past `w_l`, window constants `G_k(q_l)^{q_u} ≤ G_g` at `log y ≥ 144`
decreasing, and the certificate `hfin`, `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`: the middle
range's assembly with every window and the far range by Jensen (`RMF.uMeso_mid_le`), and the
small pieces and the central window through `w` (`RMF.uSmall_mid_le`). -/
theorem u_cell_mid {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql qu Λl Λu wl wu D : ℝ} (hx : Real.exp (Real.exp 7) ≤ x)
    (hΛl : Λl ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ Λu) (hΛl7 : 7 ≤ Λl)
    (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2)
    (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl0 : 0 < wl)
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ wu)
    (hD : ∀ w : ℝ, wl ≤ w → (1 + w) * Real.exp (-(ql * w)) ≤ D) {G₁ G₂ G₃ G₄ : ℝ}
    (hG₁ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 4 y ^ qu ≤ G₁)
    (hG₂ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 5 y ^ qu ≤ G₂)
    (hG₃ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 6 y ^ qu ≤ G₃)
    (hG₄ : ∀ y : ℕ, 144 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 7 y ^ qu ≤ G₄)
    (h12 : G₂ ≤ G₁) (h23 : G₃ ≤ G₂) (h34 : G₄ ≤ G₃)
    (hfin : D * Real.exp (ql * (1 - 2 * ql) / 100)
          * (Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl)
            + Real.exp (ql * Real.log (5776 / 10000)) * Real.exp (qu * Real.log 105)
              * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl))
        + 2 * ((1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu))
        + Real.exp (ql * Real.log (5776 / 10000)) * Real.exp (qu * (Real.log (2 * 1.195) + 4))
          * ((1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu))
        + Real.exp (ql * Real.log (5776 / 10000))
          * Real.exp (-(qu * (1 - 2 * qu) * Real.log (3 / 2))) * Real.exp (qu / 2 * Real.log Λu)
          * (1 / ql + 1 / (ql * wl) + (1 / Λl + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10))
          * (G₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
            - (G₁ - G₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
            - (G₂ - G₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
            - (G₃ - G₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
            - G₄ * Real.exp (-(qu * wu + ql * (1 - 2 * ql)))) ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨-, hL, hΛ7, -, -, -⟩ := mid_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  obtain ⟨hz2, hzy, -⟩ := midZ_facts hx
  have hsmall := uSmall_mid_le hx hΛl hΛu hΛl7 hql hqlq hqqu hqu hwl hD
  have hmeso := uMeso_mid_le hx hql hqlq hqqu hqu hwu hG₁ hG₂ hG₃ hG₄ h12 h23 h34
  have hasm := integral_rpow_weightedRademacherSum_le_u_mid_assembly (q := q) hX hx
    (by linarith) (by linarith)
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := by linarith
  have hql0 : 0 < ql := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 < a := mul_pos hq0 hv0
  have ha₀ : qu * (1 - 2 * qu) ≤ a := mul_one_sub_two_mul_anti (by linarith) hqqu
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛ0; linarith
  set R := V * Λ ^ (q / 2) with hRdef
  have hR0 : 0 < R := mul_pos hV0 (Real.rpow_pos_of_pos hΛ0 _)
  have hτ : V⁻¹ * Λ ^ (-(q / 2)) = R⁻¹ := by rw [hRdef, mul_inv, Real.rpow_neg hΛ0.le]
  rw [hτ] at hsmall
  rw [mul_assoc, hτ]
  have hRu := tauInv_le (by linarith) hΛl hΛu hqlq hqqu (by linarith) hq0.le
  rw [← hVdef, ← hRdef] at hRu
  -- the reduction's constant
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  set CR := smallQReductionConst (midY x) (midZ x) (halfEta x) (halfEps x) (1 / 32) with hCRdef
  have hCR0 : 0 ≤ CR := (smallQReductionConst_pos hz2 hzy hη hε).le
  have hCRq : CR ^ q ≤ Real.exp (ql * Real.log (5776 / 10000)) := by
    calc CR ^ q ≤ (5776 / 10000 : ℝ) ^ q := Real.rpow_le_rpow hCR0 (midCR_le hx) hq0.le
      _ ≤ (5776 / 10000 : ℝ) ^ ql :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hqlq
      _ = Real.exp (ql * Real.log (5776 / 10000)) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  set CRn := Real.exp (ql * Real.log (5776 / 10000)) with hCRn
  have hCRq0 : 0 ≤ CR ^ q := Real.rpow_nonneg hCR0 q
  set Ru := (1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu) with hRudef
  -- the far range, by Jensen
  have hB : (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q
      ≤ Real.exp (qu * (Real.log (2 * 1.195) + 4)) := by
    have hB1 : (1 : ℝ) ≤ 2 * 1.195 / Real.exp (-4) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      have : Real.exp (-4) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
      linarith
    have e : (2 * 1.195 : ℝ) / Real.exp (-4) = Real.exp (Real.log (2 * 1.195) + 4) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    rw [Nat.cast_ofNat, show Real.exp (qu * (Real.log (2 * 1.195) + 4))
      = (2 * 1.195 / Real.exp (-4)) ^ qu by rw [e, ← Real.exp_mul, mul_comm]]
    exact Real.rpow_le_rpow_of_exponent_le hB1 hqqu
  have hfar : CR ^ q * (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q
      ≤ R⁻¹ * (CRn * Real.exp (qu * (Real.log (2 * 1.195) + 4)) * Ru) := by
    refine le_inv_mul_of_mul_le hR0 ?_
    have h1 : CR ^ q * (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q
        ≤ CRn * Real.exp (qu * (Real.log (2 * 1.195) + 4)) :=
      le_trans (mul_le_mul_of_nonneg_left hB hCRq0)
        (mul_le_mul_of_nonneg_right hCRq (Real.exp_pos _).le)
    exact mul_le_mul h1 hRu hR0.le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  -- the windows
  set Sw := ∑ k ∈ Finset.Ico 4 (midJ x),
    thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (midY x) ^ q with hSwdef
  have hSw0 : 0 ≤ Sw := Finset.sum_nonneg fun k _ =>
    mul_nonneg (thetaPF_nonneg _ _ _ _ (by norm_num)) (Real.rpow_nonneg
      (le_trans zero_le_one (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith)
        k (midY x))) _)
  set Abel := G₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
    - (G₁ - G₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
    - (G₂ - G₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
    - (G₃ - G₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
    - G₄ * Real.exp (-(qu * wu + ql * (1 - 2 * ql))) with hAbel
  set Γ := 1 / ql + 1 / (ql * wl) + (1 / Λl + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10)
    with hΓdef
  have hd : 0 < 1 - Real.exp (-a) := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hTH0 : 0 < (3 / 2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hAbel0 : 0 ≤ Abel := by
    by_contra hneg
    have := mul_neg_of_pos_of_neg hTH0 (lt_of_not_ge hneg)
    have := mul_nonneg hd.le hSw0
    linarith
  have hgeom : V / (1 - Real.exp (-a)) ≤ Γ :=
    cell_geom_le_of (by linarith) hΛl hql0 hqlq hqqu hqu hwl0 hwl
  have hTH : (3 / 2 : ℝ) ^ (-a) ≤ Real.exp (-(qu * (1 - 2 * qu) * Real.log (3 / 2))) := by
    have e : Real.exp (-(qu * (1 - 2 * qu) * Real.log (3 / 2)))
        = (3 / 2 : ℝ) ^ (-(qu * (1 - 2 * qu))) := by
      rw [rpow_eq_exp_mul_log (by norm_num)]
      congr 1
      ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hΛq : Λ ^ (q / 2) ≤ Real.exp (qu / 2 * Real.log Λu) := by
    rw [← rpow_eq_exp_mul_log (by linarith)]
    calc Λ ^ (q / 2) ≤ Λ ^ (qu / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ Λu ^ (qu / 2) := Real.rpow_le_rpow hΛ0.le hΛu (by linarith)
  have hwin : CR ^ q * Sw
      ≤ R⁻¹ * (CRn * Real.exp (-(qu * (1 - 2 * qu) * Real.log (3 / 2)))
        * Real.exp (qu / 2 * Real.log Λu) * Γ * Abel) := by
    refine le_inv_mul_of_mul_le hR0 ?_
    have hSw1 : Sw ≤ (3 / 2) ^ (-a) * Abel / (1 - Real.exp (-a)) := by
      rw [le_div_iff₀ hd, mul_comm]; exact hmeso
    have e : (3 / 2 : ℝ) ^ (-a) * Abel / (1 - Real.exp (-a)) * R
        = (3 / 2) ^ (-a) * (V / (1 - Real.exp (-a))) * Λ ^ (q / 2) * Abel := by
      rw [hRdef]; field_simp
    have hSwR : Sw * R ≤ Real.exp (-(qu * (1 - 2 * qu) * Real.log (3 / 2))) * Γ
        * Real.exp (qu / 2 * Real.log Λu) * Abel := by
      calc Sw * R ≤ (3 / 2) ^ (-a) * Abel / (1 - Real.exp (-a)) * R :=
            mul_le_mul_of_nonneg_right hSw1 hR0.le
        _ = (3 / 2) ^ (-a) * (V / (1 - Real.exp (-a))) * Λ ^ (q / 2) * Abel := e
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul hTH hgeom
              (div_nonneg hV0.le hd.le) (Real.exp_pos _).le) hΛq
              (Real.rpow_nonneg hΛ0.le _) (mul_nonneg (Real.exp_pos _).le ?_)) hAbel0
            exact le_trans (div_nonneg hV0.le hd.le) hgeom
    calc CR ^ q * Sw * R = CR ^ q * (Sw * R) := by ring
      _ ≤ CRn * (Real.exp (-(qu * (1 - 2 * qu) * Real.log (3 / 2))) * Γ
          * Real.exp (qu / 2 * Real.log Λu) * Abel) :=
          mul_le_mul hCRq hSwR (mul_nonneg hSw0 hR0.le) (Real.exp_pos _).le
      _ = _ := by ring
  -- together
  have hasm' : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ)
      ≤ (uPFyAt q (midY x) + midTail x ^ q
          + CR ^ q * (uCenAt q (halfSigma x) (midY x) (midJ x) ^ q
            * uPFcAt q (halfSigma x) (midY x))
          + smallQReductionErr x (midZ x) (halfEta x) (halfEps x) ^ q)
        + CR ^ q * (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q + CR ^ q * Sw := by
    refine le_trans hasm (le_of_eq ?_)
    ring
  have hR0' : 0 ≤ R⁻¹ := (inv_pos.2 hR0).le
  have hfin' := mul_le_mul_of_nonneg_left hfin hR0'
  rw [hRudef] at hfar
  linarith [hsmall, hfar, hwin, hasm', hfin']

end RMF
