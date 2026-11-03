/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCellsChaosLeavesExplicit

/-!
# The first moment below `q = ½`: one cell of the Jensen regime

For `110 ≤ Λ = log log x ≤ 4000` and `q` in a cell, `RMF.u_cell_jensen` reduces
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` to numerals: every window by Jensen in four groups
keeping the sum's upper end (`RMF.uMeso_jensen_le`), the far range by Jensen, and the small pieces
and the central window through `w = (1 - 2q)Λ` (`RMF.uSmall_jensen_le`: `(1 + w)e^{-qw}`
decreases past `w = 1/q - 1`). The cells' numerals are in
`RMF/Weighted/UCellsJensen*Explicit.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The Jensen regime's pieces -/

/-- **Four groups on `[4, J)` keeping the sum's upper end**: with `w_k ≤ e^{-ak}c_g` on the groups
`{4}`, `{5}`, `{6}`, `[7, J)`, `c₁ ≥ … ≥ c₄ ≥ 0`, `a₀ ≤ a ≤ a₁` and `aJ ≤ T`,
`(1 - e^{-a})∑_{4≤k<J} w_k ≤ c₁e^{-4a₀} - (c₁ - c₂)e^{-5a₁} - (c₂ - c₃)e^{-6a₁}
  - (c₃ - c₄)e^{-7a₁} - c₄e^{-T}`. -/
lemma sum_four_groups_le_top {a a₀ a₁ T : ℝ} (ha : 0 < a) (ha₀ : a₀ ≤ a) (ha₁ : a ≤ a₁) {J : ℕ}
    (hJ : 7 ≤ J) (hT : a * J ≤ T) {w : ℕ → ℝ} {c₁ c₂ c₃ c₄ : ℝ} (h12 : c₂ ≤ c₁)
    (h23 : c₃ ≤ c₂) (h34 : c₄ ≤ c₃) (h4 : 0 ≤ c₄)
    (hw1 : ∀ k ∈ Finset.Ico 4 5, w k ≤ Real.exp (-(a * k)) * c₁)
    (hw2 : ∀ k ∈ Finset.Ico 5 6, w k ≤ Real.exp (-(a * k)) * c₂)
    (hw3 : ∀ k ∈ Finset.Ico 6 7, w k ≤ Real.exp (-(a * k)) * c₃)
    (hw4 : ∀ k ∈ Finset.Ico 7 J, w k ≤ Real.exp (-(a * k)) * c₄) :
    (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico 4 J, w k
      ≤ c₁ * Real.exp (-(4 * a₀)) - (c₁ - c₂) * Real.exp (-(5 * a₁))
        - (c₂ - c₃) * Real.exp (-(6 * a₁)) - (c₃ - c₄) * Real.exp (-(7 * a₁))
        - c₄ * Real.exp (-T) := by
  have e1 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 4 ≤ 5) hw1
  have e2 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 5 ≤ 6) hw2
  have e3 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 6 ≤ 7) hw3
  have e4 := one_sub_exp_neg_mul_sum_le_group ha hJ hw4
  have hs : ∑ k ∈ Finset.Ico 4 J, w k = ∑ k ∈ Finset.Ico 4 5, w k + ∑ k ∈ Finset.Ico 5 6, w k
      + ∑ k ∈ Finset.Ico 6 7, w k + ∑ k ∈ Finset.Ico 7 J, w k := by
    rw [Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 5) (by norm_num : 5 ≤ 6),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 6) (by norm_num : 6 ≤ 7),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 7) hJ]
  have x4 : Real.exp (-(a * ((4 : ℕ) : ℝ))) ≤ Real.exp (-(4 * a₀)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  have hx : ∀ n : ℕ, Real.exp (-(n * a₁)) ≤ Real.exp (-(a * (n : ℝ))) := fun n =>
    Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_left ha₁ (Nat.cast_nonneg (α := ℝ) n)
      linarith)
  have x5 := hx 5
  have x6 := hx 6
  have x7 := hx 7
  have xJ : Real.exp (-T) ≤ Real.exp (-(a * (J : ℝ))) := Real.exp_le_exp.2 (by linarith)
  push_cast at x4 x5 x6 x7 e1 e2 e3 e4 ⊢
  rw [hs, mul_add, mul_add, mul_add]
  have d12 : 0 ≤ c₁ - c₂ := by linarith
  have d23 : 0 ≤ c₂ - c₃ := by linarith
  have d34 : 0 ≤ c₃ - c₄ := by linarith
  have hc1 : 0 ≤ c₁ := by linarith
  have t1 := mul_le_mul_of_nonneg_left x4 hc1
  have t5 := mul_le_mul_of_nonneg_left x5 d12
  have t6 := mul_le_mul_of_nonneg_left x6 d23
  have t7 := mul_le_mul_of_nonneg_left x7 d34
  have tJ := mul_le_mul_of_nonneg_left xJ h4
  linarith

/-- **`(1 + w)e^{-cw}` decreases past `w = 1/c - 1`**: `1 + w ≤ (1 + u)e^{(w-u)/(1+u)}`. -/
lemma one_add_mul_exp_neg_anti {c u w : ℝ} (hc : 0 < c) (hu : 1 / c - 1 ≤ u) (huw : u ≤ w) :
    (1 + w) * Real.exp (-(c * w)) ≤ (1 + u) * Real.exp (-(c * u)) := by
  have hc1 : 0 < 1 / c := by positivity
  have hu1 : 0 < 1 + u := by linarith
  have h1 : 1 ≤ c * (1 + u) := by
    have h := mul_le_mul_of_nonneg_left (show 1 / c ≤ 1 + u by linarith) hc.le
    rwa [mul_one_div_cancel hc.ne'] at h
  have hwu : 0 ≤ w - u := by linarith
  have h2 : (w - u) / (1 + u) ≤ c * (w - u) := by
    rw [div_le_iff₀ hu1]
    have := mul_le_mul_of_nonneg_left h1 hwu
    linarith
  have h3 : 1 + w ≤ (1 + u) * Real.exp (c * (w - u)) := by
    have e : 1 + w = (1 + u) * ((w - u) / (1 + u) + 1) := by field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (le_trans (Real.add_one_le_exp _) (Real.exp_le_exp.2 h2))
      hu1.le
  calc (1 + w) * Real.exp (-(c * w))
      ≤ (1 + u) * Real.exp (c * (w - u)) * Real.exp (-(c * w)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (1 + u) * Real.exp (-(c * u)) := by
        rw [mul_assoc, ← Real.exp_add, show c * (w - u) + -(c * w) = -(c * u) by ring]

/-- The windows' count: `7 ≤ J₀ ≤ Λ + 1`. -/
lemma seven_le_tenJ_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    7 ≤ tenJ x ∧ (tenJ x : ℝ) ≤ Real.log (Real.log x) + 1 := by
  obtain ⟨hlly, hly⟩ := halfY_loglog_le hx
  have hlogy : 0 < Real.log (halfY x) := by linarith
  have h23 : Real.log (2 / 3 * Real.log (halfY x))
      = Real.log (2 / 3) + Real.log (Real.log (halfY x)) :=
    Real.log_mul (by norm_num) hlogy.ne'
  have hl23 : Real.log (2 / 3) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have h6 : 6 ≤ Real.log (2 / 3 * Real.log (halfY x)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 6 ≤ 404 := by interval_decide (trust := kernel)
    linarith
  constructor
  · have h := Nat.lt_floor_add_one (Real.log (2 / 3 * Real.log (halfY x)))
    have h7 : (6 : ℝ) < (tenJ x : ℝ) := by rw [tenJ]; push_cast; linarith
    have : 6 < tenJ x := by exact_mod_cast h7
    omega
  · rw [tenJ]
    push_cast
    have h0 : (0 : ℝ) ≤ Real.log (2 / 3 * Real.log (halfY x)) := le_trans (by norm_num) h6
    have := Nat.floor_le h0
    linarith

/-- **The geometric factor on a cell with `w = (1 - 2q)Λ ≥ w_l`**:
`(Λ⁻¹ + 1 - 2q)/(1 - e^{-q(1-2q)})
  ≤ 1/q_l + 1/(q_l w_l) + (1/Λ_l + 1 - 2q_l)(1/2 + q_u(1 - 2q_l)/10)`
(`RMF.cell_geom_le` with `w_l` for `(1 - 2q_u)·4000`). -/
lemma cell_geom_le_of {Λ q ql qu Λl wl : ℝ} (hΛl : 0 < Λl) (hΛ : Λl ≤ Λ) (hql : 0 < ql)
    (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2) (hwl0 : 0 < wl)
    (hwl : wl ≤ (1 - 2 * q) * Λ) :
    (Λ⁻¹ + (1 - 2 * q)) / (1 - Real.exp (-(q * (1 - 2 * q))))
      ≤ 1 / ql + 1 / (ql * wl) + (1 / Λl + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) := by
  have hv0 : 0 < 1 - 2 * q := by linarith
  have hq0 : 0 < q := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have ha0 : 0 < q * (1 - 2 * q) := mul_pos hq0 hv0
  have ha8 : q * (1 - 2 * q) ≤ 1 / 8 := by linarith [sq_nonneg (q - 1 / 4)]
  have hinv := inv_one_sub_exp_neg_le_taylor ha0 ha8
  have hΛi : Λ⁻¹ ≤ 1 / Λl := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hΛl hΛ
  have hΛi0 : 0 < Λ⁻¹ := inv_pos.2 hΛ0
  have hV0 : 0 ≤ Λ⁻¹ + (1 - 2 * q) := by linarith
  rw [div_eq_mul_inv]
  have e : (Λ⁻¹ + (1 - 2 * q)) * (1 / (q * (1 - 2 * q)) + 1 / 2 + q * (1 - 2 * q) / 10)
      = 1 / (q * ((1 - 2 * q) * Λ)) + 1 / q
        + (Λ⁻¹ + (1 - 2 * q)) * (1 / 2 + q * (1 - 2 * q) / 10) := by
    field_simp
    ring
  have t1 : 1 / (q * ((1 - 2 * q) * Λ)) ≤ 1 / (ql * wl) :=
    one_div_le_one_div_of_le (mul_pos hql hwl0) (mul_le_mul hqlq hwl hwl0.le hq0.le)
  have t2 : 1 / q ≤ 1 / ql := one_div_le_one_div_of_le hql hqlq
  have t3 : (Λ⁻¹ + (1 - 2 * q)) * (1 / 2 + q * (1 - 2 * q) / 10)
      ≤ (1 / Λl + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) := by
    have h1 : Λ⁻¹ + (1 - 2 * q) ≤ 1 / Λl + (1 - 2 * ql) := by linarith
    have h2 : q * (1 - 2 * q) ≤ qu * (1 - 2 * ql) :=
      mul_le_mul hqqu (by linarith) hv0.le (by linarith)
    exact mul_le_mul h1 (by linarith) (by linarith) (by linarith [one_div_pos.2 hΛl])
  calc (Λ⁻¹ + (1 - 2 * q)) * (1 - Real.exp (-(q * (1 - 2 * q))))⁻¹
      ≤ (Λ⁻¹ + (1 - 2 * q)) * (1 / (q * (1 - 2 * q)) + 1 / 2 + q * (1 - 2 * q) / 10) :=
        mul_le_mul_of_nonneg_left hinv hV0
    _ = _ := e
    _ ≤ _ := by linarith

/-- **(PF) against `τ⁻¹` through `w`**: with `w = (1 - 2q)Λ ≥ w_l ≥ 1/q_l - 1`,
`e^{-a(Λ - log Λ)}Λ^{cq}·(Λ⁻¹ + 1 - 2q)Λ^{q/2} = (1 + w)e^{-qw}Λ^{a + (c+1/2)q - 1}
  ≤ (1 + w_l)e^{-q_l w_l}Λ_l^{a₁ + (c+1/2)q_u - 1}` (`a = q(1-2q) ≤ a₁`, the exponent `≤ 0`). -/
lemma pf_tau_le {Λ q ql qu Λl wl a₁ c : ℝ} (hΛl1 : 1 ≤ Λl) (hΛl : Λl ≤ Λ) (hql0 : 0 < ql)
    (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu ≤ 1 / 2) (ha₁ : q * (1 - 2 * q) ≤ a₁)
    (hc : 0 ≤ c) (hexp : a₁ + (c + 1 / 2) * qu - 1 ≤ 0) (hwl : wl ≤ (1 - 2 * q) * Λ)
    (hwl1 : 1 / ql - 1 ≤ wl) :
    Real.exp (-(q * (1 - 2 * q) * (Λ - Real.log Λ))) * Λ ^ (c * q)
        * ((Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2))
      ≤ (1 + wl) * Real.exp (-(ql * wl)) * Λl ^ (a₁ + (c + 1 / 2) * qu - 1) := by
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := by linarith
  have h2q : 2 ≤ 1 / ql := by rw [le_div_iff₀ hql0]; linarith
  set w := (1 - 2 * q) * Λ with hw
  have hw0 : 0 ≤ w := by linarith
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
  have f1 : (1 + w) * Real.exp (-(q * w)) ≤ (1 + wl) * Real.exp (-(ql * wl)) :=
    calc (1 + w) * Real.exp (-(q * w)) ≤ (1 + w) * Real.exp (-(ql * w)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hqlq hw0))) (by linarith)
      _ ≤ (1 + wl) * Real.exp (-(ql * wl)) := one_add_mul_exp_neg_anti hql0 hwl1 hwl
  have f2 : Λ ^ (q * (1 - 2 * q) + (c + 1 / 2) * q - 1) ≤ Λl ^ (a₁ + (c + 1 / 2) * qu - 1) := by
    have hle : q * (1 - 2 * q) + (c + 1 / 2) * q - 1 ≤ a₁ + (c + 1 / 2) * qu - 1 := by
      have := mul_le_mul_of_nonneg_left hqqu (by linarith : (0 : ℝ) ≤ c + 1 / 2)
      linarith
    calc Λ ^ (q * (1 - 2 * q) + (c + 1 / 2) * q - 1) ≤ Λ ^ (a₁ + (c + 1 / 2) * qu - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hle
      _ ≤ Λl ^ (a₁ + (c + 1 / 2) * qu - 1) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hΛl hexp
  exact mul_le_mul f1 f2 (Real.rpow_nonneg hΛ0.le _)
    (mul_nonneg (by linarith) (Real.exp_pos _).le)

/-- (PF) at `y` below `(log y)^{-a}`: its bracket is negative. -/
lemma uPFyAt_le_loglog {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) :
    uPFyAt q (halfY x) ≤ Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (halfY x)))) := by
  unfold uPFyAt
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hlogy0 : 0 < Real.log (halfY x) := by linarith
  have ha : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have h1 : Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log (halfY x) - 3 / 20)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ha ?_)
    have : 9.0028 / Real.log (halfY x) ≤ 9.0028 / 22000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
    linarith
  have h2 : Real.log (halfY x) ^ (q * (2 * q - 1))
      = Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (halfY x)))) := by
    rw [rpow_eq_exp_mul_log hlogy0]
    congr 1
    ring
  rw [h2]
  calc _ ≤ 1 * Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (halfY x)))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := one_mul _

/-- (PF) at the central window below `(log y)^{-a}`: its bracket is negative for
`x ≥ exp(e^{110})`. -/
lemma uPFcAt_le_loglog {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) :
    uPFcAt q (halfSigma x) (halfY x)
      ≤ Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (halfY x)))) := by
  unfold uPFcAt
  obtain ⟨-, hL, hΛ, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hlogy0 : 0 < Real.log (halfY x) := by linarith
  have ha : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have hσy := halfSigma_mul_log_le hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ0 : 0 ≤ halfSigma x := by rw [halfSigma]; positivity
  have h16 : 1 / (16 * Real.log (Real.log x)) ≤ 1 / 1760 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hσ1 : halfSigma x ≤ 1 / 1000 := by
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Real.log (halfY x)) hσ0
    linarith
  have hl4 : Real.log 4 ≤ 14 / 10 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log (halfY x)
      + 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4) - 3 / 20)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ha ?_)
    have t1 : 9.0028 / Real.log (halfY x) ≤ 9.0028 / 22000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
    have h3 : 2 * halfSigma x * (Real.log 4 + 4) ≤ 2 * (1 / 1000) * (14 / 10 + 4) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have e : 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4)
        = 2 * (halfSigma x * Real.log (halfY x)) + 2 * halfSigma x * (Real.log 4 + 4) := by ring
    rw [e]
    linarith
  have h2 : Real.log (halfY x) ^ (q * (2 * q - 1))
      = Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (halfY x)))) := by
    rw [rpow_eq_exp_mul_log hlogy0]
    congr 1
    ring
  rw [h2]
  calc _ ≤ 1 * Real.exp (-(q * (1 - 2 * q) * Real.log (Real.log (halfY x)))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := one_mul _

/-- The far range's bound is at most its Jensen branch. -/
lemma uFarBound_le_jensen (Pf : FarChaos) (n : ℕ) (q x : ℝ) :
    uFarBound Pf n q x ≤ (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ q := by
  unfold uFarBound
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- `w = (1 - 2q)Λ` on a cell: `(1 - 2q_u)Λ_l ≤ w ≤ (1 - 2q_l)Λ_u`. -/
lemma w_bounds_of_cell {Λ q ql qu Λl Λu : ℝ} (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu ≤ 1 / 2)
    (hΛl : Λl ≤ Λ) (hΛu : Λ ≤ Λu) (hΛl0 : 0 ≤ Λl) :
    (1 - 2 * qu) * Λl ≤ (1 - 2 * q) * Λ ∧ (1 - 2 * q) * Λ ≤ (1 - 2 * ql) * Λu :=
  ⟨mul_le_mul (by linarith) hΛl hΛl0 (by linarith),
    mul_le_mul (by linarith) hΛu (by linarith) (by linarith)⟩

/-- `X ≤ R⁻¹z` from `XR ≤ z`. -/
lemma le_inv_mul_of_mul_le {X R z : ℝ} (hR : 0 < R) (h : X * R ≤ z) : X ≤ R⁻¹ * z := by
  rw [le_inv_mul_iff₀ hR, mul_comm]
  exact h

/-- **`τ⁻¹` on a cell**: `(Λ⁻¹ + 1 - 2q)Λ^{q/2} ≤ (1/Λ_l + 1 - 2q_l)e^{(q_u/2)log Λ_u}`. -/
lemma tauInv_le {Λ q ql qu Λl Λu : ℝ} (hΛl : 1 ≤ Λl) (hΛl' : Λl ≤ Λ) (hΛu : Λ ≤ Λu)
    (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu ≤ 1 / 2) (hq0 : 0 ≤ q) :
    (Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2)
      ≤ (1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu) := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : Λ⁻¹ + (1 - 2 * q) ≤ 1 / Λl + (1 - 2 * ql) := by
    have : Λ⁻¹ ≤ 1 / Λl := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by linarith) hΛl'
    linarith
  have h2 : Λ ^ (q / 2) ≤ Real.exp (qu / 2 * Real.log Λu) := by
    rw [← rpow_eq_exp_mul_log (by linarith)]
    calc Λ ^ (q / 2) ≤ Λ ^ (qu / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ Λu ^ (qu / 2) := Real.rpow_le_rpow hΛ0.le hΛu (by linarith)
  have hV0 : 0 ≤ Λ⁻¹ + (1 - 2 * q) := by
    have := inv_pos.2 hΛ0
    linarith
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hΛ0.le _)
    (by have := one_div_pos.2 (by linarith : (0 : ℝ) < Λl); linarith)

set_option maxHeartbeats 1000000 in
-- five bounds, each by a named lemma
/-- **The small pieces and the central window in the Jensen regime**: for `Λ ∈ [Λ_l, Λ_u]`,
`Λ_l ≥ 110`, `q ∈ [q_l, q_u] ⊆ [0.41, ½)` and `w = (1 - 2q)Λ ≥ w_l ≥ 1/q_l - 1`, (PF) at `y`, the
central window (`C_c ≤ 51Λ`), the smooth tail and the reduction's error are
`≤ τ·((1 + w_l)e^{-q_l w_l}(Λ_l^{a₁+q_u/2-1} + C_R'51^{q_u}Λ_l^{a₁+3q_u/2-1})
  + (e^{q_l(1.42 - 0.4995Λ_l)} + e^{-q_lΛ_l/4})(1/Λ_l + 1 - 2q_l)Λ_u^{q_u/2})`,
`τ = (Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`. -/
theorem uSmall_jensen_le {x q ql qu Λl Λu wl : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : Λl ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ Λu) (hΛl110 : 110 ≤ Λl)
    (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2)
    (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl) :
    uPFyAt q (halfY x) + halfTail x ^ q
        + smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x))
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
      ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ * Real.log (Real.log x) ^ (-(q / 2))
        * ((1 + wl) * Real.exp (-(ql * wl))
            * (Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl)
              + Real.exp (ql * Real.log (33885 / 100000)) * Real.exp (qu * Real.log 51)
                * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl))
          + (Real.exp (ql * (142 / 100 - 4995 / 10000 * Λl)) + Real.exp (-(ql * Λl / 4)))
            * (1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu)) := by
  obtain ⟨hx0, hL, hΛ110, -, -, -⟩ := half_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  obtain ⟨hlly, hly⟩ := halfY_loglog_le hx
  have hll := halfY_loglog_ge_sub hx
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
  -- the (PF) decay `e^{-a(Λ - log Λ)}`
  have hdec : Real.exp (-(a * Real.log (Real.log (halfY x))))
      ≤ Real.exp (-(a * (Λ - Real.log Λ))) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hll ha0))
  have hPFy := le_trans (uPFyAt_le_loglog hx hq0.le hq5) hdec
  have hPFc := le_trans (uPFcAt_le_loglog hx hq0.le hq5) hdec
  have hpf0 := pf_tau_le (c := 0) (by linarith) hΛl hql0 hqlq hqqu (by linarith) ha₁ le_rfl
    (by linarith) hwl hwl1
  have hpf1 := pf_tau_le (c := 1) (by linarith) hΛl hql0 hqlq hqqu (by linarith) ha₁ zero_le_one
    (by linarith) hwl hwl1
  rw [zero_mul, Real.rpow_zero, mul_one] at hpf0
  have eΛl0 : Λl ^ (ql * (1 - 2 * ql) + (0 + 1 / 2) * qu - 1)
      = Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl) := by
    rw [rpow_eq_exp_mul_log (by linarith)]; congr 1; ring
  have eΛl1 : Λl ^ (ql * (1 - 2 * ql) + (1 + 1 / 2) * qu - 1)
      = Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl) := by
    rw [rpow_eq_exp_mul_log (by linarith)]; congr 1; ring
  rw [eΛl0] at hpf0
  rw [eΛl1] at hpf1
  set D := (1 + wl) * Real.exp (-(ql * wl)) with hDdef
  have hD0 : 0 ≤ D := by
    have h2q : 2 ≤ 1 / ql := by rw [le_div_iff₀ hql0]; linarith
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  -- (PF) at `y`
  have hy : uPFyAt q (halfY x) * R
      ≤ D * Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl) :=
    le_trans (mul_le_mul_of_nonneg_right hPFy hR0.le) hpf0
  -- the central window
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  set CR := smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) with hCRdef
  have hCR0 : 0 ≤ CR := (smallQReductionConst_pos hz2 hzy hη hε).le
  have hCRq : CR ^ q ≤ Real.exp (ql * Real.log (33885 / 100000)) := by
    calc CR ^ q ≤ (33885 / 100000 : ℝ) ^ q := Real.rpow_le_rpow hCR0 (halfCR_le hx) hq0.le
      _ ≤ (33885 / 100000 : ℝ) ^ ql :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hqlq
      _ = Real.exp (ql * Real.log (33885 / 100000)) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  have hC0 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) := by
    unfold uCenAt
    have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
    have hl : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := Nat.cast_nonneg _
      linarith)
    have h2 : 0 ≤ Real.exp (2 * (1 - q)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1 := by
      have : 0 ≤ 2 * (1 - q)
          * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
          * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2 := by
        have : 0 ≤ 1 - q := by linarith
        positivity
      linarith [Real.add_one_le_exp (2 * (1 - q)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2)]
    have hlogy : 0 < Real.log (halfY x) := by linarith
    positivity
  have hCen : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
      ≤ Real.exp (qu * Real.log 51) * Λ ^ (1 * q) := by
    have h1 := uCen_le hx hq0.le
    rw [← hΛdef] at h1
    have h51 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ≤ 51 * Λ := by linarith
    calc uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q ≤ (51 * Λ) ^ q :=
          Real.rpow_le_rpow hC0 h51 hq0.le
      _ = (51 : ℝ) ^ q * Λ ^ (1 * q) := by rw [Real.mul_rpow (by norm_num) hΛ0.le, one_mul]
      _ ≤ (51 : ℝ) ^ qu * Λ ^ (1 * q) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hqqu) (Real.rpow_nonneg hΛ0.le _)
      _ = Real.exp (qu * Real.log 51) * Λ ^ (1 * q) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  have hPFc0 : 0 ≤ uPFcAt q (halfSigma x) (halfY x) := by
    unfold uPFcAt
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
  have hcen : CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
        * uPFcAt q (halfSigma x) (halfY x)) * R
      ≤ D * (Real.exp (ql * Real.log (33885 / 100000)) * Real.exp (qu * Real.log 51)
        * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl)) := by
    have hCq0 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q := Real.rpow_nonneg hC0 q
    have h1 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
        ≤ Real.exp (qu * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ))) :=
      mul_le_mul hCen hPFc hPFc0 (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hΛ0.le _))
    have h2 : Real.exp (qu * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ))) * R
        = Real.exp (qu * Real.log 51) * (Real.exp (-(a * (Λ - Real.log Λ))) * Λ ^ (1 * q) * R) := by
      ring
    have h3 := mul_le_mul_of_nonneg_left hpf1 (Real.exp_pos (qu * Real.log 51)).le
    calc CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
          * uPFcAt q (halfSigma x) (halfY x)) * R
        ≤ Real.exp (ql * Real.log (33885 / 100000))
          * (Real.exp (qu * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ)))
            * R) := by
          rw [mul_assoc]
          refine mul_le_mul hCRq (mul_le_mul_of_nonneg_right h1 hR0.le)
            (mul_nonneg (mul_nonneg hCq0 hPFc0) hR0.le) (Real.exp_pos _).le
      _ ≤ Real.exp (ql * Real.log (33885 / 100000))
          * (Real.exp (qu * Real.log 51)
            * (D * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl))) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = _ := by ring
  -- the tail and the error
  have hRu := tauInv_le (by linarith) hΛl hΛu hqlq hqqu (by linarith) hq0.le
  set Ru := (1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu) with hRudef
  have hT := halfTail_le_decay hx
  rw [← hΛdef] at hT
  have hT0 : 0 ≤ halfTail x := by
    unfold halfTail
    exact Finset.sum_nonneg fun m _ => by positivity
  have hTq : halfTail x ^ q ≤ Real.exp (ql * (142 / 100 - 4995 / 10000 * Λl)) := by
    calc halfTail x ^ q ≤ Real.exp (142 / 100 - 4995 / 10000 * Λ) ^ q :=
          Real.rpow_le_rpow hT0 hT hq0.le
      _ = Real.exp ((142 / 100 - 4995 / 10000 * Λ) * q) := by rw [← Real.exp_mul]
      _ ≤ Real.exp (ql * (142 / 100 - 4995 / 10000 * Λl)) := by
          refine Real.exp_le_exp.2 ?_
          have h1 : 142 / 100 - 4995 / 10000 * Λ ≤ 142 / 100 - 4995 / 10000 * Λl := by linarith
          have h2 : 142 / 100 - 4995 / 10000 * Λl ≤ 0 := by linarith
          have := mul_le_mul_of_nonpos_left hqlq (by linarith : 142 / 100 - 4995 / 10000 * Λ ≤ 0)
          have := mul_le_mul_of_nonneg_left h1 hql0.le
          linarith
  have hE := halfErr_le_decay hx
  obtain ⟨hs, -, -⟩ := half_big hx
  rw [← hΛdef] at hE hs
  have hE0 : 0 ≤ smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) := by
    unfold smallQReductionErr
    have hlogz : 0 < Real.log (halfZ x) := Real.log_pos (by
      have : (2 : ℝ) ≤ (halfZ x : ℝ) := by exact_mod_cast hz2
      linarith)
    have hL0 : 0 ≤ 1 + Real.log x := by linarith [Real.add_one_le_exp (110 : ℝ)]
    positivity
  have hE1 : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ≤ Real.exp (-(Λ / 4)) := by
    refine le_trans hE ?_
    rw [hs, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    have h7 : 7 * Λ ≤ Real.exp (Λ / 4) := by
      have e : Real.exp (Λ / 4) = Real.exp (Λ / 8) * Real.exp (Λ / 8) := by
        rw [← Real.exp_add]; ring_nf
      have h1 : Λ / 8 ≤ Real.exp (Λ / 8) := by linarith [Real.add_one_le_exp (Λ / 8)]
      have h2 : 56 ≤ Real.exp (Λ / 8) := by
        have : (56 : ℝ) ≤ Real.exp (55 / 4) := by interval_decide (trust := kernel)
        exact le_trans this (Real.exp_le_exp.2 (by linarith))
      rw [e]
      have := mul_le_mul h2 h1 (by linarith) (by linarith)
      linarith
    rw [show -(Λ / 4) + Λ / 2 = Λ / 4 by ring]
    exact h7
  have hEq : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
      ≤ Real.exp (-(ql * Λl / 4)) := by
    calc smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
        ≤ Real.exp (-(Λ / 4)) ^ q := Real.rpow_le_rpow hE0 hE1 hq0.le
      _ = Real.exp (-(Λ / 4) * q) := by rw [← Real.exp_mul]
      _ ≤ Real.exp (-(ql * Λl / 4)) := by
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul hqlq hΛl (by linarith) hq0.le
          linarith
  have hTE : (halfTail x ^ q + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q) * R
      ≤ (Real.exp (ql * (142 / 100 - 4995 / 10000 * Λl)) + Real.exp (-(ql * Λl / 4))) * Ru :=
    mul_le_mul (add_le_add hTq hEq) hRu hR0.le
      (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  -- together
  refine le_inv_mul_of_mul_le hR0 ?_
  have e : (uPFyAt q (halfY x) + halfTail x ^ q
        + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
          * uPFcAt q (halfSigma x) (halfY x))
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q) * R
      = uPFyAt q (halfY x) * R
        + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
          * uPFcAt q (halfSigma x) (halfY x)) * R
        + (halfTail x ^ q + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q) * R := by
    ring
  rw [e]
  rw [hRudef] at hTE
  linarith [hy, hcen, hTE]

/-- **The Jensen regime's windows, summed**: every window by Jensen in the groups
`{4}, {5}, {6}, [7, J₀)`, keeping the sum's upper end through `aJ₀ ≤ q_u w_u + a₁`
(`RMF.sum_four_groups_le_top`, `RMF.uWindowBound_le_jensen`). -/
theorem uMeso_jensen_le {x q ql qu wu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2)
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ wu) {P : ℕ → WinChaos}
    (hP : ∀ k, (P k).Valid) {G₁ G₂ G₃ G₄ : ℝ}
    (hG₁ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 4 y ^ qu ≤ G₁)
    (hG₂ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 5 y ^ qu ≤ G₂)
    (hG₃ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 6 y ^ qu ≤ G₃)
    (hG₄ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 7 y ^ qu ≤ G₄)
    (h12 : G₂ ≤ G₁) (h23 : G₃ ≤ G₂) (h34 : G₄ ≤ G₃) :
    (1 - Real.exp (-(q * (1 - 2 * q)))) * ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k
      ≤ (3 / 2) ^ (-(q * (1 - 2 * q)))
        * (G₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
          - (G₁ - G₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
          - (G₂ - G₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
          - (G₃ - G₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
          - G₄ * Real.exp (-(qu * wu + ql * (1 - 2 * ql)))) := by
  obtain ⟨-, -, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hJ7, hJΛ⟩ := seven_le_tenJ_le hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hq0 : 0 < q := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 < a := mul_pos hq0 hv0
  have ha₀ : qu * (1 - 2 * qu) ≤ a := mul_one_sub_two_mul_anti (by linarith) hqqu
  have ha₁ : a ≤ ql * (1 - 2 * ql) := mul_one_sub_two_mul_anti (by linarith) hqlq
  have hG₄0 : 0 ≤ G₄ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) 7 (halfY x))) _)
    (hG₄ _ hly)
  have hTH0 : 0 < (3 / 2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hT : a * (tenJ x : ℝ) ≤ qu * wu + ql * (1 - 2 * ql) := by
    have h1 : a * (tenJ x : ℝ) ≤ a * (Λ + 1) := mul_le_mul_of_nonneg_left hJΛ ha0.le
    have h2 : a * Λ ≤ qu * wu := by
      rw [hadef, mul_assoc]
      exact mul_le_mul hqqu hwu (mul_nonneg hv0.le (by linarith)) (by linarith)
    linarith
  have hw : ∀ (k₁ : ℕ) (G : ℝ),
      (∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql k₁ y ^ qu ≤ G) →
      ∀ k ∈ Finset.Ico 4 (tenJ x), k₁ ≤ k →
        uWindowBound P q x k ≤ Real.exp (-(a * k)) * ((3 / 2) ^ (-a) * G) :=
    fun k₁ G hG k hk hk₁ =>
      uWindowBound_le_jensen hx hq0.le hqlq hqqu (by linarith) hk₁ hk (hP k) (hG _ hly)
  have hmem : ∀ {s t : ℕ}, 4 ≤ s → t ≤ tenJ x → ∀ k ∈ Finset.Ico s t,
      k ∈ Finset.Ico 4 (tenJ x) := fun hs ht k hk =>
    Finset.mem_Ico.2 ⟨le_trans hs (Finset.mem_Ico.1 hk).1,
      lt_of_lt_of_le (Finset.mem_Ico.1 hk).2 ht⟩
  have h := sum_four_groups_le_top (w := fun k => uWindowBound P q x k) ha0 ha₀ ha₁ hJ7 hT
    (c₁ := (3 / 2) ^ (-a) * G₁) (c₂ := (3 / 2) ^ (-a) * G₂) (c₃ := (3 / 2) ^ (-a) * G₃)
    (c₄ := (3 / 2) ^ (-a) * G₄)
    (mul_le_mul_of_nonneg_left h12 hTH0.le) (mul_le_mul_of_nonneg_left h23 hTH0.le)
    (mul_le_mul_of_nonneg_left h34 hTH0.le) (mul_nonneg hTH0.le hG₄0)
    (fun k hk => hw 4 G₁ hG₁ k (hmem le_rfl (by omega) k hk) (Finset.mem_Ico.1 hk).1)
    (fun k hk => hw 5 G₂ hG₂ k (hmem (by norm_num) (by omega) k hk) (Finset.mem_Ico.1 hk).1)
    (fun k hk => hw 6 G₃ hG₃ k (hmem (by norm_num) (by omega) k hk) (Finset.mem_Ico.1 hk).1)
    (fun k hk => hw 7 G₄ hG₄ k (hmem (by norm_num) le_rfl k hk) (Finset.mem_Ico.1 hk).1)
  refine le_trans h (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
-- the assembly and three bounds, combined linearly
/-- **One cell of the Jensen regime**: for `x ≥ exp(e^{110})` with `Λ = log log x ∈ [Λ_l, Λ_u]`,
`Λ_l ≥ 110`, `q ∈ [q_l, q_u] ⊆ [0.41, ½)`, `w = (1 - 2q)Λ ∈ [w_l, w_u]` with `w_l ≥ 1/q_l - 1`,
window constants `G_k(q_l)^{q_u} ≤ G_g` decreasing, and the certificate `hfin`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`: every window and the far range by Jensen
(`RMF.uMeso_jensen_le`, `RMF.uFarBound_le_jensen`), the small pieces and the central window
through `w` (`RMF.uSmall_jensen_le`). -/
theorem u_cell_jensen {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql qu Λl Λu wl wu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛl : Λl ≤ Real.log (Real.log x)) (hΛu : Real.log (Real.log x) ≤ Λu) (hΛl110 : 110 ≤ Λl)
    (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu) (hqu : qu < 1 / 2)
    (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl)
    (hwu : (1 - 2 * q) * Real.log (Real.log x) ≤ wu) {G₁ G₂ G₃ G₄ : ℝ}
    (hG₁ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 4 y ^ qu ≤ G₁)
    (hG₂ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 5 y ^ qu ≤ G₂)
    (hG₃ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 6 y ^ qu ≤ G₃)
    (hG₄ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 7 y ^ qu ≤ G₄)
    (h12 : G₂ ≤ G₁) (h23 : G₃ ≤ G₂) (h34 : G₄ ≤ G₃)
    (hfin : (1 + wl) * Real.exp (-(ql * wl))
          * (Real.exp ((ql * (1 - 2 * ql) + qu / 2 - 1) * Real.log Λl)
            + Real.exp (ql * Real.log (33885 / 100000)) * Real.exp (qu * Real.log 51)
              * Real.exp ((ql * (1 - 2 * ql) + 3 / 2 * qu - 1) * Real.log Λl))
        + (Real.exp (ql * (142 / 100 - 4995 / 10000 * Λl)) + Real.exp (-(ql * Λl / 4)))
          * (1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu)
        + Real.exp (ql * Real.log (33885 / 100000))
          * Real.exp (qu * (Real.log (2 * 1.195) + 4))
          * ((1 / Λl + (1 - 2 * ql)) * Real.exp (qu / 2 * Real.log Λu))
        + Real.exp (ql * Real.log (33885 / 100000))
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
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  have hsmall := uSmall_jensen_le hx hΛl hΛu hΛl110 hql hqlq hqqu hqu hwl hwl1
  set P : ℕ → WinChaos := fun _ => ⟨20, 45 / 2, 35, 10, 2000⟩ with hPdef
  have hPv : ∀ k, (P k).Valid := fun _ => uChaosW_valid_7
  have hmeso := uMeso_jensen_le hx hql hqlq hqqu hqu hwu hPv hG₁ hG₂ hG₃ hG₄ h12 h23 h34
  have hasm := integral_rpow_weightedRademacherSum_le_u_assembly (q := q) hX hx (by linarith)
    (by linarith) hPv uFarP_valid 0
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := by linarith
  have hql0 : 0 < ql := by linarith
  have h2q : 2 ≤ 1 / ql := by rw [le_div_iff₀ hql0]; linarith
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
  set CR := smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) with hCRdef
  have hCR0 : 0 ≤ CR := (smallQReductionConst_pos hz2 hzy hη hε).le
  have hCRq : CR ^ q ≤ Real.exp (ql * Real.log (33885 / 100000)) := by
    calc CR ^ q ≤ (33885 / 100000 : ℝ) ^ q := Real.rpow_le_rpow hCR0 (halfCR_le hx) hq0.le
      _ ≤ (33885 / 100000 : ℝ) ^ ql :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hqlq
      _ = Real.exp (ql * Real.log (33885 / 100000)) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  set CRn := Real.exp (ql * Real.log (33885 / 100000)) with hCRn
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
  have hfar : CR ^ q * uFarBound uFarP 0 q x
      ≤ R⁻¹ * (CRn * Real.exp (qu * (Real.log (2 * 1.195) + 4)) * Ru) := by
    refine le_inv_mul_of_mul_le hR0 ?_
    have h1 : CR ^ q * uFarBound uFarP 0 q x
        ≤ CRn * Real.exp (qu * (Real.log (2 * 1.195) + 4)) :=
      le_trans (mul_le_mul_of_nonneg_left (le_trans (uFarBound_le_jensen uFarP 0 q x) hB) hCRq0)
        (mul_le_mul_of_nonneg_right hCRq (Real.exp_pos _).le)
    exact mul_le_mul h1 hRu hR0.le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  -- the windows
  set Sw := ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k with hSwdef
  have hSw0 : 0 ≤ Sw := Finset.sum_nonneg fun k _ => uWindowBound_nonneg hPv hq0.le (by linarith) k
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
    cell_geom_le_of (by linarith) hΛl hql0 hqlq hqqu hqu (by linarith) hwl
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
      ≤ (uPFyAt q (halfY x) + halfTail x ^ q
          + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
            * uPFcAt q (halfSigma x) (halfY x))
          + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q)
        + CR ^ q * uFarBound uFarP 0 q x + CR ^ q * Sw := by
    refine le_trans hasm (le_of_eq ?_)
    ring
  have hR0' : 0 ≤ R⁻¹ := (inv_pos.2 hR0).le
  have hfin' := mul_le_mul_of_nonneg_left hfin hR0'
  rw [hRudef] at hfar
  linarith [hsmall, hfar, hwin, hasm', hfin']

end RMF
