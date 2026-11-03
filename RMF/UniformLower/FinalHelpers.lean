/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.LowerConstNumeral
import RMF.Weighted.HalfEvents
import RMF.UniformLower.C3NumeralsK
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import LeanCert.Tactic.IntervalAuto

/-!
# The final assembly: helpers

For `x ≥ exp(e^{6000})` and `Λ = log log x`:

* `RMF.loglog_facts_of_six_thousand`: `Λ ≥ 6000`, `log x ≥ e^{6000}`, `x ≥ RMF.windowThreshold`
  and `x ≥ e^{405}`;
* `RMF.exists_damping_level`: the maximal damping level `T = ⌊log(1/(200σ))⌋`, with
  `σe^T ≤ 1/200 < σe^{T+1}`;
* `RMF.scaleCut_add_seven_le`: `c_{T+7} ≤ ⌊x⌋ + 1` once `T + 7 ≤ Λ`;
* `RMF.exp_neg_mul_rpow_le_of_six_thousand`: `e^{-qΛ}Λ^{q/2} ≤ e^{-(1376/1377)qΛ}` for `Λ ≥ 6000`;
* for the mid range `2100 ≤ Λ ≤ 6000`: `RMF.loglog_facts_of_2100`,
  `RMF.exp_exp_le_of_le_loglog` and `RMF.exp_neg_mul_rpow_le_of_2100` (`545/546`);
* `RMF.mul_log_ge_tangent`: `q log q` lies above its tangents;
* the certificates' cell bounds: `q log q` at the cell's worse end or `-e⁻¹`, `q(1 - 2q)` at its
  worse end or `1/8`, and `c₃ = RMF.c3FloorK q 1` from the table `RMF.c3OneTab` on the cell.
-/

namespace RMF

/-- **The range `x ≥ exp(e^{6000})`**: `Λ = log log x ≥ 6000`, `log x ≥ e^{6000}`,
`x ≥ RMF.windowThreshold` (`≤ exp(e^{1621})`, `RMF.windowThreshold_le`) and `x ≥ e^{405}`. -/
theorem loglog_facts_of_six_thousand {x : ℝ} (hx : Real.exp (Real.exp 6000) ≤ x) :
    6000 ≤ Real.log (Real.log x) ∧ Real.exp 6000 ≤ Real.log x ∧ windowThreshold ≤ x
      ∧ Real.exp 405 ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 6000 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hΛ : 6000 ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL)).2 hL
  have h1621 : Real.exp (Real.exp 1621) ≤ x :=
    le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hx
  have h405 : (405 : ℝ) ≤ Real.exp 6000 := by
    have := Real.add_one_le_exp (6000 : ℝ)
    linarith
  exact ⟨hΛ, hL, windowThreshold_le.trans h1621,
    le_trans (Real.exp_le_exp.2 h405) hx⟩

/-- **The damping level**: for `0 < σ ≤ 1/200`, `T = ⌊log(1/(200σ))⌋` has
`σe^T ≤ 1/200 < σe^{T+1}` and `log(1/(200σ)) - 1 < T ≤ log(1/(200σ))`. -/
theorem exists_damping_level {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 200) :
    ∃ T : ℕ, σ * Real.exp (T : ℝ) ≤ 1 / 200 ∧ 1 / 200 < σ * Real.exp ((T : ℝ) + 1)
      ∧ Real.log (1 / (200 * σ)) - 1 < T ∧ (T : ℝ) ≤ Real.log (1 / (200 * σ)) := by
  have h200 : 0 < 200 * σ := by positivity
  have hone : 1 ≤ 1 / (200 * σ) := by
    rw [le_div_iff₀ h200]
    linarith
  set ℓ := Real.log (1 / (200 * σ)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hone
  have heℓ : Real.exp ℓ = 1 / (200 * σ) := Real.exp_log (by positivity)
  have hfl : (⌊ℓ⌋₊ : ℝ) ≤ ℓ := Nat.floor_le hℓ0
  have hlt : ℓ < (⌊ℓ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ℓ
  refine ⟨⌊ℓ⌋₊, ?_, ?_, by linarith, hfl⟩
  · have h1 : Real.exp (⌊ℓ⌋₊ : ℝ) ≤ 1 / (200 * σ) := heℓ ▸ Real.exp_le_exp.2 hfl
    rw [le_div_iff₀ h200] at h1
    linarith
  · have h2 : 1 / (200 * σ) < Real.exp ((⌊ℓ⌋₊ : ℝ) + 1) := heℓ ▸ Real.exp_lt_exp.2 hlt
    rw [div_lt_iff₀ h200] at h2
    linarith

/-- **The cut at `T + 7` below `x`**: `c_{T+7} = ⌊exp(e^{T+7})⌋ + 1 ≤ ⌊x⌋ + 1` for `x > 1` and
`T + 7 ≤ log log x`. -/
theorem scaleCut_add_seven_le {x : ℝ} {T : ℕ} (hx : 1 < x)
    (hT : (T : ℝ) + 7 ≤ Real.log (Real.log x)) :
    scaleCut ((T : ℝ) + 7) ≤ ⌊x⌋₊ + 1 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have h1 : Real.exp ((T : ℝ) + 7) ≤ Real.log x := by
    calc Real.exp ((T : ℝ) + 7) ≤ Real.exp (Real.log (Real.log x)) := Real.exp_le_exp.2 hT
      _ = Real.log x := Real.exp_log hL
  have hb : blockScale ((T : ℝ) + 7) 0 ≤ x := by
    rw [blockScale, Nat.cast_zero, zero_add]
    calc Real.exp (Real.exp ((T : ℝ) + 7)) ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 h1
      _ = x := Real.exp_log hx0
  have := Nat.floor_mono hb
  unfold scaleCut
  omega

/-- **The error term's `Λ^{q/2}`, absorbed**: `e^{-qΛ}Λ^{q/2} ≤ e^{-(1376/1377)qΛ}` for `Λ ≥ 6000`
and `q ≥ 0`, since `log Λ/Λ ≤ log 6000/6000 ≤ 2/1377` (`Real.log_div_self_antitoneOn`). -/
theorem exp_neg_mul_rpow_le_of_six_thousand {Λ q : ℝ} (hΛ : 6000 ≤ Λ) (hq : 0 ≤ q) :
    Real.exp (-(q * Λ)) * Λ ^ (q / 2) ≤ Real.exp (-(1376 / 1377 * (q * Λ))) := by
  have hΛ0 : 0 < Λ := by linarith
  have he : Real.exp 1 ≤ 6000 := by
    have := Real.exp_one_lt_d9
    linarith
  have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hΛ)) hΛ
  simp only at hanti
  have h6 : Real.log 6000 ≤ 8.71 := by interval_decide (trust := kernel)
  have hlog : Real.log Λ ≤ 2 / 1377 * Λ := by
    rw [div_le_iff₀ hΛ0] at hanti
    have h1 : Real.log 6000 / 6000 ≤ 2 / 1377 := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    calc Real.log Λ ≤ Real.log 6000 / 6000 * Λ := hanti
      _ ≤ 2 / 1377 * Λ := mul_le_mul_of_nonneg_right h1 hΛ0.le
  have hq2 := mul_le_mul_of_nonneg_left hlog hq
  rw [Real.rpow_def_of_pos hΛ0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

/-- **The range `x ≥ exp(e^{2100})`**: `Λ = log log x ≥ 2100`, `log x ≥ e^{2100}`,
`x ≥ RMF.windowThreshold` (`≤ exp(e^{1621})`, `RMF.windowThreshold_le`) and `x ≥ e^{405}`. -/
theorem loglog_facts_of_2100 {x : ℝ} (hx : Real.exp (Real.exp 2100) ≤ x) :
    2100 ≤ Real.log (Real.log x) ∧ Real.exp 2100 ≤ Real.log x ∧ windowThreshold ≤ x
      ∧ Real.exp 405 ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 2100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hΛ : 2100 ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL)).2 hL
  have h1621 : Real.exp (Real.exp 1621) ≤ x :=
    le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hx
  have h405 : (405 : ℝ) ≤ Real.exp 2100 := by
    have := Real.add_one_le_exp (2100 : ℝ)
    linarith
  exact ⟨hΛ, hL, windowThreshold_le.trans h1621, le_trans (Real.exp_le_exp.2 h405) hx⟩

/-- `x ≥ exp(e^c)` for `x > 1` and `log log x ≥ c`. -/
theorem exp_exp_le_of_le_loglog {x c : ℝ} (hx : 1 < x) (h : c ≤ Real.log (Real.log x)) :
    Real.exp (Real.exp c) ≤ x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have h1 : Real.exp c ≤ Real.log x := (Real.le_log_iff_exp_le hL).1 h
  exact (Real.le_log_iff_exp_le (by linarith)).1 h1

/-- **The error term's `Λ^{q/2}`, absorbed from `Λ ≥ 2100`**: `e^{-qΛ}Λ^{q/2} ≤ e^{-(545/546)qΛ}`
for `q ≥ 0`, since `log Λ/Λ ≤ log 2100/2100 ≤ 2/546` (`Real.log_div_self_antitoneOn`). -/
theorem exp_neg_mul_rpow_le_of_2100 {Λ q : ℝ} (hΛ : 2100 ≤ Λ) (hq : 0 ≤ q) :
    Real.exp (-(q * Λ)) * Λ ^ (q / 2) ≤ Real.exp (-(545 / 546 * (q * Λ))) := by
  have hΛ0 : 0 < Λ := by linarith
  have he : Real.exp 1 ≤ 2100 := by
    have := Real.exp_one_lt_d9
    linarith
  have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hΛ)) hΛ
  simp only at hanti
  have h21 : Real.log 2100 ≤ 7.69 := by interval_decide (trust := kernel)
  have hlog : Real.log Λ ≤ 2 / 546 * Λ := by
    rw [div_le_iff₀ hΛ0] at hanti
    have h1 : Real.log 2100 / 2100 ≤ 2 / 546 := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    calc Real.log Λ ≤ Real.log 2100 / 2100 * Λ := hanti
      _ ≤ 2 / 546 * Λ := mul_le_mul_of_nonneg_right h1 hΛ0.le
  have hq2 := mul_le_mul_of_nonneg_left hlog hq
  rw [Real.rpow_def_of_pos hΛ0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

/-- **`q log q` above its tangent at `t`**: `t log t + (1 + log t)(q - t) ≤ q log q` for
`t, q > 0` (`Real.one_sub_inv_le_log_of_pos` at `q/t`). -/
theorem mul_log_ge_tangent {t q : ℝ} (ht : 0 < t) (hq : 0 < q) :
    t * Real.log t + (1 + Real.log t) * (q - t) ≤ q * Real.log q := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hq ht)
  rw [Real.log_div hq.ne' ht.ne', inv_div] at h
  have h2 : q * (1 - t / q) ≤ q * (Real.log q - Real.log t) := mul_le_mul_of_nonneg_left h hq.le
  have h3 : q * (1 - t / q) = q - t := by field_simp
  rw [h3] at h2
  linarith

/-! ### Cell bounds for `q log q`, `q(1 - 2q)` and `c₃` -/

/-- `q log q ≥ b log b` for `0 < q ≤ b ≤ e⁻¹`: the tangent at `b`, where `1 + log b ≤ 0`. -/
theorem mul_log_ge_of_le_exp_neg_one {q b : ℝ} (hq : 0 < q) (hqb : q ≤ b)
    (hb : b ≤ Real.exp (-1)) :
    b * Real.log b ≤ q * Real.log q := by
  have hb0 : 0 < b := lt_of_lt_of_le hq hqb
  have h := mul_log_ge_tangent hb0 hq
  have hlog : Real.log b ≤ -1 := (Real.log_le_iff_le_exp hb0).2 hb
  have h2 : 0 ≤ (1 + Real.log b) * (q - b) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  linarith

/-- `q log q ≥ -e⁻¹` for `q > 0`: the tangent at `e⁻¹`. -/
theorem neg_exp_neg_one_le_mul_log {q : ℝ} (hq : 0 < q) : -Real.exp (-1) ≤ q * Real.log q := by
  have h := mul_log_ge_tangent (Real.exp_pos (-1)) hq
  rw [Real.log_exp] at h
  linarith

/-- `q log q ≥ a log a` for `e⁻¹ ≤ a ≤ q`: the tangent at `a`, where `1 + log a ≥ 0`. -/
theorem mul_log_ge_of_exp_neg_one_le {a q : ℝ} (ha : Real.exp (-1) ≤ a) (haq : a ≤ q) :
    a * Real.log a ≤ q * Real.log q := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha
  have h := mul_log_ge_tangent ha0 (lt_of_lt_of_le ha0 haq)
  have hlog : -1 ≤ Real.log a := (Real.le_log_iff_exp_le ha0).2 ha
  have h2 : 0 ≤ (1 + Real.log a) * (q - a) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- `q(1 - 2q) ≤ b(1 - 2b)` for `q ≤ b ≤ ¼`: `b(1-2b) - q(1-2q) = (b-q)(1-2(b+q))`. -/
theorem mul_one_sub_two_mul_le_of_le {q b : ℝ} (hqb : q ≤ b) (hb : b ≤ 1 / 4) :
    q * (1 - 2 * q) ≤ b * (1 - 2 * b) := by
  have h : 0 ≤ (b - q) * (1 - 2 * (b + q)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- `q(1 - 2q) ≤ 1/8`. -/
theorem mul_one_sub_two_mul_le_eighth (q : ℝ) : q * (1 - 2 * q) ≤ 1 / 8 := by
  nlinarith [sq_nonneg (q - 1 / 4)]

/-- `q(1 - 2q) ≤ a(1 - 2a)` for `¼ ≤ a ≤ q`: `a(1-2a) - q(1-2q) = (q-a)(2(a+q)-1)`. -/
theorem mul_one_sub_two_mul_le_of_ge {a q : ℝ} (ha : 1 / 4 ≤ a) (haq : a ≤ q) :
    q * (1 - 2 * q) ≤ a * (1 - 2 * a) := by
  have h : 0 ≤ (q - a) * (2 * (a + q) - 1) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **`c₃` on a cell of the ladder of length one**: `c ≤ c3FloorK q 1` for `n_a ≤ 400q ≤ n_b` and
`q < ½`, from `c ≤ c3OneTab n 0` for `n_a ≤ n ≤ n_b`. -/
theorem le_c3FloorK_one_of_cell {c q : ℝ} {na nb : ℕ} (ha : (na : ℝ) ≤ 400 * q)
    (hb : 400 * q ≤ nb) (hq : q < 1 / 2) (h : ∀ n, na ≤ n → n ≤ nb → c ≤ c3OneTab n 0) :
    c ≤ c3FloorK q 1 := by
  rw [c3FloorK, if_pos ⟨rfl, hq⟩]
  exact h _ (Nat.le_floor ha) (Nat.floor_le_of_le hb)

end RMF
