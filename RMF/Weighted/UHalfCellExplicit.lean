/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UHalfHighExplicit

/-!
# The first moment near `q = ½`: the cell theorem past `Λ = 6000`

`RMF.u_half_core`, one cell of `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` for `q ∈ [0.49, ½)`
and `Λ ≥ 6000`, in the variable `w = (1 - 2q)Λ`: the windows of
`RMF/Weighted/UHalfHighExplicit.lean` against `τ⁻¹ = (1 + w)Λ^{q/2 - 1}`, the small pieces
(`RMF.uSmall_half_le`) and the far range. Then the cells' bounds on the high groups' terms in
numerals (`RMF.halfHb_bounded_le`, `RMF.halfHb_large_le`, `RMF.halfHigh_sum_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The assembly's real-variable pieces near `q = ½` -/

lemma uGroups_of_ge {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} {k : ℕ} (hk : 97 ≤ k) :
    uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ k = c₇ := by
  unfold uGroups
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-- `(log Λ + 11)Λ^{-3/4}` decreases past `Λ = 6000`: with `u = Λ^{3/4} ≥ u₀ = 6000^{3/4}`,
`log Λ = (4/3)log u ≤ (4/3)(log u₀ + u/u₀ - 1)`. -/
lemma log_add_mul_rpow_le {Λ : ℝ} (hΛ : 6000 ≤ Λ) :
    (Real.log Λ + 11) * Λ ^ (-(3 / 4 : ℝ))
      ≤ (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hΛ0 : 0 < Λ := by linarith
  set u := Λ ^ (3 / 4 : ℝ) with hu
  set u₀ := (6000 : ℝ) ^ (3 / 4 : ℝ) with hu₀
  have hu₀0 : 0 < u₀ := Real.rpow_pos_of_pos (by norm_num) _
  have huu : u₀ ≤ u := Real.rpow_le_rpow (by norm_num) hΛ (by norm_num)
  have hu0 : 0 < u := lt_of_lt_of_le hu₀0 huu
  have hlogΛ : Real.log Λ = 4 / 3 * Real.log u := by
    rw [hu, Real.log_rpow hΛ0]; ring
  have hlog6 : Real.log 6000 = 4 / 3 * Real.log u₀ := by
    rw [hu₀, Real.log_rpow (by norm_num)]; ring
  have hlu : Real.log u ≤ Real.log u₀ + (u / u₀ - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hu0 hu₀0)
    rw [Real.log_div hu0.ne' hu₀0.ne'] at h
    linarith
  have hneg : Λ ^ (-(3 / 4 : ℝ)) = u⁻¹ := by rw [Real.rpow_neg hΛ0.le]
  have hneg₀ : (6000 : ℝ) ^ (-(3 / 4 : ℝ)) = u₀⁻¹ := by rw [Real.rpow_neg (by norm_num)]
  have hl0 : 0 ≤ 4 / 3 * Real.log u₀ + 11 - 4 / 3 := by
    have : 0 ≤ Real.log u₀ := Real.log_nonneg (by
      rw [hu₀]; exact Real.one_le_rpow (by norm_num) (by norm_num))
    linarith
  rw [hneg, hneg₀, hlogΛ, hlog6, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hu0 hu₀0]
  have e : (Real.log u₀ + (u / u₀ - 1)) * u₀ = Real.log u₀ * u₀ + u - u₀ := by
    rw [add_mul, sub_mul, div_mul_cancel₀ u hu₀0.ne']
    ring
  have h1 := mul_le_mul_of_nonneg_right hlu hu₀0.le
  rw [e] at h1
  have h2 : (4 / 3 * Real.log u₀ + 11 - 4 / 3) * u₀ ≤ (4 / 3 * Real.log u₀ + 11 - 4 / 3) * u :=
    mul_le_mul_of_nonneg_left huu hl0
  linarith

/-- **The tail's factor against `τ⁻¹`**: with `w = (1 - 2q)Λ`, `L ≤ Λ` and `Λ ≥ 6000`,
`(Λ⁻¹ + 1 - 2q)Λ^{1/4}((4/3)(Lθ + 1)^{3/4} + log Λ + 11)
  ≤ (1 + w)((4/3)(θ + 1/6000)^{3/4} + (log 6000 + 11)6000^{-3/4})`. -/
lemma halfTail_factor_le {Λ q L θ : ℝ} (hΛ : 6000 ≤ Λ) (hq : q < 1 / 2) (hL0 : 0 ≤ L)
    (hL : L ≤ Λ) (hθ : 0 ≤ θ) :
    (Λ⁻¹ + (1 - 2 * q)) * Λ ^ (1 / 4 : ℝ)
        * (4 / 3 * (L * θ + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11))
      ≤ (1 + (1 - 2 * q) * Λ) * (4 / 3 * (θ + 1 / 6000) ^ (3 / 4 : ℝ)
        + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ))) := by
  have hΛ0 : 0 < Λ := by linarith
  have hi : Λ⁻¹ * Λ = 1 := inv_mul_cancel₀ hΛ0.ne'
  have hV : (Λ⁻¹ + (1 - 2 * q)) * Λ ^ (1 / 4 : ℝ)
      = (1 + (1 - 2 * q) * Λ) * Λ ^ (-(3 / 4 : ℝ)) := by
    rw [show (1 / 4 : ℝ) = 1 + (-(3 / 4)) by norm_num, Real.rpow_add hΛ0, Real.rpow_one]
    linear_combination Λ ^ (-(3 / 4 : ℝ)) * hi
  have h34 : (L * θ + 1) ^ (3 / 4 : ℝ) ≤ Λ ^ (3 / 4 : ℝ) * (θ + 1 / 6000) ^ (3 / 4 : ℝ) := by
    rw [← Real.mul_rpow hΛ0.le (by linarith)]
    refine Real.rpow_le_rpow (add_nonneg (mul_nonneg hL0 hθ) zero_le_one) ?_ (by norm_num)
    have h1 : L * θ ≤ Λ * θ := mul_le_mul_of_nonneg_right hL hθ
    linarith
  have hc : Λ ^ (-(3 / 4 : ℝ)) * Λ ^ (3 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hΛ0]; norm_num
  have hlog := log_add_mul_rpow_le hΛ
  have hw0 : 0 ≤ 1 + (1 - 2 * q) * Λ := by nlinarith
  have hn0 : 0 ≤ Λ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hΛ0.le _
  have t1 : Λ ^ (-(3 / 4 : ℝ)) * (L * θ + 1) ^ (3 / 4 : ℝ) ≤ (θ + 1 / 6000) ^ (3 / 4 : ℝ) := by
    calc Λ ^ (-(3 / 4 : ℝ)) * (L * θ + 1) ^ (3 / 4 : ℝ)
        ≤ Λ ^ (-(3 / 4 : ℝ)) * (Λ ^ (3 / 4 : ℝ) * (θ + 1 / 6000) ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left h34 hn0
      _ = (θ + 1 / 6000) ^ (3 / 4 : ℝ) := by rw [← mul_assoc, hc, one_mul]
  have key : Λ ^ (-(3 / 4 : ℝ)) * (4 / 3 * (L * θ + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11))
      ≤ 4 / 3 * (θ + 1 / 6000) ^ (3 / 4 : ℝ)
        + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)) := by
    linarith
  rw [hV]
  calc (1 + (1 - 2 * q) * Λ) * Λ ^ (-(3 / 4 : ℝ))
        * (4 / 3 * (L * θ + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11))
      = (1 + (1 - 2 * q) * Λ)
        * (Λ ^ (-(3 / 4 : ℝ)) * (4 / 3 * (L * θ + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hw0

/-- **The geometric factor near `q = ½`**: with `w = (1 - 2q)Λ` and `a = q(1-2q)`,
`(Λ⁻¹ + 1 - 2q)/(1 - e^{-a}) ≤ (1 + w)/(qw) + (Λ⁻¹ + 1 - 2q)(1/2 + a/10)`
(`RMF.inv_one_sub_exp_neg_le_taylor`). -/
lemma geom_half_le {Λ q : ℝ} (hΛ : 0 < Λ) (hq0 : 0 < q) (hq : q < 1 / 2) :
    (Λ⁻¹ + (1 - 2 * q)) / (1 - Real.exp (-(q * (1 - 2 * q))))
      ≤ (1 + (1 - 2 * q) * Λ) / (q * ((1 - 2 * q) * Λ))
        + (Λ⁻¹ + (1 - 2 * q)) * (1 / 2 + q * (1 - 2 * q) / 10) := by
  have hv0 : 0 < 1 - 2 * q := by linarith
  have ha0 : 0 < q * (1 - 2 * q) := mul_pos hq0 hv0
  have ha8 : q * (1 - 2 * q) ≤ 1 / 8 := by linarith [sq_nonneg (q - 1 / 4)]
  have hinv := inv_one_sub_exp_neg_le_taylor ha0 ha8
  have hV0 : 0 ≤ Λ⁻¹ + (1 - 2 * q) := by have := inv_pos.2 hΛ; linarith
  rw [div_eq_mul_inv]
  calc (Λ⁻¹ + (1 - 2 * q)) * (1 - Real.exp (-(q * (1 - 2 * q))))⁻¹
      ≤ (Λ⁻¹ + (1 - 2 * q)) * (1 / (q * (1 - 2 * q)) + 1 / 2 + q * (1 - 2 * q) / 10) :=
        mul_le_mul_of_nonneg_left hinv hV0
    _ = _ := by
        field_simp
        ring

/-- The geometric factor on a cell: `≤ 1/q_l + 1/(q_l w_l) + V_b(1/2 + a₁/10)`. -/
lemma geom_half_le_of {Λ q ql wl a₁ Vb : ℝ} (hΛ : 0 < Λ) (hql : 0 < ql) (hqlq : ql ≤ q)
    (hq : q < 1 / 2) (hwl0 : 0 < wl) (hwl : wl ≤ (1 - 2 * q) * Λ)
    (ha₁ : q * (1 - 2 * q) ≤ a₁) (hVb : Λ⁻¹ + (1 - 2 * q) ≤ Vb) :
    (Λ⁻¹ + (1 - 2 * q)) / (1 - Real.exp (-(q * (1 - 2 * q))))
      ≤ 1 / ql + 1 / (ql * wl) + Vb * (1 / 2 + a₁ / 10) := by
  have hq0 : 0 < q := lt_of_lt_of_le hql hqlq
  have hv0 : 0 < 1 - 2 * q := by linarith
  have hw0 : 0 < (1 - 2 * q) * Λ := mul_pos hv0 hΛ
  refine le_trans (geom_half_le hΛ hq0 hq) ?_
  have e : (1 + (1 - 2 * q) * Λ) / (q * ((1 - 2 * q) * Λ))
      = 1 / (q * ((1 - 2 * q) * Λ)) + 1 / q := by
    field_simp
  have t1 : 1 / (q * ((1 - 2 * q) * Λ)) ≤ 1 / (ql * wl) :=
    one_div_le_one_div_of_le (mul_pos hql hwl0) (mul_le_mul hqlq hwl hwl0.le hq0.le)
  have t2 : 1 / q ≤ 1 / ql := one_div_le_one_div_of_le hql hqlq
  have hV0 : 0 ≤ Λ⁻¹ + (1 - 2 * q) := by have := inv_pos.2 hΛ; linarith
  have ha0 : 0 ≤ q * (1 - 2 * q) := (mul_pos hq0 hv0).le
  have t3 : (Λ⁻¹ + (1 - 2 * q)) * (1 / 2 + q * (1 - 2 * q) / 10) ≤ Vb * (1 / 2 + a₁ / 10) :=
    mul_le_mul hVb (by linarith) (by linarith) (by linarith)
  rw [e]
  linarith

/-- One high group against `τ⁻¹`: with `y = qw`, `a k = y(k/Λ)`, so
`((1 + w)/y)(e^{-ak} - e^{-ak'}) ≤ (1 + w)(e^{-y s_l} - e^{-y s_h})/y` for `s_l ≤ k/Λ`,
`k'/Λ ≤ s_h` (`RMF.exp_diff_div_mono`). -/
lemma high_term_le {Λ q k k' sl sh : ℝ} (hΛ : 0 < Λ) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hsl : sl ≤ k / Λ) (hsh : k' / Λ ≤ sh) :
    (1 + (1 - 2 * q) * Λ) / (q * ((1 - 2 * q) * Λ))
        * (Real.exp (-(q * (1 - 2 * q) * k)) - Real.exp (-(q * (1 - 2 * q) * k')))
      ≤ (1 + (1 - 2 * q) * Λ) * ((Real.exp (-(q * ((1 - 2 * q) * Λ) * sl))
          - Real.exp (-(q * ((1 - 2 * q) * Λ) * sh))) / (q * ((1 - 2 * q) * Λ))) := by
  have hv0 : 0 < 1 - 2 * q := by linarith
  have hy0 : 0 < q * ((1 - 2 * q) * Λ) := mul_pos hq0 (mul_pos hv0 hΛ)
  have ek : ∀ m : ℝ, q * (1 - 2 * q) * m = q * ((1 - 2 * q) * Λ) * (m / Λ) := fun m => by
    field_simp
  rw [ek k, ek k']
  have h := exp_diff_div_mono hy0 hsl hsh
  have hw0 : 0 ≤ 1 + (1 - 2 * q) * Λ := by nlinarith
  calc (1 + (1 - 2 * q) * Λ) / (q * ((1 - 2 * q) * Λ))
        * (Real.exp (-(q * ((1 - 2 * q) * Λ) * (k / Λ)))
          - Real.exp (-(q * ((1 - 2 * q) * Λ) * (k' / Λ))))
      = (1 + (1 - 2 * q) * Λ) * ((Real.exp (-(q * ((1 - 2 * q) * Λ) * (k / Λ)))
          - Real.exp (-(q * ((1 - 2 * q) * Λ) * (k' / Λ)))) / (q * ((1 - 2 * q) * Λ))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hw0

/-- The high groups' lower ends in `k/Λ`: `1/4 - 1/6000`, then `0.99(1 - θ_g) - 1/6000`. -/
noncomputable def halfSigLo (g : ℕ) : ℝ :=
  if g = 0 then 1 / 4 - 1 / 6000 else 99 / 100 * (1 - halfTheta g) - 1 / 6000

/-- The high groups' upper ends in `k/Λ`: `1 - θ_g`. -/
noncomputable def halfSigHi (g : ℕ) : ℝ := 1 - halfTheta g

/-- `σ_l(g) ≤ k_g/Λ` past `Λ = 6000`. -/
lemma halfSigLo_le {x : ℝ} (hΛ : 6000 ≤ Real.log (Real.log x)) (g : ℕ) :
    halfSigLo g ≤ (halfKb x g : ℝ) / Real.log (Real.log x) := by
  obtain ⟨hL1, -⟩ := halfLpp_bounds hΛ
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  have hi : 1 / Real.log (Real.log x) ≤ 1 / 6000 := one_div_le_one_div_of_le (by norm_num) hΛ
  rw [le_div_iff₀ hΛ0]
  unfold halfSigLo
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · rw [if_pos rfl]
    have h := Nat.lt_floor_add_one (Real.log (Real.log x) / 4)
    have e : (halfKb x 0 : ℝ) = ⌊Real.log (Real.log x) / 4⌋₊ := by
      unfold halfKb; rw [if_pos rfl]
    have h6 : (1 / 6000 : ℝ) * Real.log (Real.log x) ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (by norm_num)]; linarith
    rw [e]
    linarith
  · rw [if_neg hg.ne']
    have h := halfKb_ge (x := x) g hg
    have hθ1 := halfTheta_le g
    have h1 : 99 / 100 * Real.log (Real.log x) * (1 - halfTheta g)
        ≤ halfLpp x * (1 - halfTheta g) := mul_le_mul_of_nonneg_right hL1 (by linarith)
    have h6 : (1 / 6000 : ℝ) * Real.log (Real.log x) ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (by norm_num)]; linarith
    nlinarith

/-- `k_g/Λ ≤ σ_h(g)` for `g ≥ 1`. -/
lemma le_halfSigHi {x : ℝ} (hΛ : 6000 ≤ Real.log (Real.log x)) {g : ℕ} (hg : 1 ≤ g) :
    (halfKb x g : ℝ) / Real.log (Real.log x) ≤ halfSigHi g := by
  obtain ⟨-, hL2⟩ := halfLpp_bounds hΛ
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  obtain ⟨h, -⟩ := halfKb_le hΛ hg
  have hθ1 := halfTheta_le g
  rw [div_le_iff₀ hΛ0]
  unfold halfSigHi
  have := mul_le_mul_of_nonneg_right hL2 (by linarith : (0 : ℝ) ≤ 1 - halfTheta g)
  linarith

lemma halfRho_mono : Monotone halfRho := fun g g' h => by
  unfold halfRho
  refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  exact Real.log_le_log (by have := halfTheta_pos g'; positivity)
    (mul_le_mul_of_nonneg_left (halfTheta_anti h) (by norm_num))

lemma halfRho_nonneg (g : ℕ) : 0 ≤ halfRho g := (Real.exp_pos _).le

/-- `ρ_8 = (0.99θ_8)^{-1/4} ≤ 2.994`. -/
lemma halfRho_eight_le : halfRho 8 ≤ 1497 / 500 := by
  unfold halfRho halfTheta
  rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 8) = 1948617 / 156250000 by norm_num]
  interval_decide (trust := kernel)

/-- The tail's constant: `(4/3)(θ_8 + 1/6000)^{3/4} + (log 6000 + 11)6000^{-3/4} ≤ 0.0797`. -/
lemma halfT8_le : 4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
    + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 797 / 10000 := by
  unfold halfTheta
  rw [show (3 / 4 * (3 / 5) ^ 8 + 1 / 6000 : ℝ) = 239321 / 18750000 by norm_num,
    rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
  interval_decide (trust := kernel)

set_option maxHeartbeats 1000000 in
-- five bounds, each by a named lemma
/-- **The small pieces and the central window near `q = ½`**: for `Λ ≥ 6000`,
`q ∈ [q_l, ½) ⊆ [0.49, ½)`, `a = q(1-2q) ≤ a₁ ≤ 1/8` and `w = (1 - 2q)Λ ≥ w_l ≥ 1/q_l - 1`,
(PF) at `y`, the central window (`C_c ≤ 51Λ`), the smooth tail and the reduction's error are
`≤ τ·((1 + w_l)e^{-q_l w_l}(6000^{a₁-3/4} + C_R'√51·6000^{a₁-1/4}) + 1/1000)`
(`RMF.uSmall_jensen_le` without an upper end: the tail and the error beat
`Λ^{q/2} ≤ e^{qΛ/800}`). -/
theorem uSmall_half_le {x q ql a₁ wl : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hql : 49 / 100 ≤ ql) (hqlq : ql ≤ q) (hq : q < 1 / 2)
    (ha₁ : q * (1 - 2 * q) ≤ a₁) (ha₁8 : a₁ ≤ 1 / 8)
    (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl) :
    uPFyAt q (halfY x) + halfTail x ^ q
        + smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x))
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
      ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ * Real.log (Real.log x) ^ (-(q / 2))
        * ((1 + wl) * Real.exp (-(ql * wl))
            * (Real.exp ((a₁ - 3 / 4) * Real.log 6000)
              + Real.exp (ql * Real.log (33885 / 100000)) * Real.exp (1 / 2 * Real.log 51)
                * Real.exp ((a₁ - 1 / 4) * Real.log 6000))
          + 1 / 1000) := by
  obtain ⟨hx0, hL, hΛ110, -, -, -⟩ := half_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  obtain ⟨hlly, hly⟩ := halfY_loglog_le hx
  have hll := halfY_loglog_ge_sub hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hq49 : 49 / 100 ≤ q := le_trans hql hqlq
  have hq0 : 0 < q := by linarith
  have hq5 : q ≤ 1 / 2 := hq.le
  have hql0 : 0 < ql := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 ≤ a := mul_nonneg hq0.le (by linarith)
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
  have hpf0 := pf_tau_le (Λl := 6000) (qu := 1 / 2) (c := 0) (by norm_num) hΛ hql0 hqlq hq5
    (by norm_num) ha₁ le_rfl (by linarith) hwl hwl1
  have hpf1 := pf_tau_le (Λl := 6000) (qu := 1 / 2) (c := 1) (by norm_num) hΛ hql0 hqlq hq5
    (by norm_num) ha₁ zero_le_one (by linarith) hwl hwl1
  rw [zero_mul, Real.rpow_zero, mul_one] at hpf0
  have e0 : (6000 : ℝ) ^ (a₁ + (0 + 1 / 2) * (1 / 2) - 1)
      = Real.exp ((a₁ - 3 / 4) * Real.log 6000) := by
    rw [rpow_eq_exp_mul_log (by norm_num)]; congr 1; ring
  have e1 : (6000 : ℝ) ^ (a₁ + (1 + 1 / 2) * (1 / 2) - 1)
      = Real.exp ((a₁ - 1 / 4) * Real.log 6000) := by
    rw [rpow_eq_exp_mul_log (by norm_num)]; congr 1; ring
  rw [e0] at hpf0
  rw [e1] at hpf1
  set D := (1 + wl) * Real.exp (-(ql * wl)) with hDdef
  -- (PF) at `y`
  have hy : uPFyAt q (halfY x) * R ≤ D * Real.exp ((a₁ - 3 / 4) * Real.log 6000) :=
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
      ≤ Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) := by
    have h1 := uCen_le hx hq0.le
    rw [← hΛdef] at h1
    have h51 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ≤ 51 * Λ := by linarith
    calc uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q ≤ (51 * Λ) ^ q :=
          Real.rpow_le_rpow hC0 h51 hq0.le
      _ = (51 : ℝ) ^ q * Λ ^ (1 * q) := by rw [Real.mul_rpow (by norm_num) hΛ0.le, one_mul]
      _ ≤ (51 : ℝ) ^ (1 / 2 : ℝ) * Λ ^ (1 * q) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq5) (Real.rpow_nonneg hΛ0.le _)
      _ = Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  have hPFc0 : 0 ≤ uPFcAt q (halfSigma x) (halfY x) := by
    unfold uPFcAt
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
  have hcen : CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
        * uPFcAt q (halfSigma x) (halfY x)) * R
      ≤ D * (Real.exp (ql * Real.log (33885 / 100000)) * Real.exp (1 / 2 * Real.log 51)
        * Real.exp ((a₁ - 1 / 4) * Real.log 6000)) := by
    have hCq0 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q := Real.rpow_nonneg hC0 q
    have h1 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
        ≤ Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ))) :=
      mul_le_mul hCen hPFc hPFc0 (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hΛ0.le _))
    have h2 : Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ)))
          * R
        = Real.exp (1 / 2 * Real.log 51)
          * (Real.exp (-(a * (Λ - Real.log Λ))) * Λ ^ (1 * q) * R) := by
      ring
    have h3 := mul_le_mul_of_nonneg_left hpf1 (Real.exp_pos (1 / 2 * Real.log 51)).le
    calc CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
          * uPFcAt q (halfSigma x) (halfY x)) * R
        ≤ Real.exp (ql * Real.log (33885 / 100000))
          * (Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ)))
            * R) := by
          rw [mul_assoc]
          refine mul_le_mul hCRq (mul_le_mul_of_nonneg_right h1 hR0.le)
            (mul_nonneg (mul_nonneg hCq0 hPFc0) hR0.le) (Real.exp_pos _).le
      _ ≤ Real.exp (ql * Real.log (33885 / 100000))
          * (Real.exp (1 / 2 * Real.log 51)
            * (D * Real.exp ((a₁ - 1 / 4) * Real.log 6000))) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = _ := by ring
  -- the tail and the error: `R ≤ Λ^{q/2} ≤ e^{qΛ/800}` against their decay
  have hV1 : V ≤ 1 := by
    have : Λ⁻¹ ≤ 1 / 6000 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΛ
    linarith
  have hΛq : Λ ^ (q / 2) ≤ Real.exp (q * Λ / 800) := by
    rw [rpow_eq_exp_mul_log hΛ0]
    refine Real.exp_le_exp.2 ?_
    have hl := log_le_div_four_hundred (by linarith : (4000 : ℝ) ≤ Λ)
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ q / 2)
    linarith
  have hR1 : R ≤ Real.exp (q * Λ / 800) := by
    have h0 : 0 ≤ Λ ^ (q / 2) := Real.rpow_nonneg hΛ0.le _
    rw [hRdef]
    calc V * Λ ^ (q / 2) ≤ 1 * Λ ^ (q / 2) := mul_le_mul_of_nonneg_right hV1 h0
      _ ≤ _ := by rw [one_mul]; exact hΛq
  have h700 : Real.exp (-700) ≤ 1 / 2000 := by
    have h8 : Real.exp (-8) ≤ 1 / 2000 := by interval_decide (trust := kernel)
    exact le_trans (Real.exp_le_exp.2 (by norm_num)) h8
  have hT := halfTail_le_decay hx
  rw [← hΛdef] at hT
  have hT0 : 0 ≤ halfTail x := by
    unfold halfTail
    exact Finset.sum_nonneg fun m _ => by positivity
  have hTR : halfTail x ^ q * R ≤ 1 / 2000 := by
    have hTq : halfTail x ^ q ≤ Real.exp ((142 / 100 - 4995 / 10000 * Λ) * q) := by
      calc halfTail x ^ q ≤ Real.exp (142 / 100 - 4995 / 10000 * Λ) ^ q :=
            Real.rpow_le_rpow hT0 hT hq0.le
        _ = _ := by rw [← Real.exp_mul]
    have h1 := mul_le_mul hTq hR1 hR0.le (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    refine le_trans h1 (le_trans (Real.exp_le_exp.2 ?_) h700)
    have hb : 142 / 100 - 4995 / 10000 * Λ + Λ / 800 ≤ -2988 := by linarith
    have := mul_le_mul_of_nonneg_left hb hq0.le
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
  have hER : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q * R ≤ 1 / 2000 := by
    have hEq : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
        ≤ Real.exp (-(Λ / 4) * q) := by
      calc smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
          ≤ Real.exp (-(Λ / 4)) ^ q := Real.rpow_le_rpow hE0 hE1 hq0.le
        _ = _ := by rw [← Real.exp_mul]
    have h1 := mul_le_mul hEq hR1 hR0.le (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    refine le_trans h1 (le_trans (Real.exp_le_exp.2 ?_) h700)
    have hqΛ : 49 / 100 * 6000 ≤ q * Λ := mul_le_mul hq49 hΛ (by norm_num) hq0.le
    linarith
  -- together
  refine le_inv_mul_of_mul_le hR0 ?_
  have e : (uPFyAt q (halfY x) + halfTail x ^ q
        + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
          * uPFcAt q (halfSigma x) (halfY x))
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q) * R
      = uPFyAt q (halfY x) * R
        + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
          * uPFcAt q (halfSigma x) (halfY x)) * R
        + halfTail x ^ q * R + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q * R := by
    ring
  rw [e]
  linarith [hy, hcen, hTR, hER]

/-- The high groups' ends are ordered: `σ_l(g) ≤ σ_h(g + 1)`. -/
lemma halfSigLo_le_hi (g : ℕ) : halfSigLo g ≤ halfSigHi (g + 1) := by
  unfold halfSigLo halfSigHi
  have h1 := halfTheta_anti (Nat.le_succ g)
  have h2 := halfTheta_le (g + 1)
  have h3 := halfTheta_le g
  split_ifs <;> linarith

/-- A window's chaos constant is nonnegative. -/
lemma winChaos_const_zero_nonneg {c : WinChaos} (hv : c.Valid) (q : ℝ) : 0 ≤ c.const 0 q 1 := by
  have hl := hv.lam
  unfold WinChaos.const shiftMomentConst
  exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)

/-! ### The cell theorem near `q = ½` -/

set_option maxHeartbeats 16000000 in
-- the assembly and its pieces
/-- **One cell near `q = ½` past `Λ = 6000`**: for `q ∈ [q_l, ½)`, `q_l ≥ 0.49`, with
`w = (1 - 2q)Λ ≥ w_l ≥ 1/q_l - 1` and `a = q(1-2q) ≤ a₁ ≤ 1/8`, the windows' parameters of
`RMF.uLow_half_le` and `RMF.uHigh_groups_le` at `q ∈ [0.49, ½]`, bounds `E_t ≤ e^{-qw/4}`,
`Λ⁻¹ + 1 - 2q ≤ V_b`, `H_b`, `T_b`, `E_0` on the high groups' terms, and the certificate `hfin`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`. -/
theorem u_half_core {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql a₁ wl Vb Et Hb Tb E0b : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hql : 49 / 100 ≤ ql) (hqlq : ql ≤ q) (hq : q < 1 / 2)
    (hwl0 : 0 < wl) (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl)
    (ha₁ : q * (1 - 2 * q) ≤ a₁) (ha₁8 : a₁ ≤ 1 / 8)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} (hv₁ : c₁.Valid) (hv₂ : c₂.Valid)
    (hv₃ : c₃.Valid) (hv₄ : c₄.Valid) (hv₅ : c₅.Valid) (hv₆ : c₆.Valid) (hv₇ : c₇.Valid)
    (hN₁ : c₁.N ≤ 2980) (hN₂ : c₂.N ≤ 2980) (hN₃ : c₃.N ≤ 2980) (hN₄ : c₄.N ≤ 2980)
    (hN₅ : c₅.N ≤ 2980) (hN₆ : c₆.N ≤ 2980) (hN₇ : c₇.N ≤ 2980)
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ G₁ G₂ G₃ G₄ G₅ G₆ G₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇ bH : ℝ}
    (hA₁ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      c₁.const E₀ q K ≤ A₁)
    (hA₂ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      c₂.const E₀ q K ≤ A₂)
    (hA₃ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      c₃.const E₀ q K ≤ A₃)
    (hA₄ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      c₄.const E₀ q K ≤ A₄)
    (hA₅ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      c₅.const E₀ q K ≤ A₅)
    (hA₆ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      c₆.const E₀ q K ≤ A₆)
    (hA₇ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      c₇.const E₀ q K ≤ A₇)
    (hG₁ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 4 y ^ (1 / 2 : ℝ) ≤ G₁)
    (hG₂ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 5 y ^ (1 / 2 : ℝ) ≤ G₂)
    (hG₃ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 6 y ^ (1 / 2 : ℝ) ≤ G₃)
    (hG₄ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 7 y ^ (1 / 2 : ℝ) ≤ G₄)
    (hG₅ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 31 y ^ (1 / 2 : ℝ) ≤ G₅)
    (hG₆ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 61 y ^ (1 / 2 : ℝ) ≤ G₆)
    (hG₇ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 97 y ^ (1 / 2 : ℝ) ≤ G₇)
    (hb₁ : G₁ * A₁ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₁)
    (hb₂ : G₂ * A₂ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₂)
    (hb₃ : G₃ * A₃ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₃)
    (hb₄ : G₄ * A₄ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₄)
    (hb₅ : G₅ * A₅ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₅)
    (hb₆ : G₆ * A₆ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₆)
    (hb₇ : G₇ * A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10763 / 10000) ≤ b₇)
    (h12 : b₂ ≤ b₁) (h23 : b₃ ≤ b₂) (h34 : b₄ ≤ b₃) (h45 : b₅ ≤ b₄) (h56 : b₆ ≤ b₅)
    (h67 : b₇ ≤ b₆) (hN : (c₇.N : ℝ) ≤ (A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 4)
    (hbH : G₇ * A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ bH)
    (hEt : Et ≤ Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) / 4)))
    (hVb : (Real.log (Real.log x))⁻¹ + (1 - 2 * q) ≤ Vb)
    (hHb : ∑ g ∈ Finset.range 8, halfRho (g + 1)
        * ((1 + (1 - 2 * q) * Real.log (Real.log x))
          * ((Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo g))
            - Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigHi (g + 1))))
            / (q * ((1 - 2 * q) * Real.log (Real.log x))))) ≤ Hb)
    (hTb : (1 + (1 - 2 * q) * Real.log (Real.log x))
        * Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo 8)) ≤ Tb)
    (hE0 : Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo 0)) ≤ E0b)
    (hfin : (1 + wl) * Real.exp (-(ql * wl))
        * (Real.exp ((a₁ - 3 / 4) * Real.log 6000)
          + Real.exp (ql * Real.log (33885 / 100000)) * Real.exp (1 / 2 * Real.log 51)
            * Real.exp ((a₁ - 1 / 4) * Real.log 6000))
      + 1 / 1000
      + Real.exp (ql * Real.log (33885 / 100000)) * Vb * Real.exp (3 / 4 * Real.log 880)
      + Real.exp (ql * Real.log (33885 / 100000))
        * (1 / ql + 1 / (ql * wl) + Vb * (1 / 2 + a₁ / 10))
        * (b₁ - (b₁ - b₂) * Real.exp (-(5 * a₁)) - (b₂ - b₃) * Real.exp (-(6 * a₁))
          - (b₃ - b₄) * Real.exp (-(7 * a₁)) - (b₄ - b₅) * Real.exp (-(31 * a₁))
          - (b₅ - b₆) * Real.exp (-(61 * a₁)) - (b₆ - b₇) * Real.exp (-(97 * a₁)) - b₇ * Et)
      + Real.exp (ql * Real.log (33885 / 100000)) * bH
        * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000)) ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hL1, hL2⟩ := halfLpp_bounds hΛ
  have hq49 : 49 / 100 ≤ q := le_trans hql hqlq
  have hq0 : 0 < q := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  have hql0 : 0 < ql := by linarith
  have hΛ0' : 0 < Real.log (Real.log x) := by linarith
  have hLpp0 : 0 ≤ halfLpp x := by linarith
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  have hA₇0 : 0 ≤ A₇ := le_trans (winChaos_const_zero_nonneg hv₇ q)
    (hA₇ 0 le_rfl (by norm_num) 1 zero_le_one (Real.one_le_exp (by norm_num)))
  have hG₇0 : 0 ≤ G₇ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by norm_num) 97 (halfY x))) _)
    (hG₇ _ hly)
  -- the pieces, before abbreviating
  have hP7 : ∀ k, 97 ≤ k → uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ k = c₇ := fun k hk => uGroups_of_ge hk
  have hPv := uGroups_valid hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇
  have hasm := integral_rpow_weightedRademacherSum_le_u_assembly hX hx hq0 hq.le hPv uFarP_valid
    (⌈Real.log (Real.log (Real.log x))⌉₊ + 4)
  have hsmall := uSmall_half_le hx hΛ hql hqlq hq ha₁ ha₁8 hwl hwl1
  have hfarb := uFarBound_uFarP_le hx (by linarith) hq0 hq.le
  have hK4 : (⌊Real.log (Real.log x) / 4⌋₊ : ℝ) ≤ Real.log (Real.log x) / 4 :=
    Nat.floor_le (by linarith)
  have hEt' : Et ≤ Real.exp (-(q * (1 - 2 * q) * ⌊Real.log (Real.log x) / 4⌋₊)) := by
    refine le_trans hEt (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left hK4 (mul_pos hq0 hv0).le
    linarith
  have hlow := uLow_half_le (ql := 49 / 100) (qu := 1 / 2) hx (by linarith) (by norm_num) hq49
    hq.le (by norm_num) hq ha₁ hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇ hN₁ hN₂ hN₃ hN₄ hN₅ hN₆ hN₇ hA₁ hA₂
    hA₃ hA₄ hA₅ hA₆ hA₇ hG₁ hG₂ hG₃ hG₄ hG₅ hG₆ hG₇ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇ h12 h23 h34 h45
    h56 h67 hEt'
  have e4 : Real.exp (-(4 * ((1 / 2 : ℝ) * (1 - 2 * (1 / 2))))) = 1 := by norm_num
  rw [e4, mul_one] at hlow
  have hhigh := uHigh_groups_le (ql := 49 / 100) (qu := 1 / 2) hx hΛ hq0 hq hq49 hq.le le_rfl
    hv₇ hP7 hA₇ hG₇ hN
  have htail := uHigh_tail_le (ql := 49 / 100) (qu := 1 / 2) hx hΛ hq0 hq hq49 hq.le le_rfl
    hv₇ hP7 hA₇ hG₇ hN
  -- the windows' ranges
  have hK0 : halfKb x 0 = ⌊Real.log (Real.log x) / 4⌋₊ := by unfold halfKb; rw [if_pos rfl]
  have hmono := halfKb_mono hΛ
  have hJ := floor_halfLpp_lt_tenJ hx hΛ
  obtain ⟨-, hk8L⟩ := halfKb_le hΛ (g := 8) (by norm_num)
  have h4K : 4 ≤ halfKb x 0 := by rw [hK0]; exact Nat.le_floor (by push_cast; linarith)
  have hsplit : ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
      = ∑ k ∈ Finset.Ico 4 ⌊Real.log (Real.log x) / 4⌋₊,
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
        + ∑ k ∈ Finset.Ico (halfKb x 0) (halfKb x 8),
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
        + ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x),
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k := by
    rw [← hK0, Finset.sum_Ico_consecutive _ h4K (hmono (Nat.zero_le 8)),
      Finset.sum_Ico_consecutive _ (le_trans h4K (hmono (Nat.zero_le 8))) (by omega)]
  -- the high groups against `τ⁻¹`, term by term
  have hterm : ∀ g, g < 8 →
      (1 + (1 - 2 * q) * Real.log (Real.log x)) / (q * ((1 - 2 * q) * Real.log (Real.log x)))
        * (Real.exp (-(q * (1 - 2 * q) * halfKb x g))
          - Real.exp (-(q * (1 - 2 * q) * halfKb x (g + 1))))
      ≤ (1 + (1 - 2 * q) * Real.log (Real.log x))
        * ((Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo g))
          - Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigHi (g + 1))))
          / (q * ((1 - 2 * q) * Real.log (Real.log x)))) := fun g _ =>
    high_term_le hΛ0' hq0 hq (halfSigLo_le hΛ g) (le_halfSigHi hΛ (by omega))
  have hekb : ∀ g, q * (1 - 2 * q) * (halfKb x g : ℝ)
      = q * ((1 - 2 * q) * Real.log (Real.log x)) * ((halfKb x g : ℝ) / Real.log (Real.log x)) :=
    fun g => by field_simp
  have hwpos : 0 ≤ q * ((1 - 2 * q) * Real.log (Real.log x)) :=
    (mul_pos hq0 (mul_pos hv0 hΛ0')).le
  have hE0' : Real.exp (-(q * (1 - 2 * q) * halfKb x 0)) ≤ E0b := by
    refine le_trans (Real.exp_le_exp.2 ?_) hE0
    rw [hekb 0]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (halfSigLo_le hΛ 0) hwpos)
  have hTb' : (1 + (1 - 2 * q) * Real.log (Real.log x))
      * Real.exp (-(q * (1 - 2 * q) * halfKb x 8)) ≤ Tb := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (add_nonneg zero_le_one (mul_pos hv0 hΛ0').le)) hTb
    rw [hekb 8]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (halfSigLo_le hΛ 8) hwpos)
  have hgeo := geom_half_le_of hΛ0' hql0 hqlq hq hwl0 hwl ha₁ hVb
  have hQ := geom_half_le hΛ0' hq0 hq
  have htf := halfTail_factor_le (L := halfLpp x) hΛ hq (by linarith) hL2 (halfTheta_pos 8).le
  have hρ8 := halfRho_eight_le
  have hT8 := halfT8_le
  -- abbreviations
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := hΛ0'
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 < a := mul_pos hq0 hv0
  set w := (1 - 2 * q) * Λ with hwdef
  have hw0 : 0 < w := mul_pos hv0 hΛ0
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛ0; linarith
  have hΛq0 : 0 < Λ ^ (-(q / 2)) := Real.rpow_pos_of_pos hΛ0 _
  set τ := V⁻¹ * Λ ^ (-(q / 2)) with hτdef
  have hτ0 : 0 < τ := mul_pos (inv_pos.2 hV0) hΛq0
  set P := uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ with hPdef
  set S1 := ∑ k ∈ Finset.Ico 4 ⌊Λ / 4⌋₊, uWindowBound P q x k with hS1def
  set S2 := ∑ k ∈ Finset.Ico (halfKb x 0) (halfKb x 8), uWindowBound P q x k with hS2def
  set S3 := ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x), uWindowBound P q x k with hS3def
  set Sw := ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k with hSwdef
  set C := (3 / 2 : ℝ) ^ (-a) with hCdef
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  have hC1 : C ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  set b := G₇ * A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) with hbdef
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg hG₇0 hA₇0) (Real.rpow_nonneg (by norm_num) _)
  have hd : 0 < 1 - Real.exp (-a) := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hSnn : ∀ s t : ℕ, 0 ≤ ∑ k ∈ Finset.Ico s t, uWindowBound P q x k := fun s t =>
    Finset.sum_nonneg fun k _ => uWindowBound_nonneg hPv hq0.le (by linarith) k
  -- the reduction's constant
  set CR := smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) with hCRdef
  have hCR0 : 0 ≤ CR := (smallQReductionConst_pos hz2 hzy hη hε).le
  set CRn := Real.exp (ql * Real.log (33885 / 100000)) with hCRn
  have hCRq : CR ^ q ≤ CRn := by
    calc CR ^ q ≤ (33885 / 100000 : ℝ) ^ q := Real.rpow_le_rpow hCR0 (halfCR_le hx) hq0.le
      _ ≤ (33885 / 100000 : ℝ) ^ ql :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hqlq
      _ = CRn := by rw [hCRn, rpow_eq_exp_mul_log (by norm_num)]
  have hCRn0 : 0 ≤ CRn := (Real.exp_pos _).le
  -- the low windows
  set Geo := 1 / ql + 1 / (ql * wl) + Vb * (1 / 2 + a₁ / 10) with hGeo
  set Abel := b₁ - (b₁ - b₂) * Real.exp (-(5 * a₁)) - (b₂ - b₃) * Real.exp (-(6 * a₁))
    - (b₃ - b₄) * Real.exp (-(7 * a₁)) - (b₄ - b₅) * Real.exp (-(31 * a₁))
    - (b₅ - b₆) * Real.exp (-(61 * a₁)) - (b₆ - b₇) * Real.exp (-(97 * a₁)) - b₇ * Et
    with hAbel
  have hS1 : S1 ≤ τ * (Geo * Abel) := by
    have hS10 : 0 ≤ S1 := hSnn _ _
    have hAb0 : 0 ≤ Abel := by
      have h1 : 0 ≤ (1 - Real.exp (-a)) * S1 := mul_nonneg hd.le hS10
      have h2 : 0 < C * Λ ^ (-(q / 2)) := mul_pos hC0 hΛq0
      by_contra hneg
      have := mul_neg_of_pos_of_neg h2 (lt_of_not_ge hneg)
      linarith
    have h1 : S1 ≤ C * Λ ^ (-(q / 2)) * Abel / (1 - Real.exp (-a)) := by
      rw [le_div_iff₀ hd]; linarith
    have e2 : C * Λ ^ (-(q / 2)) * Abel / (1 - Real.exp (-a))
        = τ * (C * (V / (1 - Real.exp (-a))) * Abel) := by
      rw [hτdef]; field_simp
    rw [e2] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hτ0.le)
    have hVd0 : 0 ≤ V / (1 - Real.exp (-a)) := div_nonneg hV0.le hd.le
    calc C * (V / (1 - Real.exp (-a))) * Abel ≤ 1 * Geo * Abel :=
          mul_le_mul_of_nonneg_right (mul_le_mul hC1 hgeo hVd0 zero_le_one) hAb0
      _ = Geo * Abel := by ring
  -- the high groups
  set Sig := ∑ g ∈ Finset.range 8, halfRho (g + 1)
    * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1)))) with hSigdef
  have hΔ0 : ∀ g, 0 ≤ Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))) :=
    fun g => sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hmono (Nat.le_succ g)) ha0.le)))
  have hSg0 : 0 ≤ Sig :=
    Finset.sum_nonneg fun g _ => mul_nonneg (halfRho_nonneg _) (hΔ0 g)
  have hSg1 : Sig ≤ 1497 / 500 * E0b := by
    have h1 : Sig ≤ ∑ g ∈ Finset.range 8, halfRho 8
        * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1)))) :=
      Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_right
        (halfRho_mono (by have := Finset.mem_range.1 hg; omega)) (hΔ0 g)
    rw [← Finset.mul_sum] at h1
    have htel := Finset.sum_range_sub' (fun g : ℕ => Real.exp (-(a * (halfKb x g : ℝ)))) 8
    rw [htel] at h1
    have h8 : 0 ≤ Real.exp (-(a * halfKb x 8)) := (Real.exp_pos _).le
    have hρ0 := halfRho_nonneg 8
    have h2 : halfRho 8 * (Real.exp (-(a * halfKb x 0)) - Real.exp (-(a * halfKb x 8)))
        ≤ 1497 / 500 * E0b :=
      mul_le_mul hρ8 (by linarith) (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hmono (Nat.zero_le 8)) ha0.le))))
        (by norm_num)
    linarith
  have hS2 : S2 ≤ τ * (b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b)) := by
    have hsum : ∑ g ∈ Finset.range 8, C * Λ ^ (-(q / 2)) * b * halfRho (g + 1)
        * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))))
        = C * Λ ^ (-(q / 2)) * b * Sig := by
      rw [hSigdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    rw [hsum] at hhigh
    have h1 : S2 ≤ C * Λ ^ (-(q / 2)) * b * Sig / (1 - Real.exp (-a)) := by
      rw [le_div_iff₀ hd]; linarith
    have e2 : C * Λ ^ (-(q / 2)) * b * Sig / (1 - Real.exp (-a))
        = τ * (C * b * (V / (1 - Real.exp (-a)) * Sig)) := by
      rw [hτdef]; field_simp
    rw [e2] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hτ0.le)
    have hin : V / (1 - Real.exp (-a)) * Sig
        ≤ Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b := by
      have hQS := mul_le_mul_of_nonneg_right hQ hSg0
      have eQ : (1 + w) / (q * w) * Sig = ∑ g ∈ Finset.range 8, halfRho (g + 1)
          * ((1 + w) / (q * w)
            * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))))) := by
        rw [hSigdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by ring
      have hA : ∑ g ∈ Finset.range 8, halfRho (g + 1)
          * ((1 + w) / (q * w)
            * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))))) ≤ Hb :=
        le_trans (Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left
          (hterm g (Finset.mem_range.1 hg)) (halfRho_nonneg _)) hHb
      have hB : V * (1 / 2 + a / 10) * Sig ≤ Vb * (1 / 2 + a₁ / 10) * (1497 / 500 * E0b) :=
        mul_le_mul (mul_le_mul hVb (by linarith) (by linarith) (by linarith)) hSg1 hSg0
          (mul_nonneg (le_trans hV0.le hVb) (by have := le_trans ha0.le ha₁; linarith))
      have e5 : ((1 + w) / (q * w) + V * (1 / 2 + a / 10)) * Sig
          = (1 + w) / (q * w) * Sig + V * (1 / 2 + a / 10) * Sig := by ring
      rw [e5] at hQS
      linarith
    have hin0 : 0 ≤ V / (1 - Real.exp (-a)) * Sig := mul_nonneg (div_nonneg hV0.le hd.le) hSg0
    calc C * b * (V / (1 - Real.exp (-a)) * Sig) ≤ 1 * b * (V / (1 - Real.exp (-a)) * Sig) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hb0) hin0
      _ ≤ 1 * b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b) :=
          mul_le_mul_of_nonneg_left hin (by linarith)
      _ = _ := by ring
  -- the tail
  have hS3 : S3 ≤ τ * (b * Tb * (797 / 10000)) := by
    have e3 : C * Λ ^ (-(q / 2)) * b * Real.exp (-(a * halfKb x 8)) * Λ ^ (1 / 4 : ℝ)
        * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11))
        = τ * (C * b * Real.exp (-(a * halfKb x 8)) * (V * Λ ^ (1 / 4 : ℝ)
          * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11)))) := by
      rw [hτdef]; field_simp
    rw [e3] at htail
    refine le_trans htail (mul_le_mul_of_nonneg_left ?_ hτ0.le)
    have hE80 : 0 ≤ Real.exp (-(a * halfKb x 8)) := (Real.exp_pos _).le
    have hT80 : 0 ≤ 4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
        + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)) := by
      have h1 : 0 ≤ (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ) :=
        Real.rpow_nonneg (by have := halfTheta_pos 8; linarith) _
      have h2 : 0 ≤ Real.log 6000 := Real.log_nonneg (by norm_num)
      have h3 : 0 ≤ (6000 : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
      exact add_nonneg (mul_nonneg (by norm_num) h1) (mul_nonneg (by linarith) h3)
    have hTb0 : 0 ≤ Tb := le_trans (mul_nonneg (by linarith) hE80) hTb'
    calc C * b * Real.exp (-(a * halfKb x 8)) * (V * Λ ^ (1 / 4 : ℝ)
          * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11)))
        ≤ 1 * b * Real.exp (-(a * halfKb x 8)) * ((1 + w)
          * (4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
            + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hb0) hE80) htf
            (mul_nonneg (mul_nonneg hV0.le (Real.rpow_nonneg hΛ0.le _)) (by
              have h1 : 0 ≤ (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) :=
                Real.rpow_nonneg (add_nonneg (mul_nonneg hLpp0 (halfTheta_pos 8).le)
                  zero_le_one) _
              have h2 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
              exact add_nonneg (mul_nonneg (by norm_num) h1) (by linarith)))
            (mul_nonneg (mul_nonneg zero_le_one hb0) hE80)
      _ = b * ((1 + w) * Real.exp (-(a * halfKb x 8)))
          * (4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
            + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ))) := by ring
      _ ≤ b * Tb * (797 / 10000) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTb' hb0) hT8 hT80 (mul_nonneg hb0 hTb0)
  -- the windows together
  have hSw : CR ^ q * Sw ≤ τ * (CRn * (Geo * Abel
      + bH * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000)))) := by
    have hSw0 : 0 ≤ Sw := hSnn _ _
    have hsp : Sw = S1 + S2 + S3 := hsplit
    have hB0 : 0 ≤ Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000) := by
      have hHb0 : 0 ≤ Hb := le_trans (Finset.sum_nonneg fun g _ => mul_nonneg (halfRho_nonneg _)
        (mul_nonneg (by linarith) (div_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
          (mul_le_mul_of_nonneg_left (halfSigLo_le_hi g) (mul_pos hq0 hw0).le))))
          (mul_pos hq0 hw0).le))) hHb
      have hE00 : 0 ≤ E0b := le_trans (Real.exp_pos _).le hE0
      have hTb0 : 0 ≤ Tb := le_trans (mul_nonneg (by linarith) (Real.exp_pos _).le) hTb
      have hVb0 : 0 ≤ Vb := le_trans hV0.le hVb
      have ha₁0 : 0 ≤ a₁ := le_trans ha0.le ha₁
      have t1 : 0 ≤ Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b :=
        mul_nonneg (mul_nonneg (mul_nonneg hVb0 (by linarith)) (by norm_num)) hE00
      have t2 : 0 ≤ Tb * (797 / 10000) := mul_nonneg hTb0 (by norm_num)
      linarith
    have hbb : b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b) + b * Tb * (797 / 10000)
        ≤ bH * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000)) := by
      have := mul_le_mul_of_nonneg_right hbH hB0
      linarith
    calc CR ^ q * Sw ≤ CRn * Sw := mul_le_mul_of_nonneg_right hCRq hSw0
      _ ≤ CRn * (τ * (Geo * Abel)
          + τ * (b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b))
          + τ * (b * Tb * (797 / 10000))) := by
          rw [hsp]
          exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hS1 hS2) hS3) hCRn0
      _ ≤ τ * (CRn * (Geo * Abel
          + bH * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000)))) := by
          have := mul_le_mul_of_nonneg_left hbb (mul_nonneg hτ0.le hCRn0)
          linarith
  -- the far range
  have hR_F : CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x
      ≤ τ * (CRn * Vb * Real.exp (3 / 4 * Real.log 880)) := by
    have h880 : (880 : ℝ) ^ (3 / 2 * q) ≤ Real.exp (3 / 4 * Real.log 880) := by
      rw [← rpow_eq_exp_mul_log (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h1 : Λ ^ (-(q / 2)) = τ * V := by rw [hτdef]; field_simp
    have hF0 : 0 ≤ uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x := by
      unfold uFarBound
      split_ifs
      · exact le_min (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by
          refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (Real.rpow_nonneg (by positivity) _)
          refine mul_nonneg (mul_nonneg ?_ (Real.rpow_nonneg ?_ _))
            (Real.rpow_nonneg (by positivity) _)
          · change 0 ≤ shiftMomentConst _ _ _ _ _ _ _ _
            unfold shiftMomentConst
            exact le_trans (Real.rpow_nonneg (by change (0 : ℝ) ≤ 1 * (1 + 67 / 2); norm_num) _)
              (le_max_left _ _)
          · have := Real.add_one_le_exp (1 : ℝ)
            exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_pos _).le) _)
      · exact Real.rpow_nonneg (by positivity) _
    have hVb0 : 0 ≤ Vb := le_trans hV0.le hVb
    calc CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x
        ≤ CRn * (Λ ^ (-(q / 2)) * (880 : ℝ) ^ (3 / 2 * q)) :=
          mul_le_mul hCRq hfarb hF0 hCRn0
      _ = τ * (CRn * (V * (880 : ℝ) ^ (3 / 2 * q))) := by rw [h1]; ring
      _ ≤ τ * (CRn * (Vb * Real.exp (3 / 4 * Real.log 880))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul hVb h880 (Real.rpow_nonneg (by norm_num) _) hVb0) hCRn0) hτ0.le
      _ = _ := by ring
  -- together
  have htot : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ) ≤ τ * ((1 + wl) * Real.exp (-(ql * wl))
            * (Real.exp ((a₁ - 3 / 4) * Real.log 6000)
              + CRn * Real.exp (1 / 2 * Real.log 51) * Real.exp ((a₁ - 1 / 4) * Real.log 6000))
          + 1 / 1000)
        + CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + CR ^ q * Sw := by
    have e : uPFyAt q (halfY x) + halfTail x ^ q
        + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
          + uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + Sw)
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
        = (uPFyAt q (halfY x) + halfTail x ^ q
          + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
            * uPFcAt q (halfSigma x) (halfY x))
          + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q)
          + CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + CR ^ q * Sw := by ring
    rw [e] at hasm
    linarith
  calc _ ≤ _ := htot
    _ ≤ τ * 25 := by
        have := mul_le_mul_of_nonneg_left hfin hτ0.le
        linarith [hR_F, hSw]
    _ = 25 * V⁻¹ * Λ ^ (-(q / 2)) := by rw [hτdef]; ring

/-! ### The cells' bounds on the high groups' terms -/

lemma halfSigLo_ge (g : ℕ) : 1499 / 6000 ≤ halfSigLo g := by
  unfold halfSigLo
  split_ifs with h
  · norm_num
  · have h1 := halfTheta_anti (show 1 ≤ g by omega)
    have h2 : halfTheta 1 = 9 / 20 := by unfold halfTheta; norm_num
    linarith

lemma halfSigLo_eight : halfSigLo 8 = 114534631 / 117187500 := by
  unfold halfSigLo halfTheta; norm_num

lemma halfSigLo_zero : halfSigLo 0 = 1499 / 6000 := by
  unfold halfSigLo; norm_num

/-- **The high groups' terms on a bounded cell**: `(1 + w)F(qw) ≤ (1 + w_u)F(q_l w_l)` for
`w ∈ [w_l, w_u]`, `q ≥ q_l`, `F(y) = (e^{-yσ_l} - e^{-yσ_h})/y` decreasing
(`RMF.exp_diff_div_anti`). -/
lemma halfHb_bounded_le {q w ql wl wu : ℝ} (hql : 0 < ql) (hqlq : ql ≤ q) (hwl0 : 0 < wl)
    (hwl : wl ≤ w) (hwu : w ≤ wu) :
    ∑ g ∈ Finset.range 8, halfRho (g + 1) * ((1 + w) * ((Real.exp (-(q * w * halfSigLo g))
        - Real.exp (-(q * w * halfSigHi (g + 1)))) / (q * w)))
      ≤ ∑ g ∈ Finset.range 8, halfRho (g + 1) * ((1 + wu)
        * ((Real.exp (-(ql * wl * halfSigLo g)) - Real.exp (-(ql * wl * halfSigHi (g + 1))))
          / (ql * wl))) := by
  refine Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left ?_ (halfRho_nonneg _)
  have hy' : 0 < ql * wl := mul_pos hql hwl0
  have hyy : ql * wl ≤ q * w := mul_le_mul hqlq hwl hwl0.le (by linarith)
  have hs0 : 0 ≤ halfSigLo g := le_trans (by norm_num) (halfSigLo_ge g)
  have hst := halfSigLo_le_hi g
  have hF := exp_diff_div_anti hy' hyy hs0 hst
  have hF0 : 0 ≤ (Real.exp (-(q * w * halfSigLo g)) - Real.exp (-(q * w * halfSigHi (g + 1))))
      / (q * w) :=
    div_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
      (mul_le_mul_of_nonneg_left hst (by linarith))))) (by linarith)
  exact mul_le_mul (by linarith) hF hF0 (by linarith)

/-- **The high groups' terms on the unbounded cell** `w ≥ W`: each is
`≤ ρ_8(1 + 1/W)e^{-q_l Wσ_l(0)}/q_l`. -/
lemma halfHb_large_le {q w ql W : ℝ} (hql : 0 < ql) (hqlq : ql ≤ q) (hW : 0 < W)
    (hWw : W ≤ w) :
    ∑ g ∈ Finset.range 8, halfRho (g + 1) * ((1 + w) * ((Real.exp (-(q * w * halfSigLo g))
        - Real.exp (-(q * w * halfSigHi (g + 1)))) / (q * w)))
      ≤ 8 * (1497 / 500 * ((1 + 1 / W) / ql * Real.exp (-(ql * W * (1499 / 6000))))) := by
  have hq0 : 0 < q := lt_of_lt_of_le hql hqlq
  have hw0 : 0 < w := lt_of_lt_of_le hW hWw
  have hy0 : 0 < q * w := mul_pos hq0 hw0
  have hB0 : 0 ≤ (1 + 1 / W) / ql * Real.exp (-(ql * W * (1499 / 6000))) :=
    mul_nonneg (div_nonneg (by have := one_div_pos.2 hW; linarith) hql.le) (Real.exp_pos _).le
  have hterm : ∀ g ∈ Finset.range 8, halfRho (g + 1) * ((1 + w)
      * ((Real.exp (-(q * w * halfSigLo g)) - Real.exp (-(q * w * halfSigHi (g + 1))))
        / (q * w))) ≤ 1497 / 500 * ((1 + 1 / W) / ql * Real.exp (-(ql * W * (1499 / 6000)))) := by
    intro g hg
    have hρ : halfRho (g + 1) ≤ 1497 / 500 :=
      le_trans (halfRho_mono (by have := Finset.mem_range.1 hg; omega)) halfRho_eight_le
    have hs := halfSigLo_ge g
    -- drop the upper end, then `(1 + w)/(qw) ≤ (1 + 1/W)/q_l` and `qwσ ≥ q_l W σ_l(0)`
    have h1 : (Real.exp (-(q * w * halfSigLo g)) - Real.exp (-(q * w * halfSigHi (g + 1))))
        / (q * w) ≤ Real.exp (-(q * w * halfSigLo g)) / (q * w) :=
      div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(q * w * halfSigHi (g + 1)))])
        hy0.le
    have h2 : (1 + w) / (q * w) ≤ (1 + 1 / W) / ql := by
      have e : (1 + w) / (q * w) = (1 / w + 1) / q := by field_simp
      rw [e]
      have t1 : 1 / w ≤ 1 / W := one_div_le_one_div_of_le hW hWw
      have t2 : 0 ≤ 1 / w + 1 := by have := one_div_pos.2 hw0; linarith
      calc (1 / w + 1) / q ≤ (1 / W + 1) / q := div_le_div_of_nonneg_right (by linarith) hq0.le
        _ ≤ (1 / W + 1) / ql :=
            div_le_div_of_nonneg_left (by have := one_div_pos.2 hW; linarith) hql hqlq
        _ = (1 + 1 / W) / ql := by ring
    have h3 : Real.exp (-(q * w * halfSigLo g)) ≤ Real.exp (-(ql * W * (1499 / 6000))) := by
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      exact mul_le_mul (mul_le_mul hqlq hWw hW.le hq0.le) hs (by norm_num) hy0.le
    have hF0 : 0 ≤ (Real.exp (-(q * w * halfSigLo g)) - Real.exp (-(q * w * halfSigHi (g + 1))))
        / (q * w) :=
      div_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_left (halfSigLo_le_hi g) hy0.le)))) hy0.le
    have h4 : (1 + w) * ((Real.exp (-(q * w * halfSigLo g))
        - Real.exp (-(q * w * halfSigHi (g + 1)))) / (q * w))
        ≤ (1 + 1 / W) / ql * Real.exp (-(ql * W * (1499 / 6000))) := by
      calc (1 + w) * ((Real.exp (-(q * w * halfSigLo g))
            - Real.exp (-(q * w * halfSigHi (g + 1)))) / (q * w))
          ≤ (1 + w) * (Real.exp (-(q * w * halfSigLo g)) / (q * w)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = (1 + w) / (q * w) * Real.exp (-(q * w * halfSigLo g)) := by ring
        _ ≤ (1 + 1 / W) / ql * Real.exp (-(ql * W * (1499 / 6000))) :=
            mul_le_mul h2 h3 (Real.exp_pos _).le
              (div_nonneg (by have := one_div_pos.2 hW; linarith) hql.le)
    exact mul_le_mul hρ h4 (mul_nonneg (by linarith) hF0) (by norm_num)
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-- `(1 + w)e^{-qwσ_l(8)} ≤ (1 + w_l)e^{-q_l w_lσ_l(8)}` for `w ≥ w_l ≥ 3/2`, `q ≥ q_l ≥ 0.49`
(`RMF.one_add_mul_exp_neg_anti`: `1/(q_lσ_l(8)) - 1 < 3/2`). -/
lemma halfTb_le {q w ql wl : ℝ} (hql : 49 / 100 ≤ ql) (hqlq : ql ≤ q) (hwl : 3 / 2 ≤ wl)
    (hww : wl ≤ w) :
    (1 + w) * Real.exp (-(q * w * halfSigLo 8))
      ≤ (1 + wl) * Real.exp (-(ql * wl * (114534631 / 117187500))) := by
  rw [halfSigLo_eight]
  have hc : 0 < ql * (114534631 / 117187500) := by positivity
  have hu : 1 / (ql * (114534631 / 117187500)) - 1 ≤ wl := by
    have : 1 / (ql * (114534631 / 117187500)) ≤ 1 / (49 / 100 * (114534631 / 117187500)) :=
      one_div_le_one_div_of_le (by norm_num) (mul_le_mul_of_nonneg_right hql (by norm_num))
    have h2 : 1 / (49 / 100 * (114534631 / 117187500 : ℝ)) ≤ 21 / 10 := by norm_num
    linarith
  have h := one_add_mul_exp_neg_anti hc hu hww
  have e1 : ∀ z : ℝ, ql * (114534631 / 117187500) * z = ql * z * (114534631 / 117187500) :=
    fun z => by ring
  rw [e1, e1] at h
  refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_))
    (by linarith)) h
  have hw0 : 0 ≤ w := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqlq hw0) (by norm_num)

/-- `e^{-qwσ_l(0)} ≤ e^{-q_l w_lσ_l(0)}`. -/
lemma halfE0_le {q w ql wl : ℝ} (hql : 0 ≤ ql) (hqlq : ql ≤ q) (hwl : 0 ≤ wl) (hww : wl ≤ w) :
    Real.exp (-(q * w * halfSigLo 0)) ≤ Real.exp (-(ql * wl * (1499 / 6000))) := by
  rw [halfSigLo_zero]
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right
    (mul_le_mul hqlq hww hwl (by linarith)) (by norm_num)))

/-- The groups' `ρ`, in numerals. -/
lemma halfRho_le_table : halfRho 1 ≤ 49 / 40 ∧ halfRho 2 ≤ 174 / 125 ∧ halfRho 3 ≤ 1581 / 1000
    ∧ halfRho 4 ≤ 1797 / 1000 ∧ halfRho 5 ≤ 1021 / 500 ∧ halfRho 6 ≤ 58 / 25
    ∧ halfRho 7 ≤ 527 / 200 ∧ halfRho 8 ≤ 1497 / 500 := by
  unfold halfRho halfTheta
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 1) = 891 / 2000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 2) = 2673 / 10000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 3) = 8019 / 50000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 4) = 24057 / 250000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 5) = 72171 / 1250000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 6) = 216513 / 6250000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 7) = 649539 / 31250000 by norm_num]
    interval_decide (trust := kernel)
  · rw [show (99 / 100 : ℝ) * (3 / 4 * (3 / 5) ^ 8) = 1948617 / 156250000 by norm_num]
    interval_decide (trust := kernel)

/-- **The high groups' sum at a cell's corner, in numerals**: `ρ_g` by `RMF.halfRho_le_table` and
the ends `σ` exactly. -/
lemma halfHigh_sum_le {y c : ℝ} (hy : 0 < y) (hc : 0 ≤ c) :
    ∑ g ∈ Finset.range 8, halfRho (g + 1) * (c * ((Real.exp (-(y * halfSigLo g))
        - Real.exp (-(y * halfSigHi (g + 1)))) / y))
      ≤ c / y * (49 / 40 * (Real.exp (-(y * (1499 / 6000))) - Real.exp (-(y * (11 / 20))))
        + 174 / 125 * (Real.exp (-(y * (1633 / 3000))) - Real.exp (-(y * (73 / 100))))
        + 1581 / 1000 * (Real.exp (-(y * (5419 / 7500))) - Real.exp (-(y * (419 / 500))))
        + 1797 / 1000 * (Real.exp (-(y * (62209 / 75000))) - Real.exp (-(y * (2257 / 2500))))
        + 1021 / 500 * (Real.exp (-(y * (167551 / 187500)))
          - Real.exp (-(y * (11771 / 12500))))
        + 58 / 25 * (Real.exp (-(y * (1747681 / 1875000))) - Real.exp (-(y * (60313 / 62500))))
        + 527 / 200 * (Real.exp (-(y * (4477459 / 4687500)))
          - Real.exp (-(y * (305939 / 312500))))
        + 1497 / 500 * (Real.exp (-(y * (45424129 / 46875000)))
          - Real.exp (-(y * (1542817 / 1562500))))) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := halfRho_le_table
  have key : ∀ (g : ℕ) (r s t : ℝ), halfRho (g + 1) ≤ r → halfSigLo g = s →
      halfSigHi (g + 1) = t →
      halfRho (g + 1) * (c * ((Real.exp (-(y * halfSigLo g))
        - Real.exp (-(y * halfSigHi (g + 1)))) / y))
        ≤ c / y * (r * (Real.exp (-(y * s)) - Real.exp (-(y * t)))) := by
    intro g r s t hr hs ht
    have hd : 0 ≤ Real.exp (-(y * s)) - Real.exp (-(y * t)) := by
      rw [← hs, ← ht]
      exact sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_left (halfSigLo_le_hi g) hy.le)))
    rw [hs, ht]
    have e : halfRho (g + 1) * (c * ((Real.exp (-(y * s)) - Real.exp (-(y * t))) / y))
        = c / y * (halfRho (g + 1) * (Real.exp (-(y * s)) - Real.exp (-(y * t)))) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hd) (div_nonneg hc hy.le)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have k0 := key 0 (49 / 40) (1499 / 6000) (11 / 20) r1 (by unfold halfSigLo; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k1 := key 1 (174 / 125) (1633 / 3000) (73 / 100) r2 (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k2 := key 2 (1581 / 1000) (5419 / 7500) (419 / 500) r3
    (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k3 := key 3 (1797 / 1000) (62209 / 75000) (2257 / 2500) r4
    (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k4 := key 4 (1021 / 500) (167551 / 187500) (11771 / 12500) r5
    (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k5 := key 5 (58 / 25) (1747681 / 1875000) (60313 / 62500) r6
    (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k6 := key 6 (527 / 200) (4477459 / 4687500) (305939 / 312500) r7
    (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  have k7 := key 7 (1497 / 500) (45424129 / 46875000) (1542817 / 1562500) r8
    (by unfold halfSigLo halfTheta; norm_num)
    (by unfold halfSigHi halfTheta; norm_num)
  linarith

/-- `((1 - ½)^{-1/2})⁴ = 4`. -/
lemma half_rpow_pow_four : ((1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ))) ^ 4 = 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show (-(1 / 2 : ℝ)) * ((4 : ℕ) : ℝ) = -2 by norm_num, Real.rpow_neg (by norm_num),
    show (1 - 1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), inv_inv, Real.rpow_two]
  norm_num

end RMF
