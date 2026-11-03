/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.Regions

/-!
# HP2's window integral with the rest: the deep cells' certificates

The discharges of `RMF.IsRestCosBound` per cell type, with the numeric side condition in the form
`interval_decide` transports (products, `Real.pi * q`, `Real.exp` of the cell's exponent `ℓ`):
the first lobe (`RMF.isRestCosBound_exp_small`, `…_large`, `…_large_sat`), the second lobe's
positive half (`RMF.isRestCosBound_exp_pos`), its negative half by the tent
(`RMF.isRestCosBound_exp_neg_low`, `…_high`), the constant bound `P₀ ≤ 0.3237` on the second lobe
(`RMF.isRestCosBound_second_const`) and the saturation `≤ 5.032` (`RMF.isRestCosBound_sat_num`);
the deep cells' ends against `π/2`, `π`, `3π/2`, `5π/2`.
-/

open MeasureTheory Real

namespace RMF

attribute [local simp] LeanCert.Core.MathConst.toReal

/-! ### The deep cells' ends -/

lemma hp2DeepEnd_eq_exp (j : ℕ) {ℓ : ℝ} (h : 2 - (j : ℝ) / 40 = ℓ) : hp2DeepEnd j = Real.exp ℓ := by
  rw [hp2DeepEnd, h]

lemma hp2DeepEnd_anti {i j : ℕ} (h : i ≤ j) : hp2DeepEnd j ≤ hp2DeepEnd i := by
  unfold hp2DeepEnd
  refine Real.exp_le_exp.2 ?_
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  linarith

/-- `e^{2 - 62/40} ≤ π/2`. -/
lemma hp2DeepEnd_le_pi_div_two {j : ℕ} (hj : 62 ≤ j) : hp2DeepEnd j ≤ π / 2 := by
  refine (hp2DeepEnd_anti hj).trans ?_
  rw [hp2DeepEnd_eq_exp 62 (ℓ := 9 / 20) (by norm_num), show π / 2 = Real.pi * (1 / 2) by ring]
  interval_decide (trust := kernel)

/-- `π/2 ≤ e^{2 - 61/40}`. -/
lemma pi_div_two_le_hp2DeepEnd {j : ℕ} (hj : j ≤ 61) : π / 2 ≤ hp2DeepEnd j := by
  refine le_trans ?_ (hp2DeepEnd_anti hj)
  rw [hp2DeepEnd_eq_exp 61 (ℓ := 19 / 40) (by norm_num), show π / 2 = Real.pi * (1 / 2) by ring]
  interval_decide (trust := kernel)

/-- `e^{2 - 35/40} ≤ π`. -/
lemma hp2DeepEnd_le_pi {j : ℕ} (hj : 35 ≤ j) : hp2DeepEnd j ≤ π := by
  refine (hp2DeepEnd_anti hj).trans ?_
  rw [hp2DeepEnd_eq_exp 35 (ℓ := 9 / 8) (by norm_num), ← sub_nonpos]
  interval_decide (trust := kernel)

/-- `π ≤ e^{2 - 34/40}`. -/
lemma pi_le_hp2DeepEnd {j : ℕ} (hj : j ≤ 34) : π ≤ hp2DeepEnd j := by
  refine le_trans ?_ (hp2DeepEnd_anti hj)
  rw [hp2DeepEnd_eq_exp 34 (ℓ := 23 / 20) (by norm_num), ← sub_nonpos]
  interval_decide (trust := kernel)

/-- `e^{2 - 18/40} ≤ 3π/2`. -/
lemma hp2DeepEnd_le_three_pi_div_two {j : ℕ} (hj : 18 ≤ j) : hp2DeepEnd j ≤ 3 * π / 2 := by
  refine (hp2DeepEnd_anti hj).trans ?_
  rw [hp2DeepEnd_eq_exp 18 (ℓ := 31 / 20) (by norm_num),
    show 3 * π / 2 = Real.pi * (3 / 2) by ring]
  interval_decide (trust := kernel)

/-- `3π/2 ≤ e^{2 - 17/40}`. -/
lemma three_pi_div_two_le_hp2DeepEnd {j : ℕ} (hj : j ≤ 17) : 3 * π / 2 ≤ hp2DeepEnd j := by
  refine le_trans ?_ (hp2DeepEnd_anti hj)
  rw [hp2DeepEnd_eq_exp 17 (ℓ := 63 / 40) (by norm_num),
    show 3 * π / 2 = Real.pi * (3 / 2) by ring]
  interval_decide (trust := kernel)

/-- `e² ≤ 5π/2`. -/
lemma hp2DeepEnd_le_five_pi_div_two (j : ℕ) : hp2DeepEnd j ≤ 5 * π / 2 := by
  refine (hp2DeepEnd_anti (Nat.zero_le j)).trans ?_
  rw [hp2DeepEnd_eq_exp 0 (ℓ := 2) (by norm_num), show 5 * π / 2 = Real.pi * (5 / 2) by ring]
  interval_decide (trust := kernel)

/-! ### The numeral constants -/

/-- **The positive half-lobe in numerals**: `lobeP(5π/2) - lobeP(3π/2) ≤ 0.3237`. -/
theorem lobeP_sub_le : lobeP (5 * π / 2) - lobeP (3 * π / 2) ≤ 0.3237 := by
  have e : lobeP (5 * π / 2) - lobeP (3 * π / 2)
      = (1 - 2 * (Real.pi * Real.pi) + Real.pi * Real.pi * Real.pi * Real.pi * (2 / 3))
          * (Real.log (Real.pi * (5 / 2)) - Real.log (Real.pi * (3 / 2)))
        + (Real.pi * 2 - Real.pi * Real.pi * Real.pi * (4 / 3)) * Real.pi
        + (Real.pi * Real.pi - 1 / 2) * (Real.pi * Real.pi * 4) * (1 / 2)
        - Real.pi * (1 / 3) * (Real.pi * Real.pi * Real.pi * (49 / 4)) * (1 / 3)
        + Real.pi * Real.pi * Real.pi * Real.pi * 34 * (1 / 96) := by
    unfold lobeP
    rw [show 5 * π / 2 = Real.pi * (5 / 2) by ring, show 3 * π / 2 = Real.pi * (3 / 2) by ring]
    ring
  rw [e]
  interval_decide (trust := kernel)

/-- `einPoly 18` in Horner form. -/
noncomputable def einH (x : ℝ) : ℝ :=
  x * ((-1) + x * ((1 / 4) + x * ((-1 / 18) + x * ((1 / 96) + x * ((-1 / 600) + x * ((1 / 4320)
    + x * ((-1 / 35280) + x * ((1 / 322560) + x * ((-1 / 3265920) + x * ((1 / 36288000)
    + x * ((-1 / 439084800) + x * ((1 / 5748019200) + x * ((-1 / 80951270400)
    + x * ((1 / 1220496076800) + x * ((-1 / 19615115520000) + x * ((1 / 334764638208000)
    + x * ((-1 / 6046686277632000) + x * ((1 / 115242726703104000)))))))))))))))))))

lemma einPoly_eighteen (x : ℝ) : einPoly (2 * 9) x = einH x := by
  simp only [einPoly, einH, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num
  ring

/-- **The saturated exponential integral in numerals**: `∫_{1/(100e)}^{∞}e^{-s}/s ds ≤ 5.032` in the
form of `RMF.isRestCosBound_sat`. -/
theorem sat_le_num : Real.log 4 - Real.log (1 / (100 * Real.exp 1))
    + einPoly (2 * 9) 4 - einPoly (2 * 9) (1 / (100 * Real.exp 1))
    + Real.exp (-4) * (Real.log (4 + 1) - Real.log 4) ≤ 5.032 := by
  have e1 : Real.log (1 / (100 * Real.exp 1)) = -(Real.log 100 + 1) := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have e2 : 1 / (100 * Real.exp 1) = Real.exp (-1) * (1 / 100) := by
    rw [Real.exp_neg]; field_simp
  rw [e1, e2, einPoly_eighteen, einPoly_eighteen]
  norm_num
  unfold einH
  interval_decide (trust := kernel)

/-- **The saturated cells**: every range of frequencies has the bound `5.032`. -/
theorem isRestCosBound_sat_num (lo hi : ℝ) : IsRestCosBound lo hi 5.032 :=
  (isRestCosBound_sat lo hi).mono sat_le_num

/-! ### The first lobe -/

/-- The damping's normalisation at `lo = e^ℓ`: `1/(100e)/e^ℓ = e^{-1-ℓ}/100`. -/
lemma damp_exp_eq (ℓ : ℝ) :
    1 / (100 * Real.exp 1) / Real.exp ℓ = Real.exp (-1 - ℓ) * (1 / 100) := by
  rw [show -1 - ℓ = -1 + -ℓ by ring, Real.exp_add, Real.exp_neg, Real.exp_neg]
  field_simp

lemma exp_two_mul_eq (ℓ : ℝ) : Real.exp (2 * ℓ) = Real.exp ℓ * Real.exp ℓ := by
  rw [← Real.exp_add]; ring_nf

/-- **The first-lobe cells with a small damping, in numerals**: for `hi ≤ π/2`, the small-damping
bound at `lo = e^ℓ` in products. -/
theorem isRestCosBound_exp_small {ℓ hi B : ℝ} (hhi : hi ≤ π / 2)
    (hB : Real.log (Real.pi * (1 / 2)) - ℓ
      - (Real.pi * Real.pi * (1 / 4) - Real.exp (2 * ℓ)) * (1 / 4)
      + (Real.pi * Real.pi * Real.pi * Real.pi * (1 / 16) - Real.exp (4 * ℓ)) * (1 / 96)
      - Real.exp (-1 - ℓ) * (1 / 100) * (1 - Real.sin (Real.exp ℓ))
      + Real.exp (-2 - 2 * ℓ) * (1 / 20000)
        * (Real.pi * (1 / 2) - Real.exp ℓ * Real.sin (Real.exp ℓ) - Real.cos (Real.exp ℓ)) ≤ B) :
    IsRestCosBound (Real.exp ℓ) hi B := by
  refine isRestCosBound_first_small (Real.exp_pos ℓ) hhi (le_trans (le_of_eq ?_) hB)
  have e4 : Real.exp (4 * ℓ) = Real.exp ℓ ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  have e2' : Real.exp (-2 - 2 * ℓ) = (Real.exp (-1 - ℓ)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.log_exp, damp_exp_eq, exp_two_mul_eq, e4, e2', show π / 2 = Real.pi * (1 / 2) by ring]
  ring

/-- The polynomial parts `J₁`, `J₃` at `lo = e^ℓ`, `β = e^{-1-ℓ}/100`, in products. -/
lemma first_lobe_J_eq (ℓ : ℝ) :
    -(Real.exp (-(1 / (100 * Real.exp 1) / Real.exp ℓ) * Real.exp ℓ)
          * (Real.exp ℓ / (1 / (100 * Real.exp 1) / Real.exp ℓ)
            + 1 / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 2)
        - Real.exp (-(1 / (100 * Real.exp 1) / Real.exp ℓ) * (π / 2))
          * (π / 2 / (1 / (100 * Real.exp 1) / Real.exp ℓ)
            + 1 / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 2)) / 2
      + (Real.exp (-(1 / (100 * Real.exp 1) / Real.exp ℓ) * Real.exp ℓ)
          * (Real.exp ℓ ^ 3 / (1 / (100 * Real.exp 1) / Real.exp ℓ)
            + 3 * Real.exp ℓ ^ 2 / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 2
            + 6 * Real.exp ℓ / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 3
            + 6 / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 4)
        - Real.exp (-(1 / (100 * Real.exp 1) / Real.exp ℓ) * (π / 2))
          * ((π / 2) ^ 3 / (1 / (100 * Real.exp 1) / Real.exp ℓ)
            + 3 * (π / 2) ^ 2 / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 2
            + 6 * (π / 2) / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 3
            + 6 / (1 / (100 * Real.exp 1) / Real.exp ℓ) ^ 4)) / 24
    = -(Real.exp (-(Real.exp (-1) * (1 / 100)))
          * (Real.exp (1 + 2 * ℓ) * 100 + Real.exp (2 + 2 * ℓ) * 10000)
        - Real.exp (-(Real.exp (-1 - ℓ) * Real.pi * (1 / 200)))
          * (Real.pi * Real.exp (1 + ℓ) * 50 + Real.exp (2 + 2 * ℓ) * 10000)) * (1 / 2)
      + (Real.exp (-(Real.exp (-1) * (1 / 100)))
          * (Real.exp (1 + 4 * ℓ) * 100 + Real.exp (2 + 4 * ℓ) * 30000
            + Real.exp (3 + 4 * ℓ) * 6000000 + Real.exp (4 + 4 * ℓ) * 600000000)
        - Real.exp (-(Real.exp (-1 - ℓ) * Real.pi * (1 / 200)))
          * (Real.pi * Real.pi * Real.pi * Real.exp (1 + ℓ) * (25 / 2)
            + Real.pi * Real.pi * Real.exp (2 + 2 * ℓ) * 7500
            + Real.pi * Real.exp (3 + 3 * ℓ) * 3000000 + Real.exp (4 + 4 * ℓ) * 600000000))
        * (1 / 24) := by
  have hβ := damp_exp_eq ℓ
  have hx : Real.exp (-1 - ℓ) * (1 / 100) * Real.exp ℓ = Real.exp (-1) * (1 / 100) := by
    rw [mul_right_comm, ← Real.exp_add]; ring_nf
  have hy : Real.exp (-1 - ℓ) * (1 / 100) * (π / 2) = Real.exp (-1 - ℓ) * Real.pi * (1 / 200) := by
    ring
  have e1 : Real.exp (1 + 2 * ℓ) = Real.exp (1 + ℓ) * Real.exp ℓ := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (2 + 2 * ℓ) = Real.exp (1 + ℓ) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (3 + 3 * ℓ) = Real.exp (1 + ℓ) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e4 : Real.exp (4 + 4 * ℓ) = Real.exp (1 + ℓ) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have f1 : Real.exp (1 + 4 * ℓ) = Real.exp (1 + ℓ) * Real.exp ℓ ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have f2 : Real.exp (2 + 4 * ℓ) = Real.exp (1 + ℓ) ^ 2 * Real.exp ℓ ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have f3 : Real.exp (3 + 4 * ℓ) = Real.exp (1 + ℓ) ^ 3 * Real.exp ℓ := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have g : Real.exp (-1 - ℓ) = (Real.exp (1 + ℓ))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have hpos := Real.exp_pos (1 + ℓ)
  have hpos' := Real.exp_pos ℓ
  rw [hβ, neg_mul, neg_mul, hx, hy, e1, e2, e3, e4, f1, f2, f3, g]
  field_simp
  ring

/-- The first lobe's exponential integral at `lo = e^ℓ`: its ends `1/(100e)` and `e^{-1-ℓ}π/200`. -/
lemma first_lobe_ends (ℓ : ℝ) :
    1 / (100 * Real.exp 1) / Real.exp ℓ * Real.exp ℓ = 1 / (100 * Real.exp 1)
      ∧ 1 / (100 * Real.exp 1) / Real.exp ℓ * (π / 2)
        = Real.exp (-1 - ℓ) * Real.pi * (1 / 200) := by
  refine ⟨div_mul_cancel₀ _ (Real.exp_pos ℓ).ne', ?_⟩
  rw [damp_exp_eq]
  ring

/-- `1/(100e) = e^{-1}/100`. -/
lemma one_div_hundred_exp_eq : 1 / (100 * Real.exp 1) = Real.exp (-1) * (1 / 100) := by
  rw [Real.exp_neg]; field_simp

/-- **The first-lobe cells with any damping, in numerals**: for `hi ≤ π/2`, a bound `e` on
the exponential integral from `1/(100e)` to `e^{-1-ℓ}π/200` and the polynomial parts in products. -/
theorem isRestCosBound_exp_large {ℓ u hi e B : ℝ} (hhi : hi ≤ π / 2) (hu : -1 - ℓ = u)
    (he : ∫ s in Real.exp (-1) * (1 / 100)..Real.exp u * Real.pi * (1 / 200),
      Real.exp (-s) / s ≤ e)
    (hB : e
      + (-(Real.exp (-(Real.exp (-1) * (1 / 100)))
          * (Real.exp (1 + 2 * ℓ) * 100 + Real.exp (2 + 2 * ℓ) * 10000)
        - Real.exp (-(Real.exp (-1 - ℓ) * Real.pi * (1 / 200)))
          * (Real.pi * Real.exp (1 + ℓ) * 50 + Real.exp (2 + 2 * ℓ) * 10000)) * (1 / 2)
      + (Real.exp (-(Real.exp (-1) * (1 / 100)))
          * (Real.exp (1 + 4 * ℓ) * 100 + Real.exp (2 + 4 * ℓ) * 30000
            + Real.exp (3 + 4 * ℓ) * 6000000 + Real.exp (4 + 4 * ℓ) * 600000000)
        - Real.exp (-(Real.exp (-1 - ℓ) * Real.pi * (1 / 200)))
          * (Real.pi * Real.pi * Real.pi * Real.exp (1 + ℓ) * (25 / 2)
            + Real.pi * Real.pi * Real.exp (2 + 2 * ℓ) * 7500
            + Real.pi * Real.exp (3 + 3 * ℓ) * 3000000 + Real.exp (4 + 4 * ℓ) * 600000000))
        * (1 / 24)) ≤ B) :
    IsRestCosBound (Real.exp ℓ) hi B := by
  obtain ⟨hx₁, hx₂⟩ := first_lobe_ends ℓ
  refine isRestCosBound_first_large (e := e) (Real.exp_pos ℓ) hhi ?_ ?_
  · rw [hx₁, hx₂, one_div_hundred_exp_eq, hu]
    exact he
  · have hJ := first_lobe_J_eq ℓ
    linarith

/-- **The first-lobe cells, the exponential integral saturated**: for `e^ℓ ≤ hi ≤ π/2`, the
exponential integral at most `5.032` (`RMF.integral_exp_neg_div_le_sat`, `RMF.sat_le_num`). -/
theorem isRestCosBound_exp_large_sat {ℓ hi B : ℝ} (hlohi : Real.exp ℓ ≤ hi) (hhi : hi ≤ π / 2)
    (hB : 5.032
      + (-(Real.exp (-(Real.exp (-1) * (1 / 100)))
          * (Real.exp (1 + 2 * ℓ) * 100 + Real.exp (2 + 2 * ℓ) * 10000)
        - Real.exp (-(Real.exp (-1 - ℓ) * Real.pi * (1 / 200)))
          * (Real.pi * Real.exp (1 + ℓ) * 50 + Real.exp (2 + 2 * ℓ) * 10000)) * (1 / 2)
      + (Real.exp (-(Real.exp (-1) * (1 / 100)))
          * (Real.exp (1 + 4 * ℓ) * 100 + Real.exp (2 + 4 * ℓ) * 30000
            + Real.exp (3 + 4 * ℓ) * 6000000 + Real.exp (4 + 4 * ℓ) * 600000000)
        - Real.exp (-(Real.exp (-1 - ℓ) * Real.pi * (1 / 200)))
          * (Real.pi * Real.pi * Real.pi * Real.exp (1 + ℓ) * (25 / 2)
            + Real.pi * Real.pi * Real.exp (2 + 2 * ℓ) * 7500
            + Real.pi * Real.exp (3 + 3 * ℓ) * 3000000 + Real.exp (4 + 4 * ℓ) * 600000000))
        * (1 / 24)) ≤ B) :
    IsRestCosBound (Real.exp ℓ) hi B := by
  obtain ⟨hx₁, hx₂⟩ := first_lobe_ends ℓ
  have hlo : Real.exp ℓ ≤ π / 2 := hlohi.trans hhi
  have hle : 1 / (100 * Real.exp 1) ≤ 1 / (100 * Real.exp 1) / Real.exp ℓ * (π / 2) := by
    have h := mul_le_mul_of_nonneg_left hlo
      (show 0 ≤ 1 / (100 * Real.exp 1) / Real.exp ℓ by positivity)
    rwa [hx₁] at h
  have hxc : 1 / (100 * Real.exp 1) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hE := integral_exp_neg_div_le_sat 9 (by positivity) hxc hle
  refine isRestCosBound_first_large (e := 5.032) (Real.exp_pos ℓ) hhi ?_ ?_
  · rw [hx₁]
    exact hE.trans sat_le_num
  · have hJ := first_lobe_J_eq ℓ
    linarith

/-! ### The exponential integral on the cells' grid -/

/-- `einPoly 8` in Horner form. -/
noncomputable def einH8 (x : ℝ) : ℝ :=
  x * ((-1) + x * ((1 / 4) + x * ((-1 / 18) + x * ((1 / 96) + x * ((-1 / 600) + x * ((1 / 4320)
    + x * ((-1 / 35280) + x * ((1 / 322560)))))))))

lemma einPoly_eight (x : ℝ) : einPoly (2 * 4) x = einH8 x := by
  simp only [einPoly, einH8, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num
  ring

/-- **A piece of the exponential integral by the chord of `e^{-s}`**: for `0 < a < b`,
`∫_a^b e^{-s}/s ds ≤ e^{-a}L + (e^{-b} - e^{-a})(1 - aL/(b - a))`, `L = log b - log a` (the chord
lies above the convex `e^{-s}`). -/
theorem integral_exp_neg_div_le_chord {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ s in a..b, Real.exp (-s) / s
      ≤ Real.exp (-a) * (Real.log b - Real.log a)
        + (Real.exp (-b) - Real.exp (-a)) * (1 - a * (Real.log b - Real.log a) / (b - a)) := by
  have hba : 0 < b - a := by linarith
  set c₁ : ℝ := (Real.exp (-b) - Real.exp (-a)) / (b - a) with hc₁
  set c₀ : ℝ := Real.exp (-a) - c₁ * a with hc₀
  have hpos : ∀ s ∈ Set.uIcc a b, 0 < s := fun s hs => by
    rw [Set.uIcc_of_le hab.le] at hs
    exact ha.trans_le hs.1
  have hchord : ∀ s ∈ Set.Icc a b, Real.exp (-s) ≤ c₀ + c₁ * s := by
    intro s hs
    set θ : ℝ := (b - s) / (b - a) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hs.2]) hba.le
    have hθ1 : 0 ≤ 1 - θ := by
      rw [hθ, one_sub_div hba.ne']
      exact div_nonneg (by linarith [hs.1]) hba.le
    have hconv := convexOn_exp.2 (Set.mem_univ (-a)) (Set.mem_univ (-b)) hθ0 hθ1 (by ring)
    simp only [smul_eq_mul] at hconv
    have e1 : θ * -a + (1 - θ) * -b = -s := by rw [hθ]; field_simp; ring
    rw [e1] at hconv
    refine hconv.trans (le_of_eq ?_)
    rw [hc₀, hc₁, hθ]
    field_simp
    ring
  have hd : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun s => c₀ * Real.log s + c₁ * s) (c₀ / s + c₁) s := by
    intro s hs
    have h1 := (Real.hasDerivAt_log (hpos s hs).ne').const_mul c₀
    have h2 := (hasDerivAt_id s).const_mul c₁
    refine (h1.add h2).congr_deriv ?_
    field_simp
  have hc : ContinuousOn (fun s => c₀ / s + c₁) (Set.uIcc a b) :=
    (continuousOn_const.div continuousOn_id fun s hs => (hpos s hs).ne').add continuousOn_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have hle : ∫ s in a..b, Real.exp (-s) / s ≤ ∫ s in a..b, (c₀ / s + c₁) := by
    refine intervalIntegral.integral_mono_on hab.le (intervalIntegrable_exp_neg_div ha hab.le)
      hc.intervalIntegrable fun s hs => ?_
    have hs0 : 0 < s := ha.trans_le hs.1
    have e : c₀ / s + c₁ = (c₀ + c₁ * s) / s := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (hchord s hs) hs0.le
  rw [hFTC] at hle
  refine hle.trans (le_of_eq ?_)
  rw [hc₀, hc₁]
  field_simp
  ring

/-- `1 - (1/40)/(e^{1/40} - 1) ≥ 0.012`. -/
lemma chord_grid_const : 0.012 ≤ 1 - 1 / 40 * (Real.exp (1 / 40) - 1)⁻¹ := by
  have h1 : 1.02531 ≤ Real.exp (1 / 40) := by interval_decide (trust := kernel)
  have h2 : 0 < Real.exp (1 / 40) - 1 := by linarith
  rw [← sub_nonneg]
  have e : 1 - 1 / 40 * (Real.exp (1 / 40) - 1)⁻¹ - 0.012
      = (0.988 * (Real.exp (1 / 40) - 1) - 1 / 40) / (Real.exp (1 / 40) - 1) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (by nlinarith) h2.le

/-- **A step of the exponential integral on the grid** `X_u = e^uπ/200`, `X_{u+1/40}`:
`∫_{X_u}^{X_{u+1/40}} e^{-s}/s ds ≤ e^{-X_u}/40 + 0.012(e^{-X_{u+1/40}} - e^{-X_u})`. -/
theorem integral_exp_neg_div_le_grid (u : ℝ) :
    ∫ s in Real.exp u * Real.pi * (1 / 200)..Real.exp (u + 1 / 40) * Real.pi * (1 / 200),
        Real.exp (-s) / s
      ≤ Real.exp (-(Real.exp u * Real.pi * (1 / 200))) * (1 / 40)
        + (Real.exp (-(Real.exp (u + 1 / 40) * Real.pi * (1 / 200)))
          - Real.exp (-(Real.exp u * Real.pi * (1 / 200)))) * 0.012 := by
  have hπ := Real.pi_pos
  have ha : 0 < Real.exp u * Real.pi * (1 / 200) := by positivity
  have hb : Real.exp (u + 1 / 40) * Real.pi * (1 / 200)
      = Real.exp u * Real.pi * (1 / 200) * Real.exp (1 / 40) := by
    rw [Real.exp_add]; ring
  have hq : 1 < Real.exp (1 / 40) := Real.one_lt_exp_iff.2 (by norm_num)
  have hab : Real.exp u * Real.pi * (1 / 200) < Real.exp (u + 1 / 40) * Real.pi * (1 / 200) := by
    rw [hb]
    exact lt_mul_of_one_lt_right ha hq
  refine (integral_exp_neg_div_le_chord ha hab).trans ?_
  have hL : Real.log (Real.exp (u + 1 / 40) * Real.pi * (1 / 200))
      - Real.log (Real.exp u * Real.pi * (1 / 200)) = 1 / 40 := by
    rw [hb, Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hk : 1 - Real.exp u * Real.pi * (1 / 200) * (1 / 40)
      / (Real.exp (u + 1 / 40) * Real.pi * (1 / 200) - Real.exp u * Real.pi * (1 / 200))
      = 1 - 1 / 40 * (Real.exp (1 / 40) - 1)⁻¹ := by
    rw [hb]
    have : Real.exp (1 / 40) - 1 ≠ 0 := by linarith
    field_simp
  rw [hL, hk]
  have hneg : Real.exp (-(Real.exp (u + 1 / 40) * Real.pi * (1 / 200)))
      - Real.exp (-(Real.exp u * Real.pi * (1 / 200))) ≤ 0 :=
    sub_nonpos.2 (Real.exp_le_exp.2 (by linarith))
  have := mul_le_mul_of_nonpos_left chord_grid_const hneg
  linarith

/-- **The exponential integral from `1/(100e)` to the grid's first point**, by Taylor's polynomial
of degree `8`. -/
theorem integral_exp_neg_div_le_start {u : ℝ}
    (hu : Real.exp (-1) * (1 / 100) ≤ Real.exp u * Real.pi * (1 / 200)) :
    ∫ s in Real.exp (-1) * (1 / 100)..Real.exp u * Real.pi * (1 / 200), Real.exp (-s) / s
      ≤ u + 1 + Real.log Real.pi - Real.log 2
        + einH8 (Real.exp u * Real.pi * (1 / 200)) - einH8 (Real.exp (-1) * (1 / 100)) := by
  have h := integral_exp_neg_div_le_ein 4 (by positivity) hu
  rw [einPoly_eight, einPoly_eight] at h
  have l2 : Real.log (Real.exp u * Real.pi * (1 / 200)) = u + Real.log Real.pi - Real.log 200 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) Real.pi_ne_zero,
      Real.log_exp, one_div, Real.log_inv]
    ring
  have l1 : Real.log (Real.exp (-1) * (1 / 100)) = -1 - Real.log 100 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_exp, one_div, Real.log_inv]
    ring
  have l3 : Real.log 200 = Real.log 2 + Real.log 100 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [l1, l2, l3] at h
  linarith

/-- **A step along the grid**: from a bound `e` up to `X_u` and a bound `s` on the next piece,
`e + s ≤ e'` bounds the exponential integral up to `X_{u'}`, `u' = u + 1/40`. -/
theorem integral_exp_neg_div_le_next {u u' e s e' : ℝ} (hu' : u + 1 / 40 = u')
    (hu : Real.exp (-1) * (1 / 100) ≤ Real.exp u * Real.pi * (1 / 200))
    (he : ∫ s in Real.exp (-1) * (1 / 100)..Real.exp u * Real.pi * (1 / 200),
      Real.exp (-s) / s ≤ e)
    (hs : Real.exp (-(Real.exp u * Real.pi * (1 / 200))) * (1 / 40)
        + (Real.exp (-(Real.exp u' * Real.pi * (1 / 200)))
          - Real.exp (-(Real.exp u * Real.pi * (1 / 200)))) * 0.012 ≤ s)
    (hee : e + s ≤ e') :
    ∫ s in Real.exp (-1) * (1 / 100)..Real.exp u' * Real.pi * (1 / 200),
      Real.exp (-s) / s ≤ e' := by
  have hπ := Real.pi_pos
  have h0 : 0 < Real.exp (-1) * (1 / 100) := by positivity
  have hle : Real.exp u * Real.pi * (1 / 200) ≤ Real.exp u' * Real.pi * (1 / 200) := by
    rw [← hu']
    have := Real.exp_le_exp.2 (show u ≤ u + 1 / 40 by linarith)
    have hp : (0 : ℝ) ≤ Real.pi * (1 / 200) := by positivity
    nlinarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp_neg_div h0 hu) (intervalIntegrable_exp_neg_div (h0.trans_le hu) hle)
  have hg := integral_exp_neg_div_le_grid u
  rw [hu'] at hg
  linarith

/-! ### The second lobe -/

/-- **The positive half-lobe cells, in numerals**: for `3π/2 ≤ e^ℓ` and `hi ≤ 5π/2`,
`lobeP(5π/2) - lobeP(e^ℓ)` in products. -/
theorem isRestCosBound_exp_pos {ℓ hi B : ℝ} (hlo : 3 * π / 2 ≤ Real.exp ℓ) (hhi : hi ≤ 5 * π / 2)
    (hB : (1 - 2 * (Real.pi * Real.pi) + Real.pi * Real.pi * Real.pi * Real.pi * (2 / 3))
          * (Real.log (Real.pi * (5 / 2)) - ℓ)
        + (Real.pi * 2 - Real.pi * Real.pi * Real.pi * (4 / 3)) * (Real.pi * (5 / 2) - Real.exp ℓ)
        + (Real.pi * Real.pi - 1 / 2) * (Real.pi * Real.pi * (25 / 4) - Real.exp (2 * ℓ)) * (1 / 2)
        - Real.pi * (1 / 3) * (Real.pi * Real.pi * Real.pi * (125 / 8) - Real.exp (3 * ℓ)) * (1 / 3)
        + (Real.pi * Real.pi * Real.pi * Real.pi * (625 / 16) - Real.exp (4 * ℓ)) * (1 / 96)
        ≤ B) :
    IsRestCosBound (Real.exp ℓ) hi B := by
  refine isRestCosBound_second_pos hlo hhi (le_trans (le_of_eq ?_) hB)
  have e3 : Real.exp (3 * ℓ) = Real.exp ℓ ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e4 : Real.exp (4 * ℓ) = Real.exp ℓ ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  unfold lobeP
  rw [Real.log_exp, exp_two_mul_eq, e3, e4, show 5 * π / 2 = Real.pi * (5 / 2) by ring]
  ring

/-- **The second lobe with the constant bound** `P₀ ≤ 0.3237`: for `π/2 ≤ lo` and `hi ≤ 5π/2`
(the negative half-lobe dropped). -/
theorem isRestCosBound_second_const {lo hi : ℝ} (hlo : π / 2 ≤ lo) (hhi : hi ≤ 5 * π / 2) :
    IsRestCosBound lo hi 0.3237 := by
  refine IsRestCosBound.split (m := 3 * π / 2) ?_ ?_
  · refine isRestCosBound_second_neg (N := 0) hlo le_rfl (by simp) (by norm_num) ?_
    rw [mul_zero, zero_add]
    exact lobeP_sub_le
  · exact isRestCosBound_second_pos le_rfl hhi lobeP_sub_le

/-- **The negative half-lobe cells below `π`, in numerals**: for `π/2 ≤ e^{ℓ₁} ≤ e^{ℓ₂} ≤ π`, the
tent's bound at `e^{ℓ₂}` damped at `e^{ℓ₁}`, plus `0.3237`. -/
theorem isRestCosBound_exp_neg_low {ℓ₁ ℓ₂ B : ℝ} (hlo : π / 2 ≤ Real.exp ℓ₁)
    (hhi₁ : Real.exp ℓ₁ ≤ Real.exp ℓ₂) (hhi₂ : Real.exp ℓ₂ ≤ π) (hB0 : 0 ≤ B)
    (hB : Real.exp (-(Real.exp (-ℓ₁) * Real.pi * (3 / 200)))
        * (Real.log Real.pi - ℓ₂ + 2 * Real.exp ℓ₂ * Real.pi⁻¹ - 1 - 3 * Real.log (3 / 2))
      + 0.3237 ≤ B) :
    IsRestCosBound (Real.exp ℓ₁) (Real.exp ℓ₂) B := by
  have hπ := Real.pi_pos
  have hN := integral_cos_div_le_tent_low (hlo.trans hhi₁) hhi₂
  refine isRestCosBound_second_neg hlo (by linarith) hN hB0 (le_trans ?_ hB)
  have e1 : -(1 / 100 / Real.exp ℓ₁) * (3 * π / 2) = -(Real.exp (-ℓ₁) * Real.pi * (3 / 200)) := by
    rw [Real.exp_neg]; field_simp; ring
  have e2 : Real.log π - Real.log (Real.exp ℓ₂) + 2 * Real.exp ℓ₂ / π - 1 - 3 * Real.log (3 / 2)
      = Real.log Real.pi - ℓ₂ + 2 * Real.exp ℓ₂ * Real.pi⁻¹ - 1 - 3 * Real.log (3 / 2) := by
    rw [Real.log_exp]; ring
  rw [e1, e2]
  linarith [lobeP_sub_le]

/-- **The negative half-lobe cells above `π`, in numerals**: for `π/2 ≤ e^{ℓ₁}` and
`π ≤ e^{ℓ₂} ≤ 3π/2`, the tent's bound at `e^{ℓ₂}` damped at `e^{ℓ₁}`, plus `0.3237`. -/
theorem isRestCosBound_exp_neg_high {ℓ₁ ℓ₂ B : ℝ} (hlo : π / 2 ≤ Real.exp ℓ₁)
    (hhi₁ : π ≤ Real.exp ℓ₂) (hhi₂ : Real.exp ℓ₂ ≤ 3 * π / 2) (hB0 : 0 ≤ B)
    (hB : Real.exp (-(Real.exp (-ℓ₁) * Real.pi * (3 / 200)))
        * (-3 * (Real.log (Real.pi * (3 / 2)) - ℓ₂) + 3 - 2 * Real.exp ℓ₂ * Real.pi⁻¹)
      + 0.3237 ≤ B) :
    IsRestCosBound (Real.exp ℓ₁) (Real.exp ℓ₂) B := by
  have hπ := Real.pi_pos
  have hN := integral_cos_div_le_tent_high hhi₁ hhi₂
  refine isRestCosBound_second_neg hlo hhi₂ hN hB0 (le_trans ?_ hB)
  have e1 : -(1 / 100 / Real.exp ℓ₁) * (3 * π / 2) = -(Real.exp (-ℓ₁) * Real.pi * (3 / 200)) := by
    rw [Real.exp_neg]; field_simp; ring
  have e2 : -3 * (Real.log (3 * π / 2) - Real.log (Real.exp ℓ₂)) + 3 - 2 * Real.exp ℓ₂ / π
      = -3 * (Real.log (Real.pi * (3 / 2)) - ℓ₂) + 3 - 2 * Real.exp ℓ₂ * Real.pi⁻¹ := by
    rw [Real.log_exp, show 3 * π / 2 = Real.pi * (3 / 2) by ring]; ring
  rw [e1, e2]
  linarith [lobeP_sub_le]

/-- **The negative half-lobe from `π/2`, in numerals**: for `π/2 ≤ e^{ℓ₂} ≤ π`, the tent's bound
at `e^{ℓ₂}` damped at `π/2` (`e^{-3/100}`), plus `0.3237`. -/
theorem isRestCosBound_neg_pi_div_two {ℓ₂ B : ℝ} (hhi₁ : π / 2 ≤ Real.exp ℓ₂)
    (hhi₂ : Real.exp ℓ₂ ≤ π) (hB0 : 0 ≤ B)
    (hB : Real.exp (-(3 / 100))
        * (Real.log Real.pi - ℓ₂ + 2 * Real.exp ℓ₂ * Real.pi⁻¹ - 1 - 3 * Real.log (3 / 2))
      + 0.3237 ≤ B) :
    IsRestCosBound (π / 2) (Real.exp ℓ₂) B := by
  have hπ := Real.pi_pos
  have hN := integral_cos_div_le_tent_low hhi₁ hhi₂
  refine isRestCosBound_second_neg le_rfl (by linarith) hN hB0 (le_trans ?_ hB)
  have e1 : -(1 / 100 / (π / 2)) * (3 * π / 2) = -(3 / 100) := by field_simp
  have e2 : Real.log π - Real.log (Real.exp ℓ₂) + 2 * Real.exp ℓ₂ / π - 1 - 3 * Real.log (3 / 2)
      = Real.log Real.pi - ℓ₂ + 2 * Real.exp ℓ₂ * Real.pi⁻¹ - 1 - 3 * Real.log (3 / 2) := by
    rw [Real.log_exp]; ring
  rw [e1, e2]
  linarith [lobeP_sub_le]

/-! ### The deep cells' weights -/

/-- `e^{2B + 10⁻¹⁹}(a_j - a_{j+1}) = e^{2B + 10⁻¹⁹ - j/40}(1 - e^{-1/40})`. -/
lemma exp_mul_cell_width_eq (B : ℝ) (j : ℕ) :
    Real.exp (2 * B + 1 / 10 ^ 19) * (hp2CellEnd j - hp2CellEnd (j + 1))
      = Real.exp (2 * B + 1 / 10 ^ 19 - (j : ℝ) / 40) * (1 - Real.exp (-(1 / 40))) := by
  unfold hp2CellEnd
  have e1 : Real.exp (-(((j + 1 : ℕ) : ℝ) / 40))
      = Real.exp (-((j : ℝ) / 40)) * Real.exp (-(1 / 40)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have e2 : Real.exp (2 * B + 1 / 10 ^ 19 - (j : ℝ) / 40)
      = Real.exp (2 * B + 1 / 10 ^ 19) * Real.exp (-((j : ℝ) / 40)) := by
    rw [← Real.exp_add]; congr 1
  rw [e1, e2]
  ring

/-- `e^{2B + 10⁻¹⁹}a_N = e^{2B + 10⁻¹⁹ - N/40}`. -/
lemma exp_mul_cell_end_eq (B : ℝ) (N : ℕ) :
    Real.exp (2 * B + 1 / 10 ^ 19) * hp2CellEnd N
      = Real.exp (2 * B + 1 / 10 ^ 19 - (N : ℝ) / 40) := by
  unfold hp2CellEnd
  rw [← Real.exp_add]
  congr 1

/-- `1 - e^{-1/40} ≤ 0.0246901`. -/
lemma one_sub_exp_neg_fortieth_le : 1 - Real.exp (-(1 / 40)) ≤ 0.0246901 := by
  interval_decide (trust := kernel)

end RMF
