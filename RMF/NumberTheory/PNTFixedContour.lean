/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.LogDerivZetaRect

/-!
# The explicit Chebyshev bound from a fixed contour

`|ψ X - X|` from the five-piece decomposition `SmoothedChebyshevPull1` (PNT+'s
`PrimeNumberTheoremAnd.MediumPNT`) on one fixed contour, `σ₁ = zetaSmallTσ = 1 - 10⁻¹⁶` and
`T₀ = e^{1000}`.  With the smoothing `bumpNu` of `RMF/PNTPlus/MediumPNTExplicit.lean`,
`ψ_ε(X) = I₁ - I₂ + I₃₇ + I₈ + I₉ + 𝓜(1̃_ε)(1)·X`, and

* `ψ_ε - ψ` is bounded by `SmoothedChebyshevCloseExplicit` (`30 log 2 · εX log X`) and
  `𝓜(1̃_ε)(1) - 1` by `MellinOfSmooth1cBound` (`2 log 2 · ε`);
* `I₁`, `I₉` by `I1Bound_of`, `I9Bound_of`, with the strip bound `logDeriv_zeta_le_strip` and the
  bump's Mellin bound `bumpMellin_hyp`;
* `I₂` by `RMF.I2Bound_unif`, which is `I2Bound_of` with its `log⁹` step replaced by a uniform
  bound `B_H` on the lower side, and `I₈` from it by the symmetry `I8I2`;
* `I₃₇` by `RMF.I37Bound_of`, which is `I5Bound_of` on `[-T, T]` instead of `[-3, 3]`.

The proofs of `RMF.I2Bound_unif` and `RMF.I37Bound_of` are adapted from those of `I2Bound_of` and
`I5Bound_of` in `RMF/PNTPlus/MediumPNTExplicit.lean` (PrimeNumberTheoremAnd, Apache 2.0
license).  The inputs on the contour -- holomorphy, the vertical bound `3·10³²` and the horizontal
bound `10¹⁴` -- are `RMF.holo_rect`, `RMF.logDeriv_zeta_le_contourV` and
`RMF.logDeriv_zeta_le_horizontal` (`NumberTheory/LogDerivZetaRect.lean`).

## Main results

* `RMF.abs_psi_sub_le_contour_of`: the bound for any `σ₁ ∈ (0, 1)` and `T > 3`, given holomorphy
  of `ζ'/ζ` on `[σ₁, 2] × [-T, T]` minus `{1}` and bounds `B_V`, `B_H` for it on the left and
  lower sides.
* `RMF.abs_psi_sub_le_fixedContour`: for `X > 3`, `0 < ε < 1` and `Xε > 2`,
  `|ψ X - X| ≤ 30 log 2·εX log X + 2 log 2·εX + 2088·X log X/(εT₀) + 3.3·10¹⁶·X/(εT₀²)
  + 1.81·10³⁴·T₀X^{σ₁}/ε`.
-/

namespace RMF

section PNTFixedContour

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)

open scoped Chebyshev

local notation "𝓜" => mellin

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open ComplexConjugate

open MeasureTheory

/-! ### The horizontal sides -/

/-- **`I₂` under a uniform bound on the lower side**: if `‖ζ'/ζ‖ ≤ B_H` on `[σ₁, 2] - iT`, then
`‖I₂‖ ≤ (1/(2π))·2·C₁B_He·X/(εT²)`: the Mellin bound gives `C₁/(εT²)`, `‖X^s‖ ≤ eX`, and the
segment has length at most `2`.  `I2Bound_of` (PrimeNumberTheoremAnd), with its `log⁹` step
replaced by `B_H`; the proof is adapted from it. -/
lemma I2Bound_unif {SmoothingF : ℝ → ℝ} {σ₁ T B_H : ℝ} (σ₁pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (Tpos : 0 < T)
    (hH : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ B_H)
    {C₁ : ℝ} (C₁pos : 0 < C₁)
    (Mbd : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ C₁ * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₂ SmoothingF ε T X σ₁‖
      ≤ (‖1 / (2 * π * I)‖ * (2 * (C₁ * B_H * rexp 1))) * X / (ε * T ^ 2) := by
  have B_H_nonneg : 0 ≤ B_H := le_trans (norm_nonneg _) (hH σ₁ le_rfl (by linarith))
  set C' : ℝ := C₁ * B_H * rexp 1 with hC'
  have : C' ≥ 0 := by positivity
  intro X X_gt ε ε_pos ε_lt_one
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  unfold I₂
  rw [norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    have : 0 ≤ (Real.log X)⁻¹ := by
      rw [inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    linarith
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T ^ 2) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T ^ 2) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T ^ 2) * 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw [abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
          calc
            1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
            _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T ^ 2) := by ring
  -- Now bound the integrand
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ B_H :=
    hH σ hσ.1.le (le_trans hσ.2 (one_add_inv_log X_gt.le).le)
  -- Then estimate the remaining factors.
  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw [norm_mul]
    _ ≤ B_H * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw [neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith [one_add_inv_log X_gt.le]
      · rw [cpow_def_of_ne_zero]
        · rw [norm_exp, ← ofReal_log, re_ofReal_mul]
          · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, sub_zero]
            rw [← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp,
              ← le_div_iff₀', add_comm, add_div, div_self, one_div]
            · exact hσ.2
            · refine (Real.log_pos ?_).ne.symm
              linarith
            · apply Real.log_pos
              linarith
            · linarith
            · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T ^ 2) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ ^ 2 + (-T) ^ 2 := by
            rw [Complex.normSq_add_mul_I]
          _ ≥ T ^ 2 := by
            rw [neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left this ε_pos.le)

/-- **`I₈` under a uniform bound on the lower side**: `‖I₈‖ = ‖I₂‖` by the symmetry `I8I2`
(PrimeNumberTheoremAnd), so `RMF.I2Bound_unif` applies. -/
lemma I8Bound_unif {SmoothingF : ℝ → ℝ} {σ₁ T B_H : ℝ} (σ₁pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (Tpos : 0 < T)
    (hH : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ B_H)
    {C₁ : ℝ} (C₁pos : 0 < C₁)
    (Mbd : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ C₁ * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₈ SmoothingF ε T X σ₁‖
      ≤ (‖1 / (2 * π * I)‖ * (2 * (C₁ * B_H * rexp 1))) * X / (ε * T ^ 2) := by
  intro X hX ε hε0 hε1
  rw [I8I2 hX, norm_neg, norm_conj]
  exact I2Bound_unif σ₁pos σ₁_lt_one Tpos hH C₁pos Mbd X hX hε0 hε1

/-! ### The vertical side -/

/-- **`I₃₇` under a bound on the vertical side**: if `‖ζ'/ζ‖ ≤ zeta_bound` on `σ₁ + i[-T, T]`,
then `‖I₃₇‖ ≤ (1/(2π))·2T·(1 + |zeta_bound|M/σ₁²)·X^{σ₁}/ε`, the Mellin bound giving
`M/(εσ₁²)` and the segment having length `2T`.  `I5Bound_of` (PrimeNumberTheoremAnd) with
`[-3, 3]` replaced by `[-T, T]`; the proof is adapted from it. -/
lemma I37Bound_of {SmoothingF : ℝ → ℝ} {σ₁ : ℝ} (hσ₁ : σ₁ ∈ Ioo 0 1) {T : ℝ} (hT : 0 ≤ T)
    {zeta_bound : ℝ}
    (zeta_prop : ∀ t : ℝ, |t| ≤ T → ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ zeta_bound)
    {M : ℝ} (M_is_pos : 0 < M)
    (M_bounds_mellin_hard : ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2)
      (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₃₇ SmoothingF ε T X σ₁‖
      ≤ (|π|⁻¹ * 2⁻¹ * (2 * T) * (1 + (σ₁ ^ 2)⁻¹ * |zeta_bound| * M)) * X ^ σ₁ / ε := by
  unfold I₃₇
  unfold SmoothedChebyshevIntegrand
  have mellin_prop : ∀ (t ε : ℝ), 0 < ε → ε < 1 →
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ ≤
        M * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹ :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₁ (by linarith [hσ₁.1]) (σ₁ + t * I)
      (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, le_refl])
      (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]; linarith [hσ₁.2]))
  simp only [mul_inv_rev] at mellin_prop
  set Const := 1 + (σ₁ ^ 2)⁻¹ * |zeta_bound| * M
  set C := |π|⁻¹ * 2⁻¹ * (2 * T) * Const
  intro X X_gt ε ε_pos ε_lt_one
  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one
  have U : 0 < σ₁ ^ 2 := by
    exact sq_pos_of_pos (by linarith [hσ₁.1])
  have easy_bound : ∀ (t : ℝ), (‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹ ≤ (σ₁ ^ 2)⁻¹ := by
    intro t
    rw [inv_le_inv₀]
    · rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      ring_nf
      simp only [le_add_iff_nonneg_right]
      exact zpow_two_nonneg t
    · rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      ring_nf
      positivity
    positivity
  have T1 : ∀ (t : ℝ), t ∈ uIoc (-T) T →
      ‖-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x))
        (↑σ₁ + ↑t * I) * (↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₁ := by
    intro t hyp_t
    have ht : |t| ≤ T := by
      rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at hyp_t
      exact abs_le.mpr ⟨hyp_t.1.le, hyp_t.2⟩
    have Z := by
      calc
        ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            (𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)) *
            (↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ =
            ‖-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
              ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
              ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
          simp only [Complex.norm_mul, Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
              ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
              ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
          simp only [Complex.norm_div, norm_neg, le_refl]
        _ ≤ zeta_bound * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
              ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
          have U := zeta_prop t ht
          simp only [Complex.norm_div] at U
          simp only [Complex.norm_div, ge_iff_le]
          linear_combination U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖
        _ ≤ |zeta_bound| * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
              ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
          have U : zeta_bound ≤ |zeta_bound| := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖)
        _ ≤ |zeta_bound| * M * ((‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) *
              ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
          have U := mellin_bound t
          linear_combination (|zeta_bound|) * U * ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖
        _ ≤ |zeta_bound| * M * (σ₁ ^ 2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
          linear_combination (|zeta_bound| * M * easy_bound t * ε⁻¹ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖)
        _ = |zeta_bound| * M * (σ₁ ^ 2)⁻¹ * ε⁻¹ * X ^ (σ₁) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₁ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left,
            ε_pos]
          positivity
    exact Z
  -- Now want to apply the triangle inequality
  -- and bound everything trivially
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]
  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₁ * |T + T|) = C * X ^ σ₁ / ε := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T + T)]
    unfold C
    ring_nf
  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

/-! ### The assembly -/

/-- The constant of `I1Bound_of` and `I9Bound_of` at the bump `bumpNu` and the strip bound
`logDeriv_zeta_le_strip`: `e·2(log 4 + 5)·bumpMellinC/(2π) ≈ 1043.72`. -/
noncomputable def contourC₁ : ℝ :=
  |π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC)

/-- The constant of `RMF.I2Bound_unif` and `RMF.I8Bound_unif` at the bump, for a bound `B_H` on
the lower side: `bumpMellinC·B_H·e/π`. -/
noncomputable def contourC₂ (B_H : ℝ) : ℝ :=
  ‖1 / (2 * π * I)‖ * (2 * (bumpMellinC * B_H * rexp 1))

/-- The constant of `RMF.I37Bound_of` at the bump, for a bound `B_V` on the vertical side
`σ₁ + i[-T, T]`: `(T/π)(1 + |B_V|·bumpMellinC/σ₁²)`. -/
noncomputable def contourC₃₇ (σ₁ T B_V : ℝ) : ℝ :=
  |π|⁻¹ * 2⁻¹ * (2 * T) * (1 + (σ₁ ^ 2)⁻¹ * |B_V| * bumpMellinC)

/-- **`|ψ X - X|` from a contour `σ₁ + i[-T, T]`, given the bounds on it.**  If `ζ'/ζ` is
holomorphic on `[σ₁, 2] × [-T, T]` minus `{1}`, `‖ζ'/ζ‖ ≤ B_V` on its left side and `≤ B_H` on its
lower side, then for `X > 3`, `0 < ε < 1` and `Xε > 2`: `|ψ X - X| ≤ 30 log 2·εX log X
+ 2 log 2·εX + 2c₁X log X/(εT) + 2c₂X/(εT²) + c₃₇X^{σ₁}/ε`.  `SmoothedChebyshevPull1` splits
`ψ_ε(X) - 𝓜(1̃_ε)(1)·X` into the five pieces, bounded by `I1Bound_of`, `I9Bound_of`,
`RMF.I2Bound_unif`, `RMF.I8Bound_unif` and `RMF.I37Bound_of`; `SmoothedChebyshevCloseExplicit`
and `MellinOfSmooth1cBound` give the first two terms. -/
theorem abs_psi_sub_le_contour_of {σ₁ T B_V B_H : ℝ} (σ₁pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (T_gt : 3 < T)
    (holo : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (hV : ∀ t : ℝ, |t| ≤ T → ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ B_V)
    (hH : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ B_H) :
    ∀ X ε : ℝ, 3 < X → 0 < ε → ε < 1 → 2 < X * ε →
      |ψ X - X| ≤ 30 * Real.log 2 * ε * X * Real.log X + 2 * Real.log 2 * ε * X
        + 2 * contourC₁ * X * Real.log X / (ε * T) + 2 * contourC₂ B_H * X / (ε * T ^ 2)
        + contourC₃₇ σ₁ T B_V * X ^ σ₁ / ε := by
  intro X ε X_gt ε_pos ε_lt_one hXε
  have hX0 : 0 < X := by linarith
  have T_pos : 0 < T := by linarith
  -- the five pieces, and the two smoothing errors
  have hpull := SmoothedChebyshevPull1 (SmoothingF := bumpNu) ε_pos ε_lt_one X X_gt T_pos
    σ₁pos σ₁_lt_one holo bumpNu_support bump_nonneg bump_massOne bumpNu_contDiff
  have hclose := SmoothedChebyshevCloseExplicit bumpNu_contDiff bumpNu_support bump_nonneg
    bump_massOne X X_gt ε ε_pos ε_lt_one hXε
  have hmain := MellinOfSmooth1cBound bumpNu_contDiff bumpNu_support bump_nonneg bump_massOne
    ε_pos ε_lt_one.le
  have h1 : ‖I₁ bumpNu ε X T‖ ≤ contourC₁ * X * Real.log X / (ε * T) :=
    I1Bound_of bumpNu_support bumpNu_contDiff bump_nonneg bump_massOne bumpMellinC_pos
      bumpMellin_hyp zetaTrivK_pos logDeriv_zeta_le_strip ε ε_pos ε_lt_one X X_gt T_gt
  have h9 : ‖I₉ bumpNu ε X T‖ ≤ contourC₁ * X * Real.log X / (ε * T) :=
    I9Bound_of bumpNu_support bumpNu_contDiff bump_nonneg bump_massOne bumpMellinC_pos
      bumpMellin_hyp zetaTrivK_pos logDeriv_zeta_le_strip ε_pos ε_lt_one X X_gt T_gt
  have h2 : ‖I₂ bumpNu ε T X σ₁‖ ≤ contourC₂ B_H * X / (ε * T ^ 2) :=
    I2Bound_unif σ₁pos σ₁_lt_one T_pos hH bumpMellinC_pos bumpMellin_hyp X X_gt ε_pos ε_lt_one
  have h8 : ‖I₈ bumpNu ε T X σ₁‖ ≤ contourC₂ B_H * X / (ε * T ^ 2) :=
    I8Bound_unif σ₁pos σ₁_lt_one T_pos hH bumpMellinC_pos bumpMellin_hyp X X_gt ε_pos ε_lt_one
  have h37 : ‖I₃₇ bumpNu ε T X σ₁‖ ≤ contourC₃₇ σ₁ T B_V * X ^ σ₁ / ε :=
    I37Bound_of ⟨σ₁pos, σ₁_lt_one⟩ T_pos.le hV bumpMellinC_pos bumpMellin_hyp X X_gt ε_pos
      ε_lt_one
  -- `ψ X - X = (ψ - ψ_ε) + (I₁ - I₂ + I₃₇ + I₈ + I₉) + (𝓜(1̃_ε)(1) - 1)·X`
  have key : ((ψ X - X : ℝ) : ℂ) = -(SmoothedChebyshev bumpNu ε X - ψ X)
      + (I₁ bumpNu ε X T - I₂ bumpNu ε T X σ₁ + I₃₇ bumpNu ε T X σ₁ + I₈ bumpNu ε T X σ₁
        + I₉ bumpNu ε X T)
      + (𝓜 (fun x ↦ (Smooth1 bumpNu ε x : ℂ)) 1 - 1) * X := by
    rw [hpull]
    push_cast
    ring
  have hM : ‖(𝓜 (fun x ↦ (Smooth1 bumpNu ε x : ℂ)) 1 - 1) * X‖ ≤ 2 * Real.log 2 * ε * X := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0.le]
    exact mul_le_mul_of_nonneg_right hmain hX0.le
  have n0 := norm_add₃_le (a := -(SmoothedChebyshev bumpNu ε X - ψ X))
    (b := I₁ bumpNu ε X T - I₂ bumpNu ε T X σ₁ + I₃₇ bumpNu ε T X σ₁ + I₈ bumpNu ε T X σ₁
      + I₉ bumpNu ε X T) (c := (𝓜 (fun x ↦ (Smooth1 bumpNu ε x : ℂ)) 1 - 1) * X)
  have n1 := norm_add_le (I₁ bumpNu ε X T - I₂ bumpNu ε T X σ₁ + I₃₇ bumpNu ε T X σ₁
    + I₈ bumpNu ε T X σ₁) (I₉ bumpNu ε X T)
  have n2 := norm_add_le (I₁ bumpNu ε X T - I₂ bumpNu ε T X σ₁ + I₃₇ bumpNu ε T X σ₁)
    (I₈ bumpNu ε T X σ₁)
  have n3 := norm_add_le (I₁ bumpNu ε X T - I₂ bumpNu ε T X σ₁) (I₃₇ bumpNu ε T X σ₁)
  have n4 := norm_sub_le (I₁ bumpNu ε X T) (I₂ bumpNu ε T X σ₁)
  rw [norm_neg] at n0
  have habs : |ψ X - X| = ‖((ψ X - X : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have e1 : 2 * contourC₁ * X * Real.log X / (ε * T)
      = contourC₁ * X * Real.log X / (ε * T) + contourC₁ * X * Real.log X / (ε * T) := by ring
  have e2 : 2 * contourC₂ B_H * X / (ε * T ^ 2)
      = contourC₂ B_H * X / (ε * T ^ 2) + contourC₂ B_H * X / (ε * T ^ 2) := by ring
  rw [habs, key]
  linarith

/-! ### The fixed contour `σ₁ = 1 - 10⁻¹⁶`, `T₀ = e^{1000}` -/

/-- `bumpMellinC = 81·bumpC/2 ≤ 188.9` (it is `≈ 188.882`), from `log 2 > 0.6931471803`. -/
lemma bumpMellinC_le_sharp : bumpMellinC ≤ 1889 / 10 := by
  rw [bumpMellinC_eq]
  have hb : bumpC ≤ 3778 / 810 := by
    rw [bumpC, inv_le_comm₀ bumpDen_pos (by norm_num)]
    have h := Real.log_two_gt_d9
    rw [log_four]
    norm_num at h ⊢
    linarith
  linarith

/-- `1/(2π) ≤ 0.15916`, from `π > 3.141592`. -/
lemma abs_pi_inv_half_le_sharp : |π|⁻¹ * 2⁻¹ ≤ 15916 / 100000 := by
  rw [abs_of_pos Real.pi_pos, ← mul_inv, inv_le_comm₀ (by positivity) (by norm_num)]
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith

/-- `‖1/(2πi)‖ = 1/(2π)`. -/
lemma norm_one_div_two_pi_I : ‖(1 : ℂ) / (2 * π * I)‖ = |π|⁻¹ * 2⁻¹ := by
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, mul_one, one_div, mul_inv, mul_comm]

/-- `contourC₁ ≤ 1044` (it is `≈ 1043.72`). -/
lemma contourC₁_le : contourC₁ ≤ 1044 := by
  have hπ := abs_pi_inv_half_le_sharp
  have he : Real.exp 1 ≤ 27182818286 / 10 ^ 10 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hK : 2 * (zetaTrivC + 1) ≤ 127725887232 / 10 ^ 10 := by
    have := Real.log_two_lt_d9
    unfold zetaTrivC
    rw [log_four]
    norm_num at this ⊢
    linarith
  have hM := bumpMellinC_le_sharp
  have hM0 := bumpMellinC_pos
  have hK0 : 0 ≤ 2 * (zetaTrivC + 1) := zetaTrivK_pos.le
  have hin : Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC
      ≤ 27182818286 / 10 ^ 10 * (127725887232 / 10 ^ 10) * (1889 / 10) :=
    mul_le_mul (mul_le_mul he hK hK0 (by norm_num)) hM hM0.le (by norm_num)
  have h0 : 0 ≤ Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC := by positivity
  unfold contourC₁
  calc |π|⁻¹ * 2⁻¹ * (Real.exp 1 * (2 * (zetaTrivC + 1)) * bumpMellinC)
      ≤ 15916 / 100000 * (27182818286 / 10 ^ 10 * (127725887232 / 10 ^ 10) * (1889 / 10)) :=
        mul_le_mul hπ hin h0 (by norm_num)
    _ ≤ 1044 := by norm_num

/-- `2·contourC₂ 10¹⁴ ≤ 3.3·10¹⁶` (`contourC₂ 10¹⁴ ≈ 1.6343·10¹⁶`). -/
lemma two_mul_contourC₂_le : 2 * contourC₂ (10 ^ 14) ≤ 33 * 10 ^ 15 := by
  have hπ := abs_pi_inv_half_le_sharp
  have he : Real.exp 1 ≤ 27182818286 / 10 ^ 10 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hM := bumpMellinC_le_sharp
  have hM0 := bumpMellinC_pos
  have hin : 2 * (bumpMellinC * 10 ^ 14 * rexp 1)
      ≤ 2 * (1889 / 10 * 10 ^ 14 * (27182818286 / 10 ^ 10)) := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hM (by norm_num : (0 : ℝ) ≤ 10 ^ 14)) he
      (Real.exp_pos 1).le (by norm_num)
    linarith
  have h0 : 0 ≤ 2 * (bumpMellinC * 10 ^ 14 * rexp 1) := by positivity
  unfold contourC₂
  rw [norm_one_div_two_pi_I]
  have := mul_le_mul hπ hin h0 (by norm_num)
  calc 2 * (|π|⁻¹ * 2⁻¹ * (2 * (bumpMellinC * 10 ^ 14 * rexp 1)))
      ≤ 2 * (15916 / 100000 * (2 * (1889 / 10 * 10 ^ 14 * (27182818286 / 10 ^ 10)))) := by
        linarith
    _ ≤ 33 * 10 ^ 15 := by norm_num

/-- `contourC₃₇ (1 - 10⁻¹⁶) T (3·10³²) ≤ 1.81·10³⁴·T` for `T ≥ 0` (the constant is
`≈ 1.8037·10³⁴`). -/
lemma contourC₃₇_le {T : ℝ} (hT : 0 ≤ T) :
    contourC₃₇ zetaSmallTσ T (3 * 10 ^ 32) ≤ 181 * 10 ^ 32 * T := by
  have hπ := abs_pi_inv_half_le_sharp
  have hM := bumpMellinC_le_sharp
  have hM0 := bumpMellinC_pos
  have hσ : (zetaSmallTσ ^ 2)⁻¹ ≤ 10001 / 10000 := by
    have hσv : zetaSmallTσ = 1 - (1 / 10 : ℝ) ^ 16 := rfl
    rw [inv_le_comm₀ (by rw [hσv]; norm_num) (by norm_num), hσv]
    norm_num
  have habs : |(3 : ℝ) * 10 ^ 32| = 3 * 10 ^ 32 := abs_of_pos (by norm_num)
  have hin : 1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ 32| * bumpMellinC
      ≤ 1 + 10001 / 10000 * (3 * 10 ^ 32) * (1889 / 10) := by
    rw [habs]
    have := mul_le_mul (mul_le_mul_of_nonneg_right hσ (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 32)) hM
      hM0.le (by norm_num)
    linarith
  have h0 : 0 ≤ 1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ 32| * bumpMellinC := by positivity
  have key : |π|⁻¹ * 2⁻¹ * (1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ 32| * bumpMellinC)
      ≤ 15916 / 100000 * (1 + 10001 / 10000 * (3 * 10 ^ 32) * (1889 / 10)) :=
    mul_le_mul hπ hin h0 (by norm_num)
  have hnum : 2 * (15916 / 100000 * (1 + 10001 / 10000 * (3 * 10 ^ 32) * (1889 / 10)))
      ≤ (181 * 10 ^ 32 : ℝ) := by norm_num
  unfold contourC₃₇
  calc |π|⁻¹ * 2⁻¹ * (2 * T) * (1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ 32| * bumpMellinC)
      = 2 * (|π|⁻¹ * 2⁻¹ * (1 + (zetaSmallTσ ^ 2)⁻¹ * |(3 : ℝ) * 10 ^ 32| * bumpMellinC)) *
          T := by ring
    _ ≤ 2 * (15916 / 100000 * (1 + 10001 / 10000 * (3 * 10 ^ 32) * (1889 / 10))) * T := by
        gcongr
    _ ≤ 181 * 10 ^ 32 * T := mul_le_mul_of_nonneg_right hnum hT

/-- **The explicit Chebyshev bound from the fixed contour** `σ₁ = zetaSmallTσ = 1 - 10⁻¹⁶`,
`T₀ = e^{1000}`: for `X > 3`, `0 < ε < 1` and `Xε > 2`,
`|ψ X - X| ≤ 30 log 2·εX log X + 2 log 2·εX + 2088·X log X/(εT₀) + 3.3·10¹⁶·X/(εT₀²)
+ 1.81·10³⁴·T₀X^{σ₁}/ε`.  `RMF.abs_psi_sub_le_contour_of` with its hypotheses discharged by
`RMF.holo_rect`, `RMF.logDeriv_zeta_le_contourV` with `B_V = 3·10³²` and
`RMF.logDeriv_zeta_le_horizontal` with `B_H = 10¹⁴`, and the constants `c₁ ≈ 1043.72 ≤ 1044`
(`I₁`, `I₉`), `c₂ ≈ 1.6343·10¹⁶` (`I₂`, `I₈`), `c₃₇ ≈ 1.8037·10³⁴·T₀ ≤ 1.81·10³⁴·T₀`. -/
theorem abs_psi_sub_le_fixedContour : ∀ X ε : ℝ, 3 < X → 0 < ε → ε < 1 → 2 < X * ε →
    |ψ X - X| ≤ 30 * Real.log 2 * ε * X * Real.log X + 2 * Real.log 2 * ε * X
      + 2088 * X * Real.log X / (ε * Real.exp 1000)
      + 33 * 10 ^ 15 * X / (ε * Real.exp 1000 ^ 2)
      + 181 * 10 ^ 32 * Real.exp 1000 * X ^ zetaSmallTσ / ε := by
  intro X ε X_gt ε_pos ε_lt_one hXε
  have hT : (3 : ℝ) < Real.exp 1000 := by
    have := Real.add_one_le_exp (1000 : ℝ)
    linarith
  have h := abs_psi_sub_le_contour_of zetaSmallTσ_pos zetaSmallTσ_lt_one hT holo_rect
    logDeriv_zeta_le_contourV (fun σ hσ _ ↦ (logDeriv_zeta_le_horizontal σ hσ).1)
    X ε X_gt ε_pos ε_lt_one hXε
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hE : 0 < Real.exp 1000 := Real.exp_pos 1000
  have e1 : 2 * contourC₁ * X * Real.log X / (ε * Real.exp 1000)
      ≤ 2088 * X * Real.log X / (ε * Real.exp 1000) := by
    have h2 : 2 * contourC₁ ≤ 2088 := by linarith [contourC₁_le]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hX0.le) hlog) (by positivity)
  have e2 : 2 * contourC₂ (10 ^ 14) * X / (ε * Real.exp 1000 ^ 2)
      ≤ 33 * 10 ^ 15 * X / (ε * Real.exp 1000 ^ 2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right two_mul_contourC₂_le hX0.le)
      (by positivity)
  have e3 : contourC₃₇ zetaSmallTσ (Real.exp 1000) (3 * 10 ^ 32) * X ^ zetaSmallTσ / ε
      ≤ 181 * 10 ^ 32 * Real.exp 1000 * X ^ zetaSmallTσ / ε :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (contourC₃₇_le hE.le) (Real.rpow_nonneg hX0.le _))
      ε_pos.le
  linarith

end PNTFixedContour

end RMF
