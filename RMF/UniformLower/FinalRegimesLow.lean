/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.FinalCellsLow
import RMF.UniformLower.SmallXBounds

/-!
# The final assembly below `½` in the low range `67.17 ≤ log log x ≤ 2100`

For a Rademacher family, `x ≥ exp(e^{67.17})` with `Λ = log log x ≤ 2100` and `0 < q < ½`, the
first conjunct of `RMF.weighted_rademacher_moments_lower_uniform_explicit_every_x` on this range
(`RMF.le_integral_rpow_belowHalfLow`).  With `δ = 1 - 2q` and `m = min{Λ, δ⁻¹}`, four regimes:

* **F** (`RMF.le_integral_rpow_floorRegimeLow`), wherever `RMF.PhiFLow q Λ ≥ 10⁻¹⁰`: the floor
  `2^{-δ}3^{-(1-q)}(0.49/log x)^q` (`RMF.le_sum_inv_largePrimeSet_half_classical`);
* **B1** (`RMF.le_integral_rpow_mainB1RegimeLow`), at a rung `r₀ ≥ 35` with
  `r₀ + 21 ≤ Λ - log(400V′)` and `RMF.PhiB1Low q Λ r₀ ≥ 10⁻¹⁰`: the reduction at the tilt
  `V′ = Λ + 24/q` with the window covering of `RMF.isWindowCovering_of_classical`, the main term on
  the one scale `k = 21` of a tube of `T - 21 ≥ r₀` blocks, the subtracted term by Jensen,
  `e^{-24}(1.195π/V′)^q ≤ e^{-24}Λ^{-q/2}` (`RMF.exists_level_belowHalfLow`);
* **B2**, `9/20 ≤ q < ½` and `δΛ ≥ 18` (`RMF.le_integral_rpow_mainB2RegimeLow`): the same on the
  scales `21 ≤ k ≤ 20 + min(K_max(q), T - 55)`, counted as `m/2`, and `RMF.PhiB2Low_ge`;
* **NH**, `δΛ ≤ 18` (`RMF.le_integral_rpow_nearHalfRegimeLow`): Hölder, `(1 + log x)^{-δ}`
  (`RMF.le_integral_rpow_weightedRademacherSum_holder`), and `RMF.nh_num_low`.

For `q ≤ 9/20` the certificates of `RMF.finalCellsLow_spec` give F or B1 at a rung.  In B1 and B2
`δΛ ≥ 1`, so `m = δ⁻¹` exactly and the subtracted and error terms keep their factor `δ`.  The
analysis (the integrals) and the arithmetic are kept apart.
-/

open MeasureTheory

namespace RMF

/-! ### The range and `min{Λ, (1-2q)⁻¹}` -/

/-- **The range `x ≥ exp(e^{67.17})`**: `Λ = log log x ≥ 67.17`, `log x ≥ e^{67.17}`,
`x ≥ e^{100}`, `x ≥ exp(10²⁰)` and `RMF.IsWindowCovering x` (`RMF.isWindowCovering_of_classical`:
`2·10²⁰ + 2 ≤ e^{67.17}`). -/
theorem loglog_facts_of_low {x : ℝ} (hx : Real.exp (Real.exp 67.17) ≤ x) :
    67.17 ≤ Real.log (Real.log x) ∧ Real.exp 67.17 ≤ Real.log x ∧ Real.exp 100 ≤ x
      ∧ Real.exp (10 ^ 20) ≤ x ∧ IsWindowCovering x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 67.17 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hΛ : 67.17 ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL)).2 hL
  have he : (2 * 10 ^ 20 + 2 : ℝ) ≤ Real.exp 67.17 := by interval_decide (trust := kernel)
  have h100 : (100 : ℝ) ≤ Real.exp 67.17 := le_trans (by norm_num) he
  have h20 : (10 ^ 20 : ℝ) ≤ Real.exp 67.17 := le_trans (by norm_num) he
  exact ⟨hΛ, hL, le_trans (Real.exp_le_exp.2 h100) hx, le_trans (Real.exp_le_exp.2 h20) hx,
    isWindowCovering_of_classical x (le_trans (Real.exp_le_exp.2 he) hx)⟩

/-- `(1-2q)min{Λ, (1-2q)⁻¹} ≤ 1` for `q < ½`. -/
lemma one_sub_two_mul_mul_min_le {q Λ : ℝ} (hq : q < 1 / 2) :
    (1 - 2 * q) * min Λ (1 - 2 * q)⁻¹ ≤ 1 := by
  have hδ : 0 < 1 - 2 * q := by linarith
  calc (1 - 2 * q) * min Λ (1 - 2 * q)⁻¹ ≤ (1 - 2 * q) * (1 - 2 * q)⁻¹ :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
    _ = 1 := mul_inv_cancel₀ hδ.ne'

/-- **The saving `1 - 2q`**: `(1-2q)min{Λ, (1-2q)⁻¹} = 1` for `q < ½` and `(1-2q)Λ ≥ 1`, where
`(1-2q)⁻¹ ≤ Λ` (`min_eq_right`). -/
lemma one_sub_two_mul_mul_min_eq {q Λ : ℝ} (hq : q < 1 / 2) (h : 1 ≤ (1 - 2 * q) * Λ) :
    (1 - 2 * q) * min Λ (1 - 2 * q)⁻¹ = 1 := by
  have hδ : 0 < 1 - 2 * q := by linarith
  have hm : (1 - 2 * q)⁻¹ ≤ Λ := by
    calc (1 - 2 * q)⁻¹ = (1 - 2 * q)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Λ) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hδ.le)
      _ = Λ := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
  rw [min_eq_right hm, mul_inv_cancel₀ hδ.ne']

/-- `log(400(Λ + 24/q)) ≤ 14` for `q ≥ 9/20` and `0 ≤ Λ ≤ 2100`: `400(2100 + 160/3) ≤ e^{14}`. -/
lemma log_four_hundred_mul_le_fourteen {q Λ : ℝ} (hq : 9 / 20 ≤ q) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ 2100) : Real.log (400 * (Λ + 24 / q)) ≤ 14 := by
  have hq0 : 0 < q := by linarith
  have h24 : 24 / q ≤ 160 / 3 := by
    rw [div_le_iff₀ hq0]
    linarith
  have h24' : 0 < 24 / q := div_pos (by norm_num) hq0
  have he : (861334 : ℝ) ≤ Real.exp 14 := by interval_decide (trust := kernel)
  rw [Real.log_le_iff_le_exp (by positivity)]
  linarith

/-! ### Arithmetic -/

/-- **F's arithmetic**: for `q < ½`, `L > 0` with `Λ = log L > 0` and `PhiFLow(q, Λ) ≥ 10⁻¹⁰`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ 2^{-(1-2q)}3^{-(1-q)}(0.49/L)^q`: `L^{-q} = e^{-qΛ}` and
`(1-2q)min{Λ, (1-2q)⁻¹} ≤ 1`. -/
lemma floor_regime_arith_low {q L : ℝ} (hq : q < 1 / 2) (hL : 0 < L)
    (hΛ : 0 < Real.log L) (hF : 1 / 10 ^ 10 ≤ PhiFLow q (Real.log L)) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / (100 * L)) ^ q := by
  have hδ : 0 < 1 - 2 * q := by linarith
  have hm0 : 0 ≤ min (Real.log L) (1 - 2 * q)⁻¹ := le_min hΛ.le (inv_nonneg.2 hδ.le)
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ.le _
  have hsplit : Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2)) = 1 := by
    rw [← Real.rpow_add hΛ, add_neg_cancel, Real.rpow_zero]
  have hLq : L ^ (-q) = Real.exp (-(q * Real.log L)) := by
    rw [Real.rpow_def_of_pos hL]
    ring_nf
  have h49 : (49 / (100 * L)) ^ q = (49 / 100 : ℝ) ^ q * L ^ (-q) := by
    rw [← div_div, Real.div_rpow (by norm_num) hL.le, Real.rpow_neg hL.le, div_eq_mul_inv]
  have hA0 : 0 ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / 100 : ℝ) ^ q
      * Real.exp (-(q * Real.log L)) := by positivity
  have hdm := one_sub_two_mul_mul_min_le (Λ := Real.log L) hq
  calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ PhiFLow q (Real.log L) * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_right hF (mul_nonneg hm0 hg0)
    _ = (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / 100 : ℝ) ^ q
          * Real.exp (-(q * Real.log L)) * ((1 - 2 * q) * min (Real.log L) (1 - 2 * q)⁻¹)
          * (Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2))) := by
        unfold PhiFLow
        ring
    _ ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / 100 : ℝ) ^ q
          * Real.exp (-(q * Real.log L)) * 1 * 1 := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdm hA0) zero_le_one
    _ = _ := by
        rw [h49, hLq]
        ring

/-- **The error term in the low range**: `cErrD(q)L^{-q} ≤ errBLow(q, Λ)min{Λ, (1-2q)⁻¹}Λ^{-q/2}`
for `q < ½`, `Λ = log L > 0` and `(1-2q)Λ ≥ 1`, with equality: the min is `(1-2q)⁻¹`. -/
lemma cErrD_mul_rpow_le_errBLow {q L : ℝ} (hq : q < 1 / 2) (hL : 0 < L) (hΛ : 0 < Real.log L)
    (hδΛ : 1 ≤ (1 - 2 * q) * Real.log L) :
    cErrD q * L ^ (-q)
      ≤ errBLow q (Real.log L) * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) := by
  have hsplit : Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2)) = 1 := by
    rw [← Real.rpow_add hΛ, add_neg_cancel, Real.rpow_zero]
  have hLq : L ^ (-q) = Real.exp (-(q * Real.log L)) := by
    rw [Real.rpow_def_of_pos hL]
    ring_nf
  have hdm := one_sub_two_mul_mul_min_eq hq hδΛ
  refine le_of_eq ?_
  calc cErrD q * L ^ (-q) = cErrD q * Real.exp (-(q * Real.log L)) * 1 * 1 := by
        rw [hLq, mul_one, mul_one]
    _ = cErrD q * Real.exp (-(q * Real.log L)) * ((1 - 2 * q) * min (Real.log L) (1 - 2 * q)⁻¹)
          * (Real.log L ^ (q / 2) * Real.log L ^ (-(q / 2))) := by rw [hdm, hsplit]
    _ = _ := by
        unfold errBLow
        ring

/-- **The subtracted term at the tilt `V′ = Λ + 24/q`, absorbed**: for `0 < q < ½` and `L > 0`
with `Λ = log L ≥ 67.17` and `(1-2q)Λ ≥ 1`,
`e^{-V′q}L^{-q}(1.195πL²/V′)^q ≤ e^{-24}(1-2q)min{Λ, (1-2q)⁻¹}Λ^{-q/2}`: the exponent is
`-24 + q(log(1.195π) - log V′)`, `log(1.195π) + (1/2)log Λ ≤ log Λ ≤ log V′`, and the min is
`(1-2q)⁻¹`. -/
lemma jensen_term_le_low {q L : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) (hL : 0 < L)
    (hΛ : 67.17 ≤ Real.log L) (hδΛ : 1 ≤ (1 - 2 * q) * Real.log L) :
    Real.exp (-((Real.log L + 24 / q) * q)) * L ^ (-q)
        * (1.195 * Real.pi * L ^ 2 / (Real.log L + 24 / q)) ^ q
      ≤ Real.exp (-24)
        * ((1 - 2 * q) * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have h24 : 0 < 24 / q := div_pos (by norm_num) hq0
  have hV0 : 0 < Real.log L + 24 / q := by linarith
  have hVq : (Real.log L + 24 / q) * q = q * Real.log L + 24 := by
    rw [add_mul, div_mul_cancel₀ _ hq0.ne']
    ring
  have hB0 : 0 < 1.195 * Real.pi * L ^ 2 / (Real.log L + 24 / q) := by positivity
  have hlogB : Real.log (1.195 * Real.pi * L ^ 2 / (Real.log L + 24 / q))
      = Real.log (1.195 * Real.pi) + 2 * Real.log L - Real.log (Real.log L + 24 / q) := by
    rw [Real.log_div (by positivity) hV0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have hπ : Real.log (1.195 * Real.pi) ≤ 1.33 := by
    have h1 : Real.log (1.195 * Real.pi) ≤ Real.log (1.195 * 3.1416) :=
      Real.log_le_log (by positivity) (by linarith [Real.pi_lt_d4])
    have h2 : Real.log (1.195 * 3.1416) ≤ 1.33 := by interval_decide (trust := kernel)
    linarith
  have h67 : (4.2 : ℝ) ≤ Real.log 67.17 := by interval_decide (trust := kernel)
  have hlogΛ : Real.log 67.17 ≤ Real.log (Real.log L) := Real.log_le_log (by norm_num) hΛ
  have hlogV : Real.log (Real.log L) ≤ Real.log (Real.log L + 24 / q) :=
    Real.log_le_log hΛ0 (by linarith)
  have hbr : Real.log (1.195 * Real.pi) - Real.log (Real.log L + 24 / q)
      + 1 / 2 * Real.log (Real.log L) ≤ 0 := by linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0.le
  have hdm := one_sub_two_mul_mul_min_eq hq hδΛ
  rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hB0, hlogB, hVq, ← Real.exp_add,
    ← Real.exp_add]
  calc Real.exp (-(q * Real.log L + 24) + Real.log L * -q
        + (Real.log (1.195 * Real.pi) + 2 * Real.log L - Real.log (Real.log L + 24 / q)) * q)
      ≤ Real.exp (-24 + Real.log (Real.log L) * -(q / 2)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-24) * Real.log L ^ (-(q / 2)) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hΛ0]
    _ = Real.exp (-24)
          * ((1 - 2 * q) * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))) := by
        rw [← mul_assoc (1 - 2 * q), hdm, one_mul]

/-- **Below `½` in the low range, the three terms combined**: the reduction
`cRed·L^{-q}I - cJ·e·L^{-q}I_J - cErrD·L^{-q} ≤ E`, the main term `A·S ≤ L^{-q}I`, Jensen
`I_J ≤ B`, the subtracted term `e·L^{-q}B ≤ e^{-24}·δ·m·g` and the error
`cErrD·L^{-q} ≤ errB·m·g` give `cRed·A·S - (δ·cJ·e^{-24} + errB)·m·g ≤ E`. -/
lemma belowHalfLow_combine {E Im Is S cR cJ' cE A Lm e B δ m g eB : ℝ}
    (hred : cR * (Lm * Im) - cJ' * e * Lm * Is - cE * Lm ≤ E)
    (hm5 : A * S ≤ Lm * Im) (hcR : 0 ≤ cR) (hJ : Is ≤ B) (hcJ : 0 ≤ cJ')
    (hcJe : 0 ≤ cJ' * e * Lm) (hsub : e * Lm * B ≤ Real.exp (-24) * (δ * (m * g)))
    (hE : cE * Lm ≤ eB * (m * g)) :
    cR * (A * S) - (δ * cJ' * Real.exp (-24) + eB) * (m * g) ≤ E := by
  have h1 := mul_le_mul_of_nonneg_left hm5 hcR
  have h2 := mul_le_mul_of_nonneg_left hJ hcJe
  have h3 := mul_le_mul_of_nonneg_left hsub hcJ
  linarith

/-- **B1's main term in the low range**: with the one scale `k = 21` on a tube of
`T - 21 ≥ r₀ ≥ 35` blocks and `T ≤ Λ`, `mainB1Low(q, qΛ, r₀)·min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤
cRed(q)·2^{2q-1}(G/(2V′))^q·∑_{k=21}Γ·N·(T-k)^{-q/2}`, `V′ = Λ + 24/q`:
`(1-2q)min{Λ, (1-2q)⁻¹} ≤ 1`, `Γ` nondecreasing in the tube's length
(`RMF.monotone_perScaleConstShort`) and `(T - 21)^{-q/2} ≥ Λ^{-q/2}`. -/
lemma mainB1Low_mul_le_sum {q Λ : ℝ} {T r₀ : ℕ} (hq0 : 0 < q) (hq : q < 1 / 2) (hr₀ : 35 ≤ r₀)
    (hT : r₀ + 21 ≤ T) (hTΛ : (T : ℝ) ≤ Λ) :
    mainB1Low q (q * Λ) r₀ * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      ≤ cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q
        * ∑ k ∈ ({21} : Finset ℕ), perScaleConstShort q (k - 20) (T - k)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by
  rw [Finset.sum_singleton]
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  have hTr : (r₀ : ℝ) + 21 ≤ T := by exact_mod_cast hT
  have hr₀r : (35 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hΛ0 : 0 < Λ := by linarith
  have h21 : ((T - 21 : ℕ) : ℝ) = (T : ℝ) - 21 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have ht : Λ ^ (-(q / 2)) ≤ ((T - 21 : ℕ) : ℝ) ^ (-(q / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by rw [h21]; linarith) (by rw [h21]; linarith) (by linarith)
  have hΓ : perScaleConstShort q 1 r₀ ≤ perScaleConstShort q 1 (T - 21) :=
    monotone_perScaleConstShort hq0.le (by linarith) 1 (by omega : r₀ ≤ T - 21)
  have hΓ0 := perScaleConstShort_nonneg hq0.le (by linarith : q ≤ 11 / 20) 1 r₀
  have hV : (q * Λ + 24) / q = Λ + 24 / q := by rw [add_div, mul_div_cancel_left₀ _ hq0.ne']
  have hdm := one_sub_two_mul_mul_min_le (Λ := Λ) hq
  have hdm0 : 0 ≤ (1 - 2 * q) * min Λ (1 - 2 * q)⁻¹ :=
    mul_nonneg (by linarith) (le_min hΛ0.le (inv_nonneg.2 (by linarith)))
  have hP0 : 0 ≤ cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q
      * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)) := by
    have := cRed_pos q
    positivity
  have hg0 : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hPT0 := mul_nonneg hP0 (hΓ0.trans hΓ)
  calc mainB1Low q (q * Λ) r₀ * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      = cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q
          * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21))
          * perScaleConstShort q 1 r₀ * ((1 - 2 * q) * min Λ (1 - 2 * q)⁻¹)
          * Λ ^ (-(q / 2)) := by
        rw [mainB1Low, hV]
        ring
    _ ≤ cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q
          * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21))
          * perScaleConstShort q 1 (T - 21) * 1 * ((T - 21 : ℕ) : ℝ) ^ (-(q / 2)) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hΓ hP0) hdm hdm0 hPT0) ht hg0
          (by rw [mul_one]; exact hPT0)
    _ = _ := by ring

/-- **B2's main term in the low range**: on the scales `21 ≤ k ≤ 20 + n`,
`n = min(K_max(q), T - 55)`, for `9/20 ≤ q < ½`, `(1-2q)Λ ≥ 18`, `T ≤ Λ` and `T > Λ - 15`: drop
`k = 21`; on `k ≥ 22` the tube has `T - k ≥ 35` blocks, `Γ ≥ perScaleLow2Short`
(`RMF.perScaleLow2Short_le`), `N ≥ e^{-20.7867β - q}` (`βn ≤ q`) and
`(T - k)^{-q/2} ≥ Λ^{-q/2}`; and `n - 1 ≥ min{Λ, (1-2q)⁻¹}/2` (`min ≤ w = (1-2q)⁻¹ ≤ Λ/18`;
`⌊w⌋ - 1 ≥ w/2` as `w ≥ 10`, and `T - 56 > Λ - 71 ≥ Λ/36` as `Λ ≥ 180`). -/
lemma mainB2Low_mul_le_sum {q Λ : ℝ} {T : ℕ} (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2)
    (hu : 18 ≤ (1 - 2 * q) * Λ) (hTΛ : (T : ℝ) ≤ Λ) (hTl : Λ - 15 < T) :
    mainB2Low q (q * Λ) * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      ≤ cRed q * (2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q
        * ∑ k ∈ Finset.Icc 21 (20 + min (c3Kmax q) (T - 55)),
          perScaleConstShort q (k - 20) (T - k)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by
  have hqpos : 0 < q := by linarith
  have hb : 0 < 1 - 2 * q := by linarith
  have hbne : 1 - 2 * q ≠ 0 := hb.ne'
  have hΛ0 : 0 < Λ := by
    rcases le_or_gt Λ 0 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos hb.le h
      linarith
    · exact h
  have hΛ180 : 180 ≤ Λ := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * q ≤ 1 / 10) hΛ0.le
    linarith
  have hT55 : 55 ≤ T := by
    have : (55 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have hβ0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hqpos.le hb.le
  have hg0 : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hnK : min (c3Kmax q) (T - 55) ≤ c3Kmax q := min_le_left _ _
  have hnT : min (c3Kmax q) (T - 55) ≤ T - 55 := min_le_right _ _
  generalize hn : min (c3Kmax q) (T - 55) = n at hnK hnT ⊢
  -- `n - 1 ≥ min{Λ, (1-2q)⁻¹}/2`
  have hw10 : 10 ≤ 1 / (1 - 2 * q) := by
    rw [le_div_iff₀ hb]
    linarith
  have hmin : min Λ (1 - 2 * q)⁻¹ ≤ 1 / (1 - 2 * q) := by
    rw [one_div]
    exact min_le_right _ _
  have hwΛ : 1 / (1 - 2 * q) ≤ Λ / 18 := by
    rw [div_le_div_iff₀ hb (by norm_num)]
    linarith
  have hnA : 1 / 2 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ (c3Kmax q : ℝ) := by
    have h1 : ⌊1 / (1 - 2 * q)⌋₊ ≤ c3Kmax q := le_max_right _ _
    have h2 : 1 / (1 - 2 * q) < (⌊1 / (1 - 2 * q)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊1 / (1 - 2 * q)⌋₊ : ℝ) ≤ c3Kmax q := by exact_mod_cast h1
    linarith
  have hnB : 1 / 2 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ ((T - 55 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hT55]
    push_cast
    linarith
  have hn1 : 1 / 2 * min Λ (1 - 2 * q)⁻¹ + 1 ≤ (n : ℝ) := by
    rw [← hn, Nat.cast_min]
    exact le_min hnA hnB
  have hn1' : 1 ≤ n := by
    have hm0 : 0 ≤ min Λ (1 - 2 * q)⁻¹ := le_min hΛ0.le (inv_nonneg.2 hb.le)
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  -- `βn ≤ q`
  have hβn : q * (1 - 2 * q) * (n : ℝ) ≤ q := by
    have h1 : (n : ℝ) ≤ 1 / (1 - 2 * q) :=
      le_trans (by exact_mod_cast hnK) (c3Kmax_le hqpos.le hq)
    calc q * (1 - 2 * q) * (n : ℝ) ≤ q * (1 - 2 * q) * (1 / (1 - 2 * q)) :=
          mul_le_mul_of_nonneg_left h1 hβ0
      _ = q := by rw [mul_assoc, mul_one_div_cancel hbne, mul_one]
  -- one scale
  have hP2 : 0 ≤ perScaleLow2Short q := by
    have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
    unfold perScaleLow2Short
    positivity
  have hc0 : 0 ≤ perScaleLow2Short q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)
      * Λ ^ (-(q / 2)) := mul_nonneg (mul_nonneg hP2 (Real.exp_pos _).le) hg0
  have he21 : (90030 : ℝ) ≤ Real.exp 21 := by interval_decide (trust := kernel)
  have hterm : ∀ k ∈ Finset.Icc 22 (20 + n),
      perScaleLow2Short q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2))
        ≤ perScaleConstShort q (k - 20) (T - k)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hΓ := perScaleLow2Short_le hq0 hq (k - 20) (r := T - k) (by omega)
    have hk20 : (k : ℝ) ≤ 20 + n := by exact_mod_cast hk.2
    have hk21 : (21 : ℝ) ≤ k := by exact_mod_cast (by omega : 21 ≤ k)
    have hek : Real.exp 21 ≤ Real.exp (k : ℝ) := Real.exp_le_exp.2 hk21
    have hs : 9.003 / Real.exp (k : ℝ) ≤ 1 / 10 ^ 4 := by
      rw [div_le_iff₀ (Real.exp_pos _)]
      linarith
    have hN : Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)
        ≤ Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ))) :=
      Real.exp_le_exp.2 (exp_arg_B2 hβ0 hk20 hβn hs)
    have hTk : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have : 0 < T - k := by omega
      exact_mod_cast this
    have hTkΛ : ((T - k : ℕ) : ℝ) ≤ Λ := le_trans (by exact_mod_cast Nat.sub_le T k) hTΛ
    have ht := Real.rpow_le_rpow_of_nonpos hTk hTkΛ (by linarith : -(q / 2) ≤ 0)
    have hΓ0 := perScaleConstShort_nonneg (q := q) hqpos.le (by linarith) (k - 20) (T - k)
    exact mul_le_mul (mul_le_mul hΓ hN (Real.exp_pos _).le hΓ0) ht hg0
      (mul_nonneg hΓ0 (Real.exp_pos _).le)
  have hf0 : ∀ k ∈ Finset.Icc 21 (20 + n), 0 ≤ perScaleConstShort q (k - 20) (T - k)
      * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
      * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := fun k _ =>
    mul_nonneg (mul_nonneg (perScaleConstShort_nonneg hqpos.le (by linarith) _ _)
      (Real.exp_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hcard : ((Finset.Icc 22 (20 + n)).card : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.card_Icc, show 20 + n + 1 - 22 = n - 1 by omega, Nat.cast_sub hn1']
    simp
  have hsum : ((n : ℝ) - 1)
        * (perScaleLow2Short q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * Λ ^ (-(q / 2)))
      ≤ ∑ k ∈ Finset.Icc 21 (20 + n), perScaleConstShort q (k - 20) (T - k)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := by
    rw [← hcard, ← nsmul_eq_mul]
    refine le_trans (Finset.card_nsmul_le_sum _ _ _ hterm) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
      fun k hk _ => hf0 k hk
  have hP0 : 0 ≤ cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q := by
    have := cRed_pos q
    positivity
  have hV : (q * Λ + 24) / q = Λ + 24 / q := by rw [add_div, mul_div_cancel_left₀ _ hqpos.ne']
  calc mainB2Low q (q * Λ) * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))
      = (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q)
        * (1 / 2 * min Λ (1 - 2 * q)⁻¹
          * (perScaleLow2Short q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)
            * Λ ^ (-(q / 2)))) := by
        rw [mainB2Low, hV]
        ring
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q)
        * (((n : ℝ) - 1)
          * (perScaleLow2Short q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)
            * Λ ^ (-(q / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hc0) hP0
    _ ≤ (cRed q * 2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (Λ + 24 / q))) ^ q)
        * ∑ k ∈ Finset.Icc 21 (20 + n), perScaleConstShort q (k - 20) (T - k)
          * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
          * ((T - k : ℕ) : ℝ) ^ (-(q / 2)) := mul_le_mul_of_nonneg_left hsum hP0
    _ = _ := by ring

/-- **NH's arithmetic in the low range**: for `L > 0` with `67.17 ≤ Λ = log L ≤ 2100`, `q < ½`
and `u = (1-2q)Λ ≤ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ (1 + L)^{-(1-2q)}`: with
`δ = 1 - 2q ≤ 0.268`, `Λ·Λ^{-q/2} = Λ^{3/4+δ/4} ≤ 2100^{3/4+67/1000}`,
`(1 + L)^{-δ} ≥ (2L)^{-δ} ≥ 2^{-0.268}e^{-u}`, `min{Λ, 1/δ}e^u ≤ Λe^{18}/18`
(`RMF.eighteen_mul_exp_le` for `u ≥ 1`), and `RMF.nh_num_low`. -/
lemma nearHalf_arith_low {q L : ℝ} (hL : 0 < L) (hΛ1 : 67.17 ≤ Real.log L)
    (hΛ2 : Real.log L ≤ 2100) (hq : q < 1 / 2) (hu : (1 - 2 * q) * Real.log L ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      ≤ (1 + L) ^ (-(1 - 2 * q)) := by
  have hΛ0 : 0 < Real.log L := by linarith
  have hδ0 : 0 < 1 - 2 * q := by linarith
  have hδ1 : 1 - 2 * q ≤ 268 / 1000 := by
    have := mul_le_mul_of_nonneg_left hΛ1 hδ0.le
    linarith
  have hL1 : 1 ≤ L := by
    rw [← Real.exp_log hL]
    exact Real.one_le_exp (by linarith)
  have hg0 : 0 ≤ Real.log L ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  -- `Λ·Λ^{-q/2} ≤ 2100^{3/4+67/1000}`
  have hA : Real.log L * Real.log L ^ (-(q / 2))
      ≤ Real.exp ((3 / 4 + 67 / 1000) * Real.log 2100) := by
    rw [show Real.log L * Real.log L ^ (-(q / 2)) = Real.log L ^ (1 + -(q / 2)) by
        rw [Real.rpow_add hΛ0, Real.rpow_one]]
    calc Real.log L ^ (1 + -(q / 2)) ≤ (2100 : ℝ) ^ (1 + -(q / 2)) :=
          Real.rpow_le_rpow hΛ0.le hΛ2 (by linarith)
      _ ≤ (2100 : ℝ) ^ (3 / 4 + 67 / 1000 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = Real.exp ((3 / 4 + 67 / 1000) * Real.log 2100) := by
          rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  -- `(1 + L)^{-δ} ≥ 2^{-0.268}e^{-u}`
  have hlow : Real.exp (-(268 / 1000 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L))
      ≤ (1 + L) ^ (-(1 - 2 * q)) := by
    have h1 : (2 * L) ^ (-(1 - 2 * q)) ≤ (1 + L) ^ (-(1 - 2 * q)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2 : (2 * L) ^ (-(1 - 2 * q))
        = Real.exp (-((1 - 2 * q) * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
      rw [Real.rpow_def_of_pos (by linarith), Real.log_mul two_ne_zero hL.ne', ← Real.exp_add]
      congr 1
      ring
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : Real.exp (-(268 / 1000 * Real.log 2))
        ≤ Real.exp (-((1 - 2 * q) * Real.log 2)) := by
      have := mul_le_mul_of_nonneg_right hδ1 hl2
      exact Real.exp_le_exp.2 (by linarith)
    calc _ ≤ Real.exp (-((1 - 2 * q) * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (2 * L) ^ (-(1 - 2 * q)) := h2.symm
      _ ≤ _ := h1
  -- `10⁻¹⁰min{Λ, 1/δ}Λ^{-q/2}e^u ≤ 2^{-0.268}`
  have hnum := nh_num_low
  have hm0 : 0 ≤ min (Real.log L) (1 - 2 * q)⁻¹ := le_min hΛ0.le (inv_nonneg.2 hδ0.le)
  have hkey : 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L)
      ≤ Real.exp (-(268 / 1000 * Real.log 2)) := by
    have hA18 : 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 18
        ≤ 18 * Real.exp (-(268 / 1000 * Real.log 2)) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 10)) (Real.exp_pos 18).le
      linarith
    rcases le_or_gt ((1 - 2 * q) * Real.log L) 1 with hu1 | hu1
    · -- `min ≤ Λ`, `e^u ≤ e ≤ e^{18}/18`
      have h17 : (18 : ℝ) ≤ Real.exp 17 := by linarith [Real.add_one_le_exp (17 : ℝ)]
      have he1 : Real.exp ((1 - 2 * q) * Real.log L) ≤ Real.exp 1 := Real.exp_le_exp.2 hu1
      have he18 : 18 * Real.exp 1 ≤ Real.exp 18 := by
        have e : Real.exp 18 = Real.exp 1 * Real.exp 17 := by rw [← Real.exp_add]; norm_num
        rw [e]
        nlinarith [Real.exp_pos 1]
      have hm : min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))
          ≤ Real.log L * Real.log L ^ (-(q / 2)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hg0
      have hP0 : 0 ≤ 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) :=
        mul_nonneg (by norm_num) (mul_nonneg hΛ0.le hg0)
      calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
            * Real.exp ((1 - 2 * q) * Real.log L)
          ≤ 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) * Real.exp 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) he1 (Real.exp_pos _).le hP0
        _ ≤ Real.exp (-(268 / 1000 * Real.log 2)) := by
            have := mul_le_mul_of_nonneg_left he18 hP0
            nlinarith
    · -- `min ≤ 1/δ = Λ/u`, `18e^u ≤ ue^{18}`
      have hu18 := eighteen_mul_exp_le hu1.le hu
      have hmu : min (Real.log L) (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Real.log L) ≤ Real.log L := by
        calc min (Real.log L) (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Real.log L)
            ≤ (1 - 2 * q)⁻¹ * ((1 - 2 * q) * Real.log L) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = Real.log L := by rw [← mul_assoc, inv_mul_cancel₀ hδ0.ne', one_mul]
      have hQ0 : 0 ≤ 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2))) :=
        mul_nonneg (by norm_num) (mul_nonneg hm0 hg0)
      have h1 := mul_le_mul_of_nonneg_left hu18 hQ0
      have h2 : 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
            * ((1 - 2 * q) * Real.log L)
          ≤ 1 / 10 ^ 10 * (Real.log L * Real.log L ^ (-(q / 2))) := by
        have := mul_le_mul_of_nonneg_right hmu hg0
        nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 18).le
      nlinarith
  -- conclude
  have hE : Real.exp (-((1 - 2 * q) * Real.log L)) * Real.exp ((1 - 2 * q) * Real.log L) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-((1 - 2 * q) * Real.log L))).le
  calc 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
      = 1 / 10 ^ 10 * (min (Real.log L) (1 - 2 * q)⁻¹ * Real.log L ^ (-(q / 2)))
        * Real.exp ((1 - 2 * q) * Real.log L) * Real.exp (-((1 - 2 * q) * Real.log L)) := by
        rw [mul_assoc _ (Real.exp _), mul_comm (Real.exp _) (Real.exp _), hE, mul_one]
    _ ≤ Real.exp (-(268 / 1000 * Real.log 2)) * Real.exp (-((1 - 2 * q) * Real.log L)) := h
    _ ≤ _ := hlow

/-! ### The reduction with the main term, at the damping level -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Below `½` in the low range: the reduction at the tilt `V′ = Λ + 24/q`, the main term and
the subtracted term by Jensen.**  For a Rademacher family, `x ≥ exp(e^{67.17})`, `0 < q < ½` with
`(1-2q)Λ ≥ 1` and `y = Λ - log(400V′) ≥ 56`, `Λ = log log x`, the damping level `T` at
`σ = 2V′/log x` has `T ≤ Λ` and `T > y - 1`, and for every set `K` of scales in `(20, T - 35]` with
`k - 20 ≤ K_max(q)`, with `G = e^{-0.592}/2` and `Γ = RMF.perScaleConstShort`,

`cRed(q)·2^{2q-1}(G/(2V′))^q∑_{k∈K}Γ(q, k-20, T-k)e^{-q(1-2q)(k+0.7866+9.003e^{-k})}(T-k)^{-q/2}`
`  - ((1-2q)cJ(q)e^{-24} + errBLow(q, Λ))·min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`.

The reduction with the window covering of `RMF.isWindowCovering_of_classical`, the main
term `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_explicit_short` and Jensen
`RMF.integral_rpow_lineDiv_le_jensen`. -/
theorem exists_level_belowHalfLow (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hδΛ : 1 ≤ (1 - 2 * q) * Real.log (Real.log x))
    (hy : 56 ≤ Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q))) :
    ∃ T : ℕ, (T : ℝ) ≤ Real.log (Real.log x)
      ∧ Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q)) - 1 < T
      ∧ ∀ K : Finset ℕ, (∀ k ∈ K, 20 < k ∧ k + 35 ≤ T) → (∀ k ∈ K, k - 20 ≤ c3Kmax q) →
        cRed q * (2 ^ (2 * q - 1)
            * (Real.exp (-0.592) / 2 / (2 * (Real.log (Real.log x) + 24 / q))) ^ q
            * ∑ k ∈ K, perScaleConstShort q (k - 20) (T - k)
              * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
              * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
          - ((1 - 2 * q) * cJ q * Real.exp (-24) + errBLow q (Real.log (Real.log x)))
            * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2)))
        ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hx100, -, hwin⟩ := loglog_facts_of_low hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx
  have hx97 : Real.exp 97 ≤ x := le_trans (Real.exp_le_exp.2 (by norm_num)) hx100
  have h24 : 0 < 24 / q := div_pos (by norm_num) hq0
  have hV0 : 0 < Real.log (Real.log x) + 24 / q := by linarith
  have h400 : 0 < 400 * (Real.log (Real.log x) + 24 / q) := by linarith
  -- `400V′ ≤ log x`, from `y ≥ 56`
  have h400L : 400 * (Real.log (Real.log x) + 24 / q) ≤ Real.log x :=
    (Real.log_le_log_iff h400 hL0).1 (by linarith)
  -- the tilt `σ = 2V′/log x` and its damping level
  have hσ : 0 < 2 * (Real.log (Real.log x) + 24 / q) / Real.log x := div_pos (by linarith) hL0
  have hσ1 : 2 * (Real.log (Real.log x) + 24 / q) / Real.log x ≤ 1 / 200 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_damping_level hσ hσ1
  have hℓ : Real.log (1 / (200 * (2 * (Real.log (Real.log x) + 24 / q) / Real.log x)))
      = Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q)) := by
    rw [show 200 * (2 * (Real.log (Real.log x) + 24 / q) / Real.log x)
        = 400 * (Real.log (Real.log x) + 24 / q) / Real.log x by ring, one_div_div,
      Real.log_div hL0.ne' h400.ne']
  rw [hℓ] at hT3 hT4
  have hl7 : 7 ≤ Real.log (400 * (Real.log (Real.log x) + 24 / q)) := by
    rw [Real.le_log_iff_exp_le h400]
    have : Real.exp 7 ≤ 1100 := by interval_decide (trust := kernel)
    linarith
  have hyT := scaleCut_add_seven_le hx1 (T := T) (by linarith)
  refine ⟨T, by linarith, hT3, fun K hK hKq => ?_⟩
  -- the reduction at `V′`
  have hlogV : 3 * (Real.log (Real.log x) + 24 / q) + 3 ≤ Real.log x := by linarith
  have hred := le_integral_rpow_weightedRademacherSum_euler_full_of_windowCovering hX
    (V := Real.log (Real.log x) + 24 / q) hV0 hx97 hwin hlogV hq0 (by linarith)
  -- the main term at `σ = 2V′/log x`
  have hm5 := le_rpow_mul_integral_rpow_integral_lineDiv_explicit_short hX hσ hq0 hq.le
    (k₀ := 20) (y := ⌊x⌋₊ + 1) le_rfl hT1 hT2 hyT hK (fun k hk _ => hKq k hk) hL0
    (div_mul_cancel₀ _ hL0.ne')
  -- the subtracted term by Jensen, and the error term
  have hJ := integral_rpow_lineDiv_le_jensen hX hx100 hV0 hq0.le (by linarith)
  have hsub := jensen_term_le_low hq0 hq hL0 hΛ hδΛ
  have hE := cErrD_mul_rpow_le_errBLow hq hL0 (by linarith) hδΛ
  exact belowHalfLow_combine hred hm5 (cRed_pos q).le hJ (cJ_pos q).le
    (mul_nonneg (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hL0.le _)) hsub hE

/-! ### The regimes -/

/-- **F, the floor in the low range**: for `x ≥ exp(e^{67.17})`, `0 < q < ½` and
`PhiFLow(q, Λ) ≥ 10⁻¹⁰`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: the floor
`2^{-(1-2q)}3^{-(1-q)}(0.49/log x)^q` (`RMF.le_integral_rpow_weightedRademacherSum_floor_of_le_sum`
with `RMF.le_sum_inv_largePrimeSet_half_classical`) and `RMF.floor_regime_arith_low`. -/
theorem le_integral_rpow_floorRegimeLow (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hq0 : 0 < q) (hq : q < 1 / 2)
    (hF : 1 / 10 ^ 10 ≤ PhiFLow q (Real.log (Real.log x))) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, hx100, hx20, -⟩ := loglog_facts_of_low hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx4 : (4 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (100 : ℝ)]) hx100
  exact le_trans (floor_regime_arith_low hq hL0 (by linarith) hF)
    (le_integral_rpow_weightedRademacherSum_floor_of_le_sum hX hx4 hq0 hq.le
      (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hL0.le))
      (le_sum_inv_largePrimeSet_half_classical hx20))

/-- **B1 in the low range**: for `x ≥ exp(e^{67.17})`, `0 < q ≤ 9/20` and a rung `r₀ ≥ 35` with
`r₀ + 21 ≤ Λ - log(400(Λ + 24/q))` and `PhiB1Low(q, Λ, r₀) ≥ 10⁻¹⁰`,
`10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: `RMF.exists_level_belowHalfLow` on the one scale
`k = 21`, whose tube has `T - 21 ≥ r₀` blocks, and `RMF.mainB1Low_mul_le_sum`. -/
theorem le_integral_rpow_mainB1RegimeLow (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hq0 : 0 < q) (hq : q ≤ 9 / 20) {r₀ : ℕ}
    (hr₀ : 35 ≤ r₀)
    (hrung : (r₀ : ℝ) + 21
      ≤ Real.log (Real.log x) - Real.log (400 * (Real.log (Real.log x) + 24 / q)))
    (hB1 : 1 / 10 ^ 10 ≤ PhiB1Low q (Real.log (Real.log x)) r₀) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -, -⟩ := loglog_facts_of_low hx
  have hr₀r : (35 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hδΛ : 1 ≤ (1 - 2 * q) * Real.log (Real.log x) := by
    have := mul_le_mul (by linarith : (1 / 10 : ℝ) ≤ 1 - 2 * q) hΛ (by norm_num) (by linarith)
    linarith
  obtain ⟨T, hTΛ, hTl, H⟩ :=
    exists_level_belowHalfLow hX hx hq0 (by linarith) hδΛ (by linarith)
  have hT : r₀ + 21 ≤ T := by
    have h : (r₀ : ℝ) + 21 < (T : ℝ) + 1 := by linarith
    have h' : r₀ + 21 < T + 1 := by exact_mod_cast h
    omega
  have h := H {21}
    (fun k hk => by
      rw [Finset.mem_singleton] at hk
      subst hk
      exact ⟨by norm_num, by omega⟩)
    (fun k hk => by
      rw [Finset.mem_singleton] at hk
      subst hk
      change 1 ≤ c3Kmax q
      exact le_max_left _ _)
  exact le_of_sub_mul_le h (mainB1Low_mul_le_sum hq0 (by linarith) hr₀ hT hTΛ)
    (by unfold PhiB1Low; ring) hB1
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **B2 in the low range**: for `x ≥ exp(e^{67.17})` with `Λ ≤ 2100`, `9/20 ≤ q < ½` and
`(1-2q)Λ ≥ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: `Λ ≥ 180` and
`log(400V′) ≤ 14`, so `RMF.exists_level_belowHalfLow` applies, on the scales
`21 ≤ k ≤ 20 + min(K_max(q), T - 55)`; `RMF.mainB2Low_mul_le_sum` and `RMF.PhiB2Low_ge`. -/
theorem le_integral_rpow_mainB2RegimeLow (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hΛ2 : Real.log (Real.log x) ≤ 2100)
    (hq0 : 9 / 20 ≤ q) (hq : q < 1 / 2) (hu : 18 ≤ (1 - 2 * q) * Real.log (Real.log x)) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, -, -, -, -⟩ := loglog_facts_of_low hx
  have hΛ180 : 180 ≤ Real.log (Real.log x) := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * q ≤ 1 / 10)
      (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))
    linarith
  have hl14 := log_four_hundred_mul_le_fourteen hq0 (by linarith) hΛ2
  obtain ⟨T, hTΛ, hTl, H⟩ :=
    exists_level_belowHalfLow hX hx (by linarith) hq (by linarith) (by linarith)
  have hT15 : Real.log (Real.log x) - 15 < T := by linarith
  have hT55 : 55 ≤ T := by
    have : (55 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have h := H (Finset.Icc 21 (20 + min (c3Kmax q) (T - 55)))
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_right (c3Kmax q) (T - 55)
      exact ⟨by omega, by omega⟩)
    (fun k hk => by
      rw [Finset.mem_Icc] at hk
      have := min_le_left (c3Kmax q) (T - 55)
      omega)
  exact le_of_sub_mul_le h (mainB2Low_mul_le_sum hq0 hq hu hTΛ hT15)
    (by unfold PhiB2Low; ring) (PhiB2Low_ge hq0 hq hΛ2 hu)
    (mul_nonneg (le_min (by linarith) (inv_nonneg.2 (by linarith)))
      (Real.rpow_nonneg (by linarith) _))

/-- **NH in the low range, near `½` by Hölder**: for `x ≥ exp(e^{67.17})` with `Λ ≤ 2100`,
`q < ½` and `(1-2q)Λ ≤ 18`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`:
`(1 + log x)^{-(1-2q)} ≤ E|S(x)|^{2q}` (`RMF.le_integral_rpow_weightedRademacherSum_holder`;
`q > 0` as `Λ ≥ 67.17`) and `RMF.nearHalf_arith_low`. -/
theorem le_integral_rpow_nearHalfRegimeLow (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hΛ2 : Real.log (Real.log x) ≤ 2100) (hq : q < 1 / 2)
    (hu : (1 - 2 * q) * Real.log (Real.log x) ≤ 18) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ, hL, -, -, -⟩ := loglog_facts_of_low hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 ≤ x := (lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) hx).le
  have hq0 : 0 < q := by
    have hb : 0 < 1 - 2 * q := by linarith
    have := mul_le_mul_of_nonneg_left hΛ hb.le
    linarith
  exact le_trans (nearHalf_arith_low hL0 hΛ hΛ2 hq hu)
    (le_integral_rpow_weightedRademacherSum_holder hX hx1 hq0 hq)

/-- **Below `½` in the low range**: for a Rademacher family, `x ≥ exp(e^{67.17})` with
`log log x ≤ 2100` and `0 < q < ½`, `10⁻¹⁰min{Λ, (1-2q)⁻¹}Λ^{-q/2} ≤ E|S(x)|^{2q}`: for
`q ≤ 9/20`, F or B1 at the rung of `RMF.finalCellsLow_spec`; above, B2 for `(1-2q)Λ ≥ 18` and NH
otherwise. -/
theorem le_integral_rpow_belowHalfLow (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp (Real.exp 67.17) ≤ x) (hΛ : Real.log (Real.log x) ≤ 2100) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  obtain ⟨hΛ0, -, -, -, -⟩ := loglog_facts_of_low hx
  rcases le_or_gt q (9 / 20) with h | h
  · rcases finalCellsLow_spec hq0 h hΛ0 hΛ with hF | ⟨r₀, hr₀, hrung, hB1⟩
    · exact le_integral_rpow_floorRegimeLow hX hx hq0 hq hF
    · exact le_integral_rpow_mainB1RegimeLow hX hx hq0 h hr₀ hrung hB1
  rcases le_or_gt 18 ((1 - 2 * q) * Real.log (Real.log x)) with h' | h'
  · exact le_integral_rpow_mainB2RegimeLow hX hx hΛ h.le hq h'
  · exact le_integral_rpow_nearHalfRegimeLow hX hx hΛ hq h'.le

end RMF
