/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import PrimeNumberTheoremAnd.StrongPNT
import RMF.PNTPlus.MediumPNTExplicit

/-!
# An explicit classical zero-free region for `ζ`

`ZeroInequality` (in `PrimeNumberTheoremAnd.StrongPNT`) proves that some `E ∈ (0, 1)` has
`Re ρ ≤ 1 - E / log |Im ρ|` for every zero `ρ` of `ζ` with `|Im ρ| ≥ 2`, and exports only the
existential.  Its proof takes `E = 1/(14D)` with `D = 5A + 4B + C`, where `A`, `B`, `C` are the
constants of `ShiftZeroBound`, `ShiftOneBound` and `ShiftTwoBound`: `B` and `C` are built from the
constant of `LogDerivZetaFinalBound`, and `A` comes from a compactness step.  This file names them.

The proofs are adapted from `PrimeNumberTheoremAnd.StrongPNT` (PrimeNumberTheoremAnd, Apache 2.0
license): the same proofs, with each constant named or taken as a parameter, and the compactness
step replaced by `triv_bound_zeta_explicit` (`A = log 4 + 4`) from
`RMF.PNTPlus.MediumPNTExplicit`.  Of `PrimeNumberTheoremAnd.StrongPNT` only declarations up to
`ZeroInequality` are used; its `sorry`s all come after it.

## Main results

* `RMF.zfLogDerivC`: the constant of `LogDerivZetaFinalBound`; `RMF.zfLogDerivC_le`: it is `≤ 7`.
* `RMF.zfDiskK`: the factor the radii of `SumBoundI` contribute; `RMF.zfDiskK_le`: `≤ 15920`.
* `RMF.ZeroInequality_of`: the zero-free region with `E = 1/(14(5A + 4B + C))`.
* `RMF.zeta_zeroFree_explicit`: `Re ρ ≤ 1 - 10⁻⁷ / log |Im ρ|` for every zero `ρ` of `ζ` with
  `|Im ρ| ≥ 2`.  The proof certifies `E ≥ 1/9361842 ≈ 1.068·10⁻⁷`; the true value of the
  proof's `E` is `≈ 1.34·10⁻⁷`.
-/

namespace RMF

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

/-! ### The values of `ζ` at `3/2` and `3` -/

/-- `‖ζ(3/2)‖ ≤ 5`, from `ZetaNear1BndExplicit` (the true value is `2.612…`). -/
theorem norm_riemannZeta_three_halves_le : ‖ζ (3 / 2)‖ ≤ 5 := by
  have h := ZetaNear1BndExplicit (3 / 2) ⟨by norm_num, by norm_num⟩
  have e : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by norm_num
  rw [e] at h
  exact h.trans (le_of_eq (by norm_num))

/-- `‖ζ 3‖ ≥ 1`, from the Dirichlet series `ζ 3 = ∑ n⁻³`, whose term at `n = 1` is `1`. -/
theorem one_le_norm_riemannZeta_three : 1 ≤ ‖ζ 3‖ := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
  have e : ((3 : ℕ) : ℂ) = 3 := by norm_num
  have hc : (∑' n : ℕ, 1 / (n : ℂ) ^ 3) = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
      Complex.ofReal_natCast]
  rw [e, hc] at h
  have h1 : (1 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
    have := hs.le_tsum 1 (fun j _ => by positivity)
    simpa using this
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact h1.trans (le_abs_self _)

/-! ### The constant of `LogDerivZetaFinalBound` -/

/-- The constant `1 + log (11‖ζ(3/2)‖/‖ζ 3‖) / log 2` that the proof of
`LogDerivZetaFinalBound` chooses. -/
noncomputable def zfLogDerivC : ℝ := 1 + Real.log (11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖)) / Real.log 2

/-- `zfLogDerivC > 0`: `‖ζ(3/2)‖ > ‖ζ 3‖` (`norm_zeta_strict_mono_ofReal`). -/
theorem zfLogDerivC_pos : 0 < zfLogDerivC := by
  have h := norm_zeta_strict_mono_ofReal (a := 3) (b := 3 / 2) (by norm_num) (by norm_num)
  have e3 : ((3 : ℝ) : ℂ) = 3 := by norm_num
  have e32 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by norm_num
  rw [e3, e32] at h
  have h3 : 0 < ‖ζ 3‖ := lt_of_lt_of_le one_pos one_le_norm_riemannZeta_three
  have hr : 1 < ‖ζ (3 / 2)‖ / ‖ζ 3‖ := (one_lt_div h3).2 h
  have hlog : 0 < Real.log (11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖)) := Real.log_pos (by linarith)
  have hq : 0 < Real.log (11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖)) / Real.log 2 :=
    div_pos hlog (Real.log_pos one_lt_two)
  unfold zfLogDerivC
  linarith

/-- `zfLogDerivC ≤ 7`: `11‖ζ(3/2)‖/‖ζ 3‖ ≤ 55 ≤ 2⁶`. -/
theorem zfLogDerivC_le : zfLogDerivC ≤ 7 := by
  have h32 := norm_riemannZeta_three_halves_le
  have h3 := one_le_norm_riemannZeta_three
  have h32pos : 0 < ‖ζ (3 / 2)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hr0 : 0 < 11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖) := by
    have : 0 < ‖ζ (3 / 2)‖ / ‖ζ 3‖ := div_pos h32pos (by linarith)
    linarith
  have hr : 11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖) ≤ 2 ^ 6 := by
    have : ‖ζ (3 / 2)‖ / ‖ζ 3‖ ≤ ‖ζ (3 / 2)‖ := div_le_self h32pos.le h3
    linarith
  have hlog : Real.log (11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖)) ≤ 6 * Real.log 2 := by
    have h := Real.log_le_log hr0 hr
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hq : Real.log (11 * (‖ζ (3 / 2)‖ / ‖ζ 3‖)) / Real.log 2 ≤ 6 := by
    rw [div_le_iff₀ (Real.log_pos one_lt_two)]
    linarith
  unfold zfLogDerivC
  linarith

/-- `LogDerivZetaFinalBound` with its constant named: `C = zfLogDerivC`. -/
theorem LogDerivZetaFinalBound_explicit {r' r R' R : ℝ} (r'_pos : 0 < r') (r'_lt_r : r' < r)
    (r_lt_one : r < 1) (r_lt_R' : r < R') (R'_lt_R : R' < R) (R_lt_one : R < 1) :
      ∀ (t : ℝ), |t| ≥ 2 →
        let f : ℂ → ℂ := fun z ↦ ζ (z + 3 / 2 + I * (t : ℂ));
          (finiteZeros : (SetOfZeros 1 f).Finite) →
            ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f →
    ‖(deriv f z / f z) - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset,
      analyticOrderNatAt f ρ / (z - ρ)‖ ≤ (16 * r ^ 2 / (r - r') ^ 3 +
      1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * (zfLogDerivC * Real.log |t|) := by
  have one_lt_zeta_div : (1 : ℝ) < ‖ζ ((3 / 2) : ℝ)‖₊ / ‖ζ (3 : ℝ)‖₊ := by
    rw [coe_nnnorm, coe_nnnorm,
      one_lt_div (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    exact norm_zeta_strict_mono_ofReal (by linarith) (by linarith)
  have hzd : (1 : ℝ) < (‖ζ (3 / 2)‖₊ / ‖ζ 3‖₊ : ℝ) := by
    simpa only [ofReal_div, ofReal_ofNat] using one_lt_zeta_div
  rw [show zfLogDerivC = 1 + Real.log (11 * (‖ζ (3 / 2)‖₊ / ‖ζ 3‖₊)) / Real.log 2 by
    simp only [zfLogDerivC, coe_nnnorm]]
  set C : ℝ := 1 + Real.log (11 * (‖ζ (3 / 2)‖₊ / ‖ζ 3‖₊)) / Real.log 2
  intro t ht f finiteZeros z hz
  set g : ℂ → ℂ := f / (fun z ↦ f 0) with g_def
  have g_def' : g = fun z ↦ f z / f 0 := rfl
  set B : ℝ := (7 + 2 * |t|) * (‖ζ (3 / 2)‖₊ / ‖ζ 3‖₊) with B_def
  have one_lt_B : 1 < B := one_lt_mul (by linarith) hzd
  have one_le_C : (1 : ℝ) ≤ 11 * (‖ζ (3 / 2)‖₊ / ‖ζ 3‖₊) := (one_lt_mul (by linarith) hzd).le
  have f0nonzero : ¬f 0 = 0 := by
    simp only [f, zero_add]
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have ifInStripNotOne {z : ℂ} (hnorm: ‖z‖ ≤ 1) : (z.re + 3 / 2 = 1 → ¬z.im + t = 0) := by
    rw [← sq_le_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply] at hnorm
    intro hre him
    have hre' : z.re = -(1/2 : ℝ) := by linarith
    have him' : z.im = -t := by linarith
    simp only [hre', him', neg_mul_neg] at hnorm
    rw [← abs_two, ge_iff_le, ← sq_le_sq] at ht
    nlinarith [hnorm, ht]
  have gAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    simp only [g_def, f, zero_add]
    intro z hz; rw [Metric.mem_closedBall, _root_.dist_zero_right] at hz
    refine AnalyticAt.div_const
      (AnalyticAt.comp (AnalyticAt.comp (analyticAt_riemannZeta ?_) analyticAt_id)
        (AnalyticAt.add (AnalyticAt.add analyticAt_id analyticAt_const) analyticAt_const))
    simp only [Pi.add_apply, id_eq, ne_eq, Complex.ext_iff, add_re, div_ofNat_re, re_ofNat,
      mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, add_zero, one_re,
      add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, one_mul, zero_add, one_im, not_and]
    exact ifInStripNotOne hz
  have g0_eq_one : g 0 = 1 := by
    simp only [g_def, Pi.div_apply, ne_eq, f0nonzero, not_false_eq_true, div_self]
  have gFiniteZeros : (SetOfZeros 1 g).Finite := by
    simp only [SetOfZeros, g_def, Pi.div_apply, div_eq_zero_iff,
      or_iff_left f0nonzero] at ⊢ finiteZeros
    exact finiteZeros
  have gBound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z' hz'
    simp only [B_def, g_def, f, zero_add, Pi.div_apply, Complex.norm_div]
    rw [div_eq_mul_one_div]
    refine mul_le_mul (GlobalBound (le_trans hz' R_lt_one.le) ht) ?_
      (one_div_nonneg.mpr (norm_nonneg _)) (by linarith)
    rw [one_div_le (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))), one_div,
      inv_div, ← toReal_coe_nnnorm, ENNReal.coe_toReal, ← NNReal.coe_div, ← nnnorm_div]
    · exact_mod_cast ZetaFixedLowerBound t
    · simp only [coe_nnnorm, ← norm_div, norm_pos_iff, div_ne_zero_iff]
      exact ⟨riemannZeta_ne_zero_of_one_lt_re (by norm_num),
        riemannZeta_ne_zero_of_one_lt_re (by norm_num)⟩
  have ghz : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' g := by
    simp only [Set.mem_sdiff, Metric.mem_closedBall, _root_.dist_zero_right, SetOfZeros,
      mem_setOf_eq, not_and, g_def, Pi.div_apply, div_eq_zero_iff, not_or] at ⊢ hz
    exact ⟨hz.1, fun hz' => ⟨hz.2 hz', f0nonzero⟩⟩
  have gFinalBound := FinalBound one_lt_B r'_pos r'_lt_r r_lt_one r_lt_R' R'_lt_R R_lt_one
    gAnalytic g0_eq_one gFiniteZeros gBound ghz
  have gFiniteZeros' : (finiteSetOfZeros_mono r_lt_one gFiniteZeros).toFinset =
    (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset := by
    simp only [SetOfZeros, g_def, Pi.div_apply, div_eq_zero_iff, or_iff_left f0nonzero]
  suffices h1 : Real.log B ≤ C * Real.log |t| by
    refine le_trans (le_of_eq ?_) (gFinalBound.trans ?_)
    · apply congrArg norm
      rw [gFiniteZeros']
      congr 1
      · simp only [g_def', deriv_div_const, div_div_div_cancel_right₀ f0nonzero]
      · refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [div_left_inj', Nat.cast_inj, g_def', analyticOrderNatAt_fun_div_const f0nonzero]
        · simp only [f]
          refine AnalyticAt.comp (analyticAt_riemannZeta ?_)
            (AnalyticAt.add (AnalyticAt.add analyticAt_id analyticAt_const)
              (AnalyticAt.mul analyticAt_const analyticAt_const))
          simp only [SetOfZeros, Complex.ext_iff, zero_re, zero_im, Finite.mem_toFinset, add_re,
            mem_setOf_eq, ne_eq, div_ofNat_re, re_ofNat, mul_re, I_re, ofReal_re, zero_mul,
            I_im, ofReal_im, mul_zero, sub_self, add_zero, one_re, add_im, div_ofNat_im, im_ofNat,
            zero_div, mul_im, one_mul, zero_add, one_im, not_and] at ⊢ hρ
          exact ifInStripNotOne (le_trans hρ.1 r_lt_one.le)
        · simp only [SetOfZeros, Set.mem_sdiff, Metric.mem_closedBall, _root_.dist_zero_right,
            mem_setOf_eq, not_and, Finite.mem_toFinset] at hz hρ
          intro h; rw [sub_eq_zero] at h; rw [h] at hz
          exact (hz.2 (le_trans hρ.1 r_lt_R'.le)) hρ.2
    · refine mul_le_mul (by rfl) h1 (Real.log_nonneg one_lt_B.le)
        (add_nonneg (div_nonneg (mul_nonneg (ofNat_nonneg' _) (sq_nonneg _))
            (pow_nonneg (sub_nonneg.mpr r'_lt_r.le) _))
          (div_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr ?_)
              (Real.log_nonneg ((one_le_div (by linarith)).mpr R'_lt_R.le)))))
      rw [le_div_iff₀ (by linarith)]; nlinarith
  rw [add_mul, one_mul, div_mul_eq_mul_div, mul_div_assoc]
  suffices h2 : Real.log B ≤ Real.log |t| + Real.log (11 * (↑‖ζ (3 / 2)‖₊ / ↑‖ζ 3‖₊)) by
    exact le_trans h2 ((add_le_add_iff_left _).mpr (le_mul_of_one_le_right
      (Real.log_nonneg one_le_C) ((one_le_div (Real.log_pos one_lt_two)).mpr
      (log_le_log zero_lt_two (RCLike.ofReal_le_ofReal.mp ht)))))
  rw [← Real.log_mul (by linarith) (by linarith),
    log_le_log_iff (by linarith) (mul_pos (by linarith) (by linarith))]
  simp only [← mul_assoc, B_def, coe_nnnorm]
  exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ### The constants of `SumBoundI`, `ShiftTwoBound` and `ShiftOneBound` -/

/-- The factor that the radii `r' = 2/3`, `r = 3/4`, `R' = 4/5`, `R = 5/6` of `SumBoundI` put in
front of the constant of `LogDerivZetaFinalBound`, `15552 + 720/(49 log(25/24)) ≈ 15911.95`. -/
noncomputable def zfDiskK : ℝ :=
  16 * (3 / 4) ^ 2 / (3 / 4 - 2 / 3) ^ 3 +
    1 / (((5 / 6) ^ 2 / (4 / 5) - 4 / 5) * Real.log ((5 / 6) / (4 / 5)))

/-- `log(25/24) ≥ 1/25`, from `log x ≥ 1 - 1/x`. -/
theorem one_div_twentyFive_le_log : (1 : ℝ) / 25 ≤ Real.log ((5 / 6) / (4 / 5)) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (5 / 6 : ℝ) / (4 / 5)) (by norm_num)
  have e : (1 : ℝ) - ((5 / 6) / (4 / 5))⁻¹ = 1 / 25 := by norm_num
  linarith

/-- `zfDiskK` with its rational parts evaluated. -/
theorem zfDiskK_eq : zfDiskK = 15552 + 1 / (49 / 720 * Real.log ((5 / 6) / (4 / 5))) := by
  have h1 : (16 : ℝ) * (3 / 4) ^ 2 / (3 / 4 - 2 / 3) ^ 3 = 15552 := by norm_num
  have h2 : ((5 : ℝ) / 6) ^ 2 / (4 / 5) - 4 / 5 = 49 / 720 := by norm_num
  unfold zfDiskK
  rw [h1, h2]

/-- `zfDiskK > 0`. -/
theorem zfDiskK_pos : 0 < zfDiskK := by
  have hL := one_div_twentyFive_le_log
  have hL0 : 0 < Real.log ((5 / 6) / (4 / 5)) := by linarith
  rw [zfDiskK_eq]
  positivity

/-- `zfDiskK ≤ 15920`. -/
theorem zfDiskK_le : zfDiskK ≤ 15920 := by
  have hL := one_div_twentyFive_le_log
  have hpos : (0 : ℝ) < 49 / 720 * Real.log ((5 / 6) / (4 / 5)) := by
    have : (0 : ℝ) < Real.log ((5 / 6) / (4 / 5)) := by linarith
    positivity
  have h368 : 1 / (49 / 720 * Real.log ((5 / 6) / (4 / 5))) ≤ 368 := by
    rw [div_le_iff₀ hpos]
    linarith
  rw [zfDiskK_eq]
  linarith

/-- `SumBoundI` from a constant `C` of `LogDerivZetaFinalBound`, with constant `zfDiskK * C`. -/
theorem SumBoundI_of {C : ℝ}
    (hL : ∀ {r' r R' R : ℝ}, 0 < r' → r' < r → ∀ (r_lt_one : r < 1), r < R' → R' < R → R < 1 →
      ∀ (t : ℝ), |t| ≥ 2 →
        let f : ℂ → ℂ := fun z ↦ ζ (z + 3 / 2 + I * (t : ℂ));
          (finiteZeros : (SetOfZeros 1 f).Finite) →
            ∀ (z : ℂ), z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f →
      ‖(deriv f z / f z) - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset,
        analyticOrderNatAt f ρ / (z - ρ)‖ ≤ (16 * r ^ 2 / (r - r') ^ 3 +
        1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * (C * Real.log |t|)) :
    ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
      ∀ (t : ℝ), |t| ≥ 2 →
        ∀ (finiteZeros : (ZeroWindow t).Finite),
    ‖ζ' (1 + δ + I * t) / ζ (1 + δ + I * t) - ∑ ρ ∈ finiteZeros.toFinset,
      analyticOrderNatAt ζ ρ / (1 + δ + I * t - ρ)‖ ≤ zfDiskK * C * Real.log |t| := by
  let r' : ℝ := 2 / 3
  let r : ℝ := 3 / 4
  let R' : ℝ := 4 / 5
  let R : ℝ := 5 / 6
  have r'_pos : 0 < r' := by norm_num
  have r'_lt_r : r' < r := by norm_num
  have r_lt_one : r < 1 := by norm_num
  have r_lt_R' : r < R' := by norm_num
  have R'_lt_R : R' < R := by norm_num
  have R_lt_one : R < 1 := by norm_num
  have LogDerivBound := hL r'_pos r'_lt_r r_lt_one r_lt_R' R'_lt_R R_lt_one
  intro δ hd t ht finiteZeros
  have LogDerivBound := LogDerivBound t ht
  extract_lets f at LogDerivBound
  have finiteZeros' : (SetOfZeros 1 f).Finite := by
    apply ZetaShiftFiniteZeros ht
    simp only [f]
  have hd' : ‖(δ : ℂ) - 1 / 2‖ < 1 / 2 := by
    obtain ⟨d0, d1⟩ := hd
    simp only [← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith, by linarith⟩
  set z : ℂ := δ - 1 / 2 with hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f := by
    simp only [SetOfZeros, f, Set.mem_sdiff, Metric.mem_closedBall, dist_zero_right, mem_setOf_eq,
      not_and]
    refine ⟨le_of_lt (lt_trans hd' (by linarith)), fun _ => riemannZeta_ne_zero_of_one_lt_re ?_⟩
    simp only [add_re, div_ofNat_re, re_ofNat, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
      mul_zero, sub_self, add_zero]
    linarith [abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm z) hd')]
  have LogDerivBound := LogDerivBound finiteZeros' z hz'
  refine le_trans (le_of_eq ?_) (LogDerivBound.trans (by rw [mul_assoc]; exact le_rfl))
  apply congrArg norm
  congr 1
  · simp only [f, hz, add_assoc, deriv_comp_add_const]
    ring_nf
  · simp only [f, hz]
    refine Finset.sum_nbij' (fun ρ => ρ - (3 / 2 + I * t)) (fun ρ => ρ + (3 / 2 + I * t))
      (fun ρ hρ => ?_) (fun ρ hρ => ?_) (fun ρ hρ => by ring_nf) (fun ρ hρ => by ring_nf)
      (fun ρ hρ => ?_)
    · simp only [Set.Finite.mem_toFinset, SetOfZeros, ZeroWindow, Set.mem_setOf_eq] at hρ ⊢
      refine ⟨?_, ?_⟩
      · simp only [r, hρ.2]
      · simp only [add_assoc, sub_add_cancel, hρ.1]
    · simp only [Set.Finite.mem_toFinset, SetOfZeros, ZeroWindow, Set.mem_setOf_eq] at hρ ⊢
      refine ⟨?_, ?_⟩
      · simp only [← add_assoc, hρ.2]
      · simp only [add_sub_cancel_right, r, hρ.1]
    · ring_nf
      rw [mul_comm, analyticOrderNatAt_fun_comp_add_left]
      ring_nf

/-- `ShiftTwoBound` from a constant `C` of `SumBoundI`, with constant `C * 2`. -/
theorem ShiftTwoBound_of {C : ℝ} (hC : 0 < C)
    (SumBound : ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
      ∀ (t : ℝ), |t| ≥ 2 →
        ∀ (finiteZeros : (ZeroWindow t).Finite),
      ‖ζ' (1 + δ + I * t) / ζ (1 + δ + I * t) - ∑ ρ ∈ finiteZeros.toFinset,
        analyticOrderNatAt ζ ρ / (1 + δ + I * t - ρ)‖ ≤ C * Real.log |t|) :
    ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
      ∀ (t : ℝ), |t| ≥ 2 →
        (ZeroWindow (2 * t)).Finite →
    -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re ≤ C * 2 * log |t| := by
  intro δ hd t ht finiteZeros
  suffices h1 : -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re ≤ C * log |2 * t| by
    refine le_trans h1 ?_
    rw [mul_assoc C, abs_mul, Real.log_mul (by norm_num) (by linarith [ht]), two_mul]
    exact mul_le_mul (by rfl) (add_le_add (log_le_log (by norm_num) (by norm_num [ht])) (by rfl))
      (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by linarith [ht]))) hC.le
  have ht' : |2 * t| ≥ 2 := by
    simp only [abs_mul, abs_ofNat, ofNat_pos, le_mul_iff_one_le_right]
    linarith
  have SumBound := SumBound δ hd _ ht' finiteZeros; rw [← Complex.norm_neg', neg_sub] at SumBound
  refine le_trans ?_ (le_trans (Complex.re_le_norm _) SumBound)
  simp only [ofReal_mul, ofReal_ofNat, sub_re, re_sum, ← mul_assoc, mul_comm]
  rw [sub_eq_add_neg, le_add_iff_nonneg_left]
  refine Finset.sum_nonneg (fun ρ hρ => ?_); simp only [ZeroWindow, ofReal_mul, ofReal_ofNat,
    Finite.mem_toFinset, mem_setOf_eq] at hρ
  have hρ_re: ρ.re ≤ 1 := by
    by_contra hre; simp only [not_le] at hre
    exact riemannZeta_ne_zero_of_one_lt_re hre hρ.1
  simp only [div_re, natCast_re, sub_re, add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, re_ofNat, mul_im, ← sq, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, one_mul, zero_add, im_ofNat, add_zero, normSq_apply, sub_im,
    add_im, one_im, natCast_im, zero_div]
  exact div_nonneg (mul_nonneg (cast_nonneg' _) (by linarith [hd.1]))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- `ShiftOneBound` from a constant `C` of `SumBoundI`, with constant `7 + C`. -/
theorem ShiftOneBound_of {C : ℝ} (hC : 0 < C)
    (SumBound : ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
      ∀ (t : ℝ), |t| ≥ 2 →
        ∀ (finiteZeros : (ZeroWindow t).Finite),
      ‖ζ' (1 + δ + I * t) / ζ (1 + δ + I * t) - ∑ ρ ∈ finiteZeros.toFinset,
        analyticOrderNatAt ζ ρ / (1 + δ + I * t - ρ)‖ ≤ C * Real.log |t|) :
    ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
      ∀ (t : ℝ), |t| ≥ 2 →
        (ZeroWindow t).Finite →
          ∀ (ρ : ℂ), ζ ρ = 0 →
            t = ρ.im →
    -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re ≤
      (7 + C) * Real.log |t| - 1 / (1 + δ - ρ.re) := by
  intro δ hd t ht finiteZeros ρ hρzero hρim
  have SumBound := SumBound δ hd t ht finiteZeros; rw [← Complex.norm_neg', neg_sub] at SumBound
  have SumBound := le_trans (Complex.re_le_norm _) SumBound
  have hρre : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hρzero
  have ρ_ne_one : ρ ≠ 1 := by rintro rfl; simp only [one_re, lt_self_iff_false] at hρre
  have analyticOnNhdZeta : AnalyticOnNhd ℂ ζ {z : ℂ | z ≠ 1} := by
    intro z hz; simp only [ne_eq, mem_setOf_eq] at hz
    exact DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1})
      (fun z' hz' => (differentiableAt_riemannZeta hz').differentiableWithinAt)
      ((isOpen_ne).mem_nhds hz)
  have hTermNonneg {ρ' : ℂ} (hρ' : ρ' ∈ finiteZeros.toFinset) :
    0 ≤ ((analyticOrderNatAt ζ ρ') / (1 + ↑δ + I * ↑t - ρ')).re := by
    simp only [div_re, natCast_re, add_re, one_re, ofReal_re, sub_re, mul_re, I_re, zero_mul, I_im,
      ofReal_im, mul_zero, sub_self, natCast_im, add_im, one_im, add_zero, sub_im, mul_im,
      one_mul, zero_add, zero_div]
    refine div_nonneg (mul_nonneg (by positivity) ?_) (normSq_nonneg _)
    by_contra h; push Not at h
    simp only [ZeroWindow, Finite.mem_toFinset, mem_setOf_eq] at hρ'
    exact riemannZeta_ne_zero_of_one_le_re (by linarith [hd.1]) hρ'.1
  by_cases hρZt : ρ ∈ finiteZeros.toFinset
  · have obvious : C * log |t| ≤ (7 + C) * log |t| := mul_le_mul (by linarith) (by rfl)
      (Real.log_nonneg (by linarith)) (by linarith)
    have SumBound := le_trans SumBound obvious
    rw [← Finset.insert_erase hρZt, ← Finset.singleton_union, ← Finset.sdiff_singleton_eq_erase,
      Finset.sum_union (by simp), Finset.sum_singleton] at SumBound
    simp only [sub_re, add_re, re_sum, add_sub_assoc] at SumBound
    rw [div_re] at SumBound
    simp only [natCast_re, add_re, one_re, ofReal_re, sub_re, mul_re, I_re, zero_mul, I_im,
      add_im, ofReal_im, mul_zero, sub_self, zero_sub, natCast_im, one_im, add_zero, sub_im,
      mul_im, ← hρim, one_mul, zero_add, zero_div, normSq_apply, mul_div_assoc,
      div_self_mul_self', ← one_div] at SumBound
    refine le_sub_left_of_add_le (le_trans (add_le_add ?_ ?_) SumBound)
    · rw [← mul_div_assoc, mul_one]
      refine div_le_div_of_nonneg_right ?_ (by linarith [hd.1])
      simp only [one_le_cast, Nat.one_le_iff_ne_zero, analyticOrderNatAt, ne_eq,
        ENat.toNat_eq_zero, analyticOrderAt_eq_zero, analyticOrderAt_eq_top, not_or, not_not]
      refine ⟨⟨DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        ((isOpen_ne).mem_nhds ρ_ne_one), hρzero⟩,
        (fun h => riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num)
        (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero analyticOnNhdZeta (z₀ := ρ)
        ((isConnected_compl_singleton_of_one_lt_rank ?_ 1).isPreconnected) ?_ ?_ ?_))⟩
      · simp only [rank_real_complex, one_lt_ofNat]
      · simp only [ne_eq, mem_setOf_eq, ρ_ne_one, not_false_eq_true]
      · simp only [EventuallyEq, Pi.zero_apply, h]
      · simp only [ne_eq, mem_setOf_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    · simp only [← add_sub_assoc, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
      refine Finset.sum_nonneg (fun ρ' hρ' => hTermNonneg ?_)
      simp only [Finset.mem_sdiff] at hρ'
      exact hρ'.1
  · have logBound : -(ζ' (1 + ↑δ + I * ↑t) / ζ (1 + ↑δ + I * ↑t)).re ≤ C * Real.log |t| := by
      refine le_trans ?_ SumBound
      rw [sub_eq_add_neg, add_re, neg_re, re_sum, le_add_iff_nonneg_left]
      exact Finset.sum_nonneg (fun ρ' hρ' => hTermNonneg hρ')
    have invBound : 1 / (1 + δ - ρ.re) ≤ 7 * Real.log |t| := by
      suffices h1 : 1 / (1 + δ - ρ.re) ≤ 4 by
        have explicitEstimate : 4 ≤ 7 * Real.log 2 := by linarith [Real.log_two_gt_d9]
        exact le_trans h1 (le_trans explicitEstimate ((mul_le_mul_iff_of_pos_left ofNat_pos').mpr
          (Real.log_le_log ofNat_pos' ht)))
      simp only [ZeroWindow, Finite.mem_toFinset, mem_setOf_eq, hρzero, true_and, not_le] at hρZt
      rw [← Complex.re_add_im ρ, hρim] at hρZt
      ring_nf at hρZt
      have : - (3 : ℂ) / 2 + ρ.re = (((ρ.re - 3 / 2) : ℝ) : ℂ) := by
        simp only [ofReal_sub, ofReal_div, ofReal_ofNat, neg_add_eq_sub, neg_div, neg_add_eq_sub]
      rw [this, Complex.norm_real, Real.norm_eq_abs] at hρZt
      have hρreImproved : ρ.re < 3 / 4 := by rcases lt_abs.mp hρZt with _ | _ <;> linarith
      rw [one_div_le (by linarith [hd.1]) four_pos]
      linarith [hd.1]
    linarith

/-! ### `ShiftZeroBound` without compactness -/

/-- `ShiftZeroBound` with the constant `A = log 4 + 4` of `triv_bound_zeta_explicit`, in place of
the original's compactness step. -/
theorem ShiftZeroBound_explicit :
    ∀ (δ : ℝ), δ ∈ Ioo 0 1 → -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ 1 / δ + (Real.log 4 + 4) := by
  intro δ hδ
  have h := triv_bound_zeta_explicit (1 + δ) 0 (by linarith [hδ.1])
  simp only [ofReal_add, ofReal_one, ofReal_zero, zero_mul, add_zero] at h
  have hre : -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ ‖-ζ' (1 + δ) / ζ (1 + δ)‖ := by
    rw [neg_div, ← Complex.neg_re]
    exact Complex.re_le_norm _
  calc -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ (1 + δ - 1)⁻¹ + (Real.log 4 + 4) := hre.trans h
    _ = 1 / δ + (Real.log 4 + 4) := by ring

/-! ### The zero-free region -/

/-- `ZeroInequality` from constants `A`, `B`, `C` of `ShiftZeroBound`, `ShiftOneBound` and
`ShiftTwoBound`: `E = 1/(14(5A + 4B + C))`. -/
theorem ZeroInequality_of {A B C : ℝ} (Age : 1 ≤ A) (Bpos : 0 < B) (Cpos : 0 < C)
    (ShiftZero : ∀ (δ : ℝ), δ ∈ Ioo 0 1 → -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ 1 / δ + A)
    (ShiftOne : ∀ (δ : ℝ), δ ∈ Ioo 0 1 → ∀ (t : ℝ), |t| ≥ 2 → (ZeroWindow t).Finite →
      ∀ (ρ : ℂ), ζ ρ = 0 → t = ρ.im →
        -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re ≤ B * Real.log |t| - 1 / (1 + δ - ρ.re))
    (ShiftTwo : ∀ (δ : ℝ), δ ∈ Ioo 0 1 → ∀ (t : ℝ), |t| ≥ 2 → (ZeroWindow (2 * t)).Finite →
      -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re ≤ C * log |t|) :
    ∀ (ρ : ℂ), ζ ρ = 0 →
      ∀ (σ : ℝ), σ = ρ.re →
        ∀ (t : ℝ), t = ρ.im → |t| ≥ 2 →
          σ ≤ 1 - (14 * (5 * A + 4 * B + C))⁻¹ / log |t| := by
  set D : ℝ := 5 * A + 4 * B + C with D_def
  set E : ℝ := (14 * D)⁻¹ with E_def
  have Dge1 : 1 ≤ D := by linarith
  intro ρ hρzero σ ρre t ρim ht
  set δ : ℝ := 1 / (2 * D * Real.log |t|) with δ_def
  have δrange : δ ∈ Ioo 0 1 := by
    simp only [mem_Ioo, δ_def, one_div_pos]
    rw [div_lt_one (by nlinarith [Real.log_le_log zero_lt_two ht, Real.log_two_gt_d9])]
    exact ⟨by nlinarith [Real.log_le_log zero_lt_two ht, Real.log_two_gt_d9],
      by nlinarith [Real.log_le_log zero_lt_two ht, Real.log_two_gt_d9]⟩
  have hugeEq :
      3 * (-ζ' (1 + δ) / ζ (1 + δ)) +
      4 * (-ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)) +
      (-ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t))
    = ∑' (n : ℕ), Λ (n) * n ^ (-(1 : ℂ) - δ)
      * ((3 : ℂ) + 4 * n ^ (-I * t) + n ^ (-2 * I * t)) := by
    rw [LogDerivativeDirichlet (s := 1 + δ) (by simp [δrange.1]),
        LogDerivativeDirichlet (s := 1 + δ + I * t) (by simp [δrange.1]),
        LogDerivativeDirichlet (s := 1 + δ + 2 * I * t) (by simp [δrange.1])]
    simp only [← tsum_mul_left, ← neg_add', mul_add]; repeat rw [← Summable.tsum_add]
    · congr 1; funext n; by_cases heq0 : n = 0
      · simp only [heq0, ArithmeticFunction.map_zero, ofReal_zero, CharP.cast_eq_zero,
          zero_div, mul_zero, add_zero, neg_add_rev, zero_mul, neg_mul]
      · simp only [div_eq_mul_inv, mul_assoc, neg_mul]
        congr 2
        · simp only [← cpow_neg, neg_add_rev]
          ring_nf
        · simp only [← cpow_neg, neg_add_rev]
          rw [cpow_add _ _ ((cast_ne_zero (R := ℂ)).mpr heq0), mul_comm]
          ring_nf
        · simp only [← cpow_neg, neg_add_rev]
          rw [cpow_add _ _ ((cast_ne_zero (R := ℂ)).mpr heq0), mul_comm]
    · refine Summable.add (Summable.mul_left _ (vonMangoldtLSeriesSummable ?_))
        (Summable.mul_left _ (vonMangoldtLSeriesSummable ?_))
      · simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, δrange.1]
      · simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
          sub_self, add_zero, lt_add_iff_pos_right, δrange.1]
    · refine vonMangoldtLSeriesSummable ?_
      simp only [add_re, one_re, ofReal_re, mul_re, re_ofNat, I_re, mul_zero, im_ofNat, I_im,
        mul_one, sub_self, zero_mul, mul_im, add_zero, ofReal_im, lt_add_iff_pos_right, δrange.1]
    · refine Summable.mul_left _ (vonMangoldtLSeriesSummable ?_)
      simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, δrange.1]
    · refine Summable.mul_left _ (vonMangoldtLSeriesSummable ?_)
      simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, lt_add_iff_pos_right, δrange.1]
  have hugeEqRe :
      3 * -(ζ' (1 + δ) / ζ (1 + δ)).re +
      4 * -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re +
      -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re
    = 2 * ∑' (n : ℕ), Λ (n) * n ^ (-1 - δ) * (1 + Real.cos (-t * Real.log n)) ^ 2 := by
    have re_eq := congr_arg Complex.re hugeEq
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, neg_mul, neg_div,
      Complex.neg_re] at re_eq
    rw [re_eq, Complex.re_tsum, ← tsum_mul_left]
    · refine tsum_congr (fun n => ?_)
      by_cases heq0 : n = 0
      · simp [heq0]
      · repeat rw [Complex.cpow_def_of_ne_zero (cast_ne_zero (R := ℂ).mpr heq0)]
        simp only [← natCast_log, mul_neg, mul_re, ofReal_re, exp_re, sub_re, neg_re, one_re,
          ofReal_im, sub_im, neg_im, one_im, neg_zero, sub_self, mul_zero, sub_zero, mul_im,
          zero_mul, add_zero, Real.cos_zero, mul_one, exp_im, Real.sin_zero, add_re, re_ofNat,
          I_re, I_im, one_mul, zero_add, Real.exp_zero, Real.cos_neg, im_ofNat, Real.sin_neg,
          add_im, neg_mul, add_sq, one_pow, Real.cos_sq, one_div]
        rw [← Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero heq0))]
        ring_nf
    · simp only [mul_add, mul_assoc]; ring_nf
      refine Summable.add (Summable.add (Summable.mul_right _ ?_) (Summable.mul_right _ ?_)) ?_
      · refine (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := 1 + δ) (by simp [δrange.1])).congr (fun n => ?_)
        by_cases heq0 : n = 0
        · simp only [heq0, LSeries.term_zero, ArithmeticFunction.map_zero, ofReal_zero,
            CharP.cast_eq_zero, zero_mul]
        · simp only [ne_eq, heq0, not_false_eq_true, LSeries.term_of_ne_zero]
          rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_add']
      · refine (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := 1 + δ + I * t) (by simp [δrange.1])).congr (fun n => ?_)
        by_cases heq0 : n = 0
        · simp only [heq0, LSeries.term_zero, ArithmeticFunction.map_zero, ofReal_zero,
            CharP.cast_eq_zero, zero_mul]
        · simp only [ne_eq, heq0, not_false_eq_true, LSeries.term_of_ne_zero]
          rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
            Complex.cpow_add _ _ ((cast_ne_zero (R := ℂ)).mpr heq0)]
          ring_nf
      · refine (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := 1 + δ + 2 * I * t) (by simp [δrange.1])).congr (fun n => ?_)
        by_cases heq0 : n = 0
        · simp only [heq0, LSeries.term_zero, ArithmeticFunction.map_zero, ofReal_zero,
            CharP.cast_eq_zero, zero_mul]
        · simp only [ne_eq, heq0, not_false_eq_true, LSeries.term_of_ne_zero]
          rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
            Complex.cpow_add _ _ ((cast_ne_zero (R := ℂ)).mpr heq0)]
          ring_nf
  have ZeroWindowOneFinite : (ZeroWindow t).Finite := ZeroWindowFinite ht
  have ZeroWindowTwoFinite : (ZeroWindow (2 * t)).Finite := by
    apply ZeroWindowFinite
    simp only [abs_mul, abs_ofNat, ge_iff_le, ofNat_pos, le_mul_iff_one_le_right]
    linarith
  have ShiftZero := ShiftZero δ δrange
  have ShiftOne := ShiftOne δ δrange t ht ZeroWindowOneFinite ρ hρzero ρim
  have ShiftTwo := ShiftTwo δ δrange t ht ZeroWindowTwoFinite
  suffices h1 : 4 / (1 + δ - σ) ≤ 3 / δ + D * Real.log |t| by
    simp only [δ_def, div_eq_mul_inv, mul_inv_rev, one_mul, inv_inv] at h1
    rw [mul_inv_le_iff₀] at h1
    · ring_nf at h1; field_simp at h1; ring_nf at h1; field_simp at h1
      rw [mul_div_cancel_left₀ _
        (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))] at h1
      rw [E_def, ← inv_mul', le_sub_comm,
        inv_le_iff_one_le_mul₀' (mul_pos (by linarith) (Real.log_pos (by linarith)))]
      linarith
    · rw [add_sub_right_comm]
      apply add_pos_of_nonneg_of_pos
      · by_contra hσ; simp only [sub_nonneg, not_le, ρre] at hσ
        exact (riemannZeta_ne_zero_of_one_lt_re hσ) hρzero
      · exact mul_pos (inv_pos.mpr (Real.log_pos (by linarith))) (by positivity)
  suffices h2 : 0 ≤ 3 / δ + 3 * A - 4 / (1 + δ - σ) + 4 * B * Real.log |t| + C * Real.log |t| by
    simp only [sub_eq_neg_add, add_assoc, le_neg_add_iff_add_le, add_zero, ge_iff_le] at ⊢ h2
    apply le_trans h2
    simp only [← add_assoc, D_def, add_mul, add_le_add_iff_right, add_le_add_iff_left]
    nlinarith [Real.log_le_log zero_lt_two ht, Real.log_two_gt_d9]
  calc 0 ≤ 2 * ∑' (n : ℕ), Λ (n) * n ^ (-1 - δ) * (1 + Real.cos (-t * Real.log n)) ^ 2 := by
        rw [mul_nonneg_iff_of_pos_left two_pos]
        exact tsum_nonneg (fun n => mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (sq_nonneg _))
    _ = 3 * -(ζ' (1 + δ) / ζ (1 + δ)).re +
        4 * -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re +
        -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re :=
        hugeEqRe.symm
    _ ≤ 3 / δ + 3 * A - 4 / (1 + δ - σ) + 4 * B * Real.log |t| + C * Real.log |t| := by
        rw [← ρre] at ShiftOne
        ring_nf at ShiftZero ShiftOne ShiftTwo ⊢
        linarith

/-- **An explicit classical zero-free region**: every zero `ρ` of `ζ` with `|Im ρ| ≥ 2` has
`Re ρ ≤ 1 - 10⁻⁷ / log |Im ρ|`.  `ZeroInequality_of` at `A = log 4 + 4`, `B = 7 + K C_L`,
`C = 2 K C_L` (`K = zfDiskK ≤ 15920`, `C_L = zfLogDerivC ≤ 7`): `D ≤ 668703`, `14D < 10⁷`. -/
theorem zeta_zeroFree_explicit :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 2 ≤ |ρ.im| → ρ.re ≤ 1 - (1 / 10 ^ 7) / Real.log |ρ.im| := by
  intro ρ hρ ht
  have hK0 := zfDiskK_pos
  have hL0 := zfLogDerivC_pos
  have hS0 : 0 < zfDiskK * zfLogDerivC := mul_pos hK0 hL0
  have hS : zfDiskK * zfLogDerivC ≤ 15920 * 7 :=
    mul_le_mul zfDiskK_le zfLogDerivC_le hL0.le (by norm_num)
  have hSum := SumBoundI_of (C := zfLogDerivC) LogDerivZetaFinalBound_explicit
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4' : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hZI := ZeroInequality_of (by linarith) (by linarith) (by linarith) ShiftZeroBound_explicit
    (ShiftOneBound_of hS0 hSum) (ShiftTwoBound_of hS0 hSum) ρ hρ ρ.re rfl ρ.im rfl ht
  have hD : 0 < 14 * (5 * (Real.log 4 + 4) + 4 * (7 + zfDiskK * zfLogDerivC) +
      zfDiskK * zfLogDerivC * 2) := by linarith
  have hE : (1 : ℝ) / 10 ^ 7 ≤ (14 * (5 * (Real.log 4 + 4) + 4 * (7 + zfDiskK * zfLogDerivC) +
      zfDiskK * zfLogDerivC * 2))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hD (by linarith)
  have hlogt : 0 ≤ Real.log |ρ.im| := Real.log_nonneg (by linarith)
  have := div_le_div_of_nonneg_right hE hlogt
  linarith

end RMF
