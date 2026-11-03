/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.ReductionExplicit
import RMF.UniformLower.FinalCells

/-!
# The final assembly: the regimes' constants

The constants the regime lemmas of the final assembly reach, as real numbers, and their numeric
lower bounds, for the target `E|S(x)|^{2q} ≥ 10⁻¹⁰·T(q, x)` at `x ≥ exp(e^{6000})`.  With
`G = e^{-0.592}/2`, `Γ = RMF.perScaleConst` and `β = q(1-2q)`:

* **B1**, `0 < q ≤ 9/20`, one scale `k = 21`, the reduction's tilt `V = 32/q`:
  `RMF.PhiB1 = RMF.mainB1 - 216·cJ·e^{-32} - RMF.errB`, `mainB1 = (1-2q)cRed·2^{2q-1}(G/(64/q))^q
  Γ(q,1)e^{-β(21.7866 + 9.003e^{-21})}` and `errB = cErr·e^{-(1376/1377)max(37/2, 6000q)}`;
* **B2**, `9/20 ≤ q < ½`, the scales `k ≥ 22` counted as `(3/5)m`: `RMF.PhiB2`, with
  `RMF.perScaleLow2` (`Γ` at `c₃ = 0.17784`) and `N ≥ e^{-20.7867β - q}`;
* **H**, `q = ½`, `V = 64`: `RMF.cHalfLB`, the subtracted term's constant `17.3`;
* **S**, `½ < q ≤ ½ + 1/(2·10⁸)`, `V = 64`, the scales capped at `J = ⌊1/(2δ)⌋`: `RMF.PhiSl`, the
  subtracted term's constant `33`.

Each is bounded below through the certificates of `RMF/UniformLower/FinalCells.lean`
(`RMF.finalCells_spec`): `RMF.PhiB1_ge`, `RMF.PhiB2_ge`, `RMF.cHalfLB_ge` (`≥ 10⁻⁷`),
`RMF.PhiSl_ge`, and the floor's and Lyapunov's numerals `RMF.floor_num`, `RMF.lyap_num`.  The
subtracted terms' constants are those of `RMF.integral_rpow_lineDiv_le_subtracted_belowHalf`
(`216`), `RMF.integral_sqrt_lineDiv_le_subtracted_half` (`17.3`) and
`RMF.integral_rpow_lineDiv_le_subtracted_sliver` (`33`).

In the mid range `2100 ≤ log log x ≤ 6000` below `½`, at the tilt `V′ = 32/q + 6000`:
`RMF.PhiB1Mid` and `RMF.PhiB2Mid`, the main terms B1's and B2's times `(32/(32 + 6000q))^q` (B2″
counting `m/2` scales), the subtracted term `cJ(q)e^{-32}` (Jensen) and the error term
`RMF.errBMid`; bounded through `RMF.finalCellsMid_spec`: `RMF.PhiB1Mid_ge`, `RMF.PhiB2Mid_ge`, and
NH's and F″'s numerals `RMF.nh_num`, `RMF.floor_num_mid`.
-/

namespace RMF

/-! ### The constants -/

/-- **B1's main term**: `(1-2q)cRed(q)2^{2q-1}(G/(2·32/q))^qΓ(q,1)e^{-q(1-2q)(21 + 0.7866 +
9.003e^{-21})}`, `G = e^{-0.592}/2`. -/
noncomputable def mainB1 (q : ℝ) : ℝ :=
  (1 - 2 * q) * cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
    * perScaleConst q 1 * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21))

/-- **The error term below `½`**: `cErr(q)e^{-(1376/1377)max(37/2, 6000q)}`. -/
noncomputable def errB (q : ℝ) : ℝ :=
  cErr q * Real.exp (-(1376 / 1377 * max (37 / 2) (6000 * q)))

/-- **B1's constant**: `mainB1 - 216cJ(q)e^{-32} - errB`. -/
noncomputable def PhiB1 (q : ℝ) : ℝ := mainB1 q - 216 * cJ q * Real.exp (-32) - errB q

/-- **The per-scale constant at `c₃ = 0.17784`**: `RMF.perScaleConst` with `c3FloorK` replaced by
its floor on `[9/20, ½)` for ladder lengths `K ≥ 2`. -/
noncomputable def perScaleLow2 (q : ℝ) : ℝ :=
  (0.17784 : ℝ) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
    * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))

/-- **B2's main term**:
`cRed(q)2^{2q-1}(G/(2·32/q))^q(3/5)perScaleLow2(q)e^{-20.7867q(1-2q) - q}`. -/
noncomputable def mainB2 (q : ℝ) : ℝ :=
  cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q * (3 / 5)
    * perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)

/-- **B2's constant**: `mainB2 - 216cJ(q)e^{-32} - errB`. -/
noncomputable def PhiB2 (q : ℝ) : ℝ := mainB2 q - 216 * cJ q * Real.exp (-32) - errB q

/-- **H's constant**: `cRed(½)(G/128)^{1/2}Γ(½,1)(3/5) - 17.3cJ(½)e^{-32} - cErr(½)e^{-3000}`. -/
noncomputable def cHalfLB : ℝ :=
  cRed (1 / 2) * (Real.exp (-0.592) / 2 / 128) ^ (1 / 2 : ℝ) * perScaleConst (1 / 2) 1 * (3 / 5)
    - 173 / 10 * cJ (1 / 2) * Real.exp (-32) - cErr (1 / 2) * Real.exp (-3000)

/-- **S's main term**: `cRed(q)2^{2q-1}(G/128)^qΓ(q,2)·½e^{-q/2}e^{-10⁻⁴}`. -/
noncomputable def mainSl (q : ℝ) : ℝ :=
  cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / 128) ^ q * perScaleConst q 2
    * (1 / 2) * Real.exp (-(q / 2)) * Real.exp (-(1 / 10 ^ 4))

/-- **S's constant**: `mainSl - 33cJ(q)e^{-64q} - cErr(q)e^{-3000}`. -/
noncomputable def PhiSl (q : ℝ) : ℝ :=
  mainSl q - 33 * cJ q * Real.exp (-(64 * q)) - cErr q * Real.exp (-3000)

/-! ### The reduction's constants, bounded -/

/-- `cJ(q) ≤ 1` for `0 ≤ q ≤ 1`: every factor is at most `1`. -/
lemma cJ_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : cJ q ≤ 1 := by
  unfold cJ
  have h1 : (3 : ℝ) ^ (-(1 - q)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-max (1 - 2 * q) 0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.2 (le_max_right _ _))
  have h3 : (8 * Real.pi) ^ (-q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  calc (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * (8 * Real.pi) ^ (-q)
      ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by norm_num)) h3 (by positivity)
          (by norm_num)
    _ = 1 := by norm_num

/-- `cErr(q) ≤ 16` for `q ≤ 1`. -/
lemma cErr_le_sixteen {q : ℝ} (hq1 : q ≤ 1) : cErr q ≤ 16 := by
  unfold cErr
  have h1 : (3 : ℝ) ^ (-(1 - q)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-max (1 - 2 * q) 0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.2 (le_max_right _ _))
  have h3 : (16 : ℝ) ^ q ≤ 16 := by
    calc (16 : ℝ) ^ q ≤ 16 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
      _ = 16 := Real.rpow_one 16
  calc (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * (16 : ℝ) ^ q
      ≤ 1 * 1 * 16 :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by norm_num)) h3 (by positivity)
          (by norm_num)
    _ = 16 := by norm_num

/-- **The error term on a cell `[a, b] ⊆ [0, ½]`**: `errB(q) ≤ e^{cellLogErr b u}` for
`u ≤ max(37/2, 6000a)` (`cErr` is increasing in `q`). -/
lemma errB_le_exp_cellLogErr {a b u q : ℝ} (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2)
    (hu : u ≤ max (37 / 2) (6000 * a)) : errB q ≤ Real.exp (cellLogErr b u) := by
  have hmax : u ≤ max (37 / 2) (6000 * q) := hu.trans (max_le_max le_rfl (by linarith))
  unfold errB cErr cellLogErr
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16), ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have f3 := mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
  have f2 := mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have f16 := mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16))
  linarith

/-! ### The main terms on a cell -/

/-- **The core on a cell `[a, b] ⊆ (0, ½]`**: for `q ∈ [a, b]`, `0 < c ≤ min(1, C)` and
`ℓ ≤ q log q`, `e^{cellLogCore a b c ℓ} ≤ cRed(q)2^{2q-1}(G/(2·32/q))^qΓ_C(q)`, `Γ_C` the
per-scale constant at `c₃ = C`: every factor at its worse end, `π ≤ 3.1416`. -/
lemma exp_cellLogCore_le {a b c C ℓ q : ℝ} (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2)
    (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hcC : c ≤ C) (hℓ : ℓ ≤ q * Real.log q) :
    Real.exp (cellLogCore a b c ℓ)
      ≤ cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
        * (C ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
          * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))) := by
  have hC0 : 0 < C := lt_of_lt_of_le hc0 hcC
  have he100 : Real.exp (-100) ≤ 1 / 1000 := by interval_decide (trust := kernel)
  have hP : (0.3165 : ℝ) ≤ (1 - Real.exp (-100)) * 0.31689 := by linarith
  have hP0 : (0 : ℝ) < (1 - Real.exp (-100)) * 0.31689 := by linarith
  have hπ0 : (0 : ℝ) < 16 * Real.pi := by positivity
  have hG : Real.exp (-0.592) / 2 / (2 * (32 / q)) = Real.exp (-0.592) * q / 128 := by
    field_simp
    ring
  have hG0 : 0 < Real.exp (-0.592) * q / 128 := by positivity
  have hGlog : Real.log (Real.exp (-0.592) * q / 128) = -0.592 - 7 * Real.log 2 + Real.log q := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) hq0.ne',
      Real.log_exp, show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    push_cast
    ring
  unfold cRed
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q), hG, ← Real.exp_mul]
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
    Real.rpow_def_of_pos hπ0, Real.rpow_def_of_pos hG0, Real.rpow_def_of_pos hC0,
    Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6482),
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [hGlog]
  unfold cellLogCore
  have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have l6 : 0 ≤ Real.log 6482 := Real.log_nonneg (by norm_num)
  have lπ0 : 0 ≤ Real.log (16 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have lπ : Real.log (16 * Real.pi) ≤ Real.log (16 * 3.1416) :=
    Real.log_le_log hπ0 (by linarith [Real.pi_lt_d4])
  have lc : Real.log c ≤ Real.log C := Real.log_le_log hc0 hcC
  have lc0 : Real.log c ≤ 0 := Real.log_nonpos hc0.le hc1
  have lP : Real.log 0.3165 ≤ Real.log ((1 - Real.exp (-100)) * 0.31689) :=
    Real.log_le_log (by norm_num) hP
  have lP0 : Real.log 0.3165 ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have f3 := mul_le_mul_of_nonneg_right haq l3
  have f2a := mul_le_mul_of_nonneg_right haq l2
  have f2b := mul_le_mul_of_nonneg_right hqb l2
  have fπa := mul_le_mul_of_nonneg_right hqb lπ0
  have fπb := mul_le_mul_of_nonneg_left lπ (by linarith : (0 : ℝ) ≤ b)
  have fC := mul_le_mul_of_nonneg_left lc (by linarith : (0 : ℝ) ≤ 2 - q)
  have fc := mul_le_mul_of_nonpos_right haq lc0
  have fP := mul_le_mul_of_nonneg_left lP (by linarith : (0 : ℝ) ≤ 2 - q)
  have fP0 := mul_le_mul_of_nonpos_right haq lP0
  have f6 := mul_le_mul_of_nonneg_right haq l6
  have fq : 0 ≤ (q - a) * (4.50001 - 2 * (q + a)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **The core on a cell `[a, b] ⊆ [½, 1]`**: for `q ∈ [a, b]` and `0 < c ≤ min(1, C)`,
`e^{cellLogHalfCore a b c} ≤ cRed(q)2^{2q-1}(G/128)^qΓ_C(q)`. -/
lemma exp_cellLogHalfCore_le {a b c C q : ℝ} (ha : 1 / 2 ≤ a) (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 1) (hc0 : 0 < c) (hc1 : c ≤ 1) (hcC : c ≤ C) :
    Real.exp (cellLogHalfCore a b c)
      ≤ cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / 128) ^ q
        * (C ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
          * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))) := by
  have hC0 : 0 < C := lt_of_lt_of_le hc0 hcC
  have he100 : Real.exp (-100) ≤ 1 / 1000 := by interval_decide (trust := kernel)
  have hP : (0.3165 : ℝ) ≤ (1 - Real.exp (-100)) * 0.31689 := by linarith
  have hP0 : (0 : ℝ) < (1 - Real.exp (-100)) * 0.31689 := by linarith
  have hπ0 : (0 : ℝ) < 16 * Real.pi := by positivity
  have hG0 : (0 : ℝ) < Real.exp (-0.592) / 2 / 128 := by positivity
  have hGlog : Real.log (Real.exp (-0.592) / 2 / 128) = -0.592 - 8 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_div (by positivity) (by norm_num),
      Real.log_exp, show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    push_cast
    ring
  unfold cRed
  rw [max_eq_right (by linarith : 1 - 2 * q ≤ 0), neg_zero, Real.rpow_zero, mul_one,
    ← Real.exp_mul]
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
    Real.rpow_def_of_pos hπ0, Real.rpow_def_of_pos hG0, Real.rpow_def_of_pos hC0,
    Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6482),
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [hGlog]
  unfold cellLogHalfCore
  have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have l6 : 0 ≤ Real.log 6482 := Real.log_nonneg (by norm_num)
  have lπ0 : 0 ≤ Real.log (16 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have lπ : Real.log (16 * Real.pi) ≤ Real.log (16 * 3.1416) :=
    Real.log_le_log hπ0 (by linarith [Real.pi_lt_d4])
  have lc : Real.log c ≤ Real.log C := Real.log_le_log hc0 hcC
  have lc0 : Real.log c ≤ 0 := Real.log_nonpos hc0.le hc1
  have lP : Real.log 0.3165 ≤ Real.log ((1 - Real.exp (-100)) * 0.31689) :=
    Real.log_le_log (by norm_num) hP
  have lP0 : Real.log 0.3165 ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have f3 := mul_le_mul_of_nonneg_right haq l3
  have f2a := mul_le_mul_of_nonneg_right haq l2
  have f2b := mul_le_mul_of_nonneg_right hqb l2
  have fπa := mul_le_mul_of_nonneg_right hqb lπ0
  have fπb := mul_le_mul_of_nonneg_left lπ (by linarith : (0 : ℝ) ≤ b)
  have fC := mul_le_mul_of_nonneg_left lc (by linarith : (0 : ℝ) ≤ 2 - q)
  have fc := mul_le_mul_of_nonpos_right haq lc0
  have fP := mul_le_mul_of_nonneg_left lP (by linarith : (0 : ℝ) ≤ 2 - q)
  have fP0 := mul_le_mul_of_nonpos_right haq lP0
  have f6 := mul_le_mul_of_nonneg_right haq l6
  have fq : 0 ≤ (q - a) * (4.50001 - 2 * (q + a)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **B1's main term on a cell**: `e^{cellLogMain a b c β ℓ} ≤ mainB1(q)` for `q ∈ [a, b]`,
`b ≤ 9/20`, `0 < c ≤ min(1, c3FloorK q 1)`, `q(1-2q) ≤ β`, `ℓ ≤ q log q`
(`21.7866 + 9.003e^{-21} ≤ 21.7867`). -/
lemma exp_cellLogMain_le_mainB1 {a b c β ℓ q : ℝ} (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 9 / 20) (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : c ≤ c3FloorK q 1)
    (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q) :
    Real.exp (cellLogMain a b c β ℓ) ≤ mainB1 q := by
  have hcore := exp_cellLogCore_le haq hqb (by linarith) hq0 hc0 hc1 hc hℓ
  have hb2 : 0 < 1 - 2 * b := by linarith
  have he21 : (90030 : ℝ) ≤ Real.exp 21 := by interval_decide (trust := kernel)
  have hs : 9.003 / Real.exp 21 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hβq0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0.le (by linarith)
  have hN : Real.exp (-(β * 21.7867))
      ≤ Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 := mul_le_mul_of_nonneg_left hs hβq0
    linarith
  have e1 : Real.exp (cellLogMain a b c β ℓ)
      = (1 - 2 * b) * Real.exp (cellLogCore a b c ℓ) * Real.exp (-(β * 21.7867)) := by
    rw [cellLogMain, show Real.log (1 - 2 * b) + cellLogCore a b c ℓ - β * 21.7867
        = Real.log (1 - 2 * b) + cellLogCore a b c ℓ + -(β * 21.7867) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hb2]
  have e2 : mainB1 q = (1 - 2 * q) * (cRed q * (2 : ℝ) ^ (2 * q - 1)
      * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
      * (c3FloorK q 1 ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))))
      * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)) := by
    rw [mainB1, perScaleConst]
    ring
  rw [e1, e2]
  have hX0 := le_trans (Real.exp_pos _).le hcore
  exact mul_le_mul (mul_le_mul (by linarith) hcore (Real.exp_pos _).le (by linarith)) hN
    (Real.exp_pos _).le (mul_nonneg (by linarith) hX0)

/-- `c3FloorK q K = 0.23292` on the grid step `[½, 201/400)`, for every ladder length. -/
lemma c3FloorK_eq_of_half_le {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 201 / 400) (K : ℕ) :
    c3FloorK q K = 0.23292 := by
  have hfl : ⌊400 * q⌋₊ = 200 := by
    rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> push_cast <;> linarith
  rw [c3FloorK, if_neg (fun h => by linarith [h.2]), c3Floor, hfl]
  rfl

/-! ### The constants from their certificates -/

/-- **B1 on a cell**: `PhiB1(q) ≥ 10⁻¹⁰` for `q ∈ [a, b]`, `b ≤ 9/20`, from
`lam ≤ cellLogMain a b c β ℓ` and `10⁻¹⁰ + 216e^{-32} + e^{cellLogErr b u} ≤ e^{lam}` (`cJ ≤ 1`). -/
theorem PhiB1_ge_of_cell {a b c β ℓ u lam q : ℝ} (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 9 / 20)
    (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : c ≤ c3FloorK q 1)
    (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q) (hu : u ≤ max (37 / 2) (6000 * a))
    (hlam : lam ≤ cellLogMain a b c β ℓ)
    (hcert : 1 / 10 ^ 10 + 216 * Real.exp (-32) + Real.exp (cellLogErr b u) ≤ Real.exp lam) :
    1 / 10 ^ 10 ≤ PhiB1 q := by
  have hmain := exp_cellLogMain_le_mainB1 haq hqb hb hq0 hc0 hc1 hc hβ hℓ
  have hlam' := Real.exp_le_exp.2 hlam
  have hJ := cJ_le_one hq0.le (by linarith)
  have herr := errB_le_exp_cellLogErr haq hqb (by linarith) hu
  have hsub : 216 * cJ q * Real.exp (-32) ≤ 216 * Real.exp (-32) := by
    have := Real.exp_pos (-32)
    nlinarith
  unfold PhiB1
  linarith

/-- **B2 from its certificate**: `PhiB2(q) ≥ 10⁻¹⁰` on `[9/20, ½)` (the cell `[9/20, ½]`,
`q log q ≥ (9/20)log(9/20)`, `q(1-2q) ≤ 9/200`). -/
theorem PhiB2_ge_of_cert {lam : ℝ}
    (hlam : lam ≤ Real.log (3 / 5)
      + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2)
    (hcert : 1 / 10 ^ 10 + 216 * Real.exp (-32) + Real.exp (cellLogErr (1 / 2) 2700)
      ≤ Real.exp lam)
    {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) : 1 / 10 ^ 10 ≤ PhiB2 q := by
  have hqpos : 0 < q := by linarith
  have hℓ := mul_log_ge_of_exp_neg_one_le (by linarith [Real.exp_neg_one_lt_d9]) hq0
  have hcore := exp_cellLogCore_le (c := 0.17784) (C := 0.17784) hq0 hq1.le le_rfl hqpos
    (by norm_num) (by norm_num) le_rfl hℓ
  have hβ := mul_one_sub_two_mul_le_of_ge (by norm_num) hq0
  have hN : Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2)
      ≤ Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (Real.log (3 / 5)
      + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2)
      = 3 / 5 * Real.exp (cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)))
        * Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2) := by
    rw [show Real.log (3 / 5) + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
        - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2
        = Real.log (3 / 5) + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
          + (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have e2 : mainB2 q = 3 / 5 * (cRed q * (2 : ℝ) ^ (2 * q - 1)
      * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
      * ((0.17784 : ℝ) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))))
      * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := by
    rw [mainB2, perScaleLow2]
    ring
  have hX0 := le_trans (Real.exp_pos _).le hcore
  have hmain : Real.exp lam ≤ mainB2 q := by
    calc Real.exp lam ≤ _ := Real.exp_le_exp.2 hlam
      _ = _ := e1
      _ ≤ _ := by
        rw [e2]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcore (by norm_num)) hN
          (Real.exp_pos _).le (mul_nonneg (by norm_num) hX0)
  have hJ := cJ_le_one hqpos.le (by linarith)
  have herr := errB_le_exp_cellLogErr (a := 9 / 20) (u := 2700) hq0 hq1.le le_rfl
    (le_max_of_le_right (by norm_num))
  have hsub : 216 * cJ q * Real.exp (-32) ≤ 216 * Real.exp (-32) := by
    have := Real.exp_pos (-32)
    nlinarith
  unfold PhiB2
  linarith

/-- **H from its certificate**: `cHalfLB ≥ 10⁻⁷` (`c₃ = c3FloorTab 200 = 0.23292` at `q = ½`,
`cJ(½) ≤ 1`, `cErr(½) ≤ 16`). -/
theorem cHalfLB_ge_of_cert {lam : ℝ}
    (hlam : lam ≤ cellLogHalfCore (1 / 2) (1 / 2) 0.23292 + Real.log (3 / 5))
    (hcert : 1 / 10 ^ 7 + 173 / 10 * Real.exp (-32) + 16 * Real.exp (-3000) ≤ Real.exp lam) :
    1 / 10 ^ 7 ≤ cHalfLB := by
  have hC := c3FloorK_eq_of_half_le (q := 1 / 2) le_rfl (by norm_num) 1
  have hcore := exp_cellLogHalfCore_le (a := 1 / 2) (b := 1 / 2) (q := 1 / 2) (c := 0.23292)
    (C := c3FloorK (1 / 2) 1) le_rfl le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
    hC.ge
  have h2 : (2 : ℝ) ^ (2 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
  rw [h2, mul_one] at hcore
  have hmain : Real.exp lam
      ≤ cRed (1 / 2) * (Real.exp (-0.592) / 2 / 128) ^ (1 / 2 : ℝ) * perScaleConst (1 / 2) 1
        * (3 / 5) := by
    calc Real.exp lam ≤ Real.exp (cellLogHalfCore (1 / 2) (1 / 2) 0.23292 + Real.log (3 / 5)) :=
          Real.exp_le_exp.2 hlam
      _ = Real.exp (cellLogHalfCore (1 / 2) (1 / 2) 0.23292) * (3 / 5) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ _ := by
          rw [perScaleConst]
          exact mul_le_mul_of_nonneg_right hcore (by norm_num)
  have hJ := cJ_le_one (q := 1 / 2) (by norm_num) (by norm_num)
  have hE := cErr_le_sixteen (q := 1 / 2) (by norm_num)
  have hsub : 173 / 10 * cJ (1 / 2) * Real.exp (-32) ≤ 173 / 10 * Real.exp (-32) := by
    have := Real.exp_pos (-32)
    nlinarith
  have herr : cErr (1 / 2) * Real.exp (-3000) ≤ 16 * Real.exp (-3000) := by
    have := Real.exp_pos (-3000)
    nlinarith
  unfold cHalfLB
  linarith

/-- **S from its certificate**: `PhiSl(q) ≥ 10⁻¹⁰` on `(½, ½ + 1/(2·10⁸)]` (`c₃ = 0.23292`,
`cJ ≤ 1`, `e^{-64q} ≤ e^{-32}`, `cErr ≤ 16`). -/
theorem PhiSl_ge_of_cert {lam : ℝ}
    (hlam : lam ≤ cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
      - (1 / 2 + 1 / (2 * 10 ^ 8)) / 2 - 1 / 10 ^ 4)
    (hcert : 1 / 10 ^ 10 + 33 * Real.exp (-32) + 16 * Real.exp (-3000) ≤ Real.exp lam)
    {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8)) : 1 / 10 ^ 10 ≤ PhiSl q := by
  have hC := c3FloorK_eq_of_half_le hq0.le (by linarith) 2
  have hcore := exp_cellLogHalfCore_le (c := 0.23292) (C := c3FloorK q 2) le_rfl hq0.le hq1
    (by norm_num) (by norm_num) (by norm_num) hC.ge
  have hN : Real.exp (-((1 / 2 + 1 / (2 * 10 ^ 8)) / 2)) ≤ Real.exp (-(q / 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
      - (1 / 2 + 1 / (2 * 10 ^ 8)) / 2 - 1 / 10 ^ 4)
      = Real.exp (cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292) * (1 / 2)
        * Real.exp (-((1 / 2 + 1 / (2 * 10 ^ 8)) / 2)) * Real.exp (-(1 / 10 ^ 4)) := by
    rw [show cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
        - (1 / 2 + 1 / (2 * 10 ^ 8)) / 2 - 1 / 10 ^ 4
        = cellLogHalfCore (1 / 2) (1 / 2 + 1 / (2 * 10 ^ 8)) 0.23292 + Real.log (1 / 2)
          + -((1 / 2 + 1 / (2 * 10 ^ 8)) / 2) + -(1 / 10 ^ 4) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have hX0 := le_trans (Real.exp_pos _).le hcore
  have hmain : Real.exp lam ≤ mainSl q := by
    calc Real.exp lam ≤ _ := Real.exp_le_exp.2 hlam
      _ = _ := e1
      _ ≤ _ := by
        rw [mainSl, perScaleConst]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hcore
          (by norm_num)) hN (Real.exp_pos _).le (mul_nonneg hX0 (by norm_num)))
          (Real.exp_pos _).le
  have hJ := cJ_le_one (q := q) (by linarith) (by linarith)
  have hE := cErr_le_sixteen (q := q) (by linarith)
  have h64 : Real.exp (-(64 * q)) ≤ Real.exp (-32) := Real.exp_le_exp.2 (by linarith)
  have hsub : 33 * cJ q * Real.exp (-(64 * q)) ≤ 33 * Real.exp (-32) := by
    have := Real.exp_pos (-(64 * q))
    have hJ0 := cJ_pos q
    nlinarith
  have herr : cErr q * Real.exp (-3000) ≤ 16 * Real.exp (-3000) := by
    have := Real.exp_pos (-3000)
    nlinarith
  unfold PhiSl
  linarith

/-! ### The numerals -/

/-- **B1**: `PhiB1(q) ≥ 10⁻¹⁰` for `0 < q ≤ 9/20` (19 cells, certified margin `≥ ×11.97`). -/
theorem PhiB1_ge {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 9 / 20) : 1 / 10 ^ 10 ≤ PhiB1 q := by
  obtain ⟨a, b, c, β, ℓ, u, lam, haq, hqb, hb, hc0, hc1, hc, hβ, hℓ, hu, hlam, hcert⟩ :=
    finalCells_spec.1 q hq0 hq
  exact PhiB1_ge_of_cell haq hqb hb hq0 hc0 hc1 hc hβ hℓ hu hlam hcert

/-- **B2**: `PhiB2(q) ≥ 10⁻¹⁰` for `9/20 ≤ q < ½` (certified margin `×119`). -/
theorem PhiB2_ge {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) : 1 / 10 ^ 10 ≤ PhiB2 q := by
  obtain ⟨lam, hlam, hcert⟩ := finalCells_spec.2.1
  exact PhiB2_ge_of_cert hlam hcert hq0 hq1

/-- **H**: `cHalfLB ≥ 10⁻⁷` (certified `cHalfLB ≥ 1.88·10⁻⁷`). -/
theorem cHalfLB_ge : 1 / 10 ^ 7 ≤ cHalfLB := by
  obtain ⟨lam, hlam, hcert⟩ := finalCells_spec.2.2.1
  exact cHalfLB_ge_of_cert hlam hcert

/-- **S**: `PhiSl(q) ≥ 10⁻¹⁰` for `½ < q ≤ ½ + 1/(2·10⁸)` (certified margin `×1222`). -/
theorem PhiSl_ge {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1 / 2 + 1 / (2 * 10 ^ 8)) :
    1 / 10 ^ 10 ≤ PhiSl q := by
  obtain ⟨lam, hlam, hcert⟩ := finalCells_spec.2.2.2.1
  exact PhiSl_ge_of_cert hlam hcert hq0 hq1

/-- **F, the floor's numeral**: `10⁻¹⁰ ≤ (1/6)e^{(37/12000)log(49/100)}e^{-37/2}(1 - 37/6000)`
(margin `×15.3`). -/
theorem floor_num : (1 : ℝ) / 10 ^ 10
    ≤ 1 / 6 * Real.exp (37 / 12000 * Real.log (49 / 100)) * Real.exp (-(37 / 2))
      * (1 - 37 / 6000) :=
  finalCells_spec.2.2.2.2.1

/-- **L, Lyapunov's numeral**: `10⁻¹⁰e^{1/2 + 1/(2·10⁸)} ≤ e^{(1 + 10⁻⁸)log 10⁻⁸}`
(margin `×60.7`). -/
theorem lyap_num : (1 : ℝ) / 10 ^ 10 * Real.exp (1 / 2 + 1 / (2 * 10 ^ 8))
    ≤ Real.exp ((1 + 1 / 10 ^ 8) * Real.log (1 / 10 ^ 8)) :=
  finalCells_spec.2.2.2.2.2

/-! ### For the regimes -/

/-- `c3Floor q ≥ 0.17784` on `[9/20, ½)`: the table `c3FloorTab` on the grid steps `180, …, 199`. -/
lemma c3Floor_ge_of_nine_twentieths_le {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) :
    0.17784 ≤ c3Floor q := by
  have hn0 : 180 ≤ ⌊400 * q⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hn1 : ⌊400 * q⌋₊ < 200 := (Nat.floor_lt (by linarith)).2 (by push_cast; linarith)
  unfold c3Floor
  generalize ⌊400 * q⌋₊ = n at hn0 hn1
  interval_cases n
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.17784)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.17784)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.18309)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.18309)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.18832)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.18832)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.19357)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.19357)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.19883)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.19883)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.20411)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.20411)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.20941)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.20941)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.21471)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.21471)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.22004)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.22004)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.22539)
  · exact (by norm_num : (0.17784 : ℝ) ≤ 0.22539)

/-- **B2's per-scale constant**: `perScaleLow2 q ≤ perScaleConst q K` on `[9/20, ½)` for every
ladder length `K ≠ 1`. -/
theorem perScaleLow2_le_perScaleConst {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) {K : ℕ}
    (hK : K ≠ 1) : perScaleLow2 q ≤ perScaleConst q K := by
  have hc : (0.17784 : ℝ) ≤ c3FloorK q K := by
    rw [c3FloorK, if_neg (fun h => hK h.1)]
    exact c3Floor_ge_of_nine_twentieths_le hq0 hq1
  have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  have hr : (0.17784 : ℝ) ^ (2 - q) ≤ c3FloorK q K ^ (2 - q) :=
    Real.rpow_le_rpow (by norm_num) hc (by linarith)
  have hX : 0 ≤ Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * (2 : ℝ) ^ (-q)
      * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q)) := by positivity
  have e1 : perScaleLow2 q = (0.17784 : ℝ) ^ (2 - q) * (Real.exp (2 * (1 - q) + 0.50001)
      ^ (-(1 - q)) * (2 : ℝ) ^ (-q) * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q)
      * (6482 : ℝ) ^ (-(1 - q))) := by
    rw [perScaleLow2]
    ring
  have e2 : perScaleConst q K = c3FloorK q K ^ (2 - q) * (Real.exp (2 * (1 - q) + 0.50001)
      ^ (-(1 - q)) * (2 : ℝ) ^ (-q) * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q)
      * (6482 : ℝ) ^ (-(1 - q))) := by
    rw [perScaleConst]
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hr hX

/-- **S's per-scale constant**: `perScaleConst q K` does not depend on `K` on `[½, 201/400)`
(`c3FloorK q K = 0.23292`). -/
theorem perScaleConst_eq_of_half_le {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 201 / 400) (K K' : ℕ) :
    perScaleConst q K = perScaleConst q K' := by
  unfold perScaleConst
  rw [c3FloorK_eq_of_half_le hq0 hq1 K, c3FloorK_eq_of_half_le hq0 hq1 K']

/-! ### The mid range `2100 ≤ log log x ≤ 6000` -/

/-- **The error term below `½`, mid range**: `cErr(q)e^{-(545/546)max(37/2, 2100q)}`. -/
noncomputable def errBMid (q : ℝ) : ℝ :=
  cErr q * Real.exp (-(545 / 546 * max (37 / 2) (2100 * q)))

/-- **B1″'s main term**: B1's at the tilt `V′ = 32/q + 6000`, `mainB1(q)(32/(32 + 6000q))^q`. -/
noncomputable def mainB1Mid (q : ℝ) : ℝ := mainB1 q * (32 / (32 + 6000 * q)) ^ q

/-- **B1″'s constant**: `mainB1Mid - cJ(q)e^{-32} - errBMid`. -/
noncomputable def PhiB1Mid (q : ℝ) : ℝ := mainB1Mid q - cJ q * Real.exp (-32) - errBMid q

/-- **B2″'s main term**: `cRed(q)2^{2q-1}(G/(2·32/q))^q(1/2)perScaleLow2(q)e^{-20.7867q(1-2q) - q}`
times the tilt's factor `(32/(32 + 6000q))^q`. -/
noncomputable def mainB2Mid (q : ℝ) : ℝ :=
  cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q * (1 / 2)
    * perScaleLow2 q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * (32 / (32 + 6000 * q)) ^ q

/-- **B2″'s constant**: `mainB2Mid - cJ(q)e^{-32} - errBMid`. -/
noncomputable def PhiB2Mid (q : ℝ) : ℝ := mainB2Mid q - cJ q * Real.exp (-32) - errBMid q

/-- **The tilt's factor at a cell's right end**: `e^{-b log(1 + 375b/2)} ≤ (32/(32 + 6000q))^q`
for `0 < q ≤ b`. -/
lemma exp_neg_mul_log_le_rpow_tilt {q b : ℝ} (hq : 0 < q) (hqb : q ≤ b) :
    Real.exp (-(b * Real.log (1 + 375 / 2 * b))) ≤ (32 / (32 + 6000 * q)) ^ q := by
  have hb : 0 < b := lt_of_lt_of_le hq hqb
  rw [Real.rpow_def_of_pos (by positivity)]
  refine Real.exp_le_exp.2 ?_
  rw [show (32 : ℝ) / (32 + 6000 * q) = (1 + 375 / 2 * q)⁻¹ by
      rw [show (1 : ℝ) + 375 / 2 * q = (32 + 6000 * q) / 32 by ring, inv_div],
    Real.log_inv]
  have h1 : Real.log (1 + 375 / 2 * q) ≤ Real.log (1 + 375 / 2 * b) :=
    Real.log_le_log (by positivity) (by linarith)
  have h0 : 0 ≤ Real.log (1 + 375 / 2 * q) := Real.log_nonneg (by linarith)
  have := mul_le_mul hqb h1 h0 hb.le
  linarith

/-- **The error term on a cell `[a, b] ⊆ [0, ½]`, mid range**: `errBMid(q) ≤ e^{cellLogErrMid b u}`
for `u ≤ max(37/2, 2100a)` (`cErr` is increasing in `q`). -/
lemma errBMid_le_exp_cellLogErrMid {a b u q : ℝ} (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2)
    (hu : u ≤ max (37 / 2) (2100 * a)) : errBMid q ≤ Real.exp (cellLogErrMid b u) := by
  have hmax : u ≤ max (37 / 2) (2100 * q) := hu.trans (max_le_max le_rfl (by linarith))
  unfold errBMid cErr cellLogErrMid
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16), ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have f3 := mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
  have f2 := mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have f16 := mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16))
  linarith

/-- **B1″'s main term on a cell**: `e^{cellLogMainMid a b c β ℓ} ≤ mainB1Mid(q)` under the
hypotheses of `RMF.exp_cellLogMain_le_mainB1`. -/
lemma exp_cellLogMainMid_le_mainB1Mid {a b c β ℓ q : ℝ} (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 9 / 20) (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : c ≤ c3FloorK q 1)
    (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q) :
    Real.exp (cellLogMainMid a b c β ℓ) ≤ mainB1Mid q := by
  have hmain := exp_cellLogMain_le_mainB1 haq hqb hb hq0 hc0 hc1 hc hβ hℓ
  have hρ := exp_neg_mul_log_le_rpow_tilt hq0 hqb
  rw [cellLogMainMid, sub_eq_add_neg, Real.exp_add, mainB1Mid]
  exact mul_le_mul hmain hρ (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hmain)

/-- **B1″ on a cell**: `PhiB1Mid(q) ≥ 10⁻¹⁰` for `q ∈ [a, b]`, `b ≤ 9/20`, from
`lam ≤ cellLogMainMid a b c β ℓ` and `10⁻¹⁰ + e^{-32} + e^{cellLogErrMid b u} ≤ e^{lam}`
(`cJ ≤ 1`). -/
theorem PhiB1Mid_ge_of_cell {a b c β ℓ u lam q : ℝ} (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 9 / 20) (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : c ≤ c3FloorK q 1)
    (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q) (hu : u ≤ max (37 / 2) (2100 * a))
    (hlam : lam ≤ cellLogMainMid a b c β ℓ)
    (hcert : 1 / 10 ^ 10 + Real.exp (-32) + Real.exp (cellLogErrMid b u) ≤ Real.exp lam) :
    1 / 10 ^ 10 ≤ PhiB1Mid q := by
  have hmain := exp_cellLogMainMid_le_mainB1Mid haq hqb hb hq0 hc0 hc1 hc hβ hℓ
  have hlam' := Real.exp_le_exp.2 hlam
  have hJ := cJ_le_one hq0.le (by linarith)
  have herr := errBMid_le_exp_cellLogErrMid haq hqb (by linarith) hu
  have hsub := mul_le_mul_of_nonneg_right hJ (Real.exp_pos (-32)).le
  rw [one_mul] at hsub
  unfold PhiB1Mid
  linarith

/-- **B2″ from its certificate**: `PhiB2Mid(q) ≥ 10⁻¹⁰` on `[9/20, ½)` (the cell `[9/20, ½]`,
`q log q ≥ (9/20)log(9/20)`, `q(1-2q) ≤ 9/200`, the tilt's factor at `½`). -/
theorem PhiB2Mid_ge_of_cert {lam : ℝ}
    (hlam : lam ≤ Real.log (1 / 2)
      + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2
      - 1 / 2 * Real.log (1 + 375 / 2 * (1 / 2)))
    (hcert : 1 / 10 ^ 10 + Real.exp (-32) + Real.exp (cellLogErrMid (1 / 2) 945) ≤ Real.exp lam)
    {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) : 1 / 10 ^ 10 ≤ PhiB2Mid q := by
  have hqpos : 0 < q := by linarith
  have hℓ := mul_log_ge_of_exp_neg_one_le (by linarith [Real.exp_neg_one_lt_d9]) hq0
  have hcore := exp_cellLogCore_le (c := 0.17784) (C := 0.17784) hq0 hq1.le le_rfl hqpos
    (by norm_num) (by norm_num) le_rfl hℓ
  have hβ := mul_one_sub_two_mul_le_of_ge (by norm_num) hq0
  have hN : Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2)
      ≤ Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := Real.exp_le_exp.2 (by linarith)
  have hρ := exp_neg_mul_log_le_rpow_tilt hqpos hq1.le
  have e1 : Real.exp (Real.log (1 / 2)
      + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2
      - 1 / 2 * Real.log (1 + 375 / 2 * (1 / 2)))
      = 1 / 2 * Real.exp (cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)))
        * Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2)
        * Real.exp (-(1 / 2 * Real.log (1 + 375 / 2 * (1 / 2)))) := by
    rw [show Real.log (1 / 2)
        + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
        - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2
        - 1 / 2 * Real.log (1 + 375 / 2 * (1 / 2))
        = Real.log (1 / 2) + cellLogCore (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20))
          + (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2)
          + -(1 / 2 * Real.log (1 + 375 / 2 * (1 / 2))) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have e2 : mainB2Mid q = 1 / 2 * (cRed q * (2 : ℝ) ^ (2 * q - 1)
      * (Real.exp (-0.592) / 2 / (2 * (32 / q))) ^ q
      * ((0.17784 : ℝ) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))))
      * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) * (32 / (32 + 6000 * q)) ^ q := by
    rw [mainB2Mid, perScaleLow2]
    ring
  have hX0 := le_trans (Real.exp_pos _).le hcore
  have hmain : Real.exp lam ≤ mainB2Mid q := by
    calc Real.exp lam ≤ _ := Real.exp_le_exp.2 hlam
      _ = _ := e1
      _ ≤ _ := by
        rw [e2]
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcore (by norm_num)) hN
          (Real.exp_pos _).le (mul_nonneg (by norm_num) hX0)) hρ (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg (by norm_num) hX0) (Real.exp_pos _).le)
  have hJ := cJ_le_one hqpos.le (by linarith)
  have herr := errBMid_le_exp_cellLogErrMid (a := 9 / 20) (u := 945) hq0 hq1.le le_rfl
    (le_max_of_le_right (by norm_num))
  have hsub := mul_le_mul_of_nonneg_right hJ (Real.exp_pos (-32)).le
  rw [one_mul] at hsub
  unfold PhiB2Mid
  linarith

/-- **B1″**: `PhiB1Mid(q) ≥ 10⁻¹⁰` for `0 < q ≤ 9/20` (25 cells, certified margin `≥ ×5.23`). -/
theorem PhiB1Mid_ge {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 9 / 20) : 1 / 10 ^ 10 ≤ PhiB1Mid q := by
  obtain ⟨a, b, c, β, ℓ, u, lam, haq, hqb, hb, hc0, hc1, hc, hβ, hℓ, hu, hlam, hcert⟩ :=
    finalCellsMid_spec.1 q hq0 hq
  exact PhiB1Mid_ge_of_cell haq hqb hb hq0 hc0 hc1 hc hβ hℓ hu hlam hcert

/-- **B2″**: `PhiB2Mid(q) ≥ 10⁻¹⁰` for `9/20 ≤ q < ½` (certified margin `×10.2`). -/
theorem PhiB2Mid_ge {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) : 1 / 10 ^ 10 ≤ PhiB2Mid q := by
  obtain ⟨lam, hlam, hcert⟩ := finalCellsMid_spec.2.1
  exact PhiB2Mid_ge_of_cert hlam hcert hq0 hq1

/-- **NH, the numeral**: `10⁻¹⁰·6000^{3/4 + 3/1400}e^{18} ≤ 18·2^{-3/350}` (margin `×3.92`). -/
theorem nh_num : (1 : ℝ) / 10 ^ 10 * Real.exp ((3 / 4 + 3 / 1400) * Real.log 6000)
      * Real.exp 18
    ≤ 18 * Real.exp (-(3 / 350 * Real.log 2)) :=
  finalCellsMid_spec.2.2.1

/-- **F″, the floor's numeral at `log log x ≥ 2100`**:
`10⁻¹⁰ ≤ (1/6)e^{(37/4200)log(49/100)}e^{-37/2}(1 - 37/2100)` (margin `×15.0`). -/
theorem floor_num_mid : (1 : ℝ) / 10 ^ 10
    ≤ 1 / 6 * Real.exp (37 / 4200 * Real.log (49 / 100)) * Real.exp (-(37 / 2))
      * (1 - 37 / 2100) :=
  finalCellsMid_spec.2.2.2

end RMF
