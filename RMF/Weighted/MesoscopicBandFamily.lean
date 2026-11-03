/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.MesoscopicBand
import RMF.Weighted.MesoscopicFamily

/-!
# The mesoscopic range of a band

The mesoscopic range of Proposition B (`RMF/Weighted/PropositionB.lean`) for a band `(y, z]` at
its shift `½ - c`.

## The windows

The blocks are those of the full-product family (`Weighted/MesoscopicFamily.lean`) read at
`x = z`: windows `(T_j/e, T_j]`, `T_j = e^{j-J}`, split points `w_j + 1 = ⌈exp(e^{J-j})⌉`.  A band
takes only `1 ≤ j ≤ J_b`, where

`J_b + log log(y+1) ≤ J ≤ J_b + log log y + 2`.

The lower bound keeps every split point above the band's bottom, `w_j ≥ y`, so that each block is
`RMF.exists_const_integral_rpow_setIntegral_normSq_band_block_le_rademacher`.  The upper bound
gives `log y ≥ e^{J-J_b-2}`, so that the block's moment-bound factor `(log w_j/log y)^{q(2q-1)}`
costs at most `e²·e^{(J_b-j)q(2q-1)}`: the full family's geometric factor, counted from the top of
the band's sub-range.  It is `+ 2` and not `+ 1` so that the two bounds can hold together:
`J - J_b` is an integer, and `[log log(y+1), log log y + 1]` is shorter than `1` and misses every
integer for some `y`.  The windows cover `e^{-J} < |t| ≤ e^{J_b-J}`, and `e^{J_b-J} ≍ 1/log y`.

## The sum

`RMF.integral_rpow_setIntegral_weight_primesIco_le_of_blocks_above` sums them against the weight
`(c²+t²)^{-1}`, decoupled from the shift.  With the normalisation `(log z)^{-1}` and the folding
onto positive heights, the range is `≪ e^{J_b γ}·m·(1+(1-q)√m)^{-q}`, `γ = q(2q-1)`,
`m = min{J_b, ⌈γ^{-1}⌉}`, for `½ < q ≤ 1`.  At `J ≈ log log z` this is `e^{J_b} ≍ κ = log z/log y`;
the comparison with the form `κ^{q(2q-1)}·b(min{1/(2q-1), log κ})` of Proposition B is
`RMF.exp_mul_ballotFactor_le`.  These statements do not cover `q = ½`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The weight cancellation for a band -/

/-- **The weight cancellation for a band's block.**  From a block bound
`E ≤ C·((log w_j/log y)^{q(2q-1)}·(T_j²·Λ)^q)·F` to
`e^{2(J+1-j)q}·E ≤ e²·e²·C·Λ^q·e^{(J_b-j)q(2q-1)}·F`, for `½ ≤ q ≤ 1` and
`J ≤ J_b + log log y + 2`: `RMF.mesoWeight_mul_block_le_above` with `(log y)^{-q(2q-1)}` in the
constant, which turns `e^{(J-j)γ}` into `e^{(J_b-j+2)γ} ≤ e²·e^{(J_b-j)γ}`, as
`log y ≥ e^{J-J_b-2}`. -/
lemma mesoWeight_mul_band_block_le {J j Jb y : ℕ} (hjJ : j ≤ J) (hy3 : 3 ≤ y)
    (hJ : (J : ℝ) ≤ Jb + Real.log (Real.log y) + 2) {q C F Λ E : ℝ}
    (hq2 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (hF : 0 ≤ F) (hΛ : 0 ≤ Λ)
    (hE : E ≤ C * ((Real.log (mesoW J j : ℝ) / Real.log y) ^ (q * (2 * q - 1))
        * ((mesoT J j) ^ 2 * Λ) ^ q) * F) :
    (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * E
      ≤ Real.exp 2 * Real.exp 2 * C * Λ ^ q
        * Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1))) * F := by
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hγ1 : q * (2 * q - 1) ≤ 1 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith)
      (show (0 : ℝ) ≤ 2 * q + 1 by linarith)]
  have hy3R : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy3
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hw2 : (2 : ℝ) ≤ (mesoW J j : ℝ) := by exact_mod_cast two_le_mesoW hjJ
  have hlogw0 : (0 : ℝ) ≤ Real.log (mesoW J j : ℝ) := Real.log_nonneg (by linarith)
  have hLy0 : (0 : ℝ) < Real.log y ^ (q * (2 * q - 1)) := Real.rpow_pos_of_pos hlogy _
  -- `(log w/log y)^γ = (log w)^γ·(log y)^{-γ}`, and the second factor goes into the constant
  have hsplit : (Real.log (mesoW J j : ℝ) / Real.log y) ^ (q * (2 * q - 1))
      = (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1)) * (Real.log y ^ (q * (2 * q - 1)))⁻¹ := by
    rw [Real.div_rpow hlogw0 hlogy.le, div_eq_mul_inv]
  have hC' : (0 : ℝ) ≤ C * (Real.log y ^ (q * (2 * q - 1)))⁻¹ :=
    mul_nonneg hC (inv_nonneg.2 hLy0.le)
  have hE' : E ≤ C * (Real.log y ^ (q * (2 * q - 1)))⁻¹
      * ((Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1)) * ((mesoT J j) ^ 2 * Λ) ^ q) * F := by
    refine le_trans hE (le_of_eq ?_)
    rw [hsplit]
    ring
  refine le_trans (mesoWeight_mul_block_le_above hjJ hq2 hq1 hC' hF hΛ hE') ?_
  -- `(log y)^{-γ}·e^{(J-j)γ} ≤ e²·e^{(J_b-j)γ}`, from `log y ≥ e^{J-J_b-2}`
  have hlower : Real.exp ((J : ℝ) - Jb - 2) ≤ Real.log y := by
    have h := Real.exp_le_exp.2 (show (J : ℝ) - Jb - 2 ≤ Real.log (Real.log y) by linarith)
    rwa [Real.exp_log hlogy] at h
  have hpow : Real.exp (((J : ℝ) - Jb - 2) * (q * (2 * q - 1)))
      ≤ Real.log y ^ (q * (2 * q - 1)) := by
    rw [← exp_rpow]
    exact Real.rpow_le_rpow (Real.exp_pos _).le hlower hγ0
  have hkey : (Real.log y ^ (q * (2 * q - 1)))⁻¹ * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1)))
      ≤ Real.exp 2 * Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1))) := by
    calc (Real.log y ^ (q * (2 * q - 1)))⁻¹ * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1)))
        ≤ (Real.exp (((J : ℝ) - Jb - 2) * (q * (2 * q - 1))))⁻¹
            * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (Real.exp_pos _) hpow) (Real.exp_pos _).le
      _ = Real.exp (2 * (q * (2 * q - 1))) * Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1))) := by
          rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp 2 * Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1))) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
  have hfac : (0 : ℝ) ≤ Real.exp 2 * C * Λ ^ q * F :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 2).le hC) (Real.rpow_nonneg hΛ q)) hF
  calc Real.exp 2 * (C * (Real.log y ^ (q * (2 * q - 1)))⁻¹) * Λ ^ q
        * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) * F
      = (Real.exp 2 * C * Λ ^ q * F)
          * ((Real.log y ^ (q * (2 * q - 1)))⁻¹
            * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1)))) := by ring
    _ ≤ (Real.exp 2 * C * Λ ^ q * F)
          * (Real.exp 2 * Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1)))) :=
        mul_le_mul_of_nonneg_left hkey hfac
    _ = Real.exp 2 * Real.exp 2 * C * Λ ^ q
          * Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1))) * F := by ring

/-! ### The shallow blocks of a band -/

/-- **A band's mesoscopic block below the depth threshold.**  The split, the moment bound for the
low part, and the Jensen--Mertens window bound for the high part at a shift of either sign, with no
depth, offset or threshold:
`E[(∫_{T/e}^{T}‖F_{y,z}(½+σ+it)‖²dt)^q]
  ≤ e^{143800e}·e^{48}·e^{37}·(log w/log y)^{q(2q-1)}·(T²·log z)^q`.
The band analogue of `RMF.integral_rpow_setIntegral_normSq_block_le_trivial`. -/
theorem integral_rpow_setIntegral_normSq_band_block_le_trivial {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ T q : ℝ} {y w z : ℕ}
    (hy2 : 2 ≤ y) (hyw : y ≤ w) (hw3 : 3 ≤ w) (hwz : w + 1 ≤ z)
    (hσ : -(1 / 12) ≤ σ) (hσz : 2 * |σ| * Real.log z ≤ 1) (hq2 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hT0 : 0 < T) (hT1 : T ≤ 1) (hTlo : 1 ≤ T * Real.log ((w : ℝ) + 1))
    (hThi : T * Real.log ((w : ℝ) + 1) ≤ 2) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37
        * ((Real.log w / Real.log y) ^ (q * (2 * q - 1)) * (T ^ 2 * Real.log z) ^ q) := by
  have hcast : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
  have hwzR : (w : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hwz
  have hw0 : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
  have hlogwz : Real.log w ≤ Real.log z := Real.log_le_log hw0 (by linarith)
  have hσw : 2 * |σ| * Real.log w ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hlogwz (by positivity)) hσz
  have hchaos := integral_rpow_setIntegral_normSq_primesIco_le_mertens_signed hY (z := w + 1)
    (x := (z : ℝ)) (σ := σ) (T := T) (q := q) (by omega) (by rw [hcast]; exact hwzR)
    (by linarith) (Or.inr hσz) hT0 hT1 (by rw [hcast]; exact hTlo) (by linarith) hq1
  rw [Nat.floor_natCast] at hchaos
  refine le_trans (integral_rpow_setIntegral_normSq_band_block_le_of_chaos hY hy2 hyw hw3
    (by omega) hσ hσw hq2 hq1 hT0 hThi hchaos) ?_
  -- `(e³⁷·A)^q ≤ e³⁷·A^q`
  have hlogz0 : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by linarith)
  have hA0 : (0 : ℝ) ≤ T ^ 2 * Real.log z := mul_nonneg (sq_nonneg T) hlogz0
  have hsplit : (Real.exp 37 * (T ^ 2 * Real.log z)) ^ q
      = (Real.exp 37) ^ q * (T ^ 2 * Real.log z) ^ q :=
    Real.mul_rpow (Real.exp_pos 37).le hA0
  have hexpq : (Real.exp 37) ^ q ≤ Real.exp 37 := by
    calc (Real.exp 37) ^ q ≤ (Real.exp 37) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (by norm_num)) hq1
      _ = Real.exp 37 := Real.rpow_one _
  rw [hsplit]
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
  have hw1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hratio : (0 : ℝ) ≤ (Real.log w / Real.log y) ^ (q * (2 * q - 1)) :=
    Real.rpow_nonneg (div_nonneg (Real.log_nonneg hw1) (Real.log_nonneg hy1)) _
  have hc0 : (0 : ℝ) ≤ Real.exp (143800 * Real.exp 1)
      * (Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1))) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hratio)
  have hAq : (0 : ℝ) ≤ (T ^ 2 * Real.log z) ^ q := Real.rpow_nonneg hA0 _
  calc Real.exp (143800 * Real.exp 1)
        * (Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1)))
        * ((Real.exp 37) ^ q * (T ^ 2 * Real.log z) ^ q)
      ≤ Real.exp (143800 * Real.exp 1)
        * (Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1)))
        * (Real.exp 37 * (T ^ 2 * Real.log z) ^ q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexpq hAq) hc0
    _ = Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37
        * ((Real.log w / Real.log y) ^ (q * (2 * q - 1)) * (T ^ 2 * Real.log z) ^ q) := by ring

/-! ### One weighted block of a band, both branches -/

/-- **A weighted mesoscopic block of a band, both branches.**  For the band `(y, z]` with `y ≥ 3`,
`J` blocks read at `x = z` with `J ≤ log(log z - log 2) + 1`, and `1 ≤ j ≤ J_b` with
`J_b + log log(y+1) ≤ J ≤ J_b + log log y + 2`, uniformly for `½ ≤ q ≤ 1` and `σ ≥ -1/12` with
`2|σ|·log z ≤ 1`, `e^{2(J+1-j)q}·E[(∫_{T_j/e}^{T_j}‖F_{y,z}(½+σ+it)‖²dt)^q]`
`  ≤ A·(log z)^q·e^{(J_b-j)q(2q-1)}·(1+(1-q)√j)^{-q}`. -/
theorem exists_const_mesoBlock_band_weighted_le_rademacher :
    ∃ (z₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y z J Jb j : ℕ),
          z₀ ≤ (z : ℝ) → 3 ≤ y → -(1 / 12) ≤ σ → 2 * |σ| * Real.log z ≤ 1 →
          1 / 2 ≤ q → q ≤ 1 → 1 ≤ j → j ≤ Jb →
          (J : ℝ) ≤ Real.log (Real.log z - Real.log 2) + 1 →
          (Jb : ℝ) + Real.log (Real.log ((y : ℝ) + 1)) ≤ J →
          (J : ℝ) ≤ Jb + Real.log (Real.log y) + 2 →
            (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
                * (∫ ω, (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
                    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                      (y + 1) (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (Real.log z) ^ q
                * (Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1)))
                    * (1 + (1 - q) * Real.sqrt j) ^ (-q)) := by
  obtain ⟨D₀, t₀, zb, Klo, A, hD₀, hKlo, hKloD, hA, HB⟩ :=
    exists_const_integral_rpow_setIntegral_normSq_band_block_le_rademacher (Ω := Ω)
  have hCt0 : (0 : ℝ) < Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37 := by
    positivity
  have hEE : (0 : ℝ) ≤ Real.exp 2 * Real.exp 2 := by positivity
  have hMMt : Real.exp 2 * Real.exp 2
        * (Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37)
      ≤ 3 * (Real.exp 2 * Real.exp 2)
        * (Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37 + A) := by
    nlinarith [mul_nonneg hEE hCt0.le, mul_nonneg hEE hA.le]
  have hMMs : Real.exp 2 * Real.exp 2 * A
      ≤ 3 * (Real.exp 2 * Real.exp 2)
        * (Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37 + A) := by
    nlinarith [mul_nonneg hEE hCt0.le, mul_nonneg hEE hA.le]
  set c : ℕ := t₀ + ⌈Real.log Klo⌉₊ + 10 with hcdef
  refine ⟨max zb 3,
    3 * (Real.exp 2 * Real.exp 2)
      * (Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37 + A)
      * (1 + Real.sqrt (c : ℝ)),
    mul_pos (mul_pos (by positivity) (by linarith)) (by positivity), ?_⟩
  intro Y ν hY σ q y z J Jb j hz hy3 hσ hσz hq2 hq1 hj1 hjJb hJle hJ1 hJ2
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hzb : zb ≤ (z : ℝ) := le_trans (le_max_left _ _) hz
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := le_trans (le_max_right _ _) hz
  have hlogz0 : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by linarith)
  have hΛq : (0 : ℝ) ≤ (Real.log z) ^ q := Real.rpow_nonneg hlogz0 _
  have hG : (0 : ℝ) ≤ Real.exp (((Jb : ℝ) - j) * (q * (2 * q - 1))) := (Real.exp_pos _).le
  have hMt0 : (0 : ℝ) ≤ Real.exp 2 * Real.exp 2
      * (Real.exp (143800 * Real.exp 1) * Real.exp 48 * Real.exp 37) := mul_nonneg hEE hCt0.le
  have hMs0 : (0 : ℝ) ≤ Real.exp 2 * Real.exp 2 * A := mul_nonneg hEE hA.le
  have hjJbR : (j : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hjJb
  have hy3R : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy3
  have hlogy1 : (0 : ℝ) ≤ Real.log (Real.log ((y : ℝ) + 1)) :=
    Real.log_nonneg (le_of_lt (one_lt_log_of_three_le (by linarith)))
  have hJbJ : Jb ≤ J := by
    have h : (Jb : ℝ) ≤ (J : ℝ) := by linarith
    exact_mod_cast h
  have hjJ : j ≤ J := le_trans hjJb hJbJ
  -- the split point is above the band's bottom
  have hyw : y ≤ mesoW J j := by
    have hlogy0 : (0 : ℝ) < Real.log ((y : ℝ) + 1) := Real.log_pos (by linarith)
    have hv : Real.log ((y : ℝ) + 1) ≤ mesoV J j := by
      have h := Real.exp_le_exp.2
        (show Real.log (Real.log ((y : ℝ) + 1)) ≤ (J : ℝ) - j by linarith)
      rwa [Real.exp_log hlogy0] at h
    have hb := (mesoW_bounds J j).1
    have h1 : (y : ℝ) + 1 ≤ Real.exp (mesoV J j) := by
      have h := Real.exp_le_exp.2 hv
      rwa [Real.exp_log (by linarith)] at h
    have h2 : ((y + 1 : ℕ) : ℝ) ≤ ((mesoW J j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : y + 1 ≤ mesoW J j + 1 := by exact_mod_cast h2
    omega
  have hwx := mesoW_add_one_le hj1 hz3 hJle
  have hwz : mesoW J j + 1 ≤ z := by
    have h : ((mesoW J j + 1 : ℕ) : ℝ) ≤ (z : ℝ) := by push_cast; exact hwx
    exact_mod_cast h
  obtain ⟨hTlo, hThi⟩ := mesoT_mul_log_mesoW_bounds hjJ
  rcases Nat.lt_or_ge j c with hshallow | hdeep
  · -- **shallow**: the trivial bound, with `1+√c` covering the missing saving
    have hblk := integral_rpow_setIntegral_normSq_band_block_le_trivial hY (by omega) hyw
      (by omega) hwz hσ hσz hq2 hq1 (mesoT_pos J j) (mesoT_le_one hjJ) hTlo hThi
    have hW := mesoWeight_mul_band_block_le hjJ hy3 hJ2 hq2 hq1 hCt0.le zero_le_one hlogz0
      (hblk.trans_eq (mul_one _).symm)
    exact meso_finish hMt0 hMMt hΛq hG zero_le_one
      (one_le_target_mul hq0 (by linarith) (le_of_lt hshallow)) hW
  · -- **deep**: the sharp bound, with the saving shifted from the depth to the index
    obtain ⟨D, hD4, hDle, hKl, hKb⟩ :=
      exists_harperOffset_at_split_scale (z : ℝ) (mesoT_pos J j) (mesoT_le_one hjJ) hKlo
    have hlogT : Real.log (mesoT J j) = (j : ℝ) - J := by
      simp only [mesoT, Real.log_exp]
    rw [hlogT] at hDle
    have hcR : ((c : ℕ) : ℝ) = (t₀ : ℝ) + (⌈Real.log Klo⌉₊ : ℝ) + 10 := by
      rw [hcdef]; push_cast; ring
    have hlogKlo : Real.log Klo ≤ (⌈Real.log Klo⌉₊ : ℝ) := Nat.le_ceil _
    have ht₀0 : (0 : ℝ) ≤ (t₀ : ℝ) := Nat.cast_nonneg _
    have hkey : (t₀ : ℝ) + Real.log Klo + 10 ≤ (j : ℝ) := by
      have h : ((c : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hdeep
      rw [hcR] at h
      linarith
    have hlogz1 : (1 : ℝ) < Real.log z := one_lt_log_of_three_le hz3
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have hJll : (J : ℝ) ≤ Real.log (Real.log z) + 1 := by
      refine le_trans hJle ?_
      have h := Real.log_le_log (by linarith : (0 : ℝ) < Real.log z - Real.log 2)
        (by linarith : Real.log z - Real.log 2 ≤ Real.log z)
      linarith
    have hDlog : (D : ℝ) ≤ Real.log (Real.log z) := by linarith
    -- `D₀ ≤ D`, because `exp D₀ ≤ Klo ≤ T·e^θ ≤ e^θ` while `θ < D`
    have hexpθ : (0 : ℝ) < Real.exp (harperOffset D z) := Real.exp_pos _
    have hle1 : mesoT J j * Real.exp (harperOffset D z) ≤ Real.exp (harperOffset D z) := by
      have h := mul_le_mul_of_nonneg_right (mesoT_le_one hjJ) hexpθ.le
      rwa [one_mul] at h
    have hD₀θ : (D₀ : ℝ) ≤ harperOffset D z :=
      Real.exp_le_exp.1 (le_trans hKloD (le_trans hKl hle1))
    have hD₀D : D₀ ≤ D := by
      have h : (D₀ : ℝ) < (D : ℝ) := lt_of_le_of_lt hD₀θ (harperOffset_lt_natCast D z)
      have h' : D₀ < D := by exact_mod_cast h
      omega
    -- the split point sits below the first block scale
    have hbs : ((mesoW J j : ℝ) + 1) ≤ blockScale (harperOffset D z) 0 :=
      mesoW_add_one_le_blockScale hjJ (four_mul_mesoV_le_exp_of_le hKlo hKl)
    -- the depth is at least `t₀ + 3`, and within `c` of the index
    have hn := harperBlockCount_add_one_add_offset hDlog
    have hθub : harperOffset D z < (D : ℝ) := harperOffset_lt_natCast D z
    have hnlb : (t₀ : ℝ) + 3 ≤ (harperBlockCount D z : ℝ) := by linarith
    have hn3 : t₀ + 3 ≤ harperBlockCount D z := by exact_mod_cast hnlb
    have ht₀ : t₀ ≤ harperBlockCount D z - 3 := by omega
    have hsub : ((harperBlockCount D z - 3 : ℕ) : ℝ) = (harperBlockCount D z : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : (3 : ℕ) ≤ harperBlockCount D z)]
      norm_num
    have hdepth : (j : ℝ) ≤ ((harperBlockCount D z - 3 : ℕ) : ℝ) + (c : ℝ) := by
      rw [hsub, hcR]
      linarith
    have hblk := HB Y ν hY σ (mesoT J j) q y (mesoW J j) z D hzb hD₀D hDlog (by omega) hyw
      (by omega) hwz hbs hσ hσz hq2 hq1 (mesoT_pos J j) (mesoT_le_one hjJ) hTlo hThi hKl hKb
      ht₀
    have hF₀ : (0 : ℝ)
        ≤ (1 + (1 - q) * Real.sqrt ((harperBlockCount D z - 3 : ℕ) : ℝ)) ^ (-q) :=
      Real.rpow_nonneg (target_base_pos (by linarith)).le _
    refine meso_finish hMs0 hMMs hΛq hG hF₀ (target_shift_le hq0 (by linarith) hdepth) ?_
    exact mesoWeight_mul_band_block_le hjJ hy3 hJ2 hq2 hq1 hA.le hF₀ hlogz0 hblk

/-! ### The sum over a band's blocks -/

/-- **The mesoscopic range of a band, with the weight.**  For `½ < q ≤ 1`, `c > 0`, a shift
`σ ≥ -1/12` with `2|σ|·log z ≤ 1`, and `J`, `J_b ≥ 1` as in
`RMF.exists_const_mesoBlock_band_weighted_le_rademacher`,

`E[(∫_{e^{-J}}^{e^{J_b-J}} (c²+t²)^{-1}‖F_{y,z}(½+σ+it)‖²dt)^q]
  ≤ A·(log z)^q·3·e^{J_b γ}·m·(1+(1-q)√m)^{-q}`,  `γ = q(2q-1)`, `m = min{J_b, ⌈γ^{-1}⌉}`. -/
theorem exists_const_integral_rpow_setIntegral_weight_band_le_rademacher :
    ∃ (z₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ c q : ℝ) (y z J Jb : ℕ),
          z₀ ≤ (z : ℝ) → 3 ≤ y → -(1 / 12) ≤ σ → 2 * |σ| * Real.log z ≤ 1 → 0 < c →
          1 / 2 < q → q ≤ 1 → 1 ≤ Jb →
          (J : ℝ) ≤ Real.log (Real.log z - Real.log 2) + 1 →
          (Jb : ℝ) + Real.log (Real.log ((y : ℝ) + 1)) ≤ J →
          (J : ℝ) ≤ Jb + Real.log (Real.log y) + 2 →
            (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) (Real.exp ((Jb : ℝ) - J)),
                (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
                  (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (z + 1)
                  (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (Real.log z) ^ q
                * (3 * Real.exp ((Jb : ℝ) * (q * (2 * q - 1)))
                  * ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ)
                  * (1 + (1 - q) * Real.sqrt ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ))
                      ^ (-q)) := by
  obtain ⟨zb, A, hA, HB⟩ := exists_const_mesoBlock_band_weighted_le_rademacher (Ω := Ω)
  refine ⟨max zb 3, A, hA, ?_⟩
  intro Y ν hY σ c q y z J Jb hz hy3 hσ hσz hc hq2 hq1 hJb1 hJle hJ1 hJ2
  have hq0 : (0 : ℝ) < q := by linarith
  have hzb : zb ≤ (z : ℝ) := le_trans (le_max_left _ _) hz
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := le_trans (le_max_right _ _) hz
  have hlogz0 : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by linarith)
  have hK : (0 : ℝ) ≤ A * (Real.log z) ^ q := mul_nonneg hA.le (Real.rpow_nonneg hlogz0 _)
  have hγ : (0 : ℝ) < q * (2 * q - 1) := mul_pos hq0 (by linarith)
  have hy3R : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy3
  have hJbJ : Jb ≤ J := by
    have h0 : (0 : ℝ) ≤ Real.log (Real.log ((y : ℝ) + 1)) :=
      Real.log_nonneg (le_of_lt (one_lt_log_of_three_le (by linarith)))
    have h : (Jb : ℝ) ≤ (J : ℝ) := by linarith
    exact_mod_cast h
  refine integral_rpow_setIntegral_weight_primesIco_le_of_blocks_above
    (γ := q * (2 * q - 1)) (β := 1 - q) (K := A * (Real.log z) ^ q)
    hY (y + 1) (z + 1) (by linarith) hc hq0 hq1 hγ (by linarith) hK hJb1 hJbJ ?_
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact HB Y ν hY σ q y z J Jb j hzb hy3 hσ hσz hq2.le hq1 hj.1 hj.2 hJle hJ1 hJ2

/-! ### The mesoscopic range of Proposition B -/

/-- **The mesoscopic range of a band, folded and normalised.**  The band analogue of
`RMF.mesoRange_le_of_range`: if the positive half of the weighted range is at most `(log z)^q·R`,
then the whole range `e^{-J} < |t| ≤ e^{J_b-J}`, in Proposition B's normalisation, is at most
`2R`.  The integrand is Proposition B's, `‖F_{y,z}(½-c+it)/(c+it)‖²`, written as in
`RMF.integral_rpow_centralWindow_primesIco_le`. -/
lemma mesoRange_band_le_of_range {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {c q R : ℝ} {y z J Jb : ℕ} (hz3 : (3 : ℝ) ≤ (z : ℝ))
    (hc : 0 < c) (hc12 : c ≤ 1 / 12) (hq1 : q ≤ 1) (hR : 0 ≤ R)
    (hrange : (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) (Real.exp ((Jb : ℝ) - J)),
        (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (z + 1) (shiftLine (-c) t) ω‖ ^ 2) ^ q ∂ν) ≤ (Real.log z) ^ q * R) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t|
          ∧ |t| ≤ Real.exp ((Jb : ℝ) - J)},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ 2 * R := by
  haveI := hY.isProbabilityMeasure
  have hlogz : (1 : ℝ) < Real.log z := one_lt_log_of_three_le hz3
  -- the integrand, decoupled
  have hint : ∀ (ω : Ω) (t : ℝ),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (c ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (z + 1) (shiftLine (-c) t) ω‖ ^ 2 := by
    intro ω t
    have hs : (1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I = shiftLine (-c) t := by
      rw [shiftLine]
      push_cast
      ring
    rw [norm_div_ofReal_add_mul_I_sq, hs]
  simp only [hint]
  -- the reflection
  have hfold := ae_setIntegral_weight_normSq_symm_primesIco hY (y + 1) (z + 1) (σ := -c)
    (by linarith) (ρ := fun t => (c ^ 2 + t ^ 2)⁻¹) (Bρ := (c ^ 2)⁻¹)
    (fun t => by norm_num)
    (by fun_prop) (fun t => by positivity)
    (fun t => by
      have h1 : (0 : ℝ) < c ^ 2 := by positivity
      have h2 : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
      exact (inv_le_inv₀ h2 h1).2 (by nlinarith [sq_nonneg t]))
    (A := Real.exp (-(J : ℝ))) (B := Real.exp ((Jb : ℝ) - J)) (Real.exp_pos _).le
    (Real.exp_le_exp.2 (by have := (Nat.cast_nonneg Jb : (0 : ℝ) ≤ Jb); linarith))
  have hcongr : (∫ ω, ((Real.log z)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t|
        ∧ |t| ≤ Real.exp ((Jb : ℝ) - J)},
        (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (z + 1) (shiftLine (-c) t) ω‖ ^ 2) ^ q ∂ν)
      = ∫ ω, ((Real.log z)⁻¹ * (2 * ∫ t in Set.Ioc (Real.exp (-(J : ℝ)))
          (Real.exp ((Jb : ℝ) - J)),
          (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (z + 1)
            (shiftLine (-c) t) ω‖ ^ 2)) ^ q ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hfold] with ω hω
    rw [hω]
  rw [hcongr]
  -- split off the constant
  have hInn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) (Real.exp ((Jb : ℝ) - J)),
      (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
        (y + 1) (z + 1) (shiftLine (-c) t) ω‖ ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
  have hsplit : ∀ ω : Ω, ((Real.log z)⁻¹ * (2 * ∫ t in Set.Ioc (Real.exp (-(J : ℝ)))
        (Real.exp ((Jb : ℝ) - J)),
        (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (z + 1) (shiftLine (-c) t) ω‖ ^ 2)) ^ q
      = ((Real.log z)⁻¹ * 2) ^ q * (∫ t in Set.Ioc (Real.exp (-(J : ℝ)))
        (Real.exp ((Jb : ℝ) - J)),
        (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (z + 1) (shiftLine (-c) t) ω‖ ^ 2) ^ q := by
    intro ω
    rw [← Real.mul_rpow (by positivity) (hInn ω), mul_assoc]
  simp only [hsplit]
  rw [integral_const_mul]
  have hCq : (0 : ℝ) ≤ ((Real.log z)⁻¹ * 2) ^ q := Real.rpow_nonneg (by positivity) _
  refine le_trans (mul_le_mul_of_nonneg_left hrange hCq) ?_
  -- `((log z)⁻¹·2)^q·(log z)^q = 2^q ≤ 2`
  have hcancel : ((Real.log z)⁻¹ * 2) ^ q * (Real.log z) ^ q = (2 : ℝ) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by linarith)]
    congr 1
    field_simp
  have h2q : (2 : ℝ) ^ q ≤ 2 := by
    calc (2 : ℝ) ^ q ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
      _ = 2 := Real.rpow_one _
  calc ((Real.log z)⁻¹ * 2) ^ q * ((Real.log z) ^ q * R)
      = ((Real.log z)⁻¹ * 2) ^ q * (Real.log z) ^ q * R := by ring
    _ = (2 : ℝ) ^ q * R := by rw [hcancel]
    _ ≤ 2 * R := mul_le_mul_of_nonneg_right h2q hR

/-- **The mesoscopic range of Proposition B, for a band.**  For `½ < q ≤ 1`, a band `(y, z]` with
`y ≥ 3`, `0 < c ≤ 1/12` with `2c·log z ≤ 1`, and a family of `J` blocks with
`J ≤ log(log z - log 2) + 1` and `1 ≤ J_b`, `J_b + log log(y+1) ≤ J ≤ J_b + log log y + 2`,

`E[((log z)⁻¹∫_{e^{-J} < |t| ≤ e^{J_b-J}}‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q]
  ≤ A·e^{J_b γ}·m·(1+(1-q)√m)^{-q}`,  `γ = q(2q-1)`, `m = min{J_b, ⌈γ^{-1}⌉}`.

`RMF.exists_const_integral_rpow_setIntegral_weight_band_le_rademacher` at `σ = -c`, folded and
normalised by `RMF.mesoRange_band_le_of_range`. -/
theorem exists_const_integral_rpow_mesoRange_band_le_rademacher :
    ∃ (z₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (c q : ℝ) (y z J Jb : ℕ),
          z₀ ≤ (z : ℝ) → 3 ≤ y → 0 < c → c ≤ 1 / 12 → 2 * c * Real.log z ≤ 1 →
          1 / 2 < q → q ≤ 1 → 1 ≤ Jb →
          (J : ℝ) ≤ Real.log (Real.log z - Real.log 2) + 1 →
          (Jb : ℝ) + Real.log (Real.log ((y : ℝ) + 1)) ≤ J →
          (J : ℝ) ≤ Jb + Real.log (Real.log y) + 2 →
            (∫ ω, ((Real.log z)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t|
                  ∧ |t| ≤ Real.exp ((Jb : ℝ) - J)},
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A * (Real.exp ((Jb : ℝ) * (q * (2 * q - 1)))
                  * ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ)
                  * (1 + (1 - q) * Real.sqrt ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ))
                      ^ (-q)) := by
  obtain ⟨zb, A, hA, HR⟩ := exists_const_integral_rpow_setIntegral_weight_band_le_rademacher
    (Ω := Ω)
  refine ⟨max zb 3, 6 * A, mul_pos (by norm_num) hA, ?_⟩
  intro Y ν hY c q y z J Jb hz hy3 hc hc12 hcz hq2 hq1 hJb1 hJle hJ1 hJ2
  have hzb : zb ≤ (z : ℝ) := le_trans (le_max_left _ _) hz
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := le_trans (le_max_right _ _) hz
  have hσz : 2 * |(-c)| * Real.log z ≤ 1 := by rw [abs_neg, abs_of_pos hc]; exact hcz
  have hS0 : (0 : ℝ) ≤ 3 * Real.exp ((Jb : ℝ) * (q * (2 * q - 1)))
      * ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ)
      * (1 + (1 - q) * Real.sqrt ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ)) ^ (-q) :=
    mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (target_base_pos hq1).le _)
  have hrange := HR Y ν hY (-c) c q y z J Jb hzb hy3 (by linarith) hσz hc hq2 hq1 hJb1 hJle
    hJ1 hJ2
  have h := mesoRange_band_le_of_range hY hz3 hc hc12 hq1 (mul_nonneg hA.le hS0)
    (le_of_le_of_eq hrange (by ring))
  refine le_trans h (le_of_eq ?_)
  ring

end RMF
