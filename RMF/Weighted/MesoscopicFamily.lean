/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.MesoscopicSum

/-!
# The `e`-adic block family

`RMF.integral_rpow_setIntegral_weight_le_of_blocks` sums the windows `(T_j/e, T_j]`,
`T_j = e^{j-J}`, given a bound on each.  Producing that bound means choosing, for each `j`, a
split point `w_j` and a barrier offset `D_j`, and checking the block bound's hypotheses.  This
file makes that choice and does the arithmetic, then sums the block bounds into the bound for the
mesoscopic range of `Z` (`RMF.exists_const_integral_rpow_mesoRange_le_rademacher`); it also bounds
the central window (`RMF.exists_const_integral_rpow_centralRange_le_rademacher`).

## The split point

The block bound wants `1 ≤ T_j·log(w_j+1) ≤ 2`, i.e. `log(w_j+1) ≍ 1/T_j`.  So with
`v_j := 1/T_j = e^{J-j}`,

`w_j + 1 := ⌈exp v_j⌉`,

which gives `v_j ≤ log(w_j+1) ≤ v_j + log 2` — the upper bound because `e^v + 1 ≤ 2e^v` once
`v ≥ 0`, and `T_j·log 2 ≤ 1` closes it.

## Why the range starts at `2/log x`, not `1/log x`

The bottom window has `T_1 ≈ 1/\log x`, so its split point is `exp(1/T_1) ≈ x` — **the whole
product**.  There is no room for `w_1 + 1 ≤ x`, and that is not an artefact: at heights
`|t| ≍ 1/\log x` the correlation length is the entire range of primes and the split is
degenerate.

The central window absorbs it.  `RMF.integral_rpow_setIntegral_normSq_div_shiftLine_le` covers
`|t| ≤ w` for any `w·log x ≤ 2`, so moving the boundary from `1/\log x` to `2/\log x` costs
nothing there and buys `v_1 ≤ (log x)/2`, hence `w_1 + 1 ≤ √x + 1`.  With `J := ⌈log(L/2)⌉` the
whole family then sits below the cutoff with a square root to spare.
-/

open MeasureTheory

namespace RMF

/-! ### The window scale -/

/-- The `e`-adic window scale at depth `j` in a range of `J` blocks: `T_j = e^{j-J}`, so that
`T_J = 1` and the family covers `(e^{-J}, 1]`. -/
noncomputable def mesoT (J j : ℕ) : ℝ := Real.exp ((j : ℝ) - J)

/-- The reciprocal scale `v_j = 1/T_j = e^{J-j}`, which is what the split point is built from. -/
noncomputable def mesoV (J j : ℕ) : ℝ := Real.exp ((J : ℝ) - j)

lemma mesoT_pos (J j : ℕ) : 0 < mesoT J j := Real.exp_pos _

lemma mesoV_pos (J j : ℕ) : 0 < mesoV J j := Real.exp_pos _

lemma mesoT_le_one {J j : ℕ} (hj : j ≤ J) : mesoT J j ≤ 1 := by
  have : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
  exact Real.exp_le_one_iff.2 (by linarith)

lemma one_le_mesoV {J j : ℕ} (hj : j ≤ J) : 1 ≤ mesoV J j := by
  have : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
  exact Real.one_le_exp (by linarith)

lemma mesoT_mul_mesoV (J j : ℕ) : mesoT J j * mesoV J j = 1 := by
  rw [mesoT, mesoV, ← Real.exp_add]
  norm_num

/-! ### The split point -/

/-- The split point of the `j`-th block: `w_j + 1 = ⌈exp(1/T_j)⌉`. -/
noncomputable def mesoW (J j : ℕ) : ℕ := ⌈Real.exp (mesoV J j)⌉₊ - 1

/-- `w_j + 1` is the ceiling itself — the subtraction never underflows. -/
lemma mesoW_add_one (J j : ℕ) : mesoW J j + 1 = ⌈Real.exp (mesoV J j)⌉₊ := by
  have h1 : 1 ≤ ⌈Real.exp (mesoV J j)⌉₊ := Nat.ceil_pos.2 (Real.exp_pos _)
  rw [mesoW]
  omega

/-- `exp v_j ≤ w_j + 1 < exp v_j + 1`. -/
lemma mesoW_bounds (J j : ℕ) :
    Real.exp (mesoV J j) ≤ ((mesoW J j : ℝ) + 1)
      ∧ ((mesoW J j : ℝ) + 1) < Real.exp (mesoV J j) + 1 := by
  have hcast : ((mesoW J j : ℝ) + 1) = ((⌈Real.exp (mesoV J j)⌉₊ : ℕ) : ℝ) := by
    rw [show ((mesoW J j : ℝ) + 1) = ((mesoW J j + 1 : ℕ) : ℝ) by push_cast; ring,
      mesoW_add_one]
  rw [hcast]
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (Real.exp_pos _).le⟩

/-- **The split point is at least `2`**, so the block bound's `2 ≤ w` holds.  `v_j ≥ 1` gives
`exp v_j ≥ e > 2`, and the ceiling of that is at least `3`. -/
lemma two_le_mesoW {J j : ℕ} (hj : j ≤ J) : 2 ≤ mesoW J j := by
  have hv := one_le_mesoV hj
  have h1 : Real.exp 1 ≤ Real.exp (mesoV J j) := Real.exp_le_exp.2 hv
  have he : (2 : ℝ) < Real.exp (mesoV J j) := by
    linarith [Real.exp_one_gt_d9, h1]
  have hb := (mesoW_bounds J j).1
  have h2 : (2 : ℝ) < (mesoW J j : ℝ) + 1 := by linarith
  have hnat : ((mesoW J j : ℝ) + 1) = ((mesoW J j + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hnat] at h2
  have h3 : (2 : ℕ) < mesoW J j + 1 := by exact_mod_cast h2
  omega

/-- **`log(w_j+1)` is `1/T_j` up to `log 2`.** -/
lemma log_mesoW_add_one_bounds {J j : ℕ} (hj : j ≤ J) :
    mesoV J j ≤ Real.log ((mesoW J j : ℝ) + 1)
      ∧ Real.log ((mesoW J j : ℝ) + 1) ≤ mesoV J j + Real.log 2 := by
  have hv := one_le_mesoV hj
  have hb := mesoW_bounds J j
  have hexp0 : (0 : ℝ) < Real.exp (mesoV J j) := Real.exp_pos _
  have h1 : (1 : ℝ) ≤ Real.exp (mesoV J j) := Real.one_le_exp (by linarith)
  have hpos : (0 : ℝ) < (mesoW J j : ℝ) + 1 := by linarith [hb.1]
  constructor
  · have h := Real.log_le_log hexp0 hb.1
    rwa [Real.log_exp] at h
  · have hle : ((mesoW J j : ℝ) + 1) ≤ 2 * Real.exp (mesoV J j) := by linarith [hb.2]
    have h := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hexp0.ne', Real.log_exp] at h
    linarith

/-- **The block bound's window hypotheses**: `1 ≤ T_j·log(w_j+1) ≤ 2`. -/
lemma mesoT_mul_log_mesoW_bounds {J j : ℕ} (hj : j ≤ J) :
    1 ≤ mesoT J j * Real.log ((mesoW J j : ℝ) + 1)
      ∧ mesoT J j * Real.log ((mesoW J j : ℝ) + 1) ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := log_mesoW_add_one_bounds hj
  have hT0 := mesoT_pos J j
  have hT1 := mesoT_le_one hj
  have hid := mesoT_mul_mesoV J j
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog20 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hT0.le]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hT0.le]

/-- **`log w_j ≥ v_j/3`**, which is the lower bound the factor `(log w_j)^{q(2q-1)}` needs.

`e^v - 1 ≥ e^{v/3}` for `v ≥ 1`: with `s = e^{v/3} ≥ 4/3` it is `s³ - s ≥ 1`, and
`(4/3)³ - 4/3 = 28/27 > 1` exactly. -/
lemma mesoV_div_three_le_log_mesoW {J j : ℕ} (hj : j ≤ J) :
    mesoV J j / 3 ≤ Real.log (mesoW J j : ℝ) := by
  have hv := one_le_mesoV hj
  have hb := mesoW_bounds J j
  set v : ℝ := mesoV J j with hvdef
  set s : ℝ := Real.exp (v / 3) with hs
  have hs0 : (0 : ℝ) < s := Real.exp_pos _
  have hs43 : (4 : ℝ) / 3 ≤ s := by
    have h1 : Real.exp (1 / 3 : ℝ) ≤ s := Real.exp_le_exp.2 (by linarith)
    linarith [Real.add_one_le_exp (1 / 3 : ℝ), h1]
  have hcube : s ^ 3 = Real.exp v := by
    have h3 : s ^ 3 = s * s * s := by ring
    rw [h3, hs, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hkey : s ≤ Real.exp v - 1 := by
    rw [← hcube]
    have hsq : (16 : ℝ) / 9 ≤ s ^ 2 := by nlinarith [hs43]
    have hprod : (0 : ℝ) ≤ (s - 4 / 3) * (s ^ 2 - 16 / 9) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hs43, hsq, hprod]
  have hw : Real.exp v - 1 ≤ (mesoW J j : ℝ) := by linarith [hb.1]
  have hle : s ≤ (mesoW J j : ℝ) := le_trans hkey hw
  have h := Real.log_le_log hs0 hle
  rwa [hs, Real.log_exp] at h

/-! ### The split's gain, as geometric decay in the depth

`(log w_j)^{q(2q-1)}` is what the split buys, and `log w_j ≍ v_j = e^{J-j}`, so it is
`≍ e^{-(J-j)α}` with `α = q(1-2q) ≥ 0` — decaying towards the *bottom* of the range.  That decay
is what makes the sum over blocks converge; the barrier only supplies the `(1+(1-q)√j)^{-q}` on
top of it. -/

/-- **The split's gain at the `j`-th block**, `(log w_j)^{q(2q-1)} ≤ 3·e^{(j-J)q(1-2q)}`.

The exponent is `≤ 0`, so the lower bound `log w_j ≥ v_j/3` becomes an upper bound on the power;
the `3` is `3^{q(1-2q)} ≤ 3^{1/8}`, charged crudely.

`RMF.exp_rpow` (`Analysis/PartialSumBounds.lean`) is `(e^a)^b = e^{ab}`. -/
lemma log_mesoW_rpow_le {J j : ℕ} (hj : j ≤ J) {q : ℝ} (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2) :
    (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
      ≤ 3 * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) := by
  have hα0 : (0 : ℝ) ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have hα1 : q * (1 - 2 * q) ≤ 1 := by nlinarith
  have hv0 : (0 : ℝ) < mesoV J j / 3 := div_pos (mesoV_pos J j) (by norm_num)
  have hlw := mesoV_div_three_le_log_mesoW hj
  have hmono : (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
      ≤ (mesoV J j / 3) ^ (q * (2 * q - 1)) :=
    Real.rpow_le_rpow_of_nonpos hv0 hlw (by nlinarith)
  have hc : q * (2 * q - 1) = -(q * (1 - 2 * q)) := by ring
  have h3 : (3 : ℝ) ^ (q * (2 * q - 1)) = ((3 : ℝ) ^ (q * (1 - 2 * q)))⁻¹ := by
    rw [hc, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hvp : (mesoV J j) ^ (q * (2 * q - 1))
      = Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) := by
    rw [mesoV, exp_rpow]
    congr 1
    ring
  have hexpand : (mesoV J j / 3) ^ (q * (2 * q - 1))
      = Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * (3 : ℝ) ^ (q * (1 - 2 * q)) := by
    rw [Real.div_rpow (mesoV_pos J j).le (by norm_num), h3, hvp, div_eq_mul_inv, inv_inv]
  have h3le : (3 : ℝ) ^ (q * (1 - 2 * q)) ≤ 3 := by
    calc (3 : ℝ) ^ (q * (1 - 2 * q)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 3 := Real.rpow_one 3
  have hexp0 : (0 : ℝ) < Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) := Real.exp_pos _
  calc (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
      ≤ (mesoV J j / 3) ^ (q * (2 * q - 1)) := hmono
    _ = Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * (3 : ℝ) ^ (q * (1 - 2 * q)) := hexpand
    _ ≤ Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * 3 :=
        mul_le_mul_of_nonneg_left h3le hexp0.le
    _ = 3 * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) := by ring

/-- **The split's gain at the `j`-th block, above the critical exponent.**
`(log w_j)^{q(2q-1)} ≤ e^{(J-j)q(2q-1)}` for `q ≥ ½`: the exponent is `≥ 0`, so the upper bound
`log w_j ≤ v_j` of `RMF.mesoW_bounds` is read, and the factor grows towards the shallow end,
`e^{(J-1)q(2q-1)} ≈ (log x)^{q(2q-1)}` at `j = 1`.  No constant is paid, since `w_j < e^{v_j}`
exactly.  The twin of `RMF.log_mesoW_rpow_le`. -/
lemma log_mesoW_rpow_le_above {J j : ℕ} (hj : j ≤ J) {q : ℝ} (hq2 : 1 / 2 ≤ q) :
    (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
      ≤ Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) := by
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hw2 : (2 : ℝ) ≤ (mesoW J j : ℝ) := by exact_mod_cast two_le_mesoW hj
  have hlog0 : (0 : ℝ) ≤ Real.log (mesoW J j : ℝ) := Real.log_nonneg (by linarith)
  have hupper : Real.log (mesoW J j : ℝ) ≤ mesoV J j := by
    have hb := (mesoW_bounds J j).2
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (mesoW J j : ℝ))
      (by linarith : (mesoW J j : ℝ) ≤ Real.exp (mesoV J j))
    rwa [Real.log_exp] at h
  calc (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
      ≤ (mesoV J j) ^ (q * (2 * q - 1)) := Real.rpow_le_rpow hlog0 hupper hγ0
    _ = Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) := by rw [mesoV, exp_rpow]

/-- **The weight cancels the block's `T²`**, exactly: `e^{2(J+1-j)}·T_j² = e²`. -/
lemma mesoWeight_mul_mesoT_sq (J j : ℕ) :
    Real.exp (2 * ((J : ℝ) + 1 - j)) * (mesoT J j) ^ 2 = Real.exp 2 := by
  rw [mesoT, show (Real.exp ((j : ℝ) - J)) ^ 2 = Real.exp (2 * ((j : ℝ) - J)) from by
    rw [show (Real.exp ((j : ℝ) - J)) ^ 2
        = Real.exp ((j : ℝ) - J) * Real.exp ((j : ℝ) - J) from by ring, ← Real.exp_add]
    congr 1
    ring, ← Real.exp_add]
  congr 1
  ring

/-! ### The weight against the block bound

Both block bounds have the shape `C·((log w_j)^{q(2q-1)}·(T_j²·Λ)^q)·F`, and the window
summation wants them multiplied by the weight `e^{2(J+1-j)}` raised to `q`.  The `T_j²` cancels
exactly, the `(log w_j)^{q(2q-1)}` becomes the geometric factor, and the rest is `Λ^q` times
a constant — with **no `T` anywhere**.  That is the whole reason the sum over blocks is a sum of
`e^{(j-J)α}·F`. -/

/-- **The weight cancellation.**  From a block bound
`E ≤ C·((log w_j)^{q(2q-1)}·(T_j²·Λ)^q)·F` to
`e^{2(J+1-j)q}·E ≤ 3e²·C·Λ^q·e^{(j-J)q(1-2q)}·F`. -/
lemma mesoWeight_mul_block_le {J j : ℕ} (hjJ : j ≤ J) {q C F Λ E : ℝ}
    (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2) (hC : 0 ≤ C) (hF : 0 ≤ F) (hΛ : 0 ≤ Λ)
    (hE : E ≤ C * ((Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
        * ((mesoT J j) ^ 2 * Λ) ^ q) * F) :
    (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * E
      ≤ 3 * Real.exp 2 * C * Λ ^ q * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * F := by
  have hw0 : (0 : ℝ) ≤ (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  have hTΛ : (0 : ℝ) ≤ (mesoT J j) ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ
  have hΛq : (0 : ℝ) ≤ Λ ^ q := Real.rpow_nonneg hΛ _
  have hLw0 : (0 : ℝ) ≤ (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1)) :=
    Real.rpow_nonneg (Real.log_nonneg (by
      have := two_le_mesoW hjJ
      have : (2 : ℝ) ≤ (mesoW J j : ℝ) := by exact_mod_cast this
      linarith)) _
  have hexp0 : (0 : ℝ) < Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) := Real.exp_pos _
  -- the weight times the block's `T²`
  have hprod : (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * ((mesoT J j) ^ 2 * Λ) ^ q
      = (Real.exp 2 * Λ) ^ q := by
    rw [← Real.mul_rpow (Real.exp_pos _).le hTΛ, ← mul_assoc, mesoWeight_mul_mesoT_sq]
  -- and `(e²Λ)^q ≤ e²Λ^q`
  have hsplit : (Real.exp 2 * Λ) ^ q = (Real.exp 2) ^ q * Λ ^ q :=
    Real.mul_rpow (Real.exp_pos 2).le hΛ
  have hexpq : (Real.exp 2) ^ q ≤ Real.exp 2 := by
    calc (Real.exp 2) ^ q ≤ (Real.exp 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by linarith)
      _ = Real.exp 2 := Real.rpow_one _
  have hlogw := log_mesoW_rpow_le hjJ hq0 hq2
  calc (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * E
      ≤ (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (C * ((Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
            * ((mesoT J j) ^ 2 * Λ) ^ q) * F) := mul_le_mul_of_nonneg_left hE hw0
    _ = C * (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
          * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * ((mesoT J j) ^ 2 * Λ) ^ q) * F := by ring
    _ = C * (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1)) * ((Real.exp 2) ^ q * Λ ^ q) * F := by
        rw [hprod, hsplit]
    _ ≤ C * (3 * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q)))) * ((Real.exp 2) ^ q * Λ ^ q)
          * F := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogw hC) (by positivity)) hF
    _ ≤ C * (3 * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q)))) * (Real.exp 2 * Λ ^ q) * F := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hF
        exact mul_le_mul_of_nonneg_right hexpq hΛq
    _ = 3 * Real.exp 2 * C * Λ ^ q * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * F := by ring

/-- **The weight cancellation, above the critical exponent.**  From a block bound
`E ≤ C·((log w_j)^{q(2q-1)}·(T_j²·Λ)^q)·F` to `e^{2(J+1-j)q}·E ≤ e²·C·Λ^q·e^{(J-j)q(2q-1)}·F`,
for `½ ≤ q ≤ 1`: `RMF.mesoWeight_mul_block_le` with `RMF.log_mesoW_rpow_le_above` in place of
`RMF.log_mesoW_rpow_le`.  The sign of the exponent decides which end of the range carries the
sum (`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above_min`). -/
lemma mesoWeight_mul_block_le_above {J j : ℕ} (hjJ : j ≤ J) {q C F Λ E : ℝ}
    (hq2 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (hF : 0 ≤ F) (hΛ : 0 ≤ Λ)
    (hE : E ≤ C * ((Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
        * ((mesoT J j) ^ 2 * Λ) ^ q) * F) :
    (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * E
      ≤ Real.exp 2 * C * Λ ^ q * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) * F := by
  have hw0 : (0 : ℝ) ≤ (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  have hTΛ : (0 : ℝ) ≤ (mesoT J j) ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ
  have hΛq : (0 : ℝ) ≤ Λ ^ q := Real.rpow_nonneg hΛ _
  have he2q : (0 : ℝ) ≤ (Real.exp 2) ^ q := Real.rpow_nonneg (Real.exp_pos 2).le _
  have hprod : (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * ((mesoT J j) ^ 2 * Λ) ^ q
      = (Real.exp 2 * Λ) ^ q := by
    rw [← Real.mul_rpow (Real.exp_pos _).le hTΛ, ← mul_assoc, mesoWeight_mul_mesoT_sq]
  have hsplit : (Real.exp 2 * Λ) ^ q = (Real.exp 2) ^ q * Λ ^ q :=
    Real.mul_rpow (Real.exp_pos 2).le hΛ
  have hexpq : (Real.exp 2) ^ q ≤ Real.exp 2 := by
    calc (Real.exp 2) ^ q ≤ (Real.exp 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by linarith)
      _ = Real.exp 2 := Real.rpow_one _
  have hlogw := log_mesoW_rpow_le_above hjJ hq2
  calc (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * E
      ≤ (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (C * ((Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
            * ((mesoT J j) ^ 2 * Λ) ^ q) * F) := mul_le_mul_of_nonneg_left hE hw0
    _ = C * (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1))
          * ((Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q * ((mesoT J j) ^ 2 * Λ) ^ q) * F := by ring
    _ = C * (Real.log (mesoW J j : ℝ)) ^ (q * (2 * q - 1)) * ((Real.exp 2) ^ q * Λ ^ q) * F := by
        rw [hprod, hsplit]
    _ ≤ C * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) * ((Real.exp 2) ^ q * Λ ^ q) * F := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogw hC) (mul_nonneg he2q hΛq)) hF
    _ ≤ C * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) * (Real.exp 2 * Λ ^ q) * F := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
          (mul_nonneg hC (Real.exp_pos _).le)) hF
        exact mul_le_mul_of_nonneg_right hexpq hΛq
    _ = Real.exp 2 * C * Λ ^ q * Real.exp (((J : ℝ) - j) * (q * (2 * q - 1))) * F := by ring

/-! ### The split point sits below the cutoff

`w_j + 1 < e^{v_j} + 1` and `v_j ≤ (log x)/2`, so `w_j + 1 < √x + 1 ≤ x`.  This is why the range
starts at `2/log x`: there the bottom window has `v_1 ≤ (log x)/2`, while at `1/log x` it would
have `v_1 ≤ log x` and there would be no room. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `x ≥ 3 > e` gives `log x > 1`, which every scale comparison below opens with. -/
lemma one_lt_log_of_three_le {x : ℝ} (hx3 : 3 ≤ x) : (1 : ℝ) < Real.log x := by
  have h1 : Real.log (Real.exp 1) < Real.log x :=
    Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  rwa [Real.log_exp] at h1

/-- **`v_j ≤ B` as soon as `J ≤ log B + 1`.**  Nothing about the product length enters: the
scale `v_j = e^{J-j}` is largest at `j = 1`, where it is `e^{J-1}`. -/
lemma mesoV_le_of_le {J j : ℕ} {B : ℝ} (hj1 : 1 ≤ j) (hB : 0 < B)
    (hJle : (J : ℝ) ≤ Real.log B + 1) : mesoV J j ≤ B := by
  have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hstep : (J : ℝ) - j ≤ Real.log B := by linarith
  have hkey := Real.exp_le_exp.2 hstep
  change Real.exp ((J : ℝ) - j) ≤ B
  rwa [Real.exp_log hB] at hkey

/-- **The split point stays inside the product**: `w_j + 1 ≤ x`, from `v_j ≤ log x - log 2`, so
that `e^{v_j} ≤ x/2`.  Any `v_1 ≤ c·log x` with `c < 1` would do for this step; the bound
`log x - log 2` is what leaves room for an integer `J` with `e^{-J}·log(y+1) ≤ 2` and
`J ≤ log(log y - log 2) + 1` (`RMF.exists_mesoRange_index`). -/
lemma mesoW_add_one_le {J j : ℕ} {x : ℝ} (hj1 : 1 ≤ j) (hx3 : 3 ≤ x)
    (hJle : (J : ℝ) ≤ Real.log (Real.log x - Real.log 2) + 1) : ((mesoW J j : ℝ) + 1) ≤ x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (1 : ℝ) < Real.log x := one_lt_log_of_three_le hx3
  have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hB : (0 : ℝ) < Real.log x - Real.log 2 := by linarith
  have hv := mesoV_le_of_le hj1 hB hJle
  have hb := (mesoW_bounds J j).2
  have hexpv : Real.exp (mesoV J j) ≤ Real.exp (Real.log x - Real.log 2) := Real.exp_le_exp.2 hv
  have hhalf : Real.exp (Real.log x - Real.log 2) = x / 2 := by
    rw [Real.exp_sub, Real.exp_log hx0, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hhalf] at hexpv
  linarith

/-! ### One block, weighted, without the barrier

The trivial block bound — the split and the low part's moment bound, with the chaos factor from
Jensen and Mertens — multiplied by the weight.  Valid at **every** `j`, with no threshold on the
depth and no offset; what it lacks is the `(1+(1-q)√t)^{-q}` saving. -/

/-- **A weighted mesoscopic block, without the barrier saving.** -/
theorem mesoBlock_weighted_le_trivial {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {x σ q : ℝ} {J j : ℕ}
    (hx3 : 3 ≤ x) (hσ : 0 ≤ σ) (hσx : σ * Real.log x ≤ 1) (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2)
    (hj1 : 1 ≤ j) (hjJ : j ≤ J)
    (hJle : (J : ℝ) ≤ Real.log (Real.log x - Real.log 2) + 1) :
    (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
        * (∫ ω, (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ 3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21) * (Real.log x) ^ q
        * Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) * 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hcast : (((mesoW J j + 1 : ℕ)) : ℝ) = (mesoW J j : ℝ) + 1 := by push_cast; ring
  have hwx := mesoW_add_one_le hj1 hx3 hJle
  have hwfl : mesoW J j + 1 ≤ ⌊x⌋₊ + 1 := by
    have : mesoW J j + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by rw [hcast]; exact hwx)
    omega
  obtain ⟨hTlo, hThi⟩ := mesoT_mul_log_mesoW_bounds hjJ
  have hblk := integral_rpow_setIntegral_normSq_block_le_trivial hY (two_le_mesoW hjJ) hwfl
    hwx hσ hσx hq0 (by linarith) (mesoT_pos J j) (mesoT_le_one hjJ) hTlo hThi
  refine mesoWeight_mul_block_le hjJ hq0 hq2 (by positivity) (by norm_num) hlogx0 ?_
  rw [mul_one]
  exact hblk

/-! ### Moving the barrier saving from the depth to the block index

The block bound's saving is `(1+(1-q)√t)^{-q}` at the *depth* `t`, and the window summation
wants it at the *index* `j`.  On the deep blocks the two differ by a constant independent of `x`,
`j ≤ t + c`, and shifting the argument of `(1+(1-q)√·)^{-q}` by `c` costs a factor `1+√c`.

The shallow blocks `j ≤ c` have no saving at all, and the same factor covers `1` there.  So a
single constant `1+√c` converts both branches into the shape the window sum consumes. -/

/-- **Shifting the depth by `c` costs a factor `1+√c`.** -/
lemma target_shift_le {t j c : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hjt : (j : ℝ) ≤ (t : ℝ) + c) :
    (1 + (1 - q) * Real.sqrt t) ^ (-q)
      ≤ (1 + Real.sqrt c) * (1 + (1 - q) * Real.sqrt j) ^ (-q) := by
  have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hsc : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
  have hsj : (0 : ℝ) ≤ Real.sqrt j := Real.sqrt_nonneg _
  have hq' : (0 : ℝ) ≤ 1 - q := by linarith
  have hcpos : (0 : ℝ) < 1 + Real.sqrt c := by linarith
  -- `√j ≤ √t + √c`, because `j ≤ t + c ≤ (√t+√c)²`
  have hadd : Real.sqrt j ≤ Real.sqrt t + Real.sqrt c := by
    have h1 : Real.sqrt t ^ 2 = (t : ℝ) := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt c ^ 2 = (c : ℝ) := Real.sq_sqrt (by positivity)
    have hsq : ((j : ℝ)) ≤ (Real.sqrt t + Real.sqrt c) ^ 2 := by
      nlinarith [mul_nonneg hst hsc]
    have h3 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at h3
  have hBt0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt t := by nlinarith
  have hBj0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt j := by nlinarith
  -- the two bases are within the factor `1+√c`
  have hbase : 1 + (1 - q) * Real.sqrt j ≤ (1 + Real.sqrt c) * (1 + (1 - q) * Real.sqrt t) := by
    nlinarith [mul_nonneg hsc (mul_nonneg hq' hst)]
  -- raising to `-q` reverses it
  have hstep : ((1 + Real.sqrt c) * (1 + (1 - q) * Real.sqrt t)) ^ (-q)
      ≤ (1 + (1 - q) * Real.sqrt j) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hBj0 hbase (by linarith)
  rw [Real.mul_rpow hcpos.le hBt0.le] at hstep
  -- cancel `(1+√c)^{-q}` on the left, and pay `(1+√c)^q ≤ 1+√c` on the right
  have hid : (1 + Real.sqrt c) ^ q * (1 + Real.sqrt c) ^ (-q) = 1 := by
    rw [← Real.rpow_add hcpos]
    simp
  have hmul := mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hcpos.le q)
  have hlhs : (1 + Real.sqrt c) ^ q
      * ((1 + Real.sqrt c) ^ (-q) * (1 + (1 - q) * Real.sqrt t) ^ (-q))
      = (1 + (1 - q) * Real.sqrt t) ^ (-q) := by
    rw [← mul_assoc, hid, one_mul]
  rw [hlhs] at hmul
  refine hmul.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hBj0.le _))
  calc (1 + Real.sqrt c) ^ q ≤ (1 + Real.sqrt c) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hq1
    _ = 1 + Real.sqrt c := Real.rpow_one _

/-- **On the shallow blocks the factor `1+√c` covers the missing saving outright.** -/
lemma one_le_target_mul {j c : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hjc : j ≤ c) :
    (1 : ℝ) ≤ (1 + Real.sqrt c) * (1 + (1 - q) * Real.sqrt j) ^ (-q) := by
  have hsj : (0 : ℝ) ≤ Real.sqrt j := Real.sqrt_nonneg _
  have hq' : (0 : ℝ) ≤ 1 - q := by linarith
  have hBj0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt j := by nlinarith
  have hjc' : Real.sqrt j ≤ Real.sqrt c := Real.sqrt_le_sqrt (by exact_mod_cast hjc)
  have hpow : (1 + (1 - q) * Real.sqrt j) ^ q ≤ 1 + Real.sqrt c := by
    calc (1 + (1 - q) * Real.sqrt j) ^ q ≤ (1 + (1 - q) * Real.sqrt j) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) hq1
      _ = 1 + (1 - q) * Real.sqrt j := Real.rpow_one _
      _ ≤ 1 + Real.sqrt c := by nlinarith
  have hid : (1 + (1 - q) * Real.sqrt j) ^ q * (1 + (1 - q) * Real.sqrt j) ^ (-q) = 1 := by
    rw [← Real.rpow_add hBj0]
    simp
  have := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hBj0.le (-q))
  rwa [hid] at this

/-! ### The two branches, in one shape

Both block bounds end as `E ≤ M₀·Λ^q·G·F₀` — the sharp one with `F₀` the barrier saving at the
depth, the trivial one with `F₀ = 1`.  `RMF.meso_finish` converts either into the single shape
the window sum consumes, at the cost of the factor `1+√c` that `RMF.target_shift_le` and
`RMF.one_le_target_mul` both supply. -/

lemma target_base_pos {m : ℕ} {q : ℝ} (hq1 : q ≤ 1) : (0 : ℝ) < 1 + (1 - q) * Real.sqrt m := by
  have h := Real.sqrt_nonneg (m : ℝ)
  nlinarith

/-- **The common last step of both branches.** -/
lemma meso_finish {E M₀ M Λq G F₀ F S : ℝ} (hM₀ : 0 ≤ M₀) (hMM : M₀ ≤ M) (hΛq : 0 ≤ Λq)
    (hG : 0 ≤ G) (hF₀ : 0 ≤ F₀) (hSF : F₀ ≤ S * F) (hE : E ≤ M₀ * Λq * G * F₀) :
    E ≤ M * S * Λq * (G * F) := by
  have hM : (0 : ℝ) ≤ M := le_trans hM₀ hMM
  refine hE.trans ?_
  have h1 : M₀ * Λq * G * F₀ ≤ M * Λq * G * F₀ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMM hΛq) hG) hF₀
  refine h1.trans ?_
  have h2 : M * Λq * G * (S * F) = M * S * Λq * (G * F) := by ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_left hSF (mul_nonneg (mul_nonneg hM hΛq) hG)

/-! ### The offset covers the split point

The block bound asks `w_j + 1 ≤ blockScale θ 0 = exp(exp θ)`.  At an offset chosen by
`RMF.exists_harperOffset_at_split_scale` we have `K ≤ T_j·e^θ` with `K ≥ 4`, i.e.
`e^θ ≥ 4/T_j = 4v_j`; and `exp(4v) ≥ exp v + 1` whenever `v ≥ 1`. -/

lemma four_mul_mesoV_le_exp_of_le {J j : ℕ} {K θ : ℝ} (hK : 4 ≤ K)
    (hKl : K ≤ mesoT J j * Real.exp θ) : 4 * mesoV J j ≤ Real.exp θ := by
  have hv0 : (0 : ℝ) < mesoV J j := mesoV_pos J j
  have h1 : K * mesoV J j ≤ Real.exp θ := by
    calc K * mesoV J j ≤ mesoT J j * Real.exp θ * mesoV J j :=
          mul_le_mul_of_nonneg_right hKl hv0.le
      _ = mesoT J j * mesoV J j * Real.exp θ := by ring
      _ = Real.exp θ := by rw [mesoT_mul_mesoV, one_mul]
  exact le_trans (mul_le_mul_of_nonneg_right hK hv0.le) h1

lemma mesoW_add_one_le_blockScale {J j : ℕ} (hj : j ≤ J) {θ : ℝ}
    (hθ : 4 * mesoV J j ≤ Real.exp θ) : ((mesoW J j : ℝ) + 1) ≤ blockScale θ 0 := by
  have hv : 1 ≤ mesoV J j := one_le_mesoV hj
  have hev : (1 : ℝ) ≤ Real.exp (mesoV J j) := Real.one_le_exp (by linarith)
  have he3 : (4 : ℝ) ≤ Real.exp (3 * mesoV J j) := by
    have h1 : Real.exp 3 ≤ Real.exp (3 * mesoV J j) := Real.exp_le_exp.2 (by linarith)
    have h2 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    linarith
  have hsplit : Real.exp (4 * mesoV J j) = Real.exp (mesoV J j) * Real.exp (3 * mesoV J j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgrow : Real.exp (mesoV J j) + 1 ≤ Real.exp (4 * mesoV J j) := by
    rw [hsplit]
    nlinarith
  have hbs : blockScale θ 0 = Real.exp (Real.exp θ) := by
    simp only [blockScale, Nat.cast_zero, zero_add]
  have hmono : Real.exp (4 * mesoV J j) ≤ Real.exp (Real.exp θ) := Real.exp_le_exp.2 hθ
  have hub := (mesoW_bounds J j).2
  rw [hbs]
  linarith

/-! ### One block, weighted, in the shape the window sum consumes

The deep blocks `j ≥ c` get the sharp bound, with the barrier saving at the depth
`harperBlockCount D x - 3`; the shallow blocks `j < c` get the trivial one.  The threshold
`c = t₀ + ⌈log Klo⌉ + 10` is exactly what the deep branch's hypotheses need: `j ≥ c` forces both
`D ≤ log log x` and `t₀ + 3 ≤ harperBlockCount D x`, and it is also the shift
`j ≤ (harperBlockCount D x - 3) + c` that moves the saving from the depth to the index.

Nothing here grows with `x`.  `D` moves with the *window*, through
`(D:ℝ) ≤ 4 + log Klo + (J - j)` — this is what "`D` varies with the height" means — and `c`,
built from the constants `t₀` and `Klo` of the block bound, does not move at all. -/

/-- **The per-block bound, both branches**, in the shape that
`RMF.integral_rpow_setIntegral_weight_le_of_blocks` consumes. -/
theorem exists_const_mesoBlock_weighted_le_rademacher :
    ∃ (x₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ q : ℝ) (J j : ℕ),
          x₀ ≤ x → 0 ≤ σ → σ * Real.log x ≤ 1 → 0 ≤ q → q ≤ 1 / 2 →
          1 ≤ j → j ≤ J → (J : ℝ) ≤ Real.log (Real.log x - Real.log 2) + 1 →
            (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
                * (∫ ω, (∫ t in Set.Icc (mesoT J j / Real.exp 1) (mesoT J j),
                    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (Real.log x) ^ q
                * (Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q)))
                    * (1 + (1 - q) * Real.sqrt j) ^ (-q)) := by
  obtain ⟨D₀, t₀, xb, Klo, A, hD₀, hKlo, hKloD, hA, HB⟩ :=
    exists_const_integral_rpow_setIntegral_normSq_block_le_rademacher (Ω := Ω)
  have hCt0 : (0 : ℝ) < Real.exp 143800 * Real.exp 7 * Real.exp 21 := by positivity
  set c : ℕ := t₀ + ⌈Real.log Klo⌉₊ + 10 with hcdef
  refine ⟨max xb 3,
    3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21 + A) * (1 + Real.sqrt (c : ℝ)),
    mul_pos (mul_pos (by positivity) (by linarith)) (by positivity), ?_⟩
  intro Y ν hY x σ q J j hx hσ hσx hq0 hq2 hj1 hjJ hJle
  have hxb : xb ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hΛq : (0 : ℝ) ≤ (Real.log x) ^ q := Real.rpow_nonneg hlogx0 _
  have hG : (0 : ℝ) ≤ Real.exp (((j : ℝ) - J) * (q * (1 - 2 * q))) := (Real.exp_pos _).le
  have hMt0 : (0 : ℝ) ≤ 3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21) := by
    positivity
  have hMs0 : (0 : ℝ) ≤ 3 * Real.exp 2 * A := mul_nonneg (by positivity) hA.le
  have hMMt : 3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21)
      ≤ 3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21 + A) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hMMs : 3 * Real.exp 2 * A
      ≤ 3 * Real.exp 2 * (Real.exp 143800 * Real.exp 7 * Real.exp 21 + A) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rcases Nat.lt_or_ge j c with hshallow | hdeep
  · -- **shallow**: the trivial bound, with `1+√c` covering the missing saving
    exact meso_finish hMt0 hMMt hΛq hG zero_le_one
      (one_le_target_mul hq0 (by linarith) (le_of_lt hshallow))
      (mesoBlock_weighted_le_trivial hY hx3 hσ hσx hq0 hq2 hj1 hjJ hJle)
  · -- **deep**: the sharp bound, with the saving shifted from the depth to the index
    obtain ⟨D, hD4, hDle, hKl, hKb⟩ :=
      exists_harperOffset_at_split_scale x (mesoT_pos J j) (mesoT_le_one hjJ) hKlo
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
    have hlogx1 : (1 : ℝ) < Real.log x := one_lt_log_of_three_le hx3
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have hJll : (J : ℝ) ≤ Real.log (Real.log x) + 1 := by
      refine le_trans hJle ?_
      have h := Real.log_le_log (by linarith : (0 : ℝ) < Real.log x - Real.log 2)
        (by linarith : Real.log x - Real.log 2 ≤ Real.log x)
      linarith
    have hDlog : (D : ℝ) ≤ Real.log (Real.log x) := by linarith
    -- `D₀ ≤ D`, because `exp D₀ ≤ Klo ≤ T·e^θ ≤ e^θ` while `θ < D`
    have hexpθ : (0 : ℝ) < Real.exp (harperOffset D x) := Real.exp_pos _
    have hle1 : mesoT J j * Real.exp (harperOffset D x) ≤ Real.exp (harperOffset D x) := by
      have h := mul_le_mul_of_nonneg_right (mesoT_le_one hjJ) hexpθ.le
      rwa [one_mul] at h
    have hD₀θ : (D₀ : ℝ) ≤ harperOffset D x :=
      Real.exp_le_exp.1 (le_trans hKloD (le_trans hKl hle1))
    have hD₀D : D₀ ≤ D := by
      have h : (D₀ : ℝ) < (D : ℝ) := lt_of_le_of_lt hD₀θ (harperOffset_lt_natCast D x)
      have h' : D₀ < D := by exact_mod_cast h
      omega
    -- the split point sits below both `x` and the first block scale
    have hbs : ((mesoW J j : ℝ) + 1) ≤ blockScale (harperOffset D x) 0 :=
      mesoW_add_one_le_blockScale hjJ (four_mul_mesoV_le_exp_of_le hKlo hKl)
    have hwx := mesoW_add_one_le hj1 hx3 hJle
    have hcast : (((mesoW J j + 1 : ℕ)) : ℝ) = (mesoW J j : ℝ) + 1 := by push_cast; ring
    have hwfl : mesoW J j + 1 ≤ ⌊x⌋₊ + 1 := by
      have h : mesoW J j + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by rw [hcast]; exact hwx)
      omega
    -- the depth is at least `t₀ + 3`, and within `c` of the index
    have hn := harperBlockCount_add_one_add_offset hDlog
    have hθub : harperOffset D x < (D : ℝ) := harperOffset_lt_natCast D x
    have hnlb : (t₀ : ℝ) + 3 ≤ (harperBlockCount D x : ℝ) := by linarith
    have hn3 : t₀ + 3 ≤ harperBlockCount D x := by exact_mod_cast hnlb
    have ht₀ : t₀ ≤ harperBlockCount D x - 3 := by omega
    have hsub : ((harperBlockCount D x - 3 : ℕ) : ℝ) = (harperBlockCount D x : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : (3 : ℕ) ≤ harperBlockCount D x)]
      norm_num
    have hdepth : (j : ℝ) ≤ ((harperBlockCount D x - 3 : ℕ) : ℝ) + (c : ℝ) := by
      rw [hsub, hcR]
      linarith
    obtain ⟨hTlo, hThi⟩ := mesoT_mul_log_mesoW_bounds hjJ
    have hblk := HB Y ν hY x σ (mesoT J j) q (mesoW J j) D hxb hD₀D hDlog
      (two_le_mesoW hjJ) hwx hwfl hbs hσ hσx hq0 (by linarith) (mesoT_pos J j)
      (mesoT_le_one hjJ) hTlo hThi hKl hKb ht₀
    have hF₀ : (0 : ℝ)
        ≤ (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - 3 : ℕ) : ℝ)) ^ (-q) :=
      Real.rpow_nonneg (target_base_pos (by linarith)).le _
    refine meso_finish hMs0 hMMs hΛq hG hF₀ (target_shift_le hq0 (by linarith) hdepth) ?_
    exact mesoWeight_mul_block_le hjJ hq0 hq2 hA.le hF₀ hlogx0 hblk

/-! ### The whole `e`-adic range

`RMF.integral_rpow_setIntegral_weight_le_of_blocks` sums the `J` windows.  The subadditivity of
`u ↦ u^q` costs a factor `2J` — that is the `min{(1-2q)^{-1}, loglog x}` of the target, in the
second of its two forms — and the barrier saving at the *top* index survives as
`(1+(1-q)√J)^{-q}`. -/

/-- **The mesoscopic range `(e^{-J}, 1]`, with the weight.** -/
theorem exists_const_integral_rpow_setIntegral_weight_le_rademacher :
    ∃ (x₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ q : ℝ) (J : ℕ),
          x₀ ≤ x → 0 < σ → σ * Real.log x ≤ 1 → 0 < q → q ≤ 1 / 2 → 1 ≤ J →
          (J : ℝ) ≤ Real.log (Real.log x - Real.log 2) + 1 →
            (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
                (σ ^ 2 + t ^ 2)⁻¹
                  * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (Real.log x) ^ q * (2 * (J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q)) := by
  obtain ⟨xb, A, hA, HB⟩ := exists_const_mesoBlock_weighted_le_rademacher (Ω := Ω)
  refine ⟨max xb 3, A, hA, ?_⟩
  intro Y ν hY x σ q J hx hσ0 hσx hq0 hq2 hJ1 hJle
  have hxb : xb ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hK : (0 : ℝ) ≤ A * (Real.log x) ^ q := mul_nonneg hA.le (Real.rpow_nonneg hlogx0 _)
  have hα : (0 : ℝ) ≤ q * (1 - 2 * q) := mul_nonneg hq0.le (by linarith)
  refine integral_rpow_setIntegral_weight_le_of_blocks
    (α := q * (1 - 2 * q)) (β := 1 - q) (K := A * (Real.log x) ^ q)
    hY (⌊x⌋₊ + 1) hσ0 hq0 (by linarith) hα (by linarith) hK hJ1 ?_
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact HB Y ν hY x σ q J j hxb hσ0.le hσx hq0.le hq2 hj.1 hj.2 hJle

/-! ### `Z_m` at the reduction's own integrand

The `Z` of the reduction (`RMF.exists_integral_rpow_weightedRademacherSum_le_reduction_explicit`)
is `(log y)^{-1}∫_ℝ ‖F_{y+1}(½+σ+it)/(σ+it)‖²dt`, over the *whole* line and with the numerator's
abscissa and the denominator decoupled.  Its mesoscopic part is
`e^{-J} < |t| ≤ 1`, and three moves turn it into the range bound above:

* `‖z/(σ+it)‖² = (σ²+t²)^{-1}‖z‖²`, which is the decoupling made explicit;
* the reflection `t ↦ -t`, which the Rademacher field and the weight are both even under, folding
  `{e^{-J} < |t| ≤ 1}` onto `(e^{-J}, 1]` at a cost of `2^q ≤ 2`;
* the division by `log y`, which cancels the range bound's `(log y)^q` **exactly**.

That last cancellation is the point: the block bound's `Λ` is the log of the *product length*, and
the reduction divides by the log of the same length.  Instantiated at the reduction's own
`y = ⌊x^{1/(4 loglog x)}⌋` the two agree, leaving `J·(1+(1-q)√J)^{-q}`, `J ≍ log log x`. -/

/-- `‖z/(σ+it)‖² = (σ²+t²)^{-1}‖z‖²`. -/
lemma norm_div_ofReal_add_mul_I_sq (σ t : ℝ) (z : ℂ) :
    ‖z / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = (σ ^ 2 + t ^ 2)⁻¹ * ‖z‖ ^ 2 := by
  rw [norm_div, div_pow, normSq_ofReal_add_mul_I]
  ring

/-- **The mesoscopic range of `Z`.** -/
lemma mesoRange_le_of_range {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν)
    {σ q R : ℝ} {y J : ℕ} (hy3 : (3 : ℝ) ≤ (y : ℝ)) (hσ0 : 0 < σ) (hq1 : q ≤ 1)
    (hR : 0 ≤ R)
    (hrange : (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν) ≤ (Real.log y) ^ q * R) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ 2 * R := by
  haveI := hY.isProbabilityMeasure
  have hlogy : (1 : ℝ) < Real.log y := one_lt_log_of_three_le hy3
  -- the integrand, decoupled
  have hint : ∀ (ω : Ω) (t : ℝ),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2 := by
    intro ω t
    rw [norm_div_ofReal_add_mul_I_sq]
    congr 3
    rw [shiftLine]
    push_cast
    ring
  simp only [hint]
  -- the reflection
  have hfold := ae_setIntegral_weight_normSq_symm hY (y + 1) hσ0.le
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹) (Bρ := (σ ^ 2)⁻¹)
    (fun t => by norm_num)
    (by fun_prop) (fun t => by positivity)
    (fun t => by
      have h1 : (0 : ℝ) < σ ^ 2 := by positivity
      have h2 : (0 : ℝ) < σ ^ 2 + t ^ 2 := by positivity
      exact (inv_le_inv₀ h2 h1).2 (by nlinarith [sq_nonneg t]))
    (A := Real.exp (-(J : ℝ))) (B := 1) (Real.exp_pos _).le
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg J)))
  have hcongr : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1},
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      = ∫ ω, ((Real.log y)⁻¹ * (2 * ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
          (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (y + 1) (shiftLine σ t) ω‖ ^ 2)) ^ q ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hfold] with ω hω
    rw [hω]
  rw [hcongr]
  -- split off the constant
  have hInn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
        (y + 1) (shiftLine σ t) ω‖ ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
  have hsplit : ∀ ω : Ω, ((Real.log y)⁻¹ * (2 * ∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2)) ^ q
      = ((Real.log y)⁻¹ * 2) ^ q * (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q := by
    intro ω
    rw [← Real.mul_rpow (by positivity) (hInn ω), mul_assoc]
  simp only [hsplit]
  rw [integral_const_mul]
  have hCq : (0 : ℝ) ≤ ((Real.log y)⁻¹ * 2) ^ q := Real.rpow_nonneg (by positivity) _
  refine le_trans (mul_le_mul_of_nonneg_left hrange hCq) ?_
  -- `((log y)⁻¹·2)^q·(log y)^q = 2^q ≤ 2`
  have hcancel : ((Real.log y)⁻¹ * 2) ^ q * (Real.log y) ^ q = (2 : ℝ) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by linarith)]
    congr 1
    field_simp
  have h2q : (2 : ℝ) ^ q ≤ 2 := by
    calc (2 : ℝ) ^ q ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  calc ((Real.log y)⁻¹ * 2) ^ q * ((Real.log y) ^ q * R)
      = ((Real.log y)⁻¹ * 2) ^ q * (Real.log y) ^ q * R := by ring
    _ = (2 : ℝ) ^ q * R := by rw [hcancel]
    _ ≤ 2 * R := mul_le_mul_of_nonneg_right h2q hR

/-- **The mesoscopic range of `Z`, at the crude depth bound.** -/
theorem exists_const_integral_rpow_mesoRange_le_rademacher :
    ∃ (y₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y J : ℕ),
          y₀ ≤ (y : ℝ) → 0 < σ → σ * Real.log y ≤ 1 → 0 < q → q ≤ 1 / 2 → 1 ≤ J →
          (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1 →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1},
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A * ((J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q)) := by
  obtain ⟨xb, A, hA, HR⟩ := exists_const_integral_rpow_setIntegral_weight_le_rademacher (Ω := Ω)
  refine ⟨max xb 3, 4 * A, by positivity, ?_⟩
  intro Y ν hY σ q y J hy hσ0 hσy hq0 hq2 hJ1 hJle
  have hyb : xb ≤ (y : ℝ) := le_trans (le_max_left _ _) hy
  have hy3 : (3 : ℝ) ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  have hF : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt J) ^ (-q) :=
    Real.rpow_nonneg (target_base_pos (by linarith)).le _
  have hrange := HR Y ν hY (y : ℝ) σ q J hyb hσ0 hσy hq0 hq2 hJ1 hJle
  rw [hfloor] at hrange
  have hshape : (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
        (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (Real.log y) ^ q * (2 * A * ((J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q))) := by
    refine hrange.trans (le_of_eq (by ring))
  have h := mesoRange_le_of_range hY hy3 hσ0 (by linarith)
    (by positivity : (0 : ℝ) ≤ 2 * A * ((J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q))) hshape
  refine h.trans (le_of_eq (by ring))

/-! ### The mesoscopic range with the geometric factor kept

The same two theorems with `RMF.integral_rpow_setIntegral_weight_le_of_blocks_geom` in place of
`RMF.integral_rpow_setIntegral_weight_le_of_blocks`.  The window count `J` is replaced by
`6(1+α^{-1})` at `α = q(1-2q)`, which is what removes the leading `log log x` from the final
statement; the price is `q < ½` strictly, since `α = 0` there. -/

/-- **The mesoscopic range, with the geometric factor kept.** -/
theorem exists_const_integral_rpow_setIntegral_weight_le_rademacher_geom :
    ∃ (x₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ q : ℝ) (J : ℕ),
          x₀ ≤ x → 0 < σ → σ * Real.log x ≤ 1 → 0 < q → q < 1 / 2 → 1 ≤ J →
          (J : ℝ) ≤ Real.log (Real.log x - Real.log 2) + 1 →
            (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
                (σ ^ 2 + t ^ 2)⁻¹
                  * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (Real.log x) ^ q
                * (6 * (1 + (q * (1 - 2 * q))⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q)) := by
  obtain ⟨xb, A, hA, HB⟩ := exists_const_mesoBlock_weighted_le_rademacher (Ω := Ω)
  refine ⟨max xb 3, A, hA, ?_⟩
  intro Y ν hY x σ q J hx hσ0 hσx hq0 hq2 hJ1 hJle
  have hxb : xb ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hK : (0 : ℝ) ≤ A * (Real.log x) ^ q := mul_nonneg hA.le (Real.rpow_nonneg hlogx0 _)
  have hα : (0 : ℝ) < q * (1 - 2 * q) := mul_pos hq0 (by linarith)
  refine integral_rpow_setIntegral_weight_le_of_blocks_geom
    (α := q * (1 - 2 * q)) (β := 1 - q) (K := A * (Real.log x) ^ q)
    hY (⌊x⌋₊ + 1) hσ0 hq0 (by linarith) hα (by linarith) hK hJ1 ?_
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact HB Y ν hY x σ q J j hxb hσ0.le hσx hq0.le (by linarith) hj.1 hj.2 hJle

/-- **`Z_m` with the geometric factor kept.**  Taking the `min` with
`RMF.exists_const_integral_rpow_mesoRange_le_rademacher` gives the `min{(1-2q)^{-1}, log log x}`
of the final statement. -/
theorem exists_const_integral_rpow_mesoRange_le_rademacher_geom :
    ∃ (y₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y J : ℕ),
          y₀ ≤ (y : ℝ) → 0 < σ → σ * Real.log y ≤ 1 → 0 < q → q < 1 / 2 → 1 ≤ J →
          (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1 →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1},
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A * ((1 + (q * (1 - 2 * q))⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q)) := by
  obtain ⟨xb, A, hA, HR⟩ :=
    exists_const_integral_rpow_setIntegral_weight_le_rademacher_geom (Ω := Ω)
  refine ⟨max xb 3, 12 * A, by positivity, ?_⟩
  intro Y ν hY σ q y J hy hσ0 hσy hq0 hq2 hJ1 hJle
  have hyb : xb ≤ (y : ℝ) := le_trans (le_max_left _ _) hy
  have hy3 : (3 : ℝ) ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  have hα : (0 : ℝ) < q * (1 - 2 * q) := mul_pos hq0 (by linarith)
  have hF : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt J) ^ (-q) :=
    Real.rpow_nonneg (target_base_pos (by linarith)).le _
  have hrange := HR Y ν hY (y : ℝ) σ q J hyb hσ0 hσy hq0 hq2 hJ1 hJle
  rw [hfloor] at hrange
  have hR0 : (0 : ℝ) ≤ 6 * A * ((1 + (q * (1 - 2 * q))⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q)) :=
    by positivity
  have hshape : (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
        (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (Real.log y) ^ q
        * (6 * A * ((1 + (q * (1 - 2 * q))⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q))) :=
    hrange.trans (le_of_eq (by ring))
  have h := mesoRange_le_of_range hY hy3 hσ0 (by linarith) hR0 hshape
  refine h.trans (le_of_eq (by ring))

/-! ### `Z_c`: the central window at the reduction's own integrand

Below `|t| ≤ w` with `w·log(y+1) ≤ 2` the field is comparable to its value at the real point
(`RMF.integral_rpow_setIntegral_normSq_div_shiftLine_le`, the two-point ratio), and the weight
integrates to at most `∫_ℝ (σ²+t²)^{-1} = π/σ`.  The rest is the moment at the real point, which
the moment bound below the critical exponent controls:
`E‖F_{y+1}(½+σ)‖^{2q} ≤ e⁷(log y)^{q(2q-1)}`.

The window's *width* never enters — only `w·log(y+1) ≤ 2`, which is what lets the mesoscopic
range start wherever `RMF.exists_const_integral_rpow_mesoRange_le_rademacher` wants it to. -/

/-- **The central window of `Z`.** -/
theorem exists_const_integral_rpow_centralRange_le_rademacher :
    ∃ A : ℝ, 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q w : ℝ) (y : ℕ), 2 ≤ y → 0 < σ → σ * Real.log y ≤ 1 → 0 < w →
          w * Real.log ((y : ℝ) + 1) ≤ 2 → 0 ≤ q → q ≤ 1 →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w,
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A * ((σ * Real.log y)⁻¹) ^ q * (Real.log y) ^ (q * (2 * q - 1)) := by
  refine ⟨Real.pi * Real.exp 143800 * Real.exp 7, by positivity, ?_⟩
  intro Y ν hY σ q w y hy hσ0 hσy hw hwy hq0 hq2
  haveI := hY.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hcast : (((y + 1 : ℕ)) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
  -- the abscissa, as the two-point lemma writes it
  have habs : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) = shiftLine σ t := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  simp only [habs]
  -- the normalisation comes out of the `q`-th power
  have hInn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc (-w) w,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hsplit : ∀ ω : Ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
      = ((Real.log y)⁻¹) ^ q * (∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q := fun ω =>
    Real.mul_rpow (by positivity) (hInn ω)
  simp only [hsplit]
  rw [integral_const_mul]
  -- the two-point ratio, then the moment bound at the real point
  have hctr := integral_rpow_setIntegral_normSq_div_shiftLine_le hY (y := y + 1) (by omega)
    hσ0 hw (by rw [hcast]; exact hwy) hq0 (by linarith)
  have hlogyq : (0 : ℝ) ≤ (Real.log y) ^ (q * (2 * q - 1)) :=
    Real.rpow_nonneg hlogy.le _
  have hpf : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν)
      ≤ Real.exp 7 * (Real.log y) ^ (q * (2 * q - 1)) := by
    rcases le_total q (1 / 2) with h | h
    · exact hRa.integral_norm_randomEulerProduct_shift_rpow_le_log_of_le_half hσ0.le hq0 h hy hσy
    · refine le_trans
        (hRa.integral_norm_randomEulerProduct_shift_rpow_le_log hσ0.le h hq2 hy) ?_
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by norm_num)) hlogyq
  have hz : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by
    rw [shiftLine]
    norm_num
  rw [hz] at hctr
  have hR0 : (0 : ℝ) ≤ (Real.pi / σ * Real.exp 143800) ^ q :=
    Real.rpow_nonneg (by positivity) _
  have hNq : (0 : ℝ) ≤ ((Real.log y)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  have hstep := mul_le_mul_of_nonneg_left
    (hctr.trans (mul_le_mul_of_nonneg_left hpf hR0)) hNq
  refine hstep.trans ?_
  -- `(log y)^{-q}·(π e^143800/σ)^q = (π e^143800)^q·(σ log y)^{-q} ≤ π e^143800·(σ log y)^{-q}`
  have hfold : ((Real.log y)⁻¹) ^ q * (Real.pi / σ * Real.exp 143800) ^ q
      = (Real.pi * Real.exp 143800) ^ q * ((σ * Real.log y)⁻¹) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hbase : (1 : ℝ) ≤ Real.pi * Real.exp 143800 := by
    nlinarith [Real.pi_gt_three, Real.add_one_le_exp (143800 : ℝ)]
  have hcst : (Real.pi * Real.exp 143800) ^ q ≤ Real.pi * Real.exp 143800 := by
    calc (Real.pi * Real.exp 143800) ^ q ≤ (Real.pi * Real.exp 143800) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = Real.pi * Real.exp 143800 := Real.rpow_one _
  have hSq : (0 : ℝ) ≤ ((σ * Real.log y)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  have hLq : (0 : ℝ) ≤ (Real.log y) ^ (q * (2 * q - 1)) := Real.rpow_nonneg hlogy.le _
  calc ((Real.log y)⁻¹) ^ q
        * ((Real.pi / σ * Real.exp 143800) ^ q
          * (Real.exp 7 * (Real.log y) ^ (q * (2 * q - 1))))
      = (((Real.log y)⁻¹) ^ q * (Real.pi / σ * Real.exp 143800) ^ q)
        * (Real.exp 7 * (Real.log y) ^ (q * (2 * q - 1))) := by ring
    _ = (Real.pi * Real.exp 143800) ^ q * ((σ * Real.log y)⁻¹) ^ q
        * (Real.exp 7 * (Real.log y) ^ (q * (2 * q - 1))) := by rw [hfold]
    _ ≤ Real.pi * Real.exp 143800 * ((σ * Real.log y)⁻¹) ^ q
        * (Real.exp 7 * (Real.log y) ^ (q * (2 * q - 1))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcst hSq) ?_
        positivity
    _ = Real.pi * Real.exp 143800 * Real.exp 7 * ((σ * Real.log y)⁻¹) ^ q
        * (Real.log y) ^ (q * (2 * q - 1)) := by ring

end RMF
