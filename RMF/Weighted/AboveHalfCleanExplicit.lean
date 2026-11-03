/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfHierarchyExplicit
import RMF.Analysis.HierarchyScales

/-!
# The levels above `q = ½`, cleaned

Once `log y ≥ 1000` every Mertens, floor and sieve error in `RMF.bandLevel` and
`RMF.bottomLevel` is a fixed small constant, and the levels become closed forms in `q`,
`κ = log z/log y`, `V = log x/log z`, the truncation bound's constant `K_c` and error `E_c`
(`RMF.lemmaTConst_mul_exp_le`, `RMF.smallQReductionErr_le`).  At `θ = 1`, `c_s = 3/2` the `m`-th
window of a band sits at `v = e^m`, and its split point `⌊exp(1.5 log z/e^m)⌋` lies in `[y, z]`
while `e^m ≤ 1.5κ`: there the split window is `(1.5κ/e^m)^{q(2q-1)}·ω(q)`
(`RMF.winSplit_le_clean`), so the windows sum geometrically to
`1.5^a e^{-a}(log^a z - log^a y)/(1 - e^{-a})`, `a = q(2q-1)` (`RMF.pfFull_mul_bandWindows_le`),
which telescopes along the hierarchy.

* a band, with supplied windows: `RMF.pfFull_mul_bandLevelW_le_clean`, its Jensen windows
  `RMF.bandWindows_jensen_clean`;
* the bottom, with supplied windows: `RMF.bottomLevelW_le_clean`, its nine top windows left to be
  bounded at their heights (`RMF.winNoSplitFull_le_of_le`, `RMF.winSplitFull_le_range`,
  `RMF.bottomT_mem`), the rest by `RMF.bottomWindows_jensen_clean`.
-/

open MeasureTheory

namespace RMF

/-! ### Numeric helpers -/

lemma nine_div_le_of_le {L : ℝ} (hL : 999 ≤ L) : 9.0028 / L ≤ 0.00902 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

lemma window_exponent_aux {u : ℝ} (hu : 1000 ≤ u) :
    ((u + 1) ^ 2 / 2 + 15.003 * (u + 1) + 34) * ((3 / 2) ^ 2 / u ^ 2) ≤ 2.33 / 2 := by
  have hu2 : 0 < u ^ 2 := by positivity
  rw [mul_div_assoc', div_le_iff₀ hu2]
  nlinarith

lemma two_sub_div_three_le {q y : ℝ} (hq0 : 1 / 2 ≤ q) (hy : 1000 ≤ y) :
    (2 - 2 * q) / (3 * y) ≤ 0.00034 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma three_halves_div_le {u : ℝ} (hu : 1000 ≤ u) : 3 / 2 / u ≤ 0.0015 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The window constant of a split window once `log y ≥ 1000`:
`(W((1-q)·2.33)/(1.498π))^q·e^{0.0185(q(2q-1) + q)}`, `W = RMF.taylorWindowW`. -/
noncomputable def omegaClean (q : ℝ) : ℝ :=
  (taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498)) ^ q
    * Real.exp (0.0185 * (q * (2 * q - 1) + q))

/-- **A split window, cleaned.**  For `½ ≤ q ≤ 1`, `2 ≤ y ≤ z` with `log y ≥ 1000` and
`1 ≤ m` with `e^m ≤ 1.5κ`, `κ = log z/log y`, the window at height `e^m/log z` split at
`RMF.splitPt (3/2)` is at most `(1.5κ/e^m)^{q(2q-1)}·RMF.omegaClean q`. -/
theorem winSplit_le_clean {q m : ℝ} {y z : ℕ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hy : 2 ≤ y)
    (hyz : y ≤ z) (hly : 1000 ≤ Real.log y) (hm1 : 1 ≤ m)
    (hm : Real.exp m ≤ 3 / 2 * (Real.log z / Real.log y)) :
    winSplit q (Real.exp m / Real.log z) y (splitPt (3 / 2) (Real.exp m / Real.log z) y z) z
      ≤ (3 / 2 * (Real.log z / Real.log y) / Real.exp m) ^ (q * (2 * q - 1))
        * omegaClean q := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hly0 : 0 < Real.log y := by linarith
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have hem : 0 < Real.exp m := Real.exp_pos m
  have he1 : Real.exp 1 ≤ Real.exp m := Real.exp_le_exp.2 hm1
  have he2 : (2.7 : ℝ) ≤ Real.exp m := le_trans (by linarith [Real.exp_one_gt_d9]) he1
  set T := Real.exp m / Real.log z with hTdef
  have hT : 0 < T := by positivity
  set u := 3 / 2 / T with hudef
  have hu : u = 3 / 2 * Real.log z / Real.exp m := by
    rw [hudef, hTdef]
    field_simp
  -- `log y ≤ u ≤ log z`
  have hu_ly : Real.log y ≤ u := by
    rw [hu, le_div_iff₀ hem]
    calc Real.log y * Real.exp m ≤ Real.log y * (3 / 2 * (Real.log z / Real.log y)) :=
          mul_le_mul_of_nonneg_left hm hly0.le
      _ = 3 / 2 * Real.log z := by field_simp
  have hu_lz : u ≤ Real.log z := by
    rw [hu, div_le_iff₀ hem]
    have := mul_le_mul_of_nonneg_left he2 hlz0.le
    linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu1000 : (1000 : ℝ) ≤ u := by linarith
  -- the split point is `⌊e^u⌋`
  have hfl_y : y ≤ ⌊Real.exp u⌋₊ := by
    refine Nat.le_floor ?_
    calc (y : ℝ) = Real.exp (Real.log y) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp u := Real.exp_le_exp.2 hu_ly
  have hfl_z : ⌊Real.exp u⌋₊ ≤ z := by
    refine Nat.floor_le_of_le ?_
    calc Real.exp u ≤ Real.exp (Real.log z) := Real.exp_le_exp.2 hu_lz
      _ = z := Real.exp_log (by linarith)
  have hsp : splitPt (3 / 2) T y z = ⌊Real.exp u⌋₊ := by
    rw [splitPt, max_eq_right hfl_y, min_eq_right hfl_z]
  rw [hsp]
  set z₁ := ⌊Real.exp u⌋₊ with hz₁def
  obtain ⟨hl1, hl2⟩ := log_floor_exp_bounds hu1
  rw [← hz₁def] at hl1 hl2
  have hl0 : 999 ≤ Real.log z₁ := by linarith [Real.log_two_lt_d9]
  have hlz₁0 : 0 < Real.log z₁ := by linarith
  -- (PF) of the lower block
  have hPF : pfBand q y z₁ ≤ (u / Real.log y) ^ (q * (2 * q - 1))
      * Real.exp (q * (2 * q - 1) * 0.0185) := by
    rw [pfBand]
    have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
    refine mul_le_mul (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hl2
      hly0.le) ha) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ha)) (Real.exp_pos _).le
      (Real.rpow_nonneg (by positivity) _)
    have h1 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
    have h2 := nine_div_le_of_le hl0
    have hy1000 : (1000 : ℝ) ≤ y := by
      have h := Real.add_one_le_exp (Real.log y)
      rw [Real.exp_log (by linarith)] at h
      linarith
    have h3 := two_sub_div_three_le hq0 hy1000
    linarith
  -- the upper block's mean
  have hM : mBand z₁ z ≤ Real.log z / (u - Real.log 2) * Real.exp 0.0181 := by
    rw [mBand]
    have hden : 0 < u - Real.log 2 := by linarith [Real.log_two_lt_d9]
    refine mul_le_mul (div_le_div_of_nonneg_left hlz0.le hden hl1) (Real.exp_le_exp.2 ?_)
      (Real.exp_pos _).le (div_nonneg hlz0.le hden.le)
    have h1 := nine_div_le_of_le hl0
    have h2 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log z)
    linarith
  -- the window's exponent
  have hb : 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2 ≤ (1 - q) * 2.33 := by
    have hq' : 0 ≤ 1 - q := by linarith
    have hz₁1 : Real.log ((z₁ + 1 : ℕ) : ℝ) ≤ u + 1 := by
      have hz₁pos : (0 : ℝ) < (z₁ : ℝ) := by
        refine Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => ?_)
        rw [h, Nat.cast_zero, Real.log_zero] at hlz₁0
        exact lt_irrefl 0 hlz₁0
      have h1 : ((z₁ + 1 : ℕ) : ℝ) ≤ Real.exp (u + 1) := by
        push_cast
        have hfle : (z₁ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
        have h2 : Real.exp (u + 1) = Real.exp u * Real.exp 1 := Real.exp_add _ _
        have h3 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp (by linarith)
        have h4 := mul_le_mul_of_nonneg_left
          (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) (Real.exp_pos u).le
        rw [h2]
        linarith
      calc Real.log ((z₁ + 1 : ℕ) : ℝ) ≤ Real.log (Real.exp (u + 1)) :=
            Real.log_le_log (by positivity) h1
        _ = u + 1 := Real.log_exp _
    have hl0' : 0 ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hT2 : T ^ 2 = (3 / 2) ^ 2 / u ^ 2 := by
      rw [hudef]
      field_simp
    have hS : Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34
        ≤ (u + 1) ^ 2 / 2 + 15.003 * (u + 1) + 34 := by
      have := pow_le_pow_left₀ hl0' hz₁1 2
      linarith
    have hkey := window_exponent_aux hu1000
    calc 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
          + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2
        ≤ 2 * (1 - q)
          * (((u + 1) ^ 2 / 2 + 15.003 * (u + 1) + 34) * ((3 / 2) ^ 2 / u ^ 2)) := by
          rw [hT2, mul_assoc (2 * (1 - q))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS (by positivity))
            (by positivity)
      _ ≤ 2 * (1 - q) * (2.33 / 2) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (1 - q) * 2.33 := by ring
  have hW := taylorWindowW_mono hb
  have hW0 : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2) :=
    taylorWindowW_nonneg (by
      have hq' : 0 ≤ 1 - q := by linarith
      have : 0 ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
      positivity)
  -- `(πT log z)(u - log 2) ≥ 1.498π`
  have hden : Real.pi * 1.498 ≤ Real.pi * T * Real.log z * (u - Real.log 2) / Real.log z := by
    have hTl : T * Real.log z = Real.exp m := by rw [hTdef]; field_simp
    have hTu : T * u = 3 / 2 := by rw [hudef]; field_simp
    have hlog2 := Real.log_two_lt_d9
    have hTsmall : T ≤ 0.0015 := by
      have : T = 3 / 2 / u := by rw [hudef]; field_simp
      rw [this]
      exact three_halves_div_le hu1000
    have hT0' : 0 ≤ T := hT.le
    rw [show Real.pi * T * Real.log z * (u - Real.log 2) / Real.log z
        = Real.pi * (T * u - T * Real.log 2) by field_simp, hTu]
    have hpi := Real.pi_pos
    have : T * Real.log 2 ≤ 0.0015 * 0.6932 :=
      mul_le_mul hTsmall (by linarith) (Real.log_nonneg (by norm_num)) (by norm_num)
    have h5 := mul_le_mul_of_nonneg_left
      (show (1.498 : ℝ) ≤ 3 / 2 - T * Real.log 2 by linarith) hpi.le
    linarith
  -- assemble
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  have hinner : taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
        * mBand z₁ z / (Real.pi * T * Real.log z)
      ≤ taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498) * Real.exp 0.0181 := by
    have hmB0 : 0 ≤ mBand z₁ z := by rw [mBand]; positivity
    have hden0 : 0 < Real.pi * T * Real.log z := by positivity
    rw [div_le_iff₀ hden0]
    have hWb : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
      taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
    have hul : 0 < u - Real.log 2 := by linarith [Real.log_two_lt_d9]
    calc taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
          + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2) * mBand z₁ z
        ≤ taylorWindowW ((1 - q) * 2.33)
          * (Real.log z / (u - Real.log 2) * Real.exp 0.0181) :=
          mul_le_mul hW hM hmB0 hWb
      _ = taylorWindowW ((1 - q) * 2.33) * Real.exp 0.0181
          * (Real.log z / (u - Real.log 2)) := by ring
      _ ≤ taylorWindowW ((1 - q) * 2.33) * Real.exp 0.0181
          * ((Real.pi * T * Real.log z) / (Real.pi * 1.498)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ hul (by positivity)]
          have := hden
          rw [le_div_iff₀ hlz0] at this
          linarith
      _ = taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498) * Real.exp 0.0181
          * (Real.pi * T * Real.log z) := by ring
  have hin0 : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
        * mBand z₁ z / (Real.pi * T * Real.log z) := by
    have hmB0 : 0 ≤ mBand z₁ z := by rw [mBand]; positivity
    positivity
  have hpow := Real.rpow_le_rpow hin0 hinner hq0'
  rw [winSplit]
  have hu_eq : u / Real.log y = 3 / 2 * (Real.log z / Real.log y) / Real.exp m := by
    rw [hu]; field_simp
  rw [hu_eq] at hPF
  calc pfBand q y z₁ * (taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
        * mBand z₁ z / (Real.pi * T * Real.log z)) ^ q
      ≤ ((3 / 2 * (Real.log z / Real.log y) / Real.exp m) ^ (q * (2 * q - 1))
          * Real.exp (q * (2 * q - 1) * 0.0185))
        * (taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498) * Real.exp 0.0181) ^ q :=
        mul_le_mul hPF hpow (Real.rpow_nonneg hin0 _) (by positivity)
    _ ≤ (3 / 2 * (Real.log z / Real.log y) / Real.exp m) ^ (q * (2 * q - 1)) * omegaClean q := by
        rw [omegaClean, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
        have hWb : 0 ≤ taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498) := by
          have : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
            taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
          positivity
        rw [Real.mul_rpow hWb (Real.exp_pos _).le, ← Real.exp_mul]
        have h1 : Real.exp (q * (2 * q - 1) * 0.0185) * ((taylorWindowW ((1 - q) * 2.33)
            / (Real.pi * 1.498)) ^ q * Real.exp (0.0181 * q))
            = (taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498)) ^ q
              * Real.exp (q * (2 * q - 1) * 0.0185 + 0.0181 * q) := by
          rw [Real.exp_add]; ring
        rw [h1]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hWb _)
        linarith

/-- **The window without a split, cleaned**: for `2 ≤ y ≤ z` with `log y ≥ 1000`,
`RMF.winNoSplit q (e^m/log z) y z ≤ ((e-1)κe^{0.0181}/(πe^m))^q`. -/
theorem winNoSplit_le_clean {q m : ℝ} {y z : ℕ} (hq0 : 0 ≤ q) (hy : 2 ≤ y) (hyz : y ≤ z)
    (hly : 1000 ≤ Real.log y) :
    winNoSplit q (Real.exp m / Real.log z) y z
      ≤ ((Real.exp 1 - 1) * (Real.log z / Real.log y) * Real.exp 0.0181
        / (Real.pi * Real.exp m)) ^ q := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hly0 : 0 < Real.log y := by linarith
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [winNoSplit]
  refine Real.rpow_le_rpow (by rw [mBand]; positivity) ?_ hq0
  have hM : mBand y z ≤ Real.log z / Real.log y * Real.exp 0.0181 := by
    rw [mBand]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
    have h2 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log z)
    linarith
  have heq : Real.pi * (Real.exp m / Real.log z) * Real.log z = Real.pi * Real.exp m := by
    field_simp
  rw [heq]
  have hpe : 0 < Real.pi * Real.exp m := by positivity
  rw [div_le_div_iff_of_pos_right hpe]
  calc (Real.exp 1 - 1) * mBand y z
      ≤ (Real.exp 1 - 1) * (Real.log z / Real.log y * Real.exp 0.0181) :=
        mul_le_mul_of_nonneg_left hM he1
    _ = (Real.exp 1 - 1) * (Real.log z / Real.log y) * Real.exp 0.0181 := by ring

/-- A reflected geometric sum: `∑_{k<n} r^{n-k}·K ≤ r(K - 1)/(1 - r)` once `K r^n ≥ 1`. -/
lemma sum_range_pow_sub_mul_le {r K : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {n : ℕ}
    (hK : 1 ≤ K * r ^ n) :
    (∑ k ∈ Finset.range n, r ^ (n - k)) * K ≤ r * (K - 1) / (1 - r) := by
  have hrefl : ∑ k ∈ Finset.range n, r ^ (n - k) = ∑ j ∈ Finset.range n, r ^ (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => r ^ (j + 1)) n]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show n - 1 - k + 1 = n - k by omega]
  have hgeom : ∑ j ∈ Finset.range n, r ^ (j + 1) = r * ((1 - r ^ n) / (1 - r)) := by
    have hne : r ≠ 1 := ne_of_lt hr1
    have h1 : (1 - r ^ n) / (1 - r) = (r ^ n - 1) / (r - 1) := by
      rw [← neg_div_neg_eq]
      ring_nf
    rw [h1, ← geom_sum_eq hne n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrefl, hgeom]
  have h1r : 0 < 1 - r := by linarith
  rw [show r * ((1 - r ^ n) / (1 - r)) * K = r * (K - K * r ^ n) / (1 - r) by
    field_simp]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hr0) h1r.le

lemma div_exp_rpow {x m a : ℝ} (hx : 0 ≤ x) :
    (x / Real.exp m) ^ a = x ^ a * Real.exp (-(a * m)) := by
  rw [Real.div_rpow hx (Real.exp_pos m).le, ← Real.exp_mul, Real.exp_neg, div_eq_mul_inv,
    mul_comm m a]

lemma exp_neg_mul_sub_eq_pow {a : ℝ} {n k : ℕ} (hk : k ≤ n) :
    Real.exp (-(a * ((n : ℝ) - k))) = Real.exp (-a) ^ (n - k) := by
  rw [← Real.exp_nat_mul, Nat.cast_sub hk]
  ring_nf

/-- The heights of a band's windows at `θ = 1`: `RMF.bandT 1 y z k = e^{J-k}/log z`. -/
lemma bandT_one_eq {y z : ℕ} (hz : 1 < Real.log z) (k : ℕ) :
    bandT 1 y z k = Real.exp ((bandJ 1 y z : ℝ) - k) / Real.log z := by
  have hlz : 0 < Real.log z := by linarith
  rw [bandT, show Real.log (1 / Real.log z) + (bandJ 1 y z : ℝ) - k
      = Real.log (1 / Real.log z) + ((bandJ 1 y z : ℝ) - k) by ring, Real.exp_add,
    Real.exp_log (by positivity)]
  field_simp

/-- **A band's windows, cleaned.**  For `½ < q ≤ 1` and `2 ≤ y ≤ z` with `log y ≥ 1000`,
at `θ = 1`, `c_s = 3/2` the windows and far range of `RMF.bandLevel` times the lower (PF) are at
most `pfFull(y)·(J₀ + far) + e^{a c_y}·ω(q)·1.5^a·e^{-a}(log^a z - log^a y)/(1 - e^{-a})`,
`a = q(2q-1)`, `c_y = 0.2641 + 9.0028/log y + (2-2q)/3`, `ω = RMF.omegaClean`: the top window
without a split, the others split (`RMF.winSplit_le_clean`) and summed geometrically. -/
theorem pfFull_mul_bandWindows_le {q : ℝ} {y z : ℕ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hy : 2 ≤ y) (hyz : y ≤ z) (hly : 1000 ≤ Real.log y) :
    pfFull q y * (∑ k ∈ Finset.range (bandJ 1 y z),
        min (winNoSplit q (bandT 1 y z k) y z)
          (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z)
      + (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q)
    ≤ pfFull q y * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q)
      + Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3))
        * omegaClean q * (3 / 2) ^ (q * (2 * q - 1))
        * (Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1)))))
        * (Real.log z ^ (q * (2 * q - 1)) - Real.log y ^ (q * (2 * q - 1))) := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hly0 : 0 < Real.log y := by linarith
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have hκ1 : 1 ≤ Real.log z / Real.log y := by rw [le_div_iff₀ hly0]; linarith
  have hκ0 : 0 < Real.log z / Real.log y := by linarith
  have hlogκ : 0 ≤ Real.log (Real.log z / Real.log y) := Real.log_nonneg hκ1
  have hJeq : bandJ 1 y z = ⌈Real.log (Real.log z / Real.log y)⌉₊ := by rw [bandJ, one_mul]
  have hJ1 : Real.log (Real.log z / Real.log y) ≤ (bandJ 1 y z : ℝ) := by
    rw [hJeq]; exact Nat.le_ceil _
  have hJ2 : (bandJ 1 y z : ℝ) < Real.log (Real.log z / Real.log y) + 1 := by
    rw [hJeq]; exact Nat.ceil_lt_add_one hlogκ
  have heJ : Real.log z / Real.log y ≤ Real.exp (bandJ 1 y z) := by
    calc Real.log z / Real.log y = Real.exp (Real.log (Real.log z / Real.log y)) :=
          (Real.exp_log hκ0).symm
      _ ≤ Real.exp (bandJ 1 y z) := Real.exp_le_exp.2 hJ1
  have hpf0 : 0 ≤ pfFull q y := by rw [pfFull]; positivity
  have hM : mBand y z ≤ Real.log z / Real.log y * Real.exp 0.0181 := by
    rw [mBand]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
    have h2 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log z)
    linarith
  have hmB0 : 0 ≤ mBand y z := by rw [mBand]; positivity
  -- the far range
  have hfar : (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q
      ≤ (Real.exp 0.0181 / Real.pi) ^ q := by
    refine Real.rpow_le_rpow (by positivity) ?_ hq0'
    rw [mul_one, div_le_div_iff₀ (by positivity) Real.pi_pos]
    have := mul_le_mul hM heJ hκ0.le (by positivity)
    nlinarith [Real.pi_pos, Real.exp_pos 0.0181, Real.exp_pos (bandJ 1 y z : ℝ)]
  -- the windows
  set J := bandJ 1 y z with hJdef
  set c := Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3))
    with hcdef
  set r := Real.exp (-(q * (2 * q - 1))) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hWp0 : 0 ≤ c * omegaClean q * (3 / 2) ^ (q * (2 * q - 1)) * (r / (1 - r))
      * (Real.log z ^ (q * (2 * q - 1)) - Real.log y ^ (q * (2 * q - 1))) := by
    have hω : 0 ≤ omegaClean q := by
      rw [omegaClean]
      have : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
        taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
      positivity
    have hrr : 0 ≤ r / (1 - r) := div_nonneg hr0 (by linarith)
    have hd : 0 ≤ Real.log z ^ (q * (2 * q - 1)) - Real.log y ^ (q * (2 * q - 1)) :=
      sub_nonneg.2 (Real.rpow_le_rpow hly0.le hlz ha.le)
    positivity
  have hsum : pfFull q y * ∑ k ∈ Finset.range J,
        min (winNoSplit q (bandT 1 y z k) y z)
          (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z)
      ≤ pfFull q y * ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + c * omegaClean q * (3 / 2) ^ (q * (2 * q - 1)) * (r / (1 - r))
          * (Real.log z ^ (q * (2 * q - 1)) - Real.log y ^ (q * (2 * q - 1))) := by
    have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hJ0c : 0 ≤ pfFull q y * ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q :=
      mul_nonneg hpf0 (Real.rpow_nonneg (div_nonneg (mul_nonneg he1 (Real.exp_pos _).le)
        Real.pi_pos.le) _)
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · rw [hJ0, Finset.sum_range_zero, mul_zero]
      linarith
    obtain ⟨n, hn⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
    rw [hn, Finset.sum_range_succ', mul_add]
    -- the top window, without a split
    have htop : pfFull q y * min (winNoSplit q (bandT 1 y z 0) y z)
          (winSplit q (bandT 1 y z 0) y (splitPt (3 / 2) (bandT 1 y z 0) y z) z)
        ≤ pfFull q y * ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q := by
      refine mul_le_mul_of_nonneg_left (le_trans (min_le_left _ _) ?_) hpf0
      rw [bandT_one_eq (by linarith) 0, Nat.cast_zero, sub_zero, ← hJdef]
      refine le_trans (winNoSplit_le_clean hq0' hy hyz hly) (Real.rpow_le_rpow
        (by positivity) ?_ hq0')
      rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have := mul_le_mul_of_nonneg_left heJ (mul_nonneg he1 (Real.exp_pos 0.0181).le)
      nlinarith [Real.pi_pos]
    -- the split windows
    have hsplit : ∀ k ∈ Finset.range n,
        min (winNoSplit q (bandT 1 y z (k + 1)) y z)
          (winSplit q (bandT 1 y z (k + 1)) y (splitPt (3 / 2) (bandT 1 y z (k + 1)) y z) z)
        ≤ (3 / 2 * (Real.log z / Real.log y)) ^ (q * (2 * q - 1)) * omegaClean q
          * r ^ (n - k) := by
      intro k hk
      have hkn := Finset.mem_range.1 hk
      refine le_trans (min_le_right _ _) ?_
      have hm : ((J : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = (n : ℝ) - k := by
        rw [hn]; push_cast; ring
      rw [bandT_one_eq (by linarith) (k + 1), ← hJdef, hm]
      have hnk : (1 : ℝ) ≤ (n : ℝ) - k := by
        have : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        push_cast at this
        linarith
      have hnκ : (n : ℝ) < Real.log (Real.log z / Real.log y) := by
        have : ((J : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hn]; push_cast; ring
        linarith
      have hexp : Real.exp ((n : ℝ) - k) ≤ 3 / 2 * (Real.log z / Real.log y) := by
        have h1 : Real.exp ((n : ℝ) - k) ≤ Real.exp (Real.log (Real.log z / Real.log y)) :=
          Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        rw [Real.exp_log hκ0] at h1
        linarith
      refine le_trans (winSplit_le_clean hq0.le hq1 hy hyz hly hnk hexp) (le_of_eq ?_)
      rw [div_exp_rpow (by positivity), hrdef, ← exp_neg_mul_sub_eq_pow hkn.le]
      ring
    have hS := Finset.sum_le_sum hsplit
    rw [← Finset.mul_sum] at hS
    -- the geometric sum
    have hK : 1 ≤ (Real.log z / Real.log y) ^ (q * (2 * q - 1)) * r ^ n := by
      rw [Real.rpow_def_of_pos hκ0, hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.one_le_exp (?_)
      have : ((J : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hn]; push_cast; ring
      nlinarith
    have hgeo := sum_range_pow_sub_mul_le hr0 hr1 hK
    have hpfeq : pfFull q y = Real.log y ^ (q * (2 * q - 1)) * c := by rw [pfFull, hcdef]
    have hlzeq : Real.log y ^ (q * (2 * q - 1)) * (Real.log z / Real.log y) ^ (q * (2 * q - 1))
        = Real.log z ^ (q * (2 * q - 1)) := by
      rw [← Real.mul_rpow hly0.le hκ0.le]
      congr 1
      field_simp
    have hsplit_tot : pfFull q y * ∑ k ∈ Finset.range n,
        min (winNoSplit q (bandT 1 y z (k + 1)) y z)
          (winSplit q (bandT 1 y z (k + 1)) y (splitPt (3 / 2) (bandT 1 y z (k + 1)) y z) z)
        ≤ c * omegaClean q * (3 / 2) ^ (q * (2 * q - 1)) * (r / (1 - r))
          * (Real.log z ^ (q * (2 * q - 1)) - Real.log y ^ (q * (2 * q - 1))) := by
      refine le_trans (mul_le_mul_of_nonneg_left hS hpf0) ?_
      have hω : 0 ≤ omegaClean q := by
        rw [omegaClean]
        have : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
          taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
        positivity
      rw [Real.mul_rpow (by norm_num) hκ0.le, hpfeq]
      have h1r : 0 < 1 - r := by linarith
      calc Real.log y ^ (q * (2 * q - 1)) * c
            * ((3 / 2) ^ (q * (2 * q - 1)) * (Real.log z / Real.log y) ^ (q * (2 * q - 1))
              * omegaClean q * ∑ k ∈ Finset.range n, r ^ (n - k))
          = c * omegaClean q * (3 / 2) ^ (q * (2 * q - 1)) * Real.log y ^ (q * (2 * q - 1))
            * ((∑ k ∈ Finset.range n, r ^ (n - k))
              * (Real.log z / Real.log y) ^ (q * (2 * q - 1))) := by ring
        _ ≤ c * omegaClean q * (3 / 2) ^ (q * (2 * q - 1)) * Real.log y ^ (q * (2 * q - 1))
            * (r * ((Real.log z / Real.log y) ^ (q * (2 * q - 1)) - 1) / (1 - r)) :=
            mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = c * omegaClean q * (3 / 2) ^ (q * (2 * q - 1)) * (r / (1 - r))
            * (Real.log y ^ (q * (2 * q - 1)) * (Real.log z / Real.log y) ^ (q * (2 * q - 1))
              - Real.log y ^ (q * (2 * q - 1))) := by ring
        _ = _ := by rw [hlzeq]
    linarith
  rw [mul_add, mul_add]
  have hfar' := mul_le_mul_of_nonneg_left hfar hpf0
  rw [hrdef] at hsum
  linarith

/-! ### The truncation bound's constant and error at `η = (log x)^{-2}` -/

lemma one_add_pow_four_le {L : ℝ} (hL : 1000 ≤ L) :
    5 * (1 + L) ^ 4 * (1 + (L ^ 2)⁻¹) ≤ 6 * L ^ 4 := by
  have hL0 : 0 < L := by linarith
  have h1 : (1 + L) ^ 4 ≤ 1.0041 * L ^ 4 := by
    have : 1 + L ≤ 1.001 * L := by linarith
    calc (1 + L) ^ 4 ≤ (1.001 * L) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
      _ = 1.001 ^ 4 * L ^ 4 := by ring
      _ ≤ 1.0041 * L ^ 4 := by gcongr; norm_num
  have h2 : (L ^ 2)⁻¹ ≤ 1 / 1000000 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : 0 ≤ L ^ 4 := by positivity
  have h3 : 5 * (1 + L) ^ 4 * (1 + (L ^ 2)⁻¹) ≤ 5 * (1.0041 * L ^ 4) * (1 + 1 / 1000000) := by
    gcongr
  nlinarith

/-- **The truncation bound's constant at the sieve level** `z' = ⌊z/(log x)^7⌋ ≥ 2`,
`η = (log x)^{-2}`: with `7 log log x + 1 ≤ ρ log z`, `ρ < 1`,
`lemmaTConst z z' η ε·e^{2/log x} ≤ (1+ε)(2/(1-ρ) + 6/log x)(1+η)(1+(log x)^{-5})e^{2/log x}`. -/
lemma lemmaTConst_mul_exp_le {x ε ρ : ℝ} {z : ℕ} (hε : 0 < ε) (hlx : 1000 ≤ Real.log x)
    (hzx : (z : ℝ) ≤ x) (hz' : 2 ≤ sieveLevel x z) (hρ1 : ρ < 1)
    (hρ : 7 * Real.log (Real.log x) + 1 ≤ ρ * Real.log z) :
    lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)
      ≤ (1 + ε) * (2 / (1 - ρ) + 6 / Real.log x) * (1 + (Real.log x ^ 2)⁻¹)
        * (1 + (Real.log x ^ 5)⁻¹) * Real.exp (2 * (Real.log x)⁻¹) := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set z' := sieveLevel x z with hz'def
  set η := (L ^ 2)⁻¹ with hηdef
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [hηdef]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hz'R : (2 : ℝ) ≤ z' := by exact_mod_cast hz'
  have hL7 : 0 < L ^ 7 := by positivity
  have hz'eq : (z' : ℝ) = (⌊(z : ℝ) / L ^ 7⌋₊ : ℕ) := by rw [hz'def, sieveLevel]
  have hfl : (z' : ℝ) ≤ z / L ^ 7 := by rw [hz'eq]; exact Nat.floor_le (by positivity)
  have hzL : 2 * L ^ 7 ≤ (z : ℝ) := by
    have := le_trans hz'R hfl
    rwa [le_div_iff₀ hL7] at this
  have hL7' : 1 ≤ L ^ 7 := one_le_pow₀ hL1
  have hz2 : (2 : ℝ) ≤ z := by linarith
  have hz0 : 0 < (z : ℝ) := by linarith
  have hlz0 : 0 < Real.log z := Real.log_pos (by linarith)
  have hz'z : (z' : ℝ) ≤ z := le_trans hfl (div_le_self hz0.le hL7')
  -- `log z' ≥ log z - 7 log L - log 2 ≥ (1 - ρ) log z`
  have hlz'lo : (1 - ρ) * Real.log z ≤ Real.log z' := by
    have hfl2 : (z : ℝ) / L ^ 7 - 1 < z' := by
      have := Nat.lt_floor_add_one ((z : ℝ) / L ^ 7)
      rw [hz'eq]
      linarith
    have hhalf : (z : ℝ) / (2 * L ^ 7) ≤ z' := by
      have h1 : (z : ℝ) / (2 * L ^ 7) = (z / L ^ 7) / 2 := by field_simp
      have h2 : (2 : ℝ) ≤ z / L ^ 7 := by rw [le_div_iff₀ hL7]; linarith
      rw [h1]
      linarith
    have h1 : Real.log ((z : ℝ) / (2 * L ^ 7)) ≤ Real.log z' :=
      Real.log_le_log (by positivity) hhalf
    rw [Real.log_div hz0.ne' (by positivity), Real.log_mul (by norm_num) hL7.ne',
      Real.log_pow] at h1
    have h2 := Real.log_two_lt_d9
    push_cast at h1
    have h3 : (1 - ρ) * Real.log z = Real.log z - ρ * Real.log z := by ring
    linarith
  have hlz' : 0 < Real.log z' := lt_of_lt_of_le (mul_pos (by linarith) hlz0) hlz'lo
  have hlzL : Real.log z ≤ L := Real.log_le_log hz0 hzx
  -- the sieve constant
  have hS1 : 2 * Real.log z / Real.log z' ≤ 2 / (1 - ρ) := by
    rw [div_le_div_iff₀ hlz' (by linarith)]
    linarith
  have hS2 : 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 * Real.log z * (1 + η) / (z * η + 1 + η)
      ≤ 6 / L := by
    have hlz'z : Real.log z' ≤ Real.log z := Real.log_le_log (by linarith) hz'z
    have hA : (1 + Real.log z') ^ 3 * Real.log z ≤ (1 + L) ^ 4 := by
      have h1 : (1 + Real.log z') ^ 3 ≤ (1 + L) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
      calc (1 + Real.log z') ^ 3 * Real.log z ≤ (1 + L) ^ 3 * (1 + L) :=
            mul_le_mul h1 (by linarith) hlz0.le (by positivity)
        _ = (1 + L) ^ 4 := by ring
    rw [div_le_div_iff₀ (by positivity) hL0]
    have hηL : L ^ 7 * η = L ^ 5 := by rw [hηdef]; field_simp
    have hz'L : (z' : ℝ) * L ^ 5 ≤ z * η := by
      have h1 := mul_le_mul_of_nonneg_right hfl hL7.le
      rw [div_mul_cancel₀ _ hL7.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 hη0.le
      rw [mul_assoc, hηL] at h2
      exact h2
    have h6 := one_add_pow_four_le hlx
    rw [← hηdef] at h6
    have hz'0 : (0 : ℝ) ≤ z' := by linarith
    have hB : 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 * Real.log z * (1 + η) * L
        ≤ 5 * z' * (1 + L) ^ 4 * (1 + η) * L := by
      have h0 : 0 ≤ 5 * (z' : ℝ) * (1 + η) * L := by positivity
      have := mul_le_mul_of_nonneg_left hA h0
      linarith
    have hC : 5 * (z' : ℝ) * (1 + L) ^ 4 * (1 + η) * L ≤ 6 * L ^ 4 * (z' * L) := by
      have := mul_le_mul_of_nonneg_right h6 (by positivity : (0 : ℝ) ≤ z' * L)
      linarith
    have hD : 6 * L ^ 4 * ((z' : ℝ) * L) = 6 * ((z' : ℝ) * L ^ 5) := by ring
    linarith
  have hT : (1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η ≤ (1 + η) * (1 + (L ^ 5)⁻¹) := by
    have h1 : (1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η
        = (1 + η) + (1 + η) ^ 2 / (z * η) := by
      field_simp
    rw [h1]
    have hηL : 2 * L ^ 7 * η = 2 * L ^ 5 := by rw [hηdef]; field_simp
    have hzη : 2 * L ^ 5 ≤ z * η := by
      have := mul_le_mul_of_nonneg_right hzL hη0.le
      linarith
    have hL5 : 0 < L ^ 5 := by positivity
    have h2 : (1 + η) ^ 2 / (z * η) ≤ (1 + η) * (L ^ 5)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have h5 : 2 ≤ (L ^ 5)⁻¹ * (z * η) := by
        rw [inv_mul_eq_div, le_div_iff₀ hL5]
        linarith
      have h6 : (1 + η) ^ 2 ≤ (1 + η) * 2 := by nlinarith
      have h7 : (1 + η) * 2 ≤ (1 + η) * ((L ^ 5)⁻¹ * (z * η)) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h8 : (1 + η) * ((L ^ 5)⁻¹ * (z * η)) = (1 + η) * (L ^ 5)⁻¹ * (z * η) := by ring
      linarith
    have h3 : (1 + η) * (1 + (L ^ 5)⁻¹) = (1 + η) + (1 + η) * (L ^ 5)⁻¹ := by ring
    linarith
  have hSSC : smallQSieveConst z z' η ≤ 2 / (1 - ρ) + 6 / L := by
    rw [smallQSieveConst]
    linarith
  have hSSC0 : 0 ≤ smallQSieveConst z z' η := by
    rw [smallQSieveConst]
    have : 0 ≤ 2 * Real.log z / Real.log z' := div_nonneg (by linarith) hlz'.le
    have : 0 ≤ 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 * Real.log z * (1 + η)
        / (z * η + 1 + η) := div_nonneg (by positivity) (by positivity)
    linarith
  rw [lemmaTConst]
  have hTnn : 0 ≤ (1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η := by positivity
  calc (1 + ε) * smallQSieveConst z z' η * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η)
        * Real.exp (2 * L⁻¹)
      ≤ (1 + ε) * (2 / (1 - ρ) + 6 / L) * ((1 + η) * (1 + (L ^ 5)⁻¹))
        * Real.exp (2 * L⁻¹) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hSSC (by linarith)) hT hTnn
          (mul_nonneg (by linarith) (le_trans hSSC0 hSSC))
    _ = _ := by ring

/-! ### The band level's pieces, cleaned -/

/-- The lower (PF)'s constant once `log y ≥ 1000`: `e^{q(2q-1)(0.2732 + (2-2q)/3)}`. -/
noncomputable def pfC1 (q : ℝ) : ℝ := Real.exp (q * (2 * q - 1) * (0.2732 + (2 - 2 * q) / 3))

/-- The (PF) constant of a lower block times its band once `log y ≥ 1000`:
`e^{q(2q-1)(0.2915 + (2-2q)/3)}`. -/
noncomputable def pfC2 (q : ℝ) : ℝ := Real.exp (q * (2 * q - 1) * (0.2915 + (2 - 2 * q) / 3))

/-- The central window's constant once `log z ≥ 1000` and `log x ≥ 50000`
(`A₁ = (2q-1)(1 + (2-2q)/3)`):
`(1.0062A₁)²(1 + e^{1.0062A₁})²/(4π) + (0.5158/π)·1.0002·(1 + (e^{2(1-q)0.5158} - 1)/3)`. -/
noncomputable def cenClean (q : ℝ) : ℝ :=
  (1.0062 * ((2 * q - 1) * (1 + (2 - 2 * q) / 3))) ^ 2
      * (1 + Real.exp (1.0062 * ((2 * q - 1) * (1 + (2 - 2 * q) / 3)))) ^ 2 / (4 * Real.pi)
    + 0.5158 / Real.pi * 1.0002 * (1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3)

lemma pfFull_le_pfC1 {q : ℝ} (hq0 : 1 / 2 ≤ q) {y : ℕ} (hly : 1000 ≤ Real.log y) :
    pfFull q y ≤ Real.log y ^ (q * (2 * q - 1)) * pfC1 q := by
  rw [pfFull, pfC1]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (by linarith) _)
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) (by linarith))
  have := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
  have h2 : 9.0028 / Real.log y ≤ 0.0091 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

lemma pfFull_mul_pfBand_le {q : ℝ} (hq0 : 1 / 2 ≤ q) {y z : ℕ} (hyz : y ≤ z)
    (hly : 1000 ≤ Real.log y) :
    pfFull q y * pfBand q y z ≤ Real.log z ^ (q * (2 * q - 1)) * pfC2 q := by
  have hly0 : 0 < Real.log y := by linarith
  have hy1 : (1 : ℝ) < y := by
    by_contra h
    have h1 : (y : ℝ) ≤ 1 := le_of_not_gt h
    have : Real.log y ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h1
    linarith
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hy1000 : (1000 : ℝ) ≤ y := by
    have h := Real.add_one_le_exp (Real.log y)
    rw [Real.exp_log (by linarith)] at h
    linarith
  rw [pfFull, pfBand, pfC2]
  have hpow : Real.log y ^ (q * (2 * q - 1)) * (Real.log z / Real.log y) ^ (q * (2 * q - 1))
      = Real.log z ^ (q * (2 * q - 1)) := by
    rw [← Real.mul_rpow hly0.le (div_nonneg hlz0.le hly0.le)]
    congr 1
    field_simp
  have h1 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
  have h2 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log z)
  have h3 := two_sub_div_three_le hq0 hy1000
  have hsum : 0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3
      + (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y))
      ≤ 0.2915 + (2 - 2 * q) / 3 := by linarith
  calc Real.log y ^ (q * (2 * q - 1))
        * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3))
        * ((Real.log z / Real.log y) ^ (q * (2 * q - 1))
          * Real.exp (q * (2 * q - 1)
            * (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y))))
      = (Real.log y ^ (q * (2 * q - 1)) * (Real.log z / Real.log y) ^ (q * (2 * q - 1)))
        * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3
          + (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y)))) := by
        rw [show q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3
            + (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y)))
          = q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3)
            + q * (2 * q - 1) * (9.0028 / Real.log y + 9.0028 / Real.log z
              + (2 - 2 * q) / (3 * y)) by ring, Real.exp_add]
        ring
    _ ≤ Real.log z ^ (q * (2 * q - 1)) * Real.exp (q * (2 * q - 1)
          * (0.2915 + (2 - 2 * q) / 3)) := by
        rw [hpow]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsum ha))
          (Real.rpow_nonneg hlz0.le _)

lemma exp_le_of_small {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 0.000162) : Real.exp x ≤ 1.0002 := by
  refine le_trans (Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)) ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The central window, cleaned**: for `½ ≤ q ≤ 1`, `log z ≥ 1000` and
`50000 ≤ log x`, `log z ≤ log x`: `RMF.cenBand q (log x)^{-2} (1/log z) z ≤ RMF.cenClean q`. -/
lemma cenBand_le_clean {q x : ℝ} {z : ℕ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hlz : 1000 ≤ Real.log z) (hzx : Real.log z ≤ Real.log x) (hlx : 50000 ≤ Real.log x) :
    cenBand q (Real.log x ^ 2)⁻¹ (1 / Real.log z) z ≤ cenClean q := by
  have hlz0 : 0 < Real.log z := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  have hz1 : (1 : ℝ) < z := by
    by_contra h
    have h1 : (z : ℝ) ≤ 1 := le_of_not_gt h
    have : Real.log z ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h1
    linarith
  set L := Real.log ((z + 1 : ℕ) : ℝ) with hLdef
  -- `log z ≤ L ≤ log z + log 2`
  have hL1 : Real.log z ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) (by push_cast; linarith)
  have hL2 : L ≤ Real.log z + Real.log 2 := by
    rw [hLdef, ← Real.log_mul (ne_of_gt (by linarith)) (by norm_num)]
    exact Real.log_le_log (by positivity) (by push_cast; linarith)
  have hlog2 := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  set B := L + Real.log 4 + 4 with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef, hlog4]; linarith
  have hBlz : B ≤ 1.00608 * Real.log z := by rw [hBdef, hlog4]; linarith
  set A1 := (2 * q - 1) * (1 + (2 - 2 * q) / 3) with hA1def
  have hA10 : 0 ≤ A1 := mul_nonneg (by linarith) (by linarith)
  set σ := (Real.log x ^ 2)⁻¹ with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  -- `σ log z ≤ 1/log x ≤ 0.00002`
  have hσlz : σ * Real.log z ≤ 0.00002 := by
    rw [hσdef, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- the first part
  have hAτ : (2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z) ≤ 1.0062 * A1 := by
    have : (2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z)
        = A1 * (B / Real.log z) := by
      rw [hA1def]; ring
    rw [this]
    have hBl : B / Real.log z ≤ 1.0062 := by
      rw [div_le_iff₀ hlz0]; linarith
    nlinarith
  have hAτσ : (2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z + σ) ≤ 1.0062 * A1 := by
    have : (2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z + σ)
        = A1 * (B / Real.log z * (1 + σ * Real.log z)) := by
      rw [hA1def]; field_simp
    rw [this]
    have hBl : B / Real.log z * (1 + σ * Real.log z) ≤ 1.0062 := by
      have h1 : B / Real.log z ≤ 1.00608 := by rw [div_le_iff₀ hlz0]; linarith
      have h2 : 0 ≤ B / Real.log z := div_nonneg hB0 hlz0.le
      have h3 : 0 ≤ σ * Real.log z := mul_nonneg hσ0 hlz0.le
      nlinarith
    nlinarith
  have hAτ0 : 0 ≤ (2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z) := by
    have : 0 ≤ (2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hB0)
    positivity
  have hpart1 : (2 * Real.pi * Real.log z)⁻¹ * (2 * (1 / Real.log z)
        * (((2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B)) ^ 2
        * (1 + Real.exp ((2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z + σ))) ^ 2
          / 4))
      ≤ (1.0062 * A1) ^ 2 * (1 + Real.exp (1.0062 * A1)) ^ 2 / (4 * Real.pi) := by
    have heq : (2 * Real.pi * Real.log z)⁻¹ * (2 * (1 / Real.log z)
        * (((2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B)) ^ 2
        * (1 + Real.exp ((2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z + σ))) ^ 2
          / 4))
        = ((2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z)) ^ 2
          * (1 + Real.exp ((2 * q - 1) * ((1 + (2 - 2 * q) / 3) * B) * (1 / Real.log z + σ)))
            ^ 2 / (4 * Real.pi) := by
      field_simp
    rw [heq]
    have hpi := Real.pi_pos
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul (pow_le_pow_left₀ hAτ0 hAτ 2)
      (pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_le_exp.2 hAτσ]) 2)
      (by positivity) (by positivity)
  -- the second part
  set S := L ^ 2 / 2 + 15.003 * L + 34 with hSdef
  have hL0 : 0 ≤ L := by linarith
  have hS0 : 0 ≤ S := by positivity
  have hSlz : S * (1 / Real.log z) ^ 2 ≤ 0.5158 := by
    rw [div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)]
    have hL2' : L ≤ Real.log z + 0.6932 := by linarith
    have h1 : L * L ≤ (Real.log z + 0.6932) * (Real.log z + 0.6932) :=
      mul_le_mul hL2' hL2' hL0 (by linarith)
    have hsq : 1000 * Real.log z ≤ Real.log z * Real.log z :=
      mul_le_mul_of_nonneg_right hlz hlz0.le
    have hS : S = L * L / 2 + 15.003 * L + 34 := by rw [hSdef]; ring
    rw [hS]
    linarith
  have hS2 : 0 ≤ S * (1 / Real.log z) ^ 2 := by positivity
  have hEσ : Real.exp (4 * (1 - q) * σ * (4 * B)) ≤ 1.0002 := by
    have hq' : 0 ≤ 1 - q := by linarith
    have h3 : 0 ≤ σ * B := mul_nonneg hσ0 hB0
    have h2 : 4 * (1 - q) * σ * (4 * B) = 16 * (1 - q) * (σ * B) := by ring
    rw [h2]
    refine exp_le_of_small (mul_nonneg (mul_nonneg (by norm_num) hq') h3) ?_
    have h1 : σ * B ≤ 1.00608 * (σ * Real.log z) := by
      have := mul_le_mul_of_nonneg_left hBlz hσ0
      linarith
    have h4 : 16 * (1 - q) * (σ * B) ≤ 8 * (σ * B) :=
      mul_le_mul_of_nonneg_right (by linarith) h3
    linarith
  have hpart2 : (2 * Real.pi * Real.log z)⁻¹ * (S * Real.exp (4 * (1 - q) * σ * (4 * B))
        * (2 * (1 / Real.log z) + 2 * (1 / Real.log z) / 3
          * (Real.exp (2 * (1 - q) * S * (1 / Real.log z) ^ 2) - 1)))
      ≤ 0.5158 / Real.pi * 1.0002 * (1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3) := by
    have heq : (2 * Real.pi * Real.log z)⁻¹ * (S * Real.exp (4 * (1 - q) * σ * (4 * B))
        * (2 * (1 / Real.log z) + 2 * (1 / Real.log z) / 3
          * (Real.exp (2 * (1 - q) * S * (1 / Real.log z) ^ 2) - 1)))
        = S * (1 / Real.log z) ^ 2 / Real.pi * Real.exp (4 * (1 - q) * σ * (4 * B))
          * (1 + (Real.exp (2 * (1 - q) * (S * (1 / Real.log z) ^ 2)) - 1) / 3) := by
      field_simp
    rw [heq]
    have hpi := Real.pi_pos
    have hq' : 0 ≤ 1 - q := by linarith
    have hE1 : Real.exp (2 * (1 - q) * (S * (1 / Real.log z) ^ 2))
        ≤ Real.exp (2 * (1 - q) * 0.5158) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hSlz (by linarith))
    have hE2 : 0 ≤ Real.exp (2 * (1 - q) * (S * (1 / Real.log z) ^ 2)) - 1 :=
      sub_nonneg.2 (Real.one_le_exp (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 - q)) hS2))
    have hX : 0 ≤ 1 + (Real.exp (2 * (1 - q) * (S * (1 / Real.log z) ^ 2)) - 1) / 3 :=
      add_nonneg zero_le_one (div_nonneg hE2 (by norm_num))
    have hX2 : 1 + (Real.exp (2 * (1 - q) * (S * (1 / Real.log z) ^ 2)) - 1) / 3
        ≤ 1 + (Real.exp (2 * (1 - q) * 0.5158) - 1) / 3 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right hE1 1) (by norm_num))
    exact mul_le_mul (mul_le_mul (div_le_div_of_nonneg_right hSlz hpi.le) hEσ
      (Real.exp_pos _).le (div_nonneg (by norm_num) hpi.le)) hX2 hX
      (mul_nonneg (div_nonneg (by norm_num) hpi.le) (by norm_num))
  rw [cenBand, cenClean, mul_add, ← hLdef, ← hBdef, ← hSdef, ← hA1def]
  exact add_le_add hpart1 hpart2

lemma cenBand_nonneg {q σ τ : ℝ} {z : ℕ} (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hlz : 0 < Real.log z) :
    0 ≤ cenBand q σ τ z := by
  rw [cenBand]
  have hL : 0 ≤ Real.log ((z + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hq' : 0 ≤ 1 - q := by linarith
  have hS : 0 ≤ Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34 := by
    positivity
  have hE : 0 ≤ Real.exp (2 * (1 - q)
      * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34)
      * τ ^ 2) - 1 := sub_nonneg.2 (Real.one_le_exp (by positivity))
  have h2 : 0 ≤ 2 * τ + 2 * τ / 3 * (Real.exp (2 * (1 - q)
      * (Real.log ((z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z + 1 : ℕ) : ℝ) + 34)
      * τ ^ 2) - 1) := by positivity
  have hpi := Real.pi_pos
  positivity

lemma smallQReductionErr_nonneg {x ε : ℝ} (hε : 0 < ε) (hlx : 0 ≤ Real.log x) (hx : 0 ≤ x)
    {z' : ℕ} (hz' : 1 ≤ z') : 0 ≤ smallQReductionErr x z' (Real.log x ^ 2)⁻¹ ε := by
  rw [smallQReductionErr]
  have : 0 ≤ Real.log z' := Real.log_nonneg (by exact_mod_cast hz')
  positivity

/-- **The truncation bound's error at the sieve level**, `η = (log x)^{-2}`: with
`7 log log x + 1 ≤ ρ log z`, `ρ < 1`:
`smallQReductionErr x z' η ε ≤ (1+1/ε)(1.003/log x + 2.0001/((1-ρ) log z))`. -/
lemma smallQReductionErr_le {x ε ρ : ℝ} {z : ℕ} (hε : 0 < ε) (hlx : 1000 ≤ Real.log x)
    (hzx : (z : ℝ) ≤ x) (hz' : 2 ≤ sieveLevel x z) (hρ1 : ρ < 1)
    (hρ : 7 * Real.log (Real.log x) + 1 ≤ ρ * Real.log z) :
    smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε
      ≤ (1 + 1 / ε) * (1.003 / Real.log x + 2.0001 / ((1 - ρ) * Real.log z)) := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set z' := sieveLevel x z with hz'def
  set η := (L ^ 2)⁻¹ with hηdef
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 1000000 := by
    rw [hηdef, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hz'R : (2 : ℝ) ≤ z' := by exact_mod_cast hz'
  have hL7 : 0 < L ^ 7 := by positivity
  have hz'eq : (z' : ℝ) = (⌊(z : ℝ) / L ^ 7⌋₊ : ℕ) := by rw [hz'def, sieveLevel]
  have hfl : (z' : ℝ) ≤ z / L ^ 7 := by rw [hz'eq]; exact Nat.floor_le (by positivity)
  have hzL : 2 * L ^ 7 ≤ (z : ℝ) := by
    have := le_trans hz'R hfl
    rwa [le_div_iff₀ hL7] at this
  have hL7' : 1 ≤ L ^ 7 := one_le_pow₀ hL1
  have hz0 : 0 < (z : ℝ) := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le hz0 hzx
  have hlz0 : 0 < Real.log z := Real.log_pos (by linarith)
  -- `log z' ≥ (1 - ρ) log z`
  have hlz'lo : (1 - ρ) * Real.log z ≤ Real.log z' := by
    have hfl2 : (z : ℝ) / L ^ 7 - 1 < z' := by
      have := Nat.lt_floor_add_one ((z : ℝ) / L ^ 7)
      rw [hz'eq]
      linarith
    have hhalf : (z : ℝ) / (2 * L ^ 7) ≤ z' := by
      have h1 : (z : ℝ) / (2 * L ^ 7) = (z / L ^ 7) / 2 := by field_simp
      have h2 : (2 : ℝ) ≤ z / L ^ 7 := by rw [le_div_iff₀ hL7]; linarith
      rw [h1]
      linarith
    have h1 : Real.log ((z : ℝ) / (2 * L ^ 7)) ≤ Real.log z' :=
      Real.log_le_log (by positivity) hhalf
    rw [Real.log_div hz0.ne' (by positivity), Real.log_mul (by norm_num) hL7.ne',
      Real.log_pow] at h1
    have h2 := Real.log_two_lt_d9
    push_cast at h1
    have h3 : (1 - ρ) * Real.log z = Real.log z - ρ * Real.log z := by ring
    linarith
  have hlz' : 0 < Real.log z' := lt_of_lt_of_le (mul_pos (by linarith) hlz0) hlz'lo
  have h2lz' : 2 / Real.log z' ≤ 2 / ((1 - ρ) * Real.log z) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos (by linarith) hlz0) hlz'lo
  -- the small pieces
  have hA : η * (1 + L) ≤ 1.001 / L := by
    rw [hηdef, le_div_iff₀ hL0]
    have : (L ^ 2)⁻¹ * (1 + L) * L = (1 + L) / L := by field_simp
    rw [this, div_le_iff₀ hL0]
    linarith
  have hB : 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 / x ≤ 0.001 / L := by
    have hz'x : (z' : ℝ) ≤ x / L ^ 7 := le_trans hfl (div_le_div_of_nonneg_right hzx hL7.le)
    have hlz'x : Real.log z' ≤ L := Real.log_le_log (by linarith)
      (le_trans hz'x (div_le_self hx0.le hL7'))
    have h1 : (1 + Real.log z') ^ 3 ≤ (1 + L) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have h2 : (1 + L) ^ 3 ≤ 2 * L ^ 3 := by
      have : 1 + L ≤ 1.001 * L := by linarith
      calc (1 + L) ^ 3 ≤ (1.001 * L) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 1.001 ^ 3 * L ^ 3 := by ring
        _ ≤ 2 * L ^ 3 := by gcongr; norm_num
    rw [div_le_div_iff₀ hx0 hL0]
    have hz'L : (z' : ℝ) * L ^ 7 ≤ x := by
      rwa [le_div_iff₀ hL7] at hz'x
    have hL3 : 0 ≤ L ^ 3 := by positivity
    have hz'0 : (0 : ℝ) ≤ z' := by linarith
    have h3 : 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 * L ≤ 5 * z' * (2 * L ^ 3) * L := by
      have := mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity : (0 : ℝ) ≤ 5 * z')
      nlinarith
    have h4 : 5 * (z' : ℝ) * (2 * L ^ 3) * L = 10 * (z' * L ^ 4) := by ring
    have h5 : 10 * ((z' : ℝ) * L ^ 4) ≤ 0.001 * x := by
      have hL3' : (10000 : ℝ) ≤ L ^ 3 := by nlinarith
      have : (z' : ℝ) * L ^ 4 * L ^ 3 = z' * L ^ 7 := by ring
      have h6 : 10000 * ((z' : ℝ) * L ^ 4) ≤ z' * L ^ 7 := by
        rw [← this]
        exact mul_le_mul_of_nonneg_left hL3' (by positivity) |>.trans_eq' (by ring)
      linarith
    linarith
  rw [smallQReductionErr]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1η : 1 + η ≤ 1.000001 := by linarith
  have hC : (1 + η) * (2 / Real.log z' + 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 / x)
      ≤ 1.000001 * (2 / ((1 - ρ) * Real.log z) + 0.001 / L) := by
    have h0 : 0 ≤ 2 / Real.log z' + 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 / x := by
      have : 0 ≤ Real.log z' := hlz'.le
      positivity
    exact mul_le_mul h1η (by linarith) h0 (by norm_num)
  have hD : 1.000001 * (2 / ((1 - ρ) * Real.log z)) ≤ 2.0001 / ((1 - ρ) * Real.log z) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by norm_num) (mul_pos (by linarith) hlz0).le
  have hE : 1.000001 * (0.001 / L) ≤ 0.002 / L := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by norm_num) hL0.le
  have hF : 1.001 / L + 0.002 / L = 1.003 / L := by ring
  linarith

lemma rpow_atom_le {q V M κ : ℝ} (hq : 0 ≤ q) (hM0 : 0 ≤ M) (hM : M ≤ κ * Real.exp 0.0181) :
    (Real.exp (-V) * M ^ Real.exp 1) ^ q
      ≤ Real.exp (-(q * V)) * (κ * Real.exp 0.0181) ^ (Real.exp 1 * q) := by
  have hκ0 : 0 ≤ κ * Real.exp 0.0181 := le_trans hM0 hM
  rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hM0 _), ← Real.exp_mul,
    ← Real.rpow_mul hM0]
  refine mul_le_mul (le_of_eq (by ring_nf)) (Real.rpow_le_rpow hM0 hM
    (mul_nonneg (Real.exp_pos 1).le hq)) (Real.rpow_nonneg hM0 _) (Real.exp_pos _).le

/-- **A band's level above `½` with supplied windows, cleaned.**  For `½ < q ≤ 1`,
`η', ε > 0`, `2 ≤ y ≤ z ≤ x` with `log y ≥ 1000`, `log x ≥ 50000`, the sieve level
`⌊z/(log x)^7⌋ ≥ 2`, the truncation bound's constant `≤ K_c` and its error `≤ E_c`, the level at
`θ = 1`, `c_s = 3/2` times the lower (PF) is at most

`log^a z·[pfC2(K_c^q(cen^q + ((1+1/η')/π)^q) + (K_c/(1000 log²x))^q)
  + pfC1·(log y/log z)^a·(K_c^q(1+η')^q(J₀ + far) + e^{-qV}(κe^{0.0181})^{eq} + E_c^q)]
  + K_c^q(1+η')^q·pfC1·ω·1.5^a·e^{-a}/(1-e^{-a})·(log^a z - log^a y)`,

`a = q(2q-1)`, `κ = log z/log y`, `V = log x/log z`, `cen = RMF.cenClean q`,
`J₀ = ((e-1)e^{0.0181}/π)^q`, `far = (e^{0.0181}/π)^q`, with the windows `w k` of
`RMF.bandLevelW` supplied with `pfFull(y)(∑ w + far) ≤ log^a z(log y/log z)^a pfC1(J₀ + far)
+ pfC1·W_B` in place of the last term's `ω·1.5^a e^{-a}/(1-e^{-a})(log^a z - log^a y)`. -/
theorem pfFull_mul_bandLevelW_le_clean {q η' ε x Kc Ec WB : ℝ} {y z : ℕ} {w : ℕ → ℝ}
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hy : 2 ≤ y) (hyz : y ≤ z)
    (hzx : (z : ℝ) ≤ x) (hly : 1000 ≤ Real.log y) (hlx : 50000 ≤ Real.log x)
    (hz' : 2 ≤ sieveLevel x z)
    (hK : lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)
      ≤ Kc)
    (hE : smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε ≤ Ec)
    (hw0 : ∀ k, 0 ≤ w k)
    (hWin : pfFull q y * (∑ k ∈ Finset.range (bandJ 1 y z), w k
        + (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q)
      ≤ Real.log z ^ (q * (2 * q - 1)) * ((Real.log y / Real.log z) ^ (q * (2 * q - 1))
          * pfC1 q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q))
        + pfC1 q * WB) :
    pfFull q y * bandLevelW q 1 η' ε x y z w
      ≤ Real.log z ^ (q * (2 * q - 1))
          * (pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
              + (Kc / (1000 * Real.log x ^ 2)) ^ q)
            + pfC1 q * (Real.log y / Real.log z) ^ (q * (2 * q - 1))
              * (Kc ^ q * (1 + η') ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
                  + (Real.exp 0.0181 / Real.pi) ^ q)
                + Real.exp (-(q * (Real.log x / Real.log z)))
                  * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q)
                + Ec ^ q))
        + Kc ^ q * (1 + η') ^ q * pfC1 q * WB := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hly0 : 0 < Real.log y := by linarith
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have hx0 : 0 < x := by linarith
  have hlzx : Real.log z ≤ Real.log x := Real.log_le_log (by linarith) hzx
  set lx := Real.log x with hlxdef
  set σ := (lx ^ 2)⁻¹ with hσdef
  have hσ : 0 < σ := by positivity
  set z' := sieveLevel x z with hz'def
  have hz'z : z' ≤ z := by
    rw [hz'def, sieveLevel]
    refine Nat.floor_le_of_le ?_
    exact div_le_self (by positivity) (one_le_pow₀ (by linarith))
  set LT := lemmaTConst z z' σ ε with hLTdef
  have hLT0 : 0 < LT := lemmaTConst_pos hz' hz'z hσ hε
  have hLTK : LT ≤ Kc := le_trans (le_mul_of_one_le_right hLT0.le
    (Real.one_le_exp (by positivity))) hK
  have hKc0 : 0 ≤ Kc := le_trans hLT0.le hLTK
  set P := pfFull q y with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef, pfFull]; positivity
  have hPle := pfFull_le_pfC1 hq0.le hly
  rw [← hPdef] at hPle
  have hPB := pfFull_mul_pfBand_le hq0.le hyz hly
  rw [← hPdef] at hPB
  have hB0 : 0 ≤ pfBand q y z := by rw [pfBand]; positivity
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hc2 : 0 ≤ pfC2 q := (Real.exp_pos _).le
  set a := q * (2 * q - 1) with hadef
  have hlya : Real.log y ^ a = Real.log z ^ a * (Real.log y / Real.log z) ^ a := by
    rw [← Real.mul_rpow hlz0.le (div_nonneg hly0.le hlz0.le)]
    congr 1
    field_simp
  have hlza0 : 0 ≤ Real.log z ^ a := Real.rpow_nonneg hlz0.le _
  have hra0 : 0 ≤ (Real.log y / Real.log z) ^ a :=
    Real.rpow_nonneg (div_nonneg hly0.le hlz0.le) _
  -- (i) the atom
  have hM : mBand y z ≤ Real.log z / Real.log y * Real.exp 0.0181 := by
    rw [mBand]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
    have h2 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log z)
    linarith
  have hmB0 : 0 ≤ mBand y z := by rw [mBand]; positivity
  have hatom := rpow_atom_le (V := lx / Real.log z) hq0' hmB0 hM
  have hatomC0 : 0 ≤ Real.exp (-(q * (lx / Real.log z)))
      * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
  have hi : P * (Real.exp (-(lx / Real.log z)) * mBand y z ^ Real.exp 1) ^ q
      ≤ Real.log z ^ a * (pfC1 q * (Real.log y / Real.log z) ^ a
        * (Real.exp (-(q * (lx / Real.log z)))
          * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q))) := by
    calc P * (Real.exp (-(lx / Real.log z)) * mBand y z ^ Real.exp 1) ^ q
        ≤ (Real.log y ^ a * pfC1 q) * (Real.exp (-(q * (lx / Real.log z)))
          * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q)) :=
          mul_le_mul hPle hatom (Real.rpow_nonneg (by positivity) _)
            (mul_nonneg (Real.rpow_nonneg hly0.le _) hc1)
      _ = _ := by rw [hlya]; ring
  -- (ii) the first error
  have hσlz : σ / Real.log z ≤ 1 / (1000 * lx ^ 2) := by
    rw [hσdef, div_le_div_iff₀ hlz0 (by positivity),
      show (lx ^ 2)⁻¹ * (1000 * lx ^ 2) = 1000 by field_simp]
    linarith
  have hii : P * ((LT * (σ / Real.log z)) ^ q * pfBand q y z)
      ≤ Real.log z ^ a * (pfC2 q * (Kc / (1000 * lx ^ 2)) ^ q) := by
    have h1 : (LT * (σ / Real.log z)) ^ q ≤ (Kc / (1000 * lx ^ 2)) ^ q := by
      refine Real.rpow_le_rpow (by positivity) ?_ hq0'
      calc LT * (σ / Real.log z) ≤ Kc * (1 / (1000 * lx ^ 2)) :=
            mul_le_mul hLTK hσlz (by positivity) hKc0
        _ = Kc / (1000 * lx ^ 2) := by ring
    calc P * ((LT * (σ / Real.log z)) ^ q * pfBand q y z)
        = (LT * (σ / Real.log z)) ^ q * (P * pfBand q y z) := by ring
      _ ≤ (Kc / (1000 * lx ^ 2)) ^ q * (Real.log z ^ a * pfC2 q) :=
          mul_le_mul h1 hPB (mul_nonneg hP0 hB0) (Real.rpow_nonneg (by positivity) _)
      _ = _ := by ring
  -- (iii)-(v) the main term
  have hK0 : 0 ≤ LT * Real.exp (2 * lx⁻¹) := by positivity
  have hKq : (LT * Real.exp (2 * lx⁻¹)) ^ q ≤ Kc ^ q := Real.rpow_le_rpow hK0 hK hq0'
  have hcen : cenBand q σ (1 / Real.log z) z ^ q ≤ cenClean q ^ q :=
    Real.rpow_le_rpow (cenBand_nonneg hq1 (by positivity) hlz0)
      (cenBand_le_clean hq0.le hq1 (by linarith) hlzx hlx) hq0'
  have hcoh : ((1 + 1 / η') / (Real.pi * 1)) ^ q = ((1 + 1 / η') / Real.pi) ^ q := by
    rw [mul_one]
  set W := ∑ k ∈ Finset.range (bandJ 1 y z), w k
      + (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q with hWdef
  have hW0 : 0 ≤ W :=
    add_nonneg (Finset.sum_nonneg fun k _ => hw0 k) (Real.rpow_nonneg (by positivity) _)
  have hW' := hWin
  have hmain : P * ((LT * Real.exp (2 * lx⁻¹)) ^ q
      * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
        + ((1 + 1 / η') / (Real.pi * 1)) ^ q * pfBand q y z + (1 + η') ^ q * W))
      ≤ Real.log z ^ a * (pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q))
          + Kc ^ q * (1 + η') ^ q * ((Real.log y / Real.log z) ^ a * pfC1 q
            * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
              + (Real.exp 0.0181 / Real.pi) ^ q)))
        + Kc ^ q * (1 + η') ^ q * (pfC1 q * WB) := by
    rw [hcoh]
    have hcoh0 : 0 ≤ ((1 + 1 / η') / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
    have hcen0 : 0 ≤ cenBand q σ (1 / Real.log z) z ^ q :=
      Real.rpow_nonneg (cenBand_nonneg hq1 (by positivity) hlz0) _
    have hη'q : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
    have hinner : P * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
          + ((1 + 1 / η') / Real.pi) ^ q * pfBand q y z + (1 + η') ^ q * W)
        ≤ Real.log z ^ a * (pfC2 q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
            + (1 + η') ^ q * ((Real.log y / Real.log z) ^ a * pfC1 q
              * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
                + (Real.exp 0.0181 / Real.pi) ^ q)))
          + (1 + η') ^ q * (pfC1 q * WB) := by
      have e1 : P * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
          + ((1 + 1 / η') / Real.pi) ^ q * pfBand q y z + (1 + η') ^ q * W)
          = (cenBand q σ (1 / Real.log z) z ^ q + ((1 + 1 / η') / Real.pi) ^ q)
            * (P * pfBand q y z) + (1 + η') ^ q * (P * W) := by ring
      rw [e1]
      have f1 : (cenBand q σ (1 / Real.log z) z ^ q + ((1 + 1 / η') / Real.pi) ^ q)
          * (P * pfBand q y z)
          ≤ (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q) * (Real.log z ^ a * pfC2 q) :=
        mul_le_mul (by linarith) hPB (mul_nonneg hP0 hB0) (add_nonneg (Real.rpow_nonneg
          (le_trans (cenBand_nonneg hq1 (by positivity) hlz0)
            (cenBand_le_clean hq0.le hq1 (by linarith) hlzx hlx)) _) hcoh0)
      have f2 := mul_le_mul_of_nonneg_left hW' hη'q
      refine le_trans (add_le_add f1 f2) (le_of_eq ?_)
      ring
    have hinner0 : 0 ≤ P * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
          + ((1 + 1 / η') / Real.pi) ^ q * pfBand q y z + (1 + η') ^ q * W) := by positivity
    calc P * ((LT * Real.exp (2 * lx⁻¹)) ^ q
          * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
            + ((1 + 1 / η') / Real.pi) ^ q * pfBand q y z + (1 + η') ^ q * W))
        = (LT * Real.exp (2 * lx⁻¹)) ^ q
          * (P * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
            + ((1 + 1 / η') / Real.pi) ^ q * pfBand q y z + (1 + η') ^ q * W)) := by ring
      _ ≤ Kc ^ q * (Real.log z ^ a * (pfC2 q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
            + (1 + η') ^ q * ((Real.log y / Real.log z) ^ a * pfC1 q
              * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
                + (Real.exp 0.0181 / Real.pi) ^ q)))
          + (1 + η') ^ q * (pfC1 q * WB)) :=
          mul_le_mul hKq hinner hinner0 (Real.rpow_nonneg hKc0 _)
      _ = _ := by ring
  -- (vi) the second error
  have hErr0 : 0 ≤ smallQReductionErr x z' σ ε :=
    smallQReductionErr_nonneg hε (by linarith) hx0.le (by omega)
  have hvi : P * smallQReductionErr x z' σ ε ^ q
      ≤ Real.log z ^ a * (pfC1 q * (Real.log y / Real.log z) ^ a * Ec ^ q) := by
    calc P * smallQReductionErr x z' σ ε ^ q ≤ (Real.log y ^ a * pfC1 q) * Ec ^ q :=
          mul_le_mul hPle (Real.rpow_le_rpow hErr0 hE hq0') (Real.rpow_nonneg hErr0 _)
            (mul_nonneg (Real.rpow_nonneg hly0.le _) hc1)
      _ = _ := by rw [hlya]; ring
  -- assembly
  have hlev : P * bandLevelW q 1 η' ε x y z w
      = P * (Real.exp (-(lx / Real.log z)) * mBand y z ^ Real.exp 1) ^ q
        + P * ((LT * (σ / Real.log z)) ^ q * pfBand q y z)
        + P * ((LT * Real.exp (2 * lx⁻¹)) ^ q
          * (cenBand q σ (1 / Real.log z) z ^ q * pfBand q y z
            + ((1 + 1 / η') / (Real.pi * 1)) ^ q * pfBand q y z + (1 + η') ^ q * W))
        + P * smallQReductionErr x z' σ ε ^ q := by
    rw [bandLevelW, hWdef]
    ring
  rw [hlev]
  refine le_trans (add_le_add (add_le_add (add_le_add hi hii) hmain) hvi) (le_of_eq ?_)
  ring

/-- **The Jensen windows of a band, cleaned**: for `½ < q ≤ 1`, `2 ≤ y ≤ z`, `log y ≥ 1000`, the
windows of `RMF.bandLevel` at `θ = 1`, `c_s = 3/2` are nonnegative and satisfy the windows'
hypothesis of `RMF.pfFull_mul_bandLevelW_le_clean` with
`W_B = ω·1.5^a e^{-a}/(1-e^{-a})·(log^a z - log^a y)` (`RMF.pfFull_mul_bandWindows_le`). -/
theorem bandWindows_jensen_clean {q : ℝ} {y z : ℕ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hy : 2 ≤ y)
    (hyz : y ≤ z) (hly : 1000 ≤ Real.log y) :
    (∀ k, 0 ≤ min (winNoSplit q (bandT 1 y z k) y z)
      (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z))
    ∧ pfFull q y * (∑ k ∈ Finset.range (bandJ 1 y z),
        min (winNoSplit q (bandT 1 y z k) y z)
          (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z)
        + (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q)
      ≤ Real.log z ^ (q * (2 * q - 1)) * ((Real.log y / Real.log z) ^ (q * (2 * q - 1))
          * pfC1 q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q))
        + pfC1 q * (omegaClean q * (3 / 2) ^ (q * (2 * q - 1))
          * (Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1)))))
          * (Real.log z ^ (q * (2 * q - 1)) - Real.log y ^ (q * (2 * q - 1)))) := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hly0 : 0 < Real.log y := by linarith
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have hmB0 : 0 ≤ mBand y z := by rw [mBand]; positivity
  set P := pfFull q y with hPdef
  have hPle := pfFull_le_pfC1 hq0.le hly
  rw [← hPdef] at hPle
  set a := q * (2 * q - 1) with hadef
  have hlya : Real.log y ^ a = Real.log z ^ a * (Real.log y / Real.log z) ^ a := by
    rw [← Real.mul_rpow hlz0.le (div_nonneg hly0.le hlz0.le)]
    congr 1
    field_simp
  have hW := pfFull_mul_bandWindows_le hq0 hq1 hy hyz hly
  rw [← hPdef, ← hadef] at hW
  set W := ∑ k ∈ Finset.range (bandJ 1 y z),
        min (winNoSplit q (bandT 1 y z k) y z)
          (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z)
      + (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q with hWdef
  have hw0 : ∀ k, 0 ≤ min (winNoSplit q (bandT 1 y z k) y z)
      (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z) := by
    intro k
    refine le_min ?_ ?_
    · rw [winNoSplit]
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hT0 : 0 ≤ bandT 1 y z k := by rw [bandT]; positivity
      exact Real.rpow_nonneg (div_nonneg (mul_nonneg he1 hmB0)
        (mul_nonneg (mul_nonneg Real.pi_pos.le hT0) hlz0.le)) _
    · rw [winSplit, pfBand]
      have : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((splitPt (3 / 2) (bandT 1 y z k)
          y z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((splitPt (3 / 2) (bandT 1 y z k) y z
          + 1 : ℕ) : ℝ) + 34) * bandT 1 y z k ^ 2) := by
        refine taylorWindowW_nonneg ?_
        have : 0 ≤ Real.log ((splitPt (3 / 2) (bandT 1 y z k) y z + 1 : ℕ) : ℝ) :=
          Real.log_natCast_nonneg _
        have : 0 ≤ 1 - q := by linarith
        positivity
      have : 0 ≤ mBand (splitPt (3 / 2) (bandT 1 y z k) y z) z := by rw [mBand]; positivity
      have : 0 ≤ bandT 1 y z k := by rw [bandT]; positivity
      positivity
  set cy := Real.exp (a * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3)) with hcydef
  have hcy : cy ≤ pfC1 q := by
    rw [hcydef, pfC1, ← hadef]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ha)
    have h1 : 9.0028 / Real.log y ≤ 0.0091 := by
      rw [div_le_iff₀ hly0]
      linarith
    linarith
  set G := omegaClean q * (3 / 2) ^ a * (Real.exp (-a) / (1 - Real.exp (-a))) with hGdef
  have hG0 : 0 ≤ G := by
    have hω : 0 ≤ omegaClean q := by
      rw [omegaClean]
      have : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
        taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
      positivity
    have ha' : 0 < a := mul_pos (by linarith) (by linarith)
    have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have : 0 ≤ Real.exp (-a) / (1 - Real.exp (-a)) :=
      div_nonneg (Real.exp_pos _).le (by linarith)
    positivity
  have hdiff : 0 ≤ Real.log z ^ a - Real.log y ^ a :=
    sub_nonneg.2 (Real.rpow_le_rpow hly0.le hlz ha)
  have hW' : P * W ≤ Real.log z ^ a * ((Real.log y / Real.log z) ^ a * pfC1 q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q))
      + pfC1 q * (G * (Real.log z ^ a - Real.log y ^ a)) := by
    have hJF : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + (Real.exp 0.0181 / Real.pi) ^ q := by
      have : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      positivity
    have h1 : P * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + (Real.exp 0.0181 / Real.pi) ^ q)
        ≤ Real.log z ^ a * ((Real.log y / Real.log z) ^ a * pfC1 q
          * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q)) := by
      calc P * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q)
          ≤ (Real.log y ^ a * pfC1 q) * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q) := mul_le_mul_of_nonneg_right hPle hJF
        _ = _ := by rw [hlya]; ring
    have h2 : cy * G * (Real.log z ^ a - Real.log y ^ a)
        ≤ pfC1 q * G * (Real.log z ^ a - Real.log y ^ a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcy hG0) hdiff
    have h3 : cy * omegaClean q * (3 / 2) ^ a * (Real.exp (-a) / (1 - Real.exp (-a)))
        * (Real.log z ^ a - Real.log y ^ a) = cy * G * (Real.log z ^ a - Real.log y ^ a) := by
      rw [hGdef]; ring
    rw [h3] at hW
    linarith
  refine ⟨hw0, le_trans hW' (le_of_eq ?_)⟩
  rw [hGdef, hadef]

/-! ### The bottom's windows -/

/-- The split window's exponent over `T²` at the split `u = 3/2/T`, with `log(z₁+1) ≤ u + 1`:
`((u+1)²/2 + 15.003(u+1) + 34)(3/2/u)²`, written out. -/
noncomputable def splitST2 (u : ℝ) : ℝ :=
  1.125 * (1 + 1 / u) ^ 2 + 33.75675 * (1 / u + 1 / u ^ 2) + 76.5 / u ^ 2

lemma splitST2_anti {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : splitST2 v ≤ splitST2 u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h1 : 1 / v ≤ 1 / u := one_div_le_one_div_of_le hu huv
  have h2 : 1 / v ^ 2 ≤ 1 / u ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hu.le huv 2)
  have h3 : (1 + 1 / v) ^ 2 ≤ (1 + 1 / u) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h4 : 76.5 / v ^ 2 ≤ 76.5 / u ^ 2 := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div 76.5 (u ^ 2)]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  rw [splitST2, splitST2]
  nlinarith

/-- **A split window of the bottom, in a range of heights.**  For `½ ≤ q ≤ 1`, a height
`T > 0` with `u = 3/2/T ∈ [u_lo, u_hi]`, `1.2 ≤ u_lo`, `u_hi ≤ log z` and `log z ≥ 1000`, the
bottom's window split at `RMF.splitPt (3/2) T 2 z` is at most
`u_hi^a e^{a(0.2641 + 9.0028/(u_lo - log 2) + (2-2q)/3)}
  ·(W(2(1-q)·RMF.splitST2 u_lo)e^{9.0028/(u_lo - log 2) + 0.0091}/(π(3/2 - (3/2/u_lo)log 2)))^q`. -/
theorem winSplitFull_le_range {q T ulo uhi : ℝ} {z : ℕ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hT : 0 < T) (hulo : ulo ≤ 3 / 2 / T) (huhi : 3 / 2 / T ≤ uhi) (hulo1 : 1.2 ≤ ulo)
    (huz : uhi ≤ Real.log z) (hlz : 1000 ≤ Real.log z) :
    winSplitFull q T (splitPt (3 / 2) T 2 z) z
      ≤ uhi ^ (q * (2 * q - 1))
        * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / (ulo - Real.log 2) + (2 - 2 * q) / 3))
        * (taylorWindowW (2 * (1 - q) * splitST2 ulo)
          * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)
          / (Real.pi * (3 / 2 - 3 / 2 / ulo * Real.log 2))) ^ q := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  have hlz0 : 0 < Real.log z := by linarith
  have hz1 : (1 : ℝ) < z := by
    by_contra h
    have h1 : (z : ℝ) ≤ 1 := le_of_not_gt h
    have : Real.log z ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h1
    linarith
  set u := 3 / 2 / T with hudef
  have hTu : T * u = 3 / 2 := by rw [hudef]; field_simp
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the split point is `⌊e^u⌋`
  have heu : (3 : ℝ) ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    have h2 : Real.exp u = Real.exp 1 * Real.exp (u - 1) := by rw [← Real.exp_add]; ring_nf
    have h3 := Real.exp_one_gt_d9
    have h4 : 1 ≤ Real.exp (u - 1) := Real.one_le_exp (by linarith)
    have h5 : 1.2 ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
    nlinarith
  have hfl_2 : 2 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hfl_z : ⌊Real.exp u⌋₊ ≤ z := by
    refine Nat.floor_le_of_le ?_
    calc Real.exp u ≤ Real.exp (Real.log z) := Real.exp_le_exp.2 (by linarith)
      _ = z := Real.exp_log (by linarith)
  have hsp : splitPt (3 / 2) T 2 z = ⌊Real.exp u⌋₊ := by
    rw [splitPt, max_eq_right hfl_2, min_eq_right hfl_z]
  rw [hsp]
  set z₁ := ⌊Real.exp u⌋₊ with hz₁def
  obtain ⟨hl1, hl2⟩ := log_floor_exp_bounds hu1
  rw [← hz₁def] at hl1 hl2
  have hden0 : 0 < ulo - Real.log 2 := by linarith
  have hl1' : ulo - Real.log 2 ≤ Real.log z₁ := by linarith
  have hlz₁0 : 0 < Real.log z₁ := by linarith
  have hinv : 9.0028 / Real.log z₁ ≤ 9.0028 / (ulo - Real.log 2) :=
    div_le_div_of_nonneg_left (by norm_num) hden0 hl1'
  -- (PF) of the lower block
  have hPF : pfFull q z₁ ≤ uhi ^ (q * (2 * q - 1))
      * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / (ulo - Real.log 2) + (2 - 2 * q) / 3)) := by
    rw [pfFull]
    exact mul_le_mul (Real.rpow_le_rpow hlz₁0.le (by linarith) ha)
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) ha)) (Real.exp_pos _).le
      (Real.rpow_nonneg (by linarith) _)
  -- the upper block's mean
  have hM : mBand z₁ z ≤ Real.log z / (u - Real.log 2)
      * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091) := by
    rw [mBand]
    have hden : 0 < u - Real.log 2 := by linarith
    refine mul_le_mul (div_le_div_of_nonneg_left hlz0.le hden hl1) (Real.exp_le_exp.2 ?_)
      (Real.exp_pos _).le (div_nonneg hlz0.le hden.le)
    have h2 : 9.0028 / Real.log z ≤ 0.0091 := by
      rw [div_le_iff₀ hlz0]; linarith
    linarith
  -- the window's exponent
  have hb : 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2 ≤ 2 * (1 - q) * splitST2 ulo := by
    have hq' : 0 ≤ 1 - q := by linarith
    have hz₁1 : Real.log ((z₁ + 1 : ℕ) : ℝ) ≤ u + 1 := by
      have h1 : ((z₁ + 1 : ℕ) : ℝ) ≤ Real.exp (u + 1) := by
        push_cast
        have hfle : (z₁ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
        have h2 : Real.exp (u + 1) = Real.exp u * Real.exp 1 := Real.exp_add _ _
        have h3 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp (by linarith)
        have h4 := mul_le_mul_of_nonneg_left
          (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) (Real.exp_pos u).le
        rw [h2]
        linarith
      calc Real.log ((z₁ + 1 : ℕ) : ℝ) ≤ Real.log (Real.exp (u + 1)) :=
            Real.log_le_log (by positivity) h1
        _ = u + 1 := Real.log_exp _
    have hl0' : 0 ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hS : Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34
        ≤ (u + 1) ^ 2 / 2 + 15.003 * (u + 1) + 34 := by
      have := pow_le_pow_left₀ hl0' hz₁1 2
      linarith
    have hT2 : T ^ 2 = (3 / 2) ^ 2 / u ^ 2 := by rw [hudef]; field_simp
    have hST : ((u + 1) ^ 2 / 2 + 15.003 * (u + 1) + 34) * ((3 / 2) ^ 2 / u ^ 2)
        = splitST2 u := by
      rw [splitST2]
      field_simp
      ring
    have hanti := splitST2_anti (by linarith : 0 < ulo) (show ulo ≤ u from hulo)
    calc 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
          + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2
        ≤ 2 * (1 - q) * (((u + 1) ^ 2 / 2 + 15.003 * (u + 1) + 34) * ((3 / 2) ^ 2 / u ^ 2)) := by
          rw [hT2, mul_assoc (2 * (1 - q))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS (by positivity))
            (by positivity)
      _ = 2 * (1 - q) * splitST2 u := by rw [hST]
      _ ≤ 2 * (1 - q) * splitST2 ulo := mul_le_mul_of_nonneg_left hanti (by positivity)
  have hW := taylorWindowW_mono hb
  have hW0 : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2) := by
    refine taylorWindowW_nonneg ?_
    have hq' : 0 ≤ 1 - q := by linarith
    have : 0 ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    positivity
  -- the denominator: `πT log z (u - log 2)/log z = π(3/2 - T log 2) ≥ π(3/2 - (3/2/u_lo)log 2)`
  have hTlo : T ≤ 3 / 2 / ulo := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hulo hT.le
    rw [hudef, mul_div_cancel₀ _ hT.ne'] at this
    linarith
  have hden1 : 0 < 3 / 2 - 3 / 2 / ulo * Real.log 2 := by
    have : 3 / 2 / ulo ≤ 1.25 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  have hinner : taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
        * mBand z₁ z / (Real.pi * T * Real.log z)
      ≤ taylorWindowW (2 * (1 - q) * splitST2 ulo)
          * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)
          / (Real.pi * (3 / 2 - 3 / 2 / ulo * Real.log 2)) := by
    have hpi := Real.pi_pos
    have hmB0 : 0 ≤ mBand z₁ z := by rw [mBand]; positivity
    have hden : 0 < u - Real.log 2 := by linarith
    have heq : Real.pi * T * Real.log z * (u - Real.log 2) / Real.log z
        = Real.pi * (3 / 2 - T * Real.log 2) := by
      have h1 : Real.pi * T * Real.log z * (u - Real.log 2) / Real.log z
          = Real.pi * (T * u - T * Real.log 2) := by
        rw [div_eq_iff hlz0.ne']
        ring
      rw [h1, hTu]
    have hWb : taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2) * mBand z₁ z
        ≤ taylorWindowW (2 * (1 - q) * splitST2 ulo)
          * (Real.log z / (u - Real.log 2) * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091)) :=
      mul_le_mul hW hM hmB0 (le_trans hW0 hW)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hTlog : T * Real.log 2 ≤ 3 / 2 / ulo * Real.log 2 :=
      mul_le_mul_of_nonneg_right hTlo hlog2'.le
    calc taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
          + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2) * mBand z₁ z
          * (Real.pi * (3 / 2 - 3 / 2 / ulo * Real.log 2))
        ≤ taylorWindowW (2 * (1 - q) * splitST2 ulo)
          * (Real.log z / (u - Real.log 2) * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091))
          * (Real.pi * (3 / 2 - T * Real.log 2)) :=
          mul_le_mul hWb (mul_le_mul_of_nonneg_left (by linarith) hpi.le)
            (by positivity) (mul_nonneg (le_trans hW0 hW) (by positivity))
      _ = taylorWindowW (2 * (1 - q) * splitST2 ulo)
          * Real.exp (9.0028 / (ulo - Real.log 2) + 0.0091) * (Real.pi * T * Real.log z) := by
          rw [← heq]
          field_simp
  have hin0 : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2)
        * mBand z₁ z / (Real.pi * T * Real.log z) := by
    have hmB0 : 0 ≤ mBand z₁ z := by rw [mBand]; positivity
    positivity
  rw [winSplitFull]
  exact mul_le_mul hPF (Real.rpow_le_rpow hin0 hinner hq0') (Real.rpow_nonneg hin0 _)
    (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le)

/-- The bottom's window without a split, from below in height: for `T ≥ T_lo > 0` and
`log z ≥ 1000`, `RMF.winNoSplitFull q T z ≤ ((e-1)e^{0.2732}/(πT_lo))^q`. -/
lemma winNoSplitFull_le_of_le {q T Tlo : ℝ} {z : ℕ} (hq0 : 0 ≤ q) (hTlo : 0 < Tlo)
    (hT : Tlo ≤ T) (hlz : 1000 ≤ Real.log z) :
    winNoSplitFull q T z ≤ ((Real.exp 1 - 1) * Real.exp 0.2732 / (Real.pi * Tlo)) ^ q := by
  have hlz0 : 0 < Real.log z := by linarith
  have hT0 : 0 < T := by linarith
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [winNoSplitFull]
  refine Real.rpow_le_rpow (by rw [mFull]; positivity) ?_ hq0
  have hM : mFull z ≤ Real.log z * Real.exp 0.2732 := by
    rw [mFull]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hlz0.le
    have : 9.0028 / Real.log z ≤ 0.0091 := by rw [div_le_iff₀ hlz0]; linarith
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpi := Real.pi_pos
  calc (Real.exp 1 - 1) * mFull z * (Real.pi * Tlo)
      ≤ (Real.exp 1 - 1) * (Real.log z * Real.exp 0.2732) * (Real.pi * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hM he1) (mul_le_mul_of_nonneg_left hT hpi.le)
          (by positivity) (by positivity)
    _ = (Real.exp 1 - 1) * Real.exp 0.2732 * (Real.pi * T * Real.log z) := by ring

/-- The bottom's `k`-th window height at `θ = 1`, `T_m = 2`: `2e^{-k} ≤ T_k < 2e^{1-k}`. -/
lemma bottomT_mem {z : ℕ} (hlz : 1 ≤ Real.log z) (k : ℕ) :
    2 * Real.exp (-(k : ℝ)) ≤ bottomT 1 2 z k ∧ bottomT 1 2 z k < 2 * Real.exp (1 - k) := by
  have hlz0 : 0 < Real.log z := by linarith
  have h2 : 0 ≤ Real.log (2 * Real.log z / 1) := by
    rw [div_one]
    exact Real.log_nonneg (by linarith)
  have hJ1 : Real.log (2 * Real.log z / 1) ≤ (bottomJ 1 2 z : ℝ) := by
    rw [bottomJ]; exact Nat.le_ceil _
  have hJ2 : (bottomJ 1 2 z : ℝ) < Real.log (2 * Real.log z / 1) + 1 := by
    rw [bottomJ]; exact Nat.ceil_lt_add_one h2
  rw [div_one] at hJ1 hJ2
  have hT : bottomT 1 2 z k = Real.exp ((bottomJ 1 2 z : ℝ) - k) / Real.log z := by
    rw [bottomT, show Real.log (1 / Real.log z) + (bottomJ 1 2 z : ℝ) - k
        = Real.log (1 / Real.log z) + ((bottomJ 1 2 z : ℝ) - k) by ring, Real.exp_add,
      Real.exp_log (by positivity)]
    field_simp
  rw [hT]
  have hlog : Real.log (2 * Real.log z) = Real.log 2 + Real.log (Real.log z) :=
    Real.log_mul (by norm_num) hlz0.ne'
  constructor
  · rw [le_div_iff₀ hlz0]
    have : Real.exp (Real.log (2 * Real.log z) - k) ≤ Real.exp ((bottomJ 1 2 z : ℝ) - k) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_sub, Real.exp_log (by positivity)] at this
    rw [Real.exp_neg]
    calc 2 * (Real.exp k)⁻¹ * Real.log z = 2 * Real.log z / Real.exp k := by ring
      _ ≤ _ := this
  · rw [div_lt_iff₀ hlz0]
    have : Real.exp ((bottomJ 1 2 z : ℝ) - k) < Real.exp (Real.log (2 * Real.log z) + 1 - k) :=
      Real.exp_lt_exp.2 (by linarith)
    rw [show Real.log (2 * Real.log z) + 1 - k = Real.log (2 * Real.log z) + (1 - k) by ring,
      Real.exp_add, Real.exp_log (by positivity)] at this
    calc Real.exp ((bottomJ 1 2 z : ℝ) - k) < 2 * Real.log z * Real.exp (1 - k) := this
      _ = 2 * Real.exp (1 - k) * Real.log z := by ring

/-- **A split window of the bottom, cleaned**: for `3/2/T = u ∈ [1000, log z]`,
`RMF.winSplitFull q T (splitPt (3/2) T 2 z) z ≤ u^a·pfC1 q·ω(q)`. -/
lemma winSplitFull_le_clean {q T : ℝ} {z : ℕ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T)
    (hu : 1000 ≤ 3 / 2 / T) (huz : 3 / 2 / T ≤ Real.log z) :
    winSplitFull q T (splitPt (3 / 2) T 2 z) z
      ≤ (3 / 2 / T) ^ (q * (2 * q - 1)) * pfC1 q * omegaClean q := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  set u := 3 / 2 / T with hudef
  refine le_trans (winSplitFull_le_range hq0 hq1 hT le_rfl le_rfl (by linarith) huz
    (by linarith)) ?_
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < u - Real.log 2 := by linarith
  have hinv : 9.0028 / (u - Real.log 2) ≤ 0.00901 := by
    rw [div_le_iff₀ hden]; linarith
  -- the (PF) constant
  have h1 : Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / (u - Real.log 2) + (2 - 2 * q) / 3))
      ≤ pfC1 q := by
    rw [pfC1]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) ha)
  -- the window
  have hST : splitST2 u ≤ 1.165 := by
    have := splitST2_anti (by norm_num : (0 : ℝ) < 1000) hu
    refine le_trans this ?_
    rw [splitST2]
    norm_num
  have hW : taylorWindowW (2 * (1 - q) * splitST2 u) ≤ taylorWindowW ((1 - q) * 2.33) :=
    taylorWindowW_mono (by nlinarith)
  have hW0 : 0 ≤ taylorWindowW (2 * (1 - q) * splitST2 u) := by
    refine taylorWindowW_nonneg (mul_nonneg (by linarith) ?_)
    rw [splitST2]
    have : 0 < u := by linarith
    positivity
  have hd : Real.pi * 1.498 ≤ Real.pi * (3 / 2 - 3 / 2 / u * Real.log 2) := by
    have h3 : 3 / 2 / u ≤ 0.0015 := three_halves_div_le hu
    have h4 : 3 / 2 / u * Real.log 2 ≤ 0.0015 * 0.6932 :=
      mul_le_mul h3 (by linarith) hlog2'.le (by norm_num)
    have := Real.pi_pos
    nlinarith
  have hinner : taylorWindowW (2 * (1 - q) * splitST2 u)
      * Real.exp (9.0028 / (u - Real.log 2) + 0.0091)
      / (Real.pi * (3 / 2 - 3 / 2 / u * Real.log 2))
      ≤ taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498) * Real.exp 0.0185 := by
    have hpi := Real.pi_pos
    rw [div_le_iff₀ (by linarith), div_mul_eq_mul_div, mul_div_assoc]
    have he : Real.exp (9.0028 / (u - Real.log 2) + 0.0091) ≤ Real.exp 0.0185 :=
      Real.exp_le_exp.2 (by linarith)
    have hWb : 0 ≤ taylorWindowW ((1 - q) * 2.33) := le_trans hW0 hW
    have hr : 1 ≤ (Real.pi * (3 / 2 - 3 / 2 / u * Real.log 2)) / (Real.pi * 1.498) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc taylorWindowW (2 * (1 - q) * splitST2 u) * Real.exp (9.0028 / (u - Real.log 2) + 0.0091)
        ≤ taylorWindowW ((1 - q) * 2.33) * Real.exp 0.0185 :=
          mul_le_mul hW he (Real.exp_pos _).le hWb
      _ ≤ taylorWindowW ((1 - q) * 2.33) * Real.exp 0.0185
          * ((Real.pi * (3 / 2 - 3 / 2 / u * Real.log 2)) / (Real.pi * 1.498)) :=
          le_mul_of_one_le_right (by positivity) hr
      _ = _ := by ring
  have hin0 : 0 ≤ taylorWindowW (2 * (1 - q) * splitST2 u)
      * Real.exp (9.0028 / (u - Real.log 2) + 0.0091)
      / (Real.pi * (3 / 2 - 3 / 2 / u * Real.log 2)) := by
    have : 0 < 3 / 2 - 3 / 2 / u * Real.log 2 := by
      have h3 : 3 / 2 / u ≤ 0.0015 := three_halves_div_le hu
      nlinarith
    have := Real.pi_pos
    positivity
  have hWb : 0 ≤ taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498) :=
    div_nonneg (le_trans hW0 hW) (by positivity)
  have hpow := Real.rpow_le_rpow hin0 hinner hq0'
  rw [Real.mul_rpow hWb (Real.exp_pos _).le, ← Real.exp_mul] at hpow
  have hom : (taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498)) ^ q
      * Real.exp (0.0185 * q) ≤ omegaClean q := by
    rw [omegaClean]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hWb _)
    nlinarith
  have hu0 : 0 ≤ u ^ (q * (2 * q - 1)) := Real.rpow_nonneg (by linarith) _
  calc u ^ (q * (2 * q - 1))
        * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / (u - Real.log 2) + (2 - 2 * q) / 3))
        * (taylorWindowW (2 * (1 - q) * splitST2 u)
          * Real.exp (9.0028 / (u - Real.log 2) + 0.0091)
          / (Real.pi * (3 / 2 - 3 / 2 / u * Real.log 2))) ^ q
      ≤ u ^ (q * (2 * q - 1)) * pfC1 q
        * ((taylorWindowW ((1 - q) * 2.33) / (Real.pi * 1.498)) ^ q * Real.exp (0.0185 * q)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hu0) hpow (Real.rpow_nonneg hin0 _)
          (mul_nonneg hu0 (Real.exp_pos _).le)
    _ ≤ u ^ (q * (2 * q - 1)) * pfC1 q * omegaClean q :=
        mul_le_mul_of_nonneg_left hom (mul_nonneg hu0 (Real.exp_pos _).le)

lemma sum_range_pow_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ (n - k) ≤ r / (1 - r) := by
  have hrefl : ∑ k ∈ Finset.range n, r ^ (n - k) = ∑ j ∈ Finset.range n, r ^ (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => r ^ (j + 1)) n]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show n - 1 - k + 1 = n - k by omega]
  have hgeom : ∑ j ∈ Finset.range n, r ^ (j + 1) = r * ((1 - r ^ n) / (1 - r)) := by
    have hne : r ≠ 1 := ne_of_lt hr1
    have h2 : (1 - r ^ n) / (1 - r) = (r ^ n - 1) / (r - 1) := by
      rw [← neg_div_neg_eq]
      ring_nf
    rw [h2, ← geom_sum_eq hne n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrefl, hgeom]
  have h1r : 0 < 1 - r := by linarith
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hr0 (by
    have := pow_nonneg hr0 n; linarith)) h1r.le

lemma exp_eight_bounds : 2500 ≤ Real.exp 8 ∧ Real.exp 8 < 2981 := by
  have h1 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  constructor
  · calc (2500 : ℝ) ≤ 2.7182818283 ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
  · calc Real.exp 1 ^ 8 < 2.7182818286 ^ 8 :=
          pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
      _ < 2981 := by norm_num

lemma exp_neg_eight_le : Real.exp (-8) ≤ 0.0004 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 8) (by norm_num)]
  have := exp_eight_bounds.1
  linarith

lemma rpow_atom_le_of {q V M B : ℝ} (hq : 0 ≤ q) (hM0 : 0 ≤ M) (hM : M ≤ B) :
    (Real.exp (-V) * M ^ Real.exp 1) ^ q ≤ Real.exp (-(q * V)) * B ^ (Real.exp 1 * q) := by
  rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hM0 _), ← Real.exp_mul,
    ← Real.rpow_mul hM0]
  refine mul_le_mul (le_of_eq (by ring_nf)) (Real.rpow_le_rpow hM0 hM
    (mul_nonneg (Real.exp_pos 1).le hq)) (Real.rpow_nonneg hM0 _) (Real.exp_pos _).le

/-- **The bottom level above `½` with supplied windows, cleaned.**  For `½ < q ≤ 1`,
`η', ε > 0`, `2 ≤ z ≤ x` with `log z ≥ 1500`, `log x ≥ 50000`, the sieve level
`⌊z/(log x)^7⌋ ≥ 2`, the truncation bound's constant `≤ K_c` and its error `≤ E_c`, the bottom
level at `θ = 1`, `c_s = 3/2`, `T_m = 2` is at most

`log^a z·pfC1·(K_c^q(cen^q + ((1+1/η')/π)^q) + (K_c/(1000 log²x))^q)
  + e^{-qV}(e^{0.2732} log z)^{eq} + E_c^q
  + K_c^q(1+η')^q(∑_{k<9} min(window k) + (e^{0.2732}/(2π))^q)
  + K_c^q(1+η')^q·pfC1·ω·1.5^a·e^{-a}/(1-e^{-a})·log^a z`:

the nine top windows are left as they are, the rest `∑_{9≤k<J} w k ≤ W_B` supplied in place of
the last term's `pfC1·ω·1.5^a e^{-a}/(1-e^{-a})·log^a z`. -/
theorem bottomLevelW_le_clean {q η' ε x Kc Ec WB : ℝ} {z : ℕ} {w : ℕ → ℝ} (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hz : 2 ≤ z) (hzx : (z : ℝ) ≤ x)
    (hlz : 1500 ≤ Real.log z) (hlx : 50000 ≤ Real.log x) (hz' : 2 ≤ sieveLevel x z)
    (hK : lemmaTConst z (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε * Real.exp (2 * (Real.log x)⁻¹)
      ≤ Kc)
    (hE : smallQReductionErr x (sieveLevel x z) (Real.log x ^ 2)⁻¹ ε ≤ Ec)
    (hw0 : ∀ k, 0 ≤ w k) (hTail : ∑ k ∈ Finset.Ico 9 (bottomJ 1 2 z), w k ≤ WB) :
    bottomLevelW q 1 η' ε 2 x z w
      ≤ Real.log z ^ (q * (2 * q - 1)) * (pfC1 q
          * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
            + (Kc / (1000 * Real.log x ^ 2)) ^ q))
        + (Real.exp (-(q * (Real.log x / Real.log z)))
            * (Real.log z * Real.exp 0.2732) ^ (Real.exp 1 * q) + Ec ^ q)
        + Kc ^ q * (1 + η') ^ q * (∑ k ∈ Finset.range 9, w k
          + (Real.exp 0.2732 / (2 * Real.pi)) ^ q)
        + Kc ^ q * (1 + η') ^ q * WB := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha' : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have ha : 0 ≤ q * (2 * q - 1) := ha'.le
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz0 : 0 < Real.log z := by linarith
  have hx0 : 0 < x := by linarith
  have hlzx : Real.log z ≤ Real.log x := Real.log_le_log (by linarith) hzx
  set lx := Real.log x with hlxdef
  set σ := (lx ^ 2)⁻¹ with hσdef
  have hσ : 0 < σ := by positivity
  set z' := sieveLevel x z with hz'def
  have hz'z : z' ≤ z := by
    rw [hz'def, sieveLevel]
    refine Nat.floor_le_of_le ?_
    exact div_le_self (by positivity) (one_le_pow₀ (by linarith))
  set LT := lemmaTConst z z' σ ε with hLTdef
  have hLT0 : 0 < LT := lemmaTConst_pos hz' hz'z hσ hε
  have hLTK : LT ≤ Kc := le_trans (le_mul_of_one_le_right hLT0.le
    (Real.one_le_exp (by positivity))) hK
  have hKc0 : 0 ≤ Kc := le_trans hLT0.le hLTK
  set a := q * (2 * q - 1) with hadef
  set P := pfFull q z with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef, pfFull]; positivity
  have hPle : P ≤ Real.log z ^ a * pfC1 q := pfFull_le_pfC1 hq0.le (by linarith)
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hlza0 : 0 ≤ Real.log z ^ a := Real.rpow_nonneg hlz0.le _
  have hmF : mFull z ≤ Real.log z * Real.exp 0.2732 := by
    rw [mFull]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hlz0.le
    have : 9.0028 / Real.log z ≤ 0.0091 := by rw [div_le_iff₀ hlz0]; linarith
    linarith
  have hmF0 : 0 ≤ mFull z := by rw [mFull]; positivity
  -- (i) the atom
  have hi := rpow_atom_le_of (V := lx / Real.log z) hq0' hmF0 hmF
  -- (ii) the first error
  have hσlz : σ / Real.log z ≤ 1 / (1000 * lx ^ 2) := by
    rw [hσdef, div_le_div_iff₀ hlz0 (by positivity),
      show (lx ^ 2)⁻¹ * (1000 * lx ^ 2) = 1000 by field_simp]
    linarith
  have hii : (LT * (σ / Real.log z)) ^ q * P
      ≤ Real.log z ^ a * (pfC1 q * (Kc / (1000 * lx ^ 2)) ^ q) := by
    have h1 : (LT * (σ / Real.log z)) ^ q ≤ (Kc / (1000 * lx ^ 2)) ^ q := by
      refine Real.rpow_le_rpow (by positivity) ?_ hq0'
      calc LT * (σ / Real.log z) ≤ Kc * (1 / (1000 * lx ^ 2)) :=
            mul_le_mul hLTK hσlz (by positivity) hKc0
        _ = Kc / (1000 * lx ^ 2) := by ring
    calc (LT * (σ / Real.log z)) ^ q * P
        ≤ (Kc / (1000 * lx ^ 2)) ^ q * (Real.log z ^ a * pfC1 q) :=
          mul_le_mul h1 hPle hP0 (Real.rpow_nonneg (by positivity) _)
      _ = _ := by ring
  -- the windows
  set J := bottomJ 1 2 z with hJdef
  have hJ1 : Real.log (2 * Real.log z) ≤ (J : ℝ) := by
    have := Nat.le_ceil (Real.log (2 * Real.log z / 1))
    rw [div_one] at this
    rw [hJdef, bottomJ]
    simpa using this
  have hJ9 : 9 ≤ J := by
    have h8 : (8 : ℝ) < Real.log (2 * Real.log z) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := exp_eight_bounds.2
      linarith
    have : (8 : ℝ) < J := lt_of_lt_of_le h8 hJ1
    exact_mod_cast this
  have heJ : 2 * Real.log z ≤ Real.exp J := by
    calc 2 * Real.log z = Real.exp (Real.log (2 * Real.log z)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp J := Real.exp_le_exp.2 hJ1
  have hfar : (mFull z / (Real.pi * 1 * Real.exp J)) ^ q
      ≤ (Real.exp 0.2732 / (2 * Real.pi)) ^ q := by
    refine Real.rpow_le_rpow (by positivity) ?_ hq0'
    rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpi := Real.pi_pos
    have h1 : mFull z * (2 * Real.pi) ≤ Real.log z * Real.exp 0.2732 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hmF (by positivity)
    have h2 : Real.exp 0.2732 * (Real.pi * (2 * Real.log z))
        ≤ Real.exp 0.2732 * (Real.pi * Real.exp J) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heJ hpi.le) (Real.exp_pos _).le
    nlinarith
  set f : ℕ → ℝ := w with hfdef
  have hsplit : (∑ k ∈ Finset.range J, f k)
      = (∑ k ∈ Finset.range 9, f k) + ∑ k ∈ Finset.Ico 9 J, f k :=
    (Finset.sum_range_add_sum_Ico f hJ9).symm
  have htail : ∑ k ∈ Finset.Ico 9 J, f k ≤ WB := hTail
  -- (iii) the main term
  have hK0 : 0 ≤ LT * Real.exp (2 * lx⁻¹) := by positivity
  have hKq : (LT * Real.exp (2 * lx⁻¹)) ^ q ≤ Kc ^ q := Real.rpow_le_rpow hK0 hK hq0'
  have hcen : cenBand q σ (1 / Real.log z) z ^ q ≤ cenClean q ^ q :=
    Real.rpow_le_rpow (cenBand_nonneg hq1 (by positivity) hlz0)
      (cenBand_le_clean hq0.le hq1 (by linarith) hlzx hlx) hq0'
  have hcen0 : 0 ≤ cenBand q σ (1 / Real.log z) z ^ q :=
    Real.rpow_nonneg (cenBand_nonneg hq1 (by positivity) hlz0) _
  have hcoh0 : 0 ≤ ((1 + 1 / η') / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
  have hcoh : ((1 + 1 / η') / (Real.pi * 1)) ^ q = ((1 + 1 / η') / Real.pi) ^ q := by
    rw [mul_one]
  have hη'q : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
  have hf0 : ∀ k, 0 ≤ f k := hw0
  have hS9 : 0 ≤ ∑ k ∈ Finset.range 9, f k := Finset.sum_nonneg fun k _ => hf0 k
  have hmain : (LT * Real.exp (2 * lx⁻¹)) ^ q
      * (cenBand q σ (1 / Real.log z) z ^ q * P + ((1 + 1 / η') / (Real.pi * 1)) ^ q * P
        + (1 + η') ^ q * ((∑ k ∈ Finset.range J, f k)
          + (mFull z / (Real.pi * 1 * Real.exp J)) ^ q))
      ≤ Real.log z ^ a * (pfC1 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)))
        + Kc ^ q * (1 + η') ^ q * ((∑ k ∈ Finset.range 9, f k)
          + (Real.exp 0.2732 / (2 * Real.pi)) ^ q)
        + Kc ^ q * (1 + η') ^ q * WB := by
    rw [hcoh, hsplit]
    have hinner : cenBand q σ (1 / Real.log z) z ^ q * P + ((1 + 1 / η') / Real.pi) ^ q * P
        + (1 + η') ^ q * ((∑ k ∈ Finset.range 9, f k) + (∑ k ∈ Finset.Ico 9 J, f k)
          + (mFull z / (Real.pi * 1 * Real.exp J)) ^ q)
        ≤ (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q) * (Real.log z ^ a * pfC1 q)
          + (1 + η') ^ q * ((∑ k ∈ Finset.range 9, f k)
            + WB
            + (Real.exp 0.2732 / (2 * Real.pi)) ^ q) := by
      have e1 : cenBand q σ (1 / Real.log z) z ^ q * P + ((1 + 1 / η') / Real.pi) ^ q * P
          = (cenBand q σ (1 / Real.log z) z ^ q + ((1 + 1 / η') / Real.pi) ^ q) * P := by ring
      rw [e1]
      refine add_le_add (mul_le_mul (by linarith) hPle hP0 (add_nonneg (le_trans hcen0 hcen)
        hcoh0)) (mul_le_mul_of_nonneg_left ?_ hη'q)
      linarith
    have hinner0 : 0 ≤ cenBand q σ (1 / Real.log z) z ^ q * P + ((1 + 1 / η') / Real.pi) ^ q * P
        + (1 + η') ^ q * ((∑ k ∈ Finset.range 9, f k) + (∑ k ∈ Finset.Ico 9 J, f k)
          + (mFull z / (Real.pi * 1 * Real.exp J)) ^ q) := by
      have hS : 0 ≤ ∑ k ∈ Finset.Ico 9 J, f k := Finset.sum_nonneg fun k _ => hf0 k
      have : 0 ≤ (mFull z / (Real.pi * 1 * Real.exp J)) ^ q :=
        Real.rpow_nonneg (by positivity) _
      positivity
    refine le_trans (mul_le_mul hKq hinner hinner0 (Real.rpow_nonneg hKc0 _)) (le_of_eq ?_)
    ring
  -- (iv) the second error
  have hErr0 : 0 ≤ smallQReductionErr x z' σ ε :=
    smallQReductionErr_nonneg hε (by linarith) hx0.le (by omega)
  have hiv : smallQReductionErr x z' σ ε ^ q ≤ Ec ^ q := Real.rpow_le_rpow hErr0 hE hq0'
  -- assembly
  have hlev : bottomLevelW q 1 η' ε 2 x z w
      = (Real.exp (-(lx / Real.log z)) * mFull z ^ Real.exp 1) ^ q
        + (LT * (σ / Real.log z)) ^ q * P
        + (LT * Real.exp (2 * lx⁻¹)) ^ q
          * (cenBand q σ (1 / Real.log z) z ^ q * P + ((1 + 1 / η') / (Real.pi * 1)) ^ q * P
            + (1 + η') ^ q * ((∑ k ∈ Finset.range J, f k)
              + (mFull z / (Real.pi * 1 * Real.exp J)) ^ q))
        + smallQReductionErr x z' σ ε ^ q := by
    rw [bottomLevelW]
  rw [hlev]
  refine le_trans (add_le_add (add_le_add (add_le_add hi hii) hmain) hiv) (le_of_eq ?_)
  ring

/-- **The bottom's Jensen windows, cleaned**: for `½ < q ≤ 1`, `2 ≤ z` with `log z ≥ 1500`, the
windows of `RMF.bottomLevel` at `θ = 1`, `T_m = 2`, `c_s = 3/2` are nonnegative and those past the
ninth sum to at most `pfC1·ω·1.5^a e^{-a}/(1-e^{-a})·log^a z`. -/
theorem bottomWindows_jensen_clean {q : ℝ} {z : ℕ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hz : 2 ≤ z)
    (hlz : 1500 ≤ Real.log z) :
    (∀ k, 0 ≤ min (winNoSplitFull q (bottomT 1 2 z k) z)
      (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z))
    ∧ ∑ k ∈ Finset.Ico 9 (bottomJ 1 2 z), min (winNoSplitFull q (bottomT 1 2 z k) z)
        (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z)
      ≤ pfC1 q * omegaClean q * (3 / 2) ^ (q * (2 * q - 1))
        * (Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1)))))
        * Real.log z ^ (q * (2 * q - 1)) := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha' : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz0 : 0 < Real.log z := by linarith
  have hmF0 : 0 ≤ mFull z := by rw [mFull]; positivity
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have ha : 0 ≤ q * (2 * q - 1) := ha'.le
  set a := q * (2 * q - 1) with hadef
  -- the windows
  set J := bottomJ 1 2 z with hJdef
  have hJ1 : Real.log (2 * Real.log z) ≤ (J : ℝ) := by
    have := Nat.le_ceil (Real.log (2 * Real.log z / 1))
    rw [div_one] at this
    rw [hJdef, bottomJ]
    simpa using this
  have hJ9 : 9 ≤ J := by
    have h8 : (8 : ℝ) < Real.log (2 * Real.log z) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := exp_eight_bounds.2
      linarith
    have : (8 : ℝ) < J := lt_of_lt_of_le h8 hJ1
    exact_mod_cast this
  have heJ : 2 * Real.log z ≤ Real.exp J := by
    calc 2 * Real.log z = Real.exp (Real.log (2 * Real.log z)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp J := Real.exp_le_exp.2 hJ1
  set f : ℕ → ℝ := fun k => min (winNoSplitFull q (bottomT 1 2 z k) z)
    (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z) with hfdef
  set r := Real.exp (-a) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hω : 0 ≤ omegaClean q := by
    rw [omegaClean]
    have : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
      taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
    positivity
  have hT : ∀ k : ℕ, bottomT 1 2 z k = Real.exp ((J : ℝ) - k) / Real.log z := by
    intro k
    rw [bottomT, ← hJdef, show Real.log (1 / Real.log z) + (J : ℝ) - k
        = Real.log (1 / Real.log z) + ((J : ℝ) - k) by ring, Real.exp_add,
      Real.exp_log (by positivity)]
    field_simp
  have htail : ∑ k ∈ Finset.Ico 9 J, f k
      ≤ pfC1 q * omegaClean q * (3 / 2) ^ a * (r / (1 - r)) * Real.log z ^ a := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range (J - 9), f (9 + i)
        ≤ (3 / 2 * Real.log z) ^ a * pfC1 q * omegaClean q * r ^ ((J - 9) - i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      refine le_trans (min_le_right _ _) ?_
      have hk9 : 9 ≤ 9 + i := by omega
      have hTk := bottomT_mem (z := z) (by linarith) (9 + i)
      have hTpos : 0 < bottomT 1 2 z (9 + i) := lt_of_lt_of_le (by positivity) hTk.1
      have hTsmall : bottomT 1 2 z (9 + i) ≤ 0.0015 := by
        refine le_trans hTk.2.le ?_
        have h1 : Real.exp (1 - ((9 + i : ℕ) : ℝ)) ≤ Real.exp (-8) :=
          Real.exp_le_exp.2 (by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
        have h2 := exp_neg_eight_le
        linarith
      have hu1000 : 1000 ≤ 3 / 2 / bottomT 1 2 z (9 + i) := by
        rw [le_div_iff₀ hTpos]; linarith
      have huz : 3 / 2 / bottomT 1 2 z (9 + i) ≤ Real.log z := by
        rw [hT (9 + i), div_div_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
        have h1 : (1 : ℝ) ≤ (J : ℝ) - ((9 + i : ℕ) : ℝ) := by
          have : ((9 + i + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : 9 + i + 1 ≤ J)
          push_cast at this ⊢
          linarith
        have h2 : Real.exp 1 ≤ Real.exp ((J : ℝ) - ((9 + i : ℕ) : ℝ)) := Real.exp_le_exp.2 h1
        have h3 := Real.exp_one_gt_d9
        have h4 := mul_le_mul_of_nonneg_left
          (show (3 / 2 : ℝ) ≤ Real.exp ((J : ℝ) - ((9 + i : ℕ) : ℝ)) by linarith) hlz0.le
        linarith
      refine le_trans (winSplitFull_le_clean hq0.le hq1 hTpos hu1000 huz) (le_of_eq ?_)
      rw [hT (9 + i), div_div_eq_mul_div, ← hadef]
      have hm : ((J : ℕ) : ℝ) - ((9 + i : ℕ) : ℝ) = (((J - 9 - i : ℕ) : ℝ)) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hm, div_exp_rpow (by positivity), hrdef, ← Real.exp_nat_mul]
      ring_nf
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hgeo := sum_range_pow_sub_le hr0 hr1 (J - 9)
    have hc : 0 ≤ (3 / 2 * Real.log z) ^ a * pfC1 q * omegaClean q := by positivity
    calc (3 / 2 * Real.log z) ^ a * pfC1 q * omegaClean q
          * ∑ i ∈ Finset.range (J - 9), r ^ (J - 9 - i)
        ≤ (3 / 2 * Real.log z) ^ a * pfC1 q * omegaClean q * (r / (1 - r)) :=
          mul_le_mul_of_nonneg_left hgeo hc
      _ = _ := by
          rw [Real.mul_rpow (by norm_num) hlz0.le]
          ring
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    rw [hfdef]
    have hT0 : 0 ≤ bottomT 1 2 z k := by rw [bottomT]; positivity
    refine le_min ?_ ?_
    · rw [winNoSplitFull]
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact Real.rpow_nonneg (div_nonneg (mul_nonneg he1 hmF0)
        (mul_nonneg (mul_nonneg Real.pi_pos.le hT0) hlz0.le)) _
    · rw [winSplitFull, pfFull]
      have : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((splitPt (3 / 2) (bottomT 1 2 z k)
          2 z + 1 : ℕ) : ℝ) ^ 2 / 2 + 15.003 * Real.log ((splitPt (3 / 2) (bottomT 1 2 z k) 2 z
          + 1 : ℕ) : ℝ) + 34) * bottomT 1 2 z k ^ 2) := by
        refine taylorWindowW_nonneg ?_
        have : 0 ≤ Real.log ((splitPt (3 / 2) (bottomT 1 2 z k) 2 z + 1 : ℕ) : ℝ) :=
          Real.log_natCast_nonneg _
        have : 0 ≤ 1 - q := by linarith
        positivity
      have : 0 ≤ mBand (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z := by rw [mBand]; positivity
      have : 0 ≤ Real.log (splitPt (3 / 2) (bottomT 1 2 z k) 2 z : ℝ) :=
        Real.log_natCast_nonneg _
      positivity
  refine ⟨hf0, le_trans htail (le_of_eq ?_)⟩
  rw [hrdef, hadef]

end RMF
