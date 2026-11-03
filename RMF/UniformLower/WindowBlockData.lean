/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.WindowCosine
import RMF.NumberTheory.MertensBlockCosine
import RMF.Probability.RademacherBlockComparisonMixed
import RMF.Weighted.HalfEvents

/-!
# The window's block data

The block statistics of the one-point step HP1: under the tilt by `|F_y(s₁)|²` at
`s₁ = ½+σ+ih`, the height block at `s₁` and the real block at `s₂ = ½+σ`, over
`B_m = RMF.primeBlockSub θ m`, in terms of `S_m = RMF.blockRpowSum θ σ m`,
`c_m = RMF.blockCosSum θ σ h m` and `C_m = RMF.blockCosSum θ σ (2h) m`.

* **Closed forms** (any `h`, `σ ≥ 0`, `m + θ ≥ 20`, within `10⁻²⁰`): height variance
  `(S_m + C_m)/2`, real variance `S_m`, covariance `c_m`, real mean `2c_m − S_m/2`, height mean
  `S_m + C_m/2`.  Past offset `20` every local variable is below `10⁻⁴⁰`.
* **The cosine sums, two regimes** (any `θ`, `m + θ ≥ 0`): `C_m(τ)` is its damped log-integral
  up to `RMF.blockCosErr θ m τ`, explicit Mertens' `2Ke^{-(m+θ)} + Kτ` below scale `104` and the
  prime number theorem's `(τ+1)/10²⁸` from it; at most `7.43·10⁻⁸` on the window from `k ≥ 20`.
* **Window numerics** (`θ = k ≥ 20`, `h ∈ RMF.halfWindow k`): `c₀, …, c₃`, `C₀, C₁, C₂` in the
  ranges of `RMF/UniformLower/WindowCosine.lean` widened by `0.01` (for `σe^{k+5} ≤ 1/200`),
  `|c_m|, |C_m| ≤ 3e^{1-m} + RMF.blockCosErr` for every block, and `S_m ∈ [0.99, 1.01]` for every
  block with `σe^{k+m+1} ≤ 1/200`.
* **The comparison's inputs** (`RMF.window_block_comparison_inputs_det`, `k ≥ 20`): both
  variances in `[1/100, 10]`, determinant `≥ RMF.windowBlockDet m` (`1.67·10⁻⁴`, `7.76·10⁻⁴`,
  `0.23` on blocks `0, 1, 2`, `0.12` beyond), means at most `1.52` (height) and `2.03` (real).  The
  determinant's main term is `S_m` times the weighted variance of `cos(h log p)`, bounded below by
  two phase windows on blocks `0`, `1` (`RMF.le_blockVariance_of_phases`).
-/

open MeasureTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The block sums -/

/-- **The block's Mertens sum** `S_m = ∑_{p∈B_m} p^{-1-2σ}`. -/
noncomputable def blockRpowSum (θ σ : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)

/-- **The block's cosine sum** `∑_{p∈B_m} cos(τ log p)p^{-1-2σ}`: `c_m` at `τ = h`, `C_m` at
`τ = 2h`. -/
noncomputable def blockCosSum (θ σ τ : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ primeBlockSub θ m, Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)

lemma blockRpowSum_nonneg (θ σ : ℝ) (m : ℕ) : 0 ≤ blockRpowSum θ σ m :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `|c_m| ≤ S_m`: the cosine is at most `1`. -/
theorem abs_blockCosSum_le_blockRpowSum (θ σ τ : ℝ) (m : ℕ) :
    |blockCosSum θ σ τ m| ≤ blockRpowSum θ σ m := by
  unfold blockCosSum blockRpowSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have hw : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_left hw (Real.abs_cos_le_one _)

/-- `S_m ≤ 1 + 1/150000` for `σ ≥ 0` and `m + θ ≥ 16`
(`RMF.sum_norm_sq_primeBlockSub_bounds_sharp`). -/
lemma blockRpowSum_le {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 16 ≤ (m : ℝ) + θ) :
    blockRpowSum θ σ m ≤ 1 + 1 / 150000 := by
  have hS : blockRpowSum θ σ m
      = ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => (norm_sq_prime_cpow_neg p (re_shiftLine σ 0)).symm
  rw [hS]
  exact (sum_norm_sq_primeBlockSub_bounds_sharp (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    hm hσ le_rfl fun p _ => norm_sq_prime_cpow_neg p (re_shiftLine σ 0)).2

/-! ### The weights past offset `20` -/

/-- `10⁸⁰ ≤ e^{e^{20}}`. -/
lemma pow_eighty_le_exp_exp_20 : (10 : ℝ) ^ 80 ≤ Real.exp (Real.exp 20) := by
  have h1 : (200 : ℝ) ≤ Real.exp 20 := by
    have h := Real.quadratic_le_exp_of_nonneg (x := 20) (by norm_num)
    norm_num at h
    linarith
  have h2 : (10 : ℝ) ^ 80 ≤ Real.exp 200 := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 200) (by norm_num) he (by norm_num)
  exact h2.trans (Real.exp_le_exp.2 h1)

/-- **Past offset `20` every weight is below `10⁻⁸⁰`**: `p^{-1-2σ} ≤ 1/p < e^{-e^{20}}` for
`σ ≥ 0`. -/
lemma rpow_le_of_mem_primeBlockSub {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) :
    ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ 1 / 10 ^ 80 := by
  rw [mem_primeBlockSub] at hp
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hbig : (10 : ℝ) ^ 80 ≤ ((p : ℕ) : ℝ) := by
    refine le_trans ?_ hp.1.le
    rw [blockScale]
    exact pow_eighty_le_exp_exp_20.trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 hm))
  calc ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / ((p : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 10 ^ 80 := one_div_le_one_div_of_le (by positivity) hbig

/-- **…so every local variable is below `10⁻⁴⁰`**: `‖p^{-s}‖ ≤ 10⁻⁴⁰` at `Re s = ½ + σ`. -/
lemma norm_cpow_le_of_mem_primeBlockSub {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hm : 20 ≤ (m : ℝ) + θ) {s : ℂ} (hres : s.re = 1 / 2 + σ) {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 10 ^ 40 := by
  have h := rpow_le_of_mem_primeBlockSub hσ hm hp
  rw [← norm_sq_prime_cpow_neg p hres,
    show (1 : ℝ) / 10 ^ 80 = (1 / 10 ^ 40) ^ 2 by norm_num] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- `‖p^{-s}‖³ ≤ 10⁻⁴⁰·p^{-1-2σ}`: a cubic remainder is `10⁻⁴⁰` of the prime's weight. -/
lemma norm_cpow_pow_three_le_of_mem_primeBlockSub {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hm : 20 ≤ (m : ℝ) + θ) {s : ℂ} (hres : s.re = 1 / 2 + σ) {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 ≤ 1 / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp
  rw [← norm_sq_prime_cpow_neg p hres,
    show ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 = ‖((p : ℕ) : ℂ) ^ (-s)‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

/-- **A per-prime error of `C·10⁻⁴⁰·p^{-1-2σ}` sums to at most `10⁻²⁰`** over a block past
offset `20`, for `C ≤ 1000`. -/
lemma sum_primeBlockSub_le_of_le_mul_rpow {θ σ C : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    (hC : C ≤ 1000) {f : Nat.Primes → ℝ}
    (hf : ∀ p ∈ primeBlockSub θ m, f p ≤ C * (1 / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))) :
    ∑ p ∈ primeBlockSub θ m, f p ≤ 1 / 10 ^ 20 := by
  have hS := blockRpowSum_le hσ (by linarith : (16 : ℝ) ≤ (m : ℝ) + θ)
  have hS0 := blockRpowSum_nonneg θ σ m
  calc ∑ p ∈ primeBlockSub θ m, f p
      ≤ ∑ p ∈ primeBlockSub θ m, C * (1 / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :=
        Finset.sum_le_sum hf
    _ = C / 10 ^ 40 * blockRpowSum θ σ m := by
        rw [blockRpowSum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ 1000 / 10 ^ 40 * (1 + 1 / 150000) := by gcongr
    _ ≤ 1 / 10 ^ 20 := by norm_num

/-- The per-prime remainders of the moments against `r³ ≤ E`, `r ≤ 1`: the variance's
`42r³ + 48r²r²`, the mean's `36r³ + 2r³r` and the covariance's `60r⁴`. -/
private lemma remainders_le {r E : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hE : r ^ 3 ≤ E) :
    42 * r ^ 3 + 48 * r ^ 2 * r ^ 2 ≤ 90 * E ∧ 36 * r ^ 3 + 2 * r ^ 3 * r ≤ 90 * E
      ∧ 60 * r ^ 4 ≤ 90 * E := by
  have h4 : r ^ 4 ≤ r ^ 3 := by
    rw [show r ^ 4 = r * r ^ 3 by ring]
    exact mul_le_of_le_one_left (pow_nonneg hr0 3) hr1
  have h3 : 0 ≤ r ^ 3 := pow_nonneg hr0 3
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [show r ^ 2 * r ^ 2 = r ^ 4 by ring]
  · nlinarith [show r ^ 3 * r = r ^ 4 by ring]
  · nlinarith

/-! ### The block statistics in closed form

Past offset `20` the local variables are below `10⁻⁴⁰`, so every cubic remainder of the two-atom
law (`RMF/EulerProduct/RademacherTiltedLaw.lean`) sums to at most `10⁻²⁰`. -/

/-- On one vertical line the local variables have one size: `‖p^{-s₁}‖ = ‖p^{-s₂}‖`. -/
lemma norm_cpow_shiftLine_eq (p : Nat.Primes) (σ h h' : ℝ) :
    ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ = ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h'))‖ := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.norm_natCast_cpow_of_pos p.2.pos,
    Complex.neg_re, Complex.neg_re, re_shiftLine, re_shiftLine]

/-- `∑ (Re p^{-s₁})² = (S_m + C_m)/2` (`RMF.sum_re_cpow_neg_sq_primeBlockSub_eq`). -/
lemma sum_re_cpow_shiftLine_sq_eq (θ σ h : ℝ) (m : ℕ) :
    ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h))).re) ^ 2
      = (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m) / 2 := by
  rw [sum_re_cpow_neg_sq_primeBlockSub_eq θ σ m (re_shiftLine σ h), im_shiftLine, blockRpowSum,
    blockCosSum, add_div]
  congr 2
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le, div_eq_mul_inv]

/-- **The height block's variance** under the tilt at `s₁ = ½+σ+ih`: `(S_m + C_m)/2` up to
`10⁻²⁰`, for any `h`, `σ ≥ 0` and `m + θ ≥ 20`. -/
theorem abs_blockMatchedVarAdd_height_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |((blockMatchedVarAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (primeBlockSub θ m) : ℝ≥0) : ℝ) - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m) / 2|
      ≤ 1 / 10 ^ 20 := by
  have hres := re_shiftLine σ h
  have hs : 0 < (shiftLine σ h).re := by rw [hres]; linarith
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
    fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp).trans (by norm_num)
  rw [sum_re_cpow_shiftLine_sq_eq] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp
  exact (remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub hσ hm hres hp)).1

/-- **The real block's variance** under the tilt at `s₁ = ½+σ+ih`: `S_m` up to `10⁻²⁰`. -/
theorem abs_blockMatchedVarAdd_real_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |((blockMatchedVarAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
        (primeBlockSub θ m) : ℝ≥0) : ℝ) - blockRpowSum θ σ m| ≤ 1 / 10 ^ 20 := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp).trans
      (by norm_num)
  rw [sum_re_cpow_neg_sq_primeBlockSub_eq_of_im_zero θ σ m (re_shiftLine σ 0)
    (im_shiftLine σ 0)] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp
  rw [norm_cpow_shiftLine_eq p σ h 0]
  exact (remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp)).1

/-- The one-point covariance's algebra: `(1 − 4κ²)(Δ_v/2)(Δ_w/2)` against `uv`, when `Δ_v`,
`Δ_w` are within `24r³` of `2u`, `2v` and `|κ|, |u|, |v| ≤ r ≤ 1/5`. -/
private lemma abs_tilt_cov_sub_le {κ Δv Δw u v r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 5)
    (hκ : |κ| ≤ r) (hu : |u| ≤ r) (hv : |v| ≤ r)
    (hΔv : |Δv - 2 * u| ≤ 24 * r ^ 3) (hΔw : |Δw - 2 * v| ≤ 24 * r ^ 3) :
    |(1 - 4 * κ ^ 2) * (Δv / 2) * (Δw / 2) - u * v| ≤ 60 * r ^ 4 := by
  have hdv : |Δv / 2 - u| ≤ 12 * r ^ 3 := by
    rw [show Δv / 2 - u = (Δv - 2 * u) / 2 by ring, abs_div, abs_two]
    linarith
  have hdw : |Δw / 2 - v| ≤ 12 * r ^ 3 := by
    rw [show Δw / 2 - v = (Δw - 2 * v) / 2 by ring, abs_div, abs_two]
    linarith
  have hr3 : 12 * r ^ 3 ≤ r := by
    have : r ^ 2 ≤ 1 / 25 := by nlinarith
    nlinarith
  have hDv : |Δv / 2| ≤ 2 * r := by
    calc |Δv / 2| = |u + (Δv / 2 - u)| := by ring_nf
      _ ≤ |u| + |Δv / 2 - u| := abs_add_le _ _
      _ ≤ 2 * r := by linarith
  have hDw : |Δw / 2| ≤ 2 * r := by
    calc |Δw / 2| = |v + (Δw / 2 - v)| := by ring_nf
      _ ≤ |v| + |Δw / 2 - v| := abs_add_le _ _
      _ ≤ 2 * r := by linarith
  have h1 : |(Δv / 2 - u) * (Δw / 2)| ≤ 24 * r ^ 4 := by
    rw [abs_mul]
    calc |Δv / 2 - u| * |Δw / 2| ≤ 12 * r ^ 3 * (2 * r) :=
          mul_le_mul hdv hDw (abs_nonneg _) (by positivity)
      _ = 24 * r ^ 4 := by ring
  have h2 : |u * (Δw / 2 - v)| ≤ 12 * r ^ 4 := by
    rw [abs_mul]
    calc |u| * |Δw / 2 - v| ≤ r * (12 * r ^ 3) := mul_le_mul hu hdw (abs_nonneg _) hr0
      _ = 12 * r ^ 4 := by ring
  have h3 : |4 * κ ^ 2 * ((Δv / 2) * (Δw / 2))| ≤ 16 * r ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hκ2 : |κ| ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hκ 2
    have hprod : |Δv / 2| * |Δw / 2| ≤ 2 * r * (2 * r) :=
      mul_le_mul hDv hDw (abs_nonneg _) (by positivity)
    calc 4 * |κ| ^ 2 * (|Δv / 2| * |Δw / 2|) ≤ 4 * r ^ 2 * (2 * r * (2 * r)) := by gcongr
      _ = 16 * r ^ 4 := by ring
  rw [show (1 - 4 * κ ^ 2) * (Δv / 2) * (Δw / 2) - u * v
      = (Δv / 2 - u) * (Δw / 2) + u * (Δw / 2 - v) - 4 * κ ^ 2 * ((Δv / 2) * (Δw / 2)) by ring]
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The block covariance** of the height and the real block under the tilt at `s₁`: `c_m` up
to `10⁻²⁰` (`RMF.blockMatchedCovAddT_eq`, per prime `(1 − 4κ_p²)D_vD_w`). -/
theorem abs_blockMatchedCovAddT_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMatchedCovAddT X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub θ m)
      - blockCosSum θ σ h m| ≤ 1 / 10 ^ 20 := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  rw [blockMatchedCovAddT_eq hX y hs hB, blockCosSum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_primeBlockSub_le_of_le_mul_rpow hσ hm (C := 90)
    (by norm_num) fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h) hp
  have hr5 : ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ ≤ 1 / 5 := hr.trans (by norm_num)
  have hnw := norm_cpow_shiftLine_eq p σ 0 h
  have hw5 : ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))‖ ≤ 1 / 5 := hnw ▸ hr5
  obtain ⟨hκ, -, -⟩ := abs_tiltMultiplier_le (((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
  have hDw := abs_localLogAdd_diff_sub_le hw5
  rw [hnw] at hDw
  have hmain : (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))).re * (((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))).re
      = Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    rw [re_mul_re_prime_eq p.2, re_shiftLine, re_shiftLine, im_shiftLine, im_shiftLine,
      show -(1 / 2 + σ + (1 / 2 + σ)) = -1 - 2 * σ by ring, sub_zero, add_zero]
    ring
  rw [← hmain]
  have key := abs_tilt_cov_sub_le (norm_nonneg _) hr5 hκ (Complex.abs_re_le_norm _)
    (hnw ▸ Complex.abs_re_le_norm _) (abs_localLogAdd_diff_sub_le hr5) hDw
  exact key.trans ((remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h) hp)).2.2)

/-- **The real block's tilted mean** under the tilt at `s₁ = ½+σ+ih`: `2c_m − S_m/2` up to
`10⁻²⁰` — per prime `2Re a·Re w − Re(w²)/2 = p^{-1-2σ}(2cos(h log p) − ½)`. -/
theorem abs_blockMeanAdd_real_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
        (primeBlockSub θ m) - (2 * blockCosSum θ σ h m - blockRpowSum θ σ m / 2)|
      ≤ 1 / 10 ^ 20 := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  have hgap := abs_blockMeanAdd_sub_sum_le hX y hs hB
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp).trans
      (by norm_num)
  have hmain : ∑ p ∈ primeBlockSub θ m, (2 * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))).re
        * (((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))).re
        - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) ^ 2).re / 2)
      = 2 * blockCosSum θ σ h m - blockRpowSum θ σ m / 2 := by
    rw [blockCosSum, blockRpowSum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rademacherDrift_prime_eq p.2 (re_shiftLine σ h) (re_shiftLine σ 0), im_shiftLine,
      im_shiftLine, sub_zero, add_zero, mul_zero, zero_mul, Real.cos_zero]
    ring
  rw [hmain] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp
  rw [norm_cpow_shiftLine_eq p σ h 0]
  exact (remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp)).2.1

/-- **The height block's tilted mean** under its own tilt: `S_m + C_m/2` up to `10⁻²⁰`, the
`σ ≥ 0` form of `RMF.abs_blockMeanAdd_sub_le_sharp`. -/
theorem abs_blockMeanAdd_height_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (primeBlockSub θ m) - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m / 2)|
      ≤ 1 / 10 ^ 20 := by
  have hres := re_shiftLine σ h
  have hs : 0 < (shiftLine σ h).re := by rw [hres]; linarith
  have hgap := abs_blockMeanAdd_sub_sum_le hX y hs hB
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
    fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp).trans (by norm_num)
  have hmain : ∑ p ∈ primeBlockSub θ m, (2 * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))).re
        * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))).re
        - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) ^ 2).re / 2)
      = blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m / 2 := by
    rw [blockCosSum, blockRpowSum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rademacherDrift_prime_eq p.2 hres hres, im_shiftLine, sub_self, zero_mul,
      Real.cos_zero, show h + h = 2 * h by ring]
    ring
  rw [hmain] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp
  exact (remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub hσ hm hres hp)).2.1

/-! ### The block cosine sums: explicit Mertens below scale `104`, the PNT from it

`C_m(τ) = RMF.blockCosSum θ σ τ m` against `∫_{e^{m+θ}}^{e^{m+θ+1}} cos(τu)e^{-2σu}/u du`: within
`2Ke^{-(m+θ)} + Kτ` by explicit Mertens (`K = RMF.mertensErrConst`, Abel summation with the error
used pointwise) on every block, so within `RMF.blockCosErr θ m τ`, the PNT's `(τ+1)/10²⁸` from
`m + θ ≥ 104` and Mertens' below; the damped integral is at most `2/(τe^{m+θ})`.  From
`m + θ ≥ 20` with `τ ≤ 2e^{-20}` the error is at most `7.43·10⁻⁸`. -/

/-- **The damped integral is bounded however long**: `|∫_A^B cos(τu)e^{-2σu}/u du| ≤ 2/(τA)` for
`0 < A ≤ B`, `τ > 0`, `σ ≥ 0` — one integration by parts against the decreasing weight
`e^{-2σu}/u`, whose variation on `[A, B]` is at most its value `≤ 1/A` at `A`. -/
theorem abs_integral_cos_mul_exp_div_le {τ σ A B : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ) (hA : 0 < A)
    (hAB : A ≤ B) :
    |∫ u in A..B, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u| ≤ 2 / (τ * A) := by
  have hpos : ∀ x ∈ Set.uIcc A B, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hAB] at hx
    exact hA.trans_le hx.1
  set g : ℝ → ℝ := fun u => Real.exp (-(2 * σ) * u) / u with hgdef
  set g' : ℝ → ℝ := fun u => -(Real.exp (-(2 * σ) * u) * (2 * σ * u + 1) / u ^ 2) with hg'def
  have hgd : ∀ x ∈ Set.uIcc A B, HasDerivAt g (g' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(2 * σ) * u))
        (Real.exp (-(2 * σ) * x) * (-(2 * σ))) x := by
      have h := ((hasDerivAt_id x).const_mul (-(2 * σ))).exp
      simpa using h
    refine (h1.div (hasDerivAt_id x) hx0).congr_deriv ?_
    simp only [hg'def, id]
    field_simp
    ring
  have hg'c : ContinuousOn g' (Set.uIcc A B) := by
    refine ContinuousOn.neg (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_)
    exact pow_ne_zero 2 (hpos x hx).ne'
  have hvd : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun u : ℝ => Real.sin (τ * u) / τ) (Real.cos (τ * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul τ).sin).div_const τ
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hcosc : Continuous fun x : ℝ => Real.cos (τ * x) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgd hvd
    hg'c.intervalIntegrable (hcosc.intervalIntegrable A B)
  have hform : (∫ u in A..B, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      = ∫ x in A..B, g x * Real.cos (τ * x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hgdef]
    ring
  rw [hform, hparts]
  -- the weight at the two ends
  have hgA0 : 0 ≤ g A := by simp only [hgdef]; positivity
  have hgB0 : 0 ≤ g B := by
    simp only [hgdef]
    exact div_nonneg (Real.exp_pos _).le (hA.le.trans hAB)
  have hgA1 : g A ≤ 1 / A := by
    simp only [hgdef]
    exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith)) hA.le
  -- the variation: `∫_A^B (-g') = g A - g B`
  have hvar : (∫ x in A..B, -g' x) = g A - g B := by
    have hd : ∀ x ∈ Set.uIcc A B, HasDerivAt (fun u => -g u) (-g' x) x :=
      fun x hx => (hgd x hx).neg
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg'c.neg.intervalIntegrable]
    ring
  have hg'le : ∀ x ∈ Set.Icc A B, 0 ≤ -g' x := by
    intro x hx
    have hx0 : 0 < x := hA.trans_le hx.1
    simp only [hg'def, neg_neg]
    positivity
  have hrem : |∫ x in A..B, g' x * (Real.sin (τ * x) / τ)| ≤ (g A - g B) / τ := by
    have hi1 : IntervalIntegrable (fun x => |g' x * (Real.sin (τ * x) / τ)|)
        MeasureTheory.volume A B :=
      (hg'c.mul (by fun_prop : Continuous fun x : ℝ => Real.sin (τ * x) / τ).continuousOn).abs
        |>.intervalIntegrable
    have hi2 : IntervalIntegrable (fun x => -g' x / τ) MeasureTheory.volume A B :=
      (hg'c.neg.div_const τ).intervalIntegrable
    have hpt : ∀ x ∈ Set.Icc A B, |g' x * (Real.sin (τ * x) / τ)| ≤ -g' x / τ := by
      intro x hx
      rw [abs_mul, abs_div, abs_of_pos hτ, abs_of_nonpos (by linarith [hg'le x hx])]
      have hs := Real.abs_sin_le_one (τ * x)
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (hg'le x hx) hs) hτ.le
    calc |∫ x in A..B, g' x * (Real.sin (τ * x) / τ)|
        ≤ ∫ x in A..B, |g' x * (Real.sin (τ * x) / τ)| :=
          intervalIntegral.abs_integral_le_integral_abs hAB
      _ ≤ ∫ x in A..B, -g' x / τ := intervalIntegral.integral_mono_on hAB hi1 hi2 hpt
      _ = (g A - g B) / τ := by rw [intervalIntegral.integral_div, hvar]
  have hsin : ∀ x : ℝ, |Real.sin (τ * x) / τ| ≤ 1 / τ := fun x => by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hτ.le
  have hsB : |g B * (Real.sin (τ * B) / τ)| ≤ g B / τ := by
    rw [abs_mul, abs_of_nonneg hgB0]
    calc g B * |Real.sin (τ * B) / τ| ≤ g B * (1 / τ) := mul_le_mul_of_nonneg_left (hsin B) hgB0
      _ = g B / τ := by ring
  have hsA : |g A * (Real.sin (τ * A) / τ)| ≤ g A / τ := by
    rw [abs_mul, abs_of_nonneg hgA0]
    calc g A * |Real.sin (τ * A) / τ| ≤ g A * (1 / τ) := mul_le_mul_of_nonneg_left (hsin A) hgA0
      _ = g A / τ := by ring
  have htot : 2 * g A / τ ≤ 2 / (τ * A) := by
    rw [div_le_div_iff₀ hτ (by positivity)]
    have := mul_le_mul_of_nonneg_left hgA1 (by positivity : (0 : ℝ) ≤ 2 * τ * A)
    have hAA : 2 * τ * A * (1 / A) = 2 * τ := by field_simp
    nlinarith
  calc |g B * (Real.sin (τ * B) / τ) - g A * (Real.sin (τ * A) / τ)
        - ∫ x in A..B, g' x * (Real.sin (τ * x) / τ)|
      ≤ |g B * (Real.sin (τ * B) / τ)| + |g A * (Real.sin (τ * A) / τ)|
        + |∫ x in A..B, g' x * (Real.sin (τ * x) / τ)| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ g B / τ + g A / τ + (g A - g B) / τ := by linarith
    _ = 2 * g A / τ := by ring
    _ ≤ 2 / (τ * A) := htot

/-- **The weighted block sum against explicit Mertens**: for `2 ≤ y₁ ≤ y₂` and `σ ≥ 0`,
`∑_{y₁ < p ≤ y₂} cos(τ log p)/p^{1+2σ}` is within `2K/log y₁ + |τ|K(log log y₂ - log log y₁)` of
`∫_{y₁}^{y₂} cosLogDiv τ t · t^{-2σ} dt`: `RMF.abs_cos_prime_sum_block_sub_integral_le_mertens`
on every initial sub-block, moved across the weight by
`RMF.abs_sum_sub_integral_weight_le_of_nonneg`. -/
theorem abs_cos_prime_sum_block_weight_sub_integral_le_mertens (τ : ℝ) {σ y₁ y₂ : ℝ}
    (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) (hσ : 0 ≤ σ) :
    |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
        Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ))
        - ∫ t in y₁..y₂, cosLogDiv τ t * t ^ (-(2 * σ))|
      ≤ 2 * mertensErrConst / Real.log y₁
        + |τ| * mertensErrConst * (Real.log (Real.log y₂) - Real.log (Real.log y₁)) := by
  refine abs_sum_sub_integral_weight_le_of_nonneg hy₁ hy hσ fun u hu => ?_
  have hK := mertensErrConst_nonneg
  have hl₁ : 0 < Real.log y₁ := Real.log_pos (by linarith)
  have hlu : Real.log y₁ ≤ Real.log u := Real.log_le_log (by linarith) hu.1
  have hlu₂ : Real.log u ≤ Real.log y₂ := Real.log_le_log (by linarith [hu.1]) hu.2
  have hll : Real.log (Real.log u) ≤ Real.log (Real.log y₂) := Real.log_le_log (by linarith) hlu₂
  refine (abs_cos_prime_sum_block_sub_integral_le_mertens τ hy₁ hu.1).trans ?_
  have h1 : mertensErrConst / Real.log u ≤ mertensErrConst / Real.log y₁ :=
    div_le_div_of_nonneg_left hK hl₁ hlu
  have h2 : |τ| * mertensErrConst * (Real.log (Real.log u) - Real.log (Real.log y₁))
      ≤ |τ| * mertensErrConst * (Real.log (Real.log y₂) - Real.log (Real.log y₁)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (abs_nonneg _) hK)
  have h3 : 2 * mertensErrConst / Real.log y₁
      = mertensErrConst / Real.log y₁ + mertensErrConst / Real.log y₁ := by ring
  linarith

/-- A block's sum as a sum over the primes of `(blockScale θ m, blockScale θ (m+1)]`. -/
lemma sum_primeBlockSub_eq_sum_Ioc (θ : ℝ) (m : ℕ) (F : ℕ → ℝ) :
    ∑ p ∈ primeBlockSub θ m, F p
      = ∑ p ∈ Finset.Ioc ⌊blockScale θ m⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p, F p := by
  rw [primeBlockSub, harperBlock, sum_primesIcoSub _ _ F, blockScale_rpow_inv_exp_one,
    filter_prime_Ioc_eq_primesIco]

/-- **The blocks `m₁ ≤ m < M` together** are the primes of `(blockScale θ m₁, blockScale θ M]`. -/
lemma sum_Ico_primeBlockSub_eq_sum_Ioc (θ : ℝ) {m₁ M : ℕ} (hmM : m₁ ≤ M) (F : ℕ → ℝ) :
    ∑ m ∈ Finset.Ico m₁ M, ∑ p ∈ primeBlockSub θ m, F p
      = ∑ p ∈ Finset.Ioc ⌊blockScale θ m₁⌋₊ ⌊blockScale θ M⌋₊ with Nat.Prime p, F p := by
  induction M, hmM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, ih, sum_primeBlockSub_eq_sum_Ioc, Finset.sum_filter,
      Finset.sum_filter, Finset.sum_filter,
      Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (blockScale_mono θ hM))
        (Nat.floor_le_floor (blockScale_mono θ (Nat.le_succ M)))]

/-- **The blocks `m₁ ≤ m < M` against explicit Mertens, telescoped**: for `τ, σ ≥ 0` and
`m₁ + θ ≥ 0`, `∑_{m₁≤m<M} C_m(τ)` is within `2Ke^{-(m₁+θ)} + Kτ(M - m₁)` of
`∫_{e^{m₁+θ}}^{e^{M+θ}} cos(τu)e^{-2σu}/u du` — one Abel summation over the union of the blocks. -/
theorem abs_sum_blockCosSum_sub_integral_le_mertens {τ σ θ : ℝ} {m₁ M : ℕ} (hmM : m₁ ≤ M)
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hm₁ : 0 ≤ (m₁ : ℝ) + θ) :
    |∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m
        - ∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 2 * mertensErrConst * Real.exp (-((m₁ : ℝ) + θ))
        + mertensErrConst * τ * ((M : ℝ) - m₁) := by
  have hlog₁ : Real.log (blockScale θ m₁) = Real.exp ((m₁ : ℝ) + θ) := log_blockScale θ m₁
  have hlog₂ : Real.log (blockScale θ M) = Real.exp ((M : ℝ) + θ) := log_blockScale θ M
  have hY₁e : Real.exp 1 ≤ blockScale θ m₁ :=
    Real.exp_le_exp.2 (Real.one_le_exp hm₁)
  have hY₁ : 2 ≤ blockScale θ m₁ := le_trans (by linarith [Real.exp_one_gt_d9]) hY₁e
  have hY : blockScale θ m₁ ≤ blockScale θ M := blockScale_mono θ hmM
  -- the sum, as one sum over `(blockScale θ m₁, blockScale θ M]`
  have hsum : ∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m
      = ∑ p ∈ Finset.Ioc ⌊blockScale θ m₁⌋₊ ⌊blockScale θ M⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
    unfold blockCosSum
    rw [sum_Ico_primeBlockSub_eq_sum_Ioc θ hmM
      (fun n => Real.cos (τ * Real.log (n : ℝ)) * (n : ℝ) ^ (-1 - 2 * σ))]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.1 hp).2.pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  -- the integral, in the variable `t = e^u`
  have hint : (∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
        Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      = ∫ t in blockScale θ m₁..blockScale θ M, cosLogDiv τ t * t ^ (-(2 * σ)) := by
    rw [← hlog₁, ← hlog₂, integral_cosLogDiv_mul_rpow_eq (by linarith) hY]
  rw [hsum, hint]
  refine (abs_cos_prime_sum_block_weight_sub_integral_le_mertens τ hY₁ hY hσ).trans
    (le_of_eq ?_)
  rw [hlog₁, hlog₂, Real.log_exp, Real.log_exp, abs_of_nonneg hτ, Real.exp_neg]
  ring

/-- **One block against explicit Mertens**: for `τ, σ ≥ 0` and `m + θ ≥ 0`,
`|C_m(τ) - ∫_{e^{m+θ}}^{e^{m+θ+1}} cos(τu)e^{-2σu}/u du| ≤ 2Ke^{-(m+θ)} + Kτ` — the Mertens
counterpart of `RMF.abs_sum_cos_primeBlockSub_sub_integral_le`, with no floor. -/
theorem abs_sum_cos_primeBlockSub_sub_integral_le_mertens (τ σ θ : ℝ) (m : ℕ) (hτ : 0 ≤ τ)
    (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |(∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 2 * mertensErrConst * Real.exp (-((m : ℝ) + θ)) + mertensErrConst * τ := by
  have h := abs_sum_blockCosSum_sub_integral_le_mertens (σ := σ) (Nat.le_succ m) hτ hσ0 hm
  rw [Nat.Ico_succ_singleton, Finset.sum_singleton] at h
  have hM : ((m + 1 : ℕ) : ℝ) + θ = (m : ℝ) + θ + 1 := by
    push_cast
    ring
  rw [hM] at h
  unfold blockCosSum at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **The block cosine error, two regimes**: `(τ+1)/10²⁸` for `m + θ ≥ 104` — the error of
`RMF.abs_sum_cos_primeBlockSub_sub_integral_le` — and Mertens' `2Ke^{-(m+θ)} + Kτ` below,
`K = mertensErrConst`. -/
noncomputable def blockCosErr (θ : ℝ) (m : ℕ) (τ : ℝ) : ℝ :=
  if 104 ≤ (m : ℝ) + θ then (τ + 1) / 10 ^ 28
  else 2 * mertensErrConst * Real.exp (-((m : ℝ) + θ)) + mertensErrConst * τ

/-- **The block cosine sum as its log-integral, two regimes**: for `τ, σ ≥ 0` and `m + θ ≥ 0`,
within `blockCosErr θ m τ` — the twin of `RMF.abs_sum_cos_primeBlockSub_sub_integral_le`, which it
is for `m + θ ≥ 104`. -/
theorem abs_sum_cos_primeBlockSub_sub_integral_le_two_regime (τ σ θ : ℝ) (m : ℕ) (hτ : 0 ≤ τ)
    (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |(∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ blockCosErr θ m τ := by
  unfold blockCosErr
  split_ifs with h
  · exact abs_sum_cos_primeBlockSub_sub_integral_le τ σ θ m hτ hσ0 h
  · exact abs_sum_cos_primeBlockSub_sub_integral_le_mertens τ σ θ m hτ hσ0 hm

/-- `|C_m(τ)| ≤ 2/(τe^{m+θ}) + E` from `|C_m(τ) - ∫| ≤ E`: the damped integral is at most
`2/(τe^{m+θ})` (`RMF.abs_integral_cos_mul_exp_div_le`). -/
lemma abs_sum_cos_primeBlockSub_le_of_sub_integral_le {τ σ θ E : ℝ} {m : ℕ} (hτ : 0 < τ)
    (hσ0 : 0 ≤ σ)
    (h : |(∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u| ≤ E) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 2 / (τ * Real.exp ((m : ℝ) + θ)) + E := by
  have hI := abs_integral_cos_mul_exp_div_le hτ hσ0 (Real.exp_pos ((m : ℝ) + θ))
    (Real.exp_le_exp.2 (by linarith : (m : ℝ) + θ ≤ (m : ℝ) + θ + 1))
  have htri := abs_add_le
    ((∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
    (∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
      Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
  rw [sub_add_cancel] at htri
  linarith

/-- **The block cosine sum, two regimes, sharp main term**: for `τ > 0`, `σ ≥ 0` and `m + θ ≥ 0`,
`|C_m(τ)| ≤ 2/(τe^{m+θ}) + blockCosErr θ m τ` on every block. -/
theorem abs_sum_cos_primeBlockSub_le_two_regime (τ σ θ : ℝ) (m : ℕ) (hτ : 0 < τ)
    (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 2 / (τ * Real.exp ((m : ℝ) + θ)) + blockCosErr θ m τ :=
  abs_sum_cos_primeBlockSub_le_of_sub_integral_le hτ hσ0
    (abs_sum_cos_primeBlockSub_sub_integral_le_two_regime τ σ θ m hτ.le hσ0 hm)

/-- **The block cosine sum, two regimes**: for `τ > 0`, `σ ≥ 0` and `m + θ ≥ 0`,
`|C_m(τ)| ≤ 3/(τe^{m+θ}) + blockCosErr θ m τ`. -/
theorem abs_sum_cos_primeBlockSub_le_explicit_floor_two_regime (τ σ θ : ℝ) (m : ℕ)
    (hτ : 0 < τ) (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 3 / (τ * Real.exp ((m : ℝ) + θ)) + blockCosErr θ m τ := by
  refine (abs_sum_cos_primeBlockSub_le_two_regime τ σ θ m hτ hσ0 hm).trans ?_
  have h23 : 2 / (τ * Real.exp ((m : ℝ) + θ)) ≤ 3 / (τ * Real.exp ((m : ℝ) + θ)) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- `e^{-20} ≤ 1/(4.85·10⁸)`. -/
lemma exp_neg_twenty_le_numeral : Real.exp (-20) ≤ 1 / 485000000 := by
  have h20 : (485000000 : ℝ) ≤ Real.exp ((20 : ℕ) : ℝ) :=
    le_exp_natCast_of_le_pow (c := 2.7182818283) (by norm_num) Real.exp_one_gt_d9.le
      (by norm_num)
  push_cast at h20
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h20

/-- **The per-block error at the floor `20`**: `blockCosErr θ m τ ≤ 7.43·10⁻⁸` for `m + θ ≥ 20`
and `τ ≤ 2e^{-20}` — Mertens' `2Ke^{-20} + 2Ke^{-20}`, `K ≤ 9.0028`. -/
theorem blockCosErr_le_numeral {θ τ : ℝ} {m : ℕ} (hm : 20 ≤ (m : ℝ) + θ)
    (hτ2 : τ ≤ 2 * Real.exp (-20)) : blockCosErr θ m τ ≤ 7.43 / 10 ^ 8 := by
  have hK := mertensErrConst_le
  have hK0 := mertensErrConst_nonneg
  have he := exp_neg_twenty_le_numeral
  have he0 : 0 ≤ Real.exp (-20) := (Real.exp_pos _).le
  have hτ1 : τ ≤ 1 := by linarith
  unfold blockCosErr
  split_ifs with h
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have hem : Real.exp (-((m : ℝ) + θ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
    have h1 : mertensErrConst * Real.exp (-((m : ℝ) + θ)) ≤ mertensErrConst * Real.exp (-20) :=
      mul_le_mul_of_nonneg_left hem hK0
    have h2 : mertensErrConst * τ ≤ mertensErrConst * (2 * Real.exp (-20)) :=
      mul_le_mul_of_nonneg_left hτ2 hK0
    have h3 : mertensErrConst * Real.exp (-20) ≤ 9.0028 * (1 / 485000000) :=
      mul_le_mul hK he he0 (by norm_num)
    linarith

/-! ### The window numerics

At `θ = k` and `h ∈ RMF.halfWindow k`, the one-point frequency has `ξ = log h + k ∈ [-1, 0]` and
the doubled one `ξ + log 2`: the ranges of `RMF/UniformLower/WindowCosine.lean` transfer to the
first blocks, and `RMF.abs_sum_cos_primeBlockSub_le_explicit_floor_two_regime` bounds every block,
with the error `RMF.blockCosErr` at most `7.43·10⁻⁸` from `k ≥ 20`. -/

/-- **The window in logarithms**: `h ∈ halfWindow k` has `0 < h` and `log h + k ∈ [-1, 0]`. -/
lemma log_add_mem_of_mem_halfWindow {k : ℕ} {h : ℝ} (hh : h ∈ halfWindow k) :
    0 < h ∧ -1 ≤ Real.log h + k ∧ Real.log h + k ≤ 0 := by
  obtain ⟨h1, h2⟩ := hh
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) h1
  refine ⟨h0, ?_, ?_⟩
  · have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_log h0 h2
    rw [Real.log_exp] at this
    linarith

/-- `h ≤ 10⁻⁶` on the window at `k ≥ 20`. -/
lemma le_millionth_of_mem_halfWindow {k : ℕ} {h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) :
    h ≤ 1 / 10 ^ 6 := by
  have h1 : (10 : ℝ) ^ 6 ≤ Real.exp 20 := by
    have := Real.pow_div_factorial_le_exp (x := 20) (by norm_num) 10
    norm_num [Nat.factorial] at this
    linarith
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-20) ≤ 1 / 10 ^ 6 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h1
  linarith [hh.2]

/-- **The window's cosine errors from `k ≥ 20`**: `blockCosErr k m τ ≤ 7.43·10⁻⁸` at the window's
frequencies `τ = h, 2h ≤ 2e^{-20}` (`RMF.blockCosErr_le_numeral`), on every block. -/
lemma blockCosErr_window_le {k m : ℕ} {h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) :
    blockCosErr k m h ≤ 7.43 / 10 ^ 8 ∧ blockCosErr k m (2 * h) ≤ 7.43 / 10 ^ 8 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (20 : ℝ) ≤ (m : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have he : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hh.1
  have hh2 : h ≤ Real.exp (-(k : ℝ)) := hh.2
  have he0 : 0 < Real.exp (-20) := Real.exp_pos _
  exact ⟨blockCosErr_le_numeral hm (by linarith), blockCosErr_le_numeral hm (by linarith)⟩

/-- **Every block's cosine sum decays**: for `e^{-(k+1)} ≤ τ` (the window's `h` and `2h`),
`|∑_{p∈B_m} cos(τ log p)p^{-1-2σ}| ≤ 3e^{1-m} + blockCosErr k m τ`
(`RMF.abs_sum_cos_primeBlockSub_le_explicit_floor_two_regime`); from `k ≥ 104` the error is
`(τ+1)/10²⁸ ≤ 10⁻²⁰` for `τ ≤ 2`. -/
theorem abs_blockCosSum_le_exp {k : ℕ} {σ τ : ℝ} (hσ : 0 ≤ σ)
    (hτ : Real.exp (-((k : ℝ) + 1)) ≤ τ) (m : ℕ) :
    |blockCosSum k σ τ m| ≤ 3 * Real.exp (1 - m) + blockCosErr k m τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have h := abs_sum_cos_primeBlockSub_le_explicit_floor_two_regime τ σ k m hτ0 hσ
    (by positivity)
  have hprod : Real.exp ((m : ℝ) - 1) ≤ τ * Real.exp ((m : ℝ) + k) := by
    calc Real.exp ((m : ℝ) - 1) = Real.exp (-((k : ℝ) + 1)) * Real.exp ((m : ℝ) + k) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ τ * Real.exp ((m : ℝ) + k) := mul_le_mul_of_nonneg_right hτ (Real.exp_pos _).le
  have h1 : 3 / (τ * Real.exp ((m : ℝ) + k)) ≤ 3 * Real.exp (1 - m) := by
    rw [div_le_iff₀ (by positivity)]
    calc (3 : ℝ) = 3 * Real.exp (1 - m) * Real.exp ((m : ℝ) - 1) := by
          rw [mul_assoc, ← Real.exp_add, show (1 - (m : ℝ)) + ((m : ℝ) - 1) = 0 by ring,
            Real.exp_zero, mul_one]
      _ ≤ 3 * Real.exp (1 - m) * (τ * Real.exp ((m : ℝ) + k)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  unfold blockCosSum
  linarith

/-- **The window's cosine sums decay**: `|c_m| ≤ 3e^{1-m} + blockCosErr k m h` and
`|C_m| ≤ 3e^{1-m} + blockCosErr k m (2h)` for every block — at most `3e^{1-m} + 7.43·10⁻⁸` from
`k ≥ 20` (`RMF.blockCosErr_window_le`), `3e^{1-m} + 10⁻²⁰` from `k ≥ 104`. -/
theorem abs_blockCosSum_le_window {k : ℕ} {σ h : ℝ} (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (m : ℕ) :
    |blockCosSum k σ h m| ≤ 3 * Real.exp (1 - m) + blockCosErr k m h
      ∧ |blockCosSum k σ (2 * h) m| ≤ 3 * Real.exp (1 - m) + blockCosErr k m (2 * h) := by
  have h0 := (log_add_mem_of_mem_halfWindow hh).1
  exact ⟨abs_blockCosSum_le_exp hσ hh.1 m, abs_blockCosSum_le_exp hσ (by linarith [hh.1]) m⟩

/-- **The first blocks as `blockCos`**: for `τ > 0` and `2σe^{k+m+1} ≤ δ`, the block sum is within
`blockCosErr k m τ + δ` of `blockCos (log τ + k) m`
(`RMF.abs_sum_cos_primeBlockSub_sub_integral_le_two_regime`, the damping
`RMF.abs_integral_cos_mul_exp_div_sub_le` and `RMF.integral_cos_div_eq_blockCos`). -/
lemma abs_blockCosSum_sub_blockCos_le {k m : ℕ} {σ τ δ : ℝ} (hσ : 0 ≤ σ) (hτ0 : 0 < τ)
    (hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ δ) :
    |blockCosSum k σ τ m - blockCos (Real.log τ + k) m| ≤ blockCosErr k m τ + δ := by
  have hA := abs_sum_cos_primeBlockSub_sub_integral_le_two_regime τ σ k m hτ0.le hσ
    (by positivity)
  have hB := abs_integral_cos_mul_exp_div_sub_le (τ := τ) (σ := σ)
    (a := Real.exp ((m : ℝ) + k)) (b := Real.exp ((m : ℝ) + k + 1))
    (Real.exp_pos _) (Real.exp_le_exp.2 (by linarith)) hσ
  rw [integral_cos_div_eq_blockCos hτ0 k m] at hB
  have h2 : 2 * σ * (Real.exp ((m : ℝ) + k + 1) - Real.exp ((m : ℝ) + k)) ≤ δ := by
    have he : Real.exp ((m : ℝ) + k + 1) = Real.exp ((k : ℝ) + m + 1) := by ring_nf
    have hpos : 0 ≤ 2 * σ * Real.exp ((m : ℝ) + k) := by positivity
    rw [mul_sub, he]
    linarith
  unfold blockCosSum
  exact (abs_sub_le _ _ _).trans (add_le_add hA (hB.trans h2))

/-- A certified range of `blockCos` transfers to the block sum, widened by `blockCosErr k m τ + δ`
(`≤ 7.43·10⁻⁸ + δ` on the window from `k ≥ 20`, `RMF.blockCosErr_window_le`). -/
lemma blockCosSum_mem_of_blockCos {k m : ℕ} {σ τ δ lo hi : ℝ} (hσ : 0 ≤ σ) (hτ0 : 0 < τ)
    (hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ δ)
    (hb : lo ≤ blockCos (Real.log τ + k) m ∧ blockCos (Real.log τ + k) m ≤ hi) :
    lo - (blockCosErr k m τ + δ) ≤ blockCosSum k σ τ m
      ∧ blockCosSum k σ τ m ≤ hi + (blockCosErr k m τ + δ) := by
  have h := abs_le.1 (abs_blockCosSum_sub_blockCos_le hσ hτ0 hδ)
  constructor <;> linarith [h.1, h.2, hb.1, hb.2]

/-- `log(2h) + k = log 2 + (log h + k)`. -/
lemma log_two_mul_add_eq {h : ℝ} (h0 : 0 < h) (k : ℕ) :
    Real.log (2 * h) + k = Real.log 2 + (Real.log h + k) := by
  rw [Real.log_mul two_ne_zero h0.ne']
  ring

/-- The doubled frequency's `ξ = log(2h) + k ∈ [log 2 - 1, log 2]`. -/
lemma log_two_mul_add_mem_of_mem_halfWindow {k : ℕ} {h : ℝ} (hh : h ∈ halfWindow k) :
    Real.log 2 - 1 ≤ Real.log (2 * h) + k ∧ Real.log (2 * h) + k ≤ Real.log 2 := by
  obtain ⟨h0, hξ1, hξ2⟩ := log_add_mem_of_mem_halfWindow hh
  rw [log_two_mul_add_eq h0]
  constructor <;> linarith

/-- **The block's Mertens sum on the window**: `S_m ∈ [0.99, 1.01]` for every block with
`σe^{k+m+1} ≤ 1/200` (`RMF.sum_norm_sq_primeBlockSub_bounds_sharp` at `η = 1/200`). -/
theorem blockRpowSum_bounds {k m : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) :
    0.99 ≤ blockRpowSum k σ m ∧ blockRpowSum k σ m ≤ 1.01 := by
  have hk' : (16 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hη : |σ| * Real.log (blockScale k (m + 1)) ≤ 1 / 200 := by
    rw [abs_of_nonneg hσ, log_blockScale]
    push_cast
    rw [show (m : ℝ) + 1 + k = (k : ℝ) + m + 1 by ring]
    exact hσm
  have hS : blockRpowSum k σ m
      = ∑ p ∈ primeBlockSub k m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => (norm_sq_prime_cpow_neg p (re_shiftLine σ 0)).symm
  obtain ⟨hlo, hhi⟩ := sum_norm_sq_primeBlockSub_bounds_sharp
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) hk' hσ hη
    fun p _ => norm_sq_prime_cpow_neg p (re_shiftLine σ 0)
  rw [← hS] at hlo hhi
  have he : (0.99004 : ℝ) ≤ Real.exp (-(2 * (1 / 200))) := by interval_decide (trust := kernel)
  constructor
  · nlinarith
  · linarith

/-! ### The determinant: the weighted variance of `cos(h log p)`

`S_m·(S_m + C_m)/2 − c_m² = S·∑w cos²φ − (∑w cos φ)²` is `S` times the weighted variance of
`cos φ_p`, `φ_p = h log p`.  It is at least `S·W₀(a−b)²/4` as soon as two sub-blocks of weight
`≥ W₀` have `cos φ ≥ a` on one and `≤ b` on the other; the sub-blocks are phase windows
`φ₁ < h log p ≤ φ₂`, weighed by block Mertens (`RMF.sum_prime_Ioc_rpow_mertens_bounds_of_le`). -/

/-- **The weighted variance is at least the separated mass.**  If `x ≥ a` on `T₁ ⊆ B` and
`x ≤ b` on `T₂ ⊆ B` with `b ≤ a`, both of weight `≥ W₀ > 0`, then
`(∑w)(∑x²w) − (∑xw)² ≥ (∑w)·W₀(a−b)²/4`. -/
theorem le_weighted_variance {ι : Type*} {B T₁ T₂ : Finset ι} {w x : ι → ℝ} {a b W₀ : ℝ}
    (hw : ∀ i ∈ B, 0 ≤ w i) (h₁ : T₁ ⊆ B) (h₂ : T₂ ⊆ B)
    (ha : ∀ i ∈ T₁, a ≤ x i) (hb : ∀ i ∈ T₂, x i ≤ b) (hab : b ≤ a) (hW₀ : 0 < W₀)
    (hW₁ : W₀ ≤ ∑ i ∈ T₁, w i) (hW₂ : W₀ ≤ ∑ i ∈ T₂, w i) :
    (∑ i ∈ B, w i) * W₀ * (a - b) ^ 2 / 4
      ≤ (∑ i ∈ B, w i) * (∑ i ∈ B, x i ^ 2 * w i) - (∑ i ∈ B, x i * w i) ^ 2 := by
  set S := ∑ i ∈ B, w i with hSdef
  set M := ∑ i ∈ B, x i * w i with hMdef
  set Q := ∑ i ∈ B, x i ^ 2 * w i with hQdef
  have hsub : ∀ {T : Finset ι}, T ⊆ B → ∀ t : ℝ,
      ∑ i ∈ T, (x i - t) ^ 2 * w i ≤ ∑ i ∈ B, (x i - t) ^ 2 * w i := fun hT t =>
    Finset.sum_le_sum_of_subset_of_nonneg hT fun i hi _ => mul_nonneg (sq_nonneg _) (hw i hi)
  have hS : W₀ ≤ S := hW₁.trans (Finset.sum_le_sum_of_subset_of_nonneg h₁ fun i hi _ => hw i hi)
  have hS0 : 0 < S := lt_of_lt_of_le hW₀ hS
  -- every centring leaves `W₀(a−b)²/4`
  have hV : ∀ t : ℝ, W₀ * (a - b) ^ 2 / 4 ≤ ∑ i ∈ B, (x i - t) ^ 2 * w i := by
    intro t
    rcases le_total t ((a + b) / 2) with ht | ht
    · refine le_trans ?_ (hsub h₁ t)
      calc W₀ * (a - b) ^ 2 / 4 ≤ (∑ i ∈ T₁, w i) * ((a - b) / 2) ^ 2 := by
            nlinarith [sq_nonneg (a - b)]
        _ = ∑ i ∈ T₁, ((a - b) / 2) ^ 2 * w i := by rw [Finset.sum_mul]; simp [mul_comm]
        _ ≤ ∑ i ∈ T₁, (x i - t) ^ 2 * w i := Finset.sum_le_sum fun i hi => by
            have hx := ha i hi
            have h0 : 0 ≤ (a - b) / 2 := by linarith
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (by linarith) 2)
              (hw i (h₁ hi))
    · refine le_trans ?_ (hsub h₂ t)
      calc W₀ * (a - b) ^ 2 / 4 ≤ (∑ i ∈ T₂, w i) * ((a - b) / 2) ^ 2 := by
            nlinarith [sq_nonneg (a - b)]
        _ = ∑ i ∈ T₂, ((a - b) / 2) ^ 2 * w i := by rw [Finset.sum_mul]; simp [mul_comm]
        _ ≤ ∑ i ∈ T₂, (x i - t) ^ 2 * w i := Finset.sum_le_sum fun i hi => by
            have hx := hb i hi
            have h0 : 0 ≤ (a - b) / 2 := by linarith
            rw [show (x i - t) ^ 2 = (t - x i) ^ 2 by ring]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (by linarith) 2)
              (hw i (h₂ hi))
  -- centred at the mean, the sum is `(SQ − M²)/S`
  have hexp : ∑ i ∈ B, (x i - M / S) ^ 2 * w i = Q - 2 * (M / S) * M + (M / S) ^ 2 * S := by
    have hterm : ∀ i ∈ B, (x i - M / S) ^ 2 * w i
        = x i ^ 2 * w i - 2 * (M / S) * (x i * w i) + (M / S) ^ 2 * w i := fun i _ => by ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have key := hV (M / S)
  rw [hexp] at key
  have hid : S * (Q - 2 * (M / S) * M + (M / S) ^ 2 * S) = S * Q - M ^ 2 := by
    field_simp
    ring
  calc S * W₀ * (a - b) ^ 2 / 4 = S * (W₀ * (a - b) ^ 2 / 4) := by ring
    _ ≤ S * (Q - 2 * (M / S) * M + (M / S) ^ 2 * S) := mul_le_mul_of_nonneg_left key hS0.le
    _ = S * Q - M ^ 2 := hid

/-- The primes in `(a, b]`, as `primesIcoSub (⌊a⌋₊+1) (⌊b⌋₊+1)`. -/
lemma mem_primesIcoSub_floor_add_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : Nat.Primes} :
    p ∈ primesIcoSub (⌊a⌋₊ + 1) (⌊b⌋₊ + 1) ↔ a < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ b := by
  rw [mem_primesIcoSub]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Nat.floor_lt ha).1 (by omega), (Nat.le_floor_iff hb).1 (by omega)⟩
  · rintro ⟨h1, h2⟩
    have h1' := (Nat.floor_lt ha).2 h1
    have h2' := (Nat.le_floor_iff hb).2 h2
    exact ⟨by omega, by omega⟩

/-- **The weight of a sub-block** `L₁ < log p ≤ L₂`: at least `e^{-2η}(log L₂ − log L₁ − 20/L₁)`
for `1 ≤ L₁ ≤ L₂` and `|σ|L₂ ≤ η` (`RMF.sum_prime_Ioc_rpow_mertens_bounds_of_le`). -/
lemma le_sum_rpow_primesIcoSub_exp {σ η L₁ L₂ : ℝ} (hL₁ : 1 ≤ L₁) (hL : L₁ ≤ L₂)
    (hσ : |σ| * L₂ ≤ η) :
    Real.exp (-(2 * η)) * (Real.log L₂ - Real.log L₁ - 20 / L₁)
      ≤ ∑ p ∈ primesIcoSub (⌊Real.exp L₁⌋₊ + 1) (⌊Real.exp L₂⌋₊ + 1),
          ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  have hx : (2 : ℝ) ≤ Real.exp L₁ := by
    have := Real.add_one_le_exp L₁
    linarith
  have h := (sum_prime_Ioc_rpow_mertens_bounds_of_le (Real.exp L₁) (Real.exp L₂) σ η hx
    (Real.exp_le_exp.2 hL) (by rwa [Real.log_exp])).1
  simp only [Real.log_exp] at h
  rw [sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-1 - 2 * σ), ← filter_prime_Ioc_eq_primesIco]
  exact h

/-- A sub-block `L₁ < log p ≤ L₂` with `e^{m+θ} ≤ L₁`, `L₂ ≤ e^{m+1+θ}` lies in block `m`. -/
lemma primesIcoSub_exp_subset_primeBlockSub {θ L₁ L₂ : ℝ} {m : ℕ}
    (h₁ : Real.exp ((m : ℝ) + θ) ≤ L₁) (h₂ : L₂ ≤ Real.exp ((m : ℝ) + 1 + θ)) :
    primesIcoSub (⌊Real.exp L₁⌋₊ + 1) (⌊Real.exp L₂⌋₊ + 1) ⊆ primeBlockSub θ m := by
  intro p hp
  rw [mem_primesIcoSub_floor_add_one (Real.exp_pos _).le (Real.exp_pos _).le] at hp
  rw [mem_primeBlockSub, blockScale, blockScale]
  push_cast
  exact ⟨lt_of_le_of_lt (Real.exp_le_exp.2 h₁) hp.1, hp.2.trans (Real.exp_le_exp.2 h₂)⟩

/-- On the sub-block `φ₁/h < log p ≤ φ₂/h` the phase is `φ₁ < h log p ≤ φ₂`. -/
lemma mem_Ioc_mul_log_of_mem_primesIcoSub {h φ₁ φ₂ : ℝ} (hh : 0 < h) {p : Nat.Primes}
    (hp : p ∈ primesIcoSub (⌊Real.exp (φ₁ / h)⌋₊ + 1) (⌊Real.exp (φ₂ / h)⌋₊ + 1)) :
    φ₁ < h * Real.log ((p : ℕ) : ℝ) ∧ h * Real.log ((p : ℕ) : ℝ) ≤ φ₂ := by
  rw [mem_primesIcoSub_floor_add_one (Real.exp_pos _).le (Real.exp_pos _).le] at hp
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have h1 := (Real.lt_log_iff_exp_lt hp0).2 hp.1
  have h2 := (Real.log_le_iff_le_exp hp0).2 hp.2
  rw [div_lt_iff₀ hh] at h1
  rw [le_div_iff₀ hh] at h2
  constructor <;> linarith

/-- **The block's weighted variance of `cos(h log p)` from two phase windows.**  If
`cos ≥ a` on `(φ₁, φ₂]` and `cos ≤ b` on `(φ₃, φ₄]`, both inside the block's phase range
`(he^{m+θ}, he^{m+1+θ}]`, and each window's Mertens weight is at least `W₀ > 0`, then
`S(S + C)/2 − c² ≥ S·W₀(a−b)²/4`. -/
theorem le_blockVariance_of_phases {θ σ h η φ₁ φ₂ φ₃ φ₄ a b W₀ : ℝ} {m : ℕ} (hh : 0 < h)
    (h₁ : h * Real.exp ((m : ℝ) + θ) ≤ φ₁) (h₁₂ : φ₁ ≤ φ₂)
    (h₂ : φ₂ ≤ h * Real.exp ((m : ℝ) + 1 + θ))
    (h₃ : h * Real.exp ((m : ℝ) + θ) ≤ φ₃) (h₃₄ : φ₃ ≤ φ₄)
    (h₄ : φ₄ ≤ h * Real.exp ((m : ℝ) + 1 + θ))
    (hφ₁ : h ≤ φ₁) (hφ₃ : h ≤ φ₃) (hση : |σ| * Real.exp ((m : ℝ) + 1 + θ) ≤ η)
    (ha : ∀ φ, φ₁ < φ → φ ≤ φ₂ → a ≤ Real.cos φ)
    (hb : ∀ φ, φ₃ < φ → φ ≤ φ₄ → Real.cos φ ≤ b) (hab : b ≤ a) (hW₀ : 0 < W₀)
    (hW₁ : W₀ ≤ Real.exp (-(2 * η)) * (Real.log φ₂ - Real.log φ₁ - 20 * h / φ₁))
    (hW₂ : W₀ ≤ Real.exp (-(2 * η)) * (Real.log φ₄ - Real.log φ₃ - 20 * h / φ₃)) :
    blockRpowSum θ σ m * W₀ * (a - b) ^ 2 / 4
      ≤ blockRpowSum θ σ m * ((blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m) / 2)
        - blockCosSum θ σ h m ^ 2 := by
  -- the phase windows as sub-blocks
  have hsubset : ∀ {ψ₁ ψ₂ : ℝ}, h * Real.exp ((m : ℝ) + θ) ≤ ψ₁ →
      ψ₂ ≤ h * Real.exp ((m : ℝ) + 1 + θ) →
      primesIcoSub (⌊Real.exp (ψ₁ / h)⌋₊ + 1) (⌊Real.exp (ψ₂ / h)⌋₊ + 1)
        ⊆ primeBlockSub θ m := by
    intro ψ₁ ψ₂ hψ₁ hψ₂
    refine primesIcoSub_exp_subset_primeBlockSub ?_ ?_
    · rw [le_div_iff₀ hh, mul_comm]
      exact hψ₁
    · rw [div_le_iff₀ hh, mul_comm]
      exact hψ₂
  have hweight : ∀ {ψ₁ ψ₂ : ℝ}, h ≤ ψ₁ → ψ₁ ≤ ψ₂ → ψ₂ ≤ h * Real.exp ((m : ℝ) + 1 + θ) →
      W₀ ≤ Real.exp (-(2 * η)) * (Real.log ψ₂ - Real.log ψ₁ - 20 * h / ψ₁) →
      W₀ ≤ ∑ p ∈ primesIcoSub (⌊Real.exp (ψ₁ / h)⌋₊ + 1) (⌊Real.exp (ψ₂ / h)⌋₊ + 1),
        ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    intro ψ₁ ψ₂ hψ₁ hψ hψ₂ hW
    have hψ₁0 : 0 < ψ₁ := lt_of_lt_of_le hh hψ₁
    have hψ₂0 : 0 < ψ₂ := lt_of_lt_of_le hψ₁0 hψ
    have hL₁ : 1 ≤ ψ₁ / h := by rw [le_div_iff₀ hh]; linarith
    have hL : ψ₁ / h ≤ ψ₂ / h := div_le_div_of_nonneg_right hψ hh.le
    have hσL : |σ| * (ψ₂ / h) ≤ η := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)) hση
      rw [div_le_iff₀ hh, mul_comm]
      exact hψ₂
    refine le_trans ?_ (le_sum_rpow_primesIcoSub_exp hL₁ hL hσL)
    rw [Real.log_div hψ₂0.ne' hh.ne', Real.log_div hψ₁0.ne' hh.ne',
      show 20 / (ψ₁ / h) = 20 * h / ψ₁ by field_simp,
      show Real.log ψ₂ - Real.log h - (Real.log ψ₁ - Real.log h) - 20 * h / ψ₁
        = Real.log ψ₂ - Real.log ψ₁ - 20 * h / ψ₁ by ring]
    exact hW
  have hcos : ∀ {ψ₁ ψ₂ : ℝ} {p : Nat.Primes},
      p ∈ primesIcoSub (⌊Real.exp (ψ₁ / h)⌋₊ + 1) (⌊Real.exp (ψ₂ / h)⌋₊ + 1) →
      ψ₁ < h * Real.log ((p : ℕ) : ℝ) ∧ h * Real.log ((p : ℕ) : ℝ) ≤ ψ₂ :=
    fun hp => mem_Ioc_mul_log_of_mem_primesIcoSub hh hp
  have hvar := le_weighted_variance (B := primeBlockSub θ m)
    (w := fun p => ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (x := fun p => Real.cos (h * Real.log ((p : ℕ) : ℝ)))
    (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (hsubset h₁ h₂) (hsubset h₃ h₄)
    (fun p hp => ha _ (hcos hp).1 (hcos hp).2) (fun p hp => hb _ (hcos hp).1 (hcos hp).2) hab
    hW₀ (hweight hφ₁ h₁₂ h₂ hW₁) (hweight hφ₃ h₃₄ h₄ hW₂)
  have hQ : ∑ p ∈ primeBlockSub θ m,
      Real.cos (h * Real.log ((p : ℕ) : ℝ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m) / 2 := by
    rw [blockRpowSum, blockCosSum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.cos_sq, show 2 * (h * Real.log ((p : ℕ) : ℝ)) = 2 * h * Real.log ((p : ℕ) : ℝ) by
      ring]
    ring
  rw [hQ] at hvar
  exact hvar

/-- **The weight floor of a phase window** at `η = 1/200`: if `φ₂ ≥ 21φ₁/20` and
`10⁵h ≤ φ₁`, then `e^{-1/100}(log φ₂ − log φ₁ − 20h/φ₁) ≥ 1/25`. -/
lemma le_phaseWindow_weight {h φ₁ φ₂ : ℝ} (hh : 0 < h) (hφ₁ : 0 < φ₁) (hφ : 21 / 20 * φ₁ ≤ φ₂)
    (hhφ : 100000 * h ≤ φ₁) :
    1 / 25 ≤ Real.exp (-(2 * (1 / 200))) * (Real.log φ₂ - Real.log φ₁ - 20 * h / φ₁) := by
  have hφ₂ : 0 < φ₂ := by linarith
  have hlog : 1 - φ₁ / φ₂ ≤ Real.log φ₂ - Real.log φ₁ := by
    rw [← Real.log_div hφ₂.ne' hφ₁.ne']
    have := Real.one_sub_inv_le_log_of_pos (div_pos hφ₂ hφ₁)
    rwa [inv_div] at this
  have hratio : φ₁ / φ₂ ≤ 20 / 21 := by
    rw [div_le_div_iff₀ hφ₂ (by norm_num)]
    linarith
  have herr : 20 * h / φ₁ ≤ 1 / 5000 := by
    rw [div_le_div_iff₀ hφ₁ (by norm_num)]
    linarith
  have he : (99 / 100 : ℝ) ≤ Real.exp (-(2 * (1 / 200))) := by
    have := Real.add_one_le_exp (-(2 * (1 / 200)) : ℝ)
    linarith
  have hB : (1 : ℝ) / 21 - 1 / 5000 ≤ Real.log φ₂ - Real.log φ₁ - 20 * h / φ₁ := by linarith
  have hB0 : (0 : ℝ) ≤ 1 / 21 - 1 / 5000 := by norm_num
  calc (1 : ℝ) / 25 ≤ 99 / 100 * (1 / 21 - 1 / 5000) := by norm_num
    _ ≤ Real.exp (-(2 * (1 / 200))) * (Real.log φ₂ - Real.log φ₁ - 20 * h / φ₁) :=
        mul_le_mul he hB hB0 (Real.exp_pos _).le

/-- `cos ≥ cos φ₂` on `(φ₁, φ₂] ⊆ [0, π]`. -/
lemma cos_ge_cos_of_mem_Ioc {φ₁ φ₂ φ : ℝ} (h₁ : 0 ≤ φ₁) (h₂ : φ₂ ≤ Real.pi) (hφ₁ : φ₁ < φ)
    (hφ₂ : φ ≤ φ₂) : Real.cos φ₂ ≤ Real.cos φ :=
  Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h₂ hφ₂

/-- `cos ≤ cos φ₃` on `(φ₃, φ₄] ⊆ [0, π]`. -/
lemma cos_le_cos_of_mem_Ioc {φ₃ φ₄ φ : ℝ} (h₃ : 0 ≤ φ₃) (h₄ : φ₄ ≤ Real.pi) (hφ₃ : φ₃ < φ)
    (hφ₄ : φ ≤ φ₄) : Real.cos φ ≤ Real.cos φ₃ :=
  Real.cos_le_cos_of_nonneg_of_le_pi h₃ (by linarith) hφ₃.le

/-- `S ≥ 0.99`, `W₀ = 1/25`, `a − b ≥ g ≥ 0` and `d ≤ 0.99g²/100` turn a phase-window bound
`S·W₀(a−b)²/4 ≤ D` into `d ≤ D`. -/
private lemma det_of_phases_le {S D W₀ a b g d : ℝ} (hS : 0.99 ≤ S) (hW : W₀ = 1 / 25)
    (hg : 0 ≤ g) (hab : g ≤ a - b) (hd : d ≤ 0.99 * g ^ 2 / 100)
    (hD : S * W₀ * (a - b) ^ 2 / 4 ≤ D) : d ≤ D := by
  subst hW
  have h1 : g ^ 2 ≤ (a - b) ^ 2 := pow_le_pow_left₀ hg hab 2
  have h2 : 0.99 * g ^ 2 ≤ S * (a - b) ^ 2 := mul_le_mul hS h1 (sq_nonneg _) (by linarith)
  linarith

/-- The determinant's main term from ranges: `S ≥ 0.99`, `C ≥ l` with `0.99 + l ≥ 0` and
`|c| ≤ u` give `S(S + C)/2 − c² ≥ 0.99(0.99 + l)/2 − u²`. -/
private lemma le_blockVariance_of_ranges {S C c l u : ℝ} (hS1 : 0.99 ≤ S) (hC : l ≤ C)
    (hc : |c| ≤ u) (hl : 0 ≤ 0.99 + l) :
    0.99 * (0.99 + l) / 2 - u ^ 2 ≤ S * ((S + C) / 2) - c ^ 2 := by
  have hA : (0.99 + l) / 2 ≤ (S + C) / 2 := by linarith
  have hprod : 0.99 * ((0.99 + l) / 2) ≤ S * ((S + C) / 2) :=
    mul_le_mul hS1 hA (by linarith) (by linarith)
  have hc2 : c ^ 2 ≤ u ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  linarith

/-- Block `2` on the window: `c₂ ∈ [-0.2101, 0.3601]` and `C₂ ≥ -0.2601`, the certified ranges
widened by `blockCosErr + 1/100`. -/
private lemma blockCosSum_two_window_le {k : ℕ} {σ h : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + ((2 : ℕ) : ℝ) + 1) ≤ 1 / 200) :
    (-0.2101 ≤ blockCosSum k σ h 2 ∧ blockCosSum k σ h 2 ≤ 0.3601)
      ∧ -0.2601 ≤ blockCosSum k σ (2 * h) 2 := by
  obtain ⟨h0, hξ1, hξ2⟩ := log_add_mem_of_mem_halfWindow hh
  obtain ⟨hξd1, hξd2⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
  obtain ⟨he₁, he₂⟩ := blockCosErr_window_le (m := 2) hk hh
  have hδ : 2 * σ * Real.exp ((k : ℝ) + ((2 : ℕ) : ℝ) + 1) ≤ 1 / 100 := by linarith
  have hc := blockCosSum_mem_of_blockCos hσ h0 hδ (blockCos_two_bounds_one_point hξ1 hξ2)
  have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
    (blockCos_two_bounds_doubled hξd1 hξd2)
  exact ⟨⟨by linarith [hc.1], by linarith [hc.2]⟩, by linarith [hC.1]⟩

/-- Blocks `m ≥ 3` on the window: `|c_m|, |C_m| ≤ 3e^{-2} + 7.43·10⁻⁸ ≤ 0.4081`. -/
private lemma blockCosSum_ge_three_window_le {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ) (hm : 3 ≤ m) :
    |blockCosSum k σ h m| ≤ 0.4081 ∧ |blockCosSum k σ (2 * h) m| ≤ 0.4081 := by
  obtain ⟨hc, hC⟩ := abs_blockCosSum_le_window hh hσ m
  obtain ⟨he₁, he₂⟩ := blockCosErr_window_le (m := m) hk hh
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have he2 : Real.exp (1 - m) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
  have he2' : Real.exp (-2) ≤ 0.136 := by
    have h2 : (7.38 : ℝ) ≤ Real.exp 2 := by
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [hsq]
      nlinarith
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
    linarith
  exact ⟨hc.trans (by linarith), hC.trans (by linarith)⟩

/-- **The certified determinant floor of the window's blocks**: `1.67·10⁻⁴` on block `0`,
`7.76·10⁻⁴` on block `1`, `0.23` on block `2` and `0.12` on every block `m ≥ 3`
(`RMF.le_blockVariance_window_det`). -/
noncomputable def windowBlockDet : ℕ → ℝ
  | 0 => 1.67 / 10 ^ 4
  | 1 => 7.76 / 10 ^ 4
  | 2 => 0.23
  | _ + 3 => 0.12

/-- `windowBlockDet m ≥ 1.67·10⁻⁴` on every block. -/
lemma le_windowBlockDet (m : ℕ) : 1.67 / 10 ^ 4 ≤ windowBlockDet m := by
  match m with
  | 0 => norm_num [windowBlockDet]
  | 1 => norm_num [windowBlockDet]
  | 2 => norm_num [windowBlockDet]
  | _ + 3 => norm_num [windowBlockDet]

/-- `windowBlockDet m = 0.12` on every block `m ≥ 3`. -/
private lemma windowBlockDet_of_three_le {m : ℕ} (hm : 3 ≤ m) : windowBlockDet m = 0.12 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  rfl

/-- **The determinant's main term on the window, block by block**: for `k ≥ 20`,
`h ∈ halfWindow k`, `σ ≥ 0` and `σe^{k+m+1} ≤ 1/200`,
`S_m(S_m + C_m)/2 − c_m² ≥ windowBlockDet m + 10⁻¹⁰`.  Blocks `0` and `1` by two phase windows
each (split at `he^k = 0.6` and `he^{k+1} = 2`: `S·W₀(a−b)²/4 ≥ 0.99(a−b)²/100` with `a − b` at
least `0.13`, `0.37` on block `0` and `0.28`, `0.71` on block `1`), block `2` by the certified
ranges `c₂ ∈ [-0.2101, 0.3601]`, `C₂ ≥ -0.2601`, blocks `m ≥ 3` by `|c_m|, |C_m| ≤ 0.4081`. -/
theorem le_blockVariance_window_det {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) :
    windowBlockDet m + 1 / 10 ^ 10
      ≤ blockRpowSum k σ m * ((blockRpowSum k σ m + blockCosSum k σ (2 * h) m) / 2)
        - blockCosSum k σ h m ^ 2 := by
  obtain ⟨hS1, hS2⟩ := blockRpowSum_bounds hk hσ hσm
  obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
  have hhs := le_millionth_of_mem_halfWindow hk hh
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- blocks `0` and `1`: phase windows inside `(x₀e^m, x₀e^{m+1}]`, `x₀ = he^k ∈ [e^{-1}, 1]`
    set x₀ := h * Real.exp k with hx₀def
    have hx0l : Real.exp (-1) ≤ x₀ := by
      calc Real.exp (-1) = Real.exp (-((k : ℝ) + 1)) * Real.exp k := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ x₀ := mul_le_mul_of_nonneg_right hh.1 (Real.exp_pos _).le
    have hx0u : x₀ ≤ 1 := by
      calc x₀ ≤ Real.exp (-(k : ℝ)) * Real.exp k :=
            mul_le_mul_of_nonneg_right hh.2 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hxe : 1 ≤ x₀ * Real.exp 1 := by
      calc (1 : ℝ) = Real.exp (-1) * Real.exp 1 := by rw [← Real.exp_add]; simp
        _ ≤ x₀ * Real.exp 1 := mul_le_mul_of_nonneg_right hx0l (Real.exp_pos _).le
    have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have he1' : Real.exp 1 ≤ 2.7183 := by linarith [Real.exp_one_lt_d9]
    have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
    have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
    have hlo : ∀ j : ℕ, h * Real.exp ((j : ℝ) + k) = x₀ * Real.exp (j : ℝ) := fun j => by
      rw [hx₀def, mul_assoc, ← Real.exp_add, add_comm]
    have hhi : ∀ j : ℕ, h * Real.exp ((j : ℝ) + 1 + k) = x₀ * Real.exp (j : ℝ) * Real.exp 1 :=
      fun j => by
        rw [hx₀def, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        ring_nf
    have hη : |σ| * Real.exp ((m : ℝ) + 1 + (k : ℝ)) ≤ 1 / 200 := by
      rw [abs_of_nonneg hσ, show (m : ℝ) + 1 + (k : ℝ) = (k : ℝ) + m + 1 by ring]
      exact hσm
    have hW : ∀ {φ₁ φ₂ : ℝ}, 1 / 2 ≤ φ₁ → 21 / 20 * φ₁ ≤ φ₂ →
        1 / 25 ≤ Real.exp (-(2 * (1 / 200))) * (Real.log φ₂ - Real.log φ₁ - 20 * h / φ₁) :=
      fun hφ₁ hφ => le_phaseWindow_weight h0 (by linarith) hφ (by linarith)
    interval_cases m
    · -- block 0: `(x₀, x₀e]`
      rcases le_total x₀ 0.6 with hx | hx
      · -- `(0.6, 0.7]` against `(0.9, 1]`
        have hc1 : (0.76 : ℝ) ≤ Real.cos (7 / 10) := by interval_decide (trust := kernel)
        have hc2 : Real.cos (9 / 10) ≤ 0.63 := by interval_decide (trust := kernel)
        refine det_of_phases_le hS1 rfl (a := 0.76) (b := 0.63) (g := 0.13) (by norm_num)
          (by norm_num) (by norm_num [windowBlockDet])
          (le_blockVariance_of_phases (η := 1 / 200) (φ₁ := 6 / 10) (φ₂ := 7 / 10)
            (φ₃ := 9 / 10) (φ₄ := 1) h0 ?_ (by norm_num) ?_ ?_ (by norm_num) ?_
            (by linarith) (by linarith) hη ?_ ?_ (by norm_num) (by norm_num)
            (hW (by norm_num) (by norm_num)) (hW (by norm_num) (by norm_num)))
        · rw [hlo 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · rw [hhi 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · rw [hlo 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · rw [hhi 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · intro φ hφ₁ hφ₂
          exact hc1.trans (cos_ge_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂)
        · intro φ hφ₁ hφ₂
          exact (cos_le_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂).trans hc2
      · -- `(1, 1.1]` against `(1.5, 1.6]`
        have hc1 : (0.45 : ℝ) ≤ Real.cos (11 / 10) := by interval_decide (trust := kernel)
        have hc2 : Real.cos (3 / 2) ≤ 0.08 := by interval_decide (trust := kernel)
        have hxe' : (0.6 : ℝ) * 2.718 ≤ x₀ * Real.exp 1 :=
          mul_le_mul hx he1 (by norm_num) (by linarith)
        refine det_of_phases_le hS1 rfl (a := 0.45) (b := 0.08) (g := 0.37) (by norm_num)
          (by norm_num) (by norm_num [windowBlockDet])
          (le_blockVariance_of_phases (η := 1 / 200) (φ₁ := 1) (φ₂ := 11 / 10)
            (φ₃ := 3 / 2) (φ₄ := 16 / 10) h0 ?_ (by norm_num) ?_ ?_ (by norm_num) ?_
            (by linarith) (by linarith) hη ?_ ?_ (by norm_num) (by norm_num)
            (hW (by norm_num) (by norm_num)) (hW (by norm_num) (by norm_num)))
        · rw [hlo 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · rw [hhi 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · rw [hlo 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · rw [hhi 0, Nat.cast_zero, Real.exp_zero, mul_one]; linarith
        · intro φ hφ₁ hφ₂
          exact hc1.trans (cos_ge_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂)
        · intro φ hφ₁ hφ₂
          exact (cos_le_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂).trans hc2
    · -- block 1: `(y, ye]`, `y = x₀e ∈ [1, e]`
      have hy2 : x₀ * Real.exp 1 ≤ 2.7183 := by
        calc x₀ * Real.exp 1 ≤ 1 * Real.exp 1 :=
              mul_le_mul_of_nonneg_right hx0u (Real.exp_pos _).le
          _ ≤ 2.7183 := by linarith
      have hye : 1 * 2.718 ≤ x₀ * Real.exp 1 * Real.exp 1 :=
        mul_le_mul hxe he1 (by norm_num) (by linarith)
      rcases le_total (x₀ * Real.exp 1) 2 with hy | hy
      · -- `(2, 2.1]` against `(2.5, 2.7]`
        have hc1 : (-0.51 : ℝ) ≤ Real.cos (21 / 10) := by interval_decide (trust := kernel)
        have hc2 : Real.cos (5 / 2) ≤ -0.79 := by interval_decide (trust := kernel)
        refine det_of_phases_le hS1 rfl (a := -0.51) (b := -0.79) (g := 0.28) (by norm_num)
          (by norm_num) (by norm_num [windowBlockDet])
          (le_blockVariance_of_phases (η := 1 / 200) (φ₁ := 2) (φ₂ := 21 / 10)
            (φ₃ := 5 / 2) (φ₄ := 27 / 10) h0 ?_ (by norm_num) ?_ ?_ (by norm_num) ?_
            (by linarith) (by linarith) hη ?_ ?_ (by norm_num) (by norm_num)
            (hW (by norm_num) (by norm_num)) (hW (by norm_num) (by norm_num)))
        · rw [hlo 1, Nat.cast_one]; linarith
        · rw [hhi 1, Nat.cast_one]; linarith
        · rw [hlo 1, Nat.cast_one]; linarith
        · rw [hhi 1, Nat.cast_one]; linarith
        · intro φ hφ₁ hφ₂
          exact hc1.trans (cos_ge_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂)
        · intro φ hφ₁ hφ₂
          exact (cos_le_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂).trans hc2
      · -- `(4.5, 5.4]` (past `π`) against `(2.8, 3.1]`
        have hc1 : Real.cos (27 / 20) ≤ 0.23 := by interval_decide (trust := kernel)
        have hc2 : Real.cos (14 / 5) ≤ -0.94 := by interval_decide (trust := kernel)
        have hye' : 2 * 2.718 ≤ x₀ * Real.exp 1 * Real.exp 1 :=
          mul_le_mul hy he1 (by norm_num) (by linarith)
        refine det_of_phases_le hS1 rfl (a := -0.23) (b := -0.94) (g := 0.71) (by norm_num)
          (by norm_num) (by norm_num [windowBlockDet])
          (le_blockVariance_of_phases (η := 1 / 200) (φ₁ := 9 / 2) (φ₂ := 27 / 5)
            (φ₃ := 14 / 5) (φ₄ := 31 / 10) h0 ?_ (by norm_num) ?_ ?_ (by norm_num) ?_
            (by linarith) (by linarith) hη ?_ ?_ (by norm_num) (by norm_num)
            (hW (by norm_num) (by norm_num)) (hW (by norm_num) (by norm_num)))
        · rw [hlo 1, Nat.cast_one]; linarith
        · rw [hhi 1, Nat.cast_one]; linarith
        · rw [hlo 1, Nat.cast_one]; linarith
        · rw [hhi 1, Nat.cast_one]; linarith
        · intro φ hφ₁ hφ₂
          have hsub : Real.cos (φ - Real.pi) ≤ Real.cos (27 / 20) :=
            Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by linarith)
          rw [Real.cos_sub_pi] at hsub
          linarith
        · intro φ hφ₁ hφ₂
          exact (cos_le_cos_of_mem_Ioc (by norm_num) (by linarith) hφ₁ hφ₂).trans hc2
  · -- blocks `m ≥ 2`: from the ranges
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨⟨hc1, hc2⟩, hC⟩ := blockCosSum_two_window_le hk hh hσ hσm
      refine le_trans ?_ (le_blockVariance_of_ranges hS1 hC (abs_le.2 ⟨by linarith, hc2⟩)
        (by norm_num))
      norm_num [windowBlockDet]
    · obtain ⟨hc, hC⟩ := blockCosSum_ge_three_window_le hk hh hσ hm3
      rw [windowBlockDet_of_three_le hm3]
      refine le_trans ?_ (le_blockVariance_of_ranges hS1 (abs_le.1 hC).1 hc (by norm_num))
      norm_num

/-- **The determinant's main term on the window**: `S_m(S_m + C_m)/2 − c_m² ≥ 10⁻⁴` for every
block with `σe^{k+m+1} ≤ 1/200`, `k ≥ 20` (`RMF.le_blockVariance_window_det`, and
`RMF.windowBlockDet m ≥ 1.67·10⁻⁴`). -/
theorem le_blockVariance_window {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) :
    1 / 10000 ≤ blockRpowSum k σ m * ((blockRpowSum k σ m + blockCosSum k σ (2 * h) m) / 2)
        - blockCosSum k σ h m ^ 2 := by
  have h1 := le_blockVariance_window_det hk hh hσ hσm
  have h2 := le_windowBlockDet m
  have h3 : (1 : ℝ) / 10000 ≤ 1.67 / 10 ^ 4 := by norm_num
  have h4 : (0 : ℝ) ≤ 1 / 10 ^ 10 := by norm_num
  linarith

/-- **`C_m ≥ -0.77` on the window**, for every block with `σe^{k+m+1} ≤ 1/200`, `k ≥ 20`: blocks
`0`, `1` from the certified doubled ranges, blocks `m ≥ 2` as above. -/
theorem blockCosSum_two_mul_ge_window {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) :
    -0.77 ≤ blockCosSum k σ (2 * h) m := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
    obtain ⟨hξd1, hξd2⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
    have he := (blockCosErr_window_le (m := m) hk hh).2
    have hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 100 := by linarith
    interval_cases m
    · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
        (blockCos_zero_bounds_doubled hξd1 hξd2)
      linarith [hC.1]
    · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
        (blockCos_one_bounds_doubled hξd1 hξd2)
      linarith [hC.1]
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      linarith [(blockCosSum_two_window_le hk hh hσ hσm).2]
    · linarith [(abs_le.1 (blockCosSum_ge_three_window_le hk hh hσ hm3).2).1]

/-- Every block's `c_m` on the window lies in `[-0.7601, 0.8101]`, for `σe^{k+m+1} ≤ 1/200`,
`k ≥ 20`: blocks `0`, `1` from the certified ranges widened by `blockCosErr + 1/100`, blocks
`m ≥ 2` as above. -/
private lemma blockCosSum_window_mem {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) :
    -0.7601 ≤ blockCosSum k σ h m ∧ blockCosSum k σ h m ≤ 0.8101 := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain ⟨h0, hξ1, hξ2⟩ := log_add_mem_of_mem_halfWindow hh
    have he := (blockCosErr_window_le (m := m) hk hh).1
    have hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 100 := by linarith
    interval_cases m
    · have hc := blockCosSum_mem_of_blockCos hσ h0 hδ (blockCos_zero_bounds_one_point hξ1 hξ2)
      constructor <;> linarith [hc.1, hc.2]
    · have hc := blockCosSum_mem_of_blockCos hσ h0 hδ (blockCos_one_bounds_one_point hξ1 hξ2)
      constructor <;> linarith [hc.1, hc.2]
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨⟨hc1, hc2⟩, -⟩ := blockCosSum_two_window_le hk hh hσ hσm
      constructor <;> linarith
    · have hc := abs_le.1 (blockCosSum_ge_three_window_le hk hh hσ hm3).1
      constructor <;> linarith [hc.1, hc.2]

/-! ### The comparison's per-block inputs -/

/-- The determinant under perturbation: `V₁V₂ − K² ≥ AS − c² − 10ε` when `V₁, V₂, K` are within
`ε ≤ 1` of `A, S, c`, with `0 ≤ A, S ≤ 2` and `|c| ≤ 2`. -/
private lemma det_perturb_le {A S c V₁ V₂ K ε : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 2) (hS0 : 0 ≤ S)
    (hS : S ≤ 2) (hc : |c| ≤ 2) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (h₁ : |V₁ - A| ≤ ε) (h₂ : |V₂ - S| ≤ ε) (h₃ : |K - c| ≤ ε) :
    A * S - c ^ 2 - 10 * ε ≤ V₁ * V₂ - K ^ 2 := by
  have p1 : |A * (V₂ - S)| ≤ 2 * ε := by
    rw [abs_mul, abs_of_nonneg hA0]
    exact mul_le_mul hA h₂ (abs_nonneg _) (by norm_num)
  have p2 : |S * (V₁ - A)| ≤ 2 * ε := by
    rw [abs_mul, abs_of_nonneg hS0]
    exact mul_le_mul hS h₁ (abs_nonneg _) (by norm_num)
  have p3 : |(V₁ - A) * (V₂ - S)| ≤ ε := by
    rw [abs_mul]
    calc |V₁ - A| * |V₂ - S| ≤ ε * 1 := mul_le_mul h₁ (h₂.trans hε) (abs_nonneg _) hε0
      _ = ε := mul_one ε
  have p4 : |2 * c * (K - c)| ≤ 4 * ε := by
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |c| * |K - c| ≤ 2 * 2 * ε := by gcongr
      _ = 4 * ε := by ring
  have p5 : (K - c) ^ 2 ≤ ε := by
    rw [← sq_abs]
    calc |K - c| ^ 2 = |K - c| * |K - c| := sq _
      _ ≤ ε * 1 := mul_le_mul h₃ (h₃.trans hε) (abs_nonneg _) hε0
      _ = ε := mul_one ε
  have hid : V₁ * V₂ - K ^ 2 = A * S - c ^ 2 + A * (V₂ - S) + S * (V₁ - A)
      + (V₁ - A) * (V₂ - S) - 2 * c * (K - c) - (K - c) ^ 2 := by ring
  rw [hid]
  rw [abs_le] at p1 p2 p3 p4
  linarith [p1.1, p2.1, p3.1, p4.2]

/-- The comparison's per-block inputs on the window from a main-term bound
`d + 10⁻¹⁰ ≤ S_m(S_m + C_m)/2 − c_m²`: both one-point variances in `[1/100, 10]` and
`V₁V₂ − Cov² ≥ d` (the closed forms within `10⁻²⁰`, `RMF.det_perturb_le`). -/
private lemma window_block_inputs_of_main (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ}
    {σ h d : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y)
    (hdet : d + 1 / 10 ^ 10
      ≤ blockRpowSum k σ m * ((blockRpowSum k σ m + blockCosSum k σ (2 * h) m) / 2)
        - blockCosSum k σ h m ^ 2) :
    (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ) ≤ 10)
      ∧ (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ) ≤ 10)
      ∧ d ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        - blockMatchedCovAddT X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) ^ 2 := by
  have hm : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hV₁ := abs_blockMatchedVarAdd_height_sub_le hX y (h := h) hσ hm hB
  have hV₂ := abs_blockMatchedVarAdd_real_sub_le hX y (h := h) hσ hm hB
  have hK := abs_blockMatchedCovAddT_sub_le hX y (h := h) hσ hm hB
  obtain ⟨hS1, hS2⟩ := blockRpowSum_bounds hk hσ hσm
  have hSC := abs_le.1 (abs_blockCosSum_le_blockRpowSum (k : ℝ) σ (2 * h) m)
  have hcS := abs_blockCosSum_le_blockRpowSum (k : ℝ) σ h m
  have hC := blockCosSum_two_mul_ge_window hk hh hσ hσm
  generalize ((blockMatchedVarAdd X μ y (shiftLine σ h)
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ) = V₁ at *
  generalize ((blockMatchedVarAdd X μ y (shiftLine σ h)
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ) = V₂ at *
  generalize blockMatchedCovAddT X μ y (shiftLine σ h)
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) = K at *
  generalize blockRpowSum k σ m = S at *
  generalize blockCosSum k σ (2 * h) m = C at *
  generalize blockCosSum k σ h m = c at *
  have hp := det_perturb_le (A := (S + C) / 2) (S := S) (c := c) (V₁ := V₁) (V₂ := V₂) (K := K)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by norm_num) hV₁ hV₂ hK
  rw [abs_le] at hV₁ hV₂
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  have h10 : (10 : ℝ) * (1 / 10 ^ 20) ≤ 1 / 10 ^ 10 := by norm_num
  nlinarith

/-- **The comparison's per-block inputs on the window**: for `h ∈ halfWindow k`, `k ≥ 20`,
`σ ≥ 0` and `σe^{k+m+1} ≤ 1/200`, both one-point variances lie in `[1/100, 10]` and
`V₁V₂ − Cov² ≥ 10⁻⁶` (`RMF.le_blockVariance_window`). -/
theorem window_block_comparison_inputs (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ) ≤ 10)
      ∧ (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ) ≤ 10)
      ∧ 1 / 10 ^ 6 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        - blockMatchedCovAddT X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) ^ 2 :=
  window_block_inputs_of_main hX y hk hh hσ hσm hB
    (le_trans (by norm_num) (le_blockVariance_window hk hh hσ hσm))

/-- **The comparison's per-block inputs on the window, with the certified determinant**, at
`s₁ = s_h`, `s₂ = s_0`: for `h ∈ halfWindow k`, `k ≥ 20`, `σ ≥ 0` and `σe^{k+m+1} ≤ 1/200`, both
one-point variances lie in `[1/100, 10]` and `V₁V₂ − Cov² ≥ windowBlockDet m` (`1.67·10⁻⁴`,
`7.76·10⁻⁴`, `0.23` on blocks `0`, `1`, `2`, `0.12` beyond; `RMF.le_blockVariance_window_det`). -/
theorem window_block_comparison_inputs_det (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {k m : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ) ≤ 10)
      ∧ (1 / 100 ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd X μ y (shiftLine σ h)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ) ≤ 10)
      ∧ windowBlockDet m ≤ ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        - blockMatchedCovAddT X μ y (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub k m) ^ 2 :=
  window_block_inputs_of_main hX y hk hh hσ hσm hB (le_blockVariance_window_det hk hh hσ hσm)

/-- **The one-point block means on the window**: for `k ≥ 20`, `h ∈ halfWindow k`, `σ ≥ 0` and
`σe^{k+m+1} ≤ 1/200`, the height block's tilted mean (`S_m + C_m/2` within `10⁻²⁰`) is at most
`1.52` and the real block's (`2c_m − S_m/2`, with `c_m ∈ [-0.7601, 0.8101]`) at most `2.03` in
absolute value, at `s₁ = s_h`, `s₂ = s_0`. -/
theorem abs_window_block_means_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (primeBlockSub k m)| ≤ 1.52
      ∧ |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
        (primeBlockSub k m)| ≤ 2.03 := by
  have hm : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hMh := abs_le.1 (abs_blockMeanAdd_height_sub_le hX y (h := h) hσ hm hB)
  have hMr := abs_le.1 (abs_blockMeanAdd_real_sub_le hX y (h := h) hσ hm hB)
  obtain ⟨hS1, hS2⟩ := blockRpowSum_bounds hk hσ hσm
  have hC := blockCosSum_two_mul_ge_window hk hh hσ hσm
  have hCS := (abs_le.1 (abs_blockCosSum_le_blockRpowSum (k : ℝ) σ (2 * h) m)).2
  obtain ⟨hc1, hc2⟩ := blockCosSum_window_mem hk hh hσ hσm
  exact ⟨abs_le.2 ⟨by linarith [hMh.1], by linarith [hMh.2]⟩,
    abs_le.2 ⟨by linarith [hMr.1], by linarith [hMr.2]⟩⟩

end RMF
