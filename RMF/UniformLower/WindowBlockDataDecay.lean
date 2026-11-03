/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.WindowBlockData

/-!
# The window's block data, with errors decaying in the block

Twins of the closed forms of `RMF/UniformLower/WindowBlockData.lean` whose errors carry a factor
`e^{-m}` on block `m`, so that they stay summable against a barrier growing like `B(2m+1)` over
all blocks `m < r`.

* **The weights decay**: on block `m` past offset `20`, `‖p^{-s}‖ ≤ e^{-(m+θ)}/10⁴⁰` (the primes
  exceed `e^{e^{m+θ}}`), so for `θ ≥ 0` every cubic remainder is `e^{-m}10⁻⁴⁰` of the prime's
  weight and a block's remainders sum to at most `e^{-m}/10²⁰`.
* **Closed forms** (`σ, θ ≥ 0`, `m + θ ≥ 20`): the five block statistics within `e^{-m}/10²⁰`.
* **The cosine sums, two regimes** (`RMF.blockCosErrDecay`): explicit Mertens' `2Ke^{-(m+θ)} + Kτ`
  below scale `104` and `(τ+1)e^{104-(m+θ)}/10²⁸` from it, since the prime number theorem's term
  is at most `e^{104-x}/10²⁸` at `x = m + θ`; so `|c_m|, |C_m| ≤ 3e^{1-m} + RMF.blockCosErrDecay`
  on the window, which is `3e^{1-m} + e^{-m}/10²⁰` at most from `k ≥ 104`.
* **Summability**: `∑_m ce^{-m}(K + B(2m+1)) ≤ c(1.59K + 3.43B)` over any set of blocks, and
  `≤ ce^{-n}(1.59(K + 2Bn) + 3.43B)` over blocks `m ≥ n`.
-/

open MeasureTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The weights decay in the block -/

/-- `10⁸⁰(e^x)² ≤ e^{e^x}` for `x ≥ 20`. -/
lemma pow_eighty_mul_exp_sq_le_exp_exp {x : ℝ} (hx : 20 ≤ x) :
    (10 : ℝ) ^ 80 * Real.exp x ^ 2 ≤ Real.exp (Real.exp x) := by
  have h1 : 200 + 2 * x ≤ Real.exp x := by
    have h := Real.pow_div_factorial_le_exp (x := x) (by linarith) 3
    norm_num [Nat.factorial] at h
    have ht : 0 ≤ x - 20 := by linarith
    nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
  have h2 : (10 : ℝ) ^ 80 ≤ Real.exp 200 := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 200) (by norm_num) he (by norm_num)
  calc (10 : ℝ) ^ 80 * Real.exp x ^ 2 ≤ Real.exp 200 * Real.exp x ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = Real.exp (200 + 2 * x) := by rw [Real.exp_add, sq, ← Real.exp_add, two_mul]
    _ ≤ Real.exp (Real.exp x) := Real.exp_le_exp.2 h1

/-- **Past offset `20` the weights decay in the block**: `p^{-1-2σ} ≤ (e^{-(m+θ)}/10⁴⁰)²` on
block `m`, for `σ ≥ 0`. -/
lemma rpow_le_of_mem_primeBlockSub_decay {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hm : 20 ≤ (m : ℝ) + θ) {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) :
    ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ (Real.exp (-((m : ℝ) + θ)) / 10 ^ 40) ^ 2 := by
  rw [mem_primeBlockSub] at hp
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hbig : (10 : ℝ) ^ 80 * Real.exp ((m : ℝ) + θ) ^ 2 ≤ ((p : ℕ) : ℝ) := by
    refine le_trans ?_ hp.1.le
    rw [blockScale]
    exact pow_eighty_mul_exp_sq_le_exp_exp hm
  have hsq : (Real.exp (-((m : ℝ) + θ)) / 10 ^ 40) ^ 2
      = 1 / ((10 : ℝ) ^ 80 * Real.exp ((m : ℝ) + θ) ^ 2) := by
    rw [Real.exp_neg]
    field_simp
  calc ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / ((p : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / ((10 : ℝ) ^ 80 * Real.exp ((m : ℝ) + θ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hbig
    _ = (Real.exp (-((m : ℝ) + θ)) / 10 ^ 40) ^ 2 := hsq.symm

/-- **…so the local variables decay**: `‖p^{-s}‖ ≤ e^{-(m+θ)}/10⁴⁰` at `Re s = ½ + σ`. -/
lemma norm_cpow_le_of_mem_primeBlockSub_decay {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hm : 20 ≤ (m : ℝ) + θ) {s : ℂ} (hres : s.re = 1 / 2 + σ) {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 := by
  have h := rpow_le_of_mem_primeBlockSub_decay hσ hm hp
  rw [← norm_sq_prime_cpow_neg p hres] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- `‖p^{-s}‖³ ≤ e^{-m}10⁻⁴⁰·p^{-1-2σ}` for `θ ≥ 0`: a cubic remainder is `e^{-m}10⁻⁴⁰` of the
prime's weight. -/
lemma norm_cpow_pow_three_le_of_mem_primeBlockSub_decay {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ) {s : ℂ} (hres : s.re = 1 / 2 + σ) {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  have hr : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 :=
    (norm_cpow_le_of_mem_primeBlockSub_decay hσ hm hres hp).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by positivity))
  rw [← norm_sq_prime_cpow_neg p hres,
    show ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 = ‖((p : ℕ) : ℂ) ^ (-s)‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

/-- **A per-prime error of `C·e^{-m}10⁻⁴⁰·p^{-1-2σ}` sums to at most `e^{-m}/10²⁰`** over a block
past offset `20`, for `C ≤ 1000`. -/
lemma sum_primeBlockSub_le_of_le_mul_rpow_decay {θ σ C : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hm : 20 ≤ (m : ℝ) + θ) (hC : C ≤ 1000) {f : Nat.Primes → ℝ}
    (hf : ∀ p ∈ primeBlockSub θ m,
      f p ≤ C * (Real.exp (-(m : ℝ)) / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))) :
    ∑ p ∈ primeBlockSub θ m, f p ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hS := blockRpowSum_le hσ (by linarith : (16 : ℝ) ≤ (m : ℝ) + θ)
  have hS0 := blockRpowSum_nonneg θ σ m
  have he : 0 ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
  calc ∑ p ∈ primeBlockSub θ m, f p
      ≤ ∑ p ∈ primeBlockSub θ m,
          C * (Real.exp (-(m : ℝ)) / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :=
        Finset.sum_le_sum hf
    _ = C * Real.exp (-(m : ℝ)) / 10 ^ 40 * blockRpowSum θ σ m := by
        rw [blockRpowSum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ 1000 * Real.exp (-(m : ℝ)) / 10 ^ 40 * (1 + 1 / 150000) := by gcongr
    _ = Real.exp (-(m : ℝ)) * (1000 / 10 ^ 40 * (1 + 1 / 150000)) := by ring
    _ ≤ Real.exp (-(m : ℝ)) * (1 / 10 ^ 20) := mul_le_mul_of_nonneg_left (by norm_num) he
    _ = Real.exp (-(m : ℝ)) / 10 ^ 20 := by ring

/-- The per-prime remainders of the moments against `r³ ≤ E`, `r ≤ 1`: the variance's
`42r³ + 48r²r²`, the mean's `36r³ + 2r³r` and the covariance's `60r⁴` (the private
`RMF.remainders_le` of `RMF/UniformLower/WindowBlockData.lean`, repeated). -/
private lemma moment_remainders_le {r E : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hE : r ^ 3 ≤ E) :
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

/-! ### The block statistics in closed form, decaying -/

/-- **The height block's variance** under the tilt at `s₁ = ½+σ+ih`: `(S_m + C_m)/2` up to
`e^{-m}/10²⁰`, for any `h`, `σ, θ ≥ 0` and `m + θ ≥ 20`. -/
theorem abs_blockMatchedVarAdd_height_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |((blockMatchedVarAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (primeBlockSub θ m) : ℝ≥0) : ℝ) - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m) / 2|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hres := re_shiftLine σ h
  have hs : 0 < (shiftLine σ h).re := by rw [hres]; linarith
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
    fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp).trans (by norm_num)
  rw [sum_re_cpow_shiftLine_sq_eq] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp
  exact (moment_remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm hres hp)).1

/-- **The real block's variance** under the tilt at `s₁ = ½+σ+ih`: `S_m` up to `e^{-m}/10²⁰`. -/
theorem abs_blockMatchedVarAdd_real_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |((blockMatchedVarAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
        (primeBlockSub θ m) : ℝ≥0) : ℝ) - blockRpowSum θ σ m|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp).trans
      (by norm_num)
  rw [sum_re_cpow_neg_sq_primeBlockSub_eq_of_im_zero θ σ m (re_shiftLine σ 0)
    (im_shiftLine σ 0)] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp
  rw [norm_cpow_shiftLine_eq p σ h 0]
  exact (moment_remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ 0) hp)).1

/-- The one-point covariance's algebra: `(1 − 4κ²)(Δ_v/2)(Δ_w/2)` against `uv`, when `Δ_v`,
`Δ_w` are within `24r³` of `2u`, `2v` and `|κ|, |u|, |v| ≤ r ≤ 1/5` (the private
`RMF.abs_tilt_cov_sub_le` of `RMF/UniformLower/WindowBlockData.lean`, repeated). -/
private lemma abs_tilt_cov_algebra_le {κ Δv Δw u v r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 5)
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
to `e^{-m}/10²⁰`. -/
theorem abs_blockMatchedCovAddT_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMatchedCovAddT X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (primeBlockSub θ m)
      - blockCosSum θ σ h m| ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  rw [blockMatchedCovAddT_eq hX y hs hB, blockCosSum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm
    (C := 90) (by norm_num) fun p hp => ?_)
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
  have key := abs_tilt_cov_algebra_le (norm_nonneg _) hr5 hκ (Complex.abs_re_le_norm _)
    (hnw ▸ Complex.abs_re_le_norm _) (abs_localLogAdd_diff_sub_le hr5) hDw
  exact key.trans ((moment_remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ h) hp)).2.2)

/-- **The real block's tilted mean** under the tilt at `s₁ = ½+σ+ih`: `2c_m − S_m/2` up to
`e^{-m}/10²⁰`. -/
theorem abs_blockMeanAdd_real_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
        (primeBlockSub θ m) - (2 * blockCosSum θ σ h m - blockRpowSum θ σ m / 2)|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
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
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp
  rw [norm_cpow_shiftLine_eq p σ h 0]
  exact (moment_remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ 0) hp)).2.1

/-- **The height block's tilted mean** under its own tilt: `S_m + C_m/2` up to `e^{-m}/10²⁰`. -/
theorem abs_blockMeanAdd_height_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y (shiftLine σ h) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
        (primeBlockSub θ m) - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m / 2)|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
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
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 90) (by norm_num)
    fun p hp => ?_)
  have hr := norm_cpow_le_of_mem_primeBlockSub hσ hm hres hp
  exact (moment_remainders_le (norm_nonneg _) (hr.trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm hres hp)).2.1

/-! ### The cosine sums, decaying -/

/-- **The explicit prime number theorem's term decays past the floor**:
`32·10⁴⁰·exp(-e^{x/10}/200) ≤ e^{104-x}/10²⁸` for `x ≥ 104` (at `x = 104` this is
`RMF.pnt_term_at_floor_le`, and the exponent `e^{x/10}/200` grows faster than `x`). -/
lemma pnt_term_le_exp_sub {x : ℝ} (hx : 104 ≤ x) :
    32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp (x / 10))
      ≤ Real.exp (104 - x) / 10 ^ 28 := by
  have h1 : (2000 : ℝ) ≤ Real.exp 10.4 := by interval_decide (trust := kernel)
  have hsplit : Real.exp (x / 10) = Real.exp 10.4 * Real.exp ((x - 104) / 10) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
    ring
  have h2 : 1 + (x - 104) / 10 ≤ Real.exp ((x - 104) / 10) := by
    linarith [Real.add_one_le_exp ((x - 104) / 10)]
  have h3 : Real.exp 10.4 * (1 + (x - 104) / 10) ≤ Real.exp 10.4 * Real.exp ((x - 104) / 10) :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have h4 : 2000 * ((x - 104) / 10) ≤ Real.exp 10.4 * ((x - 104) / 10) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h5 : Real.exp (-(1 / 200 : ℝ) * Real.exp (x / 10))
      ≤ Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4) * Real.exp (104 - x) := by
    rw [← Real.exp_add, hsplit]
    exact Real.exp_le_exp.2 (by linarith)
  calc 32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp (x / 10))
      ≤ 32 * 10 ^ (40 : ℕ) * (Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4) * Real.exp (104 - x)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4) * Real.exp (104 - x) := by
        ring
    _ ≤ 1 / 10 ^ 28 * Real.exp (104 - x) :=
        mul_le_mul_of_nonneg_right pnt_term_at_floor_le (Real.exp_pos _).le
    _ = Real.exp (104 - x) / 10 ^ 28 := by ring

/-- **The block cosine sum as its log-integral, decaying**:
`RMF.abs_sum_cos_primeBlockSub_sub_integral_le` with the error `(τ+1)e^{104-(m+θ)}/10²⁸` in place
of `(τ+1)/10²⁸` (`RMF.pnt_term_le_exp_sub` for the value at the floor). -/
theorem abs_sum_cos_primeBlockSub_sub_integral_le_decay (τ σ θ : ℝ) (m : ℕ) (hτ : 0 ≤ τ)
    (hσ0 : 0 ≤ σ) (hm : 104 ≤ (m : ℝ) + θ) :
    |(∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ (τ + 1) * Real.exp (104 - ((m : ℝ) + θ)) / 10 ^ 28 := by
  obtain ⟨hx₀2, hEθ⟩ := abs_theta_sub_le_exp_numeral_explicit
  have hthr : Real.log (Real.log blockCosineThreshold) ≤ (m : ℝ) + θ :=
    le_trans log_log_blockCosineThreshold_le_104 hm
  have hy₀2 : (2 : ℝ) ≤ blockCosineThreshold := le_trans hx₀2 (le_max_left _ _)
  have hXpos : (0 : ℝ) < blockScale θ (m + 1) := blockScale_pos θ (m + 1)
  set y₁ : ℝ := blockScale θ (m + 1) ^ (Real.exp 1)⁻¹ with hy₁def
  have hlogX : Real.log (blockScale θ (m + 1)) = Real.exp ((m : ℝ) + θ + 1) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hlogy₁ : Real.log y₁ = Real.exp ((m : ℝ) + θ) := by
    rw [hy₁def, Real.log_rpow hXpos, hlogX, show (m : ℝ) + θ + 1 = 1 + ((m : ℝ) + θ) by ring,
      Real.exp_add]
    field_simp
  have hy₁pos : (0 : ℝ) < y₁ := Real.rpow_pos_of_pos hXpos _
  have hy₀0 : (0 : ℝ) < Real.log blockCosineThreshold := Real.log_pos (by linarith)
  have hy₀y₁ : blockCosineThreshold ≤ y₁ := by
    have hle : Real.log blockCosineThreshold ≤ Real.log y₁ := by
      rw [hlogy₁, ← Real.exp_log hy₀0]
      exact Real.exp_le_exp.2 hthr
    have h := Real.exp_le_exp.2 hle
    rwa [Real.exp_log (by linarith : (0 : ℝ) < blockCosineThreshold),
      Real.exp_log hy₁pos] at h
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hy₀2 hy₀y₁
  have hy₁y₂ : y₁ ≤ blockScale θ (m + 1) := by
    rw [← Real.exp_log hy₁pos, ← Real.exp_log hXpos, hlogy₁, hlogX]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
  have hratio : Real.log (blockScale θ (m + 1)) ≤ 3 * Real.log y₁ := by
    rw [hlogX, hlogy₁, show (m : ℝ) + θ + 1 = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    have hpos : (0 : ℝ) < Real.exp ((m : ℝ) + θ) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_d9]
  -- the sum over the block, as a sum over `(y₁, y₂]`
  have hrw : ∀ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [Finset.sum_congr rfl hrw]
  have hrw2 : (∑ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [primeBlockSub, harperBlock,
      sum_primesIcoSub _ _ fun q => Real.cos (τ * Real.log (q : ℝ)) / ((q : ℝ)) ^ (1 + 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw2]
  -- the integral, in the `u = log t` form
  rw [← hlogy₁, ← hlogX, ← integral_cosLogDiv_mul_rpow_eq (by linarith) hy₁y₂]
  -- the unweighted bound on every initial sub-block
  set Mb : ℝ := 32 * 10 ^ (40 : ℕ) * (τ + 1)
      * Real.exp (-(1 / 200 : ℝ) * Real.log y₁ ^ ((1 : ℝ) / 10)) with hMbdef
  have hsub : ∀ u ∈ Set.Icc y₁ (blockScale θ (m + 1)),
      |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
          - ∫ t in y₁..u, cosLogDiv τ t| ≤ Mb := by
    intro u hu
    exact abs_cos_prime_sum_block_sub_integral_le_threshold_of_le (by norm_num) (by positivity)
      hx₀2 hEθ hτ hy₀y₁ hu.1 (le_trans (Real.log_le_log (by linarith [hu.1]) hu.2) hratio)
  refine (abs_sum_sub_integral_weight_le_of_nonneg hy₁2 hy₁y₂ hσ0 hsub).trans ?_
  -- the numeral
  have hEeq : Real.log y₁ ^ ((1 : ℝ) / 10) = Real.exp (((m : ℝ) + θ) / 10) := by
    rw [hlogy₁, ← Real.exp_mul]
    ring_nf
  have hτ1 : (0 : ℝ) ≤ τ + 1 := by linarith
  rw [hMbdef, hEeq]
  calc 32 * 10 ^ (40 : ℕ) * (τ + 1) * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      = (τ + 1) * (32 * 10 ^ (40 : ℕ)
          * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))) := by ring
    _ ≤ (τ + 1) * (Real.exp (104 - ((m : ℝ) + θ)) / 10 ^ 28) :=
        mul_le_mul_of_nonneg_left (pnt_term_le_exp_sub hm) hτ1
    _ = (τ + 1) * Real.exp (104 - ((m : ℝ) + θ)) / 10 ^ 28 := by ring

/-- **The block cosine error, two regimes, decaying past the floor**: `(τ+1)e^{104-(m+θ)}/10²⁸`
for `m + θ ≥ 104` — the error of `RMF.abs_sum_cos_primeBlockSub_sub_integral_le_decay` — and
Mertens' `2Ke^{-(m+θ)} + Kτ` below. -/
noncomputable def blockCosErrDecay (θ : ℝ) (m : ℕ) (τ : ℝ) : ℝ :=
  if 104 ≤ (m : ℝ) + θ then (τ + 1) * Real.exp (104 - ((m : ℝ) + θ)) / 10 ^ 28
  else 2 * mertensErrConst * Real.exp (-((m : ℝ) + θ)) + mertensErrConst * τ

/-- The decaying error is at most the flat one. -/
lemma blockCosErrDecay_le_blockCosErr {θ τ : ℝ} (m : ℕ) (hτ : 0 ≤ τ) :
    blockCosErrDecay θ m τ ≤ blockCosErr θ m τ := by
  unfold blockCosErrDecay blockCosErr
  split_ifs with h
  · have he : Real.exp (104 - ((m : ℝ) + θ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hτ1 : (0 : ℝ) ≤ τ + 1 := by linarith
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hτ1 he) (by positivity)
  · exact le_rfl

/-- **…decaying past the floor**: within `blockCosErrDecay θ m τ` — the twin of
`RMF.abs_sum_cos_primeBlockSub_sub_integral_le_decay`, which it is for `m + θ ≥ 104`. -/
theorem abs_sum_cos_primeBlockSub_sub_integral_le_decay_two_regime (τ σ θ : ℝ) (m : ℕ)
    (hτ : 0 ≤ τ) (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |(∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ blockCosErrDecay θ m τ := by
  unfold blockCosErrDecay
  split_ifs with h
  · exact abs_sum_cos_primeBlockSub_sub_integral_le_decay τ σ θ m hτ hσ0 h
  · exact abs_sum_cos_primeBlockSub_sub_integral_le_mertens τ σ θ m hτ hσ0 hm

/-- **The block cosine sum, two regimes, decaying past the floor, sharp main term**:
`|C_m(τ)| ≤ 2/(τe^{m+θ}) + blockCosErrDecay θ m τ` for `τ > 0`, `σ ≥ 0`, `m + θ ≥ 0`. -/
theorem abs_sum_cos_primeBlockSub_le_decay_two_regime (τ σ θ : ℝ) (m : ℕ) (hτ : 0 < τ)
    (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 2 / (τ * Real.exp ((m : ℝ) + θ)) + blockCosErrDecay θ m τ :=
  abs_sum_cos_primeBlockSub_le_of_sub_integral_le hτ hσ0
    (abs_sum_cos_primeBlockSub_sub_integral_le_decay_two_regime τ σ θ m hτ.le hσ0 hm)

/-- **The block cosine sum, two regimes, decaying past the floor**: for `τ > 0`, `σ ≥ 0` and
`m + θ ≥ 0`, `|C_m(τ)| ≤ 3/(τe^{m+θ}) + blockCosErrDecay θ m τ`. -/
theorem abs_sum_cos_primeBlockSub_le_explicit_floor_decay_two_regime (τ σ θ : ℝ) (m : ℕ)
    (hτ : 0 < τ) (hσ0 : 0 ≤ σ) (hm : 0 ≤ (m : ℝ) + θ) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 3 / (τ * Real.exp ((m : ℝ) + θ)) + blockCosErrDecay θ m τ := by
  refine (abs_sum_cos_primeBlockSub_le_decay_two_regime τ σ θ m hτ hσ0 hm).trans ?_
  have h23 : 2 / (τ * Real.exp ((m : ℝ) + θ)) ≤ 3 / (τ * Real.exp ((m : ℝ) + θ)) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- **Every block's cosine sum decays, error included**: for `e^{-(k+1)} ≤ τ` (the window's `h`
and `2h`), `|∑_{p∈B_m} cos(τ log p)p^{-1-2σ}| ≤ 3e^{1-m} + blockCosErrDecay k m τ`
(`RMF.abs_sum_cos_primeBlockSub_le_explicit_floor_decay_two_regime`); from `k ≥ 104` the error is
at most `e^{-m}/10²⁰` for `τ ≤ 2`. -/
theorem abs_blockCosSum_le_exp_decay {k : ℕ} {σ τ : ℝ} (hσ : 0 ≤ σ)
    (hτ : Real.exp (-((k : ℝ) + 1)) ≤ τ) (m : ℕ) :
    |blockCosSum k σ τ m| ≤ 3 * Real.exp (1 - m) + blockCosErrDecay k m τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have h := abs_sum_cos_primeBlockSub_le_explicit_floor_decay_two_regime τ σ k m hτ0 hσ
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

/-- **The window's cosine sums decay, error included**:
`|c_m| ≤ 3e^{1-m} + blockCosErrDecay k m h` and `|C_m| ≤ 3e^{1-m} + blockCosErrDecay k m (2h)` for
every block — at most `3e^{1-m} + e^{-m}/10²⁰` from `k ≥ 104`. -/
theorem abs_blockCosSum_le_window_decay {k : ℕ} {σ h : ℝ} (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (m : ℕ) :
    |blockCosSum k σ h m| ≤ 3 * Real.exp (1 - m) + blockCosErrDecay k m h
      ∧ |blockCosSum k σ (2 * h) m| ≤ 3 * Real.exp (1 - m) + blockCosErrDecay k m (2 * h) := by
  have h0 := (log_add_mem_of_mem_halfWindow hh).1
  exact ⟨abs_blockCosSum_le_exp_decay hσ hh.1 m,
    abs_blockCosSum_le_exp_decay hσ (by linarith [hh.1]) m⟩

/-! ### Summing the decay over the blocks -/

/-- `∑_{m∈s} e^{-m} ≤ e/(e-1)`, the full geometric series. -/
lemma sum_exp_neg_le (s : Finset ℕ) :
    ∑ m ∈ s, Real.exp (-(m : ℝ)) ≤ Real.exp 1 / (Real.exp 1 - 1) := by
  have hq0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hq1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hE : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
  have hsum := sum_le_hasSum s (fun i _ => pow_nonneg hq0 i) (hasSum_geometric_of_lt_one hq0 hq1)
  have heq : ∀ m ∈ s, Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := fun m _ => by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [Finset.sum_congr rfl heq]
  refine hsum.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- `∑_{m∈s} m e^{-m} ≤ e/(e-1)²`. -/
lemma sum_mul_exp_neg_le (s : Finset ℕ) :
    ∑ m ∈ s, (m : ℝ) * Real.exp (-(m : ℝ)) ≤ Real.exp 1 / (Real.exp 1 - 1) ^ 2 := by
  have hq0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hq1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hE : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
  have hnorm : ‖Real.exp (-1)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hsum := sum_le_hasSum s (fun i _ => mul_nonneg (Nat.cast_nonneg i) (pow_nonneg hq0 i))
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm)
  have heq : ∀ m ∈ s, (m : ℝ) * Real.exp (-(m : ℝ)) = (m : ℝ) * Real.exp (-1) ^ m :=
    fun m _ => by
      rw [← Real.exp_nat_mul]
      ring_nf
  rw [Finset.sum_congr rfl heq]
  refine hsum.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- **A decay `c·e^{-m}` is summable against a linear barrier**: for `c, K, B ≥ 0` and any set `s`
of blocks, `∑_{m∈s} ce^{-m}(K + B(2m+1)) ≤ c((K+B)e/(e-1) + 2Be/(e-1)²)`. -/
theorem sum_mul_exp_neg_mul_le {c K B : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (s : Finset ℕ) :
    ∑ m ∈ s, c * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
      ≤ c * ((K + B) * (Real.exp 1 / (Real.exp 1 - 1))
          + 2 * B * (Real.exp 1 / (Real.exp 1 - 1) ^ 2)) := by
  have hterm : ∀ m ∈ s, c * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
      = c * ((K + B) * Real.exp (-(m : ℝ)) + 2 * B * ((m : ℝ) * Real.exp (-(m : ℝ)))) :=
    fun m _ => by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc
  · exact mul_le_mul_of_nonneg_left (sum_exp_neg_le s) (by linarith)
  · exact mul_le_mul_of_nonneg_left (sum_mul_exp_neg_le s) (by linarith)

/-- **…in numerals**: at most `c(1.59K + 3.43B)`, by `e/(e-1) ≤ 1.5821` and `e/(e-1)² ≤ 0.921`. -/
theorem sum_mul_exp_neg_mul_le_numeral {c K B : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (s : Finset ℕ) :
    ∑ m ∈ s, c * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1)) ≤ c * (1.59 * K + 3.43 * B) := by
  refine (sum_mul_exp_neg_mul_le hc hK hB s).trans (mul_le_mul_of_nonneg_left ?_ hc)
  have he1 : (2.7182 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hu : Real.exp 1 / (Real.exp 1 - 1) ≤ 1.5821 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hv : Real.exp 1 / (Real.exp 1 - 1) ^ 2 ≤ 0.921 := by
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ K + B)
  have h2 := mul_le_mul_of_nonneg_left hv (by linarith : 0 ≤ 2 * B)
  linarith

/-- **…and its tail**: if every block of `s` is at least `n`, the sum is at most
`ce^{-n}(1.59(K + 2Bn) + 3.43B)` (blocks `m = n + j`, barrier `(K + 2Bn) + B(2j+1)`). -/
theorem sum_mul_exp_neg_mul_le_numeral_of_le {c K B : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hB : 0 ≤ B) {n : ℕ} {s : Finset ℕ} (hs : ∀ m ∈ s, n ≤ m) :
    ∑ m ∈ s, c * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
      ≤ c * Real.exp (-(n : ℝ)) * (1.59 * (K + 2 * B * n) + 3.43 * B) := by
  have hinj : Set.InjOn (fun m => m - n) (s : Set ℕ) := by
    intro a ha b hb hab
    have ha' := hs a ha
    have hb' := hs b hb
    simp only at hab
    omega
  have hterm : ∀ m ∈ s, c * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
      = c * Real.exp (-(n : ℝ)) * Real.exp (-((m - n : ℕ) : ℝ))
        * ((K + 2 * B * n) + B * (2 * ((m - n : ℕ) : ℝ) + 1)) := by
    intro m hm
    have he : Real.exp (-(m : ℝ)) = Real.exp (-(n : ℝ)) * Real.exp (-((m - n : ℕ) : ℝ)) := by
      rw [Nat.cast_sub (hs m hm), ← Real.exp_add]
      ring_nf
    rw [he, Nat.cast_sub (hs m hm)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_image (g := fun m => m - n)
    (f := fun j : ℕ => c * Real.exp (-(n : ℝ)) * Real.exp (-(j : ℝ))
      * ((K + 2 * B * n) + B * (2 * (j : ℝ) + 1))) hinj]
  exact sum_mul_exp_neg_mul_le_numeral (by positivity) (by positivity) hB _

end RMF
