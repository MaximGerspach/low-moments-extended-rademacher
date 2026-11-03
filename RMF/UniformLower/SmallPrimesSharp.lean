/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SmallPrimesQ
import RMF.Weighted.TwoPointAboveHalfExplicit

/-!
# (C2) at exponent `q`, sharp, over all the small primes

For `k ≥ 20`, `σ ≥ 0`, `0 ≤ h_i ≤ e^{-k}` and `0 ≤ q ≤ 1`, over every prime below `scaleCut k`:
`E[‖F(σ+ih₁)‖²‖F(σ+ih₂)‖²‖F(σ)‖^{2q-4}] ≤ e^{2(1-q)+0.50001}·E‖F(σ)‖^{2q}`
(`RMF.integral_twistQ_pair_le_sharp`).

* **One prime** (`RMF.twistQ_pair_atoms_le_sharp`): with `u = p^{-1/2-σ}` and
  `d_i = 1 - cos(h_i log p)`, the ratio to `E|1+Xu|^{2q}` is at most
  `1 + 4(1-q)u²(d₁+d₂)/(1-u²)² + 4u²d₁d₂/(1-u)⁴`: the first term is the sharp bracket
  `RMF.rpow_sub_rpow_le_sharp_of_le_one`, and in the second the weights `(1±u)^{2q-4}` are those
  of `E|1+Xu|^{2q}` times `(1±u)^{-4} ≤ (1-u)^{-4}`.
* **The prime sum**: `d_i ≤ (h_i log p)²/2 ≤ e^{-2k}(log p)²/2 ≤ 1/2`, so the two terms are at
  most `4(1-q)` and `1` times `e^{-2k}(log p)²/p`, and `e^{-2k}∑_p(log p)²/p ≤ 1/2 + O(e^{-k})`
  (`RMF.sum_log_sq_div_primesBelow_le_sharp`).  The factors `(1-u²)^{-2}` and `(1-u)^{-4}` add at
  most `1120e^{-2k}(log p)/p` per prime (`RMF.twistQ_pair_coeff_le`), `O(e^{-k})` in all by
  Mertens (`RMF.sum_log_div_primesBelow_le`).
-/

open MeasureTheory

namespace RMF

/-! ### One prime -/

/-- **The two atoms of the doubly twisted weight at exponent `q`, sharp.**  For `0 ≤ u < 1`,
`0 ≤ q ≤ 1` and `d_i ≥ 0`, their average is at most `E|1+Xu|^{2q}` times
`1 + 4(1-q)u²(d₁+d₂)/(1-u²)² + 4u²d₁d₂/(1-u)⁴`. -/
lemma twistQ_pair_atoms_le_sharp {u d₁ d₂ q : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) * (1 + u) ^ (2 * q - 4)
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) * (1 - u) ^ (2 * q - 4)) / 2
      ≤ ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)) / 2
        * (1 + 4 * (1 - q) * u ^ 2 * (d₁ + d₂) / (1 - u ^ 2) ^ 2
          + 4 * u ^ 2 * d₁ * d₂ / (1 - u) ^ 4) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  have hpow : ∀ {v : ℝ}, 0 < v → ∀ n : ℕ, v ^ (2 * q - 4 + n) = v ^ (2 * q - 4) * v ^ n := by
    intro v hv n
    rw [Real.rpow_add hv, Real.rpow_natCast]
  have ha4 : (1 + u) ^ (2 * q) = (1 + u) ^ (2 * q - 4) * (1 + u) ^ 4 := by
    rw [← hpow h1 4]
    norm_num
  have hb4 : (1 - u) ^ (2 * q) = (1 - u) ^ (2 * q - 4) * (1 - u) ^ 4 := by
    rw [← hpow h2 4]
    norm_num
  have ha2 : (1 + u) ^ (2 * q - 4) * (1 + u) ^ 2 = (1 + u) ^ (2 * q - 2) := by
    rw [← hpow h1 2]
    congr 1
    push_cast
    ring
  have hb2 : (1 - u) ^ (2 * q - 4) * (1 - u) ^ 2 = (1 - u) ^ (2 * q - 2) := by
    rw [← hpow h2 2]
    congr 1
    push_cast
    ring
  -- the mean of the two atoms
  have hid : (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) * (1 + u) ^ (2 * q - 4)
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) * (1 - u) ^ (2 * q - 4)) / 2
      = ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)) / 2
        + u * (d₁ + d₂) * ((1 - u) ^ (2 * q - 4) * (1 - u) ^ 2
          - (1 + u) ^ (2 * q - 4) * (1 + u) ^ 2)
        + 2 * u ^ 2 * d₁ * d₂ * ((1 + u) ^ (2 * q - 4) + (1 - u) ^ (2 * q - 4)) := by
    rw [ha4, hb4]
    ring
  have ha : (1 + u) ^ (2 * q - 4) = (1 + u) ^ (2 * q) / (1 + u) ^ 4 :=
    eq_div_of_mul_eq (by positivity) ha4.symm
  have hb : (1 - u) ^ (2 * q - 4) = (1 - u) ^ (2 * q) / (1 - u) ^ 4 :=
    eq_div_of_mul_eq (by positivity) hb4.symm
  have hbr := rpow_sub_rpow_le_sharp_of_le_one hu0 hu1 hq0 hq1
  set A : ℝ := (1 + u) ^ (2 * q) with hA_def
  set B : ℝ := (1 - u) ^ (2 * q) with hB_def
  have hA0 : 0 ≤ A := Real.rpow_nonneg h1.le _
  have hB0 : 0 ≤ B := Real.rpow_nonneg h2.le _
  -- the weights: `(1+u)^{2q-4} + (1-u)^{2q-4} ≤ (A + B)/(1-u)⁴`
  have hab : (1 + u) ^ (2 * q - 4) + (1 - u) ^ (2 * q - 4) ≤ (A + B) / (1 - u) ^ 4 := by
    rw [ha, hb, add_div]
    have h4 : (1 - u) ^ 4 ≤ (1 + u) ^ 4 := pow_le_pow_left₀ h2.le (by linarith) 4
    have : A / (1 + u) ^ 4 ≤ A / (1 - u) ^ 4 :=
      div_le_div_of_nonneg_left hA0 (by positivity) h4
    linarith
  have t1 : u * (d₁ + d₂) * ((1 - u) ^ (2 * q - 2) - (1 + u) ^ (2 * q - 2))
      ≤ u * (d₁ + d₂) * (2 * (1 - q) * u / (1 - u ^ 2) ^ 2 * (A + B)) :=
    mul_le_mul_of_nonneg_left hbr (mul_nonneg hu0 (add_nonneg hd₁ hd₂))
  have t2 : 2 * u ^ 2 * d₁ * d₂ * ((1 + u) ^ (2 * q - 4) + (1 - u) ^ (2 * q - 4))
      ≤ 2 * u ^ 2 * d₁ * d₂ * ((A + B) / (1 - u) ^ 4) :=
    mul_le_mul_of_nonneg_left hab (by positivity)
  rw [hid, ha2, hb2]
  have e : (A + B) / 2 * (1 + 4 * (1 - q) * u ^ 2 * (d₁ + d₂) / (1 - u ^ 2) ^ 2
        + 4 * u ^ 2 * d₁ * d₂ / (1 - u) ^ 4)
      = (A + B) / 2 + u * (d₁ + d₂) * (2 * (1 - q) * u / (1 - u ^ 2) ^ 2 * (A + B))
        + 2 * u ^ 2 * d₁ * d₂ * ((A + B) / (1 - u) ^ 4) := by
    ring
  rw [e]
  linarith [t1, t2]

/-- **The mean of the doubly twisted local weight at exponent `q`, at one prime, sharp**: for
`p ≥ 2`, `σ ≥ 0`, `0 ≤ q ≤ 1` and `u = p^{-1/2-σ}`,
`E[‖1+zp^{-s₁}‖²‖1+zp^{-s₂}‖²‖1+zp^{-σ}‖^{2q-4}] ≤ E‖1+zp^{-σ}‖^{2q}·(1 + c)` with
`c = 2(1-q)u²((h₁ log p)² + (h₂ log p)²)/(1-u²)² + u²(h₁ log p)²(h₂ log p)²/(1-u)⁴`. -/
lemma integral_twistQPair_rademacherLaw_le_sharp {p : ℕ} (hp : 2 ≤ p) {σ h₁ h₂ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₂)‖ ^ 2
        * ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q - 4) ∂rademacherLaw)
      ≤ (∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q) ∂rademacherLaw)
        * (1 + (2 * (1 - q) * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
              * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2)
              / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ^ 2
          + ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (h₁ * Real.log p) ^ 2 * (h₂ * Real.log p) ^ 2
              / (1 - (p : ℝ) ^ (-(1 / 2 + σ))) ^ 4)) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hp1R : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu_def
  have hu0 : 0 ≤ u := (Real.rpow_pos_of_pos hpR _).le
  have hu1 : u < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1R (by linarith)
  have hnorm : ∀ h : ℝ, ‖(p : ℂ) ^ (-shiftLine σ h)‖ = u := fun h =>
    norm_cpow_neg_shiftLine hp0 σ h
  have hre : ∀ h : ℝ, ((p : ℂ) ^ (-shiftLine σ h)).re = u * Real.cos (h * Real.log p) :=
    fun h => re_cpow_neg_shiftLine hp0 σ h
  have hpos : ∀ h : ℝ, ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      = (1 + u) ^ 2 - 2 * u * (1 - Real.cos (h * Real.log p)) := by
    intro h
    rw [norm_one_add_mul_sq_eq (by simp), one_mul, hre h, hnorm h]
    ring
  have hneg : ∀ h : ℝ, ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      = (1 - u) ^ 2 + 2 * u * (1 - Real.cos (h * Real.log p)) := by
    intro h
    have hrew : ((-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)).re
        = -((p : ℂ) ^ (-shiftLine σ h)).re := by simp
    rw [norm_one_add_mul_sq_eq (by simp), hnorm h, hrew, hre h]
    ring
  have hw0 : (p : ℂ) ^ (-shiftLine σ 0) = ((u : ℝ) : ℂ) := cpow_neg_shiftLine_zero p σ
  have hn1 : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 + u := by
    rw [one_mul, hw0, show (1 : ℂ) + ((u : ℝ) : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 - u := by
    rw [hw0, show (1 : ℂ) + (-1) * ((u : ℝ) : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  -- the two atoms, on both sides
  rw [integral_rademacherLaw_eq, integral_rademacherLaw_eq]
  simp only [smul_eq_mul]
  rw [hpos h₁, hpos h₂, hneg h₁, hneg h₂, hn1, hn2]
  set d₁ : ℝ := 1 - Real.cos (h₁ * Real.log p) with hd₁_def
  set d₂ : ℝ := 1 - Real.cos (h₂ * Real.log p) with hd₂_def
  have hd₁0 : 0 ≤ d₁ := by rw [hd₁_def]; linarith [Real.cos_le_one (h₁ * Real.log p)]
  have hd₂0 : 0 ≤ d₂ := by rw [hd₂_def]; linarith [Real.cos_le_one (h₂ * Real.log p)]
  have hd₁sq : d₁ ≤ (h₁ * Real.log p) ^ 2 / 2 := by
    have := abs_cos_sub_one_le (h₁ * Real.log p)
    rw [abs_le] at this
    rw [hd₁_def]
    linarith [this.1]
  have hd₂sq : d₂ ≤ (h₂ * Real.log p) ^ 2 / 2 := by
    have := abs_cos_sub_one_le (h₂ * Real.log p)
    rw [abs_le] at this
    rw [hd₂_def]
    linarith [this.1]
  have hmain := twistQ_pair_atoms_le_sharp hu0 hu1 hq0 hq1 hd₁0 hd₂0
  have hA0 : 0 ≤ ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)) / 2 := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + u) (2 * q)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - u) (2 * q)
    linarith
  -- from `d_i` to `(h_i log p)²`
  have hq' : 0 ≤ 1 - q := by linarith
  have hc1 : 4 * (1 - q) * u ^ 2 * (d₁ + d₂) / (1 - u ^ 2) ^ 2
      ≤ 2 * (1 - q) * u ^ 2 * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2)
        / (1 - u ^ 2) ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have hsum : d₁ + d₂ ≤ ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) / 2 := by linarith
    have hc : 0 ≤ 4 * (1 - q) * u ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hq') (sq_nonneg u)
    calc 4 * (1 - q) * u ^ 2 * (d₁ + d₂)
        ≤ 4 * (1 - q) * u ^ 2 * (((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hsum hc
      _ = 2 * (1 - q) * u ^ 2 * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) := by ring
  have hc2 : 4 * u ^ 2 * d₁ * d₂ / (1 - u) ^ 4
      ≤ u ^ 2 * (h₁ * Real.log p) ^ 2 * (h₂ * Real.log p) ^ 2 / (1 - u) ^ 4 := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hdd : d₁ * d₂ ≤ (h₁ * Real.log p) ^ 2 / 2 * ((h₂ * Real.log p) ^ 2 / 2) :=
      mul_le_mul hd₁sq hd₂sq hd₂0 (by positivity)
    calc 4 * u ^ 2 * d₁ * d₂ = 4 * u ^ 2 * (d₁ * d₂) := by ring
      _ ≤ 4 * u ^ 2 * ((h₁ * Real.log p) ^ 2 / 2 * ((h₂ * Real.log p) ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left hdd (by positivity)
      _ = u ^ 2 * (h₁ * Real.log p) ^ 2 * (h₂ * Real.log p) ^ 2 := by ring
  have hL : (2 : ℝ)⁻¹ * (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂)
        * (1 + u) ^ (2 * q - 4)
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) * (1 - u) ^ (2 * q - 4))
      = (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) * (1 + u) ^ (2 * q - 4)
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) * (1 - u) ^ (2 * q - 4)) / 2 := by
    ring
  have hR : (2 : ℝ)⁻¹ * ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q))
      = ((1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)) / 2 := by ring
  rw [hL, hR]
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hA0)
  linarith

/-! ### The per-prime coefficient, priced -/

/-- `u²/(1-u)⁴ ≤ u² + 548u³` for `0 ≤ u` with `u² ≤ ½`: `(1-u)⁴ ≥ 1 - 4u` and
`(1-u)⁴ ≥ 1/137`. -/
lemma sq_div_one_sub_pow_four_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ^ 2 ≤ 1 / 2) :
    u ^ 2 / (1 - u) ^ 4 ≤ u ^ 2 + 548 * u ^ 3 := by
  have hu7 : u ≤ 0.70711 := by nlinarith
  have hm : (0.29289 : ℝ) ≤ 1 - u := by linarith
  have h137 : (1 / 137 : ℝ) ≤ (1 - u) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hm 4
    norm_num at this ⊢
    linarith
  have hbern : 1 - 4 * u ≤ (1 - u) ^ 4 := by
    have := one_add_mul_le_pow (a := -u) (by linarith) 4
    rw [← sub_eq_add_neg] at this
    push_cast at this
    linarith
  have hpos : 0 < (1 - u) ^ 4 := pow_pos (by linarith) 4
  rw [div_le_iff₀ hpos]
  have hkey : 1 ≤ (1 + 548 * u) * (1 - u) ^ 4 := by
    have := mul_le_mul_of_nonneg_left h137 hu0
    nlinarith
  calc u ^ 2 = u ^ 2 * 1 := (mul_one _).symm
    _ ≤ u ^ 2 * ((1 + 548 * u) * (1 - u) ^ 4) := mul_le_mul_of_nonneg_left hkey (sq_nonneg u)
    _ = (u ^ 2 + 548 * u ^ 3) * (1 - u) ^ 4 := by ring

/-- **The per-prime coefficient of (C2), priced.**  With `u² ≤ 1/p`, `uL ≤ 2`, `0 ≤ L ≤ p`,
`p ≥ 2`, `0 ≤ P_i ≤ T²L² ≤ 1` and `0 ≤ q ≤ 1`:
`2(1-q)u²(P₁+P₂)/(1-u²)² + u²P₁P₂/(1-u)⁴ ≤ T²((5-4q)L²/p + 1120L/p)`. -/
lemma twistQ_pair_coeff_le {u L p P₁ P₂ T q : ℝ} (hu0 : 0 ≤ u) (hup : u ^ 2 ≤ 1 / p)
    (hp : 2 ≤ p) (huL : u * L ≤ 2) (hL0 : 0 ≤ L) (hLp : L ≤ p) (hP₁0 : 0 ≤ P₁)
    (hP₁ : P₁ ≤ T ^ 2 * L ^ 2) (hP₂0 : 0 ≤ P₂) (hP₂ : P₂ ≤ T ^ 2 * L ^ 2)
    (hTL : T ^ 2 * L ^ 2 ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    2 * (1 - q) * u ^ 2 * (P₁ + P₂) / (1 - u ^ 2) ^ 2 + u ^ 2 * P₁ * P₂ / (1 - u) ^ 4
      ≤ T ^ 2 * ((5 - 4 * q) * (L ^ 2 / p) + 1120 * (L / p)) := by
  have hp0 : 0 < p := by linarith
  have hq' : 0 ≤ 1 - q := by linarith
  have hu2 : u ^ 2 ≤ 1 / 2 := le_trans hup (one_div_le_one_div_of_le (by norm_num) hp)
  have hLp0 : 0 ≤ L / p := div_nonneg hL0 hp0.le
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  -- the first term
  have hA : u ^ 2 / (1 - u ^ 2) ^ 2 ≤ 1 / p + 6 * (1 / p) ^ 2 := by
    have h1 := div_one_sub_sq_le (sq_nonneg u) hu2
    have h2 : (u ^ 2) ^ 2 ≤ (1 / p) ^ 2 := pow_le_pow_left₀ (sq_nonneg u) hup 2
    linarith
  have hLp2 : L ^ 2 * (1 / p) ^ 2 ≤ L / p := by
    have e : L ^ 2 * (1 / p) ^ 2 = (L / p) * (L / p) := by ring
    have h1 : L / p ≤ 1 := (div_le_one hp0).2 hLp
    rw [e]
    exact mul_le_of_le_one_right hLp0 h1
  have t1 : 2 * (1 - q) * u ^ 2 * (P₁ + P₂) / (1 - u ^ 2) ^ 2
      ≤ 4 * (1 - q) * T ^ 2 * (L ^ 2 / p + 6 * (L / p)) := by
    have hH : P₁ + P₂ ≤ 2 * (T ^ 2 * L ^ 2) := by linarith
    have hc : 0 ≤ 2 * (1 - q) * (P₁ + P₂) :=
      mul_nonneg (mul_nonneg (by norm_num) hq') (add_nonneg hP₁0 hP₂0)
    calc 2 * (1 - q) * u ^ 2 * (P₁ + P₂) / (1 - u ^ 2) ^ 2
        = 2 * (1 - q) * (P₁ + P₂) * (u ^ 2 / (1 - u ^ 2) ^ 2) := by ring
      _ ≤ 2 * (1 - q) * (P₁ + P₂) * (1 / p + 6 * (1 / p) ^ 2) :=
          mul_le_mul_of_nonneg_left hA hc
      _ ≤ 2 * (1 - q) * (2 * (T ^ 2 * L ^ 2)) * (1 / p + 6 * (1 / p) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num) hq')
      _ = 4 * (1 - q) * T ^ 2 * (L ^ 2 / p + 6 * (L ^ 2 * (1 / p) ^ 2)) := by ring
      _ ≤ 4 * (1 - q) * T ^ 2 * (L ^ 2 / p + 6 * (L / p)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (mul_nonneg (by norm_num) hq') hT2)
          linarith
  -- the second term
  have hB := sq_div_one_sub_pow_four_le hu0 hu2
  have hu3 : u ^ 3 * L ^ 2 ≤ 2 * (L / p) := by
    calc u ^ 3 * L ^ 2 = u ^ 2 * (u * L) * L := by ring
      _ ≤ 1 / p * 2 * L := by
          refine mul_le_mul_of_nonneg_right ?_ hL0
          exact mul_le_mul hup huL (mul_nonneg hu0 hL0) (by positivity)
      _ = 2 * (L / p) := by ring
  have hu2L : u ^ 2 * L ^ 2 ≤ L ^ 2 / p := by
    calc u ^ 2 * L ^ 2 ≤ 1 / p * L ^ 2 := mul_le_mul_of_nonneg_right hup (sq_nonneg L)
      _ = L ^ 2 / p := by ring
  have hPP : P₁ * P₂ ≤ T ^ 2 * L ^ 2 := by
    calc P₁ * P₂ ≤ 1 * (T ^ 2 * L ^ 2) := mul_le_mul (hP₁.trans hTL) hP₂ hP₂0 zero_le_one
      _ = T ^ 2 * L ^ 2 := one_mul _
  have t2 : u ^ 2 * P₁ * P₂ / (1 - u) ^ 4 ≤ T ^ 2 * (L ^ 2 / p + 1096 * (L / p)) := by
    calc u ^ 2 * P₁ * P₂ / (1 - u) ^ 4 = (P₁ * P₂) * (u ^ 2 / (1 - u) ^ 4) := by ring
      _ ≤ (T ^ 2 * L ^ 2) * (u ^ 2 + 548 * u ^ 3) :=
          mul_le_mul hPP hB (by positivity) (by positivity)
      _ = T ^ 2 * (u ^ 2 * L ^ 2 + 548 * (u ^ 3 * L ^ 2)) := by ring
      _ ≤ T ^ 2 * (L ^ 2 / p + 548 * (2 * (L / p))) := by
          refine mul_le_mul_of_nonneg_left ?_ hT2
          linarith
      _ = T ^ 2 * (L ^ 2 / p + 1096 * (L / p)) := by ring
  -- together
  have e : T ^ 2 * ((5 - 4 * q) * (L ^ 2 / p) + 1120 * (L / p))
      - (4 * (1 - q) * T ^ 2 * (L ^ 2 / p + 6 * (L / p)) + T ^ 2 * (L ^ 2 / p + 1096 * (L / p)))
      = 24 * q * (T ^ 2 * (L / p)) := by ring
  have h0 : 0 ≤ 24 * q * (T ^ 2 * (L / p)) :=
    mul_nonneg (mul_nonneg (by norm_num) hq0) (mul_nonneg hT2 hLp0)
  linarith

/-! ### The sum over the primes -/

/-- `e^{-20} ≤ 1/(4·10⁸)`: `e^{20} ≥ 2.7^{20}`. -/
lemma exp_neg_twenty_le : Real.exp (-20) ≤ 1 / 400000000 := by
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h20 : (2.7 : ℝ) ^ 20 ≤ Real.exp 20 := by
    have := pow_le_pow_left₀ (by norm_num) he 20
    rwa [← Real.exp_nat_mul, show ((20 : ℕ) : ℝ) * 1 = 20 by norm_num] at this
  have h4 : (400000000 : ℝ) ≤ Real.exp 20 := le_trans (by norm_num) h20
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h4

/-- **The closing arithmetic of (C2).**  For `0 ≤ T ≤ 1/(4·10⁸)`, `0 ≤ Λ`, `TΛ ≤ 1`, `0 ≤ q ≤ 1`,
`S₂ ≤ Λ²/2 + 9.003Λ + 1` and `S₁ ≤ Λ + 5.3863`:
`T²((5-4q)S₂ + 1120S₁) ≤ 2(1-q) + 0.50001`. -/
lemma twistQ_pair_sum_arith {T Λ q S₁ S₂ : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ 1 / 400000000)
    (hΛ0 : 0 ≤ Λ) (hTΛ : T * Λ ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hS₂ : S₂ ≤ Λ ^ 2 / 2 + 9.003 * Λ + 1) (hS₁ : S₁ ≤ Λ + 5.3863) :
    T ^ 2 * ((5 - 4 * q) * S₂ + 1120 * S₁) ≤ 2 * (1 - q) + 0.50001 := by
  have hTΛ0 : 0 ≤ T * Λ := mul_nonneg hT0 hΛ0
  have hTT : T * (T * Λ) ≤ T := mul_le_of_le_one_right hT0 hTΛ
  have hT2 : T ^ 2 ≤ T * (1 / 400000000) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left hT hT0
  have h2 : T ^ 2 * S₂ ≤ 1 / 2 + 9.003 * T + T ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hS₂ (sq_nonneg T)
    have e : T ^ 2 * (Λ ^ 2 / 2 + 9.003 * Λ + 1)
        = (T * Λ) ^ 2 / 2 + 9.003 * (T * (T * Λ)) + T ^ 2 := by ring
    have h1 : (T * Λ) ^ 2 ≤ 1 := by
      rw [sq]
      exact mul_le_one₀ hTΛ hTΛ0 hTΛ
    linarith
  have h1 : T ^ 2 * S₁ ≤ T + 5.3863 * T ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hS₁ (sq_nonneg T)
    have e : T ^ 2 * (Λ + 5.3863) = T * (T * Λ) + 5.3863 * T ^ 2 := by ring
    linarith
  have h5 : (5 - 4 * q) * (T ^ 2 * S₂) ≤ (5 - 4 * q) * (1 / 2 + 9.003 * T + T ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : (5 - 4 * q) * (9.003 * T + T ^ 2) ≤ 5 * (9.003 * T + T ^ 2) := by
    have h0 : 0 ≤ 9.003 * T + T ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : 5 - 4 * q ≤ 5) h0
    linarith
  have e : T ^ 2 * ((5 - 4 * q) * S₂ + 1120 * S₁)
      = (5 - 4 * q) * (T ^ 2 * S₂) + 1120 * (T ^ 2 * S₁) := by ring
  have e2 : (5 - 4 * q) * (1 / 2 + 9.003 * T + T ^ 2)
      = 2 * (1 - q) + 1 / 2 + (5 - 4 * q) * (9.003 * T + T ^ 2) := by ring
  rw [e]
  linarith

/-- Below the cut, `log n ≤ e^θ`: `0 < n < scaleCut θ = ⌊e^{e^θ}⌋ + 1`. -/
lemma log_le_exp_of_lt_scaleCut {θ : ℝ} {n : ℕ} (hn : 0 < n) (hlt : n < scaleCut θ) :
    Real.log n ≤ Real.exp θ := by
  have hle : n ≤ ⌊blockScale θ 0⌋₊ := by
    unfold scaleCut at hlt
    omega
  have hb : (n : ℝ) ≤ blockScale θ 0 :=
    le_trans (by exact_mod_cast hle) (Nat.floor_le (blockScale_pos θ 0).le)
  have h := Real.log_le_log (by exact_mod_cast hn) hb
  rw [log_blockScale] at h
  simpa using h

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(C2) at exponent `q`, sharp.**  For `k ≥ 20`, `σ ≥ 0`, `0 ≤ h_i ≤ e^{-k}` and `0 ≤ q ≤ 1`,
over every prime below `scaleCut k`:
`E[‖F(σ+ih₁)‖²‖F(σ+ih₂)‖²‖F(σ)‖^{2q-4}] ≤ e^{2(1-q)+0.50001}·E‖F(σ)‖^{2q}`.  The per-prime factor
is `RMF.integral_twistQPair_rademacherLaw_le_sharp`, priced by `RMF.twistQ_pair_coeff_le`; the
prime sums are `RMF.sum_log_sq_div_primesBelow_le_sharp` and `RMF.sum_log_div_primesBelow_le`. -/
theorem integral_twistQ_pair_le_sharp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {k : ℕ} (hk : 20 ≤ k) {σ h₁ h₂ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hh₁0 : 0 ≤ h₁) (hh₁ : h₁ ≤ Real.exp (-(k : ℝ)))
    (hh₂0 : 0 ≤ h₂) (hh₂ : h₂ ≤ Real.exp (-(k : ℝ))) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4) ∂μ)
      ≤ Real.exp (2 * (1 - q) + 0.50001)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  classical
  set S : Finset ℕ := primesIco 0 (scaleCut (k : ℝ)) with hS_def
  set g : ℕ → ℂ → ℝ := fun p z =>
    ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₂)‖ ^ 2
      * ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q - 4) with hg_def
  set g₀ : ℕ → ℂ → ℝ := fun p z => ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q) with hg₀_def
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hbase : ∀ c : ℂ, Measurable fun z : ℂ => ‖1 + z * c‖ :=
    fun c => (measurable_const.add (measurable_id.mul measurable_const)).norm
  have hgm : ∀ p : ℕ, Measurable (g p) := fun p =>
    (((hbase _).pow_const 2).mul ((hbase _).pow_const 2)).mul ((hbase _).pow_const _)
  have hg₀m : ∀ p : ℕ, Measurable (g₀ p) := fun p => (hbase _).pow_const _
  rw [integral_congr_ae (Filter.Eventually.of_forall
      (twistQPair_eq_prod (X := X) 0 (scaleCut (k : ℝ)) σ h₁ h₂ q)),
    integral_congr_ae (Filter.Eventually.of_forall
      (rpow_norm_randomEulerProductIco_eq_prod (X := X) 0
        (scaleCut (k : ℝ)) (shiftLine σ 0) (2 * q))),
    hX.integral_prod hSp g fun p _ => (hgm p).aestronglyMeasurable,
    hX.integral_prod hSp g₀ fun p _ => (hg₀m p).aestronglyMeasurable]
  -- the per-prime bound
  have hq' : 0 ≤ 1 - q := by linarith
  set c : ℕ → ℝ := fun p =>
    2 * (1 - q) * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
        * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2)
        / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ^ 2
      + ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (h₁ * Real.log p) ^ 2 * (h₂ * Real.log p) ^ 2
        / (1 - (p : ℝ) ^ (-(1 / 2 + σ))) ^ 4 with hc_def
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    rw [hc_def]
    dsimp only
    refine add_nonneg (div_nonneg ?_ (sq_nonneg _)) (div_nonneg (by positivity) (by positivity))
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hq') (sq_nonneg _)) (by positivity)
  have hbound : ∀ p ∈ S, (∫ z, g p z ∂rademacherLaw)
      ≤ (∫ z, g₀ p z ∂rademacherLaw) * (1 + c p) :=
    fun p hp => integral_twistQPair_rademacherLaw_le_sharp (hSp p hp).two_le hσ hq0 hq1
  have hnonneg : ∀ p ∈ S, 0 ≤ ∫ z, g p z ∂rademacherLaw := by
    intro p _
    refine integral_nonneg fun z => ?_
    rw [hg_def]
    positivity
  have hnonneg₀ : ∀ p ∈ S, 0 ≤ ∫ z, g₀ p z ∂rademacherLaw := by
    intro p _
    exact integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  -- the scale
  set T : ℝ := Real.exp (-(k : ℝ)) with hT_def
  have hT0 : 0 ≤ T := (Real.exp_pos _).le
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hT : T ≤ 1 / 400000000 :=
    le_trans (Real.exp_le_exp.2 (by linarith)) exp_neg_twenty_le
  have hTe : T * Real.exp (k : ℝ) = 1 := by
    rw [hT_def, ← Real.exp_add]
    simp
  have hTlog : ∀ n : ℕ, 0 < n → n < scaleCut (k : ℝ) → T * Real.log n ≤ 1 := by
    intro n hn hlt
    calc T * Real.log n ≤ T * Real.exp (k : ℝ) :=
          mul_le_mul_of_nonneg_left (log_le_exp_of_lt_scaleCut hn hlt) hT0
      _ = 1 := hTe
  -- the per-prime coefficient
  have hterm : ∀ p ∈ S, c p
      ≤ T ^ 2 * ((5 - 4 * q) * (Real.log p ^ 2 / p) + 1120 * (Real.log p / p)) := by
    intro p hp
    have hpp := hSp p hp
    have hlt : p < scaleCut (k : ℝ) := (mem_primesIco.1 hp).2.2
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hL0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hLp : Real.log p ≤ p := by linarith [Real.log_le_sub_one_of_pos hpR]
    have hup : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 ≤ 1 / (p : ℝ) := by
      have h := prime_rpow_neg_mul_self_le_inv hpp (c := 1 / 2 + σ) (by linarith)
      rw [one_mul] at h
      calc ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
          = (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) := sq _
        _ ≤ (p : ℝ)⁻¹ := h
        _ = 1 / (p : ℝ) := (one_div _).symm
    have huL : (p : ℝ) ^ (-(1 / 2 + σ)) * Real.log p ≤ 2 := by
      have h1 : (p : ℝ) ^ (-(1 / 2 + σ)) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      have h2 : Real.log p ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hpR.le (by norm_num)
      have h3 : (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hpR]
        norm_num
      calc (p : ℝ) ^ (-(1 / 2 + σ)) * Real.log p
          ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) * ((p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) :=
            mul_le_mul h1 h2 hL0 (Real.rpow_nonneg hpR.le _)
        _ = 2 * ((p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = 2 := by rw [h3, mul_one]
    have hTL : T * Real.log p ≤ 1 := hTlog p hpp.pos hlt
    have hTL2 : T ^ 2 * Real.log p ^ 2 ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (mul_nonneg hT0 hL0) hTL
    have hP : ∀ h : ℝ, 0 ≤ h → h ≤ T → (h * Real.log p) ^ 2 ≤ T ^ 2 * Real.log p ^ 2 := by
      intro h h0 hle
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hle 2) (sq_nonneg _)
    rw [hc_def]
    dsimp only
    exact twistQ_pair_coeff_le (Real.rpow_nonneg hpR.le _) hup hp2 huL hL0 hLp (sq_nonneg _)
      (hP h₁ hh₁0 hh₁) (sq_nonneg _) (hP h₂ hh₂0 hh₂) hTL2 hq0 hq1
  -- the sum over the primes
  set N : ℕ := ⌊blockScale (k : ℝ) 0⌋₊ with hN_def
  have hSN : S = Nat.primesBelow (N + 1) := by
    rw [hS_def, primesIco_zero]
    rfl
  have hN1 : 1 ≤ N := Nat.le_floor (by
    rw [Nat.cast_one]
    linarith [two_le_blockScale_zero (θ := (k : ℝ)) (Nat.cast_nonneg k)])
  have hsum : ∑ p ∈ S, c p ≤ 2 * (1 - q) + 0.50001 := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have heq : ∑ p ∈ S, T ^ 2 * ((5 - 4 * q) * (Real.log p ^ 2 / p) + 1120 * (Real.log p / p))
        = T ^ 2 * ((5 - 4 * q) * ∑ p ∈ S, Real.log p ^ 2 / p
          + 1120 * ∑ p ∈ S, Real.log p / p) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [heq, hSN]
    have hS₂ := sum_log_sq_div_primesBelow_le_sharp N
    have hS₁ := sum_log_div_primesBelow_le hN1
    have hlog4 : Real.log 4 ≤ 1.3863 := by
      have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      linarith
    have hΛ0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hTΛ : T * Real.log N ≤ 1 := hTlog N (by omega) (by
      change N < ⌊blockScale (k : ℝ) 0⌋₊ + 1
      omega)
    exact twistQ_pair_sum_arith hT0 hT hΛ0 hTΛ hq0 hq1 hS₂ (by linarith)
  calc ∏ p ∈ S, ∫ z, g p z ∂rademacherLaw
      ≤ ∏ p ∈ S, ((∫ z, g₀ p z ∂rademacherLaw) * (1 + c p)) :=
        Finset.prod_le_prod hnonneg hbound
    _ = (∏ p ∈ S, ∫ z, g₀ p z ∂rademacherLaw) * ∏ p ∈ S, (1 + c p) :=
        Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ S, ∫ z, g₀ p z ∂rademacherLaw) * Real.exp (2 * (1 - q) + 0.50001) := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg hnonneg₀)
        exact le_trans (Real.prod_one_add_le_exp_sum S hc0) (Real.exp_le_exp.2 hsum)
    _ = Real.exp (2 * (1 - q) + 0.50001) * ∏ p ∈ S, ∫ z, g₀ p z ∂rademacherLaw := mul_comm _ _

end RMF
