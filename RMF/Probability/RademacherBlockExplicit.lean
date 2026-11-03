/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherWindowComparison
import RMF.NumberTheory.StrongBlockCosineExplicit
import RMF.NumberTheory.PNTThresholdExplicit

/-!
# The Rademacher block walk, per block, with numeral constants

The per-block inputs of a sharp Gaussian comparison for the Rademacher RMF at a single height.
At `s = ½ + σ + it` the block's local logarithms have, under the `|F(s)|²`-tilt,

* variance `½(S + C)` and mean `S + ½C` up to cubic terms, where `S = ∑_{p ∈ B} p^{-1-2σ}` is the
  Mertens block sum and `C = ∑_{p ∈ B} cos(2t log p)/p^{1+2σ}` the oscillatory one
  (`RMF.blockMatchedVarAdd_bounds_sharp`, `RMF.abs_blockMeanAdd_sub_le_sharp`);
* and `C` is small past the explicit block floor `104`: `3/(τe^{m+θ}) + (τ+1)/10²⁸` at `τ = 2t`,
  from the effective prime number theorem at its named threshold.

The Steinhaus block has `C = 0` and variance floor `0.95e^{-2η}`
(`RMF.blockMatchedVar_lower_of_le_sharp`); here the weights are below `10⁻⁶` from offset `16`, so
the floor is `0.9999e^{-2η}` less the cosine sum.
-/

open MeasureTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The explicit cosine input -/

/-- `e^η/√X ≤ 10⁻⁶` on a block with `28 + 2η ≤ e^{j+θ}`. -/
lemma exp_div_sqrt_blockScale_le_millionth {θ η : ℝ} {j : ℕ}
    (hsc : 28 + 2 * η ≤ Real.exp ((j : ℝ) + θ)) :
    Real.exp η / √(blockScale θ j) ≤ 1 / 1000000 := by
  have hb0 : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have he1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h28 : (1000000000000 : ℝ) ≤ Real.exp 28 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 28)
      (by norm_num) he1.le (by norm_num)
  have hprod : (1000000 * Real.exp η) ^ 2 ≤ blockScale θ j := by
    have hsq : (1000000 * Real.exp η) ^ 2 = 1000000000000 * Real.exp (2 * η) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [hsq, blockScale]
    calc (1000000000000 : ℝ) * Real.exp (2 * η)
        ≤ Real.exp 28 * Real.exp (2 * η) := mul_le_mul_of_nonneg_right h28 (Real.exp_pos _).le
      _ = Real.exp (28 + 2 * η) := by rw [← Real.exp_add]
      _ ≤ Real.exp (Real.exp ((j : ℝ) + θ)) := Real.exp_le_exp.2 hsc
  have hle : 1000000 * Real.exp η ≤ √(blockScale θ j) :=
    (Real.le_sqrt (by positivity) hb0.le).2 hprod
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hb0) (by norm_num)]
  linarith

/-- The interval cosine bound at a nonnegative tilt past `RMF.blockCosineThreshold`, with its
witness named, proved from `RMF/NumberTheory/PNTThresholdExplicit.lean` alone. -/
theorem abs_cos_prime_sum_block_weight_le_blockCosineThreshold :
    2 ≤ blockCosineThreshold ∧
      ∀ τ : ℝ, 0 < τ → ∀ σ y₁ y₂ : ℝ, 0 ≤ σ → blockCosineThreshold ≤ y₁ → y₁ ≤ y₂ →
        Real.log y₂ ≤ 3 * Real.log y₁ →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
        ≤ 3 / (τ * Real.log y₁)
            + 32 * 10 ^ (40 : ℕ) * (τ + 1)
                * Real.exp (-(1 / 200 : ℝ) * Real.log y₁ ^ ((1 : ℝ) / 10)) := by
  obtain ⟨hy₀, hbound⟩ := abs_cos_prime_sum_block_le_threshold_numeral_explicit
  refine ⟨hy₀, ?_⟩
  intro τ hτ σ y₁ y₂ hσ0 hy₁ hy hratio
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hy₀ hy₁
  refine abs_cos_prime_sum_block_weight_le_of_nonneg hy₁2 hy hσ0 (fun u hu => ?_)
  obtain ⟨hu1, hu2⟩ := hu
  exact hbound τ hτ y₁ u hy₁ hu1
    (le_trans (Real.log_le_log (by linarith) hu2) hratio)

/-- **The explicit block floor** `log log RMF.blockCosineThreshold ≤ 104`: the threshold is at
most `exp(10⁴⁵)` (`RMF.mediumPNTThresholdL_le_sharp`) and `10⁴⁵ ≤ e^{104}`. -/
lemma log_log_blockCosineThreshold_le_104 :
    Real.log (Real.log blockCosineThreshold) ≤ 104 := by
  have hL := mediumPNTThresholdL_le_sharp
  have hle : blockCosineThreshold ≤ Real.exp (10 ^ 45) := by
    unfold blockCosineThreshold thetaExpThreshold
    exact max_le (max_le (Real.exp_le_exp.2 hL) (Real.exp_le_exp.2 (by norm_num)))
      (Real.exp_le_exp.2 (by norm_num))
  have hge : Real.exp 1 ≤ blockCosineThreshold := by
    unfold blockCosineThreshold
    exact le_max_right _ _
  have hpos : 0 < blockCosineThreshold := lt_of_lt_of_le (Real.exp_pos 1) hge
  have h1 : Real.log blockCosineThreshold ≤ 10 ^ 45 := by
    rw [Real.log_le_iff_le_exp hpos]
    exact hle
  have hlog1 : 1 ≤ Real.log blockCosineThreshold := by
    rw [Real.le_log_iff_exp_le hpos]
    exact hge
  have h104 : (10 : ℝ) ^ 45 ≤ Real.exp 104 := by
    have he : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (10 : ℝ) ^ 45 ≤ (2.718 : ℝ) ^ (104 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (104 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 104
      _ = Real.exp 104 := by rw [← Real.exp_nat_mul]; norm_num
  calc Real.log (Real.log blockCosineThreshold) ≤ Real.log (10 ^ 45) :=
        Real.log_le_log (by linarith) h1
    _ ≤ 104 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        exact h104

/-- `32·10⁴⁰·exp(-e^{10.4}/200) ≤ 10⁻²⁸`: the effective prime number theorem's term at the
floor `104`. -/
lemma pnt_term_at_floor_le :
    32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4) ≤ 1 / 10 ^ 28 := by
  have h1 : (32800 : ℝ) ≤ Real.exp 10.4 := by interval_decide (trust := kernel)
  have h2 : Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4) ≤ Real.exp (-164) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 : 32 * 10 ^ (40 : ℕ) * Real.exp (-164) ≤ (1 : ℝ) / 10 ^ 28 := by
    interval_decide (trust := kernel)
  calc 32 * 10 ^ (40 : ℕ) * Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4)
      ≤ 32 * 10 ^ (40 : ℕ) * Real.exp (-164) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 1 / 10 ^ 28 := h3

/-! ### The block variance and the block mean, sharp -/

/-- The block sum `∑_{p ∈ block m} ‖p^{-s}‖²` from offset `16`: within `1/150000` of its Mertens
bracket, `e^{-2η}(1 - 1/150000) ≤ S ≤ 1 + 1/150000`. -/
lemma sum_norm_sq_primeBlockSub_bounds_sharp {θ σ η : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (16 : ℝ) ≤ (m : ℝ) + θ) (hσ0 : 0 ≤ σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    Real.exp (-(2 * η)) * (1 - 1 / 150000) ≤ ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2
      ∧ ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 ≤ 1 + 1 / 150000 := by
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith
  obtain ⟨hlo, hhi⟩ :=
    sum_norm_sq_harperBlock_bounds_of_le (blockScale θ (m + 1)) σ η w hbig hσ0 hσ hwn
  have hL : (10000000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [log_blockScale]
    have h17 : (10000000 : ℝ) ≤ Real.exp 17 := by interval_decide (trust := kernel)
    exact h17.trans (Real.exp_le_exp.2 (by push_cast; linarith))
  have hL0 : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
  have hd : 60 / Real.log (blockScale θ (m + 1)) ≤ 1 / 150000 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hd0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by positivity
  have he0 : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  constructor
  · refine le_trans ?_ hlo
    exact mul_le_mul_of_nonneg_left (by linarith) he0.le
  · exact le_trans hhi (by linarith)

/-- **The Rademacher block variance, sharp.**  For the one-point weights `p^{-s}`, from offset
`16` with `28 + 2η ≤ e^{m+θ}` and `σ ≥ 0`: if the block's oscillatory sum at `2 Im s` is at most
`ε`, then `0.9999e^{-2η} - ε ≤ 2V ≤ 1.0001 + ε`.

`RMF.abs_coe_blockMatchedVarAdd_sub_le` puts `V` within `(42κ + 48κ²)S` of `∑ (Re p^{-s})²`, which
`RMF.sum_re_cpow_neg_sq_primeBlockSub_eq` splits as `S/2 + C/2`, and the weights are below
`κ = 10⁻⁶` (`RMF.exp_div_sqrt_blockScale_le_millionth`). -/
theorem blockMatchedVarAdd_bounds_sharp (hX : IsRademacherPrimeValues X μ) {θ σ η ε : ℝ}
    {m y : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ)
    (hmθ : (16 : ℝ) ≤ (m : ℝ) + θ) (hsc : 28 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y)
    (hcos : |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| ≤ ε) :
    0.9999 * Real.exp (-(2 * η)) - ε
        ≤ 2 * ((blockMatchedVarAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVarAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 1.0001 + ε := by
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  set κ : ℝ := Real.exp η / √(blockScale θ m) with hκdef
  have hκ : κ ≤ 1 / 1000000 := exp_div_sqrt_blockScale_le_millionth hsc
  have hκ0 : 0 ≤ κ := by
    have := Real.sqrt_nonneg (blockScale θ m)
    positivity
  have hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hres
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ κ :=
    fun p hp => norm_le_of_mem_primeBlockSub_of_le hσ hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 :=
    fun p hp => le_trans (hwκ p hp) (by linarith)
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB hw5
  set S : ℝ := ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => sq_nonneg _
  -- the third-order error against the block sum
  have herr : (∑ p ∈ primeBlockSub θ m,
      (42 * ‖w p‖ ^ 3 + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2))
        ≤ (42 * κ + 48 * κ ^ 2) * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h0 : 0 ≤ ‖w p‖ := norm_nonneg _
    have hk := hwκ p hp
    have ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ‖w p‖ := rfl
    rw [ha]
    have h3 : ‖w p‖ ^ 3 ≤ κ * ‖w p‖ ^ 2 := by
      have hc : ‖w p‖ ^ 3 = ‖w p‖ * ‖w p‖ ^ 2 := by ring
      rw [hc]
      exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    have h4 : ‖w p‖ ^ 2 * ‖w p‖ ^ 2 ≤ κ ^ 2 * ‖w p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hk 2) (sq_nonneg _)
    linarith
  have hcoef : 42 * κ + 48 * κ ^ 2 ≤ 43 / 1000000 := by nlinarith
  -- the main term: `2 ∑ (Re w)² = S + C`
  have hsplit := sum_re_cpow_neg_sq_primeBlockSub_eq θ σ m hres
  have hSeq : (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) = S := by
    rw [hSdef]
    exact Finset.sum_congr rfl fun p hp => (hwn p hp).symm
  rw [hSeq] at hsplit
  have hre : (∑ p ∈ primeBlockSub θ m, (w p).re ^ 2)
      = ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-s)).re ^ 2 := rfl
  rw [hre, hsplit] at hgap
  obtain ⟨hSlo, hShi⟩ := sum_norm_sq_primeBlockSub_bounds_sharp hmθ hσ0 hσ hwn
  rw [← hSdef] at hSlo hShi
  rw [abs_le] at hgap hcos
  have he0 : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  have hES : (42 * κ + 48 * κ ^ 2) * S ≤ 43 / 1000000 * S :=
    mul_le_mul_of_nonneg_right hcoef hS0
  constructor
  · -- `2V ≥ S(1 - 86/10⁶) - ε ≥ 0.9999e^{-2η} - ε`
    have hlow : 0.9999 * Real.exp (-(2 * η)) ≤ S * (1 - 86 / 1000000) := by
      have h1 : Real.exp (-(2 * η)) * (1 - 1 / 150000) * (1 - 86 / 1000000)
          ≤ S * (1 - 86 / 1000000) :=
        mul_le_mul_of_nonneg_right hSlo (by norm_num)
      have h2 : 0.9999 * Real.exp (-(2 * η))
          ≤ Real.exp (-(2 * η)) * (1 - 1 / 150000) * (1 - 86 / 1000000) := by
        have hc : (0.9999 : ℝ) ≤ (1 - 1 / 150000) * (1 - 86 / 1000000) := by norm_num
        nlinarith
      linarith
    linarith [hgap.1, hcos.1]
  · -- `2V ≤ S(1 + 86/10⁶) + ε ≤ 1.0001 + ε`
    have hup : S * (1 + 86 / 1000000) ≤ 1.0001 := by
      have h1 : S * (1 + 86 / 1000000) ≤ (1 + 1 / 150000) * (1 + 86 / 1000000) :=
        mul_le_mul_of_nonneg_right hShi (by norm_num)
      have hc : (1 + 1 / 150000) * (1 + 86 / 1000000) ≤ (1.0001 : ℝ) := by norm_num
      linarith
    linarith [hgap.2, hcos.2]

/-- **The Rademacher block mean at the weight size `κ = e^η/√x_m ≤ 1/5`**: the tilted block
mean is the block sum plus half the oscillatory sum, `S + C/2`, up to `37κS`.  Summed over the
blocks `κ` decays doubly exponentially, which is what the cumulative drift needs.

`RMF.abs_blockMeanAdd_sub_sum_le` gives the main term `∑ (2(Re w)² - Re(w²)/2)`, and each term is
`(Re w)² + ‖w‖²/2 = p^{-1-2σ} + cos(2t log p)/(2p^{1+2σ})`. -/
theorem abs_blockMeanAdd_sub_le_kappa (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ}
    {m y : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hκ : Real.exp η / √(blockScale θ m) ≤ 1 / 5)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)
        - ((∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
          + (∑ p ∈ primeBlockSub θ m,
              Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)) / 2)|
      ≤ 37 * (Real.exp η / √(blockScale θ m))
        * ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  set κ : ℝ := Real.exp η / √(blockScale θ m) with hκdef
  have hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hres
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ κ :=
    fun p hp => norm_le_of_mem_primeBlockSub_of_le hσ hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 :=
    fun p hp => le_trans (hwκ p hp) hκ
  have hgap := abs_blockMeanAdd_sub_sum_le hX y hs hB hw5
  -- the main term, termwise
  have hmain : (∑ p ∈ primeBlockSub θ m,
      (2 * (((p : ℕ) : ℂ) ^ (-s)).re * (w p).re - ((w p) ^ 2).re / 2))
        = (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
          + (∑ p ∈ primeBlockSub θ m,
              Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ))
                / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsq : ((w p) ^ 2).re = (w p).re ^ 2 - (w p).im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    have hnorm : ‖w p‖ ^ 2 = (w p).re ^ 2 + (w p).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hsplit := re_cpow_neg_sq_eq p.2 hres
    have hw : (((p : ℕ) : ℂ) ^ (-s)).re = (w p).re := rfl
    rw [hw, hsq]
    have hwre : (w p).re ^ 2 = ((((p : ℕ) : ℂ)) ^ (-s)).re ^ 2 := rfl
    rw [← hwn p hp, hnorm]
    rw [hwre] at hnorm ⊢
    rw [hsplit]
    have hpn : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = (((((p : ℕ) : ℂ)) ^ (-s)).re) ^ 2 + (w p).im ^ 2 := by
      rw [← hwre, ← hnorm, hwn p hp]
    rw [hsplit] at hpn
    linarith
  -- the error, termwise
  have herr : (∑ p ∈ primeBlockSub θ m,
      (36 * ‖w p‖ ^ 3 + 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 * ‖w p‖))
        ≤ 37 * κ * ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h0 : 0 ≤ ‖w p‖ := norm_nonneg _
    have hk := hwκ p hp
    have hk0 : 0 ≤ κ := le_trans h0 hk
    have ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ‖w p‖ := rfl
    rw [ha, ← hwn p hp]
    have h3 : ‖w p‖ ^ 3 ≤ κ * ‖w p‖ ^ 2 := by
      have hc : ‖w p‖ ^ 3 = ‖w p‖ * ‖w p‖ ^ 2 := by ring
      rw [hc]
      exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    have h4 : ‖w p‖ ^ 3 * ‖w p‖ ≤ κ / 5 * ‖w p‖ ^ 2 := by
      have hc : ‖w p‖ ^ 3 * ‖w p‖ = (‖w p‖ * ‖w p‖) * ‖w p‖ ^ 2 := by ring
      rw [hc]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc ‖w p‖ * ‖w p‖ ≤ κ * (1 / 5) := mul_le_mul hk (le_trans hk hκ) h0 hk0
        _ = κ / 5 := by ring
    have hκw : 0 ≤ κ * ‖w p‖ ^ 2 := mul_nonneg hk0 (sq_nonneg _)
    linarith
  rw [hmain] at hgap
  exact hgap.trans herr

/-- **The Rademacher block mean, sharp.**  For the one-point weights `p^{-s}`, from offset `16`
with `28 + 2η ≤ e^{m+θ}`: the tilted block mean is the block sum plus half the oscillatory sum,
`S + C/2`, up to `(37/10⁶)S` — `RMF.abs_blockMeanAdd_sub_le_kappa` at `κ ≤ 10⁻⁶`. -/
theorem abs_blockMeanAdd_sub_le_sharp (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ}
    {m y : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hsc : 28 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)
        - ((∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
          + (∑ p ∈ primeBlockSub θ m,
              Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)) / 2)|
      ≤ 37 / 1000000 * ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  have hκ := exp_div_sqrt_blockScale_le_millionth hsc
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    Finset.sum_nonneg fun p _ => Real.rpow_nonneg (by positivity) _
  refine le_trans (abs_blockMeanAdd_sub_le_kappa hX hs hres (le_trans hκ (by norm_num)) hσ hB) ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hS0

end RMF
