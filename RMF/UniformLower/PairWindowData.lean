/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBoxComparisonDecay
import RMF.UniformLower.BlockCosineFloor
import RMF.EulerProduct.RademacherTwoPoint
import RMF.Probability.RademacherChaining

/-!
# HP2's post part: the Rademacher inputs

HP2's post part runs over the blocks `m ≥ d` of a pair `h₁, h₂ ∈ halfWindow k` at depth `d`
(`|h₁ - h₂|e^{k+d} ∈ (e^{-1}, 1]`) under the two-fold tilt `RMF.tiltedMeasure₂`, compared with
Gaussians at offset `k + d`.  With `S_m = RMF.blockRpowSum θ σ m` and
`C_m(τ) = RMF.blockCosSum θ σ τ m`:

* **The two-fold block statistics**, within `e^{-m}/10²⁰`: variances `(S_m + C_m(2hᵢ))/2`,
  covariance `(C_m(h₁-h₂) + C_m(h₁+h₂))/2`, means `S_m + C_m(2hᵢ)/2 + C_m(h₁-h₂) + C_m(h₁+h₂)`.
* **The telescoped cosine sums**: `∑_{m₁≤m<M} C_m(τ)` is `∫_{m₁+ξ}^{M+ξ} cos(e^v) dv`,
  `ξ = log τ + θ`, up to the two-regime error `RMF.blockCosTelErr` (explicit Mertens below scale
  `104`) and the damping; it is at most `2e^{-(m₁+ξ)}` however long.
* **The determinant on the post blocks** (`k ≥ 20`): both variances in `[0.3649, 0.6551]` and
  determinant `≥ RMF.pairBlockDet m` (`0.0205`, `0.1136`, `0.0131` on blocks `2`, `3`, `≥ 4`), both
  means at most `1.93`, on every block `m ≥ 4` past the decorrelation point and on `m ∈ {2, 3}` with
  `m ≥ d + 2`.  The shallow blocks `(m, d) ∈ {(0,0), (1,0), (1,1), (2,1), (2,2), (3,2), (3,3)}` are
  not covered.
* **The pair mass** per block: `E|F_B(s₁)|²|F_B(s₂)|² ≤
  E|F_B(s₁)|²E|F_B(s₂)|²·exp(2(C_m(h₁-h₂) + C_m(h₁+h₂)) + e^{-m}/10²⁰)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The numerical condition `hnum` at large offsets -/

/-- **The left side of `hnum`**: `(3600 + 4/√(2πV₁) + 4/√(2πV₂))(2T_m)^{1/4} ≤ e^{12 - e^{m+θ}/8}`
for variances `≥ 1/100` and `m + θ ≥ 0`. -/
lemma blockNum_lhs_le_exp {θ : ℝ} {m : ℕ} {V₁ V₂ : ℝ} (hmθ : 0 ≤ (m : ℝ) + θ)
    (hV₁ : 1 / 100 ≤ V₁) (hV₂ : 1 / 100 ≤ V₂) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) ≤ Real.exp (12 - Real.exp ((m : ℝ) + θ) / 8) := by
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp ((m : ℝ) + θ) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp hmθ
  rw [← hEdef]
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]; exact Real.exp_pos _
  have hT0 : 0 ≤ 2 * blockTAdd θ m := by have := blockTAdd_pos hlogpos; linarith
  have hT : 2 * blockTAdd θ m ≤ Real.exp (12 - E / 2) := by
    have hsq : Real.sqrt (blockScale θ m) = Real.exp (E / 2) := by
      rw [hEdef, blockScale, ← Real.exp_half]
    have hLm : Real.log (blockScale θ m) = E := by rw [hEdef, log_blockScale]
    have hexp3 : Real.exp 3 ≤ 21 := by
      simpa using exp_natCast_le_of_pow_le (c := 2.7182818286) (k := 3)
        (by linarith [Real.exp_one_lt_d9]) (by norm_num)
    have hlog4 : 8 * Real.log 4 ≤ 12 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        push_cast
        ring
      rw [h4]
      linarith [Real.log_two_lt_d9]
    have hlog40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      linarith
    have hK : blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4)) ≤ 50400 := by
      have hA : Real.exp 3 * (8 * Real.log 4) ≤ 21 * 12 :=
        mul_le_mul hexp3 hlog4 hlog40 (by norm_num)
      have hA0 : (0 : ℝ) ≤ Real.exp 3 * (8 * Real.log 4) :=
        mul_nonneg (Real.exp_pos 3).le hlog40
      calc blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4))
          ≤ 200 * (Real.exp 3 * (8 * Real.log 4)) :=
            mul_le_mul_of_nonneg_right blockThirdConstAdd_le hA0
        _ ≤ 200 * (21 * 12) := mul_le_mul_of_nonneg_left hA (by norm_num)
        _ = 50400 := by norm_num
    have h12 : (100800 : ℝ) ≤ Real.exp 12 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 12) (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    have hden : 0 < Real.exp (E / 2) * E := by positivity
    rw [blockTAdd, hsq, hLm]
    have hrw : 2 * (blockThirdConstAdd
          * (Real.exp 3 * (8 * Real.log 4 / (Real.exp (E / 2) * E))))
        = 2 * (blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4)))
          / (Real.exp (E / 2) * E) := by ring
    have hsplit : Real.exp (12 - E / 2) * (Real.exp (E / 2) * E) = Real.exp 12 * E := by
      rw [← mul_assoc, ← Real.exp_add, show 12 - E / 2 + E / 2 = (12 : ℝ) by ring]
    rw [hrw, div_le_iff₀ hden, hsplit]
    have := le_mul_of_one_le_right (Real.exp_pos 12).le hE1
    linarith
  have hquarter : (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) ≤ Real.exp (3 - E / 8) := by
    calc (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) ≤ Real.exp (12 - E / 2) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hT0 hT (by norm_num)
      _ = Real.exp (3 - E / 8) := by
          rw [← Real.exp_mul]
          congr 1
          ring
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hc : ∀ V : ℝ, 1 / 100 ≤ V → 4 / Real.sqrt (2 * Real.pi * V) ≤ 16 := by
    intro V hV
    have hs : (1 / 4 : ℝ) ≤ Real.sqrt (2 * Real.pi * V) := by
      have h := Real.sqrt_le_sqrt (show ((1 / 4 : ℝ)) ^ 2 ≤ 2 * Real.pi * V by nlinarith)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)] at h
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hcoef : 3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂)
      ≤ Real.exp 9 := by
    have h9 : (3632 : ℝ) ≤ Real.exp 9 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 9) (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    linarith [hc V₁ hV₁, hc V₂ hV₂]
  have hq0 : 0 ≤ (2 * blockTAdd θ m) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT0 _
  calc (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * (2 * blockTAdd θ m) ^ (1 / 4 : ℝ)
      ≤ Real.exp 9 * Real.exp (3 - E / 8) :=
        mul_le_mul hcoef hquarter hq0 (Real.exp_pos 9).le
    _ = Real.exp (12 - E / 8) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ### The two-fold block statistics in closed form

Under the tilt by `|F_y(s₁)|²|F_y(s₂)|²` at `sᵢ = ½+σ+ihᵢ`, on block `m` past offset `20`, with
`S_m = RMF.blockRpowSum θ σ m` and `C_m(τ) = RMF.blockCosSum θ σ τ m`: the variance at `½+σ+ih` is
`(S_m + C_m(2h))/2`, the covariance `(C_m(h₁-h₂) + C_m(h₁+h₂))/2` and the mean of walk `i`
`S_m + C_m(2hᵢ)/2 + C_m(h₁-h₂) + C_m(h₁+h₂)`, each within `e^{-m}/10²⁰`.  Against the one-point
centring the pair tilt pushes each walk by `C_m(h₁-h₂) + C_m(h₁+h₂)` per block. -/

/-- `C_m(-τ) = C_m(τ)`: the cosine is even. -/
lemma blockCosSum_neg (θ σ τ : ℝ) (m : ℕ) : blockCosSum θ σ (-τ) m = blockCosSum θ σ τ m := by
  unfold blockCosSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [neg_mul, Real.cos_neg]

/-- `C_m(|τ|) = C_m(τ)`. -/
lemma blockCosSum_abs (θ σ τ : ℝ) (m : ℕ) : blockCosSum θ σ |τ| m = blockCosSum θ σ τ m := by
  rcases abs_choice τ with h | h <;> rw [h]
  exact blockCosSum_neg θ σ τ m

/-- The two-fold per-prime remainders against `r³ ≤ E`, `0 ≤ r ≤ 1`, with every radius `r`: the
variance's `8r³ + 36(2r)²r²`, the covariance's `4(r³+r³) + 36(2r)²r²` and the mean's
`36r³ + 6(2r)³r`, each at most `152E`. -/
private lemma pair_remainders_le {r E : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hE : r ^ 3 ≤ E) :
    8 * r ^ 3 + 36 * (r + r) ^ 2 * r ^ 2 ≤ 152 * E
      ∧ 4 * (r ^ 3 + r ^ 3) + 36 * (r + r) ^ 2 * (r * r) ≤ 152 * E
      ∧ 36 * r ^ 3 + 6 * (r + r) ^ 3 * r ≤ 152 * E := by
  have h4 : r ^ 4 ≤ r ^ 3 := by
    rw [show r ^ 4 = r * r ^ 3 by ring]
    exact mul_le_of_le_one_left (pow_nonneg hr0 3) hr1
  have h3 : 0 ≤ r ^ 3 := pow_nonneg hr0 3
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [show (r + r) ^ 2 * r ^ 2 = 4 * r ^ 4 by ring]
  · nlinarith [show (r + r) ^ 2 * (r * r) = 4 * r ^ 4 by ring]
  · nlinarith [show (r + r) ^ 3 * r = 8 * r ^ 4 by ring]

/-- The tilt radii past offset `20`: each `‖p^{-(½+σ+it)}‖ ≤ 10⁻⁴⁰`, so their sum is `≤ 1/2`. -/
lemma norm_add_norm_cpow_shiftLine_le {θ σ h₁ h₂ : ℝ} {m : ℕ} (hσ : 0 ≤ σ)
    (hm : 20 ≤ (m : ℝ) + θ) {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))‖ + ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))‖ ≤ 1 / 2 := by
  have h1 := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h₁) hp
  have h2 := norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h₂) hp
  have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 4 := by norm_num
  linarith

/-- **A two-fold block variance**: under the tilt at `s₁ = ½+σ+ih₁`, `s₂ = ½+σ+ih₂`, the block at
`½+σ+ih` has variance `(S_m + C_m(2h))/2` within `e^{-m}/10²⁰` (`σ, θ ≥ 0`, `m + θ ≥ 20`); at
`h = h₁, h₂` these are `V¹_m, V²_m`. -/
theorem abs_blockMatchedVarAdd₂_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h₁ h₂ h : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
      - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h) m) / 2|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  have hr : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ ≤ 1 / 10 ^ 40 :=
    fun p hp => norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h) hp
  have hgap := abs_blockMatchedVarAdd₂_sub_le hX y hs₁ hs₂ hB
    (fun p hp => norm_add_norm_cpow_shiftLine_le hσ hm hp)
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) fun p hp => (hr p hp).trans (by norm_num)
  rw [sum_re_cpow_shiftLine_sq_eq] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 152) (by norm_num)
    fun p hp => ?_)
  rw [norm_cpow_shiftLine_eq p σ h₁ h, norm_cpow_shiftLine_eq p σ h₂ h]
  exact (pair_remainders_le (norm_nonneg _) ((hr p hp).trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ h) hp)).1

/-- `∑ Re p^{-s₁} Re p^{-s₂} = (C_m(h₁-h₂) + C_m(h₁+h₂))/2` on the line `½ + σ`. -/
lemma sum_re_mul_re_cpow_shiftLine_eq (θ σ h₁ h₂ : ℝ) (m : ℕ) :
    ∑ p ∈ primeBlockSub θ m, (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
        * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re
      = (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m) / 2 := by
  rw [blockCosSum, blockCosSum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [re_mul_re_prime_eq p.2]
  simp only [re_shiftLine, im_shiftLine]
  rw [show -(1 / 2 + σ + (1 / 2 + σ)) = -1 - 2 * σ by ring]
  ring

/-- **The two-fold block covariance**: `(C_m(h₁-h₂) + C_m(h₁+h₂))/2` within `e^{-m}/10²⁰`. -/
theorem abs_blockMatchedCovAdd_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h₁ h₂ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMatchedCovAdd X μ y (shiftLine σ h₁) (shiftLine σ h₂)
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁)))
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m)
      - (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m) / 2|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  have hr : ∀ p ∈ primeBlockSub θ m, ∀ t : ℝ,
      ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ t))‖ ≤ 1 / 10 ^ 40 :=
    fun p hp t => norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ t) hp
  have hgap := abs_blockMatchedCovAdd_sub_le hX y hs₁ hs₂ hB
    (fun p hp => norm_add_norm_cpow_shiftLine_le hσ hm hp)
    (v := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁)))
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂)))
    (fun p hp => (hr p hp h₁).trans (by norm_num)) (fun p hp => (hr p hp h₂).trans (by norm_num))
  rw [sum_re_mul_re_cpow_shiftLine_eq] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 152) (by norm_num)
    fun p hp => ?_)
  rw [norm_cpow_shiftLine_eq p σ h₁ h₂]
  exact (pair_remainders_le (norm_nonneg _) ((hr p hp h₂).trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ h₂) hp)).2.1

/-- The two-fold drift at one prime, for walk `i`: `2(Re a₁ + Re a₂)Re aᵢ - Re(aᵢ²)/2
= p^{-1-2σ}(1 + cos(2hᵢ log p)/2 + cos((h₁-h₂)log p) + cos((h₁+h₂)log p))`, stated at walk `1`
with the heights as parameters (walk `2` is the same with `h₁`, `h₂` swapped). -/
lemma pairDrift_prime_eq (p : Nat.Primes) (σ h₁ h₂ : ℝ) :
    2 * ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re + (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re)
        * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
      - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) ^ 2).re / 2
      = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) * (1 + Real.cos (2 * h₁ * Real.log ((p : ℕ) : ℝ)) / 2
          + Real.cos ((h₁ - h₂) * Real.log ((p : ℕ) : ℝ))
          + Real.cos ((h₁ + h₂) * Real.log ((p : ℕ) : ℝ))) := by
  have h1 := rademacherDrift_prime_eq p.2 (re_shiftLine σ h₁) (re_shiftLine σ h₁)
  have h2 := re_mul_re_prime_eq p.2 (shiftLine σ h₁) (shiftLine σ h₂)
  simp only [re_shiftLine, im_shiftLine] at h1 h2
  rw [show -(1 / 2 + σ + (1 / 2 + σ)) = -1 - 2 * σ by ring] at h2
  rw [show 2 * ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
          + (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re)
        * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
        - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) ^ 2).re / 2
      = (2 * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
          * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
        - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) ^ 2).re / 2)
        + 2 * ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
          * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re) by ring, h1, h2,
    sub_self, zero_mul, Real.cos_zero, show h₁ + h₁ = 2 * h₁ by ring]
  ring

/-- **The first two-fold block mean**: `S_m + C_m(2h₁)/2 + C_m(h₁-h₂) + C_m(h₁+h₂)` within
`e^{-m}/10²⁰` — the one-point height mean `S_m + C_m(2h₁)/2` plus the pair's push. -/
theorem abs_blockMeanAdd₂_fst_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h₁ h₂ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub θ m)
      - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₁) m / 2
          + (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m))|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  have hr : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))‖ ≤ 1 / 10 ^ 40 :=
    fun p hp => norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h₁) hp
  have hgap := abs_blockMeanAdd₂_sub_sum_le hX y hs₁ hs₂ hB
    (fun p hp => norm_add_norm_cpow_shiftLine_le hσ hm hp)
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) fun p hp => (hr p hp).trans (by norm_num)
  have hmain : ∑ p ∈ primeBlockSub θ m,
      (2 * ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re + (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re)
          * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re
        - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) ^ 2).re / 2)
      = blockRpowSum θ σ m + blockCosSum θ σ (2 * h₁) m / 2
          + (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m) := by
    rw [blockRpowSum, blockCosSum, blockCosSum, blockCosSum, Finset.sum_div,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pairDrift_prime_eq]
    ring
  rw [hmain] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 152) (by norm_num)
    fun p hp => ?_)
  rw [norm_cpow_shiftLine_eq p σ h₂ h₁]
  exact (pair_remainders_le (norm_nonneg _) ((hr p hp).trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ h₁) hp)).2.2

/-- **The second two-fold block mean**: `S_m + C_m(2h₂)/2 + C_m(h₁-h₂) + C_m(h₁+h₂)` within
`e^{-m}/10²⁰`. -/
theorem abs_blockMeanAdd₂_snd_sub_le_decay (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h₁ h₂ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m)
      - (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₂) m / 2
          + (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m))|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  have hr : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))‖ ≤ 1 / 10 ^ 40 :=
    fun p hp => norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ h₂) hp
  have hgap := abs_blockMeanAdd₂_sub_sum_le hX y hs₁ hs₂ hB
    (fun p hp => norm_add_norm_cpow_shiftLine_le hσ hm hp)
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) fun p hp => (hr p hp).trans (by norm_num)
  have hmain : ∑ p ∈ primeBlockSub θ m,
      (2 * ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re + (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re)
          * (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))).re
        - ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) ^ 2).re / 2)
      = blockRpowSum θ σ m + blockCosSum θ σ (2 * h₂) m / 2
          + (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m) := by
    rw [blockRpowSum, blockCosSum, blockCosSum, blockCosSum, Finset.sum_div,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h := pairDrift_prime_eq p σ h₂ h₁
    rw [show h₂ - h₁ = -(h₁ - h₂) by ring, neg_mul, Real.cos_neg, add_comm h₂ h₁] at h
    rw [add_comm ((((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))).re), h]
    ring
  rw [hmain] at hgap
  refine hgap.trans (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 152) (by norm_num)
    fun p hp => ?_)
  rw [norm_cpow_shiftLine_eq p σ h₁ h₂]
  exact (pair_remainders_le (norm_nonneg _) ((hr p hp).trans (by norm_num))
    (norm_cpow_pow_three_le_of_mem_primeBlockSub_decay hσ hθ hm (re_shiftLine σ h₂) hp)).2.2

/-! ### The telescoped cosine sums

`∑_{m₁≤m<M} C_m(τ)` is the damped integral `∫_{e^{m₁+θ}}^{e^{M+θ}} cos(τu)e^{-2σu}/u du` up to the
summed block errors: at `θ ≥ 104` the prime number theorem's, which decay (`(τ+1)e^{-m}/10²⁸` on
block `m`); from `m₁ + θ ≥ 0` the two-regime `RMF.blockCosTelErr θ m₁ τ` of
`RMF.abs_sum_blockCosSum_sub_integral_le_two_regime` (explicit Mertens below scale `104`; at most
`3.16·10⁻⁶` from `m₁ + θ ≥ 20` for `τ ≤ 2e^{-20}`, at most `1.59(τ+1)e^{-m₁}/10²⁸` from `θ ≥ 104`).
The damped integral is at most `2/(τe^{m₁+θ})` however long, and undamped it is
`∫_{m₁+ξ}^{M+ξ} cos(e^v) dv`, `ξ = log τ + θ`, whose tail is `-Ci(e^{m₁+ξ})`. -/

/-- **The substitution `u = e^v/τ` on any range**: `∫_{e^{a+θ}}^{e^{b+θ}} cos(τu)/u du =
∫_{a+ξ}^{b+ξ} cos(e^v) dv` with `ξ = log τ + θ`, for `τ > 0`. -/
theorem integral_cos_div_eq_integral_cos_exp {τ : ℝ} (hτ : 0 < τ) (θ a b : ℝ) :
    (∫ u in Real.exp (a + θ)..Real.exp (b + θ), Real.cos (τ * u) / u)
      = ∫ v in (a + (Real.log τ + θ))..(b + (Real.log τ + θ)), Real.cos (Real.exp v) := by
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun v => Real.exp v / τ) (f' := fun v => Real.exp v / τ)
    (g := fun u => Real.cos (τ * u) / u)
    (a := a + (Real.log τ + θ)) (b := b + (Real.log τ + θ))
    (Real.continuous_exp.div_const τ).continuousOn
    (fun x _ => (Real.hasDerivAt_exp x).div_const τ) (fun x _ => by positivity)
  have hf : ∀ c : ℝ, Real.exp (c + (Real.log τ + θ)) / τ = Real.exp (c + θ) := by
    intro c
    rw [show c + (Real.log τ + θ) = Real.log τ + (c + θ) by ring, Real.exp_add, Real.exp_log hτ]
    field_simp
  rw [hf a, hf b] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun v _ => ?_
  have hev : Real.exp v / τ ≠ 0 := by positivity
  simp only [Function.comp_apply]
  rw [show τ * (Real.exp v / τ) = Real.exp v by field_simp]
  field_simp

/-- **The telescoped block cosine sums as `∫ cos(e^v) dv`**: for `τ > 0`, `σ ≥ 0`, `m₁ ≤ M` and
`m₁ + θ ≥ 0`, with `ξ = log τ + θ`, `∑_{m₁≤m<M} C_m(τ)` is within
`blockCosTelErr θ m₁ τ + 2σ(e^{M+θ} - e^{m₁+θ})` of `∫_{m₁+ξ}^{M+ξ} cos(e^v) dv`; the second error
is the damping `p^{-2σ}` (`RMF.abs_integral_cos_mul_exp_div_sub_le`). -/
theorem abs_sum_blockCosSum_sub_integral_cos_exp_le {τ σ θ : ℝ} {m₁ M : ℕ} (hmM : m₁ ≤ M)
    (hτ : 0 < τ) (hσ : 0 ≤ σ) (hm₁ : 0 ≤ (m₁ : ℝ) + θ) :
    |∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m
        - ∫ v in ((m₁ : ℝ) + (Real.log τ + θ))..((M : ℝ) + (Real.log τ + θ)),
            Real.cos (Real.exp v)|
      ≤ blockCosTelErr θ m₁ τ
        + 2 * σ * (Real.exp ((M : ℝ) + θ) - Real.exp ((m₁ : ℝ) + θ)) := by
  have hmM' : (m₁ : ℝ) + θ ≤ (M : ℝ) + θ := by
    have : (m₁ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    linarith
  have h1 := abs_sum_blockCosSum_sub_integral_le_two_regime (σ := σ) hmM hτ.le hσ hm₁
  have h2 := abs_integral_cos_mul_exp_div_sub_le (τ := τ) (σ := σ)
    (Real.exp_pos ((m₁ : ℝ) + θ)) (Real.exp_le_exp.2 hmM') hσ
  rw [integral_cos_div_eq_integral_cos_exp hτ θ] at h2
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

/-- **The uniform tail bound**: for `τ > 0`, `σ ≥ 0`, `m₁ + θ ≥ 0` and every `M ≥ m₁`,
`|∑_{m₁≤m<M} C_m(τ)| ≤ 2e^{-(m₁+ξ)} + blockCosTelErr θ m₁ τ`, `ξ = log τ + θ`. -/
theorem abs_sum_blockCosSum_le {τ σ θ : ℝ} {m₁ M : ℕ} (hmM : m₁ ≤ M) (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hm₁ : 0 ≤ (m₁ : ℝ) + θ) :
    |∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m|
      ≤ 2 * Real.exp (-((m₁ : ℝ) + (Real.log τ + θ))) + blockCosTelErr θ m₁ τ := by
  have hmM' : (m₁ : ℝ) + θ ≤ (M : ℝ) + θ := by
    have : (m₁ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    linarith
  have h1 := abs_sum_blockCosSum_sub_integral_le_two_regime (σ := σ) hmM hτ.le hσ hm₁
  have h2 := abs_integral_cos_mul_exp_div_le hτ hσ (Real.exp_pos ((m₁ : ℝ) + θ))
    (Real.exp_le_exp.2 hmM')
  have hξ : Real.exp ((m₁ : ℝ) + (Real.log τ + θ)) = τ * Real.exp ((m₁ : ℝ) + θ) := by
    rw [show (m₁ : ℝ) + (Real.log τ + θ) = Real.log τ + ((m₁ : ℝ) + θ) by ring, Real.exp_add,
      Real.exp_log hτ]
  have he : 2 / (τ * Real.exp ((m₁ : ℝ) + θ))
      = 2 * Real.exp (-((m₁ : ℝ) + (Real.log τ + θ))) := by
    rw [Real.exp_neg, hξ]
    field_simp
  rw [he] at h2
  have htri := abs_add_le (∑ m ∈ Finset.Ico m₁ M, blockCosSum θ σ τ m
      - ∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
    (∫ u in Real.exp ((m₁ : ℝ) + θ)..Real.exp ((M : ℝ) + θ),
      Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
  rw [sub_add_cancel] at htri
  linarith

/-! ### The determinant on the post blocks

The main terms are `Aᵢ = (S_m + C_m(2hᵢ))/2 = ∑w cos²(hᵢ log p)` and
`K = (C_m(h₁-h₂) + C_m(h₁+h₂))/2 = ∑w cos(h₁ log p)cos(h₂ log p)`, so `A₁A₂ - K²` is a Gram
determinant, and the two-fold statistics are within `e^{-m}/10²⁰` of them.  On the post blocks
(`|h₁-h₂|e^{k+m} ≥ e^{-1}`) the difference frequency's `C_m(h₁-h₂)` is a `blockCos` value past
`-1`, in `[-0.76, 0.81]`; the sum frequencies `2h₁, 2h₂, h₁+h₂ ∈ [2e^{-(k+1)}, 2e^{-k}]` decay.
Ranges settle every block `m ≥ 4`, and the blocks `m ∈ {2, 3}` whose difference phase is past `e`.
From `k ≥ 20` every block's cosine error is at most `7.43·10⁻⁸` (`RMF.blockCosErr_le_numeral`),
inside the ranges' rounding; the Gram bounds they certify are exported as `RMF.pairBlockDet`, with
variances in `[0.3649, 0.6551]` and means at most `1.93` (`RMF.pair_block_comparison_inputs_det`,
`RMF.abs_pair_block_means_le`). -/

/-- The determinant under perturbation: `V₁V₂ − K² ≥ AS − c² − 10ε` when `V₁, V₂, K` are within
`ε ≤ 1` of `A, S, c`, with `0 ≤ A, S ≤ 2` and `|c| ≤ 2` (the private `RMF.det_perturb_le` of
`RMF/UniformLower/WindowBlockData.lean`, repeated). -/
private lemma det_perturb_le' {A S c V₁ V₂ K ε : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 2) (hS0 : 0 ≤ S)
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

/-- The Gram determinant from ranges: `lo ≤ A₁, A₂` and `|K| ≤ kk` give
`A₁A₂ − K² ≥ lo² − kk²`. -/
lemma sq_sub_sq_le_det {A₁ A₂ K lo kk : ℝ} (hlo : 0 ≤ lo) (h₁ : lo ≤ A₁) (h₂ : lo ≤ A₂)
    (hK : |K| ≤ kk) : lo ^ 2 - kk ^ 2 ≤ A₁ * A₂ - K ^ 2 := by
  have hA : lo * lo ≤ A₁ * A₂ := mul_le_mul h₁ h₂ hlo (hlo.trans h₁)
  have hK2 : K ^ 2 ≤ kk ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 2
  nlinarith

/-- **`blockCos a 0 ∈ [-0.75, 0.8]` for every `a ≥ -1`**: the certified ranges of the first three
blocks on `[-1, 2]` and `|blockCos a 0| ≤ 2e^{-a}` beyond. -/
lemma blockCos_zero_bounds_of_ge {a : ℝ} (ha : -1 ≤ a) :
    -0.75 ≤ blockCos a 0 ∧ blockCos a 0 ≤ 0.8 := by
  rcases le_or_gt a 0 with h0 | h0
  · have h := blockCos_zero_bounds_one_point ha h0
    constructor <;> linarith [h.1, h.2]
  rcases le_or_gt a 1 with h1 | h1
  · have h := blockCos_one_bounds_one_point (ξ := a - 1) (by linarith) (by linarith)
    have hrw : blockCos (a - 1) 1 = blockCos a 0 := by
      rw [blockCos_eq_zero]
      norm_num
    rw [hrw] at h
    constructor <;> linarith [h.1, h.2]
  rcases le_or_gt a 2 with h2 | h2
  · have h := blockCos_two_bounds_one_point (ξ := a - 2) (by linarith) (by linarith)
    have hrw : blockCos (a - 2) 2 = blockCos a 0 := by
      rw [blockCos_eq_zero]
      norm_num
    rw [hrw] at h
    constructor <;> linarith [h.1, h.2]
  · have h := abs_blockCos_le a 0
    rw [Nat.cast_zero, zero_add] at h
    have he : Real.exp (-a) ≤ 0.136 := by
      have h2' : (7.38 : ℝ) ≤ Real.exp 2 := by
        simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 2) (by norm_num)
          (by linarith [Real.exp_one_gt_d9]) (by norm_num)
      have h3 : Real.exp (-a) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
      have h4 : Real.exp (-2) ≤ 0.136 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
        linarith
      linarith
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]

/-- **`blockCos a 0 ∈ [-0.25, 0.35]` for every `a ≥ 1`**: blocks `2` and `3` of the certified
ranges on `[1, 3]` and `|blockCos a 0| ≤ 2e^{-a}` beyond. -/
lemma blockCos_zero_bounds_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    -0.25 ≤ blockCos a 0 ∧ blockCos a 0 ≤ 0.35 := by
  rcases le_or_gt a 2 with h2 | h2
  · have h := blockCos_two_bounds_one_point (ξ := a - 2) (by linarith) (by linarith)
    have hrw : blockCos (a - 2) 2 = blockCos a 0 := by
      rw [blockCos_eq_zero]
      norm_num
    rw [hrw] at h
    constructor <;> linarith [h.1, h.2]
  rcases le_or_gt a 3 with h3 | h3
  · have h := blockCos_three_bounds_one_point (ξ := a - 3) (by linarith) (by linarith)
    have hrw : blockCos (a - 3) 3 = blockCos a 0 := by
      rw [blockCos_eq_zero]
      norm_num
    rw [hrw] at h
    constructor <;> linarith [h.1, h.2]
  · have h := abs_blockCos_le a 0
    rw [Nat.cast_zero, zero_add] at h
    have he : Real.exp (-a) ≤ 0.05 := by
      have h3' : (20 : ℝ) ≤ Real.exp 3 := by
        simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 3) (by norm_num)
          (by linarith [Real.exp_one_gt_d9]) (by norm_num)
      have h4 : Real.exp (-a) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
      have h5 : Real.exp (-3) ≤ 0.05 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 3)]
        linarith
      linarith
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]

/-- **The difference frequency past the decorrelation point**: if `e^{-1} ≤ |D|e^{k+m}`,
`σe^{k+m+1} ≤ 1/200` and the block's cosine error `RMF.blockCosErr k m |D|` is at most `10⁻³`
(`≤ 7.43·10⁻⁸` for `k ≥ 20`, `|D| ≤ 2e^{-20}`, `RMF.blockCosErr_le_numeral`), then
`C_m(D) ∈ [-0.761, 0.811]`; if moreover `e ≤ |D|e^{k+m}`, then `C_m(D) ∈ [-0.261, 0.361]`
(`blockCos` at `m + log|D| + k`, transferred). -/
lemma blockCosSum_diff_bounds {k m : ℕ} {σ D : ℝ} (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) (herr : blockCosErr k m |D| ≤ 1 / 1000)
    (hdep : Real.exp (-1) ≤ |D| * Real.exp ((k : ℝ) + m)) :
    (-0.761 ≤ blockCosSum k σ D m ∧ blockCosSum k σ D m ≤ 0.811)
      ∧ (Real.exp 1 ≤ |D| * Real.exp ((k : ℝ) + m) →
        -0.261 ≤ blockCosSum k σ D m ∧ blockCosSum k σ D m ≤ 0.361) := by
  have hD0 : 0 < |D| := by
    rcases (abs_nonneg D).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hdep
      exact absurd hdep (not_le.2 (Real.exp_pos _))
  rw [← blockCosSum_abs]
  have hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 100 := by linarith
  have ha : (m : ℝ) + (Real.log |D| + k) = Real.log (|D| * Real.exp ((k : ℝ) + m)) := by
    rw [Real.log_mul hD0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have htr : ∀ lo hi : ℝ, lo ≤ blockCos ((m : ℝ) + (Real.log |D| + k)) 0 →
      blockCos ((m : ℝ) + (Real.log |D| + k)) 0 ≤ hi →
      lo - 0.011 ≤ blockCosSum k σ |D| m ∧ blockCosSum k σ |D| m ≤ hi + 0.011 := by
    intro lo hi hlo hhi
    rw [← blockCos_eq_zero] at hlo hhi
    have h := blockCosSum_mem_of_blockCos hσ hD0 hδ ⟨hlo, hhi⟩
    constructor <;> linarith [h.1, h.2]
  refine ⟨?_, fun he => ?_⟩
  · have ha1 : -1 ≤ (m : ℝ) + (Real.log |D| + k) := by
      rw [ha]
      have := Real.log_le_log (Real.exp_pos _) hdep
      rwa [Real.log_exp] at this
    obtain ⟨h1, h2⟩ := blockCos_zero_bounds_of_ge ha1
    have h := htr _ _ h1 h2
    constructor <;> linarith [h.1, h.2]
  · have ha1 : 1 ≤ (m : ℝ) + (Real.log |D| + k) := by
      rw [ha]
      have := Real.log_le_log (Real.exp_pos _) he
      rwa [Real.log_exp] at this
    obtain ⟨h1, h2⟩ := blockCos_zero_bounds_of_one_le ha1
    have h := htr _ _ h1 h2
    constructor <;> linarith [h.1, h.2]

/-- **The sum frequencies on the post blocks**: for `k ≥ 20`, `2e^{-(k+1)} ≤ τ ≤ 2e^{-k}` (the
window's `2h` and `h₁ + h₂`) and `σe^{k+m+1} ≤ 1/200`: `|C_m(τ)| ≤ 0.0748` for `m ≥ 4`
(`3/(τe^{m+k}) ≤ 1.5e^{1-m}` plus the block's cosine error `≤ 7.43·10⁻⁸`,
`RMF.blockCosErr_le_numeral`), `|C_3(τ)| ≤ 0.1461` and `C_2(τ) ∈ [-0.2601, 0.3101]` (`blockCos`,
transferred). -/
lemma blockCosSum_sum_bounds {k m : ℕ} {σ τ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ τ) (hτ2 : τ ≤ 2 * Real.exp (-(k : ℝ))) :
    (4 ≤ m → |blockCosSum k σ τ m| ≤ 0.0748)
      ∧ (m = 3 → |blockCosSum k σ τ m| ≤ 0.1461)
      ∧ (m = 2 → -0.2601 ≤ blockCosSum k σ τ m ∧ blockCosSum k σ τ m ≤ 0.3101) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hτ20 : τ ≤ 2 * Real.exp (-20) :=
    hτ2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num))
  have herr : blockCosErr k m τ ≤ 7.43 / 10 ^ 8 :=
    blockCosErr_le_numeral (by linarith [Nat.cast_nonneg (α := ℝ) m]) hτ20
  have hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 100 := by linarith
  -- `ξ = log τ + k ∈ [log 2 - 1, log 2]`
  have hξ1 : Real.log 2 - 1 ≤ Real.log τ + k := by
    have h := Real.log_le_log (by positivity) hτ1
    rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
  have hξ2 : Real.log τ + k ≤ Real.log 2 := by
    have h := Real.log_le_log hτ0 hτ2
    rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · have h := abs_sum_cos_primeBlockSub_le_explicit_floor_two_regime τ σ k m hτ0 hσ
      (by positivity)
    have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
    have he3 : (20.07 : ℝ) ≤ Real.exp 3 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 3) (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    have hprod : 2 * Real.exp 3 ≤ τ * Real.exp ((m : ℝ) + k) := by
      calc 2 * Real.exp 3 ≤ 2 * Real.exp ((m : ℝ) - 1) := by gcongr; linarith
        _ = 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp ((m : ℝ) + k) := by
            rw [mul_assoc, ← Real.exp_add]
            ring_nf
        _ ≤ τ * Real.exp ((m : ℝ) + k) := mul_le_mul_of_nonneg_right hτ1 (Real.exp_pos _).le
    have h1 : 3 / (τ * Real.exp ((m : ℝ) + k)) ≤ 0.07474 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 : (7.43 : ℝ) / 10 ^ 8 ≤ 0.00001 := by norm_num
    unfold blockCosSum
    linarith
  · subst hm
    have hb := abs_blockCos_le (Real.log τ + k) 3
    push_cast at hb
    have he : 2 * Real.exp (-((3 : ℝ) + (Real.log τ + k))) ≤ 0.136 := by
      have h1 : Real.exp (-((3 : ℝ) + (Real.log τ + k))) ≤ Real.exp (-(2 + Real.log 2)) :=
        Real.exp_le_exp.2 (by linarith)
      have h2 : Real.exp (-(2 + Real.log 2)) = Real.exp (-2) / 2 := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_log two_pos]
        ring
      have h3 : Real.exp (-2) ≤ 0.136 := by
        have h2' : (7.38 : ℝ) ≤ Real.exp 2 := by
          simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 2) (by norm_num)
            (by linarith [Real.exp_one_gt_d9]) (by norm_num)
        rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
        linarith
      linarith
    have h := blockCosSum_mem_of_blockCos (lo := -0.136) (hi := 0.136) hσ hτ0 hδ
      ⟨by linarith [(abs_le.1 hb).1], by linarith [(abs_le.1 hb).2]⟩
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  · subst hm
    have h := blockCosSum_mem_of_blockCos hσ hτ0 hδ (blockCos_two_bounds_doubled hξ1 hξ2)
    constructor <;> linarith [h.1, h.2]

/-- The main-term inputs from ranges: `S ≥ 0.99`, `C₁, C₂ ≥ 2lo - 0.99` and `|CD + CS| ≤ 2kk`
give `Aᵢ ≥ lo` and `A₁A₂ − K² ≥ lo² − kk²`. -/
private lemma pair_main_of_ranges {S C₁ C₂ CD CS lo kk : ℝ} (hS : 0.99 ≤ S) (hlo : 0 ≤ lo)
    (h₁ : 2 * lo - 0.99 ≤ C₁) (h₂ : 2 * lo - 0.99 ≤ C₂) (hK : |CD + CS| ≤ 2 * kk) :
    lo ≤ (S + C₁) / 2 ∧ lo ≤ (S + C₂) / 2
      ∧ lo ^ 2 - kk ^ 2 ≤ (S + C₁) / 2 * ((S + C₂) / 2) - ((CD + CS) / 2) ^ 2 := by
  have hA₁ : lo ≤ (S + C₁) / 2 := by linarith
  have hA₂ : lo ≤ (S + C₂) / 2 := by linarith
  have hK' : |(CD + CS) / 2| ≤ kk := by
    rw [abs_div, abs_two]
    linarith
  exact ⟨hA₁, hA₂, sq_sub_sq_le_det hlo hA₁ hA₂ hK'⟩

/-- **The certified two-fold determinant floor of the post blocks**: `0.0205` on block `2`,
`0.1136` on block `3`, `0.0131` on every other block — the Gram bound `lo² − kk²` of the ranges
(`lo, kk = 0.3649, 0.3356`; `0.4219, 0.2536`; `0.4576, 0.443`), rounded down.  Post blocks have
`m ≥ 2` (`RMF.pair_block_comparison_inputs_det`). -/
noncomputable def pairBlockDet (m : ℕ) : ℝ :=
  if m = 2 then 0.0205 else if m = 3 then 0.1136 else 0.0131

/-- `pairBlockDet m ≥ 0.0131` on every block. -/
lemma le_pairBlockDet (m : ℕ) : 0.0131 ≤ pairBlockDet m := by
  unfold pairBlockDet
  split_ifs <;> norm_num

/-- The main terms on a post block from `k ≥ 20`, by the ranges of `RMF.blockCosSum_sum_bounds`,
`RMF.blockCosSum_diff_bounds` and `S_m ∈ [0.99, 1 + 1/150000]`: `Aᵢ = (S_m + C_m(2hᵢ))/2` lies in
`[0.36495, 0.65506]`, `A₁A₂ − K² ≥ pairBlockDet m + 10⁻¹⁹` for `K = (C_m(h₁-h₂) + C_m(h₁+h₂))/2`,
and the two-fold means' closed forms `S_m + C_m(2hᵢ)/2 + C_m(h₁-h₂) + C_m(h₁+h₂)` are at most
`1.9233` in absolute value. -/
private lemma pair_post_main {k m : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + m))
    (hcase : 4 ≤ m ∨ (2 ≤ m ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + m))) :
    (0.36495 ≤ (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m) / 2
        ∧ (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m) / 2 ≤ 0.65506)
      ∧ (0.36495 ≤ (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m) / 2
        ∧ (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m) / 2 ≤ 0.65506)
      ∧ pairBlockDet m + 1 / 10 ^ 19 ≤ (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m) / 2
          * ((blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m) / 2)
        - ((blockCosSum k σ (h₁ - h₂) m + blockCosSum k σ (h₁ + h₂) m) / 2) ^ 2
      ∧ |blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m / 2
          + (blockCosSum k σ (h₁ - h₂) m + blockCosSum k σ (h₁ + h₂) m)| ≤ 1.9233
      ∧ |blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m / 2
          + (blockCosSum k σ (h₁ - h₂) m + blockCosSum k σ (h₁ + h₂) m)| ≤ 1.9233 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (20 : ℝ) ≤ (m : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) m]
  -- the window: `2hᵢ, h₁ + h₂ ∈ [2e^{-(k+1)}, 2e^{-k}]`, `|h₁ - h₂| ≤ e^{-k} ≤ e^{-20}`
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hek : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
  have hek1 : 0 < Real.exp (-((k : ℝ) + 1)) := Real.exp_pos _
  have he20 : 0 < Real.exp (-20 : ℝ) := Real.exp_pos _
  have hD : |h₁ - h₂| ≤ 2 * Real.exp (-20) := by
    rw [abs_le]
    constructor <;> linarith
  have herr : blockCosErr k m |h₁ - h₂| ≤ 1 / 1000 :=
    (blockCosErr_le_numeral hm' hD).trans (by norm_num)
  obtain ⟨hS1, -⟩ := blockRpowSum_bounds hk hσ hσm
  have hS2 := blockRpowSum_le (θ := k) (m := m) hσ (by linarith)
  have hC₁ := blockCosSum_sum_bounds (τ := 2 * h₁) hk hσ hσm (by linarith) (by linarith)
  have hC₂ := blockCosSum_sum_bounds (τ := 2 * h₂) hk hσ hσm (by linarith) (by linarith)
  have hCS := blockCosSum_sum_bounds (τ := h₁ + h₂) hk hσ hσm (by linarith) (by linarith)
  obtain ⟨hCD, hCD'⟩ := blockCosSum_diff_bounds hσ hσm herr hdep
  generalize blockRpowSum k σ m = S at *
  generalize blockCosSum k σ (2 * h₁) m = C₁ at *
  generalize blockCosSum k σ (2 * h₂) m = C₂ at *
  generalize blockCosSum k σ (h₁ - h₂) m = CD at *
  generalize blockCosSum k σ (h₁ + h₂) m = CS at *
  rw [abs_le, abs_le]
  rcases le_or_gt 4 m with h4 | h4
  · -- `m ≥ 4`: `|Cᵢ|, |C_S| ≤ 0.0748`, `C_D ∈ [-0.761, 0.811]`
    have e₁ := abs_le.1 (hC₁.1 h4)
    have e₂ := abs_le.1 (hC₂.1 h4)
    have eS := abs_le.1 (hCS.1 h4)
    obtain ⟨-, -, hd⟩ := pair_main_of_ranges (C₁ := C₁) (C₂ := C₂) (CD := CD) (CS := CS)
      (lo := 0.4576) (kk := 0.443) hS1 (by norm_num) (by linarith) (by linarith)
      (abs_le.2 ⟨by linarith, by linarith⟩)
    have hpd : pairBlockDet m = 0.0131 := by
      simp only [pairBlockDet, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
    rw [hpd]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, le_trans (by norm_num) hd,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨h2, he⟩ := hcase.resolve_left (by omega)
    obtain ⟨hDl, hDu⟩ := hCD' he
    rcases (by omega : m = 2 ∨ m = 3) with hm | hm
    · -- `m = 2`: `Cᵢ, C_S ∈ [-0.2601, 0.3101]`, `C_D ∈ [-0.261, 0.361]`
      obtain ⟨e₁l, e₁u⟩ := hC₁.2.2 hm
      obtain ⟨e₂l, e₂u⟩ := hC₂.2.2 hm
      obtain ⟨eSl, eSu⟩ := hCS.2.2 hm
      obtain ⟨-, -, hd⟩ := pair_main_of_ranges (C₁ := C₁) (C₂ := C₂) (CD := CD) (CS := CS)
        (lo := 0.3649) (kk := 0.3356) hS1 (by norm_num) (by linarith) (by linarith)
        (abs_le.2 ⟨by linarith, by linarith⟩)
      have hpd : pairBlockDet m = 0.0205 := by simp [pairBlockDet, hm]
      rw [hpd]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, le_trans (by norm_num) hd,
        ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · -- `m = 3`: `|Cᵢ|, |C_S| ≤ 0.1461`, `C_D ∈ [-0.261, 0.361]`
      have e₁ := abs_le.1 (hC₁.2.1 hm)
      have e₂ := abs_le.1 (hC₂.2.1 hm)
      have eS := abs_le.1 (hCS.2.1 hm)
      obtain ⟨-, -, hd⟩ := pair_main_of_ranges (C₁ := C₁) (C₂ := C₂) (CD := CD) (CS := CS)
        (lo := 0.4219) (kk := 0.2536) hS1 (by norm_num) (by linarith) (by linarith)
        (abs_le.2 ⟨by linarith, by linarith⟩)
      have hpd : pairBlockDet m = 0.1136 := by simp [pairBlockDet, hm]
      rw [hpd]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, le_trans (by norm_num) hd,
        ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The two-fold statistics from main-term bounds: on block `m` (`σ, θ ≥ 0`, `m + θ ≥ 20`), if
`lo ≤ Aᵢ ≤ hi` for `Aᵢ = (S_m + C_m(2hᵢ))/2` and `A₁A₂ − K² ≥ g + 10⁻¹⁹` for
`K = (C_m(h₁-h₂) + C_m(h₁+h₂))/2`, then both two-fold variances lie in
`[lo - 10⁻²⁰, hi + 10⁻²⁰]` and `V¹V² − cov² ≥ g` (the closed forms within `e^{-m}/10²⁰`). -/
private lemma pair_block_stats_of_main (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {θ σ h₁ h₂ lo hi g : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y)
    (hA₁ : lo ≤ (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₁) m) / 2
      ∧ (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₁) m) / 2 ≤ hi)
    (hA₂ : lo ≤ (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₂) m) / 2
      ∧ (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₂) m) / 2 ≤ hi)
    (hdet : g + 1 / 10 ^ 19 ≤ (blockRpowSum θ σ m + blockCosSum θ σ (2 * h₁) m) / 2
        * ((blockRpowSum θ σ m + blockCosSum θ σ (2 * h₂) m) / 2)
      - ((blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m) / 2) ^ 2) :
    (lo - 1 / 10 ^ 20 ≤ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ≤ hi + 1 / 10 ^ 20)
      ∧ (lo - 1 / 10 ^ 20 ≤ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ≤ hi + 1 / 10 ^ 20)
      ∧ g ≤ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        - blockMatchedCovAdd X μ y (shiftLine σ h₁) (shiftLine σ h₂)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁)))
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m) ^ 2 := by
  have hV₁ := abs_blockMatchedVarAdd₂_sub_le_decay hX y (h₁ := h₁) (h₂ := h₂) (h := h₁)
    hσ hθ hm hB
  have hV₂ := abs_blockMatchedVarAdd₂_sub_le_decay hX y (h₁ := h₁) (h₂ := h₂) (h := h₂)
    hσ hθ hm hB
  have hK := abs_blockMatchedCovAdd_sub_le_decay hX y (h₁ := h₁) (h₂ := h₂) hσ hθ hm hB
  have hS := blockRpowSum_le (θ := θ) (m := m) hσ (by linarith)
  have hS0 := blockRpowSum_nonneg θ σ m
  have hc₁ := abs_le.1 (abs_blockCosSum_le_blockRpowSum θ σ (2 * h₁) m)
  have hc₂ := abs_le.1 (abs_blockCosSum_le_blockRpowSum θ σ (2 * h₂) m)
  have hcD := abs_le.1 (abs_blockCosSum_le_blockRpowSum θ σ (h₁ - h₂) m)
  have hcS := abs_le.1 (abs_blockCosSum_le_blockRpowSum θ σ (h₁ + h₂) m)
  have hε0 : 0 ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by positivity
  have hε1 : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 := by
    have : Real.exp (-(m : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
    exact div_le_div_of_nonneg_right this (by positivity)
  generalize ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub θ m) : ℝ≥0) : ℝ) = V₁ at *
  generalize ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m) : ℝ≥0) : ℝ) = V₂ at *
  generalize blockMatchedCovAdd X μ y (shiftLine σ h₁) (shiftLine σ h₂)
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁)))
      (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub θ m) = K at *
  generalize Real.exp (-(m : ℝ)) / 10 ^ 20 = ε at *
  generalize blockRpowSum θ σ m = S at *
  generalize blockCosSum θ σ (2 * h₁) m = C₁ at *
  generalize blockCosSum θ σ (2 * h₂) m = C₂ at *
  generalize blockCosSum θ σ (h₁ - h₂) m = CD at *
  generalize blockCosSum θ σ (h₁ + h₂) m = CS at *
  have hp := det_perturb_le' (A := (S + C₁) / 2) (S := (S + C₂) / 2) (c := (CD + CS) / 2)
    (V₁ := V₁) (V₂ := V₂) (K := K) (by linarith) (by linarith) (by linarith) (by linarith)
    (abs_le.2 ⟨by linarith, by linarith⟩) hε0 (by linarith) hV₁ hV₂ hK
  rw [abs_le] at hV₁ hV₂
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  linarith

/-- **The two-fold comparison's inputs on the post blocks, with the certified determinant**: for
`h₁, h₂ ∈ halfWindow k`, `k ≥ 20`, `σ ≥ 0` with `σe^{k+m+1} ≤ 1/200` and a post block `m` (past
the decorrelation point, with `m ≥ 4` or `m ≥ 2` and the difference phase past `e`): both two-fold
variances lie in `[0.3649, 0.6551]` and `V¹V² − cov² ≥ pairBlockDet m` (`0.0205`, `0.1136`,
`0.0131` on blocks `2`, `3`, `≥ 4`). -/
theorem pair_block_comparison_inputs_det (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {k m : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + m))
    (hcase : 4 ≤ m ∨ (2 ≤ m ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + m)))
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    (0.3649 ≤ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          ≤ 0.6551)
      ∧ (0.3649 ≤ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        ∧ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
          (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          ≤ 0.6551)
      ∧ pairBlockDet m ≤ ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub k m) : ℝ≥0) : ℝ)
          * ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub k m) : ℝ≥0) : ℝ)
        - blockMatchedCovAdd X μ y (shiftLine σ h₁) (shiftLine σ h₂)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁)))
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub k m) ^ 2 := by
  have hm' : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨hA₁, hA₂, hdet, -, -⟩ := pair_post_main hk hh₁ hh₂ hσ hσm hdep hcase
  obtain ⟨hV₁, hV₂, hd⟩ := pair_block_stats_of_main hX y hσ (by positivity) hm' hB hA₁ hA₂ hdet
  exact ⟨⟨by linarith [hV₁.1], by linarith [hV₁.2]⟩, ⟨by linarith [hV₂.1], by linarith [hV₂.2]⟩,
    hd⟩

/-- **The two-fold block means on the post blocks**: under the hypotheses of
`RMF.pair_block_comparison_inputs_det`, both two-fold tilted means
(`S_m + C_m(2hᵢ)/2 + C_m(h₁-h₂) + C_m(h₁+h₂)` within `e^{-m}/10²⁰`) are at most `1.93` in absolute
value: the two means of the two-fold Gaussian at `sᵢ = ½+σ+ihᵢ`. -/
theorem abs_pair_block_means_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + m))
    (hcase : 4 ≤ m ∨ (2 ≤ m ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + m)))
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    |blockMeanAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (primeBlockSub k m)| ≤ 1.93
      ∧ |blockMeanAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
        (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (primeBlockSub k m)| ≤ 1.93 := by
  have hm' : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨-, -, -, hM₁, hM₂⟩ := pair_post_main hk hh₁ hh₂ hσ hσm hdep hcase
  have e₁ := abs_le.1 (abs_blockMeanAdd₂_fst_sub_le_decay hX y (θ := k) (σ := σ) (h₁ := h₁)
    (h₂ := h₂) (m := m) hσ (by positivity) hm' hB)
  have e₂ := abs_le.1 (abs_blockMeanAdd₂_snd_sub_le_decay hX y (θ := k) (σ := σ) (h₁ := h₁)
    (h₂ := h₂) (m := m) hσ (by positivity) hm' hB)
  have hε : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by simp)) (by positivity)
  rw [abs_le] at hM₁ hM₂
  exact ⟨abs_le.2 ⟨by linarith [e₁.1, hM₁.1], by linarith [e₁.2, hM₁.2]⟩,
    abs_le.2 ⟨by linarith [e₂.1, hM₂.1], by linarith [e₂.2, hM₂.2]⟩⟩

/-! ### The pair mass

`E‖F(s₁)‖²‖F(s₂)‖² = ∏_p ((1+n₁)(1+n₂) + 4Re a₁Re a₂)` exactly
(`RMF.integral_normSq_one_add_pair_rademacherLaw`), `aᵢ = p^{-sᵢ}`, `nᵢ = ‖aᵢ‖²`, and
`E‖F(sᵢ)‖² = ∏_p (1 + nᵢ)`; so the pair mass against the one-point masses is
`∏_p (1 + 4Re a₁Re a₂/((1+n₁)(1+n₂)))`.  On the line `½ + σ`,
`4Re a₁Re a₂ = 2p^{-1-2σ}(cos((h₁-h₂)log p) + cos((h₁+h₂)log p))` (`RMF.localTwoPointMomentAddAt_eq`
in product form). -/

/-- **The pair mass against the one-point masses**: for Rademacher values, any prime range and
`Re sᵢ > 0`, `E‖F(s₁)‖²‖F(s₂)‖² ≤ E‖F(s₁)‖²·E‖F(s₂)‖²·exp(∑_p 4Re a₁Re a₂/((1+‖a₁‖²)(1+‖a₂‖²)))`,
`aᵢ = p^{-sᵢ}`, by `1 + x ≤ eˣ` on each factor of the exact product. -/
theorem integral_normSq_mul_normSq_le_exp (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₂ ω‖ ^ 2
        ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
            ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₂ ω‖
            ^ 2 ∂μ)
        * Real.exp (∑ p ∈ primesIco y₀ y₁, 4 * ((p : ℂ) ^ (-s₁)).re * ((p : ℂ) ^ (-s₂)).re
            / ((1 + ‖(p : ℂ) ^ (-s₁)‖ ^ 2) * (1 + ‖(p : ℂ) ^ (-s₂)‖ ^ 2))) := by
  have hf := hX.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ y₁ s₁ s₂,
    hf.integral_norm_randomEulerProductIco_sq y₀ y₁ s₁,
    hf.integral_norm_randomEulerProductIco_sq y₀ y₁ s₂, Real.exp_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · exact (integral_normSq_one_add_pair_rademacherLaw_pos
      (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₁)
      (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₂)).le
  · rw [integral_normSq_one_add_pair_rademacherLaw
      (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₁)
      (norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs₂)]
    set P := (1 + ‖(p : ℂ) ^ (-s₁)‖ ^ 2) * (1 + ‖(p : ℂ) ^ (-s₂)‖ ^ 2) with hPdef
    have hP : 0 < P := by positivity
    have hx := Real.add_one_le_exp (4 * ((p : ℂ) ^ (-s₁)).re * ((p : ℂ) ^ (-s₂)).re / P)
    have hid : P + 4 * ((p : ℂ) ^ (-s₁)).re * ((p : ℂ) ^ (-s₂)).re
        = P * (4 * ((p : ℂ) ^ (-s₁)).re * ((p : ℂ) ^ (-s₂)).re / P + 1) := by
      field_simp
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hx hP.le

/-- The pair-mass term against its main part: `2nc/(1+n)² ≤ 2nc + 12n²` for `n ≥ 0`,
`|c| ≤ 2`. -/
private lemma pairMass_term_le {n c : ℝ} (hn0 : 0 ≤ n) (hc : |c| ≤ 2) :
    2 * n * c / (1 + n) ^ 2 ≤ 2 * n * c + 12 * n ^ 2 := by
  have hc' := abs_le.1 hc
  rw [div_le_iff₀ (by positivity)]
  have h1 : 0 ≤ (c + 2) * (n * (2 * n + n ^ 2)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [sq_nonneg n, pow_nonneg hn0 3, pow_nonneg hn0 4]

/-- **The pair mass of a block, decaying**: over the primes of block `m` (offset `θ ≥ 0`,
`m + θ ≥ 20`) on the line `½ + σ`, `σ ≥ 0`,
`E‖F_B(s₁)‖²‖F_B(s₂)‖² ≤ E‖F_B(s₁)‖²·E‖F_B(s₂)‖²·exp(2(C_m(h₁-h₂) + C_m(h₁+h₂)) + e^{-m}/10²⁰)`,
`F_B` the Euler product over `(blockScale θ m, blockScale θ (m+1)]`. -/
theorem integral_normSq_mul_normSq_block_le (hX : IsRademacherPrimeValues X μ)
    {θ σ h₁ h₂ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hm : 20 ≤ (m : ℝ) + θ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m⌋₊ + 1) (⌊blockScale θ (m + 1)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m⌋₊ + 1) (⌊blockScale θ (m + 1)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale θ m⌋₊ + 1) (⌊blockScale θ (m + 1)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale θ m⌋₊ + 1) (⌊blockScale θ (m + 1)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp (2 * (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m)
            + Real.exp (-(m : ℝ)) / 10 ^ 20) := by
  have hs : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; linarith
  refine (integral_normSq_mul_normSq_le_exp hX _ _ (hs h₁) (hs h₂)).trans ?_
  gcongr
  -- the exponent, as a sum over the block
  have hblock : primeBlockSub θ m
      = primesIcoSub (⌊blockScale θ m⌋₊ + 1) (⌊blockScale θ (m + 1)⌋₊ + 1) := by
    rw [primeBlockSub, harperBlock, blockScale_rpow_inv_exp_one]
  rw [← sum_primesIcoSub, ← hblock]
  -- per prime: `2nc/(1+n)² ≤ 2nc + 12n²`, `n = p^{-1-2σ}`
  have hterm : ∀ p ∈ primeBlockSub θ m,
      4 * ((((p : ℕ) : ℂ)) ^ (-(shiftLine σ h₁))).re * ((((p : ℕ) : ℂ)) ^ (-(shiftLine σ h₂))).re
          / ((1 + ‖(((p : ℕ) : ℂ)) ^ (-(shiftLine σ h₁))‖ ^ 2)
            * (1 + ‖(((p : ℕ) : ℂ)) ^ (-(shiftLine σ h₂))‖ ^ 2))
        ≤ 2 * (Real.cos ((h₁ - h₂) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
            + Real.cos ((h₁ + h₂) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
          + 12 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2 := by
    intro p hp
    have hn₁ := norm_sq_prime_cpow_neg p (re_shiftLine σ h₁)
    have hn₂ := norm_sq_prime_cpow_neg p (re_shiftLine σ h₂)
    have hre := re_mul_re_prime_eq p.2 (shiftLine σ h₁) (shiftLine σ h₂)
    simp only [re_shiftLine, im_shiftLine] at hre
    rw [show -(1 / 2 + σ + (1 / 2 + σ)) = -1 - 2 * σ by ring] at hre
    have hn0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hc : |Real.cos ((h₁ - h₂) * Real.log ((p : ℕ) : ℝ))
        + Real.cos ((h₁ + h₂) * Real.log ((p : ℕ) : ℝ))| ≤ 2 := by
      have := Real.abs_cos_le_one ((h₁ - h₂) * Real.log ((p : ℕ) : ℝ))
      have := Real.abs_cos_le_one ((h₁ + h₂) * Real.log ((p : ℕ) : ℝ))
      exact (abs_add_le _ _).trans (by linarith)
    rw [hn₁, hn₂, mul_assoc 4, hre]
    have h := pairMass_term_le hn0 hc
    rw [show (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) * (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2 by ring]
    calc 4 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ) * (Real.cos ((h₁ - h₂) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((h₁ + h₂) * Real.log ((p : ℕ) : ℝ))) / 2)
          / (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2
        = 2 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) * (Real.cos ((h₁ - h₂) * Real.log ((p : ℕ) : ℝ))
            + Real.cos ((h₁ + h₂) * Real.log ((p : ℕ) : ℝ)))
          / (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_add_distrib.symm.trans rfl]
  -- the quadratic remainder
  have hrem : ∑ p ∈ primeBlockSub θ m, 12 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
    refine sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 12) (by norm_num)
      fun p hp => ?_
    have hn := rpow_le_of_mem_primeBlockSub_decay hσ hm hp
    have hn0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have he0 : 0 ≤ Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 := by positivity
    have he1 : Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 ≤ 1 := by
      have : Real.exp (-((m : ℝ) + θ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      rw [div_le_one (by positivity)]
      linarith
    have he2 : Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by positivity)
    have hn' : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 := by
      refine hn.trans ?_
      rw [sq]
      calc Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 * (Real.exp (-((m : ℝ) + θ)) / 10 ^ 40)
          ≤ Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 * 1 := mul_le_mul_of_nonneg_left he1 he0
        _ ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 := by linarith
    rw [sq]
    have := mul_le_mul_of_nonneg_right hn' hn0
    nlinarith
  unfold blockCosSum
  linarith

end RMF
