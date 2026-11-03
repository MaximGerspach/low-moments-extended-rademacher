/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherComparisonExplicit
import RMF.Probability.FreeStartAveragedSteinhaus

/-!
# The averaged free start for the Rademacher random multiplicative function

The Rademacher twin of `RMF.freeStart_barrier_le_averaged_steinhaus`.
`RMF.freeStart_barrier_le_averaged` needs, besides the comparison of
`RMF.exists_isGaussianWalk_rademacher_of_le_sharp`,

* the cumulative drift `|∑_{m<j} E~N_m - j| ≤ C` (`RMF.abs_sum_blockGaussMeanAddAt_sub_le_sharp`,
  `C = driftRadSharpOf E₀ 16 K_d`).  The block mean is `S + C_m/2` up to cubic terms
  (`RMF.abs_blockMeanAdd_sub_le_kappa`), so beyond the Steinhaus drift it pays for the oscillatory
  sums, `∑ |C_m|/2 ≤ K_d` once `|C_m| ≤ K_d e^{-m}`, which the explicit prime number theorem gives
  past the floor `104` (`RMF.abs_sum_cos_div_primeBlockSub_le_geometric_floor`);
* the mean and variance of the walk at the free start
  (`RMF.integral_walk_blockSumAdd_tiltedMeasure`, `RMF.integral_sq_walk_blockSumAdd_sub_le`):
  variance at most `0.51r`, against the Steinhaus `(9/2)r`.

## Main results

* `RMF.abs_sum_blockGaussMeanAddAt_sub_le_sharp`
* `RMF.freeStart_barrier_le_averaged_rademacher`
* `RMF.freeStart_barrier_le_averaged_rademacher_of_floor`
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The drift -/

/-- **The weight size decays geometrically in the block index**: `e^η/√x_m ≤ e^η e^{-θ}e^{-m}`,
since `√x_m = exp(e^{m+θ}/2)` and `e^u ≥ 2u` (`Real.two_mul_le_exp`). -/
lemma exp_div_sqrt_blockScale_le_exp_neg (η θ : ℝ) (m : ℕ) :
    Real.exp η / √(blockScale θ m) ≤ Real.exp η * Real.exp (-θ) * Real.exp (-(m : ℝ)) := by
  have hsq : √(blockScale θ m) = Real.exp (Real.exp ((m : ℝ) + θ) / 2) := by
    rw [blockScale, sqrt_exp]
  have hrhs : Real.exp η * Real.exp (-θ) * Real.exp (-(m : ℝ))
      = Real.exp η / Real.exp ((m : ℝ) + θ) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hsq, hrhs]
  refine div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) (Real.exp_le_exp.2 ?_)
  have := Real.two_mul_le_exp (x := (m : ℝ) + θ)
  linarith

/-- `e² ≤ 7.4`. -/
private lemma exp_two_le_seven_four : Real.exp 2 ≤ 7.4 := by
  have h := Real.exp_one_lt_d9
  have hrw : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
  rw [hrw]
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- **The Rademacher block mean against `1`, sharp**: at the block tilt `η`,
`|E~N_m - 1| ≤ 15 min(η, 1) + 60e²e^{-(1+θ)}e^{-m} + |C_m|/2 + 38e^η e^{-θ}e^{-m}`.  The first
two terms are the Steinhaus ones (`RMF.abs_sum_rpow_primeBlockSub_sub_one_le`), the third is the
oscillatory sum and the last the two-atom law's cubic error
(`RMF.abs_blockMeanAdd_sub_le_kappa`). -/
theorem abs_blockMeanAdd_sub_one_le_sharp (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ}
    {m y : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η)
    (hmθ : (16 : ℝ) ≤ (m : ℝ) + θ) (hsc : 28 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hB : primeBlockSub θ m ⊆ primesBelowSub y) :
    |blockMeanAdd X μ y s (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) - 1|
      ≤ 15 * min η 1 + Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
        + |∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| / 2
        + 38 * Real.exp η * Real.exp (-θ) * Real.exp (-(m : ℝ)) := by
  set S := ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) with hSdef
  set C := ∑ p ∈ primeBlockSub θ m,
    Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ) with hCdef
  have hκ := exp_div_sqrt_blockScale_le_millionth hsc
  have hmean := abs_blockMeanAdd_sub_le_kappa hX hs hres (le_trans hκ (by norm_num)) hσ hB
  -- `0 ≤ S ≤ 1 + 1/150000`
  have hwn : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hres
  obtain ⟨-, hShi⟩ := sum_norm_sq_primeBlockSub_bounds_sharp hmθ hσ0 hσ hwn
  rw [Finset.sum_congr rfl hwn] at hShi
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => Real.rpow_nonneg (by positivity) _
  -- the cubic error, `37κS ≤ 38e^η e^{-θ}e^{-m}`
  have hκg := exp_div_sqrt_blockScale_le_exp_neg η θ m
  have hκ0 : 0 ≤ Real.exp η / √(blockScale θ m) := by positivity
  have hcub : 37 * (Real.exp η / √(blockScale θ m)) * S
      ≤ 38 * Real.exp η * Real.exp (-θ) * Real.exp (-(m : ℝ)) := by
    have h1 : 37 * (Real.exp η / √(blockScale θ m)) * S
        ≤ 37 * (Real.exp η / √(blockScale θ m)) * (1 + 1 / 150000) :=
      mul_le_mul_of_nonneg_left hShi (by positivity)
    have h3 : 38 * (Real.exp η / √(blockScale θ m))
        ≤ 38 * (Real.exp η * Real.exp (-θ) * Real.exp (-(m : ℝ))) :=
      mul_le_mul_of_nonneg_left hκg (by norm_num)
    linarith
  -- the Mertens part, `|S - 1| ≤ 15 min(η, 1) + e²·60/log x_{m+1}`
  have hd0 : 0 ≤ 60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))) := by positivity
  have hSm : |S - 1|
      ≤ 15 * min η 1 + Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))) := by
    rcases le_or_gt η 1 with hη1 | hη1
    · have h2 := abs_sum_rpow_primeBlockSub_sub_one_le θ σ η m (by linarith) hη0 hσ
      rw [sixty_div_log_blockScale] at h2
      have hle2 : Real.exp (2 * η) ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)
      have hlin := exp_sub_one_le_mul_exp (2 * η)
      have h2η : 2 * η * Real.exp (2 * η) ≤ 2 * η * Real.exp 2 :=
        mul_le_mul_of_nonneg_left hle2 (by linarith)
      have h74 : 2 * η * Real.exp 2 ≤ 2 * η * 7.4 :=
        mul_le_mul_of_nonneg_left exp_two_le_seven_four (by linarith)
      have hm2 : Real.exp (2 * η) * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
          ≤ Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))) :=
        mul_le_mul_of_nonneg_right hle2 hd0
      rw [min_eq_left hη1]
      linarith
    · have he2 : (0 : ℝ) ≤ Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))) :=
        mul_nonneg (Real.exp_pos _).le hd0
      rw [min_eq_right hη1.le, abs_le]
      constructor <;> linarith
  rw [abs_le] at hmean hSm
  rw [abs_le]
  have hCa := neg_abs_le C
  have hCb := le_abs_self C
  constructor <;> linarith [hmean.1, hmean.2, hSm.1, hSm.2]

/-- **The Rademacher drift constant**: `45√K + 120e²e^{-(1+θ)} + 76e^K e^{-θ} + K_d`.  The first two
summands are those of the Steinhaus `RMF.driftSharpOf`, the third the two-atom law's cubic error and
the last the oscillatory sums, `∑ K_d e^{-m}/2 ≤ K_d`. -/
noncomputable def driftRadSharpOf (K θ Kd : ℝ) : ℝ :=
  45 * Real.sqrt K + 120 * Real.exp 2 * Real.exp (-(1 + θ)) + 76 * Real.exp K * Real.exp (-θ)
    + Kd

lemma driftRadSharpOf_nonneg {K θ Kd : ℝ} (hKd : 0 ≤ Kd) : 0 ≤ driftRadSharpOf K θ Kd := by
  have := Real.sqrt_nonneg K
  rw [driftRadSharpOf]
  positivity

/-- `driftRadSharpOf` increases in the tilt scale and decreases in the offset. -/
lemma driftRadSharpOf_le {K E θ₁ θ₂ Kd : ℝ} (hK : K ≤ E) (hθ : θ₁ ≤ θ₂) :
    driftRadSharpOf K θ₂ Kd ≤ driftRadSharpOf E θ₁ Kd := by
  rw [driftRadSharpOf, driftRadSharpOf]
  have h1 : Real.sqrt K ≤ Real.sqrt E := Real.sqrt_le_sqrt hK
  have h2 : Real.exp K ≤ Real.exp E := Real.exp_le_exp.2 hK
  have h3 : Real.exp (-(1 + θ₂)) ≤ Real.exp (-(1 + θ₁)) := Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (-θ₂) ≤ Real.exp (-θ₁) := Real.exp_le_exp.2 (by linarith)
  have h5 : 120 * Real.exp 2 * Real.exp (-(1 + θ₂)) ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ₁)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : 76 * Real.exp K * Real.exp (-θ₂) ≤ 76 * Real.exp E * Real.exp (-θ₁) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h4 (Real.exp_pos _).le
      (by positivity)
  linarith

/-- **The cumulative Rademacher drift, sharp**: for `θ ≥ 16`, `j ≤ n + 1`, `28 + 2K ≤ e^θ`,
`|σ| log x_{n+1} ≤ K` and oscillatory sums `|C_m| ≤ K_d e^{-m}`,
`|∑_{m<j} E~N_m - j| ≤ driftRadSharpOf K θ K_d`.  The Steinhaus counterpart is
`RMF.abs_sum_blockGaussMean_sub_le_sharp`; the block tilt is `Ke^{m-n}`
(`RMF.sigma_le_mul_exp_sub`). -/
theorem abs_sum_blockGaussMeanAddAt_sub_le_sharp (hX : IsRademacherPrimeValues X μ) {s : ℂ}
    {θ σ K Kd : ℝ} {n j : ℕ} (hθ16 : (16 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hK0 : 0 ≤ K) (hsc : 28 + 2 * K ≤ Real.exp θ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) (hKd : 0 ≤ Kd)
    (hcos : ∀ m, m < j → |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
          ≤ Kd * Real.exp (-(m : ℝ))) :
    |(∑ m ∈ Finset.range j,
        blockGaussMeanAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
        - (j : ℝ)| ≤ driftRadSharpOf K θ Kd := by
  rw [sum_blockGaussMeanAddAt_eq X μ θ (blockCutoff θ n) n s _ hj]
  have hblock : ∀ m ∈ Finset.range j,
      |blockMeanAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
          (primeBlockSub θ m) - 1|
        ≤ 15 * min (K * Real.exp ((m : ℝ) - n)) 1
          + Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
          + Kd * Real.exp (-(m : ℝ)) / 2
          + 38 * Real.exp K * Real.exp (-θ) * Real.exp (-(m : ℝ)) := by
    intro m hm
    have hmj : m < j := Finset.mem_range.1 hm
    have hmn : m ≤ n := by omega
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hem1 : Real.exp ((m : ℝ) - n) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    have hη0 : 0 ≤ K * Real.exp ((m : ℝ) - n) := mul_nonneg hK0 (Real.exp_pos _).le
    have hηK : K * Real.exp ((m : ℝ) - n) ≤ K := mul_le_of_le_one_right hK0 hem1
    have hscm : 28 + 2 * (K * Real.exp ((m : ℝ) - n)) ≤ Real.exp ((m : ℝ) + θ) := by
      have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) := Real.exp_le_exp.2 (by linarith)
      linarith
    have hσm := sigma_le_mul_exp_sub θ σ K (m := m) hσ
    have hs : 0 < s.re := re_pos_of_block_of_le hres (by linarith) hσm
    have h := abs_blockMeanAdd_sub_one_le_sharp hX hs hres hσ0 hη0 (by linarith) hscm hσm
      (primeBlockSub_subset_primesBelowSub_of_le hmn le_rfl)
    have hc := hcos m hmj
    have heK : Real.exp (K * Real.exp ((m : ℝ) - n)) ≤ Real.exp K := Real.exp_le_exp.2 hηK
    have hp : 0 ≤ Real.exp (-θ) * Real.exp (-(m : ℝ)) := by positivity
    have hcub := mul_le_mul_of_nonneg_right heK hp
    linarith
  have hsplit : (∑ m ∈ Finset.range j, blockMeanAdd X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) - (j : ℝ)
      = ∑ m ∈ Finset.range j, (blockMeanAdd X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hA : ∑ m ∈ Finset.range j, 15 * min (K * Real.exp ((m : ℝ) - n)) 1 ≤ 45 * √K := by
    have hterm : ∀ m ∈ Finset.range j,
        15 * min (K * Real.exp ((m : ℝ) - n)) 1
          ≤ 15 * √K * Real.exp (((m : ℝ) - n) / 2) := by
      intro m _
      have h := min_one_le_sqrt (mul_nonneg hK0 (Real.exp_pos ((m : ℝ) - n)).le)
      rw [Real.sqrt_mul hK0, sqrt_exp] at h
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    calc 15 * √K * ∑ m ∈ Finset.range j, Real.exp (((m : ℝ) - n) / 2)
        ≤ 15 * √K * 3 :=
          mul_le_mul_of_nonneg_left (sum_exp_half_sub_le hj) (by positivity)
      _ = 45 * √K := by ring
  have hB : ∑ m ∈ Finset.range j,
        Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
    have hre : ∀ m : ℕ, Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
        = 60 * Real.exp 2 * Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)) := fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => hre m), ← Finset.mul_sum]
    calc 60 * Real.exp 2 * Real.exp (-(1 + θ)) * ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ))
        ≤ 60 * Real.exp 2 * Real.exp (-(1 + θ)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) (by positivity)
      _ = 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by ring
  have hC : ∑ m ∈ Finset.range j, Kd * Real.exp (-(m : ℝ)) / 2 ≤ Kd := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) hKd
    linarith
  have hD : ∑ m ∈ Finset.range j, 38 * Real.exp K * Real.exp (-θ) * Real.exp (-(m : ℝ))
      ≤ 76 * Real.exp K * Real.exp (-θ) := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j)
      (by positivity : (0 : ℝ) ≤ 38 * Real.exp K * Real.exp (-θ))
    linarith
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, driftRadSharpOf]
  linarith [hA, hB, hC, hD]

/-! ### The walk at the free start -/

/-- **The mean of the walk under the tilt**: `E~ W_r = ∑_{m<r} E~N_m` for `r ≤ n`. -/
theorem integral_walk_blockSumAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ}
    {n r : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η) (hrn : r ≤ n) :
    ∫ ω, walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ)
      = ∑ m ∈ Finset.range r,
          blockGaussMeanAddAt X μ θ (blockCutoff θ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m := by
  have hint : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m,
      Integrable (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ) :=
    fun m hm p hp => integrable_localLogAdd_tiltedMeasure hX _ hs
      (primeBlockSub_subset_primesBelowSub θ hm hp)
      (norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hm) hp)
  simp_rw [walk_apply]
  rw [integral_finsetSum _ fun m hm =>
    integrable_finsetSum _ (hint m (by have := Finset.mem_range.1 hm; omega))]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by have := Finset.mem_range.1 hm; omega
  rw [integral_finsetSum _ (hint m hmn), blockGaussMeanAddAt_of_le hmn, blockMeanAdd]

/-- **The variance of the walk under the tilt**: `E~(W_r - E~W_r)² ≤ V₀r` for `r ≤ n` when each
matched block variance is at most `V₀`.  The primes are independent under the tilt, so the variance
is the sum of the matched block variances (`RMF.coe_blockMatchedVarAdd`). -/
theorem integral_sq_walk_blockSumAdd_sub_le (hX : IsRademacherPrimeValues X μ) {θ σ η V₀ : ℝ}
    {n r : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η) (hrn : r ≤ n)
    (hV : ∀ m, m < r → ((blockMatchedVarAdd X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ V₀) :
    ∫ ω, (walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω
        - ∫ ω', walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω'
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ))
          ^ 2
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ)
      ≤ V₀ * r := by
  classical
  set P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ
    with hPdef
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_tiltedMeasure_rademacher hX _ hs
  set S := (Finset.range r).biUnion (fun m => primeBlockSub θ m) with hSdef
  have hdisj : (↑(Finset.range r) : Set ℕ).PairwiseDisjoint (fun m => primeBlockSub θ m) :=
    fun a _ b _ hab => pairwise_disjoint_primeBlockSub θ hab
  have hmem : ∀ p ∈ S, ∃ m, m < r ∧ p ∈ primeBlockSub θ m := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.1 hp
    exact ⟨m, Finset.mem_range.1 hm, hpm⟩
  have hML : ∀ p ∈ S,
      MemLp (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) 2 P := by
    intro p hp
    obtain ⟨m, hmr, hpm⟩ := hmem p hp
    have hmn : m ≤ n := by omega
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).aestronglyMeasurable
    · exact integrable_localLogAdd_sq_tiltedMeasure hX (blockCutoff θ n) hs
        (primeBlockSub_subset_primesBelowSub θ hmn hpm)
        (norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hmn) hpm)
  have hfun : (fun ω => walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω)
      = fun ω => ∑ p ∈ S, localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω) := by
    funext ω
    rw [walk_apply, hSdef, Finset.sum_biUnion hdisj]
  have hWmeas : AEMeasurable (fun ω => walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω) P := by
    rw [hfun]
    exact (Finset.measurable_sum _ fun (p : Nat.Primes) _ =>
      (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).aemeasurable
  rw [← variance_eq_integral hWmeas, hfun]
  have hindep := iIndepFun_localLogAdd_tiltedMeasure_rademacher hX (blockCutoff θ n) hs
    (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))
  have hvar : variance (fun ω => ∑ p ∈ S, localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) P
      = ∑ p ∈ S, variance (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) P := by
    have h := IndepFun.variance_sum hML (fun a _ b _ hab => hindep.indepFun hab)
    have hfe : (∑ p ∈ S, (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)))
        = (fun ω => ∑ p ∈ S, localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) := by
      funext ω
      simp
    rwa [hfe] at h
  rw [hvar, hSdef, Finset.sum_biUnion hdisj]
  have hblock : ∀ m ∈ Finset.range r,
      ∑ p ∈ primeBlockSub θ m, variance (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s))
          (X (p : ℕ) ω)) P ≤ V₀ := by
    intro m hm
    have hmr : m < r := Finset.mem_range.1 hm
    have hmn : m ≤ n := by omega
    have hw : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := fun p hp =>
      norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hmn) hp
    have hcoe := coe_blockMatchedVarAdd hX (blockCutoff θ n) hs
      (primeBlockSub_subset_primesBelowSub θ hmn) hw
    have heq : ∑ p ∈ primeBlockSub θ m, variance (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s))
          (X (p : ℕ) ω)) P
        = ((blockMatchedVarAdd X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
      rw [hcoe]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [variance_eq_sub (hML p (Finset.mem_biUnion.2 ⟨m, hm, hp⟩))]
      simp only [Pi.pow_apply]
      rfl
    rw [heq]
    exact hV m hmr
  calc ∑ m ∈ Finset.range r, ∑ p ∈ primeBlockSub θ m,
        variance (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) P
      ≤ ∑ _m ∈ Finset.range r, V₀ := Finset.sum_le_sum hblock
    _ = V₀ * r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The walk under the tilt is square integrable**: a finite sum of local logarithms, each in
`L²` (`RMF.integrable_localLogAdd_sq_tiltedMeasure`). -/
theorem memLp_walk_blockSumAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ}
    {n r : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η) (hrn : r ≤ n) :
    MemLp (walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r) 2
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ) := by
  have hML : ∀ m ∈ Finset.range r, ∀ p ∈ primeBlockSub θ m,
      MemLp (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) 2
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ) := by
    intro m hm p hp
    have hmn : m ≤ n := by have := Finset.mem_range.1 hm; omega
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).aestronglyMeasurable
    · exact integrable_localLogAdd_sq_tiltedMeasure hX (blockCutoff θ n) hs
        (primeBlockSub_subset_primesBelowSub θ hmn hp)
        (norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hmn) hp)
  have hfun : walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r
      = fun ω => ∑ m ∈ Finset.range r, ∑ p ∈ primeBlockSub θ m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω) := by
    funext ω
    simp only [walk_apply]
  rw [hfun]
  exact memLp_finsetSum _ fun m hm => memLp_finsetSum _ fun p hp => hML m hm p hp

/-! ### The free start -/

/-- The envelope of the free start, `M(j) = (9 + c)j + 10 log j`, as in
`RMF.freeStart_barrier_le_averaged_steinhaus`. -/
noncomputable def freeStartEnv (c : ℝ) (j : ℕ) : ℝ := (9 + c) * (j : ℝ) + 10 * Real.log (j : ℝ)

/-- **The four facts `RMF.freeStart_barrier_le_averaged` asks of the envelope**, law-agnostic:
`M ≥ 0`, `M' = M(m) + M(m+1) + W_m ≥ 0`, `M' ≤ 25 + 2c + (48 + 4c)m` (the comparison's envelope)
and the suffix envelope past the free start.  The proof of the Steinhaus instance, extracted. -/
lemma freeStartEnv_facts {c a : ℝ} {n r : ℕ} {hf : ℕ → ℝ} (hc0 : 0 ≤ c) (hr1 : 1 ≤ r)
    (hra : a ≤ 4 * r) (hrn : r < n) (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    (∀ j, 0 ≤ freeStartEnv c j)
      ∧ (∀ m, 0 ≤ freeStartEnv c m + freeStartEnv c (m + 1) + blockWindow m)
      ∧ (∀ m : ℕ, freeStartEnv c m + freeStartEnv c (m + 1) + blockWindow m
          ≤ 25 + 2 * c + (48 + 4 * c) * (m : ℝ))
      ∧ (∀ i : ℕ, 1 ≤ i → i ≤ n - r →
          2 * a + (1 + c) * r + c * i + |hf r| ≤ freeStartEnv c (r + i) ∧
            2 * a + (1 + c) * r + i + hf (r + i) ≤ freeStartEnv c (r + i)) := by
  have hlogle : ∀ j : ℕ, Real.log (j : ℝ) ≤ (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      linarith [Real.log_le_sub_one_of_pos hj0]
  have hM0 : ∀ j, 0 ≤ freeStartEnv c j := by
    intro j
    have h1 : (0 : ℝ) ≤ (9 + c) * (j : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    rw [freeStartEnv]
    linarith [Real.log_natCast_nonneg j]
  refine ⟨hM0, fun m => by linarith [hM0 m, hM0 (m + 1), (blockWindow_pos m).le], ?_, ?_⟩
  · intro m
    have hW : blockWindow m ≤ 1 := by
      rw [blockWindow, div_le_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have h1 := hlogle m
    have h3 : Real.log ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      rw [hcast]
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      linarith [Real.log_le_sub_one_of_pos hm1]
    have hcm : (0 : ℝ) ≤ c * (m : ℝ) := mul_nonneg hc0 (Nat.cast_nonneg m)
    rw [freeStartEnv, freeStartEnv, hcast]
    rw [hcast] at h3
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  · intro i hi1 hin
    have hfr := hhf r hr1 (by omega)
    have hfri := le_trans (le_abs_self _) (hhf (r + i) (by omega) (by omega))
    have hcast : ((r + i : ℕ) : ℝ) = (r : ℝ) + (i : ℝ) := by push_cast; ring
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hlog : Real.log (r : ℝ) ≤ Real.log ((r + i : ℕ) : ℝ) := by
      rw [hcast]
      exact Real.log_le_log hrpos (by linarith [Nat.cast_nonneg (α := ℝ) i])
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hci : (0 : ℝ) ≤ c * (i : ℝ) := mul_nonneg hc0 hi0
    rw [freeStartEnv]
    rw [hcast] at hlog hfri ⊢
    constructor <;> nlinarith

/-- The block offset of the Rademacher free start: `RMF.radUpperThreshold` at the envelope of
`RMF.freeStartEnv_facts`, `25 + 2c + (48 + 4c)m` with `c = prop5UpperSlope`. -/
noncomputable def radFreeStartThreshold (E₀ : ℝ) : ℝ :=
  radUpperThreshold E₀ (25 + 2 * prop5UpperSlope) (48 + 4 * prop5UpperSlope)

set_option maxHeartbeats 1000000 in
-- the envelope, the comparison, the drift and the two moments of `W_r`, fed to one theorem
/-- **Proposition 5's upper half with the free start averaged, for the Rademacher RMF.**  At the
threshold `RMF.radFreeStartThreshold E₀`, slope `c = prop5UpperSlope`, any free start `r ≥ a/4` and
any `hf ≤ β log` with `|hf| ≤ 10 log`, and oscillatory sums `|C_m| ≤ K_d e^{-m}` with
`K_d ≤ e^{-2E₀}/100`,
`P~(W_j ∈ [-a - cj, a + j + hf(j)] ∀ r ≤ j ≤ n)
  ≤ (1 + e^{-100})K(a + 2 + 3C + β(log r + log 2) + 0.51r/(4a) + s_R)/((1 - 2β/T)√(n - r))`,
`C = driftRadSharpOf E₀ 16 K_d`, for any constants `K`, `T`, `s_R ≥ 0` at which Probability
Result 1 holds in affine form for the variances `[0.49e^{-2E₀}, 1]` (`RMF.Result1Affine`).
The Rademacher twin of `RMF.freeStart_barrier_le_averaged_steinhaus`; `hcos` is produced by
`RMF.abs_sum_cos_div_primeBlockSub_le_geometric_floor` past the floor `104`. -/
theorem freeStart_barrier_le_averaged_rademacher (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (hX : IsRademacherPrimeValues X μ) {ϑ σ η a β K T Kd : ℝ} {n r : ℕ} {s : ℂ} {hf : ℕ → ℝ}
    (hϑ : radFreeStartThreshold E₀ ≤ ϑ) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η)
    (hηE : η ≤ E₀) (hσ : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η)
    (hKd0 : 0 ≤ Kd) (hKd : Kd ≤ Real.exp (-(2 * E₀)) / 100)
    (hcos : ∀ m, m ≤ n → |∑ p ∈ primeBlockSub ϑ m,
        Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
          ≤ Kd * Real.exp (-(m : ℝ)))
    (ha : 0 < a) (hr1 : 1 ≤ r) (hra : a ≤ 4 * r) (hrn : r < n)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j)
    (hβ : 0 ≤ β) (hhfβ : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ β * Real.log j)
    (hK : 0 < K) (hT : 2 * β < T) {sR : ℝ} (hsR : 0 ≤ sR)
    (hR1 : Result1Affine.{0} (0.49 * Real.exp (-(2 * E₀))) 1 β K T sR) :
    ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
        {ω | ∀ j, r ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
      ≤ (1 + Real.exp (-100)) * (K * ((a + 2 + 3 * driftRadSharpOf E₀ 16 Kd
          + β * (Real.log r + Real.log 2) + 0.51 * r / (4 * a)
          + sR) / (1 - 2 * β / T)) / √((n - r : ℕ) : ℝ)) := by
  set c := prop5UpperSlope with hcdef
  have hc20 : (20 : ℝ) ≤ c := twenty_le_prop5UpperSlope
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hϑ' : radUpperThreshold E₀ (25 + 2 * c) (48 + 4 * c) ≤ ϑ := hϑ
  obtain ⟨-, -, hϑ16, hϑE⟩ := radUpperThreshold_facts hE₀ hϑ'
  have hσm := hsigma_of_top_of_le hσ
  have hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + ϑ) := fun j => by
    linarith [scale_cond_28_of_le (m := j) hηE hϑE]
  have hs : 0 < s.re := re_pos_of_block_of_le hres (hsc 0) (hσm 0 (Nat.zero_le n))
  haveI : IsProbabilityMeasure
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff ϑ n) s μ) :=
    isProbabilityMeasure_tiltedMeasure_rademacher hX (blockCutoff ϑ n) hs
  obtain ⟨hM0, hM'0, hM'lin, hMenv⟩ := freeStartEnv_facts (a := a) hc0 hr1 hra hrn hhf
  -- the oscillatory sums, blockwise
  have hcos1 : ∀ m, m ≤ n → |∑ p ∈ primeBlockSub ϑ m,
      Real.cos (2 * s.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ Real.exp (-(2 * E₀)) / 100 := by
    intro m hm
    have hm1 : Real.exp (-(m : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    exact le_trans (hcos m hm) (le_trans (mul_le_of_le_one_right hKd0 hm1) hKd)
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hGw, hNm, hNG, hvlo, hvhi, hcmp⟩ :=
    exists_isGaussianWalk_rademacher_of_le_sharp hX
      (M := fun m => freeStartEnv c m + freeStartEnv c (m + 1) + blockWindow m) hE₀
      (by linarith) (by linarith) hϑ' hres hσ0 hη0 hηE hσ hM'0 hM'lin hcos1
  have hvlo' : ∀ i, 0.49 * Real.exp (-(2 * E₀)) ≤ (v i : ℝ) := by
    intro i
    have hE : Real.exp (-(2 * E₀)) ≤ Real.exp (-(2 * η)) := Real.exp_le_exp.2 (by linarith)
    linarith [hvlo i]
  have hC : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j,
      blockGaussMeanAddAt X μ ϑ (blockCutoff ϑ n) n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
        - (j : ℝ)| ≤ driftRadSharpOf E₀ 16 Kd := by
    intro j hj
    refine le_trans (abs_sum_blockGaussMeanAddAt_sub_le_sharp hX hϑ16 (by omega) hres hσ0 hη0
      (by linarith) hσ hKd0 fun m hm => hcos m (by omega)) ?_
    exact driftRadSharpOf_le hηE hϑ16
  have hW2 := memLp_walk_blockSumAdd_tiltedMeasure hX hs hres hsc hσm hrn.le
  have hmean := integral_walk_blockSumAdd_tiltedMeasure hX hs hres hsc hσm hrn.le
  have hvar := integral_sq_walk_blockSumAdd_sub_le hX (V₀ := 0.51) hs hres hsc hσm hrn.le
    fun m hm => by
      have h := (blockMatchedVarAdd_concrete_sharp hX hs hres hσ0 hηE hϑ16 hϑE
        (by omega : m ≤ n) (hσm m (by omega)) le_rfl (hcos1 m (by omega))).2
      linarith
  refine freeStart_barrier_le_averaged hGw ⟨by positivity, hvlo', hvhi⟩
    (L := fun m ω => ∑ p ∈ primeBlockSub ϑ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
    (θ := fun m => blockGaussMeanAddAt X μ ϑ (blockCutoff ϑ n) n s
      (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
    (w := blockWindow) (M := freeStartEnv c)
    (M' := fun m => freeStartEnv c m + freeStartEnv c (m + 1) + blockWindow m) (c := c)
    (C := driftRadSharpOf E₀ 16 Kd)
    (fun m => measurable_blockLocalLogAdd hX s (primeBlockSub ϑ m))
    (iIndepFun_blockSumAdd_tiltedMeasure hX (blockCutoff ϑ n) hs ϑ _) hNm hNG hC
    (fun m => blockWindow_pos m) (fun j _ => sum_inv_sq_range_le_two j) hM0 hMenv
    (fun m _ => le_rfl) (Real.exp_pos _).le (hcmp r hrn.le) hr1 hrn hβ hhfβ
    (driftRadSharpOf_nonneg hKd0) hK hT hsR hR1 ha (hW2.integrable one_le_two) ?_
    ((hW2.sub (memLp_const _)).integrable_sq) hvar
  rw [hmean]
  exact hC r hrn.le

/-- **`RMF.freeStart_barrier_le_averaged_rademacher` at a height, at the floor `ϑ`**: the
oscillatory sums are bounded by the prime number theorem with its term kept at the floor
(`RMF.abs_sum_cos_div_primeBlockSub_le_geometric_floor`), so that the height condition is
`(2|Im s| + 1)·pntFloorConst ϑ ≤ e^{-2E₀}/200`, which allows larger heights at larger floors. -/
theorem freeStart_barrier_le_averaged_rademacher_of_floor (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (hX : IsRademacherPrimeValues X μ) {ϑ σ η a β K T : ℝ} {n r : ℕ} {s : ℂ} {hf : ℕ → ℝ}
    (hϑ : radFreeStartThreshold E₀ ≤ ϑ) (hϑ104 : (104 : ℝ) ≤ ϑ) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀)
    (hσ : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * |s.im| * Real.exp ϑ)
    (hhiF : (2 * |s.im| + 1) * pntFloorConst ϑ ≤ Real.exp (-(2 * E₀)) / 200)
    (ha : 0 < a) (hr1 : 1 ≤ r) (hra : a ≤ 4 * r) (hrn : r < n)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j)
    (hβ : 0 ≤ β) (hhfβ : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ β * Real.log j)
    (hK : 0 < K) (hT : 2 * β < T) {sR : ℝ} (hsR : 0 ≤ sR)
    (hR1 : Result1Affine.{0} (0.49 * Real.exp (-(2 * E₀))) 1 β K T sR) :
    ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
        {ω | ∀ j, r ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
      ≤ (1 + Real.exp (-100)) * (K * ((a + 2
          + 3 * driftRadSharpOf E₀ 16 (Real.exp (-(2 * E₀)) / 100)
          + β * (Real.log r + Real.log 2) + 0.51 * r / (4 * a)
          + sR) / (1 - 2 * β / T)) / √((n - r : ℕ) : ℝ)) := by
  have ht : 0 < |s.im| := by
    rcases (abs_nonneg s.im).lt_or_eq with h | h
    · exact h
    · rw [← h] at hlo
      have := Real.exp_pos (2 * E₀)
      linarith
  have hKd := cosGeomConstF_le_of_height hlo hhiF
  have h := freeStart_barrier_le_averaged_rademacher E₀ hE₀ hX hϑ hres hσ0 hη0 hηE hσ
    (cosGeomConstF_nonneg ϑ s.im) hKd
    (fun m _ => abs_sum_cos_div_primeBlockSub_le_geometric_floor m hσ0 hϑ104 ht) ha hr1 hra
    hrn hhf
    hβ hhfβ hK hT hsR hR1
  refine le_trans h ?_
  have hden : 0 < 1 - 2 * β / T := by
    have hT0 : 0 < T := by linarith
    rw [sub_pos, div_lt_one hT0]
    exact hT
  have hdr : driftRadSharpOf E₀ 16 (cosGeomConstF ϑ s.im)
      ≤ driftRadSharpOf E₀ 16 (Real.exp (-(2 * E₀)) / 100) := by
    rw [driftRadSharpOf, driftRadSharpOf]
    linarith
  have h1 := div_le_div_of_nonneg_right (c := 1 - 2 * β / T) (show
      a + 2 + 3 * driftRadSharpOf E₀ 16 (cosGeomConstF ϑ s.im) + β * (Real.log r + Real.log 2)
          + 0.51 * r / (4 * a) + sR
        ≤ a + 2 + 3 * driftRadSharpOf E₀ 16 (Real.exp (-(2 * E₀)) / 100)
          + β * (Real.log r + Real.log 2) + 0.51 * r / (4 * a) + sR by linarith) hden.le
  have h2 := mul_le_mul_of_nonneg_left h1 hK.le
  have h3 := div_le_div_of_nonneg_right h2 (Real.sqrt_nonneg (((n - r : ℕ) : ℝ)))
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end RMF
