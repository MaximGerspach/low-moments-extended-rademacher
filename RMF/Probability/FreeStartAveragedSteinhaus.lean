/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.FreeStartAveraged
import RMF.Probability.HarperScalesExplicit

/-!
# The averaged free start for the Steinhaus random multiplicative function

`RMF.freeStart_barrier_le_averaged` needs the walk at the free start `r` to have mean within `C` of
`r` and variance at most `V`.  Under the tilt the walk is a sum of independent local logarithms:
* its mean is `∑_{m<r}` of the block means, which are within `C = driftSharpOf E₀ 16` of `r`
  (`RMF.integral_walk_blockSum_tiltedMeasure`, `RMF.abs_sum_blockGaussMean_sub_le_sharp`);
* its variance is the sum of the matched block variances, each at most `9/2`
  (`RMF.integral_sq_walk_blockSum_sub_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The mean of the walk under the tilt**: `E~ W_r = ∑_{m<r} blockGaussMean_m` for `r ≤ n`. -/
theorem integral_walk_blockSum_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) {θ σ η : ℝ}
    {n r : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η) (hrn : r ≤ n) :
    ∫ ω, walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ)
      = ∑ m ∈ Finset.range r, blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m := by
  have hint : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m,
      Integrable (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
        (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) :=
    fun m hm p hp => integrable_localLog_tiltedMeasure hX _ hs
      (primeBlockSub_subset_primesBelowSub θ hm hp)
      (norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hm) hp)
  simp_rw [walk_apply]
  rw [integral_finsetSum _ fun m hm =>
    integrable_finsetSum _ (hint m (by have := Finset.mem_range.1 hm; omega))]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by have := Finset.mem_range.1 hm; omega
  rw [integral_finsetSum _ (hint m hmn), blockGaussMean_of_le hmn, blockMean]

/-- **The variance of the walk under the tilt**: `E~(W_r - E~W_r)² ≤ (9/2)r` for `r ≤ n`.  The
primes are independent under the tilt, so the variance is the sum over the primes of the first `r`
blocks, blockwise the matched variances (`RMF.coe_blockMatchedVar`), each at most `9/2`
(`RMF.blockGaussVar_bounds_of_le`). -/
theorem integral_sq_walk_blockSum_sub_le (hX : IsSteinhausPrimeValues X μ) {θ σ η : ℝ}
    {n r : ℕ} {s : ℂ} (hθ : (8 : ℝ) ≤ θ) (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η) (hrn : r ≤ n) :
    ∫ ω, (walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω
        - ∫ ω', walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω'
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ))
          ^ 2
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ)
      ≤ 9 / 2 * r := by
  classical
  set P := tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ
    with hPdef
  haveI : IsProbabilityMeasure P := hX.isProbabilityMeasure_tiltedMeasure _ hs
  set S := (Finset.range r).biUnion (fun m => primeBlockSub θ m) with hSdef
  have hdisj : (↑(Finset.range r) : Set ℕ).PairwiseDisjoint (fun m => primeBlockSub θ m) :=
    fun a _ b _ hab => pairwise_disjoint_primeBlockSub θ hab
  have hmem : ∀ p ∈ S, ∃ m, m < r ∧ p ∈ primeBlockSub θ m := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.1 hp
    exact ⟨m, Finset.mem_range.1 hm, hpm⟩
  have hML : ∀ p ∈ S, MemLp (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) 2 P := by
    intro p hp
    obtain ⟨m, hmr, hpm⟩ := hmem p hp
    have hmn : m ≤ n := by omega
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)).aestronglyMeasurable
    · have h := integrable_localLog_mul_self_tiltedMeasure hX (blockCutoff θ n) hs
        (primeBlockSub_subset_primesBelowSub θ hmn hpm)
        (norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hmn) hpm)
      simpa [sq] using h
  have hfun : (fun ω => walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω)
      = fun ω => ∑ p ∈ S, localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω) := by
    funext ω
    rw [walk_apply, hSdef, Finset.sum_biUnion hdisj]
  have hWmeas : AEMeasurable (fun ω => walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r ω) P := by
    rw [hfun]
    exact (Finset.measurable_sum _ fun (p : Nat.Primes) _ =>
      (measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)).aemeasurable
  rw [← variance_eq_integral hWmeas, hfun]
  have hindep := hX.iIndepFun_localLog_tiltedMeasure (blockCutoff θ n) hs
    (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))
  have hvar : variance (fun ω => ∑ p ∈ S, localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) P
      = ∑ p ∈ S, variance (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) P := by
    have h := IndepFun.variance_sum hML (fun a _ b _ hab => hindep.indepFun hab)
    have hfe : (∑ p ∈ S, (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)))
        = (fun ω => ∑ p ∈ S, localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) := by
      funext ω
      simp
    rwa [hfe] at h
  rw [hvar, hSdef, Finset.sum_biUnion hdisj]
  have hblock : ∀ m ∈ Finset.range r,
      ∑ p ∈ primeBlockSub θ m, variance (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s))
          (X (p : ℕ) ω)) P ≤ 9 / 2 := by
    intro m hm
    have hmn : m ≤ n := by have := Finset.mem_range.1 hm; omega
    have hw : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := fun p hp =>
      norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hmn) hp
    have hcoe := coe_blockMatchedVar hX (blockCutoff θ n) hs
      (primeBlockSub_subset_primesBelowSub θ hmn) hw
    have hbound := (blockGaussVar_bounds_of_le hX hθ hs hres hσ0 hsc hσ
      (fun j _ p _ => norm_sq_prime_cpow_neg p hres) m).2
    rw [blockGaussVar, if_pos hmn] at hbound
    have heq : ∑ p ∈ primeBlockSub θ m, variance (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s))
          (X (p : ℕ) ω)) P
        = ((blockMatchedVar X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
      rw [hcoe]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [variance_eq_sub (hML p (Finset.mem_biUnion.2 ⟨m, hm, hp⟩))]
      simp only [Pi.pow_apply]
      rfl
    rw [heq]
    exact hbound
  calc ∑ m ∈ Finset.range r, ∑ p ∈ primeBlockSub θ m,
        variance (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) P
      ≤ ∑ _m ∈ Finset.range r, (9 / 2 : ℝ) := Finset.sum_le_sum hblock
    _ = 9 / 2 * r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The walk under the tilt is square integrable**: a finite sum of local logarithms, each in
`L²` (`RMF.integrable_localLog_mul_self_tiltedMeasure`). -/
theorem memLp_walk_blockSum_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) {θ σ η : ℝ}
    {n r : ℕ} {s : ℂ} (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η) (hrn : r ≤ n) :
    MemLp (walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r) 2
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) := by
  have hML : ∀ m ∈ Finset.range r, ∀ p ∈ primeBlockSub θ m,
      MemLp (fun ω => localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) 2
        (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) := by
    intro m hm p hp
    have hmn : m ≤ n := by have := Finset.mem_range.1 hm; omega
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)).aestronglyMeasurable
    · have h := integrable_localLog_mul_self_tiltedMeasure hX (blockCutoff θ n) hs
        (primeBlockSub_subset_primesBelowSub θ hmn hp)
        (norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσ m hmn) hp)
      simpa [sq] using h
  have hfun : walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) r
      = fun ω => ∑ m ∈ Finset.range r, ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω) := by
    funext ω
    simp only [walk_apply]
  rw [hfun]
  exact memLp_finsetSum _ fun m hm => memLp_finsetSum _ fun p hp => hML m hm p hp

/-- **The drift without the offsets' summand**: `45√K + 120e²e^{-(1+θ)} + 4e^{4K}·e²e^{-θ}`, the
bound of `RMF.abs_sum_blockMean_sub_le_of_le`.  `RMF.driftConstOf K θ` adds `4·blockDriftConst`,
which pays for Harper's offsets and is slack at a single tilt; at `K = 0`, `θ = 16` this is
`≈ 4·10⁻⁵` against `≈ 14.4`. -/
noncomputable def driftSharpOf (K θ : ℝ) : ℝ :=
  45 * Real.sqrt K + 120 * Real.exp 2 * Real.exp (-(1 + θ))
    + 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ))

lemma driftSharpOf_nonneg (K θ : ℝ) : 0 ≤ driftSharpOf K θ := by
  rw [driftSharpOf]
  positivity

/-- `driftSharpOf` increases in the tilt scale and decreases in the offset. -/
lemma driftSharpOf_le {K E θ₁ θ₂ : ℝ} (hK : K ≤ E) (hθ : θ₁ ≤ θ₂) :
    driftSharpOf K θ₂ ≤ driftSharpOf E θ₁ := by
  rw [driftSharpOf, driftSharpOf]
  have h1 : Real.sqrt K ≤ Real.sqrt E := Real.sqrt_le_sqrt hK
  have h2 : Real.exp (4 * K) ≤ Real.exp (4 * E) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-(1 + θ₂)) ≤ Real.exp (-(1 + θ₁)) := Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (-θ₂) ≤ Real.exp (-θ₁) := Real.exp_le_exp.2 (by linarith)
  have he2 : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
  have h5 : 120 * Real.exp 2 * Real.exp (-(1 + θ₂)) ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ₁)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : Real.exp 2 * Real.exp (-θ₂) ≤ Real.exp 2 * Real.exp (-θ₁) :=
    mul_le_mul_of_nonneg_left h4 he2
  have h7 : 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ₂))
      ≤ 4 * Real.exp (4 * E) * (Real.exp 2 * Real.exp (-θ₁)) :=
    mul_le_mul (by linarith) h6 (by positivity) (by positivity)
  linarith

/-- **The Gaussian drift at `RMF.driftSharpOf`**: `RMF.abs_sum_blockGaussMean_sub_le_of_le` without
the summand `4·blockDriftConst`. -/
theorem abs_sum_blockGaussMean_sub_le_sharp (hX : IsSteinhausPrimeValues X μ) {s : ℂ}
    {θ σ K : ℝ} {n j : ℕ} (hθ3 : (5 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hK0 : 0 ≤ K) (hsc : 14 + 2 * K ≤ Real.exp θ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ m ∈ Finset.range j,
        blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) - (j : ℝ)|
      ≤ driftSharpOf K θ := by
  rw [sum_blockGaussMean_eq X μ θ n s _ hj, driftSharpOf]
  exact abs_sum_blockMean_sub_le_of_le hX hθ3 hj hres hσ0 hK0 hsc hσ

set_option maxHeartbeats 1000000 in
-- the envelope, the comparison, the drift and the two moments of `W_r`, fed to one theorem
/-- **Proposition 5's upper half with the free start averaged, for the Steinhaus RMF.**  At the
threshold `RMF.prop5UpperThreshold E₀`, slope `c = prop5UpperSlope`, any free start `r ≥ a/4` and
any `hf ≤ β log` with `|hf| ≤ 10 log`,
`P~(W_j ∈ [-a - cj, a + j + hf(j)] ∀ r ≤ j ≤ n)
  ≤ (1 + e^{-100})K(a + 2 + 3C + β(log r + log 2) + (9/2)r/(4a) + s_R)/((1 - 2β/T)√(n - r))`,
`C = driftSharpOf E₀ 16`, for any constants `K`, `T`, `s_R ≥ 0` at which Probability Result 1 holds
in affine form for the variances `[0.475e^{-2E₀}, 9/2]` (`RMF.Result1Affine`).
`RMF.freeStart_barrier_le_averaged` with the comparison of
`RMF.exists_isGaussianWalk_steinhaus_of_le_sharp` at the envelope `M(j) = (9 + c)j + 10 log j`. -/
theorem freeStart_barrier_le_averaged_steinhaus (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (hX : IsSteinhausPrimeValues X μ) {ϑ σ η a β K T : ℝ} {n r : ℕ} {s : ℂ} {hf : ℕ → ℝ}
    (hϑ : prop5UpperThreshold E₀ ≤ ϑ) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η)
    (hηE : η ≤ E₀) (hσ : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η)
    (ha : 0 < a) (hr1 : 1 ≤ r) (hra : a ≤ 4 * r) (hrn : r < n)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j)
    (hβ : 0 ≤ β) (hhfβ : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ β * Real.log j)
    (hK : 0 < K) (hT : 2 * β < T) {sR : ℝ} (hsR : 0 ≤ sR)
    (hR1 : Result1Affine.{0} (0.475 * Real.exp (-(2 * E₀))) (9 / 2) β K T sR) :
    ((tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
        {ω | ∀ j, r ≤ j → j ≤ n →
          walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
      ≤ (1 + Real.exp (-100)) * (K * ((a + 2 + 3 * driftSharpOf E₀ 16
          + β * (Real.log r + Real.log 2) + 9 / 2 * r / (4 * a)
          + sR) / (1 - 2 * β / T)) / √((n - r : ℕ) : ℝ)) := by
  set c := prop5UpperSlope with hcdef
  have hc20 : (20 : ℝ) ≤ c := twenty_le_prop5UpperSlope
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hϑ' : max (max (blockQThrThreshold E₀ (25 + 2 * c) (48 + 4 * c))
      (blockNumThreshold E₀ ((3 * E₀ + 8) / 4))) (max 16 (Real.log (14 + 2 * E₀))) ≤ ϑ := hϑ
  have hϑ16 : (16 : ℝ) ≤ ϑ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hϑ'
  have hϑlog : Real.log (14 + 2 * E₀) ≤ ϑ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hϑ'
  have hϑE : (14 : ℝ) + 2 * E₀ ≤ Real.exp ϑ := by
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hϑlog
  have hσm := hsigma_of_top_of_le hσ
  have hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + ϑ) := fun j => scale_cond_of_le hηE hϑE
  have hs : 0 < s.re := re_pos_of_block_of_le hres (hsc 0) (hσm 0 (Nat.zero_le n))
  haveI : IsProbabilityMeasure
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ) :=
    hX.isProbabilityMeasure_tiltedMeasure (blockCutoff ϑ n) hs
  -- the envelope
  have hlogle : ∀ j : ℕ, Real.log (j : ℝ) ≤ (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      linarith [Real.log_le_sub_one_of_pos hj0]
  set M : ℕ → ℝ := fun j => (9 + c) * (j : ℝ) + 10 * Real.log (j : ℝ) with hMdef
  set M' : ℕ → ℝ := fun m => M m + M (m + 1) + blockWindow m with hM'def
  have hM0 : ∀ j, 0 ≤ M j := by
    intro j
    have h1 : (0 : ℝ) ≤ (9 + c) * (j : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    simp only [hMdef]
    linarith [Real.log_natCast_nonneg j]
  have hM'0 : ∀ m, 0 ≤ M' m := by
    intro m
    simp only [hM'def]
    linarith [hM0 m, hM0 (m + 1), (blockWindow_pos m).le]
  have hM'lin : ∀ m : ℕ, M' m ≤ 25 + 2 * c + (48 + 4 * c) * (m : ℝ) := by
    intro m
    have hW : blockWindow m ≤ 1 := by
      rw [blockWindow, div_le_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have h1 := hlogle m
    have h2 := hlogle (m + 1)
    have h3 : Real.log ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      rw [hcast]
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      linarith [Real.log_le_sub_one_of_pos hm1]
    have hcm : (0 : ℝ) ≤ c * (m : ℝ) := mul_nonneg hc0 (Nat.cast_nonneg m)
    simp only [hM'def, hMdef]
    rw [hcast]
    rw [hcast] at h3
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hMenv : ∀ i : ℕ, 1 ≤ i → i ≤ n - r →
      2 * a + (1 + c) * r + c * i + |hf r| ≤ M (r + i) ∧
        2 * a + (1 + c) * r + i + hf (r + i) ≤ M (r + i) := by
    intro i hi1 hin
    have hfr := hhf r hr1 (by omega)
    have hfri := le_trans (le_abs_self _) (hhf (r + i) (by omega) (by omega))
    have hcast : ((r + i : ℕ) : ℝ) = (r : ℝ) + (i : ℝ) := by push_cast; ring
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hlog : Real.log (r : ℝ) ≤ Real.log ((r + i : ℕ) : ℝ) := by
      rw [hcast]
      exact Real.log_le_log hrpos (by linarith [Nat.cast_nonneg (α := ℝ) i])
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hci : (0 : ℝ) ≤ c * (i : ℝ) := mul_nonneg hc0 hi0
    simp only [hMdef]
    rw [hcast] at hlog hfri ⊢
    constructor <;> nlinarith
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hGw, hNm, hNG, hvlo, hvhi, hcmp⟩ :=
    exists_isGaussianWalk_steinhaus_of_le_sharp E₀ (25 + 2 * c) (48 + 4 * c) hE₀ (by linarith)
      (by linarith) Ω X μ hX ϑ σ η n s M' hϑ hres hσ0 hη0 hηE hσ hM'0 hM'lin
  have hvlo' : ∀ i, 0.475 * Real.exp (-(2 * E₀)) ≤ (v i : ℝ) := by
    intro i
    have hE : Real.exp (-(2 * E₀)) ≤ Real.exp (-(2 * η)) := Real.exp_le_exp.2 (by linarith)
    linarith [hvlo i]
  have hC : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j,
      blockGaussMean X μ ϑ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) - (j : ℝ)|
        ≤ driftSharpOf E₀ 16 := by
    intro j hj
    refine le_trans (abs_sum_blockGaussMean_sub_le_sharp hX (by linarith : (5 : ℝ) ≤ ϑ)
      (by omega) hres hσ0 hη0 (by linarith) hσ) ?_
    exact driftSharpOf_le hηE hϑ16
  have hW2 := memLp_walk_blockSum_tiltedMeasure hX hs hres hsc hσm hrn.le
  have hmean := integral_walk_blockSum_tiltedMeasure hX hs hres hsc hσm hrn.le
  have hvar := integral_sq_walk_blockSum_sub_le hX (by linarith : (8 : ℝ) ≤ ϑ) hs hres hσ0 hsc
    hσm hrn.le
  refine freeStart_barrier_le_averaged hGw ⟨by positivity, hvlo', hvhi⟩
    (L := fun m ω => ∑ p ∈ primeBlockSub ϑ m, localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
    (θ := fun m => blockGaussMean X μ ϑ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
    (w := blockWindow) (M := M) (M' := M') (c := c) (C := driftSharpOf E₀ 16)
    (fun m => measurable_blockLocalLog hX ϑ (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
    (iIndepFun_blockSum_tiltedMeasure hX (blockCutoff ϑ n) hs ϑ _) hNm hNG hC
    (fun m => blockWindow_pos m) (fun j _ => sum_inv_sq_range_le_two j) hM0 hMenv
    (fun m _ => le_rfl) (Real.exp_pos _).le (hcmp r hrn.le) hr1 hrn hβ hhfβ
    (driftSharpOf_nonneg _ _) hK hT hsR hR1 ha (hW2.integrable one_le_two) ?_
    ((hW2.sub (memLp_const _)).integrable_sq) hvar
  rw [hmean]
  exact hC r hrn.le

/-- **`RMF.freeStart_barrier_le_averaged_steinhaus` at Harper's scales**: the block offset
`harperOffset D x` and count `harperBlockCount D x` at `D = freeStartHarperD E₀`, for which the
cutoff is `⌊x⌋ + 1` and the top scale is `x`, past `harperThreshold D 0 = e^{e^D}`. -/
theorem freeStart_barrier_harper_le_averaged_steinhaus (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (hX : IsSteinhausPrimeValues X μ) {x σ η a β K T : ℝ} {r : ℕ} {s : ℂ} {hf : ℕ → ℝ}
    (hx : harperThreshold (freeStartHarperD E₀) 0 ≤ x) (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ)
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσ : |σ| * Real.log x ≤ η)
    (ha : 0 < a) (hr1 : 1 ≤ r) (hra : a ≤ 4 * r)
    (hrn : r < harperBlockCount (freeStartHarperD E₀) x)
    (hhf : ∀ j, 1 ≤ j → j ≤ harperBlockCount (freeStartHarperD E₀) x →
      |hf j| ≤ 10 * Real.log j)
    (hβ : 0 ≤ β)
    (hhfβ : ∀ j, 1 ≤ j → j ≤ harperBlockCount (freeStartHarperD E₀) x → hf j ≤ β * Real.log j)
    (hK : 0 < K) (hT : 2 * β < T) {sR : ℝ} (hsR : 0 ≤ sR)
    (hR1 : Result1Affine.{0} (0.475 * Real.exp (-(2 * E₀))) (9 / 2) β K T sR) :
    ((tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1) s μ)
        {ω | ∀ j, r ≤ j → j ≤ harperBlockCount (freeStartHarperD E₀) x →
          walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (freeStartHarperD E₀) x) m,
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) j ω
            ∈ Set.Icc (-a - prop5UpperSlope * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
      ≤ (1 + Real.exp (-100)) * (K * ((a + 2 + 3 * driftSharpOf E₀ 16
          + β * (Real.log r + Real.log 2) + 9 / 2 * r / (4 * a)
          + sR) / (1 - 2 * β / T))
          / √((harperBlockCount (freeStartHarperD E₀) x - r : ℕ) : ℝ)) := by
  set ϑ₀ := prop5UpperThreshold E₀ with hϑ₀_expl
  obtain ⟨hx1, hDlog, -⟩ := exists_harperThreshold_of_blockCount_explicit _ 0 x hx
  have hD : freeStartHarperD E₀ = ⌈ϑ₀⌉₊ + 1 := rfl
  have hϑ : ϑ₀ ≤ harperOffset (freeStartHarperD E₀) x := by
    rw [hD]
    exact le_harperOffset_of_le x (le_ceil_add_sub_one ϑ₀ 1 le_rfl)
  have hσ' : |σ| * Real.log (blockScale (harperOffset (freeStartHarperD E₀) x)
      (harperBlockCount (freeStartHarperD E₀) x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset (freeStartHarperD E₀) x)
      (harperBlockCount (freeStartHarperD E₀) x) = ⌊x⌋₊ + 1 := blockCutoff_harperOffset hx1 hDlog
  have hmain := freeStart_barrier_le_averaged_steinhaus E₀ hE₀ hX hϑ hres hσ0 hη0 hηE hσ' ha hr1
    hra hrn hhf hβ hhfβ hK hT hsR hR1
  rwa [hcut] at hmain

end RMF
