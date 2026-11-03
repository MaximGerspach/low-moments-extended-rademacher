/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBlockComparisonMixed
import RMF.Probability.RademacherRestrictedSecondMoment.Drift

/-!
# The tilted window comparison, with the horizon at the compared blocks

`RMF.exists_isWindowComparison_primeBlockSubAdd_of_cutoff` asks the tilt to cover the block
*after* the last compared one.  Here the seam is restated with the Gaussian family's horizon at
the compared blocks: the family carries the blocks `m < n` and standard normals from `n` on, so
the tilt need not cover block `n`.  The last section defines the parameters of the block Gaussians
under the two-fold tilt `RMF.tiltedMeasure₂`.

## Main results

* `RMF.exists_isWindowComparison_primeBlockSubAdd_of_lt`
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The seam, with the horizon at the compared blocks -/

/-- The index set of block `m`: its primes for `m < n`, one fresh dummy from `n` on.
`RMF.blockIndex` with the horizon `n` itself excluded. -/
noncomputable def blockIndexLt (θ : ℝ) (n m : ℕ) : Finset (Nat.Primes ⊕ ℕ) :=
  if m < n then (primeBlockSub θ m).map ⟨Sum.inl, Sum.inl_injective⟩ else {Sum.inr m}

@[simp]
lemma mem_blockIndexLt_inl {θ : ℝ} {n m : ℕ} {p : Nat.Primes} :
    Sum.inl p ∈ blockIndexLt θ n m ↔ m < n ∧ p ∈ primeBlockSub θ m := by
  rw [blockIndexLt]
  by_cases hm : m < n <;> simp [hm]

@[simp]
lemma mem_blockIndexLt_inr {θ : ℝ} {n m k : ℕ} :
    Sum.inr k ∈ blockIndexLt θ n m ↔ ¬ m < n ∧ k = m := by
  rw [blockIndexLt]
  by_cases hm : m < n <;> simp [hm]

/-- The index sets are pairwise disjoint, as in `RMF.pairwise_disjoint_blockIndex`. -/
lemma pairwise_disjoint_blockIndexLt (θ : ℝ) (n : ℕ) :
    Pairwise fun k l => Disjoint (blockIndexLt θ n k) (blockIndexLt θ n l) := by
  intro k l hkl
  refine Finset.disjoint_left.2 ?_
  rintro (q | j) hik hil
  · rw [mem_blockIndexLt_inl] at hik hil
    exact Finset.disjoint_left.1 (pairwise_disjoint_primeBlockSub θ hkl) hik.2 hil.2
  · rw [mem_blockIndexLt_inr] at hik hil
    exact hkl (hik.2.symm.trans hil.2)

/-- The mean of the `m`-th block Gaussian: the tilted block mean for `m < n`, `0` from `n` on. -/
noncomputable def blockGaussMeanAddLt (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ :=
  if m < n then blockMeanAdd X μ y s w (primeBlockSub θ m) else 0

/-- The variance of the `m`-th block Gaussian: the matched block variance for `m < n`, `1` from
`n` on. -/
noncomputable def blockGaussVarAddLt (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ≥0 :=
  if m < n then blockMatchedVarAdd X μ y s w (primeBlockSub θ m) else 1

@[simp]
lemma blockGaussMeanAddLt_of_lt {θ : ℝ} {y n : ℕ} {s : ℂ} {w : Nat.Primes → ℂ} {m : ℕ}
    (hm : m < n) :
    blockGaussMeanAddLt X μ θ y n s w m = blockMeanAdd X μ y s w (primeBlockSub θ m) :=
  if_pos hm

@[simp]
lemma blockGaussVarAddLt_of_lt {θ : ℝ} {y n : ℕ} {s : ℂ} {w : Nat.Primes → ℂ} {m : ℕ}
    (hm : m < n) :
    blockGaussVarAddLt X μ θ y n s w m = blockMatchedVarAdd X μ y s w (primeBlockSub θ m) :=
  if_pos hm

lemma blockGaussVarAddLt_of_le {θ : ℝ} {y n : ℕ} {s : ℂ} {w : Nat.Primes → ℂ} {m : ℕ}
    (hm : n ≤ m) : blockGaussVarAddLt X μ θ y n s w m = 1 :=
  if_neg (not_lt.2 hm)

/-- Up to the horizon the Gaussians' summed mean is the summed block mean, as in
`RMF.sum_blockGaussMeanAddAt_eq`. -/
lemma sum_blockGaussMeanAddLt_eq (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) {j : ℕ} (hj : j ≤ n) :
    ∑ m ∈ Finset.range j, blockGaussMeanAddLt X μ θ y n s w m
      = ∑ m ∈ Finset.range j, blockMeanAdd X μ y s w (primeBlockSub θ m) :=
  Finset.sum_congr rfl fun m hm => by
    have : m < j := Finset.mem_range.1 hm
    exact blockGaussMeanAddLt_of_lt (by omega)

/-- **The Rademacher window comparison with only the compared blocks below the cutoff.**
`RMF.exists_isWindowComparison_primeBlockSubAdd_of_cutoff` with every hypothesis at `m < n`: the
Gaussian family carries the blocks `m < n` and standard normals from `n` on, so the tilt need not
cover block `n`. -/
theorem exists_isWindowComparison_primeBlockSubAdd_of_lt (hX : IsRademacherPrimeValues X μ)
    {s : ℂ} {θ : ℝ} {n y : ℕ} {w : Nat.Primes → ℂ} (hs : 0 < s.re)
    (hB : ∀ m, m < n → primeBlockSub θ m ⊆ primesBelowSub y)
    (hw : ∀ m, m < n → ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5)
    (ha : ∀ m, m < n → ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    {W M T q ε : ℕ → ℝ} {E : ℝ}
    (hT : ∀ m, m < n → 0 < T m) (hq : ∀ m, m < n → 0 < q m)
    (hv : ∀ m, m < n → blockMatchedVarAdd X μ y s w (primeBlockSub θ m) ≠ 0)
    (hTb : ∀ m, m < n →
      blockThirdConstAdd * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ T m)
    (hqlow : ∀ m, m < n → ∀ c, |c| ≤ M m → q m ≤ (gaussianReal
      (blockMeanAdd X μ y s w (primeBlockSub θ m))
      (blockMatchedVarAdd X μ y s w (primeBlockSub θ m))
      (Set.Ioc c (c + W m))).toReal)
    (hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        (blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ)))
      * T m ^ (1 / 4 : ℝ) ≤ ε m * q m)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m) = gaussianReal (blockGaussMeanAddLt X μ θ y n s w m)
        (blockGaussVarAddLt X μ θ y n s w m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLogAdd (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => W (m + k)) (fun m => M (m + k)) (n - k) (2 * E)) := by
  classical
  have hprob := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  have hξm : ∀ p : Nat.Primes, Measurable (fun ω => localLogAdd (w p) (X (p : ℕ) ω)) := fun p =>
    (measurable_localLogAdd (w p)).comp (hX.measurable (p : ℕ) p.2)
  have hξi := iIndepFun_localLogAdd_tiltedMeasure_rademacher hX y hs w
  -- the Gaussian family: the primes, plus a reservoir of standard normals from `n` on
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hGlaw, hGm₁, hGm₂⟩ :=
    exists_gaussian_matching_moments
      (Sum.elim (primeMeanAdd X μ y s w) (fun _ : ℕ => (0 : ℝ)))
      (Sum.elim (primeMoment₂Add X μ y s w) (fun _ : ℕ => (1 : ℝ)))
      (by
        rintro (q | j)
        · exact sq_primeMeanAdd_le X μ y s w q
        · norm_num)
  have hPm : ∀ q : Nat.Primes, Measurable (G (Sum.inl q)) := fun q => hGm _
  have hPi : iIndepFun (fun q : Nat.Primes => G (Sum.inl q)) Q := hGi.precomp Sum.inl_injective
  have hPlaw : ∀ q : Nat.Primes, Q.map (G (Sum.inl q))
      = gaussianReal (primeMeanAdd X μ y s w q)
        (matchingVar (primeMeanAdd X μ y s w q) (primeMoment₂Add X μ y s w q)) :=
    fun q => hGlaw (Sum.inl q)
  have hPm₁ : ∀ q : Nat.Primes, ∫ ω, G (Sum.inl q) ω ∂Q = primeMeanAdd X μ y s w q :=
    fun q => hGm₁ (Sum.inl q)
  have hPm₂ : ∀ q : Nat.Primes, ∫ ω, G (Sum.inl q) ω * G (Sum.inl q) ω ∂Q
      = primeMoment₂Add X μ y s w q := fun q => hGm₂ (Sum.inl q)
  have hvar : ∀ m, m < n →
      (∑ p ∈ primeBlockSub θ m, matchingVar (primeMeanAdd X μ y s w p)
          (primeMoment₂Add X μ y s w p))
        = blockMatchedVarAdd X μ y s w (primeBlockSub θ m) := fun m hm =>
    (blockMatchedVarAdd_eq_sum hX _ hs (hB m hm) (hw m hm)).symm
  have hNblock : ∀ m, m < n → (fun ω => ∑ i ∈ blockIndexLt θ n m, G i ω)
      = fun ω => ∑ p ∈ primeBlockSub θ m, G (Sum.inl p) ω := by
    intro m hm
    funext ω
    rw [blockIndexLt, if_pos hm, Finset.sum_map]
    rfl
  have hNm : ∀ m, Measurable (fun ω => ∑ i ∈ blockIndexLt θ n m, G i ω) := fun m =>
    Finset.measurable_sum _ fun i _ => hGm i
  have hNi : iIndepFun (fun m ω => ∑ i ∈ blockIndexLt θ n m, G i ω) Q :=
    iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_blockIndexLt θ n)
  have hNlaw : ∀ m, Q.map (fun ω => ∑ i ∈ blockIndexLt θ n m, G i ω)
      = gaussianReal (blockGaussMeanAddLt X μ θ y n s w m)
        (blockGaussVarAddLt X μ θ y n s w m) := by
    intro m
    rw [map_sum_gaussianReal hGm hGi hGlaw (blockIndexLt θ n m), blockGaussMeanAddLt,
      blockGaussVarAddLt]
    by_cases hm : m < n
    · rw [if_pos hm, if_pos hm, blockIndexLt, if_pos hm, Finset.sum_map, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Sum.elim_inl]
      rw [hvar m hm]
      rfl
    · rw [if_neg hm, if_neg hm, blockIndexLt, if_neg hm, Finset.sum_singleton,
        Finset.sum_singleton]
      norm_num [matchingVar]
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ i ∈ blockIndexLt θ n m, G i ω, hQ, hNm, hNi, hNlaw, ?_⟩
  have hblock : ∀ m, m < n → IsWindowComparison₁
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) Q
      (fun ω => ∑ p ∈ primeBlockSub θ m, localLogAdd (w p) (X (p : ℕ) ω))
      (fun ω => ∑ i ∈ blockIndexLt θ n m, G i ω) (W m) (M m) (ε m) := by
    intro m hm
    rw [hNblock m hm]
    have hBm := hB m hm
    have hGlaw' : ∀ p ∈ primeBlockSub θ m, Q.map (G (Sum.inl p)) = gaussianReal
        (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        (matchingVar
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))) := by
      intro p hp
      rw [hPlaw p, primeMoment₂Add_eq_of_le hX _ hs (hBm hp) (hw m hm p hp)]
      rfl
    have hTsum := sum_third_moment_blockAdd_le hX y hs hBm (hw m hm) (ha m hm) hPm hGlaw'
    refine isWindowComparison₁_of_gaussian_family_of_third_moment hξm hPm hξi hPi hPlaw
      (fun p hp => integrable_localLogAdd_tiltedMeasure hX _ hs (hBm hp) (hw m hm p hp))
      (fun p hp =>
        integrable_localLogAdd_mul_self_tiltedMeasure hX _ hs (hBm hp) (hw m hm p hp))
      (fun p _ => integrable_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (fun p _ => integrable_mul_self_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (fun p _ => (hPm₁ p).symm)
      (fun p hp => by
        rw [hPm₂ p, primeMoment₂Add_eq_of_le hX _ hs (hBm hp) (hw m hm p hp)])
      (fun p hp =>
        integrable_abs_cube_localLogAdd_tiltedMeasure hX _ hs (hBm hp) (hw m hm p hp))
      (fun p _ => integrable_abs_cube_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (hT m hm) (hq m hm) (by rw [hvar m hm]; exact hv m hm)
      (le_trans hTsum (hTb m hm))
      (by intro c hc; rw [hvar m hm]; exact hqlow m hm c hc)
      (by rw [hvar m hm]; exact hnum m hm)
  intro k hkn
  exact isWindowComparison_shift_of_indep
    (iIndepFun_blockSumAdd_tiltedMeasure hX y hs θ w) hNi hkn hε0 hsum hE hblock

/-! ### The two-fold tilt

The block Gaussians under the pair tilt `RMF.tiltedMeasure₂` by `|F_y(s₁)|²|F_y(s₂)|²`: the
two-fold block mean and matched variance for `m < n`, and `0` and `1` from `n` on. -/

end RMF
