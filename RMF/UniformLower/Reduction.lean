/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfReduction

/-!
# The lower reduction above `q = ½`: steps L1–L3

Gerspach's Proposition 6 at `α = 1` (`RMF.exists_le_integral_rpow_weightedRademacherSum_euler_full`)
is stated for `0 < q ≤ ½`, and only one step sees that range: the symmetrisation
`RMF.integral_rough_le_of_le_oneOf` costs `2^{1-2q}` below `2q = 1`, where for `2q ≥ 1` convexity
gives `RMF.integral_rough_leOf` with constant `1`.  Khintchine
(`RMF.khintchine_lower_indep_of_pos`), the smoothing (`RMF.meanSquare_le_sum_weighted`) and
Parseval hold for `q ≤ 1`.  So for `½ ≤ q ≤ 1` and `⌊x⌋ < (y+1)²`, steps L1–L3 give
`3^{-(1-q)}·E[(∑_{y<p≤x} p^{-1}|S(x/p)|²)^q] ≤ E|S(x)|^{2q}`
(`RMF.khintchine_rough_weighted_of_half_le`).  The whole reduction for `0 < q ≤ 1`, with explicit
constants, is `RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`
(`RMF/UniformLower/ReductionExplicit.lean`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Steps L1–L3 for `2q ≥ 1` -/

/-- **Step L1 for the weighted sum, `2q ≥ 1`**: the `RMF.weightedExt` instance of
`RMF.integral_rough_leOf`, constant `1`. -/
theorem integral_rough_le_weighted_of_one_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ}
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq : 1 ≤ 2 * q) :
    (∫ ω, ‖randomSum (fun ω => weightedExt fun p => X p ω) x ω
        - smoothPartial (fun ω => weightedExt fun p => X p ω) y x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ‖randomSum (fun ω => weightedExt fun p => X p ω) x ω‖ ^ (2 * q) ∂μ :=
  integral_rough_leOf hX
    (fun p _ => map_mul_left_rademacherLaw (flipSign_eq_one_or_neg_one y p))
    (fun _ _ hn hn2 => weightedExt_flipSign hn hn2)
    (fun _ hY => isBoundedRMF_weightedExt hY)
    measurable_weightedExt_primeExtend (fun h => weightedExt_congr_primes h) hxy hq

/-- **Steps L1–L3 for the weighted sum, `½ ≤ q ≤ 1`.**  For `⌊x⌋ < (y+1)²`,
`3^{-(1-q)}·E[(∑_{y<p≤x} p^{-1}|S(x/p)|²)^q] ≤ E|S(x)|^{2q}`.  The proof of
`RMF.khintchine_rough_weighted`, with the symmetrisation of `RMF.integral_rough_leOf`. -/
theorem khintchine_rough_weighted_of_half_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq : 1 ≤ 2 * q) (hq1 : q ≤ 1) :
    (3 : ℝ) ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊, (p : ℝ)⁻¹
        * ‖weightedRademacherSum (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2)
          ^ q ∂μ
      ≤ ∫ ω, ‖weightedRademacherSum
          (fun ω => squarefreeExtension fun r => X r ω) x ω‖ ^ (2 * q) ∂μ := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun r => X r ω with hfdef
  set g : Ω → ArithmeticFunction ℂ := fun ω => weightedExt fun r => X r ω with hgdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hq0 : 0 < q := by linarith
  set s : Finset ℕ := largePrimeSet y ⌊x⌋₊ with hsdef
  have hs : ∀ p ∈ s, Nat.Prime p := fun p hp => (mem_largePrimeSet.1 hp).2
  -- the two data maps
  set W : Ω → (ℕ → ℂ) := fun ω =>
    primeRestrict (smallPrimes y) fun i : smallPrimes y => X ((i : Nat.Primes) : ℕ) ω with hWdef
  have hW : Measurable W :=
    (measurable_primeRestrict _).comp
      (measurable_pi_lambda _ fun i => hX.measurable ((i : Nat.Primes) : ℕ)
        (i : Nat.Primes).2)
  have hZ : (fun ω n => if n ∈ s then f ω n else 0)
      = fun ω => primeRestrict (largePrimes y ⌊x⌋₊)
          fun i : largePrimes y ⌊x⌋₊ => X ((i : Nat.Primes) : ℕ) ω := by
    funext ω
    rw [primeRestrict_largePrimes_eqOf (fun v _ hp => squarefreeExtension_apply_prime v hp)]
  have hind : IndepFun W (fun ω n => if n ∈ s then f ω n else 0) μ := by
    rw [hZ]
    exact indepFun_primeRestrict hX _ _ (disjoint_smallPrimes_largePrimes y ⌊x⌋₊)
  -- Khintchine, on the whole range `0 < q ≤ 1`
  have hkh := khintchine_lower_indep_of_pos hX.isRademacherRMF.isOrthonormalAtPrimes
    hs hW (C := weightedRoughCoeff x) (fun p => measurable_weightedRoughCoeff x p)
    (by norm_num : (0 : ℝ) < 3)
    (fun v => integral_norm_rpow_four_primeLinearForm_le_sqfree hX hs (weightedRoughCoeff x v))
    (B := (⌊x⌋₊ : ℝ))
    (fun v p hp => norm_weightedRoughCoeff_le hx0 (hs p hp).one_lt.le v) hind hq0 hq1
  -- identify the coefficients
  have hae := ae_roughCoeffOf_eq isCoeffExtension_weightedExt hX norm_eq_one_rademacherLaw hx hxy
  have hcoeff : ∀ᵐ ω ∂μ, ∀ p ∈ s,
      weightedRoughCoeff x (W ω) p
        = ((Real.sqrt p : ℂ))⁻¹ * weightedRademacherSum f (x / p) ω := by
    filter_upwards [hae] with ω hω
    intro p hp
    obtain ⟨⟨hy, _⟩, hprime⟩ := mem_largePrimeSet.1 hp
    rw [weightedRoughCoeff, hω p hprime hy, hfdef, weightedRademacherSum_eq_randomSum]
  have hL : (∫ ω, (∑ p ∈ s, ‖weightedRoughCoeff x (W ω) p‖ ^ 2) ^ q ∂μ)
      = ∫ ω, (∑ p ∈ s, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hcoeff] with ω hω
    refine congrArg (· ^ q) (Finset.sum_congr rfl fun p hp => ?_)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hs p hp).pos
    rw [hω p hp, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hp0.le]
  have hR : (∫ ω, ‖∑ p ∈ s, weightedRoughCoeff x (W ω) p * f ω p‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ‖weightedRademacherSum f x ω‖ ^ (2 * q) ∂μ := by
    have hS : (∫ ω, ‖weightedRademacherSum f x ω‖ ^ (2 * q) ∂μ)
        = ∫ ω, ‖randomSum g x ω‖ ^ (2 * q) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hfdef, hgdef, weightedRademacherSum_eq_randomSum]
    rw [hS]
    refine le_trans (le_of_eq (integral_congr_ae ?_))
      (integral_rough_le_weighted_of_one_le hX hxy hq)
    filter_upwards [hcoeff] with ω hω
    have hsum : (∑ p ∈ s, weightedRoughCoeff x (W ω) p * f ω p)
        = ∑ p ∈ s, g ω p * randomSum g (x / p) ω := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hω p hp, hgdef, weightedExt_apply, hfdef, weightedRademacherSum_eq_randomSum,
        squarefreeExtension_apply_prime _ (hs p hp)]
      ring
    have hset : s = {p ∈ Finset.Icc 1 ⌊x⌋₊ | p.Prime ∧ y < p} := by
      ext p
      rw [hsdef, mem_largePrimeSet, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hy, hN⟩, hp⟩
        exact ⟨⟨hp.one_lt.le, hN⟩, hp, hy⟩
      · rintro ⟨⟨_, hN⟩, hp, hy⟩
        exact ⟨⟨hy, hN⟩, hp⟩
    rw [hsum, hset, ← randomSum_sub_smoothPartial_eq (f := g) hx hxy
      (isMultiplicative_weightedExt _)]
  rw [hL] at hkh
  exact le_trans hkh hR

end RMF
