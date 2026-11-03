/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBlockComparisonPair
import RMF.Probability.BlockComparisonSharp
import RMF.Probability.PairBoxCorrelated

/-!
# The pair of block walks under the one-point tilt

`RMF/Probability/RademacherBlockComparisonPair.lean` compares the pair of block walks at two heights
under the **two-fold** tilt `RMF.tiltedMeasure₂`.  The uniform lower bound's one-point step needs
the same pair under the **one-point** tilt `RMF.tiltedMeasure … y s₁ μ`, by `|F_y(s₁)|²` alone:
the height walk at `s₁ = ½+σ+ih` together with the real walk at `s₂ = ½+σ`.  This file supplies
the block data of that pair.

* `RMF.blockMatchedCovAddT` — the one-point-tilt block covariance, completing `RMF.blockMeanAdd`
  and `RMF.blockMatchedVarAdd` (which already take the tilt point and the weights separately);
  `RMF.cov_localLogAdd_tiltedMeasure_eq` is its closed form per prime, `(1 − 4κ_p²)D_vD_w`.
* `RMF.exists_gaussian_pair_block_rademacher_mixed` — the matched Gaussian family for a block.
* `RMF.sum_third_moment_pair_blockAdd_mixed_le` — the four third moments of a block, summed: at
  most `2·RMF.blockTAdd θ m`.
* `RMF.iIndepFun_blockSumPairAdd_tiltedMeasure` — the block sums are independent under the tilt.

Unlike the two-fold file, which asks `|cov| ≤ 1/100`, nothing here assumes the covariance small:
under the one-point tilt the block covariance reaches `0.8`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The block covariance under the one-point tilt -/

/-- **The one-point-tilt block covariance**, `∑_{p∈B} (E~[ξ_vξ_w] − E~ξ_v·E~ξ_w)` with
`ξ_v = localLogAdd (v p) (X p)`, under `RMF.tiltedMeasure` at the single point `s` (the tilt by
`|F_y(s)|²`).  The off-diagonal completing `RMF.blockMeanAdd` and `RMF.blockMatchedVarAdd`; not
the two-fold `RMF.blockMatchedCovAdd`. -/
noncomputable def blockMatchedCovAddT (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (v w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ((∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      - (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        * ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))

/-- **The one-point tilted covariance, in closed form.**  The tilted law has atoms `½ ± κ`,
`κ = Re a/(1 + ‖a‖²)`, so the covariance of two functions of the value is
`(¼ − κ²)(g 1 − g(−1))(h 1 − h(−1))`, here written `(1 − 4κ²)D_vD_w` with the half-increments
`D_w = (localLogAdd w 1 − localLogAdd w (−1))/2`, as in `RMF.cov_localLogAdd_tilted_pair_eq`. -/
theorem cov_localLogAdd_tilted_eq {a : ℂ} (ha : ‖a‖ < 1) (v w : ℂ) :
    (∫ z, localLogAdd v z * localLogAdd w z
        ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
      - (∫ z, localLogAdd v z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
        * (∫ z, localLogAdd w z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z))
      = (1 - 4 * (a.re / (1 + ‖a‖ ^ 2)) ^ 2)
          * ((localLogAdd v 1 - localLogAdd v (-1)) / 2)
          * ((localLogAdd w 1 - localLogAdd w (-1)) / 2) := by
  rw [integral_tilted_eq_add_rademacherLaw ha (fun z => localLogAdd v z * localLogAdd w z),
    integral_tilted_eq_add_rademacherLaw ha (localLogAdd v),
    integral_tilted_eq_add_rademacherLaw ha (localLogAdd w),
    integral_rademacherLaw_eq (fun z => localLogAdd v z * localLogAdd w z),
    integral_rademacherLaw_eq (localLogAdd v), integral_rademacherLaw_eq (localLogAdd w)]
  simp only [smul_eq_mul]
  ring

/-- **The one-point tilted covariance at one prime**: `(1 − 4κ_p²)D_vD_w` with
`κ_p = Re p^{-s}/(1 + ‖p^{-s}‖²)` the tilt multiplier, transported from the circle by
`RMF.integral_comp_tiltedMeasure_rademacher`.  No hypothesis on `v`, `w`. -/
theorem cov_localLogAdd_tiltedMeasure_eq (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) (v w : ℂ) :
    (∫ ω, localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      - (∫ ω, localLogAdd v (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        * (∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      = (1 - 4 * ((((p : ℕ) : ℂ) ^ (-s)).re / (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2)) ^ 2)
          * ((localLogAdd v 1 - localLogAdd v (-1)) / 2)
          * ((localLogAdd w 1 - localLogAdd w (-1)) / 2) := by
  rw [integral_comp_tiltedMeasure_rademacher hX y hs hp
      (g := fun z => localLogAdd v z * localLogAdd w z)
      ((measurable_localLogAdd v).mul (measurable_localLogAdd w)),
    integral_comp_tiltedMeasure_rademacher hX y hs hp (measurable_localLogAdd v),
    integral_comp_tiltedMeasure_rademacher hX y hs hp (measurable_localLogAdd w)]
  exact cov_localLogAdd_tilted_eq (norm_prime_cpow_neg_lt_one p.2 hs) v w

/-- **The block covariance in closed form**: the per-prime identity summed.  The right side does
not mention the cutoff `y`. -/
theorem blockMatchedCovAddT_eq (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (v w : Nat.Primes → ℂ) :
    blockMatchedCovAddT X μ y s v w B
      = ∑ p ∈ B, (1 - 4 * ((((p : ℕ) : ℂ) ^ (-s)).re
            / (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2)) ^ 2)
          * ((localLogAdd (v p) 1 - localLogAdd (v p) (-1)) / 2)
          * ((localLogAdd (w p) 1 - localLogAdd (w p) (-1)) / 2) :=
  Finset.sum_congr rfl fun p hp => cov_localLogAdd_tiltedMeasure_eq hX y hs (hB hp) (v p) (w p)

/-! ### Integrability and positive semidefiniteness under the one-point tilt

One lemma does all the integrability, as under the two-fold tilt: the tilted law lives on the
circle, where `RMF.localLogAdd` is bounded. -/

/-- **A bounded observable of one prime is integrable under the one-point tilt**, the twin of
`RMF.integrable_comp_tiltedMeasure₂_of_bounded_rademacher`. -/
lemma integrable_comp_tiltedMeasure_of_bounded_rademacher (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ}
    (hg : Measurable g) {C : ℝ} (hbd : ∀ z : ℂ, ‖z‖ = 1 → |g z| ≤ C) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure_rademacher hX y hs hp
    (integrable_of_ae_bound_tilted_rademacherLaw (norm_prime_cpow_neg_lt_one p.2 hs) hg hbd)

/-- The cross term is integrable under the one-point tilt. -/
lemma integrable_localLogAdd_mul_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {v w : ℂ}
    (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure_of_bounded_rademacher hX y hs hp
    (g := fun z => localLogAdd v z * localLogAdd w z)
    ((measurable_localLogAdd v).mul (measurable_localLogAdd w))
    (C := (11 / 5 * ‖v‖) * (11 / 5 * ‖w‖)) fun _ hz => by
      rw [abs_mul]
      exact mul_le_mul (abs_localLogAdd_le_of_norm_le hz hv)
        (abs_localLogAdd_le_of_norm_le hz hw) (abs_nonneg _) (by positivity)

/-- **The five `RMF.quadMonomial`s are integrable** under the one-point tilt. -/
lemma integrable_quadMonomial_localLogAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {v w : ℂ}
    (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) (j : Fin 5) :
    Integrable (fun ω => quadMonomial j
        (localLogAdd v (X (p : ℕ) ω), localLogAdd w (X (p : ℕ) ω)))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  fin_cases j <;> simp only [quadMonomial]
  · exact integrable_localLogAdd_tiltedMeasure hX y hs hp hv
  · exact integrable_localLogAdd_tiltedMeasure hX y hs hp hw
  · exact integrable_localLogAdd_mul_tiltedMeasure hX y hs hp hv hv
  · exact integrable_localLogAdd_mul_tiltedMeasure hX y hs hp hv hw
  · exact integrable_localLogAdd_mul_tiltedMeasure hX y hs hp hw hw

/-- **The Lindeberg bound is integrable** under the one-point tilt. -/
lemma integrable_windowLindebergBound_localLogAdd_tiltedMeasure
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5)
    (hw : ‖w‖ ≤ 1 / 5) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ω => windowLindebergBound δ
        (localLogAdd v (X (p : ℕ) ω), localLogAdd w (X (p : ℕ) ω)))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  refine integrable_comp_tiltedMeasure_of_bounded_rademacher hX y hs hp
    (g := fun z => windowLindebergBound δ (localLogAdd v z, localLogAdd w z))
    ((measurable_windowLindebergBound δ).comp
      ((measurable_localLogAdd v).prodMk (measurable_localLogAdd w)))
    (C := 900 / δ ^ 3 * (22 / 25) ^ 3) ?_
  intro z hz
  have hbv := abs_localLogAdd_le_of_norm_le hz hv
  have hbw := abs_localLogAdd_le_of_norm_le hz hw
  have hnn : (0 : ℝ) ≤ windowLindebergBound δ (localLogAdd v z, localLogAdd w z) := by
    rw [windowLindebergBound, lindebergBound]
    have h₃ : (0 : ℝ) < δ ^ 3 := by positivity
    positivity
  have hle := windowLindebergBound_le hδ (localLogAdd v z, localLogAdd w z)
  have hcube : (|localLogAdd v z| + |localLogAdd w z|) ^ 3 ≤ (22 / 25 : ℝ) ^ 3 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    nlinarith [hbv, hbw, hv, hw, norm_nonneg v, norm_nonneg w]
  have hcoef : (0 : ℝ) ≤ 900 / δ ^ 3 := by positivity
  rw [abs_of_nonneg hnn]
  calc windowLindebergBound δ (localLogAdd v z, localLogAdd w z)
      ≤ 900 / δ ^ 3 * (|localLogAdd v z| + |localLogAdd w z|) ^ 3 := hle
    _ ≤ 900 / δ ^ 3 * (22 / 25 : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hcube hcoef

/-- **The per-prime moment matrix is positive semidefinite** under the one-point tilt:
`RMF.psd_of_integrable_pair`, with the five moments pinned by hypotheses as in
`RMF.psd_of_tiltedMeasure₂_moments_rademacher`.  (By `RMF.cov_localLogAdd_tiltedMeasure_eq` the
matrix is even of rank one.) -/
theorem psd_of_tiltedMeasure_moments_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {v w : ℂ}
    (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) {m₁ m₂ q₁ q₁₂ q₂ : ℝ}
    (hm₁ : m₁ = ∫ ω, localLogAdd v (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
    (hm₂ : m₂ = ∫ ω, localLogAdd w (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
    (hq₁ : q₁ = ∫ ω, localLogAdd v (X (p : ℕ) ω) * localLogAdd v (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
    (hq₁₂ : q₁₂ = ∫ ω, localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
    (hq₂ : q₂ = ∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) :
    0 ≤ q₁ - m₁ ^ 2 ∧ 0 ≤ q₂ - m₂ ^ 2
      ∧ (q₁₂ - m₁ * m₂) ^ 2 ≤ (q₁ - m₁ ^ 2) * (q₂ - m₂ ^ 2) := by
  obtain ⟨T, hT⟩ : ∃ T : Measure Ω,
      T = tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ := ⟨_, rfl⟩
  have hprob : IsProbabilityMeasure T := by
    rw [hT]; exact isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  have h₁ : Integrable (fun ω => localLogAdd v (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_tiltedMeasure hX y hs hp hv
  have h₂ : Integrable (fun ω => localLogAdd w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_tiltedMeasure hX y hs hp hw
  have h₁₁ : Integrable
      (fun ω => localLogAdd v (X (p : ℕ) ω) * localLogAdd v (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_mul_tiltedMeasure hX y hs hp hv hv
  have h₁₂ : Integrable
      (fun ω => localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_mul_tiltedMeasure hX y hs hp hv hw
  have h₂₂ : Integrable
      (fun ω => localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_mul_tiltedMeasure hX y hs hp hw hw
  have h := psd_of_integrable_pair (P := T)
    (ξ := fun ω => (localLogAdd v (X (p : ℕ) ω), localLogAdd w (X (p : ℕ) ω)))
    h₁ h₂ h₁₁ h₁₂ h₂₂
  rw [hm₁, hm₂, hq₁, hq₁₂, hq₂, ← hT]
  exact h

/-! ### The matched Gaussian family for a block

`RMF.exists_gaussian_pair_block_rademacher` under the one-point tilt: the targets are zero off the
block, `RMF.psd_of_tiltedMeasure_moments_rademacher` makes them legitimate, and the block law comes
out in `RMF.blockMeanAdd`, `RMF.blockMatchedVarAdd` and `RMF.blockMatchedCovAddT`. -/

/-- **The matched Gaussian family for a block, under the one-point tilt**, with its per-prime pair
laws, its marginals and the block law. -/
theorem exists_gaussian_pair_block_rademacher_mixed (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {S : Finset Nat.Primes} (hS : S ⊆ primesBelowSub y)
    {v w : Nat.Primes → ℂ} (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 5) (hw : ∀ p ∈ S, ‖w p‖ ≤ 1 / 5) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G : Nat.Primes → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ p, Measurable (G p)) ∧ iIndepFun G Q ∧
        (∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
            (localLogAdd (v p) (X (p : ℕ) ω), localLogAdd (w p) (X (p : ℕ) ω))
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          = ∫ ω, quadMonomial j (G p ω) ∂Q) ∧
        (∀ p ∈ S, Q.map (G p) = gaussianPairLaw
          (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          ((∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
            - (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) ^ 2)
          ((∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
            - (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) ^ 2)
          ((∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
            - (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
                ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
              * ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
                ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))) ∧
        (∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
          (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          (matchingVar
            (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
            (∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)))) ∧
        (∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          (matchingVar
            (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
            (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)))) ∧
        ∀ B ⊆ S, Q.map (fun ω => ∑ p ∈ B, G p ω)
          = gaussianPairLaw (blockMeanAdd X μ y s v B) (blockMeanAdd X μ y s w B)
              ((blockMatchedVarAdd X μ y s v B : ℝ≥0) : ℝ)
              ((blockMatchedVarAdd X μ y s w B : ℝ≥0) : ℝ)
              (blockMatchedCovAddT X μ y s v w B) := by
  classical
  set T := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ with hTdef
  -- the target moments, zero off the block
  set μ₁ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) ∂T else 0 with hμ₁
  set μ₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ∂T else 0 with hμ₂
  set q₁ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω) ∂T
    else 0 with hq₁
  set q₁₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω) ∂T
    else 0 with hq₁₂
  set q₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω) ∂T
    else 0 with hq₂
  have hpsd : ∀ p, 0 ≤ q₁ p - μ₁ p ^ 2 ∧ 0 ≤ q₂ p - μ₂ p ^ 2
      ∧ (q₁₂ p - μ₁ p * μ₂ p) ^ 2 ≤ (q₁ p - μ₁ p ^ 2) * (q₂ p - μ₂ p ^ 2) := by
    intro p
    by_cases hp : p ∈ S
    · simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_pos hp]
      exact psd_of_tiltedMeasure_moments_rademacher hX y hs (hS hp) (hv p hp) (hw p hp)
        rfl rfl rfl rfl rfl
    · simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_neg hp]
      norm_num
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hGlaw, h0, h1, h2, h3, h4⟩ :=
    exists_gaussian_pair_matching_quadMonomial μ₁ μ₂ q₁ q₁₂ q₂
      (fun p => (hpsd p).1) (fun p => (hpsd p).2.1) (fun p => (hpsd p).2.2)
  refine ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, ?_, ?_, ?_, ?_, ?_⟩
  · -- the five moments agree on the block
    intro p hp j
    fin_cases j
    · have e := h0 p
      simp only [quadMonomial, hμ₁, if_pos hp] at e ⊢
      exact e.symm
    · have e := h1 p
      simp only [quadMonomial, hμ₂, if_pos hp] at e ⊢
      exact e.symm
    · have e := h2 p
      simp only [quadMonomial, hq₁, if_pos hp] at e ⊢
      exact e.symm
    · have e := h3 p
      simp only [quadMonomial, hq₁₂, if_pos hp] at e ⊢
      exact e.symm
    · have e := h4 p
      simp only [quadMonomial, hq₂, if_pos hp] at e ⊢
      exact e.symm
  · intro p hp
    rw [hGlaw p]
    simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_pos hp, hTdef]
  · intro p hp
    have hmap : Q.map (fun ω => (G p ω).1) = (Q.map (G p)).map Prod.fst := by
      rw [Measure.map_map measurable_fst (hGm p)]
      rfl
    rw [hmap, hGlaw p, map_fst_gaussianPairLaw (hpsd p).1 (hpsd p).2.1 (hpsd p).2.2]
    simp only [hμ₁, hq₁, if_pos hp, matchingVar, hTdef]
  · intro p hp
    have hmap : Q.map (fun ω => (G p ω).2) = (Q.map (G p)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hGm p)]
      rfl
    rw [hmap, hGlaw p, map_snd_gaussianPairLaw (hpsd p).1 (hpsd p).2.1 (hpsd p).2.2]
    simp only [hμ₂, hq₂, if_pos hp, matchingVar, hTdef]
  · -- the block law: the three sums are the three block statistics
    intro B hBS
    rw [map_sum_eq_gaussianPairLaw hGm hGi hGlaw (fun p => (hpsd p).1) (fun p => (hpsd p).2.1)
      (fun p => (hpsd p).2.2) B]
    have hmean₁ : ∑ p ∈ B, μ₁ p = blockMeanAdd X μ y s v B := by
      rw [blockMeanAdd]
      exact Finset.sum_congr rfl fun p hp => by simp only [hμ₁, if_pos (hBS hp), hTdef]
    have hmean₂ : ∑ p ∈ B, μ₂ p = blockMeanAdd X μ y s w B := by
      rw [blockMeanAdd]
      exact Finset.sum_congr rfl fun p hp => by simp only [hμ₂, if_pos (hBS hp), hTdef]
    have hvar₁ : ∑ p ∈ B, (q₁ p - μ₁ p ^ 2)
        = ((blockMatchedVarAdd X μ y s v B : ℝ≥0) : ℝ) := by
      rw [coe_blockMatchedVarAdd hX y hs (hBS.trans hS) (fun p hp => hv p (hBS hp))]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpow : (∫ ω, localLogAdd (v p) (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ))
          = ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          pow_two (localLogAdd (v p) (X (p : ℕ) ω)))
      simp only [hμ₁, hq₁, if_pos (hBS hp), hTdef]
      rw [hpow]
    have hvar₂ : ∑ p ∈ B, (q₂ p - μ₂ p ^ 2)
        = ((blockMatchedVarAdd X μ y s w B : ℝ≥0) : ℝ) := by
      rw [coe_blockMatchedVarAdd hX y hs (hBS.trans hS) (fun p hp => hw p (hBS hp))]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpow : (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ))
          = ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          pow_two (localLogAdd (w p) (X (p : ℕ) ω)))
      simp only [hμ₂, hq₂, if_pos (hBS hp), hTdef]
      rw [hpow]
    have hcov : ∑ p ∈ B, (q₁₂ p - μ₁ p * μ₂ p) = blockMatchedCovAddT X μ y s v w B := by
      rw [blockMatchedCovAddT]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₁, hμ₂, hq₁₂, if_pos (hBS hp), hTdef]
    rw [hmean₁, hmean₂, hvar₁, hvar₂, hcov]

/-! ### The third-moment layer

Both coordinates are observed under the one tilt at `s₁`, so each is
`RMF.third_moment_add_matching_leAdd` verbatim — there the tilt radius `‖p^{-s₁}‖` and the weight
are separate hypotheses — and on the block the two weights have equal modulus.  So the block sum of
the four third moments is at most `2·RMF.blockTAdd θ m`. -/

/-- **`hTb` for the mixed pair**: the four third moments of a block, under the one-point tilt at
`s₁`, sum to at most `2·RMF.blockTAdd θ m`. -/
theorem sum_third_moment_pair_blockAdd_mixed_le {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} {G : Nat.Primes → Ω' → ℝ × ℝ} (hX : IsRademacherPrimeValues X μ)
    {θ σ : ℝ} {m y : ℕ} {s₁ s₂ : ℂ} (hy : primeBlockSub θ m ⊆ primesBelowSub y)
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hGm : ∀ p, Measurable (G p))
    (hlaw₁ : ∀ p ∈ primeBlockSub θ m, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
      (matchingVar
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
            * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))))
    (hlaw₂ : ∀ p ∈ primeBlockSub θ m, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
      (matchingVar
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
            * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ)))) :
    ∑ p ∈ primeBlockSub θ m,
        ((∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)| ^ 3
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
          + (∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)| ^ 3
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
          + (∫ ω, |(G p ω).1| ^ 3 ∂Q) + ∫ ω, |(G p ω).2| ^ 3 ∂Q)
      ≤ 2 * blockTAdd θ m := by
  have hs₁ : 0 < s₁.re := re_pos_of_block hmθ hre₁ hσ
  have hκ := blockWeightSize_le hmθ
  -- on the block the two weights have equal modulus, at most `κ ≤ 1/1000`
  have hsmall : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖
        ∧ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 1000 := by
    intro p hp
    have h₁ := norm_sq_prime_cpow_neg p hre₁
    have h₂ := norm_sq_prime_cpow_neg p hre₂
    have heq : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := by
      have h : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 := by rw [h₁, h₂]
      calc ‖((p : ℕ) : ℂ) ^ (-s₁)‖
          = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2) := by rw [h]
        _ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := Real.sqrt_sq (norm_nonneg _)
    have hb : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub hσ hp h₁
    exact ⟨heq, by linarith⟩
  -- per prime, the four moments come to `2·blockThirdConstAdd·‖p^{-s₁}‖³`
  have hper : ∀ p ∈ primeBlockSub θ m,
      ((∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        + (∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ))
        + (∫ ω, |(G p ω).1| ^ 3 ∂Q) + ∫ ω, |(G p ω).2| ^ 3 ∂Q)
      ≤ 2 * blockThirdConstAdd * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    have hv5 : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by linarith
    have hw5 : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by rw [← heq]; linarith
    have h₁ := third_moment_add_matching_leAdd hX y hs₁ (hy hp) hv5 hv5 ((hGm p).fst)
      (hlaw₁ p hp)
    have h₂ := third_moment_add_matching_leAdd hX y hs₁ (hy hp) hw5 hv5 ((hGm p).snd)
      (hlaw₂ p hp)
    rw [← heq] at h₂
    linarith
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum]
  have h : blockThirdConstAdd * ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3
      ≤ blockTAdd θ m :=
    blockThirdConstAdd_mul_sum_le hmθ hσ fun p _ => norm_sq_prime_cpow_neg p hre₁
  linarith

/-! ### The block sums under the one-point tilt -/

/-- **The mixed block sums are independent under the one-point tilt.**  Stated as a lemma, like
its two-fold twin `RMF.iIndepFun_blockSumPairAdd_tiltedMeasure₂`, so that the shift lemma receives
it with its type already in the block-sum form. -/
theorem iIndepFun_blockSumPairAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ : ℂ} (hs₁ : 0 < s₁.re) (s₂ : ℂ) (θ : ℝ) :
    iIndepFun (fun m ω => ∑ p ∈ primeBlockSub θ m,
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s₁ μ) :=
  iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun (p : Nat.Primes) =>
      ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).prodMk
        ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)))
    ((iIndepFun_tiltedMeasure_rademacher hX y hs₁).comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun (_ : Nat.Primes) => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    (pairwise_disjoint_primeBlockSub θ)

end RMF
