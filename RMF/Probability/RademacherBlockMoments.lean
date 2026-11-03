/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTiltedMoments
import RMF.Probability.MatchingGaussian

/-!
# The Rademacher block mean and variance

The two numbers Harper's comparison Gaussian is defined by, for the Rademacher model.

## Why these are new definitions and not the existing ones

`RMF.blockMean`, `RMF.blockMatchedVar`, `RMF.blockGaussMean` and `RMF.blockGaussVar` are defined
for any `(X, μ)`, with no law hypothesis, but their *bodies* are not law-free: `RMF.blockMean` is

`∑_{p ∈ B} ∫ localLog (w p) (X p ω) ∂(tiltedMeasure (compMultExtension X) y s μ)`,

which hard-codes both the Steinhaus local variable `localLog = -log‖1 - z w‖` and the
**completely multiplicative** extension.  The Rademacher model has `localLogAdd = log‖1 + z w‖`
and the **squarefree** extension, so the block quantities are genuinely different objects, not
the same object at a different law.  Hence `blockMeanAdd` and `blockMatchedVarAdd` here.

What *is* model-agnostic is everything above the seam: `RMF.IsWindowComparison` is a relation
between two arbitrary measures and two arbitrary families of real random variables, and
`RMF/Probability/HarperChain.lean` onwards consumes only that.  So the Rademacher case only has to
produce the analogue of `RMF.exists_isWindowComparison_steinhaus_of_top`.

## The two identifications

| | Steinhaus | Rademacher |
|---|---|---|
| block mean | `∑_p Re (w p · conj p^{-s})` | `∑_p [2 (Re p^{-s})(Re w p) - Re((w p)²)/2]` |
| block variance | `∑_p ‖w p‖² / 2` | `∑_p (Re w p)²` |

At `w p = p^{-(1/2+σ+i t_j)}` and `s = 1/2 + σ + i t` these are Harper's
`∑_p c(t, t_j - t, p) / p^{1+2σ}` and `∑_p (1 + cos(2 t_j log p)) / (2 p^{1+2σ})`
(Harper, arXiv:1703.06654, §3.3).  **The Rademacher variance depends on the height and
the Steinhaus one does not**, and that is the whole reason Harper needs the offset `D(t)`: the
oscillatory half of the variance is only small once the block is high enough, which is
`RMF.harperDt` in `RMF/Probability/HarperScales.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The definitions -/

/-- The tilted mean of the Rademacher block increment — the mean of the Gaussian it is compared
to.  The counterpart of `RMF.blockMean`, with `localLogAdd` for `localLog` and the squarefree
extension for the completely multiplicative one. -/
noncomputable def blockMeanAdd (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
    ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)

/-- The variance of that Gaussian: the sum of the per-prime matched variances `E~ξ² - (E~ξ)²`.
The counterpart of `RMF.blockMatchedVar`. -/
noncomputable def blockMatchedVarAdd (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ≥0 :=
  ∑ p ∈ B, matchingVar
    (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
    (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ^ 2
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))

/-- The block increment itself, as a random variable — the object
`RMF.IsWindowComparison` compares against a Gaussian. -/
noncomputable def blockLocalLogAdd (X : ℕ → Ω → ℂ) (s : ℂ) (B : Finset Nat.Primes) (ω : Ω) : ℝ :=
  ∑ p ∈ B, localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)

lemma measurable_blockLocalLogAdd (hX : IsRademacherPrimeValues X μ) (s : ℂ)
    (B : Finset Nat.Primes) : Measurable (blockLocalLogAdd X s B) :=
  Finset.measurable_sum _ fun p _ =>
    (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)

/-! ### The block mean -/

/-- **The block mean.**  `∑_{p ∈ B} [2 (Re p^{-s})(Re w p) - Re((w p) ^ 2)/2] + O(∑ ‖w p‖ ^ 3)`.

At Harper's values the main term is `∑_{p ∈ B} c(t, t_j - t, p) / p^{1+2σ}`.  The Steinhaus
counterpart is `RMF.abs_blockMean_sub_sum_re_le`, whose main term is `∑ Re (w p · conj p^{-s})`
— one term, not two, because the circle law is rotation invariant. -/
theorem abs_blockMeanAdd_sub_sum_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMeanAdd X μ y s w B
        - ∑ p ∈ B, (2 * (((p : ℕ) : ℂ) ^ (-s)).re * (w p).re - ((w p) ^ 2).re / 2)|
      ≤ ∑ p ∈ B, (36 * ‖w p‖ ^ 3 + 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 * ‖w p‖) := by
  rw [blockMeanAdd, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLogAdd_tiltedMeasure_sub_le hX y hs (hB hp) (hw p hp)

/-! ### Harper's `c(t, t_j - t, p)`

Harper (arXiv:1703.06654, §3.3) defines

`c(t, t_j - t, p) = 2 cos(t log p) cos(t_j log p) - (1/2) cos(2 t_j log p)`,

and computes `∑_{p ∈ B_j} c(t, t_j - t, p) / p^{1+2σ} = 1 + O(1/e^{n-j} + 1/j^{4/3})` —
the drift of `+1` per block, the same as the Steinhaus case.  The identity below says the
summand of `RMF.blockMeanAdd`'s main term **is** that `c`, and decomposes it the way Harper's
estimate treats it: one piece near `1` and two oscillatory sums. -/

/-- **The block-mean summand is Harper's `c`.**  At `s = 1/2+σ+it` and `u = 1/2+σ+i t_j`,
`2 (Re p^{-s})(Re p^{-u}) - Re((p^{-u})²)/2
  = p^{-1-2σ} [cos((t - t_j) log p) + cos((t + t_j) log p) - cos(2 t_j log p)/2]`
(`RMF.re_mul_re_prime_eq`, `RMF.norm_sq_div_two_sub_re_sq`, `RMF.localMean_prime_eq`).  The first
cosine is `1 + O((t-t_j)² log² p)`; the other two are oscillatory sums that
`RMF.exists_abs_sum_cos_primeBlockSub_le'` bounds. -/
lemma rademacherDrift_prime_eq {p : ℕ} (hp : p.Prime) {s u : ℂ} {σ : ℝ}
    (hres : s.re = 1 / 2 + σ) (hu : u.re = 1 / 2 + σ) :
    2 * ((p : ℂ) ^ (-s)).re * ((p : ℂ) ^ (-u)).re - (((p : ℂ) ^ (-u)) ^ 2).re / 2
      = (p : ℝ) ^ (-1 - 2 * σ)
        * (Real.cos ((s.im - u.im) * Real.log p) + Real.cos ((s.im + u.im) * Real.log p)
            - Real.cos (2 * u.im * Real.log p) / 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  -- the product, by product-to-sum
  have hprod := re_mul_re_prime_eq hp s u
  have hsum : -(s.re + u.re) = -1 - 2 * σ := by rw [hres, hu]; ring
  rw [hsum] at hprod
  -- the square, through the norm identity
  have hsq : ((((p : ℂ) ^ (-u)) ^ 2).re) / 2
      = ((p : ℂ) ^ (-u)).re ^ 2 - ‖((p : ℂ) ^ (-u))‖ ^ 2 / 2 := by
    have h := norm_sq_div_two_sub_re_sq (((p : ℂ) ^ (-u)))
    linarith
  have hmean := localMean_prime_eq hp u
  have hre2 : (-2 : ℝ) * u.re = -1 - 2 * σ := by rw [hu]; ring
  rw [hre2] at hmean
  have him : 2 * (u.im * Real.log p) = 2 * u.im * Real.log p := by ring
  rw [him] at hmean
  rw [hsq]
  linarith [hprod, hmean]

/-! ### The block variance

The matched variance is `E~ξ² - (E~ξ)²` per prime.  The first term is `(Re w p) ^ 2 + O(‖w‖ ^ 3)`
and the second is `O(‖a‖ ² ‖w‖ ² + ‖w‖ ^ 4)`, so the mean's square is an error and not a main
term — which is why the variance sees only the *second* moment. -/

/-- The mean at one prime is `O(‖a‖‖w‖ + ‖w‖ ^ 2)`, which is what makes its square an error. -/
theorem abs_integral_localLogAdd_tiltedMeasure_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))|
      ≤ 4 * ‖((p : ℕ) : ℂ) ^ (-s)‖ * ‖w‖ + 8 * ‖w‖ ^ 2 := by
  set a : ℂ := ((p : ℕ) : ℂ) ^ (-s) with hadef
  have ha1 : ‖a‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs
  have ha0 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hdrift := abs_integral_localLogAdd_tiltedMeasure_sub_le hX y hs hp hw
  -- the main term is at most `2‖a‖‖w‖ + ‖w‖ ^ 2 / 2`
  have hare : |a.re| ≤ ‖a‖ := Complex.abs_re_le_norm a
  have hwre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hsq : |(w ^ 2).re| ≤ ‖w‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_pow]
  have hmain : |2 * a.re * w.re - (w ^ 2).re / 2| ≤ 2 * ‖a‖ * ‖w‖ + ‖w‖ ^ 2 / 2 := by
    have h1 : |2 * a.re * w.re| ≤ 2 * ‖a‖ * ‖w‖ := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hare (by norm_num)) hwre (abs_nonneg _)
        (by positivity)
    have h2 : |(w ^ 2).re / 2| ≤ ‖w‖ ^ 2 / 2 := by
      rw [abs_div, abs_two]
      linarith
    exact (abs_sub _ _).trans (by linarith)
  -- and the error is at most `36‖w‖³ + 2‖a‖³‖w‖ ≤ 2‖w‖² + 2‖a‖‖w‖`
  have herr : 36 * ‖w‖ ^ 3 + 2 * ‖a‖ ^ 3 * ‖w‖ ≤ 36 / 5 * ‖w‖ ^ 2 + 2 * ‖a‖ * ‖w‖ := by
    have hcube : 36 * ‖w‖ ^ 3 ≤ 36 / 5 * ‖w‖ ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 5 - ‖w‖) (sq_nonneg ‖w‖)]
    have hacube : 2 * ‖a‖ ^ 3 * ‖w‖ ≤ 2 * ‖a‖ * ‖w‖ := by
      nlinarith [mul_nonneg (mul_nonneg ha0 hw0)
        (by nlinarith [sq_nonneg ‖a‖] : (0 : ℝ) ≤ 1 - ‖a‖ ^ 2)]
    linarith
  rw [abs_le] at hdrift hmain ⊢
  constructor <;>
    linarith [hdrift.1, hdrift.2, hmain.1, hmain.2, sq_nonneg ‖w‖, mul_nonneg ha0 hw0]

/-- `|E| ≤ 4A + 8B` gives `E ^ 2 ≤ 48 A ^ 2 + 96 B ^ 2`, by `64 A B ≤ 32 A ^ 2 + 32 B ^ 2`.
Extracted so the `nlinarith` runs against three hypotheses rather than the theorem's twenty. -/
private lemma sq_le_of_abs_le_add {E A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : |E| ≤ 4 * A + 8 * B) : E ^ 2 ≤ 48 * A ^ 2 + 96 * B ^ 2 := by
  have hsq := sq_abs E
  nlinarith [abs_nonneg E, sq_nonneg (A - B)]

/-- **The block variance.**  `∑_{p ∈ B} (Re w p) ^ 2 + O(∑ ‖w p‖ ^ 3 + ∑ ‖p^{-s}‖ ² ‖w p‖ ²)`.
The Steinhaus counterpart `RMF.abs_blockVar_sub_le` has main term `∑ ‖w p‖ ^ 2 / 2`, which does
not see the height.  This one does: at `w p = p^{-(1/2+σ+i t_j)}` it is
`∑ (1 + cos(2 t_j log p)) / (2 p^{1+2σ})`, so pinning it two-sidedly needs the cosine block bound
as well as `RMF.sum_prime_block_rpow_bounds` — which is where Harper's `D(t)` is consumed. -/
theorem abs_blockVarAdd_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(∑ p ∈ B, ((∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ^ 2
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
            - (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) ^ 2))
        - ∑ p ∈ B, (w p).re ^ 2|
      ≤ ∑ p ∈ B, (42 * ‖w p‖ ^ 3
          + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hw5 := hw p hp
  have hw0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg (w p)
  have ha0 : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ := norm_nonneg _
  have hsq := abs_integral_localLogAdd_sq_tiltedMeasure_sub_le hX y hs (hB hp) hw5
  have hm := abs_integral_localLogAdd_tiltedMeasure_le hX y hs (hB hp) hw5
  -- the mean's square is an error: `(4‖a‖‖w‖ + 8‖w‖²)² ≤ 48‖a‖²‖w‖² + 20‖w‖³`
  have hm' : |(∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ))|
      ≤ 4 * (‖((p : ℕ) : ℂ) ^ (-s)‖ * ‖w p‖) + 8 * ‖w p‖ ^ 2 := by linarith [hm]
  have hmsq := sq_le_of_abs_le_add (by positivity : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ * ‖w p‖)
    (by positivity : (0 : ℝ) ≤ ‖w p‖ ^ 2) hm'
  have hquart : 96 * (‖w p‖ ^ 2) ^ 2 ≤ 20 * ‖w p‖ ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 5 - ‖w p‖) (pow_nonneg hw0 3)]
  have hring : 48 * (‖((p : ℕ) : ℂ) ^ (-s)‖ * ‖w p‖) ^ 2
      = 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2 := by ring
  have hmsq0 : (0 : ℝ) ≤ (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ)) ^ 2 := sq_nonneg _
  rw [abs_le] at hsq ⊢
  constructor <;> linarith [hsq.1, hsq.2]

end RMF
