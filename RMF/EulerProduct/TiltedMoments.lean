/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.TiltedPrimes

/-!
# The local moments under Harper's tilt

`RMF/EulerProduct/TiltedLaw.lean` computes the mean, the second moment and the third absolute
moment of `localLog w` against the tilted circle law `ν_a`; `RMF/EulerProduct/TiltedPrimes.lean`
identifies the law of `f(p)` under `P~` as exactly that `ν_a`, with `a = p ^ (-s)`.  This file
transports the moments across, so that they read as statements about `E~`.

## The tilt point and the observed point are different

Harper tilts **once**, at the real point `s = ½ + σ`, and then observes `log|1 - f(p) p^{-w}|^{-1}`
at `w = ½ + σ + i t_j`, with `t_j` varying from block to block.  So the tilt radius `a = p ^ (-s)`
and the observed radius `p ^ (-w)` are independent parameters throughout, and every statement
below keeps them apart.  Conflating them would silently delete the oscillation `cos (t log p)`
that carries the whole argument.

## Range

The second- and third-moment bounds need `‖p ^ (-w)‖ ≤ 1/5`, i.e. `p ^ (Re w) ≥ 5`.  This is
carried as an explicit hypothesis rather than assumed: Harper's blocks all sit far above any fixed
bound, but that is a fact about where the lemmas are applied, not about the lemmas.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Transport along the law.**  Under `P~`, an integral of a function of `f(p)` is an integral
against the tilted circle law `ν_{p ^ (-s)}`.  Every moment statement below is this plus the
corresponding computation in `RMF/EulerProduct/TiltedLaw.lean`. -/
theorem integral_comp_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X (p : ℕ) ω) ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)
      = ∫ z, g z ∂(steinhausLaw.tilted fun z => 2 * localLog (((p : ℕ) : ℂ) ^ (-s)) z) := by
  rw [← integral_map (hX.measurable (p : ℕ) p.2).aemeasurable hg.aestronglyMeasurable,
    hX.map_tiltedMeasure y hs hp]
  rfl

/-- **The drift, in the form Harper uses.**  With `a = p ^ (-s)` the tilt radius and `w` the
observed radius, `E~ localLog w (f p) = Re (w conj a) + O(‖w a‖²)`.  At `s = ½ + σ` and
`w = p ^ (-½-σ-it)` the main term is `cos (t log p) / p ^ (1+2σ)`, which summed over a block of
primes is the `+ 1` of drift per increment in Harper's Proposition 5. -/
theorem abs_integral_localLog_tiltedMeasure_sub_re_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ < 1) :
    |(∫ ω, localLog w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        - (w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re|
      ≤ ‖w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖ ^ 2
          * (1 - ‖w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖)⁻¹ / 2 := by
  rw [integral_comp_tiltedMeasure hX y hs hp (measurable_localLog w)]
  exact abs_integral_localLog_tilted_sub_re_le (norm_prime_cpow_neg_lt_one p.2 hs) hw

/-- **The tilted local second moment.**  `E~ (localLog w (f p))² = ‖w‖²/2 + O(‖w‖³)`, the tilt
contributing only at fourth order.  Note this is the *raw* second moment, which is what a
Lindeberg comparison matches — not the variance. -/
theorem abs_integral_localLog_sq_tiltedMeasure_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLog w (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) - ‖w‖ ^ 2 / 2|
      ≤ 20 * ‖w‖ ^ 3 + ‖w‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 / 2 := by
  rw [integral_comp_tiltedMeasure hX y hs hp ((measurable_localLog w).pow_const 2)]
  exact abs_integral_localLog_sq_tilted_sub_le (norm_prime_cpow_neg_lt_one p.2 hs) hw

/-- **The tilted local third absolute moment** — the Lindeberg error term. -/
theorem integral_abs_localLog_cube_tiltedMeasure_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, |localLog w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  have hg : Measurable fun z : ℂ => |localLog w z| ^ 3 := by
    simp only [← Real.norm_eq_abs]
    exact (measurable_localLog w).norm.pow_const 3
  rw [integral_comp_tiltedMeasure hX y hs hp hg]
  exact integral_abs_localLog_cube_tilted_le (norm_prime_cpow_neg_lt_one p.2 hs) hw

/-- **Transport of integrability**, the companion of `RMF.integral_comp_tiltedMeasure`. -/
theorem integrable_comp_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ}
    (hg : Integrable g (steinhausLaw.tilted fun z => 2 * localLog (((p : ℕ) : ℂ) ^ (-s)) z)) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) := by
  refine Integrable.comp_aemeasurable ?_ (hX.measurable (p : ℕ) p.2).aemeasurable
  rw [hX.map_tiltedMeasure y hs hp]
  exact hg

/-- A local term is integrable under the tilt. -/
theorem integrable_localLog_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLog w (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure hX y hs hp
    (integrable_localLog_tilted (norm_prime_cpow_neg_lt_one p.2 hs) hw)

/-- The square of a local term is integrable under `P~` — the second moment the swap matches. -/
theorem integrable_localLog_mul_self_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure hX y hs hp (g := fun z => localLog w z * localLog w z)
    (integrable_localLog_mul_self_tilted (norm_prime_cpow_neg_lt_one p.2 hs) hw)

/-- The third absolute moment of a local term is integrable under `P~` — the swap error. -/
theorem integrable_abs_cube_localLog_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => |localLog w (X (p : ℕ) ω)| ^ 3)
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure hX y hs hp (g := fun z => |localLog w z| ^ 3)
    (integrable_abs_pow_localLog_tilted (norm_prime_cpow_neg_lt_one p.2 hs) hw 3)

/-! ### Block sums

A block increment is `N = ∑_{p ∈ B} localLog (w p) (f p)`, and each of the three moments the
Lindeberg swap needs is the corresponding per-prime statement summed over `B`.  The observed radii
`w p` are left free: in Harper's application `w p = p ^ (-(1/2 + σ + i t))` while the tilt sits at
`s = 1/2 + σ`, and keeping them apart is what preserves the oscillation `cos (t log p)`.

**What the swap actually charges.**  The telescope `RMF.abs_integral_telescope_le` pays
`∑_{p ∈ B} E~E|localLog (w p) (f p)|³` — the *sum of the per-prime* third absolute moments, which
is `O(∑_{p ∈ B} p^{-3/2-3σ})` and hence tiny.  It does **not** pay the third absolute moment of the
block sum, which is a different and much larger quantity: `N - E~E N` is a sum of independent
centred terms of total variance `≈ 1/2`, so by Lyapunov `E~E|N - E~E N|³ ≥ (E~Var N)^{3/2} ≈ 0.35`,
against a right-hand side that is `≤ exp(-eʲ/2)`.  The block form is false and is not what is
wanted; the per-prime sum is both true and what the argument uses. -/

/-- **The block mean**: `E~ N = ∑_{p ∈ B} Re (w p · conj (p^{-s})) + O(∑ ‖w p · p^{-s}‖²)`.  At
`s = 1/2 + σ` and `w p = p^{-(1/2+σ+it)}` the main term is `∑_{p ∈ B} cos (t log p) / p^{1+2σ}`,
the `+1` of drift per increment in Harper's Proposition 5, and the error is `O(∑ p^{-2-4σ})`. -/
theorem abs_integral_sum_localLog_tiltedMeasure_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(∫ ω, ∑ p ∈ B, localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        - ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re|
      ≤ ∑ p ∈ B, ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖ ^ 2
          * (1 - ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖)⁻¹ / 2 := by
  rw [integral_finsetSum B fun p hp =>
      integrable_localLog_tiltedMeasure hX y hs (hB hp) (hw p hp),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLog_tiltedMeasure_sub_re_le hX y hs (hB hp)
    (lt_of_le_of_lt (hw p hp) (by norm_num))

/-- **The tilted local mean is small**: `|E~ localLog w (f p)| ≤ (49/48)‖w‖‖a‖` for
`‖w‖, ‖a‖ ≤ 1/5`, where `a = p^{-s}` is the tilt radius.  The point is the product `‖w‖‖a‖`,
`O(p^{-1-2σ})` at Harper's points rather than `O(p^{-1/2-σ})`: it makes the correction `(E~·)²`
negligible against the variance `‖w‖²/2` in the block sum, where `|E~·| ≤ 11‖w‖/5` alone would be of
the order of the main term. -/
theorem abs_integral_localLog_tiltedMeasure_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) :
    |∫ ω, localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)|
      ≤ 49 / 48 * (‖w‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖) := by
  set a : ℂ := ((p : ℕ) : ℂ) ^ (-s) with hadef
  have hwa : ‖w * (starRingEnd ℂ) a‖ = ‖w‖ * ‖a‖ := by
    rw [norm_mul, Complex.norm_conj]
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have ha0 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
  have hsmall : ‖w * (starRingEnd ℂ) a‖ ≤ 1 / 25 := by
    rw [hwa]; nlinarith
  have hkey := abs_integral_localLog_tiltedMeasure_sub_re_le hX y hs hp
    (lt_of_le_of_lt hw (by norm_num))
  have hre : |(w * (starRingEnd ℂ) a).re| ≤ ‖w‖ * ‖a‖ := by
    rw [← hwa]; exact Complex.abs_re_le_norm _
  have hden : (1 - ‖w * (starRingEnd ℂ) a‖)⁻¹ ≤ 25 / 24 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have herr : ‖w * (starRingEnd ℂ) a‖ ^ 2 * (1 - ‖w * (starRingEnd ℂ) a‖)⁻¹ / 2
      ≤ 25 / 48 * (‖w‖ * ‖a‖) ^ 2 := by
    rw [hwa] at hden ⊢
    nlinarith [sq_nonneg (‖w‖ * ‖a‖), mul_nonneg hw0 ha0]
  have habs := abs_sub_abs_le_abs_sub
    (∫ ω, localLog w (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
    ((w * (starRingEnd ℂ) a).re)
  nlinarith [hkey, hre, herr, mul_nonneg hw0 ha0]

/-- **The block second moment**: `∑_{p ∈ B} E~ (localLog (w p) (f p))² = ∑_{p ∈ B} ‖w p‖²/2 +
O(∑ ‖w p‖³) + O(∑ ‖w p‖²‖p^{-s}‖²)`.  These are the raw second moments, one per prime, which a
Lindeberg comparison matches, not the variance of the block sum.  At `w p = p^{-(1/2+σ+it)}` the
main term is `∑_{p ∈ B} 1/(2 p^{1+2σ})`, which with block Mertens is `1/2 + O(e^{-j})`. -/
theorem abs_sum_integral_localLog_sq_tiltedMeasure_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(∑ p ∈ B, ∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        - ∑ p ∈ B, ‖w p‖ ^ 2 / 2|
      ≤ ∑ p ∈ B, (20 * ‖w p‖ ^ 3 + ‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 / 2) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLog_sq_tiltedMeasure_sub_le hX y hs (hB hp) (hw p hp)

/-- **The block variance**, which the Gaussian comparison is matched to:
`V = ∑_{p∈B} (E~ξ_p² - (E~ξ_p)²)` differs from `∑_{p∈B} ‖w_p‖²/2` by at most
`∑ (20‖w_p‖³ + (5/2)‖w_p‖²‖p^{-s}‖²)`, for `‖w_p‖, ‖p^{-s}‖ ≤ 1/5`.  At `w_p = p^{-1/2-σ-it}` the
main term is Harper's variance `∑_{p∈B} 1/(2p^{1+2σ})`.  The `(E~ξ_p)²` correction is
`O(‖w_p‖²‖p^{-s}‖²)` by `RMF.abs_integral_localLog_tiltedMeasure_le`, negligible against it. -/
theorem abs_blockVar_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) (ha : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) :
    |(∑ p ∈ B, ((∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2
              ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
            - (∫ ω, localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2))
        - ∑ p ∈ B, ‖w p‖ ^ 2 / 2|
      ≤ ∑ p ∈ B, (20 * ‖w p‖ ^ 3
          + 5 / 2 * (‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2)) := by
  -- everything is obtained *before* the abbreviation, so that `set` folds it
  have h₂ := abs_sum_integral_localLog_sq_tiltedMeasure_sub_le hX y hs hB hw
  have hmean : ∀ p ∈ B, (∫ ω, localLog (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2
      ≤ 2 * (‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2) := by
    intro p hp
    have hb := abs_integral_localLog_tiltedMeasure_le hX y hs (hB hp) (hw p hp) (ha p hp)
    have h0 : (0 : ℝ) ≤ |∫ ω, localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)| := abs_nonneg _
    have hprod : (0 : ℝ) ≤ ‖w p‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖ := by positivity
    rw [← sq_abs]
    nlinarith
  have hmeanSum := Finset.sum_le_sum hmean
  have hmeanNonneg : (0 : ℝ) ≤ ∑ p ∈ B, (∫ ω, localLog (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  -- split the variance into second moment minus mean squared
  rw [show (∑ p ∈ B, ((∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
          - (∫ ω, localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2))
        - ∑ p ∈ B, ‖w p‖ ^ 2 / 2
      = ((∑ p ∈ B, ∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
          - ∑ p ∈ B, ‖w p‖ ^ 2 / 2)
        - ∑ p ∈ B, (∫ ω, localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2 by
    rw [Finset.sum_sub_distrib]; ring]
  refine le_trans (abs_sub _ _) ?_
  rw [show (∑ p ∈ B, (20 * ‖w p‖ ^ 3
        + 5 / 2 * (‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2)))
      = (∑ p ∈ B, (20 * ‖w p‖ ^ 3 + ‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 / 2))
        + ∑ p ∈ B, 2 * (‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2) by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring]
  refine add_le_add h₂ ?_
  rw [abs_of_nonneg hmeanNonneg]
  exact hmeanSum

end RMF
