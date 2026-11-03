/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTiltedPrimes

/-!
# The Rademacher local moments under the tilt

The Rademacher counterpart of `RMF/EulerProduct/TiltedMoments.lean`: the three moments of
`RMF/EulerProduct/RademacherTiltedLaw.lean` transported from the tilted local law to `P~`, one
prime at a time.

A block increment is `N = ∑_{p ∈ B} localLogAdd (w p) (f p)`, and each moment the Lindeberg swap
needs is the corresponding per-prime statement summed over `B`.  The observed radii `w p` are
left free: in Harper's application `w p = p ^ (-(1/2 + σ + i t_j))` while the tilt sits at
`s = 1/2 + σ + i t`, and keeping them apart is what preserves the oscillation.

## What is different from the Steinhaus file

**The drift has two terms.**  Where the Steinhaus block mean is `∑_p Re (w p · conj p^{-s})`, the
Rademacher one is

`∑_p [2 (Re p^{-s})(Re w p) - Re((w p) ^ 2) / 2]`,

which at Harper's values is `∑_p c(t, t_j - t, p) / p^{1+2σ}` for his
`c = 2 cos(t log p) cos(t_j log p) - (1/2) cos(2 t_j log p)`.  The second term has no Steinhaus
counterpart: the law is not rotation invariant, so the phase of `w p` survives on its own and not
only through `w p · conj p^{-s}`.

**Integrability is free.**  The tilted law has two atoms, so every bounded measurable function is
integrable, and `RMF.integrable_of_ae_bound_tilted_rademacherLaw` is the whole theory.

**The tilt radius is not small.**  `a = p^{-s}` is `2^{-1/2} = 0.707…` at the first prime, so
every statement here asks `‖a‖ < 1` and never `‖a‖ ≤ 1/5` — a hypothesis of the latter shape
would be unsatisfiable at `p = 2`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### Integrability under the tilted law -/

/-- **The whole integrability theory of the Rademacher side.**  The tilted law lives on the unit
circle and is a probability measure, so any measurable function bounded there is integrable.  The
Steinhaus file needs one such lemma per moment; here one suffices. -/
lemma integrable_of_ae_bound_tilted_rademacherLaw {a : ℂ} (ha : ‖a‖ < 1) {g : ℂ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ z : ℂ, ‖z‖ = 1 → |g z| ≤ C) :
    Integrable g (rademacherLaw.tilted fun z => 2 * localLogAdd a z) := by
  have hprob := isProbabilityMeasure_tilted_localLogAdd ha
  have hcirc : ∀ᵐ z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd a z), ‖z‖ = 1 :=
    (tilted_absolutelyContinuous rademacherLaw _) norm_eq_one_rademacherLaw
  refine (memLp_top_of_bound hg.aestronglyMeasurable C ?_).integrable le_top
  filter_upwards [hcirc] with z hz
  rw [Real.norm_eq_abs]
  exact hC z hz

lemma integrable_localLogAdd_tilted {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (localLogAdd w) (rademacherLaw.tilted fun z => 2 * localLogAdd a z) :=
  integrable_of_ae_bound_tilted_rademacherLaw ha (measurable_localLogAdd w)
    fun _ hz => abs_localLogAdd_le_of_norm_le hz hw

lemma integrable_localLogAdd_sq_tilted {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLogAdd w z ^ 2)
      (rademacherLaw.tilted fun z => 2 * localLogAdd a z) :=
  integrable_of_ae_bound_tilted_rademacherLaw ha ((measurable_localLogAdd w).pow_const 2)
    (C := (11 / 5 * ‖w‖) ^ 2) fun _ hz => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_localLogAdd_le_of_norm_le hz hw) 2

lemma measurable_abs_cube_localLogAdd (w : ℂ) :
    Measurable fun z : ℂ => |localLogAdd w z| ^ 3 := by
  simp only [← Real.norm_eq_abs]
  exact (measurable_localLogAdd w).norm.pow_const 3

lemma integrable_abs_cube_localLogAdd_tilted {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => |localLogAdd w z| ^ 3)
      (rademacherLaw.tilted fun z => 2 * localLogAdd a z) :=
  integrable_of_ae_bound_tilted_rademacherLaw ha
    (measurable_abs_cube_localLogAdd w) (C := (11 / 5 * ‖w‖) ^ 3) fun _ hz => by
      rw [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_localLogAdd_le_of_norm_le hz hw) 3

/-! ### Transport to `P~` -/

/-- **The transfer.**  A function of the value at one prime has the same `P~`-mean as it has under
the tilted local law, because `RMF.map_tiltedMeasure_rademacher` says the law *is* that one. -/
theorem integral_comp_tiltedMeasure_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X (p : ℕ) ω) ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)
      = ∫ z, g z ∂(rademacherLaw.tilted fun z => 2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s)) z) := by
  rw [← integral_map (hX.measurable (p : ℕ) p.2).aemeasurable hg.aestronglyMeasurable,
    map_tiltedMeasure_rademacher hX y hs hp]
  rfl

/-- **Transport of integrability**, the companion of the transfer. -/
theorem integrable_comp_tiltedMeasure_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {g : ℂ → ℝ}
    (hg : Integrable g
      (rademacherLaw.tilted fun z => 2 * localLogAdd (((p : ℕ) : ℂ) ^ (-s)) z)) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  refine Integrable.comp_aemeasurable ?_ (hX.measurable (p : ℕ) p.2).aemeasurable
  rw [map_tiltedMeasure_rademacher hX y hs hp]
  exact hg

theorem integrable_localLogAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd w (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure_rademacher hX y hs hp
    (integrable_localLogAdd_tilted (norm_prime_cpow_neg_lt_one p.2 hs) hw)

theorem integrable_localLogAdd_sq_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd w (X (p : ℕ) ω) ^ 2)
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure_rademacher hX y hs hp (g := fun z => localLogAdd w z ^ 2)
    (integrable_localLogAdd_sq_tilted (norm_prime_cpow_neg_lt_one p.2 hs) hw)

theorem integrable_abs_cube_localLogAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => |localLogAdd w (X (p : ℕ) ω)| ^ 3)
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  integrable_comp_tiltedMeasure_rademacher hX y hs hp (g := fun z => |localLogAdd w z| ^ 3)
    (integrable_abs_cube_localLogAdd_tilted (norm_prime_cpow_neg_lt_one p.2 hs) hw)

/-! ### The three moments at one prime -/

/-- **The drift at one prime.**  The main term is Harper's `c(t, t_j - t, p) / p^{1+2σ}` at
`w = p^{-(1/2+σ+i t_j)}` and `s = 1/2 + σ + i t`. -/
theorem abs_integral_localLogAdd_tiltedMeasure_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        - (2 * (((p : ℕ) : ℂ) ^ (-s)).re * w.re - (w ^ 2).re / 2)|
      ≤ 36 * ‖w‖ ^ 3 + 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 * ‖w‖ := by
  rw [integral_comp_tiltedMeasure_rademacher hX y hs hp (measurable_localLogAdd w)]
  exact abs_integral_localLogAdd_tilted_sub_le (norm_prime_cpow_neg_lt_one p.2 hs) hw

/-- **The second moment at one prime**, `(Re w) ^ 2 + O(‖w‖ ^ 3)`.  At Harper's values this is
`(1 + cos(2 t_j log p)) / (2 p^{1+2σ})`. -/
theorem abs_integral_localLogAdd_sq_tiltedMeasure_sub_le (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLogAdd w (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) - w.re ^ 2|
      ≤ 22 * ‖w‖ ^ 3 := by
  rw [integral_comp_tiltedMeasure_rademacher hX y hs hp
    ((measurable_localLogAdd w).pow_const 2)]
  exact abs_integral_localLogAdd_sq_tilted_sub_le (norm_prime_cpow_neg_lt_one p.2 hs) hw

/-- **The third absolute moment at one prime**, the term the Lindeberg swap charges. -/
theorem integral_abs_localLogAdd_cube_tiltedMeasure_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, |localLogAdd w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  rw [integral_comp_tiltedMeasure_rademacher hX y hs hp (measurable_abs_cube_localLogAdd w)]
  exact integral_abs_localLogAdd_cube_tilted_le (norm_prime_cpow_neg_lt_one p.2 hs) hw

end RMF
