/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.RademacherMoments
import RMF.Harper
import RMF.HarperRademacher
import RMF.Weighted.CaichUpper
import RMF.Weighted.PaperCorollaries
import RMF.UniformLower.MainExplicitAllX
import RMF.UniformLower.Extended.MainExplicit
import RMF.WeightedExtendedMoments

/-!
# Main results

The results of

> C. Atherfold, M. Gerspach and J. Hamdan, *Low moments of sums of extended Rademacher random
> multiplicative functions*,

in the order in which the paper states them, followed by the results of Harper and of Caich on
which the paper relies.  Each statement is the paper's, written in Lean, and is proved by the
library theorem named in its docstring.  The versions with explicit constants are in
`RMF/PaperExplicit.lean`, and `RMF/PaperAxioms.lean` prints the axioms of both: only `propext`,
`Classical.choice` and `Quot.sound`.

## Notation

* `X : ℕ → Ω → ℂ` with `IsRademacherPrimeValues X μ`: under the probability measure `μ`, the values
  `X p` at the primes are independent and uniform on `{±1}`.
* `compMultExtension fun p => X p ω` is the extended Rademacher function `X^e` (completely
  multiplicative), and `squarefreeExtension fun p => X p ω` is the Rademacher function `X = μ²X^e`.
* `normalisedSum f x ω = x^{-1/2} ∑_{n ≤ x} f(n)` and
  `weightedRademacherSum f x ω = ∑_{n ≤ x} f(n)/√n`.
* `momentOrder q x` is the case display of Theorems 1.1 and 1.2: `(log log x)^{-q/2}` if `q < 1/2`,
  `(log log x)^{3/4}` if `q = 1/2`, and `(log x)^{q(2q-1)}` if `q > 1/2`.
-/

namespace RMF.Paper

open MeasureTheory Filter

/-! ## Theorems 1.1 and 1.2 -/

/-- **Theorem 1.1.**  Let `0 ≤ q ≤ 1` be fixed.  Uniformly for `x ≥ 3`,
`E|x^{-1/2} ∑_{n ≤ x} X^e(n)|^{2q} ≍ momentOrder q x`, with constants independent of the
probability space (`RMF.extended_rademacher_moments`). -/
theorem theorem_1_1 (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ≤ C * momentOrder q x :=
  extended_rademacher_moments q hq0 hq1

/-- **Theorem 1.2.**  Let `0 ≤ q ≤ 1` be fixed.  Uniformly for `x ≥ 3`,
`E|∑_{n ≤ x} X(n)/√n|^{2q} ≍ momentOrder q x`, with constants independent of the probability space
(`RMF.weighted_rademacher_moments`). -/
theorem theorem_1_2 (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        c * momentOrder q x
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ
          ∧ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ) ≤ C * momentOrder q x :=
  weighted_rademacher_moments q hq0 hq1

/-! ## The bounds uniform in `q`

The paper proves the upper bound (1.3) uniformly in `q`, and its weighted analogue; the
formalisation also proves the matching lower bounds, as the paper's appendix describes.  With
`Λ = log log x`, the order of magnitude is `T(q, x) = min{Λ, (1-2q)⁻¹}·Λ^{-q/2}` for `0 < q < 1/2`,
`Λ^{3/4}` for `q = 1/2`, and `(log x)^{q(2q-1)}·min{(2q-1)⁻¹, Λ}^{3/4}` for `1/2 < q ≤ 1`; the three
cases are stated separately. -/

/-- **(1.3), with the matching lower bound**, for `x^{-1/2} ∑_{n ≤ x} X^e(n)`: there are
`c, C > 0` such that `c·T(q, x) ≤ E|·|^{2q} ≤ C·T(q, x)` for every `x ≥ 3` and `0 < q ≤ 1`.
Proved by `RMF.extended_rademacher_moments_asymp_uniform_explicit_every_x`, with `c = 10⁻¹⁰` and
`C = 30` (`RMF/PaperExplicit.lean`). -/
theorem bound_1_3_extended :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
          (∀ q : ℝ, 0 < q → q < 1 / 2 →
            c * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                * Real.log (Real.log x) ^ (-(q / 2)))
                ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
              ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
                ≤ C * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                  * Real.log (Real.log x) ^ (-(q / 2)))) ∧
          (c * Real.log (Real.log x) ^ (3 / 4 : ℝ)
              ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ
            ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ
              ≤ C * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ∧
          (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
            c * (Real.log x ^ (q * (2 * q - 1))
                * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
                ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
              ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
                ≤ C * (Real.log x ^ (q * (2 * q - 1))
                  * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) :=
  ⟨1 / 10 ^ 10, 30, by norm_num, by norm_num,
    extended_rademacher_moments_asymp_uniform_explicit_every_x⟩

/-- **The weighted analogue of (1.3), with the matching lower bound**, for `∑_{n ≤ x} X(n)/√n`:
there are `c, C > 0` such that `c·T(q, x) ≤ E|·|^{2q} ≤ C·T(q, x)` for every `x ≥ 3` and
`0 < q ≤ 1`.  Proved by `RMF.weighted_rademacher_moments_asymp_uniform_explicit_every_x`, with
`c = 10⁻¹⁰` and `C = 25` (`RMF/PaperExplicit.lean`). -/
theorem bound_1_3_weighted :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
          (∀ q : ℝ, 0 < q → q < 1 / 2 →
            c * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                * Real.log (Real.log x) ^ (-(q / 2)))
                ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
              ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
                ≤ C * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                  * Real.log (Real.log x) ^ (-(q / 2)))) ∧
          (c * Real.log (Real.log x) ^ (3 / 4 : ℝ)
              ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
            ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
              ≤ C * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ∧
          (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
            c * (Real.log x ^ (q * (2 * q - 1))
                * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
                ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
              ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                    ^ (2 * q) ∂μ
                ≤ C * (Real.log x ^ (q * (2 * q - 1))
                  * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) :=
  ⟨1 / 10 ^ 10, 25, by norm_num, by norm_num,
    weighted_rademacher_moments_asymp_uniform_explicit_every_x⟩

/-! ## Corollaries 1.3 and 1.4 -/

/-- **Corollary 1.3, extended sum.**  There is `C` such that for every `x ≥ 3` and `λ ≥ 3`,
`P(|x^{-1/2} ∑_{n ≤ x} X^e(n)| > λ(log log x)^{-1/4}) ≤ C·min{log λ, log log x}/λ`; the paper
states it for `x` sufficiently large.  Proved by `RMF.extended_rademacher_tail_explicit`, with
`C = 30e`. -/
theorem corollary_1_3_extended :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x → ∀ lam : ℝ, 3 ≤ lam →
          μ.real {ω | lam / Real.log (Real.log x) ^ (1 / 4 : ℝ)
              < ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖}
            ≤ C * min (Real.log lam) (Real.log (Real.log x)) / lam :=
  ⟨30 * Real.exp 1, by positivity, extended_rademacher_tail_explicit⟩

/-- **Corollary 1.3, weighted sum.**  There is `C` such that for every `x ≥ 3` and `λ ≥ 3`,
`P(|∑_{n ≤ x} X(n)/√n| > λ(log log x)^{-1/4}) ≤ C·min{log λ, log log x}/λ`; the paper states it
for `x` sufficiently large.  Proved by `RMF.weighted_rademacher_tail_explicit`, with `C = 25e`. -/
theorem corollary_1_3_weighted :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x → ∀ lam : ℝ, 3 ≤ lam →
          μ.real {ω | lam / Real.log (Real.log x) ^ (1 / 4 : ℝ)
              < ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖}
            ≤ C * min (Real.log lam) (Real.log (Real.log x)) / lam :=
  ⟨25 * Real.exp 1, by positivity, weighted_rademacher_tail_explicit⟩

/-- **Corollary 1.4, extended sum.**  `x^{-1/2} ∑_{n ≤ x, n ≠ □} X^e(n) → -1` in probability as
`x → ∞` (`RMF.extended_rademacher_nonsquare_tendstoInMeasure`). -/
theorem corollary_1_4_extended :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
        TendstoInMeasure μ
          (fun (x : ℝ) ω => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n,
            compMultExtension (fun p => X p ω) n) / (Real.sqrt x : ℂ))
          atTop (fun _ => -1) :=
  extended_rademacher_nonsquare_tendstoInMeasure

/-- **Corollary 1.4, weighted sum.**  `∑_{1 < n ≤ x} X(n)/√n → -1` in probability as `x → ∞`
(`RMF.weighted_rademacher_nonsquare_tendstoInMeasure`). -/
theorem corollary_1_4_weighted :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
        TendstoInMeasure μ
          (fun (x : ℝ) ω => ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
            squarefreeExtension (fun p => X p ω) n / (Real.sqrt n : ℂ))
          atTop (fun _ => -1) :=
  weighted_rademacher_nonsquare_tendstoInMeasure

/-! ## Proposition 1.5 -/

/-- **Proposition 1.5, moments.**  Let `0 ≤ q ≤ 1/2` be fixed.  Uniformly for `x ≥ 3`,
`E|∑_{n ≤ x} X^e(n)/√n|^{2q} ≪ (log x)^{q(2q+1)}`, with a constant independent of the probability
space (`RMF.weighted_extended_rademacher_moments`). -/
theorem proposition_1_5_moments (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
          (∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ) ≤ C * Real.log x ^ (q * (2 * q + 1)) :=
  weighted_extended_rademacher_moments q hq0 hq1

/-- **Proposition 1.5, limit.**  `(log x)⁻¹ ∑_{n ≤ x, n ≠ □} X^e(n)/√n → -1/2` in probability as
`x → ∞` (`RMF.weighted_extended_rademacher_nonsquare_tendstoInMeasure`). -/
theorem proposition_1_5_limit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
        TendstoInMeasure μ
          (fun (x : ℝ) ω => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n,
            compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)) / (Real.log x : ℂ))
          atTop (fun _ => -(1 / 2)) :=
  weighted_extended_rademacher_nonsquare_tendstoInMeasure

/-! ## Results the paper relies on -/

/-- **Harper, Theorem 1 (Steinhaus).**  Uniformly for `0 ≤ q ≤ 1` and `x ≥ 3`,
`E|x^{-1/2} ∑_{n ≤ x} f(n)|^{2q} ≍ (1 + (1-q)√(log log x))^{-q}`, with constants independent of
the probability space (`RMF.harper_low_moments`). -/
theorem harper_theorem_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω),
        IsSteinhausRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
              ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ ∧
            (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
              ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
  harper_low_moments

/-- **Harper, Theorem 2 (Rademacher).**  The same for the Rademacher random multiplicative function
(`RMF.harper_low_moments_rademacher`). -/
theorem harper_theorem_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω),
        IsRademacherRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
              ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ ∧
            (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
              ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
  harper_low_moments_rademacher

/-- **Caich, Theorem 1.1 (Rademacher case, upper bound).**  For `x ≥ x₀`, `2 ≤ y ≤ x` and
`0 ≤ q ≤ 1`, with `x/y = (log x)^θ`,
`E|∑_{x < n ≤ x+y} X(n)|^{2q} ≤ C·(y·min{1, θ√(log log x) + (1 + (1-q)√(log log x))⁻¹})^q`
(`RMF.integral_rpow_shortIntervalSum_le_caich`; here the probability space is fixed before the
constants). -/
theorem caich_theorem_1_1 {Ω : Type*} [MeasurableSpace Ω] :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x y q : ℝ, x₀ ≤ x → 2 ≤ y → y ≤ x → 0 ≤ q → q ≤ 1 →
          (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x y ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (y * min 1 (caichTheta x y * Real.sqrt (Real.log (Real.log x))
                + (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))⁻¹)) ^ q :=
  integral_rpow_shortIntervalSum_le_caich

end RMF.Paper
