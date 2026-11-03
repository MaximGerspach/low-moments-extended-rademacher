/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Paper
import RMF.Reduction.UpperSieveNumeral

/-!
# The main results with explicit constants

The results of `RMF/Paper.lean` whose constants the formalisation makes explicit:

* the bounds uniform in `q` — two-sided, with `10⁻¹⁰` below and `30` (extended sum), respectively
  `25` (weighted sum), above, for every `x ≥ 3`;
* Corollary 1.3, with `30e`, respectively `25e`, for every `x ≥ 3` and `λ ≥ 3`;
* the upper bound in Harper's Theorem 1 (Steinhaus), with `20`, for every `x ≥ 1`.

Notation as in `RMF/Paper.lean`; `Λ = log log x`.
-/

namespace RMF.Paper

open MeasureTheory Filter

/-! ## The bounds uniform in `q` -/

/-- **(1.3), two-sided and explicit.**  For every `x ≥ 3`:
`10⁻¹⁰·T ≤ E|x^{-1/2} ∑_{n ≤ x} X^e(n)|^{2q} ≤ 30·T`, where `T = min{Λ, (1-2q)⁻¹}·Λ^{-q/2}` for
`0 < q < 1/2`, `T = Λ^{3/4}` for `q = 1/2`, and `T = (log x)^{q(2q-1)}·min{(2q-1)⁻¹, Λ}^{3/4}` for
`1/2 < q ≤ 1` (`RMF.extended_rademacher_moments_asymp_uniform_explicit_every_x`). -/
theorem bound_1_3_extended_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))
              ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 30 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                * Real.log (Real.log x) ^ (-(q / 2)))) ∧
        (1 / 10 ^ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ
          ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ
            ≤ 30 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
              ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
                * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) :=
  extended_rademacher_moments_asymp_uniform_explicit_every_x

/-- **The weighted analogue of (1.3), two-sided and explicit.**  The same as
`bound_1_3_extended_explicit` for `∑_{n ≤ x} X(n)/√n`, with the upper constant `25`
(`RMF.weighted_rademacher_moments_asymp_uniform_explicit_every_x`). -/
theorem bound_1_3_weighted_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          1 / 10 ^ 10 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))
              ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 25 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
                * Real.log (Real.log x) ^ (-(q / 2)))) ∧
        (1 / 10 ^ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
          ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
            ≤ 25 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
              ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
            ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                  ^ (2 * q) ∂μ
              ≤ 25 * (Real.log x ^ (q * (2 * q - 1))
                * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) :=
  weighted_rademacher_moments_asymp_uniform_explicit_every_x

/-! ## Corollary 1.3 -/

/-- **Corollary 1.3, extended sum, explicit.**  For every `x ≥ 3` and `λ ≥ 3`,
`P(|x^{-1/2} ∑_{n ≤ x} X^e(n)| > λ(log log x)^{-1/4}) ≤ 30e·min{log λ, log log x}/λ`
(`RMF.extended_rademacher_tail_explicit`). -/
theorem corollary_1_3_extended_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x → ∀ lam : ℝ, 3 ≤ lam →
        μ.real {ω | lam / Real.log (Real.log x) ^ (1 / 4 : ℝ)
            < ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖}
          ≤ 30 * Real.exp 1 * min (Real.log lam) (Real.log (Real.log x)) / lam :=
  extended_rademacher_tail_explicit

/-- **Corollary 1.3, weighted sum, explicit.**  For every `x ≥ 3` and `λ ≥ 3`,
`P(|∑_{n ≤ x} X(n)/√n| > λ(log log x)^{-1/4}) ≤ 25e·min{log λ, log log x}/λ`
(`RMF.weighted_rademacher_tail_explicit`). -/
theorem corollary_1_3_weighted_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x → ∀ lam : ℝ, 3 ≤ lam →
        μ.real {ω | lam / Real.log (Real.log x) ^ (1 / 4 : ℝ)
            < ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖}
          ≤ 25 * Real.exp 1 * min (Real.log lam) (Real.log (Real.log x)) / lam :=
  weighted_rademacher_tail_explicit

/-! ## Harper's upper bound -/

/-- **Harper, Theorem 1 (Steinhaus), upper bound, explicit.**  For every `x ≥ 1` and `0 ≤ q ≤ 1`,
`E|x^{-1/2} ∑_{n ≤ x} f(n)|^{2q} ≤ 20·(1 + (1-q)√(log log x))^{-q}` (`RMF.harper_upper_numeral`). -/
theorem harper_theorem_1_upper_explicit {Ω : Type*} [MeasurableSpace Ω] :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, 1 ≤ x → 0 ≤ q → q ≤ 1 →
        ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
          ≤ 20 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
  harper_upper_numeral

end RMF.Paper
