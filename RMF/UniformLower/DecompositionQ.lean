/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SmallPrimesQ

/-!
# The decomposition at exponent `q`: the twists

The low factors of the `q = ½` decomposition (`RMF/Weighted/HalfDecomposition.lean`) at a general
exponent `q`, as functions of the values at the small primes: the numerator's
`RMF.twistPolyQ` = `‖F_S(σ+ih)‖²‖F_S(σ)‖^{2q-2}` and the denominator's
`RMF.twistPairPolyQ` = `‖F_S(σ+ih₁)‖²‖F_S(σ+ih₂)‖²‖F_S(σ)‖^{2q-4}`, their measurability, and
their values on the primes of `[a, b)` as random Euler products.
-/

open MeasureTheory

namespace RMF

/-! ### The twists at exponent `q`, as functions of the small primes -/

section Twists

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- `‖F_S(σ+ih)‖²‖F_S(σ)‖^{2q-2}`, the numerator's low factor at exponent `q`. -/
noncomputable def twistPolyQ (q : ℝ) (S : Finset ℕ) (σ h : ℝ) (v : ↥S → ℂ) : ℝ :=
  ‖primePoly S (shiftLine σ h) v‖ ^ 2 * ‖primePoly S (shiftLine σ 0) v‖ ^ (2 * q - 2)

lemma measurable_twistPolyQ (q : ℝ) (S : Finset ℕ) (σ h : ℝ) :
    Measurable (twistPolyQ q S σ h) := by
  unfold twistPolyQ
  exact (((continuous_primePoly S (shiftLine σ h)).norm.pow 2).measurable).mul
    (((continuous_primePoly S (shiftLine σ 0)).norm.measurable).pow_const _)

omit [MeasurableSpace Ω] in
lemma twistPolyQ_primesIco (q : ℝ) (a b : ℕ) (σ h : ℝ) (ω : Ω) :
    twistPolyQ q (primesIco a b) σ h (fun p => X (p : ℕ) ω)
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ^ (2 * q - 2) := by
  rw [twistPolyQ, primePoly_primesIco, primePoly_primesIco]

/-- `‖F_S(σ+ih₁)‖²‖F_S(σ+ih₂)‖²‖F_S(σ)‖^{2q-4}`, the denominator's low factor at exponent
`q`. -/
noncomputable def twistPairPolyQ (q : ℝ) (S : Finset ℕ) (σ h₁ h₂ : ℝ) (v : ↥S → ℂ) : ℝ :=
  ‖primePoly S (shiftLine σ h₁) v‖ ^ 2 * ‖primePoly S (shiftLine σ h₂) v‖ ^ 2
    * ‖primePoly S (shiftLine σ 0) v‖ ^ (2 * q - 4)

lemma measurable_twistPairPolyQ (q : ℝ) (S : Finset ℕ) (σ h₁ h₂ : ℝ) :
    Measurable (twistPairPolyQ q S σ h₁ h₂) := by
  unfold twistPairPolyQ
  exact ((((continuous_primePoly S (shiftLine σ h₁)).norm.pow 2).mul
    ((continuous_primePoly S (shiftLine σ h₂)).norm.pow 2)).measurable).mul
      (((continuous_primePoly S (shiftLine σ 0)).norm.measurable).pow_const _)

omit [MeasurableSpace Ω] in
lemma twistPairPolyQ_primesIco (q : ℝ) (a b : ℕ) (σ h₁ h₂ : ℝ) (ω : Ω) :
    twistPairPolyQ q (primesIco a b) σ h₁ h₂ (fun p => X (p : ℕ) ω)
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h₂) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ^ (2 * q - 4) := by
  rw [twistPairPolyQ, primePoly_primesIco, primePoly_primesIco, primePoly_primesIco]

end Twists

end RMF
