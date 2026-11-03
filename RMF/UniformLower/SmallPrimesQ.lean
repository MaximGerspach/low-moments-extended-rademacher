/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfDecomposition

/-!
# The small primes at exponent `q`

At a general exponent `q`, the reverse Hölder weight of the `q = ½` decomposition becomes
`‖F(σ)‖^{2q}` in place of `‖F(σ)‖`, so in its small-prime statements, (C2)
`RMF.integral_halfTwist_pair_le` and (C3) `RMF.le_setIntegral_halfLadder_twist`, the twist of the
numerator becomes `‖F(σ+ih)‖²‖F(σ)‖^{2q-2}` and that of the denominator
`‖F(σ+ih₁)‖²‖F(σ+ih₂)‖²‖F(σ)‖^{2q-4}`.  This file writes the latter, and the real-point moment
`‖F(σ)‖^r`, as products over the primes (`RMF.twistQPair_eq_prod`,
`RMF.rpow_norm_randomEulerProductIco_eq_prod`).
-/

open MeasureTheory

namespace RMF

/-! ### The weights at exponent `q`, as products over the primes -/

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The doubly twisted weight at exponent `q`, as a product over the primes. -/
lemma twistQPair_eq_prod {X : ℕ → Ω → ℂ} (a b : ℕ) (σ h₁ h₂ q : ℝ) (ω : Ω) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h₂) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ ^ (2 * q - 4)
      = ∏ p ∈ primesIco a b, (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h₁)‖ ^ 2
          * ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h₂)‖ ^ 2
          * ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q - 4)) := by
  rw [randomEulerProductIco_sqfree_eq, randomEulerProductIco_sqfree_eq,
    randomEulerProductIco_sqfree_eq, norm_prod, norm_prod, norm_prod, ← Finset.prod_pow,
    ← Finset.prod_pow, ← Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg _),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

omit [MeasurableSpace Ω] in
/-- The real-point moment at exponent `q`, as a product over the primes. -/
lemma rpow_norm_randomEulerProductIco_eq_prod {X : ℕ → Ω → ℂ} (a b : ℕ) (s : ℂ) (r : ℝ)
    (ω : Ω) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ r
      = ∏ p ∈ primesIco a b, ‖1 + X p ω * (p : ℂ) ^ (-s)‖ ^ r := by
  rw [randomEulerProductIco_sqfree_eq, norm_prod,
    Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg _)]

end RMF
