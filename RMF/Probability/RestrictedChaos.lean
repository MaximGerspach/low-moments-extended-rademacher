/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.Suppliers
import RMF.Probability.ChaosInterpolation

/-!
# The telescoping step of Hamdan's decomposition

The passage from Hamdan's restricted first moment (his Proposition 2.1) to the `q`-th moment
decomposes the chaos along a family of barrier events (Hamdan, arXiv:2604.05563, (2.18)).  Its
arithmetic core is `RMF.le_add_sum_add_of_le_add_mul`: iterating `Z ≤ R j + I j · Z` with
`0 ≤ I j ≤ 1`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The telescoped step**, as arithmetic.  From `Z ≤ R j + I j · Z` at every `j`, with `I` between
`0` and `1`: `Z ≤ R r + ∑_{j ∈ [r,m)} I j · R (j+1) + I m · Z`.  That is all Hamdan's (2.18) is: the
step `I j · I (j+1) · Z ≤ I (j+1) · Z` uses only `I j ≤ 1`, so no monotonicity of the barriers is
needed. -/
lemma le_add_sum_add_of_le_add_mul {Z : ℝ} {R I : ℕ → ℝ} (hZ : 0 ≤ Z)
    (hI0 : ∀ j, 0 ≤ I j) (hI1 : ∀ j, I j ≤ 1) (hstep : ∀ j, Z ≤ R j + I j * Z)
    (r m : ℕ) (hrm : r ≤ m) :
    Z ≤ R r + (∑ j ∈ Finset.Ico r m, I j * R (j + 1)) + I m * Z := by
  refine Nat.le_induction ?_ ?_ m hrm
  · simpa using hstep r
  · intro m hrm ih
    have h1 : I m * Z ≤ I m * (R (m + 1) + I (m + 1) * Z) :=
      mul_le_mul_of_nonneg_left (hstep (m + 1)) (hI0 m)
    have hnn : (0 : ℝ) ≤ I (m + 1) * Z := mul_nonneg (hI0 (m + 1)) hZ
    have h2 : I m * (I (m + 1) * Z) ≤ I (m + 1) * Z := by nlinarith [hI1 m]
    rw [Finset.sum_Ico_succ_top hrm]
    linarith

end RMF
