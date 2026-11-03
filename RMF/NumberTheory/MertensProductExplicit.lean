/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensProduct
import RMF.NumberTheory.CosinePrimeSumExplicit

/-!
# The sum `∑_p 1/p²`, named

`RMF.primeInvSqSum`: `∑_p 1/p²`, the witness of `RMF.exists_sum_primesBelow_inv_sq_le`
(`RMF/NumberTheory/MertensProduct.lean`).
-/

namespace RMF

/-- **`∑_p 1/p²`**, as the series over all naturals with the non-primes set to `0`. -/
noncomputable def primeInvSqSum : ℝ := ∑' n : ℕ, (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0)

end RMF
