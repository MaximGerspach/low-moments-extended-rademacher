/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperChain
import RMF.EulerProduct.Moments
import RMF.EulerProduct.LogField

/-!
# The transfer layer: from Harper's walk to ours

In this formalisation Harper's Proposition 5 is stated for the walk built from `RMF.localLog`,
tilted by `‖F_y(s)‖²`.  Hamdan's restricted first moment (his Proposition 2.1, arXiv:2604.05563)
is about the walk built from `RMF.localTaylorTwo` — his `S_t` — tilted by `e^{2S_t}`.
`RMF.abs_localLog_sub_localTaylorTwo_le` gives `|localLog − localTaylorTwo| ≤ 12‖w‖³`
**deterministically**, and at `w = p^{-s}` that sums over the primes to an absolute `κ`
(`RMF.sum_prime_Ioc_rpow_cube_le'`).

## The free start

Hamdan's `G_A` imposes no constraint for `j < A/4`, while `barrierEvent` constrains from `j = 1`, so
the containment runs the wrong way.  No conditioning argument is needed: the suffix from `j = A/4`
is a barrier event with deterministic barriers (`RMF.subset_barrierEvent_shift`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The free start

Hamdan's `G_A` imposes nothing before `j = A/4`, whereas `RMF.barrierEvent` constrains from
`j = 1`, so `barrierEvent ⊆ G_A` and the containment runs the wrong way.

The repair needs no conditioning argument.  On `G_A` the walk is inside the tube
*at* `j = r` as well, so the **suffix** `walk_{m+r} - walk_r` is inside a tube whose endpoints are
differences of the original ones — deterministic, not random.  Widening by the tube's height at `r`
is all it costs, and that height is `O(A)`, which is the same order as `A` itself.  So Proposition
5 applies to the shifted walk at `a' = O(a)` and the conclusion `≪ a'/√n ≍ a/√n` is unchanged. -/

omit [MeasurableSpace Ω] in
/-- **The free start, removed — and an arbitrary additive offset absorbed.**  A walk constrained
only on `[r, n]` has its *suffix from `r`* constrained on `[1, n-r]` by deterministic barriers: on
the event `walk_r + Z ∈ [u r, v r]`, so `walk_{m+r} - walk_r ∈ [u(m+r) - v r, v(m+r) - u r]`.  The
random offset `Z` (the primes below the bottom block, which our walk omits and Harper's `S_J`
includes) cancels in the difference, so it never has to be estimated.  This lets Harper's
Proposition 5 (constraining from `j = 1`) apply to Hamdan's `G_A`. -/
lemma subset_barrierEvent_shift {X : ℕ → Ω → ℝ} {Z : Ω → ℝ} {n r : ℕ} {u v : ℕ → ℝ}
    (hrn : r ≤ n) :
    {ω | ∀ j, r ≤ j → j ≤ n → walk X j ω + Z ω ∈ Set.Icc (u j) (v j)}
      ⊆ barrierEvent (fun m => X (m + r)) (n - r)
          (fun m => u (m + r) - v r) (fun m => v (m + r) - u r) := by
  intro ω hω m hm1 hmn
  have hr : walk X r ω + Z ω ∈ Set.Icc (u r) (v r) := hω r le_rfl hrn
  have hmr : walk X (m + r) ω + Z ω ∈ Set.Icc (u (m + r)) (v (m + r)) :=
    hω (m + r) (Nat.le_add_left r m) (by omega)
  rw [Set.mem_Icc] at hr hmr ⊢
  have hshift : walk (fun i => X (i + r)) m ω = walk X (m + r) ω - walk X r ω := by
    rw [walk_shift X r m, Nat.add_comm r m]
  rw [hshift]
  exact ⟨by linarith [hmr.1, hr.2], by linarith [hmr.2, hr.1]⟩

end RMF
