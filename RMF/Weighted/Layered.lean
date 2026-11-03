/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Factorisation

/-!
# The layered identity

For `2 ≤ y_K < … < y_1 ≤ x`,

`S(x) = F_{y_1}(½)·B_{y_1}(x) − ∑_{k=1}^{K-1} F_{y_{k+1}}(½)·T_{y_{k+1},y_k}(x) − T_{y_K}(x)`.

It is the factorisation of `RMF/Weighted/Factorisation.lean` telescoped.  The first identity
(`RMF.weightedRademacherSum_eq_mul_sub_truncationTail`) at `y = y_K` gives
`S(x) = F_{y_K}(½)·B_{y_K}(x) − T_{y_K}(x)`, and the second
(`RMF.roughWeightedRademacherSum_eq_mul_sub_blockTruncationTail`), at `(y_{k+1}, y_k)`, turns each
`F_{y_{k+1}}(½)·B_{y_{k+1}}(x)` into `F_{y_k}(½)·B_{y_k}(x) − F_{y_{k+1}}(½)·T_{y_{k+1},y_k}(x)` —
the two Euler products merging by `RMF.eulerProduct_mul_eulerProductIco`, since the block
`(y_{k+1}, y_k]` sits exactly on top of the primes `≤ y_{k+1}`.  Peeling from `k = K−1` down to
`k = 1` is `RMF.mul_roughWeightedRademacherSum_eq_sub_sum`, an induction on `K`.

## What is assumed, and what is not

Only `Y (k+1) ≤ Y k` for `1 ≤ k < K`, and `1 ≤ K`.  The conditions `2 ≤ y_K`, the strict
`y_{k+1} < y_k`, and `y_1 ≤ x` above are **all unused** — the first two because the second
identity needs only `y ≤ z`, the third because every index set here is cut out by `⌊x⌋₊`.  They
are conditions of the upper bound, not of the identity.

## Independence

In each product the two factors are also **independent** — `F_{y_{k+1}}` depends only on the
primes `≤ y_{k+1}`, `T_{y_{k+1},y_k}` only on those `> y_{k+1}`.  That statement about the law is
in `RMF/Weighted/Independence.lean`; the structural inequality (`RMF/Weighted/FixedQ.lean`) uses
it to turn `‖F·T‖_{2q}` into `‖F‖_{2q}·‖T‖_{2q}`.
-/

open Finset

namespace RMF

variable {Ω : Type*}

/-- **A head product times the block on top of it.**  The random form of
`RMF.eulerProduct_mul_eulerProductIco`; both sides are that identity at `fun n => f ω n`. -/
theorem randomEulerProduct_mul_randomEulerProductIco (f : Ω → ArithmeticFunction ℂ) {y₀ y₁ : ℕ}
    (h : y₀ ≤ y₁) (s : ℂ) (ω : Ω) :
    randomEulerProduct f y₀ s ω * randomEulerProductIco f y₀ y₁ s ω
      = randomEulerProduct f y₁ s ω :=
  eulerProduct_mul_eulerProductIco (fun n => f ω n) h s

/-- **The telescoping core of the layered identity.**  `F_{y_K}(½)·B_{y_K}(x)` peels into
`F_{y_1}(½)·B_{y_1}(x)` minus the layer terms.

Induction on `K`: the step rewrites `B_{y_{K+1}}` by the second factorisation identity
(`RMF.roughWeightedRademacherSum_eq_mul_sub_blockTruncationTail`) and merges the two Euler
products, which is exactly one more summand of the layer sum. -/
theorem mul_roughWeightedRademacherSum_eq_sub_sum {X : ℕ → Ω → ℂ} (Y : ℕ → ℕ) (x : ℝ) (ω : Ω)
    {K : ℕ} (hK : 1 ≤ K) (hY : ∀ k, 1 ≤ k → k < K → Y (k + 1) ≤ Y k) :
    randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (Y K + 1) (1 / 2) ω
        * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) (Y K) x ω
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (Y 1 + 1) (1 / 2) ω
          * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) (Y 1) x ω
        - ∑ k ∈ Finset.Ico 1 K,
            randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
                (Y (k + 1) + 1) (1 / 2) ω
              * blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
                  (Y (k + 1)) (Y k) x ω := by
  revert hY
  induction K, hK using Nat.le_induction with
  | base => intro _; simp
  | succ K hK ih =>
    intro hY
    have hIH := ih fun k hk1 hk2 => hY k hk1 (by omega)
    have hmono : Y (K + 1) ≤ Y K := hY K hK (by omega)
    have hfact := roughWeightedRademacherSum_eq_mul_sub_blockTruncationTail (X := X) hmono x ω
    have hprod := randomEulerProduct_mul_randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (Nat.succ_le_succ hmono) (1 / 2 : ℂ) ω
    rw [Finset.sum_Ico_succ_top hK, hfact, mul_sub, ← mul_assoc, hprod, hIH]
    ring

/-- **The layered identity.**  For `1 ≤ K` and `Y` nonincreasing on `[1, K]`,

`S(x) = F_{Y 1}(½)·B_{Y 1}(x) − ∑_{k=1}^{K-1} F_{Y (k+1)}(½)·T_{Y (k+1), Y k}(x) − T_{Y K}(x)`.

The independence of the two factors in each product is **not** part of this statement; see the
module docstring. -/
theorem weightedRademacherSum_eq_layered {X : ℕ → Ω → ℂ} (Y : ℕ → ℕ) (x : ℝ) (ω : Ω)
    {K : ℕ} (hK : 1 ≤ K) (hY : ∀ k, 1 ≤ k → k < K → Y (k + 1) ≤ Y k) :
    weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (Y 1 + 1) (1 / 2) ω
            * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) (Y 1) x ω
          - (∑ k ∈ Finset.Ico 1 K,
              randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
                  (Y (k + 1) + 1) (1 / 2) ω
                * blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
                    (Y (k + 1)) (Y k) x ω)
          - truncationTail (fun ω => squarefreeExtension fun p => X p ω) (Y K) x ω := by
  rw [weightedRademacherSum_eq_mul_sub_truncationTail (X := X) (Y K) x ω,
    mul_roughWeightedRademacherSum_eq_sub_sum Y x ω hK hY]

end RMF
