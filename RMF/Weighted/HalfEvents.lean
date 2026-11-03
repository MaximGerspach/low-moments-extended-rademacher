/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfPairBarrier

/-!
# The events of the `q = ½` lower bound

The objects the barriered moments (Propositions 6.3 and 6.4 of the paper), the small-prime
statements and the decomposition are stated in.  Everything lives on the block ladder of
`RMF.primeBlockSub`: at an integer offset `k`, block `m` is the primes with
`k + m < log log p ≤ k + m + 1`, and `RMF.halfBlock X k σ h m` is its contribution to
`log|F(½+σ+ih)|`, so that `RMF.walk (RMF.halfBlock X k σ h) j = log|F_{(k, k+j]}(½+σ+ih)|`.

* `RMF.halfWindow k`: the heights `h ∈ [e^{-(k+1)}, e^{-k}]`, on which `|σ+ih|^{-2} ≍ e^{2k}`.
* `RMF.halfBarrier`: the barrier `L(k,h)`.  The first `j₀` steps of the walk from scale `k` stay
  in `[-C₁, C₁]`, and the walk from `k + j₀` stays in Harper's tube `[-a - Bj, a + j - 2 log j]`
  up to scale `t`.  The second part is exactly the event of Harper's Proposition 5
  (`RMF.exists_const_proposition5_rademacher_of_cutoff_wide`), and the curvature `-2 log j` is in
  the walk's own index, where that theorem allows it.
* `RMF.halfLadder` and `RMF.halfAfter`: the events `E_≤(k)` and `E_>(k)` for the real-point walk
  `S_j = log F_{(k₀, j]}(½+σ)`, with no level `V`.
  `E_≤(k)`: `S` reaches a strict new maximum at `k`; `E_>(k)`: after `k` it never exceeds that
  value, up to scale `t`.  Their intersection says that `k` is the first place where `S` attains
  its maximum over `[k₀, t]`, so the intersections are pairwise disjoint
  (`RMF.disjoint_halfLadder_inter_halfAfter`); a weak inequality before `k` would not give this.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*}

/-- **The prime cut at scale `θ`**: a prime is below `scaleCut θ` exactly when
`p ≤ exp(e^θ)`, i.e. `log log p ≤ θ`. -/
noncomputable def scaleCut (θ : ℝ) : ℕ := ⌊blockScale θ 0⌋₊ + 1

/-- **The window of heights at scale `k`**: `[e^{-(k+1)}, e^{-k}]`. -/
def halfWindow (k : ℕ) : Set ℝ := Set.Icc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ)))

/-- **Block `m` of `log|F(½+σ+ih)|` at offset `θ`**: the local logarithms over the primes with
`θ + m < log log p ≤ θ + m + 1`.  The one-height form of `RMF.blockPairAdd`, and the increment
Harper's Proposition 5 is stated for. -/
noncomputable def halfBlock (X : ℕ → Ω → ℂ) (θ σ h : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ p ∈ primeBlockSub θ m, localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (X (p : ℕ) ω)

/-- **The barrier `L(k,h)`**: for `1 ≤ j ≤ j₀` the walk from scale `k` stays in `[-C₁, C₁]`, and
the walk from scale `k + j₀` stays in `[-a - Bj, a + j - 2 log j]` for `1 ≤ j ≤ t - k - j₀`.  Both
parts are `RMF.barrierEvent`s, the first with constant bounds. -/
def halfBarrier (X : ℕ → Ω → ℂ) (σ h : ℝ) (k j₀ t : ℕ) (C₁ a B : ℝ) : Set Ω :=
  barrierEvent (halfBlock X k σ h) j₀ (fun _ => -C₁) (fun _ => C₁)
    ∩ barrierEvent (halfBlock X ((k : ℝ) + j₀) σ h) (t - k - j₀)
        (fun j => -a - B * j) (fun j => a + j + harperHf j)

/-- **`E_≤(k)`**: the real-point walk from scale `k₀` is strictly below its value at `k` at every
earlier scale — `k` is a strict ladder time. -/
def halfLadder (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k : ℕ) : Set Ω :=
  {ω | ∀ j, j < k - k₀ → walk (halfBlock X k₀ σ 0) j ω < walk (halfBlock X k₀ σ 0) (k - k₀) ω}

/-- **`E_>(k)`**: after scale `k`, the real-point walk never rises above its value at `k`, up to
scale `t`. -/
def halfAfter (X : ℕ → Ω → ℂ) (σ : ℝ) (k t : ℕ) : Set Ω :=
  {ω | ∀ j, 1 ≤ j → j ≤ t - k → walk (halfBlock X k σ 0) j ω ≤ 0}

/-- **The walk from a later scale is the tail of the walk from an earlier one**: for `k₀ ≤ k`,
`log F_{(k, k+j]} = log F_{(k₀, k+j]} - log F_{(k₀, k]}`. -/
lemma walk_halfBlock_shift (X : ℕ → Ω → ℂ) (σ h : ℝ) {k₀ k : ℕ} (hk : k₀ ≤ k) (j : ℕ)
    (ω : Ω) :
    walk (halfBlock X k σ h) j ω
      = walk (halfBlock X k₀ σ h) (k - k₀ + j) ω - walk (halfBlock X k₀ σ h) (k - k₀) ω := by
  have hfun : halfBlock X k σ h = fun m => halfBlock X k₀ σ h (m + (k - k₀)) := by
    funext m ω'
    have hcast : ((k₀ : ℝ) + ((k - k₀ : ℕ) : ℝ)) = (k : ℝ) := by
      rw [Nat.cast_sub hk]
      ring
    simp only [halfBlock]
    rw [primeBlockSub_add, hcast]
  rw [hfun, walk_shift]

/-- **The events `E(k) = E_≤(k) ∩ E_>(k)` are pairwise disjoint.**  On `E(k')` the walk is
strictly higher at `k'` than at `k < k'`; on `E(k)` it is not. -/
lemma disjoint_halfLadder_inter_halfAfter (X : ℕ → Ω → ℂ) (σ : ℝ) {k₀ k k' t : ℕ}
    (hk₀ : k₀ ≤ k) (hkk' : k < k') (hk't : k' ≤ t) :
    Disjoint (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
      (halfLadder X σ k₀ k' ∩ halfAfter X σ k' t) := by
  refine Set.disjoint_left.2 fun ω hω hω' => ?_
  have hlt := hω'.1 (k - k₀) (by omega)
  have hle := hω.2 (k' - k) (by omega) (by omega)
  rw [walk_halfBlock_shift X σ 0 hk₀, show k - k₀ + (k' - k) = k' - k₀ from by omega] at hle
  linarith

variable [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

lemma measurable_halfBlock (hX : IsRademacherPrimeValues X μ) (θ σ h : ℝ) (m : ℕ) :
    Measurable (halfBlock X θ σ h m) :=
  Finset.measurable_sum _ fun p _ => (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)

lemma measurableSet_halfBarrier (hX : IsRademacherPrimeValues X μ) (σ h : ℝ) (k j₀ t : ℕ)
    (C₁ a B : ℝ) : MeasurableSet (halfBarrier X σ h k j₀ t C₁ a B) :=
  (measurableSet_barrierEvent (measurable_halfBlock hX _ σ h) _ _ _).inter
    (measurableSet_barrierEvent (measurable_halfBlock hX _ σ h) _ _ _)

lemma measurableSet_halfLadder (hX : IsRademacherPrimeValues X μ) (σ : ℝ) (k₀ k : ℕ) :
    MeasurableSet (halfLadder X σ k₀ k) := by
  have hrw : halfLadder X σ k₀ k = ⋂ j ∈ Set.Iio (k - k₀),
      {ω | walk (halfBlock X k₀ σ 0) j ω < walk (halfBlock X k₀ σ 0) (k - k₀) ω} := by
    ext ω
    simp only [halfLadder, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Iio]
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_lt (measurable_walk_of (measurable_halfBlock hX _ σ 0) j)
      (measurable_walk_of (measurable_halfBlock hX _ σ 0) _)

end RMF
