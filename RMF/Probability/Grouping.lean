/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Grouping an independent family into disjoint blocks

If `(f i)_{i ∈ ι}` is an independent family and `(S k)_{k ∈ κ}` are pairwise disjoint finite sets
of indices, then the block sums `∑_{i ∈ S k} f i` are again an independent family.

**Mathlib does not have this.**  Every disjoint-blocks independence result there is *binary*:
`ProbabilityTheory.indep_iSup_of_disjoint` (two σ-algebras), `iIndepFun.indepFun_finset` (two
finsets), `indepSets_piiUnionInter_of_disjoint` (two index sets), and
`iIndepFun.indepFun_finsetSum_of_notMem` (one block against one index).  There is
`iIndepFun_uncurry`, which goes blocks ⟹ whole family, but no converse.

The proof here does not redo the π-system work.  It takes Mathlib's binary
`indep_iSup_of_disjoint` and runs an induction over the finite set of blocks: peel one block `k₀`
off `insert k₀ s`, observe that `⋂_{k ∈ s} A k` lies in the σ-algebra of the *union* of the
remaining blocks — which is disjoint from `S k₀` — and recurse.

This is what lets the block increments of `log‖F_y(s)‖` over disjoint blocks of primes be treated
as an independent family, which is the hypothesis `RMF.isWindowComparison_of_indep` consumes.
-/

open MeasureTheory MeasurableSpace

namespace RMF

open ProbabilityTheory

variable {ι κ Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The σ-algebra form -/

/-- **Grouping, at the level of σ-algebras.**  An independent family of σ-algebras stays
independent after grouping along pairwise disjoint sets of indices.

Mathlib has this for *two* groups (`ProbabilityTheory.indep_iSup_of_disjoint`); this is the
`κ`-ary version, obtained from the binary one by induction on the block set. -/
theorem iIndep_biSup_of_pairwiseDisjoint {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ ‹MeasurableSpace Ω›) (h_indep : iIndep m μ) {S : κ → Set ι}
    (hS : Pairwise fun k l => Disjoint (S k) (S l)) :
    iIndep (fun k => ⨆ i ∈ S k, m i) μ := by
  classical
  rw [iIndep_iff]
  intro s A
  induction s using Finset.induction_on with
  | empty =>
    -- `μ univ = 1` is not an extra hypothesis: it is `h_indep` itself at `s = ∅`
    intro _
    simpa using (iIndep_iff m μ).1 h_indep ∅ (f := fun _ => Set.univ)
      (fun i hi => by simp at hi)
  | insert k₀ s' hk₀ ih =>
    intro hA
    -- the block `k₀` against the union of the rest
    have hdisj : Disjoint (S k₀) (⋃ k ∈ s', S k) := by
      refine Set.disjoint_iUnion_right.2 fun k => Set.disjoint_iUnion_right.2 fun hk => ?_
      exact hS (fun h => hk₀ (h ▸ hk))
    have hind := indep_iSup_of_disjoint h_le h_indep hdisj
    -- the remaining intersection lives in the σ-algebra of that union
    have hsub : ∀ k ∈ s', (⨆ i ∈ S k, m i) ≤ ⨆ i ∈ (⋃ l ∈ s', S l), m i := by
      intro k hk
      refine iSup₂_le fun i hi => ?_
      exact le_iSup₂ (f := fun i (_ : i ∈ ⋃ l ∈ s', S l) => m i) i
        (Set.mem_biUnion hk hi)
    have hmeas₂ : MeasurableSet[⨆ i ∈ (⋃ l ∈ s', S l), m i] (⋂ k ∈ s', A k) := by
      refine MeasurableSet.biInter (Set.to_countable _) fun k hk => ?_
      exact hsub k hk _ (hA k (Finset.mem_insert_of_mem hk))
    -- peel and recurse
    rw [Finset.set_biInter_insert, Finset.prod_insert hk₀,
      (Indep_iff _ _ _).1 hind _ _ (hA k₀ (Finset.mem_insert_self _ _)) hmeas₂,
      ih fun k hk => hA k (Finset.mem_insert_of_mem hk)]

/-! ### The block-sum form -/

variable {M : Type*} [MeasurableSpace M] [AddCommMonoid M] [MeasurableAdd₂ M]

/-- **Grouping an independent family into disjoint block sums.**

If `(f i)` is independent and the `S k` are pairwise disjoint, then `(∑_{i ∈ S k} f i)_k` is
independent.  This is the `κ`-ary companion of Mathlib's
`ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem`, which handles one block against one
index. -/
theorem iIndepFun_finsetSum_of_pairwiseDisjoint {f : ι → Ω → M} (hf : ∀ i, Measurable (f i))
    (h_indep : iIndepFun f μ) {S : κ → Finset ι}
    (hS : Pairwise fun k l => Disjoint (S k) (S l)) :
    iIndepFun (fun k ω => ∑ i ∈ S k, f i ω) μ := by
  classical
  have hle : ∀ i, MeasurableSpace.comap (f i) ‹MeasurableSpace M› ≤ ‹MeasurableSpace Ω› :=
    fun i => (hf i).comap_le
  have hSset : Pairwise fun k l => Disjoint ((S k : Set ι)) ((S l : Set ι)) := by
    intro k l hkl
    exact Finset.disjoint_coe.2 (hS hkl)
  have hgroup := iIndep_biSup_of_pairwiseDisjoint hle h_indep.iIndep hSset
  rw [iIndepFun_iff_iIndep]
  refine iIndep_of_iIndep_of_le hgroup fun k => ?_
  refine Measurable.comap_le (Finset.measurable_sum _ fun i hi => ?_)
  refine Measurable.of_comap_le ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ (S k : Set ι)) =>
    MeasurableSpace.comap (f i) ‹MeasurableSpace M›) i hi

end RMF
