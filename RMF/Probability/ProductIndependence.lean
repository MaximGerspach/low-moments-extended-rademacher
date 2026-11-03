/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import RMF.Analysis.Lindeberg
import RMF.Probability.MatchingGaussian

/-!
# Merging two independent families across a product measure

Two independent families living on *different* spaces become one independent family on the
product space, indexed by `ι ⊕ ι`.  This is the standard construction that realises a random
variable and its Gaussian comparison jointly, and Mathlib does not have it.

## Why the weaker statements in Mathlib are not enough

`ProbabilityTheory.indepFun_prod` gives that `X ∘ fst` and `Y ∘ snd` are independent under
`P ⊗ Q` — the *first factor against the second*.  `iIndepFun.indepFun_finset` gives one group of
coordinates against a disjoint group, within a single family.

A Lindeberg telescope needs neither.  At the step where the summand `a` is swapped, the prefix is

`∑_{i ∈ t} Y i ∘ snd + ∑_{i ∈ r} X i ∘ fst`,

which **mixes the two factors**, and it has to be independent of `X a ∘ fst` alone.  That is a
statement about the doubled family being jointly independent, and it follows from
`RMF.iIndepFun_sumElim_prod` below by `iIndepFun.indepFun_finset` — one coordinate against the
rest — composed with the measurable map that forms the sum.

## The proof

`iIndepFun_iff` reduces to: for a `Finset (ι ⊕ ι)` of comap-measurable sets, the measure of the
intersection is the product of the measures.  Each such set is a preimage `Z i ⁻¹' A i`; the ones
indexed by `Sum.inl` constrain the first coordinate only and the ones indexed by `Sum.inr` the
second, so the intersection is a *rectangle* `U ×ˢ V` and `Measure.prod_prod` splits it.  Each
side is then the original family's own `meas_biInter`.

Indexing by `ι ⊕ ι` rather than `Bool × ι` is what keeps this short: `Finset.toLeft` and
`Finset.toRight` split the index set with `Finset.mem_toLeft` a `simp` lemma, and
`Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight` splits the product to match.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {ι Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]

/-- The doubled family on the product space: `Sum.inl i` reads the first coordinate through `X i`,
`Sum.inr i` reads the second through `Y i`. -/
noncomputable def sumElimProd (X : ι → Ω → E) (Y : ι → Ω' → E) : ι ⊕ ι → Ω × Ω' → E :=
  Sum.elim (fun i (ω : Ω × Ω') => X i ω.1) (fun i (ω : Ω × Ω') => Y i ω.2)

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] in
@[simp] lemma sumElimProd_inl (X : ι → Ω → E) (Y : ι → Ω' → E) (i : ι) (ω : Ω × Ω') :
    sumElimProd X Y (Sum.inl i) ω = X i ω.1 := rfl

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] in
@[simp] lemma sumElimProd_inr (X : ι → Ω → E) (Y : ι → Ω' → E) (i : ι) (ω : Ω × Ω') :
    sumElimProd X Y (Sum.inr i) ω = Y i ω.2 := rfl

lemma measurable_sumElimProd {X : ι → Ω → E} {Y : ι → Ω' → E}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i)) :
    ∀ i, Measurable (sumElimProd X Y i) := by
  rintro (i | i)
  · exact (hXm i).comp measurable_fst
  · exact (hYm i).comp measurable_snd

open scoped Classical in
/-- The index set carrying the prefix: the `X`-coordinates over `r` and the `Y`-coordinates
over `t`. -/
private noncomputable def prefixIdx (t r : Finset ι) : Finset (ι ⊕ ι) :=
  r.image Sum.inl ∪ t.image Sum.inr

open scoped Classical in
omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
omit [MeasurableSpace E] in
private lemma sum_prefixIdx [AddCommMonoid E] {X : ι → Ω → E} {Y : ι → Ω' → E}
    (t r : Finset ι)
    (ω : Ω × Ω') :
    (∑ i ∈ (prefixIdx t r).attach, sumElimProd X Y (i : ι ⊕ ι) ω)
      = (∑ i ∈ t, Y i ω.2) + ∑ i ∈ r, X i ω.1 := by
  have hdisj : Disjoint (r.image Sum.inl) (t.image (Sum.inr : ι → ι ⊕ ι)) := by
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx'
    simp at hv
  rw [Finset.sum_attach _ fun i => sumElimProd X Y i ω, prefixIdx, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => Sum.inl_injective h),
    Finset.sum_image (fun _ _ _ _ h => Sum.inr_injective h)]
  simp only [sumElimProd_inl, sumElimProd_inr]
  exact add_comm _ _

variable {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- **Two independent families on two spaces are one independent family on the product.**

This is the joint realisation a Gaussian comparison needs: `X` lives under one law, `Y` under
another, and the swap requires them side by side and jointly independent.  Both marginals are
unchanged, so nothing about either family is disturbed by moving to the product. -/
theorem iIndepFun_sumElim_prod {X : ι → Ω → E} {Y : ι → Ω' → E}
    (hX : iIndepFun X P) (hY : iIndepFun Y Q) :
    iIndepFun (sumElimProd X Y) (P.prod Q) := by
  rw [iIndepFun_iff]
  intro s f' hf'
  simp only [MeasurableSpace.measurableSet_comap] at hf'
  choose! A hAm hAeq using hf'
  -- the two rectangle sides
  set U : Set Ω := ⋂ i ∈ s.toLeft, X i ⁻¹' A (Sum.inl i) with hUdef
  set V : Set Ω' := ⋂ i ∈ s.toRight, Y i ⁻¹' A (Sum.inr i) with hVdef
  -- the `inl` constraints see only the first coordinate, the `inr` ones only the second
  have hinl : ∀ i ∈ s.toLeft,
      f' (Sum.inl i) = (X i ⁻¹' A (Sum.inl i)) ×ˢ (Set.univ : Set Ω') := by
    intro i hi
    rw [← hAeq _ (Finset.mem_toLeft.mp hi)]
    ext ω
    simp [sumElimProd]
  have hinr : ∀ i ∈ s.toRight,
      f' (Sum.inr i) = (Set.univ : Set Ω) ×ˢ (Y i ⁻¹' A (Sum.inr i)) := by
    intro i hi
    rw [← hAeq _ (Finset.mem_toRight.mp hi)]
    ext ω
    simp [sumElimProd]
  -- the intersection is a rectangle
  have hset : (⋂ i ∈ s, f' i) = U ×ˢ V := by
    ext ω
    simp only [Set.mem_iInter, hUdef, hVdef, Set.mem_prod, Set.mem_preimage]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have hmem := h (Sum.inl i) (Finset.mem_toLeft.mp hi)
        rw [hinl i hi] at hmem
        exact hmem.1
      · have hmem := h (Sum.inr i) (Finset.mem_toRight.mp hi)
        rw [hinr i hi] at hmem
        exact hmem.2
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | inl j =>
        rw [hinl j (Finset.mem_toLeft.mpr hi)]
        exact ⟨h1 j (Finset.mem_toLeft.mpr hi), Set.mem_univ _⟩
      | inr j =>
        rw [hinr j (Finset.mem_toRight.mpr hi)]
        exact ⟨Set.mem_univ _, h2 j (Finset.mem_toRight.mpr hi)⟩
  -- each side factors under its own family
  have hU : P U = ∏ i ∈ s.toLeft, P (X i ⁻¹' A (Sum.inl i)) :=
    hX.meas_biInter fun i hi =>
      ⟨A (Sum.inl i), hAm _ (Finset.mem_toLeft.mp hi), rfl⟩
  have hV : Q V = ∏ i ∈ s.toRight, Q (Y i ⁻¹' A (Sum.inr i)) :=
    hY.meas_biInter fun i hi =>
      ⟨A (Sum.inr i), hAm _ (Finset.mem_toRight.mp hi), rfl⟩
  rw [hset, Measure.prod_prod, hU, hV,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by
      rw [hinl i hi, Measure.prod_prod, measure_univ, mul_one]
  · exact Finset.prod_congr rfl fun i hi => by
      rw [hinr i hi, Measure.prod_prod, measure_univ, one_mul]

/-! ### Regrouping an independent family into blocks

Mathlib has `ProbabilityTheory.iIndepFun_uncurry'`: if the *blocks* `((Xᵢⱼ)ⱼ)ᵢ` are independent and
each block is internally independent, then the family indexed by pairs is independent.  The
two-point argument needs the **converse** — it has the fine-grained family (from
`RMF.iIndepFun_sumElim_prod`, indexed by `ℕ ⊕ ℕ`) and wants the family of *pairs*, because that is
what carries the bivariate Gaussian increments.

The converse is true and its proof is the same chain read backwards: independence is equivalent to
the joint law being an infinite product (`iIndepFun_iff_map_fun_eq_infinitePi_map`), currying is a
measurable equivalence, and `MeasureTheory.Measure.infinitePi_map_curry` says it carries one
infinite product to the other.  The only extra step is that each block inherits independence from
the whole, which is `iIndepFun.precomp` along `j ↦ (i, j)`.
-/

/-- **Regrouping: from independent coordinates to independent blocks.**  If the family indexed by
pairs `(i, j)` is independent, so is the family of blocks `i ↦ (j ↦ X i j)`: the converse of
`ProbabilityTheory.iIndepFun_uncurry'`, which Mathlib has only in the forward direction.  Used with
`κ = Bool` to turn two independent real families into one independent family of *pairs*. -/
theorem iIndepFun_curry {κ : Type*} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ι → κ → Ω → E} (mY : ∀ i j, Measurable (Y i j))
    (h : iIndepFun (fun (p : ι × κ) ω => Y p.1 p.2 ω) P) :
    iIndepFun (fun i ω => fun j => Y i j ω) P := by
  have _ : ∀ i j, IsProbabilityMeasure (P.map (Y i j)) := fun i j =>
    Measure.isProbabilityMeasure_map (mY i j).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have hcur : (fun ω i => fun j => Y i j ω)
      = (MeasurableEquiv.curry ι κ E) ∘ (fun ω (p : ι × κ) => Y p.1 p.2 ω) := rfl
  rw [hcur, ← Measure.map_map (MeasurableEquiv.curry ι κ E).measurable (by fun_prop),
    (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h,
    MeasureTheory.Measure.infinitePi_map_curry (fun i j => P.map (Y i j))]
  refine congrArg MeasureTheory.Measure.infinitePi (funext fun i => ?_)
  have hi : iIndepFun (fun j => Y i j) P :=
    h.precomp (g := fun j : κ => (i, j)) fun a b hab => (Prod.mk.injEq .. ▸ hab).2
  exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (fun j => mY i j)).1 hi).symm

/-- **Two independent families on two spaces are one independent family of _pairs_.**
`RMF.iIndepFun_sumElim_prod` gives the fine-grained family over `ι ⊕ ι`; `RMF.iIndepFun_curry`
regroups it into pairs, each index carrying one increment of each walk.  Building the pair family on
one space (`RMF.exists_gaussian_pair_matching_moments`) gives `iIndepFun` for nothing but loses the
factorisation across the two coordinates; the product keeps it, at the cost of this lemma. -/
theorem iIndepFun_pairProd {X : ι → Ω → E} {Y : ι → Ω' → E}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hX : iIndepFun X P) (hY : iIndepFun Y Q) :
    iIndepFun (fun i (ω : Ω × Ω') => (X i ω.1, Y i ω.2)) (P.prod Q) := by
  set gmap : ι × Bool → ι ⊕ ι := fun p => cond p.2 (Sum.inr p.1) (Sum.inl p.1) with hgmap
  have hginj : Function.Injective gmap := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ h
    cases b <;> cases b' <;> simp_all
  set Yb : ι → Bool → Ω × Ω' → E := fun i b ω => cond b (Y i ω.2) (X i ω.1) with hYbdef
  have hYbm : ∀ i b, Measurable (Yb i b) := by
    intro i b
    cases b
    · exact (hXm i).comp measurable_fst
    · exact (hYm i).comp measurable_snd
  have hpair : iIndepFun (fun (p : ι × Bool) => Yb p.1 p.2) (P.prod Q) := by
    have h := (iIndepFun_sumElim_prod hX hY).precomp hginj
    have hfun : (fun p : ι × Bool => sumElimProd X Y (gmap p))
        = fun p : ι × Bool => Yb p.1 p.2 := by
      funext p ω
      rcases p with ⟨i, b⟩
      cases b <;> rfl
    exact hfun ▸ h
  exact (iIndepFun_curry hYbm hpair).comp
    (fun _ => fun u : Bool → E => (u false, u true)) fun _ => by fun_prop

/-- **A function of the first factor is independent of a function of the second.**

The one fact about a product measure that the two-point argument keeps reaching for, and the
reason it prefers a product realisation: the intersection of the two preimages is a rectangle, so
`MeasureTheory.Measure.prod_prod` is the whole proof. -/
theorem indepFun_comp_fst_snd {F : Type*} [MeasurableSpace F] (X : Ω → E) (Y : Ω' → F) :
    IndepFun (fun ω : Ω × Ω' => X ω.1) (fun ω : Ω × Ω' => Y ω.2) (P.prod Q) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro t r ht hr
  have h1 : (fun ω : Ω × Ω' => X ω.1) ⁻¹' t ∩ (fun ω : Ω × Ω' => Y ω.2) ⁻¹' r
      = (X ⁻¹' t) ×ˢ (Y ⁻¹' r) := by ext ω; simp
  have h2 : (fun ω : Ω × Ω' => X ω.1) ⁻¹' t = (X ⁻¹' t) ×ˢ (Set.univ : Set Ω') := by
    ext ω; simp
  have h3 : (fun ω : Ω × Ω' => Y ω.2) ⁻¹' r = (Set.univ : Set Ω) ×ˢ (Y ⁻¹' r) := by
    ext ω; simp
  rw [h1, h2, h3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, measure_univ,
    measure_univ, mul_one, one_mul]

/-! ### Moving between a product and its marginals

A function of the first coordinate only sees `P`, so its integral against `P ⊗ Q` is its integral
against `P`.  This is the transport that lets a statement proved on the product space be read off
on the two original spaces, and back. -/

lemma map_fst_prod_eq {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure Q] :
    Measure.map Prod.fst (P.prod Q) = P := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

lemma map_snd_prod_eq {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : Measure.map Prod.snd (P.prod Q) = Q := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]

lemma integral_comp_fst {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    ∫ z, f z.1 ∂(P.prod Q) = ∫ ω, f ω ∂P := by
  have h := integral_map (μ := P.prod Q) (φ := Prod.fst) (f := f)
    measurable_fst.aemeasurable (by rwa [map_fst_prod_eq])
  rw [map_fst_prod_eq] at h
  exact h.symm

lemma integral_comp_snd {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {g : Ω' → ℝ} (hg : AEStronglyMeasurable g Q) :
    ∫ z, g z.2 ∂(P.prod Q) = ∫ ω, g ω ∂Q := by
  have h := integral_map (μ := P.prod Q) (φ := Prod.snd) (f := g)
    measurable_snd.aemeasurable (by rwa [map_snd_prod_eq])
  rw [map_snd_prod_eq] at h
  exact h.symm

lemma integrable_comp_fst {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {f : Ω → ℝ} (hf : Integrable f P) :
    Integrable (fun z : Ω × Ω' => f z.1) (P.prod Q) := by
  refine Integrable.comp_aemeasurable ?_ measurable_fst.aemeasurable
  rwa [map_fst_prod_eq]

lemma integrable_comp_snd {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {g : Ω' → ℝ} (hg : Integrable g Q) :
    Integrable (fun z : Ω × Ω' => g z.2) (P.prod Q) := by
  refine Integrable.comp_aemeasurable ?_ measurable_snd.aemeasurable
  rwa [map_snd_prod_eq]

/-! ### The telescope's hypothesis, discharged

A Lindeberg telescope over the merged family asks, at the step where `a` is swapped, that the
prefix be independent of the coordinate being swapped.  Both directions are
`iIndepFun.indepFun_finset` — one coordinate against a disjoint group — applied to
`RMF.iIndepFun_sumElim_prod` and composed with the map that forms the sum.

Both compositions are the *same* map, `v ↦ ∑ i, v i` over the attached finset: on the group it is
the prefix, on the singleton it is the coordinate.  That is why one measurability proof serves
both. -/

open scoped Classical in
/-- The prefix `∑_{i ∈ t} Y i ∘ snd + ∑_{i ∈ r} X i ∘ fst` is independent of `X a ∘ fst` as soon as
`a ∉ r`.  Note the hypothesis does not mention `t`: the `Y` part lives on the other factor and can
never interfere with an `X` coordinate. -/
theorem indepFun_prefix_left [AddCommMonoid E] [MeasurableAdd₂ E]
    {X : ι → Ω → E} {Y : ι → Ω' → E}
    (hX : iIndepFun X P) (hY : iIndepFun Y Q)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    {t r : Finset ι} {a : ι} (har : a ∉ r) :
    IndepFun (fun ω : Ω × Ω' => (∑ i ∈ t, Y i ω.2) + ∑ i ∈ r, X i ω.1)
      (fun ω : Ω × Ω' => X a ω.1) (P.prod Q) := by
  have hnot : (Sum.inl a : ι ⊕ ι) ∉ prefixIdx t r := by
    simp only [prefixIdx, Finset.mem_union, Finset.mem_image, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, hxeq⟩
      rw [Sum.inl.injEq] at hxeq
      exact har (hxeq ▸ hx)
    · rintro ⟨x, _, hxeq⟩
      simp at hxeq
  have hind := (iIndepFun_sumElim_prod hX hY).indepFun_finset
    (prefixIdx t r) {Sum.inl a} (Finset.disjoint_singleton_right.2 hnot)
    (measurable_sumElimProd hXm hYm)
  have hcomp := hind.comp
    (φ := fun v : ↑(prefixIdx t r) → E => ∑ i ∈ Finset.univ, v i)
    (ψ := fun v : ↑({Sum.inl a} : Finset (ι ⊕ ι)) → E => ∑ i ∈ Finset.univ, v i)
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have heq₂ : ∀ ω : Ω × Ω',
      (∑ i ∈ ({Sum.inl a} : Finset (ι ⊕ ι)).attach, sumElimProd X Y (i : ι ⊕ ι) ω)
        = X a ω.1 := by
    intro ω
    rw [Finset.sum_attach _ fun i => sumElimProd X Y i ω, Finset.sum_singleton]
    rfl
  simpa only [Function.comp_def, Finset.univ_eq_attach, sum_prefixIdx, heq₂] using hcomp

open scoped Classical in
/-- The mirror image: the prefix is independent of `Y a ∘ snd` as soon as `a ∉ t`. -/
theorem indepFun_prefix_right [AddCommMonoid E] [MeasurableAdd₂ E]
    {X : ι → Ω → E} {Y : ι → Ω' → E}
    (hX : iIndepFun X P) (hY : iIndepFun Y Q)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    {t r : Finset ι} {a : ι} (hat : a ∉ t) :
    IndepFun (fun ω : Ω × Ω' => (∑ i ∈ t, Y i ω.2) + ∑ i ∈ r, X i ω.1)
      (fun ω : Ω × Ω' => Y a ω.2) (P.prod Q) := by
  have hnot : (Sum.inr a : ι ⊕ ι) ∉ prefixIdx t r := by
    simp only [prefixIdx, Finset.mem_union, Finset.mem_image, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, _, hxeq⟩
      simp at hxeq
    · rintro ⟨x, hx, hxeq⟩
      rw [Sum.inr.injEq] at hxeq
      exact hat (hxeq ▸ hx)
  have hind := (iIndepFun_sumElim_prod hX hY).indepFun_finset
    (prefixIdx t r) {Sum.inr a} (Finset.disjoint_singleton_right.2 hnot)
    (measurable_sumElimProd hXm hYm)
  have hcomp := hind.comp
    (φ := fun v : ↑(prefixIdx t r) → E => ∑ i ∈ Finset.univ, v i)
    (ψ := fun v : ↑({Sum.inr a} : Finset (ι ⊕ ι)) → E => ∑ i ∈ Finset.univ, v i)
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have heq₂ : ∀ ω : Ω × Ω',
      (∑ i ∈ ({Sum.inr a} : Finset (ι ⊕ ι)).attach, sumElimProd X Y (i : ι ⊕ ι) ω)
        = Y a ω.2 := by
    intro ω
    rw [Finset.sum_attach _ fun i => sumElimProd X Y i ω, Finset.sum_singleton]
    rfl
  simpa only [Function.comp_def, Finset.univ_eq_attach, sum_prefixIdx, heq₂] using hcomp

/-! ### The swap, for two families on two spaces

`RMF.abs_integral_telescope_le_of_indep` compares two families living on the *same* space.  Harper's
do not: the tilted increments live under `P` and the matching Gaussians under `Q`.  Lifting both to
`Ω × Ω'` fixes that — the merge makes the doubled family independent, the prefix lemmas discharge
the telescope's hypothesis, and the marginal transport carries the conclusion back to the two
original spaces. -/

/-- **The Lindeberg swap for two families on two spaces** — the additive bound `D` that
`RMF.isWindowComparison₁_of_swap` asks for.

Both sides are stated on their own space; the product is an artefact of the proof and does not
appear.  The moment hypotheses are the *raw* first and second moments, which is what
`RMF.exists_gaussian_matching_moments` is built to supply. -/
theorem abs_integral_sum_sub_le {ι : Type*} {s : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f f₁ f₂ f₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃)
    {ξ : ι → Ω → ℝ} {G : ι → Ω' → ℝ}
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    (hξ₁ : ∀ i ∈ s, Integrable (ξ i) P)
    (hξ₂ : ∀ i ∈ s, Integrable (fun ω => ξ i ω * ξ i ω) P)
    (hG₁ : ∀ i ∈ s, Integrable (G i) Q)
    (hG₂ : ∀ i ∈ s, Integrable (fun ω => G i ω * G i ω) Q)
    (hm₁ : ∀ i ∈ s, ∫ ω, ξ i ω ∂P = ∫ ω, G i ω ∂Q)
    (hm₂ : ∀ i ∈ s, ∫ ω, ξ i ω * ξ i ω ∂P = ∫ ω, G i ω * G i ω ∂Q)
    (hTξ : ∀ i ∈ s, Integrable (fun ω => |ξ i ω| ^ 3) P)
    (hTG : ∀ i ∈ s, Integrable (fun ω => |G i ω| ^ 3) Q) :
    |(∫ ω, f (∑ i ∈ s, ξ i ω) ∂P) - ∫ ω, f (∑ i ∈ s, G i ω) ∂Q|
      ≤ M₃ * ∑ i ∈ s, ((∫ ω, |ξ i ω| ^ 3 ∂P) + ∫ ω, |G i ω| ^ 3 ∂Q) := by
  classical
  set R : Measure (Ω × Ω') := P.prod Q with hRdef
  set X : ι → Ω × Ω' → ℝ := fun i z => ξ i z.1 with hXdef
  set Y : ι → Ω × Ω' → ℝ := fun i z => G i z.2 with hYdef
  have hXm : ∀ i, Measurable (X i) := fun i => (hξm i).comp measurable_fst
  have hYm : ∀ i, Measurable (Y i) := fun i => (hGm i).comp measurable_snd
  -- the six integral transports
  have eX₁ : ∀ i, (∫ z, X i z ∂R) = ∫ ω, ξ i ω ∂P := fun i =>
    integral_comp_fst (hξm i).aestronglyMeasurable
  have eY₁ : ∀ i, (∫ z, Y i z ∂R) = ∫ ω, G i ω ∂Q := fun i =>
    integral_comp_snd (hGm i).aestronglyMeasurable
  have eX₂ : ∀ i, (∫ z, X i z * X i z ∂R) = ∫ ω, ξ i ω * ξ i ω ∂P := by
    intro i; have hi := hξm i
    exact integral_comp_fst (f := fun ω => ξ i ω * ξ i ω) (by fun_prop)
  have eY₂ : ∀ i, (∫ z, Y i z * Y i z ∂R) = ∫ ω, G i ω * G i ω ∂Q := by
    intro i; have hi := hGm i
    exact integral_comp_snd (g := fun ω => G i ω * G i ω) (by fun_prop)
  have eX₃ : ∀ i, (∫ z, |X i z| ^ 3 ∂R) = ∫ ω, |ξ i ω| ^ 3 ∂P := by
    intro i; have hi := hξm i
    exact integral_comp_fst (f := fun ω => |ξ i ω| ^ 3) (by fun_prop)
  have eY₃ : ∀ i, (∫ z, |Y i z| ^ 3 ∂R) = ∫ ω, |G i ω| ^ 3 ∂Q := by
    intro i; have hi := hGm i
    exact integral_comp_snd (g := fun ω => |G i ω| ^ 3) (by fun_prop)
  -- the two endpoints
  have hsumX : ∀ z : Ω × Ω', (∑ i ∈ s, X i z) = ∑ i ∈ s, ξ i z.1 := fun z => rfl
  have hsumY : ∀ z : Ω × Ω', (∑ i ∈ s, Y i z) = ∑ i ∈ s, G i z.2 := fun z => rfl
  have eEndX : (∫ z, f (∑ i ∈ s, X i z) ∂R) = ∫ ω, f (∑ i ∈ s, ξ i ω) ∂P := by
    simp only [hsumX]
    exact integral_comp_fst (Ω' := Ω')
      (((continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable.comp
        (Finset.measurable_sum s fun i _ => hξm i))).aestronglyMeasurable
  have eEndY : (∫ z, f (∑ i ∈ s, Y i z) ∂R) = ∫ ω, f (∑ i ∈ s, G i ω) ∂Q := by
    simp only [hsumY]
    exact integral_comp_snd (Ω := Ω)
      (((continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable.comp
        (Finset.measurable_sum s fun i _ => hGm i))).aestronglyMeasurable
  -- the telescope on the product space
  have key := abs_integral_telescope_le_of_indep (μ := R) (s := s) hf hf₁ hf₂ hM₀ hM₁ hM₂ hM₃
    hXm hYm
    (fun i hi => by rw [hXdef]; exact integrable_comp_fst (hξ₁ i hi))
    (fun i hi => by rw [hXdef]; exact integrable_comp_fst (hξ₂ i hi))
    (fun i hi => by rw [hYdef]; exact integrable_comp_snd (hG₁ i hi))
    (fun i hi => by rw [hYdef]; exact integrable_comp_snd (hG₂ i hi))
    (fun i hi => by rw [eX₁, eY₁]; exact hm₁ i hi)
    (fun i hi => by rw [eX₂, eY₂]; exact hm₂ i hi)
    (fun i hi => by rw [hXdef]; exact integrable_comp_fst (hTξ i hi))
    (fun i hi => by rw [hYdef]; exact integrable_comp_snd (hTG i hi))
    (fun a _ t r hat har =>
      ⟨indepFun_prefix_left hξi hGi hξm hGm har, indepFun_prefix_right hξi hGi hξm hGm hat⟩)
  rw [eEndX, eEndY] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [eX₃, eY₃]

/-! ### The two-dimensional swap, for two families on two spaces

The pair analogue of the section above.  `RMF.iIndepFun_sumElim_prod` and the two prefix lemmas are
stated at a general value type, so at `ℝ × ℝ` the only new work is transporting the five moments
and the Lindeberg bound across the product, and bridging between the pair-valued sum in `ℝ × ℝ`
and its two components. -/

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- The prefix, componentwise — the form `RMF.abs_integral_telescope_window_le` asks for. -/
private lemma prefix_pair_eq {ι : Type*} (ξ : ι → Ω → ℝ × ℝ) (G : ι → Ω' → ℝ × ℝ)
    (t r : Finset ι) :
    (fun z : Ω × Ω' => (((∑ i ∈ t, (G i z.2).1) + ∑ i ∈ r, (ξ i z.1).1),
        ((∑ i ∈ t, (G i z.2).2) + ∑ i ∈ r, (ξ i z.1).2)))
      = fun z : Ω × Ω' => (∑ i ∈ t, G i z.2) + ∑ i ∈ r, ξ i z.1 := by
  funext z
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

/-- **The two-dimensional swap for two families on two spaces** — the pair analogue of
`RMF.abs_integral_sum_sub_le`, and what the bivariate window comparison calls.

`ξ` lives under `P`, the comparison Gaussian pair `G` under `Q`, and the swap is realised on
`P.prod Q`, where both marginals are unchanged.  The five moment equalities are the ones
`RMF.quadMonomial` names — including the mixed one. -/
theorem abs_integral_window_pair_sum_sub_le {ι : Type*} {s : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ξ : ι → Ω → ℝ × ℝ} {G : ι → Ω' → ℝ × ℝ} {δ : ℝ} (hδ : 0 < δ) (a₁ b₁ a₂ b₂ : ℝ)
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    (hmξ : ∀ i ∈ s, ∀ j, Integrable (fun ω => quadMonomial j (ξ i ω)) P)
    (hmG : ∀ i ∈ s, ∀ j, Integrable (fun ω => quadMonomial j (G i ω)) Q)
    (hmom : ∀ i ∈ s, ∀ j, (∫ ω, quadMonomial j (ξ i ω) ∂P)
      = ∫ ω, quadMonomial j (G i ω) ∂Q)
    (hTξ : ∀ i ∈ s, Integrable (fun ω => windowLindebergBound δ (ξ i ω)) P)
    (hTG : ∀ i ∈ s, Integrable (fun ω => windowLindebergBound δ (G i ω)) Q) :
    |(∫ ω, window δ a₁ b₁ (∑ i ∈ s, (ξ i ω).1)
          * window δ a₂ b₂ (∑ i ∈ s, (ξ i ω).2) ∂P)
        - ∫ ω, window δ a₁ b₁ (∑ i ∈ s, (G i ω).1)
            * window δ a₂ b₂ (∑ i ∈ s, (G i ω).2) ∂Q|
      ≤ ∑ i ∈ s, ((∫ ω, windowLindebergBound δ (ξ i ω) ∂P)
          + ∫ ω, windowLindebergBound δ (G i ω) ∂Q) := by
  classical
  have hξc : ∀ i, Measurable fun z : Ω × Ω' => ξ i z.1 := fun i => (hξm i).comp measurable_fst
  have hGc : ∀ i, Measurable fun z : Ω × Ω' => G i z.2 := fun i => (hGm i).comp measurable_snd
  -- the transports
  have eXq : ∀ i j, (∫ z, quadMonomial j (ξ i z.1) ∂(P.prod Q))
      = ∫ ω, quadMonomial j (ξ i ω) ∂P := fun i j =>
    integral_comp_fst (f := fun ω => quadMonomial j (ξ i ω))
      ((measurable_quadMonomial j).comp (hξm i)).aestronglyMeasurable
  have eYq : ∀ i j, (∫ z, quadMonomial j (G i z.2) ∂(P.prod Q))
      = ∫ ω, quadMonomial j (G i ω) ∂Q := fun i j =>
    integral_comp_snd (g := fun ω => quadMonomial j (G i ω))
      ((measurable_quadMonomial j).comp (hGm i)).aestronglyMeasurable
  have eXT : ∀ i, (∫ z, windowLindebergBound δ (ξ i z.1) ∂(P.prod Q))
      = ∫ ω, windowLindebergBound δ (ξ i ω) ∂P := fun i =>
    integral_comp_fst (f := fun ω => windowLindebergBound δ (ξ i ω))
      ((measurable_windowLindebergBound δ).comp (hξm i)).aestronglyMeasurable
  have eYT : ∀ i, (∫ z, windowLindebergBound δ (G i z.2) ∂(P.prod Q))
      = ∫ ω, windowLindebergBound δ (G i ω) ∂Q := fun i =>
    integral_comp_snd (g := fun ω => windowLindebergBound δ (G i ω))
      ((measurable_windowLindebergBound δ).comp (hGm i)).aestronglyMeasurable
  -- the two endpoints
  have hendX : Measurable fun ω : Ω => window δ a₁ b₁ (∑ i ∈ s, (ξ i ω).1)
      * window δ a₂ b₂ (∑ i ∈ s, (ξ i ω).2) :=
    ((measurable_window δ a₁ b₁).comp
        (Finset.measurable_sum s fun i _ => (hξm i).fst)).mul
      ((measurable_window δ a₂ b₂).comp (Finset.measurable_sum s fun i _ => (hξm i).snd))
  have hendY : Measurable fun ω : Ω' => window δ a₁ b₁ (∑ i ∈ s, (G i ω).1)
      * window δ a₂ b₂ (∑ i ∈ s, (G i ω).2) :=
    ((measurable_window δ a₁ b₁).comp
        (Finset.measurable_sum s fun i _ => (hGm i).fst)).mul
      ((measurable_window δ a₂ b₂).comp (Finset.measurable_sum s fun i _ => (hGm i).snd))
  have eEndX : (∫ z, window δ a₁ b₁ (∑ i ∈ s, (ξ i z.1).1)
        * window δ a₂ b₂ (∑ i ∈ s, (ξ i z.1).2) ∂(P.prod Q))
      = ∫ ω, window δ a₁ b₁ (∑ i ∈ s, (ξ i ω).1)
          * window δ a₂ b₂ (∑ i ∈ s, (ξ i ω).2) ∂P :=
    integral_comp_fst (Ω' := Ω') hendX.aestronglyMeasurable
  have eEndY : (∫ z, window δ a₁ b₁ (∑ i ∈ s, (G i z.2).1)
        * window δ a₂ b₂ (∑ i ∈ s, (G i z.2).2) ∂(P.prod Q))
      = ∫ ω, window δ a₁ b₁ (∑ i ∈ s, (G i ω).1)
          * window δ a₂ b₂ (∑ i ∈ s, (G i ω).2) ∂Q :=
    integral_comp_snd (Ω := Ω) hendY.aestronglyMeasurable
  -- the telescope on the product space
  have key := abs_integral_telescope_window_le_of_indep (μ := P.prod Q) (s := s)
    (X := fun i z => ξ i z.1) (Y := fun i z => G i z.2)
    (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) hδ hξc hGc
    (fun i hi j => integrable_comp_fst (hmξ i hi j))
    (fun i hi j => integrable_comp_snd (hmG i hi j))
    (fun i hi j => by rw [eXq i j, eYq i j]; exact hmom i hi j)
    (fun i hi => integrable_comp_fst (hTξ i hi))
    (fun i hi => integrable_comp_snd (hTG i hi))
    (fun a _ t r hat har => by
      rw [prefix_pair_eq ξ G t r]
      exact ⟨indepFun_prefix_left hξi hGi hξm hGm har,
        indepFun_prefix_right hξi hGi hξm hGm hat⟩)
  rw [eEndX, eEndY] at key
  refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [eXT i, eYT i]

/-- **The per-block swap, at the two smoothed windows.**  `RMF.smoothIndicatorLower δ u v` **is**
`RMF.window δ u v`, and `RMF.smoothIndicatorUpper δ u v` is `RMF.window δ (u-δ) (v+δ)`, so both
halves of the sandwich are `RMF.abs_integral_window_pair_sum_sub_le` at different endpoints with the
*same* bound: the Lindeberg estimate sees only the smoothing width. -/
theorem abs_integral_smoothIndicator_pair_sum_sub_le {ι : Type*} {t : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ξ : ι → Ω → ℝ × ℝ} {G : ι → Ω' → ℝ × ℝ} {δ : ℝ} (hδ : 0 < δ) (u₁ v₁ u₂ v₂ : ℝ)
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    (hmξ : ∀ i ∈ t, ∀ j, Integrable (fun ω => quadMonomial j (ξ i ω)) P)
    (hmG : ∀ i ∈ t, ∀ j, Integrable (fun ω => quadMonomial j (G i ω)) Q)
    (hmom : ∀ i ∈ t, ∀ j, (∫ ω, quadMonomial j (ξ i ω) ∂P)
      = ∫ ω, quadMonomial j (G i ω) ∂Q)
    (hTξ : ∀ i ∈ t, Integrable (fun ω => windowLindebergBound δ (ξ i ω)) P)
    (hTG : ∀ i ∈ t, Integrable (fun ω => windowLindebergBound δ (G i ω)) Q) :
    |(∫ ω, smoothIndicatorUpper δ u₁ v₁ (∑ i ∈ t, (ξ i ω).1)
            * smoothIndicatorUpper δ u₂ v₂ (∑ i ∈ t, (ξ i ω).2) ∂P)
          - ∫ ω, smoothIndicatorUpper δ u₁ v₁ (∑ i ∈ t, (G i ω).1)
              * smoothIndicatorUpper δ u₂ v₂ (∑ i ∈ t, (G i ω).2) ∂Q|
        ≤ ∑ i ∈ t, ((∫ ω, windowLindebergBound δ (ξ i ω) ∂P)
            + ∫ ω, windowLindebergBound δ (G i ω) ∂Q)
      ∧ |(∫ ω, smoothIndicatorLower δ u₁ v₁ (∑ i ∈ t, (ξ i ω).1)
            * smoothIndicatorLower δ u₂ v₂ (∑ i ∈ t, (ξ i ω).2) ∂P)
          - ∫ ω, smoothIndicatorLower δ u₁ v₁ (∑ i ∈ t, (G i ω).1)
              * smoothIndicatorLower δ u₂ v₂ (∑ i ∈ t, (G i ω).2) ∂Q|
        ≤ ∑ i ∈ t, ((∫ ω, windowLindebergBound δ (ξ i ω) ∂P)
            + ∫ ω, windowLindebergBound δ (G i ω) ∂Q) :=
  ⟨abs_integral_window_pair_sum_sub_le hδ (u₁ - δ) (v₁ + δ) (u₂ - δ) (v₂ + δ)
      hξm hGm hξi hGi hmξ hmG hmom hTξ hTG,
    abs_integral_window_pair_sum_sub_le hδ u₁ v₁ u₂ v₂ hξm hGm hξi hGi hmξ hmG hmom hTξ hTG⟩

/-! ### The Lindeberg charge, in third absolute moments

`RMF.abs_integral_smoothIndicator_pair_sum_sub_le` charges the swap
`∑_i (∫ windowLindebergBound δ (ξ i) + ∫ windowLindebergBound δ (G i))`, and what the two-point
block estimates deliver is a bound on each coordinate's **third absolute moment**.  These two
lemmas are the bridge.

The constant is `3600/δ³`: `900/δ³` from `RMF.windowLindebergBound_le`, times the `4` in
`RMF.add_cube_le` — the same crude convexity bound the one-point Gaussian third moment already
needed.  Nothing here is sharp and nothing needs to be: the margin against the box mass is a
power of `x_j`. -/

/-- **The Lindeberg charge of one pair**, in terms of its two third absolute moments. -/
theorem integral_windowLindebergBound_le {P : Measure Ω}
    {ξ : Ω → ℝ × ℝ} {δ T₁ T₂ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun ω => windowLindebergBound δ (ξ ω)) P)
    (h₁ : Integrable (fun ω => |(ξ ω).1| ^ 3) P) (h₂ : Integrable (fun ω => |(ξ ω).2| ^ 3) P)
    (hT₁ : (∫ ω, |(ξ ω).1| ^ 3 ∂P) ≤ T₁) (hT₂ : (∫ ω, |(ξ ω).2| ^ 3 ∂P) ≤ T₂) :
    (∫ ω, windowLindebergBound δ (ξ ω) ∂P) ≤ 3600 / δ ^ 3 * (T₁ + T₂) := by
  have hc : (0 : ℝ) ≤ 900 / δ ^ 3 := by positivity
  have hc' : (0 : ℝ) ≤ 3600 / δ ^ 3 := by positivity
  have hmono : (∫ ω, windowLindebergBound δ (ξ ω) ∂P)
      ≤ ∫ ω, 3600 / δ ^ 3 * (|(ξ ω).1| ^ 3 + |(ξ ω).2| ^ 3) ∂P := by
    refine integral_mono hint ((h₁.add h₂).const_mul _) fun ω => ?_
    calc windowLindebergBound δ (ξ ω)
        ≤ 900 / δ ^ 3 * (|(ξ ω).1| + |(ξ ω).2|) ^ 3 := windowLindebergBound_le hδ (ξ ω)
      _ ≤ 900 / δ ^ 3 * (4 * (|(ξ ω).1| ^ 3 + |(ξ ω).2| ^ 3)) :=
          mul_le_mul_of_nonneg_left (add_cube_le (abs_nonneg _) (abs_nonneg _)) hc
      _ = 3600 / δ ^ 3 * (|(ξ ω).1| ^ 3 + |(ξ ω).2| ^ 3) := by ring
  rw [integral_const_mul, integral_add h₁ h₂] at hmono
  nlinarith [hmono, hT₁, hT₂, hc']

/-- **The Lindeberg charge over a block**, both sides at once. -/
theorem sum_integral_windowLindebergBound_le {ι : Type*} {t : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'}
    {ξ : ι → Ω → ℝ × ℝ} {G : ι → Ω' → ℝ × ℝ} {δ T : ℝ} (hδ : 0 < δ)
    (hintξ : ∀ i ∈ t, Integrable (fun ω => windowLindebergBound δ (ξ i ω)) P)
    (hintG : ∀ i ∈ t, Integrable (fun ω => windowLindebergBound δ (G i ω)) Q)
    (hξ₁ : ∀ i ∈ t, Integrable (fun ω => |(ξ i ω).1| ^ 3) P)
    (hξ₂ : ∀ i ∈ t, Integrable (fun ω => |(ξ i ω).2| ^ 3) P)
    (hG₁ : ∀ i ∈ t, Integrable (fun ω => |(G i ω).1| ^ 3) Q)
    (hG₂ : ∀ i ∈ t, Integrable (fun ω => |(G i ω).2| ^ 3) Q)
    (hsum : ∑ i ∈ t, ((∫ ω, |(ξ i ω).1| ^ 3 ∂P) + (∫ ω, |(ξ i ω).2| ^ 3 ∂P)
        + (∫ ω, |(G i ω).1| ^ 3 ∂Q) + ∫ ω, |(G i ω).2| ^ 3 ∂Q) ≤ T) :
    ∑ i ∈ t, ((∫ ω, windowLindebergBound δ (ξ i ω) ∂P)
        + ∫ ω, windowLindebergBound δ (G i ω) ∂Q) ≤ 3600 / δ ^ 3 * T := by
  have hc : (0 : ℝ) ≤ 3600 / δ ^ 3 := by positivity
  have hterm : ∀ i ∈ t, (∫ ω, windowLindebergBound δ (ξ i ω) ∂P)
        + (∫ ω, windowLindebergBound δ (G i ω) ∂Q)
      ≤ 3600 / δ ^ 3 * ((∫ ω, |(ξ i ω).1| ^ 3 ∂P) + (∫ ω, |(ξ i ω).2| ^ 3 ∂P)
          + (∫ ω, |(G i ω).1| ^ 3 ∂Q) + ∫ ω, |(G i ω).2| ^ 3 ∂Q) := by
    intro i hi
    have hξ := integral_windowLindebergBound_le hδ (hintξ i hi) (hξ₁ i hi) (hξ₂ i hi)
      le_rfl le_rfl
    have hG := integral_windowLindebergBound_le hδ (hintG i hi) (hG₁ i hi) (hG₂ i hi)
      le_rfl le_rfl
    nlinarith [hξ, hG, hc]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum hc

end RMF
