/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FarRange
import RMF.Weighted.MesoscopicFamily
import RMF.Weighted.ReductionChoice
import RMF.Weighted.ReductionChoiceExplicit
import RMF.Weighted.SmallQDescent

/-!
# `Z`, split into its four ranges

The reduction to random Euler products
(`RMF.exists_integral_rpow_weightedRademacherSum_le_reduction_explicit`) leaves one term to bound,

`Z = (log y)^{-1} ∫_ℝ ‖F_{y+1}(½+σ+it)/(σ+it)‖² dt`,

and each of the four ranges of `|t|` has its own bound:

| range | bound | file |
|---|---|---|
| `|t| ≤ w` | `RMF.exists_const_integral_rpow_centralRange_le_rademacher` | `MesoscopicFamily` |
| `w < |t| ≤ 1` | `RMF.exists_const_integral_rpow_mesoRange_le_rademacher` | `MesoscopicFamily` |
| `1 < |t| ≤ M` | `RMF.exists_const_integral_rpow_lineMidDiv_le_rademacher` | `FarRange` |
| `M < |t|` | `RMF.exists_integral_rpow_eulerProductLine_tail_le` | `LineTail` |

This file puts them together: the additive split of `∫_ℝ` over the four sets, and the
subadditivity of `u ↦ u^q` that turns `Z = Z₁+Z₂+Z₃+Z₄` into `Z^q ≤ Z₁^q+Z₂^q+Z₃^q+Z₄^q`.

## Why the split is four ways and not two

Each range is bounded by a *different* mechanism, and no two of them overlap:

* the central window is the only one where the weight `(σ²+t²)^{-1}` is large, and the only one
  where the field is comparable to its value at a real point;
* the mesoscopic range is the only one where the barrier estimate is applied at a *varying*
  offset — `D` moves with the window;
* the mid range applies it at a fixed offset and pays for the unit windows at the fixed exponent
  `2/3`, which is what keeps `∑_n (1+n²)^{-2/3}` convergent while `q` is small;
* the tail needs no chaos estimate at all: `∫_{|t|>M}(σ²+t²)^{-1}dt ≤ 2/M` and Hölder against the
  second moment suffice.

The three cut points `w`, `1`, `M` are therefore forced, not chosen: `w` by the central window's
`w·log(y+1) ≤ 2`, `1` by the unit windows, and `M` by `(M:ℝ)+1 ≤ (loglog y)²`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The four sets partition the line -/

/-- The four ranges of `|t|`, as a partition of `ℝ`. -/
lemma integral_split_four {f : ℝ → ℝ} (hf : Integrable f) {w M : ℝ} (hw1 : w ≤ 1)
    (hM : 1 ≤ M) :
    (∫ t : ℝ, f t)
      = ((∫ t in Set.Icc (-w) w, f t) + ∫ t in {t : ℝ | w < |t| ∧ |t| ≤ 1}, f t)
        + ((∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ M}, f t) + ∫ t in {t : ℝ | M < |t|}, f t) := by
  have hAbs : Measurable fun t : ℝ => |t| := (measurable_id.abs)
  have hs1 : MeasurableSet (Set.Icc (-w) w) := measurableSet_Icc
  have hs2 : MeasurableSet {t : ℝ | w < |t| ∧ |t| ≤ 1} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have hs3 : MeasurableSet {t : ℝ | 1 < |t| ∧ |t| ≤ M} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have hs4 : MeasurableSet {t : ℝ | M < |t|} := measurableSet_lt measurable_const hAbs
  -- the first two make up `|t| ≤ 1`, the last two make up `|t| > 1`
  have h12 : Set.Icc (-w) w ∪ {t : ℝ | w < |t| ∧ |t| ≤ 1} = Set.Icc (-1) 1 := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le]
    constructor
    · rintro (h | h)
      · linarith
      · exact h.2
    · intro h
      by_cases hle : |t| ≤ w
      · exact Or.inl hle
      · exact Or.inr ⟨not_le.1 hle, h⟩
  have hd12 : Disjoint (Set.Icc (-w) w) {t : ℝ | w < |t| ∧ |t| ≤ 1} := by
    rw [Set.disjoint_left]
    rintro t ht ht'
    rw [Set.mem_Icc, ← abs_le] at ht
    exact absurd ht'.1 (not_lt.2 ht)
  have h34 : {t : ℝ | 1 < |t| ∧ |t| ≤ M} ∪ {t : ℝ | M < |t|} = {t : ℝ | 1 < |t|} := by
    ext t
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hle : |t| ≤ M
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr (not_le.1 hle)
  have hd34 : Disjoint {t : ℝ | 1 < |t| ∧ |t| ≤ M} {t : ℝ | M < |t|} := by
    rw [Set.disjoint_left]
    rintro t ht ht'
    exact absurd ht'  (not_lt.2 ht.2)
  have hcomp : Set.Icc (-1 : ℝ) 1 = {t : ℝ | 1 < |t|}ᶜ := by
    ext t
    simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, ← abs_le]
  rw [← setIntegral_union hd12 hs2 (hf.integrableOn) (hf.integrableOn), h12,
    ← setIntegral_union hd34 hs4 (hf.integrableOn) (hf.integrableOn), h34, hcomp, add_comm,
    integral_add_compl (measurableSet_lt measurable_const hAbs) hf]

/-! ### Subadditivity over the four -/

/-- `(a+b+c+d)^q ≤ a^q+b^q+c^q+d^q` for `0 ≤ q ≤ 1`, in the association the split produces. -/
lemma rpow_add_four_le {a b c d q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((a + b) + (c + d)) ^ q ≤ a ^ q + b ^ q + c ^ q + d ^ q := by
  have h1 := Real.rpow_add_le_add_rpow (by linarith : (0 : ℝ) ≤ a + b)
    (by linarith : (0 : ℝ) ≤ c + d) hq0 hq1
  have h2 := Real.rpow_add_le_add_rpow ha hb hq0 hq1
  have h3 := Real.rpow_add_le_add_rpow hc hd hq0 hq1
  linarith

/-! ### Every range of `Z` has an integrable `q`-th power

Lean's convention sends a non-integrable Bochner integral to `0`, so a bound on `∫ ω, Z_i^q` is
worth nothing until `Z_i^q` is known to be integrable — the point `RMF/Weighted/EulerLine.lean`
makes for the whole line.  For a *sub*range there is nothing new to prove: the integrand is
nonnegative, so `Z_i ≤ Z` pointwise, and
`RMF.integrable_rpow_eulerProductLine` dominates.  All that is needed is measurability in `ω`,
which is Tonelli's half — joint measurability plus
`MeasureTheory.StronglyMeasurable.integral_prod_right'` at `volume.restrict S`. -/

/-- The **decoupled** line integrand is jointly measurable.  `RMF.lineDivSqOf`'s own
`RMF.stronglyMeasurable_lineDivSqOf_sqfree` has the numerator's abscissa and the denominator
coupled; the `Z` of the reduction does not. -/
lemma stronglyMeasurable_lineDiv_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (σ : ℝ) (N : ℕ) :
    StronglyMeasurable fun z : Ω × ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1
        / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 := by
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hcongr : (fun z : Ω × ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1
        / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2)
      = fun z : Ω × ℝ =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (((1 / 2 + σ : ℝ) : ℂ) + (z.2 : ℂ) * Complex.I) z.1
          / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 :=
    funext fun z => by rw [hsline z.2]
  rw [hcongr]
  refine (((measurable_randomEulerProduct_sqfree_uncurry
    (fun p hp => hX.measurable p hp) (1 / 2 + σ) N).div ?_).norm.pow_const 2).stronglyMeasurable
  exact ((Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I).const_add _

/-- **`Z` restricted to any measurable range has an integrable `q`-th power.** -/
lemma integrable_rpow_setIntegral_lineDiv {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {q : ℝ} (hq0 : 0 ≤ q) {S : Set ℝ} (hS : MeasurableSet S) :
    Integrable (fun ω => ((Real.log y)⁻¹ * ∫ t in S,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ := by
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hmeas : StronglyMeasurable fun ω : Ω => ∫ t in S,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict S)
      (stronglyMeasurable_lineDiv_sqfree hX σ (y + 1))
  refine Integrable.mono' (integrable_rpow_eulerProductLine hX y hσ hq0)
    ((Real.continuous_rpow_const hq0).measurable.comp
      (measurable_const.mul hmeas.measurable)).aestronglyMeasurable ?_
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw (y + 1)] with ω hω
  have hint : Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    have hcongr : (fun t : ℝ =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        = fun t : ℝ =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
      funext fun t => by rw [hsline t]
    rw [hcongr]
    exact integrable_line_div_sq (by linarith) hσ hω
  have hSle : (∫ t in S,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => by positivity)
  have hS0 : (0 : ℝ) ≤ ∫ t in S,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    setIntegral_nonneg hS fun t _ => by positivity
  have hL0 : (0 : ℝ) ≤ (Real.log y)⁻¹ := by
    rcases Nat.eq_zero_or_pos y with h | h
    · simp [h]
    · exact inv_nonneg.2 (Real.log_nonneg (by exact_mod_cast h))
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg hL0 hS0) _)]
  exact Real.rpow_le_rpow (mul_nonneg hL0 hS0) (mul_le_mul_of_nonneg_left hSle hL0) hq0

/-- Adding two bounded integrals, with the functions as variables so that the `integral_add`
inside matches syntactically — `Integrable.add` produces `f + g` as a `Pi.add`, which no
`rewrite` will see through. -/
lemma integral_add_le {μ : Measure Ω} {f g : Ω → ℝ} {a b : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (ha : (∫ ω, f ω ∂μ) ≤ a) (hb : (∫ ω, g ω ∂μ) ≤ b) :
    (∫ ω, (f ω + g ω) ∂μ) ≤ a + b := by
  rw [integral_add hf hg]
  exact add_le_add ha hb

/-! ### The split, with the four range bounds as inputs

The partition of the line, the subadditivity of `u ↦ u^q` and the integrability each piece needs
do not care *which* bound each range carries.  Keeping them apart is what lets the mesoscopic
range be swapped between its crude and its geometric bound without redoing the assembly. -/

/-- **`Z` from its four ranges.** -/
lemma integral_rpow_lineDiv_le_of_ranges {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q : ℝ} {y J M : ℕ} {B₁ B₂ B₃ B₄ : ℝ}
    (hy2 : 2 ≤ y) (hσ0 : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hM1 : 1 ≤ M)
    (hb1 : (∫ ω, ((Real.log y)⁻¹
        * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₁)
    (hb2 : (∫ ω, ((Real.log y)⁻¹
        * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₂)
    (hb3 : (∫ ω, ((Real.log y)⁻¹
        * ∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₃)
    (hb4 : (∫ ω, ((Real.log y)⁻¹
        * ∫ t in {t : ℝ | (M : ℝ) < |t|},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν) ≤ B₄)
    :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ B₁ + B₂ + B₃ + B₄ := by
  haveI := hY.isProbabilityMeasure
  have hw1 : Real.exp (-(J : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg J))
  -- the four ranges
  have hs1 : MeasurableSet (Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ)))) :=
    measurableSet_Icc
  have hAbs : Measurable fun t : ℝ => |t| := measurable_id.abs
  have hs2 : MeasurableSet {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have hs3 : MeasurableSet {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have hs4 : MeasurableSet {t : ℝ | (M : ℝ) < |t|} := measurableSet_lt measurable_const hAbs
  obtain ⟨G, hG⟩ : ∃ G : Ω → ℝ → ℝ, ∀ (ω : Ω) (t : ℝ), G ω t =
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, fun _ _ => rfl⟩
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hGeq : ∀ ω : Ω, G ω = fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    fun ω => funext fun t => by rw [hG ω t, hsline t]
  simp only [← hG]
  have hG0 : ∀ (ω : Ω) (t : ℝ), (0 : ℝ) ≤ G ω t := fun ω t => by rw [hG]; positivity
  have hL0 : (0 : ℝ) ≤ (Real.log y)⁻¹ :=
    inv_nonneg.2 (Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hy2))
  -- the split, a.e. in `ω`
  have hsplit : ∀ᵐ ω ∂ν, (∫ t : ℝ, G ω t)
      = ((∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))), G ω t)
          + ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1}, G ω t)
        + ((∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)}, G ω t)
          + ∫ t in {t : ℝ | (M : ℝ) < |t|}, G ω t) := by
    filter_upwards [ae_forall_norm_le_one hY norm_le_one_rademacherLaw (y + 1)] with ω hω
    refine integral_split_four ?_ hw1 (by exact_mod_cast hM1)
    rw [hGeq ω]
    exact integrable_line_div_sq (by linarith) hσ0 hω
  -- the pointwise four-term bound
  have hpt : ∀ᵐ ω ∂ν, ((Real.log y)⁻¹ * ∫ t : ℝ, G ω t) ^ q
      ≤ ((Real.log y)⁻¹ * ∫ t in Set.Icc (-Real.exp (-(J : ℝ))) (Real.exp (-(J : ℝ))), G ω t) ^ q
        + ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1}, G ω t) ^ q
        + ((Real.log y)⁻¹ * ∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)}, G ω t) ^ q
        + ((Real.log y)⁻¹ * ∫ t in {t : ℝ | (M : ℝ) < |t|}, G ω t) ^ q := by
    filter_upwards [hsplit] with ω hω
    rw [hω, mul_add, mul_add, mul_add]
    exact rpow_add_four_le (mul_nonneg hL0 (setIntegral_nonneg hs1 fun t _ => hG0 ω t))
      (mul_nonneg hL0 (setIntegral_nonneg hs2 fun t _ => hG0 ω t))
      (mul_nonneg hL0 (setIntegral_nonneg hs3 fun t _ => hG0 ω t))
      (mul_nonneg hL0 (setIntegral_nonneg hs4 fun t _ => hG0 ω t)) hq0.le hq1
  -- integrability of the four pieces
  have hI1 := integrable_rpow_setIntegral_lineDiv hY y hσ0 hq0.le hs1
  have hI2 := integrable_rpow_setIntegral_lineDiv hY y hσ0 hq0.le hs2
  have hI3 := integrable_rpow_setIntegral_lineDiv hY y hσ0 hq0.le hs3
  have hI4 := integrable_rpow_setIntegral_lineDiv hY y hσ0 hq0.le hs4
  simp only [← hG] at hI1 hI2 hI3 hI4
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg
      (mul_nonneg hL0 (integral_nonneg fun t => hG0 ω t)) _)
    (((hI1.add hI2).add hI3).add hI4) hpt) ?_
  simp only [Pi.add_apply]
  simp only [← hG] at hb1 hb2 hb3 hb4
  exact integral_add_le ((hI1.add hI2).add hI3) hI4
    (integral_add_le (hI1.add hI2) hI3 (integral_add_le hI1 hI2 hb1 hb2) hb3) hb4

/-! ### The four ranges, assembled

The cut points enter as hypotheses, one per range: `e^{-J}·log(y+1) ≤ 2` is the central window's,
`J ≤ log(log y/2)+1` is the block family's, and `M+1 ≤ (loglog y)²` is the mid range's.  Nothing
here chooses them; that is the next step's arithmetic. -/

/-- **`Z`, bounded by its four ranges.** -/
theorem exists_const_integral_rpow_lineDiv_le_rademacher :
    ∃ (D₀ : ℕ) (y₀ A₁ A₂ A₃ A₄ : ℝ), 0 < A₁ ∧ 0 < A₂ ∧ 0 < A₃ ∧ 0 < A₄ ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y J M : ℕ),
          y₀ ≤ (y : ℝ) → 2 ≤ y → 0 < σ → σ * Real.log y ≤ 1 → 0 < q → q ≤ 1 / 2 →
          1 ≤ J → (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1 →
          Real.exp (-(J : ℝ)) * Real.log ((y : ℝ) + 1) ≤ 2 →
          1 ≤ M → ((M : ℝ) + 1) ≤ Real.log (Real.log y) ^ 2 →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A₁ * ((σ * Real.log y)⁻¹) ^ q * (Real.log y) ^ (q * (2 * q - 1))
                + A₂ * ((J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q))
                + (A₃ * (1 + (1 - 2 / 3)
                    * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ))
                    ^ (3 * q / 2)
                + (A₄ / (M : ℝ)) ^ q := by
  have h10 : (10 : ℝ) * 1 ≤ Real.exp ((3 : ℕ) : ℝ) := by
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : Real.exp ((3 : ℕ) : ℝ) = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    have h2 : (2.7 : ℝ) * 2.7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    rw [h3]
    nlinarith
  obtain ⟨A₁, hA₁, HC⟩ := exists_const_integral_rpow_centralRange_le_rademacher (Ω := Ω)
  obtain ⟨y₂, A₂, hA₂, HM⟩ := exists_const_integral_rpow_mesoRange_le_rademacher (Ω := Ω)
  obtain ⟨D₀, y₃, A₃, hA₃, HF⟩ :=
    exists_const_integral_rpow_lineMidDiv_le_rademacher (Ω := Ω) 1 zero_le_one 3 h10
  obtain ⟨A₄, hA₄, HT⟩ := exists_integral_rpow_eulerProductLine_tail_le
  refine ⟨D₀, max y₂ y₃, A₁, A₂, A₃, A₄, hA₁, hA₂, hA₃, hA₄, ?_⟩
  intro Y ν hY σ q y J M hy hy2 hσ0 hσy hq0 hq2 hJ1 hJle hJw hM1 hM
  have hy₂ : y₂ ≤ (y : ℝ) := le_trans (le_max_left _ _) hy
  have hy₃ : y₃ ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hw0 : (0 : ℝ) < Real.exp (-(J : ℝ)) := Real.exp_pos _
  have hb1 := HC Y ν hY σ q (Real.exp (-(J : ℝ))) y hy2 hσ0 hσy hw0 hJw hq0.le (by linarith)
  have hb2 := HM Y ν hY σ q y J hy₂ hσ0 hσy hq0 hq2 hJ1 hJle
  have hb3 := HF Y ν hY (y : ℝ) σ 1 q M hy₃ hσ0.le zero_le_one le_rfl
    (by rw [abs_of_pos hσ0]; exact hσy) hq0.le (by linarith) hM
  rw [hfloor] at hb3
  have hb4 := HT Ω Y ν hY q hq0 (by linarith) y hy2 σ (M : ℝ) hσ0 hM0
  exact integral_rpow_lineDiv_le_of_ranges hY hy2 hσ0 hq0 (by linarith) hM1 hb1 hb2 hb3 hb4

/-! ### The four ranges against one target

The shape the reduction wants is `J·(1+(1-q)√J)^{-q}` — the mesoscopic range's own, since the
window count `J` it pays for subadditivity dominates everything else.  The other three are
compared to it through the crude lower bound

`J·(1+(1-q)√J)^{-q} ≥ J^{3/4}/2`   (`RMF.target_ge_rpow`),

which for `q ≤ 1/2` loses nothing that matters here.

**What this discards.**  The mid range `1 < |t| ≤ M` carries a barrier saving
`(1+√(n/4)/3)^{-q}` of its own, and comparing it to the target through `J^{3/4}` throws that
saving away, at no cost here since `Z_m`'s factor `J` is larger.  Against the sharp target
`min{Λ, 1+(q(1-2q))^{-1}}·Λ^{-q/2}` the saving is kept (`RMF.mid_le_target`). -/

/-- **The target dominates `J^{3/4}/2`.**  `1+(1-q)√J ≤ 2√J` and `2^{-q}J^{-q/2} ≥ J^{-1/4}/2`. -/
lemma target_ge_rpow {q L : ℝ} (hL1 : 1 ≤ L) (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2) :
    L ^ (3 / 4 : ℝ) / 2 ≤ L * (1 + (1 - q) * Real.sqrt L) ^ (-q) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hb0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt L := by nlinarith
  have hb1 : 1 + (1 - q) * Real.sqrt L ≤ 2 * Real.sqrt L := by nlinarith
  -- `(1+(1-q)√L)^{-q} ≥ (2√L)^{-q}`
  have h1 : (2 * Real.sqrt L) ^ (-q) ≤ (1 + (1 - q) * Real.sqrt L) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hb0 hb1 (by linarith)
  -- `(2√L)^{-q} = 2^{-q}·L^{-q/2}`
  have h2 : (2 * Real.sqrt L) ^ (-q) = (2 : ℝ) ^ (-q) * L ^ (-q / 2) := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity)]
    congr 2
    ring
  have h3 : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-q) := by
    have h : (2 : ℝ) ^ (-q) ≥ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [show ((2 : ℝ) ^ (-1 : ℝ)) = 1 / 2 by
      rw [Real.rpow_neg_one]; norm_num] at h
    linarith
  have h4 : L ^ (-(1 : ℝ) / 4) ≤ L ^ (-q / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  -- `L·L^{-1/4} = L^{3/4}`
  have h5 : L * L ^ (-(1 : ℝ) / 4) = L ^ (3 / 4 : ℝ) := by
    have h : L ^ (1 : ℝ) * L ^ (-(1 : ℝ) / 4) = L ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hL0]
      norm_num
    rwa [Real.rpow_one] at h
  have hq0' : (0 : ℝ) ≤ L ^ (-q / 2) := Real.rpow_nonneg hL0.le _
  have hstep : (1 : ℝ) / 2 * L ^ (-(1 : ℝ) / 4) ≤ (2 * Real.sqrt L) ^ (-q) := by
    rw [h2]
    nlinarith [Real.rpow_nonneg hL0.le (-(1 : ℝ) / 4), h3, h4]
  calc L ^ (3 / 4 : ℝ) / 2 = L * (1 / 2 * L ^ (-(1 : ℝ) / 4)) := by
        rw [← h5]; ring
    _ ≤ L * (2 * Real.sqrt L) ^ (-q) := by
        exact mul_le_mul_of_nonneg_left hstep hL0.le
    _ ≤ L * (1 + (1 - q) * Real.sqrt L) ^ (-q) := mul_le_mul_of_nonneg_left h1 hL0.le

/-- Anything at most `K·L^{3/4}` is at most `2K` times the target. -/
lemma le_target_of_le_rpow {q u K L : ℝ} (hL1 : 1 ≤ L) (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2)
    (hK : 0 ≤ K) (hu : u ≤ K * L ^ (3 / 4 : ℝ)) :
    u ≤ 2 * K * (L * (1 + (1 - q) * Real.sqrt L) ^ (-q)) := by
  refine hu.trans ?_
  have h2 := mul_le_mul_of_nonneg_left (target_ge_rpow hL1 hq0 hq2)
    (by linarith : (0 : ℝ) ≤ 2 * K)
  calc K * L ^ (3 / 4 : ℝ) = 2 * K * (L ^ (3 / 4 : ℝ) / 2) := by ring
    _ ≤ 2 * K * (L * (1 + (1 - q) * Real.sqrt L) ^ (-q)) := h2

/-- **`Z`, at one shape.** -/
theorem exists_const_integral_rpow_lineDiv_le_target_rademacher :
    ∃ (y₀ K : ℝ), 0 < K ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y J M : ℕ),
          y₀ ≤ (y : ℝ) → 2 ≤ y → 1 ≤ Real.log y → 0 < σ → σ * Real.log y ≤ 1 →
          0 < q → q ≤ 1 / 2 →
          1 ≤ J → (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1 →
          Real.exp (-(J : ℝ)) * Real.log ((y : ℝ) + 1) ≤ 2 →
          1 ≤ M → ((M : ℝ) + 1) ≤ Real.log (Real.log y) ^ 2 →
          (σ * Real.log y)⁻¹ ≤ (J : ℝ) ^ (3 / 2 : ℝ) →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ K * ((J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q)) := by
  obtain ⟨D₀, y₀, A₁, A₂, A₃, A₄, hA₁, hA₂, hA₃, hA₄, H⟩ :=
    exists_const_integral_rpow_lineDiv_le_rademacher (Ω := Ω)
  refine ⟨y₀, 2 * A₁ + A₂ + 2 * max 1 A₃ + 2 * max 1 A₄, by positivity, ?_⟩
  intro Y ν hY σ q y J M hy hy2 hlogy hσ0 hσy hq0 hq2 hJ1 hJle hJw hM1 hM hσJ
  have hJ1R : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hJ34 : (1 : ℝ) ≤ (J : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hJ1R (by norm_num)
  have hT0 : (0 : ℝ) ≤ (J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (by nlinarith [Real.sqrt_nonneg (J : ℝ)]) _)
  -- (1) the central window
  have hσ1 : (1 : ℝ) ≤ (σ * Real.log y)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    simpa using hσy
  have hb1 : A₁ * ((σ * Real.log y)⁻¹) ^ q * (Real.log y) ^ (q * (2 * q - 1))
      ≤ A₁ * (J : ℝ) ^ (3 / 4 : ℝ) := by
    have hL1 : (Real.log y) ^ (q * (2 * q - 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlogy (by nlinarith)
    have h1 : ((σ * Real.log y)⁻¹) ^ q ≤ ((J : ℝ) ^ (3 / 2 : ℝ)) ^ q :=
      Real.rpow_le_rpow (by linarith) hσJ hq0.le
    have h2 : ((J : ℝ) ^ (3 / 2 : ℝ)) ^ q = (J : ℝ) ^ (3 / 2 * q) :=
      (Real.rpow_mul (by linarith) _ _).symm
    have h3 : (J : ℝ) ^ (3 / 2 * q) ≤ (J : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hJ1R (by linarith)
    have h4 : ((σ * Real.log y)⁻¹) ^ q ≤ (J : ℝ) ^ (3 / 4 : ℝ) := by
      rw [h2] at h1
      linarith
    have h5 : (0 : ℝ) ≤ ((σ * Real.log y)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
    calc A₁ * ((σ * Real.log y)⁻¹) ^ q * (Real.log y) ^ (q * (2 * q - 1))
        ≤ A₁ * ((σ * Real.log y)⁻¹) ^ q * 1 :=
          mul_le_mul_of_nonneg_left hL1 (mul_nonneg hA₁.le h5)
      _ = A₁ * ((σ * Real.log y)⁻¹) ^ q := mul_one _
      _ ≤ A₁ * (J : ℝ) ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left h4 hA₁.le
  -- (3) the mid range, and (4) the tail
  have hb3 : (A₃ * (1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2)
      ≤ max 1 A₃ * (J : ℝ) ^ (3 / 4 : ℝ) := by
    have hs : (0 : ℝ) ≤ Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ) :=
      Real.sqrt_nonneg _
    have hbase : (1 + (1 - 2 / 3)
        * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hb0 : (0 : ℝ) ≤ (1 + (1 - 2 / 3)
        * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    have hmul : A₃ * (1 + (1 - 2 / 3)
        * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ) ≤ A₃ := by
      nlinarith [hA₃.le]
    have hstep := rpow_le_max_one (a := A₃ * (1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ))
      (q := 3 * q / 2) (by positivity) (by linarith) (by linarith)
    have hmax : max 1 (A₃ * (1 + (1 - 2 / 3)
        * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ))
        ≤ max 1 A₃ := max_le_max le_rfl hmul
    nlinarith [hstep, hmax, le_max_left (1 : ℝ) A₃]
  have hb4 : (A₄ / (M : ℝ)) ^ q ≤ max 1 A₄ * (J : ℝ) ^ (3 / 4 : ℝ) := by
    have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    have hdiv : A₄ / (M : ℝ) ≤ A₄ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hA₄.le]
    have hstep := rpow_le_max_one (a := A₄ / (M : ℝ)) (q := q) (by positivity) hq0.le
      (by linarith)
    have hmax : max 1 (A₄ / (M : ℝ)) ≤ max 1 A₄ := max_le_max le_rfl hdiv
    nlinarith [hstep, hmax, le_max_left (1 : ℝ) A₄]
  -- assemble
  refine le_trans (H Y ν hY σ q y J M hy hy2 hσ0 hσy hq0 hq2 hJ1 hJle hJw hM1 hM) ?_
  clear H
  have g1 := le_target_of_le_rpow hJ1R hq0.le hq2 hA₁.le hb1
  have g3 := le_target_of_le_rpow (q := q) hJ1R hq0.le hq2
    (le_trans zero_le_one (le_max_left (1 : ℝ) A₃)) hb3
  have g4 := le_target_of_le_rpow (q := q) hJ1R hq0.le hq2
    (le_trans zero_le_one (le_max_left (1 : ℝ) A₄)) hb4
  clear hb1 hb3 hb4 hM hJle hJw hσJ hσy
  linarith [g1, g3, g4]

/-! ### The window for `J` is non-empty

Two conditions pin the boundary between the central and the mesoscopic range:

* `e^{-J}·log(y+1) ≤ 2`, so that the central window reaches `e^{-J}`;
* `J ≤ log(log y − log 2) + 1`, so that the bottom block's split point `w_1 + 1` stays `≤ y`.

They ask for an integer in `[log(log(y+1)/2), log(log y − log 2) + 1]`.  That interval is longer
than `1`, and `J = ⌈log(log(y+1)/2)⌉` sits in it. -/

/-- **An admissible `J` exists.** -/
lemma exists_mesoRange_index {y : ℝ} (hy : 8 ≤ y) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.exp (-(J : ℝ)) * Real.log (y + 1) ≤ 2
      ∧ (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1
      ∧ Real.log (Real.log y / 2) ≤ (J : ℝ) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  -- `log(y+1) > 2`, since `y + 1 ≥ 9 > e²`
  have he2 : Real.exp 2 < 9 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [h]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hL1 : (2 : ℝ) < Real.log (y + 1) := by
    have h := Real.log_lt_log (Real.exp_pos 2) (lt_of_lt_of_le he2 (by linarith : (9 : ℝ) ≤ y + 1))
    rwa [Real.log_exp] at h
  have hA0 : (0 : ℝ) < Real.log (y + 1) / 2 := by linarith
  have hA1 : (1 : ℝ) < Real.log (y + 1) / 2 := by linarith
  have hpos : (0 : ℝ) < Real.log (Real.log (y + 1) / 2) := Real.log_pos hA1
  refine ⟨⌈Real.log (Real.log (y + 1) / 2)⌉₊, Nat.ceil_pos.2 hpos, ?_, ?_, ?_⟩
  · -- the central window reaches `e^{-J}`
    have h1 : Real.log (Real.log (y + 1) / 2) ≤ (⌈Real.log (Real.log (y + 1) / 2)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : Real.exp (-(⌈Real.log (Real.log (y + 1) / 2)⌉₊ : ℝ))
        ≤ Real.exp (-Real.log (Real.log (y + 1) / 2)) := Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-Real.log (Real.log (y + 1) / 2)) = (Real.log (y + 1) / 2)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hA0]
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ Real.log (y + 1))
    refine h4.trans (le_of_eq ?_)
    field_simp
  · -- and the split point stays inside the product
    have hlt : (⌈Real.log (Real.log (y + 1) / 2)⌉₊ : ℝ) < Real.log (Real.log (y + 1) / 2) + 1 :=
      Nat.ceil_lt_add_one hpos.le
    have hsq : y + 1 ≤ (y / 2) ^ 2 := by nlinarith
    have hlog : Real.log (y + 1) ≤ 2 * (Real.log y - Real.log 2) := by
      have h := Real.log_le_log (by linarith : (0 : ℝ) < y + 1) hsq
      rwa [Real.log_pow, Real.log_div hy0.ne' (by norm_num)] at h
    have hmono : Real.log (Real.log (y + 1) / 2) ≤ Real.log (Real.log y - Real.log 2) :=
      Real.log_le_log hA0 (by linarith)
    linarith
  · -- and it is not much larger than `log log y`, which is what pins `σ`
    have hmon : Real.log y ≤ Real.log (y + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hly : (0 : ℝ) < Real.log y / 2 := by
      have := Real.log_pos (by linarith : (1 : ℝ) < y)
      linarith
    have hmono : Real.log (Real.log y / 2) ≤ Real.log (Real.log (y + 1) / 2) :=
      Real.log_le_log hly (by linarith)
    exact hmono.trans (Nat.le_ceil _)

/-! ### The tail index, and the parameters at the reduction's own `y` and `σ`

`M` is the only free parameter left, and the only condition on it is `M + 1 ≤ (loglog y)²`, so
`M = ⌊(loglog y)²⌋ - 1` does.  What takes work is the last hypothesis of
`RMF.exists_const_integral_rpow_lineDiv_le_target_rademacher`,

`(σ·log y)^{-1} ≤ J^{3/2}`,

which at `σ = 1/log x` and `y = ⌊x^{1/(4 loglog x)}⌋` says `log x/log y ≤ J^{3/2}`.  The left side
is at most `8·loglog x` (`RMF.eventually_log_reductionY_ge`) and `J ≥ loglog y - log 2` is at
least `loglog x - log(16·loglog x)`, so with `log u ≤ 2√u` twice the condition reduces to
`√(loglog x) ≥ 16`, i.e. `loglog x ≥ 256`. -/

/-- **An admissible `M` exists.** -/
lemma exists_mesoTail_index {L : ℝ} (hL : 2 ≤ L) :
    ∃ M : ℕ, 1 ≤ M ∧ ((M : ℝ) + 1) ≤ L ^ 2 ∧ L ^ 2 / 2 ≤ (M : ℝ) := by
  have hL4 : (4 : ℝ) ≤ L ^ 2 := by nlinarith
  have hfl : (4 : ℕ) ≤ ⌊L ^ 2⌋₊ := Nat.le_floor (by exact_mod_cast hL4)
  refine ⟨⌊L ^ 2⌋₊ - 1, by omega, ?_, ?_⟩
  · have hcast : ((⌊L ^ 2⌋₊ - 1 : ℕ) : ℝ) + 1 = ((⌊L ^ 2⌋₊ : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ ⌊L ^ 2⌋₊ := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    exact Nat.floor_le (by positivity)
  · have hcast : ((⌊L ^ 2⌋₊ - 1 : ℕ) : ℝ) = ((⌊L ^ 2⌋₊ : ℕ) : ℝ) - 1 := by
      have : (1 : ℕ) ≤ ⌊L ^ 2⌋₊ := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hlo : L ^ 2 - 1 ≤ ((⌊L ^ 2⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (L ^ 2)
      linarith
    rw [hcast]
    linarith

set_option maxHeartbeats 1000000 in
-- an eighteen-fold conjunction: the elaborator spends its budget on the anonymous constructor,
-- not on any one component
/-- **All the parameters, at the reduction's own `y` and `σ`.**

The one with content is `(σ·log y)^{-1} ≤ J^{3/2}`: `(σ·log y)^{-1} = log x/log y ≤ 8·loglog x`
(`RMF.eventually_log_reductionY_ge`), while `J ≥ loglog y - log 2 ≥ loglog x - log(16·loglog x)`,
and `log u ≤ 2√u` turns `log(16Λ) ≤ Λ/2` into `√Λ ≥ 16`.  So `J ≥ Λ/2 ≥ 256`, `√J ≥ 16`, and
`J^{3/2} = J·√J ≥ 16J ≥ 8Λ`.  The proof takes `loglog x ≥ 512 + 18·D₀`. -/
theorem eventually_exists_mesoParams (D₀ : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∃ J M : ℕ,
      2 ≤ reductionY x ∧ 1 ≤ Real.log (reductionY x) ∧
      0 < reductionSigma x ∧ reductionSigma x * Real.log (reductionY x) ≤ 1 ∧
      1 ≤ J ∧ (J : ℝ) ≤ Real.log (Real.log (reductionY x) - Real.log 2) + 1 ∧
      Real.exp (-(J : ℝ)) * Real.log (((reductionY x : ℕ) : ℝ) + 1) ≤ 2 ∧
      1 ≤ M ∧ ((M : ℝ) + 1) ≤ Real.log (Real.log (reductionY x)) ^ 2 ∧
      (reductionSigma x * Real.log (reductionY x))⁻¹ ≤ (J : ℝ) ^ (3 / 2 : ℝ) ∧
      Real.log (Real.log x) / 2 ≤ (J : ℝ) ∧ (J : ℝ) ≤ Real.log (Real.log x) + 1 ∧
      8 * Real.log (Real.log x) ≤ Real.log x ∧
      Real.log (Real.log x) / 2 ≤ Real.log (Real.log (reductionY x)) ∧
      (reductionSigma x * Real.log (reductionY x))⁻¹ ≤ 8 * Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ (M : ℝ) ∧
      Real.log (Real.log x)
        ≤ 9 * ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp (512 + 18 * (D₀ : ℝ)))),
    Filter.eventually_ge_atTop (Real.exp 16384), eventually_log_reductionY_ge,
    eventually_log_reductionY_le, tendsto_reductionY_atTop.eventually_ge_atTop 2000]
    with x hx hx16 hylo hyhi hy2000
  obtain ⟨hx1, hL, hLL⟩ := reduction_log_bounds hx16
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hΛD : (512 : ℝ) + 18 * (D₀ : ℝ) ≤ Λ := by
    have h1 : Real.exp (512 + 18 * (D₀ : ℝ)) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp (512 + 18 * (D₀ : ℝ)))) hx
      rwa [Real.log_exp] at h
    have h2 := Real.log_le_log (Real.exp_pos (512 + 18 * (D₀ : ℝ))) h1
    rwa [Real.log_exp] at h2
  have hΛ : (512 : ℝ) ≤ Λ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  -- the parameter `y`
  set y : ℕ := reductionY x with hydef
  have hy2000R : (2000 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2000
  have hy2 : 2 ≤ y := by exact_mod_cast (by linarith : (2 : ℝ) ≤ (y : ℝ))
  have hlogy1 : (1 : ℝ) < Real.log y := one_lt_log_of_three_le (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log y := by linarith
  -- `σ`, and `σ·log y ≤ 1`
  have hσ : reductionSigma x = 1 / Real.log x := rfl
  have hσ0 : (0 : ℝ) < reductionSigma x := by rw [hσ]; positivity
  have hyx : Real.log y ≤ Real.log x := by
    have h : Real.log x / (4 * Λ) ≤ Real.log x := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith [hyhi]
  have hσy : reductionSigma x * Real.log y ≤ 1 := by
    rw [hσ, div_mul_eq_mul_div, one_mul, div_le_one hL0]
    exact hyx
  -- `log(16Λ) ≤ 8√Λ ≤ Λ/2`, which is where `Λ ≥ 512` is spent
  have hs : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt hΛ0.le
  have hs16 : (16 : ℝ) ≤ Real.sqrt Λ := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrt16 : Real.sqrt (16 * Λ) = 4 * Real.sqrt Λ := by
    rw [Real.sqrt_mul (by norm_num) Λ,
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hlog16 : Real.log (16 * Λ) ≤ Λ / 2 := by
    have h := log_le_two_mul_sqrt (by positivity : (0 : ℝ) < 16 * Λ)
    rw [hsqrt16] at h
    nlinarith [hs, hs16]
  have hsplit16 : Real.log (16 * Λ) = Real.log (8 * Λ) + Real.log 2 := by
    rw [show (16 : ℝ) * Λ = 2 * (8 * Λ) by ring, Real.log_mul (by norm_num) (by positivity)]
    ring
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `loglog y ≥ Λ - log(8Λ) ≥ Λ/2 ≥ 256`
  have hloglogy : Λ - Real.log (8 * Λ) ≤ Real.log (Real.log y) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < Real.log x / (8 * Λ)) hylo
    rw [Real.log_div hL0.ne' (by positivity)] at h
    linarith
  have hLL2 : (2 : ℝ) ≤ Real.log (Real.log y) := by linarith
  -- `J` and `M`
  obtain ⟨J, hJ1, hJw, hJle, hJlb⟩ := exists_mesoRange_index (by linarith : (8 : ℝ) ≤ (y : ℝ))
  obtain ⟨M, hM1, hM, hMlo⟩ := exists_mesoTail_index hLL2
  -- `8Λ ≤ log x`: `Λ ≤ 2√(log x)` and `√(log x) ≥ 16`
  have hsL : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hL0.le
  have hsL16 : (16 : ℝ) ≤ Real.sqrt (Real.log x) := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h8L : 8 * Λ ≤ Real.log x := by
    have h := log_le_two_mul_sqrt hL0
    rw [← hΛdef] at h
    nlinarith [hsL, hsL16]
  -- `J ≤ Λ + 1`, from `log y ≤ log x`
  have hJhi : (J : ℝ) ≤ Λ + 1 := by
    refine le_trans hJle ?_
    have hlog2le : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have h1 : Real.log (Real.log y - Real.log 2) ≤ Real.log (Real.log y) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (Real.log y) ≤ Λ := Real.log_le_log hlogy0 hyx
    linarith
  have hJlb' : Λ - Real.log (16 * Λ) ≤ (J : ℝ) := by
    have hdiv : Real.log (Real.log y / 2) = Real.log (Real.log y) - Real.log 2 :=
      Real.log_div hlogy0.ne' (by norm_num)
    rw [hdiv] at hJlb
    linarith
  have hJhalf : Λ / 2 ≤ (J : ℝ) := by linarith
  have hinv : (reductionSigma x * Real.log y)⁻¹ = Real.log x / Real.log y := by
    rw [hσ, div_mul_eq_mul_div, one_mul, inv_div]
  have h8Λ : Real.log x / Real.log y ≤ 8 * Λ := by
    rw [div_le_iff₀ hlogy0]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 8 * Λ)] at hylo
    linarith
  have hLLhalf : Λ / 2 ≤ Real.log (Real.log y) := by linarith
  have hMΛ : Λ ≤ (M : ℝ) := by nlinarith [hMlo, hLLhalf, hΛ]
  have hlogy1' : (1 : ℝ) ≤ Real.log y := by linarith
  have h8Λ' : (reductionSigma x * Real.log y)⁻¹ ≤ 8 * Λ := by rw [hinv]; exact h8Λ
  have hlast : (reductionSigma x * Real.log y)⁻¹ ≤ (J : ℝ) ^ (3 / 2 : ℝ) := by
    have hJ256 : (256 : ℝ) ≤ (J : ℝ) := by linarith
    have hJ0 : (0 : ℝ) < (J : ℝ) := by linarith
    have h32 : (J : ℝ) ^ (3 / 2 : ℝ) = (J : ℝ) * Real.sqrt J := by
      have h : (J : ℝ) ^ (1 : ℝ) * (J : ℝ) ^ (1 / 2 : ℝ) = (J : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add hJ0]
        norm_num
      rw [← h, Real.rpow_one, Real.sqrt_eq_rpow]
    have hsJ : (16 : ℝ) ≤ Real.sqrt J := by
      rw [show (16 : ℝ) = Real.sqrt 256 by
        rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hJ256
    rw [hinv, h32]
    nlinarith [h8Λ, hJhalf, hsJ, hJ0]
  -- the barrier depth is comparable to `Λ`
  have hD₀y : (D₀ : ℝ) ≤ Real.log (Real.log y) := by linarith
  have hcast := cast_harperBlockCount hD₀y
  have hfl : Real.log (Real.log y) - 1 ≤ ((⌊Real.log (Real.log y)⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one (Real.log (Real.log y))]
  have hn : Λ / 2 - 1 - (D₀ : ℝ) ≤ ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  have hm4 : harperBlockCount D₀ (y : ℝ) ≤ 4 * (harperBlockCount D₀ (y : ℝ) / 4) + 3 := by omega
  have hm4R : ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ)
      ≤ 4 * ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hm4
  have hbar : Λ ≤ 9 * ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ) := by linarith
  exact ⟨J, M, hy2, hlogy1', hσ0, hσy, hJ1, hJle, hJw, hM1, hM, hlast, hJhalf, hJhi, h8L,
    hLLhalf, h8Λ', hMΛ, hbar⟩

/-! ### The upper bound, at `log log x`

`J` is within a bounded factor of `Λ = loglog x` — `Λ/2 ≤ J ≤ Λ+1` — and the target
`J·(1+(1-q)√J)^{-q}` is monotone enough in `J` that the two are interchangeable at the cost of
`4`. -/

/-- Trading `J` for `Λ` costs a factor `4`. -/
lemma target_le_of_bounds {J : ℕ} {q Λ : ℝ} (hΛ : 2 ≤ Λ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlo : Λ / 2 ≤ (J : ℝ)) (hhi : (J : ℝ) ≤ Λ + 1) :
    (J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q)
      ≤ 4 * (Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q)) := by
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  have hsΛ : (0 : ℝ) ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hq' : (0 : ℝ) ≤ 1 - q := by linarith
  have hBΛ : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by nlinarith
  have hBJ : (0 : ℝ) < 1 + (1 - q) * Real.sqrt J := by
    nlinarith [Real.sqrt_nonneg ((J : ℕ) : ℝ)]
  -- `√J ≥ √Λ/2`
  have hsJ : Real.sqrt Λ / 2 ≤ Real.sqrt J := by
    have hsq : (Real.sqrt Λ / 2) ^ 2 ≤ (J : ℝ) := by
      have h := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ Λ)
      nlinarith
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at h
  -- so `(1/2)(1+(1-q)√Λ) ≤ 1+(1-q)√J`
  have hbase : 1 / 2 * (1 + (1 - q) * Real.sqrt Λ) ≤ 1 + (1 - q) * Real.sqrt J := by
    nlinarith
  have hstep : (1 + (1 - q) * Real.sqrt J) ^ (-q)
      ≤ (1 / 2 * (1 + (1 - q) * Real.sqrt Λ)) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  have hhalf : (1 / 2 * (1 + (1 - q) * Real.sqrt Λ)) ^ (-q)
      = (1 / 2 : ℝ) ^ (-q) * (1 + (1 - q) * Real.sqrt Λ) ^ (-q) :=
    Real.mul_rpow (by norm_num) hBΛ.le
  have hpow : ((1 : ℝ) / 2) ^ (-q) ≤ 2 := by
    have h1 : ((1 : ℝ) / 2) ^ (-q) ≤ ((1 : ℝ) / 2) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    rw [show ((1 : ℝ) / 2) ^ (-(1 : ℝ)) = 2 by
      rw [Real.rpow_neg_one]; norm_num] at h1
    exact h1
  have hBq : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt Λ) ^ (-q) := Real.rpow_nonneg hBΛ.le _
  have hJq : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt J) ^ (-q) := Real.rpow_nonneg hBJ.le _
  have hfin : (1 + (1 - q) * Real.sqrt J) ^ (-q)
      ≤ 2 * (1 + (1 - q) * Real.sqrt Λ) ^ (-q) := by
    rw [hhalf] at hstep
    nlinarith [hstep, hpow, hBq]
  have hJ2 : (J : ℝ) ≤ 2 * Λ := by linarith
  nlinarith [hfin, hJ2, hJq, hBq, hJ0]

/-- **The low-moment upper bound for the weighted Rademacher sum**, in the crude form.

`E‖S(x)‖^{2q} ≪ loglog x · (1 + (1-q)√(loglog x))^{-q}` uniformly for `0 < q ≤ 1/2`.

The leading `loglog x` is the window count `J` the mesoscopic range pays for subadditivity of
`u ↦ u^q`; keeping the geometric factor in the depth sum
(`RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le`) replaces it by `min{loglog x, 1 + (q(1-2q))^{-1}}`
(`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_min`); the sharp form is
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp`, and `q > ½` is
`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_uniform_min`.  `C` and `x₀` are
independent of `x`, `q`, `X` and `μ`. -/
theorem exists_const_integral_rpow_weightedRademacherSum_le_smallQ :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (Real.log (Real.log x)
                * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)) := by
  obtain ⟨C₀, x₁, hC₀, hx₁, HR⟩ := exists_integral_rpow_weightedRademacherSum_le_reduction_explicit
  obtain ⟨yb, K, hK, HT⟩ := exists_const_integral_rpow_lineDiv_le_target_rademacher (Ω := Ω)
  obtain ⟨x₂, hev⟩ := Filter.eventually_atTop.1
    ((eventually_exists_mesoParams 0).and
      ((tendsto_reductionY_atTop.eventually_ge_atTop yb).and
        (Filter.eventually_ge_atTop (Real.exp (Real.exp 512)))))
  refine ⟨C₀ * (4 * K + 2), max x₁ x₂, by positivity, ?_⟩
  intro X μ hX x q hx hq0 hq2
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨J, M, hy2, hlogy1, hσ0, hσy, hJ1, hJle, hJw, hM1, hM, hσJ, hJlo, hJhi, h8L, -,
    -, -, -⟩, hyb, hxe⟩ := hev x hxx₂
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  have hΛ : (512 : ℝ) ≤ Λ := by
    have hL0 : (0 : ℝ) < Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 512)) hxe
      rw [Real.log_exp] at h
      linarith [Real.exp_pos (512 : ℝ)]
    have h1 : Real.exp 512 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 512)) hxe
      rwa [Real.log_exp] at h
    have h2 := Real.log_le_log (Real.exp_pos 512) h1
    rwa [Real.log_exp] at h2
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hBΛ : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by
    nlinarith [Real.sqrt_nonneg Λ]
  have hTΛ : (0 : ℝ) ≤ Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hBΛ.le _)
  -- `Z`, at the reduction's parameters
  have hZ := HT X μ hX (reductionSigma x) q (reductionY x) J M hyb hy2 hlogy1 hσ0 hσy hq0 hq2
    hJ1 hJle hJw hM1 hM hσJ
  have hZΛ : K * ((J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q))
      ≤ 4 * K * (Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q)) := by
    have h := target_le_of_bounds (Λ := Λ) (by linarith) hq0.le (by linarith) hJlo hJhi
    nlinarith [h, hK.le]
  -- the reduction's error term is at most `1`, hence at most twice the target
  have herr : (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)) ≤ 1 :=
    Real.rpow_le_one (by positivity) (by rw [div_le_one hL0]; linarith)
      (mul_nonneg hq0.le (by linarith))
  have hone : (1 : ℝ) ≤ 2 * (Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q)) := by
    have h := target_ge_rpow (L := Λ) (by linarith) hq0.le hq2
    have h34 : (1 : ℝ) ≤ Λ ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  -- assemble
  refine le_trans (HR q hq0 (by linarith) Ω X μ hX x hxx₁) ?_
  have hsum : (∫ ω, ((Real.log (reductionY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (reductionY x + 1)
            ((1 / 2 : ℂ) + ((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      + (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q))
      ≤ (4 * K + 2) * (Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q)) := by
    have h1 := le_trans hZ hZΛ
    linarith
  have hC0 : (0 : ℝ) ≤ C₀ := hC₀.le
  calc C₀ * ((∫ ω, ((Real.log (reductionY x))⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (reductionY x + 1)
              ((1 / 2 : ℂ) + ((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        + (8 * Real.log (Real.log x) / Real.log x) ^ (q * (1 - 2 * q)))
      ≤ C₀ * ((4 * K + 2) * (Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q))) :=
        mul_le_mul_of_nonneg_left hsum hC0
    _ = C₀ * (4 * K + 2) * (Λ * (1 + (1 - q) * Real.sqrt Λ) ^ (-q)) := by ring

/-! ### The four ranges against the sharp target

With the geometric factor kept, the mesoscopic range contributes `min{Λ, 1+α^{-1}}·Λ^{-q/2}` at
`Λ = log log x` and `α = q(1-2q)`, and the other three have to be measured against *that*, not
against `Λ·Λ^{-q/2}`.  Two of them are easy — the mid range and the tail are already
`O(Λ^{-q/2})`, and `min{Λ, 1+α^{-1}} ≥ 1`.  **The central window is the one that needs the
`min`.**  It is `≍ (8Λ)^q(log y)^{-α}`, which at `q = ½` is `√(8Λ)` and at no `q` is
`O(Λ^{-q/2})`; what saves it is that `Λ^{3/4}e^{-αΛ/2} ≤ min{Λ, α^{-1}}`, both branches at once,
through `u·e^{-u} ≤ 1` at `u = αΛ`. -/

/-- If `√Λ ≤ K·b`, then `b^{-q} ≤ K·Λ^{-q/2}`.  This is where `q ≤ 1` makes the barrier
denominator `Λ^{q/2}` up to an absolute constant — on `0 < q ≤ ½` the factor `(1-q)` in
`1+(1-q)√J` does nothing at all. -/
lemma rpow_neg_le_of_sqrt_le {q Λ K b : ℝ} (hΛ1 : 1 ≤ Λ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hK : 1 ≤ K) (h : Real.sqrt Λ ≤ K * b) :
    b ^ (-q) ≤ K * Λ ^ (-(q / 2)) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  have hstep : b ^ (-q) ≤ (Real.sqrt Λ / K) ^ (-q) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [div_le_iff₀ hK0]
    linarith
  have hsplit : (Real.sqrt Λ / K) ^ (-q) = Λ ^ (-(q / 2)) * K ^ q := by
    rw [Real.div_rpow hs0.le hK0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hΛ0.le,
      show (1 : ℝ) / 2 * -q = -(q / 2) from by ring, Real.rpow_neg hK0.le, div_eq_mul_inv,
      inv_inv]
  have hKq : K ^ q ≤ K := by
    calc K ^ q ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK hq1
      _ = K := Real.rpow_one _
  rw [hsplit] at hstep
  have hΛq : (0 : ℝ) ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  nlinarith [hstep, hKq, hΛq]

/-- `Λ^{3/4}·e^{-αΛ/2} ≤ Λ`. -/
lemma rpow_three_quarters_mul_exp_le_self {Λ α : ℝ} (hΛ : 1 ≤ Λ) (hα : 0 ≤ α) :
    Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)) ≤ Λ := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have h34 : Λ ^ (3 / 4 : ℝ) ≤ Λ := by
    calc Λ ^ (3 / 4 : ℝ) ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num)
      _ = Λ := Real.rpow_one _
  have hE : Real.exp (-(α * Λ / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  nlinarith [h34, hE, Real.rpow_pos_of_pos hΛ0 (3 / 4 : ℝ), Real.exp_pos (-(α * Λ / 2))]

/-- `Λ^{3/4}·e^{-αΛ/2} ≤ α^{-1}`, from `u·e^{-u/2} ≤ 2` at `u = αΛ` and `Λ^{1/4} ≥ 2`. -/
lemma rpow_three_quarters_mul_exp_le_inv {Λ α : ℝ} (hΛ : 16 ≤ Λ) (hα : 0 < α) :
    Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)) ≤ α⁻¹ := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have h34 : (0 : ℝ) < Λ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hΛ0 _
  have hE : (0 : ℝ) < Real.exp (-(α * Λ / 2)) := Real.exp_pos _
  -- `u·e^{-u/2} ≤ 2`
  have hue : (α * Λ) * Real.exp (-(α * Λ / 2)) ≤ 2 := by
    have h := Real.add_one_le_exp (α * Λ / 2)
    have hid : Real.exp (-(α * Λ / 2)) * Real.exp (α * Λ / 2) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [h, hid, hE]
  -- `Λ^{1/4} ≥ 2`, and `Λ^{3/4}·Λ^{1/4} = Λ`
  have h16 : ((16 : ℝ)) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have h14 : (2 : ℝ) ≤ Λ ^ (1 / 4 : ℝ) := by
    rw [← h16]
    exact Real.rpow_le_rpow (by norm_num) hΛ (by norm_num)
  have hsplit : Λ ^ (3 / 4 : ℝ) * Λ ^ (1 / 4 : ℝ) = Λ := by
    rw [← Real.rpow_add hΛ0, show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hkey : (α * Λ) * (Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2))) ≤ Λ := by
    have h1 : (α * Λ) * (Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)))
        = Λ ^ (3 / 4 : ℝ) * ((α * Λ) * Real.exp (-(α * Λ / 2))) := by ring
    rw [h1]
    calc Λ ^ (3 / 4 : ℝ) * ((α * Λ) * Real.exp (-(α * Λ / 2))) ≤ Λ ^ (3 / 4 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left hue h34.le
      _ ≤ Λ ^ (3 / 4 : ℝ) * Λ ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left h14 h34.le
      _ = Λ := hsplit
  have hαinv : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
  have hαX : α * (Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2))) ≤ 1 := by
    nlinarith [hkey, hΛ0]
  nlinarith [hαX, hαinv, inv_pos.2 hα, hα]

/-- **`Z_m` at `min{J, 1+α^{-1}}`**, the two depth bounds combined. -/
theorem exists_const_integral_rpow_mesoRange_le_rademacher_min :
    ∃ (y₀ A : ℝ), 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y J : ℕ),
          y₀ ≤ (y : ℝ) → 0 < σ → σ * Real.log y ≤ 1 → 0 < q → q < 1 / 2 → 1 ≤ J →
          (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1 →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-(J : ℝ)) < |t| ∧ |t| ≤ 1},
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A * (min (J : ℝ) (1 + (q * (1 - 2 * q))⁻¹)
                  * (1 + (1 - q) * Real.sqrt J) ^ (-q)) := by
  obtain ⟨y₁, A₁, hA₁, H₁⟩ := exists_const_integral_rpow_mesoRange_le_rademacher (Ω := Ω)
  obtain ⟨y₂, A₂, hA₂, H₂⟩ := exists_const_integral_rpow_mesoRange_le_rademacher_geom (Ω := Ω)
  refine ⟨max y₁ y₂, max A₁ A₂, by positivity, ?_⟩
  intro Y ν hY σ q y J hy hσ0 hσy hq0 hq2 hJ1 hJle
  have h1 := H₁ Y ν hY σ q y J (le_trans (le_max_left _ _) hy) hσ0 hσy hq0 (by linarith) hJ1 hJle
  have h2 := H₂ Y ν hY σ q y J (le_trans (le_max_right _ _) hy) hσ0 hσy hq0 hq2 hJ1 hJle
  have hF : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt J) ^ (-q) :=
    Real.rpow_nonneg (target_base_pos (by linarith)).le _
  have hJF : (0 : ℝ) ≤ (J : ℝ) * (1 + (1 - q) * Real.sqrt J) ^ (-q) :=
    mul_nonneg (Nat.cast_nonneg J) hF
  have hIF : (0 : ℝ) ≤ (1 + (q * (1 - 2 * q))⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q) := by
    have : (0 : ℝ) < q * (1 - 2 * q) := mul_pos hq0 (by linarith)
    positivity
  rcases le_total (J : ℝ) (1 + (q * (1 - 2 * q))⁻¹) with h | h
  · rw [min_eq_left h]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hJF)
  · rw [min_eq_right h]
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hIF)

/-- **`Z` from its four ranges, with the mesoscopic one sharp.**  The twin of
`RMF.exists_const_integral_rpow_lineDiv_le_rademacher` with the geometric factor kept. -/
theorem exists_const_integral_rpow_lineDiv_le_rademacher_geom :
    ∃ (D₀ : ℕ) (y₀ A₁ A₂ A₃ A₄ : ℝ), 0 < A₁ ∧ 0 < A₂ ∧ 0 < A₃ ∧ 0 < A₄ ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ q : ℝ) (y J M : ℕ),
          y₀ ≤ (y : ℝ) → 2 ≤ y → 0 < σ → σ * Real.log y ≤ 1 → 0 < q → q < 1 / 2 →
          1 ≤ J → (J : ℝ) ≤ Real.log (Real.log y - Real.log 2) + 1 →
          Real.exp (-(J : ℝ)) * Real.log ((y : ℝ) + 1) ≤ 2 →
          1 ≤ M → ((M : ℝ) + 1) ≤ Real.log (Real.log y) ^ 2 →
            (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
                    ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                  / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
              ≤ A₁ * ((σ * Real.log y)⁻¹) ^ q * (Real.log y) ^ (q * (2 * q - 1))
                + A₂ * (min (J : ℝ) (1 + (q * (1 - 2 * q))⁻¹)
                    * (1 + (1 - q) * Real.sqrt J) ^ (-q))
                + (A₃ * (1 + (1 - 2 / 3)
                    * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ))
                    ^ (3 * q / 2)
                + (A₄ / (M : ℝ)) ^ q := by
  have h10 : (10 : ℝ) * 1 ≤ Real.exp ((3 : ℕ) : ℝ) := by
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : Real.exp ((3 : ℕ) : ℝ) = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    have h2 : (2.7 : ℝ) * 2.7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    rw [h3]
    nlinarith
  obtain ⟨A₁, hA₁, HC⟩ := exists_const_integral_rpow_centralRange_le_rademacher (Ω := Ω)
  obtain ⟨y₂, A₂, hA₂, HM⟩ := exists_const_integral_rpow_mesoRange_le_rademacher_min (Ω := Ω)
  obtain ⟨D₀, y₃, A₃, hA₃, HF⟩ :=
    exists_const_integral_rpow_lineMidDiv_le_rademacher (Ω := Ω) 1 zero_le_one 3 h10
  obtain ⟨A₄, hA₄, HT⟩ := exists_integral_rpow_eulerProductLine_tail_le
  refine ⟨D₀, max y₂ y₃, A₁, A₂, A₃, A₄, hA₁, hA₂, hA₃, hA₄, ?_⟩
  intro Y ν hY σ q y J M hy hy2 hσ0 hσy hq0 hq2 hJ1 hJle hJw hM1 hM
  have hy₂ : y₂ ≤ (y : ℝ) := le_trans (le_max_left _ _) hy
  have hy₃ : y₃ ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hw0 : (0 : ℝ) < Real.exp (-(J : ℝ)) := Real.exp_pos _
  have hb1 := HC Y ν hY σ q (Real.exp (-(J : ℝ))) y hy2 hσ0 hσy hw0 hJw hq0.le (by linarith)
  have hb2 := HM Y ν hY σ q y J hy₂ hσ0 hσy hq0 hq2 hJ1 hJle
  have hb3 := HF Y ν hY (y : ℝ) σ 1 q M hy₃ hσ0.le zero_le_one le_rfl
    (by rw [abs_of_pos hσ0]; exact hσy) hq0.le (by linarith) hM
  rw [hfloor] at hb3
  have hb4 := HT Ω Y ν hY q hq0 (by linarith) y hy2 σ (M : ℝ) hσ0 hM0
  exact integral_rpow_lineDiv_le_of_ranges hY hy2 hσ0 hq0 (by linarith) hM1 hb1 hb2 hb3 hb4

/-! ### The four ranges, each against `min{Λ, 1+α^{-1}}·Λ^{-q/2}` -/

/-- `e^{-αΛ/2}` is already below the target. -/
lemma exp_le_target {Λ α q : ℝ} (hΛ : 16 ≤ Λ) (hα : 0 < α) (hq0 : 0 < q) (hq2 : q ≤ 1 / 2) :
    Real.exp (-(α * Λ / 2)) ≤ min Λ (1 + α⁻¹) * Λ ^ (-(q / 2)) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have h34 : (0 : ℝ) < Λ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hΛ0 _
  have hmin0 : (0 : ℝ) ≤ min Λ (1 + α⁻¹) := le_min (by linarith) (by positivity)
  have hkey : Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)) ≤ min Λ (1 + α⁻¹) :=
    le_min (rpow_three_quarters_mul_exp_le_self hΛ1 hα.le)
      (le_trans (rpow_three_quarters_mul_exp_le_inv hΛ hα) (by linarith [inv_pos.2 hα]))
  have hsp : Λ ^ (3 / 4 : ℝ) * Λ ^ (-(3 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add hΛ0]
    norm_num
  have hmono : Λ ^ (-(3 / 4) : ℝ) ≤ Λ ^ (-(q / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hΛ1 (by linarith)
  have h340 : (0 : ℝ) ≤ Λ ^ (-(3 / 4) : ℝ) := (Real.rpow_pos_of_pos hΛ0 _).le
  calc Real.exp (-(α * Λ / 2))
      = Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)) * Λ ^ (-(3 / 4) : ℝ) := by
        rw [mul_comm (Λ ^ (3 / 4 : ℝ)) (Real.exp (-(α * Λ / 2))), mul_assoc, hsp, mul_one]
    _ ≤ min Λ (1 + α⁻¹) * Λ ^ (-(3 / 4) : ℝ) := mul_le_mul_of_nonneg_right hkey h340
    _ ≤ min Λ (1 + α⁻¹) * Λ ^ (-(q / 2)) := mul_le_mul_of_nonneg_left hmono hmin0

/-- **The central window against the target.**  `S ≤ 8Λ` is `(σ·log y)^{-1} = log x/log y`, and
`E ≤ e^{-αΛ/2}` is `(log y)^{-α}` at `log log y ≥ Λ/2`. -/
lemma central_le_target {A S E Λ α q : ℝ} (hA : 0 < A) (hΛ : 512 ≤ Λ) (hα : 0 < α)
    (hq0 : 0 < q) (hq2 : q ≤ 1 / 2) (hS1 : 1 ≤ S) (hS : S ≤ 8 * Λ)
    (hE0 : 0 ≤ E) (hE : E ≤ Real.exp (-(α * Λ / 2))) :
    A * S ^ q * E ≤ 3 * A * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hmin0 : (0 : ℝ) ≤ min Λ (1 + α⁻¹) := le_min (by linarith) (by positivity)
  have hc1 : S ^ q ≤ (8 * Λ) ^ q := Real.rpow_le_rpow (by linarith) hS hq0.le
  have hc2 : (8 * Λ) ^ q = (8 : ℝ) ^ q * Λ ^ q := Real.mul_rpow (by norm_num) hΛ0.le
  have h9 : (3 : ℝ) = (9 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (3 : ℝ) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hc3 : (8 : ℝ) ^ q ≤ 3 := by
    calc (8 : ℝ) ^ q ≤ (8 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ ≤ (9 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := h9.symm
  have hc4 : Λ ^ q ≤ Λ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ1 hq2
  have hSq : S ^ q ≤ 3 * Λ ^ (1 / 2 : ℝ) := by
    rw [hc2] at hc1
    nlinarith [hc1, hc3, hc4, Real.rpow_nonneg hΛ0.le q,
      Real.rpow_pos_of_pos hΛ0 (1 / 2 : ℝ), Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8) q]
  have hSq0 : (0 : ℝ) ≤ S ^ q := Real.rpow_nonneg (by linarith) _
  have hsp : Λ ^ (1 / 2 : ℝ) = Λ ^ (3 / 4 : ℝ) * Λ ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_add hΛ0]
    norm_num
  have hq14 : Λ ^ (-(1 / 4) : ℝ) ≤ Λ ^ (-(q / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hΛ1 (by linarith)
  have h140 : (0 : ℝ) ≤ Λ ^ (-(1 / 4) : ℝ) := (Real.rpow_pos_of_pos hΛ0 _).le
  have hkey : Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)) ≤ min Λ (1 + α⁻¹) :=
    le_min (rpow_three_quarters_mul_exp_le_self hΛ1 hα.le)
      (le_trans (rpow_three_quarters_mul_exp_le_inv (by linarith) hα) (by linarith [inv_pos.2 hα]))
  calc A * S ^ q * E ≤ A * (3 * Λ ^ (1 / 2 : ℝ)) * Real.exp (-(α * Λ / 2)) := by
        have h1 : A * S ^ q ≤ A * (3 * Λ ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hSq hA.le
        have h2 : (0 : ℝ) ≤ A * S ^ q := mul_nonneg hA.le hSq0
        nlinarith [h1, h2, hE, hE0]
    _ = 3 * A * (Λ ^ (3 / 4 : ℝ) * Real.exp (-(α * Λ / 2)) * Λ ^ (-(1 / 4) : ℝ)) := by
        rw [hsp]; ring
    _ ≤ 3 * A * (min Λ (1 + α⁻¹) * Λ ^ (-(1 / 4) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey h140) (by linarith)
    _ ≤ 3 * A * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq14 hmin0) (by linarith)

/-- **The mesoscopic range against the target**, `J` traded for `Λ`. -/
lemma meso_le_target {A Λ α q : ℝ} {J : ℕ} (hA : 0 < A) (hΛ : 1 ≤ Λ) (hα : 0 < α)
    (hq0 : 0 < q) (hq2 : q ≤ 1 / 2) (hJlo : Λ / 2 ≤ (J : ℝ)) (hJhi : (J : ℝ) ≤ Λ + 1) :
    A * (min (J : ℝ) (1 + α⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q))
      ≤ 8 * A * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hsJ : Real.sqrt Λ / 2 ≤ Real.sqrt J := by
    have hsq : (Real.sqrt Λ / 2) ^ 2 ≤ (J : ℝ) := by
      have h := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ Λ)
      nlinarith
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at h
  have hb : (0 : ℝ) < 1 + (1 - q) * Real.sqrt J := by
    nlinarith [Real.sqrt_nonneg ((J : ℕ) : ℝ)]
  have hsq4 : Real.sqrt Λ ≤ 4 * (1 + (1 - q) * Real.sqrt J) := by
    nlinarith [hsJ, Real.sqrt_nonneg Λ]
  have hF := rpow_neg_le_of_sqrt_le (q := q) (Λ := Λ) (K := 4) hΛ hq0.le (by linarith)
    (by norm_num) hsq4
  have hF0 : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt J) ^ (-q) := Real.rpow_nonneg hb.le _
  have hΛq0 : (0 : ℝ) ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hmin0 : (0 : ℝ) ≤ min Λ (1 + α⁻¹) := le_min (by linarith) (by positivity)
  have hminJ0 : (0 : ℝ) ≤ min (J : ℝ) (1 + α⁻¹) :=
    le_min (Nat.cast_nonneg J) (by positivity)
  have hmin : min (J : ℝ) (1 + α⁻¹) ≤ 2 * min Λ (1 + α⁻¹) := by
    rcases le_total Λ (1 + α⁻¹) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by linarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by linarith [inv_pos.2 hα])
  calc A * (min (J : ℝ) (1 + α⁻¹) * (1 + (1 - q) * Real.sqrt J) ^ (-q))
      ≤ A * (2 * min Λ (1 + α⁻¹) * (4 * Λ ^ (-(q / 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hA.le
        exact mul_le_mul hmin hF hF0 (by linarith [hmin0])
    _ = 8 * A * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by ring

/-- **The mid range against the target.** -/
lemma mid_le_target {A Λ q b : ℝ} (hA : 0 < A) (hΛ : 1 ≤ Λ) (hq0 : 0 < q) (hq2 : q ≤ 1 / 2)
    (hb : 0 < b) (hsq : Real.sqrt Λ ≤ 9 * b) :
    (A * b ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2) ≤ 9 * max 1 A * Λ ^ (-(q / 2)) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hbq : (0 : ℝ) ≤ b ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg hb.le _
  have hexp : (A * b ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2) = A ^ (3 * q / 2) * b ^ (-q) := by
    rw [Real.mul_rpow hA.le hbq, ← Real.rpow_mul hb.le,
      show -(2 / 3 : ℝ) * (3 * q / 2) = -q from by ring]
  have hAq : A ^ (3 * q / 2) ≤ max 1 A := rpow_le_max_one hA (by linarith) (by linarith)
  have hFb := rpow_neg_le_of_sqrt_le (q := q) (Λ := Λ) (K := 9) hΛ hq0.le (by linarith)
    (by norm_num) hsq
  have hb0 : (0 : ℝ) ≤ b ^ (-q) := Real.rpow_nonneg hb.le _
  have hAq0 : (0 : ℝ) ≤ A ^ (3 * q / 2) := Real.rpow_nonneg hA.le _
  have hm0 : (0 : ℝ) ≤ max 1 A := le_trans zero_le_one (le_max_left _ _)
  rw [hexp]
  calc A ^ (3 * q / 2) * b ^ (-q) ≤ max 1 A * (9 * Λ ^ (-(q / 2))) :=
        mul_le_mul hAq hFb hb0 hm0
    _ = 9 * max 1 A * Λ ^ (-(q / 2)) := by ring

/-- **The tail against the target.** -/
lemma tail_le_target {A Λ q : ℝ} {M : ℕ} (hA : 0 < A) (hΛ : 1 ≤ Λ) (hq0 : 0 < q)
    (hq2 : q ≤ 1 / 2) (hM : Λ ≤ (M : ℝ)) :
    (A / (M : ℝ)) ^ q ≤ max 1 A * Λ ^ (-(q / 2)) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hsplit : (A / (M : ℝ)) ^ q = A ^ q * ((M : ℝ)) ^ (-q) := by
    rw [Real.div_rpow hA.le hM0.le, Real.rpow_neg hM0.le, div_eq_mul_inv]
  have hAq : A ^ q ≤ max 1 A := rpow_le_max_one hA hq0.le (by linarith)
  have hMq : ((M : ℝ)) ^ (-q) ≤ Λ ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hΛ0 hM (by linarith)
  have hΛq : Λ ^ (-q) ≤ Λ ^ (-(q / 2)) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  have hMq0 : (0 : ℝ) ≤ ((M : ℝ)) ^ (-q) := Real.rpow_nonneg hM0.le _
  have hm0 : (0 : ℝ) ≤ max 1 A := le_trans zero_le_one (le_max_left _ _)
  rw [hsplit]
  exact mul_le_mul hAq (le_trans hMq hΛq) hMq0 hm0

/-! ### The low-moment upper bound for the weighted Rademacher sum -/

set_option maxHeartbeats 1000000 in
-- the four range comparisons and the reduction's error term all live in one context
/-- **`E‖S(x)‖^{2q} ≪ min{log log x, 1+(q(1-2q))^{-1}}·(log log x)^{-q/2}`** for `0 < q < ½`,
uniformly in `q`, with `C` and `x₀` independent of `x`, `q`, `X` and `μ`.

This is `RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ` with the leading
`log log x` replaced by `min{log log x, 1+(q(1-2q))^{-1}}`, which is what keeping the geometric
factor in the depth sum buys.  On `0 < q ≤ ½` the factor `(1-q)` in `(1+(1-q)√(log log x))^{-q}`
lies in `[½,1)`, so the denominator is `(log log x)^{q/2}` up to an absolute constant.

The `1/q` inside `α^{-1} = (q(1-2q))^{-1}` is the depth sum read sharply; descending from a fixed
`q₀` removes it (`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp`).
`q = ½` (`α = 0`) is `RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ`. -/
theorem exists_const_integral_rpow_weightedRademacherSum_le_smallQ_min :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q < 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (min (Real.log (Real.log x)) (1 + (q * (1 - 2 * q))⁻¹)
                * (Real.log (Real.log x)) ^ (-(q / 2))) := by
  obtain ⟨C₀, x₁, hC₀, hx₁, HR⟩ := exists_integral_rpow_weightedRademacherSum_le_reduction_explicit
  obtain ⟨D₀, yb, A₁, A₂, A₃, A₄, hA₁, hA₂, hA₃, hA₄, HG⟩ :=
    exists_const_integral_rpow_lineDiv_le_rademacher_geom (Ω := Ω)
  obtain ⟨x₂, hev⟩ := Filter.eventually_atTop.1
    ((eventually_exists_mesoParams D₀).and
      ((tendsto_reductionY_atTop.eventually_ge_atTop yb).and
        (Filter.eventually_ge_atTop (Real.exp (Real.exp 512)))))
  refine ⟨C₀ * (3 * A₁ + 8 * A₂ + 9 * max 1 A₃ + max 1 A₄ + 1), max x₁ x₂, by positivity, ?_⟩
  intro X μ hX x q hx hq0 hq2
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨J, M, hy2, hlogy1, hσ0, hσy, hJ1, hJle, hJw, hM1, hM, hσJ, hJlo, hJhi, h8L,
    hLLhalf, h8S, hMΛ, hbar⟩, hyb, hxe⟩ := hev x hxx₂
  have hZ := HG X μ hX (reductionSigma x) q (reductionY x) J M hyb hy2 hσ0 hσy hq0 hq2
    hJ1 hJle hJw hM1 hM
  have hmain := HR q hq0 (by linarith) Ω X μ hX x hxx₁
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set α : ℝ := q * (1 - 2 * q) with hαdef
  have hα : (0 : ℝ) < α := by rw [hαdef]; exact mul_pos hq0 (by linarith)
  have hΛ : (512 : ℝ) ≤ Λ := by
    have h1 : Real.exp 512 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 512)) hxe
      rwa [Real.log_exp] at h
    have h2 := Real.log_le_log (Real.exp_pos 512) h1
    rw [hΛdef]
    rwa [Real.log_exp] at h2
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hlogx0 : (0 : ℝ) < Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 512)) hxe
    rw [Real.log_exp] at h
    linarith [Real.exp_pos (512 : ℝ)]
  have hlogy0 : (0 : ℝ) < Real.log (reductionY x) := by linarith
  -- (1) the central window
  have hS1 : (1 : ℝ) ≤ (reductionSigma x * Real.log (reductionY x))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    simpa using hσy
  have hErw : (Real.log (reductionY x)) ^ (q * (2 * q - 1))
      = Real.exp (-(α * Real.log (Real.log (reductionY x)))) := by
    rw [Real.rpow_def_of_pos hlogy0]
    congr 1
    rw [hαdef]
    ring
  have hE : (Real.log (reductionY x)) ^ (q * (2 * q - 1)) ≤ Real.exp (-(α * Λ / 2)) := by
    rw [hErw]
    exact Real.exp_le_exp.2 (by nlinarith [hLLhalf, hα])
  have hT1 := central_le_target hA₁ hΛ hα hq0 (by linarith) hS1 h8S
    (Real.rpow_nonneg hlogy0.le _) hE
  -- (2) the mesoscopic range
  have hT2 := meso_le_target (J := J) hA₂ hΛ1 hα hq0 (by linarith) hJlo hJhi
  -- (3) the mid range
  have hm0 : (0 : ℝ) ≤ ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hbpos : (0 : ℝ) < 1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ) := by
    have := Real.sqrt_nonneg ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ)
    linarith
  have hsq9 : Real.sqrt Λ ≤ 9 * (1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ)) := by
    have h1 : Real.sqrt Λ
        ≤ Real.sqrt (9 * ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt hbar
    have h2 : Real.sqrt (9 * ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ))
        = 3 * Real.sqrt ((harperBlockCount D₀ ((reductionY x : ℕ) : ℝ) / 4 : ℕ) : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h2] at h1
    linarith
  have hT3 := mid_le_target hA₃ hΛ1 hq0 (by linarith) hbpos hsq9
  -- (4) the tail
  have hT4 := tail_le_target (M := M) hA₄ hΛ1 hq0 (by linarith) hMΛ
  -- (5) the reduction's error term
  have hs : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt hΛ0.le
  have hs12 : (12 : ℝ) ≤ Real.sqrt Λ := by
    rw [show (12 : ℝ) = Real.sqrt 144 by
      rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrt8 : Real.sqrt (8 * Λ) ≤ 3 * Real.sqrt Λ := by
    rw [Real.sqrt_mul (by norm_num) Λ]
    have h8 : Real.sqrt 8 ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg Λ, h8]
  have hlog8 : Real.log (8 * Λ) ≤ Λ / 2 := by
    have h := log_le_two_mul_sqrt (by positivity : (0 : ℝ) < 8 * Λ)
    nlinarith [hsqrt8, hs, hs12]
  have herr : (8 * Λ / Real.log x) ^ α ≤ Real.exp (-(α * Λ / 2)) := by
    have hpos : (0 : ℝ) < 8 * Λ / Real.log x := by positivity
    rw [Real.rpow_def_of_pos hpos, Real.log_div (by positivity) hlogx0.ne', ← hΛdef]
    exact Real.exp_le_exp.2 (by nlinarith [hlog8, hα])
  have hT5 := le_trans herr (exp_le_target (by linarith) hα hq0 (by linarith))
  -- assemble
  have hT0 : (0 : ℝ) ≤ min Λ (1 + α⁻¹) * Λ ^ (-(q / 2)) :=
    mul_nonneg (le_min (by linarith) (by positivity)) (Real.rpow_nonneg hΛ0.le _)
  have hΛq0 : (0 : ℝ) ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hmin1 : (1 : ℝ) ≤ min Λ (1 + α⁻¹) :=
    le_min (by linarith) (by linarith [inv_pos.2 hα])
  have hlift : ∀ c : ℝ, 0 ≤ c →
      c * Λ ^ (-(q / 2)) ≤ c * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
    intro c hc
    have h1 : Λ ^ (-(q / 2)) ≤ min Λ (1 + α⁻¹) * Λ ^ (-(q / 2)) := by nlinarith [hmin1, hΛq0]
    exact mul_le_mul_of_nonneg_left h1 hc
  have hmax3 : (0 : ℝ) ≤ 9 * max 1 A₃ := by linarith [le_max_left (1 : ℝ) A₃]
  have hmax4 : (0 : ℝ) ≤ max 1 A₄ := by linarith [le_max_left (1 : ℝ) A₄]
  have hT3' := hT3.trans (hlift (9 * max 1 A₃) hmax3)
  have hT4' := hT4.trans (hlift (max 1 A₄) hmax4)
  refine le_trans hmain ?_
  have hsum : (∫ ω, ((Real.log (reductionY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (reductionY x + 1)
            ((1 / 2 : ℂ) + ((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      + (8 * Λ / Real.log x) ^ α
      ≤ (3 * A₁ + 8 * A₂ + 9 * max 1 A₃ + max 1 A₄ + 1) * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by
    linarith [hZ, hT1, hT2, hT3', hT4', hT5]
  calc C₀ * ((∫ ω, ((Real.log (reductionY x))⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (reductionY x + 1)
              ((1 / 2 : ℂ) + ((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((reductionSigma x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        + (8 * Λ / Real.log x) ^ α)
      ≤ C₀ * ((3 * A₁ + 8 * A₂ + 9 * max 1 A₃ + max 1 A₄ + 1)
          * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2)))) := mul_le_mul_of_nonneg_left hsum hC₀.le
    _ = C₀ * (3 * A₁ + 8 * A₂ + 9 * max 1 A₃ + max 1 A₄ + 1)
        * (min Λ (1 + α⁻¹) * Λ ^ (-(q / 2))) := by ring

/-! ### Down to `q = 0`, and the sharp `min`

Two things separate `RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_min` from the
sharp form `min{Λ, (1-2q)^{-1}}·Λ^{-q/2}`.

* `1 + (q(1-2q))^{-1}` carries a `1/q`, which is real: it is the depth sum read sharply, and no
  step below can remove it.  For `q ≥ ¼` it is at most `5(1-2q)^{-1}`; for `q < ¼` the bound is
  taken at the **fixed** `q₀ = ¼` and carried down by Jensen
  (`RMF.integral_rpow_le_rpow_of_le_exponent`), where the `min` is the constant `9`.
* `min{Λ, (1-2q)^{-1}} ≥ 1`, so the descended `≤ C·Λ^{-q/2}` already implies the target. -/

/-- The harmonic sum's moments are integrable: `‖S(x)‖ ≤ ⌊x⌋₊` a.e. -/
lemma integrable_rpow_norm_weightedRademacherSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω)
      x ω‖ ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hWm : Measurable
      (weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x) :=
    Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _
  refine (memLp_top_of_bound
    ((Real.continuous_rpow_const hr).measurable.comp hWm.norm).aestronglyMeasurable
    (((⌊x⌋₊ : ℝ)) ^ r) ?_).integrable le_top
  filter_upwards [ae_norm_weightedRademacherSum_le hRa x] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
  exact Real.rpow_le_rpow (norm_nonneg _) hω hr

/-- **The low-moment upper bound for the weighted Rademacher sum.**

`E‖S(x)‖^{2q} ≤ C · min{log log x, (1-2q)^{-1}} · (log log x)^{-q/2}`  for `0 < q < ½`,

uniformly in `q`, with `C` and `x₀` independent of `x`, `q`, `X` and `μ`.  `S(x) = ∑_{n≤x} f(n)/√n`
is the harmonically weighted sum, whose second moment is `≍ log x`.

`q = ½` is excluded: there `min{Λ, (1-2q)^{-1}} = Λ` and the statement is
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ`.  For `q > ½` the main factor is
`(log x)^{q(2q-1)}` (`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_uniform_min`). -/
theorem exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q < 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹)
                * (Real.log (Real.log x)) ^ (-(q / 2))) := by
  obtain ⟨C, x₀, hC, H⟩ := exists_const_integral_rpow_weightedRademacherSum_le_smallQ_min (Ω := Ω)
  refine ⟨5 * max 1 (9 * C), max x₀ (Real.exp (Real.exp 1)), by positivity, ?_⟩
  intro X μ hX x q hx hq0 hq2
  haveI := hX.isProbabilityMeasure
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hΛ1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
    have h1 : Real.exp 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hxe
      rwa [Real.log_exp] at h
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hΛ0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hΛq : (0 : ℝ) ≤ (Real.log (Real.log x)) ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have h2q : (0 : ℝ) < 1 - 2 * q := by linarith
  have hinv1 : (1 : ℝ) ≤ (1 - 2 * q)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h2q]
    linarith
  have hmin1 : (1 : ℝ) ≤ min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹) := le_min hΛ1 hinv1
  have hmin0 : (0 : ℝ) ≤ min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹) := by linarith
  have hCm : C ≤ max 1 (9 * C) := le_trans (by linarith) (le_max_right 1 (9 * C))
  have hCm0 : (0 : ℝ) < max 1 (9 * C) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rcases le_total (1 / 4 : ℝ) q with hq | hq
  · -- `q ≥ ¼`: the `min` is already there, up to the factor `5`
    have h := H X μ hX x q hx₀ hq0 hq2
    have hα : (0 : ℝ) < q * (1 - 2 * q) := mul_pos hq0 h2q
    have hαinv : (q * (1 - 2 * q))⁻¹ ≤ 4 * (1 - 2 * q)⁻¹ := by
      rw [show (4 : ℝ) * (1 - 2 * q)⁻¹ = ((1 - 2 * q) / 4)⁻¹ by
        rw [inv_div]; ring]
      exact (inv_le_inv₀ (a := q * (1 - 2 * q)) (b := (1 - 2 * q) / 4)
        (by positivity) (by positivity)).2 (by nlinarith)
    have hminle : min (Real.log (Real.log x)) (1 + (q * (1 - 2 * q))⁻¹)
        ≤ 5 * min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹) := by
      rcases le_total (Real.log (Real.log x)) ((1 - 2 * q)⁻¹) with h | h
      · rw [min_eq_left h]
        exact le_trans (min_le_left _ _) (by linarith)
      · rw [min_eq_right h]
        exact le_trans (min_le_right _ _) (by linarith)
    calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
        ≤ C * (min (Real.log (Real.log x)) (1 + (q * (1 - 2 * q))⁻¹)
            * (Real.log (Real.log x)) ^ (-(q / 2))) := h
      _ ≤ max 1 (9 * C) * ((5 * min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹))
            * (Real.log (Real.log x)) ^ (-(q / 2))) := by
          refine mul_le_mul hCm (mul_le_mul_of_nonneg_right hminle hΛq) ?_ hCm0.le
          exact mul_nonneg (le_min (by linarith) (by positivity)) hΛq
      _ = 5 * max 1 (9 * C) * (min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹)
            * (Real.log (Real.log x)) ^ (-(q / 2))) := by ring
  · -- `q < ¼`: descend from `q₀ = ¼`, where the `min` is the constant `9`
    have h := H X μ hX x (1 / 4) hx₀ (by norm_num) (by norm_num)
    have h9 : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * (1 / 4 : ℝ)) ∂μ)
        ≤ 9 * C * (Real.log (Real.log x)) ^ (-((1 / 4 : ℝ) / 2)) := by
      refine h.trans ?_
      have hnum : (1 : ℝ) + ((1 / 4 : ℝ) * (1 - 2 * (1 / 4 : ℝ)))⁻¹ = 9 := by norm_num
      rw [hnum]
      have hm : min (Real.log (Real.log x)) (9 : ℝ) ≤ 9 := min_le_right _ _
      have hq9 : (0 : ℝ) ≤ (Real.log (Real.log x)) ^ (-((1 / 4 : ℝ) / 2)) :=
        Real.rpow_nonneg hΛ0.le _
      calc C * (min (Real.log (Real.log x)) (9 : ℝ)
              * (Real.log (Real.log x)) ^ (-((1 / 4 : ℝ) / 2)))
          ≤ C * (9 * (Real.log (Real.log x)) ^ (-((1 / 4 : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hq9) hC.le
        _ = 9 * C * (Real.log (Real.log x)) ^ (-((1 / 4 : ℝ) / 2)) := by ring
    have hd := integral_rpow_le_rpow_of_le_exponent (q₀ := (1 / 4 : ℝ)) hq0 hq
      (by positivity : (0 : ℝ) < 9 * C) hΛ0
      (integrable_rpow_norm_weightedRademacherSum hX x (by norm_num)) h9
    refine hd.trans ?_
    calc max 1 (9 * C) * (Real.log (Real.log x)) ^ (-(q / 2))
        ≤ max 1 (9 * C) * ((5 * min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹))
            * (Real.log (Real.log x)) ^ (-(q / 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCm0.le
          nlinarith [hmin1, hΛq]
      _ = 5 * max 1 (9 * C) * (min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹)
            * (Real.log (Real.log x)) ^ (-(q / 2))) := by ring

/-! ### `q = ½`, and one statement for the whole range

`min{Λ, (1-2q)^{-1}}` is the wrong way to write the target if `q = ½` is to be included: there
`(1-2q)^{-1}` is `0⁻¹ = 0` in Lean, the `min` collapses to `0`, and the statement becomes false
rather than merely unproved.  What the `min` *means* at `q = ½` is `min{Λ, ∞} = Λ`.

The harmonic form has no junk value:

`(Λ^{-1} + (1-2q))^{-1}`

equals `Λ` exactly at `q = ½`, and for `q < ½` it is `(Λ^{-1} + ((1-2q)^{-1})^{-1})^{-1}`, which
is within a factor `2` of `min{Λ, (1-2q)^{-1}}`.  So one statement covers `0 < q ≤ ½` with
nothing lost and nothing excluded. -/

/-- `min{A,B} ≤ 2·(A^{-1}+B^{-1})^{-1}`: the harmonic mean is at least half the minimum. -/
lemma min_le_two_mul_inv_add_inv {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    min A B ≤ 2 * (A⁻¹ + B⁻¹)⁻¹ := by
  have hm0 : (0 : ℝ) < min A B := lt_min hA hB
  have hAm : A⁻¹ ≤ (min A B)⁻¹ := (inv_le_inv₀ hA hm0).2 (min_le_left _ _)
  have hBm : B⁻¹ ≤ (min A B)⁻¹ := (inv_le_inv₀ hB hm0).2 (min_le_right _ _)
  have hsum : A⁻¹ + B⁻¹ ≤ 2 * (min A B)⁻¹ := by linarith
  have hpos : (0 : ℝ) < A⁻¹ + B⁻¹ := by positivity
  have hstep : (2 * (min A B)⁻¹)⁻¹ ≤ (A⁻¹ + B⁻¹)⁻¹ :=
    (inv_le_inv₀ (by positivity) hpos).2 hsum
  have hval : (2 * (min A B)⁻¹)⁻¹ = min A B / 2 := by
    rw [mul_inv, inv_inv]
    ring
  rw [hval] at hstep
  linarith

/-- **The low-moment upper bound for the weighted Rademacher sum, on the whole range `0 < q ≤ ½`.**

`E‖S(x)‖^{2q} ≤ C · ((log log x)^{-1} + (1-2q))^{-1} · (log log x)^{-q/2}`,

uniformly in `q`, with `C` and `x₀` independent of `x`, `q`, `X` and `μ`.  `S(x) = ∑_{n≤x} f(n)/√n`.

The middle factor is `min{log log x, (1-2q)^{-1}}` up to a factor `2` for `q < ½`
(`RMF.min_le_two_mul_inv_add_inv`) and is exactly `log log x` at `q = ½`, so this is
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp` below the endpoint and
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ` at it; the endpoint is a special
case of the proof only, not of the statement. -/
theorem exists_const_integral_rpow_weightedRademacherSum_le_smallQ_uniform :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
                * (Real.log (Real.log x)) ^ (-(q / 2))) := by
  obtain ⟨C₁, x₁, hC₁, H₁⟩ :=
    exists_const_integral_rpow_weightedRademacherSum_le_smallQ_sharp (Ω := Ω)
  obtain ⟨C₂, x₂, hC₂, H₂⟩ :=
    exists_const_integral_rpow_weightedRademacherSum_le_smallQ (Ω := Ω)
  refine ⟨2 * C₁ + 2 * C₂, max (max x₁ x₂) (Real.exp (Real.exp 1)), by positivity, ?_⟩
  intro X μ hX x q hx hq0 hq2
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hΛ1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
    have h1 : Real.exp 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hxe
      rwa [Real.log_exp] at h
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hΛ0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hΛq : (0 : ℝ) ≤ (Real.log (Real.log x)) ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hH0 : (0 : ℝ) < ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ := by
    have : (0 : ℝ) < (Real.log (Real.log x))⁻¹ + (1 - 2 * q) := by
      have := inv_pos.2 hΛ0
      linarith
    positivity
  rcases lt_or_eq_of_le hq2 with hlt | heq
  · -- below the endpoint: the harmonic form is within a factor `2` of the `min`
    have h2q : (0 : ℝ) < 1 - 2 * q := by linarith
    have hmin := min_le_two_mul_inv_add_inv hΛ0 (inv_pos.2 h2q)
    rw [inv_inv] at hmin
    have h := H₁ X μ hX x q hx₁ hq0 hlt
    calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
        ≤ C₁ * (min (Real.log (Real.log x)) ((1 - 2 * q)⁻¹)
            * (Real.log (Real.log x)) ^ (-(q / 2))) := h
      _ ≤ C₁ * ((2 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹)
            * (Real.log (Real.log x)) ^ (-(q / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmin hΛq) hC₁.le
      _ ≤ (2 * C₁ + 2 * C₂) * (((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
            * (Real.log (Real.log x)) ^ (-(q / 2))) := by
          have hprod : (0 : ℝ) ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
              * (Real.log (Real.log x)) ^ (-(q / 2)) := mul_nonneg hH0.le hΛq
          nlinarith [hprod, hC₂]
  · -- at the endpoint: the middle factor is `log log x` exactly
    subst heq
    have hval : ((Real.log (Real.log x))⁻¹ + (1 - 2 * (1 / 2 : ℝ)))⁻¹
        = Real.log (Real.log x) := by
      rw [show (1 : ℝ) - 2 * (1 / 2 : ℝ) = 0 by norm_num, add_zero, inv_inv]
    have h := H₂ X μ hX x (1 / 2) hx₂ (by norm_num) le_rfl
    -- the barrier denominator, at `Λ` itself
    have hb : (0 : ℝ) < 1 + (1 - (1 / 2 : ℝ)) * Real.sqrt (Real.log (Real.log x)) := by
      have := Real.sqrt_nonneg (Real.log (Real.log x))
      linarith
    have hsq : Real.sqrt (Real.log (Real.log x))
        ≤ 2 * (1 + (1 - (1 / 2 : ℝ)) * Real.sqrt (Real.log (Real.log x))) := by
      have := Real.sqrt_nonneg (Real.log (Real.log x))
      linarith
    have hF := rpow_neg_le_of_sqrt_le (q := (1 / 2 : ℝ)) (Λ := Real.log (Real.log x)) (K := 2)
      hΛ1 (by norm_num) (by norm_num) (by norm_num) hsq
    rw [hval]
    calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * (1 / 2 : ℝ)) ∂μ)
        ≤ C₂ * (Real.log (Real.log x)
            * (1 + (1 - (1 / 2 : ℝ)) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2 : ℝ))) := h
      _ ≤ C₂ * (Real.log (Real.log x)
            * (2 * (Real.log (Real.log x)) ^ (-((1 / 2 : ℝ) / 2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hΛ0.le) hC₂.le
      _ ≤ (2 * C₁ + 2 * C₂) * (Real.log (Real.log x)
            * (Real.log (Real.log x)) ^ (-((1 / 2 : ℝ) / 2))) := by
          have hprod : (0 : ℝ) ≤ Real.log (Real.log x)
              * (Real.log (Real.log x)) ^ (-((1 / 2 : ℝ) / 2)) :=
            mul_nonneg hΛ0.le (Real.rpow_nonneg hΛ0.le _)
          nlinarith [hprod, hC₁]

end RMF
