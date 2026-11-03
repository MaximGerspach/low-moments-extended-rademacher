/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.DepthSum
import RMF.Probability.RademacherRealness
import RMF.Weighted.MesoscopicBlock

/-!
# `Z_m`: from one block to the range

`RMF.exists_const_integral_rpow_setIntegral_normSq_block_le_rademacher` bounds one window
`[T/e, T]`; `RMF.integral_rpow_setIntegral_weight_le_sum_windows_primesIco` sums the windows
against the weight `|σ+ih|^{-2}`; `RMF.sum_one_add_mul_sqrt_rpow_neg_le` evaluates the sum.  This
file joins them.

## Only the positive heights

The Rademacher coefficients are **real**, so `conj(F_y(s)) = F_y(conj s)` and hence
`‖F_y(½+σ-it)‖ = ‖F_y(½+σ+it)‖` pointwise on the realness set — the field is an even function of
the height.  The weight `|σ+it|^{-2} = (σ²+t²)^{-1}` is even too, so

`∫_{A<|t|≤B} ρ(t)‖F_y(½+σ+it)‖²dt = 2∫_{(A,B]} ρ(t)‖F_y(½+σ+it)‖²dt`.

Folding once, on the whole range, is what keeps the window family indexed by `1 ≤ j ≤ J` instead
of by `±j`; the factor `2` costs `2^q ≤ 2` in the constant.

`RMF/Probability/RademacherRealness.lean` exists for exactly this reflection — there it halves
Harper's maximum over `ℤ`, here it halves the window family.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The field is even in the height -/

/-- **Reflecting the height does not change the norm**, for a block product:
`RMF.norm_randomEulerProductIco_sqfree_heightLine_neg` in `RMF.shiftLine` coordinates. -/
lemma ae_forall_norm_randomEulerProductIco_shiftLine_neg {X : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hX : IsRademacherPrimeValues X ν) (y₀ y : ℕ) (σ : ℝ) :
    ∀ᵐ ω ∂ν, ∀ h : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ (-h)) ω‖
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ h) ω‖ := by
  filter_upwards [ae_forall_conj_eq_primesIco hX conj_eq_rademacherLaw y₀ y] with ω hω
  intro h
  have hkey := norm_randomEulerProductIco_sqfree_heightLine_neg (X := X) (y₀ := y₀)
    (y₁ := y) (σ := 1 / 2 + σ) (h := h) hω
  simpa [shiftLine, heightLine] using hkey

/-- **Reflecting the height does not change the norm**, for the full product.  The `y₀ = 0` case
of `RMF.norm_randomEulerProductIco_sqfree_heightLine_neg`, in `RMF.shiftLine` coordinates.

The case `y₀ = 0` of `RMF.ae_forall_norm_randomEulerProductIco_shiftLine_neg`. -/
lemma ae_forall_norm_randomEulerProduct_shiftLine_neg {X : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hX : IsRademacherPrimeValues X ν) (y : ℕ) (σ : ℝ) :
    ∀ᵐ ω ∂ν, ∀ h : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ (-h)) ω‖
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ h) ω‖ := by
  simpa only [randomEulerProductIco_zero] using
    ae_forall_norm_randomEulerProductIco_shiftLine_neg hX 0 y σ

/-! ### Folding the range onto the positive heights -/

/-- **The weighted integral over `A < |t| ≤ B` is twice its positive half**, for a block product
on any line `Re s = ½ + σ > 0`: `RMF.ae_setIntegral_weight_normSq_symm` with the product over
`[y₀, y)`. -/
lemma ae_setIntegral_weight_normSq_symm_primesIco {X : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hX : IsRademacherPrimeValues X ν) (y₀ y : ℕ) {σ : ℝ} (hσ : 0 < 1 / 2 + σ) {ρ : ℝ → ℝ} {Bρ : ℝ}
    (hρeven : ∀ t, ρ (-t) = ρ t) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρb : ∀ t, ρ t ≤ Bρ) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ∀ᵐ ω ∂ν, (∫ t in {t : ℝ | A < |t| ∧ |t| ≤ B},
        ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2)
      = 2 * ∫ t in Set.Ioc A B,
          ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2 := by
  haveI := hX.isProbabilityMeasure
  filter_upwards [ae_forall_norm_randomEulerProductIco_shiftLine_neg hX y₀ y σ,
    ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y hσ] with ω hrefl henv
  set U : ℝ := ∏ p ∈ primesIco y₀ y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hU
  set g : ℝ → ℝ := fun t => ρ t * ‖randomEulerProductIco
    (fun ω => squarefreeExtension fun p => X p ω) y₀ y (shiftLine σ t) ω‖ ^ 2 with hg
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hgeven : ∀ t, g (-t) = g t := fun t => by rw [hg]; simp only []; rw [hρeven t, hrefl t]
  have hgm : Measurable g := by
    refine hρm.mul ?_
    have hcont : Continuous fun t : ℝ =>
        primePoly (primesIco y₀ y) (shiftLine σ t) (fun p => X (p : ℕ) ω) :=
      (continuous_primePoly_shiftLine (fun p hp => (prime_of_mem_primesIco hp).pos) σ).comp
        (continuous_const.prodMk continuous_id)
    have h := hcont.measurable.norm.pow_const 2
    simpa only [primePoly_primesIco] using h
  have hgb : ∀ t, g t ≤ Bρ * U ^ 2 := by
    intro t
    refine mul_le_mul (hρb t) ?_ (sq_nonneg _) (le_trans (hρ0 t) (hρb t))
    exact pow_le_pow_left₀ (norm_nonneg _) (henv (shiftLine σ t) (re_shiftLine σ t)).2 2
  -- the two halves
  have hint : ∀ s : Set ℝ, volume s ≠ ⊤ → IntegrableOn g s := by
    intro s hs
    refine Measure.integrableOn_of_bounded (M := Bρ * U ^ 2) hs hgm.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
    exact hgb t
  have hsplit : {t : ℝ | A < |t| ∧ |t| ≤ B} = Set.Ioc A B ∪ Set.Ico (-B) (-A) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      constructor
      · exact fun h => Or.inl ⟨h.1, h.2⟩
      · rintro (h | h)
        · exact ⟨h.1, h.2⟩
        · exfalso; linarith [h.2]
    · rw [abs_of_nonpos ht]
      constructor
      · exact fun h => Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩
      · rintro (h | h)
        · exfalso; linarith [h.1]
        · exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hdisj : Disjoint (Set.Ioc A B) (Set.Ico (-B) (-A)) := by
    rw [Set.disjoint_left]
    rintro t ht ht'
    rw [Set.mem_Ioc] at ht
    rw [Set.mem_Ico] at ht'
    linarith [ht.1, ht'.2]
  have hvol1 : volume (Set.Ioc A B) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hvol2 : volume (Set.Ico (-B) (-A)) ≠ ⊤ := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  rw [hsplit, setIntegral_union hdisj measurableSet_Ico (hint _ hvol1) (hint _ hvol2)]
  -- the negative half equals the positive one
  have hneg : (∫ t in Set.Ico (-B) (-A), g t) = ∫ t in Set.Ioc A B, g t := by
    rw [← MeasureTheory.integral_Icc_eq_integral_Ico,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -B ≤ -A),
      ← intervalIntegral.integral_comp_neg (a := A) (b := B) g,
      intervalIntegral.integral_of_le hAB]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => hgeven t
  rw [hneg]
  ring

/-- **The weighted integral over `A < |t| ≤ B` is twice its positive half.**  Both factors are
even in `t`: the weight by hypothesis, the field by
`RMF.ae_forall_norm_randomEulerProduct_shiftLine_neg`.  `0 ≤ A` makes the two halves disjoint.
The case `y₀ = 0` of `RMF.ae_setIntegral_weight_normSq_symm_primesIco`. -/
lemma ae_setIntegral_weight_normSq_symm {X : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hX : IsRademacherPrimeValues X ν) (y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {ρ : ℝ → ℝ} {Bρ : ℝ}
    (hρeven : ∀ t, ρ (-t) = ρ t) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρb : ∀ t, ρ t ≤ Bρ) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ∀ᵐ ω ∂ν, (∫ t in {t : ℝ | A < |t| ∧ |t| ≤ B},
        ρ t * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ t) ω‖ ^ 2)
      = 2 * ∫ t in Set.Ioc A B,
          ρ t * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ t) ω‖ ^ 2 := by
  simpa only [randomEulerProductIco_zero] using
    ae_setIntegral_weight_normSq_symm_primesIco hX 0 y (σ := σ) (by linarith) hρeven hρm hρ0
      hρb hA hAB

/-! ### The shallowest blocks

The chaos estimate carries a threshold on the depth — `t₀ ≤ harperBlockCount D x - 3` — and the
depth of the `j`-th block is `≈ j`, so the `O(1)` blocks at the bottom of the range are not
covered by it.  They do not need to be.  Replacing the chaos factor by **Jensen and Mertens**
loses only the `(1+(1-q)√t)^{-q}` saving, and on `O(1)` blocks that saving was `O(1)` anyway.

What must not be used there is the *trivial* bound on the whole block: the weight `|σ+ih|^{-2}`
is largest exactly at the bottom of the range, and without the `(log w)^{q(2q-1)}` of the split
those blocks would contribute `(log y)^q` — the split is what makes them summable, not the
barrier. -/

/-- **The block product's window moment, by Jensen and Mertens, at a shift of either sign.**

`E[(∫_{T/e}^{T}‖F_{[z,x]}(½+σ+ih)‖²dh)^q] ≤ (e³⁷·T²·log x)^q` for `½ + σ > 0` with `σ ≥ 0` or
`2|σ|·log x ≤ 1`: `RMF.integral_rpow_setIntegral_normSq_primesIco_le_mertens` with the first moment
`RMF.integral_normSq_randomEulerProductIco_le_mertens_signed`, at `e³⁷` for `e²¹`. -/
lemma integral_rpow_setIntegral_normSq_primesIco_le_mertens_signed {X : ℕ → Ω → ℂ}
    {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z : ℕ} {x σ T q : ℝ}
    (hz2 : 2 ≤ z) (hzx : (z : ℝ) ≤ x) (hσ : 0 < 1 / 2 + σ)
    (hσx : 0 ≤ σ ∨ 2 * |σ| * Real.log x ≤ 1) (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hTz : 1 ≤ T * Real.log z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1)
          (shiftLine σ h) ω‖ ^ 2) ^ q ∂μ)
      ≤ (Real.exp 37 * (T ^ 2 * Real.log x)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hx2 : (2 : ℝ) ≤ x := le_trans hz2R hzx
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTe0 : (0 : ℝ) < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  have hTe : T / Real.exp 1 ≤ T := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
  have hvolfin : volume (Set.Icc (T / Real.exp 1) T) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hvol : (volume (Set.Icc (T / Real.exp 1) T)).toReal = T - T / Real.exp 1 := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  -- the per-height first moment, integrated over the window
  have hmert : ∀ h : ℝ, (∫ ω, ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 ∂μ)
      ≤ Real.exp 37 * (T * Real.log x) := fun h =>
    integral_normSq_randomEulerProductIco_le_mertens_signed hX hz2 hzx hσx hT0 hT1 hTz
      (re_shiftLine σ h)
  have hInt : Integrable (Function.uncurry fun (ω : Ω) (tt : ℝ) =>
      Set.indicator (Set.univ : Set Ω) (fun ω => ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1) (shiftLine σ tt) ω‖ ^ 2) ω)
      (μ.prod (volume.restrict (Set.Icc (T / Real.exp 1) T))) := by
    simpa only [Set.indicator_univ] using
      integrable_uncurry_normSq_shiftLine_primesIco hX z (⌊x⌋₊ + 1) hσ
        (I := Set.Icc (T / Real.exp 1) T) hvolfin
  have hmean := integral_setIntegral_indicator_le_of_per_height
    (L := fun _ => (Set.univ : Set Ω))
    (g := fun (tt : ℝ) ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1) (shiftLine σ tt) ω‖ ^ 2)
    measurableSet_Icc hvolfin hInt (fun tt _ => by
      simpa only [Set.indicator_univ] using hmert tt)
  simp only [Set.indicator_univ] at hmean
  rw [hvol] at hmean
  have hB : (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1)
        (shiftLine σ h) ω‖ ^ 2) ∂μ) ≤ Real.exp 37 * (T ^ 2 * Real.log x) := by
    refine le_trans hmean ?_
    have hfac : (T - T / Real.exp 1) * T ≤ T ^ 2 := by nlinarith [hTe0, hT0]
    calc (T - T / Real.exp 1) * (Real.exp 37 * (T * Real.log x))
        = ((T - T / Real.exp 1) * T) * (Real.exp 37 * Real.log x) := by ring
      _ ≤ T ^ 2 * (Real.exp 37 * Real.log x) :=
          mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = Real.exp 37 * (T ^ 2 * Real.log x) := by ring
  exact integral_rpow_le_rpow_of_integral_le hq0 hq1
    (Filter.Eventually.of_forall fun ω => integral_nonneg fun h => sq_nonneg _)
    (integrable_setIntegral_normSq_primesIco_signed hX z (⌊x⌋₊ + 1) hσ hTe) hB

/-- **The block product's window moment, by Jensen and Mertens.**  For `2 ≤ z ≤ x`, `σ ≥ 0`,
`0 < T ≤ 1` with `T·log z ≥ 1`, and `0 ≤ q ≤ 1`,
`E[(∫_{T/e}^{T}‖F_{[z,x]}(½+σ+ih)‖²dh)^q] ≤ (e²¹·T²·log x)^q`, with no depth and no barrier:
`RMF.integral_normSq_randomEulerProductIco_le_mertens` integrated over the window and read through
Jensen — the same first moment the interpolation uses to normalise, without the interpolation. -/
lemma integral_rpow_setIntegral_normSq_primesIco_le_mertens {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z : ℕ} {x σ T q : ℝ}
    (hz2 : 2 ≤ z) (hzx : (z : ℝ) ≤ x) (hσ : 0 ≤ σ) (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hTz : 1 ≤ T * Real.log z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1)
          (shiftLine σ h) ω‖ ^ 2) ^ q ∂μ)
      ≤ (Real.exp 21 * (T ^ 2 * Real.log x)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hx2 : (2 : ℝ) ≤ x := le_trans hz2R hzx
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTe0 : (0 : ℝ) < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  have hTe : T / Real.exp 1 ≤ T := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
  have hvolfin : volume (Set.Icc (T / Real.exp 1) T) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hvol : (volume (Set.Icc (T / Real.exp 1) T)).toReal = T - T / Real.exp 1 := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  -- the per-height first moment, integrated over the window
  have hmert : ∀ h : ℝ, (∫ ω, ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 ∂μ)
      ≤ Real.exp 21 * (T * Real.log x) := fun h =>
    integral_normSq_randomEulerProductIco_le_mertens hX hz2 hzx hσ hT0 hT1 hTz
      (re_shiftLine σ h)
  have hInt : Integrable (Function.uncurry fun (ω : Ω) (tt : ℝ) =>
      Set.indicator (Set.univ : Set Ω) (fun ω => ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1) (shiftLine σ tt) ω‖ ^ 2) ω)
      (μ.prod (volume.restrict (Set.Icc (T / Real.exp 1) T))) := by
    simpa only [Set.indicator_univ] using
      integrable_uncurry_normSq_primesIco hX z (⌊x⌋₊ + 1) hσ
        (I := Set.Icc (T / Real.exp 1) T) hvolfin
  have hmean := integral_setIntegral_indicator_le_of_per_height
    (L := fun _ => (Set.univ : Set Ω))
    (g := fun (tt : ℝ) ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1) (shiftLine σ tt) ω‖ ^ 2)
    measurableSet_Icc hvolfin hInt (fun tt _ => by
      simpa only [Set.indicator_univ] using hmert tt)
  simp only [Set.indicator_univ] at hmean
  rw [hvol] at hmean
  have hB : (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1)
        (shiftLine σ h) ω‖ ^ 2) ∂μ) ≤ Real.exp 21 * (T ^ 2 * Real.log x) := by
    refine le_trans hmean ?_
    have hfac : (T - T / Real.exp 1) * T ≤ T ^ 2 := by nlinarith [hTe0, hT0]
    calc (T - T / Real.exp 1) * (Real.exp 21 * (T * Real.log x))
        = ((T - T / Real.exp 1) * T) * (Real.exp 21 * Real.log x) := by ring
      _ ≤ T ^ 2 * (Real.exp 21 * Real.log x) :=
          mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = Real.exp 21 * (T ^ 2 * Real.log x) := by ring
  exact integral_rpow_le_rpow_of_integral_le hq0 hq1
    (Filter.Eventually.of_forall fun ω => integral_nonneg fun h => sq_nonneg _)
    (integrable_setIntegral_normSq_primesIco hX z (⌊x⌋₊ + 1) hσ hTe) hB

/-- **A mesoscopic block below the depth threshold.**

`E[(∫_{T/e}^{T}‖F_x(½+σ+it)‖²dt)^q] ≤ e^{143828}·(log w)^{q(2q-1)}·(T²·log x)^q` — the sharp block
bound with the barrier saving dropped, and **no** hypothesis on the depth, the offset or `x₀`.

Uniform on `0 ≤ q ≤ 1`, as its two inputs are. -/
theorem integral_rpow_setIntegral_normSq_block_le_trivial {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {x σ T q : ℝ} {w : ℕ}
    (hw2 : 2 ≤ w) (hwfl : w + 1 ≤ ⌊x⌋₊ + 1) (hwx : ((w : ℝ) + 1) ≤ x)
    (hσ : 0 ≤ σ) (hσx : σ * Real.log x ≤ 1) (hq0 : 0 ≤ q) (hq2 : q ≤ 1)
    (hT0 : 0 < T) (hT1 : T ≤ 1) (hTlo : 1 ≤ T * Real.log ((w : ℝ) + 1))
    (hThi : T * Real.log ((w : ℝ) + 1) ≤ 2) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ Real.exp 143800 * Real.exp 7 * Real.exp 21
        * ((Real.log w) ^ (q * (2 * q - 1)) * (T ^ 2 * Real.log x) ^ q) := by
  haveI := hY.isProbabilityMeasure
  have hw2R : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw2
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hcast : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
  have hwxle : (w : ℝ) ≤ x := by linarith
  have hσw : σ * Real.log w ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hwxle) hσ) hσx
  have hlogw0 : (0 : ℝ) ≤ Real.log w := Real.log_nonneg (by linarith)
  have hlogpow0 : (0 : ℝ) ≤ (Real.log w) ^ (q * (2 * q - 1)) := Real.rpow_nonneg hlogw0 _
  have hchaos := integral_rpow_setIntegral_normSq_primesIco_le_mertens hY (z := w + 1) (x := x)
    (by omega) (by rw [hcast]; exact hwx) hσ hT0 hT1 (by rw [hcast]; exact hTlo) hq0
    (by linarith)
  refine le_trans (integral_rpow_setIntegral_normSq_block_le_of_chaos hY hw2 hwfl hσ hσw
    hq0 hq2 hT0 hThi hchaos) ?_
  -- `(e²¹·A)^q ≤ e²¹·A^q`
  have hsplit : (Real.exp 21 * (T ^ 2 * Real.log x)) ^ q
      = (Real.exp 21) ^ q * (T ^ 2 * Real.log x) ^ q :=
    Real.mul_rpow (Real.exp_pos 21).le (by positivity)
  have hexpq : (Real.exp 21) ^ q ≤ Real.exp 21 := by
    calc (Real.exp 21) ^ q ≤ (Real.exp 21) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.add_one_le_exp (21 : ℝ)]) (by linarith)
      _ = Real.exp 21 := Real.rpow_one _
  rw [hsplit]
  have hc0 : (0 : ℝ) ≤ Real.exp 143800 * (Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1))) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hlogpow0)
  have hA0 : (0 : ℝ) ≤ (T ^ 2 * Real.log x) ^ q := Real.rpow_nonneg (by positivity) _
  calc Real.exp 143800 * (Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1)))
        * ((Real.exp 21) ^ q * (T ^ 2 * Real.log x) ^ q)
      ≤ Real.exp 143800 * (Real.exp 7 * (Real.log w) ^ (q * (2 * q - 1)))
        * (Real.exp 21 * (T ^ 2 * Real.log x) ^ q) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact mul_le_mul_of_nonneg_right hexpq hA0
    _ = Real.exp 143800 * Real.exp 7 * Real.exp 21
        * ((Real.log w) ^ (q * (2 * q - 1)) * (T ^ 2 * Real.log x) ^ q) := by ring

/-! ### The sum over the windows

The `e`-adic windows are `(T_j/e, T_j]` with `T_j = e^{j-J}`, `1 ≤ j ≤ J`, so that `T_J = 1` and
the family covers `(e^{-J}, 1]`.  On the `j`-th the weight is at most `T_{j-1}^{-2} = e^{2(J+1-j)}`,
and

`e^{2(J+1-j)}·T_j² = e²`

exactly — **the weight cancels the `T²` of the block bound**, which is why the sum has no `T` in
it at all and reduces to `RMF.sum_exp_mul_one_add_mul_sqrt_rpow_neg_le`.

The per-block bound is a hypothesis here, already divided by the weight.  That keeps all of the
index arithmetic in one place and leaves the two block bounds — sharp and trivial — to be fed in
separately. -/

/-- **The windows, summed, for a block product and a decoupled weight.**  As
`RMF.integral_rpow_setIntegral_weight_le_of_blocks_of_sum`, for the product over `[y₀, n)` on any
line `Re s = ½ + σ > 0`, against `(c²+t²)^{-1}` with its own `c > 0`, over the windows
`1 ≤ j ≤ J_b` of `J ≥ J_b` blocks, with an arbitrary per-block factor `g`.  A band of
Proposition B (`RMF/Weighted/PropositionB.lean`) uses all four: its product is a block, its
numerator sits at `½ - c` while its weight is `(c²+t²)^{-1}`, and its windows stop at
`≍ 1/log y`. -/
theorem integral_rpow_setIntegral_weight_primesIco_le_of_blocks_of_sum {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (y₀ n : ℕ) {σ c q K D : ℝ} {g : ℕ → ℝ}
    (hσ : 0 < 1 / 2 + σ) (hc0 : 0 < c) (hq0 : 0 < q) (hq1 : q ≤ 1) (hK : 0 ≤ K)
    {J Jb : ℕ} (hJ : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hD : ∑ j ∈ Finset.Icc 1 Jb, g j ≤ D)
    (hblk : ∀ j ∈ Finset.Icc 1 Jb,
        (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - J) / Real.exp 1)
                (Real.exp ((j : ℝ) - J)),
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
          ≤ K * g j) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) (Real.exp ((Jb : ℝ) - J)),
        (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ n (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ K * D := by
  classical
  have hJR : (1 : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hJ
  have hJbJR : (Jb : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJbJ
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  -- the window endpoints, in the two forms the two lemmas use
  have hlow : ∀ j : ℕ, Real.exp ((j : ℝ) - J) / Real.exp 1 = Real.exp ((j : ℝ) - 1 - J) := by
    intro j
    rw [← Real.exp_sub]
    congr 1
    ring
  -- the weight
  have hρ0 : ∀ t : ℝ, (0 : ℝ) ≤ (c ^ 2 + t ^ 2)⁻¹ := fun t => by positivity
  have hρm : Measurable fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹ := by fun_prop
  have hρb : ∀ t : ℝ, (c ^ 2 + t ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ := by
    intro t
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith [sq_nonneg t])
  refine le_trans (integral_rpow_setIntegral_weight_le_sum_windows_primesIco hX y₀ n hσ hq0 hq1
    (Finset.Icc 1 Jb) (fun j => Real.exp ((j : ℝ) - J) / Real.exp 1)
    (fun j => Real.exp ((j : ℝ) - J)) (fun j => Real.exp (2 * ((J : ℝ) + 1 - j)))
    (A := 0) (B := 1) (Bρ := (c ^ 2)⁻¹) hρ0 hρm hρb measurableSet_Ioc ?_ ?_ ?_
    (fun j => (Real.exp_pos _).le) ?_ ?_) ?_
  -- `S ⊆ [0,1]`
  · intro t ht
    exact ⟨le_trans (Real.exp_pos _).le ht.1.le,
      le_trans ht.2 (Real.exp_le_one_iff.2 (by linarith))⟩
  -- each window sits in `[0,1]`
  · intro j hj
    rw [Finset.mem_Icc] at hj
    intro t ht
    have hjJ : (j : ℝ) ≤ (J : ℝ) := le_trans (by exact_mod_cast hj.2) hJbJR
    refine ⟨le_trans (by positivity) ht.1.le, le_trans ht.2 ?_⟩
    exact Real.exp_le_one_iff.2 (by linarith)
  -- the cover
  · intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht.1
    have hlt : Real.log t ≤ (Jb : ℝ) - J := by
      have h := Real.log_le_log ht0 ht.2
      rwa [Real.log_exp] at h
    have hgt : -(J : ℝ) < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos (-(J : ℝ))) ht.1
      rwa [Real.log_exp] at this
    have hu0 : (0 : ℝ) < (J : ℝ) + Real.log t := by linarith
    refine ⟨⌈(J : ℝ) + Real.log t⌉₊, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · exact Nat.ceil_pos.2 hu0
      · exact Nat.ceil_le.2 (by linarith)
    · have hce : ((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) < (J : ℝ) + Real.log t + 1 :=
        Nat.ceil_lt_add_one hu0.le
      have hge : (J : ℝ) + Real.log t ≤ ((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      constructor
      · rw [hlow]
        have : Real.exp (((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) - 1 - J) < Real.exp (Real.log t) :=
          Real.exp_lt_exp.2 (by linarith)
        rwa [Real.exp_log ht0] at this
      · have : Real.exp (Real.log t)
            ≤ Real.exp (((⌈(J : ℝ) + Real.log t⌉₊ : ℕ) : ℝ) - J) :=
          Real.exp_le_exp.2 (by linarith)
        rwa [Real.exp_log ht0] at this
  -- the windows are non-degenerate
  · intro j _
    rw [hlow]
    exact Real.exp_le_exp.2 (by linarith)
  -- the weight on the `j`-th window
  · intro j _ t ht
    rw [hlow] at ht
    have ht0 : (0 : ℝ) < Real.exp ((j : ℝ) - 1 - J) := Real.exp_pos _
    have htt : Real.exp ((j : ℝ) - 1 - J) < t := ht.1
    have hsq : Real.exp (2 * ((j : ℝ) - 1 - J)) < t ^ 2 := by
      rw [show (2 : ℝ) * ((j : ℝ) - 1 - J) = ((j : ℝ) - 1 - J) + ((j : ℝ) - 1 - J) by ring,
        Real.exp_add]
      nlinarith [ht0, htt]
    have hinv : (Real.exp (2 * ((J : ℝ) + 1 - j)))⁻¹ = Real.exp (2 * ((j : ℝ) - 1 - J)) := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [← inv_inv (Real.exp (2 * ((J : ℝ) + 1 - j))), hinv]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by
      linarith [sq_nonneg c, hsq])
  -- the sum
  · refine le_trans (Finset.sum_le_sum hblk) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hK
    exact hD

/-- **The windows, summed.**  For `σ > 0` and `0 < q ≤ 1`, given a bound
`K·e^{(j-J)α}(1+β√j)^{-q}` on the weighted `j`-th window for every `1 ≤ j ≤ J`,
`E[(∫_{e^{-J}}^{1} |σ+it|^{-2}‖F_n(½+σ+it)‖²dt)^q] ≤ K·D` whenever `D` bounds the sum of those
factors over `1 ≤ j ≤ J`.  The block `[0, n)`, `c = σ`, `J_b = J` case of
`RMF.integral_rpow_setIntegral_weight_primesIco_le_of_blocks_of_sum`. -/
theorem integral_rpow_setIntegral_weight_le_of_blocks_of_sum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ q α β K D : ℝ}
    (hσ0 : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hK : 0 ≤ K)
    {J : ℕ} (hJ : 1 ≤ J)
    (hD : ∑ j ∈ Finset.Icc 1 J,
        Real.exp (((j : ℝ) - (J : ℝ)) * α) * (1 + β * Real.sqrt j) ^ (-q) ≤ D)
    (hblk : ∀ j ∈ Finset.Icc 1 J,
        (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - J) / Real.exp 1)
                (Real.exp ((j : ℝ) - J)),
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
          ≤ K * (Real.exp (((j : ℝ) - J) * α) * (1 + β * Real.sqrt j) ^ (-q))) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ K * D := by
  have h := integral_rpow_setIntegral_weight_primesIco_le_of_blocks_of_sum hX 0 n (σ := σ)
    (c := σ) (q := q) (K := K) (D := D)
    (g := fun j => Real.exp (((j : ℝ) - (J : ℝ)) * α) * (1 + β * Real.sqrt j) ^ (-q))
    (by linarith) hσ0 hq0 hq1 hK (J := J) (Jb := J) hJ le_rfl hD
    (by simpa only [randomEulerProductIco_zero] using hblk)
  simpa only [randomEulerProductIco_zero, sub_self, Real.exp_zero] using h

/-- **The window sum at the crude depth bound**, `2J·(1+β√J)^{-q}`: the geometric factor is
discarded and every one of the `J` windows is charged the last one's saving. -/
theorem integral_rpow_setIntegral_weight_le_of_blocks {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ q α β K : ℝ}
    (hσ0 : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    {J : ℕ} (hJ : 1 ≤ J)
    (hblk : ∀ j ∈ Finset.Icc 1 J,
        (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - J) / Real.exp 1)
                (Real.exp ((j : ℝ) - J)),
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
          ≤ K * (Real.exp (((j : ℝ) - J) * α) * (1 + β * Real.sqrt j) ^ (-q))) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ K * (2 * (J : ℝ) * (1 + β * Real.sqrt J) ^ (-q)) :=
  integral_rpow_setIntegral_weight_le_of_blocks_of_sum hX n hσ0 hq0 hq1 hK hJ
    (sum_exp_mul_one_add_mul_sqrt_rpow_neg_le hα hβ hq0.le hq1 hJ) hblk

/-- **The window sum with the geometric factor kept**, `6(1+α⁻¹)·(1+β√J)^{-q}`.

This is the bound that removes the leading `log log x` from the final statement: with
`α = q(1-2q)` the factor `1+α⁻¹` is bounded for `q` away from `0` and `½`, and taken together
with the crude bound above it gives `min{J, 1+α⁻¹}`. -/
theorem integral_rpow_setIntegral_weight_le_of_blocks_geom {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ q α β K : ℝ}
    (hσ0 : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hα : 0 < α) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    {J : ℕ} (hJ : 1 ≤ J)
    (hblk : ∀ j ∈ Finset.Icc 1 J,
        (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - J) / Real.exp 1)
                (Real.exp ((j : ℝ) - J)),
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
          ≤ K * (Real.exp (((j : ℝ) - J) * α) * (1 + β * Real.sqrt j) ^ (-q))) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) 1,
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ K * (6 * (1 + α⁻¹) * (1 + β * Real.sqrt J) ^ (-q)) :=
  integral_rpow_setIntegral_weight_le_of_blocks_of_sum hX n hσ0 hq0 (by linarith) hK hJ
    (sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_geom hα hβ hq0.le hq1 hJ) hblk

/-- **The window sum above the critical exponent, for a block product and a decoupled weight.**
Over the windows `1 ≤ j ≤ J_b` of a family of `J ≥ J_b` blocks, with the geometric factor
`e^{(J_b-j)γ}` counted from the top of the sub-range: `≤ K·3·e^{J_b γ}·m·(1+β√m)^{-q}` at
`m = min{J_b, ⌈γ^{-1}⌉}`. -/
theorem integral_rpow_setIntegral_weight_primesIco_le_of_blocks_above {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (y₀ n : ℕ) {σ c q γ β K : ℝ}
    (hσ : 0 < 1 / 2 + σ) (hc0 : 0 < c) (hq0 : 0 < q) (hq1 : q ≤ 1) (hγ : 0 < γ) (hβ : 0 ≤ β)
    (hK : 0 ≤ K) {J Jb : ℕ} (hJ : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hblk : ∀ j ∈ Finset.Icc 1 Jb,
        (Real.exp (2 * ((J : ℝ) + 1 - j))) ^ q
          * (∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - J) / Real.exp 1)
                (Real.exp ((j : ℝ) - J)),
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ n
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
          ≤ K * (Real.exp (((Jb : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q))) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-(J : ℝ))) (Real.exp ((Jb : ℝ) - J)),
        (c ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ n (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ K * (3 * Real.exp ((Jb : ℝ) * γ) * ((min Jb ⌈γ⁻¹⌉₊ : ℕ) : ℝ)
          * (1 + β * Real.sqrt ((min Jb ⌈γ⁻¹⌉₊ : ℕ) : ℝ)) ^ (-q)) :=
  integral_rpow_setIntegral_weight_primesIco_le_of_blocks_of_sum hX y₀ n
    (g := fun j => Real.exp (((Jb : ℝ) - j) * γ) * (1 + β * Real.sqrt j) ^ (-q))
    hσ hc0 hq0 hq1 hK hJ hJbJ
    (sum_exp_mul_one_add_mul_sqrt_rpow_neg_le_above_min hγ hβ hq0.le hq1 hJ) hblk

end RMF
