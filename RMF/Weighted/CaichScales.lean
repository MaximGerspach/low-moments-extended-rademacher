/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CaichReduction

/-!
# The scales of the dilated line integral, Rademacher case

`RMF.dilatedLineIntegral` weighs `|F(½+it)|²` by
`|λ^s − 1|²/|s|²`, which is at most `2(log λ)²` everywhere (`RMF.normSq_cpow_half_sub_one_le`) and
at most `7/t²` (`RMF.normSq_cpow_half_sub_one_le_seven`).  Splitting the heights at `M₀` and then
dyadically,

`dilatedLineIntegral ≤ 4(log λ)² S(M₀) + 14 ∑_{j<J} (2^j M₀)^{−2} S(2^{j+1} M₀)
  + 14 ∫_{h > 2^J M₀} |F(½+ih)|²/h² dh`,

`S(M) = ∫_0^M |F(½+ih)|² dh` (`RMF.lineMass`).  The negative heights are the positive ones
reflected: the Rademacher values are real, so `|F(½−ih)| = |F(½+ih)|`
(`RMF.norm_randomEulerProductIco_sqfree_heightLine_neg`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `S(M) = ∫_0^M ‖F(½+ih)‖² dh`, the mass of the Euler product on the critical line up to height
`M`. -/
noncomputable def lineMass (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ) (ω : Ω) : ℝ :=
  ∫ h in Set.Ioc (0 : ℝ) M, ‖randomEulerProduct F N (shiftLine 0 h) ω‖ ^ 2

lemma shiftLine_zero_eq (t : ℝ) :
    shiftLine 0 t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  rw [shiftLine, add_zero]

/-! ### Reflection -/

omit [MeasurableSpace Ω] in
/-- **The dilated integrand is even** on a path with real values: the weight depends on `t` through
`cos(t log λ)`, and `|F(½−it)| = |F(½+it)|`. -/
lemma dilatedIntegrand_neg_sqfree {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hω : ∀ p ∈ primesIco 0 N, (starRingEnd ℂ) (X p ω) = X p ω) {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ‖(l : ℂ) ^ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2
        * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω (-t)
      = ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
        * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t := by
  have hw : ‖(l : ℂ) ^ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2
      = ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 := by
    rw [normSq_cpow_half_sub_one_eq hl, normSq_cpow_half_sub_one_eq hl, mul_neg, Real.cos_neg]
  have hF : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ω‖
      = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ := by
    have h := norm_randomEulerProductIco_sqfree_heightLine_neg (σ := 1 / 2) (h := t) hω
    rw [randomEulerProductIco_zero, randomEulerProductIco_zero] at h
    exact h
  have hc : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I
      = (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  have hs : ‖((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
      = ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [hc, RCLike.norm_conj]
  rw [hw, lineDivSqOf, lineDivSqOf, norm_div, norm_div, hF, hs]

omit [MeasurableSpace Ω] in
/-- **The dilated line integral is twice its positive half**, on a path with real values. -/
lemma dilatedLineIntegral_eq_two_mul_Ioi_sqfree {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hω : ∀ p ∈ primesIco 0 N, (starRingEnd ℂ) (X p ω) = X p ω) {l : ℝ} (hl : 0 < l) :
    dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
      = 2 * ∫ t in Set.Ioi (0 : ℝ), ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
          * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t := by
  rw [dilatedLineIntegral, ← integral_comp_abs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, dilatedIntegrand_neg_sqfree hω hl t]

/-! ### The dyadic split of a half line -/

/-- Splitting a half-line integral at `b ≥ a`. -/
lemma setIntegral_Ioi_eq_Ioc_add_Ioi {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Set.Ioi a)) :
    ∫ t in Set.Ioi a, g t = (∫ t in Set.Ioc a b, g t) + ∫ t in Set.Ioi b, g t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hab]
  exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi hab))

/-- **The dyadic split of a half-line integral.**  If `g ≤ 7k/t²` beyond `M₀ > 0`, with `k ≥ 0`
integrable on bounded intervals, then for every `J`

`∫_{t > M₀} g ≤ 7 ∑_{j<J} (2^j M₀)^{−2} ∫_0^{2^{j+1}M₀} k + ∫_{t > 2^J M₀} g`. -/
lemma setIntegral_Ioi_le_dyadic {g k : ℝ → ℝ} {M₀ : ℝ} (hM₀ : 0 < M₀) (hk0 : ∀ t, 0 ≤ k t)
    (hgk : ∀ t, M₀ < t → g t ≤ 7 * (k t / t ^ 2)) (hgi : IntegrableOn g (Set.Ioi M₀))
    (hki : ∀ b, IntegrableOn k (Set.Ioc 0 b)) (J : ℕ) :
    ∫ t in Set.Ioi M₀, g t
      ≤ 7 * (∑ j ∈ Finset.range J,
            ((2 ^ j * M₀) ^ 2)⁻¹ * ∫ t in Set.Ioc 0 (2 ^ (j + 1) * M₀), k t)
        + ∫ t in Set.Ioi (2 ^ J * M₀), g t := by
  induction J with
  | zero => simp
  | succ J ih =>
    have ha0 : 0 < 2 ^ J * M₀ := mul_pos (by positivity) hM₀
    have hMa : M₀ ≤ 2 ^ J * M₀ := le_mul_of_one_le_left hM₀.le (one_le_pow₀ (by norm_num))
    have hgia : IntegrableOn g (Set.Ioi (2 ^ J * M₀)) := hgi.mono_set (Set.Ioi_subset_Ioi hMa)
    have hpiece : (∫ t in Set.Ioc (2 ^ J * M₀) (2 * (2 ^ J * M₀)), g t)
        ≤ 7 * (((2 ^ J * M₀) ^ 2)⁻¹ * ∫ t in Set.Ioc 0 (2 * (2 ^ J * M₀)), k t) := by
      have hkIoc : IntegrableOn k (Set.Ioc (2 ^ J * M₀) (2 * (2 ^ J * M₀))) :=
        (hki _).mono_set (Set.Ioc_subset_Ioc_left ha0.le)
      calc (∫ t in Set.Ioc (2 ^ J * M₀) (2 * (2 ^ J * M₀)), g t)
          ≤ ∫ t in Set.Ioc (2 ^ J * M₀) (2 * (2 ^ J * M₀)), 7 * (((2 ^ J * M₀) ^ 2)⁻¹ * k t) := by
            refine setIntegral_mono_on (hgia.mono_set Set.Ioc_subset_Ioi_self)
              ((hkIoc.const_mul _).const_mul _) measurableSet_Ioc fun t ht => ?_
            have hta : 2 ^ J * M₀ < t := ht.1
            refine (hgk t (lt_of_le_of_lt hMa hta)).trans ?_
            have h1 : k t / t ^ 2 ≤ ((2 ^ J * M₀) ^ 2)⁻¹ * k t := by
              rw [div_eq_inv_mul]
              exact mul_le_mul_of_nonneg_right
                (inv_anti₀ (pow_pos ha0 2) (pow_le_pow_left₀ ha0.le hta.le 2)) (hk0 t)
            linarith
        _ = 7 * (((2 ^ J * M₀) ^ 2)⁻¹ * ∫ t in Set.Ioc (2 ^ J * M₀) (2 * (2 ^ J * M₀)), k t) := by
            rw [integral_const_mul, integral_const_mul]
        _ ≤ 7 * (((2 ^ J * M₀) ^ 2)⁻¹ * ∫ t in Set.Ioc 0 (2 * (2 ^ J * M₀)), k t) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (by norm_num)
            exact setIntegral_mono_set (hki _) (Filter.Eventually.of_forall fun t => hk0 t)
              (LE.le.eventuallyLE (Set.Ioc_subset_Ioc_left ha0.le))
    have hsplit := setIntegral_Ioi_eq_Ioc_add_Ioi (g := g) (a := 2 ^ J * M₀)
      (b := 2 * (2 ^ J * M₀)) (by linarith) hgia
    rw [hsplit] at ih
    rw [Finset.sum_range_succ, show (2 : ℝ) ^ (J + 1) * M₀ = 2 * (2 ^ J * M₀) by ring]
    linarith [hpiece, ih]

/-! ### The pathwise bound at the scales -/

omit [MeasurableSpace Ω] in
/-- On the critical line `lineDivSqOf` is `|F(½+it)|²/(¼ + t²)`. -/
lemma lineDivSqOf_half_eq (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (ω : Ω) (t : ℝ) :
    lineDivSqOf (1 / 2) F N ω t
      = ‖randomEulerProduct F N (shiftLine 0 t) ω‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hs : ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    norm_num
  rw [lineDivSqOf, norm_div, div_pow, hs, shiftLine_zero_eq]

omit [MeasurableSpace Ω] in
/-- **The dilated line integral at its scales**, on a path whose values are real and bounded by
one: for `1 ≤ λ ≤ 2`, `M₀ > 0` and every `J`,
`dilatedLineIntegral ≤ 4(log λ)² S(M₀) + 14 ∑_{j<J} (2^j M₀)^{−2} S(2^{j+1}M₀)
  + 14 ∫_{t > 2^J M₀} |F(½+it)|²/t² dt`.
The reflection halves the line; the weight is `≤ 2(log λ)²(¼+t²)` below `M₀` and `≤ 7` above,
where `RMF.setIntegral_Ioi_le_dyadic` splits the heights. -/
theorem dilatedLineIntegral_le_scales_sqfree {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hre : ∀ p ∈ primesIco 0 N, (starRingEnd ℂ) (X p ω) = X p ω)
    (hbd : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) {l : ℝ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2)
    {M₀ : ℝ} (hM₀ : 0 < M₀) (J : ℕ) :
    dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
      ≤ 4 * Real.log l ^ 2 * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω
        + 14 * (∑ j ∈ Finset.range J, ((2 ^ j * M₀) ^ 2)⁻¹
            * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω)
        + 14 * ∫ t in Set.Ioi (2 ^ J * M₀),
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              (shiftLine 0 t) ω‖ ^ 2 / t ^ 2 := by
  have hl0 : 0 < l := by linarith
  have hJ0 : 0 < 2 ^ J * M₀ := mul_pos (by positivity) hM₀
  have hmeasF : Measurable fun t : ℝ =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω :=
    measurable_randomEulerProduct_sqfree_line (1 / 2 + 0)
  have hkb : ∀ t : ℝ,
      ‖‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖
        ^ 2‖ ≤ eulerBound N ^ 2 := fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_randomEulerProduct_sqfree_le hbd (by simp)) 2
  -- the integrand is integrable
  have hw : Continuous fun t : ℝ => ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 := by
    have hl0' : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl0.ne'
    have hcp : Continuous fun t : ℝ => (l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hl0')
    exact (hcp.sub continuous_const).norm.pow 2
  have hLi := integrable_lineDivSqOf (σ := 1 / 2) (by norm_num)
    (measurable_randomEulerProduct_sqfree_line (X := X) (N := N) (ω := ω) (1 / 2))
    (fun t => norm_randomEulerProduct_sqfree_le hbd (by norm_num))
  have hgi : Integrable (fun t : ℝ => ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
      * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t) :=
    hLi.bdd_mul hw.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact normSq_cpow_half_sub_one_le_seven hl1 hl2 t)
  have hki : ∀ b : ℝ, IntegrableOn (fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖ ^ 2)
      (Set.Ioc 0 b) := fun b =>
    Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (hmeasF.norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall hkb)
  have hkt : IntegrableOn (fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖ ^ 2
        / t ^ 2) (Set.Ioi (2 ^ J * M₀)) := by
    have hinv : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (2 ^ J * M₀)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hJ0
    have hid : ∀ t ∈ Set.Ioi (2 ^ J * M₀),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖
            ^ 2 * t ^ (-2 : ℝ)
          = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              (shiftLine 0 t) ω‖ ^ 2 / t ^ 2 := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans hJ0 (Set.mem_Ioi.1 ht)
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
        div_eq_mul_inv]
    exact IntegrableOn.congr_fun (hinv.bdd_mul (hmeasF.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall hkb)) hid measurableSet_Ioi
  -- the two pointwise bounds on the weight
  have hP2 : ∀ t : ℝ, ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
      * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t
      ≤ 2 * Real.log l ^ 2 * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 t) ω‖ ^ 2 := fun t => by
    have hq : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
    rw [lineDivSqOf_half_eq]
    set K : ℝ := ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      (shiftLine 0 t) ω‖ ^ 2 with hKdef
    calc ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 * (K / (1 / 4 + t ^ 2))
        ≤ 2 * Real.log l ^ 2 * (1 / 4 + t ^ 2) * (K / (1 / 4 + t ^ 2)) :=
          mul_le_mul_of_nonneg_right (normSq_cpow_half_sub_one_le hl1 hl2 t)
            (div_nonneg (sq_nonneg _) hq.le)
      _ = 2 * Real.log l ^ 2 * (K * ((1 / 4 + t ^ 2) / (1 / 4 + t ^ 2))) := by ring
      _ = 2 * Real.log l ^ 2 * K := by rw [div_self hq.ne', mul_one]
  have hP3 : ∀ t : ℝ, 0 < t → ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
      * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t
      ≤ 7 * (‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 t) ω‖ ^ 2 / t ^ 2) := fun t ht => by
    rw [lineDivSqOf_half_eq]
    have h1 : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 t) ω‖ ^ 2 / (1 / 4 + t ^ 2)
        ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 t) ω‖ ^ 2 / t ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos ht 2) (by linarith)
    exact mul_le_mul (normSq_cpow_half_sub_one_le_seven hl1 hl2 t) h1
      (div_nonneg (sq_nonneg _) (by positivity)) (by norm_num)
  -- the reflection, the split at `M₀`, and the three pieces
  rw [dilatedLineIntegral_eq_two_mul_Ioi_sqfree hre hl0,
    setIntegral_Ioi_eq_Ioc_add_Ioi hM₀.le (hgi.integrableOn (s := Set.Ioi (0 : ℝ)))]
  have h1 : (∫ t in Set.Ioc (0 : ℝ) M₀,
        ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
          * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t)
      ≤ 2 * Real.log l ^ 2 * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω := by
    rw [lineMass, ← integral_const_mul]
    exact setIntegral_mono_on hgi.integrableOn ((hki M₀).const_mul _) measurableSet_Ioc
      fun t _ => hP2 t
  have h2 : (∫ t in Set.Ioi M₀,
        ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
          * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t)
      ≤ 7 * (∑ j ∈ Finset.range J, ((2 ^ j * M₀) ^ 2)⁻¹
            * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω)
        + ∫ t in Set.Ioi (2 ^ J * M₀),
            ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
              * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t :=
    setIntegral_Ioi_le_dyadic (k := fun t =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 t) ω‖ ^ 2)
      hM₀ (fun t => sq_nonneg _) (fun t ht => hP3 t (lt_trans hM₀ ht)) hgi.integrableOn hki J
  have h3 : (∫ t in Set.Ioi (2 ^ J * M₀),
        ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
          * lineDivSqOf (1 / 2) (fun ω => squarefreeExtension fun p => X p ω) N ω t)
      ≤ 7 * ∫ t in Set.Ioi (2 ^ J * M₀),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (shiftLine 0 t) ω‖ ^ 2 / t ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hgi.integrableOn (hkt.const_mul _) measurableSet_Ioi
      fun t ht => hP3 t (lt_trans hJ0 ht)
  linarith [h1, h2, h3]

/-! ### The pieces are measurable, and the tail is small in mean -/

/-- **`S(M)` is measurable in `ω`**, Rademacher case. -/
lemma measurable_lineMass_sqfree {X : ℕ → Ω → ℂ} (hX : ∀ p : ℕ, p.Prime → Measurable (X p))
    (N : ℕ) (M : ℝ) :
    Measurable fun ω => lineMass (fun ω => squarefreeExtension fun p => X p ω) N M ω := by
  have hj : Measurable fun z : Ω × ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 z.2) z.1‖
        ^ 2 :=
    (measurable_randomEulerProduct_sqfree_uncurry hX (1 / 2 + 0) N).norm.pow_const 2
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) M)) hj.stronglyMeasurable).measurable

omit [MeasurableSpace Ω] in
lemma lineMass_nonneg (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ) (ω : Ω) :
    0 ≤ lineMass F N M ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _

omit [MeasurableSpace Ω] in
/-- `S(M) ≤ M·eulerBound²` on a path with `|X_p| ≤ 1`. -/
lemma lineMass_sqfree_le {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω}
    (hbd : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M) :
    lineMass (fun ω => squarefreeExtension fun p => X p ω) N M ω ≤ M * eulerBound N ^ 2 := by
  have hmeasF : Measurable fun t : ℝ =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω :=
    measurable_randomEulerProduct_sqfree_line (1 / 2 + 0)
  have hkb : ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖ ^ 2
        ≤ eulerBound N ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_randomEulerProduct_sqfree_le hbd (by simp)) 2
  have hint : IntegrableOn (fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖ ^ 2)
      (Set.Ioc 0 M) :=
    Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (hmeasF.norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hkb t)
  calc lineMass (fun ω => squarefreeExtension fun p => X p ω) N M ω
      ≤ ∫ _t in Set.Ioc (0 : ℝ) M, eulerBound N ^ 2 :=
        setIntegral_mono_on hint
          (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioc fun t _ => hkb t
    _ = M * eulerBound N ^ 2 := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hM, sub_zero]

/-- **`S(M)^q` is integrable**, Rademacher case. -/
lemma integrable_lineMass_rpow_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {M q : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) :
    Integrable (fun ω =>
      lineMass (fun ω => squarefreeExtension fun p => X p ω) N M ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw N
  have hm := measurable_lineMass_sqfree (fun p hp => hX.measurable p hp) N M
  refine (memLp_top_of_bound (hm.pow_const q).aestronglyMeasurable
    ((M * eulerBound N ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  have hnn := lineMass_nonneg (fun ω => squarefreeExtension fun p => X p ω) N M ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
  exact Real.rpow_le_rpow hnn (lineMass_sqfree_le hω hM) hq

/-- `∫_{t > T} |F(½+it)|²/t² dt`, the far tail of the dilated line integral. -/
noncomputable def lineTail (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (T : ℝ) (ω : Ω) : ℝ :=
  ∫ t in Set.Ioi T, ‖randomEulerProduct F N (shiftLine 0 t) ω‖ ^ 2 / t ^ 2

omit [MeasurableSpace Ω] in
lemma lineTail_nonneg (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (T : ℝ) (ω : Ω) :
    0 ≤ lineTail F N T ω :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The tail, integrable on the product**: `(ω, t) ↦ |F(½+it)|²/t²` on `Ω × (T, ∞)`, dominated
by `eulerBound²/t²` on the paths with `|X_p| ≤ 1`. -/
lemma integrable_uncurry_lineTail_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖ ^ 2
        / t ^ 2) (μ.prod (volume.restrict (Set.Ioi T))) := by
  haveI := hX.isProbabilityMeasure
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw N
  have hinv : IntegrableOn (fun t : ℝ => eulerBound N ^ 2 / t ^ 2) (Set.Ioi T) := by
    have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul
      (eulerBound N ^ 2)
    have hid : ∀ t ∈ Set.Ioi T, eulerBound N ^ 2 * t ^ (-2 : ℝ) = eulerBound N ^ 2 / t ^ 2 := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans hT (Set.mem_Ioi.1 ht)
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
        div_eq_mul_inv]
    exact IntegrableOn.congr_fun h hid measurableSet_Ioi
  have hjm : Measurable fun z : Ω × ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 z.2) z.1‖
        ^ 2 / z.2 ^ 2 :=
    ((measurable_randomEulerProduct_sqfree_uncurry (fun p hp => hX.measurable p hp)
      (1 / 2 + 0) N).norm.pow_const 2).div (measurable_snd.pow_const 2)
  refine Integrable.mono' (hinv.comp_snd μ) hjm.aestronglyMeasurable ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ)
    (ν := volume.restrict (Set.Ioi T))).ae hae] with z hz
  change ‖‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      (shiftLine 0 z.2) z.1‖ ^ 2 / z.2 ^ 2‖ ≤ eulerBound N ^ 2 / z.2 ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_randomEulerProduct_sqfree_le hz (by simp)) 2)
    (sq_nonneg _)

/-- **The expected tail**: `E ∫_{t>T} |F(½+it)|²/t² dt = E|F(½)|²/T`, by Fubini and the height
independence of the Rademacher second moment
(`RMF.IsRademacherRMF.integral_normSq_shiftLine_eq`). -/
theorem integral_lineTail_sqfree_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ∫ ω, lineTail (fun ω => squarefreeExtension fun p => X p ω) N T ω ∂μ
      = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 0) ω‖ ^ 2 ∂μ) / T := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hid : ∀ t ∈ Set.Ioi T,
      (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 t) ω‖ ^ 2 / t ^ 2 ∂μ)
        = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (shiftLine 0 0) ω‖ ^ 2 ∂μ) * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hT (Set.mem_Ioi.1 ht)
    rw [integral_div, hRa.integral_normSq_shiftLine_eq N t 0,
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
      div_eq_mul_inv]
  calc ∫ ω, lineTail (fun ω => squarefreeExtension fun p => X p ω) N T ω ∂μ
      = ∫ t in Set.Ioi T, ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          N (shiftLine 0 t) ω‖ ^ 2 / t ^ 2 ∂μ :=
        integral_integral_swap (integrable_uncurry_lineTail_sqfree hX N hT)
    _ = ∫ t in Set.Ioi T, (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          N (shiftLine 0 0) ω‖ ^ 2 ∂μ) * t ^ (-2 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioi hid
    _ = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 0) ω‖ ^ 2 ∂μ) / T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT,
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, div_eq_mul_inv]
        ring

/-! ### The moments at the scales -/

/-- **`lineTail` is integrable, and so is its `q`-th power**, Rademacher case: Fubini gives the
first, and the bound `eulerBound²/T` on the paths with `|X_p| ≤ 1` the second. -/
lemma integrable_lineTail_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {T q : ℝ} (hT : 0 < T) (hq : 0 ≤ q) :
    Integrable (fun ω => lineTail (fun ω => squarefreeExtension fun p => X p ω) N T ω) μ
      ∧ Integrable (fun ω =>
          lineTail (fun ω => squarefreeExtension fun p => X p ω) N T ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have h1 : Integrable (fun ω => lineTail (fun ω => squarefreeExtension fun p => X p ω) N T ω) μ :=
    (integrable_uncurry_lineTail_sqfree hX N hT).integral_prod_left
  refine ⟨h1, ?_⟩
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw N
  have hinv : IntegrableOn (fun t : ℝ => eulerBound N ^ 2 * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul _
  have hval : (∫ t in Set.Ioi T, eulerBound N ^ 2 * t ^ (-2 : ℝ)) = eulerBound N ^ 2 / T := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT,
      show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, div_eq_mul_inv]
    ring
  refine (memLp_top_of_bound (h1.aemeasurable.pow_const q).aestronglyMeasurable
    ((eulerBound N ^ 2 / T) ^ q) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  have hle : ∀ t ∈ Set.Ioi T,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 t) ω‖
          ^ 2 / t ^ 2
        ≤ eulerBound N ^ 2 * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hT (Set.mem_Ioi.1 ht)
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_randomEulerProduct_sqfree_le hω (by simp)) 2)
      (sq_nonneg _)
  have hnn := lineTail_nonneg (fun ω => squarefreeExtension fun p => X p ω) N T ω
  have hbd : lineTail (fun ω => squarefreeExtension fun p => X p ω) N T ω
      ≤ eulerBound N ^ 2 / T := by
    rw [← hval]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (sq_nonneg _)) hinv
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hle))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn q)]
  exact Real.rpow_le_rpow hnn hbd hq

/-- **The moments of the dilated line integral at its scales**, Rademacher case.  For `0 < q ≤ 1`,
`1 ≤ λ ≤ 2`, `M₀ > 0` and every `J`, with `c = (2π)^{−1}`,
`E[(c·dilatedLineIntegral)^q] ≤ (4c(log λ)²)^q E[S(M₀)^q]
  + ∑_{j<J} (14c(2^j M₀)^{−2})^q E[S(2^{j+1}M₀)^q] + (14c)^q (E|F(½)|²/(2^J M₀))^q`:
`RMF.dilatedLineIntegral_le_scales_sqfree` on the paths with real values bounded by one,
subadditivity of `t ↦ t^q`, and Jensen for the tail (`RMF.integral_lineTail_sqfree_eq`). -/
theorem integral_rpow_dilatedLineIntegral_le_scales_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {l q M₀ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hl1 : 1 ≤ l) (hl2 : l ≤ 2) (hM₀ : 0 < M₀) (J : ℕ) :
    ∫ ω, ((2 * Real.pi)⁻¹
        * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω) ^ q ∂μ
      ≤ ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
          * (∫ ω, lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω ^ q ∂μ)
        + ∑ j ∈ Finset.range J, ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
          * (∫ ω, lineMass (fun ω => squarefreeExtension fun p => X p ω) N
              (2 ^ (j + 1) * M₀) ω ^ q ∂μ)
        + ((2 * Real.pi)⁻¹ * 14) ^ q
          * ((∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              (shiftLine 0 0) ω‖ ^ 2 ∂μ) / (2 ^ J * M₀)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hJ0 : 0 < 2 ^ J * M₀ := mul_pos (by positivity) hM₀
  have hc : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  have hA : 0 ≤ (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2) := mul_nonneg hc (by positivity)
  have hB : ∀ j : ℕ, 0 ≤ (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹) := fun j =>
    mul_nonneg hc (by positivity)
  have hC : 0 ≤ (2 * Real.pi)⁻¹ * 14 := mul_nonneg hc (by norm_num)
  -- integrability of the right-hand side
  have hTl := integrable_lineTail_sqfree hX N hJ0 hq0.le
  have h1 : Integrable (fun ω => ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
      * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω ^ q) μ :=
    (integrable_lineMass_rpow_sqfree hX N hM₀.le hq0.le).const_mul _
  have hSj : ∀ j ∈ Finset.range J, Integrable (fun ω =>
      ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
        * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q) μ :=
    fun j _ => (integrable_lineMass_rpow_sqfree hX N (mul_pos (by positivity) hM₀).le
      hq0.le).const_mul _
  have h2 : Integrable (fun ω => ∑ j ∈ Finset.range J,
      ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
        * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q) μ :=
    integrable_finsetSum _ hSj
  have h3 : Integrable (fun ω => ((2 * Real.pi)⁻¹ * 14) ^ q
      * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω ^ q) μ :=
    hTl.2.const_mul _
  have h12 : Integrable (fun ω => ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
      * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω ^ q
      + ∑ j ∈ Finset.range J, ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
        * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q) μ :=
    h1.add h2
  have h123 : Integrable (fun ω => ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
      * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω ^ q
      + ∑ j ∈ Finset.range J, ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
        * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q
      + ((2 * Real.pi)⁻¹ * 14) ^ q
        * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω ^ q) μ :=
    h12.add h3
  -- the pathwise bound, raised to the power `q`
  have hre := ae_forall_conj_eq_primesIco hX conj_eq_rademacherLaw 0 N
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw N
  have hpt : ∀ᵐ ω ∂μ, ((2 * Real.pi)⁻¹
        * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω) ^ q
      ≤ ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω ^ q
        + ∑ j ∈ Finset.range J, ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q
        + ((2 * Real.pi)⁻¹ * 14) ^ q
          * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω ^ q := by
    filter_upwards [hre, hae] with ω hω1 hω2
    have hsc : dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
        ≤ 4 * Real.log l ^ 2 * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω
          + 14 * (∑ j ∈ Finset.range J, ((2 ^ j * M₀) ^ 2)⁻¹
              * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω)
          + 14 * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω :=
      dilatedLineIntegral_le_scales_sqfree hω1 hω2 hl1 hl2 hM₀ J
    have hS0nn := lineMass_nonneg (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω
    have hSnn : ∀ j : ℕ, 0 ≤ lineMass (fun ω => squarefreeExtension fun p => X p ω) N
        (2 ^ (j + 1) * M₀) ω := fun j => lineMass_nonneg _ _ _ _
    have hTnn := lineTail_nonneg (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω
    have hsum : (2 * Real.pi)⁻¹ * (14 * ∑ j ∈ Finset.range J, ((2 ^ j * M₀) ^ 2)⁻¹
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω)
        = ∑ j ∈ Finset.range J, (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hlin : (2 * Real.pi)⁻¹
          * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
        ≤ (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)
            * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω
          + ∑ j ∈ Finset.range J, (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)
            * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω
          + (2 * Real.pi)⁻¹ * 14
            * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω := by
      rw [← hsum]
      calc (2 * Real.pi)⁻¹
            * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω
          ≤ (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2
              * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω
            + 14 * (∑ j ∈ Finset.range J, ((2 ^ j * M₀) ^ 2)⁻¹
                * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω)
            + 14 * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω) :=
            mul_le_mul_of_nonneg_left hsc hc
        _ = (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)
              * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω
            + (2 * Real.pi)⁻¹ * (14 * ∑ j ∈ Finset.range J, ((2 ^ j * M₀) ^ 2)⁻¹
              * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω)
            + (2 * Real.pi)⁻¹ * 14
              * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω := by
            ring
    have hA' : 0 ≤ (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)
        * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω := mul_nonneg hA hS0nn
    have hB' : ∀ j : ℕ, 0 ≤ (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)
        * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω :=
      fun j => mul_nonneg (hB j) (hSnn j)
    have hC' : 0 ≤ (2 * Real.pi)⁻¹ * 14
        * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω :=
      mul_nonneg hC hTnn
    have hD0 : 0 ≤ (2 * Real.pi)⁻¹
        * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω :=
      mul_nonneg hc (dilatedLineIntegral_nonneg _ _ _ _)
    have hmid : (∑ j ∈ Finset.range J, (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω) ^ q
        ≤ ∑ j ∈ Finset.range J, ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q :=
      (rpow_sum_le_sum_rpow (Finset.range J) hB' hq0 hq1).trans
        (le_of_eq (Finset.sum_congr rfl fun j _ => Real.mul_rpow (hB j) (hSnn j)))
    refine (Real.rpow_le_rpow hD0 hlin hq0.le).trans ?_
    refine (rpow_add_add_le_add_add_rpow hA' (Finset.sum_nonneg fun j _ => hB' j) hC'
      hq0.le hq1).trans ?_
    rw [Real.mul_rpow hA hS0nn, Real.mul_rpow hC hTnn]
    exact add_le_add (add_le_add le_rfl hmid) le_rfl
  -- integrate, and Jensen for the tail
  have hint : (∫ ω, ((2 * Real.pi)⁻¹
        * dilatedLineIntegral (fun ω => squarefreeExtension fun p => X p ω) N l ω) ^ q ∂μ)
      ≤ ∫ ω, (((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N M₀ ω ^ q
        + ∑ j ∈ Finset.range J, ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * M₀) ^ 2)⁻¹)) ^ q
          * lineMass (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ (j + 1) * M₀) ω ^ q
        + ((2 * Real.pi)⁻¹ * 14) ^ q
          * lineTail (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω ^ q) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (mul_nonneg hc (dilatedLineIntegral_nonneg _ _ _ _)) q) h123 hpt
  rw [integral_add h12 h3, integral_add h1 h2, integral_finsetSum _ hSj] at hint
  simp only [integral_const_mul] at hint
  have hJ := integral_rpow_le_rpow_integral hq0.le hq1
    (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2
      (lineTail_nonneg (fun ω => squarefreeExtension fun p => X p ω) N (2 ^ J * M₀) ω))
    hTl.1 hTl.2
  rw [integral_lineTail_sqfree_eq hX N hJ0] at hJ
  exact hint.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hC q)))

end RMF
