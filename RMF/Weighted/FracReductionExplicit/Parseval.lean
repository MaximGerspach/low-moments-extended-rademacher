/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracReductionExplicit.Smoothing
import RMF.Reduction.SieveLevel

/-!
# The remainder's reduction, III: the sieve and Parseval

The averaged rough sum of `RMF.sum_fracRoughTerm_le_setIntegral_eps` is an integral of
`|H_y(x/t)|²` against the weighted count of the rough `r` near `t`; for `t ≥ T₀` that count is at
most `C_s(1+η)²(tη/(1+η) + 1)/(t² log y)`, by Selberg's sieve at a level `D`
(`RMF.sum_inv_sq_indicator_le_sieveConst_frac`, `C_s = 1.001e^{-γ}`).  With `w = x/t ≤ x/T₀`
and `w^{2σ} ≤ e^{2c}` the integral becomes `∫₀^∞|H_y(w)|²w^{-1-2σ}dw`, and the kernel
Mellin–Plancherel identity (`RMF.integral_normSq_sum_fracKernel_eq_line`) turns that into
the line integral of the Euler product (`RMF.integral_normSq_smoothFracSum_eq_line`):

`∫₀^∞|H_y(u)|²u^{-1-2σ}du = (2π)⁻¹∫_ℝ|F_{y+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`.

The result (`RMF.integral_norm_fracPartSum_le_of_count`) is, with
`Z_R = (log y)⁻¹∫_ℝ|F_{y+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`,

`E|R(x)| ≤ C_R^{1/2}·E[Z_R^{1/2}] + fracSmoothErr^{1/2} + fracLowErr^{1/2}`,

`C_R = (1+ε)C_s((1+η)²(η/(1+η) + 1/T₀)/η)e^{2c}/(2π)` (`RMF.fracReductionConst`), instantiated
with Selberg's sieve (`RMF.integral_norm_fracPartSum_le_explicit_selberg`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The smooth factor as a fixed finite sum -/

omit [MeasurableSpace Ω] in
/-- A deterministic bound: `|H_y(w)| ≤ ∑_{k≤N} |f(k)|` for `⌊w⌋ ≤ N`. -/
lemma norm_smoothFracSum_le_sum (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {w : ℝ} {N : ℕ}
    (hN : ⌊w⌋₊ ≤ N) (ω : Ω) :
    ‖smoothFracSum f y w ω‖ ≤ ∑ k ∈ Finset.Icc 1 N, ‖f ω k‖ := by
  rw [smoothFracSum_eq_sum_Icc f y hN ω]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun k hk => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => norm_nonneg _)
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
  have hk1R : (1 : ℝ) ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk1)
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (fracKernel_nonneg _)]
  have h1 : ‖f ω k‖ / Real.sqrt k ≤ ‖f ω k‖ := div_le_self (norm_nonneg _) hk1R
  calc ‖f ω k‖ / Real.sqrt k * fracKernel (w / k) ≤ ‖f ω k‖ * 1 :=
        mul_le_mul h1 (fracKernel_le_one _) (fracKernel_nonneg _) (norm_nonneg _)
    _ = ‖f ω k‖ := mul_one _

omit [MeasurableSpace Ω] in
/-- **`H_y` over the squarefree support**: for the Rademacher function,
`H_y(u) = ∑_{k ≤ y#, k smooth} X(k)k^{-1/2}ψ(u/k)` for every `u`.  A smooth `k > y#` is not
squarefree, and a `k > u` has `ψ(u/k) = 0`. -/
lemma smoothFracSum_eq_sum_primorial {X : ℕ → Ω → ℂ} (y : ℕ) (u : ℝ) (ω : Ω) :
    smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y u ω
      = ∑ k ∈ {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)},
          squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ)
            * (fracKernel (u / k) : ℂ) := by
  classical
  set g : ℕ → ℂ := fun k =>
    squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ) * (fracKernel (u / k) : ℂ)
    with hgdef
  set S₁ : Finset ℕ := {k ∈ Finset.Icc 1 ⌊u⌋₊ | k ∈ Nat.smoothNumbers (y + 1)} with hS₁
  set S₂ : Finset ℕ := {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)}
    with hS₂
  have h1 : ∑ k ∈ S₁, g k = ∑ k ∈ S₁ ∪ S₂, g k := by
    refine Finset.sum_subset Finset.subset_union_left fun k hk hnot => ?_
    have hk2 : k ∈ S₂ := by
      rcases Finset.mem_union.1 hk with h | h
      · exact absurd h hnot
      · exact h
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk2).1).1
    have hks : k ∈ Nat.smoothNumbers (y + 1) := (Finset.mem_filter.1 hk2).2
    have hlt : ⌊u⌋₊ < k := by
      by_contra hcon
      exact hnot (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk1, not_lt.1 hcon⟩, hks⟩)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hle : u / k ≤ 1 := (div_le_one hk0).2 (Nat.lt_of_floor_lt hlt).le
    simp only [hgdef]
    rw [fracKernel_eq_zero_of_le_one hle, Complex.ofReal_zero, mul_zero]
  have h2 : ∑ k ∈ S₂, g k = ∑ k ∈ S₁ ∪ S₂, g k := by
    refine Finset.sum_subset Finset.subset_union_right fun k hk hnot => ?_
    have hk1' : k ∈ S₁ := by
      rcases Finset.mem_union.1 hk with h | h
      · exact h
      · exact absurd h hnot
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk1').1).1
    have hks : k ∈ Nat.smoothNumbers (y + 1) := (Finset.mem_filter.1 hk1').2
    have hsf : ¬ Squarefree k := by
      intro hsf
      refine hnot (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk1, ?_⟩, hks⟩)
      exact Nat.le_of_dvd (primorial_pos y)
        (dvd_primorial_of_squarefree_of_mem_smoothNumbers hsf hks)
    simp only [hgdef]
    rw [squarefreeExtension_apply_of_not_squarefree _ hsf, zero_div, zero_mul]
  rw [smoothFracSum, h1, ← h2]

omit [MeasurableSpace Ω] in
/-- **The Dirichlet polynomial of the coefficients is the Euler product**:
`∑_{k ≤ y#, k smooth} X(k)k^{-1/2}k^{-s} = F_{y+1}(½ + s)`, the squarefree smooth `k` being the
divisors of `y#` (`RMF.dirichletSeries_smoothCoeff_eq_sqfree`). -/
lemma sum_div_cpow_eq_randomEulerProduct {X : ℕ → Ω → ℂ} (y : ℕ) (ω : Ω) (s : ℂ) :
    ∑ k ∈ {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)},
        squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ) / (k : ℂ) ^ s
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (1 / 2 + s) ω := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  rw [← dirichletSeries_smoothCoeff_eq_sqfree y ω (1 / 2 + s), dirichletSeries]
  have hzero : ∀ n ∉ {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)},
      smoothCoeff f y ω n / (n : ℂ) ^ (1 / 2 + s) = 0 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    by_cases hsm : n ∈ Nat.smoothNumbers (y + 1)
    · have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsm
      have hnot : n ∉ Finset.Icc 1 (primorial y) := fun h => hn ⟨h, hsm⟩
      have hsf : ¬ Squarefree n := by
        intro hsf
        refine hnot (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, ?_⟩)
        exact Nat.le_of_dvd (primorial_pos y)
          (dvd_primorial_of_squarefree_of_mem_smoothNumbers hsf hsm)
      rw [smoothCoeff, if_pos hsm, hfdef]
      simp [squarefreeExtension_apply_of_not_squarefree _ hsf]
    · rw [smoothCoeff, if_neg hsm, zero_div]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hsm := (Finset.mem_filter.1 hn).2
  have hn1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hcast : ((n : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt n : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_num
  rw [smoothCoeff, if_pos hsm, Complex.cpow_add _ _ hn0, hcast, div_div]

/-! ### Parseval for the smooth factor -/

omit [MeasurableSpace Ω] in
/-- **Parseval for `H_y`**: for `σ > -½`,
`∫₀^∞|H_y(u)|²u^{-1-2σ}du = (2π)⁻¹∫_ℝ|F_{y+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`.  The kernel
Mellin–Plancherel identity `RMF.integral_normSq_sum_fracKernel_eq_line` at `aₖ = X(k)k^{-1/2}` on
the smooth `k ≤ y#` (`RMF.smoothFracSum_eq_sum_primorial`), whose Dirichlet polynomial is the
Euler product (`RMF.sum_div_cpow_eq_randomEulerProduct`). -/
theorem integral_normSq_smoothFracSum_eq_line {X : ℕ → Ω → ℂ} (y : ℕ) {σ : ℝ}
    (hσ : -1 / 2 < σ) (ω : Ω) :
    (∫ u in Set.Ioi (0 : ℝ),
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y u ω‖ ^ 2
          / u ^ (1 + 2 * σ))
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
  set SF : Finset ℕ := {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)}
    with hSF
  have hSF0 : ∀ k ∈ SF, 0 < k := fun k hk => (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
  have hH : ∀ u : ℝ, smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y u ω
      = ∑ k ∈ SF, (fun k : ℕ => squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ)) k
          * (fracKernel (u / k) : ℂ) := fun u => smoothFracSum_eq_sum_primorial y u ω
  have hD : ∀ t : ℝ, ∑ k ∈ SF,
      (fun k : ℕ => squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ)) k
          / (k : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω := by
    intro t
    rw [sum_div_cpow_eq_randomEulerProduct, add_assoc]
  simp_rw [hH]
  rw [integral_normSq_sum_fracKernel_eq_line SF _ hSF0 hσ]
  simp_rw [hD]

omit [MeasurableSpace Ω] in
/-- `u ↦ |H_y(u)|²u^{-1-2σ}` is integrable on `(0, ∞)` for `σ > -½`. -/
theorem integrableOn_normSq_smoothFracSum {X : ℕ → Ω → ℂ} (y : ℕ) {σ : ℝ} (hσ : -1 / 2 < σ)
    (ω : Ω) :
    IntegrableOn (fun u : ℝ =>
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y u ω‖ ^ 2
          / u ^ (1 + 2 * σ)) (Set.Ioi 0) := by
  set SF : Finset ℕ := {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)}
    with hSF
  have hSF0 : ∀ k ∈ SF, 0 < k := fun k hk => (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
  have h := integrableOn_normSq_sum_fracKernel SF
    (fun k : ℕ => squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ)) hSF0 hσ
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only
  rw [smoothFracSum_eq_sum_primorial y u ω]

/-! ### The line integral is integrable -/

/-- **`Z_R^q` is integrable** for `σ ≥ 0` and `q ≥ 0`: by Parseval `Z_R` is
`(log y)⁻¹·2π∫₀^∞|H_y(u)|²u^{-1-2σ}du`, jointly measurable in `(ω, u)`; and almost surely
`|H_y(u)| ≤ #{k ≤ y# smooth}·u^{-1/2}` (`RMF.norm_sum_fracKernel_le`) with `H_y = 0` below `1`, so
`Z_R` is bounded. -/
theorem integrable_rpow_fracEulerLine {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q) μ := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hσ' : -1 / 2 < σ := by linarith
  have hpars := fun ω : Ω => integral_normSq_smoothFracSum_eq_line (X := X) y hσ' ω
  have hIint := fun ω : Ω => integrableOn_normSq_smoothFracSum (X := X) y hσ' ω
  have hprim := fun (u : ℝ) (ω : Ω) => smoothFracSum_eq_sum_primorial (X := X) y u ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set SF : Finset ℕ := {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)}
    with hSF
  have hSF0 : ∀ k ∈ SF, 0 < k := fun k hk => (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
  have hpi2 : (2 * Real.pi) ≠ 0 := by positivity
  have hrw : ∀ ω : Ω,
      ((Real.log y)⁻¹ * ∫ t : ℝ, ‖randomEulerProduct f (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
        = (Real.log y)⁻¹ * (2 * Real.pi)
            * ∫ u in Set.Ioi (0 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
    intro ω
    rw [hpars ω, mul_assoc, mul_inv_cancel_left₀ hpi2]
  simp only [hrw]
  -- measurability in `ω`
  have hA : Measurable fun z : Ω × ℝ => smoothFracSum f y z.2 z.1 :=
    measurable_uncurry_smoothFracSum hRa.measurable_apply y
  have hjm : Measurable fun z : Ω × ℝ =>
      ‖smoothFracSum f y z.2 z.1‖ ^ 2 / z.2 ^ (1 + 2 * σ) := by
    have hden : Measurable fun z : Ω × ℝ => z.2 ^ (1 + 2 * σ) :=
      (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + 2 * σ)).measurable.comp
        measurable_snd
    exact (hA.norm.pow_const 2).div hden
  have hsm : StronglyMeasurable fun ω : Ω =>
      ∫ u in Set.Ioi (0 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
    hjm.stronglyMeasurable.integral_prod_right'
  have hmq : Measurable fun ω : Ω => ((Real.log y)⁻¹ * (2 * Real.pi)
      * ∫ u in Set.Ioi (0 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ)) ^ q :=
    (Real.continuous_rpow_const hq0).measurable.comp (measurable_const.mul hsm.measurable)
  -- `|H_y(u)| ≤ #SF·u^{-1/2}` almost surely
  have hbnd : ∀ᵐ ω ∂μ, ∀ u : ℝ, 0 < u →
      ‖smoothFracSum f y u ω‖ ≤ (SF.card : ℝ) * u ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n] with ω hb u hu
    rw [hprim u ω]
    refine le_trans (norm_sum_fracKernel_le SF _ hSF0 hu) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _)
    calc ∑ k ∈ SF, ‖squarefreeExtension (fun p => X p ω) k / (Real.sqrt k : ℂ)‖ * Real.sqrt k
        ≤ ∑ _k ∈ SF, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk0 : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hSF0 k hk)
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0,
            div_mul_cancel₀ _ hk0.ne']
          exact hb k
      _ = (SF.card : ℝ) := by simp
  -- the `u`-integral is at most `#SF²/(1 + 2σ)`
  have hIbd : ∀ᵐ ω ∂μ,
      (∫ u in Set.Ioi (0 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        ≤ (SF.card : ℝ) ^ 2 / (1 + 2 * σ) := by
    filter_upwards [hbnd] with ω hω
    have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi zero_le_one
    have hsub' : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun u hu => hu.1
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
      Set.disjoint_left.2 fun u hu hu' => absurd hu.2 (not_le.2 hu')
    have hsplit : (∫ u in Set.Ioi (0 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        = (∫ u in Set.Ioc (0 : ℝ) 1, ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
          + ∫ u in Set.Ioi (1 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
      exact setIntegral_union hdisj measurableSet_Ioi ((hIint ω).mono_set hsub')
        ((hIint ω).mono_set hsub)
    have hlow : (∫ u in Set.Ioc (0 : ℝ) 1, ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        = 0 := by
      have h1 : (∫ u in Set.Ioc (0 : ℝ) 1, ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
          = ∫ u in Set.Ioo (0 : ℝ) 1, ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
        (setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1))).symm
      have h2 : Set.EqOn (fun u : ℝ => ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
          (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
        intro u hu
        change ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) = 0
        rw [smoothFracSum_eq_zero_of_lt_one f y hu.2 ω]
        simp
      rw [h1, setIntegral_congr_fun measurableSet_Ioo h2]
      simp
    have hmaj : IntegrableOn
        (fun u : ℝ => (SF.card : ℝ) ^ 2 * u ^ (-(2 + 2 * σ))) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    have hcmp : (∫ u in Set.Ioi (1 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        ≤ ∫ u in Set.Ioi (1 : ℝ), (SF.card : ℝ) ^ 2 * u ^ (-(2 + 2 * σ)) := by
      refine setIntegral_mono_on ((hIint ω).mono_set hsub) hmaj measurableSet_Ioi fun u hu => ?_
      have hu0 : (0 : ℝ) < u := lt_trans one_pos (Set.mem_Ioi.1 hu)
      have hnum : ‖smoothFracSum f y u ω‖ ^ 2 ≤ ((SF.card : ℝ) * u ^ (-(1 / 2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hω u hu0) 2
      have hpow : ((SF.card : ℝ) * u ^ (-(1 / 2 : ℝ))) ^ 2 / u ^ (1 + 2 * σ)
          = (SF.card : ℝ) ^ 2 * u ^ (-(2 + 2 * σ)) := by
        rw [mul_pow, ← Real.rpow_natCast (u ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hu0.le,
          mul_div_assoc, ← Real.rpow_sub hu0]
        congr 2
        push_cast
        ring
      rw [← hpow]
      exact div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hu0.le _)
    have hval : (∫ u in Set.Ioi (1 : ℝ), (SF.card : ℝ) ^ 2 * u ^ (-(2 + 2 * σ)))
        = (SF.card : ℝ) ^ 2 / (1 + 2 * σ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
        show -(2 + 2 * σ) + 1 = -(1 + 2 * σ) by ring, neg_div_neg_eq, mul_one_div]
    rw [hsplit, hlow, zero_add]
    exact le_trans hcmp (le_of_eq hval)
  have hc0 : (0 : ℝ) ≤ (Real.log y)⁻¹ * (2 * Real.pi) :=
    mul_nonneg (inv_nonneg.2 (Real.log_natCast_nonneg y)) (by positivity)
  refine (memLp_top_of_bound hmq.aestronglyMeasurable
    (((Real.log y)⁻¹ * (2 * Real.pi) * ((SF.card : ℝ) ^ 2 / (1 + 2 * σ))) ^ q) ?_).integrable
    le_top
  filter_upwards [hIbd] with ω hω
  have h0 : (0 : ℝ) ≤ ∫ u in Set.Ioi (0 : ℝ),
      ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Set.mem_Ioi.1 hu).le _)
  have hprod : (0 : ℝ) ≤ (Real.log y)⁻¹ * (2 * Real.pi)
      * ∫ u in Set.Ioi (0 : ℝ), ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
    mul_nonneg hc0 h0
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hprod q)]
  exact Real.rpow_le_rpow hprod (mul_le_mul_of_nonneg_left hω hc0) hq0

/-! ### The principal term -/

omit [MeasurableSpace Ω] in
/-- **The principal term with its coefficient.**  For `0 < T₀ ≤ x`, `σ ≥ 0` with
`σ log(x/T₀) ≤ c`, `C, K ≥ 0`: `(K/η)∫_{[T₀, x(1+η)]}|H_y(x/t)|²·C(1+η)²(tη/(1+η)+1)/(t² log y)dt`
is at most `K·C·((1+η)²(η/(1+η) + 1/T₀)/η)·e^{2c}·(2π)⁻¹·Z_R`.  `w = x/t ≤ x/T₀` has
`w^{2σ} ≤ e^{2c}`, and Parseval is `RMF.integral_normSq_smoothFracSum_eq_line`:
`RMF.setIntegral_normSq_mul_sieve_le_explicit` with `ψ` and `T₀`. -/
theorem setIntegral_normSq_smoothFracSum_mul_sieve_le {X : ℕ → Ω → ℂ} (y : ℕ)
    {σ x T₀ η C K c : ℝ} (hT₀ : 0 < T₀) (hT₀x : T₀ ≤ x) (hσ : 0 ≤ σ)
    (hσlog : σ * Real.log (x / T₀) ≤ c) (hη : 0 < η) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hlogy : 0 < Real.log y) (ω : Ω) :
    (K / η) * (∫ t in Set.Icc T₀ (x * (1 + η)),
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ K * C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀) / η) * Real.exp (2 * c)
          * (2 * Real.pi)⁻¹ * ((Real.log y)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) := by
  have hσ' : -1 / 2 < σ := by linarith
  have hpars := integral_normSq_smoothFracSum_eq_line (X := X) y hσ' ω
  have hIint := integrableOn_normSq_smoothFracSum (X := X) y hσ' ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set P : ℝ := ∫ t : ℝ, ‖randomEulerProduct f (y + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 with hPdef
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hT₀ hT₀x
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hb : T₀ ≤ x * (1 + η) := le_trans hT₀x (le_mul_of_one_le_right hx0.le (by linarith))
  set M : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x / T₀⌋₊, ‖f ω k‖ with hMdef
  have hgb : ∀ t ∈ Set.Icc T₀ (x * (1 + η)), ‖smoothFracSum f y (x / t) ω‖ ≤ M := fun t ht =>
    norm_smoothFracSum_le_sum f y
      (Nat.floor_le_floor (div_le_div_of_nonneg_left hx0.le hT₀ ht.1)) ω
  have hmeas : Measurable fun t : ℝ => ‖smoothFracSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothFracSum f y (x / t) ω :=
      (measurable_smoothFracSum_arg f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  have hint1 : IntegrableOn (fun t => ‖smoothFracSum f y (x / t) ω‖ ^ 2 / t)
      (Set.Icc T₀ (x * (1 + η))) volume := by
    refine Measure.integrableOn_of_bounded (M := M ^ 2 / T₀)
      measure_Icc_lt_top.ne (hmeas.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hT₀ ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ht0.le)]
    calc ‖smoothFracSum f y (x / t) ω‖ ^ 2 / t ≤ M ^ 2 / t := by
          gcongr
          exact hgb t ht
      _ ≤ M ^ 2 / T₀ := div_le_div_of_nonneg_left (sq_nonneg _) hT₀ ht.1
  have hstep12 : (∫ t in Set.Icc T₀ (x * (1 + η)),
        ‖smoothFracSum f y (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀)) / Real.log y
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / T₀), ‖smoothFracSum f y w ω‖ ^ 2 / w :=
    setIntegral_mul_sieveShape_le (fun u => ‖smoothFracSum f y u ω‖ ^ 2) hx0 hT₀ hb hη
      hC hlogy (fun _ => sq_nonneg _) hint1
  have hlow : (0 : ℝ) < x / (x * (1 + η)) := div_pos hx0 (mul_pos hx0 h1η)
  have hsub : Set.Ioo (x / (x * (1 + η))) (x / T₀) ⊆ Set.Ioi (0 : ℝ) :=
    fun w hw => lt_trans hlow hw.1
  have hcmp : ∀ w ∈ Set.Ioo (x / (x * (1 + η))) (x / T₀),
      ‖smoothFracSum f y w ω‖ ^ 2 / w
        ≤ Real.exp (2 * c) * (‖smoothFracSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := lt_trans hlow hw.1
    rcases lt_or_ge w 1 with hlt | hge
    · rw [smoothFracSum_eq_zero_of_lt_one f y hlt ω]
      simp
    · refine div_le_exp_mul_div_rpow (sq_nonneg _) hw0 ?_
      rw [Real.rpow_def_of_pos hw0]
      refine Real.exp_le_exp.2 ?_
      have hlogw : Real.log w ≤ Real.log (x / T₀) := Real.log_le_log hw0 hw.2.le
      have hσ2 : (0 : ℝ) ≤ 2 * σ := by linarith
      have h1 : Real.log w * (2 * σ) ≤ Real.log (x / T₀) * (2 * σ) :=
        mul_le_mul_of_nonneg_right hlogw hσ2
      have h2 : Real.log (x / T₀) * (2 * σ) = 2 * (σ * Real.log (x / T₀)) := by ring
      linarith
  have hstep3 : (∫ w in Set.Ioo (x / (x * (1 + η))) (x / T₀),
        ‖smoothFracSum f y w ω‖ ^ 2 / w)
      ≤ Real.exp (2 * c) * ∫ u in Set.Ioi (0 : ℝ),
          ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
    calc (∫ w in Set.Ioo (x / (x * (1 + η))) (x / T₀),
            ‖smoothFracSum f y w ω‖ ^ 2 / w)
        ≤ ∫ w in Set.Ioo (x / (x * (1 + η))) (x / T₀),
            Real.exp (2 * c) * (‖smoothFracSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
          refine integral_mono_of_nonneg ?_ ((hIint.mono_set hsub).const_mul _) ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact div_nonneg (sq_nonneg _) (lt_trans hlow hw.1).le
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact hcmp w hw
      _ = Real.exp (2 * c) * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / T₀),
            ‖smoothFracSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ) := integral_const_mul _ _
      _ ≤ Real.exp (2 * c) * ∫ u in Set.Ioi (0 : ℝ),
            ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine setIntegral_mono_set hIint ?_ (Filter.Eventually.of_forall fun w hw => hsub hw)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hu) _)
  have hcoef0 : (0 : ℝ) ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀)) / Real.log y := by
    positivity
  calc (K / η) * (∫ t in Set.Icc T₀ (x * (1 + η)),
          ‖smoothFracSum f y (x / t) ω‖ ^ 2
            * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ (K / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀)) / Real.log y
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / T₀),
              ‖smoothFracSum f y w ω‖ ^ 2 / w) :=
        mul_le_mul_of_nonneg_left hstep12 (by positivity)
    _ ≤ (K / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀)) / Real.log y
          * (Real.exp (2 * c) * ∫ u in Set.Ioi (0 : ℝ),
              ‖smoothFracSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hcoef0) (by positivity)
    _ = K * C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀) / η) * Real.exp (2 * c)
          * (2 * Real.pi)⁻¹ * ((Real.log y)⁻¹ * P) := by
        rw [hpars]
        field_simp

/-! ### The sieve, for `t ≥ T₀` -/

/-- **The sieve constant of Brun–Titchmarsh at level `y`, for `t ≥ T₀`**:
`C_s = 2 + 5y(1+log y)³·log y·(1+η)/(T₀η + 1 + η)`. -/
noncomputable def fracSieveConst (y : ℕ) (T₀ η : ℝ) : ℝ :=
  2 + 5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y * (1 + η) / (T₀ * η + 1 + η)

/-- **The weighted interval count by Selberg's sieve at level `D`**: for `y`-rough `S`, `y ≥ 2`
with `log y ≥ 10⁶`, `1 + η < t`, and a level `D ≥ 1` with `D^{1/(2 log y)} ≥ 40000 log² y` and
`5D(1 + log D)³·20000 log y ≤ tη/(1+η) + 1`, the count is at most
`1.001e^{-γ}(1+η)²(tη/(1+η)+1)/(t² log y)`: `RMF.roughCount_sub_le_sieveConst` on
`(t/(1+η) - 1, t]`. -/
theorem sum_inv_sq_indicator_le_sieveConst_frac {y : ℕ} (hy : 2 ≤ y) {S : Finset ℕ}
    (hSr : ∀ r ∈ S, IsRough y r) {η t D : ℝ} (hη : 0 < η) (ht : 1 + η < t) (hD : 1 ≤ D)
    (hℓ : 1000000 ≤ Real.log y) (hθ : 40000 * Real.log y ^ 2 ≤ D ^ (1 / (2 * Real.log y)))
    (herr : 5 * D * (1 + Real.log D) ^ 3 * (20000 * Real.log y) ≤ t * η / (1 + η) + 1) :
    ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ sieveConst * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y) := by
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hly : 0 < Real.log y := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t / (1 + η) - 1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha, sub_pos, one_lt_div hη0]
    exact ht
  have hat : a < t / (1 + η) := by rw [ha]; linarith
  have hH : t - a = t * η / (1 + η) + 1 := by rw [ha]; exact sub_div_sub_one_eq hη
  have hH0 : 0 < t - a := by rw [hH]; positivity
  refine le_trans (sum_inv_sq_indicator_le_rough hSr hη ht0 ha0.le hat) ?_
  have hsum : a + (t - a) = t := by ring
  have hcard := roughCount_sub_eq_card (y := y) (x := a) (H := t - a) hH0.le
  rw [hsum] at hcard
  rw [← hcard]
  have hsel := roughCount_sub_le_sieveConst hy ha0 hH0 hD hℓ hθ (by rw [hH]; exact herr)
  rw [hsum, hH] at hsel
  calc (1 + η) ^ 2 / t ^ 2 * ((roughCount y t : ℝ) - (roughCount y a : ℝ))
      ≤ (1 + η) ^ 2 / t ^ 2 * (sieveConst * (t * η / (1 + η) + 1) / Real.log y) :=
        mul_le_mul_of_nonneg_left hsel (by positivity)
    _ = sieveConst * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y) := by
        field_simp

/-! ### The rough sum at one `ω` -/

/-- **The reduction's constant**
`C_R = (1+ε)·C_s·((1+η)²(η/(1+η) + 1/T₀)/η)·e^{2c}/(2π)`; the middle factor is
`(1+η) + (1+η)²/(ηT₀)`. -/
noncomputable def fracReductionConst (Cs T₀ η ε c : ℝ) : ℝ :=
  (1 + ε) * Cs * ((1 + η) ^ 2 * (η / (1 + η) + 1 / T₀) / η) * Real.exp (2 * c)
    * (2 * Real.pi)⁻¹

lemma fracReductionConst_nonneg {Cs T₀ η ε c : ℝ} (hCs : 0 ≤ Cs) (hT₀ : 0 < T₀) (hη : 0 < η)
    (hε : 0 < ε) : 0 ≤ fracReductionConst Cs T₀ η ε c := by
  have hpi : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  rw [fracReductionConst]
  positivity

omit [MeasurableSpace Ω] in
/-- **The large rough factors at one `ω`.**  At an `ω` where every value has norm at most one,
for `S` a set of integers in `[T₀, x]`, `0 < T₀ ≤ x`, `σ ≥ 0` with `σ log(x/T₀) ≤ c`, and a count
bound `C_s` on `[T₀, x(1+η)]` (such as `RMF.sum_inv_sq_indicator_le_sieveConst_frac` gives):
`∑_{r∈S} r⁻¹|H_y(x/r)|² ≤ C_R·Z_R(ω) + ((1+1/ε)/(2η))∑_{r∈S}(2∫|H_y(x/r) - H_y(x/t)|²)/r²`. -/
theorem sum_fracRoughTerm_le_explicit {X : ℕ → Ω → ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1) {y : ℕ} (hy : 2 ≤ y)
    {σ x T₀ η ε c Cs : ℝ} (hT₀ : 0 < T₀) (hT₀x : T₀ ≤ x) (hσ : 0 ≤ σ)
    (hσlog : σ * Real.log (x / T₀) ≤ c) (hη : 0 < η) (hε : 0 < ε) (hCs : 0 < Cs)
    {S : Finset ℕ} (hST : ∀ r ∈ S, T₀ ≤ (r : ℝ)) (hSx : ∀ r ∈ S, (r : ℝ) ≤ x)
    (hcount : ∀ t ∈ Set.Icc T₀ (x * (1 + η)), ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ Cs * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)) :
    ∑ r ∈ S, fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r
      ≤ fracReductionConst Cs T₀ η ε c * ((Real.log y)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
        + ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖
                  ^ 2)) / ((r : ℝ)) ^ 2 := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hT₀ hT₀x
  have hden : (0 : ℝ) < 1 + η := by linarith
  have hS : ∀ r ∈ S, 0 < r := fun r hr => by
    have : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le hT₀ (hST r hr)
    exact_mod_cast this
  have hAle : ∀ t : ℝ, T₀ ≤ t → ‖smoothFracSum f y (x / t) ω‖ ≤ x / T₀ := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hT₀ ht
    refine le_trans (norm_smoothFracSum_le_of_bound hbnd y (x / t)) ?_
    refine le_trans (Nat.floor_le (div_nonneg hxpos.le ht0.le)) ?_
    exact div_le_div_of_nonneg_left hxpos.le hT₀ ht
  have hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ Set.Icc T₀ (x * (1 + η)) := by
    intro r hr t ht
    exact ⟨le_trans (hST r hr) ht.1, le_trans ht.2 (mul_le_mul_of_nonneg_right (hSx r hr) hden.le)⟩
  obtain ⟨hint, hintT⟩ := integrableOn_sieveShape_of_bound
    (measurable_smoothFracSum_arg f y ω) (s := x * (1 + η)) hη hT₀ hCs hlogy hAle
  have hsm := sum_fracRoughTerm_le_setIntegral_eps
    (T := Set.Icc T₀ (x * (1 + η)))
    (b := fun t => Cs * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y))
    hbnd y hxpos.le hη hε hS measurableSet_Icc hsub hcount (fun r _ => hint r) hintT
  have hpr := setIntegral_normSq_smoothFracSum_mul_sieve_le (X := X) y hT₀ hT₀x hσ hσlog hη
    hCs.le (by positivity : (0 : ℝ) ≤ 1 + ε) hlogy ω
  refine le_trans hsm (add_le_add ?_ le_rfl)
  refine le_trans hpr (le_of_eq ?_)
  rw [fracReductionConst]

/-! ### The large rough factors in `q`-th moment -/

/-- The smoothing error of one window is integrable in `ω`. -/
theorem integrable_setIntegral_normSq_smoothFracSum_sub_Icc {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r s : ℝ}
    (hx : 0 ≤ x) (hr : 0 < r) :
    Integrable (fun ω => ∫ t in Set.Icc r s,
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2)
      μ := by
  simp only [restrict_Icc_eq_Ioc]
  exact (integrable_uncurry_normSq_smoothFracSum_sub hX y hx hr).integral_prod_left

/-- **The large rough factors in `q`-th moment.**  For `0 < q ≤ 1`, `y ≥ 2`, `S` a set of
`y`-rough integers in `[T₀, x]`, `1 ≤ T₀ ≤ x`, `σ ≥ 0` with `σ log(x/T₀) ≤ c`, `η, ε > 0` and a
count bound `C_s > 0` on `[T₀, x(1+η)]`:
`E[(∑_{r∈S} r⁻¹|H_y(x/r)|²)^q] ≤ C_R^q·E[Z_R^q] + fracSmoothErr^q`. -/
theorem integral_rpow_sum_fracRoughTerm_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ x T₀ η ε c Cs q : ℝ}
    (hT₀ : 1 ≤ T₀) (hT₀x : T₀ ≤ x) (hσ : 0 ≤ σ) (hσlog : σ * Real.log (x / T₀) ≤ c)
    (hη : 0 < η) (hε : 0 < ε) (hCs : 0 < Cs) (hq0 : 0 < q) (hq1 : q ≤ 1) {S : Finset ℕ}
    (hSr : ∀ r ∈ S, IsRough y r) (hST : ∀ r ∈ S, T₀ ≤ (r : ℝ)) (hSx : ∀ r ∈ S, (r : ℝ) ≤ x)
    (hcount : ∀ t ∈ Set.Icc T₀ (x * (1 + η)), ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ Cs * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)) :
    (∫ ω, (∑ r ∈ S, fracRoughTerm
        (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q ∂μ)
      ≤ (fracReductionConst Cs T₀ η ε c) ^ q * (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
                * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q ∂μ)
        + (fracSmoothErr x η ε) ^ q := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hT₀0 : (0 : ℝ) < T₀ := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans hT₀ hT₀x
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by linarith)
  have hCR := fracReductionConst_nonneg (c := c) hCs.le hT₀0 hη hε
  have hS1 : ∀ r ∈ S, 1 ≤ r := fun r hr => by
    have : (1 : ℝ) ≤ (r : ℝ) := le_trans hT₀ (hST r hr)
    exact_mod_cast this
  obtain ⟨Err, hErr⟩ : ∃ Err : Ω → ℝ, Err = fun ω => ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Ω → ℝ, Z = fun ω => (Real.log y)⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by
    rw [hZ]
    exact mul_nonneg (inv_nonneg.2 hlogy) (integral_nonneg fun t => by positivity)
  have hErr0 : ∀ ω, 0 ≤ Err ω := fun ω => by
    rw [hErr]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => ?_)
    refine div_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
    exact setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hErrint : Integrable Err μ := by
    rw [hErr]
    refine (integrable_finsetSum S fun r hr => ?_).const_mul _
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (hS1 r hr)
    exact ((integrable_setIntegral_normSq_smoothFracSum_sub_Icc hX y hx0 hr0).const_mul
      2).div_const _
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hstep : ∀ᵐ ω ∂μ, (∑ r ∈ S, fracRoughTerm
      (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q
      ≤ (fracReductionConst Cs T₀ η ε c) ^ q * Z ω ^ q + Err ω ^ q := by
    filter_upwards [hbdd] with ω hb
    have h1 : (∑ r ∈ S, fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r)
        ≤ fracReductionConst Cs T₀ η ε c * Z ω + Err ω := by
      have h := sum_fracRoughTerm_le_explicit (X := X) (ω := ω) hb hy hT₀0 hT₀x hσ hσlog hη hε
        hCs hST hSx hcount
      rw [hZ, hErr]
      exact h
    have hsum0 : (0 : ℝ) ≤ ∑ r ∈ S, fracRoughTerm
        (fun ω => squarefreeExtension fun p => X p ω) y x ω r :=
      Finset.sum_nonneg fun r _ => fracRoughTerm_nonneg _ _ _ _ _
    calc (∑ r ∈ S, fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q
        ≤ (fracReductionConst Cs T₀ η ε c * Z ω + Err ω) ^ q := Real.rpow_le_rpow hsum0 h1 hq0.le
      _ ≤ (fracReductionConst Cs T₀ η ε c * Z ω) ^ q + Err ω ^ q :=
          Real.rpow_add_le_add_rpow (mul_nonneg hCR (hZ0 ω)) (hErr0 ω) hq0.le hq1
      _ = (fracReductionConst Cs T₀ η ε c) ^ q * Z ω ^ q + Err ω ^ q := by
          rw [Real.mul_rpow hCR (hZ0 ω)]
  have hI1 := integrable_rpow_sum_fracRoughTerm hRa y hx0 hS1 hq0.le
  have hIZ : Integrable (fun ω => (fracReductionConst Cs T₀ η ε c) ^ q * Z ω ^ q) μ := by
    rw [hZ]
    exact (integrable_rpow_fracEulerLine hX y hσ hq0.le).const_mul _
  have hIE : Integrable (fun ω => Err ω ^ q) μ :=
    integrable_rpow_of_integrable hErrint (Filter.Eventually.of_forall hErr0) hq0.le hq1
  have hJ : (∫ ω, Err ω ^ q ∂μ) ≤ (fracSmoothErr x η ε) ^ q := by
    refine integral_rpow_le_rpow_of_integral_le hq0.le hq1 (Filter.Eventually.of_forall hErr0)
      hErrint ?_
    rw [hErr]
    exact integral_fracSmoothingError_le hX hx1 hη hε hSr hS1 hSx
  calc (∫ ω, (∑ r ∈ S, fracRoughTerm
      (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q ∂μ)
      ≤ ∫ ω, ((fracReductionConst Cs T₀ η ε c) ^ q * Z ω ^ q + Err ω ^ q) ∂μ :=
        integral_mono_ae hI1 (hIZ.add hIE) hstep
    _ = (fracReductionConst Cs T₀ η ε c) ^ q * (∫ ω, Z ω ^ q ∂μ) + ∫ ω, Err ω ^ q ∂μ := by
        rw [integral_add hIZ hIE, integral_const_mul]
    _ ≤ (fracReductionConst Cs T₀ η ε c) ^ q * (∫ ω, Z ω ^ q ∂μ)
          + (fracSmoothErr x η ε) ^ q := by
        linarith [hJ]
    _ = _ := by rw [hZ]

/-! ### The reduction -/

/-- **The reduction of `E|R(x)|` to the line, given a count bound.**  For `y ≥ 2`,
`1 ≤ T₀ ≤ x`, `0 < κ ≤ log y`, `σ ≥ 0` with `σ log(x/T₀) ≤ c`, `η, ε > 0`, and `C_s > 0` bounding
the weighted count of the rough squarefree `r ∈ [T₀, x]` near every `t ∈ [T₀, x(1+η)]`:

`E|R(x)| ≤ C_R^{1/2}·E[Z_R^{1/2}] + fracSmoothErr^{1/2} + fracLowErr^{1/2}`,

`C_R = RMF.fracReductionConst C_s T₀ η ε c`, `Z_R = (log y)⁻¹∫_ℝ|F_{y+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`.
The count bound is supplied by Selberg's sieve, `RMF.sum_inv_sq_indicator_le_sieveConst_frac`. -/
theorem integral_norm_fracPartSum_le_of_count {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ x T₀ η ε c κ Cs : ℝ}
    (hT₀ : 1 ≤ T₀) (hT₀x : T₀ ≤ x) (hκ : 0 < κ) (hκy : κ ≤ Real.log y) (hσ : 0 ≤ σ)
    (hσlog : σ * Real.log (x / T₀) ≤ c) (hη : 0 < η) (hε : 0 < ε) (hCs : 0 < Cs)
    (hcount : ∀ t ∈ Set.Icc T₀ (x * (1 + η)),
      ∑ r ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ T₀ ≤ (m : ℝ)},
          (((r : ℝ)) ^ 2)⁻¹
            * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
        ≤ Cs * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ (fracReductionConst Cs T₀ η ε c) ^ (1 / 2 : ℝ) * (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
                * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
        + (fracSmoothErr x η ε) ^ (1 / 2 : ℝ) + (fracLowErr x T₀ y κ) ^ (1 / 2 : ℝ) := by
  have hsplit := integral_norm_fracPartSum_le_lowErr_add hX hy hT₀ hT₀x hκ hκy
  have hhi := integral_rpow_sum_fracRoughTerm_le_explicit hX hy hT₀ hT₀x hσ hσlog hη hε hCs
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (S := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ T₀ ≤ (m : ℝ)})
    (fun r hr => (Finset.mem_filter.1 hr).2.1)
    (fun r hr => (Finset.mem_filter.1 hr).2.2.2)
    (fun r hr => le_trans (Nat.cast_le.2 (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).2)
      (Nat.floor_le (by linarith))) hcount
  linarith

/-- **The reduction with Selberg's sieve.**  `RMF.integral_norm_fracPartSum_le_of_count` with the
count bound `RMF.sum_inv_sq_indicator_le_sieveConst_frac` and the sieve constant `1.001e^{-γ}`
(`RMF.sieveConst`), at a level `D ≥ 1` with `log y ≥ 10⁶`, `D^{1/(2 log y)} ≥ 40000 log² y` and
`5D(1 + log D)³·20000 log y ≤ T₀η/(1+η) + 1`. -/
theorem integral_norm_fracPartSum_le_explicit_selberg {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ x T₀ η ε c κ D : ℝ}
    (hT₀ : 1 + η < T₀) (hT₀x : T₀ ≤ x) (hκ : 0 < κ) (hκy : κ ≤ Real.log y) (hσ : 0 ≤ σ)
    (hσlog : σ * Real.log (x / T₀) ≤ c) (hη : 0 < η) (hε : 0 < ε) (hD : 1 ≤ D)
    (hℓ : 1000000 ≤ Real.log y) (hθ : 40000 * Real.log y ^ 2 ≤ D ^ (1 / (2 * Real.log y)))
    (herr : 5 * D * (1 + Real.log D) ^ 3 * (20000 * Real.log y) ≤ T₀ * η / (1 + η) + 1) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ (fracReductionConst sieveConst T₀ η ε c) ^ (1 / 2 : ℝ)
          * (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
                * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
        + (fracSmoothErr x η ε) ^ (1 / 2 : ℝ) + (fracLowErr x T₀ y κ) ^ (1 / 2 : ℝ) := by
  have hT₀1 : 1 ≤ T₀ := by linarith
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  refine integral_norm_fracPartSum_le_of_count hX hy hT₀1 hT₀x hκ hκy hσ hσlog hη hε
    sieveConst_pos (fun t ht => ?_)
  refine sum_inv_sq_indicator_le_sieveConst_frac hy (fun r hr => (Finset.mem_filter.1 hr).2.1)
    hη (by linarith [ht.1]) hD hℓ hθ (le_trans herr ?_)
  have h1 : T₀ * η / (1 + η) ≤ t * η / (1 + η) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.1 hη.le) hη0.le
  linarith

end RMF
