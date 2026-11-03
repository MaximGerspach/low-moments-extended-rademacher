/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedLowerWindow
import RMF.Weighted.LowerReduction

/-!
# The extended sum's lower bound in terms of random Euler products

Proposition 4.3 of the paper, before the Euler-product ratio.  With `F^e` the Euler product of
`X^e = RMF.compMultExtension X` over the primes up to `x`,
there are `c, C > 0` and `x₀`, independent of `X`, `V`, `x` and `q`, with

`c (x/log x)^q E[(∫_{|t|<1} |F^e(½+2V/log x+it)|² dt)^q]`
`  - C e^{-Vq} (x/log x)^q E[(∫_ℝ |F^e(½+V/log x+it)/(½+V/log x+it)|² dt)^q] - C (x/log x)^q`
`  ≤ E|∑_{n≤x} X^e(n)|^{2q}`

for `0 < q ≤ ½`, `V > 0`, `x ≥ x₀` and `log x ≥ 3V + 3`
(`RMF.exists_le_integral_rpow_extendedSum_euler`): symmetrisation and Khintchine
(`RMF.khintchine_rough_extended`), smoothing (`RMF.meanSquare_le_sum_extended`), and Parseval
(`RMF.extendedMeanSquare_ge_line`), as in the weighted chain.

## Parseval for `X^e`

The smooth sums of `X^e` are the partial sums of the Steinhaus-shaped Euler product
`∏_{p≤x}(1 - X(p)p^{-s})⁻¹` with `|X(p)| ≤ 1`, so the Steinhaus chain's Parseval step applies
verbatim once its hypothesis `RMF.IsBoundedRMF` is replaced by the `|f| ≤ 1` it uses
(`RMF.smoothTailIntegral_eq_line_of`), and the Dirichlet-series identity is restated for the
Rademacher law (`RMF.dirichletSeries_smoothCoeff_eq_rademacher`, the same proof).  The mean square
has the weight `z^{-2}`, so the line has the weight `|½+σ+it|^{-2}`; on `|t| < 1` it is at least
`¼` (`RMF.quarter_setIntegral_Ioo_le_integral_div`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Parseval for the smooth sums of `X^e` -/

/-- `RMF.summable_norm_smoothCoeff_div_sqrt` with the hypothesis it uses. -/
lemma summable_norm_smoothCoeff_div_sqrt_of {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) (y : ℕ) :
    ∀ᵐ ω ∂μ, Summable fun n : ℕ => ‖smoothCoeff f y ω n‖ / Real.sqrt n := by
  have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, ‖f ω n‖ ≤ 1 := by
    rw [MeasureTheory.ae_all_iff]
    exact hbd
  filter_upwards [hall] with ω hω
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_smoothIndicator_div_sqrt y)
  rw [smoothCoeff]
  split_ifs with hmem
  · exact div_le_div_of_nonneg_right (hω n) (Real.sqrt_nonneg _)
  · simp

/-- **The Dirichlet series over smooth numbers is the Euler product**, for the completely
multiplicative extension of Rademacher values: `RMF.dirichletSeries_smoothCoeff_eq` with the
Rademacher law in place of the Steinhaus one, the same proof. -/
theorem dirichletSeries_smoothCoeff_eq_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) :
    ∀ᵐ ω ∂μ, ∀ s : ℂ, 0 < s.re →
      dirichletSeries (smoothCoeff (fun ω => compMultExtension fun p => X p ω) y ω) s
        = randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (y + 1) s ω := by
  classical
  have hmeasP : Measurable fun z : ℂ => ‖z‖ ≤ 1 :=
    measurableSet_setOf.1 (measurableSet_le measurable_norm measurable_const)
  have hall : ∀ᵐ ω ∂μ, ∀ p : ℕ, p.Prime → ‖X p ω‖ ≤ 1 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro hp
    exact ((hX.hasLaw p hp).ae_iff hmeasP).2 norm_le_one_rademacherLaw
  filter_upwards [hall] with ω hω
  intro s hs
  have hlt : ∀ {p : ℕ}, p.Prime → ‖compMultCpowHom (fun p => X p ω) s p‖ < 1 := by
    intro p hp
    rw [compMultCpowHom_apply, norm_mul,
      compMultExtension_apply_prime _ hp, Complex.norm_natCast_cpow_of_pos hp.pos,
      Complex.neg_re]
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hlt1 : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-s.re) :=
      Real.rpow_pos_of_pos (by linarith) _
    nlinarith [hω p hp, norm_nonneg (X p ω)]
  have hprod := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := compMultCpowHom (fun p => X p ω) s) hlt (y + 1)).2
  have hds : dirichletSeries (smoothCoeff (fun ω => compMultExtension fun p => X p ω) y ω) s
      = ∑' m : Nat.smoothNumbers (y + 1), compMultCpowHom (fun p => X p ω) s m := by
    rw [tsum_subtype, dirichletSeries]
    refine tsum_congr fun n => ?_
    by_cases hn : n ∈ Nat.smoothNumbers (y + 1)
    · rw [Set.indicator_of_mem hn, smoothCoeff, if_pos hn, compMultCpowHom_apply,
        Complex.cpow_neg, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hn, smoothCoeff, if_neg hn, zero_div]
  rw [hds, hprod.tsum_eq, randomEulerProduct_compMult_eq hs
    (fun p hp => hω p (Nat.prime_of_mem_primesBelow hp))]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [compMultCpowHom_apply, compMultExtension_apply_prime _ (Nat.prime_of_mem_primesBelow hp)]

/-- **Parseval at the shifted abscissa**, `RMF.smoothTailIntegral_eq_line` with the hypothesis it
uses in place of `RMF.IsBoundedRMF`; the same proof. -/
theorem smoothTailIntegral_eq_line_of {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) (y : ℕ)
    (hdir : ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff f y ω) z = randomEulerProduct f (y + 1) z ω)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, smoothTailIntegral f y σ ω
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct f (y + 1) ((σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  filter_upwards [summable_norm_smoothCoeff_div_sqrt_of hbd y, hdir] with ω hsum heuler
  have hσ0 : (0 : ℝ) < σ := by linarith
  have haw : Summable (coeffWeight σ (smoothCoeff f y ω)) :=
    summable_coeffWeight_of_half hσ hsum
  have hkey := integral_normSq_partialSum_eq_line σ (smoothCoeff f y ω) hσ0 haw
  rw [smoothTailIntegral]
  simp_rw [← sum_smoothCoeff f y]
  rw [hkey]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← heuler ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ0)]
  rfl

/-- `RMF.integrableOn_smoothTail` with the hypothesis it uses. -/
lemma integrableOn_smoothTail_of {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1) (y : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, IntegrableOn
      (fun z => ‖smoothPartial f y z ω‖ ^ 2 / z ^ (1 + 2 * σ)) (Set.Ioi (0 : ℝ)) := by
  filter_upwards [summable_norm_smoothCoeff_div_sqrt_of hbd y] with ω hsum
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h := integrableOn_normSq_partialSum σ (smoothCoeff f y ω) hσ0
    (summable_coeffWeight_of_half hσ hsum)
  simpa only [sum_smoothCoeff] using h

/-- **Parseval for the smooth sums of `X^e`.**  Almost surely, for `σ ≥ ½`,
`∫_0^∞ |∑_{n≤z, y-smooth} X^e(n)|² dz/z^{1+2σ} = (2π)⁻¹ ∫_ℝ |F^e(σ+it)/(σ+it)|² dt`. -/
theorem smoothTailIntegral_eq_lineDivSq_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) y σ ω
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ, lineDivSq σ X (y + 1) ω t := by
  filter_upwards [smoothTailIntegral_eq_line_of
    (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n) y
    (dirichletSeries_smoothCoeff_eq_rademacher hX y) hσ] with ω h
  rw [h]
  rfl

/-- **The damped line integral of `F^e` has integrable `q`-th powers**: it is bounded where the
prime values are, by `RMF.integral_lineDivSq_le`, and measurable as a functional of them. -/
lemma integrable_lineDivSq_rpow_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {σ q : ℝ} (hσ : 1 / 2 ≤ σ) (hq : 0 ≤ q) :
    Integrable (fun ω => (∫ t : ℝ, lineDivSq σ X N ω t) ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hmeas : AEStronglyMeasurable (fun ω => (∫ t : ℝ, lineDivSq σ X N ω t) ^ q) μ := by
    have h1 := (measurable_lineFunctional σ N).comp
      (measurable_pi_lambda _ fun p : Nat.Primes => hX.measurable (p : ℕ) p.2)
    have hmap : Measurable fun ω =>
        (lineFunctional σ N (fun p : Nat.Primes => X (p : ℕ) ω)) ^ q := by fun_prop
    refine hmap.aestronglyMeasurable.congr ?_
    filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw N] with ω hω
    rw [lineFunctional_eq σ hσ hω]
  refine (memLp_top_of_bound hmeas
    ((8 * eulerBound N ^ 2 * ∑' n : ℤ, shiftWeight 1 n) ^ q) ?_).integrable le_top
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw N] with ω hω
  have h0 : 0 ≤ ∫ t : ℝ, lineDivSq σ X N ω t :=
    integral_nonneg fun t => by unfold lineDivSq; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 q)]
  exact Real.rpow_le_rpow h0 (integral_lineDivSq_le σ hσ hω) hq

/-! ### The main window and the cut -/

/-- **The main window.**  For `0 < c ≤ 3/2` and `|t| < 1`, `|c + it|² ≤ 4`, so the line integral
against `|c + it|⁻²` is at least a quarter of the unweighted integral over the window. -/
lemma quarter_setIntegral_Ioo_le_integral_div {F : ℝ → ℂ} {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 3 / 2)
    (hint : Integrable fun t : ℝ => ‖F t / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :
    (1 / 4 : ℝ) * (∫ t in Set.Ioo (-1 : ℝ) 1, ‖F t‖ ^ 2)
      ≤ ∫ t : ℝ, ‖F t / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  rw [← integral_const_mul]
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => by positivity) hint.integrableOn ?_)
    (setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => by positivity))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hz : ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hz0 : 0 < c ^ 2 + t ^ 2 := by positivity
  have ht2 : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).2 (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
  have hs2 : c ^ 2 ≤ 9 / 4 := by nlinarith
  rw [norm_div, div_pow, hz]
  calc 1 / 4 * ‖F t‖ ^ 2 = ‖F t‖ ^ 2 / 4 := by ring
    _ ≤ ‖F t‖ ^ 2 / (c ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hz0 (by nlinarith)

/-- **Parseval for the extended mean square, with the two shifts.**  For Rademacher `X`, `V > 0`,
`x ≥ 4` and `log x ≥ 3V + 3`, almost surely `M ≥ (8π)⁻¹ ∫_{|t|<1} |F^e(½+2V/log x+it)|² dt`
`- π⁻¹ e^{-V} ∫_ℝ |F^e(½+V/log x+it)/(½+V/log x+it)|² dt`, where
`M = ∫_1^{√x/(1+1/log x)} |∑_{n≤z} X^e(n)|² dz/z²` and `F^e` is the Euler product over the primes
up to `x`: the Steinhaus chain's comparison of `M` with the smooth tail integrals at the two
abscissae, and the cut of the weighted chain. -/
theorem extendedMeanSquare_ge_line {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V : ℝ} (hV : 0 < V)
    (hx : 3 * V + 3 ≤ Real.log x) (hx4 : 4 ≤ x) :
    ∀ᵐ ω ∂μ, (8 * Real.pi)⁻¹ * (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
      - Real.pi⁻¹ * Real.exp (-V)
          * (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t)
      ≤ ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
          ‖randomSum (fun ω => compMultExtension fun p => X p ω) z ω‖ ^ 2 / z ^ 2 := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hV0 : 0 ≤ V / Real.log x := by positivity
  have hσ₁h : (1 : ℝ) / 2 ≤ 1 / 2 + 2 * V / Real.log x := by
    have : 0 ≤ 2 * V / Real.log x := by positivity
    linarith
  have hσ₂h : (1 : ℝ) / 2 ≤ 1 / 2 + V / Real.log x := by linarith
  have hσ₂₁ : 1 / 2 + V / Real.log x ≤ 1 / 2 + 2 * V / Real.log x := by
    have : V / Real.log x ≤ 2 * V / Real.log x :=
      div_le_div_of_nonneg_right (by linarith) hlog0.le
    linarith
  have hσ₁3 : 1 / 2 + 2 * V / Real.log x ≤ 3 / 2 := by
    have : 2 * V / Real.log x ≤ 1 := (div_le_one hlog0).2 (by linarith)
    linarith
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun p => X p ω with hgdef
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖g ω n‖ ≤ 1 := fun n =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  filter_upwards [smoothTailIntegral_eq_lineDivSq_extended hX ⌊x⌋₊ hσ₁h,
    smoothTailIntegral_eq_lineDivSq_extended hX ⌊x⌋₊ hσ₂h,
    integrableOn_smoothTail_of hbd ⌊x⌋₊ hσ₁h, integrableOn_smoothTail_of hbd ⌊x⌋₊ hσ₂h,
    ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊x⌋₊ + 1)]
    with ω hP₁ hP₂ hI₁ hI₂ hω
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  have hw1 : 1 ≤ w := one_le_sqrt_div hx4
  have hwsq : w ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg x) hr1
  -- the cut
  have hsplit := setIntegral_Ioi_le_Ioc_add_mul (A := fun u => smoothPartial g ⌊x⌋₊ u ω)
    (fun u hu => smoothPartial_eq_zero hu ω) hw1 hσ₂₁ hI₁ hI₂
  rw [smoothTailIntegral] at hP₁ hP₂
  rw [hP₁, hP₂] at hsplit
  -- on `(1, w]` the shifted smooth-tail integrand is below the mean-square integrand
  have hb : (∫ u in Set.Ioc 1 w,
        ‖smoothPartial g ⌊x⌋₊ u ω‖ ^ 2 / u ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)))
      ≤ ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z ^ 2 :=
    setIntegral_mono_on
      (hI₁.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi zero_le_one)))
      (integrableOn_meanSquare_integrand g le_rfl ω) measurableSet_Ioc fun z hz =>
        smoothTail_integrand_le (by linarith) hσ₁h hz.1.le (le_trans hz.2 hwsq) ω
  -- the damping factor
  have hd : w ^ (-(2 * ((1 / 2 + 2 * V / Real.log x) - (1 / 2 + V / Real.log x))))
      ≤ 2 * Real.exp (-V) := by
    have he : (1 / 2 + 2 * V / Real.log x) - (1 / 2 + V / Real.log x)
        = 2 * V / Real.log x - V / Real.log x := by ring
    rw [he]
    exact rpow_neg_sqrt_div_le hV hx0 hx
  have hJ₂ : 0 ≤ ∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t :=
    integral_nonneg fun t => by unfold lineDivSq; positivity
  have hfull := parseval_assembly_full hb hsplit hd hJ₂
  -- the window
  have hint : Integrable fun t : ℝ =>
      ‖randomEulerProduct g (⌊x⌋₊ + 1)
          (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
        / (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    integrable_lineDivSqOf (1 / 2 + 2 * V / Real.log x) hσ₁h
      (measurable_randomEulerProduct_compMult_line (1 / 2 + 2 * V / Real.log x) hσ₁h hω)
      (fun t => norm_randomEulerProduct_le hω (by simpa using hσ₁h))
  have hwin := quarter_setIntegral_Ioo_le_integral_div
    (F := fun t => randomEulerProduct g (⌊x⌋₊ + 1)
      (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω)
    (by linarith) hσ₁3 hint
  have hwin' : (1 / 4 : ℝ) * (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct g (⌊x⌋₊ + 1)
          (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
      ≤ ∫ t : ℝ, lineDivSq (1 / 2 + 2 * V / Real.log x) X (⌊x⌋₊ + 1) ω t := hwin
  have hπ : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hwin' hπ.le
  have e1 : (2 * Real.pi)⁻¹ * ((1 / 4 : ℝ) * (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct g (⌊x⌋₊ + 1)
          (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2))
      = (8 * Real.pi)⁻¹ * (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct g (⌊x⌋₊ + 1)
          (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) := by
    ring
  linarith

/-! ### The assembly -/

/-- The constants of the assembly.  `ES, ER, EM, EW, EJ` are the moment, the rough prime sum, the
mean square, the window and the damped line, `L = log x`.  Khintchine's factor lies in `[1/6, 1]`,
`8^{-q}(8π)^{-q} ≥ (64π)⁻¹`, `40^q ≤ 40`, and every other factor is at most one. -/
lemma extended_euler_lower_arith {ES ER EM EW EJ x L V q : ℝ} (hL : 1 ≤ L) (hx : 0 < x)
    (hq0 : 0 < q) (hq12 : q ≤ 1 / 2) (hEW : 0 ≤ EW) (hEJ : 0 ≤ EJ)
    (hkh : (3 : ℝ) ^ (-(1 - q)) * ER ≤ 2 ^ (1 - 2 * q) * ES)
    (h9 : (x / (8 * L)) ^ q * EM - (40 * x / L) ^ q ≤ ER)
    (hPar : (8 * Real.pi)⁻¹ ^ q * EW - (Real.pi⁻¹ * Real.exp (-V)) ^ q * EJ ≤ EM) :
    (384 * Real.pi)⁻¹ * (x / L) ^ q * EW - 40 * Real.exp (-(V * q)) * (x / L) ^ q * EJ
      - 40 * (x / L) ^ q ≤ ES := by
  have hL0 : 0 < L := by linarith
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hxL : 0 < x / L := div_pos hx hL0
  have hl0 : 0 < (x / L) ^ q := Real.rpow_pos_of_pos hxL _
  have h8 : (x / (8 * L)) ^ q = (8 : ℝ)⁻¹ ^ q * (x / L) ^ q := by
    rw [show x / (8 * L) = (8 : ℝ)⁻¹ * (x / L) by field_simp,
      Real.mul_rpow (by norm_num) hxL.le]
  have h40 : (40 * x / L) ^ q = (40 : ℝ) ^ q * (x / L) ^ q := by
    rw [show 40 * x / L = 40 * (x / L) by ring, Real.mul_rpow (by norm_num) hxL.le]
  have hpe : (Real.pi⁻¹ * Real.exp (-V)) ^ q = Real.pi⁻¹ ^ q * Real.exp (-(V * q)) := by
    rw [Real.mul_rpow (inv_nonneg.2 hπ0.le) (Real.exp_pos _).le, ← Real.exp_mul, neg_mul]
  rw [h8, h40] at h9
  rw [hpe] at hPar
  have ht : (0 : ℝ) < 2 ^ (1 - 2 * q) := Real.rpow_pos_of_pos two_pos _
  have hk16 : (1 / 6 : ℝ) ≤ (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) := by
    have h3 : (3 : ℝ)⁻¹ ≤ (3 : ℝ) ^ (-(1 - q)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (1 - 2 * q) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - 2 * q) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    rw [le_div_iff₀ ht]
    linarith
  have hk1 : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) ≤ 1 := by
    have h3 : (3 : ℝ) ^ (-(1 - q)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ 2 ^ (1 - 2 * q) := Real.one_le_rpow (by norm_num) (by linarith)
    rw [div_le_one ht]
    linarith
  have hk0 : 0 ≤ (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) := by linarith
  have hmain : (64 * Real.pi)⁻¹ ≤ (8 : ℝ)⁻¹ ^ q * (8 * Real.pi)⁻¹ ^ q := by
    rw [← Real.mul_rpow (by norm_num) (inv_nonneg.2 (by positivity)), ← mul_inv,
      show (8 : ℝ) * (8 * Real.pi) = 64 * Real.pi by ring]
    calc (64 * Real.pi)⁻¹ = (64 * Real.pi)⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (64 * Real.pi)⁻¹ ^ q := Real.rpow_le_rpow_of_exponent_ge (by positivity)
          (inv_le_one_of_one_le₀ (by linarith)) (by linarith)
  have ha8 : 0 ≤ (8 : ℝ)⁻¹ ^ q := Real.rpow_nonneg (by norm_num) _
  have h8le : (8 : ℝ)⁻¹ ^ q ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hq0.le
  have haπ : 0 ≤ Real.pi⁻¹ ^ q := Real.rpow_nonneg (inv_nonneg.2 hπ0.le) _
  have hπle : Real.pi⁻¹ ^ q ≤ 1 :=
    Real.rpow_le_one (inv_nonneg.2 hπ0.le) (inv_le_one_of_one_le₀ hπ1) hq0.le
  have hs40 : 0 ≤ (40 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  have h40le : (40 : ℝ) ^ q ≤ 40 := by
    calc (40 : ℝ) ^ q ≤ 40 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 40 := Real.rpow_one 40
  have he0 : 0 ≤ Real.exp (-(V * q)) := (Real.exp_pos _).le
  have hkES : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) * ER ≤ ES := by
    rw [div_mul_eq_mul_div, div_le_iff₀ ht]
    linarith
  have p1 := mul_le_mul_of_nonneg_left h9 hk0
  have p2 := mul_le_mul_of_nonneg_left hPar (mul_nonneg hk0 (mul_nonneg ha8 hl0.le))
  have p3 : 1 / 6 * ((64 * Real.pi)⁻¹ * ((x / L) ^ q * EW))
      ≤ (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q)
        * ((8 : ℝ)⁻¹ ^ q * (8 * Real.pi)⁻¹ ^ q * ((x / L) ^ q * EW)) :=
    mul_le_mul hk16 (mul_le_mul_of_nonneg_right hmain (mul_nonneg hl0.le hEW))
      (mul_nonneg (inv_nonneg.2 (by positivity)) (mul_nonneg hl0.le hEW)) hk0
  have p4 : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) * ((8 : ℝ)⁻¹ ^ q * Real.pi⁻¹ ^ q)
        * (Real.exp (-(V * q)) * (x / L) ^ q * EJ)
      ≤ 1 * (Real.exp (-(V * q)) * (x / L) ^ q * EJ) :=
    mul_le_mul_of_nonneg_right (mul_le_one₀ hk1 (mul_nonneg ha8 haπ) (mul_le_one₀ h8le haπ hπle))
      (mul_nonneg (mul_nonneg he0 hl0.le) hEJ)
  have p5 : (3 : ℝ) ^ (-(1 - q)) / 2 ^ (1 - 2 * q) * (40 : ℝ) ^ q * (x / L) ^ q
      ≤ 1 * 40 * (x / L) ^ q :=
    mul_le_mul_of_nonneg_right (mul_le_mul hk1 h40le hs40 zero_le_one) hl0.le
  have hEJl : 0 ≤ Real.exp (-(V * q)) * (x / L) ^ q * EJ :=
    mul_nonneg (mul_nonneg he0 hl0.le) hEJ
  have e384 : (384 * Real.pi)⁻¹ = 1 / 6 * (64 * Real.pi)⁻¹ := by
    rw [show (384 : ℝ) * Real.pi = 6 * (64 * Real.pi) by ring, mul_inv]
    norm_num
  rw [e384]
  nlinarith

/-- **The extended lower reduction, errors explicit** (Proposition 4.3 of the paper, before the
Euler-product ratio).  There are `c, C > 0` and `x₀`, independent of `X`, `V`, `x` and `q`, such
that for every Rademacher `X`, `V > 0`, `x ≥ x₀` with `log x ≥ 3V + 3`, and `0 < q ≤ ½`,
`c (x/log x)^q E[(∫_{|t|<1} |F^e(½+2V/log x+it)|² dt)^q]`
`  - C e^{-Vq} (x/log x)^q E[(∫_ℝ |F^e(½+V/log x+it)/(½+V/log x+it)|² dt)^q] - C (x/log x)^q`
`  ≤ E|∑_{n≤x} X^e(n)|^{2q}`. -/
theorem exists_le_integral_rpow_extendedSum_euler :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ V x q : ℝ, 0 < V → x₀ ≤ x → 3 * V + 3 ≤ Real.log x → 0 < q → q ≤ 1 / 2 →
          c * (x / Real.log x) ^ q * (∫ ω, (∫ t in Set.Ioo (-1 : ℝ) 1,
              ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
                (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ)
            - C * Real.exp (-(V * q)) * (x / Real.log x) ^ q
                * (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
            - C * (x / Real.log x) ^ q
          ≤ ∫ ω, ‖randomSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨x₁, hL9⟩ := meanSquare_le_sum_extended (Ω := Ω)
  refine ⟨(384 * Real.pi)⁻¹, 40, max x₁ 4, by positivity, by norm_num,
    fun X μ hX V x q hV hx hlogV hq0 hq12 => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hq1 : q ≤ 1 := by linarith
  have hσ₂h : (1 : ℝ) / 2 ≤ 1 / 2 + V / Real.log x := by
    have : 0 ≤ V / Real.log x := div_nonneg hV.le (by linarith)
    linarith
  obtain ⟨hSp, hSx, hScov⟩ := primesIoc_sqrt_spec hx0.le
  have hkh := khintchine_rough_extended hX (by linarith) (floor_lt_floor_sqrt_add_one_sq hx0.le)
    hq0 (by linarith)
  have h9 := hL9 X μ hX x q hxx₁ hq0.le hq1 (largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) hSp hSx hScov
  have hMi : Integrable (fun ω => ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
      ‖randomSum (fun ω => compMultExtension fun p => X p ω) z ω‖ ^ 2 / z ^ 2) μ :=
    (integrable_meanSquare_prod_of (fun n => hX.measurable_compMultExtension n)
      (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n)
      le_rfl).integral_prod_left
  have hM0 : ∀ ω, 0 ≤ ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
      ‖randomSum (fun ω => compMultExtension fun p => X p ω) z ω‖ ^ 2 / z ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun z _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hPar := integral_rpow_sub_le_of_ae (extendedMeanSquare_ge_line hX hV hlogV hx4)
    (by positivity) (by positivity) hq0.le hq1
    (fun ω => setIntegral_nonneg measurableSet_Ioo fun t _ => sq_nonneg _)
    (fun ω => integral_nonneg fun t => by unfold lineDivSq; positivity)
    hM0 (integrable_lineDivSq_rpow_extended hX (⌊x⌋₊ + 1) hσ₂h hq0.le)
    (integrable_rpow_of_integrable hMi (Filter.Eventually.of_forall hM0) hq0.le hq1)
  exact extended_euler_lower_arith hlog hx0 hq0 hq12
    (integral_nonneg fun ω => Real.rpow_nonneg
      (setIntegral_nonneg measurableSet_Ioo fun t _ => sq_nonneg _) _)
    (integral_nonneg fun ω => Real.rpow_nonneg
      (integral_nonneg fun t => by unfold lineDivSq; positivity) _)
    hkh h9 hPar

end RMF
