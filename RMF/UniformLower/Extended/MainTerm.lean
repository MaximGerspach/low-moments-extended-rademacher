/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.KernelZeta
import RMF.UniformLower.PerScaleShort
import RMF.Weighted.ExtendedLowerParseval

/-!
# The extended sum's explicit lower bound: the main term

The main term's lower bound for the extended sum's line integral
`J_Y(σ) = ∫_ℝ lineDivSq (½ + σ) X y ω t dt = ∫_ℝ |F^e_y(s)/s|² dt`, `s = ½ + σ + it`, with the
weighted sum's constants.  The per-scale estimates are about the squarefree Euler product `F_y`
only and are reused; the one step that sees the kernel is the head-window mass, which for the
weighted sum is at most half the line integral of `|F_y(s)/(s - ½)|²`
(`RMF.ae_sum_headWindowMass_le_half`).

* **The windows**: `halfWindow k ⊆ (0, e^{-20}]` for `k ≥ 20`, where `σ² + t² ≤ 10⁻¹⁶`, so for
  `σ log y ≥ 16` the extended integrand is at least `1 - 10⁻⁶` times the weighted one
  (`RMF.ae_lineDiv_le_lineDivSq_of_window`).  The kernel is even in the height
  (`RMF.zetaKernel_neg`), so `J_Y` is twice its positive half
  (`RMF.ae_integral_lineDivSq_eq_two_mul`), and `(1 - 10⁻⁶)∑_k mass_k ≤ J_Y/2`
  (`RMF.ae_sum_headWindowMass_le_half_ext`).
* **The rounding**: the proof of `RMF.le_integral_normSq_high_mul_exp` gives `e^{-0.5917}` in
  place of `e^{-0.592}` (`RMF.le_integral_normSq_high_mul_exp_sharp`), and
  `(1 - 10⁻⁶)e^{-0.5917} ≥ e^{-0.592}`, so `G = e^{-0.592}/2` survives.
* **The main term**, for `16 ≤ σ log y` and the hypotheses of the weighted sum's:
  `RMF.le_rpow_mul_integral_rpow_lineDivSq_explicit` and
  `RMF.le_rpow_mul_integral_rpow_lineDivSq_explicit_short`, whose left sides are those of
  `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_explicit` and `…_explicit_short` verbatim.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The kernel is even in the height -/

/-- `shiftLine σ (-t)` is the conjugate of `shiftLine σ t`. -/
lemma shiftLine_neg_eq_conj (σ t : ℝ) : shiftLine σ (-t) = starRingEnd ℂ (shiftLine σ t) := by
  apply Complex.ext <;> simp [shiftLine]

/-- **The kernel is even in the height**: `K_N(σ, -t) = K_N(σ, t)`, as `p^{-s̄} = conj(p^{-s})`. -/
lemma zetaKernel_neg (N : ℕ) (σ t : ℝ) : zetaKernel N σ (-t) = zetaKernel N σ t := by
  unfold zetaKernel
  rw [shiftLine_neg_eq_conj, Complex.norm_conj]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primesBelow hp
  have h : 1 - ((p : ℂ) ^ (-(starRingEnd ℂ) (shiftLine σ t))) ^ 2
      = starRingEnd ℂ (1 - ((p : ℂ) ^ (-shiftLine σ t)) ^ 2) := by
    rw [← conj_natCast_cpow_neg hp'.pos, map_sub, map_one, map_pow]
  rw [h, Complex.norm_conj]

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The extended line integrand is even in the height**, almost surely, for `σ > -½`: it is
`|F_N(s)|²K_N(σ, t)` (`RMF.ae_lineDivSq_eq_mul_zetaKernel`), both factors even
(`RMF.ae_forall_norm_randomEulerProduct_shiftLine_neg`, `RMF.zetaKernel_neg`). -/
theorem ae_forall_lineDivSq_neg (hX : IsRademacherPrimeValues X μ) (N : ℕ) {σ : ℝ}
    (hσ : -(1 / 2) < σ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, lineDivSq (1 / 2 + σ) X N ω (-t) = lineDivSq (1 / 2 + σ) X N ω t := by
  filter_upwards [ae_lineDivSq_eq_mul_zetaKernel hX N,
    ae_forall_norm_randomEulerProduct_shiftLine_neg hX N σ] with ω hk hrefl
  intro t
  rw [hk σ hσ (-t), hk σ hσ t, hrefl t, zetaKernel_neg]

/-- **The extended line integral is twice its positive half**, almost surely, for `σ ≥ 0`. -/
theorem ae_integral_lineDivSq_eq_two_mul (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ}
    (hσ0 : 0 ≤ σ) :
    ∀ᵐ ω ∂μ, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u)
      = 2 * ∫ u in Set.Ioi 0, lineDivSq (1 / 2 + σ) X y ω u := by
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw y,
    ae_forall_lineDivSq_neg hX y (by linarith : -(1 / 2) < σ)] with ω hω hrefl
  have hint : Integrable fun u : ℝ => lineDivSq (1 / 2 + σ) X y ω u :=
    integrable_line_integrand (1 / 2 + σ) (by linarith) hω
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
  rw [Set.compl_Ioi] at hsplit
  have hneg : ∫ u in Set.Iic (0 : ℝ), lineDivSq (1 / 2 + σ) X y ω u
      = ∫ u in Set.Ioi 0, lineDivSq (1 / 2 + σ) X y ω u := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun u => lineDivSq (1 / 2 + σ) X y ω u)
    rw [neg_zero] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Iic fun u _ => (hrefl u).symm
  linarith

/-! ### The head-window masses against the extended line integral -/

/-- `σ² + t² ≤ 10⁻¹⁶` for `0 ≤ σ, t ≤ e^{-20}`. -/
lemma sq_add_sq_le_of_le_exp_neg_twenty {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ Real.exp (-20))
    (ht0 : 0 ≤ t) (ht : t ≤ Real.exp (-20)) : σ ^ 2 + t ^ 2 ≤ 1 / 10 ^ 16 := by
  have he : Real.exp (-20) ≤ 1 / (15 * 10 ^ 7) := by interval_decide (trust := kernel)
  have h3 : σ ^ 2 ≤ (1 / (15 * 10 ^ 7)) ^ 2 := pow_le_pow_left₀ hσ0 (hσ.trans he) 2
  have h4 : t ^ 2 ≤ (1 / (15 * 10 ^ 7)) ^ 2 := pow_le_pow_left₀ ht0 (ht.trans he) 2
  have h5 : 2 * (1 / (15 * 10 ^ 7) : ℝ) ^ 2 ≤ 1 / 10 ^ 16 := by norm_num
  linarith

/-- **The masses, summed, against the extended line integral**, almost surely: for
`σ log y ≥ 16` and scales `k ≥ 20` with `σ ≤ e^{-k}`,
`(1 - 10⁻⁶)∑_{k ∈ K} mass_k ≤ ½∫_ℝ lineDivSq (½ + σ) X y ω t dt`.  The windows lie in
`(0, e^{-20}]`, where `(1 - 10⁻⁶)|F_y(s)/(σ+it)|² ≤ lineDivSq`
(`RMF.ae_lineDiv_le_lineDivSq_of_window`), and the extended line integral is twice its positive
half: `RMF.ae_sum_headWindowMass_le_half` with the kernel compared on the windows. -/
theorem ae_sum_headWindowMass_le_half_ext (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ0 : 0 < σ) {y : ℕ} {K : Finset ℕ} {r : ℕ → ℕ} (hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)))
    (hKy : ∀ k ∈ K, ⌊blockScale k (r k)⌋₊ + 1 ≤ y) (hσy : 16 ≤ σ * Real.log y)
    (hK20 : ∀ k ∈ K, 20 ≤ k) :
    ∀ᵐ ω ∂μ, (1 - 1 / 10 ^ 6) * ∑ k ∈ K, headWindowMass X μ σ k (r k) y ω
      ≤ (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) / 2 := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw 0 y,
    ae_lineDiv_le_lineDivSq_of_window hX y, ae_integral_lineDivSq_eq_two_mul hX y hσ0.le]
    with ω hω0 hwin htwo
  have hω : ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1 := by
    simpa only [primesIco_zero] using hω0
  rw [htwo, mul_div_cancel_left₀ _ two_ne_zero]
  have hline : Integrable fun u : ℝ => lineDivSq (1 / 2 + σ) X y ω u :=
    integrable_line_integrand (1 / 2 + σ) (by linarith) hω
  have hline0 : ∀ u, 0 ≤ lineDivSq (1 / 2 + σ) X y ω u := fun u => by
    unfold lineDivSq; positivity
  rcases K.eq_empty_or_nonempty with hK | ⟨k₁, hk₁⟩
  · rw [hK, Finset.sum_empty, mul_zero]
    exact setIntegral_nonneg measurableSet_Ioi fun u _ => hline0 u
  -- `σ ≤ e^{-20}`, and the windows lie in `A = (0, e^{-20}]`
  have hσ20 : σ ≤ Real.exp (-20) := by
    have h20 : (20 : ℝ) ≤ k₁ := by exact_mod_cast hK20 k₁ hk₁
    exact (hKσ k₁ hk₁).trans (Real.exp_le_exp.2 (by linarith))
  set A : Set ℝ := Set.Ioc 0 (Real.exp (-20)) with hAdef
  have hwinA : ∀ k : ℕ, 20 ≤ k → ∀ t ∈ halfWindow k, t ∈ A := by
    intro k hk t ht
    have h20 : (20 : ℝ) ≤ k := by exact_mod_cast hk
    exact ⟨lt_of_lt_of_le (Real.exp_pos _) ht.1,
      ht.2.trans (Real.exp_le_exp.2 (by linarith))⟩
  set F : ℝ → ℂ := fun t => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
    (shiftLine σ t) ω with hF
  set F' : ℝ → ℂ := Set.indicator A F with hF'
  have hint0 : Integrable fun u : ℝ => ‖F u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [hF]
    simp_rw [shiftLine_eq_half_add]
    exact integrable_line_div_sq_half_add hσ0 hω
  have hF'eq : ∀ u : ℝ, ‖F' u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2
      = Set.indicator A (fun u => ‖F u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) u := by
    intro u
    by_cases hu : u ∈ A
    · rw [hF', Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [hF', Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      simp
  have hint : Integrable fun u : ℝ => ‖F' u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    simp_rw [hF'eq]
    exact hint0.indicator measurableSet_Ioc
  -- the weighted sum's window bound, for the integrand cut down to `A`
  have hsum := sum_setIntegral_halfWindow_le_integral_div (K := K) (σ := σ) hσ0 (F := F')
    (f := fun k => Set.indicator A (fun h => (hp1Tube X μ y k (r k) σ h).indicator
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h) ω‖ ^ 2) ω))
    (fun k hk => (integrableOn_hp1Tube_normSq hX hσ0.le
      (primeBlockSub_subset_of_cut_le (hKy k hk)) ω).congr_fun
      (fun t ht => by beta_reduce; rw [Set.indicator_of_mem (hwinA k (hK20 k hk) t ht)])
      measurableSet_Icc)
    (fun k _ t => Set.indicator_nonneg (fun _ _ => Set.indicator_nonneg
      (fun _ _ => by positivity) ω) t)
    (fun k _ t => by
      by_cases ht : t ∈ A
      · rw [Set.indicator_of_mem ht, hF', Set.indicator_of_mem ht]
        by_cases hm : ω ∈ hp1Tube X μ y k (r k) σ t
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]
          positivity
      · rw [Set.indicator_of_notMem ht, hF', Set.indicator_of_notMem ht]
        simp)
    hint hKσ
  rw [integral_congr_ae (Filter.Eventually.of_forall hF'eq),
    integral_indicator measurableSet_Ioc] at hsum
  have hmass : ∑ k ∈ K, headWindowMass X μ σ k (r k) y ω
      ≤ ∫ u in A, ‖F u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) hsum
    rw [headWindowMass]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc fun t ht => by
      rw [Set.indicator_of_mem (hwinA k (hK20 k hk) t ht)]
  -- on `A` the kernel is at least `1 - 10⁻⁶`
  have hker : (1 - 1 / 10 ^ 6) * ∫ u in A, ‖F u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2
      ≤ ∫ u in A, lineDivSq (1 / 2 + σ) X y ω u := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hint0.integrableOn.const_mul _) hline.integrableOn
      measurableSet_Ioc fun u hu => ?_
    exact hwin σ u hσy (sq_add_sq_le_of_le_exp_neg_twenty hσ0.le hσ20 hu.1.le hu.2)
  have hAI : ∫ u in A, lineDivSq (1 / 2 + σ) X y ω u
      ≤ ∫ u in Set.Ioi 0, lineDivSq (1 / 2 + σ) X y ω u :=
    setIntegral_mono_set hline.integrableOn (Filter.Eventually.of_forall hline0)
      Set.Ioc_subset_Ioi_self.eventuallyLE
  have hc0 : (0 : ℝ) ≤ 1 - 1 / 10 ^ 6 := by norm_num
  have h1 := mul_le_mul_of_nonneg_left hmass hc0
  linarith

/-! ### The sum over scales -/

/-- **The sum over scales against the extended line integral**: as
`RMF.le_integral_rpow_integral_lineDiv_head_symm`, for `σ log y ≥ 16` and scales `k ≥ 20`, with
`2^{2q-1}(1 - 10⁻⁶)^q` in place of `2^{2q-1}` and `J_Y(σ)` in place of the weighted line
integral (`RMF.ae_sum_headWindowMass_le_half_ext`). -/
theorem le_integral_rpow_lineDivSq_head_symm (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ0 : 0 < σ) {y : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {k₀ : ℕ}
    {K : Finset ℕ} {r : ℕ → ℕ} (hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)))
    (hK₀ : ∀ k ∈ K, k₀ ≤ k) (hmult : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ + 2 ≤ k₂ → k₂ - k₁ ≤ r k₁)
    (hKy : ∀ k ∈ K, ⌊blockScale k (r k)⌋₊ + 1 ≤ y) {γ : ℕ → ℝ}
    (hper : ∀ k ∈ K, γ k ≤ ∫ ω, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
      (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω ∂μ)
    (hσy : 16 ≤ σ * Real.log y) (hK20 : ∀ k ∈ K, 20 ≤ k) :
    2 ^ (2 * q - 1) * (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, γ k
      ≤ ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc0 : (0 : ℝ) < 1 - 1 / 10 ^ 6 := by norm_num
  have hint : ∀ k ∈ K, Integrable (fun ω => (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
      (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω) μ := fun k hk =>
    integrable_indicator_rpow_headWindowMass hX hσ0.le hq0
      (primeBlockSub_subset_of_cut_le (hKy k hk))
      ((measurableSet_halfLadder hX σ k₀ k).inter (measurableSet_hp1After hX σ k (r k)))
  have hline : Integrable (fun ω => (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q) μ :=
    integrable_lineDivSq_rpow_extended hX y (by linarith) hq0
  have hpt : ∀ᵐ ω ∂μ, (1 - 1 / 10 ^ 6) ^ q
        * ∑ k ∈ K, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
          (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω
      ≤ 2 ^ (1 - 2 * q) * (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q := by
    filter_upwards [ae_sum_headWindowMass_le_half_ext hX hσ0 hKσ hKy hσy hK20] with ω hω
    have h1 := sum_indicator_rpow_le_mul_rpow_sum (K := K)
      (E := fun k => halfLadder X σ k₀ k ∩ hp1After X σ k (r k)) (m := 2)
      (fun x => by convert card_filter_mem_halfLadder_inter_hp1After_le_two X σ hK₀ hmult x)
      (a := fun k ω => headWindowMass X μ σ k (r k) y ω)
      (fun k ω => headWindowMass_nonneg X μ σ k (r k) y ω) hq0 hq1 ω
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2] at h1
    have hJ0 : 0 ≤ ∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u :=
      integral_nonneg fun _ => by unfold lineDivSq; positivity
    have hS0 : 0 ≤ ∑ k ∈ K, headWindowMass X μ σ k (r k) y ω :=
      Finset.sum_nonneg fun k _ => headWindowMass_nonneg X μ σ k (r k) y ω
    have h3 := Real.rpow_le_rpow (mul_nonneg hc0.le hS0) hω hq0
    rw [Real.mul_rpow hc0.le hS0, Real.div_rpow hJ0 (by norm_num)] at h3
    calc (1 - 1 / 10 ^ 6) ^ q
          * ∑ k ∈ K, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
            (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω
        ≤ (1 - 1 / 10 ^ 6) ^ q
          * (2 ^ (1 - q) * (∑ k ∈ K, headWindowMass X μ σ k (r k) y ω) ^ q) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ (1 - q)
          * ((1 - 1 / 10 ^ 6) ^ q * (∑ k ∈ K, headWindowMass X μ σ k (r k) y ω) ^ q) := by
          ring
      _ ≤ 2 ^ (1 - q) * ((∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q / 2 ^ q) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 ^ (1 - 2 * q) * (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q := by
          rw [show (1 : ℝ) - 2 * q = (1 - q) - q by ring,
            Real.rpow_sub (by norm_num : (0 : ℝ) < 2) (1 - q)]
          ring
  calc 2 ^ (2 * q - 1) * (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, γ k
      ≤ 2 ^ (2 * q - 1) * ((1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, ∫ ω,
          (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
            (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω ∂μ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)) (by positivity)
    _ = 2 ^ (2 * q - 1) * ∫ ω, (1 - 1 / 10 ^ 6) ^ q
          * ∑ k ∈ K, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
            (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω ∂μ := by
        rw [integral_const_mul, integral_finsetSum K hint]
    _ ≤ 2 ^ (2 * q - 1) * ∫ ω, 2 ^ (1 - 2 * q)
          * (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ :=
        mul_le_mul_of_nonneg_left
          (integral_mono_ae ((integrable_finsetSum K hint).const_mul _) (hline.const_mul _) hpt)
          (by positivity)
    _ = ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
        rw [integral_const_mul, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          show 2 * q - 1 + (1 - 2 * q) = 0 by ring, Real.rpow_zero, one_mul]

/-- **The sum over scales against the extended line integral, every producer plugged in**: under
the hypotheses of `RMF.le_integral_rpow_integral_lineDiv_numeral` and `16 ≤ σ log y`,
`2^{2q-1}(1 - 10⁻⁶)^q∑_{k ∈ K} Γ(q, k - k₀)·N_q(k)·(E‖F_{[c_k,y)}(s_σ)‖²e^k/√(T - k))^q
  ≤ E[J_Y(σ)^q]`. -/
theorem le_integral_rpow_lineDivSq_numeral (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 2000 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    (hσy : 16 ≤ σ * Real.log y) :
    2 ^ (2 * q - 1) * (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q
      ≤ ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  refine le_integral_rpow_lineDivSq_head_symm hX hσ hq0.le (by linarith) (k₀ := k₀)
    (r := fun k => T - k) (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.2.2.2.2)
    (fun k hk => (hK k hk).1.le) (fun k₁ _ k₂ hk₂ _ => by have := hkT k₂ hk₂; omega)
    (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.1) (fun k hk => ?_) hσy
    (fun k hk => by have := (hK k hk).1; omega)
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
  exact le_integral_indicator_rpow_headWindowMass_numeral hX hσ.le hq0 hq1 hk₀ (hK k hk).1
    (hKq k hk) h1 h2 h3 (by have := (hK k hk).2; omega)

/-! ### `E‖F_{[c_k,y)}(s_σ)‖²e^k` from below, with the rounding slack -/

/-- **`E‖F_{[c_k,y)}(s_σ)‖²e^k` from below, at `0.5917`**: the proof of
`RMF.le_integral_normSq_high_mul_exp` gives `0.5916 + 3.16·10⁻⁶ + 10⁻²⁰ ≤ 0.5917` in place of its
`0.592`, so `E‖F_{[c_k,y)}(s_σ)‖²·e^k ≥ e^{-0.5917}/(2σ)`. -/
theorem le_integral_normSq_high_mul_exp_sharp (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 < σ) {k n y : ℕ} (hk : 20 ≤ k) (hny : ⌊blockScale k n⌋₊ + 1 ≤ y)
    (ha : 2 * σ * Real.exp (k : ℝ) ≤ 1) (hℓ : 3 ≤ 2 * σ * Real.exp ((n : ℝ) + k)) :
    Real.exp (-0.5917) / (2 * σ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ) := by
  have hc0 : scaleCut (k : ℝ) = ⌊blockScale k 0⌋₊ + 1 := rfl
  set t : ℕ → ℝ := fun p => (p : ℝ) ^ (-1 - 2 * σ) with ht
  have ht0 : ∀ p, 0 ≤ t p := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- the moment as a product, and the product from below
  have hprod : Real.exp (rangeCosSum (scaleCut (k : ℝ)) y σ 0 - rangeSqSum (scaleCut (k : ℝ)) y σ)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ := by
    rw [integral_normSq_Ico_eq_prod hX (scaleCut (k : ℝ)) y σ 0, rangeCosSum, rangeSqSum,
      ← Finset.sum_sub_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p _ => ?_
    have e : Real.cos (0 * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ) - ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2
        = t p - t p ^ 2 := by simp [ht]
    rw [e]
    exact exp_sub_sq_le_one_add (ht0 p)
  -- the quadratic remainder
  have hsq : rangeSqSum (scaleCut (k : ℝ)) y σ ≤ 1 / 10 ^ 20 := by
    have h := rangeSqSum_rest_le (r := 0) (y := y) hk hσ.le
    rw [← hc0] at h
    linarith
  -- the linear sum over the full blocks
  have hcut : scaleCut (k : ℝ) ≤ ⌊blockScale k n⌋₊ + 1 := by
    rw [hc0]; exact cut_mono k (Nat.zero_le n)
  have hlin : ∑ m ∈ Finset.Ico 0 n, blockCosSum k σ 0 m
      ≤ rangeCosSum (scaleCut (k : ℝ)) y σ 0 := by
    rw [rangeCosSum_split hcut hny, hc0, rangeCosSum_cut_eq k (Nat.zero_le n) σ 0]
    have hrest : 0 ≤ rangeCosSum (⌊blockScale k n⌋₊ + 1) y σ 0 := by
      unfold rangeCosSum
      exact Finset.sum_nonneg fun p _ => by simp only [zero_mul, Real.cos_zero, one_mul]; positivity
    linarith
  have htel := abs_sum_blockCosSum_sub_integral_le_two_regime (τ := 0) (σ := σ) (θ := k)
    (Nat.zero_le n) le_rfl hσ.le (by simp)
  have herr : blockCosTelErr (k : ℝ) 0 0 ≤ 3.16 / 10 ^ 6 :=
    blockCosTelErr_le_numeral (by simp only [Nat.cast_zero, zero_add]; exact_mod_cast hk)
      le_rfl (by positivity)
  have hint : ∫ u in Real.exp (((0 : ℕ) : ℝ) + k)..Real.exp ((n : ℝ) + k),
        Real.cos (0 * u) * Real.exp (-(2 * σ) * u) / u
      = ∫ u in Real.exp (k : ℝ)..Real.exp ((n : ℝ) + k), Real.exp (-(2 * σ) * u) / u := by
    simp only [zero_mul, Real.cos_zero, one_mul, Nat.cast_zero, zero_add]
  rw [hint] at htel
  have hI := le_integral_exp_mul_div hσ (Real.exp_pos _) ha hℓ
  have hsum : Real.log (1 / (2 * σ * Real.exp (k : ℝ))) - 0.5917
      ≤ rangeCosSum (scaleCut (k : ℝ)) y σ 0 - rangeSqSum (scaleCut (k : ℝ)) y σ := by
    have := (abs_le.1 htel).1
    linarith
  have hlog : Real.log (1 / (2 * σ * Real.exp (k : ℝ))) - 0.5917
      = Real.log (Real.exp (-0.5917) / (2 * σ * Real.exp (k : ℝ))) := by
    rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  rw [hlog] at hsum
  have hmain := le_trans (Real.exp_le_exp.2 hsum) hprod
  rw [Real.exp_log (by positivity)] at hmain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * σ)]
  have hE : 0 < Real.exp (k : ℝ) := Real.exp_pos _
  calc Real.exp (-0.5917) = Real.exp (-0.5917) / (2 * σ * Real.exp (k : ℝ))
        * (2 * σ * Real.exp (k : ℝ)) := by field_simp
    _ ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * (2 * σ * Real.exp (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = _ := by ring

/-- **The rounding absorbs the kernel's loss**: `e^{-0.592} ≤ (1 - 10⁻⁶)e^{-0.5917}`, as
`e^{-0.0003} ≤ 1/1.0003 ≤ 1 - 10⁻⁶`. -/
lemma exp_neg_592_le_mul_exp_neg_5917 :
    Real.exp (-0.592) ≤ (1 - 1 / 10 ^ 6) * Real.exp (-0.5917) := by
  have h1 : Real.exp (-0.592) = Real.exp (-0.0003) * Real.exp (-0.5917) := by
    rw [← Real.exp_add]
    norm_num
  have h2 : Real.exp (-0.0003) ≤ 1 - 1 / 10 ^ 6 := by
    have h3 := Real.add_one_le_exp (0.0003 : ℝ)
    have h4 : Real.exp (-0.0003) * Real.exp 0.0003 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h5 : 0 < Real.exp (-0.0003) := Real.exp_pos _
    nlinarith
  rw [h1]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-! ### The main term -/

/-- **The main term against the extended line integral, `E‖F_high‖²e^k` explicit**: under the
hypotheses of `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_numeral` and `16 ≤ σ log y`,
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀)·N_q(k)·(T - k)^{-q/2} ≤ L^{-q}E[J_Y(σ)^q]`,
`G = e^{-0.592}/2`, the weighted sum's left side verbatim: the kernel's `(1 - 10⁻⁶)^q` is paid by
`RMF.le_integral_normSq_high_mul_exp_sharp` and `RMF.exp_neg_592_le_mul_exp_neg_5917`. -/
theorem le_rpow_mul_integral_rpow_lineDivSq_numeral (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 2000 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) (hσy : 16 ≤ σ * Real.log y) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  have hmain := le_integral_rpow_lineDivSq_numeral hX hσ hq0 hq1 hk₀ hσT hσT' hyT hK hKq hσy
  have hV : 0 < V := by rw [← hσV]; positivity
  set G : ℝ := Real.exp (-0.592) / 2 with hG
  have hG0 : 0 < G := by positivity
  have hLq : 0 < L ^ (-q) := Real.rpow_pos_of_pos hL _
  have hc0 : (0 : ℝ) < 1 - 1 / 10 ^ 6 := by norm_num
  have hG2 : G / σ ≤ (1 - 1 / 10 ^ 6) * (Real.exp (-0.5917) / (2 * σ)) := by
    have e1 : G / σ = Real.exp (-0.592) / (2 * σ) := by rw [hG]; field_simp
    have e2 : (1 - 1 / 10 ^ 6) * (Real.exp (-0.5917) / (2 * σ))
        = (1 - 1 / 10 ^ 6) * Real.exp (-0.5917) / (2 * σ) := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right exp_neg_592_le_mul_exp_neg_5917 (by positivity)
  -- per scale: `(G/σ)^q r^{-q/2} ≤ (1 - 10⁻⁶)^q(E‖F_high‖²e^k/√r)^q`
  have hper : ∀ k ∈ K, (G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ (1 - 1 / 10 ^ 6) ^ q
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    intro k hk
    obtain ⟨-, -, -, h4, h5, h6, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
    have hk20 : 20 ≤ k := by have := (hK k hk).1; omega
    have hE := le_integral_normSq_high_mul_exp_sharp hX hσ hk20 h4 h5 h6
    have hr0 : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have := (hK k hk).2
      exact_mod_cast (by omega : 0 < T - k)
    have hsq : 0 < √((T - k : ℕ) : ℝ) := Real.sqrt_pos.2 hr0
    have hB0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ) :=
      div_nonneg (mul_nonneg (integral_nonneg fun ω => sq_nonneg _) (Real.exp_pos _).le) hsq.le
    have hmono : G / σ / √((T - k : ℕ) : ℝ)
        ≤ (1 - 1 / 10 ^ 6)
          * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hG2.trans (mul_le_mul_of_nonneg_left hE hc0.le)) hsq.le
    have hrpow := Real.rpow_le_rpow (by positivity) hmono hq0.le
    rw [Real.mul_rpow hc0.le hB0] at hrpow
    refine le_trans (le_of_eq ?_) hrpow
    rw [Real.div_rpow (by positivity) hsq.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le,
      Real.rpow_neg hr0.le, div_eq_mul_inv]
    congr 2
    ring_nf
  have hN0 : ∀ k ∈ K, 0 ≤ perScaleConst q (k - k₀)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ) := by
    intro k hk
    have hc3 := c3FloorK_pos hq0.le (by linarith) (k - k₀)
    refine mul_nonneg ?_ (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    unfold perScaleConst
    have : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
    positivity
  have hsum : (G / σ) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    calc (G / σ) ^ q * (perScaleConst q (k - k₀)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
        = perScaleConst q (k - k₀)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by ring
      _ ≤ perScaleConst q (k - k₀)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((1 - 1 / 10 ^ 6) ^ q
              * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
              / √((T - k : ℕ) : ℝ)) ^ q) :=
          mul_le_mul_of_nonneg_left (hper k hk) (hN0 k hk)
      _ = _ := by ring
  have hGV : L ^ (-q) * (G / σ) ^ q = (G / V) ^ q := by
    rw [← hσV, Real.rpow_neg hL.le, ← Real.inv_rpow hL.le,
      ← Real.mul_rpow (inv_nonneg.2 hL.le) (by positivity)]
    congr 1
    field_simp
  have h2 : (0 : ℝ) < 2 ^ (2 * q - 1) := by positivity
  calc 2 ^ (2 * q - 1) * (G / V) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      = L ^ (-q) * (2 ^ (2 * q - 1) * ((G / σ) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))) := by
        rw [← hGV]; ring
    _ ≤ L ^ (-q) * (2 ^ (2 * q - 1) * ((1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum h2.le) hLq.le
    _ = L ^ (-q) * (2 ^ (2 * q - 1) * (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain hLq.le

/-- **The main term for the extended sum, fully explicit, `0 < q ≤ ½`**: under the
hypotheses of
`RMF.le_rpow_mul_integral_rpow_integral_lineDiv_explicit` and `16 ≤ σ log y`, its left side
verbatim against `L^{-q}E[J_Y(σ)^q]`:
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀)e^{-q(1-2q)(k + 0.7866 + 9.003e^{-k})}(T - k)^{-q/2}
  ≤ L^{-q}E[(∫_ℝ lineDivSq (½ + σ) X y ω t dt)^q]`, `G = e^{-0.592}/2`. -/
theorem le_rpow_mul_integral_rpow_lineDivSq_explicit (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 2000 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) (hσy : 16 ≤ σ * Real.log y) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  refine le_trans ?_ (le_rpow_mul_integral_rpow_lineDivSq_numeral hX hσ hq0
    (by linarith) hk₀ hσT hσT' hyT hK hKq hL hσV hσy)
  have hV : 0 < V := by rw [← hσV]; positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by positivity)
  have hc3 := c3FloorK_pos hq0.le (by linarith) (k - k₀)
  have hΓ : 0 ≤ perScaleConst q (k - k₀) := by
    unfold perScaleConst
    have : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
    positivity
  have hN := le_integral_rpow_norm_low (X := X) (μ := μ) hX hσ.le hq0.le hq1 k
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hΓ) ?_
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-! ### The main term on short tubes -/

/-- **The sum over scales on short tubes against the extended line integral**: under the
hypotheses of `RMF.le_integral_rpow_integral_lineDiv_short` and `16 ≤ σ log y`,
`2^{2q-1}(1 - 10⁻⁶)^q∑_{k ∈ K} Γ(q, k - k₀, T - k)·N_q(k)·(E‖F_{[c_k,y)}(s_σ)‖²e^k/√(T - k))^q
  ≤ E[J_Y(σ)^q]`, `Γ = RMF.perScaleConstShort`. -/
theorem le_integral_rpow_lineDivSq_short (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 35 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    (hσy : 16 ≤ σ * Real.log y) :
    2 ^ (2 * q - 1) * (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q
      ≤ ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  refine le_integral_rpow_lineDivSq_head_symm hX hσ hq0.le (by linarith) (k₀ := k₀)
    (r := fun k => T - k) (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.2.2.2.2)
    (fun k hk => (hK k hk).1.le) (fun k₁ _ k₂ hk₂ _ => by have := hkT k₂ hk₂; omega)
    (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.1) (fun k hk => ?_) hσy
    (fun k hk => by have := (hK k hk).1; omega)
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
  exact le_integral_indicator_rpow_headWindowMass_short hX hσ.le hq0 hq1 hk₀ (hK k hk).1
    (hKq k hk) h1 h2 h3 (by have := (hK k hk).2; omega)

/-- **The main term on short tubes against the extended line integral, `E‖F_high‖²e^k`
explicit**: under the hypotheses of `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_short` and
`16 ≤ σ log y`, its left side verbatim against `L^{-q}E[J_Y(σ)^q]`, `G = e^{-0.592}/2`,
`Γ = RMF.perScaleConstShort`. -/
theorem le_rpow_mul_integral_rpow_lineDivSq_short (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 35 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) (hσy : 16 ≤ σ * Real.log y) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  have hmain := le_integral_rpow_lineDivSq_short hX hσ hq0 hq1 hk₀ hσT hσT' hyT hK hKq hσy
  have hV : 0 < V := by rw [← hσV]; positivity
  set G : ℝ := Real.exp (-0.592) / 2 with hG
  have hG0 : 0 < G := by positivity
  have hLq : 0 < L ^ (-q) := Real.rpow_pos_of_pos hL _
  have hc0 : (0 : ℝ) < 1 - 1 / 10 ^ 6 := by norm_num
  have hG2 : G / σ ≤ (1 - 1 / 10 ^ 6) * (Real.exp (-0.5917) / (2 * σ)) := by
    have e1 : G / σ = Real.exp (-0.592) / (2 * σ) := by rw [hG]; field_simp
    have e2 : (1 - 1 / 10 ^ 6) * (Real.exp (-0.5917) / (2 * σ))
        = (1 - 1 / 10 ^ 6) * Real.exp (-0.5917) / (2 * σ) := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right exp_neg_592_le_mul_exp_neg_5917 (by positivity)
  -- per scale: `(G/σ)^q r^{-q/2} ≤ (1 - 10⁻⁶)^q(E‖F_high‖²e^k/√r)^q`
  have hper : ∀ k ∈ K, (G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ (1 - 1 / 10 ^ 6) ^ q
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    intro k hk
    obtain ⟨-, -, -, h4, h5, h6, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
    have hk20 : 20 ≤ k := by have := (hK k hk).1; omega
    have hE := le_integral_normSq_high_mul_exp_sharp hX hσ hk20 h4 h5 h6
    have hr0 : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have := (hK k hk).2
      exact_mod_cast (by omega : 0 < T - k)
    have hsq : 0 < √((T - k : ℕ) : ℝ) := Real.sqrt_pos.2 hr0
    have hB0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ) :=
      div_nonneg (mul_nonneg (integral_nonneg fun ω => sq_nonneg _) (Real.exp_pos _).le) hsq.le
    have hmono : G / σ / √((T - k : ℕ) : ℝ)
        ≤ (1 - 1 / 10 ^ 6)
          * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hG2.trans (mul_le_mul_of_nonneg_left hE hc0.le)) hsq.le
    have hrpow := Real.rpow_le_rpow (by positivity) hmono hq0.le
    rw [Real.mul_rpow hc0.le hB0] at hrpow
    refine le_trans (le_of_eq ?_) hrpow
    rw [Real.div_rpow (by positivity) hsq.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le,
      Real.rpow_neg hr0.le, div_eq_mul_inv]
    congr 2
    ring_nf
  have hN0 : ∀ k ∈ K, 0 ≤ perScaleConstShort q (k - k₀) (T - k)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ) := fun k _ =>
    mul_nonneg (perScaleConstShort_nonneg hq0.le (by linarith) _ _)
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
  have hsum : (G / σ) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ (1 - 1 / 10 ^ 6) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    calc (G / σ) ^ q * (perScaleConstShort q (k - k₀) (T - k)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
        = perScaleConstShort q (k - k₀) (T - k)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by ring
      _ ≤ perScaleConstShort q (k - k₀) (T - k)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((1 - 1 / 10 ^ 6) ^ q
              * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
              / √((T - k : ℕ) : ℝ)) ^ q) :=
          mul_le_mul_of_nonneg_left (hper k hk) (hN0 k hk)
      _ = _ := by ring
  have hGV : L ^ (-q) * (G / σ) ^ q = (G / V) ^ q := by
    rw [← hσV, Real.rpow_neg hL.le, ← Real.inv_rpow hL.le,
      ← Real.mul_rpow (inv_nonneg.2 hL.le) (by positivity)]
    congr 1
    field_simp
  have h2 : (0 : ℝ) < 2 ^ (2 * q - 1) := by positivity
  calc 2 ^ (2 * q - 1) * (G / V) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      = L ^ (-q) * (2 ^ (2 * q - 1) * ((G / σ) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))) := by
        rw [← hGV]; ring
    _ ≤ L ^ (-q) * (2 ^ (2 * q - 1) * ((1 - 1 / 10 ^ 6) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum h2.le) hLq.le
    _ = L ^ (-q) * (2 ^ (2 * q - 1) * (1 - 1 / 10 ^ 6) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain hLq.le

/-- **The main term for the extended sum on short tubes, fully explicit, `0 < q ≤ ½`**: under
the hypotheses of `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_explicit_short` and
`16 ≤ σ log y`, its left side verbatim against `L^{-q}E[J_Y(σ)^q]`:
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀, T - k)e^{-q(1-2q)(k + 0.7866 + 9.003e^{-k})}(T - k)^{-q/2}
  ≤ L^{-q}E[(∫_ℝ lineDivSq (½ + σ) X y ω t dt)^q]`, `G = e^{-0.592}/2`,
`Γ = RMF.perScaleConstShort`. -/
theorem le_rpow_mul_integral_rpow_lineDivSq_explicit_short
    (hX : IsRademacherPrimeValues X μ) {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    {T k₀ y : ℕ} {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 35 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) (hσy : 16 ≤ σ * Real.log y) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, lineDivSq (1 / 2 + σ) X y ω u) ^ q ∂μ := by
  refine le_trans ?_ (le_rpow_mul_integral_rpow_lineDivSq_short hX hσ hq0
    (by linarith) hk₀ hσT hσT' hyT hK hKq hL hσV hσy)
  have hV : 0 < V := by rw [← hσV]; positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by positivity)
  have hΓ := perScaleConstShort_nonneg hq0.le (by linarith) (k - k₀) (T - k)
  have hN := le_integral_rpow_norm_low (X := X) (μ := μ) hX hσ.le hq0.le hq1 k
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hΓ) ?_
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end RMF
