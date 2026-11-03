/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BlockSplitExplicit
import RMF.Weighted.TwoPointAboveHalfExplicit

/-!
# The block split with a weight in the height, for `q ≤ 1`

The split of `Weighted/BlockSplitExplicit.lean` at every `0 ≤ q ≤ 1`,

`E[(∫ρ‖F_{[y₀,y)}‖²)^q] ≤ E‖F_{[y₀,z)}(½+σ)‖^{2q}·E[(∫ρ'‖F_{[z,y)}‖²)^q]`

whenever `ρ(t)e^{βt²} ≤ ρ'(t)` on the window and `β ≥ 2(1-q)S₂(z)`
(`RMF.integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one`).  The proofs are
those for `q ≤ ½`, with the two-point ratio at every `q ≤ 1`
(`RMF.integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
-- the product-space bookkeeping of the mixed bound, with two weights
/-- **The weighted mixed bound, sharp.**  With `P` the product over `[y₀, z)`, `G` over `[z, y)`,
`S = ∫ρ'‖G‖²` and `W = ∫ρ‖P G‖²` on `[a, b]`: `E[(‖P(½+σ)‖²S)^{q-1}W] ≤ E‖P(½+σ)‖^{2q}·E[S^q]`
whenever `ρ(t)e^{βt²} ≤ ρ'(t)` on `[a,b]` and `β ≥ 2(1-q)S₂(z)`.  Fubini, the two-point ratio at
each height (`RMF.integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one`) absorbed into
`ρ'`, and Fubini back. -/
lemma integral_mixed_split_weight_primesIco_le_sharp_of_le_one {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y₀ z y : ℕ} (hy₀z : y₀ ≤ z) (hzy : z ≤ y)
    {σ a b q β Bd Bd' : ℝ} {ρ ρ' : ℝ → ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hβ : 2 * (1 - q) * (Real.log z ^ 2 / 2 + 15.003 * Real.log z + 34) ≤ β)
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd)
    (hρm' : Measurable ρ') (hρ0' : ∀ t, 0 ≤ ρ' t) (hρb' : ∀ t, ρ' t ≤ Bd')
    (hρρ' : ∀ t ∈ Set.Icc a b, ρ t * Real.exp (β * t ^ 2) ≤ ρ' t)
    (hρpos' : 0 < ∫ t in Set.Icc a b, ρ' t) :
    (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b, ρ' t *
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
          * (∫ t in Set.Icc a b, ρ t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
                (shiftLine σ t) ω‖ ^ 2) ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, (∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hvolfin : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hvolfin⟩
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have henvP := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ z hc0
  have hSbd := ae_setIntegral_weight_normSq_primesIco_mem_Icc hX z y (a := a) (b := b) hσ hρm'
    hρ0' hρb'
  have hVpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hVQpos : (0 : ℝ) < ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hsliceQ := integrable_uncurry_weight_normSq_primesIco hX z y hσ hvolfin hρm' hρ0' hρb'
  -- the truncation constants
  set VP : ℝ := (∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 with hVP
  set SM : ℝ := (∫ t in Set.Icc a b, ρ' t)
    * (∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 with hSM
  have hVPpos : (0 : ℝ) < VP := by rw [hVP]; exact pow_pos hVpos 2
  have hSMpos : (0 : ℝ) < SM := by rw [hSM]; exact mul_pos hρpos' (pow_pos hVQpos 2)
  have hcontmax : ∀ C : ℝ, 0 < C → Continuous fun x : ℝ => (max x C) ^ (q - 1) := fun C hC =>
    (continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_of_lt_of_le hC (le_max_right x C)).ne'
  -- the upper window is nonnegative, so every factor is
  have hSnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc a b, ρ' t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ t) ω‖ ^ 2 := fun ω =>
    integral_nonneg fun t => mul_nonneg (hρ0' t) (sq_nonneg _)
  have hB0 : ∀ (ω : Ω) (t : ℝ), (0 : ℝ) ≤ (∫ u in Set.Icc a b, ρ' u *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ t) ω‖ ^ 2 := fun ω t =>
    mul_nonneg (Real.rpow_nonneg (hSnn ω) _) (sq_nonneg _)
  have hA0 : ∀ (ω : Ω) (t : ℝ), (0 : ℝ) ≤ (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ t) ω‖ ^ 2 := fun ω t =>
    mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) (sq_nonneg _)
  -- measurability of the factors on the product space
  have hSaesm : AEStronglyMeasurable (fun ω => ∫ t in Set.Icc a b, ρ' t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ t) ω‖ ^ 2) μ := hsliceQ.integral_prod_left.1
  have hmP : AEStronglyMeasurable (fun w : Ω × ℝ =>
      (max (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ 0) w.1‖ ^ 2) VP) ^ (q - 1)) (μ.prod (volume.restrict (Set.Icc a b))) :=
    (((hcontmax VP hVPpos).comp_aestronglyMeasurable
      ((measurable_norm_randomEulerProductIco_sqfree hX y₀ z
        (shiftLine σ 0)).pow_const 2).aestronglyMeasurable)).comp_fst
  have hmS : AEStronglyMeasurable (fun w : Ω × ℝ =>
      (max (∫ t in Set.Icc a b, ρ' t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) w.1‖ ^ 2) SM) ^ (q - 1))
      (μ.prod (volume.restrict (Set.Icc a b))) :=
    ((hcontmax SM hSMpos).comp_aestronglyMeasurable hSaesm).comp_fst
  have hmPt : AEStronglyMeasurable (fun w : Ω × ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ w.2) w.1‖ ^ 2) (μ.prod (volume.restrict (Set.Icc a b))) := by
    have h2 := (measurable_uncurry_primePoly hX (primesIco y₀ z)
      (fun p hp => prime_of_mem_primesIco hp) σ).norm.pow_const 2
    simp only [primePoly_primesIco] at h2
    exact h2.aestronglyMeasurable
  have hmQt : AEStronglyMeasurable (fun w : Ω × ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ w.2) w.1‖ ^ 2) (μ.prod (volume.restrict (Set.Icc a b))) := by
    have h2 := (measurable_uncurry_primePoly hX (primesIco z y)
      (fun p hp => prime_of_mem_primesIco hp) σ).norm.pow_const 2
    simp only [primePoly_primesIco] at h2
    exact h2.aestronglyMeasurable
  have hmρ : AEStronglyMeasurable (fun w : Ω × ℝ => ρ w.2)
      (μ.prod (volume.restrict (Set.Icc a b))) :=
    (hρm.comp measurable_snd).aestronglyMeasurable
  have hmρ' : AEStronglyMeasurable (fun w : Ω × ℝ => ρ' w.2)
      (μ.prod (volume.restrict (Set.Icc a b))) :=
    (hρm'.comp measurable_snd).aestronglyMeasurable
  -- the truncations are invisible almost surely, on the product
  have haeP : ∀ᵐ w ∂(μ.prod (volume.restrict (Set.Icc a b))),
      (max (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
          (shiftLine σ 0) w.1‖ ^ 2) VP)
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
          (shiftLine σ 0) w.1‖ ^ 2 := by
    have h0 : ∀ᵐ ω ∂μ, (max (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2) VP)
          = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2 := by
      filter_upwards [henvP] with ω hω
      have hle : VP ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
          (shiftLine σ 0) ω‖ ^ 2 := by
        rw [hVP]
        exact pow_le_pow_left₀ hVpos.le (hω (shiftLine σ 0) (re_shiftLine σ 0)).1 2
      exact max_eq_left hle
    exact Measure.quasiMeasurePreserving_fst.ae h0
  have haeS : ∀ᵐ w ∂(μ.prod (volume.restrict (Set.Icc a b))),
      (max (∫ t in Set.Icc a b, ρ' t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) w.1‖ ^ 2) SM)
        = ∫ t in Set.Icc a b, ρ' t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) w.1‖ ^ 2 := by
    have h0 : ∀ᵐ ω ∂μ, (max (∫ t in Set.Icc a b, ρ' t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) ω‖ ^ 2) SM)
          = ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2 := by
      filter_upwards [hSbd] with ω hω
      exact max_eq_left hω.1
    exact Measure.quasiMeasurePreserving_fst.ae h0
  have hGm : AEStronglyMeasurable (fun w : Ω × ℝ => ρ w.2 *
      (((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) w.1‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ w.2) w.1‖ ^ 2)
        * ((∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) w.1‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ w.2) w.1‖ ^ 2))) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (hmρ.mul ((hmP.mul hmPt).mul (hmS.mul hmQt))).congr ?_
    filter_upwards [haeP, haeS] with w h1 h2
    simp only [Pi.mul_apply]
    rw [h1, h2]
  have hHm : AEStronglyMeasurable (fun w : Ω × ℝ => ρ' w.2 *
      ((∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) w.1‖ ^ 2) ^ (q - 1)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ w.2) w.1‖ ^ 2)) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (hmρ'.mul (hmS.mul hmQt)).congr ?_
    filter_upwards [haeS] with w h2
    simp only [Pi.mul_apply]
    rw [h2]
  -- the a.e. bounds on the product space
  have haeb : ∀ᵐ w ∂(μ.prod (volume.restrict (Set.Icc a b))),
      ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) w.1‖ ^ 2) ^ (q - 1)
          ≤ VP ^ (q - 1))
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ w.2) w.1‖ ^ 2
          ≤ (∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
        ∧ ((∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) w.1‖ ^ 2) ^ (q - 1) ≤ SM ^ (q - 1))
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ w.2) w.1‖ ^ 2
          ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    have h0 : ∀ᵐ ω ∂μ, ∀ t : ℝ,
        ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1) ≤ VP ^ (q - 1))
          ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ t) ω‖ ^ 2
            ≤ (∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
          ∧ ((∫ t in Set.Icc a b, ρ' t *
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ (q - 1) ≤ SM ^ (q - 1))
          ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2
            ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
      filter_upwards [henvP, hSbd,
        ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX z y hc0] with ω hω hS hωQ
      intro t
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hle : VP ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2 := by
          rw [hVP]
          exact pow_le_pow_left₀ hVpos.le (hω (shiftLine σ 0) (re_shiftLine σ 0)).1 2
        exact Real.rpow_le_rpow_of_nonpos hVPpos hle (by linarith)
      · exact pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ t) (re_shiftLine σ t)).2 2
      · exact Real.rpow_le_rpow_of_nonpos hSMpos hS.1 (by linarith)
      · exact pow_le_pow_left₀ (norm_nonneg _) (hωQ (shiftLine σ t) (re_shiftLine σ t)).2 2
    exact (Measure.quasiMeasurePreserving_fst.ae h0).mono fun w hw => hw w.2
  have hGint : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => ρ t *
      (((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ t) ω‖ ^ 2)
        * ((∫ u in Set.Icc a b, ρ' u *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) ω‖ ^ 2))) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (memLp_top_of_bound hGm
      (Bd * ((VP ^ (q - 1) * (∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
        * (SM ^ (q - 1) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)))
      ?_).integrable le_top
    filter_upwards [haeb] with w hw
    have hAB : (0 : ℝ) ≤ _ := mul_nonneg (hA0 w.1 w.2) (hB0 w.1 w.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 _) hAB)]
    exact mul_le_mul (hρb _)
      (mul_le_mul (mul_le_mul hw.1 hw.2.1 (sq_nonneg _) (Real.rpow_nonneg hVPpos.le _))
        (mul_le_mul hw.2.2.1 hw.2.2.2 (sq_nonneg _) (Real.rpow_nonneg hSMpos.le _))
        (hB0 w.1 w.2) (by positivity))
      hAB (le_trans (hρ0 w.2) (hρb w.2))
  have hHint : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => ρ' t *
      ((∫ u in Set.Icc a b, ρ' u *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) ω‖ ^ 2)) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (memLp_top_of_bound hHm
      (Bd' * (SM ^ (q - 1) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2))
      ?_).integrable le_top
    filter_upwards [haeb] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0' _) (hB0 w.1 w.2))]
    exact mul_le_mul (hρb' _)
      (mul_le_mul hw.2.2.1 hw.2.2.2 (sq_nonneg _) (Real.rpow_nonneg hSMpos.le _))
      (hB0 w.1 w.2) (le_trans (hρ0' w.2) (hρb' w.2))
  -- the pointwise identity
  have hA : ∀ᵐ ω ∂μ,
      (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc a b, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
              (shiftLine σ t) ω‖ ^ 2)
      = ∫ t in Set.Icc a b, ρ t *
          (((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2)) := by
    filter_upwards with ω
    rw [Real.mul_rpow (sq_nonneg _) (hSnn ω), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [normSq_randomEulerProductIco_split hy₀z hzy]
    ring
  -- the two-point bound at each height
  set C₀ : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
    (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ with hC₀
  have hC₀0 : 0 ≤ C₀ := integral_nonneg fun ω => by positivity
  have hlow : ∀ t : ℝ,
      (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ t) ω‖ ^ 2 ∂μ)
        ≤ Real.exp (β * t ^ 2) * C₀ := by
    intro t
    have hmix := integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one hX y₀ z hσ hq0 hq t
    have hone : ∀ v : ℂ, ‖v‖ ^ (2 * (1 : ℝ)) = ‖v‖ ^ 2 := fun v => by
      rw [norm_rpow_two_mul v 1, Real.rpow_one]
    have htwo : ∀ v : ℂ, ‖v‖ ^ (2 * (q - 1)) = (‖v‖ ^ 2) ^ (q - 1) := fun v =>
      norm_rpow_two_mul v (q - 1)
    simp only [hone, htwo] at hmix
    refine le_trans hmix (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hC₀0)
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have h := mul_le_mul_of_nonneg_left hβ ht2
    calc 2 * (1 - q) * t ^ 2 * (Real.log z ^ 2 / 2 + 15.003 * Real.log z + 34)
        = t ^ 2 * (2 * (1 - q) * (Real.log z ^ 2 / 2 + 15.003 * Real.log z + 34)) := by ring
      _ ≤ t ^ 2 * β := h
      _ = β * t ^ 2 := by ring
  -- assemble
  have hstep : ∀ t ∈ Set.Icc a b,
      (∫ ω, ρ t *
          (((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2)) ∂μ)
        ≤ C₀ * ∫ ω, ρ' t *
            ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ∂μ := by
    intro t ht
    rw [integral_const_mul, integral_const_mul,
      integral_mixed_window_weight_split_primesIco hX y₀ z y hσ hρm' hρ0' hρb' hρpos']
    have hB : (0 : ℝ) ≤ ∫ ω, (∫ u in Set.Icc a b, ρ' u *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) ω‖ ^ 2 ∂μ := integral_nonneg fun ω => hB0 ω t
    have h1 := mul_le_mul_of_nonneg_right (hlow t) hB
    have h2 := mul_le_mul_of_nonneg_left h1 (hρ0 t)
    have h3 : ρ t * Real.exp (β * t ^ 2) * C₀ ≤ ρ' t * C₀ :=
      mul_le_mul_of_nonneg_right (hρρ' t ht) hC₀0
    have h4 := mul_le_mul_of_nonneg_right h3 hB
    calc _ ≤ ρ t * (Real.exp (β * t ^ 2) * C₀ * _) := h2
      _ = ρ t * Real.exp (β * t ^ 2) * C₀ * _ := by ring
      _ ≤ ρ' t * C₀ * _ := h4
      _ = _ := by ring
  calc (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc a b, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
      = ∫ ω, (∫ t in Set.Icc a b, ρ t *
          (((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2))) ∂μ := integral_congr_ae hA
    _ = ∫ t in Set.Icc a b, ∫ ω, ρ t *
          (((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2)) ∂μ := integral_integral_swap hGint
    _ ≤ ∫ t in Set.Icc a b, C₀ * ∫ ω, ρ' t *
            ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ∂μ :=
        setIntegral_mono_on hGint.integral_prod_right
          (hHint.integral_prod_right.const_mul _) measurableSet_Icc hstep
    _ = C₀ * ∫ t in Set.Icc a b, ∫ ω, ρ' t *
            ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ∂μ := integral_const_mul _ _
    _ = C₀ * ∫ ω, (∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
        congr 1
        rw [← integral_integral_swap hHint]
        refine integral_congr_ae ?_
        filter_upwards [hSbd] with ω hS
        have hSpos : (0 : ℝ) < ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2 := lt_of_lt_of_le hSMpos hS.1
        have hre : (∫ t in Set.Icc a b, ρ' t *
            ((∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2))
            = (∫ u in Set.Icc a b, ρ' u *
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ∫ t in Set.Icc a b, ρ' t *
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2 := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only
          ring
        rw [hre]
        nth_rewrite 2 [← Real.rpow_one (∫ t in Set.Icc a b, ρ' t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) ω‖ ^ 2)]
        rw [← Real.rpow_add hSpos]
        norm_num

/-! ### The split -/

/-- **The block split with a weight, sharp.**  For `0 ≤ q ≤ 1`, `y₀ ≤ z ≤ y`, `σ ≥ 0`,
bounded measurable weights `ρ, ρ' ≥ 0` with `0 < ∫_{[a,b]}ρ` and `ρ(t)e^{βt²} ≤ ρ'(t)` on
`[a,b]`, `β ≥ 2(1-q)((log z)²/2 + 15.003 log z + 34)`:

`E[(∫_{[a,b]}ρ‖F_{[y₀,y)}(½+σ+it)‖²dt)^q]
  ≤ E‖F_{[y₀,z)}(½+σ)‖^{2q}·E[(∫_{[a,b]}ρ'‖F_{[z,y)}(½+σ+it)‖²dt)^q]`.

`RMF.integral_rpow_setIntegral_normSq_split_primesIco_le` with the two-point ratio kept at each
height and absorbed into `ρ'`: the balanced Hölder `RMF.integral_rpow_le_of_mixed_le` at
`κ = 1`. -/
theorem integral_rpow_setIntegral_weight_split_primesIco_le_sharp_of_le_one {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y₀ z y : ℕ} (hy₀z : y₀ ≤ z)
    (hzy : z ≤ y) {σ a b q β Bd Bd' : ℝ} {ρ ρ' : ℝ → ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q)
    (hq : q ≤ 1)
    (hβ : 2 * (1 - q) * (Real.log z ^ 2 / 2 + 15.003 * Real.log z + 34) ≤ β)
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρb : ∀ t, ρ t ≤ Bd)
    (hρm' : Measurable ρ') (hρ0' : ∀ t, 0 ≤ ρ' t) (hρb' : ∀ t, ρ' t ≤ Bd')
    (hρρ' : ∀ t ∈ Set.Icc a b, ρ t * Real.exp (β * t ^ 2) ≤ ρ' t)
    (hρpos : 0 < ∫ t in Set.Icc a b, ρ t) :
    (∫ ω, (∫ t in Set.Icc a b, ρ t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ∫ ω, (∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hvolfin : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hvolfin⟩
  have hq1 : q ≤ 1 := by linarith
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hβ0 : 0 ≤ β := by
    have h1 : (0 : ℝ) ≤ 1 - q := by linarith
    have h2 : (0 : ℝ) ≤ Real.log z ^ 2 / 2 + 15.003 * Real.log z + 34 := by
      rcases Nat.eq_zero_or_pos z with hz | hz
      · subst hz; norm_num
      · have : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
        positivity
    have : (0 : ℝ) ≤ 2 * (1 - q) * (Real.log z ^ 2 / 2 + 15.003 * Real.log z + 34) := by
      positivity
    linarith
  -- the upper weight has positive mass too
  have hρint : IntegrableOn ρ (Set.Icc a b) := by
    refine (memLp_top_of_bound hρm.aestronglyMeasurable Bd ?_).integrable le_top
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρb t
  have hρint' : IntegrableOn ρ' (Set.Icc a b) := by
    refine (memLp_top_of_bound hρm'.aestronglyMeasurable Bd' ?_).integrable le_top
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0' t)]
    exact hρb' t
  have hρpos' : 0 < ∫ t in Set.Icc a b, ρ' t := by
    refine lt_of_lt_of_le hρpos (setIntegral_mono_on hρint hρint' measurableSet_Icc ?_)
    intro t ht
    have h1 : (1 : ℝ) ≤ Real.exp (β * t ^ 2) := Real.one_le_exp (by positivity)
    have h2 : ρ t ≤ ρ t * Real.exp (β * t ^ 2) := le_mul_of_one_le_right (hρ0 t) h1
    exact le_trans h2 (hρρ' t ht)
  have henvP := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ z hc0
  have hSbd := ae_setIntegral_weight_normSq_primesIco_mem_Icc hX z y (a := a) (b := b) hσ hρm'
    hρ0' hρb'
  have hWbd := ae_setIntegral_weight_normSq_primesIco_mem_Icc hX y₀ y (a := a) (b := b) hσ hρm
    hρ0 hρb
  have hEPpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hEQpos : (0 : ℝ) < ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hEYpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hFPpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) :=
    Finset.prod_pos fun p _ => by positivity
  have hFQpos : (0 : ℝ) < ∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) :=
    Finset.prod_pos fun p _ => by positivity
  set EP : ℝ := ∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hEP
  set FP : ℝ := ∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hFP
  set EQ : ℝ := ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hEQ
  set FQ : ℝ := ∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hFQ
  set EY : ℝ := ∏ p ∈ primesIco y₀ y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hEY
  set FY : ℝ := ∏ p ∈ primesIco y₀ y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hFY
  set Mρ : ℝ := ∫ t in Set.Icc a b, ρ t with hMρ
  set Mρ' : ℝ := ∫ t in Set.Icc a b, ρ' t with hMρ'
  set NL : ℝ := EP ^ 2 * (Mρ' * EQ ^ 2) with hNL
  set NU : ℝ := FP ^ 2 * (Mρ' * FQ ^ 2) with hNU
  have hNLpos : (0 : ℝ) < NL := by
    rw [hNL]; exact mul_pos (pow_pos hEPpos 2) (mul_pos hρpos' (pow_pos hEQpos 2))
  have hNUpos : (0 : ℝ) < NU := by
    rw [hNU]; exact mul_pos (pow_pos hFPpos 2) (mul_pos hρpos' (pow_pos hFQpos 2))
  -- the combined envelope
  have hbnd : ∀ᵐ ω ∂μ,
      ((NL ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b, ρ' t *
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2)
          ∧ (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b, ρ' t *
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ≤ NU)
        ∧ (Mρ * EY ^ 2 ≤ ∫ t in Set.Icc a b, ρ t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
                (shiftLine σ t) ω‖ ^ 2)
          ∧ (∫ t in Set.Icc a b, ρ t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
                (shiftLine σ t) ω‖ ^ 2) ≤ Mρ * FY ^ 2 := by
    filter_upwards [henvP, hSbd, hWbd] with ω hω hS hW
    refine ⟨⟨?_, ?_⟩, hW.1, hW.2⟩
    · rw [hNL]
      exact mul_le_mul (pow_le_pow_left₀ hEPpos.le (hω (shiftLine σ 0) (re_shiftLine σ 0)).1 2)
        hS.1 (by positivity) (sq_nonneg _)
    · rw [hNU]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
        (hω (shiftLine σ 0) (re_shiftLine σ 0)).2 2) hS.2
        (le_trans (mul_nonneg hρpos'.le (sq_nonneg _)) hS.1) (sq_nonneg _)
  -- measurability of the three observables
  have hP0m : AEStronglyMeasurable (fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2) μ :=
    ((measurable_norm_randomEulerProductIco_sqfree hX y₀ z
      (shiftLine σ 0)).pow_const 2).aestronglyMeasurable
  have hSm : AEStronglyMeasurable (fun ω => ∫ t in Set.Icc a b, ρ' t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ t) ω‖ ^ 2) μ :=
    (integrable_uncurry_weight_normSq_primesIco hX z y hσ hvolfin hρm' hρ0'
      hρb').integral_prod_left.1
  have hWm : AEStronglyMeasurable (fun ω => ∫ t in Set.Icc a b, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2) μ :=
    (integrable_uncurry_weight_normSq_primesIco hX y₀ y hσ hvolfin hρm hρ0
      hρb).integral_prod_left.1
  have hcontmax : Continuous fun x : ℝ => (max x NL) ^ (q - 1) :=
    (continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_of_lt_of_le hNLpos (le_max_right x NL)).ne'
  have hWnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc a b, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2 := fun ω =>
    integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  have hNnn : ∀ᵐ ω ∂μ, (0 : ℝ) < ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2 :=
    hbnd.mono fun ω h => lt_of_lt_of_le hNLpos h.1.1
  -- the three integrabilities
  have hNi : Integrable (fun ω => (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable (hP0m.mul hSm))
      (NU ^ q) ?_).integrable le_top
    filter_upwards [hbnd] with ω h
    simp only [Pi.mul_apply]
    have h0 : (0 : ℝ) ≤ _ := le_of_lt (lt_of_lt_of_le hNLpos h.1.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    exact Real.rpow_le_rpow h0 h.1.2 hq0
  have hi : Integrable (fun ω => (∫ t in Set.Icc a b, ρ t *
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable hWm)
      ((Mρ * FY ^ 2) ^ q) ?_).integrable le_top
    filter_upwards [hbnd] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hWnn ω) _)]
    exact Real.rpow_le_rpow (hWnn ω) h.2.2 hq0
  have hABi : Integrable (fun ω => (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
      * ∫ t in Set.Icc a b, ρ t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2) μ := by
    have hm : AEStronglyMeasurable (fun ω => (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)) μ := by
      refine (hcontmax.comp_aestronglyMeasurable (hP0m.mul hSm)).congr ?_
      filter_upwards [hbnd] with ω h
      simp only [Pi.mul_apply]
      rw [max_eq_left h.1.1]
    refine (memLp_top_of_bound (hm.mul hWm) (NL ^ (q - 1) * (Mρ * FY ^ 2)) ?_).integrable
      le_top
    filter_upwards [hbnd] with ω h
    simp only [Pi.mul_apply]
    have h0 : (0 : ℝ) < _ := lt_of_lt_of_le hNLpos h.1.1
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg h0.le _) (hWnn ω))]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hNLpos h.1.1 (by linarith)) h.2.2
      (hWnn ω) (Real.rpow_nonneg hNLpos.le _)
  -- the two positivities
  have hα : (0 : ℝ) < ∫ ω, (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
    refine lt_of_lt_of_le (Real.rpow_pos_of_pos hNLpos q) ?_
    calc NL ^ q = ∫ _ω, NL ^ q ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hNi
          (hbnd.mono fun ω h => Real.rpow_le_rpow hNLpos.le h.1.1 hq0)
  have hβpos : (0 : ℝ) < ∫ ω, (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
      * (∫ t in Set.Icc a b, ρ t *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2) ∂μ := by
    have hEY2 : (0 : ℝ) < Mρ * EY ^ 2 := mul_pos hρpos (pow_pos hEYpos 2)
    refine lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hNUpos (q - 1)) hEY2) ?_
    calc NU ^ (q - 1) * (Mρ * EY ^ 2) = ∫ _ω, NU ^ (q - 1) * (Mρ * EY ^ 2) ∂μ := by simp
      _ ≤ _ := by
          refine integral_mono_ae (integrable_const _) hABi ?_
          filter_upwards [hbnd] with ω h
          exact mul_le_mul
            (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hNLpos h.1.1) h.1.2 (by linarith))
            h.2.1 hEY2.le (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hNLpos h.1.1)) _)
  -- `E[N^q]` factors
  have hfac : (∫ ω, (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ∫ ω, (∫ t in Set.Icc a b, ρ' t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
    rw [← integral_rpow_normSq_mul_window_weight_split_primesIco hX y₀ z y σ (Set.Icc a b)
      hρm' hq0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hS0 : (0 : ℝ) ≤ ∫ t in Set.Icc a b, ρ' t *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) ω‖ ^ 2 := integral_nonneg fun t => mul_nonneg (hρ0' t) (sq_nonneg _)
    simp only
    rw [Real.mul_rpow (sq_nonneg _) hS0, ← norm_rpow_two_mul]
  -- the balanced Hölder at `κ = 1`
  have hbd : (∫ ω, (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b, ρ' t *
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc a b, ρ t *
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
      ≤ 1 * ∫ ω, (‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b, ρ' t *
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
    rw [one_mul, hfac]
    exact integral_mixed_split_weight_primesIco_le_sharp_of_le_one hX hy₀z hzy hσ hq0 hq hβ hρm
      hρ0 hρb
      hρm' hρ0' hρb' hρρ' hρpos'
  have hkey := integral_rpow_le_of_mixed_le hq0 hq1 hNnn (.of_forall hWnn) hNi hABi hi hα
    hβpos zero_le_one hbd
  rwa [Real.one_rpow, one_mul, hfac] at hkey

end RMF
