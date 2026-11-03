/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BandTailDifference
import RMF.Weighted.ReductionSmallQExplicit
import RMF.Weighted.PropositionBAssembly

/-!
# The truncation bound with its constants, in difference form

The truncation bound with every constant explicit, for a band `(y, z]` and `0 < q ≤ 1`:

`E|𝒯_{y,z}(x)|^{2q} ≤ E|T(x)|^{2q} + (Kη/log z)^q E|F(½)|^{2q} + (Ke^{2c})^q E[Ψ^q] + E_err^q`

(`RMF.integral_rpow_norm_blockTruncationTail_le_explicit`), `F = F_{y,z}` and `Ψ` the line
functional in difference form (`RMF.bandDiffLine`).  Against `Weighted/LemmaT.lean`:

* **Plancherel on `[1, ∞)`** (`RMF.integral_normSq_blockTailSum_eq_line_sub`), not on `(0, ∞)` at
  the left shift `½ - c`.  The smoothing's range `w < 1` is the coherent `F(½)`, of `dw/w`-mass at
  most `η` (the second term), and no weight `w^{2c}` is paid: `E Ψ ≈ κ` at `q = 1`, against
  `∏(1 + p^{-1+2c}) ≈ e^{1.32}κ`.
* **Brun–Titchmarsh at a level `z' ≤ z` covers every rough `r > 1`**
  (`RMF.sum_inv_sq_indicator_le_smallQSieveConst` at roughness `z`): a `z`-rough `r > 1` exceeds
  `z`, so there is no Rankin range.
* **The smoothing split is `(1+ε, 1+1/ε)`** (`RMF.sum_blockTailTerm_le_setIntegral_eps`), with its
  error bounded by `RMF.integral_blockTailSmoothingError_le_explicit`.
* **The atom**: `E|T(w)|² ≤ w^{-1/log z}·exp(e∑_{y<p≤z}1/p)`
  (`RMF.integral_normSq_blockTailSum_le_exp_sum`).

`K = RMF.lemmaTConst z z' η ε → 2(1+ε)`, `E_err = RMF.smallQReductionErr x z' η ε`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The band's line functional in difference form**,
`Ψ = (2π log z)⁻¹∫_ℝ |F(½) - F(½+σ+it)|²/|σ+it|² dt`, `F = F_{y,z}` the product over `(y, z]`:
by Plancherel on `[1, ∞)` (`RMF.integral_normSq_blockTailSum_eq_line_sub`) it is
`(log z)⁻¹∫_1^∞ |T(w)|² w^{-1-2σ} dw`. -/
noncomputable def bandDiffLine {Ω : Type*} (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (σ : ℝ)
    (ω : Ω) : ℝ :=
  (2 * Real.pi * Real.log z)⁻¹ * ∫ t : ℝ,
    ‖(randomEulerProductIco f (y + 1) (z + 1) (1 / 2 : ℂ) ω
        - randomEulerProductIco f (y + 1) (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
      / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

/-- **The constant of the band's rough sum**, `(1+ε)·C_z·((1+η)²(η/(1+η) + 1/z)/η)`, with
`C_z = RMF.smallQSieveConst z z' η` the Brun–Titchmarsh count of `z`-rough integers at the level
`z' ≤ z`.  It tends to `2(1+ε)` as `η → 0` and `log z'/log z → 1`. -/
noncomputable def lemmaTConst (z z' : ℕ) (η ε : ℝ) : ℝ :=
  (1 + ε) * smallQSieveConst z z' η * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η)

lemma bandDiffLine_nonneg {Ω : Type*} (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (σ : ℝ)
    (ω : Ω) (hz : 1 ≤ z) : 0 ≤ bandDiffLine f y z σ ω := by
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
  exact mul_nonneg (inv_nonneg.2 (by positivity)) (integral_nonneg fun t => sq_nonneg _)

lemma lemmaTConst_pos {z z' : ℕ} (hz' : 2 ≤ z') (hz'z : z' ≤ z) {η ε : ℝ} (hη : 0 < η)
    (hε : 0 < ε) : 0 < lemmaTConst z z' η ε := by
  have hz0 : (0 : ℝ) < (z : ℝ) := by
    have : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans hz' hz'z
    linarith
  have hC := smallQSieveConst_pos hz' hz'z hη
  rw [lemmaTConst]
  have h1 : 0 < (1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η := by positivity
  positivity

omit [MeasurableSpace Ω] in
/-- **The band's principal term, in difference form.**  For `0 < z ≤ x`, `σ > 0` with
`σ log(x/z) ≤ c`, `η > 0`, `C, K ≥ 0` and the sieve shape `b(t) = C(1+η)²(tη/(1+η)+1)/(t² log z)`,
`(K/η)∫_{[z, x(1+η)]}|T(x/t)|²b(t)dt` is at most `K·C·((1+η)²(η/(1+η) + 1/z)/η)·(log z)⁻¹` times
`η|F(½)|² + e^{2c}(2π)⁻¹∫|F(½) - F(½+σ+it)|²/|σ+it|²dt`, `F = F_{y,z}`.

The merge and `t ↦ x/t` (`RMF.setIntegral_mul_sieveShape_le`) leave `∫|T(w)|²dw/w` over
`w ∈ (1/(1+η), x/z)`.  Below `1` the tail is `F(½)` (`RMF.blockTailSum_of_lt_one`), a range of
`dw/w`-mass at most `η`; above it `dw/w ≤ e^{2c}dw/w^{1+2σ}` and Plancherel on `[1, ∞)`
(`RMF.integral_normSq_blockTailSum_eq_line_sub`). -/
theorem setIntegral_normSq_blockTailSum_mul_sieve_le_sub {X : ℕ → Ω → ℂ} (y z : ℕ)
    {σ x η C K c : ℝ} (hz : (0 : ℝ) < z) (hzx : (z : ℝ) ≤ x) (hσ : 0 < σ)
    (hσlog : σ * Real.log (x / z) ≤ c) (hη : 0 < η) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hlogz : 0 < Real.log z) (ω : Ω) :
    (K / η) * (∫ t in Set.Icc ((z : ℝ)) (x * (1 + η)),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z)))
      ≤ K * C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ)) / η) * ((Real.log z)⁻¹
          * (η * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                (z + 1) (1 / 2 : ℂ) ω‖ ^ 2
            + Real.exp (2 * c) * ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
              ‖(randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                    (z + 1) (1 / 2 : ℂ) ω
                  - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                    (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))) := by
  have hpars := integral_normSq_blockTailSum_eq_line_sub (X := X) y z hσ ω
  have hIint := integrableOn_normSq_blockTailSum_div_rpow
    (fun ω => squarefreeExtension fun p => X p ω) y z hσ ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set F0 : ℂ := randomEulerProductIco f (y + 1) (z + 1) (1 / 2 : ℂ) ω with hF0
  set P : ℝ := ∫ t : ℝ, ‖(F0 - randomEulerProductIco f (y + 1) (z + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
    with hPdef
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hz hzx
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hb : (z : ℝ) ≤ x * (1 + η) :=
    le_trans hzx (le_mul_of_one_le_right hx0.le (by linarith))
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ w : ℝ, ‖blockTailSum f y z w ω‖ ≤ B :=
    ⟨_, fun w => norm_blockTailSum_le_sum f y z w ω⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hmeasw : Measurable fun w : ℝ => ‖blockTailSum f y z w ω‖ ^ 2 :=
    (measurable_blockTailSum_truncation f y z ω).norm.pow_const 2
  have hmeas : Measurable fun t : ℝ => ‖blockTailSum f y z (x / t) ω‖ ^ 2 :=
    ((measurable_blockTailSum_truncation f y z ω).comp
      (measurable_const.div measurable_id)).norm.pow_const 2
  have hint1 : IntegrableOn (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2 / t)
      (Set.Icc (z : ℝ) (x * (1 + η))) volume := by
    refine Measure.integrableOn_of_bounded (M := B ^ 2 / z)
      measure_Icc_lt_top.ne (hmeas.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hz ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ht0.le)]
    calc ‖blockTailSum f y z (x / t) ω‖ ^ 2 / t ≤ B ^ 2 / t := by
          gcongr
          exact hB (x / t)
      _ ≤ B ^ 2 / z := div_le_div_of_nonneg_left (sq_nonneg _) hz ht.1
  -- the merge and `t ↦ x/t`
  have hstep12 := setIntegral_mul_sieveShape_le (fun u => ‖blockTailSum f y z u ω‖ ^ 2) hx0 hz hb
    hη hC hlogz (fun _ => sq_nonneg _) hint1
  -- the `w`-integral: `F(½)` below `1`, Plancherel above
  have hlow : x / (x * (1 + η)) = (1 + η)⁻¹ := by field_simp
  have ha1 : (1 + η)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have ha0 : (0 : ℝ) < (1 + η)⁻¹ := inv_pos.2 h1η
  have h1b : (1 : ℝ) ≤ x / z := by rw [le_div_iff₀ hz]; linarith
  have hbnd : ∀ a : ℝ, 0 < a → ∀ s : Set ℝ, MeasurableSet s → (∀ w ∈ s, a ≤ w) →
      volume s ≠ ⊤ → IntegrableOn (fun w => ‖blockTailSum f y z w ω‖ ^ 2 / w) s volume := by
    intro a ha s hs has hsv
    refine Measure.integrableOn_of_bounded (M := B ^ 2 / a) hsv
      (hmeasw.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hs] with w hw
    have hw0 : 0 < w := lt_of_lt_of_le ha (has w hw)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hw0.le)]
    calc ‖blockTailSum f y z w ω‖ ^ 2 / w ≤ B ^ 2 / w := by
          gcongr
          exact hB w
      _ ≤ B ^ 2 / a := div_le_div_of_nonneg_left (sq_nonneg _) ha (has w hw)
  have hI1 : IntegrableOn (fun w => ‖blockTailSum f y z w ω‖ ^ 2 / w)
      (Set.Ioo (1 + η)⁻¹ 1) volume :=
    hbnd _ ha0 _ measurableSet_Ioo (fun w hw => hw.1.le) (by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hI2 : IntegrableOn (fun w => ‖blockTailSum f y z w ω‖ ^ 2 / w)
      (Set.Ico 1 (x / z)) volume :=
    hbnd _ one_pos _ measurableSet_Ico (fun w hw => hw.1) (by
      rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hpiece1 : (∫ w in Set.Ioo (1 + η)⁻¹ 1, ‖blockTailSum f y z w ω‖ ^ 2 / w)
      ≤ η * ‖F0‖ ^ 2 := by
    have hpt : ∀ w ∈ Set.Ioo (1 + η)⁻¹ 1,
        ‖blockTailSum f y z w ω‖ ^ 2 / w ≤ (1 + η) * ‖F0‖ ^ 2 := by
      intro w hw
      have hw0 : 0 < w := lt_trans ha0 hw.1
      rw [hfdef, blockTailSum_of_lt_one (X := X) y z hw.2 ω, ← hfdef, ← hF0,
        div_le_iff₀ hw0]
      have hw1 : 1 ≤ (1 + η) * w := by
        have := (inv_lt_iff_one_lt_mul₀ h1η).1 hw.1
        linarith
      nlinarith [sq_nonneg ‖F0‖]
    calc (∫ w in Set.Ioo (1 + η)⁻¹ 1, ‖blockTailSum f y z w ω‖ ^ 2 / w)
        ≤ ∫ _w in Set.Ioo (1 + η)⁻¹ 1, (1 + η) * ‖F0‖ ^ 2 :=
          setIntegral_mono_on hI1 (integrableOn_const (by
            rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioo hpt
      _ = (1 - (1 + η)⁻¹) * ((1 + η) * ‖F0‖ ^ 2) := by
          rw [setIntegral_const, Real.volume_real_Ioo_of_le ha1.le, smul_eq_mul]
      _ = η * ‖F0‖ ^ 2 := by field_simp; ring
  have hpiece2 : (∫ w in Set.Ico 1 (x / z), ‖blockTailSum f y z w ω‖ ^ 2 / w)
      ≤ Real.exp (2 * c) * ((2 * Real.pi)⁻¹ * P) := by
    rw [integral_Ico_eq_integral_Ioo]
    have hsub : Set.Ioo 1 (x / z) ⊆ Set.Ioi (1 : ℝ) := fun w hw => hw.1
    have hcmp : ∀ w ∈ Set.Ioo 1 (x / z), ‖blockTailSum f y z w ω‖ ^ 2 / w
        ≤ Real.exp (2 * c) * (‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
      intro w hw
      have hw0 : (0 : ℝ) < w := lt_trans one_pos hw.1
      refine div_le_exp_mul_div_rpow (sq_nonneg _) hw0 ?_
      rw [Real.rpow_def_of_pos hw0]
      refine Real.exp_le_exp.2 ?_
      have hlogw : Real.log w ≤ Real.log (x / z) := Real.log_le_log hw0 hw.2.le
      have h1 : Real.log w * (2 * σ) ≤ Real.log (x / z) * (2 * σ) :=
        mul_le_mul_of_nonneg_right hlogw (by linarith)
      linarith
    calc (∫ w in Set.Ioo 1 (x / z), ‖blockTailSum f y z w ω‖ ^ 2 / w)
        ≤ ∫ w in Set.Ioo 1 (x / z),
            Real.exp (2 * c) * (‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
          refine integral_mono_of_nonneg ?_ ((hIint.mono_set hsub).const_mul _) ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact div_nonneg (sq_nonneg _) (lt_trans one_pos hw.1).le
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact hcmp w hw
      _ = Real.exp (2 * c) * ∫ w in Set.Ioo 1 (x / z),
            ‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ) := integral_const_mul _ _
      _ ≤ Real.exp (2 * c) * ∫ w in Set.Ioi (1 : ℝ),
            ‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine setIntegral_mono_set hIint ?_ (Filter.Eventually.of_forall fun w hw => hsub hw)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans one_pos hu)) _)
      _ = Real.exp (2 * c) * ((2 * Real.pi)⁻¹ * P) := by rw [hpars]
  have hwint : (∫ w in Set.Ioo (x / (x * (1 + η))) (x / z), ‖blockTailSum f y z w ω‖ ^ 2 / w)
      ≤ η * ‖F0‖ ^ 2 + Real.exp (2 * c) * ((2 * Real.pi)⁻¹ * P) := by
    rw [hlow, ← Set.Ioo_union_Ico_eq_Ioo ha1 h1b,
      setIntegral_union (Set.disjoint_left.2 fun w hw hw' => not_lt.2 hw'.1 hw.2)
        measurableSet_Ico hI1 hI2]
    linarith
  have hcoef0 : (0 : ℝ) ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ))) / Real.log z := by
    positivity
  calc (K / η) * (∫ t in Set.Icc ((z : ℝ)) (x * (1 + η)),
          ‖blockTailSum f y z (x / t) ω‖ ^ 2
            * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z)))
      ≤ (K / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ))) / Real.log z
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / z), ‖blockTailSum f y z w ω‖ ^ 2 / w) :=
        mul_le_mul_of_nonneg_left hstep12 (by positivity)
    _ ≤ (K / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (z : ℝ))) / Real.log z
          * (η * ‖F0‖ ^ 2 + Real.exp (2 * c) * ((2 * Real.pi)⁻¹ * P))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwint hcoef0) (by positivity)
    _ = _ := by
        field_simp

/-! ### The smoothing step and the error -/

omit [MeasurableSpace Ω] in
/-- **The band's smoothing step with a `(1+ε)` split**:
`RMF.sum_weightedRoughTerm_le_setIntegral_eps` at the band tail. -/
theorem sum_blockTailTerm_le_setIntegral_eps {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖f ω n‖ ≤ 1) (y z : ℕ) {x η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) {T : Set ℝ} (hTm : MeasurableSet T) {b : ℝ → ℝ}
    (hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ T)
    (hb : ∀ t ∈ T, ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hint : ∀ r ∈ S, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
            (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2) t) T volume)
    (hintT : IntegrableOn (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2 * b t) T volume) :
    ∑ r ∈ S, blockTailTerm f y z x ω r
      ≤ ((1 + ε) / η) * (∫ t in T, ‖blockTailSum f y z (x / t) ω‖ ^ 2 * b t)
        + ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖blockTailSum f y z (x / r) ω - blockTailSum f y z (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 := by
  set G : ℝ → ℂ := fun u => blockTailSum f y z u ω with hGdef
  have hterm : ∀ r ∈ S, blockTailTerm f y z x ω r
      = (fun t => ‖G (x / t)‖ ^ 2) (r : ℝ) / (r : ℝ) := by
    intro r _
    rw [blockTailTerm, inv_mul_eq_div]
  rw [Finset.sum_congr rfl hterm]
  have hexch := sum_smul_setIntegral_le
    (g := fun t => ‖G (x / t)‖ ^ 2) (b := b) (S := S)
    (I := fun r => Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)))
    (c := fun r => (((r : ℝ)) ^ 2)⁻¹)
    (fun t => by positivity) hsub (fun r _ => measurableSet_Icc) hint hintT hb hTm
  refine le_trans (sum_div_le_of_average_const (K := 1 + ε) (g := fun t => ‖G (x / t)‖ ^ 2)
    (e := fun r => (1 + 1 / ε) * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G (x / r) - G (x / t)‖ ^ 2))
    hη (by positivity) hS (fun r hr => ?_) hexch) (le_of_eq ?_)
  · have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS r hr
    have hle : (r : ℝ) ≤ (r : ℝ) * (1 + η) := by nlinarith
    have hkey := normSq_average_bound_eps G x hr0 hη hε
      (intervalIntegrable_normSq_blockTailSum hbnd y z hle)
      (intervalIntegrable_normSq_blockTailSum_sub hbnd y z hle)
    rw [intervalIntegral_eq_setIntegral_Icc hle, intervalIntegral_eq_setIntegral_Icc hle]
      at hkey
    exact hkey
  · congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
    ring

/-- **The expectation of the band's smoothing error, explicit.**  For `S` a set of `z`-rough
integers in `[1, x]` and a sieve level `2 ≤ z' ≤ z`,
`E[((1+1/ε)/(2η))·∑_{r∈S}(2∫‖T(x/r) - T(x/t)‖²)/r²] ≤ E_err` (`RMF.smallQReductionErr x z' η ε`):
each window contributes `2η(η + (1+η)r/x)/r`
(`RMF.integral_sum_setIntegral_normSq_blockTailSum_sub_le`), `∑_{r≤x}1/r ≤ 1 + log x`, and the
rough `r ≤ x` number at most `2x/log z' + 5z'(1+log z')³`. -/
theorem integral_blockTailSmoothingError_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {z z' : ℕ}
    (hz' : 2 ≤ z') (hz'z : z' ≤ z) {x η ε : ℝ} (hx : 1 ≤ x) (hη : 0 < η) (hε : 0 < ε)
    {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough z r) (hS1 : ∀ r ∈ S, 1 ≤ r)
    (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    (∫ ω, ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
        (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
          ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
            - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
          / ((r : ℝ)) ^ 2 ∂μ)
      ≤ smallQReductionErr x z' η ε := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hS0 : ∀ r ∈ S, 0 < r := fun r hr => hS1 r hr
  have hz2 : (2 : ℝ) ≤ (z' : ℝ) := by exact_mod_cast hz'
  have hlz : 0 < Real.log z' := Real.log_pos (by linarith)
  rw [integral_const_mul]
  have hE := integral_sum_setIntegral_normSq_blockTailSum_sub_le hX y z hx0 hη hS0
  have hc0 : (0 : ℝ) ≤ (1 + 1 / ε) / (2 * η) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hE hc0) ?_
  have hterm : ∀ r ∈ S, (1 + 1 / ε) / (2 * η) * (2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ))
      = (1 + 1 / ε) * η * ((r : ℝ))⁻¹ + (1 + 1 / ε) * (1 + η) / x := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS0 r hr
    field_simp
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  -- the harmonic mass
  have hsubI : S ⊆ Finset.Icc 1 ⌊x⌋₊ := fun r hr =>
    Finset.mem_Icc.2 ⟨hS1 r hr, Nat.le_floor (hSx r hr)⟩
  have hH : ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ 1 + Real.log x := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubI fun i _ _ => by positivity) ?_
    have hh := harmonic_le_one_add_log ⌊x⌋₊
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    refine le_trans hh ?_
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg hx]
    · linarith [Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le hx0.le)]
  -- the count
  have hcardS : (S.card : ℝ) ≤ 2 * x / Real.log z' + 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 := by
    have hsubR : S ⊆ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z' n} := fun r hr =>
      Finset.mem_filter.2 ⟨hsubI hr, (hSr r hr).mono hz'z⟩
    have h1 : (S.card : ℝ) ≤ (roughCount z' x : ℝ) := by
      rw [roughCount]
      exact_mod_cast Finset.card_le_card hsubR
    have hzero : roughCount z' (1 / 2) = 0 := by
      rw [roughCount, show ⌊(1 / 2 : ℝ)⌋₊ = 0 by norm_num]
      simp
    have hbrun := roughCount_sub_le_brun hz' (x := 1 / 2) (H := x - 1 / 2) (by norm_num)
      (by linarith)
    rw [show (1 / 2 : ℝ) + (x - 1 / 2) = x by ring, hzero, Nat.cast_zero, sub_zero] at hbrun
    have h2 : 2 * (x - 1 / 2) / Real.log z' ≤ 2 * x / Real.log z' :=
      div_le_div_of_nonneg_right (by linarith) hlz.le
    linarith
  have hc1 : 0 ≤ (1 + 1 / ε) * (1 + η) / x := by positivity
  have hstep1 : (1 + 1 / ε) * η * ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ (1 + 1 / ε) * η * (1 + Real.log x) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hstep2 : (S.card : ℝ) * ((1 + 1 / ε) * (1 + η) / x)
      ≤ (2 * x / Real.log z' + 5 * (z' : ℝ) * (1 + Real.log z') ^ 3)
          * ((1 + 1 / ε) * (1 + η) / x) :=
    mul_le_mul_of_nonneg_right hcardS hc1
  have hfin : (2 * x / Real.log z' + 5 * (z' : ℝ) * (1 + Real.log z') ^ 3)
        * ((1 + 1 / ε) * (1 + η) / x)
      = (1 + 1 / ε) * ((1 + η) * (2 / Real.log z' + 5 * (z' : ℝ) * (1 + Real.log z') ^ 3 / x)) := by
    field_simp
  rw [smallQReductionErr]
  nlinarith [hstep1, hstep2, hfin]

/-! ### The rough sum and the truncation bound -/

omit [MeasurableSpace Ω] in
/-- **The band's rough sum at one `ω`, with its constants.**  For values of norm at most one, `S` a
set of `z`-rough integers in `(1, x]`, a sieve level `2 ≤ z' ≤ z`, `1 + η < z ≤ x` and `σ > 0` with
`σ log(x/z) ≤ c`: `∑_{r∈S} r⁻¹|T(x/r)|² ≤ K((η/log z)|F(½)|² + e^{2c}Ψ) + E(ω)`, with
`K = RMF.lemmaTConst z z' η ε`, `Ψ = RMF.bandDiffLine` and `E` the smoothing error.  Every
`z`-rough `r > 1` exceeds `z`, so the sieve covers all of `S`: there is no Rankin range. -/
theorem sum_blockTailTerm_le_explicit {X : ℕ → Ω → ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1) (y : ℕ) {z z' : ℕ}
    (hz' : 2 ≤ z') (hz'z : z' ≤ z) {σ x η ε c : ℝ} (hzx : (z : ℝ) ≤ x) (hσ : 0 < σ)
    (hσlog : σ * Real.log (x / z) ≤ c) (hη : 0 < η) (hzη : 1 + η < z) (hε : 0 < ε)
    {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough z r) (hone : ∀ r ∈ S, 1 < r)
    (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    ∑ r ∈ S, blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r
      ≤ lemmaTConst z z' η ε * (η / Real.log z
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                (z + 1) (1 / 2 : ℂ) ω‖ ^ 2
          + Real.exp (2 * c) * bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω)
        + ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
                - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans hz' hz'z
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hden : (0 : ℝ) < 1 + η := by linarith
  have hlogz : (0 : ℝ) < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hS : ∀ r ∈ S, 0 < r := fun r hr => lt_trans Nat.zero_lt_one (hone r hr)
  have hC := smallQSieveConst_pos hz' hz'z hη
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ w : ℝ, ‖blockTailSum f y z w ω‖ ≤ B :=
    ⟨_, fun w => norm_blockTailSum_le_sum f y z w ω⟩
  have hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))
      ⊆ Set.Icc ((z : ℝ)) (x * (1 + η)) := by
    intro r hr t ht
    have hzr : (z : ℝ) < (r : ℝ) := by
      exact_mod_cast (hSr r hr).lt_of_one_lt (hone r hr)
    exact ⟨le_trans hzr.le ht.1, le_trans ht.2 (mul_le_mul_of_nonneg_right (hSx r hr) hden.le)⟩
  have hbT : ∀ t ∈ Set.Icc ((z : ℝ)) (x * (1 + η)),
      ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
          * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
        ≤ smallQSieveConst z z' η * (1 + η) ^ 2 * (t * η / (1 + η) + 1)
            / (t ^ 2 * Real.log z) :=
    fun t ht => sum_inv_sq_indicator_le_smallQSieveConst hz' hz'z hSr hη hzη ht.1
  obtain ⟨hint, hintT⟩ := integrableOn_sieveShape_of_bound
    (measurable_blockTailSum_truncation f y z ω) (s := x * (1 + η)) (K := B)
    hη hzpos hC hlogz (fun t _ => hB (x / t))
  have hsm := sum_blockTailTerm_le_setIntegral_eps
    (T := Set.Icc ((z : ℝ)) (x * (1 + η)))
    (b := fun t => smallQSieveConst z z' η * (1 + η) ^ 2 * (t * η / (1 + η) + 1)
      / (t ^ 2 * Real.log z))
    hbnd y z hη hε hS measurableSet_Icc hsub hbT (fun r _ => hint r) hintT
  have hpr := setIntegral_normSq_blockTailSum_mul_sieve_le_sub (X := X) y z hzpos hzx hσ hσlog
    hη hC.le (by positivity : (0 : ℝ) ≤ 1 + ε) hlogz ω
  refine le_trans hsm (add_le_add ?_ le_rfl)
  refine le_trans hpr (le_of_eq ?_)
  rw [lemmaTConst, bandDiffLine]
  ring

/-- **The band's line functional in difference form has integrable powers**: the difference is
jointly measurable and at most `2·2^{z-y}` almost surely, so
`RMF.integrable_rpow_setIntegral_lineDiv_of_bound` applies on the whole line. -/
theorem integrable_rpow_bandDiffLine {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) {σ q : ℝ} (hσ : 0 < σ) (hz : 1 < z)
    (hq0 : 0 ≤ q) :
    Integrable (fun ω => bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω ^ q)
      μ := by
  have hlz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hL : 0 < 2 * Real.pi * Real.log z := by positivity
  have hmeas1 := measurable_uncurry_randomEulerProductIco_line hX (y + 1) (z + 1) (-σ)
  have hmeas0 := measurable_uncurry_randomEulerProductIco_line hX (y + 1) (z + 1) 0
  have hF0m : Measurable fun ω : Ω => randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (1 / 2 : ℂ) ω := by
    have h := hmeas0.comp (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
    convert h using 1
    funext ω
    simp
  have hFm : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          (1 / 2 : ℂ) ω
        - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) := by
    have h := (hF0m.comp measurable_fst).sub hmeas1
    convert h using 1
    funext w
    obtain ⟨ω, t⟩ := w
    simp only [Function.comp_apply, Function.uncurry_apply_pair, Pi.sub_apply]
    congr 2
    push_cast
    ring
  have hb0 := ae_forall_norm_randomEulerProductIco_line_le_two_pow hX (y + 1) (z + 1)
    (c := 0) (by norm_num)
  have hb1 := ae_forall_norm_randomEulerProductIco_line_le_two_pow hX (y + 1) (z + 1)
    (c := -σ) (by linarith)
  have hU : ∀ᵐ ω ∂μ, ∀ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          (1 / 2 : ℂ) ω
        - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ 2 * 2 ^ (z + 1 - (y + 1)) := by
    filter_upwards [hb0, hb1] with ω h0 h1
    intro t
    have e0 : (1 / 2 : ℂ) = (1 / 2 : ℂ) - ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by simp
    have e1 : (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
        = (1 / 2 : ℂ) - ((-σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    refine le_trans (norm_sub_le _ _) ?_
    rw [e1]
    have h0' := h0 0
    rw [← e0] at h0'
    linarith [h1 t]
  have hI := integrable_rpow_setIntegral_lineDiv_of_bound (S := Set.univ) (q := q)
    (L := 2 * Real.pi * Real.log z) hσ hL hq0 hFm hU
  simp only [Measure.restrict_univ] at hI
  exact hI

/-- **The band's rough sum in `q`-th moment, with its constants.**  For `0 < q ≤ 1`, under the
hypotheses of `RMF.sum_blockTailTerm_le_explicit`:
`E[(∑_{r∈S} r⁻¹|T(x/r)|²)^q] ≤ (Kη/log z)^q E|F(½)|^{2q} + (Ke^{2c})^q E[Ψ^q] + E_err^q`,
`K = RMF.lemmaTConst z z' η ε`, `E_err = RMF.smallQReductionErr x z' η ε`. -/
theorem integral_rpow_sum_blockTailTerm_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {z z' : ℕ} (hz' : 2 ≤ z') (hz'z : z' ≤ z)
    {σ x η ε c q : ℝ} (hzx : (z : ℝ) ≤ x) (hσ : 0 < σ) (hσlog : σ * Real.log (x / z) ≤ c)
    (hη : 0 < η) (hzη : 1 + η < z) (hε : 0 < ε) (hq0 : 0 < q) (hq1 : q ≤ 1)
    {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough z r) (hone : ∀ r ∈ S, 1 < r)
    (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    (∫ ω, (∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
      ≤ (lemmaTConst z z' η ε * (η / Real.log z)) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q
          * (∫ ω, bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω ^ q ∂μ)
        + smallQReductionErr x z' η ε ^ q := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans hz' hz'z
  have hz1 : 1 < z := by omega
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith) hzx
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hK := lemmaTConst_pos hz' hz'z hη hε
  have hKa : 0 ≤ lemmaTConst z z' η ε * (η / Real.log z) := by positivity
  have hKb : 0 ≤ lemmaTConst z z' η ε * Real.exp (2 * c) := by positivity
  obtain ⟨Err, hErr⟩ : ∃ Err : Ω → ℝ, Err = fun ω => ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
          - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Ω → ℝ, A = fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
        (1 / 2 : ℂ) ω‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Ω → ℝ, Ψ = fun ω =>
      bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω := ⟨_, rfl⟩
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => by rw [hA]; positivity
  have hΨ0 : ∀ ω, 0 ≤ Ψ ω := fun ω => by rw [hΨ]; exact bandDiffLine_nonneg _ y z σ ω hz1.le
  have hErr0 : ∀ ω, 0 ≤ Err ω := fun ω => by
    rw [hErr]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => ?_)
    refine div_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
    exact setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hErrint : Integrable Err μ := by
    rw [hErr]
    refine (integrable_finsetSum S fun r _ => ?_).const_mul _
    simp only [integral_Icc_eq_integral_Ioc]
    exact ((integrable_uncurry_normSq_blockTailSum_sub hX y z x r
      ((r : ℝ) * (1 + η))).integral_prod_left.const_mul 2).div_const _
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hApow : ∀ ω, A ω ^ q
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          (1 / 2 : ℂ) ω‖ ^ (2 * q) := by
    intro ω
    rw [hA]
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hstep : ∀ᵐ ω ∂μ, (∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q
      ≤ (lemmaTConst z z' η ε * (η / Real.log z)) ^ q * A ω ^ q
        + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q * Ψ ω ^ q + Err ω ^ q := by
    filter_upwards [hbdd] with ω hb
    have h1 : (∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r)
        ≤ lemmaTConst z z' η ε * (η / Real.log z) * A ω
          + lemmaTConst z z' η ε * Real.exp (2 * c) * Ψ ω + Err ω := by
      have h := sum_blockTailTerm_le_explicit (X := X) (ω := ω) hb y hz' hz'z hzx hσ hσlog hη
        hzη hε hSr hone hSx
      rw [hA, hΨ, hErr]
      dsimp only
      linarith
    have hsum0 : (0 : ℝ) ≤ ∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r :=
      Finset.sum_nonneg fun r _ => blockTailTerm_nonneg _ _ _ _ _ _
    have ha := mul_nonneg hKa (hA0 ω)
    have hb' := mul_nonneg hKb (hΨ0 ω)
    calc (∑ r ∈ S,
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q
        ≤ (lemmaTConst z z' η ε * (η / Real.log z) * A ω
            + lemmaTConst z z' η ε * Real.exp (2 * c) * Ψ ω + Err ω) ^ q :=
          Real.rpow_le_rpow hsum0 h1 hq0.le
      _ ≤ (lemmaTConst z z' η ε * (η / Real.log z) * A ω
            + lemmaTConst z z' η ε * Real.exp (2 * c) * Ψ ω) ^ q + Err ω ^ q :=
          Real.rpow_add_le_add_rpow (add_nonneg ha hb') (hErr0 ω) hq0.le hq1
      _ ≤ (lemmaTConst z z' η ε * (η / Real.log z) * A ω) ^ q
            + (lemmaTConst z z' η ε * Real.exp (2 * c) * Ψ ω) ^ q + Err ω ^ q := by
          have := Real.rpow_add_le_add_rpow ha hb' hq0.le hq1
          linarith
      _ = (lemmaTConst z z' η ε * (η / Real.log z)) ^ q * A ω ^ q
            + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q * Ψ ω ^ q + Err ω ^ q := by
          rw [Real.mul_rpow hKa (hA0 ω), Real.mul_rpow hKb (hΨ0 ω)]
  -- integrability
  have hI1 : Integrable (fun ω => (∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q) μ :=
    integrable_rpow_sum_blockTailTerm hX y z x (fun r hr => (hone r hr).le) hq0.le
  have hIA : Integrable (fun ω => A ω ^ q) μ := by
    have hb := ae_forall_norm_randomEulerProductIco_line_le_two_pow hX (y + 1) (z + 1)
      (c := 0) (by norm_num)
    have hm : Measurable fun ω => A ω ^ q := by
      have h0 := measurable_uncurry_randomEulerProductIco_line hX (y + 1) (z + 1) 0
      have h := h0.comp (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
      rw [hA]
      refine (Real.continuous_rpow_const hq0.le).measurable.comp ?_
      convert h.norm.pow_const 2 using 1
      funext ω
      simp
    refine (memLp_top_of_bound hm.aestronglyMeasurable
      ((((2 : ℝ) ^ (z + 1 - (y + 1))) ^ 2) ^ q) ?_).integrable le_top
    filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hA0 ω) _)]
    refine Real.rpow_le_rpow (hA0 ω) ?_ hq0.le
    rw [hA]
    have h := hω 0
    simp only [Complex.ofReal_zero, sub_zero, zero_mul, add_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hIΨ : Integrable (fun ω => Ψ ω ^ q) μ := by
    rw [hΨ]
    exact integrable_rpow_bandDiffLine hX y z hσ hz1 hq0.le
  have hIE : Integrable (fun ω => Err ω ^ q) μ :=
    integrable_rpow_of_integrable hErrint (Filter.Eventually.of_forall hErr0) hq0.le hq1
  have hJ : (∫ ω, Err ω ^ q ∂μ) ≤ smallQReductionErr x z' η ε ^ q := by
    refine integral_rpow_le_rpow_of_integral_le hq0.le hq1 (Filter.Eventually.of_forall hErr0)
      hErrint ?_
    rw [hErr]
    exact integral_blockTailSmoothingError_le_explicit hX y hz' hz'z hx1 hη hε hSr
      (fun r hr => (hone r hr).le) hSx
  have hIa : Integrable (fun ω => (lemmaTConst z z' η ε * (η / Real.log z)) ^ q * A ω ^ q) μ :=
    hIA.const_mul _
  have hIb : Integrable
      (fun ω => (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q * Ψ ω ^ q) μ := hIΨ.const_mul _
  have hIab : Integrable (fun ω => (lemmaTConst z z' η ε * (η / Real.log z)) ^ q * A ω ^ q
      + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q * Ψ ω ^ q) μ := hIa.add hIb
  have hintA : (∫ ω, A ω ^ q ∂μ)
      = ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hApow)
  have hintΨ : (∫ ω, Ψ ω ^ q ∂μ)
      = ∫ ω, bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω ^ q ∂μ := by
    rw [hΨ]
  calc (∫ ω, (∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
      ≤ ∫ ω, ((lemmaTConst z z' η ε * (η / Real.log z)) ^ q * A ω ^ q
          + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q * Ψ ω ^ q + Err ω ^ q) ∂μ :=
        integral_mono_ae hI1 (hIab.add hIE) hstep
    _ = (lemmaTConst z z' η ε * (η / Real.log z)) ^ q * (∫ ω, A ω ^ q ∂μ)
          + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q * (∫ ω, Ψ ω ^ q ∂μ)
          + ∫ ω, Err ω ^ q ∂μ := by
        rw [integral_add hIab hIE, integral_add hIa hIb, integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        rw [hintA, hintΨ]
        linarith [hJ]

/-- **The truncation bound with its constants, in difference form.**  For `0 < q ≤ 1`, a band
`y ≤ z`, a sieve level `2 ≤ z' ≤ z`, `1 + η < z ≤ x`, `σ > 0` with `σ log(x/z) ≤ c` and `ε > 0`:

`E|𝒯_{y,z}(x)|^{2q} ≤ E|T(x)|^{2q} + (Kη/log z)^q E|F(½)|^{2q} + (Ke^{2c})^q E[Ψ^q] + E_err^q`,

`K = RMF.lemmaTConst z z' η ε → 2(1+ε)`, `Ψ = RMF.bandDiffLine … σ`,
`E_err = RMF.smallQReductionErr x z' η ε`.  Conditioning
(`RMF.integral_rpow_norm_blockTruncationTail_le`) and the rough sum
(`RMF.integral_rpow_sum_blockTailTerm_le_explicit`). -/
theorem integral_rpow_norm_blockTruncationTail_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y z z' : ℕ} (hyz : y ≤ z) (hz' : 2 ≤ z')
    (hz'z : z' ≤ z) {σ x η ε c q : ℝ} (hzx : (z : ℝ) ≤ x) (hσ : 0 < σ)
    (hσlog : σ * Real.log (x / z) ≤ c) (hη : 0 < η) (hzη : 1 + η < z) (hε : 0 < ε)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ (2 * q) ∂μ)
        + (lemmaTConst z z' η ε * (η / Real.log z)) ^ q
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (z + 1) (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
        + (lemmaTConst z z' η ε * Real.exp (2 * c)) ^ q
          * (∫ ω, bandDiffLine (fun ω => squarefreeExtension fun p => X p ω) y z σ ω ^ q ∂μ)
        + smallQReductionErr x z' η ε ^ q := by
  classical
  haveI := hX.isProbabilityMeasure
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans hz' hz'z
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith) hzx
  have hcond := integral_rpow_norm_blockTruncationTail_le hX hyz hx1 hq0.le hq1
  have hrough := integral_rpow_sum_blockTailTerm_le_explicit (μ := μ) hX y hz' hz'z hzx hσ
    hσlog hη hzη hε hq0 hq1
    (S := ({r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}).erase 1)
    (fun r hr => (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).2.1)
    (fun r hr => by
      have h1 := Finset.ne_of_mem_erase hr
      have h2 := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).1
      omega)
    (fun r hr => by
      have h := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).2
      exact le_trans (by exact_mod_cast h) (Nat.floor_le (by linarith)))
  linarith

/-! ### The atom -/

/-- **The atom of the truncation bound, explicit**: for `z ≥ 2` and `w > 0`,
`E|T_{y,z}(w)|² ≤ w^{-1/log z}·exp(e·∑_{y<p≤z} 1/p)`.  Rankin at `δ = 1/log z`
(`RMF.blockTailSum_le_rankin`) and `p^{1/log z} ≤ e` on the band.  With Mertens on the band
(`RMF.sum_primesIco_inv_le`) the exponential is `κ^e` up to `e^{9.0028e(1/log y + 1/log z)}`. -/
theorem integral_normSq_blockTailSum_le_exp_sum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {z : ℕ} (hz : 2 ≤ z) {w : ℝ} (hw : 0 < w) :
    (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
      ≤ w ^ (-(Real.log z)⁻¹)
        * Real.exp (Real.exp 1 * ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ))⁻¹) := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hδ : 0 < (Real.log z)⁻¹ := inv_pos.2 hlogz
  rw [integral_normSq_blockTailSum hX y z w]
  refine le_trans (blockTailSum_le_rankin y z hw hδ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hw.le _)
  refine le_trans (Real.prod_one_add_le_exp_sum _ fun p =>
    Real.rpow_nonneg (Nat.cast_nonneg p) _) (Real.exp_le_exp.2 ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpz : (p : ℝ) ≤ z := by
    have := (mem_primesIco.1 hp).2.2
    exact_mod_cast (by omega : p ≤ z)
  have hpow : (p : ℝ) ^ (Real.log z)⁻¹ ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp0]
    refine Real.exp_le_exp.2 ?_
    rw [← div_eq_mul_inv, div_le_one hlogz]
    exact Real.log_le_log hp0 hpz
  rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.2 hp0.le)

end RMF
