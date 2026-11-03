/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BandTail
import RMF.Weighted.Pointwise
import RMF.Weighted.Principal

/-!
# The band tail against the sieve

The truncation bound for a band averages the rough sum `∑_r r⁻¹|T(x/r)|²` over windows
`[r, r(1+η)]`, counts the windows by Brun's sieve, and carries the rest to the band's
Euler-product line by Plancherel.  At `η = 1/V`, `V = log x/log z`, the bound on the averaging
error is `O(1)`.  The sieve's denominator is `log z` once the sifting range
`tη/(1+η) = t/(V+1)` exceeds `z`, that is above `R₀ ≍ Vz`, and the range `z < r ≤ R₀` is left to
Rankin.  This file holds the range above `R`, at one `ω` and for abstract `η` and `R`:

* **the principal term** (`RMF.setIntegral_normSq_blockTailSum_mul_sieve_le`), the head's route
  (`RMF.setIntegral_normSq_mul_sieve_le`) at the shift `-c`: the merge and `t ↦ x/t`
  (`RMF.setIntegral_mul_sieveShape_le`), then `dw/w ≤ e²·w^{2c-1}dw` on `w ≥ ½`, then the band's
  Plancherel; `RMF.two_mul_sieve_shape_div_le_of_four_le` is the arithmetic of `η ≤ 1`, `ηR ≥ 4`;
* **the smoothing, with the sieve discharged** (`RMF.exists_sum_blockTailTerm_le_sieve`):
  `RMF.sum_blockTailTerm_le_setIntegral` with the counting bound of
  `RMF.exists_sum_inv_sq_indicator_le_sieve'` at roughness `z` and the integrability conditions of
  `RMF.integrableOn_sieveShape_of_bound`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The numerical content of the band's window.**  For `0 < η ≤ 1` and `ηR ≥ 4` the combined
weight `2(1+η)²(η/(1+η) + 1/R)/η = 2(1+η) + 2(1+η)²/(ηR)` is at most `4 + 2 < 2π`.  At `η = 1/V`
and `R = A(V+1)z` the condition is `A(V+1)z/V ≥ 4`, implied by `Az ≥ 4`. -/
lemma two_mul_sieve_shape_div_le_of_four_le {η R : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hR : 4 ≤ η * R) :
    2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / η ≤ 2 * Real.pi := by
  have hηR : (0 : ℝ) < η * R := by linarith
  have hR0 : (0 : ℝ) < R := pos_of_mul_pos_right hηR hη.le
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hval : 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / η
      = 2 * (1 + η) + 2 * (1 + η) ^ 2 / (η * R) := by
    field_simp
  rw [hval]
  have hsq : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have h2 : 2 * (1 + η) ^ 2 / (η * R) ≤ 2 := by
    rw [div_le_iff₀ hηR]
    linarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith

omit [MeasurableSpace Ω] in
/-- **The principal term for the band, at one `ω`.**  For `0 < η ≤ 1`, `0 < 2c ≤ 1`,
`0 < R ≤ x(1+η)` and `b(t) = C(1+η)²(tη/(1+η)+1)/(t² log z)` the sieve bound,
`(2/η)·∫_{[R, x(1+η)]} |T(x/t)|²·b(t) dt ≤ e²·C·(log z)⁻¹·∫_ℝ |F_{y,z}(½-c+it)/(c+it)|² dt`.
The head's route (`RMF.setIntegral_normSq_mul_sieve_le`): the merge and `t ↦ x/t`, then
`dw/w ≤ e²·w^{2c-1}dw` on `w > 1/(1+η) ≥ ½`, then the band's Plancherel
(`RMF.integral_normSq_blockTailSum_eq_line`).  No hypothesis on `X`; `η` enters through `hshape`. -/
theorem setIntegral_normSq_blockTailSum_mul_sieve_le {X : ℕ → Ω → ℂ} (y z : ℕ)
    {x η c C R : ℝ} (hx : 0 < x) (hR : 0 < R) (hRx : R ≤ x * (1 + η)) (hη : 0 < η)
    (hη1 : η ≤ 1) (hc : 0 < c) (hc1 : 2 * c ≤ 1) (hC : 0 < C) (hlogz : 0 < Real.log z)
    (hshape : 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / η ≤ 2 * Real.pi) (ω : Ω) :
    (2 / η) * (∫ t in Set.Icc R (x * (1 + η)),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z)))
      ≤ Real.exp 2 * C * ((Real.log z)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
              ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
            / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hpars := integral_normSq_blockTailSum_eq_line (X := X) y z hc ω
  have hIint := integrableOn_normSq_blockTailSum_mul_rpow
    (fun ω => squarefreeExtension fun p => X p ω) y z hc ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω
  set P : ℝ := ∫ t : ℝ, ‖randomEulerProductIco f (y + 1) (z + 1)
      ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  -- the crude bound on `T`, uniform in the truncation point
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ w : ℝ, ‖blockTailSum f y z w ω‖ ≤ B :=
    ⟨_, fun w => norm_blockTailSum_le_sum f y z w ω⟩
  have hmeas : Measurable fun t : ℝ => ‖blockTailSum f y z (x / t) ω‖ ^ 2 :=
    ((measurable_blockTailSum_truncation f y z ω).comp
      (measurable_const.div measurable_id)).norm.pow_const 2
  have hint1 : IntegrableOn (fun t => ‖blockTailSum f y z (x / t) ω‖ ^ 2 / t)
      (Set.Icc R (x * (1 + η))) volume := by
    refine Measure.integrableOn_of_bounded (M := B ^ 2 / R)
      measure_Icc_lt_top.ne (hmeas.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hR ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ht0.le)]
    calc ‖blockTailSum f y z (x / t) ω‖ ^ 2 / t ≤ B ^ 2 / t := by
          gcongr
          exact hB (x / t)
      _ ≤ B ^ 2 / R := div_le_div_of_nonneg_left (sq_nonneg _) hR ht.1
  -- Steps 1-2: the sieve's two halves merge on `t ≥ R`, and `t ↦ x/t` preserves `dt/t`
  have hstep12 : (∫ t in Set.Icc R (x * (1 + η)),
        ‖blockTailSum f y z (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z)))
      ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / Real.log z
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / R), ‖blockTailSum f y z w ω‖ ^ 2 / w :=
    setIntegral_mul_sieveShape_le (fun u => ‖blockTailSum f y z u ω‖ ^ 2) hx hR hRx hη hC.le
      hlogz (fun _ => sq_nonneg _) hint1
  -- Step 3: `dw/w ≤ e²·w^{2c-1} dw` above `1/(1+η) ≥ ½`
  have hlow : (1 / 2 : ℝ) ≤ x / (x * (1 + η)) := by
    rw [div_mul_eq_div_div, div_self hx.ne', le_div_iff₀ h1η]
    linarith
  have hsub : Set.Ioo (x / (x * (1 + η))) (x / R) ⊆ Set.Ioi (0 : ℝ) :=
    fun w hw => lt_of_lt_of_le (by norm_num) (hlow.trans hw.1.le)
  have hcmp : ∀ w ∈ Set.Ioo (x / (x * (1 + η))) (x / R),
      ‖blockTailSum f y z w ω‖ ^ 2 / w
        ≤ Real.exp 2 * (‖blockTailSum f y z w ω‖ ^ 2 * w ^ (2 * c - 1)) := by
    intro w hw
    have hw2 : (1 / 2 : ℝ) < w := lt_of_le_of_lt hlow hw.1
    have hw0 : (0 : ℝ) < w := lt_trans (by norm_num) hw2
    have hpow : w ^ (-(2 * c)) ≤ Real.exp 2 := by
      have hinv : Real.log w⁻¹ ≤ w⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hw0)
      rw [Real.log_inv] at hinv
      have hwinv : w⁻¹ < 2 := by
        rw [inv_eq_one_div, div_lt_iff₀ hw0]
        linarith
      have hL : 0 < c * (Real.log w + 1) := mul_pos hc (by linarith)
      rw [Real.rpow_def_of_pos hw0]
      refine Real.exp_le_exp.2 ?_
      have hsplit : Real.log w * -(2 * c) = 2 * c - 2 * (c * (Real.log w + 1)) := by ring
      rw [hsplit]
      linarith
    have key := div_le_exp_two_mul_div_rpow (sq_nonneg ‖blockTailSum f y z w ω‖) hw0 hpow
    have hrw : w ^ (1 + -(2 * c)) = (w ^ (2 * c - 1))⁻¹ := by
      rw [← Real.rpow_neg hw0.le]
      congr 1
      ring
    rwa [hrw, div_inv_eq_mul] at key
  have hstep3 : (∫ w in Set.Ioo (x / (x * (1 + η))) (x / R), ‖blockTailSum f y z w ω‖ ^ 2 / w)
      ≤ Real.exp 2 * ∫ u in Set.Ioi (0 : ℝ), ‖blockTailSum f y z u ω‖ ^ 2 * u ^ (2 * c - 1) := by
    calc (∫ w in Set.Ioo (x / (x * (1 + η))) (x / R), ‖blockTailSum f y z w ω‖ ^ 2 / w)
        ≤ ∫ w in Set.Ioo (x / (x * (1 + η))) (x / R),
            Real.exp 2 * (‖blockTailSum f y z w ω‖ ^ 2 * w ^ (2 * c - 1)) := by
          refine integral_mono_of_nonneg ?_ ((hIint.mono_set hsub).const_mul _) ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact div_nonneg (sq_nonneg _) (le_of_lt (hsub hw))
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact hcmp w hw
      _ = Real.exp 2 * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / R),
            ‖blockTailSum f y z w ω‖ ^ 2 * w ^ (2 * c - 1) := integral_const_mul _ _
      _ ≤ Real.exp 2 * ∫ u in Set.Ioi (0 : ℝ),
            ‖blockTailSum f y z u ω‖ ^ 2 * u ^ (2 * c - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 2).le
          refine setIntegral_mono_set hIint ?_ (Filter.Eventually.of_forall fun w hw => hsub hw)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hu) _)
  -- the constant that survives
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hcoef : 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / η * (2 * Real.pi)⁻¹ ≤ 1 := by
    calc 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / η * (2 * Real.pi)⁻¹
        ≤ 2 * Real.pi * (2 * Real.pi)⁻¹ :=
          mul_le_mul_of_nonneg_right hshape (inv_nonneg.2 hpi0.le)
      _ = 1 := mul_inv_cancel₀ hpi0.ne'
  have hRHS0 : (0 : ℝ) ≤ Real.exp 2 * C * ((Real.log z)⁻¹ * P) :=
    mul_nonneg (mul_nonneg (Real.exp_pos 2).le hC.le)
      (mul_nonneg (inv_nonneg.2 hlogz.le) hP0)
  calc (2 / η) * (∫ t in Set.Icc R (x * (1 + η)),
          ‖blockTailSum f y z (x / t) ω‖ ^ 2
            * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z)))
      ≤ (2 / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / Real.log z
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / R), ‖blockTailSum f y z w ω‖ ^ 2 / w) :=
        mul_le_mul_of_nonneg_left hstep12 (by positivity)
    _ ≤ (2 / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / Real.log z
          * (Real.exp 2 * ∫ u in Set.Ioi (0 : ℝ),
              ‖blockTailSum f y z u ω‖ ^ 2 * u ^ (2 * c - 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 ?_) (by positivity)
        exact div_nonneg (mul_nonneg hC.le (mul_nonneg (sq_nonneg _)
          (by positivity))) hlogz.le
    _ = (2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / R)) / η * (2 * Real.pi)⁻¹)
          * (Real.exp 2 * C * ((Real.log z)⁻¹ * P)) := by rw [hpars]; ring
    _ ≤ 1 * (Real.exp 2 * C * ((Real.log z)⁻¹ * P)) :=
        mul_le_mul_of_nonneg_right hcoef hRHS0
    _ = Real.exp 2 * C * ((Real.log z)⁻¹ * P) := one_mul _

/-- **The band's rough sum above `R`, at one `ω`, smoothed against the sieve.**  For `z ≥ 2`,
`η > 0` and `R > 1 + η` with `Rη/(1+η)` at least the sieve's threshold `H` and at least `z`,
`∑_{r∈S} r⁻¹|T(x/r)|² ≤ (2/η)·∫_{[R, x(1+η)]} |T(x/t)|²·b(t) dt
  + (1/η)·∑_r 2∫_{[r, r(1+η)]} |T(x/r) - T(x/t)|² dt / r²`, with the sieve bound
`b(t) = C(1+η)²(tη/(1+η)+1)/(t² log z)` (`RMF.exists_sum_inv_sq_indicator_le_sieve'` at roughness
`z`, whose denominator above `R` is `log z`), for `f` with values of norm at most one. -/
theorem exists_sum_blockTailTerm_le_sieve :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ (Ω' : Type*) (f : Ω' → ArithmeticFunction ℂ) (ω : Ω'), (∀ n, ‖f ω n‖ ≤ 1) →
      ∀ (y z : ℕ) (x η R : ℝ), 2 ≤ z → 0 < η → 1 + η < R → H ≤ R * η / (1 + η) →
        (z : ℝ) ≤ R * η / (1 + η) →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough z r) → (∀ r ∈ S, R < (r : ℝ)) →
        (∀ r ∈ S, (r : ℝ) ≤ x) →
        ∑ r ∈ S, blockTailTerm f y z x ω r
          ≤ (2 / η) * (∫ t in Set.Icc R (x * (1 + η)),
                ‖blockTailSum f y z (x / t) ω‖ ^ 2
                  * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z)))
            + (1 / η) * ∑ r ∈ S,
                (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
                  ‖blockTailSum f y z (x / r) ω - blockTailSum f y z (x / t) ω‖ ^ 2))
                  / ((r : ℝ)) ^ 2 := by
  obtain ⟨C, H₀, hC, hH₀, hsieve⟩ := exists_sum_inv_sq_indicator_le_sieve'
  refine ⟨C, H₀, hC, hH₀, ?_⟩
  intro Ω' f ω hb y z x η R hz hη hR hHR hzR S hrough hRS hSx
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hR0 : (0 : ℝ) < R := by linarith
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hS : ∀ r ∈ S, 0 < r := fun r hr => by
    have h : (0 : ℝ) < (r : ℝ) := lt_trans hR0 (hRS r hr)
    exact_mod_cast h
  -- every window sits in `[R, x(1+η)]`
  have hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ Set.Icc R (x * (1 + η)) :=
    fun r hr t ht => ⟨le_trans (hRS r hr).le ht.1,
      le_trans ht.2 (mul_le_mul_of_nonneg_right (hSx r hr) h1η.le)⟩
  -- the sieve at roughness `z`, whose denominator above `R` is `log z`
  have hbd : ∀ t ∈ Set.Icc R (x * (1 + η)), ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
      * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
        ≤ C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log z) := by
    intro t ht
    have hRt : R * η / (1 + η) ≤ t * η / (1 + η) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.1 hη.le) h1η.le
    have hkey := hsieve z S hrough hz η t hη (lt_of_lt_of_le hR ht.1) (by linarith)
    have hlog : Real.log (z : ℝ) ≤ Real.log (t * η / (1 + η) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [min_eq_left hlog] at hkey
    exact le_trans hkey (le_of_eq (by ring))
  obtain ⟨hint, hintT⟩ := integrableOn_sieveShape_of_bound
    (measurable_blockTailSum_truncation f y z ω) (s := x * (1 + η)) hη hR0 hC hlogz
    (fun t _ => norm_blockTailSum_le_of_bound hb y z (x / t))
  exact sum_blockTailTerm_le_setIntegral hb y z hη hS measurableSet_Icc hsub hbd
    (fun r _ => hint r) hintT

end RMF
