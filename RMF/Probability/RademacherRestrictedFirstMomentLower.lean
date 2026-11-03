/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.StrongScales
import RMF.Probability.RademacherRestrictedSecondMoment

/-!
# The restricted first moment from below, for the Rademacher function

The lower half of the join: the restricted integral bounded *below* by the free moment, which the
Paley–Zygmund numerator `RMF.exists_le_integral_restricted_normSq_numerator_rademacher` consumes.
The Rademacher counterpart of `RMF.exists_le_integral_restricted_normSq_of_top`; the upper half is
in `Probability/RademacherRestrictedFirstMoment.lean` and `Probability/StrongScales.lean`.

1. `RMF.exists_const_proposition5_harper_rademacher_of_top`: Harper's Proposition 6 (the
   Rademacher form of his Proposition 5) at his scales, with the tilt drop;
2. `RMF.exists_const_proposition5_harper_rademacher_of_top_slope`: its lower half at slope
   `max (RMF.blockSlope 125) B_s`;
3. `RMF.exists_le_setIntegral_restricted_normSq_rademacher_of_top`: the join at a single height;
4. `RMF.exists_le_integral_restricted_normSq_rademacher_of_top`: integrated over the heights.

The barrier runs from `1`, not from a free start `r`: that is the event the numerator is measured
on.  Its slope is `max (RMF.blockSlope 125) B_s` because the restricted second moment
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher` needs
`RMF.blockSlope 125 ≤ B_s`, and raising the slope only enlarges the event.

The file imports `Probability/RademacherRestrictedSecondMoment.lean` for
`RMF.measurableSet_prod_barrierEventAdd`.
-/

open MeasureTheory

namespace RMF

/-! ### Harper's Proposition 6 at his scales, with the drop -/

/-- **Harper's Proposition 6 at his scales and heights, with the tilt drop**: the tilted
probability of the barrier event on `[1, N-d]`, `N = RMF.harperBlockCount D x`, lies between
`α·min\{1, a/√(N-d)\}` and `A·min\{1, a/√(N-d)\}`.  The Rademacher counterpart of
`RMF.exists_const_proposition5_harper_of_top`.  The tilt bound `|σ|\log x ≤ η` with `10η ≤ e^d`
gives `|σ|\log x_{N-d+1} ≤ 1/10` (`RMF.sigma_le_tenth_of_drop`), as
`RMF.exists_const_proposition5_rademacher_of_cutoff_wide` asks. -/
theorem exists_const_proposition5_harper_rademacher_of_top :
    ∃ (D₀ : ℕ) (a₀ α A Bs Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < α ∧ 0 < A ∧ 20 ≤ Bs ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10)) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))
                ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, Bs, Tsh, c, hα, hA, hBs, hTsh, hcpos, H⟩ :=
    exists_const_proposition5_rademacher_of_cutoff_wide
  refine ⟨⌈ϑ₀⌉₊ + 5, a₀, α, A, Bs, Tsh, c, by omega, hα, hA, hBs, hTsh, hcpos, ?_⟩
  intro D hD d
  obtain ⟨x₀, hx₀⟩ := exists_harperThreshold_of_blockCount D (max (2 * d) (n₀ + d))
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ a η s hf hx hres hσ hη hτ0 hτsq hT ha hhf
  obtain ⟨hx1, hDlog, hcount⟩ := hx₀ x hx
  have h2d : 2 * d ≤ harperBlockCount D x := le_trans (le_max_left _ _) hcount
  have hn₀ : n₀ ≤ harperBlockCount D x - d :=
    le_trans (by omega) (Nat.sub_le_sub_right (le_trans (le_max_right _ _) hcount) d)
  have hϑ : ϑ₀ ≤ harperOffset D x := by
    refine le_harperOffset_of_le x ?_
    have hD₀' : ((⌈ϑ₀⌉₊ + 5 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have := le_ceil_add_sub_one ϑ₀ 5 (by norm_num)
    linarith
  have hσ' : |σ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x - d + 1)) ≤ 1 / 10 := by
    refine sigma_le_tenth_of_drop hη (by omega) ?_
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset D x) (harperBlockCount D x) = ⌊x⌋₊ + 1 :=
    blockCutoff_harperOffset hx1 hDlog
  have hy : blockCutoff (harperOffset D x) (harperBlockCount D x - d) ≤ ⌊x⌋₊ + 1 :=
    le_of_le_of_eq (blockCutoff_mono _ (Nat.sub_le _ _)) hcut
  exact H Ω' Y ν hY (harperOffset D x) σ a (harperBlockCount D x - d) (⌊x⌋₊ + 1) s hf hϑ hy
    hres hσ' hτ0 hτsq hT ha hn₀ hhf

/-! ### The slope the restricted second moment asks for

`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher` needs
`RMF.blockSlope 125 ≤ B_s` (through `RMF.harperShiftFloor` and
`RMF.result1Threshold_le_shiftedHeight`), while
`RMF.exists_const_proposition5_harper_rademacher_of_top` exports only `20 ≤ B_s`.  So the slope is
raised to `max (RMF.blockSlope 125) B_s`: a larger slope is a lower floor, hence a bigger event,
which is free for a lower bound (`RMF.barrierEvent_mono`).  The upper half of the estimate does
not survive the enlargement and is not kept. -/

/-- **The lower half of Harper's Proposition 6, at a slope `B_s ≥ RMF.blockSlope 125`**: the slope
of `RMF.exists_const_proposition5_harper_rademacher_of_top` raised to
`max (RMF.blockSlope 125) B_s`, which only enlarges the event (`RMF.barrierEvent_mono`).
`0 < \Re s` is added: it makes the tilted measure a probability measure, so the `toReal`
comparison goes through. -/
theorem exists_const_proposition5_harper_rademacher_of_top_slope :
    ∃ (D₀ : ℕ) (a₀ α Bs Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < α ∧ blockSlope 125 ≤ Bs ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10)) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))
                ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊x⌋₊ + 1) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                      (harperBlockCount D x - d)
                      (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal := by
  obtain ⟨D₀, a₀, α, A, Bs, Tsh, c, hD₀, hα, hA, hBs, hTsh, hcpos, H⟩ :=
    exists_const_proposition5_harper_rademacher_of_top
  refine ⟨D₀, a₀, α, max (blockSlope 125) Bs, Tsh, c, hD₀, hα, le_max_left _ _, hTsh, hcpos, ?_⟩
  intro D hDD d
  obtain ⟨x₀, H⟩ := H D hDD d
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ a η s hf hx hres hs hσ hη hτ0 hτsq hT ha hhf
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hY (⌊x⌋₊ + 1) hs
  refine le_trans (H Ω' Y ν hY x σ a η s hf hx hres hσ hη hτ0 hτsq hT ha hhf).1 ?_
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (barrierEvent_mono ?_ ?_))
  · intro j _ _
    have hmax : Bs ≤ max (blockSlope 125) Bs := le_max_right _ _
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  · intro j _ _
    exact le_rfl

/-! ### The join's lower half -/

/-- **The restricted first moment from below, at a single height, with the drop**:
`α·min\{1, a/√(N-d)\}·E|F(s)|² ≤ ∫_G |F(s)|²` for the barrier event `G` on `[1, N-d]`.  The
Rademacher counterpart of `RMF.exists_le_setIntegral_restricted_normSq_of_top`, from
`RMF.IsRademacherRMF.setIntegral_normSq_eq` and the lower half of Harper's Proposition 6.
`0 < \Re s` is a hypothesis: at a general tilt scale `η` it does not follow from the tilt bound. -/
theorem exists_le_setIntegral_restricted_normSq_rademacher_of_top :
    ∃ (D₀ : ℕ) (a₀ α Bs Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < α ∧ blockSlope 125 ≤ Bs ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10)) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          a₀ ≤ a →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))
                * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν
              ≤ ∫ ω in barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - Bs * j) (fun j => a + j + hf j),
                  ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  obtain ⟨D₀, a₀, α, Bs, Tsh, c, hD₀, hα, hBs, hTsh, hcpos, H⟩ :=
    exists_const_proposition5_harper_rademacher_of_top_slope
  refine ⟨D₀, a₀, α, Bs, Tsh, c, hD₀, hα, hBs, hTsh, hcpos, ?_⟩
  intro D hDD d
  obtain ⟨x₀, H⟩ := H D hDD d
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ a η s hf hx hres hs hσ hη hτ0 hτsq hT ha hhf
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hXmeas : ∀ m, Measurable fun ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := fun m =>
    Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)
  have hAm : MeasurableSet (barrierEvent
      (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
      (harperBlockCount D x - d)
      (fun j => -a - Bs * j) (fun j => a + j + hf j)) :=
    measurableSet_barrierEvent hXmeas _ _ _
  have hprop := H Ω' Y ν hY x σ a η s hf hx hres hs hσ hη hτ0 hτsq hT ha hhf
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  rw [hf'.setIntegral_normSq_eq (⌊x⌋₊ + 1) hs hAm]
  exact mul_le_mul_of_nonneg_right hprop hZ0

set_option maxHeartbeats 800000 in
-- raised for this proof
/-- **The restricted first moment from below, integrated over the heights, with the drop**:
`|T|·α·min\{1, a/√(N-d)\}·E|F(1/2+σ)|² ≤ E∫_T 1_{G(t)}|F(1/2+σ+it)|² dt`.  The Rademacher
counterpart of `RMF.exists_le_integral_restricted_normSq_of_top`, and the input of
`RMF.exists_le_integral_restricted_normSq_numerator_rademacher`.  Tonelli, the single-height bound
at each `t ∈ T`, and `RMF.IsRademacherRMF.integral_normSq_shiftLine_eq`. -/
theorem exists_le_integral_restricted_normSq_rademacher_of_top :
    ∃ (D₀ : ℕ) (a₀ α Bs Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < α ∧ blockSlope 125 ≤ Bs ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 < 1 / 2 + σ →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          a₀ ≤ a → MeasurableSet T → volume T ≠ ⊤ →
          (∀ t ∈ T, 0 < 2 * t
            ∧ (2 * t) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10))
            ∧ Tsh ≤ 2 * t * Real.exp (harperOffset D x)) →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
                * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - Bs * j) (fun j => a + j + hf j))
                  (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν := by
  obtain ⟨D₀, a₀, α, Bs, Tsh, c, hD₀, hα, hBs, hTsh, hcpos, H⟩ :=
    exists_le_setIntegral_restricted_normSq_rademacher_of_top
  refine ⟨D₀, a₀, α, Bs, Tsh, c, hD₀, hα, hBs, hTsh, hcpos, ?_⟩
  intro D hDD d
  obtain ⟨x₀, H⟩ := H D hDD d
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ a η T hf hx hσ0 hσ hη ha hT hTfin hheight hhf
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set n : ℕ := harperBlockCount D x - d with hndef
  set L : ℝ → Set Ω' := fun t => barrierEvent
    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) n
    (fun j => -a - Bs * j) (fun j => a + j + hf j) with hLdef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hLmeas : ∀ t, MeasurableSet (L t) := fun t =>
    measurableSet_barrierEvent (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hYm p)) _ _ _
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    rw [hLdef, hgdef]
    exact integrable_uncurry_indicator_normSq_rademacher hY y hσ0
      (fun t => barrierEvent
        (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) n
        (fun j => -a - Bs * j) (fun j => a + j + hf j))
      (fun t => measurableSet_barrierEvent (fun m => Finset.measurable_sum _ fun p _ =>
        (measurable_localLogAdd _).comp (hYm p)) n
        (fun j => -a - Bs * j) (fun j => a + j + hf j))
      (measurableSet_prod_barrierEventAdd hY (harperOffset D x) σ n
        (fun j => -a - Bs * j) (fun j => a + j + hf j)) hTfin
  rw [integral_integral_swap hInt]
  have hsre : ∀ t : ℝ, (0 : ℝ) < (shiftLine σ t).re := by
    intro t
    rw [re_shiftLine]
    exact hσ0
  have hper : ∀ t ∈ T, α * min 1 (a / Real.sqrt (n : ℝ)) * (∫ ω, g 0 ω ∂ν)
      ≤ ∫ ω, Set.indicator (L t) (g t) ω ∂ν := by
    intro t ht
    obtain ⟨ht0, htsq, htT⟩ := hheight t ht
    have h := H Ω' Y ν hY x σ a η (shiftLine σ t) hf hx (re_shiftLine σ t) (hsre t) hσ hη
      (by simpa [shiftLine] using ht0) (by simpa [shiftLine] using htsq)
      (by simpa [shiftLine] using htT) ha hhf
    rw [hf'.integral_normSq_shiftLine_eq y (σ := σ) 0 t, integral_indicator (hLmeas t)]
    exact h
  exact le_integral_indicator_of_per_height hT hTfin hInt hper

end RMF
