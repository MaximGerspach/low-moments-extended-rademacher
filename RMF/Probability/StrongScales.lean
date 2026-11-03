/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.StrongBarrier
import RMF.Probability.RademacherRestrictedFirstMoment

/-!
# Harper's scales and the restricted first moment, at Harper's height range

The Rademacher free-start barrier at Harper's scales, and the two first-moment bounds built on it,
with the height condition `τ² ≤ e^ϑ` replaced by `τ² ≤ exp((c/2)·e^{ϑ/10})` at
`ϑ = RMF.harperOffset D x`.  `Probability/StrongBarrier.lean` carries the same condition through
Harper's Proposition 6; the proofs here thread the condition and the rate `c` through the
arguments at `τ² ≤ e^ϑ`.

## Main results

* `RMF.exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop_wide`
* `RMF.exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop_wide`
* `RMF.exists_integral_restricted_normSq_le_rademacher_of_offset_of_drop_wide`
* `RMF.harperWindowLevel` and `RMF.harperDwExp`, the offset this condition needs on a window
  `(w, w+1]`, with their block-count and threshold lemmas -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The two Rademacher barrier slopes

`RMF.exists_const_proposition5_rademacher_of_cutoff_wide` (Harper's Proposition 6) exports a slope
`B ≥ 20` whose value is `RMF.blockSlopeAdd Kd 125`; Harper's Proposition 7 for the Rademacher RMF,
`RMF.exists_proposition7_upper_rademacher`, takes any slope `Bs ≥ RMF.blockSlope 125`.
Paley–Zygmund needs the numerator's barrier event inside the denominator's, and a steeper lower
boundary is a bigger event; `RMF.exists_const_proposition5_harper_rademacher_of_top_slope` puts
the numerator at the slope `max (RMF.blockSlope 125) B_s`, which the denominator accepts. -/

/-- **The free-start barrier at Harper's scales, at his height range.**  The mirror of
`RMF.exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop`. -/
theorem exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop_wide :
    ∃ (D₀ n₀ : ℕ) (x₀ a₀ C B Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < C ∧ 20 ≤ B ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (D r d : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10)) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x - d → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - d - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ν)
                {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, C, B, Tsh, c, hC, hB, hTsh, hcpos, H⟩ :=
    exists_const_freeStart_barrier_le_rademacher_of_cutoff_wide
  refine ⟨⌈ϑ₀⌉₊ + 5, n₀, Real.exp 3, a₀, C, B, Tsh, c, by omega, hC, hB, hTsh, hcpos, ?_⟩
  intro Ω' _ Y ν hY x σ a η D r d s hf hx hD₀ hDlog hres hspos hσ hη hτ0 hτsq hT ha ha1 hr1
    hrn hra hn₀ hhf
  have hx1 : 1 < x := by
    have h1 : (1 : ℝ) < Real.exp 3 := by
      linarith [Real.add_one_le_exp (3 : ℝ)]
    linarith
  have hϑ : ϑ₀ ≤ harperOffset D x := by
    refine le_harperOffset_of_le x ?_
    have hD₀' : ((⌈ϑ₀⌉₊ + 5 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD₀
    have := le_ceil_add_sub_one ϑ₀ 5 (by norm_num)
    linarith
  have hdc : d ≤ harperBlockCount D x := by omega
  have hσ' : |σ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x - d + 1)) ≤ 1 / 10 := by
    refine sigma_le_tenth_of_drop hη hdc ?_
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσ
  have hcut : blockCutoff (harperOffset D x) (harperBlockCount D x) = ⌊x⌋₊ + 1 :=
    blockCutoff_harperOffset hx1 hDlog
  have hy : blockCutoff (harperOffset D x) (harperBlockCount D x - d) ≤ ⌊x⌋₊ + 1 :=
    le_of_le_of_eq (blockCutoff_mono _ (Nat.sub_le _ _)) hcut
  exact H Ω' Y ν hY (harperOffset D x) σ a (harperBlockCount D x - d) r (⌊x⌋₊ + 1) s hf hϑ hy
    hres hspos hσ' hτ0 hτsq hT ha ha1 hn₀ hr1 hrn hra hhf

/-- **The join's upper half, with the offset as an input and a drop, at Harper's height range.**
The mirror of `RMF.exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop`. -/
theorem exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop_wide :
    ∃ (D₀ n₀ : ℕ) (x₀ a₀ A B Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (D r d : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im →
          (2 * s.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10)) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x - d → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - d - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω in {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)},
                ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν)
              ≤ A * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r))
                * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  obtain ⟨D₀, n₀, x₀, a₀, A, B, Tsh, c, hD₀, hA, hB, hTsh, hcpos, H⟩ :=
    exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop_wide
  refine ⟨D₀, n₀, x₀, a₀, A, B, Tsh, c, hD₀, hA, hB, hTsh, hcpos, ?_⟩
  intro Ω' _ Y ν hY x σ a η D r d s hf hx hDD hDlog hres hs hσ hη hτ0 hτsq hT ha ha1 hr1
    hrn hra hn₀ hhf
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hXmeas : ∀ m, Measurable fun ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := fun m =>
    Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)
  have hAm : MeasurableSet {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
        ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)} :=
    measurableSet_freeStartBarrier hXmeas _ _ _ _
  have hprop := H Ω' Y ν hY x σ a η D r d s hf hx hDD hDlog hres hs hσ hη hτ0 hτsq hT ha ha1
    hr1 hrn hra hn₀ hhf
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  rw [hf'.setIntegral_normSq_eq (⌊x⌋₊ + 1) hs hAm]
  exact mul_le_mul_of_nonneg_right hprop hZ0

/-- **The join's upper half, integrated over the heights, at Harper's height range**, with the
height condition `(2t)² ≤ exp((c/2)·exp(harperOffset D x / 10))` asked for every `t ∈ T`. -/
theorem exists_integral_restricted_normSq_le_rademacher_of_offset_of_drop_wide :
    ∃ (D₀ n₀ : ℕ) (x₀ a₀ A B Tsh c : ℝ),
      4 ≤ D₀ ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧ 0 < c ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (D r d : ℕ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          0 < 1 / 2 + σ → |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x - d → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - d - r →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ t ∈ T, 0 < 2 * t
            ∧ (2 * t) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D x / 10))
            ∧ Tsh ≤ 2 * t * Real.exp (harperOffset D x)) →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, (∫ t in T, Set.indicator {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)}
                (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
              ≤ (volume T).toReal
                  * (A * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)))
                * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν := by
  obtain ⟨D₀, n₀, x₀, a₀, A, B, Tsh, c, hD₀, hA, hB, hTsh, hcpos, H⟩ :=
    exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop_wide
  refine ⟨D₀, n₀, x₀, a₀, A, B, Tsh, c, hD₀, hA, hB, hTsh, hcpos, ?_⟩
  intro Ω' _ Y ν hY x σ a η D r d T hf hx hDD hDlog hσ0 hσ hη ha ha1 hr1 hrn hra hn₀ hT
    hTfin hheight hhf
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set n : ℕ := harperBlockCount D x - d with hndef
  set L : ℝ → Set Ω' := fun t => {ω | ∀ j, r ≤ j → j ≤ n →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)} with hLdef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hLmeas : ∀ t, MeasurableSet (L t) := fun t =>
    measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hYm p)) _ _ _ _
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict T)) := by
    rw [hLdef, hgdef]
    exact integrable_uncurry_indicator_normSq_rademacher hY y hσ0
      (fun t => {ω | ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
            (Y ((p : Nat.Primes) : ℕ) ω)) j ω
          ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)})
      (fun t => measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
        (measurable_localLogAdd _).comp (hYm p)) _ _ _ _)
      (measurableSet_freeStartBarrierAdd_uncurry hYm σ _ _ _ _ _) hTfin
  rw [integral_integral_swap hInt]
  have hsre : ∀ t : ℝ, (0 : ℝ) < (shiftLine σ t).re := by
    intro t
    rw [re_shiftLine]
    exact hσ0
  have hper : ∀ t ∈ T, (∫ ω, Set.indicator (L t) (g t) ω ∂ν)
      ≤ A * min 1 (a / Real.sqrt ((n : ℝ) - r)) * ∫ ω, g 0 ω ∂ν := by
    intro t ht
    obtain ⟨ht0, htsq, htT⟩ := hheight t ht
    have h := H Ω' Y ν hY x σ a η D r d (shiftLine σ t) hf hx hDD hDlog (re_shiftLine σ t)
      (hsre t) hσ hη (by simpa [shiftLine] using ht0) (by simpa [shiftLine] using htsq)
      (by simpa [shiftLine] using htT) ha ha1 hr1 hrn hra hn₀ hhf
    rw [hf'.integral_normSq_shiftLine_eq y (σ := σ) 0 t, integral_indicator (hLmeas t)]
    exact h
  exact integral_indicator_le_of_per_height hT hTfin hInt hper

/-! ### The window offset at Harper's height range

The condition `(2t)² ≤ exp((c/2)·exp(harperOffset D x / 10))` holds on the window `(w, w+1]` at
the offset `RMF.harperDwExp D₀ c w`, whose level `RMF.harperWindowLevel c w` is
`10·log((4/c)·log(2(w+1)))`, doubly logarithmic in the height. -/

/-- **The window level** `max(0, 10·log((4/c)·log(2(w+1))))`.  For `0 < c`, `0 ≤ w` and `1 ≤ D₀`,
`(2t)² ≤ exp((c/2)·exp(harperOffset D x / 10))` holds for `0 < t ≤ w + 1` at
`D = D₀ + ⌈harperWindowLevel c w⌉₊` (`RMF.sq_two_mul_le_exp_harperOffset_harperDwExp`).  The
`max 0` acts when `(4/c)·log(2(w+1)) < 1`. -/
noncomputable def harperWindowLevel (c w : ℝ) : ℝ :=
  max 0 (10 * Real.log (4 / c * Real.log (2 * (w + 1))))

lemma harperWindowLevel_nonneg (c w : ℝ) : 0 ≤ harperWindowLevel c w := le_max_left _ _

/-- **The window offset** `D₀ + ⌈harperWindowLevel c w⌉₊` at Harper's height range. -/
noncomputable def harperDwExp (D₀ : ℕ) (c w : ℝ) : ℕ := D₀ + ⌈harperWindowLevel c w⌉₊

lemma le_harperDwExp (D₀ : ℕ) (c w : ℝ) : D₀ ≤ harperDwExp D₀ c w := Nat.le_add_right _ _

/-- **`(2t)² ≤ exp((c/2)·exp(harperOffset D x / 10))` for `0 < t ≤ w + 1`, at
`D = harperDwExp D₀ c w`.**  This is the shape the `_wide` chain's `hτsq` asks for.  `1 ≤ D₀`
makes `harperOffset D₀ x ≥ 0`, so the ceiling alone carries the level. -/
lemma sq_two_mul_le_exp_harperOffset_harperDwExp {D₀ : ℕ} (hD₀ : 1 ≤ D₀) {c w t : ℝ}
    (hc : 0 < c) (hw : 0 ≤ w) (ht0 : 0 < t) (ht : t ≤ w + 1) (x : ℝ) :
    (2 * t) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset (harperDwExp D₀ c w) x / 10)) := by
  have hw1 : (0 : ℝ) < 2 * (w + 1) := by linarith
  have hlogw : 0 < Real.log (2 * (w + 1)) := Real.log_pos (by linarith)
  have hA : 0 < 4 / c * Real.log (2 * (w + 1)) := by positivity
  have hD₀R : (1 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD₀
  -- the offset clears the level, hence `10·log A`
  have hθ : harperWindowLevel c w ≤ harperOffset (harperDwExp D₀ c w) x := by
    rw [harperDwExp, harperOffset_add]
    linarith [sub_one_le_harperOffset D₀ x, Nat.le_ceil (harperWindowLevel c w)]
  have hθ' : 10 * Real.log (4 / c * Real.log (2 * (w + 1)))
      ≤ harperOffset (harperDwExp D₀ c w) x := le_trans (le_max_right _ _) hθ
  -- so `e^{θ/10} ≥ A`, and `(c/2)·A` is exactly `2·log(2(w+1))`
  have hexpA : 4 / c * Real.log (2 * (w + 1))
      ≤ Real.exp (harperOffset (harperDwExp D₀ c w) x / 10) := by
    rw [← Real.exp_log hA]
    exact Real.exp_le_exp.2 (by linarith)
  have hkey : 2 * Real.log (2 * (w + 1))
      ≤ c / 2 * Real.exp (harperOffset (harperDwExp D₀ c w) x / 10) := by
    have h := mul_le_mul_of_nonneg_left hexpA (by positivity : (0 : ℝ) ≤ c / 2)
    have hid : c / 2 * (4 / c * Real.log (2 * (w + 1))) = 2 * Real.log (2 * (w + 1)) := by
      field_simp
      ring
    linarith [hid ▸ h]
  have hid : Real.exp (2 * Real.log (2 * (w + 1))) = (2 * (w + 1)) ^ 2 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hw1]
    norm_num
  have hexp : (2 * (w + 1)) ^ 2
      ≤ Real.exp (c / 2 * Real.exp (harperOffset (harperDwExp D₀ c w) x / 10)) := by
    calc (2 * (w + 1)) ^ 2 = Real.exp (2 * Real.log (2 * (w + 1))) := hid.symm
      _ ≤ _ := Real.exp_le_exp.2 hkey
  have hmono : (2 * t) ^ 2 ≤ (2 * (w + 1)) ^ 2 := by nlinarith
  linarith

/-- **The threshold condition `2e^{D₀-1} ≤ 2t·exp(harperOffset D x)` for `1 ≤ w < t`**, at
`D = harperDwExp D₀ c w`.  Only the nonnegativity of the level is used. -/
lemma two_mul_exp_le_mul_exp_harperOffset_harperDwExp {D₀ : ℕ} {c w t : ℝ} (hw : 1 ≤ w)
    (ht : w < t) (x : ℝ) :
    2 * Real.exp ((D₀ : ℝ) - 1) ≤ 2 * t * Real.exp (harperOffset (harperDwExp D₀ c w) x) := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hmono : harperOffset D₀ x ≤ harperOffset (harperDwExp D₀ c w) x := by
    rw [harperDwExp, harperOffset_add]
    linarith [Nat.cast_nonneg (α := ℝ) ⌈harperWindowLevel c w⌉₊]
  have hθ : (D₀ : ℝ) - 1 ≤ harperOffset (harperDwExp D₀ c w) x :=
    le_trans (sub_one_le_harperOffset D₀ x) hmono
  have hexp : Real.exp ((D₀ : ℝ) - 1) ≤ Real.exp (harperOffset (harperDwExp D₀ c w) x) :=
    Real.exp_le_exp.2 hθ
  nlinarith [Real.exp_pos ((D₀ : ℝ) - 1), Real.exp_pos (harperOffset (harperDwExp D₀ c w) x)]

/-- **The level `RMF.harperDwExp` raises by**, bounded.  `RMF.harperWindowLevel` is nonnegative
by construction, so no hypothesis on `w` is needed. -/
lemma harperDwExp_sub_le_of_cut {D₀ : ℕ} {c x w : ℝ}
    (hcut : harperWindowLevel c w ≤ Real.log (Real.log x) / 3) :
    ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ) ≤ Real.log (Real.log x) / 3 + 1 := by
  have hsub : harperDwExp D₀ c w - D₀ = ⌈harperWindowLevel c w⌉₊ := by
    rw [harperDwExp]; omega
  rw [hsub]
  have h := (Nat.ceil_lt_add_one (harperWindowLevel_nonneg c w)).le
  linarith

/-- **The block count at `RMF.harperDwExp`.**  From one threshold on `log log x`, every count
hypothesis holds for every window whose level fits in `log log x / 3`.  Since the level is doubly
logarithmic, that includes windows out to `w ≈ exp((c/4)(log x)^{1/30})`. -/
lemma harper_block_count_of_window_wide {D₀ d n₀ : ℕ} {c x w : ℝ}
    (hcut : harperWindowLevel c w ≤ Real.log (Real.log x) / 3)
    (hΛ : 2 * ((D₀ : ℝ) + (max (2 * d) (n₀ + d) : ℕ) + 2) ≤ Real.log (Real.log x)) :
    D₀ ≤ harperDwExp D₀ c w ∧ (harperDwExp D₀ c w : ℝ) ≤ Real.log (Real.log x)
      ∧ 2 * d ≤ harperBlockCount (harperDwExp D₀ c w) x
      ∧ n₀ ≤ harperBlockCount (harperDwExp D₀ c w) x - d := by
  set L : ℝ := Real.log (Real.log x) with hLdef
  set M : ℕ := max (2 * d) (n₀ + d) with hMdef
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hK : ((⌈harperWindowLevel c w⌉₊ : ℕ) : ℝ) ≤ L / 3 + 1 := by
    have h := (Nat.ceil_lt_add_one (harperWindowLevel_nonneg c w)).le
    linarith
  have hDle : ((harperDwExp D₀ c w : ℕ) : ℝ) ≤ (D₀ : ℝ) + L / 3 + 1 := by
    rw [harperDwExp]
    push_cast
    linarith
  have hfl : L - 1 < (⌊L⌋₊ : ℝ) := Nat.sub_one_lt_floor L
  have hDL : ((harperDwExp D₀ c w : ℕ) : ℝ) ≤ L := by linarith
  have hcount : harperDwExp D₀ c w + M ≤ ⌊L⌋₊ := by
    have h : ((harperDwExp D₀ c w + M : ℕ) : ℝ) ≤ ((⌊L⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  have h2d : 2 * d ≤ M := le_max_left _ _
  have hn₀ : n₀ + d ≤ M := le_max_right _ _
  refine ⟨le_harperDwExp D₀ c w, hDL, ?_, ?_⟩ <;> · simp only [harperBlockCount, ← hLdef]; omega

/-- **The level is monotone in the window.** -/
lemma harperWindowLevel_mono {cr : ℝ} (hcr : 0 < cr) {w₁ w₂ : ℝ} (hw : 0 ≤ w₁) (h : w₁ ≤ w₂) :
    harperWindowLevel cr w₁ ≤ harperWindowLevel cr w₂ := by
  have hl1 : 0 < Real.log (2 * (w₁ + 1)) := Real.log_pos (by linarith)
  have hl2 : Real.log (2 * (w₁ + 1)) ≤ Real.log (2 * (w₂ + 1)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hA1 : 0 < 4 / cr * Real.log (2 * (w₁ + 1)) := by positivity
  have hA : 4 / cr * Real.log (2 * (w₁ + 1)) ≤ 4 / cr * Real.log (2 * (w₂ + 1)) :=
    mul_le_mul_of_nonneg_left hl2 (by positivity)
  have hlog := Real.log_le_log hA1 hA
  exact max_le_max le_rfl (by linarith)

/-- **The window level is at most `L/3` at every polynomial height:**
`harperWindowLevel cr w ≤ L/3` for `0 ≤ w ≤ L^k` and `L ≥ Λ`.  The proof bounds
`ℓog((4/cr)·ℓog(2(w+1))) ≤ 2√((4/cr)(3+2k)·L)` by `ℓog y ≤ 2√y` at both levels. -/
lemma exists_threshold_harperWindowLevel_le (k : ℕ) {cr : ℝ} (hcr : 0 < cr) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ L w : ℝ, Λ ≤ L → 0 ≤ w → w ≤ L ^ k →
      harperWindowLevel cr w ≤ L / 3 := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hc'0 : (0 : ℝ) < 4 / cr := by positivity
  have hB0 : (0 : ℝ) < 4 / cr * (3 + 2 * (k : ℝ)) := by positivity
  have hS0 : (0 : ℝ) ≤ 60 * Real.sqrt (4 / cr * (3 + 2 * (k : ℝ))) := by positivity
  refine ⟨max 1 ((60 * Real.sqrt (4 / cr * (3 + 2 * (k : ℝ)))) ^ 2), le_max_left _ _,
    fun L w hL hw0 hw => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hLS : (60 * Real.sqrt (4 / cr * (3 + 2 * (k : ℝ)))) ^ 2 ≤ L :=
    le_trans (le_max_right _ _) hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hs0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs1 : (1 : ℝ) ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hL1
    rwa [Real.sqrt_one] at h
  have hsL : Real.sqrt L ≤ L := by nlinarith
  have hsS : 60 * Real.sqrt (4 / cr * (3 + 2 * (k : ℝ))) ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hLS
    rwa [Real.sqrt_sq hS0] at h
  -- the inner logarithm, `≤ 3 + 2k√L`
  have hpos : (0 : ℝ) < 2 * (w + 1) := by linarith
  have hA0 : 0 < Real.log (2 * (w + 1)) := Real.log_pos (by linarith)
  have hLk : (1 : ℝ) ≤ L ^ k := one_le_pow₀ hL1
  have hlog : Real.log (2 * (w + 1)) ≤ Real.log (4 * L ^ k) :=
    Real.log_le_log hpos (by linarith)
  have hsplit : Real.log (4 * L ^ k) = Real.log 4 + (k : ℝ) * Real.log L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_mul_sqrt hL0
  have hAle : Real.log (2 * (w + 1)) ≤ 3 + 2 * (k : ℝ) * Real.sqrt L := by
    rw [hsplit] at hlog
    nlinarith [mul_le_mul_of_nonneg_left hlogL hk0]
  -- the outer logarithm, `≤ 2√((4/cr)(3+2k)L)`
  have hM0 : 0 < 4 / cr * Real.log (2 * (w + 1)) := by positivity
  have hML : 4 / cr * Real.log (2 * (w + 1)) ≤ 4 / cr * (3 + 2 * (k : ℝ)) * L := by
    have h1 : 3 + 2 * (k : ℝ) * Real.sqrt L ≤ (3 + 2 * (k : ℝ)) * L := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hAle hc'0.le]
  have hsqrtM : Real.sqrt (4 / cr * Real.log (2 * (w + 1)))
      ≤ Real.sqrt (4 / cr * (3 + 2 * (k : ℝ))) * Real.sqrt L := by
    rw [← Real.sqrt_mul hB0.le]
    exact Real.sqrt_le_sqrt hML
  have hlogM : Real.log (4 / cr * Real.log (2 * (w + 1)))
      ≤ 2 * Real.sqrt (4 / cr * Real.log (2 * (w + 1))) := log_le_two_mul_sqrt hM0
  -- and `20√((4/cr)(3+2k))·√L ≤ (√L/3)·√L = L/3`
  have hstep : 20 * (Real.sqrt (4 / cr * (3 + 2 * (k : ℝ))) * Real.sqrt L) ≤ L / 3 := by
    have hprod := mul_le_mul_of_nonneg_right hsS hs0
    nlinarith
  rw [harperWindowLevel]
  refine max_le (by linarith) ?_
  nlinarith [mul_le_mul_of_nonneg_left hsqrtM (by norm_num : (0 : ℝ) ≤ 20)]

/-- **`harperWindowLevel cr w + 2 ≤ A·(w+1)^{1/8}` for `w ≥ 0`**, with
`A = 10·|ℓog(4/cr)| + 5122`: the bound the `(|n|+1)^{-1/4}` damping needs against the square of
the level.  The proof applies `Real.log_le_rpow_div` at `ε = 1/16` twice, giving
`ℓogℓog(2(w+1)) ≤ 512·(w+1)^{1/8}`. -/
lemma exists_const_harperWindowLevel_add_two_le {cr : ℝ} (hcr : 0 < cr) :
    ∃ A : ℝ, 0 < A ∧ ∀ w : ℝ, 0 ≤ w →
      harperWindowLevel cr w + 2 ≤ A * (w + 1) ^ ((1 : ℝ) / 8) := by
  refine ⟨10 * |Real.log (4 / cr)| + 5122, by positivity, fun w hw => ?_⟩
  have hw1 : (1 : ℝ) ≤ w + 1 := by linarith
  have hu0 : (0 : ℝ) < 2 * (w + 1) := by linarith
  have hlogpos : 0 < Real.log (2 * (w + 1)) := Real.log_pos (by linarith)
  have hc0 : (0 : ℝ) < 4 / cr := by positivity
  -- `ℓog u ≤ 16·u^{1/16}`
  have h1 : Real.log (2 * (w + 1)) ≤ 16 * (2 * (w + 1)) ^ ((1 : ℝ) / 16) := by
    have h := Real.log_le_rpow_div (x := 2 * (w + 1)) (ε := 1 / 16) hu0.le (by norm_num)
    have hid : (2 * (w + 1)) ^ ((1 : ℝ) / 16) / (1 / 16)
        = 16 * (2 * (w + 1)) ^ ((1 : ℝ) / 16) := by ring
    linarith [hid ▸ h]
  -- `ℓogℓog u ≤ 16·(ℓog u)^{1/16}`
  have h2 : Real.log (Real.log (2 * (w + 1)))
      ≤ 16 * (Real.log (2 * (w + 1))) ^ ((1 : ℝ) / 16) := by
    have h := Real.log_le_rpow_div (x := Real.log (2 * (w + 1))) (ε := 1 / 16)
      hlogpos.le (by norm_num)
    have hid : (Real.log (2 * (w + 1))) ^ ((1 : ℝ) / 16) / (1 / 16)
        = 16 * (Real.log (2 * (w + 1))) ^ ((1 : ℝ) / 16) := by ring
    linarith [hid ▸ h]
  -- and `(ℓog u)^{1/16} ≤ 32·(w+1)^{1/8}`
  have h3 : (Real.log (2 * (w + 1))) ^ ((1 : ℝ) / 16)
      ≤ (16 * (2 * (w + 1)) ^ ((1 : ℝ) / 16)) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow hlogpos.le h1 (by norm_num)
  have h4 : (16 * (2 * (w + 1)) ^ ((1 : ℝ) / 16)) ^ ((1 : ℝ) / 16)
      = (16 : ℝ) ^ ((1 : ℝ) / 16) * (2 * (w + 1)) ^ ((1 : ℝ) / 256) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hu0.le _), ← Real.rpow_mul hu0.le]
    norm_num
  have h5 : (16 : ℝ) ^ ((1 : ℝ) / 16) ≤ 16 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16)
      (by norm_num : (1 : ℝ) / 16 ≤ 1)
    rwa [Real.rpow_one] at h
  have h6 : (2 * (w + 1)) ^ ((1 : ℝ) / 256)
      = (2 : ℝ) ^ ((1 : ℝ) / 256) * (w + 1) ^ ((1 : ℝ) / 256) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h7 : (2 : ℝ) ^ ((1 : ℝ) / 256) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : ℝ) / 256 ≤ 1)
    rwa [Real.rpow_one] at h
  have h8 : (w + 1) ^ ((1 : ℝ) / 256) ≤ (w + 1) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
  have h9 : (1 : ℝ) ≤ (w + 1) ^ ((1 : ℝ) / 8) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hw1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rwa [Real.one_rpow] at h
  have h10 : (0 : ℝ) ≤ (2 * (w + 1)) ^ ((1 : ℝ) / 256) := Real.rpow_nonneg hu0.le _
  have h11 : (0 : ℝ) ≤ (w + 1) ^ ((1 : ℝ) / 256) := Real.rpow_nonneg (by linarith) _
  have hchain : Real.log (Real.log (2 * (w + 1))) ≤ 512 * (w + 1) ^ ((1 : ℝ) / 8) := by
    have hA : (Real.log (2 * (w + 1))) ^ ((1 : ℝ) / 16) ≤ 32 * (w + 1) ^ ((1 : ℝ) / 8) := by
      rw [h4, h6] at h3
      nlinarith
    nlinarith
  -- the level itself
  have hsplit : Real.log (4 / cr * Real.log (2 * (w + 1)))
      = Real.log (4 / cr) + Real.log (Real.log (2 * (w + 1))) :=
    Real.log_mul (ne_of_gt hc0) (ne_of_gt hlogpos)
  have habs : Real.log (4 / cr) ≤ |Real.log (4 / cr)| := le_abs_self _
  have hlev : 10 * Real.log (4 / cr * Real.log (2 * (w + 1)))
      ≤ 10 * |Real.log (4 / cr)| + 5120 * (w + 1) ^ ((1 : ℝ) / 8) := by
    rw [hsplit]
    linarith
  have habs0 : (0 : ℝ) ≤ |Real.log (4 / cr)| := abs_nonneg _
  rw [harperWindowLevel]
  have hmax : max 0 (10 * Real.log (4 / cr * Real.log (2 * (w + 1))))
      ≤ 10 * |Real.log (4 / cr)| + 5120 * (w + 1) ^ ((1 : ℝ) / 8) := by
    refine max_le ?_ hlev
    nlinarith
  nlinarith

end RMF
