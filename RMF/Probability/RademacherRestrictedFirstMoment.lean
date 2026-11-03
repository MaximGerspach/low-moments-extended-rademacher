/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherFirstMoment
import RMF.Probability.RademacherHarperScales

/-!
# The restricted first moment, for the Rademacher random multiplicative function

The upper half of the join in `Probability/RestrictedFirstMoment.lean`, for the Rademacher RMF:
on the free-start barrier event `G`, `∫_G |F|² ≤ A·min\{1, a/√(n-r)\}·E|F|²` for the squarefree
Euler product `F`, from the tilt identity `RMF.IsRademacherRMF.setIntegral_normSq_eq` and the
free-start barrier bound.  It is stated at one height, with the offset as an input and with a
tilt drop.  The lower half is `Probability/RademacherRestrictedFirstMomentLower.lean`.

The module imports `Probability/RademacherFirstMoment.lean` and
`Probability/RademacherHarperScales.lean`, neither of which imports the other.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The upper half with the offset as an input

`D ≥ D₀` is free, subject to `(D : ℝ) ≤ \log\log x`, rather than existentially fixed: the chaos
wrapper in `Probability/RademacherChaosFirstMoment.lean` applies the bound at
`D = RMF.harperDt D₀ h`, which moves with the height. -/

/-- **The join's upper half, with the offset as an input and a drop**: the barrier event runs over
`[r, n-d]` and the tilt bound is `|σ|\log x ≤ η` with `10η ≤ e^d`.
`RMF.exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop` followed by
`RMF.IsRademacherRMF.setIntegral_normSq_eq`.  `0 < \Re s` is a hypothesis: at a general `η` it
does not follow from the tilt bound. -/
theorem exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop :
    ∃ (D₀ n₀ : ℕ) (x₀ a₀ A B Tsh : ℝ), 4 ≤ D₀ ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (D r d : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im → (2 * s.im) ^ 2 ≤ Real.exp (harperOffset D x) →
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
  obtain ⟨D₀, n₀, x₀, a₀, A, B, Tsh, hD₀, hA, hB, hTsh, H⟩ :=
    exists_const_freeStart_barrier_harper_le_rademacher_of_offset_of_drop
  refine ⟨D₀, n₀, x₀, a₀, A, B, Tsh, hD₀, hA, hB, hTsh, ?_⟩
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

end RMF
