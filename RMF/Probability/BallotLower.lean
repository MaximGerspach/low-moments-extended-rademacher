/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BarrierSupermartingale
import RMF.Probability.Result1Lower

/-!
# Cauchy–Schwarz on an event, and the survival bound from time `0`

For a Gaussian walk `S_j` and a barrier `g`, let `A_n` be the event that `S_j ≤ g(j)` for every
`j ≤ n` (`RMF.survivalSet`).  This file proves

* **Cauchy–Schwarz** on an event, `E[1_A Y]² ≤ E[1_A Y²] P(A)` (`RMF.sq_integral_indicator_le`);
* **(A1) upper at the Gaussian constant, from time `0`**: `P(A_n) ≤ (Y + c)√(2/(πW_n))` for a
  barrier `g ≤ Y` on `[0, n]`, with `W_n = ∑_{i<n} v_i`
  (`RMF.IsGaussianWalk.measureReal_survival_le_sqrt`), from the sharp survival bound of
  `RMF/Probability/BarrierSupermartingale.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

section Ballot

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **Cauchy–Schwarz on an event**: `E[1_A f]² ≤ E[1_A f²] P(A)`.  From
`0 ≤ E[1_A (P(A) f - E[1_A f])²] = P(A)(P(A) E[1_A f²] - E[1_A f]²)`, and `E[1_A f] = 0` when
`P(A) = 0`. -/
lemma sq_integral_indicator_le [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, A.indicator f ω ∂μ) ^ 2 ≤ (∫ ω, A.indicator (fun ω => f ω ^ 2) ω ∂μ) * μ.real A := by
  set P := μ.real A with hP
  set Φ := ∫ ω, A.indicator f ω ∂μ with hΦ
  set Ψ := ∫ ω, A.indicator (fun ω => f ω ^ 2) ω ∂μ with hΨ
  have hpt : ∀ ω, A.indicator (fun ω => (P * f ω - Φ) ^ 2) ω
      = P ^ 2 * A.indicator (fun ω => f ω ^ 2) ω - 2 * P * Φ * A.indicator f ω
        + Φ ^ 2 * A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        Set.indicator_of_mem hω]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_notMem hω]
      ring
  have hi1 : Integrable (fun ω => P ^ 2 * A.indicator (fun ω => f ω ^ 2) ω) μ :=
    (hf2.indicator hA).const_mul _
  have hi2 : Integrable (fun ω => 2 * P * Φ * A.indicator f ω) μ := (hf.indicator hA).const_mul _
  have hi3 : Integrable (fun ω => Φ ^ 2 * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hA).const_mul _
  have hi12 : Integrable (fun ω => P ^ 2 * A.indicator (fun ω => f ω ^ 2) ω
      - 2 * P * Φ * A.indicator f ω) μ := hi1.sub hi2
  have hone : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = P := integral_indicator_one hA
  have hexp : ∫ ω, A.indicator (fun ω => (P * f ω - Φ) ^ 2) ω ∂μ = P * (P * Ψ - Φ ^ 2) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hi12 hi3,
      integral_sub hi1 hi2, integral_const_mul, integral_const_mul, integral_const_mul, hone]
    ring
  have h0 : 0 ≤ P * (P * Ψ - Φ ^ 2) := by
    rw [← hexp]
    exact integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => sq_nonneg _) ω
  rcases (measureReal_nonneg : (0 : ℝ) ≤ P).lt_or_eq with hPpos | hP0
  · have := (mul_nonneg_iff_of_pos_left hPpos).1 h0
    linarith
  · have hμA : μ A = 0 := (measureReal_eq_zero_iff).1 hP0.symm
    have hΦ0 : Φ = 0 := by
      rw [hΦ, integral_indicator hA]
      exact setIntegral_measure_zero f hμA
    have hP0' : P = 0 := by rw [hP]; exact hP0.symm
    rw [hΦ0, hP0']
    simp

/-- **(A1) upper at the Gaussian constant, from time `0`.**  For a barrier `g ≤ Y` on `[0, n]`,
`Y ≥ 0`, `n ≥ 1`, nonzero variances and `c ≥ √(πv_j/2)`, `c > 0`:
`P(A_n) ≤ (Y + c)√(2/(πW_n))`, `W_n = ∑_{i<n} v_i`.  This is
`RMF.IsGaussianWalk.measureReal_survival_le_integral_gaussOdd` at `m = 0`, where the tube is the
constant `κ_{W_n}(Y + c)`, and `RMF.gaussOdd_le_mul_sqrt`.
`RMF.IsGaussianWalk.measureReal_forall_le_le_sqrt` is the flat-ceiling case with `W_n ≥ nv₋`. -/
theorem IsGaussianWalk.measureReal_survival_le_sqrt (h : IsGaussianWalk G v μ) {g : ℕ → ℝ}
    {Y c : ℝ} (hY : 0 ≤ Y) {n : ℕ} (hn : 1 ≤ n) (hg : ∀ j ≤ n, g j ≤ Y) (hv : ∀ j, v j ≠ 0)
    (hc0 : 0 < c) (hc : ∀ j, √(π * v j / 2) ≤ c) :
    μ.real (survivalSet G g n)
      ≤ (Y + c) * √(2 / (π * ∑ i ∈ Finset.range n, (v i : ℝ))) := by
  have hsurv := h.measureReal_survival_le_integral_gaussOdd (g := g) (Y := Y) (c := c) (m := 0)
    (Nat.zero_le n) (fun j _ hj => hg j hj) hv hc0 hc
  set V : ℝ≥0 := ∑ i ∈ Finset.Ico 0 n, v i with hV
  have hVne : V ≠ 0 := by
    rw [hV]
    intro h0
    exact hv 0 ((Finset.sum_eq_zero_iff.1 h0) 0 (Finset.mem_Ico.2 ⟨le_rfl, hn⟩))
  have hκ0 : 0 ≤ gaussOdd V (Y + c) := gaussOdd_nonneg V (by linarith)
  have hκ := gaussOdd_le_mul_sqrt hVne (show 0 ≤ Y + c by linarith)
  have hfun : (survivalSet G g 0).indicator (fun ω => gaussOdd V (Y - walk G 0 ω + c))
      = (survivalSet G g 0).indicator (fun _ => gaussOdd V (Y + c)) := by
    funext ω
    simp [walk]
  have hint : ∫ ω, (survivalSet G g 0).indicator (fun ω => gaussOdd V (Y - walk G 0 ω + c)) ω ∂μ
      ≤ gaussOdd V (Y + c) := by
    rw [hfun, integral_indicator_const _ (h.measurableSet_survivalSet g 0), smul_eq_mul]
    have hle : μ.real (survivalSet G g 0) ≤ 1 := measureReal_le_one
    nlinarith [measureReal_nonneg (μ := μ) (s := survivalSet G g 0)]
  have hVR : ((V : ℝ≥0) : ℝ) = ∑ i ∈ Finset.range n, (v i : ℝ) := by
    rw [hV, Finset.range_eq_Ico]
    push_cast
    rfl
  calc μ.real (survivalSet G g n)
      ≤ ∫ ω, (survivalSet G g 0).indicator (fun ω => gaussOdd V (Y - walk G 0 ω + c)) ω ∂μ :=
        hsurv
    _ ≤ gaussOdd V (Y + c) := hint
    _ ≤ (Y + c) * √(2 / (π * V)) := hκ
    _ = (Y + c) * √(2 / (π * ∑ i ∈ Finset.range n, (v i : ℝ))) := by rw [hVR]

end Ballot

end RMF
