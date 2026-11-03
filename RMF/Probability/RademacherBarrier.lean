/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherChaining
import RMF.Probability.MaximalBarrier

/-!
# The maximal barrier, Rademacher case

The counterpart of `RMF/Probability/MaximalBarrier.lean` (Hamdan's Lemma 2.3), built on the
Rademacher Lemma B.2 (`RMF.IsRademacherRMF.exists_measure_exists_gt_le` and `..._lt_le`).

## Two structural differences

**There is no `_shift`.**  The Steinhaus barrier reaches each subinterval `[kρ, kρ+ρ)` of `[0,1)`
through `RMF.IsSteinhausRMF.exists_measure_exists_gt_le_shift`, whose proof is a rotation by
`p^{-ikρ}`.  Rotation is not a Rademacher symmetry, so both Rademacher tails carry their base
height as a parameter and are applied at `h₀ + kρ` directly.

**The barrier carries a height offset**, where the Steinhaus one is pinned to `Set.Ico (0 : ℝ) 1`.
`RMF.periodisation_upper` shifts each `∫_n^{n+1}` back to `[0,1]` by rotating with `p^{-in}`, a
step the Rademacher law does not allow (`RMF.chaosUnitShift` shifts the abscissa, not the
height); the Rademacher windows stay at their own heights, so the barrier is stated on
`[h₀, h₀+w)`.

## The window length is a parameter, and the bound is proportional to it

The bound carries `w` as a factor, so a union over many windows costs a sum of `w`'s rather than a
count of them.  This costs the hypothesis `e^{−(j+ϑ)} ≤ w`: the partition into intervals of width
`ρ = e^{−(j+ϑ)}` has `N = ⌈w·e^{j+ϑ}⌉` pieces, and `N ≤ 2w·e^{j+ϑ}` needs `w·e^{j+ϑ} ≥ 1`; below
that `N = 1`, and the bound does not scale with `w`.  On the bands `h ∈ [e^{−k}, e^{−(k−1)})`,
where `RMF.harperDt` is constant, `w_k/ρ_k = (e−1)·e^{j + frac + D₀ − 1}` is independent of `k`
and at least `(e−1)e⁸ ≈ 5.1·10³` at the smallest admissible `j` and `D₀`.

## The exponent

The Rademacher Lemma B.2 delivers `exp(a − 2V)` where the Steinhaus barrier consumes `exp(−V²/a)`.
The union over the `N ≈ 2e^{τ+ϑ}` subintervals contributes an `e^{τ+ϑ}`, so the two branches must
beat `τ + (a − 2V)`, not `a − 2V`.  The `exp(−τ)` in
`exp(a − 2V) ≤ exp(C₁)·exp(−τ)·exp(−2A)·exp(−2b)` pays for that union, and the upper branch is
tight (`RMF.barrier_upper_exponent_two_le`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- **The barrier's upper branch at the second-moment tilt:** `τ + (a − 2(A+τ+b)) ≤ C₁ − 2A − 2b`
for `a ≤ τ + C₁`, which is what `RMF.IsRademacherRMF.exists_measure_exists_gt_le` must beat once the
union over the `N ≈ 2e^{τ+ϑ}` subintervals has contributed its `e^{τ+ϑ}`.  The left side is
`a − τ − 2A − 2b`, so the inequality is exactly `a ≤ τ + C₁` and the branch is tight, as
`RMF.barrier_upper_exponent_le` is for the Steinhaus exponent; the union consumes the `exp(−τ)`. -/
lemma barrier_upper_exponent_two_le {a τ A b C₁ : ℝ} (hale : a ≤ τ + C₁) :
    τ + (a - 2 * (A + τ + b)) ≤ C₁ - 2 * A - 2 * b := by
  linarith only [hale]

/-- **The barrier's lower branch at the second-moment tilt:** `τ + (a − 2(20τ − 4a)) ≤ C₁ − 2A − 2b`
at the lower tail's `W = 20τ − 4a`, with the union bound's `τ` included.  The left side is
`9a − 39τ ≤ 9C₁ − 30τ` by `a ≤ τ + C₁`; the right side is at least `C₁ − 10τ` by `A ≤ 4τ` and
`b ≤ τ`; so `8C₁ ≤ 20τ` suffices, and `8C₁ ≤ τ` gives it with a factor `20` to spare. -/
lemma barrier_lower_exponent_two_le {a τ A b C₁ : ℝ} (hC₁ : 1 ≤ C₁) (hτ8 : 8 * C₁ ≤ τ)
    (hale : a ≤ τ + C₁) (hA : A ≤ 4 * τ) (hb : b ≤ τ) :
    τ + (a - 2 * (20 * τ - 4 * a)) ≤ C₁ - 2 * A - 2 * b := by
  linarith only [hC₁, hτ8, hale, hA, hb]

/-- **The index bound at a shift of either sign**, `δ ≥ -1/12` (the chaining tails accept any
`σ₀ > 1/3` and are read at `σ₀ = 5/12`), on a window `[h₀, h₀+w)` with `w ≥ e^{-(j+ϑ)}`, and with
the `log p`-weighted prime sum allowed a factor `e²`, which the mesh bound `ρ·∑ ≤ Λ = Δ + 40`
absorbs.  To the left of `½` the prime sums grow termwise by `p^{-2δ} ≤ e²` once `|δ|·log x ≤ 1`. -/
theorem IsRademacherRMF.exists_const_measureReal_index_le_of_le_signed {Ω : Type*}
    [MeasurableSpace Ω] (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (ϑ A b c δ h₀ w : ℝ) (j : ℕ), 1 ≤ ϑ → 0 ≤ A → 0 ≤ b → 20 ≤ c → -(1 / 12) ≤ δ →
        (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ →
        (j : ℝ) - Δ ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) →
        (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
            ≤ Real.exp 2 * Real.exp ((j : ℝ) + ϑ) + Δ →
        C ≤ (j : ℝ) → A ≤ 4 * (j : ℝ) → b ≤ (j : ℝ) →
        Real.exp (-((j : ℝ) + ϑ)) ≤ w →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
              Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
                  (heightLine (1 / 2 + δ) h) ω‖
                ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b)}
            ≤ C * w * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b)) := by
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Δ + 40 := ⟨_, rfl⟩
  have hΛ1 : (1 : ℝ) ≤ Λ := by rw [hΛdef]; linarith
  obtain ⟨Cu, hCu, Hu⟩ := IsRademacherRMF.exists_measure_exists_gt_le
    (Ω := Ω) (σ₀ := 5 / 12) (Λ := Λ) (by norm_num) hΛ1
  obtain ⟨Cl, hCl, Hl⟩ := IsRademacherRMF.exists_measure_exists_lt_le
    (Ω := Ω) (σ₀ := 5 / 12) (Λ := Λ) (by norm_num) hΛ1
  refine ⟨max (8 * Δ) (2 * (Cu + Cl) * Real.exp Δ), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (0 : ℝ) < 8 * Δ) (le_max_left _ _)
  intro f μ hf ϑ A b c δ h₀ w j hϑ hA0 hb0 hc hδ0 hupA hlowA hP hτC hA hb hw
  have hδσ : (5 : ℝ) / 12 ≤ 1 / 2 + δ := by linarith
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  haveI := hX.isProbabilityMeasure
  set τ := (j : ℝ) with hτdef
  have hτ8 : 8 * Δ ≤ τ := le_trans (le_max_left _ _) hτC
  have hτ0 : (0 : ℝ) < τ := by linarith
  set a := ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
    (p : ℝ) ^ (-2 * (1 / 2 + δ)) with hadef
  clear_value τ a
  have hale : a ≤ τ + Δ := by linarith
  have hage : τ - Δ ≤ a := by linarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  -- the partition of `[h₀, h₀+w)` into intervals of width `ρ = e^{-(τ+ϑ)}`
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = Real.exp (-(τ + ϑ)) := ⟨_, rfl⟩
  have hρ0 : (0 : ℝ) < ρ := by rw [hρdef]; exact Real.exp_pos _
  have hρinv : Real.exp (τ + ϑ) * ρ = 1 := by
    rw [hρdef, ← Real.exp_add]
    simp
  -- `hw` says the window is at least one interval wide, which is exactly `1 ≤ wE`
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le (Real.exp_pos _) hw
  have hwE : (1 : ℝ) ≤ w * Real.exp (τ + ϑ) := by
    have h := mul_le_mul_of_nonneg_right hw (Real.exp_pos (τ + ϑ)).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈w * Real.exp (τ + ϑ)⌉₊ := ⟨_, rfl⟩
  have hNge : w * Real.exp (τ + ϑ) ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * (w * Real.exp (τ + ϑ)) := by
    rw [hNdef]
    have hce := Nat.ceil_lt_add_one (by linarith only [hwE] : (0 : ℝ) ≤ w * Real.exp (τ + ϑ))
    linarith only [hce, hwE]
  have hNρ : w ≤ (N : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hNge hρ0.le
    have he : w * Real.exp (τ + ϑ) * ρ = w := by rw [mul_assoc, hρinv, mul_one]
    linarith only [h, he]
  -- Lemma B.2's three hypotheses, at every interval
  have hrP : ρ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Λ := by
    have h1 := mul_le_mul_of_nonneg_left hP hρ0.le
    have h2 : ρ * (Real.exp 2 * Real.exp (τ + ϑ) + Δ) = Real.exp 2 + ρ * Δ := by
      rw [mul_add, show ρ * (Real.exp 2 * Real.exp (τ + ϑ))
        = Real.exp 2 * (Real.exp (τ + ϑ) * ρ) by ring, hρinv, mul_one]
    have he2 : Real.exp 2 ≤ 8 := by
      have h1 := Real.exp_one_lt_d9
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 : ℝ)]
    have hρ1 : ρ ≤ 1 := by
      rw [hρdef, Real.exp_le_one_iff]
      linarith
    have h3 : ρ * Δ ≤ Δ := by nlinarith only [hρ1, hρ0, hΔ]
    rw [hΛdef]
    linarith
  have h41 : (41 : ℝ) ≤ Λ := by rw [hΛdef]; linarith
  have h78 : 7 * τ / 8 ≤ a := by linarith
  have hbig : (41 : ℝ) * (7 * τ / 8) ≤ Λ * a :=
    mul_le_mul h41 h78 (by linarith) (by linarith)
  have hVΛ : A + τ + b ≤ Λ * a := by linarith
  have hWΛ : 20 * τ - 4 * a ≤ Λ * a := by linarith
  have hW0 : (0 : ℝ) ≤ 20 * τ - 4 * a := by linarith
  have hV0 : (0 : ℝ) ≤ A + τ + b := by linarith
  have ha1' : (1 : ℝ) ≤ ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ)) := hadef ▸ ha1
  have hVΛ' : A + τ + b ≤ Λ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hVΛ
  have hWΛ' : 20 * τ - 4 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ)))
      ≤ Λ * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hWΛ
  have hW0' : (0 : ℝ) ≤ 20 * τ
      - 4 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
      (p : ℝ) ^ (-2 * (1 / 2 + δ))) := hadef ▸ hW0
  -- the two exponents, against the entropy of the partition
  have hexpU : Real.exp (τ + ϑ) * Real.exp (a - 2 * (A + τ + b))
      ≤ Real.exp ϑ * (Real.exp Δ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_upper_exponent_two_le (τ := τ) (A := A) (b := b) (a := a) (C₁ := Δ) hale
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith only [hkey])
  have hexpL : Real.exp (τ + ϑ) * Real.exp (a - 2 * (20 * τ - 4 * a))
      ≤ Real.exp ϑ * (Real.exp Δ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) := by
    have hkey := barrier_lower_exponent_two_le (τ := τ) (A := A) (b := b) (a := a) (C₁ := Δ)
      hΔ hτ8 hale hA hb
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith only [hkey])
  -- the two families of events, one per interval, based at `h₀`
  obtain ⟨Eup, hEup⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico (h₀ + (k : ℝ) * ρ) (h₀ + (k : ℝ) * ρ + ρ),
        A + τ + b < Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  obtain ⟨Elo, hElo⟩ : ∃ E : ℕ → Set Ω, E = fun k : ℕ =>
      {ω | ∃ h ∈ Set.Ico (h₀ + (k : ℝ) * ρ) (h₀ + (k : ℝ) * ρ + ρ),
        20 * τ - 4 * a + 4 * a < -Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (⌊blockScale ϑ 0⌋₊ + 1)
          (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖} := ⟨_, rfl⟩
  have hboundU : μ.real (⋃ k ∈ Finset.range N, Eup k)
      ≤ (N : ℝ) * (Cu * Real.exp (a - 2 * (A + τ + b))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Eup k) ≤ Cu * Real.exp (a - 2 * (A + τ + b)) := by
      intro k _
      have h := Hu _ μ hf (1 / 2 + δ) (A + τ + b) ρ (h₀ + (k : ℝ) * ρ)
        (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hV0 ha1' hVΛ' hrP
      rw [← hadef] at h
      simp only [hEup]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hboundL : μ.real (⋃ k ∈ Finset.range N, Elo k)
      ≤ (N : ℝ) * (Cl * Real.exp (a - 2 * (20 * τ - 4 * a))) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range N,
        μ.real (Elo k) ≤ Cl * Real.exp (a - 2 * (20 * τ - 4 * a)) := by
      intro k _
      have h := Hl _ μ hf (1 / 2 + δ)
        (20 * τ - 4 * (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 + δ)))) ρ (h₀ + (k : ℝ) * ρ) (⌊blockScale ϑ 0⌋₊ + 1)
        (⌊blockScale ϑ j⌋₊ + 1) hδσ hρ0 hW0' ha1' hWΛ' hrP
      rw [← hadef] at h
      simp only [hElo]
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the failure on this window is covered by the two families
  have hsub : {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
      Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1) (heightLine (1 / 2 + δ) h) ω‖
        ∉ Set.Icc (-A - c * τ) (A + τ + b)}
      ⊆ (⋃ k ∈ Finset.range N, Eup k) ∪ (⋃ k ∈ Finset.range N, Elo k) := by
    rintro ω ⟨h, hh, hnot⟩
    simp only [Set.mem_Ico] at hh
    obtain ⟨k, hkN, hk⟩ := exists_lt_mem_Ico_of_lt (h := h - h₀) hρ0
      (by linarith only [hh.1]) (by linarith only [hh.2]) hNρ
    simp only [Set.mem_Ico] at hk
    have hk' : h ∈ Set.Ico (h₀ + (k : ℝ) * ρ) (h₀ + (k : ℝ) * ρ + ρ) := by
      simp only [Set.mem_Ico]
      exact ⟨by linarith only [hk.1], by linarith only [hk.2]⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlt | hgt
    · refine Or.inr (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hElo]
      have hct : 20 * τ ≤ c * τ := mul_le_mul_of_nonneg_right hc hτ0.le
      exact ⟨h, hk', by linarith only [hlt, hct, hA0]⟩
    · refine Or.inl (Set.mem_biUnion (Finset.mem_range.2 hkN) ?_)
      simp only [hEup]
      exact ⟨h, hk', hgt⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  have hU : (N : ℝ) * (Cu * Real.exp (a - 2 * (A + τ + b)))
      ≤ 2 * Cu * (w * (Real.exp ϑ * (Real.exp Δ
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by
    have h1 : (N : ℝ) * Real.exp (a - 2 * (A + τ + b))
        ≤ 2 * (w * (Real.exp (τ + ϑ) * Real.exp (a - 2 * (A + τ + b)))) := by
      have h := mul_le_mul_of_nonneg_right hNle (Real.exp_pos (a - 2 * (A + τ + b))).le
      linarith only [h]
    calc (N : ℝ) * (Cu * Real.exp (a - 2 * (A + τ + b)))
        = Cu * ((N : ℝ) * Real.exp (a - 2 * (A + τ + b))) := by ring
      _ ≤ Cu * (2 * (w * (Real.exp (τ + ϑ) * Real.exp (a - 2 * (A + τ + b))))) :=
          mul_le_mul_of_nonneg_left h1 hCu.le
      _ ≤ Cu * (2 * (w * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexpU hw0.le) (by norm_num)) hCu.le
      _ = 2 * Cu * (w * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by ring
  have hL : (N : ℝ) * (Cl * Real.exp (a - 2 * (20 * τ - 4 * a)))
      ≤ 2 * Cl * (w * (Real.exp ϑ * (Real.exp Δ
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by
    have h1 : (N : ℝ) * Real.exp (a - 2 * (20 * τ - 4 * a))
        ≤ 2 * (w * (Real.exp (τ + ϑ) * Real.exp (a - 2 * (20 * τ - 4 * a)))) := by
      have h := mul_le_mul_of_nonneg_right hNle (Real.exp_pos (a - 2 * (20 * τ - 4 * a))).le
      linarith only [h]
    calc (N : ℝ) * (Cl * Real.exp (a - 2 * (20 * τ - 4 * a)))
        = Cl * ((N : ℝ) * Real.exp (a - 2 * (20 * τ - 4 * a))) := by ring
      _ ≤ Cl * (2 * (w * (Real.exp (τ + ϑ) * Real.exp (a - 2 * (20 * τ - 4 * a))))) :=
          mul_le_mul_of_nonneg_left h1 hCl.le
      _ ≤ Cl * (2 * (w * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexpL hw0.le) (by norm_num)) hCl.le
      _ = 2 * Cl * (w * (Real.exp ϑ * (Real.exp Δ
            * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))))) := by ring
  have hmax : 2 * (Cu + Cl) * Real.exp Δ
      ≤ max (8 * Δ) (2 * (Cu + Cl) * Real.exp Δ) := le_max_right _ _
  -- the whole bound now carries `w`, so factor it out with the exponentials and
  -- compare the scalars; no division, hence no `field_simp`
  have hProd : (0 : ℝ) ≤ w * (Real.exp ϑ * (Real.exp (-(2 * A)) * Real.exp (-(2 * b)))) :=
    (mul_pos hw0 (by positivity)).le
  have hcoef : (2 * Cu + 2 * Cl) * Real.exp Δ
      ≤ max (8 * Δ) (2 * (Cu + Cl) * Real.exp Δ) := by linarith only [hmax]
  have hkey : 2 * Cu * (w * (Real.exp ϑ * (Real.exp Δ
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))
      + 2 * Cl * (w * (Real.exp ϑ * (Real.exp Δ
        * (Real.exp (-(2 * A)) * Real.exp (-(2 * b))))))
      ≤ max (8 * Δ) (2 * (Cu + Cl) * Real.exp Δ) * w * Real.exp ϑ * Real.exp (-(2 * A))
        * Real.exp (-(2 * b)) := by
    have h := mul_le_mul_of_nonneg_right hcoef hProd
    linarith only [h]
  linarith only [hboundU, hboundL, hU, hL, hkey]

/-- **Hamdan's Lemma 2.3, Rademacher case, at a shift of either sign.**  The barrier bound for
`δ ≥ -1/12`, with the `log p`-weighted prime sum allowed a factor `e²`, passed down to
`RMF.IsRademacherRMF.exists_const_measureReal_index_le_of_le_signed`. -/
theorem IsRademacherRMF.exists_const_measure_exists_barrier_le_of_le_signed {Ω : Type*}
    [MeasurableSpace Ω] (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (ϑ A c δ h₀ w : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → 0 ≤ A → 20 ≤ c → -(1 / 12) ≤ δ →
        C ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
            ≤ Real.exp 2 * Real.exp ((j : ℝ) + ϑ) + Δ) →
        Real.exp (-((r : ℝ) + ϑ)) ≤ w →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
              Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
                  (heightLine (1 / 2 + δ) h) ω‖
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C * w * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  obtain ⟨C₂, hC₂, H⟩ := IsRademacherRMF.exists_const_measureReal_index_le_of_le_signed
    (Ω := Ω) Δ hΔ
  refine ⟨C₂, hC₂, ?_⟩
  intro f μ hf ϑ A c δ h₀ w r n b hϑ hA0 hc hδ0 hC₂r hb0 hble h4 hup hlow hlogP hw
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω, E = fun j : ℕ =>
      {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w),
        Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
            (heightLine (1 / 2 + δ) h) ω‖
          ∉ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := ⟨_, rfl⟩
  have hsub : {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
      Real.log ‖randomEulerProductIco f (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
          (heightLine (1 / 2 + δ) h) ω‖
        ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      ⊆ ⋃ j ∈ Finset.Icc r n, E j := by
    rintro ω ⟨h, hh, hnot⟩
    push Not at hnot
    obtain ⟨j, hjr, hjn, hj⟩ := hnot
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hjr, hjn⟩) ?_
    simp only [hE]
    exact ⟨h, hh, hj⟩
  have hlast : ∑ j ∈ Finset.Icc r n,
        C₂ * w * Real.exp ϑ * Real.exp (-(2 * A)) * Real.exp (-(2 * b j))
      = C₂ * w * Real.exp ϑ * Real.exp (-(2 * A))
        * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
    rw [Finset.mul_sum]
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (le_of_eq hlast)
  obtain ⟨hjr, hjn⟩ := Finset.mem_Icc.1 hj
  have hjR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjr
  simp only [hE]
  have hwj : Real.exp (-((j : ℝ) + ϑ)) ≤ w :=
    le_trans (Real.exp_le_exp.2 (by linarith only [hjR])) hw
  exact H f μ hf ϑ A (b j) c δ h₀ w j hϑ hA0 (hb0 j hjr hjn) hc hδ0
    (hup j hjr hjn) (hlow j hjr hjn) (hlogP j hjr hjn) (by linarith only [hC₂r, hjR])
    (h4 j hjr hjn) (hble j hjr hjn) hwj

/-! ### The block walk `RMF.walk`, for the squarefree product

`RademacherChaosMoment` consumes the barrier through `RMF.walk` of the block family, not through
`ℓog‖F^{Ico}‖`.  The Steinhaus bridge `RMF.walk_blockSum_eq_sum_primesIco` names `localLog` in its
statement, as does `RMF.walk_blockSum_eq_sum_sdiff` beneath it, while the squarefree walk is a sum
of `RMF.localLogAdd`.  Both proofs are generic in the summand (`walk_apply`,
`RMF.biUnion_primeBlockSub_eq_sdiff`, `Finset.sum_biUnion` with
`RMF.pairwise_disjoint_primeBlockSub`, then `RMF.primesBelowSub_sdiff` and `RMF.sum_primesIcoSub`),
so one lemma with the summand abstract covers both laws. -/

/-- **The block walk telescopes to a prime sum, for any summand.**

The summand-generic form of `RMF.walk_blockSum_eq_sum_primesIco`, which is stated for `localLog`.
Instantiating at `F p ω = localLog (w p) (X p ω)` gives that lemma back; instantiating at
`localLogAdd` gives what the squarefree walk needs. -/
theorem walk_blockSum_eq_sum_primesIco_of_summand {Ω : Type*} (ϑ : ℝ) (F : ℕ → Ω → ℝ)
    (j : ℕ) (ω : Ω) :
    walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m, F (p : ℕ) ω) j ω
      = ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1), F p ω := by
  classical
  have h1 : walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m, F (p : ℕ) ω) j ω
      = ∑ p ∈ primesBelowSub (⌊blockScale ϑ j⌋₊ + 1) \ primesBelowSub (⌊blockScale ϑ 0⌋₊ + 1),
          F (p : ℕ) ω := by
    rw [walk_apply, ← biUnion_primeBlockSub_eq_sdiff ϑ j]
    refine (Finset.sum_biUnion ?_).symm
    intro a _ b _ hab
    exact pairwise_disjoint_primeBlockSub ϑ hab
  rw [h1, primesBelowSub_sdiff]
  exact sum_primesIcoSub _ _ fun p => F p ω

/-- **Hamdan's Lemma 2.3 for the squarefree block walk, at a shift of either sign.**  As
`RMF.IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le`, with `δ ≥ -1/12` and
the `log p`-weighted prime sum allowed a factor `e²`: the two relaxations of
`RMF.IsRademacherRMF.exists_const_measureReal_index_le_of_le_signed`, passed through. -/
theorem IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le_signed {Ω : Type*}
    [MeasurableSpace Ω] (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (ϑ A c δ h₀ w : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → 0 ≤ A → 20 ≤ c → -(1 / 12) ≤ δ →
        C ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
            ≤ Real.exp 2 * Real.exp ((j : ℝ) + ϑ) + Δ) →
        Real.exp (-((r : ℝ) + ϑ)) ≤ w →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
              walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C * w * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  obtain ⟨C, hC, H⟩ := IsRademacherRMF.exists_const_measure_exists_barrier_le_of_le_signed
    (Ω := Ω) Δ hΔ
  refine ⟨C, hC, ?_⟩
  intro X μ hX ϑ A c δ h₀ w r n b hϑ hA0 hc hδ0 hCr hb0 hble h4 hup hlow hlogP hw
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G =
      {ω | ∀ p ∈ Nat.primesBelow (⌊blockScale ϑ n⌋₊ + 1), ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊blockScale ϑ n⌋₊ + 1)
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hwalk : ∀ ω ∈ G, ∀ (h : ℝ) (j : ℕ), j ≤ n →
      walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
        = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
              (heightLine (1 / 2 + δ) h) ω‖ := by
    intro ω hωG h j hjn
    rw [hGdef] at hωG
    have hjm : ⌊blockScale ϑ j⌋₊ ≤ ⌊blockScale ϑ n⌋₊ :=
      Nat.floor_le_floor (blockScale_mono ϑ hjn)
    have hsub : ∀ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
        ‖X p ω‖ ≤ 1 := by
      intro p hp
      obtain ⟨hpp, -, hp2⟩ := mem_primesIco.1 hp
      exact hωG p (Nat.mem_primesBelow.2 ⟨by omega, hpp⟩)
    rw [walk_blockSum_eq_sum_primesIco_of_summand ϑ
      (fun p ω => localLogAdd ((p : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X p ω)) j ω]
    exact (log_norm_randomEulerProductIco_sqfree_eq
      (by rw [re_heightLine]; linarith) hsub).symm
  have hset : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
              (heightLine (1 / 2 + δ) h) ω‖
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
    ext ω
    constructor
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
    · rintro ⟨hωG, h, hh, hnot⟩
      exact ⟨hωG, h, hh, fun hall => hnot fun j hjr hjn => by
        rw [← hwalk ω hωG h j hjn]; exact hall j hjr hjn⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
        walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
          ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
      = μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
          Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1)
              (heightLine (1 / 2 + δ) h) ω‖
            ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)} := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _, hset,
          ← measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ C * w * Real.exp ϑ * Real.exp (-(2 * A))
          * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) :=
        H _ μ hf ϑ A c δ h₀ w r n b hϑ hA0 hc hδ0 hCr hb0 hble h4 hup hlow hlogP hw

/-- **Hamdan's Lemma 2.3 for the squarefree block walk, at a shifted abscissa and on a window**:
the counterpart of `RMF.IsSteinhausPrimeValues.exists_const_measure_exists_barrier_le_of_le`; the
passage from `ℓog‖F^{Ico}‖` to `RMF.walk` is indifferent to the abscissa and to `h₀`.  The case
`δ ≥ 0` of `RMF.IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le_signed`. -/
theorem IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le {Ω : Type*}
    [MeasurableSpace Ω] (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ∃ C > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (ϑ A c δ h₀ w : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → 0 ≤ A → 20 ≤ c → 0 ≤ δ →
        C ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ) →
        Real.exp (-((r : ℝ) + ϑ)) ≤ w →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + w), ¬ ∀ j, r ≤ j → j ≤ n →
              walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                localLogAdd (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C * w * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j)) := by
  obtain ⟨C, hC, H⟩ := IsRademacherPrimeValues.exists_const_measure_exists_barrier_le_of_le_signed
    (Ω := Ω) Δ hΔ
  refine ⟨C, hC, ?_⟩
  intro X μ hX ϑ A c δ h₀ w r n b hϑ hA0 hc hδ0 hCr hb0 hble h4 hup hlow hlogP hw
  exact H X μ hX ϑ A c δ h₀ w r n b hϑ hA0 hc (by linarith) hCr hb0 hble h4 hup hlow
    (fun j hjr hjn => le_trans (hlogP j hjr hjn)
      (by nlinarith [Real.add_one_le_exp (2 : ℝ), Real.exp_pos ((j : ℝ) + ϑ)])) hw

end RMF
