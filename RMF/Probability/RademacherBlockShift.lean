/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockShift
import RMF.Probability.RademacherWindowComparison

/-!
# The free start, for the Rademacher random multiplicative function

`RMF/Probability/BlockShift.lean` turns Harper's Proposition 5 (Harper, arXiv:1703.06654, §3.2)
into the form the restricted first moment (Hamdan's Proposition 2.1, arXiv:2604.05563) wants: a
barrier constrained only on `[r, n]` rather than from `j = 1`.  Most of its declarations know
nothing about which random multiplicative function is underneath — the block arithmetic
(`RMF.blockScale_add`, `RMF.primeBlockSub_add`, `RMF.blockCutoff_add`), the barrier-event
inclusions (`RMF.freeStart_subset_barrierEvent`, `RMF.shiftedHeight_le`) and
`RMF.walk_blockSum_eq_sum_sdiff` — and those are reused here verbatim.  The free-start wrappers,
which consume Proposition 5, are mirrored here onto
`RMF.exists_const_proposition5_rademacher_of_cutoff`.

## What the height conditions do here

Harper's Proposition 6, the Rademacher analogue (§3.3), carries conditions on the height that
Proposition 5 does not: `2·Im s` must be positive, at most `√(e^ϑ)`, and bounded below by
`Tsh/e^ϑ`.  They **transfer upward for free**: the shift applies the proposition at offset
`ϑ + r`, and `e^ϑ ≤ e^{ϑ+r}` makes both the upper and the lower condition weaker there.  So the
free-start form asks exactly what Proposition 6 asks, at the unshifted offset.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-- **The restricted first moment's probabilistic core, for the Rademacher RMF, with the tilt
cutoff free.**  `y` is the tilt cutoff; `n` and `r` are the range.  The proof applies Proposition 6
at offset `ϑ + r` and range `n - r`, and `RMF.blockCutoff_add` says the cutoff does not move under
that shift, so `RMF.blockCutoff ϑ n ≤ y` transports to the shifted call.  With the cutoff free, a
consumer running the barrier only to `n - d` instantiates rather than restates. -/
theorem exists_const_freeStart_barrier_le_rademacher_of_cutoff :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ C B Tsh : ℝ), 0 < C ∧ 20 ≤ B ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (ϑ σ a : ℝ) (n r y : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → blockCutoff ϑ n ≤ y → s.re = 1 / 2 + σ → 0 < s.re →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 / 10 →
          0 < 2 * s.im → (2 * s.im) ^ 2 ≤ Real.exp ϑ → Tsh ≤ 2 * s.im * Real.exp ϑ →
          a₀ ≤ a → 1 ≤ a → n₀ ≤ n - r → 1 ≤ r → r ≤ n → (r : ℝ) ≤ a / 4 + 1 →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                (y) s ν)
                {ω | ∀ j, r ≤ j → j ≤ n →
                  walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - B * (j : ℝ)) (a + (j : ℝ) + hf j)}).toReal
              ≤ C * min 1 (a / Real.sqrt ((n : ℝ) - r)) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, hα, hA, hB, hTsh, H⟩ :=
    exists_const_proposition5_rademacher_of_cutoff
  have hB0 : (0 : ℝ) < B := by linarith only [hB]
  refine ⟨ϑ₀, n₀, a₀, A * (29 + 2 * B), B, Tsh, by positivity, hB, hTsh, ?_⟩
  intro Ω' _ Y ν hY ϑ σ a n r y s hf hϑ hy hres hspos hσ hτ0 hτsq hT ha₀ ha1 hn₀ hr1 hrn hra hhf
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hY (y) hspos
  set a' := shiftedHeight a B hf r with ha'def
  have hc : (0 : ℝ) ≤ B := by linarith only [hB]
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hscale : blockScale (ϑ + r) (n - r + 1) = blockScale ϑ (n + 1) := by
    rw [← blockScale_add, show n - r + 1 + r = n + 1 from by omega]
  have ha'0 : a ≤ a' := by
    rw [ha'def, shiftedHeight]
    have h1 : (0 : ℝ) ≤ (B + 1) * (r : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ |hf r| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  -- the height conditions weaken at the shifted offset, since `e^ϑ ≤ e^{ϑ+r}`
  have hexpr : Real.exp ϑ ≤ Real.exp (ϑ + (r : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have hp1 : ϑ₀ ≤ ϑ + (r : ℝ) := by linarith
  have hp2 : |σ| * Real.log (blockScale (ϑ + r) (n - r + 1)) ≤ 1 / 10 := by
    rw [hscale]; exact hσ
  have hp3 : a₀ ≤ a' := by linarith
  have hpsq : (2 * s.im) ^ 2 ≤ Real.exp (ϑ + (r : ℝ)) := le_trans hτsq hexpr
  have hpT : Tsh ≤ 2 * s.im * Real.exp (ϑ + (r : ℝ)) :=
    le_trans hT (mul_le_mul_of_nonneg_left hexpr (by linarith))
  have hp4 : ∀ j : ℕ, 1 ≤ j → j ≤ n - r →
      |(fun m : ℕ => 10 * Real.log m) j| ≤ 10 * Real.log j := by
    intro j hj1 _
    have hl : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
    simp only
    rw [abs_of_nonneg (by linarith)]
  have hy' : blockCutoff (ϑ + r) (n - r) ≤ y :=
    le_of_eq_of_le (blockCutoff_add hrn) hy
  have hP5 := (H Ω' Y ν hY (ϑ + r) σ a' (n - r) y s (fun m => 10 * Real.log m)
    hp1 hy' hres hp2 hτ0 hpsq hpT hp3 hn₀ hp4).2
  rw [Nat.cast_sub hrn] at hP5
  -- the shifted walk is the block walk at offset `ϑ + r`
  have hXshift : (fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ (m + r),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω))
      = fun m ω => ∑ p ∈ primeBlockSub (ϑ + r) m,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω) := by
    funext m
    rw [primeBlockSub_add]
  have hsub := freeStart_subset_barrierEvent (X := fun m (ω : Ω') => ∑ p ∈ primeBlockSub ϑ m,
    localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (a := a) (c := B) (hf := hf) hrn hhf
  rw [hXshift] at hsub
  have hmono := measure_mono (μ := tiltedMeasure
    (fun ω => squarefreeExtension fun p => Y p ω) (y) s ν) hsub
  refine le_trans (le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hmono) hP5) ?_
  -- the widened height is `O(a)`, and `min 1 (K x) ≤ K · min 1 x` for `K ≥ 1`
  have hheight : a' ≤ (29 + 2 * B) * a :=
    shiftedHeight_le ha1 hc hr1 hra (hhf r hr1 hrn)
  have hK : (1 : ℝ) ≤ 29 + 2 * B := by linarith
  have hsq : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) - r) := Real.sqrt_nonneg _
  have hdiv : a' / Real.sqrt ((n : ℝ) - r)
      ≤ (29 + 2 * B) * (a / Real.sqrt ((n : ℝ) - r)) := by
    rw [← mul_div_assoc]
    gcongr
  have h1 := min_one_le_mul_min_one hK hdiv
  calc A * min 1 (a' / Real.sqrt ((n : ℝ) - r))
      ≤ A * ((29 + 2 * B) * min 1 (a / Real.sqrt ((n : ℝ) - r))) :=
        mul_le_mul_of_nonneg_left h1 hA.le
    _ = A * (29 + 2 * B) * min 1 (a / Real.sqrt ((n : ℝ) - r)) := by ring

end RMF
