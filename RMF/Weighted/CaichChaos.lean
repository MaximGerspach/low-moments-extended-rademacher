/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CaichScales
import RMF.Weighted.MesoscopicChaos

/-!
# The chaos over a long range of heights, Rademacher case

`RMF.integral_rpow_dilatedLineIntegral_le_scales_sqfree` leaves the moments `E[S(M)^q]` of the
line mass over `(0, M]` at the dyadic scales.  Over a unit window they are bounded by the
interpolation from the first moment to the `q`-th; over a long range two things change.

* **The bad set is a union over the range.**  Its measure grows linearly in `M`, which the level
  pays for by a raise of `½ log M` — an *additive* shift `E` of every level in the family.
* **So the restricted chaos is `≪ (a + E)/√t`, not `≪ a/√t`.**  The interpolation
  (`RMF.integral_rpow_le_of_goodSets`) converts `a/√t` into its target multiplicatively; with the
  shift that would cost a factor `E ≍ log M`, which the target cannot absorb.

`RMF.integral_rpow_le_of_goodSets_add` is the interpolation with the shift kept additive:

`E[Z^q] ≪ (1 + (1-q)√t)^{-q} + (E/√t)^q`.

Its proof is that of `RMF.integral_rpow_le_of_goodSets`, with the restricted-chaos hypothesis read
at the `a/√t` scale (the caller converts `min{1, a/√(t-r)}`), so the start-level bookkeeping moves
to the caller.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
-- the interpolation's three branches and the level arithmetic, with the shift `E`
/-- **The first-to-`q`-th-moment interpolation, with an additive shift of the levels.**
The mirror of `RMF.integral_rpow_le_of_goodSets` in which the restricted chaos at level `a` is
`≤ C₂(a + E)/√t` instead of `≤ C₂·min{1, a/√(t-⌈a/4⌉)}`, for the levels `a₀ ≤ a ≤ 3√t` the
interpolation reads.  The conclusion keeps the shift additive:
`E[Z^q] ≤ K·((1 + (1-q)√t)^{-q} + (E/√t)^q)`, with `K` explicit in `C₁`, `C₂` and `a₀`. -/
theorem integral_rpow_le_of_goodSets_add {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} {Rst : (ℝ → Set Ω) → Ω → ℝ} {win : Set ℝ}
    {q : ℝ} {t : ℕ} {a₀ C₁ C₂ E : ℝ}
    (hZ0' : ∀ ω, 0 ≤ Z ω) (hZi' : Integrable Z ν)
    (hR0' : ∀ (S : ℝ → Set Ω) (ω : Ω), 0 ≤ Rst S ω)
    (hRi' : ∀ S : ℝ → Set Ω, (∀ h, MeasurableSet (S h)) →
      MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2} → Integrable (Rst S) ν)
    (hdec : ∀ (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ), r ≤ m →
      Z ω ≤ Rst (S r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ win, ω ∉ S j h} (fun _ => (1 : ℝ)) ω * Rst (S (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ win, ω ∉ S m h} (fun _ => (1 : ℝ)) ω * Z ω)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hE : 0 ≤ E)
    (hZmean : (∫ ω, Z ω ∂ν) ≤ C₁)
    (hT2 : ⌈max a₀ 3⌉₊ ^ 2 ≤ t)
    (Gset : ℝ → ℝ → Set Ω)
    (Gmeas : ∀ a h, MeasurableSet (Gset a h))
    (Gunc : ∀ a, MeasurableSet {p : Ω × ℝ | p.1 ∈ Gset a p.2})
    (Gbad : ∀ a, a₀ ≤ a → ν.real {ω | ∃ h ∈ win, ω ∉ Gset a h} ≤ C₂ * Real.exp (-(2 * a)))
    (Gint : ∀ a, a₀ ≤ a → a ≤ 3 * Real.sqrt (t : ℝ) →
      (∫ ω, Rst (Gset a) ω ∂ν) ≤ C₂ * ((a + E) / Real.sqrt (t : ℝ))) :
    (∫ ω, Z ω ^ q ∂ν)
      ≤ (3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
            + max 1 C₂ * max 1 C₁))
          + (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)))
        * ((1 + (1 - q) * Real.sqrt (t : ℝ)) ^ (-q) + (E / Real.sqrt (t : ℝ)) ^ q) := by
  have hKz1 : (1 : ℝ) ≤ max 1 C₁ := le_max_left _ _
  have hKc1 : (1 : ℝ) ≤ max 1 C₂ := le_max_left _ _
  have hKj1 : (1 : ℝ) ≤ max 1 C₂ * (max a₀ 3 + 1) := by
    have h3 : (3 : ℝ) ≤ max a₀ 3 := le_max_right _ _
    nlinarith [hKc1]
  have hKcc : (0 : ℝ) ≤ max 1 C₂ * max 1 C₂ := mul_nonneg (by linarith) (by linarith)
  have hKcz : (0 : ℝ) ≤ max 1 C₂ * max 1 C₁ := mul_nonneg (by linarith) (by linarith)
  obtain ⟨ZZ, hZZ⟩ : ∃ ZZ : Ω → ℝ, ZZ = Z := ⟨_, rfl⟩
  rw [← hZZ]
  have hZ0 : ∀ ω, 0 ≤ ZZ ω := by
    rw [hZZ]; exact hZ0'
  have hZi : Integrable ZZ ν := by
    rw [hZZ]; exact hZi'
  have hZmean0 : (0 : ℝ) ≤ ∫ ω, ZZ ω ∂ν := integral_nonneg hZ0
  have hZmean : (∫ ω, ZZ ω ∂ν) ≤ C₁ := by
    rw [hZZ]; exact hZmean
  have hZpow : (∫ ω, ZZ ω ∂ν) ^ q ≤ max 1 C₁ :=
    le_trans (Real.rpow_le_rpow hZmean0 hZmean hq0) (rpow_le_max_one hC₁ hq0 hq1)
  have hjensen : (∫ ω, ZZ ω ^ q ∂ν) ≤ max 1 C₁ := by
    have hZqi := integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0 hq1
    exact le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall hZ0) hZi hZqi) hZpow
  set st : ℝ := Real.sqrt (t : ℝ) with hstdef
  have hst0 : (0 : ℝ) ≤ st := Real.sqrt_nonneg _
  have hAe0 : (0 : ℝ) ≤ (E / st) ^ q := Real.rpow_nonneg (div_nonneg hE hst0) _
  -- branch 1: `q = 0`, where both sides are constants
  rcases eq_or_lt_of_le hq0 with rfl | hq0'
  · have h1 : (∫ ω, ZZ ω ^ (0 : ℝ) ∂ν) = 1 := by simp
    rw [h1, neg_zero, Real.rpow_zero, Real.rpow_zero]
    linarith
  -- branch 2: the target is bounded below, so an absolute bound suffices
  rcases lt_or_ge ((1 - q) * st) 2 with hLsmall | hL2
  · have htar : (1 : ℝ) / 3 ≤ (1 + (1 - q) * st) ^ (-q) :=
      one_third_le_target hq0 hq1 hLsmall
    have hK3 : 3 * max 1 C₁
        ≤ 3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
            + max 1 C₂ * max 1 C₁))
          + (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)) := by linarith
    have hK0 : (0 : ℝ) ≤ 3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1)
        + 2 * (max 1 C₂ * max 1 C₂) + max 1 C₂ * max 1 C₁))
          + (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)) := by linarith
    have hprod := mul_le_mul hK3 htar (by norm_num) hK0
    have hadd := mul_nonneg hK0 hAe0
    rw [mul_add]
    nlinarith [hjensen]
  -- branch 3: the interpolation
  have h1q : (0 : ℝ) < 1 - q := by
    rcases le_or_gt (1 - q) 0 with h | h
    · exact absurd hL2 (by nlinarith [mul_nonneg (neg_nonneg.2 h) hst0])
    · exact h
  have hq1' : q < 1 := by linarith
  have hL0 : (0 : ℝ) < (1 - q) * st := by linarith
  have hA₀3 : (3 : ℝ) ≤ max a₀ 3 := le_max_right _ _
  have hA₀a : a₀ ≤ max a₀ 3 := le_max_left _ _
  have hA₀st : max a₀ 3 ≤ st := by
    rw [hstdef]
    refine (Real.le_sqrt (by linarith) (Nat.cast_nonneg t)).2 ?_
    have h1 : max a₀ 3 ≤ ((⌈max a₀ 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈max a₀ 3⌉₊ ^ 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hT2
    push_cast at h2
    have h3 : (0 : ℝ) ≤ max a₀ 3 := by linarith
    nlinarith [h1, h2, h3]
  have hst3 : (3 : ℝ) ≤ st := le_trans hA₀3 hA₀st
  have hstpos : (0 : ℝ) < st := by linarith
  -- the geometric family of levels
  set j₀ : ℕ := ⌈max a₀ 3 * (1 - q)⌉₊ with hj₀def
  set KK : ℕ := j₀ + ⌈(1 - q) * st⌉₊ with hKKdef
  set lev : ℕ → ℝ := fun j => (j : ℝ) / (1 - q) with hlevdef
  have hlev0 : ∀ j : ℕ, 0 ≤ lev j := fun j => div_nonneg (Nat.cast_nonneg j) h1q.le
  have hlevmul : ∀ j : ℕ, lev j * (1 - q) = (j : ℝ) := fun j => div_mul_cancel₀ _ h1q.ne'
  have hj₀ge : max a₀ 3 * (1 - q) ≤ (j₀ : ℝ) := Nat.le_ceil _
  have hA₀0 : (0 : ℝ) ≤ max a₀ 3 := by linarith
  have hj₀lt : ((j₀ : ℕ) : ℝ) ≤ max a₀ 3 * (1 - q) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hA₀0 h1q.le)).le
  have hj₀one : ((j₀ : ℕ) : ℝ) ≤ max a₀ 3 + 1 := by
    have h := mul_le_mul_of_nonneg_left (show 1 - q ≤ 1 by linarith) hA₀0
    rw [mul_one] at h
    linarith
  have hKlt : ((KK : ℕ) : ℝ) ≤ ((j₀ : ℕ) : ℝ) + ((1 - q) * st + 1) := by
    rw [hKKdef]
    push_cast
    linarith [(Nat.ceil_lt_add_one hL0.le).le]
  have hKge : (1 - q) * st ≤ ((KK : ℕ) : ℝ) := by
    rw [hKKdef]
    push_cast
    linarith [Nat.le_ceil ((1 - q) * st), Nat.cast_nonneg (α := ℝ) j₀]
  have hlevK : ∀ j : ℕ, j ≤ KK → lev j ≤ 3 * st := fun j hj =>
    level_le_three_sqrt h1q hA₀st hL2 hj₀lt hKlt (by exact_mod_cast hj)
  have ha₀lev : ∀ j : ℕ, j₀ ≤ j → a₀ ≤ lev j := by
    intro j hj
    have h2 : ((j₀ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [hlevdef, le_div_iff₀ h1q]
    linarith [mul_le_mul_of_nonneg_right hA₀a h1q.le, hj₀ge, h2]
  -- the restricted chaos at each level
  obtain ⟨RR, hRR⟩ : ∃ RR : ℕ → Ω → ℝ, RR = fun j => Rst (Gset (lev j)) := ⟨_, rfl⟩
  have hR0 : ∀ (j : ℕ) (ω : Ω), 0 ≤ RR j ω := by
    rw [hRR]; exact fun j ω => hR0' _ ω
  have hRi : ∀ j : ℕ, Integrable (RR j) ν := by
    rw [hRR]
    exact fun j => hRi' _ (fun h => Gmeas (lev j) h) (Gunc (lev j))
  have hRmean0 : ∀ j : ℕ, (0 : ℝ) ≤ ∫ ω, RR j ω ∂ν := fun j => integral_nonneg (hR0 j)
  have hRle : ∀ j : ℕ, j₀ ≤ j → j ≤ KK →
      (∫ ω, RR j ω ∂ν) ≤ C₂ * (j : ℝ) / ((1 - q) * st) + C₂ * (E / st) := by
    intro j hj1 hj2
    have hb := Gint (lev j) (ha₀lev j hj1) (hlevK j hj2)
    rw [hRR]
    refine le_trans hb (le_of_eq ?_)
    rw [hlevdef, add_div, mul_add, div_div, ← mul_div_assoc]
  -- the bad sets, replaced by measurable hulls of the same measure
  choose B hBsub hBmeas hBmeasure using fun j : ℕ => exists_measurable_superset ν
    {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h}
  have hBreal : ∀ j : ℕ, ν.real (B j) = ν.real {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h} := by
    intro j
    rw [measureReal_def, measureReal_def, hBmeasure j]
  -- the pointwise decomposition, on the hulls
  have hpt : ∀ ω, ZZ ω ≤ RR j₀ ω
      + (∑ j ∈ Finset.Ico j₀ KK, Set.indicator (B j) (fun _ => (1 : ℝ)) ω * RR (j + 1) ω)
      + Set.indicator (B KK) (fun _ => (1 : ℝ)) ω * ZZ ω := by
    intro ω
    rw [hZZ, hRR]
    refine le_trans (hdec (fun j => Gset (lev j)) ω j₀ KK (Nat.le_add_right _ _)) ?_
    have hstep : ∀ (j : ℕ) (u : ℝ), 0 ≤ u →
        Set.indicator {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h} (fun _ => (1 : ℝ)) ω * u
          ≤ Set.indicator (B j) (fun _ => (1 : ℝ)) ω * u := by
      intro j u hu
      refine mul_le_mul_of_nonneg_right ?_ hu
      by_cases hm : ω ∈ {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h}
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hBsub j hm)]
      · rw [Set.indicator_of_notMem hm]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.Ico j₀ KK) =>
      hstep j _ (by simpa [hRR] using hR0 (j + 1) ω))
    have htail := hstep KK _ (by simpa [hZZ] using hZ0 ω)
    linarith
  have hmain := integral_rpow_le_of_decomposition hZ0 hR0 hZi hRi hBmeas hq0' hq1' j₀ KK hpt
  -- the three terms
  have hM0 : (0 : ℝ) ≤ ((1 - q) * st) ^ (-q) := Real.rpow_nonneg hL0.le _
  have hsplitq : ∀ u : ℝ, 0 ≤ u → (C₂ * u / ((1 - q) * st) + C₂ * (E / st)) ^ q
      ≤ max 1 C₂ * (u ^ q * ((1 - q) * st) ^ (-q)) + max 1 C₂ * (E / st) ^ q := by
    intro u hu
    have hv : (0 : ℝ) ≤ E / st := div_nonneg hE hst0
    have hu' : (0 : ℝ) ≤ C₂ * u / ((1 - q) * st) := by positivity
    refine le_trans (Real.rpow_add_le_add_rpow hu' (mul_nonneg hC₂.le hv) hq0 hq1)
      (add_le_add ?_ ?_)
    · rw [mul_div_assoc, Real.mul_rpow hC₂.le (div_nonneg hu hL0.le),
        Real.div_rpow hu hL0.le, div_eq_mul_inv, ← Real.rpow_neg hL0.le]
      exact mul_le_mul_of_nonneg_right (rpow_le_max_one hC₂ hq0 hq1)
        (mul_nonneg (Real.rpow_nonneg hu _) hM0)
    · rw [Real.mul_rpow hC₂.le hv]
      exact mul_le_mul_of_nonneg_right (rpow_le_max_one hC₂ hq0 hq1) (Real.rpow_nonneg hv _)
  -- (a) the first term
  have hfirst : (∫ ω, RR j₀ ω ∂ν) ^ q
      ≤ max 1 C₂ * (max a₀ 3 + 1) * ((1 - q) * st) ^ (-q) + max 1 C₂ * (E / st) ^ q := by
    have h1 := Real.rpow_le_rpow (hRmean0 j₀) (hRle j₀ le_rfl (Nat.le_add_right _ _)) hq0
    refine le_trans h1 (le_trans (hsplitq _ (Nat.cast_nonneg _)) (add_le_add ?_ le_rfl))
    have hj : ((j₀ : ℕ) : ℝ) ^ q ≤ max a₀ 3 + 1 := by
      have := Real.rpow_le_rpow (Nat.cast_nonneg _) hj₀one hq0
      exact le_trans this (le_trans (rpow_le_max_one (by linarith) hq0 hq1)
        (max_le (by linarith) le_rfl))
    calc max 1 C₂ * (((j₀ : ℕ) : ℝ) ^ q * ((1 - q) * st) ^ (-q))
        ≤ max 1 C₂ * ((max a₀ 3 + 1) * ((1 - q) * st) ^ (-q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj hM0) (by linarith)
      _ = max 1 C₂ * (max a₀ 3 + 1) * ((1 - q) * st) ^ (-q) := by ring
  -- (b) the sum
  have hbadpow : ∀ j : ℕ, j₀ ≤ j →
      ν.real (B j) ^ (1 - q) ≤ max 1 C₂ * Real.exp (-2 * (j : ℝ)) := by
    intro j hj
    have h0 : (0 : ℝ) ≤ ν.real (B j) := measureReal_nonneg
    have h1 : ν.real (B j) ≤ C₂ * Real.exp (-(2 * lev j)) := by
      rw [hBreal j]
      exact Gbad (lev j) (ha₀lev j hj)
    have h2 : ν.real (B j) ^ (1 - q) ≤ (C₂ * Real.exp (-(2 * lev j))) ^ (1 - q) :=
      Real.rpow_le_rpow h0 h1 (by linarith)
    have h3 : (C₂ * Real.exp (-(2 * lev j))) ^ (1 - q)
        = C₂ ^ (1 - q) * Real.exp (-2 * (j : ℝ)) := by
      rw [Real.mul_rpow hC₂.le (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      rw [← hlevmul j]
      ring
    have h4 : C₂ ^ (1 - q) ≤ max 1 C₂ := rpow_le_max_one hC₂ h1q.le (by linarith)
    rw [h3] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
  have hstepbd : ∀ j : ℕ, j₀ ≤ j → j < KK → (∫ ω, RR (j + 1) ω ∂ν) ^ q
      ≤ max 1 C₂ * (((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q)) + max 1 C₂ * (E / st) ^ q := by
    intro j hj1 hj2
    have h1 := Real.rpow_le_rpow (hRmean0 (j + 1)) (hRle (j + 1) (by omega) (by omega)) hq0
    push_cast at h1
    exact le_trans h1 (hsplitq _ (by positivity))
  have hsumbd : (∑ j ∈ Finset.Ico j₀ KK, ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q)
      ≤ 2 * (max 1 C₂ * max 1 C₂) * ((1 - q) * st) ^ (-q)
        + 2 * (max 1 C₂ * max 1 C₂) * (E / st) ^ q := by
    have hterm : ∀ j ∈ Finset.Ico j₀ KK,
        ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q
          ≤ (max 1 C₂ * max 1 C₂ * ((1 - q) * st) ^ (-q))
              * (Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q)
            + (max 1 C₂ * max 1 C₂ * (E / st) ^ q) * Real.exp (-2 * (j : ℝ)) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
      have hA := hbadpow j hj1
      have hB := hstepbd j hj1 hj2
      have h1 : (0 : ℝ) ≤ (∫ ω, RR (j + 1) ω ∂ν) ^ q := Real.rpow_nonneg (hRmean0 (j + 1)) _
      have hprod := mul_le_mul hA hB h1 (by positivity)
      calc ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q
          ≤ (max 1 C₂ * Real.exp (-2 * (j : ℝ)))
              * (max 1 C₂ * (((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q))
                + max 1 C₂ * (E / st) ^ q) := hprod
        _ = (max 1 C₂ * max 1 C₂ * ((1 - q) * st) ^ (-q))
              * (Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q)
            + (max 1 C₂ * max 1 C₂ * (E / st) ^ q) * Real.exp (-2 * (j : ℝ)) := by ring
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 := sum_exp_mul_rpow_le hq1 (Finset.Ico j₀ KK)
    have h3 : (∑ j ∈ Finset.Ico j₀ KK, Real.exp (-2 * (j : ℝ))) ≤ 2 := by
      have h := sum_exp_mul_rpow_le (q := 0) zero_le_one (Finset.Ico j₀ KK)
      simpa only [Real.rpow_zero, mul_one] using h
    have hc1 : (0 : ℝ) ≤ max 1 C₂ * max 1 C₂ * ((1 - q) * st) ^ (-q) := mul_nonneg hKcc hM0
    have hc2 : (0 : ℝ) ≤ max 1 C₂ * max 1 C₂ * (E / st) ^ q := mul_nonneg hKcc hAe0
    have h4 := mul_le_mul_of_nonneg_left h2 hc1
    have h5 := mul_le_mul_of_nonneg_left h3 hc2
    linarith
  -- (c) the tail
  have htailbd : ν.real (B KK) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q
      ≤ max 1 C₂ * max 1 C₁ * ((1 - q) * st) ^ (-q) := by
    have hA : ν.real (B KK) ^ (1 - q) ≤ max 1 C₂ * Real.exp (-2 * (KK : ℝ)) :=
      hbadpow KK (Nat.le_add_right _ _)
    have hexp : Real.exp (-2 * (KK : ℝ)) ≤ ((1 - q) * st) ^ (-q) := by
      refine le_trans (Real.exp_le_exp.2 ?_) (exp_neg_two_mul_le_rpow_neg hL2 hq1)
      linarith [hKge]
    have h1 : (0 : ℝ) ≤ (∫ ω, ZZ ω ∂ν) ^ q := Real.rpow_nonneg hZmean0 _
    have hprod := mul_le_mul hA hZpow h1 (by positivity)
    calc ν.real (B KK) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q
        ≤ max 1 C₂ * Real.exp (-2 * (KK : ℝ)) * max 1 C₁ := hprod
      _ ≤ max 1 C₂ * ((1 - q) * st) ^ (-q) * max 1 C₁ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp (by linarith)) (by linarith)
      _ = max 1 C₂ * max 1 C₁ * ((1 - q) * st) ^ (-q) := by ring
  -- assemble
  have hMtar : ((1 - q) * st) ^ (-q) ≤ 3 / 2 * (1 + (1 - q) * st) ^ (-q) :=
    rpow_neg_le_target hL2 hq0 hq1
  have htar0 : (0 : ℝ) ≤ (1 + (1 - q) * st) ^ (-q) := Real.rpow_nonneg (by linarith) _
  have hX0 : (0 : ℝ) ≤ max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
      + max 1 C₂ * max 1 C₁ := by linarith
  have hXM := mul_le_mul_of_nonneg_left hMtar hX0
  have hK1 : (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂) + max 1 C₂ * max 1 C₁)
        * (3 / 2 * (1 + (1 - q) * st) ^ (-q))
      ≤ 3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
          + max 1 C₂ * max 1 C₁)) * (1 + (1 - q) * st) ^ (-q) := by
    have h := mul_le_mul_of_nonneg_right
      (show (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
          + max 1 C₂ * max 1 C₁) * (3 / 2)
        ≤ 3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
          + max 1 C₂ * max 1 C₁)) by linarith) htar0
    linarith
  have hK2 : (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)) * (E / st) ^ q
      ≤ (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)) * (E / st) ^ q := le_rfl
  have hextra : 0 ≤ 3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
      + max 1 C₂ * max 1 C₁)) * (E / st) ^ q := by
    have : (0 : ℝ) ≤ 3 * (max 1 C₁ + (max 1 C₂ * (max a₀ 3 + 1)
        + 2 * (max 1 C₂ * max 1 C₂) + max 1 C₂ * max 1 C₁)) := by linarith
    exact mul_nonneg this hAe0
  have hextra2 : 0 ≤ (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)) * (1 + (1 - q) * st) ^ (-q) :=
    mul_nonneg (by linarith) htar0
  rw [add_mul, mul_add, mul_add]
  linarith [hmain, hfirst, hsumbd, htailbd, hXM, hK1, hK2, hextra, hextra2]

/-! ### The long range `(1, M]`: the objects

Heights near zero need their own offsets (`RMF.harperDt`), so the unit window is kept apart:
`S(M) = S(1) + S(1, M]` (`RMF.lineMass_eq_add_lineMassIoc_sqfree`), and `S(1)` is the unit-window
chaos.  Above height one a single offset serves the whole range. -/

/-- `∫_1^M ‖F(½+ih)‖² dh`, the line mass above the unit window. -/
noncomputable def lineMassIoc (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ) (ω : Ω) : ℝ :=
  ∫ h in Set.Ioc (1 : ℝ) M, ‖randomEulerProduct F N (shiftLine 0 h) ω‖ ^ 2

/-- The same, restricted to a family of events indexed by the height. -/
noncomputable def restrictedLineMassIoc (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ)
    (G : ℝ → Set Ω) (ω : Ω) : ℝ :=
  ∫ h in Set.Ioc (1 : ℝ) M,
    Set.indicator (G h) (fun ω => ‖randomEulerProduct F N (shiftLine 0 h) ω‖ ^ 2) ω

omit [MeasurableSpace Ω] in
lemma lineMassIoc_nonneg (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ) (ω : Ω) :
    0 ≤ lineMassIoc F N M ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _

omit [MeasurableSpace Ω] in
lemma restrictedLineMassIoc_nonneg (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ)
    (G : ℝ → Set Ω) (ω : Ω) : 0 ≤ restrictedLineMassIoc F N M G ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ =>
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω

omit [MeasurableSpace Ω] in
lemma lineMassIoc_eq_restricted_univ (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ) (ω : Ω) :
    lineMassIoc F N M ω = restrictedLineMassIoc F N M (fun _ => Set.univ) ω := by
  simp only [lineMassIoc, restrictedLineMassIoc, Set.indicator_univ]

omit [MeasurableSpace Ω] in
/-- The squarefree product is continuous in the height, on every path. -/
lemma continuous_randomEulerProduct_sqfree_shiftLine {X : ℕ → Ω → ℂ} (N : ℕ) (σ : ℝ)
    (ω : Ω) :
    Continuous fun h : ℝ =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine σ h) ω := by
  have heq : ∀ h : ℝ,
      randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine σ h) ω
        = ∏ p ∈ Nat.primesBelow N, (1 + X p ω * (p : ℂ) ^ (-(shiftLine σ h))) := fun h => by
    rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  simp_rw [heq]
  refine continuous_finsetProd _ fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow hp).pos.ne'
  have hs : Continuous fun h : ℝ => -(shiftLine σ h) := by
    unfold shiftLine
    fun_prop
  exact continuous_const.add (continuous_const.mul (Continuous.const_cpow hs (Or.inl hp0)))

omit [MeasurableSpace Ω] in
/-- **The line mass splits at height one.** -/
lemma lineMass_eq_add_lineMassIoc_sqfree {X : ℕ → Ω → ℂ} (N : ℕ) {M : ℝ} (hM : 1 ≤ M)
    (ω : Ω) :
    lineMass (fun ω => squarefreeExtension fun p => X p ω) N M ω
      = lineMass (fun ω => squarefreeExtension fun p => X p ω) N 1 ω
        + lineMassIoc (fun ω => squarefreeExtension fun p => X p ω) N M ω := by
  have hc : Continuous fun h : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N (shiftLine 0 h) ω‖
        ^ 2 :=
    (continuous_randomEulerProduct_sqfree_shiftLine N 0 ω).norm.pow 2
  rw [lineMass, lineMass, lineMassIoc, ← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hM,
    setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      hc.integrableOn_Ioc hc.integrableOn_Ioc]

/-- **The restricted long-range mass is integrable**, for a measurable family: Tonelli on the
product, `RMF.integrable_uncurry_indicator_normSq_rademacher`. -/
lemma integrable_restrictedLineMassIoc_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) (M : ℝ) (G : ℝ → Set Ω)
    (hGm : ∀ h, MeasurableSet (G h)) (hGu : MeasurableSet {p : Ω × ℝ | p.1 ∈ G p.2}) :
    Integrable (restrictedLineMassIoc (fun ω => squarefreeExtension fun p => X p ω) N M G) μ :=
  (integrable_uncurry_indicator_normSq_rademacher hX N (σ := 0) (by norm_num) G hGm hGu
    (T := Set.Ioc (1 : ℝ) M)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integral_prod_left

/-- **The mean long-range mass**: `E S(1, M] ≤ M·E|F(½)|²`, by Tonelli and the height
independence of the second moment. -/
theorem integral_lineMassIoc_sqfree_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    ∫ ω, lineMassIoc (fun ω => squarefreeExtension fun p => X p ω) N M ω ∂μ
      ≤ M * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine 0 0) ω‖ ^ 2 ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hE0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      N (shiftLine 0 0) ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hInt := integrable_uncurry_indicator_normSq_rademacher hX N (σ := 0) (by norm_num)
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
    (by simp only [Set.mem_univ, Set.setOf_true]; exact MeasurableSet.univ)
    (T := Set.Ioc (1 : ℝ) M) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hle := integral_setIntegral_indicator_le_of_per_height (ν := μ) measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hInt (fun t _ => by
      rw [Set.indicator_univ]
      exact le_of_eq (hRa.integral_normSq_shiftLine_eq N t 0))
  have heq : (∫ ω, lineMassIoc (fun ω => squarefreeExtension fun p => X p ω) N M ω ∂μ)
      = ∫ ω, (∫ t in Set.Ioc (1 : ℝ) M, Set.indicator Set.univ
          (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (shiftLine 0 t) ω‖ ^ 2) ω) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      lineMassIoc_eq_restricted_univ _ N M ω)
  rw [heq]
  refine le_trans hle ?_
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  exact mul_le_mul_of_nonneg_right (by linarith) hE0

omit [MeasurableSpace Ω] in
/-- **The decomposition along a chain**, for the long-range mass scaled by `c`:
`RMF.setIntegral_le_decomposition` at `g h ω = ‖F(½+ih)‖²` and the window `(1, M]`. -/
lemma lineMassIoc_le_decomposition (F : Ω → ArithmeticFunction ℂ) (N : ℕ) (M : ℝ) {c : ℝ}
    (hc : 0 ≤ c) (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ) (hrm : r ≤ m) :
    c * lineMassIoc F N M ω
      ≤ c * restrictedLineMassIoc F N M (S r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ Set.Ioc (1 : ℝ) M, ω ∉ S j h} (fun _ => (1 : ℝ)) ω
              * (c * restrictedLineMassIoc F N M (S (j + 1)) ω))
        + Set.indicator {ω | ∃ h ∈ Set.Ioc (1 : ℝ) M, ω ∉ S m h} (fun _ => (1 : ℝ)) ω
            * (c * lineMassIoc F N M ω) :=
  setIntegral_le_decomposition
    (g := fun h ω => ‖randomEulerProduct F N (shiftLine 0 h) ω‖ ^ 2)
    (fun _ _ => sq_nonneg _) measurableSet_Ioc hc S ω r m hrm

/-! ### The long range `(1, M]`: the good family at one offset

One offset `D = harperDwExp D₀ c (M - 1)` serves every height in `(1, M]`: the strengthened height
condition holds up to `M` (`RMF.sq_two_mul_le_exp_harperOffset_harperDwExp` at `w = M - 1`), and the
threshold condition at every height `t ≥ 1`
(`RMF.two_mul_exp_le_mul_exp_harperOffset_harperDwExp_of_one_le`).  The family's level is
`a + Θ + k`, `k = D - D₀`: the `k` pays for `e^D` in the bad set, the `Θ ≥ ½ log M` for the width
of the range. -/

/-- **The threshold condition at any height `t ≥ 1`**, at every window level: the proof of
`RMF.two_mul_exp_le_mul_exp_harperOffset_harperDwExp` only uses that the offset is at least
`harperOffset D₀ x`. -/
lemma two_mul_exp_le_mul_exp_harperOffset_harperDwExp_of_one_le {D₀ : ℕ} {c w t : ℝ}
    (ht : 1 ≤ t) (x : ℝ) :
    2 * Real.exp ((D₀ : ℝ) - 1) ≤ 2 * t * Real.exp (harperOffset (harperDwExp D₀ c w) x) := by
  have hmono : harperOffset D₀ x ≤ harperOffset (harperDwExp D₀ c w) x := by
    rw [harperDwExp, harperOffset_add]
    linarith [Nat.cast_nonneg (α := ℝ) ⌈harperWindowLevel c w⌉₊]
  have hθ : (D₀ : ℝ) - 1 ≤ harperOffset (harperDwExp D₀ c w) x :=
    le_trans (sub_one_le_harperOffset D₀ x) hmono
  have hexp : Real.exp ((D₀ : ℝ) - 1) ≤ Real.exp (harperOffset (harperDwExp D₀ c w) x) :=
    Real.exp_le_exp.2 hθ
  nlinarith [Real.exp_pos ((D₀ : ℝ) - 1), Real.exp_pos (harperOffset (harperDwExp D₀ c w) x)]

/-- **The bad set over the range**, at the raised level.  One application of
`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_le` on the window `[1, 1 + M)`: its
bound `C e^D M e^{-2(a+Θ+k)}` is at most `C e^{D₀} e^{-2a}`, because `D = D₀ + k` and
`M ≤ e^{2Θ}`. -/
theorem exists_const_measureReal_notMem_lineMassIoc_family_le :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (D₀ : ℕ) (B c : ℝ) (y : ℕ) (M Θ a : ℝ), 4 ≤ D₀ → 20 ≤ B → 1 < (y : ℝ) →
          ((harperDwExp D₀ c (M - 1) : ℕ) : ℝ) ≤ Real.log (Real.log y) →
          1 ≤ M → Real.log M ≤ 2 * Θ → 0 ≤ Θ → a₀ ≤ a →
            ν.real {ω | ∃ h ∈ Set.Ioc (1 : ℝ) M, ω ∉ harperGoodRangeAdd Y B
                (harperDwExp D₀ c (M - 1)) (y : ℝ) 0
                (a + Θ + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
                (harperBlockCount (harperDwExp D₀ c (M - 1)) (y : ℝ)) h}
              ≤ C * Real.exp (D₀ : ℝ) * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_le (Ω' := Ω) 0 le_rfl
  refine ⟨max a₀ 0, C, hC, ?_⟩
  intro Y ν hY D₀ B c y M Θ a hD₀ hB hy hDL hM hΘ hΘ0 ha
  haveI := hY.isProbabilityMeasure
  set D : ℕ := harperDwExp D₀ c (M - 1) with hDdef
  set k : ℕ := D - D₀ with hkdef
  have hD₀D : D₀ ≤ D := le_harperDwExp D₀ c (M - 1)
  have hDk : (D : ℝ) = (D₀ : ℝ) + (k : ℝ) := by
    have h : D = D₀ + k := by omega
    exact_mod_cast h
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hD4 : 4 ≤ D := le_trans hD₀ hD₀D
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hM0 : (0 : ℝ) < M := by linarith
  have hoff : (0 : ℝ) ≤ harperOffset D (y : ℝ) := by
    have h4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD4
    linarith [sub_one_le_harperOffset D (y : ℝ)]
  have hwid : Real.exp (-((⌈(a + Θ + (k : ℝ)) / 4⌉₊ : ℝ) + harperOffset D (y : ℝ))) ≤ M := by
    have hceil : (0 : ℝ) ≤ ((⌈(a + Θ + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h := Real.exp_le_one_iff.2
      (by linarith : -((⌈(a + Θ + (k : ℝ)) / 4⌉₊ : ℝ) + harperOffset D (y : ℝ)) ≤ 0)
    linarith
  have hsub : {ω | ∃ h ∈ Set.Ioc (1 : ℝ) M, ω ∉ harperGoodRangeAdd Y B D (y : ℝ) 0
        (a + Θ + (k : ℝ)) (harperBlockCount D (y : ℝ)) h}
      ⊆ {ω | ∃ h ∈ Set.Ico (1 : ℝ) (1 + M), ω ∉ harperGoodRangeAdd Y B D (y : ℝ) 0
        (a + Θ + (k : ℝ)) (harperBlockCount D (y : ℝ)) h} := by
    rintro ω ⟨h, hh, hnot⟩
    exact ⟨h, ⟨hh.1.le, by linarith [hh.2]⟩, hnot⟩
  have hbd := H Y ν hY D (y : ℝ) 0 0 (a + Θ + (k : ℝ)) B 1 M hD4 hy hDL le_rfl le_rfl le_rfl
    (by simp) (le_trans (le_max_left _ _) (by linarith)) hB hwid
  have hkey : Real.exp (D : ℝ) * M * Real.exp (-(2 * (a + Θ + (k : ℝ))))
      ≤ Real.exp (D₀ : ℝ) * Real.exp (-(2 * a)) := by
    rw [← Real.exp_log hM0, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by rw [hDk]; linarith)
  calc ν.real {ω | ∃ h ∈ Set.Ioc (1 : ℝ) M, ω ∉ harperGoodRangeAdd Y B D (y : ℝ) 0
          (a + Θ + (k : ℝ)) (harperBlockCount D (y : ℝ)) h}
      ≤ ν.real {ω | ∃ h ∈ Set.Ico (1 : ℝ) (1 + M), ω ∉ harperGoodRangeAdd Y B D (y : ℝ) 0
          (a + Θ + (k : ℝ)) (harperBlockCount D (y : ℝ)) h} := measureReal_mono hsub
    _ ≤ C * Real.exp (D : ℝ) * M * Real.exp (-(2 * (a + Θ + (k : ℝ)))) := hbd
    _ = C * (Real.exp (D : ℝ) * M * Real.exp (-(2 * (a + Θ + (k : ℝ))))) := by ring
    _ ≤ C * (Real.exp (D₀ : ℝ) * Real.exp (-(2 * a))) := mul_le_mul_of_nonneg_left hkey hC.le
    _ = C * Real.exp (D₀ : ℝ) * Real.exp (-(2 * a)) := by ring

set_option maxHeartbeats 800000 in
-- one proof carries the parameter discharge of the chain, the count arithmetic and the
-- normalisation, as the window theorem
-- `RMF.exists_const_integral_restrictedChaosWindowShift_raise_le_rademacher_of_drop_wide` does
/-- **The restricted long-range mass at the raised level.**  The chaos half of the family over
`(1, M]`, read before the window chain's `(k + 1)`-conversion: at level `a' = a + Θ + k`, offset
`D = harperDwExp D₀ c (M - 1)` and base count `t = harperBlockCount D₀ y`,
`E[(M log y)^{-1} S_G(1, M]] ≤ A·(a + Θ + k)/√(t - ⌈(a+Θ)/4⌉)`: the single-height join
`RMF.exists_integral_restricted_normSq_le_rademacher_of_offset_of_drop_wide` on `T = (1, M]`, the
count at the level `a + Θ`, and Mertens for the normalisation. -/
theorem exists_const_integral_restrictedLineMassIoc_family_le :
    ∃ (D₀ _n₀ : ℕ) (a₀ A B c : ℝ), 4 ≤ D₀ ∧ 1 ≤ a₀ ∧ 0 < A ∧ 20 ≤ B ∧ 0 < c ∧
      ∃ x₀ : ℝ, ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (y : ℕ) (M Θ a : ℝ), x₀ ≤ (y : ℝ) → 1 ≤ M → 0 ≤ Θ → a₀ ≤ a →
          harperWindowLevel c (M - 1) ≤ Real.log (Real.log y) / 3 →
          8 * (⌈(a + Θ) / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ (y : ℝ) : ℝ) →
            (∫ ω, (M * Real.log y)⁻¹ * restrictedLineMassIoc
                (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M
                (fun h => harperGoodRangeAdd Y B (harperDwExp D₀ c (M - 1)) (y : ℝ) 0
                  (a + Θ + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDwExp D₀ c (M - 1)) (y : ℝ)) h) ω ∂ν)
              ≤ A * ((a + Θ + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
                  / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))) := by
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  obtain ⟨D₁, n₀, x₀c, a₀c, Ac, B, Tsh, c, hD₁, hAc, hB, hTsh, hcpos, Hc⟩ :=
    exists_integral_restricted_normSq_le_rademacher_of_offset_of_drop_wide
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_le_rademacher
  obtain ⟨D₀, hD₀ge, hTexp⟩ := exists_le_two_mul_exp_sub_one Tsh (max D₁ 4)
  have hD₁D₀ : D₁ ≤ D₀ := le_trans (le_max_left _ _) hD₀ge
  have h4D₀ : 4 ≤ D₀ := le_trans (le_max_right _ _) hD₀ge
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D₀ (24 * (D₀ + n₀ + 6))
  refine ⟨D₀, n₀, max a₀c 1, 2 * Ac * CM, B, c, h4D₀, le_max_right _ _, by positivity, hB,
    hcpos, max (max x₀c (Real.exp 3)) x₂, ?_⟩
  intro Y ν hY y M Θ a hy hM hΘ ha hcut hR
  haveI := hY.isProbabilityMeasure
  obtain ⟨-, hD₀L, hcount24⟩ := hx₂ (y : ℝ) (le_trans (le_max_right _ _) hy)
  have hyx₀ : x₀c ≤ (y : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hye3 : Real.exp 3 ≤ (y : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have ha₀c : a₀c ≤ a := le_trans (le_max_left _ _) ha
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hM0 : (0 : ℝ) < M := by linarith
  have hL0a : (0 : ℝ) ≤ Real.log (Real.log y) := le_trans (Nat.cast_nonneg _) hD₀L
  have hcountL : ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ) ≤ Real.log (Real.log y) := by
    have h3 : ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ)
        ≤ ((⌊Real.log (Real.log (y : ℝ))⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    linarith [Nat.floor_le hL0a]
  have hΛ24 : 24 * ((D₀ : ℝ) + (n₀ : ℝ) + 2 * ((0 : ℕ) : ℝ) + 6) ≤ Real.log (Real.log y) := by
    have h1 : ((24 * (D₀ + n₀ + 6) : ℕ) : ℝ) ≤ ((harperBlockCount D₀ (y : ℝ) : ℕ) : ℝ) := by
      exact_mod_cast hcount24
    push_cast at h1 ⊢
    linarith
  -- the offset and its level
  set D : ℕ := harperDwExp D₀ c (M - 1) with hDdef
  set k : ℕ := D - D₀ with hkdef
  have hD₀D : D₀ ≤ D := le_harperDwExp D₀ c (M - 1)
  have hDk : D = D₀ + k := by omega
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkR : (k : ℝ) ≤ Real.log (Real.log y) / 3 + 1 := harperDwExp_sub_le_of_cut (D₀ := D₀) hcut
  have hΛ' : 2 * ((D₀ : ℝ) + ((max (2 * 0) (n₀ + 0) : ℕ) : ℝ) + 2) ≤ Real.log (Real.log y) := by
    have hmax : max (2 * 0) (n₀ + 0) = n₀ := by omega
    rw [hmax]
    have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
    have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
    push_cast at hΛ24
    linarith
  obtain ⟨-, hDlog, -, -⟩ :=
    harper_block_count_of_window_wide (D₀ := D₀) (d := 0) (n₀ := n₀) hcut hΛ'
  -- the count at the raised level
  obtain ⟨hfit, hhalf⟩ := harperBlockCount_raise_halving_of_drop_of_level (D₀ := D₀)
    (n₀ := n₀) (k := k) (d := 0) (a := a + Θ) (x := (y : ℝ)) (by linarith) hR hΛ24 hkR
  rw [← hDk] at hfit hhalf
  set a' : ℝ := a + Θ + (k : ℝ) with ha'def
  set r : ℕ := ⌈a' / 4⌉₊ with hrdef
  have ha'1 : (1 : ℝ) ≤ a' := by linarith
  have hr1 : 1 ≤ r := Nat.ceil_pos.2 (by linarith)
  have hrub : (r : ℝ) ≤ a' / 4 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hrn : r ≤ harperBlockCount D (y : ℝ) - 0 := by omega
  have hn₀r : n₀ ≤ harperBlockCount D (y : ℝ) - 0 - r := by omega
  -- the two height conditions on `(1, M]`
  have hts : ∀ t ∈ Set.Ioc (1 : ℝ) M, 0 < 2 * t
      ∧ (2 * t) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset D (y : ℝ) / 10))
      ∧ Tsh ≤ 2 * t * Real.exp (harperOffset D (y : ℝ)) := by
    intro t ht
    have ht1 : 1 < t := ht.1
    refine ⟨by linarith, ?_, ?_⟩
    · exact sq_two_mul_le_exp_harperOffset_harperDwExp (by omega) hcpos (by linarith)
        (by linarith) (by linarith [ht.2]) (y : ℝ)
    · exact le_trans hTexp
        (two_mul_exp_le_mul_exp_harperOffset_harperDwExp_of_one_le ht1.le (y : ℝ))
  have hchain := Hc Ω Y ν hY (y : ℝ) 0 a' 0 D r 0 (Set.Ioc (1 : ℝ) M)
    (fun j => 2 * Real.log j) hyx₀ (le_trans hD₁D₀ hD₀D) hDlog (by norm_num) (by simp)
    (by simp) (by linarith) ha'1 hr1 hrn hrub hn₀r measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hts
    (fun j hj _ => by
      have h0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
      rw [abs_of_nonneg (by linarith)]
      linarith)
  have hfl : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  rw [hfl] at hchain
  have hMert' := hMert Ω Y ν hY (y : ℝ) hy2
  rw [hfl] at hMert'
  -- the chain's count, against the base count
  have hr₀1 : (1 : ℝ) ≤ (⌈(a + Θ) / 4⌉₊ : ℝ) := by
    exact_mod_cast Nat.ceil_pos.2 (by linarith : (0 : ℝ) < (a + Θ) / 4)
  have hu : 0 < (harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ) := by linarith
  have hbase : min 1 (a' / Real.sqrt (((harperBlockCount D (y : ℝ) - 0 : ℕ) : ℝ) - r))
      ≤ Real.sqrt 2
        * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))) := by
    have hsq : Real.sqrt (((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)) / 2)
        ≤ Real.sqrt (((harperBlockCount D (y : ℝ) - 0 : ℕ) : ℝ) - r) := Real.sqrt_le_sqrt hhalf
    have hsqpos : 0 < Real.sqrt
        (((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)) / 2) :=
      Real.sqrt_pos.2 (by linarith)
    refine le_trans (min_le_right _ _) ?_
    calc a' / Real.sqrt (((harperBlockCount D (y : ℝ) - 0 : ℕ) : ℝ) - r)
        ≤ a' / Real.sqrt (((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)) / 2) :=
          div_le_div_of_nonneg_left (by linarith) hsqpos hsq
      _ = Real.sqrt 2
            * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))) := by
          rw [Real.sqrt_div hu.le, div_div_eq_mul_div]
          ring
  -- assemble
  have hE0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
      (y + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => sq_nonneg _
  have hvol : (volume (Set.Ioc (1 : ℝ) M)).toReal ≤ M := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hmin0 : (0 : ℝ) ≤ min 1 (a' / Real.sqrt (((harperBlockCount D (y : ℝ) - 0 : ℕ) : ℝ) - r)) :=
    le_min zero_le_one (div_nonneg (by linarith) (Real.sqrt_nonneg _))
  have hX0 : (0 : ℝ)
      ≤ a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)) :=
    div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hc0 : (0 : ℝ) ≤ (M * Real.log y)⁻¹ := inv_nonneg.2 (mul_nonneg hM0.le hlogy.le)
  have hswap : (∫ ω, restrictedLineMassIoc (fun ω => squarefreeExtension fun p => Y p ω)
        (y + 1) M (fun h => harperGoodRangeAdd Y B D (y : ℝ) 0 a' (harperBlockCount D (y : ℝ)) h)
        ω ∂ν)
      ≤ (volume (Set.Ioc (1 : ℝ) M)).toReal
          * (Ac * min 1 (a' / Real.sqrt (((harperBlockCount D (y : ℝ) - 0 : ℕ) : ℝ) - r)))
          * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (shiftLine 0 0) ω‖ ^ 2 ∂ν := hchain
  rw [integral_const_mul]
  calc (M * Real.log y)⁻¹ * ∫ ω, restrictedLineMassIoc
          (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M
          (fun h => harperGoodRangeAdd Y B D (y : ℝ) 0 a' (harperBlockCount D (y : ℝ)) h) ω ∂ν
      ≤ (M * Real.log y)⁻¹ * ((volume (Set.Ioc (1 : ℝ) M)).toReal
          * (Ac * min 1 (a' / Real.sqrt (((harperBlockCount D (y : ℝ) - 0 : ℕ) : ℝ) - r)))
          * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (shiftLine 0 0) ω‖ ^ 2 ∂ν) := mul_le_mul_of_nonneg_left hswap hc0
    _ ≤ (M * Real.log y)⁻¹ * (M * (Ac * (Real.sqrt 2
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)))))
          * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (shiftLine 0 0) ω‖ ^ 2 ∂ν) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul hvol (mul_le_mul_of_nonneg_left hbase hAc.le)
            (mul_nonneg hAc.le hmin0) (by linarith)) hE0) hc0
    _ = (M⁻¹ * M) * (Ac * Real.sqrt 2
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)))
          * ((Real.log y)⁻¹ * ∫ ω, ‖randomEulerProduct
              (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (shiftLine 0 0) ω‖ ^ 2
                ∂ν)) := by
        rw [mul_inv]
        ring
    _ = Ac * Real.sqrt 2
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)))
          * ((Real.log y)⁻¹ * ∫ ω, ‖randomEulerProduct
              (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν) := by
        rw [inv_mul_cancel₀ hM0.ne', one_mul]
    _ ≤ Ac * Real.sqrt 2
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))) * CM :=
        mul_le_mul_of_nonneg_left hMert'
          (mul_nonneg (mul_nonneg hAc.le (Real.sqrt_nonneg _)) hX0)
    _ = Real.sqrt 2 * (Ac * CM
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)))) := by
        ring
    _ ≤ 2 * (Ac * CM
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)))) :=
        mul_le_mul_of_nonneg_right hs2 (mul_nonneg (mul_nonneg hAc.le hCM.le) hX0)
    _ = 2 * Ac * CM
          * (a' / Real.sqrt ((harperBlockCount D₀ (y : ℝ) : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))) := by
        ring

/-! ### The long range `(1, M]`: the moment -/

set_option maxHeartbeats 1600000 in
-- the interpolation's ten inputs, each discharged from the family above, over one goal
/-- **The chaos over the long range `(1, M]`.**  For `M ≥ 1` whose window level fits
(`harperWindowLevel c (M - 1) ≤ log log y / 3`), `y ≥ x₀` and `0 ≤ q ≤ 1`,
`E[((M log y)^{-1} S(1, M])^q] ≤ K·((1 + (1-q)√t)^{-q} + ((½ log M + k)/√t)^q)`,
`t = harperBlockCount D₀ y`, `k = harperDwExp D₀ c (M - 1) - D₀`.  By
`RMF.integral_rpow_le_of_goodSets_add` on the family at level `a + ½ log M + k`; when the shift
exceeds `√t`, Jensen suffices. -/
theorem exists_const_integral_rpow_lineMassIoc_le_rademacher :
    ∃ (D₀ : ℕ) (c K x₀ : ℝ), 4 ≤ D₀ ∧ 0 < c ∧ 0 < K ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (y : ℕ) (M q : ℝ), x₀ ≤ (y : ℝ) → 1 ≤ M → 0 ≤ q → q ≤ 1 →
          harperWindowLevel c (M - 1) ≤ Real.log (Real.log y) / 3 →
            ∫ ω, ((M * Real.log y)⁻¹
                * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q ∂ν
              ≤ K * ((1 + (1 - q) * Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ)) ^ (-q)
                + ((Real.log M / 2 + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
                    / Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ)) ^ q) := by
  obtain ⟨D₀, _n₀, a₀, A, B, c, hD₀, ha₀1, hA, hB, hc, x₁, Hint⟩ :=
    exists_const_integral_restrictedLineMassIoc_family_le (Ω := Ω)
  obtain ⟨a₀b, Cb, hCb, Hbad⟩ := exists_const_measureReal_notMem_lineMassIoc_family_le (Ω := Ω)
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_le_rademacher
  set a₁ : ℝ := max a₀ a₀b with ha₁def
  set C₂ : ℝ := max (Cb * Real.exp (D₀ : ℝ)) (A * Real.sqrt 2) with hC₂def
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set Kint : ℝ := 3 * (max 1 CM + (max 1 C₂ * (max a₁ 3 + 1) + 2 * (max 1 C₂ * max 1 C₂)
      + max 1 C₂ * max 1 CM)) + (max 1 C₂ + 2 * (max 1 C₂ * max 1 C₂)) with hKintdef
  have hK0 : (0 : ℝ) ≤ Kint := by
    rw [hKintdef]
    positivity
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D₀ (⌈max a₁ 3⌉₊ ^ 2 + (D₀ + 85))
  refine ⟨D₀, c, Kint + max 1 CM, max (max x₁ x₂) (Real.exp 3), hD₀, hc,
    by linarith [le_max_left 1 CM], ?_⟩
  intro Y ν hY y M q hy hM hq0 hq1 hcut
  haveI := hY.isProbabilityMeasure
  have hx₁ : x₁ ≤ (y : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hx₂' : x₂ ≤ (y : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hye3 : Real.exp 3 ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hy1 : (1 : ℝ) < (y : ℝ) := by linarith
  obtain ⟨-, hD₀L, hcountbig⟩ := hx₂ (y : ℝ) hx₂'
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy1
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  set t : ℕ := harperBlockCount D₀ (y : ℝ) with htdef
  set st : ℝ := Real.sqrt (t : ℝ) with hstdef
  set D : ℕ := harperDwExp D₀ c (M - 1) with hDdef
  set k : ℕ := D - D₀ with hkdef
  set Θ : ℝ := Real.log M / 2 with hΘdef
  have hΘ0 : 0 ≤ Θ := div_nonneg hlogM (by norm_num)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  set E : ℝ := Θ + (k : ℝ) with hEdef
  have hE0 : 0 ≤ E := by linarith
  -- the counts
  have hT2 : ⌈max a₁ 3⌉₊ ^ 2 ≤ t := le_trans (Nat.le_add_right _ _) hcountbig
  have hDt : D₀ + 85 ≤ t := le_trans (Nat.le_add_left _ _) hcountbig
  have hDt' : (D₀ : ℝ) + 85 ≤ (t : ℝ) := by exact_mod_cast hDt
  have hsts : st ^ 2 = (t : ℝ) := Real.sq_sqrt (Nat.cast_nonneg t)
  have hst9 : (9 : ℝ) ≤ st := by
    refine (Real.le_sqrt (by norm_num) (Nat.cast_nonneg t)).2 ?_
    rw [show (9 : ℝ) ^ 2 = 81 by norm_num]
    have h0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hst0 : (0 : ℝ) ≤ st := by linarith
  have hsq9 : 9 * st ≤ (t : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hst9 hst0
    nlinarith [hsts]
  have hfloor : t + D₀ ≤ ⌊Real.log (Real.log (y : ℝ))⌋₊ := by
    have h1 : t = ⌊Real.log (Real.log (y : ℝ))⌋₊ - D₀ := by rw [htdef, harperBlockCount]
    omega
  have hΛ' : 2 * ((D₀ : ℝ) + ((max (2 * 0) (0 + 0) : ℕ) : ℝ) + 2) ≤ Real.log (Real.log y) := by
    have hmax : max (2 * 0) (0 + 0) = 0 := by omega
    rw [hmax, Nat.cast_zero]
    have h2 : ((t + D₀ : ℕ) : ℝ) ≤ ((⌊Real.log (Real.log (y : ℝ))⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hfloor
    push_cast at h2
    linarith [Nat.floor_le (le_trans (Nat.cast_nonneg D₀) hD₀L)]
  obtain ⟨-, hDlog, -, -⟩ :=
    harper_block_count_of_window_wide (D₀ := D₀) (d := 0) (n₀ := 0) hcut hΛ'
  -- the objects the interpolation reads
  set cc : ℝ := (M * Real.log y)⁻¹ with hccdef
  have hcc0 : 0 ≤ cc := inv_nonneg.2 (mul_nonneg hM0.le hlogy.le)
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ p.2
  have hZ0 : ∀ ω, 0 ≤ cc * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω :=
    fun ω => mul_nonneg hcc0 (lineMassIoc_nonneg _ _ _ _)
  have hZi : Integrable (fun ω =>
      cc * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ν := by
    have h := (integrable_restrictedLineMassIoc_sqfree hY (y + 1) M (fun _ => Set.univ)
      (fun _ => MeasurableSet.univ)
      (by simp only [Set.mem_univ, Set.setOf_true]; exact MeasurableSet.univ)).const_mul cc
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [lineMassIoc_eq_restricted_univ]
  have hZmean : (∫ ω, cc * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω)
      (y + 1) M ω ∂ν) ≤ CM := by
    rw [integral_const_mul]
    have h1 := integral_lineMassIoc_sqfree_le hY (y + 1) hM
    have hM' := hMert Ω Y ν hY (y : ℝ) hy2
    rw [Nat.floor_natCast] at hM'
    calc cc * ∫ ω, lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω ∂ν
        ≤ cc * (M * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (y + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν) := mul_le_mul_of_nonneg_left h1 hcc0
      _ = (M⁻¹ * M) * ((Real.log y)⁻¹ * ∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν) := by
          rw [hccdef, mul_inv]
          ring
      _ = (Real.log y)⁻¹ * ∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν := by
          rw [inv_mul_cancel₀ hM0.ne', one_mul]
      _ ≤ CM := hM'
  have hRi : ∀ S : ℝ → Set Ω, (∀ h, MeasurableSet (S h)) →
      MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2} →
      Integrable (fun ω => cc * restrictedLineMassIoc
        (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M S ω) ν :=
    fun S hm hu => (integrable_restrictedLineMassIoc_sqfree hY (y + 1) M S hm hu).const_mul cc
  have htar0 : (0 : ℝ) ≤ (1 + (1 - q) * st) ^ (-q) :=
    Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg (by linarith) hst0)) _
  have hA0 : (0 : ℝ) ≤ (E / st) ^ q := Real.rpow_nonneg (div_nonneg hE0 hst0) _
  have hm0 : (0 : ℝ) ≤ max 1 CM := le_trans zero_le_one (le_max_left _ _)
  by_cases hEst : E ≤ st
  · -- the interpolation
    have hGbad : ∀ a, a₁ ≤ a →
        ν.real {ω | ∃ h ∈ Set.Ioc (1 : ℝ) M, ω ∉ harperGoodRangeAdd Y B D (y : ℝ) 0
          (a + Θ + (k : ℝ)) (harperBlockCount D (y : ℝ)) h} ≤ C₂ * Real.exp (-(2 * a)) := by
      intro a ha
      have h := Hbad Y ν hY D₀ B c y M Θ a hD₀ hB hy1 hDlog hM
        (by rw [hΘdef]; linarith) hΘ0 (le_trans (le_max_right _ _) ha)
      exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hGint : ∀ a, a₁ ≤ a → a ≤ 3 * st →
        (∫ ω, cc * restrictedLineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M
          (fun h => harperGoodRangeAdd Y B D (y : ℝ) 0 (a + Θ + (k : ℝ))
            (harperBlockCount D (y : ℝ)) h) ω ∂ν) ≤ C₂ * ((a + E) / st) := by
      intro a ha ha3
      have ha1 : (1 : ℝ) ≤ a := le_trans ha₀1 (le_trans (le_max_left _ _) ha)
      have hΘst : Θ ≤ st := le_trans (by linarith) hEst
      have hr₀ : ((⌈(a + Θ) / 4⌉₊ : ℕ) : ℝ) ≤ (a + Θ) / 4 + 1 :=
        (Nat.ceil_lt_add_one (by linarith)).le
      have hR : 8 * (⌈(a + Θ) / 4⌉₊ : ℝ) ≤ (t : ℝ) := by linarith
      have h := Hint Y ν hY y M Θ a hx₁ hM hΘ0 (le_trans (le_max_left _ _) ha) hcut hR
      have hpos : 0 < (t : ℝ) / 2 := by linarith
      have hsq : Real.sqrt ((t : ℝ) / 2) ≤ Real.sqrt ((t : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith)
      have hsqpos : 0 < Real.sqrt ((t : ℝ) / 2) := Real.sqrt_pos.2 hpos
      have haE : a + Θ + (k : ℝ) = a + E := by rw [hEdef]; ring
      have hconv : (a + Θ + (k : ℝ)) / Real.sqrt ((t : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))
          ≤ Real.sqrt 2 * ((a + E) / st) := by
        calc (a + Θ + (k : ℝ)) / Real.sqrt ((t : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))
            ≤ (a + Θ + (k : ℝ)) / Real.sqrt ((t : ℝ) / 2) :=
              div_le_div_of_nonneg_left (by linarith) hsqpos hsq
          _ = Real.sqrt 2 * ((a + E) / st) := by
              rw [Real.sqrt_div (Nat.cast_nonneg _), div_div_eq_mul_div, haE, hstdef]
              ring
      calc (∫ ω, cc * restrictedLineMassIoc (fun ω => squarefreeExtension fun p => Y p ω)
            (y + 1) M (fun h => harperGoodRangeAdd Y B D (y : ℝ) 0 (a + Θ + (k : ℝ))
              (harperBlockCount D (y : ℝ)) h) ω ∂ν)
          ≤ A * ((a + Θ + (k : ℝ)) / Real.sqrt ((t : ℝ) - (⌈(a + Θ) / 4⌉₊ : ℝ))) := h
        _ ≤ A * (Real.sqrt 2 * ((a + E) / st)) := mul_le_mul_of_nonneg_left hconv hA.le
        _ = (A * Real.sqrt 2) * ((a + E) / st) := by ring
        _ ≤ C₂ * ((a + E) / st) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (div_nonneg (by linarith) hst0)
    have hinterp := integral_rpow_le_of_goodSets_add (ν := ν)
      (Z := fun ω => cc * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω)
      (Rst := fun S ω => cc * restrictedLineMassIoc
        (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M S ω)
      (win := Set.Ioc (1 : ℝ) M) (q := q) (t := t) (a₀ := a₁) (C₁ := CM) (C₂ := C₂) (E := E)
      hZ0 hZi (fun S ω => mul_nonneg hcc0 (restrictedLineMassIoc_nonneg _ _ _ _ _)) hRi
      (fun S ω r m hrm => lineMassIoc_le_decomposition _ (y + 1) M hcc0 S ω r m hrm)
      hq0 hq1 hCM hC₂pos hE0 hZmean hT2
      (fun a h => harperGoodRangeAdd Y B D (y : ℝ) 0 (a + Θ + (k : ℝ))
        (harperBlockCount D (y : ℝ)) h)
      (fun a h => measurableSet_harperGoodRangeAdd hYm B D (y : ℝ) 0 _ _ h)
      (fun a => measurableSet_harperGoodRangeAdd_uncurry hYm B D (y : ℝ) 0 _ _)
      hGbad hGint
    refine le_trans hinterp (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg htar0 hA0))
  · -- the shift exceeds `√t`: the additive term is at least one, and Jensen suffices
    have hZqi := integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0 hq1
    have hjensen := integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hZ0 ω)) hZi hZqi
    have hmean0 : (0 : ℝ) ≤ ∫ ω, cc * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω)
        (y + 1) M ω ∂ν := integral_nonneg hZ0
    have hpow := le_trans (Real.rpow_le_rpow hmean0 hZmean hq0) (rpow_le_max_one hCM hq0 hq1)
    have hstpos : (0 : ℝ) < st := by linarith
    have hone : 1 ≤ (E / st) ^ q :=
      Real.one_le_rpow ((one_le_div hstpos).2 (le_of_lt (not_le.1 hEst))) hq0
    have h1 := mul_nonneg hK0 htar0
    have h2 := mul_nonneg hK0 hA0
    have h3 := mul_nonneg hm0 htar0
    calc ∫ ω, (cc * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q
          ∂ν
        ≤ max 1 CM := le_trans hjensen hpow
      _ ≤ max 1 CM * (E / st) ^ q := le_mul_of_one_le_right hm0 hone
      _ ≤ (Kint + max 1 CM) * ((1 + (1 - q) * st) ^ (-q) + (E / st) ^ q) := by
          rw [add_mul, mul_add, mul_add]
          linarith

end RMF
