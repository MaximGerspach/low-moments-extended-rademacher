/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.RademacherLower
import RMF.Probability.StrongChaosMoment
import RMF.Probability.RademacherRealness

/-!
# From the windowed chaos to `RMF.windowMaxMoment`

`RMF.windowMaxMoment` maximises, over `n : ℤ`, the `q`-th moment of

    (2π)⁻¹ ∫_{(n, n+1]} ‖A_y(½+σ+it)‖² dt

damped by `(|n|+1)^{-1/4}`, and `RMF.windowMaxMoment_le_of_split_damped` reduces bounding it to a
sharp damped bound on `|n| ≤ N₀` and a crude one everywhere.  The sharp bound is the chaos estimate
on a window (`RMF.exists_const_integral_chaosWindowShift_rpow_le_rademacher_of_top`), which is
stated for `RMF.chaosWindowShift`.

The two differ by one constant: `windowMaxMoment` normalises by `(2π)⁻¹` and
`chaosWindowShift` by `(ℓog x)⁻¹`.  This file is the conversion. -/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **The two normalisations, on one window.**  `RMF.windowMaxMoment`'s integrand is
`RMF.chaosWindowShift` times `(2π)⁻¹·ℓog x`, pointwise in `ω`.

`RMF.lineSqOf (1/2+σ)` and `‖A(RMF.shiftLine σ t)‖²` are the same term — `RMF.shiftLine` is
defined as `((1/2+σ : ℝ) : ℂ) + t·I` — so the only content is the interval-to-set integral and
`(ℓog x)⁻¹·ℓog x = 1`. -/
lemma lineSqOf_window_eq_mul_chaosWindowShift (F : Ω → ArithmeticFunction ℂ)
    {x : ℝ} (hx : 1 < x) (σ n : ℝ) (ω : Ω) :
    (2 * Real.pi)⁻¹ * ∫ t in Set.Ioc n (n + 1), lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t
      = (2 * Real.pi)⁻¹ * Real.log x * chaosWindowShift F x σ n ω := by
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hcong : ∀ t : ℝ, lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t
      = ‖randomEulerProduct F (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2 := fun _ => rfl
  rw [chaosWindowShift, intervalIntegral.integral_of_le (by linarith)]
  simp only [hcong]
  field_simp

/-- **The `q`-th moments, on one window.**  The constant comes out of the integral, and out of the
`q`-th power by `Real.mul_rpow`. -/
lemma integral_rpow_lineSqOf_window_eq (F : Ω → ArithmeticFunction ℂ) (ν : Measure Ω)
    {x : ℝ} (hx : 2 ≤ x) (σ q n : ℝ) :
    (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc n (n + 1),
        lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν)
      = ((2 * Real.pi)⁻¹ * Real.log x) ^ q
        * ∫ ω, chaosWindowShift F x σ n ω ^ q ∂ν := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hc0 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * Real.log x := by
    have := Real.pi_pos
    positivity
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [lineSqOf_window_eq_mul_chaosWindowShift F hx1 σ n ω,
    Real.mul_rpow hc0 (chaosWindowShift_nonneg hx σ n ω)]

/-- **Reflecting a window in the height leaves the windowed chaos unchanged**, almost surely:
the window at `−(n+1)` and the window at `n` have the same chaos.
`RMF.norm_randomEulerProductIco_sqfree_heightLine_neg` says `‖F(σ − ih)‖ = ‖F(σ + ih)‖` pointwise
on the realness set, and `intervalIntegral.integral_comp_neg` carries that across the window.  This
halves `RMF.windowMaxMoment`'s maximum over `ℤ` to `n ≥ 0`. -/
lemma chaosWindowShift_neg_rademacher {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (x σ n : ℝ) :
    ∀ᵐ ω ∂ν, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ
        (-(n + 1)) ω
      = chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ n ω := by
  filter_upwards [ae_forall_conj_eq_primesIco hY conj_eq_rademacherLaw 0 (⌊x⌋₊ + 1)] with ω hω
  have hrefl : ∀ h : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ (-h)) ω‖
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ h) ω‖ := by
    intro h
    have hkey := norm_randomEulerProductIco_sqfree_heightLine_neg (X := Y) (y₀ := 0)
      (y₁ := ⌊x⌋₊ + 1) (σ := 1 / 2 + σ) (h := h) hω
    simpa [shiftLine, heightLine] using hkey
  rw [chaosWindowShift, chaosWindowShift, show -(n + 1) + 1 = -n by ring,
    ← intervalIntegral.integral_comp_neg]
  congr 1
  refine intervalIntegral.integral_congr fun h _ => ?_
  rw [hrefl h]

/-- **Every integer window has a non-negative twin no further out.**  For `n ≥ 0` it is `n`
itself; for `n ≤ -1` the reflection sends `(n, n+1]` to `(-n-1, -n]`. -/
lemma exists_nat_window_eq_rademacher {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (x σ q : ℝ) (n : ℤ) :
    ∃ m : ℕ, (m : ℝ) ≤ |(n : ℝ)| ∧
      (∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ
          ((n : ℝ)) ω ^ q ∂ν)
        = ∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ
            ((m : ℝ)) ω ^ q ∂ν := by
  rcases le_or_gt 0 n with hn | hn
  · have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hn)
      push_cast at h
      linarith
    refine ⟨n.toNat, ?_, ?_⟩
    · rw [hcast]
      exact le_abs_self _
    · rw [hcast]
  · have hm0 : (0 : ℤ) ≤ -n - 1 := by omega
    have hcast : (((-n - 1).toNat : ℕ) : ℝ) = -(n : ℝ) - 1 := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hm0)
      push_cast at h
      linarith
    refine ⟨(-n - 1).toNat, ?_, ?_⟩
    · have habs : |(n : ℝ)| = -(n : ℝ) := abs_of_neg (by exact_mod_cast hn)
      rw [hcast, habs]
      linarith
    · have hne : (n : ℝ) = -((((-n - 1).toNat : ℕ) : ℝ) + 1) := by rw [hcast]; ring
      rw [hne]
      refine integral_congr_ae ?_
      filter_upwards [chaosWindowShift_neg_rademacher hY x σ
        ((((-n - 1).toNat : ℕ) : ℝ))] with ω hω
      rw [hω]

set_option maxHeartbeats 400000 in
-- three sources -- the pinned `(0,1]` window, a positive window, a reflected one -- and the two
-- monotonicities (in the window, and in the block offset) that put them on one scale
/-- **The chaos estimate at every integer window, at Harper's height range**, with `D₀`, `C`, `cr`
chosen before the tilt scale `E₀` and `d`, so a caller may choose the tilt scale afterwards; it
feeds `RMF.windowMaxMoment_le_of_split_damped`'s `hsmall`.  `n = 0` is
`RMF.exists_const_integral_chaosUnitShift_rpow_le_rademacher_of_top`, `n ≥ 1` is
`RMF.exists_const_integral_chaosWindowShift_rpow_le_rademacher_of_top`, and
`RMF.chaosWindowShift_neg_rademacher` sends `n ≤ -1` to `-n-1`. -/
theorem exists_const_integral_chaosWindowShift_rpow_le_int_rademacher_of_top :
    ∃ (D₀ : ℕ) (C cr : ℝ), 0 < C ∧ 0 < cr ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ η q : ℝ) (n : ℤ), x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          harperWindowLevel cr |(n : ℝ)| ≤ Real.log (Real.log x) / 3 →
          (∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ
              ((n : ℝ)) ω ^ q ∂ν)
            ≤ C * ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2
              * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₁, C₁, cr, hC₁, hcr, HW₀⟩ :=
    exists_const_integral_chaosWindowShift_rpow_le_rademacher_of_top (Ω' := Ω)
  obtain ⟨D₂, C₂, hC₂, HU₀⟩ :=
    exists_const_integral_chaosUnitShift_rpow_le_rademacher_of_top (Ω := Ω)
  refine ⟨max D₁ D₂, max C₁ C₂, cr,
    lt_of_lt_of_le hC₁ (le_max_left _ _), hcr, ?_⟩
  intro E₀ d hE₀ hE₁
  obtain ⟨x₁, HW⟩ := HW₀ E₀ d hE₀ hE₁
  obtain ⟨x₂, HU⟩ := HU₀ E₀ d hE₀ hE₁
  refine ⟨max x₁ x₂, ?_⟩
  intro Y ν hY x σ η q n hx hσ0 hη0 hηE hσ hq0 hq1 hcut
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  -- the target at the larger offset is the weaker one
  have hDmono : ∀ D : ℕ, D ≤ max D₁ D₂ →
      (1 + (1 - q) * Real.sqrt ((harperBlockCount D x / 4 : ℕ) : ℝ)) ^ (-q)
        ≤ (1 + (1 - q) * Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)) ^ (-q) := by
    intro D hD
    have hcount : harperBlockCount (max D₁ D₂) x ≤ harperBlockCount D x := by
      simp only [harperBlockCount]; omega
    have hcast : ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)
        ≤ ((harperBlockCount D x / 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_div_right hcount
    have hsq : Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)
        ≤ Real.sqrt ((harperBlockCount D x / 4 : ℕ) : ℝ) := Real.sqrt_le_sqrt hcast
    have hs0 : (0 : ℝ) ≤ Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ) :=
      Real.sqrt_nonneg _
    refine Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by linarith)
  -- the window, moved to a non-negative index
  obtain ⟨m, hm, heq⟩ := exists_nat_window_eq_rademacher hY x σ q n
  rw [heq]
  have hlev : harperWindowLevel cr (m : ℝ) ≤ harperWindowLevel cr |(n : ℝ)| :=
    harperWindowLevel_mono hcr (Nat.cast_nonneg m) hm
  have hceil : ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.ceil_mono hlev
  have hKn : (1 : ℝ) ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) ⌈harperWindowLevel cr |(n : ℝ)|⌉₊]
  have htarget0 : (0 : ℝ)
      ≤ (1 + (1 - q) * Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)) ^ (-q) :=
    Real.rpow_nonneg (by
      nlinarith [Real.sqrt_nonneg ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)]) _
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · -- the pinned window
    have hzero : ∀ ω : Ω, chaosWindowShift
        (fun ω => squarefreeExtension fun p => Y p ω) x σ (((0 : ℕ) : ℝ)) ω
        = chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ω := by
      intro ω
      rw [Nat.cast_zero, chaosWindowShift_zero]
    simp only [hzero]
    refine le_trans (HU Y ν hY x σ η q hx₂ hσ0 hη0 hηE hσ hq0 hq1) ?_
    have h1 := hDmono D₂ (le_max_right _ _)
    have h2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
    have h3 : (1 : ℝ) ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2 := by nlinarith
    have hmaxpos : (0 : ℝ) ≤ max C₁ C₂ := le_trans hC₂.le h2
    have h4 : C₂ ≤ max C₁ C₂ * ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left h3 hmaxpos]
    calc C₂ * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₂ x / 4 : ℕ) : ℝ)) ^ (-q)
        ≤ C₂ * (1 + (1 - q)
            * Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)) ^ (-q) :=
          mul_le_mul_of_nonneg_left h1 hC₂.le
      _ ≤ max C₁ C₂ * ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2
            * (1 + (1 - q)
              * Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)) ^ (-q) :=
          mul_le_mul_of_nonneg_right h4 htarget0
  · -- a genuine window, at `m ≥ 1`
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hcutm : harperWindowLevel cr (m : ℝ) ≤ Real.log (Real.log x) / 3 := le_trans hlev hcut
    have hsub : harperDwExp D₁ cr (m : ℝ) - D₁ = ⌈harperWindowLevel cr (m : ℝ)⌉₊ := by
      rw [harperDwExp]; omega
    have hW := HW Y ν hY x σ η q (m : ℝ) hx₁ hσ0 hη0 hηE hσ hq0 hq1 hm1R hcutm
    rw [hsub] at hW
    refine le_trans hW ?_
    have h1 := hDmono D₁ (le_max_left _ _)
    have h2 : C₁ ≤ max C₁ C₂ := le_max_left _ _
    have hKm : (0 : ℝ) ≤ ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℝ) + 1) := by
      linarith [Nat.cast_nonneg (α := ℝ) ⌈harperWindowLevel cr (m : ℝ)⌉₊]
    have hsqle : ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℝ) + 1) ^ 2
        ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2 := by nlinarith
    have hprod : C₁ * ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℝ) + 1) ^ 2
        ≤ max C₁ C₂ * ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2 := by nlinarith
    have hleft : (0 : ℝ) ≤ C₁ * ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℝ) + 1) ^ 2 := by positivity
    calc C₁ * ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℝ) + 1) ^ 2
          * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₁ x / 4 : ℕ) : ℝ)) ^ (-q)
        ≤ C₁ * ((⌈harperWindowLevel cr (m : ℝ)⌉₊ : ℝ) + 1) ^ 2
            * (1 + (1 - q)
              * Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)) ^ (-q) :=
          mul_le_mul_of_nonneg_left h1 hleft
      _ ≤ max C₁ C₂ * ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2
            * (1 + (1 - q)
              * Real.sqrt ((harperBlockCount (max D₁ D₂) x / 4 : ℕ) : ℝ)) ^ (-q) :=
          mul_le_mul_of_nonneg_right hprod htarget0

/-- **The window moments are non-negative** — `RMF.windowMaxMoment_le_of_split_damped`'s `hE0`. -/
lemma integral_rpow_lineSqOf_window_nonneg (F : Ω → ArithmeticFunction ℂ) (ν : Measure Ω)
    (x σ q n : ℝ) :
    (0 : ℝ) ≤ ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc n (n + 1),
        lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν :=
  integral_nonneg fun ω => Real.rpow_nonneg
    (mul_nonneg (by positivity) (integral_lineSqOf_nonneg _ _ _)) q

/-- **The crude bound, uniform in the window** — `RMF.windowMaxMoment_le_of_split_damped`'s
`hlarge`: `RMF.integral_rpow_setIntegral_normSq_shiftLine_le_rademacher` with the `(2π)⁻¹` carried
through `Real.mul_rpow`.  The right-hand side does not mention the window. -/
lemma integral_rpow_lineSqOf_window_le_rademacher {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q : ℝ} (hσ0 : 0 < 1 / 2 + σ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (x n : ℝ) :
    (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc n (n + 1),
        lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) ω t)
          ^ q ∂ν)
      ≤ ((2 * Real.pi)⁻¹ * ∫ ω, ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν)
        ^ q := by
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by
    have := Real.pi_pos
    positivity
  have hcong : ∀ (ω : Ω) (t : ℝ),
      lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) ω t
        = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ t) ω‖ ^ 2 := fun _ _ => rfl
  simp only [hcong]
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct
      (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν :=
    integral_nonneg fun ω => by positivity
  have hsplit : ∀ ω : Ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc n (n + 1),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ q
      = ((2 * Real.pi)⁻¹) ^ q * (∫ t in Set.Ioc n (n + 1),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q := by
    intro ω
    exact Real.mul_rpow hpi (setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity)
  rw [Real.mul_rpow hpi hZ0]
  calc (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc n (n + 1),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      = ((2 * Real.pi)⁻¹) ^ q * ∫ ω, (∫ t in Set.Ioc n (n + 1),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ ≤ ((2 * Real.pi)⁻¹) ^ q * (∫ ω, ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2
            ∂ν) ^ q :=
        mul_le_mul_of_nonneg_left
          (integral_rpow_setIntegral_normSq_shiftLine_le_rademacher hY (⌊x⌋₊ + 1) hσ0 n hq0 hq1)
          (Real.rpow_nonneg hpi q)

set_option maxHeartbeats 1000000 in
-- the split, both halves, and the choice of `N₀` that makes them meet
/-- **`RMF.windowMaxMoment` is bounded by a constant times the target**, with `D₀`, `C` chosen
before the tilt scale `E₀`, `d`: this is what Harper's Proposition 4 subtracts.  The sharp half
(`RMF.exists_const_integral_chaosWindowShift_rpow_le_int_rademacher_of_top`, out to
`N₀ = O((log log x)²)`) and the crude half (`RMF.integral_rpow_lineSqOf_window_le_rademacher`) are
joined by `RMF.windowMaxMoment_le_of_split_damped`: the sharp constant grows at most like
`(|n|+1)^{1/4}`, which the damping absorbs. -/
theorem exists_const_windowMaxMoment_le_rademacher_of_top :
    ∃ (D₀ : ℕ) (C : ℝ), 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x σ q ν
            ≤ C * ((2 * Real.pi)⁻¹ * Real.log x) ^ q
              * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₀, C₀, cr, hC₀, hcr, HS₀⟩ :=
    exists_const_integral_chaosWindowShift_rpow_le_int_rademacher_of_top (Ω := Ω)
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_shift_le_rademacher
  obtain ⟨A, hA0, hA⟩ := exists_const_harperWindowLevel_add_two_le hcr
  obtain ⟨Λ₃, hΛ₃1, hΛ₃⟩ := exists_threshold_harperWindowLevel_le 3 hcr
  set K : ℝ := max 1 CM / (C₀ * A ^ 2) with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount
    ⌈max (max Λ₃ (16 * (K + 1) ^ 4)) 1⌉₊ 0
  refine ⟨D₀, C₀ * A ^ 2, by positivity, ?_⟩
  intro E₀ d hE₀ hE₁
  obtain ⟨x₁, HS⟩ := HS₀ E₀ d hE₀ hE₁
  refine ⟨max (max x₁ x₂) 2, ?_⟩
  intro Y ν hY x σ η q hx hσ0 hη0 hηE hσ hq0 hq1
  haveI := hY.isProbabilityMeasure
  have hxa : max x₁ x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hxa
  obtain ⟨hxgt1, hLΛ, -⟩ := hx₂ x (le_trans (le_max_right _ _) hxa)
  have hσre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hxgt1
  have hpi : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 (by linarith [Real.pi_pos])
  have hMx := hMert Ω Y ν hY x σ hx2 hσ0
  set L : ℝ := Real.log (Real.log x) with hLdef
  have hLbig : max (max Λ₃ (16 * (K + 1) ^ 4)) 1 ≤ L := le_trans (Nat.le_ceil _) hLΛ
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_right _ _) hLbig
  have hLΛ₃ : Λ₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
  have hLK : 16 * (K + 1) ^ 4 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbig
  have hs0 : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  have hs1 : (1 : ℝ) ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hL1
    rwa [Real.sqrt_one] at h
  have hcountL : ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) ≤ L := by
    have h1 : harperBlockCount D₀ x / 4 ≤ ⌊L⌋₊ := by
      simp only [harperBlockCount, ← hLdef]; omega
    have h2 : ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) ≤ ((⌊L⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ L)]
  have hcs : Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt hcountL
  have hcs0 : (0 : ℝ) ≤ Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := Real.sqrt_nonneg _
  set V : ℝ := 1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) with hVdef
  have hV1 : (1 : ℝ) ≤ V := by rw [hVdef]; nlinarith
  have hVL : V ≤ 1 + Real.sqrt L := by rw [hVdef]; nlinarith
  have hVinv : V ^ (-(1 : ℝ)) ≤ V ^ (-q) :=
    Real.rpow_le_rpow_of_exponent_le hV1 (by linarith)
  have hVeq : V ^ (-(1 : ℝ)) = V⁻¹ := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ V), Real.rpow_one]
  have hVq0 : (0 : ℝ) < V ^ (-q) := Real.rpow_pos_of_pos (by linarith) _
  set Z : ℝ := ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν with hZdef
  have hZ0 : (0 : ℝ) ≤ Z := by
    rw [hZdef]
    exact integral_nonneg fun ω => by positivity
  have hZM : Z ≤ CM * Real.log x := by
    have h2 := mul_le_mul_of_nonneg_left hMx hlog.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlog), one_mul] at h2
    linarith
  set Pn : ℝ := ((2 * Real.pi)⁻¹ * Real.log x) ^ q with hPdef
  have hP0 : (0 : ℝ) < Pn := by
    rw [hPdef]
    exact Real.rpow_pos_of_pos (by positivity) _
  -- the crude half
  have hB : ∀ n : ℤ, (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
      lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) ω t)
        ^ q ∂ν) ≤ Pn * max 1 CM := by
    intro n
    refine le_trans (integral_rpow_lineSqOf_window_le_rademacher hY hσre hq0 hq1 x (n : ℝ)) ?_
    have h1 : ((2 * Real.pi)⁻¹ * Z) ^ q ≤ ((2 * Real.pi)⁻¹ * (CM * Real.log x)) ^ q :=
      Real.rpow_le_rpow (mul_nonneg hpi.le hZ0)
        (mul_le_mul_of_nonneg_left hZM hpi.le) hq0
    have hid : ((2 * Real.pi)⁻¹ * (CM * Real.log x)) ^ q = Pn * CM ^ q := by
      rw [hPdef, ← Real.mul_rpow (mul_nonneg hpi.le hlog.le) hCM.le]
      congr 1
      ring
    have h2 : CM ^ q ≤ max 1 CM := rpow_le_max_one hCM hq0 hq1
    have h3 : Pn * CM ^ q ≤ Pn * max 1 CM := mul_le_mul_of_nonneg_left h2 hP0.le
    rw [hid] at h1
    linarith
  -- the window out to which the sharp bound is used
  set G : ℝ := K * (1 + Real.sqrt L) with hGdef
  have hG0 : 0 < G := by rw [hGdef]; positivity
  set N₀ : ℕ := ⌈G⌉₊ ^ 4 with hN₀def
  have hN₀R : (N₀ : ℝ) = ((⌈G⌉₊ : ℕ) : ℝ) ^ 4 := by rw [hN₀def]; push_cast; ring
  have hGceil : G ≤ ((⌈G⌉₊ : ℕ) : ℝ) := Nat.le_ceil G
  have hN₀G : G ^ 4 ≤ (N₀ : ℝ) := by
    rw [hN₀R]
    exact pow_le_pow_left₀ hG0.le hGceil 4
  have hceilG : ((⌈G⌉₊ : ℕ) : ℝ) ≤ G + 1 := (Nat.ceil_lt_add_one hG0.le).le
  have hGL : G + 1 ≤ (K + 1) * (2 * Real.sqrt L) := by
    rw [hGdef]
    nlinarith [hs1, hK0]
  have hsq4 : Real.sqrt L ^ 4 = L ^ 2 := by
    calc Real.sqrt L ^ 4 = (Real.sqrt L ^ 2) ^ 2 := by ring
      _ = L ^ 2 := by rw [hs]
  have hN₀L : (N₀ : ℝ) ≤ L ^ 3 := by
    have h0 : (0 : ℝ) ≤ ((⌈G⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((⌈G⌉₊ : ℕ) : ℝ) ≤ (K + 1) * (2 * Real.sqrt L) := by linarith
    have h1 : (N₀ : ℝ) ≤ ((K + 1) * (2 * Real.sqrt L)) ^ 4 := by
      rw [hN₀R]
      exact pow_le_pow_left₀ h0 hle 4
    have h2 : ((K + 1) * (2 * Real.sqrt L)) ^ 4 = 16 * (K + 1) ^ 4 * L ^ 2 := by
      have hexp : ((K + 1) * (2 * Real.sqrt L)) ^ 4
          = 16 * (K + 1) ^ 4 * Real.sqrt L ^ 4 := by ring
      rw [hexp, hsq4]
    have h3 : 16 * (K + 1) ^ 4 * L ^ 2 ≤ L ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hLK (sq_nonneg L)
      calc 16 * (K + 1) ^ 4 * L ^ 2 ≤ L * L ^ 2 := h
        _ = L ^ 3 := by ring
    linarith
  have hcutN₀ : harperWindowLevel cr (N₀ : ℝ) ≤ L / 3 :=
    hΛ₃ L (N₀ : ℝ) hLΛ₃ (Nat.cast_nonneg _) hN₀L
  -- the sharp half, damped
  have hsmall : ∀ n : ℤ, |n| ≤ (N₀ : ℤ) →
      (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
        * (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
          lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) ω t)
            ^ q ∂ν) ≤ C₀ * A ^ 2 * Pn * V ^ (-q) := by
    intro n hn
    have habs0 : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
    have hnN : |(n : ℝ)| ≤ (N₀ : ℝ) := by
      have h : ((|n| : ℤ) : ℝ) ≤ ((N₀ : ℤ) : ℝ) := by exact_mod_cast hn
      rw [Int.cast_abs] at h
      push_cast at h ⊢
      linarith
    have hcutn : harperWindowLevel cr |(n : ℝ)| ≤ L / 3 :=
      le_trans (harperWindowLevel_mono hcr habs0 hnN) hcutN₀
    have hsharp := HS Y ν hY x σ η q n hx₁ hσ0 hη0 hηE hσ hq0 hq1 hcutn
    have hlvl0 : (0 : ℝ) ≤ harperWindowLevel cr |(n : ℝ)| := harperWindowLevel_nonneg _ _
    have hceil : ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ)
        ≤ harperWindowLevel cr |(n : ℝ)| + 1 := (Nat.ceil_lt_add_one hlvl0).le
    have hpow : ((|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2 = (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast ((|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hA8 : harperWindowLevel cr |(n : ℝ)| + 2 ≤ A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8) :=
      hA _ habs0
    have hlevel : (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
        ≤ A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
      have h1 : ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1
          ≤ A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8) := by linarith
      have h0 : (0 : ℝ) ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) ⌈harperWindowLevel cr |(n : ℝ)|⌉₊]
      have hsq := pow_le_pow_left₀ h0 h1 2
      have hexp : (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2
          = A ^ 2 * ((|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2 := by ring
      rw [hexp, hpow] at hsq
      exact hsq
    have hIle : (∫ ω, chaosWindowShift
        (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω ^ q ∂ν)
        ≤ C₀ * (A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * V ^ (-q) :=
      le_trans hsharp
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlevel hC₀.le) hVq0.le)
    have hd0 : (0 : ℝ) ≤ (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have hcancel : (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num
    rw [integral_rpow_lineSqOf_window_eq (fun ω => squarefreeExtension fun p => Y p ω) ν hx2
      σ q ((n : ℝ)), ← hPdef]
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIle hP0.le) hd0
    refine le_trans h3 (le_of_eq ?_)
    calc (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
          * (Pn * (C₀ * (A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * V ^ (-q)))
        = ((|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
            * (C₀ * A ^ 2 * Pn * V ^ (-q)) := by ring
      _ = C₀ * A ^ 2 * Pn * V ^ (-q) := by rw [hcancel]; ring
  -- the far branch fits, by the choice of `N₀`
  have hM1 : (1 : ℝ) ≤ max 1 CM := le_max_left _ _
  have hCA0 : (0 : ℝ) < C₀ * A ^ 2 := by positivity
  have hVinv2 : (1 : ℝ) / (1 + Real.sqrt L) ≤ V ^ (-q) := by
    have h1 : V⁻¹ ≤ V ^ (-q) := by rw [← hVeq]; exact hVinv
    have h2 : (1 : ℝ) / (1 + Real.sqrt L) ≤ 1 / V :=
      one_div_le_one_div_of_le (by linarith) hVL
    rw [one_div V] at h2
    linarith
  have hNB : ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) * (Pn * max 1 CM)
      ≤ C₀ * A ^ 2 * Pn * V ^ (-q) := by
    have hG4 : G ≤ ((N₀ : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
      have h1 : G ^ (4 : ℕ) ≤ (N₀ : ℝ) + 1 := by linarith [hN₀G]
      have h2 : (G ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ ((N₀ : ℝ) + 1) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      have h3 : (G ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = G := by
        rw [← Real.rpow_natCast G 4, ← Real.rpow_mul hG0.le]
        norm_num
      rw [h3] at h2
      exact h2
    have hneg : ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) = (((N₀ : ℝ) + 1) ^ ((1 : ℝ) / 4))⁻¹ := by
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ (N₀ : ℝ) + 1)]
    have hinv : ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) ≤ G⁻¹ := by
      rw [hneg]
      simpa [one_div] using one_div_le_one_div_of_le hG0 hG4
    have hkey : G⁻¹ * max 1 CM ≤ C₀ * A ^ 2 * V ^ (-q) := by
      have heq : G⁻¹ * max 1 CM = C₀ * A ^ 2 * (1 / (1 + Real.sqrt L)) := by
        rw [hGdef, hKdef]
        have hm0 : max 1 CM ≠ 0 := by positivity
        have hca : C₀ * A ^ 2 ≠ 0 := ne_of_gt hCA0
        have hsl : 1 + Real.sqrt L ≠ 0 := by positivity
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hVinv2 hCA0.le
    have hPk := mul_le_mul_of_nonneg_left hkey hP0.le
    have hstep : G⁻¹ * (Pn * max 1 CM) ≤ C₀ * A ^ 2 * Pn * V ^ (-q) := by
      have hid : G⁻¹ * (Pn * max 1 CM) = Pn * (G⁻¹ * max 1 CM) := by ring
      rw [hid]
      exact le_trans hPk (le_of_eq (by ring))
    exact le_trans (mul_le_mul_of_nonneg_right hinv (by positivity)) hstep
  exact windowMaxMoment_le_of_split_damped
    (fun n => integral_rpow_lineSqOf_window_nonneg _ ν x σ q _) hsmall hB hNB

/-! ### The normalisation bridge, and Harper's upper bound through the window

`RMF.reduction_upper_max_rademacher` states its maximum with `(\log y)⁻¹` in front of the window
integral; `RMF.windowMaxMoment` uses `(2π)⁻¹`.  The two differ by a constant *inside* a `q`-th
power, so the scale factors out — and it factors out **exactly**: the `((2π)⁻¹\log y)^q` that
`RMF.exists_const_windowMaxMoment_le_rademacher_of_top` carries is the reciprocal of the
`((\log y)⁻¹ 2π)^q` the bridge produces, so the composite has no `y` in its main term at all.

That is the Rademacher analogue of what `RMF.reduction_upper_unitIntegral` and the chaos estimate
do on the Steinhaus side, with the maximum of Harper's Proposition 2 in place of the unit window. -/

/-- **The reduction's maximum, renormalised to `RMF.windowMaxMoment`.**

Bounding a single window by the supremum needs the family bounded above, and
`RMF.integral_rpow_lineSqOf_window_le_rademacher` supplies exactly that — a bound with no window
in it.  The damping factor is at most `1`, so it does not disturb the bound. -/
lemma iSup_lineSqOf_window_log_le_windowMaxMoment_rademacher {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {y q : ℝ} (hy : 2 ≤ y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
        * ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
            lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) ω t)
          ^ q ∂ν)
      ≤ ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q
        * windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) y 0 q ν := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hc0 : (0 : ℝ) ≤ (Real.log y)⁻¹ * (2 * Real.pi) := by positivity
  -- the window moments, at `σ = 0`
  obtain ⟨E, hEdef⟩ : ∃ E : ℤ → ℝ, E = fun n : ℤ =>
      ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) ω t) ^ q ∂ν :=
    ⟨_, rfl⟩
  have hE0 : ∀ n : ℤ, (0 : ℝ) ≤ E n := by
    intro n
    rw [hEdef]
    simpa only [add_zero] using integral_rpow_lineSqOf_window_nonneg
      (fun ω => squarefreeExtension fun p => Y p ω) ν y 0 q (n : ℝ)
  have hEb : ∀ n : ℤ, E n ≤ ((2 * Real.pi)⁻¹ * ∫ ω, ‖randomEulerProduct
      (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν) ^ q := by
    intro n
    rw [hEdef]
    simpa only [add_zero] using
      integral_rpow_lineSqOf_window_le_rademacher hY (σ := 0) (by norm_num) hq0 hq1 y (n : ℝ)
  -- the damped family, which is `RMF.windowMaxMoment` at `σ = 0`
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ → ℝ, g = fun n : ℤ => (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * E n :=
    ⟨_, rfl⟩
  have hwm : windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) y 0 q ν
      = ⨆ n : ℤ, g n := by
    rw [hgdef, hEdef, windowMaxMoment]
    simp only [add_zero]
  have hdamp : ∀ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg ((n : ℝ))]) (by norm_num)
  have hbdd : BddAbove (Set.range g) := by
    refine ⟨((2 * Real.pi)⁻¹ * ∫ ω, ‖randomEulerProduct
      (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν) ^ q, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [hgdef]
    calc (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * E n ≤ 1 * E n :=
          mul_le_mul_of_nonneg_right (hdamp n) (hE0 n)
      _ = E n := one_mul _
      _ ≤ _ := hEb n
  -- the scale, pulled out of the `q`-th power window by window
  have hscale : ∀ I : ℝ, (Real.log y)⁻¹ * I
      = ((Real.log y)⁻¹ * (2 * Real.pi)) * ((2 * Real.pi)⁻¹ * I) := by
    intro I
    rw [mul_assoc, ← mul_assoc (2 * Real.pi), mul_inv_cancel₀ (ne_of_gt hπ), one_mul]
  have hterm : ∀ n : ℤ, (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) ω t) ^ q ∂ν)
      = ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q * E n := by
    intro n
    rw [hEdef, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [hscale (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
      lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) ω t)]
    exact Real.mul_rpow hc0 (mul_nonneg (by positivity)
      (integral_lineSqOf_nonneg (1 / 2) ((n : ℝ)) ((n : ℝ) + 1)))
  rw [hwm]
  refine ciSup_le fun n => ?_
  calc (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
        * ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
            lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => Y p ω) (⌊y⌋₊ + 1) ω t)
          ^ q ∂ν
      = ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q * g n := by rw [hterm n, hgdef]; ring
    _ ≤ ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q * ⨆ m : ℤ, g m :=
        mul_le_mul_of_nonneg_left (le_ciSup hbdd n) (Real.rpow_nonneg hc0 q)

/-- **Harper's upper bound for the Rademacher function, at the Euler-product cutoff**:
`RMF.reduction_upper_max_rademacher` (the shape of Harper's Proposition 2) composed with
`RMF.exists_const_windowMaxMoment_le_rademacher_of_top` (the chaos estimate on a window).  The two
normalisations cancel exactly, so the main term is the bare target.  `RMF.harper_upper_rademacher`
adds the cutoff numerics, all law-free: `RMF.harperCutoff`, the trade of the block count for
`ℓogℓog x`, and the `L^p` packaging of `RMF.normalisedSum`. -/
theorem exists_const_harper_upper_window_rademacher :
    ∃ (D₀ : ℕ) (x₀ C K c : ℝ) (y₀ : ℕ), 0 < C ∧ 0 ≤ K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ (Y : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues Y μ →
        ∀ (x : ℝ) (y : ℕ) (q : ℝ), y₀ ≤ y → x₀ ≤ (y : ℝ) →
          5 * (y : ℝ) * (1 + Real.log y) ^ 3 * Real.log y ≤ Real.sqrt x / 2 →
          2 / 3 ≤ q → q ≤ 1 →
          ∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => Y p ω) x ω‖ ^ (2 * q) ∂μ
            ≤ C * (1 + (1 - q)
                  * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q)
              + C * (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q := by
  obtain ⟨C₁, K, c, y₀, hC₁, hK, hc, hy₀, hred⟩ := reduction_upper_max_rademacher (Ω := Ω)
  obtain ⟨D₀, C₂, hC₂, hwin₀⟩ :=
    exists_const_windowMaxMoment_le_rademacher_of_top (Ω := Ω)
  obtain ⟨x₁, hwin⟩ := hwin₀ 0 0 le_rfl (by norm_num)
  refine ⟨D₀, x₁, C₁ * (C₂ + 1), K, c, y₀, by positivity, hK, hc, hy₀, ?_⟩
  intro Y μ hY x y q hy₀y hx₁y hyx hq23 hq1
  have hy0N : (2 : ℕ) ≤ y := le_trans hy₀ hy₀y
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0N
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  -- the target, and the error, are non-negative
  have hT0 : (0 : ℝ) ≤ (1 + (1 - q)
      * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q) :=
    Real.rpow_nonneg (by positivity) _
  have herr0 : (0 : ℝ) ≤ (Real.log y ^ K * Real.exp (-c * Real.log x / Real.log y)) ^ q :=
    (Real.rpow_pos_of_pos
      (mul_pos (Real.rpow_pos_of_pos hlog _) (Real.exp_pos _)) q).le
  -- the two scales cancel
  have hcancel : ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q * ((2 * Real.pi)⁻¹ * Real.log y) ^ q
      = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      show ((Real.log y)⁻¹ * (2 * Real.pi)) * ((2 * Real.pi)⁻¹ * Real.log y) = 1 by
        field_simp,
      Real.one_rpow]
  have hbridge := iSup_lineSqOf_window_log_le_windowMaxMoment_rademacher hY hy2 hq0 hq1
  have hw := hwin Y μ hY (y : ℝ) 0 0 q hx₁y le_rfl le_rfl le_rfl
    (by simp) hq0 hq1
  have hmain : (⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
        * ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
            lineSqOf (1 / 2) (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊(y : ℝ)⌋₊ + 1) ω t) ^ q ∂μ)
      ≤ C₂ * (1 + (1 - q)
          * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q) := by
    refine hbridge.trans ?_
    calc ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q
          * windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) (y : ℝ) 0 q μ
        ≤ ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q
            * (C₂ * ((2 * Real.pi)⁻¹ * Real.log y) ^ q
              * (1 + (1 - q)
                * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q)) :=
          mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg (by positivity) q)
      _ = C₂ * (1 + (1 - q)
            * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q) := by
          rw [show ((Real.log y)⁻¹ * (2 * Real.pi)) ^ q
              * (C₂ * ((2 * Real.pi)⁻¹ * Real.log y) ^ q
                * (1 + (1 - q)
                  * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q))
              = (((Real.log y)⁻¹ * (2 * Real.pi)) ^ q
                  * ((2 * Real.pi)⁻¹ * Real.log y) ^ q)
                * (C₂ * (1 + (1 - q)
                  * Real.sqrt ((harperBlockCount D₀ (y : ℝ) / 4 : ℕ) : ℝ)) ^ (-q)) from by ring,
            hcancel, one_mul]
  have hstep := hred Y μ hY x y q hy₀y hyx hq23 hq1
  have hprod := mul_le_mul_of_nonneg_left hmain hC₁.le
  linarith [hstep, hprod, mul_nonneg hC₁.le hT0,
    mul_nonneg (mul_nonneg hC₁.le hC₂.le) herr0]

set_option maxHeartbeats 400000 in
-- the assembly of the reduction is long; the limit is the one its Steinhaus counterpart needed
/-- **Harper's Proposition 4, with the maximum estimated.**
`RMF.reduction_lower_chaosShift_rademacher` carries `RMF.windowMaxMoment` symbolically;
`RMF.exists_const_windowMaxMoment_le_rademacher_of_top` bounds it, and this is the two composed.

    ‖∑_{n≤x} f(n)‖_{2q} ≫ √(x/ℓog x)·( ‖∫_{-½}^{½}|F(½+4V/ℓog x+it)|²dt‖_q^{1/2}
                                − √(ℓog x)·(C/e^V)·(1 + (1-q)√(n/4))^{-1/2} − C )

With the maximum estimated, the subtracted term has the same shape as the main one and only
`C/e^V` separates them, which is the form Harper's remark after Proposition 4 asks for.  The
`ℓog x` cancels exactly, and the `2q`-th root turns the target's exponent `-q` into `-1/2`.
`2V ≤ E₀` is carried: the window bound reads the chaos at `|σ|·ℓog x = 2V`, and the variance bracket
holds only up to `E₀`.  Since `C` does not depend on `E₀`, a caller may take `E₀ = 2V` for each `V`,
which `RMF.reduction_lower_chaosShift_rademacher_absorbed` does. -/
theorem reduction_lower_chaosShift_rademacher_uniform :
    ∃ (D₀ : ℕ) (c C V₀ : ℝ), 0 < c ∧ 0 < C ∧ 0 < V₀ ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d →
      ∀ V : ℝ, V₀ ≤ V → 2 * V ≤ E₀ → ∃ x₀ : ℝ,
        ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
          ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
            c * ((∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x
                    (4 * V / Real.log x) ω ^ q ∂ν) ^ (1 / (2 * q))
                  - C / Real.exp V
                      * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
                          ^ (-(1 / 2) : ℝ)
                  - C / Real.sqrt (Real.log x))
              ≤ (∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => Y p ω) x ω‖
                  ^ (2 * q) ∂ν) ^ (1 / (2 * q)) := by
  obtain ⟨c, C, V₀, hc, hC, hV₀, H⟩ := reduction_lower_chaosShift_rademacher (Ω := Ω)
  obtain ⟨D₀, Cw, hCw, HW₀⟩ :=
    exists_const_windowMaxMoment_le_rademacher_of_top (Ω := Ω)
  have hM1 : (1 : ℝ) ≤ max 1 Cw := le_max_left _ _
  refine ⟨D₀, c, C * max 1 Cw, V₀, hc, by positivity, hV₀, ?_⟩
  intro E₀ d hE₀ hE₁ V hV hVE
  obtain ⟨xw, HW⟩ := HW₀ E₀ d hE₀ hE₁
  obtain ⟨x₀, Hx⟩ := H V hV
  refine ⟨max (max x₀ xw) 2, fun Y ν hY x q hx hq23 hq1 => ?_⟩
  have hxa : max x₀ xw ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hxa
  have hxw : xw ≤ x := le_trans (le_max_right _ _) hxa
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hV0 : (0 : ℝ) < V := lt_of_lt_of_le hV₀ hV
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hr1 : 1 / (2 * q) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  refine le_trans ?_ (Hx Y ν hY x q hx₀ hq23 hq1)
  -- the window maximum, at the tilt the statement reads it
  set σ : ℝ := 2 * V / Real.log x with hσdef
  have hσ0 : (0 : ℝ) ≤ σ := by rw [hσdef]; positivity
  have hσx : |σ| * Real.log x ≤ 2 * V := by
    rw [abs_of_nonneg hσ0, hσdef, div_mul_cancel₀ _ (ne_of_gt hlog)]
  have hwmm := HW Y ν hY x σ (2 * V) q hxw hσ0 (by linarith) hVE hσx hq0.le hq1
  set Vc : ℝ := 1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) with hVcdef
  have hcs0 : (0 : ℝ) ≤ Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hVc1 : (1 : ℝ) ≤ Vc := by rw [hVcdef]; nlinarith
  have hVc0 : (0 : ℝ) < Vc := by linarith
  have hpi : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 (by linarith [Real.pi_pos])
  have hpile : (2 * Real.pi)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hmul : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 :=
      inv_mul_cancel₀ (by linarith [Real.pi_pos] : (2 : ℝ) * Real.pi ≠ 0)
    nlinarith [mul_le_mul_of_nonneg_right h1 hpi.le]
  have hpi1 : ((2 * Real.pi)⁻¹) ^ q ≤ 1 := Real.rpow_le_one hpi.le hpile hq0.le
  have hlq0 : (0 : ℝ) < Real.log x ^ q := Real.rpow_pos_of_pos hlog _
  have hVq0 : (0 : ℝ) < Vc ^ (-q) := Real.rpow_pos_of_pos hVc0 _
  -- divide by `ℓog^q x`, which the bound's own `((2π)⁻¹ℓog x)^q` cancels
  have hdiv : windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x σ q ν
      / Real.log x ^ q ≤ Cw * Vc ^ (-q) := by
    rw [div_le_iff₀ hlq0]
    refine le_trans hwmm ?_
    have hsplit : ((2 * Real.pi)⁻¹ * Real.log x) ^ q
        = ((2 * Real.pi)⁻¹) ^ q * Real.log x ^ q := Real.mul_rpow hpi.le hlog.le
    have hrest : (0 : ℝ) ≤ Cw * Real.log x ^ q * Vc ^ (-q) :=
      mul_nonneg (mul_nonneg hCw.le hlq0.le) hVq0.le
    rw [hsplit]
    calc Cw * (((2 * Real.pi)⁻¹) ^ q * Real.log x ^ q) * Vc ^ (-q)
        = ((2 * Real.pi)⁻¹) ^ q * (Cw * Real.log x ^ q * Vc ^ (-q)) := by ring
      _ ≤ 1 * (Cw * Real.log x ^ q * Vc ^ (-q)) := mul_le_mul_of_nonneg_right hpi1 hrest
      _ = Cw * Vc ^ (-q) * Real.log x ^ q := by ring
  -- and take the `2q`-th root
  have hwnn : (0 : ℝ) ≤ windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x σ q ν
      / Real.log x ^ q :=
    div_nonneg (windowMaxMoment_nonneg _ _ _ _ _) hlq0.le
  have hroot : (windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x σ q ν
      / Real.log x ^ q) ^ (1 / (2 * q)) ≤ max 1 Cw * Vc ^ (-(1 / 2) : ℝ) := by
    refine le_trans (Real.rpow_le_rpow hwnn hdiv hr0.le) ?_
    have hsplit : (Cw * Vc ^ (-q)) ^ (1 / (2 * q))
        = Cw ^ (1 / (2 * q)) * (Vc ^ (-q)) ^ (1 / (2 * q)) :=
      Real.mul_rpow hCw.le hVq0.le
    have hexp : (Vc ^ (-q)) ^ (1 / (2 * q)) = Vc ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_mul hVc0.le]
      congr 1
      field_simp
    have hCle : Cw ^ (1 / (2 * q)) ≤ max 1 Cw := rpow_le_max_one hCw hr0.le hr1
    rw [hsplit, hexp]
    exact mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg hVc0.le _)
  -- the subtracted terms only grow, so the bound only weakens
  have hexpV : (0 : ℝ) < Real.exp V := Real.exp_pos V
  have hstep : C / Real.exp V
      * (windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x σ q ν
          / Real.log x ^ q) ^ (1 / (2 * q))
      ≤ C * max 1 Cw / Real.exp V * Vc ^ (-(1 / 2) : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ C / Real.exp V)
    refine le_trans h1 (le_of_eq ?_)
    ring
  have hsq : C / Real.sqrt (Real.log x) ≤ C * max 1 Cw / Real.sqrt (Real.log x) := by
    have hCM : C ≤ C * max 1 Cw := by nlinarith
    have hinv : (0 : ℝ) ≤ (Real.sqrt (Real.log x))⁻¹ := by positivity
    calc C / Real.sqrt (Real.log x) = C * (Real.sqrt (Real.log x))⁻¹ := by ring
      _ ≤ C * max 1 Cw * (Real.sqrt (Real.log x))⁻¹ := mul_le_mul_of_nonneg_right hCM hinv
      _ = C * max 1 Cw / Real.sqrt (Real.log x) := by ring
  exact mul_le_mul_of_nonneg_left (by linarith) hc.le

set_option maxHeartbeats 400000 in
-- the assembly of the reduction is long; the limit is the one its Steinhaus counterpart needed
/-- **The Rademacher lower reduction, with its subtracted terms absorbed and no tilt scale left
in the statement** — the twin of `RMF.reduction_lower_chaosShift_absorbed`, and the form Harper's
Proposition 4 is used in: for every `V ≥ V₀`,

`c·( A^{1/(2q)} − C₀ e^{-V} W^{-1/2} ) ≤ (E|S_x|^{2q})^{1/(2q)}`,  `W = 1 + (1-q)√ℓogℓog x`,

with `c`, `C₀`, `V₀` independent of `V`, `Y`, `ν`, `x`, `q`.  Of the terms
`RMF.reduction_lower_chaosShift_rademacher_uniform` leaves, the collar `C/√ℓog x` is absorbed as in
the Steinhaus twin, and the window term by `(1 + (1-q)√(n/4))^{-1/2} ≤ 2·W^{-1/2}` once
`ℓogℓog x ≥ 4D₀ + 16`.  The tilt scale is chosen inside, `E₀ := 2V` and `d := ⌈20V⌉`, which the
uniformity of the tower below in `E₀` and `d` permits; with `E₀` fixed first, `C₀` could depend on
`E₀` while `2V ≤ E₀` caps `V`, and the choice of `V` against `C₀` would be circular. -/
theorem reduction_lower_chaosShift_rademacher_absorbed :
    ∃ c C₀ V₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < V₀ ∧
      ∀ V : ℝ, V₀ ≤ V → ∃ x₀ : ℝ,
        ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
          ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
            c * ((∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x
                    (4 * V / Real.log x) ω ^ q ∂ν) ^ (1 / (2 * q))
                  - C₀ / Real.exp V
                      * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ))
              ≤ (∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => Y p ω) x ω‖
                  ^ (2 * q) ∂ν) ^ (1 / (2 * q)) := by
  obtain ⟨D₀, c, C, V₀, hc, hC, hV₀, H⟩ :=
    reduction_lower_chaosShift_rademacher_uniform (Ω := Ω)
  refine ⟨c, 3 * C, V₀, hc, by positivity, hV₀, ?_⟩
  intro V hV
  have hV0 : (0 : ℝ) ≤ V := le_trans hV₀.le hV
  have hd : 10 * (2 * V) ≤ Real.exp ((⌈20 * V⌉₊ : ℕ) : ℝ) := by
    have h1 : (20 : ℝ) * V ≤ ((⌈20 * V⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith [Real.add_one_le_exp ((⌈20 * V⌉₊ : ℕ) : ℝ)]
  obtain ⟨x₁, Hx⟩ := H (2 * V) ⌈20 * V⌉₊ (by linarith) hd V hV le_rfl
  refine ⟨max x₁ (Real.exp (Real.exp (max (4 * V + 16) (4 * (D₀ : ℝ) + 16)))), ?_⟩
  intro Y ν hY x q hx hq23 hq1
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp (Real.exp (max (4 * V + 16) (4 * (D₀ : ℝ) + 16))) ≤ x :=
    le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hlogx : Real.exp (max (4 * V + 16) (4 * (D₀ : ℝ) + 16)) ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 hxe
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx
  have hLmax : max (4 * V + 16) (4 * (D₀ : ℝ) + 16) ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le hlogx0).2 hlogx
  have hL : 4 * V + 16 ≤ Real.log (Real.log x) := le_trans (le_max_left _ _) hLmax
  have hLD : 4 * (D₀ : ℝ) + 16 ≤ Real.log (Real.log x) := le_trans (le_max_right _ _) hLmax
  have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) < q := by linarith
  -- the shape factor
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  have hW1 : (1 : ℝ) ≤ 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by nlinarith
  have hW0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by linarith
  have hWle : 1 + (1 - q) * Real.sqrt (Real.log (Real.log x))
      ≤ 1 + Real.sqrt (Real.log (Real.log x)) := by nlinarith
  have hWr0 : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_nonneg hW0.le _
  have hhalf : ∀ z : ℝ, 0 ≤ z → z ^ (-(1 / 2) : ℝ) = (Real.sqrt z)⁻¹ := by
    intro z hz
    rw [Real.rpow_neg hz, ← Real.sqrt_eq_rpow]
  -- the block count against `ℓogℓog x`
  have hfl : Real.log (Real.log x) - 1 < (⌊Real.log (Real.log x)⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have hnN : 4 * D₀ + 15 ≤ ⌊Real.log (Real.log x)⌋₊ := by
    have h : ((4 * D₀ + 15 : ℕ) : ℝ) ≤ ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  have hcnt : Real.log (Real.log x) ≤ 16 * ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := by
    have hnat : 4 * ⌊Real.log (Real.log x)⌋₊
        ≤ 16 * (harperBlockCount D₀ x / 4) + 4 * D₀ + 12 := by
      simp only [harperBlockCount]
      omega
    have hcast : (4 : ℝ) * ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ)
        ≤ 16 * ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) + 4 * (D₀ : ℝ) + 12 := by
      exact_mod_cast hnat
    linarith
  set Wc : ℝ := 1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) with hWcdef
  have hcs0 : (0 : ℝ) ≤ Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hWc1 : (1 : ℝ) ≤ Wc := by rw [hWcdef]; nlinarith
  have hWc0 : (0 : ℝ) < Wc := by linarith
  have hsq16 : Real.sqrt (Real.log (Real.log x))
      ≤ 4 * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := by
    have h1 := Real.sqrt_le_sqrt hcnt
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
      show Real.sqrt 16 = 4 from by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
  have hW4 : 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) ≤ 4 * Wc := by
    rw [hWcdef]
    nlinarith
  -- so the window term is at most twice the shape
  have hWconv : Wc ^ (-(1 / 2) : ℝ)
      ≤ 2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
    have hsc0 : (0 : ℝ) < Real.sqrt Wc := Real.sqrt_pos.2 hWc0
    have hsW0 : (0 : ℝ) < Real.sqrt (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) :=
      Real.sqrt_pos.2 hW0
    have hroot : Real.sqrt (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))
        ≤ 2 * Real.sqrt Wc := by
      have h := Real.sqrt_le_sqrt hW4
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt 4 = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    rw [hhalf _ hWc0.le, hhalf _ hW0.le]
    have hinv := one_div_le_one_div_of_le hsW0 hroot
    rw [one_div, one_div] at hinv
    have hid : (2 * Real.sqrt Wc)⁻¹ = 2⁻¹ * (Real.sqrt Wc)⁻¹ := by
      rw [mul_inv]
    rw [hid] at hinv
    linarith
  -- the collar, exactly as in the Steinhaus twin
  have hsqrtL : Real.sqrt (Real.log (Real.log x)) ≤ Real.log (Real.log x) / 4 := by
    have hle : Real.log (Real.log x) ≤ (Real.log (Real.log x) / 4) ^ 2 := by nlinarith
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by linarith)] at h
  have hsqrtlogx : Real.sqrt (Real.log x) = Real.exp (Real.log (Real.log x) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlogx0]
    congr 1
    ring
  have hV0 : (0 : ℝ) ≤ V := le_trans hV₀.le hV
  have hev : Real.exp V * (1 + Real.sqrt (Real.log (Real.log x))) ≤ Real.sqrt (Real.log x) := by
    have hq1' : Real.exp V ≤ Real.exp (Real.log (Real.log x) / 4) :=
      Real.exp_le_exp.2 (by linarith)
    have hq2 : 1 + Real.sqrt (Real.log (Real.log x))
        ≤ Real.exp (Real.log (Real.log x) / 4) := by
      have := Real.add_one_le_exp (Real.log (Real.log x) / 4)
      linarith
    have hpos1 : (0 : ℝ) < Real.exp (Real.log (Real.log x) / 4) := Real.exp_pos _
    calc Real.exp V * (1 + Real.sqrt (Real.log (Real.log x)))
        ≤ Real.exp (Real.log (Real.log x) / 4)
            * Real.exp (Real.log (Real.log x) / 4) := by
          refine mul_le_mul hq1' hq2 (by linarith) hpos1.le
      _ = Real.exp (Real.log (Real.log x) / 2) := by
          rw [← Real.exp_add]; ring_nf
      _ = Real.sqrt (Real.log x) := hsqrtlogx.symm
  have hsq0 : (0 : ℝ) < Real.sqrt (Real.log x) := lt_of_lt_of_le (by positivity) hev
  have hcollar : C / Real.sqrt (Real.log x)
      ≤ C / Real.exp V
        * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
    have hmono : (1 + Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ)
        ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWle (by norm_num)
    have hsr : Real.sqrt (1 + Real.sqrt (Real.log (Real.log x)))
        ≤ 1 + Real.sqrt (Real.log (Real.log x)) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) + Real.sqrt (Real.log (Real.log x))
        ≤ (1 + Real.sqrt (Real.log (Real.log x))) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h
    have hsrpos : (0 : ℝ) < Real.sqrt (1 + Real.sqrt (Real.log (Real.log x))) :=
      Real.sqrt_pos.2 (by linarith)
    have hgoal : Real.exp V * Real.sqrt (1 + Real.sqrt (Real.log (Real.log x)))
        ≤ Real.sqrt (Real.log x) :=
      le_trans (mul_le_mul_of_nonneg_left hsr (Real.exp_pos V).le) hev
    have hstep : C / Real.sqrt (Real.log x)
        ≤ C / Real.exp V * (1 + Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
      have hrw : C / Real.exp V * (Real.sqrt (1 + Real.sqrt (Real.log (Real.log x))))⁻¹
          = C / (Real.exp V * Real.sqrt (1 + Real.sqrt (Real.log (Real.log x)))) := by
        field_simp
      rw [hhalf _ (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt (Real.log (Real.log x))), hrw,
        div_le_div_iff₀ hsq0 (by positivity)]
      exact mul_le_mul_of_nonneg_left hgoal hC.le
    exact hstep.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  -- the two subtracted terms together
  have hkey : C / Real.exp V * Wc ^ (-(1 / 2) : ℝ) + C / Real.sqrt (Real.log x)
      ≤ 3 * C / Real.exp V
        * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hWconv (by positivity : (0 : ℝ) ≤ C / Real.exp V)
    have hid : C / Real.exp V
          * (2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ))
        + C / Real.exp V
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ)
        = 3 * C / Real.exp V
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-(1 / 2) : ℝ) := by ring
    linarith [hcollar]
  exact le_trans (mul_le_mul_of_nonneg_left (by linarith) hc.le)
    (Hx Y ν hY x q hx₁ hq23 hq1)

/-! ### The specialisation with the tilt scale fixed first

The form below takes `E₀` and `d` *before* the constants, which is strictly weaker: a constant may
then depend on the tilt scale.  It is one line of its `_of_top` form, which quantifies the tilt
scale inside.

Three suffixes, three separate questions, and none of them answers another's:

* `_of_le` or no suffix — the tilt scale is fixed *before* the constants; `_uniform` — *inside*;
* `_absorbed` — the reduction's subtracted terms are collapsed into one of the main term's order;
* `_of_top` — the tilt hypothesis sits at the top block while the walk is stopped `d` short, which
  is what makes the constants independent of the tilt scale, so it is quantified inside. -/

/-- `RMF.exists_const_integral_chaosWindowShift_rpow_le_int_rademacher_of_top` with `E₀`
and `d` fixed first. -/
theorem exists_const_integral_chaosWindowShift_rpow_le_int_rademacher (E₀ : ℝ)
    (hE₀ : 0 ≤ E₀) (d : ℕ) (hE₁ : 10 * E₀ ≤ Real.exp d) :
    ∃ (D₀ : ℕ) (x₀ C cr : ℝ), 0 < C ∧ 0 < cr ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ η q : ℝ) (n : ℤ), x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          harperWindowLevel cr |(n : ℝ)| ≤ Real.log (Real.log x) / 3 →
          (∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ
              ((n : ℝ)) ω ^ q ∂ν)
            ≤ C * ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℝ) + 1) ^ 2
              * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₀, C, cr, hC, hcr, H⟩ :=
    exists_const_integral_chaosWindowShift_rpow_le_int_rademacher_of_top (Ω := Ω)
  obtain ⟨x₀, H⟩ := H E₀ d hE₀ hE₁
  exact ⟨D₀, x₀, C, cr, hC, hcr, H⟩

end RMF
