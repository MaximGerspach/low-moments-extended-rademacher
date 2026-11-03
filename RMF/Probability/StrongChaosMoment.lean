/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.StrongChaosFirstMoment
import RMF.Probability.RademacherChaosMoment

/-!
# The chaos moment over a window, at Harper's height range

`Probability/StrongChaosFirstMoment.lean` gives the chaos half of Harper's good-set estimate on a
window `(w, w+1]` at the offset `RMF.harperDwExp D₀ cr w`.  This file supplies the other half —
the bad set — and, with both, the `RMF.GoodFamilyAdd` the interpolation reads, hence the `q`-th
moment of the chaos on the window.

On `(0,1]` the offset `RMF.harperDt D₀ h` varies with the height, so the bad set is split into
bands with the level raised along them.  On a window the offset is constant, and a single
application of `RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_le` covers it.

`cr` is the rate in the height condition `τ² ≤ exp((cr/2)·e^{ϑ/10})`; `c` and `B` are barrier
slopes. -/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- `max 1 (u·K) ≤ K·max 1 u` for `K ≥ 1`: it lets the interpolation's constant be read as
`C·(k+1)²` with `C` independent of `k`. -/
private lemma max_one_mul_le_mul_max_one {u K : ℝ} (_hu : 0 ≤ u) (hK : 1 ≤ K) :
    max 1 (u * K) ≤ K * max 1 u := by
  rcases le_total (u * K) 1 with h | h
  · rw [max_eq_left h]
    nlinarith [le_max_left (1 : ℝ) u]
  · rw [max_eq_right h]
    nlinarith [le_max_right (1 : ℝ) u]

/-- **The interpolation's constant, with the window's factor pulled out.**  `RMF.GoodFamilyAdd`'s
`C₂` is `Cc·K` here, `K = k + 1`, and the interpolation's output is a quadratic in `C₂`; this says
the whole of it is `≤` the `K`-free constant times `K²`. -/
private lemma goodFamily_const_le_mul_sq {C₁ Cc A K : ℝ} (hCc : 0 < Cc) (hA : 0 ≤ A)
    (hK : 1 ≤ K) :
    3 * (max 1 C₁ + max 1 (2 * (Cc * K) * (A + 1))
        + 2 * (max 1 (2 * (Cc * K)) * max 1 (2 * (Cc * K)))
        + max 1 (2 * (Cc * K)) * max 1 C₁)
      ≤ 3 * (max 1 C₁ + max 1 (2 * Cc * (A + 1))
        + 2 * (max 1 (2 * Cc) * max 1 (2 * Cc))
        + max 1 (2 * Cc) * max 1 C₁) * K ^ 2 := by
  have hM₁ : (1 : ℝ) ≤ max 1 C₁ := le_max_left _ _
  have hMA : (1 : ℝ) ≤ max 1 (2 * Cc * (A + 1)) := le_max_left _ _
  have hMb : (1 : ℝ) ≤ max 1 (2 * Cc) := le_max_left _ _
  have heqA : 2 * (Cc * K) * (A + 1) = 2 * Cc * (A + 1) * K := by ring
  have heqb : 2 * (Cc * K) = 2 * Cc * K := by ring
  have hA' : max 1 (2 * (Cc * K) * (A + 1)) ≤ K * max 1 (2 * Cc * (A + 1)) := by
    rw [heqA]
    exact max_one_mul_le_mul_max_one (by positivity) hK
  have hb' : max 1 (2 * (Cc * K)) ≤ K * max 1 (2 * Cc) := by
    rw [heqb]
    exact max_one_mul_le_mul_max_one (by positivity) hK
  have hb0 : (0 : ℝ) ≤ max 1 (2 * (Cc * K)) := by linarith [le_max_left (1 : ℝ) (2 * (Cc * K))]
  have hK0 : (0 : ℝ) < K := by linarith
  have hsq : K ≤ K ^ 2 := by nlinarith
  nlinarith [mul_le_mul hb' hb' hb0 (by positivity : (0 : ℝ) ≤ K * max 1 (2 * Cc)),
    mul_le_mul_of_nonneg_right hb' (by linarith : (0 : ℝ) ≤ max 1 C₁),
    mul_nonneg (le_of_lt hK0) (by linarith : (0 : ℝ) ≤ max 1 (2 * Cc)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ max 1 (2 * Cc)) (by linarith : (0 : ℝ) ≤ max 1 C₁)]

/-- **The bad set on a window at the drop, with `E₀` and `d` inside the constant.**  The
`_of_top` ladder already gives the bound at `t - d`, so the proof only widens `(w, w+1]` to
`[w, w+2)`. -/
theorem exists_const_measureReal_notMem_harperGoodRangeAdd_window_raise_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D₀ : ℕ) (x δ η a c cr w : ℝ), 4 ≤ D₀ → 1 < x →
          ((harperDwExp D₀ cr w : ℕ) : ℝ) ≤ Real.log (Real.log x) →
          0 ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
            ν.real {ω | ∃ h ∈ Set.Ioc w (w + 1),
                ω ∉ harperGoodRangeAdd Y c (harperDwExp D₀ cr w) x δ
                  (a + ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDwExp D₀ cr w) x - d) h}
              ≤ C * Real.exp D₀ * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_top (Ω' := Ω')
  refine ⟨a₀, 2 * C, by linarith, ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D₀ x δ η a c cr w hD₀ hx1 hDL hδ0 hη0 hηE hδx ha hc
  haveI := hY.isProbabilityMeasure
  set D : ℕ := harperDwExp D₀ cr w with hDdef
  set k : ℕ := D - D₀ with hkdef
  have hD₀D : D₀ ≤ D := by rw [hDdef]; exact le_harperDwExp D₀ cr w
  have hDk : D = D₀ + k := by omega
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hD4 : 4 ≤ D := le_trans hD₀ hD₀D
  have ha' : a₀ ≤ a + (k : ℝ) := by linarith
  -- the window sits inside a half-open interval of width `2`, and dropping blocks from the top
  -- only enlarges the good set, so the undropped bound dominates
  have hsub : {ω : Ω' | ∃ h ∈ Set.Ioc w (w + 1),
      ω ∉ harperGoodRangeAdd Y c D x δ (a + (k : ℝ)) (harperBlockCount D x - d) h}
      ⊆ {ω | ∃ h ∈ Set.Ico w (w + 2),
        ω ∉ harperGoodRangeAdd Y c D x δ (a + (k : ℝ))
          (harperBlockCount D x - d) h} := by
    rintro ω ⟨h, hh, hnot⟩
    exact ⟨h, ⟨hh.1.le, by linarith [hh.2]⟩, hnot⟩
  -- the width hypothesis is free: the exponent is nonpositive
  have hoff : (0 : ℝ) ≤ harperOffset D x := by
    have h4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD4
    linarith [sub_one_le_harperOffset D x]
  have hwid : Real.exp (-((⌈(a + (k : ℝ)) / 4⌉₊ : ℝ) + harperOffset D x)) ≤ 2 := by
    have hceil : (0 : ℝ) ≤ ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h := Real.exp_le_one_iff.2 (by linarith :
      -((⌈(a + (k : ℝ)) / 4⌉₊ : ℝ) + harperOffset D x) ≤ 0)
    linarith
  have hmain := H E₀ d hE₀ hEd Y ν hY D x δ η (a + (k : ℝ)) c w 2 hD4 hx1 hDL
    hδ0 hη0 hηE hδx ha' hc hwid
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) (le_trans hmain ?_)
  -- `exp D · exp(-2(a+k)) = exp D₀ · exp(-k) · exp(-2a) ≤ exp D₀ · exp(-2a)`
  have hcast : ((D : ℕ) : ℝ) = ((D₀ : ℕ) : ℝ) + (k : ℝ) := by rw [hDk]; push_cast; ring
  have hsplit : Real.exp ((D : ℕ) : ℝ) * Real.exp (-(2 * (a + (k : ℝ))))
      = Real.exp ((D₀ : ℕ) : ℝ) * Real.exp (-(2 * a)) * Real.exp (-(k : ℝ)) := by
    rw [hcast, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hkexp : Real.exp (-(k : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hpos : (0 : ℝ) < Real.exp ((D₀ : ℕ) : ℝ) * Real.exp (-(2 * a)) := by positivity
  calc C * Real.exp ((D : ℕ) : ℝ) * 2 * Real.exp (-(2 * (a + (k : ℝ))))
      = 2 * C * (Real.exp ((D₀ : ℕ) : ℝ) * Real.exp (-(2 * a)) * Real.exp (-(k : ℝ))) := by
        rw [← hsplit]; ring
    _ ≤ 2 * C * (Real.exp ((D₀ : ℕ) : ℝ) * Real.exp (-(2 * a)) * 1) := by
        have := mul_le_mul_of_nonneg_left hkexp hpos.le
        nlinarith
    _ = 2 * C * Real.exp ((D₀ : ℕ) : ℝ) * Real.exp (-(2 * a)) := by ring

/-- **Harper's good-set estimate on a window at the drop, with `E₀` and `d` inside the
constants.** -/
theorem exists_const_harperGoodRangeAdd_bounds_window_rademacher_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ (D₀ : ℕ) (a₀ Cc B cr : ℝ), 4 ≤ D₀ ∧ 0 < Cc ∧ 20 ≤ B ∧ 0 < cr ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (x σ η a w : ℝ), x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a → 1 ≤ w →
          harperWindowLevel cr w ≤ Real.log (Real.log x) / 3 →
            ν.real {ω | ∃ h ∈ Set.Ioc w (w + 1),
                ω ∉ harperGoodRangeAdd Y B (harperDwExp D₀ cr w) x σ
                  (a + ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ))
                  (harperBlockCount (harperDwExp D₀ cr w) x - d) h}
              ≤ Cc * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1) * Real.exp (-(2 * a))
            ∧ (8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ) →
              (∫ ω, restrictedChaosWindowShift
                  (fun ω => squarefreeExtension fun p => Y p ω) x σ w
                  (fun h => harperGoodRangeAdd Y B (harperDwExp D₀ cr w) x σ
                    (a + ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ))
                    (harperBlockCount (harperDwExp D₀ cr w) x - d) h) ω ∂ν)
                ≤ Cc * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1)
                  * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ)))) := by
  obtain ⟨D₀, -, a₁, Cq, B, cr, hD₀, hCq, hB, hcr, HQ₀⟩ :=
    exists_const_integral_restrictedChaosWindowShift_raise_le_rademacher_of_drop_wide
  obtain ⟨a₂, Cb, hCb, HB⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_window_raise_of_top (Ω' := Ω')
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount (2 * D₀ + 4) 0
  refine ⟨D₀, max (max a₁ a₂) 1, max (Cb * Real.exp D₀) Cq, B, cr,
    hD₀, lt_of_lt_of_le hCb (le_trans (by nlinarith [Real.one_le_exp (Nat.cast_nonneg (α := ℝ) D₀)])
      (le_max_left _ _)), hB, hcr, ?_⟩
  intro E₀ d hE₀ hE₁
  obtain ⟨x₁, HQ⟩ := HQ₀ E₀ d hE₀ hE₁
  have hEd : E₀ ≤ Real.exp d := by linarith
  refine ⟨max x₁ x₂, ?_⟩
  intro Y ν hY x σ η a w hx hσ0 hη0 hηE hσx ha ha1 hw hcut
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨hx1, hDL2, -⟩ := hx₂ x (le_trans (le_max_right _ _) hx)
  have ha₁ : a₁ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha₂ : a₂ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have hD₀R : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hcast : ((2 * D₀ + 4 : ℕ) : ℝ) = 2 * (D₀ : ℝ) + 4 := by push_cast; ring
  have hΛ : 2 * ((D₀ : ℝ) + ((max (2 * 0) (0 + 0) : ℕ) : ℝ) + 2) ≤ Real.log (Real.log x) := by
    rw [hcast] at hDL2
    simp only [Nat.mul_zero, Nat.add_zero, Nat.max_self, Nat.cast_zero]
    linarith
  have hDL : ((harperDwExp D₀ cr w : ℕ) : ℝ) ≤ Real.log (Real.log x) :=
    (harper_block_count_of_window_wide (D₀ := D₀) (d := 0) (n₀ := 0) hcut hΛ).2.1
  have hk1 : (1 : ℝ) ≤ ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (harperDwExp D₀ cr w - D₀)]
  have hCb0 : Cb * Real.exp D₀ ≤ max (Cb * Real.exp D₀) Cq := le_max_left _ _
  have hCq0 : Cq ≤ max (Cb * Real.exp D₀) Cq := le_max_right _ _
  have hCm : (0 : ℝ) < max (Cb * Real.exp D₀) Cq := lt_of_lt_of_le hCq hCq0
  constructor
  · refine le_trans
      (HB E₀ d hE₀ hEd Y ν hY D₀ x σ η a B cr w hD₀ hx1 hDL hσ0 hη0 hηE hσx ha₂ hB) ?_
    have hexp : (0 : ℝ) < Real.exp (-(2 * a)) := Real.exp_pos _
    have h1 : Cb * Real.exp D₀
        ≤ max (Cb * Real.exp D₀) Cq * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 hexp.le
  · intro hR
    refine le_trans (HQ Ω' Y ν hY x σ η a w hx₁ hσ0 hη0 hηE hσx ha₁ ha1 hw hcut hR) ?_
    have hmin0 : (0 : ℝ)
        ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ))) :=
      le_min zero_le_one (div_nonneg (by linarith) (Real.sqrt_nonneg _))
    have h1 : Cq * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1)
        ≤ max (Cb * Real.exp D₀) Cq * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1) := by
      nlinarith
    calc Cq * ((((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1)
          * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ))))
        = Cq * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1)
            * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hmin0

/-- **The `q`-th moment of the chaos on a window, with `E₀` and `d` inside the constant.**  It
covers the windows `n ≥ 1` in
`RMF.exists_const_integral_chaosWindowShift_rpow_le_int_rademacher_of_top`. -/
theorem exists_const_integral_chaosWindowShift_rpow_le_rademacher_of_top {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ (D₀ : ℕ) (C cr : ℝ), 0 < C ∧ 0 < cr ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ x σ η q w : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 → 1 ≤ w →
          harperWindowLevel cr w ≤ Real.log (Real.log x) / 3 →
          (∫ ω, chaosWindowShift
              (fun ω => squarefreeExtension fun p => Y p ω) x σ w ω ^ q ∂ν)
            ≤ C * (((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1) ^ 2
              * (1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₀, a₀c, Cc, B, cr, hD₀, hCc, hB, hcr, H₂₀⟩ :=
    exists_const_harperGoodRangeAdd_bounds_window_rademacher_of_top (Ω' := Ω')
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_shift_le_rademacher
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D₀ (4 * ⌈max (max a₀c 1) 3⌉₊ ^ 2)
  have hA0 : (0 : ℝ) ≤ max (max a₀c 1) 3 := by
    have : (3 : ℝ) ≤ max (max a₀c 1) 3 := le_max_right _ _
    linarith
  have hM1 : (1 : ℝ) ≤ max 1 CM := le_max_left _ _
  have hMA : (1 : ℝ) ≤ max 1 (2 * Cc * (max (max a₀c 1) 3 + 1)) := le_max_left _ _
  have hMb : (1 : ℝ) ≤ max 1 (2 * Cc) := le_max_left _ _
  have hCout : (0 : ℝ) < 3 * (max 1 CM + max 1 (2 * Cc * (max (max a₀c 1) 3 + 1))
      + 2 * (max 1 (2 * Cc) * max 1 (2 * Cc)) + max 1 (2 * Cc) * max 1 CM) := by nlinarith
  refine ⟨D₀,
    3 * (max 1 CM + max 1 (2 * Cc * (max (max a₀c 1) 3 + 1))
      + 2 * (max 1 (2 * Cc) * max 1 (2 * Cc))
      + max 1 (2 * Cc) * max 1 CM), cr, hCout, hcr, ?_⟩
  intro E₀ d hE₀ hE₁
  obtain ⟨x₁, H₂⟩ := H₂₀ E₀ d hE₀ hE₁
  refine ⟨max (max x₁ x₂) 2, ?_⟩
  intro Y ν hY x σ η q w hx hσ0 hη0 hηE hσ hq0 hq1 hw hcut
  haveI := hY.isProbabilityMeasure
  have hxa : max x₁ x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hxa
  obtain ⟨hxgt1, -, hcount⟩ := hx₂ x (le_trans (le_max_right _ _) hxa)
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hσre : (0 : ℝ) < 1 / 2 + σ := by linarith
  set K : ℝ := ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ) + 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]; linarith [Nat.cast_nonneg (α := ℝ) (harperDwExp D₀ cr w - D₀)]
  have hC₂ : (0 : ℝ) < Cc * K := by positivity
  have hT2 : ⌈max (max a₀c 1) 3⌉₊ ^ 2 ≤ harperBlockCount D₀ x / 4 := by
    refine (Nat.le_div_iff_mul_le (by norm_num)).2 ?_
    rw [Nat.mul_comm]
    exact hcount
  -- the mean chaos on the window is the unit one, by height-independence
  have hmean : (∫ ω, chaosWindowShift
      (fun ω => squarefreeExtension fun p => Y p ω) x σ w ω ∂ν) ≤ CM := by
    have h := integral_rpow_chaosWindowShift_le_rademacher hY hxgt1 hσre w
      (q := 1) zero_le_one le_rfl
    simp only [Real.rpow_one] at h
    exact le_trans h (hMert Ω' Y ν hY x σ hx2 hσ0)
  refine le_trans (integral_rpow_le_of_goodFamily_rademacher (n₀ := 0) (w := w)
    (t := harperBlockCount D₀ x / 4) (a₀ := max a₀c 1) (C₁ := CM) (C₂ := Cc * K)
    hY hx2 hxgt1 hσ0 hq0 hq1 hCM hC₂ ?_
    (by omega) hT2 ?_) ?_
  · exact hmean
  · refine
      { set := fun a h => harperGoodRangeAdd Y B (harperDwExp D₀ cr w) x σ
          (a + ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ))
          (harperBlockCount (harperDwExp D₀ cr w) x - d) h
        measurableSet := fun a h => measurableSet_harperGoodRangeAdd hYm _ _ _ _ _ _ _
        measurableSet_uncurry := fun a =>
          measurableSet_harperGoodRangeAdd_uncurry hYm B (harperDwExp D₀ cr w) x σ
            (a + ((harperDwExp D₀ cr w - D₀ : ℕ) : ℝ))
            (harperBlockCount (harperDwExp D₀ cr w) x - d)
        measure_bad_le := ?_
        integral_restricted_le := ?_ }
    · intro a ha
      have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
      have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
      exact (H₂ Y ν hY x σ η a w hxx₁ hσ0 hη0 hηE hσ hac ha1 hw hcut).1
    · intro a ha h2 _
      have hac : a₀c ≤ a := le_trans (le_max_left _ _) ha
      have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
      have ha0 : (0 : ℝ) ≤ a := by linarith
      have hR1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
      have hRm : 8 * ⌈a / 4⌉₊ ≤ harperBlockCount D₀ x := by omega
      have hRmR : 8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ) := by exact_mod_cast hRm
      have hbound := (H₂ Y ν hY x σ η a w hxx₁ hσ0 hη0 hηE hσ hac ha1 hw hcut).2 hRmR
      have htmR : ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) ≤ (harperBlockCount D₀ x : ℝ) := by
        exact_mod_cast Nat.div_le_self _ _
      have hposN : ⌈a / 4⌉₊ < harperBlockCount D₀ x / 4 := by omega
      have hpos : (0 : ℝ) < ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) - (⌈a / 4⌉₊ : ℝ) := by
        have h1 : ((⌈a / 4⌉₊ : ℕ) : ℝ) < ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := by
          exact_mod_cast hposN
        linarith
      have hmin : min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ)))
          ≤ min 1 (a / Real.sqrt (((harperBlockCount D₀ x / 4 : ℕ) : ℝ) - (⌈a / 4⌉₊ : ℝ))) := by
        gcongr
      exact le_trans hbound (mul_le_mul_of_nonneg_left hmin hC₂.le)
  · have hstep := goodFamily_const_le_mul_sq (C₁ := CM) hCc hA0 hK1
    have htarget : (0 : ℝ)
        ≤ (1 + (1 - q) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) ^ (-q) :=
      Real.rpow_nonneg (by nlinarith [Real.sqrt_nonneg ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)]) _
    exact mul_le_mul_of_nonneg_right hstep htarget

end RMF
