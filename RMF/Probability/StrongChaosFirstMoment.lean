/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.StrongScales
import RMF.Probability.RademacherChaosFirstMoment

/-!
# The window integral at Harper's height range

The restricted chaos on a window `(w, w+1]` at the offset `RMF.harperDwExp D₀ c w`, whose level is
`≈ 10·log log w` (`Probability/StrongScales.lean`).  The proof is the Tonelli-and-tilt chain of
the unit window, at a general origin, with the two height facts replaced by their `_wide` forms.

## Main result

* `RMF.exists_const_integral_restrictedChaosWindowShift_raise_le_rademacher_of_drop_wide` -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

set_option maxHeartbeats 1000000 in
-- the same Tonelli-and-tilt chain as the unit-window theorem, at a general origin
/-- **The restricted chaos on `(w, w+1]` at the level `a + k`, `k = harperDwExp D₀ c w - D₀`, is at
most `C·(k+1)·min(1, a/√(n - ⌈a/4⌉))`, `n = harperBlockCount D₀ x`.**  The offset is
`RMF.harperDwExp`, so `hcut` allows `w ≈ exp((c/4)(log x)^{1/30})`.  `D₀`, `a₀`, `C`, `B`, `c` do
not depend on `E₀` and `d`; `x₀` does.  Nothing in the statement reads `n₀`. -/
theorem exists_const_integral_restrictedChaosWindowShift_raise_le_rademacher_of_drop_wide :
    ∃ (D₀ _n₀ : ℕ) (a₀ C B c : ℝ), 4 ≤ D₀ ∧ 0 < C ∧ 20 ≤ B ∧ 0 < c ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → 10 * E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ η a w : ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a → 1 ≤ w →
          harperWindowLevel c w ≤ Real.log (Real.log x) / 3 →
          8 * (⌈a / 4⌉₊ : ℝ) ≤ (harperBlockCount D₀ x : ℝ) →
            (∫ ω, restrictedChaosWindowShift
                (fun ω => squarefreeExtension fun p => Y p ω) x σ w
                (fun h => {ω | ∀ j, ⌈(a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ)) / 4⌉₊ ≤ j →
                  j ≤ harperBlockCount (harperDwExp D₀ c w) x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (harperDwExp D₀ c w) x) m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-(a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ)) - B * (j : ℝ))
                      (a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ) + (j : ℝ) + 2 * Real.log j)}) ω ∂ν)
              ≤ C * ((((harperDwExp D₀ c w - D₀ : ℕ) : ℝ) + 1)
                * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - (⌈a / 4⌉₊ : ℝ)))) := by
  obtain ⟨D₁, n₀, x₀, a₀, A, B, Tsh, c, hD₁, hA, hB, hTsh, hcpos, H⟩ :=
    exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop_wide
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_shift_le_rademacher
  obtain ⟨D₀, hD₀ge, hTexp⟩ := exists_le_two_mul_exp_sub_one Tsh (max D₁ 4)
  have hD₁D₀ : D₁ ≤ D₀ := le_trans (le_max_left _ _) hD₀ge
  have h4D₀ : 4 ≤ D₀ := le_trans (le_max_right _ _) hD₀ge
  refine ⟨D₀, n₀, a₀, A * Real.sqrt 2 * CM, B, c, h4D₀,
    by positivity, hB, hcpos, ?_⟩
  intro E₀ d _hE₀ hE₁
  obtain ⟨x₂, hx₂⟩ :=
    exists_harperThreshold_of_blockCount D₀ (24 * (D₀ + n₀ + 2 * d + 6))
  refine ⟨max (max x₀ (Real.exp 3)) x₂, ?_⟩
  intro Ω' _ Y ν hY x σ η a w hx hσ0 hη0 hηE hσx ha ha1 hw hcut hR
  obtain ⟨-, hD₀L, hcount24⟩ := hx₂ x (le_trans (le_max_right _ _) hx)
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hxm : max x₀ (Real.exp 3) ≤ x := le_trans (le_max_left _ _) hx
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hxm
  have hxe3 : Real.exp 3 ≤ x := le_trans (le_max_right _ _) hxm
  have hx2 : (2 : ℝ) ≤ x := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hηd : 10 * η ≤ Real.exp d := by linarith
  have hσre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hL0a : (0 : ℝ) ≤ Real.log (Real.log x) := le_trans (Nat.cast_nonneg _) hD₀L
  have hcountfl : harperBlockCount D₀ x ≤ ⌊Real.log (Real.log x)⌋₊ := Nat.sub_le _ _
  have hcountL : ((harperBlockCount D₀ x : ℕ) : ℝ) ≤ Real.log (Real.log x) := by
    have h3 : ((harperBlockCount D₀ x : ℕ) : ℝ)
        ≤ ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcountfl
    linarith [Nat.floor_le hL0a]
  have hΛ24 : 24 * ((D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 6) ≤ Real.log (Real.log x) := by
    have h1 : ((24 * (D₀ + n₀ + 2 * d + 6) : ℕ) : ℝ)
        ≤ ((harperBlockCount D₀ x : ℕ) : ℝ) := by exact_mod_cast hcount24
    push_cast at h1
    linarith
  set r : ℕ := ⌈a / 4⌉₊ with hrdef
  have hr1 : 1 ≤ r := Nat.ceil_pos.2 (by linarith)
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hΛ : 4 * ((r : ℝ) + (D₀ : ℝ) + (n₀ : ℝ) + 2 * (d : ℝ) + 4) ≤ Real.log (Real.log x) := by
    have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨hM1, hML, -, -⟩ :=
    harperBlockCount_harperDt_bounds_of_drop (h := 1) (n₀ := n₀) (d := d) hr1 hΛ
    one_pos le_rfl (by rw [abs_one, div_one, Real.log_one]; linarith)
  have hMpos : (0 : ℝ) < (harperBlockCount D₀ x : ℝ) - r := by linarith
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r)) :=
    le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) :=
    fun p => hY.measurable _ (p : Nat.Primes).2
  have hΛ' : 2 * ((D₀ : ℝ) + ((max (2 * (r + d)) (n₀ + (r + d)) : ℕ) : ℝ) + 2)
      ≤ Real.log (Real.log x) := by
    have hmax : ((max (2 * (r + d)) (n₀ + (r + d)) : ℕ) : ℝ)
        ≤ 2 * (r : ℝ) + 2 * (d : ℝ) + (n₀ : ℝ) := by
      have h1 : (max (2 * (r + d)) (n₀ + (r + d)) : ℕ) ≤ 2 * r + 2 * d + n₀ := by omega
      exact_mod_cast h1
    linarith
  have hw0 : (0 : ℝ) ≤ w := by linarith
  obtain ⟨hD₀le, hDlog, -, -⟩ :=
    harper_block_count_of_window_wide (D₀ := D₀) (d := r + d) (n₀ := n₀) hcut hΛ'
  set k : ℕ := harperDwExp D₀ c w - D₀ with hkdef
  have hDk : harperDwExp D₀ c w = D₀ + k := by have := le_harperDwExp D₀ c w; omega
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkR : (k : ℝ) ≤ Real.log (Real.log x) / 3 + 1 :=
    harperDwExp_sub_le_of_cut (D₀ := D₀) hcut
  have hak : (0 : ℝ) < (a + (k : ℝ)) / 4 := by linarith
  have hra1 : 1 ≤ ⌈(a + (k : ℝ)) / 4⌉₊ := Nat.ceil_pos.2 hak
  have hraub : ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ) ≤ (a + (k : ℝ)) / 4 + 1 :=
    (Nat.ceil_lt_add_one hak.le).le
  obtain ⟨hfit, -⟩ := harperBlockCount_raise_halving_of_drop_of_level (D₀ := D₀)
    (n₀ := n₀) (k := k) (d := d) (a := a) (x := x) ha1 hR hΛ24 hkR
  have hshift := min_one_div_sqrt_harperBlockCount_raise_le_of_drop_of_level
    (D₀ := D₀) (n₀ := n₀) (k := k) (d := d) (a := a) (x := x) ha1 hR hΛ24 hkR
  rw [← hDk] at hfit hshift
  have hrn : ⌈(a + (k : ℝ)) / 4⌉₊ ≤ harperBlockCount (harperDwExp D₀ c w) x - d := by omega
  have hn₀le' : n₀ ≤ harperBlockCount (harperDwExp D₀ c w) x - d - ⌈(a + (k : ℝ)) / 4⌉₊ := by omega
  set G : ℝ → Set Ω' := fun h => {ω | ∀ j,
    ⌈(a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ)) / 4⌉₊ ≤ j →
    j ≤ harperBlockCount (harperDwExp D₀ c w) x - d →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset (harperDwExp D₀ c w) x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-(a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ)) - B * (j : ℝ))
        (a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ) + (j : ℝ) + 2 * Real.log j)} with hGdef
  have hGmeas : ∀ h, MeasurableSet (G h) := by
    intro h
    simp only [hGdef]
    exact measurableSet_freeStartBarrier (fun m => Finset.measurable_sum _ fun p _ =>
      (measurable_localLogAdd _).comp (hYm p)) _ _ _ _
  have hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ G q.2} := by
    simp only [hGdef]
    exact measurableSet_freeStartBarrierAdd_uncurry hYm σ (harperOffset (harperDwExp D₀ c w) x)
      ⌈(a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ)) / 4⌉₊
      (harperBlockCount (harperDwExp D₀ c w) x - d)
      (fun j => -(a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ)) - B * (j : ℝ))
      (fun j => a + ((harperDwExp D₀ c w - D₀ : ℕ) : ℝ) + (j : ℝ) + 2 * Real.log j)
  rw [integral_restrictedChaosWindowShift_eq]
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  set g : ℝ → Ω' → ℝ := fun t ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ t) ω‖ ^ 2
    with hgdef
  have hQ0 : (0 : ℝ) ≤ ∫ ω, g 0 ω ∂ν := by
    simp only [hgdef]
    exact integral_nonneg fun ω => by positivity
  have hInt : Integrable
      (Function.uncurry fun (ω : Ω') (t : ℝ) => Set.indicator (G t) (g t) ω)
      (ν.prod (volume.restrict (Set.Ioc w (w + 1)))) :=
    integrable_uncurry_indicator_normSq_rademacher hY y (σ := σ) hσre G hGmeas hSmeas
      (T := Set.Ioc w (w + 1)) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hIntOn : IntegrableOn (fun h => ∫ ω, Set.indicator (G h) (g h) ω ∂ν)
      (Set.Ioc w (w + 1)) := hInt.integral_prod_right
  rw [integral_integral_swap hInt]
  have hMert' : (Real.log x)⁻¹ * ∫ ω, g 0 ω ∂ν ≤ CM := hMert Ω' Y ν hY x σ hx2 hσ0
  have hM' : (0 : ℝ) ≤ ((k : ℝ) + 1)
      * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r)) := by positivity
  have hjoin : (∫ h in Set.Ioc w (w + 1), ∫ ω, Set.indicator (G h) (g h) ω ∂ν)
      ≤ A * Real.sqrt 2 * (((k : ℝ) + 1)
        * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))) * ∫ ω, g 0 ω ∂ν := by
    have hc0 : (0 : ℝ) ≤ A * Real.sqrt 2 * (((k : ℝ) + 1)
        * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))) * ∫ ω, g 0 ω ∂ν :=
      mul_nonneg (mul_nonneg (mul_nonneg hA.le (Real.sqrt_nonneg 2)) hM') hQ0
    have hper : ∀ h ∈ Set.Ioc w (w + 1), (∫ ω, Set.indicator (G h) (g h) ω ∂ν)
        ≤ A * Real.sqrt 2 * (((k : ℝ) + 1)
          * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))) * ∫ ω, g 0 ω ∂ν := by
      intro h hh
      obtain ⟨hhw, hh1⟩ := hh
      have hh0 : (0 : ℝ) < h := by linarith
      have him : (shiftLine σ h).im = h := by simp [shiftLine]
      have hτsq : (2 * (shiftLine σ h).im) ^ 2
          ≤ Real.exp (c / 2 * Real.exp (harperOffset (harperDwExp D₀ c w) x / 10)) := by
        rw [him]
        exact sq_two_mul_le_exp_harperOffset_harperDwExp (by omega) hcpos hw0 hh0 hh1 x
      have hTsh' : Tsh ≤ 2 * (shiftLine σ h).im
          * Real.exp (harperOffset (harperDwExp D₀ c w) x) := by
        rw [him]
        exact le_trans hTexp
          (two_mul_exp_le_mul_exp_harperOffset_harperDwExp (D₀ := D₀) hw hhw x)
      have hchain := H Ω' Y ν hY x σ (a + (k : ℝ)) η (harperDwExp D₀ c w)
        ⌈(a + (k : ℝ)) / 4⌉₊ d (shiftLine σ h) (fun j => 2 * Real.log j) hxx₀
        (le_trans hD₁D₀ hD₀le) hDlog (re_shiftLine σ h)
        (by rw [re_shiftLine]; linarith) hσx hηd (by rw [him]; linarith) hτsq
        hTsh' (by linarith) (by linarith) hra1 hrn hraub hn₀le'
        (fun j hj _ => by
          have h0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
          rw [abs_of_nonneg (by linarith)]
          linarith)
      have hheight : (∫ ω, ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => Y p ω) y (shiftLine σ h) ω‖ ^ 2 ∂ν)
          = ∫ ω, g 0 ω ∂ν := by
        simp only [hgdef]
        exact hf'.integral_normSq_shiftLine_eq y (σ := σ) h 0
      rw [integral_indicator (hGmeas h)]
      calc (∫ ω in G h, g h ω ∂ν)
          ≤ A * min 1 ((a + (k : ℝ)) / Real.sqrt
              (((harperBlockCount (harperDwExp D₀ c w) x - d : ℕ) : ℝ)
                - ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ)))
              * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ h) ω‖ ^ 2 ∂ν := hchain
        _ = A * min 1 ((a + (k : ℝ)) / Real.sqrt
              (((harperBlockCount (harperDwExp D₀ c w) x - d : ℕ) : ℝ)
                - ((⌈(a + (k : ℝ)) / 4⌉₊ : ℕ) : ℝ)))
              * ∫ ω, g 0 ω ∂ν := by rw [hheight]
        _ ≤ A * (((k : ℝ) + 1) * (Real.sqrt 2
              * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))))
              * ∫ ω, g 0 ω ∂ν :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshift hA.le) hQ0
        _ = A * Real.sqrt 2 * (((k : ℝ) + 1)
              * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))) * ∫ ω, g 0 ω ∂ν := by
            ring
    have hconst : IntegrableOn (fun _ : ℝ => A * Real.sqrt 2 * (((k : ℝ) + 1)
        * min 1 (a / Real.sqrt ((harperBlockCount D₀ x : ℝ) - r))) * ∫ ω, g 0 ω ∂ν)
        (Set.Ioc w (w + 1)) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hmono := setIntegral_mono_on hIntOn hconst measurableSet_Ioc hper
    rwa [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith),
      show w + 1 - w = (1 : ℝ) by ring, one_mul] at hmono
  exact mul_le_mul_of_join_of_norm (inv_nonneg.2 hlogx0.le) (by positivity) hM' hjoin hMert'

end RMF
