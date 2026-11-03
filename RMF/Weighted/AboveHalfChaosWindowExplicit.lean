/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCleanExplicit
import RMF.Weighted.TenAssemblyExplicit

/-!
# The chaos windows of the levels above `q = ½`

A window of a band `(y, z]` or of the bottom at height `T` with `T log z = e^m` is bounded by the
split and the weighted chaos (`RMF.integral_rpow_window_band_le_split_chaos_of_weight`) at the
offset `D = ⌊log log z⌋ + 8 - m`, which makes the offset exactly `log log z + 7 - m` (`Te^ϑ = e^7`)
and the block count `m - 8`.  For `2008 ≤ m ≤ log log z - 97` and `log x ≥ 160000`:

`(2/(2π log z))^q·E[W^q] ≤ winSplit·RMF.chaosAbove q·(1 + (1-q)√(m-8))^{-q}`

(`RMF.window_band_le_chaos_aligned`, `RMF.window_bottom_le_chaos_aligned`), whence the levels with
the chaos (`RMF.integral_rpow_norm_blockTruncationTail_le_bandLevelCh`,
`RMF.integral_rpow_norm_truncationTail_le_bottomLevelCh`).  The chaos runs at tilt `1/160000`,
level `18`, `λ = 98/5`, `T = 30`, `κ = 8`, `δ = 1/50`, slope `11/20`, `N = 2000`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The chaos constant and multiplier -/

/-- The chaos constant of a window above `½`: `RMF.shiftMomentConst` at tilt `1/160000`, slope
`11/20`, `T = 30`, `κ = 8`, level `18`, `λ = 98/5`, `δ = 1/50` and `K_ϑ = e^7`. -/
noncomputable def chaosAbove (q : ℝ) : ℝ :=
  shiftMomentConst 1 (radAveragedConst (1 / 160000) (11 / 20) 30 8)
    (radBlockBadConst (1 / 160000) (11 / 20) * Real.exp 7) 18
    (radAveragedShift (1 / 160000) (11 / 20) 30 8) (98 / 5) (1 / 50) q

/-- The chaos factor of the window at local index `m` below the top `z`: the better of `1` and
`RMF.chaosAbove q·(1 + (1-q)√(m-8))^{-q}` when `2008 ≤ m ≤ log log z - 97`, else `1`. -/
noncomputable def chaosMult (q : ℝ) (m z : ℕ) : ℝ :=
  if 2008 ≤ m ∧ (m : ℝ) + 97 ≤ Real.log (Real.log z) then
    min 1 (chaosAbove q * (1 + (1 - q) * Real.sqrt ((m - 8 : ℕ) : ℝ)) ^ (-q))
  else 1

lemma chaosAbove_nonneg (q : ℝ) : 0 ≤ chaosAbove q := by
  rw [chaosAbove, shiftMomentConst]
  exact le_trans (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _)

lemma chaosMult_nonneg {q : ℝ} (hq1 : q ≤ 1) (m z : ℕ) : 0 ≤ chaosMult q m z := by
  rw [chaosMult]
  split_ifs
  · have h1q : 0 ≤ 1 - q := by linarith
    exact le_min zero_le_one (mul_nonneg (chaosAbove_nonneg q)
      (Real.rpow_nonneg (by positivity) _))
  · exact zero_le_one

lemma chaosMult_le_one (q : ℝ) (m z : ℕ) : chaosMult q m z ≤ 1 := by
  rw [chaosMult]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-! ### A window by the split and the chaos, at any offset -/

/-- **A band's window by the split and the weighted chaos, explicit.**  As
`RMF.window_band_le_split_explicit` with the upper block `(z₁, z]` bounded by the weighted chaos
at the offset `D` (`RMF.integral_rpow_window_band_le_split_chaos_of_weight`, at `y' = z`):

`(2/(2π log z))^q·E[W_T^q] ≤ winSplit q T y z₁ z·C·(1 + (1-q)√n)^{-q}`,

`C = shiftMomentConst 1 C_i (C_b K_ϑ) A s λ δ q`, `n = harperBlockCount D z`. -/
theorem window_band_le_split_chaos_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Kθ Amax δc : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δc) (hδ : δc ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δc * N)
    (hmono : 3 ≤ 8 * δc * Real.sqrt (N : ℝ))
    {y z₁ z D : ℕ} (hy : 2 ≤ y) (hyz₁ : y ≤ z₁) (hz₁z : z₁ ≤ z) {σ η q T A lam : ℝ}
    (hσ : 0 < σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hDlog : (D : ℝ) ≤ Real.log (Real.log z))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D z)
    (hϑ104 : (104 : ℝ) ≤ harperOffset D z)
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : σ * Real.log z ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D z))
    (hKθ : T * Real.exp (harperOffset D z) ≤ Kθ)
    (hzb : ((z₁ + 1 : ℕ) : ℝ) ≤ blockScale (harperOffset D z) 0)
    (hNn : N ≤ harperBlockCount D z)
    (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ winSplit q T y z₁ z
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ) A
            (radAveragedShift E₀ βc Tr κ) lam δc q
          * (1 + (1 - q) * Real.sqrt (harperBlockCount D z : ℝ)) ^ (-q)) := by
  set β := 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) with hβdef
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hz₁2 : (2 : ℝ) ≤ z₁ := by exact_mod_cast le_trans hy hyz₁
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans (le_trans hy hyz₁) hz₁z
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlz₁ : 0 < Real.log z₁ := Real.log_pos (by linarith)
  have hq' : 0 ≤ 1 - q := by linarith
  have hβ0 : 0 ≤ β := by
    have h2 : (0 : ℝ) ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [hβdef]
    positivity
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ hT hβ0
  have hMup := integral_normSq_Ico_shiftLine_le_mertens_ratio hX (z := z₁) (y := z)
    (le_trans hy hyz₁) hz₁z hσ.le 0
  have hV8 := integral_rpow_window_band_le_split_chaos_of_weight E₀ βc hE₀ hE₀1 hβc hβc2 hTr hκ
    hδ0 hδ hN hmono hX (y₀ := y + 1) (z₁ := z₁ + 1) (y' := z) (D := D) (by omega) (by omega)
    hσ (by linarith) hq1 hT hT1 hβ0 le_rfl (by linarith) hDlog hϑ hϑ104 hη0 hηE hσx hlo hKθ hzb
    hNn hA hAmax hlam hR hMup
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs0] at hV8
  have hPF := hX.isRademacherRMF.integral_norm_randomEulerProductIco_shift_rpow_le_above_half
    hσ.le hq0 hq1 hy hyz₁
  set P := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
    (z₁ + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ with hPdef
  set R := taylorWindowW (β * T ^ 2) / T with hRdef
  set M := Real.log z / Real.log z₁ * Real.exp (9.0028 / Real.log z + 9.0028 / Real.log z₁)
    with hMdef
  set C := shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ) A
    (radAveragedShift E₀ βc Tr κ) lam δc q with hCdef
  set G := (1 + (1 - q) * Real.sqrt (harperBlockCount D z : ℝ)) ^ (-q) with hGdef
  have hW0 : 0 ≤ taylorWindowW (β * T ^ 2) := taylorWindowW_nonneg (mul_nonneg hβ0 (sq_nonneg T))
  have hR0 : 0 ≤ R := div_nonneg hW0 hT.le
  have hM0 : 0 ≤ M := by positivity
  have hC0 : 0 ≤ C := by
    rw [hCdef, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  have hG0 : 0 ≤ G := Real.rpow_nonneg (by positivity) _
  have hc : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z)) ^ q := Real.rpow_nonneg (by positivity) _
  have hRM : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q :=
    Real.rpow_nonneg (by positivity) _
  have hPFb : P ≤ pfBand q y z₁ := by rw [pfBand]; exact hPF
  calc (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (2 / (2 * Real.pi * Real.log z)) ^ q * (P * (C * (R * M) ^ q * G)) :=
        mul_le_mul_of_nonneg_left hV8 hc
    _ = P * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q * (C * G) := by
        rw [Real.mul_rpow (x := 2 / (2 * Real.pi * Real.log z)) (y := R * M) (by positivity)
          (by positivity)]
        ring
    _ ≤ pfBand q y z₁ * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q * (C * G) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPFb hRM) (mul_nonneg hC0 hG0)
    _ = winSplit q T y z₁ z * (C * G) := by
        congr 1
        rw [winSplit]
        congr 2
        rw [hRdef, hMdef, hβdef, mBand, add_comm (9.0028 / Real.log z)]
        field_simp

/-- **The bottom's window by the split and the weighted chaos, explicit**: as
`RMF.window_band_le_split_chaos_explicit` for the full product up to `z`, split at
`2 ≤ z₁ ≤ z`, the lower block's (PF) that of the full product. -/
theorem window_bottom_le_split_chaos_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Kθ Amax δc : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δc) (hδ : δc ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δc * N)
    (hmono : 3 ≤ 8 * δc * Real.sqrt (N : ℝ))
    {z₁ z D : ℕ} (hz₁ : 2 ≤ z₁) (hz₁z : z₁ ≤ z) {σ η q T A lam : ℝ}
    (hσ : 0 < σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hDlog : (D : ℝ) ≤ Real.log (Real.log z))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D z)
    (hϑ104 : (104 : ℝ) ≤ harperOffset D z)
    (hη0 : 0 ≤ η) (hηE : η ≤ E₀) (hσx : σ * Real.log z ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D z))
    (hKθ : T * Real.exp (harperOffset D z) ≤ Kθ)
    (hzb : ((z₁ + 1 : ℕ) : ℝ) ≤ blockScale (harperOffset D z) 0)
    (hNn : N ≤ harperBlockCount D z)
    (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ winSplitFull q T z₁ z
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ) A
            (radAveragedShift E₀ βc Tr κ) lam δc q
          * (1 + (1 - q) * Real.sqrt (harperBlockCount D z : ℝ)) ^ (-q)) := by
  set β := 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) with hβdef
  have hz₁2 : (2 : ℝ) ≤ z₁ := by exact_mod_cast hz₁
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans hz₁ hz₁z
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlz₁ : 0 < Real.log z₁ := Real.log_pos (by linarith)
  have hq' : 0 ≤ 1 - q := by linarith
  have hβ0 : 0 ≤ β := by
    have h2 : (0 : ℝ) ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [hβdef]
    positivity
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ hT hβ0
  have hMup := integral_normSq_Ico_shiftLine_le_mertens_ratio hX (z := z₁) (y := z) hz₁ hz₁z
    hσ.le 0
  have hV8 := integral_rpow_window_band_le_split_chaos_of_weight E₀ βc hE₀ hE₀1 hβc hβc2 hTr hκ
    hδ0 hδ hN hmono hX (y₀ := 1) (z₁ := z₁ + 1) (y' := z) (D := D) (by omega) (by omega)
    hσ (by linarith) hq1 hT hT1 hβ0 le_rfl (by linarith) hDlog hϑ hϑ104 hη0 hηE hσx hlo hKθ hzb
    hNn hA hAmax hlam hR hMup
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs0] at hV8
  simp only [randomEulerProductIco_one] at hV8
  have hPF := hX.isRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_above_half
    hσ.le hq0 hq1 hz₁
  set P := ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z₁ + 1)
    (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ with hPdef
  set R := taylorWindowW (β * T ^ 2) / T with hRdef
  set M := Real.log z / Real.log z₁ * Real.exp (9.0028 / Real.log z + 9.0028 / Real.log z₁)
    with hMdef
  set C := shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ) (radBlockBadConst E₀ βc * Kθ) A
    (radAveragedShift E₀ βc Tr κ) lam δc q with hCdef
  set G := (1 + (1 - q) * Real.sqrt (harperBlockCount D z : ℝ)) ^ (-q) with hGdef
  have hW0 : 0 ≤ taylorWindowW (β * T ^ 2) := taylorWindowW_nonneg (mul_nonneg hβ0 (sq_nonneg T))
  have hR0 : 0 ≤ R := div_nonneg hW0 hT.le
  have hM0 : 0 ≤ M := by positivity
  have hC0 : 0 ≤ C := by
    rw [hCdef, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  have hG0 : 0 ≤ G := Real.rpow_nonneg (by positivity) _
  have hc : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z)) ^ q := Real.rpow_nonneg (by positivity) _
  have hRM : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q :=
    Real.rpow_nonneg (by positivity) _
  have hV8' : (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) ≤ P * (C * (R * M) ^ q * G) := by
    simpa only [randomEulerProductIco_one] using hV8
  calc (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (2 / (2 * Real.pi * Real.log z)) ^ q * (P * (C * (R * M) ^ q * G)) :=
        mul_le_mul_of_nonneg_left hV8' hc
    _ = P * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q * (C * G) := by
        rw [Real.mul_rpow (x := 2 / (2 * Real.pi * Real.log z)) (y := R * M) (by positivity)
          (by positivity)]
        ring
    _ ≤ pfFull q z₁ * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q * (C * G) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPF hRM) (mul_nonneg hC0 hG0)
    _ = winSplitFull q T z₁ z * (C * G) := by
        congr 1
        rw [winSplitFull]
        congr 2
        rw [hRdef, hMdef, hβdef, mBand, add_comm (9.0028 / Real.log z)]
        field_simp

/-! ### The aligned offset -/

/-- **The aligned offset.**  For `m + 97 ≤ log log z`, at `D = ⌊log log z⌋ + 8 - m`: the offset is
exactly `log log z + 7 - m`, the block count is `m - 8` and `D ≤ log log z + 8 - m`. -/
lemma harperOffset_aligned {z m : ℕ} (hm : (m : ℝ) + 97 ≤ Real.log (Real.log z)) :
    harperOffset (⌊Real.log (Real.log z)⌋₊ + 8 - m) z = Real.log (Real.log z) + 7 - m
      ∧ harperBlockCount (⌊Real.log (Real.log z)⌋₊ + 8 - m) z = m - 8
      ∧ ((⌊Real.log (Real.log z)⌋₊ + 8 - m : ℕ) : ℝ) ≤ Real.log (Real.log z) + 8 - m := by
  set L := Real.log (Real.log (z : ℝ)) with hL
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hL0 : 0 ≤ L := by linarith
  have hmfl : m + 97 ≤ ⌊L⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hcast : ((⌊L⌋₊ + 8 - m : ℕ) : ℝ) = (⌊L⌋₊ : ℝ) + 8 - m := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hfl : (⌊L⌋₊ : ℝ) = ((⌊L⌋ : ℤ) : ℝ) := natCast_floor_eq_intCast_floor hL0
  refine ⟨?_, ?_, ?_⟩
  · rw [harperOffset, ← hL, hcast, hfl]
    have := Int.fract_add_floor L
    linarith
  · rw [harperBlockCount, ← hL]
    omega
  · rw [hcast]
    linarith [Nat.floor_le hL0]

/-- `e^6 ≥ 403`. -/
lemma four_hundred_three_le_exp_six : (403 : ℝ) ≤ Real.exp 6 := by
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  have := Real.exp_one_gt_d9
  have h4 : (2.718 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
  linarith [show (403 : ℝ) ≤ 2.718 ^ 6 by norm_num]

/-- The block bad sets' level at the tilt `1/160000` is at most `18`. -/
lemma radBlockBadLevel_tilt_le : radBlockBadLevel (1 / 160000) ≤ 18 := by
  have h := half_level_le_B (Λ := 10000) le_rfl
  have e : (1 : ℝ) / (16 * 10000) = 1 / 160000 := by norm_num
  rwa [e] at h

/-- The split point at height `T ≤ 1` lies below `exp(e^7/T) - 1` when `T log y ≤ e`. -/
lemma splitPt_add_one_le_blockScale {T : ℝ} {y z : ℕ} (hy : 2 ≤ y) (hT : 0 < T) (hT1 : T ≤ 1)
    (hTy : T * Real.log y ≤ Real.exp 1) :
    ((splitPt (3 / 2) T y z + 1 : ℕ) : ℝ) ≤ Real.exp (Real.exp 7 / T) := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have he7 : (3 : ℝ) ≤ Real.exp 7 := by
    have := Real.add_one_le_exp (7 : ℝ)
    linarith
  -- the split point is at most `max y exp(3/(2T))`
  have hsp : (splitPt (3 / 2) T y z : ℝ) ≤ max (y : ℝ) (Real.exp (3 / 2 / T)) := by
    have h1 : splitPt (3 / 2) T y z ≤ max y ⌊Real.exp (3 / 2 / T)⌋₊ := min_le_right _ _
    have h2 : (splitPt (3 / 2) T y z : ℝ) ≤ ((max y ⌊Real.exp (3 / 2 / T)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine le_trans h2 ?_
    rw [Nat.cast_max]
    exact max_le_max le_rfl (Nat.floor_le (Real.exp_pos _).le)
  push_cast
  rcases le_total (y : ℝ) (Real.exp (3 / 2 / T)) with hle | hle
  · rw [max_eq_right hle] at hsp
    -- `exp(e^7/T) ≥ e·exp(3/(2T)) ≥ exp(3/(2T)) + 1`
    have h1 : 3 / 2 / T + 1 ≤ Real.exp 7 / T := by
      rw [div_add_one hT.ne', div_le_div_iff_of_pos_right hT]
      nlinarith
    have h2 : Real.exp (3 / 2 / T) * Real.exp 1 ≤ Real.exp (Real.exp 7 / T) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 h1
    have h3 : 1 ≤ Real.exp (3 / 2 / T) := Real.one_le_exp (by positivity)
    have h4 := Real.exp_one_gt_d9
    nlinarith
  · rw [max_eq_left hle] at hsp
    -- `log(y+1) ≤ 2 log y ≤ e^6 log y ≤ e^7/T`
    have h1 : Real.log ((y : ℝ) + 1) ≤ 2 * Real.log y := by
      rw [← Real.log_rpow (by linarith), Real.log_le_log_iff (by linarith) (by positivity)]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith
    have h2 : 2 * Real.log y ≤ Real.exp 7 / T := by
      rw [le_div_iff₀ hT]
      have h6 := four_hundred_three_le_exp_six
      have e7 : Real.exp 7 = Real.exp 6 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have h3 : (y : ℝ) + 1 ≤ Real.exp (Real.exp 7 / T) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]
      linarith
    linarith

/-- **The chaos's side conditions at the aligned offset.**  For a window at height
`T = e^m/log z` with `2008 ≤ m`, `m + 97 ≤ log log z` and `T log y ≤ e`, at
`D = ⌊log log z⌋ + 8 - m`: every hypothesis of the chaos on `D`, `T` and the split point. -/
lemma aligned_chaos_conditions {T : ℝ} {y z m : ℕ} (hy : 2 ≤ y) (hz : 2 ≤ z) (hm : 2008 ≤ m)
    (hmL : (m : ℝ) + 97 ≤ Real.log (Real.log z)) (hTm : T * Real.log z = Real.exp m)
    (hTy : T * Real.log y ≤ Real.exp 1) :
    0 < T ∧ T ≤ 1
      ∧ ((⌊Real.log (Real.log z)⌋₊ + 8 - m : ℕ) : ℝ) ≤ Real.log (Real.log z)
      ∧ radFreeStartThreshold (1 / 160000)
          ≤ harperOffset (⌊Real.log (Real.log z)⌋₊ + 8 - m) z
      ∧ (104 : ℝ) ≤ harperOffset (⌊Real.log (Real.log z)⌋₊ + 8 - m) z
      ∧ 600 * Real.exp (2 * (1 / 160000)) ≤ 2 * (T / Real.exp 1)
          * Real.exp (harperOffset (⌊Real.log (Real.log z)⌋₊ + 8 - m) z)
      ∧ T * Real.exp (harperOffset (⌊Real.log (Real.log z)⌋₊ + 8 - m) z) ≤ Real.exp 7
      ∧ ((splitPt (3 / 2) T y z + 1 : ℕ) : ℝ)
          ≤ blockScale (harperOffset (⌊Real.log (Real.log z)⌋₊ + 8 - m) z) 0
      ∧ 2000 ≤ harperBlockCount (⌊Real.log (Real.log z)⌋₊ + 8 - m) z
      ∧ harperBlockCount (⌊Real.log (Real.log z)⌋₊ + 8 - m) z = m - 8 := by
  obtain ⟨hϑ, hn, hD⟩ := harperOffset_aligned (z := z) hmL
  set L := Real.log (Real.log (z : ℝ)) with hL
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have heL : Real.exp L = Real.log z := Real.exp_log hlz
  have hmR : (2008 : ℝ) ≤ m := by exact_mod_cast hm
  -- `T = e^{m - L}`
  have hTe : T = Real.exp ((m : ℝ) - L) := by
    rw [Real.exp_sub, heL, eq_div_iff hlz.ne', hTm]
  have hT : 0 < T := by rw [hTe]; exact Real.exp_pos _
  have hT1 : T ≤ 1 := by rw [hTe]; exact Real.exp_le_one_iff.2 (by linarith)
  have hTϑ : T * Real.exp (harperOffset (⌊L⌋₊ + 8 - m) z) = Real.exp 7 := by
    rw [hϑ, hTe, ← Real.exp_add]
    congr 1
    ring
  have hϑ104 : (104 : ℝ) ≤ harperOffset (⌊L⌋₊ + 8 - m) z := by rw [hϑ]; linarith
  refine ⟨hT, hT1, by linarith, le_trans (radFreeStartThreshold_le_104 (by norm_num)
    (by norm_num)) hϑ104, hϑ104, ?_, le_of_eq hTϑ, ?_, by omega, hn⟩
  · have h1 : 2 * (T / Real.exp 1) * Real.exp (harperOffset (⌊L⌋₊ + 8 - m) z)
        = 2 * Real.exp 6 := by
      rw [div_eq_mul_inv, mul_assoc, mul_assoc, mul_comm (Real.exp 1)⁻¹, ← mul_assoc T, hTϑ,
        ← Real.exp_neg, ← Real.exp_add]
      norm_num
    rw [h1]
    have h2 := four_hundred_three_le_exp_six
    have h3 : Real.exp (2 * (1 / 160000)) ≤ Real.exp (1 / 5) := Real.exp_le_exp.2 (by norm_num)
    have h4 := exp_one_fifth_le
    linarith
  · refine le_trans (splitPt_add_one_le_blockScale hy hT hT1 hTy) ?_
    rw [blockScale, Nat.cast_zero, zero_add]
    refine Real.exp_le_exp.2 (le_of_eq ?_)
    rw [div_eq_iff hT.ne', mul_comm, hTϑ]

/-! ### The aligned windows -/

/-- **A band's window at `T log z = e^m` by the chaos.**  For `½ ≤ q ≤ 1`, `2 ≤ y ≤ z ≤ x` with
`log x ≥ 160000`, `2008 ≤ m ≤ log log z - 97` and `T log y ≤ e`, at `σ = (log x)^{-2}`:

`(2/(2π log z))^q·E[W_T^q] ≤ winSplit q T y z₁ z·RMF.chaosAbove q·(1 + (1-q)√(m-8))^{-q}`,

`z₁ = RMF.splitPt (3/2) T y z`: `RMF.window_band_le_split_chaos_explicit` at the aligned offset
(`RMF.aligned_chaos_conditions`). -/
theorem window_band_le_chaos_aligned {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q T : ℝ} {y z m : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hzx : (z : ℝ) ≤ x) (hlx : 160000 ≤ Real.log x) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hm : 2008 ≤ m) (hmL : (m : ℝ) + 97 ≤ Real.log (Real.log z))
    (hTm : T * Real.log z = Real.exp m) (hTy : T * Real.log y ≤ Real.exp 1) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
          (((Real.log x ^ 2)⁻¹) ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
              (shiftLine (Real.log x ^ 2)⁻¹ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ winSplit q T y (splitPt (3 / 2) T y z) z
        * (chaosAbove q * (1 + (1 - q) * Real.sqrt ((m - 8 : ℕ) : ℝ)) ^ (-q)) := by
  have hz : 2 ≤ z := le_trans hy hyz
  obtain ⟨hT, hT1, hDlog, hϑ, hϑ104, hlo, hKθ, hzb, hNn, hn⟩ :=
    aligned_chaos_conditions hy hz hm hmL hTm hTy
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlx0 : 0 < Real.log x := by linarith
  have hlzx : Real.log z ≤ Real.log x := Real.log_le_log (by linarith) hzx
  have hσ : 0 < (Real.log x ^ 2)⁻¹ := by positivity
  have hσx : (Real.log x ^ 2)⁻¹ * Real.log z ≤ (Real.log x)⁻¹ := by
    rw [inv_mul_le_iff₀ (by positivity), pow_two, mul_assoc, mul_inv_cancel₀ hlx0.ne', mul_one]
    exact hlzx
  have hηE : (Real.log x)⁻¹ ≤ 1 / 160000 := by
    rw [inv_le_comm₀ hlx0 (by norm_num)]
    norm_num
    exact hlx
  have h := window_band_le_split_chaos_explicit hX (1 / 160000) (11 / 20) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (Tr := 30) (κ := 8) (Kθ := Real.exp 7)
    (Amax := 20) (δc := 1 / 50) (N := 2000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_room half_mono hy (le_splitPt hyz) (splitPt_le _ _ y z)
    (η := (Real.log x)⁻¹) (A := 18) (lam := 98 / 5) hσ hq0 hq1 hT hT1 hDlog hϑ hϑ104
    (by positivity) hηE hσx hlo hKθ hzb hNn radBlockBadLevel_tilt_le (by norm_num) (by norm_num)
  rw [hn] at h
  exact h

/-- **The bottom's window at `T log z = e^m` by the chaos**: as `RMF.window_band_le_chaos_aligned`
for the full product up to `z`, split at `RMF.splitPt (3/2) T 2 z`. -/
theorem window_bottom_le_chaos_aligned {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q T : ℝ} {z m : ℕ} (hz : 2 ≤ z)
    (hzx : (z : ℝ) ≤ x) (hlx : 160000 ≤ Real.log x) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hm : 2008 ≤ m) (hmL : (m : ℝ) + 97 ≤ Real.log (Real.log z))
    (hTm : T * Real.log z = Real.exp m) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
          (((Real.log x ^ 2)⁻¹) ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
              (shiftLine (Real.log x ^ 2)⁻¹ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ winSplitFull q T (splitPt (3 / 2) T 2 z) z
        * (chaosAbove q * (1 + (1 - q) * Real.sqrt ((m - 8 : ℕ) : ℝ)) ^ (-q)) := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  -- `T ≤ e^{-97}`, so `T log 2 ≤ e`
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hTe : T = Real.exp ((m : ℝ) - Real.log (Real.log z)) := by
    rw [Real.exp_sub, Real.exp_log hlz, eq_div_iff hlz.ne', hTm]
  have hTy : T * Real.log (2 : ℕ) ≤ Real.exp 1 := by
    have h1 : T ≤ 1 := by rw [hTe]; exact Real.exp_le_one_iff.2 (by linarith)
    have h2 : Real.log ((2 : ℕ) : ℝ) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (1 : ℝ)
      push_cast
      linarith
    have h3 : 0 ≤ Real.log ((2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h4 : 0 < T := by rw [hTe]; exact Real.exp_pos _
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  obtain ⟨hT, hT1, hDlog, hϑ, hϑ104, hlo, hKθ, hzb, hNn, hn⟩ :=
    aligned_chaos_conditions (le_refl 2) hz hm hmL hTm hTy
  have hlx0 : 0 < Real.log x := by linarith
  have hlzx : Real.log z ≤ Real.log x := Real.log_le_log (by linarith) hzx
  have hσ : 0 < (Real.log x ^ 2)⁻¹ := by positivity
  have hσx : (Real.log x ^ 2)⁻¹ * Real.log z ≤ (Real.log x)⁻¹ := by
    rw [inv_mul_le_iff₀ (by positivity), pow_two, mul_assoc, mul_inv_cancel₀ hlx0.ne', mul_one]
    exact hlzx
  have hηE : (Real.log x)⁻¹ ≤ 1 / 160000 := by
    rw [inv_le_comm₀ hlx0 (by norm_num)]
    norm_num
    exact hlx
  have h := window_bottom_le_split_chaos_explicit hX (1 / 160000) (11 / 20) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (Tr := 30) (κ := 8) (Kθ := Real.exp 7)
    (Amax := 20) (δc := 1 / 50) (N := 2000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_room half_mono (le_splitPt hz) (splitPt_le _ _ 2 z)
    (η := (Real.log x)⁻¹) (A := 18) (lam := 98 / 5) hσ hq0 hq1 hT hT1 hDlog hϑ hϑ104
    (by positivity) hηE hσx hlo hKθ hzb hNn radBlockBadLevel_tilt_le (by norm_num) (by norm_num)
  rw [hn] at h
  exact h

/-! ### The levels with the chaos -/

/-- A band's window bound with the chaos: the better of no split and the split times the chaos
factor at the local index `m = J - k` (`RMF.chaosMult`), at `θ = 1`, `c_s = 3/2`. -/
noncomputable def winBandCh (q : ℝ) (y z k : ℕ) : ℝ :=
  min (winNoSplit q (bandT 1 y z k) y z)
    (winSplit q (bandT 1 y z k) y (splitPt (3 / 2) (bandT 1 y z k) y z) z
      * chaosMult q (bandJ 1 y z - k) z)

/-- The bottom's window bound with the chaos, at `θ = 1`, `T_m = 2`, `c_s = 3/2`. -/
noncomputable def winBotCh (q : ℝ) (z k : ℕ) : ℝ :=
  min (winNoSplitFull q (bottomT 1 2 z k) z)
    (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z
      * chaosMult q (bottomJ 1 2 z - k) z)

/-- **A band's level with the chaos**: `RMF.bandLevelW` at `θ = 1` with the windows
`RMF.winBandCh`. -/
noncomputable def bandLevelCh (q η' ε x : ℝ) (y z : ℕ) : ℝ :=
  bandLevelW q 1 η' ε x y z (winBandCh q y z)

/-- **The bottom level with the chaos**: `RMF.bottomLevelW` at `θ = 1`, `T_m = 2` with the windows
`RMF.winBotCh`. -/
noncomputable def bottomLevelCh (q η' ε x : ℝ) (z : ℕ) : ℝ :=
  bottomLevelW q 1 η' ε 2 x z (winBotCh q z)

lemma winSplit_nonneg {q T : ℝ} (hq1 : q ≤ 1) {y z₁ z : ℕ} (hT : 0 < T) :
    0 ≤ winSplit q T y z₁ z := by
  rw [winSplit, pfBand]
  refine mul_nonneg (by positivity) (Real.rpow_nonneg ?_ _)
  have h1q : 0 ≤ 1 - q := by linarith
  have hb : 0 ≤ 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2 := by
    have : (0 : ℝ) ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    positivity
  have hW := taylorWindowW_nonneg hb
  have hm : 0 ≤ mBand z₁ z := by
    rw [mBand]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
      (Real.exp_pos _).le
  have hlz : 0 ≤ Real.log z := Real.log_natCast_nonneg _
  exact div_nonneg (mul_nonneg hW hm) (by positivity)

lemma winSplitFull_nonneg {q T : ℝ} (hq1 : q ≤ 1) {z₁ z : ℕ} (hT : 0 < T) :
    0 ≤ winSplitFull q T z₁ z := by
  rw [winSplitFull, pfFull]
  refine mul_nonneg (by positivity) (Real.rpow_nonneg ?_ _)
  have h1q : 0 ≤ 1 - q := by linarith
  have hb : 0 ≤ 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) * T ^ 2 := by
    have : (0 : ℝ) ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    positivity
  have hW := taylorWindowW_nonneg hb
  have hm : 0 ≤ mBand z₁ z := by
    rw [mBand]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
      (Real.exp_pos _).le
  have hlz : 0 ≤ Real.log z := Real.log_natCast_nonneg _
  exact div_nonneg (mul_nonneg hW hm) (by positivity)

/-- The band's window at `k < J` sits at `T log z = e^{J-k}` with `T log y ≤ e`. -/
lemma bandT_aligned {y z k : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) (hz : 1 < Real.log z)
    (hk : k < bandJ 1 y z) :
    bandT 1 y z k * Real.log z = Real.exp ((bandJ 1 y z - k : ℕ) : ℝ)
      ∧ bandT 1 y z k * Real.log y ≤ Real.exp 1 := by
  have hlz : 0 < Real.log z := by linarith
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hcast : ((bandJ 1 y z - k : ℕ) : ℝ) = (bandJ 1 y z : ℝ) - k := by
    rw [Nat.cast_sub hk.le]
  rw [bandT_one_eq hz k, hcast]
  refine ⟨by field_simp, ?_⟩
  have hκ1 : 1 ≤ Real.log z / Real.log y := by rw [le_div_iff₀ hly]; linarith
  have hJ2 : (bandJ 1 y z : ℝ) < Real.log (Real.log z / Real.log y) + 1 := by
    rw [bandJ, one_mul]
    exact Nat.ceil_lt_add_one (Real.log_nonneg hκ1)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : Real.exp ((bandJ 1 y z : ℝ) - k) ≤ Real.exp (Real.log (Real.log z / Real.log y) + 1) :=
    Real.exp_le_exp.2 (by linarith)
  rw [Real.exp_add, Real.exp_log (by positivity)] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hlz]
  calc Real.exp ((bandJ 1 y z : ℝ) - k) * Real.log y
      ≤ Real.log z / Real.log y * Real.exp 1 * Real.log y :=
        mul_le_mul_of_nonneg_right h1 hly.le
    _ = Real.exp 1 * Real.log z := by field_simp

/-- The bottom's window at `k < J` sits at `T log z = e^{J-k}`. -/
lemma bottomT_aligned {z k : ℕ} (hz : 0 < Real.log z) (hk : k < bottomJ 1 2 z) :
    bottomT 1 2 z k * Real.log z = Real.exp ((bottomJ 1 2 z - k : ℕ) : ℝ) := by
  have hcast : ((bottomJ 1 2 z - k : ℕ) : ℝ) = (bottomJ 1 2 z : ℝ) - k := by
    rw [Nat.cast_sub hk.le]
  rw [bottomT, hcast, show Real.log (1 / Real.log z) + (bottomJ 1 2 z : ℝ) - k
      = Real.log (1 / Real.log z) + ((bottomJ 1 2 z : ℝ) - k) by ring, Real.exp_add,
    Real.exp_log (by positivity)]
  field_simp

/-- **A band's level above `½` with the chaos.**  For `½ ≤ q ≤ 1`, `η', ε > 0`, `2 ≤ y ≤ z ≤ x`
with `log x ≥ 160000` and the sieve level `⌊z/(log x)^7⌋ ≥ 2`:
`E|𝒯_{y,z}(x)|^{2q} ≤ RMF.bandLevelCh q η' ε x y z`, each window the better of no split, the split
and the split with the chaos (`RMF.window_band_le_chaos_aligned`). -/
theorem integral_rpow_norm_blockTruncationTail_le_bandLevelCh {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q η' ε x : ℝ} {y z : ℕ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hy : 2 ≤ y) (hyz : y ≤ z)
    (hzx : (z : ℝ) ≤ x) (hlx : 160000 ≤ Real.log x) (hz' : 2 ≤ sieveLevel x z) :
    (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ)
      ≤ bandLevelCh q η' ε x y z := by
  have hx : 1 < Real.log x := by linarith
  have hσ : 0 < (Real.log x ^ 2)⁻¹ := by
    have : 0 < Real.log x := by linarith
    positivity
  have hz2' : 2 ≤ z := le_trans hy hyz
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz2'
  -- `log z ≥ 1`: the sieve level is at least `2`
  have hlz1 : 1 < Real.log z := by
    have h1 : 2 ≤ (z : ℝ) / Real.log x ^ 7 := by
      have := hz'
      rw [sieveLevel] at this
      exact_mod_cast (Nat.le_floor_iff (by positivity)).1 this
    have h2 : (2 : ℝ) * Real.log x ^ 7 ≤ z := by
      rwa [le_div_iff₀ (by positivity)] at h1
    have h3 : Real.exp 2 ≤ (z : ℝ) := by
      have h4 : Real.exp 2 ≤ 2 * Real.log x ^ 7 := by
        have h5 : Real.exp 2 ≤ 8 := by
          have := Real.exp_one_lt_d9
          have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos 1]
        have h6 : (4 : ℝ) ≤ Real.log x ^ 7 := by
          have h2 : (2 : ℝ) ^ 7 ≤ Real.log x ^ 7 :=
            pow_le_pow_left₀ (by norm_num) (by linarith) 7
          norm_num at h2
          linarith
        linarith
      linarith
    rw [← Real.exp_lt_exp, Real.exp_log (by linarith)]
    have := Real.exp_lt_exp.2 (by norm_num : (1 : ℝ) < 2)
    linarith
  have hM := fun t => integral_normSq_line_le_mBand hX hy hyz hσ.le t
  refine integral_rpow_norm_blockTruncationTail_le_bandLevelW hX hq0 hq1 one_pos hη' hε hy hyz hzx
    hx hz' fun k hk => ?_
  rw [winBandCh]
  refine le_min (window_band_le_nosplit_explicit hX y z hz2' hσ (by linarith) hq1
    (bandT_pos k) hM) ?_
  have hJens := window_band_le_split_explicit hX hy (le_splitPt hyz) (splitPt_le _ _ y z) hσ hq0
    hq1 (bandT_pos (θ := 1) (y := y) (z := z) k) (β := 2 * (1 - q)
      * (Real.log ((splitPt (3 / 2) (bandT 1 y z k) y z + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((splitPt (3 / 2) (bandT 1 y z k) y z + 1 : ℕ) : ℝ) + 34)) le_rfl
  rw [chaosMult]
  split_ifs with hc
  · rw [mul_min_of_nonneg _ _ (winSplit_nonneg hq1 (bandT_pos k)), mul_one]
    refine le_min ?_ ?_
    · refine le_trans hJens (le_of_eq ?_)
      rw [winSplit, pfBand, mBand, add_comm (9.0028 / Real.log z)]
    · obtain ⟨hTm, hTy⟩ := bandT_aligned hy hyz hlz1 hk
      exact window_band_le_chaos_aligned hX hy hyz hzx hlx hq0 hq1 hc.1 hc.2 hTm hTy
  · rw [mul_one]
    refine le_trans hJens (le_of_eq ?_)
    rw [winSplit, pfBand, mBand, add_comm (9.0028 / Real.log z)]

/-- **The bottom level above `½` with the chaos**: as
`RMF.integral_rpow_norm_blockTruncationTail_le_bandLevelCh` for the full product up to `z`,
`E|𝒯_z(x)|^{2q} ≤ RMF.bottomLevelCh q η' ε x z`. -/
theorem integral_rpow_norm_truncationTail_le_bottomLevelCh {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q η' ε x : ℝ} {z : ℕ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hz : 2 ≤ z)
    (hzx : (z : ℝ) ≤ x) (hlx : 160000 ≤ Real.log x) (hz' : 2 ≤ sieveLevel x z) :
    (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) z x ω‖ ^ (2 * q) ∂μ)
      ≤ bottomLevelCh q η' ε x z := by
  have hx : 1 < Real.log x := by linarith
  have hσ : 0 < (Real.log x ^ 2)⁻¹ := by
    have : 0 < Real.log x := by linarith
    positivity
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (0 + 1) (z + 1) ((1 / 2 : ℂ) + (((Real.log x ^ 2)⁻¹ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        ∂μ) ≤ mFull z :=
    fun t => integral_normSq_line_le_mFull hX hz hσ.le t
  refine integral_rpow_norm_truncationTail_le_bottomLevelW hX hq0 hq1 one_pos hη' hε hz hzx hx
    hz' fun k hk => ?_
  have hT : 0 < bottomT 1 2 z k := Real.exp_pos _
  rw [winBotCh]
  refine le_min (window_band_le_nosplit_explicit hX 0 z hz hσ (by linarith) hq1 hT hM) ?_
  have hJ : _ ≤ winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z :=
    window_bottom_le_split_explicit hX (le_splitPt (c := 3 / 2) (T := bottomT 1 2 z k) hz)
      (splitPt_le (3 / 2) (bottomT 1 2 z k) 2 z) hσ hq0 hq1 hT le_rfl
  rw [chaosMult]
  split_ifs with hc
  · rw [mul_min_of_nonneg _ _ (winSplitFull_nonneg hq1 hT), mul_one]
    refine le_min hJ ?_
    exact window_bottom_le_chaos_aligned hX hz hzx hlx hq0 hq1 hc.1 hc.2
      (bottomT_aligned hlz hk)
  · rw [mul_one]
    exact hJ

end RMF
