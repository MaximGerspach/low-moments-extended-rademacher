/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.MesoscopicChaos
import RMF.Probability.RademacherAveragedExplicit
import RMF.Probability.RademacherBarrierSharp

/-!
# The mesoscopic block chaos: the block's mean and one height

Two inputs of the weighted block chaos of `Weighted/BlockChaosWeightExplicit.lean`, whose
level-shift interpolation (`RMF.integral_rpow_le_of_goodSets_shift`) normalises the process by
its **exact** mean:

* the block's second moment `E‖F_{[z,y)}(½+σ+ih)‖²` does not depend on `h`
  (`RMF.integral_normSq_Ico_shiftLine_eq`), and it is positive (`RMF.integral_normSq_Ico_pos`);
* the restricted chaos at one height is the averaged free start, across the prime split, at the
  floor `ϑ` (`RMF.setIntegral_mesoGood_normSq_Ico_le_radAveraged_of_floor`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The mean of the block -/

/-- **The block's second moment does not see the height**, for the product over `[z, y)`:
`E‖F_{[z,y)}(½+σ+ih)‖² = ∏_p (1 + p^{-1-2σ})` at every `h`
(`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq`). -/
lemma integral_normSq_Ico_shiftLine_eq {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (z y : ℕ) (σ h h' : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y
        (shiftLine σ h) ω‖ ^ 2 ∂ν)
      = ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y
          (shiftLine σ h') ω‖ ^ 2 ∂ν := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq, hf.integral_norm_randomEulerProductIco_sq]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hppos : 0 < p := (prime_of_mem_primesIco hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hppos, Complex.norm_natCast_cpow_of_pos hppos,
    Complex.neg_re, Complex.neg_re, re_shiftLine, re_shiftLine]

/-! ### The restricted chaos at one height -/

/-- **The good-set integral of a block at the floor `ϑ`**: on the barrier's good set
`mesoGood`, `∫‖F_{[z,⌊x⌋+1)}(s)‖² ≤ C·min(1, (a + s₀)/√(n - ⌈a/4⌉))·E‖F_{[z,⌊x⌋+1)}(s)‖²`,
`C = radAveragedConst E₀ β Tr κ`, `s₀ = radAveragedShift E₀ β Tr κ`, `n = harperBlockCount D x`,
under the height condition `(2|Im s| + 1)·pntFloorConst ϑ ≤ e^{-2E₀}/200`
(`RMF.measureReal_mesoGood_le_radAveraged_of_floor`), carried from the full product to the
block. -/
theorem setIntegral_mesoGood_normSq_Ico_le_radAveraged_of_floor (E₀ β : ℝ) (hE₀ : 0 ≤ E₀)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) {Tr κ : ℝ} (hTr : 4 < Tr) (hκ : 1 ≤ κ) {Y : ℕ → Ω → ℂ}
    {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {x σ η a : ℝ} {z D : ℕ} {s : ℂ} (hx1 : 1 < x)
    (hDlog : (D : ℝ) ≤ Real.log (Real.log x))
    (hϑ : radFreeStartThreshold E₀ ≤ harperOffset D x) (hϑ104 : (104 : ℝ) ≤ harperOffset D x)
    (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ) (hη0 : 0 ≤ η) (hηE : η ≤ E₀)
    (hσx : |σ| * Real.log x ≤ η)
    (hlo : 600 * Real.exp (2 * E₀) ≤ 2 * |s.im| * Real.exp (harperOffset D x))
    (hhiF : (2 * |s.im| + 1) * pntFloorConst (harperOffset D x)
      ≤ Real.exp (-(2 * E₀)) / 200)
    (hzb : (z : ℝ) ≤ blockScale (harperOffset D x) 0) (hzn : z ≤ ⌊x⌋₊ + 1)
    (ha : 1 ≤ a) (hrn : ⌈a / 4⌉₊ < harperBlockCount D x) :
    (∫ ω in mesoGood Y (harperOffset D x) prop5UpperSlope (harperBlockCount D x) ⌈a / 4⌉₊ a
          (fun j => β * Real.log j) s,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
          s ω‖ ^ 2 ∂ν)
      ≤ radAveragedConst E₀ β Tr κ
          * min 1 ((a + radAveragedShift E₀ β Tr κ)
            / Real.sqrt ((harperBlockCount D x : ℝ) - ⌈a / 4⌉₊))
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
            z (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  haveI := hY.isProbabilityMeasure
  set ϑ := harperOffset D x with hϑdef
  set n := harperBlockCount D x with hndef
  have hs : 0 < s.re := by rw [hres]; linarith
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hcut : blockCutoff ϑ n = ⌊x⌋₊ + 1 := blockCutoff_harperOffset hx1 hDlog
  have hσtop : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hσx
  have hP := measureReal_mesoGood_le_radAveraged_of_floor E₀ β hE₀ hβ0 hβ2 hTr hκ hY hϑ hϑ104
    hres hσ0 hη0 hηE hσtop hlo hhiF ha hrn
  rw [hcut] at hP
  have hGm : MeasurableSet
      (mesoGood Y ϑ prop5UpperSlope n ⌈a / 4⌉₊ a (fun j => β * Real.log j) s) :=
    measurableSet_mesoGood hY _ _ _ _ _ _ _
  have hZ0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  have hfull : (∫ ω in mesoGood Y ϑ prop5UpperSlope n ⌈a / 4⌉₊ a (fun j => β * Real.log j) s,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1) s ω‖ ^ 2
          ∂ν)
      ≤ radAveragedConst E₀ β Tr κ
          * min 1 ((a + radAveragedShift E₀ β Tr κ) / Real.sqrt ((n : ℝ) - ⌈a / 4⌉₊))
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
    rw [hf'.setIntegral_normSq_eq (⌊x⌋₊ + 1) hs hGm]
    exact mul_le_mul_of_nonneg_right hP hZ0
  -- every prime the barrier looks at lies in `[z, ⌊x⌋₊+1)`
  have hblk : ∀ m, m < n → ∀ p ∈ primeBlockSub ϑ m,
      ((p : Nat.Primes) : ℕ) ∈ primesIco z (⌊x⌋₊ + 1) := by
    intro m hm p hp
    rw [mem_primeBlockSub] at hp
    refine mem_primesIco.2 ⟨p.2, ?_, ?_⟩
    · have h0 : blockScale ϑ 0 ≤ blockScale ϑ m := blockScale_mono _ (Nat.zero_le m)
      have hzp : (z : ℝ) < ((p : ℕ) : ℝ) := lt_of_le_of_lt (le_trans hzb h0) hp.1
      exact_mod_cast hzp.le
    · have hJ : m + 1 ≤ n := by omega
      have h1 : blockScale ϑ (m + 1) ≤ blockScale ϑ n := blockScale_mono _ hJ
      rw [hϑdef, hndef, blockScale_harperOffset_last hx1 hDlog] at h1
      have he1 : (Real.exp 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp (by norm_num))
      have hxe : x ^ (Real.exp 1)⁻¹ ≤ x := by
        calc x ^ (Real.exp 1)⁻¹ ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) he1
          _ = x := Real.rpow_one x
      have hpx : ((p : ℕ) : ℝ) < (⌊x⌋₊ : ℝ) + 1 :=
        lt_of_le_of_lt (le_trans hp.2 (le_trans h1 hxe)) (Nat.lt_floor_add_one x)
      exact_mod_cast hpx
  exact setIntegral_normSq_randomEulerProductIco_le_of_le hY z (⌊x⌋₊ + 1) hzn hres hσ0
    (measurableSet_tupleGood (primesIco z (⌊x⌋₊ + 1)) ϑ prop5UpperSlope n ⌈a / 4⌉₊ a
      (fun j => β * Real.log j) s)
    (fun ω => (mem_tupleGood_iff (fun p hp => prime_of_mem_primesIco hp) hblk ω).symm) hfull

/-! ### The mean is positive -/

/-- `E‖F_{[z,y)}(s)‖² > 0` on every line `Re s = ½ + σ`, `σ ≥ 0`. -/
lemma integral_normSq_Ico_pos {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (z y : ℕ) {σ : ℝ} (hσ0 : 0 ≤ σ) {s : ℂ}
    (hs : s.re = 1 / 2 + σ) :
    (0 : ℝ) < ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y
      s ω‖ ^ 2 ∂ν := by
  have h := integral_norm_randomEulerProductIco_rpow_pos hY z y
    (by linarith : (0 : ℝ) < 1 / 2 + σ) hs 2
  have hpt : ∀ ω : Ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y s ω‖ ^ (2 : ℝ)
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z y s ω‖ ^ 2 := by
    intro ω
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [integral_congr_ae (Filter.Eventually.of_forall hpt)] at h

end RMF
