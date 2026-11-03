/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.MesoscopicBlock

/-!
# One mesoscopic block of a band, at a shift of either sign

The per-block input of the mesoscopic range of Proposition B (`RMF/Weighted/PropositionB.lean`),
for a band `(y, z]` in place of the full product.  As for the full product
(`Weighted/MesoscopicBlock.lean`), three results meet here:

* `RMF.integral_rpow_setIntegral_normSq_split_primesIco_le` — the split of the band at `w + 1` into
  its low part `(y, w]` and its high part `(w, z]`;
* `RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_signed_shift_rpow_le_log_div` — the
  moment bound for the low part, `≤ e^{48}·(log w/log y)^{q(2q-1)}`;
* `RMF.exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher_signed` —
  the mesoscopic chaos estimate for the high part, at a shift of either sign.

The shift is `σ ≥ -1/12` with `2|σ|·log z ≤ 1`, which is where a band sits at `½ - c`,
`c = 1/(2 log z)`.  The split's two-point bound then costs `e^{143800e}` rather than `e^{143800}`:
on the low part `p^{-2(½+σ)} ≤ e/p` (`RMF.rpow_neg_shift_le_exp_one_mul_inv`).  The moment bound
for a band holds for `½ ≤ q ≤ 1`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A band's block: the split and the low part's moment bound, with the chaos factor left
open.**  For the band `(y, z]` split at `w + 1`, with `2 ≤ y ≤ w ≤ z`, `w ≥ 3`, a shift
`σ ≥ -1/12` with `2|σ|·log w ≤ 1`, `½ ≤ q ≤ 1`, `T > 0` and `T·log(w+1) ≤ 2`,
`E[(∫_{T/e}^{T}‖F_{y,z}(½+σ+it)‖²dt)^q] ≤ e^{143800e}·e^{48}(log w/log y)^{q(2q-1)}·G`
whenever `G` bounds the same moment of the high part `(w, z]`.  The band analogue of
`RMF.integral_rpow_setIntegral_normSq_block_le_of_chaos`. -/
theorem integral_rpow_setIntegral_normSq_band_block_le_of_chaos {Y : ℕ → Ω → ℂ}
    {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {σ T q G : ℝ} {y w z : ℕ}
    (hy2 : 2 ≤ y) (hyw : y ≤ w) (hw3 : 3 ≤ w) (hwz : w ≤ z)
    (hσ : -(1 / 12) ≤ σ) (hσw : 2 * |σ| * Real.log w ≤ 1)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hT0 : 0 < T)
    (hThi : T * Real.log ((w : ℝ) + 1) ≤ 2)
    (hchaos : (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
          (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν) ≤ G) :
    (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ Real.exp (143800 * Real.exp 1)
        * (Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1))) * G := by
  have hcast : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
  have hw1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hab : T / Real.exp 1 < T := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]; nlinarith
  have hTe0 : (0 : ℝ) < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  -- the split, with `K = e` on the low part
  have hzt : ∀ t ∈ Set.Icc (T / Real.exp 1) T, |t| * Real.log ((w + 1 : ℕ) : ℝ) ≤ 2 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hTe0 ht.1
    have hlog0 : (0 : ℝ) ≤ Real.log ((w : ℝ) + 1) := Real.log_nonneg (by linarith)
    rw [abs_of_pos ht0, hcast]
    exact le_trans (mul_le_mul_of_nonneg_right ht.2 hlog0) hThi
  have hK : ∀ p ∈ primesIco (y + 1) (w + 1),
      (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) ≤ Real.exp 1 * ((p : ℝ))⁻¹ := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_primesIco hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hpw : p ≤ w := by have := (mem_primesIco.1 hp).2.2; omega
    have hlogp : Real.log p ≤ Real.log w := Real.log_le_log hp0 (by exact_mod_cast hpw)
    have hσp : 2 * |σ| * Real.log p ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hlogp (by positivity)) hσw
    rw [← Real.rpow_add hp0, show -(1 / 2 + σ) + -(1 / 2 + σ) = -(1 + 2 * σ) by ring]
    exact rpow_neg_shift_le_exp_one_mul_inv hpp.one_lt.le hσp
  have hsplit := integral_rpow_setIntegral_normSq_split_primesIco_le hY (y₀ := y + 1)
    (z := w + 1) (y := z + 1) (by omega) (by omega) (by omega) (σ := σ) (q := q)
    (K := Real.exp 1) hσ hab (by linarith) hq1 hK (Real.exp_pos 1).le hzt
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs0] at hsplit
  -- the moment bound for the low part
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hPF := hf.integral_norm_randomEulerProductIco_signed_shift_rpow_le_log_div hq0 hq1 hy2
    hyw hw3 hσw
  have hPF0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
      (y + 1) (w + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hCH0 : (0 : ℝ) ≤ ∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) (w + 1)
        (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (integral_nonneg fun t => sq_nonneg _) _
  have hratio0 : (0 : ℝ) ≤ Real.log w / Real.log y :=
    div_nonneg (Real.log_nonneg hw1) (Real.log_nonneg hy1)
  have hPFb0 : (0 : ℝ) ≤ Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1)) :=
    mul_nonneg (Real.exp_pos 48).le (Real.rpow_nonneg hratio0 _)
  have hexpq : Real.exp (143800 * Real.exp 1) ^ q ≤ Real.exp (143800 * Real.exp 1) := by
    calc Real.exp (143800 * Real.exp 1) ^ q ≤ Real.exp (143800 * Real.exp 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (by positivity)) hq1
      _ = Real.exp (143800 * Real.exp 1) := Real.rpow_one _
  refine le_trans hsplit ?_
  calc _ ≤ Real.exp (143800 * Real.exp 1)
          * ((Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1))) * G) :=
        mul_le_mul hexpq (mul_le_mul hPF hchaos hCH0 hPFb0) (mul_nonneg hPF0 hCH0)
          (Real.exp_pos _).le
    _ = Real.exp (143800 * Real.exp 1)
          * (Real.exp 48 * (Real.log w / Real.log y) ^ (q * (2 * q - 1))) * G := by ring

/-- **One mesoscopic block of a band.**  For the window `[T/e, T]`, the band `(y, z]` split at
`w + 1`, and the depth `t = harperBlockCount D z - 3`, uniformly for `½ ≤ q ≤ 1` and shifts
`σ ≥ -1/12` with `2|σ|·log z ≤ 1`,
`E[(∫_{T/e}^{T}‖F_{y,z}(½+σ+it)‖²dt)^q] ≤ A·(log w/log y)^{q(2q-1)}·(T²·log z)^q·(1+(1-q)√t)^{-q}`.
The band analogue of `RMF.exists_const_integral_rpow_setIntegral_normSq_block_le_rademacher`, with
its window hypotheses read at the band's top `z` in place of `x`. -/
theorem exists_const_integral_rpow_setIntegral_normSq_band_block_le_rademacher :
    ∃ (D₀ t₀ : ℕ) (x₀ Klo A : ℝ), 4 ≤ D₀ ∧ 4 ≤ Klo ∧ Real.exp (D₀ : ℝ) ≤ Klo ∧ 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (σ T q : ℝ) (y w z D : ℕ),
          x₀ ≤ (z : ℝ) → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log z) →
          2 ≤ y → y ≤ w → 3 ≤ w → w + 1 ≤ z →
          ((w : ℝ) + 1) ≤ blockScale (harperOffset D z) 0 →
          -(1 / 12) ≤ σ → 2 * |σ| * Real.log z ≤ 1 → 1 / 2 ≤ q → q ≤ 1 →
          0 < T → T ≤ 1 →
          1 ≤ T * Real.log ((w : ℝ) + 1) → T * Real.log ((w : ℝ) + 1) ≤ 2 →
          Klo ≤ T * Real.exp (harperOffset D z) →
          T * Real.exp (harperOffset D z) ≤ Real.exp 4 * Klo →
          t₀ ≤ harperBlockCount D z - 3 →
            (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  (y + 1) (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * ((Real.log w / Real.log y) ^ (q * (2 * q - 1)) * (T ^ 2 * Real.log z) ^ q)
                * (1 + (1 - q) * Real.sqrt ((harperBlockCount D z - 3 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₀, t₀, x₀, Klo, Ac, hD₀, hKlo, hKloD, hAc, HC⟩ :=
    exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher_signed
      (Ω := Ω)
  refine ⟨D₀, t₀, x₀, Klo, Real.exp (143800 * Real.exp 1) * Real.exp 48 * Ac, hD₀, hKlo, hKloD,
    by positivity, ?_⟩
  intro Y ν hY σ T q y w z D hx hDD hDlog hy2 hyw hw3 hwz hwb hσ hσz hq0 hq1 hT0 hT1 hTlo hThi
    hKl hKb ht₀
  have hz4 : (4 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 4 ≤ z)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hwzR : (w : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hwz
  have hσx : |σ| * Real.log z ≤ 1 := by nlinarith [mul_nonneg (abs_nonneg σ) hlogz.le]
  have hlogwz : Real.log w ≤ Real.log z :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < w)) (by exact_mod_cast (by omega : w ≤ z))
  have hσw : 2 * |σ| * Real.log w ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hlogwz (by positivity)) hσz
  have hchaos := HC Y ν hY (z : ℝ) σ T q (w + 1) D hx hDD hDlog (by omega)
    (by push_cast; linarith) (by rw [Nat.floor_natCast]; omega) (by push_cast; exact hwb) hσ hσx
    (Or.inr hσz) (by linarith) hq1 hT0 hT1 (by push_cast; exact hTlo) hKl hKb ht₀
  rw [Nat.floor_natCast] at hchaos
  refine le_trans (integral_rpow_setIntegral_normSq_band_block_le_of_chaos hY hy2 hyw hw3
    (by omega) hσ hσw hq0 hq1 hT0 hThi hchaos) (le_of_eq ?_)
  ring

end RMF
