/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.Step

/-!
# HP2's window integral: the sum over the cells with the rest, region by region

`r·RMF.hp2ExtSum r N B B_sat` bounded uniformly in `r ≥ r₀ ≥ 2000` (`RMF.hp2ExtSum_le`), on the
regions of `RMF/UniformLower/HP2Window/Regions.lean`:

* **the depths `d < r - 59`** (regions I, II and III's far part): the rest's factor is at most
  `1.000001`, so the bounds without the rest apply (`RMF.hp2WinRegionIIIfar_le`: III's far part);
* **the short posts `r - 59 ≤ d ≤ r - 3`**: the factor `e^{4e^{1-(r-d)} + 10⁻¹⁹}` joins the cells'
  `e^{3.1e^{1-(r-d)}}` (`RMF.hp2ExtNear_le`);
* **the deep cells and below** (region IV): the deep constant `RMF.hp2WinDeep` times
  `Z ≥ ∑_j e^{2B_j + 10⁻¹⁹}(a_j - a_{j+1}) + e^{2B_sat + 10⁻¹⁹}a_N` (`RMF.hp2ExtDeep_le`) — the
  average of the rest's factor over the deep pairs.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The sum split -/

/-- Reindexing the cells by depth: `∑_{i<40D} f i = ∑_{d<D}∑_{j<40} f(40d + j)`. -/
lemma sum_range_forty_mul (D : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (40 * D), f i
      = ∑ d ∈ Finset.range D, ∑ j ∈ Finset.range 40, f (40 * d + j) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [show 40 * (D + 1) = 40 * D + 40 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun d => ∑ j ∈ Finset.range 40, f (40 * d + j)) D]

/-- **`r·hp2ExtSum` split**: the cells of the depths `d < r - 2`, the deep cells and below them. -/
lemma mul_hp2ExtSum_eq (r N : ℕ) (B : ℕ → ℝ) (Bsat : ℝ) :
    (r : ℝ) * hp2ExtSum r N B Bsat
      = ∑ d ∈ Finset.range (r - 2), ∑ j ∈ Finset.range 40,
          (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j)
        + (∑ j ∈ Finset.range N, (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19)
            * hp2Band (40 * (r - 2) + j)
          + (r : ℝ) * hp2ExtSat r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))) := by
  unfold hp2ExtSum
  rw [Finset.sum_range_add, sum_range_forty_mul, mul_add, mul_add, Finset.mul_sum,
    Finset.mul_sum, ← add_assoc]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hd := Finset.mem_range.1 hd
      have hj := Finset.mem_range.1 hj
      have h1 : 40 * d + j < 40 * (r - 2) := by omega
      have h2 : (40 * d + j) / 40 = d := by omega
      have h3 : (40 * d + j) % 40 = j := by omega
      unfold hp2ExtCell
      rw [if_pos h1, h2, h3]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : ¬ 40 * (r - 2) + j < 40 * (r - 2) := by omega
      have h2 : 40 * (r - 2) + j - 40 * (r - 2) = j := by omega
      unfold hp2ExtCell
      rw [if_neg h1, h2]
      ring
  · ring

/-! ### The depths `d < r - 59` -/

/-- The rest's factor far from the top: `hp2ExtFac r d ≤ 1.000001` for `r - d ≥ 22`. -/
lemma hp2ExtFac_le_of_ge {r d : ℕ} (h : d + 22 ≤ r) : hp2ExtFac r d ≤ 1.000001 := by
  have hn : (22 : ℝ) ≤ ((r - d : ℕ) : ℝ) := by exact_mod_cast (show 22 ≤ r - d by omega)
  have h1 : Real.exp (1 - ((r - d : ℕ) : ℝ)) ≤ Real.exp (-21) := Real.exp_le_exp.2 (by linarith)
  have h21 : Real.exp (-21) ≤ 1 / 1000000000 := by interval_decide (trust := kernel)
  refine (Real.exp_le_exp.2 ?_).trans exp_tiny_le
  have : (1 : ℝ) / 10 ^ 19 ≤ 1 / 10 ^ 10 := by norm_num
  linarith

/-- **The depths `d < r - 59` with the rest**: at most `1.000001` times the cells without it. -/
lemma sum_cells_ext_le_far (r : ℕ) :
    ∑ d ∈ Finset.range (r - 59), ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j)
      ≤ 1.000001 * ∑ d ∈ Finset.range (r - 59), ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hd := Finset.mem_range.1 hd
  have hj := Finset.mem_range.1 hj
  have hF := hp2ExtFac_le_of_ge (r := r) (d := d) (by omega)
  have h0 : 0 ≤ (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (hp2WinCell_nonneg r d hj)) (hp2Band_nonneg _)
  calc (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j)
      = hp2ExtFac r d * ((r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)) := by ring
    _ ≤ 1.000001 * ((r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)) :=
        mul_le_mul_of_nonneg_right hF h0

/-- **Region III's far part**, the posts `r - d ≥ 60`: for `2000 ≤ r₀ ≤ r`,
`∑_{200≤d<r-59}∑_j r·hp2WinCell r d j·hp2Band(40d + j)
  ≤ 3.8568·1.000001·(1.000001·2.084195·A_sl)(2/√199 + (log(r₀/118) + 0.6214)/√r₀)`. -/
theorem hp2WinRegionIIIfar_le {r₀ r : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) {W : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    {Asl At : ℝ}
    (hAsl : ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
      * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) ≤ Asl)
    (hAt : ∑ j ∈ Finset.range 40, (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2)
      ≤ At) :
    ∑ d ∈ Finset.Ico 200 (r - 59), ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ 3.8568 * 1.000001 * (1.000001 * 2.084195 * Asl)
        * (2 / √199 + (Real.log ((r₀ : ℝ) / 118) + 0.6214) / √(r₀ : ℝ)) := by
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hrr : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hAsl0 : 0 ≤ Asl := nonneg_of_sum_W_le hW (f := fun j => hp2PostC04 j * (2 * 0.632121)
      * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05))
    (fun j hj => mul_nonneg (mul_nonneg (hp2Win_tables_four hj).1 (by norm_num))
      (hp2SlabPrefHat_nonneg (le_trans (by norm_num) (le_max_right _ _))))
    (le_of_eq_of_le (Finset.sum_congr rfl fun j _ => by ring) hAsl)
  have hpt : ∀ d ∈ Finset.Ico 200 (r - 59), ∑ j ∈ Finset.range 40,
      (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ 3.8568 * 1.000001 * (1.000001 * 2.084195 * Asl)
        * ((r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hs := Real.sqrt_pos.2 hd0
    have hNr : ((r - d : ℕ) : ℝ) = (r : ℝ) - d := by push_cast [show d ≤ r by omega]; ring
    have hN0 : (0 : ℝ) < (r : ℝ) - d := by rw [← hNr]; exact_mod_cast (show 0 < r - d by omega)
    refine (hp2WinRegionIII_depth_le (r := r) (d := d) hd.1 (by omega) hW hAsl hAt).trans ?_
    have he1 := exp_two_mul_exp_le_of_ge (d := d) (by omega)
    have he2 := exp_three_one_mul_exp_le_of_ge (n := r - d) (by omega)
    have hk : hp2Kappa4 (hp2WinN r d) ≤ 2.084195 :=
      (hp2Kappa4_anti (by norm_num) (show 60 ≤ hp2WinN r d by
        unfold hp2WinN; simp [hp2PostStart, show 4 ≤ d by omega]; omega)).trans
        hp2Kappa4_sixty_le
    have hk0 := hp2Kappa4_nonneg (hp2WinN r d)
    rw [Real.exp_add]
    calc 3.8568 / ((d : ℝ) * √(d : ℝ))
          * (Real.exp (2 * Real.exp (1 - d)) * Real.exp (3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ))))
          * min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d) * Asl) ((r : ℝ) * At)
        ≤ 3.8568 / ((d : ℝ) * √(d : ℝ)) * (1.000001 * 1.000001)
          * ((r : ℝ) / ((r - d : ℕ) : ℝ) * 2.084195 * Asl) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul he1 he2 (Real.exp_pos _).le
            (by norm_num)) (by positivity)) ((min_le_left _ _).trans ?_)
            (le_min (by positivity) (by
              have : 0 ≤ At := nonneg_of_sum_W_le hW (f := fun _ => (2 * 0.632121)
                  * (hp2SlabPrefHat 1.05 / 1.05 ^ 2))
                (fun j _ => mul_nonneg (by norm_num)
                  (div_nonneg (hp2SlabPrefHat_nonneg (by norm_num)) (by norm_num)))
                (le_of_eq_of_le (Finset.sum_congr rfl fun j _ => by ring) hAt)
              positivity)) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by positivity))
            hAsl0
      _ = 3.8568 * 1.000001 * (1.000001 * 2.084195 * Asl)
          * ((r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))) := by
          rw [hNr]
          field_simp
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_far_le (by omega)).trans ?_) (by positivity)
  have hmono := log_add_div_sqrt_le (r₀ := (r₀ : ℝ)) (r := (r : ℝ)) (c := 118) (a := 0.6214)
    (by linarith) hrr (by norm_num) (by
      have h1 : Real.log (2000 / 118) ≤ Real.log ((r₀ : ℝ) / 118) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h2 : (2 : ℝ) ≤ Real.log (2000 / 118) + 0.6214 := by
        have : Real.exp (2 - 0.6214) ≤ 2000 / 118 := by interval_decide (trust := kernel)
        have := Real.log_le_log (Real.exp_pos _) this
        rw [Real.log_exp] at this
        linarith
      linarith)
  linarith

/-! ### The short posts `r - 59 ≤ d ≤ r - 3` -/

/-- **The short posts with the rest**: for `2000 ≤ r₀ ≤ r`, the region numerals `W`, `A_sl`, `A_t`
and a bound `H` on `∑_{3≤n<60} e^{7.1e^{1-n} + 10⁻¹⁹}min(κ₄(n)A_sl/n, A_t)`,
`∑_{r-59≤d<r-2}∑_j r·hp2WinCell r d j·hp2ExtFac r d·hp2Band(40d + j)
  ≤ 3.8568·1.000001·r₀/(r₀ - 60)/√(r₀ - 60)·H` (`RMF.hp2WinRegionIII_depth_le` per depth, the
rest's factor `e^{4e^{1-n} + 10⁻¹⁹}` joining the cells' `e^{3.1e^{1-n}}`). -/
theorem hp2ExtNear_le {r₀ r : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) {W : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    {Asl At H : ℝ}
    (hAsl : ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
      * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) ≤ Asl)
    (hAt : ∑ j ∈ Finset.range 40, (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2)
      ≤ At)
    (hH : ∑ n ∈ Finset.Ico (3 : ℕ) 60, Real.exp (7.1 * Real.exp (1 - (n : ℝ)) + 1 / 10 ^ 19)
      * min (hp2Kappa4 n * Asl / n) At ≤ H) :
    ∑ d ∈ Finset.Ico (r - 59) (r - 2), ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j)
      ≤ 3.8568 * 1.000001 * ((r₀ : ℝ) / ((r₀ : ℝ) - 60) / √((r₀ : ℝ) - 60)) * H := by
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hrr : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hAt0 : 0 ≤ At := nonneg_of_sum_W_le hW (f := fun _ => (2 * 0.632121)
      * (hp2SlabPrefHat 1.05 / 1.05 ^ 2))
    (fun j _ => mul_nonneg (by norm_num)
      (div_nonneg (hp2SlabPrefHat_nonneg (by norm_num)) (by norm_num)))
    (le_of_eq_of_le (Finset.sum_congr rfl fun j _ => by ring) hAt)
  set f : ℕ → ℝ := fun n => Real.exp (7.1 * Real.exp (1 - (n : ℝ)) + 1 / 10 ^ 19)
    * min (hp2Kappa4 n * Asl / n) At with hf
  have hc : 0 ≤ 3.8568 * 1.000001 * ((r₀ : ℝ) / ((r₀ : ℝ) - 60) / √((r₀ : ℝ) - 60)) := by
    have : (0 : ℝ) < (r₀ : ℝ) - 60 := by linarith
    positivity
  have hpt : ∀ d ∈ Finset.Ico (r - 59) (r - 2), ∑ j ∈ Finset.range 40,
      (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j)
      ≤ 3.8568 * 1.000001 * ((r₀ : ℝ) / ((r₀ : ℝ) - 60) / √((r₀ : ℝ) - 60)) * f (r - d) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hdr : (r : ℝ) - 60 ≤ d := by
      have : ((r - 59 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd.1
      push_cast [show 59 ≤ r by omega] at this
      linarith
    have hd0 : (0 : ℝ) < d := by linarith
    have hs := Real.sqrt_pos.2 hd0
    have hNr : ((r - d : ℕ) : ℝ) = (r : ℝ) - d := by push_cast [show d ≤ r by omega]; ring
    have hN0 : (0 : ℝ) < ((r - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < r - d by omega)
    have hWN : hp2WinN r d = r - d := by
      unfold hp2WinN; simp [hp2PostStart, show 4 ≤ d by omega]; omega
    have hF0 : 0 ≤ hp2ExtFac r d := (Real.exp_pos _).le
    have hsum : ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j)
        = hp2ExtFac r d * ∑ j ∈ Finset.range 40,
          (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    refine (mul_le_mul_of_nonneg_left (hp2WinRegionIII_depth_le (r := r) (d := d) (by omega)
      (by omega) hW hAsl hAt) hF0).trans ?_
    rw [hWN, Real.exp_add]
    have he1 := exp_two_mul_exp_le_of_ge (d := d) (by omega)
    have hmin : min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (r - d) * Asl) ((r : ℝ) * At)
        = (r : ℝ) * min (hp2Kappa4 (r - d) * Asl / ((r - d : ℕ) : ℝ)) At := by
      rw [mul_min_of_nonneg _ _ hr0.le]
      congr 1
      field_simp
    have hrd : (r : ℝ) / ((d : ℝ) * √(d : ℝ))
        ≤ (r₀ : ℝ) / ((r₀ : ℝ) - 60) / √((r₀ : ℝ) - 60) := by
      have h60 : (0 : ℝ) < (r₀ : ℝ) - 60 := by linarith
      have hs60 : √((r₀ : ℝ) - 60) ≤ √(d : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have hs600 := Real.sqrt_pos.2 h60
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (r : ℝ) * ((r₀ : ℝ) - 60) ≤ (r₀ : ℝ) * d := by nlinarith
      calc (r : ℝ) * (((r₀ : ℝ) - 60) * √((r₀ : ℝ) - 60))
          = (r : ℝ) * ((r₀ : ℝ) - 60) * √((r₀ : ℝ) - 60) := by ring
        _ ≤ (r₀ : ℝ) * d * √(d : ℝ) :=
          mul_le_mul h1 hs60 hs600.le (by positivity)
        _ = (r₀ : ℝ) * ((d : ℝ) * √(d : ℝ)) := by ring
    have hf0 : 0 ≤ f (r - d) := by
      rw [hf]
      exact mul_nonneg (Real.exp_pos _).le (le_min (by
        have := hp2Kappa4_nonneg (r - d)
        have : 0 ≤ Asl := nonneg_of_sum_W_le hW (f := fun j => hp2PostC04 j * (2 * 0.632121)
            * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05))
          (fun j hj => mul_nonneg (mul_nonneg (hp2Win_tables_four hj).1 (by norm_num))
            (hp2SlabPrefHat_nonneg (le_trans (by norm_num) (le_max_right _ _))))
          (le_of_eq_of_le (Finset.sum_congr rfl fun j _ => by ring) hAsl)
        positivity) hAt0)
    rw [hmin]
    have hfac : hp2ExtFac r d * Real.exp (3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
        = Real.exp (7.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)) + 1 / 10 ^ 19) := by
      unfold hp2ExtFac
      rw [← Real.exp_add]
      congr 1
      ring
    calc hp2ExtFac r d * (3.8568 / ((d : ℝ) * √(d : ℝ))
          * (Real.exp (2 * Real.exp (1 - d)) * Real.exp (3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ))))
          * ((r : ℝ) * min (hp2Kappa4 (r - d) * Asl / ((r - d : ℕ) : ℝ)) At))
        = 3.8568 * Real.exp (2 * Real.exp (1 - d)) * ((r : ℝ) / ((d : ℝ) * √(d : ℝ)))
          * f (r - d) := by
          rw [hf]
          simp only
          rw [← hfac]
          field_simp
      _ ≤ 3.8568 * 1.000001 * ((r₀ : ℝ) / ((r₀ : ℝ) - 60) / √((r₀ : ℝ) - 60)) * f (r - d) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left he1
            (by norm_num)) hrd (by positivity) (by positivity)) hf0
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hH) hc
  rw [Finset.sum_Ico_reflect f (r - 59) (show r - 2 ≤ r + 1 by omega),
    show r + 1 - (r - 2) = 3 by omega, show r + 1 - (r - 59) = 60 by omega]

/-! ### The deep cells and below -/

/-- **The deep constant against the scale**: `r·hp2WinDeep r·e^{-(r-2)}
  ≤ 6.682553·hp2SlabPrefHat 1.05·3.8568/(1.05²√r₀)` for `2000 ≤ r₀ ≤ r`. -/
lemma mul_hp2WinDeep_exp_le {r₀ r : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) :
    (r : ℝ) * hp2WinDeep r * Real.exp (-((r : ℝ) - 2))
      ≤ 6.682553 * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r₀ : ℝ)) := by
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hrr : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hs := Real.sqrt_pos.2 hr0
  have hB := hp2PrefixBound_le_G (M := r) (by omega) (c := 1.05) (by norm_num)
  have hP0 := hp2SlabPrefHat_nonneg (c := 1.05) (by norm_num)
  have hexp : Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20)
      * Real.exp (-((r : ℝ) - 2)) ≤ 6.682553 := by
    rw [← Real.exp_add]
    refine le_trans (le_of_eq ?_) exp_deep_le
    congr 1
    ring
  unfold hp2WinDeep
  calc (r : ℝ) * (Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20)
          * hp2PrefixBound r 1.05 / 1.05 ^ 2) * Real.exp (-((r : ℝ) - 2))
      ≤ (r : ℝ) * (Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20)
          * (hp2SlabPrefHat 1.05 * (3.8568 / ((r : ℝ) * √(r : ℝ)))) / 1.05 ^ 2)
          * Real.exp (-((r : ℝ) - 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le)
            (by norm_num)) hr0.le) (Real.exp_pos _).le
    _ = (Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20)
          * Real.exp (-((r : ℝ) - 2))) * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r : ℝ)) := by
        field_simp
    _ ≤ 6.682553 * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r : ℝ)) := by gcongr
    _ ≤ 6.682553 * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r₀ : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrr) (by norm_num))

/-- **Region IV with the rest**: for `2000 ≤ r₀ ≤ r`, bounds `B_j`, `B_sat` and
`Z ≥ ∑_{j<N} e^{2B_j + 10⁻¹⁹}(a_j - a_{j+1}) + e^{2B_sat + 10⁻¹⁹}a_N`, the deep cells and below
them contribute at most `2·0.632121·6.682553·hp2SlabPrefHat 1.05·3.8568/(1.05²√r₀)·Z`
(`hp2Band ≤ 2L·width`, `a_{40(r-2)+j} = e^{-(r-2)}a_j`). -/
theorem hp2ExtDeep_le {r₀ r N : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) (B : ℕ → ℝ) (Bsat : ℝ)
    {Z : ℝ}
    (hZ : ∑ j ∈ Finset.range N, Real.exp (2 * B j + 1 / 10 ^ 19)
          * (hp2CellEnd j - hp2CellEnd (j + 1))
        + Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N ≤ Z) :
    ∑ j ∈ Finset.range N, (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19)
        * hp2Band (40 * (r - 2) + j)
      + (r : ℝ) * hp2ExtSat r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))
      ≤ 2 * 0.632121 * 6.682553 * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r₀ : ℝ)) * Z := by
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hrr : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hL := one_sub_exp_neg_one_le
  have hL0 := one_sub_exp_neg_one_pos
  set C : ℝ := (r : ℝ) * hp2WinDeep r * Real.exp (-((r : ℝ) - 2)) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (hp2WinDeep_nonneg r)) (Real.exp_pos _).le
  have hCle := mul_hp2WinDeep_exp_le hr₀ hr
  have hr2 : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by push_cast [show 2 ≤ r by omega]; ring
  have he : Real.exp ((r : ℝ) - 2) * Real.exp (-((r : ℝ) - 2)) = 1 := by
    rw [← Real.exp_add]; simp
  -- each deep cell's band
  have hband : ∀ j, hp2Band (40 * (r - 2) + j)
      ≤ Real.exp (-((r : ℝ) - 2))
        * (2 * (1 - Real.exp (-1)) * (hp2CellEnd j - hp2CellEnd (j + 1))) := by
    intro j
    have h := exp_mul_hp2Band_le (r - 2) j
    rw [hr2] at h
    calc hp2Band (40 * (r - 2) + j)
        = Real.exp (-((r : ℝ) - 2)) * (Real.exp ((r : ℝ) - 2) * hp2Band (40 * (r - 2) + j)) := by
          rw [← mul_assoc, mul_comm (Real.exp (-((r : ℝ) - 2))), he, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  -- the last one
  have hlast : hp2PairVol (hp2CellEnd (40 * (r - 2) + N))
      ≤ Real.exp (-((r : ℝ) - 2)) * (2 * (1 - Real.exp (-1)) * hp2CellEnd N) := by
    refine (hp2PairVol_le (hp2CellEnd_pos _).le).trans (le_of_eq ?_)
    rw [hp2CellEnd_forty_mul_add, hr2]
    ring
  have hterm : ∀ j ∈ Finset.range N, (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19)
      * hp2Band (40 * (r - 2) + j)
      ≤ C * (2 * (1 - Real.exp (-1)))
        * (Real.exp (2 * B j + 1 / 10 ^ 19) * (hp2CellEnd j - hp2CellEnd (j + 1))) := by
    intro j _
    have h0 : 0 ≤ (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (hp2WinDeep_nonneg r)) (Real.exp_pos _).le
    calc (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19) * hp2Band (40 * (r - 2) + j)
        ≤ (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19)
          * (Real.exp (-((r : ℝ) - 2)) * (2 * (1 - Real.exp (-1))
            * (hp2CellEnd j - hp2CellEnd (j + 1)))) := mul_le_mul_of_nonneg_left (hband j) h0
      _ = _ := by rw [hC]; ring
  have hsat : (r : ℝ) * hp2ExtSat r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))
      ≤ C * (2 * (1 - Real.exp (-1))) * (Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N) := by
    have h0 : 0 ≤ (r : ℝ) * hp2ExtSat r Bsat :=
      mul_nonneg (Nat.cast_nonneg r) (hp2ExtSat_nonneg r Bsat)
    calc (r : ℝ) * hp2ExtSat r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))
        ≤ (r : ℝ) * hp2ExtSat r Bsat
          * (Real.exp (-((r : ℝ) - 2)) * (2 * (1 - Real.exp (-1)) * hp2CellEnd N)) :=
          mul_le_mul_of_nonneg_left hlast h0
      _ = _ := by rw [hC]; unfold hp2ExtSat; ring
  have hZ0 : 0 ≤ ∑ j ∈ Finset.range N, Real.exp (2 * B j + 1 / 10 ^ 19)
        * (hp2CellEnd j - hp2CellEnd (j + 1))
      + Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N :=
    add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le
      (sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j)))) (mul_nonneg (Real.exp_pos _).le
      (hp2CellEnd_pos _).le)
  calc ∑ j ∈ Finset.range N, (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19)
          * hp2Band (40 * (r - 2) + j)
        + (r : ℝ) * hp2ExtSat r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))
      ≤ C * (2 * (1 - Real.exp (-1))) * (∑ j ∈ Finset.range N,
          Real.exp (2 * B j + 1 / 10 ^ 19) * (hp2CellEnd j - hp2CellEnd (j + 1))
          + Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N) := by
        rw [mul_add, Finset.mul_sum]
        exact add_le_add (Finset.sum_le_sum hterm) hsat
    _ ≤ (6.682553 * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r₀ : ℝ))) * (2 * 0.632121) * Z :=
        mul_le_mul (mul_le_mul hCle (by linarith) (by positivity) (by
          have := hp2SlabPrefHat_nonneg (c := 1.05) (by norm_num)
          positivity)) hZ hZ0 (by
          have := hp2SlabPrefHat_nonneg (c := 1.05) (by norm_num)
          positivity)
    _ = _ := by ring

/-! ### All regions -/

/-- **The sum over the cells with the rest, region by region**: for `2000 ≤ r₀ ≤ r`, the region
bounds `P`, `W`, `e`, `B`, `A_sl`, `A_t` of `RMF/UniformLower/HP2Window/Regions.lean`, the short
posts' sum `H` with the rest and the deep cells' average `Z`,
`r·hp2ExtSum r N B_d B_sat ≤ 1.000001(I + II + III_far) + near + IV·Z`. -/
theorem hp2ExtSum_le {r₀ r N : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) {P : ℕ → ℕ → ℝ}
    (hP : ∀ d < 4, ∀ j < 40, hp2WinIexpr d j * hp2Band (40 * d + j) ≤ P d j) {W : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    {e : ℕ → ℝ} (he : ∀ d : ℕ, 4 ≤ d → d < 200 → Real.exp (2 * Real.exp (1 - (d : ℝ))) ≤ e d)
    {B : ℕ → ℕ → ℝ}
    (hB : ∀ d, 4 ≤ d → d < 200 → ∀ j < 40, hp2PrefixBound d (max (hp2PostCh4 j) 1.05) ≤ B d j)
    {Asl At H : ℝ}
    (hAsl : ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
      * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) ≤ Asl)
    (hAt : ∑ j ∈ Finset.range 40, (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2)
      ≤ At)
    (hH : ∑ n ∈ Finset.Ico (3 : ℕ) 60, Real.exp (7.1 * Real.exp (1 - (n : ℝ)) + 1 / 10 ^ 19)
      * min (hp2Kappa4 n * Asl / n) At ≤ H)
    (Bd : ℕ → ℝ) (Bsat : ℝ) {Z : ℝ}
    (hZ : ∑ j ∈ Finset.range N, Real.exp (2 * Bd j + 1 / 10 ^ 19)
          * (hp2CellEnd j - hp2CellEnd (j + 1))
        + Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N ≤ Z) :
    (r : ℝ) * hp2ExtSum r N Bd Bsat
      ≤ 1.000001 * ((1 + 4 / ((r₀ : ℝ) - 4)) * ∑ d ∈ Finset.range 4, ∑ j ∈ Finset.range 40, P d j
          + ∑ d ∈ Finset.Ico 4 200, (1 + d / ((r₀ : ℝ) - 200)) * e d
            * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * W j * B d j
          + 3.8568 * 1.000001 * (1.000001 * 2.084195 * Asl)
            * (2 / √199 + (Real.log ((r₀ : ℝ) / 118) + 0.6214) / √(r₀ : ℝ)))
        + 3.8568 * 1.000001 * ((r₀ : ℝ) / ((r₀ : ℝ) - 60) / √((r₀ : ℝ) - 60)) * H
        + 2 * 0.632121 * 6.682553 * hp2SlabPrefHat 1.05 * 3.8568 / (1.05 ^ 2 * √(r₀ : ℝ)) * Z := by
  rw [mul_hp2ExtSum_eq]
  have hIV := hp2ExtDeep_le hr₀ hr Bd Bsat hZ
  have hsplit := Finset.sum_range_add_sum_Ico (fun d => ∑ j ∈ Finset.range 40,
      (r : ℝ) * hp2WinCell r d j * hp2ExtFac r d * hp2Band (40 * d + j))
    (show r - 59 ≤ r - 2 by omega)
  rw [← hsplit]
  have hnear := hp2ExtNear_le hr₀ hr hW hAsl hAt hH
  have hfar := sum_cells_ext_le_far r
  -- the depths `d < r - 59`, without the rest's factor
  have hold : ∑ d ∈ Finset.range (r - 59), ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * ∑ d ∈ Finset.range 4, ∑ j ∈ Finset.range 40, P d j
          + ∑ d ∈ Finset.Ico 4 200, (1 + d / ((r₀ : ℝ) - 200)) * e d
            * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * W j * B d j
          + 3.8568 * 1.000001 * (1.000001 * 2.084195 * Asl)
            * (2 / √199 + (Real.log ((r₀ : ℝ) / 118) + 0.6214) / √(r₀ : ℝ)) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show 200 ≤ r - 59 by omega),
      ← Finset.sum_range_add_sum_Ico _ (show 4 ≤ 200 by norm_num)]
    have hI : ∑ d ∈ Finset.range 4, ∑ j ∈ Finset.range 40,
          (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
        ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * ∑ d ∈ Finset.range 4, ∑ j ∈ Finset.range 40, P d j := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun d hd => hp2WinRegionI_le hr₀ hr (Finset.mem_range.1 hd)
        (hP d (Finset.mem_range.1 hd))
    have hII : ∑ d ∈ Finset.Ico 4 200, ∑ j ∈ Finset.range 40,
          (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
        ≤ ∑ d ∈ Finset.Ico 4 200, (1 + d / ((r₀ : ℝ) - 200)) * e d
            * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * W j * B d j :=
      Finset.sum_le_sum fun d hd => by
        obtain ⟨h4, h200⟩ := Finset.mem_Ico.1 hd
        exact hp2WinRegionII_le hr₀ hr h4 h200 (he d h4 h200) hW (hB d h4 h200)
    have hIII := hp2WinRegionIIIfar_le hr₀ hr hW hAsl hAt
    linarith
  have hold' := mul_le_mul_of_nonneg_left hold (by norm_num : (0 : ℝ) ≤ 1.000001)
  linarith

end RMF
