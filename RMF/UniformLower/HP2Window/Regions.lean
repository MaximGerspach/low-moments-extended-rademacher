/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2Window.Pairs

/-!
# HP2's window integral: the sum over the cells, region by region

The cells' constants against their bands at a depth `d`, `∑_j r·hp2WinCell r d j·hp2Band(40d + j)`,
bounded uniformly in `r ≥ r₀ ≥ 2000`, with the depths split into regions; the numerals are the
emitted tables of `RMF/UniformLower/HP2WindowNum/`, entering here as hypotheses of the region
lemmas (discharged there).

* **Region I, `d ≤ 3`** (`RMF.hp2WinRegionI_le`): each cell's constant at `n₀ = 1000` against the
  cell's exact band, `r/(r - b) ≤ 1 + 4/(r₀ - 4)`.
* **Region II, `4 ≤ d < 200`** (`RMF.hp2WinRegionII_le`): the cells factor as a `j`-constant times
  `e^{2e^{1-d}}` times the prefix bound, `e^d·band ≤ 2L(e^{-j/40} - e^{-(j+1)/40})`,
  `r/(r - d) ≤ 1 + d/(r₀ - 200)`.
* **Region III, `200 ≤ d ≤ r - 3`**, one depth at a time (`RMF.hp2WinRegionIII_depth_le`): the
  slab bound decays like `d^{-3/2}` (`RMF.hp2SlabBound_le_G`), and the better of the regular and the
  trivial post bound is taken; over the depths by telescoping,
  `∑ r/((r-d)d^{3/2}) ≤ 2/√199 + (log(r/118) + 0.6214)/√r` (`RMF.sum_far_le`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The bands -/

/-- The cells' ends are positive. -/
lemma hp2CellEnd_pos (i : ℕ) : 0 < hp2CellEnd i := Real.exp_pos _

/-- `L = 1 - e^{-1} > 0`. -/
lemma one_sub_exp_neg_one_pos : 0 < 1 - Real.exp (-1) := by
  have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
  linarith

/-- The pair volume grows at most at rate `2L`: `V(t) - V(s) ≤ 2L(t - s)` for `0 ≤ s ≤ t`. -/
lemma hp2PairVol_sub_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    hp2PairVol t - hp2PairVol s ≤ 2 * (1 - Real.exp (-1)) * (t - s) := by
  have hL := one_sub_exp_neg_one_pos
  set L := 1 - Real.exp (-1) with hLdef
  unfold hp2PairVol
  rw [← hLdef]
  set A := max (L - s) 0 with hA
  set B := max (L - t) 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBA : B ≤ A := max_le_max (by linarith) le_rfl
  have hAL : A ≤ L := max_le (by linarith) hL.le
  have hAB : A - B ≤ t - s := by
    rcases le_total (L - t) 0 with h1 | h1
    · rw [hB, max_eq_right h1]
      rcases le_total (L - s) 0 with h2 | h2
      · rw [hA, max_eq_right h2]; linarith
      · rw [hA, max_eq_left h2]; linarith
    · rw [hB, max_eq_left h1, hA, max_eq_left (by linarith)]; linarith
  have e : L ^ 2 - B ^ 2 - (L ^ 2 - A ^ 2) = (A - B) * (A + B) := by ring
  rw [e]
  have h1 : 0 ≤ A - B := by linarith
  calc (A - B) * (A + B) ≤ (t - s) * (A + B) := mul_le_mul_of_nonneg_right hAB (by linarith)
    _ ≤ (t - s) * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = 2 * L * (t - s) := by ring

/-- `V(t) ≤ 2Lt` for `t ≥ 0`. -/
lemma hp2PairVol_le {t : ℝ} (ht : 0 ≤ t) : hp2PairVol t ≤ 2 * (1 - Real.exp (-1)) * t := by
  have h := hp2PairVol_sub_le le_rfl ht
  have h0 : hp2PairVol 0 = 0 := by
    unfold hp2PairVol
    rw [sub_zero, max_eq_left one_sub_exp_neg_one_pos.le, sub_self]
  rw [h0, sub_zero, sub_zero] at h
  exact h

/-- **A band is at most `2L` times its width**: `hp2Band i ≤ 2L(e^{-i/40} - e^{-(i+1)/40})`. -/
lemma hp2Band_le (i : ℕ) :
    hp2Band i ≤ 2 * (1 - Real.exp (-1)) * (hp2CellEnd i - hp2CellEnd (i + 1)) :=
  hp2PairVol_sub_le (Real.exp_pos _).le (hp2CellEnd_anti (Nat.le_succ i))

/-- **The band below `L`**: for `e^{-i/40} ≤ L`,
`hp2Band i = (a_i - a_{i+1})(2L - a_i - a_{i+1})`. -/
lemma hp2Band_eq_prod {i : ℕ} (hi : hp2CellEnd i ≤ 1 - Real.exp (-1)) :
    hp2Band i = (hp2CellEnd i - hp2CellEnd (i + 1))
      * (2 * (1 - Real.exp (-1)) - hp2CellEnd i - hp2CellEnd (i + 1)) := by
  have hi' : hp2CellEnd (i + 1) ≤ 1 - Real.exp (-1) := (hp2CellEnd_anti (Nat.le_succ i)).trans hi
  unfold hp2Band hp2PairVol
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- **The band across `L`**: for `a_{i+1} ≤ L ≤ a_i`, `hp2Band i = (L - a_{i+1})²`. -/
lemma hp2Band_eq_sq {i : ℕ} (h₁ : 1 - Real.exp (-1) ≤ hp2CellEnd i)
    (h₂ : hp2CellEnd (i + 1) ≤ 1 - Real.exp (-1)) :
    hp2Band i = (1 - Real.exp (-1) - hp2CellEnd (i + 1)) ^ 2 := by
  unfold hp2Band hp2PairVol
  rw [max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

/-- **The band above `L`** is empty: for `L ≤ a_{i+1}`, `hp2Band i = 0`. -/
lemma hp2Band_eq_zero {i : ℕ} (h : 1 - Real.exp (-1) ≤ hp2CellEnd (i + 1)) : hp2Band i = 0 := by
  have h' : 1 - Real.exp (-1) ≤ hp2CellEnd i := h.trans (hp2CellEnd_anti (Nat.le_succ i))
  unfold hp2Band hp2PairVol
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- `e^{-19/40} ≤ 1 - e^{-1} ≤ e^{-18/40}`: the window's side `L` lies in cell `18`. -/
lemma hp2CellEnd_eighteen_nineteen :
    hp2CellEnd 19 ≤ 1 - Real.exp (-1) ∧ 1 - Real.exp (-1) ≤ hp2CellEnd 18 := by
  unfold hp2CellEnd
  norm_num
  constructor <;> interval_decide (trust := kernel)

/-- From cell `19` on, the cells lie below `L`. -/
lemma hp2CellEnd_le_of_ge {i : ℕ} (hi : 19 ≤ i) : hp2CellEnd i ≤ 1 - Real.exp (-1) :=
  (hp2CellEnd_anti hi).trans hp2CellEnd_eighteen_nineteen.1

/-- `a_{40d+j} = e^{-d}a_j`. -/
lemma hp2CellEnd_forty_mul_add (d j : ℕ) :
    hp2CellEnd (40 * d + j) = Real.exp (-(d : ℝ)) * hp2CellEnd j := by
  unfold hp2CellEnd
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **The band of depth `d`, rescaled**: `e^d·hp2Band(40d + j) ≤ 2L(a_j - a_{j+1})`. -/
lemma exp_mul_hp2Band_le (d j : ℕ) :
    Real.exp (d : ℝ) * hp2Band (40 * d + j)
      ≤ 2 * (1 - Real.exp (-1)) * (hp2CellEnd j - hp2CellEnd (j + 1)) := by
  have h := hp2Band_le (40 * d + j)
  rw [hp2CellEnd_forty_mul_add, show 40 * d + j + 1 = 40 * d + (j + 1) by ring,
    hp2CellEnd_forty_mul_add] at h
  have he : Real.exp (d : ℝ) * Real.exp (-(d : ℝ)) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (d : ℝ) * hp2Band (40 * d + j)
      ≤ Real.exp (d : ℝ) * (2 * (1 - Real.exp (-1))
        * (Real.exp (-(d : ℝ)) * hp2CellEnd j - Real.exp (-(d : ℝ)) * hp2CellEnd (j + 1))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 2 * (1 - Real.exp (-1)) * (hp2CellEnd j - hp2CellEnd (j + 1))
        * (Real.exp (d : ℝ) * Real.exp (-(d : ℝ))) := by ring
    _ = _ := by rw [he, mul_one]

/-! ### The post constants in `n₀` -/

/-- A post constant from a bound on its inverse root: `C/√x ≤ Cκ` once `1 ≤ κ²x`. -/
lemma div_sqrt_le_mul {C x κ : ℝ} (hC : 0 ≤ C) (hx : 0 < x) (hκ : 0 ≤ κ) (h : 1 ≤ κ ^ 2 * x) :
    C / √x ≤ C * κ := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  rw [div_le_iff₀ hs]
  have h1 : 1 ≤ κ * √x := by
    have e : κ * √x = √(κ ^ 2 * x) := by
      rw [Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ]
    rw [e]
    exact Real.one_le_sqrt.2 h
  calc C = C * 1 := (mul_one C).symm
    _ ≤ C * (κ * √x) := mul_le_mul_of_nonneg_left h1 hC
    _ = C * κ * √x := by ring

/-- **Class `4`'s inverse root** `κ₄(n) = 1/√((0.495 - 0.5624/n)(0.495 - 1.2572/n))`. -/
noncomputable def hp2Kappa4 (n : ℕ) : ℝ := 1 / √((0.495 - 0.5624 / n) * (0.495 - 1.2572 / n))

/-- `κ₄` decreases in `n` from `n ≥ 3`. -/
lemma hp2Kappa4_anti {m n : ℕ} (hm : 3 ≤ m) (h : m ≤ n) : hp2Kappa4 n ≤ hp2Kappa4 m := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) < m := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have a₁ : 0.5624 / (n : ℝ) ≤ 0.5624 / m := div_le_div_of_nonneg_left (by norm_num) hm0 hmn
  have a₂ : 1.2572 / (n : ℝ) ≤ 1.2572 / m := div_le_div_of_nonneg_left (by norm_num) hm0 hmn
  have b₁ : 0.5624 / (m : ℝ) ≤ 0.5624 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have b₂ : 1.2572 / (m : ℝ) ≤ 1.2572 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have p₁ : 0 < (0.495 - 0.5624 / (m : ℝ)) * (0.495 - 1.2572 / m) :=
    mul_pos (by linarith) (by linarith)
  have hle : (0.495 - 0.5624 / (m : ℝ)) * (0.495 - 1.2572 / m)
      ≤ (0.495 - 0.5624 / (n : ℝ)) * (0.495 - 1.2572 / n) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  unfold hp2Kappa4
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 p₁) (Real.sqrt_le_sqrt hle)

/-! ### The slab bound's decay and its values -/

/-- `ν = 1/2 - 4·10⁻⁶`, the variance floors' main term. -/
lemma hp2Slab_nu : (1 / 2 - 4 / 10 ^ 6 : ℝ) = 0.499996 := by norm_num

/-- **The slab bound from depth `200`**: `hp2SlabBound M c ≤ hp2SlabPrefactor c·3.8568/(M√M)` for
`M ≥ 200`, `c ≥ 0` (`RMF.hp2VarSums_ge` with `S₁ ≥ 0.1602M`, `S₂ ≥ 0.1654M`, `S₃ ≥ 0.1637M`). -/
theorem hp2SlabBound_le_G {M : ℕ} (hM : 200 ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    hp2SlabBound M c ≤ hp2SlabPrefactor c * (3.8568 / ((M : ℝ) * √(M : ℝ))) := by
  have hM' : (200 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hn : ((M : ℝ) - 2) / 3 ≤ ((M / 3 : ℕ) : ℝ) := by
    have h1 := Nat.div_add_mod M 3
    have h3 : (M : ℝ) = 3 * ((M / 3 : ℕ) : ℝ) + ((M % 3 : ℕ) : ℝ) := by exact_mod_cast h1.symm
    have h4 : ((M % 3 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : M % 3 ≤ 2)
    linarith
  have hn2 : (M : ℝ) / 3 ≤ ((M - M / 3 - M / 3 : ℕ) : ℝ) := by
    have h5 : ((M - M / 3 - M / 3 : ℕ) : ℝ) = (M : ℝ) - 2 * ((M / 3 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      ring
    have h6 : 3 * ((M / 3 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.mul_div_le M 3
    linarith
  obtain ⟨hS₁, hS₂, hS₃⟩ := hp2VarSums_ge M
  have hT0 := (hp2CosTail_le 0).1
  have hT1 := (hp2CosTail_le (M / 3)).2.2 (by omega)
  have hT2 := (hp2CosTail_le (M - M / 3)).2.2 (by omega)
  have hs₁ : 0.1602 * (M : ℝ) ≤ hp2VarSum₁ M := by linarith
  have hs₂ : 0.1654 * (M : ℝ) ≤ hp2VarSum₂ M := by linarith
  have hs₃ : 0.1637 * (M : ℝ) ≤ hp2VarSum₃ M := by linarith
  have hprod : 0.004337 * (M : ℝ) ^ 3 ≤ hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M := by
    have h12 : 0.1602 * (M : ℝ) * (0.1654 * M) ≤ hp2VarSum₁ M * hp2VarSum₂ M :=
      mul_le_mul hs₁ hs₂ (by positivity) (by linarith)
    have h123 := mul_le_mul h12 hs₃ (by positivity) (mul_nonneg (by linarith) (by linarith))
    have hM3 : 0 ≤ (M : ℝ) ^ 3 := by positivity
    linarith
  set R : ℝ := (M : ℝ) * √(M : ℝ) with hR
  have hR0 : 0 < R := by rw [hR]; exact mul_pos hM0 (Real.sqrt_pos.2 hM0)
  have hRsq : R ^ 2 = (M : ℝ) ^ 3 := by
    rw [hR, mul_pow, Real.sq_sqrt hM0.le]
    ring
  have hsqrt : 0.16507 * R ≤ √(2 * π * (hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M)) := by
    rw [show 0.16507 * R = √((0.16507 * R) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, hRsq]
    have hM3 : 0 ≤ 0.004337 * (M : ℝ) ^ 3 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * π)
    have h2 := mul_le_mul_of_nonneg_right
      (by linarith [Real.pi_gt_d6] : (2 : ℝ) * 3.141592 ≤ 2 * π) hM3
    have hM30 : 0 ≤ (M : ℝ) ^ 3 := by positivity
    nlinarith
  have hfrac : 2 / (π * √(2 * π * (hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M)))
      ≤ 3.8568 / R := by
    have hden : π * (0.16507 * R)
        ≤ π * √(2 * π * (hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M)) :=
      mul_le_mul_of_nonneg_left hsqrt Real.pi_pos.le
    have hpos : 0 < π * (0.16507 * R) := by positivity
    calc 2 / (π * √(2 * π * (hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M)))
        ≤ 2 / (π * (0.16507 * R)) := div_le_div_of_nonneg_left (by norm_num) hpos hden
      _ ≤ 3.8568 / R := by
          rw [div_le_div_iff₀ hpos hR0]
          nlinarith [Real.pi_gt_d6]
  unfold hp2SlabBound
  rw [if_pos (by omega)]
  exact mul_le_mul_of_nonneg_left hfrac (hp2SlabPrefactor_nonneg hc)

/-- **The slab bound at depth `M` from its variance floors in closed form**: for `M ≥ 12`,
`c ≥ 0`, tail bounds `t₂ ≥ hp2CosTail ⌊M/3⌋`, `t₃ ≥ hp2CosTail (M - ⌊M/3⌋)` and a numeral `g`
with `4 ≤ 2·3.14159³g²L₁L₂L₃` (`Lᵢ` the closed forms of `RMF.hp2VarSums_ge`),
`hp2SlabBound M c ≤ hp2SlabPrefactor c·g`. -/
theorem hp2SlabBound_le_of_closed {M : ℕ} (hM : 12 ≤ M) {c t₂ t₃ g : ℝ} (hc : 0 ≤ c)
    (ht₂ : hp2CosTail (M / 3) ≤ t₂) (ht₃ : hp2CosTail (M - M / 3) ≤ t₃) (hg0 : 0 ≤ g)
    (hL₁ : 0 < ((M / 3 : ℕ) : ℝ) * 0.499996 - 1.8642 / 2 - 0.0159)
    (hL₂ : 0 < ((M - M / 3 - M / 3 : ℕ) : ℝ) * 0.499996 - t₂ / 2 - 0.0159)
    (hL₃ : 0 < ((M / 3 : ℕ) : ℝ) * 0.499996 - t₃ / 2 - 0.0159)
    (hg : 4 ≤ 2 * 3.14159 ^ 3 * g ^ 2 * ((((M / 3 : ℕ) : ℝ) * 0.499996 - 1.8642 / 2 - 0.0159)
      * (((M - M / 3 - M / 3 : ℕ) : ℝ) * 0.499996 - t₂ / 2 - 0.0159)
      * (((M / 3 : ℕ) : ℝ) * 0.499996 - t₃ / 2 - 0.0159))) :
    hp2SlabBound M c ≤ hp2SlabPrefactor c * g := by
  obtain ⟨hS₁, hS₂, hS₃⟩ := hp2VarSums_ge M
  have hT0 := (hp2CosTail_le 0).1
  rw [hp2Slab_nu] at hS₁ hS₂ hS₃
  refine (hp2SlabBound_le_of_le (by omega) hc hL₁ hL₂ hL₃ (by linarith) (by linarith)
    (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ (hp2SlabPrefactor_nonneg hc))
  set P := (((M / 3 : ℕ) : ℝ) * 0.499996 - 1.8642 / 2 - 0.0159)
      * (((M - M / 3 - M / 3 : ℕ) : ℝ) * 0.499996 - t₂ / 2 - 0.0159)
      * (((M / 3 : ℕ) : ℝ) * 0.499996 - t₃ / 2 - 0.0159) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  have hπ := Real.pi_gt_d6
  -- `2/(π√(2πP)) ≤ g` from `(2/π)² ≤ g²·2πP`
  have hs : 0 < √(2 * π * P) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_iff₀ (mul_pos Real.pi_pos hs)]
  have hsq : 2 ≤ g * π * √(2 * π * P) := by
    have hpos : 0 ≤ g * π * √(2 * π * P) := by positivity
    have h2 : (g * π * √(2 * π * P)) ^ 2 = 2 * π ^ 3 * g ^ 2 * P := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hπ3 : (3.14159 : ℝ) ^ 3 ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have h3 : 4 ≤ (g * π * √(2 * π * P)) ^ 2 := by
      rw [h2]
      have := mul_le_mul_of_nonneg_right hπ3 (by positivity : (0 : ℝ) ≤ 2 * g ^ 2 * P)
      nlinarith
    nlinarith
  linarith

/-- **The doubled frequency's cosine tails from block `3`**:
`hp2CosTail n = e^{-(n-1)}·e/(e-1) ≤ 1.5821e^{-(n-1)}`. -/
lemma hp2CosTail_le_exp {n : ℕ} (hn : 3 ≤ n) :
    hp2CosTail n ≤ 1.5821 * Real.exp (-((n : ℝ) - 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 3 := ⟨n - 3, by omega⟩
  have he1 : (2.7182 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hu : Real.exp 1 / (Real.exp 1 - 1) ≤ 1.5821 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have e : hp2CosTail (i + 3) = Real.exp (-((i : ℝ) + 2)) * (Real.exp 1 / (Real.exp 1 - 1)) :=
    rfl
  rw [e, show -(((i + 3 : ℕ) : ℝ) - 1) = -((i : ℝ) + 2) by push_cast; ring, mul_comm]
  exact mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le

/-! ### The telescoped sums -/

/-- `1/(x√x) ≤ 2(1/√(x-1) - 1/√x)` for `x ≥ 2`. -/
lemma one_div_mul_sqrt_le {x : ℝ} (hx : 2 ≤ x) :
    1 / (x * √x) ≤ 2 / √(x - 1) - 2 / √x := by
  have hx0 : 0 < x := by linarith
  have hu := Real.sqrt_pos.2 hx0
  have hv := Real.sqrt_pos.2 (show (0 : ℝ) < x - 1 by linarith)
  have hu2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have hv2 : √(x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hvu : √(x - 1) ≤ √x := Real.sqrt_le_sqrt (by linarith)
  set u := √x
  set v := √(x - 1)
  have h1 : (u - v) * (u + v) = 1 := by nlinarith
  have key : v ≤ 2 * u ^ 2 * (u - v) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hvu) (sub_nonneg.2 hvu),
      mul_nonneg (sub_nonneg.2 hvu) hv.le, mul_nonneg (sub_nonneg.2 hvu) hu.le]
  rw [← hu2, div_sub_div _ _ hv.ne' hu.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hu hv]

/-- **`∑_{d∈[a,b)} d^{-3/2} ≤ 2/√(a-1) - 2/√(b-1)`** for `2 ≤ a ≤ b` (telescoping). -/
lemma sum_Ico_one_div_mul_sqrt_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ d ∈ Finset.Ico a b, 1 / ((d : ℝ) * √(d : ℝ))
      ≤ 2 / √((a : ℝ) - 1) - 2 / √((b : ℝ) - 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb]
    have h := one_div_mul_sqrt_le (x := (b : ℝ)) (by exact_mod_cast ha.trans hb)
    push_cast
    rw [show (b : ℝ) + 1 - 1 = b by ring]
    linarith

/-- `1/x ≤ log x - log(x - 1)` for `x > 1`. -/
lemma one_div_le_log_sub {x : ℝ} (hx : 1 < x) : 1 / x ≤ Real.log x - Real.log (x - 1) := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by
    exact div_pos (by linarith) hx0)
  rw [Real.log_div (by linarith) hx0.ne'] at h
  have e : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
  linarith

/-- **`∑_{d∈[A,B)} 1/(r - d) ≤ log(r - A) - log(r - B)`** for `A ≤ B < r` (telescoping). -/
lemma sum_Ico_one_div_sub_le {r A B : ℕ} (hAB : A ≤ B) (hBr : B < r) :
    ∑ d ∈ Finset.Ico A B, 1 / ((r : ℝ) - d) ≤ Real.log ((r : ℝ) - A) - Real.log ((r : ℝ) - B) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hB ih =>
    rw [Finset.sum_Ico_succ_top hB]
    have h := one_div_le_log_sub (x := (r : ℝ) - B) (by
      have : (B : ℝ) + 1 < r := by exact_mod_cast hBr
      linarith)
    have := ih (by omega)
    push_cast
    rw [show (r : ℝ) - (B + 1) = (r : ℝ) - B - 1 by ring]
    linarith

/-- `1/√x ≤ 2(√x - √(x - 1))` for `x ≥ 1`. -/
lemma one_div_sqrt_le_two_mul_sub {x : ℝ} (hx : 1 ≤ x) : 1 / √x ≤ 2 * (√x - √(x - 1)) := by
  have hx0 : 0 < x := by linarith
  have hu := Real.sqrt_pos.2 hx0
  have hv0 : 0 ≤ √(x - 1) := Real.sqrt_nonneg _
  have hu2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have hv2 : √(x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hvu : √(x - 1) ≤ √x := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ hu]
  nlinarith

/-- **`∑_{d∈[A,B)} 1/√d ≤ 2√(B - 1)`** for `1 ≤ A ≤ B`. -/
lemma sum_Ico_one_div_sqrt_le {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ d ∈ Finset.Ico A B, 1 / √(d : ℝ) ≤ 2 * √((B : ℝ) - 1) := by
  have key : ∀ B, A ≤ B → ∑ d ∈ Finset.Ico A B, 1 / √(d : ℝ)
      ≤ 2 * √((B : ℝ) - 1) - 2 * √((A : ℝ) - 1) := by
    intro B hAB
    induction B, hAB using Nat.le_induction with
    | base => simp
    | succ B hB ih =>
      rw [Finset.sum_Ico_succ_top hB]
      have h := one_div_sqrt_le_two_mul_sub (x := (B : ℝ)) (by exact_mod_cast hA.trans hB)
      push_cast
      rw [show (B : ℝ) + 1 - 1 = B by ring]
      linarith
  have := key B hAB
  have h0 : 0 ≤ √((A : ℝ) - 1) := Real.sqrt_nonneg _
  linarith

/-- **`∑_{d∈[A,B)} √d ≤ (B - A)√(B - 1)`**. -/
lemma sum_Ico_sqrt_le {A B : ℕ} (hAB : A < B) :
    ∑ d ∈ Finset.Ico A B, √(d : ℝ) ≤ ((B : ℝ) - A) * √((B : ℝ) - 1) := by
  have h := Finset.sum_le_sum (s := Finset.Ico A B) (f := fun d : ℕ => √(d : ℝ))
    (g := fun _ : ℕ => √((B : ℝ) - 1)) fun d hd => Real.sqrt_le_sqrt (by
      have := (Finset.mem_Ico.1 hd).2
      have : (d : ℝ) + 1 ≤ B := by exact_mod_cast this
      linarith)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hAB.le] at h
  exact h

/-- `log y ≤ 2(√y - 1)` for `y > 0`. -/
lemma log_le_two_mul_sqrt_sub_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * (√y - 1) := by
  have hs := Real.sqrt_pos.2 hy
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hy.le] at h
  linarith

/-- **The `r`-dependent part decreases**: for `r₀ ≤ r`, `c > 0` and `log(r₀/c) + a ≥ 2`,
`(log(r/c) + a)/√r ≤ (log(r₀/c) + a)/√r₀`. -/
lemma log_add_div_sqrt_le {r r₀ c a : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hc : 0 < c)
    (h2 : 2 ≤ Real.log (r₀ / c) + a) :
    (Real.log (r / c) + a) / √r ≤ (Real.log (r₀ / c) + a) / √r₀ := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hs₀ := Real.sqrt_pos.2 hr₀
  have hs := Real.sqrt_pos.2 hr0
  have hss : √r₀ ≤ √r := Real.sqrt_le_sqrt hr
  have hlog : Real.log (r / c) = Real.log (r₀ / c) + Real.log (r / r₀) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hl := log_le_two_mul_sqrt_sub_one (show 0 < r / r₀ by positivity)
  rw [Real.sqrt_div' r hr₀.le] at hl
  rw [hlog, div_le_div_iff₀ hs hs₀]
  set C := Real.log (r₀ / c) + a
  have e : √r / √r₀ * √r₀ = √r := div_mul_cancel₀ _ hs₀.ne'
  nlinarith [mul_le_mul_of_nonneg_right hl hs₀.le]

/-- `(1 + x)²(1 - x) ≥ 1` for `0 ≤ x ≤ 1/2`. -/
lemma one_le_one_add_sq_mul_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 ≤ (1 + x) ^ 2 * (1 - x) := by
  have h : 0 ≤ 1 - x - x ^ 2 := by nlinarith
  nlinarith [mul_nonneg hx0 h]

/-- **A term with `d ≤ r/2`**: `1/((r - d)√d) ≤ (1/r)(1/√d) + (2/r²)√d` for `0 < d ≤ r/2`. -/
lemma one_div_sub_mul_sqrt_le {r d : ℝ} (hd : 0 < d) (hdr : d ≤ r / 2) :
    1 / ((r - d) * √d) ≤ 1 / r * (1 / √d) + 2 / r ^ 2 * √d := by
  have hr : 0 < r := by linarith
  have hs := Real.sqrt_pos.2 hd
  have hsq : √d ^ 2 = d := Real.sq_sqrt hd.le
  have hrd : 0 < r - d := by linarith
  have e : 1 / r * (1 / √d) + 2 / r ^ 2 * √d = (r + 2 * d) / (r ^ 2 * √d) := by
    field_simp
    rw [hsq]
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : r ^ 2 ≤ (r + 2 * d) * (r - d) := by nlinarith
  have := mul_le_mul_of_nonneg_right key hs.le
  nlinarith

/-- **A term with `n = r - d ≤ r/2`**: `1/(n√(r - n)) ≤ (1/√r)(1/n + 1/r)` for `0 < n ≤ r/2`. -/
lemma one_div_mul_sqrt_sub_le {r n : ℝ} (hn : 0 < n) (hnr : n ≤ r / 2) :
    1 / (n * √(r - n)) ≤ 1 / √r * (1 / n + 1 / r) := by
  have hr : 0 < r := by linarith
  set x := n / r with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx, div_le_iff₀ hr]; linarith
  have h1x : 0 < 1 - x := by linarith
  have hsr := Real.sqrt_pos.2 hr
  have hsx := Real.sqrt_pos.2 h1x
  have hrn : r - n = r * (1 - x) := by rw [hx]; field_simp
  have hkey : 1 ≤ (1 + x) * √(1 - x) := by
    rw [show (1 + x) * √(1 - x) = √((1 + x) ^ 2 * (1 - x)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]]
    exact Real.one_le_sqrt.2 (one_le_one_add_sq_mul_one_sub hx0 hx1)
  rw [hrn, Real.sqrt_mul hr.le]
  have e : 1 / √r * (1 / n + 1 / r) = (1 + x) / (n * √r) := by
    rw [hx]
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ n * √r)
  nlinarith

/-- `3√(r/2)/r ≤ 2.1214/√r` for `r > 0`. -/
lemma three_mul_sqrt_half_div_le {r : ℝ} (hr : 0 < r) :
    3 * √(r / 2) / r ≤ 2.1214 / √r := by
  have hsr := Real.sqrt_pos.2 hr
  have hsq : √r ^ 2 = r := Real.sq_sqrt hr.le
  have h2 : (1.41421 : ℝ) ≤ √2 := by rw [Real.le_sqrt' (by norm_num)]; norm_num
  have hs2 := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)
  have hsd : √(r / 2) = √r / √2 := Real.sqrt_div' r (by norm_num : (0 : ℝ) ≤ 2)
  have hrr : √r * √r = r := Real.mul_self_sqrt hr.le
  rw [hsd, div_le_div_iff₀ hr hsr]
  have e : 3 * (√r / √2) * √r = 3 * r / √2 := by
    calc 3 * (√r / √2) * √r = 3 * (√r * √r) / √2 := by ring
      _ = 3 * r / √2 := by rw [hrr]
  rw [e, div_le_iff₀ hs2]
  nlinarith

/-- **The far sum's part `d ≤ r/2`**: `∑_{d∈[200, r - ⌊r/2⌋)} 1/((r - d)√d) ≤ 2.1214/√r` for
`r ≥ 2000`. -/
lemma sum_far_low_le {r : ℕ} (hr : 2000 ≤ r) :
    ∑ d ∈ Finset.Ico 200 (r - r / 2), 1 / (((r : ℝ) - d) * √(d : ℝ)) ≤ 2.1214 / √(r : ℝ) := by
  have hr' : (2000 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hh1 : ((r / 2 : ℕ) : ℝ) ≤ r / 2 := by
    have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
    have : (2 : ℝ) * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hh2 : (r : ℝ) / 2 - 1 ≤ ((r / 2 : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := r) (b := 2) (by norm_num)
    have : (r : ℝ) < (r / 2 : ℕ) * 2 + 2 := by exact_mod_cast this
    linarith
  have hB : ((r - r / 2 : ℕ) : ℝ) = (r : ℝ) - ((r / 2 : ℕ) : ℝ) := by
    push_cast [Nat.div_le_self r 2]
    ring
  have hpt : ∀ d ∈ Finset.Ico 200 (r - r / 2), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ 1 / (r : ℝ) * (1 / √(d : ℝ)) + 2 / (r : ℝ) ^ 2 * √(d : ℝ) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hd0 : (0 : ℝ) < d := by
      have : (200 : ℝ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hdr : (d : ℝ) ≤ r / 2 := by
      have : (d : ℝ) + 1 ≤ ((r - r / 2 : ℕ) : ℝ) := by exact_mod_cast hd.2
      linarith
    exact one_div_sub_mul_sqrt_le hd0 hdr
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA := sum_Ico_one_div_sqrt_le (A := 200) (B := r - r / 2) (by norm_num) (by omega)
  have hBs := sum_Ico_sqrt_le (A := 200) (B := r - r / 2) (by omega)
  have hc : ((r - r / 2 : ℕ) : ℝ) - 1 ≤ r / 2 := by linarith
  have hs1 : √(((r - r / 2 : ℕ) : ℝ) - 1) ≤ √((r : ℝ) / 2) := Real.sqrt_le_sqrt hc
  have hcnt : ((r - r / 2 : ℕ) : ℝ) - 200 ≤ r / 2 := by linarith
  have hs0 := Real.sqrt_nonneg (((r - r / 2 : ℕ) : ℝ) - 1)
  have hsh := Real.sqrt_nonneg ((r : ℝ) / 2)
  have hcnt0 : (0 : ℝ) ≤ ((r - r / 2 : ℕ) : ℝ) - 200 := by linarith
  have e1 : 1 / (r : ℝ) * ∑ d ∈ Finset.Ico 200 (r - r / 2), 1 / √(d : ℝ)
      ≤ 1 / (r : ℝ) * (2 * √((r : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left (hA.trans (by linarith)) (by positivity)
  have e2 : 2 / (r : ℝ) ^ 2 * ∑ d ∈ Finset.Ico 200 (r - r / 2), √(d : ℝ)
      ≤ 2 / (r : ℝ) ^ 2 * ((r / 2) * √((r : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left (hBs.trans (mul_le_mul hcnt hs1 hs0 (by positivity)))
      (by positivity)
  have e3 : 1 / (r : ℝ) * (2 * √((r : ℝ) / 2)) + 2 / (r : ℝ) ^ 2 * ((r / 2) * √((r : ℝ) / 2))
      = 3 * √((r : ℝ) / 2) / r := by
    field_simp
    ring
  have := three_mul_sqrt_half_div_le hr0
  linarith

/-- **The far sum's part `r - d ≤ r/2`**:
`∑_{d∈[r - ⌊r/2⌋, r - 59)} 1/((r - d)√d) ≤ (log(r/118) + 1/2)/√r` for `r ≥ 2000`. -/
lemma sum_far_high_le {r : ℕ} (hr : 2000 ≤ r) :
    ∑ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ) := by
  have hr' : (2000 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hsr := Real.sqrt_pos.2 hr0
  have hh1 : ((r / 2 : ℕ) : ℝ) ≤ r / 2 := by
    have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
    have : (2 : ℝ) * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hh2 : (r : ℝ) / 2 - 1 ≤ ((r / 2 : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := r) (b := 2) (by norm_num)
    have : (r : ℝ) < (r / 2 : ℕ) * 2 + 2 := by exact_mod_cast this
    linarith
  have hA : ((r - r / 2 : ℕ) : ℝ) = (r : ℝ) - ((r / 2 : ℕ) : ℝ) := by
    push_cast [Nat.div_le_self r 2]
    ring
  have hpt : ∀ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ 1 / √(r : ℝ) * (1 / ((r : ℝ) - d) + 1 / (r : ℝ)) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hn : (r : ℝ) - d ≤ r / 2 := by
      have : ((r - r / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hn0 : 0 < (r : ℝ) - d := by
      have : d + 59 < r := by omega
      have : (d : ℝ) + 59 < r := by exact_mod_cast this
      linarith
    have h := one_div_mul_sqrt_sub_le hn0 hn
    rw [sub_sub_cancel] at h
    exact h
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hlog := sum_Ico_one_div_sub_le (r := r) (A := r - r / 2) (B := r - 59) (by omega)
    (by omega)
  have e1 : (r : ℝ) - ((r - r / 2 : ℕ) : ℝ) = ((r / 2 : ℕ) : ℝ) := by rw [hA]; ring
  have e2 : (r : ℝ) - ((r - 59 : ℕ) : ℝ) = 59 := by push_cast [show 59 ≤ r by omega]; ring
  rw [e1, e2] at hlog
  have hhpos : (0 : ℝ) < ((r / 2 : ℕ) : ℝ) := by linarith
  have hl : Real.log ((r / 2 : ℕ) : ℝ) - Real.log 59 ≤ Real.log ((r : ℝ) / 118) := by
    rw [← Real.log_div hhpos.ne' (by norm_num)]
    exact Real.log_le_log (by positivity)
      (by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith)
  have hcnt : (((r - 59 - (r - r / 2) : ℕ) : ℝ)) * (1 / (r : ℝ)) ≤ 1 / 2 := by
    have hle : ((r - 59 - (r - r / 2) : ℕ) : ℝ) ≤ r / 2 := by
      have : r - 59 - (r - r / 2) ≤ r / 2 := by omega
      have : ((r - 59 - (r - r / 2) : ℕ) : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [mul_one_div, div_le_iff₀ hr0]
    linarith
  have hsum : ∑ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / ((r : ℝ) - d)
      + ((r - 59 - (r - r / 2) : ℕ) : ℝ) * (1 / (r : ℝ))
      ≤ Real.log ((r : ℝ) / 118) + 1 / 2 := by linarith
  calc 1 / √(r : ℝ) * (∑ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / ((r : ℝ) - d)
        + ((r - 59 - (r - r / 2) : ℕ) : ℝ) * (1 / (r : ℝ)))
      ≤ 1 / √(r : ℝ) * (Real.log ((r : ℝ) / 118) + 1 / 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ) := by ring

/-- `r/((r - d)d√d) = 1/(d√d) + 1/((r - d)√d)`. -/
lemma div_sub_mul_eq {r d : ℝ} (hd : 0 < d) (hrd : 0 < r - d) :
    r / ((r - d) * (d * √d)) = 1 / (d * √d) + 1 / ((r - d) * √d) := by
  have hs := Real.sqrt_pos.2 hd
  field_simp
  ring

/-- **The far part's sum**: for `r ≥ 2000`,
`∑_{d∈[200, r-59)} r/((r - d)d√d) ≤ 2/√199 + (log(r/118) + 0.6214)/√r`. -/
theorem sum_far_le {r : ℕ} (hr : 2000 ≤ r) :
    ∑ d ∈ Finset.Ico 200 (r - 59), (r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))
      ≤ 2 / √199 + (Real.log ((r : ℝ) / 118) + 0.6214) / √(r : ℝ) := by
  have hr' : (2000 : ℝ) ≤ r := by exact_mod_cast hr
  have hsplit : ∀ d ∈ Finset.Ico 200 (r - 59),
      (r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))
        = 1 / ((d : ℝ) * √(d : ℝ)) + 1 / (((r : ℝ) - d) * √(d : ℝ)) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hd0 : (0 : ℝ) < d := by
      have : (200 : ℝ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hrd : (0 : ℝ) < (r : ℝ) - d := by
      have : d + 59 < r := by omega
      have : (d : ℝ) + 59 < r := by exact_mod_cast this
      linarith
    exact div_sub_mul_eq hd0 hrd
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hi := sum_Ico_one_div_mul_sqrt_le (a := 200) (b := r - 59) (by norm_num) (by omega)
  have hb : ((r - 59 : ℕ) : ℝ) - 1 = (r : ℝ) - 60 := by push_cast [show 59 ≤ r by omega]; ring
  have h199 : ((200 : ℕ) : ℝ) - 1 = 199 := by norm_num
  rw [hb, h199] at hi
  have hi' : 2 / √(r : ℝ) ≤ 2 / √((r : ℝ) - 60) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by linarith))
      (Real.sqrt_le_sqrt (by linarith))
  have h2 : ∑ d ∈ Finset.Ico 200 (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ 2.1214 / √(r : ℝ) + (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ) := by
    rw [← Finset.Ico_union_Ico_eq_Ico (b := r - r / 2) (by omega) (by omega),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
    exact add_le_add (sum_far_low_le hr) (sum_far_high_le hr)
  have e : 2.1214 / √(r : ℝ) + (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ)
      = (Real.log ((r : ℝ) / 118) + 0.6214) / √(r : ℝ) + 2 / √(r : ℝ) := by ring
  linarith

/-! ### The cells' constants, with `r` taken out -/

/-- `hp2PairBoundOf C E μ μ B B = C·e^E·e^{μ + 5·10⁻²⁰}·B`. -/
lemma hp2PairBoundOf_same (C E μ B : ℝ) :
    hp2PairBoundOf C E μ μ B B = C * Real.exp E * (Real.exp (μ + 5 / 10 ^ 20) * B) := by
  unfold hp2PairBoundOf
  ring

/-- The post's `n₀` is `1000` once `r - b ≥ 1000`. -/
lemma hp2WinN_eq {r d : ℕ} (h : hp2PostStart d + 1000 ≤ r) : hp2WinN r d = 1000 := by
  unfold hp2WinN
  omega

/-- `3.1e^{1-n} ≤ 10⁻⁸` for `n ≥ 21`. -/
lemma three_one_mul_exp_le {n : ℕ} (hn : 21 ≤ n) :
    3.1 * Real.exp (1 - (n : ℝ)) ≤ 1 / 10 ^ 8 := by
  have hn' : (21 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (Real.exp_le_exp.2 (by linarith : 1 - (n : ℝ) ≤ -20)).trans exp_neg_twenty_le_numeral
  have h0 := Real.exp_pos (1 - (n : ℝ))
  calc 3.1 * Real.exp (1 - (n : ℝ)) ≤ 3.1 * (1 / 485000000) := by gcongr
    _ ≤ 1 / 10 ^ 8 := by norm_num

/-! #### Region I: `d ≤ 3` -/

/-- The class constant `C₀` of the depths `d ≤ 3`. -/
noncomputable def hp2WinC0 (d j : ℕ) : ℝ :=
  if d = 0 then hp2PostC00 j else if d = 1 then hp2PostC01 j else if d = 2 then hp2PostC02 j
  else hp2PostC03 j

/-- `κ̂_d ≥ 1/√((0.495 - a₁/1000)(0.495 - a₂/1000))` for the classes `d ≤ 3`. -/
noncomputable def hp2WinKappaHat (d : ℕ) : ℝ :=
  if d = 0 then 2.02364 else if d = 1 then 2.022339 else if d = 2 then 2.021877 else 2.023023

/-- `m̂_d ≥ e^{hp2PrefixExpM d + 5·10⁻²⁰}` for `d ≤ 3`. -/
noncomputable def hp2WinMuHat (d : ℕ) : ℝ :=
  if d = 0 then 1.000001 else if d = 1 then 3.616332 else if d = 2 then 6.054914 else 18.781833

/-- **The prefix bound in numerals** for `d ≤ 3`: exact at `d = 0`, the polynomials bounding
`RMF.hp2ShortPrefixBound` at `d = 1, 2`, `20.08554c²` at `d = 3`. -/
noncomputable def hp2WinBHat (d j : ℕ) : ℝ :=
  if d = 0 then (3 / 2 + 1 / 10 ^ 15 + hp2WinShift 0 j) ^ 2
  else if d = 1 then 3.6165 * (3 / 2 + 1 / 10 ^ 15 + hp2WinShift 1 j) ^ 2
    + 0.36788 * (3 / 2 + 1 / 10 ^ 15 + hp2WinShift 1 j) + 0.135336
  else if d = 2 then 6.0551 * (3 / 2 + 1 / 10 ^ 15 + hp2WinShift 2 j) ^ 2
    + 0.36788 * (3 / 2 + 1 / 10 ^ 15 + hp2WinShift 2 j) + 0.135336
  else 20.08554 * hp2WinShift d j ^ 2

/-- **The mass exponent's numeral** for `d ≤ 3`: `2(M_j - 0.0971 + S_d) + 1.6·10⁻²⁰ + 10⁻⁸`. -/
noncomputable def hp2WinEI (d j : ℕ) : ℝ :=
  2 * (hp2CellMassD j - 0.0971 + hp2MassS d) + 1.6 / 10 ^ 20 + 1 / 10 ^ 8

/-- **Region I's cell expression**: `C₀κ̂m̂B̂e^{Ê}`. -/
noncomputable def hp2WinIexpr (d j : ℕ) : ℝ :=
  hp2WinC0 d j * hp2WinKappaHat d * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)

/-- `e^{2(3/2 + 10⁻¹⁵)} ≤ 20.08554`. -/
lemma exp_three_le_numeral : Real.exp (2 * (3 / 2 + 1 / 10 ^ 15)) ≤ 20.08554 := by
  interval_decide (trust := kernel)

/-- The post constant of the classes `d ≤ 3` at `n₀ = 1000`. -/
lemma hp2WinCpost_le_I {d j : ℕ} (hd : d < 4) (hj : j < 40) :
    hp2WinCpost d j 1000 ≤ hp2WinC0 d j * hp2WinKappaHat d := by
  unfold hp2WinCpost hp2WinC0 hp2WinKappaHat
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with h | h | h | h <;> subst h <;> simp only
    [if_true, if_false, show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num,
      show (2 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 2 by norm_num] <;> push_cast
  · exact div_sqrt_le_mul (hp2Win_tables_zero hj).1 (by norm_num) (by norm_num) (by norm_num)
  · exact div_sqrt_le_mul (hp2Win_tables_one hj).1 (by norm_num) (by norm_num) (by norm_num)
  · exact div_sqrt_le_mul (hp2Win_tables_two hj).1 (by norm_num) (by norm_num) (by norm_num)
  · exact div_sqrt_le_mul (hp2Win_tables_three hj).1 (by norm_num) (by norm_num) (by norm_num)

/-- The prefix masses in numerals, `d ≤ 3`: `e^{hp2PrefixExpM d + 5·10⁻²⁰} ≤ m̂_d`. -/
lemma exp_hp2PrefixExpM_le {d : ℕ} (hd : d < 4) :
    Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) ≤ hp2WinMuHat d := by
  unfold hp2PrefixExpM hp2PrefixCosU hp2WinMuHat
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with h | h | h | h <;> subst h <;> norm_num
    <;> interval_decide (trust := kernel)

/-- The prefix bound in numerals, `d ≤ 3`: `hp2WinPrefix d j ≤ hp2WinBHat d j`. -/
lemma hp2WinPrefix_le_BHat {d j : ℕ} (hd : d < 4) (hj : j < 40) :
    hp2WinPrefix d j ≤ hp2WinBHat d j := by
  have hc := le_hp2WinShift (d := d) hj
  have hc0 : (0 : ℝ) ≤ hp2WinShift d j := by linarith
  unfold hp2WinPrefix hp2WinBHat
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with h | h | h | h <;> subst h
  · simp
  · simp only [show (1 : ℕ) ≠ 0 by norm_num, if_false, show (1 : ℕ) ≤ 2 by norm_num, if_true]
    exact (min_le_left _ _).trans (hp2ShortPrefixBound_one_two_le hc0).1
  · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false,
      show (2 : ℕ) ≤ 2 by norm_num, if_true]
    exact (min_le_left _ _).trans (hp2ShortPrefixBound_one_two_le hc0).2
  · simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 2 by norm_num, show ¬ (3 : ℕ) ≤ 2 by norm_num, if_false]
    unfold hp2PrefixBound
    refine (min_le_left _ _).trans ?_
    exact mul_le_mul_of_nonneg_right exp_three_le_numeral (sq_nonneg _)

/-- The mass exponent in numerals, `d ≤ 3`, `r ≥ d + 21`. -/
lemma hp2CellMassExp_le_EI {d j r : ℕ} (hr : d + 21 ≤ r) :
    hp2CellMassExp d j r ≤ hp2WinEI d j := by
  have h := three_one_mul_exp_le (n := r - d) (by omega)
  unfold hp2CellMassExp hp2WinEI
  linarith

/-- **Region I's cells with `r` taken out**: for `d ≤ 3`, `j < 40` and `2000 ≤ r₀ ≤ r`,
`r·hp2WinCell r d j ≤ (1 + 4/(r₀ - 4))·hp2WinIexpr d j`. -/
theorem hp2WinCell_le_I {r₀ r d j : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) (hd : d < 4)
    (hj : j < 40) :
    (r : ℝ) * hp2WinCell r d j ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * hp2WinIexpr d j := by
  have hb4 : hp2PostStart d ≤ 4 := by unfold hp2PostStart; split_ifs <;> omega
  have hb2 : 2 ≤ hp2PostStart d := two_le_hp2PostStart d
  have hN : hp2WinN r d = 1000 := hp2WinN_eq (by omega)
  have hC := hp2WinCpost_le_I hd hj
  have hC0 : 0 ≤ hp2WinCpost d j 1000 := hp2WinCpost_nonneg hj 1000
  have hE := Real.exp_le_exp.2 (hp2CellMassExp_le_EI (j := j) (show d + 21 ≤ r by omega))
  have hM := exp_hp2PrefixExpM_le hd
  have hB := hp2WinPrefix_le_BHat hd hj
  have hB0 := hp2WinPrefix_nonneg (d := d) hj
  have hr' : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hbR : (hp2PostStart d : ℝ) ≤ 4 := by exact_mod_cast hb4
  have hNr : ((r - hp2PostStart d : ℕ) : ℝ) = (r : ℝ) - hp2PostStart d := by
    push_cast [show hp2PostStart d ≤ r by omega]; ring
  have hfac : (r : ℝ) / ((r - hp2PostStart d : ℕ) : ℝ) ≤ 1 + 4 / ((r₀ : ℝ) - 4) := by
    rw [hNr, div_le_iff₀ (by linarith)]
    have h1 : 4 / ((r₀ : ℝ) - 4) * ((r : ℝ) - hp2PostStart d) ≥ hp2PostStart d := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    nlinarith
  have hcell : hp2WinCell r d j = hp2WinReg r d j := by
    unfold hp2WinCell; rw [if_pos hd]
  rw [hcell, hp2WinReg, hN, hp2PairBoundOf_same]
  have hPB : hp2WinCpost d j 1000 * Real.exp (hp2CellMassExp d j r)
      * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)
      ≤ hp2WinIexpr d j := by
    unfold hp2WinIexpr
    have e1 := mul_le_mul hC hE (Real.exp_pos _).le (by
      unfold hp2WinC0 hp2WinKappaHat
      have := (hp2Win_tables_zero hj).1
      have := (hp2Win_tables_one hj).1
      have := (hp2Win_tables_two hj).1
      have := (hp2Win_tables_three hj).1
      split_ifs <;> positivity)
    have e2 := mul_le_mul hM hB hB0 (by unfold hp2WinMuHat; split_ifs <;> norm_num)
    calc hp2WinCpost d j 1000 * Real.exp (hp2CellMassExp d j r)
          * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)
        ≤ hp2WinC0 d j * hp2WinKappaHat d * Real.exp (hp2WinEI d j)
          * (hp2WinMuHat d * hp2WinBHat d j) :=
          mul_le_mul e1 e2 (by positivity) (le_trans (by positivity) e1)
      _ = _ := by ring
  have hPB0 : 0 ≤ hp2WinCpost d j 1000 * Real.exp (hp2CellMassExp d j r)
      * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j) := by positivity
  have hfac0 : 0 ≤ (r : ℝ) / ((r - hp2PostStart d : ℕ) : ℝ) := by positivity
  have hf0 : 0 ≤ 1 + 4 / ((r₀ : ℝ) - 4) := by
    have := div_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) ≤ (r₀ : ℝ) - 4 by linarith)
    linarith
  calc (r : ℝ) * (hp2WinCpost d j 1000 * Real.exp (hp2CellMassExp d j r)
        * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)
        / ((r - hp2PostStart d : ℕ) : ℝ))
      = (r : ℝ) / ((r - hp2PostStart d : ℕ) : ℝ) * (hp2WinCpost d j 1000
        * Real.exp (hp2CellMassExp d j r)
        * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)) := by ring
    _ ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * hp2WinIexpr d j := mul_le_mul hfac hPB hPB0 hf0

/-- **Region I**: for `d ≤ 3`, `2000 ≤ r₀ ≤ r` and bounds `P j` on the cells' expressions against
their bands, `∑_j r·hp2WinCell r d j·hp2Band(40d + j) ≤ (1 + 4/(r₀ - 4))∑_j P j`. -/
theorem hp2WinRegionI_le {r₀ r d : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) (hd : d < 4)
    {P : ℕ → ℝ} (hP : ∀ j < 40, hp2WinIexpr d j * hp2Band (40 * d + j) ≤ P j) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * ∑ j ∈ Finset.range 40, P j := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hf : 0 ≤ 1 + 4 / ((r₀ : ℝ) - 4) := by
    have := div_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) ≤ (r₀ : ℝ) - 4 by linarith)
    linarith
  calc (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * hp2WinIexpr d j * hp2Band (40 * d + j) :=
        mul_le_mul_of_nonneg_right (hp2WinCell_le_I hr₀ hr hd hj) (hp2Band_nonneg _)
    _ ≤ (1 + 4 / ((r₀ : ℝ) - 4)) * P j := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hP j hj) hf

/-! #### The depths `d ≥ 4` -/

/-- **`Ê₄(j)`**, the exponent of the numerals `hp2WinW j` of the depths `d ≥ 4`:
`2(M_j - 0.0971 + 3.16·10⁻⁶) + 1.6·10⁻²⁰ + 10⁻⁸ + 3.72·10⁻⁸ - 0.11003 + 5·10⁻²⁰`. -/
noncomputable def hp2WinE4 (j : ℕ) : ℝ :=
  2 * (hp2CellMassD j - 0.0971 + 3.16 / 10 ^ 6) + 1.6 / 10 ^ 20 + 1 / 10 ^ 8
    + (3.72 / 10 ^ 8 - 0.11003 + 5 / 10 ^ 20)

/-- The exponents of the depths `d ≥ 4`, against `Ê₄(j)`. -/
lemma hp2Win_exponent_le {d j r : ℕ} (hd : 4 ≤ d) :
    hp2CellMassExp d j r + (hp2PrefixExpM d + 5 / 10 ^ 20) - d
      ≤ hp2WinE4 j + (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ))
        - 1 / 10 ^ 8) := by
  have hS : hp2MassS d = Real.exp (1 - d) + 3.16 / 10 ^ 6 := by
    simp [hp2MassS, show d ≠ 0 by omega, show d ≠ 1 by omega, show d ≠ 2 by omega,
      show d ≠ 3 by omega]
  have hU : hp2PrefixCosU d = -0.11003 := by
    simp [hp2PrefixCosU, show d ≠ 0 by omega, show d ≠ 1 by omega, show d ≠ 2 by omega,
      show d ≠ 3 by omega]
  unfold hp2CellMassExp hp2PrefixExpM hp2WinE4
  rw [hS, hU]
  linarith

/-- **The cells of the depths `d ≥ 4`, with the band rescaled**: for `j < 40`, `d + 3 ≤ r` and
`β + 10⁻⁸ ≥ 2e^{1-d} + 3.1e^{1-(r-d)}`,
`r·hp2WinCell r d j·hp2Band(40d + j)
  ≤ min((r/(r - d))C₀κ₄(n₀)B, rB'/1.05²)·e^β·2L·e^{Ê₄(j)}(a_j - a_{j+1})`,
`B = hp2PrefixBound d (max(c_h, 1.05))`, `B' = hp2PrefixBound d 1.05`. -/
theorem hp2WinCell_band_le_four {r d j : ℕ} (hd : 4 ≤ d) (hdr : d + 3 ≤ r) (hj : j < 40)
    {β : ℝ} (hβ : 2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)) ≤ β + 1 / 10 ^ 8) :
    (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ min ((r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
            * hp2PrefixBound d (max (hp2PostCh4 j) 1.05))
          ((r : ℝ) * (hp2PrefixBound d 1.05 / 1.05 ^ 2))
        * (Real.exp β * (2 * (1 - Real.exp (-1)))
          * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)))) := by
  have hb : hp2PostStart d = d := by simp [hp2PostStart, hd]
  have hN0 : (0 : ℝ) < ((r - d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - d)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  obtain ⟨hC0, _⟩ := hp2Win_tables_four hj
  have hB0 := hp2PrefixBound_nonneg d (c := max (hp2PostCh4 j) 1.05)
    (le_trans (by norm_num) (le_max_right _ _))
  have hB'0 := hp2PrefixBound_nonneg d (c := 1.05) (by norm_num)
  have hband0 := hp2Band_nonneg (40 * d + j)
  -- the key: the masses against the band
  set X := Real.exp (hp2CellMassExp d j r) * Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20)
    * hp2Band (40 * d + j) with hX
  set Y := Real.exp β * (2 * (1 - Real.exp (-1)))
    * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))) with hY
  have hXY : X ≤ Y := by
    have hexp := hp2Win_exponent_le (d := d) (j := j) (r := r) hd
    have hb2 := exp_mul_hp2Band_le d j
    have e : Real.exp (hp2CellMassExp d j r) * Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20)
        = Real.exp (hp2CellMassExp d j r + (hp2PrefixExpM d + 5 / 10 ^ 20) - d)
          * Real.exp (d : ℝ) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (hp2CellMassExp d j r + (hp2PrefixExpM d + 5 / 10 ^ 20) - d)
        ≤ Real.exp β * Real.exp (hp2WinE4 j) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hw0 : 0 ≤ hp2CellEnd j - hp2CellEnd (j + 1) :=
      sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j))
    calc X = Real.exp (hp2CellMassExp d j r + (hp2PrefixExpM d + 5 / 10 ^ 20) - d)
          * (Real.exp (d : ℝ) * hp2Band (40 * d + j)) := by rw [hX, e]; ring
      _ ≤ (Real.exp β * Real.exp (hp2WinE4 j))
          * (2 * (1 - Real.exp (-1)) * (hp2CellEnd j - hp2CellEnd (j + 1))) :=
          mul_le_mul h1 hb2 (by positivity) (by positivity)
      _ = Y := by rw [hY]; ring
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- the two constants
  have hreg : (r : ℝ) * hp2WinReg r d j * hp2Band (40 * d + j)
      = (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
        * hp2PrefixBound d (max (hp2PostCh4 j) 1.05) * X := by
    unfold hp2WinReg
    rw [hp2PairBoundOf_same, hb]
    have hCp : hp2WinCpost d j (hp2WinN r d) = hp2PostC04 j * hp2Kappa4 (hp2WinN r d) := by
      simp [hp2WinCpost, hp2Kappa4, show d ≠ 0 by omega, show d ≠ 1 by omega,
        show d ≠ 2 by omega, show d ≠ 3 by omega, div_eq_mul_one_div (hp2PostC04 j)]
    have hPf : hp2WinPrefix d j = hp2PrefixBound d (max (hp2PostCh4 j) 1.05) := by
      simp [hp2WinPrefix, hp2WinShift, show d ≠ 0 by omega, show ¬ d ≤ 2 by omega,
        show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega]
    rw [hCp, hPf, hX]
    field_simp
  have htriv : (r : ℝ) * hp2WinTriv r d j * hp2Band (40 * d + j)
      = (r : ℝ) * (hp2PrefixBound d 1.05 / 1.05 ^ 2) * X := by
    unfold hp2WinTriv
    rw [hp2PairBoundOf_same, hb, hX]
    field_simp
  have hcell : hp2WinCell r d j = min (hp2WinReg r d j) (hp2WinTriv r d j) := by
    unfold hp2WinCell; rw [if_neg (by omega)]
  have hmin : (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      = min ((r : ℝ) * hp2WinReg r d j * hp2Band (40 * d + j))
        ((r : ℝ) * hp2WinTriv r d j * hp2Band (40 * d + j)) := by
    rw [hcell, mul_min_of_nonneg _ _ hr0, min_mul_of_nonneg _ _ hband0]
  rw [hmin, hreg, htriv, ← min_mul_of_nonneg _ _ hX0]
  refine mul_le_mul_of_nonneg_left hXY (le_min ?_ ?_)
  · have hk : 0 ≤ hp2Kappa4 (hp2WinN r d) := by unfold hp2Kappa4; positivity
    positivity
  · positivity

/-! #### Numerals shared by the regions `d ≥ 4` -/

/-- `L = 1 - e^{-1} ≤ 0.632121`. -/
lemma one_sub_exp_neg_one_le : 1 - Real.exp (-1) ≤ 0.632121 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have e : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have : (0.367879 : ℝ) ≤ 1 / Real.exp 1 := by
    rw [le_div_iff₀ h0]; nlinarith
  linarith

/-- `κ₄(1000) ≤ 2.023923`. -/
lemma hp2Kappa4_thousand_le : hp2Kappa4 1000 ≤ 2.023923 := by
  have h := div_sqrt_le_mul (C := 1)
    (x := (0.495 - 0.5624 / (1000 : ℕ)) * (0.495 - 1.2572 / (1000 : ℕ)))
    (κ := 2.023923) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold hp2Kappa4
  simpa using h

/-- `κ₄(60) ≤ 2.084195`. -/
lemma hp2Kappa4_sixty_le : hp2Kappa4 60 ≤ 2.084195 := by
  have h := div_sqrt_le_mul (C := 1)
    (x := (0.495 - 0.5624 / (60 : ℕ)) * (0.495 - 1.2572 / (60 : ℕ)))
    (κ := 2.084195) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold hp2Kappa4
  simpa using h

/-- `κ₄ ≥ 0`. -/
lemma hp2Kappa4_nonneg (n : ℕ) : 0 ≤ hp2Kappa4 n := by unfold hp2Kappa4; positivity

/-- `e^{4.2·10⁻⁹}, e^{6.4·10⁻⁹} ≤ 1.000001`. -/
lemma exp_tiny_le : Real.exp (6.4 / 10 ^ 9) ≤ 1.000001 := by
  interval_decide (trust := kernel)

/-- `e^{2e^{1-d}} ≤ 1.000001` for `d ≥ 21`. -/
lemma exp_two_mul_exp_le_of_ge {d : ℕ} (hd : 21 ≤ d) :
    Real.exp (2 * Real.exp (1 - (d : ℝ))) ≤ 1.000001 := by
  have hd' : (21 : ℝ) ≤ d := by exact_mod_cast hd
  have h := (Real.exp_le_exp.2 (by linarith : 1 - (d : ℝ) ≤ -20)).trans exp_neg_twenty_le_numeral
  refine (Real.exp_le_exp.2 ?_).trans exp_tiny_le
  linarith

/-- `e^{3.1e^{1-n}} ≤ 1.000001` for `n ≥ 21`. -/
lemma exp_three_one_mul_exp_le_of_ge {n : ℕ} (hn : 21 ≤ n) :
    Real.exp (3.1 * Real.exp (1 - (n : ℝ))) ≤ 1.000001 := by
  have hn' : (21 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (Real.exp_le_exp.2 (by linarith : 1 - (n : ℝ) ≤ -20)).trans exp_neg_twenty_le_numeral
  refine (Real.exp_le_exp.2 ?_).trans exp_tiny_le
  linarith

/-- **The slab prefactor's numeral bound** `20.0857(3/2 + 10⁻¹⁴ + c)·hp2PrefixK c`
(`RMF.hp2SlabPrefactor_le`). -/
noncomputable def hp2SlabPrefHat (c : ℝ) : ℝ := 20.0857 * ((3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c)

/-- The prefix bound from depth `200` in numerals:
`hp2PrefixBound M c ≤ hp2SlabPrefHat c·3.8568/(M√M)`. -/
lemma hp2PrefixBound_le_G {M : ℕ} (hM : 200 ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    hp2PrefixBound M c ≤ hp2SlabPrefHat c * (3.8568 / ((M : ℝ) * √(M : ℝ))) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  refine (min_le_right _ _).trans ((hp2SlabBound_le_G hM hc).trans ?_)
  exact mul_le_mul_of_nonneg_right (hp2SlabPrefactor_le hc) (by positivity)

/-- A sum of minima is at most the minimum of the sums. -/
lemma sum_min_le_min_sum {s : Finset ℕ} {a b : ℕ → ℝ} :
    ∑ j ∈ s, min (a j) (b j) ≤ min (∑ j ∈ s, a j) (∑ j ∈ s, b j) :=
  le_min (Finset.sum_le_sum fun _ _ => min_le_left _ _)
    (Finset.sum_le_sum fun _ _ => min_le_right _ _)

/-! #### Region II: `4 ≤ d < 200` -/

/-- **Region II**: for `4 ≤ d < 200`, `2000 ≤ r₀ ≤ r`, `e ≥ e^{2e^{1-d}}`, the numerals
`W j ≥ e^{Ê₄(j)}(a_j - a_{j+1})` and prefix bounds `B j`,
`∑_j r·hp2WinCell r d j·hp2Band(40d + j)
  ≤ (1 + d/(r₀ - 200))·e·∑_j C₀(j)·2.023923·(2·0.632121)·W j·B j`. -/
theorem hp2WinRegionII_le {r₀ r d : ℕ} (hr₀ : 2000 ≤ r₀) (hr : r₀ ≤ r) (hd4 : 4 ≤ d)
    (hd : d < 200) {e : ℝ} (he : Real.exp (2 * Real.exp (1 - (d : ℝ))) ≤ e) {W B : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    (hB : ∀ j < 40, hp2PrefixBound d (max (hp2PostCh4 j) 1.05) ≤ B j) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ (1 + d / ((r₀ : ℝ) - 200)) * e
        * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * W j * B j := by
  have hr₀' : (2000 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hrr : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hdR : (d : ℝ) < 200 := by exact_mod_cast hd
  have hN : hp2WinN r d = 1000 := hp2WinN_eq (by simp [hp2PostStart, hd4]; omega)
  have hNr : ((r - d : ℕ) : ℝ) = (r : ℝ) - d := by push_cast [show d ≤ r by omega]; ring
  have hfac : (r : ℝ) / ((r - d : ℕ) : ℝ) ≤ 1 + d / ((r₀ : ℝ) - 200) := by
    rw [hNr, div_le_iff₀ (by linarith)]
    have h1 : (d : ℝ) / ((r₀ : ℝ) - 200) * ((r : ℝ) - d) ≥ d := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    nlinarith
  have hβ : 2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ))
      ≤ 2 * Real.exp (1 - d) + 1 / 10 ^ 8 := by
    have := three_one_mul_exp_le (n := r - d) (by omega)
    linarith
  have hL := one_sub_exp_neg_one_le
  have hL0 := one_sub_exp_neg_one_pos
  have hk := hp2Kappa4_thousand_le
  have hk0 := hp2Kappa4_nonneg 1000
  have he0 : 0 ≤ e := le_trans (Real.exp_pos _).le he
  have hfac0 : 0 ≤ 1 + d / ((r₀ : ℝ) - 200) := by
    have := div_nonneg (Nat.cast_nonneg d) (show (0 : ℝ) ≤ (r₀ : ℝ) - 200 by linarith)
    linarith
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  obtain ⟨hC0, _⟩ := hp2Win_tables_four hj
  have hw0 : 0 ≤ hp2CellEnd j - hp2CellEnd (j + 1) :=
    sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j))
  have hWj := hW j hj
  have hW0 : 0 ≤ W j := le_trans (by positivity) hWj
  have hBj := hB j hj
  have hBt0 := hp2PrefixBound_nonneg d (c := max (hp2PostCh4 j) 1.05)
    (le_trans (by norm_num) (le_max_right _ _))
  have hc := hp2WinCell_band_le_four (r := r) (d := d) (j := j) hd4 (by omega) hj hβ
  rw [hN] at hc
  refine hc.trans ?_
  have hY : Real.exp (2 * Real.exp (1 - d)) * (2 * (1 - Real.exp (-1)))
      * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)))
      ≤ e * (2 * 0.632121) * W j :=
    mul_le_mul (mul_le_mul he (by linarith) (by positivity) he0) hWj (by positivity)
      (by positivity)
  have hR : (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 1000)
      * hp2PrefixBound d (max (hp2PostCh4 j) 1.05)
      ≤ (1 + d / ((r₀ : ℝ) - 200)) * (hp2PostC04 j * 2.023923) * B j :=
    mul_le_mul (mul_le_mul hfac (mul_le_mul_of_nonneg_left hk hC0) (by positivity) hfac0)
      hBj hBt0 (by positivity)
  calc min ((r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 1000)
          * hp2PrefixBound d (max (hp2PostCh4 j) 1.05))
        ((r : ℝ) * (hp2PrefixBound d 1.05 / 1.05 ^ 2))
        * (Real.exp (2 * Real.exp (1 - d)) * (2 * (1 - Real.exp (-1)))
          * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))))
      ≤ ((1 + d / ((r₀ : ℝ) - 200)) * (hp2PostC04 j * 2.023923) * B j)
        * (e * (2 * 0.632121) * W j) :=
        mul_le_mul ((min_le_left _ _).trans hR) hY (by positivity)
          (le_trans (by positivity) hR)
    _ = (1 + d / ((r₀ : ℝ) - 200)) * e
        * (hp2PostC04 j * 2.023923 * (2 * 0.632121) * W j * B j) := by ring

/-! #### Region III: `200 ≤ d ≤ r - 3` -/

/-- **Region III, one depth**: for `200 ≤ d`, `d + 3 ≤ r`, the numerals `W` and the constants
`Asl`, `At`, `∑_j r·hp2WinCell r d j·hp2Band(40d + j)
  ≤ 3.8568/(d√d)·e^{2e^{1-d} + 3.1e^{1-(r-d)}}·min((r/(r - d))κ₄(n₀)Asl, r·At)`. -/
theorem hp2WinRegionIII_depth_le {r d : ℕ} (hd : 200 ≤ d) (hdr : d + 3 ≤ r) {W : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    {Asl At : ℝ}
    (hAsl : ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
      * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) ≤ Asl)
    (hAt : ∑ j ∈ Finset.range 40, (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2)
      ≤ At) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ 3.8568 / ((d : ℝ) * √(d : ℝ))
        * Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
        * min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d) * Asl) ((r : ℝ) * At) := by
  set β := 2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)) with hβdef
  set g : ℝ := 3.8568 / ((d : ℝ) * √(d : ℝ)) with hg
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hN0 : (0 : ℝ) < ((r - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < r - d by omega)
  have hL := one_sub_exp_neg_one_le
  have hL0 := one_sub_exp_neg_one_pos
  have hk0 := hp2Kappa4_nonneg (hp2WinN r d)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  -- per `j`: the regular and the trivial term
  have hpt : ∀ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ min (g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d))
            * (hp2PostC04 j * (2 * 0.632121) * W j * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05)))
          (g * Real.exp β * (r : ℝ)
            * ((2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2))) := by
    intro j hj
    have hj := Finset.mem_range.1 hj
    obtain ⟨hC0, _⟩ := hp2Win_tables_four hj
    have hw0 : 0 ≤ hp2CellEnd j - hp2CellEnd (j + 1) :=
      sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j))
    have hWj := hW j hj
    have hW0 : 0 ≤ W j := le_trans (by positivity) hWj
    have hc := hp2WinCell_band_le_four (r := r) (d := d) (j := j) (β := β) (by omega) hdr hj
      (by rw [hβdef]; linarith [show (0 : ℝ) < 1 / 10 ^ 8 by norm_num])
    refine hc.trans ?_
    have hcj : (0 : ℝ) ≤ max (hp2PostCh4 j) 1.05 := le_trans (by norm_num) (le_max_right _ _)
    have hB := hp2PrefixBound_le_G (M := d) hd hcj
    have hB' := hp2PrefixBound_le_G (M := d) hd (c := 1.05) (by norm_num)
    have hB0 := hp2PrefixBound_nonneg d hcj
    have hB'0 := hp2PrefixBound_nonneg d (c := 1.05) (by norm_num)
    have hY : Real.exp β * (2 * (1 - Real.exp (-1)))
        * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)))
        ≤ Real.exp β * (2 * 0.632121) * W j :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le) hWj
        (by positivity) (by positivity)
    have hY0 : 0 ≤ Real.exp β * (2 * (1 - Real.exp (-1)))
        * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))) := by positivity
    rw [min_mul_of_nonneg _ _ hY0]
    refine min_le_min ?_ ?_
    · calc (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
            * hp2PrefixBound d (max (hp2PostCh4 j) 1.05)
            * (Real.exp β * (2 * (1 - Real.exp (-1)))
              * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))))
          ≤ (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
            * (hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) * g)
            * (Real.exp β * (2 * 0.632121) * W j) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) hY hY0 (by
              have : 0 ≤ hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) * g :=
                le_trans hB0 hB
              positivity)
        _ = _ := by ring
    · calc (r : ℝ) * (hp2PrefixBound d 1.05 / 1.05 ^ 2)
            * (Real.exp β * (2 * (1 - Real.exp (-1)))
              * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))))
          ≤ (r : ℝ) * (hp2SlabPrefHat 1.05 * g / 1.05 ^ 2)
            * (Real.exp β * (2 * 0.632121) * W j) :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hB' (by norm_num)) hr0) hY hY0 (by
              have : 0 ≤ hp2SlabPrefHat 1.05 * g := le_trans hB'0 hB'
              positivity)
        _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans (sum_min_le_min_sum.trans ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hAsl0 : 0 ≤ g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d)) := by
    positivity
  have hAt0 : 0 ≤ g * Real.exp β * (r : ℝ) := by positivity
  calc min (g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d))
          * ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
            * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05))
        (g * Real.exp β * (r : ℝ) * ∑ j ∈ Finset.range 40,
          (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2))
      ≤ min (g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d)) * Asl)
        (g * Real.exp β * (r : ℝ) * At) :=
        min_le_min (mul_le_mul_of_nonneg_left hAsl hAsl0) (mul_le_mul_of_nonneg_left hAt hAt0)
    _ = g * Real.exp β * min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d) * Asl)
        ((r : ℝ) * At) := by
        rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ g * Real.exp β)]
        congr 1 <;> ring

/-- `Asl ≥ 0` from its defining sum's bound. -/
lemma nonneg_of_sum_W_le {W : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    {f : ℕ → ℝ} (hf : ∀ j < 40, 0 ≤ f j) {A : ℝ}
    (hA : ∑ j ∈ Finset.range 40, W j * f j ≤ A) : 0 ≤ A := by
  refine le_trans (Finset.sum_nonneg fun j hj => ?_) hA
  have hj := Finset.mem_range.1 hj
  have hw0 : 0 ≤ hp2CellEnd j - hp2CellEnd (j + 1) :=
    sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j))
  exact mul_nonneg (le_trans (by positivity) (hW j hj)) (hf j hj)

/-- `hp2SlabPrefHat c ≥ 0` for `c ≥ 0`. -/
lemma hp2SlabPrefHat_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ hp2SlabPrefHat c := by
  have := hp2PrefixK_nonneg hc
  unfold hp2SlabPrefHat
  positivity

/-! #### Region IV: the deep pairs -/

/-- `e^{2 + 3.72·10⁻⁸ - 0.1005 + 5·10⁻²⁰} ≤ 6.682553`. -/
lemma exp_deep_le : Real.exp (2 + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20) ≤ 6.682553 := by
  interval_decide (trust := kernel)

end RMF
