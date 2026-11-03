/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.WindowBlockDataDecay
import RMF.UniformLower.HP1Certificate

/-!
# HP1's cell data: from cosine ranges to the window's block data

The generic half of HP1's per-cell numerics.  The window `halfWindow k` is split into the cells
`RMF.hp1Cell k i`, `h = e^{-k-ϑ}` with `ϑ ∈ [i/80, (i+1)/80]`, `i < 80`.  On a cell,
`ξ = log h + k ∈ [-(i+1)/80, -i/80]`, and the first blocks' cosine sums are, up to Mertens' error
`RMF.blockCosErr` and the damping (`RMF.abs_blockCosSum_sub_blockCos_le`), the normalised
integrals `c_m = blockCos ξ m` and `C_m = blockCos (log 2 + ξ) m`.

* **Interpolation** (`RMF.blockCos_zero_mem_of_grid`): brackets of `blockCos · 0` at two grid points
  bound it between them, by the 2-Lipschitz bound from either end or the tent's floor.
* **Past the grid** (`RMF.abs_blockCos_zero_le_decay`): `|blockCos x 0| ≤ 1.371e^{-x}` for
  `x ≥ 2.98`, from the asymptotic antiderivative with `|Φ(b)| ≤ e^{-b}(1 + e^{-2b}/2)`; on the cell
  `|c_m| ≤ 1.371Ee^{-m}` and `|C_m| ≤ 0.6855Ee^{-m}` for `E ≥ e^{ϑ₁}`.
* **Mertens** (`RMF.blockRpowSum_bounds_of_le`): `S_m ∈ [0.99999, 1.00001]` for `m + 11 ≤ r`.
* **One block's data** (`RMF.window_block_bounds`): ranges of `c_m`, `C_m`, `S_m` give ranges of
  `RMF.windowVarH`, `…VarR`, `…Cov`, `…MeanR` (the closed forms of
  `RMF/UniformLower/WindowBlockDataDecay.lean`) and the suffix's exit exponent.
* **The bundles**: `RMF.HP1StartRanges`, the hypotheses of the per-cell certificate on blocks
  `0, 1` (`RMF.hp1LowerBoundV2_of_lowerSum`), and `RMF.HP1WindowHyps`, the block-data hypotheses of
  `RMF.le_measure_windowEvent_rademacher_floor`; `RMF.HP1CellData` is both at a cell's numerals
  `RMF.HP1CellNumerals`.

A cell's data from its ranges is derived in `RMF/UniformLower/HP1Grid/DataFloor.lean` and
`RMF/UniformLower/HP1Grid/DataShort.lean`.
-/

open MeasureTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The cells of the window -/

/-- **Cell `i` of the window at `k`**: the heights `h = e^{-k-ϑ}` with `ϑ ∈ [i/80, (i+1)/80]`. -/
def hp1Cell (k i : ℕ) : Set ℝ :=
  Set.Icc (Real.exp (-((k : ℝ) + ((i : ℝ) + 1) / 80))) (Real.exp (-((k : ℝ) + (i : ℝ) / 80)))

/-- On cell `i`, `ξ = log h + k ∈ [-(i+1)/80, -i/80]`. -/
lemma log_add_mem_of_mem_hp1Cell {k i : ℕ} {h : ℝ} (hh : h ∈ hp1Cell k i) :
    0 < h ∧ -(((i : ℝ) + 1) / 80) ≤ Real.log h + k ∧ Real.log h + k ≤ -((i : ℝ) / 80) := by
  obtain ⟨h1, h2⟩ := hh
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) h1
  refine ⟨h0, ?_, ?_⟩
  · have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_log h0 h2
    rw [Real.log_exp] at this
    linarith

lemma hp1Cell_subset_halfWindow {k i : ℕ} (hi : i < 80) : hp1Cell k i ⊆ halfWindow k := by
  intro h hh
  obtain ⟨h1, h2⟩ := hh
  have hi' : (i : ℝ) + 1 ≤ 80 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) / 80 := by positivity
  have hi1 : ((i : ℝ) + 1) / 80 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hi'
  exact ⟨le_trans (Real.exp_le_exp.2 (by linarith)) h1,
    le_trans h2 (Real.exp_le_exp.2 (by linarith))⟩

/-! ### Interpolation between grid points -/

/-- **Interpolation between two grid points.**  Brackets of `blockCos · 0` at `c₁` and `c₂` bound
it on `[x₁, x₂] ⊆ [c₁, c₂]`, by the 2-Lipschitz bound (`RMF.abs_blockCos_sub_le`) from `c₁`, from
`c₂`, or from both at once (`(lo₁ + lo₂)/2 - (c₂ - c₁)`, the floor of the tent). -/
theorem blockCos_zero_mem_of_grid {c₁ c₂ x₁ x₂ lo₁ hi₁ lo₂ hi₂ L U : ℝ}
    (h₁ : lo₁ ≤ blockCos c₁ 0 ∧ blockCos c₁ 0 ≤ hi₁)
    (h₂ : lo₂ ≤ blockCos c₂ 0 ∧ blockCos c₂ 0 ≤ hi₂) (hx₁ : c₁ ≤ x₁) (hx₂ : x₂ ≤ c₂)
    (hL : L ≤ lo₁ - 2 * (x₂ - c₁) ∨ L ≤ lo₂ - 2 * (c₂ - x₁) ∨ L ≤ (lo₁ + lo₂) / 2 - (c₂ - c₁))
    (hU : hi₁ + 2 * (x₂ - c₁) ≤ U ∨ hi₂ + 2 * (c₂ - x₁) ≤ U ∨ (hi₁ + hi₂) / 2 + (c₂ - c₁) ≤ U)
    {ξ : ℝ} (hξ₁ : x₁ ≤ ξ) (hξ₂ : ξ ≤ x₂) : L ≤ blockCos ξ 0 ∧ blockCos ξ 0 ≤ U := by
  have e₁ := abs_le.1 (abs_blockCos_sub_le c₁ ξ 0)
  have e₂ := abs_le.1 (abs_blockCos_sub_le c₂ ξ 0)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ξ - c₁)] at e₁
  rw [abs_of_nonpos (by linarith : ξ - c₂ ≤ 0)] at e₂
  constructor
  · rcases hL with hL | hL | hL <;> linarith [h₁.1, h₂.1, e₁.1, e₂.1]
  · rcases hU with hU | hU | hU <;> linarith [h₁.2, h₂.2, e₁.2, e₂.2]

/-! ### Past the grid: the decay of `blockCos` -/

/-- `|Φ(b)| ≤ e^{-b}(1 + e^{-2b}/2)` for `b ≥ 2`, `Φ = RMF.cosExpTail`: its two terms are
`(sin, cos)(e^b)` against `(e^{-b} - 2e^{-3b}, e^{-2b} - 6e^{-4b})`, a vector of length at most
`√(e^{-2b} + e^{-4b})`. -/
lemma abs_cosExpTail_le_sharp {b : ℝ} (hb : 2 ≤ b) :
    |cosExpTail b| ≤ Real.exp (-b) * (1 + Real.exp (-(2 * b)) / 2) := by
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.exp (-b) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.exp_pos _
  have ht1 : t ≤ 1 / 3 := by
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h2 : Real.exp (-b) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    rw [htdef]
    refine h2.trans ?_
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 2) (by norm_num)]
    linarith
  have hk : ∀ k : ℕ, Real.exp (-((k : ℝ) * b)) = t ^ k := by
    intro k
    rw [htdef, ← Real.exp_nat_mul]
    ring_nf
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  push_cast at h2 h3 h4
  rw [cosExpTail, ← htdef, h2, h3, h4]
  have hsc := Real.sin_sq_add_cos_sq (Real.exp b)
  set s := Real.sin (Real.exp b)
  set c := Real.cos (Real.exp b)
  have hX0 : 0 ≤ t - 2 * t ^ 3 := by nlinarith
  have hXt : t - 2 * t ^ 3 ≤ t := by nlinarith
  have hY0 : 0 ≤ t ^ 2 - 6 * t ^ 4 := by nlinarith
  have hYt : t ^ 2 - 6 * t ^ 4 ≤ t ^ 2 := by nlinarith
  have hX2 : (t - 2 * t ^ 3) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hX0 hXt 2
  have hY2 : (t ^ 2 - 6 * t ^ 4) ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ hY0 hYt 2
  have key : (s * (t - 2 * t ^ 3) - c * (t ^ 2 - 6 * t ^ 4)) ^ 2
      + (s * (t ^ 2 - 6 * t ^ 4) + c * (t - 2 * t ^ 3)) ^ 2
      = (s ^ 2 + c ^ 2) * ((t - 2 * t ^ 3) ^ 2 + (t ^ 2 - 6 * t ^ 4) ^ 2) := by ring
  rw [hsc, one_mul] at key
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  nlinarith [sq_nonneg (s * (t ^ 2 - 6 * t ^ 4) + c * (t - 2 * t ^ 3)), pow_pos ht0 6]

/-- **`blockCos` past `e³`**: `|blockCos x 0| ≤ 1.371e^{-x}` for `x ≥ 2.98`, from the asymptotic
antiderivative (`RMF.abs_integral_cos_exp_sub_cosExpTail_le`) and `RMF.abs_cosExpTail_le_sharp`;
the constant is `1 + e^{-1}` up to `0.003`. -/
theorem abs_blockCos_zero_le_decay {x : ℝ} (hx : 2.98 ≤ x) :
    |blockCos x 0| ≤ 1.371 * Real.exp (-x) := by
  have h := abs_integral_cos_exp_sub_cosExpTail_le (a := x) (b := x + 1) (by linarith)
  rw [← blockCos_zero_eq] at h
  have h1 := abs_cosExpTail_le_sharp (b := x + 1) (by linarith)
  have h0 := abs_cosExpTail_le_sharp (b := x) (by linarith)
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.exp (-x) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.exp_pos _
  have ht : t ≤ 0.0508 := by
    have h298 : Real.exp (-2.98) ≤ 0.0508 := by interval_decide (trust := kernel)
    rw [htdef]
    exact (Real.exp_le_exp.2 (by linarith)).trans h298
  have hsq : Real.exp (-(2 * x)) = t ^ 2 := by
    rw [htdef, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hq : Real.exp (-(4 * x)) = t ^ 4 := by
    rw [htdef, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hx1 : Real.exp (-(x + 1)) = Real.exp (-1) * t := by
    rw [htdef, ← Real.exp_add]
    ring_nf
  have hx2 : Real.exp (-(2 * (x + 1))) ≤ t ^ 2 := by
    rw [← hsq]
    exact Real.exp_le_exp.2 (by linarith)
  have he1 : Real.exp (-1) ≤ 0.36788 := by linarith [Real.exp_neg_one_lt_d9]
  have he0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  rw [hx1] at h1
  rw [← htdef, hsq] at h0
  rw [hq] at h
  have hΦ1 : |cosExpTail (x + 1)| ≤ 0.36788 * t * (1 + t ^ 2 / 2) := by
    refine h1.trans ?_
    have hm1 : 1 + Real.exp (-(2 * (x + 1))) / 2 ≤ 1 + t ^ 2 / 2 := by linarith
    have hm2 : Real.exp (-1) * t ≤ 0.36788 * t := mul_le_mul_of_nonneg_right he1 ht0.le
    calc Real.exp (-1) * t * (1 + Real.exp (-(2 * (x + 1))) / 2)
        ≤ Real.exp (-1) * t * (1 + t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hm1 (mul_nonneg he0 ht0.le)
      _ ≤ 0.36788 * t * (1 + t ^ 2 / 2) := mul_le_mul_of_nonneg_right hm2 (by positivity)
  have ht2 : t ^ 2 ≤ 0.0508 * t := by nlinarith
  have ht3 : t ^ 3 ≤ 0.0508 ^ 2 * t := by nlinarith
  have ht4 : t ^ 4 ≤ 0.0508 ^ 3 * t := by nlinarith
  rw [abs_le] at h hΦ1 h0 ⊢
  rw [← htdef]
  constructor <;> nlinarith [h.1, h.2, hΦ1.1, hΦ1.2, h0.1, h0.2]

/-- **The first blocks past the grid, on a cell**: `|blockCos ξ m| ≤ 1.371Ee^{-m}` for
`ξ ≥ -ϑ₁`, `e^{ϑ₁} ≤ E` and `m - ϑ₁ ≥ 2.98`. -/
lemma abs_blockCos_le_of_cell {ξ ϑ₁ E : ℝ} {m : ℕ} (hξ : -ϑ₁ ≤ ξ) (hE : Real.exp ϑ₁ ≤ E)
    (hm : 2.98 ≤ (m : ℝ) - ϑ₁) : |blockCos ξ m| ≤ 1.371 * E * Real.exp (-(m : ℝ)) := by
  rw [blockCos_eq_zero]
  refine (abs_blockCos_zero_le_decay (by linarith)).trans ?_
  have h1 : Real.exp (-((m : ℝ) + ξ)) ≤ Real.exp (-(m : ℝ)) * Real.exp ϑ₁ := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-(m : ℝ)) * Real.exp ϑ₁ ≤ Real.exp (-(m : ℝ)) * E :=
    mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
  linarith

/-- **…at the doubled frequency**: `|blockCos (log 2 + ξ) m| ≤ 0.6855Ee^{-m}` for
`m + 0.6931 - ϑ₁ ≥ 2.98` (`e^{-log 2} = 1/2`). -/
lemma abs_blockCos_log_two_le_of_cell {ξ ϑ₁ E : ℝ} {m : ℕ} (hξ : -ϑ₁ ≤ ξ)
    (hE : Real.exp ϑ₁ ≤ E) (hm : 2.98 ≤ (m : ℝ) + 0.6931 - ϑ₁) :
    |blockCos (Real.log 2 + ξ) m| ≤ 0.6855 * E * Real.exp (-(m : ℝ)) := by
  have hl := Real.log_two_gt_d9
  rw [blockCos_eq_zero]
  refine (abs_blockCos_zero_le_decay (by linarith)).trans ?_
  have h1 : Real.exp (-((m : ℝ) + (Real.log 2 + ξ)))
      = Real.exp (-(m : ℝ)) * Real.exp (-ξ) / 2 := by
    rw [show -((m : ℝ) + (Real.log 2 + ξ)) = -(m : ℝ) + -ξ - Real.log 2 by ring, Real.exp_sub,
      Real.exp_add, Real.exp_log two_pos]
  have h2 : Real.exp (-ξ) ≤ E := (Real.exp_le_exp.2 (by linarith)).trans hE
  have h3 : Real.exp (-(m : ℝ)) * Real.exp (-ξ) ≤ Real.exp (-(m : ℝ)) * E :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  rw [h1]
  linarith

/-! ### The Mertens sums -/

/-- `e^{-10} ≤ 1/20000`. -/
lemma exp_neg_ten_le : Real.exp (-10) ≤ 1 / 20000 := by
  have h : (20000 : ℝ) ≤ Real.exp 10 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 10) (N := 20000) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h

/-- **The block's Mertens sum away from the top**: `S_m ∈ [0.99999, 1.00001]` for `m + 11 ≤ r`
when `σe^{k+r} ≤ 1/200` (then `σe^{k+m+1} ≤ 10⁻⁶`; `RMF.sum_norm_sq_primeBlockSub_bounds_sharp`). -/
lemma blockRpowSum_bounds_of_le {k m r : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hm : m + 11 ≤ r) :
    0.99999 ≤ blockRpowSum k σ m ∧ blockRpowSum k σ m ≤ 1.00001 := by
  have hk' : (16 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hmr : (m : ℝ) + 11 ≤ r := by exact_mod_cast hm
  have hsplit : Real.exp ((k : ℝ) + m + 1)
      = Real.exp ((k : ℝ) + r) * Real.exp ((m : ℝ) + 1 - r) := by
    rw [← Real.exp_add]
    ring_nf
  have he10 : Real.exp ((m : ℝ) + 1 - r) ≤ 1 / 20000 :=
    (Real.exp_le_exp.2 (by linarith)).trans exp_neg_ten_le
  have hη : |σ| * Real.log (blockScale k (m + 1)) ≤ 1 / 10 ^ 6 := by
    rw [abs_of_nonneg hσ, log_blockScale]
    push_cast
    rw [show (m : ℝ) + 1 + k = (k : ℝ) + m + 1 by ring, hsplit]
    calc σ * (Real.exp ((k : ℝ) + r) * Real.exp ((m : ℝ) + 1 - r))
        = σ * Real.exp ((k : ℝ) + r) * Real.exp ((m : ℝ) + 1 - r) := by ring
      _ ≤ 1 / 200 * (1 / 20000) :=
          mul_le_mul hσr he10 (Real.exp_pos _).le (by norm_num)
      _ ≤ 1 / 10 ^ 6 := by norm_num
  have hS : blockRpowSum k σ m
      = ∑ p ∈ primeBlockSub k m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => (norm_sq_prime_cpow_neg p (re_shiftLine σ 0)).symm
  obtain ⟨hlo, hhi⟩ := sum_norm_sq_primeBlockSub_bounds_sharp
    (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) hk' hσ hη
    fun p _ => norm_sq_prime_cpow_neg p (re_shiftLine σ 0)
  rw [← hS] at hlo hhi
  have he : 1 - 2 * (1 / 10 ^ 6) ≤ Real.exp (-(2 * (1 / 10 ^ 6 : ℝ))) := by
    linarith [Real.add_one_le_exp (-(2 * (1 / 10 ^ 6 : ℝ)))]
  constructor
  · nlinarith
  · linarith

/-- `S_m ∈ [0.99, 1.00001]` on every block below the top `r` (`RMF.blockRpowSum_bounds`,
`RMF.blockRpowSum_le`). -/
lemma blockRpowSum_bounds_of_lt {k m r : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hm : m < r) :
    0.99 ≤ blockRpowSum k σ m ∧ blockRpowSum k σ m ≤ 1.00001 := by
  have hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hσ) hσr
    have : (m : ℝ) + 1 ≤ r := by exact_mod_cast hm
    linarith
  have hk' : (16 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact ⟨(blockRpowSum_bounds hk hσ hσm).1, (blockRpowSum_le hσ hk').trans (by norm_num)⟩

/-! ### One block's data -/

/-- The exit exponent's algebra: `td + t²V/2 ≤ 2t·ch + (t² - t)Sl/2 + 2e` for `0 ≤ t ≤ 1`, from
`d ≤ 2c - S/2 + e`, `V ≤ S + e`, `c ≤ ch`, `Sl ≤ S`. -/
lemma exit_exponent_le {t d V c S e ch Sl : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (he : 0 ≤ e)
    (hd : d ≤ 2 * c - S / 2 + e) (hV : V ≤ S + e) (hc : c ≤ ch) (hS : Sl ≤ S) :
    t * d + t ^ 2 * V / 2 ≤ 2 * t * ch + (t ^ 2 - t) * Sl / 2 + 2 * e := by
  have h1 := mul_le_mul_of_nonneg_left hd ht0
  have h2 := mul_le_mul_of_nonneg_left hV (sq_nonneg t)
  have h3 := mul_le_mul_of_nonneg_left hc ht0
  have h4 : (t ^ 2 - t) * S ≤ (t ^ 2 - t) * Sl := mul_le_mul_of_nonpos_left hS (by nlinarith)
  have h5 : t * e ≤ e := mul_le_of_le_one_left he ht1
  have h6 : t ^ 2 * e ≤ e := mul_le_of_le_one_left he (by nlinarith)
  nlinarith

/-- **The window's block data from its sums**, block `m` at offset `k ≥ 20`: ranges of `c_m`,
`C_m` and `S_m` give ranges of the height and real variances, the covariance and the real mean
(the closed forms of `RMF/UniformLower/WindowBlockDataDecay.lean`, within `e ≥ e^{-m}/10²⁰`), and
the exit exponent `td + t²V²/2 ≤ 2t·ch + (t² - t)Sl/2 + 2e` for `0 ≤ t ≤ 1`. -/
theorem window_block_bounds (hX : IsRademacherPrimeValues X μ) {y k m : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hB : primeBlockSub k m ⊆ primesBelowSub y)
    {cl ch Cl Ch Sl Sh e : ℝ} (he : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ e)
    (hc : cl ≤ blockCosSum k σ h m ∧ blockCosSum k σ h m ≤ ch)
    (hC : Cl ≤ blockCosSum k σ (2 * h) m ∧ blockCosSum k σ (2 * h) m ≤ Ch)
    (hS : Sl ≤ blockRpowSum k σ m ∧ blockRpowSum k σ m ≤ Sh) :
    ((Sl + Cl) / 2 - e ≤ windowVarH X μ y k σ h m
      ∧ windowVarH X μ y k σ h m ≤ (Sh + Ch) / 2 + e)
    ∧ (Sl - e ≤ windowVarR X μ y k σ h m ∧ windowVarR X μ y k σ h m ≤ Sh + e)
    ∧ (cl - e ≤ windowCov X μ y k σ h m ∧ windowCov X μ y k σ h m ≤ ch + e)
    ∧ (2 * cl - Sh / 2 - e ≤ windowMeanR X μ y k σ h m
      ∧ windowMeanR X μ y k σ h m ≤ 2 * ch - Sl / 2 + e)
    ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * windowMeanR X μ y k σ h m + t ^ 2 * windowVarR X μ y k σ h m / 2
        ≤ 2 * t * ch + (t ^ 2 - t) * Sl / 2 + 2 * e := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmk : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have he0 : 0 ≤ e := le_trans (by positivity) he
  have h1 := abs_le.1
    ((abs_blockMatchedVarAdd_height_sub_le_decay hX y (h := h) hσ hk0 hmk hB).trans he)
  have h2 := abs_le.1
    ((abs_blockMatchedVarAdd_real_sub_le_decay hX y (h := h) hσ hk0 hmk hB).trans he)
  have h3 := abs_le.1
    ((abs_blockMatchedCovAddT_sub_le_decay hX y (h := h) hσ hk0 hmk hB).trans he)
  have h4 := abs_le.1
    ((abs_blockMeanAdd_real_sub_le_decay hX y (h := h) hσ hk0 hmk hB).trans he)
  simp only [windowVarH, windowVarR, windowCov, windowMeanR]
  refine ⟨⟨by linarith [hC.1, hS.1], by linarith [hC.2, hS.2]⟩,
    ⟨by linarith [hS.1], by linarith [hS.2]⟩, ⟨by linarith [hc.1], by linarith [hc.2]⟩,
    ⟨by linarith [hc.1, hS.2], by linarith [hc.2, hS.1]⟩, fun t ht0 ht1 => ?_⟩
  exact exit_exponent_le ht0 ht1 he0 (by linarith) (by linarith) hc.2 hS.1

/-! ### The slope and the residual variance -/

lemma pairSlope_mul_self {V c : ℝ} (hV : V ≠ 0) : pairSlope V c * V = c := by
  rw [pairSlope]
  field_simp

/-- `β²V + R = W`: the slope's variance and the residual one add up to the real variance. -/
lemma pairSlope_sq_mul_add_pairResidVar {V W c : ℝ} (hV : V ≠ 0) :
    pairSlope V c ^ 2 * V + pairResidVar V W c = W := by
  rw [pairSlope, pairResidVar]
  field_simp
  ring

/-- `max(β, 0)²V + R ≤ W` for `V > 0`. -/
lemma max_pairSlope_sq_mul_add_le {V W c : ℝ} (hV : 0 < V) :
    max (pairSlope V c) 0 ^ 2 * V + pairResidVar V W c ≤ W := by
  have h := pairSlope_sq_mul_add_pairResidVar (W := W) (c := c) hV.ne'
  rcases le_total 0 (pairSlope V c) with hb | hb
  · rw [max_eq_left hb]
    exact h.le
  · rw [max_eq_right hb, sq, zero_mul, zero_mul, zero_add]
    have : 0 ≤ pairSlope V c ^ 2 * V := mul_nonneg (sq_nonneg _) hV.le
    linarith

/-- `R ≤ W` for `V > 0`. -/
lemma pairResidVar_le {V W c : ℝ} (hV : 0 < V) : pairResidVar V W c ≤ W := by
  rw [pairResidVar]
  have : 0 ≤ c ^ 2 / V := div_nonneg (sq_nonneg c) hV.le
  linarith

/-- `min(β, 0)²V ≤ n²/v` for `0 < v ≤ V`, `0 ≤ n` and `-c ≤ n`. -/
lemma min_pairSlope_sq_mul_le {V c v n : ℝ} (hv : 0 < v) (hvV : v ≤ V) (hn0 : 0 ≤ n)
    (hn : -c ≤ n) : min (pairSlope V c) 0 ^ 2 * V ≤ n ^ 2 / v := by
  have hV : 0 < V := lt_of_lt_of_le hv hvV
  rcases le_total 0 c with hc | hc
  · have hb : 0 ≤ pairSlope V c := div_nonneg hc hV.le
    rw [min_eq_right hb, sq, zero_mul, zero_mul]
    positivity
  · have hb : pairSlope V c ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hV.le
    rw [min_eq_left hb, pairSlope]
    have e : (c / V) ^ 2 * V = c ^ 2 / V := by field_simp
    rw [e]
    have hc2 : c ^ 2 ≤ n ^ 2 := by nlinarith
    calc c ^ 2 / V ≤ n ^ 2 / V := div_le_div_of_nonneg_right hc2 hV.le
      _ ≤ n ^ 2 / v := div_le_div_of_nonneg_left (sq_nonneg n) hv hvV

/-- `|β| ≤ b/v` for `0 < v ≤ V` and `|c| ≤ b`. -/
lemma abs_pairSlope_le {V c v b : ℝ} (hv : 0 < v) (hvV : v ≤ V) (hc : |c| ≤ b) :
    |pairSlope V c| ≤ b / v := by
  have hV : 0 < V := lt_of_lt_of_le hv hvV
  rw [pairSlope, abs_div, abs_of_pos hV]
  calc |c| / V ≤ b / V := div_le_div_of_nonneg_right hc hV.le
    _ ≤ b / v := div_le_div_of_nonneg_left ((abs_nonneg c).trans hc) hv hvV

/-! ### The blocks on a cell: the first ones, past the grid, far out -/

/-- `e^{-69} ≤ 10⁻²⁸`. -/
lemma exp_neg_sixty_nine_le : Real.exp (-69) ≤ 1 / 10 ^ 28 := by
  have h : (10 : ℝ) ^ 28 ≤ Real.exp 69 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 69) (N := 10 ^ 28) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) h

/-- `e^{-39} ≤ 1.2·10⁻¹⁷`. -/
lemma exp_neg_thirty_nine_le : Real.exp (-39) ≤ 1.2 / 10 ^ 17 := by
  interval_decide (trust := kernel)

/-! ### The bundles -/

/-- **HP1's start data in ranges**: the hypotheses of the per-cell certificate
(`RMF.hp1LowerBoundV2_of_lowerSum`) on the data of blocks `0, 1` — height variances `v₀ v₁`,
residual variances `s₀ s₁`, slopes `β₀ β₁`, real means `d₀ d₁`: `v₀, v₁`, `κ = β₀v₀ + β₁v₁`,
`S = β₀²v₀ + s₀ + (β₁²v₁ + s₁)`, `σ₁² = β₀²v₀ + s₀` and `d₀ + d₁` in ranges, `|d₀| ≤ d0`. -/
def HP1StartRanges (v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ v0l v0h v1l v1h kl kh Sl Sh σl σh d0 Dl Dh : ℝ) :
    Prop :=
  v₀ ∈ Set.Icc v0l v0h ∧ v₁ ∈ Set.Icc v1l v1h ∧ β₀ * v₀ + β₁ * v₁ ∈ Set.Icc kl kh
    ∧ β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁) ∈ Set.Icc Sl Sh ∧ β₀ ^ 2 * v₀ + s₀ ∈ Set.Icc σl σh
    ∧ |d₀| ≤ d0 ∧ d₀ + d₁ ∈ Set.Icc Dl Dh

/-- **HP1's window hypotheses**: the block-data hypotheses of
`RMF.le_measure_windowEvent_rademacher_floor` (blocks `m < r` of the window at offset `k`, height
`h`, cutoff `y`), verbatim: `hvb`, `hΛ`, `hBW`, `hσR`, `hKlate`, `hKR`, `hM₁`, `hK₂`. -/
def HP1WindowHyps (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k r m₀ : ℕ)
    (σ h vmin vmax a A B t Λ BW σR2 Klate KR M₁ K₂ : ℝ) : Prop :=
  (∀ m, 2 ≤ m → m < r →
      vmin ≤ windowVarH X μ y k σ h m ∧ windowVarH X μ y k σ h m ≤ vmax)
  ∧ ∑ m ∈ Finset.Ico 2 r,
      max 0 (t * windowMeanR X μ y k σ h m + t ^ 2 * (max (windowSlope X μ y k σ h m) 0 ^ 2
        * windowVarH X μ y k σ h m + windowResid X μ y k σ h m) / 2) ≤ Λ
  ∧ (∀ m, 2 ≤ m → m < r →
      windowResid X μ y k σ h m / 2 - windowMeanR X μ y k σ h m ≤ BW)
  ∧ ∑ m ∈ Finset.Ico 2 (m₀ + 2),
      min (windowSlope X μ y k σ h m) 0 ^ 2 * windowVarH X μ y k σ h m ≤ σR2
  ∧ ∑ m ∈ Finset.Ico (m₀ + 2) r,
      |min (windowSlope X μ y k σ h m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate
  ∧ ∑ m ∈ Finset.Ico 2 r,
      |windowSlope X μ y k σ h m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR
  ∧ |windowMeanR X μ y k σ h 0| ≤ M₁
  ∧ 0 ≤ K₂ + windowMeanR X μ y k σ h 0 + windowMeanR X μ y k σ h 1

/-- **HP1's numerals on one cell**: the start ranges of the per-cell certificate (`v₀, v₁, κ, |d₀|,
d₀ + d₁`; `S` and `σ₁²` are the same on every cell), the suffix parameters of
`RMF.le_measure_windowEvent_rademacher_floor` and the proof parameter `L ≥ K_late`. -/
structure HP1CellNumerals where
  v0l : ℝ
  v0h : ℝ
  v1l : ℝ
  v1h : ℝ
  kl : ℝ
  kh : ℝ
  d0 : ℝ
  Dl : ℝ
  Dh : ℝ
  vmin : ℝ
  vmax : ℝ
  t : ℝ
  Λ : ℝ
  BW : ℝ
  σR2 : ℝ
  Klate : ℝ
  KR : ℝ
  L : ℝ

/-- **HP1's data on a cell** at height `h`, at the numerals `P` and the event's parameters
`a = 3/2`, `A = 5/2`, `B = 3`, `M₁ = 7`, `K₂ = 10`, `m₀ = 8`: the start ranges
(`S ∈ [1.99997, 2.00003]`, `σ₁² ∈ [0.99998, 1.00002]`) and the window hypotheses. -/
def HP1CellData (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k r : ℕ) (σ h : ℝ) (P : HP1CellNumerals) :
    Prop :=
  HP1StartRanges (windowVarH X μ y k σ h 0) (windowVarH X μ y k σ h 1)
      (windowResid X μ y k σ h 0) (windowResid X μ y k σ h 1)
      (windowSlope X μ y k σ h 0) (windowSlope X μ y k σ h 1)
      (windowMeanR X μ y k σ h 0) (windowMeanR X μ y k σ h 1)
      P.v0l P.v0h P.v1l P.v1h P.kl P.kh 1.99997 2.00003 0.99998 1.00002 P.d0 P.Dl P.Dh
    ∧ HP1WindowHyps X μ y k r 8 σ h P.vmin P.vmax (3 / 2) (5 / 2) 3 P.t P.Λ P.BW P.σR2 P.Klate
      P.KR 7 10

/-! ### The window hypotheses from the first blocks' ranges -/

lemma sum_Ico_two_six (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Ico 2 6, f m = f 2 + f 3 + f 4 + f 5 := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp [Finset.sum_range_succ]

lemma sum_Ico_two_ten (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Ico 2 10, f m = f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp [Finset.sum_range_succ]

/-- `|min(x, 0)| ≤ |x|`. -/
lemma abs_min_zero_le (x : ℝ) : |min x 0| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [min_eq_right hx, abs_zero]
    exact abs_nonneg x
  · rw [min_eq_left hx]

/-- The sum of `hΛ` from its terms: at most `l₂ + l₃ + l₄ + l₅` when the terms from block `6` on
are nonpositive. -/
lemma sum_Ico_two_le_of_terms {F : ℕ → ℝ} {r : ℕ} {Λ l₂ l₃ l₄ l₅ : ℝ} (hr : 6 ≤ r)
    (h2 : F 2 ≤ l₂) (h3 : F 3 ≤ l₃) (h4 : F 4 ≤ l₄) (h5 : F 5 ≤ l₅)
    (h6 : ∀ m, 6 ≤ m → m < r → F m ≤ 0) (hΛ : l₂ + l₃ + l₄ + l₅ ≤ Λ) :
    ∑ m ∈ Finset.Ico 2 r, F m ≤ Λ := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 2 ≤ 6) hr, sum_Ico_two_six]
  have : ∑ m ∈ Finset.Ico 6 r, F m ≤ 0 :=
    Finset.sum_nonpos fun m hm => h6 m (Finset.mem_Ico.1 hm).1 (Finset.mem_Ico.1 hm).2
  linarith

/-- `∑_{2 ≤ m < r} f m = f 2 + f 3 + ∑_{4 ≤ m < r} f m`. -/
lemma sum_Ico_two_eq {f : ℕ → ℝ} {r : ℕ} (hr : 4 ≤ r) :
    ∑ m ∈ Finset.Ico 2 r, f m = f 2 + f 3 + ∑ m ∈ Finset.Ico 4 r, f m := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 2 ≤ 4) hr, Finset.sum_Ico_eq_sum_range]
  simp [Finset.sum_range_succ]

/-- The explicit exponentials of the suffix sums. -/
lemma hp1_exp_bounds :
    Real.exp (-4) ≤ 0.018316 ∧ Real.exp (-5) ≤ 0.0067381 ∧ Real.exp (-6) ≤ 0.002479
      ∧ Real.exp (-10) ≤ 0.00004541 ∧ Real.exp (-40) ≤ 1 / 10 ^ 17
      ∧ Real.exp (-2) ≤ 0.13534 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> interval_decide (trust := kernel)

/-- `e^{-m} ≤ b` from `e^{-n} ≤ b` for `n ≤ m`. -/
lemma exp_neg_natCast_le_of_le {m n : ℕ} {b : ℝ} (hnm : n ≤ m) (hb : Real.exp (-(n : ℝ)) ≤ b) :
    Real.exp (-(m : ℝ)) ≤ b :=
  (Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast hnm))).trans hb

/-- `(e^{-m})² ≤ q^m` from `e^{-2} ≤ q`. -/
lemma exp_neg_natCast_sq_le {m : ℕ} {q : ℝ} (hq : Real.exp (-2) ≤ q) :
    Real.exp (-(m : ℝ)) ^ 2 ≤ q ^ m := by
  have e : Real.exp (-(m : ℝ)) ^ 2 = Real.exp (-2) ^ m := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hq m

end RMF
