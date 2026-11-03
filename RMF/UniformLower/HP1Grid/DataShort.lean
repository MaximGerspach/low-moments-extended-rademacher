/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Grid.DataFloor

/-!
# HP1's cell data on short tubes

The twins of `RMF/UniformLower/HP1Grid/DataFloor.lean`'s discharge of HP1's cell data (window
scale `k ≥ 20`) on tubes of `r ≥ 35` blocks, where the floor's lemmas need `r ≥ 110`.

* **The damping from `m + 20 ≤ r`**: `2σe^{k+m+1} ≤ e^{-19}/100 ≤ 10⁻¹⁰`, in place of the floor's
  `10⁻³⁰` from `m + 70 ≤ r` (`RMF.blockCosSum_mem_of_cell_short`).  The block error
  `ε ≥ 1.12·10⁻⁷` still covers it, the real mean's `2(5.57·10⁻⁸ + 10⁻¹⁰) = 1.116·10⁻⁷` dominating
  (`RMF.window_block_bounds_of_cos_short`, blocks `0 … 3`).
* **Blocks `4 ≤ m ≤ 15`** by the cell's decay (`RMF.window_block_bounds_mid_short`): the
  covariance within the flat `1.94·10⁻⁸ ≥ 1.925·10⁻⁸ + 10⁻¹⁰` of its decaying main term (the
  floor's `1.93·10⁻⁸` does not cover the damping), so `σ_R²`'s coefficient is `1.371E + 1.58·10⁻⁴`.
* **Blocks `m ≥ 16` at any damping** (`RMF.window_block_bounds_tail_floor`):
  `RMF.window_block_bounds_far_floor` from block `16`, with `3e^{1-m} ≤ 9.2·10⁻⁷` for `10⁻¹⁶`.
* **The sums**, split at block `16`, for any `r` (`RMF.sum_decay_flat_mul_weight_le_short`): the
  tail's `8.155e^{-16}(1.59(K + 32B) + 3.43B)` in place of the floor's `e^{-40}` term.
* **The bundles** for `r ≥ 35` (`RMF.hp1StartRanges_of_cos_short`,
  `RMF.hp1WindowHyps_of_cos_short`): the floor's side conditions, with the exit exponent's sign
  from block `16`, `2t·9.2·10⁻⁷ + (t² - t)·0.99/2 + ε ≤ 0`, and `σ_R²`, `K_late`, `K_R` as above.
-/

open MeasureTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### One block's data on short tubes -/

/-- `e^{-19} ≤ 10⁻⁸`. -/
lemma exp_neg_nineteen_le : Real.exp (-19) ≤ 1 / 10 ^ 8 := by
  interval_decide (trust := kernel)

/-- **A first block's cosine sums from `blockCos`, on short tubes** (`m + 20 ≤ r`, so the damping
costs `2σe^{k+m+1} ≤ e^{-19}/100 ≤ 10⁻¹⁰`): ranges of `blockCos (log h + k) m` and
`blockCos (log 2 + (log h + k)) m` give `c_m` and `C_m` within `blockCosErr k m h + 10⁻¹⁰` and
`blockCosErr k m (2h) + 10⁻¹⁰` (`RMF.blockCosSum_mem_of_cell_floor` with `m + 70 → m + 20`). -/
lemma blockCosSum_mem_of_cell_short {k m r : ℕ} {σ h lo hi Lo Hi : ℝ}
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hm : m + 20 ≤ r)
    (hc : lo ≤ blockCos (Real.log h + k) m ∧ blockCos (Real.log h + k) m ≤ hi)
    (hC : Lo ≤ blockCos (Real.log 2 + (Real.log h + k)) m
      ∧ blockCos (Real.log 2 + (Real.log h + k)) m ≤ Hi) :
    (lo - (blockCosErr k m h + 1 / 10 ^ 10) ≤ blockCosSum k σ h m
      ∧ blockCosSum k σ h m ≤ hi + (blockCosErr k m h + 1 / 10 ^ 10))
    ∧ (Lo - (blockCosErr k m (2 * h) + 1 / 10 ^ 10) ≤ blockCosSum k σ (2 * h) m
      ∧ blockCosSum k σ (2 * h) m ≤ Hi + (blockCosErr k m (2 * h) + 1 / 10 ^ 10)) := by
  obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
  have hmr : (m : ℝ) + 20 ≤ r := by exact_mod_cast hm
  have hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 10 ^ 10 := by
    have hsplit : Real.exp ((k : ℝ) + m + 1)
        = Real.exp ((k : ℝ) + r) * Real.exp ((m : ℝ) + 1 - r) := by
      rw [← Real.exp_add]
      ring_nf
    have he : Real.exp ((m : ℝ) + 1 - r) ≤ 1 / 10 ^ 8 :=
      (Real.exp_le_exp.2 (by linarith)).trans exp_neg_nineteen_le
    rw [hsplit]
    calc 2 * σ * (Real.exp ((k : ℝ) + r) * Real.exp ((m : ℝ) + 1 - r))
        = 2 * (σ * Real.exp ((k : ℝ) + r)) * Real.exp ((m : ℝ) + 1 - r) := by ring
      _ ≤ 2 * (1 / 200) * (1 / 10 ^ 8) := by
          gcongr
      _ = 1 / 10 ^ 10 := by norm_num
  refine ⟨blockCosSum_mem_of_blockCos hσ h0 hδ hc, ?_⟩
  rw [← log_two_mul_add_eq h0 k] at hC
  exact blockCosSum_mem_of_blockCos hσ (by linarith) hδ hC

/-- **A first block's data on the cell, on short tubes** (`k ≥ 20`, `m + 20 ≤ r`): ranges of
`c_m = blockCos(ξ, m)` and `C_m = blockCos(log 2 + ξ, m)` at `ξ = log h + k` give the block data
within `ε ≥ 1.12·10⁻⁷` — `RMF.window_block_bounds_of_cos_floor` with the damping `10⁻¹⁰`
(`RMF.blockCosSum_mem_of_cell_short`; the real mean's `2(5.57·10⁻⁸ + 10⁻¹⁰) + 10⁻²⁰` fits). -/
theorem window_block_bounds_of_cos_short (hX : IsRademacherPrimeValues X μ) {k r y m : ℕ}
    {σ h ε : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hB : primeBlockSub k m ⊆ primesBelowSub y)
    (hm : m + 20 ≤ r) (hε : 1.12 / 10 ^ 7 ≤ ε) {cl ch Cl Ch : ℝ}
    (hc : cl ≤ blockCos (Real.log h + k) m ∧ blockCos (Real.log h + k) m ≤ ch)
    (hC : Cl ≤ blockCos (Real.log 2 + (Real.log h + k)) m
      ∧ blockCos (Real.log 2 + (Real.log h + k)) m ≤ Ch) :
    ((0.99999 + Cl) / 2 - ε ≤ windowVarH X μ y k σ h m
      ∧ windowVarH X μ y k σ h m ≤ (1.00001 + Ch) / 2 + ε)
    ∧ (0.99999 - ε ≤ windowVarR X μ y k σ h m ∧ windowVarR X μ y k σ h m ≤ 1.00001 + ε)
    ∧ (cl - ε ≤ windowCov X μ y k σ h m ∧ windowCov X μ y k σ h m ≤ ch + ε)
    ∧ (2 * cl - 1.00001 / 2 - ε ≤ windowMeanR X μ y k σ h m
      ∧ windowMeanR X μ y k σ h m ≤ 2 * ch - 0.99999 / 2 + ε)
    ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * windowMeanR X μ y k σ h m + t ^ 2 * windowVarR X μ y k σ h m / 2
        ≤ 2 * t * ch + (t ^ 2 - t) * 0.99999 / 2 + ε := by
  obtain ⟨hcs, hCs⟩ := blockCosSum_mem_of_cell_short hh hσ hσr hm hc hC
  have hS := blockRpowSum_bounds_of_le hk hσ hσr (by omega : m + 11 ≤ r)
  have he : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg m)))
      (by positivity)
  obtain ⟨h1, h2, h3, h4, h5⟩ := window_block_bounds hX hk hσ hB he hcs hCs hS
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hmk : (20 : ℝ) ≤ (m : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hhk : h ≤ Real.exp (-20) := hh.2.trans (Real.exp_le_exp.2 (by linarith))
  have ec := blockCosErr_le_numeral_of_le_exp hmk hhk
  have eC := blockCosErr_le_numeral hmk (by linarith : 2 * h ≤ 2 * Real.exp (-20))
  refine ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩,
    ⟨by linarith [h3.1], by linarith [h3.2]⟩, ⟨by linarith [h4.1], by linarith [h4.2]⟩,
    fun t ht0 ht1 => ?_⟩
  have h6 := h5 t ht0 ht1
  have h7 : t * (blockCosErr k m h + 1 / 10 ^ 10) ≤ 5.57 / 10 ^ 8 + 1 / 10 ^ 10 := by
    calc t * (blockCosErr k m h + 1 / 10 ^ 10) ≤ t * (5.57 / 10 ^ 8 + 1 / 10 ^ 10) :=
          mul_le_mul_of_nonneg_left (by linarith) ht0
      _ ≤ 1 * (5.57 / 10 ^ 8 + 1 / 10 ^ 10) := mul_le_mul_of_nonneg_right ht1 (by norm_num)
      _ = 5.57 / 10 ^ 8 + 1 / 10 ^ 10 := one_mul _
  linarith

/-- **A block past the grid on the cell, on short tubes** (`4 ≤ m`, `m + 20 ≤ r`, `ξ ≥ -ϑ₁`,
`ϑ₁ ≤ 1`, `e^{ϑ₁} ≤ E`, `k ≥ 20`): `RMF.window_block_bounds_mid_floor` with the damping `10⁻¹⁰`;
the covariance is within the flat `1.94·10⁻⁸ ≥ 1.925·10⁻⁸ + 10⁻¹⁰` of its decaying main term,
`|κ_m| ≤ 1.371Ee^{-m} + 1.94·10⁻⁸`.  Used for `4 ≤ m ≤ 15` when `r ≥ 35`. -/
theorem window_block_bounds_mid_short (hX : IsRademacherPrimeValues X μ) {k r y m : ℕ}
    {σ h ϑ₁ E ε : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hB : primeBlockSub k m ⊆ primesBelowSub y)
    (hm4 : 4 ≤ m) (hm : m + 20 ≤ r) (hϑ : -ϑ₁ ≤ Real.log h + k)
    (hϑ₁ : ϑ₁ ≤ 1) (hE : Real.exp ϑ₁ ≤ E) (hε : 1.12 / 10 ^ 7 ≤ ε) :
    ((0.99999 - 0.6855 * E * Real.exp (-(m : ℝ))) / 2 - ε ≤ windowVarH X μ y k σ h m
      ∧ windowVarH X μ y k σ h m ≤ (1.00001 + 0.6855 * E * Real.exp (-(m : ℝ))) / 2 + ε)
    ∧ windowVarR X μ y k σ h m ≤ 1.00001 + ε
    ∧ |windowCov X μ y k σ h m| ≤ 1.371 * E * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8
    ∧ -(2 * (1.371 * E * Real.exp (-(m : ℝ)))) - 1.00001 / 2 - ε ≤ windowMeanR X μ y k σ h m
    ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * windowMeanR X μ y k σ h m + t ^ 2 * windowVarR X μ y k σ h m / 2
        ≤ 2 * t * (1.371 * E * Real.exp (-(m : ℝ))) + (t ^ 2 - t) * 0.99999 / 2 + ε := by
  have hm4' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hc := abs_le.1 (abs_blockCos_le_of_cell (m := m) hϑ hE (by linarith))
  have hC := abs_le.1 (abs_blockCos_log_two_le_of_cell (m := m) hϑ hE (by linarith))
  obtain ⟨hcs, hCs⟩ := blockCosSum_mem_of_cell_short hh hσ hσr hm hc hC
  have hS := blockRpowSum_bounds_of_le hk hσ hσr (by omega : m + 11 ≤ r)
  have he : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith)) (by positivity)
  obtain ⟨h1, h2, h3, h4, h5⟩ := window_block_bounds hX hk hσ hB he hcs hCs hS
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hhk : h ≤ Real.exp (-20) := hh.2.trans (Real.exp_le_exp.2 (by linarith))
  have ec := blockCosErr_le_numeral_of_twentyFour_le (θ := k) (m := m) (by linarith) hhk
  have eC := blockCosErr_le_numeral (θ := k) (m := m) (by linarith)
    (by linarith : 2 * h ≤ 2 * Real.exp (-20))
  refine ⟨⟨by linarith only [h1.1, eC, hε], by linarith only [h1.2, eC, hε]⟩,
    by linarith only [h2.2, hε],
    abs_le.2 ⟨by linarith only [h3.1, ec], by linarith only [h3.2, ec]⟩,
    by linarith only [h4.1, ec, hε], fun t ht0 ht1 => ?_⟩
  have h6 := h5 t ht0 ht1
  have h7 : t * (blockCosErr k m h + 1 / 10 ^ 10) ≤ 1.925 / 10 ^ 8 + 1 / 10 ^ 10 := by
    calc t * (blockCosErr k m h + 1 / 10 ^ 10) ≤ t * (1.925 / 10 ^ 8 + 1 / 10 ^ 10) :=
          mul_le_mul_of_nonneg_left (by linarith) ht0
      _ ≤ 1 * (1.925 / 10 ^ 8 + 1 / 10 ^ 10) := mul_le_mul_of_nonneg_right ht1 (by norm_num)
      _ = 1.925 / 10 ^ 8 + 1 / 10 ^ 10 := one_mul _
  linarith only [h6, h7, hε]

/-- `e^{-15} ≤ 3.06·10⁻⁷`. -/
lemma exp_neg_fifteen_le : Real.exp (-15) ≤ 3.06 / 10 ^ 7 := by
  interval_decide (trust := kernel)

/-- **A tail block at the floor** (`16 ≤ m < r`, `k ≥ 20`, any damping):
`RMF.window_block_bounds_far_floor` from block `16` — `|c_m|, |C_m| ≤ 3e^{1-m} +
blockCosErrDecay k m τ` with `3e^{1-m} ≤ 9.2·10⁻⁷` in place of `10⁻¹⁶`; the covariance
`|κ_m| ≤ 8.155e^{-m} + 1.93·10⁻⁸`. -/
theorem window_block_bounds_tail_floor (hX : IsRademacherPrimeValues X μ) {k r y m : ℕ}
    {σ h ε : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hB : primeBlockSub k m ⊆ primesBelowSub y)
    (hm16 : 16 ≤ m) (hm : m < r) (hε : 1.12 / 10 ^ 7 ≤ ε) :
    ((0.99 - 9.2 / 10 ^ 7) / 2 - ε ≤ windowVarH X μ y k σ h m
      ∧ windowVarH X μ y k σ h m ≤ (1.00001 + 9.2 / 10 ^ 7) / 2 + ε)
    ∧ windowVarR X μ y k σ h m ≤ 1.00001 + ε
    ∧ |windowCov X μ y k σ h m| ≤ 8.155 * Real.exp (-(m : ℝ)) + 1.93 / 10 ^ 8
    ∧ -(2 * (9.2 / 10 ^ 7)) - 1.00001 / 2 - ε ≤ windowMeanR X μ y k σ h m
    ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * windowMeanR X μ y k σ h m + t ^ 2 * windowVarR X μ y k σ h m / 2
        ≤ 2 * t * (9.2 / 10 ^ 7) + (t ^ 2 - t) * 0.99 / 2 + ε := by
  have hm16' : (16 : ℝ) ≤ m := by exact_mod_cast hm16
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 : 0 < h := (log_add_mem_of_mem_halfWindow hh).1
  have hhk : h ≤ Real.exp (-20) := hh.2.trans (Real.exp_le_exp.2 (by linarith))
  obtain ⟨hc, hC⟩ := abs_blockCosSum_le_window_decay hh hσ m
  have ec : blockCosErrDecay k m h ≤ 1.925 / 10 ^ 8 :=
    (blockCosErrDecay_le_blockCosErr m h0.le).trans
      (blockCosErr_le_numeral_of_twentyFour_le (by linarith) hhk)
  have eC : blockCosErrDecay k m (2 * h) ≤ 7.43 / 10 ^ 8 :=
    (blockCosErrDecay_le_blockCosErr m (by linarith)).trans
      (blockCosErr_le_numeral (by linarith) (by linarith))
  have hem0 := Real.exp_pos (-(m : ℝ))
  have hem : Real.exp (-(m : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he1m : Real.exp (1 - m) = Real.exp 1 * Real.exp (-(m : ℝ)) := by
    rw [← Real.exp_add]
    ring_nf
  have h15 : 3 * Real.exp (1 - m) ≤ 9.2 / 10 ^ 7 := by
    have h1 : Real.exp (1 - m) ≤ Real.exp (-15) := Real.exp_le_exp.2 (by linarith)
    linarith [exp_neg_fifteen_le]
  have hS := blockRpowSum_bounds_of_lt hk hσ hσr hm
  have he20 : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 :=
    div_le_div_of_nonneg_right hem (by positivity)
  obtain ⟨h1, h2, h3, h4, h5⟩ := window_block_bounds hX hk hσ hB le_rfl (abs_le.1 hc)
    (abs_le.1 hC) hS
  have hκ : 3 * Real.exp (1 - m) + Real.exp (-(m : ℝ)) / 10 ^ 20
      ≤ 8.155 * Real.exp (-(m : ℝ)) := by
    have h1e : Real.exp 1 * Real.exp (-(m : ℝ)) ≤ 2.7182818286 * Real.exp (-(m : ℝ)) :=
      mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le hem0.le
    rw [he1m]
    linarith only [h1e, hem0]
  refine ⟨⟨by linarith only [h1.1, h15, eC, he20, hε], by linarith only [h1.2, h15, eC, he20, hε]⟩,
    by linarith only [h2.2, he20, hε],
    abs_le.2 ⟨by linarith only [h3.1, hκ, ec], by linarith only [h3.2, hκ, ec]⟩,
    by linarith only [h4.1, h15, ec, he20, hε], fun t ht0 ht1 => ?_⟩
  have h6 := h5 t ht0 ht1
  have h7 : 2 * t * (3 * Real.exp (1 - m) + blockCosErrDecay k m h)
      ≤ 2 * t * (9.2 / 10 ^ 7) + 2 * (1.925 / 10 ^ 8) := by
    have ha : 3 * Real.exp (1 - m) + blockCosErrDecay k m h ≤ 9.2 / 10 ^ 7 + 1.925 / 10 ^ 8 := by
      linarith
    have := mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 2 * t)
    linarith
  linarith only [h6, h7, he20, hε]

/-! ### The sums against the barrier, split at block `16` -/

/-- **A decaying bound with a flat part below block `84`, split at block `16`**, against the
barrier weight: if `f m ≤ c₁e^{-m} + d` on `[n, 16)`, `≤ c₂e^{-m} + d` on `[16, 84)` and
`≤ c₂e^{-m} + c₃e^{84-m}` on `[84, r)`, the sum over `[n, r)` of `f m (K + B(2m+1))` is at most
`c₁e^{-n}(1.59(K + 2Bn) + 3.43B) + c₂e^{-16}(1.59(K + 32B) + 3.43B) + d((84 - n)K + B(84² - n²))
+ c₃(1.59(K + 168B) + 3.43B)` — `RMF.sum_decay_flat_mul_weight_le` with `40 → 16`. -/
lemma sum_decay_flat_mul_weight_le_sixteen {f : ℕ → ℝ} {n r : ℕ} {c₁ c₂ c₃ d K B : ℝ}
    (hn : n ≤ 16) (hr : 84 ≤ r) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hK : 0 ≤ K)
    (hB : 0 ≤ B)
    (h₁ : ∀ m, n ≤ m → m < 16 → f m ≤ c₁ * Real.exp (-(m : ℝ)) + d)
    (h₂ : ∀ m, 16 ≤ m → m < 84 → f m ≤ c₂ * Real.exp (-(m : ℝ)) + d)
    (h₃ : ∀ m, 84 ≤ m → m < r → f m ≤ c₂ * Real.exp (-(m : ℝ)) + c₃ * Real.exp (84 - m)) :
    ∑ m ∈ Finset.Ico n r, f m * (K + B * (2 * m + 1))
      ≤ c₁ * Real.exp (-(n : ℝ)) * (1.59 * (K + 2 * B * n) + 3.43 * B)
        + c₂ * Real.exp (-16) * (1.59 * (K + 32 * B) + 3.43 * B)
        + d * ((84 - (n : ℝ)) * K + B * (7056 - (n : ℝ) ^ 2))
        + c₃ * (1.59 * (K + 168 * B) + 3.43 * B) := by
  have hw : ∀ m : ℕ, 0 ≤ K + B * (2 * (m : ℝ) + 1) := fun m => by positivity
  rw [← Finset.sum_Ico_consecutive _ hn (by omega : 16 ≤ r),
    ← Finset.sum_Ico_consecutive _ (by norm_num : 16 ≤ 84) hr]
  -- the three ranges, termwise
  have s₁ : ∑ m ∈ Finset.Ico n 16, f m * (K + B * (2 * m + 1))
      ≤ ∑ m ∈ Finset.Ico n 16, c₁ * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
        + d * ∑ m ∈ Finset.Ico n 16, (K + B * (2 * (m : ℝ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.1 hm
    calc f m * (K + B * (2 * m + 1))
        ≤ (c₁ * Real.exp (-(m : ℝ)) + d) * (K + B * (2 * m + 1)) :=
          mul_le_mul_of_nonneg_right (h₁ m hm1 hm2) (hw m)
      _ = c₁ * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1)) + d * (K + B * (2 * m + 1)) := by
          ring
  have s₂ : ∑ m ∈ Finset.Ico (16 : ℕ) 84, f m * (K + B * (2 * m + 1))
      ≤ ∑ m ∈ Finset.Ico (16 : ℕ) 84, c₂ * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
        + d * ∑ m ∈ Finset.Ico (16 : ℕ) 84, (K + B * (2 * (m : ℝ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.1 hm
    calc f m * (K + B * (2 * m + 1))
        ≤ (c₂ * Real.exp (-(m : ℝ)) + d) * (K + B * (2 * m + 1)) :=
          mul_le_mul_of_nonneg_right (h₂ m hm1 hm2) (hw m)
      _ = c₂ * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1)) + d * (K + B * (2 * m + 1)) := by
          ring
  have s₃ : ∑ m ∈ Finset.Ico 84 r, f m * (K + B * (2 * m + 1))
      ≤ ∑ m ∈ Finset.Ico 84 r, c₂ * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
        + ∑ m ∈ Finset.Ico 84 r,
          c₃ * Real.exp 84 * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.1 hm
    have he : Real.exp (84 - (m : ℝ)) = Real.exp 84 * Real.exp (-(m : ℝ)) := by
      rw [← Real.exp_add]
      ring_nf
    calc f m * (K + B * (2 * m + 1))
        ≤ (c₂ * Real.exp (-(m : ℝ)) + c₃ * Real.exp (84 - m)) * (K + B * (2 * m + 1)) :=
          mul_le_mul_of_nonneg_right (h₃ m hm1 hm2) (hw m)
      _ = c₂ * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1))
          + c₃ * Real.exp 84 * Real.exp (-(m : ℝ)) * (K + B * (2 * m + 1)) := by
          rw [he]
          ring
  -- the decaying parts
  have A₁ := sum_mul_exp_neg_mul_le_numeral_of_le (s := Finset.Ico n 16) hc₁ hK hB
    (fun m hm => (Finset.mem_Ico.1 hm).1)
  have A₂ := sum_mul_exp_neg_mul_le_numeral_of_le (s := Finset.Ico 16 r) (n := 16) hc₂ hK hB
    (fun m hm => (Finset.mem_Ico.1 hm).1)
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 16 ≤ 84) hr] at A₂
  have A₃ := sum_mul_exp_neg_mul_le_numeral_of_le (s := Finset.Ico 84 r) (n := 84)
    (c := c₃ * Real.exp 84) (by positivity) hK hB (fun m hm => (Finset.mem_Ico.1 hm).1)
  have e84 : c₃ * Real.exp 84 * Real.exp (-((84 : ℕ) : ℝ)) = c₃ := by
    rw [mul_assoc, ← Real.exp_add]
    norm_num
  rw [e84] at A₃
  -- the flat part
  have hW := sum_Ico_weight_eq K B (by omega : n ≤ 84)
  rw [← Finset.sum_Ico_consecutive _ hn (by norm_num : 16 ≤ 84)] at hW
  push_cast at A₂ A₃ hW
  have hd : d * (∑ m ∈ Finset.Ico n 16, (K + B * (2 * (m : ℝ) + 1))
      + ∑ m ∈ Finset.Ico (16 : ℕ) 84, (K + B * (2 * (m : ℝ) + 1)))
      = d * ((84 - (n : ℝ)) * K + B * (7056 - (n : ℝ) ^ 2)) := by
    rw [hW]
    ring
  linarith [s₁, s₂, s₃, A₁, A₂, A₃, hd]

/-- **…for any number of blocks `r`**: `RMF.sum_decay_flat_mul_weight_le_sixteen` with the bounds
asked only below `r` (`d ≥ 0`); the sum over `[n, r)` is the one over `[n, max(r, 84))` of `f`
cut off at `r`, and `0` is below every bound. -/
lemma sum_decay_flat_mul_weight_le_short {f : ℕ → ℝ} {n r : ℕ} {c₁ c₂ c₃ d K B : ℝ}
    (hn : n ≤ 16) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hB : 0 ≤ B)
    (h₁ : ∀ m, n ≤ m → m < 16 → m < r → f m ≤ c₁ * Real.exp (-(m : ℝ)) + d)
    (h₂ : ∀ m, 16 ≤ m → m < 84 → m < r → f m ≤ c₂ * Real.exp (-(m : ℝ)) + d)
    (h₃ : ∀ m, 84 ≤ m → m < r → f m ≤ c₂ * Real.exp (-(m : ℝ)) + c₃ * Real.exp (84 - m)) :
    ∑ m ∈ Finset.Ico n r, f m * (K + B * (2 * m + 1))
      ≤ c₁ * Real.exp (-(n : ℝ)) * (1.59 * (K + 2 * B * n) + 3.43 * B)
        + c₂ * Real.exp (-16) * (1.59 * (K + 32 * B) + 3.43 * B)
        + d * ((84 - (n : ℝ)) * K + B * (7056 - (n : ℝ) ^ 2))
        + c₃ * (1.59 * (K + 168 * B) + 3.43 * B) := by
  have hsum : ∑ m ∈ Finset.Ico n r, f m * (K + B * (2 * m + 1))
      = ∑ m ∈ Finset.Ico n (max r 84), (if m < r then f m else 0) * (K + B * (2 * m + 1)) := by
    have h1 : ∑ m ∈ Finset.Ico n r, f m * (K + B * (2 * m + 1))
        = ∑ m ∈ Finset.Ico n r, (if m < r then f m else 0) * (K + B * (2 * m + 1)) :=
      Finset.sum_congr rfl fun m hm => by rw [if_pos (Finset.mem_Ico.1 hm).2]
    rw [h1]
    refine Finset.sum_subset (Finset.Ico_subset_Ico_right (le_max_left r 84)) fun m hm hm' => ?_
    have hmr : ¬ m < r := fun h => hm' (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hm).1, h⟩)
    rw [if_neg hmr, zero_mul]
  rw [hsum]
  refine sum_decay_flat_mul_weight_le_sixteen (f := fun m => if m < r then f m else 0) hn
    (le_max_right r 84) hc₁ hc₂ hc₃ hK hB (fun m hnm hm16 => ?_) (fun m hm16 hm84 => ?_)
    (fun m hm84 _ => ?_)
  · split_ifs with hmr
    · exact h₁ m hnm hm16 hmr
    · positivity
  · split_ifs with hmr
    · exact h₂ m hm16 hm84 hmr
    · positivity
  · split_ifs with hmr
    · exact h₃ m hm84 hmr
    · positivity

/-! ### The bundles on short tubes -/

/-- **HP1's start data on short tubes** (`k ≥ 20`, `r ≥ 35`): `RMF.hp1StartRanges_of_cos_floor`
with the first blocks' damping from `m + 20 ≤ r` (`RMF.window_block_bounds_of_cos_short`). -/
theorem hp1StartRanges_of_cos_short (hX : IsRademacherPrimeValues X μ) {k r y : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 35 ≤ r)
    {ε : ℝ} (hε : 1.12 / 10 ^ 7 ≤ ε)
    {c0l c0h c1l c1h C0l C0h C1l C1h : ℝ}
    (hc₀ : c0l ≤ blockCos (Real.log h + k) 0 ∧ blockCos (Real.log h + k) 0 ≤ c0h)
    (hc₁ : c1l ≤ blockCos (Real.log h + k) 1 ∧ blockCos (Real.log h + k) 1 ≤ c1h)
    (hC₀ : C0l ≤ blockCos (Real.log 2 + (Real.log h + k)) 0
      ∧ blockCos (Real.log 2 + (Real.log h + k)) 0 ≤ C0h)
    (hC₁ : C1l ≤ blockCos (Real.log 2 + (Real.log h + k)) 1
      ∧ blockCos (Real.log 2 + (Real.log h + k)) 1 ≤ C1h)
    {v0l v0h v1l v1h kl kh Sl Sh σl σh d0 Dl Dh : ℝ}
    (hv₀ : 0 < v0l ∧ v0l ≤ (0.99999 + C0l) / 2 - ε ∧ (1.00001 + C0h) / 2 + ε ≤ v0h)
    (hv₁ : 0 < v1l ∧ v1l ≤ (0.99999 + C1l) / 2 - ε ∧ (1.00001 + C1h) / 2 + ε ≤ v1h)
    (hκ : kl ≤ c0l + c1l - 2 * ε ∧ c0h + c1h + 2 * ε ≤ kh)
    (hS : Sl ≤ 2 * 0.99999 - 2 * ε ∧ 2 * 1.00001 + 2 * ε ≤ Sh)
    (hσ₁ : σl ≤ 0.99999 - ε ∧ 1.00001 + ε ≤ σh)
    (hd₀ : -d0 ≤ 2 * c0l - 1.00001 / 2 - ε ∧ 2 * c0h - 0.99999 / 2 + ε ≤ d0)
    (hD : Dl ≤ 2 * (c0l + c1l) - 1.00001 - 2 * ε
      ∧ 2 * (c0h + c1h) - 0.99999 + 2 * ε ≤ Dh) :
    HP1StartRanges (windowVarH X μ y k σ h 0) (windowVarH X μ y k σ h 1)
      (windowResid X μ y k σ h 0) (windowResid X μ y k σ h 1)
      (windowSlope X μ y k σ h 0) (windowSlope X μ y k σ h 1)
      (windowMeanR X μ y k σ h 0) (windowMeanR X μ y k σ h 1)
      v0l v0h v1l v1h kl kh Sl Sh σl σh d0 Dl Dh := by
  obtain ⟨b0V, b0W, b0κ, b0d, -⟩ :=
    window_block_bounds_of_cos_short hX hk hh hσ hσr (hy 0 (by omega)) (by omega) hε hc₀ hC₀
  obtain ⟨b1V, b1W, b1κ, b1d, -⟩ :=
    window_block_bounds_of_cos_short hX hk hh hσ hσr (hy 1 (by omega)) (by omega) hε hc₁ hC₁
  have hV0 : windowVarH X μ y k σ h 0 ≠ 0 := by linarith [b0V.1, hv₀.1, hv₀.2.1]
  have hV1 : windowVarH X μ y k σ h 1 ≠ 0 := by linarith [b1V.1, hv₁.1, hv₁.2.1]
  have e0 : windowSlope X μ y k σ h 0 * windowVarH X μ y k σ h 0 = windowCov X μ y k σ h 0 :=
    pairSlope_mul_self hV0
  have e1 : windowSlope X μ y k σ h 1 * windowVarH X μ y k σ h 1 = windowCov X μ y k σ h 1 :=
    pairSlope_mul_self hV1
  have f0 : windowSlope X μ y k σ h 0 ^ 2 * windowVarH X μ y k σ h 0
      + windowResid X μ y k σ h 0 = windowVarR X μ y k σ h 0 :=
    pairSlope_sq_mul_add_pairResidVar hV0
  have f1 : windowSlope X μ y k σ h 1 ^ 2 * windowVarH X μ y k σ h 1
      + windowResid X μ y k σ h 1 = windowVarR X μ y k σ h 1 :=
    pairSlope_sq_mul_add_pairResidVar hV1
  refine ⟨⟨by linarith [b0V.1, hv₀.2.1], by linarith [b0V.2, hv₀.2.2]⟩,
    ⟨by linarith [b1V.1, hv₁.2.1], by linarith [b1V.2, hv₁.2.2]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, e1]
    exact ⟨by linarith [b0κ.1, b1κ.1, hκ.1], by linarith [b0κ.2, b1κ.2, hκ.2]⟩
  · rw [f0, f1]
    exact ⟨by linarith [b0W.1, b1W.1, hS.1], by linarith [b0W.2, b1W.2, hS.2]⟩
  · rw [f0]
    exact ⟨by linarith [b0W.1, hσ₁.1], by linarith [b0W.2, hσ₁.2]⟩
  · exact abs_le.2 ⟨by linarith [b0d.1, hd₀.1], by linarith [b0d.2, hd₀.2]⟩
  · exact ⟨by linarith [b0d.1, b1d.1, hD.1], by linarith [b0d.2, b1d.2, hD.2]⟩

/-- `1.94·10⁻⁸ ≤ 1.58·10⁻⁴e^{-m}` for `m ≤ 9` (`e^{-9} ≥ 1.234·10⁻⁴`): the flat covariance error
on short tubes inside `σ_R²`'s decaying coefficient. -/
lemma flat_le_mul_exp_neg_of_le_nine_short {m : ℕ} (hm : m ≤ 9) :
    1.94 / 10 ^ 8 ≤ 1.58 / 10 ^ 4 * Real.exp (-(m : ℝ)) := by
  have e9 : (1.234 : ℝ) / 10 ^ 4 ≤ Real.exp (-9) := by interval_decide (trust := kernel)
  have hm' : (m : ℝ) ≤ 9 := by exact_mod_cast hm
  have h1 : Real.exp (-9) ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have h2 := mul_le_mul_of_nonneg_left (e9.trans h1) (by norm_num : (0 : ℝ) ≤ 1.58 / 10 ^ 4)
  linarith

/-- `e^{-16} ≤ 1.1254·10⁻⁷`. -/
lemma exp_neg_sixteen_le : Real.exp (-16) ≤ 1.1254 / 10 ^ 7 := by
  interval_decide (trust := kernel)

set_option maxHeartbeats 1000000 in
-- Eight hypotheses from the ranges of four explicit blocks and three tails; long rather than deep.
/-- **HP1's window hypotheses on short tubes** (`k ≥ 20`, `r ≥ 35`, `m₀ = 8`):
`RMF.hp1WindowHyps_of_cos_floor` with blocks `0 … 3` from their ranges at the damping `10⁻¹⁰`
(`RMF.window_block_bounds_of_cos_short`), `4 ≤ m ≤ 15` by the cell's decay
(`RMF.window_block_bounds_mid_short`, the flat covariance error `1.94·10⁻⁸`) and `m ≥ 16` at any
damping (`RMF.window_block_bounds_tail_floor`; decaying again from block `84`,
`RMF.abs_windowCov_le_of_eightyFour_le`): the exit exponent's sign from block `16` (`hΛ₁₆`), `σ_R²`
with the coefficient `1.371E + 1.58·10⁻⁴`, and `K_late`, `K_R` with the tail
`8.155e^{-16}(1.59(2a + 2A + 32B) + 3.43B)/v_t` (`e^{-16} ≤ 1.1254·10⁻⁷`) and the flat sums at
`1.94·10⁻⁸` (`RMF.sum_decay_flat_mul_weight_le_short`). -/
theorem hp1WindowHyps_of_cos_short (hX : IsRademacherPrimeValues X μ) {k r y : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 35 ≤ r)
    {ε : ℝ} (hε : 1.12 / 10 ^ 7 ≤ ε)
    {ϑ₁ E : ℝ} (hϑ : -ϑ₁ ≤ Real.log h + k) (hϑ₀ : 0 ≤ ϑ₁) (hϑ₁ : ϑ₁ ≤ 1)
    (hE : Real.exp ϑ₁ ≤ E)
    {c0l c0h c1l c1h c2l c2h c3l c3h C0l C0h C1l C1h C2l C2h C3l C3h : ℝ}
    (hc₀ : c0l ≤ blockCos (Real.log h + k) 0 ∧ blockCos (Real.log h + k) 0 ≤ c0h)
    (hc₁ : c1l ≤ blockCos (Real.log h + k) 1 ∧ blockCos (Real.log h + k) 1 ≤ c1h)
    (hc₂ : c2l ≤ blockCos (Real.log h + k) 2 ∧ blockCos (Real.log h + k) 2 ≤ c2h)
    (hc₃ : c3l ≤ blockCos (Real.log h + k) 3 ∧ blockCos (Real.log h + k) 3 ≤ c3h)
    (hC₀ : C0l ≤ blockCos (Real.log 2 + (Real.log h + k)) 0
      ∧ blockCos (Real.log 2 + (Real.log h + k)) 0 ≤ C0h)
    (hC₁ : C1l ≤ blockCos (Real.log 2 + (Real.log h + k)) 1
      ∧ blockCos (Real.log 2 + (Real.log h + k)) 1 ≤ C1h)
    (hC₂ : C2l ≤ blockCos (Real.log 2 + (Real.log h + k)) 2
      ∧ blockCos (Real.log 2 + (Real.log h + k)) 2 ≤ C2h)
    (hC₃ : C3l ≤ blockCos (Real.log 2 + (Real.log h + k)) 3
      ∧ blockCos (Real.log 2 + (Real.log h + k)) 3 ≤ C3h)
    {vmin vmax v2l v3l vt a A B t Λ BW n2 n3 b2 b3 σR2 Klate KR M₁ K₂ : ℝ}
    (hv₂ : 0 < v2l ∧ v2l ≤ (0.99999 + C2l) / 2 - ε)
    (hv₃ : 0 < v3l ∧ v3l ≤ (0.99999 + C3l) / 2 - ε)
    (hvt : 0 < vt ∧ vt ≤ (0.99 - 0.6855 * E * 0.018316) / 2 - ε)
    (hvmin : vmin ≤ v2l ∧ vmin ≤ v3l ∧ vmin ≤ vt)
    (hvmax : (1.00001 + C2h) / 2 + ε ≤ vmax ∧ (1.00001 + C3h) / 2 + ε ≤ vmax
      ∧ (1.00001 + 0.6855 * E * 0.018316) / 2 + ε ≤ vmax)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (hΛ : max 0 (2 * t * c2h + (t ^ 2 - t) * 0.99999 / 2 + ε)
        + max 0 (2 * t * c3h + (t ^ 2 - t) * 0.99999 / 2 + ε)
        + max 0 (2 * t * (1.371 * E * 0.018316) + (t ^ 2 - t) * 0.99999 / 2 + ε)
        + max 0 (2 * t * (1.371 * E * 0.0067381) + (t ^ 2 - t) * 0.99999 / 2 + ε)
        ≤ Λ)
    (hΛ₆ : 2 * t * (1.371 * E * 0.002479) + (t ^ 2 - t) * 0.99999 / 2 + ε ≤ 0)
    (hΛ₁₆ : 2 * t * (9.2 / 10 ^ 7) + (t ^ 2 - t) * 0.99 / 2 + ε ≤ 0)
    (hBW : 1.00001 - 2 * c2l + 2 * ε ≤ BW ∧ 1.00001 - 2 * c3l + 2 * ε ≤ BW
      ∧ 1.00001 + 2 * (1.371 * E * 0.018316) + 2 * ε ≤ BW)
    (hn₂ : 0 ≤ n2 ∧ ε - c2l ≤ n2) (hn₃ : 0 ≤ n3 ∧ ε - c3l ≤ n3)
    (hσR : n2 ^ 2 / v2l + n3 ^ 2 / v3l + (1.371 * E + 1.58 / 10 ^ 4) ^ 2
        * (0.13534 ^ 4 + 0.13534 ^ 5 + 0.13534 ^ 6 + 0.13534 ^ 7 + 0.13534 ^ 8 + 0.13534 ^ 9) / vt
        ≤ σR2)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKlate : 1.371 * E / vt * 0.00004541 * (1.59 * (2 * a + 2 * A + 2 * B * 10) + 3.43 * B)
        + 8.155 / vt * (1.1254 / 10 ^ 7) * (1.59 * (2 * a + 2 * A + 2 * B * 16) + 3.43 * B)
        + 1.94 / 10 ^ 8 / vt * (74 * (2 * a + 2 * A) + 6956 * B)
        + 1 / 10 ^ 27 / vt * (1.59 * (2 * a + 2 * A + 2 * B * 84) + 3.43 * B) ≤ Klate)
    (hb₂ : c2h + ε ≤ b2 ∧ ε - c2l ≤ b2)
    (hb₃ : c3h + ε ≤ b3 ∧ ε - c3l ≤ b3)
    (hKR : b2 / v2l * (2 * a + 2 * A + 5 * B) + b3 / v3l * (2 * a + 2 * A + 7 * B)
        + (1.371 * E / vt * 0.018316 * (1.59 * (2 * a + 2 * A + 2 * B * 4) + 3.43 * B)
          + 8.155 / vt * (1.1254 / 10 ^ 7) * (1.59 * (2 * a + 2 * A + 2 * B * 16) + 3.43 * B)
          + 1.94 / 10 ^ 8 / vt * (80 * (2 * a + 2 * A) + 7040 * B)
          + 1 / 10 ^ 27 / vt * (1.59 * (2 * a + 2 * A + 2 * B * 84) + 3.43 * B)) ≤ KR)
    (hM₁ : -M₁ ≤ 2 * c0l - 1.00001 / 2 - ε ∧ 2 * c0h - 0.99999 / 2 + ε ≤ M₁)
    (hK₂ : 0 ≤ K₂ + (2 * c0l - 1.00001 / 2 - ε) + (2 * c1l - 1.00001 / 2 - ε)) :
    HP1WindowHyps X μ y k r 8 σ h vmin vmax a A B t Λ BW σR2 Klate KR M₁ K₂ := by
  obtain ⟨e4, e5, e6, e10, -, e2⟩ := hp1_exp_bounds
  have e16 := exp_neg_sixteen_le
  have hE1 : 1 ≤ E := (Real.one_le_exp hϑ₀).trans hE
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hvt0, hvt⟩ := hvt
  -- the explicit blocks
  obtain ⟨-, -, -, b0d, -⟩ :=
    window_block_bounds_of_cos_short hX hk hh hσ hσr (hy 0 (by omega)) (by omega) hε hc₀ hC₀
  obtain ⟨-, -, -, b1d, -⟩ :=
    window_block_bounds_of_cos_short hX hk hh hσ hσr (hy 1 (by omega)) (by omega) hε hc₁ hC₁
  obtain ⟨b2V, b2W, b2κ, b2d, b2X⟩ :=
    window_block_bounds_of_cos_short hX hk hh hσ hσr (hy 2 (by omega)) (by omega) hε hc₂ hC₂
  obtain ⟨b3V, b3W, b3κ, b3d, b3X⟩ :=
    window_block_bounds_of_cos_short hX hk hh hσ hσr (hy 3 (by omega)) (by omega) hε hc₃ hC₃
  have hV₂ : v2l ≤ windowVarH X μ y k σ h 2 := by linarith only [b2V.1, hv₂.2]
  have hV₃ : v3l ≤ windowVarH X μ y k σ h 3 := by linarith only [b3V.1, hv₃.2]
  -- the blocks past the grid: by the cell's decay to block `15`, at any damping from `16`
  have hexp : ∀ m : ℕ, 4 ≤ m → Real.exp (-(m : ℝ)) ≤ 0.018316 := fun m hm =>
    exp_neg_natCast_le_of_le hm (by rw [show ((4 : ℕ) : ℝ) = 4 by norm_num]; exact e4)
  have hmid := fun (m : ℕ) (hm4 : 4 ≤ m) (hm15 : m ≤ 15) =>
    window_block_bounds_mid_short hX hk hh hσ hσr (hy m (by omega)) hm4 (by omega) hϑ hϑ₁ hE hε
  have htl := fun (m : ℕ) (hm16 : 16 ≤ m) (hmr : m < r) =>
    window_block_bounds_tail_floor hX hk hh hσ hσr (hy m hmr) hm16 hmr hε
  have hpnt := fun (m : ℕ) (hm84 : 84 ≤ m) (hmr : m < r) =>
    abs_windowCov_le_of_eightyFour_le hX hk hh hσ (hy m hmr) hm84
  have hEe : 0 ≤ 0.6855 * E := by positivity
  -- every block from `4` on: `vt ≤ V¹ ≤ (1.00001 + 0.6855E·0.018316)/2 + ε`, `W`, `d`
  have htail : ∀ m : ℕ, 4 ≤ m → m < r → vt ≤ windowVarH X μ y k σ h m
      ∧ windowVarH X μ y k σ h m ≤ (1.00001 + 0.6855 * E * 0.018316) / 2 + ε
      ∧ windowVarR X μ y k σ h m ≤ 1.00001 + ε
      ∧ -(2 * (1.371 * E * 0.018316)) - 1.00001 / 2 - ε
        ≤ windowMeanR X μ y k σ h m := by
    intro m hm4 hmr
    rcases lt_or_ge m 16 with hm16 | hm16
    · obtain ⟨hV, hW, -, hd, -⟩ := hmid m hm4 (by omega)
      have h1 := mul_le_mul_of_nonneg_left (hexp m hm4) hEe
      have h2 : 1.371 * E * Real.exp (-(m : ℝ)) ≤ 1.371 * E * 0.018316 :=
        mul_le_mul_of_nonneg_left (hexp m hm4) (by positivity)
      exact ⟨by linarith only [hV.1, h1, hvt], by linarith only [hV.2, h1], hW,
        by linarith only [hd, h2]⟩
    · obtain ⟨hV, hW, -, hd, -⟩ := htl m hm16 hmr
      exact ⟨by linarith only [hV.1, hE1, hvt], by linarith only [hV.2, hE1], hW,
        by linarith only [hd, hE1]⟩
  have hpos : ∀ m : ℕ, 2 ≤ m → m < r → 0 < windowVarH X μ y k σ h m := by
    intro m hm2 hmr
    rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | hm4
    · linarith only [hV₂, hv₂.1]
    · linarith only [hV₃, hv₃.1]
    · linarith only [(htail m hm4 hmr).1, hvt0]
  -- the covariances past the grid: decaying, a flat part below block `84`
  have hκmid : ∀ m : ℕ, 4 ≤ m → m < 16 → |windowCov X μ y k σ h m|
      ≤ 1.371 * E * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8 := fun m hm4 hm16 =>
    (hmid m hm4 (by omega)).2.2.1
  have hκtl : ∀ m : ℕ, 16 ≤ m → m < r → |windowCov X μ y k σ h m|
      ≤ 8.155 * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8 := fun m hm16 hmr => by
    have := (htl m hm16 hmr).2.2.1
    linarith
  -- the slopes past the grid
  have hβmid : ∀ m : ℕ, 4 ≤ m → m < 16 → |windowSlope X μ y k σ h m|
      ≤ 1.371 * E / vt * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8 / vt := by
    intro m hm4 hm16
    have := abs_pairSlope_le hvt0 (htail m hm4 (by omega)).1 (hκmid m hm4 hm16)
    calc |windowSlope X μ y k σ h m|
        ≤ (1.371 * E * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8) / vt := this
      _ = 1.371 * E / vt * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8 / vt := by ring
  have hβtl : ∀ m : ℕ, 16 ≤ m → m < r → |windowSlope X μ y k σ h m|
      ≤ 8.155 / vt * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8 / vt := by
    intro m hm16 hmr
    have := abs_pairSlope_le hvt0 (htail m (by omega) hmr).1 (hκtl m hm16 hmr)
    calc |windowSlope X μ y k σ h m|
        ≤ (8.155 * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8) / vt := this
      _ = 8.155 / vt * Real.exp (-(m : ℝ)) + 1.94 / 10 ^ 8 / vt := by ring
  have hβpnt : ∀ m : ℕ, 84 ≤ m → m < r → |windowSlope X μ y k σ h m|
      ≤ 8.155 / vt * Real.exp (-(m : ℝ)) + 1 / 10 ^ 27 / vt * Real.exp (84 - m) := by
    intro m hm84 hmr
    have := abs_pairSlope_le hvt0 (htail m (by omega) hmr).1 (hpnt m hm84 hmr)
    calc |windowSlope X μ y k σ h m|
        ≤ (8.155 * Real.exp (-(m : ℝ)) + Real.exp (84 - m) / 10 ^ 27) / vt := this
      _ = 8.155 / vt * Real.exp (-(m : ℝ)) + 1 / 10 ^ 27 / vt * Real.exp (84 - m) := by ring
  have hK : 0 ≤ 2 * a + 2 * A := by positivity
  have hwt : ∀ m : ℕ, (a + A + B * m) + (a + A + B * (m + 1)) = (2 * a + 2 * A) + B * (2 * m + 1) :=
    fun m => by ring
  have hc₁ : 0 ≤ 1.371 * E / vt := by positivity
  have hc₂ : 0 ≤ 8.155 / vt := by positivity
  have hc₃ : 0 ≤ 1 / 10 ^ 27 / vt := by positivity
  have hd : 0 ≤ 1.94 / 10 ^ 8 / vt := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- hvb
  · intro m hm2 hmr
    rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | hm4
    · exact ⟨by linarith only [hV₂, hvmin.1], by linarith only [b2V.2, hvmax.1]⟩
    · exact ⟨by linarith only [hV₃, hvmin.2.1], by linarith only [b3V.2, hvmax.2.1]⟩
    · obtain ⟨h1, h2, -⟩ := htail m hm4 hmr
      exact ⟨by linarith only [h1, hvmin.2.2], by linarith only [h2, hvmax.2.2]⟩
  -- hΛ
  · have hterm : ∀ m : ℕ, 2 ≤ m → m < r → ∀ Y : ℝ,
        t * windowMeanR X μ y k σ h m + t ^ 2 * windowVarR X μ y k σ h m / 2 ≤ Y →
        max 0 (t * windowMeanR X μ y k σ h m + t ^ 2 * (max (windowSlope X μ y k σ h m) 0 ^ 2
          * windowVarH X μ y k σ h m + windowResid X μ y k σ h m) / 2) ≤ max 0 Y := by
      intro m hm2 hmr Y hY
      have h1 := max_pairSlope_sq_mul_add_le (W := windowVarR X μ y k σ h m)
        (c := windowCov X μ y k σ h m) (hpos m hm2 hmr)
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg t)
      refine max_le_max le_rfl ?_
      change t * windowMeanR X μ y k σ h m + t ^ 2 * (max (pairSlope (windowVarH X μ y k σ h m)
          (windowCov X μ y k σ h m)) 0 ^ 2 * windowVarH X μ y k σ h m
          + pairResidVar (windowVarH X μ y k σ h m) (windowVarR X μ y k σ h m)
            (windowCov X μ y k σ h m)) / 2 ≤ Y
      linarith
    have hmidX : ∀ m : ℕ, 4 ≤ m → m ≤ 15 → ∀ b : ℝ, Real.exp (-(m : ℝ)) ≤ b →
        t * windowMeanR X μ y k σ h m + t ^ 2 * windowVarR X μ y k σ h m / 2
          ≤ 2 * t * (1.371 * E * b) + (t ^ 2 - t) * 0.99999 / 2 + ε := by
      intro m hm4 hm15 b hb
      have h1 := (hmid m hm4 hm15).2.2.2.2 t ht0 ht1
      have h2 : 2 * t * (1.371 * E * Real.exp (-(m : ℝ))) ≤ 2 * t * (1.371 * E * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
      linarith
    refine sum_Ico_two_le_of_terms (by omega) (hterm 2 le_rfl (by omega) _ (b2X t ht0 ht1))
      (hterm 3 (by norm_num) (by omega) _ (b3X t ht0 ht1))
      (hterm 4 (by norm_num) (by omega) _ (hmidX 4 le_rfl (by norm_num) 0.018316
        (by rw [show ((4 : ℕ) : ℝ) = 4 by norm_num]; exact e4)))
      (hterm 5 (by norm_num) (by omega) _ (hmidX 5 (by norm_num) (by norm_num) 0.0067381
        (by rw [show ((5 : ℕ) : ℝ) = 5 by norm_num]; exact e5))) (fun m hm6 hmr => ?_) hΛ
    rcases lt_or_ge m 16 with hm16 | hm16
    · have h1 := hterm m (by omega) hmr _ (hmidX m (by omega) (by omega) 0.002479
        (exp_neg_natCast_le_of_le hm6 (by rw [show ((6 : ℕ) : ℝ) = 6 by norm_num]; exact e6)))
      rwa [max_eq_left hΛ₆] at h1
    · have h1 := hterm m (by omega) hmr _ ((htl m hm16 hmr).2.2.2.2 t ht0 ht1)
      rwa [max_eq_left hΛ₁₆] at h1
  -- hBW
  · intro m hm2 hmr
    have hR := pairResidVar_le (W := windowVarR X μ y k σ h m) (c := windowCov X μ y k σ h m)
      (hpos m hm2 hmr)
    have hε0 : 0 ≤ ε := le_trans (by norm_num) hε
    change pairResidVar (windowVarH X μ y k σ h m) (windowVarR X μ y k σ h m)
      (windowCov X μ y k σ h m) / 2 - windowMeanR X μ y k σ h m ≤ BW
    rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | hm4
    · linarith only [hR, b2W.2, b2d.1, hBW.1, hε0]
    · linarith only [hR, b3W.2, b3d.1, hBW.2.1, hε0]
    · obtain ⟨-, -, hW, hd⟩ := htail m hm4 hmr
      linarith only [hR, hW, hd, hBW.2.2, hε0]
  -- hσR
  · rw [show (8 : ℕ) + 2 = 10 by norm_num, sum_Ico_two_ten]
    have hG₂ : min (windowSlope X μ y k σ h 2) 0 ^ 2 * windowVarH X μ y k σ h 2 ≤ n2 ^ 2 / v2l :=
      min_pairSlope_sq_mul_le hv₂.1 hV₂ hn₂.1 (by linarith only [b2κ.1, hn₂.2])
    have hG₃ : min (windowSlope X μ y k σ h 3) 0 ^ 2 * windowVarH X μ y k σ h 3 ≤ n3 ^ 2 / v3l :=
      min_pairSlope_sq_mul_le hv₃.1 hV₃ hn₃.1 (by linarith only [b3κ.1, hn₃.2])
    have hG : ∀ m : ℕ, 4 ≤ m → m < 10 →
        min (windowSlope X μ y k σ h m) 0 ^ 2 * windowVarH X μ y k σ h m
          ≤ (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ m / vt := by
      intro m hm4 hm10
      have hmr : m < r := by omega
      have hκ := hκmid m hm4 (by omega)
      have hflat := flat_le_mul_exp_neg_of_le_nine_short (m := m) (by omega)
      have hn : -windowCov X μ y k σ h m ≤ (1.371 * E + 1.58 / 10 ^ 4) * Real.exp (-(m : ℝ)) := by
        have := (neg_le_abs _).trans hκ
        linarith
      have hn0 : 0 ≤ (1.371 * E + 1.58 / 10 ^ 4) * Real.exp (-(m : ℝ)) :=
        mul_nonneg (by positivity) (Real.exp_pos _).le
      have h1 := min_pairSlope_sq_mul_le hvt0 (htail m hm4 hmr).1 hn0 hn
      have h2 := exp_neg_natCast_sq_le (m := m) e2
      calc _ ≤ ((1.371 * E + 1.58 / 10 ^ 4) * Real.exp (-(m : ℝ))) ^ 2 / vt := h1
        _ = (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * Real.exp (-(m : ℝ)) ^ 2 / vt := by ring
        _ ≤ (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ m / vt := by gcongr
    have h4 := hG 4 le_rfl (by norm_num)
    have h5 := hG 5 (by norm_num) (by norm_num)
    have h6 := hG 6 (by norm_num) (by norm_num)
    have h7 := hG 7 (by norm_num) (by norm_num)
    have h8 := hG 8 (by norm_num) (by norm_num)
    have h9 := hG 9 (by norm_num) (by norm_num)
    have hsum : (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ 4 / vt
        + (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ 5 / vt
        + (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ 6 / vt
        + (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ 7 / vt
        + (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ 8 / vt
        + (1.371 * E + 1.58 / 10 ^ 4) ^ 2 * 0.13534 ^ 9 / vt
        = (1.371 * E + 1.58 / 10 ^ 4) ^ 2
          * (0.13534 ^ 4 + 0.13534 ^ 5 + 0.13534 ^ 6 + 0.13534 ^ 7 + 0.13534 ^ 8
            + 0.13534 ^ 9) / vt := by ring
    linarith only [hG₂, hG₃, h4, h5, h6, h7, h8, h9, hsum, hσR]
  -- hKlate
  · rw [show (8 : ℕ) + 2 = 10 by norm_num]
    simp_rw [hwt]
    have hs := sum_decay_flat_mul_weight_le_short
      (f := fun m => |min (windowSlope X μ y k σ h m) 0|)
      (n := 10) (r := r) (c₁ := 1.371 * E / vt) (c₂ := 8.155 / vt) (c₃ := 1 / 10 ^ 27 / vt)
      (d := 1.94 / 10 ^ 8 / vt) (by norm_num) hc₁ hc₂ hc₃ hd hK hB
      (fun m hm10 hm16 _ => (abs_min_zero_le _).trans (hβmid m (by omega) hm16))
      (fun m hm16 _ hmr => (abs_min_zero_le _).trans (hβtl m hm16 hmr))
      (fun m hm84 hmr => (abs_min_zero_le _).trans (hβpnt m hm84 hmr))
    have hP₁ : 0 ≤ 1.59 * (2 * a + 2 * A + 2 * B * 10) + 3.43 * B := by positivity
    have hP₂ : 0 ≤ 1.59 * (2 * a + 2 * A + 32 * B) + 3.43 * B := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e10 hc₁) hP₁
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e16 hc₂) hP₂
    simp only [Nat.cast_ofNat] at hs
    linarith only [hs, h1, h2, hKlate]
  -- hKR
  · simp_rw [hwt]
    rw [sum_Ico_two_eq (by omega)]
    have hs := sum_decay_flat_mul_weight_le_short (f := fun m => |windowSlope X μ y k σ h m|)
      (n := 4) (r := r) (c₁ := 1.371 * E / vt) (c₂ := 8.155 / vt) (c₃ := 1 / 10 ^ 27 / vt)
      (d := 1.94 / 10 ^ 8 / vt) (by norm_num) hc₁ hc₂ hc₃ hd hK hB
      (fun m hm4 hm16 _ => hβmid m hm4 hm16)
      (fun m hm16 _ hmr => hβtl m hm16 hmr)
      (fun m hm84 hmr => hβpnt m hm84 hmr)
    have hβ₂ : |windowSlope X μ y k σ h 2| ≤ b2 / v2l :=
      abs_pairSlope_le hv₂.1 hV₂ (abs_le.2 ⟨by linarith only [b2κ.1, hb₂.2],
        by linarith only [b2κ.2, hb₂.1]⟩)
    have hβ₃ : |windowSlope X μ y k σ h 3| ≤ b3 / v3l :=
      abs_pairSlope_le hv₃.1 hV₃ (abs_le.2 ⟨by linarith only [b3κ.1, hb₃.2],
        by linarith only [b3κ.2, hb₃.1]⟩)
    have hw₂ : 0 ≤ 2 * a + 2 * A + B * (2 * ((2 : ℕ) : ℝ) + 1) := by positivity
    have hw₃ : 0 ≤ 2 * a + 2 * A + B * (2 * ((3 : ℕ) : ℝ) + 1) := by positivity
    have h2 := mul_le_mul_of_nonneg_right hβ₂ hw₂
    have h3 := mul_le_mul_of_nonneg_right hβ₃ hw₃
    have hP₁ : 0 ≤ 1.59 * (2 * a + 2 * A + 2 * B * 4) + 3.43 * B := by positivity
    have hP₂ : 0 ≤ 1.59 * (2 * a + 2 * A + 32 * B) + 3.43 * B := by positivity
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e4 hc₁) hP₁
    have h5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e16 hc₂) hP₂
    simp only [Nat.cast_ofNat] at hs h2 h3 ⊢
    have e₂ : b2 / v2l * (2 * a + 2 * A + B * (2 * 2 + 1))
        = b2 / v2l * (2 * a + 2 * A + 5 * B) := by
      ring
    have e₃ : b3 / v3l * (2 * a + 2 * A + B * (2 * 3 + 1))
        = b3 / v3l * (2 * a + 2 * A + 7 * B) := by
      ring
    linarith only [hs, h2, h3, h4, h5, hKR, e₂, e₃]
  -- hM₁
  · exact abs_le.2 ⟨by linarith only [b0d.1, hM₁.1], by linarith only [b0d.2, hM₁.2]⟩
  -- hK₂
  · linarith only [b0d.1, b1d.1, hK₂]

end RMF
