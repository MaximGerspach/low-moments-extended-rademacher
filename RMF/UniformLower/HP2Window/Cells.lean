/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2PairCells

/-!
# HP2's window integral: the pair bound on every cell

For heights `h₁, h₂` in the window at `k ≥ 20`, `t = |h₁ - h₂|e^k`, the per-cell discharges of the
pair bound `RMF.integral_hp1Tube_inter_le_hp2PairBoundOf` (`RMF/UniformLower/HP2PairCells.lean`)
give `E[1_{H(k,h₁)∩H(k,h₂)}‖F(s₁)‖²‖F(s₂)‖²] ≤ E‖F(s₁)‖²E‖F(s₂)‖²·C` with a constant `C` that
depends only on the cell of `t`:

* on the cell `j` of depth `d ≤ r - 3` (`t ∈ (e^{-(40d+j+1)/40}, e^{-(40d+j)/40}]`),
  `C = RMF.hp2WinCell r d j` (`RMF.integral_pair_le_hp2WinCell`) — the post bound of the cell's
  class with `n₀ = min(r - b, 1000)`, the cell's bridge, its mass, the prefix masses with Mertens
  telescoped (`RMF.hp2PrefixExpM`: the per-block `1 + 1/150000` would grow like `e^{d/150000}`),
  the best prefix bound of the depth, and for `d ≥ 4` also the trivial post bound (probability
  `≤ 1`, `RMF.isHP2PostBound_trivial`);
* below the last cell (`t ≤ e^{-(r-2)}`), the prefix alone at `M = r`, `C = RMF.hp2WinDeep r`
  (`RMF.integral_pair_le_hp2WinDeep`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The prefix masses with Mertens telescoped -/

/-- `C_m(0) = S_m`. -/
lemma blockCosSum_zero (θ σ : ℝ) (m : ℕ) : blockCosSum θ σ 0 m = blockRpowSum θ σ m := by
  unfold blockCosSum blockRpowSum
  simp

/-- `∫_a^b e^{-2σu}/u du ≤ log(b/a)` for `0 < a ≤ b`, `σ ≥ 0`. -/
lemma integral_exp_div_le_log {a b σ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hσ : 0 ≤ σ) :
    ∫ u in a..b, Real.cos (0 * u) * Real.exp (-(2 * σ) * u) / u ≤ Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [← integral_inv_of_pos ha hb]
  have hc : ContinuousOn (fun u : ℝ => Real.cos (0 * u) * Real.exp (-(2 * σ) * u) / u)
      (Set.uIcc a b) := by
    refine ContinuousOn.div (by fun_prop) continuousOn_id fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    exact (lt_of_lt_of_le ha hu.1).ne'
  have hc' : ContinuousOn (fun u : ℝ => u⁻¹) (Set.uIcc a b) := by
    refine continuousOn_id.inv₀ fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    exact (lt_of_lt_of_le ha hu.1).ne'
  refine intervalIntegral.integral_mono_on hab (hc.intervalIntegrable) (hc'.intervalIntegrable)
    fun u hu => ?_
  have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
  rw [zero_mul, Real.cos_zero, one_mul, div_eq_mul_inv]
  have he : Real.exp (-(2 * σ) * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.exp (-(2 * σ) * u) * u⁻¹ ≤ 1 * u⁻¹ :=
        mul_le_mul_of_nonneg_right he (inv_nonneg.2 hu0.le)
    _ = u⁻¹ := one_mul _

/-- `2Ke^{-k} ≤ 3.72·10⁻⁸` for `k ≥ 20`, `K = RMF.mertensErrConst`. -/
lemma two_mul_mertensErrConst_exp_le {k : ℝ} (hk : 20 ≤ k) :
    2 * mertensErrConst * Real.exp (-k) ≤ 3.72 / 10 ^ 8 := by
  have hK := mertensErrConst_le
  have hK0 := mertensErrConst_nonneg
  have he : Real.exp (-k) ≤ 1 / 485000000 :=
    (Real.exp_le_exp.2 (by linarith : -k ≤ -20)).trans exp_neg_twenty_le_numeral
  have he0 := Real.exp_pos (-k)
  calc 2 * mertensErrConst * Real.exp (-k) ≤ 2 * 9.0028 * (1 / 485000000) :=
        mul_le_mul (by linarith) he he0.le (by norm_num)
    _ ≤ 3.72 / 10 ^ 8 := by norm_num

/-- **Mertens' block sums telescoped**: `∑_{m<d} S_m ≤ d + 3.72·10⁻⁸` for `k ≥ 20`, `σ ≥ 0` — one
Abel summation over the union of the blocks (`RMF.abs_sum_blockCosSum_sub_integral_le_mertens` at
`τ = 0`), in place of `(1 + 1/150000)d` block by block. -/
theorem sum_blockRpowSum_le_tel {k d : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) :
    ∑ m ∈ Finset.range d, blockRpowSum k σ m ≤ d + 3.72 / 10 ^ 8 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have h := abs_sum_blockCosSum_sub_integral_le_mertens (τ := 0) (σ := σ) (θ := k) (m₁ := 0)
    (M := d) (Nat.zero_le d) le_rfl hσ (by positivity)
  have hsum : ∑ m ∈ Finset.Ico 0 d, blockCosSum k σ 0 m
      = ∑ m ∈ Finset.range d, blockRpowSum k σ m := by
    rw [← Finset.range_eq_Ico]; exact Finset.sum_congr rfl fun m _ => blockCosSum_zero _ _ _
  rw [hsum] at h
  have hint := integral_exp_div_le_log (σ := σ) (Real.exp_pos ((((0 : ℕ) : ℝ) + k)))
    (Real.exp_le_exp.2 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d] :
      ((0 : ℕ) : ℝ) + k ≤ (d : ℝ) + k)) hσ
  rw [← Real.exp_sub, Real.log_exp] at hint
  have herr := two_mul_mertensErrConst_exp_le (k := ((0 : ℕ) : ℝ) + k) (by push_cast; linarith)
  have h2 := (abs_le.1 h).2
  have hz : mertensErrConst * 0 * ((d : ℝ) - ((0 : ℕ) : ℝ)) = 0 := by ring
  have e : (d : ℝ) + k - (((0 : ℕ) : ℝ) + k) = d := by push_cast; ring
  rw [e] at hint
  linarith

/-- **The prefix-mass exponent with Mertens telescoped**: `d + 3.72·10⁻⁸ + U_d`,
`U_d = RMF.hp2PrefixCosU d` (in place of `(1 + 1/150000)d + U_d`, which grows like `e^{d/150000}`
in the pair integral). -/
noncomputable def hp2PrefixExpM (d : ℕ) : ℝ := d + 3.72 / 10 ^ 8 + hp2PrefixCosU d

/-- **The prefix masses at `RMF.hp2PrefixExpM`**: for `k ≥ 20`, `h ∈ halfWindow k` and
`σe^{k+d+3} ≤ 1/200`, `∑_{m<d}(S_m + C_m(2h)) ≤ hp2PrefixExpM d`. -/
theorem hp2PrefixExpM_le {k d : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσd : σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) ≤ 1 / 200) :
    ∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
      ≤ hp2PrefixExpM d := by
  rw [Finset.sum_add_distrib]
  unfold hp2PrefixExpM
  linarith [sum_blockRpowSum_le_tel (d := d) hk hσ,
    sum_blockCosSum_two_mul_le_hp2PrefixCosU hk hh hσ hσd]

/-- **The doubled frequency over all `r ≥ 4` compared blocks**, with only `σe^{k+r} ≤ 1/200`:
`∑_{m<r}C_m(2h) ≤ -0.1005` (as `RMF.sum_blockCosSum_two_mul_le_hp2PrefixCosU` at `d ≥ 4`, the
damping `≤ 1/100`). -/
theorem sum_blockCosSum_two_mul_le_deep {k r : ℕ} {σ h : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hr : 4 ≤ r) :
    ∑ m ∈ Finset.range r, blockCosSum k σ (2 * h) m ≤ -0.1005 := by
  obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
  obtain ⟨hx₁, hx₂⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ2 : 2 * h ≤ 2 * Real.exp (-20) := by
    have := Real.exp_le_exp.2 (show -(k : ℝ) ≤ -20 by linarith)
    linarith [hh.2]
  have hT := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := 0) (j := r) hk hσ
    (by positivity) hτ2)
  have hD := damping_le_of_le (m₁ := 0) (j := r) hσ hσr (by omega)
  simp only [add_zero, Nat.cast_zero, zero_add] at hT hD
  obtain ⟨l2l, l2u⟩ := log_two_numerals
  have hΦ2 := cosExpAnti_two_cosExpTail_two_mem.2
  have hJ2 := hp2Phase_zero_two hx₁ hx₂
  have hd4 : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have e := cosExpInt_add (Real.log (2 * h) + k) 2 (r + (Real.log (2 * h) + k))
  have hJ := abs_le.1 (abs_cosExpInt_two_sub_le
    (by linarith : (2 : ℝ) ≤ r + (Real.log (2 * h) + k)))
  have hK := abs_le.1 ((abs_cosExpTail_le_phase (v := r + (Real.log (2 * h) + k))).2.2
    (by linarith))
  linarith [hT.2]

/-- **The deep prefix exponent**: over all `r ≥ 4` blocks,
`∑_{m<r}(S_m + C_m(2h)) ≤ r + 3.72·10⁻⁸ - 0.1005`. -/
theorem sum_prefix_le_deep {k r : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hr : 4 ≤ r) :
    ∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
      ≤ r + 3.72 / 10 ^ 8 - 0.1005 := by
  rw [Finset.sum_add_distrib]
  linarith [sum_blockRpowSum_le_tel (d := r) hk hσ,
    sum_blockCosSum_two_mul_le_deep hk hh hσ hσr hr]

/-! ### The trivial post bound -/

section Trivial

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- `1 ≤ (A₁ + c)(A₂ + c)/c²` for `A₁, A₂ ≥ 0 < c`. -/
lemma one_le_mul_div_sq {A₁ A₂ c : ℝ} (h₁ : 0 ≤ A₁) (h₂ : 0 ≤ A₂) (hc : 0 < c) :
    1 ≤ (A₁ + c) * (A₂ + c) / c ^ 2 := by
  rw [le_div_iff₀ (by positivity), one_mul]
  nlinarith

/-- **The trivial post bound**: the post tubes have two-fold tilted probability at most `1`, so
`RMF.IsHP2PostBound` holds with `C_post = (r - b)/c_h²` for any `c_h > 0` and `b < r` — better than
the regular post bound for short posts (`r - b ≲ 8`). -/
theorem isHP2PostBound_trivial (hX : IsRademacherPrimeValues X μ) {y k d r : ℕ}
    {σ h₁ h₂ ch : ℝ} (hσ : 0 ≤ σ) (hch : 0 < ch) (hbr : hp2PostStart d < r) :
    IsHP2PostBound X μ y k d r σ h₁ h₂ (((r - hp2PostStart d : ℕ) : ℝ) / ch ^ 2) ch := by
  intro z₁ z₂ _ _
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  have hN : (0 : ℝ) < ((r - hp2PostStart d : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < r - hp2PostStart d)
  have hA₁ := le_max_right (3 / 2 + 1 / 10 ^ 15 - z₁) 0
  have hA₂ := le_max_right (3 / 2 + 1 / 10 ^ 15 - z₂) 0
  have h1 := one_le_mul_div_sq hA₁ hA₂ hch
  refine measureReal_le_one.trans (h1.trans (le_of_eq ?_))
  field_simp

end Trivial

/-! ### The per-cell constants -/

/-- **The post bound's `n₀`**: `min(r - b, 1000)`, `b = hp2PostStart d`. -/
def hp2WinN (r d : ℕ) : ℕ := min (r - hp2PostStart d) 1000

/-- **The post constant of the cell's class** at `n₀`:
`C₀/√((0.495 - a₁/n₀)(0.495 - a₂/n₀))` (`RMF.isHP2PostBound_cell_zero` … `…_deep`). -/
noncomputable def hp2WinCpost (d j n : ℕ) : ℝ :=
  if d = 0 then hp2PostC00 j / √((0.495 - 0.8391 / n) * (0.495 - 0.8427 / n))
  else if d = 1 then hp2PostC01 j / √((0.495 - 0.6408 / n) * (0.495 - 0.405 / n))
  else if d = 2 then hp2PostC02 j / √((0.495 - 0.5624 / n) * (0.495 - 0.2574 / n))
  else if d = 3 then hp2PostC03 j / √((0.495 - 0.5624 / n) * (0.495 - 0.818 / n))
  else hp2PostC04 j / √((0.495 - 0.5624 / n) * (0.495 - 1.2572 / n))

/-- **The prefix's shift** `c = c_h + x`: the cell's post shift plus its bridge shift for `d ≤ 3`,
`max(c_h, 1.05)` for `d ≥ 4` (no bridge; `RMF.hp2PrefixBound` is a prefix bound for `c ≥ 1.05`). -/
noncomputable def hp2WinShift (d j : ℕ) : ℝ :=
  if d = 0 then hp2PostCh0 j + hp2BridgeX0 j
  else if d = 1 then hp2PostCh1 j + hp2BridgeX1 j
  else if d = 2 then hp2PostCh2 j + hp2BridgeX2 j
  else if d = 3 then hp2PostCh3 j + hp2BridgeX3 j
  else max (hp2PostCh4 j) 1.05

/-- **The prefix bound of the depth**: exact at `d = 0`, the better of the short-prefix bound
`RMF.hp2ShortPrefixBound` and `RMF.hp2PrefixBound` at `d = 1, 2`, `RMF.hp2PrefixBound` beyond. -/
noncomputable def hp2WinPrefix (d j : ℕ) : ℝ :=
  if d = 0 then (3 / 2 + 1 / 10 ^ 15 + hp2WinShift 0 j) ^ 2
  else if d ≤ 2 then min (hp2ShortPrefixBound d (hp2WinShift d j))
    (hp2PrefixBound d (hp2WinShift d j))
  else hp2PrefixBound d (hp2WinShift d j)

/-- **The regular per-cell constant**: the pair bound with the cell's numerals,
`hp2PairBoundOf C_post E_mass μ μ B B/(r - b)`. -/
noncomputable def hp2WinReg (r d j : ℕ) : ℝ :=
  hp2PairBoundOf (hp2WinCpost d j (hp2WinN r d)) (hp2CellMassExp d j r) (hp2PrefixExpM d)
    (hp2PrefixExpM d) (hp2WinPrefix d j) (hp2WinPrefix d j) / ((r - hp2PostStart d : ℕ) : ℝ)

/-- **The per-cell constant with the trivial post bound** (`d ≥ 4`): `C_post = (r - d)/1.05²`,
`c = 1.05`. -/
noncomputable def hp2WinTriv (r d j : ℕ) : ℝ :=
  hp2PairBoundOf (((r - hp2PostStart d : ℕ) : ℝ) / 1.05 ^ 2) (hp2CellMassExp d j r)
    (hp2PrefixExpM d) (hp2PrefixExpM d) (hp2PrefixBound d 1.05) (hp2PrefixBound d 1.05)
    / ((r - hp2PostStart d : ℕ) : ℝ)

/-- **HP2's per-cell constant** on cell `j` of depth `d`: the regular one for `d ≤ 3`, the better
of the regular and the trivial one for `d ≥ 4`. -/
noncomputable def hp2WinCell (r d j : ℕ) : ℝ :=
  if d < 4 then hp2WinReg r d j else min (hp2WinReg r d j) (hp2WinTriv r d j)

/-- **HP2's constant for the deep pairs** (`t ≤ e^{-(r-2)}`): the prefix alone at `M = r`,
`e^{r + 3.72·10⁻⁸ - 0.1005 + 5·10⁻²⁰}·hp2PrefixBound r 1.05/1.05²`. -/
noncomputable def hp2WinDeep (r : ℕ) : ℝ :=
  Real.exp (r + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20) * hp2PrefixBound r 1.05 / 1.05 ^ 2

/-! ### The tables' signs -/

/-- Class `0`'s numerals: `C₀, c_h, x ≥ 0` and `c_h + x ≥ 1.05`. -/
lemma hp2Win_tables_zero {j : ℕ} (hj : j < 40) :
    0 ≤ hp2PostC00 j ∧ 0 ≤ hp2PostCh0 j ∧ 0 ≤ hp2BridgeX0 j
      ∧ 1.05 ≤ hp2PostCh0 j + hp2BridgeX0 j := by
  interval_cases j <;> norm_num [hp2PostC00, hp2PostCh0, hp2BridgeX0]

/-- Class `1`'s numerals: `C₀, c_h, x ≥ 0` and `c_h + x ≥ 1.05`. -/
lemma hp2Win_tables_one {j : ℕ} (hj : j < 40) :
    0 ≤ hp2PostC01 j ∧ 0 ≤ hp2PostCh1 j ∧ 0 ≤ hp2BridgeX1 j
      ∧ 1.05 ≤ hp2PostCh1 j + hp2BridgeX1 j := by
  interval_cases j <;> norm_num [hp2PostC01, hp2PostCh1, hp2BridgeX1]

/-- Class `2`'s numerals: `C₀, c_h, x ≥ 0` and `c_h + x ≥ 1.05`. -/
lemma hp2Win_tables_two {j : ℕ} (hj : j < 40) :
    0 ≤ hp2PostC02 j ∧ 0 ≤ hp2PostCh2 j ∧ 0 ≤ hp2BridgeX2 j
      ∧ 1.05 ≤ hp2PostCh2 j + hp2BridgeX2 j := by
  interval_cases j <;> norm_num [hp2PostC02, hp2PostCh2, hp2BridgeX2]

/-- Class `3`'s numerals: `C₀, c_h, x ≥ 0` and `c_h + x ≥ 1.05`. -/
lemma hp2Win_tables_three {j : ℕ} (hj : j < 40) :
    0 ≤ hp2PostC03 j ∧ 0 ≤ hp2PostCh3 j ∧ 0 ≤ hp2BridgeX3 j
      ∧ 1.05 ≤ hp2PostCh3 j + hp2BridgeX3 j := by
  interval_cases j <;> norm_num [hp2PostC03, hp2PostCh3, hp2BridgeX3]

/-- Class `4`'s numerals: `C₀, c_h ≥ 0`. -/
lemma hp2Win_tables_four {j : ℕ} (hj : j < 40) : 0 ≤ hp2PostC04 j ∧ 0 ≤ hp2PostCh4 j := by
  interval_cases j <;> norm_num [hp2PostC04, hp2PostCh4]

/-- The post constant is nonnegative on the cells. -/
lemma hp2WinCpost_nonneg {d j : ℕ} (hj : j < 40) (n : ℕ) : 0 ≤ hp2WinCpost d j n := by
  unfold hp2WinCpost
  split_ifs
  · exact div_nonneg (hp2Win_tables_zero hj).1 (Real.sqrt_nonneg _)
  · exact div_nonneg (hp2Win_tables_one hj).1 (Real.sqrt_nonneg _)
  · exact div_nonneg (hp2Win_tables_two hj).1 (Real.sqrt_nonneg _)
  · exact div_nonneg (hp2Win_tables_three hj).1 (Real.sqrt_nonneg _)
  · exact div_nonneg (hp2Win_tables_four hj).1 (Real.sqrt_nonneg _)

/-- The prefix's shift is at least `1.05` on the cells. -/
lemma le_hp2WinShift {d j : ℕ} (hj : j < 40) : 1.05 ≤ hp2WinShift d j := by
  unfold hp2WinShift
  split_ifs
  · exact (hp2Win_tables_zero hj).2.2.2
  · exact (hp2Win_tables_one hj).2.2.2
  · exact (hp2Win_tables_two hj).2.2.2
  · exact (hp2Win_tables_three hj).2.2.2
  · exact le_max_right _ _

/-- The prefix bound is nonnegative on the cells. -/
lemma hp2WinPrefix_nonneg {d j : ℕ} (hj : j < 40) : 0 ≤ hp2WinPrefix d j := by
  have hc := le_hp2WinShift (d := d) hj
  have hc0 : (0 : ℝ) ≤ hp2WinShift d j := by linarith
  unfold hp2WinPrefix
  split_ifs
  · positivity
  · refine le_min ?_ (hp2PrefixBound_nonneg d hc0)
    unfold hp2ShortPrefixBound hp2ShortPrefixBoundOf
    positivity
  · exact hp2PrefixBound_nonneg d hc0

/-- `hp2PairBoundOf C E μ μ B B ≥ 0` for `C, B ≥ 0`. -/
lemma hp2PairBoundOf_nonneg {C E μ₁ μ₂ B₁ B₂ : ℝ} (hC : 0 ≤ C) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    0 ≤ hp2PairBoundOf C E μ₁ μ₂ B₁ B₂ := by
  unfold hp2PairBoundOf
  positivity

/-- The per-cell constant is nonnegative. -/
lemma hp2WinCell_nonneg (r d : ℕ) {j : ℕ} (hj : j < 40) : 0 ≤ hp2WinCell r d j := by
  have hreg : 0 ≤ hp2WinReg r d j :=
    div_nonneg (hp2PairBoundOf_nonneg (hp2WinCpost_nonneg hj _) (hp2WinPrefix_nonneg hj)
      (hp2WinPrefix_nonneg hj)) (Nat.cast_nonneg _)
  have htriv : 0 ≤ hp2WinTriv r d j :=
    div_nonneg (hp2PairBoundOf_nonneg (by positivity)
      (hp2PrefixBound_nonneg d (by norm_num)) (hp2PrefixBound_nonneg d (by norm_num)))
      (Nat.cast_nonneg _)
  unfold hp2WinCell
  split_ifs
  · exact hreg
  · exact le_min hreg htriv

/-- The deep constant is nonnegative. -/
lemma hp2WinDeep_nonneg (r : ℕ) : 0 ≤ hp2WinDeep r := by
  have := hp2PrefixBound_nonneg r (c := 1.05) (by norm_num)
  unfold hp2WinDeep
  positivity

/-! ### The pair bound on a cell -/

section PairCell

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The post bound's `n₀` is admissible: `3 ≤ n₀` and `b + n₀ ≤ r` once `b + 3 ≤ r`. -/
lemma hp2WinN_spec {r d : ℕ} (h : hp2PostStart d + 3 ≤ r) :
    3 ≤ hp2WinN r d ∧ hp2PostStart d + hp2WinN r d ≤ r := by
  unfold hp2WinN
  constructor <;> omega

/-- The post start is `4` or `d` past depth `3`, at most `4` below. -/
lemma hp2PostStart_add_three_le {r d : ℕ} (hdr : d + 3 ≤ r) (hr : 7 ≤ r) :
    hp2PostStart d + 3 ≤ r := by
  unfold hp2PostStart
  split_ifs <;> omega

/-- **The pair bound on cell `j` of depth `d ≤ r - 3`**: for `k ≥ 20`, heights in the window,
`σe^{k+r} ≤ 1/200`, the tilt cutoff `y ≥ c_r`, a pair in cell `j < 40` of depth `d` and `r ≥ 7`,
`E[1_{H₁∩H₂}‖F(s₁)‖²‖F(s₂)‖²] ≤ E‖F(s₁)‖²E‖F(s₂)‖²·hp2WinCell r d j` (the per-cell discharges of
`RMF.integral_hp1Tube_inter_le_hp2PairBoundOf`, the prefix masses by `RMF.hp2PrefixExpM_le`). -/
theorem integral_pair_le_hp2WinCell (hX : IsRademacherPrimeValues X μ) {k r y d j : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40) (hcell : IsHP2UCell k d j h₁ h₂)
    (hdr : d + 3 ≤ r) (hr : 7 ≤ r) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * hp2WinCell r d j := by
  have hbr3 := hp2PostStart_add_three_le hdr hr
  obtain ⟨hn₀, hn₀r⟩ := hp2WinN_spec hbr3
  have hbr : hp2PostStart d ≤ r := by omega
  have hdr' : (d : ℝ) + 3 ≤ r := by exact_mod_cast hdr
  have hσd : σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) ≤ 1 / 200 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hσ) hσr
  have hσd' : σ * Real.exp ((k : ℝ) + d) ≤ 1 / 200 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hσ) hσd
  have hyd : ⌊blockScale k d⌋₊ + 1 ≤ y := (cut_mono k (show d ≤ r by omega)).trans hyr
  have hmass := hp2CellMass_le hk hh₁ hh₂ hσ hσr hj hcell hdr
  have hμ₁ := hp2PrefixExpM_le hk hh₁ hσ hσd
  have hμ₂ := hp2PrefixExpM_le hk hh₂ hσ hσd
  have hE0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ) :=
    mul_nonneg (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
  have hzero : ∀ {h : ℝ} (d' : ℕ), hp2PostStart d' = d' →
      ∑ i ∈ Finset.range (hp2PostStart d' - d'), pairVarH X μ y k σ h₁ h₂ h (i + d')
        + (∑ i ∈ Finset.range (hp2PostStart d' - d'),
          (pairMeanH X μ y k σ h₁ h₂ h (i + d') - windowMeanH X μ y k σ h (i + d'))) ^ 2
        ≤ (0 : ℝ) ^ 2 := by
    intro h d' hb
    rw [hb, Nat.sub_self]
    simp
  -- the regular bound, for every depth
  have hreg : ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * hp2WinReg r d j := by
    rw [hp2WinReg, ← mul_div_assoc]
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ 4 ≤ d) with h0 | h1 | h2 | h3 | h4
    · subst h0
      obtain ⟨hC, hch, hx, hc⟩ := hp2Win_tables_zero hj
      have hpost := isHP2PostBound_cell_zero hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r
      have hB : ∀ {h : ℝ}, IsHP2PrefixBound X μ y k 0 σ h (hp2PostCh0 j + hp2BridgeX0 j)
          (hp2WinPrefix 0 j) := fun {h} => by
        have := isHP2PrefixBound_zero hX y k (h := h) hσ (c := hp2PostCh0 j + hp2BridgeX0 j)
          (by linarith)
        simpa [hp2WinPrefix, hp2WinShift] using this
      have e := integral_hp1Tube_inter_le_hp2PairBoundOf hX hk hσ hyr hbr hpost
        (div_nonneg hC (Real.sqrt_nonneg _)) hch hx
        (hp2CellBridge_zero_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inl rfl))
        (hp2CellBridge_zero_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inr rfl))
        hmass hμ₁ hμ₂ hB hB
      simpa [hp2WinCpost] using e
    · subst h1
      obtain ⟨hC, hch, hx, hc⟩ := hp2Win_tables_one hj
      have hpost := isHP2PostBound_cell_one hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r
      have hB : ∀ {h : ℝ}, h ∈ halfWindow k → IsHP2PrefixBound X μ y k 1 σ h
          (hp2PostCh1 j + hp2BridgeX1 j) (hp2WinPrefix 1 j) := fun {h} hh => by
        have := (isHP2PrefixBound_hp2ShortPrefixBound hX hk hh hσ hσd hyd (by linarith)).min
          (isHP2PrefixBound_hp2PrefixBound hX hk hh hσ hσd' hyd hc)
        simpa [hp2WinPrefix, hp2WinShift] using this
      have e := integral_hp1Tube_inter_le_hp2PairBoundOf hX hk hσ hyr hbr hpost
        (div_nonneg hC (Real.sqrt_nonneg _)) hch hx
        (hp2CellBridge_one_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inl rfl))
        (hp2CellBridge_one_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inr rfl))
        hmass hμ₁ hμ₂ (hB hh₁) (hB hh₂)
      simpa [hp2WinCpost] using e
    · subst h2
      obtain ⟨hC, hch, hx, hc⟩ := hp2Win_tables_two hj
      have hpost := isHP2PostBound_cell_two hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r
      have hB : ∀ {h : ℝ}, h ∈ halfWindow k → IsHP2PrefixBound X μ y k 2 σ h
          (hp2PostCh2 j + hp2BridgeX2 j) (hp2WinPrefix 2 j) := fun {h} hh => by
        have := (isHP2PrefixBound_hp2ShortPrefixBound hX hk hh hσ hσd hyd (by linarith)).min
          (isHP2PrefixBound_hp2PrefixBound hX hk hh hσ hσd' hyd hc)
        simpa [hp2WinPrefix, hp2WinShift] using this
      have e := integral_hp1Tube_inter_le_hp2PairBoundOf hX hk hσ hyr hbr hpost
        (div_nonneg hC (Real.sqrt_nonneg _)) hch hx
        (hp2CellBridge_two_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inl rfl))
        (hp2CellBridge_two_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inr rfl))
        hmass hμ₁ hμ₂ (hB hh₁) (hB hh₂)
      simpa [hp2WinCpost] using e
    · subst h3
      obtain ⟨hC, hch, hx, hc⟩ := hp2Win_tables_three hj
      have hpost := isHP2PostBound_cell_three hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r
      have hB : ∀ {h : ℝ}, h ∈ halfWindow k → IsHP2PrefixBound X μ y k 3 σ h
          (hp2PostCh3 j + hp2BridgeX3 j) (hp2WinPrefix 3 j) := fun {h} hh => by
        have := isHP2PrefixBound_hp2PrefixBound hX hk hh hσ hσd' hyd hc
        simpa [hp2WinPrefix, hp2WinShift] using this
      have e := integral_hp1Tube_inter_le_hp2PairBoundOf hX hk hσ hyr hbr hpost
        (div_nonneg hC (Real.sqrt_nonneg _)) hch hx
        (hp2CellBridge_three_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inl rfl))
        (hp2CellBridge_three_le hX hk hh₁ hh₂ hσ hσr hyr hj hcell hn₀ hn₀r (Or.inr rfl))
        hmass hμ₁ hμ₂ (hB hh₁) (hB hh₂)
      simpa [hp2WinCpost] using e
    · obtain ⟨hC, hch⟩ := hp2Win_tables_four hj
      have hb : hp2PostStart d = d := by simp [hp2PostStart, h4]
      have hn₀r' : d + hp2WinN r d ≤ r := by
        have h' := hn₀r
        rw [hb] at h'
        exact h'
      have hpost := (isHP2PostBound_cell_deep hX hk hh₁ hh₂ hσ hσr hyr h4 hj hcell hn₀
        hn₀r').mono le_rfl (le_max_left (hp2PostCh4 j) 1.05)
        (div_nonneg hC (Real.sqrt_nonneg _)) hch
      have hc : (1.05 : ℝ) ≤ max (hp2PostCh4 j) 1.05 + 0 := by
        rw [add_zero]; exact le_max_right _ _
      have hB : ∀ {h : ℝ}, h ∈ halfWindow k → IsHP2PrefixBound X μ y k d σ h
          (max (hp2PostCh4 j) 1.05 + 0) (hp2WinPrefix d j) := fun {h} hh => by
        have := isHP2PrefixBound_hp2PrefixBound hX hk hh hσ hσd' hyd hc
        have hd0 : d ≠ 0 := by omega
        have hd1 : ¬ d ≤ 2 := by omega
        have hd1' : d ≠ 1 := by omega
        have hd2 : d ≠ 2 := by omega
        have hd3 : d ≠ 3 := by omega
        simpa [hp2WinPrefix, hp2WinShift, hd0, hd1, hd1', hd2, hd3] using this
      have e := integral_hp1Tube_inter_le_hp2PairBoundOf hX hk hσ hyr hbr hpost
        (div_nonneg hC (Real.sqrt_nonneg _)) (le_trans hch (le_max_left _ _)) le_rfl
        (hzero d hb) (hzero d hb) hmass hμ₁ hμ₂ (hB hh₁) (hB hh₂)
      have hd0 : d ≠ 0 := by omega
      have hd1 : d ≠ 1 := by omega
      have hd2 : d ≠ 2 := by omega
      have hd3 : d ≠ 3 := by omega
      simpa [hp2WinCpost, hd0, hd1, hd2, hd3] using e
  unfold hp2WinCell
  split_ifs with hd4
  · exact hreg
  -- the trivial post bound for `d ≥ 4`
  have h4 : 4 ≤ d := by omega
  have hb : hp2PostStart d = d := by simp [hp2PostStart, h4]
  have hpost := isHP2PostBound_trivial (y := y) (k := k) (d := d) (r := r) (h₁ := h₁) (h₂ := h₂)
    hX hσ (ch := 1.05) (by norm_num) (by omega)
  have hc : (1.05 : ℝ) ≤ 1.05 + 0 := by norm_num
  have hB : ∀ {h : ℝ}, h ∈ halfWindow k → IsHP2PrefixBound X μ y k d σ h (1.05 + 0)
      (hp2PrefixBound d 1.05) := fun {h} hh => by
    have := isHP2PrefixBound_hp2PrefixBound hX hk hh hσ hσd' hyd hc
    simpa using this
  have e := integral_hp1Tube_inter_le_hp2PairBoundOf hX hk hσ hyr hbr hpost (by positivity)
    (by norm_num) le_rfl (hzero d hb) (hzero d hb) hmass hμ₁ hμ₂ (hB hh₁) (hB hh₂)
  have htriv : ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * hp2WinTriv r d j := by
    rw [hp2WinTriv, ← mul_div_assoc]
    exact e
  calc _ ≤ _ := le_min hreg htriv
    _ = _ := by rw [mul_min_of_nonneg _ _ hE0]

/-- **The pair bound for the deep pairs**: for every pair in the window (`h₁ = h₂` included) and
`r ≥ 4`, `E[1_{H₁∩H₂}‖F(s₁)‖²‖F(s₂)‖²] ≤ E‖F(s₁)‖²E‖F(s₂)‖²·hp2WinDeep r`
(`RMF.integral_hp1Tube_inter_le_deep` at `c = 1.05`, the exponents by `RMF.sum_prefix_le_deep`). -/
theorem integral_pair_le_hp2WinDeep (hX : IsRademacherPrimeValues X μ) {k r y : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hr : 4 ≤ r) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * hp2WinDeep r := by
  have h := integral_hp1Tube_inter_le_deep hX hk hh₁ hh₂ hσ hσr hyr (c := 1.05) le_rfl
  refine h.trans ?_
  have e₁ := sum_prefix_le_deep hk hh₁ hσ hσr hr
  have e₂ := sum_prefix_le_deep hk hh₂ hσ hσr hr
  set M : ℝ := (r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20 with hM
  have x₁ := Real.exp_le_exp.2 (by linarith : ∑ m ∈ Finset.range r,
    (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m) + 5 / 10 ^ 20 ≤ M)
  have x₂ := Real.exp_le_exp.2 (by linarith : ∑ m ∈ Finset.range r,
    (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m) + 5 / 10 ^ 20 ≤ M)
  have hP := hp2PrefixBound_nonneg r (c := 1.05) (by norm_num)
  have hE0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ) :=
    mul_nonneg (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
  have hmean : (Real.exp (∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
        + 5 / 10 ^ 20)
      + Real.exp (∑ m ∈ Finset.range r, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
        + 5 / 10 ^ 20)) / 2 ≤ Real.exp M := by linarith
  unfold hp2WinDeep
  rw [← hM]
  calc _ = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * ((Real.exp (∑ m ∈ Finset.range r,
              (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m) + 5 / 10 ^ 20)
            + Real.exp (∑ m ∈ Finset.range r,
              (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m) + 5 / 10 ^ 20)) / 2
          * (hp2PrefixBound r 1.05 / 1.05 ^ 2)) := by ring
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmean (by positivity)) hE0

end PairCell

/-! ### The cells -/

/-- **The cells' ends** `e^{-i/40}`: cell `i = 40d + j` is `t ∈ (e^{-(i+1)/40}, e^{-i/40}]`. -/
noncomputable def hp2CellEnd (i : ℕ) : ℝ := Real.exp (-((i : ℝ) / 40))

/-- The cells' ends decrease. -/
lemma hp2CellEnd_anti {i i' : ℕ} (h : i ≤ i') : hp2CellEnd i' ≤ hp2CellEnd i := by
  unfold hp2CellEnd
  refine Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right ?_ (by norm_num)))
  exact_mod_cast h

/-- **Every `t ∈ (e^{-N/40}, 1]` is in a cell `i < N`**: `i = ⌊-40 log t⌋`. -/
lemma exists_cell_of_lt {N : ℕ} {t : ℝ} (ht : hp2CellEnd N < t) (ht1 : t ≤ 1) :
    ∃ i < N, hp2CellEnd (i + 1) < t ∧ t ≤ hp2CellEnd i := by
  have ht0 : 0 < t := lt_of_le_of_lt (Real.exp_pos _).le ht
  have hl : 0 ≤ -40 * Real.log t := by
    have := Real.log_nonpos ht0.le ht1
    linarith
  set i := ⌊-40 * Real.log t⌋₊ with hi
  have h1 : (i : ℝ) ≤ -40 * Real.log t := Nat.floor_le hl
  have h2 : -40 * Real.log t < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hup : t ≤ hp2CellEnd i := by
    unfold hp2CellEnd
    rw [← Real.exp_log ht0]
    exact Real.exp_le_exp.2 (by linarith)
  have hlo : hp2CellEnd (i + 1) < t := by
    unfold hp2CellEnd
    rw [← Real.exp_log ht0]
    refine Real.exp_lt_exp.2 ?_
    push_cast
    linarith
  refine ⟨i, ?_, hlo, hup⟩
  by_contra hN
  exact absurd (lt_of_lt_of_le ht (hup.trans (hp2CellEnd_anti (not_lt.1 hN)))) (lt_irrefl _)

/-- **The cell of a pair**: `t = |h₁ - h₂|e^k ∈ (e^{-(40d+j+1)/40}, e^{-(40d+j)/40}]` puts the
pair in `RMF.IsHP2UCell k d j`. -/
lemma isHP2UCell_of_mem {k d j : ℕ} {h₁ h₂ : ℝ}
    (h : |h₁ - h₂| * Real.exp (k : ℝ)
      ∈ Set.Ioc (hp2CellEnd (40 * d + j + 1)) (hp2CellEnd (40 * d + j))) :
    IsHP2UCell k d j h₁ h₂ := by
  have hsplit : |h₁ - h₂| * Real.exp ((k : ℝ) + d) = |h₁ - h₂| * Real.exp (k : ℝ) * Real.exp d := by
    rw [Real.exp_add]; ring
  have e1 : hp2CellEnd (40 * d + j + 1) * Real.exp d = Real.exp (-(((j : ℝ) + 1) / 40)) := by
    unfold hp2CellEnd
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have e2 : hp2CellEnd (40 * d + j) * Real.exp d = Real.exp (-((j : ℝ) / 40)) := by
    unfold hp2CellEnd
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hd := Real.exp_pos (d : ℝ)
  unfold IsHP2UCell
  rw [hsplit, ← e1, ← e2]
  exact ⟨mul_le_mul_of_nonneg_right h.1.le hd.le, mul_le_mul_of_nonneg_right h.2 hd.le⟩

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- A pair in the window has `|h₁ - h₂|e^k ≤ 1 - e^{-1}`. -/
lemma abs_sub_mul_exp_le_of_mem_halfWindow {k : ℕ} {h₁ h₂ : ℝ} (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) : |h₁ - h₂| * Real.exp (k : ℝ) ≤ 1 - Real.exp (-1) := by
  obtain ⟨a₁, b₁⟩ := hh₁
  obtain ⟨a₂, b₂⟩ := hh₂
  have hL : |h₁ - h₂| ≤ Real.exp (-(k : ℝ)) - Real.exp (-((k : ℝ) + 1)) := by
    rw [abs_le]; constructor <;> linarith
  have e1 : Real.exp (-(k : ℝ)) * Real.exp (k : ℝ) = 1 := by
    rw [← Real.exp_add]; simp
  have e2 : Real.exp (-((k : ℝ) + 1)) * Real.exp (k : ℝ) = Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |h₁ - h₂| * Real.exp (k : ℝ)
      ≤ (Real.exp (-(k : ℝ)) - Real.exp (-((k : ℝ) + 1))) * Real.exp (k : ℝ) :=
        mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
    _ = 1 - Real.exp (-1) := by rw [sub_mul, e1, e2]

end Step

end RMF
