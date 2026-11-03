/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2PostFloor
import RMF.UniformLower.HP1Grid.Data
import RMF.UniformLower.HP2PairCells.Anchors

/-!
# The partial integrals of `cos(e^v)`, for HP2's cells

The tools behind the per-cell bounds of `RMF/UniformLower/HP2PairCells.lean`.

* **The partial integral** `J(a, b) = ∫_a^b cos(e^v) dv` (`RMF.cosExpInt`): the telescoped block
  cosine sums are its values (`RMF.abs_sum_blockCosSum_sub_cosExpInt`, error
  `3.16·10⁻⁶ + 2σ(e^{M+k} - e^{m₁+k})`).
* **Sign pieces and corners**: between the zeros `z_n = log((2n+1)π/2)` (`RMF.hp2Z`) of `cos(e^v)`
  its integrand has one sign, so over a box of endpoints the extremes of `J` are at corners
  (`RMF.cosExpInt_le_corner`, `RMF.le_cosExpInt_corner`); the corners' values are the anchors of
  `RMF/UniformLower/HP2PairCells/Anchors.lean` (`RMF.cosExpInt_mem_anti`, `…_across`).
* **The pushes' cores**: `J(a, T) ≥ min(0, J(a, z₁))` for all `T ≥ a`
  (`RMF.push_core_z1`), `≥ min(0, J(a, z₃))` from `a ∈ [z₁, 2]` (`RMF.push_core_z3`).
* **The phases** `x = log τ + k ∈ [log 2 - 1, log 2]` of the window's sum and doubled frequencies
  (`RMF.log_add_mem_of_window`) and the partial integrals from `d + x` over them.
* **The cells**: `RMF.IsHP2UCell k d j h₁ h₂`, the fractional depth `u ∈ [j/40, (j+1)/40]`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The partial integrals of `cos(e^v)`

`J(a, b) = ∫_a^b cos(e^v) dv` (`RMF.cosExpInt`): the telescoped block cosine sums are its values
(`∑_{m₁≤m<M} C_m(τ) ≈ J(m₁ + ξ, M + ξ)`, `ξ = log τ + k`,
`RMF.abs_sum_blockCosSum_sub_integral_cos_exp_le`).  Between the zeros `z_n = log((2n+1)π/2)` of
`cos(e^v)` its integrand has one sign, so over a cell of endpoints its extremes are at the cell's
corners (`RMF.cosExpInt_le_corner`); the corners' values are Taylor's antiderivative
`RMF.cosExpAnti` below `2` and the asymptotic `RMF.cosExpTail` above. -/

section CosExpInt

/-- **The partial integral** `J(a, b) = ∫_a^b cos(e^v) dv`. -/
noncomputable def cosExpInt (a b : ℝ) : ℝ := ∫ v in a..b, Real.cos (Real.exp v)

lemma intervalIntegrable_cos_exp (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => Real.cos (Real.exp v)) MeasureTheory.volume a b :=
  (by fun_prop : Continuous fun v : ℝ => Real.cos (Real.exp v)).intervalIntegrable a b

/-- `J(a, b) + J(b, c) = J(a, c)`. -/
lemma cosExpInt_add (a b c : ℝ) : cosExpInt a b + cosExpInt b c = cosExpInt a c :=
  intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_cos_exp a b)
    (intervalIntegrable_cos_exp b c)

lemma cosExpInt_self (a : ℝ) : cosExpInt a a = 0 := intervalIntegral.integral_same

/-- `J(b, a) = -J(a, b)`. -/
lemma cosExpInt_symm (a b : ℝ) : cosExpInt b a = -cosExpInt a b :=
  intervalIntegral.integral_symm a b

/-- `cos(e^v) ≥ 0` for `e^v ∈ [(2n - 1/2)π, (2n + 1/2)π]`. -/
lemma cos_exp_nonneg_of_exp {v : ℝ} (n : ℕ) (h1 : (2 * n - 1 / 2) * π ≤ Real.exp v)
    (h2 : Real.exp v ≤ (2 * n + 1 / 2) * π) : 0 ≤ Real.cos (Real.exp v) := by
  rw [← Real.cos_sub_nat_mul_two_pi (Real.exp v) n]
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)

/-- `cos(e^v) ≤ 0` for `e^v ∈ [(2n + 1/2)π, (2n + 3/2)π]`. -/
lemma cos_exp_nonpos_of_exp {v : ℝ} (n : ℕ) (h1 : (2 * n + 1 / 2) * π ≤ Real.exp v)
    (h2 : Real.exp v ≤ (2 * n + 3 / 2) * π) : Real.cos (Real.exp v) ≤ 0 := by
  rw [← Real.cos_sub_nat_mul_two_pi (Real.exp v) n]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)

/-- `J(p, q) ≥ 0` where `e^v ∈ [(2n - 1/2)π, (2n + 1/2)π]` on `[p, q]`. -/
lemma cosExpInt_nonneg_of_exp {p q : ℝ} (n : ℕ) (hpq : p ≤ q)
    (hp : (2 * n - 1 / 2) * π ≤ Real.exp p) (hq : Real.exp q ≤ (2 * n + 1 / 2) * π) :
    0 ≤ cosExpInt p q :=
  intervalIntegral.integral_nonneg hpq fun _ hv => cos_exp_nonneg_of_exp n
    (hp.trans (Real.exp_le_exp.2 hv.1)) ((Real.exp_le_exp.2 hv.2).trans hq)

/-- `J(p, q) ≤ 0` where `e^v ∈ [(2n + 1/2)π, (2n + 3/2)π]` on `[p, q]`. -/
lemma cosExpInt_nonpos_of_exp {p q : ℝ} (n : ℕ) (hpq : p ≤ q)
    (hp : (2 * n + 1 / 2) * π ≤ Real.exp p) (hq : Real.exp q ≤ (2 * n + 3 / 2) * π) :
    cosExpInt p q ≤ 0 := by
  have h := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume)
    (f := fun v => -Real.cos (Real.exp v)) hpq
    fun _ hv => neg_nonneg.2 (cos_exp_nonpos_of_exp n
      (hp.trans (Real.exp_le_exp.2 hv.1)) ((Real.exp_le_exp.2 hv.2).trans hq))
  rw [intervalIntegral.integral_neg] at h
  unfold cosExpInt
  linarith

/-- **The corners, from above**: `J(a, b) ≤ J(a', b')` once `J(a', a) ≥ 0` and `J(b, b') ≥ 0`. -/
lemma cosExpInt_le_corner {a b a' b' : ℝ} (ha : 0 ≤ cosExpInt a' a) (hb : 0 ≤ cosExpInt b b') :
    cosExpInt a b ≤ cosExpInt a' b' := by
  have h1 := cosExpInt_add a' a b
  have h2 := cosExpInt_add a' b b'
  linarith

/-- **The corners, from below**: `J(a', b') ≤ J(a, b)` once `J(a', a) ≤ 0` and `J(b, b') ≤ 0`. -/
lemma le_cosExpInt_corner {a b a' b' : ℝ} (ha : cosExpInt a' a ≤ 0) (hb : cosExpInt b b' ≤ 0) :
    cosExpInt a' b' ≤ cosExpInt a b := by
  have h1 := cosExpInt_add a' a b
  have h2 := cosExpInt_add a' b b'
  linarith

/-- `J(a, b)` by Taylor's antiderivative below `2`
(`RMF.abs_integral_cos_exp_sub_cosExpAnti_le`). -/
lemma abs_cosExpInt_sub_anti_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 2) :
    |cosExpInt a b - (cosExpAnti b - cosExpAnti a)| ≤ (b - a) / 10 ^ 6 :=
  abs_integral_cos_exp_sub_cosExpAnti_le hab hb

/-- `J(a, b)` by the asymptotic antiderivative
(`RMF.abs_integral_cos_exp_sub_cosExpTail_le`). -/
lemma abs_cosExpInt_sub_tail_le {a b : ℝ} (hab : a ≤ b) :
    |cosExpInt a b - (cosExpTail b - cosExpTail a)| ≤ 6 * Real.exp (-(4 * a)) :=
  abs_integral_cos_exp_sub_cosExpTail_le hab

/-- `6e^{-8} ≤ 0.002013`. -/
lemma six_mul_exp_neg_eight_le' : 6 * Real.exp (-8) ≤ 0.002013 := by
  interval_decide (trust := kernel)

/-- `J(2, b)` for `b ≥ 2`: within `0.002013` of `Φ(b) - Φ(2)`. -/
lemma abs_cosExpInt_two_sub_le {b : ℝ} (hb : 2 ≤ b) :
    |cosExpInt 2 b - (cosExpTail b - cosExpTail 2)| ≤ 0.002013 := by
  have h := abs_cosExpInt_sub_tail_le hb
  rw [show -(4 * (2 : ℝ)) = -8 by norm_num] at h
  exact h.trans six_mul_exp_neg_eight_le'

/-- `cos(e^v) ≥ 0` up to `z₀ = log(π/2)`: `J(p, q) ≥ 0` for `p ≤ q ≤ z₀`. -/
lemma cosExpInt_nonneg_le_z0 {p q : ℝ} (hpq : p ≤ q) (hq : q ≤ hp2Z 0) : 0 ≤ cosExpInt p q := by
  refine cosExpInt_nonneg_of_exp 0 hpq (by nlinarith [Real.exp_pos p, Real.pi_pos]) ?_
  have h := (Real.exp_le_exp.2 hq).trans_eq (exp_hp2Z 0)
  push_cast at h ⊢
  linarith

/-- `J(p, q) ≥ 0` for `z_{2m-1} ≤ p ≤ q ≤ z_{2m}`, `m ≥ 1`. -/
lemma cosExpInt_nonneg_z {p q : ℝ} (m : ℕ) (hm : 1 ≤ m) (hpq : p ≤ q)
    (hp : hp2Z (2 * m - 1) ≤ p) (hq : q ≤ hp2Z (2 * m)) : 0 ≤ cosExpInt p q := by
  refine cosExpInt_nonneg_of_exp m hpq ?_ ?_
  · have h := (exp_hp2Z (2 * m - 1)).symm.trans_le (Real.exp_le_exp.2 hp)
    have hc : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at h
    linarith
  · have h := (Real.exp_le_exp.2 hq).trans_eq (exp_hp2Z (2 * m))
    push_cast at h
    linarith

/-- `J(p, q) ≤ 0` for `z_{2m} ≤ p ≤ q ≤ z_{2m+1}`. -/
lemma cosExpInt_nonpos_z {p q : ℝ} (m : ℕ) (hpq : p ≤ q) (hp : hp2Z (2 * m) ≤ p)
    (hq : q ≤ hp2Z (2 * m + 1)) : cosExpInt p q ≤ 0 := by
  refine cosExpInt_nonpos_of_exp m hpq ?_ ?_
  · have h := (exp_hp2Z (2 * m)).symm.trans_le (Real.exp_le_exp.2 hp)
    push_cast at h
    linarith
  · have h := (Real.exp_le_exp.2 hq).trans_eq (exp_hp2Z (2 * m + 1))
    push_cast at h
    linarith

/-- `J(p, q) ≤ 0` on `[z₀, z₁]`. -/
lemma cosExpInt_nonpos_z01 {p q : ℝ} (hpq : p ≤ q) (hp : hp2Z 0 ≤ p) (hq : q ≤ hp2Z 1) :
    cosExpInt p q ≤ 0 :=
  cosExpInt_nonpos_z 0 hpq (by simpa using hp) (by simpa using hq)

/-- `J(p, q) ≥ 0` on `[z₁, z₂]`. -/
lemma cosExpInt_nonneg_z12 {p q : ℝ} (hpq : p ≤ q) (hp : hp2Z 1 ≤ p) (hq : q ≤ hp2Z 2) :
    0 ≤ cosExpInt p q :=
  cosExpInt_nonneg_z 1 le_rfl hpq (by simpa using hp) (by simpa using hq)

/-- `J(p, q) ≤ 0` on `[z₂, z₃]`. -/
lemma cosExpInt_nonpos_z23 {p q : ℝ} (hpq : p ≤ q) (hp : hp2Z 2 ≤ p) (hq : q ≤ hp2Z 3) :
    cosExpInt p q ≤ 0 :=
  cosExpInt_nonpos_z 1 hpq (by simpa using hp) (by simpa using hq)

/-- `J(p, q) ≥ 0` on `[z₃, z₄]`. -/
lemma cosExpInt_nonneg_z34 {p q : ℝ} (hpq : p ≤ q) (hp : hp2Z 3 ≤ p) (hq : q ≤ hp2Z 4) :
    0 ≤ cosExpInt p q :=
  cosExpInt_nonneg_z 2 (by norm_num) hpq (by simpa using hp) (by simpa using hq)

/-- `J(p, q) ≤ 0` on `[z₄, z₅]`. -/
lemma cosExpInt_nonpos_z45 {p q : ℝ} (hpq : p ≤ q) (hp : hp2Z 4 ≤ p) (hq : q ≤ hp2Z 5) :
    cosExpInt p q ≤ 0 :=
  cosExpInt_nonpos_z 2 hpq (by simpa using hp) (by simpa using hq)

/-- `J(q, p) ≤ 0` from `0 ≤ J(p, q)`. -/
lemma cosExpInt_nonpos_rev {p q : ℝ} (h : 0 ≤ cosExpInt p q) : cosExpInt q p ≤ 0 := by
  rw [cosExpInt_symm]; linarith

/-- `0 ≤ J(q, p)` from `J(p, q) ≤ 0`. -/
lemma cosExpInt_nonneg_rev {p q : ℝ} (h : cosExpInt p q ≤ 0) : 0 ≤ cosExpInt q p := by
  rw [cosExpInt_symm]; linarith

/-- The zeros increase. -/
lemma hp2Z_mono {m n : ℕ} (h : m ≤ n) : hp2Z m ≤ hp2Z n := by
  unfold hp2Z
  refine Real.log_le_log (by positivity) ?_
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  have := Real.pi_pos
  nlinarith

/-- `0 ≤ z₀`, `z₁ ≤ 2 ≤ z₂`: `π/2 ≥ 1`, `3π/2 ≤ e² ≤ 5π/2`. -/
lemma hp2Z_bounds : 0 ≤ hp2Z 0 ∧ hp2Z 1 ≤ 2 ∧ 2 ≤ hp2Z 2 := by
  have he₁ : (7.389 : ℝ) ≤ Real.exp 2 := by interval_decide (trust := kernel)
  have he₂ : Real.exp 2 ≤ (7.39 : ℝ) := by interval_decide (trust := kernel)
  have hπ₁ := Real.pi_gt_three
  have hπ₂ := Real.pi_lt_d2
  refine ⟨?_, ?_, ?_⟩
  · unfold hp2Z
    exact Real.log_nonneg (by push_cast; linarith)
  · unfold hp2Z
    rw [Real.log_le_iff_le_exp (by positivity)]
    push_cast
    linarith
  · unfold hp2Z
    rw [Real.le_log_iff_exp_le (by positivity)]
    push_cast
    linarith

/-- **The asymptotic antiderivative past a point**: `|Φ(T)| ≤ e^{-t}(1 + e^{-2t}/2)` for
`2 ≤ t ≤ T` (`RMF.abs_cosExpTail_le_sharp`, the bound decreasing in `T`). -/
lemma abs_cosExpTail_le_of_ge {t T : ℝ} (ht : 2 ≤ t) (hT : t ≤ T) :
    |cosExpTail T| ≤ Real.exp (-t) * (1 + Real.exp (-(2 * t)) / 2) := by
  refine (abs_cosExpTail_le_sharp (ht.trans hT)).trans ?_
  have h1 : Real.exp (-T) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-(2 * T)) ≤ Real.exp (-(2 * t)) := Real.exp_le_exp.2 (by linarith)
  have h5 : 1 + Real.exp (-(2 * T)) / 2 ≤ 1 + Real.exp (-(2 * t)) / 2 := by linarith
  exact mul_le_mul h1 h5 (by positivity) (Real.exp_pos _).le

/-- `e^{-z_n} = 2/((2n+1)π)`. -/
lemma exp_neg_hp2Z (n : ℕ) : Real.exp (-hp2Z n) = 2 / ((2 * n + 1) * π) := by
  rw [Real.exp_neg, exp_hp2Z]
  field_simp

end CosExpInt

/-! ### The telescoped sums as partial integrals, and the `u`-cells -/

section Telescoped

/-- **A telescoped block cosine sum as a partial integral**: for `0 < τ ≤ 2e^{-20}` (every
frequency of the window pairs from `k ≥ 20`) and a run of blocks `m₁ ≤ m < m₁ + j`,
`|∑_{i<j} C_{i+m₁}(τ) - J(m₁ + ξ, m₁ + j + ξ)| ≤ 3.16·10⁻⁶ + 2σ(e^{m₁+j+k} - e^{m₁+k})`,
`ξ = log τ + k` (`RMF.abs_sum_blockCosSum_sub_integral_cos_exp_le`,
`RMF.blockCosTelErr_le_numeral`). -/
lemma abs_sum_blockCosSum_sub_cosExpInt {k m₁ j : ℕ} {σ τ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hτ0 : 0 < τ) (hτ2 : τ ≤ 2 * Real.exp (-20)) :
    |∑ i ∈ Finset.range j, blockCosSum k σ τ (i + m₁)
        - cosExpInt (m₁ + (Real.log τ + k)) (m₁ + j + (Real.log τ + k))|
      ≤ 3.16 / 10 ^ 6 + 2 * σ * (Real.exp ((m₁ : ℝ) + j + k) - Real.exp ((m₁ : ℝ) + k)) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hIco : ∑ i ∈ Finset.range j, blockCosSum k σ τ (i + m₁)
      = ∑ m ∈ Finset.Ico m₁ (m₁ + j), blockCosSum k σ τ m := by
    rw [Finset.sum_Ico_eq_sum_range, show m₁ + j - m₁ = j by omega]
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm i m₁]
  rw [hIco]
  have h := abs_sum_blockCosSum_sub_integral_cos_exp_le (τ := τ) (σ := σ) (θ := k) (m₁ := m₁)
    (M := m₁ + j) (by omega) hτ0 hσ (by positivity)
  have he := blockCosTelErr_le_numeral (θ := k) (m₁ := m₁)
    (by linarith [Nat.cast_nonneg (α := ℝ) m₁]) hτ0.le hτ2
  have hint : cosExpInt (m₁ + (Real.log τ + k)) (m₁ + j + (Real.log τ + k))
      = ∫ v in ((m₁ : ℝ) + (Real.log τ + k))..(((m₁ + j : ℕ) : ℝ) + (Real.log τ + k)),
          Real.cos (Real.exp v) := by
    unfold cosExpInt
    push_cast
    rfl
  have hM : Real.exp (((m₁ + j : ℕ) : ℝ) + k) = Real.exp ((m₁ : ℝ) + j + k) := by push_cast; rfl
  rw [hint]
  rw [hM] at h
  linarith

/-- The damping `2σ(e^{M} - e^{m})` over blocks ending at `M`, from `σe^{k+M} ≤ c`: at most
`2c`. -/
lemma two_mul_sigma_damping_le {σ c A B : ℝ} (hσ : 0 ≤ σ) (hB : σ * B ≤ c) (hA : 0 ≤ A) :
    2 * σ * (B - A) ≤ 2 * c := by
  have : 0 ≤ σ * A := mul_nonneg hσ hA
  nlinarith

/-- **The pair's `u`-cell `j` at depth `d`**: `|h₁ - h₂|e^{k+d} ∈ [e^{-(j+1)/40}, e^{-j/40}]` —
the fractional depth `u` of `|h₁ - h₂|e^k = e^{-d-u}` in `[j/40, (j+1)/40]`. -/
def IsHP2UCell (k d j : ℕ) (h₁ h₂ : ℝ) : Prop :=
  Real.exp (-(((j : ℝ) + 1) / 40)) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + d)
    ∧ |h₁ - h₂| * Real.exp ((k : ℝ) + d) ≤ Real.exp (-((j : ℝ) / 40))

/-- A pair in a cell `j < 40` is at depth `d`: `e^{-1} ≤ |h₁ - h₂|e^{k+d} ≤ 1`. -/
lemma IsHP2UCell.depth {k d j : ℕ} {h₁ h₂ : ℝ} (hj : j < 40) (h : IsHP2UCell k d j h₁ h₂) :
    Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + d)
      ∧ |h₁ - h₂| * Real.exp ((k : ℝ) + d) ≤ 1 := by
  have hj' : (j : ℝ) + 1 ≤ 40 := by exact_mod_cast hj
  refine ⟨le_trans (Real.exp_le_exp.2 ?_) h.1, h.2.trans (Real.exp_le_one_iff.2 ?_)⟩
  · rw [neg_le_neg_iff, div_le_one (by norm_num)]
    exact hj'
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 40)]

/-- **The cell's phase**: in cell `j`, `ξ = d + log|h₁ - h₂| + k ∈ [-(j+1)/40, -j/40]`. -/
lemma IsHP2UCell.xi_mem {k d j : ℕ} {h₁ h₂ : ℝ} (h : IsHP2UCell k d j h₁ h₂) :
    0 < |h₁ - h₂| ∧ -(((j : ℝ) + 1) / 40) ≤ (d : ℝ) + (Real.log |h₁ - h₂| + k)
      ∧ (d : ℝ) + (Real.log |h₁ - h₂| + k) ≤ -((j : ℝ) / 40) := by
  have hD0 : 0 < |h₁ - h₂| := by
    rcases (abs_nonneg (h₁ - h₂)).lt_or_eq with h' | h'
    · exact h'
    · have := h.1
      rw [← h', zero_mul] at this
      exact absurd this (not_le.2 (Real.exp_pos _))
  have ha : (d : ℝ) + (Real.log |h₁ - h₂| + k)
      = Real.log (|h₁ - h₂| * Real.exp ((k : ℝ) + d)) := by
    rw [Real.log_mul hD0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine ⟨hD0, ?_, ?_⟩
  · rw [ha]
    have := Real.log_le_log (Real.exp_pos _) h.1
    rwa [Real.log_exp] at this
  · rw [ha]
    have := Real.log_le_log (by positivity) h.2
    rwa [Real.log_exp] at this

/-- The window's frequencies: `2e^{-(k+1)} ≤ τ ≤ 2e^{-k}` has `log 2 - 1 ≤ log τ + k ≤ log 2`. -/
lemma log_add_mem_of_window {k : ℕ} {τ : ℝ} (hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ τ)
    (hτ2 : τ ≤ 2 * Real.exp (-(k : ℝ))) :
    Real.log 2 - 1 ≤ Real.log τ + k ∧ Real.log τ + k ≤ Real.log 2 := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  constructor
  · have h := Real.log_le_log (by positivity) hτ1
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
  · have h := Real.log_le_log hτ0 hτ2
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
    linarith

end Telescoped

/-! ### The pushes' cores: the partial integrals' minima

The partial integral `J(a, T)` over `T ≥ a` is at least `min(0, J(a, z₁))`,
and from `a ∈ [z₁, 2]` at least `min(0, J(a, z₃))`: past the first minimum the later ones are
higher (`J(z₁, 2) ≥ Φ(2) + K₂ + 0.002013`, `Φ(z₃) + K₄ + 0.004026 ≤ 0`, `K_n` the bound on
`|Φ|` past `z_n`). -/

section PushCore

attribute [local simp] LeanCert.Core.MathConst.toReal in
/-- `K₂ = e^{-z₂}(1 + e^{-2z₂}/2) ≤ 0.12836`. -/
lemma tail_hp2Z_two_le : Real.exp (-hp2Z 2) * (1 + Real.exp (-(2 * hp2Z 2)) / 2) ≤ 0.12836 := by
  have h1 : Real.exp (-hp2Z 2) = 2 * (π⁻¹ * (1 / 5)) := by
    rw [exp_neg_hp2Z]; push_cast; field_simp; ring
  have h2 : Real.exp (-(2 * hp2Z 2)) = Real.exp (-hp2Z 2) * Real.exp (-hp2Z 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, h1, show ∀ x : ℝ, x / 2 = x * (1 / 2) from fun x => by ring]
  interval_decide (trust := kernel)

attribute [local simp] LeanCert.Core.MathConst.toReal in
/-- `K₄ = e^{-z₄}(1 + e^{-2z₄}/2) ≤ 0.07092`. -/
lemma tail_hp2Z_four_le : Real.exp (-hp2Z 4) * (1 + Real.exp (-(2 * hp2Z 4)) / 2) ≤ 0.07092 := by
  have h1 : Real.exp (-hp2Z 4) = 2 * (π⁻¹ * (1 / 9)) := by
    rw [exp_neg_hp2Z]; push_cast; field_simp; ring
  have h2 : Real.exp (-(2 * hp2Z 4)) = Real.exp (-hp2Z 4) * Real.exp (-hp2Z 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, h1, show ∀ x : ℝ, x / 2 = x * (1 / 2) from fun x => by ring]
  interval_decide (trust := kernel)

/-- `J(z₁, 2) ≥ Φ(2) + 0.12836 + 0.002013` (`J(z₁, 2) ≈ 0.3081`). -/
lemma cosExpInt_z1_two_ge : cosExpTail 2 + 0.12836 + 0.002013 ≤ cosExpInt (hp2Z 1) 2 := by
  have hz := hp2Z_bounds
  have h := abs_le.1 (abs_cosExpInt_sub_anti_le hz.2.1 le_rfl)
  obtain ⟨⟨hA2l, -⟩, -, hT2u⟩ := cosExpAnti_two_cosExpTail_two_mem
  obtain ⟨-, hAz⟩ := hp2AnchorA_z1
  have hz1 : 0 ≤ hp2Z 1 := hz.1.trans (hp2Z_mono (by norm_num))
  have he : (2 - hp2Z 1) / 10 ^ 6 ≤ 2 / 10 ^ 6 := by
    rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
  linarith [h.1]

/-- **The first minimum**: for every `T ≥ a`, `J(a, T) ≥ min(0, J(a, z₁))`. -/
lemma push_core_z1 {a T : ℝ} (haT : a ≤ T) :
    min 0 (cosExpInt a (hp2Z 1)) ≤ cosExpInt a T := by
  have hz := hp2Z_bounds
  have hz01 : hp2Z 0 ≤ hp2Z 1 := hp2Z_mono (by norm_num)
  have hz12 : hp2Z 1 ≤ hp2Z 2 := hp2Z_mono (by norm_num)
  rcases le_total T (hp2Z 0) with h0 | h0
  · exact (min_le_left _ _).trans (cosExpInt_nonneg_le_z0 haT h0)
  rcases le_total T (hp2Z 1) with h1 | h1
  · have hn : cosExpInt T (hp2Z 1) ≤ 0 :=
      cosExpInt_nonpos_z 0 h1 (by simpa using h0) (by simp)
    have := cosExpInt_add a T (hp2Z 1)
    exact (min_le_right _ _).trans (by linarith)
  rcases le_total T (hp2Z 2) with h2 | h2
  · have hn : 0 ≤ cosExpInt (hp2Z 1) T :=
      cosExpInt_nonneg_z 1 le_rfl h1 (by simp) (by simpa using h2)
    have := cosExpInt_add a (hp2Z 1) T
    exact (min_le_right _ _).trans (by linarith)
  · -- past `z₂`: `J(2, T) ≥ Φ(T) - Φ(2) - 0.002013 ≥ -K₂ - Φ(2) - 0.002013`
    have hT2 : 2 ≤ T := hz.2.2.trans h2
    have hJ2 := abs_le.1 (abs_cosExpInt_two_sub_le hT2)
    have hK := abs_le.1 ((abs_cosExpTail_le_of_ge (hz.2.2) h2).trans tail_hp2Z_two_le)
    have hz1 := cosExpInt_z1_two_ge
    have e1 := cosExpInt_add a (hp2Z 1) 2
    have e2 := cosExpInt_add a 2 T
    exact (min_le_right _ _).trans (by linarith [hJ2.1, hK.1])

/-- **The second minimum**: for `z₁ ≤ a ≤ 2` and every `T ≥ a`, `J(a, T) ≥ min(0, J(a, z₃))`. -/
lemma push_core_z3 {a : ℝ} (ha₁ : hp2Z 1 ≤ a) (ha₂ : a ≤ 2) {T : ℝ} (haT : a ≤ T) :
    min 0 (cosExpInt a (hp2Z 3)) ≤ cosExpInt a T := by
  have hz := hp2Z_bounds
  have hz23 : hp2Z 2 ≤ hp2Z 3 := hp2Z_mono (by norm_num)
  have hz34 : hp2Z 3 ≤ hp2Z 4 := hp2Z_mono (by norm_num)
  have ha2 : a ≤ hp2Z 2 := ha₂.trans hz.2.2
  rcases le_total T (hp2Z 2) with h2 | h2
  · exact (min_le_left _ _).trans (cosExpInt_nonneg_z 1 le_rfl haT (by simpa using ha₁)
      (by simpa using h2))
  rcases le_total T (hp2Z 3) with h3 | h3
  · have hn : cosExpInt T (hp2Z 3) ≤ 0 :=
      cosExpInt_nonpos_z 1 h3 (by simpa using h2) (by simp)
    have := cosExpInt_add a T (hp2Z 3)
    exact (min_le_right _ _).trans (by linarith)
  rcases le_total T (hp2Z 4) with h4 | h4
  · have hn : 0 ≤ cosExpInt (hp2Z 3) T :=
      cosExpInt_nonneg_z 2 (by norm_num) h3 (by simp) (by simpa using h4)
    have := cosExpInt_add a (hp2Z 3) T
    exact (min_le_right _ _).trans (by linarith)
  · -- past `z₄`
    have h24 : 2 ≤ hp2Z 4 := hz.2.2.trans (hz23.trans hz34)
    have h2z3 : 2 ≤ hp2Z 3 := hz.2.2.trans hz23
    have hJT := abs_le.1 (abs_cosExpInt_two_sub_le (h24.trans h4))
    have hJ3 := abs_le.1 (abs_cosExpInt_two_sub_le h2z3)
    have hK := abs_le.1 ((abs_cosExpTail_le_of_ge h24 h4).trans tail_hp2Z_four_le)
    obtain ⟨-, hΦ3⟩ := hp2AnchorPhi_z3
    have e1 := cosExpInt_add a 2 T
    have e2 := cosExpInt_add a 2 (hp2Z 3)
    exact (min_le_right _ _).trans (by linarith [hJT.1, hJ3.2, hK.1])

/-- **A push from its core**: `min(0, J(a, z)) ≤ J(a, T)`, `J(a, z) ≥ V`, `P ≥ 0` and `P ≥ -V` give
`-J(a, T) ≤ P`. -/
lemma neg_le_of_push_core {JaT Jaz V P : ℝ} (hc : min 0 Jaz ≤ JaT) (hs : V ≤ Jaz) (hP0 : 0 ≤ P)
    (hP : -V ≤ P) : -JaT ≤ P := by
  rcases le_total 0 Jaz with h | h
  · rw [min_eq_left h] at hc
    linarith
  · rw [min_eq_right h] at hc
    linarith

end PushCore

/-! ### The zeros located, and the corner values -/

section Zeros

attribute [local simp] LeanCert.Core.MathConst.toReal

/-- `z_n = log(π(2n+1)/2)`, in the form interval arithmetic reads. -/
lemma hp2Z_eq (n : ℕ) : hp2Z n = Real.log (π * ((2 * n + 1) / 2)) := by
  unfold hp2Z
  congr 1
  ring

/-- **The zeros to four decimals**: `z₀ ≈ 0.45158`, `z₁ ≈ 1.55019`, `z₂ ≈ 2.06102`,
`z₃ ≈ 2.39749`, `z₄ ≈ 2.64881`, `z₅ ≈ 2.84948`. -/
lemma hp2Z_numerals :
    (0.4515 ≤ hp2Z 0 ∧ hp2Z 0 ≤ 0.4516) ∧ (1.5501 ≤ hp2Z 1 ∧ hp2Z 1 ≤ 1.5503)
      ∧ (2.061 ≤ hp2Z 2 ∧ hp2Z 2 ≤ 2.0611) ∧ (2.3974 ≤ hp2Z 3 ∧ hp2Z 3 ≤ 2.3975)
      ∧ (2.6488 ≤ hp2Z 4 ∧ hp2Z 4 ≤ 2.6489) ∧ (2.8494 ≤ hp2Z 5 ∧ hp2Z 5 ≤ 2.8495) := by
  simp only [hp2Z_eq]
  norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | (rw [Real.le_log_iff_exp_le (by positivity)]; interval_decide (trust := kernel))
    | (rw [Real.log_le_iff_le_exp (by positivity)]; interval_decide (trust := kernel))

end Zeros

/-- `log 2 ∈ [0.693147, 0.693148]`. -/
lemma log_two_numerals : 0.693147 ≤ Real.log 2 ∧ Real.log 2 ≤ 0.693148 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

/-- **A corner's value below `2`**: `J(p, q) ≤ A(q) - A(p) + 3·10⁻⁶` and `≥ A(q) - A(p) - 3·10⁻⁶`
for `p ≤ q ≤ 2`, `q - p ≤ 3`. -/
lemma cosExpInt_mem_anti {p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 2) (h3 : q - p ≤ 3) :
    cosExpAnti q - cosExpAnti p - 3 / 10 ^ 6 ≤ cosExpInt p q
      ∧ cosExpInt p q ≤ cosExpAnti q - cosExpAnti p + 3 / 10 ^ 6 := by
  have h := abs_le.1 (abs_cosExpInt_sub_anti_le hpq hq)
  have he : (q - p) / 10 ^ 6 ≤ 3 / 10 ^ 6 := by
    rw [div_le_div_iff_of_pos_right (by norm_num)]; exact h3
  constructor <;> linarith [h.1, h.2]

/-- **A corner's value across `2`**: for `p ≤ 2 ≤ q`, `2 - p ≤ 3`,
`J(p, q) = J(p, 2) + J(2, q)` within `0.002016` of `A(2) - A(p) + Φ(q) - Φ(2)`. -/
lemma cosExpInt_mem_across {p q : ℝ} (hp : p ≤ 2) (hq : 2 ≤ q) (h3 : 2 - p ≤ 3) :
    cosExpAnti 2 - cosExpAnti p + cosExpTail q - cosExpTail 2 - 0.002016 ≤ cosExpInt p q
      ∧ cosExpInt p q ≤ cosExpAnti 2 - cosExpAnti p + cosExpTail q - cosExpTail 2 + 0.002016 := by
  have h1 := cosExpInt_mem_anti hp le_rfl h3
  have h2 := abs_le.1 (abs_cosExpInt_two_sub_le hq)
  have e := cosExpInt_add p 2 q
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### The phases of the window's frequencies

For the sum frequency `h₁ + h₂` and the doubled frequency `2h` the block phase is
`x = log τ + k ∈ [log 2 - 1, log 2]` (`RMF.log_add_mem_of_window`); the sums over the first
blocks are the partial integrals from `d + x`, bounded over the whole range of `x` by the sign
pieces. -/

section Phases

/-- **`J(x, 2)` over the phases**: `≤ max(J(log 2 - 1, 2), J(log 2, 2))`. -/
lemma cosExpInt_phase_two_le {x : ℝ} (h₁ : Real.log 2 - 1 ≤ x) (h₂ : x ≤ Real.log 2) :
    cosExpInt x 2 ≤ max (cosExpInt (Real.log 2 - 1) 2) (cosExpInt (Real.log 2) 2) := by
  obtain ⟨hz0, hz1⟩ : hp2Z 0 ≤ 0.4516 ∧ 1.5501 ≤ hp2Z 1 :=
    ⟨hp2Z_numerals.1.2, hp2Z_numerals.2.1.1⟩
  have hl := log_two_numerals
  rcases le_total x (hp2Z 0) with hx | hx
  · refine le_max_of_le_left (cosExpInt_le_corner (cosExpInt_nonneg_le_z0 h₁ hx) ?_)
    rw [cosExpInt_self]
  · refine le_max_of_le_right (cosExpInt_le_corner ?_ ?_)
    · rw [cosExpInt_symm]
      exact neg_nonneg.2 (cosExpInt_nonpos_z 0 h₂ (by simpa using hx) (by simp; linarith))
    · rw [cosExpInt_self]

/-- **`J(1 + x, 2)` over the phases**: `≤ J(z₁, 2)` (the maximum at the zero `z₁`). -/
lemma cosExpInt_phase_one_two_le {x : ℝ} (h₁ : Real.log 2 - 1 ≤ x) (h₂ : x ≤ Real.log 2) :
    cosExpInt (1 + x) 2 ≤ cosExpInt (hp2Z 1) 2 := by
  obtain ⟨⟨-, hz0⟩, -, ⟨hz2, -⟩, -⟩ := hp2Z_numerals
  have hl := log_two_numerals
  rcases le_total (1 + x) (hp2Z 1) with hx | hx
  · have hn := cosExpInt_nonpos_z 0 hx (by simp; linarith) (by simp)
    have := cosExpInt_add (1 + x) (hp2Z 1) 2
    linarith
  · have hn := cosExpInt_nonneg_z 1 le_rfl hx (by simp) (by simp; linarith)
    have := cosExpInt_add (hp2Z 1) (1 + x) 2
    linarith

/-- **`J(1 + x, 2)` over the phases, from below**: `≥ min(J(log 2, 2), J(log 2 + 1, 2))`. -/
lemma cosExpInt_phase_one_two_ge {x : ℝ} (h₁ : Real.log 2 - 1 ≤ x) (h₂ : x ≤ Real.log 2) :
    min (cosExpInt (Real.log 2) 2) (cosExpInt (Real.log 2 + 1) 2) ≤ cosExpInt (1 + x) 2 := by
  obtain ⟨⟨-, hz0⟩, -, ⟨hz2, -⟩, -⟩ := hp2Z_numerals
  have hl := log_two_numerals
  rcases le_total (1 + x) (hp2Z 1) with hx | hx
  · refine min_le_of_left_le (le_cosExpInt_corner ?_ ?_)
    · exact cosExpInt_nonpos_z 0 (by linarith) (by simp; linarith) (by simpa using hx)
    · rw [cosExpInt_self]
  · refine min_le_of_right_le (le_cosExpInt_corner ?_ ?_)
    · rw [cosExpInt_symm]
      exact neg_nonpos.2 (cosExpInt_nonneg_z 1 le_rfl (by linarith) (by simpa using hx)
        (by simp; linarith))
    · rw [cosExpInt_self]

/-- **`J(2 + x, 2)` over the phases below `2`**: `≤ J(log 2 + 1, 2)`. -/
lemma cosExpInt_phase_two_two_le {x : ℝ} (h₁ : Real.log 2 - 1 ≤ x) (h₂ : x ≤ 0) :
    0 ≤ cosExpInt (2 + x) 2 ∧ cosExpInt (2 + x) 2 ≤ cosExpInt (Real.log 2 + 1) 2 := by
  obtain ⟨-, ⟨-, hz1⟩, ⟨hz2, -⟩, -⟩ := hp2Z_numerals
  have hl := log_two_numerals
  have hn := cosExpInt_nonneg_z 1 le_rfl (by linarith : Real.log 2 + 1 ≤ 2 + x)
    (by simp; linarith) (by simp; linarith)
  have hn' := cosExpInt_nonneg_z 1 le_rfl (by linarith : 2 + x ≤ 2) (by simp; linarith)
    (by simp; linarith)
  have := cosExpInt_add (Real.log 2 + 1) (2 + x) 2
  constructor <;> linarith

/-- **`J(x, 1 + x)` over the phases** (the prefix mass at one block): at most
`max(J(log 2 - 1, log 2), log 2 + 1 - z₁)` — the corner `x = log 2 - 1` below `z₀`, and from `z₀`
on the integrand is negative up to `z₁`. -/
lemma cosExpInt_phase_one_le {x : ℝ} (h₁ : Real.log 2 - 1 ≤ x) (h₂ : x ≤ Real.log 2) :
    cosExpInt x (1 + x) ≤ max (cosExpInt (Real.log 2 - 1) (Real.log 2))
      (Real.log 2 + 1 - hp2Z 1) := by
  obtain ⟨⟨hz0l, hz0⟩, ⟨hz1, hz1u⟩, ⟨hz2, -⟩, -⟩ := hp2Z_numerals
  have hl := log_two_numerals
  rcases le_total x (hp2Z 0) with hx | hx
  · -- the corner `(log 2 - 1, log 2)`: `1 + x ∈ [log 2, 1 + z₀] ⊂ [z₀, z₁]`
    refine le_max_of_le_left (cosExpInt_le_corner (cosExpInt_nonneg_le_z0 h₁ hx) ?_)
    rw [cosExpInt_symm]
    refine neg_nonneg.2 (cosExpInt_nonpos_z 0 (by linarith) (by simp; linarith) ?_)
    simp only [mul_zero, zero_add]
    linarith
  · refine le_max_of_le_right ?_
    rcases le_total (1 + x) (hp2Z 1) with hx1 | hx1
    · have hn := cosExpInt_nonpos_z 0 (by linarith : x ≤ 1 + x) (by simpa using hx)
        (by simpa using hx1)
      linarith
    · -- `J(x, z₁) ≤ 0` and `J(z₁, 1 + x) ≤ 1 + x - z₁`
      have hn := cosExpInt_nonpos_z 0 (by linarith : x ≤ hp2Z 1) (by simpa using hx) (by simp)
      have hb : cosExpInt (hp2Z 1) (1 + x) ≤ 1 + x - hp2Z 1 := by
        have h := intervalIntegral.integral_mono_on (f := fun v => Real.cos (Real.exp v))
          (g := fun _ => (1 : ℝ)) hx1 (intervalIntegrable_cos_exp _ _) intervalIntegrable_const
          (fun v _ => Real.cos_le_one _)
        simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
        exact h
      have := cosExpInt_add x (hp2Z 1) (1 + x)
      linarith

end Phases

/-! ### The tails of `Φ` past the phases' blocks -/

section Tails

/-- `K(2) = e^{-2}(1 + e^{-4}/2) ≤ 0.136576`. -/
lemma tail_two_le : Real.exp (-2) * (1 + Real.exp (-(2 * 2)) / 2) ≤ 0.136576 := by
  rw [show ∀ x : ℝ, x / 2 = x * (1 / 2) from fun x => by ring]
  interval_decide (trust := kernel)

/-- `K(log 2 + 2) = (e^{-2}/2)(1 + e^{-4}/8) ≤ 0.067823`. -/
lemma tail_log_two_add_two_le :
    Real.exp (-(Real.log 2 + 2)) * (1 + Real.exp (-(2 * (Real.log 2 + 2))) / 2) ≤ 0.067823 := by
  have h1 : Real.exp (-(Real.log 2 + 2)) = Real.exp (-2) * (1 / 2) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)]
    ring
  have h2 : Real.exp (-(2 * (Real.log 2 + 2))) = Real.exp (-(Real.log 2 + 2))
      * Real.exp (-(Real.log 2 + 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, show ∀ x : ℝ, x / 2 = x * (1 / 2) from fun x => by ring, h1]
  interval_decide (trust := kernel)

/-- `K(log 2 + 3) = (e^{-3}/2)(1 + e^{-6}/8) ≤ 0.024903`. -/
lemma tail_log_two_add_three_le :
    Real.exp (-(Real.log 2 + 3)) * (1 + Real.exp (-(2 * (Real.log 2 + 3))) / 2) ≤ 0.024903 := by
  have h1 : Real.exp (-(Real.log 2 + 3)) = Real.exp (-3) * (1 / 2) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)]
    ring
  have h2 : Real.exp (-(2 * (Real.log 2 + 3))) = Real.exp (-(Real.log 2 + 3))
      * Real.exp (-(Real.log 2 + 3)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, show ∀ x : ℝ, x / 2 = x * (1 / 2) from fun x => by ring, h1]
  interval_decide (trust := kernel)

/-- `6e^{-4(log 2 + 2)} ≤ 0.000126`. -/
lemma six_mul_exp_neg_four_log_two_add_two_le :
    6 * Real.exp (-(4 * (Real.log 2 + 2))) ≤ 0.000126 := by
  have h1 : Real.exp (-(4 * (Real.log 2 + 2))) = Real.exp (-8) * (1 / 16) := by
    rw [show -(4 * (Real.log 2 + 2)) = -8 + -(4 * Real.log 2) by ring, Real.exp_add,
      show -(4 * Real.log 2) = -Real.log 16 by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring,
      Real.exp_neg (Real.log 16), Real.exp_log (by norm_num)]
    ring
  rw [h1]
  interval_decide (trust := kernel)

/-- **`|Φ|` past a phase's block**: for `v ≥ t ≥ 2` with `t` one of `2`, `log 2 + 2`,
`log 2 + 3`, `|Φ(v)|` is at most `0.136576`, `0.067823`, `0.024903`. -/
lemma abs_cosExpTail_le_phase {v : ℝ} :
    (2 ≤ v → |cosExpTail v| ≤ 0.136576)
      ∧ (Real.log 2 + 2 ≤ v → |cosExpTail v| ≤ 0.067823)
      ∧ (Real.log 2 + 3 ≤ v → |cosExpTail v| ≤ 0.024903) := by
  have hl := log_two_numerals
  refine ⟨fun h => (abs_cosExpTail_le_of_ge le_rfl h).trans tail_two_le,
    fun h => (abs_cosExpTail_le_of_ge (by linarith) h).trans tail_log_two_add_two_le,
    fun h => (abs_cosExpTail_le_of_ge (by linarith) h).trans tail_log_two_add_three_le⟩

end Tails

end RMF
