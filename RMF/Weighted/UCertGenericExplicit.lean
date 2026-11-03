/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UAssemblyExplicit

/-!
# The first moment below `q = ½`: the certificate's generic lemmas

The pieces from which the cells of the certificate for the bound (U),
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` with `Λ = log log x`, are assembled.

* **window groups summed** (`RMF.one_sub_exp_neg_mul_sum_le_group`): `w_k ≤ e^{-ak}c̄` on
  `[s, t)` gives `(1 - e^{-a})·∑_{s≤k<t} w_k ≤ c̄(e^{-as} - e^{-at})`;
  `1/(1 - e^{-x}) ≤ 1/x + 1/2 + x/10` (`RMF.inv_one_sub_exp_neg_le_taylor`) keeps the `1/q` of
  `a = q(1-2q)`;
* **one window** (`RMF.uWindowBound_le_chaos`, `RMF.uWindowBound_le_jensen`): (PF) below its power,
  the window's constant decreasing in `q` and `k`, the chaos factor split as
  `(1-q)^{-q}n^{-q/2}`, and `(Λ/n)^{q/2} ≤ ρ`;
* **the chaos constant on a cell of `q`** (`RMF.winChaosConst_le_cell`) from its leaves at the tilt
  `E₀ ≤ 1/33680`;
* **the far windows** (`RMF.uFarParams`): level `A₀ + j` and room `N₀ + 20j`, valid for every `j`,
  with a chaos constant linear in `j` (`RMF.uFarParams_const_le`), and the far range's product
  `(1 - 2q)B^{3q/2}` decreasing on a cell (`RMF.one_sub_two_mul_rpow_le`);
* **the small pieces**: the smooth tail `≤ e^{1.42 - 0.4995Λ}` (`RMF.halfTail_le_decay`), the
  reduction's error `≤ 7Λ/√L` (`RMF.halfErr_le_decay`), the central window at `q`
  (`RMF.uCen_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### Geometric sums -/

/-- `e^{-a}` to the power `k` is `e^{-ak}`. -/
lemma exp_neg_pow (a : ℝ) (k : ℕ) : Real.exp (-a) ^ k = Real.exp (-(a * k)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **A geometric window sum, exactly**: `(1 - e^{-a})·∑_{s≤k<t} e^{-ak} = e^{-as} - e^{-at}`. -/
lemma one_sub_exp_neg_mul_sum_Ico {a : ℝ} (ha : 0 < a) {s t : ℕ} (hst : s ≤ t) :
    (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico s t, Real.exp (-(a * k))
      = Real.exp (-(a * s)) - Real.exp (-(a * t)) := by
  have hx : Real.exp (-a) ≠ 1 := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    exact this.ne
  have h := geom_sum_Ico hx hst
  simp only [exp_neg_pow] at h
  rw [h]
  have hd : Real.exp (-a) - 1 ≠ 0 := sub_ne_zero.2 hx
  field_simp
  ring

/-- **`1/(1 - e^{-x}) ≤ 1/x + 1/2 + x/10`** for `0 < x ≤ 1/8`: from
`e^{-x} ≤ 1 - x + x²/2 - x³/6 + 5x⁴/96` (`Real.exp_bound` at `n = 4`). -/
lemma inv_one_sub_exp_neg_le_taylor {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 8) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 / x + 1 / 2 + x / 10 := by
  have hb := Real.exp_bound (x := -x) (by rw [abs_neg, abs_of_pos hx0]; linarith)
    (n := 4) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 4, (-x) ^ m / (m.factorial : ℝ)
      = 1 - x + x ^ 2 / 2 - x ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum, abs_neg, abs_of_pos hx0] at hb
  have hup : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + 5 * x ^ 4 / 96 := by
    have := (abs_sub_le_iff.1 hb).1
    have hc : x ^ 4 * ((Nat.succ 4 : ℕ) / ((Nat.factorial 4 : ℕ) * (4 : ℕ)) : ℝ)
        = 5 * x ^ 4 / 96 := by
      norm_num [Nat.factorial]
      ring
    linarith
  have hpos : 0 < x - x ^ 2 / 2 + x ^ 3 / 6 - 5 * x ^ 4 / 96 := by
    have h2 : x ^ 2 ≤ x / 8 := by nlinarith
    have h4 : x ^ 4 ≤ x / 8 := by nlinarith [pow_le_pow_left₀ hx0.le hx 4]
    have h3 : 0 ≤ x ^ 3 := by positivity
    nlinarith
  have hlow : x - x ^ 2 / 2 + x ^ 3 / 6 - 5 * x ^ 4 / 96 ≤ 1 - Real.exp (-x) := by linarith
  have hpoly : x ≤ (x - x ^ 2 / 2 + x ^ 3 / 6 - 5 * x ^ 4 / 96) * (1 + x / 2 + x ^ 2 / 10) := by
    have h2 : 0 ≤ x ^ 2 := sq_nonneg x
    have e : (x - x ^ 2 / 2 + x ^ 3 / 6 - 5 * x ^ 4 / 96) * (1 + x / 2 + x ^ 2 / 10) - x
        = x ^ 3 * (1 / 60 - 3 / 160 * x - 3 / 320 * x ^ 2 - 1 / 192 * x ^ 3) := by ring
    have hx2 : x ^ 2 ≤ 1 / 64 := by nlinarith
    have hx3 : x ^ 3 ≤ 1 / 512 := by nlinarith [pow_le_pow_left₀ hx0.le hx 3]
    have hin : 0 ≤ 1 / 60 - 3 / 160 * x - 3 / 320 * x ^ 2 - 1 / 192 * x ^ 3 := by linarith
    have := mul_nonneg (pow_nonneg hx0.le 3) hin
    linarith
  have hd : 0 < 1 - Real.exp (-x) := lt_of_lt_of_le hpos hlow
  rw [inv_eq_one_div, div_le_iff₀ hd]
  have e2 : (1 / x + 1 / 2 + x / 10) = (1 + x / 2 + x ^ 2 / 10) / x := by
    field_simp
  rw [e2, div_mul_eq_mul_div, le_div_iff₀ hx0]
  have h1 : 0 ≤ 1 + x / 2 + x ^ 2 / 10 := by positivity
  calc 1 * x ≤ (x - x ^ 2 / 2 + x ^ 3 / 6 - 5 * x ^ 4 / 96) * (1 + x / 2 + x ^ 2 / 10) := by
        linarith
    _ ≤ (1 - Real.exp (-x)) * (1 + x / 2 + x ^ 2 / 10) := mul_le_mul_of_nonneg_right hlow h1
    _ = (1 + x / 2 + x ^ 2 / 10) * (1 - Real.exp (-x)) := by ring

/-! ### Monotonicity in `q` -/

/-- **The chaos factor, split**: `(1 + (1-q)√n)^{-q} ≤ (1-q)^{-q}·n^{-q/2}` for `0 ≤ q < 1`,
`n > 0`. -/
lemma one_add_mul_sqrt_rpow_neg_le {q n : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n) :
    (1 + (1 - q) * Real.sqrt n) ^ (-q) ≤ (1 - q) ^ (-q) * n ^ (-(q / 2)) := by
  have h1q : 0 < 1 - q := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hle : (1 - q) * Real.sqrt n ≤ 1 + (1 - q) * Real.sqrt n := by linarith
  calc (1 + (1 - q) * Real.sqrt n) ^ (-q) ≤ ((1 - q) * Real.sqrt n) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    _ = (1 - q) ^ (-q) * Real.sqrt n ^ (-q) := Real.mul_rpow h1q.le hs.le
    _ = (1 - q) ^ (-q) * n ^ (-(q / 2)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
        congr 2
        ring

/-- `(1-q)^{-q}` is increasing: `(1-q)^{-q} ≤ (1-b)^{-b}` for `0 ≤ q ≤ b < 1`. -/
lemma one_sub_rpow_neg_self_le {q b : ℝ} (hq0 : 0 ≤ q) (hqb : q ≤ b) (hb1 : b < 1) :
    (1 - q) ^ (-q) ≤ (1 - b) ^ (-b) := by
  have h1q : 0 < 1 - q := by linarith
  have h1b : 0 < 1 - b := by linarith
  rw [Real.rpow_def_of_pos h1q, Real.rpow_def_of_pos h1b]
  refine Real.exp_le_exp.2 ?_
  have hl : Real.log (1 - b) ≤ Real.log (1 - q) := Real.log_le_log h1b (by linarith)
  have hlb : Real.log (1 - b) ≤ 0 := Real.log_nonpos h1b.le (by linarith)
  -- `log(1-q)·(-q) ≤ log(1-b)·(-q) ≤ log(1-b)·(-b)`
  have h1 : Real.log (1 - q) * (-q) ≤ Real.log (1 - b) * (-q) :=
    mul_le_mul_of_nonpos_right hl (by linarith)
  have h2 : Real.log (1 - b) * (-q) ≤ Real.log (1 - b) * (-b) :=
    mul_le_mul_of_nonpos_left (by linarith) hlb
  linarith

/-! ### The windows' constants -/

/-- `thetaWindowConstQ` is decreasing in `q`:
`thetaWindowConstQ θ q k y ≤ thetaWindowConstQ θ a k y` for `a ≤ q`, `θ > 0`. -/
lemma thetaWindowConstQ_anti_q {θ a q : ℝ} (hθ : 0 < θ) (haq : a ≤ q) (k y : ℕ) :
    thetaWindowConstQ θ q k y ≤ thetaWindowConstQ θ a k y := by
  unfold thetaWindowConstQ
  have hW : taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      ≤ taylorWindowW (2 * (1 - a) * thetaWindowExp θ k) := by
    refine taylorWindowW_mono (mul_le_mul_of_nonneg_right (by linarith) ?_)
    exact thetaWindowExp_nonneg hθ.le k
  have h2 : (0 : ℝ) ≤ 2 / θ := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW h2) (Real.exp_pos _).le

/-- `thetaWindowConstQ` is decreasing in the window index. -/
lemma thetaWindowConstQ_anti_k {θ q : ℝ} (hθ : 0 < θ) (hq : q ≤ 1) {k₁ k : ℕ} (hk : k₁ ≤ k)
    (y : ℕ) : thetaWindowConstQ θ q k y ≤ thetaWindowConstQ θ q k₁ y := by
  unfold thetaWindowConstQ
  have hW : taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      ≤ taylorWindowW (2 * (1 - q) * thetaWindowExp θ k₁) :=
    taylorWindowW_mono (mul_le_mul_of_nonneg_left (thetaWindowExp_anti hθ.le hk)
      (by linarith))
  have he : Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ)
      ≤ Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k₁ : ℝ)) / θ) := by
    refine Real.exp_le_exp.2 (add_le_add le_rfl ?_)
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hθ.le
    exact Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast hk))
  have hW0 : 0 ≤ taylorWindowW (2 * (1 - q) * thetaWindowExp θ k) :=
    taylorWindowW_nonneg (mul_nonneg (by linarith) (thetaWindowExp_nonneg hθ.le k))
  have h2 : (0 : ℝ) ≤ 2 / θ := by positivity
  calc 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
        * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ)
      ≤ 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k₁)
        * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW h2) (Real.exp_pos _).le
    _ ≤ 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k₁)
        * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k₁ : ℝ)) / θ) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg h2 (le_trans hW0 hW))

/-- `thetaWindowConstQ ≥ 1` for `θ ≤ 2` and `q ≤ 1`. -/
lemma one_le_thetaWindowConstQ {θ q : ℝ} (hθ : 0 < θ) (hθ2 : θ ≤ 2) (hq : q ≤ 1) (k y : ℕ) :
    1 ≤ thetaWindowConstQ θ q k y := by
  unfold thetaWindowConstQ
  have hb : 0 ≤ 2 * (1 - q) * thetaWindowExp θ k :=
    mul_nonneg (by linarith) (thetaWindowExp_nonneg hθ.le k)
  have hW : Real.exp 1 - 1 ≤ taylorWindowW (2 * (1 - q) * thetaWindowExp θ k) := by
    have h := taylorWindowW_mono hb
    unfold taylorWindowW at h ⊢
    have h0 : (Real.exp 1 - 1) + 0 * (1 - (Real.exp 1)⁻¹)
        + (Real.exp 0 - 1 - 0) * (1 - (Real.exp 1)⁻¹ ^ 3) / 3 = Real.exp 1 - 1 := by simp
    rw [h0] at h
    exact h
  have he1 : 1 ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
  have h2θ : 1 ≤ 2 / θ := by rw [le_div_iff₀ hθ]; linarith
  have hE : 1 ≤ Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) :=
    Real.one_le_exp (by positivity)
  have h1 : 1 ≤ 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k) := by nlinarith
  nlinarith

/-- **(PF) at the split point below its power**: `RMF.thetaPF σ θ q k ≤ θ^{-a}e^{-ak}`,
`a = q(1-2q) ≥ 0`, once the exponent's bracket is negative. -/
lemma thetaPF_le {σ θ q : ℝ} (hθ : 0 < θ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {k : ℕ}
    (hbr : 9.0028 / (θ * Real.exp k) + 2 * σ * (θ * Real.exp k + 1 / 100 + Real.log 4 + 4)
      ≤ 3 / 20) :
    thetaPF σ θ q k ≤ θ ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k)) := by
  have ha : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  unfold thetaPF
  have h1 : Real.exp (q * (1 - 2 * q) * (9.0028 / (θ * Real.exp k)
      + 2 * σ * (θ * Real.exp k + 1 / 100 + Real.log 4 + 4) - 3 / 20)) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ha (by linarith))
  have h2 : (θ * Real.exp k) ^ (q * (2 * q - 1))
      = θ ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k)) := by
    rw [Real.mul_rpow hθ.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 1
    · ring_nf
    · congr 1
      ring
  rw [h2]
  have h3 : 0 ≤ θ ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k)) :=
    mul_nonneg (Real.rpow_nonneg hθ.le _) (Real.exp_pos _).le
  calc Real.exp (q * (1 - 2 * q) * (9.0028 / (θ * Real.exp k)
        + 2 * σ * (θ * Real.exp k + 1 / 100 + Real.log 4 + 4) - 3 / 20))
        * (θ ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k)))
      ≤ 1 * (θ ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k))) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = _ := one_mul _

/-! ### The chaos constant -/

/-- **The far range's product is decreasing on the cell**: `(1 - 2q)B^{3q/2} ≤ (1 - 2a)B^{3a/2}`
for `a ≤ q` and `(1 - 2a)·(3/2)log B ≤ 2`, `B ≥ 1` (from `e^{-x} ≥ 1 - x`). -/
lemma one_sub_two_mul_rpow_le {a q B : ℝ} (haq : a ≤ q) (hB : 1 ≤ B)
    (hc : (1 - 2 * a) * (3 / 2 * Real.log B) ≤ 2) (ha : a ≤ 1 / 2) :
    (1 - 2 * q) * B ^ (3 / 2 * q) ≤ (1 - 2 * a) * B ^ (3 / 2 * a) := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos hB0]
  set c := 3 / 2 * Real.log B with hcdef
  set t := q - a with htdef
  have ht : 0 ≤ t := by linarith
  have e1 : Real.log B * (3 / 2 * q) = Real.log B * (3 / 2 * a) + c * t := by
    rw [hcdef, htdef]; ring
  rw [e1, Real.exp_add]
  have hex : 1 - c * t ≤ Real.exp (-(c * t)) := by linarith [Real.add_one_le_exp (-(c * t))]
  have hE : 0 < Real.exp (c * t) := Real.exp_pos _
  have hinv : Real.exp (-(c * t)) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add]; simp
  -- `(1 - 2q) ≤ (1 - 2a)e^{-ct}` since `(1 - 2a)(1 - ct) ≥ 1 - 2a - 2t`
  have hV : 0 ≤ 1 - 2 * a := by linarith
  have h1 : 1 - 2 * q ≤ (1 - 2 * a) * Real.exp (-(c * t)) := by
    have h2 : (1 - 2 * a) * (1 - c * t) ≤ (1 - 2 * a) * Real.exp (-(c * t)) :=
      mul_le_mul_of_nonneg_left hex hV
    have h3 : (1 - 2 * a) * c * t ≤ 2 * t := by
      have := mul_le_mul_of_nonneg_right hc ht
      linarith
    nlinarith
  have hEa : 0 ≤ Real.exp (Real.log B * (3 / 2 * a)) := (Real.exp_pos _).le
  calc (1 - 2 * q) * (Real.exp (Real.log B * (3 / 2 * a)) * Real.exp (c * t))
      ≤ (1 - 2 * a) * Real.exp (-(c * t)) * (Real.exp (Real.log B * (3 / 2 * a))
          * Real.exp (c * t)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hEa hE.le)
    _ = (1 - 2 * a) * Real.exp (Real.log B * (3 / 2 * a))
          * (Real.exp (-(c * t)) * Real.exp (c * t)) := by ring
    _ = (1 - 2 * a) * Real.exp (Real.log B * (3 / 2 * a)) := by rw [hinv, mul_one]

/-! ### The chaos constant's leaves at the tilt `E₀ ≤ 1/33680`, any `T`, `κ` -/

/-- `radAveragedConst E₀ (11/20) T κ ≤ (1 + 10⁻⁷)·1.16341·(1 + (11/20)/(4κ))/(1 - (11/10)/T)`. -/
lemma radAveragedConst_le_of {E₀ Tr κ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680)
    (hTr : 11 / 10 < Tr) (hκ : 0 < κ) :
    radAveragedConst E₀ (11 / 20) Tr κ
      ≤ (1 + 1 / 10000000) * (116341 / 100000) * (1 + 11 / 20 / (4 * κ))
        / (1 - 2 * (11 / 20) / Tr) := by
  have hK := radAveragedK_le_half hE₀1
  have hK0 : 0 ≤ radAveragedK E₀ := le_trans zero_le_one (one_le_radAveragedK hE₀)
  have he := exp_neg_hundred_le
  have hd : 0 < 1 - 2 * (11 / 20) / Tr := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hk0 : 0 ≤ 1 + 11 / 20 / (4 * κ) := by positivity
  unfold radAveragedConst
  refine div_le_div_of_nonneg_right ?_ hd.le
  refine mul_le_mul_of_nonneg_right ?_ hk0
  exact mul_le_mul (by linarith) hK hK0 (by norm_num)

/-- **The level shift at any `T`, `κ`**: with `log κ ≤ ℓκ` and `log(1.16341·T) ≤ ℓKT`,
`radAveragedShift E₀ (11/20) T κ ≤ 3·0.2553 + (11/20)(ℓκ + 1/κ + 0.693148) + 29/20 + 4/25
  + 2·1.253315 + (11/20)(1 + 0.693148 + 3.912024) + (11/10)ℓKT`. -/
lemma radAveragedShift_le_of {E₀ Tr κ ℓκ ℓKT : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680)
    (hTr : 1 ≤ Tr) (hℓκ : Real.log κ ≤ ℓκ)
    (hℓKT : Real.log (116341 / 100000 * Tr) ≤ ℓKT) :
    radAveragedShift E₀ (11 / 20) Tr κ
      ≤ 3 * (2553 / 10000) + 11 / 20 * ℓκ + 11 / 20 / κ + 11 / 20 * (693148 / 1000000)
        + (2 - 11 / 20) + 4 / 25 + 2 * (1253315 / 1000000)
        + 11 / 20 * (1 + 693148 / 1000000 + 3912024 / 1000000) + 2 * (11 / 20) * ℓKT := by
  have hd := driftRadSharpOf_le_half hE₀ hE₀1
  have hlog2 : Real.log 2 ≤ 693148 / 1000000 := by linarith [Real.log_two_lt_d9]
  have hlog50 : Real.log (2 * ((25 : ℕ) : ℝ)) ≤ 3912024 / 1000000 := by
    rw [show (2 : ℝ) * ((25 : ℕ) : ℝ) = 50 by norm_num]
    exact log_fifty_le
  have hpi := Real.pi_lt_d6
  have hsq : √(Real.pi * 1 / 2) ≤ 1253315 / 1000000 := by
    have h : Real.pi * 1 / 2 ≤ (1253315 / 1000000) ^ 2 := by nlinarith
    calc √(Real.pi * 1 / 2) ≤ √((1253315 / 1000000) ^ 2) := Real.sqrt_le_sqrt h
      _ = 1253315 / 1000000 := Real.sqrt_sq (by norm_num)
  have hK := radAveragedK_le_half hE₀1
  have hK1 := one_le_radAveragedK hE₀
  have hlogKT : Real.log (radAveragedK E₀ * Tr) ≤ ℓKT :=
    le_trans (Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_right hK (by linarith))) hℓKT
  unfold radAveragedShift result1SharpShift
  push_cast
  have h1 : 11 / 20 * Real.log κ ≤ 11 / 20 * ℓκ := mul_le_mul_of_nonneg_left hℓκ (by norm_num)
  have h2 : 2 * (11 / 20) * Real.log (radAveragedK E₀ * Tr) ≤ 2 * (11 / 20) * ℓKT :=
    mul_le_mul_of_nonneg_left hlogKT (by norm_num)
  have h3 : 11 / 20 * Real.log 2 ≤ 11 / 20 * (693148 / 1000000) :=
    mul_le_mul_of_nonneg_left hlog2 (by norm_num)
  have h4 : 11 / 20 * (1 + Real.log 2 + Real.log (2 * 25))
      ≤ 11 / 20 * (1 + 693148 / 1000000 + 3912024 / 1000000) := by
    have : Real.log (2 * 25) ≤ 3912024 / 1000000 := by
      have := hlog50
      push_cast at this
      exact this
    exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  linarith

/-- `radBlockBadConst E₀ (11/20) ≤ e^{18.42}` for `E₀ ≤ 1/33680`
(`RMF.radBlockBadConst_mul_le_half` without its `e⁸`). -/
lemma radBlockBadConst_le_exp {E₀ : ℝ} (hE₀1 : E₀ ≤ 1 / 33680) :
    radBlockBadConst E₀ (11 / 20) ≤ Real.exp (1842 / 100) := by
  have h := radBlockBadConst_mul_le_half hE₀1
  have e : Real.exp (2642 / 100) = Real.exp (1842 / 100) * Real.exp 8 := by
    rw [← Real.exp_add]; norm_num
  rw [e] at h
  exact le_of_mul_le_mul_right h (Real.exp_pos 8)

/-- **A window's chaos constant on a cell of `q`**: for `q ∈ [a, b] ⊆ [0, 1]`,
`E₀ ≤ 1/33680`, a level shift `K ≤ e^{ℓK}` and the leaves' numerals,
`c.const E₀ q K ≤ max j d` (`RMF.shiftMomentConst_le_exp`, `RMF.certD_le_end`). -/
lemma winChaosConst_le_cell {a b q E₀ K ℓK Ci' s' U cb e j d : ℝ} (c : WinChaos)
    (hq0 : 0 ≤ q) (haq : a ≤ q) (hqb : q ≤ b) (hb1 : b ≤ 1)
    (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) (hK0 : 0 ≤ K) (hK : K ≤ Real.exp ℓK)
    (hTr : 4 < c.Tr) (hκ : 1 ≤ c.kap) (hA : 0 ≤ c.A) (hlam : 0 < c.lam)
    (hCi : radAveragedConst E₀ (11 / 20) c.Tr c.kap ≤ Ci')
    (hs : radAveragedShift E₀ (11 / 20) c.Tr c.kap ≤ s')
    (hLA : 1842 / 100 + ℓK - 2 * c.A ≤ 0) (hU : (c.A + s') * (1 - a) ≤ U)
    (hcb1 : 1 ≤ (1 + 1 / c.lam) * (10102 / 10000) * Ci')
    (hcb : (1 + 1 / c.lam) * (10102 / 10000) * Ci' ≤ cb)
    (he : (1 ≤ U ∧ e = b) ∨ (0 < U ∧ U ≤ 1 ∧ e = a))
    (hJ : Real.exp (b * Real.log (1 + c.lam)) ≤ j)
    (hD : Real.exp (b * Real.log cb) * (Real.exp (e * Real.log U)
        + Real.exp ((1 - b) * (1842 / 100 + ℓK - 2 * c.A))
          * (Real.exp (b * Real.log (U + 1)) * (1156519 / 1000000) + 181016 / 1000000))
      + 135336 / 1000000 * Real.exp ((1 - b) * (1842 / 100 + ℓK - 2 * c.A))
        * Real.exp (b * Real.log 1) ≤ d) :
    c.const E₀ q K ≤ max j d := by
  have hq1 : q ≤ 1 := le_trans hqb hb1
  have hCi0 : 0 ≤ radAveragedConst E₀ (11 / 20) c.Tr c.kap :=
    le_trans zero_le_one (one_le_radAveragedConst hE₀ (by norm_num) (by norm_num) hTr hκ)
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num) hTr hκ
  have hCb0 : 0 ≤ radBlockBadConst E₀ (11 / 20) * K :=
    mul_nonneg (radBlockBadConst_pos E₀ (by norm_num)).le hK0
  have hCbL : radBlockBadConst E₀ (11 / 20) * K ≤ Real.exp (1842 / 100 + ℓK) := by
    rw [Real.exp_add]
    exact mul_le_mul (radBlockBadConst_le_exp hE₀1) hK hK0 (Real.exp_pos _).le
  have hAs : 0 ≤ c.A + radAveragedShift E₀ (11 / 20) c.Tr c.kap := by linarith
  have hUq : (c.A + radAveragedShift E₀ (11 / 20) c.Tr c.kap) * (1 - q) ≤ U := by
    refine le_trans ?_ hU
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h := shiftMomentConst_le_exp (C₁ := 1) (N := 1)
    (Ci := radAveragedConst E₀ (11 / 20) c.Tr c.kap) (Ci' := Ci')
    (Cb := radBlockBadConst E₀ (11 / 20) * K) (LB := 1842 / 100 + ℓK)
    (s := radAveragedShift E₀ (11 / 20) c.Tr c.kap) (U := U) (IS := 10102 / 10000)
    (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000) (EM2 := 135336 / 1000000) (A := c.A)
    (lam := c.lam) (δ := 1 / 50) (q := q) hq0 hq1 zero_le_one le_rfl hCi0 hCi hCb0 hCbL hAs hUq
    hlam (by norm_num) inv_sqrt_one_sub_fiftieth_le inv_one_sub_exp_neg_two_le
    exp_neg_two_mul_inv_sq_le exp_neg_two_le_cert
  have hJq : Real.exp (q * Real.log (1 * (1 + c.lam))) ≤ j := by
    rw [one_mul]
    refine le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqb ?_)) hJ
    exact Real.log_nonneg (by linarith)
  have hDq := le_trans (certD_le_end (c := (1 + 1 / c.lam) * (10102 / 10000) * Ci') (U := U)
    (LB := 1842 / 100 + ℓK) (A := c.A) (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000)
    (EM2 := 135336 / 1000000) (N := 1) (cb := cb) (e := e) hq0 haq hqb hb1 hcb1 hcb he hLA
    (by norm_num) (by norm_num) (by norm_num) le_rfl) hD
  unfold WinChaos.const
  exact le_trans h (max_le_max hJq hDq)

/-! ### Window groups, summed -/

/-- **One group, from per-window bounds**: `w_k ≤ e^{-ak}c̄` on `[s, t)` gives
`(1 - e^{-a})·∑_{s≤k<t} w_k ≤ c̄(e^{-as} - e^{-at})`. -/
lemma one_sub_exp_neg_mul_sum_le_group {a : ℝ} (ha : 0 < a) {s t : ℕ} (hst : s ≤ t)
    {w : ℕ → ℝ} {cb : ℝ} (hw : ∀ k ∈ Finset.Ico s t, w k ≤ Real.exp (-(a * k)) * cb) :
    (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico s t, w k
      ≤ cb * (Real.exp (-(a * s)) - Real.exp (-(a * t))) := by
  have h1 : (0 : ℝ) ≤ 1 - Real.exp (-a) := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h2 := Finset.sum_le_sum hw
  rw [← Finset.sum_mul] at h2
  calc (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico s t, w k
      ≤ (1 - Real.exp (-a)) * ((∑ k ∈ Finset.Ico s t, Real.exp (-(a * k))) * cb) :=
        mul_le_mul_of_nonneg_left h2 h1
    _ = cb * ((1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico s t, Real.exp (-(a * k))) := by ring
    _ = cb * (Real.exp (-(a * s)) - Real.exp (-(a * t))) := by
        rw [one_sub_exp_neg_mul_sum_Ico ha hst]

/-! ### One window at the large range's parameters -/

/-- **The window's (PF) bracket is negative**: for `x ≥ exp(e^{110})`, `k ≥ 4` with
`(3/2)e^k ≤ log y`, `9.0028/((3/2)e^k) + 2σ((3/2)e^k + 1/100 + log 4 + 4) ≤ 3/20`. -/
lemma thetaPF_bracket_half {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ} (hk : 4 ≤ k)
    (hky : 3 / 2 * Real.exp k ≤ Real.log (halfY x)) :
    9.0028 / (3 / 2 * Real.exp k)
      + 2 * halfSigma x * (3 / 2 * Real.exp k + 1 / 100 + Real.log 4 + 4) ≤ 3 / 20 := by
  obtain ⟨-, hL, hΛ, -, -, -⟩ := half_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ0 : 0 ≤ halfSigma x := by rw [halfSigma]; positivity
  have hσy := halfSigma_mul_log_le hx
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have he4 : (54 : ℝ) ≤ Real.exp k := by
    have h : Real.exp 4 ≤ Real.exp k := Real.exp_le_exp.2 hkR
    have h4 : (54 : ℝ) ≤ Real.exp 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
      have := Real.exp_one_gt_d9
      have h5 : (2.718 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      linarith [show (54 : ℝ) ≤ 2.718 ^ 4 by norm_num]
    linarith
  have h1 : 9.0028 / (3 / 2 * Real.exp k) ≤ 9.0028 / 81 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  -- `σ ≤ 1/(16Λ log y) ≤ 1/1000` and `2σ log y ≤ 1/(8Λ) ≤ 1/880`
  have hlogy : 1 ≤ Real.log (halfY x) := by linarith
  have hσ1 : halfSigma x ≤ 1 / 1000 := by
    have h16 : 1 / (16 * Real.log (Real.log x)) ≤ 1 / 1760 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have := mul_le_mul_of_nonneg_left hlogy hσ0
    linarith
  have hl4 : Real.log 4 ≤ 14 / 10 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have h2 : 2 * halfSigma x * (3 / 2 * Real.exp k) ≤ 2 / 1760 := by
    have h16 : 1 / (16 * Real.log (Real.log x)) ≤ 1 / 1760 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have := mul_le_mul_of_nonneg_left hky hσ0
    nlinarith
  have h3 : 2 * halfSigma x * (1 / 100 + Real.log 4 + 4)
      ≤ 2 * (1 / 1000) * (1 / 100 + 14 / 10 + 4) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  nlinarith

/-- **A chaos window at the large range's parameters**: for `x ≥ exp(e^{110})`, `a ≤ q ≤ b ≤ ½`,
`k₁ ≤ k < J₀` with room, and bounds `G_{k₁}(a)^b ≤ G`, `C_k ≤ A` on the chaos constant,
`(Λ/n_k)^{1/4} ≤ ρ` (`ρ ≥ 1`):

`b_k ≤ e^{-q(1-2q)k}·((3/2)^{-q(1-2q)}Λ^{-q/2}·G·A·(1-b)^{-b}·ρ)`. -/
lemma uWindowBound_le_chaos {x q a b G A ρ : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hq0 : 0 ≤ q) (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2) {P : ℕ → WinChaos} {k k₁ : ℕ}
    (hk₁ : k₁ ≤ k) (hk : k ∈ Finset.Ico 4 (tenJ x)) (hPk : (P k).Valid)
    (hroom : (P k).N ≤ harperBlockCount (uOffset k) (halfY x))
    (hG : thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ b ≤ G)
    (hA : (P k).const (1 / (16 * Real.log (Real.log x))) q
      (Real.exp ((uOffset k : ℝ) - k)) ≤ A)
    (hρ1 : 1 ≤ ρ)
    (hρ : (Real.log (Real.log x) / harperBlockCount (uOffset k) (halfY x)) ^ (1 / 4 : ℝ) ≤ ρ)
    (hn : 0 < (harperBlockCount (uOffset k) (halfY x) : ℝ)) :
    uWindowBound P q x k ≤ Real.exp (-(q * (1 - 2 * q) * k))
      * ((3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
        * (G * A * (1 - b) ^ (-b) * ρ)) := by
  obtain ⟨-, hL, hΛ, -, -, -⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, -, -, -⟩ := halfY_facts hx
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  rw [Finset.mem_Ico] at hk
  have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [tenJ] at hk; exact hk.2)
  set n := (harperBlockCount (uOffset k) (halfY x) : ℝ) with hndef
  set Λ := Real.log (Real.log x) with hΛdef
  -- the four factors
  have hPF := thetaPF_le (σ := halfSigma x) (θ := 3 / 2) (by norm_num) hq0 (by linarith) (k := k)
    (thetaPF_bracket_half hx hk.1 hky)
  have hG1 : 1 ≤ thetaWindowConstQ (3 / 2) q k (halfY x) :=
    one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) k (halfY x)
  have hGq : thetaWindowConstQ (3 / 2) q k (halfY x) ^ q ≤ G := by
    have h1 : thetaWindowConstQ (3 / 2) q k (halfY x) ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) :=
      le_trans (thetaWindowConstQ_anti_q (by norm_num) haq k (halfY x))
        (thetaWindowConstQ_anti_k (by norm_num) (by linarith) hk₁ (halfY x))
    have h2 : 1 ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) := le_trans hG1 h1
    calc thetaWindowConstQ (3 / 2) q k (halfY x) ^ q
        ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ q :=
          Real.rpow_le_rpow (by linarith) h1 hq0
      _ ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ b := Real.rpow_le_rpow_of_exponent_le h2 hqb
      _ ≤ G := hG
  have hχ : (1 + (1 - q) * Real.sqrt n) ^ (-q) ≤ (1 - b) ^ (-b) * (Λ ^ (-(q / 2)) * ρ) := by
    refine le_trans (one_add_mul_sqrt_rpow_neg_le hq0 (by linarith) hn) ?_
    refine mul_le_mul (one_sub_rpow_neg_self_le hq0 hqb (by linarith)) ?_
      (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg (by linarith) _)
    -- `n^{-q/2} = Λ^{-q/2}(Λ/n)^{q/2} ≤ Λ^{-q/2}ρ`
    have e : n ^ (-(q / 2)) = Λ ^ (-(q / 2)) * (Λ / n) ^ (q / 2) := by
      rw [Real.div_rpow hΛ0.le hn.le, Real.rpow_neg hn.le, Real.rpow_neg hΛ0.le]
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hΛ0.le _)
    rcases le_or_gt 1 (Λ / n) with h1 | h1
    · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) hρ
    · have : (Λ / n) ^ (q / 2) ≤ 1 :=
        Real.rpow_le_one (div_nonneg hΛ0.le hn.le) h1.le (by linarith)
      linarith
  -- the chaos branch
  have hCq0 : 0 ≤ (P k).const (1 / (16 * Λ)) q (Real.exp ((uOffset k : ℝ) - k)) := by
    have hl := hPk.lam
    unfold WinChaos.const shiftMomentConst
    exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
  have hchi0 : 0 ≤ (1 + (1 - q) * Real.sqrt n) ^ (-q) := by
    have : 0 ≤ 1 - q := by linarith
    exact Real.rpow_nonneg (by positivity) _
  unfold uWindowBound
  rw [if_pos hroom]
  have hmin : min 1 ((P k).const (1 / (16 * Λ)) q (Real.exp ((uOffset k : ℝ) - k))
      * (1 + (1 - q) * Real.sqrt n) ^ (-q)) ≤ A * ((1 - b) ^ (-b) * (Λ ^ (-(q / 2)) * ρ)) :=
    le_trans (min_le_right _ _) (mul_le_mul hA hχ hchi0 (le_trans hCq0 hA))
  have hPF0 : 0 ≤ thetaPF (halfSigma x) (3 / 2) q k := thetaPF_nonneg _ _ _ _ (by norm_num)
  have hGq0 : 0 ≤ thetaWindowConstQ (3 / 2) q k (halfY x) ^ q := Real.rpow_nonneg (by linarith) _
  have hmin0 : 0 ≤ min 1 ((P k).const (1 / (16 * Λ)) q (Real.exp ((uOffset k : ℝ) - k))
      * (1 + (1 - q) * Real.sqrt n) ^ (-q)) := le_min zero_le_one (mul_nonneg hCq0 hchi0)
  calc thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (halfY x) ^ q
        * min 1 ((P k).const (1 / (16 * Λ)) q (Real.exp ((uOffset k : ℝ) - k))
          * (1 + (1 - q) * Real.sqrt n) ^ (-q))
      ≤ ((3 / 2) ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k))) * G
        * (A * ((1 - b) ^ (-b) * (Λ ^ (-(q / 2)) * ρ))) :=
        mul_le_mul (mul_le_mul hPF hGq hGq0 (by positivity)) hmin hmin0
          (mul_nonneg (by positivity) (le_trans hGq0 hGq))
    _ = Real.exp (-(q * (1 - 2 * q) * k)) * ((3 / 2) ^ (-(q * (1 - 2 * q))) * Λ ^ (-(q / 2))
          * (G * A * (1 - b) ^ (-b) * ρ)) := by ring

/-- **A Jensen window at the large range's parameters**: `b_k ≤ e^{-q(1-2q)k}·((3/2)^{-q(1-2q)}G)`
for `k₁ ≤ k < J₀` and `G_{k₁}(a)^b ≤ G`. -/
lemma uWindowBound_le_jensen {x q a b G : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hq0 : 0 ≤ q) (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2) {P : ℕ → WinChaos} {k k₁ : ℕ}
    (hk₁ : k₁ ≤ k) (hk : k ∈ Finset.Ico 4 (tenJ x)) (hPk : (P k).Valid)
    (hG : thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ b ≤ G) :
    uWindowBound P q x k
      ≤ Real.exp (-(q * (1 - 2 * q) * k)) * ((3 / 2) ^ (-(q * (1 - 2 * q))) * G) := by
  obtain ⟨-, hL, hΛ, -, -, -⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, -, -, -⟩ := halfY_facts hx
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  rw [Finset.mem_Ico] at hk
  have hky := tenJ_window hlogy (by omega : k ≠ 0) (by rw [tenJ] at hk; exact hk.2)
  have hPF := thetaPF_le (σ := halfSigma x) (θ := 3 / 2) (by norm_num) hq0 (by linarith) (k := k)
    (thetaPF_bracket_half hx hk.1 hky)
  have hG1 : 1 ≤ thetaWindowConstQ (3 / 2) q k (halfY x) :=
    one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) k (halfY x)
  have hGq : thetaWindowConstQ (3 / 2) q k (halfY x) ^ q ≤ G := by
    have h1 : thetaWindowConstQ (3 / 2) q k (halfY x) ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) :=
      le_trans (thetaWindowConstQ_anti_q (by norm_num) haq k (halfY x))
        (thetaWindowConstQ_anti_k (by norm_num) (by linarith) hk₁ (halfY x))
    have h2 : 1 ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) := le_trans hG1 h1
    calc thetaWindowConstQ (3 / 2) q k (halfY x) ^ q
        ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ q :=
          Real.rpow_le_rpow (by linarith) h1 hq0
      _ ≤ thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ b := Real.rpow_le_rpow_of_exponent_le h2 hqb
      _ ≤ G := hG
  have hPF0 : 0 ≤ thetaPF (halfSigma x) (3 / 2) q k := thetaPF_nonneg _ _ _ _ (by norm_num)
  have hGq0 : 0 ≤ thetaWindowConstQ (3 / 2) q k (halfY x) ^ q := Real.rpow_nonneg (by linarith) _
  have hfac : (if (P k).N ≤ harperBlockCount (uOffset k) (halfY x) then
      min 1 ((P k).const (1 / (16 * Real.log (Real.log x))) q (Real.exp ((uOffset k : ℝ) - k))
        * (1 + (1 - q) * Real.sqrt (harperBlockCount (uOffset k) (halfY x) : ℝ)) ^ (-q))
      else 1) ≤ 1 := by
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  have hfac0 : 0 ≤ (if (P k).N ≤ harperBlockCount (uOffset k) (halfY x) then
      min 1 ((P k).const (1 / (16 * Real.log (Real.log x))) q (Real.exp ((uOffset k : ℝ) - k))
        * (1 + (1 - q) * Real.sqrt (harperBlockCount (uOffset k) (halfY x) : ℝ)) ^ (-q))
      else 1) := by
    split_ifs
    · refine le_min zero_le_one (mul_nonneg ?_ ?_)
      · have hl := hPk.lam
        unfold WinChaos.const shiftMomentConst
        exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
      · have : 0 ≤ 1 - q := by linarith
        exact Real.rpow_nonneg (by positivity) _
    · exact zero_le_one
  unfold uWindowBound
  calc thetaPF (halfSigma x) (3 / 2) q k * thetaWindowConstQ (3 / 2) q k (halfY x) ^ q * _
      ≤ ((3 / 2) ^ (-(q * (1 - 2 * q))) * Real.exp (-(q * (1 - 2 * q) * k))) * G * 1 :=
        mul_le_mul (mul_le_mul hPF hGq hGq0 (by positivity)) hfac hfac0
          (mul_nonneg (by positivity) (le_trans hGq0 hGq))
    _ = Real.exp (-(q * (1 - 2 * q) * k)) * ((3 / 2) ^ (-(q * (1 - 2 * q))) * G) := by ring

/-! ### The far windows' parameters -/

/-- The far windows' chaos parameters of (U): level `A₀ + j` and room `N₀ + 20j` for far window
`j`, the level growing with the window's height as its level shift `e^{2j+102}` does. -/
def uFarParams (lam Tr kap A₀ : ℝ) (N₀ : ℕ) : FarChaos :=
  ⟨lam, Tr, kap, fun j => A₀ + j, fun j => N₀ + 20 * j⟩

/-- `√(N₀ + 20j) ≤ √N₀ + j/5` once `√N₀ ≥ 50`. -/
lemma sqrt_add_twenty_mul_le {N₀ : ℝ} (hN : 2500 ≤ N₀) (j : ℝ) (hj : 0 ≤ j) :
    Real.sqrt (N₀ + 20 * j) ≤ Real.sqrt N₀ + j / 5 := by
  have hs : 50 ≤ Real.sqrt N₀ := by
    rw [show (50 : ℝ) = Real.sqrt (50 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_le_left (by positivity)]
  have hsq : Real.sqrt N₀ ^ 2 = N₀ := Real.sq_sqrt (by linarith)
  nlinarith

/-- The far windows' parameters are valid for every `j` once they are at `j = 0` and `N₀ ≥ 2500`:
each window adds `1/4 + 3/20 ≤ 20/50` to the room condition's two sides' difference. -/
lemma uFarParams_valid {lam Tr kap A₀ : ℝ} {N₀ : ℕ} (hTr : 4 < Tr) (hkap : 1 ≤ kap)
    (hlam : 1 ≤ lam) (hA : 20 ≤ A₀) (hN : 2500 ≤ N₀)
    (hroom : A₀ / 4 + 3 * Real.sqrt (N₀ : ℝ) / 4 + 1 ≤ 1 / 50 * N₀) :
    (uFarParams lam Tr kap A₀ N₀).Valid where
  Tr := hTr
  kap := hkap
  lam := hlam
  A j := by
    change 20 ≤ A₀ + (j : ℝ)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  N j := by
    change 2000 ≤ N₀ + 20 * j
    omega
  room j := by
    change (A₀ + (j : ℝ)) / 4 + 3 * Real.sqrt ((N₀ + 20 * j : ℕ) : ℝ) / 4 + 1
      ≤ 1 / 50 * ((N₀ + 20 * j : ℕ) : ℝ)
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hN' : (2500 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN
    have hs := sqrt_add_twenty_mul_le hN' (j : ℝ) hj
    push_cast
    linarith

set_option maxHeartbeats 1000000 in
-- a long chain of explicit bounds, no search
/-- **A far window's chaos constant, linear in the window**: at `A_j = A₀ + j` and level shift
`e^{2j+102}` the bad sets' factor `(C_b e^{2j+102}e^{-2A_j})^{1/3}` does not depend on `j`, and
`u_j = (A_j + s)/3` enters through `u^{2/3}` (Bernoulli, `rpow_one_add_le_one_add_mul_self`):
`const_j ≤ M + D·j` from numerals `c ≥ (1 + 1/λ)·1.0102·C_i'`, `(A₀ + s')/3 ≤ U`,
`E ≥ e^{(18.42 + 102 - 2A₀)/3}`, and the two branches' certificates `hM1`, `hM2`, `hD`. -/
lemma uFarParams_const_le {E₀ lam Tr kap A₀ Ci' s' c U E M D : ℝ} {N₀ : ℕ}
    (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) (hTr : 4 < Tr) (hkap : 1 ≤ kap) (hlam : 0 < lam)
    (hA : 20 ≤ A₀)
    (hCi : radAveragedConst E₀ (11 / 20) Tr kap ≤ Ci')
    (hs : radAveragedShift E₀ (11 / 20) Tr kap ≤ s')
    (hc : (1 + 1 / lam) * (10102 / 10000) * Ci' ≤ c) (hU : (A₀ + s') / 3 ≤ U)
    (hE : Real.exp ((1842 / 100 + 102 - 2 * A₀) / 3) ≤ E)
    (hM1 : Real.exp (2 / 3 * Real.log (1 + lam)) ≤ M)
    (hM2 : Real.exp (2 / 3 * Real.log c) * (Real.exp (2 / 3 * Real.log U)
        + E * (Real.exp (2 / 3 * Real.log (U + 1)) * (1156519 / 1000000) + 181016 / 1000000))
      + 135336 / 1000000 * E ≤ M)
    (hD : Real.exp (2 / 3 * Real.log c) * (2 / 9) * (Real.exp (-(1 / 3 * Real.log (A₀ / 3)))
      + E * (1156519 / 1000000) * Real.exp (-(1 / 3 * Real.log (A₀ / 3 + 1)))) ≤ D)
    (j : ℕ) :
    (uFarParams lam Tr kap A₀ N₀).const E₀ j ≤ M + D * j := by
  change shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) Tr kap)
      (radBlockBadConst E₀ (11 / 20) * Real.exp (2 * (j : ℝ) + 102)) (A₀ + j)
      (radAveragedShift E₀ (11 / 20) Tr kap) lam (1 / 50) (2 / 3) ≤ M + D * j
  unfold shiftMomentConst
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hCi0 : 0 ≤ radAveragedConst E₀ (11 / 20) Tr kap :=
    le_trans zero_le_one (one_le_radAveragedConst hE₀ (by norm_num) (by norm_num) hTr hkap)
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num) hTr hkap
  have hCb0 : 0 < radBlockBadConst E₀ (11 / 20) := radBlockBadConst_pos E₀ (by norm_num)
  have hCbL : radBlockBadConst E₀ (11 / 20) ≤ Real.exp (1842 / 100) := radBlockBadConst_le_exp hE₀1
  set s := radAveragedShift E₀ (11 / 20) Tr kap with hsdef
  set Ci := radAveragedConst E₀ (11 / 20) Tr kap with hCidef
  set Cb := radBlockBadConst E₀ (11 / 20) with hCbdef
  -- the bad sets' factor does not depend on `j`
  have hEb : (Cb * Real.exp (2 * (j : ℝ) + 102) * Real.exp (-(2 * (A₀ + j)))) ^ (1 - 2 / 3 : ℝ)
      ≤ E := by
    have e1 : Cb * Real.exp (2 * (j : ℝ) + 102) * Real.exp (-(2 * (A₀ + j)))
        = Cb * Real.exp (102 - 2 * A₀) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e1]
    have h1 : Cb * Real.exp (102 - 2 * A₀) ≤ Real.exp (1842 / 100 + 102 - 2 * A₀) := by
      rw [show (1842 / 100 : ℝ) + 102 - 2 * A₀ = 1842 / 100 + (102 - 2 * A₀) by ring,
        Real.exp_add]
      exact mul_le_mul_of_nonneg_right hCbL (Real.exp_pos _).le
    refine le_trans (Real.rpow_le_rpow (by positivity) h1 (by norm_num)) ?_
    rw [← Real.exp_mul]
    refine le_trans (le_of_eq ?_) hE
    congr 1
    ring
  have hE0 : 0 ≤ E := le_trans (Real.rpow_nonneg (by positivity) _) hEb
  -- Bernoulli for `t ↦ t^{2/3}`
  have hu0 : 0 < A₀ / 3 := by linarith
  have hbern : ∀ v h : ℝ, 0 < v → 0 ≤ h →
      (v + h) ^ (2 / 3 : ℝ) ≤ v ^ (2 / 3 : ℝ) + 2 / 3 * v ^ (-(1 / 3 : ℝ)) * h := by
    intro v h hv hh
    have e : v + h = v * (1 + h / v) := by field_simp
    rw [e, Real.mul_rpow hv.le (by positivity)]
    have hhv : 0 ≤ h / v := by positivity
    have hb := rpow_one_add_le_one_add_mul_self (s := h / v) (by linarith)
      (p := 2 / 3) (by norm_num) (by norm_num)
    have hv23 : 0 ≤ v ^ (2 / 3 : ℝ) := Real.rpow_nonneg hv.le _
    have e2 : v ^ (2 / 3 : ℝ) * (2 / 3 * (h / v)) = 2 / 3 * v ^ (-(1 / 3 : ℝ)) * h := by
      rw [show (-(1 / 3 : ℝ)) = 2 / 3 - 1 by norm_num, Real.rpow_sub hv, Real.rpow_one]
      field_simp
    calc v ^ (2 / 3 : ℝ) * (1 + h / v) ^ (2 / 3 : ℝ) ≤ v ^ (2 / 3 : ℝ) * (1 + 2 / 3 * (h / v)) :=
          mul_le_mul_of_nonneg_left hb hv23
      _ = v ^ (2 / 3 : ℝ) + 2 / 3 * v ^ (-(1 / 3 : ℝ)) * h := by rw [mul_add, mul_one, e2]
  -- `u_j^{2/3}` and `(u_j + 1)^{2/3}`
  have hA_j : (A₀ + (j : ℝ) + s) * (1 - 2 / 3) = (A₀ + s) / 3 + j / 3 := by ring
  have hU1 : (A₀ + s) / 3 ≤ U := le_trans (by linarith) hU
  have hlow : A₀ / 3 ≤ (A₀ + s) / 3 := by linarith
  have hle : (A₀ / 3) ^ (-(1 / 3 : ℝ)) = Real.exp (-(1 / 3 * Real.log (A₀ / 3))) := by
    rw [rpow_eq_exp_mul_log hu0]; ring_nf
  have hle1 : (A₀ / 3 + 1) ^ (-(1 / 3 : ℝ)) = Real.exp (-(1 / 3 * Real.log (A₀ / 3 + 1))) := by
    rw [rpow_eq_exp_mul_log (by linarith)]; ring_nf
  set P₀ := Real.exp (-(1 / 3 * Real.log (A₀ / 3))) with hP₀
  set P₁ := Real.exp (-(1 / 3 * Real.log (A₀ / 3 + 1))) with hP₁
  have hP₀0 : 0 ≤ P₀ := (Real.exp_pos _).le
  have hP₁0 : 0 ≤ P₁ := (Real.exp_pos _).le
  have hu23 : ((A₀ + (j : ℝ) + s) * (1 - 2 / 3)) ^ (2 / 3 : ℝ)
      ≤ Real.exp (2 / 3 * Real.log U) + 2 / 9 * P₀ * j := by
    rw [hA_j]
    have hb := hbern ((A₀ + s) / 3) (j / 3) (by linarith) (by positivity)
    have h1 : ((A₀ + s) / 3) ^ (2 / 3 : ℝ) ≤ Real.exp (2 / 3 * Real.log U) :=
      le_trans (Real.rpow_le_rpow (by linarith) hU1 (by norm_num))
        (rpow_le_exp_mul_log (by linarith) _)
    have h2 : ((A₀ + s) / 3) ^ (-(1 / 3 : ℝ)) ≤ P₀ := by
      rw [← hle]
      exact Real.rpow_le_rpow_of_nonpos hu0 hlow (by norm_num)
    have h3 : 2 / 3 * ((A₀ + s) / 3) ^ (-(1 / 3 : ℝ)) * (j / 3) ≤ 2 / 9 * P₀ * j := by
      have h4 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 / 9 * j)
      calc 2 / 3 * ((A₀ + s) / 3) ^ (-(1 / 3 : ℝ)) * (j / 3)
          = ((A₀ + s) / 3) ^ (-(1 / 3 : ℝ)) * (2 / 9 * j) := by ring
        _ ≤ P₀ * (2 / 9 * j) := h4
        _ = 2 / 9 * P₀ * j := by ring
    linarith
  have hu231 : ((A₀ + (j : ℝ) + s) * (1 - 2 / 3) + 1) ^ (2 / 3 : ℝ)
      ≤ Real.exp (2 / 3 * Real.log (U + 1)) + 2 / 9 * P₁ * j := by
    rw [hA_j]
    have e : (A₀ + s) / 3 + j / 3 + 1 = ((A₀ + s) / 3 + 1) + j / 3 := by ring
    rw [e]
    have hb := hbern ((A₀ + s) / 3 + 1) (j / 3) (by linarith) (by positivity)
    have h1 : ((A₀ + s) / 3 + 1) ^ (2 / 3 : ℝ) ≤ Real.exp (2 / 3 * Real.log (U + 1)) :=
      le_trans (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
        (rpow_le_exp_mul_log (by linarith) _)
    have h2 : ((A₀ + s) / 3 + 1) ^ (-(1 / 3 : ℝ)) ≤ P₁ := by
      rw [← hle1]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have h3 : 2 / 3 * ((A₀ + s) / 3 + 1) ^ (-(1 / 3 : ℝ)) * (j / 3) ≤ 2 / 9 * P₁ * j := by
      have h4 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 / 9 * j)
      calc 2 / 3 * ((A₀ + s) / 3 + 1) ^ (-(1 / 3 : ℝ)) * (j / 3)
          = ((A₀ + s) / 3 + 1) ^ (-(1 / 3 : ℝ)) * (2 / 9 * j) := by ring
        _ ≤ P₁ * (2 / 9 * j) := h4
        _ = 2 / 9 * P₁ * j := by ring
    linarith
  -- the decomposition branch's constant
  have hsq : 0 < Real.sqrt (1 - 1 / 50) := Real.sqrt_pos.2 (by norm_num)
  have hlam1 : 0 ≤ 1 + lam⁻¹ := by have := inv_nonneg.2 hlam.le; linarith
  have hcC : (1 + lam⁻¹) * Ci / Real.sqrt (1 - 1 / 50) ≤ c := by
    refine le_trans ?_ hc
    rw [div_eq_mul_inv, one_div lam]
    calc (1 + lam⁻¹) * Ci * (Real.sqrt (1 - 1 / 50))⁻¹
        = (1 + lam⁻¹) * (Real.sqrt (1 - 1 / 50))⁻¹ * Ci := by ring
      _ ≤ (1 + lam⁻¹) * (10102 / 10000) * Ci' :=
          mul_le_mul (mul_le_mul_of_nonneg_left inv_sqrt_one_sub_fiftieth_le hlam1) hCi hCi0
            (by positivity)
  have hcC0 : 0 ≤ (1 + lam⁻¹) * Ci / Real.sqrt (1 - 1 / 50) :=
    div_nonneg (mul_nonneg hlam1 hCi0) hsq.le
  set Cq := Real.exp (2 / 3 * Real.log c) with hCq
  have hc23 : ((1 + lam⁻¹) * Ci / Real.sqrt (1 - 1 / 50)) ^ (2 / 3 : ℝ) ≤ Cq :=
    le_trans (Real.rpow_le_rpow hcC0 hcC (by norm_num)) (rpow_le_exp_mul_log (le_trans hcC0 hcC) _)
  have hCq0 : 0 ≤ Cq := (Real.exp_pos _).le
  -- the Jensen branch
  have hJ : (1 * (1 + lam)) ^ (2 / 3 : ℝ) ≤ M := by
    rw [one_mul]
    exact le_trans (rpow_le_exp_mul_log (by linarith) _) hM1
  -- the two brackets
  have hS1 := inv_one_sub_exp_neg_two_le
  have hS2 := exp_neg_two_mul_inv_sq_le
  have hEM := exp_neg_two_le_cert
  have hS10 : 0 ≤ (1 - Real.exp (-2))⁻¹ := by
    have : Real.exp (-2) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    exact inv_nonneg.2 (by linarith)
  set Eb := (Cb * Real.exp (2 * (j : ℝ) + 102) * Real.exp (-(2 * (A₀ + j)))) ^ (1 - 2 / 3 : ℝ)
    with hEbdef
  have hEb0 : 0 ≤ Eb := Real.rpow_nonneg (by positivity) _
  set uu := (A₀ + (j : ℝ) + s) * (1 - 2 / 3) with huudef
  have huu0 : 0 ≤ uu := by rw [hA_j]; linarith
  set X := Real.exp (2 / 3 * Real.log U) with hX
  set Y := Real.exp (2 / 3 * Real.log (U + 1)) with hY
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hY0 : 0 ≤ Y := (Real.exp_pos _).le
  have hp1 : (uu + 1) ^ (2 / 3 : ℝ) * (1 - Real.exp (-2))⁻¹
      ≤ (Y + 2 / 9 * P₁ * j) * (1156519 / 1000000) :=
    mul_le_mul hu231 hS1 hS10 (by positivity)
  have hbr2 : Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ ≤ 181016 / 1000000 := hS2
  have hbr : (uu + 1) ^ (2 / 3 : ℝ) * (1 - Real.exp (-2))⁻¹
      + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹
      ≤ (Y * (1156519 / 1000000) + 181016 / 1000000) + 2 / 9 * (1156519 / 1000000) * P₁ * j := by
    have e : (Y + 2 / 9 * P₁ * j) * (1156519 / 1000000)
        = Y * (1156519 / 1000000) + 2 / 9 * (1156519 / 1000000) * P₁ * j := by ring
    linarith
  have hbr0 : 0 ≤ (uu + 1) ^ (2 / 3 : ℝ) * (1 - Real.exp (-2))⁻¹
      + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ := by positivity
  have hEbr := mul_le_mul hEb hbr hbr0 hE0
  have hinner : uu ^ (2 / 3 : ℝ) + Eb * ((uu + 1) ^ (2 / 3 : ℝ) * (1 - Real.exp (-2))⁻¹
      + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹)
      ≤ (X + E * (Y * (1156519 / 1000000) + 181016 / 1000000))
        + 2 / 9 * (P₀ + E * (1156519 / 1000000) * P₁) * j := by
    have e : E * ((Y * (1156519 / 1000000) + 181016 / 1000000)
        + 2 / 9 * (1156519 / 1000000) * P₁ * j)
        = E * (Y * (1156519 / 1000000) + 181016 / 1000000)
          + 2 / 9 * (E * (1156519 / 1000000) * P₁) * j := by ring
    have e2 : 2 / 9 * (P₀ + E * (1156519 / 1000000) * P₁) * j
        = 2 / 9 * P₀ * j + 2 / 9 * (E * (1156519 / 1000000) * P₁) * j := by ring
    linarith
  have hinner0 : 0 ≤ uu ^ (2 / 3 : ℝ) + Eb * ((uu + 1) ^ (2 / 3 : ℝ) * (1 - Real.exp (-2))⁻¹
      + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹) := by positivity
  have hmain := mul_le_mul hc23 hinner hinner0 hCq0
  have hEM2E : Real.exp (-2) * Eb * 1 ^ (2 / 3 : ℝ) ≤ 135336 / 1000000 * E := by
    rw [Real.one_rpow, mul_one]
    exact mul_le_mul hEM hEb hEb0 (by norm_num)
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hDj : 0 ≤ D * j := mul_nonneg hD0 hj
  have hsplit : Cq * ((X + E * (Y * (1156519 / 1000000) + 181016 / 1000000))
      + 2 / 9 * (P₀ + E * (1156519 / 1000000) * P₁) * j)
      = Cq * (X + E * (Y * (1156519 / 1000000) + 181016 / 1000000))
        + Cq * (2 / 9) * (P₀ + E * (1156519 / 1000000) * P₁) * j := by ring
  have hDj' : Cq * (2 / 9) * (P₀ + E * (1156519 / 1000000) * P₁) * j ≤ D * j :=
    mul_le_mul_of_nonneg_right hD hj
  refine max_le (le_trans hJ (by linarith)) ?_
  linarith

/-! ### The small pieces -/

/-- **The smooth tail decays**: `T ≤ e^{1.42 - 0.4995Λ}` (`RMF.halfTail_le_one`'s proof, which
stops at `≤ 1`). -/
lemma halfTail_le_decay {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    halfTail x ≤ Real.exp (142 / 100 - 4995 / 10000 * Real.log (Real.log x)) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, -⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 22000 ≤ Real.log (halfY x) := by linarith
  have hlypos : 0 < Real.log (halfY x) := by linarith
  have hU : 0 < Real.log (Real.log x) / 2 := by linarith
  have hκ : 4 ≤ Real.log (Real.log (Real.log x) / 2) := by
    rw [Real.le_log_iff_exp_le hU]
    have : Real.exp 4 ≤ 55 := by interval_decide (trust := kernel)
    linarith
  have h := smoothTailSum_le_rankin_explicit (y := halfY x) hy2 hx0
    (κ := Real.log (Real.log (Real.log x) / 2)) (by linarith)
  rw [Real.exp_log hU] at h
  unfold halfTail
  refine le_trans h ?_
  have hratio : Real.log (Real.log x) / 2 ≤ Real.log x / Real.log (halfY x) := by
    rw [le_div_iff₀ hlypos]
    have h1 := hlogy_le
    rw [halfA, le_div_iff₀ hΛpos] at h1
    linarith
  have hl4 : Real.log 4 + 4 ≤ 6 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfrac : (Real.log 4 + 4) / Real.log (halfY x) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hlypos]
    linarith
  have hf0 : 0 ≤ (Real.log 4 + 4) / Real.log (halfY x) := by positivity
  have e1 : (Real.log (Real.log x) / 2 - 1) * (1 + (Real.log 4 + 4) / Real.log (halfY x))
      ≤ Real.log (Real.log x) / 2 * (1 + 1 / 1000) := by
    have h1 : Real.log (Real.log x) / 2 - 1 ≤ Real.log (Real.log x) / 2 := by linarith
    have h2 : 0 ≤ Real.log (Real.log x) / 2 - 1 := by linarith
    calc (Real.log (Real.log x) / 2 - 1) * (1 + (Real.log 4 + 4) / Real.log (halfY x))
        ≤ Real.log (Real.log x) / 2 * (1 + (Real.log 4 + 4) / Real.log (halfY x)) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ Real.log (Real.log x) / 2 * (1 + 1 / 1000) :=
          mul_le_mul_of_nonneg_left (by linarith) hU.le
  have e2 : 4 * (Real.log (Real.log x) / 2)
      ≤ Real.log (Real.log (Real.log x) / 2) * Real.log x / Real.log (halfY x) := by
    rw [mul_div_assoc]
    exact mul_le_mul hκ hratio hU.le (by linarith)
  have hly_le : Real.log (halfY x) ≤ Real.exp (Real.log (Real.log x)) := by
    rw [hexpΛ]
    obtain ⟨-, -, -, -, -, haL⟩ := half_params hx
    linarith
  calc Real.log (halfY x) * Real.exp (1.42 + (Real.log (Real.log x) / 2 - 1)
        * (1 + (Real.log 4 + 4) / Real.log (halfY x))
        - Real.log (Real.log (Real.log x) / 2) * Real.log x / Real.log (halfY x))
      ≤ Real.exp (Real.log (Real.log x)) * Real.exp (1.42 + Real.log (Real.log x) / 2
          * (1 + 1 / 1000) - 4 * (Real.log (Real.log x) / 2)) :=
        mul_le_mul hly_le (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (Real.log (Real.log x) + (1.42 + Real.log (Real.log x) / 2
          * (1 + 1 / 1000) - 4 * (Real.log (Real.log x) / 2))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (142 / 100 - 4995 / 10000 * Real.log (Real.log x)) :=
        Real.exp_le_exp.2 (by linarith)

/-- The error's arithmetic, decaying: for `s ≥ 10⁶`, `100Λ ≤ s`, `Λ ≥ 1`, `0 ≤ E` and
`E·L⁶ ≤ 46080` (`L = s²`), `(1+s)(2/L² + 2(2Λ/L + 40L³E)) ≤ 7Λ/s`. -/
lemma half_err_arith_decay {s Λ E : ℝ} (hs6 : 1000000 ≤ s) (hsΛ : 100 * Λ ≤ s) (hΛ1 : 1 ≤ Λ)
    (hE0 : 0 ≤ E) (hE : E * (s ^ 2) ^ 6 ≤ 46080) :
    (1 + s) * (2 / (s ^ 2) ^ 2 + 2 * (2 * Λ / s ^ 2 + 40 * (s ^ 2) ^ 3 * E)) ≤ 7 * Λ / s := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hs3 : (1000000000000000000 : ℝ) ≤ s ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hs6 3
    norm_num at this
    linarith
  have hs2 : (1000000000000 : ℝ) ≤ s ^ 2 := by nlinarith
  have t1 : (1 + s) * (2 / (s ^ 2) ^ 2) ≤ Λ / s := by
    rw [show (1 + s) * (2 / (s ^ 2) ^ 2) = (2 + 2 * s) / (s * s ^ 3) by field_simp,
      div_le_div_iff₀ (by positivity) hs0]
    have h1 : (2 + 2 * s) * s ≤ 4 * s ^ 2 := by nlinarith
    have h2 : 4 * s ^ 2 ≤ s * s ^ 3 := by
      have e : s * s ^ 3 = s ^ 2 * s ^ 2 := by ring
      rw [e]
      nlinarith
    have h3 : s * s ^ 3 ≤ Λ * (s * s ^ 3) := by
      have : 0 ≤ s * s ^ 3 := by positivity
      nlinarith
    linarith
  have t2 : (1 + s) * (2 * (2 * Λ / s ^ 2)) ≤ 4 * Λ / s + Λ / s := by
    rw [show (1 + s) * (2 * (2 * Λ / s ^ 2)) = 4 * Λ / s + 4 * Λ / s ^ 2 by field_simp; ring]
    have : 4 * Λ / s ^ 2 ≤ Λ / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith
    linarith
  have t3 : (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) ≤ Λ / s := by
    have h1 : (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) ≤ 160 * s * ((s ^ 2) ^ 3 * E) := by
      have : 0 ≤ (s ^ 2) ^ 3 * E := by positivity
      nlinarith
    have h2 : (s ^ 2) ^ 3 * E * (s ^ 2) ^ 3 ≤ 46080 := by
      calc (s ^ 2) ^ 3 * E * (s ^ 2) ^ 3 = E * (s ^ 2) ^ 6 := by ring
        _ ≤ 46080 := hE
    have h3 : (s ^ 2) ^ 3 * E ≤ 46080 / (s ^ 2) ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      exact h2
    have h4 : 160 * s * (46080 / (s ^ 2) ^ 3) ≤ Λ / s := by
      rw [show 160 * s * (46080 / (s ^ 2) ^ 3) = 7372800 / (s ^ 2 * s ^ 3) by field_simp; ring,
        div_le_div_iff₀ (by positivity) hs0]
      have h6 : (7372800 : ℝ) ≤ s * s ^ 3 := by nlinarith
      have h7 : 7372800 * s ≤ s ^ 2 * s ^ 3 := by nlinarith
      have h8 : s ^ 2 * s ^ 3 ≤ Λ * (s ^ 2 * s ^ 3) := by
        have : 0 ≤ s ^ 2 * s ^ 3 := by positivity
        nlinarith
      linarith
    calc (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) ≤ 160 * s * ((s ^ 2) ^ 3 * E) := h1
      _ ≤ 160 * s * (46080 / (s ^ 2) ^ 3) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ Λ / s := h4
  have hsplit : (1 + s) * (2 / (s ^ 2) ^ 2 + 2 * (2 * Λ / s ^ 2 + 40 * (s ^ 2) ^ 3 * E))
      = (1 + s) * (2 / (s ^ 2) ^ 2) + (1 + s) * (2 * (2 * Λ / s ^ 2))
        + (1 + s) * (2 * (40 * (s ^ 2) ^ 3 * E)) := by ring
  have e7 : 7 * Λ / s = Λ / s + (4 * Λ / s + Λ / s) + Λ / s := by ring
  rw [hsplit, e7]
  linarith

/-- **The reduction's error decays**: `E_err ≤ 7Λ/√L` (`RMF.halfErr_le_one`'s proof with
`RMF.half_err_arith_decay`). -/
lemma halfErr_le_decay {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    smallQReductionErr x (halfZ x) (halfEta x) (halfEps x)
      ≤ 7 * Real.log (Real.log x) / Real.sqrt (Real.log x) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := half_params hx
  obtain ⟨hz2, -, hlogz⟩ := halfZ_facts hx
  obtain ⟨-, hsΛ, hs6⟩ := half_big hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hsq : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hLpos.le
  have hε : 1 / halfEps x = Real.sqrt (Real.log x) := by rw [halfEps, one_div, inv_inv]
  have hη0 : 0 < halfEta x := by rw [halfEta]; positivity
  have hL1 : 1 ≤ Real.log x := by
    have : (1 : ℝ) ≤ Real.exp 110 := Real.one_le_exp (by norm_num)
    linarith
  -- `η(1 + L) ≤ 2/L²` and `η ≤ 1`
  have hη2 : halfEta x * (1 + Real.log x) ≤ 2 / Real.log x ^ 2 := by
    rw [halfEta, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    nlinarith
  have hη1 : halfEta x ≤ 1 := by
    rw [halfEta]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  -- `2/log z ≤ 2Λ/L`
  have hlogz0 : 0 < Real.log (halfZ x) := by linarith
  have hA : halfA x * Real.log (Real.log x) = 2 * Real.log x := by
    rw [halfA]
    field_simp
  have t1 : 2 / Real.log (halfZ x) ≤ 2 * Real.log (Real.log x) / Real.log x := by
    rw [div_le_div_iff₀ hlogz0 hLpos]
    have h1 : halfA x / 2 ≤ Real.log (halfZ x) := by linarith
    nlinarith
  -- `5z(1+log z)³/x ≤ 40L³e^{-L/2}`
  have hzle : (halfZ x : ℝ) ≤ Real.exp (halfA x) :=
    le_trans (Nat.floor_le (Real.exp_pos _).le) (Real.exp_le_exp.2 (by linarith))
  have hz0 : (0 : ℝ) < (halfZ x : ℝ) := by
    have : (2 : ℝ) ≤ (halfZ x : ℝ) := by exact_mod_cast hz2
    linarith
  have hlogzle : Real.log (halfZ x) ≤ halfA x :=
    le_trans (Real.log_le_log hz0 hzle) (le_of_eq (Real.log_exp _))
  have hcube : (1 + Real.log (halfZ x)) ^ 3 ≤ (2 * Real.log x) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have haL2 : halfA x ≤ Real.log x / 2 := by
    rw [halfA, div_le_iff₀ hΛpos]
    nlinarith
  have hxe : Real.exp (Real.log x) = x := Real.exp_log hx0
  have h2 : Real.exp (halfA x) ≤ Real.exp (-(Real.log x / 2)) * x := by
    calc Real.exp (halfA x) ≤ Real.exp (-(Real.log x / 2) + Real.log x) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(Real.log x / 2)) * x := by rw [Real.exp_add, hxe]
  have t2 : 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 / x
      ≤ 40 * Real.log x ^ 3 * Real.exp (-(Real.log x / 2)) := by
    rw [div_le_iff₀ hx0]
    calc 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3
        ≤ 5 * (Real.exp (-(Real.log x / 2)) * x) * (2 * Real.log x) ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hzle h2) (by norm_num)) hcube
            (by positivity) (by positivity)
      _ = 40 * Real.log x ^ 3 * Real.exp (-(Real.log x / 2)) * x := by ring
  -- `e^{-L/2}·L⁶ ≤ 46080`
  have hexpneg : Real.exp (-(Real.log x / 2)) * Real.log x ^ 6 ≤ 46080 := by
    have h6 := pow_six_le_exp (u := Real.log x / 2) (by linarith)
    have h1 : Real.exp (-(Real.log x / 2)) * Real.exp (Real.log x / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : (Real.log x / 2) ^ 6 = Real.log x ^ 6 / 64 := by ring
    rw [h3] at h6
    have h4 := Real.exp_pos (-(Real.log x / 2))
    calc Real.exp (-(Real.log x / 2)) * Real.log x ^ 6
        ≤ Real.exp (-(Real.log x / 2)) * (64 * (720 * Real.exp (Real.log x / 2))) :=
          mul_le_mul_of_nonneg_left (by linarith) h4.le
      _ = 46080 * (Real.exp (-(Real.log x / 2)) * Real.exp (Real.log x / 2)) := by ring
      _ = 46080 := by rw [h1, mul_one]
  -- assemble
  have hp : 0 ≤ 2 / Real.log (halfZ x) + 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 / x := by
    positivity
  have hsum : halfEta x * (1 + Real.log x) + (1 + halfEta x) * (2 / Real.log (halfZ x)
      + 5 * (halfZ x : ℝ) * (1 + Real.log (halfZ x)) ^ 3 / x)
      ≤ 2 / Real.log x ^ 2 + 2 * (2 * Real.log (Real.log x) / Real.log x
        + 40 * Real.log x ^ 3 * Real.exp (-(Real.log x / 2))) := by
    have := mul_le_mul (by linarith : 1 + halfEta x ≤ 2) (add_le_add t1 t2) hp (by norm_num)
    linarith
  have hs0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hfin := mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt (Real.log x))
  have harith := half_err_arith_decay (s := Real.sqrt (Real.log x))
    (Λ := Real.log (Real.log x)) (E := Real.exp (-(Real.log x / 2))) hs6 hsΛ (by linarith)
    (Real.exp_pos _).le (by rw [hsq]; exact hexpneg)
  rw [hsq] at harith
  unfold smallQReductionErr
  rw [hε]
  linarith

/-- **The central window at exponent `q`**: `C_c(q) ≤ 50.266Λ + 11.44` (`RMF.tenCen_le` with the
exponent `2(1-q)S₂w² ≤ 2S₂w²`). -/
lemma uCen_le {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hq0 : 0 ≤ q) :
    uCenAt q (halfSigma x) (halfY x) (tenJ x)
      ≤ 50266 / 1000 * Real.log (Real.log x) + 1144 / 100 := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, ha9, -⟩ := half_params hx
  obtain ⟨hy2, -, hlogy_le, hlogy_ge, -, -⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hly : 22000 ≤ Real.log (halfY x) := by linarith
  have hlypos : 0 < Real.log (halfY x) := by linarith
  have hA : halfA x * Real.log (Real.log x) = 2 * Real.log x := by
    rw [halfA]
    field_simp
  have hLbig : 60000 * Real.log (Real.log x) ≤ Real.log x := by
    have h := hundred_mul_pow_ten_le_exp hΛ
    rw [hexpΛ] at h
    have h9 : (110 : ℝ) ^ 9 ≤ Real.log (Real.log x) ^ 9 := pow_le_pow_left₀ (by norm_num) hΛ 9
    have : Real.log (Real.log x) ^ 10 = Real.log (Real.log x) ^ 9 * Real.log (Real.log x) := by
      ring
    nlinarith
  unfold uCenAt
  rw [add_div]
  -- the first part
  have hp1 : Real.pi / halfSigma x / Real.log (halfY x) ≤ 50266 / 1000 * Real.log (Real.log x) := by
    have e1 : Real.pi / halfSigma x = 32 * Real.pi * Real.log x := by
      rw [halfSigma]
      field_simp
    rw [e1, div_le_iff₀ hlypos]
    have hpi := Real.pi_lt_d6
    have h1 := mul_le_mul_of_nonneg_left hlogy_ge hΛpos.le
    nlinarith
  -- the second part
  have hw0 : 0 < Real.exp (-((tenJ x : ℕ) : ℝ)) := Real.exp_pos _
  have hwly : Real.exp (-((tenJ x : ℕ) : ℝ)) * Real.log (halfY x) ≤ 3 / 2 := by
    have h23 : 0 < 2 / 3 * Real.log (halfY x) := by positivity
    have hJ : Real.log (2 / 3 * Real.log (halfY x)) ≤ ((tenJ x : ℕ) : ℝ) := by
      rw [tenJ]
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc Real.exp (-((tenJ x : ℕ) : ℝ)) * Real.log (halfY x)
        ≤ Real.exp (-Real.log (2 / 3 * Real.log (halfY x))) * Real.log (halfY x) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hlypos.le
      _ = 3 / 2 := by
          rw [Real.exp_neg, Real.exp_log h23]
          field_simp
  have hS : Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34
      ≤ 502 / 1000 * Real.log (halfY x) ^ 2 := by
    have hy0 : (0 : ℝ) < (halfY x : ℝ) := by
      have : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
      linarith
    have h1 : Real.log ((halfY x : ℝ) + 1) ≤ Real.log (halfY x) + 1 := by
      have h2 : Real.log ((halfY x : ℝ) + 1) ≤ Real.log (2 * (halfY x : ℝ)) :=
        Real.log_le_log (by positivity) (by
          have : (1 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast (by omega : 1 ≤ halfY x)
          linarith)
      rw [Real.log_mul (by norm_num) hy0.ne'] at h2
      linarith
    have h0 : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := hy0.le
      linarith)
    have h3 : Real.log ((halfY x : ℝ) + 1) ^ 2 ≤ (Real.log (halfY x) + 1) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    nlinarith
  set w := Real.exp (-((tenJ x : ℕ) : ℝ)) with hwdef
  set ly := Real.log (halfY x) with hlydef
  set S₂ := Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34
    with hS₂def
  have hS0 : 0 ≤ S₂ := by
    rw [hS₂def]
    have h0 : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := Nat.cast_nonneg _
      linarith)
    positivity
  have hκ0 : 0 ≤ 9 / 4 * (2 * S₂ / ly ^ 2) := by positivity
  have hκ : 9 / 4 * (2 * S₂ / ly ^ 2) ≤ 22590 / 10000 := by
    have : 2 * S₂ / ly ^ 2 ≤ 1004 / 1000 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hwl0 : 0 ≤ w * ly := by positivity
  have hs0 : 0 ≤ (w * ly) ^ 2 / (9 / 4) := by positivity
  have hs1 : (w * ly) ^ 2 / (9 / 4) ≤ 1 := by
    rw [div_le_one (by norm_num)]
    have := pow_le_pow_left₀ hwl0 hwly 2
    linarith [show ((3 : ℝ) / 2) ^ 2 = 9 / 4 by norm_num]
  have hconv := exp_mul_le_one_add_mul (x := 9 / 4 * (2 * S₂ / ly ^ 2)) hs0 hs1
  have hexp1 : 2 * S₂ * w ^ 2 = (w * ly) ^ 2 / (9 / 4) * (9 / 4 * (2 * S₂ / ly ^ 2)) := by
    field_simp
  have hek : Real.exp (9 / 4 * (2 * S₂ / ly ^ 2)) - 1 ≤ 85750 / 10000 := by
    have : Real.exp (22590 / 10000) ≤ 95750 / 10000 := by interval_decide (trust := kernel)
    linarith [Real.exp_le_exp.2 hκ]
  have hq2 : Real.exp (2 * (1 - q) * S₂ * w ^ 2) ≤ Real.exp (2 * S₂ * w ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 ≤ S₂ * w ^ 2 := by positivity
    nlinarith
  have hp2 : 2 * (Real.exp (2 * (1 - q) * S₂ * w ^ 2) - 1) / w / ly ≤ 1144 / 100 := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have h1 : Real.exp ((w * ly) ^ 2 / (9 / 4) * (9 / 4 * (2 * S₂ / ly ^ 2))) - 1
        ≤ (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (2 * S₂ / ly ^ 2)) - 1) := by linarith
    have h2 : (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (2 * S₂ / ly ^ 2)) - 1)
        ≤ (w * ly) * (3 / 2) / (9 / 4) * (85750 / 10000) := by
      have hsq : (w * ly) ^ 2 ≤ (w * ly) * (3 / 2) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_left hwly hwl0
      calc (w * ly) ^ 2 / (9 / 4) * (Real.exp (9 / 4 * (2 * S₂ / ly ^ 2)) - 1)
          ≤ (w * ly) ^ 2 / (9 / 4) * (85750 / 10000) :=
            mul_le_mul_of_nonneg_left hek hs0
        _ ≤ (w * ly) * (3 / 2) / (9 / 4) * (85750 / 10000) := by
            have := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 9 / 4)
            linarith
    rw [hexp1] at hq2
    linarith
  linarith

end RMF
