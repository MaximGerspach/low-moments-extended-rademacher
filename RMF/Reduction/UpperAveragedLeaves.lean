/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperAveraged
import RMF.Reduction.UpperNumerals
import PrimeNumberTheoremAnd.EulerMascheroniBounds
import LeanCert.Tactic.IntervalAuto

/-!
# The chaos constant at the averaged free start: the leaves, in exponential form

`RMF.chaosAveragedConst` at `q ∈ [2/3, 1]` is `k·shiftMomentConst(…)`.  This file bounds it, and the
periodisation sum, by closed expressions in `q` whose only transcendental operations are `exp` and
`log` of rationals, so that interval arithmetic can certify them on intervals of `q`:

* `RMF.tsum_lineWeight_rpow_eq`, `RMF.tsum_quarter_add_sq_rpow_le`: the periodisation sum as six
  terms and the integral tail;
* `RMF.shiftMomentConst_le_exp`: the interpolation constant at upper bounds of its leaves;
* the leaves: `e^{γ + 9.0028/10⁶} ≤ 1.7811`, `averagedK 0 ≤ 1.1816`,
  `harperGoodBadConstOf 0 β ≤ e^{50.1 + log(2β/(2β-1))}` (`harperGoodBadConst 0 ≤ e^{50.39}` at
  `β = 2`), the averaged free start's constant and shift at log-slope `β`, `e^{-2}` and
  `1/√(1 - 1/100)`.

The certified numeral is `RMF.harper_upper_numeral` (`RMF/Reduction/UpperSieveLeaves.lean`,
`RMF/Reduction/UpperSieveNumeral.lean`).
-/

open MeasureTheory

namespace RMF

/-! ### Powers as exponentials -/

/-- `x^q ≤ e^{q log x}` for `x ≥ 0`, with equality for `x > 0`. -/
lemma rpow_le_exp_mul_log {x : ℝ} (hx : 0 ≤ x) (q : ℝ) : x ^ q ≤ Real.exp (q * Real.log x) := by
  rcases hx.eq_or_lt with rfl | hx
  · rcases eq_or_ne q 0 with rfl | hq
    · simp
    · rw [Real.zero_rpow hq]
      exact (Real.exp_pos _).le
  · rw [Real.rpow_def_of_pos hx, mul_comm]

lemma rpow_eq_exp_mul_log {x : ℝ} (hx : 0 < x) (q : ℝ) : x ^ q = Real.exp (q * Real.log x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

lemma inv_rpow_eq_exp_neg {x : ℝ} (hx : 0 < x) (q : ℝ) :
    x⁻¹ ^ q = Real.exp (-(q * Real.log x)) := by
  rw [Real.inv_rpow hx.le, rpow_eq_exp_mul_log hx, Real.exp_neg]

/-! ### The interpolation constant -/

/-- **`RMF.shiftMomentConst` at upper bounds of its leaves, in exponential form**: the Jensen
branch `e^{q log(N(1+λ))}` and the decomposition branch at `C₁ ≤ N`, `C_i ≤ C_i'`, `C_b ≤ e^{L_B}`,
`(A + s)(1 - q) ≤ U` and upper bounds `IS`, `S1`, `S2`, `EM2` on `1/√(1-δ)`, `(1-e^{-2})⁻¹`,
`e^{-2}(1-e^{-2})⁻²` and `e^{-2}`. -/
lemma shiftMomentConst_le_exp {C₁ Ci Cb A s lam δ q N Ci' LB U IS S1 S2 EM2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 ≤ C₁) (hC₁N : C₁ ≤ N) (hCi : 0 ≤ Ci) (hCiC : Ci ≤ Ci')
    (hCb : 0 ≤ Cb) (hCbL : Cb ≤ Real.exp LB) (hAs : 0 ≤ A + s) (hU : (A + s) * (1 - q) ≤ U)
    (hlam : 0 < lam) (hδ : δ < 1) (hIS : (Real.sqrt (1 - δ))⁻¹ ≤ IS)
    (hS1 : (1 - Real.exp (-2))⁻¹ ≤ S1) (hS2 : Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ ≤ S2)
    (hEM2 : Real.exp (-2) ≤ EM2) :
    shiftMomentConst C₁ Ci Cb A s lam δ q
      ≤ max (Real.exp (q * Real.log (N * (1 + lam))))
          (Real.exp (q * Real.log ((1 + 1 / lam) * IS * Ci'))
              * (Real.exp (q * Real.log U) + Real.exp ((1 - q) * (LB - 2 * A))
                * (Real.exp (q * Real.log (U + 1)) * S1 + S2))
            + EM2 * Real.exp ((1 - q) * (LB - 2 * A)) * Real.exp (q * Real.log N)) := by
  have hq1' : 0 ≤ 1 - q := by linarith
  have hu0 : 0 ≤ (A + s) * (1 - q) := mul_nonneg hAs hq1'
  have hU0 : 0 ≤ U := le_trans hu0 hU
  have hsq : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.2 (by linarith)
  have he21 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hS10 : 0 ≤ (1 - Real.exp (-2))⁻¹ := inv_nonneg.2 (by linarith)
  have hS20 : 0 ≤ Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ :=
    mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (sq_nonneg _))
  have hN0 : 0 ≤ N := le_trans hC₁ hC₁N
  have hIS0 : 0 ≤ IS := le_trans (inv_nonneg.2 hsq.le) hIS
  have hEM20 : 0 ≤ EM2 := le_trans (Real.exp_pos _).le hEM2
  -- the bad sets' factor
  have hE0 : 0 ≤ (Cb * Real.exp (-(2 * A))) ^ (1 - q) :=
    Real.rpow_nonneg (mul_nonneg hCb (Real.exp_pos _).le) _
  have hE : (Cb * Real.exp (-(2 * A))) ^ (1 - q) ≤ Real.exp ((1 - q) * (LB - 2 * A)) := by
    calc (Cb * Real.exp (-(2 * A))) ^ (1 - q)
        ≤ (Real.exp LB * Real.exp (-(2 * A))) ^ (1 - q) :=
          Real.rpow_le_rpow (mul_nonneg hCb (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_right hCbL (Real.exp_pos _).le) hq1'
      _ = Real.exp ((1 - q) * (LB - 2 * A)) := by
          rw [← Real.exp_add, ← Real.exp_mul]
          congr 1
          ring
  -- the Jensen branch
  have hJ : (C₁ * (1 + lam)) ^ q ≤ Real.exp (q * Real.log (N * (1 + lam))) :=
    le_trans (Real.rpow_le_rpow (mul_nonneg hC₁ (by linarith))
      (mul_le_mul_of_nonneg_right hC₁N (by linarith)) hq0)
      (rpow_le_exp_mul_log (mul_nonneg hN0 (by linarith)) q)
  -- the decomposition branch
  have hlam1 : 0 ≤ 1 + lam⁻¹ := by
    have := inv_nonneg.2 hlam.le
    linarith
  have hc : (1 + lam⁻¹) * Ci / Real.sqrt (1 - δ) ≤ (1 + 1 / lam) * IS * Ci' := by
    rw [div_eq_mul_inv, one_div]
    calc (1 + lam⁻¹) * Ci * (Real.sqrt (1 - δ))⁻¹ = (1 + lam⁻¹) * (Real.sqrt (1 - δ))⁻¹ * Ci := by
          ring
      _ ≤ (1 + lam⁻¹) * IS * Ci' :=
          mul_le_mul (mul_le_mul_of_nonneg_left hIS hlam1) hCiC hCi (mul_nonneg hlam1 hIS0)
  have hc0 : 0 ≤ (1 + lam⁻¹) * Ci / Real.sqrt (1 - δ) :=
    div_nonneg (mul_nonneg hlam1 hCi) hsq.le
  have hcq : ((1 + lam⁻¹) * Ci / Real.sqrt (1 - δ)) ^ q
      ≤ Real.exp (q * Real.log ((1 + 1 / lam) * IS * Ci')) :=
    le_trans (Real.rpow_le_rpow hc0 hc hq0) (rpow_le_exp_mul_log (le_trans hc0 hc) q)
  have hu : ((A + s) * (1 - q)) ^ q ≤ Real.exp (q * Real.log U) :=
    le_trans (Real.rpow_le_rpow hu0 hU hq0) (rpow_le_exp_mul_log hU0 q)
  have hu1 : ((A + s) * (1 - q) + 1) ^ q ≤ Real.exp (q * Real.log (U + 1)) :=
    le_trans (Real.rpow_le_rpow (by linarith) (by linarith) hq0)
      (rpow_le_exp_mul_log (by linarith) q)
  have hN : C₁ ^ q ≤ Real.exp (q * Real.log N) :=
    le_trans (Real.rpow_le_rpow hC₁ hC₁N hq0) (rpow_le_exp_mul_log hN0 q)
  have hin0 : 0 ≤ ((A + s) * (1 - q) + 1) ^ q * (1 - Real.exp (-2))⁻¹
      + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) hS10) hS20
  unfold shiftMomentConst
  refine max_le_max hJ (add_le_add (mul_le_mul hcq ?_ ?_ (Real.exp_pos _).le) ?_)
  · exact add_le_add hu (mul_le_mul hE (add_le_add (mul_le_mul hu1 hS1 hS10 (Real.exp_pos _).le)
      hS2) hin0 (Real.exp_pos _).le)
  · exact add_nonneg (Real.rpow_nonneg hu0 _) (mul_nonneg hE0 hin0)
  · exact mul_le_mul (mul_le_mul hEM2 hE hE0 hEM20) hN (Real.rpow_nonneg hC₁ _)
      (mul_nonneg hEM20 (Real.exp_pos _).le)

/-! ### The periodisation sum -/

/-- `∑_{n ∈ ℤ} w_n^q = 2∑_{d ≥ 0} (1/4 + d²)^{-q}`: the windows left of `0` repeat the distances of
the windows right of it. -/
lemma tsum_lineWeight_rpow_eq {q : ℝ} (hq : 1 / 2 < q) :
    ∑' n : ℤ, lineWeight n ^ q = 2 * ∑' d : ℕ, ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q := by
  have hS := summable_lineWeight_rpow hq
  have hpos : ∀ d : ℕ, lineWeight (d : ℤ) ^ q = ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q := by
    intro d
    have hd : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
    rw [lineWeight, lineDist, if_pos hd, Int.cast_natCast]
  have hneg : ∀ d : ℕ, lineWeight (-((d : ℤ) + 1)) ^ q = ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q := by
    intro d
    have hd : ¬ (0 ≤ -((d : ℤ) + 1)) := by omega
    have hsq : (-(((-((d : ℤ) + 1) : ℤ) : ℝ) + 1)) ^ 2 = (d : ℝ) ^ 2 := by push_cast; ring
    rw [lineWeight, lineDist, if_neg hd, hsq]
  have hinj₁ : Function.Injective (fun d : ℕ => (d : ℤ)) := Nat.cast_injective
  have hinj₂ : Function.Injective (fun d : ℕ => -((d : ℤ) + 1)) := by
    intro a b h
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at h
    exact h
  have h1 : Summable fun d : ℕ => lineWeight (d : ℤ) ^ q := hS.comp_injective hinj₁
  have h2 : Summable fun d : ℕ => lineWeight (-((d : ℤ) + 1)) ^ q := hS.comp_injective hinj₂
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => lineWeight n ^ q) h1 h2, tsum_congr hpos,
    tsum_congr hneg]
  ring

/-- **The tail by the integral**: `∑_{d ≥ 0} (1/4 + d²)^{-q} ≤ ∑_{d < 6} (1/4 + d²)^{-q}
+ 5^{1-2q}/(2q - 1)` for `q > 1/2`, since `(1/4 + d²)^{-q} ≤ d^{-2q} ≤ ∫_{d-1}^d t^{-2q} dt`. -/
lemma tsum_quarter_add_sq_rpow_le {q : ℝ} (hq : 1 / 2 < q) :
    ∑' d : ℕ, ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q
      ≤ ∑ d ∈ Finset.range 6, ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q + 5 ^ (1 - 2 * q) / (2 * q - 1) := by
  have hq1 : 0 < 2 * q - 1 := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hf0 : ∀ d : ℕ, 0 ≤ ((1 / 4 + (d : ℝ) ^ 2)⁻¹) ^ q := fun d =>
    Real.rpow_nonneg (by positivity) q
  have htail0 : (0 : ℝ) ≤ 5 ^ (1 - 2 * q) / (2 * q - 1) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) hq1.le
  -- the terms past `5` against `x^{-2q}`
  have hterm : ∀ j : ℕ, ((1 / 4 + ((6 + j : ℕ) : ℝ) ^ 2)⁻¹) ^ q
      ≤ (5 + ((j + 1 : ℕ) : ℝ)) ^ (-(2 * q)) := by
    intro j
    have hx : ((6 + j : ℕ) : ℝ) = 5 + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hx]
    set x : ℝ := 5 + ((j + 1 : ℕ) : ℝ) with hxdef
    have hxpos : 0 < x := by positivity
    have hle : x ^ 2 ≤ 1 / 4 + x ^ 2 := by linarith
    calc ((1 / 4 + x ^ 2)⁻¹) ^ q ≤ ((x ^ 2)⁻¹) ^ q :=
          Real.rpow_le_rpow (by positivity) (inv_anti₀ (by positivity) hle) hq0
      _ = x ^ (-(2 * q)) := by
          rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le,
            ← Real.rpow_neg hxpos.le]
          norm_num
  have hanti : ∀ m : ℕ, AntitoneOn (fun x : ℝ => x ^ (-(2 * q))) (Set.Icc 5 (5 + (m : ℝ))) := by
    intro m x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint : ∀ m : ℕ,
      ∫ x in (5 : ℝ)..5 + (m : ℝ), x ^ (-(2 * q)) ≤ 5 ^ (1 - 2 * q) / (2 * q - 1) := by
    intro m
    have h0 : (0 : ℝ) ∉ Set.uIcc 5 (5 + (m : ℝ)) := by
      rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) m])]
      intro h
      linarith [h.1]
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show -(2 * q) + 1 = 1 - 2 * q by ring]
    have hm : (0 : ℝ) ≤ (5 + (m : ℝ)) ^ (1 - 2 * q) := Real.rpow_nonneg (by positivity) _
    have hneg : 1 - 2 * q < 0 := by linarith
    calc ((5 + (m : ℝ)) ^ (1 - 2 * q) - 5 ^ (1 - 2 * q)) / (1 - 2 * q)
        = (5 ^ (1 - 2 * q) - (5 + (m : ℝ)) ^ (1 - 2 * q)) / (2 * q - 1) := by
          rw [div_eq_div_iff hneg.ne hq1.ne']
          ring
      _ ≤ 5 ^ (1 - 2 * q) / (2 * q - 1) := div_le_div_of_nonneg_right (by linarith) hq1.le
  refine Real.tsum_le_of_sum_range_le hf0 fun n => ?_
  rcases le_or_gt n 6 with hn | hn
  · calc ∑ i ∈ Finset.range n, ((1 / 4 + (i : ℝ) ^ 2)⁻¹) ^ q
        ≤ ∑ i ∈ Finset.range 6, ((1 / 4 + (i : ℝ) ^ 2)⁻¹) ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hn) fun i _ _ => hf0 i
      _ ≤ _ := le_add_of_nonneg_right htail0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 6 + m := ⟨n - 6, by omega⟩
    rw [Finset.sum_range_add]
    refine add_le_add le_rfl ?_
    calc ∑ j ∈ Finset.range m, ((1 / 4 + ((6 + j : ℕ) : ℝ) ^ 2)⁻¹) ^ q
        ≤ ∑ j ∈ Finset.range m, (5 + ((j + 1 : ℕ) : ℝ)) ^ (-(2 * q)) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ ≤ ∫ x in (5 : ℝ)..5 + (m : ℝ), x ^ (-(2 * q)) := (hanti m).sum_le_integral
      _ ≤ 5 ^ (1 - 2 * q) / (2 * q - 1) := hint m

/-! ### The leaves -/

/-- `e^{γ + 9.0028/10⁶} ≤ 1.7811`, from `γ ≤ 0.577216` (`hγ_hi`). -/
lemma normSqLogSharpConst_million_le : normSqLogSharpConst 1000000 ≤ 17811 / 10000 := by
  have hγ := hγ_hi
  have h : Real.exp (5772251 / 10000000) ≤ 17811 / 10000 := by
    interval_decide (trust := kernel)
  refine le_trans (Real.exp_le_exp.2 ?_) h
  norm_num at hγ ⊢
  linarith

/-- `averagedK 0 ≤ 1.1816`: `50/(24·0.475π) ≤ 1.1816²`, since `π > 3.141592`. -/
lemma averagedK_zero_le : averagedK 0 ≤ 11816 / 10000 := by
  have hpi := Real.pi_gt_d6
  have h : 2 * 25 / (24 * (Real.pi * (0.475 * Real.exp (-(2 * 0))))) ≤ (11816 / 10000) ^ 2 := by
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one, div_le_iff₀ (by positivity)]
    nlinarith
  unfold averagedK
  calc √(2 * 25 / (24 * (Real.pi * (0.475 * Real.exp (-(2 * 0))))))
        ≤ √((11816 / 10000) ^ 2) := Real.sqrt_le_sqrt h
    _ = 11816 / 10000 := Real.sqrt_sq (by norm_num)

/-- `e^{-100} ≤ 10⁻⁷`. -/
lemma exp_neg_hundred_le : Real.exp (-100) ≤ 1 / 10000000 := by
  have h17 := exp_seventeen_ge
  have h1 : Real.exp (-100) ≤ Real.exp (-17) := Real.exp_le_exp.2 (by norm_num)
  have h3 : Real.exp (-17) = (Real.exp 17)⁻¹ := Real.exp_neg 17
  have h2 : (Real.exp 17)⁻¹ ≤ 1 / 24000000 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h17
  linarith

/-- **The averaged free start's constant at `E₀ = 0`**, at log-slope `β ∈ [0, 2]`:
`averagedConst 0 β T κ ≤ (1 + 10⁻⁷)·1.1816·(1 + β/(4κ))/(1 - 2β/T)`. -/
lemma averagedConst_zero_le {β T κ : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hT : 4 < T) (hκ : 0 < κ) :
    averagedConst 0 β T κ
      ≤ (1 + 1 / 10000000) * (11816 / 10000) * (1 + β / (4 * κ)) / (1 - 2 * β / T) := by
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - 2 * β / T := by
    rw [sub_pos, div_lt_one hT0]
    linarith
  have he := exp_neg_hundred_le
  have hK := averagedK_zero_le
  have hK0 : 0 ≤ averagedK 0 := le_trans zero_le_one (one_le_averagedK le_rfl)
  have hk : 0 ≤ 1 + β / (4 * κ) := by
    have : 0 ≤ β / (4 * κ) := div_nonneg hβ0 (by linarith)
    linarith
  unfold averagedConst
  refine div_le_div_of_nonneg_right ?_ hden.le
  exact mul_le_mul (mul_le_mul (by linarith) hK hK0 (by norm_num)) le_rfl hk (by positivity)

/-- `driftSharpOf 0 16 = e²(120e^{-17} + 4e^{-16}) ≤ 1/15000`. -/
lemma driftSharpOf_zero_sixteen_le : driftSharpOf 0 16 ≤ 1 / 15000 := by
  have h17 := exp_seventeen_ge
  have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h]
    nlinarith [Real.exp_pos 1]
  have hu : (Real.exp 17)⁻¹ ≤ 1 / 24000000 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h17
  have hu0 : 0 ≤ (Real.exp 17)⁻¹ := inv_nonneg.2 (Real.exp_pos _).le
  have h1 : Real.exp (-(1 + 16)) = (Real.exp 17)⁻¹ := by rw [← Real.exp_neg]; norm_num
  have h2 : Real.exp (-16) = Real.exp 1 * (Real.exp 17)⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    norm_num
  have he20 := (Real.exp_pos 2).le
  have he10 := (Real.exp_pos 1).le
  unfold driftSharpOf
  rw [Real.sqrt_zero, mul_zero, zero_add, mul_zero, Real.exp_zero, mul_one, h1, h2]
  have t1 : 120 * Real.exp 2 * (Real.exp 17)⁻¹ ≤ 120 * 7.4 * (1 / 24000000) :=
    mul_le_mul (mul_le_mul_of_nonneg_left he2 (by norm_num)) hu hu0 (by norm_num)
  have t2 : 4 * (Real.exp 2 * (Real.exp 1 * (Real.exp 17)⁻¹))
      ≤ 4 * (7.4 * (2.72 * (1 / 24000000))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul he2 ?_ (by positivity) (by norm_num)) (by norm_num)
    exact mul_le_mul he1 hu hu0 (by norm_num)
  linarith

/-- `log 50 ≤ 3.912024`. -/
lemma log_fifty_le : Real.log 50 ≤ 3912024 / 1000000 := by
  interval_decide (trust := kernel)

/-- **The averaged free start's shift at `E₀ = 0` and log-slope `β ≥ 0`**, given rational
bounds `ℓκ ≥ log κ` and `ℓ ≥ log(1.1816T)`. -/
lemma averagedShift_zero_le {β T κ ℓκ ℓKT : ℝ} (hβ0 : 0 ≤ β) (hT : 4 < T)
    (hℓκ : Real.log κ ≤ ℓκ) (hℓKT : Real.log (11816 / 10000 * T) ≤ ℓKT) :
    averagedShift 0 β T κ ≤ 3 * (1 / 15000) + β * ℓκ + β / κ + β * (693148 / 1000000) + (2 - β)
      + 45 / 32 + 2 * (2658681 / 1000000) + β * (1 + 693148 / 1000000 + 3912024 / 1000000)
      + 2 * β * ℓKT := by
  have hd := driftSharpOf_zero_sixteen_le
  have hlog2 : Real.log 2 ≤ 693148 / 1000000 := by linarith [Real.log_two_lt_d9]
  have hlog50 : Real.log (2 * ((25 : ℕ) : ℝ)) ≤ 3912024 / 1000000 := by
    rw [show (2 : ℝ) * ((25 : ℕ) : ℝ) = 50 by norm_num]
    exact log_fifty_le
  have hpi := Real.pi_lt_d6
  have hsq : √(Real.pi * (9 / 2) / 2) ≤ 2658681 / 1000000 := by
    have h : Real.pi * (9 / 2) / 2 ≤ (2658681 / 1000000) ^ 2 := by nlinarith
    calc √(Real.pi * (9 / 2) / 2) ≤ √((2658681 / 1000000) ^ 2) := Real.sqrt_le_sqrt h
      _ = 2658681 / 1000000 := Real.sqrt_sq (by norm_num)
  have hK := averagedK_zero_le
  have hK1 := one_le_averagedK (E₀ := 0) le_rfl
  have hT0 : 0 < T := by linarith
  have hlogKT : Real.log (averagedK 0 * T) ≤ ℓKT :=
    le_trans (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hK hT0.le)) hℓKT
  have t1 : β * Real.log κ ≤ β * ℓκ := mul_le_mul_of_nonneg_left hℓκ hβ0
  have t2 : β * Real.log 2 ≤ β * (693148 / 1000000) := mul_le_mul_of_nonneg_left hlog2 hβ0
  have t3 : β * (1 + Real.log 2 + Real.log (2 * ((25 : ℕ) : ℝ)))
      ≤ β * (1 + 693148 / 1000000 + 3912024 / 1000000) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ0
  have t4 : 2 * β * Real.log (averagedK 0 * T) ≤ 2 * β * ℓKT :=
    mul_le_mul_of_nonneg_left hlogKT (by linarith)
  unfold averagedShift result1SharpShift
  linarith

/-- **`harperGoodBadConstOf 0 β ≤ e^{LB}`** for `β > 1/2` and `LB ≥ 50.1 + log(2β/(2β - 1))`:
`indexSharpConst 1 ≤ e^{32.1}`, `e^D ≤ e^{18}` and `Σ_i i^{-2β} ≤ 2β/(2β - 1)`
(`RMF.tsum_nat_rpow_neg_le`). -/
lemma harperGoodBadConstOf_zero_le_exp {β LB : ℝ} (hβ : 1 / 2 < β)
    (hLB : 501 / 10 + Real.log (2 * β / (2 * β - 1)) ≤ LB) :
    harperGoodBadConstOf 0 β ≤ Real.exp LB := by
  unfold harperGoodBadConstOf
  rw [harperSharpDeficit_zero]
  have hI : indexSharpConst 1 ≤ Real.exp 32.1 := by
    have h2 := indexSharpConst_two_le
    have heq : indexSharpConst 2 = indexSharpConst 1 * Real.exp 1 := by
      have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      unfold indexSharpConst
      rw [h]
      ring
    have h33 : Real.exp 33.1 = Real.exp 32.1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [heq, h33] at h2
    exact le_of_mul_le_mul_right h2 (Real.exp_pos 1)
  have hD : Real.exp (freeStartHarperD 0 : ℝ) ≤ Real.exp 18 := by
    refine Real.exp_le_exp.2 ?_
    exact_mod_cast freeStartHarperD_zero_le
  have hz : ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) ≤ 2 * β / (2 * β - 1) :=
    tsum_nat_rpow_neg_le (by linarith)
  have hzpos : 0 < 2 * β / (2 * β - 1) := div_pos (by linarith) (by linarith)
  have hz0 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-(2 * β)) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  have hI0 := (indexSharpConst_pos 1).le
  calc indexSharpConst 1 * Real.exp (freeStartHarperD 0 : ℝ) * ∑' i : ℕ, (i : ℝ) ^ (-(2 * β))
      ≤ Real.exp 32.1 * Real.exp 18 * (2 * β / (2 * β - 1)) :=
        mul_le_mul (mul_le_mul hI hD (Real.exp_pos _).le (Real.exp_pos _).le) hz hz0
          (by positivity)
    _ = Real.exp (501 / 10 + Real.log (2 * β / (2 * β - 1))) := by
        rw [Real.exp_add, Real.exp_log hzpos, ← Real.exp_add]
        norm_num
    _ ≤ Real.exp LB := Real.exp_le_exp.2 hLB

/-- `0.1353352 ≤ e^{-2} ≤ 0.1353353`. -/
lemma exp_neg_two_mem :
    1353352 / 10000000 ≤ Real.exp (-2) ∧ Real.exp (-2) ≤ 1353353 / 10000000 := by
  constructor
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

lemma exp_neg_two_le_cert : Real.exp (-2) ≤ 135336 / 1000000 := by
  linarith [exp_neg_two_mem.2]

lemma inv_one_sub_exp_neg_two_le : (1 - Real.exp (-2))⁻¹ ≤ 1156519 / 1000000 := by
  have h := exp_neg_two_mem.2
  have hpos : 0 < 1 - Real.exp (-2) := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  norm_num
  linarith

lemma exp_neg_two_mul_inv_sq_le :
    Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ ≤ 181016 / 1000000 := by
  obtain ⟨h1, h2⟩ := exp_neg_two_mem
  have hpos : 0 < (1 - Real.exp (-2)) ^ 2 := by
    have : 0 < 1 - Real.exp (-2) := by linarith
    positivity
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

lemma inv_sqrt_one_sub_le : (Real.sqrt (1 - 1 / 100))⁻¹ ≤ 100504 / 100000 := by
  have h : (100000 / 100504 : ℝ) ≤ Real.sqrt (1 - 1 / 100) := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  calc (Real.sqrt (1 - 1 / 100))⁻¹ ≤ (100000 / 100504 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 100504 / 100000 := by norm_num

/-! ### The chaos constant -/

/-- **The decomposition branch's certificate function**:
`e^{q log c}(e^{q log U} + E(e^{q log(U+1)}S₁ + S₂)) + EM2·E·e^{q log N}` with
`E = e^{(1-q)(L_B - 2A)}`. -/
noncomputable def certD (c U LB A S1 S2 EM2 N q : ℝ) : ℝ :=
  Real.exp (q * Real.log c) * (Real.exp (q * Real.log U) + Real.exp ((1 - q) * (LB - 2 * A))
      * (Real.exp (q * Real.log (U + 1)) * S1 + S2))
    + EM2 * Real.exp ((1 - q) * (LB - 2 * A)) * Real.exp (q * Real.log N)

/-- **The chaos constant at the averaged free start below its certificate functions**, at
`δ = 1/100` and `L₀ = 10⁶`: for `q ∈ [0, 1]`, `A ≥ 0`, `λ > 0`, `T > 4`, `κ ≥ 1`, `β ∈ (1/2, 2]`,
rational bounds `ℓκ ≥ log κ`, `ℓ ≥ log(1.1816T)` and `LB ≥ 50.1 + log(2β/(2β - 1))`, and
`U ≥ (A + s̄)(1 - q)` with `s̄` the bound of `RMF.averagedShift_zero_le`. -/
lemma chaosAveragedConst_le_cert {Af lamf Tf κf βf : ℝ → ℝ} {k q ℓκ ℓKT U LB : ℝ} (hk : 0 ≤ k)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hA : 0 ≤ Af q) (hlam : 0 < lamf q) (hT : 4 < Tf q)
    (hκ : 1 ≤ κf q) (hβ : 1 / 2 < βf q) (hβ2 : βf q ≤ 2)
    (hLB : 501 / 10 + Real.log (2 * βf q / (2 * βf q - 1)) ≤ LB)
    (hℓκ : Real.log (κf q) ≤ ℓκ) (hℓKT : Real.log (11816 / 10000 * Tf q) ≤ ℓKT)
    (hU : (Af q + (3 * (1 / 15000) + βf q * ℓκ + βf q / κf q + βf q * (693148 / 1000000)
      + (2 - βf q) + 45 / 32 + 2 * (2658681 / 1000000)
      + βf q * (1 + 693148 / 1000000 + 3912024 / 1000000) + 2 * βf q * ℓKT)) * (1 - q) ≤ U) :
    chaosAveragedConst Af lamf Tf κf βf (1 / 100) k 1000000 q
      ≤ k * max (Real.exp (q * Real.log (17811 / 10000 * (1 + lamf q))))
          (certD ((1 + 1 / lamf q) * (100504 / 100000)
              * ((1 + 1 / 10000000) * (11816 / 10000) * (1 + βf q / (4 * κf q))
                / (1 - 2 * βf q / Tf q) * (17811 / 10000)))
            U LB (Af q) (1156519 / 1000000) (181016 / 1000000) (135336 / 1000000)
            (17811 / 10000) q) := by
  unfold chaosAveragedConst certD
  refine mul_le_mul_of_nonneg_left ?_ hk
  have hβ0 : 0 ≤ βf q := by linarith
  have hs := averagedShift_zero_le hβ0 hT hℓκ hℓKT
  have hs0 := averagedShift_nonneg (E₀ := 0) le_rfl hβ0 hβ2 hT hκ
  have hC := averagedConst_zero_le (κ := κf q) hβ0 hβ2 hT (by linarith)
  have hC0 : 0 ≤ averagedConst 0 (βf q) (Tf q) (κf q) :=
    le_trans zero_le_one (one_le_averagedConst le_rfl hβ0 hβ2 hT hκ)
  have hN := normSqLogSharpConst_million_le
  have hN0 := (normSqLogSharpConst_pos 1000000).le
  have hT0 : 0 < Tf q := by linarith
  have hden : 0 < 1 - 2 * βf q / Tf q := by
    rw [sub_pos, div_lt_one hT0]
    linarith
  have hCb0 : 0 ≤ (1 + 1 / 10000000) * (11816 / 10000) * (1 + βf q / (4 * κf q))
      / (1 - 2 * βf q / Tf q) := by
    have : 0 ≤ βf q / (4 * κf q) := div_nonneg hβ0 (by linarith)
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hden.le
  have hq1' : 0 ≤ 1 - q := by linarith
  exact shiftMomentConst_le_exp hq0 hq1 hN0 hN (mul_nonneg hC0 hN0) (mul_le_mul hC hN hN0 hCb0)
    (harperGoodBadConstOf_pos 0 hβ).le (harperGoodBadConstOf_zero_le_exp hβ hLB)
    (add_nonneg hA hs0)
    (le_trans (mul_le_mul_of_nonneg_right (add_le_add_right hs _) hq1') hU) hlam
    (by norm_num : (1 : ℝ) / 100 < 1) inv_sqrt_one_sub_le inv_one_sub_exp_neg_two_le
    exp_neg_two_mul_inv_sq_le exp_neg_two_le_cert

/-! ### One interval of `q` -/

/-- **The decomposition branch at the endpoints of `[a, b]`**: every factor of `RMF.certD` is
monotone in `q`, so it is at most its value at the worse endpoint (`e = b` if `U ≥ 1`, `e = a` if
`U ≤ 1`). -/
lemma certD_le_end {a b q c cb U e LB A S1 S2 EM2 N : ℝ} (hq0 : 0 ≤ q) (haq : a ≤ q)
    (hqb : q ≤ b) (hb1 : b ≤ 1) (hc : 1 ≤ c) (hccb : c ≤ cb)
    (he : (1 ≤ U ∧ e = b) ∨ (0 < U ∧ U ≤ 1 ∧ e = a)) (hLA : LB - 2 * A ≤ 0) (hS1 : 0 ≤ S1)
    (hS2 : 0 ≤ S2) (hEM2 : 0 ≤ EM2) (hN : 1 ≤ N) :
    certD c U LB A S1 S2 EM2 N q
      ≤ Real.exp (b * Real.log cb) * (Real.exp (e * Real.log U) + Real.exp ((1 - b) * (LB - 2 * A))
          * (Real.exp (b * Real.log (U + 1)) * S1 + S2))
        + EM2 * Real.exp ((1 - b) * (LB - 2 * A)) * Real.exp (b * Real.log N) := by
  have hb0 : 0 ≤ b := le_trans hq0 hqb
  have hU0 : 0 < U := by
    rcases he with ⟨h, -⟩ | ⟨h, -, -⟩
    · linarith
    · exact h
  have tc : Real.exp (q * Real.log c) ≤ Real.exp (b * Real.log cb) := by
    refine Real.exp_le_exp.2 (le_trans (mul_le_mul_of_nonneg_right hqb (Real.log_nonneg hc)) ?_)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hccb) hb0
  have tU : Real.exp (q * Real.log U) ≤ Real.exp (e * Real.log U) := by
    refine Real.exp_le_exp.2 ?_
    rcases he with ⟨h, rfl⟩ | ⟨-, h, rfl⟩
    · exact mul_le_mul_of_nonneg_right hqb (Real.log_nonneg h)
    · exact mul_le_mul_of_nonpos_right haq (Real.log_nonpos hU0.le h)
  have tE : Real.exp ((1 - q) * (LB - 2 * A)) ≤ Real.exp ((1 - b) * (LB - 2 * A)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right (by linarith) hLA)
  have tU1 : Real.exp (q * Real.log (U + 1)) ≤ Real.exp (b * Real.log (U + 1)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqb (Real.log_nonneg (by linarith)))
  have tN : Real.exp (q * Real.log N) ≤ Real.exp (b * Real.log N) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqb (Real.log_nonneg hN))
  have hin : Real.exp (q * Real.log (U + 1)) * S1 + S2
      ≤ Real.exp (b * Real.log (U + 1)) * S1 + S2 :=
    add_le_add_left (mul_le_mul_of_nonneg_right tU1 hS1) _
  have hin0 : 0 ≤ Real.exp (q * Real.log (U + 1)) * S1 + S2 :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le hS1) hS2
  unfold certD
  refine add_le_add (mul_le_mul tc (add_le_add tU (mul_le_mul tE hin hin0 (Real.exp_pos _).le))
    (add_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hin0)) (Real.exp_pos _).le) ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left tE hEM2) tN (Real.exp_pos _).le
    (mul_nonneg hEM2 (Real.exp_pos _).le)

lemma chaosAveragedConst_nonneg {Af lamf Tf κf βf : ℝ → ℝ} {δ k L₀ q : ℝ} (hk : 0 ≤ k)
    (hlam : 0 ≤ lamf q) :
    0 ≤ chaosAveragedConst Af lamf Tf κf βf δ k L₀ q := by
  unfold chaosAveragedConst shiftMomentConst
  refine mul_nonneg hk (le_trans (Real.rpow_nonneg ?_ _) (le_max_left _ _))
  exact mul_nonneg (normSqLogSharpConst_pos L₀).le (by linarith)

/-- `chaosAveragedConst` reads its parameter functions only at `q`. -/
lemma chaosAveragedConst_eq_const {Af lamf Tf κf βf : ℝ → ℝ} {q A lam T κ β δ k L₀ : ℝ}
    (hA : Af q = A) (hl : lamf q = lam) (hT : Tf q = T) (hκ : κf q = κ) (hβ : βf q = β) :
    chaosAveragedConst Af lamf Tf κf βf δ k L₀ q
      = chaosAveragedConst (fun _ => A) (fun _ => lam) (fun _ => T) (fun _ => κ) (fun _ => β) δ k
          L₀ q := by
  unfold chaosAveragedConst
  rw [hA, hl, hT, hκ, hβ]

/-! ### The logarithms of the parameters -/

lemma log_sixteen_le : Real.log 16 ≤ 2772589 / 1000000 := by
  interval_decide (trust := kernel)

lemma log_KT_sixty_le : Real.log (11816 / 10000 * 60) ≤ 852243 / 200000 := by
  interval_decide (trust := kernel)

end RMF
