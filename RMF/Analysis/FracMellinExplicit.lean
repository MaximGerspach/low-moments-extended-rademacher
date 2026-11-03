/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.ZetaValues
import PrimeNumberTheoremAnd.EulerMascheroniBounds
import RMF.Analysis.PartialSumBounds

/-!
# The Mellin transform of the fractional-part kernel

The fractional-part sum is `R√x = ∑_{m≤x} X(m)φ(x/m)` with `φ(v) = {√v}·1_{v≥1}`, and its smooth
part is `H(w) = ∑ₖ X(k)k^{-1/2}ψ(w/k)` with the kernel `ψ(v) = φ(v)/√v` (`RMF.fracKernel`).  Here
`φ̂(s) = ∫₁^∞ {√v} v^{-s-1} dv = 2∫₁^∞ {w} w^{-2s-1} dw` (`RMF.fracMellin`), so `ψ̂(s) = φ̂(s + ½)`
(`RMF.integral_fracKernel_div_mul_cpow`: `∫₀^∞ ψ(u/k)u^{-s-1}du = k^{-s}φ̂(s + ½)`).

* **Closed form** `φ̂(s) = 1/(s - ½) - ζ(2s)/s` for `Re s > ½` (`RMF.fracMellin_eq_zeta`).
* **Sup bound** `|φ̂(s)| ≤ φ̂(½) = 2(1 - γ) ≤ 0.8456` for `Re s ≥ ½` (`RMF.norm_fracMellin_le`,
  `RMF.norm_fracMellin_le_numeral`).
* **Decay cap** `|φ̂(s)| ≤ (2/|2s|)(1/|t| + H_K - 1) + 1/K`, `t = Im s ≠ 0`, `K ≥ 1`
  (`RMF.norm_fracMellin_le_cap`), and `|φ̂(s)| ≤ (1 + 1/|t| + log(1 + |t|))/|t|`
  (`RMF.norm_fracMellin_le_decay`).
* Conjugation symmetry, and continuity on `Re s > 0`, so regularity at `½`
  (`RMF.fracMellin_conj`, `RMF.continuousAt_fracMellin`, `RMF.continuous_fracMellin_line`).
* **The kernel Mellin–Plancherel identity**, for finite `S ⊆ ℕ_{≥1}` and `σ > -½`
  (`RMF.integral_normSq_sum_fracKernel_eq_line`):
  `∫₀^∞ |∑ₖ aₖψ(u/k)|² u^{-1-2σ} du = (2π)⁻¹ ∫_ℝ |∑ₖ aₖk^{-σ-it}|²·|φ̂(½ + σ + it)|² dt`.
* **The total**: `∫_ℝ|φ̂(½ + σ + it)|²dt = 4π∫₁^∞{w}²w^{-3-4σ}dw ≤ 4πc₃` for `σ ≥ 0`, with
  `c₃ = 3/2 - γ - π²/12 ≤ 0.10032` (`RMF.integral_fract_sq_mul_rpow_neg_three`, `RMF.cThree_le`);
  over `t > 0`, half of it: `≤ 2πc₃ ≤ 0.6305` (`RMF.integral_Ioi_normSq_fracMellin_le`).
-/

open MeasureTheory

open scoped FourierTransform

namespace RMF

/-! ### The kernel and its Mellin transform -/

/-- **The fractional-part kernel** `ψ(v) = {√v}/√v` for `v ≥ 1`, and `0` for `v < 1`. -/
noncomputable def fracKernel (v : ℝ) : ℝ :=
  if 1 ≤ v then Int.fract (Real.sqrt v) / Real.sqrt v else 0

/-- **The Mellin transform** `φ̂(s) = 2∫₁^∞ {w} w^{-2s-1} dw` of `φ(v) = {√v}·1_{v ≥ 1}`: it is
`∫₁^∞ {√v} v^{-s-1} dv` written in `w = √v` (`RMF.fracMellin_eq_integral_sqrt`), and the kernel's
transform is `ψ̂(s) = φ̂(s + ½)` (`RMF.integral_fracKernel_mul_cpow`).  Absolutely convergent for
`Re s > 0`. -/
noncomputable def fracMellin (s : ℂ) : ℂ :=
  2 * ∫ w in Set.Ioi (1 : ℝ), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-2 * s - 1)

/-! ### Unit intervals -/

/-- `{x} = x - n` on `[n, n + 1)`. -/
lemma fract_eq_sub_natCast {x : ℝ} {n : ℕ} (h1 : (n : ℝ) ≤ x) (h2 : x < n + 1) :
    Int.fract x = x - n := by
  have hfl : ⌊x⌋ = (n : ℤ) := Int.floor_eq_iff.2 ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [← Int.self_sub_floor, hfl, Int.cast_natCast]

/-- Interval integrals agree when the integrands agree on the open interval. -/
lemma intervalIntegral_congr_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Ioo a b, f x = g x) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- **An integral over `(K, ∞)` is the sum of its unit pieces.** -/
lemma hasSum_intervalIntegral_of_integrableOn_Ioi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {K : ℝ} (hf : IntegrableOn f (Set.Ioi K)) :
    HasSum (fun n : ℕ => ∫ w in (K + n)..(K + n + 1), f w) (∫ w in Set.Ioi K, f w) := by
  have hU : (⋃ n : ℕ, Set.Ioc (K + n) (K + n + 1)) = Set.Ioi K := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨n, h1, -⟩
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hw
      have hpos : 0 < w - K := by linarith
      have h1 : 1 ≤ ⌈w - K⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
      refine ⟨⌈w - K⌉₊ - 1, ?_, ?_⟩
      · have := Nat.ceil_lt_add_one hpos.le
        rw [Nat.cast_sub h1, Nat.cast_one]
        linarith
      · rw [Nat.cast_sub h1, Nat.cast_one]
        linarith [Nat.le_ceil (w - K)]
  have hd : Pairwise (Function.onFun Disjoint fun n : ℕ => Set.Ioc (K + n) (K + n + 1)) := by
    intro m n hmn
    have h := Set.pairwise_disjoint_Ioc_add_intCast K (show (m : ℤ) ≠ n by exact_mod_cast hmn)
    simpa only [Function.onFun, Int.cast_natCast] using h
  have h := hasSum_integral_iUnion (fun n => measurableSet_Ioc) hd (by rw [hU]; exact hf)
  rw [hU] at h
  have hfun : (fun n : ℕ => ∫ w in (K + n)..(K + n + 1), f w)
      = fun n : ℕ => ∫ w in Set.Ioc (K + n) (K + n + 1), f w :=
    funext fun n => intervalIntegral.integral_of_le (by linarith)
  rw [hfun]
  exact h

/-! ### Integrability -/

lemma measurable_fract_mul_cpow (z : ℂ) :
    Measurable fun w : ℝ => ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ z :=
  (Complex.measurable_ofReal.comp measurable_fract).mul (by fun_prop)

lemma norm_fract_mul_cpow {w : ℝ} (hw : 0 < w) (z : ℂ) :
    ‖((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ z‖ = Int.fract w * w ^ z.re := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg w),
    Complex.norm_cpow_eq_rpow_re_of_pos hw]

/-- `{w} w^z` is integrable on `(1, ∞)` for `Re z < -1`. -/
lemma integrableOn_fract_mul_cpow {z : ℂ} (hz : z.re < -1) :
    IntegrableOn (fun w : ℝ => ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ z) (Set.Ioi 1) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hz one_pos)
    (measurable_fract_mul_cpow z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hw0 : (0 : ℝ) < w := lt_trans one_pos hw
  rw [norm_fract_mul_cpow hw0]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hw0.le _) (Int.fract_lt_one w).le

/-- `{w}^k w^r` is integrable on `(c, ∞)`, `c > 0`, for `r < -1`. -/
lemma integrableOn_fract_pow_mul_rpow (k : ℕ) {r c : ℝ} (hr : r < -1) (hc : 0 < c) :
    IntegrableOn (fun w : ℝ => Int.fract w ^ k * w ^ r) (Set.Ioi c) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hr hc)
    ((measurable_fract.pow_const k).mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hw0 : (0 : ℝ) < w := lt_trans hc hw
  have hf0 := Int.fract_nonneg w
  have hfk : Int.fract w ^ k ≤ 1 := pow_le_one₀ hf0 (Int.fract_lt_one w).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hf0 k) (Real.rpow_nonneg hw0.le _))]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hw0.le _) hfk

/-- **Integrability from a support and a power bound.**  A function vanishing on `(0, c]` and
bounded by `C u^r`, `r < -1`, on `(c, ∞)` is integrable on `(0, ∞)`. -/
lemma integrableOn_Ioi_zero_of_le_rpow {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {c : ℝ}
    (hc : 0 < c) (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi c)))
    (h0 : ∀ u ∈ Set.Ioc 0 c, f u = 0) {C r : ℝ} (hr : r < -1)
    (hb : ∀ u ∈ Set.Ioi c, ‖f u‖ ≤ C * u ^ r) : IntegrableOn f (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le]
  refine IntegrableOn.union ?_ ?_
  · exact (integrableOn_zero).congr_fun (fun u hu => (h0 u hu).symm) measurableSet_Ioc
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hr hc).const_mul C) hf ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hb u hu

/-! ### The substitution `v = w²` and the kernel's Mellin transform -/

/-- `∫₀^∞ g(u) du = ∫₀^∞ 2w·g(w²) dw`. -/
lemma integral_Ioi_eq_integral_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∫ u in Set.Ioi (0 : ℝ), g u = ∫ w in Set.Ioi (0 : ℝ), (2 * w) • g (w ^ (2 : ℝ)) := by
  rw [← integral_comp_rpow_Ioi g (p := 2) two_ne_zero]
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  norm_num

/-- **`φ̂` is the Mellin transform of `φ(v) = {√v}·1_{v ≥ 1}`**: `φ̂(s) = ∫₁^∞ {√v} v^{-s-1} dv`,
for every `s` (the substitution `v = w²` needs no convergence). -/
theorem fracMellin_eq_integral_sqrt (s : ℂ) :
    fracMellin s
      = ∫ v in Set.Ioi (1 : ℝ), ((Int.fract (Real.sqrt v) : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1) := by
  set h : ℝ → ℂ := fun v => ((Int.fract (Real.sqrt v) : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1) with hh
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi zero_le_one
  have h1 : ∫ v in Set.Ioi (1 : ℝ), h v
      = ∫ v in Set.Ioi (0 : ℝ), Set.indicator (Set.Ioi 1) h v := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      (fun v hv => Set.indicator_of_notMem hv.2 h)]
    exact setIntegral_congr_fun measurableSet_Ioi fun v hv => (Set.indicator_of_mem hv h).symm
  have h2 : ∀ w ∈ Set.Ioi (0 : ℝ) \ Set.Ioi 1,
      (2 * w) • Set.indicator (Set.Ioi 1) h (w ^ (2 : ℝ)) = 0 := by
    intro w hw
    have hw0 : 0 < w := hw.1
    have hw1 : w ≤ 1 := not_lt.1 hw.2
    have hle : w ^ (2 : ℝ) ≤ 1 := Real.rpow_le_one hw0.le hw1 (by norm_num)
    rw [Set.indicator_of_notMem (show w ^ (2 : ℝ) ∉ Set.Ioi (1 : ℝ) from not_lt.2 hle), smul_zero]
  rw [h1, integral_Ioi_eq_integral_sq,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub h2, fracMellin,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw0 : (0 : ℝ) < w := lt_trans one_pos hw
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw0.ne'
  have hw2 : w ^ (2 : ℝ) = w ^ 2 := Real.rpow_two w
  have hmem : w ^ (2 : ℝ) ∈ Set.Ioi (1 : ℝ) := by
    rw [hw2]
    exact one_lt_pow₀ (Set.mem_Ioi.1 hw) two_ne_zero
  have hsq : Real.sqrt (w ^ (2 : ℝ)) = w := by rw [hw2, Real.sqrt_sq hw0.le]
  have he : (-2 * s - 1 : ℂ) = ((2 : ℝ) : ℂ) * (-s - 1) + 1 := by push_cast; ring
  rw [Set.indicator_of_mem hmem, hh]
  simp only
  rw [hsq, ← Complex.cpow_mul_ofReal_nonneg hw0.le, he, Complex.cpow_add _ _ hwC,
    Complex.cpow_one, Complex.real_smul]
  push_cast
  ring

/-- `ψ(v) = 0` for `v ≤ 1`. -/
lemma fracKernel_eq_zero_of_le_one {v : ℝ} (hv : v ≤ 1) : fracKernel v = 0 := by
  unfold fracKernel
  split_ifs with h
  · rw [le_antisymm hv h]
    simp
  · rfl

lemma fracKernel_nonneg (v : ℝ) : 0 ≤ fracKernel v := by
  unfold fracKernel
  split_ifs
  · exact div_nonneg (Int.fract_nonneg _) (Real.sqrt_nonneg _)
  · exact le_rfl

lemma measurable_fracKernel : Measurable fracKernel :=
  Measurable.ite measurableSet_Ici
    ((measurable_fract.comp Real.continuous_sqrt.measurable).div Real.continuous_sqrt.measurable)
    measurable_const

/-- `ψ(u/k) ≤ √k·u^{-1/2}`: `{√v} < 1`. -/
lemma fracKernel_div_le {u k : ℝ} (hu : 0 < u) (hk : 0 < k) :
    fracKernel (u / k) ≤ Real.sqrt k * u ^ (-(1 / 2 : ℝ)) := by
  have hrhs : 0 ≤ Real.sqrt k * u ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hu.le _)
  unfold fracKernel
  split_ifs with h
  · have hsq : 0 < Real.sqrt (u / k) := Real.sqrt_pos.2 (div_pos hu hk)
    have hval : Real.sqrt k * u ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (u / k) := by
      rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, Real.sqrt_div' u hk.le]
      have hu' : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
      have hk' : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
      field_simp
    rw [hval]
    exact div_le_div_of_nonneg_right (Int.fract_lt_one _).le hsq.le
  · exact hrhs

/-- **The kernel's Mellin transform**: `∫₀^∞ ψ(u) u^{-s-1} du = φ̂(s + ½)`, for every `s`. -/
theorem integral_fracKernel_mul_cpow (s : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), (fracKernel u : ℂ) * (u : ℂ) ^ (-s - 1) = fracMellin (s + 1 / 2) := by
  have hz : ∀ u ∈ Set.Ioi (0 : ℝ) \ Set.Ioi 1, (fracKernel u : ℂ) * (u : ℂ) ^ (-s - 1) = 0 := by
    intro u hu
    rw [fracKernel_eq_zero_of_le_one (not_lt.1 hu.2), Complex.ofReal_zero, zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ioi_subset_Ioi zero_le_one) hz, fracMellin_eq_integral_sqrt]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu0.ne'
  have hsq : ((Real.sqrt u : ℝ) : ℂ) = (u : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu0.le]
    norm_num
  have hpow : (u : ℂ) ^ (-(s + 1 / 2) - 1) = (u : ℂ) ^ (-s - 1) / (u : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_sub _ _ huC]
    ring_nf
  rw [fracKernel, if_pos (le_of_lt hu), Complex.ofReal_div, hsq, hpow]
  ring

/-- **The dilated kernel's Mellin transform**: `∫₀^∞ ψ(u/k) u^{-s-1} du = k^{-s} φ̂(s + ½)` for
`k > 0`. -/
theorem integral_fracKernel_div_mul_cpow {k : ℝ} (hk : 0 < k) (s : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), (fracKernel (u / k) : ℂ) * (u : ℂ) ^ (-s - 1)
      = (k : ℂ) ^ (-s) * fracMellin (s + 1 / 2) := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk.ne'
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ => (fracKernel (u / k) : ℂ) * (u : ℂ) ^ (-s - 1)) 0 hk
  rw [mul_zero] at h
  have hL : ∫ x in Set.Ioi (0 : ℝ), (fracKernel (k * x / k) : ℂ) * ((k * x : ℝ) : ℂ) ^ (-s - 1)
      = (k : ℂ) ^ (-s - 1) * fracMellin (s + 1 / 2) := by
    rw [← integral_fracKernel_mul_cpow, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [mul_div_cancel_left₀ x hk.ne', Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hk.le (le_of_lt hx)]
    ring
  rw [hL, Complex.real_smul] at h
  have hpow : (k : ℂ) ^ (-s) = (k : ℂ) ^ (-s - 1) * (k : ℂ) := by
    conv_lhs => rw [show -s = (-s - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hkC, Complex.cpow_one]
  have hk' : ((k⁻¹ : ℝ) : ℂ) = (k : ℂ)⁻¹ := Complex.ofReal_inv k
  rw [hk'] at h
  have h' : ∫ u in Set.Ioi (0 : ℝ), (fracKernel (u / k) : ℂ) * (u : ℂ) ^ (-s - 1)
      = (k : ℂ) * ((k : ℂ) ^ (-s - 1) * fracMellin (s + 1 / 2)) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hkC, one_mul]
  rw [h', hpow]
  ring

/-! ### The bound `|φ̂| ≤ 2(1 - γ)` on `Re s ≥ ½` -/

/-- `‖φ̂(s)‖ ≤ 2∫₁^∞ {w} w^{-2 Re s - 1} dw`. -/
lemma norm_fracMellin_le_integral (s : ℂ) :
    ‖fracMellin s‖ ≤ 2 * ∫ w in Set.Ioi (1 : ℝ), Int.fract w * w ^ (-2 * s.re - 1) := by
  rw [fracMellin, norm_mul, Complex.norm_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  rw [norm_fract_mul_cpow (lt_trans one_pos hw)]
  congr 2
  simp

/-- The unit pieces of `∫₁^∞ {w}/w² dw` are Mathlib's `ZetaAsymptotics.term (n + 1) 1`. -/
lemma intervalIntegral_fract_mul_rpow_neg_two_eq_term (n : ℕ) :
    ∫ w in ((1 : ℝ) + n)..((1 : ℝ) + n + 1), Int.fract w * w ^ (-2 : ℝ)
      = ZetaAsymptotics.term (n + 1) 1 := by
  have ha : ((n + 1 : ℕ) : ℝ) = 1 + n := by push_cast; ring
  rw [ZetaAsymptotics.term, ha]
  refine intervalIntegral_congr_Ioo (by linarith) fun x hx => ?_
  have hx0 : 0 < x := by
    have := hx.1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfr := fract_eq_sub_natCast (n := n + 1) (x := x) (by push_cast; linarith [hx.1])
    (by push_cast; linarith [hx.2])
  rw [hfr, ha, Real.rpow_neg hx0.le, show (1 : ℝ) + 1 = 2 by norm_num, div_eq_mul_inv]

/-- **`∫₁^∞ {w}/w² dw = 1 - γ`**, from `ZetaAsymptotics.term_tsum_one`. -/
theorem integral_fract_mul_rpow_neg_two :
    ∫ w in Set.Ioi (1 : ℝ), Int.fract w * w ^ (-2 : ℝ) = 1 - Real.eulerMascheroniConstant := by
  have hint : IntegrableOn (fun w : ℝ => Int.fract w * w ^ (-2 : ℝ)) (Set.Ioi 1) := by
    simpa only [pow_one] using
      integrableOn_fract_pow_mul_rpow 1 (by norm_num : (-2 : ℝ) < -1) one_pos
  have h := hasSum_intervalIntegral_of_integrableOn_Ioi hint
  simp_rw [intervalIntegral_fract_mul_rpow_neg_two_eq_term] at h
  exact h.unique ZetaAsymptotics.term_tsum_one

/-- **`|φ̂(s)| ≤ 2(1 - γ)` for `Re s ≥ ½`**: `|φ̂(s)| ≤ φ̂(Re s) ≤ φ̂(½) = 2(1 - γ)`. -/
theorem norm_fracMellin_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖fracMellin s‖ ≤ 2 * (1 - Real.eulerMascheroniConstant) := by
  refine le_trans (norm_fracMellin_le_integral s) ?_
  rw [← integral_fract_mul_rpow_neg_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 : IntegrableOn (fun w : ℝ => Int.fract w * w ^ (-2 * s.re - 1)) (Set.Ioi 1) := by
    simpa only [pow_one] using
      integrableOn_fract_pow_mul_rpow 1 (by linarith : -2 * s.re - 1 < -1) one_pos
  have h2 : IntegrableOn (fun w : ℝ => Int.fract w * w ^ (-2 : ℝ)) (Set.Ioi 1) := by
    simpa only [pow_one] using
      integrableOn_fract_pow_mul_rpow 1 (by norm_num : (-2 : ℝ) < -1) one_pos
  refine setIntegral_mono_on h1 h2 measurableSet_Ioi fun w hw => ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (le_of_lt hw) (by linarith)) (Int.fract_nonneg w)

/-- `2(1 - γ) ≤ 0.8456`, from `γ ≥ 0.577215` (`hγ_lo`). -/
lemma two_mul_one_sub_eulerMascheroni_le : 2 * (1 - Real.eulerMascheroniConstant) ≤ 0.8456 := by
  have := hγ_lo
  norm_num at this ⊢
  linarith

/-- **`|φ̂(s)| ≤ 0.8456` for `Re s ≥ ½`.** -/
theorem norm_fracMellin_le_numeral {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖fracMellin s‖ ≤ 0.8456 :=
  le_trans (norm_fracMellin_le hs) two_mul_one_sub_eulerMascheroni_le

/-- **`|φ̂(s)|² ≤ 0.7151` for `Re s ≥ ½`.** -/
theorem normSq_fracMellin_le_numeral {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖fracMellin s‖ ^ 2 ≤ 0.7151 := by
  have h := norm_fracMellin_le_numeral hs
  have h0 := norm_nonneg (fracMellin s)
  nlinarith

/-! ### Conjugation symmetry and continuity -/

/-- **Conjugation symmetry**: `φ̂(s̄) = conj φ̂(s)`. -/
theorem fracMellin_conj (s : ℂ) :
    fracMellin (starRingEnd ℂ s) = starRingEnd ℂ (fracMellin s) := by
  rw [fracMellin, fracMellin, map_mul, map_ofNat, ← integral_conj]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw0 : (0 : ℝ) < w := lt_trans one_pos hw
  have harg : (w : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hw0.le]
    exact Real.pi_ne_zero.symm
  have hc := Complex.cpow_conj (w : ℂ) (-2 * s - 1) harg
  rw [Complex.conj_ofReal] at hc
  have he : -2 * starRingEnd ℂ s - 1 = starRingEnd ℂ (-2 * s - 1) := by
    rw [map_sub, map_mul, map_neg, map_ofNat, map_one]
  rw [map_mul, Complex.conj_ofReal, he, hc]

/-- `|φ̂(½ + σ - it)| = |φ̂(½ + σ + it)|`. -/
theorem norm_fracMellin_neg (σ t : ℝ) :
    ‖fracMellin (1 / 2 + σ + (-t : ℝ) * Complex.I)‖
      = ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ := by
  have h : (1 / 2 + σ + (-t : ℝ) * Complex.I : ℂ)
      = starRingEnd ℂ (1 / 2 + σ + t * Complex.I) := by
    apply Complex.ext <;> simp
  rw [h, fracMellin_conj, Complex.norm_conj]

/-- **`φ̂` is continuous on `Re s > 0`**; in particular it is regular at `½`, where the closed
form's pole `1/(s - ½)` cancels against `ζ(2s)/s`. -/
theorem continuousAt_fracMellin {s₀ : ℂ} (hs₀ : 0 < s₀.re) : ContinuousAt fracMellin s₀ := by
  unfold fracMellin
  refine continuousAt_const.mul ?_
  have hnhds : ∀ᶠ s in nhds s₀, s₀.re / 2 < s.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by linarith))
  refine continuousAt_of_dominated (bound := fun w : ℝ => w ^ (-s₀.re - 1))
    (Filter.Eventually.of_forall fun s => (measurable_fract_mul_cpow _).aestronglyMeasurable)
    ?_ (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) ?_
  · filter_upwards [hnhds] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : (0 : ℝ) < w := lt_trans one_pos hw
    rw [norm_fract_mul_cpow hw0]
    have hre : (-2 * s - 1).re = -2 * s.re - 1 := by simp
    rw [hre]
    calc Int.fract w * w ^ (-2 * s.re - 1) ≤ 1 * w ^ (-2 * s.re - 1) :=
          mul_le_mul_of_nonneg_right (Int.fract_lt_one w).le (Real.rpow_nonneg hw0.le _)
      _ ≤ w ^ (-s₀.re - 1) := by
          rw [one_mul]
          exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hw) (by linarith)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (lt_trans one_pos hw).ne'
    refine continuousAt_const.mul (ContinuousAt.const_cpow ?_ (Or.inl hwC))
    fun_prop

/-- **Continuity on vertical lines**: `t ↦ φ̂(½ + σ + it)` is continuous for `σ > -½`. -/
theorem continuous_fracMellin_line {σ : ℝ} (hσ : -1 / 2 < σ) :
    Continuous fun t : ℝ => fracMellin (1 / 2 + σ + t * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hre : 0 < (1 / 2 + σ + t * Complex.I : ℂ).re := by
    simp
    linarith
  exact (continuousAt_fracMellin hre).comp
    (f := fun t : ℝ => (1 / 2 + (σ : ℂ) + (t : ℂ) * Complex.I)) (by fun_prop)

/-! ### The decay cap

On `[1, K]` the integral of `{w}w^{-a-1}`, `a = 2s`, is summed by parts:
`∫_m^{m+1}(w - m)w^{-a-1}dw = ((m+1)^{1-a} - m^{1-a})/(a(1-a)) - (m+1)^{-a}/a`, the first part
telescopes, and `|(n+1)^{-a}| ≤ 1/(n+1)` for `Re a ≥ 1`.  Beyond `K`, `{w}w^{-Re a - 1} ≤ {w}/w²`,
whose integral over `[m, m+1]` is at most `1/(2m(m+1))`: on that interval `{w}/w²` lies below the
derivative `1/(2m) - m/(2w²)` of `w/(2m) + m/(2w)`. -/

/-- `{w} ≤ w - m` for `w ≥ m`. -/
lemma fract_le_sub_natCast {w : ℝ} {m : ℕ} (h : (m : ℝ) ≤ w) : Int.fract w ≤ w - m := by
  have hfl : (m : ℤ) ≤ ⌊w⌋ := Int.le_floor.2 (by exact_mod_cast h)
  have hfl' : (m : ℝ) ≤ (⌊w⌋ : ℝ) := by exact_mod_cast hfl
  rw [← Int.self_sub_floor]
  linarith

lemma intervalIntegrable_fract_mul_rpow (r : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun w : ℝ => Int.fract w * w ^ r) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := max (a ^ r) (b ^ r)) measure_Ioc_lt_top.ne
    ((measurable_fract.mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have hw0 : 0 < w := lt_trans ha hw.1
  have hf0 := Int.fract_nonneg w
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 (Real.rpow_nonneg hw0.le _))]
  have hpow : w ^ r ≤ max (a ^ r) (b ^ r) := by
    rcases le_total 0 r with hr | hr
    · exact le_trans (Real.rpow_le_rpow hw0.le hw.2 hr) (le_max_right _ _)
    · exact le_trans (Real.rpow_le_rpow_of_nonpos ha hw.1.le hr) (le_max_left _ _)
  calc Int.fract w * w ^ r ≤ 1 * w ^ r :=
        mul_le_mul_of_nonneg_right (Int.fract_lt_one w).le (Real.rpow_nonneg hw0.le _)
    _ ≤ max (a ^ r) (b ^ r) := by rw [one_mul]; exact hpow

lemma intervalIntegrable_fract_mul_cpow (z : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun w : ℝ => ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ z) volume a b := by
  have h := intervalIntegrable_fract_mul_rpow z.re ha hab
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at h ⊢
  refine Integrable.mono' h.norm (measurable_fract_mul_cpow z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have hw0 : 0 < w := lt_trans ha hw.1
  rw [norm_fract_mul_cpow hw0, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Int.fract_nonneg w) (Real.rpow_nonneg hw0.le _))]

/-- **`∫_m^{m+1} {w}/w² dw ≤ 1/(2m(m+1))`.** -/
lemma intervalIntegral_fract_mul_rpow_neg_two_le {m : ℕ} (hm : 1 ≤ m) :
    ∫ w in (m : ℝ)..(m + 1), Int.fract w * w ^ (-2 : ℝ) ≤ 1 / (2 * m * (m + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ m + 1 := by linarith
  set G : ℝ → ℝ := fun w => w / (2 * m) + m / (2 * w) with hG
  set g : ℝ → ℝ := fun w => 1 / (2 * m) - m / (2 * w ^ 2) with hg
  have hderiv : ∀ w ∈ Set.uIcc (m : ℝ) (m + 1), HasDerivAt G (g w) w := by
    intro w hw
    rw [Set.uIcc_of_le hle] at hw
    have hw0 : 0 < w := lt_of_lt_of_le hm0 hw.1
    have h1 : HasDerivAt (fun w : ℝ => w / (2 * m)) (1 / (2 * m)) w :=
      (hasDerivAt_id w).div_const (2 * m)
    have h2 : HasDerivAt (fun w : ℝ => (m : ℝ) / (2 * w))
        ((0 * (2 * w) - m * (2 * 1)) / (2 * w) ^ 2) w :=
      (hasDerivAt_const w (m : ℝ)).div ((hasDerivAt_id w).const_mul 2) (by positivity)
    refine (h1.add h2).congr_deriv ?_
    change 1 / (2 * (m : ℝ)) + (0 * (2 * w) - m * (2 * 1)) / (2 * w) ^ 2
      = 1 / (2 * (m : ℝ)) - m / (2 * w ^ 2)
    field_simp
    ring
  have hgc : ContinuousOn g (Set.uIcc (m : ℝ) (m + 1)) := by
    refine ContinuousOn.sub continuousOn_const (ContinuousOn.div continuousOn_const
      (by fun_prop) fun w hw => ?_)
    rw [Set.uIcc_of_le hle] at hw
    have hw0 : 0 < w := lt_of_lt_of_le hm0 hw.1
    positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hgc.intervalIntegrable
  have hmono : ∫ w in (m : ℝ)..(m + 1), Int.fract w * w ^ (-2 : ℝ)
      ≤ ∫ w in (m : ℝ)..(m + 1), g w := by
    refine intervalIntegral.integral_mono_on hle
      (intervalIntegrable_fract_mul_rpow (-2) hm0 hle) hgc.intervalIntegrable fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le hm0 hw.1
    have hfr := fract_le_sub_natCast hw.1
    have hw2 : w ^ (-2 : ℝ) = 1 / w ^ 2 := by
      rw [Real.rpow_neg hw0.le, Real.rpow_two, one_div]
    have hkey : g w - (w - m) * (1 / w ^ 2) = (w - m) ^ 2 / (2 * m * w ^ 2) := by
      simp only [hg]
      field_simp
      ring
    have hsq : 0 ≤ (w - m) ^ 2 / (2 * m * w ^ 2) := by positivity
    rw [hw2]
    calc Int.fract w * (1 / w ^ 2) ≤ (w - m) * (1 / w ^ 2) :=
          mul_le_mul_of_nonneg_right hfr (by positivity)
      _ ≤ g w := by linarith
  rw [hFTC] at hmono
  refine le_trans hmono (le_of_eq ?_)
  simp only [hG]
  field_simp
  ring

/-- `∑ₙ 1/(2(N+n)(N+n+1)) = 1/(2N)`, by telescoping. -/
lemma hasSum_inv_two_mul_succ {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun n : ℕ => 1 / (2 * ((N : ℝ) + n) * ((N : ℝ) + n + 1))) (1 / (2 * N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpart : ∀ M : ℕ, ∑ n ∈ Finset.range M, 1 / (2 * ((N : ℝ) + n) * ((N : ℝ) + n + 1))
      = 1 / (2 * N) - 1 / (2 * ((N : ℝ) + M)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      push_cast
      field_simp
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  simp_rw [hpart]
  have hlim : Filter.Tendsto (fun M : ℕ => 1 / (2 * ((N : ℝ) + M))) Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    refine Filter.Tendsto.const_mul_atTop (by norm_num) ?_
    exact Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.sub hlim

/-- **The tail**: `∫_N^∞ {w}/w² dw ≤ 1/(2N)` for `N ≥ 1`. -/
lemma integral_Ioi_fract_mul_rpow_neg_two_le {N : ℕ} (hN : 1 ≤ N) :
    ∫ w in Set.Ioi (N : ℝ), Int.fract w * w ^ (-2 : ℝ) ≤ 1 / (2 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : IntegrableOn (fun w : ℝ => Int.fract w * w ^ (-2 : ℝ)) (Set.Ioi N) := by
    simpa only [pow_one] using
      integrableOn_fract_pow_mul_rpow 1 (by norm_num : (-2 : ℝ) < -1) hN0
  refine hasSum_le (fun n => ?_) (hasSum_intervalIntegral_of_integrableOn_Ioi hint)
    (hasSum_inv_two_mul_succ hN)
  have h := intervalIntegral_fract_mul_rpow_neg_two_le (m := N + n) (by omega)
  push_cast at h
  exact h

/-- **One unit interval, summed by parts**: for `m ≥ 1`, `a ≠ 0, 1`,
`∫_m^{m+1} {w}w^{-a-1}dw = ((m+1)^{1-a} - m^{1-a})/(a(1-a)) - (m+1)^{-a}/a`. -/
lemma intervalIntegral_fract_mul_cpow_eq {m : ℕ} (hm : 1 ≤ m) {a : ℂ} (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) :
    ∫ w in (m : ℝ)..(m + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)
      = (((m : ℂ) + 1) ^ (1 - a) - (m : ℂ) ^ (1 - a)) / (a * (1 - a))
        - ((m : ℂ) + 1) ^ (-a) / a := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ m + 1 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (m : ℝ) (m + 1) := by
    rw [Set.uIcc_of_le hle]
    intro h
    linarith [h.1]
  have hcongr : ∫ w in (m : ℝ)..(m + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)
      = ∫ w in (m : ℝ)..(m + 1), ((w : ℂ) ^ (-a) - (m : ℂ) * (w : ℂ) ^ (-a - 1)) := by
    refine intervalIntegral_congr_Ioo hle fun w hw => ?_
    have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (lt_trans hm0 hw.1).ne'
    have hp : (w : ℂ) ^ (-a) = (w : ℂ) ^ (-a - 1) * (w : ℂ) := by
      conv_lhs => rw [show -a = (-a - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ hwC, Complex.cpow_one]
    rw [fract_eq_sub_natCast hw.1.le hw.2, hp]
    push_cast
    ring
  have hi1 : IntervalIntegrable (fun w : ℝ => (w : ℂ) ^ (-a)) volume m (m + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  have hi2 : IntervalIntegrable (fun w : ℝ => (m : ℂ) * (w : ℂ) ^ (-a - 1)) volume m (m + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _
  have hr1 : -a ≠ -1 := fun h => ha1 (neg_inj.1 h)
  have hr2 : -a - 1 ≠ -1 := fun h => ha0 (by linear_combination -h)
  rw [hcongr, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨hr1, h0⟩), integral_cpow (Or.inr ⟨hr2, h0⟩)]
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hm1C : (m : ℂ) + 1 ≠ 0 := by
    have : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact_mod_cast this
  have ha1' : 1 - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha1)
  have ha1'' : -a + 1 ≠ 0 := by rwa [neg_add_eq_sub]
  have e1 : ((((m : ℝ) + 1 : ℝ) : ℂ)) = (m : ℂ) + 1 := by push_cast; ring
  have e2 : (((m : ℝ) : ℂ)) = (m : ℂ) := by push_cast; ring
  rw [e1, e2, show -a - 1 + 1 = -a by ring, show -a + 1 = 1 - a by ring]
  have p1 : ((m : ℂ) + 1) ^ (1 - a) = ((m : ℂ) + 1) * ((m : ℂ) + 1) ^ (-a) := by
    rw [show 1 - a = 1 + -a by ring, Complex.cpow_add _ _ hm1C, Complex.cpow_one]
  have p2 : (m : ℂ) ^ (1 - a) = (m : ℂ) * (m : ℂ) ^ (-a) := by
    rw [show 1 - a = 1 + -a by ring, Complex.cpow_add _ _ hmC, Complex.cpow_one]
  rw [p1, p2]
  field_simp
  ring

/-- **The head `[1, K+1]`, summed by parts**: for `a ≠ 0, 1`,
`∫_1^{K+1} {w}w^{-a-1}dw = ((K+1)^{1-a} - 1)/(a(1-a)) - (∑_{n<K}(n+2)^{-a})/a`. -/
lemma intervalIntegral_one_fract_mul_cpow_eq (K : ℕ) {a : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∫ w in (1 : ℝ)..(K + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)
      = (((K : ℂ) + 1) ^ (1 - a) - 1) / (a * (1 - a))
        - (∑ n ∈ Finset.range K, ((n : ℂ) + 2) ^ (-a)) / a := by
  have hint : ∀ k < K, IntervalIntegrable
      (fun w : ℝ => ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)) volume
      ((fun n : ℕ => (n : ℝ) + 1) k) ((fun n : ℕ => (n : ℝ) + 1) (k + 1)) := by
    intro k _
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact intervalIntegrable_fract_mul_cpow (-a - 1) hk0 hle
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp only [Nat.cast_zero, zero_add] at hsum
  push_cast at hsum
  rw [← hsum]
  have hterm : ∀ k ∈ Finset.range K,
      ∫ w in ((k : ℝ) + 1)..((k : ℝ) + 1 + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)
        = ((((k : ℂ) + 1) + 1) ^ (1 - a) - ((k : ℂ) + 1) ^ (1 - a)) / (a * (1 - a))
          - ((k : ℂ) + 2) ^ (-a) / a := by
    intro k _
    have h := intervalIntegral_fract_mul_cpow_eq (m := k + 1) (by omega) ha0 ha1
    push_cast at h
    rw [h, show (k : ℂ) + 1 + 1 = (k : ℂ) + 2 by ring]
  have htel : ∑ i ∈ Finset.range K, (((i : ℂ) + 1 + 1) ^ (1 - a) - ((i : ℂ) + 1) ^ (1 - a))
      = ((K : ℂ) + 1) ^ (1 - a) - 1 := by
    have h := Finset.sum_range_sub (fun n : ℕ => ((n : ℂ) + 1) ^ (1 - a)) K
    push_cast at h
    rw [h]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    htel]

/-- `∑_{n<K} 1/(n+2) = H_{K+1} - 1`. -/
lemma sum_range_one_div_add_two (K : ℕ) :
    ∑ n ∈ Finset.range K, 1 / ((n : ℝ) + 2) = (harmonic (K + 1) : ℝ) - 1 := by
  induction K with
  | zero => simp [harmonic_succ]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ (K + 1)]
    push_cast
    ring

/-- **The head is small**: for `Re a ≥ 1` and `Im a ≠ 0`,
`|∫_1^{K+1} {w}w^{-a-1}dw| ≤ (2/|Im a| + H_{K+1} - 1)/|a|`. -/
lemma norm_intervalIntegral_one_fract_mul_cpow_le (K : ℕ) {a : ℂ} (ha : 1 ≤ a.re)
    (him : a.im ≠ 0) :
    ‖∫ w in (1 : ℝ)..(K + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)‖
      ≤ (2 / |a.im| + ((harmonic (K + 1) : ℝ) - 1)) / ‖a‖ := by
  have ha0 : a ≠ 0 := fun h => him (by rw [h, Complex.zero_im])
  have ha1 : a ≠ 1 := fun h => him (by rw [h, Complex.one_im])
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have him0 : 0 < |a.im| := abs_pos.2 him
  rw [intervalIntegral_one_fract_mul_cpow_eq K ha0 ha1]
  have hK : ‖((K : ℂ) + 1) ^ (1 - a)‖ ≤ 1 := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
      have := (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
      linarith
    have hc : ((K : ℂ) + 1) = (((K : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    refine Real.rpow_le_one_of_one_le_of_nonpos hK1 ?_
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h1a : |a.im| ≤ ‖1 - a‖ := by
    have h := Complex.abs_im_le_norm (1 - a)
    rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
  have hA : ‖(((K : ℂ) + 1) ^ (1 - a) - 1) / (a * (1 - a))‖ ≤ 2 / |a.im| / ‖a‖ := by
    have hnum : ‖((K : ℂ) + 1) ^ (1 - a) - 1‖ ≤ 2 := by
      calc ‖((K : ℂ) + 1) ^ (1 - a) - 1‖ ≤ ‖((K : ℂ) + 1) ^ (1 - a)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have h1a0 : 0 < ‖1 - a‖ := lt_of_lt_of_le him0 h1a
    rw [norm_div, norm_mul]
    calc ‖((K : ℂ) + 1) ^ (1 - a) - 1‖ / (‖a‖ * ‖1 - a‖) ≤ 2 / (‖a‖ * ‖1 - a‖) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 2 / (‖a‖ * |a.im|) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_left h1a hna.le)
      _ = 2 / |a.im| / ‖a‖ := by rw [div_div, mul_comm]
  have hB : ‖(∑ n ∈ Finset.range K, ((n : ℂ) + 2) ^ (-a)) / a‖
      ≤ ((harmonic (K + 1) : ℝ) - 1) / ‖a‖ := by
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ hna.le
    rw [← sum_range_one_div_add_two]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    have hc : ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    calc ((n : ℝ) + 2) ^ (-a.re) ≤ ((n : ℝ) + 2) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn2 (by linarith)
      _ = 1 / ((n : ℝ) + 2) := by rw [Real.rpow_neg_one, one_div]
  calc ‖(((K : ℂ) + 1) ^ (1 - a) - 1) / (a * (1 - a))
        - (∑ n ∈ Finset.range K, ((n : ℂ) + 2) ^ (-a)) / a‖
      ≤ ‖(((K : ℂ) + 1) ^ (1 - a) - 1) / (a * (1 - a))‖
        + ‖(∑ n ∈ Finset.range K, ((n : ℂ) + 2) ^ (-a)) / a‖ := norm_sub_le _ _
    _ ≤ 2 / |a.im| / ‖a‖ + ((harmonic (K + 1) : ℝ) - 1) / ‖a‖ := add_le_add hA hB
    _ = (2 / |a.im| + ((harmonic (K + 1) : ℝ) - 1)) / ‖a‖ := by ring

/-- **The decay cap**: for `Re s ≥ ½`, `t = Im s ≠ 0` and `K ≥ 1`,
`|φ̂(s)| ≤ (2/|2s|)(1/|t| + H_K - 1) + 1/K`, `H_K` the harmonic number. -/
theorem norm_fracMellin_le_cap {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : s.im ≠ 0) {K : ℕ}
    (hK : 1 ≤ K) :
    ‖fracMellin s‖ ≤ 2 / ‖2 * s‖ * (1 / |s.im| + ((harmonic K : ℝ) - 1)) + 1 / K := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hre2 : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  have him2 : (2 * s).im = 2 * s.im := by simp [Complex.mul_im]
  set a : ℂ := 2 * s with hadef
  have hre : 1 ≤ a.re := by
    rw [hre2]
    linarith
  have him : a.im = 2 * s.im := him2
  have himne : a.im ≠ 0 := by rw [him]; exact mul_ne_zero two_ne_zero ht
  have hexp : -2 * s - 1 = -a - 1 := by rw [hadef]; ring
  have hc0 : (0 : ℝ) < (K' : ℝ) + 1 := by positivity
  have hc1 : (1 : ℝ) ≤ (K' : ℝ) + 1 := by
    have := (Nat.cast_nonneg K' : (0 : ℝ) ≤ K')
    linarith
  have hreal : -a.re - 1 < -1 := by linarith
  have hint : IntegrableOn (fun w : ℝ => ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1))
      (Set.Ioi 1) := by
    refine integrableOn_fract_mul_cpow ?_
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact hreal
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Set.Ioi_subset_Ioi hc1))
  rw [fracMellin, hexp, ← hsplit]
  have hH := norm_intervalIntegral_one_fract_mul_cpow_le K' hre himne
  have hT : ‖∫ w in Set.Ioi ((K' : ℝ) + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)‖
      ≤ 1 / (2 * ((K' : ℝ) + 1)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hT' := integral_Ioi_fract_mul_rpow_neg_two_le (N := K' + 1) (by omega)
    push_cast at hT'
    refine le_trans ?_ hT'
    have h1 : IntegrableOn (fun w : ℝ => Int.fract w * w ^ (-a.re - 1))
        (Set.Ioi ((K' : ℝ) + 1)) := by
      simpa only [pow_one] using integrableOn_fract_pow_mul_rpow 1 hreal hc0
    have h2 : IntegrableOn (fun w : ℝ => Int.fract w * w ^ (-2 : ℝ)) (Set.Ioi ((K' : ℝ) + 1)) := by
      simpa only [pow_one] using integrableOn_fract_pow_mul_rpow 1 (by norm_num) hc0
    rw [setIntegral_congr_fun measurableSet_Ioi fun w hw => norm_fract_mul_cpow (lt_trans hc0 hw) _]
    refine setIntegral_mono_on ?_ h2 measurableSet_Ioi fun w hw => ?_
    · refine h1.congr_fun (fun w _ => ?_) measurableSet_Ioi
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    · have hw1 : 1 ≤ w := le_trans hc1 (le_of_lt hw)
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith))
        (Int.fract_nonneg w)
  have hnorm : ‖a‖ = ‖2 * s‖ := by rw [hadef]
  have habs : |a.im| = 2 * |s.im| := by rw [him, abs_mul, abs_two]
  have hs0 : 0 < |s.im| := abs_pos.2 ht
  have hna : 0 < ‖a‖ := norm_pos_iff.2 (fun h => himne (by rw [h, Complex.zero_im]))
  rw [norm_mul, Complex.norm_two]
  calc 2 * ‖(∫ w in (1 : ℝ)..((K' : ℝ) + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1))
        + ∫ w in Set.Ioi ((K' : ℝ) + 1), ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1)‖
      ≤ 2 * ((2 / |a.im| + ((harmonic (K' + 1) : ℝ) - 1)) / ‖a‖
          + 1 / (2 * ((K' : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (le_trans (norm_add_le _ _) (add_le_add hH hT)) (by norm_num)
    _ = 2 / ‖2 * s‖ * (1 / |s.im| + ((harmonic (K' + 1) : ℝ) - 1)) + 1 / ((K' + 1 : ℕ) : ℝ) := by
        rw [habs, ← hnorm]
        push_cast
        field_simp

/-- **A simple decay bound**, the cap at `K = ⌈|t|⌉`: for `Re s ≥ ½` and `t = Im s ≠ 0`,
`|φ̂(s)| ≤ (1 + 1/|t| + log(1 + |t|))/|t|`. -/
theorem norm_fracMellin_le_decay {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : s.im ≠ 0) :
    ‖fracMellin s‖ ≤ (1 + 1 / |s.im| + Real.log (1 + |s.im|)) / |s.im| := by
  set τ : ℝ := |s.im| with hτdef
  have hτ : 0 < τ := abs_pos.2 ht
  have hK : 1 ≤ ⌈τ⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hτ).ne'
  have hcap := norm_fracMellin_le_cap hs ht hK
  have hKτ : τ ≤ (⌈τ⌉₊ : ℝ) := Nat.le_ceil τ
  have hKτ' : (⌈τ⌉₊ : ℝ) < τ + 1 := Nat.ceil_lt_add_one hτ.le
  have hK0 : (0 : ℝ) < (⌈τ⌉₊ : ℝ) := lt_of_lt_of_le hτ hKτ
  have hH : (harmonic ⌈τ⌉₊ : ℝ) - 1 ≤ Real.log (1 + τ) := by
    have h1 := harmonic_le_one_add_log ⌈τ⌉₊
    have h2 : Real.log (⌈τ⌉₊ : ℝ) ≤ Real.log (1 + τ) := Real.log_le_log hK0 (by linarith)
    linarith
  have hH0 : 0 ≤ (harmonic ⌈τ⌉₊ : ℝ) - 1 := by
    obtain ⟨K', hK'⟩ : ∃ K', ⌈τ⌉₊ = K' + 1 := ⟨⌈τ⌉₊ - 1, by omega⟩
    rw [hK', ← sum_range_one_div_add_two]
    exact Finset.sum_nonneg fun n _ => by positivity
  have h2s : 2 / ‖2 * s‖ ≤ 1 / τ := by
    have hle : 2 * τ ≤ ‖2 * s‖ := by
      have h := Complex.abs_im_le_norm (2 * s)
      have him2 : (2 * s).im = 2 * s.im := by simp [Complex.mul_im]
      rwa [him2, abs_mul, abs_two] at h
    rw [div_le_div_iff₀ (by linarith) hτ]
    linarith
  have h1K : 1 / (⌈τ⌉₊ : ℝ) ≤ 1 / τ := one_div_le_one_div_of_le hτ hKτ
  calc ‖fracMellin s‖
      ≤ 2 / ‖2 * s‖ * (1 / τ + ((harmonic ⌈τ⌉₊ : ℝ) - 1)) + 1 / (⌈τ⌉₊ : ℝ) := hcap
    _ ≤ 1 / τ * (1 / τ + Real.log (1 + τ)) + 1 / τ := by
        gcongr
    _ = (1 + 1 / τ + Real.log (1 + τ)) / τ := by
        field_simp
        ring

/-! ### The closed form

`φ̂(s) = 1/(s - ½) - ζ(2s)/s` on `Re s > ½`: the head formula as `K → ∞`, where
`(K+1)^{1-2s} → 0` and `∑_{n<K}(n+2)^{-2s} → ζ(2s) - 1`. -/

/-- **The closed form** `φ̂(s) = 1/(s - ½) - ζ(2s)/s` for `Re s > ½`. -/
theorem fracMellin_eq_zeta {s : ℂ} (hs : 1 / 2 < s.re) :
    fracMellin s = 1 / (s - 1 / 2) - riemannZeta (2 * s) / s := by
  have hre2 : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  set a : ℂ := 2 * s with hadef
  have ha : 1 < a.re := by rw [hre2]; linarith
  have ha0 : a ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha; linarith
  have ha1 : a ≠ 1 := fun h => by rw [h, Complex.one_re] at ha; linarith
  have hexp : -2 * s - 1 = -a - 1 := by rw [hadef]; ring
  have hint : IntegrableOn (fun w : ℝ => ((Int.fract w : ℝ) : ℂ) * (w : ℂ) ^ (-a - 1))
      (Set.Ioi 1) := by
    refine integrableOn_fract_mul_cpow ?_
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 1 hint
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  simp_rw [intervalIntegral_one_fract_mul_cpow_eq _ ha0 ha1] at hlim1
  have hpow : Filter.Tendsto (fun K : ℕ => ((K : ℂ) + 1) ^ (1 - a)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hc : ∀ K : ℕ, ‖((K : ℂ) + 1) ^ (1 - a)‖ = ((K : ℝ) + 1) ^ (-(a.re - 1)) := by
      intro K
      have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      rw [show ((K : ℂ) + 1) = (((K : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hK]
      congr 1
      simp
    simp_rw [hc]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hzeta : Filter.Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, ((n : ℂ) + 2) ^ (-a))
      Filter.atTop (nhds (riemannZeta a - 1)) := by
    have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ a) := by
      have h := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 ha)
      simpa using h
    have hs1 : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ a) (riemannZeta a) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow ha]
      exact hsum.hasSum
    have hs2 := (hasSum_nat_add_iff' 1).2 hs1
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, Complex.one_cpow,
      div_one, Nat.cast_add, Nat.cast_one] at hs2
    refine hs2.tendsto_sum_nat.congr fun K => Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg, ← one_div]
    ring_nf
  have hlim2 : Filter.Tendsto (fun K : ℕ => (((K : ℂ) + 1) ^ (1 - a) - 1) / (a * (1 - a))
        - (∑ n ∈ Finset.range K, ((n : ℂ) + 2) ^ (-a)) / a) Filter.atTop
      (nhds ((0 - 1) / (a * (1 - a)) - (riemannZeta a - 1) / a)) :=
    ((hpow.sub_const 1).div_const _).sub (hzeta.div_const _)
  have hI := tendsto_nhds_unique hlim1 hlim2
  rw [fracMellin, hexp, hI, hadef]
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hs12 : s - 1 / 2 ≠ 0 := fun h => by
    have h' : (s - 1 / 2).re = 0 := by rw [h, Complex.zero_re]
    simp at h'
    linarith
  have h12 : 1 - 2 * s ≠ 0 := fun h => by
    have h' : (1 - 2 * s).re = 0 := by rw [h, Complex.zero_re]
    simp at h'
    linarith
  have h21 : 2 * s - 1 ≠ 0 := by
    intro h
    exact h12 (by linear_combination -h)
  rw [show (1 : ℂ) / (s - 1 / 2) = 2 / (2 * s - 1) by
    rw [div_eq_div_iff hs12 h21]
    ring]
  field_simp
  ring

/-! ### The kernel Mellin–Plancherel identity

For finitely many `aₖ`, `k ≥ 1`, and `σ > -½`, `F(u) = ∑ₖ aₖψ(u/k)` vanishes on `(0, 1]` and is at
most `(∑‖aₖ‖√k)u^{-1/2}` (`RMF.fracKernel_div_le`), so `g(v) = F(eᵛ)e^{-σv}` lies in `L¹ ∩ L²`.
Its Fourier transform is the Mellin transform of `F` on `Re s = σ`, `∑ₖ aₖk^{-s}φ̂(½ + s)`
(`RMF.integral_fracKernel_div_mul_cpow`), and `RMF.integral_normSq_fourier` closes it, as for
`RMF.integral_normSq_partialSum_eq_line`. -/

/-- `∫₀^∞ ψ(u/k) u^{-s-1} du` converges absolutely for `k > 0`, `Re s > -½`. -/
lemma integrableOn_fracKernel_div_mul_cpow {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : -1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => (fracKernel (u / k) : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi 0) := by
  refine integrableOn_Ioi_zero_of_le_rpow hk ?_ (fun u hu => ?_) (C := Real.sqrt k)
    (r := -s.re - 3 / 2) (by linarith) (fun u hu => ?_)
  · exact ((Complex.measurable_ofReal.comp (measurable_fracKernel.comp
      (measurable_id.div_const k))).mul (by fun_prop)).aestronglyMeasurable
  · have hle : u / k ≤ 1 := (div_le_one hk).2 hu.2
    rw [fracKernel_eq_zero_of_le_one hle, Complex.ofReal_zero, zero_mul]
  · have hu0 : 0 < u := lt_trans hk hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fracKernel_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc fracKernel (u / k) * u ^ (-s.re - 1)
        ≤ Real.sqrt k * u ^ (-(1 / 2 : ℝ)) * u ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (fracKernel_div_le hu0 hk) (Real.rpow_nonneg hu0.le _)
      _ = Real.sqrt k * u ^ (-s.re - 3 / 2) := by
          rw [mul_assoc, ← Real.rpow_add hu0]
          ring_nf

variable (S : Finset ℕ) (a : ℕ → ℂ)

/-- `F(u) = ∑_{k∈S} aₖψ(u/k)` vanishes for `u ≤ 1`. -/
lemma sum_fracKernel_eq_zero (hS : ∀ k ∈ S, 0 < k) {u : ℝ} (hu : u ≤ 1) :
    ∑ k ∈ S, a k * (fracKernel (u / k) : ℂ) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hS k hk
  have hle : u / k ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  rw [fracKernel_eq_zero_of_le_one hle, Complex.ofReal_zero, mul_zero]

/-- `|F(u)| ≤ (∑‖aₖ‖√k)·u^{-1/2}`. -/
lemma norm_sum_fracKernel_le (hS : ∀ k ∈ S, 0 < k) {u : ℝ} (hu : 0 < u) :
    ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖
      ≤ (∑ k ∈ S, ‖a k‖ * Real.sqrt k) * u ^ (-(1 / 2 : ℝ)) := by
  rw [Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hS k hk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fracKernel_nonneg _),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (fracKernel_div_le hu hk0) (norm_nonneg _)

lemma measurable_sum_fracKernel :
    Measurable fun u : ℝ => ∑ k ∈ S, a k * (fracKernel (u / k) : ℂ) :=
  Finset.measurable_sum _ fun _ _ => measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_fracKernel.comp (measurable_id.div_const _)))

/-- **`L¹`**: `∫₀^∞ |F(u)| u^{-1-σ} du < ∞` for `σ > -½`. -/
lemma integrableOn_norm_sum_fracKernel (hS : ∀ k ∈ S, 0 < k) {σ : ℝ} (hσ : -1 / 2 < σ) :
    IntegrableOn (fun u : ℝ => ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ / u ^ (1 + σ))
      (Set.Ioi 0) := by
  refine integrableOn_Ioi_zero_of_le_rpow one_pos ?_ (fun u hu => ?_)
    (C := ∑ k ∈ S, ‖a k‖ * Real.sqrt k) (r := -σ - 3 / 2) (by linarith) (fun u hu => ?_)
  · exact ((measurable_sum_fracKernel S a).norm.div (by fun_prop)).aestronglyMeasurable
  · rw [sum_fracKernel_eq_zero S a hS hu.2, norm_zero, zero_div]
  · have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hden : 0 < u ^ (1 + σ) := Real.rpow_pos_of_pos hu0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hden.le)]
    calc ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ / u ^ (1 + σ)
        ≤ (∑ k ∈ S, ‖a k‖ * Real.sqrt k) * u ^ (-(1 / 2 : ℝ)) / u ^ (1 + σ) :=
          div_le_div_of_nonneg_right (norm_sum_fracKernel_le S a hS hu0) hden.le
      _ = (∑ k ∈ S, ‖a k‖ * Real.sqrt k) * u ^ (-σ - 3 / 2) := by
          rw [mul_div_assoc, ← Real.rpow_sub hu0]
          ring_nf

/-- **`L²`**: `∫₀^∞ |F(u)|² u^{-1-2σ} du < ∞` for `σ > -½`. -/
lemma integrableOn_normSq_sum_fracKernel (hS : ∀ k ∈ S, 0 < k) {σ : ℝ} (hσ : -1 / 2 < σ) :
    IntegrableOn (fun u : ℝ => ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ ^ 2 / u ^ (1 + 2 * σ))
      (Set.Ioi 0) := by
  refine integrableOn_Ioi_zero_of_le_rpow one_pos ?_ (fun u hu => ?_)
    (C := (∑ k ∈ S, ‖a k‖ * Real.sqrt k) ^ 2) (r := -2 - 2 * σ) (by linarith) (fun u hu => ?_)
  · exact (((measurable_sum_fracKernel S a).norm.pow_const 2).div
      (by fun_prop)).aestronglyMeasurable
  · rw [sum_fracKernel_eq_zero S a hS hu.2, norm_zero]
    simp
  · have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hden : 0 < u ^ (1 + 2 * σ) := Real.rpow_pos_of_pos hu0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
    have hb := norm_sum_fracKernel_le S a hS hu0
    calc ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ ^ 2 / u ^ (1 + 2 * σ)
        ≤ ((∑ k ∈ S, ‖a k‖ * Real.sqrt k) * u ^ (-(1 / 2 : ℝ))) ^ 2 / u ^ (1 + 2 * σ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb 2) hden.le
      _ = (∑ k ∈ S, ‖a k‖ * Real.sqrt k) ^ 2 * u ^ (-2 - 2 * σ) := by
          have hpow : (u ^ (-(1 / 2 : ℝ))) ^ 2 / u ^ (1 + 2 * σ) = u ^ (-2 - 2 * σ) := by
            rw [← Real.rpow_natCast (u ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hu0.le,
              ← Real.rpow_sub hu0]
            congr 1
            push_cast
            ring
          rw [mul_pow, mul_div_assoc, hpow]

variable (σ : ℝ)

/-- `g(v) = F(eᵛ)e^{-σv}`, `F(u) = ∑_{k∈S} aₖψ(u/k)`: the function whose Fourier transform is
the Mellin transform of `F` on `Re s = σ`. -/
noncomputable def logFracKernelSum (v : ℝ) : ℂ :=
  (∑ k ∈ S, a k * (fracKernel (Real.exp v / k) : ℂ)) * (Real.exp (-σ * v) : ℂ)

lemma norm_logFracKernelSum (v : ℝ) :
    ‖logFracKernelSum S a σ v‖
      = Real.exp (-σ * v) * ‖∑ k ∈ S, a k * (fracKernel (Real.exp v / k) : ℂ)‖ := by
  rw [logFracKernelSum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

lemma measurable_logFracKernelSum : Measurable (logFracKernelSum S a σ) :=
  ((measurable_sum_fracKernel S a).comp Real.measurable_exp).mul (by fun_prop)

lemma exp_mul_norm_eq_logFracKernelSum (v : ℝ) :
    Real.exp v * (‖∑ k ∈ S, a k * (fracKernel (Real.exp v / k) : ℂ)‖ / Real.exp v ^ (1 + σ))
      = ‖logFracKernelSum S a σ v‖ := by
  rw [norm_logFracKernelSum, exp_rpow]
  have h : Real.exp v / Real.exp (v * (1 + σ)) = Real.exp (-σ * v) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [← h]
  ring

lemma exp_mul_normSq_eq_logFracKernelSum (v : ℝ) :
    Real.exp v
        * (‖∑ k ∈ S, a k * (fracKernel (Real.exp v / k) : ℂ)‖ ^ 2 / Real.exp v ^ (1 + 2 * σ))
      = ‖logFracKernelSum S a σ v‖ ^ 2 := by
  rw [norm_logFracKernelSum, exp_rpow]
  have h : Real.exp v / Real.exp (v * (1 + 2 * σ)) = Real.exp (-σ * v) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [mul_pow, ← h]
  ring

lemma integral_normSq_logFracKernelSum :
    ∫ v : ℝ, ‖logFracKernelSum S a σ v‖ ^ 2
      = ∫ u in Set.Ioi (0 : ℝ),
          ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ ^ 2 / u ^ (1 + 2 * σ) := by
  rw [integral_Ioi_eq_integral_exp]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun v => (exp_mul_normSq_eq_logFracKernelSum S a σ v).symm)

lemma integrable_logFracKernelSum (hS : ∀ k ∈ S, 0 < k) {σ : ℝ} (hσ : -1 / 2 < σ) :
    Integrable (logFracKernelSum S a σ) :=
  (integrable_norm_iff (measurable_logFracKernelSum S a σ).aestronglyMeasurable).1
    (((integrableOn_Ioi_iff_integrable_exp
      (fun u : ℝ => ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ / u ^ (1 + σ))).1
        (integrableOn_norm_sum_fracKernel S a hS hσ)).congr
      (Filter.Eventually.of_forall (exp_mul_norm_eq_logFracKernelSum S a σ)))

lemma memLp_two_logFracKernelSum (hS : ∀ k ∈ S, 0 < k) {σ : ℝ} (hσ : -1 / 2 < σ) :
    MemLp (logFracKernelSum S a σ) 2 :=
  (memLp_two_iff_integrable_sq_norm
    (measurable_logFracKernelSum S a σ).aestronglyMeasurable).2
    (((integrableOn_Ioi_iff_integrable_exp
      (fun u : ℝ => ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ ^ 2 / u ^ (1 + 2 * σ))).1
        (integrableOn_normSq_sum_fracKernel S a hS hσ)).congr
      (Filter.Eventually.of_forall (exp_mul_normSq_eq_logFracKernelSum S a σ)))

/-- **The Mellin transform of `F`**: `∫₀^∞ F(u)u^{-s-1}du = (∑ₖ aₖk^{-s})·φ̂(½ + s)` on
`Re s > -½`. -/
theorem integral_sum_fracKernel_mul_cpow (hS : ∀ k ∈ S, 0 < k) {s : ℂ} (hs : -1 / 2 < s.re) :
    ∫ u in Set.Ioi (0 : ℝ), (∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)) * (u : ℂ) ^ (-s - 1)
      = (∑ k ∈ S, a k / (k : ℂ) ^ s) * fracMellin (1 / 2 + s) := by
  have hint : ∀ k ∈ S, IntegrableOn
      (fun u : ℝ => a k * ((fracKernel (u / k) : ℂ) * (u : ℂ) ^ (-s - 1))) (Set.Ioi 0) :=
    fun k hk => (integrableOn_fracKernel_div_mul_cpow (by exact_mod_cast hS k hk) hs).const_mul _
  have hpt : ∀ u : ℝ, (∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)) * (u : ℂ) ^ (-s - 1)
      = ∑ k ∈ S, a k * ((fracKernel (u / k) : ℂ) * (u : ℂ) ^ (-s - 1)) := fun u => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ hint, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hS k hk
  rw [integral_const_mul, integral_fracKernel_div_mul_cpow hk0, Complex.cpow_neg,
    add_comm s (1 / 2)]
  push_cast
  ring

/-- **The Fourier transform of `g`**: `𝓕g(ξ) = (∑ₖ aₖk^{-s})·φ̂(½ + s)`, `s = σ + 2πiξ`. -/
theorem fourier_logFracKernelSum (hS : ∀ k ∈ S, 0 < k) {σ : ℝ} (hσ : -1 / 2 < σ) (ξ : ℝ) :
    𝓕 (logFracKernelSum S a σ) ξ
      = (∑ k ∈ S, a k / (k : ℂ) ^ ((σ : ℂ) + 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I))
        * fracMellin (1 / 2 + ((σ : ℂ) + 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I)) := by
  set s : ℂ := (σ : ℂ) + 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I with hsdef
  have hs : -1 / 2 < s.re := by simp [hsdef, hσ]
  rw [← integral_sum_fracKernel_mul_cpow S a hS hs, integral_Ioi_eq_integral_exp_smul,
    Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hpos : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hne : ((Real.exp v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have hlog : Complex.log ((Real.exp v : ℝ) : ℂ) = (v : ℂ) := by
    rw [← Complex.ofReal_log hpos.le, Real.log_exp]
  simp only [logFracKernelSum]
  have hinner : (inner ℝ v ξ : ℝ) = v * ξ := Real.inner_apply v ξ
  rw [Complex.cpow_def_of_ne_zero hne, hlog, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_exp, Complex.ofReal_exp, hinner]
  simp only [show ∀ z w x : ℂ, Complex.exp z * (w * Complex.exp x) = w * Complex.exp (z + x)
    from fun z w x => by rw [Complex.exp_add]; ring]
  congr 1
  simp only [hsdef]
  push_cast
  ring_nf

/-- **The kernel Mellin–Plancherel identity.**  For a finite `S ⊆ ℕ_{≥1}`, coefficients `aₖ` and
`σ > -½`,

`∫₀^∞ |∑ₖ aₖψ(u/k)|² u^{-1-2σ} du = (2π)⁻¹ ∫_ℝ |∑ₖ aₖk^{-σ-it}|²·|φ̂(½ + σ + it)|² dt`,

`φ̂(½ + s) = ψ̂(s)` the kernel's Mellin transform.  With `aₖ = X(k)k^{-1/2}` on the `y`-smooth
squarefree `k`, the sum is `F_y(½ + σ + it)`: `RMF.integral_normSq_smoothWeightedSum_eq_line` with
`1/(σ + it)` replaced by `ψ̂(σ + it)`. -/
theorem integral_normSq_sum_fracKernel_eq_line (hS : ∀ k ∈ S, 0 < k) {σ : ℝ}
    (hσ : -1 / 2 < σ) :
    ∫ u in Set.Ioi (0 : ℝ), ‖∑ k ∈ S, a k * (fracKernel (u / k) : ℂ)‖ ^ 2 / u ^ (1 + 2 * σ)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖∑ k ∈ S, a k / (k : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hkey : ∀ t : ℝ,
      ‖∑ k ∈ S, a k / (k : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
        = ‖𝓕 (logFracKernelSum S a σ) ((2 * Real.pi)⁻¹ * t)‖ ^ 2 := by
    intro t
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have harg : ((σ : ℂ) + 2 * (Real.pi : ℂ) * ((((2 * Real.pi)⁻¹ * t : ℝ)) : ℂ) * Complex.I)
        = (σ : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [fourier_logFracKernelSum S a hS hσ, harg, norm_mul, mul_pow, ← add_assoc]
  rw [← integral_normSq_logFracKernelSum S a σ,
    ← integral_normSq_fourier (integrable_logFracKernelSum S a hS hσ)
      (memLp_two_logFracKernelSum S a hS hσ)]
  simp_rw [hkey]
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun ξ => ‖𝓕 (logFracKernelSum S a σ) ξ‖ ^ 2) (2 * Real.pi)⁻¹, inv_inv,
    abs_of_pos hpi, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

/-- **The right-hand side is integrable**: `𝓕g ∈ L²`. -/
theorem integrable_normSq_sum_mul_fracMellin (hS : ∀ k ∈ S, 0 < k) {σ : ℝ}
    (hσ : -1 / 2 < σ) :
    Integrable fun t : ℝ => ‖∑ k ∈ S, a k / (k : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
  have h1 := integrable_logFracKernelSum S a hS hσ
  have h2 := memLp_two_logFracKernelSum S a hS hσ
  have hF : MemLp (𝓕 (logFracKernelSum S a σ)) 2 :=
    (Lp.memLp (𝓕 (h2.toLp) : Lp ℂ 2 volume)).ae_eq (coeFn_fourier_toLp h1 h2)
  have hsq := (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  have hpi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  refine (hsq.comp_mul_left' hpi).congr (Filter.Eventually.of_forall fun t => ?_)
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have harg : ((σ : ℂ) + 2 * (Real.pi : ℂ) * ((((2 * Real.pi)⁻¹ * t : ℝ)) : ℂ) * Complex.I)
      = (σ : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    field_simp
  simp only
  rw [fourier_logFracKernelSum S a hS hσ, harg, norm_mul, mul_pow, ← add_assoc]

/-! ### The total `∫|φ̂|²`

The identity at `S = {1}` reads `∫_ℝ|φ̂(½ + σ + it)|²dt = 2π∫₀^∞ψ(u)²u^{-1-2σ}du
= 4π∫₁^∞{w}²w^{-3-4σ}dw`, at most `4πc₃` for `σ ≥ 0`, with
`c₃ = ∫₁^∞{w}²w^{-3}dw = 3/2 - γ - π²/12` (unit pieces
`log(1 + 1/m) - 2/(m+1) + (2m+1)/(2(m+1)²)`, partial sums `log N - H_N + 3/2 - H_N^{(2)}/2`).
The integrand is even in `t`, so the half line carries `2πc₃ ≤ 0.6305`. -/

/-- The case `S = {1}`, `a = 1` of the kernel identity. -/
lemma integral_normSq_fracMellin_eq_two_pi_mul {σ : ℝ} (hσ : -1 / 2 < σ) :
    ∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      = 2 * Real.pi * ∫ u in Set.Ioi (0 : ℝ), fracKernel u ^ 2 / u ^ (1 + 2 * σ) := by
  have h := integral_normSq_sum_fracKernel_eq_line {1} (fun _ => 1) (by simp) hσ
  simp only [Finset.sum_singleton, Nat.cast_one, div_one, one_mul, Complex.one_cpow, norm_one,
    one_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- `∫₀^∞ ψ(u)²u^{-1-2σ}du = 2∫₁^∞{w}²w^{-3-4σ}dw`, by `u = w²`. -/
lemma integral_fracKernel_sq_eq (σ : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), fracKernel u ^ 2 / u ^ (1 + 2 * σ)
      = 2 * ∫ w in Set.Ioi (1 : ℝ), Int.fract w ^ 2 * w ^ (-3 - 4 * σ) := by
  have h2 : ∀ w ∈ Set.Ioi (0 : ℝ) \ Set.Ioi 1,
      (2 * w) • (fracKernel (w ^ (2 : ℝ)) ^ 2 / (w ^ (2 : ℝ)) ^ (1 + 2 * σ)) = 0 := by
    intro w hw
    have hle : w ^ (2 : ℝ) ≤ 1 := Real.rpow_le_one hw.1.le (not_lt.1 hw.2) (by norm_num)
    rw [fracKernel_eq_zero_of_le_one hle]
    simp
  rw [integral_Ioi_eq_integral_sq, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi (Set.Ioi_subset_Ioi zero_le_one) h2, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw0 : (0 : ℝ) < w := lt_trans one_pos hw
  have hw2 : w ^ (2 : ℝ) = w ^ 2 := Real.rpow_two w
  have h1 : (1 : ℝ) ≤ w ^ (2 : ℝ) := by
    rw [hw2]
    nlinarith [le_of_lt (Set.mem_Ioi.1 hw)]
  have hsq : Real.sqrt (w ^ (2 : ℝ)) = w := by rw [hw2, Real.sqrt_sq hw0.le]
  have hpow : (w ^ (2 : ℝ)) ^ (1 + 2 * σ) = w * w ^ (1 + 4 * σ) := by
    rw [← Real.rpow_mul hw0.le, show 2 * (1 + 2 * σ) = 1 + (1 + 4 * σ) by ring,
      Real.rpow_add hw0, Real.rpow_one]
  have hneg : w ^ (-3 - 4 * σ) = (w * w * w ^ (1 + 4 * σ))⁻¹ := by
    rw [show (-3 - 4 * σ) = -(1 + (1 + (1 + 4 * σ))) by ring, Real.rpow_neg hw0.le,
      Real.rpow_add hw0, Real.rpow_add hw0, Real.rpow_one, mul_assoc]
  have hpos : 0 < w ^ (1 + 4 * σ) := Real.rpow_pos_of_pos hw0 _
  rw [fracKernel, if_pos h1, hsq, hpow, hneg, smul_eq_mul]
  field_simp

/-- **The exact total**: `∫_ℝ|φ̂(½ + σ + it)|²dt = 4π∫₁^∞{w}²w^{-3-4σ}dw` for `σ > -½`. -/
theorem integral_normSq_fracMellin_eq {σ : ℝ} (hσ : -1 / 2 < σ) :
    ∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      = 4 * Real.pi * ∫ w in Set.Ioi (1 : ℝ), Int.fract w ^ 2 * w ^ (-3 - 4 * σ) := by
  rw [integral_normSq_fracMellin_eq_two_pi_mul hσ, integral_fracKernel_sq_eq]
  ring

/-- **`t ↦ |φ̂(½ + σ + it)|²` is integrable** for `σ > -½`. -/
theorem integrable_normSq_fracMellin {σ : ℝ} (hσ : -1 / 2 < σ) :
    Integrable fun t : ℝ => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
  have h := integrable_normSq_sum_mul_fracMellin {1} (fun _ => 1) (by simp) hσ
  simp only [Finset.sum_singleton, Nat.cast_one, div_one, Complex.one_cpow, norm_one, one_pow,
    one_mul] at h
  exact h

/-- One unit piece of `c₃`: `∫_m^{m+1}{w}²w^{-3}dw = log(1 + 1/m) - 2/(m+1) + (2m+1)/(2(m+1)²)`,
from the antiderivative `log w + 2m/w - m²/(2w²)` of `(w-m)²/w³`. -/
lemma intervalIntegral_fract_sq_mul_rpow_neg_three {m : ℕ} (hm : 1 ≤ m) :
    ∫ w in (m : ℝ)..(m + 1), Int.fract w ^ 2 * w ^ (-3 : ℝ)
      = Real.log ((m : ℝ) + 1) - Real.log m - 2 / ((m : ℝ) + 1)
        + (2 * m + 1) / (2 * ((m : ℝ) + 1) ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ m + 1 := by linarith
  have hcongr : ∫ w in (m : ℝ)..(m + 1), Int.fract w ^ 2 * w ^ (-3 : ℝ)
      = ∫ w in (m : ℝ)..(m + 1), (w - m) ^ 2 / w ^ 3 := by
    refine intervalIntegral_congr_Ioo hle fun w hw => ?_
    have hw0 : 0 < w := lt_trans hm0 hw.1
    rw [fract_eq_sub_natCast hw.1.le hw.2, Real.rpow_neg hw0.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  set F : ℝ → ℝ := fun w => Real.log w + 2 * m / w - (m : ℝ) ^ 2 / (2 * w ^ 2) with hF
  have hderiv : ∀ w ∈ Set.uIcc (m : ℝ) (m + 1), HasDerivAt F ((w - m) ^ 2 / w ^ 3) w := by
    intro w hw
    rw [Set.uIcc_of_le hle] at hw
    have hw0 : 0 < w := lt_of_lt_of_le hm0 hw.1
    have h1 := Real.hasDerivAt_log hw0.ne'
    have h2 : HasDerivAt (fun w : ℝ => 2 * (m : ℝ) / w) ((0 * w - 2 * m * 1) / w ^ 2) w :=
      (hasDerivAt_const w (2 * (m : ℝ))).div (hasDerivAt_id w) hw0.ne'
    have h3 : HasDerivAt (fun w : ℝ => (m : ℝ) ^ 2 / (2 * w ^ 2))
        ((0 * (2 * w ^ 2) - (m : ℝ) ^ 2 * (2 * ((2 : ℕ) * w ^ (2 - 1)))) / (2 * w ^ 2) ^ 2) w :=
      (hasDerivAt_const w ((m : ℝ) ^ 2)).div ((hasDerivAt_pow 2 w).const_mul 2) (by positivity)
    refine ((h1.add h2).sub h3).congr_deriv ?_
    norm_num
    field_simp
    ring
  have hcont : ContinuousOn (fun w : ℝ => (w - m) ^ 2 / w ^ 3) (Set.uIcc (m : ℝ) (m + 1)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => ?_
    rw [Set.uIcc_of_le hle] at hw
    have hw0 : 0 < w := lt_of_lt_of_le hm0 hw.1
    positivity
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hF]
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  field_simp
  ring

/-- Partial sums of the unit pieces of `c₃`. -/
lemma sum_range_cThree_piece (N : ℕ) :
    ∑ n ∈ Finset.range N, (Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1)
        - 2 / ((n : ℝ) + 1 + 1) + (2 * ((n : ℝ) + 1) + 1) / (2 * ((n : ℝ) + 1 + 1) ^ 2))
      = Real.log ((N : ℝ) + 1) - harmonic (N + 1) + 3 / 2
        - (∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) ^ 2) / 2 := by
  induction N with
  | zero => simp [harmonic_succ]; norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ (N + 1), Finset.sum_range_succ _ (N + 1)]
    push_cast
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    field_simp
    ring

/-- **`c₃ = ∫₁^∞{w}²w^{-3}dw = 3/2 - γ - π²/12`.** -/
theorem integral_fract_sq_mul_rpow_neg_three :
    ∫ w in Set.Ioi (1 : ℝ), Int.fract w ^ 2 * w ^ (-3 : ℝ)
      = 3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12 := by
  have hint : IntegrableOn (fun w : ℝ => Int.fract w ^ 2 * w ^ (-3 : ℝ)) (Set.Ioi 1) :=
    integrableOn_fract_pow_mul_rpow 2 (by norm_num) one_pos
  have h := (hasSum_intervalIntegral_of_integrableOn_Ioi hint).tendsto_sum_nat
  have hpiece : ∀ n : ℕ, ∫ w in ((1 : ℝ) + n)..((1 : ℝ) + n + 1), Int.fract w ^ 2 * w ^ (-3 : ℝ)
      = Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1)
        + (2 * ((n : ℝ) + 1) + 1) / (2 * ((n : ℝ) + 1 + 1) ^ 2) := by
    intro n
    have hp := intervalIntegral_fract_sq_mul_rpow_neg_three (m := n + 1) (by omega)
    push_cast at hp
    rw [show (1 : ℝ) + n = n + 1 by ring, hp]
  simp_rw [hpiece, sum_range_cThree_piece] at h
  -- the limit of the closed form
  have hH : Filter.Tendsto (fun N : ℕ => (harmonic (N + 1) : ℝ) - Real.log ((N : ℝ) + 1))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have := Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1)
    refine this.congr fun N => ?_
    simp
  have hZ : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) ^ 2)
      Filter.atTop (nhds (Real.pi ^ 2 / 6)) := by
    have hs := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add,
      Nat.cast_one] at hs
    exact hs.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim : Filter.Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - harmonic (N + 1) + 3 / 2
        - (∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) ^ 2) / 2) Filter.atTop
      (nhds (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12)) := by
    have := (hH.neg.const_add (3 / 2 : ℝ)).sub (hZ.div_const 2)
    convert this using 2
    · ring
    · ring
  exact tendsto_nhds_unique h hlim

/-- **`c₃ ≤ 0.10032`** (`c₃ = 0.100317…`), from `γ ≥ 0.577215` and `π > 3.141592`. -/
theorem cThree_le : 3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12 ≤ 0.10032 := by
  have hγ := hγ_lo
  have hπ := Real.pi_gt_d6
  have hπ2 : (3.141592 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by gcongr
  norm_num at hγ hπ2 ⊢
  linarith

/-- **The total**: for `σ ≥ 0`, `∫_ℝ|φ̂(½ + σ + it)|²dt ≤ 4πc₃`. -/
theorem integral_normSq_fracMellin_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      ≤ 4 * Real.pi * (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12) := by
  rw [integral_normSq_fracMellin_eq (by linarith), ← integral_fract_sq_mul_rpow_neg_three]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine setIntegral_mono_on (integrableOn_fract_pow_mul_rpow 2 (by linarith) one_pos)
    (integrableOn_fract_pow_mul_rpow 2 (by norm_num) one_pos) measurableSet_Ioi fun w hw => ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (le_of_lt hw) (by linarith)) (sq_nonneg _)

/-- **`∫_ℝ|φ̂(½ + σ + it)|²dt ≤ 1.261`** for `σ ≥ 0`. -/
theorem integral_normSq_fracMellin_le_numeral {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 1.261 := by
  refine le_trans (integral_normSq_fracMellin_le hσ) ?_
  have hc := cThree_le
  have hπ := Real.pi_lt_d6
  have hc0 : 0 ≤ 3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12 := by
    have hγ := hγ_hi
    have hπ2 : Real.pi ^ 2 ≤ (3.141593 : ℝ) ^ 2 := by gcongr
    norm_num at hγ hπ2 ⊢
    linarith
  calc 4 * Real.pi * (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12)
      ≤ 4 * 3.141593 * 0.10032 := by gcongr
    _ ≤ 1.261 := by norm_num

/-- **The half line carries half**: `∫_{t>0}|φ̂(½ + σ + it)|²dt = ½∫_ℝ`, the integrand being
even (`RMF.norm_fracMellin_neg`). -/
theorem integral_Ioi_normSq_fracMellin_eq (σ : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      = (∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) / 2 := by
  have h := integral_comp_abs (f := fun t : ℝ => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
  have heven : ∀ t : ℝ, ‖fracMellin (1 / 2 + σ + (|t| : ℝ) * Complex.I)‖ ^ 2
      = ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, norm_fracMellin_neg]
  simp only [heven] at h
  rw [h]
  ring

/-- **`∫_{t>0}|φ̂(½ + σ + it)|²dt ≤ 2πc₃ ≤ 0.6305`** for `σ ≥ 0`. -/
theorem integral_Ioi_normSq_fracMellin_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ t in Set.Ioi (0 : ℝ), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 0.6305 := by
  rw [integral_Ioi_normSq_fracMellin_eq]
  have h := integral_normSq_fracMellin_le hσ
  have hc := cThree_le
  have hπ := Real.pi_lt_d6
  have hc0 : 0 ≤ 3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12 := by
    have hγ := hγ_hi
    have hπ2 : Real.pi ^ 2 ≤ (3.141593 : ℝ) ^ 2 := by gcongr
    norm_num at hγ hπ2 ⊢
    linarith
  have hb : 4 * Real.pi * (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12)
      ≤ 4 * 3.141593 * 0.10032 := by gcongr
  have hnum : (4 * 3.141593 * 0.10032 : ℝ) / 2 ≤ 0.6305 := by norm_num
  linarith

/-- **Window masses**: any window `A ⊆ (0, ∞)` carries at most `0.6305`. -/
theorem setIntegral_normSq_fracMellin_le {σ : ℝ} (hσ : 0 ≤ σ) {A : Set ℝ}
    (hA0 : A ⊆ Set.Ioi 0) :
    ∫ t in A, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 0.6305 := by
  refine le_trans (setIntegral_mono_set (integrable_normSq_fracMellin (by linarith)).integrableOn
    (Filter.Eventually.of_forall fun t => sq_nonneg _) hA0.eventuallyLE) ?_
  exact integral_Ioi_normSq_fracMellin_le hσ

/-- **Window masses from the sup bound**: `∫_a^b|φ̂(½ + σ + it)|²dt ≤ 0.7151(b - a)`. -/
theorem setIntegral_Icc_normSq_fracMellin_le {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Icc a b, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 0.7151 * (b - a) := by
  have hre : ∀ t : ℝ, 1 / 2 ≤ (1 / 2 + σ + t * Complex.I : ℂ).re := fun t => by simp; linarith
  calc ∫ t in Set.Icc a b, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
      ≤ ∫ _t in Set.Icc a b, (0.7151 : ℝ) :=
        setIntegral_mono_on (integrable_normSq_fracMellin (by linarith)).integrableOn
          (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc
          fun t _ => normSq_fracMellin_le_numeral (hre t)
    _ = 0.7151 * (b - a) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, mul_comm]

end RMF
