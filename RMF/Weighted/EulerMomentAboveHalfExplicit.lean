/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.EulerMomentBand
import RMF.Weighted.BlockFamilyExplicit

/-!
# The Euler product moment above `q = ½`, sharp

For `½ ≤ q ≤ 1` and `σ ≥ 0`,

* `E‖F_{y+1}(½+σ)‖^{2q} ≤ (log y)^{q(2q-1)}·exp(q(2q-1)(0.2641 + 9.0028/log y + (2-2q)/3))`
  (`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_above_half`);
* `E‖F_{y,z}(½+σ)‖^{2q} ≤ κ^{q(2q-1)}·exp(q(2q-1)(9.0028/log y + 9.0028/log z + (2-2q)/(3y)))`
  for a band (`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_shift_rpow_le_above_half`).

**Every constant carries the factor `q(2q-1)`**, so both bounds tend to the exact value `1` of
`E|F(½)|` as `q ↓ ½`.  The chord (`RMF.rademacher_local_chord`) does not: its exponent is `2q-1`,
off by `(2q-1)(1-q)` per prime; nor does the fine bound (`RMF.rademacher_local_fine`), whose
absolute `10t⁴` costs `e^{1/3}` over the primes past `31`.  Here the local moment is bounded to
fourth order with the factor kept (`RMF.rademacher_local_above_half`): its `t`-derivative
`q((1+t)^{2q-1} - (1-t)^{2q-1})` is at most `q(2q-1)(2t + (4/3)(2-2q)t³)` on `t² ≤ ½`, by the
fundamental theorem of calculus twice and weighted AM–GM on `u^{2q-2}`
(`RMF.rpow_one_add_sub_rpow_one_sub_le`).
-/

open MeasureTheory

namespace RMF

/-! ### The local moment above `½` -/

/-- `2/(1 - v²) ≤ 2 + 4v²` for `v² ≤ ½`. -/
lemma two_div_one_sub_sq_le {v : ℝ} (hv : v ^ 2 ≤ 1 / 2) : 2 / (1 - v ^ 2) ≤ 2 + 4 * v ^ 2 := by
  have h1 : 0 < 1 - v ^ 2 := by linarith
  rw [div_le_iff₀ h1]
  nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg v) (by linarith : (0 : ℝ) ≤ 1 / 2 - v ^ 2)]

/-- `u^{λ-1} ≤ (1-λ)/u + λ` for `u > 0` and `0 ≤ λ ≤ 1`: weighted AM–GM on `u⁻¹` and `1`. -/
lemma rpow_sub_one_le_inv {u l : ℝ} (hu : 0 < u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    u ^ (l - 1) ≤ (1 - l) * u⁻¹ + l := by
  have h := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - l) hl0
    (inv_nonneg.2 hu.le) zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le,
    show -(1 - l) = l - 1 by ring] at h
  exact h

/-- **The odd part of `u ↦ u^λ` at `1`**: `(1+s)^λ - (1-s)^λ ≤ λ(2s + (4/3)(1-λ)s³)` for
`0 ≤ λ ≤ 1`, `s ≥ 0` and `s² ≤ ½`.  Its derivative `λ((1+v)^{λ-1} + (1-v)^{λ-1})` is at most
`λ((1-λ)·2/(1-v²) + 2λ) ≤ λ(2 + 4(1-λ)v²)` (`RMF.rpow_sub_one_le_inv`). -/
theorem rpow_one_add_sub_rpow_one_sub_le {s l : ℝ} (hs0 : 0 ≤ s) (hs : s ^ 2 ≤ 1 / 2)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    (1 + s) ^ l - (1 - s) ^ l ≤ l * (2 * s + 4 / 3 * (1 - l) * s ^ 3) := by
  have hs1 : s < 1 := by nlinarith
  -- the derivative on `[0, s]`
  have hH : ∀ v ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun v => (1 + v) ^ l - (1 - v) ^ l)
      (1 * l * (1 + v) ^ (l - 1) - (-1) * l * (1 - v) ^ (l - 1)) v := by
    intro v hv
    rw [Set.uIcc_of_le hs0] at hv
    have h1 : (0 : ℝ) < 1 + v := by linarith [hv.1]
    have h2 : (0 : ℝ) < 1 - v := by linarith [hv.2]
    have ha := ((hasDerivAt_id v).const_add 1).rpow_const (p := l) (Or.inl h1.ne')
    have hb := ((hasDerivAt_id v).const_sub 1).rpow_const (p := l) (Or.inl h2.ne')
    exact ha.sub hb
  have hcont : ContinuousOn (fun v : ℝ => 1 * l * (1 + v) ^ (l - 1) - (-1) * l * (1 - v) ^ (l - 1))
      (Set.uIcc 0 s) := by
    intro v hv
    rw [Set.uIcc_of_le hs0] at hv
    have h1 : (0 : ℝ) < 1 + v := by linarith [hv.1]
    have h2 : (0 : ℝ) < 1 - v := by linarith [hv.2]
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (fun v : ℝ => (1 + v) ^ (l - 1)) v :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl h1.ne')
    have c2 : ContinuousAt (fun v : ℝ => (1 - v) ^ (l - 1)) v :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl h2.ne')
    exact (continuousAt_const.mul c1).sub (continuousAt_const.mul c2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hH (hcont.intervalIntegrable)
  -- the bound's antiderivative
  have hB : ∀ v ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun v => l * (2 * v + 4 / 3 * (1 - l) * v ^ 3))
      (l * (2 + 4 * (1 - l) * v ^ 2)) v := by
    intro v _
    have h := (((hasDerivAt_id v).const_mul 2).add ((hasDerivAt_pow 3 v).const_mul
      (4 / 3 * (1 - l)))).const_mul l
    refine h.congr_deriv ?_
    rw [show (3 : ℕ) - 1 = 2 from rfl]
    push_cast
    ring
  have hBcont : ContinuousOn (fun v : ℝ => l * (2 + 4 * (1 - l) * v ^ 2)) (Set.uIcc 0 s) :=
    (continuous_const.mul (continuous_const.add
      (continuous_const.mul (continuous_pow 2)))).continuousOn
  have hFTCB := intervalIntegral.integral_eq_sub_of_hasDerivAt hB (hBcont.intervalIntegrable)
  -- the pointwise comparison
  have hmono : (∫ v in (0 : ℝ)..s, 1 * l * (1 + v) ^ (l - 1) - (-1) * l * (1 - v) ^ (l - 1))
      ≤ ∫ v in (0 : ℝ)..s, l * (2 + 4 * (1 - l) * v ^ 2) := by
    refine intervalIntegral.integral_mono_on hs0 (hcont.intervalIntegrable)
      (hBcont.intervalIntegrable) fun v hv => ?_
    have hv2 : v ^ 2 ≤ 1 / 2 := le_trans (pow_le_pow_left₀ hv.1 hv.2 2) hs
    have h1 : (0 : ℝ) < 1 + v := by linarith [hv.1]
    have h2 : (0 : ℝ) < 1 - v := by linarith [hv.2]
    have e1 := rpow_sub_one_le_inv h1 hl0 hl1
    have e2 := rpow_sub_one_le_inv h2 hl0 hl1
    have hsum : (1 + v)⁻¹ + (1 - v)⁻¹ = 2 / (1 - v ^ 2) := by
      rw [inv_add_inv h1.ne' h2.ne']
      congr 1 <;> ring
    have hq := two_div_one_sub_sq_le hv2
    have hsum' : (1 + v) ^ (l - 1) + (1 - v) ^ (l - 1) ≤ 2 + 4 * (1 - l) * v ^ 2 := by
      have h3 : (1 + v) ^ (l - 1) + (1 - v) ^ (l - 1)
          ≤ (1 - l) * ((1 + v)⁻¹ + (1 - v)⁻¹) + 2 * l := by linarith
      rw [hsum] at h3
      have h4 : (1 - l) * (2 / (1 - v ^ 2)) ≤ (1 - l) * (2 + 4 * v ^ 2) :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      linarith
    have := mul_le_mul_of_nonneg_left hsum' hl0
    linarith
  have h0 : (1 + (0 : ℝ)) ^ l - (1 - 0) ^ l = 0 := by norm_num
  rw [hFTC, hFTCB, h0] at hmono
  simpa using hmono

/-- **The Rademacher local moment above `½`, to fourth order.**  For `t ≥ 0` with `t² ≤ ½` and
`½ ≤ q ≤ 1`, `½[(1+t)^{2q} + (1-t)^{2q}] ≤ 1 + q(2q-1)(t² + ((2-2q)/3)t⁴)`.

Both terms carry the factor `q(2q-1)`, which the chord (`RMF.rademacher_local_chord`, exponent
`2q-1`) and the fine bound (`RMF.rademacher_local_fine`, an absolute `10t⁴`) do not: the product
over all primes then costs `exp(q(2q-1)·O(1))`, which tends to `1` as `q ↓ ½`.  The derivative in
`t` is `q((1+t)^{2q-1} - (1-t)^{2q-1})`, bounded by `RMF.rpow_one_add_sub_rpow_one_sub_le`. -/
theorem rademacher_local_above_half {t q : ℝ} (ht0 : 0 ≤ t) (ht : t ^ 2 ≤ 1 / 2)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    ((1 + t) ^ (2 * q) + (1 - t) ^ (2 * q)) / 2
      ≤ 1 + q * (2 * q - 1) * (t ^ 2 + (2 - 2 * q) / 3 * t ^ 4) := by
  have ht1 : t < 1 := by nlinarith
  have hG : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
      (fun s => ((1 + s) ^ (2 * q) + (1 - s) ^ (2 * q)) / 2)
      ((1 * (2 * q) * (1 + s) ^ (2 * q - 1) + (-1) * (2 * q) * (1 - s) ^ (2 * q - 1)) / 2) s := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    have h1 : (0 : ℝ) < 1 + s := by linarith [hs.1]
    have h2 : (0 : ℝ) < 1 - s := by linarith [hs.2]
    have ha := ((hasDerivAt_id s).const_add 1).rpow_const (p := 2 * q) (Or.inl h1.ne')
    have hb := ((hasDerivAt_id s).const_sub 1).rpow_const (p := 2 * q) (Or.inl h2.ne')
    exact (ha.add hb).div_const 2
  have hGcont : ContinuousOn (fun s : ℝ =>
      (1 * (2 * q) * (1 + s) ^ (2 * q - 1) + (-1) * (2 * q) * (1 - s) ^ (2 * q - 1)) / 2)
      (Set.uIcc 0 t) := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    have h1 : (0 : ℝ) < 1 + s := by linarith [hs.1]
    have h2 : (0 : ℝ) < 1 - s := by linarith [hs.2]
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (fun s : ℝ => (1 + s) ^ (2 * q - 1)) s :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl h1.ne')
    have c2 : ContinuousAt (fun s : ℝ => (1 - s) ^ (2 * q - 1)) s :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl h2.ne')
    exact ((continuousAt_const.mul c1).add (continuousAt_const.mul c2)).div_const 2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hGcont.intervalIntegrable
  have hB : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
      (fun s => q * (2 * q - 1) * (s ^ 2 + (2 - 2 * q) / 3 * s ^ 4))
      (q * (2 * q - 1) * (2 * s + 4 / 3 * (1 - (2 * q - 1)) * s ^ 3)) s := by
    intro s _
    have h := ((hasDerivAt_pow 2 s).add ((hasDerivAt_pow 4 s).const_mul
      ((2 - 2 * q) / 3))).const_mul (q * (2 * q - 1))
    refine h.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, show (4 : ℕ) - 1 = 3 from rfl]
    push_cast
    ring
  have hBcont : ContinuousOn (fun s : ℝ =>
      q * (2 * q - 1) * (2 * s + 4 / 3 * (1 - (2 * q - 1)) * s ^ 3)) (Set.uIcc 0 t) :=
    (continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul (continuous_pow 3)))).continuousOn
  have hFTCB := intervalIntegral.integral_eq_sub_of_hasDerivAt hB hBcont.intervalIntegrable
  have hmono : (∫ s in (0 : ℝ)..t,
        (1 * (2 * q) * (1 + s) ^ (2 * q - 1) + (-1) * (2 * q) * (1 - s) ^ (2 * q - 1)) / 2)
      ≤ ∫ s in (0 : ℝ)..t, q * (2 * q - 1) * (2 * s + 4 / 3 * (1 - (2 * q - 1)) * s ^ 3) := by
    refine intervalIntegral.integral_mono_on ht0 hGcont.intervalIntegrable
      hBcont.intervalIntegrable fun s hs => ?_
    have hs2 : s ^ 2 ≤ 1 / 2 := le_trans (pow_le_pow_left₀ hs.1 hs.2 2) ht
    have h := rpow_one_add_sub_rpow_one_sub_le hs.1 hs2 (by linarith : (0 : ℝ) ≤ 2 * q - 1)
      (by linarith : 2 * q - 1 ≤ 1)
    have hq : (0 : ℝ) ≤ q := by linarith
    have := mul_le_mul_of_nonneg_left h hq
    have e : (1 * (2 * q) * (1 + s) ^ (2 * q - 1) + (-1) * (2 * q) * (1 - s) ^ (2 * q - 1)) / 2
        = q * ((1 + s) ^ (2 * q - 1) - (1 - s) ^ (2 * q - 1)) := by ring
    rw [e]
    linarith
  rw [hFTC, hFTCB] at hmono
  have h0 : ((1 + (0 : ℝ)) ^ (2 * q) + (1 - 0) ^ (2 * q)) / 2 = 1 := by norm_num
  rw [h0] at hmono
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    sub_zero] at hmono
  linarith

/-! ### At a prime, over a set of primes, and the moments -/

/-- **The local moment above `½` at a prime, at a shifted abscissa**:
`E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)(t² + ((2-2q)/3)t⁴))`, `t² = p^{-(1+2σ)}`, for `σ ≥ 0`
and `½ ≤ q ≤ 1` (`t² ≤ 1/p ≤ ½`, `RMF.rademacher_local_above_half`). -/
theorem integral_norm_one_add_prime_shift_le_above_half {p : ℕ} (hp : p.Prime) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ))
          + (2 - 2 * q) / 3 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsq : ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 2 = (p : ℝ) ^ (-(1 + 2 * σ)) :=
    rpow_neg_shift_sq p σ
  have hinv : (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ((p : ℝ))⁻¹ := rpow_neg_shift_le_inv hp.one_lt.le hσ
  have hhalf : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have ht2 : ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 2 ≤ 1 / 2 := by rw [hsq]; linarith
  have ht1 : (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ 1 := by nlinarith
  rw [cpow_neg_ofReal_eq p (1 / 2 + σ), integral_norm_one_add_mul_rpow_rademacherLaw_real ht0 ht1]
  refine le_trans (rademacher_local_above_half ht0 ht2 hq0 hq1) ?_
  rw [show ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 4 = (((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 2) ^ 2 by ring,
    hsq]
  have := Real.add_one_le_exp (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ))
    + (2 - 2 * q) / 3 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2))
  linarith

/-- **The local product above `½`, over any set of primes**:
`∏_{p∈S} E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)∑_{p∈S}(t_p² + ((2-2q)/3)t_p⁴))`. -/
theorem prod_integral_norm_one_add_prime_shift_le_above_half {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∏ p ∈ S, ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * ∑ p ∈ S, ((p : ℝ) ^ (-(1 + 2 * σ))
          + (2 - 2 * q) / 3 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod
    (fun p _ => integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _)
    fun p hp => integral_norm_one_add_prime_shift_le_above_half (hS p hp) hσ hq0 hq1

/-- `∑_{p∈S} (p^{-(1+2σ)})² ≤ ∑_{m ≤ n < N} 1/n²` for primes `S` in `[m, N)`, `σ ≥ 0`. -/
lemma sum_rpow_neg_shift_sq_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m N : ℕ}
    (hSmN : ∀ p ∈ S, m ≤ p ∧ p < N) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ p ∈ S, ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ ∑ n ∈ Finset.Ico m N, (1 : ℝ) / (n : ℝ) ^ 2 := by
  have hsub : S ⊆ Finset.Ico m N := fun p hp =>
    Finset.mem_Ico.2 ⟨(hSmN p hp).1, (hSmN p hp).2⟩
  refine le_trans (Finset.sum_le_sum fun p hp => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
  have h1 := rpow_neg_shift_le_inv (hS p hp).one_lt.le hσ
  have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg hp0.le _
  calc ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ (((p : ℝ))⁻¹) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (1 : ℝ) / (p : ℝ) ^ 2 := by rw [inv_pow, one_div]

/-- **The Euler product moment above `½`, sharp, for the full product at a right shift.**  For
`½ ≤ q ≤ 1`, `σ ≥ 0` and `y ≥ 2`:
`E‖F_{y+1}(½+σ)‖^{2q} ≤ (log y)^{q(2q-1)}·exp(q(2q-1)(0.2641 + 9.0028/log y + (2-2q)/3))`.  Every
constant carries `q(2q-1)`, so the bound tends to `1` as `q ↓ ½`
(`RMF.prod_integral_norm_one_add_prime_shift_le_above_half`, Mertens with `M ≤ 0.2641`, and
`∑_{n≥2} 1/n² ≤ 1`). -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_above_half
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    {y : ℕ} (hy : 2 ≤ y) :
    (∫ ω, ‖randomEulerProduct f (y + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.log y ^ (q * (2 * q - 1))
        * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3)) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  rw [hf.integral_norm_randomEulerProduct_rpow_of_pos (y + 1)
    (by rw [Complex.ofReal_re]; linarith) (2 * q)]
  have hprimes : ∀ p ∈ Nat.primesBelow (y + 1), p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow hp
  refine le_trans (prod_integral_norm_one_add_prime_shift_le_above_half hprimes hσ hq0 hq1) ?_
  have h1 : ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ Real.log (Real.log y) + 0.2641 + 9.0028 / Real.log y := by
    refine le_trans (Finset.sum_le_sum fun p hp =>
      rpow_neg_shift_le_inv (hprimes p hp).one_lt.le hσ) ?_
    linarith [sum_primesBelow_inv_le_log_log_add_mertens hy, mertens_const_le]
  have h2 : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ 1 := by
    refine le_trans (sum_rpow_neg_shift_sq_le hprimes (m := 2) (N := y + 1) (fun p hp =>
      ⟨(hprimes p hp).two_le, Nat.lt_of_lt_of_le (Nat.mem_primesBelow.1 hp).1 le_rfl⟩) hσ) ?_
    have h := sum_inv_sq_Ico_le (m := 2) le_rfl (y + 1)
    norm_num at h ⊢
    exact h
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hc0 : (0 : ℝ) ≤ (2 - 2 * q) / 3 := by linarith
  have hsum : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ) ^ (-(1 + 2 * σ))
      + (2 - 2 * q) / 3 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)
      ≤ Real.log (Real.log y) + (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left h2 hc0
    linarith
  have hrpow : Real.log y ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log y)) := by
    rw [Real.rpow_def_of_pos hL0]
    ring_nf
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left hsum hγ0
  linarith

/-- **The Euler product moment above `½`, sharp, for a band at a right shift.**  For
`½ ≤ q ≤ 1`, `σ ≥ 0` and `2 ≤ y ≤ z`:
`E‖F_{y,z}(½+σ)‖^{2q} ≤ κ^{q(2q-1)}·exp(q(2q-1)(9.0028/log y + 9.0028/log z + (2-2q)/(3y)))`,
`κ = log z/log y`, `F_{y,z}` the product over `y < p ≤ z`: Mertens on the band
(`RMF.sum_primesIco_inv_le`), whose constant cancels, and `∑_{n>y} 1/n² ≤ 1/y`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_shift_rpow_le_above_half
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) :
    (∫ ω, ‖randomEulerProductIco f (y + 1) (z + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ (Real.log z / Real.log y) ^ (q * (2 * q - 1))
        * Real.exp (q * (2 * q - 1)
            * (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y))) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hly : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  rw [hf.integral_norm_randomEulerProductIco_rpow_of_pos (y + 1) (z + 1)
    (by rw [Complex.ofReal_re]; linarith) q]
  have hprimes : ∀ p ∈ primesIco (y + 1) (z + 1), p.Prime := fun p hp =>
    prime_of_mem_primesIco hp
  refine le_trans (prod_integral_norm_one_add_prime_shift_le_above_half hprimes hσ hq0 hq1) ?_
  have h1 : ∑ p ∈ primesIco (y + 1) (z + 1), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ Real.log (Real.log z) - Real.log (Real.log y) + 9.0028 / Real.log z
        + 9.0028 / Real.log y := by
    refine le_trans (Finset.sum_le_sum fun p hp =>
      rpow_neg_shift_le_inv (hprimes p hp).one_lt.le hσ) ?_
    exact sum_primesIco_inv_le hy hyz
  have h2 : ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ 1 / (y : ℝ) := by
    refine le_trans (sum_rpow_neg_shift_sq_le hprimes (m := y + 1) (N := z + 1) (fun p hp =>
      ⟨(mem_primesIco.1 hp).2.1, (mem_primesIco.1 hp).2.2⟩) hσ) ?_
    have h := sum_inv_sq_Ico_le (m := y + 1) (by omega) (z + 1)
    push_cast at h
    rwa [show (y : ℝ) + 1 - 1 = y by ring] at h
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hc0 : (0 : ℝ) ≤ (2 - 2 * q) / 3 := by linarith
  have hsum : ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ) ^ (-(1 + 2 * σ))
      + (2 - 2 * q) / 3 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)
      ≤ Real.log (Real.log z / Real.log y)
        + (9.0028 / Real.log y + 9.0028 / Real.log z + (2 - 2 * q) / (3 * y)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Real.log_div hlz.ne' hly.ne']
    have h3 := mul_le_mul_of_nonneg_left h2 hc0
    have e : (2 - 2 * q) / 3 * (1 / (y : ℝ)) = (2 - 2 * q) / (3 * y) := by
      field_simp
    linarith
  have hκ : 0 < Real.log z / Real.log y := div_pos hlz hly
  have hrpow : (Real.log z / Real.log y) ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log z / Real.log y)) := by
    rw [Real.rpow_def_of_pos hκ]
    ring_nf
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left hsum hγ0
  linarith

end RMF
