/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.EulerMomentShiftExplicit
import RMF.NumberTheory.MertensExplicit
import PrimeNumberTheoremAnd.EulerMascheroniBounds

/-!
# The Euler product moment below the critical exponent, with no loss at the small primes

For the Rademacher Euler product at `½ + σ`, `σ ≥ 0`, and `0 ≤ q ≤ ½`,

`E‖F_{y+1}(½+σ)‖^{2q} ≤ exp(q(1-2q)(9.0028/log y + 2σ(log y + log 4 + 4) - 3/20))·(log y)^{q(2q-1)}`

(`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp`), against the
`e⁷` of `RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_of_le_half`.  Two
changes remove the constant:

* **The two-atom moment, at every prime.**  `((1+u)^a + (1-u)^a)/2 ≤ 1 - a(1-a)u²/2` for
  `0 ≤ a ≤ 1`, `0 ≤ u < 1` (`RMF.rpow_add_rpow_le_two_sub`), by monotonicity: the derivative is
  `(a/2)((1-u)^{a-1} - (1+u)^{a-1} - 2(1-a)u) ≥ 0`, and `(1-u)^{-b} - (1+u)^{-b} ≥ 2bu` because it
  is `e^m·2 sinh(b·artanh u) ≥ 2b u`.  So the product is at most `exp(q(2q-1)∑_p p^{-(1+2σ)})`, with
  no local cost; the split at `31` of `RMF.prod_integral_norm_one_add_prime_shift_le_of_le_half`
  pays `3/5`.
* **Mertens' second theorem from below, with its constant.**  `M ≥ 3/20`
  (`RMF.mertens_const_ge`, true value `0.2615`) from `M = γ + ∑_p (log(1 - 1/p) + 1/p)`, the
  exact summands at `2, 3, 5`, `log(1 - 1/p) + 1/p ≥ -1/(p(p-1))` at `7 ≤ p ≤ 47` and the tail
  bound `4/48` of `Mertens.sum_M_eq_summand_le`.  Then
  `∑_{p ≤ y} 1/p ≥ log log y + M - 9.0028/log y`, and the tilt costs `2σ∑(log p)/p`.

The exponent is negative once `9.0028/log y + 2σ(log y + log 4 + 4) ≤ 3/20`, e.g. for
`log y ≥ 120` and `σ log y ≤ 1/48`; there the bound is `(log y)^{q(2q-1)}` with constant `1`.  At
`q = ½` the moment is exactly `1` whatever the Mertens constants.
-/

open MeasureTheory

namespace RMF

/-! ### The two-atom moment below `1` -/

/-- `log(1+u) - log(1-u) ≥ 2u` on `[0, 1)`: the first term of the series. -/
lemma two_mul_le_log_sub_log {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * u ≤ Real.log (1 + u) - Real.log (1 - u) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := u) (by rw [abs_of_nonneg hu0]; exact hu1)
  have := le_hasSum h 0 (fun j _ => by positivity)
  simpa using this

/-- `(1-u)^{a-1} - (1+u)^{a-1} ≥ 2(1-a)u` for `a ≤ 1`, `0 ≤ u < 1`: with `b = 1-a`, the
difference is `e^m(e^d - e^{-d})` with `m ≥ 0` and `2d = b log((1+u)/(1-u)) ≥ 2bu`. -/
lemma two_mul_le_rpow_sub_rpow_neg {u a : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ha1 : a ≤ 1) :
    2 * (1 - a) * u ≤ (1 - u) ^ (a - 1) - (1 + u) ^ (a - 1) := by
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  set b := 1 - a with hb
  have hb0 : 0 ≤ b := by linarith
  set α := -Real.log (1 - u) with hα
  set β := Real.log (1 + u) with hβ
  have hαβ : β ≤ α := by
    rw [hα, hβ]
    have : Real.log (1 + u) + Real.log (1 - u) ≤ 0 := by
      rw [← Real.log_mul hp.ne' hm.ne']
      exact Real.log_nonpos (by positivity) (by nlinarith)
    linarith
  have hQ : (1 - u) ^ (a - 1) = Real.exp (b * α) := by
    rw [Real.rpow_def_of_pos hm, hα, hb]
    congr 1
    ring
  have hP : (1 + u) ^ (a - 1) = Real.exp (-(b * β)) := by
    rw [Real.rpow_def_of_pos hp, hβ, hb]
    congr 1
    ring
  rw [hQ, hP]
  set m := b * (α - β) / 2 with hm'
  set d := b * (α + β) / 2 with hd
  have hm0 : 0 ≤ m := by
    rw [hm']
    have := mul_nonneg hb0 (sub_nonneg.2 hαβ)
    linarith
  have hlog := two_mul_le_log_sub_log hu0 hu1
  have hd0 : 0 ≤ d := by
    rw [hd]
    have hαβ0 : 0 ≤ α + β := by
      rw [hα, hβ]
      linarith
    have := mul_nonneg hb0 hαβ0
    linarith
  have h1 : Real.exp (b * α) = Real.exp m * Real.exp d := by
    rw [← Real.exp_add]
    congr 1
    rw [hm', hd]
    ring
  have h2 : Real.exp (-(b * β)) = Real.exp m * Real.exp (-d) := by
    rw [← Real.exp_add]
    congr 1
    rw [hm', hd]
    ring
  rw [h1, h2, ← mul_sub]
  have hsinh : 2 * d ≤ Real.exp d - Real.exp (-d) := by
    have := Real.self_le_sinh_iff.2 hd0
    rw [Real.sinh_eq] at this
    linarith
  have hdu : 2 * b * u ≤ 2 * d := by
    rw [hd, hα, hβ]
    have := mul_le_mul_of_nonneg_left hlog hb0
    linarith
  have hem : 1 ≤ Real.exp m := Real.one_le_exp hm0
  have hsd : 0 ≤ Real.exp d - Real.exp (-d) := le_trans (by linarith) hsinh
  calc 2 * b * u ≤ Real.exp d - Real.exp (-d) := le_trans hdu hsinh
    _ = 1 * (Real.exp d - Real.exp (-d)) := (one_mul _).symm
    _ ≤ Real.exp m * (Real.exp d - Real.exp (-d)) := mul_le_mul_of_nonneg_right hem hsd

/-- **The two-atom moment below `1`**: `((1+u)^a + (1-u)^a)/2 ≤ 1 - a(1-a)u²/2` for `0 ≤ a ≤ 1`,
`0 ≤ u < 1`.  The gap `φ(u) = 1 - a(1-a)u²/2 - ((1+u)^a + (1-u)^a)/2` vanishes at `0` and is
nondecreasing on `[0, 1)` by `RMF.two_mul_le_rpow_sub_rpow_neg`. -/
theorem rpow_add_rpow_le_two_sub {u a : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    ((1 + u) ^ a + (1 - u) ^ a) / 2 ≤ 1 - a * (1 - a) / 2 * u ^ 2 := by
  set φ : ℝ → ℝ := fun v => 1 - a * (1 - a) / 2 * v ^ 2 - ((1 + v) ^ a + (1 - v) ^ a) / 2
    with hφ
  have hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ
      (-(a * (1 - a) / 2 * (2 * v)) - (1 * a * (1 + v) ^ (a - 1)
        + (-1) * a * (1 - v) ^ (a - 1)) / 2) v := by
    intro v hv
    have hp : (1 + v) ≠ 0 := by linarith [hv.1]
    have hm : (1 - v) ≠ 0 := by linarith [hv.2]
    have h1 : HasDerivAt (fun v : ℝ => 1 + v) 1 v := (hasDerivAt_id v).const_add 1
    have h2 : HasDerivAt (fun v : ℝ => 1 - v) (-1) v := (hasDerivAt_id v).const_sub 1
    have h3 := (h1.rpow_const (p := a) (Or.inl hp)).add (h2.rpow_const (p := a) (Or.inl hm))
    have h4 : HasDerivAt (fun v : ℝ => a * (1 - a) / 2 * v ^ 2)
        (a * (1 - a) / 2 * (2 * v)) v := by
      have := (hasDerivAt_pow 2 v).const_mul (a * (1 - a) / 2)
      simpa using this
    exact (h4.const_sub 1).sub (h3.div_const 2)
  have hmono : MonotoneOn φ (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) ?_ ?_ ?_
    · intro v hv
      have hp : 0 < 1 + v := by linarith [hv.1]
      have hm : 0 < 1 - v := by linarith [hv.2]
      refine ContinuousAt.continuousWithinAt ?_
      have c1 : ContinuousAt (fun v : ℝ => (1 + v) ^ a) v :=
        (continuousAt_const.add continuousAt_id).rpow_const (Or.inl hp.ne')
      have c2 : ContinuousAt (fun v : ℝ => (1 - v) ^ a) v :=
        (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl hm.ne')
      exact (continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.pow 2))).sub
        ((c1.add c2).div_const 2)
    · rw [interior_Ico]
      intro v hv
      exact (hderiv v hv).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro v hv
      rw [(hderiv v hv).deriv]
      have hk := two_mul_le_rpow_sub_rpow_neg hv.1.le hv.2 ha1
      nlinarith [mul_le_mul_of_nonneg_left hk ha0]
  have h0 : φ 0 = 0 := by simp [hφ]
  have := hmono ⟨le_refl 0, by norm_num⟩ ⟨hu0, hu1⟩ hu0
  rw [h0] at this
  simp only [hφ] at this
  linarith

/-! ### The product -/

/-- `p^{-(½+σ)} < 1` for a prime `p` and `σ ≥ 0`. -/
lemma rpow_neg_shift_lt_one {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- **The local moment below the critical exponent, with no loss**:
`E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)p^{-(1+2σ)})` for `0 ≤ q ≤ ½` and `σ ≥ 0`, at every
prime. -/
theorem integral_norm_one_add_prime_shift_le_sharp {p : ℕ} (hp : p.Prime) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ))) := by
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) := Real.rpow_nonneg (by positivity) _
  have ht1 := rpow_neg_shift_lt_one hp hσ
  rw [cpow_neg_ofReal_eq p (1 / 2 + σ),
    integral_norm_one_add_mul_rpow_rademacherLaw_real ht0 ht1.le]
  have hloc := rpow_add_rpow_le_two_sub ht0 ht1 (by linarith : (0 : ℝ) ≤ 2 * q)
    (by linarith : 2 * q ≤ 1)
  rw [rpow_neg_shift_sq] at hloc
  refine le_trans hloc ?_
  have hexp := Real.add_one_le_exp (q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ)))
  have heq : 1 - 2 * q * (1 - 2 * q) / 2 * (p : ℝ) ^ (-(1 + 2 * σ))
      = q * (2 * q - 1) * (p : ℝ) ^ (-(1 + 2 * σ)) + 1 := by ring
  rw [heq]
  exact hexp

/-- **The local product below the critical exponent, with no loss**:
`∏_{p<y} E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)∑_{p<y} p^{-(1+2σ)})`. -/
theorem prod_integral_norm_one_add_prime_shift_le_sharp {σ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (y : ℕ) :
    (∏ p ∈ Nat.primesBelow y,
        ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * ∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ))) := by
  have hnn : ∀ p ∈ Nat.primesBelow y,
      (0 : ℝ) ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw :=
    fun p _ => integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  refine le_trans (Finset.prod_le_prod hnn fun p hp =>
    integral_norm_one_add_prime_shift_le_sharp (Nat.prime_of_mem_primesBelow hp) hσ hq0 hq1) ?_
  rw [← Real.exp_sum, Finset.mul_sum]

/-- **The Rademacher Euler-product moment at a shifted real abscissa, below the critical
exponent, with no loss**: `E‖F_y(½+σ)‖^{2q} ≤ exp(q(2q-1)∑_{p<y} p^{-(1+2σ)})`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_sharp
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (y : ℕ) :
    (∫ ω, ‖randomEulerProduct f y (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (q * (2 * q - 1) * ∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ))) := by
  rw [hf.integral_norm_randomEulerProduct_rpow_of_pos y
    (by rw [Complex.ofReal_re]; linarith) (2 * q)]
  exact prod_integral_norm_one_add_prime_shift_le_sharp hσ hq0 hq1 y

/-! ### The Meissel–Mertens constant from below -/

/-- `log(1 - 1/p) + 1/p ≥ -1/(p(p-1))`, from `log x ≥ 1 - 1/x`. -/
lemma mertens_summand_ge {n : ℕ} (hn : n.Prime) :
    -(1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤ Mertens.M_eq_summand n := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
  have hpos : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  rw [mertens_summand_eq hn]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hne : (n : ℝ) ≠ 0 := by positivity
  have hne1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hinv : (1 - 1 / (n : ℝ))⁻¹ = (n : ℝ) / ((n : ℝ) - 1) := by
    field_simp
  rw [hinv] at hlog
  have hid : -(1 / ((n : ℝ) * ((n : ℝ) - 1))) = 1 - (n : ℝ) / ((n : ℝ) - 1) + 1 / (n : ℝ) := by
    field_simp
    ring
  rw [hid]
  linarith

/-- **The Meissel–Mertens constant is at least `3/20`** (true value `0.26150`).
`M = γ + ∑_p (log(1 - 1/p) + 1/p)` (`Mertens.M.eq`), with the tail past `48` at most `4/48`
(`Mertens.sum_M_eq_summand_le`); the summands at `2, 3, 5` are evaluated with Mathlib's decimal
bounds for `log 2, log 3, log 5`, the other twelve below `48` bounded by `-1/(p(p-1))`
(`RMF.mertens_summand_ge`).  The margin is `0.0029`. -/
theorem mertens_const_ge : (3 / 20 : ℝ) ≤ Mertens.M := by
  classical
  have htail := Mertens.sum_M_eq_summand_le (N := 48) (by norm_num)
  rw [Mertens.γ.eq_eulerMascheroni] at htail
  have hlow := (abs_le.1 htail).2
  have hset : (Finset.range 48).filter Nat.Prime
      = ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) := by decide
  have hsum : ∑ n ∈ Finset.range 48, Mertens.M_eq_summand n
      = ∑ n ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ),
          Mertens.M_eq_summand n := by
    rw [← hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rfl
    · simp
  have e2 : Mertens.M_eq_summand 2 = 1 / 2 - Real.log 2 := by
    rw [mertens_summand_eq Nat.prime_two,
      show (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have e3 : Mertens.M_eq_summand 3 = 1 / 3 + Real.log 2 - Real.log 3 := by
    rw [mertens_summand_eq (by norm_num),
      show (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
    norm_num
    ring
  have e5 : Mertens.M_eq_summand 5 = 1 / 5 + 2 * Real.log 2 - Real.log 5 := by
    rw [mertens_summand_eq (by norm_num),
      show (1 : ℝ) - 1 / ((5 : ℕ) : ℝ) = (2 : ℝ) ^ 2 / 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  have hg : ∀ p : ℕ, p.Prime → ∀ c : ℝ, c ≤ -(1 / ((p : ℝ) * ((p : ℝ) - 1))) →
      c ≤ Mertens.M_eq_summand p := fun p hp c hc => hc.trans (mertens_summand_ge hp)
  have h7 := hg 7 (by norm_num) (-(1 / 42)) (by norm_num)
  have h11 := hg 11 (by norm_num) (-(1 / 110)) (by norm_num)
  have h13 := hg 13 (by norm_num) (-(1 / 156)) (by norm_num)
  have h17 := hg 17 (by norm_num) (-(1 / 272)) (by norm_num)
  have h19 := hg 19 (by norm_num) (-(1 / 342)) (by norm_num)
  have h23 := hg 23 (by norm_num) (-(1 / 506)) (by norm_num)
  have h29 := hg 29 (by norm_num) (-(1 / 812)) (by norm_num)
  have h31 := hg 31 (by norm_num) (-(1 / 930)) (by norm_num)
  have h37 := hg 37 (by norm_num) (-(1 / 1332)) (by norm_num)
  have h41 := hg 41 (by norm_num) (-(1 / 1640)) (by norm_num)
  have h43 := hg 43 (by norm_num) (-(1 / 1806)) (by norm_num)
  have h47 := hg 47 (by norm_num) (-(1 / 2162)) (by norm_num)
  rw [hsum] at hlow
  repeat rw [Finset.sum_insert (by decide)] at hlow
  rw [Finset.sum_singleton] at hlow
  rw [e2, e3, e5] at hlow
  have hγ := hγ_lo
  norm_num at hlow
  linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

/-- **Mertens' second theorem from below, with its constant**:
`log log y + M - 9.0028/log y ≤ ∑_{p ≤ y} 1/p` for `y ≥ 2`. -/
theorem log_log_add_le_sum_primesBelow_inv {y : ℕ} (hy : 2 ≤ y) :
    Real.log (Real.log y) + Mertens.M - 9.0028 / Real.log y
      ≤ ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ := by
  classical
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have heq := Mertens.sum_prime_div_eq (y : ℝ)
  have habs := Mertens.E₂p.abs_le hy2
  have hconst := mertens_error_const_le
  have hE : -(9.0028 / Real.log y) ≤ Mertens.E₂p (y : ℝ) := by
    have h1 := (abs_le.1 habs).1
    have h2 : (Real.log 4 + 6 + Mertens.E₁) / Real.log y ≤ 9.0028 / Real.log y :=
      div_le_div_of_nonneg_right hconst hlogy.le
    linarith
  rw [Nat.floor_natCast] at heq
  have hset : Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 y) = Nat.primesBelow (y + 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesBelow]
    exact ⟨fun hp => ⟨by omega, hp.2⟩, fun hp => ⟨⟨hp.2.pos, by omega⟩, hp.2⟩⟩
  rw [hset] at heq
  have hinv : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
      = ∑ p ∈ Nat.primesBelow (y + 1), (1 : ℝ) / p :=
    Finset.sum_congr rfl fun p _ => (one_div _).symm
  rw [hinv, heq]
  linarith

/-- **Mertens' second theorem from below, at a shifted abscissa, with its constant**:
`log log y + 3/20 - 9.0028/log y - 2σ(log y + log 4 + 4) ≤ ∑_{p ≤ y} p^{-(1+2σ)}` for `y ≥ 2`,
`σ ≥ 0`. -/
theorem log_log_sub_le_sum_primesBelow_rpow_sharp {y : ℕ} (hy : 2 ≤ y) {σ : ℝ} (hσ : 0 ≤ σ) :
    Real.log (Real.log y) + 3 / 20 - 9.0028 / Real.log y
        - 2 * σ * (Real.log y + Real.log 4 + 4)
      ≤ ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ)) := by
  classical
  have hterm : ∀ p ∈ Nat.primesBelow (y + 1),
      ((p : ℝ))⁻¹ - 2 * σ * (Real.log p / p) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hfac : (p : ℝ) ^ (-(1 + 2 * σ)) = ((p : ℝ))⁻¹ * Real.exp (-(2 * σ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (inv_pos.2 hp0), ← Real.exp_add,
        Real.log_inv]
      congr 1
      ring
    have hexp : 1 - 2 * σ * Real.log p ≤ Real.exp (-(2 * σ * Real.log p)) := by
      linarith [Real.add_one_le_exp (-(2 * σ * Real.log p))]
    have hmul := mul_le_mul_of_nonneg_left hexp (inv_nonneg.2 hp0.le)
    rw [← hfac] at hmul
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  have hlow := log_log_add_le_sum_primesBelow_inv hy
  have hM := mertens_const_ge
  have hfirst := sum_log_div_primesBelow_le (by omega : 1 ≤ y)
  have hshift : (∑ p ∈ Nat.primesBelow (y + 1), 2 * σ * (Real.log p / p))
      ≤ 2 * σ * (Real.log y + Real.log 4 + 4) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hfirst (by linarith)
  linarith

/-! ### The log form -/

/-- **The moment below the critical exponent, at a shifted abscissa, sharp.**  For `0 ≤ q ≤ ½`,
`σ ≥ 0` and `y ≥ 2`,

`E‖F_{y+1}(½+σ)‖^{2q}
  ≤ exp(q(1-2q)(9.0028/log y + 2σ(log y + log 4 + 4) - 3/20))·(log y)^{q(2q-1)}`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    {y : ℕ} (hy : 2 ≤ y) :
    (∫ ω, ‖randomEulerProduct f (y + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (q * (1 - 2 * q)
          * (9.0028 / Real.log y + 2 * σ * (Real.log y + Real.log 4 + 4) - 3 / 20))
        * (Real.log y) ^ (q * (2 * q - 1)) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  refine le_trans (hf.integral_norm_randomEulerProduct_shift_rpow_le_sharp hσ hq0 hq1 (y + 1)) ?_
  have hlow := log_log_sub_le_sum_primesBelow_rpow_sharp hy hσ
  have hc : q * (2 * q - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0 (by linarith)
  rw [Real.rpow_def_of_pos hlogy, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonpos_left hlow hc
  nlinarith [this]

/-- **The moment at `½` below the critical exponent, sharp**: the case `σ = 0`, in the form
`randomEulerProduct f (y + 1) (1 / 2)`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_half_rpow_le_log_sharp
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) {y : ℕ} (hy : 2 ≤ y) :
    (∫ ω, ‖randomEulerProduct f (y + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log y - 3 / 20))
        * (Real.log y) ^ (q * (2 * q - 1)) := by
  have h := hf.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp le_rfl hq0 hq1 hy
  have hs : (((1 / 2 + 0 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  rw [hs] at h
  simpa using h

end RMF
