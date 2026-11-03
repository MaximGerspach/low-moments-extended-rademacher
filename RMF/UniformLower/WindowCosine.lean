/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBlockExplicit
import LeanCert.Tactic.IntervalAuto
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The first blocks' cosine sums

The block sums `∑_{p ∈ primeBlockSub θ m} cos(τ log p)p^{-1-2σ}` for the first blocks above a cut,
where the decay bound `3/(τe^{m+θ})` of
`RMF.abs_sum_cos_primeBlockSub_le_explicit_floor_two_regime` exceeds `1`: the main term is kept as
its log-integral.

* **(A)** `RMF.abs_sum_cos_primeBlockSub_sub_integral_le`: within `(τ+1)/10²⁸` of
  `∫_{e^{m+θ}}^{e^{m+θ+1}} cos(τu)e^{-2σu}/u du` for `m + θ ≥ 104` — the Abel summation
  `RMF.cos_prime_sum_block_eq` without its main term, and the weight moved across by
  `RMF.abs_sum_sub_integral_weight_le_of_nonneg`.
* **(B)** `RMF.abs_integral_cos_mul_exp_div_sub_le`: the damping `e^{-2σu}` costs `2σ(b-a)`.
* **(C)** `RMF.integral_cos_div_eq_blockCos`: the undamped integral is `RMF.blockCos (log τ + θ) m`,
  where `blockCos ξ m = ∫_{m+ξ}^{m+1+ξ} cos(e^v) dv`.
* **(D)** `blockCos ξ m ≥ 1 - (e²-1)e^{2(m+ξ)}/4`, `|blockCos ξ m| ≤ 2e^{-(m+ξ)}`, `blockCos` is
  `2`-Lipschitz in `ξ`, and `blockCos · 0` is antitone on `[-1, log π - 1]`.
* **(E)** The ranges of the first blocks at the one-point frequency (`ξ ∈ [-1, 0]`) and the
  doubled one (`ξ ∈ [log 2 - 1, log 2]`): kernel-checked interval arithmetic at 37 points, on
  Taylor's polynomial for `cos` below `e²` (`RMF.cosExpAnti`) and the asymptotic antiderivative
  above (`RMF.cosExpTail`), interpolated by the Lipschitz bound.
-/

namespace RMF

/-! ### The block sum as its integral -/

/-- **The block sum minus its main term.**  `RMF.cos_prime_sum_block_eq` without the main
term: the two boundary terms and the error integral of `RMF.abs_cos_prime_sum_block_le`. -/
theorem abs_cos_prime_sum_block_sub_integral_le {τ C y₁ y₂ : ℝ} (hC : 0 ≤ C)
    (hE : ∀ t : ℝ, y₁ ≤ t → t ≤ y₂ → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ 2)
    (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) :
    |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
        - ∫ t in y₁..y₂, cosLogDiv τ t|
      ≤ 2 * C / Real.log y₁ ^ 3 + C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) := by
  have hy₂ : (2 : ℝ) ≤ y₂ := hy₁.trans hy
  have hlog₁ : (0 : ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  have hmono : Real.log y₁ ≤ Real.log y₂ := Real.log_le_log (by linarith) hy
  rw [cos_prime_sum_block_eq τ hy₁ hy]
  have h2 : |cosLogDiv τ y₂ * (Chebyshev.theta y₂ - y₂)| ≤ C / Real.log y₁ ^ 3 :=
    (abs_cosLogDiv_mul_sub_le τ hy₂ (hE y₂ hy le_rfl)).trans (by gcongr)
  have h3 : |cosLogDiv τ y₁ * (Chebyshev.theta y₁ - y₁)| ≤ C / Real.log y₁ ^ 3 :=
    abs_cosLogDiv_mul_sub_le τ hy₁ (hE y₁ le_rfl hy)
  have h4 : |∫ t in y₁..y₂, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
      ≤ C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) := abs_integral_deriv_mul_sub_le' τ hC hE hy₁ hy
  have hb : 2 * C / Real.log y₁ ^ 3 = C / Real.log y₁ ^ 3 + C / Real.log y₁ ^ 3 := by ring
  rw [abs_le] at h2 h3 h4 ⊢
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- **The block sum minus its main term, past the effective prime number theorem's threshold**:
at most `32C₀(τ+1)e^{-c(log y₁)^{1/10}}`, the error half of
`RMF.abs_cos_prime_sum_block_le_threshold_of_le`. -/
theorem abs_cos_prime_sum_block_sub_integral_le_threshold_of_le {c C₀ : ℝ} (hc0 : 0 < c)
    (hC₀ : 0 ≤ C₀) {x₀ : ℝ} (hx₀2 : 2 ≤ x₀) (hE : ∀ x ≥ x₀,
      |Chebyshev.theta x - x| ≤ C₀ * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))))
    {τ y₁ y₂ : ℝ} (hτ : 0 ≤ τ) (hy₁ : max x₀ (Real.exp 1) ≤ y₁) (hy : y₁ ≤ y₂)
    (hlog2 : Real.log y₂ ≤ 3 * Real.log y₁) :
    |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
        - ∫ t in y₁..y₂, cosLogDiv τ t|
      ≤ 32 * C₀ * (τ + 1) * Real.exp (-c * Real.log y₁ ^ ((1 : ℝ) / 10)) := by
  have hy₁x₀ : x₀ ≤ y₁ := le_trans (le_max_left _ _) hy₁
  have hy₁e : Real.exp 1 ≤ y₁ := le_trans (le_max_right _ _) hy₁
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hx₀2 hy₁x₀
  set L : ℝ := Real.log y₁ with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) hy₁e
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < L := by linarith
  have hr0 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hL0.le _
  set E : ℝ := Real.exp (-c * L ^ ((1 : ℝ) / 10)) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set Cy : ℝ := 9 * C₀ * E * L ^ 2 with hCydef
  have hCy0 : (0 : ℝ) ≤ Cy := by positivity
  have hEy : ∀ t : ℝ, y₁ ≤ t → t ≤ y₂ →
      |Chebyshev.theta t - t| ≤ Cy * t / Real.log t ^ 2 := by
    intro s hs1 hs2
    have hs0 : (0 : ℝ) < s := by linarith
    have hLs : L ≤ Real.log s := Real.log_le_log (by linarith) hs1
    have hLs0 : (0 : ℝ) < Real.log s := by linarith
    have hLs2 : Real.log s ≤ 3 * L := le_trans (Real.log_le_log (by linarith) hs2) hlog2
    have h1 := hE s (le_trans hy₁x₀ hs1)
    have h2 : Real.exp (-c * Real.log s ^ ((1 : ℝ) / 10)) ≤ E := by
      refine Real.exp_le_exp.2 ?_
      have h3 : L ^ ((1 : ℝ) / 10) ≤ Real.log s ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow hL0.le hLs (by norm_num)
      nlinarith
    have h4 : |Chebyshev.theta s - s| ≤ C₀ * s * E := by
      have h5 : C₀ * (s * Real.exp (-c * Real.log s ^ ((1 : ℝ) / 10))) ≤ C₀ * (s * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hs0.le) hC₀
      nlinarith
    have h6 : C₀ * s * E ≤ Cy * s / Real.log s ^ 2 := by
      rw [hCydef, le_div_iff₀ (by positivity)]
      have h7 : Real.log s ^ 2 ≤ 9 * L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hC₀ hs0.le) hE0.le]
    linarith
  refine (abs_cos_prime_sum_block_sub_integral_le hCy0 hEy hy₁2 hy).trans ?_
  have hCE : (0 : ℝ) ≤ C₀ * E := mul_nonneg hC₀ hE0.le
  have h1 : 2 * Cy / L ^ 3 = 18 * (C₀ * E) / L := by rw [hCydef]; field_simp; ring
  have h2 : Cy * (|τ| + 3) / (2 * L ^ 2) = 9 / 2 * (C₀ * E) * (τ + 3) := by
    rw [abs_of_nonneg hτ, hCydef]; field_simp
  have h3 : 18 * (C₀ * E) / L ≤ 18 * (C₀ * E) := by
    rw [div_le_iff₀ hL0]; nlinarith
  rw [h1, h2]
  nlinarith [h3, hCE, hτ, mul_nonneg hCE hτ]

/-- `cosLogDiv τ` is continuous on `(1, ∞)`. -/
lemma continuousOn_cosLogDiv_Ioi (τ : ℝ) : ContinuousOn (cosLogDiv τ) (Set.Ioi 1) := by
  intro t ht
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : t ≠ 0 := by positivity
  refine ContinuousAt.continuousWithinAt ?_
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  change ContinuousAt (fun t => Real.cos (τ * Real.log t) / (t * Real.log t)) t
  exact (Real.continuous_cos.continuousAt.comp (continuousAt_const.mul hlog)).div
    (continuousAt_id.mul hlog) (mul_ne_zero ht0 (Real.log_pos ht1).ne')

/-- **Moving the weight `t^{-2σ}` across a block's sum minus its integral**, at `σ ≥ 0`: if every
initial sub-block's unweighted sum is within `M` of its integral, so is the weighted sum.  Abel
summation for the sum, integration by parts for the integral; the weight is nonnegative and
decreasing, so the cost `t₂^{-2σ} + ∫|d(t^{-2σ})|` is `y₁^{-2σ} ≤ 1`. -/
theorem abs_sum_sub_integral_weight_le_of_nonneg {τ σ M y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁)
    (hy : y₁ ≤ y₂) (hσ : 0 ≤ σ)
    (hM : ∀ u ∈ Set.Icc y₁ y₂,
      |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
          - ∫ t in y₁..u, cosLogDiv τ t| ≤ M) :
    |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
        Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ))
        - ∫ t in y₁..y₂, cosLogDiv τ t * t ^ (-(2 * σ))| ≤ M := by
  have hy₁0 : (0 : ℝ) < y₁ := by linarith
  have hy₂0 : (0 : ℝ) < y₂ := by linarith
  set c : ℕ → ℝ := fun k => if k.Prime then Real.cos (τ * Real.log k) / k else 0 with hc
  set f : ℝ → ℝ := fun u => u ^ (-(2 * σ)) with hfdef
  set T : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k with hTdef
  set I : ℝ → ℝ := fun u => ∫ t in y₁..u, cosLogDiv τ t with hIdef
  set D : ℝ → ℝ := fun t => T t - T y₁ - I t with hDdef
  -- the weight
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (-(2 * σ) * t ^ (-(2 * σ) - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hdeq : Set.EqOn (deriv f) (fun t => -(2 * σ) * t ^ (-(2 * σ) - 1)) (Set.Icc y₁ y₂) :=
    fun t ht => (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).deriv
  have hf_diff : ∀ t ∈ Set.Icc y₁ y₂, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).differentiableAt
  have hf'c : ContinuousOn (deriv f) (Set.Icc y₁ y₂) := by
    refine ContinuousOn.congr ?_ hdeq
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
      Or.inl (lt_of_lt_of_le hy₁0 ht.1).ne')
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y₁ y₂) := hf'c.integrableOn_Icc
  have hf_int' : IntervalIntegrable (deriv f) MeasureTheory.volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hf_int
  have hFTC : (∫ t in y₁..y₂, deriv f t) = f y₂ - f y₁ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hf_int'
    rw [Set.uIcc_of_le hy] at ht
    exact (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).differentiableAt.hasDerivAt
  -- the integral `I` and its derivative
  have hgc : ContinuousOn (cosLogDiv τ) (Set.Ioi 1) := continuousOn_cosLogDiv_Ioi τ
  have hgi : ∀ u, y₁ ≤ u → IntervalIntegrable (cosLogDiv τ) MeasureTheory.volume y₁ u :=
    fun u hu => intervalIntegrable_cosLogDiv τ hy₁ hu
  have hIderiv : ∀ t ∈ Set.uIcc y₁ y₂, HasDerivAt I (cosLogDiv τ t) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht1 : t ∈ Set.Ioi (1 : ℝ) := Set.mem_Ioi.2 (by linarith [ht.1])
    exact intervalIntegral.integral_hasDerivAt_right (hgi t ht.1)
      (hgc.stronglyMeasurableAtFilter isOpen_Ioi t ht1)
      (hgc.continuousAt (isOpen_Ioi.mem_nhds ht1))
  have hIc : ContinuousOn I (Set.Icc y₁ y₂) := fun t ht =>
    (hIderiv t (by rwa [Set.uIcc_of_le hy])).continuousAt.continuousWithinAt
  have hIy₁ : I y₁ = 0 := intervalIntegral.integral_same
  -- the three integrands are integrable
  have hTint : IntervalIntegrable (fun t => deriv f t * T t) MeasureTheory.volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      (integrableOn_mul_sum_Icc c (m := 0) hy₁0.le hf_int)
  have hIint : IntervalIntegrable (fun t => deriv f t * I t) MeasureTheory.volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr (hf'c.mul hIc).integrableOn_Icc
  have hcint : IntervalIntegrable (fun t => deriv f t * T y₁) MeasureTheory.volume y₁ y₂ :=
    hf_int'.mul_const _
  have hDint : IntervalIntegrable (fun t => deriv f t * D t) MeasureTheory.volume y₁ y₂ := by
    have h := (hTint.sub hcint).sub hIint
    refine h.congr fun t _ => ?_
    simp only [hDdef]
    ring
  -- the sum, by Abel summation
  have hLHS : (∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, f k * c k)
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · have hk0 : (0:ℝ) < k := by exact_mod_cast hp.pos
      have hpow : (k : ℝ) ^ (1 + 2 * σ) = (k : ℝ) * (k : ℝ) ^ (2 * σ) := by
        rw [Real.rpow_add hk0, Real.rpow_one]
      have hinv : (k : ℝ) ^ (-(2 * σ)) = ((k : ℝ) ^ (2 * σ))⁻¹ := Real.rpow_neg hk0.le _
      have hne : (k : ℝ) ^ (2 * σ) ≠ 0 := (Real.rpow_pos_of_pos hk0 _).ne'
      simp only [hc, hfdef, if_pos hp]
      rw [hpow, hinv]
      field_simp
    · simp only [hc, if_neg hp, mul_zero]
  have habel := sum_mul_eq_sub_sub_integral_mul c hy₁0.le hy hf_diff hf_int
  rw [← intervalIntegral.integral_of_le hy] at habel
  -- the integral, by parts
  have hparts : (∫ t in y₁..y₂, f t * cosLogDiv τ t)
      = f y₂ * I y₂ - f y₁ * I y₁ - ∫ t in y₁..y₂, deriv f t * I t :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t ht => by
        rw [Set.uIcc_of_le hy] at ht
        exact (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).differentiableAt.hasDerivAt)
      hIderiv hf_int' (hgi y₂ hy)
  have hint_eq : (∫ t in y₁..y₂, cosLogDiv τ t * t ^ (-(2 * σ)))
      = ∫ t in y₁..y₂, f t * cosLogDiv τ t :=
    intervalIntegral.integral_congr fun t _ => by simp only [hfdef]; ring
  -- the difference is `f y₂ D y₂ - ∫ f' D`
  have hsplit : (∫ t in y₁..y₂, deriv f t * D t)
      = (∫ t in y₁..y₂, deriv f t * T t) - (f y₂ - f y₁) * T y₁
        - ∫ t in y₁..y₂, deriv f t * I t := by
    have h1 : (∫ t in y₁..y₂, deriv f t * D t)
        = ∫ t in y₁..y₂, (deriv f t * T t - deriv f t * T y₁ - deriv f t * I t) :=
      intervalIntegral.integral_congr fun t _ => by simp only [hDdef]; ring
    rw [h1, intervalIntegral.integral_sub (hTint.sub hcint) hIint,
      intervalIntegral.integral_sub hTint hcint, intervalIntegral.integral_mul_const, hFTC]
  have hkey : (∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
        Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ))
        - ∫ t in y₁..y₂, cosLogDiv τ t * t ^ (-(2 * σ))
      = f y₂ * D y₂ - ∫ t in y₁..y₂, deriv f t * D t := by
    rw [← hLHS, habel, hint_eq, hparts, hsplit, hIy₁]
    simp only [hDdef, hTdef]
    ring
  -- the bound on `D`
  have hD : ∀ u ∈ Set.Icc y₁ y₂, |D u| ≤ M := by
    intro u hu
    have h := hM u hu
    have hsum : (∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
        = T u - T y₁ := by
      rw [Finset.sum_filter, sum_Ioc_eq_sub (Nat.floor_le_floor hu.1)]
    rw [hsum] at h
    simpa only [hDdef] using h
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hD y₁ ⟨le_rfl, hy⟩)
  -- the weight is nonnegative and decreasing
  have hneg : ∀ t ∈ Set.Icc y₁ y₂, deriv f t ≤ 0 := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hy₁0 ht.1
    rw [hdeq ht]
    have hp : (0:ℝ) ≤ t ^ (-(2 * σ) - 1) := (Real.rpow_pos_of_pos ht0 _).le
    nlinarith
  have hfy₂0 : (0:ℝ) < f y₂ := Real.rpow_pos_of_pos hy₂0 _
  have hfy₁1 : f y₁ ≤ 1 := by
    simp only [hfdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hintabs : |∫ t in y₁..y₂, deriv f t * D t| ≤ M * (f y₁ - f y₂) := by
    calc |∫ t in y₁..y₂, deriv f t * D t|
        ≤ ∫ t in y₁..y₂, |deriv f t * D t| := intervalIntegral.abs_integral_le_integral_abs hy
      _ ≤ ∫ t in y₁..y₂, M * (-deriv f t) := by
          refine intervalIntegral.integral_mono_on hy hDint.abs (hf_int'.neg.const_mul M)
            fun t ht => ?_
          rw [abs_mul, abs_of_nonpos (hneg t ht), mul_comm]
          exact mul_le_mul_of_nonneg_right (hD t ht) (by linarith [hneg t ht])
      _ = M * (f y₁ - f y₂) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hFTC]
          ring
  rw [hkey]
  calc |f y₂ * D y₂ - ∫ t in y₁..y₂, deriv f t * D t|
      ≤ |f y₂ * D y₂| + |∫ t in y₁..y₂, deriv f t * D t| := abs_sub _ _
    _ ≤ f y₂ * M + M * (f y₁ - f y₂) := by
        rw [abs_mul, abs_of_pos hfy₂0]
        exact add_le_add (mul_le_mul_of_nonneg_left (hD y₂ ⟨hy, le_rfl⟩) hfy₂0.le) hintabs
    _ = M * f y₁ := by ring
    _ ≤ M := by nlinarith

/-- The substitution `u = log t`: `∫_{y₁}^{y₂} cosLogDiv τ t · t^{-2σ} dt =
∫_{log y₁}^{log y₂} cos(τu) e^{-2σu}/u du`. -/
lemma integral_cosLogDiv_mul_rpow_eq {τ σ y₁ y₂ : ℝ} (hy₁ : 1 < y₁) (hy : y₁ ≤ y₂) :
    (∫ t in y₁..y₂, cosLogDiv τ t * t ^ (-(2 * σ)))
      = ∫ u in Real.log y₁..Real.log y₂, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u := by
  have hy₁0 : (0 : ℝ) < y₁ := by linarith
  have hy₂0 : (0 : ℝ) < y₂ := by linarith
  have hle : Real.log y₁ ≤ Real.log y₂ := Real.log_le_log hy₁0 hy
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := Real.exp) (f' := Real.exp) (g := fun t => cosLogDiv τ t * t ^ (-(2 * σ)))
    (a := Real.log y₁) (b := Real.log y₂) Real.continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
  rw [Real.exp_log hy₁0, Real.exp_log hy₂0] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hle] at hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.log_pos hy₁) hu.1
  simp only [Function.comp_apply, cosLogDiv, Real.log_exp]
  rw [← Real.exp_mul, show u * -(2 * σ) = -(2 * σ) * u by ring]
  have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  field_simp

/-- **The block cosine sum as its log-integral**, past the explicit floor `104`: for `τ ≥ 0`,
`σ ≥ 0` and `m + θ ≥ 104`,
`|∑_{p ∈ block m} cos(τ log p)p^{-1-2σ} - ∫_{e^{m+θ}}^{e^{m+θ+1}} cos(τu)e^{-2σu}/u du| ≤
(τ+1)/10²⁸`. -/
theorem abs_sum_cos_primeBlockSub_sub_integral_le (τ σ θ : ℝ) (m : ℕ) (hτ : 0 ≤ τ)
    (hσ0 : 0 ≤ σ) (hm : 104 ≤ (m : ℝ) + θ) :
    |(∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1),
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ (τ + 1) / 10 ^ 28 := by
  obtain ⟨hx₀2, hEθ⟩ := abs_theta_sub_le_exp_numeral_explicit
  have hthr : Real.log (Real.log blockCosineThreshold) ≤ (m : ℝ) + θ :=
    le_trans log_log_blockCosineThreshold_le_104 hm
  have hy₀2 : (2 : ℝ) ≤ blockCosineThreshold := le_trans hx₀2 (le_max_left _ _)
  have hXpos : (0 : ℝ) < blockScale θ (m + 1) := blockScale_pos θ (m + 1)
  set y₁ : ℝ := blockScale θ (m + 1) ^ (Real.exp 1)⁻¹ with hy₁def
  have hlogX : Real.log (blockScale θ (m + 1)) = Real.exp ((m : ℝ) + θ + 1) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hlogy₁ : Real.log y₁ = Real.exp ((m : ℝ) + θ) := by
    rw [hy₁def, Real.log_rpow hXpos, hlogX, show (m : ℝ) + θ + 1 = 1 + ((m : ℝ) + θ) by ring,
      Real.exp_add]
    field_simp
  have hy₁pos : (0 : ℝ) < y₁ := Real.rpow_pos_of_pos hXpos _
  have hy₀0 : (0 : ℝ) < Real.log blockCosineThreshold := Real.log_pos (by linarith)
  have hy₀y₁ : blockCosineThreshold ≤ y₁ := by
    have hle : Real.log blockCosineThreshold ≤ Real.log y₁ := by
      rw [hlogy₁, ← Real.exp_log hy₀0]
      exact Real.exp_le_exp.2 hthr
    have h := Real.exp_le_exp.2 hle
    rwa [Real.exp_log (by linarith : (0 : ℝ) < blockCosineThreshold),
      Real.exp_log hy₁pos] at h
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hy₀2 hy₀y₁
  have hy₁y₂ : y₁ ≤ blockScale θ (m + 1) := by
    rw [← Real.exp_log hy₁pos, ← Real.exp_log hXpos, hlogy₁, hlogX]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
  have hratio : Real.log (blockScale θ (m + 1)) ≤ 3 * Real.log y₁ := by
    rw [hlogX, hlogy₁, show (m : ℝ) + θ + 1 = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    have hpos : (0 : ℝ) < Real.exp ((m : ℝ) + θ) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_d9]
  -- the sum over the block, as a sum over `(y₁, y₂]`
  have hrw : ∀ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [Finset.sum_congr rfl hrw]
  have hrw2 : (∑ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [primeBlockSub, harperBlock,
      sum_primesIcoSub _ _ fun q => Real.cos (τ * Real.log (q : ℝ)) / ((q : ℝ)) ^ (1 + 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw2]
  -- the integral, in the `u = log t` form
  rw [← hlogy₁, ← hlogX, ← integral_cosLogDiv_mul_rpow_eq (by linarith) hy₁y₂]
  -- the unweighted bound on every initial sub-block
  set Mb : ℝ := 32 * 10 ^ (40 : ℕ) * (τ + 1)
      * Real.exp (-(1 / 200 : ℝ) * Real.log y₁ ^ ((1 : ℝ) / 10)) with hMbdef
  have hsub : ∀ u ∈ Set.Icc y₁ (blockScale θ (m + 1)),
      |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
          - ∫ t in y₁..u, cosLogDiv τ t| ≤ Mb := by
    intro u hu
    exact abs_cos_prime_sum_block_sub_integral_le_threshold_of_le (by norm_num) (by positivity)
      hx₀2 hEθ hτ hy₀y₁ hu.1 (le_trans (Real.log_le_log (by linarith [hu.1]) hu.2) hratio)
  refine (abs_sum_sub_integral_weight_le_of_nonneg hy₁2 hy₁y₂ hσ0 hsub).trans ?_
  -- the numeral
  have hEeq : Real.log y₁ ^ ((1 : ℝ) / 10) = Real.exp (((m : ℝ) + θ) / 10) := by
    rw [hlogy₁, ← Real.exp_mul]
    ring_nf
  have he : Real.exp 10.4 ≤ Real.exp (((m : ℝ) + θ) / 10) := Real.exp_le_exp.2 (by linarith)
  have hexp : Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      ≤ Real.exp (-(1 / 200 : ℝ) * Real.exp 10.4) := Real.exp_le_exp.2 (by linarith)
  have hτ1 : (0 : ℝ) ≤ τ + 1 := by linarith
  rw [hMbdef, hEeq]
  calc 32 * 10 ^ (40 : ℕ) * (τ + 1) * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))
      = (τ + 1) * (32 * 10 ^ (40 : ℕ)
          * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10))) := by ring
    _ ≤ (τ + 1) * (1 / 10 ^ 28) := by
        refine mul_le_mul_of_nonneg_left ?_ hτ1
        exact le_trans (mul_le_mul_of_nonneg_left hexp (by positivity)) pnt_term_at_floor_le
    _ = (τ + 1) / 10 ^ 28 := by ring

/-! ### Damping and the normalised integral -/

/-- **Damping.**  `|∫_a^b cos(τu)e^{-2σu}/u du - ∫_a^b cos(τu)/u du| ≤ 2σ(b-a)` for `0 < a ≤ b`
and `σ ≥ 0`, from `1 - e^{-x} ≤ x`. -/
theorem abs_integral_cos_mul_exp_div_sub_le {τ σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hσ : 0 ≤ σ) :
    |(∫ u in a..b, Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        - ∫ u in a..b, Real.cos (τ * u) / u| ≤ 2 * σ * (b - a) := by
  have hc1 : ContinuousOn (fun u : ℝ => Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div (by fun_prop) continuousOn_id fun u hu => (ha.trans_le hu.1).ne'
  have hc2 := continuousOn_cos_div (τ := τ) ha hab
  rw [← intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable]
  have hbound : ∀ u ∈ Set.uIoc a b,
      ‖Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u - Real.cos (τ * u) / u‖ ≤ 2 * σ := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    have hu0 : 0 < u := ha.trans hu.1
    have hform : Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u - Real.cos (τ * u) / u
        = Real.cos (τ * u) * (Real.exp (-(2 * σ) * u) - 1) / u := by ring
    rw [Real.norm_eq_abs, hform, abs_div, abs_mul, abs_of_pos hu0, div_le_iff₀ hu0]
    have h1 : |Real.cos (τ * u)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |Real.exp (-(2 * σ) * u) - 1| ≤ 2 * σ * u := by
      have he : Real.exp (-(2 * σ) * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have he' : 1 - 2 * σ * u ≤ Real.exp (-(2 * σ) * u) := by
        linarith [Real.add_one_le_exp (-(2 * σ) * u)]
      rw [abs_le]
      constructor <;> linarith
    calc |Real.cos (τ * u)| * |Real.exp (-(2 * σ) * u) - 1| ≤ 1 * (2 * σ * u) :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 2 * σ * u := one_mul _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at h

/-- **The normalised block integral** `∫_{m+ξ}^{m+1+ξ} cos(e^v) dv`: the block's main term at
`ξ = log τ + θ` (`RMF.integral_cos_div_eq_blockCos`).  It depends on `m + ξ` only. -/
noncomputable def blockCos (ξ : ℝ) (m : ℕ) : ℝ :=
  ∫ v in ((m : ℝ) + ξ)..((m : ℝ) + 1 + ξ), Real.cos (Real.exp v)

/-- **The substitution `u = e^{v}/τ`**: `∫_{e^{m+θ}}^{e^{m+θ+1}} cos(τu)/u du =
blockCos (log τ + θ) m` for `τ > 0`. -/
theorem integral_cos_div_eq_blockCos {τ : ℝ} (hτ : 0 < τ) (θ : ℝ) (m : ℕ) :
    (∫ u in Real.exp ((m : ℝ) + θ)..Real.exp ((m : ℝ) + θ + 1), Real.cos (τ * u) / u)
      = blockCos (Real.log τ + θ) m := by
  rw [blockCos]
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun v => Real.exp v / τ) (f' := fun v => Real.exp v / τ)
    (g := fun u => Real.cos (τ * u) / u)
    (a := (m : ℝ) + (Real.log τ + θ)) (b := (m : ℝ) + 1 + (Real.log τ + θ))
    (Real.continuous_exp.div_const τ).continuousOn
    (fun x _ => (Real.hasDerivAt_exp x).div_const τ) (fun x _ => by positivity)
  have hfa : Real.exp ((m : ℝ) + (Real.log τ + θ)) / τ = Real.exp ((m : ℝ) + θ) := by
    rw [show (m : ℝ) + (Real.log τ + θ) = Real.log τ + ((m : ℝ) + θ) by ring, Real.exp_add,
      Real.exp_log hτ]
    field_simp
  have hfb : Real.exp ((m : ℝ) + 1 + (Real.log τ + θ)) / τ = Real.exp ((m : ℝ) + θ + 1) := by
    rw [show (m : ℝ) + 1 + (Real.log τ + θ) = Real.log τ + ((m : ℝ) + θ + 1) by ring,
      Real.exp_add, Real.exp_log hτ]
    field_simp
  rw [hfa, hfb] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun v _ => ?_
  have hev : Real.exp v / τ ≠ 0 := by positivity
  simp only [Function.comp_apply]
  rw [show τ * (Real.exp v / τ) = Real.exp v by field_simp]
  field_simp

/-! ### Elementary bounds on `blockCos` -/

/-- **The correlated regime.**  `1 - (e²-1)e^{2(m+ξ)}/4 ≤ blockCos ξ m`, from
`cos w ≥ 1 - w²/2`. -/
theorem one_sub_le_blockCos (ξ : ℝ) (m : ℕ) :
    1 - (Real.exp 2 - 1) * Real.exp (2 * ((m : ℝ) + ξ)) / 4 ≤ blockCos ξ m := by
  rw [blockCos]
  have hab : (m : ℝ) + ξ ≤ (m : ℝ) + 1 + ξ := by linarith
  have hpt : ∀ v ∈ Set.Icc ((m : ℝ) + ξ) ((m : ℝ) + 1 + ξ),
      1 - Real.exp (2 * v) / 2 ≤ Real.cos (Real.exp v) := by
    intro v _
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.exp v)
    rwa [sq, ← Real.exp_add, show v + v = 2 * v by ring] at h
  have hint1 : IntervalIntegrable (fun v : ℝ => 1 - Real.exp (2 * v) / 2) MeasureTheory.volume
      ((m : ℝ) + ξ) ((m : ℝ) + 1 + ξ) :=
    (by fun_prop : Continuous fun v : ℝ => 1 - Real.exp (2 * v) / 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun v : ℝ => Real.cos (Real.exp v)) MeasureTheory.volume
      ((m : ℝ) + ξ) ((m : ℝ) + 1 + ξ) :=
    (by fun_prop : Continuous fun v : ℝ => Real.cos (Real.exp v)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hpt
  have hderiv : ∀ x ∈ Set.uIcc ((m : ℝ) + ξ) ((m : ℝ) + 1 + ξ),
      HasDerivAt (fun v : ℝ => v - Real.exp (2 * v) / 4) (1 - Real.exp (2 * x) / 2) x := by
    intro x _
    have h := (hasDerivAt_id x).sub
      ((((Real.hasDerivAt_exp (2 * x)).comp x ((hasDerivAt_id x).const_mul 2))).div_const 4)
    refine h.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1] at hmono
  have hexp : Real.exp (2 * ((m : ℝ) + 1 + ξ)) = Real.exp 2 * Real.exp (2 * ((m : ℝ) + ξ)) := by
    rw [← Real.exp_add]
    ring_nf
  have hcalc : ((m : ℝ) + 1 + ξ - Real.exp (2 * ((m : ℝ) + 1 + ξ)) / 4)
      - ((m : ℝ) + ξ - Real.exp (2 * ((m : ℝ) + ξ)) / 4)
      = 1 - (Real.exp 2 - 1) * Real.exp (2 * ((m : ℝ) + ξ)) / 4 := by
    rw [hexp]
    ring
  linarith

/-- `|∫_c^b cos u/u du| ≤ 2/c` for `0 < c ≤ b`: one integration by parts, as in
`RMF.abs_integral_cos_div_tail_le'`, without rounding the three terms up separately. -/
lemma abs_integral_cos_div_le_two_div {c b : ℝ} (hc : 0 < c) (hcb : c ≤ b) :
    |∫ u in c..b, Real.cos u / u| ≤ 2 / c := by
  have hb : 0 < b := hc.trans_le hcb
  have hderiv1 : ∀ x ∈ Set.uIcc c b, HasDerivAt (fun u : ℝ => 1 / u) (-(1 / x ^ 2)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rw [Set.uIcc_of_le hcb] at hx
      exact (hc.trans_le hx.1).ne'
    simpa [one_div] using (hasDerivAt_inv hx0)
  have hderiv2 : ∀ x ∈ Set.uIcc c b, HasDerivAt Real.sin (Real.cos x) x :=
    fun x _ => Real.hasDerivAt_sin x
  have hint1 : IntervalIntegrable (fun x : ℝ => -(1 / x ^ 2)) MeasureTheory.volume c b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hcb]
    exact (continuousOn_one_div_sq hc b).neg
  have hint2 : IntervalIntegrable Real.cos MeasureTheory.volume c b :=
    Real.continuous_cos.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderiv1 hderiv2 hint1 hint2
  have hgoal : (∫ u in c..b, Real.cos u / u) = ∫ x in c..b, (1 / x) * Real.cos x :=
    intervalIntegral.integral_congr fun x _ => by rw [one_div, div_eq_inv_mul]
  rw [hgoal, hparts]
  have hinvsq : (∫ x in c..b, 1 / x ^ 2) = 1 / c - 1 / b := by
    have hderiv : ∀ x ∈ Set.uIcc c b, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / x ^ 2) x := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rw [Set.uIcc_of_le hcb] at hx
        exact (hc.trans_le hx.1).ne'
      simpa [one_div] using (hasDerivAt_inv hx0).const_mul (-1 : ℝ)
    have hint : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) MeasureTheory.volume c b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hcb]
      exact continuousOn_one_div_sq hc b
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  have hrem : |∫ x in c..b, -(1 / x ^ 2) * Real.sin x| ≤ 1 / c - 1 / b := by
    have habs : IntervalIntegrable
        (fun x : ℝ => |-(1 / x ^ 2) * Real.sin x|) MeasureTheory.volume c b := by
      refine ContinuousOn.intervalIntegrable (ContinuousOn.abs ?_)
      rw [Set.uIcc_of_le hcb]
      exact ((continuousOn_one_div_sq hc b).neg).mul Real.continuous_sin.continuousOn
    have hmaj : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) MeasureTheory.volume c b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hcb]
      exact continuousOn_one_div_sq hc b
    have hpt : ∀ x ∈ Set.Icc c b, |-(1 / x ^ 2) * Real.sin x| ≤ 1 / x ^ 2 := by
      intro x hx
      have hx0 : 0 < x := hc.trans_le hx.1
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / x ^ 2)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one x)
    calc |∫ x in c..b, -(1 / x ^ 2) * Real.sin x|
        ≤ ∫ x in c..b, |-(1 / x ^ 2) * Real.sin x| :=
          intervalIntegral.abs_integral_le_integral_abs hcb
      _ ≤ ∫ x in c..b, 1 / x ^ 2 := intervalIntegral.integral_mono_on hcb habs hmaj hpt
      _ = 1 / c - 1 / b := hinvsq
  have hbd : ∀ {x : ℝ}, 0 < x → |1 / x * Real.sin x| ≤ 1 / x := by
    intro x hx
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / x)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one x)
  calc |1 / b * Real.sin b - 1 / c * Real.sin c - ∫ x in c..b, -(1 / x ^ 2) * Real.sin x|
      ≤ |1 / b * Real.sin b - 1 / c * Real.sin c|
        + |∫ x in c..b, -(1 / x ^ 2) * Real.sin x| := abs_sub _ _
    _ ≤ (|1 / b * Real.sin b| + |1 / c * Real.sin c|)
        + |∫ x in c..b, -(1 / x ^ 2) * Real.sin x| := by
        gcongr
        exact abs_sub _ _
    _ ≤ (1 / b + 1 / c) + (1 / c - 1 / b) := by linarith [hbd hb, hbd hc, hrem]
    _ = 2 / c := by ring

/-- **The decorrelated regime.**  `|blockCos ξ m| ≤ 2e^{-(m+ξ)}`: after `w = e^v`, the
integral `∫ cos w/w dw` from `e^{m+ξ}`. -/
theorem abs_blockCos_le (ξ : ℝ) (m : ℕ) : |blockCos ξ m| ≤ 2 * Real.exp (-((m : ℝ) + ξ)) := by
  have h := integral_cos_div_eq_blockCos (τ := 1) one_pos ξ m
  rw [Real.log_one, zero_add] at h
  rw [← h]
  simp only [one_mul]
  refine (abs_integral_cos_div_le_two_div (Real.exp_pos _)
    (Real.exp_le_exp.2 (by linarith))).trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- **The shift in `ξ`.**  `blockCos ξ' m - blockCos ξ m =
∫_{m+ξ}^{m+ξ'} (cos(e^{v+1}) - cos(e^v)) dv`. -/
theorem blockCos_sub_eq (ξ ξ' : ℝ) (m : ℕ) :
    blockCos ξ' m - blockCos ξ m
      = ∫ v in ((m : ℝ) + ξ)..((m : ℝ) + ξ'),
          (Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v)) := by
  have hF : Continuous fun v : ℝ => Real.cos (Real.exp v) := by fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => Real.cos (Real.exp v))
      MeasureTheory.volume a b := fun a b => hF.intervalIntegrable a b
  have hF1 : Continuous fun v : ℝ => Real.cos (Real.exp (v + 1)) := by fun_prop
  rw [blockCos, blockCos, intervalIntegral.integral_interval_sub_interval_comm (hi _ _) (hi _ _)
      (hi _ _), intervalIntegral.integral_sub (hF1.intervalIntegrable _ _) (hi _ _),
    intervalIntegral.integral_comp_add_right (fun v => Real.cos (Real.exp v)) (1 : ℝ),
    intervalIntegral.integral_symm ((m : ℝ) + ξ) ((m : ℝ) + ξ'),
    intervalIntegral.integral_symm ((m : ℝ) + 1 + ξ) ((m : ℝ) + 1 + ξ'),
    show (m : ℝ) + ξ + 1 = (m : ℝ) + 1 + ξ by ring,
    show (m : ℝ) + ξ' + 1 = (m : ℝ) + 1 + ξ' by ring]
  ring

/-- **`blockCos` is `2`-Lipschitz in `ξ`**: its derivative is `cos(e^{m+1+ξ}) - cos(e^{m+ξ})`. -/
theorem abs_blockCos_sub_le (ξ ξ' : ℝ) (m : ℕ) :
    |blockCos ξ' m - blockCos ξ m| ≤ 2 * |ξ' - ξ| := by
  rw [blockCos_sub_eq]
  have hbd : ∀ v ∈ Set.uIoc ((m : ℝ) + ξ) ((m : ℝ) + ξ'),
      ‖Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v)‖ ≤ 2 := by
    intro v _
    rw [Real.norm_eq_abs]
    have h1 := Real.abs_cos_le_one (Real.exp (v + 1))
    have h2 := Real.abs_cos_le_one (Real.exp v)
    calc |Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v)|
        ≤ |Real.cos (Real.exp (v + 1))| + |Real.cos (Real.exp v)| := abs_sub _ _
      _ ≤ 2 := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, show (m : ℝ) + ξ' - ((m : ℝ) + ξ) = ξ' - ξ by ring] at h
  exact h

/-- **Monotonicity at `m = 0`**: `blockCos · 0` is antitone on `[-1, log π - 1]`, where
`e^{v+1} ≤ π` and `cos` decreases on `[0, π]`. -/
theorem blockCos_antitoneOn :
    AntitoneOn (fun ξ => blockCos ξ 0) (Set.Icc (-1) (Real.log Real.pi - 1)) := by
  intro ξ hξ ξ' hξ' hle
  have h := blockCos_sub_eq ξ ξ' 0
  simp only [Nat.cast_zero, zero_add] at h
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v))
      MeasureTheory.volume ξ ξ' :=
    (by fun_prop : Continuous fun v : ℝ =>
      Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v)).intervalIntegrable _ _
  have hpt : ∀ v ∈ Set.Icc ξ ξ',
      Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v) ≤ (fun _ : ℝ => (0 : ℝ)) v := by
    intro v hv
    have hv1 : v + 1 ≤ Real.log Real.pi := by linarith [hv.2, hξ'.2]
    have he : Real.exp (v + 1) ≤ Real.pi := by
      calc Real.exp (v + 1) ≤ Real.exp (Real.log Real.pi) := Real.exp_le_exp.2 hv1
        _ = Real.pi := Real.exp_log Real.pi_pos
    have := Real.cos_le_cos_of_nonneg_of_le_pi (Real.exp_pos v).le he
      (Real.exp_le_exp.2 (by linarith))
    simp only
    linarith
  have hmono := intervalIntegral.integral_mono_on hle hint intervalIntegrable_const hpt
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hmono
  change blockCos ξ' 0 ≤ blockCos ξ 0
  linarith

/-! ### The first blocks numerically: Taylor below `e²`, asymptotics above -/

/-- `Re ∑_{m<2K} (wi)^m/m! = ∑_{k<K} (-1)^k w^{2k}/(2k)!`. -/
lemma re_sum_ofReal_mul_I_pow_eq (w : ℝ) (K : ℕ) :
    (∑ m ∈ Finset.range (2 * K), ((w : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re
      = ∑ k ∈ Finset.range K, (-1) ^ k * w ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : ((w : ℂ) * Complex.I) ^ (2 * K) = (((-1) ^ K * w ^ (2 * K) : ℝ) : ℂ) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
      push_cast
      ring
    have h2 : ((w : ℂ) * Complex.I) ^ (2 * K + 1)
        = (((-1) ^ K * w ^ (2 * K + 1) : ℝ) : ℂ) * Complex.I := by
      rw [pow_succ, h1]
      push_cast
      ring
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ _ (2 * K + 1),
      Finset.sum_range_succ _ (2 * K), Complex.add_re, Complex.add_re, ih,
      Finset.sum_range_succ _ K, h1, h2, Complex.div_natCast_re, Complex.div_natCast_re,
      Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, zero_div, add_zero]

/-- **Taylor's bound for the cosine**: `|cos w - ∑_{k<16} (-1)^k w^{2k}/(2k)!| ≤ 10⁻⁶` for
`0 ≤ w ≤ 8` (`Complex.exp_bound'` at `iw` with `32` terms). -/
lemma abs_cos_sub_taylor_le {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 8) :
    |Real.cos w - ∑ k ∈ Finset.range 16, (-1) ^ k * w ^ (2 * k) / ((2 * k).factorial : ℝ)|
      ≤ 1 / 10 ^ 6 := by
  have hx : ‖(w : ℂ) * Complex.I‖ = w := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw0]
  have hb := Complex.exp_bound' (x := (w : ℂ) * Complex.I) (n := 32)
    (by rw [hx]; norm_num; linarith)
  have hre : Real.cos w
        - ∑ k ∈ Finset.range 16, (-1) ^ k * w ^ (2 * k) / ((2 * k).factorial : ℝ)
      = (Complex.exp ((w : ℂ) * Complex.I)
          - ∑ m ∈ Finset.range 32, ((w : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, show (32 : ℕ) = 2 * 16 by norm_num,
      re_sum_ofReal_mul_I_pow_eq]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
  rw [hx]
  have hw32 : w ^ 32 ≤ 8 ^ 32 := pow_le_pow_left₀ hw0 hw 32
  calc w ^ 32 / ((32 : ℕ).factorial : ℝ) * 2 ≤ 8 ^ 32 / ((32 : ℕ).factorial : ℝ) * 2 := by
        gcongr
    _ ≤ 1 / 10 ^ 6 := by norm_num [Nat.factorial]

/-- **The antiderivative of the cosine's Taylor polynomial at `e^x`**:
`x + ∑_{k=1}^{15} (-1)^k e^{2kx}/(2k·(2k)!)`. -/
noncomputable def cosExpAnti (x : ℝ) : ℝ :=
  x + ∑ k ∈ Finset.range 15, (-1) ^ (k + 1) * Real.exp x ^ (2 * (k + 1))
    / ((2 * ((k : ℝ) + 1)) * ((2 * (k + 1)).factorial : ℝ))

/-- `cosExpAnti' x = ∑_{k<16} (-1)^k e^{2kx}/(2k)!`, the Taylor polynomial of `cos` at `e^x`. -/
lemma hasDerivAt_cosExpAnti (x : ℝ) :
    HasDerivAt cosExpAnti
      (∑ k ∈ Finset.range 16, (-1) ^ k * Real.exp x ^ (2 * k) / ((2 * k).factorial : ℝ)) x := by
  have hterm : ∀ k ∈ Finset.range 15, HasDerivAt
      (fun y => (-1 : ℝ) ^ (k + 1) * Real.exp y ^ (2 * (k + 1))
        / ((2 * ((k : ℝ) + 1)) * ((2 * (k + 1)).factorial : ℝ)))
      ((-1) ^ (k + 1) * Real.exp x ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)) x := by
    intro k _
    have h := (((Real.hasDerivAt_exp x).pow (2 * (k + 1))).const_mul
      ((-1 : ℝ) ^ (k + 1))).div_const ((2 * ((k : ℝ) + 1)) * ((2 * (k + 1)).factorial : ℝ))
    refine h.congr_deriv ?_
    have hf : ((2 * (k + 1)).factorial : ℝ) ≠ 0 := by positivity
    have hk : (2 * ((k : ℝ) + 1)) ≠ 0 := by positivity
    have hpow : Real.exp x ^ (2 * (k + 1)) = Real.exp x ^ (2 * (k + 1) - 1) * Real.exp x := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * (k + 1))]
    rw [hpow]
    push_cast
    field_simp
  have h := (hasDerivAt_id x).add (HasDerivAt.sum hterm)
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ' _ 15]
  simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  ring

/-- **The first blocks by Taylor's theorem**: for `a ≤ b ≤ 2`,
`|∫_a^b cos(e^v) dv - (cosExpAnti b - cosExpAnti a)| ≤ (b-a)/10⁶`. -/
theorem abs_integral_cos_exp_sub_cosExpAnti_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 2) :
    |(∫ v in a..b, Real.cos (Real.exp v)) - (cosExpAnti b - cosExpAnti a)|
      ≤ (b - a) / 10 ^ 6 := by
  set P : ℝ → ℝ := fun v =>
    ∑ k ∈ Finset.range 16, (-1) ^ k * Real.exp v ^ (2 * k) / ((2 * k).factorial : ℝ) with hP
  have hPc : Continuous P := continuous_finsetSum _ fun k _ => by fun_prop
  have hFTC : (∫ v in a..b, P v) = cosExpAnti b - cosExpAnti a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_cosExpAnti v)
      (hPc.intervalIntegrable a b)
  have hc0 : Continuous fun v : ℝ => Real.cos (Real.exp v) := by fun_prop
  rw [← hFTC, ← intervalIntegral.integral_sub (hc0.intervalIntegrable a b)
    (hPc.intervalIntegrable a b)]
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hbd : ∀ v ∈ Set.uIoc a b, ‖Real.cos (Real.exp v) - P v‖ ≤ 1 / 10 ^ 6 := by
    intro v hv
    rw [Set.uIoc_of_le hab] at hv
    rw [Real.norm_eq_abs]
    exact abs_cos_sub_taylor_le (Real.exp_pos v).le
      ((Real.exp_le_exp.2 (by linarith [hv.2])).trans he2)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at h
  linarith

/-- `cosExpAnti` in Horner form in `e^{2x}`, for interval arithmetic. -/
lemma cosExpAnti_eq_horner (x : ℝ) :
    cosExpAnti x =
      x + Real.exp (2 * x) * ((-1 / 4) + Real.exp (2 * x) * ((1 / 96) + Real.exp (2 * x) * ((-1 /
      4320) + Real.exp (2 * x) * ((1 / 322560) + Real.exp (2 * x) * ((-1 / 36288000) + Real.exp (2 *
      x) * ((1 / 5748019200) + Real.exp (2 * x) * ((-1 / 1220496076800) + Real.exp (2 * x) * ((1 /
      334764638208000) + Real.exp (2 * x) * ((-1 / 115242726703104000) + Real.exp (2 * x) * ((1 /
      48658040163532800000) + Real.exp (2 * x) * ((-1 / 24728016011107368960000) + Real.exp (2 * x)
      * ((1 / 14890761641597746544640000) + Real.exp (2 * x) * ((-1 / 10485577989291746525184000000)
      + Real.exp (2 * x) * ((1 / 8536873649127988094042112000000) + Real.exp (2 * x) * (-1 /
      7957585794365731759089254400000000))))))))))))))) := by
  have hy : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [← Real.exp_add]
    ring_nf
  rw [hy, cosExpAnti]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

/-- **The asymptotic antiderivative**
`Φ(v) = sin(e^v)(e^{-v} - 2e^{-3v}) - cos(e^v)(e^{-2v} - 6e^{-4v})`. -/
noncomputable def cosExpTail (v : ℝ) : ℝ :=
  Real.sin (Real.exp v) * (Real.exp (-v) - 2 * Real.exp (-(3 * v)))
    - Real.cos (Real.exp v) * (Real.exp (-(2 * v)) - 6 * Real.exp (-(4 * v)))

/-- `Φ'(v) = cos(e^v)(1 - 24e^{-4v})`. -/
lemma hasDerivAt_cosExpTail (v : ℝ) :
    HasDerivAt cosExpTail (Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v)))) v := by
  have hs := (Real.hasDerivAt_exp v).sin
  have hc := (Real.hasDerivAt_exp v).cos
  have he1 : HasDerivAt (fun y => Real.exp (-y)) (Real.exp (-v) * (-1)) v :=
    (hasDerivAt_neg' v).exp
  have he : ∀ c : ℝ, HasDerivAt (fun y => Real.exp (-(c * y))) (Real.exp (-(c * v)) * (-c)) v := by
    intro c
    have hl : HasDerivAt (fun y : ℝ => -(c * y)) (-c) v := by
      have h0 : HasDerivAt (-fun y : ℝ => c * y) (-c) v := by
        simpa using ((hasDerivAt_id v).const_mul c).neg
      exact h0
    exact hl.exp
  have h := (hs.mul (he1.sub ((he 3).const_mul 2))).sub
    (hc.mul ((he 2).sub ((he 4).const_mul 6)))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]
  have h1 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp v * Real.exp (-(2 * v)) = Real.exp (-v) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp v * Real.exp (-(3 * v)) = Real.exp (-(2 * v)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp v * Real.exp (-(4 * v)) = Real.exp (-(3 * v)) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination Real.cos (Real.exp v) * h1 - 2 * Real.cos (Real.exp v) * h3
    + Real.sin (Real.exp v) * h2 - 6 * Real.sin (Real.exp v) * h4

/-- **The first blocks by the asymptotic expansion**: for `a ≤ b`,
`|∫_a^b cos(e^v) dv - (Φ b - Φ a)| ≤ 6e^{-4a}`. -/
theorem abs_integral_cos_exp_sub_cosExpTail_le {a b : ℝ} (hab : a ≤ b) :
    |(∫ v in a..b, Real.cos (Real.exp v)) - (cosExpTail b - cosExpTail a)|
      ≤ 6 * Real.exp (-(4 * a)) := by
  have hc1 : Continuous fun v : ℝ => Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v))) := by
    fun_prop
  have hc0 : Continuous fun v : ℝ => Real.cos (Real.exp v) := by fun_prop
  have hFTC : (∫ v in a..b, Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v))))
      = cosExpTail b - cosExpTail a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_cosExpTail v)
      (hc1.intervalIntegrable a b)
  rw [← hFTC, ← intervalIntegral.integral_sub (hc0.intervalIntegrable a b)
    (hc1.intervalIntegrable a b)]
  have hmaj : Continuous fun v : ℝ => 24 * Real.exp (-(4 * v)) := by fun_prop
  have hpt : ∀ v ∈ Set.Icc a b,
      |Real.cos (Real.exp v) - Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v)))|
        ≤ 24 * Real.exp (-(4 * v)) := by
    intro v _
    rw [show Real.cos (Real.exp v) - Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v)))
        = 24 * Real.exp (-(4 * v)) * Real.cos (Real.exp v) by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 24 * Real.exp (-(4 * v)))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have hanti : (∫ v in a..b, 24 * Real.exp (-(4 * v)))
      = 6 * (Real.exp (-(4 * a)) - Real.exp (-(4 * b))) := by
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun v : ℝ => -(6 * Real.exp (-(4 * v)))) (24 * Real.exp (-(4 * x))) x := by
      intro x _
      have hl : HasDerivAt (fun y : ℝ => -(4 * y)) (-4) x := by
        have h0 : HasDerivAt (-fun y : ℝ => 4 * y) (-4) x := by
          simpa using ((hasDerivAt_id x).const_mul (4 : ℝ)).neg
        exact h0
      have h := (hl.exp.const_mul 6).neg
      refine h.congr_deriv ?_
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hmaj.intervalIntegrable a b)]
    ring
  calc |∫ v in a..b,
          (Real.cos (Real.exp v) - Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v))))|
      ≤ ∫ v in a..b,
          |Real.cos (Real.exp v) - Real.cos (Real.exp v) * (1 - 24 * Real.exp (-(4 * v)))| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ v in a..b, 24 * Real.exp (-(4 * v)) :=
        intervalIntegral.integral_mono_on hab ((hc0.sub hc1).abs.intervalIntegrable a b)
          (hmaj.intervalIntegrable a b) hpt
    _ = 6 * (Real.exp (-(4 * a)) - Real.exp (-(4 * b))) := hanti
    _ ≤ 6 * Real.exp (-(4 * a)) := by nlinarith [Real.exp_pos (-(4 * b))]

/-- `Φ` with `e^{-kv} = (e^v)^{-k}`, for interval arithmetic. -/
lemma cosExpTail_eq_inv (v : ℝ) :
    cosExpTail v = Real.sin (Real.exp v)
        * ((Real.exp v)⁻¹ * (1 - 2 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹)))
      - Real.cos (Real.exp v)
        * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹ * (1 - 6 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹))) := by
  have h1 : Real.exp (-v) = (Real.exp v)⁻¹ := Real.exp_neg v
  have hk : ∀ k : ℕ, Real.exp (-(k * v)) = (Real.exp v)⁻¹ ^ k := by
    intro k
    rw [← h1, ← Real.exp_nat_mul]
    ring_nf
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  push_cast at h2 h3 h4
  rw [cosExpTail, h1, h2, h3, h4]
  ring

/-- `Φ` at a phase reduced by `2nπ`, for interval arithmetic. -/
lemma cosExpTail_eq_turn_even (v N : ℝ) (n : ℕ) (hN : N = 2 * n) :
    cosExpTail v = Real.sin (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (1 - 2 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹)))
      - Real.cos (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹ * (1 - 6 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹))) := by
  rw [cosExpTail_eq_inv, hN, show Real.pi * (2 * (n : ℝ)) = n * (2 * Real.pi) by ring,
    Real.sin_sub_nat_mul_two_pi, Real.cos_sub_nat_mul_two_pi]

/-- `Φ` at a phase reduced by `(2n+1)π`, for interval arithmetic. -/
lemma cosExpTail_eq_turn_odd (v N : ℝ) (n : ℕ) (hN : N = 2 * n + 1) :
    cosExpTail v = -Real.sin (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (1 - 2 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹)))
      + Real.cos (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹ * (1 - 6 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹))) := by
  rw [cosExpTail_eq_inv, hN, show Real.exp v - Real.pi * (2 * (n : ℝ) + 1)
      = Real.exp v - Real.pi - n * (2 * Real.pi) by ring,
    Real.sin_sub_nat_mul_two_pi, Real.cos_sub_nat_mul_two_pi, Real.sin_sub_pi, Real.cos_sub_pi]
  ring

/-- `Φ` at a phase reduced by `(2n+1/2)π`, for interval arithmetic. -/
lemma cosExpTail_eq_turn_half (v N : ℝ) (n : ℕ) (hN : N = 2 * n + 1 / 2) :
    cosExpTail v = Real.cos (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (1 - 2 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹)))
      + Real.sin (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹ * (1 - 6 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹))) := by
  rw [cosExpTail_eq_inv, hN, show Real.exp v - Real.pi * (2 * (n : ℝ) + 1 / 2)
      = Real.exp v - Real.pi / 2 - n * (2 * Real.pi) by ring,
    Real.sin_sub_nat_mul_two_pi, Real.cos_sub_nat_mul_two_pi, Real.sin_sub_pi_div_two,
    Real.cos_sub_pi_div_two]
  ring

/-- `Φ` at a phase reduced by `(2n+3/2)π`, for interval arithmetic. -/
lemma cosExpTail_eq_turn_three_half (v N : ℝ) (n : ℕ) (hN : N = 2 * n + 3 / 2) :
    cosExpTail v = -Real.cos (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (1 - 2 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹)))
      - Real.sin (Real.exp v - Real.pi * N)
        * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹ * (1 - 6 * ((Real.exp v)⁻¹ * (Real.exp v)⁻¹))) := by
  rw [cosExpTail_eq_inv, hN, show Real.exp v - Real.pi * (2 * (n : ℝ) + 3 / 2)
      = Real.exp v - Real.pi - Real.pi / 2 - n * (2 * Real.pi) by ring,
    Real.sin_sub_nat_mul_two_pi, Real.cos_sub_nat_mul_two_pi, Real.sin_sub_pi_div_two,
    Real.cos_sub_pi_div_two, Real.sin_sub_pi, Real.cos_sub_pi]
  ring

/-- `blockCos a 0` is the unit integral from `a`. -/
lemma blockCos_zero_eq (a : ℝ) : blockCos a 0 = ∫ v in a..(a + 1), Real.cos (Real.exp v) := by
  rw [blockCos]
  congr 1 <;> push_cast <;> ring

/-- **`blockCos` below `e²`**: `|blockCos c 0 - (cosExpAnti (c+1) - cosExpAnti c)| ≤ 10⁻⁶` for
`c ≤ 1`. -/
lemma abs_blockCos_zero_sub_anti_le {c d : ℝ} (hd : d = c + 1) (hc : c ≤ 1) :
    |blockCos c 0 - (cosExpAnti d - cosExpAnti c)| ≤ 1 / 10 ^ 6 := by
  subst hd
  rw [blockCos_zero_eq]
  have h := abs_integral_cos_exp_sub_cosExpAnti_le (a := c) (b := c + 1) (by linarith)
    (by linarith)
  rwa [show c + 1 - c = (1 : ℝ) by ring] at h

/-- `6e^{-8} ≤ 1/400 - 10⁻⁶`. -/
lemma six_mul_exp_neg_eight_le : 6 * Real.exp (-8) ≤ 1 / 400 - 1 / 10 ^ 6 := by
  have h : (2900 : ℝ) ≤ Real.exp 8 := by interval_decide (trust := kernel)
  have hinv : Real.exp (-8) ≤ 1 / 2900 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h
  linarith

/-- **`blockCos` across `e²`**: split at `2`, Taylor below and the asymptotic expansion above,
within `1/400` for `1 ≤ c ≤ 2`. -/
lemma abs_blockCos_zero_sub_mixed_le {c d : ℝ} (hd : d = c + 1) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    |blockCos c 0 - (cosExpAnti 2 - cosExpAnti c + (cosExpTail d - cosExpTail 2))|
      ≤ 1 / 400 := by
  subst hd
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => Real.cos (Real.exp v))
      MeasureTheory.volume a b :=
    fun a b => (by fun_prop : Continuous fun v : ℝ => Real.cos (Real.exp v)).intervalIntegrable a b
  rw [blockCos_zero_eq, ← intervalIntegral.integral_add_adjacent_intervals (hi c 2) (hi 2 (c + 1))]
  have h1 := abs_integral_cos_exp_sub_cosExpAnti_le (a := c) (b := 2) hc2 le_rfl
  have h2 := abs_integral_cos_exp_sub_cosExpTail_le (a := 2) (b := c + 1) (by linarith)
  have he := six_mul_exp_neg_eight_le
  rw [show -(4 * (2 : ℝ)) = -8 by norm_num] at h2
  rw [abs_le] at h1 h2 ⊢
  have h3 : (2 - c) / 10 ^ 6 ≤ 1 / 10 ^ 6 := by
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    linarith
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **`blockCos` above `e²`**: `|blockCos c 0 - (Φ(c+1) - Φ c)| ≤ 1/400` for `c ≥ 2`. -/
lemma abs_blockCos_zero_sub_tail_le {c d : ℝ} (hd : d = c + 1) (hc : 2 ≤ c) :
    |blockCos c 0 - (cosExpTail d - cosExpTail c)| ≤ 1 / 400 := by
  subst hd
  rw [blockCos_zero_eq]
  have h := abs_integral_cos_exp_sub_cosExpTail_le (a := c) (b := c + 1) (by linarith)
  have he := six_mul_exp_neg_eight_le
  have hmono : Real.exp (-(4 * c)) ≤ Real.exp (-8) := Real.exp_le_exp.2 (by linarith)
  have h6 : 6 * Real.exp (-(4 * c)) ≤ 6 * Real.exp (-8) := by linarith
  linarith

attribute [local simp] LeanCert.Core.MathConst.toReal

/-- `cosExpAnti 2 ∈ [-0.46762, -0.46741]` and `cosExpTail 2 ∈ [0.10912, 0.10933]`, the
constant part of the certificates across `e²`. -/
lemma cosExpAnti_two_cosExpTail_two_mem :
    (-0.46762 ≤ cosExpAnti 2 ∧ cosExpAnti 2 ≤ -0.46741) ∧
      (0.10912 ≤ cosExpTail 2 ∧ cosExpTail 2 ≤ 0.10933) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  · simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  · rw [cosExpTail_eq_turn_even 2 2 1 (by norm_num)]
    interval_decide (trust := kernel)
  · rw [cosExpTail_eq_turn_even 2 2 1 (by norm_num)]
    interval_decide (trust := kernel)

/-- `blockCos (-1) 0 ∈ [0.793299, 0.794401]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_m80 :
    0.793299 ≤ blockCos (-1) 0 ∧ blockCos (-1) 0 ≤ 0.794401 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (-1)) (d := 0)
    (by norm_num) (by norm_num)
  have e1 : (0.7933 : ℝ) ≤ cosExpAnti 0 - cosExpAnti (-1) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti 0 - cosExpAnti (-1) ≤ (0.7944 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (-19 / 80) 0 ∈ [0.200999, 0.202101]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_m19 :
    0.200999 ≤ blockCos (-19 / 80) 0 ∧ blockCos (-19 / 80) 0 ≤ 0.202101 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (-19 / 80)) (d := (61 / 80))
    (by norm_num) (by norm_num)
  have e1 : (0.201 : ℝ) ≤ cosExpAnti (61 / 80) - cosExpAnti (-19 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (61 / 80) - cosExpAnti (-19 / 80) ≤ (0.2021 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos 0 0 ∈ [-0.124001, -0.122899]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_0 :
    -0.124001 ≤ blockCos 0 0 ∧ blockCos 0 0 ≤ -0.122899 := by
  have h := abs_blockCos_zero_sub_anti_le (c := 0) (d := 1)
    (by norm_num) (by norm_num)
  have e1 : (-0.124 : ℝ) ≤ cosExpAnti 1 - cosExpAnti 0 := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti 1 - cosExpAnti 0 ≤ (-0.1229 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (3 / 40) 0 ∈ [-0.233101, -0.231999]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_6 :
    -0.233101 ≤ blockCos (3 / 40) 0 ∧ blockCos (3 / 40) 0 ≤ -0.231999 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (3 / 40)) (d := (43 / 40))
    (by norm_num) (by norm_num)
  have e1 : (-0.2331 : ℝ) ≤ cosExpAnti (43 / 40) - cosExpAnti (3 / 40) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (43 / 40) - cosExpAnti (3 / 40) ≤ (-0.232 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (7 / 40) 0 ∈ [-0.374901, -0.373799]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_14 :
    -0.374901 ≤ blockCos (7 / 40) 0 ∧ blockCos (7 / 40) 0 ≤ -0.373799 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (7 / 40)) (d := (47 / 40))
    (by norm_num) (by norm_num)
  have e1 : (-0.3749 : ℝ) ≤ cosExpAnti (47 / 40) - cosExpAnti (7 / 40) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (47 / 40) - cosExpAnti (7 / 40) ≤ (-0.3738 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (31 / 80) 0 ∈ [-0.611201, -0.610099]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_31 :
    -0.611201 ≤ blockCos (31 / 80) 0 ∧ blockCos (31 / 80) 0 ≤ -0.610099 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (31 / 80)) (d := (111 / 80))
    (by norm_num) (by norm_num)
  have e1 : (-0.6112 : ℝ) ≤ cosExpAnti (111 / 80) - cosExpAnti (31 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (111 / 80) - cosExpAnti (31 / 80) ≤ (-0.6101 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (33 / 80) 0 ∈ [-0.628401, -0.627299]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_33 :
    -0.628401 ≤ blockCos (33 / 80) 0 ∧ blockCos (33 / 80) 0 ≤ -0.627299 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (33 / 80)) (d := (113 / 80))
    (by norm_num) (by norm_num)
  have e1 : (-0.6284 : ℝ) ≤ cosExpAnti (113 / 80) - cosExpAnti (33 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (113 / 80) - cosExpAnti (33 / 80) ≤ (-0.6273 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (39 / 80) 0 ∈ [-0.660901, -0.659799]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_39 :
    -0.660901 ≤ blockCos (39 / 80) 0 ∧ blockCos (39 / 80) 0 ≤ -0.659799 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (39 / 80)) (d := (119 / 80))
    (by norm_num) (by norm_num)
  have e1 : (-0.6609 : ℝ) ≤ cosExpAnti (119 / 80) - cosExpAnti (39 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (119 / 80) - cosExpAnti (39 / 80) ≤ (-0.6598 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (1 / 2) 0 ∈ [-0.663301, -0.662199]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_40 :
    -0.663301 ≤ blockCos (1 / 2) 0 ∧ blockCos (1 / 2) 0 ≤ -0.662199 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (1 / 2)) (d := (3 / 2))
    (by norm_num) (by norm_num)
  have e1 : (-0.6633 : ℝ) ≤ cosExpAnti (3 / 2) - cosExpAnti (1 / 2) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (3 / 2) - cosExpAnti (1 / 2) ≤ (-0.6622 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (9 / 16) 0 ∈ [-0.660601, -0.659499]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_45 :
    -0.660601 ≤ blockCos (9 / 16) 0 ∧ blockCos (9 / 16) 0 ≤ -0.659499 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (9 / 16)) (d := (25 / 16))
    (by norm_num) (by norm_num)
  have e1 : (-0.6606 : ℝ) ≤ cosExpAnti (25 / 16) - cosExpAnti (9 / 16) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (25 / 16) - cosExpAnti (9 / 16) ≤ (-0.6595 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (23 / 40) 0 ∈ [-0.657101, -0.655999]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_46 :
    -0.657101 ≤ blockCos (23 / 40) 0 ∧ blockCos (23 / 40) 0 ≤ -0.655999 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (23 / 40)) (d := (63 / 40))
    (by norm_num) (by norm_num)
  have e1 : (-0.6571 : ℝ) ≤ cosExpAnti (63 / 40) - cosExpAnti (23 / 40) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (63 / 40) - cosExpAnti (23 / 40) ≤ (-0.656 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (11 / 16) 0 ∈ [-0.579501, -0.578399]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_55 :
    -0.579501 ≤ blockCos (11 / 16) 0 ∧ blockCos (11 / 16) 0 ≤ -0.578399 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (11 / 16)) (d := (27 / 16))
    (by norm_num) (by norm_num)
  have e1 : (-0.5795 : ℝ) ≤ cosExpAnti (27 / 16) - cosExpAnti (11 / 16) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (27 / 16) - cosExpAnti (11 / 16) ≤ (-0.5784 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (57 / 80) 0 ∈ [-0.551601, -0.550499]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_57 :
    -0.551601 ≤ blockCos (57 / 80) 0 ∧ blockCos (57 / 80) 0 ≤ -0.550499 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (57 / 80)) (d := (137 / 80))
    (by norm_num) (by norm_num)
  have e1 : (-0.5516 : ℝ) ≤ cosExpAnti (137 / 80) - cosExpAnti (57 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (137 / 80) - cosExpAnti (57 / 80) ≤ (-0.5505 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (4 / 5) 0 ∈ [-0.428801, -0.427699]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_64 :
    -0.428801 ≤ blockCos (4 / 5) 0 ∧ blockCos (4 / 5) 0 ≤ -0.427699 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (4 / 5)) (d := (9 / 5))
    (by norm_num) (by norm_num)
  have e1 : (-0.4288 : ℝ) ≤ cosExpAnti (9 / 5) - cosExpAnti (4 / 5) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (9 / 5) - cosExpAnti (4 / 5) ≤ (-0.4277 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (73 / 80) 0 ∈ [-0.240201, -0.239099]`, certified from `RMF.cosExpAnti`. -/
theorem blockCos_zero_grid_73 :
    -0.240201 ≤ blockCos (73 / 80) 0 ∧ blockCos (73 / 80) 0 ≤ -0.239099 := by
  have h := abs_blockCos_zero_sub_anti_le (c := (73 / 80)) (d := (153 / 80))
    (by norm_num) (by norm_num)
  have e1 : (-0.2402 : ℝ) ≤ cosExpAnti (153 / 80) - cosExpAnti (73 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have e2 : cosExpAnti (153 / 80) - cosExpAnti (73 / 80) ≤ (-0.2391 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (43 / 40) 0 ∈ [-0.02335, -0.01653]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_86 :
    -0.02335 ≤ blockCos (43 / 40) 0 ∧ blockCos (43 / 40) 0 ≤ -0.01653 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (43 / 40)) (d := (83 / 40))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.4347 : ℝ) ≤ cosExpAnti (43 / 40) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (43 / 40) ≤ (-0.434 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (0.1221 : ℝ) ≤ cosExpTail (83 / 40) := by
    rw [cosExpTail_eq_turn_half (83 / 40) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (83 / 40) ≤ (0.1228 : ℝ) := by
    rw [cosExpTail_eq_turn_half (83 / 40) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (87 / 80) 0 ∈ [-0.01305, -0.00623]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_87 :
    -0.01305 ≤ blockCos (87 / 80) 0 ∧ blockCos (87 / 80) 0 ≤ -0.00623 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (87 / 80)) (d := (167 / 80))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.447 : ℝ) ≤ cosExpAnti (87 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (87 / 80) ≤ (-0.4463 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (0.1201 : ℝ) ≤ cosExpTail (167 / 80) := by
    rw [cosExpTail_eq_turn_half (167 / 80) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (167 / 80) ≤ (0.1208 : ℝ) := by
    rw [cosExpTail_eq_turn_half (167 / 80) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (103 / 80) 0 ∈ [0.02865, 0.03547]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_103 :
    0.02865 ≤ blockCos (103 / 80) 0 ∧ blockCos (103 / 80) 0 ≤ 0.03547 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (103 / 80)) (d := (183 / 80))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.6414 : ℝ) ≤ cosExpAnti (103 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (103 / 80) ≤ (-0.6407 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (-0.0326 : ℝ) ≤ cosExpTail (183 / 80) := by
    rw [cosExpTail_eq_turn_odd (183 / 80) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (183 / 80) ≤ (-0.0319 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (183 / 80) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (111 / 80) 0 ∈ [0.04995, 0.05677]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_111 :
    0.04995 ≤ blockCos (111 / 80) 0 ∧ blockCos (111 / 80) 0 ≤ 0.05677 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (111 / 80)) (d := (191 / 80))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.7193 : ℝ) ≤ cosExpAnti (111 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (111 / 80) ≤ (-0.7186 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (-0.0892 : ℝ) ≤ cosExpTail (191 / 80) := by
    rw [cosExpTail_eq_turn_odd (191 / 80) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (191 / 80) ≤ (-0.0885 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (191 / 80) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (119 / 80) 0 ∈ [0.13895, 0.14577]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_119 :
    0.13895 ≤ blockCos (119 / 80) 0 ∧ blockCos (119 / 80) 0 ≤ 0.14577 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (119 / 80)) (d := (199 / 80))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.767 : ℝ) ≤ cosExpAnti (119 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (119 / 80) ≤ (-0.7663 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (-0.0479 : ℝ) ≤ cosExpTail (199 / 80) := by
    rw [cosExpTail_eq_turn_three_half (199 / 80) (7 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (199 / 80) ≤ (-0.0472 : ℝ) := by
    rw [cosExpTail_eq_turn_three_half (199 / 80) (7 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (63 / 40) 0 ∈ [0.22955, 0.23637]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_126 :
    0.22955 ≤ blockCos (63 / 40) 0 ∧ blockCos (63 / 40) 0 ≤ 0.23637 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (63 / 40)) (d := (103 / 40))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.7745 : ℝ) ≤ cosExpAnti (63 / 40) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (63 / 40) ≤ (-0.7738 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (0.0352 : ℝ) ≤ cosExpTail (103 / 40) := by
    rw [cosExpTail_eq_turn_even (103 / 40) 4 2 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (103 / 40) ≤ (0.0359 : ℝ) := by
    rw [cosExpTail_eq_turn_even (103 / 40) 4 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (13 / 8) 0 ∈ [0.24815, 0.25497]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_130 :
    0.24815 ≤ blockCos (13 / 8) 0 ∧ blockCos (13 / 8) 0 ≤ 0.25497 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (13 / 8)) (d := (21 / 8))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.7626 : ℝ) ≤ cosExpAnti (13 / 8) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (13 / 8) ≤ (-0.7619 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (0.0657 : ℝ) ≤ cosExpTail (21 / 8) := by
    rw [cosExpTail_eq_turn_even (21 / 8) 4 2 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (21 / 8) ≤ (0.0664 : ℝ) := by
    rw [cosExpTail_eq_turn_even (21 / 8) 4 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (27 / 16) 0 ∈ [0.21035, 0.21717]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_135 :
    0.21035 ≤ blockCos (27 / 16) 0 ∧ blockCos (27 / 16) 0 ≤ 0.21717 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (27 / 16)) (d := (43 / 16))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.7313 : ℝ) ≤ cosExpAnti (27 / 16) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (27 / 16) ≤ (-0.7306 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (0.0592 : ℝ) ≤ cosExpTail (43 / 16) := by
    rw [cosExpTail_eq_turn_half (43 / 16) (9 / 2) 2 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (43 / 16) ≤ (0.0599 : ℝ) := by
    rw [cosExpTail_eq_turn_half (43 / 16) (9 / 2) 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (71 / 40) 0 ∈ [0.06455, 0.07137]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_142 :
    0.06455 ≤ blockCos (71 / 40) 0 ∧ blockCos (71 / 40) 0 ≤ 0.07137 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (71 / 40)) (d := (111 / 40))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.6615 : ℝ) ≤ cosExpAnti (71 / 40) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (71 / 40) ≤ (-0.6608 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (-0.0168 : ℝ) ≤ cosExpTail (111 / 40) := by
    rw [cosExpTail_eq_turn_odd (111 / 40) 5 2 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (111 / 40) ≤ (-0.0161 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (111 / 40) 5 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (9 / 5) 0 ∈ [0.01935, 0.02617]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_144 :
    0.01935 ≤ blockCos (9 / 5) 0 ∧ blockCos (9 / 5) 0 ≤ 0.02617 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (9 / 5)) (d := (14 / 5))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.6377 : ℝ) ≤ cosExpAnti (9 / 5) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (9 / 5) ≤ (-0.637 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (-0.0382 : ℝ) ≤ cosExpTail (14 / 5) := by
    rw [cosExpTail_eq_turn_odd (14 / 5) 5 2 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (14 / 5) ≤ (-0.0375 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (14 / 5) 5 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (157 / 80) 0 ∈ [-0.06935, -0.06253]`, certified from `RMF.cosExpAnti` and
`RMF.cosExpTail`. -/
theorem blockCos_zero_grid_157 :
    -0.06935 ≤ blockCos (157 / 80) 0 ∧ blockCos (157 / 80) 0 ≤ -0.06253 := by
  have h := abs_blockCos_zero_sub_mixed_le (c := (157 / 80)) (d := (237 / 80))
    (by norm_num) (by norm_num) (by norm_num)
  have hK := cosExpAnti_two_cosExpTail_two_mem
  have s1 : (-0.489 : ℝ) ≤ cosExpAnti (157 / 80) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have s2 : cosExpAnti (157 / 80) ≤ (-0.4883 : ℝ) := by
    simp only [cosExpAnti_eq_horner]
    interval_decide (trust := kernel)
  have p1 : (0.0218 : ℝ) ≤ cosExpTail (237 / 80) := by
    rw [cosExpTail_eq_turn_even (237 / 80) 6 3 (by norm_num)]
    interval_decide (trust := kernel)
  have p2 : cosExpTail (237 / 80) ≤ (0.0225 : ℝ) := by
    rw [cosExpTail_eq_turn_even (237 / 80) 6 3 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hK.1.1, hK.1.2, hK.2.1, hK.2.2]

/-- `blockCos (161 / 80) 0 ∈ [-0.0687, -0.0626]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_161 :
    -0.0687 ≤ blockCos (161 / 80) 0 ∧ blockCos (161 / 80) 0 ≤ -0.0626 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (161 / 80)) (d := (241 / 80))
    (by norm_num) (by norm_num)
  have e1 : (-0.0662 : ℝ) ≤ cosExpTail (241 / 80) - cosExpTail (161 / 80) := by
    rw [cosExpTail_eq_turn_even (241 / 80) 6 3 (by norm_num),
      cosExpTail_eq_turn_even (161 / 80) 2 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (241 / 80) - cosExpTail (161 / 80) ≤ (-0.0651 : ℝ) := by
    rw [cosExpTail_eq_turn_even (241 / 80) 6 3 (by norm_num),
      cosExpTail_eq_turn_even (161 / 80) 2 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (33 / 16) 0 ∈ [-0.0978, -0.0917]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_165 :
    -0.0978 ≤ blockCos (33 / 16) 0 ∧ blockCos (33 / 16) 0 ≤ -0.0917 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (33 / 16)) (d := (49 / 16))
    (by norm_num) (by norm_num)
  have e1 : (-0.0953 : ℝ) ≤ cosExpTail (49 / 16) - cosExpTail (33 / 16) := by
    rw [cosExpTail_eq_turn_half (49 / 16) (13 / 2) 3 (by norm_num),
      cosExpTail_eq_turn_even (33 / 16) 2 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (49 / 16) - cosExpTail (33 / 16) ≤ (-0.0942 : ℝ) := by
    rw [cosExpTail_eq_turn_half (49 / 16) (13 / 2) 3 (by norm_num),
      cosExpTail_eq_turn_even (33 / 16) 2 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (43 / 20) 0 ∈ [-0.137, -0.1309]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_172 :
    -0.137 ≤ blockCos (43 / 20) 0 ∧ blockCos (43 / 20) 0 ≤ -0.1309 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (43 / 20)) (d := (63 / 20))
    (by norm_num) (by norm_num)
  have e1 : (-0.1345 : ℝ) ≤ cosExpTail (63 / 20) - cosExpTail (43 / 20) := by
    rw [cosExpTail_eq_turn_odd (63 / 20) 7 3 (by norm_num),
      cosExpTail_eq_turn_half (43 / 20) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (63 / 20) - cosExpTail (43 / 20) ≤ (-0.1334 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (63 / 20) 7 3 (by norm_num),
      cosExpTail_eq_turn_half (43 / 20) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (89 / 40) 0 ∈ [-0.0325, -0.0264]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_178 :
    -0.0325 ≤ blockCos (89 / 40) 0 ∧ blockCos (89 / 40) 0 ≤ -0.0264 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (89 / 40)) (d := (129 / 40))
    (by norm_num) (by norm_num)
  have e1 : (-0.03 : ℝ) ≤ cosExpTail (129 / 40) - cosExpTail (89 / 40) := by
    rw [cosExpTail_eq_turn_three_half (129 / 40) (15 / 2) 3 (by norm_num),
      cosExpTail_eq_turn_half (89 / 40) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (129 / 40) - cosExpTail (89 / 40) ≤ (-0.0289 : ℝ) := by
    rw [cosExpTail_eq_turn_three_half (129 / 40) (15 / 2) 3 (by norm_num),
      cosExpTail_eq_turn_half (89 / 40) (5 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (23 / 10) 0 ∈ [0.0745, 0.0806]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_184 :
    0.0745 ≤ blockCos (23 / 10) 0 ∧ blockCos (23 / 10) 0 ≤ 0.0806 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (23 / 10)) (d := (33 / 10))
    (by norm_num) (by norm_num)
  have e1 : (0.077 : ℝ) ≤ cosExpTail (33 / 10) - cosExpTail (23 / 10) := by
    rw [cosExpTail_eq_turn_half (33 / 10) (17 / 2) 4 (by norm_num),
      cosExpTail_eq_turn_odd (23 / 10) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (33 / 10) - cosExpTail (23 / 10) ≤ (0.0781 : ℝ) := by
    rw [cosExpTail_eq_turn_half (33 / 10) (17 / 2) 4 (by norm_num),
      cosExpTail_eq_turn_odd (23 / 10) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (191 / 80) 0 ∈ [0.0535, 0.0596]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_191 :
    0.0535 ≤ blockCos (191 / 80) 0 ∧ blockCos (191 / 80) 0 ≤ 0.0596 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (191 / 80)) (d := (271 / 80))
    (by norm_num) (by norm_num)
  have e1 : (0.056 : ℝ) ≤ cosExpTail (271 / 80) - cosExpTail (191 / 80) := by
    rw [cosExpTail_eq_turn_odd (271 / 80) 9 4 (by norm_num),
      cosExpTail_eq_turn_odd (191 / 80) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (271 / 80) - cosExpTail (191 / 80) ≤ (0.0571 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (271 / 80) 9 4 (by norm_num),
      cosExpTail_eq_turn_odd (191 / 80) 3 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (101 / 40) 0 ∈ [0.0265, 0.0326]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_202 :
    0.0265 ≤ blockCos (101 / 40) 0 ∧ blockCos (101 / 40) 0 ≤ 0.0326 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (101 / 40)) (d := (141 / 40))
    (by norm_num) (by norm_num)
  have e1 : (0.029 : ℝ) ≤ cosExpTail (141 / 40) - cosExpTail (101 / 40) := by
    rw [cosExpTail_eq_turn_half (141 / 40) (21 / 2) 5 (by norm_num),
      cosExpTail_eq_turn_three_half (101 / 40) (7 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (141 / 40) - cosExpTail (101 / 40) ≤ (0.0301 : ℝ) := by
    rw [cosExpTail_eq_turn_half (141 / 40) (21 / 2) 5 (by norm_num),
      cosExpTail_eq_turn_three_half (101 / 40) (7 / 2) 1 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (51 / 20) 0 ∈ [-0.0222, -0.0161]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_204 :
    -0.0222 ≤ blockCos (51 / 20) 0 ∧ blockCos (51 / 20) 0 ≤ -0.0161 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (51 / 20)) (d := (71 / 20))
    (by norm_num) (by norm_num)
  have e1 : (-0.0197 : ℝ) ≤ cosExpTail (71 / 20) - cosExpTail (51 / 20) := by
    rw [cosExpTail_eq_turn_odd (71 / 20) 11 5 (by norm_num),
      cosExpTail_eq_turn_even (51 / 20) 4 2 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (71 / 20) - cosExpTail (51 / 20) ≤ (-0.0186 : ℝ) := by
    rw [cosExpTail_eq_turn_odd (71 / 20) 11 5 (by norm_num),
      cosExpTail_eq_turn_even (51 / 20) 4 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (11 / 4) 0 ∈ [-0.0346, -0.0285]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_220 :
    -0.0346 ≤ blockCos (11 / 4) 0 ∧ blockCos (11 / 4) 0 ≤ -0.0285 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (11 / 4)) (d := (15 / 4))
    (by norm_num) (by norm_num)
  have e1 : (-0.0321 : ℝ) ≤ cosExpTail (15 / 4) - cosExpTail (11 / 4) := by
    rw [cosExpTail_eq_turn_three_half (15 / 4) (27 / 2) 6 (by norm_num),
      cosExpTail_eq_turn_half (11 / 4) (9 / 2) 2 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (15 / 4) - cosExpTail (11 / 4) ≤ (-0.031 : ℝ) := by
    rw [cosExpTail_eq_turn_three_half (15 / 4) (27 / 2) 6 (by norm_num),
      cosExpTail_eq_turn_half (11 / 4) (9 / 2) 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (111 / 40) 0 ∈ [0.0044, 0.0105]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_222 :
    0.0044 ≤ blockCos (111 / 40) 0 ∧ blockCos (111 / 40) 0 ≤ 0.0105 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (111 / 40)) (d := (151 / 40))
    (by norm_num) (by norm_num)
  have e1 : (0.0069 : ℝ) ≤ cosExpTail (151 / 40) - cosExpTail (111 / 40) := by
    rw [cosExpTail_eq_turn_three_half (151 / 40) (27 / 2) 6 (by norm_num),
      cosExpTail_eq_turn_odd (111 / 40) 5 2 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (151 / 40) - cosExpTail (111 / 40) ≤ (0.008 : ℝ) := by
    rw [cosExpTail_eq_turn_three_half (151 / 40) (27 / 2) 6 (by norm_num),
      cosExpTail_eq_turn_odd (111 / 40) 5 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos (47 / 16) 0 ∈ [0.0152, 0.0213]`, certified from `RMF.cosExpTail`. -/
theorem blockCos_zero_grid_235 :
    0.0152 ≤ blockCos (47 / 16) 0 ∧ blockCos (47 / 16) 0 ≤ 0.0213 := by
  have h := abs_blockCos_zero_sub_tail_le (c := (47 / 16)) (d := (63 / 16))
    (by norm_num) (by norm_num)
  have e1 : (0.0177 : ℝ) ≤ cosExpTail (63 / 16) - cosExpTail (47 / 16) := by
    rw [cosExpTail_eq_turn_even (63 / 16) 16 8 (by norm_num),
      cosExpTail_eq_turn_three_half (47 / 16) (11 / 2) 2 (by norm_num)]
    interval_decide (trust := kernel)
  have e2 : cosExpTail (63 / 16) - cosExpTail (47 / 16) ≤ (0.0188 : ℝ) := by
    rw [cosExpTail_eq_turn_even (63 / 16) 16 8 (by norm_num),
      cosExpTail_eq_turn_three_half (47 / 16) (11 / 2) 2 (by norm_num)]
    interval_decide (trust := kernel)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `blockCos ξ m = blockCos (m + ξ) 0`: the block integral depends on `m + ξ` only. -/
lemma blockCos_eq_zero (ξ : ℝ) (m : ℕ) : blockCos ξ m = blockCos ((m : ℝ) + ξ) 0 := by
  simp only [blockCos, Nat.cast_zero, zero_add]
  congr 1
  ring

/-- **Interpolation**: a certified value at `c` bounds `blockCos a 0` on `[c - r, c + r]`, up to
the Lipschitz cost `2r` (`RMF.abs_blockCos_sub_le`). -/
lemma blockCos_zero_bounds_of_near {a c r lo hi L U : ℝ}
    (hc : lo ≤ blockCos c 0 ∧ blockCos c 0 ≤ hi) (h1 : c - r ≤ a) (h2 : a ≤ c + r)
    (hL : L ≤ lo - 2 * r) (hU : hi + 2 * r ≤ U) : L ≤ blockCos a 0 ∧ blockCos a 0 ≤ U := by
  have h := abs_blockCos_sub_le c a 0
  have ha : |a - c| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, hc.1, hc.2]

/-- **The first block at the one-point frequency**: `blockCos ξ 0 ∈ [-0.13, 0.8]` for
`ξ ∈ [-1, 0]`, by monotonicity (`RMF.blockCos_antitoneOn`) from the values at `-1` and `0`. -/
theorem blockCos_zero_bounds_one_point {ξ : ℝ} (h1 : -1 ≤ ξ) (h2 : ξ ≤ 0) :
    -0.13 ≤ blockCos ξ 0 ∧ blockCos ξ 0 ≤ 0.8 := by
  have hpi : (0 : ℝ) ≤ Real.log Real.pi - 1 := by
    have he : Real.exp 1 ≤ Real.pi := by linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rw [Real.log_exp] at h
    linarith
  have hmem : ξ ∈ Set.Icc (-1) (Real.log Real.pi - 1) := ⟨h1, by linarith⟩
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1) (Real.log Real.pi - 1) := ⟨le_rfl, by linarith⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (-1) (Real.log Real.pi - 1) := ⟨by norm_num, hpi⟩
  have hup : blockCos ξ 0 ≤ blockCos (-1) 0 := blockCos_antitoneOn hm1 hmem h1
  have hlo : blockCos 0 0 ≤ blockCos ξ 0 := blockCos_antitoneOn hmem h0 h2
  constructor <;> linarith [blockCos_zero_grid_m80.2, blockCos_zero_grid_0.1]

/-- **The block after the cut at the one-point frequency**: `blockCos ξ 1 ∈ [-0.75, 0]` for
`ξ ∈ [-1, 0]`. -/
theorem blockCos_one_bounds_one_point {ξ : ℝ} (h1 : -1 ≤ ξ) (h2 : ξ ≤ 0) :
    -0.75 ≤ blockCos ξ 1 ∧ blockCos ξ 1 ≤ 0 := by
  have hrw : blockCos ξ 1 = blockCos (1 + ξ) 0 := by
    rw [blockCos_eq_zero]
    norm_num
  rw [hrw]
  have ha1 : (0 : ℝ) ≤ 1 + ξ := by linarith
  have ha2 : 1 + ξ ≤ (1 : ℝ) := by linarith
  generalize (1 : ℝ) + ξ = a at ha1 ha2 ⊢
  rcases le_or_gt a (143 / 400) with hb0 | hb0
  · exact blockCos_zero_bounds_of_near (r := (73 / 400)) blockCos_zero_grid_14
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (47 / 100) with hb1 | hb1
  · exact blockCos_zero_bounds_of_near (r := (23 / 400)) blockCos_zero_grid_33
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (27 / 50) with hb2 | hb2
  · exact blockCos_zero_bounds_of_near (r := (1 / 25)) blockCos_zero_grid_40
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (247 / 400) with hb3 | hb3
  · exact blockCos_zero_bounds_of_near (r := (17 / 400)) blockCos_zero_grid_46
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (323 / 400) with hb4 | hb4
  · exact blockCos_zero_bounds_of_near (r := (19 / 200)) blockCos_zero_grid_57
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact blockCos_zero_bounds_of_near (r := (47 / 400)) blockCos_zero_grid_73
    (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- **The second block at the one-point frequency**: `blockCos ξ 2 ∈ [-0.2, 0.35]` for
`ξ ∈ [-1, 0]`. -/
theorem blockCos_two_bounds_one_point {ξ : ℝ} (h1 : -1 ≤ ξ) (h2 : ξ ≤ 0) :
    -0.2 ≤ blockCos ξ 2 ∧ blockCos ξ 2 ≤ 0.35 := by
  have hrw : blockCos ξ 2 = blockCos (2 + ξ) 0 := by
    rw [blockCos_eq_zero]
    norm_num
  rw [hrw]
  have ha1 : (1 : ℝ) ≤ 2 + ξ := by linarith
  have ha2 : 2 + ξ ≤ (2 : ℝ) := by linarith
  generalize (2 : ℝ) + ξ = a at ha1 ha2 ⊢
  rcases le_or_gt a (471 / 400) with hb0 | hb0
  · exact blockCos_zero_bounds_of_near (r := (9 / 100)) blockCos_zero_grid_87
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (559 / 400) with hb1 | hb1
  · exact blockCos_zero_bounds_of_near (r := (11 / 100)) blockCos_zero_grid_103
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (127 / 80) with hb2 | hb2
  · exact blockCos_zero_bounds_of_near (r := (1 / 10)) blockCos_zero_grid_119
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (167 / 100) with hb3 | hb3
  · exact blockCos_zero_bounds_of_near (r := (9 / 200)) blockCos_zero_grid_130
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (381 / 200) with hb4 | hb4
  · exact blockCos_zero_bounds_of_near (r := (13 / 100)) blockCos_zero_grid_142
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact blockCos_zero_bounds_of_near (r := (1 / 16)) blockCos_zero_grid_157
    (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- **The third block at the one-point frequency**: `blockCos ξ 3 ∈ [-0.25, 0.2]` for
`ξ ∈ [-1, 0]`. -/
theorem blockCos_three_bounds_one_point {ξ : ℝ} (h1 : -1 ≤ ξ) (h2 : ξ ≤ 0) :
    -0.25 ≤ blockCos ξ 3 ∧ blockCos ξ 3 ≤ 0.2 := by
  have hrw : blockCos ξ 3 = blockCos (3 + ξ) 0 := by
    rw [blockCos_eq_zero]
    norm_num
  rw [hrw]
  have ha1 : (2 : ℝ) ≤ 3 + ξ := by linarith
  have ha2 : 3 + ξ ≤ (3 : ℝ) := by linarith
  generalize (3 : ℝ) + ξ = a at ha1 ha2 ⊢
  rcases le_or_gt a (427 / 200) with hb0 | hb0
  · exact blockCos_zero_bounds_of_near (r := (29 / 400)) blockCos_zero_grid_165
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (233 / 100) with hb1 | hb1
  · exact blockCos_zero_bounds_of_near (r := (21 / 200)) blockCos_zero_grid_178
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (491 / 200) with hb2 | hb2
  · exact blockCos_zero_bounds_of_near (r := (27 / 400)) blockCos_zero_grid_191
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (531 / 200) with hb3 | hb3
  · exact blockCos_zero_bounds_of_near (r := (21 / 200)) blockCos_zero_grid_204
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (571 / 200) with hb4 | hb4
  · exact blockCos_zero_bounds_of_near (r := (21 / 200)) blockCos_zero_grid_220
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact blockCos_zero_bounds_of_near (r := (17 / 200)) blockCos_zero_grid_235
    (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- **The first block at the doubled frequency**: `blockCos ξ 0 ∈ [-0.75, 0.35]` for
`ξ ∈ [log 2 - 1, log 2]`. -/
theorem blockCos_zero_bounds_doubled {ξ : ℝ} (h1 : Real.log 2 - 1 ≤ ξ) (h2 : ξ ≤ Real.log 2) :
    -0.75 ≤ blockCos ξ 0 ∧ blockCos ξ 0 ≤ 0.35 := by
  have ha1 : (0 - 0.3068528197 : ℝ) ≤ ξ := by linarith [Real.log_two_gt_d9]
  have ha2 : ξ ≤ (0 + 0.6931471808 : ℝ) := by linarith [Real.log_two_lt_d9]
  rcases le_or_gt ξ (-67 / 400) with hb0 | hb0
  · exact blockCos_zero_bounds_of_near (r := (7 / 100)) blockCos_zero_grid_m19
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ξ (33 / 100) with hb1 | hb1
  · exact blockCos_zero_bounds_of_near (r := (51 / 200)) blockCos_zero_grid_6
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ξ (181 / 400) with hb2 | hb2
  · exact blockCos_zero_bounds_of_near (r := (13 / 200)) blockCos_zero_grid_31
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ξ (53 / 100) with hb3 | hb3
  · exact blockCos_zero_bounds_of_near (r := (17 / 400)) blockCos_zero_grid_39
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt ξ (121 / 200) with hb4 | hb4
  · exact blockCos_zero_bounds_of_near (r := (17 / 400)) blockCos_zero_grid_45
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact blockCos_zero_bounds_of_near (r := (33 / 400)) blockCos_zero_grid_55
    (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- **The block after the cut at the doubled frequency**: `blockCos ξ 1 ∈ [-0.65, 0.35]` for
`ξ ∈ [log 2 - 1, log 2]`. -/
theorem blockCos_one_bounds_doubled {ξ : ℝ} (h1 : Real.log 2 - 1 ≤ ξ) (h2 : ξ ≤ Real.log 2) :
    -0.65 ≤ blockCos ξ 1 ∧ blockCos ξ 1 ≤ 0.35 := by
  have hrw : blockCos ξ 1 = blockCos (1 + ξ) 0 := by
    rw [blockCos_eq_zero]
    norm_num
  rw [hrw]
  have ha1 : (1 - 0.3068528197 : ℝ) ≤ 1 + ξ := by linarith [Real.log_two_gt_d9]
  have ha2 : 1 + ξ ≤ (1 + 0.6931471808 : ℝ) := by linarith [Real.log_two_lt_d9]
  generalize (1 : ℝ) + ξ = a at ha1 ha2 ⊢
  rcases le_or_gt a (363 / 400) with hb0 | hb0
  · exact blockCos_zero_bounds_of_near (r := (43 / 400)) blockCos_zero_grid_64
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (251 / 200) with hb1 | hb1
  · exact blockCos_zero_bounds_of_near (r := (9 / 50)) blockCos_zero_grid_86
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (153 / 100) with hb2 | hb2
  · exact blockCos_zero_bounds_of_near (r := (57 / 400)) blockCos_zero_grid_111
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (651 / 400) with hb3 | hb3
  · exact blockCos_zero_bounds_of_near (r := (21 / 400)) blockCos_zero_grid_126
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact blockCos_zero_bounds_of_near (r := (1 / 16)) blockCos_zero_grid_135
    (by linarith) (by linarith) (by norm_num) (by norm_num)

/-- **The second block at the doubled frequency**: `blockCos ξ 2 ∈ [-0.25, 0.3]` for
`ξ ∈ [log 2 - 1, log 2]`. -/
theorem blockCos_two_bounds_doubled {ξ : ℝ} (h1 : Real.log 2 - 1 ≤ ξ) (h2 : ξ ≤ Real.log 2) :
    -0.25 ≤ blockCos ξ 2 ∧ blockCos ξ 2 ≤ 0.3 := by
  have hrw : blockCos ξ 2 = blockCos (2 + ξ) 0 := by
    rw [blockCos_eq_zero]
    norm_num
  rw [hrw]
  have ha1 : (2 - 0.3068528197 : ℝ) ≤ 2 + ξ := by linarith [Real.log_two_gt_d9]
  have ha2 : 2 + ξ ≤ (2 + 0.6931471808 : ℝ) := by linarith [Real.log_two_lt_d9]
  generalize (2 : ℝ) + ξ = a at ha1 ha2 ⊢
  rcases le_or_gt a (773 / 400) with hb0 | hb0
  · exact blockCos_zero_bounds_of_near (r := (53 / 400)) blockCos_zero_grid_144
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (21 / 10) with hb1 | hb1
  · exact blockCos_zero_bounds_of_near (r := (7 / 80)) blockCos_zero_grid_161
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (881 / 400) with hb2 | hb2
  · exact blockCos_zero_bounds_of_near (r := (21 / 400)) blockCos_zero_grid_172
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (963 / 400) with hb3 | hb3
  · exact blockCos_zero_bounds_of_near (r := (43 / 400)) blockCos_zero_grid_184
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  rcases le_or_gt a (531 / 200) with hb4 | hb4
  · exact blockCos_zero_bounds_of_near (r := (13 / 100)) blockCos_zero_grid_202
      (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact blockCos_zero_bounds_of_near (r := (1 / 8)) blockCos_zero_grid_222
    (by linarith) (by linarith) (by norm_num) (by norm_num)

end RMF
