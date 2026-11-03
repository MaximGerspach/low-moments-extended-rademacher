/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowNum

/-!
# HP2's window integral with the rest: Taylor bounds and the exponential integral

Elementary bounds behind the rest's damped cosine integrals
(`RMF/UniformLower/HP2WindowExt/Lobe.lean`).

* **Alternating Taylor bounds** for `e^{-s}`, `s ≥ 0`:
  `(-1)^n(e^{-s} - ∑_{i<n}(-s)^i/i!) ≥ 0` (`RMF.exp_neg_taylor_alt`); and
  `cos x ≤ 1 - x²/2 + x⁴/24` (`RMF.cos_le_quartic`).
* **The exponential integral** `∫_{x₁}^{x₂} e^{-s}/s ds`, `0 < x₁ ≤ x₂`: at most
  `log x₂ - log x₁ + ∑_{i=1}^{2K}(-1)^i(x₂^i - x₁^i)/(i·i!)` (`RMF.integral_exp_neg_div_le_ein`),
  at most `e^{-x₁}(log(x₁ + 1) - log x₁)` (`RMF.integral_exp_neg_div_le_tail`), and both at once
  past a cut `x_c` (`RMF.integral_exp_neg_div_le_sat`).
-/

open MeasureTheory Real

namespace RMF

/-! ### Alternating Taylor bounds -/

/-- The Taylor polynomial `∑_{i<n}(-s)^i/i!` of `e^{-s}`. -/
noncomputable def expNegPoly (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-s) ^ i / (i.factorial : ℝ)

lemma expNegPoly_succ (n : ℕ) (s : ℝ) :
    expNegPoly (n + 1) s = expNegPoly n s + (-s) ^ n / (n.factorial : ℝ) := by
  simp only [expNegPoly, Finset.sum_range_succ]

/-- `(∑_{i<n+1}(-s)^i/i!)' = -∑_{i<n}(-s)^i/i!`. -/
lemma hasDerivAt_expNegPoly (n : ℕ) (s : ℝ) :
    HasDerivAt (expNegPoly (n + 1)) (-expNegPoly n s) s := by
  induction n with
  | zero =>
    have e : expNegPoly (0 + 1) = fun _ => (1 : ℝ) := by
      funext x
      simp [expNegPoly]
    rw [e]
    simpa [expNegPoly] using hasDerivAt_const s (1 : ℝ)
  | succ n ih =>
    have e : expNegPoly (n + 1 + 1)
        = fun x => expNegPoly (n + 1) x + (-x) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      funext x
      exact expNegPoly_succ (n + 1) x
    rw [e]
    have h2 : HasDerivAt (fun x : ℝ => (-x) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (-((-s) ^ n / (n.factorial : ℝ))) s := by
      have h := ((hasDerivAt_neg s).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      refine h.congr_deriv ?_
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    refine (ih.add h2).congr_deriv ?_
    rw [expNegPoly_succ]
    ring

/-- `∑_{i<n+1}(-0)^i/i! = 1`. -/
lemma expNegPoly_zero (n : ℕ) : expNegPoly (n + 1) 0 = 1 := by
  induction n with
  | zero => simp [expNegPoly]
  | succ n ih => rw [expNegPoly_succ, ih]; simp

/-- **Alternating Taylor bounds for `e^{-s}`**: `(-1)^n(e^{-s} - ∑_{i<n}(-s)^i/i!) ≥ 0` for
`s ≥ 0` — the remainder's derivative is the previous remainder with the other sign. -/
theorem exp_neg_taylor_alt (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (-1) ^ n * (Real.exp (-s) - expNegPoly n s) := by
  induction n generalizing s with
  | zero => simp [expNegPoly, (Real.exp_pos _).le]
  | succ n ih =>
    set f : ℝ → ℝ := fun x => (-1) ^ (n + 1) * (Real.exp (-x) - expNegPoly (n + 1) x) with hf
    have hd : ∀ x, HasDerivAt f ((-1) ^ n * (Real.exp (-x) - expNegPoly n x)) x := by
      intro x
      have h1 : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-x)) x := by
        simpa using (hasDerivAt_neg x).exp
      have h := (h1.sub (hasDerivAt_expNegPoly n x)).const_mul ((-1 : ℝ) ^ (n + 1))
      refine h.congr_deriv ?_
      ring
    have hmono : MonotoneOn f (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact ih (le_of_lt hx)
    have h0 : f 0 = 0 := by
      simp only [hf, neg_zero, Real.exp_zero, expNegPoly_zero, sub_self, mul_zero]
    have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
    rw [h0] at h
    exact h

/-- `e^{-s} ≤ ∑_{i≤2K}(-s)^i/i!` for `s ≥ 0`. -/
lemma exp_neg_le_expNegPoly (K : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s) ≤ expNegPoly (2 * K + 1) s := by
  have h := exp_neg_taylor_alt (2 * K + 1) hs
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at h
  linarith

/-- `e^{-x} ≤ 1 - x + x²/2` for `x ≥ 0`. -/
lemma exp_neg_le_quad {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h := exp_neg_le_expNegPoly 1 hx
  simp only [expNegPoly, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for every real `x` (`sin y ≥ y - y³/6` for `y ≥ 0`, integrated). -/
theorem cos_le_quartic (x : ℝ) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
    intro y hy
    set f : ℝ → ℝ := fun z => 1 - z ^ 2 / 2 + z ^ 4 / 24 - Real.cos z with hf
    have hd : ∀ z, HasDerivAt f (-z + z ^ 3 / 6 + Real.sin z) z := by
      intro z
      have h := (((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_pow 2 z).div_const 2)).add
        ((hasDerivAt_pow 4 z).div_const 24)).sub (Real.hasDerivAt_cos z)
      refine h.congr_deriv ?_
      push_cast
      ring
    have hmono : MonotoneOn f (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun z _ => (hd z).continuousAt.continuousWithinAt)
        (fun z _ => (hd z).differentiableAt.differentiableWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      rw [(hd z).deriv]
      have := Real.sin_ge_sub_cube (le_of_lt hz)
      linarith
    have h0 : f 0 = 0 := by simp [hf]
    have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
    rw [h0] at h
    simp only [hf] at h
    linarith
  rcases le_total 0 x with h | h
  · exact key x h
  · have := key (-x) (by linarith)
    rw [Real.cos_neg] at this
    have e2 : (-x) ^ 2 = x ^ 2 := by ring
    have e4 : (-x) ^ 4 = x ^ 4 := by ring
    rw [e2, e4] at this
    exact this

/-! ### The exponential integral -/

/-- `∑_{i<n}(-1)^{i+1}x^{i+1}/((i+1)·(i+1)!)`, the polynomial part of the Taylor antiderivative of
`e^{-s}/s`. -/
noncomputable def einPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1) ^ (i + 1) * x ^ (i + 1) / (((i + 1 : ℕ) : ℝ) * ((i + 1).factorial : ℝ))

/-- `einPoly' = ∑_{i<n}(-1)^{i+1}x^i/(i+1)!`. -/
lemma hasDerivAt_einPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (einPoly n)
      (∑ i ∈ Finset.range n, (-1) ^ (i + 1) * x ^ i / ((i + 1).factorial : ℝ)) x := by
  have hterm : ∀ i ∈ Finset.range n, HasDerivAt
      (fun y : ℝ => (-1) ^ (i + 1) * y ^ (i + 1) / (((i + 1 : ℕ) : ℝ) * ((i + 1).factorial : ℝ)))
      ((-1) ^ (i + 1) * x ^ i / ((i + 1).factorial : ℝ)) x := by
    intro i _
    have h := ((hasDerivAt_pow (i + 1) x).const_mul ((-1 : ℝ) ^ (i + 1))).div_const
      (((i + 1 : ℕ) : ℝ) * ((i + 1).factorial : ℝ))
    refine h.congr_deriv ?_
    have hi : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hf : ((i + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]
    field_simp
  exact HasDerivAt.fun_sum hterm

/-- `e^{-s}/s ≤ 1/s + ∑_{i<2K}(-1)^{i+1}s^i/(i+1)!` for `s > 0`. -/
lemma exp_neg_div_le_ein (K : ℕ) {s : ℝ} (hs : 0 < s) :
    Real.exp (-s) / s
      ≤ s⁻¹ + ∑ i ∈ Finset.range (2 * K), (-1) ^ (i + 1) * s ^ i / ((i + 1).factorial : ℝ) := by
  have h := exp_neg_le_expNegPoly K hs.le
  have hP : expNegPoly (2 * K + 1) s
      = 1 + s * ∑ i ∈ Finset.range (2 * K), (-1) ^ (i + 1) * s ^ i / ((i + 1).factorial : ℝ) := by
    rw [expNegPoly, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow, pow_succ s i]
    ring
  rw [hP] at h
  rw [div_le_iff₀ hs]
  have e : (s⁻¹ + ∑ i ∈ Finset.range (2 * K), (-1) ^ (i + 1) * s ^ i
      / ((i + 1).factorial : ℝ)) * s
      = 1 + s * ∑ i ∈ Finset.range (2 * K), (-1) ^ (i + 1) * s ^ i
        / ((i + 1).factorial : ℝ) := by
    field_simp
  rw [e]
  exact h

/-- `s ↦ e^{-s}/s` is interval integrable on `[x₁, x₂]`, `0 < x₁ ≤ x₂`. -/
lemma intervalIntegrable_exp_neg_div {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) :
    IntervalIntegrable (fun s : ℝ => Real.exp (-s) / s) volume x₁ x₂ := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (by fun_prop) continuousOn_id fun s hs => ?_
  rw [Set.uIcc_of_le hx] at hs
  exact (hx₁.trans_le hs.1).ne'

/-- **The exponential integral by Taylor's polynomial**: for `0 < x₁ ≤ x₂`,
`∫_{x₁}^{x₂} e^{-s}/s ds ≤ log x₂ - log x₁ + einPoly (2K) x₂ - einPoly (2K) x₁`. -/
theorem integral_exp_neg_div_le_ein (K : ℕ) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) :
    ∫ s in x₁..x₂, Real.exp (-s) / s
      ≤ Real.log x₂ - Real.log x₁ + einPoly (2 * K) x₂ - einPoly (2 * K) x₁ := by
  have hpos : ∀ s ∈ Set.uIcc x₁ x₂, 0 < s := fun s hs => by
    rw [Set.uIcc_of_le hx] at hs
    exact hx₁.trans_le hs.1
  set g : ℝ → ℝ := fun s =>
    s⁻¹ + ∑ i ∈ Finset.range (2 * K), (-1) ^ (i + 1) * s ^ i / ((i + 1).factorial : ℝ) with hg
  have hgc : ContinuousOn g (Set.uIcc x₁ x₂) := by
    refine ContinuousOn.add (continuousOn_inv₀.mono fun s hs => (hpos s hs).ne') ?_
    exact (continuous_finsetSum _ fun i _ => by fun_prop).continuousOn
  have hd : ∀ s ∈ Set.uIcc x₁ x₂, HasDerivAt (fun s => Real.log s + einPoly (2 * K) s) (g s) s :=
    fun s hs => (Real.hasDerivAt_log (hpos s hs).ne').add (hasDerivAt_einPoly (2 * K) s)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hgc.intervalIntegrable
  have hle : ∫ s in x₁..x₂, Real.exp (-s) / s ≤ ∫ s in x₁..x₂, g s :=
    intervalIntegral.integral_mono_on hx (intervalIntegrable_exp_neg_div hx₁ hx)
      hgc.intervalIntegrable fun s hs => exp_neg_div_le_ein K (hx₁.trans_le hs.1)
  rw [hFTC] at hle
  linarith

/-- **The exponential integral's tail**: for `0 < x₁ ≤ x₂`,
`∫_{x₁}^{x₂} e^{-s}/s ds ≤ e^{-x₁}(log(x₁ + 1) - log x₁)` — the antiderivative
`-e^{-s}(log(s + 1) - log s)` has derivative at least `e^{-s}/s`, as `log(1 + 1/s) ≥ 1/(s + 1)`. -/
theorem integral_exp_neg_div_le_tail {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) :
    ∫ s in x₁..x₂, Real.exp (-s) / s
      ≤ Real.exp (-x₁) * (Real.log (x₁ + 1) - Real.log x₁) := by
  have hpos : ∀ s ∈ Set.uIcc x₁ x₂, 0 < s := fun s hs => by
    rw [Set.uIcc_of_le hx] at hs
    exact hx₁.trans_le hs.1
  set φ : ℝ → ℝ := fun s => -(Real.exp (-s) * (Real.log (s + 1) - Real.log s)) with hφ
  set φ' : ℝ → ℝ := fun s =>
    Real.exp (-s) * (Real.log (s + 1) - Real.log s) + Real.exp (-s) * (1 / (s * (s + 1)))
    with hφ'
  have hd : ∀ s ∈ Set.uIcc x₁ x₂, HasDerivAt φ (φ' s) s := by
    intro s hs
    have hs0 := hpos s hs
    have h1 : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-s)) s := by
      simpa using (hasDerivAt_neg s).exp
    have h2 : HasDerivAt (fun s => Real.log (s + 1)) (1 / (s + 1)) s := by
      have := ((hasDerivAt_id s).add_const 1).log (by positivity)
      simpa using this
    have h3 : HasDerivAt Real.log (1 / s) s := by
      simpa using Real.hasDerivAt_log hs0.ne'
    have h := (h1.mul (h2.sub h3)).neg
    refine h.congr_deriv ?_
    simp only [hφ', Pi.sub_apply]
    field_simp
    ring
  have hφ'c : ContinuousOn φ' (Set.uIcc x₁ x₂) := by
    have hl1 : ContinuousOn (fun s : ℝ => Real.log (s + 1)) (Set.uIcc x₁ x₂) :=
      ContinuousOn.log (by fun_prop) fun s hs => by linarith [hpos s hs]
    have hl2 : ContinuousOn Real.log (Set.uIcc x₁ x₂) :=
      Real.continuousOn_log.mono fun s hs => (hpos s hs).ne'
    refine ContinuousOn.add ((by fun_prop : Continuous fun s : ℝ => Real.exp (-s)).continuousOn.mul
      (hl1.sub hl2)) ((by fun_prop : Continuous fun s : ℝ => Real.exp (-s)).continuousOn.mul ?_)
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun s hs => ?_
    have := hpos s hs
    positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hφ'c.intervalIntegrable
  have hle : ∫ s in x₁..x₂, Real.exp (-s) / s ≤ ∫ s in x₁..x₂, φ' s := by
    refine intervalIntegral.integral_mono_on hx (intervalIntegrable_exp_neg_div hx₁ hx)
      hφ'c.intervalIntegrable fun s hs => ?_
    have hs0 : 0 < s := hx₁.trans_le hs.1
    have hlog : 1 / (s + 1) ≤ Real.log (s + 1) - Real.log s := by
      rw [← Real.log_div (by positivity) hs0.ne']
      have h := Real.one_sub_inv_le_log_of_pos (show 0 < (s + 1) / s by positivity)
      have e : 1 - ((s + 1) / s)⁻¹ = 1 / (s + 1) := by field_simp; ring
      linarith
    have he := Real.exp_pos (-s)
    simp only [hφ']
    have e : Real.exp (-s) / s
        = Real.exp (-s) * (1 / (s + 1)) + Real.exp (-s) * (1 / (s * (s + 1))) := by
      field_simp
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left hlog he.le) le_rfl
  rw [hFTC] at hle
  have hend : 0 ≤ Real.exp (-x₂) * (Real.log (x₂ + 1) - Real.log x₂) := by
    have hx₂ : 0 < x₂ := hx₁.trans_le hx
    have : Real.log x₂ ≤ Real.log (x₂ + 1) := Real.log_le_log hx₂ (by linarith)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  simp only [hφ] at hle
  linarith

/-- **The exponential integral, uniformly in its end**: for `0 < x₁ ≤ x_c` and `x₂ ≥ x₁`,
`∫_{x₁}^{x₂} e^{-s}/s ds ≤ log x_c - log x₁ + einPoly (2K) x_c - einPoly (2K) x₁
  + e^{-x_c}(log(x_c + 1) - log x_c)` (Taylor up to the cut, the tail bound past it). -/
theorem integral_exp_neg_div_le_sat (K : ℕ) {x₁ xc x₂ : ℝ} (hx₁ : 0 < x₁) (hxc : x₁ ≤ xc)
    (hx : x₁ ≤ x₂) :
    ∫ s in x₁..x₂, Real.exp (-s) / s
      ≤ Real.log xc - Real.log x₁ + einPoly (2 * K) xc - einPoly (2 * K) x₁
        + Real.exp (-xc) * (Real.log (xc + 1) - Real.log xc) := by
  have hxc0 : 0 < xc := hx₁.trans_le hxc
  have htail0 : 0 ≤ Real.exp (-xc) * (Real.log (xc + 1) - Real.log xc) := by
    have : Real.log xc ≤ Real.log (xc + 1) := Real.log_le_log hxc0 (by linarith)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hE := integral_exp_neg_div_le_ein K hx₁ hxc
  rcases le_total x₂ xc with h | h
  · -- the integrand is positive: extend to the cut
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_neg_div hx₁ hx) (intervalIntegrable_exp_neg_div (hx₁.trans_le hx) h)
    have hnn : 0 ≤ ∫ s in x₂..xc, Real.exp (-s) / s :=
      intervalIntegral.integral_nonneg h fun s hs => by
        have : 0 < s := (hx₁.trans_le hx).trans_le hs.1
        positivity
    linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_neg_div hx₁ hxc) (intervalIntegrable_exp_neg_div hxc0 h)
    have hT := integral_exp_neg_div_le_tail hxc0 h
    linarith

end RMF
