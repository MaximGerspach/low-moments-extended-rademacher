/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LevelAboveHalfExplicit
import RMF.Weighted.ThetaWindowExplicit

/-!
# The pieces of a level above `q = ½`, in closed form

Closed-form bounds for the pieces of `RMF.integral_rpow_norm_blockTruncationTail_le_split`, in the
variables the certificate works in.

* **the windows** without a split (`RMF.window_band_le_nosplit_explicit`) and by the split and
  Jensen (`RMF.window_band_le_split_explicit`), with (PF) and Mertens in closed form;
* **the central window** (`RMF.setIntegral_inv_mul_diffQ_le`):
  `∫_{-τ}^{τ}(σ²+t²)⁻¹Q(σ,t)dt ≤ 2τ·a²(1+e^{a(τ+σ)})²/4
    + K₂e^{4(1-q)σK₃}(2τ + (2τ/3)(e^{2(1-q)K₂τ²} - 1))`,
  from `e^x - 1 ≤ x(1+e^x)/2` (`RMF.exp_sub_one_le_mul_one_add_exp_div_two`) and the chord of
  `s ↦ e^{cs}` on `[0, τ²]`, with `a ≥ (2q-1)K₁` and the prime sums `K₁, K₂, K₃` bounded by
  Mertens' first theorem (`RMF.diffK₁_le`, `RMF.diffK₃_le`) and `RMF.sum_log_sq_mul_primesIco_le`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The prime sums of `Q` -/

/-- `∑_{p<y₁} log p/p ≤ log y₁ + log 4 + 4` over any band `[y₀, y₁)`. -/
lemma sum_log_div_primesIco_le_log (y₀ y₁ : ℕ) :
    ∑ p ∈ primesIco y₀ y₁, Real.log p / p ≤ Real.log y₁ + Real.log 4 + 4 := by
  classical
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge y₁ 2 with hy | hy
  · have hempty : primesIco y₀ y₁ = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      obtain ⟨hprime, -, hlt⟩ := mem_primesIco.1 hp
      have := hprime.two_le
      omega
    rw [hempty, Finset.sum_empty]
    have := Real.log_natCast_nonneg y₁
    linarith
  obtain ⟨N, rfl⟩ : ∃ N, y₁ = N + 1 := ⟨y₁ - 1, by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hsub : primesIco y₀ (N + 1) ⊆ Nat.primesBelow (N + 1) := by
    intro p hp
    obtain ⟨hprime, -, hlt⟩ := mem_primesIco.1 hp
    exact Nat.mem_primesBelow.2 ⟨hlt, hprime⟩
  have hnn : ∀ p ∈ Nat.primesBelow (N + 1), p ∉ primesIco y₀ (N + 1) →
      (0 : ℝ) ≤ Real.log p / p := fun p _ _ => by
    have := Real.log_natCast_nonneg p
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
  refine le_trans (sum_log_div_primesBelow_le hN1) ?_
  have hmono : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast Nat.le_succ N)
  linarith

/-- `K₁ ≤ (1 + (2-2q)/3)(log y₁ + log 4 + 4)` for `q ≤ 1`: `1/p² ≤ 1/(2p)`. -/
lemma diffK₁_le (y₀ y₁ : ℕ) {q : ℝ} (hq1 : q ≤ 1) :
    diffK₁ y₀ y₁ q ≤ (1 + (2 - 2 * q) / 3) * (Real.log y₁ + Real.log 4 + 4) := by
  have hc : (0 : ℝ) ≤ 1 + (2 - 2 * q) / 3 := by linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_log_div_primesIco_le_log y₀ y₁) hc)
  rw [diffK₁, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesIco hp).two_le
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hq : 0 ≤ 2 - 2 * q := by linarith
  have h1 : 2 / 3 * (2 - 2 * q) / (p : ℝ) ^ 2 ≤ (2 - 2 * q) / 3 / p := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hq (by linarith : (0 : ℝ) ≤ p))
      (by linarith : (0 : ℝ) ≤ p - 2)]
  calc Real.log p * (1 / (p : ℝ) + 2 / 3 * (2 - 2 * q) / (p : ℝ) ^ 2)
      ≤ Real.log p * (1 / (p : ℝ) + (2 - 2 * q) / 3 / p) :=
        mul_le_mul_of_nonneg_left (by linarith) hl
    _ = (1 + (2 - 2 * q) / 3) * (Real.log p / p) := by ring

/-- `K₃ ≤ 4(log y₁ + log 4 + 4)`: `6/p² ≤ 3/p`. -/
lemma diffK₃_le (y₀ y₁ : ℕ) : diffK₃ y₀ y₁ ≤ 4 * (Real.log y₁ + Real.log 4 + 4) := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_log_div_primesIco_le_log y₀ y₁)
    (by norm_num))
  rw [diffK₃, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesIco hp).two_le
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : 6 / (p : ℝ) ^ 2 ≤ 3 / p := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc Real.log p * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)
      ≤ Real.log p * (1 / (p : ℝ) + 3 / p) := mul_le_mul_of_nonneg_left (by linarith) hl
    _ = 4 * (Real.log p / p) := by ring

lemma diffK₁_nonneg (y₀ y₁ : ℕ) {q : ℝ} (hq1 : q ≤ 1) : 0 ≤ diffK₁ y₀ y₁ q :=
  Finset.sum_nonneg fun p _ => by
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hq : 0 ≤ 2 - 2 * q := by linarith
    positivity

lemma diffK₃_nonneg (y₀ y₁ : ℕ) : 0 ≤ diffK₃ y₀ y₁ :=
  Finset.sum_nonneg fun p _ => by
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    positivity

/-! ### Two elementary bounds -/

/-- `e^x - 1 ≤ x(1+e^x)/2` for `x ≥ 0`: the difference has derivative `(1 - e^x + xe^x)/2 ≥ 0`
(`tanh(x/2) ≤ x/2`). -/
lemma exp_sub_one_le_mul_one_add_exp_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * (1 + Real.exp x) / 2 := by
  have hmono : MonotoneOn (fun s : ℝ => s * (1 + Real.exp s) / 2 - (Real.exp s - 1))
      (Set.Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun s : ℝ => s * (1 + Real.exp s) / 2
        - (Real.exp s - 1)).continuousOn
    · intro s _
      exact (by fun_prop : Differentiable ℝ fun s : ℝ => s * (1 + Real.exp s) / 2
        - (Real.exp s - 1)) s |>.differentiableWithinAt
    · intro s _
      have d : HasDerivAt (fun s : ℝ => s * (1 + Real.exp s) / 2 - (Real.exp s - 1))
          ((1 * (1 + Real.exp s) + s * (0 + Real.exp s)) / 2 - Real.exp s) s :=
        ((((hasDerivAt_id' s).mul ((hasDerivAt_const s 1).add (Real.hasDerivAt_exp s))).div_const
          2)).sub ((Real.hasDerivAt_exp s).sub_const 1)
      rw [d.deriv]
      have h := Real.one_sub_le_exp_neg s
      have he : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
      have hpos := Real.exp_pos s
      nlinarith [mul_le_mul_of_nonneg_left h hpos.le]
  have h := hmono ⟨le_refl 0, hx⟩ ⟨hx, le_refl x⟩ hx
  simp only [Real.exp_zero, zero_mul, zero_div, sub_self] at h
  linarith

/-- The chord of `s ↦ e^{cs}` on `[0, τ²]`: `e^{ct²} ≤ 1 + (t²/τ²)(e^{cτ²} - 1)` for `t² ≤ τ²`,
`τ ≠ 0`. -/
lemma exp_mul_sq_le_chord {c t τ : ℝ} (hτ : τ ≠ 0) (ht : t ^ 2 ≤ τ ^ 2) :
    Real.exp (c * t ^ 2) ≤ 1 + t ^ 2 / τ ^ 2 * (Real.exp (c * τ ^ 2) - 1) := by
  have hτ2 : 0 < τ ^ 2 := by positivity
  set l := t ^ 2 / τ ^ 2 with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hτ2]; exact ht
  have hconv := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (c * τ ^ 2))
    (by linarith : (0 : ℝ) ≤ 1 - l) hl0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have heq : l * (c * τ ^ 2) = c * t ^ 2 := by
    rw [hl]
    field_simp
  rw [heq] at hconv
  linarith

/-! ### The central window in closed form -/

/-- **The central window's integral in closed form.**  For `½ ≤ q ≤ 1`, `σ > 0`, `τ > 0`,
`a ≥ (2q-1)K₁`, `K₂' ≥ K₂` and `K₃' ≥ K₃`:

`∫_{-τ}^{τ}(σ²+t²)⁻¹Q(σ,t)dt ≤ 2τ·a²(1+e^{a(τ+σ)})²/4
  + K₂'e^{4(1-q)σK₃'}(2τ + (2τ/3)(e^{2(1-q)K₂'τ²} - 1))`:

`(e^{ar}-1)/r ≤ a(1+e^{ar})/2` at `r = √(σ²+t²) ≤ τ + σ`, and the chord of `s ↦ e^{cs}`. -/
theorem setIntegral_inv_mul_diffQ_le (y₀ y₁ : ℕ) {q σ τ a K₂ K₃ : ℝ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hσ : 0 < σ) (hτ : 0 < τ) (ha : (2 * q - 1) * diffK₁ y₀ y₁ q ≤ a)
    (hK₂ : diffK₂ y₀ y₁ ≤ K₂) (hK₃ : diffK₃ y₀ y₁ ≤ K₃) :
    (∫ t in Set.Icc (-τ) τ, (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t)
      ≤ 2 * τ * (a ^ 2 * (1 + Real.exp (a * (τ + σ))) ^ 2 / 4)
        + K₂ * Real.exp (4 * (1 - q) * σ * K₃)
          * (2 * τ + 2 * τ / 3 * (Real.exp (2 * (1 - q) * K₂ * τ ^ 2) - 1)) := by
  have hq' : 0 ≤ 1 - q := by linarith
  have hd0 : 0 ≤ 2 * q - 1 := by linarith
  have hK₁0 := diffK₁_nonneg y₀ y₁ hq1
  have hK₂0 := diffK₂_nonneg y₀ y₁
  have hK₃0 := diffK₃_nonneg y₀ y₁
  have ha0 : 0 ≤ a := le_trans (mul_nonneg hd0 hK₁0) ha
  have hK₂'0 : 0 ≤ K₂ := le_trans hK₂0 hK₂
  have hK₃'0 : 0 ≤ K₃ := le_trans hK₃0 hK₃
  set α := a ^ 2 * (1 + Real.exp (a * (τ + σ))) ^ 2 / 4 with hα
  set B := K₂ * Real.exp (4 * (1 - q) * σ * K₃) with hB
  set E := Real.exp (2 * (1 - q) * K₂ * τ ^ 2) - 1 with hE
  have hα0 : 0 ≤ α := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hE0 : 0 ≤ E := by
    have : 0 ≤ 2 * (1 - q) * K₂ * τ ^ 2 := by positivity
    linarith [Real.one_le_exp this]
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Icc (-τ) τ, (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t
      ≤ α + B * (1 + t ^ 2 / τ ^ 2 * E) := by
    intro t ht
    have ht2 : t ^ 2 ≤ τ ^ 2 := by
      have : |t| ≤ τ := abs_le.2 ⟨ht.1, ht.2⟩
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ τ ^ 2 := pow_le_pow_left₀ (abs_nonneg t) this 2
    have hw : 0 < σ ^ 2 + t ^ 2 := by positivity
    have hsplit : (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t
        = (σ ^ 2 + t ^ 2)⁻¹ * (Real.exp ((2 * q - 1) * Real.sqrt (σ ^ 2 + t ^ 2)
            * diffK₁ y₀ y₁ q) - 1) ^ 2
          + diffK₂ y₀ y₁
            * Real.exp ((1 - q) * (2 * t ^ 2 * diffK₂ y₀ y₁ + 4 * σ * diffK₃ y₀ y₁)) := by
      rw [diffQ, mul_add]
      congr 1
      field_simp
    rw [hsplit]
    -- the first part
    set r := Real.sqrt (σ ^ 2 + t ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hw
    have hr2 : r ^ 2 = σ ^ 2 + t ^ 2 := Real.sq_sqrt hw.le
    have hrle : r ≤ τ + σ := by
      rw [hr, Real.sqrt_le_left (by linarith)]
      have hat : |t| ≤ τ := abs_le.2 ⟨ht.1, ht.2⟩
      nlinarith [sq_abs t, abs_nonneg t]
    set x := (2 * q - 1) * r * diffK₁ y₀ y₁ q with hx
    have hx0 : 0 ≤ x := by positivity
    have hxr : x ≤ r * a := by
      have := mul_le_mul_of_nonneg_right ha hr0.le
      calc x = (2 * q - 1) * diffK₁ y₀ y₁ q * r := by rw [hx]; ring
        _ ≤ a * r := this
        _ = r * a := by ring
    have hxa : x ≤ a * (τ + σ) :=
      le_trans hxr (by rw [mul_comm r a]; exact mul_le_mul_of_nonneg_left hrle ha0)
    have hHH := exp_sub_one_le_mul_one_add_exp_div_two hx0
    have hHH0 : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h1 : Real.exp x - 1 ≤ r * (a * (1 + Real.exp (a * (τ + σ))) / 2) := by
      refine le_trans hHH ?_
      have he : 1 + Real.exp x ≤ 1 + Real.exp (a * (τ + σ)) := by
        linarith [Real.exp_le_exp.2 hxa]
      have h1e : 0 ≤ 1 + Real.exp x := by positivity
      have := mul_le_mul hxr he h1e (by positivity)
      calc x * (1 + Real.exp x) / 2 ≤ r * a * (1 + Real.exp (a * (τ + σ))) / 2 := by linarith
        _ = r * (a * (1 + Real.exp (a * (τ + σ))) / 2) := by ring
    have h2 : (Real.exp x - 1) ^ 2 ≤ r ^ 2 * (a * (1 + Real.exp (a * (τ + σ))) / 2) ^ 2 := by
      have := pow_le_pow_left₀ hHH0 h1 2
      rwa [mul_pow] at this
    have hfirst : (σ ^ 2 + t ^ 2)⁻¹ * (Real.exp x - 1) ^ 2 ≤ α := by
      calc (σ ^ 2 + t ^ 2)⁻¹ * (Real.exp x - 1) ^ 2
          ≤ (σ ^ 2 + t ^ 2)⁻¹ * (r ^ 2 * (a * (1 + Real.exp (a * (τ + σ))) / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hw.le)
        _ = (a * (1 + Real.exp (a * (τ + σ))) / 2) ^ 2 := by
            rw [hr2]
            field_simp
        _ = α := by rw [hα]; ring
    -- the second part
    have hmono : (1 - q) * (2 * t ^ 2 * diffK₂ y₀ y₁ + 4 * σ * diffK₃ y₀ y₁)
        ≤ 4 * (1 - q) * σ * K₃ + 2 * (1 - q) * K₂ * t ^ 2 := by
      have h2' := mul_le_mul_of_nonneg_left hK₂ (by positivity : (0 : ℝ) ≤ (1 - q) * 2 * t ^ 2)
      have h3' := mul_le_mul_of_nonneg_left hK₃ (by positivity : (0 : ℝ) ≤ (1 - q) * 4 * σ)
      nlinarith [h2', h3']
    have hchord := exp_mul_sq_le_chord (c := 2 * (1 - q) * K₂) hτ.ne' ht2
    have hsecond : diffK₂ y₀ y₁
        * Real.exp ((1 - q) * (2 * t ^ 2 * diffK₂ y₀ y₁ + 4 * σ * diffK₃ y₀ y₁))
        ≤ B * (1 + t ^ 2 / τ ^ 2 * E) := by
      calc diffK₂ y₀ y₁
            * Real.exp ((1 - q) * (2 * t ^ 2 * diffK₂ y₀ y₁ + 4 * σ * diffK₃ y₀ y₁))
          ≤ K₂ * Real.exp (4 * (1 - q) * σ * K₃ + 2 * (1 - q) * K₂ * t ^ 2) :=
            mul_le_mul hK₂ (Real.exp_le_exp.2 hmono) (Real.exp_pos _).le hK₂'0
        _ = B * Real.exp (2 * (1 - q) * K₂ * t ^ 2) := by
            rw [Real.exp_add, hB]
            ring
        _ ≤ B * (1 + t ^ 2 / τ ^ 2 * E) := mul_le_mul_of_nonneg_left hchord hB0
    linarith
  -- integrate
  have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t := by
    have hc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun t => (by positivity : (0 : ℝ) < σ ^ 2 + t ^ 2).ne'
    exact hc.mul (continuous_diffQ y₀ y₁ q σ)
  have hrhs : Continuous fun t : ℝ => α + B * (1 + t ^ 2 / τ ^ 2 * E) := by fun_prop
  refine le_trans (setIntegral_mono_on hcont.integrableOn_Icc hrhs.integrableOn_Icc
    measurableSet_Icc hpt) (le_of_eq ?_)
  have hfun : (fun t : ℝ => α + B * (1 + t ^ 2 / τ ^ 2 * E))
      = fun t : ℝ => (α + B) + B * E / τ ^ 2 * t ^ 2 := by
    funext t
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), hfun,
    intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_pow 2).intervalIntegrable _ _ |>.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow,
    smul_eq_mul]
  have hτ0 : τ ≠ 0 := hτ.ne'
  field_simp
  ring

/-! ### The windows, explicit -/

/-- **A band's window without a split, explicit**: for the band `(y, z]`, `z ≥ 2`, `σ > 0`,
`0 ≤ q ≤ 1`, `T > 0` and `M` bounding the band's second moment on the line,
`(2/(2π log z))^q·E[(∫_{T/e}^{T}(σ²+t²)⁻¹‖F(½+σ+it)‖²dt)^q] ≤ ((e-1)M/(πT log z))^q`. -/
theorem window_band_le_nosplit_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (hz : 2 ≤ z) {σ q T M : ℝ} (hσ : 0 < σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T)
    (hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (y + 1) (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ M) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ ((Real.exp 1 - 1) * M / (Real.pi * T * Real.log z)) ^ q := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun ω => sq_nonneg _) (hM 0)
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hJ := integral_rpow_window_band_le_jensen_nosplit hX (y + 1) (z + 1) hσ hq0 hq1 hT hM
  have hc : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z)) ^ q := Real.rpow_nonneg (by positivity) _
  refine le_trans (mul_le_mul_of_nonneg_left hJ hc) (le_of_eq ?_)
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **A band's window by the split and Jensen, explicit.**  For the band `(y, z]` split at
`y ≤ z₁ ≤ z`, `2 ≤ y`, `σ > 0`, `½ ≤ q ≤ 1`, `T > 0` and `β ≥ 2(1-q)S₂(z₁+1)`:

`(2/(2π log z))^q·E[W_T^q]
  ≤ (log z₁/log y)^{q(2q-1)}e^{q(2q-1)(9.0028/log y + 9.0028/log z₁ + (2-2q)/(3y))}
    ·(W(βT²)·(log z/log z₁)e^{9.0028/log z + 9.0028/log z₁}/(πT log z))^q`,

`W = RMF.taylorWindowW`: the split and Jensen
(`RMF.integral_rpow_window_band_le_split_jensen_of_weight`), (PF) on the lower block and Mertens on
the upper one. -/
theorem window_band_le_split_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y z₁ z : ℕ} (hy : 2 ≤ y) (hyz₁ : y ≤ z₁)
    (hz₁z : z₁ ≤ z) {σ q T β : ℝ} (hσ : 0 < σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T)
    (hβ : 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) ≤ β) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (Real.log z₁ / Real.log y) ^ (q * (2 * q - 1))
          * Real.exp (q * (2 * q - 1)
            * (9.0028 / Real.log y + 9.0028 / Real.log z₁ + (2 - 2 * q) / (3 * y)))
        * (taylorWindowW (β * T ^ 2)
          * (Real.log z / Real.log z₁ * Real.exp (9.0028 / Real.log z + 9.0028 / Real.log z₁))
          / (Real.pi * T * Real.log z)) ^ q := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hz₁2 : (2 : ℝ) ≤ z₁ := by exact_mod_cast le_trans hy hyz₁
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans (le_trans hy hyz₁) hz₁z
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlz₁ : 0 < Real.log z₁ := Real.log_pos (by linarith)
  have hq' : 0 ≤ 1 - q := by linarith
  have hβ0 : 0 ≤ β := by
    have h2 : (0 : ℝ) ≤ Real.log ((z₁ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have : (0 : ℝ) ≤ 2 * (1 - q) * (Real.log ((z₁ + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((z₁ + 1 : ℕ) : ℝ) + 34) := by positivity
    linarith
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ hT hβ0
  have hMup := integral_normSq_Ico_shiftLine_le_mertens_ratio hX (z := z₁) (y := z)
    (le_trans hy hyz₁) hz₁z hσ.le 0
  have hV7 := integral_rpow_window_band_le_split_jensen_of_weight hX (y₀ := y + 1)
    (z₁ := z₁ + 1) (y := z + 1) (by omega) (by omega) hσ (by linarith) hq1 hT hβ0 hβ hR hMup
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs0] at hV7
  have hPF := hX.isRademacherRMF.integral_norm_randomEulerProductIco_shift_rpow_le_above_half
    hσ.le hq0 hq1 hy hyz₁
  set P := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
    (z₁ + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ with hPdef
  set R := taylorWindowW (β * T ^ 2) / T with hRdef
  set M := Real.log z / Real.log z₁ * Real.exp (9.0028 / Real.log z + 9.0028 / Real.log z₁)
    with hMdef
  have hW0 : 0 ≤ taylorWindowW (β * T ^ 2) := by
    have := taylorWindowW_nonneg (mul_nonneg hβ0 (sq_nonneg T))
    exact this
  have hR0 : 0 ≤ R := div_nonneg hW0 hT.le
  have hM0 : 0 ≤ M := by positivity
  have hc : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z)) ^ q := Real.rpow_nonneg (by positivity) _
  have hRM : (0 : ℝ) ≤ (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q :=
    Real.rpow_nonneg (by positivity) _
  calc (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ (2 / (2 * Real.pi * Real.log z)) ^ q * (P * (R * M) ^ q) :=
        mul_le_mul_of_nonneg_left hV7 hc
    _ = P * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q := by
        rw [Real.mul_rpow (x := 2 / (2 * Real.pi * Real.log z)) (y := R * M) (by positivity)
          (by positivity)]
        ring
    _ ≤ _ * (2 / (2 * Real.pi * Real.log z) * (R * M)) ^ q := mul_le_mul_of_nonneg_right hPF hRM
    _ = _ := by
        congr 2
        rw [hRdef, hMdef]
        field_simp

end RMF
