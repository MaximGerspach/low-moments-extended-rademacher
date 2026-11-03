/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.PartialSumBounds
import RMF.Analysis.FourierPlancherel

/-!
# Parseval for a dilated difference

An input to Caich's upper bound for short-interval sums (Caich, arXiv:2402.06426, Theorem 1.1;
`RMF.integral_rpow_shortIntervalSum_le_caich`).  For `λ > 0` and `A(u) = ∑_{n ≤ u} aₙ`,

`∫_0^∞ |A(λu) − A(u)|² u^{−1−2σ} du = (2π)^{−1} ∫_ℝ |(λ^s − 1)·D(s)/s|² dt`,   `s = σ + it`

(`RMF.integral_normSq_dilatedPartialSum_eq_line`).  This is the identity the short-interval
reduction lands on: over the `y`-smooth numbers, `∑_{x/m < n ≤ (x+y)/m}` is `A(λu) − A(u)` at
`u = x/m`, `λ = (x+y)/x`.

With `c = log λ` and `g(v) = e^{−σv}A(e^v)` (`RMF.logPartialSum`), Plancherel is applied to
`h(v) = e^{σc}g(v+c) − g(v) = e^{−σv}(A(e^{v+c}) − A(e^v))`.  Translation turns `𝓕g` into
`e^{2πicξ}𝓕g`, so `𝓕h(ξ) = (λ^s − 1)𝓕g(ξ)` at `s = σ + 2πiξ` (`RMF.fourier_logPartialSum`), and
`RMF.integral_normSq_fourier` closes it.

On the critical line the multiplier is controlled by `RMF.normSq_cpow_half_sub_one_le` and
`RMF.normSq_cpow_half_sub_one_le_seven`: for `1 ≤ λ ≤ 2`,
`|λ^{½+it} − 1|² ≤ 2(log λ)²(¼ + t²)` and `≤ 7`.
-/

open MeasureTheory

open scoped FourierTransform

namespace RMF

variable (σ : ℝ) (a : ℕ → ℂ)

/-- `h(v) = e^{σc}g(v + c) − g(v)`, `g = RMF.logPartialSum σ a`: the logarithmic form of the
difference `A(e^c u) − A(u)`. -/
noncomputable def dilatedLogPartialSum (c v : ℝ) : ℂ :=
  (Real.exp (σ * c) : ℂ) * logPartialSum σ a (v + c) - logPartialSum σ a v

lemma dilatedLogPartialSum_eq (c v : ℝ) :
    dilatedLogPartialSum σ a c v
      = (∑ n ∈ Finset.Icc 1 ⌊Real.exp c * Real.exp v⌋₊, a n
          - ∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n) * (Real.exp (-σ * v) : ℂ) := by
  have hexp : Real.exp (σ * c) * Real.exp (-σ * (v + c)) = Real.exp (-σ * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hev : Real.exp (v + c) = Real.exp c * Real.exp v := by
    rw [Real.exp_add, mul_comm]
  have hC : ((Real.exp (σ * c) : ℝ) : ℂ) * ((Real.exp (-σ * (v + c)) : ℝ) : ℂ)
      = ((Real.exp (-σ * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hexp]
  rw [dilatedLogPartialSum, logPartialSum, logPartialSum, hev]
  linear_combination (∑ n ∈ Finset.Icc 1 ⌊Real.exp c * Real.exp v⌋₊, a n) * hC

lemma measurable_dilatedLogPartialSum (c : ℝ) : Measurable (dilatedLogPartialSum σ a c) := by
  have hg := measurable_logPartialSum σ a
  have hgc : Measurable fun v => logPartialSum σ a (v + c) :=
    hg.comp (measurable_id.add_const c)
  exact (hgc.const_mul _).sub hg

lemma exp_mul_normSq_dilated_eq (c v : ℝ) :
    Real.exp v * (‖∑ n ∈ Finset.Icc 1 ⌊Real.exp c * Real.exp v⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ ^ 2 / Real.exp v ^ (1 + 2 * σ))
      = ‖dilatedLogPartialSum σ a c v‖ ^ 2 := by
  have h : Real.exp v / Real.exp (v * (1 + 2 * σ)) = Real.exp (-σ * v) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [dilatedLogPartialSum_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), exp_rpow]
  generalize ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp c * Real.exp v⌋₊, a n
      - ∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ = D
  calc Real.exp v * (D ^ 2 / Real.exp (v * (1 + 2 * σ)))
      = (Real.exp v / Real.exp (v * (1 + 2 * σ))) * D ^ 2 := by ring
    _ = (D * Real.exp (-σ * v)) ^ 2 := by rw [h]; ring

lemma integral_normSq_dilatedLogPartialSum (c : ℝ) :
    ∫ v : ℝ, ‖dilatedLogPartialSum σ a c v‖ ^ 2
      = ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp c * u⌋₊, a n
          - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ) := by
  rw [integral_Ioi_eq_integral_exp]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun v => (exp_mul_normSq_dilated_eq σ a c v).symm)

lemma integrable_dilatedLogPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) (c : ℝ) :
    Integrable (dilatedLogPartialSum σ a c) := by
  have hg := integrable_logPartialSum σ a hσ ha
  have hgc : Integrable fun v => logPartialSum σ a (v + c) := hg.comp_add_right c
  exact (hgc.const_mul _).sub hg

lemma memLp_two_dilatedLogPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) (c : ℝ) :
    MemLp (dilatedLogPartialSum σ a c) 2 := by
  have hg := memLp_two_logPartialSum σ a hσ ha
  have hgc : MemLp (logPartialSum σ a ∘ fun v => v + c) 2 :=
    hg.comp_measurePreserving (measurePreserving_add_right volume c)
  exact (hgc.const_mul _).sub hg

/-! ### The Fourier transform of `h` -/

theorem fourier_dilatedLogPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a))
    (c ξ : ℝ) :
    𝓕 (dilatedLogPartialSum σ a c) ξ
      = ((Real.exp (σ * c) : ℂ) * Complex.exp (↑(2 * Real.pi * (c * ξ)) * Complex.I) - 1)
        * 𝓕 (logPartialSum σ a) ξ := by
  set ch : ℝ → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) with hch
  have hF : ∀ φ : ℝ → ℂ, 𝓕 φ ξ = ∫ v, ch v * φ v := by
    intro φ
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hinner : (inner ℝ v ξ : ℝ) = v * ξ := Real.inner_apply v ξ
    simp only [smul_eq_mul, hch, hinner]
  have hchm : Measurable ch := by
    rw [hch]
    fun_prop
  have hchb : ∀ v, ‖ch v‖ ≤ 1 := fun v => by
    rw [hch, Complex.norm_exp_ofReal_mul_I]
  have hg := integrable_logPartialSum σ a hσ ha
  have hgc : Integrable fun v => logPartialSum σ a (v + c) := hg.comp_add_right c
  have hI0 : Integrable fun v => ch v * logPartialSum σ a v :=
    hg.bdd_mul hchm.aestronglyMeasurable (Filter.Eventually.of_forall hchb)
  have hI1 : Integrable fun v => ch v * logPartialSum σ a (v + c) :=
    hgc.bdd_mul hchm.aestronglyMeasurable (Filter.Eventually.of_forall hchb)
  -- translation
  have hshift : ∀ v, ch (v + c - c) = ch v := fun v => by rw [add_sub_cancel_right]
  have hphase : ∀ w, ch (w - c) = Complex.exp (↑(2 * Real.pi * (c * ξ)) * Complex.I) * ch w := by
    intro w
    rw [hch, ← Complex.exp_add]
    push_cast
    ring_nf
  have htrans : (∫ v, ch v * logPartialSum σ a (v + c))
      = Complex.exp (↑(2 * Real.pi * (c * ξ)) * Complex.I)
        * ∫ v, ch v * logPartialSum σ a v := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun w : ℝ => ch (w - c) * logPartialSum σ a w) c
    simp only [hshift] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hphase]
    ring
  rw [hF, hF]
  have hsplit : (∫ v, ch v * dilatedLogPartialSum σ a c v)
      = (Real.exp (σ * c) : ℂ) * (∫ v, ch v * logPartialSum σ a (v + c))
        - ∫ v, ch v * logPartialSum σ a v := by
    rw [← integral_const_mul, ← integral_sub (hI1.const_mul _) hI0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [dilatedLogPartialSum]
    ring
  rw [hsplit, htrans]
  ring

/-! ### Parseval for the dilated difference -/

/-- **Parseval for a dilated difference.**  For `σ > 0`, `λ > 0` and `∑ ‖aₙ‖/n^σ < ∞`,

`∫_0^∞ |A(λu) − A(u)|² u^{−1−2σ} du = (2π)^{−1} ∫_ℝ |(λ^s − 1)·D(s)/s|² dt`,   `s = σ + it`. -/
theorem integral_normSq_dilatedPartialSum_eq_line (hσ : 0 < σ) (ha : Summable (coeffWeight σ a))
    {l : ℝ} (hl : 0 < l) :
    ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖((l : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) - 1)
            * (∑' n : ℕ, a n / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hne : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  have hlc : Real.exp (Real.log l) = l := Real.exp_log hl
  have hmult : ∀ t : ℝ, (Real.exp (σ * Real.log l) : ℂ)
      * Complex.exp (↑(2 * Real.pi * (Real.log l * ((2 * Real.pi)⁻¹ * t))) * Complex.I)
      = (l : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.cpow_def_of_ne_zero hne,
      ← Complex.ofReal_log hl.le]
    congr 1
    push_cast
    field_simp
  have hkey : ∀ t : ℝ,
      ‖((l : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) - 1)
        * (∑' n : ℕ, a n / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = ‖𝓕 (dilatedLogPartialSum σ a (Real.log l)) ((2 * Real.pi)⁻¹ * t)‖ ^ 2 := by
    intro t
    have harg : ((σ : ℂ) + 2 * (Real.pi : ℂ) * ((((2 * Real.pi)⁻¹ * t : ℝ)) : ℂ) * Complex.I)
        = (σ : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [fourier_dilatedLogPartialSum σ a hσ ha, fourier_logPartialSum σ a hσ ha, harg, hmult,
      mul_div_assoc]
  have hLHS : ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ)
      = ∫ v : ℝ, ‖dilatedLogPartialSum σ a (Real.log l) v‖ ^ 2 := by
    rw [integral_normSq_dilatedLogPartialSum, hlc]
  rw [hLHS, ← integral_normSq_fourier (integrable_dilatedLogPartialSum σ a hσ ha _)
      (memLp_two_dilatedLogPartialSum σ a hσ ha _)]
  simp_rw [hkey]
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun ξ => ‖𝓕 (dilatedLogPartialSum σ a (Real.log l)) ξ‖ ^ 2) (2 * Real.pi)⁻¹, inv_inv,
    abs_of_pos hpi, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

/-- **The dilated difference's integrand is integrable**, as the `L²` norm of `h`. -/
theorem integrableOn_normSq_dilatedPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a))
    {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ)) (Set.Ioi (0 : ℝ)) := by
  have hlc : Real.exp (Real.log l) = l := Real.exp_log hl
  have hsq : Integrable fun v => ‖dilatedLogPartialSum σ a (Real.log l) v‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_dilatedLogPartialSum σ a _).aestronglyMeasurable).1
      (memLp_two_dilatedLogPartialSum σ a hσ ha _)
  refine (integrableOn_Ioi_iff_integrable_exp _).2 (hsq.congr ?_)
  refine Filter.Eventually.of_forall fun v => ?_
  have h := exp_mul_normSq_dilated_eq σ a (Real.log l) v
  rw [hlc] at h
  exact h.symm

/-! ### The critical line -/

theorem integrableOn_normSq_dilatedPartialSum_half
    (ha : Summable fun n : ℕ => ‖a n‖ / Real.sqrt n) {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hσ : (0 : ℝ) < 1 / 2 := by norm_num
  have hw : coeffWeight (1 / 2) a = fun n : ℕ => ‖a n‖ / Real.sqrt n :=
    funext (coeffWeight_half a)
  have haw : Summable (coeffWeight (1 / 2) a) := by rw [hw]; exact ha
  refine (integrableOn_normSq_dilatedPartialSum (1 / 2) a hσ haw hl).congr_fun
    (fun u _ => ?_) measurableSet_Ioi
  simp only [show (1 : ℝ) + 2 * (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integral_normSq_dilatedPartialSum_eq_line_half
    (ha : Summable fun n : ℕ => ‖a n‖ / Real.sqrt n) {l : ℝ} (hl : 0 < l) :
    ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖((l : ℂ) ^ (1 / 2 + (t : ℂ) * Complex.I) - 1)
            * (∑' n : ℕ, a n / (n : ℂ) ^ (1 / 2 + (t : ℂ) * Complex.I))
            / (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hσ : (0 : ℝ) < 1 / 2 := by norm_num
  have hw : coeffWeight (1 / 2) a = fun n : ℕ => ‖a n‖ / Real.sqrt n :=
    funext (coeffWeight_half a)
  have haw : Summable (coeffWeight (1 / 2) a) := by rw [hw]; exact ha
  have hkey := integral_normSq_dilatedPartialSum_eq_line (1 / 2) a hσ haw hl
  have hL : ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * (1 / 2 : ℝ))
      = ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊l * u⌋₊, a n
        - ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [show (1 : ℝ) + 2 * (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← hL, hkey]
  norm_num

/-! ### The multiplier on the critical line -/

lemma cpow_half_add_mul_I_eq {l : ℝ} (hl : 0 < l) (t : ℝ) :
    (l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = (Real.exp (Real.log l / 2) : ℂ) * Complex.exp (↑(Real.log l * t) * Complex.I) := by
  have hne : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hl.le, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `|λ^{½+it} − 1|² = (λ^{½} − 1)² + 2λ^{½}(1 − cos(t log λ))`. -/
lemma normSq_cpow_half_sub_one_eq {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
      = (Real.exp (Real.log l / 2) - 1) ^ 2
        + 2 * Real.exp (Real.log l / 2) * (1 - Real.cos (Real.log l * t)) := by
  rw [cpow_half_add_mul_I_eq hl t, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, sub_zero]
  have hsc := Real.sin_sq_add_cos_sq (Real.log l * t)
  linear_combination (Real.exp (Real.log l / 2)) ^ 2 * hsc

/-- **The multiplier is small near the real axis.**  For `1 ≤ λ ≤ 2`,
`|λ^{½+it} − 1|² ≤ 2(log λ)²(¼ + t²)`: `λ^{½} − 1 ≤ ½λ^{½}log λ` and `1 − cos θ ≤ θ²/2`. -/
lemma normSq_cpow_half_sub_one_le {l : ℝ} (h1 : 1 ≤ l) (h2 : l ≤ 2) (t : ℝ) :
    ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2
      ≤ 2 * Real.log l ^ 2 * (1 / 4 + t ^ 2) := by
  have hl : 0 < l := by linarith
  rw [normSq_cpow_half_sub_one_eq hl t]
  set c : ℝ := Real.log l with hc
  have hc0 : 0 ≤ c := Real.log_nonneg h1
  set e : ℝ := Real.exp (c / 2) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by linarith)
  have hesq : e ^ 2 = l := by
    rw [he, ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * (c / 2) = c by ring, hc, Real.exp_log hl]
  have hsub : e - 1 ≤ c / 2 * e := by
    have h := Real.add_one_le_exp (-(c / 2))
    have hmul : Real.exp (-(c / 2)) * e = 1 := by
      rw [he, ← Real.exp_add]
      simp
    nlinarith
  have hA : (e - 1) ^ 2 ≤ c ^ 2 / 2 := by
    have h0 : 0 ≤ e - 1 := by linarith
    have hsq : (e - 1) ^ 2 ≤ (c / 2 * e) ^ 2 := pow_le_pow_left₀ h0 hsub 2
    have hce : (c / 2 * e) ^ 2 = c ^ 2 / 4 * e ^ 2 := by ring
    rw [hce, hesq] at hsq
    nlinarith [sq_nonneg c]
  have hcos : 1 - Real.cos (c * t) ≤ (c * t) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := c * t)
    linarith
  have he2 : e ≤ 2 := by nlinarith
  have hB : 2 * e * (1 - Real.cos (c * t)) ≤ 2 * c ^ 2 * t ^ 2 := by
    have h1c : 0 ≤ 1 - Real.cos (c * t) := by linarith [Real.cos_le_one (c * t)]
    calc 2 * e * (1 - Real.cos (c * t)) ≤ 2 * 2 * ((c * t) ^ 2 / 2) :=
          mul_le_mul (by linarith) hcos h1c (by norm_num)
      _ = 2 * c ^ 2 * t ^ 2 := by ring
  nlinarith [hA, hB]

/-- **The multiplier is bounded.**  For `1 ≤ λ ≤ 2`, `|λ^{½+it} − 1|² ≤ 7`. -/
lemma normSq_cpow_half_sub_one_le_seven {l : ℝ} (h1 : 1 ≤ l) (h2 : l ≤ 2) (t : ℝ) :
    ‖(l : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 ≤ 7 := by
  have hl : 0 < l := by linarith
  rw [normSq_cpow_half_sub_one_eq hl t]
  set c : ℝ := Real.log l with hc
  have hc0 : 0 ≤ c := Real.log_nonneg h1
  set e : ℝ := Real.exp (c / 2) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by linarith)
  have hesq : e ^ 2 = l := by
    rw [he, ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * (c / 2) = c by ring, hc, Real.exp_log hl]
  have he32 : e ≤ 3 / 2 := by nlinarith
  have h1c : 1 - Real.cos (c * t) ≤ 2 := by linarith [Real.neg_one_le_cos (c * t)]
  have h1c0 : 0 ≤ 1 - Real.cos (c * t) := by linarith [Real.cos_le_one (c * t)]
  have hA : (e - 1) ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 2 * e * (1 - Real.cos (c * t)) ≤ 6 := by nlinarith
  linarith

end RMF
