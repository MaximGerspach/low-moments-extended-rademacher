/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.TwoPointAboveHalfExplicit
import RMF.Weighted.EulerMomentAboveHalfExplicit
import RMF.Weighted.LemmaTExplicit

/-!
# The central window of the difference form

For `½ ≤ q ≤ 1` and the band product `F` over `[y₀, y₁)`, the normalised difference moment at one
height has a closed form over the primes (`RMF.integral_rpow_mul_normSq_sub_eq_prod`): with `m`,
`R`, `E` the plain, two-point and cross local moments, `e = E/m` and `r = R/m`,

`E[‖F(½)‖^{2q-2}‖F(½) - F(s)‖²]/E‖F(½)‖^{2q} = ‖1 - ∏e_p‖² + (∏r_p - ‖∏e_p‖²)`,

both parts of second order in `s - ½` (`RMF.one_add_prod_sub_two_re_prod_le`).  Bounded prime by
prime at `s = ½+σ+it` (`RMF.prime_difference_inputs`) this is `Q(σ, t) = RMF.diffQ`
(`RMF.integral_rpow_mul_normSq_sub_le`), and Hölder against `‖F(½)‖^{2q-2}` over the window
(`RMF.integral_rpow_setIntegral_le_of_mixed`) gives the central window of the difference
functional (`RMF.integral_rpow_centralWindow_diff_le`):

`E[(∫_{-τ}^{τ}L⁻¹(σ²+t²)⁻¹‖F(½) - F(½+σ+it)‖²)^q]
  ≤ (∫_{-τ}^{τ}L⁻¹(σ²+t²)⁻¹Q(σ,t))^q·E‖F(½)‖^{2q}`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### One prime: the three local moments -/

/-- **The local cross moment at one prime, against the Rademacher law**:
`E[‖1+Xa‖^{2q-2}(1+Xa)·conj(1+Xu)] = ½((1+a)^{2q-1}conj(1+u) + (1-a)^{2q-1}conj(1-u))` for real
`0 ≤ a < 1`. -/
lemma integral_cross_rademacherLaw {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (u : ℂ) :
    (∫ z, ((‖1 + z * (a : ℂ)‖ ^ (2 * q - 2) : ℝ) : ℂ) * ((1 + z * (a : ℂ))
        * (starRingEnd ℂ) (1 + z * u)) ∂rademacherLaw)
      = (2 : ℝ)⁻¹ • ((((1 + a) ^ (2 * q - 1) : ℝ) : ℂ) * (starRingEnd ℂ) (1 + u)
        + (((1 - a) ^ (2 * q - 1) : ℝ) : ℂ) * (starRingEnd ℂ) (1 - u)) := by
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm : (0 : ℝ) < 1 - a := by linarith
  have e1 : ‖(1 : ℂ) + 1 * (a : ℂ)‖ = 1 + a := by
    rw [one_mul, show (1 : ℂ) + (a : ℂ) = ((1 + a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp]
  have e2 : ‖(1 : ℂ) + -1 * (a : ℂ)‖ = 1 - a := by
    rw [show (1 : ℂ) + -1 * (a : ℂ) = ((1 - a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hm]
  have p1 : (1 + a) ^ (2 * q - 2) * (1 + a) = (1 + a) ^ (2 * q - 1) := by
    rw [show 2 * q - 1 = (2 * q - 2) + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  have p2 : (1 - a) ^ (2 * q - 2) * (1 - a) = (1 - a) ^ (2 * q - 1) := by
    rw [show 2 * q - 1 = (2 * q - 2) + 1 by ring, Real.rpow_add hm, Real.rpow_one]
  rw [integral_rademacherLaw_eq, e1, e2]
  congr 1
  simp only [one_mul, neg_one_mul]
  rw [← p1, ← p2]
  push_cast
  ring_nf

/-- **The local two-point moment at one prime**:
`E[‖1+Xa‖^{2q-2}‖1+Xu‖²] = ½((1+a)^{2q-2}‖1+u‖² + (1-a)^{2q-2}‖1-u‖²)`. -/
lemma integral_two_point_rademacherLaw_eq {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (u : ℂ) :
    (∫ z, ‖1 + z * (a : ℂ)‖ ^ (2 * q - 2) * ‖1 + z * u‖ ^ 2 ∂rademacherLaw)
      = (2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q - 2) * ‖1 + u‖ ^ 2
        + (1 - a) ^ (2 * q - 2) * ‖1 - u‖ ^ 2) := by
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm : (0 : ℝ) < 1 - a := by linarith
  have e1 : ‖(1 : ℂ) + 1 * (a : ℂ)‖ = 1 + a := by
    rw [one_mul, show (1 : ℂ) + (a : ℂ) = ((1 + a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp]
  have e2 : ‖(1 : ℂ) + -1 * (a : ℂ)‖ = 1 - a := by
    rw [show (1 : ℂ) + -1 * (a : ℂ) = ((1 - a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hm]
  rw [integral_rademacherLaw_eq, e1, e2, smul_eq_mul]
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]

/-- **The plain local moment at one prime**: `E‖1+Xa‖^{2q} = ½((1+a)^{2q} + (1-a)^{2q})`. -/
lemma integral_plain_rademacherLaw_eq {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∫ z, ‖1 + z * (a : ℂ)‖ ^ (2 * q) ∂rademacherLaw)
      = (2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) := by
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm : (0 : ℝ) < 1 - a := by linarith
  have e1 : ‖(1 : ℂ) + 1 * (a : ℂ)‖ = 1 + a := by
    rw [one_mul, show (1 : ℂ) + (a : ℂ) = ((1 + a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp]
  have e2 : ‖(1 : ℂ) + -1 * (a : ℂ)‖ = 1 - a := by
    rw [show (1 : ℂ) + -1 * (a : ℂ) = ((1 - a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hm]
  rw [integral_rademacherLaw_eq, e1, e2, smul_eq_mul]

/-! ### One prime: the identities -/

/-- **The cross moment minus the plain one**: with `m` the plain moment and `E` the cross moment,
`E - m = ½(conj u - a)((1+a)^{2q-1} - (1-a)^{2q-1})`. -/
lemma cross_sub_plain_eq {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (u : ℂ) :
    (2 : ℝ)⁻¹ • ((((1 + a) ^ (2 * q - 1) : ℝ) : ℂ) * (starRingEnd ℂ) (1 + u)
        + (((1 - a) ^ (2 * q - 1) : ℝ) : ℂ) * (starRingEnd ℂ) (1 - u))
      - (((2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q)) : ℝ) : ℂ)
      = (2 : ℝ)⁻¹ • (((starRingEnd ℂ) u - (a : ℂ))
        * ((((1 + a) ^ (2 * q - 1) - (1 - a) ^ (2 * q - 1) : ℝ)) : ℂ)) := by
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm : (0 : ℝ) < 1 - a := by linarith
  have p1 : (1 + a) ^ (2 * q) = (1 + a) ^ (2 * q - 1) * (1 + a) := by
    rw [← Real.rpow_add_one hp.ne', show 2 * q - 1 + 1 = 2 * q by ring]
  have p2 : (1 - a) ^ (2 * q) = (1 - a) ^ (2 * q - 1) * (1 - a) := by
    rw [← Real.rpow_add_one hm.ne', show 2 * q - 1 + 1 = 2 * q by ring]
  rw [p1, p2]
  simp only [map_add, map_sub, map_one, Complex.real_smul]
  push_cast
  ring

/-- **The Lagrange identity of the two-point law**: with `P = (1+a)^{2q-2}`, `M = (1-a)^{2q-2}`,
`m` the plain, `E` the cross and `R` the two-point moment, `m·R - ‖E‖² = P·M·‖u - a‖²`. -/
lemma plain_mul_two_point_sub_normSq_cross {a P M : ℝ} (u : ℂ) :
    ((2 : ℝ)⁻¹ * (P * (1 + a) ^ 2 + M * (1 - a) ^ 2))
        * ((2 : ℝ)⁻¹ * (P * ‖1 + u‖ ^ 2 + M * ‖1 - u‖ ^ 2))
      - ‖(2 : ℝ)⁻¹ • (((P * (1 + a) : ℝ) : ℂ) * (starRingEnd ℂ) (1 + u)
          + ((M * (1 - a) : ℝ) : ℂ) * (starRingEnd ℂ) (1 - u))‖ ^ 2
      = P * M * ‖u - (a : ℂ)‖ ^ 2 := by
  simp only [Complex.real_smul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, map_add, map_sub, map_one]
  ring

/-! ### The three moments over a band -/

/-- The plain local moment `½((1+a)^{2q} + (1-a)^{2q})`. -/
noncomputable def plainLocal (q a : ℝ) : ℝ := (2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q) + (1 - a) ^ (2 * q))

/-- The local two-point moment `½((1+a)^{2q-2}‖1+u‖² + (1-a)^{2q-2}‖1-u‖²)`. -/
noncomputable def twoPointLocal (q a : ℝ) (u : ℂ) : ℝ :=
  (2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q - 2) * ‖1 + u‖ ^ 2 + (1 - a) ^ (2 * q - 2) * ‖1 - u‖ ^ 2)

/-- The local cross moment `½((1+a)^{2q-1}conj(1+u) + (1-a)^{2q-1}conj(1-u))`. -/
noncomputable def crossLocal (q a : ℝ) (u : ℂ) : ℂ :=
  (2 : ℝ)⁻¹ • ((((1 + a) ^ (2 * q - 1) : ℝ) : ℂ) * (starRingEnd ℂ) (1 + u)
    + (((1 - a) ^ (2 * q - 1) : ℝ) : ℂ) * (starRingEnd ℂ) (1 - u))

/-- `‖A - B‖² = ‖A‖² + ‖B‖² - 2 Re(A·conj B)`. -/
lemma norm_sub_sq_eq_re (A B : ℂ) :
    ‖A - B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * (A * (starRingEnd ℂ) B).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- `‖A‖^{2q-2}‖A‖² = ‖A‖^{2q}` for `q > 0`, also at `A = 0`. -/
lemma norm_rpow_two_mul_sub_two_mul_sq {q : ℝ} (hq : 0 < q) (A : ℂ) :
    ‖A‖ ^ (2 * q - 2) * ‖A‖ ^ 2 = ‖A‖ ^ (2 * q) := by
  rcases eq_or_lt_of_le (norm_nonneg A) with h | h
  · rw [← h, Real.zero_rpow (by linarith : (2 : ℝ) * q ≠ 0)]
    simp
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]
    norm_num

/-- **The pointwise identity behind the three moments**: for `q > 0`,
`‖A‖^{2q-2}‖A - B‖² = ‖A‖^{2q} + ‖A‖^{2q-2}‖B‖² - 2 Re(‖A‖^{2q-2}·A·conj B)`. -/
lemma norm_rpow_mul_norm_sub_sq {q : ℝ} (hq : 0 < q) (A B : ℂ) :
    ‖A‖ ^ (2 * q - 2) * ‖A - B‖ ^ 2
      = ‖A‖ ^ (2 * q) + ‖A‖ ^ (2 * q - 2) * ‖B‖ ^ 2
        - 2 * ((((‖A‖ ^ (2 * q - 2) : ℝ)) : ℂ) * (A * (starRingEnd ℂ) B)).re := by
  rw [norm_sub_sq_eq_re, Complex.re_ofReal_mul, ← norm_rpow_two_mul_sub_two_mul_sq hq A]
  ring

/-- **The three moments of a band factor over its primes.**  For `0 < q ≤ 1` and `Re s ≥ ½`, with
`F` the band product over `[y₀, y₁)`, `a_p = p^{-1/2}` and `u_p = p^{-s}`:

`E[‖F(½)‖^{2q-2}‖F(½) - F(s)‖²] = ∏_p m_p + ∏_p R_p - 2 Re ∏_p E_p`,

`m_p`, `R_p`, `E_p` the plain, two-point and cross local moments (`RMF.plainLocal`,
`RMF.twoPointLocal`, `RMF.crossLocal`).  The pointwise identity
`RMF.norm_rpow_mul_norm_sub_sq`, then independence (`RMF.IsIIDPrimeValues.integral_prod`, in `ℂ`
for the cross term). -/
theorem integral_rpow_mul_normSq_sub_eq_prod {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (1 / 2 : ℂ) ω‖ ^ (2 * q - 2)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (1 / 2 : ℂ) ω
          - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2
        ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
        + ∏ p ∈ primesIco y₀ y₁, twoPointLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) ((p : ℂ) ^ (-s))
        - 2 * (∏ p ∈ primesIco y₀ y₁,
            crossLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) ((p : ℂ) ^ (-s))).re := by
  classical
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set F : ℂ → Ω → ℂ := fun w ω =>
    randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ w ω with hFdef
  have hre0 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  -- the envelope
  set Lo : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) with hLo
  set Up : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) with hUp
  have hLo0 : 0 < Lo := Finset.prod_pos fun p hp => by
    have := prime_rpow_neg_lt_one (prime_of_mem_primesIco hp) (c := 1 / 2) (by norm_num)
    linarith
  have henv := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := 1 / 2)
    (by norm_num)
  have henv' := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := s.re)
    (by linarith)
  set Up' : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-s.re)) with hUp'
  have hm0 : AEMeasurable (F (1 / 2 : ℂ)) μ := hf.aemeasurable_randomEulerProductIco y₀ y₁ _
  have hm1 : AEMeasurable (F s) μ := hf.aemeasurable_randomEulerProductIco y₀ y₁ _
  -- integrability of the three pieces
  have hI1 : Integrable (fun ω => ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q)) μ := by
    refine (memLp_top_of_bound (hm0.norm.pow_const _).aestronglyMeasurable (Up ^ (2 * q)) ?_
      ).integrable le_top
    filter_upwards [henv] with ω hω
    have h := (hω (1 / 2 : ℂ) hre0).2
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) h (by linarith)
  have hneg : ∀ ω, Lo ≤ ‖F (1 / 2 : ℂ) ω‖ →
      ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) ≤ Lo ^ (2 * q - 2) := fun ω h =>
    Real.rpow_le_rpow_of_nonpos hLo0 h (by linarith)
  have hI2 : Integrable (fun ω => ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) * ‖F s ω‖ ^ 2) μ := by
    refine (memLp_top_of_bound (((hm0.norm.pow_const _).mul
      (hm1.norm.pow_const 2))).aestronglyMeasurable (Lo ^ (2 * q - 2) * Up' ^ 2) ?_
      ).integrable le_top
    filter_upwards [henv, henv'] with ω hω hω'
    simp only [Pi.mul_apply]
    have h0 := hω (1 / 2 : ℂ) hre0
    have h1 := (hω' s rfl).2
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul (hneg ω h0.1) (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by positivity)
      (Real.rpow_nonneg hLo0.le _)
  have hI3 : Integrable (fun ω => (((‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) : ℝ)) : ℂ)
      * (F (1 / 2 : ℂ) ω * (starRingEnd ℂ) (F s ω))) μ := by
    refine (memLp_top_of_bound ((Complex.measurable_ofReal.comp_aemeasurable
      (hm0.norm.pow_const _)).mul (hm0.mul (Complex.continuous_conj.measurable.comp_aemeasurable
        hm1))).aestronglyMeasurable (Lo ^ (2 * q - 2) * (Up * Up')) ?_).integrable le_top
    filter_upwards [henv, henv'] with ω hω hω'
    simp only [Pi.mul_apply, Function.comp_apply]
    have h0 := hω (1 / 2 : ℂ) hre0
    have h1 := (hω' s rfl).2
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg
      (norm_nonneg _) _), Complex.norm_conj]
    exact mul_le_mul (hneg ω h0.1) (mul_le_mul h0.2 h1 (norm_nonneg _) (by positivity))
      (by positivity) (Real.rpow_nonneg hLo0.le _)
  -- the identity, integrated
  have hpt : ∀ ω, ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) * ‖F (1 / 2 : ℂ) ω - F s ω‖ ^ 2
      = ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) + ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) * ‖F s ω‖ ^ 2
        - 2 * RCLike.re ((((‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) : ℝ)) : ℂ)
          * (F (1 / 2 : ℂ) ω * (starRingEnd ℂ) (F s ω))) := fun ω =>
    norm_rpow_mul_norm_sub_sq hq0 _ _
  have hIre : Integrable (fun ω => 2 * RCLike.re ((((‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) : ℝ)) : ℂ)
      * (F (1 / 2 : ℂ) ω * (starRingEnd ℂ) (F s ω)))) μ := hI3.re.const_mul 2
  have hI12 : Integrable (fun ω => ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q)
      + ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) * ‖F s ω‖ ^ 2) μ := hI1.add hI2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hI12 hIre,
    integral_add hI1 hI2, integral_const_mul, integral_re hI3]
  -- the plain moment
  have hA : (∫ ω, ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) := by
    rw [hFdef]
    dsimp only
    rw [hf.integral_norm_randomEulerProductIco_rpow_of_pos y₀ y₁ (by norm_num) q]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    have ha0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have ha1 : (p : ℝ) ^ (-(1 / 2) : ℝ) < 1 := prime_rpow_neg_lt_one hpp (by norm_num)
    rw [cpow_neg_half_eq, integral_plain_rademacherLaw_eq ha0 ha1, plainLocal]
  -- the two-point moment
  have hB : (∫ ω, ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) * ‖F s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, twoPointLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) ((p : ℂ) ^ (-s)) := by
    have hsvec : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 < (![(1 / 2 : ℂ), s] j).re := by
      intro j _
      fin_cases j <;> simp
      linarith
    have h := integral_prod_norm_randomEulerProductIco_rpow_sqfree hX norm_le_one_rademacherLaw
      y₀ y₁ (Finset.univ : Finset (Fin 2)) hsvec (q := ![q - 1, 1])
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have e1 : (2 : ℝ) * (q - 1) = 2 * q - 2 := by ring
    have hrw : ∀ v : ℂ, ‖v‖ ^ (2 * (1 : ℝ)) = ‖v‖ ^ 2 := fun v => by
      rw [mul_one, Real.rpow_two]
    simp only [e1, hrw] at h
    rw [hFdef]
    dsimp only
    rw [h]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    have ha0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have ha1 : (p : ℝ) ^ (-(1 / 2) : ℝ) < 1 := prime_rpow_neg_lt_one hpp (by norm_num)
    rw [cpow_neg_half_eq, integral_two_point_rademacherLaw_eq ha0 ha1, twoPointLocal]
  -- the cross moment
  have hC : (∫ ω, (((‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) : ℝ)) : ℂ)
        * (F (1 / 2 : ℂ) ω * (starRingEnd ℂ) (F s ω)) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, crossLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) ((p : ℂ) ^ (-s)) := by
    have hprod : ∀ ω, (((‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2) : ℝ)) : ℂ)
        * (F (1 / 2 : ℂ) ω * (starRingEnd ℂ) (F s ω))
        = ∏ p ∈ primesIco y₀ y₁, ((((‖1 + X p ω * (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖
            ^ (2 * q - 2) : ℝ)) : ℂ)
          * ((1 + X p ω * (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))
            * (starRingEnd ℂ) (1 + X p ω * (p : ℂ) ^ (-s)))) := by
      intro ω
      have h0 : F (1 / 2 : ℂ) ω = ∏ p ∈ primesIco y₀ y₁,
          (1 + X p ω * (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) := by
        rw [hFdef]
        dsimp only
        rw [randomEulerProductIco_sqfree_eq]
        exact Finset.prod_congr rfl fun p _ => by rw [cpow_neg_half_eq]
      have h1 : F s ω = ∏ p ∈ primesIco y₀ y₁, (1 + X p ω * (p : ℂ) ^ (-s)) := by
        rw [hFdef]
        exact randomEulerProductIco_sqfree_eq _ _ _ _
      rw [h0, h1, norm_prod, ← Real.finsetProd_rpow (primesIco y₀ y₁)
        (fun b => ‖1 + X b ω * (((b : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖)
        (fun _ _ => norm_nonneg _) (2 * q - 2),
        Complex.ofReal_prod, map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    rw [hX.integral_prod (fun p hp => prime_of_mem_primesIco hp)
      (fun p z => ((((‖1 + z * (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖ ^ (2 * q - 2) : ℝ)) : ℂ)
        * ((1 + z * (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))
          * (starRingEnd ℂ) (1 + z * (p : ℂ) ^ (-s))))) ?_]
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hpp := prime_of_mem_primesIco hp
      have ha0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
      have ha1 : (p : ℝ) ^ (-(1 / 2) : ℝ) < 1 := prime_rpow_neg_lt_one hpp (by norm_num)
      rw [integral_cross_rademacherLaw ha0 ha1, crossLocal]
    · intro p _
      refine Measurable.aestronglyMeasurable ?_
      have hc : Continuous fun z : ℂ => 1 + z * (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
        fun_prop
      have hc' : Continuous fun z : ℂ => 1 + z * (p : ℂ) ^ (-s) := by fun_prop
      exact (Complex.measurable_ofReal.comp (hc.measurable.norm.pow_const _)).mul
        (hc.measurable.mul (Complex.continuous_conj.measurable.comp hc'.measurable))
  rw [hA, hB, hC]
  rfl

/-! ### Bounding the three moments -/

/-- `∏y - ∏x ≤ (∑(y - x))·∏ max(y, 1)` for `0 ≤ x ≤ y` termwise. -/
lemma prod_sub_prod_le_sum_mul_prod_max {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hxy : ∀ i ∈ S, x i ≤ y i) :
    ∏ i ∈ S, y i - ∏ i ∈ S, x i ≤ (∑ i ∈ S, (y i - x i)) * ∏ i ∈ S, max (y i) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk IH =>
    have hx' : ∀ i ∈ S, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hxy' : ∀ i ∈ S, x i ≤ y i := fun i hi => hxy i (Finset.mem_insert_of_mem hi)
    have ih := IH hx' hxy'
    have hxk := hx k (Finset.mem_insert_self k S)
    have hyk := hxy k (Finset.mem_insert_self k S)
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk]
    have hyS : ∏ i ∈ S, y i ≤ ∏ i ∈ S, max (y i) 1 :=
      Finset.prod_le_prod (fun i hi => le_trans (hx' i hi) (hxy' i hi))
        fun i _ => le_max_left _ _
    have hyS0 : 0 ≤ ∏ i ∈ S, y i :=
      Finset.prod_nonneg fun i hi => le_trans (hx' i hi) (hxy' i hi)
    have hM1 : 1 ≤ ∏ i ∈ S, max (y i) 1 := by
      calc (1 : ℝ) = ∏ _i ∈ S, (1 : ℝ) := by simp
        _ ≤ ∏ i ∈ S, max (y i) 1 :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => le_max_right _ _
    have hsum0 : 0 ≤ ∑ i ∈ S, (y i - x i) :=
      Finset.sum_nonneg fun i hi => by linarith [hxy' i hi]
    have hmk : 1 ≤ max (y k) 1 := le_max_right _ _
    have hymk : y k ≤ max (y k) 1 := le_max_left _ _
    have e : y k * ∏ i ∈ S, y i - x k * ∏ i ∈ S, x i
        = (y k - x k) * ∏ i ∈ S, y i + x k * (∏ i ∈ S, y i - ∏ i ∈ S, x i) := by ring
    rw [e]
    have h1 : (y k - x k) * ∏ i ∈ S, y i ≤ (y k - x k) * (max (y k) 1 * ∏ i ∈ S, max (y i) 1) := by
      refine mul_le_mul_of_nonneg_left (le_trans hyS ?_) (by linarith)
      nlinarith
    have h2 : x k * (∏ i ∈ S, y i - ∏ i ∈ S, x i)
        ≤ max (y k) 1 * ((∑ i ∈ S, (y i - x i)) * ∏ i ∈ S, max (y i) 1) := by
      have h3 : x k * (∏ i ∈ S, y i - ∏ i ∈ S, x i)
          ≤ x k * ((∑ i ∈ S, (y i - x i)) * ∏ i ∈ S, max (y i) 1) :=
        mul_le_mul_of_nonneg_left ih hxk
      refine le_trans h3 (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    nlinarith [h1, h2]

/-- **The shape of the normalised difference moment**: for `‖e_i‖² ≤ r_i`,
`1 + ∏r - 2 Re ∏e = ‖1 - ∏e‖² + (∏r - ‖∏e‖²)`, at most
`(exp(∑‖e_i - 1‖) - 1)² + (∑(r_i - ‖e_i‖²))·∏max(r_i, 1)`.
Both parts are of second order in `e - 1` and `r - ‖e‖²`. -/
lemma one_add_prod_sub_two_re_prod_le {ι : Type*} (S : Finset ι) (e : ι → ℂ) (r : ι → ℝ)
    (her : ∀ i ∈ S, ‖e i‖ ^ 2 ≤ r i) :
    1 + ∏ i ∈ S, r i - 2 * (∏ i ∈ S, e i).re
      ≤ (Real.exp (∑ i ∈ S, ‖e i - 1‖) - 1) ^ 2
        + (∑ i ∈ S, (r i - ‖e i‖ ^ 2)) * ∏ i ∈ S, max (r i) 1 := by
  set E := ∏ i ∈ S, e i with hE
  have hid : 1 + ∏ i ∈ S, r i - 2 * E.re = ‖E - 1‖ ^ 2 + (∏ i ∈ S, r i - ‖E‖ ^ 2) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [hid]
  have hn : ‖E - 1‖ ≤ Real.exp (∑ i ∈ S, ‖e i - 1‖) - 1 := by
    have h := Finset.norm_prod_one_add_sub_one_le S (fun i => e i - 1)
    simp only [add_sub_cancel] at h
    exact h
  have hsq : ‖E - 1‖ ^ 2 ≤ (Real.exp (∑ i ∈ S, ‖e i - 1‖) - 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hprod : ∏ i ∈ S, r i - ‖E‖ ^ 2
      ≤ (∑ i ∈ S, (r i - ‖e i‖ ^ 2)) * ∏ i ∈ S, max (r i) 1 := by
    have hEn : ‖E‖ ^ 2 = ∏ i ∈ S, ‖e i‖ ^ 2 := by rw [hE, norm_prod, Finset.prod_pow]
    rw [hEn]
    exact prod_sub_prod_le_sum_mul_prod_max S (fun i => ‖e i‖ ^ 2) r
      (fun i _ => sq_nonneg _) her
  linarith

/-- The plain local moment is at least `1` for `q ≥ ½`: Bernoulli on both atoms. -/
lemma one_le_plainLocal {q a : ℝ} (hq : 1 / 2 ≤ q) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    1 ≤ plainLocal q a := by
  have h1 := one_add_mul_self_le_rpow_one_add (s := a) (by linarith) (p := 2 * q) (by linarith)
  have h2 := one_add_mul_self_le_rpow_one_add (s := -a) (by linarith) (p := 2 * q) (by linarith)
  rw [← sub_eq_add_neg] at h2
  rw [plainLocal]
  linarith

/-- The plain local moment in the two-atom form `½(P(1+a)² + M(1-a)²)`. -/
lemma plainLocal_eq {q a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    plainLocal q a = (2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q - 2) * (1 + a) ^ 2
      + (1 - a) ^ (2 * q - 2) * (1 - a) ^ 2) := by
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm : (0 : ℝ) < 1 - a := by linarith
  rw [plainLocal, ← Real.rpow_natCast (1 + a), ← Real.rpow_natCast (1 - a),
    ← Real.rpow_add hp, ← Real.rpow_add hm]
  norm_num

/-- **The cross moment is close to the plain one**: `‖E/m - 1‖ ≤ ‖u - a‖(2q-1)(a + (2/3)(2-2q)a³)`
for `½ ≤ q ≤ 1`, `a ≥ 0`, `a² ≤ ½`. -/
lemma norm_crossLocal_div_sub_one_le {q a : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (ha : a ^ 2 ≤ 1 / 2) (u : ℂ) :
    ‖crossLocal q a u / (plainLocal q a : ℂ) - 1‖
      ≤ ‖u - (a : ℂ)‖ * ((2 * q - 1) * (a + 2 / 3 * (2 - 2 * q) * a ^ 3)) := by
  have ha1 : a < 1 := by nlinarith
  have hm := one_le_plainLocal hq0 ha0 ha1
  have hm0 : (plainLocal q a : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have hdiff := cross_sub_plain_eq (q := q) ha0 ha1 u
  have hodd := rpow_one_add_sub_rpow_one_sub_le ha0 ha (by linarith : (0 : ℝ) ≤ 2 * q - 1)
    (by linarith : 2 * q - 1 ≤ 1)
  have hodd0 : 0 ≤ (1 + a) ^ (2 * q - 1) - (1 - a) ^ (2 * q - 1) := by
    have : (1 - a) ^ (2 * q - 1) ≤ (1 + a) ^ (2 * q - 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    linarith
  rw [div_sub_one hm0, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [div_le_iff₀ (by linarith)]
  have hE : crossLocal q a u - (plainLocal q a : ℂ)
      = (2 : ℝ)⁻¹ • (((starRingEnd ℂ) u - (a : ℂ))
        * ((((1 + a) ^ (2 * q - 1) - (1 - a) ^ (2 * q - 1) : ℝ)) : ℂ)) := by
    rw [crossLocal, plainLocal]
    exact hdiff
  rw [hE, norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hodd0,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have hconj : ‖(starRingEnd ℂ) u - (a : ℂ)‖ = ‖u - (a : ℂ)‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, Complex.conj_ofReal]
  rw [hconj]
  have hu0 : 0 ≤ ‖u - (a : ℂ)‖ := norm_nonneg _
  have key : (2 : ℝ)⁻¹ * (‖u - (a : ℂ)‖ * ((1 + a) ^ (2 * q - 1) - (1 - a) ^ (2 * q - 1)))
      ≤ ‖u - (a : ℂ)‖ * ((2 * q - 1) * (a + 2 / 3 * (2 - 2 * q) * a ^ 3)) := by
    have h := mul_le_mul_of_nonneg_left hodd hu0
    have e : (2 * q - 1) * (2 * a + 4 / 3 * (1 - (2 * q - 1)) * a ^ 3)
        = 2 * ((2 * q - 1) * (a + 2 / 3 * (2 - 2 * q) * a ^ 3)) := by ring
    rw [e] at h
    nlinarith
  have hprod0 : 0 ≤ ‖u - (a : ℂ)‖ * ((2 * q - 1) * (a + 2 / 3 * (2 - 2 * q) * a ^ 3)) :=
    mul_nonneg hu0 (mul_nonneg (by linarith) (add_nonneg ha0
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg ha0 3))))
  nlinarith

/-- **The variance of the tilted two-point law**: `R/m - ‖E/m‖² ≤ ‖u - a‖²/(1-a²)²`, from the
Lagrange identity `mR - ‖E‖² = PM‖u - a‖²` and `m ≥ (1-a²)√(PM)`. -/
lemma twoPointLocal_div_sub_normSq_le {q a : ℝ} (hq0 : 1 / 2 ≤ q) (ha0 : 0 ≤ a)
    (ha : a ^ 2 ≤ 1 / 2) (u : ℂ) :
    twoPointLocal q a u / plainLocal q a - ‖crossLocal q a u / (plainLocal q a : ℂ)‖ ^ 2
      ≤ ‖u - (a : ℂ)‖ ^ 2 / (1 - a ^ 2) ^ 2 := by
  have ha1 : a < 1 := by nlinarith
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm' : (0 : ℝ) < 1 - a := by linarith
  have hm := one_le_plainLocal hq0 ha0 ha1
  set P := (1 + a) ^ (2 * q - 2) with hP
  set M := (1 - a) ^ (2 * q - 2) with hM
  have hP0 : 0 < P := Real.rpow_pos_of_pos hp _
  have hM0 : 0 < M := Real.rpow_pos_of_pos hm' _
  have hmeq := plainLocal_eq (q := q) ha0 ha1
  rw [← hP, ← hM] at hmeq
  have hE : crossLocal q a u = (2 : ℝ)⁻¹ • (((P * (1 + a) : ℝ) : ℂ) * (starRingEnd ℂ) (1 + u)
      + ((M * (1 - a) : ℝ) : ℂ) * (starRingEnd ℂ) (1 - u)) := by
    rw [crossLocal, hP, hM, ← Real.rpow_add_one hp.ne', ← Real.rpow_add_one hm'.ne',
      show 2 * q - 2 + 1 = 2 * q - 1 by ring]
  have hR : twoPointLocal q a u = (2 : ℝ)⁻¹ * (P * ‖1 + u‖ ^ 2 + M * ‖1 - u‖ ^ 2) := by
    rw [twoPointLocal]
  have hlag := plain_mul_two_point_sub_normSq_cross (a := a) (P := P) (M := M) u
  have hmpos : 0 < plainLocal q a := by linarith
  -- `m² ≥ (1-a²)²PM`
  have hamgm : (1 - a ^ 2) ^ 2 * (P * M) ≤ plainLocal q a ^ 2 := by
    rw [hmeq]
    have e : (1 - a ^ 2) ^ 2 = (1 + a) ^ 2 * (1 - a) ^ 2 := by ring
    rw [e]
    nlinarith [sq_nonneg (P * (1 + a) ^ 2 - M * (1 - a) ^ 2), hP0, hM0]
  have hd0 : 0 < (1 - a ^ 2) ^ 2 := by
    have : 0 < 1 - a ^ 2 := by linarith
    positivity
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hmpos.le, div_pow]
  have hlhs : twoPointLocal q a u / plainLocal q a - ‖crossLocal q a u‖ ^ 2 / plainLocal q a ^ 2
      = (plainLocal q a * twoPointLocal q a u - ‖crossLocal q a u‖ ^ 2) / plainLocal q a ^ 2 := by
    field_simp
  rw [hlhs, hE, hR, hmeq]
  rw [hmeq] at hamgm hmpos
  rw [hlag]
  rw [div_le_div_iff₀ (pow_pos hmpos 2) hd0]
  have hu : 0 ≤ ‖u - (a : ℂ)‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hamgm hu]

/-- The two-point moment dominates the square of the cross moment: `‖E/m‖² ≤ R/m`, by the Lagrange
identity (`RMF.plain_mul_two_point_sub_normSq_cross`). -/
lemma normSq_crossLocal_div_le {q a : ℝ} (hq0 : 1 / 2 ≤ q) (ha0 : 0 ≤ a) (ha1 : a < 1) (u : ℂ) :
    ‖crossLocal q a u / (plainLocal q a : ℂ)‖ ^ 2 ≤ twoPointLocal q a u / plainLocal q a := by
  have hp : (0 : ℝ) < 1 + a := by linarith
  have hm' : (0 : ℝ) < 1 - a := by linarith
  have hm := one_le_plainLocal hq0 ha0 ha1
  have hmpos : 0 < plainLocal q a := by linarith
  set P := (1 + a) ^ (2 * q - 2) with hP
  set M := (1 - a) ^ (2 * q - 2) with hM
  have hP0 : 0 < P := Real.rpow_pos_of_pos hp _
  have hM0 : 0 < M := Real.rpow_pos_of_pos hm' _
  have hmeq := plainLocal_eq (q := q) ha0 ha1
  rw [← hP, ← hM] at hmeq
  have hE : crossLocal q a u = (2 : ℝ)⁻¹ • (((P * (1 + a) : ℝ) : ℂ) * (starRingEnd ℂ) (1 + u)
      + ((M * (1 - a) : ℝ) : ℂ) * (starRingEnd ℂ) (1 - u)) := by
    rw [crossLocal, hP, hM, ← Real.rpow_add_one hp.ne', ← Real.rpow_add_one hm'.ne',
      show 2 * q - 2 + 1 = 2 * q - 1 by ring]
  have hR : twoPointLocal q a u = (2 : ℝ)⁻¹ * (P * ‖1 + u‖ ^ 2 + M * ‖1 - u‖ ^ 2) := by
    rw [twoPointLocal]
  have hlag := plain_mul_two_point_sub_normSq_cross (a := a) (P := P) (M := M) u
  rw [← hmeq, ← hE, ← hR] at hlag
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hmpos.le, div_pow,
    div_le_div_iff₀ (pow_pos hmpos 2) hmpos]
  have h0 : 0 ≤ P * M * ‖u - (a : ℂ)‖ ^ 2 := by positivity
  nlinarith

/-- **A prime's factor at a shifted height**: `p^{-(½+σ+it)} = p^{-1/2}·e^{-σ log p - it log p}`. -/
lemma natCast_cpow_neg_half_add_eq {p : ℕ} (hp : 0 < p) (σ t : ℝ) :
    (p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))
      = (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * Complex.exp (((-(σ * Real.log p) : ℝ) : ℂ)
        + ((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsplit : (p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))
      = (p : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (((-(σ * Real.log p) : ℝ) : ℂ)
        + ((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
    rw [show -((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)
        = -(1 / 2 : ℂ) + -((σ : ℂ) + (t : ℂ) * Complex.I) by ring,
      Complex.cpow_add _ _ hp0,
      Complex.cpow_def_of_ne_zero hp0 (-((σ : ℂ) + (t : ℂ) * Complex.I)),
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hpR.le]
    congr 2
    push_cast
    ring
  rw [hsplit, cpow_neg_half_eq]

lemma re_ofReal_add_ofReal_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp

lemma im_ofReal_add_ofReal_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp

/-- `‖e^{-a-ib} - 1‖² ≤ a² + b²` for `a ≥ 0`: the square is `(1-e^{-a})² + 2e^{-a}(1 - cos b)`. -/
lemma norm_exp_neg_sub_one_sq_le {a b : ℝ} (ha : 0 ≤ a) :
    ‖Complex.exp (((-a : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have hre : (Complex.exp (((-a : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * Complex.I)).re
      = Real.exp (-a) * Real.cos b := by
    rw [Complex.exp_re]
    simp
  have him : (Complex.exp (((-a : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * Complex.I)).im
      = -(Real.exp (-a) * Real.sin b) := by
    rw [Complex.exp_im]
    simp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, hre, him]
  have hcs := Real.sin_sq_add_cos_sq b
  have hid : (Real.exp (-a) * Real.cos b - 1) * (Real.exp (-a) * Real.cos b - 1)
      + (-(Real.exp (-a) * Real.sin b) - 0) * (-(Real.exp (-a) * Real.sin b) - 0)
      = (1 - Real.exp (-a)) ^ 2 + 2 * Real.exp (-a) * (1 - Real.cos b) := by
    linear_combination Real.exp (-a) ^ 2 * hcs
  rw [hid]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := b)
  have hc1 := Real.cos_le_one b
  have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hea : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  have h1 : (1 - Real.exp (-a)) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : 2 * Real.exp (-a) * (1 - Real.cos b) ≤ b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 he1) (sub_nonneg.2 hc1)]
  linarith

/-- `‖p^{-(½+σ+it)} - p^{-1/2}‖ ≤ p^{-1/2}·√(σ²+t²)·log p` for `σ ≥ 0`. -/
lemma norm_natCast_cpow_neg_half_add_sub_le {p : ℕ} (hp : 0 < p) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ‖(p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))
        - (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖
      ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) * (Real.sqrt (σ ^ 2 + t ^ 2) * Real.log p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hℓ : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  rw [natCast_cpow_neg_half_add_eq hp, ← mul_sub_one, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hpR.le _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hpR.le _)
  have h := norm_exp_neg_sub_one_sq_le (a := σ * Real.log p) (b := t * Real.log p)
    (mul_nonneg hσ hℓ)
  have hr : (Real.sqrt (σ ^ 2 + t ^ 2) * Real.log p) ^ 2
      = (σ * Real.log p) ^ 2 + (t * Real.log p) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hℓ)
    two_ne_zero).1 (le_trans h (le_of_eq hr.symm))

/-- **The two-point bracket at a shifted height**: for `σ ≥ 0`,
`p^{-1/2}(p^{-1/2} - Re p^{-(½+σ+it)}) ≤ (1/p)(t²(log p)²/2 + σ log p)`. -/
lemma rpow_neg_half_mul_sub_re_le {p : ℕ} (hp : 0 < p) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    (p : ℝ) ^ (-(1 / 2) : ℝ) * ((p : ℝ) ^ (-(1 / 2) : ℝ)
        - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))).re)
      ≤ 1 / (p : ℝ) * (t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p) := by
  have hℓ : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hre : ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))).re
      = (p : ℝ) ^ (-(1 / 2) : ℝ) * (Real.exp (-(σ * Real.log p)) * Real.cos (t * Real.log p)) := by
    rw [natCast_cpow_neg_half_add_eq hp, Complex.re_ofReal_mul, Complex.exp_re,
      re_ofReal_add_ofReal_mul_I, im_ofReal_add_ofReal_mul_I, Real.cos_neg]
  have ha2 : ((p : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 = 1 / (p : ℝ) := by rw [rpow_neg_half_sq hp, one_div]
  have hE : 1 - Real.exp (-(σ * Real.log p)) * Real.cos (t * Real.log p)
      ≤ t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := t * Real.log p)
    have hc1 := Real.cos_le_one (t * Real.log p)
    have hσℓ : 0 ≤ σ * Real.log p := mul_nonneg hσ hℓ
    have he1 : Real.exp (-(σ * Real.log p)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hea : 1 - σ * Real.log p ≤ Real.exp (-(σ * Real.log p)) := by
      linarith [Real.add_one_le_exp (-(σ * Real.log p))]
    have hsq : (t * Real.log p) ^ 2 = t ^ 2 * Real.log p ^ 2 := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 he1)]
  rw [hre]
  calc (p : ℝ) ^ (-(1 / 2) : ℝ) * ((p : ℝ) ^ (-(1 / 2) : ℝ) - (p : ℝ) ^ (-(1 / 2) : ℝ)
        * (Real.exp (-(σ * Real.log p)) * Real.cos (t * Real.log p)))
      = ((p : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2
          * (1 - Real.exp (-(σ * Real.log p)) * Real.cos (t * Real.log p)) := by ring
    _ ≤ ((p : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 * (t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p) :=
        mul_le_mul_of_nonneg_left hE (sq_nonneg _)
    _ = 1 / (p : ℝ) * (t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p) := by rw [ha2]

/-- **The two-point ratio at one prime, as a bracket**: for `‖u‖ ≤ a`,
`R/m ≤ 1 + 4(1-q)a(a - Re u)/(1-a²)²` (`RMF.two_point_local_ratio_le_sharp_of_le_one`; the
two-point moment only grows with `‖u‖`). -/
lemma twoPointLocal_div_le_one_add {q a : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a < 1) {u : ℂ} (hun : ‖u‖ ≤ a) :
    twoPointLocal q a u / plainLocal q a
      ≤ 1 + 4 * (1 - q) * (a * (a - u.re)) / (1 - a ^ 2) ^ 2 := by
  have hm := one_le_plainLocal hq0 ha0 ha1
  have hre : u.re ≤ a := le_trans (Complex.re_le_norm _) hun
  have hloc := two_point_local_ratio_le_sharp_of_le_one (a := a) (v := u.re) (q := q)
    ha0 ha1 hre (by linarith) hq1
  have hu2 : ‖u‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hun 2
  have hn1 : ‖1 + u‖ ^ 2 = 1 + 2 * u.re + ‖u‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hn2 : ‖1 - u‖ ^ 2 = 1 - 2 * u.re + ‖u‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hP0 : 0 < (1 + a) ^ (2 * q - 2) := Real.rpow_pos_of_pos (by linarith) _
  have hM0 : 0 < (1 - a) ^ (2 * q - 2) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_iff₀ (by linarith), twoPointLocal, hn1, hn2]
  have hmono : (2 : ℝ)⁻¹ * ((1 + a) ^ (2 * q - 2) * (1 + 2 * u.re + ‖u‖ ^ 2)
      + (1 - a) ^ (2 * q - 2) * (1 - 2 * u.re + ‖u‖ ^ 2))
      ≤ ((1 + a) ^ (2 * q - 2) * (1 + 2 * u.re + a ^ 2)
        + (1 - a) ^ (2 * q - 2) * (1 - 2 * u.re + a ^ 2)) / 2 := by
    nlinarith
  refine le_trans hmono (le_trans hloc (le_of_eq ?_))
  rw [plainLocal]
  ring

/-- **The per-prime inputs of the difference moment at `p`**, `a = p^{-1/2}`,
`u = p^{-(½+σ+it)}`, `σ ≥ 0`, `r = √(σ²+t²)`: `‖e - 1‖ ≤ (2q-1)r log p (1/p + (2/3)(2-2q)/p²)`,
`r_p - ‖e‖² ≤ r²(log p)²(1/p + 6/p²)` and
`max(r_p, 1) ≤ 1 + (1-q)(2t²(log p)² + 4σ log p)(1/p + 6/p²)`, with `e = E/m`, `r_p = R/m`. -/
lemma prime_difference_inputs {p : ℕ} (hp : p.Prime) {q σ : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hσ : 0 ≤ σ) (t : ℝ) :
    ‖crossLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
          ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)))
        / (plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) : ℂ) - 1‖
      ≤ (2 * q - 1) * Real.sqrt (σ ^ 2 + t ^ 2)
        * (Real.log p * (1 / (p : ℝ) + 2 / 3 * (2 - 2 * q) / (p : ℝ) ^ 2))
    ∧ twoPointLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
          ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)))
        / plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
        - ‖crossLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
            ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)))
          / (plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) : ℂ)‖ ^ 2
      ≤ (σ ^ 2 + t ^ 2) * (Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2))
    ∧ max (twoPointLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
          ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)))
        / plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))) 1
      ≤ 1 + (1 - q) * (2 * t ^ 2 * Real.log p ^ 2 + 4 * σ * Real.log p)
          * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := by
  have hbr := rpow_neg_half_mul_sub_re_le hp.pos hσ t
  have hdist0 := norm_natCast_cpow_neg_half_add_sub_le hp.pos hσ t
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (p : ℝ) ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ⟨_, rfl⟩
  rw [← ha, ← hu] at hbr hdist0 ⊢
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ha0 : 0 ≤ a := by rw [ha]; exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  have ha1 : a < 1 := by rw [ha]; exact prime_rpow_neg_lt_one hp (by norm_num)
  have hsq : a ^ 2 = 1 / (p : ℝ) := by rw [ha, rpow_neg_half_sq hp.pos, one_div]
  have ha2 : a ^ 2 ≤ 1 / 2 := by rw [hsq]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hsre : ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by simp
  have hun : ‖u‖ ≤ a := by
    rw [hu, ha, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, hsre]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  set r := Real.sqrt (σ ^ 2 + t ^ 2) with hr
  have hr2 : r ^ 2 = σ ^ 2 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hx2 : 1 / (p : ℝ) ≤ 1 / 2 := by rw [← hsq]; exact ha2
  have hw := div_one_sub_sq_le hx0 hx2
  refine ⟨?_, ?_, ?_⟩
  · have h1 := norm_crossLocal_div_sub_one_le hq0 hq1 ha0 ha2 u
    have hc0 : 0 ≤ (2 * q - 1) * (a + 2 / 3 * (2 - 2 * q) * a ^ 3) :=
      mul_nonneg (by linarith) (add_nonneg ha0
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg ha0 3)))
    refine le_trans h1 (le_trans (mul_le_mul_of_nonneg_right hdist0 hc0) (le_of_eq ?_))
    have e4 : a ^ 4 = 1 / (p : ℝ) ^ 2 := by
      rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, hsq]
      field_simp
    have e3 : a * (a + 2 / 3 * (2 - 2 * q) * a ^ 3) = a ^ 2 + 2 / 3 * (2 - 2 * q) * a ^ 4 := by
      ring
    calc a * (r * Real.log p) * ((2 * q - 1) * (a + 2 / 3 * (2 - 2 * q) * a ^ 3))
        = (2 * q - 1) * r * (Real.log p * (a * (a + 2 / 3 * (2 - 2 * q) * a ^ 3))) := by ring
      _ = (2 * q - 1) * r * (Real.log p * (1 / (p : ℝ) + 2 / 3 * (2 - 2 * q) / (p : ℝ) ^ 2)) := by
          rw [e3, hsq, e4]
          ring
  · have h1 := twoPointLocal_div_sub_normSq_le hq0 ha0 ha2 u
    have hsq2 : ‖u - (a : ℂ)‖ ^ 2 ≤ (a * (r * Real.log p)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hdist0 2
    have hd0 : 0 < (1 - a ^ 2) ^ 2 := by
      have : 0 < 1 - a ^ 2 := by linarith
      positivity
    have hstep : ‖u - (a : ℂ)‖ ^ 2 / (1 - a ^ 2) ^ 2
        ≤ (a * (r * Real.log p)) ^ 2 / (1 - a ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hsq2 hd0.le
    have heq : (a * (r * Real.log p)) ^ 2 / (1 - a ^ 2) ^ 2
        = (σ ^ 2 + t ^ 2) * (Real.log p ^ 2 * ((1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2)) := by
      rw [mul_pow, mul_pow, hr2, hsq]
      ring
    have hw' : Real.log p ^ 2 * ((1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2)
        ≤ Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_left (le_trans hw (le_of_eq ?_)) (sq_nonneg _)
      ring
    calc _ ≤ ‖u - (a : ℂ)‖ ^ 2 / (1 - a ^ 2) ^ 2 := h1
      _ ≤ (a * (r * Real.log p)) ^ 2 / (1 - a ^ 2) ^ 2 := hstep
      _ = (σ ^ 2 + t ^ 2) * (Real.log p ^ 2 * ((1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2)) := heq
      _ ≤ (σ ^ 2 + t ^ 2) * (Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hw' (by positivity)
  · have hre : u.re ≤ a := le_trans (Complex.re_le_norm _) hun
    have hq' : 0 ≤ 4 * (1 - q) := by linarith
    have hbr0 : 0 ≤ 4 * (1 - q) * (a * (a - u.re)) / (1 - a ^ 2) ^ 2 :=
      div_nonneg (mul_nonneg hq' (mul_nonneg ha0 (by linarith))) (sq_nonneg _)
    have hB0 : 0 ≤ t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p :=
      add_nonneg (by positivity) (mul_nonneg hσ hlog)
    refine le_trans (max_le (twoPointLocal_div_le_one_add hq0 hq1 ha0 ha1 hun)
      (by linarith)) ?_
    calc 1 + 4 * (1 - q) * (a * (a - u.re)) / (1 - a ^ 2) ^ 2
        ≤ 1 + 4 * (1 - q) * (1 / (p : ℝ) * (t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p))
            / (1 - a ^ 2) ^ 2 :=
          add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbr hq')
            (sq_nonneg _))
      _ = 1 + 4 * (1 - q) * (t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p)
            * ((1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2) := by
          rw [hsq]
          ring
      _ ≤ 1 + 4 * (1 - q) * (t ^ 2 * Real.log p ^ 2 / 2 + σ * Real.log p)
            * (1 / (p : ℝ) + 6 * (1 / (p : ℝ)) ^ 2) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hw (mul_nonneg hq' hB0))
      _ = 1 + (1 - q) * (2 * t ^ 2 * Real.log p ^ 2 + 4 * σ * Real.log p)
            * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := by ring

/-! ### The bound at one height -/

/-- `K₁ = ∑_p log p·(1/p + (2/3)(2-2q)/p²)` over the band `[y₀, y₁)`. -/
noncomputable def diffK₁ (y₀ y₁ : ℕ) (q : ℝ) : ℝ :=
  ∑ p ∈ primesIco y₀ y₁, Real.log p * (1 / (p : ℝ) + 2 / 3 * (2 - 2 * q) / (p : ℝ) ^ 2)

/-- `K₂ = ∑_p (log p)²·(1/p + 6/p²)` over the band `[y₀, y₁)`. -/
noncomputable def diffK₂ (y₀ y₁ : ℕ) : ℝ :=
  ∑ p ∈ primesIco y₀ y₁, Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)

/-- `K₃ = ∑_p log p·(1/p + 6/p²)` over the band `[y₀, y₁)`. -/
noncomputable def diffK₃ (y₀ y₁ : ℕ) : ℝ :=
  ∑ p ∈ primesIco y₀ y₁, Real.log p * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2)

/-- The bound `Q(σ, t)` of the normalised difference moment at `½ + σ + it` on the band
`[y₀, y₁)`: `(e^{(2q-1)rK₁} - 1)² + r²K₂·e^{(1-q)(2t²K₂ + 4σK₃)}`, `r = √(σ²+t²)`
(`RMF.integral_rpow_mul_normSq_sub_le`). -/
noncomputable def diffQ (y₀ y₁ : ℕ) (q σ t : ℝ) : ℝ :=
  (Real.exp ((2 * q - 1) * Real.sqrt (σ ^ 2 + t ^ 2) * diffK₁ y₀ y₁ q) - 1) ^ 2
    + (σ ^ 2 + t ^ 2) * diffK₂ y₀ y₁
      * Real.exp ((1 - q) * (2 * t ^ 2 * diffK₂ y₀ y₁ + 4 * σ * diffK₃ y₀ y₁))

lemma diffK₂_nonneg (y₀ y₁ : ℕ) : 0 ≤ diffK₂ y₀ y₁ :=
  Finset.sum_nonneg fun p _ => by positivity

lemma diffQ_nonneg (y₀ y₁ : ℕ) (q σ t : ℝ) : 0 ≤ diffQ y₀ y₁ q σ t :=
  add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by positivity) (diffK₂_nonneg y₀ y₁))
    (Real.exp_pos _).le)

lemma continuous_diffQ (y₀ y₁ : ℕ) (q σ : ℝ) : Continuous (diffQ y₀ y₁ q σ) := by
  unfold diffQ
  fun_prop

set_option maxHeartbeats 400000 in
-- the product bookkeeping over the band
/-- **The normalised difference moment at one height, bounded.**  For `½ ≤ q ≤ 1`, `σ ≥ 0` and
real `t`, with `F` the band product over `[y₀, y₁)`:

`E[‖F(½)‖^{2q-2}‖F(½) - F(½+σ+it)‖²] ≤ Q(σ, t)·E‖F(½)‖^{2q}`,  `Q = RMF.diffQ`.

The three moments in closed form (`RMF.integral_rpow_mul_normSq_sub_eq_prod`), their normalised
shape (`RMF.one_add_prod_sub_two_re_prod_le`) and the per-prime bounds
(`RMF.prime_difference_inputs`). -/
theorem integral_rpow_mul_normSq_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {q σ : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hσ : 0 ≤ σ) (t : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          (1 / 2 : ℂ) ω‖ ^ (2 * q - 2)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (1 / 2 : ℂ) ω
          - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ diffQ y₀ y₁ q σ t
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hsre : ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by simp
  have hid := integral_rpow_mul_normSq_sub_eq_prod hX y₀ y₁ (q := q) (by linarith) hq1
    (s := (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hsre]; linarith)
  have hplain : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
      (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) := by
    rw [hf.integral_norm_randomEulerProductIco_rpow_of_pos y₀ y₁ (by norm_num) q]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    have ha0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have ha1 : (p : ℝ) ^ (-(1 / 2) : ℝ) < 1 := prime_rpow_neg_lt_one hpp (by norm_num)
    rw [cpow_neg_half_eq, integral_plain_rademacherLaw_eq ha0 ha1, plainLocal]
  rw [hid, hplain]
  -- opaque names for the local quantities
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ, m = fun p : ℕ => plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, R = fun p : ℕ => twoPointLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
      ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℂ, E = fun p : ℕ => crossLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
      ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) := ⟨_, rfl⟩
  have hm1 : ∀ p ∈ primesIco y₀ y₁, 1 ≤ m p := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    simp only [hm]
    exact one_le_plainLocal hq0 (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (prime_rpow_neg_lt_one hpp (by norm_num))
  have hinputs : ∀ p ∈ primesIco y₀ y₁,
      ‖E p / (m p : ℂ) - 1‖
        ≤ (2 * q - 1) * Real.sqrt (σ ^ 2 + t ^ 2)
          * (Real.log p * (1 / (p : ℝ) + 2 / 3 * (2 - 2 * q) / (p : ℝ) ^ 2))
      ∧ R p / m p - ‖E p / (m p : ℂ)‖ ^ 2
        ≤ (σ ^ 2 + t ^ 2) * (Real.log p ^ 2 * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2))
      ∧ max (R p / m p) 1
        ≤ 1 + (1 - q) * (2 * t ^ 2 * Real.log p ^ 2 + 4 * σ * Real.log p)
            * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := by
    intro p hp
    simp only [hm, hR, hE]
    exact prime_difference_inputs (prime_of_mem_primesIco hp) hq0 hq1 hσ t
  have hvar : ∀ p ∈ primesIco y₀ y₁, ‖E p / (m p : ℂ)‖ ^ 2 ≤ R p / m p := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    simp only [hm, hR, hE]
    exact normSq_crossLocal_div_le hq0 (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (prime_rpow_neg_lt_one hpp (by norm_num)) _
  have hprodm : ∏ p ∈ primesIco y₀ y₁, plainLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
      = ∏ p ∈ primesIco y₀ y₁, m p := by rw [hm]
  have hprodR : ∏ p ∈ primesIco y₀ y₁, twoPointLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
      ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)))
      = ∏ p ∈ primesIco y₀ y₁, R p := by
    rw [hR]
  have hprodE : ∏ p ∈ primesIco y₀ y₁, crossLocal q ((p : ℝ) ^ (-(1 / 2) : ℝ))
      ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)))
      = ∏ p ∈ primesIco y₀ y₁, E p := by
    rw [hE]
  rw [hprodm, hprodR, hprodE]
  -- normalise
  have hM : 0 < ∏ p ∈ primesIco y₀ y₁, m p :=
    Finset.prod_pos fun p hp => by linarith [hm1 p hp]
  have hRn : ∏ p ∈ primesIco y₀ y₁, R p
      = (∏ p ∈ primesIco y₀ y₁, m p) * ∏ p ∈ primesIco y₀ y₁, (R p / m p) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := hm1 p hp
    field_simp
  have hEn : ∏ p ∈ primesIco y₀ y₁, E p
      = ((∏ p ∈ primesIco y₀ y₁, m p : ℝ) : ℂ) * ∏ p ∈ primesIco y₀ y₁, (E p / (m p : ℂ)) := by
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have h0 : (m p : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; linarith [hm1 p hp]
    field_simp
  rw [hRn, hEn, Complex.re_ofReal_mul]
  have hshape := one_add_prod_sub_two_re_prod_le (primesIco y₀ y₁) (fun p => E p / (m p : ℂ))
    (fun p => R p / m p) hvar
  -- the three bounds
  set K₁ := diffK₁ y₀ y₁ q with hK₁
  set K₂ := diffK₂ y₀ y₁ with hK₂
  set K₃ := diffK₃ y₀ y₁ with hK₃
  set r := Real.sqrt (σ ^ 2 + t ^ 2) with hr
  have hS1 : ∑ p ∈ primesIco y₀ y₁, ‖E p / (m p : ℂ) - 1‖ ≤ (2 * q - 1) * r * K₁ := by
    rw [hK₁, diffK₁, Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hinputs p hp).1
  have hS2 : ∑ p ∈ primesIco y₀ y₁, (R p / m p - ‖E p / (m p : ℂ)‖ ^ 2)
      ≤ (σ ^ 2 + t ^ 2) * K₂ := by
    rw [hK₂, diffK₂, Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hinputs p hp).2.1
  have hS3 : ∏ p ∈ primesIco y₀ y₁, max (R p / m p) 1
      ≤ Real.exp ((1 - q) * (2 * t ^ 2 * K₂ + 4 * σ * K₃)) := by
    have hx : ∀ p : ℕ, 0 ≤ (1 - q) * (2 * t ^ 2 * Real.log p ^ 2 + 4 * σ * Real.log p)
        * (1 / (p : ℝ) + 6 / (p : ℝ) ^ 2) := fun p => by
      have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
      exact mul_nonneg (mul_nonneg (by linarith) (add_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) hσ) hl))) (by positivity)
    refine le_trans (Finset.prod_le_prod (fun p _ => le_trans zero_le_one (le_max_right _ _))
      fun p hp => (hinputs p hp).2.2) (le_trans (Real.prod_one_add_le_exp_sum _ hx) ?_)
    refine le_of_eq (congrArg Real.exp ?_)
    rw [hK₂, hK₃, diffK₂, diffK₃, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hK₂0 : 0 ≤ K₂ := diffK₂_nonneg y₀ y₁
  have hA0 : 0 ≤ Real.exp (∑ p ∈ primesIco y₀ y₁, ‖E p / (m p : ℂ) - 1‖) - 1 := by
    linarith [Real.add_one_le_exp (∑ p ∈ primesIco y₀ y₁, ‖E p / (m p : ℂ) - 1‖),
      Finset.sum_nonneg fun p (_ : p ∈ primesIco y₀ y₁) => norm_nonneg (E p / (m p : ℂ) - 1)]
  have hA : (Real.exp (∑ p ∈ primesIco y₀ y₁, ‖E p / (m p : ℂ) - 1‖) - 1) ^ 2
      ≤ (Real.exp ((2 * q - 1) * r * K₁) - 1) ^ 2 :=
    pow_le_pow_left₀ hA0 (by linarith [Real.exp_le_exp.2 hS1]) 2
  have hB : (∑ p ∈ primesIco y₀ y₁, (R p / m p - ‖E p / (m p : ℂ)‖ ^ 2))
        * ∏ p ∈ primesIco y₀ y₁, max (R p / m p) 1
      ≤ (σ ^ 2 + t ^ 2) * K₂ * Real.exp ((1 - q) * (2 * t ^ 2 * K₂ + 4 * σ * K₃)) :=
    mul_le_mul hS2 hS3 (Finset.prod_nonneg fun p _ => le_trans zero_le_one (le_max_right _ _))
      (mul_nonneg (by positivity) hK₂0)
  have hkey : 1 + ∏ p ∈ primesIco y₀ y₁, (R p / m p)
      - 2 * (∏ p ∈ primesIco y₀ y₁, (E p / (m p : ℂ))).re
      ≤ diffQ y₀ y₁ q σ t := by
    change _ ≤ (Real.exp ((2 * q - 1) * r * K₁) - 1) ^ 2
      + (σ ^ 2 + t ^ 2) * K₂ * Real.exp ((1 - q) * (2 * t ^ 2 * K₂ + 4 * σ * K₃))
    linarith
  have heq : (∏ p ∈ primesIco y₀ y₁, m p)
        + (∏ p ∈ primesIco y₀ y₁, m p) * ∏ p ∈ primesIco y₀ y₁, (R p / m p)
      - 2 * ((∏ p ∈ primesIco y₀ y₁, m p) * (∏ p ∈ primesIco y₀ y₁, (E p / (m p : ℂ))).re)
      = (1 + ∏ p ∈ primesIco y₀ y₁, (R p / m p)
          - 2 * (∏ p ∈ primesIco y₀ y₁, (E p / (m p : ℂ))).re) * ∏ p ∈ primesIco y₀ y₁, m p := by
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hkey hM.le

/-! ### Hölder over a window -/

/-- **Hölder against a plain observable, over a window**, bounded version.  For `0 < q ≤ 1`, `N`
measurable with `c ≤ N ≤ C` almost surely (`c > 0`), `G ≥ 0` jointly measurable and bounded, and a
per-height bound `E[N^{q-1}G(·,t)] ≤ B(t)·E[N^q]` on `[a, b]` with `B ≥ 0` integrable there:
`E[(∫_a^b G(·,t)dt)^q] ≤ (∫_a^b B)^q·E[N^q]`.  `RMF.integral_rpow_le_of_mixed_le` with Fubini; the
degenerate case `E[N^{q-1}W] = 0` forces `W = 0` almost surely. -/
theorem integral_rpow_setIntegral_le_of_mixed {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : Ω → ℝ} {G : Ω → ℝ → ℝ} {B : ℝ → ℝ} {a b q c C D : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hNm : Measurable N) (hN : ∀ᵐ ω ∂μ, c ≤ N ω ∧ N ω ≤ C)
    (hGm : Measurable (Function.uncurry G)) (hG0 : ∀ ω t, 0 ≤ G ω t)
    (hGD : ∀ᵐ ω ∂μ, ∀ t, G ω t ≤ D)
    (hB0 : ∀ t, 0 ≤ B t) (hBi : IntegrableOn B (Set.Icc a b))
    (hper : ∀ t ∈ Set.Icc a b, (∫ ω, N ω ^ (q - 1) * G ω t ∂μ) ≤ B t * ∫ ω, N ω ^ q ∂μ) :
    (∫ ω, (∫ t in Set.Icc a b, G ω t) ^ q ∂μ)
      ≤ (∫ t in Set.Icc a b, B t) ^ q * ∫ ω, N ω ^ q ∂μ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  set len : ℝ := volume.real (Set.Icc a b) with hlen
  have hlen0 : 0 ≤ len := measureReal_nonneg
  set W : Ω → ℝ := fun ω => ∫ t in Set.Icc a b, G ω t with hW
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => integral_nonneg fun t => hG0 ω t
  have hWD : ∀ᵐ ω ∂μ, W ω ≤ D * len := by
    filter_upwards [hGD] with ω hω
    have h := norm_setIntegral_le_of_norm_le_const (s := Set.Icc a b)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) (C := D)
      (f := fun t => G ω t) (fun t _ => by
        rw [Real.norm_of_nonneg (hG0 ω t)]; exact hω t)
    rw [Real.norm_of_nonneg (hW0 ω)] at h
    exact h
  have hWm : Measurable W :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc a b))
      hGm.stronglyMeasurable).measurable
  -- integrabilities
  have hNq : Integrable (fun ω => N ω ^ q) μ := by
    refine (memLp_top_of_bound (hNm.pow_const q).aestronglyMeasurable (C ^ q) ?_).integrable le_top
    filter_upwards [hN] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans hc.le hω.1) _)]
    exact Real.rpow_le_rpow (le_trans hc.le hω.1) hω.2 hq0.le
  have hNq1 : ∀ᵐ ω ∂μ, N ω ^ (q - 1) ≤ c ^ (q - 1) := by
    filter_upwards [hN] with ω hω
    exact Real.rpow_le_rpow_of_nonpos hc hω.1 (by linarith)
  have hABi : Integrable (fun ω => N ω ^ (q - 1) * W ω) μ := by
    refine (memLp_top_of_bound ((hNm.pow_const _).mul hWm).aestronglyMeasurable
      (c ^ (q - 1) * (D * len)) ?_).integrable le_top
    filter_upwards [hN, hNq1, hWD] with ω hω h1 hwd
    simp only [Pi.mul_apply]
    have h0 : 0 ≤ N ω ^ (q - 1) := Real.rpow_nonneg (le_trans hc.le hω.1) _
    rw [Real.norm_of_nonneg (mul_nonneg h0 (hW0 ω))]
    exact mul_le_mul h1 hwd (hW0 ω) (Real.rpow_nonneg hc.le _)
  have hWq : Integrable (fun ω => W ω ^ q) μ := by
    refine (memLp_top_of_bound (hWm.pow_const q).aestronglyMeasurable ((D * len) ^ q) ?_
      ).integrable le_top
    filter_upwards [hWD] with ω hwd
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hW0 ω) _)]
    exact Real.rpow_le_rpow (hW0 ω) hwd hq0.le
  have hα : 0 < ∫ ω, N ω ^ q ∂μ := by
    have hlow : ∀ᵐ ω ∂μ, c ^ q ≤ N ω ^ q := by
      filter_upwards [hN] with ω hω
      exact Real.rpow_le_rpow hc.le hω.1 hq0.le
    have h := integral_mono_ae (integrable_const (c ^ q)) hNq hlow
    rw [integral_const, probReal_univ, one_smul] at h
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hc q) h
  have hκ : 0 ≤ ∫ t in Set.Icc a b, B t := setIntegral_nonneg measurableSet_Icc fun t _ => hB0 t
  -- the mixed moment, by Fubini
  have hbd : (∫ ω, N ω ^ (q - 1) * W ω ∂μ)
      ≤ (∫ t in Set.Icc a b, B t) * ∫ ω, N ω ^ q ∂μ := by
    have hprod : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => N ω ^ (q - 1) * G ω t)
        (μ.prod (volume.restrict (Set.Icc a b))) := by
      have hmeas : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) => N ω ^ (q - 1) * G ω t) :=
        ((hNm.pow_const _).comp measurable_fst).mul hGm
      refine (memLp_top_of_bound hmeas.aestronglyMeasurable (c ^ (q - 1) * D) ?_).integrable
        le_top
      have hae : ∀ᵐ z ∂(μ.prod (volume.restrict (Set.Icc a b))),
          (c ≤ N z.1 ∧ N z.1 ≤ C) ∧ ∀ t, G z.1 t ≤ D :=
        (Measure.quasiMeasurePreserving_fst (μ := μ)
          (ν := volume.restrict (Set.Icc a b))).ae (hN.and hGD)
      filter_upwards [hae] with z hzz
      have hz := hzz.1
      change ‖N z.1 ^ (q - 1) * G z.1 z.2‖ ≤ c ^ (q - 1) * D
      have h0 : 0 ≤ N z.1 ^ (q - 1) := Real.rpow_nonneg (le_trans hc.le hz.1) _
      rw [Real.norm_of_nonneg (mul_nonneg h0 (hG0 _ _))]
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hc hz.1 (by linarith)) (hzz.2 _)
        (hG0 _ _) (Real.rpow_nonneg hc.le _)
    have hpull : ∀ ω, N ω ^ (q - 1) * W ω = ∫ t in Set.Icc a b, N ω ^ (q - 1) * G ω t := by
      intro ω
      rw [hW]
      exact (integral_const_mul _ _).symm
    simp_rw [hpull]
    rw [integral_integral_swap hprod]
    have hinner : IntegrableOn (fun t => ∫ ω, N ω ^ (q - 1) * G ω t ∂μ) (Set.Icc a b) :=
      hprod.integral_prod_right
    calc (∫ t in Set.Icc a b, ∫ ω, N ω ^ (q - 1) * G ω t ∂μ)
        ≤ ∫ t in Set.Icc a b, B t * ∫ ω, N ω ^ q ∂μ :=
          setIntegral_mono_on hinner (hBi.mul_const _) measurableSet_Icc hper
      _ = (∫ t in Set.Icc a b, B t) * ∫ ω, N ω ^ q ∂μ := integral_mul_const _ _
  -- the degenerate case
  have hβ0 : 0 ≤ ∫ ω, N ω ^ (q - 1) * W ω ∂μ := integral_nonneg_of_ae (by
    filter_upwards [hN] with ω hω
    exact mul_nonneg (Real.rpow_nonneg (le_trans hc.le hω.1) _) (hW0 ω))
  rcases eq_or_lt_of_le hβ0 with h0 | hβ
  · have hz : (fun ω => N ω ^ (q - 1) * W ω) =ᵐ[μ] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hABi).1 h0.symm
      filter_upwards [hN] with ω hω
      exact mul_nonneg (Real.rpow_nonneg (le_trans hc.le hω.1) _) (hW0 ω)
    have hWz : ∀ᵐ ω ∂μ, W ω ^ q = 0 := by
      filter_upwards [hz, hN] with ω hω hNω
      have hpos : 0 < N ω ^ (q - 1) := Real.rpow_pos_of_pos (lt_of_lt_of_le hc hNω.1) _
      have hWω : W ω = 0 := by
        rcases mul_eq_zero.1 hω with h | h
        · exact absurd h hpos.ne'
        · exact h
      rw [hWω, Real.zero_rpow hq0.ne']
    rw [integral_congr_ae hWz, integral_zero]
    exact mul_nonneg (Real.rpow_nonneg hκ _) hα.le
  · have hN0 : ∀ᵐ ω ∂μ, 0 < N ω := by
      filter_upwards [hN] with ω hω
      exact lt_of_lt_of_le hc hω.1
    exact integral_rpow_le_of_mixed_le hq0.le hq1 hN0 (.of_forall hW0) hNq hABi hWq hα hβ hκ hbd

/-! ### The central window -/

/-- **The central window of the difference form.**  For `½ ≤ q ≤ 1`, `σ > 0`, `L > 0` and any
`τ`, with `F` the band product over `[y₀, y₁)`:

`E[(∫_{-τ}^{τ}L⁻¹(σ²+t²)⁻¹‖F(½) - F(½+σ+it)‖²dt)^q]
  ≤ (∫_{-τ}^{τ}L⁻¹(σ²+t²)⁻¹Q(σ,t)dt)^q·E‖F(½)‖^{2q}`,

`Q = RMF.diffQ`: Hölder against `‖F(½)‖^{2q-2}` over the window
(`RMF.integral_rpow_setIntegral_le_of_mixed`) and the per-height bound
(`RMF.integral_rpow_mul_normSq_sub_le`). -/
theorem integral_rpow_centralWindow_diff_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {q σ L τ : ℝ} (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) (hσ : 0 < σ) (hL : 0 < L) :
    (∫ ω, (∫ t in Set.Icc (-τ) τ, L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (1 / 2 : ℂ) ω
          - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ)
      ≤ (∫ t in Set.Icc (-τ) τ, L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t) ^ q
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
            (1 / 2 : ℂ) ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  set F : ℂ → Ω → ℂ := fun w ω =>
    randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ w ω with hFdef
  -- measurability
  have hjoint0 := measurable_uncurry_randomEulerProductIco_line hX y₀ y₁ 0
  have hjoint := measurable_uncurry_randomEulerProductIco_line hX y₀ y₁ (-σ)
  have hline : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) := by
    convert hjoint using 1
    funext z
    obtain ⟨ω, t⟩ := z
    simp [hFdef]
  have hF0m : Measurable (F (1 / 2 : ℂ)) := by
    have h := hjoint0.comp (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
    convert h using 1
    funext ω
    simp [hFdef]
  -- the envelope
  set Lo : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) with hLo
  set Up : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) with hUp
  set Upσ : ℝ := ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hUpσ
  have hLo0 : 0 < Lo := Finset.prod_pos fun p hp => by
    have := prime_rpow_neg_lt_one (prime_of_mem_primesIco hp) (c := 1 / 2) (by norm_num)
    linarith
  have henv := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := 1 / 2)
    (by norm_num)
  have henvσ := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁ (c := 1 / 2 + σ)
    (by linarith)
  have hre0 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hret : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ :=
    fun t => by simp
  have hN : ∀ᵐ ω ∂μ, Lo ^ 2 ≤ ‖F (1 / 2 : ℂ) ω‖ ^ 2 ∧ ‖F (1 / 2 : ℂ) ω‖ ^ 2 ≤ Up ^ 2 := by
    filter_upwards [henv] with ω hω
    have h := hω (1 / 2 : ℂ) hre0
    exact ⟨pow_le_pow_left₀ hLo0.le h.1 2, pow_le_pow_left₀ (norm_nonneg _) h.2 2⟩
  have hGD : ∀ᵐ ω ∂μ, ∀ t : ℝ, L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
      * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        ≤ L⁻¹ * (σ ^ 2)⁻¹ * (Up + Upσ) ^ 2 := by
    filter_upwards [henv, henvσ] with ω hω hωσ t
    have h0 := (hω (1 / 2 : ℂ) hre0).2
    have h1 := (hωσ _ (hret t)).2
    have hsub : ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ Up + Upσ := le_trans (norm_sub_le _ _) (add_le_add h0 h1)
    have hw : (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith [sq_nonneg t])
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hsub 2
    have hL0 : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw hL0) hsq (sq_nonneg _)
      (mul_nonneg hL0 (inv_nonneg.2 (by positivity)))
  have hB0 : ∀ t : ℝ, 0 ≤ L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t := fun t =>
    mul_nonneg (mul_nonneg (inv_nonneg.2 hL.le) (inv_nonneg.2 (by positivity)))
      (diffQ_nonneg y₀ y₁ q σ t)
  have hBc : Continuous fun t : ℝ => L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t := by
    have hc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun t => (by positivity : (0 : ℝ) < σ ^ 2 + t ^ 2).ne'
    exact (continuous_const.mul hc).mul (continuous_diffQ y₀ y₁ q σ)
  have hper : ∀ t ∈ Set.Icc (-τ) τ,
      (∫ ω, (‖F (1 / 2 : ℂ) ω‖ ^ 2) ^ (q - 1) * (L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
          * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ∂μ)
        ≤ L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t
          * ∫ ω, (‖F (1 / 2 : ℂ) ω‖ ^ 2) ^ q ∂μ := by
    intro t _
    have hbase := integral_rpow_mul_normSq_sub_le hX y₀ y₁ hq0 hq1 hσ.le t
    have hrw : ∀ ω, (‖F (1 / 2 : ℂ) ω‖ ^ 2) ^ (q - 1) * (L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
          * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
        = L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * (‖F (1 / 2 : ℂ) ω‖ ^ (2 * q - 2)
          * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) := by
      intro ω
      rw [← norm_rpow_two_mul, show 2 * (q - 1) = 2 * q - 2 by ring]
      ring
    have hrw2 : ∀ ω, (‖F (1 / 2 : ℂ) ω‖ ^ 2) ^ q = ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) := fun ω =>
      (norm_rpow_two_mul _ q).symm
    simp_rw [hrw, hrw2]
    rw [integral_const_mul]
    have hw0 : 0 ≤ L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ :=
      mul_nonneg (inv_nonneg.2 hL.le) (inv_nonneg.2 (by positivity))
    have := mul_le_mul_of_nonneg_left hbase hw0
    linarith
  have hGm : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) => L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
      * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) := by
    have hc : Measurable fun z : Ω × ℝ => L⁻¹ * (σ ^ 2 + z.2 ^ 2)⁻¹ := by fun_prop
    exact hc.mul ((((hF0m.comp measurable_fst).sub hline).norm).pow_const 2)
  have hmain := integral_rpow_setIntegral_le_of_mixed (μ := μ)
    (N := fun ω => ‖F (1 / 2 : ℂ) ω‖ ^ 2)
    (G := fun ω t => L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹
      * ‖F (1 / 2 : ℂ) ω - F ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
    (B := fun t => L⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ * diffQ y₀ y₁ q σ t) (a := -τ) (b := τ)
    (by linarith) hq1 (pow_pos hLo0 2) (hF0m.norm.pow_const 2) hN hGm
    (fun ω t => by positivity) hGD hB0 hBc.integrableOn_Icc hper
  have hrw2 : ∀ ω, (‖F (1 / 2 : ℂ) ω‖ ^ 2) ^ q = ‖F (1 / 2 : ℂ) ω‖ ^ (2 * q) := fun ω =>
    (norm_rpow_two_mul _ q).symm
  simp_rw [hrw2] at hmain
  exact hmain

end RMF
