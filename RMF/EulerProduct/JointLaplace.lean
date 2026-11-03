/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.LogField
import RMF.EulerProduct.Tilted
import RMF.EulerProduct.Block
import RMF.NumberTheory.LogPrimeSum

/-!
# The joint Laplace transform (Hamdan's Lemma B.1)

The chaining argument of Lemma B.2 of Hamdan, *Partial sums of random multiplicative functions
with supercritical divisor twists* (arXiv:2604.05563), needs a *joint* tail bound,

`P( S_j(σ) ≥ V₁, S_j(σ+ih₁) - S_j(σ+ih₂) ≥ V₂ ) ≪ exp(-V₁²/j - c V₂^{3/2}/(e^j|h₂-h₁|))`,

and Hamdan gets it by a Chernoff bound on

`E exp(λ₁ S_j(σ) + λ₂ (S_j(σ+ih₁) - S_j(σ+ih₂)))`.

Cauchy–Schwarz cannot decouple the two events — halving both Gaussian exponents is fatal — so the
joint transform is genuinely required.

## What this file builds

Written multiplicatively, that Laplace transform is a joint moment of the Euler product at three
abscissas with exponents `(λ₁, λ₂, -λ₂)`, one of them **negative**.  So the local theory is needed
at negative real exponents and at several weights at once; the factorisation over the primes
(`RMF.integral_prod_norm_randomEulerProductIco_rpow_compMult`) already allows either sign.

The multi-weight local expansion is

`E_z ∏_a ‖(1 - z w_a)⁻¹‖ ^ (2 q_a) = 1 + ‖∑_a q_a w_a‖² + O(‖w‖³)`.

Its second-order coefficient is `RMF.sum_sum_re_mul_conj_eq_norm_sq`, which specialises to
`q²‖w‖²` at one weight and to Harper's `(2 + 2cos((t₁-t₂)log p))p^{-2σ}` at two.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {ι : Type*}

/-! ### Deterministic bounds on the circle -/

/-- The weighted truncation sum is `O(Q · |A| · t)` pointwise. -/
lemma abs_sum_smul_localTaylorTwo_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {z : ℂ} {Q t : ℝ}
    (hz : ‖z‖ = 1) (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t) (ht : t ≤ 1) :
    |∑ a ∈ A, q a * localTaylorTwo (w a) z| ≤ 2 * (Q * A.card) * t := by
  have hterm : ∀ a ∈ A, |q a * localTaylorTwo (w a) z| ≤ 2 * Q * t := by
    intro a ha
    have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) (hq a ha)
    have ht0 : 0 ≤ t := le_trans (norm_nonneg _) (hw a ha)
    have hwa : ‖w a‖ ≤ 1 := le_trans (hw a ha) ht
    have hloc := abs_localTaylorTwo_le hz hwa
    calc |q a * localTaylorTwo (w a) z| = |q a| * |localTaylorTwo (w a) z| := abs_mul _ _
      _ ≤ Q * (2 * t) := by
          refine mul_le_mul (hq a ha) (le_trans hloc (by linarith [hw a ha])) (abs_nonneg _) hQ0
      _ = 2 * Q * t := by ring
  calc |∑ a ∈ A, q a * localTaylorTwo (w a) z|
      ≤ ∑ a ∈ A, |q a * localTaylorTwo (w a) z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ A, 2 * Q * t := Finset.sum_le_sum hterm
    _ = 2 * (Q * A.card) * t := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The weighted local-log sum is at most `Q|A| log(1/(1-θ))` on the circle for `‖w_a‖ ≤ θ < 1`,
with no smallness in `θ`. -/
lemma abs_sum_smul_localLog_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {z : ℂ} {Q θ : ℝ}
    (hz : ‖z‖ = 1) (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ θ) (hθ : θ < 1) :
    |∑ a ∈ A, q a * localLog (w a) z| ≤ (Q * A.card) * Real.log ((1 - θ)⁻¹) := by
  have hterm : ∀ a ∈ A, |q a * localLog (w a) z| ≤ Q * Real.log ((1 - θ)⁻¹) := by
    intro a ha
    have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) (hq a ha)
    have hL0 : 0 ≤ Real.log ((1 - θ)⁻¹) := by
      have h1 : (0 : ℝ) < 1 - θ := by linarith
      have ht0 : (0 : ℝ) ≤ ‖w a‖ := norm_nonneg _
      refine Real.log_nonneg (one_le_inv_iff₀.mpr ⟨h1, by linarith [hw a ha]⟩)
    calc |q a * localLog (w a) z| = |q a| * |localLog (w a) z| := abs_mul _ _
      _ ≤ Q * Real.log ((1 - θ)⁻¹) :=
          mul_le_mul (hq a ha) (abs_localLog_le hz (hw a ha) hθ) (abs_nonneg _) hQ0
  calc |∑ a ∈ A, q a * localLog (w a) z|
      ≤ ∑ a ∈ A, |q a * localLog (w a) z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ A, Q * Real.log ((1 - θ)⁻¹) := Finset.sum_le_sum hterm
    _ = (Q * A.card) * Real.log ((1 - θ)⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The weight vector: `‖∑_a q_a w_a‖ ≤ Q · |A| · t` when `|q_a| ≤ Q` and `‖w_a‖ ≤ t` on `A`. -/
lemma norm_sum_smul_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {Q t : ℝ}
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t) :
    ‖∑ a ∈ A, (q a : ℂ) * w a‖ ≤ (Q * A.card) * t := by
  have hterm : ∀ a ∈ A, ‖(q a : ℂ) * w a‖ ≤ Q * t := by
    intro a ha
    have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) (hq a ha)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hq a ha) (hw a ha) (norm_nonneg _) hQ0
  calc ‖∑ a ∈ A, (q a : ℂ) * w a‖ ≤ ∑ a ∈ A, ‖(q a : ℂ) * w a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ A, Q * t := Finset.sum_le_sum hterm
    _ = (Q * A.card) * t := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ### The joint exponent and its quadratic model -/

/-- **The joint exponent.**  `∑_a λ_a localLog(w_a, z)` with `λ_a = 2 q_a`: writing a joint moment
of the Euler product as `exp` of this is `RMF.prod_norm_inv_one_sub_rpow_eq_exp`. -/
noncomputable def logExponent (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) (z : ℂ) : ℝ :=
  2 * ∑ a ∈ A, q a * localLog (w a) z

/-- Its degree-two truncation, obtained by replacing each `localLog` by `localTaylorTwo`. -/
noncomputable def taylorExponent (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) (z : ℂ) : ℝ :=
  2 * ∑ a ∈ A, q a * localTaylorTwo (w a) z

lemma measurable_logExponent (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    Measurable (logExponent A q w) := by
  unfold logExponent
  exact (Finset.measurable_sum _ fun a _ => (measurable_localLog _).const_mul _).const_mul _

lemma measurable_taylorExponent (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    Measurable (taylorExponent A q w) := by
  unfold taylorExponent
  exact (Finset.measurable_sum _ fun a _ =>
    (measurable_localTaylorTwo _).const_mul _).const_mul _

/-- The pointwise bound on the quadratic model, from `RMF.abs_sum_smul_localTaylorTwo_le`. -/
lemma abs_taylorExponent_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {z : ℂ} {Q t : ℝ}
    (hz : ‖z‖ = 1) (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t) (ht : t ≤ 1) :
    |taylorExponent A q w z| ≤ 4 * (Q * A.card) * t := by
  unfold taylorExponent
  rw [abs_mul, abs_two]
  linarith [abs_sum_smul_localTaylorTwo_le hz hq hw ht]

/-- The pointwise bound on the exponent itself, `|logExponent| ≤ 2Q|A| log(1/(1-θ))` for
`‖w_a‖ ≤ θ < 1`, with no smallness in `θ`. -/
lemma abs_logExponent_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {z : ℂ} {Q θ : ℝ}
    (hz : ‖z‖ = 1) (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ θ) (hθ : θ < 1) :
    |logExponent A q w z| ≤ 2 * (Q * A.card) * Real.log ((1 - θ)⁻¹) := by
  unfold logExponent
  rw [abs_mul, abs_two]
  linarith [abs_sum_smul_localLog_le hz hq hw hθ]

/-- The transfer bound between the two, from
`RMF.abs_sum_smul_localLog_sub_sum_smul_localTaylorTwo_le`. -/
lemma abs_logExponent_sub_taylorExponent_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {z : ℂ}
    {Q t : ℝ} (hz : ‖z‖ = 1) (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t)
    (ht : t ≤ 1 / 5) :
    |logExponent A q w z - taylorExponent A q w z| ≤ 24 * (Q * A.card) * t ^ 3 := by
  unfold logExponent taylorExponent
  rw [← mul_sub, abs_mul, abs_two]
  linarith [abs_sum_smul_localLog_sub_sum_smul_localTaylorTwo_le hz hq hw ht]

/-! ### The two moments of the quadratic model -/

/-- The model is centred: each `localTaylorTwo` is. -/
lemma integral_taylorExponent (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    (∫ z, taylorExponent A q w z ∂steinhausLaw) = 0 := by
  unfold taylorExponent
  rw [integral_const_mul, integral_finsetSum A fun a _ =>
    (integrable_localTaylorTwo (w a)).const_mul _]
  simp [integral_const_mul, integral_localTaylorTwo]

/-- Its second moment, from `RMF.integral_sum_smul_localTaylorTwo_sq`. -/
lemma integral_taylorExponent_sq (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    (∫ z, taylorExponent A q w z ^ 2 ∂steinhausLaw)
      = 2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 2 := by
  have hexp : ∀ z : ℂ, taylorExponent A q w z ^ 2
      = 4 * (∑ a ∈ A, q a * localTaylorTwo (w a) z) ^ 2 := by
    intro z
    unfold taylorExponent
    ring
  simp_rw [hexp]
  rw [integral_const_mul, integral_sum_smul_localTaylorTwo_sq]
  ring

/-! ### The expansion, in the small-`t` regime

`K = Q·|A|` is the size parameter: `|taylorExponent| ≤ 4Kt`, so `4Kt ≤ 1` is exactly what makes
`RMF.abs_exp_sub_taylor_le` applicable.  Outside that range the estimate is recovered by the
two-regime device `RMF.le_mul_cube_of_two_regime`, since there `t³` is bounded below. -/

/-- **The multi-weight local expansion, fine regime**: for `t ≤ 1/5` and `4Kt ≤ 1`, `K = Q·|A|`,
`E_z ∏_a ‖(1 - z w_a)⁻¹‖^{2q_a} = 1 + ‖∑_a q_a w_a‖² + O(t³)`.  The three error terms are replacing
`exp(logExponent)` by `exp(taylorExponent)` (`48e·K·t³`), the quadratic Taylor remainder of `exp`
(`64K³t³`), and the quartic `‖∑_a q_a w_a²‖²/4` left in the second moment (`≤ K²t³/20`). -/
theorem abs_integral_prod_localIntegrand_sub_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    {Q t : ℝ} (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t) (hQ0 : 0 ≤ Q)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 5) (hsmall : 4 * (Q * A.card) * t ≤ 1) :
    |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
        - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)|
      ≤ (64 * (Q * A.card) ^ 3 + 48 * Real.exp 1 * (Q * A.card)
          + (Q * A.card) ^ 2 / 20) * t ^ 3 := by
  have hK0 : (0 : ℝ) ≤ Q * A.card := mul_nonneg hQ0 (Nat.cast_nonneg _)
  have hwlt : ∀ a ∈ A, ‖w a‖ < 1 := fun a ha => lt_of_le_of_lt (hw a ha) (by linarith)
  have hLTsmall : 24 * (Q * A.card) * t ^ 3 ≤ 1 := by nlinarith [sq_nonneg t]
  -- pointwise facts on the circle
  have hae : ∀ᵐ z ∂steinhausLaw,
      (∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a)) = Real.exp (logExponent A q w z) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact prod_norm_inv_one_sub_rpow_eq_exp A q w hz hwlt
  have hTae : ∀ᵐ z ∂steinhausLaw, |taylorExponent A q w z| ≤ 1 := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact le_trans (abs_taylorExponent_le hz hq hw (by linarith)) hsmall
  have hLTae : ∀ᵐ z ∂steinhausLaw,
      |logExponent A q w z - taylorExponent A q w z| ≤ 24 * (Q * A.card) * t ^ 3 :=
    by filter_upwards [norm_eq_one_steinhausLaw] with z hz
       exact abs_logExponent_sub_taylorExponent_le hz hq hw ht
  have hLae : ∀ᵐ z ∂steinhausLaw, |logExponent A q w z| ≤ 2 := by
    filter_upwards [hTae, hLTae] with z h1 h2
    have h3 := abs_sub_abs_le_abs_sub (logExponent A q w z) (taylorExponent A q w z)
    linarith
  -- integrability, all from boundedness
  have hmT := measurable_taylorExponent A q w
  have hmL := measurable_logExponent A q w
  have hiT2 : Integrable (fun z => taylorExponent A q w z ^ 2) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (hmT.pow_const 2).aestronglyMeasurable 1 <| by
      filter_upwards [hTae] with z hz
      rw [Real.norm_eq_abs, abs_pow]
      nlinarith [abs_nonneg (taylorExponent A q w z)]
  have hiT : Integrable (taylorExponent A q w) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw hmT.aestronglyMeasurable 1 <| by
      filter_upwards [hTae] with z hz
      rwa [Real.norm_eq_abs]
  have hiexpT : Integrable (fun z => Real.exp (taylorExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      (Real.measurable_exp.comp hmT).aestronglyMeasurable (Real.exp 1) <| by
      filter_upwards [hTae] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 hz).2
  have hiexpL : Integrable (fun z => Real.exp (logExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      (Real.measurable_exp.comp hmL).aestronglyMeasurable (Real.exp 2) <| by
      filter_upwards [hLae] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 hz).2
  have hiquad₁ : Integrable (fun z : ℂ => 1 + taylorExponent A q w z) steinhausLaw :=
    (integrable_const 1).add hiT
  have hiquad : Integrable
      (fun z => 1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2) steinhausLaw :=
    hiquad₁.add (hiT2.div_const 2)
  rw [integral_congr_ae hae]
  -- step 1: `exp(logExponent)` against `exp(taylorExponent)`
  have hstep1 : |(∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
      - ∫ z, Real.exp (taylorExponent A q w z) ∂steinhausLaw|
      ≤ 48 * Real.exp 1 * (Q * A.card) * t ^ 3 := by
    rw [← integral_sub hiexpL hiexpT]
    have hb : ∀ᵐ z ∂steinhausLaw,
        ‖Real.exp (logExponent A q w z) - Real.exp (taylorExponent A q w z)‖
          ≤ 48 * Real.exp 1 * (Q * A.card) * t ^ 3 := by
      filter_upwards [hTae, hLTae] with z h1 h2
      have hid : Real.exp (logExponent A q w z) - Real.exp (taylorExponent A q w z)
          = Real.exp (taylorExponent A q w z)
            * (Real.exp (logExponent A q w z - taylorExponent A q w z) - 1) := by
        rw [mul_sub, ← Real.exp_add, mul_one]
        ring_nf
      have h4 : |logExponent A q w z - taylorExponent A q w z| ≤ 1 := le_trans h2 hLTsmall
      have h5 := Real.abs_exp_sub_one_le h4
      have h6 : Real.exp (taylorExponent A q w z) ≤ Real.exp 1 :=
        Real.exp_le_exp.2 (abs_le.1 h1).2
      rw [Real.norm_eq_abs, hid, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (taylorExponent A q w z)
            * |Real.exp (logExponent A q w z - taylorExponent A q w z) - 1|
          ≤ Real.exp 1 * (2 * (24 * (Q * A.card) * t ^ 3)) := by
            refine mul_le_mul h6 (le_trans h5 (by linarith)) (abs_nonneg _) (Real.exp_pos _).le
        _ = 48 * Real.exp 1 * (Q * A.card) * t ^ 3 := by ring
    have key := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at key
    simpa using key
  -- step 2: the quadratic Taylor remainder of `exp`
  have hstep2 : |(∫ z, Real.exp (taylorExponent A q w z) ∂steinhausLaw)
      - ∫ z, (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2) ∂steinhausLaw|
      ≤ 64 * (Q * A.card) ^ 3 * t ^ 3 := by
    rw [← integral_sub hiexpT hiquad]
    have hb : ∀ᵐ z ∂steinhausLaw,
        ‖Real.exp (taylorExponent A q w z)
            - (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2)‖
          ≤ 64 * (Q * A.card) ^ 3 * t ^ 3 := by
      filter_upwards [norm_eq_one_steinhausLaw, hTae] with z hz h1
      have hT4 := abs_taylorExponent_le hz hq hw (by linarith : t ≤ 1)
      have hcube : |taylorExponent A q w z| ^ 3 ≤ (4 * (Q * A.card) * t) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) hT4 3
      rw [Real.norm_eq_abs]
      calc |Real.exp (taylorExponent A q w z)
              - (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2)|
          ≤ |taylorExponent A q w z| ^ 3 := abs_exp_sub_taylor_le h1
        _ ≤ (4 * (Q * A.card) * t) ^ 3 := hcube
        _ = 64 * (Q * A.card) ^ 3 * t ^ 3 := by ring
    have key := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at key
    simpa using key
  -- step 3: the quadratic integrates to `1 + ‖u‖²` up to a quartic
  have hquad : (∫ z, (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2)
      ∂steinhausLaw)
      = 1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := by
    rw [integral_add hiquad₁ (hiT2.div_const 2), integral_add (integrable_const 1) hiT,
      integral_const, integral_taylorExponent, integral_div, integral_taylorExponent_sq]
    simp only [probReal_univ, smul_eq_mul, mul_one, add_zero]
    ring
  have hquart : ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 ≤ (Q * A.card) ^ 2 / 20 * t ^ 3 := by
    have hsq : ∀ a ∈ A, ‖w a ^ 2‖ ≤ t ^ 2 := by
      intro a ha
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hw a ha) 2
    have hv := norm_sum_smul_le (q := q) (w := fun a => w a ^ 2) hq hsq
    have hv0 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := norm_nonneg _
    have hsq2 : ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 ≤ ((Q * A.card) * t ^ 2) ^ 2 :=
      pow_le_pow_left₀ hv0 hv 2
    have hsq3 : ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 ≤ (Q * A.card) ^ 2 * t ^ 4 := by
      calc ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 ≤ ((Q * A.card) * t ^ 2) ^ 2 := hsq2
        _ = (Q * A.card) ^ 2 * t ^ 4 := by ring
    have hkey : (Q * A.card) ^ 2 * t ^ 4 / 4 ≤ (Q * A.card) ^ 2 / 20 * t ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (Q * (A.card : ℝ))) (pow_nonneg ht0 3))
        (by linarith : (0 : ℝ) ≤ 1 / 5 - t)]
    linarith
  rw [hquad] at hstep2
  have hfinal : |(∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
      - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)|
      ≤ 48 * Real.exp 1 * (Q * A.card) * t ^ 3 + 64 * (Q * A.card) ^ 3 * t ^ 3
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := by
    have h1 := abs_le.1 hstep1
    have h2 := abs_le.1 hstep2
    have h3 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := by positivity
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc |(∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
        - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)|
      ≤ 48 * Real.exp 1 * (Q * A.card) * t ^ 3 + 64 * (Q * A.card) ^ 3 * t ^ 3
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := hfinal
    _ ≤ 48 * Real.exp 1 * (Q * A.card) * t ^ 3 + 64 * (Q * A.card) ^ 3 * t ^ 3
        + (Q * A.card) ^ 2 / 20 * t ^ 3 := by linarith [hquart]
    _ = (64 * (Q * A.card) ^ 3 + 48 * Real.exp 1 * (Q * A.card)
          + (Q * A.card) ^ 2 / 20) * t ^ 3 := by ring

/-! ### Removing the smallness hypothesis

Where `4Kt > 1` the quantity `t³` is bounded below, so a crude bound on the whole expression is
already `O(t³)`.  `RMF.le_mul_cube_of_two_regime` packages that trade, exactly as
`RMF.exists_taylor_bound_one_sub_rpow` does for the scalar expansion. -/

/-- `log (5/4) ≤ 1/4`, the numeric fact behind the crude bound. -/
lemma log_five_quarters_le : Real.log ((1 - (1 / 5 : ℝ))⁻¹) ≤ 1 / 4 := by
  have h : ((1 : ℝ) - 1 / 5)⁻¹ = 5 / 4 := by norm_num
  rw [h]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  linarith

/-- **The crude bound**, valid on the whole range `t ≤ 1/5` with no smallness assumption.

Both sides are non-negative — the integrand is a product of norms — so the difference is at most
their sum, and each is bounded by an absolute constant in `K = Q·|A|`. -/
lemma abs_integral_prod_localIntegrand_sub_le_crude {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    {Q t : ℝ} (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ t) (hQ0 : 0 ≤ Q)
    (ht : t ≤ 1 / 5) :
    |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
        - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)|
      ≤ Real.exp (Q * A.card / 2) + (1 + (Q * A.card) ^ 2 / 25) := by
  have hK0 : (0 : ℝ) ≤ Q * A.card := mul_nonneg hQ0 (Nat.cast_nonneg _)
  have hwlt : ∀ a ∈ A, ‖w a‖ < 1 := fun a ha => lt_of_le_of_lt (hw a ha) (by linarith)
  have hae : ∀ᵐ z ∂steinhausLaw,
      (∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a)) = Real.exp (logExponent A q w z) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact prod_norm_inv_one_sub_rpow_eq_exp A q w hz hwlt
  have hLb : ∀ᵐ z ∂steinhausLaw,
      Real.exp (logExponent A q w z) ≤ Real.exp (Q * A.card / 2) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    refine Real.exp_le_exp.2 ?_
    have h1 := abs_logExponent_le hz hq (fun a ha => le_trans (hw a ha) ht)
      (by norm_num : (1 / 5 : ℝ) < 1)
    have h2 := (abs_le.1 h1).2
    have h3 : 2 * (Q * A.card) * Real.log ((1 - (1 / 5 : ℝ))⁻¹)
        ≤ 2 * (Q * A.card) * (1 / 4) :=
      mul_le_mul_of_nonneg_left log_five_quarters_le (by linarith)
    linarith
  have hiexpL : Integrable (fun z => Real.exp (logExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      ((Real.measurable_exp.comp (measurable_logExponent A q w))).aestronglyMeasurable
      (Real.exp (Q * A.card / 2)) <| by
      filter_upwards [hLb] with z hz
      rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [integral_congr_ae hae]
  have hup : (∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
      ≤ Real.exp (Q * A.card / 2) := by
    calc (∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
        ≤ ∫ _z, Real.exp (Q * A.card / 2) ∂steinhausLaw :=
          integral_mono_ae hiexpL (integrable_const _) hLb
      _ = Real.exp (Q * A.card / 2) := by simp
  have hlow : (0 : ℝ) ≤ ∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw :=
    integral_nonneg fun z => (Real.exp_pos _).le
  have hu0 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a‖ := norm_nonneg _
  have hu : ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 ≤ (Q * A.card) ^ 2 / 25 := by
    have h1 := norm_sum_smul_le hq hw
    have h2 : ‖∑ a ∈ A, (q a : ℂ) * w a‖ ≤ (Q * A.card) / 5 := by
      have := mul_le_mul_of_nonneg_left ht hK0
      linarith
    calc ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 ≤ ((Q * A.card) / 5) ^ 2 :=
          pow_le_pow_left₀ hu0 h2 2
      _ = (Q * A.card) ^ 2 / 25 := by ring
  have hu2 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith [Real.exp_pos (Q * A.card / 2)]

/-- **The multi-weight local expansion**, with no smallness hypothesis:

`E_z ∏_a ‖(1 - z w_a)⁻¹‖^{2q_a} = 1 + ‖∑_a q_a w_a‖² + O_{Q,A}(t³)`   for all `t ≤ 1/5`.

The local input to Hamdan's Lemma B.1. -/
theorem exists_local_multi_expansion_steinhausLaw (A : Finset ι) {Q : ℝ} (hQ0 : 0 ≤ Q) :
    ∃ C > 0, ∀ (q : ι → ℝ) (w : ι → ℂ) (t : ℝ),
      (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, ‖w a‖ ≤ t) → 0 ≤ t → t ≤ 1 / 5 →
        |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
            - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)| ≤ C * t ^ 3 := by
  have hK0 : (0 : ℝ) ≤ Q * A.card := mul_nonneg hQ0 (Nat.cast_nonneg _)
  set K : ℝ := Q * A.card with hKdef
  set d : ℝ := 1 / (4 * (K + 1)) with hddef
  have hd : 0 < d := by rw [hddef]; positivity
  set Cfine : ℝ := 64 * K ^ 3 + 48 * Real.exp 1 * K + K ^ 2 / 20 with hCfine
  set M : ℝ := Real.exp (K / 2) + (1 + K ^ 2 / 25) with hMdef
  have hCfine0 : 0 ≤ Cfine := by rw [hCfine]; positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  refine ⟨Cfine + M / d ^ 3 + 1, by positivity, ?_⟩
  intro q w t hq hw ht0 ht
  have hfine : t ≤ d →
      |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
        - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)| ≤ Cfine * t ^ 3 := by
    intro htd
    have hsmall : 4 * (Q * A.card) * t ≤ 1 := by
      have h1 : t ≤ 1 / (4 * (K + 1)) := by rwa [← hddef]
      have h2 : (0 : ℝ) < 4 * (K + 1) := by linarith
      rw [le_div_iff₀ h2] at h1
      nlinarith
    exact abs_integral_prod_localIntegrand_sub_le hq hw hQ0 ht0 ht hsmall
  have hcrude := abs_integral_prod_localIntegrand_sub_le_crude hq hw hQ0 ht
  have hcube := le_mul_cube_of_two_regime hd ht0 hM0 hCfine0 hfine hcrude
  nlinarith [pow_nonneg ht0 3]

/-! ### Taking logarithms

`RMF.exists_abs_log_sub_poly_le` turns a fine expansion `I = 1 + P + O(t³)` into
`log I = P + O(t³)`, given a crude bound on `|log I|`.  That crude bound is immediate here: the
exponent is bounded on the circle, so the moment is trapped between `e^{±K/2}`. -/

/-- **The joint local moment is trapped between `e^{±Λ}`** for any pointwise bound `Λ` on the
exponent.

Separating the bound from where it comes from is what lets the pair estimate reuse this step: its
own exponent bound, `RMF.abs_logExponent_pairWeight_le`, is uniform in `λ₂`, which
`RMF.abs_logExponent_le` is not. -/
lemma abs_log_integral_prod_localIntegrand_le_of_bound {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    {Λ : ℝ} (hw : ∀ a ∈ A, ‖w a‖ < 1)
    (hbnd : ∀ z : ℂ, ‖z‖ = 1 → |logExponent A q w z| ≤ Λ) :
    |Real.log (∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)| ≤ Λ := by
  have hae : ∀ᵐ z ∂steinhausLaw,
      (∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a)) = Real.exp (logExponent A q w z) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact prod_norm_inv_one_sub_rpow_eq_exp A q w hz hw
  have hb : ∀ᵐ z ∂steinhausLaw, |logExponent A q w z| ≤ Λ := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact hbnd z hz
  have hiexpL : Integrable (fun z => Real.exp (logExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      ((Real.measurable_exp.comp (measurable_logExponent A q w))).aestronglyMeasurable
      (Real.exp Λ) <| by
      filter_upwards [hb] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 hz).2
  rw [integral_congr_ae hae]
  have hup : (∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw) ≤ Real.exp Λ := by
    calc (∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
        ≤ ∫ _z, Real.exp Λ ∂steinhausLaw :=
          integral_mono_ae hiexpL (integrable_const _)
            (by filter_upwards [hb] with z hz
                exact Real.exp_le_exp.2 (abs_le.1 hz).2)
      _ = Real.exp Λ := by simp
  have hlo : Real.exp (-Λ) ≤ ∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw := by
    calc Real.exp (-Λ) = ∫ _z, Real.exp (-Λ) ∂steinhausLaw := by simp
      _ ≤ ∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw :=
          integral_mono_ae (integrable_const _) hiexpL
            (by filter_upwards [hb] with z hz
                exact Real.exp_le_exp.2 (abs_le.1 hz).1)
  have hpos : (0 : ℝ) < ∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw :=
    lt_of_lt_of_le (Real.exp_pos _) hlo
  have h1 : Real.log (∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw) ≤ Λ := by
    have h := Real.log_le_log hpos hup
    rwa [Real.log_exp] at h
  have h2 : -Λ ≤ Real.log (∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw) := by
    have h := Real.log_le_log (Real.exp_pos _) hlo
    rwa [Real.log_exp] at h
  exact abs_le.2 ⟨h2, h1⟩

/-- The same hypotheses make the joint local moment positive, so its logarithm is meaningful. -/
lemma integral_prod_localIntegrand_pos_of_bound {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    {Λ : ℝ} (hw : ∀ a ∈ A, ‖w a‖ < 1)
    (hbnd : ∀ z : ℂ, ‖z‖ = 1 → |logExponent A q w z| ≤ Λ) :
    0 < ∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw := by
  have hae : ∀ᵐ z ∂steinhausLaw,
      (∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a)) = Real.exp (logExponent A q w z) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact prod_norm_inv_one_sub_rpow_eq_exp A q w hz hw
  have hb : ∀ᵐ z ∂steinhausLaw, |logExponent A q w z| ≤ Λ := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact hbnd z hz
  have hiexpL : Integrable (fun z => Real.exp (logExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      ((Real.measurable_exp.comp (measurable_logExponent A q w))).aestronglyMeasurable
      (Real.exp Λ) <| by
      filter_upwards [hb] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 hz).2
  rw [integral_congr_ae hae]
  refine lt_of_lt_of_le (Real.exp_pos (-Λ)) ?_
  calc Real.exp (-Λ) = ∫ _z, Real.exp (-Λ) ∂steinhausLaw := by simp
    _ ≤ ∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw :=
        integral_mono_ae (integrable_const _) hiexpL
          (by filter_upwards [hb] with z hz
              exact Real.exp_le_exp.2 (abs_le.1 hz).1)

/-- **The joint local moment is trapped between `e^{±M}`**, `M = 2K log((1-θ)⁻¹)`.  Hence its
logarithm is bounded, with no smallness in `t` — the crude input of
`RMF.exists_abs_log_sub_poly_le`, which is what extends the expansion from `t ≤ 1/5` to the whole
range `t ≤ θ`.  The extension is not optional: at `Re s = 1/2` the primes below `25` have
`p^{-1/2} > 1/5`. -/
lemma abs_log_integral_prod_localIntegrand_le {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {Q θ : ℝ}
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ θ) (hθ : θ < 1) :
    |Real.log (∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)|
      ≤ 2 * (Q * A.card) * Real.log ((1 - θ)⁻¹) :=
  abs_log_integral_prod_localIntegrand_le_of_bound
    (fun a ha => lt_of_le_of_lt (hw a ha) hθ) fun _ hz => abs_logExponent_le hz hq hw hθ

/-- **The joint local expansion after taking logarithms.**  For `|q_a| ≤ Q` and `‖w_a‖ ≤ t ≤ θ < 1`,
`log E_z ∏_a ‖(1 - z w_a)⁻¹‖^{2q_a} = ‖∑_a q_a w_a‖² + O_{Q,θ,A}(t³)`.  Summed over the primes at
`w_a = p^{-σ-ih_a}` it turns Hamdan's Laplace transform into a prime sum. -/
theorem exists_abs_log_local_multi_le (A : Finset ι) {Q θ : ℝ} (hQ0 : 0 ≤ Q) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) :
    ∃ C > 0, ∀ (q : ι → ℝ) (w : ι → ℂ) (t : ℝ),
      (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, ‖w a‖ ≤ t) → 0 ≤ t → t ≤ θ →
        |Real.log (∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
            - ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2| ≤ C * t ^ 3 := by
  have hK0 : (0 : ℝ) ≤ Q * A.card := mul_nonneg hQ0 (Nat.cast_nonneg _)
  have hL0 : (0 : ℝ) ≤ Real.log ((1 - θ)⁻¹) :=
    Real.log_nonneg (one_le_inv_iff₀.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨C₀, hC₀, hexp⟩ := exists_local_multi_expansion_steinhausLaw A hQ0
  obtain ⟨C, hC, hbound⟩ := exists_abs_log_sub_poly_le (C₀ := C₀)
    (K := (Q * A.card) ^ 2) (M₀ := 2 * (Q * A.card) * Real.log ((1 - θ)⁻¹))
    hC₀.le (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro q w t hq hw ht0 ht
  refine hbound _ _ t ht0 (by linarith)
    (fun h5 => hexp q w t hq hw ht0 h5) ?_
    (abs_log_integral_prod_localIntegrand_le hq (fun a ha => le_trans (hw a ha) ht) hθ)
  -- the polynomial part is `O(t²)`
  have hu0 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a‖ := norm_nonneg _
  have h1 := norm_sum_smul_le hq hw
  have hsq : ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 ≤ ((Q * A.card) * t) ^ 2 :=
    pow_le_pow_left₀ hu0 h1 2
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)]
  nlinarith

/-! ### Summing over the primes

The passage from a local estimate to a prime sum is `RMF.abs_log_prod_sub_sum_le`, which is
already indexed abstractly by `p`; all that is needed is to evaluate the local bound at
`w_a = p^{-s_a}` and to know that the error series `∑_p p^{-3σ}` converges, which it does for
`σ > 1/3`.  Every abscissa shares the same real part, so all three weights have the same modulus
`p^{-σ}` and one `t` serves for all of them. -/

/-- The joint local moment is positive, so its logarithm is meaningful. -/
lemma integral_prod_localIntegrand_pos {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {Q θ : ℝ}
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hw : ∀ a ∈ A, ‖w a‖ ≤ θ) (hθ : θ < 1) :
    0 < ∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw :=
  integral_prod_localIntegrand_pos_of_bound
    (fun a ha => lt_of_le_of_lt (hw a ha) hθ) fun _ hz => abs_logExponent_le hz hq hw hθ

/-- **The joint local expansion, summed over the primes.**  For `|q_a| ≤ Q` and `Re s_a = σ ≥ σ₀`,
`log ∏_{p ∈ [y₀,y)} E_z ∏_a ‖(1 - z p^{-s_a})⁻¹‖^{2q_a}` is `∑_{p ∈ [y₀,y)} ‖∑_a q_a p^{-s_a}‖²`
up to a constant depending only on `A`, `Q` and `σ₀`.  The main term is bounded in
`RMF.sum_norm_sum_smul_cpow_le`. -/
theorem exists_multi_prime_sum_bound_steinhausLaw (A : Finset ι) {Q σ₀ : ℝ} (hQ0 : 0 ≤ Q)
    (hσ₀ : 1 / 3 < σ₀) :
    ∃ C > 0, ∀ (q : ι → ℝ) (s : ι → ℂ) (σ : ℝ) (y₀ y : ℕ),
      (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, (s a).re = σ) → σ₀ ≤ σ →
        |Real.log (∏ p ∈ primesIco y₀ y,
              ∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
            - ∑ p ∈ primesIco y₀ y, ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2|
          ≤ C := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨C₁, hC₁, hloc⟩ := exists_abs_log_local_multi_le A hQ0 hθ0 hθ
  have hT0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨C₁ * ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) + C₁, by positivity, ?_⟩
  intro q s σ y₀ y hq hs hσ
  -- every abscissa has real part `σ`, so every weight has modulus `p ^ (-σ)`
  have hnorm : ∀ p ∈ primesIco y₀ y, ∀ a ∈ A,
      ‖((p : ℂ)) ^ (-s a)‖ = (p : ℝ) ^ (-σ) := by
    intro p hp a ha
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos,
      Complex.neg_re, hs a ha]
  have hle : ∀ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpos : ∀ p ∈ primesIco y₀ y,
      0 < ∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw := by
    intro p hp
    exact integral_prod_localIntegrand_pos (Q := Q) hq
      (fun a ha => le_trans (le_of_eq (hnorm p hp a ha)) (hle p hp)) hθ
  have hterm : ∀ p ∈ primesIco y₀ y,
      |Real.log (∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
          - ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2|
        ≤ C₁ * (p : ℝ) ^ (-3 * σ) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).pos
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
    have h := hloc q (fun a => (p : ℂ) ^ (-s a)) ((p : ℝ) ^ (-σ)) hq
      (fun a ha => le_of_eq (hnorm p hp a ha)) ht0 (hle p hp)
    have hcube : ((p : ℝ) ^ (-σ)) ^ 3 = (p : ℝ) ^ (-3 * σ) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 3, ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    rwa [hcube] at h
  have hmain := abs_log_prod_sub_sum_le hpos hterm
  refine le_trans hmain ?_
  have hsum : ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * σ)
      ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₀) := sum_primesIco_rpow_le hσ₀ hσ y₀ y
  nlinarith [hC₁.le]

/-! ### The joint moment of the Euler product

The prime sum above is a product of *local* moments.  The factorisation
`RMF.IsSteinhausRMF.integral_prod_norm_randomEulerProductIco_rpow`, which allows exponents of
either sign, identifies that product with a joint moment of the Euler product itself. -/

/-- **The joint moment of a Steinhaus Euler product is a prime sum**:
`log E ∏_a ‖F_{[y₀,y)}(s_a)‖^{2q_a} = ∑_{p ∈ [y₀,y)} ‖∑_a q_a p^{-s_a}‖² + O(1)` for `|q_a| ≤ Q`
of either sign and `Re s_a = σ ≥ σ₀ > 1/3`, with the constant independent of `f`, `μ`, `y₀`, `y`
and the points.  Additively, this is the cumulant of `∑_a λ_a log‖F(s_a)‖` with `λ_a = 2q_a`:
Hamdan's joint Laplace transform. -/
theorem IsSteinhausRMF.exists_log_joint_moment_prime_sum {Ω : Type*} [MeasurableSpace Ω]
    (A : Finset ι) {Q σ₀ : ℝ} (hQ0 : 0 ≤ Q) (hσ₀ : 1 / 3 < σ₀) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (q : ι → ℝ) (s : ι → ℂ) (σ : ℝ) (y₀ y : ℕ),
        (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, (s a).re = σ) → σ₀ ≤ σ →
          |Real.log (∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ)
              - ∑ p ∈ primesIco y₀ y, ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2|
            ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_multi_prime_sum_bound_steinhausLaw A hQ0 hσ₀
  refine ⟨C, hC, ?_⟩
  intro f μ hf q s σ y₀ y hq hs hσ
  have hre : ∀ a ∈ A, 0 < (s a).re := fun a ha => by rw [hs a ha]; linarith
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y A hre]
  exact hbound q s σ y₀ y hq hs hσ

/-! ### Evaluating the main term

By the polarisation identity `∑_{p<y} ‖∑_a q_a p^{-s_a}‖²` is
`∑_{a,b} q_a q_b ∑_p p^{-2σ} cos((h_a - h_b) log p)`.  Replacing each cosine by `1` leaves
`(∑_a q_a)² ∑_p p^{-2σ}`, and the deficit is controlled by `1 - cos θ ≤ |θ|`.

That crude cosine bound is what produces Hamdan's `e^j|h₁-h₂|`: at `σ = 1/2` the deficit is at most
`|Δ| ∑_{p<y} (log p)/p ≪ |Δ| log y`, and `log x_j = e^j`.  The quadratic `1 - cos θ ≤ θ²/2` would
give `(e^jΔ)²` instead, through `∑_p p^{-2σ}(log p)²`.  The linear bound is the one Hamdan uses. -/

/-- `1 - cos θ ≤ |θ|`: the quadratic bound below `|θ| ≤ 2`, the trivial one above. -/
lemma one_sub_cos_le_abs (x : ℝ) : 1 - Real.cos x ≤ |x| := by
  rcases le_or_gt |x| 2 with h | h
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
    have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [abs_nonneg x]
  · nlinarith [Real.neg_one_le_cos x]

/-- **The local main term, in terms of the points' spread**:
`‖∑_a q_a p^{-s_a}‖² ≤ p^{-2σ}[(∑_a q_a)² + Q²|A|² D log p]` when every `s_a` has real part `σ` and
their imaginary parts differ by at most `D`.  For Hamdan's Lemma B.1, `q = (λ₁, λ₂, -λ₂)/2`, the
first term is `λ₁²/4`: the increment `S(σ+ih₁) - S(σ+ih₂)` carries no variance of its own at
leading order, and everything it costs is proportional to `D`. -/
lemma norm_sum_smul_cpow_le {A : Finset ι} {q : ι → ℝ} {s : ι → ℂ} {σ D Q : ℝ} {p : ℕ}
    (hp : 0 < p) (hp1 : 1 ≤ p) (hs : ∀ a ∈ A, (s a).re = σ)
    (hD : ∀ a ∈ A, ∀ b ∈ A, |(s a).im - (s b).im| ≤ D) (hq : ∀ a ∈ A, |q a| ≤ Q)
    (hQ0 : 0 ≤ Q) :
    ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2
      ≤ (p : ℝ) ^ (-2 * σ) * ((∑ a ∈ A, q a) ^ 2 + Q ^ 2 * A.card ^ 2 * D * Real.log p) := by
  have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
  have hpow0 : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by positivity) _
  rw [← sum_sum_re_mul_conj_eq_norm_sq A q (fun a => (p : ℂ) ^ (-s a))]
  have hcos : ∀ a ∈ A, ∀ b ∈ A,
      q a * q b * (((p : ℂ) ^ (-s a)) * (starRingEnd ℂ) ((p : ℂ) ^ (-s b))).re
        = (p : ℝ) ^ (-2 * σ)
          * (q a * q b * Real.cos (((s a).im - (s b).im) * Real.log p)) := by
    intro a ha b hb
    rw [re_natCast_cpow_neg_mul_conj hp, hs a ha, hs b hb,
      show -(σ + σ) = -2 * σ by ring]
    ring
  have hpull : (∑ a ∈ A, ∑ b ∈ A,
      q a * q b * (((p : ℂ) ^ (-s a)) * (starRingEnd ℂ) ((p : ℂ) ^ (-s b))).re)
      = (p : ℝ) ^ (-2 * σ) * ∑ a ∈ A, ∑ b ∈ A,
          q a * q b * Real.cos (((s a).im - (s b).im) * Real.log p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => hcos a ha b hb
  rw [hpull]
  refine mul_le_mul_of_nonneg_left ?_ hpow0
  have hterm : ∀ a ∈ A, (∑ b ∈ A,
      q a * q b * Real.cos (((s a).im - (s b).im) * Real.log p))
      ≤ ∑ b ∈ A, (q a * q b + Q ^ 2 * (D * Real.log p)) := by
    intro a ha
    refine Finset.sum_le_sum fun b hb => ?_
    have h2 : |((s a).im - (s b).im) * Real.log p| ≤ D * Real.log p := by
      rw [abs_mul, abs_of_nonneg hlog0]
      exact mul_le_mul_of_nonneg_right (hD a ha b hb) hlog0
    have h3 : |q a * q b| ≤ Q ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (hq a ha) (hq b hb) (abs_nonneg _) hQ0
    have hc0 : (0 : ℝ) ≤ 1 - Real.cos (((s a).im - (s b).im) * Real.log p) := by
      linarith [Real.cos_le_one (((s a).im - (s b).im) * Real.log p)]
    have hc1 : 1 - Real.cos (((s a).im - (s b).im) * Real.log p) ≤ D * Real.log p :=
      le_trans (one_sub_cos_le_abs _) h2
    nlinarith [mul_le_mul_of_nonneg_right h3 hc0,
      mul_le_mul_of_nonneg_left hc1 (sq_nonneg Q),
      mul_le_mul_of_nonneg_right (neg_le_abs (q a * q b)) hc0]
  calc (∑ a ∈ A, ∑ b ∈ A, q a * q b * Real.cos (((s a).im - (s b).im) * Real.log p))
      ≤ ∑ a ∈ A, ∑ b ∈ A, (q a * q b + Q ^ 2 * (D * Real.log p)) :=
        Finset.sum_le_sum hterm
    _ = (∑ a ∈ A, ∑ b ∈ A, q a * q b)
        + ∑ _a ∈ A, ∑ _b ∈ A, Q ^ 2 * (D * Real.log p) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
    _ = (∑ a ∈ A, q a) ^ 2 + Q ^ 2 * A.card ^ 2 * D * Real.log p := by
        have h1 : (∑ a ∈ A, ∑ b ∈ A, q a * q b) = (∑ a ∈ A, q a) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
        rw [h1]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The main term, summed over the primes**: over `p ∈ [y₀, y)`,
`∑_p ‖∑_a q_a p^{-s_a}‖² ≤ (∑_a q_a)² ∑_p p^{-2σ} + Q²|A|² D ∑_p p^{-2σ} log p`.  The two prime sums
are left symbolic; at `σ = 1/2` they are `∑_p 1/p = log log y + O(1)` (Mertens) and
`∑_p (log p)/p ≤ log y + O(1)` (`RMF.sum_log_div_prime_le`). -/
theorem sum_norm_sum_smul_cpow_le {A : Finset ι} {q : ι → ℝ} {s : ι → ℂ} {σ D Q : ℝ} (y₀ y : ℕ)
    (hs : ∀ a ∈ A, (s a).re = σ) (hD : ∀ a ∈ A, ∀ b ∈ A, |(s a).im - (s b).im| ≤ D)
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hQ0 : 0 ≤ Q) :
    (∑ p ∈ primesIco y₀ y, ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2)
      ≤ (∑ a ∈ A, q a) ^ 2 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)
        + Q ^ 2 * A.card ^ 2 * D
          * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
  have hterm : ∀ p ∈ primesIco y₀ y,
      ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2
        ≤ (∑ a ∈ A, q a) ^ 2 * (p : ℝ) ^ (-2 * σ)
          + Q ^ 2 * A.card ^ 2 * D * ((p : ℝ) ^ (-2 * σ) * Real.log p) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have h := norm_sum_smul_cpow_le (q := q) (s := s) (σ := σ) (D := D) (Q := Q)
      hpp.pos hpp.one_lt.le hs hD hq hQ0
    calc ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2
        ≤ (p : ℝ) ^ (-2 * σ)
            * ((∑ a ∈ A, q a) ^ 2 + Q ^ 2 * A.card ^ 2 * D * Real.log p) := h
      _ = (∑ a ∈ A, q a) ^ 2 * (p : ℝ) ^ (-2 * σ)
            + Q ^ 2 * A.card ^ 2 * D * ((p : ℝ) ^ (-2 * σ) * Real.log p) := by ring
  calc (∑ p ∈ primesIco y₀ y, ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2)
      ≤ ∑ p ∈ primesIco y₀ y, ((∑ a ∈ A, q a) ^ 2 * (p : ℝ) ^ (-2 * σ)
          + Q ^ 2 * A.card ^ 2 * D * ((p : ℝ) ^ (-2 * σ) * Real.log p)) :=
        Finset.sum_le_sum hterm
    _ = (∑ a ∈ A, q a) ^ 2 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)
        + Q ^ 2 * A.card ^ 2 * D
          * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ### Hamdan's Lemma B.1, Laplace-transform half

Combining the prime-sum identity with the bound on its main term gives the cumulant estimate the
Chernoff step consumes.  At `q = (λ₁, λ₂, -λ₂)/2` over three abscissas `σ, σ+ih₁, σ+ih₂`:

* `(∑_a q_a)² = λ₁²/4`, and at `σ = 1/2` the first prime sum is `log log y + O(1)` — Hamdan's
  `λ₁² j/4`;
* `D = max|h_a - h_b|`, and the second prime sum is `≤ log y + O(1) = e^j + O(1)` — his
  `c λ₂² e^j|h₁-h₂|`.

The Chernoff bounds follow below, with the exponents left free
(`RMF.IsSteinhausRMF.exists_measure_le_exp`, `RMF.IsSteinhausRMF.exists_measure_le_exp_pair`);
neither touches the Euler product again. -/

/-- **The joint cumulant bound.**  Over `p ∈ [y₀, y)`,
`log E ∏_a ‖F_{[y₀,y)}(s_a)‖^{2q_a} ≤ (∑_a q_a)² ∑_p p^{-2σ} + Q²|A|² D ∑_p p^{-2σ} log p + C`,
with `C` independent of `f`, `μ`, `y₀`, `y` and the points.  This is the Laplace-transform half of
Hamdan's Lemma B.1. -/
theorem IsSteinhausRMF.exists_log_joint_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (A : Finset ι) {Q σ₀ : ℝ} (hQ0 : 0 ≤ Q) (hσ₀ : 1 / 3 < σ₀) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (q : ι → ℝ) (s : ι → ℂ) (σ D : ℝ) (y₀ y : ℕ),
        (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, (s a).re = σ) → σ₀ ≤ σ →
        (∀ a ∈ A, ∀ b ∈ A, |(s a).im - (s b).im| ≤ D) →
          Real.log (∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ)
            ≤ (∑ a ∈ A, q a) ^ 2 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)
              + Q ^ 2 * A.card ^ 2 * D
                * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
              + C := by
  obtain ⟨C, hC, hbound⟩ :=
    IsSteinhausRMF.exists_log_joint_moment_prime_sum (Ω := Ω) A hQ0 hσ₀
  refine ⟨C, hC, ?_⟩
  intro f μ hf q s σ D y₀ y hq hs hσ hD
  have h1 := abs_le.1 (hbound f μ hf q s σ y₀ y hq hs hσ)
  have h2 := sum_norm_sum_smul_cpow_le (q := q) (s := s) (σ := σ) (D := D) (Q := Q)
    y₀ y hs hD hq hQ0
  linarith [h1.2]

/-! ### From the product form to the walks

The joint moment above is multiplicative; the Chernoff bound is additive.  The bridge is
`∏_a g_a^{λ_a} = exp(∑_a λ_a log g_a)`, which needs the `g_a` positive — true almost surely for the
Euler product, off the null set where some local factor vanishes. -/

/-- `∏_a g_a^{λ_a} = exp(∑_a λ_a log g_a)` for positive `g`. -/
lemma prod_rpow_eq_exp_sum {A : Finset ι} {l g : ι → ℝ} (hg : ∀ a ∈ A, 0 < g a) :
    (∏ a ∈ A, g a ^ l a) = Real.exp (∑ a ∈ A, l a * Real.log (g a)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Real.rpow_def_of_pos (hg a ha)]
  congr 1
  ring

/-- **The joint moment is the expectation of an exponential of the walks.**

`∏_a ‖F_y(s_a)‖^{2q_a} = exp(∑_a 2q_a log‖F_y(s_a)‖)` almost surely.  Under the Steinhaus law the
Euler product is a.e. non-zero, which is exactly what the identity needs; and
`log‖F_y(s)‖` is the walk `S` at abscissa `s`. -/
lemma IsSteinhausRMF.prod_norm_rpow_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    (A : Finset ι) (q : ι → ℝ) (s : ι → ℂ) (y₀ y : ℕ) (hs : ∀ a ∈ A, 0 < (s a).re) :
    (fun ω => ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a))
      =ᵐ[μ] fun ω => Real.exp
        (∑ a ∈ A, 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) := by
  have hall : ∀ᵐ ω ∂μ, ∀ a ∈ A, randomEulerProductIco f y₀ y (s a) ω ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact IsSteinhausRMF.ae_randomEulerProductIco_ne_zero hf y₀ y (hs a ha)
  filter_upwards [hall] with ω hω
  exact prod_rpow_eq_exp_sum fun a ha => norm_pos_iff.2 (hω a ha)

/-! ### Integrability of the joint integrand

The Chernoff bound is a Markov inequality, so it needs the exponential integrable.  For a
**negative** exponent that is not automatic from the upper bound
`RMF.IsSteinhausRMF.ae_norm_randomEulerProductIco_le`:
`‖F‖^{2q}` blows up where `‖F‖` is small.  What
saves it is that `F_y` is a *finite* product, so `‖F_y‖` is bounded **below** as well, and the
walk `log‖F_y‖` is therefore bounded on both sides. -/

/-- **A deterministic lower bound on the Steinhaus Euler product.**  The mirror of
`RMF.IsSteinhausRMF.ae_norm_randomEulerProductIco_le`: each local factor has modulus at least
`(1 + ‖p^{-s}‖)⁻¹`. -/
lemma IsSteinhausRMF.ae_le_norm_randomEulerProductIco {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, (∏ p ∈ primesIco y₀ y, (1 + ‖(p : ℂ) ^ (-s)‖)⁻¹)
      ≤ ‖randomEulerProductIco f y₀ y s ω‖ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y] with ω hω
  rw [randomEulerProductIco_compMult_eq hs hω, norm_prod]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
  have hup : ‖1 - X p ω * (p : ℂ) ^ (-s)‖ ≤ 1 + ‖(p : ℂ) ^ (-s)‖ := by
    have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
    have h2 := norm_sub_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
    rw [norm_one] at h2
    linarith
  have hlow : 0 < ‖1 - X p ω * (p : ℂ) ^ (-s)‖ := by
    have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
    have h2 := norm_sub_norm_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
    rw [norm_one] at h2
    linarith
  rw [norm_inv]
  exact inv_anti₀ hlow hup

/-- **The walk is bounded on both sides**: almost surely
`|log‖F_{[y₀,y)}(s)‖| ≤ log ∏_{p ∈ [y₀,y)} (1 - ‖p^{-s}‖)⁻¹`, since `‖F‖` lies between
`∏(1+‖p^{-s}‖)⁻¹` and `∏(1-‖p^{-s}‖)⁻¹`, and the first is at least the reciprocal of the second. -/
lemma IsSteinhausRMF.ae_abs_log_norm_randomEulerProductIco_le {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y₀ y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, |Real.log ‖randomEulerProductIco f y₀ y s ω‖|
      ≤ Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹) := by
  have hUpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
    refine Finset.prod_pos fun p hp => ?_
    have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    exact inv_pos.2 (by linarith)
  have hLU : (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹)⁻¹
      ≤ ∏ p ∈ primesIco y₀ y, (1 + ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
    · have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
      positivity
    · have hw := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
      have h0 : (0 : ℝ) ≤ ‖(p : ℂ) ^ (-s)‖ := norm_nonneg _
      rw [inv_inv, ← one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ‖(p : ℂ) ^ (-s)‖)]
      nlinarith
  filter_upwards [hf.ae_norm_randomEulerProductIco_le y₀ y hs,
    hf.ae_le_norm_randomEulerProductIco y₀ y hs] with ω hup hlo
  have hLpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 + ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
    refine Finset.prod_pos fun p hp => ?_
    positivity
  have hFpos : (0 : ℝ) < ‖randomEulerProductIco f y₀ y s ω‖ := lt_of_lt_of_le hLpos hlo
  rw [abs_le]
  constructor
  · have h1 := Real.log_le_log hLpos hlo
    have h2 := Real.log_le_log (by positivity) hLU
    rw [Real.log_inv] at h2
    linarith
  · exact Real.log_le_log hFpos hup

/-- **The joint integrand `∏_a ‖F_{[y₀,y)}(s_a)‖^{2q_a}` is integrable**, for `|q_a| ≤ Q` and
`Re s_a > 0`: the walks are bounded on both sides
(`RMF.IsSteinhausRMF.ae_abs_log_norm_randomEulerProductIco_le`).  The Chernoff bound needs this,
and the factorisation of the joint moment does not supply it: it evaluates the integral without
excluding the junk value of a divergent one. -/
lemma IsSteinhausRMF.integrable_prod_norm_rpow {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    (A : Finset ι) (q : ι → ℝ) (s : ι → ℂ) (y₀ y : ℕ) {Q : ℝ}
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hQ0 : 0 ≤ Q) (hs : ∀ a ∈ A, 0 < (s a).re) :
    Integrable (fun ω => ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) μ := by
  haveI := hf.isProbabilityMeasure
  have hmeas : AEStronglyMeasurable
      (fun ω => ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) μ := by
    refine AEStronglyMeasurable.congr ?_ (hf.prod_norm_rpow_ae_eq A q s y₀ y hs).symm
    have hsum : AEMeasurable
        (fun ω => ∑ a ∈ A, 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) μ := by
      have hone : ∀ a ∈ A, AEMeasurable
          (fun ω => 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) μ := by
        intro a ha
        exact (Real.measurable_log.comp_aemeasurable
          ((hf.aemeasurable_randomEulerProductIco y₀ y (hs a ha)).norm)).const_mul (2 * q a)
      have h := Finset.aemeasurable_sum (μ := μ) A hone
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp
    exact (Real.measurable_exp.comp_aemeasurable hsum).aestronglyMeasurable
  have hall : ∀ᵐ ω ∂μ, ∀ a ∈ A, |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖|
      ≤ Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact hf.ae_abs_log_norm_randomEulerProductIco_le y₀ y (hs a ha)
  refine (memLp_top_of_bound hmeas
    (Real.exp (2 * Q * ∑ a ∈ A,
      Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹))) ?_).integrable le_top
  filter_upwards [hall, hf.prod_norm_rpow_ae_eq A q s y₀ y hs] with ω h1 h2
  rw [Real.norm_eq_abs, h2, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  have hL := h1 a ha
  have hM0 : (0 : ℝ)
      ≤ Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) :=
    le_trans (abs_nonneg _) hL
  have hqa := hq a ha
  have h3 : q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖
      ≤ Q * Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) := by
    have h4 : q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖
        ≤ |q a| * |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖| := by
      calc q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖
          ≤ |q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖| := le_abs_self _
        _ = |q a| * |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖| := abs_mul _ _
    have h5 : |q a| * |Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖|
        ≤ Q * Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖(p : ℂ) ^ (-s a)‖)⁻¹) :=
      mul_le_mul hqa hL (abs_nonneg _) hQ0
    linarith
  linarith

/-! ### A joint Chernoff bound with crude constants

Markov against the joint moment, from the cumulant bound
`RMF.IsSteinhausRMF.exists_log_joint_moment_le`, the integrability
`RMF.IsSteinhausRMF.integrable_prod_norm_rpow`, and positivity of the moment, which
`RMF.integral_prod_localIntegrand_pos` gives prime by prime. -/

/-- **A joint Chernoff bound, crude constants.**  If `|q_a| ≤ Q`, `Re s_a = σ ≥ σ₀`, the heights
lie within `D` of each other and `∑_a 2q_a log ‖F(s_a)‖ ≥ W` on a measurable `E`, then
`P(E) ≤ exp((∑_a q_a)² ∑_p p^{-2σ} + Q²|A|²D ∑_p p^{-2σ} log p + C - W)` over `p ∈ [y₀, y)`, with
`C` independent of `f`, `μ`, `y₀`, `y`, the points and `E`.  Its `D` term does not shrink with the
gap between two heights; for the pair, where it does, see
`RMF.IsSteinhausRMF.exists_measure_le_exp_pair`. -/
theorem IsSteinhausRMF.exists_measure_le_exp {Ω : Type*} [MeasurableSpace Ω]
    (A : Finset ι) {Q σ₀ : ℝ} (hQ0 : 0 ≤ Q) (hσ₀ : 1 / 3 < σ₀) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (q : ι → ℝ) (s : ι → ℂ) (σ D W : ℝ) (y₀ y : ℕ) (E : Set Ω),
        (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, (s a).re = σ) → σ₀ ≤ σ →
        (∀ a ∈ A, ∀ b ∈ A, |(s a).im - (s b).im| ≤ D) → MeasurableSet E →
        (∀ ω ∈ E, W ≤ ∑ a ∈ A, 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) →
          μ.real E ≤ Real.exp ((∑ a ∈ A, q a) ^ 2
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            + Q ^ 2 * A.card ^ 2 * D
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
            + C - W) := by
  obtain ⟨C, hC, hbound⟩ := IsSteinhausRMF.exists_log_joint_moment_le (Ω := Ω) A hQ0 hσ₀
  refine ⟨C, hC, ?_⟩
  intro f μ hf q s σ D W y₀ y E hq hs hσ hD hE hW
  haveI := hf.isProbabilityMeasure
  have hre : ∀ a ∈ A, 0 < (s a).re := fun a ha => by rw [hs a ha]; linarith
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hint := hf.integrable_prod_norm_rpow A q s y₀ y hq hQ0 hre
  -- the joint moment is positive
  have hIpos : (0 : ℝ) < ∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ := by
    rw [hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y A hre]
    refine Finset.prod_pos fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    refine integral_prod_localIntegrand_pos (Q := Q) hq (θ := (2 : ℝ) ^ (-σ₀)) ?_ hθ
    intro a ha
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, hs a ha]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- Markov: on `E` the integrand is at least `exp W`
  have hge : ∀ᵐ ω ∂(μ.restrict E), Real.exp W
      ≤ ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) := by
    filter_upwards [ae_restrict_of_ae (hf.prod_norm_rpow_ae_eq A q s y₀ y hre),
      ae_restrict_mem hE] with ω h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (hW ω h2)
  have h1 : μ.real E * Real.exp W
      ≤ ∫ ω in E, (∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) ∂μ := by
    have hc : (∫ _ω in E, Real.exp W ∂μ) = μ.real E * Real.exp W := by
      rw [setIntegral_const, smul_eq_mul]
    rw [← hc]
    exact integral_mono_ae (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hge
  have h2 : (∫ ω in E, (∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) ∂μ)
      ≤ ∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ := by
    refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) _
  -- and the moment is at most `exp B`
  have h3 : (∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ)
      ≤ Real.exp ((∑ a ∈ A, q a) ^ 2 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
        + Q ^ 2 * A.card ^ 2 * D
          * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) + C) := by
    have h := hbound f μ hf q s σ D y₀ y hq hs hσ hD
    have h4 := Real.exp_le_exp.2 h
    rwa [Real.exp_log hIpos] at h4
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos W)]
  linarith

/-! ### The two prime sums at `σ = 1/2`

`RMF.IsSteinhausRMF.exists_measure_le_exp` leaves both prime sums symbolic.  On the critical line
they are the two classical ones: `∑_p 1/p = log log y + O(1)` (Mertens) and
`∑_p (log p)/p ≤ log y + O(1)`.  The second is `RMF.sum_log_div_prime_le`, indexed over
`Finset.Ioc 0 ⌊x⌋₊` rather than `Nat.primesBelow`; since every term is non-negative the transfer
is a subset argument, not a re-derivation. -/

/-- `∑_{p < y} (log p)/p ≤ log y + log 4 + 4`, indexed by `Nat.primesBelow`. -/
lemma sum_primesBelow_log_div_le {y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ Nat.primesBelow y, Real.log p / p ≤ Real.log y + Real.log 4 + 4 := by
  have hsub : Nat.primesBelow y
      ⊆ (Finset.Ioc 0 ⌊(y : ℝ)⌋₊).filter (fun p => Nat.Prime p) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
    exact ⟨⟨hp.2.pos, le_of_lt hp.1⟩, hp.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
    log_div_natCast_nonneg p) ?_
  exact sum_log_div_prime_le (by exact_mod_cast hy)

/-- On the critical line the first prime sum is the harmonic one over the primes. -/
lemma sum_primesBelow_rpow_half (y : ℕ) :
    (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-2 * (1 / 2 : ℝ)))
      = ∑ p ∈ Nat.primesBelow y, ((p : ℝ))⁻¹ :=
  Finset.sum_congr rfl fun p _ => by
    rw [show (-2 : ℝ) * (1 / 2) = -1 by ring, Real.rpow_neg_one]

/-- And the second is `∑_p (log p)/p`. -/
lemma sum_primesBelow_rpow_half_mul_log (y : ℕ) :
    (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-2 * (1 / 2 : ℝ)) * Real.log p)
      = ∑ p ∈ Nat.primesBelow y, Real.log p / p :=
  Finset.sum_congr rfl fun p _ => by
    rw [show (-2 : ℝ) * (1 / 2) = -1 by ring, Real.rpow_neg_one, inv_mul_eq_div]

/-! ### The combination moments

The chain above is uniform only for bounded exponents, because it bounds each weight separately.
What actually controls every quantity in the expansion is the family of **combination moments**

`m_k := ∑_a q_a w_a^k`,

and the way to see that is the power series: with `L = 2 ∑_a q_a localLog(w_a, z)`,

`L = Re(2 ∑_a q_a (-Log(1 - z w_a))) = Re(2 ∑_{k≥1} z^k m_k / k)`.

The degree-two truncation is `Re(2 z m₁ + z² m₂)`, and the transfer error is
`Re(2 ∑_{k≥3} z^k m_k / k)` — so it is small exactly when the *combination* is, which is what
Hamdan's regime `λ₂ Δ ≲ 1` provides even for `λ₂` large. -/

/-- **`localLog` as a power series.**  `localLog w z = Re ∑_k (z w)^k / k` for `‖z w‖ < 1`.

The `k = 0` term vanishes: Lean's `x / 0 = 0`. -/
lemma hasSum_localLog {w z : ℂ} (h : ‖z * w‖ < 1) :
    HasSum (fun n : ℕ => (((z * w) ^ n / n : ℂ)).re) (localLog w z) := by
  have h1 := Complex.hasSum_taylorSeries_neg_log h
  have h2 := Complex.reCLM.hasSum h1
  have h3 : Complex.reCLM (-Complex.log (1 - z * w)) = localLog w z := by
    rw [Complex.reCLM_apply, Complex.neg_re, Complex.log_re, localLog]
  rwa [h3] at h2

/-- The first three terms of that series are exactly `RMF.localTaylorTwo`. -/
lemma sum_range_three_localLog_series (w z : ℂ) :
    (∑ i ∈ Finset.range 3, (((z * w) ^ i / i : ℂ)).re) = localTaylorTwo w z := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, localTaylorTwo]
  have e0 : (((z * w) ^ (0 : ℕ) / (0 : ℕ) : ℂ)).re = 0 := by norm_num
  have e1 : (((z * w) ^ (1 : ℕ) / (1 : ℕ) : ℂ)).re = (z * w).re := by norm_num
  have e2 : (((z * w) ^ (2 : ℕ) / (2 : ℕ) : ℂ)).re = (z ^ 2 * w ^ 2).re / 2 := by
    rw [mul_pow]
    norm_num [Complex.div_re]
  rw [e0, e1, e2]
  ring

/-- **The cubic tail.**  `localLog w z - localTaylorTwo w z = Re ∑_{k≥3} (z w)^k / k`. -/
lemma localLog_sub_localTaylorTwo_eq_tsum {w z : ℂ} (h : ‖z * w‖ < 1) :
    localLog w z - localTaylorTwo w z
      = ∑' n : ℕ, (((z * w) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re := by
  have hs := hasSum_localLog h
  have hsplit := hs.summable.sum_add_tsum_nat_add 3
  rw [hs.tsum_eq, sum_range_three_localLog_series] at hsplit
  have hcast : ∀ n : ℕ, (((z * w) ^ (n + 3) / ((n + 3 : ℕ) : ℂ)).re)
      = (((z * w) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re := by
    intro n
    push_cast
    ring_nf
  rw [← tsum_congr hcast]
  linarith [hsplit]

/-- The cubic tail is summable — it is a tail of `RMF.hasSum_localLog`. -/
lemma summable_localLog_tail {w z : ℂ} (h : ‖z * w‖ < 1) :
    Summable (fun n : ℕ => (((z * w) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re) := by
  have h1 : Summable (fun n : ℕ => (((z * w) ^ (n + 3) / ((n + 3 : ℕ) : ℂ)) : ℂ).re) :=
    (summable_nat_add_iff 3).2 (hasSum_localLog h).summable
  refine h1.congr fun n => ?_
  push_cast
  ring_nf

/-- **The transfer error through the combination moments**: if `‖m_k‖ ≤ M k θ^k` for `k ≥ 3`, then
`|logExponent - taylorExponent| ≤ 2 M θ³/(1-θ)`.  The factor `k` cancels the `1/k` of the series:
for `q = (λ₁, λ₂, -λ₂)/2` at `w_a = p^{-σ-ih_a}`, `‖m_k‖ ≤ (λ₁/2) t^k + (λ₂/2) k t^k Δ log p`, so
`M ≈ λ₁/2 + (λ₂/2) Δ log p` stays bounded even when `λ₂` does not, which
`RMF.abs_logExponent_sub_taylorExponent_le` cannot see. -/
lemma abs_logExponent_sub_taylorExponent_le_of_moments {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ}
    {z : ℂ} {θ M : ℝ} (hz : ‖z‖ = 1) (hw : ∀ a ∈ A, ‖w a‖ ≤ θ) (hθ : θ < 1) (hθ0 : 0 ≤ θ)
    (hM : ∀ k : ℕ, 3 ≤ k → ‖∑ a ∈ A, (q a : ℂ) * w a ^ k‖ ≤ M * k * θ ^ k) :
    |logExponent A q w z - taylorExponent A q w z| ≤ 2 * (M * θ ^ 3 / (1 - θ)) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hterm : ∀ a ∈ A, ‖z * w a‖ < 1 := fun a ha => by
    rw [norm_mul, hz, one_mul]; exact lt_of_le_of_lt (hw a ha) hθ
  set g : ℕ → ℂ := fun n =>
    (z ^ (n + 3) / ((n : ℕ) + 3)) * ∑ a ∈ A, (q a : ℂ) * w a ^ (n + 3) with hgdef
  have hden : ∀ n : ℕ, ‖((n : ℕ) + 3 : ℂ)‖ = (n : ℝ) + 3 := by
    intro n
    rw [show (((n : ℕ) : ℂ) + 3) = (((n : ℝ) + 3 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgnorm : ∀ n : ℕ, ‖g n‖ ≤ M * θ ^ (n + 3) := by
    intro n
    have hk := hM (n + 3) (by omega)
    have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    rw [hcast] at hk
    have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    rw [hgdef]
    simp only [norm_mul, norm_div, norm_pow, hz, one_pow, hden n]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
    nlinarith [pow_nonneg hθ0 (n + 3)]
  have hgeo : Summable fun n : ℕ => M * θ ^ (n + 3) := by
    have hb := (summable_geometric_of_lt_one hθ0 hθ).mul_left (M * θ ^ 3)
    exact hb.congr fun n => by rw [pow_add]; ring
  have hgsum : Summable g := hgeo.of_norm_bounded hgnorm
  -- the error is twice the real part of `∑' g`
  have hre : logExponent A q w z - taylorExponent A q w z = 2 * (∑' n : ℕ, g n).re := by
    have hswap : (∑' n : ℕ, g n).re = ∑' n : ℕ, (g n).re :=
      ((Complex.reCLM.hasSum hgsum.hasSum).tsum_eq).symm
    have hpt : ∀ n : ℕ, (g n).re
        = ∑ a ∈ A, q a * (((z * w a) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re := by
      intro n
      rw [hgdef]
      simp only [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show (z ^ (n + 3) / (((n : ℕ) : ℂ) + 3)) * ((q a : ℂ) * w a ^ (n + 3))
          = (q a : ℂ) * ((z * w a) ^ (n + 3) / (((n : ℕ) : ℂ) + 3)) by
        rw [mul_pow]; ring, Complex.re_ofReal_mul]
    have hsum_a : ∀ a ∈ A, Summable
        (fun n : ℕ => q a * (((z * w a) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re) :=
      fun a ha => (summable_localLog_tail (hterm a ha)).mul_left _
    have hswap2 : (∑' n : ℕ, ∑ a ∈ A,
        q a * (((z * w a) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re)
        = ∑ a ∈ A, ∑' n : ℕ,
          q a * (((z * w a) ^ (n + 3) / ((n : ℕ) + 3) : ℂ)).re := by
      exact (hasSum_sum fun a ha => (hsum_a a ha).hasSum).tsum_eq
    rw [hswap, tsum_congr hpt, hswap2, logExponent, taylorExponent, ← mul_sub,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← mul_sub, localLog_sub_localTaylorTwo_eq_tsum (hterm a ha), ← tsum_mul_left]
  rw [hre, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hnormsum : Summable (fun n : ℕ => ‖g n‖) :=
    hgeo.of_nonneg_of_le (fun n => norm_nonneg _) hgnorm
  calc |(∑' n : ℕ, g n).re| ≤ ‖∑' n : ℕ, g n‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' n : ℕ, ‖g n‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, M * θ ^ (n + 3) := hnormsum.tsum_le_tsum hgnorm hgeo
    _ = M * θ ^ 3 / (1 - θ) := by
        rw [show (fun n : ℕ => M * θ ^ (n + 3)) = fun n : ℕ => (M * θ ^ 3) * θ ^ n from
          funext fun n => by rw [pow_add]; ring, tsum_mul_left,
          tsum_geometric_of_lt_one hθ0 hθ, div_eq_mul_inv]

/-- **The quadratic model, in terms of the combination moments.**

`T = 2 Re(z m₁) + Re(z² m₂)`, where `m₁ = ∑_a q_a w_a` and `m₂ = ∑_a q_a w_a²`.  Real
coefficients pull through the real part, which is the whole computation. -/
lemma taylorExponent_eq_re {A : Finset ι} (q : ι → ℝ) (w : ι → ℂ) (z : ℂ) :
    taylorExponent A q w z
      = 2 * (z * ∑ a ∈ A, (q a : ℂ) * w a).re
        + (z ^ 2 * ∑ a ∈ A, (q a : ℂ) * w a ^ 2).re := by
  have h1 : (z * ∑ a ∈ A, (q a : ℂ) * w a).re = ∑ a ∈ A, q a * (z * w a).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show z * ((q a : ℂ) * w a) = ((q a : ℝ) : ℂ) * (z * w a) by ring,
      Complex.re_ofReal_mul]
  have h2 : (z ^ 2 * ∑ a ∈ A, (q a : ℂ) * w a ^ 2).re
      = ∑ a ∈ A, q a * (z ^ 2 * w a ^ 2).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show z ^ 2 * ((q a : ℂ) * w a ^ 2) = ((q a : ℝ) : ℂ) * (z ^ 2 * w a ^ 2) by ring,
      Complex.re_ofReal_mul]
  rw [h1, h2, taylorExponent, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold localTaylorTwo
  ring

/-- **The model is small exactly when the combination moments are.**

`|T| ≤ 2‖m₁‖ + ‖m₂‖`.  Compare `RMF.abs_taylorExponent_le`, which gives `4 Q |A| t` — correct but
blind to any cancellation among the weights, and therefore useless when one coefficient is
large. -/
lemma abs_taylorExponent_le_moments {A : Finset ι} {q : ι → ℝ} {w : ι → ℂ} {z : ℂ}
    (hz : ‖z‖ = 1) :
    |taylorExponent A q w z|
      ≤ 2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := by
  have h1 : |2 * (z * ∑ a ∈ A, (q a : ℂ) * w a).re|
      ≤ 2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc |(z * ∑ a ∈ A, (q a : ℂ) * w a).re| ≤ ‖z * ∑ a ∈ A, (q a : ℂ) * w a‖ :=
          Complex.abs_re_le_norm _
      _ = ‖∑ a ∈ A, (q a : ℂ) * w a‖ := by rw [norm_mul, hz, one_mul]
  have h2 : |(z ^ 2 * ∑ a ∈ A, (q a : ℂ) * w a ^ 2).re|
      ≤ ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := by
    calc |(z ^ 2 * ∑ a ∈ A, (q a : ℂ) * w a ^ 2).re|
        ≤ ‖z ^ 2 * ∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := Complex.abs_re_le_norm _
      _ = ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := by
          rw [norm_mul, norm_pow, hz, one_pow, one_mul]
  rw [taylorExponent_eq_re]
  exact le_trans (abs_add_le _ _) (by linarith)

/-- **The multi-weight local expansion, through the combination moments**: if `‖w_a‖ < 1`,
`2‖m₁‖ + ‖m₂‖ ≤ 1` and `ε ≤ 1` bounds `|logExponent - taylorExponent|` on the circle, then
`|E_z ∏_a ‖(1 - z w_a)⁻¹‖^{2q_a} - (1 + ‖m₁‖²)| ≤ 2eε + (2‖m₁‖ + ‖m₂‖)³ + ‖m₂‖²/4`.  No hypothesis
refers to the individual weights, unlike the `4 Q |A| t ≤ 1` of
`RMF.abs_integral_prod_localIntegrand_sub_le`, so this reaches Hamdan's regime, where `λ₂` is large
but `λ₂ Δ` is not; `ε` comes from `RMF.abs_logExponent_sub_taylorExponent_le_of_moments`. -/
theorem abs_integral_prod_localIntegrand_sub_le_of_moments {A : Finset ι} {q : ι → ℝ}
    {w : ι → ℂ} {ε : ℝ} (hw1 : ∀ a ∈ A, ‖w a‖ < 1)
    (hκ : 2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ≤ 1)
    (hε : ε ≤ 1)
    (hLT : ∀ z : ℂ, ‖z‖ = 1 →
      |logExponent A q w z - taylorExponent A q w z| ≤ ε) :
    |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
        - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)|
      ≤ 2 * Real.exp 1 * ε
        + (2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖) ^ 3
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := by
  have hκ0 : (0 : ℝ) ≤ 2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖
      + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := by positivity
  -- pointwise facts on the circle
  have hae : ∀ᵐ z ∂steinhausLaw,
      (∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a)) = Real.exp (logExponent A q w z) := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact prod_norm_inv_one_sub_rpow_eq_exp A q w hz hw1
  have hTae : ∀ᵐ z ∂steinhausLaw, |taylorExponent A q w z| ≤ 1 := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact le_trans (abs_taylorExponent_le_moments hz) hκ
  have hTκ : ∀ᵐ z ∂steinhausLaw, |taylorExponent A q w z|
      ≤ 2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact abs_taylorExponent_le_moments hz
  have hLTae : ∀ᵐ z ∂steinhausLaw,
      |logExponent A q w z - taylorExponent A q w z| ≤ ε := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact hLT z hz
  have hLae : ∀ᵐ z ∂steinhausLaw, |logExponent A q w z| ≤ 2 := by
    filter_upwards [hTae, hLTae] with z h1 h2
    have h3 := abs_sub_abs_le_abs_sub (logExponent A q w z) (taylorExponent A q w z)
    linarith
  -- integrability, all from boundedness
  have hmT := measurable_taylorExponent A q w
  have hmL := measurable_logExponent A q w
  have hiT2 : Integrable (fun z => taylorExponent A q w z ^ 2) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (hmT.pow_const 2).aestronglyMeasurable 1 <| by
      filter_upwards [hTae] with z hz
      rw [Real.norm_eq_abs, abs_pow]
      nlinarith [abs_nonneg (taylorExponent A q w z)]
  have hiT : Integrable (taylorExponent A q w) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw hmT.aestronglyMeasurable 1 <| by
      filter_upwards [hTae] with z hz
      rwa [Real.norm_eq_abs]
  have hiexpT : Integrable (fun z => Real.exp (taylorExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      (Real.measurable_exp.comp hmT).aestronglyMeasurable (Real.exp 1) <| by
      filter_upwards [hTae] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 hz).2
  have hiexpL : Integrable (fun z => Real.exp (logExponent A q w z)) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw
      (Real.measurable_exp.comp hmL).aestronglyMeasurable (Real.exp 2) <| by
      filter_upwards [hLae] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 hz).2
  have hiquad₁ : Integrable (fun z : ℂ => 1 + taylorExponent A q w z) steinhausLaw :=
    (integrable_const 1).add hiT
  have hiquad : Integrable
      (fun z => 1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2) steinhausLaw :=
    hiquad₁.add (hiT2.div_const 2)
  rw [integral_congr_ae hae]
  -- step 1: `exp(logExponent)` against `exp(taylorExponent)`
  have hstep1 : |(∫ z, Real.exp (logExponent A q w z) ∂steinhausLaw)
      - ∫ z, Real.exp (taylorExponent A q w z) ∂steinhausLaw|
      ≤ 2 * Real.exp 1 * ε := by
    rw [← integral_sub hiexpL hiexpT]
    have hb : ∀ᵐ z ∂steinhausLaw,
        ‖Real.exp (logExponent A q w z) - Real.exp (taylorExponent A q w z)‖
          ≤ 2 * Real.exp 1 * ε := by
      filter_upwards [hTae, hLTae] with z h1 h2
      have hid : Real.exp (logExponent A q w z) - Real.exp (taylorExponent A q w z)
          = Real.exp (taylorExponent A q w z)
            * (Real.exp (logExponent A q w z - taylorExponent A q w z) - 1) := by
        rw [mul_sub, ← Real.exp_add, mul_one]
        ring_nf
      have h4 : |logExponent A q w z - taylorExponent A q w z| ≤ 1 := le_trans h2 hε
      have h5 := Real.abs_exp_sub_one_le h4
      have h6 : Real.exp (taylorExponent A q w z) ≤ Real.exp 1 :=
        Real.exp_le_exp.2 (abs_le.1 h1).2
      rw [Real.norm_eq_abs, hid, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (taylorExponent A q w z)
            * |Real.exp (logExponent A q w z - taylorExponent A q w z) - 1|
          ≤ Real.exp 1 * (2 * ε) := by
            refine mul_le_mul h6 (le_trans h5 (by linarith)) (abs_nonneg _) (Real.exp_pos _).le
        _ = 2 * Real.exp 1 * ε := by ring
    have key := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at key
    simpa using key
  -- step 2: the quadratic Taylor remainder of `exp`
  have hstep2 : |(∫ z, Real.exp (taylorExponent A q w z) ∂steinhausLaw)
      - ∫ z, (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2) ∂steinhausLaw|
      ≤ (2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖ + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖) ^ 3 := by
    rw [← integral_sub hiexpT hiquad]
    have hb : ∀ᵐ z ∂steinhausLaw,
        ‖Real.exp (taylorExponent A q w z)
            - (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2)‖
          ≤ (2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖
              + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖) ^ 3 := by
      filter_upwards [hTae, hTκ] with z h1 h2
      rw [Real.norm_eq_abs]
      calc |Real.exp (taylorExponent A q w z)
              - (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2)|
          ≤ |taylorExponent A q w z| ^ 3 := abs_exp_sub_taylor_le h1
        _ ≤ (2 * ‖∑ a ∈ A, (q a : ℂ) * w a‖
              + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖) ^ 3 :=
            pow_le_pow_left₀ (abs_nonneg _) h2 3
    have key := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at key
    simpa using key
  -- step 3: the quadratic integrates to `1 + ‖m₁‖² + ‖m₂‖²/4`
  have hquad : (∫ z, (1 + taylorExponent A q w z + taylorExponent A q w z ^ 2 / 2)
      ∂steinhausLaw)
      = 1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := by
    rw [integral_add hiquad₁ (hiT2.div_const 2), integral_add (integrable_const 1) hiT,
      integral_const, integral_taylorExponent, integral_div, integral_taylorExponent_sq]
    simp only [probReal_univ, smul_eq_mul, mul_one, add_zero]
    ring
  rw [hquad] at hstep2
  have h1 := abs_le.1 hstep1
  have h2 := abs_le.1 hstep2
  have h3 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 4 := by positivity
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### The increment of two abscissas

The combination moments of Hamdan's weight `q = (λ₁, λ₂, -λ₂)/2` at the three abscissas
`σ, σ + i h₁, σ + i h₂` are

```
m_k = (λ₁/2) w₀^k + (λ₂/2) (w₁^k - w₂^k),      w_a = p^{-s_a}
```

so everything hinges on the **power difference** `w₁^k - w₂^k`, whose modulus carries a factor
`‖w₁ - w₂‖ ≤ p^{-σ} |h₁ - h₂| log p`.  Three elementary ingredients, in order: the algebraic power
difference, the chord bound for prime powers, and the Lipschitz bound for `log` away from `0` that
keeps the crude estimates uniform in `λ₂`. -/

/-- **A power difference.**  `‖w₁^k - w₂^k‖ ≤ k t^{k-1} ‖w₁ - w₂‖` when both weights have modulus
at most `t`.

The geometric factorisation `w₁^k - w₂^k = (∑_{i<k} w₁^i w₂^{k-1-i})(w₁ - w₂)`, with each of the
`k` terms of modulus at most `t^{k-1}`. -/
lemma norm_pow_sub_pow_le {w₁ w₂ : ℂ} {t : ℝ} (h₁ : ‖w₁‖ ≤ t) (h₂ : ‖w₂‖ ≤ t) (k : ℕ) :
    ‖w₁ ^ k - w₂ ^ k‖ ≤ k * t ^ (k - 1) * ‖w₁ - w₂‖ := by
  have ht0 : (0 : ℝ) ≤ t := le_trans (norm_nonneg _) h₁
  rw [← geom_sum₂_mul w₁ w₂ k, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ i ∈ Finset.range k, w₁ ^ i * w₂ ^ (k - 1 - i)‖
      ≤ ∑ i ∈ Finset.range k, ‖w₁ ^ i * w₂ ^ (k - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range k, t ^ (k - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i + (k - 1 - i) = k - 1 := by
          have := Finset.mem_range.1 hi
          omega
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖w₁‖ ^ i * ‖w₂‖ ^ (k - 1 - i) ≤ t ^ i * t ^ (k - 1 - i) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₁ i)
                (pow_le_pow_left₀ (norm_nonneg _) h₂ _) (by positivity) (by positivity)
          _ = t ^ (k - 1) := by rw [← pow_add, hik]
    _ = k * t ^ (k - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The chord bound for prime powers**: two points with the same real part give
`‖p^{-s₁} - p^{-s₂}‖ ≤ p^{-σ} |t₁ - t₂| log p`.  Squared, this is the quadratic cosine bound
`2(1 - cos(Δ log p)) ≤ (Δ log p)²`.  `RMF.one_sub_cos_le_abs` is the linear one, used where the
kernel is summed against `p^{-2σ}` and only `∑_p p^{-2σ} log p` should appear; here the difference
is taken before any summation. -/
lemma norm_natCast_cpow_neg_sub_le {p : ℕ} (hp : 0 < p) {s₁ s₂ : ℂ} {σ : ℝ}
    (h₁ : s₁.re = σ) (h₂ : s₂.re = σ) :
    ‖(p : ℂ) ^ (-s₁) - (p : ℂ) ^ (-s₂)‖
      ≤ (p : ℝ) ^ (-σ) * (|s₁.im - s₂.im| * Real.log p) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
  have hpow0 : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hpR _
  have hn₁ : ‖(p : ℂ) ^ (-s₁)‖ = (p : ℝ) ^ (-σ) := by
    rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re, h₁]
  have hn₂ : ‖(p : ℂ) ^ (-s₂)‖ = (p : ℝ) ^ (-σ) := by
    rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re, h₂]
  have hrhs0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) * (|s₁.im - s₂.im| * Real.log p) := by positivity
  have hsplit : (p : ℝ) ^ (-(σ + σ)) = (p : ℝ) ^ (-σ) * (p : ℝ) ^ (-σ) := by
    rw [← Real.rpow_add hpR]
    ring_nf
  have hsq : ‖(p : ℂ) ^ (-s₁) - (p : ℂ) ^ (-s₂)‖ ^ 2
      ≤ ((p : ℝ) ^ (-σ) * (|s₁.im - s₂.im| * Real.log p)) ^ 2 := by
    have hns : ‖(p : ℂ) ^ (-s₁) - (p : ℂ) ^ (-s₂)‖ ^ 2
        = 2 * ((p : ℝ) ^ (-σ) * (p : ℝ) ^ (-σ))
          * (1 - Real.cos ((s₁.im - s₂.im) * Real.log p)) := by
      rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, hn₁, hn₂, re_natCast_cpow_neg_mul_conj hp, h₁, h₂, hsplit]
      ring
    have hcos : 1 - Real.cos ((s₁.im - s₂.im) * Real.log p)
        ≤ ((s₁.im - s₂.im) * Real.log p) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := (s₁.im - s₂.im) * Real.log p)]
    have habs : ((s₁.im - s₂.im) * Real.log p) ^ 2
        = (|s₁.im - s₂.im| * Real.log p) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    rw [hns]
    nlinarith [hpow0.le, sq_nonneg (|s₁.im - s₂.im| * Real.log p),
      mul_pos hpow0 hpow0]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs0] at this

/-- **`log` is Lipschitz away from zero.**  `|log a - log b| ≤ |a - b| / m` when both arguments
are at least `m > 0`.

This is what keeps the crude bounds of the pair estimate uniform in `λ₂`: the exponent
`λ₂ (localLog(w₁, z) - localLog(w₂, z))` is controlled by `λ₂ ‖w₁ - w₂‖ / (1 - θ)`, which stays
bounded as `λ₂ → ∞` with `λ₂ ‖w₁ - w₂‖` fixed. -/
lemma abs_log_sub_log_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have key : ∀ u v : ℝ, m ≤ u → m ≤ v → u ≤ v → Real.log v - Real.log u ≤ (v - u) / m := by
    intro u v hu hv huv
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hm hu
    have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hm hv
    have h1 : Real.log v - Real.log u ≤ v / u - 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < v / u by positivity)
      rwa [Real.log_div hv0.ne' hu0.ne'] at h
    have h2 : (Real.log v - Real.log u) * u ≤ v - u := by
      have h3 := mul_le_mul_of_nonneg_right h1 hu0.le
      have h4 : (v / u - 1) * u = v - u := by field_simp
      linarith [h4 ▸ h3]
    have h3 : (0 : ℝ) ≤ Real.log v - Real.log u :=
      sub_nonneg.2 (Real.log_le_log hu0 huv)
    rw [le_div_iff₀ hm]
    nlinarith
  rcases le_total a b with h | h
  · rw [abs_sub_comm (Real.log a), abs_sub_comm a,
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log (lt_of_lt_of_le hm ha) h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact key a b ha hb h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log (lt_of_lt_of_le hm hb) h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact key b a hb ha h

/-- `x^{-σ} \log x ≤ 1/σ`: the elementary `\log x ≤ x^σ/σ`.

The point of this bound is that it is **uniform in `p`**: the per-prime smallness the local
expansion needs is `M_p p^{-σ} ≤ 1/4` with `M_p = λ₁/2 + (λ₂ Δ/2) \log p`, and `\log p \cdot p^{-σ}`
does not grow. -/
lemma rpow_neg_mul_log_le {x σ : ℝ} (hx : 0 ≤ x) (hσ : 0 < σ) :
    x ^ (-σ) * Real.log x ≤ 1 / σ := by
  rcases eq_or_lt_of_le hx with h | hx0
  · rw [← h, Real.zero_rpow (by simpa using hσ.ne'), Real.log_zero, mul_zero]
    positivity
  · have h1 : Real.log x ≤ x ^ σ / σ := Real.log_le_rpow_div hx hσ
    have h2 : (0 : ℝ) < x ^ (-σ) := Real.rpow_pos_of_pos hx0 _
    calc x ^ (-σ) * Real.log x ≤ x ^ (-σ) * (x ^ σ / σ) :=
          mul_le_mul_of_nonneg_left h1 h2.le
      _ = 1 / σ := by
          rw [mul_div_assoc', ← Real.rpow_add hx0, neg_add_cancel, Real.rpow_zero]

/-! ### The three-abscissa family

Hamdan's Laplace transform is the joint moment at `q = (λ₁, λ₂, -λ₂)/2` over the abscissas
`σ, σ + i h₁, σ + i h₂`.  Naming the two families once keeps the statements readable and records the
one structural fact everything below rests on: **the second and third weights are exactly
opposite**, so every quantity sees the pair only through the increment `w₁ - w₂`. -/

/-- Hamdan's three weights `(λ₁, λ₂, -λ₂)/2`, halved because a joint moment carries `2 q_a`. -/
noncomputable def pairWeight (l₁ l₂ : ℝ) : Fin 3 → ℝ := ![l₁ / 2, l₂ / 2, -(l₂ / 2)]

/-- The three abscissas `σ`, `σ + i h₁`, `σ + i h₂`. -/
noncomputable def pairAbscissa (σ h₁ h₂ : ℝ) : Fin 3 → ℂ :=
  ![(σ : ℂ), (σ : ℂ) + (h₁ : ℂ) * Complex.I, (σ : ℂ) + (h₂ : ℂ) * Complex.I]

/-- A weighted sum against `RMF.pairWeight` sees the pair only through `g 1 - g 2`. -/
lemma sum_pairWeight_mul (l₁ l₂ : ℝ) (g : Fin 3 → ℝ) :
    ∑ a, pairWeight l₁ l₂ a * g a = l₁ / 2 * g 0 + l₂ / 2 * (g 1 - g 2) := by
  simp only [Fin.sum_univ_three, pairWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The same, over `ℂ`: this is the combination moment `m_k` when `g a = w a ^ k`. -/
lemma sum_pairWeight_smul (l₁ l₂ : ℝ) (g : Fin 3 → ℂ) :
    ∑ a, (pairWeight l₁ l₂ a : ℂ) * g a
      = ((l₁ / 2 : ℝ) : ℂ) * g 0 + ((l₂ / 2 : ℝ) : ℂ) * (g 1 - g 2) := by
  simp only [Fin.sum_univ_three, pairWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  push_cast
  ring

lemma pairAbscissa_re (σ h₁ h₂ : ℝ) (a : Fin 3) : (pairAbscissa σ h₁ h₂ a).re = σ := by
  fin_cases a <;>
    simp [pairAbscissa]

lemma pairAbscissa_im_one (σ h₁ h₂ : ℝ) : (pairAbscissa σ h₁ h₂ 1).im = h₁ := by
  simp [pairAbscissa]

lemma pairAbscissa_im_two (σ h₁ h₂ : ℝ) : (pairAbscissa σ h₁ h₂ 2).im = h₂ := by
  simp [pairAbscissa]

/-- **The combination moments of the pair**: `‖m_k‖ ≤ M k t^k` for `k ≥ 1`, with
`M = λ₁/2 + (λ₂/2) d`, when all three weights have modulus at most `t` and `‖w₁ - w₂‖ ≤ t d`.  This
is the hypothesis of `RMF.abs_logExponent_sub_taylorExponent_le_of_moments`, and `M` does not grow
with `λ₂` as long as `λ₂ d` stays bounded: Hamdan's regime `λ₂ ≤ |h₁ - h₂|^{-1}`. -/
lemma norm_sum_pairWeight_pow_le {l₁ l₂ t d : ℝ} {w : Fin 3 → ℂ} (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (h0 : ‖w 0‖ ≤ t) (h1 : ‖w 1‖ ≤ t) (h2 : ‖w 2‖ ≤ t)
    (h12 : ‖w 1 - w 2‖ ≤ t * d) {k : ℕ} (hk : 1 ≤ k) :
    ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ k‖ ≤ (l₁ / 2 + l₂ / 2 * d) * k * t ^ k := by
  have ht0 : (0 : ℝ) ≤ t := le_trans (norm_nonneg _) h0
  have htk : (0 : ℝ) ≤ t ^ k := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpow : t ^ (k - 1) * t = t ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  have hterm0 : ‖((l₁ / 2 : ℝ) : ℂ) * w 0 ^ k‖ ≤ l₁ / 2 * t ^ k := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h0 k) (by linarith)
  have hterm1 : ‖((l₂ / 2 : ℝ) : ℂ) * (w 1 ^ k - w 2 ^ k)‖ ≤ l₂ / 2 * ((k : ℝ) * (t ^ k * d)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc ‖w 1 ^ k - w 2 ^ k‖ ≤ (k : ℝ) * t ^ (k - 1) * ‖w 1 - w 2‖ :=
          norm_pow_sub_pow_le h1 h2 k
      _ ≤ (k : ℝ) * t ^ (k - 1) * (t * d) := by
          refine mul_le_mul_of_nonneg_left h12 ?_
          positivity
      _ = (k : ℝ) * (t ^ k * d) := by rw [← hpow]; ring
  rw [sum_pairWeight_smul]
  have hsum := norm_add_le (((l₁ / 2 : ℝ) : ℂ) * w 0 ^ k)
    (((l₂ / 2 : ℝ) : ℂ) * (w 1 ^ k - w 2 ^ k))
  nlinarith [mul_nonneg (mul_nonneg hl₁ htk) (sub_nonneg.2 hk1)]

/-- **The first moment of the pair, squared**: `‖m₁‖² ≤ λ₁² t²/4 + ((λ₁λ₂ + λ₂²)/2) t² d`.  The
summands are Hamdan's three: `λ₁² j/4` after summing `t² = p^{-2σ}` over the primes, and two
increment terms proportional to `d = Δ log p`, whose prime sum is `Δ e^j`.  Bounding
`‖w₁ - w₂‖²` by `‖w₁ - w₂‖ · 2t` keeps the prime sum inside `∑_p p^{-2σ} log p`. -/
lemma norm_sum_pairWeight_sq_le {l₁ l₂ t d : ℝ} {w : Fin 3 → ℂ} (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (h0 : ‖w 0‖ ≤ t) (h1 : ‖w 1‖ ≤ t) (h2 : ‖w 2‖ ≤ t)
    (h12 : ‖w 1 - w 2‖ ≤ t * d) :
    ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2
      ≤ l₁ ^ 2 / 4 * t ^ 2 + (l₁ * l₂ + l₂ ^ 2) / 2 * (t ^ 2 * d) := by
  have ht0 : (0 : ℝ) ≤ t := le_trans (norm_nonneg _) h0
  have h2t : ‖w 1 - w 2‖ ≤ 2 * t := by
    calc ‖w 1 - w 2‖ ≤ ‖w 1‖ + ‖w 2‖ := norm_sub_le _ _
      _ ≤ 2 * t := by linarith
  have hX0 : (0 : ℝ) ≤ ‖w 1 - w 2‖ := norm_nonneg _
  have hbound : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖
      ≤ l₁ / 2 * t + l₂ / 2 * ‖w 1 - w 2‖ := by
    rw [sum_pairWeight_smul]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ l₁ / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ l₂ / 2)]
    have hstep : l₁ / 2 * ‖w 0‖ ≤ l₁ / 2 * t :=
      mul_le_mul_of_nonneg_left h0 (by linarith)
    linarith
  have hsq : ‖w 1 - w 2‖ * ‖w 1 - w 2‖ ≤ (2 * t) * (t * d) :=
    mul_le_mul h2t h12 hX0 (by linarith)
  have hlin : l₁ * l₂ * t * ‖w 1 - w 2‖ ≤ l₁ * l₂ * t * (t * d) := by
    refine mul_le_mul_of_nonneg_left h12 ?_
    positivity
  have hnn : (0 : ℝ) ≤ l₁ / 2 * t + l₂ / 2 * ‖w 1 - w 2‖ := by positivity
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) hbound 2, sq_nonneg l₂]

/-- `log((1-θ)⁻¹) ≤ θ/(1-θ)`. -/
lemma log_inv_one_sub_le {θ : ℝ} (hθ : θ < 1) :
    Real.log ((1 - θ)⁻¹) ≤ θ / (1 - θ) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 - θ)⁻¹ by positivity)
  have he : (1 - θ)⁻¹ - 1 = θ / (1 - θ) := by
    rw [eq_div_iff h1θ.ne', sub_mul, inv_mul_cancel₀ h1θ.ne', one_mul]
    ring
  linarith [he ▸ h]

/-- **The crude exponent bound, uniform in `λ₂`.**

`|L| ≤ 2 M θ/(1-θ)` with `M = λ₁/2 + (λ₂/2) d`.  Compare `RMF.abs_logExponent_le`, whose
`2 Q |A| \log((1-θ)^{-1})` charges `λ₂` in full: here the pair enters only through
`λ₂ |localLog(w₁, z) - localLog(w₂, z)| ≤ λ₂ ‖w₁ - w₂‖/(1-θ)`, and `log` is Lipschitz away from
zero by `RMF.abs_log_sub_log_le`. -/
lemma abs_logExponent_pairWeight_le {l₁ l₂ θ d : ℝ} {w : Fin 3 → ℂ} {z : ℂ} (hz : ‖z‖ = 1)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hθ : θ < 1) (h0 : ‖w 0‖ ≤ θ)
    (h1 : ‖w 1‖ ≤ θ) (h2 : ‖w 2‖ ≤ θ) (h12 : ‖w 1 - w 2‖ ≤ θ * d) :
    |logExponent Finset.univ (pairWeight l₁ l₂) w z|
      ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * (θ / (1 - θ)) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hlow : ∀ a : Fin 3, ‖w a‖ ≤ θ → 1 - θ ≤ ‖1 - z * w a‖ := by
    intro a ha
    have := (norm_one_sub_mul_bounds (w := w a) hz).1
    linarith
  have hL0 : |localLog (w 0) z| ≤ θ / (1 - θ) :=
    le_trans (abs_localLog_le hz h0 hθ) (log_inv_one_sub_le hθ)
  have hL12 : |localLog (w 1) z - localLog (w 2) z| ≤ θ * d / (1 - θ) := by
    have hchord : |‖1 - z * w 2‖ - ‖1 - z * w 1‖| ≤ ‖w 1 - w 2‖ := by
      have h := abs_norm_sub_norm_le (1 - z * w 2) (1 - z * w 1)
      have he : (1 - z * w 2) - (1 - z * w 1) = z * (w 1 - w 2) := by ring
      rw [he, norm_mul, hz, one_mul] at h
      exact h
    have hlip := abs_log_sub_log_le h1θ (hlow 2 h2) (hlow 1 h1)
    have hstep : |localLog (w 1) z - localLog (w 2) z|
        = |Real.log ‖1 - z * w 2‖ - Real.log ‖1 - z * w 1‖| := by
      rw [localLog, localLog]
      ring_nf
    rw [hstep]
    refine le_trans hlip ?_
    rw [div_le_div_iff_of_pos_right h1θ]
    exact le_trans hchord h12
  have hsplit : logExponent Finset.univ (pairWeight l₁ l₂) w z
      = 2 * (l₁ / 2 * localLog (w 0) z + l₂ / 2 * (localLog (w 1) z - localLog (w 2) z)) := by
    rw [logExponent, sum_pairWeight_mul]
  have hassoc : 2 * (l₁ / 2 + l₂ / 2 * d) * (θ / (1 - θ))
      = 2 * ((l₁ / 2 + l₂ / 2 * d) * (θ / (1 - θ))) := by ring
  rw [hsplit, abs_mul, abs_two, hassoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ l₁ / 2),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ l₂ / 2)]
  have hA : l₁ / 2 * |localLog (w 0) z| ≤ l₁ / 2 * (θ / (1 - θ)) :=
    mul_le_mul_of_nonneg_left hL0 (by linarith)
  have hB : l₂ / 2 * |localLog (w 1) z - localLog (w 2) z| ≤ l₂ / 2 * (θ * d / (1 - θ)) :=
    mul_le_mul_of_nonneg_left hL12 (by linarith)
  have he : l₁ / 2 * (θ / (1 - θ)) + l₂ / 2 * (θ * d / (1 - θ))
      = (l₁ / 2 + l₂ / 2 * d) * (θ / (1 - θ)) := by ring
  linarith [he ▸ add_le_add hA hB]

/-! ### The pair expansion, prime by prime

Feeding the moment bounds of the previous section into
`RMF.abs_integral_prod_localIntegrand_sub_le_of_moments`, and gluing to the crude regime.

The gluing variable is **not** `t` but `x = (1 + M) t`, `M = λ₁/2 + (λ₂/2) d`.  That is forced:
the fine expansion is valid when the *combination* is small, i.e. when `M t` is small, and `M` is
unbounded in Hamdan's regime.  It is `x³`, not `M³ t³` and `M t³` separately, that the sum over
primes then has to converge — and it does, because `x = (1 + λ₁/2 + (λ₂ Δ/2)\log p) p^{-σ}`. -/

/-- **The pair expansion, before logarithms**: for `q = RMF.pairWeight λ₁ λ₂`,
`M = λ₁/2 + (λ₂/2) d` and `x = (1 + M) t ≤ (1-θ₀)/8`,
`|E_z ∏_a ‖(1 - z w_a)⁻¹‖^{2 q_a} - (1 + ‖m₁‖²)| ≤ (4e/(1-θ₀) + 65) x³`.  The smallness hypothesis
is on `x`, hence on `M t`, not on the individual exponents. -/
lemma abs_integral_prod_localIntegrand_sub_pair_le {l₁ l₂ t d θ₀ : ℝ} {w : Fin 3 → ℂ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hd0 : 0 ≤ d) (ht0 : 0 ≤ t) (htθ : t ≤ θ₀) (hθ₀ : θ₀ < 1)
    (hw : ∀ a, ‖w a‖ ≤ t) (h12 : ‖w 1 - w 2‖ ≤ t * d)
    (hsmall : (1 + (l₁ / 2 + l₂ / 2 * d)) * t ≤ (1 - θ₀) / 8) :
    |(∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
        - (1 + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2)|
      ≤ (4 * Real.exp 1 / (1 - θ₀) + 65) * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 := by
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  have ht1 : t < 1 := lt_of_le_of_lt htθ hθ₀
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have ht30 : (0 : ℝ) ≤ t ^ 3 := by positivity
  have ht3le : t ^ 3 ≤ t := by
    have h := mul_nonneg (mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - t))
      (by linarith : (0 : ℝ) ≤ 1 + t)
    linarith [h]
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = l₁ / 2 + l₂ / 2 * d := ⟨_, rfl⟩
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  rw [← hMdef] at hsmall ⊢
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (1 + M) * t := ⟨_, rfl⟩
  rw [← hxdef] at hsmall ⊢
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
  have hMtx : M * t ≤ x := by rw [hxdef]; nlinarith
  have hx3 : x ^ 3 = (1 + M) ^ 3 * t ^ 3 := by rw [hxdef]; ring
  have hM30 : (0 : ℝ) ≤ M ^ 3 := by positivity
  have hMsq0 : (0 : ℝ) ≤ M ^ 2 := by positivity
  have hMx3 : M * t ^ 3 ≤ x ^ 3 := by
    rw [hx3]
    exact mul_le_mul_of_nonneg_right (by nlinarith) ht30
  have hM2x3 : M ^ 2 * t ^ 3 ≤ x ^ 3 := by
    rw [hx3]
    exact mul_le_mul_of_nonneg_right (by nlinarith) ht30
  have hwlt : ∀ a ∈ (Finset.univ : Finset (Fin 3)), ‖w a‖ < 1 :=
    fun a _ => lt_of_le_of_lt (hw a) ht1
  have hwle : ∀ a ∈ (Finset.univ : Finset (Fin 3)), ‖w a‖ ≤ t := fun a _ => hw a
  have hmom : ∀ k : ℕ, 1 ≤ k →
      ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ k‖ ≤ M * k * t ^ k := by
    intro k hk
    rw [hMdef]
    exact norm_sum_pairWeight_pow_le hl₁ hl₂ (hw 0) (hw 1) (hw 2) h12 hk
  have hm1 : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ≤ M * t := by
    simpa using hmom 1 le_rfl
  have hm2 : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖ ≤ M * 2 * t ^ 2 := by
    simpa using hmom 2 (by norm_num)
  have hm20 : (0 : ℝ) ≤ ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖ := norm_nonneg _
  have hMt2 : M * t ^ 2 ≤ M * t := by nlinarith [mul_nonneg hM0 ht0]
  have hMt3 : M * t ^ 3 ≤ M * t := mul_le_mul_of_nonneg_left ht3le hM0
  have hMt : M * t ≤ (1 - θ₀) / 8 := le_trans hMtx hsmall
  have hkappa : 2 * ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖
      + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖ ≤ 1 := by linarith
  have hLT : ∀ z : ℂ, ‖z‖ = 1 →
      |logExponent Finset.univ (pairWeight l₁ l₂) w z
        - taylorExponent Finset.univ (pairWeight l₁ l₂) w z| ≤ 2 * (M * t ^ 3 / (1 - t)) :=
    fun z hz => abs_logExponent_sub_taylorExponent_le_of_moments hz hwle ht1 ht0
      fun k hk => hmom k (by omega)
  have hden : M * t ^ 3 / (1 - t) ≤ M * t ^ 3 / (1 - θ₀) := by
    rw [div_le_div_iff₀ h1t h1θ₀]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM0 ht30)
  have he1 : M * t ^ 3 / (1 - θ₀) ≤ x / (1 - θ₀) := by
    rw [div_le_div_iff_of_pos_right h1θ₀]
    exact le_trans hMt3 hMtx
  have he2 : x / (1 - θ₀) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ h1θ₀ (by norm_num)]
    linarith
  have hε1 : 2 * (M * t ^ 3 / (1 - t)) ≤ 1 := by linarith
  have hexp := abs_integral_prod_localIntegrand_sub_le_of_moments
    (A := (Finset.univ : Finset (Fin 3))) (q := pairWeight l₁ l₂) (w := w)
    (ε := 2 * (M * t ^ 3 / (1 - t))) hwlt hkappa hε1 hLT
  refine le_trans hexp ?_
  have hA : 2 * Real.exp 1 * (2 * (M * t ^ 3 / (1 - t)))
      ≤ 4 * Real.exp 1 / (1 - θ₀) * x ^ 3 := by
    have h1 : M * t ^ 3 / (1 - t) ≤ x ^ 3 / (1 - θ₀) :=
      le_trans hden (by rw [div_le_div_iff_of_pos_right h1θ₀]; exact hMx3)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * Real.exp 1)
    calc 2 * Real.exp 1 * (2 * (M * t ^ 3 / (1 - t)))
        = 4 * Real.exp 1 * (M * t ^ 3 / (1 - t)) := by ring
      _ ≤ 4 * Real.exp 1 * (x ^ 3 / (1 - θ₀)) := h2
      _ = 4 * Real.exp 1 / (1 - θ₀) * x ^ 3 := by ring
  have hB : (2 * ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖
      + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖) ^ 3 ≤ 64 * x ^ 3 := by
    have h1 : 2 * ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖
        + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖ ≤ 4 * x := by linarith
    calc (2 * ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖
          + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖) ^ 3 ≤ (4 * x) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h1 3
      _ = 64 * x ^ 3 := by ring
  have hC : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖ ^ 2 / 4 ≤ x ^ 3 := by
    have h1 : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a ^ 2‖ ^ 2 ≤ (M * 2 * t ^ 2) ^ 2 :=
      pow_le_pow_left₀ hm20 hm2 2
    have h2 : (M * 2 * t ^ 2) ^ 2 = 4 * (M ^ 2 * t ^ 3 * t) := by ring
    have h3 : M ^ 2 * t ^ 3 * t ≤ x ^ 3 := by
      have h := mul_le_mul_of_nonneg_left ht1.le (mul_nonneg hMsq0 ht30)
      rw [mul_one] at h
      linarith
    linarith
  linarith

/-- **The pair expansion after taking logarithms**: for `t ≤ θ₀ < 1`,
`log E_z ∏_a ‖(1 - z w_a)⁻¹‖^{2 q_a} = ‖m₁‖² + O(x³)`, `x = (1 + M) t`, with a constant depending
only on `θ₀`.  The pair analogue of `RMF.exists_abs_log_local_multi_le`, whose constant is
exponential in the exponents and so useless in Hamdan's regime. -/
theorem exists_abs_log_local_pair_le {θ₀ : ℝ} (hθ₀0 : 0 ≤ θ₀) (hθ₀ : θ₀ < 1) :
    ∃ C > 0, ∀ (l₁ l₂ t d : ℝ) (w : Fin 3 → ℂ), 0 ≤ l₁ → 0 ≤ l₂ → 0 ≤ d → 0 ≤ t → t ≤ θ₀ →
      (∀ a, ‖w a‖ ≤ t) → ‖w 1 - w 2‖ ≤ t * d →
        |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
            - ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2|
          ≤ C * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 := by
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = 4 * Real.exp 1 / (1 - θ₀) + 65 := ⟨_, rfl⟩
  have hCf0 : (0 : ℝ) < Cf := by rw [hCfdef]; positivity
  obtain ⟨d₀, hd₀def⟩ : ∃ d₀ : ℝ, d₀ = min ((1 - θ₀) / 8) (1 / (4 * (Cf + 1))) := ⟨_, rfl⟩
  have hd₀0 : (0 : ℝ) < d₀ := by
    rw [hd₀def]
    exact lt_min (by positivity) (by positivity)
  have hd₀8 : d₀ ≤ (1 - θ₀) / 8 := by rw [hd₀def]; exact min_le_left _ _
  have hd₀le : d₀ ≤ 1 / 8 := le_trans hd₀8 (by linarith)
  have hCd₀ : Cf * d₀ ≤ 1 / 4 := by
    have hd₀C : d₀ ≤ 1 / (4 * (Cf + 1)) := by rw [hd₀def]; exact min_le_right _ _
    have h1 : Cf * d₀ ≤ Cf * (1 / (4 * (Cf + 1))) :=
      mul_le_mul_of_nonneg_left hd₀C hCf0.le
    have h2 : Cf * (1 / (4 * (Cf + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  obtain ⟨Ctail, hCtail⟩ : ∃ Ctail : ℝ, Ctail = 2 / ((1 - θ₀) * d₀ ^ 2) + 1 / d₀ := ⟨_, rfl⟩
  have hCtail0 : (0 : ℝ) ≤ Ctail := by rw [hCtail]; positivity
  refine ⟨2 * (1 + Cf) ^ 2 + Cf + Ctail, by positivity, ?_⟩
  intro l₁ l₂ t d w hl₁ hl₂ hd0 ht0 htθ hw h12
  have ht1 : t < 1 := lt_of_le_of_lt htθ hθ₀
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hfine0 :=
    abs_integral_prod_localIntegrand_sub_pair_le hl₁ hl₂ hd0 ht0 htθ hθ₀ hw h12
  have hcrude0 : |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂steinhausLaw)| ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * (t / (1 - t)) :=
    abs_log_integral_prod_localIntegrand_le_of_bound
      (fun a _ => lt_of_le_of_lt (hw a) ht1) fun _ hz =>
      abs_logExponent_pairWeight_le hz hl₁ hl₂ ht1 (hw 0) (hw 1) (hw 2) h12
  have hm1' : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ≤ (l₁ / 2 + l₂ / 2 * d) * t := by
    simpa using norm_sum_pairWeight_pow_le hl₁ hl₂ (hw 0) (hw 1) (hw 2) h12 (k := 1) le_rfl
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = l₁ / 2 + l₂ / 2 * d := ⟨_, rfl⟩
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  rw [← hMdef] at hfine0 hcrude0 hm1' ⊢
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (1 + M) * t := ⟨_, rfl⟩
  rw [← hxdef] at hfine0 ⊢
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
  have hx20 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have hx30 : (0 : ℝ) ≤ x ^ 3 := by positivity
  have hMtx : M * t ≤ x := by rw [hxdef]; nlinarith
  have hm1x : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ≤ x := le_trans hm1' hMtx
  have hPx : |‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2| ≤ 1 * x ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (∑ a, (pairWeight l₁ l₂ a : ℂ) * w a)]
  have hP2 : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2 ≤ 1 * x ^ 2 := (abs_le.1 hPx).2
  have hP0 : (0 : ℝ) ≤ ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2 := by positivity
  have hcrudex : |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂steinhausLaw)| ≤ 2 * x / (1 - θ₀) := by
    refine le_trans hcrude0 ?_
    have hfrac : t / (1 - t) ≤ t / (1 - θ₀) := by
      rw [div_le_div_iff₀ h1t h1θ₀]
      exact mul_le_mul_of_nonneg_left (by linarith) ht0
    have h1 : 2 * M * (t / (1 - t)) ≤ 2 * M * (t / (1 - θ₀)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    have h2 : 2 * M * (t / (1 - θ₀)) ≤ 2 * x / (1 - θ₀) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right h1θ₀]
      linarith
    linarith
  rcases le_or_gt x d₀ with hfine | hbig
  · -- the fine regime: `x ≤ d₀` makes the combination small
    have hIP : |(∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
        - (1 + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2)| ≤ Cf * x ^ 3 := by
      rw [hCfdef]
      exact hfine0 (le_trans hfine hd₀8)
    have hhalf : |(∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
        - 1| ≤ 1 / 2 := by
      have h3 : Cf * x ^ 3 ≤ Cf * d₀ * x ^ 2 := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfine hx20) hCf0.le
        calc Cf * x ^ 3 = Cf * (x * x ^ 2) := by ring
          _ ≤ Cf * (d₀ * x ^ 2) := h
          _ = Cf * d₀ * x ^ 2 := by ring
      have h4 : Cf * d₀ * x ^ 2 ≤ 1 / 4 * x ^ 2 := mul_le_mul_of_nonneg_right hCd₀ hx20
      have h5 : x ^ 2 ≤ 1 / 64 := by nlinarith [le_trans hfine hd₀le]
      have h1 := abs_le.1 hIP
      rw [abs_le]
      constructor <;> linarith only [h1.1, h1.2, hP2, hP0, h3, h4, h5]
    have h := abs_log_sub_poly_le hx0
      (by linarith [le_trans hfine hd₀le]) hCf0.le hIP hPx hhalf
    calc |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
          - ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2|
        ≤ (2 * (1 + Cf) ^ 2 + Cf) * x ^ 3 := h
      _ ≤ (2 * (1 + Cf) ^ 2 + Cf + Ctail) * x ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) hx30
  · -- the crude regime: `x > d₀`, so `x³` dominates both `x` and `x²`
    have hA : 2 * x / (1 - θ₀) ≤ 2 / ((1 - θ₀) * d₀ ^ 2) * x ^ 3 := by
      have hxx : d₀ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hd₀0.le hbig.le 2
      rw [div_mul_eq_mul_div, div_le_div_iff₀ h1θ₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hxx
        (by positivity : (0 : ℝ) ≤ 2 * x * (1 - θ₀))]
    have hB : 1 * x ^ 2 ≤ 1 / d₀ * x ^ 3 := by
      rw [one_mul, div_mul_eq_mul_div, le_div_iff₀ hd₀0]
      nlinarith [sq_nonneg x, hbig.le]
    have hsplit := abs_sub (Real.log (∫ z, ∏ a,
        ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw))
      (‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2)
    have habsP : |‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2|
        = ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2 := abs_of_nonneg (by positivity)
    have hfin : (2 / ((1 - θ₀) * d₀ ^ 2) + 1 / d₀) * x ^ 3
        ≤ (2 * (1 + Cf) ^ 2 + Cf + Ctail) * x ^ 3 := by
      rw [← hCtail]
      exact mul_le_mul_of_nonneg_right
        (by linarith only [sq_nonneg (1 + Cf), hCf0.le]) hx30
    rw [habsP] at hsplit
    linarith only [hsplit, hcrudex, hP2, hA, hB, hfin]

/-! ### The pair expansion, summed over the primes

The per-prime error is `C ((1 + λ₁/2 + (λ₂ Δ/2)\log p) p^{-σ})³`, which carries powers of
`\log p` that `RMF.sum_primesBelow_rpow_le` cannot see.  They are traded for a slightly larger
abscissa: `\log p \cdot p^{-δ} ≤ 1/δ`, so the bracket is `≤ K p^{-(σ-δ)}` with
`K = 1 + λ₁/2 + λ₂Δ/(2δ)` independent of `p`, and `σ - δ ≥ σ₁ = (σ₀ + 1/3)/2 > 1/3` keeps the
resulting series convergent. -/

/-- **Trading a `log p` for a slightly larger abscissa.**

`(a + b \log x) x^{-σ} ≤ (a + b/δ) x^{-(σ-δ)}` for `x ≥ 1` and `δ > 0`. -/
lemma add_mul_log_mul_rpow_neg_le {x : ℝ} (hx1 : 1 ≤ x) {a b σ δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : 0 < δ) :
    (a + b * Real.log x) * x ^ (-σ) ≤ (a + b / δ) * x ^ (-(σ - δ)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hsplit : x ^ (-σ) = x ^ (-δ) * x ^ (-(σ - δ)) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hδ0 : (0 : ℝ) ≤ x ^ (-δ) := Real.rpow_nonneg hx0.le _
  have hδ1 : x ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hkey : (a + b * Real.log x) * x ^ (-δ) ≤ a + b / δ := by
    have h1 : a * x ^ (-δ) ≤ a := by nlinarith
    have h2 : b * (Real.log x * x ^ (-δ)) ≤ b * (1 / δ) :=
      mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact rpow_neg_mul_log_le hx0.le hδ) hb
    have h3 : b * (1 / δ) = b / δ := by ring
    nlinarith
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hx0.le _)

/-- **The pair expansion, summed over the primes**: over `p ∈ [y₀, y)`,
`log ∏_p E_z ∏_a ‖(1 - z p^{-s_a})⁻¹‖^{2q_a} = ∑_p ‖m₁(p)‖² + O(1)` for `λ₁ ≤ Λ` and
`λ₂ |h₁ - h₂| ≤ Λ`, with a constant depending only on `σ₀` and `Λ`.  **`λ₂` itself is not
bounded**, unlike in `RMF.exists_multi_prime_sum_bound_steinhausLaw`: Hamdan's chaining has
`λ₂ ≈ √V₂ e^{-j}|h₁-h₂|^{-1}` growing as the net refines, while `λ₂|h₁-h₂|` stays bounded. -/
theorem exists_pair_prime_sum_bound_steinhausLaw {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (l₁ l₂ σ h₁ h₂ : ℝ) (y₀ y : ℕ), 0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ →
      l₂ * |h₁ - h₂| ≤ Λ →
        |Real.log (∏ p ∈ primesIco y₀ y, ∫ z, ∏ a,
              ‖(1 - z * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a))⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
              ∂steinhausLaw)
            - ∑ p ∈ primesIco y₀ y, ‖∑ a,
                (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2|
          ≤ C := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨C₁, hC₁, hloc⟩ := exists_abs_log_local_pair_le hθ0 hθ
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (σ₀ - 1 / 3) / 2 := ⟨_, rfl⟩
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; linarith
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = (σ₀ + 1 / 3) / 2 := ⟨_, rfl⟩
  have hσ₁1 : 1 / 3 < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁δ : σ₀ - δ = σ₁ := by rw [hδdef, hσ₁def]; ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + Λ / 2 + Λ / 2 / δ := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hT0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₁) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨C₁ * K ^ 3 * (∑' n : ℕ, (n : ℝ) ^ (-3 * σ₁)) + 1, by positivity, ?_⟩
  intro l₁ l₂ σ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
  have hD0 : (0 : ℝ) ≤ |h₁ - h₂| := abs_nonneg _
  have hnorm : ∀ p ∈ primesIco y₀ y, ∀ a : Fin 3,
      ‖((p : ℂ)) ^ (-pairAbscissa σ h₁ h₂ a)‖ = (p : ℝ) ^ (-σ) := by
    intro p hp a
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos,
      Complex.neg_re, pairAbscissa_re]
  have hle : ∀ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hincr : ∀ p ∈ primesIco y₀ y,
      ‖(p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 1) - (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 2)‖
        ≤ (p : ℝ) ^ (-σ) * (|h₁ - h₂| * Real.log p) := by
    intro p hp
    have h := norm_natCast_cpow_neg_sub_le (prime_of_mem_primesIco hp).pos
      (s₁ := pairAbscissa σ h₁ h₂ 1) (s₂ := pairAbscissa σ h₁ h₂ 2) (σ := σ)
      (pairAbscissa_re σ h₁ h₂ 1) (pairAbscissa_re σ h₁ h₂ 2)
    rwa [pairAbscissa_im_one, pairAbscissa_im_two] at h
  have hpos : ∀ p ∈ primesIco y₀ y, 0 < ∫ z, ∏ a,
      ‖(1 - z * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a))⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂steinhausLaw := by
    intro p hp
    have hwlt : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        ‖(p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ < 1 := fun a _ => by
      rw [hnorm p hp a]
      exact lt_of_le_of_lt (hle p hp) hθ
    refine integral_prod_localIntegrand_pos_of_bound hwlt fun z hz =>
      abs_logExponent_pairWeight_le (θ := (p : ℝ) ^ (-σ))
        (d := |h₁ - h₂| * Real.log p) hz hl₁ hl₂ (lt_of_le_of_lt (hle p hp) hθ)
        (le_of_eq (hnorm p hp 0)) (le_of_eq (hnorm p hp 1)) (le_of_eq (hnorm p hp 2))
        (hincr p hp)
  have hterm : ∀ p ∈ primesIco y₀ y,
      |Real.log (∫ z, ∏ a,
            ‖(1 - z * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a))⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
            ∂steinhausLaw)
          - ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2|
        ≤ C₁ * K ^ 3 * (p : ℝ) ^ (-3 * σ₁) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h := hloc l₁ l₂ ((p : ℝ) ^ (-σ)) (|h₁ - h₂| * Real.log p)
      (fun a => (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)) hl₁ hl₂ (by positivity) ht0
      (hle p hp) (fun a => le_of_eq (hnorm p hp a)) (hincr p hp)
    refine le_trans h ?_
    have hxK : (1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p))) * (p : ℝ) ^ (-σ)
        ≤ K * (p : ℝ) ^ (-σ₁) := by
      have hrw : (1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p)))
          = (1 + l₁ / 2) + l₂ * |h₁ - h₂| / 2 * Real.log p := by ring
      rw [hrw]
      refine le_trans (add_mul_log_mul_rpow_neg_le hp1 (by linarith)
        (by positivity) hδ0) ?_
      have hcoeff : (1 + l₁ / 2) + l₂ * |h₁ - h₂| / 2 / δ ≤ K := by
        have hb : l₂ * |h₁ - h₂| / 2 / δ ≤ Λ / 2 / δ := by
          rw [div_le_div_iff_of_pos_right hδ0]
          linarith
        rw [hKdef]
        linarith
      have hexp : (p : ℝ) ^ (-(σ - δ)) ≤ (p : ℝ) ^ (-σ₁) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by rw [← hσ₁δ]; linarith)
      have hpos1 : (0 : ℝ) ≤ (p : ℝ) ^ (-(σ - δ)) := Real.rpow_nonneg (by linarith) _
      calc ((1 + l₁ / 2) + l₂ * |h₁ - h₂| / 2 / δ) * (p : ℝ) ^ (-(σ - δ))
          ≤ K * (p : ℝ) ^ (-(σ - δ)) := mul_le_mul_of_nonneg_right hcoeff hpos1
        _ ≤ K * (p : ℝ) ^ (-σ₁) := mul_le_mul_of_nonneg_left hexp hK0.le
    have hcube : ((p : ℝ) ^ (-σ₁)) ^ 3 = (p : ℝ) ^ (-3 * σ₁) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ₁)) 3, ← Real.rpow_mul (by linarith)]
      congr 1
      push_cast
      ring
    have hx0 : (0 : ℝ) ≤ (1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p)))
        * (p : ℝ) ^ (-σ) := by positivity
    have hcubed := pow_le_pow_left₀ hx0 hxK 3
    have hRHS : (K * (p : ℝ) ^ (-σ₁)) ^ 3 = K ^ 3 * (p : ℝ) ^ (-3 * σ₁) := by
      rw [mul_pow, hcube]
    calc C₁ * ((1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p))) * (p : ℝ) ^ (-σ)) ^ 3
        ≤ C₁ * (K * (p : ℝ) ^ (-σ₁)) ^ 3 := mul_le_mul_of_nonneg_left hcubed hC₁.le
      _ = C₁ * K ^ 3 * (p : ℝ) ^ (-3 * σ₁) := by rw [hRHS]; ring
  have hmain := abs_log_prod_sub_sum_le hpos hterm
  refine le_trans hmain ?_
  have hsum : ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * σ₁)
      ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * σ₁) := sum_primesIco_rpow_le hσ₁1 le_rfl y₀ y
  have hC0 : (0 : ℝ) ≤ C₁ * K ^ 3 := by positivity
  nlinarith

/-! ### Evaluating the main term of the pair

`∑_{p<y} ‖m₁(p)‖²` splits into Hamdan's three pieces: `λ₁²/4` against `∑_p p^{-2σ}` — which at
`σ = 1/2` is `\log\log y + O(1) = j + O(1)`, his `λ₁² j/4` — and two increment terms, each carrying
a factor `Δ = |h₁ - h₂|` and summed against `∑_p p^{-2σ}\log p ≤ \log y + O(1) = e^j + O(1)`.

Hamdan states the second and third as `cλ₂² e^jΔ` and `c(λ₂ e^jΔ)²`.  The bound below gives
`(λ₁λ₂ + λ₂²)Δ e^j/2`, which is at least as strong: `Δ e^j ≤ 1` in his range, so
`(λ₂ e^jΔ)² ≤ λ₂² e^jΔ`, and `λ₁λ₂ ≤ Λλ₂ ≤ Λλ₂²` once `λ₂ ≥ 1`. -/

/-- **The main term of the pair expansion.**  Over `p ∈ [y₀, y)`,

`∑_p ‖m₁(p)‖² ≤ (λ₁²/4) ∑_p p^{-2σ} + ((λ₁λ₂ + λ₂²)/2) Δ ∑_p p^{-2σ}\log p`.

The two prime sums are left symbolic, as in `RMF.sum_norm_sum_smul_cpow_le`, so the statement does
not depend on where the block cutoff sits. -/
theorem sum_norm_sum_pairWeight_cpow_le {l₁ l₂ σ h₁ h₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (y₀ y : ℕ) :
    (∑ p ∈ primesIco y₀ y,
        ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2)
      ≤ l₁ ^ 2 / 4 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)
        + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂|
          * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
  have hterm : ∀ p ∈ primesIco y₀ y,
      ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2
        ≤ l₁ ^ 2 / 4 * (p : ℝ) ^ (-2 * σ)
          + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂| * ((p : ℝ) ^ (-2 * σ) * Real.log p) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hnorm : ∀ a : Fin 3, ‖((p : ℂ)) ^ (-pairAbscissa σ h₁ h₂ a)‖ = (p : ℝ) ^ (-σ) :=
      fun a => by
        rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, pairAbscissa_re]
    have hincr : ‖(p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 1) - (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 2)‖
        ≤ (p : ℝ) ^ (-σ) * (|h₁ - h₂| * Real.log p) := by
      have h := norm_natCast_cpow_neg_sub_le hpp.pos
        (s₁ := pairAbscissa σ h₁ h₂ 1) (s₂ := pairAbscissa σ h₁ h₂ 2) (σ := σ)
        (pairAbscissa_re σ h₁ h₂ 1) (pairAbscissa_re σ h₁ h₂ 2)
      rwa [pairAbscissa_im_one, pairAbscissa_im_two] at h
    have h := norm_sum_pairWeight_sq_le (l₁ := l₁) (l₂ := l₂) (t := (p : ℝ) ^ (-σ))
      (d := |h₁ - h₂| * Real.log p)
      (w := fun a => (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)) hl₁ hl₂
      (le_of_eq (hnorm 0)) (le_of_eq (hnorm 1)) (le_of_eq (hnorm 2)) hincr
    have hsq : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-2 * σ) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    rw [hsq] at h
    calc ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2
        ≤ l₁ ^ 2 / 4 * (p : ℝ) ^ (-2 * σ)
          + (l₁ * l₂ + l₂ ^ 2) / 2 * ((p : ℝ) ^ (-2 * σ) * (|h₁ - h₂| * Real.log p)) := h
      _ = l₁ ^ 2 / 4 * (p : ℝ) ^ (-2 * σ)
          + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂| * ((p : ℝ) ^ (-2 * σ) * Real.log p) := by
          ring
  calc (∑ p ∈ primesIco y₀ y,
        ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2)
      ≤ ∑ p ∈ primesIco y₀ y, (l₁ ^ 2 / 4 * (p : ℝ) ^ (-2 * σ)
          + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂| * ((p : ℝ) ^ (-2 * σ) * Real.log p)) :=
        Finset.sum_le_sum hterm
    _ = l₁ ^ 2 / 4 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)
        + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂|
          * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ### Hamdan's Lemma B.1, Laplace half

Written additively, `∏_a ‖F_y(s_a)‖^{2q_a}` is `exp(λ₁ S_y(σ) + λ₂(S_y(σ+ih₁) - S_y(σ+ih₂)))`,
so the theorem below is exactly the Laplace-transform estimate that (B.2) feeds to Chernoff.
Compare `RMF.IsSteinhausRMF.exists_log_joint_moment_le`, which is the same statement with the
crude constants: there `Q` bounds every exponent and `D` every pair of heights, so the `λ₂` term
is `λ₂² \max_a|h_a|e^j`, which does **not** vanish with the increment.  Here it does. -/

/-- **Hamdan's Lemma B.1, Laplace half.**  With `S = log ‖F‖`, `Δ = |h₁-h₂|` and sums over
`p ∈ [y₀, y)`, `log E exp(λ₁S(σ) + λ₂(S(σ+ih₁) - S(σ+ih₂)))` is at most
`(λ₁²/4)∑_p p^{-2σ} + ((λ₁λ₂+λ₂²)/2)Δ∑_p p^{-2σ}\log p + C` for `0 ≤ λ₁ ≤ Λ`, `λ₂ ≥ 0`, `λ₂Δ ≤ Λ`,
with `C` independent of `f`, `μ`, `y₀`, `y`, the heights and the exponents.  `λ₂` itself is
unbounded, as in Hamdan's `1 ≤ λ₂ ≤ |h₁-h₂|^{-1}` and the chaining of his Lemma B.2. -/
theorem IsSteinhausRMF.exists_log_joint_moment_pair_le {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (l₁ l₂ σ h₁ h₂ : ℝ) (y₀ y : ℕ), 0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ →
        l₂ * |h₁ - h₂| ≤ Λ →
          Real.log (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖
                ^ (2 * pairWeight l₁ l₂ a) ∂μ)
            ≤ l₁ ^ 2 / 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
              + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂|
                * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
              + C := by
  obtain ⟨C, hC, hbound⟩ := exists_pair_prime_sum_bound_steinhausLaw (σ₀ := σ₀) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₁ l₂ σ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissa σ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissa_re]
    linarith
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y Finset.univ hre]
  have h1 := abs_le.1 (hbound l₁ l₂ σ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ)
  have h2 := sum_norm_sum_pairWeight_cpow_le (l₁ := l₁) (l₂ := l₂) (σ := σ)
    (h₁ := h₁) (h₂ := h₂) hl₁ hl₂ y₀ y
  linarith [h1.2]

/-! ### Lemma B.1 for the pair, assembled

Markov against the joint moment, exactly as in `RMF.IsSteinhausRMF.exists_measure_le_exp` but
with the pair cumulant bound, whose constants do not see `λ₂`.  Written additively the joint
moment is `E \exp(λ₁ S_y(σ) + λ₂(S_y(σ+ih₁) - S_y(σ+ih₂)))`, so this is Hamdan's (B.2). -/

/-- Each of the three weights has modulus at most `λ₁/2 + λ₂/2`. -/
lemma abs_pairWeight_le {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (a : Fin 3) :
    |pairWeight l₁ l₂ a| ≤ l₁ / 2 + l₂ / 2 := by
  have hcases : pairWeight l₁ l₂ a = l₁ / 2 ∨ pairWeight l₁ l₂ a = l₂ / 2
      ∨ pairWeight l₁ l₂ a = -(l₂ / 2) := by
    fin_cases a <;> simp [pairWeight]
  rcases hcases with h | h | h <;> rw [h, abs_le] <;> constructor <;> linarith

/-- The exponent of the joint moment is the pair combination of the walks. -/
lemma sum_two_mul_pairWeight_mul (l₁ l₂ : ℝ) (g : Fin 3 → ℝ) :
    (∑ a, 2 * pairWeight l₁ l₂ a * g a) = l₁ * g 0 + l₂ * (g 1 - g 2) := by
  simp only [Fin.sum_univ_three, pairWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The pair joint moment of the Euler product is positive**, so its logarithm is meaningful.
Prime by prime, from `RMF.integral_prod_localIntegrand_pos_of_bound` against the exponent bound
that is uniform in `λ₂`. -/
lemma IsSteinhausRMF.integral_prod_norm_pair_pos {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {σ₀ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (l₁ l₂ σ h₁ h₂ : ℝ) (y₀ y : ℕ) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hσ : σ₀ ≤ σ) :
    (0 : ℝ) < ∫ ω, ∏ a,
      ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖ ^ (2 * pairWeight l₁ l₂ a)
        ∂μ := by
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissa σ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissa_re]
    linarith
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y Finset.univ hre]
  refine Finset.prod_pos fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hnorm : ∀ a : Fin 3, ‖((p : ℂ)) ^ (-pairAbscissa σ h₁ h₂ a)‖ = (p : ℝ) ^ (-σ) :=
    fun a => by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, pairAbscissa_re]
  have hle : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hincr : ‖(p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 1) - (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 2)‖
      ≤ (p : ℝ) ^ (-σ) * (|h₁ - h₂| * Real.log p) := by
    have h := norm_natCast_cpow_neg_sub_le hpp.pos
      (s₁ := pairAbscissa σ h₁ h₂ 1) (s₂ := pairAbscissa σ h₁ h₂ 2) (σ := σ)
      (pairAbscissa_re σ h₁ h₂ 1) (pairAbscissa_re σ h₁ h₂ 2)
    rwa [pairAbscissa_im_one, pairAbscissa_im_two] at h
  refine integral_prod_localIntegrand_pos_of_bound
    (fun a _ => by rw [hnorm a]; exact lt_of_le_of_lt hle hθ) fun z hz =>
    abs_logExponent_pairWeight_le (θ := (p : ℝ) ^ (-σ))
      (d := |h₁ - h₂| * Real.log p) hz hl₁ hl₂ (lt_of_le_of_lt hle hθ)
      (le_of_eq (hnorm 0)) (le_of_eq (hnorm 1)) (le_of_eq (hnorm 2)) hincr

/-- **Hamdan's Lemma B.1, Chernoff form**, exponents free.  With `S = log ‖F‖`, `A = ∑_p p^{-2σ}`
and `B = |h₁-h₂| ∑_p p^{-2σ}\log p` over `p ∈ [y₀, y)`,
`P(S(σ) ≥ V₁, S(σ+ih₁) - S(σ+ih₂) ≥ V₂) ≤ exp((λ₁²/4)A + ((λ₁λ₂+λ₂²)/2)B + C - λ₁V₁ - λ₂V₂)`
for `0 ≤ λ₁ ≤ Λ`, `λ₂ ≥ 0` and `λ₂|h₁-h₂| ≤ Λ`.  `λ₁ = 2V₁/A` gives Hamdan's `-V₁²/j` at `σ = 1/2`,
and `λ₂ = √V₂/B` his `V₂^{3/2}` term. -/
theorem IsSteinhausRMF.exists_measure_le_exp_pair {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (l₁ l₂ σ h₁ h₂ V₁ V₂ : ℝ) (y₀ y : ℕ) (E : Set Ω),
        0 ≤ l₁ → 0 ≤ l₂ → σ₀ ≤ σ → l₁ ≤ Λ → l₂ * |h₁ - h₂| ≤ Λ → MeasurableSet E →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ 0) ω‖) →
        (∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ 1) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ 2) ω‖) →
          μ.real E ≤ Real.exp (l₁ ^ 2 / 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂|
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
            + C - (l₁ * V₁ + l₂ * V₂)) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsSteinhausRMF.exists_log_joint_moment_pair_le (Ω := Ω) (σ₀ := σ₀) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₁ l₂ σ h₁ h₂ V₁ V₂ y₀ y E hl₁ hl₂ hσ hl₁Λ hl₂Λ hE hE₁ hE₂
  haveI := hf.isProbabilityMeasure
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissa σ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissa_re]
    linarith
  have hq : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      |pairWeight l₁ l₂ a| ≤ l₁ / 2 + l₂ / 2 := fun a _ => abs_pairWeight_le hl₁ hl₂ a
  have hint := hf.integrable_prod_norm_rpow Finset.univ (pairWeight l₁ l₂)
    (pairAbscissa σ h₁ h₂) y₀ y hq (by linarith) hre
  have hIpos := hf.integral_prod_norm_pair_pos hσ₀ l₁ l₂ σ h₁ h₂ y₀ y hl₁ hl₂ hσ
  have hW : ∀ ω ∈ E, l₁ * V₁ + l₂ * V₂
      ≤ ∑ a, 2 * pairWeight l₁ l₂ a
        * Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖ := by
    intro ω hω
    rw [sum_two_mul_pairWeight_mul]
    have hA := mul_le_mul_of_nonneg_left (hE₁ ω hω) hl₁
    have hB := mul_le_mul_of_nonneg_left (hE₂ ω hω) hl₂
    linarith
  have hge : ∀ᵐ ω ∂(μ.restrict E), Real.exp (l₁ * V₁ + l₂ * V₂)
      ≤ ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) := by
    filter_upwards [ae_restrict_of_ae (hf.prod_norm_rpow_ae_eq Finset.univ
      (pairWeight l₁ l₂) (pairAbscissa σ h₁ h₂) y₀ y hre), ae_restrict_mem hE] with ω h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (hW ω h2)
  have h1 : μ.real E * Real.exp (l₁ * V₁ + l₂ * V₂)
      ≤ ∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a)) ∂μ := by
    have hc : (∫ _ω in E, Real.exp (l₁ * V₁ + l₂ * V₂) ∂μ)
        = μ.real E * Real.exp (l₁ * V₁ + l₂ * V₂) := by
      rw [setIntegral_const, smul_eq_mul]
    rw [← hc]
    exact integral_mono_ae (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hge
  have h2 : (∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a)) ∂μ)
      ≤ ∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a) ∂μ := by
    refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) _
  have h3 : (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) ∂μ)
      ≤ Real.exp (l₁ ^ 2 / 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
        + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂|
          * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) + C) := by
    have h := hbound f μ hf l₁ l₂ σ h₁ h₂ y₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
    have h4 := Real.exp_le_exp.2 h
    rwa [Real.exp_log hIpos] at h4
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  linarith

/-! ### The one-point tail, at a general abscissa

Hamdan's Lemma B.2 opens by splitting off `P(S_j(σ) > V - 2)` — his (A.3) — and its `q = 0`
summand is the same quantity.  Lemma B.2 needs the full sum `∑_{p<y}` at `σ = 1/2 - k/\log x`, and
at an arbitrary height.

That is the one-abscissa case of `RMF.IsSteinhausRMF.exists_measure_le_exp`: with a single
abscissa the spread `D` may be taken to be `0`, so the second prime sum drops out and only
`(∑_a q_a)² ∑_p p^{-2σ}` survives. -/

/-- **The one-point upper tail, exponent free.**

`P(E) ≤ exp(λ²/4 · ∑_{p<y}p^{-2σ} + C - λV)` on any event where `\log‖F_y(s)‖ ≥ V`, for every
`0 ≤ λ ≤ Λ`, at every abscissa of real part `σ ≥ σ₀ > 1/3` — the height is unconstrained. -/
theorem IsSteinhausRMF.exists_measure_ge_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (l σ V : ℝ) (s : ℂ) (y₀ y : ℕ) (E : Set Ω),
        0 ≤ l → l ≤ Λ → s.re = σ → σ₀ ≤ σ → MeasurableSet E →
        (∀ ω ∈ E, V ≤ Real.log ‖randomEulerProductIco f y₀ y s ω‖) →
          μ.real E ≤ Real.exp (l ^ 2 / 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            + C - l * V) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsSteinhausRMF.exists_measure_le_exp (Ω := Ω) ({0} : Finset ℕ)
      (Q := Λ / 2) (σ₀ := σ₀) (by linarith) hσ₀
  refine ⟨C, hC, ?_⟩
  intro f μ hf l σ V s y₀ y E hl hlΛ hs hσ hE hEV
  have hW : ∀ ω ∈ E, l * V ≤ ∑ a ∈ ({0} : Finset ℕ),
      2 * (l / 2) * Real.log ‖randomEulerProductIco f y₀ y s ω‖ := by
    intro ω hω
    rw [Finset.sum_singleton]
    nlinarith [hEV ω hω]
  have h := hbound f μ hf (fun _ => l / 2) (fun _ => s) σ 0 (l * V) y₀ y E
    (fun a _ => by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ l / 2)]; linarith)
    (fun _ _ => hs) hσ (fun _ _ _ _ => by simp) hE hW
  refine le_trans h (le_of_eq ?_)
  congr 1
  rw [Finset.sum_singleton, Finset.card_singleton]
  push_cast
  ring

/-- **The one-point Gaussian tail.**

`P(E) ≤ exp(C - V²/A)`, `A = ∑_{p<y}p^{-2σ}`, at the optimal `λ = 2V/A`.  At `σ = 1/2`,
`y = x_j` Mertens gives `A = j + O(1)`, which is Hamdan's `exp(-V²/j)`. -/
theorem IsSteinhausRMF.exists_measure_ge_le_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ V : ℝ) (s : ℂ) (y₀ y : ℕ) (E : Set Ω), 0 ≤ V → s.re = σ → σ₀ ≤ σ →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        2 * V / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) ≤ Λ →
        MeasurableSet E →
        (∀ ω ∈ E, V ≤ Real.log ‖randomEulerProductIco f y₀ y s ω‖) →
          μ.real E
            ≤ Real.exp (C - V ^ 2 / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsSteinhausRMF.exists_measure_ge_le (Ω := Ω) (σ₀ := σ₀) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf σ V s y₀ y E hV hs hσ hA hlΛ hE hEV
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  rw [← hAdef] at hA hlΛ ⊢
  have h := hbound f μ hf (2 * V / A) σ V s y₀ y E (by positivity) hlΛ hs hσ hE hEV
  rw [← hAdef] at h
  refine le_trans h (Real.exp_le_exp.2 (le_of_eq ?_))
  field_simp
  ring

end RMF
