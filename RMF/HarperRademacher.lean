/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Harper
import RMF.Reduction.RademacherHarperMoment
import RMF.Reduction.RademacherUpper

/-!
# Harper's Theorem 2: the Rademacher random multiplicative function

For the Rademacher random multiplicative function `f` — independent fair signs at the primes,
`f(n) = ∏_{p ∣ n} f(p)` on the squarefree integers and `0` elsewhere (`RMF.IsRademacherRMF`) —
uniformly for `q ∈ [0,1]` and `x ≥ 3`,

`E|S_x|^{2q} ≍ (1 + (1-q)√(log log x))^{-q}`,   `S_x = x^{-1/2} ∑_{n ≤ x} f(n)`,

with constants independent of the probability space (`RMF.harper_low_moments_rademacher`).
The completely multiplicative extension `X^e` of the paper is a different function.

The assembly is the Steinhaus one of `RMF/Harper.lean`.  The only change is the second moment,
`E‖S_x‖² = Q(⌊x⌋)/x` with `Q` the squarefree count, which is at least `1/48` for `x ≥ 3`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

universe u

/-! ### The second moment -/

/-- **The second moment of the normalised Rademacher sum**: `E‖S_x‖² = Q(⌊x⌋)/x`, with `Q` the
number of squarefree integers. -/
lemma IsRademacherRMF.integral_rpow_two_normalisedSum {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) {x : ℝ} (hx : 0 < x) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) ∂μ = (squarefreeCount ⌊x⌋₊ : ℝ) / x := by
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have hpt : ∀ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) = ‖partialSum f ⌊x⌋₊ ω‖ ^ 2 / x := by
    intro ω
    rw [rpow_two_eq_sq, normalisedSum, randomSum_eq_partialSum, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hsx.le, div_pow, Real.sq_sqrt hx.le]
  simp_rw [hpt]
  rw [integral_div, hf.second_moment, squarefreeCount]

/-- **`E‖S_x‖² ≥ 1/48` for every `x ≥ 3`.**  For `x ≥ 144`, `Q(⌊x⌋) ≥ ⌊x⌋/8`; below `144`,
`Q(⌊x⌋) ≥ 3` gives `3/x > 1/48`, and that range sets the constant. -/
lemma IsRademacherRMF.integral_rpow_two_normalisedSum_ge {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) {x : ℝ}
    (hx : 3 ≤ x) : (1 : ℝ) / 48 ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 : ℝ) ∂μ := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [hf.integral_rpow_two_normalisedSum hx0, le_div_iff₀ hx0]
  have hfloor : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  rcases le_or_gt (144 : ℝ) x with hbig | hsmall
  · have hfl : 144 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hbig)
    have h1 : ((⌊x⌋₊ : ℝ)) / 8 ≤ squarefreeCount ⌊x⌋₊ := eighth_le_squarefreeCount hfl
    linarith
  · have hfl : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have h1 : (3 : ℝ) ≤ (squarefreeCount ⌊x⌋₊ : ℝ) := by
      exact_mod_cast three_le_squarefreeCount hfl
    linarith

/-! ### Harper's Theorem 2 -/

/-- `‖S_x‖^r` is integrable for every `r ≥ 0`: it is bounded and `μ` is a probability measure. -/
lemma integrable_rpow_normalisedSum_rademacher {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => ‖normalisedSum f x ω‖ ^ r) μ := by
  haveI := hf.isProbabilityMeasure
  have hmeas : Measurable fun ω => normalisedSum f x ω := hf.measurable_normalisedSum x
  have hm : AEStronglyMeasurable (fun ω => ‖normalisedSum f x ω‖ ^ r) μ := by fun_prop
  refine (memLp_top_of_bound hm (((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ r) ?_).integrable le_top
  filter_upwards [hf.ae_norm_normalisedSum_le x] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hω hr

/-- **The full-range lower constant for the Rademacher function**: `RMF.harperFullConstOf` at
`sm = 1/48`, the second moment of `RMF.IsRademacherRMF.integral_rpow_two_normalisedSum_ge`.  The
upper constant `C₁` stays a parameter — unlike the Steinhaus `20`, it is not a numeral. -/
noncomputable def harperFullConstRademacher (C₁ c₁ x₀ : ℝ) : ℝ :=
  harperFullConstOf (1 / 48) C₁ c₁ x₀

lemma harperFullConstRademacher_pos {C₁ c₁ x₀ : ℝ} (hc₁ : 0 < c₁) :
    0 < harperFullConstRademacher C₁ c₁ x₀ :=
  harperFullConstOf_pos (by norm_num) hc₁

/-- **Harper's lower bound for the Rademacher function on `0 ≤ q ≤ 1` and `x ≥ 3`, with the
constant a formula**: `RMF.le_integral_rpow_normalisedSum_full_of_law` at `sm = 1/48`.  Only the
second moment differs from the Steinhaus instance; the assembly itself is shared. -/
theorem le_integral_rpow_normalisedSum_full_rademacher_of_lower {C₁ c₁ x₀ : ℝ}
    (hC₁ : 0 < C₁) (hc₁ : 0 < c₁)
    (HA : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q < 1 →
        c₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
    (HU : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
        (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
          ≤ C₁ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
        harperFullConstRademacher C₁ c₁ x₀
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  rw [harperFullConstRademacher]
  exact le_integral_rpow_normalisedSum_full_of_law (fun f μ => IsRademacherRMF f μ)
    (by norm_num) hC₁ hc₁
    (fun _ _ hf x => hf.ae_norm_normalisedSum_le x)
    (fun _ _ hf x hx => by
      haveI := hf.isProbabilityMeasure
      exact hf.integral_rpow_two_normalisedSum_ge hx)
    (fun _ _ hf x _ hr => integrable_rpow_normalisedSum_rademacher hf x hr) HA HU

/-- **Harper's lower bound for the Rademacher function on `0 ≤ q ≤ 1` and `x ≥ 3`, on one
probability space**: the law-generic assembly `RMF.le_integral_rpow_normalisedSum_full_of_law`
with the second moment's constant `1/48`.  The `c` produced is
`RMF.harperFullConstRademacher C₁ c₁ x₀`, not an opaque witness. -/
theorem exists_le_integral_rpow_normalisedSum_full_rademacher (Ω : Type*)
    [MeasurableSpace Ω] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
            ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ := by
  obtain ⟨c₁, hc₁, x₀, HA⟩ := exists_le_integral_rpow_normalisedSum_rademacher Ω
  obtain ⟨C₁, hC₁, HU⟩ := harper_upper_ge_three_rademacher (Ω := Ω)
  exact ⟨harperFullConstRademacher C₁ c₁ x₀, harperFullConstRademacher_pos hc₁,
    le_integral_rpow_normalisedSum_full_rademacher_of_lower hC₁ hc₁ HA HU⟩

/-- **Harper's Theorem 2.**  For the Rademacher random multiplicative function, uniformly for
`q ∈ [0,1]` and `x ≥ 3`,

`E|S_x|^{2q} ≍ (1 + (1-q)√(log log x))^{-q}`,

with constants independent of the probability space.  On the coordinate model the two bounds are
`RMF.exists_le_integral_rpow_normalisedSum_full_rademacher` and
`RMF.harper_upper_ge_three_rademacher`;
`RMF.IsIIDPrimeValues.integral_rpow_normalisedSum_squarefreeExtension_eq` carries them to every
space. -/
theorem harper_low_moments_rademacher :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω),
        IsRademacherRMF f μ →
        ∀ x q : ℝ, 3 ≤ x → 0 ≤ q → q ≤ 1 →
          c * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
              ≤ ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ ∧
            (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
              ≤ C * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  have hcoord : IsRademacherRMF (fun v : Nat.Primes → ℂ => squarefreeExtension (primeExtend v))
      (Measure.infinitePi fun _ : Nat.Primes => rademacherLaw) :=
    IsRademacherPrimeValues.isRademacherRMF (isIIDPrimeValues_primeExtend rademacherLaw)
  obtain ⟨c, hc, HL⟩ := exists_le_integral_rpow_normalisedSum_full_rademacher (Nat.Primes → ℂ)
  obtain ⟨C, hC, HU⟩ := harper_upper_ge_three_rademacher (Ω := Nat.Primes → ℂ)
  refine ⟨c, C, hc, hC, fun Ω _ f μ hf x q hx hq0 hq1 => ?_⟩
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  rw [IsIIDPrimeValues.integral_rpow_normalisedSum_squarefreeExtension_eq hX]
  exact ⟨HL _ _ hcoord x q hx hq0 hq1, HU _ _ hcoord x q hx hq0 hq1⟩

end RMF
