/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedSecondMoment.Ranges
import RMF.EulerProduct.TwoPointExplicit
import RMF.NumberTheory.CosinePrimeSumExplicit

/-!
# The second moment's range constants, named

The constants that the two `pairIco` factors of the second moment are built from, named; Harper's
(5.1) is named in `RMF/EulerProduct/TwoPointExplicit.lean`.

* `RMF.primeIocTailConst` — the tilted prime tail, `RMF.exists_sum_prime_Ioc_rpow_tail_le`;
* `RMF.mertensIcoInvSubConst` — Mertens' second theorem over a range, at
  `RMF.primesBelowInvLogLogConst`;
* `RMF.cosRpowLowConst` — the (5.1) exponent below `e^{1/|t|}`;
* `RMF.pairIcoConst`, `RMF.pairIcoConstAt` — the two-point block moments themselves.

**No prime number theorem enters any of these.**  Mertens' second theorem and the geometric tail
are all they use.  The one place where the second moment's constants reach the prime number
theorem is `RMF.exists_integral_normSq_high_le`, through
`RMF.exists_abs_cos_prime_sum_sub_log_min_le` and `RS_prime.pnt`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The tilted prime tail's constant**, `RMF.exists_sum_prime_Ioc_rpow_tail_le`'s witness
written out: the dyadic count `\log 2 + 20/\log 2` times the geometric sum `e^{-1}/(1-e^{-1})`. -/
noncomputable def primeIocTailConst : ℝ :=
  (Real.log 2 + 20 / Real.log 2) * (Real.exp (-1 : ℝ) * (1 - Real.exp (-1 : ℝ))⁻¹)

/-- **Mertens' second theorem over a range**, at twice
`RMF.primesBelowInvLogLogConst` — one endpoint each. -/
noncomputable def mertensIcoInvSubConst : ℝ := 2 * primesBelowInvLogLogConst

/-- `RMF.mertensIcoInvSubConst` is positive. -/
lemma mertensIcoInvSubConst_pos : 0 < mertensIcoInvSubConst := by
  have h := (exists_abs_sum_primesBelow_inv_sub_log_log_le_explicit).1
  rw [mertensIcoInvSubConst]
  positivity

/-- **`RMF.exists_abs_sum_primesIco_inv_sub_le` with its witness named.** -/
theorem abs_sum_primesIco_inv_sub_le :
    ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      |∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), ((p : ℝ))⁻¹
        - (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ)))|
        ≤ mertensIcoInvSubConst := by
  obtain ⟨hC, h⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le_explicit
  rw [mertensIcoInvSubConst]
  set C : ℝ := primesBelowInvLogLogConst with hCdef
  refine fun N₁ N₂ hN₁ hN12 => ?_
  have hN₂ : 2 ≤ N₂ := le_trans hN₁ hN12
  have hsub : Nat.primesBelow (N₁ + 1) ⊆ Nat.primesBelow (N₂ + 1) := primesBelow_mono (by omega)
  have hsum : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1), ((p : ℝ))⁻¹)
      = (∑ p ∈ Nat.primesBelow (N₂ + 1), ((p : ℝ))⁻¹)
        - ∑ p ∈ Nat.primesBelow (N₁ + 1), ((p : ℝ))⁻¹ :=
    eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  have h₁ := h N₁ hN₁
  have h₂ := h N₂ hN₂
  rw [hsum, abs_le]
  rw [abs_le] at h₁ h₂
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **The (5.1) exponent below `e^{1/|t|}`**, at `2 + 2\cos ≤ 4` and Mertens. -/
noncomputable def cosRpowLowConst : ℝ := 4 * mertensIcoInvSubConst

/-- `RMF.cosRpowLowConst` is positive. -/
lemma cosRpowLowConst_pos : 0 < cosRpowLowConst := by
  have h := mertensIcoInvSubConst_pos
  rw [cosRpowLowConst]
  positivity

/-- **`RMF.exists_sum_two_add_two_cos_rpow_low_le` with its witness named.** -/
theorem sum_two_add_two_cos_rpow_low_le :
    ∀ (t σ : ℝ), 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + cosRpowLowConst := by
  have hmert := abs_sum_primesIco_inv_sub_le
  rw [cosRpowLowConst]
  set C : ℝ := mertensIcoInvSubConst with hCdef
  refine fun t σ hσ N₁ N₂ hN₁ hN12 => ?_
  have hterm : ∀ p ∈ primesIco (N₁ + 1) (N₂ + 1),
      (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ) ≤ 4 * ((p : ℝ))⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have hrpow : (p : ℝ) ^ (-1 - 2 * σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hcos : (2 : ℝ) + 2 * Real.cos (t * Real.log p) ≤ 4 := by
      linarith [Real.cos_le_one (t * Real.log p)]
    calc (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)
        ≤ 4 * (p : ℝ) ^ (-1 : ℝ) :=
          mul_le_mul hcos hrpow (by positivity) (by norm_num)
      _ = 4 * ((p : ℝ))⁻¹ := by rw [Real.rpow_neg_one]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have h := hmert N₁ N₂ hN₁ hN12
  rw [abs_le] at h
  linarith [hsum, h.2]

/-- **The two-point block moment below `e^{1/|t|}`**: the exponent of the (5.1) exponent and
its error, at the shortest range `x = 400` (`RMF.twoPointTailConst`). -/
noncomputable def pairIcoConst : ℝ := Real.exp (cosRpowLowConst + twoPointTailConst)

/-- **The two-point block moment with the error charged at a floor `y`**: the exponent of the
(5.1) exponent and `RMF.twoPointTailConstAt y`.  `RMF.pairIcoConst` is the case `y = 400`. -/
noncomputable def pairIcoConstAt (y : ℝ) : ℝ :=
  Real.exp (cosRpowLowConst + twoPointTailConstAt y)

/-- `RMF.pairIcoConstAt` at `400` is `RMF.pairIcoConst`. -/
lemma pairIcoConstAt_four_hundred : pairIcoConstAt 400 = pairIcoConst := rfl
/-- `RMF.pairIcoConstAt` is positive. -/
lemma pairIcoConstAt_pos (y : ℝ) : 0 < pairIcoConstAt y := Real.exp_pos _

/-- `RMF.pairIcoConstAt y` is at least `1` for `y ≥ 400`. -/
lemma one_le_pairIcoConstAt {y : ℝ} (hy : 400 ≤ y) : 1 ≤ pairIcoConstAt y :=
  Real.one_le_exp (by linarith [cosRpowLowConst_pos, twoPointTailConstAt_pos hy])

/-- **`RMF.exists_integral_normSq_pairIco_le` with its witness named, from a floor `y`.**  The
error is charged at `y` rather than at the shortest admissible range `400`, so the constant
`RMF.pairIcoConstAt y` carries `RMF.twoPointTailConstAt y` instead of `RMF.twoPointTailConst`. -/
theorem integral_normSq_pairIco_le_at (y : ℝ) (hy : 400 ≤ y) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ t : ℝ) (N₁ N₂ : ℕ), 0 ≤ σ → y ≤ (N₁ : ℝ) → N₁ ≤ N₂ →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          ≤ pairIcoConstAt y * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  have h51 := abs_log_integral_two_point_le (Ω := Ω)
  have hsum := sum_two_add_two_cos_rpow_low_le
  rw [pairIcoConstAt]
  set C : ℝ := twoPointMomentConst with hCdef
  set D : ℝ := cosRpowLowConst with hDdef
  set T : ℝ := twoPointTailConstAt y with hTdef
  refine fun f μ hf σ t N₁ N₂ hσ hyN₁ hN12 => ?_
  have hN₁ : (400 : ℝ) ≤ (N₁ : ℝ) := le_trans hy hyN₁
  have hexp4 : ∀ r : ℝ, 0 < r → Real.exp (4 * Real.log r) = r ^ 4 := by
    intro r hr
    rw [show (4 : ℝ) * Real.log r = Real.log r + Real.log r + Real.log r + Real.log r by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr]
    ring
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hN₂R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  have hlogN₂ : (1 : ℝ) ≤ Real.log (N₂ : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hN₂R)
  have hre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hs₁ : (0 : ℝ) < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hs₂ : (0 : ℝ) < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by linarith
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by positivity
    linarith
  have h := h51 f μ hf σ t ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) (by exact_mod_cast hN₁) hN₂R hσ'
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ T :=
    twoPointMomentConst_div_le_tailAt hy hyN₁
  have hps := hsum t σ hσ N₁ N₂ (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ))) hN12
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
        ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ 4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + T) := by
    linarith [h.2, hps, herr]
  have hEpos := hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂
  have hratio : (0 : ℝ) < Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ) := by
    apply div_pos <;> linarith
  have hconv : Real.exp (4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ)))
      + (D + T)) = Real.exp (D + T) * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
    rw [← Real.log_div (by linarith) (by linarith), Real.exp_add, hexp4 _ hratio]
    ring
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + T)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + T) * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := hconv

/-- `RMF.pairIcoConst` is at least `1`: the exponential of a positive constant. -/
lemma one_le_pairIcoConst : 1 ≤ pairIcoConst :=
  Real.one_le_exp (by linarith [cosRpowLowConst_pos, twoPointTailConst_pos])

/-- **The two-point moment of the Euler product, from a floor `y ≥ 400`**: the Euler product is
split at `y + 1`, so the primes below the floor are bounded pointwise by `RMF.eulerBound (y+1)`
and the rest in mean from `y`, charging the (5.1) error at `y`. -/
theorem integral_normSq_pair_below_le_at (y : ℕ) (hy : 400 ≤ y) :
    ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (σ t u : ℝ) (z : ℕ), 0 ≤ σ → (y : ℝ) ≤ (z : ℝ) →
        (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (z + 1)
                (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (z + 1)
                (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ (1 + eulerBound (y + 1) ^ 4) * pairIcoConstAt (y : ℝ) / Real.log (y : ℝ) ^ 4
              * Real.log (z : ℝ) ^ 4 := by
  have hyR : (400 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlow := integral_normSq_pairIco_le_at (Ω := Ω) (y : ℝ) hyR
  have hK₁ : 0 < pairIcoConstAt (y : ℝ) := pairIcoConstAt_pos _
  set K₁ : ℝ := pairIcoConstAt (y : ℝ) with hK₁def
  have hlog400 : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  intro X μ hX σ t u z hσ hz
  haveI := hX.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  have hσ' : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hs₁ : (0 : ℝ) < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hσ'
  have hs₂ : (0 : ℝ) < ((((1 / 2 + σ : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I)).re := by
    simpa using hσ'
  have hh₁ : (1 : ℝ) / 2 ≤ (((1 / 2 + σ : ℝ) : ℂ)).re := by
    simpa using (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + σ)
  have hh₂ : (1 : ℝ) / 2 ≤ ((((1 / 2 + σ : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I)).re := by
    simpa using (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + σ)
  have hzN : y ≤ z := by exact_mod_cast hz
  simp only [← randomEulerProductIco_zero]
  rw [integral_normSq_ico_pair_shift hX 0 (z + 1) hσ' t u, shiftLine_zero_height, shiftLine,
    hf.integral_normSq_mul_normSq_Ico_split (Nat.zero_le (y + 1))
      (by omega : y + 1 ≤ z + 1) hs₁ hs₂]
  have hbot : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 (y + 1)
            ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 (y + 1)
            (((1 / 2 + σ : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ 1 + eulerBound (y + 1) ^ 4 := by
    have hae : ∀ᵐ ω ∂μ,
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 (y + 1)
              ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 (y + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I) ω‖ ^ 2
          ≤ 1 + eulerBound (y + 1) ^ 4 := by
      filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw (y + 1)] with ω hω
      rw [randomEulerProductIco_zero, randomEulerProductIco_zero]
      have h1 := norm_randomEulerProduct_le hω hh₁
      have h2 := norm_randomEulerProduct_le hω hh₂
      have hE : (0 : ℝ) ≤ eulerBound (y + 1) := eulerBound_nonneg (y + 1)
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2,
        pow_nonneg (norm_nonneg (randomEulerProduct
          (fun ω => compMultExtension fun p => X p ω) (y + 1) ((1 / 2 + σ : ℝ) : ℂ) ω)) 2,
        pow_nonneg hE 2, sq_nonneg (eulerBound (y + 1) ^ 2)]
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
      (integrable_const _) hae) ?_
    simp
  have hmid := hlow (fun ω => compMultExtension fun p => X p ω) μ hf σ (u - t) y z hσ
    le_rfl hzN
  have hmid0 := (hf.integral_normSq_mul_normSq_Ico_pos (y + 1) (z + 1) hs₁ hs₂).le
  calc (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 (y + 1)
              ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 (y + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (y + 1) (z + 1)
              ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (y + 1) (z + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I) ω‖ ^ 2 ∂μ
      ≤ (1 + eulerBound (y + 1) ^ 4)
          * (K₁ * (Real.log (z : ℝ) / Real.log ((y : ℕ) : ℝ)) ^ 4) :=
        mul_le_mul hbot hmid hmid0 (by positivity)
    _ = (1 + eulerBound (y + 1) ^ 4) * K₁ / Real.log (y : ℝ) ^ 4 * Real.log (z : ℝ) ^ 4 := by
        rw [div_pow]
        field_simp

/-- `RMF.eulerBound` is monotone: every factor is at least `1`. -/
lemma eulerBound_mono {M N : ℕ} (h : M ≤ N) : eulerBound M ≤ eulerBound N := by
  unfold eulerBound
  refine Finset.prod_le_prod_of_subset_of_one_le (Nat.primesBelow_mono h)
    (fun p hp => (inv_pos.2 (one_sub_inv_sqrt_pos (Nat.prime_of_mem_primesBelow hp))).le)
    (fun p hp _ => ?_)
  have hpos := one_sub_inv_sqrt_pos (Nat.prime_of_mem_primesBelow hp)
  rw [one_le_inv₀ hpos]
  have : 0 ≤ (Real.sqrt p)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  linarith

end RMF
