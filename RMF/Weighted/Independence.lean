/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Layered

/-!
# The independence half of the layered identity

In each product `F_{y}(½)·T_{y,z}(x)` of the layered identity **the two factors are
independent** — `F_y` depends only on the values at the primes `p ≤ y`, `T_{y,z}` only on those at
`p > y`, every index of the tail being `y`-rough.

The upper bound for fixed `½ < q < 1` uses it in exactly one form, the multiplicativity of the
`2q`-th moment:

`∫ ‖F·T‖^r = (∫ ‖F‖^r)·(∫ ‖T‖^r)`,   equivalently `‖F·T‖_r = ‖F‖_r·‖T‖_r`.

## What `Reduction/Suppliers.lean` supplies

The two σ-algebras `RMF.smoothAlgebra X y` and `RMF.roughAlgebra X y`, their independence
(`RMF.indep_smoothAlgebra_roughAlgebra`), and the two measurability transfers
`RMF.measurable_smoothAlgebra_squarefreeExtension` and
`RMF.measurable_roughAlgebra_squarefreeExtension`.  What is added here is only

* that `F_y(s)` is `𝓕_y`-measurable — the Euler product over `primesBelow (y+1)` is a product of
  local factors `1 + X p · p^{-s}`, one per prime `p ≤ y`;
* that `T_{y,z}(x)` is `𝓖_y`-measurable — every index of the tail is `y`-rough;
* that `B_y(x)` is `𝓖_y`-measurable, for the same reason.  The fixed-`q` bound does not need it,
  its top scale `⌊x⌋₊` making `B = 1`; the inequality with a free top scale
  (`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`) does;
* and the passage from independent σ-algebras to a product of integrals, which is
  `ProbabilityTheory.indep_of_indep_of_le_left`/`_right` followed by
  `ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral`.

No integrability hypothesis appears: the Mathlib lemma carries none, both sides being `0` when
the product fails to be integrable.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The two factors, and which σ-algebra each lives on -/

omit [MeasurableSpace Ω] in
/-- **`F_y(s)` is `𝓕_y`-measurable.**  Its local factor at `p` is `1 + X p · p^{-s}`
(`RMF.localFactor_squarefreeExtension`), and the product runs over the primes `p ≤ y`. -/
lemma measurable_smoothAlgebra_randomEulerProduct {X : ℕ → Ω → ℂ} (y : ℕ) (s : ℂ) :
    Measurable[smoothAlgebra X y]
      (randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s) := by
  change Measurable[smoothAlgebra X y] fun ω =>
    ∏ p ∈ Nat.primesBelow (y + 1),
      localFactor (fun n => squarefreeExtension (fun p => X p ω) n) p s
  refine Finset.measurable_prod _ fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hpy : p ≤ y := Nat.lt_succ_iff.1 (Nat.lt_of_mem_primesBelow hp)
  have hle : MeasurableSpace.comap (X p) inferInstance ≤ smoothAlgebra X y :=
    le_iSup₂_of_le p ⟨hpp, hpy⟩ le_rfl
  have hXp : Measurable[smoothAlgebra X y] (X p) :=
    Measurable.mono (Measurable.of_comap_le le_rfl) hle le_rfl
  simp only [localFactor_squarefreeExtension _ hpp]
  exact (hXp.mul_const _).const_add _

omit [MeasurableSpace Ω] in
/-- **`T_{y,z}(x)` is `𝓖_y`-measurable.**  Every index of the tail is `y`-rough, so
`RMF.measurable_roughAlgebra_squarefreeExtension` applies term by term. -/
lemma measurable_roughAlgebra_blockTruncationTail {X : ℕ → Ω → ℂ} (y z : ℕ) (x : ℝ) :
    Measurable[roughAlgebra X y]
      (blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x) := by
  refine Finset.measurable_sum _ fun n hn => ?_
  exact (measurable_roughAlgebra_squarefreeExtension
    (Finset.mem_filter.1 hn).2.2.1).div_const _

/-! ### The product of moments -/

/-- **Independent σ-algebras give a product of moments.**  For `V` measurable for `𝓕_y` and `W`
for `𝓖_y`, `∫ ‖V·W‖^r = (∫ ‖V‖^r)·(∫ ‖W‖^r)`.

Stated for a bare pair rather than for `F` and `T` so that the two measurability facts are the
only inputs; `r` is unconstrained. -/
theorem integral_rpow_norm_mul_eq_mul_of_measurable {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (y : ℕ) {V W : Ω → ℂ} (r : ℝ)
    (hV : Measurable[smoothAlgebra X y] V) (hW : Measurable[roughAlgebra X y] W) :
    (∫ ω, ‖V ω * W ω‖ ^ r ∂μ)
      = (∫ ω, ‖V ω‖ ^ r ∂μ) * ∫ ω, ‖W ω‖ ^ r ∂μ := by
  have hVW : ProbabilityTheory.IndepFun V W μ :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left
        (indep_smoothAlgebra_roughAlgebra hX y) hV.comap_le) hW.comap_le
  have hVm : Measurable V := hV.mono (smoothAlgebra_le hX y) le_rfl
  have hWm : Measurable W := hW.mono (roughAlgebra_le hX y) le_rfl
  have hrp : Measurable fun t : ℂ => ‖t‖ ^ r := by fun_prop
  have hcomp : ProbabilityTheory.IndepFun (fun ω => ‖V ω‖ ^ r) (fun ω => ‖W ω‖ ^ r) μ :=
    hVW.comp hrp hrp
  calc (∫ ω, ‖V ω * W ω‖ ^ r ∂μ) = ∫ ω, ‖V ω‖ ^ r * ‖W ω‖ ^ r ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    _ = (∫ ω, ‖V ω‖ ^ r ∂μ) * ∫ ω, ‖W ω‖ ^ r ∂μ := by
        exact hcomp.integral_fun_mul_eq_mul_integral (hrp.comp hVm).aestronglyMeasurable
          (hrp.comp hWm).aestronglyMeasurable

/-- **The independence in the layered identity, in the form the fixed-`q` bound uses it.**

`E‖F_y(s)·T_{y,z}(x)‖^r = E‖F_y(s)‖^r · E‖T_{y,z}(x)‖^r`, i.e. `‖F·T‖_r = ‖F‖_r·‖T‖_r` for every
`r`.  At `r = 2q` this is the step that turns each layer of the layered identity into a product of
two moments, the Euler product's and the block tail's. -/
theorem integral_rpow_norm_randomEulerProduct_mul_blockTruncationTail {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (y z : ℕ) (s : ℂ) (x r : ℝ) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s ω
          * blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ r ∂μ)
      = (∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s ω‖ ^ r ∂μ)
        * ∫ ω, ‖blockTruncationTail
            (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ r ∂μ :=
  integral_rpow_norm_mul_eq_mul_of_measurable hX y r
    (measurable_smoothAlgebra_randomEulerProduct y s)
    (measurable_roughAlgebra_blockTruncationTail y z x)

omit [MeasurableSpace Ω] in
/-- **`B_y(x)` is `𝓖_y`-measurable.**  Every index of the rough sum is `y`-rough, so
`RMF.measurable_roughAlgebra_squarefreeExtension` applies term by term, exactly as for the tail. -/
lemma measurable_roughAlgebra_roughWeightedRademacherSum {X : ℕ → Ω → ℂ} (y : ℕ) (x : ℝ) :
    Measurable[roughAlgebra X y]
      (roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x) := by
  refine Finset.measurable_sum _ fun n hn => ?_
  exact (measurable_roughAlgebra_squarefreeExtension (Finset.mem_filter.1 hn).2).div_const _

/-- **The top layer splits too.**  `E‖F_y(s)·B_y(x)‖^r = E‖F_y(s)‖^r · E‖B_y(x)‖^r`.

The fixed-`q` bound does not need it: at its top scale `y = ⌊x⌋₊` the rough sum is `1`
(`RMF.roughWeightedRademacherSum_floor_eq_one`).  With the top scale free, as in
`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`, it is a genuine factor. -/
theorem integral_rpow_norm_randomEulerProduct_mul_roughWeightedRademacherSum {X : ℕ → Ω → ℂ}
    {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (y : ℕ) (s : ℂ) (x r : ℝ) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s ω
          * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω‖
            ^ r ∂μ)
      = (∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s ω‖ ^ r ∂μ)
        * ∫ ω, ‖roughWeightedRademacherSum
            (fun ω => squarefreeExtension fun p => X p ω) y x ω‖ ^ r ∂μ :=
  integral_rpow_norm_mul_eq_mul_of_measurable hX y r
    (measurable_smoothAlgebra_randomEulerProduct y s)
    (measurable_roughAlgebra_roughWeightedRademacherSum y x)

end RMF
