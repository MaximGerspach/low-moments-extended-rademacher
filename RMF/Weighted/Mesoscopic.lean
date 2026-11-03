/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CentralWindow
import RMF.Weighted.Layered

/-!
# The mesoscopic range `1/log y < |t| ≤ 1`

`Z = Z_c + Z_m + Z_f`, and `RMF/Weighted/CentralWindow.lean` bounds `Z_c`.  This file is about
`Z_m`, which is covered by **`e`-adic blocks**

`T_j = e^j/log y`,  `j = 1, …, J = ⌈log log y⌉`,  `B_j = (T_{j-1}, T_j]`,

chosen `e`-adic so that the block index *is* the depth: `log(T_j·log y) = j`.

Two facts make each block self-similar.  On `B_j` the weight is `|σ+ih|^{-2} ≍ T_j^{-2}`; and
splitting the product at `z_j := exp(1/T_j) = y^{e^{-j}}` puts the *low* part `F_{z_j}` at the
scale where the block has length exactly one correlation length, `|B_j| ≍ 1/log z_j`, and leaves
the *high* part over the top `j` `e`-adic prime scales.  A block is therefore Harper's unit-window
problem with `log log y` replaced by the depth `j`.

## The split, without conditioning

There is no need to tilt by `|F_{z_j}(½+σ)|`, condition on the primes above `z_j`, or apply
conditional Jensen.  Apply `RMF.integral_rpow_le_of_mixed_le` with

`N = ‖F_{z_j}(½+σ)‖²·S`,  `S = ∫_{B_j}‖F_{(z_j,y]}(½+σ+ih)‖²dh`,  `W = ∫_{B_j}‖F_y(½+σ+ih)‖²dh`,

whose hypothesis `E[N^{q-1}W] ≤ κ·E[N^q]` unwinds by Fubini and independence into
`E[‖F_{z_j}(½+σ)‖^{2q-2}‖F_{z_j}(½+σ+ih)‖²] ≤ e^{143800}E‖F_{z_j}(½+σ)‖^{2q}`, a two-point bound
for the Euler product whose hypothesis `|h|·log z_j ≤ 2` holds because `|h| ≤ T_j = 1/log z_j`.
Then `E[N^q] = E‖F_{z_j}(½+σ)‖^{2q}·E[S^q]`, again by independence.  So the split costs one
application of the balanced Hölder inequality.

This file supplies the independence that both steps need, the block split itself
(`RMF.integral_rpow_setIntegral_normSq_split_le`), and the decomposition of `Z_m` into windows.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Disjoint ranges of primes are independent -/

/-- **The values on two disjoint sets of primes are independent.**

`ProbabilityTheory.iIndepFun.indepFun_finset` is stated for two disjoint `Finset`s of the index
type, here `Nat.Primes`; the two sets arrive as `Finset ℕ`, so they are carried across by their
images and the tuples reindexed with `MeasureTheory.IndepFun.comp`. -/
theorem IsIIDPrimeValues.indepFun_of_disjoint {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) {S T : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hT : ∀ p ∈ T, p.Prime) (hST : Disjoint S T) :
    IndepFun (fun ω (p : ↥S) => X (p : ℕ) ω) (fun ω (p : ↥T) => X (p : ℕ) ω) μ := by
  classical
  set e : ↥S → Nat.Primes := fun p => ⟨(p : ℕ), hS p p.2⟩ with he
  set f : ↥T → Nat.Primes := fun p => ⟨(p : ℕ), hT p p.2⟩ with hf
  set S' : Finset Nat.Primes := Finset.univ.image e with hS'
  set T' : Finset Nat.Primes := Finset.univ.image f with hT'
  have hdisj : Disjoint S' T' := by
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hp'
    have hab : (b : ℕ) = (a : ℕ) := congrArg Subtype.val hb
    exact Finset.disjoint_left.1 hST a.2 (by rw [← hab]; exact b.2)
  have hind := hX.iIndep.indepFun_finset S' T' hdisj fun p => hX.measurable (p : ℕ) p.2
  exact hind.comp
    (measurable_pi_lambda _ fun p =>
      measurable_pi_apply (⟨e p, Finset.mem_image_of_mem e (Finset.mem_univ p)⟩ : ↥S'))
    (measurable_pi_lambda _ fun p =>
      measurable_pi_apply (⟨f p, Finset.mem_image_of_mem f (Finset.mem_univ p)⟩ : ↥T'))

/-- **Expectations split across two disjoint sets of primes.**  A functional of the values on `S`
and a functional of the values on `T` are independent, so the expectation of their product
factors. -/
theorem IsIIDPrimeValues.integral_mul_split_of_disjoint {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) {S T : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hT : ∀ p ∈ T, p.Prime) (hST : Disjoint S T)
    {φ : (↥S → ℂ) → ℝ} {ψ : (↥T → ℂ) → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφm : AEStronglyMeasurable (fun ω => φ fun p => X (p : ℕ) ω) μ)
    (hψm : AEStronglyMeasurable (fun ω => ψ fun p => X (p : ℕ) ω) μ) :
    (∫ ω, (φ fun p => X (p : ℕ) ω) * (ψ fun p => X (p : ℕ) ω) ∂μ)
      = (∫ ω, φ fun p => X (p : ℕ) ω ∂μ) * ∫ ω, ψ fun p => X (p : ℕ) ω ∂μ :=
  ((hX.indepFun_of_disjoint hS hT hST).comp hφ hψ).integral_fun_mul_eq_mul_integral hφm hψm

/-- **Expectations split across `z`.**  A functional of the values below `z` and a functional of
the values in `[z, y)` are independent, so the expectation of their product factors.  This is the
interface both steps of the block split use.

The case `[0, z)`, `[z, y)` of `RMF.IsIIDPrimeValues.integral_mul_split_of_disjoint`. -/
theorem IsIIDPrimeValues.integral_mul_split {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (z y : ℕ)
    {φ : (↥(Nat.primesBelow z) → ℂ) → ℝ} {ψ : (↥(primesIco z y) → ℂ) → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφm : AEStronglyMeasurable (fun ω => φ fun p => X (p : ℕ) ω) μ)
    (hψm : AEStronglyMeasurable (fun ω => ψ fun p => X (p : ℕ) ω) μ) :
    (∫ ω, (φ fun p => X (p : ℕ) ω) * (ψ fun p => X (p : ℕ) ω) ∂μ)
      = (∫ ω, φ fun p => X (p : ℕ) ω ∂μ) * ∫ ω, ψ fun p => X (p : ℕ) ω ∂μ := by
  exact hX.integral_mul_split_of_disjoint (S := Nat.primesBelow z) (T := primesIco z y)
    (fun p hp => Nat.prime_of_mem_primesBelow hp) (fun p hp => prime_of_mem_primesIco hp)
    (by simpa only [primesIco_zero] using disjoint_primesIco 0 z y) hφ hψ hφm hψm

/-! ### The envelope of the high product

The mirror of `RMF.ae_forall_norm_randomEulerProduct_mem_Icc` for the block `(z, y]`.  As there,
one almost-sure event — `‖X p ω‖ ≤ 1` for the finitely many primes involved — covers **every**
`s` on the line `Re s = c` at once, which is what makes the bound usable inside the `h`-integral.
-/

/-- The lower envelope of the block product is positive: every factor is `1 - p^{-c} ≥ 1/4`.
The case `c ≥ 1/2` of `RMF.prod_one_sub_prime_rpow_primesIco_pos_of_pos`. -/
lemma prod_one_sub_prime_rpow_primesIco_pos {z y : ℕ} {c : ℝ} (hc : 1 / 2 ≤ c) :
    (0 : ℝ) < ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-c)) :=
  prod_one_sub_prime_rpow_primesIco_pos_of_pos (by linarith)

/-- **The two-sided envelope of the block product**, uniform along the line `Re s = c`.  The
case `c ≥ 1/2` of `RMF.ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos`. -/
lemma ae_forall_norm_randomEulerProductIco_mem_Icc {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {c : ℝ} (hc : 1 / 2 ≤ c) :
    ∀ᵐ ω ∂μ, ∀ s : ℂ, s.re = c →
      (∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-c)))
          ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y s ω‖
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y s ω‖
          ≤ ∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-c)) :=
  ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX z y (by linarith)

omit [MeasurableSpace Ω] in
/-- **The split of a block product at an interior cutoff**, in the norm-squared form:
`‖F_{[y₀,y)}‖² = ‖F_{[y₀,z)}‖²·‖F_{[z,y)}‖²`, which is `RMF.eulerProductIco_mul` read through
`‖·‖²`. -/
lemma normSq_randomEulerProductIco_split {X : ℕ → Ω → ℂ} {y₀ z y : ℕ} (hy₀z : y₀ ≤ z)
    (hzy : z ≤ y) (s : ℂ) (ω : Ω) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y s ω‖ ^ 2
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z s ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y s ω‖ ^ 2 := by
  have h : randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z s ω
        * randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y s ω
      = randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y s ω :=
    eulerProductIco_mul _ hy₀z hzy s
  rw [← h, norm_mul, mul_pow]

omit [MeasurableSpace Ω] in
/-- **The split of the full product into low and high**, in the norm-squared form the block
argument uses.  `RMF.randomEulerProduct_mul_randomEulerProductIco` read through `‖·‖²`.

The block `[0, y)` case of `RMF.normSq_randomEulerProductIco_split`. -/
lemma normSq_randomEulerProduct_split {X : ℕ → Ω → ℂ} {z y : ℕ} (hzy : z ≤ y) (s : ℂ) (ω : Ω) :
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2
      = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y s ω‖ ^ 2 := by
  simpa only [randomEulerProductIco_zero] using
    normSq_randomEulerProductIco_split (X := X) (Nat.zero_le z) hzy s ω

/-! ### The Euler polynomial as a function of the prime values

`RMF.IsIIDPrimeValues.integral_mul_split` wants each factor presented as a *measurable function
of the tuple of values*, so both products are read through `RMF.primePoly`: the low one at
`Nat.primesBelow z`, the high one at `RMF.primesIco z y`. -/

/-- The Euler polynomial over a finite set of primes, as a function of the values at them. -/
noncomputable def primePoly (S : Finset ℕ) (s : ℂ) (v : ↥S → ℂ) : ℂ :=
  ∏ p : ↥S, (1 + v p * ((p : ℕ) : ℂ) ^ (-s))

lemma continuous_primePoly (S : Finset ℕ) (s : ℂ) : Continuous (primePoly S s) :=
  continuous_finsetProd _ fun p _ => ((continuous_apply p).mul continuous_const).const_add 1

/-- **Joint continuity in the values and the height**, which is what makes the window integral
of the block product a measurable function of the values. -/
lemma continuous_primePoly_shiftLine {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (σ : ℝ) :
    Continuous fun w : (↥S → ℂ) × ℝ => primePoly S (shiftLine σ w.2) w.1 :=
  continuous_finsetProd _ fun p _ =>
    (((continuous_apply p).comp continuous_fst).mul
      ((continuous_cpow_neg_shiftLine (hS p p.2) σ).comp continuous_snd)).const_add 1

omit [MeasurableSpace Ω] in
lemma primePoly_primesBelow {X : ℕ → Ω → ℂ} (z : ℕ) (s : ℂ) (ω : Ω) :
    primePoly (Nat.primesBelow z) s (fun p => X (p : ℕ) ω)
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω := by
  rw [randomEulerProduct, eulerProduct_squarefreeExtension, primePoly]
  exact Finset.prod_coe_sort _ fun p => 1 + X p ω * ((p : ℕ) : ℂ) ^ (-s)

omit [MeasurableSpace Ω] in
lemma primePoly_primesIco {X : ℕ → Ω → ℂ} (z y : ℕ) (s : ℂ) (ω : Ω) :
    primePoly (primesIco z y) s (fun p => X (p : ℕ) ω)
      = randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y s ω := by
  rw [randomEulerProductIco_sqfree_eq, primePoly]
  exact Finset.prod_coe_sort _ fun p => 1 + X p ω * ((p : ℕ) : ℂ) ^ (-s)

/-- The window integral of the block product, as a function of the values at its primes. -/
noncomputable def primePolyWindow (S : Finset ℕ) (σ : ℝ) (I : Set ℝ) (v : ↥S → ℂ) : ℝ :=
  ∫ h in I, ‖primePoly S (shiftLine σ h) v‖ ^ 2

lemma measurable_primePolyWindow {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (σ : ℝ) (I : Set ℝ) :
    Measurable (primePolyWindow S σ I) :=
  (StronglyMeasurable.integral_prod_right' (ν := volume.restrict I)
    (((continuous_primePoly_shiftLine hS σ).norm.pow 2)).stronglyMeasurable).measurable

omit [MeasurableSpace Ω] in
lemma primePolyWindow_primesIco {X : ℕ → Ω → ℂ} (z y : ℕ) (σ : ℝ) (I : Set ℝ) (ω : Ω) :
    primePolyWindow (primesIco z y) σ I (fun p => X (p : ℕ) ω)
      = ∫ h in I, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2 := by
  simp only [primePolyWindow, primePoly_primesIco]

/-! ### The two independence steps -/

/-- The tuple of values at a finite set of primes is measurable. -/
lemma measurable_primeTuple {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Measurable fun ω => (fun p : ↥S => X (p : ℕ) ω) :=
  measurable_pi_lambda _ fun p => hX.measurable (p : ℕ) (hS (p : ℕ) p.2)

/-- **`E[‖F_{[y₀,z)}(½+σ)‖^{2q}·S^q] = E‖F_{[y₀,z)}(½+σ)‖^{2q}·E[S^q]`**, `S` the window integral
of the block product over `[z, y)`: the values at the primes of `[y₀, z)` and of `[z, y)` are
independent (`RMF.IsIIDPrimeValues.integral_mul_split_of_disjoint`). -/
lemma integral_rpow_normSq_mul_window_split_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ z y : ℕ) (σ : ℝ) (I : Set ℝ) {q : ℝ} (hq0 : 0 ≤ q) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ (2 * q)
          * (∫ h in I, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ h) ω‖ ^ 2) ^ q ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ∫ ω, (∫ h in I, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            z y (shiftLine σ h) ω‖ ^ 2) ^ q ∂μ := by
  have hφ : Measurable fun v : ↥(primesIco y₀ z) → ℂ =>
      ‖primePoly (primesIco y₀ z) (shiftLine σ 0) v‖ ^ (2 * q) :=
    ((continuous_primePoly _ _).norm.rpow_const fun _ => Or.inr (by positivity)).measurable
  have hψ : Measurable fun v : ↥(primesIco z y) → ℂ =>
      primePolyWindow (primesIco z y) σ I v ^ q :=
    (Real.continuous_rpow_const hq0).measurable.comp
      (measurable_primePolyWindow (fun p hp => (prime_of_mem_primesIco hp).pos) σ I)
  have h := hX.integral_mul_split_of_disjoint (fun p hp => prime_of_mem_primesIco hp)
    (fun p hp => prime_of_mem_primesIco hp) (disjoint_primesIco y₀ z y) hφ hψ
    (hφ.comp (measurable_primeTuple hX _ fun p hp =>
      prime_of_mem_primesIco hp)).aestronglyMeasurable
    (hψ.comp (measurable_primeTuple hX _ fun p hp =>
      prime_of_mem_primesIco hp)).aestronglyMeasurable
  simpa only [primePoly_primesIco, primePolyWindow_primesIco] using h

/-! ### The window integral of the block product -/

/-- Joint measurability of the block product in `(ω, h)`, through `RMF.primePoly`. -/
lemma measurable_uncurry_primePoly {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω}
    (hX : IsIIDPrimeValues X ν μ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (σ : ℝ) :
    Measurable fun w : Ω × ℝ => primePoly S (shiftLine σ w.2) fun p => X (p : ℕ) w.1 :=
  (continuous_primePoly_shiftLine (fun p hp => (hS p hp).pos) σ).measurable.comp
    (((measurable_primeTuple hX S hS).comp measurable_fst).prodMk measurable_snd)

/-- **The Tonelli slice for the block product** over `(z, y]`; the bound is the upper envelope,
which does not move along the line.  The case `σ ≥ 0` of
`RMF.integrable_uncurry_normSq_shiftLine_primesIco`. -/
lemma integrable_uncurry_normSq_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {I : Set ℝ}
    (hI : volume I ≠ ⊤) :
    Integrable (Function.uncurry fun (ω : Ω) (h : ℝ) =>
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2)
      (μ.prod (volume.restrict I)) :=
  integrable_uncurry_normSq_shiftLine_primesIco hX z y (by linarith) hI

/-- **The window integral of the block product is two-sided**, on any line `Re s = ½ + σ > 0`. -/
lemma ae_setIntegral_normSq_primesIco_mem_Icc_signed {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ a b : ℝ} (hσ : 0 < 1 / 2 + σ) (hab : a ≤ b) :
    ∀ᵐ ω ∂μ, (b - a) * (∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
          ≤ ∫ h in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ h) ω‖ ^ 2
        ∧ (∫ h in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ h) ω‖ ^ 2)
          ≤ (b - a) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
  haveI := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hslice := integrable_uncurry_normSq_shiftLine_primesIco hX z y (I := Set.Icc a b) hσ
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hconst : ∀ C : ℝ, (∫ _h in Set.Icc a b, C) = (b - a) * C := fun C => by
    rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul]
  filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX z y hσ,
    hslice.prod_right_ae] with ω hω hint
  constructor
  · rw [← hconst]
    refine integral_mono (by exact integrable_const _) hint fun h => ?_
    exact pow_le_pow_left₀ (prod_one_sub_prime_rpow_primesIco_pos_of_pos hσ).le
      (hω (shiftLine σ h) (re_shiftLine σ h)).1 2
  · rw [← hconst]
    refine integral_mono hint (by exact integrable_const _) fun h => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ h) (re_shiftLine σ h)).2 2

/-! ### Independence up to almost-everywhere equality -/

/-- `RMF.IsIIDPrimeValues.integral_mul_split_of_disjoint` when the two factors are only *almost
everywhere* functions of the values on `S` and on `T`. -/
lemma IsIIDPrimeValues.integral_mul_split_ae_of_disjoint {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) {S T : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hT : ∀ p ∈ T, p.Prime) (hST : Disjoint S T) {Φ Ψ : Ω → ℝ}
    {φ : (↥S → ℂ) → ℝ} {ψ : (↥T → ℂ) → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hΦ : Φ =ᵐ[μ] fun ω => φ fun p => X (p : ℕ) ω)
    (hΨ : Ψ =ᵐ[μ] fun ω => ψ fun p => X (p : ℕ) ω) :
    (∫ ω, Φ ω * Ψ ω ∂μ) = (∫ ω, Φ ω ∂μ) * ∫ ω, Ψ ω ∂μ := by
  have hmul : (fun ω => Φ ω * Ψ ω)
      =ᵐ[μ] fun ω => (φ fun p => X (p : ℕ) ω) * (ψ fun p => X (p : ℕ) ω) := by
    filter_upwards [hΦ, hΨ] with ω h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hmul, integral_congr_ae hΦ, integral_congr_ae hΨ]
  exact hX.integral_mul_split_of_disjoint hS hT hST hφ hψ
    (hφ.comp (measurable_primeTuple hX S hS)).aestronglyMeasurable
    (hψ.comp (measurable_primeTuple hX T hT)).aestronglyMeasurable

/-- **The second independence step for two consecutive blocks**, at one height `t₀`, on any line
`Re s = ½ + σ > 0`: the mixed expectation factors into its part on the block `[y₀, z)` below the
split and its part on the block `[z, y)` above it. -/
lemma integral_mixed_window_split_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ z y : ℕ) {σ a b q t₀ : ℝ} (hσ : 0 < 1 / 2 + σ)
    (hab : a < b) :
    (∫ ω, ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ t₀) ω‖ ^ 2)
          * ((∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t₀) ω‖ ^ 2) ∂μ)
      = (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ t₀) ω‖ ^ 2 ∂μ)
        * ∫ ω, (∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t₀) ω‖ ^ 2 ∂μ := by
  set VP : ℝ := (∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 with hVP
  set SM : ℝ := (b - a) * (∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 with hSM
  have hVPpos : (0 : ℝ) < VP := by
    rw [hVP]; exact pow_pos (prod_one_sub_prime_rpow_primesIco_pos_of_pos hσ) 2
  have hSMpos : (0 : ℝ) < SM := by
    rw [hSM]
    exact mul_pos (by linarith) (pow_pos (prod_one_sub_prime_rpow_primesIco_pos_of_pos hσ) 2)
  -- the truncated functions on the tuples
  have hcontmax : ∀ C : ℝ, 0 < C → Continuous fun x : ℝ => (max x C) ^ (q - 1) := by
    intro C hC
    exact (continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_of_lt_of_le hC (le_max_right x C)).ne'
  refine hX.integral_mul_split_ae_of_disjoint (fun p hp => prime_of_mem_primesIco hp)
    (fun p hp => prime_of_mem_primesIco hp) (disjoint_primesIco y₀ z y)
    (φ := fun v => (max (‖primePoly (primesIco y₀ z) (shiftLine σ 0) v‖ ^ 2) VP) ^ (q - 1)
      * ‖primePoly (primesIco y₀ z) (shiftLine σ t₀) v‖ ^ 2)
    (ψ := fun v => (max (primePolyWindow (primesIco z y) σ (Set.Icc a b) v) SM) ^ (q - 1)
      * ‖primePoly (primesIco z y) (shiftLine σ t₀) v‖ ^ 2)
    (((hcontmax VP hVPpos).comp ((continuous_primePoly _ _).norm.pow 2)).mul
      ((continuous_primePoly _ _).norm.pow 2)).measurable
    ((((hcontmax SM hSMpos).measurable).comp
        (measurable_primePolyWindow (fun p hp => (prime_of_mem_primesIco hp).pos) σ _)).mul
      ((continuous_primePoly _ _).norm.pow 2).measurable) ?_ ?_
  · filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ z hσ] with ω hω
    have h1 := (hω (shiftLine σ 0) (re_shiftLine σ 0)).1
    have h2 : VP ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ 0) ω‖ ^ 2 := by
      rw [hVP]
      exact pow_le_pow_left₀ (prod_one_sub_prime_rpow_primesIco_pos_of_pos hσ).le h1 2
    simp only [primePoly_primesIco, max_eq_left h2]
  · filter_upwards [ae_setIntegral_normSq_primesIco_mem_Icc_signed hX z y hσ hab.le] with ω hω
    rw [← hSM] at hω
    simp only [primePoly_primesIco, primePolyWindow_primesIco, max_eq_left hω.1]

/-! ### The Fubini assembly -/

/-- **The mixed bound for two consecutive blocks, to the left of `½`.**  For the product over
`[y₀, y)` split at `z`, at `σ ≥ -1/12` and with `p^{-2(½+σ)} ≤ K/p` on the low block: the
two-point bound is `RMF.integral_mixed_norm_randomEulerProductIco_le_exp`, at `e^{143800K}`. -/
lemma integral_mixed_split_primesIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y₀ z y : ℕ} (hz : 2 ≤ z) (hy₀z : y₀ ≤ z) (hzy : z ≤ y)
    {σ a b q K : ℝ} (hσ : -(1 / 12) ≤ σ) (hab : a < b) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hK : ∀ p ∈ primesIco y₀ z,
      (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) ≤ K * ((p : ℝ))⁻¹)
    (hK0 : 0 ≤ K)
    (hzt : ∀ t ∈ Set.Icc a b, |t| * Real.log z ≤ 2) :
    (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
          * (∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
                (shiftLine σ t) ω‖ ^ 2) ∂μ)
      ≤ Real.exp (143800 * K)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, (∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) := by
  haveI := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hc : (5 : ℝ) / 12 ≤ 1 / 2 + σ := by linarith
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hbase : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  have henvP := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ z hc0
  have hSbd := ae_setIntegral_normSq_primesIco_mem_Icc_signed hX z y hc0 hab.le
  have hVpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hVQpos : (0 : ℝ) < ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  -- the two slices
  have hsliceY := integrable_uncurry_normSq_shiftLine_primesIco hX y₀ y (I := Set.Icc a b) hc0
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsliceQ := integrable_uncurry_normSq_shiftLine_primesIco hX z y (I := Set.Icc a b) hc0
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- the truncation constants, and the truncated exponentials
  set VP : ℝ := (∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 with hVP
  set SM : ℝ := (b - a) * (∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 with hSM
  have hVPpos : (0 : ℝ) < VP := by rw [hVP]; exact pow_pos hVpos 2
  have hSMpos : (0 : ℝ) < SM := by
    rw [hSM]; exact mul_pos (by linarith) (pow_pos hVQpos 2)
  have hcontmax : ∀ C : ℝ, 0 < C → Continuous fun x : ℝ => (max x C) ^ (q - 1) := fun C hC =>
    (continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_of_lt_of_le hC (le_max_right x C)).ne'
  -- measurability of the two `ω`-factors
  have hSaesm : AEStronglyMeasurable (fun ω => ∫ t in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ t) ω‖ ^ 2) μ := hsliceQ.integral_prod_left.1
  have hmP : AEStronglyMeasurable (fun w : Ω × ℝ =>
      (max (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ 0) w.1‖ ^ 2) VP) ^ (q - 1)) (μ.prod (volume.restrict (Set.Icc a b))) :=
    (((hcontmax VP hVPpos).comp_aestronglyMeasurable
      ((measurable_norm_randomEulerProductIco_sqfree hX y₀ z
        (shiftLine σ 0)).pow_const 2).aestronglyMeasurable)).comp_fst
  have hmS : AEStronglyMeasurable (fun w : Ω × ℝ =>
      (max (∫ t in Set.Icc a b,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) w.1‖ ^ 2) SM) ^ (q - 1))
      (μ.prod (volume.restrict (Set.Icc a b))) :=
    ((hcontmax SM hSMpos).comp_aestronglyMeasurable hSaesm).comp_fst
  have hmPt : AEStronglyMeasurable (fun w : Ω × ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ w.2) w.1‖ ^ 2) (μ.prod (volume.restrict (Set.Icc a b))) := by
    have h2 := (measurable_uncurry_primePoly hX (primesIco y₀ z)
      (fun p hp => prime_of_mem_primesIco hp) σ).norm.pow_const 2
    simp only [primePoly_primesIco] at h2
    exact h2.aestronglyMeasurable
  have hmQt : AEStronglyMeasurable (fun w : Ω × ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ w.2) w.1‖ ^ 2) (μ.prod (volume.restrict (Set.Icc a b))) := by
    have h2 := (measurable_uncurry_primePoly hX (primesIco z y)
      (fun p hp => prime_of_mem_primesIco hp) σ).norm.pow_const 2
    simp only [primePoly_primesIco] at h2
    exact h2.aestronglyMeasurable
  -- the truncations are invisible almost surely, on the product
  have haeP : ∀ᵐ w ∂(μ.prod (volume.restrict (Set.Icc a b))),
      (max (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
          (shiftLine σ 0) w.1‖ ^ 2) VP)
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
          (shiftLine σ 0) w.1‖ ^ 2 := by
    have h0 : ∀ᵐ ω ∂μ, (max (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2) VP)
          = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2 := by
      filter_upwards [henvP] with ω hω
      have hle : VP ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
          (shiftLine σ 0) ω‖ ^ 2 := by
        rw [hVP]
        exact pow_le_pow_left₀ hVpos.le (hω (shiftLine σ 0) (re_shiftLine σ 0)).1 2
      exact max_eq_left hle
    exact Measure.quasiMeasurePreserving_fst.ae h0
  have haeS : ∀ᵐ w ∂(μ.prod (volume.restrict (Set.Icc a b))),
      (max (∫ t in Set.Icc a b,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) w.1‖ ^ 2) SM)
        = ∫ t in Set.Icc a b,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) w.1‖ ^ 2 := by
    have h0 : ∀ᵐ ω ∂μ, (max (∫ t in Set.Icc a b,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) ω‖ ^ 2) SM)
          = ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2 := by
      filter_upwards [hSbd] with ω hω
      exact max_eq_left hω.1
    exact Measure.quasiMeasurePreserving_fst.ae h0
  -- the two product integrands are integrable: measurable, and bounded by the envelopes
  have hGm : AEStronglyMeasurable (fun w : Ω × ℝ =>
      ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) w.1‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ w.2) w.1‖ ^ 2)
        * ((∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) w.1‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ w.2) w.1‖ ^ 2)) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine ((hmP.mul hmPt).mul (hmS.mul hmQt)).congr ?_
    filter_upwards [haeP, haeS] with w h1 h2
    simp only [Pi.mul_apply]
    rw [h1, h2]
  have hHm : AEStronglyMeasurable (fun w : Ω × ℝ =>
      (∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) w.1‖ ^ 2) ^ (q - 1)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ w.2) w.1‖ ^ 2) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (hmS.mul hmQt).congr ?_
    filter_upwards [haeS] with w h2
    simp only [Pi.mul_apply]
    rw [h2]
  -- the a.e. bounds on the product space
  have haeb : ∀ᵐ w ∂(μ.prod (volume.restrict (Set.Icc a b))),
      ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) w.1‖ ^ 2) ^ (q - 1)
          ≤ VP ^ (q - 1))
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ w.2) w.1‖ ^ 2
          ≤ (∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
        ∧ ((∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) w.1‖ ^ 2) ^ (q - 1) ≤ SM ^ (q - 1))
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ w.2) w.1‖ ^ 2
          ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    have h0 : ∀ᵐ ω ∂μ, ∀ t : ℝ,
        ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1) ≤ VP ^ (q - 1))
          ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ t) ω‖ ^ 2
            ≤ (∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
          ∧ ((∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ (q - 1) ≤ SM ^ (q - 1))
          ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2
            ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
      filter_upwards [henvP, hSbd,
        ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX z y hc0] with ω hω hS hωQ
      intro t
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hle : VP ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2 := by
          rw [hVP]
          exact pow_le_pow_left₀ hVpos.le (hω (shiftLine σ 0) (re_shiftLine σ 0)).1 2
        exact Real.rpow_le_rpow_of_nonpos hVPpos hle (by linarith)
      · exact pow_le_pow_left₀ (norm_nonneg _) (hω (shiftLine σ t) (re_shiftLine σ t)).2 2
      · exact Real.rpow_le_rpow_of_nonpos hSMpos hS.1 (by linarith)
      · exact pow_le_pow_left₀ (norm_nonneg _) (hωQ (shiftLine σ t) (re_shiftLine σ t)).2 2
    exact (Measure.quasiMeasurePreserving_fst.ae h0).mono fun w hw => hw w.2
  have hGint : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ t) ω‖ ^ 2)
        * ((∫ u in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) ω‖ ^ 2)) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (memLp_top_of_bound hGm
      ((VP ^ (q - 1) * (∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
        * (SM ^ (q - 1) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2))
      ?_).integrable le_top
    filter_upwards [haeb] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul hw.1 hw.2.1 (sq_nonneg _) (Real.rpow_nonneg hVPpos.le _))
      (mul_le_mul hw.2.2.1 hw.2.2.2 (sq_nonneg _) (Real.rpow_nonneg hSMpos.le _))
      (by positivity) (by positivity)
  have hHint : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      (∫ u in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ t) ω‖ ^ 2) (μ.prod (volume.restrict (Set.Icc a b))) := by
    refine (memLp_top_of_bound hHm
      (SM ^ (q - 1) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ?_).integrable
      le_top
    filter_upwards [haeb] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hw.2.2.1 hw.2.2.2 (sq_nonneg _) (Real.rpow_nonneg hSMpos.le _)
  -- (A) the pointwise identity
  have hA : ∀ᵐ ω ∂μ,
      (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
              (shiftLine σ t) ω‖ ^ 2)
      = ∫ t in Set.Icc a b,
          ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b,
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) := by
    filter_upwards [hSbd] with ω hS
    rw [Real.mul_rpow (sq_nonneg _) (le_trans hSMpos.le hS.1), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [normSq_randomEulerProductIco_split hy₀z hzy]
    ring
  -- (D) the two-point bound at each height
  have hlow : ∀ t ∈ Set.Icc a b,
      (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ t) ω‖ ^ 2 ∂μ)
        ≤ Real.exp (143800 * K) * ∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
    intro t ht
    have hthr : |(shiftLine σ t).im| * Real.log z ≤ 2 := by
      rw [im_shiftLine]; exact hzt t ht
    have hmix := integral_mixed_norm_randomEulerProductIco_le_exp hX (y₀ := y₀) hz hc
      (re_shiftLine σ t) hthr hK hK0 hq0 hq1
    rw [← hbase] at hmix
    have hone : ∀ v : ℂ, ‖v‖ ^ (2 * (1 : ℝ)) = ‖v‖ ^ 2 := fun v => by
      rw [norm_rpow_two_mul v 1, Real.rpow_one]
    simp only [hone, norm_rpow_two_mul] at hmix
    rwa [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (norm_rpow_two_mul (randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
        (shiftLine σ 0) ω) q).symm)] at hmix
  -- assemble
  calc (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
      = ∫ ω, (∫ t in Set.Icc a b,
          ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b,
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2)) ∂μ := integral_congr_ae hA
    _ = ∫ t in Set.Icc a b, ∫ ω,
          ((‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
                (shiftLine σ t) ω‖ ^ 2)
            * ((∫ u in Set.Icc a b,
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                    (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ∂μ := integral_integral_swap hGint
    _ ≤ ∫ _t in Set.Icc a b, (Real.exp (143800 * K) * ∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, (∫ u in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ _t) ω‖ ^ 2 ∂μ := by
        refine setIntegral_mono_on hGint.integral_prod_right
          (hHint.integral_prod_right.const_mul _) measurableSet_Icc fun t ht => ?_
        rw [integral_mixed_window_split_primesIco hX y₀ z y hc0 hab]
        exact mul_le_mul_of_nonneg_right (hlow t ht)
          (integral_nonneg fun ω => by positivity)
    _ = (Real.exp (143800 * K) * ∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ t in Set.Icc a b, ∫ ω, (∫ u in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ u) ω‖ ^ 2) ^ (q - 1)
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2 ∂μ := integral_const_mul _ _
    _ = Real.exp (143800 * K)
          * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ∫ ω, (∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) := by
        rw [mul_assoc]
        congr 2
        rw [← integral_integral_swap hHint]
        refine integral_congr_ae ?_
        filter_upwards [hSbd] with ω hS
        have hSpos : (0 : ℝ) < ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2 := lt_of_lt_of_le hSMpos hS.1
        rw [integral_const_mul]
        nth_rewrite 2 [← Real.rpow_one (∫ t in Set.Icc a b,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ t) ω‖ ^ 2)]
        rw [← Real.rpow_add hSpos]
        norm_num

/-- **The block split for two consecutive blocks, to the left of `½`.**  For `0 ≤ q ≤ 1`,
`2 ≤ z`, `y₀ ≤ z ≤ y`, `σ ≥ -1/12`, `a < b`, `|t|·log z ≤ 2` on `[a,b]` and `p^{-2(½+σ)} ≤ K/p`
on `[y₀, z)`, `E[(∫_{[a,b]}‖F_{[y₀,y)}(½+σ+it)‖²dt)^q]`
`  ≤ e^{143800Kq}·E‖F_{[y₀,z)}(½+σ)‖^{2q}·E[(∫_{[a,b]}‖F_{[z,y)}(½+σ+it)‖²dt)^q]`, by the
balanced Hölder from `RMF.integral_mixed_split_primesIco_le`.  At the shift `½ - c` of a band of
Proposition B (`RMF/Weighted/PropositionB.lean`), `2c·log z ≤ 1` gives `K = e`
(`RMF.rpow_neg_shift_le_exp_one_mul_inv`). -/
theorem integral_rpow_setIntegral_normSq_split_primesIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y₀ z y : ℕ} (hz : 2 ≤ z) (hy₀z : y₀ ≤ z) (hzy : z ≤ y)
    {σ a b q K : ℝ} (hσ : -(1 / 12) ≤ σ) (hab : a < b) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hK : ∀ p ∈ primesIco y₀ z,
      (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) ≤ K * ((p : ℝ))⁻¹)
    (hK0 : 0 ≤ K)
    (hzt : ∀ t ∈ Set.Icc a b, |t| * Real.log z ≤ 2) :
    (∫ ω, (∫ t in Set.Icc a b,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ Real.exp (143800 * K) ^ q
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, (∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) := by
  haveI := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have henvP := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ z hc0
  have hSbd := ae_setIntegral_normSq_primesIco_mem_Icc_signed hX z y hc0 hab.le
  have hWbd := ae_setIntegral_normSq_primesIco_mem_Icc_signed hX y₀ y hc0 hab.le
  have hEPpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hEQpos : (0 : ℝ) < ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hEYpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have hFPpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) :=
    Finset.prod_pos fun p _ => by positivity
  have hFQpos : (0 : ℝ) < ∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) :=
    Finset.prod_pos fun p _ => by positivity
  have hFYpos : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) :=
    Finset.prod_pos fun p _ => by positivity
  set EP : ℝ := ∏ p ∈ primesIco y₀ z, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hEP
  set FP : ℝ := ∏ p ∈ primesIco y₀ z, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hFP
  set EQ : ℝ := ∏ p ∈ primesIco z y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hEQ
  set FQ : ℝ := ∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hFQ
  set EY : ℝ := ∏ p ∈ primesIco y₀ y, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) with hEY
  set FY : ℝ := ∏ p ∈ primesIco y₀ y, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hFY
  set NL : ℝ := EP ^ 2 * ((b - a) * EQ ^ 2) with hNL
  set NU : ℝ := FP ^ 2 * ((b - a) * FQ ^ 2) with hNU
  have hNLpos : (0 : ℝ) < NL := by
    rw [hNL]; exact mul_pos (pow_pos hEPpos 2) (mul_pos (by linarith) (pow_pos hEQpos 2))
  have hNUpos : (0 : ℝ) < NU := by
    rw [hNU]; exact mul_pos (pow_pos hFPpos 2) (mul_pos (by linarith) (pow_pos hFQpos 2))
  -- the combined envelope
  have hbnd : ∀ᵐ ω ∂μ,
      ((NL ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2)
          ∧ (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
              (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ≤ NU)
        ∧ ((b - a) * EY ^ 2 ≤ ∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
                (shiftLine σ t) ω‖ ^ 2)
          ∧ (∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
                (shiftLine σ t) ω‖ ^ 2) ≤ (b - a) * FY ^ 2 := by
    filter_upwards [henvP, hSbd, hWbd] with ω hω hS hW
    refine ⟨⟨?_, ?_⟩, hW.1, hW.2⟩
    · rw [hNL]
      exact mul_le_mul (pow_le_pow_left₀ hEPpos.le (hω (shiftLine σ 0) (re_shiftLine σ 0)).1 2)
        hS.1 (by positivity) (sq_nonneg _)
    · rw [hNU]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
        (hω (shiftLine σ 0) (re_shiftLine σ 0)).2 2) hS.2 (le_trans (by positivity) hS.1)
        (sq_nonneg _)
  -- measurability of the three observables
  have hP0m : AEStronglyMeasurable (fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2) μ :=
    ((measurable_norm_randomEulerProductIco_sqfree hX y₀ z
      (shiftLine σ 0)).pow_const 2).aestronglyMeasurable
  have hSm : AEStronglyMeasurable (fun ω => ∫ t in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ t) ω‖ ^ 2) μ :=
    (integrable_uncurry_normSq_shiftLine_primesIco hX z y (I := Set.Icc a b) hc0
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integral_prod_left.1
  have hWm : AEStronglyMeasurable (fun ω => ∫ t in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2) μ :=
    (integrable_uncurry_normSq_shiftLine_primesIco hX y₀ y (I := Set.Icc a b) hc0
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integral_prod_left.1
  have hcontmax : Continuous fun x : ℝ => (max x NL) ^ (q - 1) :=
    (continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_of_lt_of_le hNLpos (le_max_right x NL)).ne'
  have hWnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2 := fun ω => integral_nonneg fun t => by positivity
  have hNnn : ∀ᵐ ω ∂μ, (0 : ℝ) < ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2 :=
    hbnd.mono fun ω h => lt_of_lt_of_le hNLpos h.1.1
  -- the three integrabilities
  have hNi : Integrable (fun ω => (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable (hP0m.mul hSm))
      (NU ^ q) ?_).integrable le_top
    filter_upwards [hbnd] with ω h
    simp only [Pi.mul_apply]
    have h0 : (0 : ℝ) ≤ _ := le_of_lt (lt_of_lt_of_le hNLpos h.1.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    exact Real.rpow_le_rpow h0 h.1.2 hq0
  have hi : Integrable (fun ω => (∫ t in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0).comp_aestronglyMeasurable hWm)
      (((b - a) * FY ^ 2) ^ q) ?_).integrable le_top
    filter_upwards [hbnd] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hWnn ω) _)]
    exact Real.rpow_le_rpow (hWnn ω) h.2.2 hq0
  have hABi : Integrable (fun ω => (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
      * ∫ t in Set.Icc a b,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2) μ := by
    have hm : AEStronglyMeasurable (fun ω => (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)) μ := by
      refine (hcontmax.comp_aestronglyMeasurable (hP0m.mul hSm)).congr ?_
      filter_upwards [hbnd] with ω h
      simp only [Pi.mul_apply]
      rw [max_eq_left h.1.1]
    refine (memLp_top_of_bound (hm.mul hWm) (NL ^ (q - 1) * ((b - a) * FY ^ 2)) ?_).integrable
      le_top
    filter_upwards [hbnd] with ω h
    simp only [Pi.mul_apply]
    have h0 : (0 : ℝ) < _ := lt_of_lt_of_le hNLpos h.1.1
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg h0.le _) (hWnn ω))]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hNLpos h.1.1 (by linarith)) h.2.2
      (hWnn ω) (Real.rpow_nonneg hNLpos.le _)
  -- the two positivities
  have hα : (0 : ℝ) < ∫ ω, (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
    refine lt_of_lt_of_le (Real.rpow_pos_of_pos hNLpos q) ?_
    calc NL ^ q = ∫ _ω, NL ^ q ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hNi
          (hbnd.mono fun ω h => Real.rpow_le_rpow hNLpos.le h.1.1 hq0)
  have hβ : (0 : ℝ) < ∫ ω, (‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
        * ∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
      * (∫ t in Set.Icc a b,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2) ∂μ := by
    have hEY2 : (0 : ℝ) < (b - a) * EY ^ 2 := mul_pos (by linarith) (pow_pos hEYpos 2)
    refine lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hNUpos (q - 1)) hEY2) ?_
    calc NU ^ (q - 1) * ((b - a) * EY ^ 2) = ∫ _ω, NU ^ (q - 1) * ((b - a) * EY ^ 2) ∂μ := by simp
      _ ≤ _ := by
          refine integral_mono_ae (integrable_const _) hABi ?_
          filter_upwards [hbnd] with ω h
          exact mul_le_mul
            (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hNLpos h.1.1) h.1.2 (by linarith))
            h.2.1 hEY2.le (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hNLpos h.1.1)) _)
  -- `E[N^q]` factors
  have hfac : (∫ ω, (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ z
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ∫ ω, (∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
    rw [← integral_rpow_normSq_mul_window_split_primesIco hX y₀ z y σ (Set.Icc a b) hq0]
    refine integral_congr_ae ?_
    filter_upwards [hSbd] with ω hS
    have hS0 : (0 : ℝ) ≤ _ := le_trans (mul_nonneg (by linarith) (sq_nonneg EQ)) hS.1
    rw [Real.mul_rpow (sq_nonneg _) hS0, ← norm_rpow_two_mul]
  -- the balanced Hölder
  have hbd : (∫ ω, (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
          * ∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ (q - 1)
        * (∫ t in Set.Icc a b,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
              (shiftLine σ t) ω‖ ^ 2) ∂μ)
      ≤ Real.exp (143800 * K) * ∫ ω, (‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) y₀ z (shiftLine σ 0) ω‖ ^ 2
            * ∫ t in Set.Icc a b,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                  (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
    rw [hfac]
    exact integral_mixed_split_primesIco_le hX hz hy₀z hzy hσ hab hq0 hq1 hK hK0 hzt
  have hkey := integral_rpow_le_of_mixed_le hq0 hq1 hNnn (.of_forall hWnn) hNi hABi hi hα hβ
    (Real.exp_pos _).le hbd
  rwa [hfac] at hkey

/-- **The block split.**  For `2 ≤ z ≤ y`, `σ ≥ 0`, `a < b`, `|t|·log z ≤ 2` on `[a,b]` and
`0 ≤ q ≤ 1`,
`E[(∫_{[a,b]}‖F_y(½+σ+it)‖²dt)^q] ≤ e^{143800q}·E‖F_z(½+σ)‖^{2q}·E[(∫_{[a,b]}‖F_{(z,y]}‖²dt)^q]`
by the balanced Hölder `RMF.integral_rpow_le_of_mixed_le` at `N = ‖F_z(½+σ)‖²·S`.  On the block
`(T_{j-1}, T_j]` at `z = exp(1/T_j)` the hypothesis on `t` reads `|t| ≤ 2T_j`.  The case `y₀ = 0`,
`K = 1` of `RMF.integral_rpow_setIntegral_normSq_split_primesIco_le`. -/
theorem integral_rpow_setIntegral_normSq_split_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {σ a b q : ℝ} (hσ : 0 ≤ σ) (hab : a < b) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hzt : ∀ t ∈ Set.Icc a b, |t| * Real.log z ≤ 2) :
    (∫ ω, (∫ t in Set.Icc a b,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ Real.exp 143800 ^ q
        * ((∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z
              (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, (∫ t in Set.Icc a b,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ) := by
  have h := integral_rpow_setIntegral_normSq_split_primesIco_le hX (y₀ := 0) hz (Nat.zero_le z)
    hzy (σ := σ) (a := a) (b := b) (q := q) (K := 1) (by linarith) hab hq0 hq1
    (fun p hp => prime_rpow_neg_mul_self_le_inv (prime_of_mem_primesIco hp) (by linarith))
    zero_le_one hzt
  simpa only [randomEulerProductIco_zero, mul_one] using h

/-! ### The decomposition into windows

`Z_m` is an integral over `{1/log y < |t| ≤ 1}` against the weight `|σ+it|^{-2}`, and the block
argument wants it as a sum over windows.  The covering step is cheapest as a **pointwise weight
domination**: if the windows cover the domain and `ρ ≤ c i` on the `i`-th, then

`1_S(t)·ρ(t) ≤ ∑_i c i·1_{(a i, b i]}(t)`

for every `t`, because every term on the right is nonnegative — **so no disjointness is needed**,
and the covering never has to be seen by the measure theory.  The rest is `integral_mono` on
one interval containing everything, and `MeasureTheory.integral_finsetSum`. -/

/-- **Window domination, pathwise.**  With `g ≥ 0` integrable on `[A,B]`, `ρ` a nonnegative
bounded measurable weight, and windows `(a i, b i] ⊆ [A,B]` covering `S ⊆ [A,B]` with `ρ ≤ c i`
on the `i`-th,

`∫_S ρ·g ≤ ∑_i (c i)·∫_{[a i, b i]} g`. -/
theorem setIntegral_weight_le_sum_windows {ι : Type*} {g ρ : ℝ → ℝ} {A B Bρ : ℝ} (I : Finset ι)
    (a b c : ι → ℝ) {S : Set ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgint : IntegrableOn g (Set.Icc A B))
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρm : Measurable ρ) (hρb : ∀ t, ρ t ≤ Bρ)
    (hS : MeasurableSet S) (hSAB : S ⊆ Set.Icc A B)
    (hIAB : ∀ i ∈ I, Set.Ioc (a i) (b i) ⊆ Set.Icc A B)
    (hcov : ∀ t ∈ S, ∃ i ∈ I, t ∈ Set.Ioc (a i) (b i))
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hρc : ∀ i ∈ I, ∀ t ∈ Set.Ioc (a i) (b i), ρ t ≤ c i) :
    (∫ t in S, ρ t * g t) ≤ ∑ i ∈ I, c i * ∫ t in Set.Icc (a i) (b i), g t := by
  classical
  -- the pointwise domination
  have hpt : ∀ t, Set.indicator S (fun t => ρ t * g t) t
      ≤ ∑ i ∈ I, c i * Set.indicator (Set.Ioc (a i) (b i)) g t := by
    intro t
    have hnn : ∀ i ∈ I, (0 : ℝ) ≤ c i * Set.indicator (Set.Ioc (a i) (b i)) g t :=
      fun i hi => mul_nonneg (hc i hi) (Set.indicator_nonneg (fun _ _ => hg0 _) t)
    by_cases hts : t ∈ S
    · rw [Set.indicator_of_mem hts]
      obtain ⟨i₀, hi₀I, hi₀⟩ := hcov t hts
      have h1 : c i₀ * g t ≤ ∑ i ∈ I, c i * Set.indicator (Set.Ioc (a i) (b i)) g t := by
        have h := Finset.single_le_sum
          (f := fun i => c i * Set.indicator (Set.Ioc (a i) (b i)) g t) hnn hi₀I
        rwa [Set.indicator_of_mem hi₀] at h
      exact le_trans (mul_le_mul_of_nonneg_right (hρc i₀ hi₀I t hi₀) (hg0 t)) h1
    · rw [Set.indicator_of_notMem hts]
      exact Finset.sum_nonneg hnn
  -- the two integrabilities on `[A,B]`
  have hρg : IntegrableOn (fun t => ρ t * g t) (Set.Icc A B) := by
    refine Integrable.bdd_mul (c := Bρ) hgint hρm.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact hρb t
  have hint1 : IntegrableOn (Set.indicator S (fun t => ρ t * g t)) (Set.Icc A B) :=
    hρg.indicator hS
  have hint2 : IntegrableOn
      (fun t => ∑ i ∈ I, c i * Set.indicator (Set.Ioc (a i) (b i)) g t) (Set.Icc A B) :=
    integrable_finsetSum _ fun i _ => (hgint.indicator measurableSet_Ioc).const_mul _
  -- and the two rewrites of the endpoints
  have hlhs : (∫ t in S, ρ t * g t)
      = ∫ t in Set.Icc A B, Set.indicator S (fun t => ρ t * g t) t := by
    rw [setIntegral_indicator hS, Set.inter_eq_right.2 hSAB]
  have hrhs : ∀ i ∈ I, (∫ t in Set.Icc A B, Set.indicator (Set.Ioc (a i) (b i)) g t)
      = ∫ t in Set.Icc (a i) (b i), g t := by
    intro i hi
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.2 (hIAB i hi),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hlhs]
  calc (∫ t in Set.Icc A B, Set.indicator S (fun t => ρ t * g t) t)
      ≤ ∫ t in Set.Icc A B, ∑ i ∈ I, c i * Set.indicator (Set.Ioc (a i) (b i)) g t :=
        integral_mono hint1 hint2 hpt
    _ = ∑ i ∈ I, c i * ∫ t in Set.Icc A B, Set.indicator (Set.Ioc (a i) (b i)) g t := by
        rw [integral_finsetSum _ fun i _ => (hgint.indicator measurableSet_Ioc).const_mul _]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i ∈ I, c i * ∫ t in Set.Icc (a i) (b i), g t :=
        Finset.sum_congr rfl fun i hi => by rw [hrhs i hi]

/-- **The window decomposition for a block product, in expectation**, on any line
`Re s = ½ + σ > 0`, for the product over `[y₀, y)`: `RMF.setIntegral_weight_le_sum_windows` on
every path, then subadditivity of `u ↦ u^q`.  The weight `ρ` is arbitrary, so it need not be tied
to the numerator's shift. -/
theorem integral_rpow_setIntegral_weight_le_sum_windows_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y : ℕ) {σ q : ℝ} (hσ : 0 < 1 / 2 + σ) (hq0 : 0 < q)
    (hq1 : q ≤ 1)
    {ι : Type*} (I : Finset ι) (a b c : ι → ℝ) {A B Bρ : ℝ} {ρ : ℝ → ℝ} {S : Set ℝ}
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρm : Measurable ρ) (hρb : ∀ t, ρ t ≤ Bρ)
    (hS : MeasurableSet S) (hSAB : S ⊆ Set.Icc A B)
    (hIAB : ∀ i ∈ I, Set.Ioc (a i) (b i) ⊆ Set.Icc A B)
    (hcov : ∀ t ∈ S, ∃ i ∈ I, t ∈ Set.Ioc (a i) (b i))
    (hc : ∀ i, 0 ≤ c i) (hab : ∀ i ∈ I, a i ≤ b i)
    (hρc : ∀ i ∈ I, ∀ t ∈ Set.Ioc (a i) (b i), ρ t ≤ c i) :
    (∫ ω, (∫ t in S, ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ ∑ i ∈ I, (c i) ^ q * ∫ ω, (∫ t in Set.Icc (a i) (b i),
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hSnn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in S,
      ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2 :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (by positivity)
  have hYnn : ∀ (i : ι) (ω : Ω), (0 : ℝ) ≤ ∫ t in Set.Icc (a i) (b i),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2 := fun i ω => integral_nonneg fun t => by positivity
  -- each window moment is integrable: measurable by the slice, bounded by the envelope
  have hYint : ∀ i ∈ I, Integrable (fun ω => (∫ t in Set.Icc (a i) (b i),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ := by
    intro i hi
    have hm : Integrable (fun ω => ∫ t in Set.Icc (a i) (b i),
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2) μ :=
      (integrable_uncurry_normSq_shiftLine_primesIco hX y₀ y (I := Set.Icc (a i) (b i)) hσ
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integral_prod_left
    refine (memLp_top_of_bound
      ((Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable hm.1)
      (((b i - a i) * (∏ p ∈ primesIco y₀ y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ^ q)
      ?_).integrable le_top
    filter_upwards [ae_setIntegral_normSq_primesIco_mem_Icc_signed hX y₀ y hσ (hab i hi)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hYnn i ω) _)]
    exact Real.rpow_le_rpow (hYnn i ω) hω.2 hq0.le
  have hRint : Integrable (fun ω => ∑ i ∈ I, (c i) ^ q * (∫ t in Set.Icc (a i) (b i),
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (shiftLine σ t) ω‖ ^ 2) ^ q) μ :=
    integrable_finsetSum _ fun i hi => (hYint i hi).const_mul _
  -- pathwise: the window domination, then subadditivity of `u ↦ u^q`
  have hstep : ∀ᵐ ω ∂μ, (∫ t in S,
        ρ t * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (shiftLine σ t) ω‖ ^ 2) ^ q
      ≤ ∑ i ∈ I, (c i) ^ q * (∫ t in Set.Icc (a i) (b i),
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (shiftLine σ t) ω‖ ^ 2) ^ q := by
    filter_upwards [(integrable_uncurry_normSq_shiftLine_primesIco hX y₀ y (I := Set.Icc A B) hσ
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).prod_right_ae] with ω hint0
    have hint : IntegrableOn (fun t => ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) y₀ y (shiftLine σ t) ω‖ ^ 2)
        (Set.Icc A B) := hint0
    have hA := setIntegral_weight_le_sum_windows I a b c (fun t => by positivity) hint
      hρ0 hρm hρb hS hSAB hIAB hcov (fun i _ => hc i) hρc
    refine le_trans (Real.rpow_le_rpow (hSnn ω) hA hq0.le) ?_
    refine le_trans (rpow_sum_le_sum_rpow I
      (fun i => mul_nonneg (hc i) (hYnn i ω)) hq0 hq1) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => Real.mul_rpow (hc i) (hYnn i ω)
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hSnn ω) q) hRint hstep) ?_
  rw [integral_finsetSum _ fun i hi => (hYint i hi).const_mul _]
  exact le_of_eq (Finset.sum_congr rfl fun i _ => integral_const_mul _ _)

end RMF
