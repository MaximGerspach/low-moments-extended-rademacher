/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosFirstMoment
import RMF.Probability.MaximalBarrier

/-!
# The `q`-th moment of the chaos

The interpolation of Soundararajan and Zaman, as in Hamdan's proof of his Proposition 1.2
(Hamdan, arXiv:2604.05563): from `P(h ∉ G_A) ≪ e^{-2A}` (his Lemma 2.3) and
`E[Z²(A)] ≪ A/√t` (his Proposition 2.1) to

`E[(Z²)^q] ≪ (1 + (1-q)√t)^{-q}`, uniformly in `q ∈ [0, 1]`,

for the chaos `Z²` of the Steinhaus random multiplicative function at the abscissa `1/2 + σ`.

## Main results

* `RMF.integral_rpow_le_of_decomposition`: the `q`-th moment of the pointwise decomposition
  `Z ≤ R_r + ∑_{j ∈ [r,m)} 1_{B_j} R_{j+1} + 1_{B_m} Z`, by subadditivity of `x ↦ x^q`, Hölder
  (`RMF.integral_indicator_mul_rpow_le`) and Jensen (`RMF.integral_rpow_le_rpow_integral`).
* `RMF.harperGood` and its variants, the good sets, and
  `RMF.exists_const_harperGood_bounds_of_scale` and `RMF.exists_const_harperGood_bounds_of_top`,
  their two bounds at one level.
* `RMF.integral_rpow_le_of_goodSets`: the interpolation over an abstract good-set family, read
  through `RMF.GoodFamily`.
* `RMF.exists_const_integral_chaosUnit_rpow_le`,
  `RMF.exists_const_integral_chaosUnitShift_rpow_le` and
  `RMF.exists_const_integral_chaosUnitShift_rpow_le_of_top`: the bound at `σ = 0`, at a shift, and
  at a shift with the top `d` blocks dropped.

**`q = 0` and `q = 1` are excluded from the decomposition step.**  At `q = 0` the identity
`(1_B · u)^q = 1_B · u^q` fails, since off `B` the left side is `0^0 = 1`; the interpolation treats
`q = 0` as its own branch, where both sides are `1`.  At `q = 1` Hölder's conjugate exponent
`1/(1-q)` is undefined; the interpolation reaches `q = 1` through the branch `(1-q)√t < 2`, which
uses only Jensen and the bound on `E[Z²]`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Two rewritings of `1_B · u`

Both directions are needed: as a product, to match `RMF.integral_indicator_mul_rpow_le`; as an
indicator, to get integrability from `MeasureTheory.Integrable.indicator`. -/

omit [MeasurableSpace Ω] in
/-- `1_B · u` is the indicator of `u`, not of the constant `1`. -/
lemma indicator_one_mul (B : Set Ω) (u : Ω → ℝ) :
    (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω * u ω) = Set.indicator B u := by
  funext ω
  by_cases hω : ω ∈ B
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, one_mul]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]

omit [MeasurableSpace Ω] in
/-- `(1_B · u)^q = 1_B · u^q`, for `q > 0`.

`q > 0` is what makes it true off `B`, where the left side is `0^q`. -/
lemma indicator_one_mul_rpow {B : Set Ω} {u : Ω → ℝ} {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    (Set.indicator B (fun _ => (1 : ℝ)) ω * u ω) ^ q
      = Set.indicator B (fun _ => (1 : ℝ)) ω * u ω ^ q := by
  by_cases hω : ω ∈ B
  · rw [Set.indicator_of_mem hω, one_mul, one_mul]
  · rw [Set.indicator_of_notMem hω, zero_mul, zero_mul, Real.zero_rpow hq0.ne']

/-! ### The `q`-th moment -/

/-- **The `q`-th moment of the decomposition.**  From the pointwise bound
`Z ≤ R_r + ∑_{j ∈ [r,m)} 1_{B_j} R_{j+1} + 1_{B_m} Z`, all terms nonnegative and integrable, and
`q ∈ (0,1)`:
`E[Z^q] ≤ (E R_r)^q + ∑_{j ∈ [r,m)} μ(B_j)^{1-q}(E R_{j+1})^q + μ(B_m)^{1-q}(E Z)^q`.
The bad sets enter with exponent `1-q`, which the geometric family `n_j = j/(1-q)` of the
interpolation is designed to cancel. -/
theorem integral_rpow_le_of_decomposition {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {R : ℕ → Ω → ℝ} {B : ℕ → Set Ω}
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hR0 : ∀ j ω, 0 ≤ R j ω)
    (hZi : Integrable Z μ) (hRi : ∀ j, Integrable (R j) μ)
    (hB : ∀ j, MeasurableSet (B j)) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (r m : ℕ)
    (hpt : ∀ ω, Z ω ≤ R r ω + (∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω)
      + Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω) :
    (∫ ω, Z ω ^ q ∂μ)
      ≤ (∫ ω, R r ω ∂μ) ^ q
        + (∑ j ∈ Finset.Ico r m, μ.real (B j) ^ (1 - q) * (∫ ω, R (j + 1) ω ∂μ) ^ q)
        + μ.real (B m) ^ (1 - q) * (∫ ω, Z ω ∂μ) ^ q := by
  have hi0 : ∀ (C : Set Ω) (ω : Ω), (0 : ℝ) ≤ Set.indicator C (fun _ => (1 : ℝ)) ω :=
    fun C ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  -- integrability of every piece
  have hZq : Integrable (fun ω => Z ω ^ q) μ :=
    integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0.le hq1.le
  have hRq : ∀ j, Integrable (fun ω => R j ω ^ q) μ := fun j =>
    integrable_rpow_of_integrable (hRi j) (Filter.Eventually.of_forall (hR0 j)) hq0.le hq1.le
  have hIRq : ∀ j, Integrable
      (fun ω => Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) μ := by
    intro j
    rw [indicator_one_mul]
    exact (hRq (j + 1)).indicator (hB j)
  have hIZq : Integrable
      (fun ω => Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω ^ q) μ := by
    rw [indicator_one_mul]
    exact hZq.indicator (hB m)
  have hSum : Integrable (fun ω => ∑ j ∈ Finset.Ico r m,
      Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) μ :=
    integrable_finsetSum _ fun j _ => hIRq j
  -- the pointwise inequality, at the `q`-th power
  have hptq : ∀ ω, Z ω ^ q ≤ R r ω ^ q
      + (∑ j ∈ Finset.Ico r m,
          Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q)
      + Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω ^ q := by
    intro ω
    have hb0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hi0 _ ω) (hR0 _ ω)
    have hc0 : (0 : ℝ) ≤ Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω :=
      mul_nonneg (hi0 _ ω) (hZ0 ω)
    have hab0 : (0 : ℝ) ≤ R r ω + ∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω := by
      linarith [hR0 r ω]
    have h1 : Z ω ^ q ≤ (R r ω + (∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω)
      + Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω) ^ q :=
      Real.rpow_le_rpow (hZ0 ω) (hpt ω) hq0.le
    have h2 := Real.rpow_add_le_add_rpow hab0 hc0 hq0.le hq1.le
    have h3 := Real.rpow_add_le_add_rpow (hR0 r ω) hb0 hq0.le hq1.le
    have h4 : (∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω) ^ q
        ≤ ∑ j ∈ Finset.Ico r m,
          (Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω) ^ q :=
      rpow_sum_le_sum_rpow _ (fun j => mul_nonneg (hi0 _ ω) (hR0 _ ω)) hq0 hq1.le
    have h5 : (∑ j ∈ Finset.Ico r m,
        (Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω) ^ q)
        = ∑ j ∈ Finset.Ico r m,
          Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q :=
      Finset.sum_congr rfl fun j _ => indicator_one_mul_rpow hq0 ω
    have h6 : (Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω) ^ q
        = Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω ^ q :=
      indicator_one_mul_rpow hq0 ω
    rw [h5] at h4
    rw [h6] at h2
    linarith
  -- integrate, and bound each term
  have hAB : Integrable (fun ω => R r ω ^ q + ∑ j ∈ Finset.Ico r m,
      Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) μ := (hRq r).add hSum
  have hmono := integral_mono hZq (((hRq r).add hSum).add hIZq) hptq
  simp only [Pi.add_apply] at hmono
  have hs1 : (∫ ω, R r ω ^ q + (∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q)
      + Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω ^ q ∂μ)
      = (∫ ω, R r ω ^ q + (∑ j ∈ Finset.Ico r m,
          Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) ∂μ)
        + ∫ ω, Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω ^ q ∂μ :=
    integral_add hAB hIZq
  have hs2 : (∫ ω, R r ω ^ q + (∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) ∂μ)
      = (∫ ω, R r ω ^ q ∂μ)
        + ∫ ω, (∑ j ∈ Finset.Ico r m,
            Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) ∂μ :=
    integral_add (hRq r) hSum
  have hs3 : (∫ ω, (∑ j ∈ Finset.Ico r m,
        Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q) ∂μ)
      = ∑ j ∈ Finset.Ico r m,
          ∫ ω, Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q ∂μ :=
    integral_finsetSum _ fun j _ => hIRq j
  rw [hs1, hs2, hs3] at hmono
  have hJr : (∫ ω, R r ω ^ q ∂μ) ≤ (∫ ω, R r ω ∂μ) ^ q :=
    integral_rpow_le_rpow_integral hq0.le hq1.le
      (Filter.Eventually.of_forall fun ω => hR0 r ω) (hRi r) (hRq r)
  have hHj : ∀ j ∈ Finset.Ico r m,
      (∫ ω, Set.indicator (B j) (fun _ => (1 : ℝ)) ω * R (j + 1) ω ^ q ∂μ)
        ≤ μ.real (B j) ^ (1 - q) * (∫ ω, R (j + 1) ω ∂μ) ^ q := fun j _ =>
    integral_indicator_mul_rpow_le (Filter.Eventually.of_forall (hR0 (j + 1))) (hRi (j + 1))
      (hB j) hq0 hq1
  have hHm : (∫ ω, Set.indicator (B m) (fun _ => (1 : ℝ)) ω * Z ω ^ q ∂μ)
      ≤ μ.real (B m) ^ (1 - q) * (∫ ω, Z ω ∂μ) ^ q :=
    integral_indicator_mul_rpow_le (Filter.Eventually.of_forall hZ0) hZi (hB m) hq0 hq1
  have hSj := Finset.sum_le_sum hHj
  linarith

/-! ### The good set

The two bounds of the interpolation speak of the same family of sets, and this is it.  Everything
is pinned except the level `a`:

* the **tube** is `[-a - c·j, a + j + 2\log j]` with `c = RMF.blockSlope 125`, the barrier slope
  of Harper's Proposition 5;
* the **envelope** is the one-sided `2\log j`, admissible for both bounds and summing to `ζ(4)`;
* the **start index** is `⌈a/4⌉₊`, Hamdan's `A/4`.

**The start index is forced from both sides.**  Hamdan's Proposition 2.1 needs `r ≤ a/4 + 1`, and
his Lemma 2.3 needs `a ≤ 4j` for every `j` in the range, that is `a/4 ≤ r`.  Together they pin `r`
to `⌈a/4⌉₊`, so it is written that way rather than carried as two more hypotheses. -/

/-- **The good set at level `a`**: the `ω` whose block walk at `1/2 + ih` stays in the tube
`[-a - c·j, a + j + 2\log j]`, `c = RMF.blockSlope 125`, for every block `j` from `⌈a/4⌉₊` to
`RMF.harperBlockCount D x`.  The counterpart of Hamdan's `G_A`, his (2.12). -/
def harperGood {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (D : ℕ) (x a h : ℝ) : Set Ω' :=
  {ω | ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine 0 h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j)}

/-- **The good set at level `a`, at a shifted abscissa and barrier slope `c`**: the tube is
`[-a - c·j, a + j + 2\log j]`.  The slope is a parameter because Harper's Proposition 5 at tilt
scale `E₀` produces its barrier at `RMF.blockSlopeOf E₀ 125`, and the two bounds must speak of the
same tube: the barrier bound controls the complement, the chaos bound integrates over the set. -/
def harperGoodSlope {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (c : ℝ) (D : ℕ) (x δ a t : ℝ) : Set Ω' :=
  {ω | ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine δ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j)}

lemma mem_harperGoodSlope {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {c : ℝ} {D : ℕ} {x δ a t : ℝ}
    {ω : Ω'} :
    ω ∈ harperGoodSlope Y c D x δ a t ↔ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine δ t))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j) := Iff.rfl

/-- It is measurable, at any slope. -/
lemma measurableSet_harperGoodSlope {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (c : ℝ) (D : ℕ) (x δ a t : ℝ) :
    MeasurableSet (harperGoodSlope Y c D x δ a t) :=
  measurableSet_freeStartBarrier (fun _ => Finset.measurable_sum _ fun p _ =>
    (measurable_localLog _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)) _ _ _ _

/-- And so is its uncurried form, which the `t`-integral needs. -/
lemma measurableSet_harperGoodSlope_uncurry {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (c : ℝ) (D : ℕ) (x δ a : ℝ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ harperGoodSlope Y c D x δ a q.2} :=
  measurableSet_freeStartBarrier_uncurry
    (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2) δ _ _ _ _ _

/-- **The good set with top index `t`**: the tube condition for `j ∈ [⌈a/4⌉₊, t]`;
`RMF.harperGoodSlope` is the case `t = RMF.harperBlockCount D x`.  The range is a parameter
because the decoupled form of Harper's Proposition 5 constrains the barrier on `[⌈a/4⌉, t-d]`
while the tilt stays at the top, and both bounds must speak of the same set. -/
def harperGoodRange {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (c : ℝ) (D : ℕ) (x δ a : ℝ) (t : ℕ)
    (h : ℝ) : Set Ω' :=
  {ω | ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ t →
    walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine δ h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
      ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j)}

lemma mem_harperGoodRange {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {c : ℝ} {D : ℕ} {x δ a : ℝ} {t : ℕ}
    {h : ℝ} {ω : Ω'} :
    ω ∈ harperGoodRange Y c D x δ a t h ↔ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ t →
      walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine δ h))) (Y ((p : Nat.Primes) : ℕ) ω)) j ω
        ∈ Set.Icc (-a - c * (j : ℝ)) (a + (j : ℝ) + 2 * Real.log j) := Iff.rfl

/-- It is measurable, at any range. -/
lemma measurableSet_harperGoodRange {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (c : ℝ) (D : ℕ) (x δ a : ℝ) (t : ℕ)
    (h : ℝ) : MeasurableSet (harperGoodRange Y c D x δ a t h) :=
  measurableSet_freeStartBarrier (fun _ => Finset.measurable_sum _ fun p _ =>
    (measurable_localLog _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)) _ _ _ _

/-- And so is its uncurried form. -/
lemma measurableSet_harperGoodRange_uncurry {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (c : ℝ) (D : ℕ) (x δ a : ℝ) (t : ℕ) :
    MeasurableSet {q : Ω' × ℝ | q.1 ∈ harperGoodRange Y c D x δ a t q.2} :=
  measurableSet_freeStartBarrier_uncurry
    (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2) δ _ _ _ _ _

/-! ### The two bounds at a single level

Both bounds, at one level `a`, with every hypothesis discharged.  Keeping them in one theorem
makes the constants `D`, `n₀`, `x₀`, `a₀` and `C` common to both; the interpolation needs a single
`D`, since the good set is indexed by it.

The barrier bound needs no index conditions: if `⌈a/4⌉₊` exceeds the top block the constraint is
vacuous, the bad set is empty, and the bound holds trivially.  The chaos bound does need them, so
they are hypotheses of that conjunct alone. -/

/-- **The good set's two bounds at a general tilt scale** `|δ|·\log x ≤ η ≤ E₀`, with barrier
slope `RMF.blockSlopeOf E₀ 125`; the constants depend on `E₀`.  The barrier bound's deficit is
`Δ = 1 + 45√E₀ + 120e² + C` (`RMF.abs_sum_primesIco_rpow_sub_le_of_le'` at `K = E₀`), spent
additively in the exponent by `RMF.barrier_upper_exponent_le`.  The chaos bound is
`RMF.exists_const_integral_restrictedChaosUnitShift_le_of_le`, on the unit window because the
decomposition puts the bad event `∃ h ∈ [0,1), ω ∉ G h` outside the height integral. -/
theorem exists_const_harperGood_bounds_of_scale (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (D n₀ : ℕ) (x₀ a₀ C : ℝ), 4 ≤ D ∧ 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ x δ η a : ℝ, x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ →
          |δ| * Real.log x ≤ η → a₀ ≤ a →
          ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
              ω ∉ harperGoodSlope Y (blockSlopeOf E₀ 125) D x δ a h}
              ≤ C * Real.exp (-(2 * a)) ∧
            (⌈a / 4⌉₊ ≤ harperBlockCount D x → n₀ ≤ harperBlockCount D x - ⌈a / 4⌉₊ →
              (∫ ω, restrictedChaosUnitShift
                  (fun ω => compMultExtension fun p => Y p ω) x δ
                  (harperGoodSlope Y (blockSlopeOf E₀ 125) D x δ a) ω ∂ν)
                ≤ C * min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - ⌈a / 4⌉₊))) := by
  obtain ⟨D, n₀, x₀, a₀, C₁, hD, hC₁, H₁⟩ :=
    exists_const_integral_restrictedChaosUnitShift_le_of_le E₀ hE₀
  obtain ⟨Clog, hClog, hlogsum⟩ := exists_const_sum_primesIco_rpow_log_le
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D n₀
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 + 45 * √E₀ + 120 * Real.exp 2 + Clog := ⟨_, rfl⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    have := Real.exp_pos (2 : ℝ)
    linarith [Real.sqrt_nonneg E₀]
  obtain ⟨C₂, hC₂, H₂⟩ :=
    IsSteinhausPrimeValues.exists_const_measure_exists_barrier_le_of_le (Ω := Ω) Δ hΔ1
  have hζ40 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  refine ⟨D, n₀, max x₀ x₂, max (max a₀ 1) (4 * C₂),
    max C₁ (C₂ * Real.exp D * ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)),
    hD, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro Y ν hY x δ η a hx hδ0 hη0 hηE hδx ha
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx1, hDlog, hcount⟩ := hx₂ x hxx₂
  have hD4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hϑ3 : (3 : ℝ) ≤ harperOffset D x := by linarith [sub_one_le_harperOffset D x]
  have hδtop : |δ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x + 1)) ≤ η := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact hδx
  have hClogΔ : Clog ≤ Δ := by
    rw [hΔdef]
    linarith [Real.exp_pos (2 : ℝ), Real.sqrt_nonneg E₀]
  have hps : ∀ j, j ≤ harperBlockCount D x →
      |(∑ p ∈ primesIco (⌊blockScale (harperOffset D x) 0⌋₊ + 1)
          (⌊blockScale (harperOffset D x) j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
        ≤ 45 * √η + 120 * Real.exp 2 * Real.exp (-(1 + harperOffset D x)) := fun j hj =>
    abs_sum_primesIco_rpow_sub_le_of_le' hϑ3 (by omega) hη0 hδ0 hδtop
  have hpsΔ : ∀ j, j ≤ harperBlockCount D x →
      |(∑ p ∈ primesIco (⌊blockScale (harperOffset D x) 0⌋₊ + 1)
          (⌊blockScale (harperOffset D x) j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
        ≤ Δ := by
    intro j hj
    refine le_trans (hps j hj) ?_
    have h1 : Real.exp (-(1 + harperOffset D x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith)
    have h2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
    have hsq : √η ≤ √E₀ := Real.sqrt_le_sqrt hηE
    rw [hΔdef]
    nlinarith [hClog]
  have ha₀ : a₀ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have haC₂ : 4 * C₂ ≤ a := le_trans (le_max_right _ _) ha
  have ha4 : (0 : ℝ) ≤ a / 4 := by linarith
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hrge : a / 4 ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hra : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ a / 4 + 1 := (Nat.ceil_lt_add_one ha4).le
  have hCr : C₂ ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by linarith
  have h4 : ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x → a ≤ 4 * (j : ℝ) := by
    intro j hj _
    have : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : ∀ j, ⌈a / 4⌉₊ ≤ j → (0 : ℝ) ≤ Real.log j := by
    intro j hj
    exact Real.log_nonneg (by exact_mod_cast le_trans hr1 hj)
  refine ⟨?_, ?_⟩
  · -- the barrier half
    have hϑ : (1 : ℝ) ≤ harperOffset D x := by
      have hD2 : (2 : ℕ) ≤ D := by omega
      have hD' : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD2
      linarith [sub_one_le_harperOffset D x]
    have hbar := H₂ Y ν hY (harperOffset D x) a (blockSlopeOf E₀ 125) δ ⌈a / 4⌉₊
      (harperBlockCount D x) (fun j => 2 * Real.log j) hϑ (by linarith)
      (twenty_le_blockSlopeOf E₀ 125) hδ0 hCr (fun j hj _ => by linarith [hlog j hj])
      (fun j hj _ => two_log_le_self (le_trans hr1 hj)) h4
      (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).2])
      (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).1])
      (fun j _ _ => le_trans (hlogsum (harperOffset D x) δ hϑ hδ0 _) (by linarith))
    have hset : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
        ω ∉ harperGoodSlope Y (blockSlopeOf E₀ 125) D x δ a h}
        = {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x →
            walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
              localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (Y (p : ℕ) ω)) j ω
              ∈ Set.Icc (-a - blockSlopeOf E₀ 125 * (j : ℝ))
                (a + (j : ℝ) + (fun j => 2 * Real.log j) j)} := by
      ext ω
      simp only [Set.mem_setOf_eq, mem_harperGoodSlope, heightLine_eq_shiftLine]
    rw [hset]
    refine le_trans hbar ?_
    have hsum := sum_exp_neg_envelope_le (r := ⌈a / 4⌉₊) (n := harperBlockCount D x) hr1
    have hexpϑ : Real.exp (harperOffset D x) ≤ Real.exp D :=
      Real.exp_le_exp.2 (harperOffset_lt_natCast D x).le
    have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x),
        Real.exp (-(2 * (2 * Real.log j))) :=
      Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
    have hA : C₂ * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
        ≤ C₂ * Real.exp D * Real.exp (-(2 * a)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexpϑ hC₂.le)
        (Real.exp_pos _).le
    calc C₂ * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
          * ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x),
              Real.exp (-(2 * (2 * Real.log j)))
        ≤ C₂ * Real.exp D * Real.exp (-(2 * a)) * ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) :=
          mul_le_mul hA hsum h2 (by positivity)
      _ = C₂ * Real.exp D * (∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) * Real.exp (-(2 * a)) := by ring
      _ ≤ max C₁ (C₂ * Real.exp D * ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) * Real.exp (-(2 * a)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · -- the chaos half
    intro hrn hn₀
    have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt ((harperBlockCount D x : ℝ) - ⌈a / 4⌉₊)) :=
      le_min zero_le_one (div_nonneg (by linarith) (Real.sqrt_nonneg _))
    have hchaos := H₁ Ω Y ν hY x δ η a ⌈a / 4⌉₊ (fun j => 2 * Real.log j) hxx₀ hδ0 hη0
      hηE hδx ha₀ ha1 hr1 hrn hra hn₀ (fun j hj1 _ => by
        have h0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
        rw [abs_of_nonneg (by linarith)]
        linarith)
    exact le_trans hchaos (mul_le_mul_of_nonneg_right (le_max_left _ _) hmin0)

/-- **The level `a₀` of `RMF.exists_const_harperGood_bounds_of_top`**, written out: the
restricted chaos's own level, pushed up to `1` and to four times the barrier's constant, which
is where `RMF.IsSteinhausPrimeValues.exists_const_measure_exists_barrier_le_of_le` wants its
starting index. -/
noncomputable def harperGoodTopLevel (a₀ C₂ : ℝ) : ℝ := max (max a₀ 1) (4 * C₂)

/-- **The constant `C` of `RMF.exists_const_harperGood_bounds_of_top`**, written out: the larger
of the restricted chaos's constant and the barrier's, the latter carrying the entropy factor
`e^D` and the envelope sum `ζ(4)`. -/
noncomputable def harperGoodTopConst (C₁ C₂ : ℝ) (D : ℕ) : ℝ :=
  max C₁ (C₂ * Real.exp D * ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ))

/-- **`RMF.exists_const_harperGood_bounds_of_top` with its level and constant named, the barrier's
level `L` apart from its constant `C₂`.**  The deficit is `Δ = 46 + 120e² + C_{\log}`.  The barrier
`H₂` is asked for from the index `L` on, and is told that the block offset is at least `D - 1`: the
sharp form of Hamdan's Lemma 2.3 (`RMF/Probability/MaximalBarrierSharp.lean`) needs both. -/
theorem le_const_harperGood_bounds_of_restricted_of {D n₀ : ℕ} {a₀ C₁ Clog Δ C₂ L : ℝ}
    (hD : 4 ≤ D) (hClog : 0 < Clog)
    (hΔdef : Δ = 1 + 45 + 120 * Real.exp 2 + Clog) (hC₂ : 0 < C₂)
    (H₁ :
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          2 * d ≤ harperBlockCount D x - r → n₀ ≤ harperBlockCount D x - r - d →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => compMultExtension fun p => Y p ω) x σ
                (fun t => {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}) ω ∂ν)
              ≤ C₁ * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)))
    (hlogsum :
      ∀ (ϑ δ : ℝ), 1 ≤ ϑ → 0 ≤ δ → ∀ j : ℕ,
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
        ≤ Real.exp ((j : ℝ) + ϑ) + Clog)
    (H₂ :
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (ϑ A c δ : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → (D : ℝ) - 1 ≤ ϑ → 0 ≤ A → 20 ≤ c →
        0 ≤ δ → L ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ) →
          μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
              walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C₂ * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j))) :
    ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ (x δ η a : ℝ) (t : ℕ), t = harperBlockCount D x - d →
        x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ →
        |δ| * Real.log x ≤ η → harperGoodTopLevel a₀ L ≤ a →
        ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
            ω ∉ harperGoodRange Y (blockSlope 125) D x δ a t h}
            ≤ harperGoodTopConst C₁ C₂ D * Real.exp (-(2 * a)) ∧
          (⌈a / 4⌉₊ ≤ harperBlockCount D x → 2 * d ≤ harperBlockCount D x - ⌈a / 4⌉₊ →
            n₀ ≤ harperBlockCount D x - ⌈a / 4⌉₊ - d →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => compMultExtension fun p => Y p ω) x δ
                (harperGoodRange Y (blockSlope 125) D x δ a t) ω ∂ν)
              ≤ harperGoodTopConst C₁ C₂ D * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) := by
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    have := Real.exp_pos (2 : ℝ)
    linarith
  have hζ40 : (0 : ℝ) ≤ ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) :=
    tsum_nonneg fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  rw [harperGoodTopLevel, harperGoodTopConst]
  intro d E₀ hE₀ hEd
  obtain ⟨x₀, H₁⟩ := H₁ d E₀ hE₀ hEd
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D (max n₀ (2 * d))
  -- the drop dominates the tilt scale and one, which is what the shortened range needs
  have hKd : max E₀ 1 ≤ Real.exp d := max_le hEd (Real.one_le_exp (Nat.cast_nonneg d))
  refine ⟨max x₀ x₂, ?_⟩
  intro Y ν hY x δ η a t ht hx hδ0 hη0 hηE hδx ha
  subst ht
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx1, hDlog, hcount⟩ := hx₂ x hxx₂
  have hdn : 2 * d ≤ harperBlockCount D x := le_trans (le_max_right _ _) hcount
  have hD4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hϑ3 : (3 : ℝ) ≤ harperOffset D x := by linarith [sub_one_le_harperOffset D x]
  -- the tilt scale at the top of the *shortened* range is at most one
  have hδE : |δ| * Real.log (blockScale (harperOffset D x) (harperBlockCount D x + 1))
      ≤ max E₀ 1 := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact le_trans (le_trans hδx hηE) (le_max_left _ _)
  have hδtop : |δ| * Real.log (blockScale (harperOffset D x) (harperBlockCount D x - d + 1)) ≤ 1 :=
    sigma_le_one_of_drop hKd (by omega) hδE
  have hClogΔ : Clog ≤ Δ := by
    rw [hΔdef]
    linarith [Real.exp_pos (2 : ℝ)]
  have hpsΔ : ∀ j, j ≤ harperBlockCount D x - d →
      |(∑ p ∈ primesIco (⌊blockScale (harperOffset D x) 0⌋₊ + 1)
          (⌊blockScale (harperOffset D x) j⌋₊ + 1), (p : ℝ) ^ (-2 * (1 / 2 + δ))) - (j : ℝ)|
        ≤ Δ := by
    intro j hj
    refine le_trans (abs_sum_primesIco_rpow_sub_le_of_le' hϑ3 (by omega) zero_le_one hδ0
      hδtop) ?_
    have h1 : Real.exp (-(1 + harperOffset D x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith)
    have h2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
    rw [hΔdef, Real.sqrt_one]
    nlinarith [hClog]
  have ha₀ : a₀ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have haC₂ : 4 * L ≤ a := le_trans (le_max_right _ _) ha
  have ha4 : (0 : ℝ) ≤ a / 4 := by linarith
  have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
  have hrge : a / 4 ≤ (⌈a / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hra : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ a / 4 + 1 := (Nat.ceil_lt_add_one ha4).le
  have hCr : L ≤ ((⌈a / 4⌉₊ : ℕ) : ℝ) := by linarith
  have h4 : ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x - d → a ≤ 4 * (j : ℝ) := by
    intro j hj _
    have : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : ∀ j, ⌈a / 4⌉₊ ≤ j → (0 : ℝ) ≤ Real.log j := by
    intro j hj
    exact Real.log_nonneg (by exact_mod_cast le_trans hr1 hj)
  refine ⟨?_, ?_⟩
  · -- the barrier half, at the absolute deficit
    have hϑ : (1 : ℝ) ≤ harperOffset D x := by linarith
    have hbar := H₂ Y ν hY (harperOffset D x) a (blockSlope 125) δ ⌈a / 4⌉₊
      (harperBlockCount D x - d) (fun j => 2 * Real.log j) hϑ (sub_one_le_harperOffset D x)
      (by linarith)
      (twenty_le_blockSlope 125) hδ0 hCr (fun j hj _ => by linarith [hlog j hj])
      (fun j hj _ => two_log_le_self (le_trans hr1 hj)) h4
      (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).2])
      (fun j _ hjn => by linarith [(abs_le.1 (hpsΔ j hjn)).1])
      (fun j _ _ => le_trans (hlogsum (harperOffset D x) δ hϑ hδ0 _) (by linarith))
    have hset : {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
        ω ∉ harperGoodRange Y (blockSlope 125) D x δ a (harperBlockCount D x - d) h}
        = {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, ⌈a / 4⌉₊ ≤ j → j ≤ harperBlockCount D x - d →
            walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
              localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (Y (p : ℕ) ω)) j ω
              ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ))
                (a + (j : ℝ) + (fun j => 2 * Real.log j) j)} := by
      ext ω
      simp only [Set.mem_setOf_eq, mem_harperGoodRange, heightLine_eq_shiftLine]
    rw [hset]
    refine le_trans hbar ?_
    have hsum := sum_exp_neg_envelope_le (r := ⌈a / 4⌉₊) (n := harperBlockCount D x - d) hr1
    have hexpϑ : Real.exp (harperOffset D x) ≤ Real.exp D :=
      Real.exp_le_exp.2 (harperOffset_lt_natCast D x).le
    have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x - d),
        Real.exp (-(2 * (2 * Real.log j))) :=
      Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
    have hA : C₂ * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
        ≤ C₂ * Real.exp D * Real.exp (-(2 * a)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexpϑ hC₂.le)
        (Real.exp_pos _).le
    calc C₂ * Real.exp (harperOffset D x) * Real.exp (-(2 * a))
          * ∑ j ∈ Finset.Icc ⌈a / 4⌉₊ (harperBlockCount D x - d),
              Real.exp (-(2 * (2 * Real.log j)))
        ≤ C₂ * Real.exp D * Real.exp (-(2 * a)) * ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ) :=
          mul_le_mul hA hsum h2 (by positivity)
      _ = C₂ * Real.exp D * (∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) * Real.exp (-(2 * a)) := by ring
      _ ≤ max C₁ (C₂ * Real.exp D * ∑' i : ℕ, (i : ℝ) ^ (-4 : ℝ)) * Real.exp (-(2 * a)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · -- the chaos half
    intro hrn hdr hn₀
    have hmin0 : (0 : ℝ)
        ≤ min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - ⌈a / 4⌉₊)) :=
      le_min zero_le_one (div_nonneg (by linarith) (Real.sqrt_nonneg _))
    have hchaos := H₁ Y ν hY x δ η a ⌈a / 4⌉₊ (fun j => 2 * Real.log j) hxx₀ hδ0 hη0
      hηE hδx ha₀ ha1 hr1 hrn hra hdr hn₀ (fun j hj1 _ => by
        have h0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
        rw [abs_of_nonneg (by linarith)]
        linarith)
    exact le_trans hchaos (mul_le_mul_of_nonneg_right (le_max_left _ _) hmin0)

/-- **`RMF.exists_const_harperGood_bounds_of_top` with its level and constant named**:
`RMF.le_const_harperGood_bounds_of_restricted_of` with the barrier's level its constant. -/
theorem le_const_harperGood_bounds_of_restricted {D n₀ : ℕ} {a₀ C₁ Clog Δ C₂ : ℝ}
    (hD : 4 ≤ D) (hClog : 0 < Clog)
    (hΔdef : Δ = 1 + 45 + 120 * Real.exp 2 + Clog) (hC₂ : 0 < C₂)
    (H₁ :
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (r : ℕ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η →
          a₀ ≤ a → 1 ≤ a →
          1 ≤ r → r ≤ harperBlockCount D x → (r : ℝ) ≤ a / 4 + 1 →
          2 * d ≤ harperBlockCount D x - r → n₀ ≤ harperBlockCount D x - r - d →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => compMultExtension fun p => Y p ω) x σ
                (fun t => {ω | ∀ j, r ≤ j → j ≤ harperBlockCount D x - d →
                  walk (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t)))
                      (Y ((p : Nat.Primes) : ℕ) ω)) j ω
                    ∈ Set.Icc (-a - blockSlope 125 * (j : ℝ))
                        (a + (j : ℝ) + hf j)}) ω ∂ν)
              ≤ C₁ * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r)))
    (hlogsum :
      ∀ (ϑ δ : ℝ), 1 ≤ ϑ → 0 ≤ δ → ∀ j : ℕ,
      (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
          (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p)
        ≤ Real.exp ((j : ℝ) + ϑ) + Clog)
    (H₂ :
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (ϑ A c δ : ℝ) (r n : ℕ) (b : ℕ → ℝ), 1 ≤ ϑ → 0 ≤ A → 20 ≤ c → 0 ≤ δ → C₂ ≤ (r : ℝ) →
        (∀ j, r ≤ j → j ≤ n → 0 ≤ b j) →
        (∀ j, r ≤ j → j ≤ n → b j ≤ (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n → A ≤ 4 * (j : ℝ)) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) ≤ (j : ℝ) + Δ) →
        (∀ j, r ≤ j → j ≤ n → (j : ℝ) - Δ ≤
          ∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ))) →
        (∀ j, r ≤ j → j ≤ n →
          (∑ p ∈ primesIco (⌊blockScale ϑ 0⌋₊ + 1) (⌊blockScale ϑ j⌋₊ + 1),
            (p : ℝ) ^ (-2 * (1 / 2 + δ)) * Real.log p) ≤ Real.exp ((j : ℝ) + ϑ) + Δ) →
          μ.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ¬ ∀ j, r ≤ j → j ≤ n →
              walk (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
          localLog (((p : ℕ) : ℂ) ^ (-(heightLine (1 / 2 + δ) h))) (X (p : ℕ) ω)) j ω
                ∈ Set.Icc (-A - c * (j : ℝ)) (A + (j : ℝ) + b j)}
            ≤ C₂ * Real.exp ϑ * Real.exp (-(2 * A))
              * ∑ j ∈ Finset.Icc r n, Real.exp (-(2 * b j))) :
    ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ (x δ η a : ℝ) (t : ℕ), t = harperBlockCount D x - d →
        x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ →
        |δ| * Real.log x ≤ η → harperGoodTopLevel a₀ C₂ ≤ a →
        ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
            ω ∉ harperGoodRange Y (blockSlope 125) D x δ a t h}
            ≤ harperGoodTopConst C₁ C₂ D * Real.exp (-(2 * a)) ∧
          (⌈a / 4⌉₊ ≤ harperBlockCount D x → 2 * d ≤ harperBlockCount D x - ⌈a / 4⌉₊ →
            n₀ ≤ harperBlockCount D x - ⌈a / 4⌉₊ - d →
            (∫ ω, restrictedChaosUnitShift
                (fun ω => compMultExtension fun p => Y p ω) x δ
                (harperGoodRange Y (blockSlope 125) D x δ a t) ω ∂ν)
              ≤ harperGoodTopConst C₁ C₂ D * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) :=
  le_const_harperGood_bounds_of_restricted_of (L := C₂) hD hClog hΔdef hC₂ H₁ hlogsum
    (fun X μ hX ϑ A c δ r n b hϑ _ => H₂ X μ hX ϑ A c δ r n b hϑ)

/-- **The good set's two bounds with the top `d` blocks dropped, at an absolute deficit.**  The
barrier runs only to `t = n - d`, where `RMF.sigma_le_one_of_drop` puts the tilt scale under `1`,
so the deficit is `Δ = 46 + 120e² + C` instead of `RMF.exists_const_harperGood_bounds_of_scale`'s
`1 + 45√E₀ + 120e² + C`, and `D`, `n₀`, `a₀`, `C` do not depend on `d` or on `E₀ ≤ e^d` (only `x₀`
does).  A caller may therefore choose `E₀` after seeing the constants. -/
theorem exists_const_harperGood_bounds_of_top :
    ∃ (D n₀ : ℕ) (a₀ C : ℝ), 4 ≤ D ∧ 0 < C ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ (x δ η a : ℝ) (t : ℕ), t = harperBlockCount D x - d →
          x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ →
          |δ| * Real.log x ≤ η → a₀ ≤ a →
          ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
              ω ∉ harperGoodRange Y (blockSlope 125) D x δ a t h}
              ≤ C * Real.exp (-(2 * a)) ∧
            (⌈a / 4⌉₊ ≤ harperBlockCount D x → 2 * d ≤ harperBlockCount D x - ⌈a / 4⌉₊ →
              n₀ ≤ harperBlockCount D x - ⌈a / 4⌉₊ - d →
              (∫ ω, restrictedChaosUnitShift
                  (fun ω => compMultExtension fun p => Y p ω) x δ
                  (harperGoodRange Y (blockSlope 125) D x δ a t) ω ∂ν)
                ≤ C * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) := by
  obtain ⟨D, n₀, a₀, C₁, hD, hC₁, H₁⟩ :=
    exists_const_integral_restrictedChaosUnitShift_le_of_top
  obtain ⟨Clog, hClog, hlogsum⟩ := exists_const_sum_primesIco_rpow_log_le
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 + 45 + 120 * Real.exp 2 + Clog := ⟨_, rfl⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := by
    rw [hΔdef]
    have := Real.exp_pos (2 : ℝ)
    linarith
  obtain ⟨C₂, hC₂, H₂⟩ :=
    IsSteinhausPrimeValues.exists_const_measure_exists_barrier_le_of_le (Ω := Ω) Δ hΔ1
  exact ⟨D, n₀, harperGoodTopLevel a₀ C₂, harperGoodTopConst C₁ C₂ D, hD,
    lt_of_lt_of_le hC₁ (le_max_left _ _),
    le_const_harperGood_bounds_of_restricted hD hClog hΔdef hC₂
      (fun d E₀ hE₀ hEd => (H₁ d E₀ hE₀ hEd).imp fun _ h => h Ω) hlogsum H₂⟩

/-! ### The index arithmetic

Three inequalities about the geometric family `n_j = j/(1-q)`, stated with no probability in
them. -/

/-- **Every level of the family is below `3√t`.**  This is Hamdan's `A ≤ 3√t`, and it is what makes
the index conditions of the good set's two bounds dischargeable.

`hL2` is where `2 ≤ (1-q)√t` is used: it turns the ceiling loss `1/(1-q)` of `j₀` and `K` into
`√t/2`, which is what keeps the level below a *multiple* of `√t` rather than growing with `1/(1-q)`.
-/
lemma level_le_three_sqrt {q st A₀ jr Kr u : ℝ} (h1q : 0 < 1 - q) (hA₀st : A₀ ≤ st)
    (hL2 : 2 ≤ (1 - q) * st) (hj₀ : jr ≤ A₀ * (1 - q) + 1)
    (hK : Kr ≤ jr + ((1 - q) * st + 1)) (hu : u ≤ Kr) :
    u / (1 - q) ≤ 3 * st := by
  rw [div_le_iff₀ h1q]
  nlinarith [mul_le_mul_of_nonneg_right hA₀st h1q.le]

/-- **The start index of a level below `3√t` is below `t/2`**, once `√t ≥ 3`. -/
lemma start_le_half {lev st T r : ℝ} (hlev0 : 0 ≤ lev) (hlev : lev ≤ 3 * st)
    (hst3 : 3 ≤ st) (hsts : st ^ 2 = T) (hr : r ≤ lev / 4 + 1) :
    r ≤ T / 2 := by
  nlinarith

/-- **And the denominator of the second bound is at least `√t/2`.**  This is where the
`\min\{1, a/√(n-r)\}` of Hamdan's Proposition 2.1, as formalised, becomes his `a/√t`; the factor
`2` is the whole cost of the free start. -/
lemma min_one_div_sqrt_sub_le {a st T r : ℝ} (ha0 : 0 ≤ a) (hst : 0 < st) (hsts : st ^ 2 = T)
    (hr : r ≤ T / 2) : min 1 (a / Real.sqrt (T - r)) ≤ 2 * a / st := by
  refine le_trans (min_le_right _ _) ?_
  have hT0 : (0 : ℝ) ≤ T := by nlinarith
  have hhalf : st / 2 ≤ Real.sqrt (T - r) := by
    refine (Real.le_sqrt (by positivity) (by linarith)).2 ?_
    nlinarith
  have h2 : a / Real.sqrt (T - r) ≤ a / (st / 2) :=
    div_le_div_of_nonneg_left ha0 (by positivity) hhalf
  have h3 : a / (st / 2) = 2 * a / st := by
    field_simp
  rwa [h3] at h2

/-! ### The interpolation

The interpolation of Soundararajan and Zaman over a **geometric family of barriers**, as in
Hamdan's proof of his Proposition 1.2.  With `t` the number of blocks and `L := (1-q)√t`, the
levels are `n_j := j/(1-q)` for `j₀ := ⌈A₀(1-q)⌉₊ ≤ j ≤ K := j₀ + ⌈L⌉₊`.  The bad sets enter
with exponent `1-q`, and `P(bad_j)^{1-q} ≪ e^{-2n_j(1-q)} = e^{-2j}` is free of `q`:
`RMF.sum_exp_mul_rpow_le` sums `e^{-2j}(j+1)^q` to an absolute constant, and `L^{-q}` factors out.

**The three branches.**  `q = 0`: both sides are constants.  `L < 2`: the target is `≥ 1/3`
(`RMF.one_third_le_target`), and Jensen with the mean chaos bounds the left side.  `L ≥ 2`: the
interpolation proper; `L ≥ 2` forces `q < 1`, which `RMF.integral_rpow_le_of_decomposition` needs.

**The bad sets need not be measurable**: `∃ h ∈ [0,1)` is an uncountable union of complements.
`MeasureTheory.exists_measurable_superset` replaces each by a measurable hull of the same measure;
the pointwise decomposition only improves, since the restricted chaos is nonnegative.

The interpolation is proved once, in `RMF.integral_rpow_le_of_goodSets`, and reads the good sets
only through the fields bundled in `RMF.GoodFamily`. -/

/-- **What the interpolation reads a good-set family through.**  `set a h` is the good set at
level `a` and height `h`; the two measurability fields are what the `h`-integral needs,
`measure_bad_le` drives the geometric sum, and `integral_restricted_le` is the chaos bound on it.
`RMF.exists_const_integral_chaosUnitShift_rpow_le` and its `_of_top` form build it differently and
are not instances of one another: the first lets the slope grow with `E₀` and keeps every block,
the second fixes the slope and drops `d` blocks, with `E₀ ≤ e^d`. -/
structure GoodFamily {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℂ) (ν : Measure Ω)
    (x σ : ℝ) (t n₀ : ℕ) (a₀ C₂ : ℝ) where
  /-- The good set at level `a` and height `h`. -/
  set : ℝ → ℝ → Set Ω
  measurableSet : ∀ a h, MeasurableSet (set a h)
  measurableSet_uncurry : ∀ a, MeasurableSet {p : Ω × ℝ | p.1 ∈ set a p.2}
  /-- The bad set is exponentially small in the level. -/
  measure_bad_le : ∀ a, a₀ ≤ a →
    ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ set a h} ≤ C₂ * Real.exp (-(2 * a))
  /-- The chaos, restricted to the good set. -/
  integral_restricted_le : ∀ a, a₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ t → n₀ ≤ t - ⌈a / 4⌉₊ →
    (∫ ω, restrictedChaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ (set a) ω ∂ν)
      ≤ C₂ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))

set_option maxHeartbeats 1000000 in
-- 300 lines: the interpolation, three branches, the hulls and the level arithmetic in one
/-- **The interpolation, over an abstract chaos.**  For `q ∈ [0,1]`,
`E[Z^q] ≤ C·(1 + (1-q)√t)^{-q}` with `C` explicit in `C₁`, `C₂` and `a₀`, given `E Z ≤ C₁` and a
decomposition `hdec` of `Z` along good sets whose bad sets over the window `win` have measure
`≤ C₂e^{-2a}` and on which the restricted chaos `Rst` is `≤ C₂\min\{1, a/√(t - ⌈a/4⌉₊)\}`.
`RMF.integral_rpow_le_of_goodFamily` (window `[0,1)`) and
`RMF.integral_rpow_le_of_goodFamily_rademacher` (window `(w, w+1]`) are its instances. -/
theorem integral_rpow_le_of_goodSets {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} {Rst : (ℝ → Set Ω) → Ω → ℝ} {win : Set ℝ}
    {q : ℝ} {t n₀ : ℕ} {a₀ C₁ C₂ : ℝ}
    (hZ0' : ∀ ω, 0 ≤ Z ω) (hZi' : Integrable Z ν)
    (hR0' : ∀ (S : ℝ → Set Ω) (ω : Ω), 0 ≤ Rst S ω)
    (hRi' : ∀ S : ℝ → Set Ω, (∀ h, MeasurableSet (S h)) →
      MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2} → Integrable (Rst S) ν)
    (hdec : ∀ (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ), r ≤ m →
      Z ω ≤ Rst (S r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ win, ω ∉ S j h} (fun _ => (1 : ℝ)) ω * Rst (S (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ win, ω ∉ S m h} (fun _ => (1 : ℝ)) ω * Z ω)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hZmean : (∫ ω, Z ω ∂ν) ≤ C₁)
    (hT1 : 2 * n₀ ≤ t) (hT2 : ⌈max a₀ 3⌉₊ ^ 2 ≤ t)
    (Gset : ℝ → ℝ → Set Ω)
    (Gmeas : ∀ a h, MeasurableSet (Gset a h))
    (Gunc : ∀ a, MeasurableSet {p : Ω × ℝ | p.1 ∈ Gset a p.2})
    (Gbad : ∀ a, a₀ ≤ a → ν.real {ω | ∃ h ∈ win, ω ∉ Gset a h} ≤ C₂ * Real.exp (-(2 * a)))
    (Gint : ∀ a, a₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ t → n₀ ≤ t - ⌈a / 4⌉₊ →
      (∫ ω, Rst (Gset a) ω ∂ν) ≤ C₂ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) :
    (∫ ω, Z ω ^ q ∂ν)
      ≤ 3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)
        * (1 + (1 - q) * Real.sqrt (t : ℝ)) ^ (-q) := by
  have hKz1 : (1 : ℝ) ≤ max 1 C₁ := le_max_left _ _
  have hKb1 : (1 : ℝ) ≤ max 1 (2 * C₂) := le_max_left _ _
  have hKj1 : (1 : ℝ) ≤ max 1 (2 * C₂ * (max a₀ 3 + 1)) := le_max_left _ _
  obtain ⟨ZZ, hZZ⟩ : ∃ ZZ : Ω → ℝ,
      ZZ = Z :=
    ⟨_, rfl⟩
  rw [← hZZ]
  have hZ0 : ∀ ω, 0 ≤ ZZ ω := by
    rw [hZZ]; exact hZ0'
  have hZi : Integrable ZZ ν := by
    rw [hZZ]; exact hZi'
  have hZmean0 : (0 : ℝ) ≤ ∫ ω, ZZ ω ∂ν := integral_nonneg hZ0
  have hZmean : (∫ ω, ZZ ω ∂ν) ≤ C₁ := by
    rw [hZZ]; exact hZmean
  have hZpow : (∫ ω, ZZ ω ∂ν) ^ q ≤ max 1 C₁ :=
    le_trans (Real.rpow_le_rpow hZmean0 hZmean hq0) (rpow_le_max_one hC₁ hq0 hq1)
  have hjensen : (∫ ω, ZZ ω ^ q ∂ν) ≤ max 1 C₁ := by
    have hZqi := integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0 hq1
    exact le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall hZ0) hZi hZqi) hZpow
  set st : ℝ := Real.sqrt (t : ℝ) with hstdef
  have hst0 : (0 : ℝ) ≤ st := Real.sqrt_nonneg _
  -- branch 1: `q = 0`, where both sides are constants
  rcases eq_or_lt_of_le hq0 with rfl | hq0'
  · have h1 : (∫ ω, ZZ ω ^ (0 : ℝ) ∂ν) = 1 := by simp
    rw [h1, neg_zero, Real.rpow_zero, mul_one]
    nlinarith
  -- branch 2: the target is bounded below, so an absolute bound suffices
  rcases lt_or_ge ((1 - q) * st) 2 with hLsmall | hL2
  · have htar : (1 : ℝ) / 3 ≤ (1 + (1 - q) * st) ^ (-q) :=
      one_third_le_target hq0 hq1 hLsmall
    have hKbb : (0 : ℝ) ≤ max 1 (2 * C₂) * max 1 (2 * C₂) :=
      mul_nonneg (by linarith) (by linarith)
    have hKbz : (0 : ℝ) ≤ max 1 (2 * C₂) * max 1 C₁ :=
      mul_nonneg (by linarith) (by linarith)
    have hC0 : (0 : ℝ) < 3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
        + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁) := by
      linarith
    linarith [mul_le_mul_of_nonneg_left htar hC0.le, hjensen]
  -- branch 3: the interpolation
  have h1q : (0 : ℝ) < 1 - q := by
    rcases le_or_gt (1 - q) 0 with h | h
    · exact absurd hL2 (by nlinarith [mul_nonneg (neg_nonneg.2 h) hst0])
    · exact h
  have hq1' : q < 1 := by linarith
  have hL0 : (0 : ℝ) < (1 - q) * st := by linarith
  have hA₀3 : (3 : ℝ) ≤ max a₀ 3 := le_max_right _ _
  have hA₀a : a₀ ≤ max a₀ 3 := le_max_left _ _
  have hA₀st : max a₀ 3 ≤ st := by
    rw [hstdef]
    refine (Real.le_sqrt (by linarith) (Nat.cast_nonneg t)).2 ?_
    have h1 : max a₀ 3 ≤ ((⌈max a₀ 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈max a₀ 3⌉₊ ^ 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hT2
    push_cast at h2
    have h3 : (0 : ℝ) ≤ max a₀ 3 := by linarith
    nlinarith [h1, h2, h3]
  have hst3 : (3 : ℝ) ≤ st := le_trans hA₀3 hA₀st
  have hsts : st ^ 2 = (t : ℝ) := Real.sq_sqrt (Nat.cast_nonneg t)
  have hn₀st : (n₀ : ℝ) ≤ (t : ℝ) / 2 := by
    have h : ((2 * n₀ : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hT1
    push_cast at h
    linarith
  -- the geometric family of levels
  set j₀ : ℕ := ⌈max a₀ 3 * (1 - q)⌉₊ with hj₀def
  set KK : ℕ := j₀ + ⌈(1 - q) * st⌉₊ with hKKdef
  set lev : ℕ → ℝ := fun j => (j : ℝ) / (1 - q) with hlevdef
  have hlev0 : ∀ j : ℕ, 0 ≤ lev j := fun j => div_nonneg (Nat.cast_nonneg j) h1q.le
  have hlevmul : ∀ j : ℕ, lev j * (1 - q) = (j : ℝ) := fun j => div_mul_cancel₀ _ h1q.ne'
  have hj₀ge : max a₀ 3 * (1 - q) ≤ (j₀ : ℝ) := Nat.le_ceil _
  have hA₀0 : (0 : ℝ) ≤ max a₀ 3 := by linarith
  have hj₀lt : ((j₀ : ℕ) : ℝ) ≤ max a₀ 3 * (1 - q) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hA₀0 h1q.le)).le
  have hj₀one : ((j₀ : ℕ) : ℝ) ≤ max a₀ 3 + 1 := by
    have h := mul_le_mul_of_nonneg_left (show 1 - q ≤ 1 by linarith) hA₀0
    rw [mul_one] at h
    linarith
  have hKlt : ((KK : ℕ) : ℝ) ≤ ((j₀ : ℕ) : ℝ) + ((1 - q) * st + 1) := by
    rw [hKKdef]
    push_cast
    linarith [(Nat.ceil_lt_add_one hL0.le).le]
  have hKge : (1 - q) * st ≤ ((KK : ℕ) : ℝ) := by
    rw [hKKdef]
    push_cast
    linarith [Nat.le_ceil ((1 - q) * st), Nat.cast_nonneg (α := ℝ) j₀]
  have hlevK : ∀ j : ℕ, j ≤ KK → lev j ≤ 3 * st := fun j hj =>
    level_le_three_sqrt h1q hA₀st hL2 hj₀lt hKlt (by exact_mod_cast hj)
  have hrhalf : ∀ j : ℕ, j ≤ KK → ((⌈lev j / 4⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) / 2 := fun j hj =>
    start_le_half (hlev0 j) (hlevK j hj) hst3 hsts
      (Nat.ceil_lt_add_one (by linarith [hlev0 j])).le
  have hrtwo : ∀ j : ℕ, j ≤ KK → 2 * ⌈lev j / 4⌉₊ ≤ t := by
    intro j hj
    have hc : ((2 * ⌈lev j / 4⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by
      push_cast
      linarith [hrhalf j hj]
    exact_mod_cast hc
  have hrn : ∀ j : ℕ, j ≤ KK → ⌈lev j / 4⌉₊ ≤ t := by
    intro j hj
    have hc : ((⌈lev j / 4⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by
      linarith [hrhalf j hj, Nat.cast_nonneg (α := ℝ) t]
    exact_mod_cast hc
  have hn₀K : ∀ j : ℕ, j ≤ KK → n₀ ≤ t - ⌈lev j / 4⌉₊ := by
    intro j hj
    refine Nat.le_sub_of_add_le ?_
    have hc : ((n₀ + ⌈lev j / 4⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by
      push_cast
      linarith [hrhalf j hj, hn₀st]
    exact_mod_cast hc
  have ha₀lev : ∀ j : ℕ, j₀ ≤ j → a₀ ≤ lev j := by
    intro j hj
    have h2 : ((j₀ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [hlevdef, le_div_iff₀ h1q]
    linarith [mul_le_mul_of_nonneg_right hA₀a h1q.le, hj₀ge, h2]
  -- the restricted chaos at each level
  obtain ⟨RR, hRR⟩ : ∃ RR : ℕ → Ω → ℝ, RR = fun j =>
      Rst (Gset (lev j)) := ⟨_, rfl⟩
  have hR0 : ∀ (j : ℕ) (ω : Ω), 0 ≤ RR j ω := by
    rw [hRR]; exact fun j ω => hR0' _ ω
  have hRi : ∀ j : ℕ, Integrable (RR j) ν := by
    rw [hRR]
    exact fun j => hRi' _ (fun h => Gmeas (lev j) h) (Gunc (lev j))
  have hRmean0 : ∀ j : ℕ, (0 : ℝ) ≤ ∫ ω, RR j ω ∂ν := fun j => integral_nonneg (hR0 j)
  have hRle : ∀ j : ℕ, j₀ ≤ j → j ≤ KK →
      (∫ ω, RR j ω ∂ν) ≤ 2 * C₂ * (lev j) / st := by
    intro j hj1 hj2
    have hb := Gint (lev j) (ha₀lev j hj1)
      (hrtwo j hj2) (hn₀K j hj2)
    rw [hRR]
    refine le_trans hb ?_
    have hmin := min_one_div_sqrt_sub_le (hlev0 j) (by linarith : (0 : ℝ) < st) hsts
      (hrhalf j hj2)
    have h2 : C₂ * min 1 (lev j / Real.sqrt ((t : ℝ) - ((⌈lev j / 4⌉₊ : ℕ) : ℝ)))
        ≤ C₂ * (2 * lev j / st) := mul_le_mul_of_nonneg_left hmin hC₂.le
    calc C₂ * min 1 (lev j / Real.sqrt ((t : ℝ) - ((⌈lev j / 4⌉₊ : ℕ) : ℝ)))
        ≤ C₂ * (2 * lev j / st) := h2
      _ = 2 * C₂ * lev j / st := by ring
  -- the bad sets, replaced by measurable hulls of the same measure
  choose B hBsub hBmeas hBmeasure using fun j : ℕ => exists_measurable_superset ν
    {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h}
  have hBreal : ∀ j : ℕ, ν.real (B j)
      = ν.real {ω | ∃ h ∈ win,
        ω ∉ Gset (lev j) h} := by
    intro j
    rw [measureReal_def, measureReal_def, hBmeasure j]
  -- the pointwise decomposition, on the hulls
  have hpt : ∀ ω, ZZ ω ≤ RR j₀ ω
      + (∑ j ∈ Finset.Ico j₀ KK,
          Set.indicator (B j) (fun _ => (1 : ℝ)) ω * RR (j + 1) ω)
      + Set.indicator (B KK) (fun _ => (1 : ℝ)) ω * ZZ ω := by
    intro ω
    rw [hZZ, hRR]
    refine le_trans (hdec (fun j => Gset (lev j)) ω j₀ KK (Nat.le_add_right _ _)) ?_
    have hstep : ∀ (j : ℕ) (u : ℝ), 0 ≤ u →
        Set.indicator {ω | ∃ h ∈ win,
            ω ∉ Gset (lev j) h}
            (fun _ => (1 : ℝ)) ω * u
          ≤ Set.indicator (B j) (fun _ => (1 : ℝ)) ω * u := by
      intro j u hu
      refine mul_le_mul_of_nonneg_right ?_ hu
      by_cases hm : ω ∈ {ω | ∃ h ∈ win,
          ω ∉ Gset (lev j) h}
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hBsub j hm)]
      · rw [Set.indicator_of_notMem hm]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.Ico j₀ KK) =>
      hstep j _ (by simpa [hRR] using hR0 (j + 1) ω))
    have htail := hstep KK _ (by simpa [hZZ] using hZ0 ω)
    linarith
  have hmain := integral_rpow_le_of_decomposition hZ0 hR0 hZi hRi hBmeas hq0' hq1' j₀ KK hpt
  -- the three terms
  have hpow : ∀ e u v : ℝ, 0 ≤ e → e ≤ 1 → 0 ≤ u → u ≤ v → 0 < v → u ^ e ≤ max 1 v :=
    fun e u v he0 he1 hu huv hv =>
      le_trans (Real.rpow_le_rpow hu huv he0) (rpow_le_max_one hv he0 he1)
  have hdiv : ∀ u : ℝ, 0 ≤ u → (u / ((1 - q) * st)) ^ q
      = u ^ q * ((1 - q) * st) ^ (-q) := by
    intro u hu
    rw [div_eq_mul_inv, Real.mul_rpow hu (inv_nonneg.2 hL0.le), Real.inv_rpow hL0.le,
      ← Real.rpow_neg hL0.le]
  have hM0 : (0 : ℝ) ≤ ((1 - q) * st) ^ (-q) := Real.rpow_nonneg hL0.le _
  -- (a) the first term
  have hfirst : (∫ ω, RR j₀ ω ∂ν) ^ q
      ≤ max 1 (2 * C₂ * (max a₀ 3 + 1)) * ((1 - q) * st) ^ (-q) := by
    have h1 : (∫ ω, RR j₀ ω ∂ν) ≤ (2 * C₂ * (j₀ : ℝ)) / ((1 - q) * st) := by
      have h := hRle j₀ le_rfl (Nat.le_add_right _ _)
      rw [hlevdef] at h
      calc (∫ ω, RR j₀ ω ∂ν) ≤ 2 * C₂ * ((j₀ : ℝ) / (1 - q)) / st := h
        _ = (2 * C₂ * (j₀ : ℝ)) / ((1 - q) * st) := by field_simp
    have h2 : (∫ ω, RR j₀ ω ∂ν) ^ q ≤ ((2 * C₂ * (j₀ : ℝ)) / ((1 - q) * st)) ^ q :=
      Real.rpow_le_rpow (hRmean0 j₀) h1 hq0
    rw [hdiv _ (by positivity)] at h2
    refine le_trans h2 (mul_le_mul_of_nonneg_right ?_ hM0)
    have hC2' : (0 : ℝ) ≤ 2 * C₂ := by linarith
    have hvpos : (0 : ℝ) < 2 * C₂ * (max a₀ 3 + 1) :=
      mul_pos (by linarith) (by linarith)
    exact hpow q _ _ hq0 hq1 (by positivity) (mul_le_mul_of_nonneg_left hj₀one hC2') hvpos
  -- (b) the sum
  have hbadpow : ∀ j : ℕ, j₀ ≤ j →
      ν.real (B j) ^ (1 - q) ≤ max 1 (2 * C₂) * Real.exp (-2 * (j : ℝ)) := by
    intro j hj
    have h0 : (0 : ℝ) ≤ ν.real (B j) := measureReal_nonneg
    have h1 : ν.real (B j) ≤ C₂ * Real.exp (-(2 * lev j)) := by
      rw [hBreal j]
      exact Gbad (lev j) (ha₀lev j hj)
    have h2 : ν.real (B j) ^ (1 - q) ≤ (C₂ * Real.exp (-(2 * lev j))) ^ (1 - q) :=
      Real.rpow_le_rpow h0 h1 (by linarith)
    have h3 : (C₂ * Real.exp (-(2 * lev j))) ^ (1 - q)
        = C₂ ^ (1 - q) * Real.exp (-2 * (j : ℝ)) := by
      rw [Real.mul_rpow hC₂.le (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      rw [← hlevmul j]
      ring
    have h4 : C₂ ^ (1 - q) ≤ max 1 (2 * C₂) :=
      hpow (1 - q) C₂ (2 * C₂) h1q.le (by linarith) hC₂.le (by linarith) (by linarith)
    rw [h3] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
  have hstepbd : ∀ j : ℕ, j₀ ≤ j → j < KK → (∫ ω, RR (j + 1) ω ∂ν) ^ q
      ≤ max 1 (2 * C₂) * (((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q)) := by
    intro j hj1 hj2
    have h1 : (∫ ω, RR (j + 1) ω ∂ν) ≤ (2 * C₂ * ((j : ℝ) + 1)) / ((1 - q) * st) := by
      have h := hRle (j + 1) (by omega) (by omega)
      rw [hlevdef] at h
      push_cast at h
      calc (∫ ω, RR (j + 1) ω ∂ν) ≤ 2 * C₂ * (((j : ℝ) + 1) / (1 - q)) / st := h
        _ = (2 * C₂ * ((j : ℝ) + 1)) / ((1 - q) * st) := by field_simp
    have h2 : (∫ ω, RR (j + 1) ω ∂ν) ^ q
        ≤ ((2 * C₂ * ((j : ℝ) + 1)) / ((1 - q) * st)) ^ q :=
      Real.rpow_le_rpow (hRmean0 (j + 1)) h1 hq0
    rw [hdiv _ (by positivity), Real.mul_rpow (by positivity) (by positivity)] at h2
    refine le_trans h2 ?_
    have hk : (2 * C₂) ^ q ≤ max 1 (2 * C₂) :=
      rpow_le_max_one (by linarith) hq0 hq1
    have hp1 : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ q := Real.rpow_nonneg (by positivity) _
    calc (2 * C₂) ^ q * ((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q)
        = (2 * C₂) ^ q * (((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q)) := by ring
      _ ≤ max 1 (2 * C₂) * (((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q)) :=
          mul_le_mul_of_nonneg_right hk (mul_nonneg hp1 hM0)
  have hKbb0 : (0 : ℝ)
      ≤ max 1 (2 * C₂) * max 1 (2 * C₂) * ((1 - q) * st) ^ (-q) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hM0
  have hsumbd : (∑ j ∈ Finset.Ico j₀ KK, ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q)
      ≤ 2 * (max 1 (2 * C₂) * max 1 (2 * C₂) * ((1 - q) * st) ^ (-q)) := by
    have hterm : ∀ j ∈ Finset.Ico j₀ KK,
        ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q
          ≤ (max 1 (2 * C₂) * max 1 (2 * C₂) * ((1 - q) * st) ^ (-q))
              * (Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
      have hA := hbadpow j hj1
      have hB := hstepbd j hj1 hj2
      have h0 : (0 : ℝ) ≤ ν.real (B j) ^ (1 - q) := Real.rpow_nonneg measureReal_nonneg _
      have h1 : (0 : ℝ) ≤ (∫ ω, RR (j + 1) ω ∂ν) ^ q :=
        Real.rpow_nonneg (hRmean0 (j + 1)) _
      have hprod := mul_le_mul hA hB h1 (by positivity)
      calc ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q
          ≤ (max 1 (2 * C₂) * Real.exp (-2 * (j : ℝ)))
              * (max 1 (2 * C₂) * (((j : ℝ) + 1) ^ q * ((1 - q) * st) ^ (-q))) := hprod
        _ = (max 1 (2 * C₂) * max 1 (2 * C₂) * ((1 - q) * st) ^ (-q))
              * (Real.exp (-2 * (j : ℝ)) * ((j : ℝ) + 1) ^ q) := by ring
    have h1 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at h1
    have h2 := sum_exp_mul_rpow_le hq1 (Finset.Ico j₀ KK)
    refine le_trans h1 ?_
    have h3 := mul_le_mul_of_nonneg_left h2 hKbb0
    linarith
  -- (c) the tail
  have htailbd : ν.real (B KK) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q
      ≤ max 1 (2 * C₂) * max 1 C₁ * ((1 - q) * st) ^ (-q) := by
    have hA : ν.real (B KK) ^ (1 - q) ≤ max 1 (2 * C₂) * Real.exp (-2 * (KK : ℝ)) :=
      hbadpow KK (Nat.le_add_right _ _)
    have hexp : Real.exp (-2 * (KK : ℝ)) ≤ ((1 - q) * st) ^ (-q) := by
      refine le_trans (Real.exp_le_exp.2 ?_) (exp_neg_two_mul_le_rpow_neg hL2 hq1)
      linarith [hKge]
    have h0 : (0 : ℝ) ≤ ν.real (B KK) ^ (1 - q) := Real.rpow_nonneg measureReal_nonneg _
    have h1 : (0 : ℝ) ≤ (∫ ω, ZZ ω ∂ν) ^ q := Real.rpow_nonneg hZmean0 _
    have hprod := mul_le_mul hA hZpow h1 (by positivity)
    calc ν.real (B KK) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q
        ≤ max 1 (2 * C₂) * Real.exp (-2 * (KK : ℝ)) * max 1 C₁ := hprod
      _ ≤ max 1 (2 * C₂) * ((1 - q) * st) ^ (-q) * max 1 C₁ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp (by linarith)) (by linarith)
      _ = max 1 (2 * C₂) * max 1 C₁ * ((1 - q) * st) ^ (-q) := by ring
  -- assemble
  have hMtar : ((1 - q) * st) ^ (-q) ≤ 3 / 2 * (1 + (1 - q) * st) ^ (-q) :=
    rpow_neg_le_target hL2 hq0 hq1
  have htar0 : (0 : ℝ) ≤ (1 + (1 - q) * st) ^ (-q) :=
    Real.rpow_nonneg (by linarith) _
  have hKbb : (0 : ℝ) ≤ max 1 (2 * C₂) * max 1 (2 * C₂) :=
    mul_nonneg (by linarith) (by linarith)
  have hKbz : (0 : ℝ) ≤ max 1 (2 * C₂) * max 1 C₁ :=
    mul_nonneg (by linarith) (by linarith)
  have hX0 : (0 : ℝ) ≤ max 1 (2 * C₂ * (max a₀ 3 + 1))
      + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁ := by
    linarith
  calc (∫ ω, ZZ ω ^ q ∂ν)
      ≤ (∫ ω, RR j₀ ω ∂ν) ^ q
        + (∑ j ∈ Finset.Ico j₀ KK, ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q)
        + ν.real (B KK) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q := hmain
    _ ≤ (max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)
        * ((1 - q) * st) ^ (-q) := by linarith [hfirst, hsumbd, htailbd]
    _ ≤ (max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)
        * (3 / 2 * (1 + (1 - q) * st) ^ (-q)) := mul_le_mul_of_nonneg_left hMtar hX0
    _ = (3 / 2 * (max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁))
        * (1 + (1 - q) * st) ^ (-q) := by ring
    _ ≤ 3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)
        * (1 + (1 - q) * st) ^ (-q) :=
        mul_le_mul_of_nonneg_right (by linarith) htar0
/-- **The interpolation, for the Steinhaus RMF.**  The `RMF.integral_rpow_le_of_goodSets` instance
at the chaos on `[0, 1)`.  The facts the abstract form asks for are the two nonnegativity lemmas,
the two integrability lemmas and `RMF.chaosUnitShift_le_decomposition`; the good-set data is
`G`'s fields, unchanged. -/
theorem integral_rpow_le_of_goodFamily {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsSteinhausPrimeValues Y ν) {x σ q : ℝ} {t n₀ : ℕ} {a₀ C₁ C₂ : ℝ}
    (hx2 : (2 : ℝ) ≤ x) (hxgt1 : (1 : ℝ) < x) (_hσ0 : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hZmean : (∫ ω, chaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν) ≤ C₁)
    (hT1 : 2 * n₀ ≤ t) (hT2 : ⌈max a₀ 3⌉₊ ^ 2 ≤ t)
    (G : GoodFamily Y ν x σ t n₀ a₀ C₂) :
    (∫ ω, chaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
      ≤ 3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
          + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)
        * (1 + (1 - q) * Real.sqrt (t : ℝ)) ^ (-q) := by
  haveI := hY.isProbabilityMeasure
  exact integral_rpow_le_of_goodSets
    (Z := chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ)
    (Rst := fun S => restrictedChaosUnitShift
      (fun ω => compMultExtension fun p => Y p ω) x σ S)
    (win := Set.Ico (0 : ℝ) 1)
    (fun ω => chaosUnitShift_nonneg hx2 ω)
    (integrable_chaosUnitShift hY x σ (by linarith))
    (fun S ω => restrictedChaosUnitShift_nonneg hxgt1 σ S ω)
    (fun S hm hu => integrable_restrictedChaosUnitShift hY x σ (by linarith) S hm hu)
    (fun S ω r m hrm => chaosUnitShift_le_decomposition hxgt1 σ S ω r m hrm)
    hq0 hq1 hC₁ hC₂ hZmean hT1 hT2
    G.set G.measurableSet G.measurableSet_uncurry G.measure_bad_le G.integral_restricted_le

/-- **The `q`-th moment of the chaos at a shifted abscissa.**  `E[(Z²)^q] ≪ (1 + (1-q)√t)^{-q}`
for the chaos at `1/2 + σ`, `t = RMF.harperBlockCount D x`, uniformly in `q ∈ [0,1]`, in `σ ≥ 0`
with `|σ|\log x ≤ η ≤ E₀`, and in `x ≥ x₀`; `D`, `x₀` and `C` depend on `E₀`.  The good set is
`RMF.harperGoodSlope` at `RMF.blockSlopeOf E₀ 125`, bounded by
`RMF.exists_const_harperGood_bounds_of_scale`.  The lower reduction reads it at `σ = 2V/\log x`,
moved to `[-1/2, 1/2]` by `RMF.integral_rpow_window_eq`. -/
theorem exists_const_integral_chaosUnitShift_rpow_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (D : ℕ) (x₀ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnitShift
              (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt (harperBlockCount D x : ℝ)) ^ (-q) := by
  obtain ⟨D, n₀, x₁, a₀, C₂, -, hC₂, H₂⟩ :=
    exists_const_harperGood_bounds_of_scale (Ω := Ω) E₀ hE₀
  obtain ⟨C₁, hC₁, H₁⟩ := exists_const_integral_chaosUnitShift_le
  obtain ⟨x₂, hx₂⟩ :=
    exists_harperThreshold_of_blockCount D (max (2 * n₀) (⌈max a₀ 3⌉₊ ^ 2))
  refine ⟨D, max (max x₁ x₂) 2,
    3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
      + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁),
    by positivity, ?_⟩
  intro Y ν hY x σ η q hx hσ0 hη0 hηE hσ hq0 hq1
  have hxa : max x₁ x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hxa
  obtain ⟨hxgt1, hDlog, hcount⟩ := hx₂ x (le_trans (le_max_right _ _) hxa)
  exact integral_rpow_le_of_goodFamily hY hx2 hxgt1 hσ0 hq0 hq1 hC₁ hC₂
    (H₁ Ω Y ν hY x σ hx2 hσ0)
    (le_trans (le_max_left _ _) hcount) (le_trans (le_max_right _ _) hcount)
    { set := fun a => harperGoodSlope Y (blockSlopeOf E₀ 125) D x σ a
      measurableSet := fun a h => measurableSet_harperGoodSlope hY _ D x σ a h
      measurableSet_uncurry := fun a =>
        measurableSet_harperGoodSlope_uncurry hY _ D x σ a
      measure_bad_le := fun a ha =>
        (H₂ Y ν hY x σ η a hxx₁ hσ0 hη0 hηE hσ ha).1
      integral_restricted_le := fun a ha h2 h3 =>
        (H₂ Y ν hY x σ η a hxx₁ hσ0 hη0 hηE hσ ha).2 (by omega) h3 }

/-- **The `q`-th moment of the chaos at `σ = 0`.**  This is
`RMF.exists_const_integral_chaosUnitShift_rpow_le` at `E₀ = 0`, where the tilt hypotheses `0 ≤ σ`,
`η ≤ E₀` and `|σ|\log x ≤ η` all read `0 ≤ 0`; the binder shape `∃ D x₀ C, ∀ Y ν` is the same, so
the constant is uniform in the same things. -/
theorem exists_const_integral_chaosUnit_rpow_le :
    ∃ (D : ℕ) (x₀ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnit (fun ω => compMultExtension fun p => Y p ω) x ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt (harperBlockCount D x : ℝ)) ^ (-q) := by
  obtain ⟨D, x₀, C, hC, H⟩ :=
    exists_const_integral_chaosUnitShift_rpow_le (Ω := Ω) 0 le_rfl
  refine ⟨D, x₀, C, hC, ?_⟩
  intro Y ν hY x q hx hq0 hq1
  have hz : |(0 : ℝ)| * Real.log x ≤ 0 := by simp
  have h := H Y ν hY x 0 0 q hx le_rfl le_rfl le_rfl hz hq0 hq1
  have heq : ∀ ω, chaosUnitShift
      (fun ω => compMultExtension fun p => Y p ω) x 0 ω
      = chaosUnit (fun ω => compMultExtension fun p => Y p ω) x ω :=
    fun ω => chaosUnitShift_zero _ _ _
  simp_rw [heq] at h
  exact h

/-- **The constant of `RMF.exists_const_integral_chaosUnitShift_rpow_le_of_top`**, written out:
one term for the first block, one for each of the good set's two bounds, one for the barrier
sum and one for the tail, all tripled by the three-way split.  `C₁` is the unrestricted first
moment's constant, `C₂` the good set's, and `a₀` its level. -/
noncomputable def chaosUnitShiftRpowConst (C₁ C₂ a₀ : ℝ) : ℝ :=
  3 * (max 1 C₁ + max 1 (2 * C₂ * (max a₀ 3 + 1))
    + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 C₁)

/-- **`RMF.exists_const_integral_chaosUnitShift_rpow_le_of_top` with its constant named.**  The
interpolation does not move the block offset `D`, and its constant is
`RMF.chaosUnitShiftRpowConst C₁ C₂ a₀` in the two sources' constants and the good set's
level. -/
theorem le_const_integral_chaosUnitShift_rpow_of_good {D n₀ : ℕ} {a₀ C₂ C₁ : ℝ}
    (hC₂ : 0 < C₂) (hC₁ : 0 < C₁)
    (H₂ :
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ (x δ η a : ℝ) (t : ℕ), t = harperBlockCount D x - d →
          x₀ ≤ x → 0 ≤ δ → 0 ≤ η → η ≤ E₀ →
          |δ| * Real.log x ≤ η → a₀ ≤ a →
          ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1,
              ω ∉ harperGoodRange Y (blockSlope 125) D x δ a t h}
              ≤ C₂ * Real.exp (-(2 * a)) ∧
            (⌈a / 4⌉₊ ≤ harperBlockCount D x → 2 * d ≤ harperBlockCount D x - ⌈a / 4⌉₊ →
              n₀ ≤ harperBlockCount D x - ⌈a / 4⌉₊ - d →
              (∫ ω, restrictedChaosUnitShift
                  (fun ω => compMultExtension fun p => Y p ω) x δ
                  (harperGoodRange Y (blockSlope 125) D x δ a t) ω ∂ν)
                ≤ C₂ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))))
    (H₁ :
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω),
      IsSteinhausPrimeValues Y ν → ∀ x σ : ℝ, 2 ≤ x → 0 ≤ σ →
        (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν)
          ≤ C₁) :
    ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
    ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
        |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
        (∫ ω, chaosUnitShift
            (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
          ≤ chaosUnitShiftRpowConst C₁ C₂ a₀
              * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ)) ^ (-q) := by
  intro d E₀ hE₀ hEd
  obtain ⟨x₁, H₂⟩ := H₂ d E₀ hE₀ hEd
  obtain ⟨x₂, hx₂⟩ :=
    exists_harperThreshold_of_blockCount D
      (max (max (2 * n₀ + d) (⌈max a₀ 3⌉₊ ^ 2 + d)) (4 * d))
  refine ⟨max (max x₁ x₂) 2, ?_⟩
  intro Y ν hY x σ η q hx hσ0 hη0 hηE hσ hq0 hq1
  have hxa : max x₁ x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hxa
  obtain ⟨hxgt1, hDlog, hcount⟩ := hx₂ x (le_trans (le_max_right _ _) hxa)
  have hdd : 4 * d ≤ harperBlockCount D x := le_trans (le_max_right _ _) hcount
  have hcl : max (2 * n₀ + d) (⌈max a₀ 3⌉₊ ^ 2 + d) ≤ harperBlockCount D x :=
    le_trans (le_max_left _ _) hcount
  have hcl1 : 2 * n₀ + d ≤ harperBlockCount D x := le_trans (le_max_left _ _) hcl
  have hcl2 : ⌈max a₀ 3⌉₊ ^ 2 + d ≤ harperBlockCount D x :=
    le_trans (le_max_right _ _) hcl
  exact integral_rpow_le_of_goodFamily hY hx2 hxgt1 hσ0 hq0 hq1 hC₁ hC₂
    (H₁ Y ν hY x σ hx2 hσ0)
    (Nat.le_sub_of_add_le hcl1) (Nat.le_sub_of_add_le hcl2)
    { set := fun a =>
        harperGoodRange Y (blockSlope 125) D x σ a (harperBlockCount D x - d)
      measurableSet := fun a h => measurableSet_harperGoodRange hY _ D x σ a _ h
      measurableSet_uncurry := fun a =>
        measurableSet_harperGoodRange_uncurry hY _ D x σ a _
      measure_bad_le := fun a ha =>
        (H₂ Y ν hY x σ η a _ rfl hxx₁ hσ0 hη0 hηE hσ ha).1
      integral_restricted_le := fun a ha h2 h3 =>
        (H₂ Y ν hY x σ η a _ rfl hxx₁ hσ0 hη0 hηE hσ ha).2
          (by omega) (by omega) (by omega) }

set_option maxHeartbeats 400000 in
-- the `GoodFamily` structure is elaborated against the drop's block count, which is what
-- costs here; the body itself is short
/-- **The `q`-th moment of the chaos at a shifted abscissa, with the top `d` blocks dropped.**
The interpolation is unchanged; what changes is the block count it is read at,
`t = RMF.harperBlockCount D x - d`, and the constants: `D` and `C` do not depend on `d` or on
`E₀ ≤ e^d`, only `x₀` does.  `RMF.exists_const_integral_chaosUnitShift_rpow_le` keeps every
block, with constants depending on `E₀`. -/
theorem exists_const_integral_chaosUnitShift_rpow_le_of_top :
    ∃ (D : ℕ) (C : ℝ), 0 < C ∧
      ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
        ∀ x σ η q : ℝ, x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 1 →
          (∫ ω, chaosUnitShift
              (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
            ≤ C * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - d : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D, n₀, a₀, C₂, -, hC₂, H₂⟩ :=
    exists_const_harperGood_bounds_of_top (Ω := Ω)
  obtain ⟨C₁, hC₁, H₁⟩ := exists_const_integral_chaosUnitShift_le
  refine ⟨D, chaosUnitShiftRpowConst C₁ C₂ a₀, ?_,
    le_const_integral_chaosUnitShift_rpow_of_good hC₂ hC₁ H₂ (H₁ Ω)⟩
  rw [chaosUnitShiftRpowConst]
  positivity

end RMF
