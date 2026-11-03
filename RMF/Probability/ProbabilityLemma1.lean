/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Anticoncentration
import RMF.Probability.CurvedBarrier
import RMF.Analysis.IteratedLog

/-!
# Probability Lemma 1: the exponent budget

Harper's inductive step splits an integral over the endpoint `u` of the first block into a middle
range `−L⁴ ≤ u ≤ a + 200 L` and a tail `u ≤ −L⁴`, where `L = log_{k+1} n`.  In the middle range he
bounds the integrand by a uniform (A1) estimate, integrates the Gaussian weight, and asserts that
the result is `≪ 1/(√n L²)`.

Two observations reduce that step to arithmetic.

**The Gaussian segment integral needs nothing new.**  What Harper writes as
`(1/(√(2π) s)) ∫_{−T}^{U} e^{−u²/2s²} du` is exactly `P(N(0,s²) ∈ [−T, U])`, and
`RMF.measure_Icc_gaussianReal_le` already bounds the mass of *any* interval by its length times the
peak density, `(U+T)/√(2π s²)` — uniformly in the position of the interval.  So no new integral
estimate is required, only the arithmetic of the exponents.

**The exponents.**  With `T = L⁴`, `U = a + 200 L`, `s ≍ L¹⁰` and the (A1) factor of size
`a + L⁴ ≍ L⁴`, the product is `L⁴ · L⁴ / L¹⁰ = L⁻²`.  This is the budget `4 + 4 − 10 = −2`, and it
is what `RMF.budget_of_le` makes explicit.  The absorption of `a` uses the standing hypothesis
`L = log_{k+1} n ≥ a/1000` of the induction; without it the `a` would not fit inside `L⁴`.

The exponents `4` and `20` are locked to one another: `s² ≍ L²⁰` forces `s ≍ L¹⁰`, and `4+4−10 = −2`
is what makes the per-level error summable.  A different split point would break the budget.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-- **The exponent budget of Harper’s inductive step**, `4 + 4 − 10 = −2`: `XY/s ≤ K₁K₂D/L²` when
`X ≤ K₁L⁴`, `Y ≤ K₂L⁴`, `s ≥ L¹⁰/D` and `L ≥ 1`.  Here `L = log_{k+1} n`, `s` is the standard
deviation of the first block and `X`, `Y` are the two factors of the middle range; Harper’s
`(a + 200L) + L⁴` and `a + L⁴` fit with `K₁ = 1201`, `K₂ = 1001` under `a ≤ 1000 L`.  The factors
are general because the one-step estimate carries the (A1) constant `A(a + 10 log L + T)`, affine
in that quantity rather than equal to it. -/
lemma budget_of_le {X Y K₁ K₂ L D s : ℝ} (hL : 1 ≤ L) (hD : 0 < D)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : X ≤ K₁ * L ^ 4) (hY : Y ≤ K₂ * L ^ 4)
    (hs : L ^ 10 / D ≤ s) :
    X * Y / s ≤ K₁ * K₂ * D / L ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL4 : (0 : ℝ) < L ^ 4 := by positivity
  have hK₁ : (0 : ℝ) ≤ K₁ := nonneg_of_mul_nonneg_left (hX0.trans hX) hL4
  have hK₂ : (0 : ℝ) ≤ K₂ := nonneg_of_mul_nonneg_left (hY0.trans hY) hL4
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
  have hDs : L ^ 10 ≤ D * s := by
    rw [div_le_iff₀ hD] at hs; linarith
  have hprod : X * Y ≤ K₁ * K₂ * L ^ 8 :=
    (mul_le_mul hX hY hY0 (mul_nonneg hK₁ hL4.le)).trans_eq (by ring)
  rw [div_le_div_iff₀ hspos (by positivity)]
  have h1 : X * Y * L ^ 2 ≤ K₁ * K₂ * L ^ 10 := by
    linarith [mul_le_mul_of_nonneg_right hprod (pow_pos hL0 2).le]
  have h3 : K₁ * K₂ * L ^ 10 ≤ K₁ * K₂ * D * s := by
    linarith [mul_le_mul_of_nonneg_left hDs (mul_nonneg hK₁ hK₂)]
  linarith

/-- **The middle term collapses.**  The (A1) factor and the window width are both `O(Λ⁴)`, the
first-block standard deviation is `≳ Λ¹⁰`, and the remaining `1/√(n−N)` is at most `√2/√n` when the
split is before the midpoint.  Budget: `4 + 4 − 10 = −2`. -/
lemma middle_term_le {A₁ Y s Λ D K₁ K₂ : ℝ} {m n : ℕ} (hΛ : 1 ≤ Λ) (hD : 0 < D)
    (hA0 : 0 ≤ A₁) (hY0 : 0 ≤ Y) (hA : A₁ ≤ K₁ * Λ ^ 4) (hY : Y ≤ K₂ * Λ ^ 4)
    (hs : Λ ^ 10 / D ≤ s) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : (n : ℝ) ≤ 2 * (m : ℝ)) :
    A₁ / √((m : ℝ)) * (Y / s) ≤ √2 * (K₁ * K₂ * D) / (Λ ^ 2 * √((n : ℝ))) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsm : (0 : ℝ) < √((m : ℝ)) := Real.sqrt_pos.2 hmR
  have hsn : (0 : ℝ) < √((n : ℝ)) := Real.sqrt_pos.2 hnR
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
  have hbud := budget_of_le hΛ hD hA0 hY0 hA hY hs
  have hprodnn : (0 : ℝ) ≤ A₁ * Y / s := by positivity
  have hKnn : (0 : ℝ) ≤ K₁ * K₂ * D := by
    simpa using (le_div_iff₀ (by positivity : (0 : ℝ) < Λ ^ 2)).1 (hprodnn.trans hbud)
  have hsq : √((n : ℝ)) ≤ √2 * √((m : ℝ)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hmn
  calc A₁ / √((m : ℝ)) * (Y / s) = (A₁ * Y / s) / √((m : ℝ)) := by ring
    _ ≤ (K₁ * K₂ * D / Λ ^ 2) / √((m : ℝ)) := by gcongr
    _ = (K₁ * K₂ * D) / (Λ ^ 2 * √((m : ℝ))) := by ring
    _ ≤ √2 * (K₁ * K₂ * D) / (Λ ^ 2 * √((n : ℝ))) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hKnn (pow_pos hΛ0 2).le)]

/-- **The tail term collapses.**  The round-trip ratio is `O(1/Λ³)` and the level-`N` probability is
`O(Λ/√n)`; their product is `O(1/(Λ²√n))`.  Budget: `3 − 1 = 2`. -/
lemma tail_term_le {ρ A₂ Λ Kρ B : ℝ} {n : ℕ} (hΛ : 1 ≤ Λ) (hn : 1 ≤ n)
    (hρ0 : 0 ≤ ρ) (hA0 : 0 ≤ A₂) (hρ : ρ ≤ Kρ / Λ ^ 3) (hA : A₂ ≤ B * Λ) :
    ρ * (A₂ / √((n : ℝ))) ≤ Kρ * B / (Λ ^ 2 * √((n : ℝ))) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √((n : ℝ)) := Real.sqrt_pos.2 hnR
  have hKρ : (0 : ℝ) ≤ Kρ := by
    simpa using (le_div_iff₀ (by positivity : (0 : ℝ) < Λ ^ 3)).1 (hρ0.trans hρ)
  have hB : (0 : ℝ) ≤ B := nonneg_of_mul_nonneg_left (hA0.trans hA) hΛ0
  calc ρ * (A₂ / √((n : ℝ)))
      ≤ (Kρ / Λ ^ 3) * (B * Λ / √((n : ℝ))) := by
        refine mul_le_mul hρ (by gcongr) (by positivity) (by positivity)
    _ = Kρ * B / (Λ ^ 2 * √((n : ℝ))) := by field_simp

/-! ### Why the errors add rather than compound

This is the one piece of Harper’s induction that cannot be paraphrased.  Each level contributes an
absolute error of size `L/√n` from (A2) — far too big, since the whole quantity being estimated is
itself only of size `L/√n`, and `log* n` such errors would swamp it.  The fix is a round trip.

**Additive → multiplicative.**  In the tail range `u ≤ −L⁴` the suffix barrier is everywhere at
least `L⁴`, so by (A1) *lower* the surviving probability is `≫ L⁴/√n`.  An absolute error of
`L/√n` against `L⁴/√n` is a *relative* error of `1/L³`, Harper's "crucial point".

**Multiplicative → additive.**  The relative error then multiplies the whole level-`(k+1)`
probability, which by (A1) *upper* — via the constant-barrier sandwich — is itself `≪ L/√n`.  So the
recombined absolute error is `(1/L³)·(L/√n) = 1/(L²√n)`, summable over the iterated-logarithm scale:
an error measured against `sup_u Φ(u)` becomes one measured against the *integrated* `Q`. -/

/-- **Additive to multiplicative** — Harper’s "crucial point".  An absolute error `ε` on a quantity
that is itself at least `δ` is a relative error of at most `ε/δ`. -/
lemma abs_sub_le_relative {P P' ε δ : ℝ} (hδ : 0 < δ) (hδP : δ ≤ P') (h : |P - P'| ≤ ε) :
    |P - P'| ≤ (ε / δ) * P' := by
  have hε0 : (0 : ℝ) ≤ ε := le_trans (abs_nonneg _) h
  calc |P - P'| ≤ ε := h
    _ = (ε / δ) * δ := by field_simp
    _ ≤ (ε / δ) * P' := mul_le_mul_of_nonneg_left hδP (div_nonneg hε0 hδ.le)

/-! ### The telescope

Once the one-step estimate holds at every level, the lemma follows by the triangle inequality along
the chain of freeze points.  This is the only place the individual errors are summed, and it is
where `RMF.sum_inv_sq_iterLog_le` enters. -/

/-- **Telescoping.**  A chain of one-step bounds gives a bound on the total displacement. -/
lemma abs_sub_telescope {f e : ℕ → ℝ} {k : ℕ} (h : ∀ i < k, |f i - f (i + 1)| ≤ e i) :
    |f 0 - f k| ≤ ∑ i ∈ Finset.range k, e i := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := h k (Nat.lt_succ_self k)
      have hprev := ih fun i hi => h i (hi.trans (Nat.lt_succ_self k))
      rw [Finset.sum_range_succ]
      calc |f 0 - f (k + 1)| = |(f 0 - f k) + (f k - f (k + 1))| := by congr 1; ring
        _ ≤ |f 0 - f k| + |f k - f (k + 1)| := abs_add_le _ _
        _ ≤ (∑ i ∈ Finset.range k, e i) + e k := add_le_add hprev hk

/-- The accumulated error over levels `1..k`, dropping the level-`0` term. -/
lemma sum_inv_sq_iterLog_succ_le {k : ℕ} {x : ℝ} (h : IterLogGood k x) :
    ∑ i ∈ Finset.range k, 1 / iterLog (i + 1) x ^ 2
      ≤ (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ / iterLog k x ^ 2 := by
  refine le_trans ?_ (sum_inv_sq_iterLog_le h)
  rw [Finset.sum_range_succ' (fun i => 1 / iterLog i x ^ 2) k]
  have h0 : (0 : ℝ) ≤ 1 / iterLog 0 x ^ 2 := by positivity
  linarith

/-- **The accumulated error of the induction.**  If the one-step estimate holds at every level with
error `C/(R · log_{i+1}² n)`, the total displacement is at most a constant times the last term — the
sum does not accumulate over the `log*` many levels. -/
lemma abs_sub_telescope_iterLog {f : ℕ → ℝ} {C R x : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hR : 0 < R) (hgood : IterLogGood k x)
    (h : ∀ i < k, |f i - f (i + 1)| ≤ C / (R * iterLog (i + 1) x ^ 2)) :
    |f 0 - f k| ≤ C * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ / (R * iterLog k x ^ 2) := by
  have htk : 1 ≤ iterLog k x := hgood.one_le le_rfl
  have htk0 : iterLog k x ≠ 0 := by intro hc; rw [hc] at htk; linarith
  refine le_trans (abs_sub_telescope h) ?_
  have hrw : ∀ i ∈ Finset.range k,
      C / (R * iterLog (i + 1) x ^ 2) = (C / R) * (1 / iterLog (i + 1) x ^ 2) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  calc (C / R) * ∑ i ∈ Finset.range k, 1 / iterLog (i + 1) x ^ 2
      ≤ (C / R) * ((1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ / iterLog k x ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_iterLog_succ_le hgood) (div_nonneg hC hR.le)
    _ = C * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ / (R * iterLog k x ^ 2) := by ring

/-! ### The prefix/suffix split

Harper writes the inductive step as an integral over the value `u` of the first block sum, against
the Gaussian density of that sum.  Read literally that is a *conditioning* on `{S_N = u}`, which
would need a disintegration.  It is not necessary, and the reason is worth recording: the barrier
for the suffix depends on the prefix **only through the endpoint** `S_N`, and `S_N` is a real random
variable independent of the whole suffix path.  So the split is Fubini on a product law, exactly the
pattern of `RMF.measure_add_mem_Icc_le_of_indepFun`, with no conditional measures anywhere.

The truncation of the `u`-range is then automatic rather than a separate argument: `u` is confined
to the set `A` by the prefix constraint, and taking `A = (-∞, β_N]` is Harper's cutoff at
`a + 200 log_{k+2} n`, since the barrier at time `N = (log_{k+1} n)^{20}` has exactly that
height. -/

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

/-- **The prefix/suffix split, as Fubini.**  For a measurable statistic `T` of the prefix path,
a set `A` of its values and suffix-path sets `E t`,
`P(T(prefix) ∈ A, suffix ∈ E(T(prefix))) = ∫_{t ∈ A} P(suffix ∈ E t) dLaw(T(prefix))(t)`.
No conditional measure appears: prefix and suffix block are independent, so this is
`Measure.prod_apply` on the product of their laws.  Restricting to `A` carries Harper's truncation
of the `u`-range; `T = id` is used here, and Probability Result 2 uses `T = (· N)`. -/
theorem IsGaussianWalk.measure_stat_inter_block {α : Type*} [MeasurableSpace α]
    (h : IsGaussianWalk G v μ) (N n : ℕ) {T : (ℕ → ℝ) → α} (hT : Measurable T)
    {A : Set α} (hA : MeasurableSet A) {E : α → Set (ℕ → ℝ)}
    (hE : MeasurableSet {p : α × (ℕ → ℝ) | p.2 ∈ E p.1}) :
    μ ({ω | T (prefixSums N fun i => G i ω) ∈ A} ∩
        {ω | (blockSums N n fun i => G i ω) ∈ E (T (prefixSums N fun i => G i ω))})
      = ∫⁻ t in A, μ {ω | (blockSums N n fun i => G i ω) ∈ E t}
          ∂(μ.map fun ω => T (prefixSums N fun i => G i ω)) := by
  classical
  have hmP : Measurable fun ω => prefixSums N fun i => G i ω :=
    (measurable_prefixSums N).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hmT : Measurable fun ω => T (prefixSums N fun i => G i ω) := hT.comp hmP
  have hmB : Measurable fun ω => blockSums N n fun i => G i ω :=
    (measurable_blockSums N n).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hind : IndepFun (fun ω => T (prefixSums N fun i => G i ω))
      (fun ω => blockSums N n fun i => G i ω) μ :=
    (h.indepFun_prefixSums_blockSums N n).comp hT measurable_id
  set S : Set (α × (ℕ → ℝ)) := {p | p.1 ∈ A} ∩ {p | p.2 ∈ E p.1} with hSdef
  have hS : MeasurableSet S := (hA.preimage measurable_fst).inter hE
  have hset : {ω | T (prefixSums N fun i => G i ω) ∈ A} ∩
      {ω | (blockSums N n fun i => G i ω) ∈ E (T (prefixSums N fun i => G i ω))}
      = (fun ω => (T (prefixSums N fun i => G i ω), blockSums N n fun i => G i ω)) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply (hmT.prodMk hmB) hS,
    hind.map_prod_eq_prod_map_map hmT.aemeasurable hmB.aemeasurable, Measure.prod_apply hS]
  have hslice : ∀ t : α,
      (μ.map fun ω => blockSums N n fun i => G i ω) (Prod.mk t ⁻¹' S)
        = A.indicator (fun t => μ {ω | (blockSums N n fun i => G i ω) ∈ E t}) t := by
    intro t
    by_cases ht : t ∈ A
    · have hEt : MeasurableSet (E t) := hE.preimage measurable_prodMk_left
      have hpre : Prod.mk t ⁻¹' S = E t := by
        ext y
        simp only [hSdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, ht, true_and]
      rw [hpre, Set.indicator_of_mem ht, Measure.map_apply hmB hEt]
      rfl
    · have hpre : Prod.mk t ⁻¹' S = ∅ := by
        ext y
        simp only [hSdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, ht,
          false_and, Set.mem_empty_iff_false]
      rw [hpre, Set.indicator_of_notMem ht, measure_empty]
  simp_rw [hslice]
  rw [lintegral_indicator hA (fun t => μ {ω | (blockSums N n fun i => G i ω) ∈ E t})]

/-- **The whole-path instance**, `T = id`.  This is the form the tail range needs: the prefix event
is retained, because the relative error of the round trip is measured against it. -/
theorem IsGaussianWalk.measure_prefix_inter_block (h : IsGaussianWalk G v μ) (N n : ℕ)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) {E : (ℕ → ℝ) → Set (ℕ → ℝ)}
    (hE : MeasurableSet {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 ∈ E p.1}) :
    μ ({ω | (prefixSums N fun i => G i ω) ∈ A} ∩
        {ω | (blockSums N n fun i => G i ω) ∈ E (prefixSums N fun i => G i ω)})
      = ∫⁻ x in A, μ {ω | (blockSums N n fun i => G i ω) ∈ E x}
          ∂(μ.map fun ω => prefixSums N fun i => G i ω) :=
  h.measure_stat_inter_block N n measurable_id hA hE

/-- **The endpoint instance**, `T = (· N)`.  The prefix enters only through `S_N`, so the measure
integrated against is the one-dimensional law of `S_N` — a genuine Gaussian on `ℝ`, which is what
makes the absolute-moment bounds of `RMF/Probability/GaussianEstimates.lean` applicable.  This is
the form Probability Result 2 uses. -/
theorem IsGaussianWalk.measure_endpoint_inter_block (h : IsGaussianWalk G v μ) (N n : ℕ)
    {A : Set ℝ} (hA : MeasurableSet A) {E : ℝ → Set (ℕ → ℝ)}
    (hE : MeasurableSet {p : ℝ × (ℕ → ℝ) | p.2 ∈ E p.1}) :
    μ ({ω | walk G N ω ∈ A} ∩ {ω | (blockSums N n fun i => G i ω) ∈ E (walk G N ω)})
      = ∫⁻ u in A, μ {ω | (blockSums N n fun i => G i ω) ∈ E u} ∂(μ.map (walk G N)) := by
  have hrw : (fun ω => (fun x : ℕ → ℝ => x N) (prefixSums N fun i => G i ω)) = walk G N :=
    funext fun ω => prefixSums_comp G le_rfl ω
  have key := h.measure_stat_inter_block N n (T := fun x : ℕ → ℝ => x N)
    (measurable_pi_apply N) hA hE
  rw [hrw] at key
  have hs1 : {ω | walk G N ω ∈ A} = {ω | prefixSums N (fun i => G i ω) N ∈ A} := by
    ext ω
    simp only [Set.mem_setOf_eq, prefixSums_comp G (le_refl N) ω]
  have hs2 : {ω | (blockSums N n fun i => G i ω) ∈ E (walk G N ω)}
      = {ω | (blockSums N n fun i => G i ω) ∈ E (prefixSums N (fun i => G i ω) N)} := by
    ext ω
    simp only [Set.mem_setOf_eq, prefixSums_comp G (le_refl N) ω]
  rw [hs1, hs2]
  exact key

/-! ### The split, for an arbitrary barrier

Everything from here to the one-step comparison depends on the barrier only through an **envelope**:
that the two levels agree on the prefix range, that the lower level is constant past the split time,
and that the other sits in a band around it.  Nothing is monotone, and no inclusion between the two
curved-barrier events is ever used.

This is what lets the *downward* barrier `a − 10 log(min{j,L})`, which Probability Result 1’s lower
bound needs, use the same development: under it the two levels exchange roles, and phrased in terms
of the band it is the same argument with different numbers.
-/

/-- The prefix half of a barrier event, for an arbitrary barrier. -/
def prefixSet (β : ℕ → ℝ) (N : ℕ) : Set (ℕ → ℝ) :=
  {x | ∀ j ≤ N, x j ≤ β j}

/-- The suffix half, displaced by the prefix endpoint `x N`. -/
def suffixSet (β : ℕ → ℝ) (N n : ℕ) (x : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {y | ∀ j, N < j → j ≤ n → y j ≤ β j - x N}

omit [MeasurableSpace Ω] in
/-- **The barrier event, split at time `N`**, for an arbitrary barrier. -/
lemma barrier_event_eq (G : ℕ → Ω → ℝ) (β : ℕ → ℝ) {N n : ℕ} (hNn : N ≤ n) :
    {ω | ∀ j ≤ n, walk G j ω ≤ β j}
      = {ω | (prefixSums N fun i => G i ω) ∈ prefixSet β N}
          ∩ {ω | (blockSums N n fun i => G i ω)
              ∈ suffixSet β N n (prefixSums N fun i => G i ω)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, prefixSet, suffixSet]
  constructor
  · intro hf
    refine ⟨fun j hj => ?_, fun j hNj hjn => ?_⟩
    · rw [prefixSums_comp G hj ω]
      exact hf j (hj.trans hNn)
    · rw [blockSums_comp G hNj.le hjn ω, prefixSums_comp G (le_refl N) ω]
      linarith [hf j hjn]
  · rintro ⟨hpre, hsuf⟩ j hjn
    rcases le_or_gt j N with hj | hj
    · have := hpre j hj
      rwa [prefixSums_comp G hj ω] at this
    · have := hsuf j hj hjn
      rw [blockSums_comp G hj.le hjn ω, prefixSums_comp G (le_refl N) ω] at this
      linarith

/-- **The prefix condition sees only the prefix range.**  This is why the tail term recombines into
the other level’s probability rather than into something new. -/
lemma prefixSet_congr {β β' : ℕ → ℝ} {N : ℕ} (hagree : ∀ j ≤ N, β j = β' j) :
    prefixSet β N = prefixSet β' N := by
  ext x
  simp only [prefixSet, Set.mem_setOf_eq]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [hagree j hj]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Above.**  If the barrier is at most `chi` past the split time, the suffix event sits inside a
constant-barrier event at height `chi - u` for the shifted walk.  The hypothesis `u ≤ chi` is needed
only for the index `i = 0`, where the shifted walk sits at `0`. -/
lemma suffix_subset_const {β : ℕ → ℝ} {chi u : ℝ} {N n : ℕ}
    (hβ : ∀ j, N < j → β j ≤ chi) (hu : u ≤ chi) :
    {ω | ∀ j, N < j → j ≤ n → walk G j ω - walk G N ω ≤ β j - u}
      ⊆ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ chi - u} := by
  intro ω hω i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    simpa [walk] using by linarith
  · have hj : N < N + i := by omega
    have := hω (N + i) hj (by omega)
    rw [walk_shift]
    linarith [hβ (N + i) hj]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The suffix event is a barrier event for the shifted walk**, exactly — with the barrier read
at the *original* indices `N + i` and displaced by the prefix endpoint `x N`.  Unlike
`RMF.suffixSet_const_eq` the barrier need not be constant, and restricting to `1 ≤ i` removes the
side condition at `i = 0`.  This is the form Probability Result 1 consumes: its event is indexed by
`1 ≤ i ≤ m`, and the perturbation it sees at its own step `i` is `β (N + i)`. -/
lemma suffixSet_eq_shift (G : ℕ → Ω → ℝ) (β : ℕ → ℝ) {N n : ℕ} (x : ℕ → ℝ) :
    {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
      = {ω | ∀ i, 1 ≤ i → i ≤ n - N →
          walk (fun m => G (m + N)) i ω ≤ β (N + i) - x N} := by
  ext ω
  simp only [suffixSet, Set.mem_setOf_eq]
  constructor
  · intro hf i hi1 hi
    have hj : N < N + i := by omega
    have := hf (N + i) hj (by omega)
    rw [blockSums_comp G hj.le (by omega) ω] at this
    rw [walk_shift]
    linarith
  · intro hg j hNj hjn
    have hi := hg (j - N) (by omega) (by omega)
    rw [walk_shift, show N + (j - N) = j from by omega] at hi
    rw [blockSums_comp G hNj.le hjn ω]
    linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Below.**  If the barrier is at least `clo` past the split time, a constant-barrier event at
height `clo - u` for the shifted walk sits inside the suffix event. -/
lemma const_subset_suffix {β : ℕ → ℝ} {clo u : ℝ} {N n : ℕ}
    (hβ : ∀ j, N < j → clo ≤ β j) :
    {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ clo - u}
      ⊆ {ω | ∀ j, N < j → j ≤ n → walk G j ω - walk G N ω ≤ β j - u} := by
  intro ω hω j hNj hjn
  have hi : j - N ≤ n - N := by omega
  have := hω (j - N) hi
  rw [walk_shift, show N + (j - N) = j from by omega] at this
  linarith [hβ j hNj]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **A barrier constant past the split time gives a constant-barrier suffix event**, exactly — not
merely a containment.  That is what lets the round trip, which is stated for two constant barriers,
apply to it. -/
lemma suffixSet_const_eq (G : ℕ → Ω → ℝ) {β : ℕ → ℝ} {c : ℝ} {N n : ℕ}
    (hβ : ∀ j, N < j → β j = c) {x : ℕ → ℝ} (hx : x N ≤ c) :
    {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
      = {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ c - x N} := by
  ext ω
  simp only [suffixSet, Set.mem_setOf_eq]
  constructor
  · intro hf i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      simpa [walk] using by linarith
    · have hj : N < N + i := by omega
      have := hf (N + i) hj (by omega)
      rw [blockSums_comp G hj.le (by omega) ω, hβ (N + i) hj] at this
      rw [walk_shift]
      linarith
  · intro hg j hNj hjn
    have hi : j - N ≤ n - N := by omega
    have := hg (j - N) hi
    rw [walk_shift, show N + (j - N) = j from by omega] at this
    rw [blockSums_comp G hNj.le hjn ω, hβ j hNj]
    linarith

lemma measurableSet_prefixSet (β : ℕ → ℝ) (N : ℕ) : MeasurableSet (prefixSet β N) := by
  have hrw : prefixSet β N = ⋂ j ∈ Set.Iic N, {x : ℕ → ℝ | x j ≤ β j} := by
    ext x
    simp only [prefixSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Iic]
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (measurable_pi_apply j) measurable_const

lemma measurableSet_suffixSet (β : ℕ → ℝ) (N n : ℕ) :
    MeasurableSet {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 ∈ suffixSet β N n p.1} := by
  have hrw : {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 ∈ suffixSet β N n p.1}
      = ⋂ j ∈ Set.Ioc N n, {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 j ≤ β j - p.1 N} := by
    ext p
    simp only [suffixSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Ioc]
    exact ⟨fun hf j hj => hf j hj.1 hj.2, fun hf j h1 h2 => hf j ⟨h1, h2⟩⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_
  exact measurableSet_le ((measurable_pi_apply j).comp measurable_snd)
    (measurable_const.sub ((measurable_pi_apply N).comp measurable_fst))

/-- The prefix half of the barrier event. -/
def prefixBarrierSet (a L : ℝ) (N : ℕ) : Set (ℕ → ℝ) :=
  {x | ∀ j ≤ N, x j ≤ frozenBarrier a L j}

/-- The suffix half, with the barrier displaced by the prefix endpoint `x N`. -/
def suffixBarrierSet (a L : ℝ) (N n : ℕ) (x : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {y | ∀ j, N < j → j ≤ n → y j ≤ frozenBarrier a L j - x N}

omit [MeasurableSpace Ω] in
/-- **The barrier event, split at time `N`.** -/
lemma frozenBarrier_event_eq (G : ℕ → Ω → ℝ) (a L : ℝ) {N n : ℕ} (hNn : N ≤ n) :
    {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a L j}
      = {ω | (prefixSums N fun i => G i ω) ∈ prefixBarrierSet a L N}
          ∩ {ω | (blockSums N n fun i => G i ω)
              ∈ suffixBarrierSet a L N n (prefixSums N fun i => G i ω)} :=
  barrier_event_eq G (frozenBarrier a L) hNn

/-- **The prefix condition does not see the freeze point**, as long as the split time is at or
before it.  This is why the tail term recombines into the level-`L'` probability. -/
lemma prefixBarrierSet_congr {a L L' : ℝ} {N : ℕ} (hN : (N : ℝ) ≤ L') (hLL : L' ≤ L) :
    prefixBarrierSet a L N = prefixBarrierSet a L' N :=
  prefixSet_congr fun j hj => by
    have hjL' : (j : ℝ) ≤ L' := le_trans (by exact_mod_cast hj) hN
    rw [frozenBarrier_of_le (le_trans hjL' hLL), frozenBarrier_of_le hjL']

/-! ### The middle range of the one-step estimate

On the part of the prefix event where the endpoint exceeds `-T`, the suffix probability admits a
bound that is **uniform in the prefix path**: the barrier for the shifted walk is
`β_{a,L}(j) - u ≤ a + 10 log L + T`, a constant, so (A1) applies with a constant that does not
depend on `u`.  The contribution is therefore that bound times the mass of the prefix event, and no
integration beyond `∫_A c = c·ν(A)` is required. -/

/-- The family of suffix-barrier sets is jointly measurable. -/
lemma measurableSet_suffixBarrierSet (a L : ℝ) (N n : ℕ) :
    MeasurableSet {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 ∈ suffixBarrierSet a L N n p.1} :=
  measurableSet_suffixSet (frozenBarrier a L) N n

/-- **The middle range, for an arbitrary barrier.**  If the barrier is at most `chi` from the split
time on, then uniformly over prefix paths in `A` the suffix probability is at most
`A(chi + T)/√(n-N)`, so the joint probability is that times the mass of `A`.

The bound is uniform in the path because the suffix barrier `β j - x_N` is at most the *constant*
`chi + T` there — above by `chi`, below by the split `x_N > -T`. -/
theorem IsGaussianWalk.measure_prefixSet_inter_suffixSet_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {β : ℕ → ℝ} {chi T : ℝ} {N n : ℕ}
    (hβ : ∀ j, N ≤ j → β j ≤ chi)
    (hnN : 1 ≤ n - N) {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    (hAsub : A ⊆ prefixSet β N ∩ {x | -T < x N}) :
    μ ({ω | (prefixSums N fun i => G i ω) ∈ A}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixSet β N n (prefixSums N fun i => G i ω)})
      ≤ ENNReal.ofReal (barrierConst vmin vmax (chi + T) / √((n - N : ℕ) : ℝ))
          * μ {ω | (prefixSums N fun i => G i ω) ∈ A} := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  have hmP : Measurable fun ω => prefixSums N fun i => G i ω :=
    (measurable_prefixSums N).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hpt : ∀ x ∈ A, μ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
      ≤ ENNReal.ofReal (barrierConst vmin vmax (chi + T) / √((n - N : ℕ) : ℝ)) := by
    intro x hx
    obtain ⟨hxP, hxT⟩ := hAsub hx
    simp only [Set.mem_setOf_eq] at hxT
    have hxN : x N ≤ chi := le_trans (hxP N le_rfl) (hβ N le_rfl)
    have hc0 : (0 : ℝ) ≤ chi - x N := by linarith
    have hset : {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
        = {ω | ∀ j, N < j → j ≤ n → walk G j ω - walk G N ω ≤ β j - x N} := by
      ext ω
      simp only [suffixSet, Set.mem_setOf_eq]
      exact forall_congr' fun j => forall_congr' fun h1 => forall_congr' fun h2 => by
        rw [blockSums_comp G h1.le h2 ω]
    rw [hset]
    refine le_trans (measure_mono (suffix_subset_const (fun j hj => hβ j hj.le) hxN)) ?_
    have hbp := (h.shift N).barrierProb_le_of_comparable_mgf hc0 ⟨hvmin, fun i => hlo (i + N), fun i
      => hhi (i + N)⟩
      hnN
    have hmono : barrierConst vmin vmax (chi - x N) ≤ barrierConst vmin vmax (chi + T) :=
      barrierConst_mono hvmin (by linarith)
    have hnR : (0 : ℝ) < √((n - N : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnN)
    have hCnn : (0 : ℝ) ≤ barrierConst vmin vmax (chi + T) / √((n - N : ℕ) : ℝ) :=
      div_nonneg (barrierConst_nonneg hvmin (by linarith)) hnR.le
    refine ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hCnn |>.2 ?_
    calc (μ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ chi - x N}).toReal
        = barrierProb μ (fun m => G (m + N)) (chi - x N) (n - N) := rfl
      _ ≤ barrierConst vmin vmax (chi - x N) / √((n - N : ℕ) : ℝ) := hbp
      _ ≤ barrierConst vmin vmax (chi + T) / √((n - N : ℕ) : ℝ) := by gcongr
  have hpre : {ω | (prefixSums N fun i => G i ω) ∈ A}
      = (fun ω => prefixSums N fun i => G i ω) ⁻¹' A := rfl
  rw [h.measure_prefix_inter_block N n hA (measurableSet_suffixSet β N n), hpre,
    ← Measure.map_apply hmP hA]
  calc ∫⁻ x in A, μ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
        ∂(μ.map fun ω => prefixSums N fun i => G i ω)
      ≤ ∫⁻ _ in A, ENNReal.ofReal
          (barrierConst vmin vmax (chi + T) / √((n - N : ℕ) : ℝ))
          ∂(μ.map fun ω => prefixSums N fun i => G i ω) := by
        refine setLIntegral_mono measurable_const ?_
        intro x hx
        exact hpt x hx
    _ = _ := by rw [setLIntegral_const]

/-- **The middle range.**  Uniformly over the prefix paths in `A`, the suffix probability is at most
`A(a + 10 log L + T)/√(n-N)`; hence the joint probability is that times the mass of `A`. -/
theorem IsGaussianWalk.measure_prefix_inter_suffix_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a L T : ℝ} (hL : 1 ≤ L)
    {N n : ℕ} (hnN : 1 ≤ n - N) {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    (hAsub : A ⊆ prefixBarrierSet a L N ∩ {x | -T < x N}) :
    μ ({ω | (prefixSums N fun i => G i ω) ∈ A}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixBarrierSet a L N n (prefixSums N fun i => G i ω)})
      ≤ ENNReal.ofReal (barrierConst vmin vmax (a + 10 * Real.log L + T) / √((n - N : ℕ) : ℝ))
          * μ {ω | (prefixSums N fun i => G i ω) ∈ A} :=
  h.measure_prefixSet_inter_suffixSet_le hv
    (fun j _ => frozenBarrier_le_const hL j) hnN hA hAsub

/-! ### (A2) in barrier form

Probability Lemma 1 does not use (A2) as a statement about the running maximum; it uses it to
compare two barrier probabilities whose barriers differ by `c`.  The translation is exact: the
difference of the two barrier events **is** the window event of (A2),

`{ S_j ≤ b+c ∀ j≤n } ∖ { S_j ≤ b ∀ j≤n }  =  { b < max_{j≤n} S_j ≤ b+c }`,

which is also why the half-open form of (A2) is the right one. -/

/-- **(A2), in barrier form.**  The barrier probability is Lipschitz in the barrier height, with
constant `K/√n`. -/
theorem IsGaussianWalk.barrierProb_sub_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    barrierProb μ G (b + c) n - barrierProb μ G b n
      ≤ maxWindowConst vmin vmax c / √(n : ℝ) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  set Eb := {ω | ∀ j ≤ n, walk G j ω ≤ b} with hEb
  set Ec := {ω | ∀ j ≤ n, walk G j ω ≤ b + c} with hEc
  have hmb : MeasurableSet Eb := h.measurableSet_forall_le b n
  have hsub : Eb ⊆ Ec := fun ω hω j hj => (hω j hj).trans (by linarith)
  -- the difference of the two barrier events is exactly the window event of (A2)
  have hc1 : {ω | ∃ j ≤ n, b < walk G j ω} = Ebᶜ := by
    ext ω
    rw [Set.mem_compl_iff, hEb, Set.mem_setOf_eq, Set.mem_setOf_eq]
    push Not
    rfl
  have hc2 : {ω | ∃ j ≤ n, b + c < walk G j ω} = Ecᶜ := by
    ext ω
    rw [Set.mem_compl_iff, hEc, Set.mem_setOf_eq, Set.mem_setOf_eq]
    push Not
    rfl
  have hdiff : Ec \ Eb
      = {ω | ∃ j ≤ n, b < walk G j ω} \ {ω | ∃ j ≤ n, b + c < walk G j ω} := by
    rw [hc1, hc2, Set.sdiff_eq, Set.sdiff_eq, compl_compl]
    exact Set.inter_comm _ _
  have hmeas : μ (Ec \ Eb) = μ Ec - μ Eb :=
    measure_sdiff hsub hmb.nullMeasurableSet (by finiteness)
  have hkey : barrierProb μ G (b + c) n - barrierProb μ G b n = (μ (Ec \ Eb)).toReal := by
    rw [hmeas, barrierProb, barrierProb,
      ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]
  rw [hkey, hdiff]
  exact h.measure_max_mem_Ioc_le ⟨hvmin, hlo, hhi⟩ b hc hn

/-! ### (A1) lower, with a constant uniform over walks

`RMF.IsGaussianWalk.le_barrierProb` is explicit but carries a factor `exp(-c²/2V)`, which decays
once the barrier exceeds the standard deviation.  The tail range applies the bound to every shifted
walk and needs a constant that does not depend on the walk, so the barrier is kept below `√V`;
there the exponential is at least `e^{-1/2}`. -/

/-- **(A1) lower, uniform.**  For `0 ≤ c ≤ √(n v₋)`,
`barrierProb ≥ 2c e^{-1/2}/√(2π n v₊)`, a constant depending only on the variance bounds. -/
theorem IsGaussianWalk.explicit_le_barrierProb (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) (hcn : c ≤ √((n : ℝ) * vmin)) :
    2 * c * Real.exp (-(1 : ℝ) / 2) / √(2 * π * ((n : ℝ) * vmax)) ≤ barrierProb μ G c n := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set V : ℝ := ((∑ m ∈ Finset.range n, v m : ℝ≥0) : ℝ) with hVdef
  have hVlo : (n : ℝ) * vmin ≤ V := by
    rw [hVdef]
    push_cast
    calc (n : ℝ) * vmin = ∑ _m ∈ Finset.range n, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.range n, (v m : ℝ) := Finset.sum_le_sum fun m _ => hlo m
  have hVhi : V ≤ (n : ℝ) * vmax := by
    rw [hVdef]
    push_cast
    calc ∑ m ∈ Finset.range n, (v m : ℝ) ≤ ∑ _m ∈ Finset.range n, vmax :=
          Finset.sum_le_sum fun m _ => hhi m
      _ = (n : ℝ) * vmax := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le (by positivity) hVlo
  have hne : (∑ m ∈ Finset.range n, v m) ≠ 0 := by
    intro hcon
    rw [hVdef, hcon] at hVpos
    simp at hVpos
  -- the exponential is at least `e^{-1/2}` because `c² ≤ n v₋ ≤ V`
  have hcsq : c ^ 2 ≤ V := ((Real.le_sqrt hc (by positivity)).1 hcn).trans hVlo
  have hexp : Real.exp (-(1 : ℝ) / 2) ≤ Real.exp (-c ^ 2 / (2 * V)) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hsqrt : √(2 * π * V) ≤ √(2 * π * ((n : ℝ) * vmax)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hVhi (by positivity))
  have hsqpos : (0 : ℝ) < √(2 * π * V) := Real.sqrt_pos.2 (by positivity)
  refine le_trans ?_ (h.le_barrierProb hne hc)
  rw [← hVdef]
  gcongr

/-- **(A1) lower, uniform, with the exponential kept.**  `RMF.IsGaussianWalk.le_barrierProb`
gives `2c\,e^{-c²/2V}/√(2πV)` at the walk's own variance `V`;
`RMF.IsGaussianWalk.explicit_le_barrierProb` then caps the exponential at `e^{-1/2}`, which is
what the tail range needs but which costs a factor `e^{1/2} = 1.65` when `c ≪ √n`.

Here the exponent is bounded by `n v₋ ≤ V` instead, so the bound is
`2c\,e^{-c²/(2nv₋)}/√(2πnv₊)`: never worse, and it drops the hypothesis `c ≤ √(nv₋)`.  At the
small barrier levels the chaos numerator uses, the exponential is essentially `1`. -/
theorem IsGaussianWalk.explicit_le_barrierProb_exp (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    2 * c * Real.exp (-c ^ 2 / (2 * ((n : ℝ) * vmin))) / √(2 * π * ((n : ℝ) * vmax))
      ≤ barrierProb μ G c n := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set V : ℝ := ((∑ m ∈ Finset.range n, v m : ℝ≥0) : ℝ) with hVdef
  have hVlo : (n : ℝ) * vmin ≤ V := by
    rw [hVdef]
    push_cast
    calc (n : ℝ) * vmin = ∑ _m ∈ Finset.range n, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.range n, (v m : ℝ) := Finset.sum_le_sum fun m _ => hlo m
  have hVhi : V ≤ (n : ℝ) * vmax := by
    rw [hVdef]
    push_cast
    calc ∑ m ∈ Finset.range n, (v m : ℝ) ≤ ∑ _m ∈ Finset.range n, vmax :=
          Finset.sum_le_sum fun m _ => hhi m
      _ = (n : ℝ) * vmax := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnv : (0 : ℝ) < (n : ℝ) * vmin := by positivity
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le hnv hVlo
  have hne : (∑ m ∈ Finset.range n, v m) ≠ 0 := by
    intro hcon
    rw [hVdef, hcon] at hVpos
    simp at hVpos
  have hexp : Real.exp (-c ^ 2 / (2 * ((n : ℝ) * vmin))) ≤ Real.exp (-c ^ 2 / (2 * V)) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg c, hVlo, hnv]
  have hsqrt : √(2 * π * V) ≤ √(2 * π * ((n : ℝ) * vmax)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hVhi (by positivity))
  have hsqpos : (0 : ℝ) < √(2 * π * V) := Real.sqrt_pos.2 (by positivity)
  refine le_trans ?_ (h.le_barrierProb hne hc)
  rw [← hVdef]
  gcongr

/-- **The reflection lower bound, uniform and at a barrier of either sign.**  The form the
start-law averaging of the chaos numerator consumes: no sign condition on `c`, the exponential
kept (`RMF.IsGaussianWalk.explicit_le_barrierProb_exp`) and the variance bracket's own upper
bound in the denominator. -/
theorem IsGaussianWalk.explicit_le_barrierProb_posPart (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) (c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    2 * max c 0 * Real.exp (-(max c 0) ^ 2 / (2 * ((n : ℝ) * vmin)))
        / √(2 * π * ((n : ℝ) * vmax))
      ≤ barrierProb μ G c n := by
  rcases le_or_gt 0 c with hc | hc
  · rw [max_eq_left hc]
    exact h.explicit_le_barrierProb_exp hv hc hn
  · rw [max_eq_right hc.le]
    simp only [mul_zero, zero_mul, zero_div]
    exact ENNReal.toReal_nonneg

/-- The uniform reflection lower bound as a function of the barrier level, at either sign. -/
noncomputable def ballotLower (vmin vmax : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  2 * max c 0 * Real.exp (-(max c 0) ^ 2 / (2 * ((n : ℝ) * vmin)))
    / √(2 * π * ((n : ℝ) * vmax))

/-- `RMF.ballotLower` with the exponential linearised: `2c⁺(1 - (c⁺)²/(2nv₋))/√(2πnv₊)`.
Linear in `c⁺` up to a cubic, which is what lets the start average produce `Ẽ(a-S)⁺` and a
third moment rather than an expectation of an exponential. -/
noncomputable def ballotLinear (vmin vmax : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  2 * max c 0 * (1 - (max c 0) ^ 2 / (2 * ((n : ℝ) * vmin)))
    / √(2 * π * ((n : ℝ) * vmax))

/-- `e^{-t} ≥ 1 - t`, pointwise in the barrier level. -/
lemma ballotLinear_le_ballotLower {vmin vmax : ℝ} (hvmin : 0 < vmin) {n : ℕ} (hn : 1 ≤ n)
    (c : ℝ) : ballotLinear vmin vmax n c ≤ ballotLower vmin vmax n c := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnv : (0 : ℝ) < (n : ℝ) * vmin := by positivity
  have hc0 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  rw [ballotLinear, ballotLower]
  have hlin : 1 - (max c 0) ^ 2 / (2 * ((n : ℝ) * vmin))
      ≤ Real.exp (-(max c 0) ^ 2 / (2 * ((n : ℝ) * vmin))) := by
    have hx := Real.add_one_le_exp (-((max c 0) ^ 2 / (2 * ((n : ℝ) * vmin))))
    have hrw : -(max c 0) ^ 2 / (2 * ((n : ℝ) * vmin))
        = -((max c 0) ^ 2 / (2 * ((n : ℝ) * vmin))) := by ring
    rw [hrw]
    linarith
  gcongr

/-- **`ofReal` of an integral is below the `lintegral` of `ofReal`**, with no sign hypothesis:
`f ≤ f⁺` and `ofReal` does not see the difference. -/
lemma ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hf : Integrable f ν) :
    ENNReal.ofReal (∫ x, f x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  have hpos : Integrable (fun x => max (f x) 0) ν := hf.pos_part
  have hle : (∫ x, f x ∂ν) ≤ ∫ x, max (f x) 0 ∂ν :=
    integral_mono hf hpos fun x => le_max_left _ _
  refine le_trans (ENNReal.ofReal_le_ofReal hle) ?_
  rw [ofReal_integral_eq_lintegral_ofReal hpos (Filter.Eventually.of_forall
    fun x => le_max_right _ _)]
  refine le_of_eq (lintegral_congr fun x => ?_)
  rcases le_or_gt 0 (f x) with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h.le, ENNReal.ofReal_eq_zero.2 h.le, ENNReal.ofReal_zero]

/-- **The tail range, pointwise.**  Two constant barriers differing by `c`, with the lower one at
least `T`: the difference of the two barrier probabilities is a *relative* error of size `ε/δ`,
where `ε` is the (A2) Lipschitz bound and `δ` the uniform (A1) lower bound.

This is Harper’s "crucial point" in the form the induction uses.  With `T = Λ⁴` and `c ≪ Λ` the
ratio is `≪ 1/Λ³`, which is what makes the per-level error summable. -/
theorem IsGaussianWalk.barrierProb_sub_le_relative (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {b c T : ℝ} (hT : 0 < T) (hTb : T ≤ b) (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n)
    (hTn : T ≤ √((n : ℝ) * vmin)) :
    |barrierProb μ G (b + c) n - barrierProb μ G b n|
      ≤ (maxWindowConst vmin vmax c / √(n : ℝ))
          / (2 * T * Real.exp (-(1 : ℝ) / 2) / √(2 * π * ((n : ℝ) * vmax)))
        * barrierProb μ G b n := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnum : (0 : ℝ) < 2 * T * Real.exp (-(1 : ℝ) / 2) := by positivity
  have hδ : (0 : ℝ) < 2 * T * Real.exp (-(1 : ℝ) / 2) / √(2 * π * ((n : ℝ) * vmax)) :=
    div_pos hnum (Real.sqrt_pos.2 (by positivity))
  have hδP : 2 * T * Real.exp (-(1 : ℝ) / 2) / √(2 * π * ((n : ℝ) * vmax))
      ≤ barrierProb μ G b n :=
    le_trans (h.explicit_le_barrierProb ⟨hvmin, hlo, hhi⟩ hT.le hn hTn)
      (barrierProb_mono (μ := μ) G hTb n)
  refine abs_sub_le_relative hδ hδP ?_
  have hmono := barrierProb_mono (μ := μ) G (by linarith : b ≤ b + c) n
  rw [abs_of_nonneg (by linarith)]
  exact h.barrierProb_sub_le ⟨hvmin, hlo, hhi⟩ b hc hn

/-! ### The tail range, in event form

At the *lower* freeze point `M`, the suffix barrier is genuinely constant as soon as the split time
brackets it from below: for `j > N` and `M ≤ N + 1` one has `min{j, M} = M`, so
`β_{a,M}(j) = a + 10 log M`.  The freeze point itself stays real: Harper’s is
`(log_{i+1} n)²⁰`.  That side of the comparison is therefore an **equality** with a
constant-barrier event, not merely a containment, which is what lets the pointwise round trip be
applied to it. -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The relative error of the tail round trip: the (A2) Lipschitz bound over the uniform (A1) lower
bound, at window width `c`, floor `T`, and length `m`. -/
noncomputable def tailRatio (vmin vmax c T : ℝ) (m : ℕ) : ℝ :=
  (maxWindowConst vmin vmax c / √(m : ℝ))
    / (2 * T * Real.exp (-(1 : ℝ) / 2) / √(2 * π * ((m : ℝ) * vmax)))

/-- The ratio is a quotient of nonnegative quantities.  `RMF.maxWindowConst` and
`RMF.tailRatio` are opaque, so `positivity` cannot see this by itself. -/
lemma tailRatio_nonneg {vmin vmax c T : ℝ} (hvmin : 0 < vmin) (hc : 0 ≤ c) (hT : 0 ≤ T) (m : ℕ) :
    0 ≤ tailRatio vmin vmax c T m := by
  have hK : (0 : ℝ) ≤ maxWindowConst vmin vmax c :=
    le_trans zero_le_one (one_le_maxWindowConst hvmin hc)
  rw [tailRatio]
  exact div_nonneg (div_nonneg hK (Real.sqrt_nonneg _)) (by positivity)

/-- **The round-trip ratio does not depend on the length.**  The `√m` in the (A2) numerator cancels
the `√m` inside the (A1) lower bound, leaving a quantity that depends only on the window width, the
floor `T` and the variance bound.  This is what makes the ratio uniform across levels. -/
lemma tailRatio_eq {vmin vmax c T : ℝ} (hvmax : 0 < vmax) (hT : T ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    tailRatio vmin vmax c T m
      = maxWindowConst vmin vmax c * √(2 * π * vmax) / (2 * T * Real.exp (-(1 : ℝ) / 2)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.2 hmR
  have hsplit : √(2 * π * ((m : ℝ) * vmax)) = √(2 * π * vmax) * √(m : ℝ) := by
    rw [show 2 * π * ((m : ℝ) * vmax) = (2 * π * vmax) * (m : ℝ) by ring,
      Real.sqrt_mul (by positivity)]
  have hspv : (0 : ℝ) < √(2 * π * vmax) := Real.sqrt_pos.2 (by positivity)
  have he : (0 : ℝ) < Real.exp (-(1 : ℝ) / 2) := Real.exp_pos _
  rw [tailRatio, hsplit]
  field_simp

/-- **The round-trip ratio, bounded.**  Monotonicity of the (A2) constant in the window width, on
top of `RMF.tailRatio_eq`.  With `c ≤ 200Λ` and `T = Λ⁴` the caller supplies `K = K(200Λ) = O(Λ)`,
giving `ρ = O(1/Λ³)`. -/
lemma tailRatio_le {vmin vmax c T K : ℝ} (hvmax : 0 < vmax) (hT : 0 < T)
    {m : ℕ} (hm : 1 ≤ m) (hK : maxWindowConst vmin vmax c ≤ K) :
    tailRatio vmin vmax c T m
      ≤ K * √(2 * π * vmax) / (2 * T * Real.exp (-(1 : ℝ) / 2)) := by
  rw [tailRatio_eq hvmax (ne_of_gt hT) hm]
  have hden : (0 : ℝ) < 2 * T * Real.exp (-(1 : ℝ) / 2) := by positivity
  gcongr

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Membership of the block sums in the suffix set, written in the walk’s own coordinates. -/
lemma suffixSet_mem_eq (G : ℕ → Ω → ℝ) (β : ℕ → ℝ) (N n : ℕ) (x : ℕ → ℝ) :
    {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
      = {ω | ∀ j, N < j → j ≤ n → walk G j ω - walk G N ω ≤ β j - x N} := by
  ext ω
  simp only [suffixSet, Set.mem_setOf_eq]
  exact forall_congr' fun j => forall_congr' fun h1 => forall_congr' fun h2 => by
    rw [blockSums_comp G h1.le h2 ω]

/-- **The tail range, pointwise, for any barrier — both directions.**  Let `β₀` be constant
`= c` past the split time and `β` lie in `[clo, chi]` there, `clo ≤ c ≤ chi`.  If `T ≤ clo - x_N`,
each of the two suffix probabilities is within a factor `1 + ρ` of the other, `ρ` the round-trip
ratio at window width `chi - clo`.  Both directions come from one round trip on
`(clo - x_N, chi - x_N)`, which is what lets the downward barrier reuse it; the floor is referenced
to `clo`, free upward (`clo = c`) and a threshold on the level downward (`clo = a - 10 log L`). -/
lemma IsGaussianWalk.suffixSet_tail_pointwise (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {β β₀ : ℕ → ℝ} {c clo chi T : ℝ} {N n : ℕ} (hT : 0 < T) (hnN : 1 ≤ n - N)
    (hTn : T ≤ √((((n - N : ℕ)) : ℝ) * vmin))
    (hβ₀ : ∀ j, N < j → β₀ j = c) (hβlo : ∀ j, N < j → clo ≤ β j)
    (hβhi : ∀ j, N < j → β j ≤ chi) (hclo : clo ≤ c) (hchi : c ≤ chi)
    {x : ℕ → ℝ} (hfloor : T ≤ clo - x N) :
    μ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
        ≤ ENNReal.ofReal (1 + tailRatio vmin vmax (chi - clo) T (n - N))
          * μ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β₀ N n x}
      ∧ μ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β₀ N n x}
        ≤ ENNReal.ofReal (1 + tailRatio vmin vmax (chi - clo) T (n - N))
          * μ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x} := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hxclo : x N ≤ clo := by linarith
  have hw0 : (0 : ℝ) ≤ chi - clo := by linarith
  set b : ℝ := clo - x N with hb
  have hTb : T ≤ b := by simp only [hb]; linarith
  -- the three constant-barrier events for the shifted walk
  have hlowsub : {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b}
      ⊆ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x} := by
    rw [suffixSet_mem_eq]
    exact const_subset_suffix hβlo
  have huppsub : {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β N n x}
      ⊆ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b + (chi - clo)} := by
    rw [suffixSet_mem_eq, show b + (chi - clo) = chi - x N by simp only [hb]; ring]
    exact suffix_subset_const hβhi (by linarith)
  have hzero : {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β₀ N n x}
      = {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ c - x N} :=
    suffixSet_const_eq G hβ₀ (by linarith)
  -- the round trip, in real form
  have hratio : (0 : ℝ) ≤ tailRatio vmin vmax (chi - clo) T (n - N) :=
    tailRatio_nonneg hvmin hw0 hT.le _
  have hrel := (h.shift N).barrierProb_sub_le_relative ⟨hvmin, fun i => hlo (i + N), fun i => hhi
    (i + N)⟩
    hT hTb hw0 hnN hTn
  have hmono := barrierProb_mono (μ := μ) (fun m => G (m + N))
    (by linarith : b ≤ b + (chi - clo)) (n - N)
  have hreal : barrierProb μ (fun m => G (m + N)) (b + (chi - clo)) (n - N)
      ≤ (1 + tailRatio vmin vmax (chi - clo) T (n - N))
        * barrierProb μ (fun m => G (m + N)) b (n - N) := by
    rw [abs_of_nonneg (by linarith)] at hrel
    simp only [tailRatio]
    linarith
  have hfin0 : μ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b} ≠ ⊤ := measure_ne_top _ _
  have hfin1 : μ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b + (chi - clo)} ≠ ⊤ :=
    measure_ne_top _ _
  have hstep : μ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b + (chi - clo)}
      ≤ ENNReal.ofReal (1 + tailRatio vmin vmax (chi - clo) T (n - N))
        * μ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b} := by
    rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin0,
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- the level-`β₀` event sits between the two constant ones
  have hmid1 : {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b}
      ⊆ {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β₀ N n x} := by
    rw [hzero]
    exact fun ω hω i hi => le_trans (hω i hi) (by simp only [hb]; linarith)
  have hmid2 : {ω | (blockSums N n fun i => G i ω) ∈ suffixSet β₀ N n x}
      ⊆ {ω | ∀ i ≤ n - N, walk (fun m => G (m + N)) i ω ≤ b + (chi - clo)} := by
    rw [hzero]
    exact fun ω hω i hi => le_trans (hω i hi) (by simp only [hb]; linarith)
  constructor
  · exact le_trans (le_trans (measure_mono huppsub) hstep)
      (mul_le_mul_right (measure_mono hmid1) _)
  · exact le_trans (le_trans (measure_mono hmid2) hstep)
      (mul_le_mul_right (measure_mono hlowsub) _)

/-- **The explicit constant of (A1) lower**, in the `min {1, ·/√n}` shape:
`2e^{-1/2}·min{1, √v₋}/√(2π v₊)`.  It depends only on the variance bounds, which is what makes
Harper’s "uniformly" formalisable: downstream the walk changes with `x` and `n`. -/
noncomputable def barrierConstLow (vmin vmax : ℝ) : ℝ :=
  2 * Real.exp (-(1 : ℝ) / 2) * min 1 (√vmin) / √(2 * π * vmax)

lemma barrierConstLow_pos {vmin vmax : ℝ} (hvmin : 0 < vmin) (hvmax : 0 < vmax) :
    0 < barrierConstLow vmin vmax := by
  have h1 : (0 : ℝ) < min 1 (√vmin) := lt_min one_pos (Real.sqrt_pos.2 hvmin)
  have h2 : (0 : ℝ) < √(2 * π * vmax) := Real.sqrt_pos.2 (by positivity)
  rw [barrierConstLow]
  exact div_pos (mul_pos (by positivity) h1) h2

/-- **(A1) lower, with an explicit constant and the `min` shape.**  For every `c ≥ 0` and `n ≥ 1`,
`barrierConstLow v₋ v₊ · min{1, c/√n} ≤ P(S_j ≤ c ∀ j ≤ n)`.  The two cases of the `min` are those
of `RMF.IsGaussianWalk.explicit_le_barrierProb`: below the standard deviation the bound is linear in
`c`; above it the barrier is lowered to `√(n v₋)`, where the probability is bounded below by a
constant depending only on the variance bounds. -/
theorem IsGaussianWalk.barrierConstLow_le_barrierProb (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    barrierConstLow vmin vmax * min 1 (c / √(n : ℝ)) ≤ barrierProb μ G c n := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsvmin : (0 : ℝ) < √vmin := Real.sqrt_pos.2 hvmin
  have hspv : (0 : ℝ) < √(2 * π * vmax) := Real.sqrt_pos.2 (by positivity)
  have he : (0 : ℝ) < Real.exp (-(1 : ℝ) / 2) := Real.exp_pos _
  have hmv : (0 : ℝ) < min 1 (√vmin) := lt_min one_pos hsvmin
  have hsv : √((n : ℝ) * vmin) = √(n : ℝ) * √vmin := Real.sqrt_mul (by linarith) _
  have hs2 : √(2 * π * ((n : ℝ) * vmax)) = √(2 * π * vmax) * √(n : ℝ) := by
    rw [show 2 * π * ((n : ℝ) * vmax) = (2 * π * vmax) * (n : ℝ) by ring,
      Real.sqrt_mul (by positivity)]
  rcases le_or_gt c (√((n : ℝ) * vmin)) with hcase | hcase
  · refine le_trans ?_ (h.explicit_le_barrierProb ⟨hvmin, hlo, hhi⟩ hc hn hcase)
    rw [hs2, barrierConstLow]
    have hstep : 2 * Real.exp (-(1 : ℝ) / 2) * min 1 (√vmin) / √(2 * π * vmax)
        * min 1 (c / √(n : ℝ))
        ≤ 2 * Real.exp (-(1 : ℝ) / 2) * 1 / √(2 * π * vmax) * (c / √(n : ℝ)) := by
      refine mul_le_mul ?_ (min_le_right _ _) (le_min zero_le_one (by positivity)) (by positivity)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)) hspv.le
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  · refine le_trans ?_ (le_trans (h.explicit_le_barrierProb ⟨hvmin, hlo, hhi⟩
      (Real.sqrt_nonneg _) hn le_rfl) (barrierProb_mono (μ := μ) G hcase.le n))
    rw [hs2, hsv, barrierConstLow]
    have hstep : 2 * Real.exp (-(1 : ℝ) / 2) * min 1 (√vmin) / √(2 * π * vmax)
        * min 1 (c / √(n : ℝ))
        ≤ 2 * Real.exp (-(1 : ℝ) / 2) * √vmin / √(2 * π * vmax) * 1 := by
      refine mul_le_mul ?_ (min_le_left _ _) (le_min zero_le_one (by positivity)) (by positivity)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)) hspv.le
    refine le_trans hstep (le_of_eq ?_)
    field_simp

/-- **The tail range, pointwise, in event form.**  For a prefix path in the barrier event whose
endpoint is at most `-T`, the level-`L` suffix probability exceeds the level-`N` one by a factor of
at most `1 + tailRatio`. -/
lemma IsGaussianWalk.suffix_tail_pointwise (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L M T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) {N n : ℕ} (hN : 1 ≤ N) (hNM : (N : ℝ) ≤ M)
    (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hnN : 1 ≤ n - N) (hTn : T ≤ √((((n - N : ℕ)) : ℝ) * vmin))
    {x : ℕ → ℝ} (hxT : x N ≤ -T) :
    μ {ω | (blockSums N n fun i => G i ω) ∈ suffixBarrierSet a L N n x}
      ≤ ENNReal.ofReal
            (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T (n - N))
        * μ {ω | (blockSums N n fun i => G i ω) ∈ suffixBarrierSet a M N n x} := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := le_trans hN1 hNM
  have hL1 : (1 : ℝ) ≤ L := le_trans hM1 hML
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hlogML : Real.log M ≤ Real.log L := Real.log_le_log (by linarith) hML
  have hβ₀ : ∀ j, N < j → frozenBarrier a M j = a + 10 * Real.log M := by
    intro j hj
    have hjR : M ≤ (j : ℝ) := le_trans hMN (by exact_mod_cast hj)
    rw [frozenBarrier, min_eq_right hjR]
  have hβlo : ∀ j, N < j → a + 10 * Real.log M ≤ frozenBarrier a L j := by
    intro j hj
    have hjR : M ≤ (j : ℝ) := le_trans hMN (by exact_mod_cast hj)
    have hmin : M ≤ min (j : ℝ) L := le_min hjR hML
    have := Real.log_le_log (by linarith) hmin
    simp only [frozenBarrier]
    linarith
  have hgen := h.suffixSet_tail_pointwise ⟨hvmin, hlo, hhi⟩ hT hnN hTn hβ₀ hβlo
    (fun j _ => frozenBarrier_le_const hL1 j) (le_refl (a + 10 * Real.log M))
    (by linarith : a + 10 * Real.log M ≤ a + 10 * Real.log L)
    (x := x) (by linarith)
  rw [show a + 10 * Real.log L - (a + 10 * Real.log M)
      = 10 * Real.log L - 10 * Real.log M by ring] at hgen
  exact hgen.1

/-- **The tail range, integrated.**  The pointwise bound integrates over the tail part of the
prefix event, giving the same relative bound on the joint probabilities.

No measurability of the suffix kernel `x ↦ P(suffix ∈ S(x))` is needed: `lintegral` is monotone
without it, and the bound holds almost everywhere on `A` by `self_mem_ae_restrict`. -/
theorem IsGaussianWalk.measure_prefix_inter_suffix_tail_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax)
    {a L M T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) {N n : ℕ} (hN : 1 ≤ N)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hnN : 1 ≤ n - N) (hTn : T ≤ √((((n - N : ℕ)) : ℝ) * vmin))
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    (hAsub : A ⊆ prefixBarrierSet a L N ∩ {x | x N ≤ -T}) :
    μ ({ω | (prefixSums N fun i => G i ω) ∈ A}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixBarrierSet a L N n (prefixSums N fun i => G i ω)})
      ≤ ENNReal.ofReal
            (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T (n - N))
        * μ ({ω | (prefixSums N fun i => G i ω) ∈ A}
            ∩ {ω | (blockSums N n fun i => G i ω)
                ∈ suffixBarrierSet a M N n (prefixSums N fun i => G i ω)}) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  rw [h.measure_prefix_inter_block N n hA (measurableSet_suffixBarrierSet a L N n),
    h.measure_prefix_inter_block N n hA (measurableSet_suffixBarrierSet a M N n),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict hA] with x hx
  obtain ⟨-, hxT⟩ := hAsub hx
  simp only [Set.mem_setOf_eq] at hxT
  exact h.suffix_tail_pointwise ⟨hvmin, hlo, hhi⟩ ha hT hN hNM hMN hML hnN hTn hxT

/-! ### Combining the two ranges

The prefix barrier event splits at the endpoint value `-T` into a middle and a tail part; these are
disjoint and measurable, so the joint probabilities add.  Bounding the middle part by the uniform
(A1) estimate and the tail part by the round trip gives the one-step comparison.  Everything here
is additivity and monotonicity of measures. -/

lemma measurableSet_prefixBarrierSet (a L : ℝ) (N : ℕ) :
    MeasurableSet (prefixBarrierSet a L N) :=
  measurableSet_prefixSet (frozenBarrier a L) N

/-- **The one-step comparison.**  The level-`L` barrier probability is at most the middle-range
contribution plus `(1 + ρ)` times the level-`N` one. -/
theorem IsGaussianWalk.curvedBarrier_step_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L M T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) {N n : ℕ} (hN : 1 ≤ N)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hNn : N ≤ n) (hnN : 1 ≤ n - N)
    (hTn : T ≤ √((((n - N : ℕ)) : ℝ) * vmin)) :
    μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a L j}
      ≤ ENNReal.ofReal
            (barrierConst vmin vmax (a + 10 * Real.log L + T) / √((((n - N : ℕ)) : ℝ)))
          * μ {ω | (prefixSums N fun i => G i ω)
              ∈ prefixBarrierSet a L N ∩ {x | -T < x N}}
        + ENNReal.ofReal
            (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T (n - N))
          * μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a M j} := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL : (1 : ℝ) ≤ L := le_trans hN1 (le_trans hNM hML)
  set Pm : Set (ℕ → ℝ) := prefixBarrierSet a L N ∩ {x | -T < x N} with hPm
  set Pt : Set (ℕ → ℝ) := prefixBarrierSet a L N ∩ {x | x N ≤ -T} with hPt
  have hmP : Measurable fun ω => prefixSums N fun i => G i ω :=
    (measurable_prefixSums N).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hmB : Measurable fun ω => blockSums N n fun i => G i ω :=
    (measurable_blockSums N n).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hPmm : MeasurableSet Pm :=
    (measurableSet_prefixBarrierSet a L N).inter
      (measurableSet_lt measurable_const (measurable_pi_apply N))
  have hPtm : MeasurableSet Pt :=
    (measurableSet_prefixBarrierSet a L N).inter
      (measurableSet_le (measurable_pi_apply N) measurable_const)
  have hunion : prefixBarrierSet a L N = Pm ∪ Pt := by
    ext x
    simp only [hPm, hPt, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx
      rcases lt_or_ge (-T) (x N) with hlt | hge
      · exact Or.inl ⟨hx, hlt⟩
      · exact Or.inr ⟨hx, hge⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hdisj : Disjoint ({ω | (prefixSums N fun i => G i ω) ∈ Pm}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixBarrierSet a L N n (prefixSums N fun i => G i ω)})
      ({ω | (prefixSums N fun i => G i ω) ∈ Pt}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixBarrierSet a L N n (prefixSums N fun i => G i ω)}) := by
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    have hm := h1.1
    have ht := h2.1
    simp only [hPm, hPt, Set.mem_setOf_eq, Set.mem_inter_iff] at hm ht
    linarith [hm.2, ht.2]
  have hmeasT : MeasurableSet ({ω | (prefixSums N fun i => G i ω) ∈ Pt}
      ∩ {ω | (blockSums N n fun i => G i ω)
          ∈ suffixBarrierSet a L N n (prefixSums N fun i => G i ω)}) :=
    (hmP hPtm).inter ((hmP.prodMk hmB) (measurableSet_suffixBarrierSet a L N n))
  -- split the barrier event
  have hpre : {ω | (prefixSums N fun i => G i ω) ∈ Pm ∪ Pt}
      = {ω | (prefixSums N fun i => G i ω) ∈ Pm}
        ∪ {ω | (prefixSums N fun i => G i ω) ∈ Pt} := rfl
  rw [frozenBarrier_event_eq G a L hNn, hunion, hpre, Set.union_inter_distrib_right,
    measure_union hdisj hmeasT]
  gcongr
  · exact h.measure_prefix_inter_suffix_le ⟨hvmin, hlo, hhi⟩ hL hnN hPmm (by rw [hPm])
  · refine le_trans (h.measure_prefix_inter_suffix_tail_le ⟨hvmin, hlo, hhi⟩ ha hT hN hNM hMN hML
      hnN hTn hPtm (by rw [hPt])) ?_
    gcongr
    rw [frozenBarrier_event_eq G a M hNn]
    refine Set.inter_subset_inter_left _ fun ω hω => ?_
    have hmem : (prefixSums N fun i => G i ω) ∈ prefixBarrierSet a L N := hω.1
    rwa [prefixBarrierSet_congr hNM hML] at hmem

/-! ### The middle mass

The prefix event confines the endpoint to a window: below by the split `x_N > -T`, above by the
barrier at time `N`, which is `a + 10 log N`.  So its mass is at most the Gaussian mass of a window
of width `a + 10 log N + T`, and the exponent budget then turns the middle contribution into
`1/(√n Λ²)`. -/

/-- **The middle mass.**  The prefix event with endpoint above `-T` sits inside a window of width
`a + 10 log N + T` for `S_N`. -/
theorem IsGaussianWalk.measure_prefix_mid_le (h : IsGaussianWalk G v μ) {a L T : ℝ}
    {N : ℕ} (hNL : (N : ℝ) ≤ L) (hV : (∑ m ∈ Finset.range N, v m) ≠ 0) :
    μ {ω | (prefixSums N fun i => G i ω) ∈ prefixBarrierSet a L N ∩ {x | -T < x N}}
      ≤ ENNReal.ofReal ((a + 10 * Real.log N + T)
          / √(2 * π * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ))) := by
  have hsub : {ω | (prefixSums N fun i => G i ω) ∈ prefixBarrierSet a L N ∩ {x | -T < x N}}
      ⊆ walk G N ⁻¹' Set.Icc (-T) (-T + (a + 10 * Real.log N + T)) := by
    rintro ω ⟨h1, h2⟩
    have hpe : prefixSums N (fun i => G i ω) N = walk G N ω := prefixSums_comp G (le_refl N) ω
    simp only [Set.mem_setOf_eq] at h2
    rw [hpe] at h2
    have hup := h1 N le_rfl
    rw [frozenBarrier, min_eq_left hNL, hpe] at hup
    exact ⟨h2.le, by linarith⟩
  refine le_trans (measure_mono hsub) ?_
  rw [← Measure.map_apply (h.measurable_walk N) measurableSet_Icc, h.map_walk N]
  exact measure_Icc_gaussianReal_le_ofReal 0 hV _ _

/-- **(A1) upper for the curved barrier**, in `ℝ≥0∞` form.  The frozen barrier never exceeds
`a + 10 log L`, so (A1) applies at that constant height. -/
theorem IsGaussianWalk.measure_frozenBarrier_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a L j}
      ≤ ENNReal.ofReal (barrierConst vmin vmax (a + 10 * Real.log L) / √(n : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hc0 : (0 : ℝ) ≤ a + 10 * Real.log L := by
    linarith [Real.log_nonneg hL]
  have hnR : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsub : {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a L j}
      ⊆ {ω | ∀ j ≤ n, walk G j ω ≤ a + 10 * Real.log L} :=
    fun ω hω j hj => (hω j hj).trans (frozenBarrier_le_const hL j)
  refine le_trans (measure_mono hsub) ?_
  refine ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (div_nonneg (barrierConst_nonneg hvmin hc0) hnR.le) |>.2 ?_
  exact h.barrierProb_le_of_comparable_mgf hc0 ⟨hvmin, hlo, hhi⟩ hn

/-! ### The one-step comparison in real form

`RMF.IsGaussianWalk.curvedBarrier_step_le` lives in `ℝ≥0∞`, where the multiplicative phrasing kept
subtraction out of the way.  The numeric estimates that follow are inequalities between reals, so
the comparison is transported across here, once. -/

/-- The one-step comparison, with every quantity a real number. -/
theorem IsGaussianWalk.curvedBarrierProb_step_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L M T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) {N n : ℕ} (hN : 1 ≤ N)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hNn : N ≤ n) (hnN : 1 ≤ n - N)
    (hTn : T ≤ √((((n - N : ℕ)) : ℝ) * vmin)) :
    curvedBarrierProb μ G a L n
      ≤ barrierConst vmin vmax (a + 10 * Real.log L + T) / √((((n - N : ℕ)) : ℝ))
          * (μ {ω | (prefixSums N fun i => G i ω)
              ∈ prefixBarrierSet a L N ∩ {x | -T < x N}}).toReal
        + (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T (n - N))
          * curvedBarrierProb μ G a M n := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hm : (0 : ℝ) < (((n - N : ℕ)) : ℝ) := by exact_mod_cast hnN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := le_trans hN1 hNM
  have hL : (1 : ℝ) ≤ L := le_trans hM1 hML
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hc0 : (0 : ℝ) ≤ 10 * Real.log L - 10 * Real.log M :=
    by linarith [Real.log_le_log (by linarith : (0 : ℝ) < M) hML]
  have hA1 : (0 : ℝ) ≤ barrierConst vmin vmax (a + 10 * Real.log L + T) / √((((n - N : ℕ)) : ℝ)) :=
    div_nonneg (barrierConst_nonneg hvmin (by linarith)) (Real.sqrt_nonneg _)
  have hratio : (0 : ℝ) ≤ tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T (n - N) := by
    have hK : (0 : ℝ) ≤ maxWindowConst vmin vmax (10 * Real.log L - 10 * Real.log M) :=
      le_trans zero_le_one (one_le_maxWindowConst hvmin hc0)
    have hden : (0 : ℝ)
        < 2 * T * Real.exp (-(1 : ℝ) / 2) / √(2 * π * ((((n - N : ℕ)) : ℝ) * vmax)) := by
      exact div_pos (by positivity) (Real.sqrt_pos.2 (by positivity))
    exact div_nonneg (div_nonneg hK (Real.sqrt_nonneg _)) hden.le
  have hstep := h.curvedBarrier_step_le ⟨hvmin, hlo, hhi⟩ ha hT hN hNM hMN hML hNn hnN hTn
  have hfin1 : ENNReal.ofReal (barrierConst vmin vmax (a + 10 * Real.log L + T)
        / √((((n - N : ℕ)) : ℝ)))
      * μ {ω | (prefixSums N fun i => G i ω) ∈ prefixBarrierSet a L N ∩ {x | -T < x N}} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hfin2 : ENNReal.ofReal
        (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T (n - N))
      * μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrier a M j} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have := ENNReal.toReal_mono (by finiteness) hstep
  rwa [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA1, ENNReal.toReal_ofReal (by linarith)] at this
/-! ### The one-step estimate, assembled

`RMF.IsGaussianWalk.curvedBarrierProb_step_le` bounds the level-`L` probability by a middle term
plus `(1 + ρ)` times the level-`M` one, and `RMF.middle_term_le` together with `RMF.tail_term_le`
collapses the two contributions onto `1/(Λ²√n)` once the quantities have the advertised sizes.
That is where the standing hypotheses of Harper’s induction enter, at level `Λ = log_{i+1} n`:
`a ≤ 1000Λ`; `10 log L ≤ c₀Λ`, with equality at `c₀ = 200` for `L = (log_i n)²⁰`; `Λ²⁰ ≤ M`, which
makes the first block's standard deviation `≳ Λ¹⁰`; `N ≤ M ≤ N + 1`; and `2N ≤ n`.

The freeze point `M` is real and the split time `N` an integer.  The prefix condition is
level-independent only if `N ≤ M`, the level-`M` suffix barrier constant only if `M ≤ N + 1`, and
`N = ⌊M⌋` meets both, while taking `M = N` would force `M = (log_i n)²⁰` exactly.  The (A1) constant
must grow **linearly** (`RMF.barrierConst_le_mul`), not merely monotonically. -/

/-- The per-level constant of Probability Lemma 1: the middle contribution `√2·K₁·K₂·D` plus the
tail contribution `K_ρ·B`.  The numerals are the ones the standing hypotheses produce:
`a + 10 log L + T ≤ (1001 + c₀)Λ⁴`, `a + 10 log M ≤ (1000 + c₀)Λ`, and a window of width
`≤ c₀Λ`; at Harper’s `c₀ = 200` these read `1201`, `1200`, `200`.  The `√2` inside `D` is the price
of the split time being `⌊M⌋` rather than `M`: it costs a factor `2` in the first block’s
variance. -/
noncomputable def stepConst (vmin vmax c₀ : ℝ) : ℝ :=
  √2 * (barrierConstBound vmin vmax (1001 + c₀) * (1001 + c₀) * (√2 / √(2 * π * vmin)))
    + maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax) / (2 * Real.exp (-(1 : ℝ) / 2))
        * barrierConstBound vmin vmax (1000 + c₀)

lemma stepConst_nonneg {vmin vmax c₀ : ℝ} (hvmin : 0 < vmin) (hc₀ : 0 ≤ c₀) :
    0 ≤ stepConst vmin vmax c₀ := by
  have h1 : (0 : ℝ) ≤ barrierConstBound vmin vmax (1001 + c₀) :=
    barrierConstBound_nonneg hvmin (by linarith)
  have h2 : (0 : ℝ) ≤ barrierConstBound vmin vmax (1000 + c₀) :=
    barrierConstBound_nonneg hvmin (by linarith)
  have h3 : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ := maxWindowConstBound_nonneg hvmin hc₀
  have hA : (0 : ℝ)
      ≤ √2 * (barrierConstBound vmin vmax (1001 + c₀) * (1001 + c₀) * (√2 / √(2 * π * vmin))) :=
    mul_nonneg (Real.sqrt_nonneg 2)
      (mul_nonneg (mul_nonneg h1 (by linarith)) (by positivity))
  have hB : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax)
      / (2 * Real.exp (-(1 : ℝ) / 2)) * barrierConstBound vmin vmax (1000 + c₀) :=
    mul_nonneg (div_nonneg (mul_nonneg h3 (Real.sqrt_nonneg _)) (by positivity)) h2
  rw [stepConst]
  linarith

/-- **The one-step estimate of Probability Lemma 1.**  Moving the freeze point from `M` out to `L`
changes the curved-barrier probability by at most `stepConst/(Λ²√n)`.  Both freeze points are real;
the integer `N` is only the split time, required to bracket `M`.  The error is measured against
`Λ⁻²`, summable along the iterated-logarithm scale, so `RMF.abs_sub_telescope_iterLog` turns the
chain of these into a single bound of the same shape. -/
theorem IsGaussianWalk.abs_curvedBarrierProb_sub_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a Λ L M c₀ : ℝ} {N n : ℕ} (hΛ : 1 ≤ Λ) (ha : 0 ≤ a) (haΛ : a ≤ 1000 * Λ)
    (hML : M ≤ L) (hlogL : 10 * Real.log L ≤ c₀ * Λ) (hΛM : Λ ^ 20 ≤ M)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hN : 1 ≤ N) (hNn : 2 * N ≤ n)
    (hTn : Λ ^ 4 ≤ √((((n - N : ℕ)) : ℝ) * vmin)) :
    |curvedBarrierProb μ G a L n - curvedBarrierProb μ G a M n|
      ≤ stepConst vmin vmax c₀ / (Λ ^ 2 * √(n : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  -- the shape of the pieces
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ4 : (1 : ℝ) ≤ Λ ^ 4 := one_le_pow₀ hΛ
  have hT : (0 : ℝ) < Λ ^ 4 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := le_trans hN1 hNM
  have hL1 : (1 : ℝ) ≤ L := le_trans hM1 hML
  have hNL : (N : ℝ) ≤ L := le_trans hNM hML
  have hNn' : N ≤ n := by omega
  have hn : 1 ≤ n := by omega
  have hnN : 1 ≤ n - N := by omega
  have hmn : (n : ℝ) ≤ 2 * (((n - N : ℕ)) : ℝ) := by
    have hcast : (((n - N : ℕ)) : ℝ) = (n : ℝ) - (N : ℝ) := Nat.cast_sub hNn'
    have h2N : (2 : ℝ) * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    rw [hcast]; linarith
  -- the logarithms
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hlogM0 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  have hlogNM : Real.log N ≤ Real.log M := Real.log_le_log (by linarith) hNM
  have hlogML : Real.log M ≤ Real.log L := Real.log_le_log (by linarith) hML
  have hc₀ : (0 : ℝ) ≤ c₀ := nonneg_of_mul_nonneg_left (by linarith) hΛ0
  have hΛΛ4 : Λ ≤ Λ ^ 4 := le_self_pow₀ hΛ (by norm_num)
  have hargL : a + 10 * Real.log L + Λ ^ 4 ≤ (1001 + c₀) * Λ ^ 4 := by
    linarith [mul_le_mul_of_nonneg_left hΛΛ4 hc₀]
  have hargN : a + 10 * Real.log N + Λ ^ 4 ≤ (1001 + c₀) * Λ ^ 4 := by linarith
  have hargM : a + 10 * Real.log M ≤ (1000 + c₀) * Λ := by linarith
  have hwin : 10 * Real.log L - 10 * Real.log M ≤ c₀ * Λ := by linarith
  -- the two (A1) constants, by linear growth
  have hA1 : barrierConst vmin vmax (a + 10 * Real.log L + Λ ^ 4)
      ≤ barrierConstBound vmin vmax (1001 + c₀) * Λ ^ 4 := barrierConst_le_mul hvmin hΛ4 hargL
  have hA2 : barrierConst vmin vmax (a + 10 * Real.log M)
      ≤ barrierConstBound vmin vmax (1000 + c₀) * Λ := barrierConst_le_mul hvmin hΛ hargM
  have hA1nn : (0 : ℝ) ≤ barrierConst vmin vmax (a + 10 * Real.log L + Λ ^ 4) :=
    barrierConst_nonneg hvmin (by linarith)
  have hA2nn : (0 : ℝ) ≤ barrierConst vmin vmax (a + 10 * Real.log M) :=
    barrierConst_nonneg hvmin (by linarith)
  -- the first block has standard deviation at least `Λ¹⁰√(π v₋)`; the factor `2` is the price of
  -- the split time being `⌊M⌋` rather than `M`
  have hΛ2N : Λ ^ 20 ≤ 2 * (N : ℝ) := by linarith
  have hVcast : ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ) = ∑ m ∈ Finset.range N, ((v m : ℝ)) :=
    NNReal.coe_sum _ _
  have hsum : (N : ℝ) * vmin ≤ ∑ m ∈ Finset.range N, ((v m : ℝ)) := by
    calc (N : ℝ) * vmin = ∑ _m ∈ Finset.range N, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.range N, ((v m : ℝ)) := Finset.sum_le_sum fun m _ => hlo m
  have hVpos : (0 : ℝ) < ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ) := by
    rw [hVcast]
    exact Finset.sum_pos (fun m _ => lt_of_lt_of_le hvmin (hlo m))
      (Finset.nonempty_range_iff.2 (by omega))
  have hVN : (∑ m ∈ Finset.range N, v m) ≠ 0 := by
    intro hc
    rw [hc] at hVpos
    simp at hVpos
  have hVlow : Λ ^ 20 * vmin ≤ 2 * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ) := by
    rw [hVcast]
    have h1 : Λ ^ 20 * vmin ≤ (2 * (N : ℝ)) * vmin := mul_le_mul_of_nonneg_right hΛ2N hvmin.le
    have h2 : (2 * (N : ℝ)) * vmin = 2 * ((N : ℝ) * vmin) := by ring
    linarith
  have hs : Λ ^ 10 / (√2 / √(2 * π * vmin))
      ≤ √(2 * π * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ)) := by
    have hs2 : √2 ≠ 0 := ne_of_gt (by positivity)
    have hpv : √(π * vmin) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have e1 : √((Λ ^ 10) ^ 2 * (π * vmin)) = Λ ^ 10 * √(π * vmin) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have e2 : √(2 * π * vmin) = √2 * √(π * vmin) := by
      rw [show 2 * π * vmin = 2 * (π * vmin) by ring, Real.sqrt_mul (by norm_num)]
    have hrw : Λ ^ 10 / (√2 / √(2 * π * vmin)) = √((Λ ^ 10) ^ 2 * (π * vmin)) := by
      rw [e1, e2]
      field_simp
    rw [hrw]
    refine Real.sqrt_le_sqrt ?_
    have hπ := Real.pi_pos
    linarith [mul_le_mul_of_nonneg_left hVlow hπ.le]
  -- the middle mass
  have hmidR : (μ {ω | (prefixSums N fun i => G i ω)
        ∈ prefixBarrierSet a L N ∩ {x | -(Λ ^ 4) < x N}}).toReal
      ≤ (a + 10 * Real.log N + Λ ^ 4)
          / √(2 * π * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal
      (div_nonneg (by linarith) (Real.sqrt_nonneg _))
      (h.measure_prefix_mid_le hNL hVN)
  -- the level-`M` probability
  have hQM : curvedBarrierProb μ G a M n
      ≤ barrierConst vmin vmax (a + 10 * Real.log M) / √(n : ℝ) := by
    simp only [curvedBarrierProb]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hA2nn (Real.sqrt_nonneg _))
      (h.measure_frozenBarrier_le ⟨hvmin, hlo, hhi⟩ hM1 ha hn)
  -- the round-trip ratio
  have hρ0 : (0 : ℝ) ≤ tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4) (n - N) :=
    tailRatio_nonneg hvmin (by linarith) (by positivity) _
  have hρ : tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4) (n - N)
      ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax)
          / (2 * Real.exp (-(1 : ℝ) / 2)) / Λ ^ 3 := by
    refine le_trans (tailRatio_le hvmax hT hnN (maxWindowConst_le_mul hvmin hΛ hwin)) (le_of_eq ?_)
    have hE : Real.exp (-(1 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hΛne : Λ ≠ 0 := ne_of_gt hΛ0
    field_simp
  -- the middle term, collapsed
  have h1 : curvedBarrierProb μ G a L n
      ≤ √2 * (barrierConstBound vmin vmax (1001 + c₀) * (1001 + c₀) * (√2 / √(2 * π * vmin)))
            / (Λ ^ 2 * √(n : ℝ))
        + (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4) (n - N))
            * curvedBarrierProb μ G a M n := by
    refine le_trans (h.curvedBarrierProb_step_le ⟨hvmin, hlo, hhi⟩
      ha hT hN hNM hMN hML hNn' hnN hTn)
      (add_le_add ?_ le_rfl)
    refine le_trans (mul_le_mul_of_nonneg_left hmidR (by positivity)) ?_
    exact middle_term_le hΛ (by positivity) hA1nn (by linarith) hA1 hargN hs hnN hn hmn
  -- the tail term, collapsed
  have h2 : tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4) (n - N)
        * curvedBarrierProb μ G a M n
      ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax) / (2 * Real.exp (-(1 : ℝ) / 2))
          * barrierConstBound vmin vmax (1000 + c₀) / (Λ ^ 2 * √(n : ℝ)) :=
    le_trans (mul_le_mul_of_nonneg_left hQM hρ0) (tail_term_le hΛ hn hρ0 hA2nn hρ hA2)
  -- recombine
  have hmono : curvedBarrierProb μ G a M n ≤ curvedBarrierProb μ G a L n :=
    curvedBarrierProb_mono (μ := μ) (by linarith : (0 : ℝ) < M) hML n
  have hring : (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4) (n - N))
        * curvedBarrierProb μ G a M n
      = curvedBarrierProb μ G a M n
        + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4) (n - N)
          * curvedBarrierProb μ G a M n := by ring
  have hsplit : stepConst vmin vmax c₀ / (Λ ^ 2 * √(n : ℝ))
      = √2 * (barrierConstBound vmin vmax (1001 + c₀) * (1001 + c₀) * (√2 / √(2 * π * vmin)))
            / (Λ ^ 2 * √(n : ℝ))
        + maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax) / (2 * Real.exp (-(1 : ℝ) / 2))
            * barrierConstBound vmin vmax (1000 + c₀) / (Λ ^ 2 * √(n : ℝ)) := by
    rw [stepConst]; ring
  have hMb0 : (0 : ℝ)
      ≤ √2 * (barrierConstBound vmin vmax (1001 + c₀) * (1001 + c₀) * (√2 / √(2 * π * vmin)))
        / (Λ ^ 2 * √(n : ℝ)) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
      (mul_nonneg (mul_nonneg (barrierConstBound_nonneg hvmin (by linarith)) (by linarith))
        (by positivity))) (by positivity)
  have hTb0 : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax)
      / (2 * Real.exp (-(1 : ℝ) / 2)) * barrierConstBound vmin vmax (1000 + c₀)
      / (Λ ^ 2 * √(n : ℝ)) := by
    have h3 : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ := maxWindowConstBound_nonneg hvmin hc₀
    exact div_nonneg (mul_nonneg (div_nonneg (mul_nonneg h3 (Real.sqrt_nonneg _))
      (by positivity)) (barrierConstBound_nonneg hvmin (by linarith))) (by positivity)
  rw [abs_le, hsplit]
  exact ⟨by linarith, by linarith⟩

/-! ### Probability Lemma 1

The chain of one-step estimates, summed.  The point of the iterated-logarithm scale is that the
per-level errors `1/(√n log_i² n)` **add** rather than compound, and decay geometrically, so the
accumulated error is a constant multiple of the last term rather than `log* n` times it. -/

/-- **Probability Lemma 1.**  Along a chain of real freeze points `L 0 ≥ L 1 ≥ ⋯ ≥ L k` — Harper’s
`(log_i n)²⁰` — with integer split times `N i` bracketing `L (i+1)`, the curved-barrier probability
moves by at most `stepConst · (1 - e⁻²)⁻¹ / (√n · log_k² n)`.

The hypotheses are the standing ones of Harper’s induction: the barrier height is at most
`1000 log_k n`; the freeze points decrease; each is at least the twentieth power of its level; the
logarithm of the previous one is at most `c₀/10` times the level; the split time brackets the new
freeze point and lies before the midpoint; and the suffix is long enough for the floor `T = log⁴`
of the tail range.  At Harper’s `L i = (log_i n)²⁰` and `N i = ⌊(log_{i+1} n)²⁰⌋` the first four
hold with equality or by definition, with `c₀ = 200` exact.  One hypothesis `a ≤ 1000 log_k n`
suffices because `RMF.iterLog_le_iterLog` makes the last level the binding one. -/
theorem IsGaussianWalk.abs_curvedBarrierProb_sub_iterLog (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a c₀ : ℝ} (ha : 0 ≤ a) (hc₀ : 0 ≤ c₀)
    {L : ℕ → ℝ} {N : ℕ → ℕ} {k n : ℕ}
    (hgood : IterLogGood k (n : ℝ)) (haΛ : a ≤ 1000 * iterLog k (n : ℝ))
    (hmono : ∀ i < k, L (i + 1) ≤ L i)
    (hlogL : ∀ i < k, 10 * Real.log (L i) ≤ c₀ * iterLog (i + 1) (n : ℝ))
    (hpow : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 20 ≤ L (i + 1))
    (hsplitL : ∀ i < k, ((N i : ℕ) : ℝ) ≤ L (i + 1))
    (hsplitU : ∀ i < k, L (i + 1) ≤ ((N i : ℕ) : ℝ) + 1)
    (hNone : ∀ i < k, 1 ≤ N i)
    (hhalf : ∀ i < k, 2 * N i ≤ n)
    (hfloor : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 4 ≤ √(((n - N i : ℕ) : ℝ) * vmin)) :
    |curvedBarrierProb μ G a (L 0) n - curvedBarrierProb μ G a (L k) n|
      ≤ stepConst vmin vmax c₀ * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by simpa using hgood.one_le (Nat.zero_le k)
  have hR : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  refine abs_sub_telescope_iterLog (f := fun i => curvedBarrierProb μ G a (L i) n)
    (stepConst_nonneg hvmin hc₀) hR hgood ?_
  intro i hi
  have hΛ : (1 : ℝ) ≤ iterLog (i + 1) (n : ℝ) := hgood.one_le hi
  have haΛi : a ≤ 1000 * iterLog (i + 1) (n : ℝ) := by
    have := iterLog_le_iterLog hi hgood
    linarith
  have key := h.abs_curvedBarrierProb_sub_le ⟨hvmin, hlo, hhi⟩ hΛ ha haΛi (hmono i hi) (hlogL i hi)
    (hpow i hi) (hsplitL i hi) (hsplitU i hi) (hNone i hi) (hhalf i hi) (hfloor i hi)
  rwa [mul_comm (iterLog (i + 1) (n : ℝ) ^ 2) (√(n : ℝ))] at key

/-- **Probability Lemma 1, with Harper’s left-hand side.**  When the first freeze point is at or
past `n` the level-`0` probability is the *unfrozen* one, `P(S_j ≤ a + 10 log j for all j ≤ n)`,
because `min{j, L 0} = j` throughout the range.  That is the quantity Harper starts from; with
`L 0 = n²⁰` the hypothesis is automatic.

At `L i = (log_i n)²⁰` this is Harper’s Probability Lemma 1 verbatim, the right-hand side being
`P(S_j ≤ a + 10 log(min{j, (log_k n)²⁰}) for all j ≤ n)`. -/
theorem IsGaussianWalk.abs_measure_forall_le_sub_iterLog (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a c₀ : ℝ} (ha : 0 ≤ a) (hc₀ : 0 ≤ c₀)
    {L : ℕ → ℝ} {N : ℕ → ℕ} {k n : ℕ}
    (hgood : IterLogGood k (n : ℝ)) (haΛ : a ≤ 1000 * iterLog k (n : ℝ))
    (hL0 : (n : ℝ) ≤ L 0)
    (hmono : ∀ i < k, L (i + 1) ≤ L i)
    (hlogL : ∀ i < k, 10 * Real.log (L i) ≤ c₀ * iterLog (i + 1) (n : ℝ))
    (hpow : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 20 ≤ L (i + 1))
    (hsplitL : ∀ i < k, ((N i : ℕ) : ℝ) ≤ L (i + 1))
    (hsplitU : ∀ i < k, L (i + 1) ≤ ((N i : ℕ) : ℝ) + 1)
    (hNone : ∀ i < k, 1 ≤ N i)
    (hhalf : ∀ i < k, 2 * N i ≤ n)
    (hfloor : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 4 ≤ √(((n - N i : ℕ) : ℝ) * vmin)) :
    |(μ {ω | ∀ j ≤ n, walk G j ω ≤ a + 10 * Real.log j}).toReal
        - curvedBarrierProb μ G a (L k) n|
      ≤ stepConst vmin vmax c₀ * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  rw [← curvedBarrierProb_of_le (μ := μ) (G := G) (a := a) hL0]
  exact h.abs_curvedBarrierProb_sub_iterLog ⟨hvmin, hlo, hhi⟩ ha hc₀ hgood haΛ hmono hlogL hpow
    hsplitL hsplitU hNone hhalf hfloor

/-! ### Harper’s own freeze points

The theorem above is stated for an arbitrary admissible chain, which is what the induction needs.
Instantiating it at Harper’s own `L i = (log_i n)²⁰`, with split times `N i = ⌊(log_{i+1} n)²⁰⌋`,
gives Probability Lemma 1 as Harper states it — and, just as importantly, shows the hypotheses
of the general form are **not vacuous**.

Seven of the nine hold with equality, by definition, or from `⌊·⌋`.  In particular
`10 log((log_i n)²⁰) = 200 log_{i+1} n` **on the nose**, so `c₀ = 200` is exactly Harper’s
constant.  Only two survive, and both say the same thing: `n` is past an absolute threshold. -/

/-- **Probability Lemma 1, as Harper states it.**  For a Gaussian walk with variances in
`[v₋, v₊]`, `0 ≤ a ≤ 1000 log_k n`, and `n` large enough that `2(log n)²⁰ ≤ n` and
`2(log n)⁸ ≤ n v₋`,

`| P(S_j ≤ a + 10 log j ∀ j ≤ n) − P(S_j ≤ a + 10 log(min{j, (log_k n)²⁰}) ∀ j ≤ n) |`
`   ≤ C(v₋,v₊) / (√n · log_k² n)`.

The two size conditions are the only place "`n` large" enters; everything else in the chain is an
identity. -/
theorem IsGaussianWalk.abs_measure_forall_le_sub_iterLog_pow (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a : ℝ} (ha : 0 ≤ a) {k n : ℕ}
    (hgood : IterLogGood k (n : ℝ)) (haΛ : a ≤ 1000 * iterLog k (n : ℝ))
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ))
    (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin) :
    |(μ {ω | ∀ j ≤ n, walk G j ω ≤ a + 10 * Real.log j}).toReal
        - curvedBarrierProb μ G a (iterLog k (n : ℝ) ^ 20) n|
      ≤ stepConst vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by simpa using hgood.one_le (Nat.zero_le k)
  -- every level of the chain sits below the first
  have hle1 : ∀ i, i < k → iterLog (i + 1) (n : ℝ) ≤ Real.log n := by
    intro i hi
    have h2 := iterLog_le_iterLog (Nat.succ_le_succ (Nat.zero_le i)) (hgood.mono hi)
    rwa [iterLog_one] at h2
  have hpos : ∀ i, i < k → (0 : ℝ) < iterLog (i + 1) (n : ℝ) := fun i hi => hgood.pos hi
  have hpow8 : ∀ i, i < k → ∀ m : ℕ, iterLog (i + 1) (n : ℝ) ^ m ≤ Real.log n ^ m :=
    fun i hi m => pow_le_pow_left₀ (hpos i hi).le (hle1 i hi) m
  -- the split time is before the midpoint
  have hhalfAll : ∀ i < k, 2 * ⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ ≤ n := by
    intro i hi
    have hfl : ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) ≤ iterLog (i + 1) (n : ℝ) ^ 20 :=
      Nat.floor_le (by positivity)
    have hR : (2 : ℝ) * ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      linarith [hpow8 i hi 20]
    exact_mod_cast hR
  refine h.abs_measure_forall_le_sub_iterLog (L := fun i => iterLog i (n : ℝ) ^ 20)
    (N := fun i => ⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊) ⟨hvmin, hlo, hhi⟩ ha (by norm_num) hgood haΛ
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hhalfAll ?_
  · -- the first freeze point is past `n`
    simpa using le_self_pow₀ hn1 (by norm_num)
  · -- the freeze points decrease
    intro i hi
    exact pow_le_pow_left₀ (hpos i hi).le (iterLog_le_iterLog (Nat.le_succ i) (hgood.mono hi)) 20
  · -- `10 log((log_i n)²⁰) = 200 log_{i+1} n`, on the nose
    intro i hi
    rw [Real.log_pow, iterLog_succ]
    push_cast
    linarith
  · -- the new freeze point is the twentieth power of its level, by definition
    intro i _
    exact le_rfl
  · -- `⌊M⌋ ≤ M`
    intro i _
    exact Nat.floor_le (by positivity)
  · -- `M ≤ ⌊M⌋ + 1`
    intro i _
    exact (Nat.lt_floor_add_one _).le
  · -- the split time is at least `1`
    intro i hi
    refine Nat.le_floor ?_
    push_cast
    exact one_le_pow₀ (hgood.one_le hi)
  · -- the suffix is long enough for the floor `T = log⁴`
    intro i hi
    have h4 : (0 : ℝ) < iterLog (i + 1) (n : ℝ) ^ 4 := pow_pos (hpos i hi) 4
    have hhi2 := hhalfAll i hi
    have hcast : ((n - ⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ)
        = (n : ℝ) - ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) :=
      Nat.cast_sub (by omega)
    have hNn : (2 : ℝ) * ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hhi2
    have hNv : ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) * vmin ≤ ((n : ℝ) / 2) * vmin :=
      mul_le_mul_of_nonneg_right (by linarith) hvmin.le
    rw [Real.le_sqrt' h4, hcast]
    linarith [hpow8 i hi 8, hbig2, hNv]

end RMF
