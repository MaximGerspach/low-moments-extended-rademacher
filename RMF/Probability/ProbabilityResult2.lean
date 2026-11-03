/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ProbabilityLemma1Lower

/-!
# Probability Result 2 — the two-sided band

Harper's Probability Result 2 (Harper, arXiv:1703.06654, §3.2) adds a loose lower barrier
`g(j) ≤ −Bj` to Probability Result 1 and caps the upper one at `min{a, Bj}`, and asserts that
neither changes the order:

`P( g(j) ≤ S_j ≤ min{a, Bj} + h(j)  ∀ 1 ≤ j ≤ n )  ≍  min{1, a/√n}`.

Both new barriers are linear in `j`; the asymmetry is in the slope, the upper one tracking the
drift with slope exactly `1` and the lower one loose with slope `-B`.

## The two halves

The **upper** bound is immediate: `min{a, Bj} ≤ a`, so the band event sits inside Probability
Result 1's event and the constant is `RMF.result1Const` unchanged
(`RMF.IsGaussianWalk.measure_bandEvent_le`).

The **lower** bound (`RMF.IsGaussianWalk.le_measure_bandEvent_of_result1Lower`) is Harper's
Appendix A.2, and is the work.  Writing `E` for Result 1's event,
the band event contains `E` minus the paths that break one of the two new constraints at some time
`k`, so

`P(band) ≥ P(E) − ∑_{k=1}^n P(E ∩ B_k)`,   `B_k = {S_k ≤ −Bk} ∪ {S_k ≥ Bk − 10 log k}`.

Result 1's lower bound handles `P(E)`; each `P(E ∩ B_k)` is bounded by splitting the walk at time
`k` (the prefix/suffix factorisation of `RMF.IsGaussianWalk.measure_stat_inter_block`), applying
Result 1's *upper* bound to the suffix, and integrating the result against the law of `S_k`.  Both
families of bad paths sit inside the single set `{|S_k| ≥ Bk/2}` once `B ≥ 20`, so one estimate
covers both.

## The size hypotheses double

Result 1 needs `2 (log n)²⁰ ≤ n` and `2 (log n)⁸ ≤ n v₋`.  Here it gets applied to a *suffix* of
length `m = n − k ≥ n/2`, so the hypotheses are imposed at double strength — `4 (log n)²⁰ ≤ n` and
`4 (log n)⁸ ≤ n v₋` — which is what makes them survive the passage to the half-length suffix.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-! ### The telescoping sum

The bad-path estimate at time `k` comes out as `≪ 1/k²` after the `10 log(k+1)` is absorbed, and
the union bound sums it over `1 ≤ k ≤ n`.  Mathlib has the convergence of `∑ 1/k²` but not a bound
on its partial sums, so here is one, by the telescope `1/k² ≤ 1/(k-1) - 1/k`.
-/

/-- `∑_{k=1}^{n} 1/k² ≤ 2 - 1/n`, the sharp form of the telescope. -/
lemma sum_inv_sq_Icc_le_sub (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hstep : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hn0) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith

/-- `∑_{k=1}^{n} 1/k² ≤ 2`, for every `n`. -/
lemma sum_inv_sq_Icc_le_two (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hinv : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith [sum_inv_sq_Icc_le_sub n hn]

/-! ### The band event

`RMF.bandEvent a B hf g n` is the event of Probability Result 2.  Naming it keeps the statements
readable and makes the two containments — into Result 1's event above, and out of the punctured
version below — single rewrites.
-/

/-- **The band event.**  The walk stays above `g` and below the capped barrier `min{a, Bj} + h(j)`,
for `1 ≤ j ≤ n`. -/
def bandEvent (G : ℕ → Ω → ℝ) (a B : ℝ) (hf g : ℕ → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j, 1 ≤ j → j ≤ n → g j ≤ walk G j ω ∧ walk G j ω ≤ min a (B * j) + hf j}

/-- **Probability Result 1's event**, the upper barrier alone: `S_j ≤ a + h(j)` for `1 ≤ j ≤ n`. -/
def upperEvent (G : ℕ → Ω → ℝ) (a : ℝ) (hf : ℕ → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The band sits inside Result 1's event.**  Capping the barrier at `min{a, Bj}` only lowers it,
and the lower barrier only removes paths. -/
lemma bandEvent_subset_upperEvent (G : ℕ → Ω → ℝ) (a B : ℝ) (hf g : ℕ → ℝ) (n : ℕ) :
    bandEvent G a B hf g n ⊆ upperEvent G a hf n := fun _ hω j hj1 hjn =>
  le_trans (hω j hj1 hjn).2 (by linarith [min_le_left a (B * (j : ℝ))])

/-! ### The upper bound

One containment and Probability Result 1.  Only the one-sided hypothesis `h(j) ≤ 10 log j` is used,
and the constant is `RMF.result1Const` unchanged — adding barriers cannot raise the probability, so
Result 2's upper constant is literally Result 1's.
-/

/-- **Probability Result 2, upper bound.**  Immediate from Probability Result 1, since
`min{a, Bj} ≤ a`. -/
theorem IsGaussianWalk.measure_bandEvent_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a B : ℝ} (ha : 1000 ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf g : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j) :
    (μ (bandEvent G a B hf g n)).toReal ≤ result1Const vmin vmax * min 1 (a / √(n : ℝ)) :=
  le_trans
    (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (bandEvent_subset_upperEvent G a B hf g n)))
    (h.measure_forall_le_le hv ha hn hbig hbig2 hhf)

/-! ### The estimate at one time `k`

Fix `k` and let `T = Bk/2`.  The paths that break one of the two new constraints at time `k` all
have `|S_k| ≥ T`, and they still respect Result 1's barrier after time `k`; that is
`RMF.badSet`.  The estimate for it has three moves:

* **split at `k`** — `RMF.IsGaussianWalk.measure_endpoint_inter_block` turns the measure into an
  integral of the suffix probability against the law of `S_k`, which is a Gaussian on `ℝ`;
* **Result 1 on the suffix** — `RMF.suffixSet_eq_shift` makes the suffix event a barrier event for
  the shifted walk, and Result 1's *upper* bound applies at level `a + |u| + 10 log(k+1)`;
* **integrate** — the resulting weight is `≤ K·(1 + |u|)` on the region `|u| ≥ T`, and
  `RMF.lintegral_tail_one_add_abs_le` bounds its integral by an eighth absolute moment.
-/

/-- **The bad set at time `k`.**  Paths whose position at time `k` is at distance at least `T` from
the origin, and which respect the barrier `β` after time `k`.  Result 1's barrier *before* time `k`
is deliberately dropped: it is not needed, and dropping it makes the split a two-factor one. -/
def badSet (G : ℕ → Ω → ℝ) (β : ℕ → ℝ) (T : ℝ) (k n : ℕ) : Set Ω :=
  {ω | T ≤ |walk G k ω|} ∩ {ω | ∀ j, k < j → j ≤ n → walk G j ω ≤ β j}

/-- **The bad set, split at time `k`.**  The suffix probability is read at the shifted indices, so
that Probability Result 1 applies to it directly. -/
theorem IsGaussianWalk.measure_badSet_eq (h : IsGaussianWalk G v μ) (β : ℕ → ℝ) (T : ℝ)
    (k n : ℕ) :
    μ (badSet G β T k n)
      = ∫⁻ u in {u : ℝ | T ≤ |u|},
          μ {ω | ∀ i, 1 ≤ i → i ≤ n - k →
              walk (fun m => G (m + k)) i ω ≤ β (k + i) - u} ∂(μ.map (walk G k)) := by
  have hA : MeasurableSet {u : ℝ | T ≤ |u|} :=
    measurableSet_le measurable_const measurable_id.abs
  have hE : MeasurableSet {q : ℝ × (ℕ → ℝ) | q.2 ∈ suffixSet β k n (fun _ => q.1)} := by
    have hrw : {q : ℝ × (ℕ → ℝ) | q.2 ∈ suffixSet β k n (fun _ => q.1)}
        = ⋂ j ∈ Set.Ioc k n, {q : ℝ × (ℕ → ℝ) | q.2 j ≤ β j - q.1} := by
      ext q
      simp only [suffixSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Ioc]
      exact ⟨fun hq j hj => hq j hj.1 hj.2, fun hq j h1 h2 => hq j ⟨h1, h2⟩⟩
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le ((measurable_pi_apply j).comp measurable_snd)
        (measurable_const.sub measurable_fst)
  have key := h.measure_endpoint_inter_block k n
    (E := fun u => suffixSet β k n (fun _ => u)) hA hE
  have hsuf : {ω | (blockSums k n fun i => G i ω) ∈ suffixSet β k n (fun _ => walk G k ω)}
      = {ω | ∀ j, k < j → j ≤ n → walk G j ω ≤ β j} := by
    ext ω
    simp only [suffixSet, Set.mem_setOf_eq]
    constructor
    · intro hq j hkj hjn
      have := hq j hkj hjn
      rw [blockSums_comp G hkj.le hjn ω] at this
      linarith
    · intro hq j hkj hjn
      rw [blockSums_comp G hkj.le hjn ω]
      linarith [hq j hkj hjn]
  have hpre : {ω | walk G k ω ∈ {u : ℝ | T ≤ |u|}} = {ω | T ≤ |walk G k ω|} := rfl
  rw [hsuf, hpre] at key
  rw [badSet, key]
  refine lintegral_congr fun u => congrArg μ ?_
  exact suffixSet_eq_shift G β (fun _ => u)

/-- **The suffix probability, by Probability Result 1.**  After the split the suffix is a barrier
event for the shifted walk at level `a - u`.  Raising it to `a + |u| + 10 log(k+1)` puts it in the
form Result 1's upper bound takes: the perturbation the shifted walk sees at its own step `i` is
`h(k+i) - 10 log(k+1) ≤ 10 log i`, since `k + i ≤ (k+1) i`.  The size conditions are imposed at `n`
and used at `m = n - k ≥ n/2`, which is what the doubled constant `4` is for. -/
theorem IsGaussianWalk.measure_shift_barrier_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a : ℝ} (ha : 1000 ≤ a) {k n : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j) (u : ℝ) :
    (μ {ω | ∀ i, 1 ≤ i → i ≤ n - k →
        walk (fun m => G (m + k)) i ω ≤ (a + hf (k + i)) - u}).toReal
      ≤ result1Const vmin vmax
          * min 1 ((a + |u| + 10 * Real.log ((k : ℝ) + 1)) / √(((n - k : ℕ)) : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hkln : k ≤ n := by omega
  have hm : 1 ≤ n - k := by omega
  have hmn : n - k ≤ n := by omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmR : (1 : ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans hm hmn)
  -- the suffix has at least half the length
  have hhalf : (n : ℝ) / 2 ≤ ((n - k : ℕ) : ℝ) := by
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkln
    have hkn2 : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    rw [hcast]; linarith
  -- the size conditions transfer to the suffix
  have hlogm : Real.log ((n - k : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by linarith) (by exact_mod_cast hmn)
  have hlogm0 : (0 : ℝ) ≤ Real.log ((n - k : ℕ) : ℝ) := Real.log_nonneg hmR
  have hbigm : 2 * Real.log ((n - k : ℕ) : ℝ) ^ 20 ≤ ((n - k : ℕ) : ℝ) := by
    have := pow_le_pow_left₀ hlogm0 hlogm 20
    linarith
  have hbig2m : 2 * Real.log ((n - k : ℕ) : ℝ) ^ 8 ≤ ((n - k : ℕ) : ℝ) * vmin := by
    have h8 := pow_le_pow_left₀ hlogm0 hlogm 8
    have hvm : (n : ℝ) / 2 * vmin ≤ ((n - k : ℕ) : ℝ) * vmin :=
      mul_le_mul_of_nonneg_right hhalf hvmin.le
    linarith
  -- the raised level, and the perturbation it leaves
  have hc0 : (0 : ℝ) ≤ 10 * Real.log ((k : ℝ) + 1) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    linarith [Real.log_nonneg h1]
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have ha' : (1000 : ℝ) ≤ a + |u| + 10 * Real.log ((k : ℝ) + 1) := by linarith
  have hsub : {ω | ∀ i, 1 ≤ i → i ≤ n - k →
        walk (fun t => G (t + k)) i ω ≤ (a + hf (k + i)) - u}
      ⊆ {ω | ∀ i, 1 ≤ i → i ≤ n - k →
        walk (fun t => G (t + k)) i ω
          ≤ (a + |u| + 10 * Real.log ((k : ℝ) + 1))
              + (hf (k + i) - 10 * Real.log ((k : ℝ) + 1))} := by
    intro ω hω i hi1 hi
    have := hω i hi1 hi
    linarith [neg_abs_le u]
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)) ?_
  -- the shifted perturbation respects Result 1's envelope
  have hhf' : ∀ i, 1 ≤ i → i ≤ n - k →
      hf (k + i) - 10 * Real.log ((k : ℝ) + 1) ≤ 10 * Real.log i := by
    intro i hi1 hi
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hki : k + i ≤ n := by omega
    have hbase := hhf (k + i) (by omega) hki
    have hcast : ((k + i : ℕ) : ℝ) = (k : ℝ) + (i : ℝ) := by push_cast; ring
    rw [hcast] at hbase
    have hprod : (k : ℝ) + (i : ℝ) ≤ ((k : ℝ) + 1) * (i : ℝ) := by nlinarith
    have hlog : Real.log ((k : ℝ) + (i : ℝ)) ≤ Real.log (((k : ℝ) + 1) * (i : ℝ)) :=
      Real.log_le_log (by linarith) hprod
    rw [Real.log_mul (by linarith) (by linarith)] at hlog
    linarith
  exact (h.shift k).measure_forall_le_le ⟨hvmin, fun i => hlo (i + k), fun i => hhi (i + k)⟩
    ha' hm hbigm hbig2m hhf'

/-- **The suffix probability, against the reference scale.**  The bound of
`RMF.IsGaussianWalk.measure_shift_barrier_le`, with the excess barrier height
`(a + |u| + 10 log(k+1))/a` pulled out of the `min` (`RMF.min_one_mul_le`) and the suffix length
`m ≥ n/2` traded for `n` at the cost of a `√2`.  The factor multiplying `min {1, a/√n}` is
`(1 + 10 log(k+1))·(1 + |u|)`: summable against `1/k³`, integrable against the law of `S_k`. -/
theorem IsGaussianWalk.measure_shift_barrier_le_weight (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a : ℝ} (ha : 1000 ≤ a) {k n : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j) (u : ℝ) :
    (μ {ω | ∀ i, 1 ≤ i → i ≤ n - k →
        walk (fun m => G (m + k)) i ω ≤ (a + hf (k + i)) - u}).toReal
      ≤ result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1))
          * min 1 (a / √(n : ℝ)) * (1 + |u|) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hkln : k ≤ n := by omega
  have hm : 1 ≤ n - k := by omega
  have hmR : (1 : ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hsm : (0 : ℝ) < √(((n - k : ℕ)) : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have ha0 : (0 : ℝ) < a := by linarith
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hc0 : (0 : ℝ) ≤ 10 * Real.log ((k : ℝ) + 1) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    linarith [Real.log_nonneg hk1]
  have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have hmin0 : (0 : ℝ) ≤ min 1 (a / √(n : ℝ)) := le_min zero_le_one (by positivity)
  have hA1 : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  -- the suffix has at least half the length, so its `√m` is worth a `√n/√2`
  have hhalf : (n : ℝ) / 2 ≤ ((n - k : ℕ) : ℝ) := by
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkln
    have hkn2 : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    rw [hcast]; linarith
  have hsq : √(n : ℝ) ≤ √2 * √(((n - k : ℕ)) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hstep1 : a / √(((n - k : ℕ)) : ℝ) ≤ √2 * (a / √(n : ℝ)) := by
    rw [div_le_iff₀ hsm]
    have hkey : a * √(n : ℝ) ≤ a * (√2 * √(((n - k : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq ha0.le
    rw [mul_comm (√2) (a / √(n : ℝ)), div_mul_eq_mul_div, div_mul_eq_mul_div,
      le_div_iff₀ hsn]
    nlinarith
  -- pull the excess barrier height out of the `min`
  have hlam1 : (1 : ℝ) ≤ (a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a := by
    rw [le_div_iff₀ ha0]; linarith
  have hlam0 : (0 : ℝ) ≤ (a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a := by linarith
  have hrw : (a + |u| + 10 * Real.log ((k : ℝ) + 1)) / √(((n - k : ℕ)) : ℝ)
      = ((a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a) * (a / √(((n - k : ℕ)) : ℝ)) := by
    field_simp
  have hlam2 : (a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a
      ≤ (1 + 10 * Real.log ((k : ℝ) + 1)) * (1 + |u|) := by
    rw [div_le_iff₀ ha0]
    nlinarith [mul_nonneg hc0 hu0, mul_nonneg hc0 (by linarith : (0 : ℝ) ≤ a - 1),
      mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ a - 1)]
  have hchain : min 1 ((a + |u| + 10 * Real.log ((k : ℝ) + 1)) / √(((n - k : ℕ)) : ℝ))
      ≤ (1 + 10 * Real.log ((k : ℝ) + 1)) * (1 + |u|) * (√2 * min 1 (a / √(n : ℝ))) := by
    rw [hrw]
    calc min 1 ((a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a * (a / √(((n - k : ℕ)) : ℝ)))
        ≤ (a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a * min 1 (a / √(((n - k : ℕ)) : ℝ)) :=
          min_one_mul_le hlam1
      _ ≤ (a + |u| + 10 * Real.log ((k : ℝ) + 1)) / a * (√2 * min 1 (a / √(n : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (le_trans (min_le_min le_rfl hstep1) (min_one_mul_le hs2)) hlam0
      _ ≤ (1 + 10 * Real.log ((k : ℝ) + 1)) * (1 + |u|) * (√2 * min 1 (a / √(n : ℝ))) :=
          mul_le_mul_of_nonneg_right hlam2 (by positivity)
  refine le_trans (h.measure_shift_barrier_le ⟨hvmin, hlo, hhi⟩ ha hk hkn hbig hbig2 hhf u) ?_
  calc result1Const vmin vmax
        * min 1 ((a + |u| + 10 * Real.log ((k : ℝ) + 1)) / √(((n - k : ℕ)) : ℝ))
      ≤ result1Const vmin vmax
          * ((1 + 10 * Real.log ((k : ℝ) + 1)) * (1 + |u|) * (√2 * min 1 (a / √(n : ℝ)))) :=
        mul_le_mul_of_nonneg_left hchain (by linarith)
    _ = result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1))
          * min 1 (a / √(n : ℝ)) * (1 + |u|) := by ring

/-- **The constant of the one-step estimate**, `5376·√2·result1Const v₋ v₊·E|N(0,1)|⁸·v₊⁴`.
`5376 = 256 · 21`: the `256` is `2 · 2⁷` from the eighth-moment tail bound at `T = Bk/2`, and the
`21` is the crude `1 + 10 log(k+1) ≤ 21k`. -/
noncomputable def result2StepConst (vmin vmax : ℝ) : ℝ :=
  5376 * √2 * result1Const vmin vmax * absMomentConst 8 * vmax ^ 4

lemma result2StepConst_nonneg (vmin vmax : ℝ) : 0 ≤ result2StepConst vmin vmax := by
  have hA1 : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  have hC8 : (0 : ℝ) ≤ absMomentConst 8 := absMomentConst_nonneg 8
  rw [result2StepConst]
  positivity

/-- **The estimate at one time `k`.**  For `2k ≤ n` the mass of the paths that break a new
constraint at time `k` is at most `C · min{1, a/√n} / (B⁷ k²)` — summable in `k`, and small in `B`.

The `1/k²` is what the union bound needs.  It comes from `1/k³` in the tail bound (eighth moment
against `T = Bk/2` and `V ≤ k v₊`) against `21k` from the shifted barrier's `10 log(k+1)`. -/
theorem IsGaussianWalk.measure_badSet_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a B : ℝ} (ha : 1000 ≤ a) (hB : 20 ≤ B) {k n : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j) :
    (μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)).toReal
      ≤ result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / (B ^ 7 * (k : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have ha0 : (0 : ℝ) < a := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hT1 : (1 : ℝ) ≤ B * (k : ℝ) / 2 := by nlinarith
  have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have hC8 : (0 : ℝ) ≤ absMomentConst 8 := absMomentConst_nonneg 8
  have hA1 : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  have hmin0 : (0 : ℝ) ≤ min 1 (a / √(n : ℝ)) := le_min zero_le_one (by positivity)
  have hc0 : (0 : ℝ) ≤ 10 * Real.log ((k : ℝ) + 1) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    linarith [Real.log_nonneg hk1]
  -- the weight in front of `1 + |u|`
  have hW0 : (0 : ℝ) ≤ result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1))
      * min 1 (a / √(n : ℝ)) := by
    have h1 : (0 : ℝ) ≤ result1Const vmin vmax * √2 := by positivity
    have h2 : (0 : ℝ) ≤ result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1)) :=
      mul_nonneg h1 (by linarith)
    exact mul_nonneg h2 hmin0
  -- the first-block variance
  have hV0 : (0 : ℝ) ≤ ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hV : ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ≤ (k : ℝ) * vmax := by
    push_cast
    calc ∑ mm ∈ Finset.range k, (v mm : ℝ) ≤ ∑ _mm ∈ Finset.range k, vmax :=
          Finset.sum_le_sum fun mm _ => hhi mm
      _ = (k : ℝ) * vmax := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the pointwise bound, in `ℝ≥0∞`
  have hpt : ∀ u : ℝ, μ {ω | ∀ i, 1 ≤ i → i ≤ n - k →
      walk (fun mm => G (mm + k)) i ω ≤ (a + hf (k + i)) - u}
      ≤ ENNReal.ofReal (result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1))
            * min 1 (a / √(n : ℝ)))
          * ENNReal.ofReal (1 + |u|) := by
    intro u
    rw [← ENNReal.ofReal_mul hW0]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (mul_nonneg hW0 (by positivity))).2
      (h.measure_shift_barrier_le_weight ⟨hvmin, hlo, hhi⟩ ha hk hkn hbig hbig2 hhf u)
  -- integrate
  have hmain : μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)
      ≤ ENNReal.ofReal ((result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1))
            * min 1 (a / √(n : ℝ)))
          * (2 * absMomentConst 8 * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4
              / (B * (k : ℝ) / 2) ^ 7)) := by
    rw [h.measure_badSet_eq, h.map_walk k]
    calc ∫⁻ u in {u : ℝ | B * (k : ℝ) / 2 ≤ |u|},
            μ {ω | ∀ i, 1 ≤ i → i ≤ n - k →
              walk (fun mm => G (mm + k)) i ω ≤ (a + hf (k + i)) - u}
            ∂(gaussianReal 0 (∑ mm ∈ Finset.range k, v mm))
        ≤ ∫⁻ _u in {u : ℝ | B * (k : ℝ) / 2 ≤ |u|},
            ENNReal.ofReal (result1Const vmin vmax * √2
                * (1 + 10 * Real.log ((k : ℝ) + 1)) * min 1 (a / √(n : ℝ)))
              * ENNReal.ofReal (1 + |_u|)
            ∂(gaussianReal 0 (∑ mm ∈ Finset.range k, v mm)) := lintegral_mono hpt
      _ = ENNReal.ofReal (result1Const vmin vmax * √2
              * (1 + 10 * Real.log ((k : ℝ) + 1)) * min 1 (a / √(n : ℝ)))
            * ∫⁻ u in {u : ℝ | B * (k : ℝ) / 2 ≤ |u|}, ENNReal.ofReal (1 + |u|)
              ∂(gaussianReal 0 (∑ mm ∈ Finset.range k, v mm)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (result1Const vmin vmax * √2
              * (1 + 10 * Real.log ((k : ℝ) + 1)) * min 1 (a / √(n : ℝ)))
            * ENNReal.ofReal (2 * absMomentConst 8
                * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4
                / (B * (k : ℝ) / 2) ^ 7) := by
          gcongr
          exact lintegral_tail_one_add_abs_le _ hT1
      _ = _ := (ENNReal.ofReal_mul hW0).symm
  refine le_trans (ENNReal.toReal_le_of_le_ofReal (by positivity) hmain) ?_
  -- the arithmetic
  have hkey : (1 + 10 * Real.log ((k : ℝ) + 1))
      * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4
      ≤ 21 * (k : ℝ) * ((k : ℝ) ^ 4 * vmax ^ 4) := by
    have hlogk : Real.log ((k : ℝ) + 1) ≤ (k : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1)
      linarith
    have hcle : 1 + 10 * Real.log ((k : ℝ) + 1) ≤ 21 * (k : ℝ) := by linarith
    have h4 : ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4 ≤ ((k : ℝ) * vmax) ^ 4 :=
      pow_le_pow_left₀ hV0 hV 4
    have h4' : ((k : ℝ) * vmax) ^ 4 = (k : ℝ) ^ 4 * vmax ^ 4 := by ring
    rw [h4'] at h4
    have hpow0 : (0 : ℝ) ≤ (k : ℝ) ^ 4 * vmax ^ 4 := by positivity
    calc (1 + 10 * Real.log ((k : ℝ) + 1))
          * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4
        ≤ (1 + 10 * Real.log ((k : ℝ) + 1)) * ((k : ℝ) ^ 4 * vmax ^ 4) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ ≤ 21 * (k : ℝ) * ((k : ℝ) ^ 4 * vmax ^ 4) := mul_le_mul_of_nonneg_right hcle hpow0
  have hAsn : (0 : ℝ) ≤ result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ)) := by
    have : (0 : ℝ) ≤ result1Const vmin vmax * √2 := by positivity
    exact mul_nonneg this hmin0
  have hT7 : (0 : ℝ) < (B * (k : ℝ) / 2) ^ 7 := by positivity
  rw [show (result1Const vmin vmax * √2 * (1 + 10 * Real.log ((k : ℝ) + 1))
        * min 1 (a / √(n : ℝ)))
      * (2 * absMomentConst 8 * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4
          / (B * (k : ℝ) / 2) ^ 7)
      = (result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ))) * (2 * absMomentConst 8)
        * ((1 + 10 * Real.log ((k : ℝ) + 1))
            * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4) / (B * (k : ℝ) / 2) ^ 7 from by
    ring]
  rw [div_le_div_iff₀ hT7 (by positivity), result2StepConst]
  have hmul : (result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ))) * (2 * absMomentConst 8)
      * ((1 + 10 * Real.log ((k : ℝ) + 1))
          * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4)
      ≤ (result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ))) * (2 * absMomentConst 8)
        * (21 * (k : ℝ) * ((k : ℝ) ^ 4 * vmax ^ 4)) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hBk : (0 : ℝ) < B ^ 7 * (k : ℝ) ^ 2 := by positivity
  have hrest : (result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ))) * (2 * absMomentConst 8)
        * (21 * (k : ℝ) * ((k : ℝ) ^ 4 * vmax ^ 4)) * (B ^ 7 * (k : ℝ) ^ 2)
      = 5376 * √2 * result1Const vmin vmax * absMomentConst 8 * vmax ^ 4
          * min 1 (a / √(n : ℝ)) * (B * (k : ℝ) / 2) ^ 7 := by
    field_simp
    ring
  calc (result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ))) * (2 * absMomentConst 8)
        * ((1 + 10 * Real.log ((k : ℝ) + 1))
            * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4) * (B ^ 7 * (k : ℝ) ^ 2)
      ≤ (result1Const vmin vmax * √2 * min 1 (a / √(n : ℝ))) * (2 * absMomentConst 8)
          * (21 * (k : ℝ) * ((k : ℝ) ^ 4 * vmax ^ 4)) * (B ^ 7 * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmul hBk.le
    _ = _ := hrest

/-- **The estimate at one time `k`, past the midpoint.**  For `2k > n` the suffix is too short for
Probability Result 1 — but it does not have to be used.  Bounding the suffix probability by `1`
leaves the Gaussian tail alone, and that is already small enough. -/
theorem IsGaussianWalk.measure_badSet_le_tail (h : IsGaussianWalk G v μ) (β : ℕ → ℝ) {T : ℝ}
    (hT : 1 ≤ T) (k n : ℕ) :
    (μ (badSet G β T k n)).toReal
      ≤ 2 * absMomentConst 8 * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4 / T ^ 7 := by
  have hC8 : (0 : ℝ) ≤ absMomentConst 8 := absMomentConst_nonneg 8
  have hV0 : (0 : ℝ) ≤ ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hT0 : (0 : ℝ) < T := by linarith
  have hA : MeasurableSet {u : ℝ | T ≤ |u|} :=
    measurableSet_le measurable_const measurable_id.abs
  have hstep : μ (badSet G β T k n)
      ≤ ENNReal.ofReal (2 * absMomentConst 8
          * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4 / T ^ 7) := by
    calc μ (badSet G β T k n) ≤ μ {ω | T ≤ |walk G k ω|} := measure_mono Set.inter_subset_left
      _ = (μ.map (walk G k)) {u : ℝ | T ≤ |u|} := by
          rw [Measure.map_apply (h.measurable_walk k) hA]; rfl
      _ = gaussianReal 0 (∑ mm ∈ Finset.range k, v mm) {u : ℝ | T ≤ |u|} := by rw [h.map_walk k]
      _ = ∫⁻ _u in {u : ℝ | T ≤ |u|}, 1
            ∂(gaussianReal 0 (∑ mm ∈ Finset.range k, v mm)) := (setLIntegral_one _).symm
      _ ≤ ∫⁻ u in {u : ℝ | T ≤ |u|}, ENNReal.ofReal (1 + |u|)
            ∂(gaussianReal 0 (∑ mm ∈ Finset.range k, v mm)) := by
          refine lintegral_mono fun u => ?_
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
          exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg u])
      _ ≤ _ := lintegral_tail_one_add_abs_le _ hT
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hstep

/-- **The estimate at one time `k`, uniformly in `k`.**  Both branches land on the same bound, so
the union bound has a single `∑ 1/k²` to sum.  Past the midpoint the constant is smaller — the
`∑ 1/k³` there is traded for `√n · min{1, a/√n} ≥ 1` and `√n ≤ √2 k`, which costs one power of `k`
and a `√2`. -/
theorem IsGaussianWalk.measure_badSet_le_uniform (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a B : ℝ} (ha : 1000 ≤ a) (hB : 20 ≤ B) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j) :
    (μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)).toReal
      ≤ result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / (B ^ 7 * (k : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  rcases le_or_gt (2 * k) n with h2 | h2
  · exact h.measure_badSet_le ⟨hvmin, hlo, hhi⟩ ha hB hk h2 hbig hbig2 hhf
  -- past the midpoint: bound the suffix probability by `1`
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hB0 : (0 : ℝ) < B := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.2 hnR
  have hT1 : (1 : ℝ) ≤ B * (k : ℝ) / 2 := by nlinarith
  have hC8 : (0 : ℝ) ≤ absMomentConst 8 := absMomentConst_nonneg 8
  have hA1 : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have hV0 : (0 : ℝ) ≤ ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hV : ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ≤ (k : ℝ) * vmax := by
    push_cast
    calc ∑ mm ∈ Finset.range k, (v mm : ℝ) ≤ ∑ _mm ∈ Finset.range k, vmax :=
          Finset.sum_le_sum fun mm _ => hhi mm
      _ = (k : ℝ) * vmax := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 : ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 * vmax ^ 4 := by
    have := pow_le_pow_left₀ hV0 hV 4
    calc ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4 ≤ ((k : ℝ) * vmax) ^ 4 := this
      _ = (k : ℝ) ^ 4 * vmax ^ 4 := by ring
  -- the reference scale is at least `1/√n`, and past the midpoint `√n ≤ √2 k`
  have hminlow : 1 / √(n : ℝ) ≤ min 1 (a / √(n : ℝ)) := by
    refine le_min ?_ ?_
    · rw [div_le_one hsn]; exact hsn1
    · exact div_le_div_of_nonneg_right (by linarith) hsn.le
  have hmin0 : (0 : ℝ) ≤ min 1 (a / √(n : ℝ)) := le_min zero_le_one (by positivity)
  have hnk : (n : ℝ) ≤ 2 * (k : ℝ) := by
    have : n ≤ 2 * k := by omega
    exact_mod_cast this
  have hsq : √(n : ℝ) ≤ √2 * (k : ℝ) := by
    have hstep : √(n : ℝ) ≤ √2 * √(k : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hnk
    have hkk : √(k : ℝ) ≤ (k : ℝ) := Real.sqrt_le_self_iff.2 (Or.inr hkR)
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  have hkey : (1 : ℝ) ≤ √2 * (k : ℝ) * min 1 (a / √(n : ℝ)) := by
    have h1 : (1 : ℝ) ≤ √(n : ℝ) * min 1 (a / √(n : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hminlow hsn.le
      rw [mul_one_div, div_self (ne_of_gt hsn)] at this
      linarith
    nlinarith
  refine le_trans (h.measure_badSet_le_tail (fun j => a + hf j) hT1 k n) ?_
  have hT7 : (0 : ℝ) < (B * (k : ℝ) / 2) ^ 7 := by positivity
  have hBk3 : (0 : ℝ) < B ^ 7 * (k : ℝ) ^ 3 := by positivity
  have hBk2 : (0 : ℝ) < B ^ 7 * (k : ℝ) ^ 2 := by positivity
  have hstep1 : 2 * absMomentConst 8 * ((∑ mm ∈ Finset.range k, v mm : ℝ≥0) : ℝ) ^ 4
        / (B * (k : ℝ) / 2) ^ 7
      ≤ 256 * absMomentConst 8 * vmax ^ 4 / (B ^ 7 * (k : ℝ) ^ 3) := by
    rw [div_le_div_iff₀ hT7 hBk3,
      show (B * (k : ℝ) / 2) ^ 7 = B ^ 7 * (k : ℝ) ^ 7 / 128 from by ring]
    nlinarith [mul_le_mul_of_nonneg_left h4
      (show (0 : ℝ) ≤ 2 * absMomentConst 8 * (B ^ 7 * (k : ℝ) ^ 3) by positivity)]
  have hstep2 : 256 * absMomentConst 8 * vmax ^ 4 / (B ^ 7 * (k : ℝ) ^ 3)
      ≤ 256 * √2 * absMomentConst 8 * vmax ^ 4 * min 1 (a / √(n : ℝ))
          / (B ^ 7 * (k : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hBk3 hBk2]
    nlinarith [mul_le_mul_of_nonneg_left hkey
      (show (0 : ℝ) ≤ 256 * absMomentConst 8 * vmax ^ 4 * (B ^ 7 * (k : ℝ) ^ 2) by positivity)]
  have hstep3 : 256 * √2 * absMomentConst 8 * vmax ^ 4 * min 1 (a / √(n : ℝ))
        / (B ^ 7 * (k : ℝ) ^ 2)
      ≤ result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / (B ^ 7 * (k : ℝ) ^ 2) := by
    refine div_le_div_of_nonneg_right ?_ hBk2.le
    rw [result2StepConst]
    have hfac : (0 : ℝ) ≤ √2 * absMomentConst 8 * vmax ^ 4 * min 1 (a / √(n : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hC8) (by positivity)) hmin0
    calc 256 * √2 * absMomentConst 8 * vmax ^ 4 * min 1 (a / √(n : ℝ))
        = 256 * (√2 * absMomentConst 8 * vmax ^ 4 * min 1 (a / √(n : ℝ))) := by ring
      _ ≤ (5376 * result1Const vmin vmax)
            * (√2 * absMomentConst 8 * vmax ^ 4 * min 1 (a / √(n : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hfac
      _ = 5376 * √2 * result1Const vmin vmax * absMomentConst 8 * vmax ^ 4
            * min 1 (a / √(n : ℝ)) := by ring
  linarith

/-! ### The lower bound

Harper's Appendix A.2.  The slope `B` is produced together with the bound, because the two are
inseparable: `B` has to be large enough that the accumulated mass of the bad paths falls below half
of Probability Result 1's lower bound, and how large that is depends on the variance bounds through
Result 1's own constants.
-/

/-- **The threshold on `a` for Probability Result 2**, `max 1000 (result1Threshold v₋ v₊)`.
The upper half needs `1000 ≤ a`, Probability Result 1's upper threshold; the lower half needs
Result 1's lower threshold, where the iterated-logarithm induction bottoms out. -/
noncomputable def result2Threshold (vmin vmax : ℝ) : ℝ :=
  max 1000 (result1Threshold vmin vmax)

/-- **The threshold of Probability Result 2 at a lower threshold `R` of Result 1**,
`max 1000 R`; `RMF.result2Threshold` is the case `R = RMF.result1Threshold`. -/
noncomputable def result2ThresholdOf (R : ℝ) : ℝ := max 1000 R

lemma le_result2ThresholdOf (R : ℝ) : (1000 : ℝ) ≤ result2ThresholdOf R := le_max_left _ _

lemma le_result2ThresholdOf_right (R : ℝ) : R ≤ result2ThresholdOf R := le_max_right _ _

/-! ### The union bound

`RMF.breakSet G B k` collects the paths that break one of the two new constraints at time `k`.  A
path in Result 1's event that breaks none of them is in the band, and a path in Result 1's event
that breaks one of them is in `RMF.badSet` — so the union bound turns the estimate of the previous
section into the lower bound.
-/

/-- **The paths that break a new constraint at time `k`**: either below the lower barrier, or above
the cap.  A path above the cap and below Result 1's barrier has `Sₖ > Bk + h(k) ≥ Bk - 10 log k`. -/
def breakSet (G : ℕ → Ω → ℝ) (B : ℝ) (k : ℕ) : Set Ω :=
  {ω | walk G k ω ≤ -(B * k)} ∪ {ω | B * k - 10 * Real.log k ≤ walk G k ω}

omit [IsProbabilityMeasure μ] in
lemma measurableSet_breakSet (h : IsGaussianWalk G v μ) (B : ℝ) (k : ℕ) :
    MeasurableSet (breakSet G B k) :=
  MeasurableSet.union (measurableSet_le (h.measurable_walk k) measurable_const)
    (measurableSet_le measurable_const (h.measurable_walk k))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Breaking nothing puts a path in the band.**  The upper cap needs the *lower* half of
`|h(j)| ≤ 10 log j`: `S_j < Bj - 10 log j ≤ Bj + h(j)`. -/
lemma mem_bandEvent_of_forall_notMem_breakSet {a B : ℝ} {hf g : ℕ → ℝ} {n : ℕ}
    (hhf : ∀ j, 1 ≤ j → j ≤ n → -(10 * Real.log j) ≤ hf j) (hg : ∀ j, g j ≤ -(B * j))
    {ω : Ω} (hω : ω ∈ upperEvent G a hf n)
    (hbreak : ∀ k, 1 ≤ k → k ≤ n → ω ∉ breakSet G B k) :
    ω ∈ bandEvent G a B hf g n := by
  intro j hj1 hjn
  have hb := hbreak j hj1 hjn
  rw [breakSet, Set.mem_union] at hb
  push Not at hb
  obtain ⟨hlow, hhigh⟩ := hb
  simp only [Set.mem_setOf_eq] at hlow hhigh
  refine ⟨le_trans (hg j) (by linarith), ?_⟩
  rw [show min a (B * (j : ℝ)) + hf j = min (a + hf j) (B * (j : ℝ) + hf j) from
    (min_add_add_right a (B * (j : ℝ)) (hf j)).symm]
  refine le_min (hω j hj1 hjn) ?_
  linarith [hhf j hj1 hjn]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Breaking one puts a path in `badSet`.**  Both halves of `RMF.breakSet` land in
`|Sₖ| ≥ Bk/2`; for the upper one that is `10 log k ≤ k ≤ Bk/2`, which is what `B ≥ 20` is for. -/
lemma inter_breakSet_subset_badSet {a B : ℝ} {hf : ℕ → ℝ} (hB : 20 ≤ B) {k n : ℕ}
    (hk : 1 ≤ k) :
    upperEvent G a hf n ∩ breakSet G B k
      ⊆ badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n := by
  rintro ω ⟨hup, hbr⟩
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (k : ℝ))
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hBk : (0 : ℝ) ≤ B * (k : ℝ) := mul_nonneg (by linarith) hk0
  have hgap : 20 * (k : ℝ) ≤ B * (k : ℝ) := mul_le_mul_of_nonneg_right hB hk0
  refine ⟨?_, fun j hkj hjn => hup j (by omega) hjn⟩
  change B * (k : ℝ) / 2 ≤ |walk G k ω|
  rcases hbr with hlow | hhigh
  · simp only [Set.mem_setOf_eq] at hlow
    have := neg_abs_le (walk G k ω)
    linarith
  · simp only [Set.mem_setOf_eq] at hhigh
    have := le_abs_self (walk G k ω)
    linarith

/-- **The slope of Probability Result 2's barriers**,
`max 20 ((4·result2StepConst v₋ v₊ / result1LowerConst v₋ v₊)^{1/7})`.  `20` makes
`10 log k ≤ Bk/2`, so that both families of bad paths sit inside `{|Sₖ| ≥ Bk/2}`; the second
term makes the accumulated bad mass at most half of Probability Result 1's lower bound.  Each bad
block has mass `≪ 1/(B⁷k²)`, so the condition is `4·stepConst ≤ αB⁷`
(`RMF.four_result2StepConst_le`), hence the seventh root. -/
noncomputable def result2Slope (vmin vmax : ℝ) : ℝ :=
  max 20 ((4 * result2StepConst vmin vmax / result1LowerConst vmin vmax) ^ ((1 : ℝ) / 7))

lemma le_result2Slope (vmin vmax : ℝ) : (20 : ℝ) ≤ result2Slope vmin vmax := le_max_left _ _

/-- **`x^{1/7}` raised to the seventh is `x`**, for `x ≥ 0`. -/
lemma rpow_one_seventh_pow_seven {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 7)) ^ (7 : ℕ) = x := by
  rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 7)) 7, ← Real.rpow_mul hx]
  norm_num

/-- The defining property: four times the one-step constant fits inside `α B⁷`.  This is the
*only* quantitative fact about `RMF.result2Slope` that Result 2 uses, besides `20 ≤ B`. -/
lemma four_result2StepConst_le {vmin vmax : ℝ} (hvmin : 0 < vmin) (hvmax : 0 < vmax) :
    4 * result2StepConst vmin vmax
      ≤ result1LowerConst vmin vmax * result2Slope vmin vmax ^ 7 := by
  have hα : (0 : ℝ) < result1LowerConst vmin vmax := result1LowerConst_pos hvmin hvmax
  have hS : (0 : ℝ) ≤ result2StepConst vmin vmax := result2StepConst_nonneg vmin vmax
  have hr0 : (0 : ℝ) ≤ 4 * result2StepConst vmin vmax / result1LowerConst vmin vmax := by
    positivity
  have hroot : (4 * result2StepConst vmin vmax / result1LowerConst vmin vmax) ^ ((1 : ℝ) / 7)
      ≤ result2Slope vmin vmax := le_max_right _ _
  have hpow : 4 * result2StepConst vmin vmax / result1LowerConst vmin vmax
      ≤ result2Slope vmin vmax ^ 7 := by
    rw [← rpow_one_seventh_pow_seven hr0]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hr0 _) hroot 7
  rw [div_le_iff₀ hα] at hpow
  linarith

/-- **Probability Result 2, lower bound** — Harper's Appendix A.2.  Let the walk's variances lie
in `[v₋, v₊]` and let it satisfy the lower half of Probability Result 1 from a level `R` with the
constant `result1LowerConst v₋ v₊` (`hR`; `RMF.result1Lower_iteratedLog` supplies it at
`R = result1Threshold v₋ v₊`).  For `a ≥ result2ThresholdOf R = max 1000 R`, `n ≥ 1`,
`4(log n)²⁰ ≤ n`, `4(log n)⁸ ≤ n v₋`, `|h(j)| ≤ 10 log j` and `g(j) ≤ -Bj` with
`B = RMF.result2Slope v₋ v₊`, the band event has probability at least
`(result1LowerConst v₋ v₊ / 2)·min{1, a/√n}`.

The slope is chosen by the summation: writing `E` for Result 1's event and
`Bₖ = {Sₖ ≤ -Bk} ∪ {Sₖ ≥ Bk - 10 log k}`, the band event contains `E \ ⋃ₖ Bₖ`, so
`P(band) ≥ P(E) - ∑_{k=1}^n P(E ∩ Bₖ)`.  Result 1's lower bound gives `P(E)`; each `P(E ∩ Bₖ)`
is `≪ 1/(B⁷k²)`, by splitting at time `k` (`RMF.IsGaussianWalk.measure_endpoint_inter_block`),
Result 1's upper bound on the suffix (`RMF.suffixSet_eq_shift`) and the tail integral
`RMF.lintegral_tail_one_add_abs_le`; `RMF.sum_inv_sq_Icc_le_two` sums it, and `B ≥ 20` puts both
families of bad paths inside `{|Sₖ| ≥ Bk/2}`. -/
theorem IsGaussianWalk.le_measure_bandEvent_of_result1Lower (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {R : ℝ}
    (hR : Result1LowerOn G μ vmin R (result1LowerConst vmin vmax)) :
      ∀ a : ℝ, result2ThresholdOf R ≤ a → ∀ n : ℕ, 1 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        ∀ hf g : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (∀ j, g j ≤ -(result2Slope vmin vmax * j)) →
            result1LowerConst vmin vmax / 2 * min 1 (a / √(n : ℝ))
              ≤ (μ (bandEvent G a (result2Slope vmin vmax) hf g n)).toReal := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hα0 : (0 : ℝ) < result1LowerConst vmin vmax := result1LowerConst_pos hvmin hvmax
  intro a ha n hn hbig hbig2 hf g hhf hg
  set B : ℝ := result2Slope vmin vmax with hBdef
  have hB : (20 : ℝ) ≤ B := le_result2Slope vmin vmax
  have hB0 : (0 : ℝ) < B := by linarith
  have ha1000 : (1000 : ℝ) ≤ a := le_trans (le_result2ThresholdOf R) ha
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hmin0 : (0 : ℝ) ≤ min 1 (a / √(n : ℝ)) :=
    le_min zero_le_one (by positivity)
  have hlog20 : (0 : ℝ) ≤ Real.log n ^ 20 := by positivity
  have hlog8 : (0 : ℝ) ≤ Real.log n ^ 8 := by positivity
  have hhfup : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ 10 * Real.log j :=
    fun j hj1 hjn => le_trans (le_abs_self _) (hhf j hj1 hjn)
  have hhflow : ∀ j, 1 ≤ j → j ≤ n → -(10 * Real.log j) ≤ hf j :=
    fun j hj1 hjn => by linarith [neg_abs_le (hf j), hhf j hj1 hjn]
  -- Probability Result 1, lower bound
  have hmain : result1LowerConst vmin vmax * min 1 (a / √(n : ℝ))
      ≤ (μ (upperEvent G a hf n)).toReal :=
    hR a (le_trans (le_result2ThresholdOf_right R) ha) n hn (by linarith) (by linarith) hf
      hhflow
  -- the union bound
  have hSm : MeasurableSet (⋃ k ∈ (Finset.Icc 1 n : Finset ℕ), breakSet G B k) :=
    Finset.measurableSet_biUnion _ fun k _ => measurableSet_breakSet h B k
  have hsplit : μ (upperEvent G a hf n)
      ≤ μ (bandEvent G a B hf g n)
        + ∑ k ∈ Finset.Icc 1 n, μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n) := by
    have hdiff : upperEvent G a hf n \ (⋃ k ∈ (Finset.Icc 1 n : Finset ℕ), breakSet G B k)
        ⊆ bandEvent G a B hf g n := by
      rintro ω ⟨hω, hout⟩
      refine mem_bandEvent_of_forall_notMem_breakSet hhflow hg hω fun k hk1 hkn hmem => hout ?_
      exact Set.mem_biUnion (Finset.mem_Icc.2 ⟨hk1, hkn⟩) hmem
    have hinter : upperEvent G a hf n ∩ (⋃ k ∈ (Finset.Icc 1 n : Finset ℕ), breakSet G B k)
        = ⋃ k ∈ (Finset.Icc 1 n : Finset ℕ), (upperEvent G a hf n ∩ breakSet G B k) := by
      rw [Set.inter_iUnion₂]
    calc μ (upperEvent G a hf n)
        = μ (upperEvent G a hf n ∩ (⋃ k ∈ (Finset.Icc 1 n : Finset ℕ), breakSet G B k))
            + μ (upperEvent G a hf n \ (⋃ k ∈ (Finset.Icc 1 n : Finset ℕ), breakSet G B k)) :=
          (measure_inter_add_sdiff _ hSm).symm
      _ ≤ (∑ k ∈ Finset.Icc 1 n, μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n))
            + μ (bandEvent G a B hf g n) := by
          refine add_le_add ?_ (measure_mono hdiff)
          rw [hinter]
          refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum fun k hk => ?_)
          exact measure_mono
            (inter_breakSet_subset_badSet hB (Finset.mem_Icc.1 hk).1)
      _ = _ := add_comm _ _
  -- in the reals
  have hreal : (μ (upperEvent G a hf n)).toReal
      ≤ (μ (bandEvent G a B hf g n)).toReal
        + ∑ k ∈ Finset.Icc 1 n,
            (μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)).toReal := by
    have hsne : (∑ k ∈ Finset.Icc 1 n,
        μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun k _ => measure_ne_top _ _
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hsne⟩) hsplit
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hsne,
      ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)] at hmono
  -- the accumulated bad mass
  have hbad : ∑ k ∈ Finset.Icc 1 n,
        (μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)).toReal
      ≤ 2 * (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7) := by
    have hterm : ∀ k ∈ Finset.Icc 1 n,
        (μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)).toReal
          ≤ (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7)
              * ((1 : ℝ) / (k : ℝ) ^ 2) := by
      intro k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have := h.measure_badSet_le_uniform ⟨hvmin, hlo, hhi⟩ ha1000 hB hk1 hkn hbig hbig2 hhfup
      calc (μ (badSet G (fun j => a + hf j) (B * (k : ℝ) / 2) k n)).toReal
          ≤ result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / (B ^ 7 * (k : ℝ) ^ 2) := this
        _ = (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7)
              * ((1 : ℝ) / (k : ℝ) ^ 2) := by
            field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hfac : (0 : ℝ) ≤ result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7 :=
      div_nonneg (mul_nonneg (result2StepConst_nonneg vmin vmax) hmin0) (by positivity)
    calc (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7)
          * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2
        ≤ (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7) * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le_two n) hfac
      _ = _ := by ring
  -- and the choice of `B` makes it at most half the main term
  have hhalf : 2 * (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7)
      ≤ result1LowerConst vmin vmax / 2 * min 1 (a / √(n : ℝ)) := by
    have hkey : 4 * result2StepConst vmin vmax ≤ result1LowerConst vmin vmax * B ^ 7 :=
      four_result2StepConst_le hvmin hvmax
    have hB7 : (0 : ℝ) < B ^ 7 := by positivity
    rw [show 2 * (result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7)
        = 2 * result2StepConst vmin vmax * min 1 (a / √(n : ℝ)) / B ^ 7 from by ring,
      div_le_iff₀ hB7]
    linarith [mul_le_mul_of_nonneg_right hkey hmin0]
  linarith

end RMF
