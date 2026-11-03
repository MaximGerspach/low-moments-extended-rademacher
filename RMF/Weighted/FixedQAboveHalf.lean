/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Hypercontractivity
import RMF.Analysis.Minkowski
import RMF.Weighted.FixedQTerms
import RMF.NumberTheory.LogPrimeSum
import RMF.NumberTheory.MertensProduct

/-!
# The weighted Rademacher sum at fixed `q > ½`: the order of magnitude

For fixed `q > ½`, `E|S(x)|^{2q} ≍ (log x)^{q(2q-1)}`, `S(x) = ∑_{n≤x} f(n)/√n`
(`RMF.exists_integral_rpow_weightedRademacherSum_asymp_largeQ`).

`S(x)` is a Rademacher chaos: the coefficient of `∏_{p ∈ A} X_p` is `n_A^{-1/2}` when
`n_A = ∏_{p ∈ A} p ≤ x` and `0` otherwise (`RMF.weightedRademacherSum_eq_chaosSum`).
Bonami–Beckner (`RMF.chaosNormSq_rpow_le_integral`, `RMF.integral_rpow_le_chaosNormSq`)
therefore compares `E|S(x)|^{2q}` with `(∑_{n ≤ x} μ²(n) (2q-1)^{ω(n)}/n)^q`, from below for
`q ≤ 1` and from above for `q ≥ 1`, and that sum is `≍ (log x)^{2q-1}` by Rankin's trick with
`y = x^{1/U}` and Mertens.  This gives the lower bound for `½ < q ≤ 1` and the upper bound for
`q ≥ 1`; the upper bound for `½ < q < 1` is
`RMF.exists_integral_rpow_norm_weightedRademacherSum_le`.

**The upper bound is uniform in `q`**: `RMF.exists_chaosNormSq_cutCoeff_le` is uniform in the
chaos exponent, so `RMF.exists_integral_rpow_weightedRademacherSum_le_uniform_of_one_le` holds
with one constant for all `q ≥ 1`, with the factor `exp(C·q(2q-1))`; for `½ < q ≤ 1` the uniform
form is `RMF.exists_integral_rpow_norm_weightedRademacherSum_le_uniform_min`.

For `q > 1` the lower bound restricts to the `y`-smooth part `A` (a contraction in `L^{2q}`),
written as the Euler product `F_y(½)` minus the smooth tail `T` beyond `x`:
`E|F_y(½)|^{2q} ≫ (log y)^{q(2q-1)}`, hypercontractivity bounds `E|T|^{2q} ≤ N_{2q-1}(T)^q`, Rankin
makes `N_{2q-1}(T)` a small fraction of `(log y)^{2q-1}`, and Minkowski leaves
`E|A|^{2q} ≫ (log y)^{q(2q-1)}`.

Only the weighted sum `S(x)` is treated here, and the lower bounds' constants depend on `q`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The weighted sum as a Rademacher chaos -/

/-- The primes up to `y`, as a finite set of `Nat.Primes`: the index set of the chaos. -/
def primesUpTo (y : ℕ) : Finset Nat.Primes := (Nat.primesBelow (y + 1)).subtype Nat.Prime

lemma mem_primesUpTo {y : ℕ} {p : Nat.Primes} : p ∈ primesUpTo y ↔ (p : ℕ) ≤ y := by
  have h : p ∈ primesUpTo y ↔ (p : ℕ) ∈ Nat.primesBelow (y + 1) := Finset.mem_subtype
  rw [h, Nat.mem_primesBelow]
  exact ⟨fun h => Nat.lt_succ_iff.1 h.1, fun h => ⟨Nat.lt_succ_iff.2 h, p.2⟩⟩

lemma primesUpTo_mono {y z : ℕ} (h : y ≤ z) : primesUpTo y ⊆ primesUpTo z :=
  fun _ hp => mem_primesUpTo.2 (le_trans (mem_primesUpTo.1 hp) h)

lemma prod_primesUpTo {M : Type*} [CommMonoid M] (y : ℕ) (g : ℕ → M) :
    ∏ p ∈ primesUpTo y, g p = ∏ p ∈ Nat.primesBelow (y + 1), g p :=
  Finset.prod_subtype_of_mem g fun _ hp => Nat.prime_of_mem_primesBelow hp

/-- `n ↦ n^{-1/2}`, in the form the weighted sum is written in. -/
noncomputable def sqrtInv (n : ℕ) : ℂ := ((Real.sqrt n : ℝ) : ℂ)⁻¹

lemma sqrtInv_mul (m n : ℕ) : sqrtInv (m * n) = sqrtInv m * sqrtInv n := by
  simp only [sqrtInv, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul,
    mul_inv]

lemma sqrtInv_prod {ι : Type*} (A : Finset ι) (g : ι → ℕ) :
    sqrtInv (∏ i ∈ A, g i) = ∏ i ∈ A, sqrtInv (g i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [sqrtInv]
  | insert a A ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, sqrtInv_mul, ih]

lemma sq_norm_sqrtInv (n : ℕ) : ‖sqrtInv n‖ ^ 2 = ((n : ℝ))⁻¹ := by
  rw [sqrtInv, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

lemma natCast_cpow_neg_half (n : ℕ) : (n : ℂ) ^ (-(1 / 2 : ℂ)) = sqrtInv n := by
  rw [sqrtInv, ← Complex.ofReal_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _),
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  norm_num

/-- A product of distinct primes is squarefree. -/
lemma squarefree_prod_primes (A : Finset Nat.Primes) : Squarefree (∏ p ∈ A, (p : ℕ)) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p _ q _ hpq => ?_)
    fun p _ => p.2.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)

lemma primeFactors_prod_primes (A : Finset Nat.Primes) :
    (∏ p ∈ A, (p : ℕ)).primeFactors = A.map (Function.Embedding.subtype Nat.Prime) := by
  have h := Nat.primeFactors_prod (s := A.map (Function.Embedding.subtype Nat.Prime))
    fun p hp => by
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 hp
      exact q.2
  rwa [Finset.prod_map] at h

lemma subtype_map_primes (A : Finset Nat.Primes) :
    (A.map (Function.Embedding.subtype Nat.Prime)).subtype Nat.Prime = A := by
  ext p
  rw [Finset.mem_subtype, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqp⟩
    rwa [← Subtype.ext hqp]
  · exact fun hp => ⟨p, hp, rfl⟩

lemma prod_primeFactors_subtype {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors.subtype Nat.Prime, (p : ℕ) = n :=
  (Finset.prod_subtype_of_mem (fun p : ℕ => p) fun _ hp => Nat.prime_of_mem_primeFactors hp).trans
    (Nat.prod_primeFactors_of_squarefree hn)

/-- The coefficient of `∏_{p ∈ A} X_p` in `S(x)`, `N = ⌊x⌋`: `n_A^{-1/2}` if `n_A ≤ N`. -/
noncomputable def cutCoeff (N : ℕ) (A : Finset Nat.Primes) : ℂ :=
  if ∏ p ∈ A, (p : ℕ) ≤ N then sqrtInv (∏ p ∈ A, (p : ℕ)) else 0

/-- The coefficient of `∏_{p ∈ A} X_p` in the Euler product at `½`: `n_A^{-1/2}`. -/
noncomputable def fullCoeff (A : Finset Nat.Primes) : ℂ := sqrtInv (∏ p ∈ A, (p : ℕ))

/-- The coefficients beyond `N`, what the Euler product has and `S(x)` has not. -/
noncomputable def tailCoeff (N : ℕ) (A : Finset Nat.Primes) : ℂ :=
  if ∏ p ∈ A, (p : ℕ) ≤ N then 0 else sqrtInv (∏ p ∈ A, (p : ℕ))

lemma cutCoeff_eq_sub (N : ℕ) (A : Finset Nat.Primes) :
    cutCoeff N A = fullCoeff A - tailCoeff N A := by
  unfold cutCoeff fullCoeff tailCoeff
  split_ifs <;> ring

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **The weighted sum is a Rademacher chaos** over the primes up to `N = ⌊x⌋`: the squarefree
`n ≤ N` are the products `n_A` of the sets `A` of primes with `n_A ≤ N`. -/
theorem weightedRademacherSum_eq_chaosSum (X : ℕ → Ω → ℂ) (x : ℝ) (ω : Ω) :
    weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      = chaosSum (fun p : Nat.Primes => X p) (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) ω := by
  classical
  set N := ⌊x⌋₊
  -- only squarefree `n` contribute
  have h1 : weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      = ∑ n ∈ Finset.Icc 1 N with Squarefree n, sqrtInv n * ∏ p ∈ n.primeFactors, X p ω := by
    rw [weightedRademacherSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rw [squarefreeExtension_apply_of_squarefree _ hn, sqrtInv, div_eq_inv_mul]
    · rw [squarefreeExtension_apply_of_not_squarefree _ hn, zero_div]
  -- and only the sets `A` with `n_A ≤ N`
  have h2 : chaosSum (fun p : Nat.Primes => X p) (primesUpTo N) (cutCoeff N) ω
      = ∑ A ∈ (primesUpTo N).powerset.filter (fun A : Finset Nat.Primes => ∏ p ∈ A, (p : ℕ) ≤ N),
          sqrtInv (∏ p ∈ A, (p : ℕ)) * ∏ p ∈ A, X p ω := by
    rw [chaosSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    unfold cutCoeff
    split_ifs <;> simp
  rw [h1, h2]
  symm
  refine Finset.sum_nbij' (fun A => ∏ p ∈ A, (p : ℕ))
    (fun n => (n.primeFactors.subtype Nat.Prime : Finset Nat.Primes))
    (fun A hA => ?_) (fun n hn => ?_) (fun A _ => ?_) (fun n hn => ?_) (fun A _ => ?_)
  · obtain ⟨-, hAN⟩ := Finset.mem_filter.1 hA
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2
      ⟨Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p _ => p.2.ne_zero), hAN⟩,
      squarefree_prod_primes A⟩
  · obtain ⟨hnI, hsq⟩ := Finset.mem_filter.1 hn
    have hnN := (Finset.mem_Icc.1 hnI).2
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun p hp => ?_, ?_⟩
    · have hp' : (p : ℕ) ∈ n.primeFactors := Finset.mem_subtype.1 hp
      exact mem_primesUpTo.2 (le_trans (Nat.le_of_mem_primeFactors hp') hnN)
    · exact (prod_primeFactors_subtype hsq).trans_le hnN
  · rw [primeFactors_prod_primes, subtype_map_primes]
  · exact prod_primeFactors_subtype (Finset.mem_filter.1 hn).2
  · rw [primeFactors_prod_primes, Finset.prod_map]
    rfl

omit [MeasurableSpace Ω] in
/-- **The Euler product at `½` is the full chaos** over the primes up to `y`. -/
theorem randomEulerProduct_half_eq_chaosSum (X : ℕ → Ω → ℂ) (y : ℕ) (ω : Ω) :
    randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (1 / 2) ω
      = chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) fullCoeff ω := by
  have hprod : ∏ p ∈ Nat.primesBelow (y + 1), (1 + X p ω * (p : ℂ) ^ (-(1 / 2 : ℂ)))
      = ∏ p ∈ primesUpTo y, (1 + X p ω * ((p : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))) :=
    (prod_primesUpTo y fun p => 1 + X p ω * (p : ℂ) ^ (-(1 / 2 : ℂ))).symm
  rw [randomEulerProduct, eulerProduct_squarefreeExtension, hprod, Finset.prod_one_add, chaosSum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [fullCoeff, sqrtInv_prod, Finset.prod_mul_distrib, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun p _ => natCast_cpow_neg_half p

/-! ### The coefficient norms -/

lemma sq_norm_fullCoeff (A : Finset Nat.Primes) :
    ‖fullCoeff A‖ ^ 2 = ∏ p ∈ A, (((p : ℕ) : ℝ))⁻¹ := by
  rw [fullCoeff, sq_norm_sqrtInv, Nat.cast_prod, Finset.prod_inv_distrib]

/-- The weighted norm of the Euler product's coefficients is an Euler product. -/
lemma chaosNormSq_fullCoeff (S : Finset Nat.Primes) (t : ℝ) :
    chaosNormSq S fullCoeff t = ∏ p ∈ S, (1 + t * (((p : ℕ) : ℝ))⁻¹) := by
  rw [chaosNormSq, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [sq_norm_fullCoeff, ← Finset.prod_const, ← Finset.prod_mul_distrib]

lemma chaosNormSq_cut_add_tail (N : ℕ) (S : Finset Nat.Primes) (t : ℝ) :
    chaosNormSq S (cutCoeff N) t + chaosNormSq S (tailCoeff N) t = chaosNormSq S fullCoeff t := by
  rw [chaosNormSq, chaosNormSq, chaosNormSq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  unfold cutCoeff tailCoeff fullCoeff
  split_ifs <;> simp

lemma chaosNormSq_mono {ι : Type*} {S T : Finset ι} (hST : S ⊆ T) (c : Finset ι → ℂ) {t : ℝ}
    (ht : 0 ≤ t) : chaosNormSq S c t ≤ chaosNormSq T c t :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.powerset_mono.2 hST) fun _ _ _ =>
    mul_nonneg (pow_nonneg ht _) (sq_nonneg _)

/-- `1/n ≤ x^{-δ} n^{δ-1}` for `n ≥ x`: Rankin's trick for one term. -/
lemma inv_le_rpow_neg_mul_rpow {x n δ : ℝ} (hx : 0 < x) (hxn : x ≤ n) (hδ : 0 ≤ δ) :
    n⁻¹ ≤ x ^ (-δ) * n ^ (δ - 1) := by
  have hn : 0 < n := lt_of_lt_of_le hx hxn
  rw [Real.rpow_sub_one hn.ne', Real.rpow_neg hx.le]
  have h1 : 1 ≤ (x ^ δ)⁻¹ * n ^ δ := by
    rw [← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hx δ), one_mul]
    exact Real.rpow_le_rpow hx.le hxn hδ
  calc n⁻¹ = 1 * n⁻¹ := (one_mul _).symm
    _ ≤ ((x ^ δ)⁻¹ * n ^ δ) * n⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)
    _ = (x ^ δ)⁻¹ * (n ^ δ / n) := by ring

/-- **Rankin's bound on the tail coefficients.** -/
lemma chaosNormSq_tailCoeff_le (S : Finset Nat.Primes) {x δ t : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ)
    (ht : 0 ≤ t) :
    chaosNormSq S (tailCoeff ⌊x⌋₊) t
      ≤ x ^ (-δ) * ∏ p ∈ S, (1 + t * (((p : ℕ) : ℝ)) ^ (δ - 1)) := by
  rw [chaosNormSq, Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_le_sum fun A _ => ?_
  have hprod : ∏ p ∈ A, (t * (((p : ℕ) : ℝ)) ^ (δ - 1))
      = t ^ A.card * (((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ)) ^ (δ - 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.cast_prod,
      Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg _)]
  rw [hprod]
  unfold tailCoeff
  split_ifs with h
  · rw [norm_zero, sq, mul_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg hx.le _)
      (mul_nonneg (pow_nonneg ht _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rw [sq_norm_sqrtInv]
    have hxn : x ≤ ((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ) := by
      have h' : ⌊x⌋₊ + 1 ≤ ∏ p ∈ A, (p : ℕ) := by omega
      have h'' : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ ((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ) := by exact_mod_cast h'
      exact le_trans (Nat.lt_floor_add_one x).le h''
    calc t ^ A.card * (((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ))⁻¹
        ≤ t ^ A.card * (x ^ (-δ) * (((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ)) ^ (δ - 1)) :=
          mul_le_mul_of_nonneg_left (inv_le_rpow_neg_mul_rpow hx hxn hδ) (pow_nonneg ht _)
      _ = x ^ (-δ) * (t ^ A.card * (((∏ p ∈ A, (p : ℕ) : ℕ) : ℝ)) ^ (δ - 1)) := by ring

/-! ### Products over the primes -/

/-- `e^u ≤ 1 + (e - 1) u` on `[0, 1]`: the exponential lies below its chord. -/
lemma exp_le_one_add_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.exp u ≤ 1 + (Real.exp 1 - 1) * u := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (by linarith : (0 : ℝ) ≤ 1 - u) h0
    (by ring : (1 - u) + u = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at h
  linarith

/-- The constant of the Rankin product, `(e - 1)(1 + (log 4 + 4)/log 2)`. -/
noncomputable def rankinConst : ℝ := (Real.exp 1 - 1) * (1 + (Real.log 4 + 4) / Real.log 2)

lemma one_le_exp_one_sub_one : 1 ≤ Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

lemma rankinConst_nonneg : 0 ≤ rankinConst := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold rankinConst
  have := one_le_exp_one_sub_one
  positivity

/-- **The Rankin product costs only a constant factor.**  For `δ log y ≤ 1`,
`∏_{p ≤ y} (1 + t p^{δ-1}) ≤ e^{t K} ∏_{p ≤ y} (1 + t/p)`: on `p ≤ y`,
`p^δ - 1 ≤ (e - 1) δ log p`, and Mertens' first theorem sums `δ log p / p` to
`δ log y + O(δ) = O(1)`. -/
theorem prod_one_add_mul_rpow_le_exp_mul_prod {y : ℕ} (hy : 2 ≤ y) {t δ : ℝ} (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) (hδy : δ * Real.log y ≤ 1) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ (δ - 1))
      ≤ Real.exp (t * rankinConst) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  have he := one_le_exp_one_sub_one
  -- one prime: `1 + t p^{δ-1} ≤ (1 + t/p) exp(t (e - 1) δ log p / p)`
  have hper : ∀ p ∈ Nat.primesBelow (y + 1),
      1 + t * (p : ℝ) ^ (δ - 1)
        ≤ (1 + t * (p : ℝ)⁻¹) * Real.exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p)) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hpy : (p : ℝ) ≤ y := by
      exact_mod_cast Nat.lt_succ_iff.1 (Nat.mem_primesBelow.1 hp).1
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hu1 : δ * Real.log p ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpy) hδ) hδy
    have hpδ : (p : ℝ) ^ δ ≤ 1 + (Real.exp 1 - 1) * (δ * Real.log p) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log p)]
      exact exp_le_one_add_mul (mul_nonneg hδ hlogp) hu1
    have hsplit : t * (p : ℝ) ^ (δ - 1)
        ≤ t * (p : ℝ)⁻¹ + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) := by
      rw [Real.rpow_sub_one hp0.ne']
      calc t * ((p : ℝ) ^ δ / p)
          ≤ t * ((1 + (Real.exp 1 - 1) * (δ * Real.log p)) / p) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpδ hp0.le) ht
        _ = t * (p : ℝ)⁻¹ + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) := by ring
    have hv : 0 ≤ t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) :=
      mul_nonneg (mul_nonneg ht (mul_nonneg (by linarith) hδ)) (div_nonneg hlogp hp0.le)
    have ha : 0 ≤ t * (p : ℝ)⁻¹ := mul_nonneg ht (inv_nonneg.2 hp0.le)
    have hexp := Real.add_one_le_exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p))
    calc 1 + t * (p : ℝ) ^ (δ - 1)
        ≤ 1 + t * (p : ℝ)⁻¹ + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) := by linarith
      _ ≤ (1 + t * (p : ℝ)⁻¹) * (1 + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p)) := by
          nlinarith [mul_nonneg ha hv]
      _ ≤ (1 + t * (p : ℝ)⁻¹) * Real.exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  -- Mertens' first theorem
  have hsum : ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p ≤ Real.log y + Real.log 4 + 4 := by
    have h := sum_log_div_prime_le (x := (y : ℝ)) (by exact_mod_cast (by omega : 1 ≤ y))
    rwa [Nat.floor_natCast, ← primesBelow_succ_eq_filter_Ioc] at h
  have hδ2 : δ ≤ 1 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    nlinarith [mul_le_mul_of_nonneg_left hlogy hδ]
  have hkey : (Real.exp 1 - 1) * δ * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
      ≤ rankinConst := by
    have h1 : δ * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
        ≤ 1 + (Real.log 4 + 4) / Real.log 2 := by
      calc δ * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
          ≤ δ * (Real.log y + Real.log 4 + 4) := mul_le_mul_of_nonneg_left hsum hδ
        _ = δ * Real.log y + δ * (Real.log 4 + 4) := by ring
        _ ≤ 1 + 1 / Real.log 2 * (Real.log 4 + 4) :=
            add_le_add hδy (mul_le_mul_of_nonneg_right hδ2 (by linarith))
        _ = 1 + (Real.log 4 + 4) / Real.log 2 := by ring
    calc (Real.exp 1 - 1) * δ * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
        = (Real.exp 1 - 1) * (δ * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p) := by ring
      _ ≤ (Real.exp 1 - 1) * (1 + (Real.log 4 + 4) / Real.log 2) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = rankinConst := rfl
  have hP0 : 0 ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) :=
    Finset.prod_nonneg fun p _ => add_nonneg zero_le_one (mul_nonneg ht (inv_nonneg.2
      (Nat.cast_nonneg p)))
  calc ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ (δ - 1))
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), ((1 + t * (p : ℝ)⁻¹)
          * Real.exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p))) :=
        Finset.prod_le_prod (fun p _ => add_nonneg zero_le_one
          (mul_nonneg ht (Real.rpow_nonneg (Nat.cast_nonneg p) _))) hper
    _ = (∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹))
          * Real.exp (t * ((Real.exp 1 - 1) * δ * ∑ p ∈ Nat.primesBelow (y + 1),
              Real.log p / p)) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹)) * Real.exp (t * rankinConst) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hkey ht)) hP0
    _ = Real.exp (t * rankinConst) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) :=
        mul_comm _ _

/-- `e^{u - u²} ≤ 1 + u` for `u ≥ 0`. -/
lemma exp_sub_sq_le_one_add {u : ℝ} (hu : 0 ≤ u) : Real.exp (u - u ^ 2) ≤ 1 + u := by
  have hpos : 0 < 1 + u := by linarith
  have key : (1 + u)⁻¹ ≤ 1 - u + u ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [pow_nonneg hu 3]
  have hlog : u - u ^ 2 ≤ Real.log (1 + u) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    linarith
  calc Real.exp (u - u ^ 2) ≤ Real.exp (Real.log (1 + u)) := Real.exp_le_exp.2 hlog
    _ = 1 + u := Real.exp_log hpos

/-- **`∏_{p ≤ y} (1 + t/p) ≫ (log y)^t`**, by Mertens' second theorem: `log(1 + t/p)` is
`t/p` up to `t²/p²`, which sums to `O(t²)`. -/
theorem exists_le_prod_one_add :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → ∀ t : ℝ, 0 ≤ t →
      Real.exp (-(C * (t + t ^ 2))) * Real.log y ^ t
        ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
  obtain ⟨C₂, hC₂, hmert⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  obtain ⟨B, hB0, hB⟩ := exists_sum_primesBelow_inv_sq_le
  refine ⟨C₂ + B, by positivity, fun y hy t ht => ?_⟩
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hper : ∀ p ∈ Nat.primesBelow (y + 1),
      Real.exp (t * (p : ℝ)⁻¹ - t ^ 2 * (1 / (p : ℝ) ^ 2)) ≤ 1 + t * (p : ℝ)⁻¹ := by
    intro p _
    have h := exp_sub_sq_le_one_add (mul_nonneg ht (inv_nonneg.2 (Nat.cast_nonneg p)))
    have heq : t * (p : ℝ)⁻¹ - (t * (p : ℝ)⁻¹) ^ 2
        = t * (p : ℝ)⁻¹ - t ^ 2 * (1 / (p : ℝ) ^ 2) := by ring
    rwa [heq] at h
  have hprod : Real.exp (t * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹
        - t ^ 2 * ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2)
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) hper
  have hm := (abs_le.1 (hmert y hy)).1
  have h1 : t * (Real.log (Real.log y) - C₂) ≤ t * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left (by linarith) ht
  have h2 : t ^ 2 * ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2 ≤ t ^ 2 * B :=
    mul_le_mul_of_nonneg_left (hB (y + 1)) (sq_nonneg t)
  have h3 : 0 ≤ C₂ * t ^ 2 + B * t := add_nonneg (mul_nonneg hC₂.le (sq_nonneg t))
    (mul_nonneg hB0 ht)
  have hexp : -((C₂ + B) * (t + t ^ 2)) + Real.log (Real.log y) * t
      ≤ t * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹
        - t ^ 2 * ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2 := by
    linarith
  calc Real.exp (-((C₂ + B) * (t + t ^ 2))) * Real.log y ^ t
      = Real.exp (-((C₂ + B) * (t + t ^ 2)) + Real.log (Real.log y) * t) := by
        rw [Real.rpow_def_of_pos hlogy, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 hexp
    _ ≤ _ := hprod

/-- **The lower-bound twin of `RMF.exists_moment_half_le`**: for `q ≥ ½`,
`E|F_y(½)|^{2q} ≫ (log y)^{q(2q-1)}` for the Rademacher Euler product.  The same proof: the
moment factors over the primes (`RMF.integral_norm_randomEulerProduct_rpow_sqfree`), the local
factors multiply to `exp(q(2q-1) ∑_{p ≤ y} 1/p + O(1))`
(`RMF.exists_prime_sum_bound_rademacherLaw`), and Mertens; the one extra input is the positivity
of the local factors. -/
theorem exists_le_integral_rpow_randomEulerProduct_half {q : ℝ} (hq : 1 / 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ y : ℕ, 2 ≤ y →
        c * Real.log y ^ (q * (2 * q - 1))
          ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (1 / 2) ω‖ ^ (2 * q) ∂μ := by
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨C₁, hC₁, hps⟩ :=
    exists_prime_sum_bound_rademacherLaw hq0 (by norm_num : (1 : ℝ) / 3 < 1 / 2)
  obtain ⟨C₂, hC₂, hmert⟩ := exists_abs_sum_primesBelow_inv_sub_log_log_le
  have hk : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0 (by linarith)
  refine ⟨Real.exp (-(C₁ + q * (2 * q - 1) * C₂)), Real.exp_pos _, fun X μ hX y hy => ?_⟩
  rw [integral_norm_randomEulerProduct_rpow_sqfree hX (y + 1) (1 / 2 : ℂ)
    (by linarith : (0 : ℝ) ≤ 2 * q)]
  -- the local factors are positive, from their value at `z = 1`
  have hP : 0 < ∏ p ∈ Nat.primesBelow (y + 1),
      ∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw := by
    refine Finset.prod_pos fun p _ => ?_
    rw [integral_rademacherLaw_eq, smul_eq_mul, one_mul, natCast_cpow_neg_half]
    have hne : (1 : ℂ) + sqrtInv p ≠ 0 := by
      have h : (1 : ℂ) + sqrtInv p = ((1 + (Real.sqrt p)⁻¹ : ℝ) : ℂ) := by
        rw [sqrtInv]
        push_cast
        ring
      rw [h, Complex.ofReal_ne_zero]
      positivity
    have h1 : 0 < ‖(1 : ℂ) + sqrtInv p‖ ^ (2 * q) := Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _
    have h2 : 0 ≤ ‖1 + -1 * sqrtInv p‖ ^ (2 * q) := Real.rpow_nonneg (norm_nonneg _) _
    exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg h1 h2)
  have hbound := hps q ⟨by linarith, le_rfl⟩ (1 / 2 : ℂ) (by norm_num) (y + 1)
  have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have him : ((1 / 2 : ℂ)).im = 0 := by norm_num
  have hS : (∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ) ^ (-2 * ((1 / 2 : ℂ)).re)
        * (q ^ 2 + q * (q - 1) * Real.cos (2 * (((1 / 2 : ℂ)).im * Real.log p)))))
      = q * (2 * q - 1) * ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hre, him]
    norm_num [Real.rpow_neg_one]
    ring
  rw [hS] at hbound
  have hm := (abs_le.1 (hmert y hy)).1
  have hb := (abs_le.1 hbound).1
  have hmul : q * (2 * q - 1) * (Real.log (Real.log y) - C₂)
      ≤ q * (2 * q - 1) * ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_left (by linarith) hk
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  calc Real.exp (-(C₁ + q * (2 * q - 1) * C₂)) * Real.log y ^ (q * (2 * q - 1))
      = Real.exp (-(C₁ + q * (2 * q - 1) * C₂) + Real.log (Real.log y) * (q * (2 * q - 1))) := by
        rw [Real.rpow_def_of_pos hlogy, ← Real.exp_add]
    _ ≤ Real.exp (Real.log (∏ p ∈ Nat.primesBelow (y + 1),
          ∫ z, ‖1 + z * (p : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ (2 * q) ∂rademacherLaw)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = _ := Real.exp_log hP

/-! ### Rankin with `y = x^{1/U}` -/

lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- **The choice `y = ⌊x^{1/U}⌋`**: for `x ≥ e^{2U}` it has `2 ≤ y ≤ ⌊x⌋` and
`U log y ≤ log x ≤ 2U log y`. -/
lemma exists_nat_log_between {U x : ℝ} (hU : 1 ≤ U) (hx : Real.exp (2 * U) ≤ x) :
    ∃ y : ℕ, 2 ≤ y ∧ y ≤ ⌊x⌋₊ ∧ U * Real.log y ≤ Real.log x
      ∧ Real.log x ≤ 2 * U * Real.log y := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hU0 : 0 < U := by linarith
  have hlogx : 2 * U ≤ Real.log x := by
    rw [← Real.log_exp (2 * U)]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hY2 : (2 : ℝ) ≤ Real.exp (Real.log x / U) := by
    have h1 : (2 : ℝ) ≤ Real.log x / U := by rw [le_div_iff₀ hU0]; linarith
    have h2 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    have h3 : Real.exp 2 ≤ Real.exp (Real.log x / U) := Real.exp_le_exp.2 h1
    linarith
  have hYx : Real.exp (Real.log x / U) ≤ x := by
    calc Real.exp (Real.log x / U) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.2 (div_le_self (by linarith) hU)
      _ = x := Real.exp_log hx0
  refine ⟨⌊Real.exp (Real.log x / U)⌋₊, Nat.le_floor (by exact_mod_cast hY2),
    Nat.floor_le_floor hYx, ?_, ?_⟩
  · have hy0 : (0 : ℝ) < ⌊Real.exp (Real.log x / U)⌋₊ := by
      exact_mod_cast Nat.floor_pos.2 (by linarith)
    have h := Real.log_le_log hy0 (Nat.floor_le (Real.exp_pos _).le)
    rw [Real.log_exp, le_div_iff₀ hU0] at h
    linarith
  · have hfl : Real.exp (Real.log x / U) / 2 ≤ ⌊Real.exp (Real.log x / U)⌋₊ := by
      have := Nat.sub_one_lt_floor (Real.exp (Real.log x / U))
      linarith
    have hlog := Real.log_le_log (by positivity) hfl
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hlog
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * U)
    have h3 : 2 * U * (Real.log x / U - Real.log 2) = 2 * Real.log x - 2 * U * Real.log 2 := by
      rw [mul_sub, mul_assoc, mul_div_cancel₀ _ hU0.ne']
    have h4 : 2 * U * Real.log 2 ≤ 2 * U * 1 :=
      mul_le_mul_of_nonneg_left hlog2.le (by linarith)
    rw [h3] at h2
    linarith

/-- **The smooth tail is a small fraction of the Euler product's norm**: with `y ≥ 2` and
`U log y ≤ log x`, `N_t(tail) ≤ e^{-U} e^{tK} ∏_{p ≤ y} (1 + t/p)`. -/
lemma chaosNormSq_tailCoeff_le_exp {x U t : ℝ} {y : ℕ} (hy : 2 ≤ y) (hx : 0 < x) (ht : 0 ≤ t)
    (hU : U * Real.log y ≤ Real.log x) :
    chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) t
      ≤ Real.exp (-U) * Real.exp (t * rankinConst)
        * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hδ0 : 0 ≤ (Real.log y)⁻¹ := inv_nonneg.2 hlogy.le
  have hδy : (Real.log y)⁻¹ * Real.log y ≤ 1 := by rw [inv_mul_cancel₀ hlogy.ne']
  have hrank := chaosNormSq_tailCoeff_le (primesUpTo y) hx hδ0 ht
  have hconv : ∏ p ∈ primesUpTo y, (1 + t * (((p : ℕ) : ℝ)) ^ ((Real.log y)⁻¹ - 1))
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ ((Real.log y)⁻¹ - 1)) :=
    prod_primesUpTo y fun p : ℕ => 1 + t * (p : ℝ) ^ ((Real.log y)⁻¹ - 1)
  rw [hconv] at hrank
  have hprod := prod_one_add_mul_rpow_le_exp_mul_prod hy ht hδ0 hδy
  have hxδ : x ^ (-(Real.log y)⁻¹) ≤ Real.exp (-U) := by
    rw [Real.rpow_def_of_pos hx]
    refine Real.exp_le_exp.2 ?_
    have h : U ≤ Real.log x * (Real.log y)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hlogy]
      exact hU
    linarith
  calc chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) t
      ≤ x ^ (-(Real.log y)⁻¹)
          * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ ((Real.log y)⁻¹ - 1)) := hrank
    _ ≤ Real.exp (-U) * (Real.exp (t * rankinConst)
          * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹)) :=
        mul_le_mul hxδ hprod (Finset.prod_nonneg fun p _ => add_nonneg zero_le_one
          (mul_nonneg ht (Real.rpow_nonneg (Nat.cast_nonneg p) _))) (Real.exp_pos _).le
    _ = Real.exp (-U) * Real.exp (t * rankinConst)
          * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by ring

/-- **The smooth tail is as small a fraction of `(log y)^t` as we like**, for `U` large. -/
lemma exists_chaosNormSq_tailCoeff_le_small {t η : ℝ} (ht : 0 ≤ t) (hη : 0 < η) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ (x : ℝ) (y : ℕ), 2 ≤ y → 0 < x → U * Real.log y ≤ Real.log x →
      chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) t ≤ η * Real.log y ^ t := by
  obtain ⟨C, hC, hprod⟩ := exists_prod_one_add_le_rpow_log
  refine ⟨max 1 (t * rankinConst + t * C - Real.log η), le_max_left _ _,
    fun x y hy hx hU => ?_⟩
  have h1 := chaosNormSq_tailCoeff_le_exp hy hx ht hU
  have h2 := hprod y hy t ht (fun p => t * (p : ℝ)⁻¹)
    (fun p _ => mul_nonneg ht (inv_nonneg.2 (Nat.cast_nonneg p))) fun p _ => le_rfl
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))
  set U := max 1 (t * rankinConst + t * C - Real.log η) with hU_def
  have hexp : Real.exp (-U) * Real.exp (t * rankinConst) * Real.exp (t * C) ≤ η := by
    rw [← Real.exp_add, ← Real.exp_add]
    calc Real.exp (-U + t * rankinConst + t * C) ≤ Real.exp (Real.log η) :=
          Real.exp_le_exp.2 (by linarith [le_max_right 1 (t * rankinConst + t * C - Real.log η)])
      _ = η := Real.exp_log hη
  calc chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) t
      ≤ Real.exp (-U) * Real.exp (t * rankinConst)
          * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := h1
    _ ≤ Real.exp (-U) * Real.exp (t * rankinConst) * (Real.exp (t * C) * Real.log y ^ t) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Real.exp (-U) * Real.exp (t * rankinConst) * Real.exp (t * C)) * Real.log y ^ t := by
        ring
    _ ≤ η * Real.log y ^ t := mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hlogy _)

/-- **`∑_{n ≤ x} μ²(n) t^{ω(n)}/n ≫ (log x)^t`**, in chaos form: restrict to `y = x^{1/U}`,
where the cut costs at most half of `∏_{p ≤ y}(1 + t/p)` once `e^{-U} e^{tK} ≤ ½`. -/
theorem exists_le_chaosNormSq_cutCoeff {t : ℝ} (ht : 0 ≤ t) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ x : ℝ, x₀ ≤ x →
      c * Real.log x ^ t ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) t := by
  obtain ⟨Cl, hCl, hlow⟩ := exists_le_prod_one_add
  have hK := rankinConst_nonneg
  have hU1 : 1 ≤ t * rankinConst + 1 := by have := mul_nonneg ht hK; linarith
  refine ⟨Real.exp (-(Cl * (t + t ^ 2))) / 2 * ((2 * (t * rankinConst + 1)) ^ t)⁻¹,
    Real.exp (2 * (t * rankinConst + 1)), by positivity, fun x hx => ?_⟩
  obtain ⟨y, hy2, hyN, hUy, hyU⟩ := exists_nat_log_between hU1 hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hy2' : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := by nlinarith
  have hsplit := chaosNormSq_cut_add_tail ⌊x⌋₊ (primesUpTo y) t
  have hfull : chaosNormSq (primesUpTo y) fullCoeff t
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
    rw [chaosNormSq_fullCoeff]
    exact prod_primesUpTo y fun p : ℕ => 1 + t * (p : ℝ)⁻¹
  have htail := chaosNormSq_tailCoeff_le_exp hy2 hx0 ht hUy
  have hlowy := hlow y hy2 t ht
  have hmono := chaosNormSq_mono (primesUpTo_mono hyN) (cutCoeff ⌊x⌋₊) ht
  have hhalf : Real.exp (-(t * rankinConst + 1)) * Real.exp (t * rankinConst) ≤ 1 / 2 := by
    rw [← Real.exp_add, show -(t * rankinConst + 1) + t * rankinConst = -1 by ring]
    exact exp_neg_one_le_half
  set P := ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) with hP_def
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun p _ => add_nonneg zero_le_one
    (mul_nonneg ht (inv_nonneg.2 (Nat.cast_nonneg p)))
  have hcut : P / 2 ≤ chaosNormSq (primesUpTo y) (cutCoeff ⌊x⌋₊) t := by
    have h1 := mul_le_mul_of_nonneg_right hhalf hP0
    linarith
  have hlogyx : Real.log x / (2 * (t * rankinConst + 1)) ≤ Real.log y := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hpow := Real.rpow_le_rpow (div_nonneg hlogx.le (by linarith)) hlogyx ht
  rw [Real.div_rpow hlogx.le (by linarith)] at hpow
  calc Real.exp (-(Cl * (t + t ^ 2))) / 2 * ((2 * (t * rankinConst + 1)) ^ t)⁻¹ * Real.log x ^ t
      = Real.exp (-(Cl * (t + t ^ 2))) / 2
          * (Real.log x ^ t / (2 * (t * rankinConst + 1)) ^ t) := by ring
    _ ≤ Real.exp (-(Cl * (t + t ^ 2))) / 2 * Real.log y ^ t :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ P / 2 := by linarith
    _ ≤ chaosNormSq (primesUpTo y) (cutCoeff ⌊x⌋₊) t := hcut
    _ ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) t := hmono

/-- **`∑_{n ≤ x} μ²(n) t^{ω(n)}/n ≪ (log x)^t`**, in chaos form: drop the cut. -/
theorem exists_chaosNormSq_cutCoeff_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ, 2 ≤ x →
      chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) t ≤ Real.exp (t * C) * Real.log x ^ t := by
  obtain ⟨C, hC, hprod⟩ := exists_prod_one_add_le_rpow_log
  refine ⟨C, hC, fun t ht x hx => ?_⟩
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN' : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hsplit := chaosNormSq_cut_add_tail ⌊x⌋₊ (primesUpTo ⌊x⌋₊) t
  have htail0 := chaosNormSq_nonneg (primesUpTo ⌊x⌋₊) (tailCoeff ⌊x⌋₊) ht
  have hfull : chaosNormSq (primesUpTo ⌊x⌋₊) fullCoeff t
      = ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + t * (p : ℝ)⁻¹) := by
    rw [chaosNormSq_fullCoeff]
    exact prod_primesUpTo _ fun p : ℕ => 1 + t * (p : ℝ)⁻¹
  have hP := hprod ⌊x⌋₊ hN t ht (fun p => t * (p : ℝ)⁻¹)
    (fun p _ => mul_nonneg ht (inv_nonneg.2 (Nat.cast_nonneg p))) fun p _ => le_rfl
  have hlogN : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hpow : Real.log ⌊x⌋₊ ^ t ≤ Real.log x ^ t :=
    Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlogN ht
  calc chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) t
      ≤ chaosNormSq (primesUpTo ⌊x⌋₊) fullCoeff t := by linarith
    _ = ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + t * (p : ℝ)⁻¹) := hfull
    _ ≤ Real.exp (t * C) * Real.log ⌊x⌋₊ ^ t := hP
    _ ≤ Real.exp (t * C) * Real.log x ^ t := mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

/-! ### The moments -/

lemma memLp_chaosSum {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ] {Y : ι → Ω → ℂ}
    (hm : ∀ i, Measurable (Y i)) (hlaw : ∀ i, HasLaw (Y i) rademacherLaw μ) (S : Finset ι)
    (c : Finset ι → ℂ) (r : ℝ) : MemLp (chaosSum Y S c) (ENNReal.ofReal r) μ :=
  memLp_ofReal_of_bound (measurable_chaosSum hm S c).aestronglyMeasurable
    ((ae_forall_norm_le_one_of_hasLaw hlaw S).mono fun _ hω => norm_chaosSum_le c hω)

/-- Minkowski for two functions. -/
lemma rpow_inv_integral_rpow_norm_add_le {E : Type*} [NormedAddCommGroup E] {μ : Measure Ω}
    {f g : Ω → E} {r : ℝ} (hr : 1 ≤ r) (hf : MemLp f (ENNReal.ofReal r) μ)
    (hg : MemLp g (ENNReal.ofReal r) μ) :
    (∫ ω, ‖f ω + g ω‖ ^ r ∂μ) ^ r⁻¹
      ≤ (∫ ω, ‖f ω‖ ^ r ∂μ) ^ r⁻¹ + (∫ ω, ‖g ω‖ ^ r ∂μ) ^ r⁻¹ := by
  have h := rpow_inv_integral_rpow_norm_sum_le (s := Finset.univ) (g := ![f, g]) hr
    fun i _ => by fin_cases i <;> simpa
  simpa [Fin.sum_univ_two] using h

omit [MeasurableSpace Ω] in
/-- **The Minkowski step.**  If `‖F‖ ≤ ‖A‖ + ‖T‖` in `L^r`, `E|F|^r ≥ M` and
`E|T|^r ≤ M/2^r`, then `E|A|^r ≥ M/2^r`. -/
lemma le_of_rpow_inv_le_add {IA IF IT M r : ℝ} (hr : 0 < r) (hIA : 0 ≤ IA) (hIT : 0 ≤ IT)
    (hM : 0 ≤ M) (hmink : IF ^ r⁻¹ ≤ IA ^ r⁻¹ + IT ^ r⁻¹) (hF : M ≤ IF) (hT : IT ≤ M / 2 ^ r) :
    M / 2 ^ r ≤ IA := by
  have h2r : (0 : ℝ) < 2 ^ r := Real.rpow_pos_of_pos two_pos r
  have hMr : (M / 2 ^ r) ^ r⁻¹ = M ^ r⁻¹ / 2 := by
    rw [Real.div_rpow hM h2r.le, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_inv_cancel₀ hr.ne', Real.rpow_one]
  have hF' : M ^ r⁻¹ ≤ IF ^ r⁻¹ := Real.rpow_le_rpow hM hF (inv_nonneg.2 hr.le)
  have hT' : IT ^ r⁻¹ ≤ M ^ r⁻¹ / 2 := by
    rw [← hMr]
    exact Real.rpow_le_rpow hIT hT (inv_nonneg.2 hr.le)
  have hA' : M ^ r⁻¹ / 2 ≤ IA ^ r⁻¹ := by linarith
  calc M / 2 ^ r = ((M / 2 ^ r) ^ r⁻¹) ^ r := by
        rw [← Real.rpow_mul (div_nonneg hM h2r.le), inv_mul_cancel₀ hr.ne', Real.rpow_one]
    _ = (M ^ r⁻¹ / 2) ^ r := by rw [hMr]
    _ ≤ (IA ^ r⁻¹) ^ r :=
        Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hM _) (by norm_num)) hA' hr.le
    _ = IA := by rw [← Real.rpow_mul hIA, inv_mul_cancel₀ hr.ne', Real.rpow_one]

omit [MeasurableSpace Ω] in
lemma rpow_tail_algebra {c₀ L q : ℝ} (hc₀ : 0 < c₀) (hL : 0 ≤ L) (hq : 0 < q) :
    (c₀ ^ q⁻¹ / 4 * L ^ (2 * q - 1)) ^ q = c₀ * L ^ (q * (2 * q - 1)) / 2 ^ (2 * q) := by
  have h4 : (4 : ℝ) ^ q = 2 ^ (2 * q) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
    norm_num
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hL _),
    Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hc₀.le,
    inv_mul_cancel₀ hq.ne', Real.rpow_one, ← Real.rpow_mul hL, h4, mul_comm (2 * q - 1) q]
  ring

/-- **The lower bound for `½ < q ≤ 1`**: Bonami–Beckner from below,
`E|S(x)|^{2q} ≥ (∑_{n ≤ x} μ²(n)(2q-1)^{ω(n)}/n)^q ≫ (log x)^{q(2q-1)}`. -/
theorem exists_le_integral_rpow_weightedRademacherSum_of_le_one {q : ℝ} (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        c * Real.log x ^ (q * (2 * q - 1))
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨c, x₀, hc, hlow⟩ := exists_le_chaosNormSq_cutCoeff (t := 2 * q - 1) (by linarith)
  refine ⟨c ^ q, max x₀ 2, Real.rpow_pos_of_pos hc q, fun X μ hX x hx => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith [le_max_right x₀ 2])
  have hhyp := chaosNormSq_rpow_le_integral (μ := μ) (Y := fun p : Nat.Primes => X p)
    (fun p => hX.measurable p p.2) hX.iIndep (fun p => hX.hasLaw p p.2)
    (p := 2 * q) (by linarith) (by linarith) (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊)
  simp_rw [weightedRademacherSum_eq_chaosSum]
  refine le_trans ?_ hhyp
  have hbase := hlow x (le_trans (le_max_left _ _) hx)
  calc c ^ q * Real.log x ^ (q * (2 * q - 1)) = (c * Real.log x ^ (2 * q - 1)) ^ q := by
        rw [Real.mul_rpow hc.le (Real.rpow_nonneg hlogx.le _), ← Real.rpow_mul hlogx.le,
          mul_comm (2 * q - 1) q]
    _ ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) (2 * q - 1) ^ q :=
        Real.rpow_le_rpow (mul_nonneg hc.le (Real.rpow_nonneg hlogx.le _)) hbase (by linarith)
    _ = chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) (2 * q - 1) ^ (2 * q / 2) := by
        rw [mul_div_cancel_left₀ q two_ne_zero]

/-- **The upper bound for `q ≥ 1`, uniformly in `q`.**  One `C`, independent of `x` and `q`:
`E|S(x)|^{2q} ≤ exp(C·q(2q-1))·(log x)^{q(2q-1)}` for all `q ≥ 1` and `x ≥ 2`.  The constant of
`RMF.exists_chaosNormSq_cutCoeff_le` is uniform in the chaos exponent, so `q` sits inside the
existential; `RMF.exists_integral_rpow_weightedRademacherSum_le_of_one_le` is its fixed-`q`
reading. -/
theorem exists_integral_rpow_weightedRademacherSum_le_uniform_of_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x q : ℝ, 2 ≤ x → 1 ≤ q →
        ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ
          ≤ Real.exp (C * (q * (2 * q - 1))) * Real.log x ^ (q * (2 * q - 1)) := by
  obtain ⟨C, hC, hupp⟩ := exists_chaosNormSq_cutCoeff_le
  refine ⟨C, hC, fun X μ hX x q hx hq => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have ht : (0 : ℝ) ≤ 2 * q - 1 := by linarith
  have hhyp := integral_rpow_le_chaosNormSq (μ := μ) (Y := fun p : Nat.Primes => X p)
    (fun p => hX.measurable p p.2) hX.iIndep (fun p => hX.hasLaw p p.2)
    (r := 2 * q) (by linarith) (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊)
  simp_rw [weightedRademacherSum_eq_chaosSum]
  refine le_trans hhyp ?_
  have hb := hupp (2 * q - 1) ht x hx
  have h0 := chaosNormSq_nonneg (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) ht
  calc chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) (2 * q - 1) ^ (2 * q / 2)
      = chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) (2 * q - 1) ^ q := by
        rw [mul_div_cancel_left₀ q two_ne_zero]
    _ ≤ (Real.exp ((2 * q - 1) * C) * Real.log x ^ (2 * q - 1)) ^ q :=
        Real.rpow_le_rpow h0 hb (by linarith)
    _ = Real.exp (C * (q * (2 * q - 1))) * Real.log x ^ (q * (2 * q - 1)) := by
        rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hlogx.le _),
          ← Real.rpow_mul hlogx.le, mul_comm (2 * q - 1) q, ← Real.exp_mul]
        congr 2
        ring

/-- **The upper bound for `q ≥ 1`**: Bonami–Beckner from above,
`E|S(x)|^{2q} ≤ (∑_{n ≤ x} μ²(n)(2q-1)^{ω(n)}/n)^q ≪ (log x)^{q(2q-1)}`.  The fixed-`q` reading
of `RMF.exists_integral_rpow_weightedRademacherSum_le_uniform_of_one_le`. -/
theorem exists_integral_rpow_weightedRademacherSum_le_of_one_le {q : ℝ} (hq : 1 ≤ q) :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ
          ≤ C * Real.log x ^ (q * (2 * q - 1)) := by
  obtain ⟨C, hC, h⟩ := exists_integral_rpow_weightedRademacherSum_le_uniform_of_one_le (Ω := Ω)
  exact ⟨Real.exp (C * (q * (2 * q - 1))), 2, Real.exp_pos _,
    fun X μ hX x hx => h X μ hX x q hx hq⟩

/-- **The lower bound for `q ≥ 1`.**  Bonami–Beckner only bounds from above here, so:
`E|S(x)|^{2q}` dominates the moment of its `y`-smooth part `A = F_y(½) - T`, `y = x^{1/U}`; the
Euler product has `E|F_y(½)|^{2q} ≫ (log y)^{q(2q-1)}`, the tail `T` beyond `x` has
`E|T|^{2q} ≤ N_{2q-1}(T)^q` with `N_{2q-1}(T)` a small fraction of `(log y)^{2q-1}`, and
Minkowski gives `E|A|^{2q} ≫ (log y)^{q(2q-1)} ≫ (log x)^{q(2q-1)}`. -/
theorem exists_le_integral_rpow_weightedRademacherSum_of_one_le {q : ℝ} (hq : 1 ≤ q) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        c * Real.log x ^ (q * (2 * q - 1))
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  have hq0 : 0 < q := by linarith
  have ht : (0 : ℝ) ≤ 2 * q - 1 := by linarith
  obtain ⟨c₀, hc₀, hE⟩ := exists_le_integral_rpow_randomEulerProduct_half (Ω := Ω)
    (by linarith : (1 : ℝ) / 2 ≤ q)
  obtain ⟨U, hU1, htail⟩ := exists_chaosNormSq_tailCoeff_le_small ht
    (by positivity : (0 : ℝ) < c₀ ^ q⁻¹ / 4)
  refine ⟨c₀ / 2 ^ (2 * q) * ((2 * U) ^ (q * (2 * q - 1)))⁻¹, Real.exp (2 * U), by positivity,
    fun X μ hX x hx => ?_⟩
  haveI := hX.isProbabilityMeasure
  obtain ⟨y, hy2, hyN, hUy, hyU⟩ := exists_nat_log_between hU1 hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hy2' : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := by nlinarith
  have hm : ∀ p : Nat.Primes, Measurable ((fun p : Nat.Primes => X p) p) :=
    fun p => hX.measurable p p.2
  have hlaw : ∀ p : Nat.Primes, HasLaw ((fun p : Nat.Primes => X p) p) rademacherLaw μ :=
    fun p => hX.hasLaw p p.2
  -- `E|S(x)|^{2q}` dominates the moment of the `y`-smooth part
  have hsub := integral_rpow_chaosSum_le_of_subset hm hX.iIndep hlaw (r := 2 * q) (by linarith)
    (primesUpTo_mono hyN) (cutCoeff ⌊x⌋₊)
  simp_rw [weightedRademacherSum_eq_chaosSum]
  refine le_trans ?_ hsub
  -- the Euler product
  have hF : c₀ * Real.log y ^ (q * (2 * q - 1))
      ≤ ∫ ω, ‖chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) fullCoeff ω‖ ^ (2 * q) ∂μ := by
    have h := hE X μ hX y hy2
    simp_rw [randomEulerProduct_half_eq_chaosSum] at h
    exact h
  -- the smooth tail beyond `x`
  have hT : ∫ ω, ‖chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) (tailCoeff ⌊x⌋₊) ω‖
        ^ (2 * q) ∂μ
      ≤ c₀ * Real.log y ^ (q * (2 * q - 1)) / 2 ^ (2 * q) := by
    have h1 := integral_rpow_le_chaosNormSq hm hX.iIndep hlaw (r := 2 * q) (by linarith)
      (primesUpTo y) (tailCoeff ⌊x⌋₊)
    have h2 := htail x y hy2 hx0 hUy
    have h0 := chaosNormSq_nonneg (primesUpTo y) (tailCoeff ⌊x⌋₊) ht
    calc _ ≤ chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) (2 * q - 1) ^ (2 * q / 2) := h1
      _ = chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) (2 * q - 1) ^ q := by
          rw [mul_div_cancel_left₀ q two_ne_zero]
      _ ≤ (c₀ ^ q⁻¹ / 4 * Real.log y ^ (2 * q - 1)) ^ q := Real.rpow_le_rpow h0 h2 hq0.le
      _ = c₀ * Real.log y ^ (q * (2 * q - 1)) / 2 ^ (2 * q) :=
          rpow_tail_algebra hc₀ hlogy.le hq0
  -- Minkowski: `F = A + T`
  have hmink : (∫ ω, ‖chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) fullCoeff ω‖
        ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ (∫ ω, ‖chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) (cutCoeff ⌊x⌋₊) ω‖
          ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
        + (∫ ω, ‖chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) (tailCoeff ⌊x⌋₊) ω‖
          ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ := by
    have hc : (fun A => fullCoeff A - tailCoeff ⌊x⌋₊ A) = cutCoeff ⌊x⌋₊ :=
      funext fun A => (cutCoeff_eq_sub _ A).symm
    have hsplit : ∀ ω, chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) fullCoeff ω
        = chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) (cutCoeff ⌊x⌋₊) ω
          + chaosSum (fun p : Nat.Primes => X p) (primesUpTo y) (tailCoeff ⌊x⌋₊) ω := by
      intro ω
      rw [← hc, chaosSum_sub]
      ring
    simp_rw [hsplit]
    exact rpow_inv_integral_rpow_norm_add_le (by linarith) (memLp_chaosSum hm hlaw _ _ _)
      (memLp_chaosSum hm hlaw _ _ _)
  have hA := le_of_rpow_inv_le_add (by linarith : (0 : ℝ) < 2 * q)
    (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (mul_nonneg hc₀.le (Real.rpow_nonneg hlogy.le _)) hmink hF hT
  refine le_trans ?_ hA
  -- `log y ≥ log x / (2U)`
  have hk : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0.le ht
  have hlogyx : Real.log x / (2 * U) ≤ Real.log y := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hpow := Real.rpow_le_rpow (div_nonneg hlogx.le (by linarith)) hlogyx hk
  rw [Real.div_rpow hlogx.le (by linarith)] at hpow
  calc c₀ / 2 ^ (2 * q) * ((2 * U) ^ (q * (2 * q - 1)))⁻¹ * Real.log x ^ (q * (2 * q - 1))
      = c₀ / 2 ^ (2 * q) * (Real.log x ^ (q * (2 * q - 1)) / (2 * U) ^ (q * (2 * q - 1))) := by
        ring
    _ ≤ c₀ / 2 ^ (2 * q) * Real.log y ^ (q * (2 * q - 1)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = c₀ * Real.log y ^ (q * (2 * q - 1)) / 2 ^ (2 * q) := by ring

/-- **The order of magnitude at fixed `q > ½`**: `E|S(x)|^{2q} ≍ (log x)^{q(2q-1)}`, where
`S(x) = ∑_{n ≤ x} f(n)/√n` for the Rademacher function `f`.  Upper bound:
`RMF.exists_integral_rpow_norm_weightedRademacherSum_le` for `q < 1`,
`RMF.exists_integral_rpow_weightedRademacherSum_le_of_one_le` for `q ≥ 1`.  Lower bound:
`RMF.exists_le_integral_rpow_weightedRademacherSum_of_le_one` for `q ≤ 1`,
`RMF.exists_le_integral_rpow_weightedRademacherSum_of_one_le` for `q ≥ 1`. -/
theorem exists_integral_rpow_weightedRademacherSum_asymp_largeQ {q : ℝ} (hq : 1 / 2 < q) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
        c * Real.log x ^ (q * (2 * q - 1))
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ
          ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
                ^ (2 * q) ∂μ
            ≤ C * Real.log x ^ (q * (2 * q - 1)) := by
  obtain ⟨c, x₁, hc, hlow⟩ : ∃ c x₁ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, x₁ ≤ x →
        c * Real.log x ^ (q * (2 * q - 1))
          ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
    rcases le_total q 1 with hq1 | hq1
    · exact exists_le_integral_rpow_weightedRademacherSum_of_le_one hq hq1
    · exact exists_le_integral_rpow_weightedRademacherSum_of_one_le hq1
  obtain ⟨C, x₂, hC, hupp⟩ : ∃ C x₂ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, x₂ ≤ x →
        ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ
          ≤ C * Real.log x ^ (q * (2 * q - 1)) := by
    rcases lt_or_ge q 1 with hq1 | hq1
    · obtain ⟨C, x₂, hC, h⟩ := exists_integral_rpow_norm_weightedRademacherSum_le hq hq1
      exact ⟨C, x₂, hC, fun X μ hX x hx => h Ω X μ hX x hx⟩
    · exact exists_integral_rpow_weightedRademacherSum_le_of_one_le hq1
  exact ⟨c, C, max x₁ x₂, hc, hC, fun X μ hX x hx =>
    ⟨hlow X μ hX x (le_trans (le_max_left _ _) hx), hupp X μ hX x (le_trans (le_max_right _ _) hx)⟩⟩

end RMF
