/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.HarperMoment
import RMF.Reduction.RademacherSteps

/-!
# The lower reduction for the Rademacher function

The upper reduction (`RMF.reduction_upper_rademacher`) is verbatim its Steinhaus mirror, because
every quantity it bounds is bounded *above*, and the Rademacher function is pointwise smaller than
the Steinhaus one.

**The lower reduction is where that stops being free.**  It bounds things from *below*, and there
the two models genuinely part company:

| quantity | Steinhaus | Rademacher |
|---|---|---|
| `E‖A_y(s)‖²` | `∏_{p<y}(1 - p^{-2σ})⁻¹` | `∏_{p<y}(1 + p^{-2σ})` |
| `E‖∑_{n≤N} f(n)‖²` | `N` | `#{n ≤ N squarefree}` |

Both are smaller for Rademacher, which is the right direction for an upper bound and the wrong one
for a lower bound.  So the lower chain's constants change, and this file tracks where.

## The local factor

`RMF.exp_sum_le_integral_norm_randomEulerProduct_sq` bounds the Steinhaus product below by
`exp(∑_{p<y} p^{-2σ})`, factor by factor through `e^u ≤ (1-u)⁻¹`.  The squarefree factor `1 + u`
is smaller.  The per-factor bound `e^{u/2} ≤ 1 + u` on `[0,1]` is sharp but halves the exponent;
summing instead through `log(1+u) ≥ u - u²` gives `e^{-1}exp(∑_{p<y} p^{-2σ})`, with the full
exponent (`RMF.exp_sum_sub_one_le_integral_norm_randomEulerProduct_sq_sqfree`), because
`∑_p p^{-2}` converges.  The numerator uses the full exponent: Paley–Zygmund consumes it as
`N^{2-q}/D^{1-q}`, so the halved bound would cost a power of `log x`.
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The same bound with the full exponent

The per-factor bound `e^{u/2} ≤ 1 + u` is sharp as a statement about one factor, and that is
exactly why it is the wrong tool for the product: it spends the whole of `u`'s second-order
deficit at every prime, where the deficit is summable.  What follows uses
`\log(1+u) \ge u - u^2` instead and pays `\sum_{p<y} p^{-2} \le 1` once. -/

/-- `\log(1+u) \ge u - u^2` for `u \ge 0`.

From `Real.log_le_sub_one_of_pos` at `(1+u)^{-1}`, which gives `\log(1+u) \ge u/(1+u)`, and
`u/(1+u) \ge u - u^2` since `(u - u^2)(1+u) = u - u^3 \le u`. -/
lemma sub_sq_le_log_one_add {u : ℝ} (hu : 0 ≤ u) : u - u ^ 2 ≤ Real.log (1 + u) := by
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + u)⁻¹ by positivity)
  rw [Real.log_inv] at h
  have h2 : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by
    field_simp
    ring
  rw [h2] at h
  have h3 : u / (1 + u) ≤ Real.log (1 + u) := by linarith
  refine le_trans ?_ h3
  rw [le_div_iff₀ h1u]
  nlinarith

/-- `\sum_{i<k} (i+2)^{-2} \le 1 - 1/(k+1)`, by telescoping
`(i+2)^{-2} \le 1/(i+1) - 1/(i+2)`. -/
lemma sum_range_inv_add_two_sq_le (k : ℕ) :
    ∑ i ∈ Finset.range k, (((i : ℝ) + 2) ^ 2)⁻¹ ≤ 1 - 1 / ((k : ℝ) + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk1 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hstep : (((k : ℝ) + 2) ^ 2)⁻¹ ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
      have hkey : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) - (((k : ℝ) + 2) ^ 2)⁻¹
          = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2) ^ 2) := by
        field_simp
        ring
      have hpos : (0 : ℝ) < 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2) ^ 2) := by positivity
      linarith
    push_cast
    rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 from by ring]
    linarith

/-- `\sum_{p<y} p^{-2} \le 1`.  The primes below `y` sit in `[2,y)`, and the telescoping bound
applies there. -/
lemma sum_primesBelow_inv_sq_le (y : ℕ) :
    ∑ p ∈ Nat.primesBelow y, (((p : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 := by
  have hsub : Nat.primesBelow y ⊆ Finset.Ico 2 y := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    exact Finset.mem_Ico.2 ⟨hp.2.two_le, hp.1⟩
  have hnn : ∀ p ∈ Finset.Ico 2 y, (0 : ℝ) ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ := fun p _ => by positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  have hcongr : ∀ i ∈ Finset.range (y - 2), ((((2 + i : ℕ) : ℕ) : ℝ) ^ 2)⁻¹
      = (((i : ℝ) + 2) ^ 2)⁻¹ := by
    intro i _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr]
  have h := sum_range_inv_add_two_sq_le (y - 2)
  have hpos : (0 : ℝ) < ((y - 2 : ℕ) : ℝ) + 1 := by positivity
  have : (0 : ℝ) < 1 / (((y - 2 : ℕ) : ℝ) + 1) := by positivity
  linarith

/-- **The second moment of the squarefree Euler product, from below, with the full exponent**:
`E‖F_y(s)‖² ≥ e^{-1}\exp(\sum_{p<y} p^{-2σ})` for `σ = \Re s \ge 1/2`.  This is what the
Rademacher numerator (`RMF.exists_le_integral_restricted_normSq_numerator_rademacher`) needs:
halving the exponent would turn `\log x` into `\sqrt{\log x}`, which Paley–Zygmund cannot absorb.
`\Re s \ge 1/2` makes the deficit summable: `\sum_p p^{-4\Re s} \le \sum_p p^{-2} \le 1`. -/
theorem exp_sum_sub_one_le_integral_norm_randomEulerProduct_sq_sqfree
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    Real.exp ((∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-2 * s.re)) - 1)
      ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2 ∂μ := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  rw [hf.integral_norm_randomEulerProduct_sq' y s]
  -- the product as an exponential of a sum of logs
  have hprodpos : ∀ p ∈ Nat.primesBelow y, (0 : ℝ) < 1 + (p : ℝ) ^ (-2 * s.re) := by
    intro p _
    have : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * s.re) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    linarith
  have hprod : ∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-2 * s.re))
      = Real.exp (∑ p ∈ Nat.primesBelow y, Real.log (1 + (p : ℝ) ^ (-2 * s.re))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p hp => (Real.exp_log (hprodpos p hp)).symm
  rw [hprod]
  refine Real.exp_le_exp.2 ?_
  -- per prime: `\log(1+u) ≥ u - u² ≥ u - p^{-2}`
  have hterm : ∀ p ∈ Nat.primesBelow y,
      (p : ℝ) ^ (-2 * s.re) - (((p : ℕ) : ℝ) ^ 2)⁻¹
        ≤ Real.log (1 + (p : ℝ) ^ (-2 * s.re)) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hu0 : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * s.re) := Real.rpow_nonneg hp0.le _
    have hsq : ((p : ℝ) ^ (-2 * s.re)) ^ 2 ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
      have h1 : ((p : ℝ) ^ (-2 * s.re)) ^ 2 = (p : ℝ) ^ (-4 * s.re) := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ (-2 * s.re)) 2, ← Real.rpow_mul hp0.le]
        norm_num
        ring_nf
      have h2 : ((p : ℝ)) ^ (-4 * s.re) ≤ ((p : ℝ)) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      have h3 : ((p : ℝ)) ^ (-2 : ℝ) = (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hp0.le, Real.rpow_natCast]
      rw [h1, ← h3]
      exact h2
    exact le_trans (by linarith [sub_sq_le_log_one_add hu0]) (sub_sq_le_log_one_add hu0)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  linarith [sum_primesBelow_inv_sq_le y, hsum]

/-- **The second moment at a shifted abscissa, from below, with the full exponent**:
`E‖F_y(1/2+σ)‖² ≥ e^{(n-d)-64}` — the Steinhaus order, with `RMF.le_integral_normSq_of_drop`'s
`63` become `64`; the extra `1` is `\sum_p p^{-2}`. -/
theorem le_integral_normSq_of_drop_sqfree' (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ}
    {n d y : ℕ} (hθ : (3 : ℝ) ≤ θ) (hd : d ≤ n) (hσ0 : 0 ≤ σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ Real.exp d)
    (hy : ⌊blockScale θ (n - d)⌋₊ + 1 ≤ y) :
    Real.exp (((n : ℝ) - (d : ℝ)) - 64)
      ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ := by
  have hre : (shiftLine σ 0).re = 1 / 2 + σ := re_shiftLine σ 0
  have hshalf : (1 : ℝ) / 2 ≤ (shiftLine σ 0).re := by rw [hre]; linarith
  refine le_trans (Real.exp_le_exp.2 ?_)
    (exp_sum_sub_one_le_integral_norm_randomEulerProduct_sq_sqfree hX y hshalf)
  -- from here the argument is `RMF.le_integral_normSq_of_drop`'s, verbatim
  have hsub : primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (n - d)⌋₊ + 1)
      ⊆ Nat.primesBelow y := by
    intro p hp
    rw [mem_primesIco] at hp
    exact Nat.mem_primesBelow.2 ⟨by omega, hp.1⟩
  have hterm : ∀ p ∈ Nat.primesBelow y, (0 : ℝ) ≤ (p : ℝ) ^ (-2 * (shiftLine σ 0).re) :=
    fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hterm p hp
  have hcongr : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (n - d)⌋₊ + 1),
      (p : ℝ) ^ (-2 * (shiftLine σ 0).re) = (p : ℝ) ^ (-1 - 2 * σ) := by
    intro p _
    rw [hre, rpow_neg_two_half_add]
  rw [Finset.sum_congr rfl hcongr] at hle
  linarith [le_sum_rpow_primesIco_of_drop hθ hd hσ0 hσ, hle]

/-! ### The smooth tail, Rademacher

`RMF.smoothTailIntegral_eq_line` is stated at `RMF.IsBoundedRMF` with the Dirichlet identity as
an input, so both laws feed it.  The bound that follows is at the **same** `RMF.eulerBound`, since
the squarefree Euler product obeys it (`RMF.norm_randomEulerProduct_sqfree_le`). -/

/-- The Dirichlet identity in the shape `RMF.smoothTailIntegral_eq_line` consumes.  Unconditional,
because `RMF.dirichletSeries_smoothCoeff_eq_sqfree` is. -/
lemma ae_dirichletSeries_smoothCoeff_eq_sqfree (y : ℕ) :
    ∀ᵐ ω ∂μ, ∀ z : ℂ, 0 < z.re →
      dirichletSeries (smoothCoeff (fun ω => squarefreeExtension fun p => X p ω) y ω) z
        = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) z ω :=
  Filter.Eventually.of_forall fun ω z _ => dirichletSeries_smoothCoeff_eq_sqfree y ω z

/-- **The smooth tail integral is bounded, Rademacher.**  The twin of
`RMF.smoothTailIntegral_le`, at the same constant. -/
lemma smoothTailIntegral_le_sqfree (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) :
    ∀ᵐ ω ∂μ, smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) y σ ω
      ≤ (2 * Real.pi)⁻¹ * (8 * eulerBound (y + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [smoothTailIntegral_eq_line (IsRademacherRMF.isBoundedRMF hRa) y
      (ae_dirichletSeries_smoothCoeff_eq_sqfree y) hσ,
    ae_forall_norm_le_one hX norm_le_one_rademacherLaw (y + 1)] with ω heq hω
  rw [heq]
  exact mul_le_mul_of_nonneg_left (integral_lineDivSqOf_sqfree_le hσ hω) (by positivity)

/-! ### The fourth moment of the prime linear form

The Steinhaus proof's spine is `RMF.sq_primeLinearForm`, `S² = ∑_{(p,q)} c_p c_q f(pq)`, which is
**complete** multiplicativity.  For the squarefree extension `f(p)f(q) = f(pq)` holds only when
`p ≠ q`; at `p = q` it gives `f(p)² = 1` while `f(p²) = 0`.

**That single diagonal is the whole difference.**  Writing `pairIndex (p,q)` for `1` when `p = q`
and `pq` otherwise, `f(p)f(q) = f(pairIndex (p,q))` holds *always* at primes, and the Steinhaus
argument goes through with `pairIndex` in place of the product — except in the fibre count, where
the diagonal fibre has `#s` elements rather than at most two.  That is what turns the constant `2`
into `3`, and by `RMF.reduction_lower_meanSquare`'s existential it does not matter which. -/

/-- `1` on the diagonal, the product off it.  At primes, `f(p)·f(q) = f (pairIndex (p,q))`. -/
def pairIndex (z : ℕ × ℕ) : ℕ := if z.1 = z.2 then 1 else z.1 * z.2

lemma squarefree_pairIndex {z : ℕ × ℕ} (h1 : z.1.Prime) (h2 : z.2.Prime) :
    Squarefree (pairIndex z) := by
  rw [pairIndex]
  split_ifs with h
  · exact squarefree_one
  · exact (Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_primes h1 h2).2 h, h1.squarefree,
      h2.squarefree⟩)

lemma pairIndex_ne_zero {z : ℕ × ℕ} (h1 : z.1.Prime) (h2 : z.2.Prime) : pairIndex z ≠ 0 := by
  rw [pairIndex]
  split_ifs
  · exact one_ne_zero
  · exact Nat.mul_ne_zero h1.ne_zero h2.ne_zero

/-- The prime values square to one, almost surely. -/
lemma ae_sq_X_eq_one (hX : IsRademacherPrimeValues X μ) {p : ℕ} (hp : p.Prime) :
    ∀ᵐ ω ∂μ, (X p ω) ^ 2 = 1 := by
  have hmeasP : Measurable fun z : ℂ => z ^ 2 = 1 :=
    measurableSet_setOf.1 (measurableSet_eq_fun (by fun_prop) measurable_const)
  exact ((hX.hasLaw p hp).ae_iff hmeasP).2 sq_eq_one_rademacherLaw

/-- **The pair identity.**  `f(p)·f(q) = f (pairIndex (p,q))` at primes — off the diagonal this is
ordinary multiplicativity at coprime arguments, and on it `f(p)² = 1`. -/
lemma mul_squarefreeExtension_prime (hX : IsRademacherPrimeValues X μ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) :
    ∀ᵐ ω ∂μ, ∀ z ∈ s ×ˢ s,
      squarefreeExtension (fun p => X p ω) z.1 * squarefreeExtension (fun p => X p ω) z.2
        = squarefreeExtension (fun p => X p ω) (pairIndex z) := by
  have hall : ∀ p ∈ s, ∀ᵐ ω ∂μ, (X p ω) ^ 2 = 1 :=
    fun p hp => ae_sq_X_eq_one hX (hs p hp)
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω z hz
  rw [Finset.mem_product] at hz
  have h1 := hs z.1 hz.1
  have h2 := hs z.2 hz.2
  rw [squarefreeExtension_apply_prime _ h1, squarefreeExtension_apply_prime _ h2, pairIndex]
  split_ifs with h
  · rw [squarefreeExtension_apply_one, ← h, ← sq]
    exact hω z.1 hz.1
  · rw [(isMultiplicative_squarefreeExtension (fun p => X p ω)).map_mul_of_coprime
      ((Nat.coprime_primes h1 h2).2 h), squarefreeExtension_apply_prime _ h1,
      squarefreeExtension_apply_prime _ h2]

/-- **The fibres of `pairIndex` at primes.**  If two prime pairs share a `pairIndex` then either
both are diagonal, or they are equal, or one is the other swapped.

This is the whole combinatorial content: the diagonal fibre is *large* — every `(p,p)` maps to
`1` — where the Steinhaus fibre `z₁z₂ = w₁w₂` has at most two elements.  Bounding the diagonal
block by `(∑‖cₖ‖²)²` instead of term-by-term is what costs the extra `1`. -/
lemma pairIndex_eq_cases {z w : ℕ × ℕ} (hz1 : z.1.Prime) (hz2 : z.2.Prime)
    (hw1 : w.1.Prime) (hw2 : w.2.Prime) (h : pairIndex z = pairIndex w) :
    (z.1 = z.2 ∧ w.1 = w.2) ∨ w = z ∨ w = (z.2, z.1) := by
  rw [pairIndex, pairIndex] at h
  split_ifs at h with hz hw hw
  · exact Or.inl ⟨hz, hw⟩
  · exact absurd h.symm (by
      have := Nat.one_lt_mul_iff.2 ⟨hw1.pos, hw2.pos, Or.inl hw1.one_lt⟩
      omega)
  · exact absurd h (by
      have := Nat.one_lt_mul_iff.2 ⟨hz1.pos, hz2.pos, Or.inl hz1.one_lt⟩
      omega)
  · have hdvd : z.1 ∣ w.1 * w.2 := ⟨z.2, h.symm⟩
    rcases (Nat.Prime.dvd_mul hz1).1 hdvd with hd | hd
    · have e1 : z.1 = w.1 := (Nat.prime_dvd_prime_iff_eq hz1 hw1).1 hd
      have e2 : z.2 = w.2 := by
        have h' := h
        rw [e1] at h'
        exact Nat.eq_of_mul_eq_mul_left hw1.pos h'
      exact Or.inr (Or.inl (Prod.ext e1.symm e2.symm))
    · have e1 : z.1 = w.2 := (Nat.prime_dvd_prime_iff_eq hz1 hw2).1 hd
      have e2 : z.2 = w.1 := by
        have h' := h
        rw [e1, mul_comm w.1 w.2] at h'
        exact Nat.eq_of_mul_eq_mul_left hw2.pos h'
      exact Or.inr (Or.inr (Prod.ext e2.symm e1.symm))

omit [MeasurableSpace Ω] in
/-- The square of the prime linear form, as a single sum over pairs.  The mirror of
`RMF.sq_primeLinearForm`, with `pairIndex` where it has the product. -/
lemma sq_primeLinearForm_sqfree {f : Ω → ArithmeticFunction ℂ} {s : Finset ℕ} (c : ℕ → ℂ)
    {ω : Ω} (hω : ∀ z ∈ s ×ˢ s, f ω z.1 * f ω z.2 = f ω (pairIndex z)) :
    primeLinearForm f s c ω ^ 2
      = ∑ p ∈ s, ∑ q ∈ s, c p * c q * f ω (pairIndex (p, q)) := by
  rw [primeLinearForm, sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← hω (p, q) (Finset.mem_product.2 ⟨hp, hq⟩)]
  ring

/-- A guarded value is nonnegative when the value is. -/
lemma ite_nonneg_of_nonneg {P : Prop} [Decidable P] {V : ℝ} (hV : 0 ≤ V) :
    0 ≤ (if P then V else 0) := by
  split_ifs
  · exact hV
  · exact le_rfl

/-- The weighted diagonal of `s ×ˢ s` is `∑ₖ ‖cₖ‖²`. -/
lemma sum_diag_weight (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ w ∈ s ×ˢ s, (if w.1 = w.2 then ‖c w.1‖ * ‖c w.2‖ else 0))
      = ∑ p ∈ s, ‖c p‖ ^ 2 := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only
  rw [Finset.sum_ite_eq s p (fun q => ‖c p‖ * ‖c q‖), if_pos hp]
  ring

/-- The full square of `s ×ˢ s`, weighted, is `(∑ₖ‖cₖ‖²)²`. -/
lemma sum_prod_weight (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ z ∈ s ×ˢ s, ‖c z.1‖ ^ 2 * ‖c z.2‖ ^ 2) = (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']

/-- **The fibre sum.**  The trichotomy of `RMF.pairIndex_eq_cases` splits it into the diagonal
block, `w = z`, and `w = swap z`; each contributes `(∑ₖ‖cₖ‖²)²`, the last because the weight is
swap-invariant.  Hence the constant `3`, where the Steinhaus fibre — of size at most two — gives
`2`. -/
lemma fibre_sum_pairIndex_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) :
    (∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
      (if pairIndex z = pairIndex w then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
      ≤ 3 * (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
  classical
  have hpt : ∀ z ∈ s ×ˢ s, ∀ w ∈ s ×ˢ s,
      (if pairIndex z = pairIndex w then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0)
        ≤ (if z.1 = z.2 ∧ w.1 = w.2 then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0)
          + (if w = z then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0)
          + (if w = (z.2, z.1) then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0) := by
    intro z hz w hw
    rw [Finset.mem_product] at hz hw
    have hV : (0 : ℝ) ≤ ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) := by positivity
    have hA := ite_nonneg_of_nonneg (P := z.1 = z.2 ∧ w.1 = w.2) hV
    have hB := ite_nonneg_of_nonneg (P := w = z) hV
    have hC := ite_nonneg_of_nonneg (P := w = (z.2, z.1)) hV
    by_cases heq : pairIndex z = pairIndex w
    · rw [if_pos heq]
      rcases pairIndex_eq_cases (hs z.1 hz.1) (hs z.2 hz.2) (hs w.1 hw.1) (hs w.2 hw.2) heq with
          h | h | h
      · rw [if_pos h] at hA ⊢; linarith
      · rw [if_pos h] at hB ⊢; linarith
      · rw [if_pos h] at hC ⊢; linarith
    · rw [if_neg heq]; linarith
  refine le_trans (Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun w hw => hpt z hz w hw) ?_
  simp_rw [Finset.sum_add_distrib]
  -- the diagonal block
  have hA : (∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
      (if z.1 = z.2 ∧ w.1 = w.2 then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
      = (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
    have hinner : ∀ z ∈ s ×ˢ s, (∑ w ∈ s ×ˢ s,
        (if z.1 = z.2 ∧ w.1 = w.2 then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
        = (if z.1 = z.2 then ‖c z.1‖ * ‖c z.2‖ else 0) * ∑ p ∈ s, ‖c p‖ ^ 2 := by
      intro z _
      by_cases hz : z.1 = z.2
      · rw [if_pos hz, ← sum_diag_weight s c, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hw : w.1 = w.2
        · rw [if_pos ⟨hz, hw⟩, if_pos hw]
        · rw [if_neg (fun h => hw h.2), if_neg hw, mul_zero]
      · rw [if_neg hz, zero_mul]
        exact Finset.sum_eq_zero fun w _ => if_neg (fun h => hz h.1)
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, sum_diag_weight s c, sq]
  -- the two off-diagonal blocks
  have hB : (∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
      (if w = z then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
      = (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
    have hinner : ∀ z ∈ s ×ˢ s, (∑ w ∈ s ×ˢ s,
        (if w = z then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
        = ‖c z.1‖ ^ 2 * ‖c z.2‖ ^ 2 := by
      intro z hz
      rw [Finset.sum_ite_eq' (s ×ˢ s) z
        (fun w => ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖)), if_pos hz]
      ring
    rw [Finset.sum_congr rfl hinner, sum_prod_weight s c]
  have hC : (∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
      (if w = (z.2, z.1) then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
      = (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
    have hinner : ∀ z ∈ s ×ˢ s, (∑ w ∈ s ×ˢ s,
        (if w = (z.2, z.1) then ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0))
        = ‖c z.1‖ ^ 2 * ‖c z.2‖ ^ 2 := by
      intro z hz
      rw [Finset.mem_product] at hz
      have hswap : (z.2, z.1) ∈ s ×ˢ s := Finset.mem_product.2 ⟨hz.2, hz.1⟩
      rw [Finset.sum_ite_eq' (s ×ˢ s) (z.2, z.1)
        (fun w => ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖)), if_pos hswap]
      ring
    rw [Finset.sum_congr rfl hinner, sum_prod_weight s c]
  rw [hA, hB, hC]
  ring_nf
  exact le_rfl

/-- **The fourth moment of the prime linear form, Rademacher**:
`E‖∑_{p∈s} c_p f(p)‖⁴ ≤ 3(∑_{p∈s}‖c_p‖²)²`, the twin of
`RMF.integral_norm_pow_four_primeLinearForm_le`, whose constant is `2`.  The extra `1` is the
diagonal: `pairIndex` sends every `(p,p)` to `1`, so that fibre has `#s` elements where the
Steinhaus fibre `z₁z₂ = w₁w₂` has at most two.  Only the absoluteness of the constant matters. -/
theorem integral_norm_pow_four_primeLinearForm_le_sqfree
    (hX : IsRademacherPrimeValues X μ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) :
    (∫ ω, ‖primeLinearForm (fun ω => squarefreeExtension fun p => X p ω) s c ω‖ ^ 4 ∂μ)
      ≤ 3 * (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
  classical
  haveI := hX.isProbabilityMeasure
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hRa : IsRademacherRMF f μ := hX.isRademacherRMF
  have hne : ∀ z ∈ s ×ˢ s, pairIndex z ≠ 0 := fun z hz => by
    rw [Finset.mem_product] at hz
    exact pairIndex_ne_zero (hs z.1 hz.1) (hs z.2 hz.2)
  have hsf : ∀ z ∈ s ×ˢ s, Squarefree (pairIndex z) := fun z hz => by
    rw [Finset.mem_product] at hz
    exact squarefree_pairIndex (hs z.1 hz.1) (hs z.2 hz.2)
  -- the square, as a single sum over pairs
  have hsq : ∀ᵐ ω ∂μ, primeLinearForm f s c ω ^ 2
      = ∑ z ∈ s ×ˢ s, c z.1 * c z.2 * f ω (pairIndex z) := by
    filter_upwards [mul_squarefreeExtension_prime hX hs] with ω hω
    rw [Finset.sum_product]
    exact sq_primeLinearForm_sqfree (f := f) c hω
  -- the fourth power, expanded
  have hexp : ∀ᵐ ω ∂μ, ((‖primeLinearForm f s c ω‖ ^ 4 : ℝ) : ℂ)
      = ∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
          c z.1 * c z.2 * (starRingEnd ℂ) (c w.1 * c w.2)
            * (f ω (pairIndex z) * (starRingEnd ℂ) (f ω (pairIndex w))) := by
    filter_upwards [hsq] with ω hω
    have h4 : (‖primeLinearForm f s c ω‖ ^ 4 : ℝ) = ‖primeLinearForm f s c ω ^ 2‖ ^ 2 := by
      rw [norm_pow]; ring
    rw [h4, Complex.ofReal_pow, ← Complex.mul_conj', hω, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by simp only [map_mul]; ring
  -- integrate, using orthogonality on each cross term
  have hint : ∀ z ∈ s ×ˢ s, ∀ w ∈ s ×ˢ s,
      Integrable (fun ω => c z.1 * c z.2 * (starRingEnd ℂ) (c w.1 * c w.2)
        * (f ω (pairIndex z) * (starRingEnd ℂ) (f ω (pairIndex w)))) μ :=
    fun z _ w _ => (hRa.integrable_mul_conj (pairIndex z) (pairIndex w)).const_mul _
  have hval : ((∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ : ℝ) : ℂ)
      = ∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
          (if pairIndex z = pairIndex w then
            c z.1 * c z.2 * (starRingEnd ℂ) (c w.1 * c w.2) else 0) := by
    rw [← integral_complex_ofReal, integral_congr_ae hexp]
    rw [integral_finsetSum _ fun z hz => integrable_finsetSum _ fun w hw => hint z hz w hw]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [integral_finsetSum _ fun w hw => hint z hz w hw]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [integral_const_mul, hRa.orthogonality (hne z hz) (hne w hw)]
    by_cases heq : pairIndex z = pairIndex w
    · rw [if_pos ⟨heq, hsf z hz⟩, if_pos heq]; ring
    · rw [if_neg (fun h => heq h.1), if_neg heq]; ring
  -- pass to moduli
  have hnn : (0 : ℝ) ≤ ∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ :=
    integral_nonneg fun ω => by positivity
  have hmod : (∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ)
      ≤ ∑ z ∈ s ×ˢ s, ∑ w ∈ s ×ˢ s,
          (if pairIndex z = pairIndex w then
            ‖c z.1‖ * ‖c z.2‖ * (‖c w.1‖ * ‖c w.2‖) else 0) := by
    have h1 : (∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ)
        = ‖((∫ ω, ‖primeLinearForm f s c ω‖ ^ 4 ∂μ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [h1, hval]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun z _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun w _ => ?_)
    split
    · rw [norm_mul, norm_mul, Complex.norm_conj, norm_mul]
    · simp
  exact le_trans hmod (fibre_sum_pairIndex_le hs c)

/-! ### Khintchine for the Rademacher function, with the constant supplied

`RMF.khintchine_rough_rademacher` carries `K` as a hypothesis.  The fourth moment just proved
supplies it at `K = 3`, so the Rademacher analogue of `RMF.khintchine_rough` is unconditional. -/

/-- The `Real.rpow` form of `RMF.integral_norm_pow_four_primeLinearForm_le_sqfree`, which is what
`RMF.khintchine_rough_rademacher` asks for.  The mirror of
`RMF.integral_norm_rpow_four_primeLinearForm_le`. -/
lemma integral_norm_rpow_four_primeLinearForm_le_sqfree
    (hX : IsRademacherPrimeValues X μ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (c : ℕ → ℂ) :
    (∫ ω, ‖primeLinearForm (fun ω => squarefreeExtension fun p => X p ω) s c ω‖ ^ (4 : ℝ) ∂μ)
      ≤ 3 * (∑ p ∈ s, ‖c p‖ ^ 2) ^ 2 := by
  haveI := hX.isProbabilityMeasure
  have heq :
      (∫ ω, ‖primeLinearForm (fun ω => squarefreeExtension fun p => X p ω) s c ω‖ ^ (4 : ℝ) ∂μ)
        = ∫ ω, ‖primeLinearForm (fun ω => squarefreeExtension fun p => X p ω) s c ω‖ ^ 4 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [heq]
  exact integral_norm_pow_four_primeLinearForm_le_sqfree hX hs c

/-- **Khintchine on the rough part, for the Rademacher function**, unconditional: the `K = 3`
instance of `RMF.khintchine_rough_rademacher`,
`E‖∑_{n≤x} f(n)‖^{2q} ≥ 3^{-(1-q)} E(∑_{y<p≤x} ‖∑_{m≤x/p} f(m)‖²)^q` for `q ∈ [2/3,1]`.
The constant is `3` rather than the Steinhaus `2` because the `RMF.pairIndex` diagonal fibre has
`#s` elements; `RMF.reduction_lower_meanSquare` is existential in its constants. -/
theorem khintchine_rough_rademacher_three (hX : IsRademacherPrimeValues X μ)
    {x : ℝ} {y : ℕ} (hx : 1 ≤ x) (hxy : ⌊x⌋₊ < (y + 1) ^ 2)
    {q : ℝ} (hq23 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    (3 : ℝ) ^ (-(1 - q)) * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊,
        ‖randomSum (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2) ^ q ∂μ
      ≤ ∫ ω, ‖randomSum (fun ω => squarefreeExtension fun r => X r ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  exact khintchine_rough_rademacher hX hx hxy (by norm_num)
    (fun v => integral_norm_rpow_four_primeLinearForm_le_sqfree hX
      (fun p hp => (mem_largePrimeSet.1 hp).2) v) hq23 hq1

/-! ### The lower-bound chain, end to end, for the Rademacher function -/

/-- **The lower-bound chain, end to end**, Rademacher: the `K = 3` instance of
`RMF.meanSquare_le_momentOf`, with the Khintchine input supplied by
`RMF.khintchine_rough_rademacher_three`.  The mirror of `RMF.meanSquare_le_moment`, with `2`
replaced by `3`; the threshold `x₀` does not depend on `f`, `ν`, `x` or `q`. -/
theorem meanSquare_le_moment_rademacher :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (ν : Measure Ω), IsRademacherRMF f ν →
      ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        (3 : ℝ) ^ (-(1 - q)) * ((x / 8) ^ q * (∫ ω, meanSquareIntegral f x ω ^ q ∂ν)
            - (x / (8 * Real.log x ^ 2)) ^ q - (8 * x / Real.log x) ^ q)
          ≤ ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂ν := by
  obtain ⟨x₀, h⟩ := meanSquare_le_momentOf (Ω := Ω)
  refine ⟨x₀, fun f ν hf x q hx hq23 hq1 => ?_⟩
  obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  exact h _ ν (IsRademacherRMF.isBoundedRMF hY.isRademacherRMF) 3 (by norm_num)
    (fun x q hx1 hxy hq23 hq1 => khintchine_rough_rademacher_three hY hx1 hxy hq23 hq1)
    x q hx hq23 hq1

/-- **Harper's Proposition 3, first bound**, Rademacher: the `K = 3` instance of
`RMF.reduction_lower_meanSquareOf`.

The mirror of `RMF.reduction_lower_meanSquare`; the leading constant is `3^{-1/4}·√(1/8)` where
the Steinhaus one is `2^{-1/4}·√(1/8)`, and the statement is existential in it either way. -/
theorem reduction_lower_meanSquare_rademacher :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (f : Ω → ArithmeticFunction ℂ) (ν : Measure Ω), IsRademacherRMF f ν →
        ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
          c * ((∫ ω, meanSquareIntegral f x ω ^ q ∂ν) ^ (1 / (2 * q))
                - C / Real.sqrt (Real.log x))
            ≤ (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂ν) ^ (1 / (2 * q)) :=
  reduction_lower_meanSquareOf (by norm_num) (meanSquare_le_moment_rademacher (Ω := Ω))

/-! ### The smooth tail in Harper's max form -/
/-- **The smooth tail's `q`-th moment, in Harper's max form**: the Rademacher analogue of
`RMF.integral_rpow_smoothTail_le`.  Where the Steinhaus bound lands on `E[chaosShift^q]` — one
window, reached by rotation invariance — this lands on the maximum over windows, which is what
Harper's Proposition 4 subtracts.  The law-specific inputs are `RMF.IsRademacherRMF.isBoundedRMF`
and `RMF.dirichletSeries_smoothCoeff_eq_sqfree`, which needs no hypothesis on `s`. -/
theorem integral_rpow_smoothTail_le_max_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {δ : ℝ} (hδ0 : 0 ≤ δ) (y : ℕ)
    {q : ℝ} (hq0 : 5 / 8 < q) (hq1 : q ≤ 1) :
    (∫ ω, smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) y (1 / 2 + δ) ω ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
        * ⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
            * ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
                lineSqOf (1 / 2 + δ) (fun ω => squarefreeExtension fun p => X p ω) (y + 1) ω t)
                  ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hL : (∫ ω, smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) y
        (1 / 2 + δ) ω ^ q ∂μ)
      = ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
          lineDivSqOf (1 / 2 + δ) (fun ω => squarefreeExtension fun p => X p ω) (y + 1) ω t)
            ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [smoothTailIntegral_eq_line (IsRademacherRMF.isBoundedRMF hX.isRademacherRMF) y
      (Filter.Eventually.of_forall fun ω z _ => dirichletSeries_smoothCoeff_eq_sqfree y ω z)
      (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + δ)] with ω heq
    rw [heq]
    rfl
  rw [hL]
  exact integral_rpow_line_le_max_rademacher_sup hX (by linarith) (y + 1)
    (by positivity) hq0 hq1

/-! ### Four Rademacher inputs to the shifted-tail chain

`RMF.rpow_smoothTail_sub_le` is law-free, and `RMF.integrableOn_smoothTail` and
`RMF.measurable_meanSquareIntegral` take `RMF.IsBoundedRMF`.  The four below supply the rest. -/

/-- The joint measurability of `RMF.lineSqOf` for the squarefree product, as a
`StronglyMeasurable` on `Ω × ℝ`. -/
lemma stronglyMeasurable_lineSqOf_sqfree (hX : IsRademacherPrimeValues X μ) (σ : ℝ) (N : ℕ) :
    StronglyMeasurable fun z : Ω × ℝ =>
      lineSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2 := by
  simp only [lineSqOf]
  exact ((measurable_randomEulerProduct_sqfree_uncurry
    (fun p hp => hX.measurable p hp) σ N).norm.pow_const 2).stronglyMeasurable

/-- The same for `RMF.lineDivSqOf`. -/
lemma stronglyMeasurable_lineDivSqOf_sqfree (hX : IsRademacherPrimeValues X μ) (σ : ℝ) (N : ℕ) :
    StronglyMeasurable fun z : Ω × ℝ =>
      lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) N z.1 z.2 := by
  simp only [lineDivSqOf]
  refine (((measurable_randomEulerProduct_sqfree_uncurry
    (fun p hp => hX.measurable p hp) σ N).div ?_).norm.pow_const 2).stronglyMeasurable
  exact (Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I |>.const_add _

/-- **The lower side, Rademacher.**  The twin of `RMF.smoothTail_ge_chaosShift`. -/
lemma smoothTail_ge_chaosShift_sqfree (hX : IsRademacherPrimeValues X μ) {x δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hlog : 0 < Real.log x) :
    ∀ᵐ ω ∂μ, (2 * Real.pi)⁻¹ * (4 / 5) * (Real.log x
        * chaosShift (fun ω => squarefreeExtension fun p => X p ω) x δ ω)
      ≤ smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) ⌊x⌋₊ (1 / 2 + δ) ω := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [smoothTailIntegral_eq_line (IsRademacherRMF.isBoundedRMF hRa) ⌊x⌋₊
      (ae_dirichletSeries_smoothCoeff_eq_sqfree ⌊x⌋₊) (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + δ),
    ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊x⌋₊ + 1)] with ω heq hω
  have hw := integral_lineDivSqOf_ge (G := fun ω => squarefreeExtension fun p => X p ω)
    (N := ⌊x⌋₊ + 1) (ω := ω) (1 / 2 + δ) (by linarith) (by linarith)
    (measurable_randomEulerProduct_sqfree_line (1 / 2 + δ))
    (fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using (by linarith : (1:ℝ)/2 ≤ 1/2+δ)))
  rw [heq, chaosShift_eqOf]
  have hcancel : (2 * Real.pi)⁻¹ * (4 / 5) * (Real.log x * ((Real.log x)⁻¹
        * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
            lineSqOf (1 / 2 + δ) (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1) ω t))
      = (2 * Real.pi)⁻¹ * ((4 / 5)
          * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
              lineSqOf (1 / 2 + δ) (fun ω => squarefreeExtension fun p => X p ω)
                (⌊x⌋₊ + 1) ω t) := by
    field_simp
  rw [hcancel]
  exact mul_le_mul_of_nonneg_left hw (by positivity)

/-- **The `q`-th power of the shifted tail is integrable, Rademacher.** -/
lemma integrable_smoothTail_rpow_sqfree (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ q : ℝ}
    (hσ : 1 / 2 ≤ σ) (hq : 0 ≤ q) :
    Integrable
      (fun ω => smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) y σ ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hmeas : AEStronglyMeasurable
      (fun ω => smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) y σ ω ^ q) μ := by
    have hL := (stronglyMeasurable_lineDivSqOf_sqfree hX σ (y + 1)).integral_prod_right'
      (ν := volume)
    have hmap : AEStronglyMeasurable (fun ω => ((2 * Real.pi)⁻¹ * ∫ t : ℝ,
        lineDivSqOf σ (fun ω => squarefreeExtension fun p => X p ω) (y + 1) ω t) ^ q) μ :=
      (Real.continuous_rpow_const hq).comp_aestronglyMeasurable
        (hL.aestronglyMeasurable.const_mul _)
    refine hmap.congr ?_
    filter_upwards [smoothTailIntegral_eq_line (IsRademacherRMF.isBoundedRMF hRa) y
      (ae_dirichletSeries_smoothCoeff_eq_sqfree y) hσ] with ω heq
    rw [heq]
    rfl
  set B : ℝ := (2 * Real.pi)⁻¹ * (8 * eulerBound (y + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n)
    with hBdef
  refine (memLp_top_of_bound hmeas (B ^ q) ?_).integrable le_top
  filter_upwards [smoothTailIntegral_le_sqfree hX y hσ] with ω hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (smoothTailIntegral_nonneg _ _ _ _) q)]
  exact Real.rpow_le_rpow (smoothTailIntegral_nonneg _ _ _ _) hb hq

/-- **The `q`-th power of the shifted Euler-product integral is integrable, Rademacher.** -/
lemma integrable_chaosShift_rpow_sqfree (hX : IsRademacherPrimeValues X μ) {y δ q : ℝ}
    (hy : 0 ≤ (Real.log y)⁻¹) (hδ : 0 ≤ δ) (hq : 0 ≤ q) :
    Integrable
      (fun ω => chaosShift (fun ω => squarefreeExtension fun p => X p ω) y δ ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊y⌋₊ + 1)
  have hmeas : AEStronglyMeasurable
      (fun ω => chaosShift (fun ω => squarefreeExtension fun p => X p ω) y δ ω ^ q) μ := by
    have hSq := stronglyMeasurable_lineSqOf_sqfree hX (1 / 2 + δ) (⌊y⌋₊ + 1)
    have hW := hSq.integral_prod_right'
      (ν := volume.restrict (Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ)))
    have hmap : AEStronglyMeasurable (fun ω => ((Real.log y)⁻¹ *
        ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2 : ℝ),
          lineSqOf (1 / 2 + δ) (fun ω => squarefreeExtension fun p => X p ω)
            (⌊y⌋₊ + 1) ω t) ^ q) μ :=
      (Real.continuous_rpow_const hq).comp_aestronglyMeasurable
        (hW.aestronglyMeasurable.const_mul _)
    refine hmap.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [chaosShift_eqOf]
  refine (memLp_top_of_bound hmeas
    (((Real.log y)⁻¹ * eulerBound (⌊y⌋₊ + 1) ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (chaosShift_nonnegOf hy ω) q)]
  refine Real.rpow_le_rpow (chaosShift_nonnegOf hy ω) ?_ hq
  rw [chaosShift_eqOf]
  refine mul_le_mul_of_nonneg_left ?_ hy
  have h := window_leOf (1 / 2 + δ) (F := fun ω => squarefreeExtension fun p => X p ω)
    (N := ⌊y⌋₊ + 1) (ω := ω) (measurable_randomEulerProduct_sqfree_line (1 / 2 + δ))
    (fun t => norm_randomEulerProduct_sqfree_le hω
      (by simpa using (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + δ))) (-(1 : ℝ) / 2)
  rw [show (-(1 : ℝ) / 2 + 1) = (1 / 2 : ℝ) by norm_num] at h
  exact h

/-- **The `q`-th power of the mean-square integral is integrable, Rademacher.** -/
lemma integrable_meanSquare_rpow_sqfree (hX : IsRademacherPrimeValues X μ) {x q : ℝ}
    (hx : Real.exp 1 ≤ x) (hq : 0 ≤ q) :
    Integrable
      (fun ω => meanSquareIntegral (fun ω => squarefreeExtension fun p => X p ω) x ω ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by nlinarith
  set B : ℝ := (2 * Real.pi)⁻¹ * (8 * eulerBound (⌊x⌋₊ + 1) ^ 2 * ∑' n : ℤ, shiftWeight 1 n)
    with hBdef
  have hnn : ∀ ω, 0 ≤ meanSquareIntegral (fun ω => squarefreeExtension fun p => X p ω) x ω := by
    intro ω
    refine mul_nonneg (by positivity) ?_
    rw [intervalIntegral.integral_of_le hsx]
    exact setIntegral_nonneg measurableSet_Ioc fun _z hz =>
      div_nonneg (sq_nonneg _) (by positivity)
  refine (memLp_top_of_bound
    ((measurable_meanSquareIntegral (IsRademacherRMF.isBoundedRMF hRa)
      hx1.le).pow_const q).aestronglyMeasurable
    (((Real.log x)⁻¹ * B) ^ q) ?_).integrable le_top
  filter_upwards [integrableOn_smoothTail (IsRademacherRMF.isBoundedRMF hRa)
      ⌊x⌋₊ (le_refl (1 / 2 : ℝ)),
    smoothTailIntegral_le_sqfree hX ⌊x⌋₊ (le_refl (1 / 2 : ℝ))] with ω hint hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hnn ω) q)]
  refine Real.rpow_le_rpow (hnn ω) ?_ hq
  have hkey := meanSquare_le_smoothTail (f := fun ω => squarefreeExtension fun p => X p ω) hx hint
  rw [le_inv_mul_iff₀ hlog]
  linarith

/-! ### Harper's Proposition 4, before the `2q`-th root

Proposition 4 differs from Proposition 3 in one term: the main term keeps
the single window `[-1/2,1/2]`, and only the SUBTRACTED term becomes a maximum over windows.  So
the assembly below is the Steinhaus one with `E[chaosShift^q]` replaced by
`RMF.windowMaxMoment` in the subtracted position, and nowhere else. -/

/-- **The maximum Harper's Proposition 4 subtracts**: the windows' `q`-th moments
`E((2π)⁻¹∫_{(n,n+1]} ‖A(½+σ+it)‖² dt)^q`, damped by `(|n|+1)^{-1/4}`, supremum over `n ∈ ℤ` (`0`
if unbounded).  The damping is what makes the residual `∑_n (|n|+1)^{1/4}/(|n|^{2q}+1)` converge,
which it does exactly when `q > 5/8`. -/
noncomputable def windowMaxMoment (F : Ω → ArithmeticFunction ℂ) (x σ q : ℝ)
    (ν : Measure Ω) : ℝ :=
  ⨆ n : ℤ, (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
    * ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν

/-- **The maximum, split at `N₀`**: if the damped moments `(|n|+1)^{-1/4}·Eₙ` are at most `T` for
`|n| ≤ N₀`, every `Eₙ` is at most `B`, and `(N₀+1)^{-1/4}B ≤ T`, then `RMF.windowMaxMoment ≤ T`.
The sharp hypothesis is on the damped moment because the chaos estimate has no uniform bound on
`|n| ≤ N₀`: its constant grows with the window, doubly logarithmically through
`RMF.harperWindowLevel`, since a window at height `w` forces an offset of `10·ℓogℓog w`.  What is
uniform is the damped moment, because `(|n|+1)^{-1/4}` beats `(ℓogℓog|n|)²`. -/
lemma windowMaxMoment_le_of_split_damped {F : Ω → ArithmeticFunction ℂ} {x σ q : ℝ}
    {ν : Measure Ω} {N₀ : ℕ} {B T : ℝ}
    (hE0 : ∀ n : ℤ, (0 : ℝ) ≤ ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν)
    (hsmall : ∀ n : ℤ, |n| ≤ (N₀ : ℤ) →
      (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4)
        * (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
          lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν) ≤ T)
    (hlarge : ∀ n : ℤ,
      (∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν) ≤ B)
    (hNB : ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) * B ≤ T) :
    windowMaxMoment F x σ q ν ≤ T := by
  refine ciSup_le fun n => ?_
  set E : ℝ := ∫ ω, ((2 * Real.pi)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
    lineSqOf (1 / 2 + σ) F (⌊x⌋₊ + 1) ω t) ^ q ∂ν with hEdef
  by_cases hn : |n| ≤ (N₀ : ℤ)
  · exact hsmall n hn
  · have hcast : ((N₀ : ℝ) + 1) ≤ |(n : ℝ)| + 1 := by
      have h : (N₀ : ℤ) < |n| := lt_of_not_ge hn
      have h' : ((N₀ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h.le
      rw [Int.cast_abs] at h'
      push_cast at h' ⊢
      linarith
    have h1 : (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) ≤ ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcast (by norm_num)
    calc (|(n : ℝ)| + 1) ^ (-(1 : ℝ) / 4) * E
        ≤ ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) * E := mul_le_mul_of_nonneg_right h1 (hE0 n)
      _ ≤ ((N₀ : ℝ) + 1) ^ (-(1 : ℝ) / 4) * B :=
          mul_le_mul_of_nonneg_left (hlarge n) (Real.rpow_nonneg (by positivity) _)
      _ ≤ T := hNB

/-- `RMF.windowMaxMoment` is nonnegative whether or not the family is bounded above: if it is, the
supremum dominates the `n = 0` term, and if it is not, `Real.sSup` is `0` by convention. -/
lemma windowMaxMoment_nonneg (F : Ω → ArithmeticFunction ℂ) (x σ q : ℝ) (ν : Measure Ω) :
    0 ≤ windowMaxMoment F x σ q ν :=
  Real.iSup_nonneg fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (by positivity) (integral_lineSqOf_nonneg _ _ _)) q)

/-- `RMF.integral_rpow_smoothTail_le_max_rademacher`, read through `RMF.windowMaxMoment`. -/
lemma integral_rpow_smoothTail_le_windowMaxMoment (hX : IsRademacherPrimeValues X μ) {x δ : ℝ}
    (hδ0 : 0 ≤ δ) {q : ℝ} (hq0 : 5 / 8 < q) (hq1 : q ≤ 1) :
    (∫ ω, smoothTailIntegral (fun ω => squarefreeExtension fun p => X p ω) ⌊x⌋₊
        (1 / 2 + δ) ω ^ q ∂μ)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
        * windowMaxMoment (fun ω => squarefreeExtension fun p => X p ω) x δ q μ :=
  integral_rpow_smoothTail_le_max_rademacher hX hδ0 ⌊x⌋₊ hq0 hq1

/-- **Harper's Proposition 4, before the `2q`-th root.**  The twin of
`RMF.meanSquare_ge_chaosShift`, with the subtracted Euler-product integral replaced by
`RMF.windowMaxMoment`, divided by `(log x)^q` because the maximum is over UNnormalised windows. -/
theorem meanSquare_ge_chaosShift_rademacher :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ x q V : ℝ, Real.exp 1 ≤ x → 2 / 3 ≤ q → q ≤ 1 → 0 ≤ V →
          4 * V / Real.log x ≤ 1 / 2 →
          c * (∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x
                (4 * V / Real.log x) ω ^ q ∂ν)
              - C * Real.exp (-(2 * V * q))
                  * windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x
                      (2 * V / Real.log x) q ν / Real.log x ^ q
            ≤ ∫ ω, meanSquareIntegral (fun ω => squarefreeExtension fun p => Y p ω) x ω ^ q ∂ν := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbase : (0 : ℝ) < (2 * Real.pi)⁻¹ * (4 / 5) := by positivity
  have hinv1 : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right; linarith
  have hbase1 : (2 * Real.pi)⁻¹ * (4 / 5) ≤ 1 := by nlinarith [hbase.le]
  have hW23 : (0 : ℝ) < 8 * ∑' n : ℤ,
      shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
    have h0 : (0 : ℝ) < ∑' n : ℤ,
        shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
      (summable_shiftWeight_mul_abs_add_one_rpow (by norm_num)).tsum_pos
        (fun n => mul_nonneg (shiftWeight_nonneg _ n) (Real.rpow_nonneg (by positivity) _)) 0
        (mul_pos (shiftWeight_pos _ 0) (Real.rpow_pos_of_pos (by norm_num) _))
    linarith
  refine ⟨(2 * Real.pi)⁻¹ * (4 / 5),
    8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4),
    hbase, hW23, ?_⟩
  intro Y ν hY x q V hx hq23 hq1 hV hV1
  haveI := hY.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hx
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hq0 : (0 : ℝ) < q := by linarith
  have hδ0 : (0 : ℝ) ≤ 4 * V / Real.log x := by positivity
  have hδ'0 : (0 : ℝ) ≤ 2 * V / Real.log x := by positivity
  have hδ'1 : 2 * V / Real.log x ≤ 1 / 2 := by
    have heq : 2 * V / Real.log x = 1 / 2 * (4 * V / Real.log x) := by ring
    rw [heq]; nlinarith
  set F : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => Y p ω with hFdef
  set L4 : ℝ := Real.log x ^ q with hL4def
  set P : ℝ := ∫ ω, chaosShift F x (4 * V / Real.log x) ω ^ q ∂ν with hPdef
  set S : ℝ := windowMaxMoment F x (2 * V / Real.log x) q ν with hSdef
  set M : ℝ := ∫ ω, meanSquareIntegral F x ω ^ q ∂ν with hMdef
  have hL40 : (0 : ℝ) < L4 := Real.rpow_pos_of_pos hlog q
  have hP0 : (0 : ℝ) ≤ P :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (chaosShift_nonnegOf (inv_nonneg.2 hlog.le) ω) q
  have hS0 : (0 : ℝ) ≤ S := windowMaxMoment_nonneg _ _ _ _ _
  -- integrability
  have hIT4 : Integrable
      (fun ω => smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q) ν :=
    integrable_smoothTail_rpow_sqfree hY ⌊x⌋₊ (by linarith) hq0.le
  have hIT2 : Integrable
      (fun ω => smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q) ν :=
    integrable_smoothTail_rpow_sqfree hY ⌊x⌋₊ (by linarith) hq0.le
  have hIM : Integrable (fun ω => meanSquareIntegral F x ω ^ q) ν :=
    integrable_meanSquare_rpow_sqfree hY hx hq0.le
  -- the pointwise chain, integrated
  have hchain : (∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q ∂ν)
        - Real.exp (-(2 * V * q))
            * ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂ν
      ≤ L4 * M := by
    have hRHS : (∫ ω, (Real.log x * meanSquareIntegral F x ω) ^ q ∂ν) = L4 * M := by
      rw [hL4def, hMdef, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        Real.mul_rpow hlog.le (meanSquareIntegral_nonneg hx1.le ω))
    have hIR : Integrable (fun ω => (Real.log x * meanSquareIntegral F x ω) ^ q) ν := by
      refine (hIM.const_mul (Real.log x ^ q)).congr ?_
      exact Filter.Eventually.of_forall fun ω =>
        (Real.mul_rpow hlog.le (meanSquareIntegral_nonneg hx1.le ω)).symm
    have hmono : (∫ ω, (smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q
          - Real.exp (-(2 * V * q))
              * smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q) ∂ν)
        ≤ ∫ ω, (Real.log x * meanSquareIntegral F x ω) ^ q ∂ν := by
      refine integral_mono_ae (hIT4.sub (hIT2.const_mul _)) hIR ?_
      filter_upwards [integrableOn_smoothTail (IsRademacherRMF.isBoundedRMF hRa) ⌊x⌋₊
          (show (1 : ℝ) / 2 ≤ 1 / 2 + 4 * V / Real.log x by linarith),
        integrableOn_smoothTail (IsRademacherRMF.isBoundedRMF hRa) ⌊x⌋₊
          (show (1 : ℝ) / 2 ≤ 1 / 2 + 2 * V / Real.log x by linarith),
        integrableOn_smoothTail (IsRademacherRMF.isBoundedRMF hRa) ⌊x⌋₊
          (le_refl (1 / 2 : ℝ))]
        with ω i4 i2 ih
      exact rpow_smoothTail_sub_le hx hV hq0.le hq1 i4 i2 ih
    rw [integral_sub hIT4 (hIT2.const_mul _), integral_const_mul, hRHS] at hmono
    exact hmono
  -- the lower side
  have hi : ((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * (L4 * P)
      ≤ ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q ∂ν := by
    have hexp : ((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * (L4 * P)
        = ∫ ω, ((2 * Real.pi)⁻¹ * (4 / 5)
            * (Real.log x * chaosShift F x (4 * V / Real.log x) ω)) ^ q ∂ν := by
      rw [hL4def, hPdef, ← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      rw [Real.mul_rpow hbase.le
          (mul_nonneg hlog.le (chaosShift_nonnegOf (inv_nonneg.2 hlog.le) ω)),
        Real.mul_rpow hlog.le (chaosShift_nonnegOf (inv_nonneg.2 hlog.le) ω)]
    rw [hexp]
    refine integral_mono_ae ?_ hIT4 ?_
    · exact ((integrable_chaosShift_rpow_sqfree hY (inv_nonneg.2 hlog.le) hδ0 hq0.le).const_mul
        (((2 * Real.pi)⁻¹ * (4 / 5)) ^ q * Real.log x ^ q)).congr
        (Filter.Eventually.of_forall fun ω => by
          simp only
          rw [Real.mul_rpow hbase.le
              (mul_nonneg hlog.le (chaosShift_nonnegOf (inv_nonneg.2 hlog.le) ω)),
            Real.mul_rpow hlog.le (chaosShift_nonnegOf (inv_nonneg.2 hlog.le) ω)]
          ring)
    · filter_upwards [smoothTail_ge_chaosShift_sqfree hY hδ0 hV1 hlog] with ω hb
      exact Real.rpow_le_rpow
        (mul_nonneg hbase.le (mul_nonneg hlog.le
          (chaosShift_nonnegOf (inv_nonneg.2 hlog.le) ω))) hb hq0.le
  -- the upper side: the maximum, not one window
  have hii : (∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂ν)
      ≤ 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S :=
    integral_rpow_smoothTail_le_windowMaxMoment hY hδ'0 (by linarith) hq1
  -- the constants
  have hcq : (2 * Real.pi)⁻¹ * (4 / 5) ≤ ((2 * Real.pi)⁻¹ * (4 / 5)) ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_ge hbase hbase1 hq1
    rwa [Real.rpow_one] at h
  have hCq : 8 * (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
      ≤ 8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
    have h := tsum_shiftWeight_mul_abs_add_one_rpow_le (q₀ := 2 / 3) (by norm_num) hq23
    linarith
  have hE : (0 : ℝ) < Real.exp (-(2 * V * q)) := Real.exp_pos _
  -- combine, then divide by `L4`
  have hlow : (2 * Real.pi)⁻¹ * (4 / 5) * (L4 * P)
      ≤ ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 4 * V / Real.log x) ω ^ q ∂ν := by
    refine le_trans (mul_le_mul_of_nonneg_right hcq (mul_nonneg hL40.le hP0)) hi
  have hup : Real.exp (-(2 * V * q))
        * ∫ ω, smoothTailIntegral F ⌊x⌋₊ (1 / 2 + 2 * V / Real.log x) ω ^ q ∂ν
      ≤ Real.exp (-(2 * V * q))
        * ((8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * S) := by
    refine mul_le_mul_of_nonneg_left (le_trans hii ?_) hE.le
    exact mul_le_mul_of_nonneg_right hCq hS0
  have hfinal : L4 * ((2 * Real.pi)⁻¹ * (4 / 5) * P
      - (8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
          * Real.exp (-(2 * V * q)) * S / L4)
      ≤ L4 * M := by
    have hexp : L4 * ((2 * Real.pi)⁻¹ * (4 / 5) * P
        - (8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
            * Real.exp (-(2 * V * q)) * S / L4)
        = (2 * Real.pi)⁻¹ * (4 / 5) * (L4 * P)
          - Real.exp (-(2 * V * q))
            * ((8 * ∑' n : ℤ, shiftWeight (2 / 3 : ℝ) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
                * S) := by
      field_simp
    rw [hexp]
    linarith
  exact le_of_mul_le_mul_left hfinal hL40

/-- **Harper's Proposition 4.**  The `2q`-th root of
`RMF.meanSquare_ge_chaosShift_rademacher`, composed with
`RMF.reduction_lower_meanSquare_rademacher`.

`‖∑_{n≤x}f(n)‖_{2q} ≫ √(x/log x)( ‖∫_{-1/2}^{1/2}|F(½+4V/log x+it)|²dt‖_q^{1/2}`
`  − (C/e^V)·(max_N (|N|+1)^{-1/4}E[(∫_{window N})^q])^{1/(2q)} − C )`,

divided through by `√x`.  The maximum sits where Proposition 3 has the single window at
`2V/log x`, and **nowhere else** — the main term is unchanged.

The exponent bookkeeping is `RMF.reduction_lower_chaosShift`'s verbatim: the `2q`-th root turns
`e^{-2Vq}` into `e^{-V}` because `2Vq·(1/(2q)) = V`, and `RMF.prop3_arith2` keeps the exported
constants free of `q`. -/
theorem reduction_lower_chaosShift_rademacher :
    ∃ c C V₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < V₀ ∧
      ∀ V : ℝ, V₀ ≤ V → ∃ x₀ : ℝ,
        ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
          ∀ x q : ℝ, x₀ ≤ x → 2 / 3 ≤ q → q ≤ 1 →
            c * ((∫ ω, chaosShift (fun ω => squarefreeExtension fun p => Y p ω) x
                    (4 * V / Real.log x) ω ^ q ∂ν) ^ (1 / (2 * q))
                  - C / Real.exp V
                      * (windowMaxMoment (fun ω => squarefreeExtension fun p => Y p ω) x
                          (2 * V / Real.log x) q ν / Real.log x ^ q) ^ (1 / (2 * q))
                  - C / Real.sqrt (Real.log x))
              ≤ (∫ ω, ‖normalisedSum (fun ω => squarefreeExtension fun p => Y p ω) x ω‖
                  ^ (2 * q) ∂ν) ^ (1 / (2 * q)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hM⟩ := meanSquare_ge_chaosShift_rademacher (Ω := Ω)
  obtain ⟨c₂, C₂, hc₂, hC₂, x₀, hprop⟩ := reduction_lower_meanSquare_rademacher (Ω := Ω)
  have hc₀0 : (0 : ℝ) < min c₁ 1 := lt_min hc₁ one_pos
  refine ⟨c₂ * min c₁ 1, max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1), 1, by positivity,
    lt_of_lt_of_le (by positivity : (0 : ℝ) < C₂ / min c₁ 1) (le_max_right _ _), one_pos, ?_⟩
  intro V hV
  refine ⟨max x₀ (Real.exp (8 * V)), fun Y ν hY x q hx hq23 hq1 => ?_⟩
  haveI := hY.isProbabilityMeasure
  set F : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => Y p ω with hFdef
  -- scales
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxV : Real.exp (8 * V) ≤ x := le_trans (le_max_right _ _) hx
  have hV0 : (0 : ℝ) ≤ V := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxV
  have hL8V : 8 * V ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxV
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hxe : Real.exp 1 ≤ x := le_trans (Real.exp_le_exp.2 (by linarith)) hxV
  have hx1 : (1 : ℝ) ≤ x := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith [hxe]
  have hshift : 4 * V / Real.log x ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hr1 : 1 / (2 * q) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hlinv : (0 : ℝ) ≤ (Real.log x)⁻¹ := by positivity
  -- nonnegativity
  have hE4 : (0 : ℝ) ≤ ∫ ω, chaosShift F x (4 * V / Real.log x) ω ^ q ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosShift_nonnegOf hlinv ω) _
  have hE2 : (0 : ℝ) ≤ windowMaxMoment F x (2 * V / Real.log x) q ν / Real.log x ^ q :=
    div_nonneg (windowMaxMoment_nonneg _ _ _ _ _) (Real.rpow_nonneg hL0.le _)
  have hS0 : (0 : ℝ) ≤ ∫ ω, meanSquareIntegral F x ω ^ q ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (meanSquareIntegral_nonneg hx1 ω) _
  -- the `M`-chain, at the `2q`-th power
  have hMc := hM Y ν hY x q V hxe hq23 hq1 hV0 hshift
  rw [show C₁ * Real.exp (-(2 * V * q))
        * windowMaxMoment F x (2 * V / Real.log x) q ν / Real.log x ^ q
      = C₁ * Real.exp (-(2 * V * q))
        * (windowMaxMoment F x (2 * V / Real.log x) q ν / Real.log x ^ q) from
    mul_div_assoc _ _ _] at hMc
  -- `sub_zero` rather than `linarith`: the goal's integrands carry `V / ℓog x`, and
  -- linarith's denominator-clearing step cannot rewrite under the integral's binder
  have hthree := rpow_sub_three_le hS0 (mul_nonneg hc₁.le hE4)
    (mul_nonneg (mul_nonneg hC₁.le (Real.exp_pos _).le) hE2) le_rfl
    (by rw [sub_zero]; exact hMc) hr0.le hr1
  rw [Real.zero_rpow (ne_of_gt hr0), sub_zero, Real.mul_rpow hc₁.le hE4,
    Real.mul_rpow (mul_nonneg hC₁.le (Real.exp_pos _).le) hE2,
    Real.mul_rpow hC₁.le (Real.exp_pos _).le] at hthree
  have hexp : (Real.exp (-(2 * V * q))) ^ (1 / (2 * q)) = (Real.exp V)⁻¹ := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_neg]
    congr 1
    field_simp
  rw [hexp] at hthree
  -- the constants stay `q`-free
  have hK1 : min c₁ 1 ≤ c₁ ^ (1 / (2 * q)) := by
    rcases le_or_gt c₁ 1 with h | h
    · refine le_trans (min_le_left _ _) ?_
      calc c₁ = c₁ ^ (1 : ℝ) := (Real.rpow_one c₁).symm
        _ ≤ c₁ ^ (1 / (2 * q)) := Real.rpow_le_rpow_of_exponent_ge hc₁ h hr1
    · exact le_trans (min_le_right _ _) (Real.one_le_rpow h.le hr0.le)
  have hK2 : C₁ ^ (1 / (2 * q))
      ≤ min c₁ 1 * max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1) := by
    refine le_trans (rpow_le_one_add hC₁.le hr0.le hr1) ?_
    have h := mul_le_mul_of_nonneg_left
      (le_max_left ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1)) hc₀0.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hc₀0)] at h
  have hC₂' : C₂ ≤ min c₁ 1 * max ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1) := by
    have h := mul_le_mul_of_nonneg_left
      (le_max_right ((1 + C₁) / min c₁ 1) (C₂ / min c₁ 1)) hc₀0.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hc₀0)] at h
  -- and the first bound
  have hP := hprop F ν hY.isRademacherRMF x q hxx₀ hq23 hq1
  exact prop3_arith2 (Real.rpow_nonneg hE4 _) (Real.rpow_nonneg hE2 _) (Real.exp_pos V)
    (Real.sqrt_pos.2 hL0) hc₂ hK1 hK2 hC₂' hthree hP

end RMF
