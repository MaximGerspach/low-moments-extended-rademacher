/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import RMF.Reduction.Smoothing

/-!
# Reassembling the smoothing windows

The main term of the smoothing step in Harper's proof of his Proposition 3 (Harper, *Moments of
random multiplicative functions, I*, arXiv:1703.06654).  After smoothing, the main term is

`∑_{√x<p≤x} log p · (X/p) ∫_p^{p(1+1/X)} ‖∑_{m≤x/t} f(m)‖² dt`,

and its dependence on `p` is now *only* through the window `(p, p(1+1/X)]`.  So the sum can be
pulled inside the integral: it becomes `∫ ‖∑_{m≤x/t} f(m)‖² w(t) dt` with

`w(t) = X ∑_{p < t ≤ p(1+1/X)} (log p)/p`,

and `RMF.window_weight_ge` says `w(t) ≥ 1/2` on `[√x, x]`.  The substitution `z = x/t` then turns
the `t`-integral into `x ∫ ‖∑_{m≤z} f(m)‖² dz/z²`, which is `RMF.meanSquareIntegral` up to the
`(log x)⁻¹` in its definition.

## Where the range comes from

The window at `p` reaches down to `p`, so a `t` below `√x(1+1/X)` can be covered by primes below
`√x`, which are not in the sum.  The `t`-integral therefore starts at `√x(1+1/X)` rather than
`√x`, and after the substitution the `z`-integral ends at `√x/(1+1/X)` rather than `√x`.  The
missing sliver has expected mass `log(1+1/X) ≤ 1/X`, which is the same order as everything else
the reduction discards.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*}

/-! ### The substitution `z = x/t` -/

/-- The image of `(a, b]` under `t ↦ x/t` is `[x/b, x/a)`. -/
lemma image_div_Ioc {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) :
    (fun t => x / t) '' Set.Ioc a b = Set.Ico (x / b) (x / a) := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  ext z
  simp only [Set.mem_image, Set.mem_Ioc, Set.mem_Ico]
  constructor
  · rintro ⟨t, ⟨hat, htb⟩, rfl⟩
    have ht0 : (0 : ℝ) < t := lt_trans ha hat
    refine ⟨?_, ?_⟩
    · rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ ht0 htb) hx.le
    · have hgap : x / a - x / t = x * (t - a) / (a * t) := by field_simp
      have hpos : (0 : ℝ) < x * (t - a) / (a * t) :=
        div_pos (by nlinarith) (by positivity)
      linarith
  · rintro ⟨h1, h2⟩
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le (by positivity) h1
    refine ⟨x / z, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hz0]
      rw [lt_div_iff₀ ha] at h2
      linarith
    · rw [div_le_iff₀ hz0]
      rw [div_le_iff₀ hb] at h1
      linarith
    · field_simp

/-- **The substitution `z = x/t`.**  For `0 < a ≤ b`,
`∫_a^b G(x/t) dt = x ∫_{x/b}^{x/a} G(z) dz/z²`.

`G` is arbitrary — no continuity — because the change of variables used is the measure-theoretic
one, `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`.  That matters: the `G` this is
applied to is a step function of `z`. -/
lemma setIntegral_comp_div {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) (G : ℝ → ℝ) :
    (∫ t in Set.Ioc a b, G (x / t)) = x * ∫ z in Set.Ioc (x / b) (x / a), G z / z ^ 2 := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hderiv : ∀ t ∈ Set.Ioc a b,
      HasDerivWithinAt (fun t => x / t) (-(x / t ^ 2)) (Set.Ioc a b) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans ha ht.1)
    have h := (hasDerivAt_inv ht0).const_mul x
    have he : x * -(t ^ 2)⁻¹ = -(x / t ^ 2) := by field_simp
    rw [he] at h
    have h2 : (fun u : ℝ => x * u⁻¹) = fun u : ℝ => x / u := by
      funext u
      rw [div_eq_mul_inv]
    rw [h2] at h
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun t => x / t) (Set.Ioc a b) := by
    intro u hu v hv huv
    have hu0 : (0 : ℝ) < u := lt_trans ha hu.1
    have hv0 : (0 : ℝ) < v := lt_trans ha hv.1
    simp only at huv
    field_simp at huv
    linarith
  have hmain := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioc hderiv hinj (fun z => x * (G z / z ^ 2))
  rw [image_div_Ioc hx ha hab] at hmain
  have hrhs : (∫ t in Set.Ioc a b, |-(x / t ^ 2)| • (x * (G (x / t) / (x / t) ^ 2)))
      = ∫ t in Set.Ioc a b, G (x / t) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans ha ht.1
    rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity)]
    field_simp
  rw [hrhs, MeasureTheory.integral_Ico_eq_integral_Ioc, integral_const_mul] at hmain
  exact hmain.symm

/-! ### The swap -/

/-- For `t ≥ 1` the moving cutoff `x/t` is below `x`, so the summatory function is bounded
uniformly along the whole range of integration. -/
lemma norm_randomSum_div_le (f : Ω → ArithmeticFunction ℂ) {x t : ℝ} (hx : 0 ≤ x) (ht : 1 ≤ t)
    (ω : Ω) : ‖randomSum f (x / t) ω‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f ω n‖ := by
  have h : x / t ≤ x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact norm_randomSum_le_of_le f h ω

/-- Hence the integrand of the window integrals is integrable on any interval above `1`. -/
lemma integrableOn_normSq_randomSum_div (f : Ω → ArithmeticFunction ℂ) {x c d : ℝ} (hx : 0 ≤ x)
    (hc : 1 ≤ c) (ω : Ω) :
    IntegrableOn (fun t => ‖randomSum f (x / t) ω‖ ^ 2) (Set.Ioc c d) := by
  refine Measure.integrableOn_of_bounded (M := (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f ω n‖) ^ 2)
    measure_Ioc_lt_top.ne
    ((measurable_randomSum_div f x ω).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_randomSum_div_le f hx (le_trans hc ht.1.le) ω) 2

/-- **The swap, for any integrand.**  At `X = log x` the windows `(p, p(1+1/X)]` of the primes
`√x < p ≤ x` cover `(√x(1+1/X), x]` with total weight `w(t) ≥ 1/2` (`RMF.window_weight_ge`),
so the window averages of a nonnegative `G`, summed with weights `log p`, dominate half of its
integral over that range.  Only nonnegativity and integrability on intervals above `1` are used;
Harper's case is `RMF.half_setIntegral_le_window_sum`. -/
theorem half_setIntegral_le_window_sumOf :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ G : ℝ → ℝ, (∀ t, 0 ≤ G t) →
      (∀ c d : ℝ, 1 ≤ c → IntegrableOn G (Set.Ioc c d)) →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        1 / 2 * (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x, G t)
          ≤ ∑ p ∈ S, Real.log p * (Real.log x / p
              * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), G t) := by
  obtain ⟨x₀, hw⟩ := window_weight_ge
  refine ⟨max x₀ 4, fun x hx G hG0 hGi S hSp hS => ?_⟩
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hXpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  set r : ℝ := 1 + 1 / Real.log x with hrdef
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr1 : (1 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  set a : ℝ := Real.sqrt x * r with hadef
  have hsqa : Real.sqrt x < a := by nlinarith
  have ha1 : (1 : ℝ) ≤ a := by linarith
  set c : ℕ → ℝ := fun p => Real.log p * (Real.log x / p) with hcdef
  have hc0 : ∀ p : ℕ, 0 ≤ c p := by
    intro p
    rw [hcdef]
    exact mul_nonneg (Real.log_natCast_nonneg p) (by positivity)
  -- integrability, on the range and on each window
  have hIG : IntegrableOn G (Set.Ioc a x) := hGi a x ha1
  have hIind : ∀ p : ℕ, IntegrableOn (Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G)
      (Set.Ioc a x) := fun p => hIG.indicator measurableSet_Ioc
  -- (1) each window integral dominates its part inside the range
  have hstep1 : ∀ p ∈ S, (∫ t in Set.Ioc a x,
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t)
      ≤ ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * r), G t := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSp p hp).two_le
    rw [setIntegral_indicator measurableSet_Ioc]
    refine setIntegral_mono_set (hGi p (p * r) (by linarith))
      (Filter.Eventually.of_forall hG0) ?_
    exact LE.le.eventuallyLE Set.inter_subset_right
  -- (2) the finite sum comes out of the integral
  have hstep2 : (∫ t in Set.Ioc a x, ∑ p ∈ S, c p *
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t)
      = ∑ p ∈ S, c p * ∫ t in Set.Ioc a x,
          Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t := by
    rw [integral_finsetSum _ fun p _ => (hIind p).const_mul (c p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  -- (3) the weight is at least `1/2` on the range
  have hstep3 : ∀ t ∈ Set.Ioc a x, 1 / 2 * G t ≤ ∑ p ∈ S, c p *
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t := by
    intro t ht
    have hat : a < t := ht.1
    have htx : t ≤ x := ht.2
    have hsqt : Real.sqrt x ≤ t := le_of_lt (lt_trans hsqa hat)
    -- the primes of the window at `t`
    set W : Finset ℕ := S.filter (fun q : ℕ => (q : ℝ) < t ∧ t ≤ (q : ℝ) * r) with hWdef
    have hmem : ∀ p : ℕ, p.Prime → (p : ℝ) < t → t ≤ (p : ℝ) * r → p ∈ W := by
      intro p hprime hpt htp
      rw [hWdef]
      refine Finset.mem_filter.2 ⟨hS p hprime ?_ (le_of_lt (lt_of_lt_of_le hpt htx)), hpt, htp⟩
      nlinarith
    have hweight := hw x t hxx₀ hsqt htx W hmem
    -- the indicator sum collapses onto that set
    have hcollapse : (∑ p ∈ S, c p *
        Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t) = (∑ p ∈ W, c p) * G t := by
      rw [Finset.sum_mul, hWdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : (p : ℝ) < t ∧ t ≤ (p : ℝ) * r
      · rw [if_pos hp, Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hp.1, hp.2⟩)]
      · rw [if_neg hp, Set.indicator_of_notMem (fun hm => hp (Set.mem_Ioc.1 hm)), mul_zero]
    rw [hcollapse]
    have hcsum : (1 : ℝ) / 2 ≤ ∑ p ∈ W, c p := by
      refine le_trans hweight (le_of_eq ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [hcdef]; ring
    nlinarith [hG0 t]
  -- (4) assemble
  have hI2 : IntegrableOn (fun t => ∑ p ∈ S, c p *
      Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t) (Set.Ioc a x) :=
    integrable_finsetSum _ fun p _ => (hIind p).const_mul (c p)
  calc 1 / 2 * (∫ t in Set.Ioc a x, G t)
      = ∫ t in Set.Ioc a x, 1 / 2 * G t := (integral_const_mul _ _).symm
    _ ≤ ∫ t in Set.Ioc a x, ∑ p ∈ S, c p *
          Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t :=
        setIntegral_mono_on (hIG.const_mul _) hI2 measurableSet_Ioc hstep3
    _ = ∑ p ∈ S, c p * ∫ t in Set.Ioc a x,
          Set.indicator (Set.Ioc (p : ℝ) ((p : ℝ) * r)) G t := hstep2
    _ ≤ ∑ p ∈ S, c p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * r), G t :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hstep1 p hp) (hc0 p)
    _ = ∑ p ∈ S, Real.log p * (Real.log x / p
          * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * r), G t) :=
        Finset.sum_congr rfl fun p _ => by rw [hcdef]; ring

/-- **The swap**, for Harper's integrand `‖∑_{m≤x/t} f(m)‖²`: the instance of
`RMF.half_setIntegral_le_window_sumOf`.

Nothing probabilistic happens here: the statement is pointwise in `ω`, and `f` enters only
through the boundedness of its partial sums. -/
theorem half_setIntegral_le_window_sum :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (ω : Ω) (x : ℝ), x₀ ≤ x →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        1 / 2 * (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
            ‖randomSum f (x / t) ω‖ ^ 2)
          ≤ ∑ p ∈ S, Real.log p * (Real.log x / p
              * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
                  ‖randomSum f (x / t) ω‖ ^ 2) := by
  obtain ⟨x₀, h⟩ := half_setIntegral_le_window_sumOf
  exact ⟨max x₀ 0, fun f ω x hx S hSp hS =>
    h x (le_trans (le_max_left _ _) hx) _ (fun t => by positivity)
      (fun c d hc => integrableOn_normSq_randomSum_div f (le_trans (le_max_right _ _) hx) hc ω)
      S hSp hS⟩

/-! ### The main term -/

/-- **The main term.**  At `X = log x`, the `log p`-weighted sum of the smoothed window averages
dominates half of `x ∫_1^{√x/(1+1/X)} ‖∑_{m≤z} f(m)‖² dz/z²`, which is `RMF.meanSquareIntegral`
up to the `(log x)⁻¹` in that definition and the truncation at `√x/(1+1/X)`.  A `t` below
`√x(1+1/X)` is reached only from primes below `√x`, which are not in the sum; the sliver
`(√x/(1+1/X), √x]` costs an expected `log(1+1/X) ≤ 1/X` (`RMF.integral_sliverIntegral_le`). -/
theorem half_meanSquare_le_window_sum :
    ∃ x₀ : ℝ, ∀ (f : Ω → ArithmeticFunction ℂ) (ω : Ω) (x : ℝ), x₀ ≤ x →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        1 / 2 * (x * ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
            ‖randomSum f z ω‖ ^ 2 / z ^ 2)
          ≤ ∑ p ∈ S, Real.log p * (Real.log x / p
              * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
                  ‖randomSum f (x / t) ω‖ ^ 2) := by
  obtain ⟨x₀, hswap⟩ := half_setIntegral_le_window_sum (Ω := Ω)
  refine ⟨max x₀ 4, fun f ω x hx S hSp hS => ?_⟩
  have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hXpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hX1 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    nlinarith [Real.exp_one_lt_d9]
  set r : ℝ := 1 + 1 / Real.log x with hrdef
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hr2 : r ≤ 2 := by
    have h : 1 / Real.log x ≤ 1 := by
      rw [div_le_one hXpos]
      linarith
    linarith
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsq2 : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h4
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have ha0 : (0 : ℝ) < Real.sqrt x * r := by positivity
  have hax : Real.sqrt x * r ≤ x := by nlinarith
  have h1 : x / x = 1 := div_self (ne_of_gt hx0)
  have h2 : x / (Real.sqrt x * r) = Real.sqrt x / r := by
    field_simp
    nlinarith
  have hsubst : (∫ t in Set.Ioc (Real.sqrt x * r) x, ‖randomSum f (x / t) ω‖ ^ 2)
      = x * ∫ z in Set.Ioc 1 (Real.sqrt x / r), ‖randomSum f z ω‖ ^ 2 / z ^ 2 := by
    have h := setIntegral_comp_div hx0 ha0 hax (fun z => ‖randomSum f z ω‖ ^ 2)
    rw [h1, h2] at h
    exact h
  rw [← hsubst]
  exact hswap f ω x hxx₀ S hSp hS

end RMF
