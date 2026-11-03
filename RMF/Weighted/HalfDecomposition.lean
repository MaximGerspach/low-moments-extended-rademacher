/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfFirstMoment
import RMF.Weighted.LowerReduction

/-!
# The decomposition at `q = ½`

`RMF.exists_le_integral_sqrt_lineDiv_half`: for `V ≥ 1` and `x ≥ x₀(V)`, with `F` over the primes
up to `x` and a constant independent of `V` and `x`,

`E[((log x)^{-1}∫_ℝ |F(½+2V/log x+it)|²/|2V/log x+it|² dt)^{1/2}] ≫ V^{-1/2}(log log x)^{3/4}`.

This is the main term of the lower reduction
`RMF.exists_le_integral_norm_weightedRademacherSum_half_line`, and (6.3) of the paper
(the proof of Theorem 1.2 at `q = ½`).  The line is cut into
the windows `RMF.halfWindow k`, one Paley–Zygmund estimate is made per window, and the estimates
add along the disjoint events `E(k) = E_≤(k) ∩ E_>(k)`, one per scale.  The inputs are the
barriered first moment (Proposition 6.3 of the paper,
`RMF.exists_le_setIntegral_halfBarrier_halfAfter`), the second moment (Proposition 6.4,
`RMF.exists_integral_sq_setIntegral_halfBarrier_le`), and the small-prime statements (C2)
`RMF.integral_halfTwist_pair_le` and (C3) `RMF.le_setIntegral_halfLadder_twist`, which replace
Propositions 6.1 and 6.2 of the paper.

## Map

* **Deterministic steps**: reverse Hölder in Young form (`RMF.le_integral_weight_sqrt`); the line
  dominates the weighted window sum (`RMF.sum_setIntegral_halfWindow_le_integral_div`); the primes
  below `scaleCut k₀` cost the constant `RMF.halfHeadConst`; square roots add along disjoint
  events; together, the pointwise step `RMF.ae_sum_indicator_sqrt_halfWindowMass_le`.
* **Independence across the cut at `scaleCut k`** (`RMF.setIntegral_mul_split_primeAlgebra`):
  `E_≤(k)` lives below it, `E_>(k)` and the barrier `L(k,h)` above.
* **The numerator** is `≥ |halfWindow k|·c₃·c₄` by (C3) and the first moment
  (`RMF.le_integral_setIntegral_twist_normSq`); **the denominator** is `≤ e^{132}` times the second
  moment's quantity by (C2) (`RMF.integral_invCube_mul_sq_setIntegral_le`).
* **The Paley–Zygmund estimate at one scale** (`RMF.le_integral_indicator_sqrt_halfWindowMass`,
  at `P = e^t/√(t-k)` in `RMF.le_integral_indicator_sqrt_halfWindowMass_final`) and the sum over
  scales (`RMF.le_integral_sqrt_integral_lineDiv`).
* **The choice**: `σ = 2V/log x`, `t = ⌊log(1/σ)⌋-4`, `y = ⌊x⌋₊+1`, `K = [k₀+2, ⌊t/2⌋]`; then
  `|K| ≥ t/4` and `(log x)^{-1/2}e^{t/2} ≥ e^{-5/2}(2V)^{-1/2}` (`RMF.final_arith`).
-/

open MeasureTheory

set_option linter.style.longFile 2800

namespace RMF

/-! ### Reverse Hölder with a weight

The decomposition needs to go from the two moments `∫ wY` and `∫ wY²` down to `∫ w√Y`, with
`w = 1_{E(k)}‖F_{(k₀,k]}(σ)‖`; the unweighted
`RMF.integral_le_rpow_integral_rpow_mul_rpow_integral_sq` cannot be used, because dividing out
`‖F_{(k₀,k]}(σ)‖³` is exactly what keeps (C2)'s second moment bounded.

Hölder at the conjugate pair `(3/2, 3)` under `w·μ` would give
`∫ wY ≤ (∫ w√Y)^{2/3}(∫ wY²)^{1/3}`.  It is used in Young form, with one free parameter `λ` in
place of the optimisation, which loses only the constant `(3/4)√(3/2) = 0.918…`.  The pointwise
inequality behind it, `3λ²u² ≤ 2λ³u + u⁴` at `u = √Y`, is the factorisation
`u(u-λ)²(u+2λ) ≥ 0`. -/

section ReverseHolder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The pointwise Young inequality behind the split: `u² ≤ (2λ/3)u + u⁴/(3λ²)` for `u ≥ 0`,
which is `u(u-λ)²(u+2λ) ≥ 0` divided by `3λ²`. -/
private lemma sq_le_young_sq {u lam : ℝ} (hu : 0 ≤ u) (hlam : 0 < lam) :
    u ^ 2 ≤ 2 * lam / 3 * u + 1 / (3 * lam ^ 2) * u ^ 4 := by
  have hfac : 0 ≤ u * ((u - lam) ^ 2 * (u + 2 * lam)) :=
    mul_nonneg hu (mul_nonneg (sq_nonneg _) (by linarith))
  have hpos : (0 : ℝ) < 3 * lam ^ 2 := by positivity
  rw [← sub_nonneg]
  have hid : 2 * lam / 3 * u + 1 / (3 * lam ^ 2) * u ^ 4 - u ^ 2
      = u * ((u - lam) ^ 2 * (u + 2 * lam)) / (3 * lam ^ 2) := by
    field_simp
    ring
  rw [hid]
  exact div_nonneg hfac hpos.le

/-- **Weighted Young at the reverse-Hölder split.**  For `w, Y ≥ 0` and any `λ > 0`,
`∫ wY ≤ (2λ/3)·∫ w√Y + (3λ²)⁻¹·∫ wY²`. -/
theorem integral_weight_mul_le_young {w Y : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hY : ∀ ω, 0 ≤ Y ω)
    {lam : ℝ} (hlam : 0 < lam)
    (h0 : Integrable (fun ω => w ω * Y ω) μ)
    (h1 : Integrable (fun ω => w ω * Real.sqrt (Y ω)) μ)
    (h2 : Integrable (fun ω => w ω * Y ω ^ 2) μ) :
    (∫ ω, w ω * Y ω ∂μ)
      ≤ 2 * lam / 3 * (∫ ω, w ω * Real.sqrt (Y ω) ∂μ)
        + 1 / (3 * lam ^ 2) * ∫ ω, w ω * Y ω ^ 2 ∂μ := by
  have hpt : ∀ ω, w ω * Y ω
      ≤ 2 * lam / 3 * (w ω * Real.sqrt (Y ω)) + 1 / (3 * lam ^ 2) * (w ω * Y ω ^ 2) := by
    intro ω
    have hsq : Real.sqrt (Y ω) ^ 2 = Y ω := Real.sq_sqrt (hY ω)
    have hyoung := sq_le_young_sq (Real.sqrt_nonneg (Y ω)) hlam
    have hpow : Real.sqrt (Y ω) ^ 4 = Y ω ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    rw [hsq, hpow] at hyoung
    have hmul := mul_le_mul_of_nonneg_left hyoung (hw ω)
    calc w ω * Y ω
        ≤ w ω * (2 * lam / 3 * Real.sqrt (Y ω) + 1 / (3 * lam ^ 2) * Y ω ^ 2) := hmul
      _ = 2 * lam / 3 * (w ω * Real.sqrt (Y ω)) + 1 / (3 * lam ^ 2) * (w ω * Y ω ^ 2) := by ring
  calc (∫ ω, w ω * Y ω ∂μ)
      ≤ ∫ ω, (2 * lam / 3 * (w ω * Real.sqrt (Y ω))
          + 1 / (3 * lam ^ 2) * (w ω * Y ω ^ 2)) ∂μ :=
        integral_mono h0 ((h1.const_mul _).add (h2.const_mul _)) hpt
    _ = 2 * lam / 3 * (∫ ω, w ω * Real.sqrt (Y ω) ∂μ)
          + 1 / (3 * lam ^ 2) * ∫ ω, w ω * Y ω ^ 2 ∂μ := by
        rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul,
          integral_const_mul]

/-- **Reverse Hölder, in the form the decomposition consumes.**  Given `∫ wY ≥ N` and
`∫ wY² ≤ D`, any `λ > 0` that makes the second moment's contribution at most half the first,
`D/(3λ²) ≤ N/2`, leaves `∫ w√Y ≥ 3N/(4λ)`.  The optimal choice `λ = √(2D/(3N))` gives
`∫ w√Y ≥ (3/4)√(3/2)·N^{3/2}/√D`. -/
theorem le_integral_weight_sqrt {w Y : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hY : ∀ ω, 0 ≤ Y ω)
    {lam N D : ℝ} (hlam : 0 < lam)
    (h0 : Integrable (fun ω => w ω * Y ω) μ)
    (h1 : Integrable (fun ω => w ω * Real.sqrt (Y ω)) μ)
    (h2 : Integrable (fun ω => w ω * Y ω ^ 2) μ)
    (hN : N ≤ ∫ ω, w ω * Y ω ∂μ) (hD : (∫ ω, w ω * Y ω ^ 2 ∂μ) ≤ D)
    (hhalf : D / (3 * lam ^ 2) ≤ N / 2) :
    3 * N / (4 * lam) ≤ ∫ ω, w ω * Real.sqrt (Y ω) ∂μ := by
  have hyoung := integral_weight_mul_le_young hw hY hlam h0 h1 h2
  have hDd : 1 / (3 * lam ^ 2) * (∫ ω, w ω * Y ω ^ 2 ∂μ) ≤ D / (3 * lam ^ 2) :=
    calc 1 / (3 * lam ^ 2) * (∫ ω, w ω * Y ω ^ 2 ∂μ)
        ≤ 1 / (3 * lam ^ 2) * D :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = D / (3 * lam ^ 2) := by ring
  have hkey : N / 2 ≤ 2 * lam / 3 * ∫ ω, w ω * Real.sqrt (Y ω) ∂μ := by linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * lam)]
  linarith

end ReverseHolder

/-! ### The line integral dominates the weighted window sum

The first step of the decomposition is deterministic in `ω`.  On `RMF.halfWindow k` the divisor
satisfies `|σ+ih|² = σ² + h² ≤ 2e^{-2k}` as soon as `σ ≤ e^{-k}`, so the damped line integral is
at least `e^{2k}/2` times the undamped window integral — and the windows, being disjoint but for
their endpoints, may all be counted at once.  `RMF.half_setIntegral_Ioo_le_integral_div` is the
single-window case; this is the same estimate with the scales kept apart. -/

section WindowSum

/-- The half-open window `(e^{-(k+1)}, e^{-k}]`: genuinely disjoint across `k`, and differing
from `RMF.halfWindow k` by one point. -/
private abbrev halfWindowIoc (k : ℕ) : Set ℝ :=
  Set.Ioc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ)))

private lemma halfWindowIoc_ae_eq (k : ℕ) : halfWindowIoc k =ᵐ[volume] halfWindow k :=
  Ioc_ae_eq_Icc

private lemma halfWindowIoc_disjoint {i j : ℕ} (hij : i < j) :
    Disjoint (halfWindowIoc i) (halfWindowIoc j) := by
  refine Set.disjoint_left.2 fun t hti htj => ?_
  have hij' : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
  have h3 : Real.exp (-(j : ℝ)) ≤ Real.exp (-((i : ℝ) + 1)) :=
    Real.exp_le_exp.2 (by linarith)
  exact absurd (lt_of_lt_of_le hti.1 (le_trans htj.2 h3)) (lt_irrefl _)

/-- **The line integral dominates the weighted window sum.**  For `0 < σ ≤ e^{-k}` (`k ∈ K`),
`F(t)/(σ+it)` square-integrable, and nonnegative `f ≤ ‖F‖²` integrable on each window,
`∑_{k ∈ K} (e^{2k}/2) ∫_{halfWindow k} f ≤ ∫_ℝ ‖F(t)/(σ+it)‖² dt`.  The slack `f ≤ ‖F‖²` is where
the barrier indicator enters: the windows see only the part of the line the barrier admits. -/
lemma sum_setIntegral_halfWindow_le_integral_div {F : ℝ → ℂ} {f : ℕ → ℝ → ℝ} {σ : ℝ}
    (hσ0 : 0 < σ) {K : Finset ℕ} (hfi : ∀ k ∈ K, IntegrableOn (f k) (halfWindow k))
    (hf0 : ∀ k ∈ K, ∀ t, 0 ≤ f k t) (hfF : ∀ k ∈ K, ∀ t, f k t ≤ ‖F t‖ ^ 2)
    (hint : Integrable fun t : ℝ => ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
    (hK : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ))) :
    ∑ k ∈ K, Real.exp (2 * (k : ℝ)) / 2 * (∫ t in halfWindow k, f k t)
      ≤ ∫ t : ℝ, ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  classical
  have hfi' : ∀ k ∈ K, IntegrableOn (f k) (halfWindowIoc k) :=
    fun k hk => (integrableOn_congr_set_ae (halfWindowIoc_ae_eq k)).2 (hfi k hk)
  have hstep : ∀ k ∈ K, Real.exp (2 * (k : ℝ)) / 2 * (∫ t in halfWindow k, f k t)
      ≤ ∫ t in halfWindowIoc k, ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    intro k hk
    rw [← setIntegral_congr_set (halfWindowIoc_ae_eq k), ← integral_const_mul]
    refine setIntegral_mono_on ((hfi' k hk).const_mul _) hint.integrableOn measurableSet_Ioc
      fun t ht => ?_
    have hσk : σ ≤ Real.exp (-(k : ℝ)) := hK k hk
    have htk : t ≤ Real.exp (-(k : ℝ)) := ht.2
    have ht0 : 0 < t := lt_of_le_of_lt (Real.exp_pos _).le ht.1
    have hz : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = σ ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have hz0 : (0 : ℝ) < σ ^ 2 + t ^ 2 := by positivity
    have hsq : Real.exp (-(k : ℝ)) ^ 2 = Real.exp (-(2 * (k : ℝ))) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hzle : σ ^ 2 + t ^ 2 ≤ 2 * Real.exp (-(2 * (k : ℝ))) := by
      have h1 : σ ^ 2 ≤ Real.exp (-(k : ℝ)) ^ 2 := by nlinarith [hσ0.le, hσk]
      have h2 : t ^ 2 ≤ Real.exp (-(k : ℝ)) ^ 2 := by nlinarith [ht0.le, htk]
      rw [← hsq]
      linarith
    have hexp : Real.exp (2 * (k : ℝ)) * Real.exp (-(2 * (k : ℝ))) = 1 := by
      rw [← Real.exp_add]
      simp
    have hc0 : (0 : ℝ) ≤ Real.exp (2 * (k : ℝ)) / 2 * f k t := by
      have := hf0 k hk t
      positivity
    rw [norm_div, div_pow, hz, le_div_iff₀ hz0]
    calc Real.exp (2 * (k : ℝ)) / 2 * f k t * (σ ^ 2 + t ^ 2)
        ≤ Real.exp (2 * (k : ℝ)) / 2 * f k t * (2 * Real.exp (-(2 * (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left hzle hc0
      _ = f k t := by linear_combination f k t * hexp
      _ ≤ ‖F t‖ ^ 2 := hfF k hk t
  calc ∑ k ∈ K, Real.exp (2 * (k : ℝ)) / 2 * (∫ t in halfWindow k, f k t)
      ≤ ∑ k ∈ K, ∫ t in halfWindowIoc k, ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
        Finset.sum_le_sum hstep
    _ = ∫ t in ⋃ k ∈ K, halfWindowIoc k, ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
        refine (integral_biUnion_finset K (fun i _ => measurableSet_Ioc) ?_
          fun i _ => hint.integrableOn).symm
        intro i _ j _ hij
        rcases lt_or_gt_of_ne hij with h | h
        · exact halfWindowIoc_disjoint h
        · exact (halfWindowIoc_disjoint h).symm
    _ ≤ ∫ t : ℝ, ‖F t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => sq_nonneg _)

end WindowSum

/-! ### Peeling the smallest primes

(C2) and (C3) control the primes above `RMF.scaleCut k₀` only, and the two barriered moments those
above `RMF.scaleCut k`; the ones below `RMF.scaleCut k₀` cost no more than a constant, since on
`Re s ≥ ½` each local factor `1 + X_p p^{-s}` has modulus at least `1 - p^{-1/2} ≥ 1 - 2^{-1/2}`.
The constant is astronomically small — `k₀ ≥ 20`, so the cut is past `e^{e^{20}}` — but it is a
constant, and everything downstream is existential in it. -/

section Peel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **What the primes below a cut cost**: `∏_{p<N}(1 - p^{-1/2})`, a positive constant. -/
noncomputable def halfHeadConst (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))

lemma halfHeadConst_pos (N : ℕ) : 0 < halfHeadConst N := by
  unfold halfHeadConst
  refine Finset.prod_pos fun p hp => ?_
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.one_lt_of_mem_primesBelow hp
  have := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num : (-(1 / 2 : ℝ)) < 0)
  linarith

omit [MeasurableSpace Ω] in
/-- **The primes below a fixed cut cost only a constant.**  The head of
`RMF.le_norm_randomEulerProductIco_sqfree`, with the per-prime bound made uniform in `s` on the
half-plane `Re s ≥ ½`. -/
lemma halfHeadConst_le_norm_randomEulerProduct {X : ℕ → Ω → ℂ} (N : ℕ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) {ω : Ω} (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    halfHeadConst N
      ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N s ω‖ := by
  have hlow := le_norm_randomEulerProductIco_sqfree (X := X) 0 N (s := s)
    (by linarith) (ω := ω) (by rwa [primesIco_zero])
  rw [randomEulerProductIco_zero, primesIco_zero] at hlow
  refine le_trans ?_ hlow
  unfold halfHeadConst
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.one_lt_of_mem_primesBelow hp
    have := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num : (-(1 / 2 : ℝ)) < 0)
    linarith
  · have hp0 : 0 < p := (Nat.prime_of_mem_primesBelow hp).pos
    have h1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
    have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re]
    have hle : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    rw [hnorm]
    linarith

omit [MeasurableSpace Ω] in
/-- **The full product with the decomposition's two cuts put in.**  For `y₀ ≤ y₁ ≤ y` and
`Re s ≥ ½`, `‖F_{<y}(s)‖² ≥ c(y₀)²·‖F_{[y₀,y₁)}(s)‖²·‖F_{[y₁,y)}(s)‖²`. -/
lemma sq_halfHeadConst_mul_normSq_le {X : ℕ → Ω → ℂ} {y₀ y₁ y : ℕ} (h₀ : y₀ ≤ y₁) (h₁ : y₁ ≤ y)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) {ω : Ω} (hω : ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1) :
    halfHeadConst y₀ ^ 2
        * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₁ y s ω‖ ^ 2)
      ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2 := by
  have hsplit : randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y₀ s ω
      * (randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω
        * randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₁ y s ω)
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω := by
    rw [randomEulerProductIco_mul _ h₀ h₁ s ω,
      ← randomEulerProductIco_zero (fun ω => squarefreeExtension fun p => X p ω) y₀ s ω,
      randomEulerProductIco_mul _ (Nat.zero_le _) (h₀.trans h₁) s ω,
      randomEulerProductIco_zero]
  have hhead : halfHeadConst y₀
      ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y₀ s ω‖ := by
    refine halfHeadConst_le_norm_randomEulerProduct y₀ hs fun p hp => hω p ?_
    exact Nat.mem_primesBelow.2 ⟨lt_of_lt_of_le (Nat.lt_of_mem_primesBelow hp) (h₀.trans h₁),
      Nat.prime_of_mem_primesBelow hp⟩
  have hsq : halfHeadConst y₀ ^ 2
      ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y₀ s ω‖ ^ 2 :=
    pow_le_pow_left₀ (halfHeadConst_pos y₀).le hhead 2
  have hnorm : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2
      = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y₀ s ω‖ ^ 2
        * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₁ y s ω‖ ^ 2)
      := by
    rw [← hsplit, norm_mul, norm_mul]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right hsq (by positivity)

end Peel

/-! ### Square roots add along disjoint events

`(∑_k a_k)^{1/2} ≥ ∑_k a_k^{1/2}` is false; restricted to *disjoint* events it is true, and
trivially so — at each point at most one summand survives.  This is what lets the decomposition
sum one Paley–Zygmund estimate per scale without paying a Cauchy–Schwarz: the ladder event
`E(k)` records the *first* scale at which the walk is high, so the `E(k)` are disjoint by
construction. -/

section DisjointSqrt

/-- **Square roots add along disjoint events.**  For pairwise disjoint `E k` and nonnegative
`a k`, `∑_{k ∈ K} 1_{E k}·√(a k) ≤ √(∑_{k ∈ K} a k)` pointwise. -/
lemma sum_indicator_sqrt_le_sqrt_sum {α : Type*} {K : Finset ℕ} {E : ℕ → Set α}
    (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (E i) (E j))
    {a : ℕ → α → ℝ} (ha : ∀ k x, 0 ≤ a k x) (x : α) :
    ∑ k ∈ K, Set.indicator (E k) (fun x => Real.sqrt (a k x)) x
      ≤ Real.sqrt (∑ k ∈ K, a k x) := by
  classical
  by_cases hx : ∃ k ∈ K, x ∈ E k
  · obtain ⟨k₀, hk₀K, hk₀⟩ := hx
    have hsum : ∑ k ∈ K, Set.indicator (E k) (fun x => Real.sqrt (a k x)) x
        = Set.indicator (E k₀) (fun x => Real.sqrt (a k₀ x)) x :=
      Finset.sum_eq_single_of_mem k₀ hk₀K fun b hb hbk =>
        Set.indicator_of_notMem
          (fun hxb => Set.disjoint_left.1 (hdisj b hb k₀ hk₀K hbk) hxb hk₀) _
    rw [hsum, Set.indicator_of_mem hk₀]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun i _ => ha i x) hk₀K)
  · have hz : ∀ k ∈ K, Set.indicator (E k) (fun x => Real.sqrt (a k x)) x = 0 :=
      fun k hk => Set.indicator_of_notMem (fun hxk => hx ⟨k, hk, hxk⟩) _
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    exact Real.sqrt_nonneg _

end DisjointSqrt

/-! ### The swap, with a height-dependent weight

Both moments of the decomposition are expectations of a window integral, and both carry a
small-prime factor that depends on the height as well as on `ω` — the twist `R(h)` — so the
weight cannot be pulled out of the height integral as in
`RMF.integral_mul_setIntegral_indicator_normSq_Ico_eq`, which is the case `ψ ω h = ψ ω` of what
follows.  Integrability is the same argument: the restricted block weight is product-integrable
(`RMF.integrable_uncurry_indicator_normSq_primesIco`), and a bounded jointly measurable factor
does not spoil that. -/

section Swap

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **One swap, with a weight that also depends on the height.**  For `ψ` jointly measurable and
bounded on the product, `E[∫_W ψ(·,h)·1_{L h}‖F_{[z,y)}(σ+ih)‖² dh] = ∫_W E[…] dh`. -/
theorem integral_setIntegral_mul_indicator_normSq_Ico_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω)
    (hSmeas : MeasurableSet {q : Ω × ℝ | q.1 ∈ L q.2}) {W : Set ℝ} (hWfin : volume W ≠ ⊤)
    (ψ : Ω → ℝ → ℝ)
    (hψm : AEStronglyMeasurable (Function.uncurry ψ) (μ.prod (volume.restrict W)))
    {c : ℝ} (hψb : ∀ᵐ q ∂(μ.prod (volume.restrict W)), ‖Function.uncurry ψ q‖ ≤ c) :
    (∫ ω, (∫ h in W, ψ ω h * Set.indicator (L h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω) ∂μ)
      = ∫ h in W, ∫ ω, ψ ω h * Set.indicator (L h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2) ω ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hWfin⟩
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX z y hσ hWfin L hSmeas
  have hInt : Integrable (Function.uncurry fun (ω : Ω) (h : ℝ) => ψ ω h * Set.indicator (L h)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) ω) (μ.prod (volume.restrict W)) :=
    hbase.bdd_mul hψm hψb
  exact integral_integral_swap hInt

end Swap

/-! ### The scale-`k` window mass

What one scale of the decomposition retains of the line integral: the window `[e^{-(k+1)},e^{-k}]`,
the barrier `L(k,h)`, the two prime cuts at `RMF.scaleCut k₀` and `RMF.scaleCut k`, and the weight
`e^{2k}/2` of `RMF.sum_setIntegral_halfWindow_le_integral_div`.  The smallest primes are not here:
they are replaced by `RMF.halfHeadConst`. -/

section WindowMass

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- `RMF.shiftLine` written the way the line integral of `RMF.exists_le_integral_sqrt_lineDiv_half`
writes it. -/
lemma shiftLine_eq_half_add (σ h : ℝ) :
    shiftLine σ h = (1 / 2 : ℂ) + (σ : ℂ) + (h : ℂ) * Complex.I := by
  rw [shiftLine]
  push_cast
  ring

omit [MeasurableSpace Ω] in
/-- **The block product moves continuously along the vertical line**, at a fixed `ω`: it is a
finite product of continuous factors.  The one-variable slice of
`RMF.continuous_primePoly_shiftLine`. -/
lemma continuous_normSq_randomEulerProductIco_shiftLine (z y : ℕ) (σ : ℝ) (ω : Ω) :
    Continuous fun h : ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2 := by
  have hc := continuous_primePoly_shiftLine (S := primesIco z y)
    (fun p hp => (prime_of_mem_primesIco hp).pos) σ
  have h1 : Continuous fun h : ℝ =>
      primePoly (primesIco z y) (shiftLine σ h) (fun p => X (p : ℕ) ω) :=
    hc.comp (continuous_const.prodMk continuous_id)
  have heq : (fun h : ℝ =>
        ‖primePoly (primesIco z y) (shiftLine σ h) (fun p => X (p : ℕ) ω)‖ ^ 2)
      = fun h : ℝ => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2 :=
    funext fun h => by rw [primePoly_primesIco]
  rw [← heq]
  exact h1.norm.pow 2

/-- **The barrier, sliced at a fixed `ω`, is a measurable set of heights**: the slice of
`RMF.measurableSet_prod_halfBarrier`. -/
lemma measurableSet_halfBarrier_slice (hX : IsRademacherPrimeValues X μ) (σ : ℝ)
    (k j₀ t : ℕ) (C₁ a B : ℝ) (ω : Ω) :
    MeasurableSet {h : ℝ | ω ∈ halfBarrier X σ h k j₀ t C₁ a B} :=
  measurable_prodMk_left (measurableSet_prod_halfBarrier hX σ k j₀ t C₁ a B)

/-- **The scale-`k` window mass**:
`(e^{2k}/2)∫_{halfWindow k} 1_{L(k,h)}‖F_{(k₀,k]}(½+σ+ih)‖²‖F_{(k,y)}(½+σ+ih)‖² dh`. -/
noncomputable def halfWindowMass (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ)
    (ω : Ω) : ℝ :=
  Real.exp (2 * (k : ℝ)) / 2 * ∫ h in halfWindow k,
    Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω

/-- The window integrand is integrable in the height, at every `ω`: it is a continuous function
cut down to a measurable set of heights, on a bounded window. -/
lemma integrableOn_halfWindow_barrier (hX : IsRademacherPrimeValues X μ) (σ : ℝ)
    (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ) (ω : Ω) :
    IntegrableOn (fun h => Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) (halfWindow k) := by
  have hcont : Continuous fun h : ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 :=
    (continuous_normSq_randomEulerProductIco_shiftLine _ _ σ ω).mul
      (continuous_normSq_randomEulerProductIco_shiftLine _ _ σ ω)
  have hrw : (fun h : ℝ => Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω)
      = Set.indicator {h : ℝ | ω ∈ halfBarrier X σ h k j₀ t C₁ a B}
        (fun h => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) := by
    funext h
    by_cases hm : ω ∈ halfBarrier X σ h k j₀ t C₁ a B
    · have hm' : h ∈ {h : ℝ | ω ∈ halfBarrier X σ h k j₀ t C₁ a B} := hm
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
    · have hm' : h ∉ {h : ℝ | ω ∈ halfBarrier X σ h k j₀ t C₁ a B} := hm
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm']
  rw [hrw, halfWindow]
  exact (hcont.integrableOn_Icc).indicator
    (measurableSet_halfBarrier_slice hX σ k j₀ t C₁ a B ω)

end WindowMass

/-! ### The pointwise step

The three deterministic facts, put together: the line dominates the weighted window sum
(`RMF.sum_setIntegral_halfWindow_le_integral_div`), the smallest primes cost only a constant
(`RMF.sq_halfHeadConst_mul_normSq_le`), and square roots add along disjoint events
(`RMF.sum_indicator_sqrt_le_sqrt_sum`).  Nothing probabilistic happens here: the only use of the
law is `‖X_p‖ ≤ 1` almost surely, which is what makes the Euler products finite. -/

section Pointwise

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
lemma halfWindowMass_nonneg (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ) (ω : Ω) :
    0 ≤ halfWindowMass X σ k₀ k j₀ t y C₁ a B ω := by
  refine mul_nonneg (by positivity) (integral_nonneg fun h => ?_)
  exact Set.indicator_nonneg (fun _ _ => by positivity) ω

/-- **The pointwise step of the decomposition.**  For pairwise disjoint events `E k` and scales
`k ∈ K` with `σ ≤ e^{-k}` and `scaleCut k₀ ≤ scaleCut k ≤ y`, almost surely
`∑_{k ∈ K} 1_{E k}·c(k₀)·√(mass k) ≤ √(∫_ℝ ‖F_{<y}(½+σ+it)/(σ+it)‖² dt)`, with
`mass k = RMF.halfWindowMass` and `c(k₀) = RMF.halfHeadConst (scaleCut k₀)`.  The events enter
only through their disjointness. -/
theorem ae_sum_indicator_sqrt_halfWindowMass_le (hX : IsRademacherPrimeValues X μ)
    {σ : ℝ} (hσ0 : 0 < σ) {k₀ j₀ t y : ℕ} {C₁ a B : ℝ} {K : Finset ℕ}
    (hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)))
    (hKlo : ∀ k ∈ K, scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hKhi : ∀ k ∈ K, scaleCut (k : ℝ) ≤ y)
    {E : ℕ → Set Ω} (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (E i) (E j)) :
    ∀ᵐ ω ∂μ, ∑ k ∈ K, Set.indicator (E k)
        (fun ω => halfHeadConst (scaleCut (k₀ : ℝ))
          * Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω
      ≤ Real.sqrt (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw 0 y] with ω hω0
  have hω : ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1 := by
    simpa only [primesIco_zero] using hω0
  have hc₀0 : 0 < halfHeadConst (scaleCut (k₀ : ℝ)) := halfHeadConst_pos _
  have hA0 : ∀ (k : ℕ) (ω' : Ω), 0 ≤ halfHeadConst (scaleCut (k₀ : ℝ)) ^ 2
      * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω' :=
    fun k ω' => mul_nonneg (sq_nonneg _) (halfWindowMass_nonneg X σ k₀ k j₀ t y C₁ a B ω')
  have hint : Integrable fun u : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ u) ω
        / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    simp_rw [shiftLine_eq_half_add]
    exact integrable_line_div_sq_half_add hσ0 hω
  -- the barriered window integrand is below the full product
  have hfF : ∀ k ∈ K, ∀ h : ℝ, halfHeadConst (scaleCut (k₀ : ℝ)) ^ 2
        * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω
      ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ h) ω‖ ^ 2 := by
    intro k hk h
    by_cases hmem : ω ∈ halfBarrier X σ h k j₀ t C₁ a B
    · rw [Set.indicator_of_mem hmem]
      exact sq_halfHeadConst_mul_normSq_le (X := X) (hKlo k hk) (hKhi k hk)
        (s := shiftLine σ h) (by rw [re_shiftLine]; linarith) hω
    · rw [Set.indicator_of_notMem hmem, mul_zero]
      positivity
  -- the window sum, against the line
  have hstep2 : ∑ k ∈ K, halfHeadConst (scaleCut (k₀ : ℝ)) ^ 2
        * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω
      ≤ ∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    have hwin := sum_setIntegral_halfWindow_le_integral_div (K := K) (σ := σ) hσ0
      (F := fun u : ℝ => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ u) ω)
      (f := fun k h => halfHeadConst (scaleCut (k₀ : ℝ)) ^ 2
        * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω)
      (fun k _ => (integrableOn_halfWindow_barrier hX σ k₀ k j₀ t y C₁ a B ω).const_mul _)
      (fun k _ h => mul_nonneg (sq_nonneg _)
        (Set.indicator_nonneg (fun _ _ => by positivity) ω))
      hfF hint hKσ
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hwin
    rw [halfWindowMass, integral_const_mul]
    ring
  calc ∑ k ∈ K, Set.indicator (E k)
        (fun ω => halfHeadConst (scaleCut (k₀ : ℝ))
          * Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω
      = ∑ k ∈ K, Set.indicator (E k) (fun ω' => Real.sqrt
          (halfHeadConst (scaleCut (k₀ : ℝ)) ^ 2
            * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω')) ω :=
        Finset.sum_congr rfl fun k _ => congrArg (fun g => Set.indicator (E k) g ω)
          (funext fun ω' => by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc₀0.le])
    _ ≤ Real.sqrt (∑ k ∈ K, halfHeadConst (scaleCut (k₀ : ℝ)) ^ 2
          * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω) :=
        sum_indicator_sqrt_le_sqrt_sum hdisj hA0 ω
    _ ≤ _ := Real.sqrt_le_sqrt hstep2

end Pointwise

/-! ### Independence across the cut, for a low factor that is not a square

`RMF.setIntegral_normSq_split₂` splits `∫_{A∩B}‖F_{[a,c)}(s)‖²` and `RMF.setIntegral_twist_split₂`
splits the twisted weight on both sides; the decomposition needs a *mixed* split — the twist
`RMF.twistPoly` below the cut, the square above it for the numerator and the pair
`RMF.pairPoly` above it for the denominator.  All of them are `RMF.integral_mul_split_Ico` at a
pair of tuple functions, which is what the statement below takes. -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
private lemma indicator_preimage_apply {ι : Type*} (T : Set ι) (g : ι → ℝ) (τ : Ω → ι) (x : Ω) :
    Set.indicator (τ ⁻¹' T) (fun x => g (τ x)) x = Set.indicator T g (τ x) := by
  by_cases hm : τ x ∈ T
  · rw [Set.indicator_of_mem (show x ∈ τ ⁻¹' T from hm), Set.indicator_of_mem hm]
  · rw [Set.indicator_of_notMem (show x ∉ τ ⁻¹' T from hm), Set.indicator_of_notMem hm]

/-- **A low factor and a high factor factorise across the cut**, on events of the two algebras.
`RMF.setIntegral_normSq_split₂` is the case `φ = ψ = RMF.normSqPoly`. -/
theorem setIntegral_mul_split_primeAlgebra (hX : IsRademacherPrimeValues X μ) {a b c : ℕ}
    {A B : Set Ω} (hA : MeasurableSet[primeAlgebra X a b] A)
    (hB : MeasurableSet[primeAlgebra X b c] B)
    {φ : (↥(primesIco a b) → ℂ) → ℝ} {ψ : (↥(primesIco b c) → ℂ) → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫ ω in A ∩ B, (φ fun p => X (p : ℕ) ω) * (ψ fun p => X (p : ℕ) ω) ∂μ)
      = (∫ ω in A, (φ fun p => X (p : ℕ) ω) ∂μ)
        * ∫ ω in B, (ψ fun p => X (p : ℕ) ω) ∂μ := by
  classical
  obtain ⟨T₁, hT₁, rfl⟩ := hA
  obtain ⟨T₂, hT₂, rfl⟩ := hB
  have hmeas₁ : MeasurableSet ((fun (ω : Ω) (p : ↥(primesIco a b)) => X (p : ℕ) ω) ⁻¹' T₁) :=
    (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT₁
  have hmeas₂ : MeasurableSet ((fun (ω : Ω) (p : ↥(primesIco b c)) => X (p : ℕ) ω) ⁻¹' T₂) :=
    (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT₂
  have hsplit := integral_mul_split_Ico hX (hφ.indicator hT₁) (hψ.indicator hT₂)
  rw [← integral_indicator (hmeas₁.inter hmeas₂), ← integral_indicator hmeas₁,
    ← integral_indicator hmeas₂]
  have e1 : ∀ ω : Ω, Set.indicator
        ((fun (ω : Ω) (p : ↥(primesIco a b)) => X (p : ℕ) ω) ⁻¹' T₁
          ∩ (fun (ω : Ω) (p : ↥(primesIco b c)) => X (p : ℕ) ω) ⁻¹' T₂)
        (fun ω => (φ fun p => X (p : ℕ) ω) * (ψ fun p => X (p : ℕ) ω)) ω
      = Set.indicator T₁ φ (fun p => X (p : ℕ) ω)
        * Set.indicator T₂ ψ (fun p => X (p : ℕ) ω) := by
    intro ω
    have h1 := indicator_preimage_apply T₁ φ
      (fun (ω : Ω) (p : ↥(primesIco a b)) => X (p : ℕ) ω) ω
    have h2 := indicator_preimage_apply T₂ ψ
      (fun (ω : Ω) (p : ↥(primesIco b c)) => X (p : ℕ) ω) ω
    rw [Set.inter_indicator_mul, h1, h2]
  have e2 : ∀ ω : Ω, Set.indicator
        ((fun (ω : Ω) (p : ↥(primesIco a b)) => X (p : ℕ) ω) ⁻¹' T₁)
        (fun ω => φ fun p => X (p : ℕ) ω) ω = Set.indicator T₁ φ (fun p => X (p : ℕ) ω) :=
    fun ω => indicator_preimage_apply T₁ φ
      (fun (ω : Ω) (p : ↥(primesIco a b)) => X (p : ℕ) ω) ω
  have e3 : ∀ ω : Ω, Set.indicator
        ((fun (ω : Ω) (p : ↥(primesIco b c)) => X (p : ℕ) ω) ⁻¹' T₂)
        (fun ω => ψ fun p => X (p : ℕ) ω) ω = Set.indicator T₂ ψ (fun p => X (p : ℕ) ω) :=
    fun ω => indicator_preimage_apply T₂ ψ
      (fun (ω : Ω) (p : ↥(primesIco b c)) => X (p : ℕ) ω) ω
  rw [integral_congr_ae (Filter.Eventually.of_forall e1),
    integral_congr_ae (Filter.Eventually.of_forall e2),
    integral_congr_ae (Filter.Eventually.of_forall e3)]
  exact hsplit

/-- `‖F_{[a,b)}(σ+ih₁)‖²‖F_{[a,b)}(σ+ih₂)‖²/‖F_{[a,b)}(σ)‖³`, the low factor of the denominator —
the quantity (C2) bounds above.  The pair analogue of `RMF.twistPoly`. -/
noncomputable def twistPairPoly (S : Finset ℕ) (σ h₁ h₂ : ℝ) (v : ↥S → ℂ) : ℝ :=
  ‖primePoly S (shiftLine σ h₁) v‖ ^ 2 * ‖primePoly S (shiftLine σ h₂) v‖ ^ 2
    / ‖primePoly S (shiftLine σ 0) v‖ ^ 3

lemma measurable_twistPairPoly (S : Finset ℕ) (σ h₁ h₂ : ℝ) :
    Measurable (twistPairPoly S σ h₁ h₂) := by
  unfold twistPairPoly
  exact ((((continuous_primePoly S (shiftLine σ h₁)).norm.pow 2).mul
    ((continuous_primePoly S (shiftLine σ h₂)).norm.pow 2)).measurable).div
      (((continuous_primePoly S (shiftLine σ 0)).norm.pow 3).measurable)

omit [MeasurableSpace Ω] in
lemma twistPairPoly_primesIco (a b : ℕ) (σ h₁ h₂ : ℝ) (ω : Ω) :
    twistPairPoly (primesIco a b) σ h₁ h₂ (fun p => X (p : ℕ) ω)
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h₂) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ^ 3 := by
  rw [twistPairPoly, primePoly_primesIco, primePoly_primesIco, primePoly_primesIco]

end Split

/-! ### Which side of the cut each event lives on

`E_≤(k)` is a statement about the walk from `k₀` up to `k`, so it belongs to the algebra of the
primes in `[scaleCut k₀, scaleCut k)`; `E_>(k)` and the barrier `L(k,h)` are statements about the
walk from `k` on, so they belong to the algebra of `[scaleCut k, y)`.  That is the whole content
of the factorisation: `RMF.setIntegral_mul_split_primeAlgebra` does the rest. -/

section Events

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}

omit [MeasurableSpace Ω] in
/-- **`E_≤(k)` lives below the cut.** -/
lemma measurableSet_primeAlgebra_halfLadder (σ : ℝ) {k₀ k b : ℕ} (hk : k₀ ≤ k)
    (hb : scaleCut (k : ℝ) ≤ b) :
    MeasurableSet[primeAlgebra X (scaleCut (k₀ : ℝ)) b] (halfLadder X σ k₀ k) := by
  have hcast : (k₀ : ℝ) + ((k - k₀ : ℕ) : ℝ) = (k : ℝ) := by
    rw [Nat.cast_sub hk]
    ring
  have hw : ∀ j ≤ k - k₀, Measurable[primeAlgebra X (scaleCut (k₀ : ℝ)) b]
      (walk (halfBlock X (k₀ : ℝ) σ 0) j) := by
    intro j hj
    have h := measurable_primeAlgebra_walk (X := X) (k₀ : ℝ) σ 0 hj
    rw [hcast] at h
    exact h.mono (primeAlgebra_mono le_rfl hb) le_rfl
  have hrw : halfLadder X σ k₀ k
      = ⋂ j ∈ Set.Iio (k - k₀), {ω | walk (halfBlock X (k₀ : ℝ) σ 0) j ω
          < walk (halfBlock X (k₀ : ℝ) σ 0) (k - k₀) ω} := by
    ext ω
    simp only [halfLadder, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Iio]
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j hj => ?_
  exact measurableSet_lt (hw j (le_of_lt hj)) (hw _ le_rfl)

omit [MeasurableSpace Ω] in
/-- **`E_>(k)` lives above the cut**: it is the level event at level `0`. -/
lemma measurableSet_primeAlgebra_halfAfter (σ : ℝ) {k t y : ℕ} (hkt : k ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) :
    MeasurableSet[primeAlgebra X (scaleCut (k : ℝ)) y] (halfAfter X σ k t) := by
  have hcast : (k : ℝ) + ((t - k : ℕ) : ℝ) = (t : ℝ) := by
    rw [Nat.cast_sub hkt]
    ring
  have h := measurableSet_primeAlgebra_level (X := X) (k : ℝ) σ
    (n := t - k) (b := y) (by rw [hcast]; exact hy) 0
  exact h

omit [MeasurableSpace Ω] in
/-- **The barrier lives above the cut.** -/
lemma measurableSet_primeAlgebra_halfBarrier (σ h : ℝ) {k j₀ t y : ℕ} (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (C₁ a B : ℝ) :
    MeasurableSet[primeAlgebra X (scaleCut (k : ℝ)) y] (halfBarrier X σ h k j₀ t C₁ a B) := by
  have hkt : (k : ℝ) + (j₀ : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkj
  have hcast : (k : ℝ) + (j₀ : ℕ) + ((t - k - j₀ : ℕ) : ℝ) = (t : ℝ) := by
    rw [Nat.cast_sub (by omega : j₀ ≤ t - k), Nat.cast_sub (by omega : k ≤ t)]
    ring
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_primeAlgebra_barrierEvent (X := X) (k : ℝ) σ h
      (le_trans (scaleCut_mono (by linarith)) hy) _ _
  · have hm := measurableSet_primeAlgebra_barrierEvent (X := X) ((k : ℝ) + j₀) σ h
      (n := t - k - j₀) (b := y) (by rw [hcast]; exact hy)
      (fun j => -a - B * j) (fun j => a + j + harperHf j)
    exact primeAlgebra_mono (scaleCut_mono (by linarith)) le_rfl _ hm

end Events

/-! ### The two integrands, factorised

At one height the numerator's integrand is `1_{E_≤}·(‖F_{(k₀,k]}(σ+ih)‖²/‖F_{(k₀,k]}(σ)‖)` below
the cut against `1_{E_>∩L(h)}·‖F_{(k,y)}(σ+ih)‖²` above it — exactly the two quantities (C3) and
the first moment bound.  At two heights the denominator's is
`‖F_{(k₀,k]}(σ+ih₁)‖²‖F_{(k₀,k]}(σ+ih₂)‖²/‖F_{(k₀,k]}(σ)‖³` below, which is (C2), against
`1_{L(h₁)∩L(h₂)}‖F_{(k,y)}(σ+ih₁)‖²‖F_{(k,y)}(σ+ih₂)‖²` above, which the second moment bounds once
the heights are integrated out. -/

section Factorise

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The numerator's integrand factorises across the cut.** -/
theorem setIntegral_twist_mul_normSq_split (hX : IsRademacherPrimeValues X μ) {σ h : ℝ}
    {k₀ k j₀ t y : ℕ} (hk : k₀ ≤ k) (hkj : k + j₀ ≤ t) (hy : scaleCut (t : ℝ) ≤ y)
    (C₁ a B : ℝ) :
    (∫ ω in halfLadder X σ k₀ k ∩ (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t),
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
      = (∫ ω in halfLadder X σ k₀ k,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  have hsplit := setIntegral_mul_split_primeAlgebra (X := X) hX
    (A := halfLadder X σ k₀ k) (B := halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
    (measurableSet_primeAlgebra_halfLadder σ hk le_rfl)
    ((measurableSet_primeAlgebra_halfBarrier σ h hkj hy C₁ a B).inter
      (measurableSet_primeAlgebra_halfAfter σ (by omega) hy))
    (measurable_twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h)
    (measurable_normSqPoly (primesIco (scaleCut (k : ℝ)) y) (shiftLine σ h))
  simpa only [twistPoly_primesIco, normSqPoly_primesIco] using hsplit

/-- **The denominator's integrand factorises across the cut.** -/
theorem setIntegral_twistPair_mul_pair_split (hX : IsRademacherPrimeValues X μ) {σ h₁ h₂ : ℝ}
    {k₀ k j₀ t y : ℕ} (hkj : k + j₀ ≤ t) (hy : scaleCut (t : ℝ) ≤ y) (C₁ a B : ℝ) :
    (∫ ω in halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3 ∂μ)
        * ∫ ω in halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
  have hsplit := setIntegral_mul_split_primeAlgebra (X := X) hX
    (A := (Set.univ : Set Ω))
    (B := halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B)
    MeasurableSet.univ
    ((measurableSet_primeAlgebra_halfBarrier σ h₁ hkj hy C₁ a B).inter
      (measurableSet_primeAlgebra_halfBarrier σ h₂ hkj hy C₁ a B))
    (measurable_twistPairPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h₁ h₂)
    (measurable_pairPoly (primesIco (scaleCut (k : ℝ)) y) (shiftLine σ h₁) (shiftLine σ h₂))
  rw [Set.univ_inter, setIntegral_univ] at hsplit
  simpa only [twistPairPoly_primesIco, pairPoly_primesIco] using hsplit

end Factorise

/-! ### The two bounds at one height

With the integrands factorised, (C3) and the first moment multiply into the numerator and (C2)
divides out of the denominator.  Both statements take the two inputs as hypotheses rather than
unfolding the existentials: (C3) is `RMF.le_setIntegral_halfLadder_twist`, the first moment is
`RMF.exists_le_setIntegral_halfBarrier_halfAfter`, (C2) is `RMF.integral_halfTwist_pair_le`, and
the assembly reads them off in the order the constants are fixed. -/

section OneHeight

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The denominator at two heights**: (C2) divides out. -/
theorem setIntegral_twistPair_mul_pair_le (hX : IsRademacherPrimeValues X μ) {σ h₁ h₂ : ℝ}
    {k₀ k j₀ t y : ℕ} {C₁ a B K : ℝ} (hkj : k + j₀ ≤ t) (hy : scaleCut (t : ℝ) ≤ y)
    (hC₂ : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3 ∂μ) ≤ K) :
    (∫ ω in halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ∂μ)
      ≤ K * ∫ ω in halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
  have hhigh0 : (0 : ℝ) ≤ ∫ ω in halfBarrier X σ h₁ k j₀ t C₁ a B ∩
        halfBarrier X σ h₂ k j₀ t C₁ a B,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
    setIntegral_nonneg
      ((measurableSet_of_primeAlgebra hX
          (measurableSet_primeAlgebra_halfBarrier (X := X) σ h₁ hkj hy C₁ a B)).inter
        (measurableSet_of_primeAlgebra hX
          (measurableSet_primeAlgebra_halfBarrier (X := X) σ h₂ hkj hy C₁ a B)))
      fun ω _ => by positivity
  rw [setIntegral_twistPair_mul_pair_split hX hkj hy C₁ a B]
  exact mul_le_mul_of_nonneg_right hC₂ hhigh0

end OneHeight

/-! ### The small-prime weights, jointly in `(ω, h)`

Both height integrals swap through `RMF.integral_setIntegral_mul_indicator_normSq_Ico_eq`, whose
weight must be jointly measurable and bounded on the product.  The weights are the small-prime
factors `RMF.twistPoly` and `RMF.twistPairPoly`; joint measurability is
`RMF.measurable_uncurry_primePoly`, and the bound is the envelope
`RMF.ae_forall_norm_randomEulerProductIco_mem_Icc`, which does not move along the line.  Both
bounds grow with `k`, and that is harmless: they are used only for integrability. -/

section JointWeights

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The upper envelope of the block product on `Re s = ½ + σ`. -/
noncomputable def blockEnvUp (a b : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ primesIco a b, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))

/-- The lower envelope of the block product on `Re s = ½ + σ`, positive for `σ ≥ 0`. -/
noncomputable def blockEnvDown (a b : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ primesIco a b, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))

lemma blockEnvDown_pos (a b : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) : 0 < blockEnvDown a b σ :=
  prod_one_sub_prime_rpow_primesIco_pos (by linarith)

/-- The block product's two-sided envelope, in the two abbreviations. -/
lemma ae_forall_norm_randomEulerProductIco_env (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂μ, ∀ h : ℝ,
      blockEnvDown a b σ
          ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖
        ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ≤ blockEnvUp a b σ := by
  filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc hX a b (c := 1 / 2 + σ)
    (by linarith)] with ω hω h
  exact hω (shiftLine σ h) (re_shiftLine σ h)

/-- **The twist, jointly measurable in `(ω, h)`.** -/
lemma measurable_uncurry_twistPoly (hX : IsRademacherPrimeValues X μ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (σ : ℝ) :
    Measurable fun w : Ω × ℝ => twistPoly S σ w.2 (fun p => X (p : ℕ) w.1) := by
  unfold twistPoly
  refine Measurable.div (((measurable_uncurry_primePoly hX S hS σ).norm).pow_const 2) ?_
  exact (((continuous_primePoly S (shiftLine σ 0)).measurable).comp
    ((measurable_primeTuple hX S hS).comp measurable_fst)).norm

/-- **The twist is bounded, uniformly in the height.** -/
lemma ae_forall_twistPoly_le (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂μ, ∀ h : ℝ, ‖twistPoly (primesIco a b) σ h (fun p => X (p : ℕ) ω)‖
      ≤ blockEnvUp a b σ ^ 2 / blockEnvDown a b σ := by
  filter_upwards [ae_forall_norm_randomEulerProductIco_env hX a b hσ] with ω hω h
  have hd := (hω 0).1
  have hu := (hω h).2
  have hd0 : 0 < blockEnvDown a b σ := blockEnvDown_pos a b hσ
  rw [twistPoly_primesIco, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hu 2) hd0 hd

end JointWeights

/-! ### The numerator's height integral

Fubini once, then the factorisation at each height.  The weight carried through the swap is the
twist cut down to `E_≤(k)`: bounded because the small-prime product is, jointly measurable
because `RMF.measurable_uncurry_primePoly` is.  Both facts are extracted, because the swap needs
them and so does the integrability of what comes out of it. -/

section Numerator

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
lemma volume_halfWindow_ne_top (k : ℕ) : volume (halfWindow k) ≠ ⊤ := by
  rw [halfWindow]
  exact measure_Icc_lt_top.ne

omit [MeasurableSpace Ω] in
lemma volume_real_halfWindow (k : ℕ) :
    volume.real (halfWindow k) = Real.exp (-(k : ℝ)) - Real.exp (-((k : ℝ) + 1)) := by
  have hle : Real.exp (-((k : ℝ) + 1)) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.2 (by linarith)
  rw [halfWindow, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- The barrier intersected with `E_>(k)` is jointly measurable in `(ω, h)`. -/
lemma measurableSet_prod_halfBarrier_inter_halfAfter (hX : IsRademacherPrimeValues X μ) (σ : ℝ)
    (k j₀ t y : ℕ) (hkt : k ≤ t) (hy : scaleCut (t : ℝ) ≤ y) (C₁ a B : ℝ) :
    MeasurableSet {q : Ω × ℝ |
      q.1 ∈ halfBarrier X σ q.2 k j₀ t C₁ a B ∩ halfAfter X σ k t} :=
  (measurableSet_prod_halfBarrier hX σ k j₀ t C₁ a B).inter
    ((measurableSet_of_primeAlgebra hX
      (measurableSet_primeAlgebra_halfAfter (X := X) (y := y) σ hkt hy)).preimage measurable_fst)

omit [MeasurableSpace Ω] in
/-- The twist, cut down to an event, uncurried. -/
lemma uncurry_indicator_twistPoly_eq (A : Set Ω) (S : Finset ℕ) (σ : ℝ) :
    (Function.uncurry fun (ω : Ω) (h : ℝ) =>
        Set.indicator A (fun ω => twistPoly S σ h (fun p => X (p : ℕ) ω)) ω)
      = Set.indicator (Prod.fst ⁻¹' A)
        (fun w : Ω × ℝ => twistPoly S σ w.2 (fun p => X (p : ℕ) w.1)) := by
  funext w
  rw [Function.uncurry_apply_pair]
  by_cases hm : w.1 ∈ A
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show w ∈ Prod.fst ⁻¹' A from hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show w ∉ Prod.fst ⁻¹' A from hm)]

/-- The swap's weight is jointly measurable. -/
lemma aestronglyMeasurable_uncurry_indicator_twistPoly (hX : IsRademacherPrimeValues X μ)
    {A : Set Ω} (hAm : MeasurableSet A) (S : Finset ℕ) (hSp : ∀ p ∈ S, Nat.Prime p) (σ : ℝ)
    (W : Set ℝ) :
    AEStronglyMeasurable (Function.uncurry fun (ω : Ω) (h : ℝ) =>
        Set.indicator A (fun ω => twistPoly S σ h (fun p => X (p : ℕ) ω)) ω)
      (μ.prod (volume.restrict W)) := by
  rw [uncurry_indicator_twistPoly_eq]
  exact ((measurable_uncurry_twistPoly hX S hSp σ).indicator
    (hAm.preimage measurable_fst)).aestronglyMeasurable

/-- The swap's weight is bounded on the product. -/
lemma ae_bound_uncurry_indicator_twistPoly (hX : IsRademacherPrimeValues X μ) (A : Set Ω)
    (a b : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (W : Set ℝ) :
    ∀ᵐ q ∂(μ.prod (volume.restrict W)),
      ‖Function.uncurry (fun (ω : Ω) (h : ℝ) =>
          Set.indicator A (fun ω => twistPoly (primesIco a b) σ h (fun p => X (p : ℕ) ω)) ω) q‖
        ≤ blockEnvUp a b σ ^ 2 / blockEnvDown a b σ := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually
    (ae_forall_twistPoly_le hX a b hσ)] with q hq
  rw [uncurry_indicator_twistPoly_eq]
  by_cases hm : q ∈ Prod.fst ⁻¹' A
  · rw [Set.indicator_of_mem hm]
    exact hq q.2
  · rw [Set.indicator_of_notMem hm, norm_zero]
    exact le_trans (norm_nonneg _) (hq 0)

/-- **At one height, the numerator's integrand is (C3)'s times the first moment's.** -/
theorem integral_indicator_twist_mul_indicator_normSq_eq (hX : IsRademacherPrimeValues X μ)
    {σ h : ℝ} {k₀ k j₀ t y : ℕ} (hk : k₀ ≤ k) (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (C₁ a B : ℝ) :
    (∫ ω, Set.indicator (halfLadder X σ k₀ k)
          (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
            (fun p => X (p : ℕ) ω)) ω
        * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω ∂μ)
      = (∫ ω in halfLadder X σ k₀ k,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  have hAm : MeasurableSet (halfLadder X σ k₀ k) :=
    measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)
  have hBm : MeasurableSet (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t) :=
    (measurableSet_of_primeAlgebra hX
        (measurableSet_primeAlgebra_halfBarrier (X := X) (y := y) σ h hkj hy C₁ a B)).inter
      (measurableSet_of_primeAlgebra hX
        (measurableSet_primeAlgebra_halfAfter (X := X) (y := y) σ (by omega) hy))
  have hcomb : ∀ ω : Ω, Set.indicator (halfLadder X σ k₀ k)
          (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
            (fun p => X (p : ℕ) ω)) ω
        * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω
      = Set.indicator (halfLadder X σ k₀ k ∩
            (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t))
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω := by
    intro ω
    have hfac : Set.indicator (halfLadder X σ k₀ k)
          (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
            (fun p => X (p : ℕ) ω)) ω
        = Set.indicator (halfLadder X σ k₀ k)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖) ω := by
      by_cases hm : ω ∈ halfLadder X σ k₀ k
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, twistPoly_primesIco]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
    rw [Set.inter_indicator_mul, hfac]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcomb),
    integral_indicator (hAm.inter hBm),
    setIntegral_twist_mul_normSq_split hX hk hkj hy C₁ a B]

/-- **The numerator's height integral.** -/
theorem integral_setIntegral_twist_normSq_eq (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk : k₀ ≤ k) (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (C₁ a B : ℝ) :
    (∫ ω, (∫ h in halfWindow k,
        Set.indicator (halfLadder X σ k₀ k)
            (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
              (fun p => X (p : ℕ) ω)) ω
          * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ∂μ)
      = ∫ h in halfWindow k,
          (∫ ω in halfLadder X σ k₀ k,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
                / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
            * ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  have hAm : MeasurableSet (halfLadder X σ k₀ k) :=
    measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)
  rw [integral_setIntegral_mul_indicator_normSq_Ico_eq hX (scaleCut (k : ℝ)) y hσ
    (fun h => halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
    (measurableSet_prod_halfBarrier_inter_halfAfter hX σ k j₀ t y (by omega) hy C₁ a B)
    (volume_halfWindow_ne_top k) _
    (aestronglyMeasurable_uncurry_indicator_twistPoly hX hAm _
      (fun p hp => prime_of_mem_primesIco hp) σ (halfWindow k))
    (ae_bound_uncurry_indicator_twistPoly hX (halfLadder X σ k₀ k) (scaleCut (k₀ : ℝ))
      (scaleCut (k : ℝ)) hσ (halfWindow k))]
  exact setIntegral_congr_fun measurableSet_Icc fun h _ =>
    integral_indicator_twist_mul_indicator_normSq_eq hX hk hkj hy C₁ a B

/-- **The numerator's height integrand is integrable.** -/
theorem integrableOn_setIntegral_twist_normSq (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk : k₀ ≤ k) (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (C₁ a B : ℝ) :
    IntegrableOn (fun h : ℝ =>
        (∫ ω in halfLadder X σ k₀ k,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
          * ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ) (halfWindow k) := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict (halfWindow k)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_ne le_top (volume_halfWindow_ne_top k)⟩
  have hAm : MeasurableSet (halfLadder X σ k₀ k) :=
    measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX (scaleCut (k : ℝ)) y hσ
    (volume_halfWindow_ne_top k)
    (fun h => halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
    (measurableSet_prod_halfBarrier_inter_halfAfter hX σ k j₀ t y (by omega) hy C₁ a B)
  have hInt := hbase.bdd_mul
    (aestronglyMeasurable_uncurry_indicator_twistPoly hX hAm
      (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)))
      (fun p hp => prime_of_mem_primesIco hp) σ (halfWindow k))
    (ae_bound_uncurry_indicator_twistPoly hX (halfLadder X σ k₀ k) (scaleCut (k₀ : ℝ))
      (scaleCut (k : ℝ)) hσ (halfWindow k))
  have hrw := hInt.integral_prod_right
  refine hrw.congr (Filter.Eventually.of_forall fun h => ?_)
  exact integral_indicator_twist_mul_indicator_normSq_eq hX hk hkj hy C₁ a B

/-- **The numerator, bounded below.**  (C3) and the first moment hold uniformly on the window, so
the window integral of their product is at least `|halfWindow k|·c₃·c₄`. -/
theorem le_integral_setIntegral_twist_normSq (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk : k₀ ≤ k) (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) {C₁ a B c₃ c₄ : ℝ} (hc₄ : 0 ≤ c₄)
    (h₃ : ∀ h ∈ halfWindow k, c₃ ≤ ∫ ω in halfLadder X σ k₀ k,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
    (h₄ : ∀ h ∈ halfWindow k, c₄ ≤ ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ) :
    c₃ * c₄ * (Real.exp (-(k : ℝ)) - Real.exp (-((k : ℝ) + 1)))
      ≤ ∫ ω, (∫ h in halfWindow k,
          Set.indicator (halfLadder X σ k₀ k)
              (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
                (fun p => X (p : ℕ) ω)) ω
            * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
                (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ∂μ := by
  have hAm : MeasurableSet (halfLadder X σ k₀ k) :=
    measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)
  have hpt : ∀ h ∈ halfWindow k, c₃ * c₄
      ≤ (∫ ω in halfLadder X σ k₀ k,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
    intro h hh
    exact mul_le_mul (h₃ h hh) (h₄ h hh) hc₄
      (setIntegral_nonneg hAm fun ω _ => by positivity)
  rw [integral_setIntegral_twist_normSq_eq hX hσ hk hkj hy C₁ a B, ← volume_real_halfWindow k]
  exact setIntegral_ge_of_const_le_real measurableSet_Icc (volume_halfWindow_ne_top k) hpt
    (integrableOn_setIntegral_twist_normSq hX hσ hk hkj hy C₁ a B)

end Numerator

/-! ### The denominator's height integral

`‖F_{(k₀,k]}(s)‖²‖F_{(k,y)}(s)‖² = ‖F_{(k₀,y)}(s)‖²`, so the window mass is the barriered window
integral of a *single* block, and the denominator's weight `‖F_{(k₀,k]}(σ)‖^{-3}` does not move
with the height.  Both swaps are then
`RMF.integral_mul_setIntegral_indicator_normSq_Ico_eq`, in the two-step pattern of
`RMF.integral_sq_setIntegral_indicator_normSq_Ico_eq`, which is that lemma with a weight. -/

section Denominator

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- **The window mass, as a single block.** -/
lemma halfWindowMass_eq_single {σ : ℝ} {k₀ k j₀ t y : ℕ}
    (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ)) (hhi : scaleCut (k : ℝ) ≤ y) (C₁ a B : ℝ)
    (ω : Ω) :
    halfWindowMass X σ k₀ k j₀ t y C₁ a B ω
      = Real.exp (2 * (k : ℝ)) / 2 * ∫ h in halfWindow k,
          Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω := by
  rw [halfWindowMass]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun h _ => ?_
  by_cases hm : ω ∈ halfBarrier X σ h k j₀ t C₁ a B
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm,
      normSq_randomEulerProductIco_split hlo hhi]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]

/-- **The weighted double swap.**  `RMF.integral_sq_setIntegral_indicator_normSq_Ico_eq` with a
bounded weight carried through both steps — which is what the denominator needs, its weight
being `‖F_{(k₀,k]}(σ)‖^{-3}`. -/
theorem integral_mul_sq_setIntegral_indicator_normSq_Ico_eq (hX : IsRademacherPrimeValues X μ)
    (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω) (hLmeas : ∀ h, MeasurableSet (L h))
    (hSmeas : MeasurableSet {q : Ω × ℝ | q.1 ∈ L q.2}) {W : Set ℝ} (hWfin : volume W ≠ ⊤)
    (ψ : Ω → ℝ) (hψm : AEStronglyMeasurable ψ μ) {c : ℝ} (hψb : ∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ c) :
    (∫ ω, ψ ω * (∫ h in W, Set.indicator (L h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
      = ∫ h₁ in W, ∫ h₂ in W, ∫ ω, ψ ω
          * Set.indicator (L h₁)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (L h₂)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set g : ℝ → Ω → ℝ := fun h ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
      (shiftLine σ h) ω‖ ^ 2 with hgdef
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX z y hσ hWfin L hSmeas
  have hbnd := ae_forall_norm_indicator_normSq_Ico_le hX z y hσ L
  have hc0 : (0 : ℝ) ≤ c := by
    obtain ⟨ω, hω⟩ := hψb.exists
    exact le_trans (norm_nonneg _) hω
  have hIm : AEStronglyMeasurable (fun ω => ∫ h in W, Set.indicator (L h) (g h) ω) μ :=
    hbase.integral_prod_left.aestronglyMeasurable
  have hIb : ∀ᵐ ω ∂μ, ‖∫ h in W, Set.indicator (L h) (g h) ω‖
      ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real W := by
    filter_upwards [hbnd] with ω hω
    exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hWfin) fun h _ => hω h
  have hOb : ∀ᵐ ω ∂μ, ‖ψ ω * ∫ h in W, Set.indicator (L h) (g h) ω‖
      ≤ c * ((∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real W) := by
    filter_upwards [hψb, hIb] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hc0
  have hexp : (∫ ω, ψ ω * (∫ h in W, Set.indicator (L h) (g h) ω) ^ 2 ∂μ)
      = ∫ ω, (ψ ω * ∫ h in W, Set.indicator (L h) (g h) ω)
          * (∫ h in W, Set.indicator (L h) (g h) ω) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [hexp, integral_mul_setIntegral_indicator_normSq_Ico_eq hX z y hσ L hSmeas hWfin
    (fun ω => ψ ω * ∫ h in W, Set.indicator (L h) (g h) ω) (hψm.mul hIm) hOb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₁ => ?_)
  have hφm : AEStronglyMeasurable (fun ω => ψ ω * Set.indicator (L h₁) (g h₁) ω) μ :=
    hψm.mul ((hf'.integrable_norm_randomEulerProductIco_sq z y (shiftLine σ h₁)).indicator
      (hLmeas h₁)).aestronglyMeasurable
  have hφb : ∀ᵐ ω ∂μ, ‖ψ ω * Set.indicator (L h₁) (g h₁) ω‖
      ≤ c * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    filter_upwards [hψb, hbnd] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 (h2 h₁) (norm_nonneg _) hc0
  calc (∫ ω, (ψ ω * ∫ h₂ in W, Set.indicator (L h₂) (g h₂) ω)
          * Set.indicator (L h₁) (g h₁) ω ∂μ)
      = ∫ ω, (ψ ω * Set.indicator (L h₁) (g h₁) ω)
          * (∫ h₂ in W, Set.indicator (L h₂) (g h₂) ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    _ = ∫ h₂ in W, ∫ ω, (ψ ω * Set.indicator (L h₁) (g h₁) ω)
          * Set.indicator (L h₂) (g h₂) ω ∂μ :=
        integral_mul_setIntegral_indicator_normSq_Ico_eq hX z y hσ L hSmeas hWfin
          (fun ω => ψ ω * Set.indicator (L h₁) (g h₁) ω) hφm hφb

/-- **The `h`-integrand of a swap is integrable.**  The same product-integrable uncurried
integrand as `RMF.integral_mul_setIntegral_indicator_normSq_Ico_eq`, read the other way.  All
four integrability facts the denominator's comparison needs are instances of this. -/
theorem integrableOn_integral_mul_indicator_normSq (hX : IsRademacherPrimeValues X μ) (z y : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω) (hSmeas : MeasurableSet {q : Ω × ℝ | q.1 ∈ L q.2})
    {W : Set ℝ} (hWfin : volume W ≠ ⊤) (ψ : Ω → ℝ) (hψm : AEStronglyMeasurable ψ μ)
    {c : ℝ} (hψb : ∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ c) :
    IntegrableOn (fun h : ℝ => ∫ ω, ψ ω * Set.indicator (L h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω ∂μ) W := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  haveI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hWfin⟩
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX z y hσ hWfin L hSmeas
  have hψprod : AEStronglyMeasurable (fun q : Ω × ℝ => ψ q.1) (μ.prod (volume.restrict W)) :=
    hψm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hψbprod : ∀ᵐ q ∂(μ.prod (volume.restrict W)), ‖ψ q.1‖ ≤ c :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hψb
  exact (hbase.bdd_mul hψprod hψbprod).integral_prod_right

/-- **The denominator's comparison.**  If at every pair of heights the weighted moment of the
block `[z, y)` is at most `K` times the unweighted moment of the block `[z', y')`, the same holds
once both heights are integrated out. -/
theorem integral_mul_sq_setIntegral_le (hX : IsRademacherPrimeValues X μ) (z y z' y' : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) (L : ℝ → Set Ω) (hLmeas : ∀ h, MeasurableSet (L h))
    (hSmeas : MeasurableSet {q : Ω × ℝ | q.1 ∈ L q.2}) {W : Set ℝ} (hWmeas : MeasurableSet W)
    (hWfin : volume W ≠ ⊤) (ψ : Ω → ℝ) (hψm : AEStronglyMeasurable ψ μ)
    {c : ℝ} (hψb : ∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ c) {K : ℝ}
    (hcomp : ∀ h₁ ∈ W, ∀ h₂ ∈ W, (∫ ω, ψ ω
          * Set.indicator (L h₁)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (L h₂)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
                (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
        ≤ K * ∫ ω, Set.indicator (L h₁)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                z' y' (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (L h₂)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                z' y' (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ) :
    (∫ ω, ψ ω * (∫ h in W, Set.indicator (L h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
      ≤ K * ∫ ω, (∫ h in W, Set.indicator (L h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z' y'
            (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  set g : ℝ → Ω → ℝ := fun h ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
      (shiftLine σ h) ω‖ ^ 2 with hgdef
  set g' : ℝ → Ω → ℝ := fun h ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z' y'
      (shiftLine σ h) ω‖ ^ 2 with hg'def
  have hf' : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX z y hσ hWfin L hSmeas
  have hbase' := integrable_uncurry_indicator_normSq_primesIco hX z' y' hσ hWfin L hSmeas
  have hbnd := ae_forall_norm_indicator_normSq_Ico_le hX z y hσ L
  have hbnd' := ae_forall_norm_indicator_normSq_Ico_le hX z' y' hσ L
  have hc0 : (0 : ℝ) ≤ c := by
    obtain ⟨ω, hω⟩ := hψb.exists
    exact le_trans (norm_nonneg _) hω
  -- the weights at one height, and the two window integrals
  have hφm : ∀ h₁ : ℝ, AEStronglyMeasurable
      (fun ω => ψ ω * Set.indicator (L h₁) (g h₁) ω) μ := fun h₁ =>
    hψm.mul ((hf'.integrable_norm_randomEulerProductIco_sq z y
      (shiftLine σ h₁)).indicator (hLmeas h₁)).aestronglyMeasurable
  have hφb : ∀ h₁ : ℝ, ∀ᵐ ω ∂μ, ‖ψ ω * Set.indicator (L h₁) (g h₁) ω‖
      ≤ c * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    intro h₁
    filter_upwards [hψb, hbnd] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 (h2 h₁) (norm_nonneg _) hc0
  have hφm' : ∀ h₁ : ℝ, AEStronglyMeasurable (fun ω => Set.indicator (L h₁) (g' h₁) ω) μ :=
    fun h₁ => ((hf'.integrable_norm_randomEulerProductIco_sq z' y'
      (shiftLine σ h₁)).indicator (hLmeas h₁)).aestronglyMeasurable
  have hφb' : ∀ h₁ : ℝ, ∀ᵐ ω ∂μ, ‖Set.indicator (L h₁) (g' h₁) ω‖
      ≤ (∏ p ∈ primesIco z' y', (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    intro h₁
    filter_upwards [hbnd'] with ω h2
    exact h2 h₁
  have hIm : AEStronglyMeasurable (fun ω => ∫ h in W, Set.indicator (L h) (g h) ω) μ :=
    hbase.integral_prod_left.aestronglyMeasurable
  have hIm' : AEStronglyMeasurable (fun ω => ∫ h in W, Set.indicator (L h) (g' h) ω) μ :=
    hbase'.integral_prod_left.aestronglyMeasurable
  have hIb : ∀ᵐ ω ∂μ, ‖∫ h in W, Set.indicator (L h) (g h) ω‖
      ≤ (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real W := by
    filter_upwards [hbnd] with ω hω
    exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hWfin) fun h _ => hω h
  have hIb' : ∀ᵐ ω ∂μ, ‖∫ h in W, Set.indicator (L h) (g' h) ω‖
      ≤ (∏ p ∈ primesIco z' y', (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real W := by
    filter_upwards [hbnd'] with ω hω
    exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hWfin) fun h _ => hω h
  have hOb : ∀ᵐ ω ∂μ, ‖ψ ω * ∫ h in W, Set.indicator (L h) (g h) ω‖
      ≤ c * ((∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real W) := by
    filter_upwards [hψb, hIb] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hc0
  -- the inner swap, in the form the outer integrability needs
  have heqA : ∀ h₁ : ℝ, (∫ ω, (ψ ω * ∫ h in W, Set.indicator (L h) (g h) ω)
        * Set.indicator (L h₁) (g h₁) ω ∂μ)
      = ∫ h₂ in W, ∫ ω, ψ ω * Set.indicator (L h₁) (g h₁) ω
          * Set.indicator (L h₂) (g h₂) ω ∂μ := by
    intro h₁
    calc (∫ ω, (ψ ω * ∫ h in W, Set.indicator (L h) (g h) ω)
          * Set.indicator (L h₁) (g h₁) ω ∂μ)
        = ∫ ω, (ψ ω * Set.indicator (L h₁) (g h₁) ω)
            * (∫ h in W, Set.indicator (L h) (g h) ω) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      _ = ∫ h₂ in W, ∫ ω, (ψ ω * Set.indicator (L h₁) (g h₁) ω)
            * Set.indicator (L h₂) (g h₂) ω ∂μ :=
          integral_mul_setIntegral_indicator_normSq_Ico_eq hX z y hσ L hSmeas hWfin
            (fun ω => ψ ω * Set.indicator (L h₁) (g h₁) ω) (hφm h₁) (hφb h₁)
  have heqB : ∀ h₁ : ℝ, (∫ ω, (∫ h in W, Set.indicator (L h) (g' h) ω)
        * Set.indicator (L h₁) (g' h₁) ω ∂μ)
      = ∫ h₂ in W, ∫ ω, Set.indicator (L h₁) (g' h₁) ω
          * Set.indicator (L h₂) (g' h₂) ω ∂μ := by
    intro h₁
    calc (∫ ω, (∫ h in W, Set.indicator (L h) (g' h) ω)
          * Set.indicator (L h₁) (g' h₁) ω ∂μ)
        = ∫ ω, Set.indicator (L h₁) (g' h₁) ω
            * (∫ h in W, Set.indicator (L h) (g' h) ω) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      _ = ∫ h₂ in W, ∫ ω, Set.indicator (L h₁) (g' h₁) ω
            * Set.indicator (L h₂) (g' h₂) ω ∂μ :=
          integral_mul_setIntegral_indicator_normSq_Ico_eq hX z' y' hσ L hSmeas hWfin
            (fun ω => Set.indicator (L h₁) (g' h₁) ω) (hφm' h₁) (hφb' h₁)
  -- the four integrability facts
  have hIntA : IntegrableOn (fun h₁ : ℝ => ∫ h₂ in W, ∫ ω, ψ ω
      * Set.indicator (L h₁) (g h₁) ω * Set.indicator (L h₂) (g h₂) ω ∂μ) W :=
    (integrableOn_integral_mul_indicator_normSq hX z y hσ L hSmeas hWfin _
      (hψm.mul hIm) hOb).congr (Filter.Eventually.of_forall heqA)
  have hIntB : IntegrableOn (fun h₁ : ℝ => ∫ h₂ in W, ∫ ω,
      Set.indicator (L h₁) (g' h₁) ω * Set.indicator (L h₂) (g' h₂) ω ∂μ) W :=
    (integrableOn_integral_mul_indicator_normSq hX z' y' hσ L hSmeas hWfin _
      hIm' hIb').congr (Filter.Eventually.of_forall heqB)
  have hIntA' : ∀ h₁ : ℝ, IntegrableOn (fun h₂ : ℝ =>
      ∫ ω, ψ ω * Set.indicator (L h₁) (g h₁) ω * Set.indicator (L h₂) (g h₂) ω ∂μ) W :=
    fun h₁ => integrableOn_integral_mul_indicator_normSq hX z y hσ L hSmeas hWfin _
      (hφm h₁) (hφb h₁)
  have hIntB' : ∀ h₁ : ℝ, IntegrableOn (fun h₂ : ℝ =>
      ∫ ω, Set.indicator (L h₁) (g' h₁) ω * Set.indicator (L h₂) (g' h₂) ω ∂μ) W :=
    fun h₁ => integrableOn_integral_mul_indicator_normSq hX z' y' hσ L hSmeas hWfin _
      (hφm' h₁) (hφb' h₁)
  rw [integral_mul_sq_setIntegral_indicator_normSq_Ico_eq hX z y hσ L hLmeas hSmeas hWfin ψ
      hψm hψb,
    integral_sq_setIntegral_indicator_normSq_Ico_eq hX z' y' hσ L hLmeas hSmeas hWfin,
    ← integral_const_mul]
  refine setIntegral_mono_on hIntA ((hIntB.const_mul K)) hWmeas fun h₁ hh₁ => ?_
  rw [← integral_const_mul]
  exact setIntegral_mono_on (hIntA' h₁) ((hIntB' h₁).const_mul K) hWmeas
    fun h₂ hh₂ => hcomp h₁ hh₁ h₂ hh₂

omit [MeasurableSpace Ω] in
/-- A weight against two indicators is the indicator of the intersection. -/
private lemma mul_two_indicators (ψ f₁ f₂ : Ω → ℝ) (S₁ S₂ : Set Ω) (ω : Ω) :
    ψ ω * Set.indicator S₁ f₁ ω * Set.indicator S₂ f₂ ω
      = Set.indicator (S₁ ∩ S₂) (fun ω => ψ ω * f₁ ω * f₂ ω) ω := by
  by_cases h1 : ω ∈ S₁
  · by_cases h2 : ω ∈ S₂
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
        Set.indicator_of_mem (Set.mem_inter h1 h2)]
    · have hni : ω ∉ S₁ ∩ S₂ := fun hc => h2 (Set.mem_of_mem_inter_right hc)
      rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem hni, mul_zero]
  · have hni : ω ∉ S₁ ∩ S₂ := fun hc => h1 (Set.mem_of_mem_inter_left hc)
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hni, mul_zero, zero_mul]

/-- **(C2) at one pair of heights**, in the form the comparison takes: the weight
`‖F_{(k₀,k]}(σ)‖^{-3}` against the two blocks `[scaleCut k₀, y)` costs a factor `e^{132}` over
the two blocks `[scaleCut k, y)`. -/
theorem integral_invCube_mul_pair_le (hX : IsRademacherPrimeValues X μ) {σ h₁ h₂ : ℝ}
    {k₀ k j₀ t y : ℕ} (hk₀ : 1 ≤ k₀) (hk : k₀ ≤ k) (hσ : 0 ≤ σ) (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (hh₁0 : 0 ≤ h₁) (hh₁ : h₁ ≤ Real.exp (-(k : ℝ)))
    (hh₂0 : 0 ≤ h₂) (hh₂ : h₂ ≤ Real.exp (-(k : ℝ))) (C₁ a B : ℝ) :
    (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
        * Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
      ≤ Real.exp 132 * ∫ ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ := by
  have hm₁ : MeasurableSet (halfBarrier X σ h₁ k j₀ t C₁ a B) :=
    measurableSet_of_primeAlgebra hX
      (measurableSet_primeAlgebra_halfBarrier (X := X) (y := y) σ h₁ hkj hy C₁ a B)
  have hm₂ : MeasurableSet (halfBarrier X σ h₂ k j₀ t C₁ a B) :=
    measurableSet_of_primeAlgebra hX
      (measurableSet_primeAlgebra_halfBarrier (X := X) (y := y) σ h₂ hkj hy C₁ a B)
  -- both sides as set integrals over the pair barrier
  have hleft : ∀ ω : Ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
        * Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω
      = Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
                / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3
              * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2)) ω := by
    intro ω
    refine (mul_two_indicators (fun ω => (‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
        (shiftLine σ 0) ω‖ ^ 3)⁻¹) _ _ _ _ ω).trans ?_
    refine congrArg (fun f => Set.indicator _ f ω) (funext fun ω' => ?_)
    rw [normSq_randomEulerProductIco_split hlo hhi (shiftLine σ h₁) ω',
      normSq_randomEulerProductIco_split hlo hhi (shiftLine σ h₂) ω', div_eq_mul_inv]
    ring
  have hright : ∀ ω : Ω, Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (halfBarrier X σ h₂ k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω
      = Set.indicator (halfBarrier X σ h₁ k j₀ t C₁ a B ∩ halfBarrier X σ h₂ k j₀ t C₁ a B)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω := by
    intro ω
    exact (Set.inter_indicator_mul _ _ ω).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hleft),
    integral_congr_ae (Filter.Eventually.of_forall hright),
    integral_indicator (hm₁.inter hm₂), integral_indicator (hm₁.inter hm₂)]
  exact setIntegral_twistPair_mul_pair_le hX hkj hy
    (integral_halfTwist_pair_le hX hk₀ hk hσ hh₁0 hh₁ hh₂0 hh₂)

/-- **The denominator, with both heights integrated out.**  (C2) at every pair of heights on the
window, then the comparison, leaving `e^{132}` times the second moment's quantity. -/
theorem integral_invCube_mul_sq_setIntegral_le (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk₀ : 1 ≤ k₀) (hk : k₀ ≤ k) (hkj : k + j₀ ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (C₁ a B : ℝ) :
    (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
        * (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
      ≤ Real.exp 132 * ∫ ω, (∫ h in halfWindow k,
          Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ := by
  have hd0 : 0 < blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ :=
    blockEnvDown_pos _ _ hσ
  refine integral_mul_sq_setIntegral_le hX (scaleCut (k₀ : ℝ)) y (scaleCut (k : ℝ)) y hσ
    (fun h => halfBarrier X σ h k j₀ t C₁ a B)
    (fun h => measurableSet_of_primeAlgebra hX
      (measurableSet_primeAlgebra_halfBarrier (X := X) (y := y) σ h hkj hy C₁ a B))
    (measurableSet_prod_halfBarrier hX σ k j₀ t C₁ a B) measurableSet_Icc
    (volume_halfWindow_ne_top k)
    (fun ω => (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹)
    (((measurable_norm_randomEulerProductIco hX (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
      (shiftLine σ 0)).pow_const 3).inv).aestronglyMeasurable
    (c := (blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ ^ 3)⁻¹) ?_ ?_
  · filter_upwards [ae_forall_norm_randomEulerProductIco_env hX (scaleCut (k₀ : ℝ))
      (scaleCut (k : ℝ)) hσ] with ω hω
    have hd := (hω 0).1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hd0.le hd 3)
  · intro h₁ hh₁ h₂ hh₂
    have hb₁ : (0 : ℝ) ≤ h₁ := le_trans (Real.exp_pos _).le hh₁.1
    have hb₂ : (0 : ℝ) ≤ h₂ := le_trans (Real.exp_pos _).le hh₂.1
    exact integral_invCube_mul_pair_le hX hk₀ hk hσ hkj hy hlo hhi hb₁ hh₁.2 hb₂ hh₂.2 C₁ a B

end Denominator

/-! ### The Paley–Zygmund estimate at one scale

Reverse Hölder (`RMF.le_integral_weight_sqrt`) with `w = 1_{E(k)}‖F_{(k₀,k]}(σ)‖` and
`Y = mass_k/‖F_{(k₀,k]}(σ)‖²`.  The weight is what makes `w√Y` exactly `1_{E(k)}√(mass_k)`, `wY`
the numerator of the last two sections and `wY²` at most their denominator. -/

section OneScale

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The window mass is measurable. -/
lemma aestronglyMeasurable_halfWindowMass (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ}
    (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ)) (hhi : scaleCut (k : ℝ) ≤ y) (C₁ a B : ℝ) :
    AEStronglyMeasurable (fun ω => halfWindowMass X σ k₀ k j₀ t y C₁ a B ω) μ := by
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX (scaleCut (k₀ : ℝ)) y hσ
    (volume_halfWindow_ne_top k) (fun h => halfBarrier X σ h k j₀ t C₁ a B)
    (measurableSet_prod_halfBarrier hX σ k j₀ t C₁ a B)
  have h := (hbase.integral_prod_left.aestronglyMeasurable).const_mul
    (Real.exp (2 * (k : ℝ)) / 2)
  exact h.congr (Filter.Eventually.of_forall fun ω =>
    (halfWindowMass_eq_single hlo hhi C₁ a B ω).symm)

/-- The window mass is bounded. -/
lemma ae_halfWindowMass_le (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 0 ≤ σ)
    {k₀ k j₀ t y : ℕ} (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (C₁ a B : ℝ) :
    ∀ᵐ ω ∂μ, halfWindowMass X σ k₀ k j₀ t y C₁ a B ω
      ≤ Real.exp (2 * (k : ℝ)) / 2
        * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k)) := by
  filter_upwards [ae_forall_norm_indicator_normSq_Ico_le hX (scaleCut (k₀ : ℝ)) y hσ
    (fun h => halfBarrier X σ h k j₀ t C₁ a B)] with ω hω
  rw [halfWindowMass_eq_single hlo hhi C₁ a B ω]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (le_abs_self _) ?_
  rw [← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const
    (lt_of_le_of_ne le_top (volume_halfWindow_ne_top k)) fun h _ => hω h

private lemma integrable_of_bdd [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hm : AEStronglyMeasurable f μ) {C : ℝ} (hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hm hb

/-- The reverse Hölder's weight at scale `k`: the event `E(k)`, weighted by the small-prime
product at the real point. -/
private noncomputable def pzW (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k t : ℕ) (ω : Ω) : ℝ :=
  Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
    (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖) ω

/-- The reverse Hölder's variable at scale `k`: the window mass, normalised. -/
private noncomputable def pzY (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ)
    (ω : Ω) : ℝ :=
  halfWindowMass X σ k₀ k j₀ t y C₁ a B ω
    / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 2

omit [MeasurableSpace Ω] in
private lemma pzW_nonneg (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k t : ℕ) (ω : Ω) :
    0 ≤ pzW X σ k₀ k t ω :=
  Set.indicator_nonneg (fun _ _ => norm_nonneg _) ω

omit [MeasurableSpace Ω] in
private lemma pzY_nonneg (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ) (ω : Ω) :
    0 ≤ pzY X σ k₀ k j₀ t y C₁ a B ω :=
  div_nonneg (halfWindowMass_nonneg X σ k₀ k j₀ t y C₁ a B ω) (by positivity)

omit [MeasurableSpace Ω] in
/-- `w·√Y = 1_{E(k)}√(mass_k)`, off the null set where the small-prime product vanishes. -/
private lemma pzW_mul_sqrt_pzY {X : ℕ → Ω → ℂ} {σ : ℝ} {k₀ k j₀ t y : ℕ} {C₁ a B : ℝ} {ω : Ω}
    (hpos : 0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖) :
    pzW X σ k₀ k t ω * Real.sqrt (pzY X σ k₀ k j₀ t y C₁ a B ω)
      = Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω := by
  rw [pzW, pzY]
  by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ halfAfter X σ k t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Real.sqrt_div
      (halfWindowMass_nonneg X σ k₀ k j₀ t y C₁ a B ω), Real.sqrt_sq hpos.le]
    field_simp
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]

omit [MeasurableSpace Ω] in
/-- `w·Y = 1_{E(k)}·mass_k/‖F_{(k₀,k]}(σ)‖`. -/
private lemma pzW_mul_pzY (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ) (ω : Ω) :
    pzW X σ k₀ k t ω * pzY X σ k₀ k j₀ t y C₁ a B ω
      = Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => halfWindowMass X σ k₀ k j₀ t y C₁ a B ω
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖) ω := by
  rw [pzW, pzY]
  by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ halfAfter X σ k t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
    rcases eq_or_lt_of_le (norm_nonneg (randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
      (shiftLine σ 0) ω)) with h0 | h0
    · rw [← h0]
      simp
    · field_simp
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]

omit [MeasurableSpace Ω] in
/-- `w·Y² ≤ ‖F_{(k₀,k]}(σ)‖^{-3}·mass_k²`. -/
private lemma pzW_mul_pzY_sq_le (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ) (C₁ a B : ℝ)
    (ω : Ω) :
    pzW X σ k₀ k t ω * pzY X σ k₀ k j₀ t y C₁ a B ω ^ 2
      ≤ (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
        * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω ^ 2 := by
  have hM := halfWindowMass_nonneg X σ k₀ k j₀ t y C₁ a B ω
  rw [pzW, pzY]
  by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ halfAfter X σ k t
  · rw [Set.indicator_of_mem hm]
    rcases eq_or_lt_of_le (norm_nonneg (randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
      (shiftLine σ 0) ω)) with h0 | h0
    · rw [← h0]
      simp
    · have hne : ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ≠ 0 := ne_of_gt h0
      refine le_of_eq ?_
      field_simp
  · rw [Set.indicator_of_notMem hm, zero_mul]
    positivity

omit [MeasurableSpace Ω] in
/-- `1_{E(k)}·mass_k/‖F_{(k₀,k]}(σ)‖` is the numerator's window integral. -/
private lemma indicator_halfWindowMass_div_eq (X : ℕ → Ω → ℂ) (σ : ℝ) (k₀ k j₀ t y : ℕ)
    (C₁ a B : ℝ) (ω : Ω) :
    Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
        (fun ω => halfWindowMass X σ k₀ k j₀ t y C₁ a B ω
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖) ω
      = Real.exp (2 * (k : ℝ)) / 2 * ∫ h in halfWindow k,
          Set.indicator (halfLadder X σ k₀ k)
              (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
                (fun p => X (p : ℕ) ω)) ω
            * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
                (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω := by
  by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ halfAfter X σ k t
  · rw [Set.indicator_of_mem hm, halfWindowMass, mul_div_assoc, ← integral_div]
    refine congrArg (fun r => Real.exp (2 * (k : ℝ)) / 2 * r)
      (setIntegral_congr_fun measurableSet_Icc fun h _ => ?_)
    rw [Set.indicator_of_mem hm.1]
    by_cases hL : ω ∈ halfBarrier X σ h k j₀ t C₁ a B
    · rw [Set.indicator_of_mem hL, Set.indicator_of_mem (Set.mem_inter hL hm.2),
        twistPoly_primesIco]
      ring
    · rw [Set.indicator_of_notMem hL,
        Set.indicator_of_notMem (fun hc => hL (Set.mem_of_mem_inter_left hc)), zero_div, mul_zero]
  · rw [Set.indicator_of_notMem hm]
    have hzero : ∀ h : ℝ, Set.indicator (halfLadder X σ k₀ k)
          (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
            (fun p => X (p : ℕ) ω)) ω
        * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω = 0 := by
      intro h
      by_cases hlad : ω ∈ halfLadder X σ k₀ k
      · have haf : ω ∉ halfAfter X σ k t := fun hc => hm (Set.mem_inter hlad hc)
        rw [Set.indicator_of_notMem (fun hc => haf (Set.mem_of_mem_inter_right hc)), mul_zero]
      · rw [Set.indicator_of_notMem hlad, zero_mul]
    have hz : (∫ h in halfWindow k, Set.indicator (halfLadder X σ k₀ k)
          (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
            (fun p => X (p : ℕ) ω)) ω
        * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) = 0 := by
      refine (setIntegral_congr_fun (s := halfWindow k) measurableSet_Icc
        (fun h _ => hzero h)).trans ?_
      simp
    rw [hz, mul_zero]

/-- **The Paley–Zygmund estimate at one scale.**  Reverse Hölder with
`w = 1_{E(k)}‖F_{(k₀,k]}(σ)‖` and `Y = mass_k/‖F_{(k₀,k]}(σ)‖²`, whose three moments are the
numerator of `RMF.le_integral_setIntegral_twist_normSq`, the denominator of
`RMF.integral_invCube_mul_sq_setIntegral_le`, and `1_{E(k)}√(mass_k)`. -/
theorem le_integral_indicator_sqrt_halfWindowMass (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk₀5 : 5 ≤ scaleCut (k₀ : ℝ)) (hkt : k ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (hk : k₀ ≤ k) {C₁ a B lam N D : ℝ} (hlam : 0 < lam)
    (hN : N ≤ Real.exp (2 * (k : ℝ)) / 2 * ∫ ω, (∫ h in halfWindow k,
        Set.indicator (halfLadder X σ k₀ k)
            (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
              (fun p => X (p : ℕ) ω)) ω
          * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ∂μ)
    (hD : (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
          * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω ^ 2 ∂μ) ≤ D)
    (hhalf : D / (3 * lam ^ 2) ≤ N / 2) :
    3 * N / (4 * lam)
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hpos := ae_norm_randomEulerProductIco_pos hX (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
    hk₀5 hσ
  have hEm : MeasurableSet (halfLadder X σ k₀ k ∩ halfAfter X σ k t) :=
    (measurableSet_of_primeAlgebra hX
        (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)).inter
      (measurableSet_of_primeAlgebra hX
        (measurableSet_primeAlgebra_halfAfter (X := X) (y := y) σ hkt hy))
  have hFm : Measurable (fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
      (shiftLine σ 0) ω‖) :=
    measurable_norm_randomEulerProductIco hX (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))
      (shiftLine σ 0)
  have hMm := aestronglyMeasurable_halfWindowMass hX hσ (j₀ := j₀) (t := t) hlo hhi C₁ a B
  have henv := ae_forall_norm_randomEulerProductIco_env hX (scaleCut (k₀ : ℝ))
    (scaleCut (k : ℝ)) hσ
  have hd0 : 0 < blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ :=
    blockEnvDown_pos _ _ hσ
  -- the weight and the variable, measurable and bounded
  have hwm : AEStronglyMeasurable (pzW X σ k₀ k t) μ :=
    ((hFm.indicator hEm).aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hYm : AEStronglyMeasurable (pzY X σ k₀ k j₀ t y C₁ a B) μ :=
    (hMm.aemeasurable.div (hFm.pow_const 2).aemeasurable).aestronglyMeasurable
  have hwb : ∀ᵐ ω ∂μ, ‖pzW X σ k₀ k t ω‖
      ≤ blockEnvUp (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ := by
    filter_upwards [henv] with ω hω
    have hup := (hω 0).2
    rw [Real.norm_eq_abs, abs_of_nonneg (pzW_nonneg X σ k₀ k t ω), pzW]
    by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ halfAfter X σ k t
    · rw [Set.indicator_of_mem hm]
      exact hup
    · rw [Set.indicator_of_notMem hm]
      exact le_trans (norm_nonneg _) hup
  have hYb : ∀ᵐ ω ∂μ, ‖pzY X σ k₀ k j₀ t y C₁ a B ω‖
      ≤ Real.exp (2 * (k : ℝ)) / 2
          * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k))
        / blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ ^ 2 := by
    filter_upwards [henv, ae_halfWindowMass_le hX hσ (j₀ := j₀) (t := t) hlo hhi C₁ a B] with
      ω hω hMle
    have hlow := (hω 0).1
    rw [Real.norm_eq_abs, abs_of_nonneg (pzY_nonneg X σ k₀ k j₀ t y C₁ a B ω), pzY]
    exact div_le_div₀ (by positivity) hMle (by positivity) (pow_le_pow_left₀ hd0.le hlow 2)
  -- the three integrabilities
  have h0 : Integrable (fun ω => pzW X σ k₀ k t ω * pzY X σ k₀ k j₀ t y C₁ a B ω) μ := by
    refine integrable_of_bdd (hwm.mul hYm)
      (C := blockEnvUp (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ
        * (Real.exp (2 * (k : ℝ)) / 2
            * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k))
          / blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ ^ 2)) ?_
    filter_upwards [hwb, hYb] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  have h1 : Integrable (fun ω => pzW X σ k₀ k t ω
      * Real.sqrt (pzY X σ k₀ k j₀ t y C₁ a B ω)) μ := by
    refine integrable_of_bdd
      (hwm.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hYm))
      (C := blockEnvUp (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ
        * Real.sqrt (Real.exp (2 * (k : ℝ)) / 2
            * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k))
          / blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ ^ 2)) ?_
    filter_upwards [hwb, hYb] with ω hw1 hw2
    rw [norm_mul]
    refine mul_le_mul hw1 ?_ (norm_nonneg _) (le_trans (norm_nonneg _) hw1)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    exact le_trans (le_abs_self _) (by rwa [← Real.norm_eq_abs])
  have h2 : Integrable (fun ω => pzW X σ k₀ k t ω * pzY X σ k₀ k j₀ t y C₁ a B ω ^ 2) μ := by
    refine integrable_of_bdd (hwm.mul (hYm.pow 2))
      (C := blockEnvUp (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ
        * (Real.exp (2 * (k : ℝ)) / 2
            * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k))
          / blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ ^ 2) ^ 2) ?_
    filter_upwards [hwb, hYb] with ω hw1 hw2
    rw [norm_mul, norm_pow]
    exact mul_le_mul hw1 (pow_le_pow_left₀ (norm_nonneg _) hw2 2) (by positivity)
      (le_trans (norm_nonneg _) hw1)
  -- the two moments
  have hNeq : (∫ ω, pzW X σ k₀ k t ω * pzY X σ k₀ k j₀ t y C₁ a B ω ∂μ)
      = Real.exp (2 * (k : ℝ)) / 2 * ∫ ω, (∫ h in halfWindow k,
        Set.indicator (halfLadder X σ k₀ k)
            (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
              (fun p => X (p : ℕ) ω)) ω
          * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [pzW_mul_pzY, indicator_halfWindowMass_div_eq]
  have hDle : (∫ ω, pzW X σ k₀ k t ω * pzY X σ k₀ k j₀ t y C₁ a B ω ^ 2 ∂μ) ≤ D := by
    refine le_trans (integral_mono h2 ?_ (fun ω => pzW_mul_pzY_sq_le X σ k₀ k j₀ t y C₁ a B ω))
      hD
    refine integrable_of_bdd (((hFm.pow_const 3).inv).aestronglyMeasurable.mul (hMm.pow 2))
      (C := (blockEnvDown (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) σ ^ 3)⁻¹
        * (Real.exp (2 * (k : ℝ)) / 2
            * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k))) ^ 2) ?_
    filter_upwards [henv, ae_halfWindowMass_le hX hσ (j₀ := j₀) (t := t) hlo hhi C₁ a B] with
      ω hω hMle
    have hlow := (hω 0).1
    have hM0 := halfWindowMass_nonneg X σ k₀ k j₀ t y C₁ a B ω
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    refine mul_le_mul (inv_anti₀ (by positivity) (pow_le_pow_left₀ hd0.le hlow 3))
      (pow_le_pow_left₀ hM0 hMle 2) (by positivity) (by positivity)
  -- reverse Hölder
  refine le_trans (le_integral_weight_sqrt (pzW_nonneg X σ k₀ k t)
    (pzY_nonneg X σ k₀ k j₀ t y C₁ a B) hlam h0 h1 h2 (hNeq ▸ hN) hDle hhalf) (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  exact pzW_mul_sqrt_pzY hω

end OneScale

/-! ### The scales are disjoint, and the arithmetic of the step

`E(k) = E_≤(k) ∩ E_>(k)` says that the walk from `k₀` is at a strict record at `k` and never
recovers it up to `t`; two scales cannot both do that, which is what
`RMF.sum_indicator_sqrt_le_sqrt_sum` asks for.  The arithmetic of the Paley–Zygmund step is
separated out because the square roots are where `nlinarith` would go wrong in a large
context. -/

section Scales

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The `λ` of the Paley–Zygmund step at one scale: `√(2d₀P/(3n₀))`, where `N ≥ n₀P` and
`D ≤ d₀P²`. -/
noncomputable def pzLam (n₀ d₀ P : ℝ) : ℝ := Real.sqrt (2 * d₀ * P / (3 * n₀))

lemma pzLam_pos {n₀ d₀ P : ℝ} (hn₀ : 0 < n₀) (hd₀ : 0 < d₀) (hP : 0 < P) :
    0 < pzLam n₀ d₀ P :=
  Real.sqrt_pos.2 (by positivity)

/-- **The reverse-Hölder condition holds at that `λ`**, with equality. -/
lemma pz_half_le {n₀ d₀ P N D : ℝ} (hn₀ : 0 < n₀) (hd₀ : 0 < d₀) (hP : 0 < P)
    (hN : n₀ * P ≤ N) (hD : D ≤ d₀ * P ^ 2) :
    D / (3 * pzLam n₀ d₀ P ^ 2) ≤ N / 2 := by
  have hsq : pzLam n₀ d₀ P ^ 2 = 2 * d₀ * P / (3 * n₀) :=
    Real.sq_sqrt (by positivity)
  rw [pzLam] at hsq
  rw [pzLam, hsq]
  have h3 : (3 : ℝ) * (2 * d₀ * P / (3 * n₀)) = 2 * d₀ * P / n₀ := by
    field_simp
  rw [h3, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
  have hstep : D * 2 ≤ d₀ * P ^ 2 * 2 := by linarith
  have hgoal : d₀ * P ^ 2 * 2 ≤ N * (2 * d₀ * P / n₀) := by
    have hid : N * (2 * d₀ * P / n₀) - d₀ * P ^ 2 * 2 = (N - n₀ * P) * (2 * d₀ * P / n₀) := by
      field_simp
    have hnn : (0 : ℝ) ≤ (N - n₀ * P) * (2 * d₀ * P / n₀) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  linarith

/-- **The value of `3N/(4λ)` at that `λ`**: `≥ (3n₀/4)√(3n₀/(2d₀))·√P`. -/
lemma pz_value_le {n₀ d₀ P N : ℝ} (hn₀ : 0 < n₀) (hd₀ : 0 < d₀) (hP : 0 < P)
    (hN : n₀ * P ≤ N) :
    3 * n₀ / 4 * Real.sqrt (3 * n₀ / (2 * d₀)) * Real.sqrt P
      ≤ 3 * N / (4 * pzLam n₀ d₀ P) := by
  have hlam : 0 < pzLam n₀ d₀ P := pzLam_pos hn₀ hd₀ hP
  have hkey : Real.sqrt (3 * n₀ / (2 * d₀)) * Real.sqrt P * pzLam n₀ d₀ P = P := by
    rw [pzLam, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [show 3 * n₀ / (2 * d₀) * P * (2 * d₀ * P / (3 * n₀)) = P ^ 2 by field_simp]
    exact Real.sqrt_sq hP.le
  rw [le_div_iff₀ (by positivity)]
  calc 3 * n₀ / 4 * Real.sqrt (3 * n₀ / (2 * d₀)) * Real.sqrt P * (4 * pzLam n₀ d₀ P)
      = 3 * n₀ * (Real.sqrt (3 * n₀ / (2 * d₀)) * Real.sqrt P * pzLam n₀ d₀ P) := by ring
    _ = 3 * (n₀ * P) := by rw [hkey]; ring
    _ ≤ 3 * N := by linarith

/-- **The scale-`k` summand of the pointwise step is integrable**, which is what lets the sum
over scales be taken outside the expectation. -/
theorem integrable_indicator_sqrt_halfWindowMass (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk : k₀ ≤ k) (hkt : k ≤ t) (hy : scaleCut (t : ℝ) ≤ y)
    (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ)) (hhi : scaleCut (k : ℝ) ≤ y) (C₁ a B : ℝ) :
    Integrable (fun ω => Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
      (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω) μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hEm : MeasurableSet (halfLadder X σ k₀ k ∩ halfAfter X σ k t) :=
    (measurableSet_of_primeAlgebra hX
        (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)).inter
      (measurableSet_of_primeAlgebra hX
        (measurableSet_primeAlgebra_halfAfter (X := X) (y := y) σ hkt hy))
  have hMm := aestronglyMeasurable_halfWindowMass hX hσ (j₀ := j₀) (t := t) hlo hhi C₁ a B
  refine integrable_of_bdd
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hMm).indicator hEm)
    (C := Real.sqrt (Real.exp (2 * (k : ℝ)) / 2
      * (blockEnvUp (scaleCut (k₀ : ℝ)) y σ ^ 2 * volume.real (halfWindow k)))) ?_
  filter_upwards [ae_halfWindowMass_le hX hσ (j₀ := j₀) (t := t) hlo hhi C₁ a B] with ω hMle
  have h0 : 0 ≤ Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
      (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω :=
    Set.indicator_nonneg (fun _ _ => Real.sqrt_nonneg _) ω
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ halfAfter X σ k t
  · rw [Set.indicator_of_mem hm]
    exact Real.sqrt_le_sqrt hMle
  · rw [Set.indicator_of_notMem hm]
    positivity

end Scales

/-! ### The estimate at one scale, and the sum over scales

The numerator, the denominator and the arithmetic of the step, put together: at each scale
`∫ 1_{E(k)}√(mass_k) ≫ √P` with `P = e^t/√(t-k)`, and the scales add because the events are
disjoint. -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The denominator, in the shape `RMF.le_integral_indicator_sqrt_halfWindowMass` asks for. -/
lemma integral_invCube_mul_halfWindowMass_sq_eq (X : ℕ → Ω → ℂ) (μ : Measure Ω) (σ : ℝ)
    {k₀ k j₀ t y : ℕ} (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (C₁ a B : ℝ) :
    (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
          * halfWindowMass X σ k₀ k j₀ t y C₁ a B ω ^ 2 ∂μ)
      = Real.exp (4 * (k : ℝ)) / 4
        * ∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
            * (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
                (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ := by
  have hexp : Real.exp (2 * (k : ℝ)) ^ 2 = Real.exp (4 * (k : ℝ)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [halfWindowMass_eq_single hlo hhi C₁ a B ω, mul_pow, div_pow, hexp]
  ring

/-- **The Paley–Zygmund estimate at one scale, with the two moments supplied.**  With
`P = e^t/√(t-k)`, `N ≥ n₀P` and `D ≤ d₀P²`. -/
theorem le_integral_indicator_sqrt_halfWindowMass_of_bounds (hX : IsRademacherPrimeValues X μ)
    {σ : ℝ} (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk₀5 : 5 ≤ scaleCut (k₀ : ℝ)) (hkt : k ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (hk : k₀ ≤ k) {C₁ a B n₀ d₀ P : ℝ}
    (hn₀ : 0 < n₀) (hd₀ : 0 < d₀) (hP : 0 < P)
    (hNum : n₀ * P ≤ Real.exp (2 * (k : ℝ)) / 2 * ∫ ω, (∫ h in halfWindow k,
        Set.indicator (halfLadder X σ k₀ k)
            (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
              (fun p => X (p : ℕ) ω)) ω
          * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ∂μ)
    (hDen : Real.exp (4 * (k : ℝ)) / 4
        * (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
            * (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
                (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
        ≤ d₀ * P ^ 2) :
    3 * n₀ / 4 * Real.sqrt (3 * n₀ / (2 * d₀)) * Real.sqrt P
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ := by
  refine le_trans (pz_value_le hn₀ hd₀ hP le_rfl) ?_
  refine le_integral_indicator_sqrt_halfWindowMass hX hσ hk₀5 hkt hy hlo hhi hk
    (pzLam_pos hn₀ hd₀ hP) hNum ?_ (pz_half_le hn₀ hd₀ hP le_rfl le_rfl)
  rw [integral_invCube_mul_halfWindowMass_sq_eq X μ σ hlo hhi C₁ a B]
  exact hDen

omit [MeasurableSpace Ω] in
private lemma indicator_const_mul' (S : Set Ω) (c : ℝ) (f : Ω → ℝ) (ω : Ω) :
    Set.indicator S (fun ω => c * f ω) ω = c * Set.indicator S f ω := by
  by_cases hm : ω ∈ S
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, mul_zero]

/-- **The square root of the line integral is integrable.**
`RMF.integrable_rpow_eulerProductLine_of_two_le` at `q = ½`. -/
theorem integrable_sqrt_integral_lineDiv (hX : IsRademacherPrimeValues X μ) {y : ℕ}
    (hy : 3 ≤ y) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun ω => Real.sqrt (∫ u : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ u) ω
        / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2)) μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have h := integrable_rpow_eulerProductLine_of_two_le hX (y := y') (by omega) hσ
    (q := 1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [Real.sqrt_eq_rpow]
  simp_rw [shiftLine_eq_half_add]

/-- **The sum over scales.**  The pointwise step, integrated: the per-scale estimates add,
because the events `E(k)` are disjoint. -/
theorem le_integral_sqrt_integral_lineDiv (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ0 : 0 < σ) {k₀ j₀ t y : ℕ} (hy3 : 3 ≤ y) (hyt : scaleCut (t : ℝ) ≤ y)
    {C₁ a B γ : ℝ} {K : Finset ℕ}
    (hKk₀ : ∀ k ∈ K, k₀ ≤ k) (hKt : ∀ k ∈ K, k ≤ t)
    (hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)))
    (hKlo : ∀ k ∈ K, scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hKhi : ∀ k ∈ K, scaleCut (k : ℝ) ≤ y)
    (hper : ∀ k ∈ K, γ ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
        (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ) :
    halfHeadConst (scaleCut (k₀ : ℝ)) * ((K.card : ℝ) * γ)
      ≤ ∫ ω, Real.sqrt (∫ u : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
              (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc₀0 : 0 < halfHeadConst (scaleCut (k₀ : ℝ)) := halfHeadConst_pos _
  have hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      Disjoint (halfLadder X σ k₀ i ∩ halfAfter X σ i t)
        (halfLadder X σ k₀ j ∩ halfAfter X σ j t) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_halfLadder_inter_halfAfter X σ (hKk₀ i hi) h (hKt j hj)
    · exact (disjoint_halfLadder_inter_halfAfter X σ (hKk₀ j hj) h (hKt i hi)).symm
  have hint : ∀ k ∈ K, Integrable (fun ω => Set.indicator
      (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
        (fun ω => halfHeadConst (scaleCut (k₀ : ℝ))
          * Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω) μ := by
    intro k hk
    refine ((integrable_indicator_sqrt_halfWindowMass hX hσ0.le (j₀ := j₀) (hKk₀ k hk)
      (hKt k hk) hyt
      (hKlo k hk) (hKhi k hk) C₁ a B).const_mul (halfHeadConst (scaleCut (k₀ : ℝ)))).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    exact (indicator_const_mul' _ _ _ ω).symm
  have hterm : ∀ k ∈ K, halfHeadConst (scaleCut (k₀ : ℝ)) * γ
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => halfHeadConst (scaleCut (k₀ : ℝ))
            * Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ := by
    intro k hk
    rw [integral_congr_ae (Filter.Eventually.of_forall
      fun ω => indicator_const_mul' (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
        (halfHeadConst (scaleCut (k₀ : ℝ)))
        (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω),
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hper k hk) hc₀0.le
  calc halfHeadConst (scaleCut (k₀ : ℝ)) * ((K.card : ℝ) * γ)
      = ∑ _k ∈ K, halfHeadConst (scaleCut (k₀ : ℝ)) * γ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ k ∈ K, ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => halfHeadConst (scaleCut (k₀ : ℝ))
            * Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ :=
        Finset.sum_le_sum hterm
    _ = ∫ ω, ∑ k ∈ K, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => halfHeadConst (scaleCut (k₀ : ℝ))
            * Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ :=
        (integral_finsetSum K hint).symm
    _ ≤ _ :=
        integral_mono_ae (integrable_finsetSum K hint)
          (integrable_sqrt_integral_lineDiv hX hy3 hσ0)
          (ae_sum_indicator_sqrt_halfWindowMass_le hX hσ0 hKσ hKlo hKhi hdisj)

omit [MeasurableSpace Ω] in
/-- `u / √(√u) = u^{3/4}`. -/
lemma div_sqrt_sqrt_eq_rpow {u : ℝ} (hu : 0 < u) :
    u / Real.sqrt (Real.sqrt u) = u ^ (3 / 4 : ℝ) := by
  have h1 : Real.sqrt (Real.sqrt u) = u ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
    norm_num
  rw [h1, show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, Real.rpow_sub hu, Real.rpow_one]

/-- **The scale-`k` estimate, in the form the sum over scales uses.**  The same as
`RMF.le_integral_indicator_sqrt_halfWindowMass_of_bounds` at `P = e^t/√(t-k)`, with `√P`
replaced by the `k`-free `√(e^t/√t)`. -/
theorem le_integral_indicator_sqrt_halfWindowMass_uniform (hX : IsRademacherPrimeValues X μ)
    {σ : ℝ} (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk₀5 : 5 ≤ scaleCut (k₀ : ℝ)) (hkt : k ≤ t)
    (hy : scaleCut (t : ℝ) ≤ y) (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ))
    (hhi : scaleCut (k : ℝ) ≤ y) (hk : k₀ ≤ k) {C₁ a B n₀ d₀ : ℝ}
    (hn₀ : 0 < n₀) (hd₀ : 0 < d₀) (hklt : (k : ℝ) < t)
    (hNum : n₀ * (Real.exp (t : ℝ) / Real.sqrt ((t : ℝ) - k))
        ≤ Real.exp (2 * (k : ℝ)) / 2 * ∫ ω, (∫ h in halfWindow k,
        Set.indicator (halfLadder X σ k₀ k)
            (fun ω => twistPoly (primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))) σ h
              (fun p => X (p : ℕ) ω)) ω
          * Set.indicator (halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ∂μ)
    (hDen : Real.exp (4 * (k : ℝ)) / 4
        * (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
            * (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
                (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
        ≤ d₀ * (Real.exp (t : ℝ) / Real.sqrt ((t : ℝ) - k)) ^ 2) :
    3 * n₀ / 4 * Real.sqrt (3 * n₀ / (2 * d₀))
        * Real.sqrt (Real.exp (t : ℝ) / Real.sqrt (t : ℝ))
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ := by
  have ht0 : (0 : ℝ) < (t : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg k) hklt
  have hsub : (0 : ℝ) < (t : ℝ) - k := by linarith
  have hP : 0 < Real.exp (t : ℝ) / Real.sqrt ((t : ℝ) - k) := by positivity
  refine le_trans ?_ (le_integral_indicator_sqrt_halfWindowMass_of_bounds hX hσ hk₀5 hkt hy
    hlo hhi hk hn₀ hd₀ hP hNum hDen)
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  refine div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) ?_
  exact Real.sqrt_le_sqrt (by linarith)

/-- **The scale-`k` estimate, from (C2), (C3) and the two barriered moments.**  The numerator is
`n₀·e^t/√(t-k)` *exactly*, with `n₀ = c₃c₄(1-e^{-1})/2`, and the denominator is
`d₀·(e^t/√(t-k))²` with `d₀ = e^{132}C₃/4`. -/
theorem le_integral_indicator_sqrt_halfWindowMass_final (hX : IsRademacherPrimeValues X μ)
    {σ : ℝ} (hσ : 0 ≤ σ) {k₀ k j₀ t y : ℕ} (hk₀5 : 5 ≤ scaleCut (k₀ : ℝ)) (hk₀1 : 1 ≤ k₀)
    (hk : k₀ ≤ k) (hklt : k < t) (hkj : k + j₀ ≤ t) (hy : scaleCut (t : ℝ) ≤ y)
    (hlo : scaleCut (k₀ : ℝ) ≤ scaleCut (k : ℝ)) (hhi : scaleCut (k : ℝ) ≤ y)
    {C₁ a B c₃ c₄ C₃ : ℝ} (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) (hC₃ : 0 < C₃)
    (h₃ : ∀ h ∈ halfWindow k, c₃ ≤ ∫ ω in halfLadder X σ k₀ k,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
    (h₄ : ∀ h ∈ halfWindow k,
      c₄ * Real.exp ((t : ℝ) - k) / Real.sqrt ((t : ℝ) - k)
        ≤ ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
    (hM3 : (∫ ω, (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
        ≤ C₃ * Real.exp (2 * (t : ℝ) - 4 * k) / ((t : ℝ) - k)) :
    3 * (c₃ * c₄ * (1 - Real.exp (-1)) / 2) / 4
        * Real.sqrt (3 * (c₃ * c₄ * (1 - Real.exp (-1)) / 2)
            / (2 * (Real.exp 132 * C₃ / 4)))
        * Real.sqrt (Real.exp (t : ℝ) / Real.sqrt (t : ℝ))
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ := by
  have hklt' : (k : ℝ) < t := by exact_mod_cast hklt
  have hsub : (0 : ℝ) < (t : ℝ) - k := by linarith
  have hS : (0 : ℝ) < Real.sqrt ((t : ℝ) - k) := Real.sqrt_pos.2 hsub
  have hSsq : Real.sqrt ((t : ℝ) - k) ^ 2 = (t : ℝ) - k := Real.sq_sqrt hsub.le
  have he1 : Real.exp (-1 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hn₀ : 0 < c₃ * c₄ * (1 - Real.exp (-1)) / 2 := by
    have : (0 : ℝ) < 1 - Real.exp (-1) := by linarith
    positivity
  have hd₀ : 0 < Real.exp 132 * C₃ / 4 := by positivity
  refine le_integral_indicator_sqrt_halfWindowMass_uniform hX hσ hk₀5 (le_of_lt hklt) hy hlo hhi
    hk hn₀ hd₀ hklt' ?_ ?_
  · -- the numerator
    have hnum := le_integral_setIntegral_twist_normSq hX hσ hk hkj hy
      (c₄ := c₄ * Real.exp ((t : ℝ) - k) / Real.sqrt ((t : ℝ) - k)) (by positivity) h₃ h₄
    have halg : Real.exp (2 * (k : ℝ)) / 2
          * (c₃ * (c₄ * Real.exp ((t : ℝ) - k) / Real.sqrt ((t : ℝ) - k))
            * (Real.exp (-(k : ℝ)) - Real.exp (-((k : ℝ) + 1))))
        = c₃ * c₄ * (1 - Real.exp (-1)) / 2 * (Real.exp (t : ℝ) / Real.sqrt ((t : ℝ) - k)) := by
      have hsplit : Real.exp (-((k : ℝ) + 1)) = Real.exp (-(k : ℝ)) * Real.exp (-1) := by
        rw [← Real.exp_add]
        ring_nf
      have hprod : Real.exp (2 * (k : ℝ)) * Real.exp ((t : ℝ) - k) * Real.exp (-(k : ℝ))
          = Real.exp (t : ℝ) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      rw [hsplit, ← hprod]
      field_simp
    rw [← halg]
    exact mul_le_mul_of_nonneg_left hnum (by positivity)
  · -- the denominator
    have hden := integral_invCube_mul_sq_setIntegral_le hX hσ hk₀1 hk hkj hy hlo hhi C₁ a B
    have hchain : (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3)⁻¹
            * (∫ h in halfWindow k, Set.indicator (halfBarrier X σ h k j₀ t C₁ a B)
                (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut (k₀ : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
        ≤ Real.exp 132 * (C₃ * Real.exp (2 * (t : ℝ) - 4 * k) / ((t : ℝ) - k)) :=
      le_trans hden (mul_le_mul_of_nonneg_left hM3 (Real.exp_pos _).le)
    refine le_trans (mul_le_mul_of_nonneg_left hchain (by positivity)) (le_of_eq ?_)
    have hprod : Real.exp (4 * (k : ℝ)) * Real.exp (2 * (t : ℝ) - 4 * k)
        = Real.exp (2 * (t : ℝ)) := by
      rw [← Real.exp_add]
      ring_nf
    have hesq : Real.exp (t : ℝ) ^ 2 = Real.exp (2 * (t : ℝ)) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [div_pow, hSsq, hesq, ← hprod]
    field_simp

omit [MeasurableSpace Ω] in
/-- `√(e^u) = e^{u/2}`. -/
lemma sqrt_exp_eq (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  have h : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [← h, Real.sqrt_sq (Real.exp_pos _).le]

omit [MeasurableSpace Ω] in
/-- **The last arithmetic of the decomposition.**  With `|K| ≥ t/4`, `t ≥ Λ/2` and
`e^t ≥ e^{-5}(log x)/(2V)`, the sum `(log x)^{-1/2}·|K|·√(e^t/√t)` is at least
`[e^{-5/2}/(4√2)](1/2)^{3/4}V^{-1/2}Λ^{3/4}`. -/
lemma final_arith {card tt Lx V Λ : ℝ} (hV : 1 ≤ V) (hΛ1 : 1 ≤ Λ)
    (htt : 0 < tt) (hLx : 0 < Lx) (hcard : tt / 4 ≤ card) (hΛtt : Λ / 2 ≤ tt)
    (hexp : Real.exp (-5) * (Lx / (2 * V)) ≤ Real.exp tt) :
    Real.exp (-(5 / 2 : ℝ)) / (4 * Real.sqrt 2) * (1 / 2 : ℝ) ^ (3 / 4 : ℝ)
        * V ^ (-(1 / 2 : ℝ)) * Λ ^ (3 / 4 : ℝ)
      ≤ Lx ^ (-(1 / 2 : ℝ)) * (card * Real.sqrt (Real.exp tt / Real.sqrt tt)) := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hsq2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hsqL : (0 : ℝ) < Real.sqrt Lx := Real.sqrt_pos.2 hLx
  have hq : (0 : ℝ) < Real.sqrt (Real.sqrt tt) := Real.sqrt_pos.2 (Real.sqrt_pos.2 htt)
  have h5 : Real.sqrt (Real.exp (-5 : ℝ)) = Real.exp (-(5 / 2 : ℝ)) := by
    rw [sqrt_exp_eq]
    norm_num
  -- the window factor
  have hs : Real.sqrt (Real.exp tt / Real.sqrt tt)
      = Real.exp (tt / 2) / Real.sqrt (Real.sqrt tt) := by
    rw [Real.sqrt_div (Real.exp_pos _).le, sqrt_exp_eq]
  -- the shift factor
  have hshift : Real.exp (-(5 / 2 : ℝ)) / Real.sqrt (2 * V)
      ≤ Real.exp (tt / 2) / Real.sqrt Lx := by
    have h1 : Real.sqrt (Real.exp (-5) * (Lx / (2 * V))) ≤ Real.exp (tt / 2) := by
      rw [← sqrt_exp_eq]
      exact Real.sqrt_le_sqrt hexp
    have h2 : Real.sqrt (Real.exp (-5) * (Lx / (2 * V)))
        = Real.exp (-(5 / 2 : ℝ)) * Real.sqrt Lx / Real.sqrt (2 * V) := by
      rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_div hLx.le, h5]
      ring
    rw [h2, div_le_iff₀ (Real.sqrt_pos.2 (show (0 : ℝ) < 2 * V by positivity))] at h1
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 (show (0 : ℝ) < 2 * V by positivity)) hsqL]
    exact h1
  -- the scale factor
  have hscale : (1 / 2 : ℝ) ^ (3 / 4 : ℝ) * Λ ^ (3 / 4 : ℝ)
      ≤ tt / Real.sqrt (Real.sqrt tt) := by
    rw [div_sqrt_sqrt_eq_rpow htt, ← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hsqV2 : Real.sqrt (2 * V) = Real.sqrt 2 * Real.sqrt V := Real.sqrt_mul (by norm_num) V
  have hVrpow : V ^ (-(1 / 2 : ℝ)) = (Real.sqrt V)⁻¹ := by
    rw [Real.rpow_neg hV0.le, ← Real.sqrt_eq_rpow]
  have hLrpow : Lx ^ (-(1 / 2 : ℝ)) = (Real.sqrt Lx)⁻¹ := by
    rw [Real.rpow_neg hLx.le, ← Real.sqrt_eq_rpow]
  have hcard0 : (0 : ℝ) ≤ card := le_trans (by positivity) hcard
  rw [hs, hVrpow, hLrpow]
  calc Real.exp (-(5 / 2 : ℝ)) / (4 * Real.sqrt 2) * (1 / 2 : ℝ) ^ (3 / 4 : ℝ)
        * (Real.sqrt V)⁻¹ * Λ ^ (3 / 4 : ℝ)
      = 1 / 4 * ((1 / 2 : ℝ) ^ (3 / 4 : ℝ) * Λ ^ (3 / 4 : ℝ))
          * (Real.exp (-(5 / 2 : ℝ)) / (Real.sqrt 2 * Real.sqrt V)) := by
        field_simp
    _ ≤ 1 / 4 * (tt / Real.sqrt (Real.sqrt tt))
          * (Real.exp (-(5 / 2 : ℝ)) / (Real.sqrt 2 * Real.sqrt V)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by norm_num))
          (by positivity)
    _ ≤ 1 / 4 * (tt / Real.sqrt (Real.sqrt tt)) * (Real.exp (tt / 2) / Real.sqrt Lx) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hsqV2]
        exact hshift
    _ ≤ card / Real.sqrt (Real.sqrt tt) * (Real.exp (tt / 2) / Real.sqrt Lx) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [show (1 : ℝ) / 4 * (tt / Real.sqrt (Real.sqrt tt))
            = tt / 4 / Real.sqrt (Real.sqrt tt) by ring]
        gcongr
    _ = (Real.sqrt Lx)⁻¹ * (card * (Real.exp (tt / 2) / Real.sqrt (Real.sqrt tt))) := by
        field_simp

end Assembly

/-! ### Choosing the scales

`σ = 2V/log x`, `t = ⌊log(1/σ)⌋ - 4`, `y = ⌊x⌋₊ + 1` and `K = [k₀+2, ⌊t/2⌋]`.  The three
numerical facts this choice has to deliver are separated out: the second moment's truncation sits
below `y`, the first moment's cut at `t+1` sits below `y`, and `σe^t` lands in `(e^{-5}, e^{-4}]`,
which is what makes `σe^{t+1} ≤ 1/10` and `e^{-6} ≤ σe^t` hold at once. -/

section Choice

/-- **The second moment's truncation sits below `⌊x⌋₊+1`.**  At `σ = 2V/log x` with `V ≥ 1` the
truncation `⌈e^{1/(2σ)}⌉` is at most `x/2`, since `1/(2σ) = log x/(4V) ≤ log x - log 2`. -/
lemma harperTruncation_lt_floor_succ {V x : ℝ} (hV : 1 ≤ V) (hx : Real.exp 4 ≤ x) :
    harperTruncation (2 * V / Real.log x) < ⌊x⌋₊ + 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlog : 4 ≤ Real.log x := by
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hinv : 1 / (2 * (2 * V / Real.log x)) = Real.log x / (4 * V) := by
    have hV0 : (0 : ℝ) < V := by linarith
    have hl0 : (0 : ℝ) < Real.log x := by linarith
    field_simp
    ring
  have h1 : Real.log x / (4 * V) ≤ Real.log x / 4 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have h2 : Real.log x / 4 ≤ Real.log x - Real.log 2 := by
    have := Real.log_two_lt_d9
    linarith
  have hle : Real.exp (1 / (2 * (2 * V / Real.log x))) ≤ x / 2 := by
    rw [hinv]
    calc Real.exp (Real.log x / (4 * V)) ≤ Real.exp (Real.log x - Real.log 2) :=
          Real.exp_le_exp.2 (le_trans h1 h2)
      _ = x / 2 := by
          rw [Real.exp_sub, Real.exp_log hx0, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have h2e : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hx2 : (2 : ℝ) ≤ x := le_trans h2e hx
  have hfl : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hceil : harperTruncation (2 * V / Real.log x) ≤ ⌊x⌋₊ := by
    rw [harperTruncation, Nat.ceil_le]
    linarith
  omega

/-- **The first moment's cut sits below `⌊x⌋₊+1`** as soon as `e^θ ≤ log x`. -/
lemma scaleCut_le_floor_succ {θ x : ℝ} (hx : 0 < x) (h : Real.exp θ ≤ Real.log x) :
    scaleCut θ ≤ ⌊x⌋₊ + 1 := by
  rw [scaleCut, blockScale]
  refine Nat.succ_le_succ (Nat.floor_le_floor ?_)
  calc Real.exp (Real.exp ((0 : ℕ) + θ)) = Real.exp (Real.exp θ) := by norm_num
    _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 h
    _ = x := Real.exp_log hx

/-- **The scale.**  `t = ⌊L⌋ - 4` sits in `(L-5, L-4]`. -/
lemma exists_scale_floor_sub_four {L : ℝ} (hL : 4 ≤ L) :
    ∃ t : ℕ, L - 5 < (t : ℝ) ∧ (t : ℝ) ≤ L - 4 := by
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hfl4 : 4 ≤ ⌊L⌋₊ := Nat.le_floor (by exact_mod_cast hL)
  refine ⟨⌊L⌋₊ - 4, ?_, ?_⟩
  · have hcast : ((⌊L⌋₊ - 4 : ℕ) : ℝ) = (⌊L⌋₊ : ℝ) - 4 := by
      rw [Nat.cast_sub hfl4]
      norm_num
    rw [hcast]
    have := Nat.lt_floor_add_one L
    linarith
  · have hcast : ((⌊L⌋₊ - 4 : ℕ) : ℝ) = (⌊L⌋₊ : ℝ) - 4 := by
      rw [Nat.cast_sub hfl4]
      norm_num
    rw [hcast]
    have := Nat.floor_le hL0
    linarith

end Choice

/-! ### The main term at `q = ½`

`σ = 2V/log x`, `t = ⌊log(1/σ)⌋-4`, `y = ⌊x⌋₊+1`, `K = [k₀+2, ⌊t/2⌋]`, and `k₀` the largest of
the thresholds the two barriered moments and (C3) ask for.  The proof checks that this one choice
satisfies all of their hypotheses. -/

section Final

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `2VE ≤ Lx/10` and `V ≥ 1` give `E ≤ Lx`. -/
private lemma exp_le_of_two_mul_le {V E Lx : ℝ} (hV : 1 ≤ V) (hE : 0 < E) (hLx : 0 < Lx)
    (h : 2 * V * E ≤ 1 / 10 * Lx) : E ≤ Lx := by
  nlinarith [hV, hE, hLx, h]

omit [MeasurableSpace Ω] in
/-- `sE² ≤ c ≤ 1`, `1 ≤ E` and `Ek ≤ E` give `s·Ek ≤ 1`. -/
private lemma mul_exp_le_one {s E Ek c : ℝ} (hs : 0 < s) (hE : 1 ≤ E) (hEk : Ek ≤ E)
    (h : s * E * E ≤ c) (hc : c ≤ 1) : s * Ek ≤ 1 := by
  have hE0 : (0 : ℝ) < E := by linarith
  have hsE : (0 : ℝ) < s * E := mul_pos hs hE0
  have h1 : s * Ek ≤ s * E := mul_le_mul_of_nonneg_left hEk hs.le
  have h2 : s * E ≤ s * E * E := le_mul_of_one_le_right hsE.le hE
  linarith

omit [MeasurableSpace Ω] in
/-- `A·Lx ≤ 2V·Et` gives `A·(Lx/(2V)) ≤ Et`. -/
private lemma mul_div_le_of_le {A Lx V Et : ℝ} (hV : 0 < V) (h : A * Lx ≤ 2 * V * Et) :
    A * (Lx / (2 * V)) ≤ Et := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  linarith

set_option maxHeartbeats 1000000 in
-- The assembly unpacks (C2), (C3) and the two barriered moments and checks their hypotheses at
-- one choice of `(k₀, σ, t, y, K)`; the elaboration is long rather than deep.
/-- **The main term at `q = ½`**, for `V ≥ 1` and `x ≥ x₀(V)`, with `c` independent of `V` and `x`:
`E[((log x)^{-1}∫_ℝ |F(½+2V/log x+it)/(2V/log x+it)|² dt)^{1/2}] ≥ c·V^{-1/2}(log log x)^{3/4}`.
The main term of `RMF.exists_le_integral_norm_weightedRademacherSum_half_line`.  From (C2), (C3),
the first moment (`RMF.exists_le_setIntegral_halfBarrier_halfAfter`) and the second moment
(`RMF.exists_integral_sq_setIntegral_halfBarrier_le`). -/
theorem exists_le_integral_sqrt_lineDiv_half :
    ∃ c : ℝ, 0 < c ∧ ∀ V : ℝ, 1 ≤ V → ∃ x₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
        c * V ^ (-(1 / 2 : ℝ)) * Real.log (Real.log x) ^ (3 / 4 : ℝ)
          ≤ Real.log x ^ (-(1 / 2 : ℝ)) * ∫ ω, (∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
                ^ (1 / 2 : ℝ) ∂μ := by
  classical
  obtain ⟨j₀, C₁, a, B, c₄, k₁₄, T₀₄, hC₁, ha, hB, hc₄, HM4⟩ :=
    exists_le_setIntegral_halfBarrier_halfAfter (Ω := Ω)
  obtain ⟨C₃, hC₃, k₁₃, T₀₃, HM3⟩ :=
    exists_integral_sq_setIntegral_halfBarrier_le (Ω := Ω) j₀ C₁ a B hC₁ ha hB
  set c₃ : ℝ := (Real.exp (-(20 * 200000 * 2) - 8 * 200000 ^ 2 * 2) / 4) ^ 2 / 2 with hc₃def
  have hc₃ : 0 < c₃ := by rw [hc₃def]; positivity
  obtain ⟨k₀, hk₀20, hk₀₁₄, hk₀₁₃⟩ : ∃ k₀ : ℕ, 20 ≤ k₀ ∧ k₁₄ ≤ k₀ ∧ k₁₃ ≤ k₀ :=
    ⟨max 20 (max k₁₄ k₁₃), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨T₀, hT₀₄le, hT₀₃le⟩ : ∃ T₀ : ℕ, T₀₄ ≤ T₀ ∧ T₀₃ ≤ T₀ :=
    ⟨max T₀₄ T₀₃, le_max_left _ _, le_max_right _ _⟩
  have he1 : Real.exp (-1 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  set n₀ : ℝ := c₃ * c₄ * (1 - Real.exp (-1)) / 2 with hn₀def
  set d₀ : ℝ := Real.exp 132 * C₃ / 4 with hd₀def
  have hn₀0 : 0 < n₀ := by
    have h : (0 : ℝ) < 1 - Real.exp (-1) := by linarith
    rw [hn₀def]
    positivity
  have hd₀0 : 0 < d₀ := by
    rw [hd₀def]
    positivity
  set A : ℝ := 3 * n₀ / 4 * Real.sqrt (3 * n₀ / (2 * d₀)) with hAdef
  have hA0 : 0 < A := by
    rw [hAdef]
    positivity
  set c₀ : ℝ := halfHeadConst (scaleCut (k₀ : ℝ)) with hc₀def
  have hc₀0 : 0 < c₀ := halfHeadConst_pos _
  refine ⟨c₀ * A * (Real.exp (-(5 / 2 : ℝ)) / (4 * Real.sqrt 2)) * (1 / 2 : ℝ) ^ (3 / 4 : ℝ),
    by positivity, fun V hV => ?_⟩
  set M : ℝ := 2 * Real.log (2 * V) + 4 * ((k₀ : ℝ) + 2) + 2 * (T₀ : ℝ) + 4 * (j₀ : ℝ) + 60
    with hMdef
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (Real.exp 4)).and
      ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop M))
  refine ⟨x₀, fun X μ hX x hx => ?_⟩
  obtain ⟨hxe4, hΛM⟩ := hx₀ x hx
  have hΛ : M ≤ Real.log (Real.log x) := hΛM
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe4
  have hlogx : (4 : ℝ) ≤ Real.log x := by
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    exact Real.log_le_log (Real.exp_pos _) hxe4
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hlog2V : (0 : ℝ) ≤ Real.log (2 * V) := Real.log_nonneg (by linarith)
  set σ : ℝ := 2 * V / Real.log x with hσdef
  have hσ0 : 0 < σ := by
    rw [hσdef]
    positivity
  set L : ℝ := Real.log (Real.log x) - Real.log (2 * V) with hLdef
  have hσexp : σ = Real.exp (-L) := by
    have hlogσ : Real.log σ = -L := by
      rw [hσdef, Real.log_div (by positivity) hL0.ne', hLdef]
      ring
    rw [← hlogσ, Real.exp_log hσ0]
  have hL4 : (4 : ℝ) ≤ L := by
    rw [hLdef]
    rw [hMdef] at hΛ
    have h1 : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨t, ht1, ht2⟩ := exists_scale_floor_sub_four hL4
  -- the height conditions
  have hσt : σ * Real.exp (t : ℝ) ≤ Real.exp (-4 : ℝ) := by
    rw [hσexp, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hσt5 : Real.exp (-5 : ℝ) ≤ σ * Real.exp (t : ℝ) := by
    rw [hσexp, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hσt6 : Real.exp (-6 : ℝ) ≤ σ * Real.exp (t : ℝ) :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) hσt5
  have he3 : (10 : ℝ) ≤ Real.exp 3 := by
    have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
    have hc : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hsq : (7.29 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [h27]
    have hcu : (10 : ℝ) ≤ Real.exp 1 ^ 3 := by nlinarith [h27, hsq]
    rw [hc]
    exact hcu
  have hσt1 : σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 := by
    have hrw : σ * Real.exp ((t : ℝ) + 1) = σ * Real.exp (t : ℝ) * Real.exp 1 := by
      rw [Real.exp_add]
      ring
    have h34 : Real.exp (-4 : ℝ) * Real.exp 1 = Real.exp (-3 : ℝ) := by
      rw [← Real.exp_add]
      norm_num
    have h10 : Real.exp (-3 : ℝ) ≤ 1 / 10 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) he3
    rw [hrw]
    calc σ * Real.exp (t : ℝ) * Real.exp 1
        ≤ Real.exp (-4 : ℝ) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right hσt (Real.exp_pos 1).le
      _ = Real.exp (-3 : ℝ) := h34
      _ ≤ 1 / 10 := h10
  -- the cut
  set y : ℕ := ⌊x⌋₊ + 1 with hydef
  have hyM4 : scaleCut ((t : ℝ) + 1) ≤ y := by
    refine scaleCut_le_floor_succ hx0 ?_
    have h1 := hσt1
    rw [hσdef, div_mul_eq_mul_div, div_le_iff₀ hL0] at h1
    exact exp_le_of_two_mul_le hV (Real.exp_pos _) hL0 h1
  have hyM3 : harperTruncation σ < y := by
    rw [hσdef, hydef]
    exact harperTruncation_lt_floor_succ hV hxe4
  have hy : scaleCut (t : ℝ) ≤ y := le_trans (scaleCut_mono (by linarith)) hyM4
  have hy3 : 3 ≤ y := by
    have h2e : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  -- the scales
  have httR : 4 * ((k₀ : ℝ) + 2) + 2 * (T₀ : ℝ) + 4 * (j₀ : ℝ) + 55 < (t : ℝ) := by
    rw [hLdef] at ht1
    rw [hMdef] at hΛ
    linarith
  have htnat : 4 * (k₀ + 2) + 2 * T₀ + 4 * j₀ + 55 < t := by
    have hcast : ((4 * (k₀ + 2) + 2 * T₀ + 4 * j₀ + 55 : ℕ) : ℝ) < ((t : ℕ) : ℝ) := by
      push_cast
      linarith [httR]
    exact Nat.cast_lt.mp hcast
  set K : Finset ℕ := Finset.Icc (k₀ + 2) (t / 2) with hKdef
  have hKmem : ∀ k ∈ K, k₀ + 2 ≤ k ∧ k ≤ t / 2 := by
    intro k hk
    rw [hKdef, Finset.mem_Icc] at hk
    exact hk
  have hcardK : t ≤ 4 * K.card := by
    rw [hKdef, Nat.card_Icc]
    omega
  -- the per-scale estimate
  have hper : ∀ k ∈ K, A * Real.sqrt (Real.exp (t : ℝ) / Real.sqrt (t : ℝ))
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ halfAfter X σ k t)
          (fun ω => Real.sqrt (halfWindowMass X σ k₀ k j₀ t y C₁ a B ω)) ω ∂μ := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hKmem k hk
    have hk₀k : k₀ ≤ k := by omega
    have hklt : k < t := by omega
    have hkj : k + j₀ ≤ t := by omega
    have hkT4 : k + T₀₄ ≤ t := by omega
    have hkT3 : k + T₀₃ ≤ t := by omega
    have hk14 : k₁₄ ≤ k := by omega
    have hk13 : k₁₃ ≤ k := by omega
    have hkR : (k : ℝ) ≤ (t : ℝ) / 2 := by
      have h2 : 2 * k ≤ t := by omega
      have h2' : ((2 * k : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) := Nat.cast_le.mpr h2
      push_cast at h2'
      linarith
    have hσk : σ * Real.exp (k : ℝ) ≤ 1 := by
      have hmono : Real.exp (k : ℝ) ≤ Real.exp ((t : ℝ) / 2) := Real.exp_le_exp.2 hkR
      have hhalf : Real.exp ((t : ℝ) / 2) * Real.exp ((t : ℝ) / 2) = Real.exp (t : ℝ) := by
        rw [← Real.exp_add]
        ring_nf
      have h1 : σ * Real.exp ((t : ℝ) / 2) * Real.exp ((t : ℝ) / 2) ≤ Real.exp (-4 : ℝ) := by
        rw [mul_assoc, hhalf]
        exact hσt
      have h2 : (1 : ℝ) ≤ Real.exp ((t : ℝ) / 2) :=
        Real.one_le_exp (by positivity)
      have h3 : Real.exp (-4 : ℝ) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        norm_num
      exact mul_exp_le_one hσ0 h2 hmono h1 h3
    refine le_integral_indicator_sqrt_halfWindowMass_final hX hσ0.le
      (five_le_scaleCut (Nat.one_le_cast.mpr (by omega))) (by omega) hk₀k hklt hkj hy
      (scaleCut_mono (Nat.cast_le.mpr hk₀k))
      (le_trans (scaleCut_mono (Nat.cast_le.mpr hklt.le)) hy) hc₃ hc₄ hC₃ ?_ ?_ ?_
    · intro h hh
      rw [halfWindow, Set.mem_Icc] at hh
      exact le_setIntegral_halfLadder_twist hX hk₀20 (by omega) hσ0.le hσk
        (le_trans (Real.exp_pos _).le hh.1) hh.2
    · intro h hh
      exact HM4 X μ hX k t y σ h hk14 hkT4 hσ0 hσt1 hσt6 hyM4 hh
    · exact HM3 X μ hX k t y σ hk13 hkT3 hσ0 hσt1 hσt6 hyM3
  -- the sum over scales
  have hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hKmem k hk
    have hkR : (k : ℝ) ≤ (t : ℝ) / 2 := by
      have h2 : 2 * k ≤ t := by omega
      have h2' : ((2 * k : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) := Nat.cast_le.mpr h2
      push_cast at h2'
      linarith
    have hmono : Real.exp (k : ℝ) ≤ Real.exp ((t : ℝ) / 2) := Real.exp_le_exp.2 hkR
    have hhalf : Real.exp ((t : ℝ) / 2) * Real.exp ((t : ℝ) / 2) = Real.exp (t : ℝ) := by
      rw [← Real.exp_add]
      ring_nf
    have h2 : (1 : ℝ) ≤ Real.exp ((t : ℝ) / 2) := Real.one_le_exp (by positivity)
    have h3 : Real.exp (-4 : ℝ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    rw [Real.exp_neg, le_inv_comm₀ hσ0 (Real.exp_pos _)]
    have h4 : σ * Real.exp ((t : ℝ) / 2) * Real.exp ((t : ℝ) / 2) ≤ Real.exp (-4 : ℝ) := by
      rw [mul_assoc, hhalf]
      exact hσt
    have h5 : σ * Real.exp (k : ℝ) ≤ 1 := mul_exp_le_one hσ0 h2 hmono h4 h3
    rw [← le_div_iff₀' hσ0] at h5
    calc Real.exp (k : ℝ) ≤ 1 / σ := h5
      _ = σ⁻¹ := by rw [one_div]
  have hsum := le_integral_sqrt_integral_lineDiv hX hσ0 hy3 hy
    (fun k hk => by have := hKmem k hk; omega)
    (fun k hk => by have := hKmem k hk; omega)
    hKσ
    (fun k hk => scaleCut_mono (Nat.cast_le.mpr (by have := hKmem k hk; omega)))
    (fun k hk => le_trans (scaleCut_mono
      (Nat.cast_le.mpr (by have := hKmem k hk; omega))) hy)
    hper
  -- the final arithmetic
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    have : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg _
    linarith [httR, (Nat.cast_nonneg T₀ : (0:ℝ) ≤ (T₀:ℝ)),
      (Nat.cast_nonneg j₀ : (0:ℝ) ≤ (j₀:ℝ))]
  have hΛ1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
    rw [hMdef] at hΛ
    have h1 : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hcard : (t : ℝ) / 4 ≤ (K.card : ℝ) := by
    have h4 : ((t : ℕ) : ℝ) ≤ ((4 * K.card : ℕ) : ℝ) := Nat.cast_le.mpr hcardK
    push_cast at h4
    linarith
  have htΛ : Real.log (Real.log x) / 2 ≤ (t : ℝ) := by
    rw [hLdef] at ht1
    rw [hMdef] at hΛ
    have h1 : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hexpLx : Real.exp (-5) * (Real.log x / (2 * V)) ≤ Real.exp (t : ℝ) := by
    have h := hσt5
    rw [hσdef, div_mul_eq_mul_div, le_div_iff₀ hL0] at h
    exact mul_div_le_of_le (by linarith) h
  have hfin := final_arith (card := (K.card : ℝ)) (tt := (t : ℝ)) (Lx := Real.log x) (V := V)
    (Λ := Real.log (Real.log x)) hV hΛ1 ht0 hL0 hcard htΛ hexpLx
  have hconv : (∫ ω, Real.sqrt (∫ u : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ∂μ)
      = ∫ ω, (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [Real.sqrt_eq_rpow]
    simp_rw [shiftLine_eq_half_add, hydef, hσdef]
  rw [← hconv]
  calc c₀ * A * (Real.exp (-(5 / 2 : ℝ)) / (4 * Real.sqrt 2)) * (1 / 2 : ℝ) ^ (3 / 4 : ℝ)
        * V ^ (-(1 / 2 : ℝ)) * Real.log (Real.log x) ^ (3 / 4 : ℝ)
      = c₀ * A * (Real.exp (-(5 / 2 : ℝ)) / (4 * Real.sqrt 2) * (1 / 2 : ℝ) ^ (3 / 4 : ℝ)
          * V ^ (-(1 / 2 : ℝ)) * Real.log (Real.log x) ^ (3 / 4 : ℝ)) := by ring
    _ ≤ c₀ * A * (Real.log x ^ (-(1 / 2 : ℝ))
          * ((K.card : ℝ) * Real.sqrt (Real.exp (t : ℝ) / Real.sqrt (t : ℝ)))) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = Real.log x ^ (-(1 / 2 : ℝ))
          * (c₀ * ((K.card : ℝ) * (A * Real.sqrt (Real.exp (t : ℝ) / Real.sqrt (t : ℝ))))) := by
        ring
    _ ≤ Real.log x ^ (-(1 / 2 : ℝ)) * ∫ ω, Real.sqrt (∫ u : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
              (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ∂μ :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

end Final

end RMF
