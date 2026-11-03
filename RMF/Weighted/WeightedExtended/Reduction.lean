/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedReduction

/-!
# The weighted extended sum: the square classes

The first step of the proof of Proposition 1.5 of the paper.  Write `n = s²m` with `m`
squarefree.  Then `X^e(n) = X(m)` almost surely, and `∑_{s ≤ √(x/m)} 1/s = ½ log(x/m) + r(√(x/m))`
with `0 ≤ r ≤ 1` (`RMF.harmonicRemainder_mem_Icc`), so almost surely
(`RMF.ae_weightedRademacherSum_compMultExtension_eq`)

`∑_{n≤x} X^e(n)/√n = ½A(x) + B(x)`,  `A(x) = ∑_{m≤x} X(m)m^{-1/2} log(x/m)`,
`B(x) = ∑_{m≤x} X(m)m^{-1/2} r(√(x/m))`.

`B(x)` is small: by orthogonality and Jensen,
`E|B(x)|^{2q} ≤ (1 + log x)^q` for `0 ≤ q ≤ 1` (`RMF.integral_rpow_norm_harmonicRemainderSum_le`).
`A(x)` is the Riesz mean that Perron's formula turns into a line integral of the Euler product
(`RMF/Weighted/WeightedExtended/Perron.lean`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The square classes, with a weight -/

/-- **The square classes, with a weight.**  If `v(p)² = 1` at the primes `p ≤ x`, then
`∑_{n≤x} v^e(n)g(n) = ∑_{m≤x} v^{sf}(m)∑_{s≤√(x/m)} g(s²m)`: the weighted twin of
`RMF.sum_compMultExtension_eq_sum_squarefreeExtension_mul`. -/
lemma sum_compMultExtension_mul_eq_sum_squarefreeExtension_mul_sum {v : ℕ → ℂ} {x : ℝ}
    (hx : 0 ≤ x) (hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → v p ^ 2 = 1) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension v n * g n
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension v m
          * ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, g (s ^ 2 * m) := by
  classical
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, compMultExtension v n * g n
      = ∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).sigma
          (fun m => Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊),
            squarefreeExtension v p.1 * g (p.2 ^ 2 * p.1) := by
        symm
        refine Finset.sum_bij (fun p _ => p.2 ^ 2 * p.1) (fun p hp => ?_)
          (fun p hp p' hp' h => ?_) (fun n hn => ?_) (fun p hp => ?_)
        · obtain ⟨hm, hs⟩ := Finset.mem_sigma.1 hp
          obtain ⟨hm1, -⟩ := Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1
          obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
          refine Finset.mem_Icc.2 ⟨?_, (le_floor_sqrt_div_iff hx hm1 p.2).1 hsx⟩
          exact le_trans hm1
            (le_mul_of_one_le_left (Nat.zero_le _) (Nat.pos_of_ne_zero (pow_ne_zero 2 (by omega))))
        · obtain ⟨hm, hs⟩ := Finset.mem_sigma.1 hp
          obtain ⟨hm', hs'⟩ := Finset.mem_sigma.1 hp'
          have hs1 := (Finset.mem_Icc.1 hs).1
          have hs1' := (Finset.mem_Icc.1 hs').1
          obtain ⟨h1, h2⟩ := eq_and_eq_of_sq_mul_eq_sq_mul (by omega) (by omega)
            (Finset.mem_filter.1 hm).2 (Finset.mem_filter.1 hm').2 h
          exact Sigma.ext h1 (heq_of_eq h2)
        · obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.1 hn
          obtain ⟨a, b, ha, hb, hab, hasf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
          have hb1 : 1 ≤ b ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hb.ne')
          have han : a ≤ n := by
            rw [← hab]
            exact le_mul_of_one_le_left (Nat.zero_le a) hb1
          have hbx : b ^ 2 * a ≤ ⌊x⌋₊ := by
            rw [hab]
            exact hnx
          exact ⟨⟨a, b⟩, Finset.mem_sigma.2 ⟨Finset.mem_filter.2
            ⟨Finset.mem_Icc.2 ⟨ha, han.trans hnx⟩, hasf⟩,
            Finset.mem_Icc.2 ⟨hb, (le_floor_sqrt_div_iff hx ha b).2 hbx⟩⟩, hab⟩
        · obtain ⟨hm, hs⟩ := Finset.mem_sigma.1 hp
          obtain ⟨hmI, hmsf⟩ := Finset.mem_filter.1 hm
          obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
          have hm1 := (Finset.mem_Icc.1 hmI).1
          have hle := (le_floor_sqrt_div_iff hx hm1 p.2).1 hsx
          have hce := compMultExtension_sq_mul_eq (v := v) (by omega : p.2 ≠ 0) hmsf
            fun q hq hqs => hv q hq (by
              calc q ≤ p.2 := Nat.le_of_dvd (by omega) hqs
                _ ≤ p.2 ^ 2 := le_self_pow hs1 two_ne_zero
                _ ≤ p.2 ^ 2 * p.1 := le_mul_of_one_le_right (Nat.zero_le _) hm1
                _ ≤ ⌊x⌋₊ := hle)
          rw [hce]
    _ = ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter Squarefree,
          ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, squarefreeExtension v m * g (s ^ 2 * m) :=
        Finset.sum_sigma _ _ _
    _ = ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter Squarefree,
          squarefreeExtension v m * ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, g (s ^ 2 * m) :=
        Finset.sum_congr rfl fun m _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension v m
          * ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, g (s ^ 2 * m) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs with h
        · rfl
        · rw [squarefreeExtension_apply_of_not_squarefree v h, zero_mul]

/-! ### The harmonic remainder -/

/-- The remainder `r(T) = H(⌊T⌋) - log T` of the harmonic sum `∑_{s ≤ T} 1/s`. -/
noncomputable def harmonicRemainder (T : ℝ) : ℝ := (harmonic ⌊T⌋₊ : ℝ) - Real.log T

/-- `0 ≤ r(T) ≤ 1` for `T ≥ 1`: `log T ≤ H(⌊T⌋) ≤ 1 + log T` (`log_le_harmonic_floor`,
`harmonic_floor_le_one_add_log`). -/
lemma harmonicRemainder_mem_Icc {T : ℝ} (hT : 1 ≤ T) : harmonicRemainder T ∈ Set.Icc 0 1 := by
  have h1 := log_le_harmonic_floor T (by linarith)
  have h2 := harmonic_floor_le_one_add_log T hT
  rw [harmonicRemainder, Set.mem_Icc]
  constructor <;> linarith

/-- `0 ≤ r(√(x/n)) ≤ 1` on the range `1 ≤ n ≤ x` of the sums below. -/
lemma harmonicRemainder_sqrt_div_mem_Icc {x : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
    harmonicRemainder (Real.sqrt (x / n)) ∈ Set.Icc 0 1 := by
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hx1 : 1 ≤ x := Nat.floor_pos.1 (by omega)
  have hx : (n : ℝ) ≤ x := (Nat.cast_le.2 hnx).trans (Nat.floor_le (by linarith))
  refine harmonicRemainder_mem_Icc (Real.one_le_sqrt.2 ?_)
  rw [le_div_iff₀ hn0, one_mul]
  exact hx

/-- `∑_{s ≤ √(x/m)} 1/√(s²m) = m^{-1/2}(½ log(x/m) + r(√(x/m)))` for `m ≥ 1` and `x ≥ 0`. -/
lemma sum_inv_sqrt_sq_mul_eq {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 1 ≤ m) :
    ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, (Real.sqrt ((s ^ 2 * m : ℕ) : ℝ))⁻¹
      = (Real.sqrt m)⁻¹ * (1 / 2 * Real.log (x / m) + harmonicRemainder (Real.sqrt (x / m))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ s : ℕ, (Real.sqrt ((s ^ 2 * m : ℕ) : ℝ))⁻¹ = (Real.sqrt m)⁻¹ * (s : ℝ)⁻¹ := by
    intro s
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _),
      mul_inv, mul_comm]
  have hH : ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, (s : ℝ)⁻¹
      = (harmonic ⌊Real.sqrt (x / m)⌋₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.mul_sum, hH, harmonicRemainder,
    Real.log_sqrt (div_nonneg hx hm0.le)]
  ring

/-! ### The split `S^e = ½A + B` -/

/-- The Riesz mean `A(x) = ∑_{n≤x} f(n) n^{-1/2} log(x/n)`. -/
noncomputable def logWeightedSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n / (Real.sqrt n : ℂ) * (Real.log (x / n) : ℂ)

/-- The remainder sum `B(x) = ∑_{n≤x} f(n) n^{-1/2} r(√(x/n))`, `r = RMF.harmonicRemainder`. -/
noncomputable def harmonicRemainderSum (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n / (Real.sqrt n : ℂ) * (harmonicRemainder (Real.sqrt (x / n)) : ℂ)

/-- **The split of the weighted extended sum.**  Almost surely, for `x ≥ 1`,
`∑_{n≤x} X^e(n)/√n = ½A(x) + B(x)`: the square classes
(`RMF.sum_compMultExtension_mul_eq_sum_squarefreeExtension_mul_sum`) and
`∑_{s ≤ √(x/m)} 1/s = ½ log(x/m) + r(√(x/m))`. -/
theorem ae_weightedRademacherSum_compMultExtension_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    ∀ᵐ ω ∂μ, weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω
      = 1 / 2 * logWeightedSum (fun ω => squarefreeExtension fun p => X p ω) x ω
        + harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω := by
  have hx0 : 0 ≤ x := by linarith
  have hmeas : Measurable fun z : ℂ => z ^ 2 = 1 :=
    measurableSet_setOf.1 ((measurable_id.pow_const 2) (measurableSet_singleton 1))
  have hprimes : ∀ p ∈ Finset.Icc 1 ⌊x⌋₊, ∀ᵐ ω ∂μ, p.Prime → X p ω ^ 2 = 1 := by
    intro p _
    by_cases hp : p.Prime
    · filter_upwards [((hX.hasLaw p hp).ae_iff hmeas).2 sq_eq_one_rademacherLaw] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hp
  filter_upwards [(Filter.eventually_all_finset _).2 hprimes] with ω hω
  have hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → X p ω ^ 2 = 1 := fun p hp hpx =>
    hω p (Finset.mem_Icc.2 ⟨hp.one_lt.le, hpx⟩) hp
  have hL : weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          compMultExtension (fun p => X p ω) n * ((Real.sqrt n : ℂ))⁻¹ :=
    Finset.sum_congr rfl fun n _ => div_eq_mul_inv _ _
  rw [hL, sum_compMultExtension_mul_eq_sum_squarefreeExtension_mul_sum hx0 hv, logWeightedSum,
    harmonicRemainderSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hc : ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt (x / m)⌋₊, ((Real.sqrt ((s ^ 2 * m : ℕ) : ℝ) : ℂ))⁻¹
      = (((Real.sqrt m)⁻¹ * (1 / 2 * Real.log (x / m)
          + harmonicRemainder (Real.sqrt (x / m))) : ℝ) : ℂ) := by
    rw [← sum_inv_sqrt_sq_mul_eq hx0 (Finset.mem_Icc.1 hm).1]
    push_cast
    rfl
  rw [hc]
  push_cast
  ring

/-! ### `B` is small -/

omit [MeasurableSpace Ω] in
/-- `B(x) = ∑_{m≤x} c(m)f(m)` with `c(m) = r(√(x/m))/√m`. -/
lemma harmonicRemainderSum_eq_sum_mul (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    harmonicRemainderSum f x ω = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((harmonicRemainder (Real.sqrt (x / n)) / Real.sqrt n : ℝ) : ℂ) * f ω n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- **The mean square of `B`.**  For `x ≥ 1`,
`E|B(x)|² = ∑_{m≤x, squarefree} r(√(x/m))²/m ≤ ∑_{m≤x} 1/m ≤ 1 + log x`, by orthogonality
(`RMF.integral_normSq_weightedSum_of_orthogonality'`) and `0 ≤ r ≤ 1`. -/
theorem integral_normSq_harmonicRemainderSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ ω, ‖harmonicRemainderSum f x ω‖ ^ 2 ∂μ) ≤ 1 + Real.log x := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hne : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, n ≠ 0 := fun n hn =>
    Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hn).1
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ)
    (s := Finset.Icc 1 ⌊x⌋₊)
    (c := fun n : ℕ => ((harmonicRemainder (Real.sqrt (x / n)) / Real.sqrt n : ℝ) : ℂ))
    (d := fun m => ((if Squarefree m then 1 else 0 : ℝ) : ℂ))
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n
      · subst h
        by_cases hs : Squarefree m <;> simp [hs]
      · simp [h])
  simp_rw [← harmonicRemainderSum_eq_sum_mul, Complex.norm_real, Real.norm_eq_abs] at key
  have hreal : (∫ ω, ‖harmonicRemainderSum f x ω‖ ^ 2 ∂μ)
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, |harmonicRemainder (Real.sqrt (x / m)) / Real.sqrt m| ^ 2
          * (if Squarefree m then 1 else 0) := by
    exact_mod_cast key
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊x⌋₊,
      |harmonicRemainder (Real.sqrt (x / m)) / Real.sqrt m| ^ 2 * (if Squarefree m then 1 else 0)
        ≤ (m : ℝ)⁻¹ := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    obtain ⟨hr0, hr1⟩ := harmonicRemainder_sqrt_div_mem_Icc hm
    have hsq : |harmonicRemainder (Real.sqrt (x / m)) / Real.sqrt m| ^ 2
        = harmonicRemainder (Real.sqrt (x / m)) ^ 2 * (m : ℝ)⁻¹ := by
      rw [sq_abs, div_pow, Real.sq_sqrt hm0.le, div_eq_mul_inv]
    rw [hsq]
    have hr2 : harmonicRemainder (Real.sqrt (x / m)) ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
    split_ifs
    · rw [mul_one]
      exact mul_le_of_le_one_left (inv_nonneg.2 hm0.le) hr2
    · rw [mul_zero]
      exact inv_nonneg.2 hm0.le
  have hH : ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m : ℝ)⁻¹ = (harmonic ⌊x⌋₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [hreal]
  calc ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, |harmonicRemainder (Real.sqrt (x / m)) / Real.sqrt m| ^ 2
          * (if Squarefree m then 1 else 0)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (harmonic ⌊x⌋₊ : ℝ) := hH
    _ ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx

/-- `B(x)` is bounded, by `⌊x⌋`, so its moments are integrable. -/
lemma integrable_rpow_norm_harmonicRemainderSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω =>
      ‖harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hm : Measurable (harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x) :=
    Finset.measurable_sum _ fun n _ => ((hRa.measurable_apply n).div_const _).mul_const _
  refine (memLp_top_of_bound
    ((Real.continuous_rpow_const hr).measurable.comp hm.norm).aestronglyMeasurable
    ((⌊x⌋₊ : ℝ) ^ r) ?_).integrable le_top
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 ⌊x⌋₊)).2
    fun n _ => hRa.norm_apply_le_one n] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖squarefreeExtension (fun p => X p ω) n
      / (Real.sqrt n : ℂ) * (harmonicRemainder (Real.sqrt (x / n)) : ℂ)‖ ≤ 1 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    obtain ⟨hr0, hr1⟩ := harmonicRemainder_sqrt_div_mem_Icc hn
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 hn1
    have hq : ‖squarefreeExtension (fun p => X p ω) n‖ / Real.sqrt n ≤ 1 :=
      (div_le_one (by linarith)).2 (le_trans (hω n hn) hs1)
    exact mul_le_one₀ hq hr0 hr1
  refine Real.rpow_le_rpow (norm_nonneg _) (le_trans (norm_sum_le _ _) ?_) hr
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖squarefreeExtension (fun p => X p ω) n
          / (Real.sqrt n : ℂ) * (harmonicRemainder (Real.sqrt (x / n)) : ℂ)‖
      ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (⌊x⌋₊ : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

/-- **`B` is small.**  `E|B(x)|^{2q} ≤ (1 + log x)^q` for `x ≥ 1` and `0 ≤ q ≤ 1`: Jensen
(`RMF.integral_rpow_le_rpow_of_integral_le`) from the mean square. -/
theorem integral_rpow_norm_harmonicRemainderSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (1 + Real.log x) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hint : Integrable (fun ω =>
      ‖harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2) μ :=
    (integrable_rpow_norm_harmonicRemainderSum hX x (by norm_num : (0 : ℝ) ≤ 2)).congr
      (Filter.Eventually.of_forall fun ω => Real.rpow_two _)
  have hpow : ∀ ω,
      ‖harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        = (‖harmonicRemainderSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2) ^ q :=
    fun ω => by rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  simp_rw [hpow]
  exact integral_rpow_le_rpow_of_integral_le hq0 hq1
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint
    (integral_normSq_harmonicRemainderSum_le hX.isRademacherRMF hx)

end RMF
