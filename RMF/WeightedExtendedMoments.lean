/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.WeightedExtended.Moments
import RMF.Weighted.PaperCorollaries

/-!
# Proposition 1.5 of the paper: the weighted extended sum

The paper, Proposition 1.5: *let `0 ≤ q ≤ ½` be fixed.  Uniformly for `x ≥ 3`,
`E|∑_{n≤x} X^e(n)/√n|^{2q} ≪ (log x)^{q(2q+1)}`, and as `x → ∞`,
`(log x)⁻¹∑_{n≤x, n≠□} X^e(n)/√n → -½` in probability.*  Here `X^e` is the completely
multiplicative extension of the Rademacher signs.

* The moments (`RMF.weighted_extended_rademacher_moments`), with a constant depending on `q`
  only, not on the probability space: `RMF.weighted_extended_rademacher_moments_uniform` gives
  `C(1 + q⁻²)` for `0 < q ≤ ½`, and `q = 0` is `E|S|⁰ = 1`.
* The limit (`RMF.weighted_extended_rademacher_nonsquare_tendstoInMeasure`): almost surely the
  squares contribute `∑_{s≤√x} 1/s = ½log x + r(√x)` with `0 ≤ r ≤ 1`
  (`RMF.ae_sum_isSquare_compMultExtension_div_sqrt`), and `(log x)⁻¹∑_{n≤x} X^e(n)/√n → 0` by
  Markov from the moments at `q = ¼`.  "`n ≠ □`" is `¬IsSquare n` and convergence in probability
  is `MeasureTheory.TendstoInMeasure` along `x → ∞` in `ℝ`, as in Corollary 1.4
  (`RMF/Weighted/PaperCorollaries.lean`).
-/

open MeasureTheory Filter Topology

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The squares -/

/-- **The squares, with a weight.**  If `v(p)² = 1` at the primes `p ≤ x`, then
`∑_{n≤x, n = □} v^e(n)g(n) = ∑_{s≤√x} g(s²)`: the weighted form of
`RMF.sum_isSquare_compMultExtension_eq`, by the same reindexing. -/
lemma sum_isSquare_compMultExtension_mul_eq {v : ℕ → ℂ} {x : ℝ} (hx : 0 ≤ x)
    (hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → v p ^ 2 = 1) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsSquare n, compMultExtension v n * g n
      = ∑ s ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, g (s ^ 2) := by
  have key : ∀ s : ℕ, s ≤ ⌊Real.sqrt x⌋₊ ↔ s ^ 2 ≤ ⌊x⌋₊ := fun s => by
    simpa using le_floor_sqrt_div_iff hx one_pos s
  symm
  refine Finset.sum_bij (fun s _ => s ^ 2) (fun s hs => ?_) (fun s _ s' _ h => ?_)
    (fun n hn => ?_) (fun s hs => ?_)
  · obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hs1, (key s).1 hsx⟩,
      ⟨s, sq s⟩⟩
  · exact Nat.pow_left_injective two_ne_zero h
  · obtain ⟨hnI, r, hr⟩ := Finset.mem_filter.1 hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.1 hnI
    have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      simp at hr
      omega
    exact ⟨r, Finset.mem_Icc.2 ⟨hr1, (key r).2 (by rw [sq, ← hr]; exact hnx)⟩,
      by rw [sq, hr]⟩
  · obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
    have hle := (key s).1 hsx
    have h := compMultExtension_sq_mul_eq (v := v) (m := 1) (by omega) squarefree_one
      fun p hp hps => hv p hp ((Nat.le_of_dvd (by omega) hps).trans
        ((le_self_pow hs1 two_ne_zero).trans hle))
    rw [mul_one, squarefreeExtension_apply_one] at h
    rw [h, one_mul]

/-- **The squares carry the harmonic number.**  Almost surely, for `x ≥ 0`,
`∑_{n≤x, n = □} X^e(n)/√n = ∑_{s≤√x} 1/s = H(⌊√x⌋)`, as `X^e(s²) = 1`
(`RMF.sum_isSquare_compMultExtension_mul_eq` at `g(n) = n^{-1/2}`). -/
lemma ae_sum_isSquare_compMultExtension_div_sqrt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 0 ≤ x) :
    ∀ᵐ ω ∂μ, ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsSquare n,
        compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)
      = ((harmonic ⌊Real.sqrt x⌋₊ : ℝ) : ℂ) := by
  have hsq : ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), X p ω ^ 2 = 1 :=
    (Filter.eventually_all_finset _).2 fun p hp =>
      ae_sq_X_eq_one hX (Nat.prime_of_mem_primesBelow hp)
  filter_upwards [hsq] with ω hω
  have hS := sum_isSquare_compMultExtension_mul_eq (v := fun p => X p ω) hx
    (fun p hp hpx => hω p (Nat.mem_primesBelow.2 ⟨by omega, hp⟩))
    (fun n => ((Real.sqrt n : ℝ) : ℂ)⁻¹)
  beta_reduce at hS
  simp only [div_eq_mul_inv]
  rw [hS, harmonic_eq_sum_Icc]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.sqrt_sq (Nat.cast_nonneg s), Complex.ofReal_natCast]

/-! ### Proposition 1.5 -/

/-- **Proposition 1.5 of the paper, the moments.**  The paper: *let `0 ≤ q ≤ ½` be fixed.
Uniformly for `x ≥ 3`, `E|∑_{n≤x} X^e(n)/√n|^{2q} ≪ (log x)^{q(2q+1)}`.*  Here with `C`
depending on `q` only, not on the probability space: `C(1 + q⁻²)` from
`RMF.weighted_extended_rademacher_moments_uniform` for `q > 0`, and `1` at `q = 0`. -/
theorem weighted_extended_rademacher_moments (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
          (∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ) ≤ C * Real.log x ^ (q * (2 * q + 1)) := by
  rcases eq_or_lt_of_le hq0 with h0 | hq0'
  · subst h0
    refine ⟨1, one_pos, fun Ω _ X μ hX x _ => ?_⟩
    haveI := hX.isProbabilityMeasure
    simp
  obtain ⟨C, hC, H⟩ := weighted_extended_rademacher_moments_uniform
  exact ⟨C * (1 + (q ^ 2)⁻¹), by positivity, fun Ω _ X μ hX x hx => H Ω X μ hX x q hx hq0' hq1⟩

/-- **Proposition 1.5 of the paper, the limit.**  The paper: *as `x` tends to infinity,
`(log x)⁻¹∑_{n≤x, n≠□} X^e(n)/√n → -½` in probability.*  Here "`n ≠ □`" is `¬IsSquare n` and
convergence in probability is `MeasureTheory.TendstoInMeasure` along `x → ∞` in `ℝ`.  The squares
contribute `H(⌊√x⌋) = ½log x + r(√x)`, `0 ≤ r ≤ 1`
(`RMF.ae_sum_isSquare_compMultExtension_div_sqrt`, `RMF.harmonicRemainder_mem_Icc`), and
`E|(log x)⁻¹∑_{n≤x}X^e(n)/√n|^{1/2} ≤ C(log x)^{-1/8}` by
`RMF.weighted_extended_rademacher_moments` at `q = ¼`. -/
theorem weighted_extended_rademacher_nonsquare_tendstoInMeasure :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
        TendstoInMeasure μ
          (fun (x : ℝ) ω => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n,
            compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)) / (Real.log x : ℂ))
          atTop (fun _ => -(1 / 2)) := by
  intro Ω _ X μ hX
  haveI := hX.isProbabilityMeasure
  obtain ⟨C, -, H⟩ := weighted_extended_rademacher_moments (1 / 4) (by norm_num) (by norm_num)
  have hb : Tendsto (fun x : ℝ => C * Real.log x ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      Real.tendsto_log_atTop).const_mul C
    rw [mul_zero] at h
    exact h
  refine tendstoInMeasure_of_norm_sub_le_add
    (Z := fun x ω => weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω
      / (Real.log x : ℂ))
    (b := fun x => C * Real.log x ^ (-(1 / 8 : ℝ)))
    (δ := fun x => (Real.log x)⁻¹) (r := 1 / 2) (by norm_num)
    (Filter.Eventually.of_forall fun x => ?_) ?_ hb ?_
    (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
  · -- each `|(log x)⁻¹S^e(x)|^{1/2}` is integrable
    refine ((integrable_rpow_norm_weightedRademacherSum_compMultExtension hX x
      (r := 1 / 2) (by norm_num)).div_const (‖(Real.log x : ℂ)‖ ^ (1 / 2 : ℝ))).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  · -- the moment at `q = ¼`
    filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hm := H Ω X μ hX x hx
    rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
      show (1 / 4 : ℝ) * (1 / 2 + 1) = 3 / 8 by norm_num] at hm
    have hpt : ∀ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω
        / (Real.log x : ℂ)‖ ^ (1 / 2 : ℝ)
        = ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
          ^ (1 / 2 : ℝ) / Real.log x ^ (1 / 2 : ℝ) := fun ω => by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hL0.le,
        Real.div_rpow (norm_nonneg _) hL0.le]
    simp only [hpt]
    rw [integral_div]
    calc (∫ ω, ‖weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω‖
          ^ (1 / 2 : ℝ) ∂μ) / Real.log x ^ (1 / 2 : ℝ)
        ≤ C * Real.log x ^ (3 / 8 : ℝ) / Real.log x ^ (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_right hm (Real.rpow_nonneg hL0.le _)
      _ = C * Real.log x ^ (-(1 / 8 : ℝ)) := by
          rw [mul_div_assoc, ← Real.rpow_sub hL0]
          norm_num
  · -- pathwise: the squares contribute `½ log x + r(√x)`
    filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hr := harmonicRemainder_mem_Icc (Real.one_le_sqrt.2 (by linarith : (1 : ℝ) ≤ x))
    have hH : (harmonic ⌊Real.sqrt x⌋₊ : ℝ)
        = harmonicRemainder (Real.sqrt x) + Real.log x / 2 := by
      rw [harmonicRemainder, Real.log_sqrt (by linarith)]
      ring
    have habs : |1 / 2 - (harmonic ⌊Real.sqrt x⌋₊ : ℝ) / Real.log x| ≤ (Real.log x)⁻¹ := by
      rw [hH]
      have e : 1 / 2 - (harmonicRemainder (Real.sqrt x) + Real.log x / 2) / Real.log x
          = -(harmonicRemainder (Real.sqrt x) * (Real.log x)⁻¹) := by
        field_simp
        ring
      rw [e, abs_neg, abs_of_nonneg (mul_nonneg hr.1 (inv_nonneg.2 hL0.le))]
      exact mul_le_of_le_one_left (inv_nonneg.2 hL0.le) hr.2
    filter_upwards [ae_sum_isSquare_compMultExtension_div_sqrt hX (by linarith : (0 : ℝ) ≤ x)]
      with ω hω
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) IsSquare
      (fun n => compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ))
    beta_reduce at hsplit
    rw [hω] at hsplit
    have hS : weightedRademacherSum (fun ω => compMultExtension fun p => X p ω) x ω
        = ((harmonic ⌊Real.sqrt x⌋₊ : ℝ) : ℂ)
          + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n,
            compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ) := hsplit.symm
    rw [hS]
    generalize (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n,
      compMultExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)) = N
    have e : N / (Real.log x : ℂ) - -(1 / 2)
        = (((harmonic ⌊Real.sqrt x⌋₊ : ℝ) : ℂ) + N) / (Real.log x : ℂ)
          + ((1 / 2 - (harmonic ⌊Real.sqrt x⌋₊ : ℝ) / Real.log x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

end RMF
