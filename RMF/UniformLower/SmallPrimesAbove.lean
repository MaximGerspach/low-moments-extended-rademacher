/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.DecompositionQ

/-!
# The small primes above `q = ½`

For `q ≤ 1` and `σ ≥ 0`, the twisted weight of the numerator at exponent `q` dominates the
real-point moment: `E‖F_{[a,b)}(σ)‖^{2q} ≤ E[‖F_{[a,b)}(σ+ih)‖²‖F_{[a,b)}(σ)‖^{2q-2}]`
(`RMF.integral_rpow_norm_randomEulerProductIco_le_twistQ`), prime by prime: with
`u = p^{-1/2-σ}`, `v = p^{-1/2-σ-ih}` and `d = 1 - cos(h log p)`,
`E[|1+Xv|²|1+Xu|^{2q-2}] = E|1+Xu|^{2q} + ud((1-u)^{2q-2} - (1+u)^{2q-2}) ≥ E|1+Xu|^{2q}`
(`RMF.integral_rpow_rademacherLaw_le_twistQ`).  The skeleton of (C3)*,
`RMF.le_setIntegral_halfLadder_twistQ_ville`, applies it on both sides of the cut.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Below the cut: one prime, and the product -/

/-- **One prime, below the cut**: `E‖1+zp^{-σ}‖^{2q} ≤ E[‖1+zp^{-(σ+ih)}‖²‖1+zp^{-σ}‖^{2q-2}]` for
`q ≤ 1`, `σ ≥ 0` and `p ≥ 2`. -/
lemma integral_rpow_rademacherLaw_le_twistQ {p : ℕ} (hp : 2 ≤ p) {σ h q : ℝ} (hσ : 0 ≤ σ)
    (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q) ∂rademacherLaw)
      ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
          * ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q - 2) ∂rademacherLaw := by
  have hp0 : 0 < p := by omega
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu_def
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hu0 : 0 ≤ u := Real.rpow_nonneg hpR.le _
  have hu1 : u < 1 := rpow_neg_half_add_lt_one hp hσ
  have hnorm : ∀ h : ℝ, ‖(p : ℂ) ^ (-shiftLine σ h)‖ = u := fun h =>
    norm_cpow_neg_shiftLine hp0 σ h
  have hre : ∀ h : ℝ, ((p : ℂ) ^ (-shiftLine σ h)).re = u * Real.cos (h * Real.log p) :=
    fun h => re_cpow_neg_shiftLine hp0 σ h
  have hpos : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      = (1 + u) ^ 2 - 2 * u * (1 - Real.cos (h * Real.log p)) := by
    rw [norm_one_add_mul_sq_eq (by simp), one_mul, hre h, hnorm h]
    ring
  have hneg : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      = (1 - u) ^ 2 + 2 * u * (1 - Real.cos (h * Real.log p)) := by
    have hrew : ((-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)).re
        = -((p : ℂ) ^ (-shiftLine σ h)).re := by simp
    rw [norm_one_add_mul_sq_eq (by simp), hnorm h, hrew, hre h]
    ring
  have hw0 : (p : ℂ) ^ (-shiftLine σ 0) = ((u : ℝ) : ℂ) := cpow_neg_shiftLine_zero p σ
  have hn1 : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 + u := by
    rw [one_mul, hw0, show (1 : ℂ) + ((u : ℝ) : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 - u := by
    rw [hw0, show (1 : ℂ) + (-1) * ((u : ℝ) : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [integral_rademacherLaw_eq, integral_rademacherLaw_eq]
  simp only [smul_eq_mul]
  rw [hpos, hneg, hn1, hn2]
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  have hsq : ∀ {v : ℝ}, 0 < v → v ^ 2 * v ^ (2 * q - 2) = v ^ (2 * q) := by
    intro v hv
    rw [← Real.rpow_natCast, ← Real.rpow_add hv]
    congr 1
    push_cast
    ring
  have hd : 0 ≤ 1 - Real.cos (h * Real.log p) := by linarith [Real.cos_le_one (h * Real.log p)]
  have hmono : (1 + u) ^ (2 * q - 2) ≤ (1 - u) ^ (2 * q - 2) :=
    Real.rpow_le_rpow_of_nonpos h2 (by linarith) (by linarith)
  have hexp : ((1 + u) ^ 2 - 2 * u * (1 - Real.cos (h * Real.log p))) * (1 + u) ^ (2 * q - 2)
      + ((1 - u) ^ 2 + 2 * u * (1 - Real.cos (h * Real.log p))) * (1 - u) ^ (2 * q - 2)
      = (1 + u) ^ (2 * q) + (1 - u) ^ (2 * q)
        + 2 * u * (1 - Real.cos (h * Real.log p))
          * ((1 - u) ^ (2 * q - 2) - (1 + u) ^ (2 * q - 2)) := by
    rw [← hsq h1, ← hsq h2]
    ring
  rw [hexp]
  have hextra : 0 ≤ 2 * u * (1 - Real.cos (h * Real.log p))
      * ((1 - u) ^ (2 * q - 2) - (1 + u) ^ (2 * q - 2)) :=
    mul_nonneg (mul_nonneg (by linarith) hd) (by linarith)
  nlinarith [hextra]

omit [MeasurableSpace Ω] in
/-- The twist at exponent `q`, as a product over the primes. -/
lemma twistQ_eq_prod {X : ℕ → Ω → ℂ} (a b : ℕ) (σ h q : ℝ) (ω : Ω) :
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ ^ (2 * q - 2)
      = ∏ p ∈ primesIco a b, (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
          * ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q - 2)) := by
  rw [randomEulerProductIco_sqfree_eq, randomEulerProductIco_sqfree_eq, norm_prod, norm_prod,
    ← Finset.prod_pow, ← Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg _),
    ← Finset.prod_mul_distrib]

/-- **Below the cut**: `E‖F_{[a,b)}(σ)‖^{2q} ≤ E[‖F_{[a,b)}(σ+ih)‖²‖F_{[a,b)}(σ)‖^{2q-2}]` for
`q ≤ 1` and `σ ≥ 0`, prime by prime. -/
theorem integral_rpow_norm_randomEulerProductIco_le_twistQ {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ h q : ℝ} (hσ : 0 ≤ σ) (hq1 : q ≤ 1) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  classical
  have hSp : ∀ p ∈ primesIco a b, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hbase : ∀ c : ℂ, Measurable fun z : ℂ => ‖1 + z * c‖ :=
    fun c => (measurable_const.add (measurable_id.mul measurable_const)).norm
  rw [integral_congr_ae (Filter.Eventually.of_forall
      (rpow_norm_randomEulerProductIco_eq_prod (X := X) a b (shiftLine σ 0) (2 * q))),
    integral_congr_ae (Filter.Eventually.of_forall (twistQ_eq_prod (X := X) a b σ h q)),
    hX.integral_prod hSp (fun p z => ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q))
      fun p _ => ((hbase _).pow_const _).aestronglyMeasurable,
    hX.integral_prod hSp (fun p z => ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
        * ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q - 2))
      fun p _ => (((hbase _).pow_const 2).mul ((hbase _).pow_const _)).aestronglyMeasurable]
  refine Finset.prod_le_prod (fun p _ => integral_nonneg fun z => Real.rpow_nonneg
    (norm_nonneg _) _) fun p hp => ?_
  exact integral_rpow_rademacherLaw_le_twistQ (hSp p hp).two_le hσ hq1

end RMF
