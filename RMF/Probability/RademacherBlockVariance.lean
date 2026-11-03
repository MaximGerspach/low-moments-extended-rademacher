/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBlockMoments
import RMF.Probability.BlockComparison

/-!
# Pinning the Rademacher block variance

The block variance of `RMF/Probability/RademacherBlockMoments.lean` is `∑_{p ∈ B} (Re w p) ^ 2`.
Unlike the Steinhaus `∑ ‖w p‖ ^ 2 / 2`, it **depends on the height**, and this file is where that
dependence is paid for.

At `w p = p^{-u}` with `Re u = 1/2 + σ`, `RMF.localMean_prime_eq` splits each term:

`(Re p^{-u}) ^ 2 = p^{-1-2σ}/2 + cos(2 (Im u) log p) · p^{-1-2σ}/2`,

so the block variance is **half the block sum plus half an oscillatory prime sum**.  The first
half is pinned by `RMF.abs_sum_rpow_primeBlockSub_sub_one_le` exactly as in the Steinhaus case.
The second half has no Steinhaus counterpart, and is small only once the block is high enough:
it is at most `K / (τ e^{m+θ})` at frequency `τ = 2 Im u`.

**This is where Harper's `D(t)` is consumed.**  `τ e^{m+θ} ≥ Tsh` is exactly the height condition
`RMF.two_mul_exp_le_mul_exp_harperOffset_harperDt` supplies, uniformly in `t`, from a condition on
the base offset alone.  The first brackets take the cosine bound as a hypothesis `hcos`; it is
discharged at the end of the file.  `RMF.exists_abs_sum_cos_primeBlockSub_le` needs `τ ≤ 1`, which
covers `|Im u| ≤ 1/2` only; `RMF.exists_abs_sum_cos_primeBlockSub_le'` covers every `τ > 0` with
`τ ^ 2 ≤ e^{m+θ}`.
-/

open MeasureTheory
open scoped NNReal

namespace RMF

/-! ### The split -/

/-- **Each term of the Rademacher block variance splits in two.**  This is
`RMF.localMean_prime_eq` rearranged, with the exponent written in `σ`. -/
lemma re_cpow_neg_sq_eq {p : ℕ} (hp : p.Prime) {u : ℂ} {σ : ℝ} (hu : u.re = 1 / 2 + σ) :
    (((p : ℂ)) ^ (-u)).re ^ 2
      = (p : ℝ) ^ (-1 - 2 * σ) / 2
        + Real.cos (2 * u.im * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) / 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h := localMean_prime_eq hp u
  rw [norm_prime_cpow_neg_sq hp] at h
  have hre : (-2 : ℝ) * u.re = -1 - 2 * σ := by rw [hu]; ring
  have him : 2 * (u.im * Real.log p) = 2 * u.im * Real.log p := by ring
  rw [hre, him] at h
  have hbridge : Real.cos (2 * u.im * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)
      = (p : ℝ) ^ (-1 - 2 * σ) * Real.cos (2 * u.im * Real.log p) := by
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le, div_eq_mul_inv]
    ring
  rw [hbridge]
  linarith

/-- The block variance is half the block sum plus half the oscillatory sum. -/
lemma sum_re_cpow_neg_sq_primeBlockSub_eq (θ σ : ℝ) (m : ℕ) {u : ℂ} (hu : u.re = 1 / 2 + σ) :
    (∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2)
      = (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) / 2
        + (∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * u.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => re_cpow_neg_sq_eq p.2 hu

/-! ### The bracket -/

/-- **The Rademacher block variance is `1/2` up to the two errors.**

`(e^{2η} - 1) + e^{2η}·60/\log X` is the block sum's own deviation, the same error the Steinhaus
case pays.  `K` is the oscillatory sum, which is new, and which the height condition controls. -/
theorem abs_sum_re_cpow_neg_sq_primeBlockSub_sub_half_le (θ σ η K : ℝ) (m : ℕ) {u : ℂ}
    (hu : u.re = 1 / 2 + σ) (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ) (hη : 0 ≤ η)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hcos : |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * u.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| ≤ K) :
    |(∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2) - 1 / 2|
      ≤ ((Real.exp (2 * η) - 1)
          + Real.exp (2 * η) * (60 / Real.log (blockScale θ (m + 1))) + K) / 2 := by
  have hblock := abs_sum_rpow_primeBlockSub_sub_one_le θ σ η m hmθ hη hσ
  rw [sum_re_cpow_neg_sq_primeBlockSub_eq θ σ m hu]
  rw [abs_le] at hblock hcos ⊢
  constructor <;> linarith [hblock.1, hblock.2, hcos.1, hcos.2]

/-- **The two-sided bracket**, in the shape the Gaussian comparison consumes: the Rademacher block
variance lies in `[1/4, 3/4]` once the tilt is mild, the block is high, and the oscillatory sum is
small.  Each hypothesis has a supplier: `η ≤ 1/10` from the tilt scale at the top
(`RMF.sigma_le_mul_exp_sub`), `9 ≤ m + θ` from the block offset, and `K ≤ 1/10` from the block
cosine bound at a frequency the height condition keeps large. -/
theorem sum_re_cpow_neg_sq_primeBlockSub_bounds (θ σ η K : ℝ) (m : ℕ) {u : ℂ}
    (hu : u.re = 1 / 2 + σ) (hmθ : (9 : ℝ) ≤ (m : ℝ) + θ) (hη : 0 ≤ η) (hη' : η ≤ 1 / 10)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η) (hK : K ≤ 1 / 10)
    (hcos : |∑ p ∈ primeBlockSub θ m,
        Real.cos (2 * u.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)| ≤ K) :
    1 / 4 ≤ ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2
      ∧ (∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2) ≤ 3 / 4 := by
  have hmain := abs_sum_re_cpow_neg_sq_primeBlockSub_sub_half_le θ σ η K m hu (by linarith) hη
    hσ hcos
  -- `\log X = e^{m+1+θ} ≥ e^{10} ≥ 6000`, so the block-sum error is at most `60/6000`
  have hlog : Real.log (blockScale θ (m + 1)) = Real.exp ((m : ℝ) + 1 + θ) := by
    rw [blockScale, Real.log_exp]
    push_cast
    ring_nf
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h10 : (6000 : ℝ) ≤ Real.exp 10 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 10) (by norm_num) he1.le (by norm_num)
  have hL : (6000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [hlog]
    exact h10.trans (Real.exp_le_exp.2 (by linarith))
  have hL0 : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
  have hfrac : 60 / Real.log (blockScale θ (m + 1)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  -- `e^{2η} ≤ 1.3` because `(e^{2η})^5 = e^{10η} ≤ e` and `1.3^5 = 3.71 > e`
  have hexp : Real.exp (2 * η) ≤ 1.3 := by
    by_contra hcon
    rw [not_le] at hcon
    have h5 : Real.exp (2 * η) ^ 5 ≤ Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have hpow : (1.3 : ℝ) ^ 5 ≤ Real.exp (2 * η) ^ 5 :=
      pow_le_pow_left₀ (by norm_num) hcon.le 5
    nlinarith [Real.exp_one_lt_d9]
  have hexp0 : (0 : ℝ) < Real.exp (2 * η) := Real.exp_pos _
  have hprod : Real.exp (2 * η) * (60 / Real.log (blockScale θ (m + 1))) ≤ 1.3 / 100 := by
    have h0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by positivity
    nlinarith
  rw [abs_le] at hmain
  constructor <;> linarith [hmain.1, hmain.2]

/-! ### The bracket at zero height

The lemma above controls the oscillatory half of the variance through the height condition, and
so asks `0 < 2 Im u`.  At `Im u = 0` that hypothesis has no instances — and `Im u = 0` is exactly
the case the one-point wrapper needs, so it gets its own statement rather than a hypothesis
nothing can discharge.

There the local factor `p^{-u}` is real and positive, so `(Re p^{-u}) ² = p^{-1-2σ}` outright:
the variance **is** the block sum, with no cosine to control, and it lands near `1` rather than
near `1/2`.  Still inside the bracket the Gaussian comparison wants. -/

/-- At zero height the block variance is the block sum. -/
lemma sum_re_cpow_neg_sq_primeBlockSub_eq_of_im_zero (θ σ : ℝ) (m : ℕ) {u : ℂ}
    (hu : u.re = 1 / 2 + σ) (him : u.im = 0) :
    (∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2)
      = ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  rw [sum_re_cpow_neg_sq_primeBlockSub_eq θ σ m hu]
  have hcos : ∀ p ∈ primeBlockSub θ m,
      Real.cos (2 * u.im * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)
        = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p _ => by
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [him, show (2 : ℝ) * 0 * Real.log ((p : ℕ) : ℝ) = 0 by ring, Real.cos_zero,
      show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le, one_div]
  rw [Finset.sum_congr rfl hcos]
  ring

/-! ### Discharging the oscillatory bound

`RMF.exists_abs_cos_prime_sum_block_weight_le'` is stated over an interval; the block estimates
want it over `RMF.primeBlockSub`.  The bridge is the one
`RMF.exists_abs_sum_cos_primeBlockSub_le` uses, with the primed input; that lemma is not imported
here. -/

/-- **The block cosine sum past `τ = 1`.**  `|∑_{p ∈ block m} cos(τ log p) / p^{1+2σ}|
≤ K / (τ e^{m+θ})` for every `τ > 0` with `τ ^ 2 ≤ e^{m+θ}`, in place of the `τ ≤ 1` of
`RMF.exists_abs_sum_cos_primeBlockSub_le`. -/
theorem exists_abs_sum_cos_primeBlockSub_le' :
    ∃ K > 0, ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → 0 ≤ θ → τ ^ 2 ≤ Real.exp ((m : ℝ) + θ) →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ K / (τ * Real.exp ((m : ℝ) + θ)) := by
  obtain ⟨K₀, hK₀, h28⟩ := exists_abs_cos_prime_sum_block_weight_le'
  refine ⟨3 * K₀, by positivity, fun τ σ θ m hτ hθ hτ2 hσ => ?_⟩
  have hXpos : (0 : ℝ) < blockScale θ (m + 1) := blockScale_pos θ (m + 1)
  set y₁ : ℝ := blockScale θ (m + 1) ^ (Real.exp 1)⁻¹ with hy₁def
  have hlogX : Real.log (blockScale θ (m + 1)) = Real.exp (((m : ℝ) + 1) + θ) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hlogy₁ : Real.log y₁ = Real.exp ((m : ℝ) + θ) := by
    rw [hy₁def, Real.log_rpow hXpos, hlogX,
      show ((m : ℝ) + 1) + θ = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    field_simp
  have hy₁pos : (0 : ℝ) < y₁ := Real.rpow_pos_of_pos hXpos _
  have hexp1 : (1 : ℝ) ≤ Real.exp ((m : ℝ) + θ) := by
    rw [Real.one_le_exp_iff]
    positivity
  have hy₁e : Real.exp 1 ≤ y₁ := by
    rw [← Real.exp_log hy₁pos, hlogy₁]
    exact Real.exp_le_exp.2 hexp1
  have hy₁y₂ : y₁ ≤ blockScale θ (m + 1) := by
    rw [← Real.exp_log hy₁pos, ← Real.exp_log hXpos, hlogy₁, hlogX]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
  have hτ2' : τ ^ 2 ≤ Real.log y₁ := by rw [hlogy₁]; exact hτ2
  have hrw : (∑ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [primeBlockSub, harperBlock,
      sum_primesIcoSub _ _ fun q => Real.cos (τ * Real.log (q : ℝ)) / ((q : ℝ)) ^ (1 + 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  refine le_trans (h28 τ hτ σ y₁ (blockScale θ (m + 1)) hy₁e hτ2' hy₁y₂ hσ) ?_
  have hquot : Real.log (blockScale θ (m + 1) / y₁) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [Real.log_div hXpos.ne' hy₁pos.ne']
    have : (0 : ℝ) ≤ Real.log y₁ := by rw [hlogy₁]; positivity
    linarith
  have habs : (0 : ℝ) ≤ |σ| := abs_nonneg _
  have hnum : 1 + 2 * |σ| * Real.log (blockScale θ (m + 1) / y₁) ≤ 3 := by
    nlinarith [hσ, hquot, habs]
  have hden : (0 : ℝ) < τ * Real.log y₁ := by
    rw [hlogy₁]
    positivity
  rw [hlogy₁] at hden ⊢
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  linarith [mul_le_mul_of_nonneg_left hnum hK₀.le]

/-- **The bracket, with nothing left to supply.**  Past an absolute threshold on `τ e^{m+θ}` — the
height condition `RMF.two_mul_exp_le_mul_exp_harperOffset_harperDt` produces from a condition on
the base offset alone — the Rademacher block variance lies in `[1/4, 3/4]`.  The frequency is
`τ = 2 Im u`, twice the height; `RMF.exists_abs_sum_cos_primeBlockSub_le'` covers every height with
`(2 Im u) ^ 2 ≤ e^{m+θ}`. -/
theorem exists_sum_re_cpow_neg_sq_primeBlockSub_bounds :
    ∃ Tsh > 0, ∀ (θ σ η : ℝ) (m : ℕ) (u : ℂ),
      u.re = 1 / 2 + σ → (9 : ℝ) ≤ (m : ℝ) + θ → 0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * u.im → (2 * u.im) ^ 2 ≤ Real.exp ((m : ℝ) + θ) →
      Tsh ≤ 2 * u.im * Real.exp ((m : ℝ) + θ) →
      1 / 4 ≤ ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2
        ∧ (∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2) ≤ 3 / 4 := by
  obtain ⟨K, hK, hcosbd⟩ := exists_abs_sum_cos_primeBlockSub_le'
  refine ⟨10 * K, by positivity, ?_⟩
  intro θ σ η m u hu hmθ hθ hη hη' hσ hτ hτ2 hTsh
  have hcos := hcosbd (2 * u.im) σ θ m hτ hθ hτ2 (by linarith)
  have hprod : (0 : ℝ) < 2 * u.im * Real.exp ((m : ℝ) + θ) := by positivity
  have hsmall : K / (2 * u.im * Real.exp ((m : ℝ) + θ)) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hprod (by norm_num)]
    linarith
  exact sum_re_cpow_neg_sq_primeBlockSub_bounds θ σ η (1 / 10) m hu hmθ hη hη' hσ le_rfl
    (hcos.trans hsmall)

end RMF
