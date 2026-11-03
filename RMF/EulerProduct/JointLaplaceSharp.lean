/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.JointLaplaceExplicit

/-!
# The joint Laplace transform on the primes above a threshold

The local constants of `RMF/EulerProduct/JointLaplaceExplicit.lean` bound the local expansion
error `|log E_z(…) - main|` by `C·p^{-3σ}` uniformly in the prime; summed over **all** primes,
that pays for `p = 2, 3, …` at the worst local constant, and `RMF.localMultiLogConst` is
exponential in the Laplace parameter.  At Harper's block scales every prime is at least
`exp(e^{ϑ})`, and there the same per-prime bound sums to almost nothing.  This file keeps the
local constants and sums only over `y₀ ≤ p`:

* `RMF.sum_primesIco_rpow_le_tail`: `∑_{y₀ ≤ p < y} p^{-3σ} ≤ y₀^{-3δ} ∑_n n^{-3(σ₀-δ)}`;
* `RMF.multiTailConst`, `RMF.multi_prime_sum_tail_le`: the multi-weight expansion over `[y₀, y)`,
  with error `multiTailConst·y₀^{-3(σ₀-1/3)/2}`;
* `RMF.pairTailConst`, `RMF.pair_prime_sum_tail_le`: the same for the pair expansion;
* `RMF.IsSteinhausRMF.measure_le_exp_of_log_le`: Markov against a bound on the log-moment;
* `RMF.IsSteinhausRMF.measure_ge_le_gaussian_tail`: the one-point Gaussian tail, with the tail
  error.  One link of the chain is `RMF.IsSteinhausRMF.measure_link_le_tail`, in
  `Probability/ChainingSharp`, where the abscissas `RMF.heightLine` live.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {ι : Type*}

/-! ### The prime sums above a threshold -/

/-- **The cube prime sum above `y₀` decays in `y₀`**: `∑_{y₀ ≤ p < y} p^{-3σ}` is at most
`y₀^{-3δ} ∑_n n^{-3(σ₀-δ)}`, for `0 ≤ δ` with `σ₀ - δ > 1/3`. -/
lemma sum_primesIco_rpow_le_tail {σ₀ σ δ : ℝ} (hδ : 0 ≤ δ) (hσ₀δ : 1 / 3 < σ₀ - δ) (hσ : σ₀ ≤ σ)
    {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ) :
    ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * σ)
      ≤ (y₀ : ℝ) ^ (-3 * δ) * ∑' n : ℕ, (n : ℝ) ^ (-3 * (σ₀ - δ)) := by
  have hy₀R : (0 : ℝ) < (y₀ : ℝ) := by exact_mod_cast hy₀
  have hstep : ∀ p ∈ primesIco y₀ y,
      (p : ℝ) ^ (-3 * σ) ≤ (y₀ : ℝ) ^ (-3 * δ) * (p : ℝ) ^ (-3 * (σ - δ)) := by
    intro p hp
    have hyp : y₀ ≤ p := (mem_primesIco.1 hp).2.1
    have hyR : (y₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hyp
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hy₀R hyR
    rw [show -3 * σ = -3 * δ + -3 * (σ - δ) by ring, Real.rpow_add hp0]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hy₀R hyR (by linarith)) (Real.rpow_nonneg hp0.le _)
  calc ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * σ)
      ≤ ∑ p ∈ primesIco y₀ y, (y₀ : ℝ) ^ (-3 * δ) * (p : ℝ) ^ (-3 * (σ - δ)) :=
        Finset.sum_le_sum hstep
    _ = (y₀ : ℝ) ^ (-3 * δ) * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * (σ - δ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (y₀ : ℝ) ^ (-3 * δ) * ∑' n : ℕ, (n : ℝ) ^ (-3 * (σ₀ - δ)) :=
        mul_le_mul_of_nonneg_left (sum_primesIco_rpow_le hσ₀δ (by linarith) y₀ y)
          (Real.rpow_nonneg hy₀R.le _)

/-- A tail `C·y^{-ε}` is at most `1` once `y ≥ C^{1/ε}`. -/
lemma mul_rpow_neg_le_one_of_le {C ε y : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hy : C ^ ε⁻¹ ≤ y) :
    C * y ^ (-ε) ≤ 1 := by
  rcases hC.eq_or_lt with h0 | hCpos
  · rw [← h0, zero_mul]
    norm_num
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hCpos _) hy
  have hpow : C ≤ y ^ ε := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hC _) hy hε.le
    rwa [Real.rpow_inv_rpow hC hε.ne'] at h
  rw [Real.rpow_neg hy0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hy0 _)]
  exact hpow

/-! ### The multi-weight expansion above a threshold -/

/-- **The multi-weight expansion's tail constant**: `C₁ ∑_k k^{-3σ₁}`, with
`C₁ = localMultiLogConst Q 2^{-σ₀} n` and `σ₁ = (σ₀+1/3)/2`. -/
noncomputable def multiTailConst (Q σ₀ : ℝ) (n : ℕ) : ℝ :=
  localMultiLogConst Q ((2 : ℝ) ^ (-σ₀)) n * ∑' k : ℕ, (k : ℝ) ^ (-3 * ((σ₀ + 1 / 3) / 2))

lemma multiTailConst_nonneg (A : Finset ι) {Q σ₀ : ℝ} (hQ0 : 0 ≤ Q) (hσ₀ : 1 / 3 < σ₀) :
    0 ≤ multiTailConst Q σ₀ A.card := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hC₁, -⟩ := exists_abs_log_local_multi_le_explicit A hQ0 hθ0 hθ
  exact mul_nonneg hC₁.le (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **The multi-weight expansion over the primes in `[y₀, y)`**, with error
`multiTailConst Q σ₀ |A| · y₀^{-3(σ₀-1/3)/2}`. -/
theorem multi_prime_sum_tail_le (A : Finset ι) {Q σ₀ : ℝ} (hQ0 : 0 ≤ Q) (hσ₀ : 1 / 3 < σ₀)
    {q : ι → ℝ} {s : ι → ℂ} {σ : ℝ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ)
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hs : ∀ a ∈ A, (s a).re = σ) (hσ : σ₀ ≤ σ) :
    |Real.log (∏ p ∈ primesIco y₀ y,
          ∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
        - ∑ p ∈ primesIco y₀ y, ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2|
      ≤ multiTailConst Q σ₀ A.card * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2)) := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hC₁, hloc⟩ := exists_abs_log_local_multi_le_explicit A hQ0 hθ0 hθ
  set C₁ := localMultiLogConst Q ((2 : ℝ) ^ (-σ₀)) A.card with hC₁_expl
  -- every abscissa has real part `σ`, so every weight has modulus `p ^ (-σ)`
  have hnorm : ∀ p ∈ primesIco y₀ y, ∀ a ∈ A,
      ‖((p : ℂ)) ^ (-s a)‖ = (p : ℝ) ^ (-σ) := by
    intro p hp a ha
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos,
      Complex.neg_re, hs a ha]
  have hle : ∀ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpos : ∀ p ∈ primesIco y₀ y,
      0 < ∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw := by
    intro p hp
    exact integral_prod_localIntegrand_pos (Q := Q) hq
      (fun a ha => le_trans (le_of_eq (hnorm p hp a ha)) (hle p hp)) hθ
  have hterm : ∀ p ∈ primesIco y₀ y,
      |Real.log (∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
          - ‖∑ a ∈ A, (q a : ℂ) * (p : ℂ) ^ (-s a)‖ ^ 2|
        ≤ C₁ * (p : ℝ) ^ (-3 * σ) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).pos
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
    have h := hloc q (fun a => (p : ℂ) ^ (-s a)) ((p : ℝ) ^ (-σ)) hq
      (fun a ha => le_of_eq (hnorm p hp a ha)) ht0 (hle p hp)
    have hcube : ((p : ℝ) ^ (-σ)) ^ 3 = (p : ℝ) ^ (-3 * σ) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 3, ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    rwa [hcube] at h
  have hmain := abs_log_prod_sub_sum_le hpos hterm
  refine le_trans hmain ?_
  have htail := sum_primesIco_rpow_le_tail (σ₀ := σ₀) (σ := σ) (δ := (σ₀ - 1 / 3) / 2)
    (by linarith) (by linarith) hσ hy₀ y
  rw [show σ₀ - (σ₀ - 1 / 3) / 2 = (σ₀ + 1 / 3) / 2 by ring] at htail
  calc C₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * σ)
      ≤ C₁ * ((y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2))
          * ∑' n : ℕ, (n : ℝ) ^ (-3 * ((σ₀ + 1 / 3) / 2))) :=
        mul_le_mul_of_nonneg_left htail hC₁.le
    _ = multiTailConst Q σ₀ A.card * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2)) := by
        rw [multiTailConst]
        ring

/-! ### The pair expansion above a threshold -/

/-- **The pair expansion's tail constant**: `C₁K³∑_n n^{-3σ₂}`, with `C₁ = localPairConst 2^{-σ₀}`,
`δ = (σ₀-1/3)/2`, `K = 1 + Λ/2 + Λ/(2δ)`, `σ₁ = (σ₀+1/3)/2` and `σ₂ = (σ₁+1/3)/2`. -/
noncomputable def pairTailConst (σ₀ Λ : ℝ) : ℝ :=
  localPairConst ((2 : ℝ) ^ (-σ₀)) * (1 + Λ / 2 + Λ / 2 / ((σ₀ - 1 / 3) / 2)) ^ 3
    * ∑' n : ℕ, (n : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 + 1 / 3) / 2))

lemma pairTailConst_nonneg {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    0 ≤ pairTailConst σ₀ Λ := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hC₁, -⟩ := exists_abs_log_local_pair_le_explicit hθ0 hθ
  have hδ : (0 : ℝ) < (σ₀ - 1 / 3) / 2 := by linarith
  have hT : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 + 1 / 3) / 2)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [pairTailConst]
  positivity

/-- **The pair expansion over the primes in `[y₀, y)`**, with error
`pairTailConst σ₀ Λ · y₀^{-3(σ₁-1/3)/2}`, `σ₁ = (σ₀+1/3)/2`. -/
theorem pair_prime_sum_tail_le {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ)
    {l₁ l₂ σ h₁ h₂ : ℝ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hσ : σ₀ ≤ σ) (hl₁Λ : l₁ ≤ Λ) (hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ) :
    |Real.log (∏ p ∈ primesIco y₀ y, ∫ z, ∏ a,
          ‖(1 - z * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a))⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
          ∂steinhausLaw)
        - ∑ p ∈ primesIco y₀ y, ‖∑ a,
            (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2|
      ≤ pairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hC₁, hloc⟩ := exists_abs_log_local_pair_le_explicit hθ0 hθ
  set C₁ := localPairConst ((2 : ℝ) ^ (-σ₀)) with hC₁_expl
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (σ₀ - 1 / 3) / 2 := ⟨_, rfl⟩
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; linarith
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = (σ₀ + 1 / 3) / 2 := ⟨_, rfl⟩
  have hσ₁1 : 1 / 3 < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁δ : σ₀ - δ = σ₁ := by rw [hδdef, hσ₁def]; ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + Λ / 2 + Λ / 2 / δ := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hnorm : ∀ p ∈ primesIco y₀ y, ∀ a : Fin 3,
      ‖((p : ℂ)) ^ (-pairAbscissa σ h₁ h₂ a)‖ = (p : ℝ) ^ (-σ) := by
    intro p hp a
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos,
      Complex.neg_re, pairAbscissa_re]
  have hle : ∀ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hincr : ∀ p ∈ primesIco y₀ y,
      ‖(p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 1) - (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ 2)‖
        ≤ (p : ℝ) ^ (-σ) * (|h₁ - h₂| * Real.log p) := by
    intro p hp
    have h := norm_natCast_cpow_neg_sub_le (prime_of_mem_primesIco hp).pos
      (s₁ := pairAbscissa σ h₁ h₂ 1) (s₂ := pairAbscissa σ h₁ h₂ 2) (σ := σ)
      (pairAbscissa_re σ h₁ h₂ 1) (pairAbscissa_re σ h₁ h₂ 2)
    rwa [pairAbscissa_im_one, pairAbscissa_im_two] at h
  have hpos : ∀ p ∈ primesIco y₀ y, 0 < ∫ z, ∏ a,
      ‖(1 - z * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a))⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂steinhausLaw := by
    intro p hp
    have hwlt : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        ‖(p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ < 1 := fun a _ => by
      rw [hnorm p hp a]
      exact lt_of_le_of_lt (hle p hp) hθ
    refine integral_prod_localIntegrand_pos_of_bound hwlt fun z hz =>
      abs_logExponent_pairWeight_le (θ := (p : ℝ) ^ (-σ))
        (d := |h₁ - h₂| * Real.log p) hz hl₁ hl₂ (lt_of_le_of_lt (hle p hp) hθ)
        (le_of_eq (hnorm p hp 0)) (le_of_eq (hnorm p hp 1)) (le_of_eq (hnorm p hp 2))
        (hincr p hp)
  have hterm : ∀ p ∈ primesIco y₀ y,
      |Real.log (∫ z, ∏ a,
            ‖(1 - z * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a))⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
            ∂steinhausLaw)
          - ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)‖ ^ 2|
        ≤ C₁ * K ^ 3 * (p : ℝ) ^ (-3 * (σ - δ)) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h := hloc l₁ l₂ ((p : ℝ) ^ (-σ)) (|h₁ - h₂| * Real.log p)
      (fun a => (p : ℂ) ^ (-pairAbscissa σ h₁ h₂ a)) hl₁ hl₂ (by positivity) ht0
      (hle p hp) (fun a => le_of_eq (hnorm p hp a)) (hincr p hp)
    refine le_trans h ?_
    have hxK : (1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p))) * (p : ℝ) ^ (-σ)
        ≤ K * (p : ℝ) ^ (-(σ - δ)) := by
      have hrw : (1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p)))
          = (1 + l₁ / 2) + l₂ * |h₁ - h₂| / 2 * Real.log p := by ring
      rw [hrw]
      refine le_trans (add_mul_log_mul_rpow_neg_le hp1 (by linarith)
        (by positivity) hδ0) ?_
      have hcoeff : (1 + l₁ / 2) + l₂ * |h₁ - h₂| / 2 / δ ≤ K := by
        have hb : l₂ * |h₁ - h₂| / 2 / δ ≤ Λ / 2 / δ := by
          rw [div_le_div_iff_of_pos_right hδ0]
          linarith
        rw [hKdef]
        linarith
      have hpos1 : (0 : ℝ) ≤ (p : ℝ) ^ (-(σ - δ)) := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul_of_nonneg_right hcoeff hpos1
    have hcube : ((p : ℝ) ^ (-(σ - δ))) ^ 3 = (p : ℝ) ^ (-3 * (σ - δ)) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-(σ - δ))) 3, ← Real.rpow_mul (by linarith)]
      congr 1
      push_cast
      ring
    have hx0 : (0 : ℝ) ≤ (1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p)))
        * (p : ℝ) ^ (-σ) := by positivity
    have hcubed := pow_le_pow_left₀ hx0 hxK 3
    have hRHS : (K * (p : ℝ) ^ (-(σ - δ))) ^ 3 = K ^ 3 * (p : ℝ) ^ (-3 * (σ - δ)) := by
      rw [mul_pow, hcube]
    calc C₁ * ((1 + (l₁ / 2 + l₂ / 2 * (|h₁ - h₂| * Real.log p))) * (p : ℝ) ^ (-σ)) ^ 3
        ≤ C₁ * (K * (p : ℝ) ^ (-(σ - δ))) ^ 3 := mul_le_mul_of_nonneg_left hcubed hC₁.le
      _ = C₁ * K ^ 3 * (p : ℝ) ^ (-3 * (σ - δ)) := by rw [hRHS]; ring
  have hmain := abs_log_prod_sub_sum_le hpos hterm
  refine le_trans hmain ?_
  have htail := sum_primesIco_rpow_le_tail (σ₀ := σ₁) (σ := σ - δ) (δ := (σ₁ - 1 / 3) / 2)
    (by linarith) (by linarith) (by linarith) hy₀ y
  rw [show σ₁ - (σ₁ - 1 / 3) / 2 = (σ₁ + 1 / 3) / 2 by ring] at htail
  have hC0 : (0 : ℝ) ≤ C₁ * K ^ 3 := by positivity
  calc C₁ * K ^ 3 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-3 * (σ - δ))
      ≤ C₁ * K ^ 3 * ((y₀ : ℝ) ^ (-3 * ((σ₁ - 1 / 3) / 2))
          * ∑' n : ℕ, (n : ℝ) ^ (-3 * ((σ₁ + 1 / 3) / 2))) :=
        mul_le_mul_of_nonneg_left htail hC0
    _ = pairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) := by
        rw [pairTailConst, hKdef, hδdef, hσ₁def]
        ring

/-! ### Markov against the log-moment -/

/-- **Markov against a bound on the log-moment.**  If `∑_a 2q_a log‖F(s_a)‖ ≥ W` on a measurable
`E` and the prime-by-prime log-moment is at most `B`, then `P(E) ≤ exp(B - W)`. -/
theorem IsSteinhausRMF.measure_le_exp_of_log_le {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {A : Finset ι}
    {q : ι → ℝ} {s : ι → ℂ} {Q B W : ℝ} {y₀ y : ℕ} {E : Set Ω}
    (hq : ∀ a ∈ A, |q a| ≤ Q) (hQ0 : 0 ≤ Q) (hre : ∀ a ∈ A, 0 < (s a).re)
    (hpos : 0 < ∏ p ∈ primesIco y₀ y,
      ∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
    (hlog : Real.log (∏ p ∈ primesIco y₀ y,
      ∫ z, ∏ a ∈ A, ‖(1 - z * (p : ℂ) ^ (-s a))⁻¹‖ ^ (2 * q a) ∂steinhausLaw) ≤ B)
    (hE : MeasurableSet E)
    (hW : ∀ ω ∈ E, W ≤ ∑ a ∈ A, 2 * q a * Real.log ‖randomEulerProductIco f y₀ y (s a) ω‖) :
    μ.real E ≤ Real.exp (B - W) := by
  haveI := hf.isProbabilityMeasure
  have hint := hf.integrable_prod_norm_rpow A q s y₀ y hq hQ0 hre
  have heq := hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y A hre (q := q)
  have hge : ∀ᵐ ω ∂(μ.restrict E), Real.exp W
      ≤ ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) := by
    filter_upwards [ae_restrict_of_ae (hf.prod_norm_rpow_ae_eq A q s y₀ y hre),
      ae_restrict_mem hE] with ω h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (hW ω h2)
  have h1 : μ.real E * Real.exp W
      ≤ ∫ ω in E, (∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) ∂μ := by
    have hc : (∫ _ω in E, Real.exp W ∂μ) = μ.real E * Real.exp W := by
      rw [setIntegral_const, smul_eq_mul]
    rw [← hc]
    exact integral_mono_ae (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hge
  have h2 : (∫ ω in E, (∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a)) ∂μ)
      ≤ ∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ := by
    refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) _
  have h3 : (∫ ω, ∏ a ∈ A, ‖randomEulerProductIco f y₀ y (s a) ω‖ ^ (2 * q a) ∂μ)
      ≤ Real.exp B := by
    rw [heq, ← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hlog
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos W)]
  linarith

/-! ### The one-point tail -/

/-- **The one-point Gaussian tail above a threshold.**  For `0 ≤ V ≤ Q A`,
`A = ∑_{y₀ ≤ p < y} p^{-2σ}`: `P(log‖F(s)‖ ≥ V) ≤ exp(T - V²/A)`, with
`T = multiTailConst Q σ₀ 1 · y₀^{-3(σ₀-1/3)/2}`. -/
theorem IsSteinhausRMF.measure_ge_le_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {σ₀ Q : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hQ0 : 0 ≤ Q) {σ V : ℝ} {s : ℂ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ)
    {E : Set Ω} (hV : 0 ≤ V) (hs : s.re = σ) (hσ : σ₀ ≤ σ)
    (hA : 0 < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hVQ : V ≤ Q * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) (hE : MeasurableSet E)
    (hEV : ∀ ω ∈ E, V ≤ Real.log ‖randomEulerProductIco f y₀ y s ω‖) :
    μ.real E ≤ Real.exp (multiTailConst Q σ₀ 1 * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2))
      - V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  rw [← hAdef] at hA hVQ ⊢
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = V / A := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have huQ : u ≤ Q := by rw [hudef, div_le_iff₀ hA]; linarith
  have huA : u * A = V := by rw [hudef]; field_simp
  have hσ0 : 0 < σ := by linarith
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq : ∀ a ∈ ({0} : Finset ℕ), |(fun _ : ℕ => u) a| ≤ Q := fun _ _ => by
    change |u| ≤ Q
    rw [abs_of_nonneg hu0]
    exact huQ
  have hre : ∀ a ∈ ({0} : Finset ℕ), 0 < ((fun _ : ℕ => s) a).re := fun _ _ => by
    change 0 < s.re
    rw [hs]
    exact hσ0
  have hpos : 0 < ∏ p ∈ primesIco y₀ y, ∫ z, ∏ a ∈ ({0} : Finset ℕ),
      ‖(1 - z * (p : ℂ) ^ (-(fun _ : ℕ => s) a))⁻¹‖ ^ (2 * (fun _ : ℕ => u) a) ∂steinhausLaw := by
    refine Finset.prod_pos fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    refine integral_prod_localIntegrand_pos (Q := Q) hq (θ := (2 : ℝ) ^ (-σ₀)) ?_ hθ
    intro a _
    change ‖(p : ℂ) ^ (-s)‖ ≤ _
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, hs]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have htail := multi_prime_sum_tail_le ({0} : Finset ℕ) hQ0 hσ₀ (q := fun _ => u)
    (s := fun _ => s) hy₀ y hq (fun _ _ => hs) hσ
  rw [Finset.card_singleton] at htail
  have hmain := sum_norm_sum_smul_cpow_le (A := ({0} : Finset ℕ)) (q := fun _ : ℕ => u)
    (s := fun _ : ℕ => s) (σ := σ) (D := 0) (Q := Q) y₀ y (fun _ _ => hs)
    (fun _ _ _ _ => by simp) hq hQ0
  rw [← hAdef] at hmain
  have hR : (∑ a ∈ ({0} : Finset ℕ), (fun _ : ℕ => u) a) ^ 2 * A
      + Q ^ 2 * (({0} : Finset ℕ).card : ℝ) ^ 2 * 0
        * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p = u ^ 2 * A := by
    simp
  have hlog := (abs_le.1 htail).2
  refine le_trans (hf.measure_le_exp_of_log_le hq hQ0 hre hpos
    (B := u ^ 2 * A + multiTailConst Q σ₀ 1 * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2)))
    (W := 2 * u * V) (by linarith) hE ?_) ?_
  · intro ω hω
    rw [Finset.sum_singleton]
    have h := hEV ω hω
    change 2 * u * V ≤ 2 * u * Real.log ‖randomEulerProductIco f y₀ y s ω‖
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · refine Real.exp_le_exp.2 (le_of_eq ?_)
    rw [← huA]
    field_simp
    ring

end RMF
