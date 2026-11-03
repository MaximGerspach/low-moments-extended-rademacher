/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherJointLaplace
import RMF.EulerProduct.JointLaplaceSharp

/-!
# The Rademacher pair Laplace transform above a threshold

The Rademacher counterparts of the constants of `RMF/EulerProduct/JointLaplaceExplicit.lean` and
`RMF/EulerProduct/JointLaplaceSharp.lean`.

* `RMF.radLocalPairConst`: the witness of `RMF.exists_abs_log_local_pair_rademacherLaw`, named, and
  `RMF.abs_log_local_pair_rademacherLaw_le_explicit`, the statement at it (the same proof).
* `RMF.radPairTailConst` and `RMF.rad_pair_prime_sum_tail_le`: the pair expansion over the primes in
  `[y₀, y)`, with error `radPairTailConst σ₀ Λ · y₀^{-3(σ₁-1/3)/2}`, `σ₁ = (σ₀+1/3)/2`.  The
  Steinhaus counterpart is `RMF.pair_prime_sum_tail_le`; the family of points is general, as in
  `RMF.exists_prime_sum_bound_pair_family_rademacherLaw`, so the base height is free.
* `RMF.IsRademacherRMF.measure_le_exp_pair_at_of_log_le`: Markov against a bound on the log of the
  joint moment at `RMF.pairAbscissaAt`.
-/

open MeasureTheory

namespace RMF

/-! ### The local pair constant -/

/-- The fine-regime constant of the Rademacher local pair expansion,
`8/(1-θ₀)³ + 4/(1-θ₀) + 2`. -/
noncomputable def radLocalPairFine (θ₀ : ℝ) : ℝ := 8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2

/-- The scale separating the fine and the crude regimes, `min((1-θ₀)/8, 1/(4(C_f+1)))`. -/
noncomputable def radLocalPairScale (θ₀ : ℝ) : ℝ :=
  min ((1 - θ₀) / 8) (1 / (4 * (radLocalPairFine θ₀ + 1)))

/-- The crude-regime constant, `2/((1-θ₀)d₀²) + 6/d₀`. -/
noncomputable def radLocalPairTail (θ₀ : ℝ) : ℝ :=
  2 / ((1 - θ₀) * radLocalPairScale θ₀ ^ 2) + 6 / radLocalPairScale θ₀

/-- **The constant of the Rademacher local pair expansion**, `2(6 + C_f)² + C_f + C_tail`: the
witness of `RMF.exists_abs_log_local_pair_rademacherLaw`. -/
noncomputable def radLocalPairConst (θ₀ : ℝ) : ℝ :=
  2 * (6 + radLocalPairFine θ₀) ^ 2 + radLocalPairFine θ₀ + radLocalPairTail θ₀

/-- **The local pair bound at a named constant**: `RMF.exists_abs_log_local_pair_rademacherLaw`
with its witness `RMF.radLocalPairConst θ₀`, by the same proof. -/
theorem abs_log_local_pair_rademacherLaw_le_explicit {θ₀ : ℝ} (hθ₀0 : 0 ≤ θ₀) (hθ₀ : θ₀ < 1) :
    0 < radLocalPairConst θ₀ ∧ ∀ (l₁ l₂ t d : ℝ) (w : Fin 3 → ℂ), 0 ≤ l₁ → 0 ≤ l₂ → 0 ≤ d →
      0 ≤ t → t ≤ θ₀ → (∀ a, ‖w a‖ ≤ t) → ‖w 1 - w 2‖ ≤ t * d →
        |Real.log (∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw)
            - ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
                - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
                + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)|
          ≤ radLocalPairConst θ₀ * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 := by
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = 8 / (1 - θ₀) ^ 3 + 4 / (1 - θ₀) + 2 := ⟨_, rfl⟩
  have hCf0 : (0 : ℝ) < Cf := by rw [hCfdef]; positivity
  obtain ⟨d₀, hd₀def⟩ : ∃ d₀ : ℝ, d₀ = min ((1 - θ₀) / 8) (1 / (4 * (Cf + 1))) := ⟨_, rfl⟩
  have hd₀0 : (0 : ℝ) < d₀ := by
    rw [hd₀def]
    exact lt_min (by positivity) (by positivity)
  have hd₀8 : d₀ ≤ (1 - θ₀) / 8 := by rw [hd₀def]; exact min_le_left _ _
  have hd₀le : d₀ ≤ 1 / 8 := le_trans hd₀8 (by linarith)
  have hCd₀ : Cf * d₀ ≤ 1 / 4 := by
    have hd₀C : d₀ ≤ 1 / (4 * (Cf + 1)) := by rw [hd₀def]; exact min_le_right _ _
    have h1 : Cf * d₀ ≤ Cf * (1 / (4 * (Cf + 1))) := mul_le_mul_of_nonneg_left hd₀C hCf0.le
    have h2 : Cf * (1 / (4 * (Cf + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  obtain ⟨Ctail, hCtail⟩ : ∃ Ctail : ℝ, Ctail = 2 / ((1 - θ₀) * d₀ ^ 2) + 6 / d₀ := ⟨_, rfl⟩
  have hCtail0 : (0 : ℝ) ≤ Ctail := by rw [hCtail]; positivity
  have hconst : radLocalPairConst θ₀ = 2 * (6 + Cf) ^ 2 + Cf + Ctail := by
    rw [hCtail, hd₀def, hCfdef]
    rfl
  rw [hconst]
  refine ⟨by positivity, ?_⟩
  intro l₁ l₂ t d w hl₁ hl₂ hd0 ht0 htθ hw h12
  have ht1 : t < 1 := lt_of_le_of_lt htθ hθ₀
  have hM0 : (0 : ℝ) ≤ l₁ / 2 + l₂ / 2 * d := by positivity
  have hx0 : (0 : ℝ) ≤ (1 + (l₁ / 2 + l₂ / 2 * d)) * t := by positivity
  have hMtx : (l₁ / 2 + l₂ / 2 * d) * t ≤ (1 + (l₁ / 2 + l₂ / 2 * d)) * t := by nlinarith
  have hwlt : ∀ a ∈ (Finset.univ : Finset (Fin 3)), ‖w a‖ < 1 := fun a _ =>
    lt_of_le_of_lt (hw a) ht1
  have hcrude0 : |Real.log (∫ z, ∏ a, ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂rademacherLaw)| ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * (t / (1 - t)) :=
    abs_log_integral_prod_rademacherLaw_le_of_bound hwlt fun z hz =>
      abs_two_mul_sum_pairWeight_localLogAdd_le hz hl₁ hl₂ ht1 (hw 0) (hw 1) (hw 2) h12
  have hP := abs_pair_main_term_le hl₁ hl₂ hd0 ht0 (hw 0) (hw 1) (hw 2) h12
  rcases le_or_gt ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) d₀ with hfine | hbig
  · have hsmall : (l₁ / 2 + l₂ / 2 * d) * t ≤ (1 - θ₀) / 8 :=
      le_trans hMtx (le_trans hfine hd₀8)
    have hIP := abs_integral_prod_pairWeight_sub_one_add_le hl₁ hl₂ hd0 ht0 htθ hθ₀
      (hw 0) (hw 1) (hw 2) h12 hsmall
    rw [← hCfdef] at hIP
    have hhalf := abs_sub_one_le_half_of_fine hCf0.le hx0 hfine hd₀le hCd₀ hIP hP
    have hx1 : (1 + (l₁ / 2 + l₂ / 2 * d)) * t ≤ 1 := by
      linarith [le_trans hfine hd₀le]
    refine le_trans (abs_log_sub_poly_le hx0 hx1 hCf0.le hIP hP hhalf) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hsplit := abs_sub (Real.log (∫ z, ∏ a,
      ‖1 + z * w a‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw))
      ((∑ a, pairWeight l₁ l₂ a * ‖w a‖ ^ 2)
        - 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re ^ 2)
        + 2 * (∑ a, pairWeight l₁ l₂ a * (w a).re) ^ 2)
    have hcr := crude_le_of_le_theta hM0 ht0 htθ hθ₀ hMtx
    have hdom := crude_dominate hd₀0 hbig hθ₀
    rw [← hCtail] at hdom
    have hfin : Ctail * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3
        ≤ (2 * (6 + Cf) ^ 2 + Cf + Ctail) * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (6 + Cf), hCf0.le]) (by positivity)
    linarith

/-! ### The pair expansion above a threshold -/

/-- **The Rademacher pair expansion's tail constant**: `C₁K³∑_n n^{-3σ₂}`, with
`C₁ = radLocalPairConst 2^{-σ₀}`, `δ = (σ₀-1/3)/2`, `K = 1 + Λ/2 + Λ/(2δ)`,
`σ₁ = (σ₀+1/3)/2` and `σ₂ = (σ₁+1/3)/2`: `RMF.pairTailConst` at the Rademacher local constant. -/
noncomputable def radPairTailConst (σ₀ Λ : ℝ) : ℝ :=
  radLocalPairConst ((2 : ℝ) ^ (-σ₀)) * (1 + Λ / 2 + Λ / 2 / ((σ₀ - 1 / 3) / 2)) ^ 3
    * ∑' n : ℕ, (n : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 + 1 / 3) / 2))

lemma radPairTailConst_nonneg {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    0 ≤ radPairTailConst σ₀ Λ := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hC₁, -⟩ := abs_log_local_pair_rademacherLaw_le_explicit hθ0 hθ
  have hδ : (0 : ℝ) < (σ₀ - 1 / 3) / 2 := by linarith
  have hT : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 + 1 / 3) / 2)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [radPairTailConst]
  positivity

/-- **The Rademacher pair expansion over the primes in `[y₀, y)`**, at a general family of points
`s : Fin 3 → ℂ` with `Re s_a = σ ≥ σ₀`, `|Im s₁ - Im s₂| ≤ D`, `l₁ ≤ Λ` and `l₂ D ≤ Λ`: the log of
the pair moment is its phase-sensitive main term up to
`radPairTailConst σ₀ Λ · y₀^{-3(σ₁-1/3)/2}`, `σ₁ = (σ₀+1/3)/2`.  The proof of
`RMF.exists_prime_sum_bound_pair_family_rademacherLaw`, with the error summed over `p ≥ y₀` as in
`RMF.pair_prime_sum_tail_le`. -/
theorem rad_pair_prime_sum_tail_le {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ)
    {l₁ l₂ σ D : ℝ} {s : Fin 3 → ℂ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ) (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (hσ : σ₀ ≤ σ) (hl₁Λ : l₁ ≤ Λ) (hD0 : 0 ≤ D) (hre : ∀ a, (s a).re = σ)
    (him : |(s 1).im - (s 2).im| ≤ D) (hl₂Λ : l₂ * D ≤ Λ) :
    |Real.log (∏ p ∈ primesIco y₀ y, ∫ z, ∏ a,
          ‖1 + z * (p : ℂ) ^ (-s a)‖ ^ (2 * pairWeight l₁ l₂ a) ∂rademacherLaw)
        - ∑ p ∈ primesIco y₀ y,
            ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-s a)‖ ^ 2)
              - 2 * (∑ a, pairWeight l₁ l₂ a * ((p : ℂ) ^ (-s a)).re ^ 2)
              + 2 * (∑ a, pairWeight l₁ l₂ a * ((p : ℂ) ^ (-s a)).re) ^ 2)|
      ≤ radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) := by
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  have hθ : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hC₁, hloc⟩ := abs_log_local_pair_rademacherLaw_le_explicit hθ0 hθ
  set C₁ := radLocalPairConst ((2 : ℝ) ^ (-σ₀)) with hC₁_expl
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (σ₀ - 1 / 3) / 2 := ⟨_, rfl⟩
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; linarith
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = (σ₀ + 1 / 3) / 2 := ⟨_, rfl⟩
  have hσ₁1 : 1 / 3 < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁δ : σ₀ - δ = σ₁ := by rw [hδdef, hσ₁def]; ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + Λ / 2 + Λ / 2 / δ := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hnorm : ∀ p ∈ primesIco y₀ y, ∀ a : Fin 3,
      ‖((p : ℂ)) ^ (-s a)‖ = (p : ℝ) ^ (-σ) := by
    intro p hp a
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos,
      Complex.neg_re, hre a]
  have hle : ∀ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).two_le
    calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hincr : ∀ p ∈ primesIco y₀ y,
      ‖(p : ℂ) ^ (-s 1) - (p : ℂ) ^ (-s 2)‖
        ≤ (p : ℝ) ^ (-σ) * (D * Real.log p) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    have hrp : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h := norm_natCast_cpow_neg_sub_le hpp.pos
      (s₁ := s 1) (s₂ := s 2) (σ := σ)
      (hre 1) (hre 2)
    exact le_trans h (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right him hlogp) hrp)
  have hpos : ∀ p ∈ primesIco y₀ y, 0 < ∫ z, ∏ a,
      ‖1 + z * (p : ℂ) ^ (-s a)‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂rademacherLaw := by
    intro p hp
    refine integral_prod_norm_one_add_mul_rpow_pos fun a _ => ?_
    rw [hnorm p hp a]
    exact lt_of_le_of_lt (hle p hp) hθ
  have hterm : ∀ p ∈ primesIco y₀ y,
      |Real.log (∫ z, ∏ a,
            ‖1 + z * (p : ℂ) ^ (-s a)‖ ^ (2 * pairWeight l₁ l₂ a)
            ∂rademacherLaw)
          - ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-s a)‖ ^ 2)
              - 2 * (∑ a, pairWeight l₁ l₂ a
                  * ((p : ℂ) ^ (-s a)).re ^ 2)
              + 2 * (∑ a, pairWeight l₁ l₂ a
                  * ((p : ℂ) ^ (-s a)).re) ^ 2)|
        ≤ C₁ * K ^ 3 * (p : ℝ) ^ (-3 * (σ - δ)) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hp1
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
    have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    have h := hloc l₁ l₂ ((p : ℝ) ^ (-σ)) (D * Real.log p)
      (fun a => (p : ℂ) ^ (-s a)) hl₁ hl₂ (mul_nonneg hD0 hlog0) ht0
      (hle p hp) (fun a => le_of_eq (hnorm p hp a)) (hincr p hp)
    refine le_trans h ?_
    have hxK : (1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p))) * (p : ℝ) ^ (-σ)
        ≤ K * (p : ℝ) ^ (-(σ - δ)) :=
      pair_bracket_le_rpow hp1 hl₁ hl₂ hD0 hδ0 hK0 hl₁Λ hl₂Λ (le_of_eq hKdef.symm) le_rfl
    have hx0 : (0 : ℝ) ≤ (1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p)))
        * (p : ℝ) ^ (-σ) := by positivity
    have hcubed := pow_le_pow_left₀ hx0 hxK 3
    have hRHS : (K * (p : ℝ) ^ (-(σ - δ))) ^ 3 = K ^ 3 * (p : ℝ) ^ (-3 * (σ - δ)) := by
      rw [mul_pow, rpow_neg_cube_eq hp0]
    calc C₁ * ((1 + (l₁ / 2 + l₂ / 2 * (D * Real.log p))) * (p : ℝ) ^ (-σ)) ^ 3
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
    _ = radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) := by
        rw [radPairTailConst, hKdef, hδdef, hσ₁def]
        ring

/-- **The pair expansion at a general base above a threshold**: `RMF.rad_pair_prime_sum_tail_le` at
`RMF.pairAbscissaAt σ h₀ h₁ h₂`, `D = |h₁ - h₂|`. -/
theorem rad_pair_prime_sum_tail_le_at {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ)
    {l₁ l₂ σ h₀ h₁ h₂ : ℝ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hσ : σ₀ ≤ σ) (hl₁Λ : l₁ ≤ Λ) (hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ) :
    |Real.log (∏ p ∈ primesIco y₀ y, ∫ z, ∏ a,
          ‖1 + z * (p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ (2 * pairWeight l₁ l₂ a)
          ∂rademacherLaw)
        - ∑ p ∈ primesIco y₀ y,
            ((∑ a, pairWeight l₁ l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
              - 2 * (∑ a, pairWeight l₁ l₂ a
                  * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
              + 2 * (∑ a, pairWeight l₁ l₂ a
                  * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2)|
      ≤ radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) :=
  rad_pair_prime_sum_tail_le hσ₀ hΛ hy₀ y hl₁ hl₂ hσ hl₁Λ (abs_nonneg _)
    (pairAbscissaAt_re σ h₀ h₁ h₂)
    (le_of_eq (by rw [pairAbscissaAt_im_one, pairAbscissaAt_im_two])) hl₂Λ

/-! ### Markov against the log of the joint moment -/

/-- **Markov at the pair abscissas, against a bound on the log of the joint moment**: if
`log E ∏_a ‖F(s_a)‖^{2q_a} ≤ B` at `s = RMF.pairAbscissaAt σ h₀ h₁ h₂` and weights
`RMF.pairWeight l₁ l₂`, then on any measurable `E` where
`l₁ log‖F(s_0)‖ + l₂(log‖F(s_1)‖ - log‖F(s_2)‖) ≥ W`, `P(E) ≤ exp(B - W)`.  The body of
`RMF.IsRademacherRMF.exists_measure_le_exp_pair_at` with the log bound as input. -/
theorem IsRademacherRMF.measure_le_exp_pair_at_of_log_le {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {σ₀ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) {l₁ l₂ σ h₀ h₁ h₂ W B : ℝ} {y₀ y : ℕ} {E : Set Ω}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hσ : σ₀ ≤ σ)
    (hlog : Real.log (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) ∂μ) ≤ B)
    (hE : MeasurableSet E)
    (hEW : ∀ ω ∈ E, W
      ≤ l₁ * Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 0) ω‖
        + l₂ * (Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 1) ω‖
          - Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 2) ω‖)) :
    μ.real E ≤ Real.exp (B - W) := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissaAt σ h₀ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissaAt_re]
    linarith
  have hq : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      |pairWeight l₁ l₂ a| ≤ l₁ / 2 + l₂ / 2 := fun a _ => abs_pairWeight_le hl₁ hl₂ a
  have hint := hf.integrable_prod_norm_rpow Finset.univ (pairWeight l₁ l₂)
    (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hq (by linarith) hre
  have hIpos := hf.integral_prod_norm_pair_pos_at hσ₀ l₁ l₂ σ h₀ h₁ h₂ y₀ y hσ
  have hW : ∀ ω ∈ E, W
      ≤ ∑ a, 2 * pairWeight l₁ l₂ a
        * Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖ := by
    intro ω hω
    rw [sum_two_mul_pairWeight_mul]
    exact hEW ω hω
  have hge : ∀ᵐ ω ∂(μ.restrict E), Real.exp W
      ≤ ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) := by
    filter_upwards [ae_restrict_of_ae (hf.prod_norm_rpow_ae_eq Finset.univ
      (pairWeight l₁ l₂) (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hre), ae_restrict_mem hE] with ω h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (hW ω h2)
  have h1 : μ.real E * Real.exp W
      ≤ ∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a)) ∂μ := by
    have hc : (∫ _ω in E, Real.exp W ∂μ)
        = μ.real E * Real.exp W := by
      rw [setIntegral_const, smul_eq_mul]
    rw [← hc]
    exact integral_mono_ae (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hge
  have h2 : (∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a)) ∂μ)
      ≤ ∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight l₁ l₂ a) ∂μ := by
    refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) _
  have h3 : (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight l₁ l₂ a) ∂μ) ≤ Real.exp B := by
    have h4 := Real.exp_le_exp.2 hlog
    rwa [Real.exp_log hIpos] at h4
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  linarith

end RMF
