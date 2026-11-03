/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfSecondMoment
import RMF.Weighted.CentralWindow

/-!
# The small primes at `q = ½`: the twisted moments

The two statements about the primes *below* the window's scale that the decomposition at `q = ½`
(`RMF/Weighted/HalfDecomposition.lean`) uses in place of Propositions 6.1 and 6.2 of the paper.
The small primes are tilted by `|F(½+σ)|` itself, with
exponent `1 = 2q`: at a real point the Rademacher local factor is `1 ± u`, `u = p^{-1/2-σ}`, so
`E|F(½+σ)| = 1` exactly and `|F(½+σ)|·P` is a probability measure.  The two statements are
moments of the twist `R(h) = |F(½+σ+ih)|²/|F(½+σ)|²` against it.

* **(C2)** `E[|F(σ)|·R(h₁)R(h₂)] ≤ C` — `RMF.integral_halfTwist_pair_le`.  Per prime the mean is
  `1 + 2u²(d₁+d₂)/(1-u²) + 2u²d₁d₂((1+u)^{-3}+(1-u)^{-3})`, `d_i = 1 - cos(h_i log p)`, and
  `∑_p u²(h log p)² ≪ 1` for `h ≤ e^{-k}`, because `∑_{p < e^{e^k}} (log p)²/p ≪ e^{2k}`.
* **(C3)** `E[|F(σ)|·R(h)·1_{E_≤(k)}] ≥ c` — `RMF.le_setIntegral_halfLadder_twist`, where
  `E_≤(k) = RMF.halfLadder` asks the real-point walk from `k₀` to reach a strict new maximum at
  `k`.  Under the twisted law the value at each prime still has two atoms, with weights
  `RMF.twistPi`, and the walk's increment over a scale has mean `u²(1-4d)/2 + O(u³)` and second
  moment `u² + O(u³)` there (`RMF.abs_twistMean_sub_le`, `RMF.abs_twistVar_sub_le`).  So each
  scale carries a drift `≍ +1/2` except where the twist bites, `d ≍ 1`, which for `h ≤ e^{-k}`
  is only the top two scales.  The ladder event is then produced by three independent pieces:
  the top two scales each rise by `200` with positive probability (`RMF.twistMGF_ge` and a
  weighted Paley–Zygmund, `RMF.le_setIntegral_twist_scale`), and every suffix below them stays
  above `-200` (`RMF.twistMGF_neg_le` and Chernoff, `RMF.half_le_setIntegral_twist_good`) — on
  their intersection every suffix of the walk is positive, which is the ladder event.

Both bounds are uniform in the height and in the scales, and their constants are absolute (and
enormous: the anti-concentration at a level `200` is paid for by an exponential).
-/

set_option linter.style.longFile 3300

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The local factor at a shifted line

`p^{-(½+σ+ih)}` has modulus `u = p^{-1/2-σ}` and real part `u cos(h log p)`, so on the two atoms
`z = ±1` the local weight `‖1 + z p^{-s}‖²` is `1 ± 2u cos(h log p) + u²`, which is
`(1±u)² ∓ 2u(1 - cos(h log p))`. -/

lemma norm_cpow_neg_shiftLine {p : ℕ} (hp : 0 < p) (σ h : ℝ) :
    ‖(p : ℂ) ^ (-shiftLine σ h)‖ = (p : ℝ) ^ (-(1 / 2 + σ)) := by
  rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re, re_shiftLine]

lemma re_cpow_neg_shiftLine {p : ℕ} (hp : 0 < p) (σ h : ℝ) :
    ((p : ℂ) ^ (-shiftLine σ h)).re = (p : ℝ) ^ (-(1 / 2 + σ)) * Real.cos (h * Real.log p) := by
  rw [re_natCast_cpow_neg hp, re_shiftLine, im_shiftLine]

/-- At the real point the local factor is the positive real `1 ± u`. -/
lemma cpow_neg_shiftLine_zero (p : ℕ) (σ : ℝ) :
    (p : ℂ) ^ (-shiftLine σ 0) = (((p : ℝ) ^ (-(1 / 2 + σ)) : ℝ) : ℂ) := by
  have h : shiftLine σ 0 = ((1 / 2 + σ : ℝ) : ℂ) := by
    rw [shiftLine]
    push_cast
    ring
  rw [h, natCast_cpow_neg_ofReal]

/-! ### The per-prime factor of (C2) -/

/-- **The two atoms of the doubly twisted weight.**  With `d_i = 1 - cos(h_i log p)` the average of
`‖1 + z p^{-s₁}‖²‖1 + z p^{-s₂}‖²/‖1 + z p^{-σ}‖³` over `z = ±1` is
`1 + 2u²(d₁+d₂)/(1-u²) + u²d₁d₂(2(1+u)^{-3} + 2(1-u)^{-3})`. -/
lemma twist_pair_atoms_eq {u d₁ d₂ : ℝ} (hu0 : 0 < u) (hu : u < 1) :
    (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) / (1 + u) ^ 3
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) / (1 - u) ^ 3) / 2
      = 1 + 2 * u ^ 2 * (d₁ + d₂) / (1 - u ^ 2)
        + u ^ 2 * d₁ * d₂ * (2 / (1 + u) ^ 3 + 2 / (1 - u) ^ 3) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  rw [show (1 : ℝ) - u ^ 2 = (1 + u) * (1 - u) by ring]
  field_simp
  ring

/-- **The per-prime bound of (C2)**: the average over the two atoms is at most
`1 + 21u²(d₁+d₂)`. -/
lemma twist_pair_atoms_le {u d₁ d₂ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2)
    (hd₁ : 0 ≤ d₁) (hd₁2 : d₁ ≤ 2) (hd₂ : 0 ≤ d₂) (hd₂2 : d₂ ≤ 2) :
    (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) / (1 + u) ^ 3
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) / (1 - u) ^ 3) / 2
      ≤ 1 + 21 * u ^ 2 * (d₁ + d₂) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (1 / 2 : ℝ) ≤ 1 - u := by linarith
  have h2' : (0 : ℝ) < 1 - u := by linarith
  rw [twist_pair_atoms_eq hu0 (by linarith)]
  have hsq : (3 / 4 : ℝ) ≤ 1 - u ^ 2 := by nlinarith
  have hprod : d₁ * d₂ ≤ d₁ + d₂ := by nlinarith
  -- the first correction
  have hA : 2 * u ^ 2 * (d₁ + d₂) / (1 - u ^ 2) ≤ 8 / 3 * (u ^ 2 * (d₁ + d₂)) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0:ℝ) ≤ d₁ + d₂)]
  -- the second
  have hB1 : 2 / (1 + u) ^ 3 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg u, mul_nonneg (mul_nonneg hu0.le hu0.le) hu0.le]
  have hB2 : 2 / (1 - u) ^ 3 ≤ 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (1 - u), pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h2 3]
  have hB : u ^ 2 * d₁ * d₂ * (2 / (1 + u) ^ 3 + 2 / (1 - u) ^ 3)
      ≤ 18 * (u ^ 2 * (d₁ + d₂)) := by
    have h0 : 0 ≤ u ^ 2 * d₁ * d₂ := by positivity
    calc u ^ 2 * d₁ * d₂ * (2 / (1 + u) ^ 3 + 2 / (1 - u) ^ 3)
        ≤ u ^ 2 * d₁ * d₂ * 18 := by
          refine mul_le_mul_of_nonneg_left (by linarith) h0
      _ = 18 * (u ^ 2 * (d₁ * d₂)) := by ring
      _ ≤ 18 * (u ^ 2 * (d₁ + d₂)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (sq_nonneg u))
            (by norm_num)
  have hpos : 0 ≤ u ^ 2 * (d₁ + d₂) := mul_nonneg (sq_nonneg u) (by linarith)
  linarith

/-! ### The mean of the doubly twisted weight at one prime -/

/-- `p^{-1/2-σ} ≤ 1/2` at every prime `p ≥ 5` and every `σ ≥ 0`. -/
lemma rpow_neg_half_add_le_half {p : ℕ} (hp : 5 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) :
    (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / 2 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : (5 : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hp5 (by norm_num)
  have h2 : (2 : ℝ) ≤ (5 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h4 : Real.sqrt 4 ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
  have h3 : (p : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ (1 / 2 + σ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have h4 : (0 : ℝ) < (p : ℝ) ^ (1 / 2 + σ) := Real.rpow_pos_of_pos hp0 _
  rw [Real.rpow_neg hp0.le, inv_le_comm₀ h4 (by norm_num)]
  linarith

/-- **The mean of the doubly twisted local weight at one prime**, `p ≥ 5`:
`E[‖1+zp^{-s₁}‖²‖1+zp^{-s₂}‖²/‖1+zp^{-σ}‖³] ≤ 1 + 11u²((h₁ log p)² + (h₂ log p)²)`. -/
lemma integral_twistPair_rademacherLaw_le {p : ℕ} (hp : 5 ≤ p) {σ h₁ h₂ : ℝ} (hσ : 0 ≤ σ) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₂)‖ ^ 2
        / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ 3 ∂rademacherLaw)
      ≤ 1 + 11 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
          * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu_def
  have hu0 : 0 < u := Real.rpow_pos_of_pos hpR _
  have hu2 : u ≤ 1 / 2 := rpow_neg_half_add_le_half hp hσ
  have hnorm : ∀ h : ℝ, ‖(p : ℂ) ^ (-shiftLine σ h)‖ = u := fun h =>
    norm_cpow_neg_shiftLine hp0 σ h
  have hre : ∀ h : ℝ, ((p : ℂ) ^ (-shiftLine σ h)).re = u * Real.cos (h * Real.log p) :=
    fun h => re_cpow_neg_shiftLine hp0 σ h
  have hpos : ∀ h : ℝ, ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      = (1 + u) ^ 2 - 2 * u * (1 - Real.cos (h * Real.log p)) := by
    intro h
    rw [norm_one_add_mul_sq_eq (by simp), one_mul, hre h, hnorm h]
    ring
  have hneg : ∀ h : ℝ, ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      = (1 - u) ^ 2 + 2 * u * (1 - Real.cos (h * Real.log p)) := by
    intro h
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
  -- the two atoms
  rw [integral_rademacherLaw_eq]
  simp only [smul_eq_mul]
  rw [hpos h₁, hpos h₂, hneg h₁, hneg h₂, hn1, hn2]
  set d₁ : ℝ := 1 - Real.cos (h₁ * Real.log p) with hd₁_def
  set d₂ : ℝ := 1 - Real.cos (h₂ * Real.log p) with hd₂_def
  have hd₁0 : 0 ≤ d₁ := by rw [hd₁_def]; linarith [Real.cos_le_one (h₁ * Real.log p)]
  have hd₂0 : 0 ≤ d₂ := by rw [hd₂_def]; linarith [Real.cos_le_one (h₂ * Real.log p)]
  have hd₁2 : d₁ ≤ 2 := by rw [hd₁_def]; linarith [Real.neg_one_le_cos (h₁ * Real.log p)]
  have hd₂2 : d₂ ≤ 2 := by rw [hd₂_def]; linarith [Real.neg_one_le_cos (h₂ * Real.log p)]
  have hd₁sq : d₁ ≤ (h₁ * Real.log p) ^ 2 / 2 := by
    have := abs_cos_sub_one_le (h₁ * Real.log p)
    rw [abs_le] at this
    rw [hd₁_def]
    linarith [this.1]
  have hd₂sq : d₂ ≤ (h₂ * Real.log p) ^ 2 / 2 := by
    have := abs_cos_sub_one_le (h₂ * Real.log p)
    rw [abs_le] at this
    rw [hd₂_def]
    linarith [this.1]
  have hmain := twist_pair_atoms_le hu0 hu2 hd₁0 hd₁2 hd₂0 hd₂2
  have hstep : 21 * u ^ 2 * (d₁ + d₂)
      ≤ 11 * u ^ 2 * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) := by
    have hsum : d₁ + d₂ ≤ ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) / 2 := by linarith
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith : (0:ℝ) ≤ d₁ + d₂)]
  have hhalf : (2 : ℝ)⁻¹ * (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) / (1 + u) ^ 3
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) / (1 - u) ^ 3)
      = (((1 + u) ^ 2 - 2 * u * d₁) * ((1 + u) ^ 2 - 2 * u * d₂) / (1 + u) ^ 3
        + ((1 - u) ^ 2 + 2 * u * d₁) * ((1 - u) ^ 2 + 2 * u * d₂) / (1 - u) ^ 3) / 2 := by
    ring
  rw [hhalf]
  linarith

/-! ### The sum over the small primes -/

/-- `log (scaleCut θ) ≤ e^θ + 1`: the cut is `⌊e^{e^θ}⌋ + 1 ≤ 2e^{e^θ}`. -/
lemma log_scaleCut_le (θ : ℝ) : Real.log ((scaleCut θ : ℕ) : ℝ) ≤ Real.exp θ + 1 := by
  have hb : (1 : ℝ) ≤ blockScale θ 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.one_le_exp (Real.exp_pos _).le
  have hle : ((scaleCut θ : ℕ) : ℝ) ≤ 2 * blockScale θ 0 := by
    have hfl : ((⌊blockScale θ 0⌋₊ : ℕ) : ℝ) ≤ blockScale θ 0 := Nat.floor_le (by linarith)
    unfold scaleCut
    push_cast
    linarith
  have hpos : (0 : ℝ) < ((scaleCut θ : ℕ) : ℝ) := by
    have : 0 < scaleCut θ := by unfold scaleCut; omega
    exact_mod_cast this
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (by positivity), blockScale] at hlog
  simp only [Nat.cast_zero, zero_add, Real.log_exp] at hlog
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

/-- `5 ≤ scaleCut θ` for `θ ≥ 1`: `e^{e^θ} ≥ e² > 7`. -/
lemma five_le_scaleCut {θ : ℝ} (hθ : 1 ≤ θ) : 5 ≤ scaleCut θ := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (2 : ℝ) ≤ Real.exp θ := by
    have := Real.exp_le_exp.2 hθ
    linarith
  have h7 : ((7 : ℕ) : ℝ) ≤ blockScale θ 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    have hmono : Real.exp 2 ≤ Real.exp (Real.exp θ) := Real.exp_le_exp.2 h2
    have h22 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    push_cast
    nlinarith
  have := Nat.le_floor h7
  unfold scaleCut
  omega

/-- **The weighted prime sum below the cut**: `∑_{p < scaleCut k} (log p)²/p ≤ 6e^{2k}`. -/
lemma sum_log_sq_div_primesBelow_scaleCut_le {k : ℕ} (hk : 1 ≤ k) :
    ∑ p ∈ Nat.primesBelow (scaleCut (k : ℝ)), Real.log p ^ 2 / p
      ≤ 6 * Real.exp (2 * (k : ℝ)) := by
  have hy : 1 ≤ scaleCut (k : ℝ) := by unfold scaleCut; omega
  have hbase := sum_log_sq_div_primesBelow_le (y := scaleCut (k : ℝ)) hy
  set L : ℝ := Real.log ((scaleCut (k : ℝ) : ℕ) : ℝ) with hL_def
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hy)
  have hLle : L ≤ Real.exp (k : ℝ) + 1 := log_scaleCut_le (k : ℝ)
  have hE : (2.7 : ℝ) ≤ Real.exp (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have := Real.exp_le_exp.2 hk1
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hsq : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) * Real.exp (k : ℝ) := by
    rw [← Real.exp_add]; ring_nf
  refine le_trans hbase ?_
  rw [hsq]
  nlinarith [Real.exp_pos (k : ℝ), sq_nonneg (Real.exp (k : ℝ) - 2.7),
    mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp (k : ℝ) - 2.7) hL0]

/-! ### (C2): the doubly twisted small primes -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(C2), with an explicit constant.**  `E[|F(σ+ih₁)|²|F(σ+ih₂)|²/|F(σ)|³] ≤ e^{132}` for the
primes between the cuts at `k₀ ≥ 1` and `k ≥ k₀`, at heights `0 ≤ h_i ≤ e^{-k}`.

Per prime the mean is `1 + 2u²(d₁+d₂)/(1-u²) + O(u²d₁d₂) ≤ 1 + 11u²((h₁ log p)² + (h₂ log p)²)`
(`RMF.integral_twistPair_rademacherLaw_le`); the product of those is at most the exponential of
`11(h₁²+h₂²)∑_p (log p)²/p ≤ 11·2e^{-2k}·6e^{2k}`. -/
theorem integral_halfTwist_pair_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {k₀ k : ℕ} (hk₀ : 1 ≤ k₀) (hkk : k₀ ≤ k) {σ h₁ h₂ : ℝ}
    (hσ : 0 ≤ σ) (hh₁0 : 0 ≤ h₁) (hh₁ : h₁ ≤ Real.exp (-(k : ℝ)))
    (hh₂0 : 0 ≤ h₂) (hh₂ : h₂ ≤ Real.exp (-(k : ℝ))) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3 ∂μ)
      ≤ Real.exp 132 := by
  classical
  set S : Finset ℕ := primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) with hS_def
  set g : ℕ → ℂ → ℝ := fun p z =>
    ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₁)‖ ^ 2 * ‖1 + z * (p : ℂ) ^ (-shiftLine σ h₂)‖ ^ 2
      / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ 3 with hg_def
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hS5 : ∀ p ∈ S, 5 ≤ p := by
    intro p hp
    have h1 : scaleCut (k₀ : ℝ) ≤ p := (mem_primesIco.1 hp).2.1
    have h2 : 5 ≤ scaleCut (k₀ : ℝ) := five_le_scaleCut (by exact_mod_cast hk₀)
    omega
  have hgm : ∀ p : ℕ, Measurable (g p) := by
    intro p
    rw [hg_def]
    fun_prop
  -- the pointwise product form
  have hpt : ∀ ω : Ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ 3
        = ∏ p ∈ S, g p (X p ω) := by
    intro ω
    rw [hg_def, hS_def]
    simp only [randomEulerProductIco_sqfree_eq, norm_prod, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hX.integral_prod hSp g
    fun p _ => (hgm p).aestronglyMeasurable]
  -- the per-prime bound
  have hbound : ∀ p ∈ S, (∫ z, g p z ∂rademacherLaw)
      ≤ 1 + 11 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
          * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2) :=
    fun p hp => integral_twistPair_rademacherLaw_le (hS5 p hp) hσ
  have hnonneg : ∀ p ∈ S, 0 ≤ ∫ z, g p z ∂rademacherLaw := by
    intro p _
    refine integral_nonneg fun z => ?_
    rw [hg_def]
    positivity
  refine le_trans (Finset.prod_le_prod hnonneg hbound) ?_
  refine le_trans (Real.prod_one_add_le_exp_sum S (f := fun p =>
    11 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2))
    fun p => by positivity) ?_
  refine Real.exp_le_exp.2 ?_
  -- the sum over the primes
  have hterm : ∀ p ∈ S,
      11 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * ((h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2)
        ≤ 11 * (h₁ ^ 2 + h₂ ^ 2) * (Real.log p ^ 2 / p) := by
    intro p hp
    have hpp := hSp p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hu : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 ≤ 1 / (p : ℝ) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le]
      calc (p : ℝ) ^ (-(1 / 2 + σ) * (2 : ℕ)) ≤ (p : ℝ) ^ (-1 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
            push_cast
            linarith
        _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hexp : (h₁ * Real.log p) ^ 2 + (h₂ * Real.log p) ^ 2
        = (h₁ ^ 2 + h₂ ^ 2) * Real.log p ^ 2 := by ring
    rw [hexp]
    have hprod : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * ((h₁ ^ 2 + h₂ ^ 2) * Real.log p ^ 2)
        ≤ 1 / (p : ℝ) * ((h₁ ^ 2 + h₂ ^ 2) * Real.log p ^ 2) :=
      mul_le_mul_of_nonneg_right hu (by positivity)
    calc 11 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * ((h₁ ^ 2 + h₂ ^ 2) * Real.log p ^ 2)
        = 11 * (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * ((h₁ ^ 2 + h₂ ^ 2) * Real.log p ^ 2)) := by ring
      _ ≤ 11 * (1 / (p : ℝ) * ((h₁ ^ 2 + h₂ ^ 2) * Real.log p ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 11 * (h₁ ^ 2 + h₂ ^ 2) * (Real.log p ^ 2 / p) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  -- the prime sum, and the height bound
  have hsub : S ⊆ Nat.primesBelow (scaleCut (k : ℝ)) := by
    intro p hp
    obtain ⟨hpp, _, hlt⟩ := mem_primesIco.1 hp
    exact Nat.mem_primesBelow.2 ⟨hlt, hpp⟩
  have hsum : ∑ p ∈ S, Real.log p ^ 2 / p ≤ 6 * Real.exp (2 * (k : ℝ)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_)
      (sum_log_sq_div_primesBelow_scaleCut_le (by omega))
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
    have hl : 0 ≤ Real.log p := Real.log_nonneg hp1
    positivity
  have hh : h₁ ^ 2 + h₂ ^ 2 ≤ 2 * Real.exp (-(2 * (k : ℝ))) := by
    have he : Real.exp (-(k : ℝ)) * Real.exp (-(k : ℝ)) = Real.exp (-(2 * (k : ℝ))) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (-(k : ℝ))]
  have hEE : Real.exp (-(2 * (k : ℝ))) * Real.exp (2 * (k : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hs0 : 0 ≤ ∑ p ∈ S, Real.log p ^ 2 / p := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSp p hp).one_lt.le
    have hl : 0 ≤ Real.log p := Real.log_nonneg hp1
    positivity
  nlinarith [Real.exp_pos (2 * (k : ℝ)), Real.exp_pos (-(2 * (k : ℝ))),
    mul_nonneg (by positivity : (0:ℝ) ≤ h₁ ^ 2 + h₂ ^ 2) hs0]

/-! ### Two-atom exponential moments

(C3) rests on the moment generating function of one prime's contribution under the twisted law.
That law has two atoms, so the estimates below are elementary: a quadratic upper bound and a
cubic lower bound for `exp`, averaged over two points. -/

/-- `e^x ≤ 1 + x + x²` on `|x| ≤ 1`. -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  rw [abs_le] at h
  linarith [h.2]

/-- `e^x ≥ 1 + x + x²/2 - |x|³` on `|x| ≤ 1`. -/
lemma one_add_add_half_sq_sub_le_exp {x : ℝ} (hx : |x| ≤ 1) :
    1 + x + x ^ 2 / 2 - |x| ^ 3 ≤ Real.exp x := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, x ^ m / (Nat.factorial m) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum, abs_le] at h
  have hc : |x| ^ 3 * ((3 : ℕ).succ / ((Nat.factorial 3) * 3)) ≤ |x| ^ 3 := by
    have h0 : (0 : ℝ) ≤ |x| ^ 3 := by positivity
    have : ((3 : ℕ).succ : ℝ) / ((Nat.factorial 3 : ℕ) * 3) ≤ 1 := by
      norm_num [Nat.factorial]
    nlinarith
  linarith [h.1]

/-- **The two-atom moment generating function, from above**: with mean `m` and second moment `v`,
`π e^{λa} + (1-π) e^{λb} ≤ exp(λm + λ²v)`. -/
lemma twoAtom_mgf_le {π a b l : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (ha : |l * a| ≤ 1) (hb : |l * b| ≤ 1) :
    π * Real.exp (l * a) + (1 - π) * Real.exp (l * b)
      ≤ Real.exp (l * (π * a + (1 - π) * b) + l ^ 2 * (π * a ^ 2 + (1 - π) * b ^ 2)) := by
  have h1 : Real.exp (l * a) ≤ 1 + l * a + (l * a) ^ 2 := exp_le_one_add_add_sq ha
  have h2 : Real.exp (l * b) ≤ 1 + l * b + (l * b) ^ 2 := exp_le_one_add_add_sq hb
  have hstep : π * Real.exp (l * a) + (1 - π) * Real.exp (l * b)
      ≤ 1 + (l * (π * a + (1 - π) * b) + l ^ 2 * (π * a ^ 2 + (1 - π) * b ^ 2)) := by
    have h1' : π * Real.exp (l * a) ≤ π * (1 + l * a + (l * a) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hπ0
    have h2' : (1 - π) * Real.exp (l * b) ≤ (1 - π) * (1 + l * b + (l * b) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h3 : π * (1 + l * a + (l * a) ^ 2) + (1 - π) * (1 + l * b + (l * b) ^ 2)
        = 1 + (l * (π * a + (1 - π) * b) + l ^ 2 * (π * a ^ 2 + (1 - π) * b ^ 2)) := by ring
    linarith
  refine le_trans hstep ?_
  linarith [Real.add_one_le_exp (l * (π * a + (1 - π) * b)
    + l ^ 2 * (π * a ^ 2 + (1 - π) * b ^ 2))]

/-- **The two-atom moment generating function, from below**: `exp(λm + λ²v/8) ≤ π e^{λa} +
(1-π)e^{λb}`, for atoms of size at most `s` with `|λ|s ≤ 1/4`, a mean small against the second
moment (`32m² ≤ v`) and `λ²v ≤ 1/2`. -/
lemma twoAtom_mgf_ge {π a b l s : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hs0 : 0 ≤ s)
    (ha : |a| ≤ s) (hb : |b| ≤ s) (hls : |l| * s ≤ 1 / 4)
    (hmv : 32 * (π * a + (1 - π) * b) ^ 2 ≤ π * a ^ 2 + (1 - π) * b ^ 2)
    (hlv : l ^ 2 * (π * a ^ 2 + (1 - π) * b ^ 2) ≤ 1 / 2) :
    Real.exp (l * (π * a + (1 - π) * b) + l ^ 2 * (π * a ^ 2 + (1 - π) * b ^ 2) / 8)
      ≤ π * Real.exp (l * a) + (1 - π) * Real.exp (l * b) := by
  set m : ℝ := π * a + (1 - π) * b with hm_def
  set v : ℝ := π * a ^ 2 + (1 - π) * b ^ 2 with hv_def
  have hπ1' : (0 : ℝ) ≤ 1 - π := by linarith
  have hv0 : 0 ≤ v := by rw [hv_def]; positivity
  have hl0 : 0 ≤ |l| := abs_nonneg l
  have hlv0 : 0 ≤ l ^ 2 * v := by positivity
  have hla : |l * a| ≤ 1 := by
    rw [abs_mul]
    calc |l| * |a| ≤ |l| * s := mul_le_mul_of_nonneg_left ha hl0
      _ ≤ 1 / 4 := hls
      _ ≤ 1 := by norm_num
  have hlb : |l * b| ≤ 1 := by
    rw [abs_mul]
    calc |l| * |b| ≤ |l| * s := mul_le_mul_of_nonneg_left hb hl0
      _ ≤ 1 / 4 := hls
      _ ≤ 1 := by norm_num
  -- the cubic lower bound at each atom, with the cube traded for the square
  have hcubeA : |l * a| ^ 3 ≤ |l| * s * (l ^ 2 * a ^ 2) := by
    have hid : |l * a| ^ 3 = |l| * |a| * (l ^ 2 * a ^ 2) := by
      rw [abs_mul, ← sq_abs l, ← sq_abs a]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hl0) (by positivity)
  have hcubeB : |l * b| ^ 3 ≤ |l| * s * (l ^ 2 * b ^ 2) := by
    have hid : |l * b| ^ 3 = |l| * |b| * (l ^ 2 * b ^ 2) := by
      rw [abs_mul, ← sq_abs l, ← sq_abs b]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hl0) (by positivity)
  have hcube : π * |l * a| ^ 3 + (1 - π) * |l * b| ^ 3 ≤ l ^ 2 * v / 4 := by
    have h1 : π * |l * a| ^ 3 ≤ π * (|l| * s * (l ^ 2 * a ^ 2)) :=
      mul_le_mul_of_nonneg_left hcubeA hπ0
    have h2 : (1 - π) * |l * b| ^ 3 ≤ (1 - π) * (|l| * s * (l ^ 2 * b ^ 2)) :=
      mul_le_mul_of_nonneg_left hcubeB hπ1'
    have h3 : π * (|l| * s * (l ^ 2 * a ^ 2)) + (1 - π) * (|l| * s * (l ^ 2 * b ^ 2))
        = |l| * s * (l ^ 2 * v) := by rw [hv_def]; ring
    have h4 : |l| * s * (l ^ 2 * v) ≤ 1 / 4 * (l ^ 2 * v) :=
      mul_le_mul_of_nonneg_right hls hlv0
    linarith
  have hkey : 1 + l * m + l ^ 2 * v / 4
      ≤ π * Real.exp (l * a) + (1 - π) * Real.exp (l * b) := by
    have hA := one_add_add_half_sq_sub_le_exp hla
    have hB := one_add_add_half_sq_sub_le_exp hlb
    have h1 : π * (1 + l * a + (l * a) ^ 2 / 2 - |l * a| ^ 3) ≤ π * Real.exp (l * a) :=
      mul_le_mul_of_nonneg_left hA hπ0
    have h2 : (1 - π) * (1 + l * b + (l * b) ^ 2 / 2 - |l * b| ^ 3)
        ≤ (1 - π) * Real.exp (l * b) := mul_le_mul_of_nonneg_left hB hπ1'
    have h3 : π * (1 + l * a + (l * a) ^ 2 / 2) + (1 - π) * (1 + l * b + (l * b) ^ 2 / 2)
        = 1 + l * m + l ^ 2 * v / 2 := by rw [hm_def, hv_def]; ring
    linarith
  -- the exponent is below that bound
  have ha2 : a ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs a]
    exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hvs : v ≤ s ^ 2 := by
    have h1 : π * a ^ 2 ≤ π * s ^ 2 := mul_le_mul_of_nonneg_left ha2 hπ0
    have h2 : (1 - π) * b ^ 2 ≤ (1 - π) * s ^ 2 := mul_le_mul_of_nonneg_left hb2 hπ1'
    rw [hv_def]
    nlinarith
  have hm2 : m ^ 2 ≤ v / 32 := by linarith
  have hls2 : l ^ 2 * s ^ 2 ≤ 1 / 16 := by
    have h1 : (|l| * s) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hls 2
    have h2 : (|l| * s) ^ 2 = l ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
    rw [h2] at h1
    linarith
  have hlmsq : (l * m) ^ 2 ≤ 1 / 512 := by
    have h1 : l ^ 2 * m ^ 2 ≤ l ^ 2 * (s ^ 2 / 32) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg l)
    have h2 : (l * m) ^ 2 = l ^ 2 * m ^ 2 := by ring
    linarith [h2 ▸ h1]
  have hz1 : |l * m + l ^ 2 * v / 8| ≤ 1 := by
    have h1 : |l * m| ≤ 1 / 22 := by
      nlinarith [abs_nonneg (l * m), sq_abs (l * m)]
    have h2 : l ^ 2 * v / 8 ≤ 1 / 16 := by linarith
    have h3 : (0 : ℝ) ≤ l ^ 2 * v / 8 := by positivity
    have h4 : |l * m + l ^ 2 * v / 8| ≤ |l * m| + |l ^ 2 * v / 8| := abs_add_le _ _
    rw [abs_of_nonneg h3] at h4
    linarith
  have hzsq : (l * m + l ^ 2 * v / 8) ^ 2 ≤ l ^ 2 * v / 8 := by
    have h1 : (l * m) ^ 2 ≤ l ^ 2 * v / 32 := by
      have hh : l ^ 2 * m ^ 2 ≤ l ^ 2 * (v / 32) := mul_le_mul_of_nonneg_left hm2 (sq_nonneg l)
      have hid : (l * m) ^ 2 = l ^ 2 * m ^ 2 := by ring
      rw [hid]
      linarith
    have hsq : (l ^ 2 * v) * (l ^ 2 * v) ≤ 1 / 2 * (l ^ 2 * v) :=
      mul_le_mul_of_nonneg_right hlv hlv0
    have h2 : (l ^ 2 * v / 8) ^ 2 ≤ l ^ 2 * v / 128 := by
      have hid : (l ^ 2 * v / 8) ^ 2 = (l ^ 2 * v) * (l ^ 2 * v) / 64 := by ring
      rw [hid]
      linarith
    have hsplit : (l * m + l ^ 2 * v / 8) ^ 2 ≤ 2 * (l * m) ^ 2 + 2 * (l ^ 2 * v / 8) ^ 2 := by
      nlinarith [sq_nonneg (l * m - l ^ 2 * v / 8)]
    linarith
  have hexp : Real.exp (l * m + l ^ 2 * v / 8)
      ≤ 1 + (l * m + l ^ 2 * v / 8) + (l * m + l ^ 2 * v / 8) ^ 2 :=
    exp_le_one_add_add_sq hz1
  linarith

/-! ### The twisted law at one prime

Under the twist by `‖1+zp^{-s}‖²/‖1+zp^{-σ}‖` the value at `p` still has two atoms, with weights
proportional to `W^± = ((1±u)² ∓ 2ud)/(1±u)`, `u = p^{-1/2-σ}`, `d = 1 - cos(h log p)`.  The atom
`+1` therefore carries `RMF.twistPi u d`, and the mean of `log‖1 + zp^{-σ}‖` under it is
`(u² - 4u²d)/2 + O(u³)`: the drift `u²/2` of the exponent-`1` tilt, reduced by the twist. -/

/-- The weight of the atom `X_p = 1` under the twisted law at one prime, as a function of
`u = p^{-1/2-σ}` and `d = 1 - cos(h log p)`. -/
noncomputable def twistPi (u d : ℝ) : ℝ :=
  ((1 + u) ^ 2 - 2 * u * d) * (1 - u) / (2 * (1 - u ^ 2) + 4 * u ^ 2 * d)

section TwistPrime

variable {u d : ℝ}

lemma twistDen_pos (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) :
    (0 : ℝ) < 2 * (1 - u ^ 2) + 4 * u ^ 2 * d := by
  have h1 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have h2 : (0 : ℝ) ≤ 4 * u ^ 2 * d := by positivity
  linarith

lemma twistNum_pos_nonneg (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd2 : d ≤ 2) :
    (0 : ℝ) ≤ ((1 + u) ^ 2 - 2 * u * d) * (1 - u) := by
  have h1 : (0 : ℝ) ≤ 1 - u := by linarith
  have h2 : (0 : ℝ) ≤ (1 + u) ^ 2 - 2 * u * d := by nlinarith
  positivity

lemma twistNum_neg_nonneg (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) :
    (0 : ℝ) ≤ ((1 - u) ^ 2 + 2 * u * d) * (1 + u) := by
  have h1 : (0 : ℝ) ≤ 1 + u := by linarith
  have h2 : (0 : ℝ) ≤ (1 - u) ^ 2 + 2 * u * d := by positivity
  positivity

/-- The two atom weights sum to one. -/
lemma one_sub_twistPi (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) :
    1 - twistPi u d = ((1 - u) ^ 2 + 2 * u * d) * (1 + u) / (2 * (1 - u ^ 2) + 4 * u ^ 2 * d) := by
  have hD := twistDen_pos hu0 hu hd0
  rw [twistPi, eq_div_iff (ne_of_gt hD), sub_mul, div_mul_cancel₀ _ (ne_of_gt hD)]
  ring

lemma twistPi_nonneg (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    0 ≤ twistPi u d :=
  div_nonneg (twistNum_pos_nonneg hu0 hu hd2) (twistDen_pos hu0 hu hd0).le

lemma twistPi_le_one (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (_hd2 : d ≤ 2) :
    twistPi u d ≤ 1 := by
  have h := one_sub_twistPi hu0 hu hd0
  have h2 : (0 : ℝ) ≤ ((1 - u) ^ 2 + 2 * u * d) * (1 + u)
      / (2 * (1 - u ^ 2) + 4 * u ^ 2 * d) :=
    div_nonneg (twistNum_neg_nonneg hu0 hu hd0) (twistDen_pos hu0 hu hd0).le
  linarith

/-! ### The logarithm at the two atoms -/

/-- `|log(1+u) - (u - u²/2)| ≤ 2u³` for `0 < u ≤ 1/2`. -/
lemma abs_log_one_add_sub_quad_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * u ^ 3 := by
  have habs : |(-u : ℝ)| < 1 := by rw [abs_neg, abs_of_pos hu0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  have hsum : ∑ i ∈ Finset.range 2, (-u : ℝ) ^ (i + 1) / (i + 1) = -u + u ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum, show (1 : ℝ) - -u = 1 + u by ring, abs_neg, abs_of_pos hu0] at h
  have hd : u ^ 3 / (1 - u) ≤ 2 * u ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_pos hu0 3]
  have hrw : |Real.log (1 + u) - (u - u ^ 2 / 2)| = |-u + u ^ 2 / 2 + Real.log (1 + u)| := by
    congr 1
    ring
  rw [hrw]
  linarith

/-- `|log(1-u) - (-u - u²/2)| ≤ 2u³` for `0 < u ≤ 1/2`. -/
lemma abs_log_one_sub_sub_quad_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |Real.log (1 - u) - (-u - u ^ 2 / 2)| ≤ 2 * u ^ 3 := by
  have habs : |u| < 1 := by rw [abs_of_pos hu0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  have hsum : ∑ i ∈ Finset.range 2, (u : ℝ) ^ (i + 1) / (i + 1) = u + u ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum, abs_of_pos hu0] at h
  have hd : u ^ 3 / (1 - u) ≤ 2 * u ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_pos hu0 3]
  have hrw : |Real.log (1 - u) - (-u - u ^ 2 / 2)| = |u + u ^ 2 / 2 + Real.log (1 - u)| := by
    congr 1
    ring
  rw [hrw]
  linarith

/-- If `x` is within `2u³` of `u + cu²/2` with `|c| ≤ 1`, then `x²` is within `2u³` of `u²`. -/
lemma abs_sq_sub_sq_le_of_close {x u c : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hc : |c| ≤ 1)
    (hlo : u + c * u ^ 2 / 2 - 2 * u ^ 3 ≤ x) (hhi : x ≤ u + c * u ^ 2 / 2 + 2 * u ^ 3) :
    |x ^ 2 - u ^ 2| ≤ 2 * u ^ 3 := by
  rw [abs_le] at hc
  have h0 : 0 ≤ u + c * u ^ 2 / 2 - 2 * u ^ 3 := by nlinarith
  have h3 : 0 ≤ x := by linarith
  have hsq1 : x * x ≤ (u + c * u ^ 2 / 2 + 2 * u ^ 3) * (u + c * u ^ 2 / 2 + 2 * u ^ 3) :=
    mul_self_le_mul_self h3 hhi
  have hsq2 : (u + c * u ^ 2 / 2 - 2 * u ^ 3) * (u + c * u ^ 2 / 2 - 2 * u ^ 3) ≤ x * x :=
    mul_self_le_mul_self h0 hlo
  have hsqx : x ^ 2 = x * x := sq x
  rw [abs_le, hsqx]
  constructor <;> nlinarith [pow_pos hu0 3, pow_pos hu0 4, pow_pos hu0 5, hc.1, hc.2]

/-! ### The mean and the second moment under the twisted law -/

/-- **The drift at one prime**: the mean of `log‖1 + zp^{-σ}‖` under the twisted law is
`(u² - 4u²d)/2 + O(u³)`.  At `d = 0` this is the `u²/2` of the untwisted exponent-1 tilt; the
twist subtracts `2u²d`. -/
lemma abs_twistMean_sub_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    |twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u)
        - (u ^ 2 - 4 * u ^ 2 * d) / 2| ≤ 9 * u ^ 3 := by
  have hu2 : u ≤ 1 / 2 := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hu4 : (0 : ℝ) < u ^ 4 := pow_pos hu0 4
  have hE₁ := abs_log_one_add_sub_quad_le hu0 hu2
  have hE₂ := abs_log_one_sub_sub_quad_le hu0 hu2
  rw [abs_le] at hE₁ hE₂
  have hD := twistDen_pos hu0 hu hd0
  have hA0 := twistNum_pos_nonneg hu0 hu hd2
  have hB0 := twistNum_neg_nonneg hu0 hu hd0
  have hAle : ((1 + u) ^ 2 - 2 * u * d) * (1 - u) ≤ 2 := by nlinarith
  have hBle : ((1 - u) ^ 2 + 2 * u * d) * (1 + u) ≤ 2 := by nlinarith
  have hD1 : (1 : ℝ) ≤ 2 * (1 - u ^ 2) + 4 * u ^ 2 * d := by nlinarith
  have hdd : |d * (d - 1)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hmean : twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u)
      = (((1 + u) ^ 2 - 2 * u * d) * (1 - u) * Real.log (1 + u)
          + ((1 - u) ^ 2 + 2 * u * d) * (1 + u) * Real.log (1 - u))
        / (2 * (1 - u ^ 2) + 4 * u ^ 2 * d) := by
    rw [one_sub_twistPi hu0 hu hd0, twistPi]
    field_simp
  have hpoly : ((1 + u) ^ 2 - 2 * u * d) * (1 - u) * (u - u ^ 2 / 2)
      + ((1 - u) ^ 2 + 2 * u * d) * (1 + u) * (-u - u ^ 2 / 2)
      - (u ^ 2 - 4 * u ^ 2 * d) / 2 * (2 * (1 - u ^ 2) + 4 * u ^ 2 * d)
      = 8 * u ^ 4 * (d * (d - 1)) := by ring
  rw [hmean]
  clear hmean
  set A : ℝ := ((1 + u) ^ 2 - 2 * u * d) * (1 - u) with hA_def
  set B : ℝ := ((1 - u) ^ 2 + 2 * u * d) * (1 + u) with hB_def
  set D : ℝ := 2 * (1 - u ^ 2) + 4 * u ^ 2 * d with hD_def
  set a : ℝ := Real.log (1 + u) with ha_def
  set b : ℝ := Real.log (1 - u) with hb_def
  clear_value A B D a b
  clear hA_def hB_def hD_def ha_def hb_def
  -- the numerator, against the main term
  have hsplit : A * a + B * b - (u ^ 2 - 4 * u ^ 2 * d) / 2 * D
      = 8 * u ^ 4 * (d * (d - 1)) + (A * (a - (u - u ^ 2 / 2)) + B * (b - (-u - u ^ 2 / 2))) := by
    rw [← hpoly]
    ring
  have h1 : |8 * u ^ 4 * (d * (d - 1))| ≤ 16 * u ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * u ^ 4)]
    nlinarith
  have h2 : |A * (a - (u - u ^ 2 / 2))| ≤ 4 * u ^ 3 := by
    have hab : |a - (u - u ^ 2 / 2)| ≤ 2 * u ^ 3 := abs_le.2 ⟨hE₁.1, hE₁.2⟩
    rw [abs_mul, abs_of_nonneg hA0]
    nlinarith [abs_nonneg (a - (u - u ^ 2 / 2))]
  have h3 : |B * (b - (-u - u ^ 2 / 2))| ≤ 4 * u ^ 3 := by
    have hab : |b - (-u - u ^ 2 / 2)| ≤ 2 * u ^ 3 := abs_le.2 ⟨hE₂.1, hE₂.2⟩
    rw [abs_mul, abs_of_nonneg hB0]
    nlinarith [abs_nonneg (b - (-u - u ^ 2 / 2))]
  have h4 := abs_add_le (A * (a - (u - u ^ 2 / 2))) (B * (b - (-u - u ^ 2 / 2)))
  have h5 := abs_add_le (8 * u ^ 4 * (d * (d - 1)))
    (A * (a - (u - u ^ 2 / 2)) + B * (b - (-u - u ^ 2 / 2)))
  have hnum : |A * a + B * b - (u ^ 2 - 4 * u ^ 2 * d) / 2 * D| ≤ 9 * u ^ 3 := by
    rw [hsplit]
    have h16 : 16 * u ≤ 1 := by linarith
    have h6 : 16 * u ^ 4 ≤ u ^ 3 :=
      calc 16 * u ^ 4 = 16 * u * u ^ 3 := by ring
        _ ≤ 1 * u ^ 3 := mul_le_mul_of_nonneg_right h16 hu3.le
        _ = u ^ 3 := one_mul _
    linarith
  -- divide by the denominator
  have hdiv : (A * a + B * b) / D - (u ^ 2 - 4 * u ^ 2 * d) / 2
      = (A * a + B * b - (u ^ 2 - 4 * u ^ 2 * d) / 2 * D) / D := by
    rw [eq_div_iff (ne_of_gt hD), sub_mul, div_mul_cancel₀ _ (ne_of_gt hD)]
  rw [hdiv, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hfin : 9 * u ^ 3 * 1 ≤ 9 * u ^ 3 * D := mul_le_mul_of_nonneg_left hD1 (by positivity)
  linarith

/-- **The second moment at one prime**: `u² + O(u³)`. -/
lemma abs_twistVar_sub_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    |twistPi u d * Real.log (1 + u) ^ 2 + (1 - twistPi u d) * Real.log (1 - u) ^ 2 - u ^ 2|
      ≤ u ^ 2 / 2 := by
  have hu2 : u ≤ 1 / 2 := by linarith
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hE₁ := abs_log_one_add_sub_quad_le hu0 hu2
  have hE₂ := abs_log_one_sub_sub_quad_le hu0 hu2
  rw [abs_le] at hE₁ hE₂
  have hD := twistDen_pos hu0 hu hd0
  have hA0 := twistNum_pos_nonneg hu0 hu hd2
  have hB0 := twistNum_neg_nonneg hu0 hu hd0
  have hAle : ((1 + u) ^ 2 - 2 * u * d) * (1 - u) ≤ 2 := by nlinarith
  have hBle : ((1 - u) ^ 2 + 2 * u * d) * (1 + u) ≤ 2 := by nlinarith
  have hD1 : (1 : ℝ) ≤ 2 * (1 - u ^ 2) + 4 * u ^ 2 * d := by nlinarith
  have hAB : ((1 + u) ^ 2 - 2 * u * d) * (1 - u) + ((1 - u) ^ 2 + 2 * u * d) * (1 + u)
      = 2 * (1 - u ^ 2) + 4 * u ^ 2 * d := by ring
  have hmean : twistPi u d * Real.log (1 + u) ^ 2 + (1 - twistPi u d) * Real.log (1 - u) ^ 2
      = (((1 + u) ^ 2 - 2 * u * d) * (1 - u) * Real.log (1 + u) ^ 2
          + ((1 - u) ^ 2 + 2 * u * d) * (1 + u) * Real.log (1 - u) ^ 2)
        / (2 * (1 - u ^ 2) + 4 * u ^ 2 * d) := by
    rw [one_sub_twistPi hu0 hu hd0, twistPi]
    field_simp
  rw [hmean]
  clear hmean
  set A : ℝ := ((1 + u) ^ 2 - 2 * u * d) * (1 - u) with hA_def
  set B : ℝ := ((1 - u) ^ 2 + 2 * u * d) * (1 + u) with hB_def
  set D : ℝ := 2 * (1 - u ^ 2) + 4 * u ^ 2 * d with hD_def
  set a : ℝ := Real.log (1 + u) with ha_def
  set b : ℝ := Real.log (1 - u) with hb_def
  clear_value A B D a b
  clear hA_def hB_def hD_def ha_def hb_def
  -- each atom's square is `u² + O(u³)`
  have hasq : |a ^ 2 - u ^ 2| ≤ 2 * u ^ 3 :=
    abs_sq_sub_sq_le_of_close (c := -1) hu0 hu (by rw [abs_neg, abs_one])
      (by linarith [hE₁.1]) (by linarith [hE₁.2])
  have hbsq : |b ^ 2 - u ^ 2| ≤ 2 * u ^ 3 := by
    have hneg : |(-b) ^ 2 - u ^ 2| ≤ 2 * u ^ 3 :=
      abs_sq_sub_sq_le_of_close (c := 1) hu0 hu (by rw [abs_one])
        (by linarith [hE₂.2]) (by linarith [hE₂.1])
    rwa [show (-b) ^ 2 = b ^ 2 by ring] at hneg
  have hsplit : A * a ^ 2 + B * b ^ 2 - u ^ 2 * D
      = A * (a ^ 2 - u ^ 2) + B * (b ^ 2 - u ^ 2) := by
    rw [← hAB]
    ring
  have h1 : |A * (a ^ 2 - u ^ 2)| ≤ 4 * u ^ 3 := by
    rw [abs_mul, abs_of_nonneg hA0]
    nlinarith [abs_nonneg (a ^ 2 - u ^ 2)]
  have h2 : |B * (b ^ 2 - u ^ 2)| ≤ 4 * u ^ 3 := by
    rw [abs_mul, abs_of_nonneg hB0]
    nlinarith [abs_nonneg (b ^ 2 - u ^ 2)]
  have h3 := abs_add_le (A * (a ^ 2 - u ^ 2)) (B * (b ^ 2 - u ^ 2))
  have hnum : |A * a ^ 2 + B * b ^ 2 - u ^ 2 * D| ≤ 8 * u ^ 3 := by
    rw [hsplit]
    linarith
  have hdiv : (A * a ^ 2 + B * b ^ 2) / D - u ^ 2
      = (A * a ^ 2 + B * b ^ 2 - u ^ 2 * D) / D := by
    rw [eq_div_iff (ne_of_gt hD), sub_mul, div_mul_cancel₀ _ (ne_of_gt hD)]
  rw [hdiv, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have h8 : 8 * u ^ 3 ≤ u ^ 2 / 2 := by nlinarith [pow_pos hu0 3]
  have hfin : u ^ 2 / 2 * 1 ≤ u ^ 2 / 2 * D := mul_le_mul_of_nonneg_left hD1 (by positivity)
  linarith

end TwistPrime

/-! ### The twisted weight at one prime, integrated

`E[e^{λ log‖1+zp^{-σ}‖}·‖1+zp^{-s}‖²/‖1+zp^{-σ}‖]` is the product of the normalisation
`1 + 2u²d/(1-u²)` and the two-atom moment generating function with weight `RMF.twistPi u d`. -/

/-- **The twisted weight at one prime, with an exponential factor.**  At `l = 0` this is the
normalisation `1 + 2u²d/(1-u²) ≥ 1` of the twist itself. -/
lemma integral_exp_mul_twistWeight_rademacherLaw {p : ℕ} (hp : 5 ≤ p) {σ h l : ℝ} (hσ : 0 ≤ σ) :
    (∫ z, Real.exp (l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
        * (‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
        ∂rademacherLaw)
      = (1 + 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
            / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2))
        * (twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))
              * Real.exp (l * Real.log (1 + (p : ℝ) ^ (-(1 / 2 + σ))))
            + (1 - twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p)))
              * Real.exp (l * Real.log (1 - (p : ℝ) ^ (-(1 / 2 + σ))))) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu_def
  set d : ℝ := 1 - Real.cos (h * Real.log p) with hd_def
  have hu0 : 0 < u := Real.rpow_pos_of_pos hpR _
  have hu2 : u ≤ 1 / 2 := rpow_neg_half_add_le_half hp hσ
  have hd0 : 0 ≤ d := by rw [hd_def]; linarith [Real.cos_le_one (h * Real.log p)]
  have hd2 : d ≤ 2 := by rw [hd_def]; linarith [Real.neg_one_le_cos (h * Real.log p)]
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h1u' : (0 : ℝ) < 1 - u := by linarith
  have hsq : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
  have hD : (0 : ℝ) < 2 * (1 - u ^ 2) + 4 * u ^ 2 * d := by nlinarith
  -- the two atoms
  have hnorm0pos : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 + u := by
    rw [one_mul, cpow_neg_shiftLine_zero p σ, ← hu_def,
      show (1 : ℂ) + ((u : ℝ) : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnorm0neg : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 - u := by
    rw [cpow_neg_shiftLine_zero p σ, ← hu_def,
      show (1 : ℂ) + (-1) * ((u : ℝ) : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnormhpos : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 = (1 + u) ^ 2 - 2 * u * d := by
    rw [norm_one_add_mul_sq_eq (by simp), one_mul, re_cpow_neg_shiftLine hp0,
      norm_cpow_neg_shiftLine hp0, ← hu_def, hd_def]
    ring
  have hnormhneg : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 = (1 - u) ^ 2 + 2 * u * d := by
    have hrw : ((-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)).re
        = -((p : ℂ) ^ (-shiftLine σ h)).re := by simp
    rw [norm_one_add_mul_sq_eq (by simp), hrw, re_cpow_neg_shiftLine hp0,
      norm_cpow_neg_shiftLine hp0, ← hu_def, hd_def]
    ring
  rw [integral_rademacherLaw_eq]
  simp only [smul_eq_mul]
  rw [hnorm0pos, hnorm0neg, hnormhpos, hnormhneg, twistPi]
  have h1 : (1 + u) ≠ 0 := ne_of_gt h1u
  have h2 : (1 - u) ≠ 0 := ne_of_gt h1u'
  have h3 : (1 - u ^ 2) ≠ 0 := ne_of_gt hsq
  have h4 : (2 * (1 - u ^ 2) + 4 * u ^ 2 * d) ≠ 0 := ne_of_gt hD
  field_simp
  ring

/-! ### The moment generating function at one prime

Three bounds, all instances of the two-atom estimates with the mean and second moment of
`RMF.abs_twistMean_sub_le` and `RMF.abs_twistVar_sub_le`.  Every bound is an exponential of a
multiple of `u²`, so products over a range of primes are exponentials of `∑_p u_p²`. -/

section TwistMGF

variable {u d l : ℝ}

/-- The two atoms are at most `2u` in size. -/
lemma abs_log_one_add_le_two_mul (hu0 : 0 < u) (hu : u ≤ 1 / 200) :
    |Real.log (1 + u)| ≤ 2 * u := by
  have h1 : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + u)
    linarith
  have h2 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg h2]
  linarith

lemma abs_log_one_sub_le_two_mul (hu0 : 0 < u) (hu : u ≤ 1 / 200) :
    |Real.log (1 - u)| ≤ 2 * u := by
  have hE := abs_log_one_sub_sub_quad_le hu0 (by linarith)
  rw [abs_le] at hE
  have h2 : Real.log (1 - u) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rw [abs_of_nonpos h2]
  nlinarith [pow_pos hu0 3]

/-- The mean is between `-5u²` and `5u²`. -/
lemma abs_twistMean_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    |twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u)| ≤ 5 * u ^ 2 := by
  have h := abs_twistMean_sub_le hu0 hu hd0 hd2
  rw [abs_le] at h ⊢
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have h9 : 9 * u ^ 3 ≤ u ^ 2 / 2 := by nlinarith
  have hM : |(u ^ 2 - 4 * u ^ 2 * d) / 2| ≤ 4.5 * u ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg u]
  rw [abs_le] at hM
  constructor <;> linarith [h.1, h.2, hM.1, hM.2]

/-- On a prime where the twist is small (`d ≤ 1/24`), the drift is at least `u²/5`. -/
lemma twistMean_ge_of_small (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 24) :
    u ^ 2 / 5 ≤ twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u) := by
  have h := abs_twistMean_sub_le hu0 hu hd0 (by linarith)
  rw [abs_le] at h
  have hu3 : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have h9 : 9 * u ^ 3 ≤ u ^ 2 / 20 := by nlinarith
  nlinarith [h.1, sq_nonneg u]

/-- The second moment is between `u²/2` and `2u²`. -/
lemma twistVar_bounds (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    u ^ 2 / 2 ≤ twistPi u d * Real.log (1 + u) ^ 2 + (1 - twistPi u d) * Real.log (1 - u) ^ 2
      ∧ twistPi u d * Real.log (1 + u) ^ 2 + (1 - twistPi u d) * Real.log (1 - u) ^ 2
        ≤ 2 * u ^ 2 := by
  have h := abs_twistVar_sub_le hu0 hu hd0 hd2
  rw [abs_le] at h
  constructor <;> nlinarith [h.1, h.2, sq_nonneg u]

/-- **The moment generating function at one prime, from above.** -/
lemma twistMGF_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (hl0 : 0 ≤ l) (hlu : l * (2 * u) ≤ 1 / 4) :
    twistPi u d * Real.exp (l * Real.log (1 + u))
        + (1 - twistPi u d) * Real.exp (l * Real.log (1 - u))
      ≤ Real.exp (l * (5 * u ^ 2) + l ^ 2 * (2 * u ^ 2)) := by
  have hπ0 := twistPi_nonneg hu0 hu hd0 hd2
  have hπ1 := twistPi_le_one hu0 hu hd0 hd2
  have hA := abs_log_one_add_le_two_mul hu0 hu
  have hB := abs_log_one_sub_le_two_mul hu0 hu
  have hla : |l * Real.log (1 + u)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hl0]
    calc l * |Real.log (1 + u)| ≤ l * (2 * u) := mul_le_mul_of_nonneg_left hA hl0
      _ ≤ 1 / 4 := hlu
      _ ≤ 1 := by norm_num
  have hlb : |l * Real.log (1 - u)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hl0]
    calc l * |Real.log (1 - u)| ≤ l * (2 * u) := mul_le_mul_of_nonneg_left hB hl0
      _ ≤ 1 / 4 := hlu
      _ ≤ 1 := by norm_num
  refine le_trans (twoAtom_mgf_le hπ0 hπ1 hla hlb) (Real.exp_le_exp.2 ?_)
  have hm := abs_twistMean_le hu0 hu hd0 hd2
  rw [abs_le] at hm
  have hv := twistVar_bounds hu0 hu hd0 hd2
  have h1 : l * (twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u))
      ≤ l * (5 * u ^ 2) := mul_le_mul_of_nonneg_left hm.2 hl0
  have h2 : l ^ 2 * (twistPi u d * Real.log (1 + u) ^ 2 + (1 - twistPi u d) * Real.log (1 - u) ^ 2)
      ≤ l ^ 2 * (2 * u ^ 2) := mul_le_mul_of_nonneg_left hv.2 (sq_nonneg l)
  linarith

/-- **The moment generating function at one prime with a negative exponent**, where the twist is
small: the drift `u²/5` works for us. -/
lemma twistMGF_neg_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 24)
    (hl0 : 0 ≤ l) (hlu : l * (2 * u) ≤ 1 / 4) :
    twistPi u d * Real.exp (-l * Real.log (1 + u))
        + (1 - twistPi u d) * Real.exp (-l * Real.log (1 - u))
      ≤ Real.exp (-l * (u ^ 2 / 5) + l ^ 2 * (2 * u ^ 2)) := by
  have hd2 : d ≤ 2 := by linarith
  have hπ0 := twistPi_nonneg hu0 hu hd0 hd2
  have hπ1 := twistPi_le_one hu0 hu hd0 hd2
  have hA := abs_log_one_add_le_two_mul hu0 hu
  have hB := abs_log_one_sub_le_two_mul hu0 hu
  have hla : |(-l) * Real.log (1 + u)| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hl0]
    calc l * |Real.log (1 + u)| ≤ l * (2 * u) := mul_le_mul_of_nonneg_left hA hl0
      _ ≤ 1 / 4 := hlu
      _ ≤ 1 := by norm_num
  have hlb : |(-l) * Real.log (1 - u)| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hl0]
    calc l * |Real.log (1 - u)| ≤ l * (2 * u) := mul_le_mul_of_nonneg_left hB hl0
      _ ≤ 1 / 4 := hlu
      _ ≤ 1 := by norm_num
  refine le_trans (twoAtom_mgf_le hπ0 hπ1 hla hlb) (Real.exp_le_exp.2 ?_)
  have hm := twistMean_ge_of_small hu0 hu hd0 hd
  have hv := twistVar_bounds hu0 hu hd0 hd2
  have h1 : -l * (twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u))
      ≤ -l * (u ^ 2 / 5) := by
    have := mul_le_mul_of_nonneg_left hm hl0
    nlinarith
  have h2 : (-l) ^ 2 * (twistPi u d * Real.log (1 + u) ^ 2
        + (1 - twistPi u d) * Real.log (1 - u) ^ 2)
      ≤ l ^ 2 * (2 * u ^ 2) := by
    have hsq : (-l) ^ 2 = l ^ 2 := by ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hv.2 (sq_nonneg l)
  linarith

/-- **The moment generating function at one prime, from below.** -/
lemma twistMGF_ge (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (hl0 : 0 ≤ l) (hlu : l * (2 * u) ≤ 1 / 4) (hlv : l ^ 2 * (2 * u ^ 2) ≤ 1 / 2) :
    Real.exp (-l * (5 * u ^ 2) + l ^ 2 * (u ^ 2 / 16))
      ≤ twistPi u d * Real.exp (l * Real.log (1 + u))
        + (1 - twistPi u d) * Real.exp (l * Real.log (1 - u)) := by
  have hπ0 := twistPi_nonneg hu0 hu hd0 hd2
  have hπ1 := twistPi_le_one hu0 hu hd0 hd2
  have hA := abs_log_one_add_le_two_mul hu0 hu
  have hB := abs_log_one_sub_le_two_mul hu0 hu
  have hm := abs_twistMean_le hu0 hu hd0 hd2
  have hv := twistVar_bounds hu0 hu hd0 hd2
  have hu2 : (0 : ℝ) < u ^ 2 := pow_pos hu0 2
  have hls : |l| * (2 * u) ≤ 1 / 4 := by rwa [abs_of_nonneg hl0]
  -- the hypotheses of the two-atom bound
  have hmv : 32 * (twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u)) ^ 2
      ≤ twistPi u d * Real.log (1 + u) ^ 2 + (1 - twistPi u d) * Real.log (1 - u) ^ 2 := by
    rw [abs_le] at hm
    have hsq : (twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u)) ^ 2
        ≤ (5 * u ^ 2) ^ 2 := by nlinarith [hm.1, hm.2]
    have hfin : 32 * (5 * u ^ 2) ^ 2 ≤ u ^ 2 / 2 := by
      have h1 : u ^ 2 ≤ 1 / 40000 := by nlinarith
      calc 32 * (5 * u ^ 2) ^ 2 = 800 * (u ^ 2 * u ^ 2) := by ring
        _ ≤ 800 * (1 / 40000 * u ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hu2.le) (by norm_num)
        _ ≤ u ^ 2 / 2 := by linarith
    linarith [hv.1]
  have hlv' : l ^ 2 * (twistPi u d * Real.log (1 + u) ^ 2
      + (1 - twistPi u d) * Real.log (1 - u) ^ 2) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hv.2 (sq_nonneg l)
    linarith
  refine le_trans (Real.exp_le_exp.2 ?_)
    (twoAtom_mgf_ge hπ0 hπ1 (by positivity) hA hB hls hmv hlv')
  rw [abs_le] at hm
  have h1 : -l * (5 * u ^ 2)
      ≤ l * (twistPi u d * Real.log (1 + u) + (1 - twistPi u d) * Real.log (1 - u)) := by
    have := mul_le_mul_of_nonneg_left hm.1 hl0
    nlinarith
  have h2 : l ^ 2 * (u ^ 2 / 16)
      ≤ l ^ 2 * (twistPi u d * Real.log (1 + u) ^ 2
        + (1 - twistPi u d) * Real.log (1 - u) ^ 2) / 8 := by
    have := mul_le_mul_of_nonneg_left hv.1 (sq_nonneg l)
    linarith
  linarith

end TwistMGF

/-! ### The twisted weight over a range of primes

Everything above is combined here: the weight `‖F(½+σ+ih)‖²/‖F(½+σ)‖` over a range of primes,
with an exponential factor in the real-point walk, factorises into per-prime integrals, so the
bounds of the previous section multiply into exponentials of `U = ∑_p p^{-1-2σ}`. -/

lemma norm_one_add_mul_pos_of_le_one {a z : ℂ} (hz : ‖z‖ ≤ 1) (ha : ‖a‖ < 1) :
    0 < ‖1 + z * a‖ := by
  have hza : ‖z * a‖ ≤ ‖a‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg z]
  have h := norm_sub_norm_le (1 : ℂ) (-(z * a))
  rw [norm_one, norm_neg, sub_neg_eq_add] at h
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

section Range

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h l : ℝ}

/-- **The twisted weight over a range, factorised.**  Both the weight and the exponential of the
real-point walk are products over the primes of the range. -/
theorem integral_exp_mul_twist_eq_prod (hX : IsRademacherPrimeValues X μ) (ha5 : 5 ≤ a)
    (hσ : 0 ≤ σ) :
    (∫ ω, Real.exp (l * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ 0) ω‖) ∂μ)
      = ∏ p ∈ primesIco a b,
          ∫ z, Real.exp (l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
            * (‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
              / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖) ∂rademacherLaw := by
  classical
  have hSp : ∀ p ∈ primesIco a b, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hS5 : ∀ p ∈ primesIco a b, 5 ≤ p := by
    intro p hp
    have := (mem_primesIco.1 hp).2.1
    omega
  set g : ℕ → ℂ → ℝ := fun p z => Real.exp (l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
    * (‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
    with hg_def
  have hgm : ∀ p : ℕ, Measurable (g p) := by
    intro p
    rw [hg_def]
    fun_prop
  -- the pointwise identity, off the null set where some value exceeds one in modulus
  have hpt : ∀ᵐ ω ∂μ,
      Real.exp (l * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ 0) ω‖)
        = ∏ p ∈ primesIco a b, g p (X p ω) := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
    have hpos : ∀ p ∈ primesIco a b, 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖ := by
      intro p hp
      refine norm_one_add_mul_pos_of_le_one (hω p hp) ?_
      rw [norm_cpow_neg_shiftLine (hSp p hp).pos]
      have h5 := hS5 p hp
      have := rpow_neg_half_add_le_half h5 hσ
      linarith
    rw [hg_def]
    simp only [randomEulerProductIco_sqfree_eq, norm_prod]
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum, Real.exp_sum,
      ← Finset.prod_pow, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  rw [integral_congr_ae hpt]
  exact hX.integral_prod hSp g fun p _ => (hgm p).aestronglyMeasurable

/-- The normalisation of the twist over a range is at least one. -/
theorem one_le_integral_twist (hX : IsRademacherPrimeValues X μ) (ha5 : 5 ≤ a) (hσ : 0 ≤ σ) :
    1 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ ∂μ := by
  have hzero := integral_exp_mul_twist_eq_prod (X := X) (μ := μ) (a := a) (b := b) (σ := σ)
    (h := h) (l := 0) hX ha5 hσ
  simp only [zero_mul, Real.exp_zero, one_mul] at hzero
  rw [hzero]
  refine Finset.one_le_prod fun p hp => ?_
  have hp5 : 5 ≤ p := by
    have := (mem_primesIco.1 hp).2.1
    omega
  have heq := integral_exp_mul_twistWeight_rademacherLaw (l := 0) hp5 (h := h) hσ
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at heq
  rw [heq]
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hu0 : (0 : ℝ) < (p : ℝ) ^ (-(1 / 2 + σ)) := Real.rpow_pos_of_pos hpR _
  have hu2 : (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / 2 := rpow_neg_half_add_le_half hp5 hσ
  have hd0 : (0 : ℝ) ≤ 1 - Real.cos (h * Real.log p) := by
    linarith [Real.cos_le_one (h * Real.log p)]
  have hd2 : 1 - Real.cos (h * Real.log p) ≤ 2 := by
    linarith [Real.neg_one_le_cos (h * Real.log p)]
  have hsq : (0 : ℝ) < 1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by nlinarith
  have hπ : twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))
      + (1 - twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))) = 1 := by ring
  rw [hπ, mul_one]
  have : (0 : ℝ) ≤ 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
      / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by positivity
  linarith

end Range

/-! ### From one prime to a range -/

/-- `p^{-1/2-σ} ≤ 1/c` as soon as `c² ≤ p`. -/
lemma rpow_neg_half_add_le_inv {p : ℕ} {c σ : ℝ} (hc : 1 ≤ c) (hp : c ^ 2 ≤ (p : ℝ))
    (hσ : 0 ≤ σ) : (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / c := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by nlinarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : (c ^ 2 : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hp (by norm_num)
  have h2 : (c ^ 2 : ℝ) ^ (1 / 2 : ℝ) = c := by
    rw [show (c ^ 2 : ℝ) = c * c by ring, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self hc0.le]
  have h3 : (p : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ (1 / 2 + σ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have h4 : (0 : ℝ) < (p : ℝ) ^ (1 / 2 + σ) := Real.rpow_pos_of_pos hp0 _
  rw [Real.rpow_neg hp0.le, inv_le_comm₀ h4 (by positivity)]
  rw [h2] at h1
  have hinv : (1 / c)⁻¹ = c := by
    rw [one_div, inv_inv]
  rw [hinv]
  linarith

/-- A product of per-prime bounds, multiplied out. -/
lemma prod_le_prod_mul_exp {S : Finset ℕ} {I J c : ℕ → ℝ} (hI0 : ∀ p ∈ S, 0 ≤ I p)
    (hIJ : ∀ p ∈ S, I p ≤ J p * Real.exp (c p)) :
    ∏ p ∈ S, I p ≤ (∏ p ∈ S, J p) * Real.exp (∑ p ∈ S, c p) := by
  calc ∏ p ∈ S, I p ≤ ∏ p ∈ S, J p * Real.exp (c p) := Finset.prod_le_prod hI0 hIJ
    _ = (∏ p ∈ S, J p) * ∏ p ∈ S, Real.exp (c p) := Finset.prod_mul_distrib
    _ = (∏ p ∈ S, J p) * Real.exp (∑ p ∈ S, c p) := by rw [Real.exp_sum]

/-- The same, from below. -/
lemma prod_mul_exp_le_prod {S : Finset ℕ} {I J c : ℕ → ℝ} (hJ0 : ∀ p ∈ S, 0 ≤ J p)
    (hIJ : ∀ p ∈ S, J p * Real.exp (c p) ≤ I p) :
    (∏ p ∈ S, J p) * Real.exp (∑ p ∈ S, c p) ≤ ∏ p ∈ S, I p := by
  calc (∏ p ∈ S, J p) * Real.exp (∑ p ∈ S, c p)
      = (∏ p ∈ S, J p) * ∏ p ∈ S, Real.exp (c p) := by rw [Real.exp_sum]
    _ = ∏ p ∈ S, J p * Real.exp (c p) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ p ∈ S, I p :=
        Finset.prod_le_prod (fun p hp => mul_nonneg (hJ0 p hp) (Real.exp_pos _).le) hIJ

section RangeMGF

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h l : ℝ}

/-- Every prime of a range above `40000` has `u ≤ 1/200`, `d ∈ [0,2]`. -/
lemma twist_prime_hyps {p : ℕ} (hp : 40000 ≤ p) (hσ : 0 ≤ σ) :
    0 < (p : ℝ) ^ (-(1 / 2 + σ)) ∧ (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / 200
      ∧ 0 ≤ 1 - Real.cos (h * Real.log p) ∧ 1 - Real.cos (h * Real.log p) ≤ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  refine ⟨Real.rpow_pos_of_pos hp0 _, ?_, ?_, ?_⟩
  · refine rpow_neg_half_add_le_inv (by norm_num : (1:ℝ) ≤ 200) ?_ hσ
    have : ((40000 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    norm_num at this ⊢
    linarith
  · linarith [Real.cos_le_one (h * Real.log p)]
  · linarith [Real.neg_one_le_cos (h * Real.log p)]

/-- **The exponential moment of the real-point walk over a range, from above.** -/
theorem integral_exp_mul_twist_range_le (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) (hl0 : 0 ≤ l)
    (hlu : ∀ p ∈ primesIco a b, l * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4) :
    (∫ ω, Real.exp (l * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ 0) ω‖) ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖ ∂μ)
        * Real.exp (l * (5 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
          + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) := by
  have ha5 : 5 ≤ a := by omega
  have hzero := integral_exp_mul_twist_eq_prod (X := X) (μ := μ) (a := a) (b := b) (σ := σ)
    (h := h) (l := 0) hX ha5 hσ
  simp only [zero_mul, Real.exp_zero, one_mul] at hzero
  rw [integral_exp_mul_twist_eq_prod hX ha5 hσ, hzero]
  have hsum : l * (5 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
      + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
      = ∑ p ∈ primesIco a b, (l * (5 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
          + l ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) := by
    have hterm : ∀ p : ℕ, l * (5 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
        + l ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
        = (5 * l + 2 * l ^ 2) * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.mul_sum]
    ring
  rw [hsum]
  refine prod_le_prod_mul_exp (fun p _ => integral_nonneg fun z => by positivity)
    fun p hp => ?_
  have hp40 : 40000 ≤ p := by
    have := (mem_primesIco.1 hp).2.1
    omega
  have hp5 : 5 ≤ p := by omega
  obtain ⟨hu0, hu, hd0, hd2⟩ := twist_prime_hyps (h := h) hp40 hσ
  rw [integral_exp_mul_twistWeight_rademacherLaw hp5 hσ]
  have hzp := integral_exp_mul_twistWeight_rademacherLaw (l := 0) hp5 (h := h) hσ
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at hzp
  rw [hzp]
  have hZ0 : (0 : ℝ) ≤ 1 + 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
      / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
    have hsq : (0 : ℝ) < 1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by nlinarith
    have : (0 : ℝ) ≤ 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
        / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by positivity
    linarith
  have hπ : twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))
      + (1 - twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))) = 1 := by ring
  rw [hπ, mul_one]
  exact mul_le_mul_of_nonneg_left (twistMGF_le hu0 hu hd0 hd2 hl0 (hlu p hp)) hZ0

/-- **The exponential moment of the real-point walk over a range, from below.** -/
theorem integral_exp_mul_twist_range_ge (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) (hl0 : 0 ≤ l)
    (hlu : ∀ p ∈ primesIco a b, l * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4)
    (hlv : ∀ p ∈ primesIco a b, l ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ 1 / 2) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖ ∂μ)
        * Real.exp (-l * (5 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
          + l ^ 2 * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 16))
      ≤ ∫ ω, Real.exp (l * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ 0) ω‖) ∂μ := by
  have ha5 : 5 ≤ a := by omega
  have hzero := integral_exp_mul_twist_eq_prod (X := X) (μ := μ) (a := a) (b := b) (σ := σ)
    (h := h) (l := 0) hX ha5 hσ
  simp only [zero_mul, Real.exp_zero, one_mul] at hzero
  rw [integral_exp_mul_twist_eq_prod hX ha5 hσ, hzero]
  have hsum : -l * (5 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
      + l ^ 2 * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 16)
      = ∑ p ∈ primesIco a b, (-l * (5 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
          + l ^ 2 * (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 / 16)) := by
    have hterm : ∀ p : ℕ, -l * (5 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
        + l ^ 2 * (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 / 16)
        = (-(5 * l) + l ^ 2 / 16) * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.mul_sum]
    ring
  rw [hsum]
  refine prod_mul_exp_le_prod (fun p _ => integral_nonneg fun z => by positivity)
    fun p hp => ?_
  have hp40 : 40000 ≤ p := by
    have := (mem_primesIco.1 hp).2.1
    omega
  have hp5 : 5 ≤ p := by omega
  obtain ⟨hu0, hu, hd0, hd2⟩ := twist_prime_hyps (h := h) hp40 hσ
  rw [integral_exp_mul_twistWeight_rademacherLaw hp5 hσ]
  have hzp := integral_exp_mul_twistWeight_rademacherLaw (l := 0) hp5 (h := h) hσ
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at hzp
  rw [hzp]
  have hZ0 : (0 : ℝ) ≤ 1 + 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
      / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
    have hsq : (0 : ℝ) < 1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by nlinarith
    have : (0 : ℝ) ≤ 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
        / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by positivity
    linarith
  have hπ : twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))
      + (1 - twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))) = 1 := by ring
  rw [hπ, mul_one]
  exact mul_le_mul_of_nonneg_left (twistMGF_ge hu0 hu hd0 hd2 hl0 (hlu p hp) (hlv p hp)) hZ0

/-- **The exponential moment with a negative exponent, where the twist is small.**  This is the
Chernoff bound for the *lower* tail of the real-point walk. -/
theorem integral_exp_neg_mul_twist_range_le (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) (hl0 : 0 ≤ l)
    (hlu : ∀ p ∈ primesIco a b, l * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4)
    (hgood : ∀ p ∈ primesIco a b, 1 - Real.cos (h * Real.log p) ≤ 1 / 24) :
    (∫ ω, Real.exp (-l * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
                (shiftLine σ 0) ω‖) ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖ ∂μ)
        * Real.exp (-l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
          + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) := by
  have ha5 : 5 ≤ a := by omega
  have hzero := integral_exp_mul_twist_eq_prod (X := X) (μ := μ) (a := a) (b := b) (σ := σ)
    (h := h) (l := 0) hX ha5 hσ
  simp only [zero_mul, Real.exp_zero, one_mul] at hzero
  rw [integral_exp_mul_twist_eq_prod hX ha5 hσ, hzero]
  have hsum : -l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
      + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
      = ∑ p ∈ primesIco a b, (-l * (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 / 5)
          + l ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) := by
    have hterm : ∀ p : ℕ, -l * (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 / 5)
        + l ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
        = (-(l / 5) + 2 * l ^ 2) * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.mul_sum]
    ring
  rw [hsum]
  refine prod_le_prod_mul_exp (fun p _ => integral_nonneg fun z => by positivity)
    fun p hp => ?_
  have hp40 : 40000 ≤ p := by
    have := (mem_primesIco.1 hp).2.1
    omega
  have hp5 : 5 ≤ p := by omega
  obtain ⟨hu0, hu, hd0, hd2⟩ := twist_prime_hyps (h := h) hp40 hσ
  rw [integral_exp_mul_twistWeight_rademacherLaw hp5 hσ]
  have hzp := integral_exp_mul_twistWeight_rademacherLaw (l := 0) hp5 (h := h) hσ
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at hzp
  rw [hzp]
  have hZ0 : (0 : ℝ) ≤ 1 + 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
      / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
    have hsq : (0 : ℝ) < 1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by nlinarith
    have : (0 : ℝ) ≤ 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * (1 - Real.cos (h * Real.log p))
        / (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by positivity
    linarith
  have hπ : twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))
      + (1 - twistPi ((p : ℝ) ^ (-(1 / 2 + σ))) (1 - Real.cos (h * Real.log p))) = 1 := by ring
  rw [hπ, mul_one]
  exact mul_le_mul_of_nonneg_left
    (twistMGF_neg_le hu0 hu hd0 (hgood p hp) hl0 (hlu p hp)) hZ0

end RangeMGF

/-! ### Integrability

Every integrand here is a product over the primes of the range of factors that are bounded on the
unimodularity event, so all of them are bounded, hence integrable against a probability measure. -/

section RangeIntegrable

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h l : ℝ}

/-- On the unimodularity event the local weight and the local logarithm are controlled by `u`. -/
lemma abs_exp_mul_twist_le_of_norm_le_one {p : ℕ} (hp : 5 ≤ p) (hσ : 0 ≤ σ) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    |Real.exp (l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
        * (‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)|
      ≤ Real.exp ((2 * |l| + 7) * (p : ℝ) ^ (-(1 / 2 + σ))) := by
  have hp0 : 0 < p := by omega
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu_def
  have hu0 : (0 : ℝ) < u := Real.rpow_pos_of_pos (by exact_mod_cast hp0) _
  have hu2 : u ≤ 1 / 2 := rpow_neg_half_add_le_half hp hσ
  have hw0 : ‖(p : ℂ) ^ (-shiftLine σ 0)‖ = u := norm_cpow_neg_shiftLine hp0 σ 0
  have hwh : ‖(p : ℂ) ^ (-shiftLine σ h)‖ = u := norm_cpow_neg_shiftLine hp0 σ h
  -- the two local quantities
  have hlo : 1 - u ≤ ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(z * (p : ℂ) ^ (-shiftLine σ 0)))
    rw [norm_one, norm_neg, sub_neg_eq_add, norm_mul, hw0] at h
    nlinarith [norm_nonneg z, hu0.le]
  have hhi : ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ≤ 1 + u := by
    have h := norm_add_le (1 : ℂ) (z * (p : ℂ) ^ (-shiftLine σ 0))
    rw [norm_one, norm_mul, hw0] at h
    nlinarith [norm_nonneg z, hu0.le]
  have hhih : ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ≤ 1 + u := by
    have h := norm_add_le (1 : ℂ) (z * (p : ℂ) ^ (-shiftLine σ h))
    rw [norm_one, norm_mul, hwh] at h
    nlinarith [norm_nonneg z, hu0.le]
  have hpos : (0 : ℝ) < ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ := by linarith
  -- the logarithm is at most `2u` in size
  have hlog : |Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖| ≤ 2 * u := by
    have h1 : Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ≤ 2 * u := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    have h2 : -(2 * u) ≤ Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ := by
      have hlow : Real.log (1 - u) ≤ Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ :=
        Real.log_le_log (by linarith) hlo
      have hE := abs_log_one_sub_sub_quad_le hu0 hu2
      rw [abs_le] at hE
      nlinarith [pow_pos hu0 3, hE.1]
    rw [abs_le]
    exact ⟨h2, h1⟩
  -- the weight is at most `1 + 4u`
  have hweight : ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ≤ 1 + 7 * u := by
    rw [div_le_iff₀ hpos]
    have hsq : ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 ≤ (1 + u) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hhih 2
    nlinarith
  have hweight0 : (0 : ℝ) ≤ ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
      / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ := by positivity
  -- multiply the two bounds
  rw [abs_of_nonneg (by positivity)]
  have hexp1 : Real.exp (l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
      ≤ Real.exp (2 * |l| * u) := by
    refine Real.exp_le_exp.2 ?_
    calc l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖
        ≤ |l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖| := le_abs_self _
      _ = |l| * |Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖| := abs_mul _ _
      _ ≤ |l| * (2 * u) := mul_le_mul_of_nonneg_left hlog (abs_nonneg l)
      _ = 2 * |l| * u := by ring
  have hexp2 : (1 : ℝ) + 7 * u ≤ Real.exp (7 * u) := by
    linarith [Real.add_one_le_exp (7 * u)]
  calc Real.exp (l * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
        * (‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 / ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖)
      ≤ Real.exp (2 * |l| * u) * (1 + 7 * u) :=
        mul_le_mul hexp1 hweight hweight0 (Real.exp_pos _).le
    _ ≤ Real.exp (2 * |l| * u) * Real.exp (7 * u) :=
        mul_le_mul_of_nonneg_left hexp2 (Real.exp_pos _).le
    _ = Real.exp ((2 * |l| + 7) * u) := by rw [← Real.exp_add]; ring_nf

/-- The exponentially weighted twist over a range is bounded, hence integrable. -/
lemma integrable_exp_mul_twist (hX : IsRademacherPrimeValues X μ) (ha5 : 5 ≤ a) (hσ : 0 ≤ σ) :
    Integrable (fun ω => Real.exp (l * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
        * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖)) μ := by
  haveI := hX.isProbabilityMeasure
  have hSp : ∀ p ∈ primesIco a b, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hS5 : ∀ p ∈ primesIco a b, 5 ≤ p := by
    intro p hp
    have := (mem_primesIco.1 hp).2.1
    omega
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (l * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
      * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖)) μ := by
    have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
    have hm0 := (hf.aemeasurable_randomEulerProductIco a b (shiftLine σ 0)).norm
    have hmh := (hf.aemeasurable_randomEulerProductIco a b (shiftLine σ h)).norm
    exact (((hm0.log.const_mul l).exp).mul ((hmh.pow_const 2).div hm0)).aestronglyMeasurable
  refine (memLp_top_of_bound hmeas
    (Real.exp ((2 * |l| + 7) * ∑ p ∈ primesIco a b, (p : ℝ) ^ (-(1 / 2 + σ)))) ?_).integrable le_top
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
  have hpos : ∀ p ∈ primesIco a b, 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖ := by
    intro p hp
    refine norm_one_add_mul_pos_of_le_one (hω p hp) ?_
    rw [norm_cpow_neg_shiftLine (hSp p hp).pos]
    have := rpow_neg_half_add_le_half (hS5 p hp) hσ
    linarith
  have hprod : Real.exp (l * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
      * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖)
      = ∏ p ∈ primesIco a b, (Real.exp (l * Real.log ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖)
          * (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
            / ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖)) := by
    simp only [randomEulerProductIco_sqfree_eq, norm_prod]
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum, Real.exp_sum,
      ← Finset.prod_pow, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  rw [Real.norm_eq_abs, hprod]
  have habs : |∏ p ∈ primesIco a b, (Real.exp (l * Real.log ‖1 + X p ω * (p : ℂ) ^
          (-shiftLine σ 0)‖) * (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
            / ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖))|
      = ∏ p ∈ primesIco a b, |Real.exp (l * Real.log ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖)
          * (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
            / ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖)| := Finset.abs_prod _ _
  rw [habs]
  calc ∏ p ∈ primesIco a b, |Real.exp (l * Real.log ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖)
          * (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2
            / ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖)|
      ≤ ∏ p ∈ primesIco a b, Real.exp ((2 * |l| + 7) * (p : ℝ) ^ (-(1 / 2 + σ))) :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _)
          (fun p hp => abs_exp_mul_twist_le_of_norm_le_one (hS5 p hp) hσ (hω p hp))
    _ = Real.exp (∑ p ∈ primesIco a b, (2 * |l| + 7) * (p : ℝ) ^ (-(1 / 2 + σ))) :=
        (Real.exp_sum _ _).symm
    _ = Real.exp ((2 * |l| + 7) * ∑ p ∈ primesIco a b, (p : ℝ) ^ (-(1 / 2 + σ))) := by
        rw [← Finset.mul_sum]

end RangeIntegrable

/-! ### The two tail estimates for the real-point walk over a range

With the weight `W = ‖F(½+σ+ih)‖²/‖F(½+σ)‖` and the walk `Y = log‖F(½+σ)‖`, the exponential
moments above give a Chernoff bound for `{Y ≤ -A}` and a Paley–Zygmund bound for `{A ≤ Y}`.  The
second is the anti-concentration the ladder event needs, and the only place where a *lower* bound
on a probability is produced. -/

section RangeTails

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h : ℝ}

lemma measurable_norm_randomEulerProductIco (hX : IsRademacherPrimeValues X μ) (a b : ℕ) (s : ℂ) :
    Measurable fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ := by
  have he : ∀ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖
      = ‖∏ p ∈ primesIco a b, (1 + X p ω * (p : ℂ) ^ (-s))‖ :=
    fun ω => by rw [randomEulerProductIco_sqfree_eq]
  simp only [he]
  exact (Finset.measurable_prod _ fun p hp =>
    ((hX.measurable p (prime_of_mem_primesIco hp)).mul_const _).const_add _).norm

/-- **The lower tail of the real-point walk over a range.**  Chernoff against the twisted weight,
with the drift `U/5` of the small-twist primes. -/
theorem setIntegral_twist_le_of_le_neg (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) {A l : ℝ} (hl0 : 0 ≤ l)
    (hlu : ∀ p ∈ primesIco a b, l * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4)
    (hgood : ∀ p ∈ primesIco a b, 1 - Real.cos (h * Real.log p) ≤ 1 / 24) :
    (∫ ω in {ω | Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          a b (shiftLine σ 0) ω‖ ≤ -A},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖ ∂μ)
        * Real.exp (-(l * A) + (-l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
            + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2))) := by
  have ha5 : 5 ≤ a := by omega
  set Y : Ω → ℝ := fun ω => Real.log ‖randomEulerProductIco
    (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖ with hY_def
  set W : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        a b (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ 0) ω‖ with hW_def
  have hWm : MeasurableSet {ω | Y ω ≤ -A} :=
    measurableSet_le ((measurable_norm_randomEulerProductIco hX a b (shiftLine σ 0)).log)
      measurable_const
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by rw [hW_def]; positivity
  have hint : Integrable (fun ω => Real.exp (-l * Y ω) * W ω) μ :=
    integrable_exp_mul_twist (l := -l) hX ha5 hσ
  -- the pointwise Chernoff inequality
  have hpt : ∀ ω, Set.indicator {ω | Y ω ≤ -A} W ω
      ≤ Real.exp (-(l * A)) * (Real.exp (-l * Y ω) * W ω) := by
    intro ω
    by_cases hmem : ω ∈ {ω | Y ω ≤ -A}
    · rw [Set.indicator_of_mem hmem]
      have hYA : Y ω ≤ -A := hmem
      have h1 : (1 : ℝ) ≤ Real.exp (-(l * A)) * Real.exp (-l * Y ω) := by
        rw [← Real.exp_add]
        refine Real.one_le_exp ?_
        nlinarith
      have := mul_le_mul_of_nonneg_right h1 (hW0 ω)
      calc W ω = 1 * W ω := (one_mul _).symm
        _ ≤ Real.exp (-(l * A)) * Real.exp (-l * Y ω) * W ω := this
        _ = Real.exp (-(l * A)) * (Real.exp (-l * Y ω) * W ω) := by ring
    · rw [Set.indicator_of_notMem hmem]
      positivity
  rw [← integral_indicator hWm]
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    Set.indicator_nonneg (fun _ _ => hW0 _) ω) (hint.const_mul _)
    (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul]
  have hb := integral_exp_neg_mul_twist_range_le (h := h) hX ha hσ hl0 hlu hgood
  calc Real.exp (-(l * A)) * ∫ ω, Real.exp (-l * Y ω) * W ω ∂μ
      ≤ Real.exp (-(l * A)) * ((∫ ω, W ω ∂μ)
          * Real.exp (-l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
            + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2))) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = (∫ ω, W ω ∂μ)
          * Real.exp (-(l * A) + (-l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
            + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2))) := by
        rw [show Real.exp (-(l * A)
              + (-l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
                + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)))
            = Real.exp (-(l * A))
              * Real.exp (-l * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 5)
                + l ^ 2 * (2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) from
            Real.exp_add _ _]
        ring

/-- **The upper tail of the real-point walk over a range, from below.**  Paley–Zygmund: the
weighted measure of `{A ≤ Y}` is at least `e^{-20lU - 8l²U}/4` times the total weight, as soon as
the exponential moment at `l` is at least twice `e^{lA}`. -/
theorem le_setIntegral_twist_of_le (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) {A l : ℝ} (hl1 : 1 ≤ l)
    (hlu : ∀ p ∈ primesIco a b, (2 * l) * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4)
    (hlv : ∀ p ∈ primesIco a b, (2 * l) ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ 1 / 2)
    (hlevel : 2 * Real.exp (l * A)
      ≤ Real.exp (-l * (5 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
        + l ^ 2 * ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 16))) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ∂μ)
        * (Real.exp (-(20 * l * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
            - 8 * l ^ 2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 4)
      ≤ ∫ ω in {ω | A ≤ Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖ ∂μ := by
  have ha5 : 5 ≤ a := by omega
  have hl0 : (0 : ℝ) ≤ l := by linarith
  set U : ℝ := ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 with hU_def
  set Y : Ω → ℝ := fun ω => Real.log ‖randomEulerProductIco
    (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖ with hY_def
  set W : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        a b (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ 0) ω‖ with hW_def
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by rw [hW_def]; positivity
  have hYmeas : Measurable Y :=
    (measurable_norm_randomEulerProductIco hX a b (shiftLine σ 0)).log
  have hAmeas : MeasurableSet {ω | A ≤ Y ω} := measurableSet_le measurable_const hYmeas
  have hTmeas : MeasurableSet {ω | Real.exp (l * A) < Real.exp (l * Y ω)} :=
    measurableSet_lt measurable_const ((hYmeas.const_mul l).exp)
  -- the three moments
  have hlu1 : ∀ p ∈ primesIco a b, l * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4 := by
    intro p hp
    have h := hlu p hp
    have hu0 : (0 : ℝ) < (p : ℝ) ^ (-(1 / 2 + σ)) := by
      have hp0 : (0 : ℕ) < p := (prime_of_mem_primesIco hp).pos
      exact Real.rpow_pos_of_pos (by exact_mod_cast hp0) _
    nlinarith
  have hlv1 : ∀ p ∈ primesIco a b, l ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ 1 / 2 := by
    intro p hp
    have h := hlv p hp
    have hu0 : (0 : ℝ) < ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
      have hp0 : (0 : ℕ) < p := (prime_of_mem_primesIco hp).pos
      exact pow_pos (Real.rpow_pos_of_pos (by exact_mod_cast hp0) _) 2
    nlinarith
  have hN0 : 1 ≤ ∫ ω, W ω ∂μ := one_le_integral_twist hX ha5 hσ
  have hIz := integral_exp_mul_twist_range_ge (h := h) hX ha hσ hl0 hlu1 hlv1
  have hIz2 := integral_exp_mul_twist_range_le (h := h) (l := 2 * l) hX ha hσ (by linarith) hlu
  have hintZ : Integrable (fun ω => Real.exp (l * Y ω) * W ω) μ :=
    integrable_exp_mul_twist hX ha5 hσ
  have hintZ2 : Integrable (fun ω => Real.exp (2 * l * Y ω) * W ω) μ :=
    integrable_exp_mul_twist hX ha5 hσ
  have hintW : Integrable W μ := by
    have := integrable_exp_mul_twist (X := X) (μ := μ) (a := a) (b := b) (σ := σ) (h := h)
      (l := 0) hX ha5 hσ
    simpa using this
  -- abbreviations
  set N : ℝ := ∫ ω, W ω ∂μ with hN_def
  set Iz : ℝ := ∫ ω, Real.exp (l * Y ω) * W ω ∂μ with hIz_def
  set Iz2 : ℝ := ∫ ω, Real.exp (2 * l * Y ω) * W ω ∂μ with hIz2_def
  set G₁ : ℝ := Real.exp (-l * (5 * U) + l ^ 2 * (U / 16)) with hG₁_def
  set G₂ : ℝ := Real.exp (2 * l * (5 * U) + (2 * l) ^ 2 * (2 * U)) with hG₂_def
  have hG₁0 : 0 < G₁ := Real.exp_pos _
  have hG₂0 : 0 < G₂ := Real.exp_pos _
  have hIzge : N * G₁ ≤ Iz := hIz
  have hIz2le : Iz2 ≤ N * G₂ := hIz2
  have hN0' : 0 < N := by linarith
  have hD0 : 0 < Iz - Real.exp (l * A) * N := by
    have h1 : 2 * Real.exp (l * A) ≤ G₁ := hlevel
    have h2 : N * (2 * Real.exp (l * A)) ≤ N * G₁ := mul_le_mul_of_nonneg_left h1 hN0'.le
    nlinarith [Real.exp_pos (l * A)]
  have hIz20 : 0 < Iz2 := by
    have hge := integral_exp_mul_twist_range_ge (h := h) (l := 2 * l) hX ha hσ (by linarith)
      hlu hlv
    rw [← hU_def, ← hN_def, ← hIz2_def] at hge
    have hpos : 0 < N * Real.exp (-(2 * l) * (5 * U) + (2 * l) ^ 2 * (U / 16)) :=
      mul_pos hN0' (Real.exp_pos _)
    linarith
  -- Paley-Zygmund, with the optimal split
  set D : ℝ := Iz - Real.exp (l * A) * N with hD_def
  set s : ℝ := Iz2 / D with hs_def
  have hs0 : 0 < s := div_pos hIz20 hD0
  have hintInd : Integrable (Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W) μ :=
    hintW.indicator hTmeas
  have hI1 : Integrable (fun ω => Real.exp (l * A) * W ω) μ := hintW.const_mul _
  have hI2 : Integrable (fun ω => Real.exp (2 * l * Y ω) * W ω / (2 * s)) μ :=
    hintZ2.div_const _
  have hI3 : Integrable (fun ω => s / 2
      * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω) μ := hintInd.const_mul _
  have hpt : ∀ ω, Real.exp (l * Y ω) * W ω
      ≤ Real.exp (l * A) * W ω
        + (Real.exp (2 * l * Y ω) * W ω / (2 * s)
          + s / 2 * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω) := by
    intro ω
    have hz2 : Real.exp (2 * l * Y ω) = Real.exp (l * Y ω) * Real.exp (l * Y ω) := by
      rw [← Real.exp_add]
      ring_nf
    by_cases hmem : ω ∈ {ω | Real.exp (l * A) < Real.exp (l * Y ω)}
    · rw [Set.indicator_of_mem hmem]
      have hs2 : (0 : ℝ) < 2 * s := by linarith
      have hid : Real.exp (2 * l * Y ω) / (2 * s) + s / 2 - Real.exp (l * Y ω)
          = (Real.exp (l * Y ω) - s) ^ 2 / (2 * s) := by
        rw [hz2]
        field_simp
        ring
      have hnn : 0 ≤ (Real.exp (l * Y ω) - s) ^ 2 / (2 * s) :=
        div_nonneg (sq_nonneg _) hs2.le
      have hkey : Real.exp (l * Y ω) ≤ Real.exp (2 * l * Y ω) / (2 * s) + s / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hkey (hW0 ω)
      have hexpand : (Real.exp (2 * l * Y ω) / (2 * s) + s / 2) * W ω
          = Real.exp (2 * l * Y ω) * W ω / (2 * s) + s / 2 * W ω := by ring
      rw [hexpand] at hmul
      have hexp0 : 0 ≤ Real.exp (l * A) * W ω := by positivity
      linarith
    · rw [Set.indicator_of_notMem hmem]
      have hle : Real.exp (l * Y ω) ≤ Real.exp (l * A) := not_lt.1 hmem
      have hmul := mul_le_mul_of_nonneg_right hle (hW0 ω)
      have h2 : 0 ≤ Real.exp (2 * l * Y ω) * W ω / (2 * s) := by positivity
      linarith
  have e1 : (∫ ω, (Real.exp (2 * l * Y ω) * W ω / (2 * s)
        + s / 2 * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω) ∂μ)
      = (∫ ω, Real.exp (2 * l * Y ω) * W ω / (2 * s) ∂μ)
        + ∫ ω, s / 2 * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω ∂μ :=
    integral_add hI2 hI3
  have e2 : (∫ ω, (Real.exp (l * A) * W ω
        + (Real.exp (2 * l * Y ω) * W ω / (2 * s)
          + s / 2 * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω)) ∂μ)
      = (∫ ω, Real.exp (l * A) * W ω ∂μ)
        + ∫ ω, (Real.exp (2 * l * Y ω) * W ω / (2 * s)
            + s / 2 * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω) ∂μ :=
    integral_add hI1 (hI2.add hI3)
  have hsplit : Iz ≤ Real.exp (l * A) * N
      + (Iz2 / (2 * s)
        + s / 2 * ∫ ω in {ω | Real.exp (l * A) < Real.exp (l * Y ω)}, W ω ∂μ) := by
    have hmono : (∫ ω, Real.exp (l * Y ω) * W ω ∂μ)
        ≤ ∫ ω, (Real.exp (l * A) * W ω
            + (Real.exp (2 * l * Y ω) * W ω / (2 * s)
              + s / 2 * Set.indicator {ω | Real.exp (l * A) < Real.exp (l * Y ω)} W ω)) ∂μ :=
      integral_mono hintZ (hI1.add (hI2.add hI3)) hpt
    rw [e2, e1, integral_const_mul, integral_div, integral_const_mul,
      integral_indicator hTmeas, ← hN_def, ← hIz2_def] at hmono
    exact hmono
  -- solve for the indicator integral
  have hIndt : D ^ 2 / Iz2 ≤ ∫ ω in {ω | Real.exp (l * A) < Real.exp (l * Y ω)}, W ω ∂μ := by
    have h2 : Iz2 / (2 * s) = D / 2 := by
      rw [hs_def]
      field_simp
    rw [h2] at hsplit
    have h3 : D / 2 ≤ s / 2 * ∫ ω in {ω | Real.exp (l * A) < Real.exp (l * Y ω)}, W ω ∂μ := by
      rw [hD_def]
      linarith
    have h4 : D / s ≤ ∫ ω in {ω | Real.exp (l * A) < Real.exp (l * Y ω)}, W ω ∂μ := by
      rw [div_le_iff₀ hs0]
      linarith
    have h5 : D / s = D ^ 2 / Iz2 := by
      rw [hs_def]
      field_simp
    rwa [h5] at h4
  -- the event inclusion
  have hsub : {ω | Real.exp (l * A) < Real.exp (l * Y ω)} ⊆ {ω | A ≤ Y ω} := by
    intro ω hω
    have hlt := Real.exp_lt_exp.1 hω
    have hA : A < Y ω := by
      by_contra hc
      have hc' : Y ω ≤ A := not_lt.1 hc
      nlinarith
    exact le_of_lt hA
  have hmono : (∫ ω in {ω | Real.exp (l * A) < Real.exp (l * Y ω)}, W ω ∂μ)
      ≤ ∫ ω in {ω | A ≤ Y ω}, W ω ∂μ :=
    setIntegral_mono_set hintW.integrableOn (Filter.Eventually.of_forall hW0)
      (Filter.Eventually.of_forall hsub)
  refine le_trans ?_ (le_trans hIndt hmono)
  -- the quantitative bound on `D²/Iz2`, in the abstract
  have hU0 : 0 ≤ U := by
    rw [hU_def]
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hG : G₁ ^ 2 / G₂
      = Real.exp (2 * (-l * (5 * U) + l ^ 2 * (U / 16))
        - (2 * l * (5 * U) + (2 * l) ^ 2 * (2 * U))) := by
    rw [hG₁_def, hG₂_def, sq, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have hmono2 : Real.exp (-(20 * l * U) - 8 * l ^ 2 * U) ≤ G₁ ^ 2 / G₂ := by
    rw [hG]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg (sq_nonneg l) hU0]
  clear_value s D G₂ G₁ Iz2 Iz N U
  clear hs_def hG₂_def hG₁_def hIz2_def hIz_def hN_def hU_def hG hpt hsplit e1 e2
    hIndt hmono hI1 hI2 hI3 hintInd
  have hDge : N * G₁ / 2 ≤ D := by
    have h1 : 2 * Real.exp (l * A) ≤ G₁ := hlevel
    have h2 : N * (2 * Real.exp (l * A)) ≤ N * G₁ := mul_le_mul_of_nonneg_left h1 hN0'.le
    rw [hD_def]
    nlinarith
  have hDsq : (N * G₁ / 2) ^ 2 ≤ D ^ 2 := by
    have h0 : 0 ≤ N * G₁ / 2 := by positivity
    nlinarith
  rw [le_div_iff₀ hIz20]
  have hstep0 : N * (Real.exp (-(20 * l * U) - 8 * l ^ 2 * U) / 4) * Iz2
      ≤ N * (G₁ ^ 2 / G₂ / 4) * Iz2 := by
    refine mul_le_mul_of_nonneg_right ?_ hIz20.le
    refine mul_le_mul_of_nonneg_left ?_ hN0'.le
    linarith [div_le_div_of_nonneg_right hmono2 (by norm_num : (0:ℝ) ≤ 4)]
  have hstep1 : N * (G₁ ^ 2 / G₂ / 4) * Iz2 ≤ N * (G₁ ^ 2 / G₂ / 4) * (N * G₂) :=
    mul_le_mul_of_nonneg_left hIz2le (mul_nonneg hN0'.le (by positivity))
  have hstep2 : N * (G₁ ^ 2 / G₂ / 4) * (N * G₂) = (N * G₁ / 2) ^ 2 := by
    field_simp
    ring
  linarith

end RangeTails

/-! ### The mass of a range of scales

`U = ∑_{p ∈ [scaleCut m, scaleCut n)} p^{-1-2σ}` is `n - m` up to the `σ`-damping and Mertens'
error: at most `n - m + 1/10`, and at least `e^{-3}(n - m - 1/10)` as long as `σe^n ≤ 1`, which
keeps `p^{-2σ} ≥ e^{-3}` over the range. -/

section Mass

variable {σ : ℝ}

lemma sq_rpow_neg_le_inv {p : ℕ} (hp : 1 ≤ p) (hσ : 0 ≤ σ) :
    ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 ≤ 1 / p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le]
  calc (p : ℝ) ^ (-(1 / 2 + σ) * (2 : ℕ)) ≤ (p : ℝ) ^ (-1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
        push_cast
        linarith
    _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]

lemma le_sq_rpow_neg {p : ℕ} (hp : 1 ≤ p) (_hσ : 0 ≤ σ) (hlog : 2 * σ * Real.log p ≤ 3) :
    Real.exp (-3) * (1 / p) ≤ ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsplit : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 = (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le,
      ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  have hdamp : Real.exp (-3) ≤ (p : ℝ) ^ (-(2 * σ)) := by
    rw [Real.rpow_def_of_pos hp0]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  rw [hsplit, Real.rpow_neg_one, one_div]
  have hinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  calc Real.exp (-3) * (p : ℝ)⁻¹ = (p : ℝ)⁻¹ * Real.exp (-3) := by ring
    _ ≤ (p : ℝ)⁻¹ * (p : ℝ) ^ (-(2 * σ)) := mul_le_mul_of_nonneg_left hdamp hinv.le

/-- **The mass of a range of scales, from above**: `U ≤ n - m + 1/10`. -/
lemma sum_sq_rpow_neg_primesIco_le {m n : ℕ} (hm : 20 ≤ m) (hmn : m ≤ n) (hσ : 0 ≤ σ) :
    ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)), ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
      ≤ (n : ℝ) - m + 1 / 10 := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hx2 : (2 : ℝ) ≤ blockScale (m : ℝ) 0 := two_le_blockScale_zero hm0
  have hxy : blockScale (m : ℝ) 0 ≤ blockScale (n : ℝ) 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 hmnR)
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le _ _ hx2 hxy
  rw [filter_prime_Ioc_eq_primesIco, log_log_blockScale_zero, log_log_blockScale_zero] at hmert
  have h20 : 20 / Real.log (blockScale (m : ℝ) 0) ≤ 1 / 10 := by
    rw [log_blockScale, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h200 : (200 : ℝ) ≤ Real.exp ((0 : ℝ) + m) := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h1 : Real.exp (20 : ℝ) ≤ Real.exp ((0 : ℝ) + m) := by
        refine Real.exp_le_exp.2 ?_
        linarith
      have h2 : Real.exp (20 : ℝ) = Real.exp 1 ^ (20 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : (2.7 : ℝ) ^ (20 : ℕ) ≤ Real.exp 1 ^ (20 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he.le 20
      have h4 : (200 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
      linarith
    push_cast at h200 ⊢
    linarith
  have hterm : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
      ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 ≤ 1 / p := by
    intro p hp
    exact sq_rpow_neg_le_inv (prime_of_mem_primesIco hp).one_lt.le hσ
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have habs := (abs_le.1 hmert).2
  unfold scaleCut
  linarith

/-- **The mass of a range of scales, from below**: `e^{-3}(n - m - 1/10) ≤ U` when `σe^n ≤ 1`,
which keeps the `σ`-damping mild over the range. -/
lemma le_sum_sq_rpow_neg_primesIco {m n : ℕ} (hm : 20 ≤ m) (hmn : m ≤ n) (hσ : 0 ≤ σ)
    (hσn : σ * Real.exp (n : ℝ) ≤ 1) :
    Real.exp (-3) * ((n : ℝ) - m - 1 / 10)
      ≤ ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)), ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hx2 : (2 : ℝ) ≤ blockScale (m : ℝ) 0 := two_le_blockScale_zero hm0
  have hxy : blockScale (m : ℝ) 0 ≤ blockScale (n : ℝ) 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 hmnR)
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le _ _ hx2 hxy
  rw [filter_prime_Ioc_eq_primesIco, log_log_blockScale_zero, log_log_blockScale_zero] at hmert
  have h20 : 20 / Real.log (blockScale (m : ℝ) 0) ≤ 1 / 10 := by
    rw [log_blockScale, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h200 : (200 : ℝ) ≤ Real.exp ((0 : ℝ) + m) := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h1 : Real.exp (20 : ℝ) ≤ Real.exp ((0 : ℝ) + m) := by
        refine Real.exp_le_exp.2 ?_
        linarith
      have h2 : Real.exp (20 : ℝ) = Real.exp 1 ^ (20 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : (2.7 : ℝ) ^ (20 : ℕ) ≤ Real.exp 1 ^ (20 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he.le 20
      have h4 : (200 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
      linarith
    push_cast at h200 ⊢
    linarith
  -- every prime of the range has mild damping
  have hterm : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
      Real.exp (-3) * (1 / p) ≤ ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hplt : (p : ℕ) < scaleCut (n : ℝ) := (mem_primesIco.1 hp).2.2
    have hple : ((p : ℕ) : ℝ) ≤ ((scaleCut (n : ℝ) : ℕ) : ℝ) := by exact_mod_cast hplt.le
    have hlogp : Real.log p ≤ Real.exp (n : ℝ) + 1 := by
      refine le_trans (Real.log_le_log (by exact_mod_cast hpp.pos) hple) ?_
      exact log_scaleCut_le (n : ℝ)
    have hn20 : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hm hmn
    have hen2 : (2 : ℝ) ≤ Real.exp (n : ℝ) := by
      linarith [Real.add_one_le_exp ((n : ℝ))]
    have hσ1 : σ ≤ 1 / 2 := by nlinarith
    have hlog : 2 * σ * Real.log p ≤ 3 := by
      have h1 : σ * Real.log p ≤ σ * (Real.exp (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogp hσ
      nlinarith
    exact le_sq_rpow_neg hpp.one_lt.le hσ hlog
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum]
  have habs := (abs_le.1 hmert).1
  have hsum : (n : ℝ) - m - 1 / 10
      ≤ ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)), 1 / (p : ℝ) := by
    unfold scaleCut
    linarith
  exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le

end Mass

/-! ### Independence across a cut

The twisted weight of a range, and any event defined by the walk over a sub-range, are functions
of the values at the primes of that range, so `RMF.integral_mul_split_Ico` factorises them across
a cut.  This is what lets the ladder event be built out of three independent pieces. -/

/-- The twisted weight over a range, as a function of the values at its primes. -/
noncomputable def twistPoly (S : Finset ℕ) (σ h : ℝ) (v : ↥S → ℂ) : ℝ :=
  ‖primePoly S (shiftLine σ h) v‖ ^ 2 / ‖primePoly S (shiftLine σ 0) v‖

lemma measurable_twistPoly (S : Finset ℕ) (σ h : ℝ) : Measurable (twistPoly S σ h) := by
  unfold twistPoly
  exact (((continuous_primePoly S (shiftLine σ h)).norm.pow 2).measurable).div
    ((continuous_primePoly S (shiftLine σ 0)).norm.measurable)

section Split

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ h : ℝ}

omit [MeasurableSpace Ω] in
lemma twistPoly_primesIco (a b : ℕ) (σ h : ℝ) (ω : Ω) :
    twistPoly (primesIco a b) σ h (fun p => X (p : ℕ) ω)
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ := by
  rw [twistPoly, primePoly_primesIco, primePoly_primesIco]

/-- **The factorisation across a cut** of two events carrying the twisted weight. -/
theorem integral_twist_indicator_mul_split (hX : IsRademacherPrimeValues X μ) {a b c : ℕ}
    {T₁ : Set (↥(primesIco a b) → ℂ)} (hT₁ : MeasurableSet T₁)
    {T₂ : Set (↥(primesIco b c) → ℂ)} (hT₂ : MeasurableSet T₂) :
    (∫ ω, Set.indicator T₁ (twistPoly (primesIco a b) σ h) (fun p => X (p : ℕ) ω)
        * Set.indicator T₂ (twistPoly (primesIco b c) σ h) (fun p => X (p : ℕ) ω) ∂μ)
      = (∫ ω, Set.indicator T₁ (twistPoly (primesIco a b) σ h) (fun p => X (p : ℕ) ω) ∂μ)
        * ∫ ω, Set.indicator T₂ (twistPoly (primesIco b c) σ h) (fun p => X (p : ℕ) ω) ∂μ :=
  integral_mul_split_Ico hX ((measurable_twistPoly _ _ _).indicator hT₁)
    ((measurable_twistPoly _ _ _).indicator hT₂)

/-- **The twisted weight is multiplicative across a cut**, off the null set where some value
exceeds one in modulus. -/
lemma twist_mul_split_ae {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∀ᵐ ω ∂μ, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ 0) ω‖
        = (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖)
          * (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
                (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
                (shiftLine σ 0) ω‖) := by
  filter_upwards [] with ω
  rw [← randomEulerProductIco_mul _ hab hbc (shiftLine σ h),
    ← randomEulerProductIco_mul _ hab hbc (shiftLine σ 0), norm_mul, norm_mul, mul_pow]
  rcases eq_or_ne (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
      (shiftLine σ 0) ω‖) 0 with h0 | h0
  · rw [h0]
    simp
  rcases eq_or_ne (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
      (shiftLine σ 0) ω‖) 0 with h1 | h1
  · rw [h1]
    simp
  field_simp

/-- Almost every `ω` has all its values on the unit circle over a range, and hence a positive
block product at the real point. -/
lemma ae_norm_randomEulerProductIco_pos (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    (ha5 : 5 ≤ a) (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂μ, 0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
      (shiftLine σ 0) ω‖ := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
  rw [randomEulerProductIco_sqfree_eq, norm_prod]
  refine Finset.prod_pos fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  have hp5 : 5 ≤ (p : ℕ) := by
    have := (mem_primesIco.1 hp).2.1
    omega
  refine norm_one_add_mul_pos_of_le_one (hω p hp) ?_
  rw [norm_cpow_neg_shiftLine hpp.pos]
  have := rpow_neg_half_add_le_half hp5 hσ
  linarith

end Split

/-! ### The twisted measure of a product event -/

section SplitEvents

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ h : ℝ}

/-- **The twisted weight of a product event factorises across a cut.** -/
theorem setIntegral_twist_split₂ (hX : IsRademacherPrimeValues X μ) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) {T₁ : Set (↥(primesIco a b) → ℂ)} (hT₁ : MeasurableSet T₁)
    {T₂ : Set (↥(primesIco b c) → ℂ)} (hT₂ : MeasurableSet T₂) :
    (∫ ω in {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
          ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ 0) ω‖ ∂μ)
      = (∫ ω in {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ 0) ω‖ ∂μ)
        * ∫ ω in {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂},
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
                (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
                (shiftLine σ 0) ω‖ ∂μ := by
  have hmeas₁ : MeasurableSet {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} :=
    (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT₁
  have hmeas₂ : MeasurableSet {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} :=
    (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT₂
  have hsplit := integral_twist_indicator_mul_split (X := X) (μ := μ) (σ := σ) (h := h) hX hT₁ hT₂
  rw [← integral_indicator (hmeas₁.inter hmeas₂), ← integral_indicator hmeas₁,
    ← integral_indicator hmeas₂]
  have e1 : (∫ ω, Set.indicator ({ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
          ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂})
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ 0) ω‖) ω ∂μ)
      = ∫ ω, Set.indicator T₁ (twistPoly (primesIco a b) σ h) (fun p => X (p : ℕ) ω)
          * Set.indicator T₂ (twistPoly (primesIco b c) σ h) (fun p => X (p : ℕ) ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [twist_mul_split_ae (X := X) (σ := σ) (h := h) hab hbc] with ω hω
    by_cases h₁ : (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁
    · by_cases h₂ : (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂
      · have hmem : ω ∈ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
            ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := ⟨h₁, h₂⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h₁, Set.indicator_of_mem h₂,
          twistPoly_primesIco, twistPoly_primesIco, hω]
      · have hnot : ω ∉ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
            ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := fun hc => h₂ hc.2
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₂,
          Set.indicator_of_mem h₁, mul_zero]
    · have hnot : ω ∉ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
          ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := fun hc => h₁ hc.1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₁, zero_mul]
  have e2 : (∫ ω, Set.indicator {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖) ω ∂μ)
      = ∫ ω, Set.indicator T₁ (twistPoly (primesIco a b) σ h) (fun p => X (p : ℕ) ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    by_cases h₁ : (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁
    · have hmem : ω ∈ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} := h₁
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h₁, twistPoly_primesIco]
    · have hnot : ω ∉ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} := h₁
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₁]
  have e3 : (∫ ω, Set.indicator {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂}
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
            (shiftLine σ 0) ω‖) ω ∂μ)
      = ∫ ω, Set.indicator T₂ (twistPoly (primesIco b c) σ h) (fun p => X (p : ℕ) ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    by_cases h₂ : (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂
    · have hmem : ω ∈ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := h₂
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h₂, twistPoly_primesIco]
    · have hnot : ω ∉ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := h₂
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₂]
  rw [e1, e2, e3]
  exact hsplit

/-- The normalisations multiply across a cut. -/
theorem integral_twist_mul_split (hX : IsRademacherPrimeValues X μ) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c
            (shiftLine σ 0) ω‖ ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
              (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c
              (shiftLine σ 0) ω‖ ∂μ := by
  have h := setIntegral_twist_split₂ (X := X) (μ := μ) (σ := σ) (h := h) hX hab hbc
    (T₁ := Set.univ) MeasurableSet.univ (T₂ := Set.univ) MeasurableSet.univ
  simpa using h

end SplitEvents

/-! ### The two ingredients of the ladder event

At the two top scales the walk rises by `200` with positive twisted probability (Paley–Zygmund);
over the good range below them every suffix sum stays above `-200` with twisted probability at
least `1/2` (Chernoff and a union bound).  The levels are absolute, and so are the constants. -/

/-- Past the cut at scale `20` every prime exceeds `10^14`. -/
lemma pow_fourteen_le_scaleCut {θ : ℝ} (hθ : 20 ≤ θ) : 100000000000000 ≤ scaleCut θ := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h20 : Real.exp (20 : ℝ) = Real.exp 1 ^ (20 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h33 : (33 : ℝ) ≤ Real.exp θ := by
    have h1 : Real.exp (20 : ℝ) ≤ Real.exp θ := Real.exp_le_exp.2 hθ
    have h2 : (2.7 : ℝ) ^ (20 : ℕ) ≤ Real.exp 1 ^ (20 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he.le 20
    have h3 : (33 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith
  have hbig : ((100000000000000 : ℕ) : ℝ) ≤ blockScale θ 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    have h1 : Real.exp (33 : ℝ) ≤ Real.exp (Real.exp θ) := Real.exp_le_exp.2 h33
    have h2 : Real.exp (33 : ℝ) = Real.exp 1 ^ (33 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : (2.7 : ℝ) ^ (33 : ℕ) ≤ Real.exp 1 ^ (33 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he.le 33
    have h5 : ((100000000000000 : ℕ) : ℝ) ≤ (2.7 : ℝ) ^ (33 : ℕ) := by
      push_cast
      norm_num
    calc ((100000000000000 : ℕ) : ℝ) ≤ (2.7 : ℝ) ^ (33 : ℕ) := h5
      _ ≤ Real.exp 1 ^ (33 : ℕ) := h3
      _ = Real.exp (33 : ℝ) := h2.symm
      _ ≤ Real.exp (Real.exp θ) := h1
  have := Nat.le_floor hbig
  unfold scaleCut
  omega

/-- Past the cut at scale `20` every prime has `p^{-1/2-σ} ≤ 10^{-7}`. -/
lemma rpow_neg_half_add_le_tiny {θ : ℝ} (hθ : 20 ≤ θ) {p : ℕ} (hp : scaleCut θ ≤ p) {σ : ℝ}
    (hσ : 0 ≤ σ) : (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / 10000000 := by
  refine rpow_neg_half_add_le_inv (by norm_num : (1 : ℝ) ≤ 10000000) ?_ hσ
  have h1 : (100000000000000 : ℕ) ≤ p := le_trans (pow_fourteen_le_scaleCut hθ) hp
  have h2 : ((100000000000000 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
  push_cast at h2
  norm_num
  linarith

section Ladder

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ h : ℝ}

set_option maxRecDepth 8000 in
/-- **One scale rises by `200` with positive twisted probability.**  Paley–Zygmund at
`l = 200000`, where the mass `U ≥ 0.04` of a single scale makes the exponential moment beat
`e^{200l}`. -/
theorem le_setIntegral_twist_scale (hX : IsRademacherPrimeValues X μ) {m : ℕ} (hm : 20 ≤ m)
    (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((m : ℝ) + 1) ≤ 1) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)) (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * (Real.exp (-(20 * 200000 * 2) - 8 * 200000 ^ 2 * 2) / 4)
      ≤ ∫ ω in {ω | (200 : ℝ) ≤ Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (m : ℝ))
            (scaleCut ((m + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
  have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ha : 40000 ≤ scaleCut (m : ℝ) := by
    have h1 : (100000000000000 : ℕ) ≤ scaleCut (m : ℝ) := pow_fourteen_le_scaleCut hmR
    omega
  -- the smallness of every `u_p` over the scale
  have htiny : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / 10000000 := by
    intro p hp
    exact rpow_neg_half_add_le_tiny hmR (mem_primesIco.1 hp).2.1 hσ
  have hu0 : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      (0 : ℝ) < (p : ℝ) ^ (-(1 / 2 + σ)) := by
    intro p hp
    have hp0 : (0 : ℕ) < p := (prime_of_mem_primesIco hp).pos
    exact Real.rpow_pos_of_pos (by exact_mod_cast hp0) _
  have hlu : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      (2 * (200000 : ℝ)) * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4 := by
    intro p hp
    have h1 := htiny p hp
    have h0 := hu0 p hp
    linarith
  have hlv : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      (2 * (200000 : ℝ)) ^ 2 * (2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ 1 / 2 := by
    intro p hp
    have h1 := htiny p hp
    have h0 := hu0 p hp
    have hsq : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 ≤ 1 / 100000000000000 := by
      have := mul_le_mul h1 h1 h0.le (by norm_num)
      calc ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
          = (p : ℝ) ^ (-(1 / 2 + σ)) * (p : ℝ) ^ (-(1 / 2 + σ)) := sq _
        _ ≤ (1 / 10000000) * (1 / 10000000) := this
        _ = 1 / 100000000000000 := by norm_num
    linarith
  -- the mass of one scale
  have hmass : (0.04 : ℝ)
      ≤ ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
          ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
    have hσn : σ * Real.exp (((m + 1 : ℕ) : ℝ)) ≤ 1 := by
      have : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [this]
      exact hσm
    have h := le_sum_sq_rpow_neg_primesIco (m := m) (n := m + 1) hm (by omega) hσ hσn
    have hcast : ((m + 1 : ℕ) : ℝ) - (m : ℝ) - 1 / 10 = 9 / 10 := by push_cast; ring
    rw [hcast] at h
    have he3 : (0.045 : ℝ) ≤ Real.exp (-3) := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h2 : Real.exp (3 : ℝ) = Real.exp 1 ^ (3 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : Real.exp 1 ^ (3 : ℕ) ≤ (2.7182818286 : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
      have h4 : (2.7182818286 : ℝ) ^ (3 : ℕ) ≤ 22 := by norm_num
      have h5 : Real.exp (3 : ℝ) ≤ 22 := by linarith
      have h7 : Real.exp (-3 : ℝ) = 1 / Real.exp 3 := by
        rw [Real.exp_neg, one_div]
      rw [h7, le_div_iff₀ (Real.exp_pos 3)]
      linarith
    linarith
  -- the level condition
  have hlevel : 2 * Real.exp ((200000 : ℝ) * 200)
      ≤ Real.exp (-(200000 : ℝ) * (5 * ∑ p ∈ primesIco (scaleCut (m : ℝ))
            (scaleCut ((m + 1 : ℕ) : ℝ)), ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
          + (200000 : ℝ) ^ 2 * ((∑ p ∈ primesIco (scaleCut (m : ℝ))
            (scaleCut ((m + 1 : ℕ) : ℝ)), ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 16)) := by
    set U : ℝ := ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 with hU_def
    have hexp : -(200000 : ℝ) * (5 * U) + (200000 : ℝ) ^ 2 * (U / 16)
        = U * 2499000000 := by ring
    rw [hexp]
    have h1 : (200000 : ℝ) * 200 + 1 ≤ U * 2499000000 := by linarith
    have h2 : 2 * Real.exp ((200000 : ℝ) * 200) ≤ Real.exp ((200000 : ℝ) * 200 + 1) := by
      rw [Real.exp_add]
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos ((200000 : ℝ) * 200)).le
      linarith
    exact le_trans h2 (Real.exp_le_exp.2 h1)
  have hmain := le_setIntegral_twist_of_le (X := X) (μ := μ) (h := h) (A := 200) (l := 200000)
    hX ha hσ (by norm_num) hlu hlv hlevel
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun ω => by positivity)
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine Real.exp_le_exp.2 ?_
  have hUle : (∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ 2 := by
    have h := sum_sq_rpow_neg_primesIco_le (m := m) (n := m + 1) hm (by omega) hσ
    have hcast : ((m + 1 : ℕ) : ℝ) - (m : ℝ) + 1 / 10 = 11 / 10 := by push_cast; ring
    rw [hcast] at h
    linarith
  have hU0 : (0 : ℝ) ≤ ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
      ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hkey : (20 * 200000 + 8 * 200000 ^ 2)
      * (∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut ((m + 1 : ℕ) : ℝ)),
        ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
      ≤ (20 * 200000 + 8 * 200000 ^ 2) * 2 := mul_le_mul_of_nonneg_left hUle (by norm_num)
  linarith

end Ladder

/-! ### The good range -/

/-- The event, as a set of tuples, that the walk over a range ends at or below `-A`. -/
noncomputable def twistDown (S : Finset ℕ) (σ A : ℝ) : Set (↥S → ℂ) :=
  {v | Real.log ‖primePoly S (shiftLine σ 0) v‖ ≤ -A}

/-- The event, as a set of tuples, that the walk over a range ends at or above `A`. -/
noncomputable def twistUp (S : Finset ℕ) (σ A : ℝ) : Set (↥S → ℂ) :=
  {v | A ≤ Real.log ‖primePoly S (shiftLine σ 0) v‖}

lemma measurableSet_twistDown (S : Finset ℕ) (σ A : ℝ) : MeasurableSet (twistDown S σ A) :=
  measurableSet_le ((continuous_primePoly S (shiftLine σ 0)).norm.measurable.log) measurable_const

lemma measurableSet_twistUp (S : Finset ℕ) (σ A : ℝ) : MeasurableSet (twistUp S σ A) :=
  measurableSet_le measurable_const
    ((continuous_primePoly S (shiftLine σ 0)).norm.measurable.log)

section Good

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ h : ℝ}

omit [MeasurableSpace Ω] in
lemma mem_twistDown_iff (a b : ℕ) (A : ℝ) (ω : Ω) :
    (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ twistDown (primesIco a b) σ A
      ↔ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ ≤ -A := by
  rw [twistDown, Set.mem_setOf_eq, primePoly_primesIco]

omit [MeasurableSpace Ω] in
lemma mem_twistUp_iff (a b : ℕ) (A : ℝ) (ω : Ω) :
    (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ twistUp (primesIco a b) σ A
      ↔ A ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ := by
  rw [twistUp, Set.mem_setOf_eq, primePoly_primesIco]

set_option maxRecDepth 8000 in
/-- **One suffix of the good range drops below `-200` with small twisted weight.** -/
theorem setIntegral_twist_suffix_le (hX : IsRademacherPrimeValues X μ) {k₀ i M : ℕ}
    (hk₀ : 20 ≤ k₀) (hk₀i : k₀ ≤ i) (hiM : i ≤ M) (hσ : 0 ≤ σ) (hσM : σ * Real.exp (M : ℝ) ≤ 1)
    (hgood : ∀ p ∈ primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ)),
      1 - Real.cos (h * Real.log p) ≤ 1 / 24) :
    (∫ ω in {ω | (fun p : ↥(primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))) => X (p : ℕ) ω)
          ∈ twistDown (primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))) σ 200},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * Real.exp (-10 - Real.exp (-3) * ((M : ℝ) - i - 1 / 10) / 200) := by
  have hiR : (20 : ℝ) ≤ (i : ℝ) := by
    have : (20 : ℕ) ≤ i := le_trans hk₀ hk₀i
    exact_mod_cast this
  have hci : 40000 ≤ scaleCut (i : ℝ) := by
    have h1 : (100000000000000 : ℕ) ≤ scaleCut (i : ℝ) := pow_fourteen_le_scaleCut hiR
    omega
  have hcut : scaleCut (k₀ : ℝ) ≤ scaleCut (i : ℝ) :=
    scaleCut_mono (by exact_mod_cast hk₀i)
  have hcut' : scaleCut (i : ℝ) ≤ scaleCut (M : ℝ) :=
    scaleCut_mono (by exact_mod_cast hiM)
  -- factorise at the cut
  have hsplit := setIntegral_twist_split₂ (X := X) (μ := μ) (σ := σ) (h := h) hX hcut hcut'
    (T₁ := Set.univ) MeasurableSet.univ
    (T₂ := twistDown (primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))) σ 200)
    (measurableSet_twistDown _ _ _)
  simp only [Set.mem_univ, Set.setOf_true, Set.univ_inter, setIntegral_univ] at hsplit
  rw [hsplit, integral_twist_mul_split (X := X) (μ := μ) (σ := σ) (h := h) hX hcut hcut']
  -- the Chernoff bound on the suffix
  have hlu : ∀ p ∈ primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ)),
      (1 / 20 : ℝ) * (2 * (p : ℝ) ^ (-(1 / 2 + σ))) ≤ 1 / 4 := by
    intro p hp
    have h1 := rpow_neg_half_add_le_tiny hiR (mem_primesIco.1 hp).2.1 hσ
    have h0 : (0 : ℝ) < (p : ℝ) ^ (-(1 / 2 + σ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (prime_of_mem_primesIco hp).pos) _
    linarith
  have hchern := setIntegral_twist_le_of_le_neg (X := X) (μ := μ) (h := h) (A := 200)
    (l := 1 / 20) hX hci hσ (by norm_num) hlu hgood
  have hsetEq : {ω | (fun p : ↥(primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))) => X (p : ℕ) ω)
        ∈ twistDown (primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))) σ 200}
      = {ω | Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ≤ -200} := by
    ext ω
    exact mem_twistDown_iff (X := X) (σ := σ) _ _ _ ω
  rw [hsetEq]
  -- the mass of the suffix
  have hmass : Real.exp (-3) * ((M : ℝ) - i - 1 / 10)
      ≤ ∑ p ∈ primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ)), ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 :=
    le_sum_sq_rpow_neg_primesIco (by omega) hiM hσ hσM
  have hN0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (i : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (i : ℝ)) (shiftLine σ 0) ω‖ ∂μ :=
    integral_nonneg fun ω => by positivity
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hN0
  refine le_trans hchern ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (integral_nonneg fun ω => by positivity)
  set U : ℝ := ∑ p ∈ primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ)),
    ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 with hU_def
  have hU0 : 0 ≤ U := by
    rw [hU_def]
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hid : -((1 / 20 : ℝ) * 200) + (-(1 / 20 : ℝ) * (U / 5) + (1 / 20 : ℝ) ^ 2 * (2 * U))
      = -10 - U / 200 := by ring
  rw [hid]
  have hmono : Real.exp (-3) * ((M : ℝ) - i - 1 / 10) / 200 ≤ U / 200 := by
    linarith
  linarith

set_option maxRecDepth 8000 in
/-- **The good range keeps every suffix above `-200`**, with at least half the twisted weight.
The union bound over the suffixes converges because the mass of the suffix from scale `i` grows
linearly in `M - i`, so the Chernoff bounds decay geometrically. -/
theorem half_le_setIntegral_twist_good (hX : IsRademacherPrimeValues X μ) {k₀ M : ℕ}
    (hk₀ : 20 ≤ k₀) (hk₀M : k₀ ≤ M) (hσ : 0 ≤ σ) (hσM : σ * Real.exp (M : ℝ) ≤ 1)
    (hgood : ∀ p ∈ primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)),
      1 - Real.cos (h * Real.log p) ≤ 1 / 24) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ) / 2
      ≤ ∫ ω in {ω | ∀ i, k₀ ≤ i → i < M → (-200 : ℝ)
            ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
  have hk₀5 : 5 ≤ scaleCut (k₀ : ℝ) := five_le_scaleCut (by
    have : (20 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
    linarith)
  set W : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ with hW_def
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by rw [hW_def]; positivity
  have hWint : Integrable W μ := by
    have := integrable_exp_mul_twist (X := X) (μ := μ) (a := scaleCut (k₀ : ℝ))
      (b := scaleCut (M : ℝ)) (σ := σ) (h := h) (l := 0) hX hk₀5 hσ
    simpa using this
  set C : Set Ω := {ω | ∀ i, k₀ ≤ i → i < M → (-200 : ℝ)
    ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖} with hC_def
  have hCmeas : MeasurableSet C := by
    have hrw : C = ⋂ i ∈ Set.Ico k₀ M, {ω | (-200 : ℝ)
        ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖} := by
      ext ω
      simp only [hC_def, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Ico]
      exact ⟨fun hω i hi => hω i hi.1 hi.2, fun hω i h1 h2 => hω i ⟨h1, h2⟩⟩
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
      measurableSet_le measurable_const
        ((measurable_norm_randomEulerProductIco hX _ _ (shiftLine σ 0)).log)
  -- the complement is covered by the suffix events
  have hcov : ∀ ω, Set.indicator Cᶜ W ω
      ≤ ∑ d ∈ Finset.range (M - k₀), Set.indicator
          {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) =>
              X (p : ℕ) ω)
            ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) σ 200}
          W ω := by
    intro ω
    by_cases hmem : ω ∈ Cᶜ
    · rw [Set.indicator_of_mem hmem]
      obtain ⟨i, hi₁, hi₂, hi₃⟩ : ∃ i, k₀ ≤ i ∧ i < M ∧ ¬ ((-200 : ℝ)
          ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖) := by
        by_contra hc
        refine hmem fun i hi₁ hi₂ => ?_
        by_contra hc2
        exact hc ⟨i, hi₁, hi₂, hc2⟩
      have hd : M - 1 - i < M - k₀ := by omega
      have hidx : M - 1 - (M - 1 - i) = i := by omega
      have hmem' : ω ∈ {ω | (fun p : ↥(primesIco (scaleCut (((M - 1 - (M - 1 - i)) : ℕ) : ℝ))
            (scaleCut (M : ℝ))) => X (p : ℕ) ω)
          ∈ twistDown (primesIco (scaleCut (((M - 1 - (M - 1 - i)) : ℕ) : ℝ))
            (scaleCut (M : ℝ))) σ 200} := by
        rw [hidx]
        rw [Set.mem_setOf_eq, mem_twistDown_iff]
        linarith [not_le.1 hi₃]
      refine le_trans (le_of_eq (Set.indicator_of_mem hmem' W).symm) ?_
      exact Finset.single_le_sum (f := fun d => Set.indicator
        {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) =>
            X (p : ℕ) ω)
          ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) σ 200} W ω)
        (fun d _ => Set.indicator_nonneg (fun _ _ => hW0 _) ω) (Finset.mem_range.2 hd)
    · rw [Set.indicator_of_notMem hmem]
      exact Finset.sum_nonneg fun d _ => Set.indicator_nonneg (fun _ _ => hW0 _) ω
  -- each suffix event is small
  have hterm : ∀ d ∈ Finset.range (M - k₀),
      (∫ ω in {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) =>
            X (p : ℕ) ω)
          ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) σ 200},
        W ω ∂μ)
      ≤ (∫ ω, W ω ∂μ) * (Real.exp (-10) * Real.exp (-0.000225) ^ d) := by
    intro d hd
    have hdlt : d < M - k₀ := Finset.mem_range.1 hd
    have hi₁ : k₀ ≤ M - 1 - d := by omega
    have hi₂ : M - 1 - d ≤ M := by omega
    have hgood' : ∀ p ∈ primesIco (scaleCut (((M - 1 - d : ℕ)) : ℝ)) (scaleCut (M : ℝ)),
        1 - Real.cos (h * Real.log p) ≤ 1 / 24 := by
      intro p hp
      refine hgood p ?_
      obtain ⟨hpp, hlo, hhi⟩ := mem_primesIco.1 hp
      refine mem_primesIco.2 ⟨hpp, ?_, hhi⟩
      have : scaleCut (k₀ : ℝ) ≤ scaleCut (((M - 1 - d : ℕ)) : ℝ) :=
        scaleCut_mono (by exact_mod_cast hi₁)
      omega
    have hmain := setIntegral_twist_suffix_le (X := X) (μ := μ) (σ := σ) (h := h) hX hk₀ hi₁ hi₂
      hσ hσM hgood'
    rw [← hW_def] at hmain
    refine le_trans hmain ?_
    refine mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun ω => hW0 ω)
    -- the exponential decay in `d`
    have hcast : (M : ℝ) - ((M - 1 - d : ℕ) : ℝ) - 1 / 10 = (d : ℝ) + 9 / 10 := by
      have h1 : ((M - 1 - d : ℕ) : ℝ) = (M : ℝ) - 1 - (d : ℝ) := by
        have : (M - 1 - d : ℕ) + (1 + d) = M := by omega
        have hcast2 : (((M - 1 - d : ℕ) : ℝ)) + (1 + (d : ℝ)) = (M : ℝ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
        linarith
      rw [h1]
      ring
    rw [hcast]
    have he3 : (0.045 : ℝ) ≤ Real.exp (-3) := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h2 : Real.exp (3 : ℝ) = Real.exp 1 ^ (3 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : Real.exp 1 ^ (3 : ℕ) ≤ (2.7182818286 : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
      have h4 : (2.7182818286 : ℝ) ^ (3 : ℕ) ≤ 22 := by norm_num
      have h5 : Real.exp (3 : ℝ) ≤ 22 := by linarith
      have h7 : Real.exp (-3 : ℝ) = 1 / Real.exp 3 := by
        rw [Real.exp_neg, one_div]
      rw [h7, le_div_iff₀ (Real.exp_pos 3)]
      linarith
    have hpow : Real.exp (-0.000225 : ℝ) ^ d = Real.exp (-(0.000225 * (d : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  -- sum up
  have hcompl : (∫ ω in Cᶜ, W ω ∂μ) ≤ (∫ ω, W ω ∂μ) / 2 := by
    have hmeasd : ∀ d : ℕ, MeasurableSet
        {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) =>
            X (p : ℕ) ω)
          ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) σ 200} :=
      fun d => (measurable_primeTuple hX _ fun p hp =>
        prime_of_mem_primesIco hp) (measurableSet_twistDown _ _ _)
    have hint : ∀ d : ℕ, Integrable (Set.indicator
        {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) =>
            X (p : ℕ) ω)
          ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) σ 200}
        W) μ := fun d => hWint.indicator (hmeasd d)
    have hstep : (∫ ω in Cᶜ, W ω ∂μ)
        ≤ ∑ d ∈ Finset.range (M - k₀),
            ∫ ω in {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ))
                  (scaleCut (M : ℝ))) => X (p : ℕ) ω)
                ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ))
                  (scaleCut (M : ℝ))) σ 200}, W ω ∂μ := by
      rw [← integral_indicator hCmeas.compl]
      have hsum : ∑ d ∈ Finset.range (M - k₀),
          (∫ ω in {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ))
                (scaleCut (M : ℝ))) => X (p : ℕ) ω)
              ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ))
                (scaleCut (M : ℝ))) σ 200}, W ω ∂μ)
          = ∫ ω, ∑ d ∈ Finset.range (M - k₀), Set.indicator
              {ω | (fun p : ↥(primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ)) (scaleCut (M : ℝ))) =>
                  X (p : ℕ) ω)
                ∈ twistDown (primesIco (scaleCut ((M - 1 - d : ℕ) : ℝ))
                  (scaleCut (M : ℝ))) σ 200} W ω ∂μ := by
        rw [integral_finsetSum _ fun d _ => hint d]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_indicator (hmeasd d)]
      rw [hsum]
      exact integral_mono (hWint.indicator hCmeas.compl)
        (integrable_finsetSum _ fun d _ => hint d) hcov
    refine le_trans hstep ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hr0 : (0 : ℝ) ≤ Real.exp (-0.000225) := (Real.exp_pos _).le
    have hr1 : Real.exp (-0.000225 : ℝ) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    have hgeo : ∑ d ∈ Finset.range (M - k₀), Real.exp (-0.000225 : ℝ) ^ d
        ≤ (1 - Real.exp (-0.000225 : ℝ))⁻¹ := geom_sum_le_inv_one_sub hr0 hr1 _
    have hgap : (1 : ℝ) / 4500 ≤ 1 - Real.exp (-0.000225 : ℝ) := by
      have h1 : (1 : ℝ) + 0.000225 ≤ Real.exp (0.000225 : ℝ) := by
        linarith [Real.add_one_le_exp (0.000225 : ℝ)]
      have h2 : Real.exp (-0.000225 : ℝ) = 1 / Real.exp (0.000225 : ℝ) := by
        rw [Real.exp_neg, one_div]
      have h4 : 1 / Real.exp (0.000225 : ℝ) ≤ 1 / (1 + 0.000225) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
      rw [h2]
      norm_num at h4 ⊢
      linarith
    have hinv : (1 - Real.exp (-0.000225 : ℝ))⁻¹ ≤ 4500 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hsum2 : ∑ d ∈ Finset.range (M - k₀), Real.exp (-0.000225 : ℝ) ^ d ≤ 4500 := by
      linarith
    have hexp10 : Real.exp (-10 : ℝ) * 4500 ≤ 1 / 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h2 : Real.exp (10 : ℝ) = Real.exp 1 ^ (10 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : (2.7 : ℝ) ^ (10 : ℕ) ≤ Real.exp 1 ^ (10 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he.le 10
      have h4 : (9000 : ℝ) ≤ (2.7 : ℝ) ^ (10 : ℕ) := by norm_num
      have h5 : (9000 : ℝ) ≤ Real.exp (10 : ℝ) := by linarith
      have h6 : Real.exp (-10 : ℝ) = 1 / Real.exp 10 := by
        rw [Real.exp_neg, one_div]
      rw [h6, div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
      linarith
    have hN0 : (0 : ℝ) ≤ ∫ ω, W ω ∂μ := integral_nonneg fun ω => hW0 ω
    have hsum3 : ∑ i ∈ Finset.range (M - k₀), Real.exp (-10) * Real.exp (-0.000225 : ℝ) ^ i
        ≤ 1 / 2 := by
      rw [← Finset.mul_sum]
      linarith [mul_le_mul_of_nonneg_left hsum2 (Real.exp_pos (-10 : ℝ)).le]
    have hfin := mul_le_mul_of_nonneg_left hsum3 hN0
    linarith
  have hsplit : (∫ ω in C, W ω ∂μ) + ∫ ω in Cᶜ, W ω ∂μ = ∫ ω, W ω ∂μ :=
    integral_add_compl hCmeas hWint
  linarith

end Good

/-! ### (C3): the ladder event carries a constant share of the twisted weight -/

section Assembly

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ h : ℝ}

/-- `primesIco` is monotone in both endpoints. -/
lemma primesIco_subset {a b a' b' : ℕ} (h1 : a ≤ a') (h2 : b' ≤ b) :
    primesIco a' b' ⊆ primesIco a b := by
  intro p hp
  obtain ⟨hpp, hlo, hhi⟩ := mem_primesIco.1 hp
  exact mem_primesIco.2 ⟨hpp, by omega, by omega⟩

/-- **The walk over a suffix, from the Euler products.**  Off the null set where a value exceeds
one in modulus, `walk n - walk j = log‖F_{[c_{k₀+j}, c_k)}‖`. -/
lemma walk_sub_walk_eq_log (hX : IsRademacherPrimeValues X μ) {k₀ k : ℕ} (hk₀ : 20 ≤ k₀)
    (hk₀k : k₀ ≤ k) (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂μ, ∀ j ≤ k - k₀,
      walk (halfBlock X (k₀ : ℝ) σ 0) (k - k₀) ω - walk (halfBlock X (k₀ : ℝ) σ 0) j ω
        = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut ((k₀ + j : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
    (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))] with ω hω
  intro j hj
  have hk₀5 : 5 ≤ scaleCut (k₀ : ℝ) := five_le_scaleCut (by
    have : (20 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
    linarith)
  have hcut1 : scaleCut (k₀ : ℝ) ≤ scaleCut ((k₀ + j : ℕ) : ℝ) := by
    refine scaleCut_mono ?_
    have : (k₀ : ℕ) ≤ k₀ + j := by omega
    exact_mod_cast this
  have hcut2 : scaleCut ((k₀ + j : ℕ) : ℝ) ≤ scaleCut (k : ℝ) := by
    refine scaleCut_mono ?_
    have : (k₀ + j : ℕ) ≤ k := by omega
    exact_mod_cast this
  -- the two walks, as logarithms of Euler products
  have hwj : walk (halfBlock X (k₀ : ℝ) σ 0) j ω
      = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut ((k₀ + j : ℕ) : ℝ)) (shiftLine σ 0) ω‖ := by
    have hcast : ((k₀ : ℝ) + (j : ℝ)) = ((k₀ + j : ℕ) : ℝ) := by push_cast; ring
    have hbase := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) (k₀ : ℝ) σ 0 j hσ
      (ω := ω) (by
        rw [hcast]
        intro p hp
        exact hω p (primesIco_subset le_rfl hcut2 hp))
    rw [hcast] at hbase
    exact hbase.symm
  have hwn : walk (halfBlock X (k₀ : ℝ) σ 0) (k - k₀) ω
      = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ := by
    have hcast : ((k₀ : ℝ) + ((k - k₀ : ℕ) : ℝ)) = (k : ℝ) := by
      rw [Nat.cast_sub hk₀k]
      ring
    have hbase := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) (k₀ : ℝ) σ 0
      (k - k₀) hσ (ω := ω) (by
        rw [hcast]
        exact hω)
    rw [hcast] at hbase
    exact hbase.symm
  rw [hwj, hwn]
  -- and the product splits
  have hpos : ∀ a b : ℕ, scaleCut (k₀ : ℝ) ≤ a → b ≤ scaleCut (k : ℝ) → a ≤ b →
      0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ 0) ω‖ := by
    intro a b ha hb hab
    rw [randomEulerProductIco_sqfree_eq, norm_prod]
    refine Finset.prod_pos fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    have hmem : (p : ℕ) ∈ primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) :=
      primesIco_subset ha hb hp
    have hp5 : 5 ≤ (p : ℕ) := by
      have h1 : scaleCut (k₀ : ℝ) ≤ (p : ℕ) := (mem_primesIco.1 hmem).2.1
      omega
    refine norm_one_add_mul_pos_of_le_one (hω p hmem) ?_
    rw [norm_cpow_neg_shiftLine hpp.pos]
    have := rpow_neg_half_add_le_half hp5 hσ
    linarith
  have hmul : ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut ((k₀ + j : ℕ) : ℝ)) (shiftLine σ 0) ω‖
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut ((k₀ + j : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ := by
    rw [← randomEulerProductIco_mul _ hcut1 hcut2, norm_mul]
  rw [hmul, Real.log_mul (ne_of_gt (hpos _ _ le_rfl hcut2 hcut1))
    (ne_of_gt (hpos _ _ hcut1 le_rfl hcut2))]
  ring

set_option maxRecDepth 8000 in
/-- **(C3): the ladder event carries a constant share of the twisted weight.**

The three pieces: the top scale and the one below it each rise by `200`
(`RMF.le_setIntegral_twist_scale`, Paley–Zygmund), and all the suffixes below them stay above
`-200` (`RMF.half_le_setIntegral_twist_good`, Chernoff).  On their intersection every suffix of
the walk from `k₀` is positive, which is the ladder event. -/
theorem le_setIntegral_halfLadder_twist (hX : IsRademacherPrimeValues X μ) {k₀ k : ℕ}
    (hk₀ : 20 ≤ k₀) (hk : k₀ + 2 ≤ k) (hσ : 0 ≤ σ) (hσk : σ * Real.exp (k : ℝ) ≤ 1)
    (hh0 : 0 ≤ h) (hh : h ≤ Real.exp (-(k : ℝ))) :
    (Real.exp (-(20 * 200000 * 2) - 8 * 200000 ^ 2 * 2) / 4) ^ 2 / 2
      ≤ ∫ ω in halfLadder X σ k₀ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
  classical
  set M : ℕ := k - 2 with hM_def
  have hMk : M + 2 = k := by omega
  have hk₀M : k₀ ≤ M := by omega
  have hM20 : 20 ≤ M := by omega
  have hcut₁ : scaleCut (k₀ : ℝ) ≤ scaleCut (M : ℝ) := scaleCut_mono (by exact_mod_cast hk₀M)
  have hcut₂ : scaleCut (M : ℝ) ≤ scaleCut ((M + 1 : ℕ) : ℝ) :=
    scaleCut_mono (by exact_mod_cast Nat.le_succ M)
  have hcut₃ : scaleCut ((M + 1 : ℕ) : ℝ) ≤ scaleCut (k : ℝ) :=
    scaleCut_mono (by exact_mod_cast (by omega : M + 1 ≤ k))
  set W : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ with hW_def
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by rw [hW_def]; positivity
  -- the three events
  set E₁ : Set Ω := {ω | (200 : ℝ) ≤ Real.log ‖randomEulerProductIco
    (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((M + 1 : ℕ) : ℝ))
    (scaleCut ((M + 1 + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖} with hE₁_def
  set E₂ : Set Ω := {ω | (200 : ℝ) ≤ Real.log ‖randomEulerProductIco
    (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (M : ℝ))
    (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖} with hE₂_def
  set Eg : Set Ω := {ω | ∀ i, k₀ ≤ i → i < M → (-200 : ℝ)
    ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖} with hEg_def
  -- the ladder event contains their intersection
  have hincl : ∀ᵐ ω ∂μ, ω ∈ Eg → ω ∈ E₂ → ω ∈ E₁ → ω ∈ halfLadder X σ k₀ k := by
    filter_upwards [walk_sub_walk_eq_log (k := k) hX hk₀ (by omega) hσ,
      ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
        (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ))] with ω hwalk hω hg h2 h1
    intro j hj
    have hjk : j ≤ k - k₀ := le_of_lt hj
    have hkey := hwalk j hjk
    have hk₀5 : 5 ≤ scaleCut (k₀ : ℝ) := five_le_scaleCut (by
      have : (20 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
      linarith)
    -- the suffix from `k₀ + j` is positive
    have hpos : ∀ a b : ℕ, scaleCut (k₀ : ℝ) ≤ a → b ≤ scaleCut (k : ℝ) → a ≤ b →
        0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ := by
      intro a b ha hb hab
      rw [randomEulerProductIco_sqfree_eq, norm_prod]
      refine Finset.prod_pos fun p hp => ?_
      have hpp := prime_of_mem_primesIco hp
      have hmem : (p : ℕ) ∈ primesIco (scaleCut (k₀ : ℝ)) (scaleCut (k : ℝ)) :=
        primesIco_subset ha hb hp
      have hp5 : 5 ≤ (p : ℕ) := by
        have h1 : scaleCut (k₀ : ℝ) ≤ (p : ℕ) := (mem_primesIco.1 hmem).2.1
        omega
      refine norm_one_add_mul_pos_of_le_one (hω p hmem) ?_
      rw [norm_cpow_neg_shiftLine hpp.pos]
      have := rpow_neg_half_add_le_half hp5 hσ
      linarith
    have hsplitlog : ∀ i : ℕ, k₀ ≤ i → i ≤ M →
        Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (i : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
          = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖
            + (Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖
              + Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖) := by
      intro i hi₁ hi₂
      have hci : scaleCut (k₀ : ℝ) ≤ scaleCut (i : ℝ) := scaleCut_mono (by exact_mod_cast hi₁)
      have hciM : scaleCut (i : ℝ) ≤ scaleCut (M : ℝ) := scaleCut_mono (by exact_mod_cast hi₂)
      rw [← randomEulerProductIco_mul _ hciM (le_trans hcut₂ hcut₃) (shiftLine σ 0),
        ← randomEulerProductIco_mul _ hcut₂ hcut₃ (shiftLine σ 0), norm_mul, norm_mul,
        Real.log_mul (ne_of_gt (hpos _ _ hci (le_trans hcut₂ hcut₃) hciM))
          (ne_of_gt (mul_pos (hpos _ _ (le_trans hci hciM) hcut₃ hcut₂)
            (hpos _ _ (le_trans (le_trans hci hciM) hcut₂) le_rfl hcut₃))),
        Real.log_mul (ne_of_gt (hpos _ _ (le_trans hci hciM) hcut₃ hcut₂))
          (ne_of_gt (hpos _ _ (le_trans (le_trans hci hciM) hcut₂) le_rfl hcut₃))]
    have hMcast : ((M + 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by
      have : M + 1 + 1 = k := by omega
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    rw [hE₁_def, Set.mem_setOf_eq, hMcast] at h1
    rw [hE₂_def, Set.mem_setOf_eq] at h2
    -- two cases: the start is at most `M`, or it is `M + 1`
    rcases le_or_gt (k₀ + j) M with hcase | hcase
    · have hg' : (-200 : ℝ)
          ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut ((k₀ + j : ℕ) : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ := by
        rcases eq_or_lt_of_le hcase with heq | hlt
        · rw [heq]
          have : ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ = 1 := by
            rw [randomEulerProductIco_sqfree_eq, norm_prod, primesIco_self]
            simp
          rw [this, Real.log_one]
          norm_num
        · exact hg (k₀ + j) (by omega) hlt
      have hsum := hsplitlog (k₀ + j) (by omega) hcase
      have : (0 : ℝ) < Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((k₀ + j : ℕ) : ℝ))
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ := by
        rw [hsum]
        linarith
      linarith [hkey]
    · have hidx : k₀ + j = M + 1 := by omega
      have : (0 : ℝ) < Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((k₀ + j : ℕ) : ℝ))
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ := by
        rw [hidx]
        linarith
      linarith [hkey]
  -- the three events, as events on the values of their own ranges
  have hEgtuple : ∃ T : Set (↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) → ℂ),
      MeasurableSet T ∧ ∀ ω, ω ∈ Eg
        ↔ (fun p : ↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) => X (p : ℕ) ω) ∈ T := by
    have hone : ∀ i : ℕ, ∃ T : Set (↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) → ℂ),
        MeasurableSet T ∧ ∀ ω, ((k₀ ≤ i ∧ i < M) → (-200 : ℝ)
            ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (i : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖)
          ↔ (fun p : ↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) => X (p : ℕ) ω) ∈ T := by
      intro i
      by_cases hi : k₀ ≤ i ∧ i < M
      · have hsub : primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))
            ⊆ primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) :=
          primesIco_subset (scaleCut_mono (by exact_mod_cast hi.1)) le_rfl
        obtain ⟨T, hTm, hTiff⟩ := exists_tuple_event_of_subset (X := X) hsub
          (measurableSet_twistUp (primesIco (scaleCut (i : ℝ)) (scaleCut (M : ℝ))) σ (-200))
          (G := {ω | (-200 : ℝ) ≤ Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (i : ℝ)) (scaleCut (M : ℝ))
            (shiftLine σ 0) ω‖})
          (fun ω => (mem_twistUp_iff (X := X) (σ := σ) _ _ (-200) ω).symm)
        refine ⟨T, hTm, fun ω => ?_⟩
        rw [← hTiff ω]
        simp only [Set.mem_setOf_eq, hi, true_implies, and_self]
      · exact ⟨Set.univ, MeasurableSet.univ, fun ω => by
          simp only [Set.mem_univ, iff_true]
          intro hc
          exact absurd hc hi⟩
    choose T hTm hTiff using hone
    refine ⟨⋂ i ∈ Finset.range M, T i, ?_, fun ω => ?_⟩
    · exact MeasurableSet.biInter (Set.to_countable _) fun i _ => hTm i
    · simp only [Set.mem_iInter, Finset.mem_range]
      constructor
      · intro hω i hi
        exact (hTiff i ω).1 fun hc => hω i hc.1 hc.2
      · intro hω i hi₁ hi₂
        exact (hTiff i ω).2 (hω i hi₂) ⟨hi₁, hi₂⟩
  obtain ⟨Tg, hTgm, hTgiff⟩ := hEgtuple
  -- the two top scales, lifted to the range above `c_M`
  have hsub₂ : primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))
      ⊆ primesIco (scaleCut (M : ℝ)) (scaleCut (k : ℝ)) := primesIco_subset le_rfl hcut₃
  have hsub₁ : primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))
      ⊆ primesIco (scaleCut (M : ℝ)) (scaleCut (k : ℝ)) := primesIco_subset hcut₂ le_rfl
  have hMcast : ((M + 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by
    have : M + 1 + 1 = k := by omega
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  have hE₁iff : ∀ ω, ω ∈ E₁ ↔ (fun p : ↥(primesIco (scaleCut ((M + 1 : ℕ) : ℝ))
      (scaleCut (k : ℝ))) => X (p : ℕ) ω)
        ∈ twistUp (primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))) σ 200 := by
    intro ω
    rw [hE₁_def, Set.mem_setOf_eq, hMcast, mem_twistUp_iff]
  have hE₂iff : ∀ ω, ω ∈ E₂ ↔ (fun p : ↥(primesIco (scaleCut (M : ℝ))
      (scaleCut ((M + 1 : ℕ) : ℝ))) => X (p : ℕ) ω)
        ∈ twistUp (primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))) σ 200 := by
    intro ω
    rw [hE₂_def, Set.mem_setOf_eq, mem_twistUp_iff]
  obtain ⟨T₂', hT₂'m, hT₂'iff⟩ := exists_tuple_event_of_subset (X := X) hsub₂
    (measurableSet_twistUp (primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))) σ 200)
    (G := E₂) hE₂iff
  obtain ⟨T₁', hT₁'m, hT₁'iff⟩ := exists_tuple_event_of_subset (X := X) hsub₁
    (measurableSet_twistUp (primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))) σ 200)
    (G := E₁) hE₁iff
  -- the ladder integral dominates the intersection
  have hWint : Integrable W μ := by
    have hk₀5 : 5 ≤ scaleCut (k₀ : ℝ) := five_le_scaleCut (by
      have : (20 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
      linarith)
    have := integrable_exp_mul_twist (X := X) (μ := μ) (a := scaleCut (k₀ : ℝ))
      (b := scaleCut (k : ℝ)) (σ := σ) (h := h) (l := 0) hX hk₀5 hσ
    simpa using this
  have hmono : (∫ ω in {ω | (fun p : ↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) =>
          X (p : ℕ) ω) ∈ Tg}
        ∩ {ω | (fun p : ↥(primesIco (scaleCut (M : ℝ)) (scaleCut (k : ℝ))) => X (p : ℕ) ω)
          ∈ T₂' ∩ T₁'}, W ω ∂μ)
      ≤ ∫ ω in halfLadder X σ k₀ k, W ω ∂μ := by
    refine setIntegral_mono_set hWint.integrableOn
      (Filter.Eventually.of_forall fun ω => hW0 ω) ?_
    filter_upwards [hincl] with ω hω hmem
    refine hω ((hTgiff ω).2 hmem.1) ((hT₂'iff ω).2 hmem.2.1) ((hT₁'iff ω).2 hmem.2.2)
  refine le_trans ?_ hmono
  -- factorise the intersection
  rw [setIntegral_twist_split₂ (X := X) (μ := μ) (σ := σ) (h := h) hX hcut₁
    (le_trans hcut₂ hcut₃) hTgm (hT₂'m.inter hT₁'m)]
  have hsplit2 : (∫ ω in {ω | (fun p : ↥(primesIco (scaleCut (M : ℝ)) (scaleCut (k : ℝ))) =>
          X (p : ℕ) ω) ∈ T₂' ∩ T₁'},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
      = (∫ ω in E₂, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ h) ω‖ ^ 2
          / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * ∫ ω in E₁, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
    have hsets : {ω | (fun p : ↥(primesIco (scaleCut (M : ℝ)) (scaleCut (k : ℝ))) =>
          X (p : ℕ) ω) ∈ T₂' ∩ T₁'}
        = {ω | (fun p : ↥(primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))) =>
            X (p : ℕ) ω)
            ∈ twistUp (primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))) σ 200}
          ∩ {ω | (fun p : ↥(primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))) =>
            X (p : ℕ) ω)
            ∈ twistUp (primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))) σ 200} := by
      ext ω
      constructor
      · intro hm
        exact ⟨(hE₂iff ω).1 ((hT₂'iff ω).2 hm.1), (hE₁iff ω).1 ((hT₁'iff ω).2 hm.2)⟩
      · intro hm
        exact ⟨(hT₂'iff ω).1 ((hE₂iff ω).2 hm.1), (hT₁'iff ω).1 ((hE₁iff ω).2 hm.2)⟩
    have hs₂ : {ω | (fun p : ↥(primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))) =>
          X (p : ℕ) ω)
        ∈ twistUp (primesIco (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ))) σ 200} = E₂ := by
      ext ω
      exact (hE₂iff ω).symm
    have hs₁ : {ω | (fun p : ↥(primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))) =>
          X (p : ℕ) ω)
        ∈ twistUp (primesIco (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))) σ 200} = E₁ := by
      ext ω
      exact (hE₁iff ω).symm
    rw [hsets, setIntegral_twist_split₂ (X := X) (μ := μ) (σ := σ) (h := h) hX hcut₂ hcut₃
      (measurableSet_twistUp _ _ _) (measurableSet_twistUp _ _ _), hs₂, hs₁]
  rw [hsplit2]
  -- the three bounds
  have hEgbound : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ) / 2
      ≤ ∫ ω in {ω | (fun p : ↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) =>
            X (p : ℕ) ω) ∈ Tg},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
    have hgood : ∀ p ∈ primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)),
        1 - Real.cos (h * Real.log p) ≤ 1 / 24 := by
      intro p hp
      have hpp := prime_of_mem_primesIco hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
      have hlogp : Real.log p ≤ Real.exp (M : ℝ) + 1 := by
        refine le_trans (Real.log_le_log (by exact_mod_cast hpp.pos) ?_) (log_scaleCut_le (M : ℝ))
        exact_mod_cast (mem_primesIco.1 hp).2.2.le
      have hθ : h * Real.log p ≤ 1 / 5 := by
        have hMk : Real.exp (M : ℝ) + 1 ≤ Real.exp ((k : ℝ) - 2) + 1 := by
          have : (M : ℝ) ≤ (k : ℝ) - 2 := by
            have : (M : ℝ) + 2 = (k : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hMk
            linarith
          linarith [Real.exp_le_exp.2 this]
        have hexp : Real.exp ((k : ℝ) - 2) * Real.exp (-(k : ℝ)) = Real.exp (-2 : ℝ) := by
          rw [← Real.exp_add]
          ring_nf
        have he2 : Real.exp (-2 : ℝ) ≤ 0.14 := by
          have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
            rw [← Real.exp_add]
            norm_num
          have h3 : Real.exp (-2 : ℝ) = 1 / Real.exp 2 := by
            rw [Real.exp_neg, one_div]
          rw [h3, div_le_iff₀ (Real.exp_pos 2)]
          nlinarith [Real.exp_pos 1]
        have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
        have hexp0 : (0 : ℝ) < Real.exp (-(k : ℝ)) := Real.exp_pos _
        have hstep : h * Real.log p ≤ Real.exp (-(k : ℝ)) * (Real.exp ((k : ℝ) - 2) + 1) := by
          have h1 : h * Real.log p ≤ Real.exp (-(k : ℝ)) * Real.log p :=
            mul_le_mul_of_nonneg_right hh hlog0
          have h2 : Real.exp (-(k : ℝ)) * Real.log p
              ≤ Real.exp (-(k : ℝ)) * (Real.exp ((k : ℝ) - 2) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hexp0.le
          linarith
        have hk20 : (20 : ℝ) ≤ (k : ℝ) := by
          have : (20 : ℕ) ≤ k := by omega
          exact_mod_cast this
        have hsmall : Real.exp (-(k : ℝ)) ≤ 1 / 100 := by
          have h1 : Real.exp (-(k : ℝ)) * Real.exp (k : ℝ) = 1 := by
            rw [← Real.exp_add]
            simp
          have h2 : (100 : ℝ) ≤ Real.exp (k : ℝ) := by
            have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have h3 : Real.exp (20 : ℝ) ≤ Real.exp (k : ℝ) := Real.exp_le_exp.2 hk20
            have h4 : Real.exp (20 : ℝ) = Real.exp 1 ^ (20 : ℕ) := by
              rw [← Real.exp_nat_mul]
              norm_num
            have h5 : (2.7 : ℝ) ^ (20 : ℕ) ≤ Real.exp 1 ^ (20 : ℕ) :=
              pow_le_pow_left₀ (by norm_num) he.le 20
            have h6 : (100 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
            linarith
          nlinarith [Real.exp_pos (-(k : ℝ))]
        have hprod : Real.exp (-(k : ℝ)) * (Real.exp ((k : ℝ) - 2) + 1)
            = Real.exp (-2 : ℝ) + Real.exp (-(k : ℝ)) := by
          rw [mul_add, mul_one, ← Real.exp_add, show -(k : ℝ) + ((k : ℝ) - 2) = -2 by ring]
        have hstep2 : Real.exp (-(k : ℝ)) * (Real.exp ((k : ℝ) - 2) + 1)
            ≤ Real.exp (-(k : ℝ)) * (Real.exp ((k : ℝ) - 2) + 1) := le_rfl
        rw [hprod] at hstep
        linarith
      have hd := abs_cos_sub_one_le (h * Real.log p)
      rw [abs_le] at hd
      have hθ0 : 0 ≤ h * Real.log p := mul_nonneg hh0 (Real.log_nonneg hp1)
      nlinarith [hd.1]
    have hσM : σ * Real.exp (M : ℝ) ≤ 1 := by
      have h1 : Real.exp (M : ℝ) ≤ Real.exp (k : ℝ) :=
        Real.exp_le_exp.2 (by exact_mod_cast (by omega : M ≤ k))
      nlinarith [Real.exp_pos (M : ℝ)]
    have hbase := half_le_setIntegral_twist_good (X := X) (μ := μ) (σ := σ) (h := h)
      hX hk₀ hk₀M hσ hσM hgood
    have hsetg : Eg = {ω | (fun p : ↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) =>
        X (p : ℕ) ω) ∈ Tg} := by
      ext ω
      exact hTgiff ω
    rw [← hsetg]
    exact hbase
  have hE₂bound := le_setIntegral_twist_scale (X := X) (μ := μ) (h := h) hX hM20 hσ (by
    have h1 : Real.exp ((M : ℝ) + 1) ≤ Real.exp (k : ℝ) := by
      refine Real.exp_le_exp.2 ?_
      have : (M : ℝ) + 2 = (k : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hMk
      linarith
    nlinarith [Real.exp_pos ((M : ℝ) + 1)])
  have hE₁bound := le_setIntegral_twist_scale (X := X) (μ := μ) (h := h) hX
    (by omega : 20 ≤ M + 1) hσ (by
    have h1 : Real.exp (((M + 1 : ℕ) : ℝ) + 1) ≤ Real.exp (k : ℝ) := by
      refine Real.exp_le_exp.2 ?_
      have : (M : ℝ) + 2 = (k : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hMk
      push_cast
      linarith
    nlinarith [Real.exp_pos (((M + 1 : ℕ) : ℝ) + 1)])
  rw [show M + 1 + 1 = k from by omega] at hE₁bound
  have hE₁set : E₁ = {ω | (200 : ℝ) ≤ Real.log ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((M + 1 : ℕ) : ℝ))
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖} := by
    rw [hE₁_def, hMcast]
  rw [← hE₁set] at hE₁bound
  -- the three normalisations are at least one
  have hk₀5 : 5 ≤ scaleCut (k₀ : ℝ) := five_le_scaleCut (by
    have : (20 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
    linarith)
  have hM5 : 5 ≤ scaleCut (M : ℝ) := five_le_scaleCut (by
    have : (20 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM20
    linarith)
  have hM15 : 5 ≤ scaleCut ((M + 1 : ℕ) : ℝ) := five_le_scaleCut (by
    have : (20 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      have : (20 : ℕ) ≤ M + 1 := by omega
      exact_mod_cast this
    linarith)
  have hNA : (1 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ :=
    one_le_integral_twist hX hk₀5 hσ
  have hNmid : (1 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (M : ℝ))
        (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (M : ℝ))
        (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖ ∂μ :=
    one_le_integral_twist hX hM5 hσ
  have hNtop : (1 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((M + 1 : ℕ) : ℝ))
        (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ :=
    one_le_integral_twist hX hM15 hσ
  set pzc : ℝ := Real.exp (-(20 * 200000 * 2) - 8 * 200000 ^ 2 * 2) / 4 with hpzc_def
  have hpzc0 : 0 < pzc := by
    rw [hpzc_def]
    positivity
  -- the three factors
  have hf₁ : (1 : ℝ) / 2 ≤ ∫ ω in {ω | (fun p : ↥(primesIco (scaleCut (k₀ : ℝ))
        (scaleCut (M : ℝ))) => X (p : ℕ) ω) ∈ Tg},
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
        / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
    linarith
  have hf₂ : pzc ≤ ∫ ω in E₂, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (M : ℝ))
        (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (M : ℝ))
        (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
    refine le_trans ?_ hE₂bound
    nlinarith
  have hf₃ : pzc ≤ ∫ ω in E₁, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((M + 1 : ℕ) : ℝ))
        (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
      / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ∂μ := by
    refine le_trans ?_ hE₁bound
    nlinarith
  calc pzc ^ 2 / 2 = 1 / 2 * (pzc * pzc) := by ring
    _ ≤ (∫ ω in {ω | (fun p : ↥(primesIco (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ))) =>
            X (p : ℕ) ω) ∈ Tg},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k₀ : ℝ)) (scaleCut (M : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
        * ((∫ ω in E₂, ‖randomEulerProductIco
              (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (M : ℝ))
              (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ h) ω‖ ^ 2
            / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (M : ℝ)) (scaleCut ((M + 1 : ℕ) : ℝ)) (shiftLine σ 0) ω‖ ∂μ)
          * ∫ ω in E₁, ‖randomEulerProductIco
                (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ((M + 1 : ℕ) : ℝ))
                (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              / ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ((M + 1 : ℕ) : ℝ)) (scaleCut (k : ℝ))
                (shiftLine σ 0) ω‖ ∂μ) := by
        refine mul_le_mul hf₁ (mul_le_mul hf₂ hf₃ hpzc0.le
          (le_trans hpzc0.le hf₂)) (by positivity) (le_trans (by norm_num) hf₁)

end Assembly
end RMF
