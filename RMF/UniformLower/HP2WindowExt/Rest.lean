/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.Lobe

/-!
# HP2's window integral: the primes above block `r`

The tubes constrain the blocks `m < r` only.  The primes of `[c_r, y)` — every prime above block
`r - 1` up to the tilt cutoff `y`, the top block partial — are independent of the tubes, so they
multiply the pair integral by their pair mass (`RMF.integral_hp1Tube_inter_rest_le`):
`E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] ≤ E‖F_y(s₁)‖²E‖F_y(s₂)‖²·K·e^T` once the same holds with `K`
alone over the blocks `m < r`, where `T = 2∫_A^U cos(|h₁ - h₂|u)e^{-2σu}/u du + 10⁻¹⁹`,
`A = e^{r+k}`, `U = RMF.restU k r y ≥ A`.

* **The top block** `R = RMF.restTop k r y` (`c_R ≤ y < c_{R+1}`): its partial cosine sum against
  the integral up to `log max(y - 1, e^{e^{R+k}})` by the explicit PNT
  (`RMF.abs_rangeCosSum_top_sub_integral_le`), as for a full block.
* **The pair mass over any prime range** (`RMF.integral_normSq_mul_normSq_Ico_le`) and the rest's
  exponent (`RMF.rest_exponent_le`): the difference frequency's integral, the sum frequency's
  `≤ e^{1-r}`, the PNT errors and the quadratic remainder.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The cosine sums over a prime range -/

/-- The cosine sum over the primes of `[a, b)`: `∑_p cos(τ log p)p^{-1-2σ}`. -/
noncomputable def rangeCosSum (a b : ℕ) (σ τ : ℝ) : ℝ :=
  ∑ p ∈ primesIco a b, Real.cos (τ * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ)

/-- The quadratic remainder over the primes of `[a, b)`: `∑_p (p^{-1-2σ})²`. -/
noncomputable def rangeSqSum (a b : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2

/-- A block as the primes between two cutoffs. -/
lemma primeBlockSub_eq_primesIcoSub (θ : ℝ) (m : ℕ) :
    primeBlockSub θ m = primesIcoSub (⌊blockScale θ m⌋₊ + 1) (⌊blockScale θ (m + 1)⌋₊ + 1) := by
  rw [primeBlockSub, harperBlock, blockScale_rpow_inv_exp_one]

/-- **A sum over the primes between two cutoffs is the sum over the blocks between them.** -/
lemma sum_primesIco_cut_eq_sum_blocks (θ : ℝ) {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℝ) :
    ∑ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), f p
      = ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m, f (p : ℕ) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have hempty : primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1) = ∅ := by
      ext p
      simp only [mem_primesIco, Finset.notMem_empty, iff_false, not_and]
      intro _ h1 h2
      omega
    rw [hempty, Finset.Ico_self, Finset.sum_empty, Finset.sum_empty]
  | succ b hb ih =>
    have hmono : ∀ i j : ℕ, i ≤ j → ⌊blockScale θ i⌋₊ + 1 ≤ ⌊blockScale θ j⌋₊ + 1 :=
      fun i j hij => Nat.succ_le_succ (Nat.floor_mono (blockScale_mono θ hij))
    rw [← primesIco_union (hmono a b hb) (hmono b (b + 1) (Nat.le_succ b)),
      Finset.sum_union (disjoint_primesIco _ _ _), ih, Finset.sum_Ico_succ_top hb,
      primeBlockSub_eq_primesIcoSub, sum_primesIcoSub]

/-- The cosine is even: `rangeCosSum` at `|τ|` is `rangeCosSum` at `τ`. -/
lemma rangeCosSum_abs (a b : ℕ) (σ τ : ℝ) : rangeCosSum a b σ |τ| = rangeCosSum a b σ τ := by
  unfold rangeCosSum
  refine Finset.sum_congr rfl fun p hp => ?_
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [← abs_of_nonneg hl, ← abs_mul, Real.cos_abs, abs_of_nonneg hl]

/-- `rangeCosSum` over the blocks between two cutoffs. -/
lemma rangeCosSum_cut_eq (k : ℕ) {a b : ℕ} (hab : a ≤ b) (σ τ : ℝ) :
    rangeCosSum (⌊blockScale k a⌋₊ + 1) (⌊blockScale k b⌋₊ + 1) σ τ
      = ∑ m ∈ Finset.Ico a b, blockCosSum k σ τ m := by
  unfold rangeCosSum
  rw [sum_primesIco_cut_eq_sum_blocks (k : ℝ) hab]
  rfl

/-- The prime ranges add up. -/
lemma rangeCosSum_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (σ τ : ℝ) :
    rangeCosSum a c σ τ = rangeCosSum a b σ τ + rangeCosSum b c σ τ := by
  unfold rangeCosSum
  rw [← primesIco_union hab hbc, Finset.sum_union (disjoint_primesIco _ _ _)]

/-! ### The top block -/

/-- Past any cutoff lies a block's cutoff: `y < c_{r+y+1}`. -/
lemma exists_lt_cut (k r y : ℕ) : ∃ n : ℕ, y < ⌊blockScale k (r + n + 1)⌋₊ + 1 := by
  refine ⟨y, Nat.lt_succ_of_le (Nat.le_floor ?_)⟩
  have h1 : ((r + y + 1 : ℕ) : ℝ) + k ≤ Real.exp (((r + y + 1 : ℕ) : ℝ) + k) := by
    linarith [Real.add_one_le_exp (((r + y + 1 : ℕ) : ℝ) + k)]
  have h2 : Real.exp (((r + y + 1 : ℕ) : ℝ) + k) ≤ blockScale k (r + y + 1) := by
    rw [blockScale]
    linarith [Real.add_one_le_exp (Real.exp (((r + y + 1 : ℕ) : ℝ) + k))]
  have h3 : (y : ℝ) ≤ ((r + y + 1 : ℕ) : ℝ) + k := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) k]
  linarith

/-- **The top block of the rest**: the block `R ≥ r` with `c_R ≤ y < c_{R+1}` (for `y ≥ c_r`). -/
noncomputable def restTop (k r y : ℕ) : ℕ := r + Nat.find (exists_lt_cut k r y)

lemma le_restTop (k r y : ℕ) : r ≤ restTop k r y := Nat.le_add_right _ _

lemma lt_cut_restTop (k r y : ℕ) : y < ⌊blockScale k (restTop k r y + 1)⌋₊ + 1 :=
  Nat.find_spec (exists_lt_cut k r y)

lemma cut_restTop_le {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    ⌊blockScale k (restTop k r y)⌋₊ + 1 ≤ y := by
  unfold restTop
  rcases Nat.eq_zero_or_pos (Nat.find (exists_lt_cut k r y)) with h | h
  · rw [h, add_zero]
    exact hyr
  · have hmin := Nat.find_min (exists_lt_cut k r y) (Nat.sub_lt h one_pos)
    rw [not_lt, show r + (Nat.find (exists_lt_cut k r y) - 1) + 1
      = r + Nat.find (exists_lt_cut k r y) by omega] at hmin
    exact hmin

/-- **The rest's length** `U = log max(y - 1, e^{e^{R+k}})`, `R = RMF.restTop k r y`. -/
noncomputable def restU (k r y : ℕ) : ℝ :=
  Real.log (max ((y : ℝ) - 1) (blockScale k (restTop k r y)))

/-- `e^{R+k} ≤ U`. -/
lemma exp_restTop_le_restU (k r y : ℕ) :
    Real.exp ((restTop k r y : ℝ) + k) ≤ restU k r y := by
  unfold restU
  rw [← log_blockScale]
  exact Real.log_le_log (blockScale_pos _ _) (le_max_right _ _)

/-- `e^{r+k} ≤ U`. -/
lemma exp_le_restU (k r y : ℕ) : Real.exp ((r : ℝ) + k) ≤ restU k r y := by
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_restTop_le_restU k r y)
  have : (r : ℝ) ≤ restTop k r y := by exact_mod_cast le_restTop k r y
  linarith

/-- `⌊max(y - 1, e^{e^{R+k}})⌋₊ = y - 1` once `c_R ≤ y`. -/
lemma floor_max_eq {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    ⌊max ((y : ℝ) - 1) (blockScale k (restTop k r y))⌋₊ = y - 1 := by
  have hR := cut_restTop_le hyr
  have hy1 : 1 ≤ y := by omega
  have hcast : (y : ℝ) - 1 = ((y - 1 : ℕ) : ℝ) := by push_cast [hy1]; ring
  rcases le_total (blockScale k (restTop k r y)) ((y : ℝ) - 1) with h | h
  · rw [max_eq_left h, hcast, Nat.floor_natCast]
  · rw [max_eq_right h]
    have h1 : y - 1 ≤ ⌊blockScale k (restTop k r y)⌋₊ :=
      Nat.le_floor (by rw [← hcast]; exact h)
    omega

/-- **The top block's partial cosine sum against its integral**, by the explicit PNT: for
`τ, σ ≥ 0`, `r + k ≥ 104` and `y ≥ c_r`, `∑_{c_R ≤ p < y} cos(τ log p)p^{-1-2σ}` is within
`(τ+1)e^{104-(R+k)}/10²⁸` of `∫_{e^{R+k}}^{U} cos(τu)e^{-2σu}/u du` (the proof of
`RMF.abs_sum_cos_primeBlockSub_sub_integral_le_decay` with the block's top at
`max(y - 1, e^{e^{R+k}}) ≤ e^{e^{R+k+1}}`). -/
theorem abs_rangeCosSum_top_sub_integral_le {k r y : ℕ} {σ τ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ)
    (hkr : 104 ≤ (r : ℝ) + k) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    |rangeCosSum (⌊blockScale k (restTop k r y)⌋₊ + 1) y σ τ
        - ∫ u in Real.exp ((restTop k r y : ℝ) + k)..restU k r y,
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ (τ + 1) * Real.exp (104 - ((restTop k r y : ℝ) + k)) / 10 ^ 28 := by
  set R := restTop k r y with hRdef
  have hm : 104 ≤ (R : ℝ) + k := by
    have : (r : ℝ) ≤ R := by exact_mod_cast le_restTop k r y
    linarith
  obtain ⟨hx₀2, hEθ⟩ := abs_theta_sub_le_exp_numeral_explicit
  have hthr : Real.log (Real.log blockCosineThreshold) ≤ (R : ℝ) + k :=
    le_trans log_log_blockCosineThreshold_le_104 hm
  have hy₀2 : (2 : ℝ) ≤ blockCosineThreshold := le_trans hx₀2 (le_max_left _ _)
  set y₁ : ℝ := blockScale k R with hy₁def
  set Y : ℝ := max ((y : ℝ) - 1) y₁ with hYdef
  have hy₁pos : (0 : ℝ) < y₁ := blockScale_pos _ _
  have hlogy₁ : Real.log y₁ = Real.exp ((R : ℝ) + k) := log_blockScale _ _
  have hy₀0 : (0 : ℝ) < Real.log blockCosineThreshold := Real.log_pos (by linarith)
  have hy₀y₁ : blockCosineThreshold ≤ y₁ := by
    have hle : Real.log blockCosineThreshold ≤ Real.log y₁ := by
      rw [hlogy₁, ← Real.exp_log hy₀0]
      exact Real.exp_le_exp.2 hthr
    have h := Real.exp_le_exp.2 hle
    rwa [Real.exp_log (by linarith : (0 : ℝ) < blockCosineThreshold),
      Real.exp_log hy₁pos] at h
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hy₀2 hy₀y₁
  have hy₁Y : y₁ ≤ Y := le_max_right _ _
  have hYpos : (0 : ℝ) < Y := hy₁pos.trans_le hy₁Y
  -- the top of the range is below the next block's scale
  have hYtop : Y ≤ blockScale k (R + 1) := by
    refine max_le ?_ (blockScale_mono _ (Nat.le_succ R))
    have h1 := lt_cut_restTop k r y
    have h2 : (y : ℝ) - 1 ≤ (⌊blockScale k (R + 1)⌋₊ : ℝ) := by
      have : y ≤ ⌊blockScale k (R + 1)⌋₊ + 1 := h1.le
      have : (y : ℝ) ≤ (⌊blockScale k (R + 1)⌋₊ : ℝ) + 1 := by exact_mod_cast this
      linarith
    exact h2.trans (Nat.floor_le (blockScale_pos _ _).le)
  have hlogX : Real.log (blockScale k (R + 1)) = Real.exp ((R : ℝ) + k + 1) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hratio : Real.log Y ≤ 3 * Real.log y₁ := by
    refine (Real.log_le_log hYpos hYtop).trans ?_
    rw [hlogX, hlogy₁, show (R : ℝ) + k + 1 = 1 + ((R : ℝ) + k) by ring, Real.exp_add]
    have hpos : (0 : ℝ) < Real.exp ((R : ℝ) + k) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_d9]
  -- the sum over the partial block, as a sum over `(y₁, Y]`
  have hfl : ⌊Y⌋₊ = y - 1 := floor_max_eq hyr
  have hy1 : 1 ≤ y := by have := cut_restTop_le hyr; omega
  have hrw : rangeCosSum (⌊y₁⌋₊ + 1) y σ τ
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊Y⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [filter_prime_Ioc_eq_primesIco, hfl, Nat.sub_add_cancel hy1, rangeCosSum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primesIco hp).pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [hrw, show restU k r y = Real.log Y from rfl]
  -- the integral, in the `u = log t` form
  rw [← hlogy₁, ← integral_cosLogDiv_mul_rpow_eq (by linarith) hy₁Y]
  -- the unweighted bound on every initial sub-range
  set Mb : ℝ := 32 * 10 ^ (40 : ℕ) * (τ + 1)
      * Real.exp (-(1 / 200 : ℝ) * Real.log y₁ ^ ((1 : ℝ) / 10)) with hMbdef
  have hsub : ∀ u ∈ Set.Icc y₁ Y,
      |(∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p)
          - ∫ t in y₁..u, cosLogDiv τ t| ≤ Mb := by
    intro u hu
    exact abs_cos_prime_sum_block_sub_integral_le_threshold_of_le (by norm_num) (by positivity)
      hx₀2 hEθ hτ hy₀y₁ hu.1 (le_trans (Real.log_le_log (by linarith [hu.1]) hu.2) hratio)
  refine (abs_sum_sub_integral_weight_le_of_nonneg hy₁2 hy₁Y hσ hsub).trans ?_
  -- the numeral
  have hEeq : Real.log y₁ ^ ((1 : ℝ) / 10) = Real.exp (((R : ℝ) + k) / 10) := by
    rw [hlogy₁, ← Real.exp_mul]
    ring_nf
  have hτ1 : (0 : ℝ) ≤ τ + 1 := by linarith
  rw [hMbdef, hEeq]
  calc 32 * 10 ^ (40 : ℕ) * (τ + 1) * Real.exp (-(1 / 200 : ℝ) * Real.exp (((R : ℝ) + k) / 10))
      = (τ + 1) * (32 * 10 ^ (40 : ℕ)
          * Real.exp (-(1 / 200 : ℝ) * Real.exp (((R : ℝ) + k) / 10))) := by ring
    _ ≤ (τ + 1) * (Real.exp (104 - ((R : ℝ) + k)) / 10 ^ 28) :=
        mul_le_mul_of_nonneg_left (pnt_term_le_exp_sub hm) hτ1
    _ = (τ + 1) * Real.exp (104 - ((R : ℝ) + k)) / 10 ^ 28 := by ring

/-- **The rest's cosine sum against its integral**: for `τ, σ ≥ 0`, `r + k ≥ 104` and `y ≥ c_r`,
`|∑_{c_r ≤ p < y} cos(τ log p)p^{-1-2σ} - ∫_{e^{r+k}}^{U} cos(τu)e^{-2σu}/u du|
  ≤ 2.59(τ+1)e^{104-(r+k)}/10²⁸` — the full blocks `r ≤ m < R` telescoped
(`RMF.abs_sum_blockCosSum_sub_integral_le_of_floor`), the top block partial. -/
theorem abs_rangeCosSum_rest_sub_integral_le {k r y : ℕ} {σ τ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ)
    (hkr : 104 ≤ (r : ℝ) + k) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    |rangeCosSum (⌊blockScale k r⌋₊ + 1) y σ τ
        - ∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
            Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u|
      ≤ 2.59 * (τ + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28 := by
  set R := restTop k r y with hRdef
  have hrR : r ≤ R := le_restTop k r y
  have hrR' : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have hcut : ⌊blockScale k r⌋₊ + 1 ≤ ⌊blockScale k R⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_mono (blockScale_mono _ hrR))
  rw [rangeCosSum_split hcut (cut_restTop_le hyr), rangeCosSum_cut_eq k hrR]
  have hA := abs_sum_blockCosSum_sub_integral_le_of_floor (σ := σ) (θ := k) hrR hτ hσ hkr
  have hB := abs_rangeCosSum_top_sub_integral_le hτ hσ hkr hyr
  have h1 : Real.exp ((r : ℝ) + k) ≤ Real.exp ((R : ℝ) + k) := Real.exp_le_exp.2 (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (Real.exp_pos ((r : ℝ) + k)) h1)
    (intervalIntegrable_cos_mul_exp_div (τ := τ) (σ := σ) (Real.exp_pos ((R : ℝ) + k))
      (exp_restTop_le_restU k r y))
  rw [← hsplit]
  have he : Real.exp (104 - ((R : ℝ) + k)) ≤ Real.exp (104 - ((r : ℝ) + k)) :=
    Real.exp_le_exp.2 (by linarith)
  have hτ1 : (0 : ℝ) ≤ τ + 1 := by linarith
  have hB' : (τ + 1) * Real.exp (104 - ((R : ℝ) + k)) / 10 ^ 28
      ≤ (τ + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hτ1) (by positivity)
  have htri := abs_add_le
    (∑ m ∈ Finset.Ico r R, blockCosSum k σ τ m - ∫ u in Real.exp ((r : ℝ) + k)..Real.exp
      ((R : ℝ) + k), Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
    (rangeCosSum (⌊blockScale k R⌋₊ + 1) y σ τ - ∫ u in Real.exp ((R : ℝ) + k)..restU k r y,
      Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
  have e : (∑ m ∈ Finset.Ico r R, blockCosSum k σ τ m
        + rangeCosSum (⌊blockScale k R⌋₊ + 1) y σ τ)
      - ((∫ u in Real.exp ((r : ℝ) + k)..Real.exp ((R : ℝ) + k),
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        + ∫ u in Real.exp ((R : ℝ) + k)..restU k r y,
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
      = (∑ m ∈ Finset.Ico r R, blockCosSum k σ τ m - ∫ u in Real.exp ((r : ℝ) + k)..Real.exp
          ((R : ℝ) + k), Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u)
        + (rangeCosSum (⌊blockScale k R⌋₊ + 1) y σ τ - ∫ u in Real.exp ((R : ℝ) + k)..restU k r y,
          Real.cos (τ * u) * Real.exp (-(2 * σ) * u) / u) := by ring
  rw [e]
  have h159 : 1.59 * (τ + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28
      + (τ + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28
      = 2.59 * (τ + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28 := by ring
  linarith

/-! ### The quadratic remainder -/

/-- A block's quadratic remainder: `∑_{p∈B_m} 12(p^{-1-2σ})² ≤ e^{-m}/10²⁰` for `m + θ ≥ 20`,
`θ ≥ 0`. -/
lemma sum_sq_primeBlockSub_le {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ)
    (hm : 20 ≤ (m : ℝ) + θ) :
    ∑ p ∈ primeBlockSub θ m, 12 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  refine sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hm (C := 12) (by norm_num) fun p hp => ?_
  have hn := rpow_le_of_mem_primeBlockSub_decay hσ hm hp
  have hn0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he0 : 0 ≤ Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 := by positivity
  have he1 : Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 ≤ 1 := by
    have : Real.exp (-((m : ℝ) + θ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [div_le_one (by positivity)]
    linarith
  have he2 : Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 :=
    div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by positivity)
  have hn' : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 := by
    refine hn.trans ?_
    rw [sq]
    calc Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 * (Real.exp (-((m : ℝ) + θ)) / 10 ^ 40)
        ≤ Real.exp (-((m : ℝ) + θ)) / 10 ^ 40 * 1 := mul_le_mul_of_nonneg_left he1 he0
      _ ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 := by linarith
  rw [sq]
  have := mul_le_mul_of_nonneg_right hn' hn0
  nlinarith

/-- **The rest's quadratic remainder**: `12∑_{c_r ≤ p < y}(p^{-1-2σ})² ≤ 2/10²⁰` for `k ≥ 20`. -/
theorem rangeSqSum_rest_le {k r y : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) :
    12 * rangeSqSum (⌊blockScale k r⌋₊ + 1) y σ ≤ 2 / 10 ^ 20 := by
  set R := restTop k r y with hRdef
  have hrR : r ≤ R + 1 := (le_restTop k r y).trans (Nat.le_succ _)
  have hy : y ≤ ⌊blockScale k (R + 1)⌋₊ + 1 := (lt_cut_restTop k r y).le
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  -- enlarge the range to the next block boundary
  have hsub : rangeSqSum (⌊blockScale k r⌋₊ + 1) y σ
      ≤ rangeSqSum (⌊blockScale k r⌋₊ + 1) (⌊blockScale k (R + 1)⌋₊ + 1) σ := by
    unfold rangeSqSum
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hy⟩
  have hblocks : 12 * rangeSqSum (⌊blockScale k r⌋₊ + 1) (⌊blockScale k (R + 1)⌋₊ + 1) σ
      = ∑ m ∈ Finset.Ico r (R + 1), ∑ p ∈ primeBlockSub k m,
          12 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2 := by
    unfold rangeSqSum
    rw [Finset.mul_sum, sum_primesIco_cut_eq_sum_blocks (k : ℝ) hrR
      (fun p => 12 * ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2)]
  have hterm : ∀ m ∈ Finset.Ico r (R + 1), ∑ p ∈ primeBlockSub k m,
      12 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2 ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := fun m _ =>
    sum_sq_primeBlockSub_le hσ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hgeo := sum_exp_neg_le (Finset.Ico r (R + 1))
  have he : Real.exp 1 / (Real.exp 1 - 1) ≤ 2 := by
    have h1 := Real.exp_one_gt_d9
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc 12 * rangeSqSum (⌊blockScale k r⌋₊ + 1) y σ
      ≤ 12 * rangeSqSum (⌊blockScale k r⌋₊ + 1) (⌊blockScale k (R + 1)⌋₊ + 1) σ := by linarith
    _ ≤ ∑ m ∈ Finset.Ico r (R + 1), Real.exp (-(m : ℝ)) / 10 ^ 20 := by
        rw [hblocks]
        exact Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.Ico r (R + 1), Real.exp (-(m : ℝ))) / 10 ^ 20 := by rw [Finset.sum_div]
    _ ≤ 2 / 10 ^ 20 := div_le_div_of_nonneg_right (hgeo.trans he) (by positivity)

/-! ### The pair mass over a prime range -/

/-- The pair-mass term against its main part: `2nc/(1+n)² ≤ 2nc + 12n²` for `n ≥ 0`,
`|c| ≤ 2`. -/
lemma pairMass_term_le_main {n c : ℝ} (hn0 : 0 ≤ n) (hc : |c| ≤ 2) :
    2 * n * c / (1 + n) ^ 2 ≤ 2 * n * c + 12 * n ^ 2 := by
  have hc' := abs_le.1 hc
  rw [div_le_iff₀ (by positivity)]
  have h1 : 0 ≤ (c + 2) * (n * (2 * n + n ^ 2)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [sq_nonneg n, pow_nonneg hn0 3, pow_nonneg hn0 4]

section Mass

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The one-point moment over a prime range**:
`E‖F_{[a,b)}(s_h)‖² = ∏_{a≤p<b}(1 + p^{-1-2σ})`, whatever the height `h`. -/
theorem integral_normSq_Ico_eq_prod (hX : IsRademacherPrimeValues X μ) (a b : ℕ) (σ h : ℝ) :
    ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ h) ω‖ ^ 2 ∂μ
      = ∏ p ∈ primesIco a b, (1 + (p : ℝ) ^ (-1 - 2 * σ)) := by
  rw [hX.isRademacherRMF.integral_norm_randomEulerProductIco_sq]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hn := norm_sq_prime_cpow_neg ⟨p, prime_of_mem_primesIco hp⟩ (re_shiftLine σ h)
  congr 1

/-- **The pair mass over a prime range**: for `σ ≥ 0`,
`E‖F(s₁)‖²‖F(s₂)‖² ≤ E‖F(s₁)‖²E‖F(s₂)‖²·exp(2(C(h₁-h₂) + C(h₁+h₂)) + 12Q)` over the primes of
`[a, b)`, `C = RMF.rangeCosSum`, `Q = RMF.rangeSqSum`. -/
theorem integral_normSq_mul_normSq_Ico_le (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    {σ h₁ h₂ : ℝ} (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp (2 * (rangeCosSum a b σ (h₁ - h₂) + rangeCosSum a b σ (h₁ + h₂))
            + 12 * rangeSqSum a b σ) := by
  have hs : ∀ t : ℝ, 0 < (shiftLine σ t).re := fun t => by rw [re_shiftLine]; linarith
  refine (integral_normSq_mul_normSq_le_exp hX _ _ (hs h₁) (hs h₂)).trans ?_
  gcongr
  have hterm : ∀ p ∈ primesIco a b,
      4 * ((p : ℂ) ^ (-(shiftLine σ h₁))).re * ((p : ℂ) ^ (-(shiftLine σ h₂))).re
          / ((1 + ‖(p : ℂ) ^ (-(shiftLine σ h₁))‖ ^ 2) * (1 + ‖(p : ℂ) ^ (-(shiftLine σ h₂))‖ ^ 2))
        ≤ 2 * (Real.cos ((h₁ - h₂) * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ)
            + Real.cos ((h₁ + h₂) * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ))
          + 12 * ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2 := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hn₁ : ‖(p : ℂ) ^ (-(shiftLine σ h₁))‖ ^ 2 = (p : ℝ) ^ (-1 - 2 * σ) := by
      simpa using norm_sq_prime_cpow_neg ⟨p, hpp⟩ (re_shiftLine σ h₁)
    have hn₂ : ‖(p : ℂ) ^ (-(shiftLine σ h₂))‖ ^ 2 = (p : ℝ) ^ (-1 - 2 * σ) := by
      simpa using norm_sq_prime_cpow_neg ⟨p, hpp⟩ (re_shiftLine σ h₂)
    have hre := re_mul_re_prime_eq hpp (shiftLine σ h₁) (shiftLine σ h₂)
    simp only [re_shiftLine, im_shiftLine] at hre
    rw [show -(1 / 2 + σ + (1 / 2 + σ)) = -1 - 2 * σ by ring] at hre
    have hn0 : (0 : ℝ) ≤ (p : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hc : |Real.cos ((h₁ - h₂) * Real.log p) + Real.cos ((h₁ + h₂) * Real.log p)| ≤ 2 := by
      have := Real.abs_cos_le_one ((h₁ - h₂) * Real.log p)
      have := Real.abs_cos_le_one ((h₁ + h₂) * Real.log p)
      exact (abs_add_le _ _).trans (by linarith)
    rw [hn₁, hn₂, mul_assoc 4, hre]
    have h := pairMass_term_le_main hn0 hc
    rw [show (1 + (p : ℝ) ^ (-1 - 2 * σ)) * (1 + (p : ℝ) ^ (-1 - 2 * σ))
      = (1 + (p : ℝ) ^ (-1 - 2 * σ)) ^ 2 by ring]
    calc 4 * ((p : ℝ) ^ (-1 - 2 * σ) * (Real.cos ((h₁ - h₂) * Real.log p)
            + Real.cos ((h₁ + h₂) * Real.log p)) / 2) / (1 + (p : ℝ) ^ (-1 - 2 * σ)) ^ 2
        = 2 * (p : ℝ) ^ (-1 - 2 * σ) * (Real.cos ((h₁ - h₂) * Real.log p)
            + Real.cos ((h₁ + h₂) * Real.log p)) / (1 + (p : ℝ) ^ (-1 - 2 * σ)) ^ 2 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  unfold rangeCosSum rangeSqSum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

end Mass

/-! ### The rest's exponent -/

/-- `2/(Se^{r+k}) ≤ e^{1-r}` for the window's sum frequency `S = h₁ + h₂ ≥ 2e^{-(k+1)}`. -/
lemma two_div_sum_freq_le {k r : ℕ} {h₁ h₂ : ℝ} (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) :
    2 / ((h₁ + h₂) * Real.exp ((r : ℝ) + k)) ≤ Real.exp (1 - (r : ℝ)) := by
  obtain ⟨a₁, -⟩ := hh₁
  obtain ⟨a₂, -⟩ := hh₂
  have hS : 2 * Real.exp (-((k : ℝ) + 1)) ≤ h₁ + h₂ := by linarith
  have hS0 : 0 < h₁ + h₂ := lt_of_lt_of_le (by positivity) hS
  rw [div_le_iff₀ (by positivity)]
  have e : Real.exp (1 - (r : ℝ)) * (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp ((r : ℝ) + k))
      = 2 := by
    have h1 : Real.exp (1 - (r : ℝ)) * Real.exp (-((k : ℝ) + 1)) * Real.exp ((r : ℝ) + k) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add,
        show (1 - (r : ℝ)) + -((k : ℝ) + 1) + ((r : ℝ) + k) = 0 by ring, Real.exp_zero]
    linear_combination 2 * h1
  calc (2 : ℝ) = Real.exp (1 - (r : ℝ)) * (2 * Real.exp (-((k : ℝ) + 1))
        * Real.exp ((r : ℝ) + k)) := e.symm
    _ ≤ Real.exp (1 - (r : ℝ)) * ((h₁ + h₂) * Real.exp ((r : ℝ) + k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le)
          (Real.exp_pos _).le

/-- **The rest's pair-mass exponent**: for `k ≥ 20`, `r ≥ 2000`, `σ ≥ 0`, heights in the window
and `y ≥ c_r`, `2(C(h₁-h₂) + C(h₁+h₂)) + 12Q ≤ 2∫_{e^{r+k}}^U cos(|h₁ - h₂|u)e^{-2σu}/u du + 10⁻¹⁹`
over the primes of `[c_r, y)`, `U = RMF.restU k r y`. -/
theorem rest_exponent_le {k r y : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hr : 2000 ≤ r) (hσ : 0 ≤ σ)
    (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    2 * (rangeCosSum (⌊blockScale k r⌋₊ + 1) y σ (h₁ - h₂)
        + rangeCosSum (⌊blockScale k r⌋₊ + 1) y σ (h₁ + h₂))
      + 12 * rangeSqSum (⌊blockScale k r⌋₊ + 1) y σ
      ≤ 2 * (∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
          Real.cos (|h₁ - h₂| * u) * Real.exp (-(2 * σ) * u) / u) + 1 / 10 ^ 19 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hr' : (2000 : ℝ) ≤ r := by exact_mod_cast hr
  have hkr : 104 ≤ (r : ℝ) + k := by linarith
  obtain ⟨hS0, hS2⟩ := add_mem_of_mem_halfWindow_floor hk hh₁ hh₂
  have hSpos : 0 < h₁ + h₂ := by
    obtain ⟨a₁, -⟩ := hh₁
    obtain ⟨a₂, -⟩ := hh₂
    linarith [Real.exp_pos (-((k : ℝ) + 1))]
  have hD2 : |h₁ - h₂| ≤ 2 * Real.exp (-20) := by
    obtain ⟨a₁, b₁⟩ := hh₁
    obtain ⟨a₂, b₂⟩ := hh₂
    have e1 : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
    have e2 := Real.exp_pos (-((k : ℝ) + 1))
    rw [abs_le]
    constructor <;> linarith
  have he20 := exp_neg_twenty_le_numeral
  -- the difference frequency
  have hD := abs_rangeCosSum_rest_sub_integral_le (y := y) (σ := σ) (τ := |h₁ - h₂|)
    (abs_nonneg _) hσ hkr hyr
  rw [rangeCosSum_abs] at hD
  -- the sum frequency
  have hS := abs_rangeCosSum_rest_sub_integral_le (y := y) (σ := σ) (τ := h₁ + h₂) hS0 hσ hkr hyr
  have hSint := abs_integral_cos_mul_exp_div_le (σ := σ) hSpos hσ (Real.exp_pos ((r : ℝ) + k))
    (exp_le_restU k r y)
  have hSe := two_div_sum_freq_le (r := r) hh₁ hh₂
  -- the quadratic remainder
  have hQ := rangeSqSum_rest_le (r := r) (y := y) hk hσ
  -- the tiny errors
  have hpnt : Real.exp (104 - ((r : ℝ) + k)) ≤ Real.exp (-1916) := Real.exp_le_exp.2 (by linarith)
  have hpnt' : Real.exp (-1916) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hr1 : Real.exp (1 - (r : ℝ)) ≤ Real.exp (-1999) := Real.exp_le_exp.2 (by linarith)
  have hsmall : Real.exp (-1999) ≤ 1 / 10 ^ 30 := by
    have : Real.exp (-1999) ≤ Real.exp (-100) := Real.exp_le_exp.2 (by norm_num)
    refine this.trans ?_
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have h1 : (10 : ℝ) ^ 30 ≤ (2.7 : ℝ) ^ (100 : ℕ) := by norm_num
    have h2 : (2.7 : ℝ) ^ (100 : ℕ) ≤ Real.exp 1 ^ (100 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 100
    rw [← Real.exp_nat_mul] at h2
    norm_num at h2 ⊢
    linarith
  have hD1 : (|h₁ - h₂| + 1) * Real.exp (104 - ((r : ℝ) + k)) ≤ 2 :=
    calc (|h₁ - h₂| + 1) * Real.exp (104 - ((r : ℝ) + k)) ≤ 2 * 1 :=
          mul_le_mul (by linarith) (hpnt.trans hpnt') (Real.exp_pos _).le (by norm_num)
      _ = 2 := by ring
  have hS1 : (h₁ + h₂ + 1) * Real.exp (104 - ((r : ℝ) + k)) ≤ 2 :=
    calc (h₁ + h₂ + 1) * Real.exp (104 - ((r : ℝ) + k)) ≤ 2 * 1 :=
          mul_le_mul (by linarith) (hpnt.trans hpnt') (Real.exp_pos _).le (by norm_num)
      _ = 2 := by ring
  have hDe : 2.59 * (|h₁ - h₂| + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28
      ≤ 5.18 / 10 ^ 28 := by
    rw [mul_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hSe' : 2.59 * (h₁ + h₂ + 1) * Real.exp (104 - ((r : ℝ) + k)) / 10 ^ 28
      ≤ 5.18 / 10 ^ 28 := by
    rw [mul_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hD' := (abs_le.1 hD).2
  have hS' := (abs_le.1 hS).2
  have hSint' := (abs_le.1 hSint).2
  linarith

section Extension

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The rest multiplies in**: for `k ≥ 20`, `r ≥ 2000`, `σ ≥ 0`, heights in the window, the tilt
cutoff `y ≥ c_r` and a bound `E[1_{H₁∩H₂}W_{[c₀,c_r)}] ≤ E‖F_r(s₁)‖²E‖F_r(s₂)‖²·K` over the
blocks `m < r`, the same over all the primes below `y`:
`E[1_{H₁∩H₂}W_{[c₀,y)}] ≤ E‖F_y(s₁)‖²E‖F_y(s₂)‖²·K·e^{2∫_A^U cos(|h₁-h₂|u)e^{-2σu}/u du + 10⁻¹⁹}`,
`A = e^{r+k}`, `U = RMF.restU k r y` (independence across `c_r`, the pair mass over `[c_r, y)`). -/
theorem integral_hp1Tube_inter_rest_le (hX : IsRademacherPrimeValues X μ) {k r y : ℕ}
    {σ h₁ h₂ K : ℝ} (hk : 20 ≤ k) (hr : 2000 ≤ r) (hσ : 0 ≤ σ) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hK : ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ) * K) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * K * Real.exp (2 * (∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
            Real.cos (|h₁ - h₂| * u) * Real.exp (-(2 * σ) * u) / u) + 1 / 10 ^ 19) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hc0r : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k r⌋₊ + 1 := cut_mono k (Nat.zero_le r)
  set H : Set Ω := hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂ with hHdef
  have hHa : MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)] H :=
    (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₁).inter
      (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₂)
  have hH : MeasurableSet H := measurableSet_of_primeAlgebra hX hHa
  set W : ℕ → ℕ → Ω → ℝ := fun a b ω =>
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h₁) ω‖
        ^ 2
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ h₂) ω‖ ^ 2 with hWdef
  have hWa : ∀ a b, Measurable[primeAlgebra X a b] (W a b) := fun a b =>
    (measurable_primeAlgebra_normSq a b _).mul (measurable_primeAlgebra_normSq a b _)
  have hind : IndepFun (H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)))
      (W (⌊blockScale k r⌋₊ + 1) y) μ :=
    indepFun_of_primeAlgebra hX ((hWa _ _).indicator hHa) (hWa _ _)
  have hsplit : ∀ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) y) ω
      = H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω
        * W (⌊blockScale k r⌋₊ + 1) y ω := by
    intro ω
    by_cases hω : ω ∈ H
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      simp only [hWdef]
      rw [normSq_randomEulerProductIco_split hc0r hyr (shiftLine σ h₁) ω,
        normSq_randomEulerProductIco_split hc0r hyr (shiftLine σ h₂) ω]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  have hfac : ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) y) ω ∂μ
      = (∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ)
        * ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hsplit)]
    exact hind.integral_fun_mul_eq_mul_integral
      (((hWa _ _).indicator hHa).mono (primeAlgebra_le hX _ _) le_rfl).aestronglyMeasurable
      ((hWa _ _).mono (primeAlgebra_le hX _ _) le_rfl).aestronglyMeasurable
  set T : ℝ := 2 * (∫ u in Real.exp ((r : ℝ) + k)..restU k r y,
      Real.cos (|h₁ - h₂| * u) * Real.exp (-(2 * σ) * u) / u) + 1 / 10 ^ 19 with hTdef
  have hmass := integral_normSq_mul_normSq_Ico_le hX (⌊blockScale k r⌋₊ + 1) y
    (h₁ := h₁) (h₂ := h₂) hσ
  have hexp := rest_exponent_le hk hr hσ hh₁ hh₂ hyr
  have hmass' : ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp T :=
    hmass.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp)
      (mul_nonneg (integral_nonneg fun ω => by positivity)
        (integral_nonneg fun ω => by positivity)))
  have hsq₁ := integral_normSq_Ico_split hX hc0r hyr (shiftLine σ h₁)
  have hsq₂ := integral_normSq_Ico_split hX hc0r hyr (shiftLine σ h₂)
  rw [← integral_indicator hH] at hK ⊢
  change ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) y) ω ∂μ ≤ _
  change ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ ≤ _ at hK
  rw [hfac, hsq₁, hsq₂]
  have hA0 : 0 ≤ ∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => by simp only [hWdef]; positivity) ω
  have hB0 : 0 ≤ ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ :=
    integral_nonneg fun ω => by simp only [hWdef]; positivity
  calc (∫ ω, H.indicator (W (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)) ω ∂μ)
        * ∫ ω, W (⌊blockScale k r⌋₊ + 1) y ω ∂μ
      ≤ ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ) * K)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k r⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
          * Real.exp T) :=
        mul_le_mul hK hmass' hB0 (le_trans hA0 hK)
    _ = _ := by ring

end Extension

end RMF
