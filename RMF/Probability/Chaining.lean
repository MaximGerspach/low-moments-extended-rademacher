/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.JointLaplace
import RMF.Probability.RestrictedFirstMoment

/-!
# Chaining over the height (Hamdan's Lemma B.2)

Passing from the first moment of the chaos to its `q`-th moment needs a **maximal** barrier bound,
`P(∃h ∈ [0,1] : h ∉ G_A) ≪ e^{-2A}` (Hamdan's Lemma 2.3; Hamdan, *Partial sums of random
multiplicative functions with supercritical divisor twists*, arXiv:2604.05563), whose engine is
Hamdan's Lemma B.2, `P(max_{h ∈ [0,e^{-j})} S_j(σ+ih) > V) ≪ exp(-V²/j)` for `0 ≤ V ≤ Cj`.  This
file proves it as `P(∃h ∈ [0,r) : log‖F_y(σ+ih)‖ > V) ≤ C exp(-V²/A)`, `A = ∑_{p<y} p^{-2σ}`
(`RMF.IsSteinhausRMF.exists_measure_exists_gt_le`), on any interval `[h₀, h₀+r)`
(`RMF.IsSteinhausRMF.exists_measure_exists_gt_le_shift`) and for the lower tail
(`RMF.IsSteinhausRMF.exists_measure_exists_lt_le`).  The analytic input is Lemma B.1,
`RMF.IsSteinhausRMF.exists_measure_le_exp_pair`; this file does the chaining: a net of heights, a
telescoping decomposition of the increment along it, and two nested union bounds.

## The design, and where it departs from Hamdan's proof

* **The chain is finite.**  Hamdan telescopes along an infinite e-adic sequence and sums a series,
  which needs continuity of `h ↦ S(σ+ih)` to converge.  Here the chain stops at a level `L` where
  the residual `|S(h) - S(h_L)|` is below `1` *deterministically*, by the Lipschitz bound
  `|S(h) - S(h')| ≤ C |h - h'| ∑_{p<y} p^{-σ} log p` that
  `RMF.norm_natCast_cpow_neg_sub_le` supplies.  A finite telescoping needs no limit.

* **The net has ratio `4`, and the weights are geometric.**  Hamdan splits the increment with
  weights `1/(e(ℓ+1)²)`, which forces the level sum `∑_ℓ e^ℓ exp(-c q^{3/2} e^ℓ/(ℓ+1)³)` — a
  convergent but awkward series.  With ratio `K = 4` and weights `w_ℓ = (1/4)(3/4)^ℓ` the level
  sum becomes `∑_ℓ 4^{ℓ+1} exp(-b (9/4)^ℓ)`, and `(9/4)^ℓ ≥ 1 + ℓ` turns it into a geometric
  series.  The condition for this to work is `θ²K > 1`: the increment variance at level `ℓ` is
  `∝ K^{-ℓ}`, so the Gaussian exponent is `∝ w_ℓ² K^ℓ = (θ²K)^ℓ`, which must outgrow the `K^ℓ`
  points of the net.  Purely geometric weights with `θ² K ≤ 1` fail, and that is exactly why
  Hamdan's polynomial weights appear — they are not the only choice.
-/

open Finset MeasureTheory

namespace RMF

/-! ### The net

`netApprox r ℓ h` is the largest point of `{i r / 4^ℓ : i}` at or below `h`.  Level `0` sends every
`h ∈ [0,r)` to `0`, which is what makes the chain start at the base point. -/

/-- The largest point of the net `{i·r/4^ℓ : i ∈ ℕ}` at or below `h`, for `0 < r` and `0 ≤ h`;
for `h < 0` the value is `0`. -/
noncomputable def netApprox (r : ℝ) (ℓ : ℕ) (h : ℝ) : ℝ := ⌊h * 4 ^ ℓ / r⌋₊ * (r / 4 ^ ℓ)

lemma netApprox_le {r h : ℝ} (hr : 0 < r) (h0 : 0 ≤ h) (ℓ : ℕ) : netApprox r ℓ h ≤ h := by
  have hp : (0 : ℝ) < 4 ^ ℓ := by positivity
  have hfl : (⌊h * 4 ^ ℓ / r⌋₊ : ℝ) ≤ h * 4 ^ ℓ / r := Nat.floor_le (by positivity)
  unfold netApprox
  rw [← le_div_iff₀ (by positivity : (0 : ℝ) < r / 4 ^ ℓ)]
  calc (⌊h * 4 ^ ℓ / r⌋₊ : ℝ) ≤ h * 4 ^ ℓ / r := hfl
    _ = h / (r / 4 ^ ℓ) := by field_simp

lemma sub_netApprox_lt {r h : ℝ} (hr : 0 < r) (ℓ : ℕ) :
    h - netApprox r ℓ h < r / 4 ^ ℓ := by
  have hp : (0 : ℝ) < 4 ^ ℓ := by positivity
  have hfl : h * 4 ^ ℓ / r < ⌊h * 4 ^ ℓ / r⌋₊ + 1 := Nat.lt_floor_add_one _
  have hkey : h < netApprox r ℓ h + r / 4 ^ ℓ := by
    unfold netApprox
    rw [show (⌊h * 4 ^ ℓ / r⌋₊ : ℝ) * (r / 4 ^ ℓ) + r / 4 ^ ℓ
        = ((⌊h * 4 ^ ℓ / r⌋₊ : ℝ) + 1) * (r / 4 ^ ℓ) by ring,
      ← div_lt_iff₀ (by positivity : (0 : ℝ) < r / 4 ^ ℓ)] at *
    calc h / (r / 4 ^ ℓ) = h * 4 ^ ℓ / r := by field_simp
      _ < (⌊h * 4 ^ ℓ / r⌋₊ : ℝ) + 1 := hfl
  linarith

/-- Level `0` of the chain is the base point. -/
lemma netApprox_zero_eq {r h : ℝ} (hr : 0 < r) (hh : h < r) :
    netApprox r 0 h = 0 := by
  have hfl : ⌊h * 4 ^ (0 : ℕ) / r⌋₊ = 0 := by
    refine Nat.floor_eq_zero.2 ?_
    rw [pow_zero, mul_one, div_lt_one hr]
    exact hh
  unfold netApprox
  rw [hfl]
  simp

/-- The index of the level-`ℓ` link lies below `4 ^ ℓ`. -/
lemma netApprox_index_lt {r h : ℝ} (hr : 0 < r) (h0 : 0 ≤ h) (hh : h < r) (ℓ : ℕ) :
    ⌊h * 4 ^ ℓ / r⌋₊ < 4 ^ ℓ := by
  have hnn : (0 : ℝ) ≤ h * 4 ^ ℓ / r := by positivity
  refine (Nat.floor_lt hnn).2 ?_
  rw [div_lt_iff₀ hr]
  push_cast
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) ℓ]

/-! ### Splitting an increment along the chain

The arithmetic core: if the links of a chain add up to at least `u`, and the weights sum to at
most `1`, then some link carries at least its weighted share.  This is where the union bound over
levels comes from. -/

/-- **Some link carries its share.**  If `u ≤ ∑_{ℓ<L} a ℓ` with `0 < u` and `∑_{ℓ<L} w ℓ ≤ 1`,
`w ≥ 0`, then `u · w ℓ ≤ a ℓ` for some `ℓ < L`. -/
lemma exists_mul_le_of_sum_le {L : ℕ} {a w : ℕ → ℝ} {u : ℝ} (hu : 0 < u)
    (hwsum : ∑ ℓ ∈ Finset.range L, w ℓ ≤ 1)
    (ha : u ≤ ∑ ℓ ∈ Finset.range L, a ℓ) :
    ∃ ℓ ∈ Finset.range L, u * w ℓ ≤ a ℓ := by
  by_contra hcon
  have hcon' : ∀ ℓ ∈ Finset.range L, a ℓ < u * w ℓ := by
    intro ℓ hℓ
    by_contra h
    exact hcon ⟨ℓ, hℓ, not_lt.1 h⟩
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp only [Finset.range_zero, Finset.sum_empty] at ha
    linarith
  have hne : (Finset.range L).Nonempty := Finset.nonempty_range_iff.2 hL.ne'
  have hlt : ∑ ℓ ∈ Finset.range L, a ℓ < ∑ ℓ ∈ Finset.range L, u * w ℓ :=
    Finset.sum_lt_sum_of_nonempty hne hcon'
  have heq : ∑ ℓ ∈ Finset.range L, u * w ℓ = u * ∑ ℓ ∈ Finset.range L, w ℓ :=
    (Finset.mul_sum _ _ _).symm
  nlinarith [hu.le]

/-- The level-`ℓ` link is the level-`(ℓ+1)` link with its index rounded down to a multiple of
`4`. -/
lemma netApprox_succ_parent (r h : ℝ) (ℓ : ℕ) :
    netApprox r ℓ h = ((⌊h * 4 ^ (ℓ + 1) / r⌋₊ / 4 : ℕ) : ℝ) * (r / 4 ^ ℓ) := by
  have hrw : h * 4 ^ ℓ / r = (h * 4 ^ (ℓ + 1) / r) / ((4 : ℕ) : ℝ) := by
    push_cast
    rw [pow_succ]
    ring
  unfold netApprox
  rw [hrw, Nat.floor_div_natCast]

/-- The chain weights `w_ℓ = (1/4)(3/4)^ℓ` sum to at most `1`. -/
lemma sum_chainWeight_le (L : ℕ) :
    ∑ ℓ ∈ Finset.range L, (1 / 4 : ℝ) * (3 / 4) ^ ℓ ≤ 1 := by
  have hkey : (1 / 4 : ℝ) * (((3 / 4 : ℝ) ^ L - 1) / ((3 / 4 : ℝ) - 1)) = 1 - (3 / 4 : ℝ) ^ L := by
    field_simp
    ring
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (3 / 4 : ℝ) ≠ 1), hkey]
  have hp : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ L := by positivity
  linarith

/-! ### The chaining inclusion

Everything above the probability is deterministic: a Lipschitz function that rises by `q`
somewhere on `[0,r)` has a link of the chain that rises by its weighted share.  The Lipschitz
constant enters only through the level `L` at which the chain is cut, and it enters
*logarithmically* — which is why the crude bound `Lip ≈ ∑_p p^{-σ}\log p ≈ √y \log y`, useless as a
net spacing, costs nothing here. -/

/-- **The chaining inclusion.**  If `S` rises by at least `q` from `0` to some `h ∈ [0,r)`, is
`Lip`-Lipschitz, and the chain is cut at a level `L` with `Lip · r/4^L ≤ q/2`, then some link rises
by at least its share `(q/2)(1/4)(3/4)^ℓ`.  The link `(ℓ, i)`, `ℓ < L`, `i < 4^{ℓ+1}`, joins the
net points of index `i` and `4⌊i/4⌋` at level `ℓ+1`, which are the level-`(ℓ+1)` and level-`ℓ`
approximations to the same `h`. -/
lemma exists_link_ge {S : ℝ → ℝ} {r q Lip : ℝ} {L : ℕ} (hr : 0 < r) (hq : 0 < q)
    (hLip0 : 0 ≤ Lip) (hLip : ∀ t t' : ℝ, |S t - S t'| ≤ Lip * |t - t'|)
    (hcut : Lip * (r / 4 ^ L) ≤ q / 2)
    {h : ℝ} (hh0 : 0 ≤ h) (hhr : h < r) (hS : q ≤ S h - S 0) :
    ∃ ℓ ∈ Finset.range L, ∃ i ∈ Finset.range (4 ^ (ℓ + 1)),
      q / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
        ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1)))
          - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) := by
  have hg0 : S (netApprox r 0 h) = S 0 := by rw [netApprox_zero_eq hr hhr]
  have htel : ∑ ℓ ∈ Finset.range L,
      (S (netApprox r (ℓ + 1) h) - S (netApprox r ℓ h))
      = S (netApprox r L h) - S (netApprox r 0 h) :=
    Finset.sum_range_sub (fun ℓ => S (netApprox r ℓ h)) L
  have hres : |S h - S (netApprox r L h)| ≤ q / 2 := by
    have h1 : |h - netApprox r L h| ≤ r / 4 ^ L := by
      rw [abs_of_nonneg (by linarith [netApprox_le hr hh0 L])]
      exact (sub_netApprox_lt (h := h) hr L).le
    have h2 := hLip h (netApprox r L h)
    have h3 : Lip * |h - netApprox r L h| ≤ Lip * (r / 4 ^ L) :=
      mul_le_mul_of_nonneg_left h1 hLip0
    linarith
  have hsum : q / 2 ≤ ∑ ℓ ∈ Finset.range L,
      (S (netApprox r (ℓ + 1) h) - S (netApprox r ℓ h)) := by
    rw [htel, hg0]
    have h4 := abs_le.1 hres
    linarith
  obtain ⟨ℓ, hℓ, hlink⟩ := exists_mul_le_of_sum_le (by linarith : (0 : ℝ) < q / 2)
    (sum_chainWeight_le L) hsum
  refine ⟨ℓ, hℓ, ⌊h * 4 ^ (ℓ + 1) / r⌋₊, ?_, ?_⟩
  · exact Finset.mem_range.2 (netApprox_index_lt hr hh0 hhr (ℓ + 1))
  · have hA : netApprox r (ℓ + 1) h = ((⌊h * 4 ^ (ℓ + 1) / r⌋₊ : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)) :=
      rfl
    have hB : netApprox r ℓ h
        = ((4 * (⌊h * 4 ^ (ℓ + 1) / r⌋₊ / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)) := by
      rw [netApprox_succ_parent r h ℓ]
      push_cast
      rw [pow_succ]
      ring
    rw [← hA, ← hB]
    exact hlink

/-! ### The Lipschitz bound

The chain is cut where the residual is below `q/2`, and the level at which that happens depends on
a Lipschitz constant for `h ↦ S(σ+ih)`.  The available constant is crude — `∑_{p<y} p^{-σ}\log p`,
of size `√y \log y` on the critical line — but it enters only through `\log_4` of itself, so its
size costs nothing. -/

/-- **`localLog` is Lipschitz in the weight**, away from the boundary of the disc:
`|localLog w z - localLog w' z| ≤ ‖w - w'‖/(1-θ)` for `‖z‖ ≤ 1` and `‖w‖, ‖w'‖ ≤ θ < 1`. -/
lemma abs_localLog_sub_localLog_le {w w' z : ℂ} {θ : ℝ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ θ)
    (hw' : ‖w'‖ ≤ θ) (hθ : θ < 1) :
    |localLog w z - localLog w' z| ≤ ‖w - w'‖ / (1 - θ) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hlow : ∀ v : ℂ, ‖v‖ ≤ θ → 1 - θ ≤ ‖1 - z * v‖ := by
    intro v hv
    have h1 : ‖z * v‖ ≤ θ := by
      rw [norm_mul]
      calc ‖z‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
        _ = ‖v‖ := one_mul _
        _ ≤ θ := hv
    have h2 := norm_sub_norm_le (1 : ℂ) (z * v)
    rw [norm_one] at h2
    linarith
  have hchord : |‖1 - z * w'‖ - ‖1 - z * w‖| ≤ ‖w - w'‖ := by
    have h := abs_norm_sub_norm_le (1 - z * w') (1 - z * w)
    have he : 1 - z * w' - (1 - z * w) = z * (w - w') := by ring
    rw [he, norm_mul] at h
    calc |‖1 - z * w'‖ - ‖1 - z * w‖| ≤ ‖z‖ * ‖w - w'‖ := h
      _ ≤ 1 * ‖w - w'‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = ‖w - w'‖ := one_mul _
  have hstep : |localLog w z - localLog w' z|
      = |Real.log ‖1 - z * w'‖ - Real.log ‖1 - z * w‖| := by
    rw [localLog, localLog]
    congr 1
    ring
  rw [hstep]
  refine le_trans (abs_log_sub_log_le h1θ (hlow w' hw') (hlow w hw)) ?_
  exact (div_le_div_iff_of_pos_right h1θ).2 hchord

/-- **The walk is Lipschitz in the height**, with constant
`(1-2^{-σ})^{-1} ∑_{p∈B} p^{-σ}\log p`.  Deterministic on the set where the values are
unimodular — which is what lets the chain be cut at a finite level. -/
lemma abs_sum_localLog_sub_le {B : Finset ℕ} (hB : ∀ p ∈ B, Nat.Prime p) {Y : ℕ → ℂ}
    (hY : ∀ p ∈ B, ‖Y p‖ ≤ 1) {s s' : ℂ} {σ : ℝ} (hs : s.re = σ) (hs' : s'.re = σ)
    (hσ : 0 < σ) :
    |(∑ p ∈ B, localLog ((p : ℂ) ^ (-s)) (Y p)) - ∑ p ∈ B, localLog ((p : ℂ) ^ (-s')) (Y p)|
      ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ * (∑ p ∈ B, (p : ℝ) ^ (-σ) * Real.log p) * |s.im - s'.im| := by
  have hθ : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1θ : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by linarith
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p hp => ?_)
  have hpp := hB p hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
  have hnorm : ∀ u : ℂ, u.re = σ → ‖((p : ℂ)) ^ (-u)‖ = (p : ℝ) ^ (-σ) := by
    intro u hu
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re, hu]
  have hle : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have hdiff := norm_natCast_cpow_neg_sub_le (p := p) hpp.pos hs hs'
  have hloc := abs_localLog_sub_localLog_le (θ := (2 : ℝ) ^ (-σ)) (hY p hp)
    (by rw [hnorm s hs]; exact hle) (by rw [hnorm s' hs']; exact hle) hθ
  calc |localLog ((p : ℂ) ^ (-s)) (Y p) - localLog ((p : ℂ) ^ (-s')) (Y p)|
      ≤ ‖(p : ℂ) ^ (-s) - (p : ℂ) ^ (-s')‖ / (1 - (2 : ℝ) ^ (-σ)) := hloc
    _ ≤ ((p : ℝ) ^ (-σ) * (|s.im - s'.im| * Real.log p)) / (1 - (2 : ℝ) ^ (-σ)) :=
        (div_le_div_iff_of_pos_right h1θ).2 hdiff
    _ = (1 - (2 : ℝ) ^ (-σ))⁻¹ * ((p : ℝ) ^ (-σ) * Real.log p) * |s.im - s'.im| := by
        field_simp

/-! ### The level sum

The union bound over the net costs `4^{ℓ+1}` at level `ℓ`, and Lemma B.1 pays `exp(-b (9/4)^ℓ)`
there: the increment variance at level `ℓ` is proportional to `4^{-ℓ}` and the weight is
`(3/4)^ℓ/4`, so the Gaussian exponent carries `(3/4)^{2ℓ} 4^ℓ = (9/4)^ℓ`.  Since `9/4 > 1` the
exponent outgrows the count, and `(9/4)^ℓ ≥ 1 + ℓ` collapses the sum to a geometric series.

This is the inequality the whole choice of net ratio and weights is for.  With Hamdan's weights
`1/(e(ℓ+1)²)` the same sum is `∑_ℓ e^ℓ exp(-b e^ℓ/(ℓ+1)^4)`, which converges but is not
geometric. -/

/-- `(9/4)^ℓ ≥ 1 + ℓ`. -/
lemma one_add_le_pow_nine_quarters (ℓ : ℕ) : (1 : ℝ) + ℓ ≤ (9 / 4 : ℝ) ^ ℓ := by
  induction ℓ with
  | zero => norm_num
  | succ n ih =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hpow : (0 : ℝ) < (9 / 4 : ℝ) ^ n := by positivity
      rw [pow_succ]
      push_cast
      nlinarith

/-- A partial geometric series is below its limit. -/
lemma geom_sum_le_inv_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i ≤ (1 - x)⁻¹ := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have he : (x ^ n - 1) / (x - 1) = (1 - x ^ n) / (1 - x) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [geom_sum_eq (by linarith : x ≠ 1), he, ← one_div]
  exact (div_le_div_iff_of_pos_right h1x).2 (by nlinarith [pow_nonneg hx0 n])

/-- **The level sum.**  `∑_{ℓ<L} 4^{ℓ+1} exp(-b (9/4)^ℓ) ≤ 8 e^{-b}` for `b ≥ 3`.

The threshold `b ≥ 3` is what makes `4 e^{-b} ≤ 1/2`, so that the geometric series converges with
a constant; below it the chaining is not used at all — the corresponding levels of the `q`-sum are
handled by the one-point tail. -/
lemma sum_level_le {b : ℝ} (hb : 3 ≤ b) (L : ℕ) :
    ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1) * Real.exp (-(b * (9 / 4 : ℝ) ^ ℓ))
      ≤ 8 * Real.exp (-b) := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hexp0 : (0 : ℝ) < Real.exp (-b) := Real.exp_pos _
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have he3 : (8 : ℝ) ≤ Real.exp 3 := by
    have hsplit : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [hsplit]
    nlinarith [he1, Real.exp_pos (1 : ℝ)]
  have hsmall : 4 * Real.exp (-b) ≤ 1 / 2 := by
    have h1 : Real.exp (-b) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(3 : ℝ)) = (Real.exp 3)⁻¹ := by rw [Real.exp_neg]
    have h3 : (Real.exp 3)⁻¹ ≤ (8 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (Real.exp_pos 3) (by norm_num)]
      exact he3
    rw [h2] at h1
    linarith
  have hpow : ∀ n : ℕ, Real.exp (-b) ^ n = Real.exp (-(b * n)) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hterm : ∀ ℓ ∈ Finset.range L,
      (4 : ℝ) ^ (ℓ + 1) * Real.exp (-(b * (9 / 4 : ℝ) ^ ℓ))
        ≤ 4 * Real.exp (-b) * (4 * Real.exp (-b)) ^ ℓ := by
    intro ℓ _
    have h1 : b * (1 + (ℓ : ℝ)) ≤ b * (9 / 4 : ℝ) ^ ℓ :=
      mul_le_mul_of_nonneg_left (one_add_le_pow_nine_quarters ℓ) hb0
    have h2 : Real.exp (-(b * (9 / 4 : ℝ) ^ ℓ)) ≤ Real.exp (-(b * (1 + (ℓ : ℝ)))) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-(b * (1 + (ℓ : ℝ)))) = Real.exp (-b) * Real.exp (-b) ^ ℓ := by
      rw [hpow ℓ, ← Real.exp_add]
      congr 1
      ring
    have h4 : (4 : ℝ) ^ (ℓ + 1) * Real.exp (-(b * (1 + (ℓ : ℝ))))
        = 4 * Real.exp (-b) * (4 * Real.exp (-b)) ^ ℓ := by
      rw [h3, mul_pow]
      ring
    calc (4 : ℝ) ^ (ℓ + 1) * Real.exp (-(b * (9 / 4 : ℝ) ^ ℓ))
        ≤ (4 : ℝ) ^ (ℓ + 1) * Real.exp (-(b * (1 + (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * Real.exp (-b) * (4 * Real.exp (-b)) ^ ℓ := h4
  calc ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1) * Real.exp (-(b * (9 / 4 : ℝ) ^ ℓ))
      ≤ ∑ ℓ ∈ Finset.range L, 4 * Real.exp (-b) * (4 * Real.exp (-b)) ^ ℓ :=
        Finset.sum_le_sum hterm
    _ = 4 * Real.exp (-b) * ∑ ℓ ∈ Finset.range L, (4 * Real.exp (-b)) ^ ℓ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * Real.exp (-b) * (1 - 4 * Real.exp (-b))⁻¹ :=
        mul_le_mul_of_nonneg_left
          (geom_sum_le_inv_one_sub (by positivity) (by linarith) L) (by positivity)
    _ ≤ 8 * Real.exp (-b) := by
        have hinv : (1 - 4 * Real.exp (-b))⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        nlinarith [hexp0.le]

/-! ### The height sum

The outer union bound runs over the level `q` of the base point, and each term carries
`exp(-(V-q-1)²/A)` from the one-point tail together with `exp(-c q²)` from the chaining.
Expanding the square,

`-(V-q-1)²/A = -V²/A + (2V(q+1) - (q+1)²)/A ≤ -V²/A + 2Λ(q+1)`   when `V ≤ Λ A`,

so the `q`-sum is `exp(-V²/A)` times `∑_q exp(α q - c q²)` with `α = 2Λ`.  That sum is bounded by
completing the square and comparing with a geometric series — no Gaussian summation needed. -/

/-- **The height sum.**  `∑_{q<N} exp(α q - c q²) ≤ exp(α²/(2c)) (1 - e^{-c/2})⁻¹`.

Completing the square gives `α q - c q² ≤ α²/(2c) - (c/2) q²`, and `q² ≥ q` on `ℕ` turns the
remainder into a geometric series. -/
lemma sum_exp_linear_sub_sq_le {α c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ q ∈ Finset.range N, Real.exp (α * q - c * (q : ℝ) ^ 2)
      ≤ Real.exp (α ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹ := by
  have hlt : Real.exp (-(c / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hnn : (0 : ℝ) ≤ Real.exp (-(c / 2)) := (Real.exp_pos _).le
  have hterm : ∀ q ∈ Finset.range N, Real.exp (α * q - c * (q : ℝ) ^ 2)
      ≤ Real.exp (α ^ 2 / (2 * c)) * Real.exp (-(c / 2)) ^ q := by
    intro q _
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hsq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · norm_num
      · have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        nlinarith
    have hcs : α * q - c * (q : ℝ) ^ 2 ≤ α ^ 2 / (2 * c) - c / 2 * (q : ℝ) := by
      have hstep : α * q - c * (q : ℝ) ^ 2 ≤ α ^ 2 / (2 * c) - c / 2 * (q : ℝ) ^ 2 := by
        rw [← sub_nonneg]
        have hkey : α ^ 2 / (2 * c) - c / 2 * (q : ℝ) ^ 2 - (α * q - c * (q : ℝ) ^ 2)
            = (c * (q : ℝ) - α) ^ 2 / (2 * c) := by
          field_simp
          ring
        rw [hkey]
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ c / 2)]
    have hpow : Real.exp (-(c / 2)) ^ q = Real.exp (-(c / 2) * q) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    linarith
  calc ∑ q ∈ Finset.range N, Real.exp (α * q - c * (q : ℝ) ^ 2)
      ≤ ∑ q ∈ Finset.range N, Real.exp (α ^ 2 / (2 * c)) * Real.exp (-(c / 2)) ^ q :=
        Finset.sum_le_sum hterm
    _ = Real.exp (α ^ 2 / (2 * c)) * ∑ q ∈ Finset.range N, Real.exp (-(c / 2)) ^ q :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (α ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹ :=
        mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hnn hlt N) (Real.exp_pos _).le

/-! ### From the Euler product to the walk

Lemma B.1 is stated for `\log‖F_y‖` at the three abscissas of `RMF.pairAbscissa`; the chaining is
stated for the walk `∑_p localLog`.  On the set where the values are unimodular the two agree, and
that is the only bridge needed. -/

/-- The abscissa `σ + i h`. -/
noncomputable def heightLine (σ h : ℝ) : ℂ := (σ : ℂ) + (h : ℂ) * Complex.I

@[simp] lemma re_heightLine (σ h : ℝ) : (heightLine σ h).re = σ := by
  simp [heightLine]

@[simp] lemma im_heightLine (σ h : ℝ) : (heightLine σ h).im = h := by
  simp [heightLine]

lemma pairAbscissa_zero_eq (σ h₁ h₂ : ℝ) : pairAbscissa σ h₁ h₂ 0 = heightLine σ 0 := by
  simp [pairAbscissa, heightLine]

lemma pairAbscissa_one_eq (σ h₁ h₂ : ℝ) : pairAbscissa σ h₁ h₂ 1 = heightLine σ h₁ := by
  simp [pairAbscissa, heightLine]

lemma pairAbscissa_two_eq (σ h₁ h₂ : ℝ) : pairAbscissa σ h₁ h₂ 2 = heightLine σ h₂ := by
  simp [pairAbscissa, heightLine]

/-- **The logarithm of the Euler product is the walk.**

`\log‖F_y(s)‖ = ∑_{p<y} localLog(p^{-s}, X_p)` at every `ω` whose values are unimodular. -/
lemma log_norm_randomEulerProductIco_eq {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y s ω‖
      = ∑ p ∈ primesIco y₀ y, localLog ((p : ℂ) ^ (-s)) (X p ω) := by
  have hne : ∀ p ∈ primesIco y₀ y, ‖(1 - X p ω * (p : ℂ) ^ (-s))⁻¹‖ ≠ 0 := by
    intro p hp
    have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
      norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    have hpos := norm_one_sub_mul_pos (hω p hp) hw
    have : (1 : ℂ) - X p ω * (p : ℂ) ^ (-s) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hpos
      exact lt_irrefl 0 hpos
    simpa using this
  rw [randomEulerProductIco_compMult_eq hs hω, norm_prod, Real.log_prod hne]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_inv, Real.log_inv, localLog]

/-- **A level at which the chain's residual is small.**

`∃ L, Lip · r/4^L ≤ u` for any `u > 0` — the whole content of "the chain may be cut", and the only
place the Lipschitz constant is used.  It enters through `\log_4` of itself, so a constant of size
`√y \log y` costs `L ≈ e^j/2`, which is harmless: the union bound over the net at level `L` is
paid for by a Gaussian exponent of size `(9/4)^L`. -/
lemma exists_level_le {Lip r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    ∃ L : ℕ, Lip * (r / 4 ^ L) ≤ u := by
  rcases le_or_gt Lip 0 with hL | hL
  · refine ⟨0, ?_⟩
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (0 : ℕ) := by positivity
    nlinarith [div_pos hr h4]
  · obtain ⟨L, hLL⟩ := pow_unbounded_of_one_lt (Lip * r / u) (by norm_num : (1 : ℝ) < 4)
    refine ⟨L, ?_⟩
    have h4 : (0 : ℝ) < (4 : ℝ) ^ L := by positivity
    rw [div_lt_iff₀ hu] at hLL
    rw [mul_div_assoc', div_le_iff₀ h4]
    linarith

/-! ### The deterministic reduction

Everything the union bound needs, at a single `ω`: the excursion above `V` is either already
visible at the base point, or it is carried by one link of the chain, at a level `q` that the
deterministic bound `|S 0| ≤ M` keeps **finite**.  That finiteness is what turns the union bound
over `q` into a `Finset` sum — the constant does not depend on `Q`, because the `q`-sum converges
(`RMF.sum_exp_linear_sub_sq_le`). -/

/-- **The deterministic reduction.**  If `S` rises above `V` somewhere on `[0,r)` and is
`Lip`-Lipschitz with the chain cut at `L`, then either `S 0 > V - 1`, or some level `q ∈ [1, Q]`
has `S 0 ≤ V - q` (and `V - q - 1 < S 0` when `q < Q`) and a link `(ℓ, i)` carrying
`(q/2)(1/4)(3/4)^ℓ`.  The cap `Q` is a parameter: at `Q ≈ 2V` it keeps Lemma B.1's admissibility
`λ₂Δ ≤ Λ`, and the top bracket `S 0 ≤ V - Q` is carried by the increment alone, at `λ₁ = 0`, as
Hamdan's `B_{V-2}` is. -/
lemma exists_level_link_of_exists_gt {S : ℝ → ℝ} {r V Lip : ℝ} {L Q : ℕ}
    (hr : 0 < r) (hQ : 1 ≤ Q) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ u v : ℝ, |S u - S v| ≤ Lip * |u - v|)
    (hcut : Lip * (r / 4 ^ L) ≤ 1 / 2)
    (hex : ∃ h ∈ Set.Ico 0 r, V < S h) :
    V - 1 < S 0 ∨ ∃ q ∈ Finset.Icc 1 Q, ((q < Q → V - q - 1 < S 0) ∧ S 0 ≤ V - q) ∧
      ∃ ℓ ∈ Finset.range L, ∃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
          ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1)))
            - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) := by
  by_cases hbase : V - 1 < S 0
  · exact Or.inl hbase
  refine Or.inr ?_
  replace hbase : S 0 ≤ V - 1 := not_lt.1 hbase
  obtain ⟨h, hh, hSh⟩ := hex
  have hVS : (1 : ℝ) ≤ V - S 0 := by linarith
  have hVS0 : (0 : ℝ) ≤ V - S 0 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = min ⌊V - S 0⌋₊ Q := ⟨_, rfl⟩
  have hfl1 : 1 ≤ ⌊V - S 0⌋₊ := Nat.le_floor (by exact_mod_cast hVS)
  have hq1 : 1 ≤ q := by rw [hqdef]; exact le_min hfl1 hQ
  have hqQ : q ≤ Q := by rw [hqdef]; exact min_le_right _ _
  have hqfl : q ≤ ⌊V - S 0⌋₊ := by rw [hqdef]; exact min_le_left _ _
  have hqle : (q : ℝ) ≤ V - S 0 := by
    refine le_trans ?_ (Nat.floor_le hVS0)
    exact_mod_cast hqfl
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hcut' : Lip * (r / 4 ^ L) ≤ (q : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  have hrise : (q : ℝ) ≤ S h - S 0 := by linarith
  obtain ⟨ℓ, hℓ, i, hi, hlink⟩ :=
    exists_link_ge hr hq0 hLip0 hLip hcut' hh.1 hh.2 hrise
  refine ⟨q, Finset.mem_Icc.2 ⟨hq1, hqQ⟩, ⟨fun hlt => ?_, by linarith⟩, ℓ, hℓ, i, hi, hlink⟩
  have hqeq : q = ⌊V - S 0⌋₊ := by
    rw [hqdef] at hlt ⊢
    omega
  have := Nat.lt_floor_add_one (V - S 0)
  rw [← hqeq] at this
  linarith

/-! ### The base-point terms

For `q` below a fixed threshold the chaining is not used at all: the level bracket
`V - q - 1 < S 0` alone already gives `exp(-V²/A)`, because
`(V-q-1)²/A ≥ V²/A - 2Λ(q+1)` when `V ≤ Λ A`.  That threshold is what the `ℓ`-sum needs
(`RMF.sum_level_le` wants `b ≥ 3`), so the two halves of the argument meet here. -/

/-- **Shifting the Gaussian exponent.**  `V²/A - 2Λu ≤ (V-u)²/A` when `V ≤ Λ A` and `u ≥ 0`.

Every step of the `q`-sum uses this: dropping from `V` to `V - q - 1` in the one-point tail costs
at most `2Λ(q+1)` in the exponent, a *linear* loss, which the chaining's `-c q²` then absorbs. -/
lemma sq_div_sub_lower {A V u Λ : ℝ} (hA : 0 < A) (hu : 0 ≤ u) (hVΛ : V ≤ Λ * A) :
    V ^ 2 / A - 2 * Λ * u ≤ (V - u) ^ 2 / A := by
  rw [← sub_nonneg]
  have he : (V - u) ^ 2 / A - (V ^ 2 / A - 2 * Λ * u)
      = (2 * Λ * u * A - 2 * V * u + u ^ 2) / A := by
    field_simp
    ring
  rw [he]
  refine div_nonneg ?_ hA.le
  nlinarith [mul_le_mul_of_nonneg_left hVΛ hu, sq_nonneg u]

/-- **The base-point terms.**  `P(E) ≤ C exp(-V²/A)` on any event where `\log‖F_y(s)‖ ≥ V - u`,
for `0 ≤ u ≤ u₀`, with `C` independent of `f`, `μ`, `σ`, `V`, `u`, `y₀`, `y` and `E`.  Both signs
of `V - u` are covered: when it is negative the bound is trivial, because `V < u ≤ u₀` forces
`V²/A ≤ Λ V ≤ Λ u₀`. -/
theorem IsSteinhausRMF.exists_measure_base_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ u₀ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) (hu₀ : 0 ≤ u₀) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ V u : ℝ) (s : ℂ) (y₀ y : ℕ) (E : Set Ω), s.re = σ → σ₀ ≤ σ → 0 ≤ V →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        V ≤ Λ * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) → 0 ≤ u → u ≤ u₀ →
        MeasurableSet E → (∀ ω ∈ E, V - u ≤ Real.log ‖randomEulerProductIco f y₀ y s ω‖) →
          μ.real E ≤ C * Real.exp (-(V ^ 2 / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)))) := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    IsSteinhausRMF.exists_measure_ge_le_gaussian (Ω := Ω) (σ₀ := σ₀) (Λ := 2 * Λ) hσ₀
      (by linarith)
  refine ⟨Real.exp (C₀ + 2 * Λ * u₀) + Real.exp (Λ * u₀), by positivity, ?_⟩
  intro f μ hf σ V u s y₀ y E hs hσ hV hA hVΛ hu hu' hE hEV
  haveI := hf.isProbabilityMeasure
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  rw [← hAdef] at hA hVΛ ⊢
  have hexp0 : (0 : ℝ) < Real.exp (-(V ^ 2 / A)) := Real.exp_pos _
  have hkey := sq_div_sub_lower hA hu hVΛ
  rcases le_or_gt 0 (V - u) with hpos | hneg
  · have h2Λ : 2 * (V - u) / A ≤ 2 * Λ := by
      rw [div_le_iff₀ hA]
      nlinarith [hA.le]
    have h := hbound f μ hf σ (V - u) s y₀ y E hpos hs hσ (hAdef ▸ hA) (by rw [← hAdef]; exact h2Λ)
      hE hEV
    rw [← hAdef] at h
    refine le_trans h ?_
    have hstep : Real.exp (C₀ - (V - u) ^ 2 / A)
        ≤ Real.exp (C₀ + 2 * Λ * u₀) * Real.exp (-(V ^ 2 / A)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_le_mul_of_nonneg_left hu' (by linarith : (0 : ℝ) ≤ 2 * Λ)]
    nlinarith [Real.exp_pos (C₀ + 2 * Λ * u₀), Real.exp_pos (Λ * u₀)]
  · have hVu : V < u₀ := by linarith
    have hVA : V ^ 2 / A ≤ Λ * u₀ := by
      rw [div_le_iff₀ hA]
      nlinarith [hVΛ, hV, hA.le]
    have hone : μ.real E ≤ 1 := by
      have h := measureReal_mono (μ := μ) (Set.subset_univ E) (measure_ne_top μ _)
      rwa [probReal_univ] at h
    have hstep : (1 : ℝ) ≤ Real.exp (Λ * u₀) * Real.exp (-(V ^ 2 / A)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      linarith
    nlinarith [Real.exp_pos (C₀ + 2 * Λ * u₀), hexp0]

/-- `∑_{p<y} p^{-2σ}\log p ≥ (\log 2) ∑_{p<y} p^{-2σ}`: every prime has `\log p ≥ \log 2`.

Small, but it is what keeps Lemma B.1's admissibility `λ₂Δ ≤ Λ` satisfied along the whole chain.
The increment threshold at level `q` is `V₂ ≲ q ≲ V`, and `λ₂Δ = V₂/P₁`; with `V ≤ Λ A` this is
`≤ Λ/\log 2`, an absolute bound.  Without it the admissibility would degrade as `A/P₁`, which is
not controlled. -/
lemma log_two_mul_sum_le_sum_mul_log (σ : ℝ) (y₀ y : ℕ) :
    Real.log 2 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
      ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hpow : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg (by linarith) _
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  nlinarith

/-! ### The chaining terms

Lemma B.1 at one link, with `λ₂` chosen from an *upper bound* `D` for the spacing rather than the
spacing itself.  That is deliberate: consecutive links can coincide (`i ≡ 0 \bmod 4`), and there
`|h₁-h₂| = 0` would make the optimal `λ₂` undefined.  Using `D = 3r/4^{ℓ+1}` throughout keeps
`λ₂ = V₂/(D P₁)` well defined and only weakens the bound. -/

/-- **One link of the chain.**  `P(E) ≤ exp(λ₁²A/4 - λ₁V₁ + λ₁V₂/2 - V₂²/(2 D P₁) + C)` for
`0 ≤ λ₁ ≤ Λ`, on any event where the base point is at least `V₁` and the increment across a gap of
size at most `D` is at least `V₂`.  The cross term `λ₁V₂/2` is the price of the joint estimate; it
is absorbed by `V₂²/(2 D P₁)` once `V₂ ≥ 4Λ D P₁`, which is what the threshold on `q` is for. -/
theorem IsSteinhausRMF.exists_measure_link_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (l₁ σ V₁ V₂ D h₁ h₂ : ℝ) (y₀ y : ℕ) (E : Set Ω),
        0 ≤ l₁ → l₁ ≤ Λ → σ₀ ≤ σ → |h₁ - h₂| ≤ D → 0 ≤ V₂ → 0 < D →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) →
        V₂ / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
        MeasurableSet E →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ 0) ω‖) →
        (∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₁) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₂) ω‖) →
          μ.real E ≤ Real.exp (l₁ ^ 2 / 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            - l₁ * V₁ + l₁ * V₂ / 2
            - V₂ ^ 2 / (2 * (D * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p))
            + C) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsSteinhausRMF.exists_measure_le_exp_pair (Ω := Ω) (σ₀ := σ₀) (Λ := Λ) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₁ σ V₁ V₂ D h₁ h₂ y₀ y E hl₁ hl₁Λ hσ hD hV₂ hD0 hP₁ hV₂P hE hE₁ hE₂
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ,
      P = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  rw [← hPdef] at hP₁ hV₂P
  rw [← hAdef, ← hPdef]
  have hB : (0 : ℝ) < D * P := by positivity
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂ : ℝ, l₂ = V₂ / (D * P) := ⟨_, rfl⟩
  have hl₂ : (0 : ℝ) ≤ l₂ := by rw [hl₂def]; positivity
  have hl₂B : l₂ * (D * P) = V₂ := by rw [hl₂def]; field_simp
  have hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ := by
    have h1 : l₂ * |h₁ - h₂| ≤ l₂ * D := mul_le_mul_of_nonneg_left hD hl₂
    have h2 : l₂ * D = V₂ / P := by rw [hl₂def]; field_simp
    linarith [h2 ▸ h1]
  have h := hbound f μ hf l₁ l₂ σ h₁ h₂ V₁ V₂ y₀ y E hl₁ hl₂ hσ hl₁Λ hl₂Λ hE
    (by rw [pairAbscissa_zero_eq σ h₁ h₂]; exact hE₁)
    (by rw [pairAbscissa_one_eq σ h₁ h₂, pairAbscissa_two_eq σ h₁ h₂]; exact hE₂)
  rw [← hAdef, ← hPdef] at h
  refine le_trans h (Real.exp_le_exp.2 ?_)
  have hcross : (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂| * P ≤ (l₁ * l₂ + l₂ ^ 2) / 2 * (D * P) := by
    have hnn : (0 : ℝ) ≤ (l₁ * l₂ + l₂ ^ 2) / 2 := by positivity
    have h1 : |h₁ - h₂| * P ≤ D * P := mul_le_mul_of_nonneg_right hD hP₁.le
    nlinarith
  have hexpand : (l₁ * l₂ + l₂ ^ 2) / 2 * (D * P) = l₁ * V₂ / 2 + V₂ ^ 2 / (2 * (D * P)) := by
    rw [hl₂def]
    field_simp
  have hl₂V : l₂ * V₂ = V₂ ^ 2 / (D * P) := by
    rw [hl₂def]
    field_simp
  have hsplit : V₂ ^ 2 / (D * P) = 2 * (V₂ ^ 2 / (2 * (D * P))) := by
    field_simp
  linarith [hexpand ▸ hcross]

/-! ### The double sum

`∑_q ∑_ℓ` of the chaining terms.  The `ℓ`-sum is `RMF.sum_level_le` and collapses to `8e^{-cq²}`;
the `q`-sum is then `RMF.sum_exp_linear_sub_sq_le` after `RMF.sq_div_sub_lower` turns
`-(V-q-1)²/A` into `-V²/A + 2Λ(q+1)`. -/

/-- **The double sum.**  `∑_{q∈T} ∑_{ℓ<L} 4^{ℓ+1} exp(-W + 2Λ(q+1) - c q² (9/4)^ℓ)` is at most
`8e^{2Λ}·e^{(2Λ)²/(2c)}(1 - e^{-c/2})⁻¹·e^{-W}`, provided every `q ∈ T` has `c q² ≥ 3`.  At
`W = V²/A` and `V ≤ ΛA`, `RMF.sq_div_sub_lower` bounds `-(V-q-1)²/A` by `-W + 2Λ(q+1)`. -/
lemma sum_chaining_le {W Λ c : ℝ} (hc : 0 < c)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 3 ≤ c * (q : ℝ) ^ 2) (L : ℕ) :
    ∑ q ∈ T, ∑ ℓ ∈ Finset.range L,
        (4 : ℝ) ^ (ℓ + 1)
          * Real.exp (-W + 2 * Λ * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ)
      ≤ 8 * Real.exp (2 * Λ)
        * (Real.exp ((2 * Λ) ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹)
        * Real.exp (-W) := by
  have hstep : ∀ q ∈ T, ∑ ℓ ∈ Finset.range L,
      (4 : ℝ) ^ (ℓ + 1)
        * Real.exp (-W + 2 * Λ * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ)
        ≤ 8 * Real.exp (-W) * Real.exp (2 * Λ)
          * Real.exp (2 * Λ * (q : ℝ) - c * (q : ℝ) ^ 2) := by
    intro q hq
    have hfac : ∀ ℓ : ℕ,
        (4 : ℝ) ^ (ℓ + 1)
          * Real.exp (-W + 2 * Λ * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ)
          = Real.exp (-W + 2 * Λ * ((q : ℝ) + 1))
            * ((4 : ℝ) ^ (ℓ + 1) * Real.exp (-(c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ))) := by
      intro ℓ
      rw [show -W + 2 * Λ * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ
          = (-W + 2 * Λ * ((q : ℝ) + 1)) + -(c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) by ring,
        Real.exp_add]
      ring
    calc ∑ ℓ ∈ Finset.range L,
          (4 : ℝ) ^ (ℓ + 1)
            * Real.exp (-W + 2 * Λ * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ)
        = Real.exp (-W + 2 * Λ * ((q : ℝ) + 1)) * ∑ ℓ ∈ Finset.range L,
            ((4 : ℝ) ^ (ℓ + 1) * Real.exp (-(c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ℓ _ => hfac ℓ
      _ ≤ Real.exp (-W + 2 * Λ * ((q : ℝ) + 1)) * (8 * Real.exp (-(c * (q : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left (sum_level_le (hT q hq) L) (Real.exp_pos _).le
      _ ≤ 8 * Real.exp (-W) * Real.exp (2 * Λ)
            * Real.exp (2 * Λ * (q : ℝ) - c * (q : ℝ) ^ 2) := by
          have hL : ∀ a b : ℝ, Real.exp a * (8 * Real.exp b) = 8 * Real.exp (a + b) := by
            intro a b
            rw [Real.exp_add]
            ring
          have hR : ∀ a b d : ℝ,
              8 * Real.exp a * Real.exp b * Real.exp d = 8 * Real.exp (a + b + d) := by
            intro a b d
            rw [Real.exp_add, Real.exp_add]
            ring
          rw [hL, hR]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
          linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T ⊆ Finset.range N := ⟨T.sup id + 1, fun q hq =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hq))⟩
  have hnn : ∀ q ∈ Finset.range N, q ∉ T →
      (0 : ℝ) ≤ 8 * Real.exp (-W) * Real.exp (2 * Λ)
        * Real.exp (2 * Λ * (q : ℝ) - c * (q : ℝ) ^ 2) := by
    intro q _ _
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN hnn) ?_
  rw [← Finset.mul_sum]
  have hgeo := sum_exp_linear_sub_sq_le (α := 2 * Λ) hc N
  have hpos : (0 : ℝ) ≤ 8 * Real.exp (-W) * Real.exp (2 * Λ) := by positivity
  have hle := mul_le_mul_of_nonneg_left hgeo hpos
  refine le_trans hle (le_of_eq ?_)
  ring

/-! ### The union bound

`RMF.exists_level_link_of_exists_gt` in measure.  Only monotonicity and the finite union bound are
used, and both hold for **arbitrary** sets — `μ` is an outer measure — so no measurability of the
supremum event is needed here.  (It is needed downstream, where the event is integrated
against.) -/

/-- **The union bound.**

It stops at the level of `q`, without expanding the inner union over `(ℓ, i)`.  That is not
laziness: for `q` below the threshold the chaining is never used, and the `q`-slice is bounded by
its *bracket* alone — expanding it into `4^{ℓ+1}` terms there would be fatal, since nothing
decays in `ℓ`. -/
lemma measureReal_inter_exists_gt_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {S : ℝ → Ω → ℝ} {G : Set Ω} {r V Lip : ℝ} {L Q : ℕ}
    (hr : 0 < r) (hQ : 1 ≤ Q) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ ω ∈ G, ∀ u v : ℝ, |S u ω - S v ω| ≤ Lip * |u - v|)
    (hcut : Lip * (r / 4 ^ L) ≤ 1 / 2) :
    μ.real (G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω})
      ≤ μ.real (G ∩ {ω | V - 1 < S 0 ω})
        + ∑ q ∈ Finset.Icc 1 Q,
            μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
              (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
                ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
                    ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                      - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})) := by
  have hincl : G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω}
      ⊆ (G ∩ {ω | V - 1 < S 0 ω}) ∪ ⋃ q ∈ Finset.Icc 1 Q,
          ⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
            (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
              ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
                  ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                    - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}) := by
    rintro ω ⟨hωG, hωex⟩
    rcases exists_level_link_of_exists_gt hr hQ hLip0 (hLip ω hωG) hcut hωex with
      hb | ⟨q, hq, hbr, ℓ, hℓ, i, hi, hlink⟩
    · exact Or.inl ⟨hωG, hb⟩
    · exact Or.inr (Set.mem_biUnion hq (Set.mem_biUnion hℓ
        (Set.mem_biUnion hi ⟨⟨hωG, hbr⟩, hlink⟩)))
  calc μ.real (G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω})
      ≤ μ.real ((G ∩ {ω | V - 1 < S 0 ω}) ∪ ⋃ q ∈ Finset.Icc 1 Q,
          ⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
            (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
              ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
                  ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                    - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})) :=
        measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ μ.real (G ∩ {ω | V - 1 < S 0 ω})
        + μ.real (⋃ q ∈ Finset.Icc 1 Q, ⋃ ℓ ∈ Finset.range L,
            ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
              (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
                ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
                    ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                      - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})) :=
        measureReal_union_le _ _
    _ ≤ μ.real (G ∩ {ω | V - 1 < S 0 ω})
        + ∑ q ∈ Finset.Icc 1 Q,
            μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
              (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
                ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
                    ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                      - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})) := by
        gcongr
        exact measureReal_biUnion_finset_le _ _

/-- **A deterministic lower bound for the walk:** `\log‖F_y(s)‖ ≥ -∑_{p<y}\log(1 + p^{-σ})` wherever
the values are unimodular.  It is used only in the top bracket `q = Q`, where nothing bounds `S(σ)`
below, so the Chernoff exponent `λ₁` is `0` there; Lemma B.1 still asks for *some* `V₁` below the
base point, and any deterministic bound will do, since `λ₁V₁ = 0`. -/
lemma le_log_norm_randomEulerProductIco {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    -∑ p ∈ primesIco y₀ y, Real.log (1 + ((p : ℕ) : ℝ) ^ (-s.re))
      ≤ Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y s ω‖ := by
  rw [log_norm_randomEulerProductIco_eq hs hω, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  have hw : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
  have hwlt : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one hpp hs
  have hpos := norm_one_sub_mul_pos (hω p hp) hwlt
  have hup : ‖1 - X p ω * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 + ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
    have h1 : ‖X p ω * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
    have h2 := norm_sub_le (1 : ℂ) (X p ω * ((p : ℕ) : ℂ) ^ (-s))
    rw [norm_one] at h2
    linarith
  rw [localLog, neg_le_neg_iff, ← hw]
  exact Real.log_le_log hpos hup

/-! ### One link, with the exponent in the shape the double sum consumes

Separated from the assembly because it is the only genuinely numeric step: at level `ℓ` the
increment threshold is `V₂ = q(3/4)^ℓ/8` and the gap is at most `D = 3r/4^{ℓ+1}`, so

```
V₂²/(2 D P₁) = q² (9/4)^ℓ / (96 r P₁) ≥ 2c q² (9/4)^ℓ,     c = 1/(192Λ),
```

using `r P₁ ≤ Λ`.  Half of that absorbs the cross term `λ₁V₂/2` once `q ≥ 24Λ²`, and the other
half is what the level sum decays by. -/

/-- `((3/4)^ℓ)² 4^ℓ = (9/4)^ℓ` — the identity behind `θ²K > 1`. -/
lemma sq_chainWeight_mul_pow (ℓ : ℕ) : ((3 / 4 : ℝ) ^ ℓ) ^ 2 * (4 : ℝ) ^ ℓ = (9 / 4 : ℝ) ^ ℓ := by
  rw [← pow_mul, mul_comm ℓ 2, pow_mul, ← mul_pow]
  norm_num

/-- **The increment threshold is large enough**, twice over: `V₂²/(2 D P) ≥ 2 c q² (9/4)^ℓ`. -/
lemma two_mul_le_sq_div_two_mul {r P Λ : ℝ} (hr : 0 < r) (hP : 0 < P) (hΛ : 0 < Λ)
    (hrP : r * P ≤ Λ) (q ℓ : ℕ) :
    2 * (1 / (192 * Λ)) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ
      ≤ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (2 * (3 * r / 4 ^ (ℓ + 1) * P)) := by
  have hp4 : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
  have hw0 : (0 : ℝ) < (3 / 4 : ℝ) ^ ℓ := by positivity
  have hrP0 : (0 : ℝ) < r * P := by positivity
  have hval : ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
      / (2 * (3 * r / 4 ^ (ℓ + 1) * P))
      = (q : ℝ) ^ 2 * (((3 / 4 : ℝ) ^ ℓ) ^ 2 * (4 : ℝ) ^ ℓ) / (96 * (r * P)) := by
    rw [pow_succ]
    field_simp
    ring
  have hkey : 2 * (1 / (192 * Λ)) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ
      = ((q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ) / (96 * Λ) := by
    field_simp
    ring
  have hpow0 : (0 : ℝ) < (9 / 4 : ℝ) ^ ℓ := by positivity
  rw [hval, sq_chainWeight_mul_pow, hkey,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hrP (mul_nonneg hq0 hpow0.le)]

/-- **The increment threshold dominates the gap**: `4Λ D P ≤ V₂` once `q ≥ 24Λ²`.

This is what lets the joint estimate's cross term be absorbed, and it is the *first* reason for
the threshold on `q`; the second is that the level sum needs `b ≥ 3`. -/
lemma four_mul_le_chainWeight {r P Λ : ℝ} (hr : 0 < r) (hP : 0 < P) (hΛ : 0 < Λ)
    (hrP : r * P ≤ Λ) {q : ℕ} (hq : 24 * Λ ^ 2 ≤ (q : ℝ)) (ℓ : ℕ) :
    4 * Λ * (3 * r / 4 ^ (ℓ + 1) * P) ≤ (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) := by
  have hp4 : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
  have h3l : (1 : ℝ) ≤ (3 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  have hlhs : 4 * Λ * (3 * r / 4 ^ (ℓ + 1) * P) = 3 * Λ * (r * P) / 4 ^ ℓ := by
    rw [pow_succ]
    field_simp
  have hrhs : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) = (q : ℝ) * 3 ^ ℓ / (8 * 4 ^ ℓ) := by
    rw [div_pow]
    field_simp
    ring
  rw [hlhs, hrhs, div_le_div_iff₀ hp4 (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hrP (by positivity : (0 : ℝ) ≤ 24 * Λ * 4 ^ ℓ),
    mul_le_mul_of_nonneg_left h3l (by positivity : (0 : ℝ) ≤ (q : ℝ) * 4 ^ ℓ),
    mul_le_mul_of_nonneg_right hq hp4.le, mul_nonneg hΛ.le hp4.le]

/-- **The cross term is absorbed by a quarter of the increment variance**, once `4ΛB ≤ V₂`. -/
lemma cross_le_quarter {l₁ Λ V₂ B : ℝ} (hB : 0 < B) (hV₂ : 0 ≤ V₂)
    (hl₁ : l₁ ≤ 2 * Λ) (hVD : 4 * Λ * B ≤ V₂) :
    l₁ * V₂ / 2 ≤ V₂ ^ 2 / (4 * B) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hl₁ hV₂, mul_le_mul_of_nonneg_right hVD hV₂, hB.le]

/-! ### Lemma B.2

Everything meets here.  The threshold `q₀ = ⌈24Λ² + 24Λ⌉` is where the two halves join: its first
term makes the joint estimate's cross term `λ₁V₂/2` absorbable by half of `V₂²/(2DP₁)`, and its
second gives the level sum its `b ≥ 3`.  Below the threshold the chaining is not used at all and
the bracket's own Gaussian tail suffices; above it, the bracket and the chain are used jointly,
which is exactly what Lemma B.1 is for. -/

set_option maxHeartbeats 1000000 in
-- the assembly: eight lemmas, two nested union bounds and a case split in one declaration
/-- **Hamdan's Lemma B.2.**

`P( ∃h ∈ [0,r) : \log‖F_y(σ+ih)‖ > V ) ≤ C exp(-V²/A)`,  `A = ∑_{p<y}p^{-2σ}`,

for `σ₀ ≤ σ`, `0 ≤ V ≤ Λ A`, `1 ≤ A` and `r P₁ ≤ Λ`, `P₁ = ∑_{p<y}p^{-2σ}\log p`, with `C`
independent of `f`, `μ`, `σ`, `V`, `r`, `y₀` and `y` (given `σ₀ > 1/3` and `Λ ≥ 1`).

At `σ = 1/2`, `y = x_j`, `r = e^{-j}` Mertens gives `A = j + O(1)` and `P₁ ≤ e^j + O(1)`, so the
hypotheses read `V ≤ Cj` and `e^{-j}e^j ≤ Λ`, and the conclusion is his `≪ exp(-V²/j)`.  Both
prime sums are left symbolic, as in Lemma B.1; `Probability/MaximalBarrier.lean` evaluates them at
the block scales. -/
theorem IsSteinhausRMF.exists_measure_exists_gt_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ V r : ℝ) (y₀ y : ℕ), σ₀ ≤ σ → 0 < r → 0 ≤ V →
        1 ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        V ≤ Λ * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
          μ.real {ω | ∃ h ∈ Set.Ico 0 r,
              V < Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
            ≤ C * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (192 * Λ) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  obtain ⟨q₀, hq₀def⟩ : ∃ q₀ : ℕ, q₀ = ⌈24 * Λ ^ 2 + 24 * Λ⌉₊ := ⟨_, rfl⟩
  have hq₀ge : (24 : ℝ) * Λ ^ 2 + 24 * Λ ≤ (q₀ : ℝ) := by rw [hq₀def]; exact Nat.le_ceil _
  obtain ⟨Λ', hΛ'def⟩ : ∃ Λ' : ℝ, Λ' = 3 * Λ + (q₀ : ℝ) + 3 := ⟨_, rfl⟩
  have hΛ'0 : (0 : ℝ) ≤ Λ' := by rw [hΛ'def]; positivity
  obtain ⟨Csum, hCsumdef⟩ : ∃ Csum : ℝ, Csum = 8 * Real.exp (2 * Λ)
      * (Real.exp ((2 * Λ) ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹) := ⟨_, rfl⟩
  have hCsum0 : (0 : ℝ) ≤ Csum := by
    have h1 : Real.exp (-(c / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have h2 : (0 : ℝ) < 1 - Real.exp (-(c / 2)) := by linarith
    rw [hCsumdef]
    positivity
  obtain ⟨Cb, hCb, hbase⟩ := IsSteinhausRMF.exists_measure_base_le (Ω := Ω) (σ₀ := σ₀)
    (Λ := Λ) (u₀ := (q₀ : ℝ) + 1) hσ₀ (by linarith) (by positivity)
  obtain ⟨Cl, hCl, hlink⟩ := IsSteinhausRMF.exists_measure_link_le (Ω := Ω) (σ₀ := σ₀)
    (Λ := Λ') hσ₀ hΛ'0
  refine ⟨(q₀ : ℝ) * Cb + Cb + Real.exp Cl * Csum, ?_, ?_⟩
  · have := Real.exp_pos Cl
    nlinarith [Nat.cast_nonneg (α := ℝ) q₀, hCb, hCsum0]
  intro f μ hf σ V r y₀ y hσ hr hV hA1 hVΛ hrP
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  haveI := hf.isProbabilityMeasure
  have hA : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := by linarith
  have hP : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
    have h := log_two_mul_sum_le_sum_mul_log σ y₀ y
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- the unimodularity set, on which the walk *is* the Euler product's logarithm
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    have hrw : {ω : Ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1}
        = ⋂ p ∈ primesIco y₀ y, {ω : Ω | ‖X p ω‖ ≤ 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hGdef, hrw]
    exact (primesIco y₀ y).measurableSet_biInter fun p hp =>
      measurableSet_le ((hX.measurable p (prime_of_mem_primesIco hp)).norm)
        measurable_const
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → Ω → ℝ, S = fun t ω =>
      ∑ p ∈ primesIco y₀ y, localLog ((p : ℂ) ^ (-(heightLine σ t))) (X p ω) := ⟨_, rfl⟩
  have hSmeas : ∀ t : ℝ, Measurable (S t) := by
    intro t
    simp only [hSdef]
    exact Finset.measurable_sum _ fun p hp =>
      (measurable_localLog _).comp (hX.measurable p (prime_of_mem_primesIco hp))
  have hSeq : ∀ (t : ℝ) (ω : Ω), ω ∈ G →
      S t ω = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
        (heightLine σ t) ω‖ := by
    intro t ω hω
    rw [hGdef] at hω
    simp only [hSdef]
    exact (log_norm_randomEulerProductIco_eq (by rw [re_heightLine]; exact hσ0) hω).symm
  -- the Lipschitz bound, and the level at which the chain is cut
  obtain ⟨Lip, hLipdef⟩ : ∃ Lip : ℝ, Lip = (1 - (2 : ℝ) ^ (-σ))⁻¹
      * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) * Real.log p := ⟨_, rfl⟩
  have hθ : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hLip0 : (0 : ℝ) ≤ Lip := by
    have h1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by linarith
    have h2 : (0 : ℝ) ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) * Real.log p := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpp := prime_of_mem_primesIco hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
      have hl := Real.log_nonneg hp1
      have hr0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
      positivity
    rw [hLipdef]
    positivity
  have hLip : ∀ ω ∈ G, ∀ u v : ℝ, |S u ω - S v ω| ≤ Lip * |u - v| := by
    intro ω hω u v
    rw [hGdef] at hω
    have h := abs_sum_localLog_sub_le (B := primesIco y₀ y)
      (fun p hp => prime_of_mem_primesIco hp) hω
      (re_heightLine σ u) (re_heightLine σ v) hσ0
    rw [im_heightLine, im_heightLine] at h
    simp only [hSdef]
    rw [hLipdef]
    exact h
  obtain ⟨L, hL⟩ := exists_level_le (Lip := Lip) hr (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌈V⌉₊ + q₀ + 2 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; omega
  have hq₀Q : q₀ < Q := by rw [hQdef]; omega
  have hQge : V + (q₀ : ℝ) + 2 ≤ (Q : ℝ) := by
    rw [hQdef]
    push_cast
    have := Nat.le_ceil V
    linarith
  -- the target, moved onto the unimodularity set and expressed through the walk
  have htarget : μ.real {ω | ∃ h ∈ Set.Ico 0 r,
      V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
        (heightLine σ h) ω‖} = μ.real (G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω}) := by
    have hset : G ∩ {ω | ∃ h ∈ Set.Ico 0 r,
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖} = G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω} := by
      ext ω
      constructor
      · rintro ⟨hωG, h, hh, hlt⟩
        exact ⟨hωG, h, hh, by rw [hSeq h ω hωG]; exact hlt⟩
      · rintro ⟨hωG, h, hh, hlt⟩
        exact ⟨hωG, h, hh, by rw [← hSeq h ω hωG]; exact hlt⟩
    unfold MeasureTheory.Measure.real
    rw [measure_eq_measure_inter_of_compl_null hGnull, hset]
  rw [htarget]
  refine le_trans (measureReal_inter_exists_gt_le (μ := μ) (S := S) (G := G) (V := V)
    hr hQ1 hLip0 hLip hL) ?_
  -- the base point of the whole event
  have hVA : V ^ 2 / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) ≤ Λ * V := by
    rw [div_le_iff₀ hA]
    nlinarith
  have hbase0 : μ.real (G ∩ {ω | V - 1 < S 0 ω})
      ≤ Cb * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
    refine hbase _ μ hf σ V 1 (heightLine σ 0) y₀ y _ (re_heightLine σ 0) hσ hV hA hVΛ
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) q₀])
      (hGmeas.inter (measurableSet_lt measurable_const (hSmeas 0))) ?_
    rintro ω ⟨hωG, hlt⟩
    simp only [Set.mem_setOf_eq] at hlt
    rw [← hSeq 0 ω hωG]
    linarith
  -- the bracket at level `q` is measurable, and sits inside the unimodularity set
  have hbrmeas : ∀ q : ℕ, MeasurableSet
      {ω : Ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q} := by
    intro q
    by_cases hqQ : q < Q
    · have hrw : {ω : Ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          = {ω : Ω | V - q - 1 < S 0 ω} ∩ {ω : Ω | S 0 ω ≤ V - q} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        exact ⟨fun h => ⟨h.1 hqQ, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩
      rw [hrw]
      exact (measurableSet_lt measurable_const (hSmeas 0)).inter
        (measurableSet_le (hSmeas 0) measurable_const)
    · have hrw : {ω : Ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          = {ω : Ω | S 0 ω ≤ V - q} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hqQ, h⟩⟩
      rw [hrw]
      exact measurableSet_le (hSmeas 0) measurable_const
  -- the slices below the threshold: the bracket alone
  have hsmall : ∀ q ∈ Finset.Ioc 0 q₀,
      μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Cb * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
    intro q hq
    have hq₀ : q ≤ q₀ := (Finset.mem_Ioc.1 hq).2
    have hqQ : q < Q := lt_of_le_of_lt hq₀ hq₀Q
    have hsub : (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
        ⊆ G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q} := by
      refine Set.iUnion₂_subset fun ℓ _ => Set.iUnion₂_subset fun i _ => ?_
      exact Set.inter_subset_left
    refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
    refine hbase _ μ hf σ V ((q : ℝ) + 1) (heightLine σ 0) y₀ y _ (re_heightLine σ 0) hσ hV hA
      hVΛ (by positivity) ?_ (hGmeas.inter (hbrmeas q)) ?_
    · have hcast : (q : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast hq₀
      linarith
    · rintro ω ⟨hωG, hbr, -⟩
      rw [← hSeq 0 ω hωG]
      have := hbr hqQ
      linarith
  -- abbreviations for the two prime sums
  obtain ⟨AA, hAAdef⟩ : ∃ AA : ℝ, AA = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨PP, hPPdef⟩ : ∃ PP : ℝ,
      PP = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  have hPlow : Real.log 2 * AA ≤ PP := by
    rw [hAAdef, hPPdef]
    exact log_two_mul_sum_le_sum_mul_log σ y₀ y
  rw [← hAAdef] at hA hA1 hVΛ hbase0 hsmall ⊢
  rw [← hPPdef] at hP hrP
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hVA : V ^ 2 / AA ≤ Λ * V := by
    rw [div_le_iff₀ hA]
    nlinarith
  have hq₀R : (0 : ℝ) ≤ (q₀ : ℝ) := Nat.cast_nonneg q₀
  have hQupper : (Q : ℝ) ≤ V + (q₀ : ℝ) + 3 := by
    rw [hQdef]
    push_cast
    have := Nat.ceil_lt_add_one hV
    linarith
  -- one link of the chain, above the threshold
  have hterm : ∀ q ℓ i : ℕ, q₀ < q → q ≤ Q → ∀ E : Set Ω, MeasurableSet E → E ⊆ G →
      (∀ ω ∈ E, q < Q → V - q - 1 < S 0 ω) →
      (∀ ω ∈ E, (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
        ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
          - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω) →
      μ.real E ≤ Real.exp Cl
        * Real.exp (-(V ^ 2 / AA) + 2 * Λ * ((q : ℝ) + 1)
          - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro q ℓ i hq₀q hqQ' E hEmeas hEG hE1 hE2
    have hqR : (24 : ℝ) * Λ ^ 2 + 24 * Λ ≤ (q : ℝ) := by
      have h1 : (q₀ : ℝ) < (q : ℝ) := by exact_mod_cast hq₀q
      linarith
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ'
    have hp4 : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
    have hgap : |(i : ℝ) * (r / 4 ^ (ℓ + 1)) - ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))|
        ≤ 3 * r / 4 ^ (ℓ + 1) := by
      have hdm : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
      have hcast : (i : ℝ) - ((4 * (i / 4) : ℕ) : ℝ) = ((i % 4 : ℕ) : ℝ) := by
        have h := congrArg (fun n : ℕ => (n : ℝ)) hdm
        push_cast at h ⊢
        linarith
      have hmod3 : ((i % 4 : ℕ) : ℝ) ≤ 3 := by
        have h : i % 4 ≤ 3 := by omega
        exact_mod_cast h
      have hr4 : (0 : ℝ) < r / 4 ^ (ℓ + 1) := by positivity
      rw [← sub_mul, hcast, abs_of_nonneg (by positivity),
        show 3 * r / 4 ^ (ℓ + 1) = 3 * (r / 4 ^ (ℓ + 1)) by ring]
      exact mul_le_mul_of_nonneg_right hmod3 hr4.le
    have hD0 : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) := by positivity
    have hBpos : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) * PP := by positivity
    have hw1 : ((3 : ℝ) / 4) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hV2ge : (0 : ℝ) ≤ (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) := by positivity
    have hV2small : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) ≤ (q : ℝ) / 8 := by
      linarith [mul_le_mul_of_nonneg_left hw1 hq0R]
    have hV2P : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) / PP ≤ Λ' := by
      rw [div_le_iff₀ hP, hΛ'def]
      have h2 : V + (q₀ : ℝ) + 3 ≤ (Λ + (q₀ : ℝ) + 3) * AA := by
        have hz := mul_le_mul_of_nonneg_left hA1 (by linarith : (0 : ℝ) ≤ (q₀ : ℝ) + 3)
        linarith only [hz, hVΛ]
      have h3 : (3 * Λ + (q₀ : ℝ) + 3) * (Real.log 2 * AA)
          ≤ (3 * Λ + (q₀ : ℝ) + 3) * PP :=
        mul_le_mul_of_nonneg_left hPlow (by linarith)
      have hscal : (Λ + (q₀ : ℝ) + 3) / 8 ≤ (3 * Λ + (q₀ : ℝ) + 3) * Real.log 2 := by
        have hz := mul_le_mul_of_nonneg_left hlog2.le
          (show (0 : ℝ) ≤ 3 * Λ + (q₀ : ℝ) + 3 by linarith)
        linarith only [hz, hq₀R, hΛ0.le]
      have h4 := mul_le_mul_of_nonneg_right hscal hA.le
      linarith only [hV2small, hqQR, hQupper, h2, h3, h4]
    have hnum := two_mul_le_sq_div_two_mul hr hP hΛ0 hrP q ℓ
    rw [← hcdef] at hnum
    have hhalves : ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (2 * (3 * r / 4 ^ (ℓ + 1) * PP))
        = 2 * (((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
          / (4 * (3 * r / 4 ^ (ℓ + 1) * PP))) := by
      field_simp
      ring
    have hquarter : c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ
        ≤ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
          / (4 * (3 * r / 4 ^ (ℓ + 1) * PP)) := by linarith
    rcases le_or_gt 0 (V - (q : ℝ) - 1) with hpos | hneg
    · have hqQ : q < Q := by
        have h1 : (q : ℝ) < (Q : ℝ) := by linarith
        exact_mod_cast h1
      have hl1 : (0 : ℝ) ≤ 2 * (V - (q : ℝ) - 1) / AA := by positivity
      have hl1two : 2 * (V - (q : ℝ) - 1) / AA ≤ 2 * Λ := by
        rw [div_le_iff₀ hA]
        linarith only [hVΛ, hq0R]
      have hl1Λ : 2 * (V - (q : ℝ) - 1) / AA ≤ Λ' := by
        rw [hΛ'def]
        linarith
      have hVD := four_mul_le_chainWeight hr hP hΛ0 hrP (by linarith : 24 * Λ ^ 2 ≤ (q : ℝ)) ℓ
      have hcross := cross_le_quarter hBpos hV2ge hl1two hVD
      have hshift := sq_div_sub_lower (A := AA) (V := V) (u := (q : ℝ) + 1) (Λ := Λ)
        hA (by positivity) hVΛ
      have hsq : (2 * (V - (q : ℝ) - 1) / AA) ^ 2 / 4 * AA
          - 2 * (V - (q : ℝ) - 1) / AA * (V - (q : ℝ) - 1)
          = -((V - ((q : ℝ) + 1)) ^ 2 / AA) := by
        field_simp
        ring
      have h := hlink _ μ hf (2 * (V - (q : ℝ) - 1) / AA) σ (V - (q : ℝ) - 1)
        ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) (3 * r / 4 ^ (ℓ + 1))
        ((i : ℝ) * (r / 4 ^ (ℓ + 1))) (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) y₀ y E
        hl1 hl1Λ hσ hgap hV2ge hD0 (hPPdef ▸ hP) (hPPdef ▸ hV2P) hEmeas
        (fun ω hω => by
          rw [← hSeq 0 ω (hEG hω)]
          exact le_of_lt (hE1 ω hω hqQ))
        (fun ω hω => by
          rw [← hSeq _ ω (hEG hω), ← hSeq _ ω (hEG hω)]
          exact hE2 ω hω)
      rw [← hAAdef, ← hPPdef] at h
      refine le_trans h ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith only [hsq, hshift, hcross, hquarter, hhalves]
    · obtain ⟨V₁, hV₁def⟩ : ∃ V₁ : ℝ, V₁ = -∑ p ∈ primesIco y₀ y,
          Real.log (1 + ((p : ℕ) : ℝ) ^ (-(heightLine σ 0).re)) := ⟨_, rfl⟩
      have hE1' : ∀ ω ∈ E, V₁
            ≤ Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
              (heightLine σ 0) ω‖ := by
        intro ω hω
        have hωG : ω ∈ G := hEG hω
        rw [hGdef] at hωG
        rw [hV₁def]
        exact le_log_norm_randomEulerProductIco (by rw [re_heightLine]; exact hσ0) hωG
      have hΛq : (0 : ℝ) ≤ Λ * ((q : ℝ) + 1) := by positivity
      have hΛV : Λ * V ≤ Λ * ((q : ℝ) + 1) := by
        have hz := mul_pos hΛ0 (show (0 : ℝ) < (q : ℝ) + 1 - V by linarith only [hneg])
        linarith only [hz]
      have hcq : (0 : ℝ) ≤ c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ :=
        mul_nonneg (mul_nonneg hc.le (sq_nonneg _))
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4) ℓ)
      have h := hlink _ μ hf 0 σ V₁
        ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) (3 * r / 4 ^ (ℓ + 1))
        ((i : ℝ) * (r / 4 ^ (ℓ + 1))) (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) y₀ y E
        le_rfl hΛ'0 hσ hgap hV2ge hD0 (hPPdef ▸ hP) (hPPdef ▸ hV2P) hEmeas hE1'
        (fun ω hω => by
          rw [← hSeq _ ω (hEG hω), ← hSeq _ ω (hEG hω)]
          exact hE2 ω hω)
      rw [← hAAdef, ← hPPdef] at h
      refine le_trans h ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith only [hhalves, hquarter, hVA, hΛV, hΛq, hcq]
  -- the slices above the threshold
  have hbig : ∀ q ∈ Finset.Ioc q₀ Q,
      μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Real.exp Cl * ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1)
          * Real.exp (-(V ^ 2 / AA) + 2 * Λ * ((q : ℝ) + 1)
            - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro q hq
    have hq₀q : q₀ < q := (Finset.mem_Ioc.1 hq).1
    have hqQ' : q ≤ Q := (Finset.mem_Ioc.1 hq).2
    rw [Finset.mul_sum]
    refine le_trans (measureReal_biUnion_finset_le _ _) (Finset.sum_le_sum fun ℓ _ => ?_)
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hb : ∀ i ∈ Finset.range (4 ^ (ℓ + 1)),
        μ.real (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})
        ≤ Real.exp Cl * Real.exp (-(V ^ 2 / AA) + 2 * Λ * ((q : ℝ) + 1)
            - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
      intro i _
      refine hterm q ℓ i hq₀q hqQ' _
        ((hGmeas.inter (hbrmeas q)).inter
          (measurableSet_le measurable_const ((hSmeas _).sub (hSmeas _))))
        (fun ω hω => hω.1.1) (fun ω hω hlt => hω.1.2.1 hlt) (fun ω hω => hω.2)
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)
  -- the two halves of the `q`-sum
  have hIcc : (Finset.Icc 1 Q : Finset ℕ) = Finset.Ioc 0 Q := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le q₀) hq₀Q.le]
  have hsum1 := Finset.sum_le_sum hsmall
  rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at hsum1
  have hsum2 := Finset.sum_le_sum hbig
  rw [← Finset.mul_sum] at hsum2
  have hT : ∀ q ∈ Finset.Ioc q₀ Q, 3 ≤ c * (q : ℝ) ^ 2 := by
    intro q hq
    have hq₀q : q₀ < q := (Finset.mem_Ioc.1 hq).1
    have h1 : (q₀ : ℝ) < (q : ℝ) := by exact_mod_cast hq₀q
    have hqR : (24 : ℝ) * Λ ≤ (q : ℝ) := by
      nlinarith only [hq₀ge, h1, hΛ0.le, sq_nonneg Λ]
    have hq2 : 576 * Λ ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith only [hqR, hΛ0.le]
    rw [hcdef, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith only [hq2, hΛ, hΛ0.le]
  have hchain := sum_chaining_le (W := V ^ 2 / AA) (Λ := Λ) (c := c) hc
    (Finset.Ioc q₀ Q) hT L
  rw [← hCsumdef] at hchain
  have hexpCl : (0 : ℝ) < Real.exp Cl := Real.exp_pos Cl
  have hfin := mul_le_mul_of_nonneg_left hchain hexpCl.le
  nlinarith only [hbase0, hsum1, hsum2, hfin]

/-! ### Shifting the base height

Lemma B.2 lives on `[0, r)`; Lemma 2.3 needs it on each of the `e^j` intervals `[h₀, h₀+r)` that
partition `[0,1]`.  Hamdan gets that from stationarity of the law in `h`.  Stationarity is a
statement about a measure-preserving map of the sample space, and there is none here.  What there
*is* is a rotation of the **family**: with `X'_p = p^{-ih₀}X_p`,

```
X'_p · p^{-(σ+iu)}  =  X_p · p^{-(σ+i(h₀+u))},
```

so the two events coincide **pointwise on `Ω`**, and `X'` is Steinhaus by
`RMF.IsSteinhausPrimeValues.mul_unimodular`.  No pushforward, no joint law, no measure-preserving
map. -/

/-- Rotating by `p^{-ih₀}` has unit modulus. -/
lemma norm_cpow_neg_mul_I {p : ℕ} (hp : 0 < p) (h₀ : ℝ) :
    ‖(p : ℂ) ^ (-((h₀ : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp

/-- `σ + i(h₀+u) = (σ + iu) + ih₀`. -/
lemma heightLine_add (σ h₀ u : ℝ) :
    heightLine σ (h₀ + u) = heightLine σ u + (h₀ : ℂ) * Complex.I := by
  simp only [heightLine]
  push_cast
  ring

/-- **A rotation of the values is a shift of the height**, prime by prime. -/
lemma localLog_cpow_neg_mul {p : ℕ} (hp : 0 < p) (h₀ : ℝ) (s z : ℂ) :
    localLog ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * z)
      = localLog ((p : ℂ) ^ (-(s + (h₀ : ℂ) * Complex.I))) z := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  have hsplit : (p : ℂ) ^ (-(s + (h₀ : ℂ) * Complex.I))
      = (p : ℂ) ^ (-s) * (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) := by
    rw [neg_add, Complex.cpow_add _ _ hp0]
  rw [localLog, localLog, hsplit,
    show ((p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * z) * (p : ℂ) ^ (-s)
      = z * ((p : ℂ) ^ (-s) * (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I))) from by ring]

/-- **The rotated family at height `u` is the original at height `h₀+u`.** -/
lemma log_norm_randomEulerProductIco_rotate {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {σ h₀ u : ℝ}
    (hσ : 0 < σ) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
        (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * X p ω) y₀ y (heightLine σ u) ω‖
      = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ (h₀ + u)) ω‖ := by
  have hω' : ∀ p ∈ primesIco y₀ y,
      ‖(p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * X p ω‖ ≤ 1 := by
    intro p hp
    rw [norm_mul, norm_cpow_neg_mul_I (prime_of_mem_primesIco hp).pos, one_mul]
    exact hω p hp
  rw [log_norm_randomEulerProductIco_eq (by rw [re_heightLine]; exact hσ) hω',
    log_norm_randomEulerProductIco_eq (by rw [re_heightLine]; exact hσ) hω, heightLine_add]
  exact Finset.sum_congr rfl fun p hp =>
    localLog_cpow_neg_mul (prime_of_mem_primesIco hp).pos h₀ _ _

/-- **Lemma B.2 on an arbitrary interval.**

The same bound as `RMF.IsSteinhausRMF.exists_measure_exists_gt_le`, with `[0,r)` replaced by
`[h₀, h₀+r)`; the case `h₀ = 0` is that theorem.  Nothing about the estimate changes -- Lemma B.1
sees the heights only through their differences -- and the proof is the rotation above. -/
theorem IsSteinhausRMF.exists_measure_exists_gt_le_shift {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ V r h₀ : ℝ) (y₀ y : ℕ), σ₀ ≤ σ → 0 < r → 0 ≤ V →
        1 ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        V ≤ Λ * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
              V < Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
            ≤ C * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  obtain ⟨C, hC, H⟩ := IsSteinhausRMF.exists_measure_exists_gt_le (Ω := Ω) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf σ V r h₀ y₀ y hσ hr hV hA1 hVΛ hrP
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hX' := hX.mul_unimodular (c := fun p : ℕ => (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)))
    (fun p hp => norm_cpow_neg_mul_I hp h₀)
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hset : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖}
      = G ∩ {ω | ∃ u ∈ Set.Ico (0 : ℝ) r,
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
          (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * X p ω) y₀ y (heightLine σ u) ω‖} := by
    ext ω
    constructor
    · rintro ⟨hωG, h, hh, hlt⟩
      have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
      refine ⟨hωG, h - h₀, ?_, ?_⟩
      · simp only [Set.mem_Ico] at hh ⊢
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      · rw [log_norm_randomEulerProductIco_rotate hσ0 hωu, show h₀ + (h - h₀) = h from by ring]
        exact hlt
    · rintro ⟨hωG, u, hu, hlt⟩
      have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
      refine ⟨hωG, h₀ + u, ?_, ?_⟩
      · simp only [Set.mem_Ico] at hu ⊢
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · rw [← log_norm_randomEulerProductIco_rotate hσ0 hωu]
        exact hlt
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖}
      = μ.real {ω | ∃ u ∈ Set.Ico (0 : ℝ) r,
          V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * X p ω) y₀ y (heightLine σ u) ω‖} := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _, hset,
          ← measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ C * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) :=
        H _ μ hX'.isSteinhausRMF σ V r y₀ y hσ hr hV hA1 hVΛ hrP

/-! ### The lower tail, by reflection

Lemma B.2 is an upper tail, and Hamdan's Lemma 2.3 needs the lower one too (his Remark B.3).
Instead of carrying a sign through Lemma B.1 and B.2's assembly, reflect the values: with
`w_p = X_p p^{-s}` and `(1-w)(1+w) = 1-w²`,

```
S[X](s) + S[-X](s)  =  -∑_{p<y} \log‖1 - w_p²‖  =:  T(s),
```

and `T` is bounded **deterministically**, by `4∑_{p<y}p^{-2σ}`.  So the lower tail of the maximum is
the upper tail for the reflected family, which is Steinhaus as the rotated one is.  The loss
`4∑p^{-2σ} ≈ 4j` is affordable at the lower barrier, level `20j - A ≥ 16j`: `(16j-4j)²/j = 144j`
against `2A ≤ 8j` plus the entropy `e^j`.  At the upper barrier `(A+j)²/j = 2A+j` is tight, so the
upper tail must be the chaining itself. -/

/-- `p^{-2σ} ≤ 3/4` at every prime, for `σ ≥ 1/3`: the room the reflection bound needs. -/
lemma rpow_prime_neg_two_mul_le {σ : ℝ} (hσ : 1 / 3 ≤ σ) {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) ^ (-2 * σ) ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ (-2 * σ) ≤ (2 : ℝ) ^ (-2 * σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h2 : (2 : ℝ) ^ (-2 * σ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [hsq, hpos]
  linarith

/-- **The reflected local variable.**  `localLog w z + localLog w (-z) = -\log‖1 - (zw)²‖`. -/
lemma localLog_add_localLog_neg {w z : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    localLog w z + localLog w ((-1 : ℂ) * z) = -Real.log ‖1 - (z * w) ^ 2‖ := by
  have hz' : ‖(-1 : ℂ) * z‖ ≤ 1 := by rwa [norm_mul, norm_neg, norm_one, one_mul]
  have h1 := norm_one_sub_mul_pos hz hw
  have h2 := norm_one_sub_mul_pos hz' hw
  have hprod : (1 - z * w) * (1 - ((-1 : ℂ) * z) * w) = 1 - (z * w) ^ 2 := by ring
  rw [localLog, localLog, ← hprod, norm_mul, Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
  ring

/-- `|\log‖1-v‖| ≤ ‖v‖/(1-‖v‖)` for `‖v‖ < 1`.

Both sides of `1-‖v‖ ≤ ‖1-v‖ ≤ 1+‖v‖` are needed, and `\log(1+u) ≤ -\log(1-u)` because
`(1+u)(1-u) ≤ 1`; the resulting `-\log(1-u)` is then `RMF.log_inv_one_sub_le`. -/
lemma abs_log_norm_one_sub_le {v : ℂ} (hv : ‖v‖ < 1) :
    |Real.log ‖1 - v‖| ≤ ‖v‖ / (1 - ‖v‖) := by
  have hu0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have h1 : (0 : ℝ) < 1 - ‖v‖ := by linarith
  have hlow : 1 - ‖v‖ ≤ ‖1 - v‖ := by
    have h := norm_sub_norm_le (1 : ℂ) v
    simpa using h
  have hup : ‖1 - v‖ ≤ 1 + ‖v‖ := by
    have h := norm_sub_le (1 : ℂ) v
    simpa using h
  have hpos : (0 : ℝ) < ‖1 - v‖ := lt_of_lt_of_le h1 hlow
  have hA : Real.log (1 - ‖v‖) ≤ Real.log ‖1 - v‖ := Real.log_le_log h1 hlow
  have hB : Real.log ‖1 - v‖ ≤ Real.log (1 + ‖v‖) := Real.log_le_log hpos hup
  have hC : Real.log (1 + ‖v‖) ≤ -Real.log (1 - ‖v‖) := by
    have h2 : (1 + ‖v‖) * (1 - ‖v‖) ≤ 1 := by nlinarith
    have h3 := Real.log_le_log (by positivity : (0 : ℝ) < (1 + ‖v‖) * (1 - ‖v‖)) h2
    rw [Real.log_mul (by positivity) (ne_of_gt h1), Real.log_one] at h3
    linarith
  have hD : -Real.log (1 - ‖v‖) ≤ ‖v‖ / (1 - ‖v‖) := by
    have h := log_inv_one_sub_le (θ := ‖v‖) hv
    rw [Real.log_inv] at h
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The walk at the reflected family dominates the walk's negative**, up to `4∑_{p<y}p^{-2σ}`. -/
lemma neg_log_norm_randomEulerProductIco_le {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 1 / 3 ≤ s.re) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y s ω‖
      ≤ Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y s ω‖
          + 4 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * s.re) := by
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hω' : ∀ p ∈ primesIco y₀ y, ‖(-1 : ℂ) * X p ω‖ ≤ 1 := by
    intro p hp
    rw [norm_mul, norm_neg, norm_one, one_mul]
    exact hω p hp
  rw [log_norm_randomEulerProductIco_eq hs0 hω, log_norm_randomEulerProductIco_eq hs0 hω']
  have hterm : ∀ p ∈ primesIco y₀ y,
      -localLog ((p : ℂ) ^ (-s)) (X p ω)
        ≤ localLog ((p : ℂ) ^ (-s)) ((-1 : ℂ) * X p ω) + 4 * (p : ℝ) ^ (-2 * s.re) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
    have hwlt : ‖(p : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one hpp hs0
    have hkey := localLog_add_localLog_neg (hω p hp) hwlt
    have hsq : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
    have hnv : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ ≤ (p : ℝ) ^ (-2 * s.re) := by
      rw [norm_pow, norm_mul, hw, ← hsq]
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
      have ha : ‖X p ω‖ ≤ 1 := hω p hp
      have ha0 : (0 : ℝ) ≤ ‖X p ω‖ := norm_nonneg _
      calc (‖X p ω‖ * (p : ℝ) ^ (-s.re)) ^ 2
          = ‖X p ω‖ ^ 2 * ((p : ℝ) ^ (-s.re)) ^ 2 := by ring
        _ ≤ 1 * ((p : ℝ) ^ (-s.re)) ^ 2 :=
            mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = ((p : ℝ) ^ (-s.re)) ^ 2 := one_mul _
    have h34 : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ ≤ 3 / 4 :=
      le_trans hnv (rpow_prime_neg_two_mul_le (by linarith) hpp.two_le)
    have hvlt : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ < 1 := by linarith
    have habs := abs_log_norm_one_sub_le hvlt
    have hfrac : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ / (1 - ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖)
        ≤ 4 * (p : ℝ) ^ (-2 * s.re) := by
      have hpos : (0 : ℝ) < 1 - ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ := by linarith
      rw [div_le_iff₀ hpos]
      nlinarith [norm_nonneg ((X p ω * (p : ℂ) ^ (-s)) ^ 2), hnv]
    have hle := (abs_le.1 habs).2
    linarith [hkey]
  calc -∑ p ∈ primesIco y₀ y, localLog ((p : ℂ) ^ (-s)) (X p ω)
      = ∑ p ∈ primesIco y₀ y, -localLog ((p : ℂ) ^ (-s)) (X p ω) := by
        rw [Finset.sum_neg_distrib]
    _ ≤ ∑ p ∈ primesIco y₀ y, (localLog ((p : ℂ) ^ (-s)) ((-1 : ℂ) * X p ω)
          + 4 * (p : ℝ) ^ (-2 * s.re)) := Finset.sum_le_sum hterm
    _ = ∑ p ∈ primesIco y₀ y, localLog ((p : ℂ) ^ (-s)) ((-1 : ℂ) * X p ω)
          + 4 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * s.re) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Lemma B.2 below**: the maximum of `-\log‖F_y‖` over an interval has the same Gaussian tail.

The threshold carries the deterministic loss `4∑_{p<y}p^{-2σ}` of the reflection.  That loss is
harmless in Lemma 2.3, where the lower barrier sits at `-16j` and the prime sum is `j + O(1)`. -/
theorem IsSteinhausRMF.exists_measure_exists_lt_le {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ W r h₀ : ℝ) (y₀ y : ℕ), σ₀ ≤ σ → 0 < r → 0 ≤ W →
        1 ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        W ≤ Λ * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
              W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
                < -Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
            ≤ C * Real.exp (-(W ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  obtain ⟨C, hC, H⟩ := IsSteinhausRMF.exists_measure_exists_gt_le_shift (Ω := Ω) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf σ W r h₀ y₀ y hσ hr hW hA1 hWΛ hrP
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hσ13 : (1 : ℝ) / 3 ≤ σ := by linarith
  have hX' := hX.mul_unimodular (c := fun _ : ℕ => (-1 : ℂ))
    (fun _ _ => by rw [norm_neg, norm_one])
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hsub : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      ⊆ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} := by
    rintro ω ⟨hωG, h, hh, hlt⟩
    have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
    have hre : (heightLine σ h).re = σ := re_heightLine σ h
    have hrefl := neg_log_norm_randomEulerProductIco_le (X := X) (y := y)
      (s := heightLine σ h) (by rw [hre]; exact hσ13) hωu
    rw [hre] at hrefl
    exact ⟨h, hh, by linarith⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      = μ.real (G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            < -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
              (heightLine σ h) ω‖}) := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ C * Real.exp (-(W ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) :=
        H _ μ hX'.isSteinhausRMF σ W r h₀ y₀ y hσ hr hW hA1 hWΛ hrP

end RMF
