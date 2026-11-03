/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BallotReversal
import RMF.Probability.BallotLower

/-!
# The slab local ballot with summed variances: the ingredients

For a centred Gaussian walk below a flat ceiling `y ≥ 0`, the probability of surviving `M` steps
and ending in a slab below `y` is bounded at the sharp order `M^{-3/2}`, with the variances summed
over the three parts of the path instead of bounded below by one `v₋`
(`RMF.IsGaussianWalk.measureReal_survive_slab_le_sqrt`, in `RMF/UniformLower/HP2Prefix.lean`).
This file holds the ingredients:

* `RMF.IsGaussianWalk.measureReal_survival_le_sqrt_of_lt`: the sharp survival
  `RMF.IsGaussianWalk.measureReal_survival_le_sqrt` with its hypotheses on `v_j` and `c` for
  `j < n` only, so that a walk padded past its horizon keeps `c ≥ √(πv₊/2)` of its own steps;
* `RMF.sum_range_revIdx`, `RMF.revIdx_lt`: the reversed last block and its variances;
* `RMF.sqrt_slab_eq`: the product of the three factors, `2/(π√(2πS₁S₂S₃))`;
* `RMF.cast_choose_slab`: the binomial coefficients of the sums over slabs.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*}

/-- The reversed last block's variances are those of `[M - K, M)`. -/
lemma sum_range_revIdx (w : ℕ → ℝ) {K M : ℕ} (hKM : K ≤ M) :
    ∑ i ∈ Finset.range K, w (revIdx M i) = ∑ i ∈ Finset.Ico (M - K) M, w i := by
  have h1 : ∑ i ∈ Finset.range K, w (revIdx M i)
      = ∑ i ∈ Finset.range K, w (M - K + (K - 1 - i)) :=
    Finset.sum_congr rfl fun i hi => by
      have hi' := Finset.mem_range.1 hi
      congr 1
      unfold revIdx
      rw [if_pos (by omega)]
      omega
  have h2 := Finset.sum_range_reflect (fun j => w (M - K + j)) K
  have h3 := Finset.sum_Ico_eq_sum_range w (M - K) M
  rw [show M - (M - K) = K by omega] at h3
  rw [h1, h3]
  exact h2

/-- `revIdx M` keeps `[0, K)`, `K ≤ M`, below `M`. -/
lemma revIdx_lt {K M m : ℕ} (hKM : K ≤ M) (hm : m < K) : revIdx M m < M := by
  unfold revIdx
  rw [if_pos (by omega)]
  omega

variable [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-! ### The sharp survival with hypotheses on `[0, n)` -/

/-- **The sharp survival bound, with the variance hypotheses on `[0, n)` only**:
`P(S_j ≤ g(j) ∀ j ≤ n) ≤ (Y + c)√(2/(π∑_{i<n} v_i))` for `g ≤ Y` on `[0, n]`, `Y ≥ 0`, `n ≥ 1`,
`v_j ≠ 0` and `c ≥ √(πv_j/2)` for `j < n`.  `RMF.IsGaussianWalk.measureReal_survival_le_sqrt` asks
both for every `j`, which a walk padded past its horizon (the comparisons pad with variance `1`)
meets only for `c ≥ √(π/2)`; its supermartingale steps
(`RMF.IsGaussianWalk.integral_survival_gaussOdd_step`) only see `j < n`, and this is its proof
with that bookkeeping. -/
theorem IsGaussianWalk.measureReal_survival_le_sqrt_of_lt (h : IsGaussianWalk G v μ)
    {g : ℕ → ℝ} {Y c : ℝ} (hY : 0 ≤ Y) {n : ℕ} (hn : 1 ≤ n) (hg : ∀ j ≤ n, g j ≤ Y)
    (hv : ∀ j, j < n → v j ≠ 0) (hc0 : 0 < c) (hc : ∀ j, j < n → √(π * v j / 2) ≤ c) :
    μ.real (survivalSet G g n)
      ≤ (Y + c) * √(2 / (π * ∑ i ∈ Finset.range n, (v i : ℝ))) := by
  -- the supermartingale, from `n` down to `n - d`
  have key : ∀ d, d ≤ n → μ.real (survivalSet G g n)
      ≤ ∫ ω, (survivalSet G g (n - d)).indicator
          (fun ω => gaussOdd (∑ i ∈ Finset.Ico (n - d) n, v i)
            (Y - walk G (n - d) ω + c)) ω ∂μ := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty]
      rw [← integral_indicator_one (h.measurableSet_survivalSet g n)]
      refine le_of_eq (integral_congr_ae (ae_of_all _ fun ω => ?_))
      by_cases hω : ω ∈ survivalSet G g n
      · have hSn : walk G n ω ≤ g n := hω n le_rfl
        have hgn := hg n le_rfl
        rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, gaussOdd_zero_var (by linarith)]
        rfl
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    | succ d ih =>
      intro hd
      have hk : n - (d + 1) + 1 = n - d := by omega
      have hstep := h.integral_survival_gaussOdd_step (g := g) (Y := Y) (c := c)
        (∑ i ∈ Finset.Ico (n - d) n, v i) (k := n - (d + 1))
        (hg _ (by omega)) (by rw [hk]; exact hg _ (by omega)) (hv _ (by omega)) hc0
        (hc _ (by omega))
      rw [hk] at hstep
      have hsum : v (n - (d + 1)) + ∑ i ∈ Finset.Ico (n - d) n, v i
          = ∑ i ∈ Finset.Ico (n - (d + 1)) n, v i := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n - (d + 1) < n), hk]
      rw [hsum] at hstep
      exact le_trans (ih (by omega)) hstep
  have hsurv := key n le_rfl
  rw [Nat.sub_self] at hsurv
  -- at time `0` the tube is the constant `κ_V(Y + c)`
  set V : ℝ≥0 := ∑ i ∈ Finset.Ico 0 n, v i with hV
  have hVne : V ≠ 0 := by
    rw [hV]
    intro h0
    exact hv 0 hn ((Finset.sum_eq_zero_iff.1 h0) 0 (Finset.mem_Ico.2 ⟨le_rfl, hn⟩))
  have hκ0 : 0 ≤ gaussOdd V (Y + c) := gaussOdd_nonneg V (by linarith)
  have hκ := gaussOdd_le_mul_sqrt hVne (show 0 ≤ Y + c by linarith)
  have hfun : (survivalSet G g 0).indicator (fun ω => gaussOdd V (Y - walk G 0 ω + c))
      = (survivalSet G g 0).indicator (fun _ => gaussOdd V (Y + c)) := by
    funext ω
    simp [walk]
  have hint : ∫ ω, (survivalSet G g 0).indicator (fun ω => gaussOdd V (Y - walk G 0 ω + c)) ω ∂μ
      ≤ gaussOdd V (Y + c) := by
    rw [hfun, integral_indicator_const _ (h.measurableSet_survivalSet g 0), smul_eq_mul]
    have hle : μ.real (survivalSet G g 0) ≤ 1 := measureReal_le_one
    nlinarith [measureReal_nonneg (μ := μ) (s := survivalSet G g 0)]
  have hVR : ((V : ℝ≥0) : ℝ) = ∑ i ∈ Finset.range n, (v i : ℝ) := by
    rw [hV, Finset.range_eq_Ico]
    push_cast
    rfl
  calc μ.real (survivalSet G g n)
      ≤ ∫ ω, (survivalSet G g 0).indicator (fun ω => gaussOdd V (Y - walk G 0 ω + c)) ω ∂μ :=
        hsurv
    _ ≤ gaussOdd V (Y + c) := hint
    _ ≤ (Y + c) * √(2 / (π * V)) := hκ
    _ = (Y + c) * √(2 / (π * ∑ i ∈ Finset.range n, (v i : ℝ))) := by rw [hVR]

/-! ### The slab local ballot's arithmetic -/

/-- `√(2/(πS₁))·√(2/(πS₃))/√(2πS₂) = 2/(π√(2πS₁S₂S₃))`. -/
lemma sqrt_slab_eq {S₁ S₂ S₃ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hS₃ : 0 < S₃) :
    √(2 / (π * S₁)) * √(2 / (π * S₃)) / √(2 * π * S₂)
      = 2 / (π * √(2 * π * (S₁ * S₂ * S₃))) := by
  have hπ := Real.pi_pos
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div (by positivity)]
  have hrhs : 2 / (π * √(2 * π * (S₁ * S₂ * S₃)))
      = √((2 / π) ^ 2 / (2 * π * (S₁ * S₂ * S₃))) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
    field_simp
  rw [hrhs]
  congr 1
  field_simp

/-! ### The sum over slabs -/

/-- The binomial coefficients `C(n+2,2)`, `C(n+3,3)`, `C(n+4,4)`, in `ℝ`:
`2C(n+2,2) = (n + 1)(n + 2)` and `kC(n+k,k) = (n + k)C(n+k-1,k-1)`. -/
lemma cast_choose_slab (n : ℕ) :
    (((n + 2).choose 2 : ℕ) : ℝ) * 2 = ((n : ℝ) + 1) * ((n : ℝ) + 2)
      ∧ ((n : ℝ) + 3) * (((n + 2).choose 2 : ℕ) : ℝ) = (((n + 3).choose 3 : ℕ) : ℝ) * 3
      ∧ ((n : ℝ) + 4) * (((n + 3).choose 3 : ℕ) : ℝ) = (((n + 4).choose 4 : ℕ) : ℝ) * 4 := by
  have e2 : (n + 2).choose 2 * 2 = (n + 1) * (n + 2) := by
    have h := Nat.add_one_mul_choose_eq (n + 1) 1
    rw [Nat.choose_one_right] at h
    calc (n + 2).choose 2 * 2 = (n + 1 + 1).choose (1 + 1) * (1 + 1) := rfl
      _ = (n + 1 + 1) * (n + 1) := h.symm
      _ = (n + 1) * (n + 2) := by ring
  have e3 : (n + 3) * (n + 2).choose 2 = (n + 3).choose 3 * 3 :=
    Nat.add_one_mul_choose_eq (n + 2) 2
  have e4 : (n + 4) * (n + 3).choose 3 = (n + 4).choose 4 * 4 :=
    Nat.add_one_mul_choose_eq (n + 3) 3
  exact ⟨by exact_mod_cast e2, by exact_mod_cast e3, by exact_mod_cast e4⟩

end RMF
