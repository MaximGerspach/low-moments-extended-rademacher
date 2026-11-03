/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedCaich

/-!
# The fractional-part sum below `q = ½`

Proposition 3.2 of the paper, for `0 ≤ q ≤ ½`.  With
`R(x) = x^{-1/2}∑_{n≤x} X(n){√(x/n)}` (`RMF.fracPartSum`), `E|R(x)| ≪ (log log x)^{-1/4}`
(`RMF.exists_integral_norm_fracPartSum_le`), hence `E|R(x)|^{2q} ≪ (log log x)^{-q/2}` for
`0 ≤ q ≤ ½` (`RMF.exists_integral_rpow_norm_fracPartSum_le_smallQ`).  With the weighted bound
this gives the uniform upper bound for the extended sum below `½`, Theorem 1.1 there
(`RMF.exists_const_integral_rpow_normalisedSum_compMultExtension_le_smallQ_uniform`).

Split `n ≤ x` at `x/(M+1)²`, where `M = ⌊(log log x)^{1/4}⌋`.  Below the split, orthogonality
gives `E|·| ≤ √x/(M+1)`.  Above it, on each block `I_m = (x/(m+1)², x/m²]` the weight
`{√(x/n)} = √(x/n) - m` decreases and stays below `1`, so summation by parts
(`RMF.integral_norm_sum_Ioc_mul_le`) bounds the block by its largest partial sum.  That is one or
two short intervals, each no longer than its start and bounded by Caich at `q = ½` crudely enough
(`y·log(s/y) ≤ 2√(sy)`) to give `≪ √x·m^{-5/4}·(log log x)^{-1/4} + 4`, which is summable in `m`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Summation by parts -/

/-- **Summation by parts on `(a, b]`**, against the partial sums `C(k) = ∑_{a<n≤k} c(n)`:
`∑_{a<n≤b} c(n)w(n) = ∑_{a<k≤b} (w(k) - w(k+1))·C(k) + w(b+1)·C(b)`. -/
lemma sum_Ioc_mul_eq_sum_sub_mul_add (c : ℕ → ℂ) (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, c n * (w n : ℂ)
      = ∑ k ∈ Finset.Ioc a b, ((w k - w (k + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc a k, c n
        + (w (b + 1) : ℂ) * ∑ n ∈ Finset.Ioc a b, c n := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih, Finset.sum_Ioc_succ_top hab,
      Finset.sum_Ioc_succ_top hab]
    push_cast
    ring

/-- The weights of a summation by parts telescope: `∑_{a<k≤b} (w(k) - w(k+1)) = w(a+1) - w(b+1)`. -/
lemma sum_Ioc_sub_succ_eq (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, (w k - w (k + 1)) = w (a + 1) - w (b + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih]
    ring

/-- **Summation by parts, in norm.**  If `w` decreases on `(a, b+1]` and `w(b+1) ≥ 0`, then
`|∑_{a<n≤b} c(n)w(n)| ≤ ∑_{a<k≤b} (w(k) - w(k+1))·|C(k)| + w(b+1)·|C(b)|`. -/
lemma norm_sum_Ioc_mul_le (c : ℕ → ℂ) (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hw : ∀ k ∈ Finset.Ioc a b, w (k + 1) ≤ w k) (hw0 : 0 ≤ w (b + 1)) :
    ‖∑ n ∈ Finset.Ioc a b, c n * (w n : ℂ)‖
      ≤ ∑ k ∈ Finset.Ioc a b, (w k - w (k + 1)) * ‖∑ n ∈ Finset.Ioc a k, c n‖
        + w (b + 1) * ‖∑ n ∈ Finset.Ioc a b, c n‖ := by
  rw [sum_Ioc_mul_eq_sum_sub_mul_add c w hab]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k hk => le_of_eq ?_)) (le_of_eq ?_))
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hw k hk))]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]

/-- **Summation by parts in expectation.**  If `w` decreases on `(a, b+1]`, `w(b+1) ≥ 0`, and every
partial sum `C(k) = ∑_{a<n≤k} c(n)`, `a < k ≤ b`, has `E|C(k)| ≤ B`, then
`E|∑_{a<n≤b} c(n)w(n)| ≤ w(a+1)·B`: the weights `w(k) - w(k+1)` and `w(b+1)` are nonnegative and
add up to `w(a+1)`. -/
theorem integral_norm_sum_Ioc_mul_le {μ : Measure Ω} (c : ℕ → Ω → ℂ) (w : ℕ → ℝ) {a b : ℕ}
    (hab : a ≤ b) (hc : ∀ n, Integrable (c n) μ) (hw : ∀ k ∈ Finset.Ioc a b, w (k + 1) ≤ w k)
    (hw0 : 0 ≤ w (b + 1)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k ∈ Finset.Ioc a b, (∫ ω, ‖∑ n ∈ Finset.Ioc a k, c n ω‖ ∂μ) ≤ B) :
    (∫ ω, ‖∑ n ∈ Finset.Ioc a b, c n ω * (w n : ℂ)‖ ∂μ) ≤ w (a + 1) * B := by
  have hC : ∀ k, Integrable (fun ω => ‖∑ n ∈ Finset.Ioc a k, c n ω‖) μ := fun k =>
    (integrable_finsetSum (Finset.Ioc a k) fun n _ => hc n).norm
  have hBb : (∫ ω, ‖∑ n ∈ Finset.Ioc a b, c n ω‖ ∂μ) ≤ B := by
    rcases eq_or_lt_of_le hab with h | h
    · subst h
      simpa using hB0
    · exact hB b (Finset.mem_Ioc.2 ⟨h, le_rfl⟩)
  have hS : Integrable (fun ω => ∑ k ∈ Finset.Ioc a b,
      (w k - w (k + 1)) * ‖∑ n ∈ Finset.Ioc a k, c n ω‖) μ :=
    integrable_finsetSum (Finset.Ioc a b) fun k _ => (hC k).const_mul (w k - w (k + 1))
  calc (∫ ω, ‖∑ n ∈ Finset.Ioc a b, c n ω * (w n : ℂ)‖ ∂μ)
      ≤ ∫ ω, (∑ k ∈ Finset.Ioc a b, (w k - w (k + 1)) * ‖∑ n ∈ Finset.Ioc a k, c n ω‖
          + w (b + 1) * ‖∑ n ∈ Finset.Ioc a b, c n ω‖) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
          (hS.add ((hC b).const_mul (w (b + 1)))) ?_
        filter_upwards with ω
        exact norm_sum_Ioc_mul_le (fun n => c n ω) w hab hw hw0
    _ = ∑ k ∈ Finset.Ioc a b, (w k - w (k + 1)) * (∫ ω, ‖∑ n ∈ Finset.Ioc a k, c n ω‖ ∂μ)
          + w (b + 1) * (∫ ω, ‖∑ n ∈ Finset.Ioc a b, c n ω‖ ∂μ) := by
        rw [integral_add hS ((hC b).const_mul (w (b + 1))),
          integral_finsetSum (Finset.Ioc a b) fun k _ => (hC k).const_mul (w k - w (k + 1))]
        simp only [integral_const_mul]
    _ ≤ ∑ k ∈ Finset.Ioc a b, (w k - w (k + 1)) * B + w (b + 1) * B :=
        add_le_add (Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (hB k hk) (sub_nonneg.2 (hw k hk)))
          (mul_le_mul_of_nonneg_left hBb hw0)
    _ = w (a + 1) * B := by
        rw [← Finset.sum_mul, sum_Ioc_sub_succ_eq w hab]
        ring

/-- **Tiling by consecutive intervals.**  For `t` decreasing,
`∑_{t(M)<n≤t(0)} g(n) = ∑_{j<M} ∑_{t(j+1)<n≤t(j)} g(n)`. -/
lemma sum_Ioc_eq_sum_range_sum_Ioc (g : ℕ → ℂ) (t : ℕ → ℕ) (ht : ∀ j, t (j + 1) ≤ t j)
    (M : ℕ) :
    ∑ n ∈ Finset.Ioc (t M) (t 0), g n
      = ∑ j ∈ Finset.range M, ∑ n ∈ Finset.Ioc (t (j + 1)) (t j), g n := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih, ← Finset.sum_Ioc_consecutive g (ht M)
      (antitone_nat_of_succ_le ht (Nat.zero_le M))]
    exact add_comm _ _

/-! ### The blocks `I_m = (x/(m+1)², x/m²]` -/

/-- On `I_m = (x/(m+1)², x/m²]`, `m ≤ √(x/n) < m + 1`. -/
lemma le_sqrt_div_and_lt_of_mem_Ioc {x : ℝ} (hx : 0 ≤ x) {m n : ℕ} (hm : 1 ≤ m)
    (hn : n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊) :
    (m : ℝ) ≤ Real.sqrt (x / n) ∧ Real.sqrt (x / n) < (m : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h1
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm10 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlo : x / ((m : ℝ) + 1) ^ 2 < n := Nat.lt_of_floor_lt h1
  have hhi : (n : ℝ) ≤ x / (m : ℝ) ^ 2 :=
    (Nat.le_floor_iff (div_nonneg hx (sq_nonneg _))).1 h2
  refine ⟨?_, ?_⟩
  · rw [Real.le_sqrt (Nat.cast_nonneg m) (div_nonneg hx hn0.le), le_div_iff₀ hn0]
    have := (le_div_iff₀ (pow_pos hm0 2)).1 hhi
    linarith
  · rw [Real.sqrt_lt' hm10, div_lt_iff₀ hn0]
    have := (div_lt_iff₀ (pow_pos hm10 2)).1 hlo
    linarith

/-- On `I_m`, `{√(x/n)} = √(x/n) - m`. -/
lemma fract_sqrt_div_eq_of_mem_Ioc {x : ℝ} (hx : 0 ≤ x) {m n : ℕ} (hm : 1 ≤ m)
    (hn : n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊) :
    Int.fract (Real.sqrt (x / n)) = Real.sqrt (x / n) - m := by
  obtain ⟨hlow, hup⟩ := le_sqrt_div_and_lt_of_mem_Ioc hx hm hn
  have hfl : ⌊Real.sqrt (x / n)⌋ = (m : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨hlow, hup⟩
  rw [← Int.self_sub_floor, hfl, Int.cast_natCast]

/-! ### Short intervals: counting and splitting -/

omit [MeasurableSpace Ω] in
/-- A short interval ending at an integer: `M(s, k - s) = ∑_{⌊s⌋<n≤k} f(n)`. -/
lemma shortIntervalSum_natCast_sub (f : Ω → ArithmeticFunction ℂ) (s : ℝ) (k : ℕ) (ω : Ω) :
    shortIntervalSum f s ((k : ℝ) - s) ω = ∑ n ∈ Finset.Ioc ⌊s⌋₊ k, f ω n := by
  have h : s + ((k : ℝ) - s) = k := by ring
  rw [shortIntervalSum, h, Nat.floor_natCast]

omit [MeasurableSpace Ω] in
/-- Splitting at `2s`: for `0 ≤ s` and `2s ≤ k`, `∑_{⌊s⌋<n≤k} f(n) = M(s, s) + M(2s, k - 2s)`. -/
lemma sum_Ioc_floor_eq_shortIntervalSum_add (f : Ω → ArithmeticFunction ℂ) {s : ℝ} (hs : 0 ≤ s)
    {k : ℕ} (hk : 2 * s ≤ k) (ω : Ω) :
    ∑ n ∈ Finset.Ioc ⌊s⌋₊ k, f ω n
      = shortIntervalSum f s s ω + shortIntervalSum f (2 * s) ((k : ℝ) - 2 * s) ω := by
  rw [shortIntervalSum_natCast_sub, shortIntervalSum, ← two_mul,
    Finset.sum_Ioc_consecutive (fun n => f ω n) (Nat.floor_le_floor (by linarith))
      (Nat.floor_le_of_le hk)]

/-- Values of a Rademacher function are integrable. -/
lemma IsRademacherRMF.integrable_apply {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hf : IsRademacherRMF f μ) (n : ℕ) : Integrable (fun ω => f ω n) μ :=
  Integrable.of_bound (hf.measurable_apply n).aestronglyMeasurable 1 (hf.norm_apply_le_one n)

/-- Short-interval sums of a Rademacher function are integrable. -/
lemma integrable_norm_shortIntervalSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (s y : ℝ) :
    Integrable (fun ω =>
      ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  unfold shortIntervalSum
  exact (integrable_finsetSum (Finset.Ioc ⌊s⌋₊ ⌊s + y⌋₊) fun n _ => hRa.integrable_apply n).norm

/-- For `0 ≤ y < 2` a short interval holds at most two integers, so `E|M(s,y)| ≤ 2`. -/
lemma integral_norm_shortIntervalSum_le_two {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {s y : ℝ} (hs : 0 ≤ s) (hy0 : 0 ≤ y) (hy : y < 2) :
    (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ) ≤ 2 := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hcard : (Finset.Ioc ⌊s⌋₊ ⌊s + y⌋₊).card ≤ 2 := by
    have h1 : (⌊s + y⌋₊ : ℝ) ≤ s + y := Nat.floor_le (by linarith)
    have h2 : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
    have h3 : (⌊s + y⌋₊ : ℝ) < ⌊s⌋₊ + 3 := by linarith
    have h4 : ⌊s + y⌋₊ < ⌊s⌋₊ + 3 := by exact_mod_cast h3
    rw [Nat.card_Ioc]
    omega
  calc (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
      ≤ ∫ _ω, (2 : ℝ) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
          (integrable_const _) ?_
        filter_upwards [(Filter.eventually_all_finset (Finset.Ioc ⌊s⌋₊ ⌊s + y⌋₊)).2
          fun n _ => hRa.norm_apply_le_one n] with ω hω
        calc ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖
            ≤ ∑ n ∈ Finset.Ioc ⌊s⌋₊ ⌊s + y⌋₊, ‖squarefreeExtension (fun p => X p ω) n‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.Ioc ⌊s⌋₊ ⌊s + y⌋₊, (1 : ℝ) := Finset.sum_le_sum hω
          _ = (Finset.Ioc ⌊s⌋₊ ⌊s + y⌋₊).card := by simp
          _ ≤ 2 := by exact_mod_cast hcard
    _ = 2 := by simp

/-- **Caich at `q = ½`, for every length.**  There are `C` and `s₀` such that for every Rademacher
`X`, `s ≥ s₀` and `0 ≤ y ≤ s`, `E|M(s,y)| ≤ C·√((2√(sy) + 2y)/√(log log s)) + 2`:
`RMF.exists_integral_norm_shortIntervalSum_le` for `y ≥ 2`, the count of integers below. -/
theorem exists_integral_norm_shortIntervalSum_le_add_two :
    ∃ C s₀ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ s y : ℝ, s₀ ≤ s → 0 ≤ y → y ≤ s →
        (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
          ≤ C * Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y)
            / Real.sqrt (Real.log (Real.log s))) + 2 := by
  obtain ⟨C, s₀, hC, H⟩ := exists_integral_norm_shortIntervalSum_le (Ω := Ω)
  refine ⟨C, max s₀ 0, hC, ?_⟩
  intro X μ hX s y hs hy0 hys
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
  have hnn : 0 ≤ C * Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y)
      / Real.sqrt (Real.log (Real.log s))) := mul_nonneg hC.le (Real.sqrt_nonneg _)
  rcases lt_or_ge y 2 with hy | hy
  · have h2 := integral_norm_shortIntervalSum_le_two hX hs0 hy0 hy
    linarith
  · have h := H X μ hX s y (le_trans (le_max_left _ _) hs) hy hys
    linarith

/-! ### The algebra of a block -/

/-- `1 ≤ log log x` for `x ≥ e^e`. -/
lemma one_le_log_log_of_exp_exp_le {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    1 ≤ Real.log (Real.log x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have h := Real.log_le_log (Real.exp_pos 1) hlogx
  rwa [Real.log_exp] at h

/-- The length of `I_m`: `x/m² - x/(m+1)² ≤ 2x/m³`. -/
lemma div_sq_sub_div_add_one_sq_le {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) :
    x / m ^ 2 - x / (m + 1) ^ 2 ≤ 2 * (x / m ^ 3) := by
  have hm1 : 0 < m + 1 := by linarith
  rw [div_sub_div _ _ (pow_pos hm 2).ne' (pow_pos hm1 2).ne', mul_div_assoc',
    div_le_div_iff₀ (mul_pos (pow_pos hm 2) (pow_pos hm1 2)) (pow_pos hm 3)]
  nlinarith [mul_nonneg (mul_nonneg hx hm.le) hm.le,
    mul_nonneg (mul_nonneg (mul_nonneg hx hm.le) hm.le) hm.le]

/-- `x/m² ≤ 4x/(m+1)²` for `m ≥ 1`. -/
lemma div_sq_le_four_mul_div_add_one_sq {x m : ℝ} (hx : 0 ≤ x) (hm : 1 ≤ m) :
    x / m ^ 2 ≤ 4 * (x / (m + 1) ^ 2) := by
  have hm0 : 0 < m := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hm0 2) (pow_pos (by linarith : 0 < m + 1) 2)]
  nlinarith [mul_nonneg (mul_nonneg hx (by linarith : 0 ≤ 3 * m + 1)) (sub_nonneg.2 hm)]

/-- For `x ≥ e^e` and `s ≥ √x`, `log log s ≥ ¼ log log x`. -/
lemma log_log_div_four_le_log_log {x s : ℝ} (hx : Real.exp (Real.exp 1) ≤ x)
    (hs : Real.sqrt x ≤ s) : Real.log (Real.log x) / 4 ≤ Real.log (Real.log s) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hΛ1 := one_le_log_log_of_exp_exp_le hx
  have hlx : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) hlogx
  have hlogs : Real.log x / 2 ≤ Real.log s := by
    rw [← Real.log_sqrt hx0.le]
    exact Real.log_le_log (Real.sqrt_pos.2 hx0) hs
  have h1 : Real.log (Real.log x / 2) ≤ Real.log (Real.log s) :=
    Real.log_le_log (by linarith) hlogs
  rw [Real.log_div hlx.ne' two_ne_zero] at h1
  have h2 : Real.log 2 < 3 / 4 := lt_trans Real.log_two_lt_d9 (by norm_num)
  linarith

/-- **The size of one piece.**  For `x ≥ 0`, `m ≥ 1`, `0 ≤ s ≤ 2x/m²`, `0 ≤ y ≤ 2x/m³`,
`log log x ≥ 1` and `log log s ≥ ¼ log log x`,
`√((2√(sy) + 2y)/√(log log s)) ≤ 4√x/(m·m^{1/4}·(log log x)^{1/4})`: `√(sy) ≤ 2x/m^{5/2}`,
`y ≤ 2x/m^{5/2}` and `√(log log s) ≥ ½(log log x)^{1/2}`. -/
lemma sqrt_div_sqrt_log_log_le {x s y : ℝ} {m : ℕ} (hx : 0 ≤ x) (hm : 1 ≤ m)
    (hs : s ≤ 2 * (x / (m : ℝ) ^ 2)) (hy0 : 0 ≤ y) (hy : y ≤ 2 * (x / (m : ℝ) ^ 3))
    (hΛ1 : 1 ≤ Real.log (Real.log x))
    (hΛ : Real.log (Real.log x) / 4 ≤ Real.log (Real.log s)) :
    Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt (Real.log (Real.log s)))
      ≤ 4 * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
        * Real.log (Real.log x) ^ (1 / 4 : ℝ))) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (m : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Λ ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hΛdef] at hΛ1 hΛ ⊢
  rw [← ht, ← hr]
  have ht1 : 1 ≤ t := by
    rw [ht]
    exact Real.one_le_rpow hm1 (by norm_num)
  have hr1 : 1 ≤ r := by
    rw [hr]
    exact Real.one_le_rpow hΛ1 (by norm_num)
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < r := by linarith
  have ht4 : t ^ 4 = m := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    norm_num
  have hr4 : r ^ 4 = Λ := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hden : 0 < (m : ℝ) ^ 2 * t ^ 2 := mul_pos (pow_pos hm0 2) (pow_pos ht0 2)
  have h2x : 0 ≤ 2 * x := by linarith
  have hsy : Real.sqrt (s * y) ≤ 2 * x / ((m : ℝ) ^ 2 * t ^ 2) := by
    rw [Real.sqrt_le_left (div_nonneg h2x hden.le)]
    calc s * y ≤ (2 * (x / (m : ℝ) ^ 2)) * (2 * (x / (m : ℝ) ^ 3)) :=
          mul_le_mul hs hy hy0 (mul_nonneg zero_le_two (div_nonneg hx (sq_nonneg _)))
      _ = (2 * x) ^ 2 / ((m : ℝ) ^ 4 * (m : ℝ)) := by ring
      _ = (2 * x / ((m : ℝ) ^ 2 * t ^ 2)) ^ 2 := by
          rw [div_pow, ← ht4]
          ring
  have hy' : y ≤ 2 * x / ((m : ℝ) ^ 2 * t ^ 2) := by
    have ht2 : t ^ 2 ≤ (m : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (one_le_pow₀ ht1 (n := 2)) (sq_nonneg t)
      rw [← ht4]
      nlinarith [h]
    calc y ≤ 2 * (x / (m : ℝ) ^ 3) := hy
      _ ≤ 2 * (x / ((m : ℝ) ^ 2 * t ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hx hden ?_) zero_le_two
          calc (m : ℝ) ^ 2 * t ^ 2 ≤ (m : ℝ) ^ 2 * m :=
                mul_le_mul_of_nonneg_left ht2 (by positivity)
            _ = (m : ℝ) ^ 3 := by ring
      _ = 2 * x / ((m : ℝ) ^ 2 * t ^ 2) := by ring
  have hnum : 2 * Real.sqrt (s * y) + 2 * y ≤ 8 * x / ((m : ℝ) ^ 2 * t ^ 2) := by
    have e : 8 * x / ((m : ℝ) ^ 2 * t ^ 2)
        = 2 * (2 * x / ((m : ℝ) ^ 2 * t ^ 2)) + 2 * (2 * x / ((m : ℝ) ^ 2 * t ^ 2)) := by ring
    rw [e]
    linarith
  have hl0 : 0 ≤ Real.log (Real.log s) := by linarith
  have hr2 : 0 ≤ r ^ 2 / 2 := by positivity
  have hsq : r ^ 2 / 2 ≤ Real.sqrt (Real.log (Real.log s)) := by
    rw [Real.le_sqrt hr2 hl0]
    calc (r ^ 2 / 2) ^ 2 = r ^ 4 / 4 := by ring
      _ = Λ / 4 := by rw [hr4]
      _ ≤ Real.log (Real.log s) := hΛ
  have hfrac : (2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt (Real.log (Real.log s))
      ≤ (4 * (Real.sqrt x / ((m : ℝ) * t * r))) ^ 2 := by
    calc (2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt (Real.log (Real.log s))
        ≤ (8 * x / ((m : ℝ) ^ 2 * t ^ 2)) / (r ^ 2 / 2) :=
          div_le_div₀ (div_nonneg (by linarith) hden.le) hnum (div_pos (pow_pos hr0 2) two_pos)
            hsq
      _ = (4 * (Real.sqrt x / ((m : ℝ) * t * r))) ^ 2 := by
          rw [mul_pow, div_pow, Real.sq_sqrt hx]
          ring
  have hz0 : 0 ≤ 4 * (Real.sqrt x / ((m : ℝ) * t * r)) :=
    mul_nonneg (by norm_num) (div_nonneg (Real.sqrt_nonneg x)
      (mul_pos (mul_pos hm0 ht0) hr0).le)
  calc Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y) / Real.sqrt (Real.log (Real.log s)))
      ≤ Real.sqrt ((4 * (Real.sqrt x / ((m : ℝ) * t * r))) ^ 2) := Real.sqrt_le_sqrt hfrac
    _ = 4 * (Real.sqrt x / ((m : ℝ) * t * r)) := Real.sqrt_sq hz0

/-! ### Short intervals inside a block -/

/-- **One piece of a partial sum on `I_m`.**  There are `C` and `x₁` such that for every Rademacher
`X`, `x ≥ x₁`, `m ≥ 1`, `√x ≤ s ≤ 2x/m²` and `0 ≤ y ≤ min(s, 2x/m³)`,
`E|M(s,y)| ≤ C·√x/(m·m^{1/4}·(log log x)^{1/4}) + 2`. -/
theorem exists_integral_norm_shortIntervalSum_le_of_block :
    ∃ C x₁ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (x : ℝ) (m : ℕ) (s y : ℝ), x₁ ≤ x → 1 ≤ m → Real.sqrt x ≤ s →
        s ≤ 2 * (x / (m : ℝ) ^ 2) → 0 ≤ y → y ≤ s → y ≤ 2 * (x / (m : ℝ) ^ 3) →
        (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
          ≤ C * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
            * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 2 := by
  obtain ⟨C, s₀, hC, H⟩ := exists_integral_norm_shortIntervalSum_le_add_two (Ω := Ω)
  refine ⟨4 * C, max (Real.exp (Real.exp 1)) (max s₀ 1 ^ 2), mul_pos four_pos hC, ?_⟩
  intro X μ hX x m s y hx hm hsx hs hy0 hys hy
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hs₀ : s₀ ≤ s := by
    have h1 : max s₀ 1 ≤ Real.sqrt x :=
      (Real.le_sqrt (le_trans zero_le_one (le_max_right _ _)) hx0.le).2
        (le_trans (le_max_right _ _) hx)
    linarith [le_max_left s₀ 1]
  have h := H X μ hX s y hs₀ hy0 hys
  have hkey := sqrt_div_sqrt_log_log_le hx0.le hm hs hy0 hy
    (one_le_log_log_of_exp_exp_le hxe) (log_log_div_four_le_log_log hxe hsx)
  calc (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
      ≤ C * Real.sqrt ((2 * Real.sqrt (s * y) + 2 * y)
          / Real.sqrt (Real.log (Real.log s))) + 2 := h
    _ ≤ C * (4 * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
          * Real.log (Real.log x) ^ (1 / 4 : ℝ)))) + 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hkey hC.le) le_rfl
    _ = 4 * C * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
          * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 2 := by ring

/-- **A partial sum on `I_m`.**  There are `K` and `x₁` such that for every Rademacher `X`,
`x ≥ x₁`, `m ≥ 1` with `(m+1)² ≤ √x`, and `x/(m+1)² < k ≤ x/m²`,
`E|∑_{x/(m+1)²<n≤k} X(n)| ≤ K·√x/(m·m^{1/4}·(log log x)^{1/4}) + 4`.  With `x' = x/(m+1)²` the sum
is `M(x', k - x')` if `k ≤ 2x'`, and `M(x', x') + M(2x', k - 2x')` otherwise, each piece no longer
than its start, as Caich's bound asks (`I_1` and `I_2` are longer than their left ends). -/
theorem exists_integral_norm_sum_Ioc_floor_le :
    ∃ K x₁ : ℝ, 0 < K ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (x : ℝ) (m k : ℕ), x₁ ≤ x → 1 ≤ m → ((m : ℝ) + 1) ^ 2 ≤ Real.sqrt x →
        ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ < k → k ≤ ⌊x / (m : ℝ) ^ 2⌋₊ →
        (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ k,
            squarefreeExtension (fun p => X p ω) n‖ ∂μ)
          ≤ K * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
            * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 4 := by
  obtain ⟨C, x₁, hC, H⟩ := exists_integral_norm_shortIntervalSum_le_of_block (Ω := Ω)
  refine ⟨2 * C, max x₁ (Real.exp (Real.exp 1)), mul_pos two_pos hC, ?_⟩
  intro X μ hX x m k hx hm hm2 hk1 hk2
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hΛ1 := one_le_log_log_of_exp_exp_le hxe
  have hz0 : 0 ≤ Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
      * Real.log (Real.log x) ^ (1 / 4 : ℝ)) :=
    div_nonneg (Real.sqrt_nonneg x) (mul_nonneg (mul_nonneg hm0.le
      (Real.rpow_nonneg hm0.le _)) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
      * Real.log (Real.log x) ^ (1 / 4 : ℝ)) := ⟨_, rfl⟩
  rw [← hz] at hz0 ⊢
  have H' : ∀ s y : ℝ, Real.sqrt x ≤ s → s ≤ 2 * (x / (m : ℝ) ^ 2) → 0 ≤ y → y ≤ s →
      y ≤ 2 * (x / (m : ℝ) ^ 3) →
      (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) s y ω‖ ∂μ)
        ≤ C * z + 2 := by
    intro s y h1 h2 h3 h4 h5
    rw [hz]
    exact H X μ hX x m s y hx₁ hm h1 h2 h3 h4 h5
  obtain ⟨x', hx'⟩ : ∃ x' : ℝ, x' = x / ((m : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hx'] at hk1 ⊢
  have hx'0 : 0 < x' := by
    rw [hx']
    exact div_pos hx0 (by positivity)
  have hsqx : Real.sqrt x ≤ x' := by
    rw [hx', ← Real.div_sqrt (x := x)]
    exact div_le_div_of_nonneg_left hx0.le (by positivity) hm2
  have hk1' : x' < k := Nat.lt_of_floor_lt hk1
  have hk2' : (k : ℝ) ≤ x / (m : ℝ) ^ 2 :=
    (Nat.le_floor_iff (div_nonneg hx0.le (sq_nonneg _))).1 hk2
  have hmx : x' ≤ x / (m : ℝ) ^ 2 := by
    rw [hx']
    exact div_le_div_of_nonneg_left hx0.le (pow_pos hm0 2)
      (pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) 2)
  have h4 : x / (m : ℝ) ^ 2 ≤ 4 * x' := by
    rw [hx']
    exact div_sq_le_four_mul_div_add_one_sq hx0.le hm1
  have hlen : x / (m : ℝ) ^ 2 - x' ≤ 2 * (x / (m : ℝ) ^ 3) := by
    rw [hx']
    exact div_sq_sub_div_add_one_sq_le hx0.le hm0
  have hCz : 0 ≤ C * z := mul_nonneg hC.le hz0
  rcases le_or_gt (k : ℝ) (2 * x') with hk | hk
  · calc (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x'⌋₊ k, squarefreeExtension (fun p => X p ω) n‖ ∂μ)
        = ∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x'
            ((k : ℝ) - x') ω‖ ∂μ := by
          simp only [shortIntervalSum_natCast_sub]
      _ ≤ C * z + 2 := H' x' ((k : ℝ) - x') hsqx (by linarith) (by linarith) (by linarith)
            (by linarith)
      _ ≤ 2 * C * z + 4 := by linarith
  · have hM := integrable_norm_shortIntervalSum hX (μ := μ)
    calc (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x'⌋₊ k, squarefreeExtension (fun p => X p ω) n‖ ∂μ)
        = ∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x' x' ω
            + shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) (2 * x')
              ((k : ℝ) - 2 * x') ω‖ ∂μ := by
          congr 1
          funext ω
          rw [sum_Ioc_floor_eq_shortIntervalSum_add
            (fun ω => squarefreeExtension fun p => X p ω) hx'0.le hk.le ω]
      _ ≤ ∫ ω, (‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x' x' ω‖
            + ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) (2 * x')
              ((k : ℝ) - 2 * x') ω‖) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
            ((hM x' x').add (hM (2 * x') ((k : ℝ) - 2 * x')))
            (Filter.Eventually.of_forall fun ω => norm_add_le _ _)
      _ = (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x' x' ω‖ ∂μ)
            + ∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) (2 * x')
              ((k : ℝ) - 2 * x') ω‖ ∂μ :=
          integral_add (hM x' x') (hM (2 * x') ((k : ℝ) - 2 * x'))
      _ ≤ (C * z + 2) + (C * z + 2) :=
          add_le_add (H' x' x' hsqx (by linarith) hx'0.le le_rfl (by linarith))
            (H' (2 * x') ((k : ℝ) - 2 * x') (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith))
      _ = 2 * C * z + 4 := by ring

/-- **The sum over `I_m`.**  There are `K` and `x₁` such that for every Rademacher `X`, `x ≥ x₁` and
`m ≥ 1` with `(m+1)² ≤ √x`,
`E|∑_{x/(m+1)²<n≤x/m²} X(n){√(x/n)}| ≤ K·√x/(m·m^{1/4}·(log log x)^{1/4}) + 4`.  On `I_m` the
weight `{√(x/n)} = max(√(x/n) - m, 0)` decreases and stays below `1`, so summation by parts
(`RMF.integral_norm_sum_Ioc_mul_le`) bounds the sum by its largest partial sum
(`RMF.exists_integral_norm_sum_Ioc_floor_le`). -/
theorem exists_integral_norm_sum_Ioc_fract_le :
    ∃ K x₁ : ℝ, 0 < K ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (x : ℝ) (m : ℕ), x₁ ≤ x → 1 ≤ m → ((m : ℝ) + 1) ^ 2 ≤ Real.sqrt x →
        (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊,
            squarefreeExtension (fun p => X p ω) n
              * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ)
          ≤ K * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
            * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 4 := by
  obtain ⟨K, x₁, hK, H⟩ := exists_integral_norm_sum_Ioc_floor_le (Ω := Ω)
  refine ⟨K, max x₁ (Real.exp (Real.exp 1)), hK, ?_⟩
  intro X μ hX x m hx hm hm2
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hab : ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ≤ ⌊x / (m : ℝ) ^ 2⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hx0.le (pow_pos hm0 2)
      (pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) 2))
  have hB0 : 0 ≤ K * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
      * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 4 := by
    have hΛ1 := one_le_log_log_of_exp_exp_le hxe
    have h : 0 ≤ Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
        * Real.log (Real.log x) ^ (1 / 4 : ℝ)) :=
      div_nonneg (Real.sqrt_nonneg x) (mul_nonneg (mul_nonneg hm0.le
        (Real.rpow_nonneg hm0.le _)) (Real.rpow_nonneg (by linarith) _))
    linarith [mul_nonneg hK.le h]
  have hsum : ∀ ω, ∑ n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊,
        squarefreeExtension (fun p => X p ω) n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊,
        squarefreeExtension (fun p => X p ω) n * ((max (Real.sqrt (x / n) - m) 0 : ℝ) : ℂ) :=
    fun ω => Finset.sum_congr rfl fun n hn => by
      rw [fract_sqrt_div_eq_of_mem_Ioc hx0.le hm hn,
        max_eq_left (sub_nonneg.2 (le_sqrt_div_and_lt_of_mem_Ioc hx0.le hm hn).1)]
  have hw : ∀ k ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊,
      max (Real.sqrt (x / ((k + 1 : ℕ) : ℝ)) - m) 0 ≤ max (Real.sqrt (x / (k : ℝ)) - m) 0 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by
      have : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.1 hk).1
      exact_mod_cast this
    exact max_le_max (sub_le_sub_right (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_left hx0.le hk0 (by push_cast; linarith))) _) le_rfl
  have hwa : max (Real.sqrt (x / ((⌊x / ((m : ℝ) + 1) ^ 2⌋₊ + 1 : ℕ) : ℝ)) - m) 0 ≤ 1 := by
    have hm10 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h1 : x / ((m : ℝ) + 1) ^ 2 < (⌊x / ((m : ℝ) + 1) ^ 2⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have ha0 : (0 : ℝ) < (⌊x / ((m : ℝ) + 1) ^ 2⌋₊ : ℝ) + 1 := by positivity
    have h2 : Real.sqrt (x / ((⌊x / ((m : ℝ) + 1) ^ 2⌋₊ + 1 : ℕ) : ℝ)) < (m : ℝ) + 1 := by
      rw [Real.sqrt_lt' hm10]
      push_cast
      rw [div_lt_iff₀ ha0]
      have := (div_lt_iff₀ (pow_pos hm10 2)).1 h1
      linarith
    exact max_le (by linarith) zero_le_one
  calc (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊,
          squarefreeExtension (fun p => X p ω) n
            * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ)
      = ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / ((m : ℝ) + 1) ^ 2⌋₊ ⌊x / (m : ℝ) ^ 2⌋₊,
          squarefreeExtension (fun p => X p ω) n
            * ((max (Real.sqrt (x / n) - m) 0 : ℝ) : ℂ)‖ ∂μ := by
        congr 1
        funext ω
        rw [hsum ω]
    _ ≤ max (Real.sqrt (x / ((⌊x / ((m : ℝ) + 1) ^ 2⌋₊ + 1 : ℕ) : ℝ)) - m) 0
          * (K * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
            * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 4) :=
        integral_norm_sum_Ioc_mul_le (fun n ω => squarefreeExtension (fun p => X p ω) n)
          (fun n => max (Real.sqrt (x / (n : ℝ)) - m) 0) hab (fun n => hRa.integrable_apply n)
          hw (le_max_right _ _) hB0
          (fun k hk => H X μ hX x m k hx₁ hm hm2 (Finset.mem_Ioc.1 hk).1 (Finset.mem_Ioc.1 hk).2)
    _ ≤ 1 * (K * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
          * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 4) := mul_le_mul_of_nonneg_right hwa hB0
    _ = K * (Real.sqrt x / ((m : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)
          * Real.log (Real.log x) ^ (1 / 4 : ℝ))) + 4 := one_mul _

/-! ### Below the blocks: orthogonality -/

/-- `E|∑_{n∈S} f(n)c(n)|² ≤ #S` for coefficients of modulus at most one and `0 ∉ S`, by
orthogonality (`RMF.integral_normSq_weightedSum_of_orthogonality'`). -/
theorem integral_normSq_sum_mul_le_card {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (c : ℕ → ℂ)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) :
    (∫ ω, ‖∑ n ∈ S, f ω n * c n‖ ^ 2 ∂μ) ≤ S.card := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ) (s := S) (c := c)
    (d := fun m => ((if Squarefree m then 1 else 0 : ℝ) : ℂ))
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hS m hm) (hS n hn)]
      by_cases h : m = n
      · subst h
        by_cases hs : Squarefree m <;> simp [hs]
      · simp [h])
  have hcomm : ∀ ω, ∑ n ∈ S, f ω n * c n = ∑ n ∈ S, c n * f ω n := fun ω =>
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  simp_rw [hcomm]
  have hreal : (∫ ω, ‖∑ n ∈ S, c n * f ω n‖ ^ 2 ∂μ)
      = ∑ m ∈ S, ‖c m‖ ^ 2 * (if Squarefree m then 1 else 0) := by
    exact_mod_cast key
  rw [hreal]
  calc ∑ m ∈ S, ‖c m‖ ^ 2 * (if Squarefree m then 1 else 0)
      ≤ ∑ _m ∈ S, (1 : ℝ) := Finset.sum_le_sum fun m hm => by
        split_ifs
        · rw [mul_one]
          exact pow_le_one₀ (norm_nonneg _) (hc m hm)
        · rw [mul_zero]
          exact zero_le_one
    _ = S.card := by simp

/-- `E|∑_{n∈S} X(n)c(n)| ≤ √#S` for coefficients of modulus at most one and `0 ∉ S`: Jensen from
`RMF.integral_normSq_sum_mul_le_card`. -/
theorem integral_norm_sum_mul_le_sqrt_card {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (c : ℕ → ℂ)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) :
    (∫ ω, ‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖ ∂μ)
      ≤ Real.sqrt S.card := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hint : Integrable (fun ω =>
      ‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖ ^ 2) μ := by
    refine Integrable.of_bound (((Finset.measurable_sum S fun n _ =>
      (hRa.measurable_apply n).mul_const (c n)).norm.pow_const 2).aestronglyMeasurable)
      ((S.card : ℝ) ^ 2) ?_
    filter_upwards [(Filter.eventually_all_finset S).2 fun n _ => hRa.norm_apply_le_one n]
      with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hle : ‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖ ≤ S.card := by
      calc ‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖
          ≤ ∑ n ∈ S, ‖squarefreeExtension (fun p => X p ω) n * c n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ S, (1 : ℝ) := Finset.sum_le_sum fun n hn => by
            rw [norm_mul]
            exact mul_le_one₀ (hω n hn) (norm_nonneg _) (hc n hn)
        _ = S.card := by simp
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have h := integral_rpow_le_rpow_of_integral_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint
    (integral_normSq_sum_mul_le_card hRa S hS c hc)
  calc (∫ ω, ‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖ ∂μ)
      = ∫ ω, (‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
        congr 1
        funext ω
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ (S.card : ℝ) ^ (1 / 2 : ℝ) := h
    _ = Real.sqrt S.card := (Real.sqrt_eq_rpow _).symm

/-! ### Assembly -/

/-- `16 log log x ≤ x` for `x ≥ 1024`. -/
lemma sixteen_mul_log_log_le {x : ℝ} (hx : 1024 ≤ x) : 16 * Real.log (Real.log x) ≤ x := by
  have hx0 : 0 < x := by linarith
  have hsx : 32 ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num) hx0.le).2 (by norm_num; linarith)
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx0)
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hll : Real.log (Real.log x) ≤ Real.log x - 1 :=
    Real.log_le_sub_one_of_pos (Real.log_pos (by linarith))
  have h32 : 32 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
    mul_le_mul_of_nonneg_right hsx (Real.sqrt_nonneg x)
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  linarith

omit [MeasurableSpace Ω] in
/-- **The tiling of `R(x)`.**  For `x ≥ 0` and every `M`, `√x·R(x)` is the sum over
`0 < n ≤ x/(M+1)²` plus the sums over the blocks `(x/(j+2)², x/(j+1)²]`, `j < M`. -/
lemma fracPartSum_eq_div (f : Ω → ArithmeticFunction ℂ) {x : ℝ} (hx : 0 ≤ x) (M : ℕ) (ω : Ω) :
    fracPartSum f x ω
      = (∑ n ∈ Finset.Ioc 0 ⌊x / ((M : ℝ) + 1) ^ 2⌋₊,
            f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)
          + ∑ j ∈ Finset.range M, ∑ n ∈ Finset.Ioc ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊
              ⌊x / ((j : ℝ) + 1) ^ 2⌋₊, f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ))
        / (Real.sqrt x : ℂ) := by
  have ht : ∀ j : ℕ, ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊ ≤ ⌊x / ((j : ℝ) + 1) ^ 2⌋₊ := fun j =>
    Nat.floor_le_floor (div_le_div_of_nonneg_left hx (by positivity)
      (pow_le_pow_left₀ (by positivity) (by push_cast; linarith) 2))
  have htil : ∑ n ∈ Finset.Ioc ⌊x / ((M : ℝ) + 1) ^ 2⌋₊ ⌊x / (((0 : ℕ) : ℝ) + 1) ^ 2⌋₊,
        f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)
      = ∑ j ∈ Finset.range M, ∑ n ∈ Finset.Ioc ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊
          ⌊x / ((j : ℝ) + 1) ^ 2⌋₊, f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) :=
    sum_Ioc_eq_sum_range_sum_Ioc (fun n => f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ))
      (fun j : ℕ => ⌊x / ((j : ℝ) + 1) ^ 2⌋₊) ht M
  have hM0 : ⌊x / ((M : ℝ) + 1) ^ 2⌋₊ ≤ ⌊x / (((0 : ℕ) : ℝ) + 1) ^ 2⌋₊ :=
    antitone_nat_of_succ_le (f := fun j : ℕ => ⌊x / ((j : ℝ) + 1) ^ 2⌋₊) ht (Nat.zero_le M)
  have h0 : ⌊x / (((0 : ℕ) : ℝ) + 1) ^ 2⌋₊ = ⌊x⌋₊ := by simp
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [fracPartSum, ← Finset.sum_div, hIcc]
  congr 1
  rw [← h0, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hM0, htil]

/-- Finite sums of a Rademacher function against deterministic coefficients are integrable. -/
lemma integrable_norm_sum_squarefreeExtension_mul {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (S : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ S, squarefreeExtension (fun p => X p ω) n * c n‖) μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  exact (integrable_finsetSum S fun n _ => (hRa.integrable_apply n).mul_const (c n)).norm

/-- **Proposition 3.2 of the paper at `q = ½`.**  There are `C` and `x₀` such that for every
Rademacher `X` and `x ≥ x₀`, `E|R(x)| ≤ C·(log log x)^{-1/4}`.  With `r = (log log x)^{1/4}` and
`M = ⌊r⌋`: below `x/(M+1)²`, `E|·| ≤ √x/(M+1)` by orthogonality
(`RMF.integral_norm_sum_mul_le_sqrt_card`); the block `I_m`, `m ≤ M`, contributes at most
`K·√x·m^{-5/4}/r + 4` (`RMF.exists_integral_norm_sum_Ioc_fract_le`); and `∑ m^{-5/4} < ∞`,
`4M ≤ 4√x/r`. -/
theorem exists_integral_norm_fracPartSum_le :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
          ≤ C * Real.log (Real.log x) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨K, x₁, hK, H⟩ := exists_integral_norm_sum_Ioc_fract_le (Ω := Ω)
  have hZs : Summable (fun n : ℕ => ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by norm_num)
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∑' n : ℕ, ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    exact tsum_nonneg fun n => inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine ⟨K * Z + 5, max (max x₁ (Real.exp (Real.exp 1))) 1024,
    add_pos_of_nonneg_of_pos (mul_nonneg hK.le hZ0) (by norm_num), ?_⟩
  intro X μ hX x hx
  haveI := hX.isProbabilityMeasure
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxe : Real.exp (Real.exp 1) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1024 : 1024 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hΛ1 := one_le_log_log_of_exp_exp_le hxe
  have hΛx := sixteen_mul_log_log_le hx1024
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hΛx ⊢
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Λ ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [hr]
    exact Real.one_le_rpow hΛ1 (by norm_num)
  have hr0 : 0 < r := by linarith
  have hr4 : r ^ 4 = Λ := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hΛ0]
    norm_num
  have hrinv : Λ ^ (-(1 / 4 : ℝ)) = r⁻¹ := by
    rw [hr, Real.rpow_neg hΛ0]
  rw [hrinv]
  have h4r : 0 ≤ 4 * r ^ 2 := by positivity
  have hr2x : 4 * r ^ 2 ≤ Real.sqrt x := by
    rw [Real.le_sqrt h4r hx0.le]
    calc (4 * r ^ 2) ^ 2 = 16 * r ^ 4 := by ring
      _ = 16 * Λ := by rw [hr4]
      _ ≤ x := hΛx
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊r⌋₊ := ⟨_, rfl⟩
  have hMr : (M : ℝ) ≤ r := by
    rw [hM]
    exact Nat.floor_le hr0.le
  have hrM : r < (M : ℝ) + 1 := by
    rw [hM]
    exact Nat.lt_floor_add_one r
  have hM2 : ∀ m : ℕ, m ≤ M → ((m : ℝ) + 1) ^ 2 ≤ Real.sqrt x := fun m hm => by
    have hm' : (m : ℝ) ≤ M := by exact_mod_cast hm
    calc ((m : ℝ) + 1) ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = 4 * r ^ 2 := by ring
      _ ≤ Real.sqrt x := hr2x
  have hint := integrable_norm_sum_squarefreeExtension_mul hX (μ := μ)
  -- below the blocks
  have htail : (∫ ω, ‖∑ n ∈ Finset.Ioc 0 ⌊x / ((M : ℝ) + 1) ^ 2⌋₊,
      squarefreeExtension (fun p => X p ω) n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ)
        ≤ Real.sqrt x / ((M : ℝ) + 1) := by
    have hM10 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    calc _ ≤ Real.sqrt (Finset.Ioc 0 ⌊x / ((M : ℝ) + 1) ^ 2⌋₊).card :=
          integral_norm_sum_mul_le_sqrt_card hX _ (fun n hn => (Finset.mem_Ioc.1 hn).1.ne')
            (fun n => ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)) (fun n _ => by
              show ‖((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ≤ 1
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
              exact (Int.fract_lt_one _).le)
      _ ≤ Real.sqrt (x / ((M : ℝ) + 1) ^ 2) := by
          rw [Nat.card_Ioc, Nat.sub_zero]
          exact Real.sqrt_le_sqrt (Nat.floor_le (div_nonneg hx0.le (sq_nonneg _)))
      _ = Real.sqrt x / ((M : ℝ) + 1) := by
          rw [Real.sqrt_div hx0.le, Real.sqrt_sq hM10.le]
  -- the blocks
  have hblock : ∀ j ∈ Finset.range M,
      (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊ ⌊x / ((j : ℝ) + 1) ^ 2⌋₊,
        squarefreeExtension (fun p => X p ω) n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ)
        ≤ K * (Real.sqrt x * (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ * r⁻¹) + 4 := by
    intro j hj
    have hT := H X μ hX x (j + 1) hx₁ (Nat.le_add_left 1 j) (hM2 (j + 1) (Finset.mem_range.1 hj))
    have e : ((j + 1 : ℕ) : ℝ) ^ 2 = ((j : ℝ) + 1) ^ 2 := by simp
    have hj0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have e2 : ((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
        = ((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) := by
      rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hj0, Real.rpow_one]
    rw [e, e2, ← hΛ, ← hr] at hT
    calc _ ≤ K * (Real.sqrt x / (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) * r)) + 4 := hT
      _ = K * (Real.sqrt x * (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ * r⁻¹) + 4 := by ring
  have hsumZ : ∑ j ∈ Finset.range M, (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ ≤ Z := by
    have h1 : ∑ n ∈ Finset.range (M + 1), ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹
        = ∑ j ∈ Finset.range M, (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹
          + (((0 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ :=
      Finset.sum_range_succ' (fun n : ℕ => ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹) M
    have h2 : ∑ n ∈ Finset.range (M + 1), ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ ≤ Z := by
      rw [hZ]
      exact hZs.sum_le_tsum _ fun n _ => inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have h3 : (0 : ℝ) ≤ (((0 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ :=
      inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
    linarith
  have hsumeq : ∑ j ∈ Finset.range M,
        (K * (Real.sqrt x * (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ * r⁻¹) + 4)
      = K * Real.sqrt x * r⁻¹ * ∑ j ∈ Finset.range M, (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹
        + 4 * M := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have hintB : ∀ j ∈ Finset.range M, Integrable (fun ω =>
      ‖∑ n ∈ Finset.Ioc ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊ ⌊x / ((j : ℝ) + 1) ^ 2⌋₊,
        squarefreeExtension (fun p => X p ω) n
          * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖) μ := fun j _ => hint _ _
  have hintT := hint (Finset.Ioc 0 ⌊x / ((M : ℝ) + 1) ^ 2⌋₊)
    (fun n => ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ))
  have hintS := integrable_finsetSum (Finset.range M) hintB
  calc (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      = (∫ ω, ‖∑ n ∈ Finset.Ioc 0 ⌊x / ((M : ℝ) + 1) ^ 2⌋₊,
            squarefreeExtension (fun p => X p ω) n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)
          + ∑ j ∈ Finset.range M, ∑ n ∈ Finset.Ioc ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊
              ⌊x / ((j : ℝ) + 1) ^ 2⌋₊, squarefreeExtension (fun p => X p ω) n
                * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ) / Real.sqrt x := by
        rw [← integral_div]
        congr 1
        funext ω
        rw [fracPartSum_eq_div _ hx0.le M ω, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsx]
    _ ≤ ((∫ ω, ‖∑ n ∈ Finset.Ioc 0 ⌊x / ((M : ℝ) + 1) ^ 2⌋₊,
            squarefreeExtension (fun p => X p ω) n
              * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ)
          + ∑ j ∈ Finset.range M, ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x / (((j + 1 : ℕ) : ℝ) + 1) ^ 2⌋₊
              ⌊x / ((j : ℝ) + 1) ^ 2⌋₊, squarefreeExtension (fun p => X p ω) n
                * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ)‖ ∂μ) / Real.sqrt x := by
        refine div_le_div_of_nonneg_right ?_ hsx.le
        rw [← integral_finsetSum (Finset.range M) hintB, ← integral_add hintT hintS]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
          (hintT.add hintS) ?_
        filter_upwards with ω
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (Real.sqrt x / ((M : ℝ) + 1) + ∑ j ∈ Finset.range M,
          (K * (Real.sqrt x * (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹ * r⁻¹) + 4)) / Real.sqrt x :=
        div_le_div_of_nonneg_right (add_le_add htail (Finset.sum_le_sum hblock)) hsx.le
    _ ≤ (K * Z + 5) * r⁻¹ := by
        rw [hsumeq, div_le_iff₀ hsx]
        have ha : Real.sqrt x / ((M : ℝ) + 1) ≤ r⁻¹ * Real.sqrt x := by
          calc Real.sqrt x / ((M : ℝ) + 1) ≤ Real.sqrt x / r :=
                div_le_div_of_nonneg_left hsx.le hr0 hrM.le
            _ = r⁻¹ * Real.sqrt x := by ring
        have hb : K * Real.sqrt x * r⁻¹
              * ∑ j ∈ Finset.range M, (((j + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹
            ≤ K * Real.sqrt x * r⁻¹ * Z :=
          mul_le_mul_of_nonneg_left hsumZ
            (mul_nonneg (mul_nonneg hK.le hsx.le) (inv_nonneg.2 hr0.le))
        have hc : (M : ℝ) ≤ r⁻¹ * Real.sqrt x := by
          have hrr : r * r ≤ Real.sqrt x := by nlinarith [hr2x, sq_nonneg r]
          calc (M : ℝ) ≤ r := hMr
            _ = r⁻¹ * (r * r) := by rw [← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul]
            _ ≤ r⁻¹ * Real.sqrt x := mul_le_mul_of_nonneg_left hrr (inv_nonneg.2 hr0.le)
        linarith

/-- **Proposition 3.2 of the paper for `0 ≤ q ≤ ½`.**  There are `C` and `x₀` such that for
every Rademacher `X`, every `0 ≤ q ≤ ½` and every `x ≥ x₀`,
`E|R(x)|^{2q} ≤ C·(log log x)^{-q/2}`: Jensen from `RMF.exists_integral_norm_fracPartSum_le`. -/
theorem exists_integral_rpow_norm_fracPartSum_le_smallQ :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 / 2 →
        (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
          ≤ C * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨C, x₀, hC, H⟩ := exists_integral_norm_fracPartSum_le (Ω := Ω)
  refine ⟨max C 1, max x₀ (Real.exp (Real.exp 1)), lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro X μ hX x q hx hq0 hq2
  haveI := hX.isProbabilityMeasure
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hΛ0 : 0 ≤ Real.log (Real.log x) := by
    have := one_le_log_log_of_exp_exp_le hxe
    linarith
  have h1 := H X μ hX x (le_trans (le_max_left _ _) hx)
  have hint : Integrable (fun ω =>
      ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖) μ :=
    (integrable_rpow_norm_fracPartSum hX x (by norm_num : (0 : ℝ) ≤ 1)).congr
      (Filter.Eventually.of_forall fun ω => Real.rpow_one _)
  have hJ := integral_rpow_le_rpow_of_integral_le (by linarith : (0 : ℝ) ≤ 2 * q)
    (by linarith : 2 * q ≤ 1) (Filter.Eventually.of_forall fun ω => norm_nonneg _) hint h1
  calc (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (C * Real.log (Real.log x) ^ (-(1 / 4 : ℝ))) ^ (2 * q) := hJ
    _ = C ^ (2 * q) * Real.log (Real.log x) ^ (-(q / 2)) := by
        rw [Real.mul_rpow hC.le (Real.rpow_nonneg hΛ0 _), ← Real.rpow_mul hΛ0,
          show -(1 / 4 : ℝ) * (2 * q) = -(q / 2) by ring]
    _ ≤ max C 1 * Real.log (Real.log x) ^ (-(q / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hΛ0 _)
        calc C ^ (2 * q) ≤ (max C 1) ^ (2 * q) :=
              Real.rpow_le_rpow hC.le (le_max_left _ _) (by linarith)
          _ ≤ (max C 1) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) (by linarith)
          _ = max C 1 := Real.rpow_one _

/-- **The uniform upper bound below `q = ½`, for the extended sum** (Theorem 1.1, upper
bound, for `0 < q ≤ ½`).  There are `C` and `x₀` such that, for every Rademacher `X`, every
`0 < q ≤ ½` and every `x ≥ x₀`,

`E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≤ C·((log log x)⁻¹ + (1 - 2q))⁻¹·(log log x)^{-q/2}`,

the bound of its weighted twin
`RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ_uniform`.  Through
`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le`, from that twin for `S(x)` and
`RMF.exists_integral_rpow_norm_fracPartSum_le_smallQ` for `R(x)`, which is absorbed because
`((log log x)⁻¹ + (1 - 2q))⁻¹ ≥ ½`. -/
theorem exists_const_integral_rpow_normalisedSum_compMultExtension_le_smallQ_uniform :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ≤ C * (((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
                * (Real.log (Real.log x)) ^ (-(q / 2))) := by
  obtain ⟨C₁, x₁, hC₁, H₁⟩ :=
    exists_const_integral_rpow_weightedRademacherSum_le_smallQ_uniform (Ω := Ω)
  obtain ⟨C₂, x₂, hC₂, H₂⟩ := exists_integral_rpow_norm_fracPartSum_le_smallQ (Ω := Ω)
  refine ⟨2 * C₁ + 4 * C₂, max (max x₁ x₂) (Real.exp (Real.exp 1)), by linarith, ?_⟩
  intro X μ hX x q hx hq0 hq2
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (Real.exp_pos 1).le) hxe
  have hΛ1 := one_le_log_log_of_exp_exp_le hxe
  have hS := H₁ X μ hX x q hx₁ hq0 hq2
  have hR := H₂ X μ hX x q hx₂ hq0.le hq2
  have hcmp := integral_rpow_norm_normalisedSum_compMultExtension_le hX hx1 hq0.le
    (by linarith : q ≤ 1)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hS hR ⊢
  have hΛ0 : 0 < Λ := by linarith
  have hP0 : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  have hinv1 : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1
  have hA0 : 0 < Λ⁻¹ + (1 - 2 * q) := by
    have := inv_pos.2 hΛ0
    linarith
  have hA : (2 : ℝ)⁻¹ ≤ (Λ⁻¹ + (1 - 2 * q))⁻¹ := inv_anti₀ hA0 (by linarith)
  have hAP : (2 : ℝ)⁻¹ * Λ ^ (-(q / 2)) ≤ (Λ⁻¹ + (1 - 2 * q))⁻¹ * Λ ^ (-(q / 2)) :=
    mul_le_mul_of_nonneg_right hA hP0
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ 2 * (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        + 2 * (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ) := hcmp
    _ ≤ 2 * (C₁ * ((Λ⁻¹ + (1 - 2 * q))⁻¹ * Λ ^ (-(q / 2)))) + 2 * (C₂ * Λ ^ (-(q / 2))) := by
        linarith
    _ ≤ (2 * C₁ + 4 * C₂) * ((Λ⁻¹ + (1 - 2 * q))⁻¹ * Λ ^ (-(q / 2))) := by
        nlinarith [mul_le_mul_of_nonneg_left hAP hC₂.le]

end RMF
