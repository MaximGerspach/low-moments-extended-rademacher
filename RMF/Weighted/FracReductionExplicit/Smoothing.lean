/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracReductionExplicit.Split

/-!
# The remainder's reduction, II: smoothing over short intervals

The large rough factors of `RMF.integral_norm_fracPartSum_le_lowErr_add`,
`∑_{m∈S} m⁻¹|H_y(x/m)|²`, are averaged over `t ∈ [m, m(1+η)]` with the split
`‖a‖² ≤ (1+ε)‖b‖² + (1+1/ε)‖a-b‖²`, as for the weighted sum
(`RMF.sum_fracRoughTerm_le_setIntegral_eps`).

The work is in the error.  `ψ(v) = {√v}/√v` jumps at the squares, so `H_y(x/m) - H_y(x/t)`
has two parts (`RMF.fracKernel_sub_sq_le`): a smooth one, `|ψ(v) - ψ(v')| ≤ η/2` when no square
`s² ≥ 4` lies in `(v', v]`, and the jumps, where only `|ψ(v) - ψ(v')|² ≤ 1/v'` is available.  In
mean square (`RMF.integral_normSq_smoothFracSum_sub_le`) the jumps are counted by the `k` with
`x/(1+η) < mks² ≤ x` for some `s ≥ 2`; summed over the rough `m`, the pairs `(m, k)` inject into
`n = mk` (`RMF.rough_smooth_unique`), and the `n ≤ x` with a multiple `ns²` in `(x/(1+η), x]`
number at most `ηx/(1+η) + √x` (`RMF.sum_card_fracJump_le`).  The expected error is
`RMF.fracSmoothErr x η ε = (1+1/ε)((η²/4)(1 + log x)² + η + (1+η)/√x)`
(`RMF.integral_fracSmoothingError_le`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The averaging step at one `ω` -/

omit [MeasurableSpace Ω] in
/-- `t ↦ |H_y(x/t)|²` is interval integrable: measurable, and at most `⌊x/r⌋²` on `[r, s]`. -/
lemma intervalIntegrable_normSq_smoothFracSum {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x r s : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hrs : r ≤ s) :
    IntervalIntegrable (fun t => ‖smoothFracSum f y (x / t) ω‖ ^ 2) volume r s := by
  have hmeas : Measurable fun t : ℝ => ‖smoothFracSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothFracSum f y (x / t) ω :=
      (measurable_smoothFracSum_arg f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrs]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := ((⌊x / r⌋₊ : ℝ)) ^ 2)
    (measure_Ioc_lt_top).ne hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hfl : (⌊x / t⌋₊ : ℝ) ≤ (⌊x / r⌋₊ : ℝ) := by
    have : x / t ≤ x / r := div_le_div_of_nonneg_left hx hr (le_of_lt ht.1)
    exact_mod_cast Nat.floor_le_floor this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (norm_smoothFracSum_le_of_bound hb y _) hfl) 2

omit [MeasurableSpace Ω] in
/-- `t ↦ |H_y(x/r) - H_y(x/t)|²` is interval integrable on `[r, s]`. -/
lemma intervalIntegrable_normSq_smoothFracSum_sub {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x r s : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun t => ‖smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω‖ ^ 2) volume r s := by
  have hmeas : Measurable fun t : ℝ =>
      ‖smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothFracSum f y (x / t) ω :=
      (measurable_smoothFracSum_arg f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrs]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := (2 * (⌊x / r⌋₊ : ℝ)) ^ 2)
    (measure_Ioc_lt_top).ne hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hfl : (⌊x / t⌋₊ : ℝ) ≤ (⌊x / r⌋₊ : ℝ) := by
    have hd : x / t ≤ x / r := div_le_div_of_nonneg_left hx hr (le_of_lt ht.1)
    exact_mod_cast Nat.floor_le_floor hd
  have h1 := norm_smoothFracSum_le_of_bound hb y (x / r)
  have h2 := le_trans (norm_smoothFracSum_le_of_bound hb y (x / t)) hfl
  have hsub : ‖smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω‖
      ≤ 2 * (⌊x / r⌋₊ : ℝ) := le_trans (norm_sub_le _ _) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hsub 2

omit [MeasurableSpace Ω] in
/-- **The averaging step with a `(1+ε)` split.**  At an `ω` where every value has norm at most
one, `∑_{r∈S} r⁻¹|H_y(x/r)|²` is at most `(1+ε)/η` times a single integral against a bound `b` on
the weighted count of the intervals `[r, r(1+η)]` containing `t`, plus `(1+1/ε)/(2η)` times the
smoothing errors: `RMF.sum_weightedRoughTerm_le_setIntegral_eps` with `H_y` in place of `A_y`. -/
theorem sum_fracRoughTerm_le_setIntegral_eps {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x η ε : ℝ} (hx : 0 ≤ x) (hη : 0 < η) (hε : 0 < ε)
    {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) {T : Set ℝ} (hTm : MeasurableSet T) {b : ℝ → ℝ}
    (hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ T)
    (hb : ∀ t ∈ T, ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hint : ∀ r ∈ S, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
            (fun t => ‖smoothFracSum f y (x / t) ω‖ ^ 2) t) T volume)
    (hintT : IntegrableOn
      (fun t => ‖smoothFracSum f y (x / t) ω‖ ^ 2 * b t) T volume) :
    ∑ r ∈ S, fracRoughTerm f y x ω r
      ≤ ((1 + ε) / η) * (∫ t in T, ‖smoothFracSum f y (x / t) ω‖ ^ 2 * b t)
        + ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 := by
  set G : ℝ → ℂ := fun u => smoothFracSum f y u ω with hGdef
  have hterm : ∀ r ∈ S, fracRoughTerm f y x ω r
      = (fun t => ‖G (x / t)‖ ^ 2) (r : ℝ) / (r : ℝ) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hS r hr
    rw [fracRoughTerm]
    field_simp
    rfl
  rw [Finset.sum_congr rfl hterm]
  have hexch := sum_smul_setIntegral_le
    (g := fun t => ‖G (x / t)‖ ^ 2) (b := b) (S := S)
    (I := fun r => Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)))
    (c := fun r => (((r : ℝ)) ^ 2)⁻¹)
    (fun t => by positivity) hsub (fun r _ => measurableSet_Icc) hint hintT hb hTm
  refine le_trans (sum_div_le_of_average_const (K := 1 + ε) (g := fun t => ‖G (x / t)‖ ^ 2)
    (e := fun r => (1 + 1 / ε) * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G (x / r) - G (x / t)‖ ^ 2))
    hη (by positivity) hS (fun r hr => ?_) hexch) (le_of_eq ?_)
  · have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS r hr
    have hle : (r : ℝ) ≤ (r : ℝ) * (1 + η) := by nlinarith
    have hkey := normSq_average_bound_eps G x hr0 hη hε
      (intervalIntegrable_normSq_smoothFracSum hbnd y hx hr0
        (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
      (intervalIntegrable_normSq_smoothFracSum_sub hbnd y hx hr0
        (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
    rw [intervalIntegral_eq_setIntegral_Icc hle, intervalIntegral_eq_setIntegral_Icc hle]
      at hkey
    exact hkey
  · congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
    ring

/-! ### The kernel across a short multiplicative step -/

/-- `ψ(v) = (√v - ⌊√v⌋)/√v` for `v ≥ 1`. -/
lemma fracKernel_eq_sub_floor {v : ℝ} (hv : 1 ≤ v) :
    fracKernel v = (Real.sqrt v - ⌊Real.sqrt v⌋₊) / Real.sqrt v := by
  rw [fracKernel, if_pos hv, fract_eq_sub_natCast (Nat.floor_le (Real.sqrt_nonneg _))
    (Nat.lt_floor_add_one _)]

/-- `(p - q)² ≤ max(p², q²)` for `p, q ≥ 0`, in the form used below. -/
lemma sub_sq_le_of_nonneg {p q B : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpB : p ^ 2 ≤ B)
    (hqB : q ^ 2 ≤ B) : (p - q) ^ 2 ≤ B := by
  rcases le_total p q with h | h
  · have h1 : (p - q) ^ 2 = (q - p) ^ 2 := by ring
    rw [h1]
    exact le_trans (pow_le_pow_left₀ (by linarith) (by linarith) 2) hqB
  · exact le_trans (pow_le_pow_left₀ (by linarith) (by linarith) 2) hpB

/-- **The kernel across a short multiplicative step.**  For `0 < v' ≤ v ≤ (1+η)v'`, `η ≥ 0`:
either `(ψ(v) - ψ(v'))² ≤ η²/4`, or a square `s² ≥ 4` lies in `(v', v]` and
`(ψ(v) - ψ(v'))² ≤ 1/v'`.  Between consecutive squares `ψ(v) = 1 - n/√v`, which moves by at most
`√v/√v' - 1 ≤ η/2`; across one, both values are at most `1/√v'`. -/
lemma fracKernel_sub_sq_le {v v' η : ℝ} (hv' : 0 < v') (hle : v' ≤ v)
    (hvη : v ≤ (1 + η) * v') (hη : 0 ≤ η) :
    (fracKernel v - fracKernel v') ^ 2 ≤ η ^ 2 / 4
      ∨ ((∃ s : ℕ, 2 ≤ s ∧ v' < (s : ℝ) ^ 2 ∧ (s : ℝ) ^ 2 ≤ v)
        ∧ (fracKernel v - fracKernel v') ^ 2 ≤ v'⁻¹) := by
  have hv : 0 < v := lt_of_lt_of_le hv' hle
  -- the general bound, valid in every case
  have hgen : (fracKernel v - fracKernel v') ^ 2 ≤ v'⁻¹ :=
    sub_sq_le_of_nonneg (fracKernel_nonneg v) (fracKernel_nonneg v')
      ((fracKernel_sq_le_inv hv).trans (inv_anti₀ hv' hle)) (fracKernel_sq_le_inv hv')
  set a := Real.sqrt v with ha
  set b := Real.sqrt v' with hb
  have hb0 : 0 < b := Real.sqrt_pos.2 hv'
  have ha0 : 0 < a := Real.sqrt_pos.2 hv
  have hba : b ≤ a := Real.sqrt_le_sqrt hle
  have hsa : a ^ 2 = v := Real.sq_sqrt hv.le
  have hsb : b ^ 2 = v' := Real.sq_sqrt hv'.le
  -- `a ≤ (1 + η/2) b`
  have hab : a ≤ (1 + η / 2) * b := by
    have h1 : a ^ 2 ≤ ((1 + η / 2) * b) ^ 2 := by
      rw [hsa, mul_pow, hsb]
      have : (1 + η) ≤ (1 + η / 2) ^ 2 := by nlinarith [sq_nonneg η]
      nlinarith [hv'.le]
    exact (pow_le_pow_iff_left₀ ha0.le (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 h1
  set n := ⌊b⌋₊ with hn
  set N := ⌊a⌋₊ with hN
  have hnb : (n : ℝ) ≤ b := Nat.floor_le hb0.le
  have hbn : b < (n : ℝ) + 1 := Nat.lt_floor_add_one b
  have hNa : (N : ℝ) ≤ a := Nat.floor_le ha0.le
  have haN : a < (N : ℝ) + 1 := Nat.lt_floor_add_one a
  have hnN : n ≤ N := Nat.floor_le_floor hba
  by_cases hv1 : v < 1
  · -- below `1` both values vanish
    left
    rw [fracKernel_eq_zero_of_le_one hv1.le, fracKernel_eq_zero_of_le_one (by linarith)]
    have : (0 : ℝ) ≤ η ^ 2 / 4 := by positivity
    simpa using this
  have hv1' : 1 ≤ v := not_lt.1 hv1
  have ha1 : 1 ≤ a := by
    rw [ha, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hv1'
  have hψv : fracKernel v = (a - N) / a := fracKernel_eq_sub_floor hv1'
  rcases Nat.eq_or_lt_of_le hnN with heq | hlt
  · -- the same floor: no square in between
    have hN1 : 1 ≤ N := by
      by_contra hcon
      have h0 : N = 0 := by omega
      rw [h0, Nat.cast_zero, zero_add] at haN
      linarith
    have hn1 : (1 : ℝ) ≤ n := by rw [heq]; exact_mod_cast hN1
    have hv'1 : 1 ≤ v' := by
      have : (1 : ℝ) ≤ b := le_trans hn1 hnb
      rw [← hsb]
      nlinarith
    have hψv' : fracKernel v' = (b - n) / b := fracKernel_eq_sub_floor hv'1
    left
    rw [hψv, hψv', ← heq]
    have hdiff : (a - n) / a - (b - n) / b = n * (a - b) / (a * b) := by
      field_simp
      ring
    rw [hdiff]
    have hnum0 : 0 ≤ (n : ℝ) * (a - b) := mul_nonneg (by positivity) (by linarith)
    have hden : 0 < a * b := mul_pos ha0 hb0
    have hd0 : 0 ≤ (n : ℝ) * (a - b) / (a * b) := div_nonneg hnum0 hden.le
    have hd1 : (n : ℝ) * (a - b) / (a * b) ≤ η / 2 := by
      rw [div_le_iff₀ hden]
      have h1 : (n : ℝ) * (a - b) ≤ b * (a - b) := mul_le_mul_of_nonneg_right hnb (by linarith)
      have h2 : b * (a - b) ≤ b * (η / 2 * b) := mul_le_mul_of_nonneg_left (by linarith) hb0.le
      have h3 : b * (η / 2 * b) ≤ η / 2 * (a * b) := by nlinarith
      linarith
    calc ((n : ℝ) * (a - b) / (a * b)) ^ 2 ≤ (η / 2) ^ 2 := pow_le_pow_left₀ hd0 hd1 2
      _ = η ^ 2 / 4 := by ring
  · -- a larger floor at `v`
    by_cases hn0 : n = 0
    · have hb1 : b < 1 := by
        have := hbn
        rw [hn0, Nat.cast_zero, zero_add] at this
        exact this
      have hv'1 : v' ≤ 1 := by
        rw [← hsb]
        nlinarith
      have hψv' : fracKernel v' = 0 := fracKernel_eq_zero_of_le_one hv'1
      by_cases hN2 : 2 ≤ N
      · right
        refine ⟨⟨2, le_rfl, ?_, ?_⟩, hgen⟩
        · have : v' < 1 := by rw [← hsb]; nlinarith
          norm_num
          linarith
        · have h2 : (2 : ℝ) ≤ a := le_trans (by exact_mod_cast hN2) hNa
          rw [← hsa]
          push_cast
          nlinarith
      · -- `N = 1`: `1 ≤ a < 2`, and `a ≤ (1 + η/2)b < 1 + η/2`
        have hN1 : N = 1 := by omega
        left
        rw [hψv, hψv', hN1, Nat.cast_one, sub_zero]
        have hd0 : 0 ≤ (a - 1) / a := div_nonneg (by linarith) ha0.le
        have hd1 : (a - 1) / a ≤ η / 2 := by
          rw [div_le_iff₀ ha0]
          have : a < 1 + η / 2 := by nlinarith
          nlinarith
        calc ((a - 1) / a) ^ 2 ≤ (η / 2) ^ 2 := pow_le_pow_left₀ hd0 hd1 2
          _ = η ^ 2 / 4 := by ring
    · -- `s = n + 1 ≥ 2` with `v' < s² ≤ v`
      right
      refine ⟨⟨n + 1, by omega, ?_, ?_⟩, hgen⟩
      · rw [← hsb]
        push_cast
        nlinarith
      · have h1 : ((n + 1 : ℕ) : ℝ) ≤ a := le_trans (by exact_mod_cast hlt) hNa
        rw [← hsa]
        exact pow_le_pow_left₀ (by positivity) h1 2

/-! ### The mean square of the smoothing difference -/

open Classical in
/-- **The smoothing difference in mean square.**  For `x, r ≥ 1`, `η ≥ 0` and
`r ≤ t ≤ r(1+η)`, `E|H_y(x/r) - H_y(x/t)|² ≤ (η²/4)(1 + log x) + ((1+η)r/x)·J`, `J` the number of
smooth `k ≤ x/r` with `x/(1+η) < rks² ≤ x` for some `s ≥ 2`.  Orthogonality leaves
`∑_{k ≤ x/r} k⁻¹(ψ(x/(rk)) - ψ(x/(tk)))²`; each term is `RMF.fracKernel_sub_sq_le` at
`v = x/(rk)`, `v' = x/(tk)`, the jump costing `k⁻¹/v' = t/x ≤ (1+η)r/x`. -/
theorem integral_normSq_smoothFracSum_sub_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r t η : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r)
    (hη : 0 ≤ η) (hrt : r ≤ t) (htr : t ≤ r * (1 + η)) :
    (∫ ω, ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
        - smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2 ∂μ)
      ≤ η ^ 2 / 4 * (1 + Real.log x) + (1 + η) * r / x
          * (({k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧
              ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < r * k * (s : ℝ) ^ 2
                ∧ r * k * (s : ℝ) ^ 2 ≤ x}).card : ℝ) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < r := by linarith
  have ht0 : 0 < t := by linarith
  set K : Finset ℕ := {k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1)} with hKdef
  have hK0 : ∀ k ∈ K, k ≠ 0 := fun k hk => by
    have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    omega
  have hNt : ⌊x / t⌋₊ ≤ ⌊x / r⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left hx0.le hr0 hrt)
  set c : ℕ → ℂ := fun k =>
    (((Real.sqrt k)⁻¹ * (fracKernel (x / r / k) - fracKernel (x / t / k)) : ℝ) : ℂ) with hcdef
  have hdiff : ∀ ω, smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω
      = ∑ k ∈ K, f ω k * c k := by
    intro ω
    rw [smoothFracSum_eq_sum_Icc f y hNt ω, smoothFracSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hcdef]
    push_cast
    ring
  simp_rw [hdiff]
  refine le_trans (integral_normSq_sum_mul_le_sum_normSq hRa K hK0 c) ?_
  -- each term
  set J : ℕ → Prop := fun k => ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < r * k * (s : ℝ) ^ 2
    ∧ r * k * (s : ℝ) ^ 2 ≤ x with hJdef
  have hterm : ∀ k ∈ K, ‖c k‖ ^ 2
      ≤ (k : ℝ)⁻¹ * (η ^ 2 / 4) + (if J k then (1 + η) * r / x else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hc : ‖c k‖ ^ 2 = (k : ℝ)⁻¹ * (fracKernel (x / r / k) - fracKernel (x / t / k)) ^ 2 := by
      simp only [hcdef]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt hk0.le]
    rw [hc]
    have hv' : 0 < x / t / k := div_pos (div_pos hx0 ht0) hk0
    have hle : x / t / k ≤ x / r / k :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hx0.le hr0 hrt) hk0.le
    have hvη : x / r / k ≤ (1 + η) * (x / t / k) := by
      rw [div_div, div_div, ← mul_div_assoc, div_le_div_iff₀ (mul_pos hr0 hk0) (mul_pos ht0 hk0)]
      have : t * k ≤ (1 + η) * (r * k) := by nlinarith
      nlinarith
    have hif0 : (0 : ℝ) ≤ (if J k then (1 + η) * r / x else 0) := by
      split_ifs
      · positivity
      · exact le_rfl
    rcases fracKernel_sub_sq_le hv' hle hvη hη with h | ⟨⟨s, hs2, hs1, hs2'⟩, h⟩
    · have : (k : ℝ)⁻¹ * (fracKernel (x / r / k) - fracKernel (x / t / k)) ^ 2
          ≤ (k : ℝ)⁻¹ * (η ^ 2 / 4) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hk0.le)
      linarith
    · have hJ : J k := by
        refine ⟨s, hs2, ?_, ?_⟩
        · -- `x/(tk) < s²` and `t ≤ r(1+η)`
          have h1 : x < t * k * (s : ℝ) ^ 2 := by
            rw [div_div, div_lt_iff₀ (mul_pos ht0 hk0)] at hs1
            linarith
          have h2 : t * k * (s : ℝ) ^ 2 ≤ r * (1 + η) * k * (s : ℝ) ^ 2 := by
            have := mul_le_mul_of_nonneg_right htr (by positivity : (0 : ℝ) ≤ k * (s : ℝ) ^ 2)
            nlinarith
          rw [div_lt_iff₀ (by linarith)]
          nlinarith
        · rw [div_div, le_div_iff₀ (mul_pos hr0 hk0)] at hs2'
          linarith
      rw [if_pos hJ]
      have h1 : (k : ℝ)⁻¹ * (fracKernel (x / r / k) - fracKernel (x / t / k)) ^ 2
          ≤ (k : ℝ)⁻¹ * (x / t / k)⁻¹ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hk0.le)
      have h2 : (k : ℝ)⁻¹ * (x / t / k)⁻¹ = t / x := by
        field_simp
      have h3 : t / x ≤ (1 + η) * r / x := by
        rw [div_le_div_iff_of_pos_right hx0]
        linarith
      have h4 : (0 : ℝ) ≤ (k : ℝ)⁻¹ * (η ^ 2 / 4) := by positivity
      linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  -- the harmonic mass of `K`
  have hH : ∑ k ∈ K, (k : ℝ)⁻¹ ≤ 1 + Real.log x := by
    have hsub : K ⊆ Finset.Icc 1 ⌊x / r⌋₊ := Finset.filter_subset _ _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity) ?_
    have hh := harmonic_le_one_add_log ⌊x / r⌋₊
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    refine le_trans hh ?_
    rcases Nat.eq_zero_or_pos ⌊x / r⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg hx]
    · have h1 : ((⌊x / r⌋₊ : ℕ) : ℝ) ≤ x :=
        le_trans (Nat.floor_le (div_pos hx0 hr0).le) (div_le_self hx0.le hr)
      linarith [Real.log_le_log (by exact_mod_cast hpos) h1]
  have hfil : K.filter J = {k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧
      ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < r * k * (s : ℝ) ^ 2 ∧ r * k * (s : ℝ) ^ 2 ≤ x} := by
    rw [hKdef, Finset.filter_filter]
  rw [hfil]
  have hη4 : 0 ≤ η ^ 2 / 4 := by positivity
  have hcard0 : (0 : ℝ) ≤ (({k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧
      ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < r * k * (s : ℝ) ^ 2
        ∧ r * k * (s : ℝ) ^ 2 ≤ x}).card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hH hη4]

/-! ### The Tonelli swap -/

/-- `(ω, t) ↦ H_y(x/t)(ω)` is jointly measurable: `RMF.measurable_uncurry_smoothFracSum` at
`w = x/t`. -/
lemma measurable_smoothFracSum_div {f : Ω → ArithmeticFunction ℂ}
    (hf : ∀ n, Measurable fun ω => f ω n) (y : ℕ) (x : ℝ) :
    Measurable fun p : Ω × ℝ => smoothFracSum f y (x / p.2) p.1 := by
  set G : (Ω × ℝ) × ℕ → ℂ := fun q =>
    ∑ k ∈ {k ∈ Finset.Icc 1 q.2 | k ∈ Nat.smoothNumbers (y + 1)},
      f q.1.1 k / (Real.sqrt k : ℂ) * (fracKernel (x / q.1.2 / k) : ℂ) with hGdef
  have hG : Measurable G := by
    refine measurable_from_prod_countable_left fun n => ?_
    change Measurable fun z : Ω × ℝ =>
      ∑ k ∈ {k ∈ Finset.Icc 1 n | k ∈ Nat.smoothNumbers (y + 1)},
        f z.1 k / (Real.sqrt k : ℂ) * (fracKernel (x / z.2 / k) : ℂ)
    refine Finset.measurable_sum _ fun k _ => ?_
    refine (((hf k).comp measurable_fst).div_const _).mul ?_
    exact Complex.measurable_ofReal.comp
      (measurable_fracKernel.comp ((measurable_const.div measurable_snd).div_const _))
  have hcomp : (fun p : Ω × ℝ => smoothFracSum f y (x / p.2) p.1)
      = G ∘ fun p : Ω × ℝ => (p, ⌊x / p.2⌋₊) := by
    funext p
    rfl
  rw [hcomp]
  exact hG.comp (measurable_id.prodMk
    (Nat.measurable_floor.comp (measurable_const.div measurable_snd)))

/-- **The smoothing difference is product-integrable**: jointly measurable
(`RMF.measurable_uncurry_smoothFracSum`) and at most `(2⌊x/r⌋)²` on `Ω × (r, s]`. -/
theorem integrable_uncurry_normSq_smoothFracSum_sub {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x r s : ℝ}
    (hx : 0 ≤ x) (hr : 0 < r) :
    Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2)
      (μ.prod (volume.restrict (Set.Ioc r s))) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set N : ℕ := ⌊x / r⌋₊ with hNdef
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc r s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmeas : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ‖smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω‖ ^ 2) := by
    have h1 : Measurable fun p : Ω × ℝ => smoothFracSum f y (x / r) p.1 :=
      (measurable_smoothFracSum hRa.measurable_apply y (x / r)).comp measurable_fst
    have h2 : Measurable fun p : Ω × ℝ => smoothFracSum f y (x / p.2) p.1 :=
      measurable_smoothFracSum_div hRa.measurable_apply y x
    exact ((h1.sub h2).norm).pow_const 2
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖f ω n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hbddP : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Ioc r s))), ∀ n, ‖f p.1 n‖ ≤ 1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hbdd
  have hmemP : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Ioc r s))), p.2 ∈ Set.Ioc r s :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioc)
  have hbound : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Ioc r s))),
      ‖Function.uncurry (fun (ω : Ω) (t : ℝ) =>
        ‖smoothFracSum f y (x / r) ω - smoothFracSum f y (x / t) ω‖ ^ 2) p‖
        ≤ (2 * (N : ℝ)) ^ 2 := by
    filter_upwards [hbddP, hmemP] with p hb hp
    have hleN : ⌊x / p.2⌋₊ ≤ N :=
      Nat.floor_le_floor (div_le_div_of_nonneg_left hx hr (le_of_lt hp.1))
    have h1 : ‖smoothFracSum f y (x / r) p.1‖ ≤ (N : ℝ) :=
      norm_smoothFracSum_le_of_bound hb y (x / r)
    have h2 : ‖smoothFracSum f y (x / p.2) p.1‖ ≤ (N : ℝ) := by
      refine le_trans (norm_smoothFracSum_le_of_bound hb y (x / p.2)) ?_
      exact_mod_cast hleN
    have hsub : ‖smoothFracSum f y (x / r) p.1 - smoothFracSum f y (x / p.2) p.1‖
        ≤ 2 * (N : ℝ) := le_trans (norm_sub_le _ _) (by linarith)
    have hn0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
  exact (memLp_top_of_bound hmeas.aestronglyMeasurable ((2 * (N : ℝ)) ^ 2) hbound).integrable
    le_top

/-- **The expectation of the smoothing errors, from per-window bounds.**  If on each window
`t ∈ [r, r(1+η)]` the mean square of `G(x/r) - G(x/t)` is at most `B r`, and the difference is
jointly integrable, then `E∑_r (2∫‖G(x/r) - G(x/t)‖²)/r² ≤ ∑_r 2ηB(r)/r`:
`RMF.integral_sum_setIntegral_normSq_sub_le_of_integrable` with a general bound. -/
theorem integral_sum_setIntegral_normSq_sub_le_of_bound {μ : Measure Ω}
    [IsProbabilityMeasure μ] (G : Ω → ℝ → ℂ) {x η : ℝ} (hη : 0 < η)
    {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) (B : ℕ → ℝ)
    (hjoint : ∀ r ∈ S, Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ‖G ω (x / r) - G ω (x / t)‖ ^ 2)
        (μ.prod (volume.restrict (Set.Ioc (r : ℝ) ((r : ℝ) * (1 + η))))))
    (hpt : ∀ r ∈ S, ∀ t ∈ Set.Icc (r : ℝ) ((r : ℝ) * (1 + η)),
        (∫ ω, ‖G ω (x / r) - G ω (x / t)‖ ^ 2 ∂μ) ≤ B r) :
    (∫ ω, ∑ r ∈ S, (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖G ω (x / r) - G ω (x / t)‖ ^ 2)) / ((r : ℝ)) ^ 2 ∂μ)
      ≤ ∑ r ∈ S, 2 * η * B r / (r : ℝ) := by
  classical
  have hbridge : ∀ (g : ℝ → ℝ) (a b : ℝ), (∫ t in Set.Icc a b, g t) = ∫ t in Set.Ioc a b, g t := by
    intro g a b
    rw [← MeasureTheory.Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  have hint : ∀ r ∈ S, Integrable (fun ω => (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G ω (x / r) - G ω (x / t)‖ ^ 2)) / ((r : ℝ)) ^ 2) μ := by
    intro r hr
    simp_rw [hbridge]
    exact (((hjoint r hr).integral_prod_left).const_mul 2).div_const _
  rw [integral_finsetSum _ hint]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hS r hr
  have hlen : (r : ℝ) * (1 + η) - (r : ℝ) = (r : ℝ) * η := by ring
  have hvol : volume.real (Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η))) = (r : ℝ) * η := by
    rw [measureReal_def, Real.volume_Ioc, hlen,
      ENNReal.toReal_ofReal (mul_nonneg hr0.le hη.le)]
  have hshape : ∀ ω : Ω, (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G ω (x / r) - G ω (x / t)‖ ^ 2)) / ((r : ℝ)) ^ 2
      = (2 / ((r : ℝ)) ^ 2) * (∫ t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)),
          ‖G ω (x / r) - G ω (x / t)‖ ^ 2) := by
    intro ω
    rw [hbridge]
    ring
  simp_rw [hshape]
  rw [integral_const_mul, integral_integral_swap (hjoint r hr)]
  have hmono : (∫ t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        (∫ ω, ‖G ω (x / r) - G ω (x / t)‖ ^ 2 ∂μ))
      ≤ ∫ _t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)), B r := by
    refine setIntegral_mono_on ((hjoint r hr).integral_prod_right)
      (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc ?_
    intro t ht
    exact hpt r hr t ⟨ht.1.le, ht.2⟩
  rw [setIntegral_const, hvol, smul_eq_mul] at hmono
  have hc0 : (0 : ℝ) ≤ 2 / ((r : ℝ)) ^ 2 := by positivity
  calc (2 / ((r : ℝ)) ^ 2) * (∫ t in Set.Ioc ((r : ℝ)) ((r : ℝ) * (1 + η)),
          (∫ ω, ‖G ω (x / r) - G ω (x / t)‖ ^ 2 ∂μ))
      ≤ (2 / ((r : ℝ)) ^ 2) * ((r : ℝ) * η * B r) := mul_le_mul_of_nonneg_left hmono hc0
    _ = 2 * η * B r / (r : ℝ) := by field_simp

/-! ### Counting the jumps -/

/-- `∑_{2≤s≤S} 1/s² ≤ 1 - 1/S` for `S ≥ 1`. -/
lemma sum_Icc_two_inv_sq_le_aux (S : ℕ) (hS : 1 ≤ S) :
    ∑ s ∈ Finset.Icc 2 S, ((s : ℝ) ^ 2)⁻¹ ≤ 1 - 1 / (S : ℝ) := by
  induction S, hS using Nat.le_induction with
  | base => norm_num
  | succ S hS ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ S + 1)]
    have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
    have key : (((S + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / (S : ℝ) - 1 / ((S + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hS0.ne' (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `∑_{2≤s≤S} 1/s² ≤ 1`. -/
lemma sum_Icc_two_inv_sq_le_one (S : ℕ) : ∑ s ∈ Finset.Icc 2 S, ((s : ℝ) ^ 2)⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos S with h | h
  · subst h
    simp
  · have h1 := sum_Icc_two_inv_sq_le_aux S h
    have h2 : (0 : ℝ) ≤ 1 / (S : ℝ) := by positivity
    linarith

/-- `#(⌊A⌋, ⌊B⌋] ≤ B - A + 1` for `0 ≤ A ≤ B`. -/
lemma card_Ioc_floor_le {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).card : ℝ) ≤ B - A + 1 := by
  rw [Nat.card_Ioc]
  have hfl : ⌊A⌋₊ ≤ ⌊B⌋₊ := Nat.floor_le_floor hAB
  rw [Nat.cast_sub hfl]
  have h1 : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (le_trans hA hAB)
  have h2 : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
  linarith

open Classical in
/-- **Counting the jumps.**  For `S` a set of `y`-rough integers `≥ 1`, `x ≥ 0` and `η ≥ 0`,
the pairs `(r, k)`, `k ≤ x/r` smooth, with `x/(1+η) < rks² ≤ x` for some `s ≥ 2`, number at most
`ηx/(1+η) + √x`.  They inject into `n = rk` (`RMF.rough_smooth_unique`); for each `2 ≤ s ≤ √x`
the `n` with `ns² ∈ (x/(1+η), x]` lie in `(⌊x/((1+η)s²)⌋, ⌊x/s²⌋]`, of length
`ηx/((1+η)s²) + 1`, and `∑_{s≥2} 1/s² ≤ 1`. -/
theorem sum_card_fracJump_le {y : ℕ} {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r)
    (hS1 : ∀ r ∈ S, 1 ≤ r) {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    ∑ r ∈ S, (({k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧
        ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < (r : ℝ) * k * (s : ℝ) ^ 2
          ∧ (r : ℝ) * k * (s : ℝ) ^ 2 ≤ x}).card : ℝ)
      ≤ η / (1 + η) * x + Real.sqrt x := by
  classical
  have hη1 : (0 : ℝ) < 1 + η := by linarith
  set J : ℕ → Prop := fun n => ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < (n : ℝ) * (s : ℝ) ^ 2
    ∧ (n : ℝ) * (s : ℝ) ^ 2 ≤ x with hJdef
  set K : ℕ → Finset ℕ := fun r => {k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧
    ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < (r : ℝ) * k * (s : ℝ) ^ 2
      ∧ (r : ℝ) * k * (s : ℝ) ^ 2 ≤ x} with hKdef
  set T : Finset ℕ := {n ∈ Finset.Icc 1 ⌊x⌋₊ | J n} with hTdef
  -- the pairs inject into `T`
  have h1 : ∑ r ∈ S, ((K r).card : ℝ) ≤ (T.card : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.card_sigma]
    refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun p => p.1 * p.2) ?_ ?_)
    · rintro ⟨r, k⟩ hp
      rw [Finset.mem_coe, Finset.mem_sigma] at hp
      change r * k ∈ (T : Set ℕ)
      obtain ⟨hr, hk⟩ := hp
      obtain ⟨hkI, hks, s, hs2, hs1, hs2'⟩ := Finset.mem_filter.1 hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hkI).1
      have hr1 := hS1 r hr
      have hrk : ((r * k : ℕ) : ℝ) = (r : ℝ) * k := by push_cast; ring
      have hs1R : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ s := by exact_mod_cast hs2
        nlinarith
      have hrk0 : (0 : ℝ) ≤ (r : ℝ) * k := by positivity
      rw [Finset.mem_coe, hTdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hr1 hk1, ?_⟩, ⟨s, hs2, ?_, ?_⟩⟩
      · refine Nat.le_floor ?_
        rw [hrk]
        nlinarith
      · rw [hrk]
        exact hs1
      · rw [hrk]
        exact hs2'
    · rintro ⟨r, k⟩ hp ⟨r', k'⟩ hp' h
      rw [Finset.mem_coe, Finset.mem_sigma] at hp hp'
      have hks := (Finset.mem_filter.1 hp.2).2.1
      have hks' := (Finset.mem_filter.1 hp'.2).2.1
      simp only at h
      obtain ⟨h1, h2⟩ := rough_smooth_unique (hSr r hp.1) hks (hSr r' hp'.1) hks'
        (hS1 r hp.1) h
      subst h1
      subst h2
      rfl
  -- `T` is covered by `2 ≤ s ≤ √x`
  have h2 : (T.card : ℝ) ≤ ∑ s ∈ Finset.Icc 2 ⌊Real.sqrt x⌋₊,
      ((Finset.Ioc ⌊x / ((1 + η) * (s : ℝ) ^ 2)⌋₊ ⌊x / (s : ℝ) ^ 2⌋₊).card : ℝ) := by
    rw [← Nat.cast_sum]
    refine Nat.cast_le.2 (le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le)
    intro n hn
    rw [hTdef, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, -⟩, s, hs2, hs1, hs2'⟩ := hn
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hs0 : (0 : ℝ) < (s : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs2
      positivity
    rw [Finset.mem_biUnion]
    refine ⟨s, Finset.mem_Icc.2 ⟨hs2, Nat.le_floor ?_⟩, Finset.mem_Ioc.2 ⟨?_, Nat.le_floor ?_⟩⟩
    · rw [Real.le_sqrt (Nat.cast_nonneg s) hx]
      nlinarith
    · rw [Nat.floor_lt (div_nonneg hx (by positivity)), div_lt_iff₀ (by positivity)]
      have : x / (1 + η) < (n : ℝ) * (s : ℝ) ^ 2 := hs1
      rw [div_lt_iff₀ hη1] at this
      nlinarith
    · rw [le_div_iff₀ hs0]
      exact hs2'
  -- each piece, and the sum over `s`
  have h3 : ∀ s ∈ Finset.Icc 2 ⌊Real.sqrt x⌋₊,
      ((Finset.Ioc ⌊x / ((1 + η) * (s : ℝ) ^ 2)⌋₊ ⌊x / (s : ℝ) ^ 2⌋₊).card : ℝ)
        ≤ η / (1 + η) * x * ((s : ℝ) ^ 2)⁻¹ + 1 := by
    intro s hs
    have hs2 : 2 ≤ s := (Finset.mem_Icc.1 hs).1
    have hs0 : (0 : ℝ) < (s : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs2
      positivity
    have hA : 0 ≤ x / ((1 + η) * (s : ℝ) ^ 2) := div_nonneg hx (by positivity)
    have hAB : x / ((1 + η) * (s : ℝ) ^ 2) ≤ x / (s : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hx hs0 (le_mul_of_one_le_left hs0.le (by linarith))
    refine le_trans (card_Ioc_floor_le hA hAB) (le_of_eq ?_)
    field_simp
    ring
  have hcount : ((Finset.Icc 2 ⌊Real.sqrt x⌋₊).card : ℝ) ≤ Real.sqrt x := by
    rw [Nat.card_Icc]
    have h1 : ⌊Real.sqrt x⌋₊ + 1 - 2 ≤ ⌊Real.sqrt x⌋₊ := by omega
    exact le_trans (Nat.cast_le.2 h1) (Nat.floor_le (Real.sqrt_nonneg x))
  have hsum := Finset.sum_le_sum h3
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hinv := sum_Icc_two_inv_sq_le_one ⌊Real.sqrt x⌋₊
  have hc0 : 0 ≤ η / (1 + η) * x := by positivity
  have h4 : η / (1 + η) * x * ∑ s ∈ Finset.Icc 2 ⌊Real.sqrt x⌋₊, ((s : ℝ) ^ 2)⁻¹
      ≤ η / (1 + η) * x := by
    calc η / (1 + η) * x * ∑ s ∈ Finset.Icc 2 ⌊Real.sqrt x⌋₊, ((s : ℝ) ^ 2)⁻¹
        ≤ η / (1 + η) * x * 1 := mul_le_mul_of_nonneg_left hinv hc0
      _ = η / (1 + η) * x := mul_one _
  linarith

/-! ### The smoothing error, in expectation -/

/-- **The smoothing error** `(1+1/ε)((η²/4)(1 + log x)² + η + (1+η)/√x)`. -/
noncomputable def fracSmoothErr (x η ε : ℝ) : ℝ :=
  (1 + 1 / ε) * (η ^ 2 / 4 * (1 + Real.log x) ^ 2 + η + (1 + η) / Real.sqrt x)

/-- **The expectation of the smoothing error.**  For `S` a set of `y`-rough integers in
`[1, x]`, `x ≥ 1`, `η, ε > 0`:
`E[((1+1/ε)/(2η))∑_{r∈S}(2∫_{[r, r(1+η)]}|H_y(x/r) - H_y(x/t)|²dt)/r²] ≤ fracSmoothErr x η ε`.
Each window costs `2η((η²/4)(1 + log x) + ((1+η)r/x)J_r)/r`
(`RMF.integral_normSq_smoothFracSum_sub_le`); `∑_{r≤x} 1/r ≤ 1 + log x` and
`∑_r J_r ≤ ηx/(1+η) + √x` (`RMF.sum_card_fracJump_le`). -/
theorem integral_fracSmoothingError_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} {x η ε : ℝ} (hx : 1 ≤ x) (hη : 0 < η)
    (hε : 0 < ε) {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r) (hS1 : ∀ r ∈ S, 1 ≤ r)
    (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    (∫ ω, ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
        (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
          ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
            - smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
          / ((r : ℝ)) ^ 2 ∂μ)
      ≤ fracSmoothErr x η ε := by
  classical
  haveI := hX.isProbabilityMeasure
  have hx0 : (0 : ℝ) < x := by linarith
  have hS0 : ∀ r ∈ S, 0 < r := fun r hr => hS1 r hr
  set Jc : ℕ → ℝ := fun r => (({k ∈ Finset.Icc 1 ⌊x / r⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧
    ∃ s : ℕ, 2 ≤ s ∧ x / (1 + η) < (r : ℝ) * k * (s : ℝ) ^ 2
      ∧ (r : ℝ) * k * (s : ℝ) ^ 2 ≤ x}).card : ℝ) with hJc
  rw [integral_const_mul]
  have hE := integral_sum_setIntegral_normSq_sub_le_of_bound
    (fun ω u => smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y u ω) hη hS0
    (fun r => η ^ 2 / 4 * (1 + Real.log x) + (1 + η) * (r : ℝ) / x * Jc r)
    (fun r hr => integrable_uncurry_normSq_smoothFracSum_sub hX y hx0.le
      (by exact_mod_cast hS0 r hr))
    (fun r hr t ht => integral_normSq_smoothFracSum_sub_le hX y hx
      (by exact_mod_cast hS1 r hr) hη.le ht.1 ht.2)
  have hc0 : (0 : ℝ) ≤ (1 + 1 / ε) / (2 * η) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hE hc0) ?_
  have hterm : ∀ r ∈ S, (1 + 1 / ε) / (2 * η)
      * (2 * η * (η ^ 2 / 4 * (1 + Real.log x) + (1 + η) * (r : ℝ) / x * Jc r) / (r : ℝ))
      = (1 + 1 / ε) * (η ^ 2 / 4 * (1 + Real.log x)) * ((r : ℝ))⁻¹
        + (1 + 1 / ε) * (1 + η) / x * Jc r := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS0 r hr
    field_simp
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  -- the harmonic mass
  have hsubI : S ⊆ Finset.Icc 1 ⌊x⌋₊ := fun r hr =>
    Finset.mem_Icc.2 ⟨hS1 r hr, Nat.le_floor (hSx r hr)⟩
  have hH : ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ 1 + Real.log x := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubI fun i _ _ => by positivity) ?_
    have hh := harmonic_le_one_add_log ⌊x⌋₊
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    refine le_trans hh ?_
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg hx]
    · linarith [Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le hx0.le)]
  -- the jumps
  have hJ := sum_card_fracJump_le hSr hS1 hx0.le hη.le
  have hlog0 : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  have ha0 : (0 : ℝ) ≤ (1 + 1 / ε) * (η ^ 2 / 4 * (1 + Real.log x)) := by positivity
  have hb0 : (0 : ℝ) ≤ (1 + 1 / ε) * (1 + η) / x := by positivity
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hstep1 : (1 + 1 / ε) * (η ^ 2 / 4 * (1 + Real.log x)) * ∑ r ∈ S, ((r : ℝ))⁻¹
      ≤ (1 + 1 / ε) * (η ^ 2 / 4 * (1 + Real.log x)) * (1 + Real.log x) :=
    mul_le_mul_of_nonneg_left hH ha0
  have hstep2 : (1 + 1 / ε) * (1 + η) / x * ∑ r ∈ S, Jc r
      ≤ (1 + 1 / ε) * (1 + η) / x * (η / (1 + η) * x + Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hJ hb0
  have hfin : (1 + 1 / ε) * (1 + η) / x * (η / (1 + η) * x + Real.sqrt x)
      = (1 + 1 / ε) * (η + (1 + η) / Real.sqrt x) := by
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hA : (1 + η) / x * (η / (1 + η) * x) = η := by field_simp
    have hB : (1 + η) / x * Real.sqrt x = (1 + η) / Real.sqrt x := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hx0.ne' hsx.ne', mul_assoc, hsq]
    calc (1 + 1 / ε) * (1 + η) / x * (η / (1 + η) * x + Real.sqrt x)
        = (1 + 1 / ε) * ((1 + η) / x * (η / (1 + η) * x) + (1 + η) / x * Real.sqrt x) := by
          ring
      _ = (1 + 1 / ε) * (η + (1 + η) / Real.sqrt x) := by rw [hA, hB]
  rw [fracSmoothErr]
  nlinarith [hstep1, hstep2, hfin]

end RMF
