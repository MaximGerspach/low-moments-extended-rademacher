/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.StepShort
import RMF.UniformLower.HP2WindowExtNum

/-!
# HP2's window integral: the sum over the cells on short tubes, region by region

`r·RMF.hp2ExtSumS r 400 hp2ExtB 5.032` bounded for tubes of `r ≥ r₀ ≥ 35` blocks by quantities
uniform in `r` except the far depths' sum (`RMF.hp2ExtSumS_le_regions`), for a rung `r₀` with the
depths split at `D` and the short posts `r - d < N`:

* **the slab bound in closed form** `RMF.hp2SlabG` (`⌊M/3⌋` replaced by `(M - 2)/3`), exact at
  `M ≡ 2 (mod 3)` and with `(M + x)·hp2SlabG M` decreasing (`RMF.add_mul_hp2SlabG_anti`);
* **region I**, `d ≤ 3`: the post constant at `n₀ ≥ r₀ - b` (`RMF.hp2WinRegionIS_le_num`);
* **region II**, `4 ≤ d < D`: `r/(r - d) ≤ r₀/(r₀ - d)`, `κ₄(n₀) ≤ κ₄(r₀ - D + 1)`
  (`RMF.hp2WinRegionIIS_le`, `RMF.hp2WinIIS_sum_le`);
* **the short posts** `r - d < N`: `r·hp2SlabG (r - n) ≤ r₀·hp2SlabG (r₀ - n)`
  (`RMF.hp2NearS_depth_le`);
* **the deep cells**: `r·hp2SlabG r ≤ ρ·hp2SlabG ρ` (`RMF.hp2DeepS_le`);
* **the far depths** `D ≤ d ≤ r - N`, the one sum that grows with `r`: `≤ ∑ (1 + d/N)·hp2WinG d`
  up to the end of a cell of tube lengths (`RMF.hp2FarSum_le_table`), and from depth `200` by
  `RMF.sum_far_le`'s telescoping for `r ≥ 260` (`RMF.hp2FarSum_le_tail`).

The cells of tube lengths in numerals: `RMF.hp2ExtSumS_le_cell`, `RMF.hp2ExtSumS_le_cell_tail`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The sum split -/

/-- **`r·hp2ExtSumS` split**: the cells of the depths `d < r - 2`, the deep cells and below them. -/
lemma mul_hp2ExtSumS_eq (r N : ℕ) (B : ℕ → ℝ) (Bsat : ℝ) :
    (r : ℝ) * hp2ExtSumS r N B Bsat
      = ∑ d ∈ Finset.range (r - 2), ∑ j ∈ Finset.range 40,
          (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
        + (∑ j ∈ Finset.range N, (r : ℝ) * hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 4)
            * hp2Band (40 * (r - 2) + j)
          + (r : ℝ) * hp2ExtSatS r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))) := by
  unfold hp2ExtSumS
  rw [Finset.sum_range_add, sum_range_forty_mul, mul_add, mul_add, Finset.mul_sum,
    Finset.mul_sum, ← add_assoc]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hd := Finset.mem_range.1 hd
      have hj := Finset.mem_range.1 hj
      have h1 : 40 * d + j < 40 * (r - 2) := by omega
      have h2 : (40 * d + j) / 40 = d := by omega
      have h3 : (40 * d + j) % 40 = j := by omega
      unfold hp2ExtCellS
      rw [if_pos h1, h2, h3]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : ¬ 40 * (r - 2) + j < 40 * (r - 2) := by omega
      have h2 : 40 * (r - 2) + j - 40 * (r - 2) = j := by omega
      unfold hp2ExtCellS
      rw [if_neg h1, h2]
      ring
  · ring

/-! ### A closed-form slab majorant -/

/-- **The variance floors' product in closed form** at depth `M`: the floors of
`RMF.hp2SlabBound_le_of_closed` with `⌊M/3⌋` replaced by `(M - 2)/3`, `M - 2⌊M/3⌋` by
`(M + 4)/3` and the tails by `0.029`, `0.0002`. -/
noncomputable def hp2SlabPC (M : ℕ) : ℝ :=
  (((M : ℝ) - 2) * (0.499996 / 3) - 0.948) * (((M : ℝ) + 4) * (0.499996 / 3) - 0.0304)
    * (((M : ℝ) - 2) * (0.499996 / 3) - 0.016)

/-- **The closed-form slab majorant** `hp2SlabG M = 2/√(2·3.14159³·hp2SlabPC M)`: for `M ≥ 17`,
`hp2SlabBound M c ≤ hp2SlabPrefactor c·hp2SlabG M` (`RMF.hp2SlabBound_le_slabG`), and
`(M + x)·hp2SlabG M` decreases in `M` (`RMF.add_mul_hp2SlabG_anti`). -/
noncomputable def hp2SlabG (M : ℕ) : ℝ := 2 / √(2 * 3.14159 ^ 3 * hp2SlabPC M)

/-- The closed-form slab majorant is nonnegative. -/
lemma hp2SlabG_nonneg (M : ℕ) : 0 ≤ hp2SlabG M := by
  unfold hp2SlabG
  positivity

/-- The three closed-form floors are positive from `M ≥ 17`. -/
lemma hp2SlabPC_factors_pos {M : ℕ} (hM : 17 ≤ M) :
    0 < ((M : ℝ) - 2) * (0.499996 / 3) - 0.948 ∧ 0 < ((M : ℝ) + 4) * (0.499996 / 3) - 0.0304
      ∧ 0 < ((M : ℝ) - 2) * (0.499996 / 3) - 0.016 := by
  have h : (17 : ℝ) ≤ M := by exact_mod_cast hM
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- The closed-form product is positive from `M ≥ 17`. -/
lemma hp2SlabPC_pos {M : ℕ} (hM : 17 ≤ M) : 0 < hp2SlabPC M := by
  obtain ⟨h₁, h₂, h₃⟩ := hp2SlabPC_factors_pos hM
  unfold hp2SlabPC
  positivity

/-- `hp2SlabG M ≤ x` from `4 ≤ 2·3.14159³x²·hp2SlabPC M`: the numerals' form. -/
lemma hp2SlabG_le_of {M : ℕ} {x : ℝ} (hx : 0 ≤ x) (hP : 0 < hp2SlabPC M)
    (h : 4 ≤ 2 * 3.14159 ^ 3 * x ^ 2 * hp2SlabPC M) : hp2SlabG M ≤ x := by
  have hK : 0 < 2 * 3.14159 ^ 3 * hp2SlabPC M := by positivity
  have hs := Real.sqrt_pos.2 hK
  unfold hp2SlabG
  rw [div_le_iff₀ hs]
  have e : x * √(2 * 3.14159 ^ 3 * hp2SlabPC M) = √(x ^ 2 * (2 * 3.14159 ^ 3 * hp2SlabPC M)) := by
    rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx]
  rw [e, show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **The closed form below the exact floors**: for `M ≥ 17`, `hp2SlabPC M` is at most the
product of the variance floors of `RMF.hp2SlabBound_le_of_closed` with the tails `0.029`,
`0.0002` — the floors' product increases in `⌊M/3⌋` on `[(M - 2)/3, M/3]`, and equals the closed
form at `⌊M/3⌋ = (M - 2)/3`. -/
lemma hp2SlabPC_le_floors {M : ℕ} (hM : 17 ≤ M) :
    hp2SlabPC M ≤ (((M / 3 : ℕ) : ℝ) * 0.499996 - 1.8642 / 2 - 0.0159)
      * (((M - M / 3 - M / 3 : ℕ) : ℝ) * 0.499996 - 0.029 / 2 - 0.0159)
      * (((M / 3 : ℕ) : ℝ) * 0.499996 - 0.0002 / 2 - 0.0159) := by
  obtain ⟨n, s, hs, rfl⟩ : ∃ n s, s < 3 ∧ M = 3 * n + s :=
    ⟨M / 3, M % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod M 3).symm⟩
  have hn : (3 * n + s) / 3 = n := by omega
  have hm : 3 * n + s - n - n = n + s := by omega
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast (show 5 ≤ n by omega)
  rw [hn, hm]
  unfold hp2SlabPC
  push_cast
  interval_cases s <;> norm_num <;> nlinarith

/-- **The slab bound by its closed-form majorant**: for `M ≥ 17`, `c ≥ 0`,
`hp2SlabBound M c ≤ hp2SlabPrefactor c·hp2SlabG M` (`RMF.hp2SlabBound_le_of_closed` with the
tails `hp2CosTail ⌊M/3⌋ ≤ 0.029`, `hp2CosTail (M - ⌊M/3⌋) ≤ 0.0002`,
`RMF.hp2SlabPC_le_floors`). -/
theorem hp2SlabBound_le_slabG {M : ℕ} (hM : 17 ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    hp2SlabBound M c ≤ hp2SlabPrefactor c * hp2SlabG M := by
  have hn5 : 5 ≤ M / 3 := by omega
  have he4 : Real.exp (-4) ≤ 0.01833 := by interval_decide (trust := kernel)
  have he11 : Real.exp (-11) ≤ 0.0001 := by interval_decide (trust := kernel)
  have ht₂ : hp2CosTail (M / 3) ≤ 0.029 := by
    refine (hp2CosTail_le_exp (by omega)).trans ?_
    have h5 : (5 : ℝ) ≤ ((M / 3 : ℕ) : ℝ) := by exact_mod_cast hn5
    have := Real.exp_le_exp.2 (show -(((M / 3 : ℕ) : ℝ) - 1) ≤ -4 by linarith)
    nlinarith
  have ht₃ : hp2CosTail (M - M / 3) ≤ 0.0002 := by
    refine (hp2CosTail_le_exp (by omega)).trans ?_
    have h12 : (12 : ℝ) ≤ ((M - M / 3 : ℕ) : ℝ) := by exact_mod_cast (show 12 ≤ M - M / 3 by omega)
    have := Real.exp_le_exp.2 (show -(((M - M / 3 : ℕ) : ℝ) - 1) ≤ -11 by linarith)
    nlinarith
  have h5 : (5 : ℝ) ≤ ((M / 3 : ℕ) : ℝ) := by exact_mod_cast hn5
  have h5' : (5 : ℝ) ≤ ((M - M / 3 - M / 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 5 ≤ M - M / 3 - M / 3 by omega)
  have hP := hp2SlabPC_pos hM
  have hPle := hp2SlabPC_le_floors hM
  refine hp2SlabBound_le_of_closed (by omega) hc ht₂ ht₃ (hp2SlabG_nonneg M) (by linarith)
    (by linarith) (by linarith) ?_
  have hg2 : hp2SlabG M ^ 2 * (2 * 3.14159 ^ 3 * hp2SlabPC M) = 4 := by
    have hK : 0 < 2 * 3.14159 ^ 3 * hp2SlabPC M := by positivity
    unfold hp2SlabG
    rw [div_pow, Real.sq_sqrt hK.le, div_mul_cancel₀ _ hK.ne']
    norm_num
  have hg0 : 0 ≤ hp2SlabG M ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hPle (by positivity : (0 : ℝ) ≤ 2 * 3.14159 ^ 3
    * hp2SlabG M ^ 2)]

/-- **The prefix bound by the closed-form majorant**: `hp2PrefixBound M c ≤ hp2SlabPrefHat c·
hp2SlabG M` for `M ≥ 17`, `c ≥ 0`. -/
lemma hp2PrefixBound_le_slabG {M : ℕ} (hM : 17 ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    hp2PrefixBound M c ≤ hp2SlabPrefHat c * hp2SlabG M :=
  (min_le_right _ _).trans ((hp2SlabBound_le_slabG hM hc).trans
    (mul_le_mul_of_nonneg_right (hp2SlabPrefactor_le hc) (hp2SlabG_nonneg M)))

/-- **`(M + x)·hp2SlabG M` decreases** in `M ≥ 17` for `x ≥ 0`: `(M' + x)²PC(M) ≤ (M + x)²PC(M')`
factor by factor. -/
lemma add_mul_hp2SlabG_anti {M M' : ℕ} (hM : 17 ≤ M) (h : M ≤ M') {x : ℝ} (hx : 0 ≤ x) :
    ((M' : ℝ) + x) * hp2SlabG M' ≤ ((M : ℝ) + x) * hp2SlabG M := by
  have hM' : 17 ≤ M' := hM.trans h
  have hMr : (M : ℝ) ≤ M' := by exact_mod_cast h
  have h17 : (17 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨a₁, a₂, a₃⟩ := hp2SlabPC_factors_pos hM
  obtain ⟨b₁, b₂, b₃⟩ := hp2SlabPC_factors_pos hM'
  have hP := hp2SlabPC_pos hM
  have hP' := hp2SlabPC_pos hM'
  set K : ℝ := 2 * 3.14159 ^ 3 with hK
  have hK0 : 0 < K := by rw [hK]; norm_num
  have hs := Real.sqrt_pos.2 (mul_pos hK0 hP)
  have hs' := Real.sqrt_pos.2 (mul_pos hK0 hP')
  -- the factors
  have f₁ : ((M' : ℝ) + x) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.948)
      ≤ ((M : ℝ) + x) * (((M' : ℝ) - 2) * (0.499996 / 3) - 0.948) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hMr) hx]
  have f₂ : ((M : ℝ) + 4) * (0.499996 / 3) - 0.0304 ≤ ((M' : ℝ) + 4) * (0.499996 / 3) - 0.0304 := by
    nlinarith
  have f₃ : ((M' : ℝ) + x) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.016)
      ≤ ((M : ℝ) + x) * (((M' : ℝ) - 2) * (0.499996 / 3) - 0.016) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hMr) hx]
  have key : ((M' : ℝ) + x) ^ 2 * hp2SlabPC M ≤ ((M : ℝ) + x) ^ 2 * hp2SlabPC M' := by
    unfold hp2SlabPC
    have p₁ : 0 ≤ ((M' : ℝ) + x) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.948) := by positivity
    have p₃ : 0 ≤ ((M' : ℝ) + x) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.016) := by positivity
    calc ((M' : ℝ) + x) ^ 2 * ((((M : ℝ) - 2) * (0.499996 / 3) - 0.948)
          * (((M : ℝ) + 4) * (0.499996 / 3) - 0.0304) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.016))
        = (((M' : ℝ) + x) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.948))
          * (((M : ℝ) + 4) * (0.499996 / 3) - 0.0304)
          * (((M' : ℝ) + x) * (((M : ℝ) - 2) * (0.499996 / 3) - 0.016)) := by ring
      _ ≤ (((M : ℝ) + x) * (((M' : ℝ) - 2) * (0.499996 / 3) - 0.948))
          * (((M' : ℝ) + 4) * (0.499996 / 3) - 0.0304)
          * (((M : ℝ) + x) * (((M' : ℝ) - 2) * (0.499996 / 3) - 0.016)) :=
        mul_le_mul (mul_le_mul f₁ f₂ a₂.le (p₁.trans f₁)) f₃ p₃ (mul_nonneg (p₁.trans f₁) b₂.le)
      _ = ((M : ℝ) + x) ^ 2 * ((((M' : ℝ) - 2) * (0.499996 / 3) - 0.948)
          * (((M' : ℝ) + 4) * (0.499996 / 3) - 0.0304)
          * (((M' : ℝ) - 2) * (0.499996 / 3) - 0.016)) := by ring
  unfold hp2SlabG
  rw [← hK, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hs' hs]
  have hx1 : 0 ≤ (M' : ℝ) + x := by positivity
  have hx2 : 0 ≤ (M : ℝ) + x := by positivity
  have e1 : ((M' : ℝ) + x) * √(K * hp2SlabPC M) = √(((M' : ℝ) + x) ^ 2 * (K * hp2SlabPC M)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx1]
  have e2 : ((M : ℝ) + x) * √(K * hp2SlabPC M') = √(((M : ℝ) + x) ^ 2 * (K * hp2SlabPC M')) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx2]
  have hle : √(((M' : ℝ) + x) ^ 2 * (K * hp2SlabPC M))
      ≤ √(((M : ℝ) + x) ^ 2 * (K * hp2SlabPC M')) := by
    refine Real.sqrt_le_sqrt ?_
    calc ((M' : ℝ) + x) ^ 2 * (K * hp2SlabPC M) = K * (((M' : ℝ) + x) ^ 2 * hp2SlabPC M) := by
          ring
      _ ≤ K * (((M : ℝ) + x) ^ 2 * hp2SlabPC M') := mul_le_mul_of_nonneg_left key hK0.le
      _ = ((M : ℝ) + x) ^ 2 * (K * hp2SlabPC M') := by ring
  calc ((M' : ℝ) + x) * 2 * √(K * hp2SlabPC M)
      = 2 * (((M' : ℝ) + x) * √(K * hp2SlabPC M)) := by ring
    _ ≤ 2 * (((M : ℝ) + x) * √(K * hp2SlabPC M')) := by rw [e1, e2]; linarith
    _ = ((M : ℝ) + x) * 2 * √(K * hp2SlabPC M') := by ring

/-- `r·hp2SlabG r` decreases in `r ≥ 17`. -/
lemma mul_hp2SlabG_anti {M M' : ℕ} (hM : 17 ≤ M) (h : M ≤ M') :
    (M' : ℝ) * hp2SlabG M' ≤ M * hp2SlabG M := by
  simpa using add_mul_hp2SlabG_anti hM h (x := 0) le_rfl

/-! ### The small factors -/

/-- `e^x ≤ 1.000101` for `x ≤ 1.009·10⁻⁴`: the rest's `10⁻⁴` with every `e^{-16}`-small term. -/
lemma exp_le_one_000101 {x : ℝ} (hx : x ≤ 1.009 / 10 ^ 4) : Real.exp x ≤ 1.000101 :=
  (Real.exp_le_exp.2 hx).trans (by interval_decide (trust := kernel))

/-- `e^{1-n} ≤ 1.13·10⁻⁷` for `n ≥ 17`. -/
lemma exp_one_sub_le_of_ge {n : ℕ} (hn : 17 ≤ n) : Real.exp (1 - (n : ℝ)) ≤ 1.13 / 10 ^ 7 := by
  have hn' : (17 : ℝ) ≤ n := by exact_mod_cast hn
  have h16 : Real.exp (-16) ≤ 1.13 / 10 ^ 7 := by interval_decide (trust := kernel)
  exact (Real.exp_le_exp.2 (by linarith)).trans h16

/-- `e^{1-n} ≤ 4.14·10⁻⁸` for `n ≥ 18` (`RMF.exp_neg_seventeen_le`). -/
lemma exp_one_sub_le_of_ge_eighteen {n : ℕ} (hn : 18 ≤ n) :
    Real.exp (1 - (n : ℝ)) ≤ 0.0000000414 := by
  have hn' : (18 : ℝ) ≤ n := by exact_mod_cast hn
  exact (Real.exp_le_exp.2 (by linarith)).trans exp_neg_seventeen_le

/-- **The rest's factor on short tubes, `r - d ≥ 18`**: `hp2ExtFacS r d ≤ 1.000101`. -/
lemma hp2ExtFacS_le {r d : ℕ} (h : d + 18 ≤ r) : hp2ExtFacS r d ≤ 1.000101 := by
  have := exp_one_sub_le_of_ge_eighteen (n := r - d) (by omega)
  exact exp_le_one_000101 (by linarith)

/-! ### Region I: the depths `d ≤ 3` -/

/-- **The post bound's product of class `d`** at `n₀ = n`, `(0.495 - a₁/n)(0.495 - a₂/n)`:
`RMF.hp2WinCpost d j n` is the class's `C₀` over its root. -/
noncomputable def hp2WinX (d n : ℕ) : ℝ :=
  if d = 0 then (0.495 - 0.8391 / n) * (0.495 - 0.8427 / n)
  else if d = 1 then (0.495 - 0.6408 / n) * (0.495 - 0.405 / n)
  else if d = 2 then (0.495 - 0.5624 / n) * (0.495 - 0.2574 / n)
  else if d = 3 then (0.495 - 0.5624 / n) * (0.495 - 0.818 / n)
  else (0.495 - 0.5624 / n) * (0.495 - 1.2572 / n)

/-- `hp2WinX d` is positive and increases from `n ≥ 3`. -/
lemma hp2WinX_le {d m n : ℕ} (hm : 3 ≤ m) (h : m ≤ n) :
    0 < hp2WinX d m ∧ hp2WinX d m ≤ hp2WinX d n := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) < m := by linarith
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ 1.2572 → 0 ≤ b → b ≤ 1.2572 →
      0 < (0.495 - a / m) * (0.495 - b / m)
        ∧ (0.495 - a / m) * (0.495 - b / m) ≤ (0.495 - a / n) * (0.495 - b / n) := by
    intro a b ha ha' hb hb'
    have a₁ : a / (n : ℝ) ≤ a / m := div_le_div_of_nonneg_left ha hm0 hmn
    have a₂ : b / (n : ℝ) ≤ b / m := div_le_div_of_nonneg_left hb hm0 hmn
    have b₁ : a / (m : ℝ) ≤ 1.2572 / 3 := div_le_div₀ (by norm_num) ha' (by norm_num) hm'
    have b₂ : b / (m : ℝ) ≤ 1.2572 / 3 := div_le_div₀ (by norm_num) hb' (by norm_num) hm'
    exact ⟨mul_pos (by linarith) (by linarith),
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)⟩
  unfold hp2WinX
  split_ifs
  · exact key _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `RMF.hp2WinCpost` as `C₀/√(hp2WinX d n)` on the classes `d ≤ 3`. -/
lemma hp2WinCpost_eq_of_lt {d j n : ℕ} (hd : d < 4) :
    hp2WinCpost d j n = hp2WinC0 d j / √(hp2WinX d n) := by
  unfold hp2WinCpost hp2WinC0 hp2WinX
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with h | h | h | h <;> subst h <;> simp

/-- `κ₄` as `1/√(hp2WinX 4 n)`. -/
lemma hp2Kappa4_eq (n : ℕ) : hp2Kappa4 n = 1 / √(hp2WinX 4 n) := by
  unfold hp2Kappa4 hp2WinX
  simp

/-- **The post constant of the classes `d ≤ 3` from `n₀ ≥ m`**: `C₀·K` once `1 ≤ K²·hp2WinX d m`. -/
lemma hp2WinCpost_le_of {d j n m : ℕ} (hd : d < 4) (hj : j < 40) (hm : 3 ≤ m) (hmn : m ≤ n)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : 1 ≤ K ^ 2 * hp2WinX d m) :
    hp2WinCpost d j n ≤ hp2WinC0 d j * K := by
  obtain ⟨hX0, hX⟩ := hp2WinX_le (d := d) hm hmn
  have hC0 : 0 ≤ hp2WinC0 d j := by
    unfold hp2WinC0
    have := (hp2Win_tables_zero hj).1
    have := (hp2Win_tables_one hj).1
    have := (hp2Win_tables_two hj).1
    have := (hp2Win_tables_three hj).1
    split_ifs <;> assumption
  rw [hp2WinCpost_eq_of_lt hd]
  exact div_sqrt_le_mul hC0 (hX0.trans_le hX) hK0
    (hK.trans (mul_le_mul_of_nonneg_left hX (sq_nonneg K)))

/-- `κ₄(n) ≤ K` for `n ≥ m ≥ 3` once `1 ≤ K²·hp2WinX 4 m`. -/
lemma hp2Kappa4_le_of {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : 1 ≤ K ^ 2 * hp2WinX 4 m) : hp2Kappa4 n ≤ K := by
  obtain ⟨hX0, hX⟩ := hp2WinX_le (d := 4) hm hmn
  rw [hp2Kappa4_eq]
  simpa using div_sqrt_le_mul (C := 1) (by norm_num) (hX0.trans_le hX) hK0
    (hK.trans (mul_le_mul_of_nonneg_left hX (sq_nonneg K)))

/-- **Region I's cells on short tubes**: for `d ≤ 3`, `j < 40`, `35 ≤ ρ ≤ r` and
`1 ≤ K²·hp2WinX d (ρ - b)`, `b = hp2PostStart d`,
`r·hp2WinCell r d j ≤ (ρ/(ρ - b))·K·C₀m̂B̂e^{Ê}` — `RMF.hp2WinCell_le_I` with the post constant
at `n₀ ≥ ρ - b` in place of `n₀ = 1000`. -/
theorem hp2WinCell_le_IS {ρ r d j : ℕ} (hρ : 35 ≤ ρ) (hρ' : ρ ≤ 1000) (hr : ρ ≤ r) (hd : d < 4)
    (hj : j < 40) {K : ℝ} (hK0 : 0 ≤ K) (hK : 1 ≤ K ^ 2 * hp2WinX d (ρ - hp2PostStart d)) :
    (r : ℝ) * hp2WinCell r d j
      ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) * K
        * (hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)) := by
  have hb4 : hp2PostStart d ≤ 4 := by unfold hp2PostStart; split_ifs <;> omega
  have hm3 : 3 ≤ ρ - hp2PostStart d := by omega
  have hN : ρ - hp2PostStart d ≤ hp2WinN r d := by unfold hp2WinN; omega
  have hC := hp2WinCpost_le_of hd hj hm3 hN hK0 hK
  have hC0 : 0 ≤ hp2WinCpost d j (hp2WinN r d) := hp2WinCpost_nonneg hj _
  have hE := Real.exp_le_exp.2 (hp2CellMassExp_le_EI (j := j) (show d + 21 ≤ r by omega))
  have hM := exp_hp2PrefixExpM_le hd
  have hB := hp2WinPrefix_le_BHat hd hj
  have hB0 := hp2WinPrefix_nonneg (d := d) hj
  have hρr : (35 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hrr : (ρ : ℝ) ≤ r := by exact_mod_cast hr
  have hbR : (hp2PostStart d : ℝ) ≤ 4 := by exact_mod_cast hb4
  have hb0 : (0 : ℝ) ≤ hp2PostStart d := Nat.cast_nonneg _
  have hNr : ((r - hp2PostStart d : ℕ) : ℝ) = (r : ℝ) - hp2PostStart d := by
    push_cast [show hp2PostStart d ≤ r by omega]; ring
  have hfac : (r : ℝ) / ((r - hp2PostStart d : ℕ) : ℝ) ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) := by
    rw [hNr, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg hb0 (sub_nonneg.2 hrr)]
  have hcell : hp2WinCell r d j = hp2WinReg r d j := by
    unfold hp2WinCell; rw [if_pos hd]
  have hC0' : 0 ≤ hp2WinC0 d j := by
    unfold hp2WinC0
    have := (hp2Win_tables_zero hj).1
    have := (hp2Win_tables_one hj).1
    have := (hp2Win_tables_two hj).1
    have := (hp2Win_tables_three hj).1
    split_ifs <;> assumption
  rw [hcell, hp2WinReg, hp2PairBoundOf_same]
  have hPB : hp2WinCpost d j (hp2WinN r d) * Real.exp (hp2CellMassExp d j r)
      * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)
      ≤ K * (hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)) := by
    have e1 := mul_le_mul hC hE (Real.exp_pos _).le (by positivity)
    have e2 := mul_le_mul hM hB hB0 (by unfold hp2WinMuHat; split_ifs <;> norm_num)
    calc hp2WinCpost d j (hp2WinN r d) * Real.exp (hp2CellMassExp d j r)
          * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)
        ≤ hp2WinC0 d j * K * Real.exp (hp2WinEI d j) * (hp2WinMuHat d * hp2WinBHat d j) :=
          mul_le_mul e1 e2 (by positivity) (le_trans (by positivity) e1)
      _ = _ := by ring
  have hPB0 : 0 ≤ hp2WinCpost d j (hp2WinN r d) * Real.exp (hp2CellMassExp d j r)
      * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j) := by positivity
  have hfac0 : 0 ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) := div_nonneg (by linarith) (by linarith)
  calc (r : ℝ) * (hp2WinCpost d j (hp2WinN r d) * Real.exp (hp2CellMassExp d j r)
        * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)
        / ((r - hp2PostStart d : ℕ) : ℝ))
      = (r : ℝ) / ((r - hp2PostStart d : ℕ) : ℝ) * (hp2WinCpost d j (hp2WinN r d)
        * Real.exp (hp2CellMassExp d j r)
        * (Real.exp (hp2PrefixExpM d + 5 / 10 ^ 20) * hp2WinPrefix d j)) := by ring
    _ ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d)
        * (K * (hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j))) :=
        mul_le_mul hfac hPB hPB0 hfac0
    _ = _ := by ring

/-- **Region I on short tubes**: for `d ≤ 3`, `35 ≤ ρ ≤ r` and `1 ≤ K²·hp2WinX d (ρ - b)`,
`∑_j r·hp2WinCell r d j·hp2ExtFacS r d·hp2Band(40d + j)
  ≤ (ρ/(ρ - b))·K·1.000101·(∑_j hp2WinP d j)/κ̂_d` (the rows `RMF.hp2WinP_spec`,
`hp2WinIexpr = C₀κ̂m̂B̂e^{Ê}`). -/
theorem hp2WinRegionIS_le {ρ r d : ℕ} (hρ : 35 ≤ ρ) (hρ' : ρ ≤ 1000) (hr : ρ ≤ r) (hd : d < 4)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : 1 ≤ K ^ 2 * hp2WinX d (ρ - hp2PostStart d)) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) * K * 1.000101
        * ((∑ j ∈ Finset.range 40, hp2WinP d j) / hp2WinKappaHat d) := by
  have hρr : (35 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hb4 : (hp2PostStart d : ℝ) ≤ 4 := by
    exact_mod_cast (show hp2PostStart d ≤ 4 by unfold hp2PostStart; split_ifs <;> omega)
  have hκ : 0 < hp2WinKappaHat d := by unfold hp2WinKappaHat; split_ifs <;> norm_num
  have hF := hp2ExtFacS_le (r := r) (d := d) (by omega)
  have hF0 : 0 ≤ hp2ExtFacS r d := (Real.exp_pos _).le
  have hfac0 : 0 ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) * K :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hK0
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have hcell := hp2WinCell_le_IS hρ hρ' hr hd hj hK0 hK
  have hP := hp2WinP_spec d hd j hj
  have hband0 := hp2Band_nonneg (40 * d + j)
  have hI : hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)
      * hp2Band (40 * d + j) ≤ hp2WinP d j / hp2WinKappaHat d := by
    rw [le_div_iff₀ hκ]
    calc hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)
          * hp2Band (40 * d + j) * hp2WinKappaHat d
        = hp2WinIexpr d j * hp2Band (40 * d + j) := by unfold hp2WinIexpr; ring
      _ ≤ hp2WinP d j := hP
  have hcell0 : 0 ≤ (r : ℝ) * hp2WinCell r d j :=
    mul_nonneg (Nat.cast_nonneg r) (hp2WinCell_nonneg r d hj)
  calc (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      ≤ ((ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) * K
          * (hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)))
        * 1.000101 * hp2Band (40 * d + j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hcell hF hF0 (hcell0.trans hcell)) hband0
    _ = (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) * K * 1.000101
        * (hp2WinC0 d j * hp2WinMuHat d * hp2WinBHat d j * Real.exp (hp2WinEI d j)
          * hp2Band (40 * d + j)) := by ring
    _ ≤ (ρ : ℝ) / ((ρ : ℝ) - hp2PostStart d) * K * 1.000101
        * (hp2WinP d j / hp2WinKappaHat d) :=
        mul_le_mul_of_nonneg_left hI (mul_nonneg hfac0 (by norm_num))

/-! ### The depths `d ≥ 4` -/

/-- **One depth `d ≥ 4` from a slab majorant `g`**: `RMF.hp2WinRegionIII_depth_le` with
`hp2PrefixBound d c ≤ hp2SlabPrefHat c·g` (`c ≥ 0`) in place of the slab bound from depth `200`:
for `d + 3 ≤ r` and the numerals `W`, `A_sl`, `A_t`,
`∑_j r·hp2WinCell r d j·hp2Band(40d + j)
  ≤ g·e^{2e^{1-d} + 3.1e^{1-(r-d)}}·min((r/(r - d))κ₄(n₀)A_sl, r·A_t)`. -/
theorem hp2WinCell_sum_le_of_slab {r d : ℕ} (hd : 4 ≤ d) (hdr : d + 3 ≤ r) {g : ℝ} (hg0 : 0 ≤ g)
    (hg : ∀ c : ℝ, 0 ≤ c → hp2PrefixBound d c ≤ hp2SlabPrefHat c * g) {W : ℕ → ℝ}
    (hW : ∀ j < 40, Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)) ≤ W j)
    {Asl At : ℝ}
    (hAsl : ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
      * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) ≤ Asl)
    (hAt : ∑ j ∈ Finset.range 40, (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2)
      ≤ At) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ g * Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
        * min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d) * Asl) ((r : ℝ) * At) := by
  set β := 2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)) with hβdef
  have hN0 : (0 : ℝ) < ((r - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < r - d by omega)
  have hL := one_sub_exp_neg_one_le
  have hL0 := one_sub_exp_neg_one_pos
  have hk0 := hp2Kappa4_nonneg (hp2WinN r d)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  -- per `j`: the regular and the trivial term
  have hpt : ∀ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ min (g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d))
            * (hp2PostC04 j * (2 * 0.632121) * W j * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05)))
          (g * Real.exp β * (r : ℝ)
            * ((2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2))) := by
    intro j hj
    have hj := Finset.mem_range.1 hj
    obtain ⟨hC0, _⟩ := hp2Win_tables_four hj
    have hw0 : 0 ≤ hp2CellEnd j - hp2CellEnd (j + 1) :=
      sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j))
    have hWj := hW j hj
    have hW0 : 0 ≤ W j := le_trans (by positivity) hWj
    have hc := hp2WinCell_band_le_four (r := r) (d := d) (j := j) (β := β) hd hdr hj
      (by rw [hβdef]; linarith [show (0 : ℝ) < 1 / 10 ^ 8 by norm_num])
    refine hc.trans ?_
    have hcj : (0 : ℝ) ≤ max (hp2PostCh4 j) 1.05 := le_trans (by norm_num) (le_max_right _ _)
    have hB := hg _ hcj
    have hB' := hg 1.05 (by norm_num)
    have hB0 := hp2PrefixBound_nonneg d hcj
    have hB'0 := hp2PrefixBound_nonneg d (c := 1.05) (by norm_num)
    have hY : Real.exp β * (2 * (1 - Real.exp (-1)))
        * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)))
        ≤ Real.exp β * (2 * 0.632121) * W j :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le) hWj
        (by positivity) (by positivity)
    have hY0 : 0 ≤ Real.exp β * (2 * (1 - Real.exp (-1)))
        * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))) := by positivity
    rw [min_mul_of_nonneg _ _ hY0]
    refine min_le_min ?_ ?_
    · calc (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
            * hp2PrefixBound d (max (hp2PostCh4 j) 1.05)
            * (Real.exp β * (2 * (1 - Real.exp (-1)))
              * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))))
          ≤ (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
            * (hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) * g)
            * (Real.exp β * (2 * 0.632121) * W j) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) hY hY0 (by
              have : 0 ≤ hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) * g :=
                le_trans hB0 hB
              positivity)
        _ = _ := by ring
    · calc (r : ℝ) * (hp2PrefixBound d 1.05 / 1.05 ^ 2)
            * (Real.exp β * (2 * (1 - Real.exp (-1)))
              * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))))
          ≤ (r : ℝ) * (hp2SlabPrefHat 1.05 * g / 1.05 ^ 2)
            * (Real.exp β * (2 * 0.632121) * W j) :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hB' (by norm_num)) hr0) hY hY0 (by
              have : 0 ≤ hp2SlabPrefHat 1.05 * g := le_trans hB'0 hB'
              positivity)
        _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans (sum_min_le_min_sum.trans ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hAsl0 : 0 ≤ g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d)) := by
    positivity
  have hAt0 : 0 ≤ g * Real.exp β * (r : ℝ) := by positivity
  calc min (g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d))
          * ∑ j ∈ Finset.range 40, hp2PostC04 j * (2 * 0.632121) * W j
            * hp2SlabPrefHat (max (hp2PostCh4 j) 1.05))
        (g * Real.exp β * (r : ℝ) * ∑ j ∈ Finset.range 40,
          (2 * 0.632121) * W j * (hp2SlabPrefHat 1.05 / 1.05 ^ 2))
      ≤ min (g * Real.exp β * ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d)) * Asl)
        (g * Real.exp β * (r : ℝ) * At) :=
        min_le_min (mul_le_mul_of_nonneg_left hAsl hAsl0) (mul_le_mul_of_nonneg_left hAt hAt0)
    _ = g * Real.exp β * min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d) * Asl)
        ((r : ℝ) * At) := by
        rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ g * Real.exp β)]
        congr 1 <;> ring

/-! ### Region II: the depths `4 ≤ d < D` -/

/-- The slab values `hp2WinG d`, `12 ≤ d < 200`, are nonnegative. -/
lemma hp2WinG_nonneg {d : ℕ} (h₀ : 12 ≤ d) (h₁ : d < 200) : 0 ≤ hp2WinG d := by
  have h := hp2WinG_spec h₀ h₁ (c := 1) (by norm_num)
  have h0 : 0 ≤ hp2SlabBound d 1 := by
    have := hp2SlabPrefactor_nonneg (c := 1) (by norm_num)
    unfold hp2SlabBound
    split_ifs <;> positivity
  have hP : 0 < hp2SlabPrefHat 1 := by unfold hp2SlabPrefHat hp2PrefixK; norm_num
  exact (mul_nonneg_iff_of_pos_left hP).1 (h0.trans h)

/-- **Region II on short tubes, one depth**: for `4 ≤ d < 200`, `19 ≤ m ≤ 1000`, `d + m ≤ r` and
`1 ≤ K²·hp2WinX 4 m`,
`∑_j r·hp2WinCell r d j·hp2ExtFacS r d·hp2Band(40d + j) ≤ (1 + d/m)(K/2.023923)·1.000101·hp2WinE d
  ·∑_j C₀(j)·2.023923·(2·0.632121)·hp2WinW j·hp2WinB d j` — `RMF.hp2WinRegionII_le` with
`n₀ = min(r - d, 1000) ≥ m` in place of `n₀ = 1000`, and the rest's factor. -/
theorem hp2WinRegionIIS_le {r m d : ℕ} (hd4 : 4 ≤ d) (hd : d < 200) (hm : 19 ≤ m)
    (hm1000 : m ≤ 1000) (hdm : d + m ≤ r) {K : ℝ} (hK0 : 0 ≤ K) (hK : 1 ≤ K ^ 2 * hp2WinX 4 m) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      ≤ (1 + d / (m : ℝ)) * (K / 2.023923) * 1.000101 * hp2WinE d
        * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * hp2WinW j
          * hp2WinB d j := by
  have hm' : (19 : ℝ) ≤ m := by exact_mod_cast hm
  have hdmr : (d : ℝ) + m ≤ r := by exact_mod_cast hdm
  have hNr : ((r - d : ℕ) : ℝ) = (r : ℝ) - d := by push_cast [show d ≤ r by omega]; ring
  have hfac : (r : ℝ) / ((r - d : ℕ) : ℝ) ≤ 1 + d / (m : ℝ) := by
    rw [hNr, div_le_iff₀ (by linarith)]
    have h1 : (d : ℝ) / m * ((r : ℝ) - d) ≥ d := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    nlinarith
  have hk : hp2Kappa4 (hp2WinN r d) ≤ K :=
    hp2Kappa4_le_of (by omega) (by unfold hp2WinN; simp [hp2PostStart, hd4]; omega) hK0 hK
  have hk0 := hp2Kappa4_nonneg (hp2WinN r d)
  -- the mass factor with the rest's
  have hx := exp_one_sub_le_of_ge_eighteen (n := r - d) (by omega)
  have hFx : Real.exp (3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ))) * hp2ExtFacS r d ≤ 1.000101 := by
    unfold hp2ExtFacS
    rw [← Real.exp_add]
    exact exp_le_one_000101 (by linarith)
  have hL := one_sub_exp_neg_one_le
  have hL0 := one_sub_exp_neg_one_pos
  have hfac0 : 0 ≤ 1 + d / (m : ℝ) := by positivity
  have he := hp2WinE_spec d hd4 hd
  have he0 : 0 ≤ hp2WinE d := le_trans (Real.exp_pos _).le he
  have hF0 : 0 ≤ hp2ExtFacS r d := (Real.exp_pos _).le
  have hEF : Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
      * hp2ExtFacS r d ≤ hp2WinE d * 1.000101 := by
    rw [Real.exp_add, mul_assoc]
    exact mul_le_mul he hFx (mul_nonneg (Real.exp_pos _).le hF0) he0
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  obtain ⟨hC0, _⟩ := hp2Win_tables_four hj
  have hw0 : 0 ≤ hp2CellEnd j - hp2CellEnd (j + 1) :=
    sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j))
  have hWj := hp2WinW_spec hj
  have hW0 : 0 ≤ hp2WinW j := le_trans (by positivity) hWj
  have hBj := hp2WinB_spec d hd4 hd j hj
  have hBt0 := hp2PrefixBound_nonneg d (c := max (hp2PostCh4 j) 1.05)
    (le_trans (by norm_num) (le_max_right _ _))
  have hc := hp2WinCell_band_le_four (r := r) (d := d) (j := j)
    (β := 2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ))) hd4 (by omega) hj
    (by linarith [show (0 : ℝ) < 1 / 10 ^ 8 by norm_num])
  -- the regular term
  have hR : (r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
      * hp2PrefixBound d (max (hp2PostCh4 j) 1.05)
      ≤ (1 + d / (m : ℝ)) * (hp2PostC04 j * K) * hp2WinB d j :=
    mul_le_mul (mul_le_mul hfac (mul_le_mul_of_nonneg_left hk hC0) (by positivity) hfac0)
      hBj hBt0 (by positivity)
  have hY : Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
      * hp2ExtFacS r d * (2 * (1 - Real.exp (-1)))
      * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1)))
      ≤ hp2WinE d * 1.000101 * (2 * 0.632121) * hp2WinW j :=
    mul_le_mul (mul_le_mul hEF (by linarith) (by positivity) (by positivity)) hWj
      (by positivity) (by positivity)
  calc (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      = (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j) * hp2ExtFacS r d := by ring
    _ ≤ min ((r : ℝ) / ((r - d : ℕ) : ℝ) * (hp2PostC04 j * hp2Kappa4 (hp2WinN r d))
            * hp2PrefixBound d (max (hp2PostCh4 j) 1.05))
          ((r : ℝ) * (hp2PrefixBound d 1.05 / 1.05 ^ 2))
        * (Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
          * (2 * (1 - Real.exp (-1)))
          * (Real.exp (hp2WinE4 j) * (hp2CellEnd j - hp2CellEnd (j + 1))))
        * hp2ExtFacS r d := mul_le_mul_of_nonneg_right hc hF0
    _ ≤ ((1 + d / (m : ℝ)) * (hp2PostC04 j * K) * hp2WinB d j)
        * (hp2WinE d * 1.000101 * (2 * 0.632121) * hp2WinW j) := by
        rw [mul_assoc]
        exact mul_le_mul ((min_le_left _ _).trans hR) (le_of_eq_of_le (by ring) hY)
          (by positivity) (le_trans (by positivity) hR)
    _ = (1 + d / (m : ℝ)) * (K / 2.023923) * 1.000101 * hp2WinE d
        * (hp2PostC04 j * 2.023923 * (2 * 0.632121) * hp2WinW j * hp2WinB d j) := by ring

/-- **Region II's depths with weights**: for `12 ≤ D ≤ 200` and weights `w_d ≥ 0`,
`∑_{4≤d<D} w_d·hp2WinE d·∑_j C₀(j)·2.023923·(2·0.632121)·hp2WinW j·hp2WinB d j
  ≤ A_pw∑_{4≤d<12} w_d e_d + 1.00004·A_sl κ₄(1000)∑_{12≤d<D} w_d g_d` — `RMF.hp2WinII_le`'s
factorisation with the weights `w_d` in place of `1 + d/(r₀ - 200)`. -/
theorem hp2WinIIS_sum_le {D : ℕ} (hD : 12 ≤ D) (hD200 : D ≤ 200) {w : ℕ → ℝ}
    (hw : ∀ d ∈ Finset.Ico 4 D, 0 ≤ w d) :
    ∑ d ∈ Finset.Ico 4 D, w d * hp2WinE d
        * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * hp2WinW j
          * hp2WinB d j
      ≤ 110.1056 * ∑ d ∈ Finset.Ico 4 12, w d * hp2WinE2 d
        + 1.00004 * 747.8028 * ∑ d ∈ Finset.Ico 12 D, w d * hp2WinG d := by
  rw [← Finset.sum_Ico_consecutive _ (show 4 ≤ 12 by norm_num) hD]
  have hlow : ∀ d ∈ Finset.Ico 4 12, w d * hp2WinE d
        * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * hp2WinW j
          * hp2WinB d j
      = w d * hp2WinE2 d * hp2WinSApw := by
    intro d hd
    have h := (Finset.mem_Ico.1 hd).2
    simp only [hp2WinE, hp2WinB, if_pos h, hp2WinSApw]
  have hhigh : ∀ d ∈ Finset.Ico 12 D, w d * hp2WinE d
        * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * hp2WinW j
          * hp2WinB d j
      = 1.00004 * hp2WinSAslK * (w d * hp2WinG d) := by
    intro d hd
    have h : ¬ d < 12 := by have := (Finset.mem_Ico.1 hd).1; omega
    simp only [hp2WinE, hp2WinB, if_neg h]
    have e : ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121) * hp2WinW j
          * (hp2SlabPrefHat (max (hp2PostCh4 j) 1.05) * hp2WinG d)
        = hp2WinSAslK * hp2WinG d := by
      rw [hp2WinSAslK, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    ring
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, ← Finset.sum_mul, ← Finset.mul_sum]
  have hE0 : 0 ≤ ∑ d ∈ Finset.Ico 4 12, w d * hp2WinE2 d := Finset.sum_nonneg fun d hd => by
    have hd := Finset.mem_Ico.1 hd
    exact mul_nonneg (hw d (Finset.mem_Ico.2 ⟨hd.1, by omega⟩))
      ((Real.exp_pos _).le.trans (hp2WinE2_spec hd.1 hd.2))
  have hG0 : 0 ≤ ∑ d ∈ Finset.Ico 12 D, w d * hp2WinG d := Finset.sum_nonneg fun d hd => by
    have hd := Finset.mem_Ico.1 hd
    exact mul_nonneg (hw d (Finset.mem_Ico.2 ⟨by omega, hd.2⟩)) (hp2WinG_nonneg hd.1 (by omega))
  calc (∑ d ∈ Finset.Ico 4 12, w d * hp2WinE2 d) * hp2WinSApw
        + 1.00004 * hp2WinSAslK * ∑ d ∈ Finset.Ico 12 D, w d * hp2WinG d
      ≤ (∑ d ∈ Finset.Ico 4 12, w d * hp2WinE2 d) * 110.1056
        + 1.00004 * 747.8028 * ∑ d ∈ Finset.Ico 12 D, w d * hp2WinG d :=
        add_le_add (mul_le_mul_of_nonneg_left hp2WinSApw_le hE0)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2WinSAslK_le (by norm_num))
            hG0)
    _ = _ := by ring

/-! ### The far depths `D ≤ d ≤ r - N` -/

/-- **The far depths' slab majorant**: the slab values `hp2WinG d` below depth `200`,
`3.8568/(d√d)` from there. -/
noncomputable def hp2FarG (d : ℕ) : ℝ :=
  if d < 200 then hp2WinG d else 3.8568 / ((d : ℝ) * √(d : ℝ))

/-- `hp2PrefixBound d c ≤ hp2SlabPrefHat c·hp2FarG d` from depth `12` (`RMF.hp2WinG_spec`,
`RMF.hp2PrefixBound_le_G`). -/
lemma hp2PrefixBound_le_farG {d : ℕ} (hd : 12 ≤ d) {c : ℝ} (hc : 0 ≤ c) :
    hp2PrefixBound d c ≤ hp2SlabPrefHat c * hp2FarG d := by
  unfold hp2FarG
  split_ifs with h
  · exact (min_le_right _ _).trans (hp2WinG_spec hd h hc)
  · exact hp2PrefixBound_le_G (by omega) hc

/-- The far depths' slab majorant is nonnegative from depth `12`. -/
lemma hp2FarG_nonneg {d : ℕ} (hd : 12 ≤ d) : 0 ≤ hp2FarG d := by
  unfold hp2FarG
  split_ifs with h
  · exact hp2WinG_nonneg hd h
  · positivity

/-- **A far depth on short tubes**: for `17 ≤ d`, `18 ≤ N ≤ 1000`, `d + N ≤ r` and
`1 ≤ K²·hp2WinX 4 N`, `∑_j r·hp2WinCell r d j·hp2ExtFacS r d·hp2Band(40d + j)
  ≤ 1.000101·K·369.4819·(r/(r - d))·hp2FarG d` (the regular post bound, `κ₄(n₀) ≤ κ₄(N)`). -/
theorem hp2FarS_depth_le {r d N : ℕ} (hd : 17 ≤ d) (hN : 18 ≤ N) (hN1000 : N ≤ 1000)
    (hdr : d + N ≤ r) {K : ℝ} (hK0 : 0 ≤ K) (hK : 1 ≤ K ^ 2 * hp2WinX 4 N) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      ≤ 1.000101 * K * 369.4819 * ((r : ℝ) / ((r : ℝ) - d) * hp2FarG d) := by
  have h := hp2WinCell_sum_le_of_slab (r := r) (d := d) (by omega) (by omega)
    (hp2FarG_nonneg (by omega)) (fun c hc => hp2PrefixBound_le_farG (by omega) hc)
    (fun j hj => hp2WinW_spec hj) hp2WinSAsl_le hp2WinSAt_le
  have hk : hp2Kappa4 (hp2WinN r d) ≤ K :=
    hp2Kappa4_le_of (by omega)
      (by unfold hp2WinN; simp [hp2PostStart, show 4 ≤ d by omega]; omega) hK0 hK
  have hk0 := hp2Kappa4_nonneg (hp2WinN r d)
  have hNr : ((r - d : ℕ) : ℝ) = (r : ℝ) - d := by push_cast [show d ≤ r by omega]; ring
  have hrd : (0 : ℝ) < (r : ℝ) - d := by
    rw [← hNr]; exact_mod_cast (show 0 < r - d by omega)
  have hx := exp_one_sub_le_of_ge_eighteen (n := r - d) (by omega)
  have hy := exp_one_sub_le_of_ge (n := d) hd
  have hF0 : 0 ≤ hp2ExtFacS r d := (Real.exp_pos _).le
  have hEF : Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
      * hp2ExtFacS r d ≤ 1.000101 := by
    unfold hp2ExtFacS
    rw [← Real.exp_add]
    exact exp_le_one_000101 (by linarith)
  have hg0 := hp2FarG_nonneg (d := d) (by omega)
  have hsum : ∑ j ∈ Finset.range 40,
      (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      = hp2ExtFacS r d * ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmin : min ((r : ℝ) / ((r - d : ℕ) : ℝ) * hp2Kappa4 (hp2WinN r d) * 369.4819)
      ((r : ℝ) * 103.0756) ≤ (r : ℝ) / ((r : ℝ) - d) * K * 369.4819 := by
    refine (min_le_left _ _).trans ?_
    rw [hNr]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by positivity)) (by norm_num)
  rw [hsum]
  calc hp2ExtFacS r d * ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r d j * hp2Band (40 * d + j)
      ≤ hp2ExtFacS r d * (hp2FarG d
          * Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
          * ((r : ℝ) / ((r : ℝ) - d) * K * 369.4819)) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hmin
          (mul_nonneg hg0 (Real.exp_pos _).le))) hF0
    _ = (Real.exp (2 * Real.exp (1 - d) + 3.1 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
          * hp2ExtFacS r d) * (K * 369.4819 * ((r : ℝ) / ((r : ℝ) - d) * hp2FarG d)) := by ring
    _ ≤ 1.000101 * (K * 369.4819 * ((r : ℝ) / ((r : ℝ) - d) * hp2FarG d)) :=
        mul_le_mul_of_nonneg_right hEF (by positivity)
    _ = _ := by ring

/-- **The far depths' sum on a cell below the tail**: for `12 ≤ D`, `1 ≤ N ≤ r < ρ'` and
`ρ' ≤ N + 200`, `∑_{D≤d≤r-N} (r/(r - d))·hp2FarG d ≤ ∑_{D≤d<ρ'-N} (1 + d/N)·hp2WinG d`
(`r/(r - d) ≤ 1 + d/N` for `r - d ≥ N`, and the terms up to `ρ' - N` nonnegative). -/
theorem hp2FarSum_le_table {D N r ρ' : ℕ} (hD : 12 ≤ D) (hN : 1 ≤ N) (hNr : N ≤ r) (hr : r < ρ')
    (hρ' : ρ' ≤ N + 200) :
    ∑ d ∈ Finset.Ico D (r - N + 1), (r : ℝ) / ((r : ℝ) - d) * hp2FarG d
      ≤ ∑ d ∈ Finset.Ico D (ρ' - N), (1 + d / (N : ℝ)) * hp2WinG d := by
  have hsub : Finset.Ico D (r - N + 1) ⊆ Finset.Ico D (ρ' - N) :=
    Finset.Ico_subset_Ico_right (by omega)
  refine (Finset.sum_le_sum fun d hd => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => ?_)
  · have hd := Finset.mem_Ico.1 hd
    have h200 : d < 200 := by omega
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hdN : (d : ℝ) + N ≤ r := by exact_mod_cast (show d + N ≤ r by omega)
    have hg0 := hp2WinG_nonneg (show 12 ≤ d by omega) h200
    have hfar : hp2FarG d = hp2WinG d := by unfold hp2FarG; rw [if_pos h200]
    rw [hfar]
    refine mul_le_mul_of_nonneg_right ?_ hg0
    rw [div_le_iff₀ (by linarith)]
    have h1 : (d : ℝ) / N * ((r : ℝ) - d) ≥ d := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    nlinarith
  · have hd := Finset.mem_Ico.1 hd
    exact mul_nonneg (by positivity) (hp2WinG_nonneg (by omega) (by omega))

/-- **The far sum's part `d ≤ r/2` from `r ≥ 402`**: `RMF.sum_far_low_le`'s argument, which needs
only `200 < r - ⌊r/2⌋`. -/
lemma sum_far_low_le_of_ge {r : ℕ} (hr : 402 ≤ r) :
    ∑ d ∈ Finset.Ico 200 (r - r / 2), 1 / (((r : ℝ) - d) * √(d : ℝ)) ≤ 2.1214 / √(r : ℝ) := by
  have hr' : (402 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hh1 : ((r / 2 : ℕ) : ℝ) ≤ r / 2 := by
    have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
    have : (2 : ℝ) * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hh2 : (r : ℝ) / 2 - 1 ≤ ((r / 2 : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := r) (b := 2) (by norm_num)
    have : (r : ℝ) < (r / 2 : ℕ) * 2 + 2 := by exact_mod_cast this
    linarith
  have hB : ((r - r / 2 : ℕ) : ℝ) = (r : ℝ) - ((r / 2 : ℕ) : ℝ) := by
    push_cast [Nat.div_le_self r 2]
    ring
  have hpt : ∀ d ∈ Finset.Ico 200 (r - r / 2), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ 1 / (r : ℝ) * (1 / √(d : ℝ)) + 2 / (r : ℝ) ^ 2 * √(d : ℝ) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hd0 : (0 : ℝ) < d := by
      have : (200 : ℝ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hdr : (d : ℝ) ≤ r / 2 := by
      have : (d : ℝ) + 1 ≤ ((r - r / 2 : ℕ) : ℝ) := by exact_mod_cast hd.2
      linarith
    exact one_div_sub_mul_sqrt_le hd0 hdr
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA := sum_Ico_one_div_sqrt_le (A := 200) (B := r - r / 2) (by norm_num) (by omega)
  have hBs := sum_Ico_sqrt_le (A := 200) (B := r - r / 2) (by omega)
  have hc : ((r - r / 2 : ℕ) : ℝ) - 1 ≤ r / 2 := by linarith
  have hs1 : √(((r - r / 2 : ℕ) : ℝ) - 1) ≤ √((r : ℝ) / 2) := Real.sqrt_le_sqrt hc
  have hcnt : ((r - r / 2 : ℕ) : ℝ) - 200 ≤ r / 2 := by linarith
  have hs0 := Real.sqrt_nonneg (((r - r / 2 : ℕ) : ℝ) - 1)
  have hsh := Real.sqrt_nonneg ((r : ℝ) / 2)
  have hcnt0 : (0 : ℝ) ≤ ((r - r / 2 : ℕ) : ℝ) - 200 := by linarith
  have e1 : 1 / (r : ℝ) * ∑ d ∈ Finset.Ico 200 (r - r / 2), 1 / √(d : ℝ)
      ≤ 1 / (r : ℝ) * (2 * √((r : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left (hA.trans (by linarith)) (by positivity)
  have e2 : 2 / (r : ℝ) ^ 2 * ∑ d ∈ Finset.Ico 200 (r - r / 2), √(d : ℝ)
      ≤ 2 / (r : ℝ) ^ 2 * ((r / 2) * √((r : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left (hBs.trans (mul_le_mul hcnt hs1 hs0 (by positivity)))
      (by positivity)
  have e3 : 1 / (r : ℝ) * (2 * √((r : ℝ) / 2)) + 2 / (r : ℝ) ^ 2 * ((r / 2) * √((r : ℝ) / 2))
      = 3 * √((r : ℝ) / 2) / r := by
    field_simp
    ring
  have := three_mul_sqrt_half_div_le hr0
  linarith

/-- **The far sum's part `r - d ≤ r/2` from `r ≥ 402`**: `RMF.sum_far_high_le`'s argument. -/
lemma sum_far_high_le_of_ge {r : ℕ} (hr : 402 ≤ r) :
    ∑ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ) := by
  have hr' : (402 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hsr := Real.sqrt_pos.2 hr0
  have hh1 : ((r / 2 : ℕ) : ℝ) ≤ r / 2 := by
    have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
    have : (2 : ℝ) * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hh2 : (r : ℝ) / 2 - 1 ≤ ((r / 2 : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := r) (b := 2) (by norm_num)
    have : (r : ℝ) < (r / 2 : ℕ) * 2 + 2 := by exact_mod_cast this
    linarith
  have hA : ((r - r / 2 : ℕ) : ℝ) = (r : ℝ) - ((r / 2 : ℕ) : ℝ) := by
    push_cast [Nat.div_le_self r 2]
    ring
  have hpt : ∀ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
      ≤ 1 / √(r : ℝ) * (1 / ((r : ℝ) - d) + 1 / (r : ℝ)) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hn : (r : ℝ) - d ≤ r / 2 := by
      have : ((r - r / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hn0 : 0 < (r : ℝ) - d := by
      have : d + 59 < r := by omega
      have : (d : ℝ) + 59 < r := by exact_mod_cast this
      linarith
    have h := one_div_mul_sqrt_sub_le hn0 hn
    rw [sub_sub_cancel] at h
    exact h
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hlog := sum_Ico_one_div_sub_le (r := r) (A := r - r / 2) (B := r - 59) (by omega)
    (by omega)
  have e1 : (r : ℝ) - ((r - r / 2 : ℕ) : ℝ) = ((r / 2 : ℕ) : ℝ) := by rw [hA]; ring
  have e2 : (r : ℝ) - ((r - 59 : ℕ) : ℝ) = 59 := by push_cast [show 59 ≤ r by omega]; ring
  rw [e1, e2] at hlog
  have hhpos : (0 : ℝ) < ((r / 2 : ℕ) : ℝ) := by linarith
  have hl : Real.log ((r / 2 : ℕ) : ℝ) - Real.log 59 ≤ Real.log ((r : ℝ) / 118) := by
    rw [← Real.log_div hhpos.ne' (by norm_num)]
    exact Real.log_le_log (by positivity)
      (by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith)
  have hcnt : (((r - 59 - (r - r / 2) : ℕ) : ℝ)) * (1 / (r : ℝ)) ≤ 1 / 2 := by
    have hle : ((r - 59 - (r - r / 2) : ℕ) : ℝ) ≤ r / 2 := by
      have : r - 59 - (r - r / 2) ≤ r / 2 := by omega
      have : ((r - 59 - (r - r / 2) : ℕ) : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [mul_one_div, div_le_iff₀ hr0]
    linarith
  have hsum : ∑ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / ((r : ℝ) - d)
      + ((r - 59 - (r - r / 2) : ℕ) : ℝ) * (1 / (r : ℝ))
      ≤ Real.log ((r : ℝ) / 118) + 1 / 2 := by linarith
  calc 1 / √(r : ℝ) * (∑ d ∈ Finset.Ico (r - r / 2) (r - 59), 1 / ((r : ℝ) - d)
        + ((r - 59 - (r - r / 2) : ℕ) : ℝ) * (1 / (r : ℝ)))
      ≤ 1 / √(r : ℝ) * (Real.log ((r : ℝ) / 118) + 1 / 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ) := by ring

/-- `(log(r/118) + 0.6214)/√r ≤ 0.09243` for every `r > 0` (the maximum sits at `r = 118e^{1.3786}`;
`log y ≤ 2(√y - 1)` at `y = r/468.25`). -/
lemma log_div_add_div_sqrt_le {r : ℝ} (hr : 0 < r) :
    (Real.log (r / 118) + 0.6214) / √r ≤ 0.09243 := by
  have hs := Real.sqrt_pos.2 hr
  have hy : 0 < r / 468.25 := by positivity
  have hl := log_le_two_mul_sqrt_sub_one hy
  have hc : Real.log (468.25 / 118) ≤ 1.3786 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    interval_decide (trust := kernel)
  have hsplit : Real.log (r / 118) = Real.log (r / 468.25) + Real.log (468.25 / 118) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hsq : √(r / 468.25) = √r / √468.25 := Real.sqrt_div' r (by norm_num)
  have hk : 2 / √468.25 ≤ 2 * 0.046215 :=
    div_sqrt_le_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [div_le_iff₀ hs]
  rw [hsq] at hl
  have h1 : Real.log (r / 118) + 0.6214 ≤ 2 / √468.25 * √r := by
    rw [hsplit]
    have e : 2 * (√r / √468.25 - 1) = 2 / √468.25 * √r - 2 := by ring
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hk hs.le]

/-- **The far sum from depth `200` on tubes of `r ≥ 260` blocks**:
`∑_{200≤d<r-59} r/((r - d)d√d) ≤ 2/√199 + 0.09243` — from `r ≥ 402` `RMF.sum_far_le`'s split and
`RMF.log_div_add_div_sqrt_le`; below, `√d ≥ √200` and `∑_d 1/(r - d) ≤ log(201/59)`. -/
theorem sum_far_le_of_ge {r : ℕ} (hr : 260 ≤ r) :
    ∑ d ∈ Finset.Ico 200 (r - 59), (r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))
      ≤ 2 / √199 + 0.09243 := by
  have hr' : (260 : ℝ) ≤ r := by exact_mod_cast hr
  have hsplit : ∀ d ∈ Finset.Ico 200 (r - 59),
      (r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))
        = 1 / ((d : ℝ) * √(d : ℝ)) + 1 / (((r : ℝ) - d) * √(d : ℝ)) := by
    intro d hd
    have hd := Finset.mem_Ico.1 hd
    have hd0 : (0 : ℝ) < d := by
      have : (200 : ℝ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hrd : (0 : ℝ) < (r : ℝ) - d := by
      have : d + 59 < r := by omega
      have : (d : ℝ) + 59 < r := by exact_mod_cast this
      linarith
    exact div_sub_mul_eq hd0 hrd
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hi := sum_Ico_one_div_mul_sqrt_le (a := 200) (b := r - 59) (by norm_num) (by omega)
  have hb : ((r - 59 : ℕ) : ℝ) - 1 = (r : ℝ) - 60 := by push_cast [show 59 ≤ r by omega]; ring
  have h199 : ((200 : ℕ) : ℝ) - 1 = 199 := by norm_num
  rw [hb, h199] at hi
  have hs60 : 0 ≤ 2 / √((r : ℝ) - 60) := by positivity
  rcases le_or_gt 402 r with h402 | h402
  · have hi' : 2 / √(r : ℝ) ≤ 2 / √((r : ℝ) - 60) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by linarith))
        (Real.sqrt_le_sqrt (by linarith))
    have h2 : ∑ d ∈ Finset.Ico 200 (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
        ≤ 2.1214 / √(r : ℝ) + (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ) := by
      rw [← Finset.Ico_union_Ico_eq_Ico (b := r - r / 2) (by omega) (by omega),
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
      exact add_le_add (sum_far_low_le_of_ge h402) (sum_far_high_le_of_ge h402)
    have hmax := log_div_add_div_sqrt_le (r := (r : ℝ)) (by linarith)
    have e : 2.1214 / √(r : ℝ) + (Real.log ((r : ℝ) / 118) + 1 / 2) / √(r : ℝ)
        = (Real.log ((r : ℝ) / 118) + 0.6214) / √(r : ℝ) + 2 / √(r : ℝ) := by ring
    linarith
  · have hpt : ∀ d ∈ Finset.Ico 200 (r - 59), 1 / (((r : ℝ) - d) * √(d : ℝ))
        ≤ 1 / ((r : ℝ) - d) * (1 / √200) := by
      intro d hd
      have hd := Finset.mem_Ico.1 hd
      have hd200 : (200 : ℝ) ≤ d := by exact_mod_cast hd.1
      have hrd : (0 : ℝ) < (r : ℝ) - d := by
        have : d + 59 < r := by omega
        have : (d : ℝ) + 59 < r := by exact_mod_cast this
        linarith
      have hs : √200 ≤ √(d : ℝ) := Real.sqrt_le_sqrt hd200
      have hs0 : 0 < √(200 : ℝ) := Real.sqrt_pos.2 (by norm_num)
      rw [one_div_mul_one_div]
      exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hs hrd.le)
    have hlog := sum_Ico_one_div_sub_le (r := r) (A := 200) (B := r - 59) (by omega) (by omega)
    have e2 : (r : ℝ) - ((r - 59 : ℕ) : ℝ) = 59 := by push_cast [show 59 ≤ r by omega]; ring
    rw [e2] at hlog
    have hr401 : (r : ℝ) ≤ 401 := by exact_mod_cast (show r ≤ 401 by omega)
    have hl1 : Real.log ((r : ℝ) - ((200 : ℕ) : ℝ)) ≤ Real.log 201 :=
      Real.log_le_log (by push_cast; linarith) (by push_cast; linarith)
    have hl2 : Real.log 201 - Real.log 59 ≤ 1.2259 := by
      rw [← Real.log_div (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
      interval_decide (trust := kernel)
    have hk : 1 / √(200 : ℝ) ≤ 0.070711 := by
      simpa using div_sqrt_le_mul (C := 1) (x := 200) (κ := 0.070711) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    have hS0 : 0 ≤ ∑ d ∈ Finset.Ico 200 (r - 59), 1 / ((r : ℝ) - d) :=
      Finset.sum_nonneg fun d hd => by
        have hd := Finset.mem_Ico.1 hd
        have : (d : ℝ) + 59 < r := by exact_mod_cast (show d + 59 < r by omega)
        exact div_nonneg (by norm_num) (by linarith)
    have hsum := Finset.sum_le_sum hpt
    rw [← Finset.sum_mul] at hsum
    have hS : ∑ d ∈ Finset.Ico 200 (r - 59), 1 / ((r : ℝ) - d) ≤ 1.2259 :=
      (hlog.trans (sub_le_sub_right hl1 _)).trans hl2
    have hprod : (∑ d ∈ Finset.Ico 200 (r - 59), 1 / ((r : ℝ) - d)) * (1 / √200)
        ≤ 1.2259 * 0.070711 :=
      mul_le_mul hS hk (by positivity) (by norm_num)
    linarith

/-- **The far depths' sum on the tail cell**: for `12 ≤ D ≤ 200`, `N = 60` and `r ≥ 260`,
`∑_{D≤d≤r-60} (r/(r - d))·hp2FarG d ≤ ∑_{D≤d<200}(1 + d/60)·hp2WinG d + 3.8568(2/√199 + 0.09243)`
(`RMF.sum_far_le_of_ge` from depth `200`). -/
theorem hp2FarSum_le_tail {D r : ℕ} (hD : 12 ≤ D) (hD200 : D ≤ 200) (hr : 260 ≤ r) :
    ∑ d ∈ Finset.Ico D (r - 60 + 1), (r : ℝ) / ((r : ℝ) - d) * hp2FarG d
      ≤ ∑ d ∈ Finset.Ico D 200, (1 + d / (60 : ℝ)) * hp2WinG d
        + 3.8568 * (2 / √199 + 0.09243) := by
  rw [← Finset.sum_Ico_consecutive _ hD200 (show 200 ≤ r - 60 + 1 by omega)]
  refine add_le_add (Finset.sum_le_sum fun d hd => ?_) ?_
  · have hd := Finset.mem_Ico.1 hd
    have hdN : (d : ℝ) + 60 ≤ r := by exact_mod_cast (show d + 60 ≤ r by omega)
    have hg0 := hp2WinG_nonneg (show 12 ≤ d by omega) hd.2
    have hfar : hp2FarG d = hp2WinG d := by unfold hp2FarG; rw [if_pos hd.2]
    rw [hfar]
    refine mul_le_mul_of_nonneg_right ?_ hg0
    rw [div_le_iff₀ (by linarith)]
    have h1 : (d : ℝ) / 60 * ((r : ℝ) - d) ≥ d := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    nlinarith
  · have e : ∀ d ∈ Finset.Ico 200 (r - 60 + 1), (r : ℝ) / ((r : ℝ) - d) * hp2FarG d
        = 3.8568 * ((r : ℝ) / (((r : ℝ) - d) * ((d : ℝ) * √(d : ℝ)))) := by
      intro d hd
      have h200 : ¬ d < 200 := by have := (Finset.mem_Ico.1 hd).1; omega
      unfold hp2FarG
      rw [if_neg h200, div_mul_div_comm, mul_comm (r : ℝ) 3.8568, mul_div_assoc]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, show r - 60 + 1 = r - 59 by omega]
    exact mul_le_mul_of_nonneg_left (sum_far_le_of_ge hr) (by norm_num)

/-! ### The short posts `r - d < N` -/

/-- **A short post on short tubes**: for `3 ≤ n < 60` and `n + 18 ≤ r₀ ≤ r`, the depth
`d = r - n`: `∑_j r·hp2WinCell r d j·hp2ExtFacS r d·hp2Band(40d + j)
  ≤ 1.000101·(r₀·hp2SlabG (r₀ - n))·hp2ExtPsi n` (the better of the two post bounds,
`RMF.hp2ExtPsi_spec`, and `r·hp2SlabG (r - n) ≤ r₀·hp2SlabG (r₀ - n)`). -/
theorem hp2NearS_depth_le {r₀ r n : ℕ} (hn : 3 ≤ n) (hn60 : n < 60) (h : n + 18 ≤ r₀)
    (hr : r₀ ≤ r) :
    ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r (r - n) j * hp2ExtFacS r (r - n)
        * hp2Band (40 * (r - n) + j)
      ≤ 1.000101 * ((r₀ : ℝ) * hp2SlabG (r₀ - n)) * hp2ExtPsi n := by
  have hd18 : 18 ≤ r - n := by omega
  have hc := hp2WinCell_sum_le_of_slab (r := r) (d := r - n) (by omega) (by omega)
    (hp2SlabG_nonneg (r - n)) (fun c hc => hp2PrefixBound_le_slabG (by omega) hc)
    (fun j hj => hp2WinW_spec hj) hp2WinSAsl_le hp2WinSAt_le
  have hrn : r - (r - n) = n := by omega
  have hWN : hp2WinN r (r - n) = n := by
    unfold hp2WinN; simp [hp2PostStart, show 4 ≤ r - n by omega]; omega
  rw [hWN, hrn] at hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hmin : min ((r : ℝ) / (n : ℝ) * hp2Kappa4 n * 369.4819) ((r : ℝ) * 103.0756)
      = (r : ℝ) * min (hp2Kappa4 n * 369.4819 / n) 103.0756 := by
    rw [mul_min_of_nonneg _ _ hr0]
    congr 1
    field_simp
  rw [hmin] at hc
  have hF : hp2ExtFacS r (r - n)
      * Real.exp (2 * Real.exp (1 - ((r - n : ℕ) : ℝ)) + 3.1 * Real.exp (1 - (n : ℝ)))
      = Real.exp (2 * Real.exp (1 - ((r - n : ℕ) : ℝ)) + 1 / 10 ^ 4 - 1 / 10 ^ 19)
        * Real.exp (7.1 * Real.exp (1 - (n : ℝ)) + 1 / 10 ^ 19) := by
    unfold hp2ExtFacS
    rw [hrn, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hd' := exp_one_sub_le_of_ge_eighteen (n := r - n) hd18
  have hE1 : Real.exp (2 * Real.exp (1 - ((r - n : ℕ) : ℝ)) + 1 / 10 ^ 4 - 1 / 10 ^ 19)
      ≤ 1.000101 := exp_le_one_000101 (by linarith)
  have hpsi := hp2ExtPsi_spec hn hn60
  have hmono := add_mul_hp2SlabG_anti (M := r₀ - n) (M' := r - n) (by omega) (by omega)
    (x := (n : ℝ)) (Nat.cast_nonneg n)
  have hc1 : ((r - n : ℕ) : ℝ) + n = r := by push_cast [show n ≤ r by omega]; ring
  have hc2 : ((r₀ - n : ℕ) : ℝ) + n = r₀ := by push_cast [show n ≤ r₀ by omega]; ring
  rw [hc1, hc2] at hmono
  have hg0 := hp2SlabG_nonneg (r - n)
  have hF0 : 0 ≤ hp2ExtFacS r (r - n) := (Real.exp_pos _).le
  have hmin0 : 0 ≤ min (hp2Kappa4 n * 369.4819 / n) 103.0756 :=
    le_min (by have := hp2Kappa4_nonneg n; positivity) (by norm_num)
  have hsum : ∑ j ∈ Finset.range 40, (r : ℝ) * hp2WinCell r (r - n) j * hp2ExtFacS r (r - n)
        * hp2Band (40 * (r - n) + j)
      = hp2ExtFacS r (r - n) * ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r (r - n) j * hp2Band (40 * (r - n) + j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  calc hp2ExtFacS r (r - n) * ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r (r - n) j * hp2Band (40 * (r - n) + j)
      ≤ hp2ExtFacS r (r - n) * (hp2SlabG (r - n)
          * Real.exp (2 * Real.exp (1 - ((r - n : ℕ) : ℝ)) + 3.1 * Real.exp (1 - (n : ℝ)))
          * ((r : ℝ) * min (hp2Kappa4 n * 369.4819 / n) 103.0756)) :=
        mul_le_mul_of_nonneg_left hc hF0
    _ = (hp2ExtFacS r (r - n)
          * Real.exp (2 * Real.exp (1 - ((r - n : ℕ) : ℝ)) + 3.1 * Real.exp (1 - (n : ℝ))))
        * ((r : ℝ) * hp2SlabG (r - n)) * min (hp2Kappa4 n * 369.4819 / n) 103.0756 := by ring
    _ = Real.exp (2 * Real.exp (1 - ((r - n : ℕ) : ℝ)) + 1 / 10 ^ 4 - 1 / 10 ^ 19)
        * ((r : ℝ) * hp2SlabG (r - n))
        * (Real.exp (7.1 * Real.exp (1 - (n : ℝ)) + 1 / 10 ^ 19)
          * min (hp2Kappa4 n * 369.4819 / n) 103.0756) := by rw [hF]; ring
    _ ≤ 1.000101 * ((r₀ : ℝ) * hp2SlabG (r₀ - n)) * hp2ExtPsi n :=
        mul_le_mul (mul_le_mul hE1 hmono (mul_nonneg hr0 hg0) (by norm_num)) hpsi
          (mul_nonneg (Real.exp_pos _).le hmin0)
          (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (hp2SlabG_nonneg _)))

/-! ### The deep cells and below -/

/-- **The deep constant against the scale on short tubes**: for `17 ≤ ρ ≤ r`,
`r·hp2WinDeep r·e^{-(r-2)} ≤ 6.682553·hp2SlabPrefHat 1.05·(ρ·hp2SlabG ρ)/1.05²`
(`RMF.exp_deep_le`, `RMF.hp2PrefixBound_le_slabG`, `RMF.mul_hp2SlabG_anti`). -/
lemma mul_hp2WinDeep_exp_le_short {ρ r : ℕ} (hρ : 17 ≤ ρ) (hr : ρ ≤ r) :
    (r : ℝ) * hp2WinDeep r * Real.exp (-((r : ℝ) - 2))
      ≤ 6.682553 * hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) / 1.05 ^ 2 := by
  have hB := hp2PrefixBound_le_slabG (M := r) (by omega) (c := 1.05) (by norm_num)
  have hB0 := hp2PrefixBound_nonneg r (c := 1.05) (by norm_num)
  have hP0 := hp2SlabPrefHat_nonneg (c := 1.05) (by norm_num)
  have hmono := mul_hp2SlabG_anti hρ hr
  have hexp : Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20)
      * Real.exp (-((r : ℝ) - 2)) ≤ 6.682553 := by
    rw [← Real.exp_add]
    refine le_trans (le_of_eq ?_) exp_deep_le
    congr 1
    ring
  have hRB : (r : ℝ) * hp2PrefixBound r 1.05 ≤ hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) :=
    calc (r : ℝ) * hp2PrefixBound r 1.05 ≤ (r : ℝ) * (hp2SlabPrefHat 1.05 * hp2SlabG r) :=
          mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg r)
      _ = hp2SlabPrefHat 1.05 * ((r : ℝ) * hp2SlabG r) := by ring
      _ ≤ hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) := mul_le_mul_of_nonneg_left hmono hP0
  unfold hp2WinDeep
  calc (r : ℝ) * (Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20)
          * hp2PrefixBound r 1.05 / 1.05 ^ 2) * Real.exp (-((r : ℝ) - 2))
      = (Real.exp ((r : ℝ) + 3.72 / 10 ^ 8 - 0.1005 + 5 / 10 ^ 20) * Real.exp (-((r : ℝ) - 2)))
        * ((r : ℝ) * hp2PrefixBound r 1.05) / 1.05 ^ 2 := by ring
    _ ≤ 6.682553 * (hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ)) / 1.05 ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul hexp hRB (mul_nonneg (Nat.cast_nonneg r) hB0)
          (by norm_num)) (by norm_num)
    _ = _ := by ring

/-- **The deep cells and below on short tubes**: for `17 ≤ ρ ≤ r`, the deep cells' constants
`e^{2·hp2ExtB j + 10⁻⁴}` and the saturated `e^{2·5.032 + 10⁻⁴}` contribute at most
`2·0.632121·(6.682553·hp2SlabPrefHat 1.05·(ρ·hp2SlabG ρ)/1.05²)·(1.000101·25.177512)` —
`RMF.hp2ExtDeep_le`'s argument with the average `e^{10⁻⁴}Z` (`RMF.hp2ExtDeepAvgS_le`,
`RMF.hp2ExtZ_le`). -/
theorem hp2DeepS_le {ρ r : ℕ} (hρ : 17 ≤ ρ) (hr : ρ ≤ r) :
    ∑ j ∈ Finset.range 400, (r : ℝ) * hp2WinDeep r * Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4)
        * hp2Band (40 * (r - 2) + j)
      + (r : ℝ) * hp2ExtSatS r 5.032 * hp2PairVol (hp2CellEnd (40 * (r - 2) + 400))
      ≤ 2 * 0.632121 * (6.682553 * hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) / 1.05 ^ 2)
        * (1.000101 * 25.177512) := by
  have hL := one_sub_exp_neg_one_le
  have hL0 := one_sub_exp_neg_one_pos
  set C : ℝ := (r : ℝ) * hp2WinDeep r * Real.exp (-((r : ℝ) - 2)) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (hp2WinDeep_nonneg r)) (Real.exp_pos _).le
  have hCle := mul_hp2WinDeep_exp_le_short hρ hr
  have hr2 : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by push_cast [show 2 ≤ r by omega]; ring
  have he : Real.exp ((r : ℝ) - 2) * Real.exp (-((r : ℝ) - 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hband : ∀ j, hp2Band (40 * (r - 2) + j)
      ≤ Real.exp (-((r : ℝ) - 2))
        * (2 * (1 - Real.exp (-1)) * (hp2CellEnd j - hp2CellEnd (j + 1))) := by
    intro j
    have h := exp_mul_hp2Band_le (r - 2) j
    rw [hr2] at h
    calc hp2Band (40 * (r - 2) + j)
        = Real.exp (-((r : ℝ) - 2)) * (Real.exp ((r : ℝ) - 2) * hp2Band (40 * (r - 2) + j)) := by
          rw [← mul_assoc, mul_comm (Real.exp (-((r : ℝ) - 2))), he, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hlast : hp2PairVol (hp2CellEnd (40 * (r - 2) + 400))
      ≤ Real.exp (-((r : ℝ) - 2)) * (2 * (1 - Real.exp (-1)) * hp2CellEnd 400) := by
    refine (hp2PairVol_le (hp2CellEnd_pos _).le).trans (le_of_eq ?_)
    rw [hp2CellEnd_forty_mul_add, hr2]
    ring
  have hterm : ∀ j ∈ Finset.range 400,
      (r : ℝ) * hp2WinDeep r * Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4) * hp2Band (40 * (r - 2) + j)
      ≤ C * (2 * (1 - Real.exp (-1)))
        * (Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4) * (hp2CellEnd j - hp2CellEnd (j + 1))) := by
    intro j _
    have h0 : 0 ≤ (r : ℝ) * hp2WinDeep r * Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (hp2WinDeep_nonneg r)) (Real.exp_pos _).le
    calc (r : ℝ) * hp2WinDeep r * Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4)
          * hp2Band (40 * (r - 2) + j)
        ≤ (r : ℝ) * hp2WinDeep r * Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4)
          * (Real.exp (-((r : ℝ) - 2)) * (2 * (1 - Real.exp (-1))
            * (hp2CellEnd j - hp2CellEnd (j + 1)))) := mul_le_mul_of_nonneg_left (hband j) h0
      _ = _ := by rw [hC]; ring
  have hsat : (r : ℝ) * hp2ExtSatS r 5.032 * hp2PairVol (hp2CellEnd (40 * (r - 2) + 400))
      ≤ C * (2 * (1 - Real.exp (-1))) * (Real.exp (2 * 5.032 + 1 / 10 ^ 4) * hp2CellEnd 400) := by
    have h0 : 0 ≤ (r : ℝ) * hp2ExtSatS r 5.032 :=
      mul_nonneg (Nat.cast_nonneg r) (hp2ExtSatS_nonneg r 5.032)
    calc (r : ℝ) * hp2ExtSatS r 5.032 * hp2PairVol (hp2CellEnd (40 * (r - 2) + 400))
        ≤ (r : ℝ) * hp2ExtSatS r 5.032
          * (Real.exp (-((r : ℝ) - 2)) * (2 * (1 - Real.exp (-1)) * hp2CellEnd 400)) :=
          mul_le_mul_of_nonneg_left hlast h0
      _ = _ := by rw [hC]; unfold hp2ExtSatS; ring
  have hZ := hp2ExtDeepAvgS_le hp2ExtZ_le
  have hZ0 : 0 ≤ ∑ j ∈ Finset.range 400, Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4)
        * (hp2CellEnd j - hp2CellEnd (j + 1))
      + Real.exp (2 * 5.032 + 1 / 10 ^ 4) * hp2CellEnd 400 :=
    add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le
      (sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j)))) (mul_nonneg (Real.exp_pos _).le
      (hp2CellEnd_pos _).le)
  have he4 : Real.exp (1 / 10 ^ 4) ≤ 1.000101 := exp_le_one_000101 (by norm_num)
  have hZ' : Real.exp (1 / 10 ^ 4) * 25.177512 ≤ 1.000101 * 25.177512 :=
    mul_le_mul_of_nonneg_right he4 (by norm_num)
  calc ∑ j ∈ Finset.range 400, (r : ℝ) * hp2WinDeep r * Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4)
          * hp2Band (40 * (r - 2) + j)
        + (r : ℝ) * hp2ExtSatS r 5.032 * hp2PairVol (hp2CellEnd (40 * (r - 2) + 400))
      ≤ C * (2 * (1 - Real.exp (-1))) * (∑ j ∈ Finset.range 400,
          Real.exp (2 * hp2ExtB j + 1 / 10 ^ 4) * (hp2CellEnd j - hp2CellEnd (j + 1))
          + Real.exp (2 * 5.032 + 1 / 10 ^ 4) * hp2CellEnd 400) := by
        rw [mul_add, Finset.mul_sum]
        exact add_le_add (Finset.sum_le_sum hterm) hsat
    _ ≤ (6.682553 * hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) / 1.05 ^ 2) * (2 * 0.632121)
          * (1.000101 * 25.177512) :=
        mul_le_mul (mul_le_mul hCle (by linarith) (by positivity) (hC0.trans hCle))
          (hZ.trans hZ') hZ0 (mul_nonneg (hC0.trans hCle) (by norm_num))
    _ = _ := by ring

/-! ### All regions -/

/-- **Region I at a rung in numerals**: for `35 ≤ ρ ≤ min(r, 1000)` and
`1 ≤ K_d²·hp2WinX d (ρ - b_d)` (`b = 2, 3, 4, 4`), the depths `d ≤ 3` contribute at most
`1.000101·∑_d (ρ/(ρ - b_d))·K_d·(∑_j hp2WinP d j)/κ̂_d` (`RMF.hp2WinRegionIS_le`). -/
lemma hp2WinRegionIS_le_num {ρ r : ℕ} (hρ : 35 ≤ ρ) (hρ' : ρ ≤ 1000) (hr : ρ ≤ r)
    {K₀ K₁ K₂ K₃ : ℝ} (h₀ : 0 ≤ K₀) (h₀' : 1 ≤ K₀ ^ 2 * hp2WinX 0 (ρ - 2))
    (h₁ : 0 ≤ K₁) (h₁' : 1 ≤ K₁ ^ 2 * hp2WinX 1 (ρ - 3))
    (h₂ : 0 ≤ K₂) (h₂' : 1 ≤ K₂ ^ 2 * hp2WinX 2 (ρ - 4))
    (h₃ : 0 ≤ K₃) (h₃' : 1 ≤ K₃ ^ 2 * hp2WinX 3 (ρ - 4)) :
    ∑ d ∈ Finset.range 4, ∑ j ∈ Finset.range 40,
        (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j)
      ≤ 1.000101 * ((ρ : ℝ) / ((ρ : ℝ) - 2) * K₀ * (5.540237 / 2.02364)
          + (ρ : ℝ) / ((ρ : ℝ) - 3) * K₁ * (204.173191 / 2.022339)
          + (ρ : ℝ) / ((ρ : ℝ) - 4) * K₂ * (209.20073 / 2.021877)
          + (ρ : ℝ) / ((ρ : ℝ) - 4) * K₃ * (349.146933 / 2.023023)) := by
  have b₀ : hp2PostStart 0 = 2 := by simp [hp2PostStart]
  have b₁ : hp2PostStart 1 = 3 := by simp [hp2PostStart]
  have b₂ : hp2PostStart 2 = 4 := by simp [hp2PostStart]
  have b₃ : hp2PostStart 3 = 4 := by simp [hp2PostStart]
  have k₀ : hp2WinKappaHat 0 = 2.02364 := by simp [hp2WinKappaHat]
  have k₁ : hp2WinKappaHat 1 = 2.022339 := by simp [hp2WinKappaHat]
  have k₂ : hp2WinKappaHat 2 = 2.021877 := by simp [hp2WinKappaHat]
  have k₃ : hp2WinKappaHat 3 = 2.023023 := by simp [hp2WinKappaHat]
  have s₀ : ∑ j ∈ Finset.range 40, hp2WinP 0 j = 5.540237 := hp2WinP0_sum
  have s₁ : ∑ j ∈ Finset.range 40, hp2WinP 1 j = 204.173191 := hp2WinP1_sum
  have s₂ : ∑ j ∈ Finset.range 40, hp2WinP 2 j = 209.20073 := hp2WinP2_sum
  have s₃ : ∑ j ∈ Finset.range 40, hp2WinP 3 j = 349.146933 := hp2WinP3_sum
  have e₀ := hp2WinRegionIS_le (r := r) (d := 0) hρ hρ' hr (by norm_num) h₀ (by rw [b₀]; exact h₀')
  have e₁ := hp2WinRegionIS_le (r := r) (d := 1) hρ hρ' hr (by norm_num) h₁ (by rw [b₁]; exact h₁')
  have e₂ := hp2WinRegionIS_le (r := r) (d := 2) hρ hρ' hr (by norm_num) h₂ (by rw [b₂]; exact h₂')
  have e₃ := hp2WinRegionIS_le (r := r) (d := 3) hρ hρ' hr (by norm_num) h₃ (by rw [b₃]; exact h₃')
  rw [b₀, k₀, s₀, Nat.cast_ofNat] at e₀
  rw [b₁, k₁, s₁, Nat.cast_ofNat] at e₁
  rw [b₂, k₂, s₂, Nat.cast_ofNat] at e₂
  rw [b₃, k₃, s₃, Nat.cast_ofNat] at e₃
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  calc _ ≤ (ρ : ℝ) / ((ρ : ℝ) - 2) * K₀ * 1.000101 * (5.540237 / 2.02364)
        + (ρ : ℝ) / ((ρ : ℝ) - 3) * K₁ * 1.000101 * (204.173191 / 2.022339)
        + (ρ : ℝ) / ((ρ : ℝ) - 4) * K₂ * 1.000101 * (209.20073 / 2.021877)
        + (ρ : ℝ) / ((ρ : ℝ) - 4) * K₃ * 1.000101 * (349.146933 / 2.023023) :=
      add_le_add (add_le_add (add_le_add e₀ e₁) e₂) e₃
    _ = _ := by ring

/-- **HP2's sum over the cells with the rest on short tubes, region by region**: for a rung
`35 ≤ r₀ ≤ 1000` with the depths split at `17 ≤ D ≤ 200` and `18 ≤ N ≤ 60`, `D + N ≤ r₀`, a deep
start `r₀ ≤ ρ ≤ r`, the post constants' numerals `K` (`1 ≤ K²·hp2WinX d n`) and region II's
weighted sums `SE`, `SGw`, `r·hp2ExtSumS r 400 hp2ExtB 5.032` is at most the sum of: region I at
the rung (`RMF.hp2WinRegionIS_le_num`); region II, `4 ≤ d < D`, with `r/(r - d) ≤ r₀/(r₀ - d)`
and `κ₄(n₀) ≤ κ₄(r₀ - D + 1)` (`RMF.hp2WinRegionIIS_le`, `RMF.hp2WinIIS_sum_le`); the short
posts `r - d < N` at the rung (`RMF.hp2NearS_depth_le`); the deep cells at `ρ`
(`RMF.hp2DeepS_le`); and the far depths `D ≤ d ≤ r - N` (`RMF.hp2FarS_depth_le`), still as a sum
over `d`. -/
theorem hp2ExtSumS_le_regions {r₀ ρ D N r : ℕ} (hr₀ : 35 ≤ r₀) (hr₀' : r₀ ≤ 1000)
    (hρ : r₀ ≤ ρ) (hr : ρ ≤ r) (hD : 17 ≤ D) (hD200 : D ≤ 200) (hN : 18 ≤ N) (hN60 : N ≤ 60)
    (hDN : D + N ≤ r₀)
    {K₀ K₁ K₂ K₃ K₄ Kn : ℝ} (h₀ : 0 ≤ K₀) (h₀' : 1 ≤ K₀ ^ 2 * hp2WinX 0 (r₀ - 2))
    (h₁ : 0 ≤ K₁) (h₁' : 1 ≤ K₁ ^ 2 * hp2WinX 1 (r₀ - 3))
    (h₂ : 0 ≤ K₂) (h₂' : 1 ≤ K₂ ^ 2 * hp2WinX 2 (r₀ - 4))
    (h₃ : 0 ≤ K₃) (h₃' : 1 ≤ K₃ ^ 2 * hp2WinX 3 (r₀ - 4))
    (h₄ : 0 ≤ K₄) (h₄' : 1 ≤ K₄ ^ 2 * hp2WinX 4 (r₀ - D + 1))
    (hn : 0 ≤ Kn) (hn' : 1 ≤ Kn ^ 2 * hp2WinX 4 N)
    {SE SGw : ℝ}
    (hSE : ∑ d ∈ Finset.Ico 4 12, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinE2 d ≤ SE)
    (hSGw : ∑ d ∈ Finset.Ico 12 D, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinG d ≤ SGw) :
    (r : ℝ) * hp2ExtSumS r 400 hp2ExtB 5.032
      ≤ 1.000101 * ((r₀ : ℝ) / ((r₀ : ℝ) - 2) * K₀ * (5.540237 / 2.02364)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 3) * K₁ * (204.173191 / 2.022339)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₂ * (209.20073 / 2.021877)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₃ * (349.146933 / 2.023023))
        + K₄ / 2.023923 * 1.000101 * (110.1056 * SE + 1.00004 * 747.8028 * SGw)
        + 1.000101 * ∑ n ∈ Finset.Ico 3 N, (r₀ : ℝ) * hp2SlabG (r₀ - n) * hp2ExtPsi n
        + 2 * 0.632121 * (6.682553 * hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) / 1.05 ^ 2)
          * (1.000101 * 25.177512)
        + 1.000101 * Kn * 369.4819
          * ∑ d ∈ Finset.Ico D (r - N + 1), (r : ℝ) / ((r : ℝ) - d) * hp2FarG d := by
  have hr₀r : r₀ ≤ r := hρ.trans hr
  rw [mul_hp2ExtSumS_eq]
  set T : ℕ → ℝ := fun d => ∑ j ∈ Finset.range 40,
    (r : ℝ) * hp2WinCell r d j * hp2ExtFacS r d * hp2Band (40 * d + j) with hT
  have hsplit : ∑ d ∈ Finset.range (r - 2), T d
      = ∑ d ∈ Finset.range 4, T d + ∑ d ∈ Finset.Ico 4 D, T d
        + ∑ d ∈ Finset.Ico D (r - N + 1), T d + ∑ d ∈ Finset.Ico (r - N + 1) (r - 2), T d := by
    rw [← Finset.sum_range_add_sum_Ico _ (show 4 ≤ r - 2 by omega),
      ← Finset.sum_Ico_consecutive _ (show 4 ≤ D by omega) (show D ≤ r - 2 by omega),
      ← Finset.sum_Ico_consecutive _ (show D ≤ r - N + 1 by omega)
        (show r - N + 1 ≤ r - 2 by omega)]
    ring
  rw [hsplit]
  -- region I
  have hI : ∑ d ∈ Finset.range 4, T d
      ≤ 1.000101 * ((r₀ : ℝ) / ((r₀ : ℝ) - 2) * K₀ * (5.540237 / 2.02364)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 3) * K₁ * (204.173191 / 2.022339)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₂ * (209.20073 / 2.021877)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₃ * (349.146933 / 2.023023)) :=
    hp2WinRegionIS_le_num hr₀ hr₀' hr₀r h₀ h₀' h₁ h₁' h₂ h₂' h₃ h₃'
  -- region II
  have hII : ∑ d ∈ Finset.Ico 4 D, T d
      ≤ K₄ / 2.023923 * 1.000101 * (110.1056 * SE + 1.00004 * 747.8028 * SGw) := by
    have hw : ∀ d ∈ Finset.Ico 4 D, (0 : ℝ) ≤ 1 + d / ((r₀ - d : ℕ) : ℝ) :=
      fun d _ => by positivity
    have hK0 : 0 ≤ K₄ / 2.023923 * 1.000101 := by positivity
    calc ∑ d ∈ Finset.Ico 4 D, T d
        ≤ ∑ d ∈ Finset.Ico 4 D, (1 + d / ((r₀ - d : ℕ) : ℝ)) * (K₄ / 2.023923) * 1.000101
            * hp2WinE d * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121)
              * hp2WinW j * hp2WinB d j :=
          Finset.sum_le_sum fun d hd => by
            have hd := Finset.mem_Ico.1 hd
            have hX := (hp2WinX_le (d := 4) (show 3 ≤ r₀ - D + 1 by omega)
              (show r₀ - D + 1 ≤ r₀ - d by omega)).2
            exact hp2WinRegionIIS_le (r := r) (m := r₀ - d) (d := d) hd.1 (by omega)
              (by omega) (by omega) (by omega) h₄
              (h₄'.trans (mul_le_mul_of_nonneg_left hX (sq_nonneg K₄)))
      _ = K₄ / 2.023923 * 1.000101 * ∑ d ∈ Finset.Ico 4 D,
            (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinE d
              * ∑ j ∈ Finset.range 40, hp2PostC04 j * 2.023923 * (2 * 0.632121)
                * hp2WinW j * hp2WinB d j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ ≤ K₄ / 2.023923 * 1.000101
            * (110.1056 * ∑ d ∈ Finset.Ico 4 12, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinE2 d
              + 1.00004 * 747.8028
                * ∑ d ∈ Finset.Ico 12 D, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinG d) :=
          mul_le_mul_of_nonneg_left (hp2WinIIS_sum_le (by omega) hD200 hw) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK0
  -- the far depths
  have hfar : ∑ d ∈ Finset.Ico D (r - N + 1), T d
      ≤ 1.000101 * Kn * 369.4819
        * ∑ d ∈ Finset.Ico D (r - N + 1), (r : ℝ) / ((r : ℝ) - d) * hp2FarG d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd => by
      have hd := Finset.mem_Ico.1 hd
      exact hp2FarS_depth_le (r := r) (d := d) (N := N) (by omega) hN (by omega) (by omega) hn hn'
  -- the short posts
  have hnear : ∑ d ∈ Finset.Ico (r - N + 1) (r - 2), T d
      ≤ 1.000101 * ∑ n ∈ Finset.Ico 3 N, (r₀ : ℝ) * hp2SlabG (r₀ - n) * hp2ExtPsi n := by
    have hre : ∑ d ∈ Finset.Ico (r - N + 1) (r - 2), T d
        = ∑ n ∈ Finset.Ico 3 N, T (r - n) := by
      have h := Finset.sum_Ico_reflect (fun n => T (r - n)) (r - N + 1) (m := r - 2) (n := r)
        (by omega)
      rw [show r + 1 - (r - 2) = 3 by omega, show r + 1 - (r - N + 1) = N by omega] at h
      rw [← h]
      exact Finset.sum_congr rfl fun d hd => by
        have hd := Finset.mem_Ico.1 hd
        simp only [show r - (r - d) = d by omega]
    rw [hre, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => by
      have hn := Finset.mem_Ico.1 hn
      calc T (r - n) ≤ 1.000101 * ((r₀ : ℝ) * hp2SlabG (r₀ - n)) * hp2ExtPsi n :=
            hp2NearS_depth_le (r₀ := r₀) (r := r) (n := n) hn.1 (by omega) (by omega) hr₀r
        _ = 1.000101 * ((r₀ : ℝ) * hp2SlabG (r₀ - n) * hp2ExtPsi n) := by ring
  -- the deep cells
  have hdeep := hp2DeepS_le (ρ := ρ) (r := r) (by omega) hr
  linarith

/-! ### The cells of tube lengths in numerals -/

/-- **The deep cells' term in numerals**: `hp2SlabPrefHat 1.05 ≤ 146.948718` and a numeral
`g ≥ hp2SlabG ρ`. -/
lemma hp2DeepS_num {ρ : ℕ} {g : ℝ} (hg : hp2SlabG ρ ≤ g) :
    2 * 0.632121 * (6.682553 * hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) / 1.05 ^ 2)
        * (1.000101 * 25.177512)
      ≤ 2 * 0.632121 * (6.682553 * 146.948718 * ((ρ : ℝ) * g) / 1.05 ^ 2)
        * (1.000101 * 25.177512) := by
  have hP : hp2SlabPrefHat 1.05 ≤ 146.948718 := by
    unfold hp2SlabPrefHat hp2PrefixK
    norm_num
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  have h1 : hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ) ≤ 146.948718 * ((ρ : ℝ) * g) :=
    mul_le_mul hP (mul_le_mul_of_nonneg_left hg hρ0) (mul_nonneg hρ0 (hp2SlabG_nonneg ρ))
      (by norm_num)
  have h2 : 6.682553 * hp2SlabPrefHat 1.05 * ((ρ : ℝ) * hp2SlabG ρ)
      ≤ 6.682553 * 146.948718 * ((ρ : ℝ) * g) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right h2 (by norm_num)) (by norm_num)) (by norm_num)

/-- **A cell of tube lengths below the tail**: under the hypotheses of
`RMF.hp2ExtSumS_le_regions`, for `r < ρ' ≤ N + 200` and numerals
`QN ≥ ∑_{3≤n<N} r₀·hp2SlabG (r₀ - n)·hp2ExtPsi n`, `g ≥ hp2SlabG ρ`,
`F ≥ ∑_{D≤d<ρ'-N} (1 + d/N)·hp2WinG d`, `r·hp2ExtSumS r 400 hp2ExtB 5.032` is at most the
regions' bound in numerals (`RMF.hp2FarSum_le_table`, `RMF.hp2DeepS_num`). -/
theorem hp2ExtSumS_le_cell {r₀ ρ ρ' D N r : ℕ} (hr₀ : 35 ≤ r₀) (hr₀' : r₀ ≤ 1000)
    (hρ : r₀ ≤ ρ) (hr : ρ ≤ r) (hD : 17 ≤ D) (hD200 : D ≤ 200) (hN : 18 ≤ N) (hN60 : N ≤ 60)
    (hDN : D + N ≤ r₀)
    {K₀ K₁ K₂ K₃ K₄ Kn : ℝ} (h₀ : 0 ≤ K₀) (h₀' : 1 ≤ K₀ ^ 2 * hp2WinX 0 (r₀ - 2))
    (h₁ : 0 ≤ K₁) (h₁' : 1 ≤ K₁ ^ 2 * hp2WinX 1 (r₀ - 3))
    (h₂ : 0 ≤ K₂) (h₂' : 1 ≤ K₂ ^ 2 * hp2WinX 2 (r₀ - 4))
    (h₃ : 0 ≤ K₃) (h₃' : 1 ≤ K₃ ^ 2 * hp2WinX 3 (r₀ - 4))
    (h₄ : 0 ≤ K₄) (h₄' : 1 ≤ K₄ ^ 2 * hp2WinX 4 (r₀ - D + 1))
    (hn : 0 ≤ Kn) (hn' : 1 ≤ Kn ^ 2 * hp2WinX 4 N)
    {SE SGw : ℝ}
    (hSE : ∑ d ∈ Finset.Ico 4 12, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinE2 d ≤ SE)
    (hSGw : ∑ d ∈ Finset.Ico 12 D, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinG d ≤ SGw)
    (hr' : r < ρ') (hρ' : ρ' ≤ N + 200) {QN g F : ℝ}
    (hQN : ∑ n ∈ Finset.Ico 3 N, (r₀ : ℝ) * hp2SlabG (r₀ - n) * hp2ExtPsi n ≤ QN)
    (hg : hp2SlabG ρ ≤ g)
    (hF : ∑ d ∈ Finset.Ico D (ρ' - N), (1 + d / (N : ℝ)) * hp2WinG d ≤ F) :
    (r : ℝ) * hp2ExtSumS r 400 hp2ExtB 5.032
      ≤ 1.000101 * ((r₀ : ℝ) / ((r₀ : ℝ) - 2) * K₀ * (5.540237 / 2.02364)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 3) * K₁ * (204.173191 / 2.022339)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₂ * (209.20073 / 2.021877)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₃ * (349.146933 / 2.023023))
        + K₄ / 2.023923 * 1.000101 * (110.1056 * SE + 1.00004 * 747.8028 * SGw)
        + 1.000101 * QN
        + 2 * 0.632121 * (6.682553 * 146.948718 * ((ρ : ℝ) * g) / 1.05 ^ 2)
          * (1.000101 * 25.177512)
        + 1.000101 * Kn * 369.4819 * F := by
  have h := hp2ExtSumS_le_regions hr₀ hr₀' hρ hr hD hD200 hN hN60 hDN h₀ h₀' h₁ h₁' h₂ h₂' h₃ h₃'
    h₄ h₄' hn hn' hSE hSGw
  have hfar := hp2FarSum_le_table (D := D) (N := N) (r := r) (ρ' := ρ') (by omega) (by omega)
    (by omega) hr' hρ'
  have hdeep := hp2DeepS_num (ρ := ρ) hg
  have h1 := mul_le_mul_of_nonneg_left (hfar.trans hF)
    (show (0 : ℝ) ≤ 1.000101 * Kn * 369.4819 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hQN (show (0 : ℝ) ≤ 1.000101 by norm_num)
  linarith

/-- **The tail cell of tube lengths `r ≥ 260`**: under the hypotheses of
`RMF.hp2ExtSumS_le_regions` with `N = 60`, for `260 ≤ r` and numerals `QN`, `g` as in
`RMF.hp2ExtSumS_le_cell` and `F ≥ ∑_{D≤d<200} (1 + d/60)·hp2WinG d`,
`r·hp2ExtSumS r 400 hp2ExtB 5.032` is at most the regions' bound in numerals with the far depths
from `200` by `RMF.hp2FarSum_le_tail` (`2/√199 ≤ 2·0.070888121`). -/
theorem hp2ExtSumS_le_cell_tail {r₀ ρ D r : ℕ} (hr₀ : 35 ≤ r₀) (hr₀' : r₀ ≤ 1000)
    (hρ : r₀ ≤ ρ) (hr : ρ ≤ r) (hD : 17 ≤ D) (hD200 : D ≤ 200) (hDN : D + 60 ≤ r₀)
    (h260 : 260 ≤ ρ)
    {K₀ K₁ K₂ K₃ K₄ Kn : ℝ} (h₀ : 0 ≤ K₀) (h₀' : 1 ≤ K₀ ^ 2 * hp2WinX 0 (r₀ - 2))
    (h₁ : 0 ≤ K₁) (h₁' : 1 ≤ K₁ ^ 2 * hp2WinX 1 (r₀ - 3))
    (h₂ : 0 ≤ K₂) (h₂' : 1 ≤ K₂ ^ 2 * hp2WinX 2 (r₀ - 4))
    (h₃ : 0 ≤ K₃) (h₃' : 1 ≤ K₃ ^ 2 * hp2WinX 3 (r₀ - 4))
    (h₄ : 0 ≤ K₄) (h₄' : 1 ≤ K₄ ^ 2 * hp2WinX 4 (r₀ - D + 1))
    (hn : 0 ≤ Kn) (hn' : 1 ≤ Kn ^ 2 * hp2WinX 4 60)
    {SE SGw : ℝ}
    (hSE : ∑ d ∈ Finset.Ico 4 12, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinE2 d ≤ SE)
    (hSGw : ∑ d ∈ Finset.Ico 12 D, (1 + d / ((r₀ - d : ℕ) : ℝ)) * hp2WinG d ≤ SGw) {QN g F : ℝ}
    (hQN : ∑ n ∈ Finset.Ico 3 60, (r₀ : ℝ) * hp2SlabG (r₀ - n) * hp2ExtPsi n ≤ QN)
    (hg : hp2SlabG ρ ≤ g)
    (hF : ∑ d ∈ Finset.Ico D 200, (1 + d / (60 : ℝ)) * hp2WinG d ≤ F) :
    (r : ℝ) * hp2ExtSumS r 400 hp2ExtB 5.032
      ≤ 1.000101 * ((r₀ : ℝ) / ((r₀ : ℝ) - 2) * K₀ * (5.540237 / 2.02364)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 3) * K₁ * (204.173191 / 2.022339)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₂ * (209.20073 / 2.021877)
          + (r₀ : ℝ) / ((r₀ : ℝ) - 4) * K₃ * (349.146933 / 2.023023))
        + K₄ / 2.023923 * 1.000101 * (110.1056 * SE + 1.00004 * 747.8028 * SGw)
        + 1.000101 * QN
        + 2 * 0.632121 * (6.682553 * 146.948718 * ((ρ : ℝ) * g) / 1.05 ^ 2)
          * (1.000101 * 25.177512)
        + 1.000101 * Kn * 369.4819 * (F + 3.8568 * (2 * 0.070888121 + 0.09243)) := by
  have h := hp2ExtSumS_le_regions hr₀ hr₀' hρ hr hD hD200 (by norm_num) le_rfl hDN h₀ h₀' h₁ h₁'
    h₂ h₂' h₃ h₃' h₄ h₄' hn hn' hSE hSGw
  have hfar := hp2FarSum_le_tail (D := D) (r := r) (by omega) hD200 (by omega)
  have hdeep := hp2DeepS_num (ρ := ρ) hg
  have k₁ : 2 / √199 ≤ 2 * 0.070888121 :=
    div_sqrt_le_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hF' : ∑ d ∈ Finset.Ico D 200, (1 + d / (60 : ℝ)) * hp2WinG d
      + 3.8568 * (2 / √199 + 0.09243) ≤ F + 3.8568 * (2 * 0.070888121 + 0.09243) := by
    linarith
  have h1 := mul_le_mul_of_nonneg_left (hfar.trans hF')
    (show (0 : ℝ) ≤ 1.000101 * Kn * 369.4819 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hQN (show (0 : ℝ) ≤ 1.000101 by norm_num)
  linarith

end RMF
