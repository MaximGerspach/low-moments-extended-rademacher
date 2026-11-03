/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.LogPowerBound
import RMF.Reduction.Suppliers

/-!
# The sieve bound at short intervals

`RMF.roughCount_sub_le_brun` bounds the `y`-rough integers in an interval of length `H` by

`2H/log y + 5y(1 + log y)³`,

and it holds for every `H > 0`.  But the smoothing step of the small-`q` reduction uses intervals
of length `H ≈ √y`, where the **additive remainder swamps the main term** and the bound says
nothing.  The wrapper `RMF.exists_roughCount_sub_le` makes that explicit by demanding
`5y(1 + log y)³·log y ≤ H`, which `H ≈ √y` fails outright.

The fix needs no new sieve theory, only the observation the sieve literature makes when it writes
the bound as `H/min{log y, log H}`: **sift by fewer primes.**  A `y`-rough integer is `z`-rough for
every `z ≤ y`, so the existing bound may be applied at `z = min{y, ⌊H^{1/10}⌋}`.  The remainder
becomes `5H^{1/10}(1 + log H)³`, which is `o(H/log H)`, while the main term degrades from
`2H/log y` to `20H/min{log y, log H}`.

## Main results

* `RMF.IsRough.mono`: rough for a larger sifting parameter implies rough for a smaller one;
* `RMF.roughCount_sub_mono`: hence the interval counts are monotone in the sifting parameter.
-/

open Finset

namespace RMF

/-! ### Monotonicity in the sifting parameter -/

/-- **Sifting by fewer primes catches more.**  If every prime factor of `n` exceeds `y` and
`z ≤ y`, then every prime factor of `n` exceeds `z`. -/
theorem IsRough.mono {z y n : ℕ} (hzy : z ≤ y) (h : IsRough y n) : IsRough z n :=
  isRough_iff.2 fun p hp hpn => lt_of_le_of_lt hzy (isRough_iff.1 h p hp hpn)

/-- The `y`-rough integers of an interval, as a `Finset`.  `RMF.roughCount` counts an initial
segment; the difference of two of them is this. -/
theorem roughCount_sub_eq_card {y : ℕ} {x H : ℝ} (hH : 0 ≤ H) :
    (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ)
      = ({n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y n}.card : ℝ) := by
  classical
  have hxH : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : {n ∈ Finset.Icc 1 ⌊x + H⌋₊ | IsRough y n}
      = {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n}
        ∪ {n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y n} := by
    rw [← Finset.filter_union]
    congr 1
    rw [show Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ from rfl,
      show Finset.Icc 1 ⌊x + H⌋₊ = Finset.Ioc 0 ⌊x + H⌋₊ from rfl]
    exact (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hxH).symm
  have hdisj : Disjoint {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n}
      {n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y n} := by
    refine Finset.disjoint_filter_filter (Finset.disjoint_left.2 fun n hn hn' => ?_)
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc] at hn'
    omega
  have := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint hdisj] at this
  rw [roughCount, roughCount, this]
  push_cast
  ring

/-- **The interval count is monotone in the sifting parameter.**  Sifting by the primes up to `z`
rather than up to `y ≥ z` can only catch more. -/
theorem roughCount_sub_mono {z y : ℕ} (hzy : z ≤ y) {x H : ℝ} (hH : 0 ≤ H) :
    (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ)
      ≤ (roughCount z (x + H) : ℝ) - (roughCount z x : ℝ) := by
  classical
  rw [roughCount_sub_eq_card hH, roughCount_sub_eq_card hH]
  have hsub : {n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough y n}
      ⊆ {n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ | IsRough z n} := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.mono hzy⟩
  exact_mod_cast Finset.card_le_card hsub

/-! ### The bound at short intervals -/

/-- **The sieve bound at short intervals.**  `#{y-rough in (x, x+H]} ≤ C·H / min{log y, log H}`
for `2 ≤ y` and `H ≥ H₀`, with no lower bound on `H` relative to `y`; the witnesses are `C = 80`
and `H₀ = e^21`.  The proof sifts by fewer primes: at `z = min{y, ⌊H^{1/10}⌋}` the remainder
`5z(1+log z)³ ≤ 40·H^{1/10}(log H)³` of `RMF.roughCount_sub_le_brun` is at most `40·H/log H`
(`RMF.rpow_mul_log_pow_three_le`), and the main term `2H/log z` loses at most a factor `20`
(`RMF.exists_roughCount_sub_le` instead demands `H` large against `y`). -/
theorem exists_roughCount_sub_le_short :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (x H : ℝ), 2 ≤ y → 0 < x → H₀ ≤ H →
        (roughCount y (x + H) : ℝ) - (roughCount y x : ℝ)
          ≤ C * H / min (Real.log y) (Real.log H) := by
  refine ⟨80, Real.exp 21, by norm_num, Real.exp_pos 21, ?_⟩
  intro y x H hy hx hHe
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (Real.exp_pos 21) hHe
  have hlogH : (21 : ℝ) ≤ Real.log H := by
    rw [← Real.log_exp 21]
    exact Real.log_le_log (Real.exp_pos 21) hHe
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hH1R : (1 : ℝ) ≤ H := le_trans (Real.one_le_exp (by norm_num)) hHe
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hmin0 : (0 : ℝ) < min (Real.log y) (Real.log H) := lt_min hlogy0 hlogH0
  -- sift by fewer primes
  set w : ℝ := H ^ (1 / 10 : ℝ) with hwdef
  have hw0 : (0 : ℝ) < w := Real.rpow_pos_of_pos hH0 _
  have hlogw : Real.log w = Real.log H / 10 := by
    rw [hwdef, Real.log_rpow hH0]
    ring
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hw2 : (2 : ℝ) ≤ w := by
    have hle : Real.log 2 ≤ Real.log w := by rw [hlogw]; linarith
    have h2 := Real.exp_le_exp.2 hle
    rwa [Real.exp_log (by norm_num), Real.exp_log hw0] at h2
  set z : ℕ := min y ⌊w⌋₊ with hzdef
  have hfl2 : 2 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw2)
  have hz2 : 2 ≤ z := le_min hy hfl2
  have hzy : z ≤ y := Nat.min_le_left _ _
  have hzw : (z : ℝ) ≤ w :=
    le_trans (by exact_mod_cast Nat.min_le_right y ⌊w⌋₊) (Nat.floor_le hw0.le)
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hlogz0 : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  -- the main term loses at most a factor 20
  have hminz : min (Real.log y) (Real.log H) ≤ 20 * Real.log z := by
    rcases le_total y ⌊w⌋₊ with hcase | hcase
    · have he : z = y := by rw [hzdef]; exact min_eq_left hcase
      have : Real.log y = Real.log z := by rw [he]
      calc min (Real.log y) (Real.log H) ≤ Real.log y := min_le_left _ _
        _ = Real.log z := this
        _ ≤ 20 * Real.log z := by linarith
    · have he : z = ⌊w⌋₊ := by rw [hzdef]; exact min_eq_right hcase
      have hzf : (z : ℝ) = (⌊w⌋₊ : ℝ) := by rw [he]
      have hge : w / 2 ≤ (z : ℝ) := by
        rw [hzf]
        have := Nat.sub_one_lt_floor w
        have h1 : w - 1 ≤ (⌊w⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one w]
        linarith
      have hlz : Real.log w - Real.log 2 ≤ Real.log z := by
        have := Real.log_le_log (by positivity) hge
        rwa [Real.log_div (by positivity) (by norm_num)] at this
      calc min (Real.log y) (Real.log H) ≤ Real.log H := min_le_right _ _
        _ ≤ 20 * (Real.log H / 10 - 1) := by linarith
        _ ≤ 20 * (Real.log w - Real.log 2) := by rw [hlogw]; linarith
        _ ≤ 20 * Real.log z := by linarith
  -- the remainder is `o(H / log H)`, with the literal constant `40`
  have hrem : 5 * (z : ℝ) * (1 + Real.log z) ^ 3 ≤ 40 * (H / Real.log H) := by
    have hlw : Real.log z ≤ Real.log H := by
      have : (z : ℝ) ≤ H := by
        refine le_trans hzw ?_
        rw [hwdef]
        exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
      exact Real.log_le_log (by linarith) this
    have h1l : 1 + Real.log z ≤ 2 * Real.log H := by linarith
    have hcube : (1 + Real.log z) ^ 3 ≤ 8 * Real.log H ^ 3 := by
      have h0 : (0 : ℝ) ≤ 1 + Real.log z := by linarith
      calc (1 + Real.log z) ^ 3 ≤ (2 * Real.log H) ^ 3 := by gcongr
        _ = 8 * Real.log H ^ 3 := by ring
    have hbig : H ^ (1 / 10 : ℝ) * Real.log H ^ 3 ≤ H / Real.log H :=
      rpow_mul_log_pow_three_le hHe
    calc 5 * (z : ℝ) * (1 + Real.log z) ^ 3 ≤ 5 * w * (8 * Real.log H ^ 3) := by
          gcongr
      _ = 40 * (H ^ (1/10:ℝ) * Real.log H ^ 3) := by rw [hwdef]; ring
      _ ≤ 40 * (H / Real.log H) := by linarith
  -- assemble
  have hbrun := roughCount_sub_le_brun hz2 hx hH0
  have hmono := roughCount_sub_mono hzy hH0.le (x := x)
  refine le_trans hmono (le_trans hbrun ?_)
  have hterm1 : 2 * H / Real.log z ≤ 40 * H / min (Real.log y) (Real.log H) := by
    rw [div_le_div_iff₀ hlogz0 hmin0]
    nlinarith [hminz, hH0.le]
  have hdiv : H / Real.log H ≤ H / min (Real.log y) (Real.log H) := by
    rw [div_le_div_iff₀ hlogH0 hmin0]
    nlinarith [min_le_right (Real.log y) (Real.log H), hH0.le]
  have hterm2 : 40 * (H / Real.log H) ≤ 40 * H / min (Real.log y) (Real.log H) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have : (80 : ℝ) * H / min (Real.log y) (Real.log H)
      = 40 * H / min (Real.log y) (Real.log H)
        + 40 * H / min (Real.log y) (Real.log H) := by ring
  rw [this]
  exact add_le_add hterm1 (le_trans hrem hterm2)

/-- **The counting function of the smoothing intervals.**  If `t ∈ [r, r(1+η)]` then
`r ≥ t/(1+η)`, so the weight `r⁻²` is at most `(1+η)²/t²`, uniformly in `r`.  Summing, the
weighted count is at most `(1+η)²/t²` times the plain count of intervals containing `t`.

This is where the sieve enters: that plain count is over `r` in `[t/(1+η), t]`, an interval of
length `ηt/(1+η)`, and `RMF.exists_roughCount_sub_le_short` bounds it when the `r` are rough. -/
theorem sum_inv_sq_indicator_le (S : Finset ℕ) {η t : ℝ} (ht : 0 < t) :
    ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ ((1 + η) ^ 2 / t ^ 2)
          * ((S.filter fun r : ℕ => t ∈ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).card : ℝ) := by
  classical
  set F : Finset ℕ := S.filter fun r : ℕ => t ∈ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) with hF
  have hzero : ∀ r ∈ S, r ∉ F →
      (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t = 0 := by
    intro r hr hnot
    have hmem : t ∉ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) := by
      intro h
      exact hnot (by rw [hF]; exact Finset.mem_filter.2 ⟨hr, h⟩)
    rw [Set.indicator_of_notMem hmem, mul_zero]
  rw [← Finset.sum_subset (by rw [hF]; exact Finset.filter_subset _ S) hzero]
  calc ∑ r ∈ F, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ ∑ _r ∈ F, ((1 + η) ^ 2 / t ^ 2) := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hmem : t ∈ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) := by
          rw [hF] at hr
          exact (Finset.mem_filter.1 hr).2
        have hrt := hmem.1
        have htr := hmem.2
        have hr0 : (0 : ℝ) < r := by
          by_contra hcon
          have hz : ((r : ℝ)) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg r)
          rw [hz, zero_mul] at htr
          linarith
        rw [Set.indicator_of_mem hmem, mul_one, div_eq_mul_inv,
          inv_le_iff_one_le_mul₀ (by positivity)]
        have h1 : t ^ 2 ≤ ((r : ℝ) * (1 + η)) ^ 2 := by nlinarith
        calc (1 : ℝ) = (t ^ 2)⁻¹ * t ^ 2 := by field_simp
          _ ≤ (t ^ 2)⁻¹ * ((r : ℝ) * (1 + η)) ^ 2 := by gcongr
          _ = (1 + η) ^ 2 * (t ^ 2)⁻¹ * (r : ℝ) ^ 2 := by ring
    _ = ((1 + η) ^ 2 / t ^ 2) * ((F).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ### The smoothing intervals' counting function, as a rough count

`RMF.sum_inv_sq_indicator_le` leaves the plain count of `r ∈ S` with `t ∈ [r, r(1+η)]`.  When the
`r` are rough that count is a count of rough integers in an interval, which is what the sieve
bounds.  The interval is `(a, t]` for any `a` below `t/(1+η)`. -/

/-- **The smoothing intervals containing `t` are rough integers in `(a, t]`.**  From
`t ≤ r(1+η)` the index `r` is at least `t/(1+η)`, hence above `a`; and `r ≤ t` puts it below
`⌊t⌋₊`. -/
theorem card_filter_le_card_rough_Ioc {y : ℕ} {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r)
    {η t a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a < t / (1 + η)) :
    (S.filter fun r : ℕ => t ∈ Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).card
      ≤ {n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊ | IsRough y n}.card := by
  classical
  refine Finset.card_le_card fun r hr => ?_
  rw [Finset.mem_filter] at hr ⊢
  have hrS : r ∈ S := hr.1
  have hrt : ((r : ℕ) : ℝ) ≤ t := hr.2.1
  have htr : t ≤ ((r : ℕ) : ℝ) * (1 + η) := hr.2.2
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  have hge : t / (1 + η) ≤ (r : ℝ) := by
    rw [div_le_iff₀ hη0]
    exact htr
  have hfa : ((⌊a⌋₊ : ℕ) : ℝ) ≤ a := Nat.floor_le ha
  refine ⟨Finset.mem_Ioc.2 ⟨?_, Nat.le_floor hrt⟩, hSr r hrS⟩
  have : ((⌊a⌋₊ : ℕ) : ℝ) < (r : ℝ) := lt_of_le_of_lt hfa (lt_of_lt_of_le haη hge)
  exact_mod_cast this

/-! ### The counting function, bounded by the sieve

Putting `RMF.sum_inv_sq_indicator_le`, `RMF.card_filter_le_card_rough_Ioc` and
`RMF.exists_roughCount_sub_le_short` together: the weighted count of smoothing intervals
containing `t` is at most `(1+η)²/t²` times a rough count over `(t/(1+η) - 1, t]`, an interval of
length `H = tη/(1+η) + 1`, which the sieve bounds by `C·H/min{log y, log H}`.

**The `+1` in `H` is not slack**: it is what makes `H` bounded below independently of `η`, so the
sieve's absolute threshold `H₀` can be met by taking `t` large rather than by constraining `η`. -/

/-- **The weighted interval count, as a rough count.**  Combining the weight bound with the
identification of the index set.  The left endpoint `a` is a parameter: any `a < t/(1+η)` works,
and leaving it free keeps the arithmetic out of the statement. -/
theorem sum_inv_sq_indicator_le_rough {y : ℕ} {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r)
    {η t a : ℝ} (hη : 0 < η) (ht : 0 < t) (ha : 0 ≤ a) (hat : a < t / (1 + η)) :
    ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ ((1 + η) ^ 2 / t ^ 2)
          * (({n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊ | IsRough y n}).card : ℝ) := by
  refine le_trans (sum_inv_sq_indicator_le S ht) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast card_filter_le_card_rough_Ioc hSr hη ha hat

/-- **The weighted interval count, bounded by the sieve.**  The constant and the threshold are
absolute.  `a` stays a parameter, so the caller chooses it — at `a = t/(1+η) - 1` the interval has
length `tη/(1+η) + 1`, which is at least `1` whatever `η`, so the sieve's threshold is met by
taking `t` large rather than by constraining `η`. -/
theorem exists_sum_inv_sq_indicator_le_sieve :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (S : Finset ℕ), (∀ r ∈ S, IsRough y r) → 2 ≤ y →
      ∀ η t a : ℝ, 0 < η → 0 < a → a < t / (1 + η) → H₀ ≤ t - a →
        ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
            * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
          ≤ ((1 + η) ^ 2 / t ^ 2)
              * (C * (t - a) / min (Real.log y) (Real.log (t - a))) := by
  obtain ⟨C, H₀, hC, hH₀, hsieve⟩ := exists_roughCount_sub_le_short
  refine ⟨C, H₀, hC, hH₀, fun y S hSr hy η t a hη ha0 hat hH => ?_⟩
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  have hta : a < t := by linarith
  have ht0 : (0 : ℝ) < t := lt_trans ha0 hta
  refine le_trans (sum_inv_sq_indicator_le_rough hSr hη ht0 ha0.le hat) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum : a + (t - a) = t := by ring
  have hcard := roughCount_sub_eq_card (y := y) (x := a) (H := t - a) (by linarith)
  rw [hsum] at hcard
  have hkey := hsieve y a (t - a) hy ha0 hH
  rw [hsum] at hkey
  rw [← hcard]
  exact hkey

/-! ### The counting bound in the form the exchange consumes

`RMF.sum_smul_setIntegral_le` wants a single function `b` of `t` bounding the weighted count.
Specialising the left endpoint to `a = t/(1+η) - 1` gives it, with interval length
`H = tη/(1+η) + 1`. -/

/-- `t - (t/(1+η) - 1) = tη/(1+η) + 1`, the length of the smoothing interval's preimage. -/
lemma sub_div_sub_one_eq {η t : ℝ} (hη : 0 < η) :
    t - (t / (1 + η) - 1) = t * η / (1 + η) + 1 := by
  have hη0 : (1 : ℝ) + η ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **The counting bound with the endpoint chosen.**  `b t = ((1+η)²/t²)·C·H/min{log y, log H}`
with `H = tη/(1+η) + 1`, which is the function `RMF.sum_smul_setIntegral_le` consumes.

`H ≥ 1` whatever `η`, so the absolute threshold is met by taking `t` large. -/
theorem exists_sum_inv_sq_indicator_le_sieve' :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (S : Finset ℕ), (∀ r ∈ S, IsRough y r) → 2 ≤ y →
      ∀ η t : ℝ, 0 < η → 1 + η < t → H₀ ≤ t * η / (1 + η) + 1 →
        ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
            * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
          ≤ ((1 + η) ^ 2 / t ^ 2)
              * (C * (t * η / (1 + η) + 1)
                  / min (Real.log y) (Real.log (t * η / (1 + η) + 1))) := by
  obtain ⟨C, H₀, hC, hH₀, hmain⟩ := exists_sum_inv_sq_indicator_le_sieve
  refine ⟨C, H₀, hC, hH₀, fun y S hSr hy η t hη ht hH => ?_⟩
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  have harith : t - (t / (1 + η) - 1) = t * η / (1 + η) + 1 := sub_div_sub_one_eq hη
  have ha0 : (0 : ℝ) < t / (1 + η) - 1 := by
    rw [sub_pos, lt_div_iff₀ hη0, one_mul]
    exact ht
  have hat : t / (1 + η) - 1 < t / (1 + η) := by linarith
  have hkey := hmain y S hSr hy η t (t / (1 + η) - 1) hη ha0 hat (by rw [harith]; exact hH)
  rwa [harith] at hkey

/-! ### The harmonic mass of the rough integers

The error term of the smoothing needs `∑_{R < r ≤ R'} 1/r` over rough `r`, not the count.  On a
**dyadic** block the two are the same thing: every `r` exceeds `R`, so the sum is at most the
count over `R`, and the count is `≪ R/log y` — the `R` cancels and the block contributes `1/log y`
whatever its position.

`min{log y, log R}` collapses to `log y` as soon as `R ≥ y`, which is why the block bound is
clean.  The full range then costs one factor of the number of dyadic blocks. -/

/-- **One dyadic block of rough integers is small.**  The sieve's `min{log y, log R}` collapses
to `log y` as soon as `R ≥ y`, so the count is `≤ C·R/log y` **wherever the block sits** — the
position drops out entirely.

Both the harmonic mass (`RMF.exists_sum_inv_rough_dyadic_le`) and the global count
(`RMF.exists_roughCount_le`) are built on this one fact. -/
theorem exists_roughCount_dyadic_le :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (R : ℝ), 2 ≤ y → (y : ℝ) ≤ R → H₀ ≤ R →
        (({n ∈ Finset.Ioc ⌊R⌋₊ ⌊R + R⌋₊ | IsRough y n}).card : ℝ) ≤ C * R / Real.log y := by
  obtain ⟨C, H₀, hC, hH₀, hsieve⟩ := exists_roughCount_sub_le_short
  refine ⟨C, max H₀ 2, hC, by positivity, fun y R hy hyR hR => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right H₀ 2) hR)
  have hyR2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogR : Real.log y ≤ Real.log R := Real.log_le_log (by linarith) hyR
  have hcount := hsieve y R R hy hR0 (le_trans (le_max_left H₀ 2) hR)
  rw [roughCount_sub_eq_card hR0.le] at hcount
  rwa [min_eq_left hlogR] at hcount

/-- **One dyadic block of rough integers has harmonic mass `≪ 1/log y`.**  Each `r` exceeds `R`,
so the sum is at most `card/R`, and the sieve makes the count `≪ R/log y`. -/
theorem exists_sum_inv_rough_dyadic_le :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (R : ℝ), 2 ≤ y → (y : ℝ) ≤ R → H₀ ≤ R →
        ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R + R⌋₊ | IsRough y n}, ((r : ℝ))⁻¹
          ≤ C / Real.log y := by
  obtain ⟨C, H₀, hC, hH₀, hblock⟩ := exists_roughCount_dyadic_le
  refine ⟨C, max H₀ 2, hC, by positivity, fun y R hy hyR hR => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right H₀ 2) hR)
  -- every term is at most `1/R`
  have hterm : ∀ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R + R⌋₊ | IsRough y n}, ((r : ℝ))⁻¹ ≤ R⁻¹ := by
    intro r hr
    have hrR : R < (r : ℝ) := by
      have h : ⌊R⌋₊ < r := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hr).1).1
      have h' : (⌊R⌋₊ : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast h
      exact lt_of_lt_of_le (Nat.lt_floor_add_one R) h'
    exact inv_anti₀ hR0 hrR.le
  -- the count is `≤ C·R/log y`
  have hcount := hblock y R hy hyR (le_trans (le_max_left H₀ 2) hR)
  calc ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R + R⌋₊ | IsRough y n}, ((r : ℝ))⁻¹
      ≤ ∑ _r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R + R⌋₊ | IsRough y n}, R⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (({n ∈ Finset.Ioc ⌊R⌋₊ ⌊R + R⌋₊ | IsRough y n}).card : ℝ) * R⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * R / Real.log y) * R⁻¹ :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = C / Real.log y := by
        field_simp

/-- **The harmonic mass of the rough integers over a dyadic range.**  Iterating
`RMF.exists_sum_inv_rough_dyadic_le` over `k` blocks: the rough `r ∈ (R, 2^k R]` carry harmonic
mass at most `k·C/log y`.

The count of blocks is the only thing that grows, which is what turns this into the bound
`≪ (1 + log(R'/R))/log y` once `k` is chosen as `⌈log₂(R'/R)⌉`. -/
theorem exists_sum_inv_rough_pow_le :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (R : ℝ) (k : ℕ), 2 ≤ y → (y : ℝ) ≤ R → H₀ ≤ R →
        ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 ^ k * R⌋₊ | IsRough y n}, ((r : ℝ))⁻¹
          ≤ k * (C / Real.log y) := by
  classical
  obtain ⟨C, H₀, hC, hH₀, hblock⟩ := exists_sum_inv_rough_dyadic_le
  refine ⟨C, H₀, hC, hH₀, fun y R k hy hyR hR => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hH₀ hR
  induction k with
  | zero =>
      have h0 : (2 : ℝ) ^ (0 : ℕ) * R = R := by norm_num
      rw [h0]
      simp
  | succ k ih =>
      have hpow : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hRk : R ≤ 2 ^ k * R := le_mul_of_one_le_left hR0.le h2k
      have heq : (2 : ℝ) ^ (k + 1) * R = 2 ^ k * R + 2 ^ k * R := by ring
      have hfl1 : ⌊R⌋₊ ≤ ⌊(2 : ℝ) ^ k * R⌋₊ := Nat.floor_le_floor hRk
      have hfl2 : ⌊(2 : ℝ) ^ k * R⌋₊ ≤ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ := by
        refine Nat.floor_le_floor ?_
        rw [heq]
        nlinarith [mul_pos hpow hR0]
      -- the top block, positioned at `2^k R`
      have hblk := hblock y (2 ^ k * R) hy (le_trans hyR hRk) (le_trans hR hRk)
      rw [← heq] at hblk
      -- split the range at `2^k R`
      have hsplit : {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ | IsRough y n}
          = {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ k * R⌋₊ | IsRough y n}
            ∪ {n ∈ Finset.Ioc ⌊(2 : ℝ) ^ k * R⌋₊ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ | IsRough y n} := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc hfl1 hfl2]
      have hdisj : Disjoint {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ k * R⌋₊ | IsRough y n}
          {n ∈ Finset.Ioc ⌊(2 : ℝ) ^ k * R⌋₊ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ | IsRough y n} := by
        rw [Finset.disjoint_left]
        intro n hn hn'
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hn hn'
        omega
      rw [hsplit, Finset.sum_union hdisj]
      have : ((k + 1 : ℕ) : ℝ) * (C / Real.log y) = k * (C / Real.log y) + C / Real.log y := by
        push_cast
        ring
      rw [this]
      exact add_le_add ih hblk

/-- **The rough integers in `(R, R']` carry harmonic mass `≪ (1 + log(R'/R))/log y`.**

This is the estimate the error term of the smoothing consumes.  It follows from the dyadic form
by taking `k = ⌈log₂(R'/R)⌉` blocks; `1/log 2 < 2` converts the base-2 logarithm to the natural
one, which is the only place a numeric constant enters. -/
theorem exists_sum_inv_rough_Ioc_le :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (R R' : ℝ), 2 ≤ y → (y : ℝ) ≤ R → H₀ ≤ R → R ≤ R' →
        ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R'⌋₊ | IsRough y n}, ((r : ℝ))⁻¹
          ≤ C * (1 + Real.log (R' / R)) / Real.log y := by
  classical
  obtain ⟨C, H₀, hC, hH₀, hpow⟩ := exists_sum_inv_rough_pow_le
  refine ⟨3 / 2 * C, H₀, by positivity, hH₀, fun y R R' hy hyR hR hRR' => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hH₀ hR
  have hR'0 : (0 : ℝ) < R' := lt_of_lt_of_le hR0 hRR'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) ≤ Real.log (R' / R) := Real.log_nonneg ((one_le_div hR0).2 hRR')
  have hlogy : (0 : ℝ) < Real.log y := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    linarith
  obtain ⟨k, hkge, hklt⟩ : ∃ k : ℕ, Real.log (R' / R) / Real.log 2 ≤ (k : ℝ)
      ∧ (k : ℝ) < Real.log (R' / R) / Real.log 2 + 1 :=
    ⟨⌈Real.log (R' / R) / Real.log 2⌉₊, Nat.le_ceil _,
      Nat.ceil_lt_add_one (div_nonneg hL hlog2.le)⟩
  -- `2^k R` dominates `R'`
  have hdom : R' ≤ 2 ^ k * R := by
    have h1 : Real.log (R' / R) ≤ Real.log ((2 : ℝ) ^ k) := by
      rw [Real.log_pow]
      rw [div_le_iff₀ hlog2] at hkge
      linarith
    have h2 : R' / R ≤ (2 : ℝ) ^ k :=
      (Real.log_le_log_iff (div_pos hR'0 hR0) (by positivity)).1 h1
    rwa [div_le_iff₀ hR0] at h2
  -- the sum only grows when the range does
  have hsub : {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R'⌋₊ | IsRough y n}
      ⊆ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ k * R⌋₊ | IsRough y n} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_le_floor hdom)⟩, hn.2⟩
  -- the number of blocks costs a factor `1/log 2 = 1.443`, which `3/2` covers
  have hkle : (k : ℝ) ≤ 3 / 2 * (1 + Real.log (R' / R)) := by
    have hone : (1 : ℝ) ≤ 3 / 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : Real.log (R' / R) / Real.log 2 ≤ 3 / 2 * Real.log (R' / R) := by
      rw [div_le_iff₀ hlog2]
      calc Real.log (R' / R) = Real.log (R' / R) * 1 := (mul_one _).symm
        _ ≤ Real.log (R' / R) * (3 / 2 * Real.log 2) := mul_le_mul_of_nonneg_left hone hL
        _ = 3 / 2 * Real.log (R' / R) * Real.log 2 := by ring
    linarith
  calc ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊R'⌋₊ | IsRough y n}, ((r : ℝ))⁻¹
      ≤ ∑ r ∈ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ k * R⌋₊ | IsRough y n}, ((r : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => inv_nonneg.2 (Nat.cast_nonneg i))
    _ ≤ (k : ℝ) * (C / Real.log y) := hpow y R k hy hyR hR
    _ ≤ (3 / 2 * (1 + Real.log (R' / R))) * (C / Real.log y) :=
        mul_le_mul_of_nonneg_right hkle (div_nonneg hC.le hlogy.le)
    _ = 3 / 2 * C * (1 + Real.log (R' / R)) / Real.log y := by ring

/-! ### The sieve's denominator at `η = y^{-1/2}`

The sieve bounds by `C·H/min{log y, log H}` with `H = tη/(1+η) + 1`, and that denominator is only
useful if `H` is not much smaller than `y`.  At `η = y^{-1/2}` it is not: roughness puts every
`r > 1` above `y`, so `t ≥ y`, and then `H ≥ √y`.

The inequality is exact — `y/(√y+1) + 1 ≥ √y` reduces to `1 ≥ 0` — so **no threshold on `y`**
beyond `2` is needed, and none is imposed. -/

/-- **At `η = y^{-1/2}` and `t ≥ y`, the sifting range reaches `√y`.**  The inequality
`y/(√y+1) + 1 ≥ √y` is exact, reducing to `1 ≥ 0`. -/
theorem sqrt_le_sifting_range {y : ℕ} (hy : 2 ≤ y) {t : ℝ} (ht : (y : ℝ) ≤ t) :
    Real.sqrt y ≤ t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1 := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hs : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hs1 : (0 : ℝ) < Real.sqrt y + 1 := by linarith
  have hden : (0 : ℝ) < 1 + 1 / Real.sqrt y := by positivity
  have hss : Real.sqrt y * Real.sqrt y = (y : ℝ) := Real.mul_self_sqrt hy0.le
  -- the sifting range at `t = y` already reaches `√y`
  have hval : (y : ℝ) * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y)
      = (y : ℝ) / (Real.sqrt y + 1) := by
    rw [div_eq_div_iff hden.ne' hs1.ne']
    field_simp
  have hstep : Real.sqrt y ≤ (y : ℝ) / (Real.sqrt y + 1) + 1 := by
    have h1 : (Real.sqrt y - 1) * (Real.sqrt y + 1) ≤ (y : ℝ) := by
      have he : (Real.sqrt y - 1) * (Real.sqrt y + 1) = Real.sqrt y * Real.sqrt y - 1 := by ring
      rw [he, hss]
      linarith
    have h2 : Real.sqrt y - 1 ≤ (y : ℝ) / (Real.sqrt y + 1) := by
      rw [le_div_iff₀ hs1]
      exact h1
    linarith
  have hmono : (y : ℝ) * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y)
      ≤ t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) := by gcongr
  have hH : Real.sqrt y ≤ t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1 := by
    rw [hval] at hmono
    linarith
  exact hH

/-- **A sifting range reaching `√y` makes the sieve's denominator at least `½ log y`.** -/
theorem half_log_le_min_log_of_sqrt_le {y : ℕ} (hy : 2 ≤ y) {H : ℝ} (hH : Real.sqrt y ≤ H) :
    Real.log y / 2 ≤ min (Real.log y) (Real.log H) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hs : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by linarith)
  refine le_min (by linarith) ?_
  rw [← Real.log_sqrt hy0.le]
  exact Real.log_le_log hs hH

/-! ### The global count of rough integers

The error term of the smoothing has two halves.  The first sums `η` against the harmonic mass of
the rough `r`, which is what `RMF.exists_sum_inv_rough_Ioc_le` supplies.  The second sums
`(1+η)r/x` against their **count**, and needs `#{r ≤ x rough} ≪ x/log y` — the same dyadic
argument, but with the blocks now growing rather than cancelling. -/

/-- **`k` dyadic blocks of rough integers.**  Unlike the harmonic mass, where each block
contributes the same `1/log y`, the count grows with the block; `k` of them total
`(2^k − 1)·C·R/log y`, rounded up to `2^k` here. -/
theorem exists_roughCount_pow_le :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (R : ℝ) (k : ℕ), 2 ≤ y → (y : ℝ) ≤ R → H₀ ≤ R →
        (({n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 ^ k * R⌋₊ | IsRough y n}).card : ℝ)
          ≤ 2 ^ k * (C * R / Real.log y) := by
  classical
  obtain ⟨C, H₀, hC, hH₀, hblock⟩ := exists_roughCount_dyadic_le
  refine ⟨C, H₀, hC, hH₀, fun y R k hy hyR hR => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hH₀ hR
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  induction k with
  | zero =>
      have h0 : (2 : ℝ) ^ (0 : ℕ) * R = R := by norm_num
      rw [h0]
      have hz : (({n ∈ Finset.Ioc ⌊R⌋₊ ⌊R⌋₊ | IsRough y n}).card : ℝ) = 0 := by simp
      rw [hz]
      simpa using div_nonneg (mul_nonneg hC.le hR0.le) hlogy.le
  | succ k ih =>
      have hpow : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hRk : R ≤ 2 ^ k * R := le_mul_of_one_le_left hR0.le h2k
      have heq : (2 : ℝ) ^ (k + 1) * R = 2 ^ k * R + 2 ^ k * R := by ring
      have hfl1 : ⌊R⌋₊ ≤ ⌊(2 : ℝ) ^ k * R⌋₊ := Nat.floor_le_floor hRk
      have hfl2 : ⌊(2 : ℝ) ^ k * R⌋₊ ≤ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ := by
        refine Nat.floor_le_floor ?_
        rw [heq]
        linarith [mul_pos hpow hR0]
      have hblk := hblock y (2 ^ k * R) hy (le_trans hyR hRk) (le_trans hR hRk)
      rw [← heq] at hblk
      have hsplit : {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ | IsRough y n}
          = {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ k * R⌋₊ | IsRough y n}
            ∪ {n ∈ Finset.Ioc ⌊(2 : ℝ) ^ k * R⌋₊ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ | IsRough y n} := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc hfl1 hfl2]
      have hdisj : Disjoint {n ∈ Finset.Ioc ⌊R⌋₊ ⌊(2 : ℝ) ^ k * R⌋₊ | IsRough y n}
          {n ∈ Finset.Ioc ⌊(2 : ℝ) ^ k * R⌋₊ ⌊(2 : ℝ) ^ (k + 1) * R⌋₊ | IsRough y n} := by
        rw [Finset.disjoint_left]
        intro n hn hn'
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hn hn'
        omega
      have hsum : (2 : ℝ) ^ (k + 1) * (C * R / Real.log y)
          = 2 ^ k * (C * R / Real.log y) + 2 ^ k * (C * R / Real.log y) := by ring
      rw [hsplit, Finset.card_union_of_disjoint hdisj, Nat.cast_add, hsum]
      exact add_le_add ih (le_trans hblk (le_of_eq (by ring)))

/-- **Below `y` the only rough integer is `1`.**  Every rough `n > 1` has a prime factor, hence
one exceeding `y`, hence exceeds `y` itself. -/
theorem roughCount_self_le_one (y : ℕ) : roughCount y (y : ℝ) ≤ 1 := by
  classical
  have hfl : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
  have hsub : {n ∈ Finset.Icc 1 ⌊(y : ℝ)⌋₊ | IsRough y n} ⊆ {1} := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hnr⟩ := hn
    rw [Finset.mem_singleton]
    by_contra hne
    have hlt : y < n := hnr.lt_of_one_lt (lt_of_le_of_ne hn1 (Ne.symm hne))
    omega
  calc roughCount y (y : ℝ) = ({n ∈ Finset.Icc 1 ⌊(y : ℝ)⌋₊ | IsRough y n}).card := rfl
    _ ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton 1

/-- **The rough integers up to `x` number at most `1 + C·x/log y`.**  The `1` is the integer `1`
itself, rough for every `y` and the only rough integer below `y`.

This is the second half of the smoothing error: summed against `(1+η)r/x` it contributes the
`(log y)⁻¹` of `log x/√y + (log y)⁻¹`. -/
theorem exists_roughCount_le :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧
      ∀ (y : ℕ) (x : ℝ), 2 ≤ y → H₀ ≤ (y : ℝ) → (y : ℝ) ≤ x →
        (roughCount y x : ℝ) ≤ 1 + C * x / Real.log y := by
  classical
  obtain ⟨C, H₀, hC, hH₀, hpow⟩ := exists_roughCount_pow_le
  refine ⟨2 * C, H₀, by positivity, hH₀, fun y x hy hHy hyx => ?_⟩
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hy0 hyx
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) ≤ Real.log (x / y) := Real.log_nonneg ((one_le_div hy0).2 hyx)
  obtain ⟨k, hkge, hklt⟩ : ∃ k : ℕ, Real.log (x / y) / Real.log 2 ≤ (k : ℝ)
      ∧ (k : ℝ) < Real.log (x / y) / Real.log 2 + 1 :=
    ⟨⌈Real.log (x / y) / Real.log 2⌉₊, Nat.le_ceil _,
      Nat.ceil_lt_add_one (div_nonneg hL hlog2.le)⟩
  -- `x ≤ 2^k y`, and `2^k` costs only a factor `2` over `x/y`
  have hdom : x ≤ 2 ^ k * (y : ℝ) := by
    have h1 : Real.log (x / y) ≤ Real.log ((2 : ℝ) ^ k) := by
      rw [Real.log_pow]
      rw [div_le_iff₀ hlog2] at hkge
      linarith
    have h2 : x / y ≤ (2 : ℝ) ^ k :=
      (Real.log_le_log_iff (div_pos hx0 hy0) (by positivity)).1 h1
    rwa [div_le_iff₀ hy0] at h2
  have hpk : (2 : ℝ) ^ k ≤ 2 * (x / (y : ℝ)) := by
    have hk2 : ((k : ℝ) - 1) * Real.log 2 ≤ Real.log (x / y) := by
      have h : (k : ℝ) - 1 < Real.log (x / y) / Real.log 2 := by linarith
      rw [lt_div_iff₀ hlog2] at h
      linarith
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log (2 * (x / (y : ℝ))) := by
      rw [Real.log_pow, Real.log_mul (by norm_num) (div_pos hx0 hy0).ne']
      linarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).1 h1
  -- split off the rough integers below `y`, of which there is exactly one
  have hsplit : (roughCount y x : ℝ) = (roughCount y (y : ℝ) : ℝ)
      + (({n ∈ Finset.Ioc ⌊(y : ℝ)⌋₊ ⌊x⌋₊ | IsRough y n}).card : ℝ) := by
    have h := roughCount_sub_eq_card (y := y) (x := (y : ℝ)) (H := x - (y : ℝ)) (by linarith)
    rw [show (y : ℝ) + (x - (y : ℝ)) = x by ring] at h
    linarith
  have hone : (roughCount y (y : ℝ) : ℝ) ≤ 1 := by exact_mod_cast roughCount_self_le_one y
  have hsub : {n ∈ Finset.Ioc ⌊(y : ℝ)⌋₊ ⌊x⌋₊ | IsRough y n}
      ⊆ {n ∈ Finset.Ioc ⌊(y : ℝ)⌋₊ ⌊(2 : ℝ) ^ k * (y : ℝ)⌋₊ | IsRough y n} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_le_floor hdom)⟩, hn.2⟩
  have hcard : (({n ∈ Finset.Ioc ⌊(y : ℝ)⌋₊ ⌊x⌋₊ | IsRough y n}).card : ℝ)
      ≤ 2 ^ k * (C * (y : ℝ) / Real.log y) := by
    refine le_trans ?_ (hpow y (y : ℝ) k hy le_rfl hHy)
    exact_mod_cast Finset.card_le_card hsub
  have hfinal : (2 : ℝ) ^ k * (C * (y : ℝ) / Real.log y) ≤ 2 * C * x / Real.log y := by
    have h1 := mul_le_mul_of_nonneg_right hpk
      (div_nonneg (mul_nonneg hC.le hy0.le) hlogy.le)
    have heq : (2 * (x / (y : ℝ))) * (C * (y : ℝ) / Real.log y) = 2 * C * x / Real.log y := by
      field_simp
    rwa [heq] at h1
  linarith

/-- **The sieve at `η = y^{-1/2}`, with the `min` collapsed.**  Roughness puts every `r ∈ S`
above `y`, so `t ≥ y` on the intervals that matter; then the sifting range reaches `√y`
(`RMF.sqrt_le_sifting_range`) and the sieve's denominator is at least `½ log y`.

The threshold `y₀` is where the sieve's own `H₀` is paid for, once and for all: `√y ≥ H₀`. -/
theorem exists_sum_inv_sq_indicator_le_sqrt :
    ∃ C y₀ : ℝ, 0 < C ∧ 0 < y₀ ∧
      ∀ (y : ℕ) (S : Finset ℕ), (∀ r ∈ S, IsRough y r) → 2 ≤ y → y₀ ≤ (y : ℝ) →
      ∀ t : ℝ, (y : ℝ) ≤ t →
        ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
            * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + 1 / Real.sqrt y))).indicator (fun _ => (1 : ℝ)) t
          ≤ C * (1 + 1 / Real.sqrt y) ^ 2 * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)
              / (t ^ 2 * Real.log y) := by
  obtain ⟨C, H₀, hC, hH₀, hsieve⟩ := exists_sum_inv_sq_indicator_le_sieve'
  refine ⟨2 * C, max (H₀ ^ 2) 4, by positivity, by positivity, ?_⟩
  intro y S hSr hy hy0 t ht
  have hy4 : (4 : ℝ) ≤ (y : ℝ) := le_trans (le_max_right (H₀ ^ 2) 4) hy0
  have hyH : H₀ ^ 2 ≤ (y : ℝ) := le_trans (le_max_left (H₀ ^ 2) 4) hy0
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hs : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hη : (0 : ℝ) < 1 / Real.sqrt y := by positivity
  have hden0 : (0 : ℝ) < 1 + 1 / Real.sqrt y := by positivity
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  -- `√y ≥ 2`, so `1 + η ≤ 3/2 < 4 ≤ y ≤ t`
  have hs2 : (2 : ℝ) ≤ Real.sqrt y := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy4
  have ht1 : 1 + 1 / Real.sqrt y < t := by
    have hhalf : 1 / Real.sqrt y ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hs (by norm_num)]
      linarith
    linarith
  -- the sieve's own threshold, paid once
  have hHs : H₀ ≤ Real.sqrt y := by
    rw [show H₀ = Real.sqrt (H₀ ^ 2) by rw [Real.sqrt_sq hH₀.le]]
    exact Real.sqrt_le_sqrt hyH
  have hsift := sqrt_le_sifting_range hy ht
  have hkey := hsieve y S hSr hy (1 / Real.sqrt y) t hη ht1 (le_trans hHs hsift)
  have hmin := half_log_le_min_log_of_sqrt_le hy hsift
  have hHnn : (0 : ℝ) ≤ t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1 := by
    have h : (0 : ℝ) ≤ t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) :=
      div_nonneg (mul_nonneg ht0.le hη.le) hden0.le
    linarith
  have hstep : C * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)
        / min (Real.log y) (Real.log (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1))
      ≤ C * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1) / (Real.log y / 2) :=
    div_le_div_of_nonneg_left (mul_nonneg hC.le hHnn) (by linarith) hmin
  have hmul : ((1 + 1 / Real.sqrt y) ^ 2 / t ^ 2)
        * (C * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)
            / min (Real.log y) (Real.log (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)))
      ≤ ((1 + 1 / Real.sqrt y) ^ 2 / t ^ 2)
        * (C * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1) / (Real.log y / 2)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have hfin : ((1 + 1 / Real.sqrt y) ^ 2 / t ^ 2)
        * (C * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1) / (Real.log y / 2))
      = 2 * C * (1 + 1 / Real.sqrt y) ^ 2 * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)
          / (t ^ 2 * Real.log y) := by
    field_simp
    try ring
  linarith [hkey, hmul, hfin]

end RMF
