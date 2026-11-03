/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperSieveLeaves

/-!
# Harper's upper bound at the sieve constant: the certificate, part 3

Intervals 16–23 of `q ∈ [8/9, 1]`.

Above the switch point `8/9`, the constant of `RMF.harper_upper_averaged_sieve_switch` is at most
`20` on each interval `I_i = [8/9 + i/216, 8/9 + (i+1)/216]`.  Each bound is
`RMF.upper_sieve_le_of_end` with three point inequalities certified by interval arithmetic in the
kernel.
-/

namespace RMF

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 16 of the sieve certificate**, `q ∈ [26 / 27, 209 / 216]`. -/
theorem upper_sieve_cert_I16 : ∀ q ∈ Set.Icc (26 / 27 : ℝ) (209 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 26 / 27) (b := 209 / 216) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 27 / 25)
    (cb := 253537 / 100000) (Ub := 73903 / 40000) (e := 209 / 216)
    (r := 2097 / 2000) (j := 115003 / 10000) (d := 12913 / 1250)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 17 of the sieve certificate**, `q ∈ [209 / 216, 35 / 36]`. -/
theorem upper_sieve_cert_I17 : ∀ q ∈ Set.Icc (209 / 216 : ℝ) (35 / 36),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 209 / 216) (b := 35 / 36) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 101)
    (cb := 253537 / 100000) (Ub := 1616629 / 1000000) (e := 35 / 36)
    (r := 5197 / 5000) (j := 23271 / 2000) (d := 9737 / 1000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 18 of the sieve certificate**, `q ∈ [35 / 36, 211 / 216]`. -/
theorem upper_sieve_cert_I18 : ∀ q ∈ Set.Icc (35 / 36 : ℝ) (211 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 35 / 36) (b := 211 / 216) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 18 / 17)
    (cb := 253537 / 100000) (Ub := 692841 / 500000) (e := 211 / 216)
    (r := 2061 / 2000) (j := 58861 / 5000) (d := 18179 / 2000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 19 of the sieve certificate**, `q ∈ [211 / 216, 53 / 54]`. -/
theorem upper_sieve_cert_I19 : ∀ q ∈ Set.Icc (211 / 216 : ℝ) (53 / 54),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 211 / 216) (b := 53 / 54) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 103)
    (cb := 253537 / 100000) (Ub := 230947 / 200000) (e := 53 / 54)
    (r := 5109 / 5000) (j := 23821 / 2000) (d := 83837 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 20 of the sieve certificate**, `q ∈ [53 / 54, 71 / 72]`. -/
theorem upper_sieve_cert_I20 : ∀ q ∈ Set.Icc (53 / 54 : ℝ) (71 / 72),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 53 / 54) (b := 71 / 72) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 27 / 26)
    (cb := 253537 / 100000) (Ub := 230947 / 250000) (e := 53 / 54)
    (r := 10131 / 10000) (j := 15063 / 1250) (d := 15233 / 2000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr ⟨by norm_num, by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 21 of the sieve certificate**, `q ∈ [71 / 72, 107 / 108]`. -/
theorem upper_sieve_cert_I21 : ∀ q ∈ Set.Icc (71 / 72 : ℝ) (107 / 108),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 71 / 72) (b := 107 / 108) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 36 / 35)
    (cb := 253537 / 100000) (Ub := 692841 / 1000000) (e := 71 / 72)
    (r := 5023 / 5000) (j := 1524 / 125) (d := 16961 / 2500)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr ⟨by norm_num, by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 22 of the sieve certificate**, `q ∈ [107 / 108, 215 / 216]`. -/
theorem upper_sieve_cert_I22 : ∀ q ∈ Set.Icc (107 / 108 : ℝ) (215 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 107 / 108) (b := 215 / 216) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 54 / 53)
    (cb := 253537 / 100000) (Ub := 230947 / 500000) (e := 107 / 108)
    (r := 9963 / 10000) (j := 123353 / 10000) (d := 14703 / 2500)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr ⟨by norm_num, by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 23 of the sieve certificate**, `q ∈ [215 / 216, 1]`. -/
theorem upper_sieve_cert_I23 : ∀ q ∈ Set.Icc (215 / 216 : ℝ) (1),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 215 / 216) (b := 1) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 107)
    (cb := 253537 / 100000) (Ub := 230947 / 1000000) (e := 215 / 216)
    (r := 247 / 250) (j := 62401 / 5000) (d := 24519 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr ⟨by norm_num, by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

end RMF
