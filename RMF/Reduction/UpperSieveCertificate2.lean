/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperSieveLeaves

/-!
# Harper's upper bound at the sieve constant: the certificate, part 2

Intervals 8–15 of `q ∈ [8/9, 1]`.

Above the switch point `8/9`, the constant of `RMF.harper_upper_averaged_sieve_switch` is at most
`20` on each interval `I_i = [8/9 + i/216, 8/9 + (i+1)/216]`.  Each bound is
`RMF.upper_sieve_le_of_end` with three point inequalities certified by interval arithmetic in the
kernel.
-/

namespace RMF

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 8 of the sieve certificate**, `q ∈ [25 / 27, 67 / 72]`. -/
theorem upper_sieve_cert_I08 : ∀ q ∈ Set.Icc (25 / 27 : ℝ) (67 / 72),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 44) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 25 / 27) (b := 67 / 72) (A := 44) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 27 / 23)
    (cb := 253537 / 100000) (Ub := 4584039 / 1000000) (e := 67 / 72)
    (r := 5633 / 5000) (j := 104743 / 10000) (d := 110267 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 9 of the sieve certificate**, `q ∈ [67 / 72, 101 / 108]`. -/
theorem upper_sieve_cert_I09 : ∀ q ∈ Set.Icc (67 / 72 : ℝ) (101 / 108),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 45) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 67 / 72) (b := 101 / 108) (A := 45) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 36 / 31)
    (cb := 253537 / 100000) (Ub := 4366981 / 1000000) (e := 101 / 108)
    (r := 5581 / 5000) (j := 52987 / 5000) (d := 107123 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 10 of the sieve certificate**, `q ∈ [101 / 108, 203 / 216]`. -/
theorem upper_sieve_cert_I10 : ∀ q ∈ Set.Icc (101 / 108 : ℝ) (203 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 41) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 101 / 108) (b := 203 / 216) (A := 41) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 54 / 47)
    (cb := 253537 / 100000) (Ub := 381659 / 100000) (e := 203 / 216)
    (r := 11061 / 10000) (j := 107219 / 10000) (d := 106223 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 11 of the sieve certificate**, `q ∈ [203 / 216, 17 / 18]`. -/
theorem upper_sieve_cert_I11 : ∀ q ∈ Set.Icc (203 / 216 : ℝ) (17 / 18),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 38) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 203 / 216) (b := 17 / 18) (A := 38) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 95)
    (cb := 253537 / 100000) (Ub := 3363421 / 1000000) (e := 17 / 18)
    (r := 10961 / 10000) (j := 108479 / 10000) (d := 53981 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 12 of the sieve certificate**, `q ∈ [17 / 18, 205 / 216]`. -/
theorem upper_sieve_cert_I12 : ∀ q ∈ Set.Icc (17 / 18 : ℝ) (205 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 36) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 17 / 18) (b := 205 / 216) (A := 36) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 9 / 8)
    (cb := 253537 / 100000) (Ub := 598717 / 200000) (e := 205 / 216)
    (r := 5431 / 5000) (j := 54877 / 5000) (d := 27401 / 2500)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 13 of the sieve certificate**, `q ∈ [205 / 216, 103 / 108]`. -/
theorem upper_sieve_cert_I13 : ∀ q ∈ Set.Icc (205 / 216 : ℝ) (103 / 108),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 35) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 205 / 216) (b := 103 / 108) (A := 35) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 97)
    (cb := 253537 / 100000) (Ub := 1346597 / 500000) (e := 103 / 108)
    (r := 5383 / 5000) (j := 111043 / 10000) (d := 109003 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 14 of the sieve certificate**, `q ∈ [103 / 108, 23 / 24]`. -/
theorem upper_sieve_cert_I14 : ∀ q ∈ Set.Icc (103 / 108 : ℝ) (23 / 24),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 33) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 103 / 108) (b := 23 / 24) (A := 33) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 54 / 49)
    (cb := 253537 / 100000) (Ub := 471153 / 200000) (e := 23 / 24)
    (r := 1067 / 1000) (j := 28087 / 2500) (d := 22137 / 2000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 15 of the sieve certificate**, `q ∈ [23 / 24, 26 / 27]`. -/
theorem upper_sieve_cert_I15 : ∀ q ∈ Set.Icc (23 / 24 : ℝ) (26 / 27),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 32) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 23 / 24) (b := 26 / 27) (A := 32) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 12 / 11)
    (cb := 253537 / 100000) (Ub := 1039261 / 500000) (e := 26 / 27)
    (r := 10577 / 10000) (j := 28417 / 2500) (d := 54367 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

end RMF
