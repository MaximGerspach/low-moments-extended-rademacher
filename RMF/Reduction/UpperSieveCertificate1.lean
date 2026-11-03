/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperSieveLeaves

/-!
# Harper's upper bound at the sieve constant: the certificate, part 1

Intervals 0–7 of `q ∈ [8/9, 1]` and the switch point `8/9`.

Above the switch point, the constant of `RMF.harper_upper_averaged_sieve_switch` is at most `20` on
each interval `I_i = [8/9 + i/216, 8/9 + (i+1)/216]`, and at `8/9` it is at most `14981 / 1000`.
Each bound is `RMF.upper_sieve_le_of_end` with three point inequalities certified by interval
arithmetic in the kernel.
-/

namespace RMF

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **The sieve certificate at the switch point** `q = 8/9`: the chain's constant
is at most `14981 / 1000`. -/
theorem upper_sieve_cert_P : ∀ q ∈ Set.Icc (8 / 9 : ℝ) (8 / 9),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 39) (fun _ => 8)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 14981 / 1000 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 8 / 9) (b := 8 / 9) (A := 39) (lam := 8) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 9 / 7)
    (cb := 2444821 / 1000000) (Ub := 6320503 / 1000000) (e := 8 / 9)
    (r := 2423 / 2000) (j := 29473 / 2500) (d := 61661 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 0 of the sieve certificate**, `q ∈ [8 / 9, 193 / 216]`. -/
theorem upper_sieve_cert_I00 : ∀ q ∈ Set.Icc (8 / 9 : ℝ) (193 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 40) (fun _ => 8)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 8 / 9) (b := 193 / 216) (A := 40) (lam := 8) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 9 / 7)
    (cb := 2444821 / 1000000) (Ub := 3215807 / 500000) (e := 193 / 216)
    (r := 6083 / 5000) (j := 14927 / 1250) (d := 15747 / 1250)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 1 of the sieve certificate**, `q ∈ [193 / 216, 97 / 108]`. -/
theorem upper_sieve_cert_I01 : ∀ q ∈ Set.Icc (193 / 216 : ℝ) (97 / 108),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 40) (fun _ => 8)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 193 / 216) (b := 97 / 108) (A := 40) (lam := 8) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 85)
    (cb := 2444821 / 1000000) (Ub := 616363 / 100000) (e := 97 / 108)
    (r := 6023 / 5000) (j := 1512 / 125) (d := 31003 / 2500)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 2 of the sieve certificate**, `q ∈ [97 / 108, 65 / 72]`. -/
theorem upper_sieve_cert_I02 : ∀ q ∈ Set.Icc (97 / 108 : ℝ) (65 / 72),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 39) (fun _ => 8)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 97 / 108) (b := 65 / 72) (A := 39) (lam := 8) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 54 / 43)
    (cb := 2444821 / 1000000) (Ub := 1158759 / 200000) (e := 65 / 72)
    (r := 1491 / 1250) (j := 30631 / 2500) (d := 12237 / 1000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 3 of the sieve certificate**, `q ∈ [65 / 72, 49 / 54]`. -/
theorem upper_sieve_cert_I03 : ∀ q ∈ Set.Icc (65 / 72 : ℝ) (49 / 54),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 41) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 65 / 72) (b := 49 / 54) (A := 41) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 36 / 29)
    (cb := 253537 / 100000) (Ub := 1144977 / 200000) (e := 49 / 54)
    (r := 11813 / 10000) (j := 98801 / 10000) (d := 61861 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 4 of the sieve certificate**, `q ∈ [49 / 54, 197 / 216]`. -/
theorem upper_sieve_cert_I04 : ∀ q ∈ Set.Icc (49 / 54 : ℝ) (197 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 42) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 49 / 54) (b := 197 / 216) (A := 42) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 27 / 22)
    (cb := 253537 / 100000) (Ub := 173277 / 31250) (e := 197 / 216)
    (r := 11699 / 10000) (j := 49981 / 5000) (d := 121331 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 5 of the sieve certificate**, `q ∈ [197 / 216, 11 / 12]`. -/
theorem upper_sieve_cert_I05 : ∀ q ∈ Set.Icc (197 / 216 : ℝ) (11 / 12),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 42) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 197 / 216) (b := 11 / 12) (A := 42) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 89)
    (cb := 253537 / 100000) (Ub := 5267621 / 1000000) (e := 11 / 12)
    (r := 2897 / 2500) (j := 6321 / 625) (d := 59387 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 6 of the sieve certificate**, `q ∈ [11 / 12, 199 / 216]`. -/
theorem upper_sieve_cert_I06 : ∀ q ∈ Set.Icc (11 / 12 : ℝ) (199 / 216),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 43) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 11 / 12) (b := 199 / 216) (A := 43) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 6 / 5)
    (cb := 253537 / 100000) (Ub := 5073711 / 1000000) (e := 199 / 216)
    (r := 11479 / 10000) (j := 4093 / 400) (d := 58039 / 5000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

set_option maxHeartbeats 4000000 in
-- three kernel interval checks and exact rational arithmetic on long numerals
/-- **Interval 7 of the sieve certificate**, `q ∈ [199 / 216, 25 / 27]`. -/
theorem upper_sieve_cert_I07 : ∀ q ∈ Set.Icc (199 / 216 : ℝ) (25 / 27),
    1001 / 1000 * reductionSieveConst q * chaosAveragedConst (fun _ => 44) (fun _ => 6)
      (fun _ => 60) (fun _ => 16) (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 q
        + 1 / 100 ≤ 20 := by
  intro q hq
  exact upper_sieve_le_of_end (a := 199 / 216) (b := 25 / 27) (A := 44) (lam := 6) (T := 60)
    (κ := 16) (β := 11 / 20) (LB := 26249 / 500)
    (ℓκ := 2772589 / 1000000) (ℓKT := 852243 / 200000) (ia := 108 / 91)
    (cb := 253537 / 100000) (Ub := 2435271 / 500000) (e := 25 / 27)
    (r := 11371 / 10000) (j := 103527 / 10000) (d := 113257 / 10000)
    (by norm_num) hq.1 hq.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by interval_decide (trust := kernel))
    log_sixteen_le log_KT_sixty_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨by norm_num, rfl⟩)
    (by interval_decide (trust := kernel)) (by interval_decide (trust := kernel))
    (by interval_decide (trust := kernel)) (by norm_num)

end RMF
