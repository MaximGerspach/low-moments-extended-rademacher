/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperSwitch
import RMF.Reduction.UpperSieveCertificate1
import RMF.Reduction.UpperSieveCertificate2
import RMF.Reduction.UpperSieveCertificate3

/-!
# Harper's upper bound with the constant `20`

`RMF.harper_upper_averaged_sieve_switch` at the switch point `p = 8/9`, `δ = 1/100`,
`k = 1001/1000`, `η = 1/100`, `L₀ = 10⁶`, and parameters `A`, `λ₀`, `T`, `κ` constant on each of
the intervals `[8/9 + i/216, 8/9 + (i+1)/216]` of `[8/9, 1]` (`RMF.sieveCertA` …, looked up at
`RMF.sieveCertIdx q = ⌈216(q - 8/9)⌉₊`).

* Above `8/9` the chain's constant is certified below `20` interval by interval
  (`RMF/Reduction/UpperSieveCertificate{1,2,3}.lean`; the worst interval gives `15.37`), with the
  good set's log-slope `β = 11/20`.
* At `8/9` it is at most `C_p = 14981 / 1000`.
* Below `8/9` the descent `C_p^{q/p}((1-q)/(1-p))^q` is at most `20` on each interval of a
  partition of `[0, 8/9]` (`RMF.switchDescent_le_of_end`; the worst gives `19.96`).

The threshold is `x₀ = exp(exp 10⁴)`: `N = 99²` blocks with room at `δ`, the chaos from
`exp(exp 9900)` and the reduction from `log log x = 10⁴` (`RMF/Reduction/UpperNumerals.lean`).
Below `x₀`, `E|S_x|^{2q} ≤ 1` costs `max_q (1 + (1-q)√(log log x₀))^q ≤ 16`
(`RMF.harper_upper_of_rpow_le`, `RMF.harper_level_small_range`).  Probability Result 1 enters at
the Gaussian constant (`RMF.result1Affine_sharp`).

For the Steinhaus random multiplicative function, every `q ∈ [0, 1]` and every `x ≥ 1`,
`E|S_x|^{2q} ≤ 20·(1 + (1-q)√(log log x))^{-q}` (`RMF.harper_upper_numeral`).
-/

open MeasureTheory

namespace RMF

/-- The interval of the sieve certificate containing `q ∈ [8/9, 1]`: `⌈216(q - 8/9)⌉₊`, which is
`i + 1` on `(8/9 + i/216, 8/9 + (i+1)/216]` and `0` at `q = 8/9`. -/
noncomputable def sieveCertIdx (q : ℝ) : ℕ := ⌈216 * (q - 8 / 9)⌉₊

/-- The level `A` of the sieve certificate on each interval. -/
noncomputable def sieveCertTableA : ℕ → ℝ
  | 0 => 39
  | 1 => 40
  | 2 => 40
  | 3 => 39
  | 4 => 41
  | 5 => 42
  | 6 => 42
  | 7 => 43
  | 8 => 44
  | 9 => 44
  | 10 => 45
  | 11 => 41
  | 12 => 38
  | 13 => 36
  | 14 => 35
  | 15 => 33
  | 16 => 32
  | 17 => 32
  | 18 => 32
  | 19 => 32
  | 20 => 32
  | 21 => 32
  | 22 => 32
  | 23 => 32
  | 24 => 32
  | _ => 32
/-- The Jensen parameter `λ₀` of the sieve certificate on each interval. -/
noncomputable def sieveCertTableLam : ℕ → ℝ
  | 0 => 8
  | 1 => 8
  | 2 => 8
  | 3 => 8
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 6
  | 14 => 6
  | 15 => 6
  | 16 => 6
  | 17 => 6
  | 18 => 6
  | 19 => 6
  | 20 => 6
  | 21 => 6
  | 22 => 6
  | 23 => 6
  | 24 => 6
  | _ => 6
/-- The parameter `T` of Probability Result 1 in the sieve certificate on each interval. -/
noncomputable def sieveCertTableT : ℕ → ℝ
  | 0 => 60
  | 1 => 60
  | 2 => 60
  | 3 => 60
  | 4 => 60
  | 5 => 60
  | 6 => 60
  | 7 => 60
  | 8 => 60
  | 9 => 60
  | 10 => 60
  | 11 => 60
  | 12 => 60
  | 13 => 60
  | 14 => 60
  | 15 => 60
  | 16 => 60
  | 17 => 60
  | 18 => 60
  | 19 => 60
  | 20 => 60
  | 21 => 60
  | 22 => 60
  | 23 => 60
  | 24 => 60
  | _ => 60
/-- The concavity point `κ` of the free start in the sieve certificate on each interval. -/
noncomputable def sieveCertTableKappa : ℕ → ℝ
  | 0 => 16
  | 1 => 16
  | 2 => 16
  | 3 => 16
  | 4 => 16
  | 5 => 16
  | 6 => 16
  | 7 => 16
  | 8 => 16
  | 9 => 16
  | 10 => 16
  | 11 => 16
  | 12 => 16
  | 13 => 16
  | 14 => 16
  | 15 => 16
  | 16 => 16
  | 17 => 16
  | 18 => 16
  | 19 => 16
  | 20 => 16
  | 21 => 16
  | 22 => 16
  | 23 => 16
  | 24 => 16
  | _ => 16
noncomputable def sieveCertA (q : ℝ) : ℝ := sieveCertTableA (sieveCertIdx q)

noncomputable def sieveCertLam (q : ℝ) : ℝ := sieveCertTableLam (sieveCertIdx q)

noncomputable def sieveCertT (q : ℝ) : ℝ := sieveCertTableT (sieveCertIdx q)

noncomputable def sieveCertKappa (q : ℝ) : ℝ := sieveCertTableKappa (sieveCertIdx q)

lemma sieveCertTableA_bounds (n : ℕ) : 32 ≤ sieveCertTableA n ∧ sieveCertTableA n ≤ 45 := by
  unfold sieveCertTableA
  split <;> norm_num

lemma one_le_sieveCertTableLam (n : ℕ) : 1 ≤ sieveCertTableLam n := by
  unfold sieveCertTableLam
  split <;> norm_num

lemma four_lt_sieveCertTableT (n : ℕ) : 4 < sieveCertTableT n := by
  unfold sieveCertTableT
  split <;> norm_num

lemma one_le_sieveCertTableKappa (n : ℕ) : 1 ≤ sieveCertTableKappa n := by
  unfold sieveCertTableKappa
  split <;> norm_num

set_option maxHeartbeats 4000000 in
-- twenty-five cases, each a table lookup and one interval of the certificate
/-- **The certified constant on `[8/9, 1]`, at the sieve constant.** -/
theorem upper_sieve_cert_le {p : ℝ} (hp : 8 / 9 ≤ p) (hp1 : p ≤ 1) :
    1001 / 1000 * reductionSieveConst p * chaosAveragedConst sieveCertA sieveCertLam sieveCertT
      sieveCertKappa (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 p + 1 / 100 ≤ 20 := by
  obtain ⟨k, hkdef⟩ : ∃ k, sieveCertIdx p = k := ⟨_, rfl⟩
  have hk : k ≤ 24 := by
    rw [← hkdef, sieveCertIdx]
    exact Nat.ceil_le.2 (by push_cast; linarith)
  have hhi216 : 216 * (p - 8 / 9) ≤ (k : ℝ) := by
    rw [← hkdef, sieveCertIdx]
    exact Nat.le_ceil _
  interval_cases k
  · -- index 0
    have hlo : (8 / 9 : ℝ) ≤ p := hp
    have hhi : p ≤ 8 / 9 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 39) (lam := 8) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact le_trans (upper_sieve_cert_P p ⟨hlo, hhi⟩) (by norm_num)
  · -- index 1
    have hlo : (8 / 9 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 0 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 193 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 40) (lam := 8) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I00 p ⟨hlo, hhi⟩
  · -- index 2
    have hlo : (193 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 1 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 97 / 108 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 40) (lam := 8) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I01 p ⟨hlo, hhi⟩
  · -- index 3
    have hlo : (97 / 108 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 2 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 65 / 72 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 39) (lam := 8) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I02 p ⟨hlo, hhi⟩
  · -- index 4
    have hlo : (65 / 72 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 3 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 49 / 54 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 41) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I03 p ⟨hlo, hhi⟩
  · -- index 5
    have hlo : (49 / 54 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 4 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 197 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 42) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I04 p ⟨hlo, hhi⟩
  · -- index 6
    have hlo : (197 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 5 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 11 / 12 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 42) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I05 p ⟨hlo, hhi⟩
  · -- index 7
    have hlo : (11 / 12 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 6 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 199 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 43) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I06 p ⟨hlo, hhi⟩
  · -- index 8
    have hlo : (199 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 7 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 25 / 27 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 44) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I07 p ⟨hlo, hhi⟩
  · -- index 9
    have hlo : (25 / 27 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 8 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 67 / 72 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 44) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I08 p ⟨hlo, hhi⟩
  · -- index 10
    have hlo : (67 / 72 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 9 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 101 / 108 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 45) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I09 p ⟨hlo, hhi⟩
  · -- index 11
    have hlo : (101 / 108 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 10 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 203 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 41) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I10 p ⟨hlo, hhi⟩
  · -- index 12
    have hlo : (203 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 11 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 17 / 18 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 38) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I11 p ⟨hlo, hhi⟩
  · -- index 13
    have hlo : (17 / 18 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 12 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 205 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 36) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I12 p ⟨hlo, hhi⟩
  · -- index 14
    have hlo : (205 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 13 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 103 / 108 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 35) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I13 p ⟨hlo, hhi⟩
  · -- index 15
    have hlo : (103 / 108 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 14 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 23 / 24 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 33) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I14 p ⟨hlo, hhi⟩
  · -- index 16
    have hlo : (23 / 24 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 15 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 26 / 27 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I15 p ⟨hlo, hhi⟩
  · -- index 17
    have hlo : (26 / 27 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 16 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 209 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I16 p ⟨hlo, hhi⟩
  · -- index 18
    have hlo : (209 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 17 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 35 / 36 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I17 p ⟨hlo, hhi⟩
  · -- index 19
    have hlo : (35 / 36 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 18 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 211 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I18 p ⟨hlo, hhi⟩
  · -- index 20
    have hlo : (211 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 19 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 53 / 54 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I19 p ⟨hlo, hhi⟩
  · -- index 21
    have hlo : (53 / 54 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 20 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 71 / 72 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I20 p ⟨hlo, hhi⟩
  · -- index 22
    have hlo : (71 / 72 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 21 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 107 / 108 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I21 p ⟨hlo, hhi⟩
  · -- index 23
    have hlo : (107 / 108 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 22 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 215 / 216 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I22 p ⟨hlo, hhi⟩
  · -- index 24
    have hlo : (215 / 216 : ℝ) ≤ p := by
      have h := Nat.lt_ceil.1 (show 23 < ⌈216 * (p - 8 / 9)⌉₊ by
        rw [← sieveCertIdx, hkdef]; norm_num)
      push_cast at h
      linarith
    have hhi : p ≤ 1 := by
      have h := hhi216
      push_cast at h
      linarith
    rw [chaosAveragedConst_eq_const (A := 32) (lam := 6) (T := 60) (κ := 16) (β := 11 / 20)
      (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
      (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
    exact upper_sieve_cert_I23 p ⟨hlo, hhi⟩

/-- **The chain's constant at the switch point `8/9`** is at most `14981 / 1000`. -/
theorem upper_sieve_cert_switch :
    1001 / 1000 * reductionSieveConst (8 / 9) * chaosAveragedConst sieveCertA sieveCertLam
      sieveCertT sieveCertKappa (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000 (8 / 9) + 1 / 100
        ≤ 14981 / 1000 := by
  have hkdef : sieveCertIdx (8 / 9) = 0 := by
    unfold sieveCertIdx
    norm_num
  rw [chaosAveragedConst_eq_const (A := 39) (lam := 8) (T := 60) (κ := 16) (β := 11 / 20)
    (by rw [sieveCertA, hkdef]; rfl) (by rw [sieveCertLam, hkdef]; rfl)
    (by rw [sieveCertT, hkdef]; rfl) (by rw [sieveCertKappa, hkdef]; rfl) (by rfl)]
  exact upper_sieve_cert_P (8 / 9) ⟨le_rfl, le_rfl⟩

set_option maxHeartbeats 4000000 in
-- 9 cases, each one kernel interval check
/-- **The certified constant for every `q ∈ [0, 1]`**: the chain above `8/9`
(`RMF.upper_sieve_cert_le`), and below it the descent from `C_p ≤ 14981 / 1000`
(`RMF.upper_sieve_cert_switch`) on 9 intervals (`RMF.switchDescent_le_of_end`). -/
theorem upperSwitchConst_cert_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    upperSwitchConst (chaosAveragedConst sieveCertA sieveCertLam sieveCertT sieveCertKappa
      (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000) (1001 / 1000) (1 / 100) (8 / 9) q
        ≤ 20 := by
  unfold upperSwitchConst
  split_ifs with hpq
  · exact upper_sieve_cert_le hpq hq1
  have hqp : q < 8 / 9 := not_le.1 hpq
  have hCp := upper_sieve_cert_switch
  have hC0 : 0 ≤ 1001 / 1000 * reductionSieveConst (8 / 9) * chaosAveragedConst sieveCertA
      sieveCertLam sieveCertT sieveCertKappa (fun _ => 11 / 20) (1 / 100) (1001 / 1000) 1000000
        (8 / 9) + 1 / 100 := by
    have h1 := reductionSieveConst_nonneg (8 / 9)
    have h2 := chaosAveragedConst_nonneg (Af := sieveCertA) (lamf := sieveCertLam)
      (Tf := sieveCertT) (κf := sieveCertKappa) (βf := fun _ => 11 / 20) (δ := 1 / 100)
      (L₀ := 1000000) (q := 8 / 9)
      (by norm_num : (0 : ℝ) ≤ 1001 / 1000) (le_trans zero_le_one (one_le_sieveCertTableLam _))
    have h3 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1001 / 1000) h1) h2
    linarith
  rcases le_or_gt q (571 / 1000) with h1 | h1
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 0) (q₂ := 571 / 1000) (r := 5139 / 8000) (s := 9)
      (by norm_num) (by norm_num) (by norm_num) hq0 h1 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (681 / 1000) with h2 | h2
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 571 / 1000) (q₂ := 681 / 1000) (r := 6129 / 8000) (s := 3861 / 1000)
      (by norm_num) (by norm_num) (by norm_num) h1.le h2 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (73 / 100) with h3 | h3
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 681 / 1000) (q₂ := 73 / 100) (r := 657 / 800) (s := 2871 / 1000)
      (by norm_num) (by norm_num) (by norm_num) h2.le h3 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (761 / 1000) with h4 | h4
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 73 / 100) (q₂ := 761 / 1000) (r := 6849 / 8000) (s := 243 / 100)
      (by norm_num) (by norm_num) (by norm_num) h3.le h4 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (1571 / 2000) with h5 | h5
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 761 / 1000) (q₂ := 1571 / 2000) (r := 14139 / 16000) (s := 2151 / 1000)
      (by norm_num) (by norm_num) (by norm_num) h4.le h5 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (1617 / 2000) with h6 | h6
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 1571 / 2000) (q₂ := 1617 / 2000) (r := 14553 / 16000) (s := 3861 / 2000)
      (by norm_num) (by norm_num) (by norm_num) h5.le h6 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (417 / 500) with h7 | h7
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 1617 / 2000) (q₂ := 417 / 500) (r := 3753 / 4000) (s := 3447 / 2000)
      (by norm_num) (by norm_num) (by norm_num) h6.le h7 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (1737 / 2000) with h8 | h8
  · exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 417 / 500) (q₂ := 1737 / 2000) (r := 15633 / 16000) (s := 747 / 500)
      (by norm_num) (by norm_num) (by norm_num) h7.le h8 (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))
  exact le_trans (switchDescent_le_of_end (c := 14981 / 1000) (p := 8 / 9)
      (q₁ := 1737 / 2000) (q₂ := 8 / 9) (r := 1) (s := 2367 / 2000)
      (by norm_num) (by norm_num) (by norm_num) h8.le hqp.le (by norm_num) hC0 hCp (by norm_num)
      (by norm_num) (by norm_num)) (by interval_decide (trust := kernel))

/-- **Room for the certificate's levels**: the block count `N = 99²` at `δ = 1/100` and
`A ≤ 45`, `45/4 + 3·99/4 + 1 ≤ 98.01`. -/
lemma sieveCert_room :
    (45 : ℝ) / 4 + 3 * Real.sqrt ((9801 : ℕ) : ℝ) / 4 + 1 ≤ 1 / 100 * ((9801 : ℕ) : ℝ) := by
  rw [sqrt_nine_thousand_eight_hundred_one]
  norm_num

/-- **Harper's upper bound with the constant `20`.**  For the Steinhaus random multiplicative
function, every `q ∈ [0, 1]` and every `x ≥ 1`,

`E|S_x|^{2q} ≤ 20·(1 + (1-q)√(log log x))^{-q}`.

Past `x₀ = exp(exp 10⁴)` it is `RMF.harper_upper_averaged_sieve_switch` at the switch point `8/9`
and the certificate's parameters, with `N = 99²` blocks, the chaos from `exp(exp 9900)` and the
level `Λ = 10⁴`, and `RMF.upperSwitchConst_cert_le`.  Below `x₀` it is `E|S_x|^{2q} ≤ 1`, at the
cost `max_q (1 + (1-q)√(log log x₀))^q ≤ 16` (`RMF.harper_upper_of_rpow_le`). -/
theorem harper_upper_numeral {Ω : Type*} [MeasurableSpace Ω] :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, 1 ≤ x → 0 ≤ q → q ≤ 1 →
        ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
          ≤ 20 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  intro f μ hf x q hx hq0 hq1
  refine harper_upper_of_rpow_le hf (fun q hq0 hq1 => le_trans (harper_level_small_range hq0 hq1)
    (by norm_num)) (fun x q hx hq0 hq1 => ?_) hx hq0 hq1
  have hA : ∀ t, harperBadLevel 0 ≤ sieveCertA t ∧ sieveCertA t ≤ 45 := fun t =>
    ⟨le_trans harperBadLevel_zero_le (sieveCertTableA_bounds _).1, (sieveCertTableA_bounds _).2⟩
  have h := harper_upper_averaged_sieve_switch (A := sieveCertA) (lam := sieveCertLam)
    (T := sieveCertT) (κ := sieveCertKappa) (β := fun _ => 11 / 20) (Amax := 45) (δ := 1 / 100)
    (k := 1001 / 1000) (η := 1 / 100) (L₀ := 1000000) (ℓ₀ := 9900) (Λ := 10000) (N := 9801)
    (p := 8 / 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hA (fun t => one_le_sieveCertTableLam _) (fun t => four_lt_sieveCertTableT _)
    (fun t => one_le_sieveCertTableKappa _) (fun _ => ⟨by norm_num, by norm_num⟩) sieveCert_room
    harper_level_room_mono harper_level_blocks harper_level_k harper_level_mertens
    (le_trans (by norm_num) harper_level_mertens) (by norm_num) harper_level_start
    harper_level_cutoff harper_level_rankin harper_level_eta f μ hf x q hx hq0 hq1
  refine le_trans h (mul_le_mul_of_nonneg_right (upperSwitchConst_cert_le hq0 hq1) ?_)
  refine Real.rpow_nonneg ?_ _
  have := mul_nonneg (sub_nonneg.2 hq1) (Real.sqrt_nonneg (Real.log (Real.log x)))
  linarith

end RMF
