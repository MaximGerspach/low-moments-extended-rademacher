/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CentralWindowBand
import RMF.Weighted.MesoscopicBandFamily
import RMF.Weighted.FarRangeBand
import RMF.Weighted.LineSplit

/-!
# Proposition B: the pieces

**Proposition B** is the bound, for a band of primes `(y, z]`,

`E[((log z)⁻¹∫_ℝ |F_{y,z}(½-c+it)|²/|c+it|² dt)^q] ≪ κ^{q(2q-1)}·b(min{1/(2q-1), log κ})`,

`c = 1/(2 log z)`, `κ = log z/log y`, with `b` the ballot factor below; it is assembled, for
`½ < q ≤ 1`, in `RMF/Weighted/PropositionBAssembly.lean`.  It comes from its three ranges: the
central window (`RMF.integral_rpow_centralWindow_primesIco_le`), the mesoscopic range
(`RMF.exists_const_integral_rpow_mesoRange_band_le_rademacher`) and the far range
(`RMF.integral_rpow_farRange_primesIco_le`).  This file holds what the assembly needs besides them:

* the ballot factor `b(m) = m/(1+(1-q)√m)^q` (`RMF.ballotFactor`): increasing, `b(λm) ≤ λ·b(m)`
  for `λ ≥ 1`, and `b ≥ ½` on `m ≥ 1`;
* the conversion of the mesoscopic range's bound `e^{J_b γ}·b(min{J_b, ⌈γ^{-1}⌉})` into the form
  `κ^γ·b(min{1/(2q-1), log κ})`, at a cost `3e` (`RMF.exp_mul_ballotFactor_le`);
* the split of `∫_ℝ` into the three ranges, for any damped line integrand
  (`RMF.integral_rpow_lineDiv_le_of_three_ranges`);
* the crude bound `(πe^{45}/(c·log y))^q` on the whole line, for the bands too short or too low
  for the three ranges to apply (`RMF.integral_rpow_lineDiv_primesIco_le`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The ballot factor `b(m)` -/

/-- **The ballot factor** `b(m) = m/(1+(1-q)√m)^q`. -/
noncomputable def ballotFactor (q m : ℝ) : ℝ := m * (1 + (1 - q) * Real.sqrt m) ^ (-q)

/-- **The ratio bound for `b`.**  For `0 < m₁ ≤ m₂` and `0 ≤ q ≤ 1`,
`(m₂/m₁)^{1-q/2}·b(m₁) ≤ b(m₂)`.  With `r = √m₂/√m₁ ≥ 1`, `1+(1-q)√m₂ ≤ r·(1+(1-q)√m₁)`, so
`b(m₂) ≥ r^{2-q}·b(m₁)`, and `r^{2-q} = (m₂/m₁)^{1-q/2}`. -/
lemma rpow_mul_ballotFactor_le {q m₁ m₂ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hm₁ : 0 < m₁)
    (hm : m₁ ≤ m₂) : (m₂ / m₁) ^ (1 - q / 2) * ballotFactor q m₁ ≤ ballotFactor q m₂ := by
  unfold ballotFactor
  have ha : (0 : ℝ) ≤ 1 - q := by linarith
  have hm₂ : 0 < m₂ := lt_of_lt_of_le hm₁ hm
  have hu₁ : 0 < Real.sqrt m₁ := Real.sqrt_pos.2 hm₁
  have hu : Real.sqrt m₁ ≤ Real.sqrt m₂ := Real.sqrt_le_sqrt hm
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt m₂ / Real.sqrt m₁ := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by rw [hr]; exact (one_le_div hu₁).2 hu
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hu₂ : Real.sqrt m₂ = r * Real.sqrt m₁ := by rw [hr, div_mul_cancel₀ _ hu₁.ne']
  have hm₂r : m₂ = r ^ 2 * m₁ := by
    rw [← Real.sq_sqrt hm₂.le, ← Real.sq_sqrt hm₁.le, hu₂]
    ring
  have hB₁ : 0 < 1 + (1 - q) * Real.sqrt m₁ :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg ha hu₁.le)
  have hB₂ : 0 < 1 + (1 - q) * Real.sqrt m₂ :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg ha (Real.sqrt_nonneg _))
  have hbase : 1 + (1 - q) * Real.sqrt m₂ ≤ r * (1 + (1 - q) * Real.sqrt m₁) := by
    have h : r * (1 + (1 - q) * Real.sqrt m₁) - (1 + (1 - q) * Real.sqrt m₂) = r - 1 := by
      rw [hu₂]
      ring
    linarith
  have hpow : (r * (1 + (1 - q) * Real.sqrt m₁)) ^ (-q) ≤ (1 + (1 - q) * Real.sqrt m₂) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hB₂ hbase (by linarith)
  rw [Real.mul_rpow hr0.le hB₁.le] at hpow
  have hratio : (m₂ / m₁) ^ (1 - q / 2) = r ^ 2 * r ^ (-q) := by
    have h1 : m₂ / m₁ = r ^ (2 : ℝ) := by
      rw [hm₂r, Real.rpow_two, mul_div_assoc, div_self hm₁.ne', mul_one]
    rw [h1, ← Real.rpow_mul hr0.le, ← Real.rpow_two, ← Real.rpow_add hr0]
    congr 1
    ring
  calc (m₂ / m₁) ^ (1 - q / 2) * (m₁ * (1 + (1 - q) * Real.sqrt m₁) ^ (-q))
      = r ^ 2 * m₁ * (r ^ (-q) * (1 + (1 - q) * Real.sqrt m₁) ^ (-q)) := by
        rw [hratio]
        ring
    _ ≤ m₂ * (1 + (1 - q) * Real.sqrt m₂) ^ (-q) := by
        rw [← hm₂r]
        exact mul_le_mul_of_nonneg_left hpow hm₂.le

/-- **`b` is increasing** on `m > 0`, for `0 ≤ q ≤ 1`: `RMF.rpow_mul_ballotFactor_le`, whose factor
`(m₂/m₁)^{1-q/2}` is at least `1`. -/
lemma ballotFactor_le_ballotFactor {q m₁ m₂ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hm₁ : 0 < m₁)
    (hm : m₁ ≤ m₂) : ballotFactor q m₁ ≤ ballotFactor q m₂ := by
  have hb0 : 0 ≤ ballotFactor q m₁ := by
    unfold ballotFactor
    exact mul_nonneg hm₁.le (Real.rpow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (by linarith) (Real.sqrt_nonneg _))) _)
  have hr : 1 ≤ (m₂ / m₁) ^ (1 - q / 2) :=
    Real.one_le_rpow ((one_le_div hm₁).2 hm) (by linarith)
  calc ballotFactor q m₁ ≤ (m₂ / m₁) ^ (1 - q / 2) * ballotFactor q m₁ :=
        le_mul_of_one_le_left hb0 hr
    _ ≤ ballotFactor q m₂ := rpow_mul_ballotFactor_le hq0 hq1 hm₁ hm

/-- **The ratio bound at the power `1/(2q)`**: for `½ ≤ q ≤ 1` and `0 < m₁ ≤ m₂`,
`b(m₁)^{1/(2q)} ≤ (m₁/m₂)^{1/4}·b(m₂)^{1/(2q)}`, by `RMF.rpow_mul_ballotFactor_le`, then
`(1-q/2)/(2q) ≥ 1/4` against the ratio `m₁/m₂ ≤ 1`. -/
lemma ballotFactor_rpow_inv_le {q m₁ m₂ : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hm₁ : 0 < m₁)
    (hm : m₁ ≤ m₂) :
    ballotFactor q m₁ ^ (2 * q)⁻¹ ≤ (m₁ / m₂) ^ (1 / 4 : ℝ) * ballotFactor q m₂ ^ (2 * q)⁻¹ := by
  have hq : 0 ≤ q := by linarith
  have hm₂ : 0 < m₂ := lt_of_lt_of_le hm₁ hm
  have hb : ∀ m : ℝ, 0 < m → 0 ≤ ballotFactor q m := fun m hm0 => by
    unfold ballotFactor
    exact mul_nonneg hm0.le (Real.rpow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (by linarith) (Real.sqrt_nonneg _))) _)
  have hρ0 : 0 < m₁ / m₂ := div_pos hm₁ hm₂
  have hρ1 : m₁ / m₂ ≤ 1 := (div_le_one hm₂).2 hm
  -- `b(m₁) ≤ (m₁/m₂)^{1-q/2}·b(m₂)`
  have hinv : (m₁ / m₂) ^ (1 - q / 2) * (m₂ / m₁) ^ (1 - q / 2) = 1 := by
    have h11 : m₁ / m₂ * (m₂ / m₁) = 1 := by
      rw [div_mul_div_comm, mul_comm m₁ m₂, div_self (mul_pos hm₂ hm₁).ne']
    rw [← Real.mul_rpow hρ0.le (div_pos hm₂ hm₁).le, h11, Real.one_rpow]
  have h1 : ballotFactor q m₁ ≤ (m₁ / m₂) ^ (1 - q / 2) * ballotFactor q m₂ := by
    calc ballotFactor q m₁
        = (m₁ / m₂) ^ (1 - q / 2) * ((m₂ / m₁) ^ (1 - q / 2) * ballotFactor q m₁) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ (m₁ / m₂) ^ (1 - q / 2) * ballotFactor q m₂ :=
          mul_le_mul_of_nonneg_left (rpow_mul_ballotFactor_le hq hq1 hm₁ hm)
            (Real.rpow_nonneg hρ0.le _)
  -- at the power `1/(2q)`
  have hw0 : 0 < (2 * q)⁻¹ := inv_pos.2 (by linarith)
  have h2 := Real.rpow_le_rpow (hb m₁ hm₁) h1 hw0.le
  rw [Real.mul_rpow (Real.rpow_nonneg hρ0.le _) (hb m₂ hm₂), ← Real.rpow_mul hρ0.le] at h2
  refine le_trans h2 (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (hb m₂ hm₂) _))
  refine Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 ?_
  have hw : (2 * q)⁻¹ * (2 * q) = 1 := inv_mul_cancel₀ (ne_of_gt (by linarith))
  nlinarith [mul_nonneg (sub_nonneg.2 hq1) hw0.le]

/-- **Scaling the argument of `b`**: `b(λm) ≤ λ·b(m)` for `λ ≥ 1`. -/
lemma ballotFactor_mul_le {q l m : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hm : 0 ≤ m) (hl : 1 ≤ l) :
    ballotFactor q (l * m) ≤ l * ballotFactor q m := by
  unfold ballotFactor
  have ha : (0 : ℝ) ≤ 1 - q := by linarith
  have hB : 0 < 1 + (1 - q) * Real.sqrt m :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg ha (Real.sqrt_nonneg _))
  have hsq : Real.sqrt m ≤ Real.sqrt (l * m) := Real.sqrt_le_sqrt (le_mul_of_one_le_left hm hl)
  have hbase : 1 + (1 - q) * Real.sqrt m ≤ 1 + (1 - q) * Real.sqrt (l * m) := by
    have h := mul_le_mul_of_nonneg_left hsq ha
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hB hbase (by linarith : -q ≤ 0)
  calc l * m * (1 + (1 - q) * Real.sqrt (l * m)) ^ (-q)
      ≤ l * m * (1 + (1 - q) * Real.sqrt m) ^ (-q) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by linarith) hm)
    _ = l * (m * (1 + (1 - q) * Real.sqrt m) ^ (-q)) := by ring

/-- **`b(m) ≥ ½` for `m ≥ 1`**: the base of the power is at least `1` and at most `1+√m ≤ 2m`, and
the power is at least its first. -/
lemma half_le_ballotFactor {q m : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hm : 1 ≤ m) :
    1 / 2 ≤ ballotFactor q m := by
  unfold ballotFactor
  have hm0 : 0 < m := by linarith
  have hmne : m ≠ 0 := hm0.ne'
  have hs0 := Real.sqrt_nonneg m
  have hsm : Real.sqrt m ≤ m := (Real.sqrt_le_left hm0.le).2 (by nlinarith)
  have hqs : 0 ≤ q * Real.sqrt m := mul_nonneg hq0 hs0
  have hexp : (1 - q) * Real.sqrt m = Real.sqrt m - q * Real.sqrt m := by ring
  have hB1 : 1 ≤ 1 + (1 - q) * Real.sqrt m := by
    have := mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) hs0
    linarith
  have hBle : 1 + (1 - q) * Real.sqrt m ≤ 2 * m := by linarith
  have hpow : (1 + (1 - q) * Real.sqrt m) ^ (-1 : ℝ) ≤ (1 + (1 - q) * Real.sqrt m) ^ (-q) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have hinv : (2 * m)⁻¹ ≤ (1 + (1 - q) * Real.sqrt m)⁻¹ := inv_anti₀ (by linarith) hBle
  have hhalf : m * (2 * m)⁻¹ = 1 / 2 := by
    rw [mul_inv, ← mul_assoc, mul_comm m 2⁻¹, mul_assoc, mul_inv_cancel₀ hmne, mul_one, one_div]
  calc (1 : ℝ) / 2 = m * (2 * m)⁻¹ := hhalf.symm
    _ ≤ m * (1 + (1 - q) * Real.sqrt m) ^ (-q) :=
        mul_le_mul_of_nonneg_left (hinv.trans hpow) hm0.le

/-- **The mesoscopic bound of a band, in the form of Proposition B.**  For `½ < q ≤ 1`,
`κ ≥ e` and `1 ≤ J_b ≤ log κ + 1`, with `γ = q(2q-1)`,
`e^{J_b γ}·b(min{J_b, ⌈γ^{-1}⌉}) ≤ 3e·κ^γ·b(min{1/(2q-1), log κ})`.
`e^{J_b γ} ≤ e·κ^γ` because `γ ≤ 1`; and `min{J_b, ⌈γ^{-1}⌉} ≤ 3·min{1/(2q-1), log κ}` because
`J_b ≤ 2 log κ` and `⌈γ^{-1}⌉ ≤ γ^{-1}+1 ≤ 3/(2q-1)`, so `b` increasing
(`RMF.ballotFactor_le_ballotFactor`) and `RMF.ballotFactor_mul_le` give the `3`. -/
lemma exp_mul_ballotFactor_le {q κ : ℝ} {Jb : ℕ} (hq2 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hκ : Real.exp 1 ≤ κ) (hJb1 : 1 ≤ Jb) (hJbκ : (Jb : ℝ) ≤ Real.log κ + 1) :
    Real.exp ((Jb : ℝ) * (q * (2 * q - 1))) * ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ)
        * (1 + (1 - q) * Real.sqrt ((min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ : ℕ) : ℝ)) ^ (-q)
      ≤ 3 * Real.exp 1
        * (κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ))) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hd0 : (0 : ℝ) < 2 * q - 1 := by linarith
  have hγ0 : (0 : ℝ) < q * (2 * q - 1) := mul_pos (by linarith) hd0
  have hγ1 : q * (2 * q - 1) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1) (by linarith : (0 : ℝ) ≤ 2 * q + 1)]
  have hγlo : (2 * q - 1) / 2 ≤ q * (2 * q - 1) := by
    nlinarith [mul_nonneg hd0.le (by linarith : (0 : ℝ) ≤ q - 1 / 2)]
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le (Real.exp_pos 1) hκ
  have hlogκ : (1 : ℝ) ≤ Real.log κ := by
    have h := Real.log_le_log (Real.exp_pos 1) hκ
    rwa [Real.log_exp] at h
  have hdinv : (1 : ℝ) ≤ (2 * q - 1)⁻¹ := (one_le_inv₀ hd0).2 (by linarith)
  -- the argument of `b`
  set m : ℕ := min Jb ⌈(q * (2 * q - 1))⁻¹⌉₊ with hmdef
  have hceil1 : 1 ≤ ⌈(q * (2 * q - 1))⁻¹⌉₊ := Nat.succ_le_of_lt (Nat.ceil_pos.2 (inv_pos.2 hγ0))
  have hm1 : 1 ≤ m := le_min hJb1 hceil1
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmJ : (m : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast min_le_left _ _
  have hmC : (m : ℝ) ≤ (⌈(q * (2 * q - 1))⁻¹⌉₊ : ℝ) := by exact_mod_cast min_le_right _ _
  have hceil : (⌈(q * (2 * q - 1))⁻¹⌉₊ : ℝ) < (q * (2 * q - 1))⁻¹ + 1 :=
    Nat.ceil_lt_add_one (inv_pos.2 hγ0).le
  have hγinv : (q * (2 * q - 1))⁻¹ ≤ 2 * (2 * q - 1)⁻¹ := by
    have h := inv_anti₀ (by linarith : (0 : ℝ) < (2 * q - 1) / 2) hγlo
    rwa [inv_div, div_eq_mul_inv] at h
  have hm3 : (m : ℝ) ≤ 3 * min (2 * q - 1)⁻¹ (Real.log κ) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
    exact le_min (by linarith) (by linarith)
  -- `b` at the two arguments
  have hmin0 : (0 : ℝ) ≤ min (2 * q - 1)⁻¹ (Real.log κ) := le_min (by linarith) (by linarith)
  have hb : ballotFactor q (m : ℝ) ≤ 3 * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ)) :=
    le_trans (ballotFactor_le_ballotFactor hq0 hq1 (by linarith) hm3)
      (ballotFactor_mul_le hq0 hq1 hmin0 (by norm_num))
  have hb0 : (0 : ℝ) ≤ ballotFactor q (m : ℝ) := by
    unfold ballotFactor
    have hB : (0 : ℝ) ≤ 1 + (1 - q) * Real.sqrt (m : ℝ) := by
      have := mul_nonneg (show (0 : ℝ) ≤ 1 - q by linarith) (Real.sqrt_nonneg (m : ℝ))
      linarith
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hB _)
  -- the exponential
  have hexp : Real.exp ((Jb : ℝ) * (q * (2 * q - 1))) ≤ Real.exp 1 * κ ^ (q * (2 * q - 1)) := by
    rw [Real.rpow_def_of_pos hκ0, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_right hJbκ hγ0.le]
  calc Real.exp ((Jb : ℝ) * (q * (2 * q - 1))) * (m : ℝ)
        * (1 + (1 - q) * Real.sqrt (m : ℝ)) ^ (-q)
      = Real.exp ((Jb : ℝ) * (q * (2 * q - 1))) * ballotFactor q (m : ℝ) := by
        unfold ballotFactor
        ring
    _ ≤ (Real.exp 1 * κ ^ (q * (2 * q - 1)))
          * (3 * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ))) :=
        mul_le_mul hexp hb hb0 (mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg hκ0.le _))
    _ = 3 * Real.exp 1
          * (κ ^ (q * (2 * q - 1)) * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log κ))) := by ring

/-! ### The three ranges of the line -/

/-- The three ranges of `|t|`, as a partition of `ℝ`. -/
lemma integral_split_three {f : ℝ → ℝ} (hf : Integrable f) {w T : ℝ} (hwT : w ≤ T) :
    (∫ t : ℝ, f t)
      = (∫ t in Set.Icc (-w) w, f t) + (∫ t in {t : ℝ | w < |t| ∧ |t| ≤ T}, f t)
        + ∫ t in {t : ℝ | T < |t|}, f t := by
  have hAbs : Measurable fun t : ℝ => |t| := measurable_id.abs
  have hs2 : MeasurableSet {t : ℝ | w < |t| ∧ |t| ≤ T} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have h12 : Set.Icc (-w) w ∪ {t : ℝ | w < |t| ∧ |t| ≤ T} = Set.Icc (-T) T := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le]
    constructor
    · rintro (h | h)
      · linarith
      · exact h.2
    · intro h
      by_cases hle : |t| ≤ w
      · exact Or.inl hle
      · exact Or.inr ⟨not_le.1 hle, h⟩
  have hd12 : Disjoint (Set.Icc (-w) w) {t : ℝ | w < |t| ∧ |t| ≤ T} := by
    rw [Set.disjoint_left]
    rintro t ht ht'
    rw [Set.mem_Icc, ← abs_le] at ht
    exact absurd ht'.1 (not_lt.2 ht)
  have hcomp : Set.Icc (-T) T = {t : ℝ | T < |t|}ᶜ := by
    ext t
    simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, ← abs_le]
  rw [← setIntegral_union hd12 hs2 hf.integrableOn hf.integrableOn, h12, hcomp, add_comm,
    integral_add_compl (measurableSet_lt measurable_const hAbs) hf]

/-- `(a+b+c)^q ≤ a^q+b^q+c^q` for `0 ≤ q ≤ 1`. -/
lemma rpow_add_three_le {a b c q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : (a + b + c) ^ q ≤ a ^ q + b ^ q + c ^ q := by
  have h1 := Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc hq0 hq1
  have h2 := Real.rpow_add_le_add_rpow ha hb hq0 hq1
  linarith

/-- **A damped line integral from its three ranges.**  If `F(ω, t)` is jointly measurable and
bounded by `U` almost surely uniformly in `t`, then for `σ > 0`, `L > 0`, `0 ≤ q ≤ 1` and `w ≤ T`,
`E[(L⁻¹∫_ℝ |F|²/|σ+it|²)^q] ≤ B₁ + B₂ + B₃` whenever `B₁`, `B₂`, `B₃` bound the same moment over
`|t| ≤ w`, `w < |t| ≤ T` and `|t| > T`: the partition `RMF.integral_split_three` on every path,
integrable by the envelope, then subadditivity of `u ↦ u^q`, each piece being integrable by
`RMF.integrable_rpow_setIntegral_lineDiv_of_bound`. -/
theorem integral_rpow_lineDiv_le_of_three_ranges {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ → ℂ} {σ U L q w T B₁ B₂ B₃ : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hwT : w ≤ T) (hF : Measurable (Function.uncurry F))
    (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U)
    (hb1 : (∫ ω, (L⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) ≤ B₁)
    (hb2 : (∫ ω, (L⁻¹ * ∫ t in {t : ℝ | w < |t| ∧ |t| ≤ T},
        ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) ≤ B₂)
    (hb3 : (∫ ω, (L⁻¹ * ∫ t in {t : ℝ | T < |t|},
        ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) ≤ B₃) :
    (∫ ω, (L⁻¹ * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ B₁ + B₂ + B₃ := by
  have hpos : ∀ t : ℝ, 0 < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hpt : ∀ ω t, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := fun ω t => by
    rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
      Complex.normSq_add_mul_I, div_eq_mul_inv]
  have hρ := integrable_inv_sq_add_sq hσ.ne'
  have hL0 : (0 : ℝ) ≤ L⁻¹ := inv_nonneg.2 hL.le
  -- every path is integrable on the line
  have hline : ∀ᵐ ω ∂μ,
      Integrable fun t : ℝ => ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    filter_upwards [hU] with ω hω
    have hmeas : Measurable fun t : ℝ => ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      have h1 : Measurable fun t : ℝ => F ω t := hF.comp (measurable_const.prodMk measurable_id)
      have h2 : Measurable fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I :=
        (Complex.measurable_ofReal.mul_const Complex.I).const_add _
      exact (h1.div h2).norm.pow_const 2
    refine Integrable.mono' (hρ.const_mul (U ^ 2)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    change ‖‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ U ^ 2 * (σ ^ 2 + t ^ 2)⁻¹
    rw [Real.norm_of_nonneg (sq_nonneg _), hpt ω t]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hω t) 2)
      (inv_nonneg.2 (hpos t).le)
  have hAbs : Measurable fun t : ℝ => |t| := measurable_id.abs
  have hs1 : MeasurableSet (Set.Icc (-w) w) := measurableSet_Icc
  have hs2 : MeasurableSet {t : ℝ | w < |t| ∧ |t| ≤ T} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have hs3 : MeasurableSet {t : ℝ | T < |t|} := measurableSet_lt measurable_const hAbs
  -- the pointwise three-term bound
  have hpt3 : ∀ᵐ ω ∂μ,
      (L⁻¹ * ∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
        ≤ (L⁻¹ * ∫ t in Set.Icc (-w) w, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
          + (L⁻¹ * ∫ t in {t : ℝ | w < |t| ∧ |t| ≤ T},
              ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
          + (L⁻¹ * ∫ t in {t : ℝ | T < |t|},
              ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q := by
    filter_upwards [hline] with ω hω
    rw [integral_split_three hω hwT, mul_add, mul_add]
    exact rpow_add_three_le (mul_nonneg hL0 (setIntegral_nonneg hs1 fun t _ => sq_nonneg _))
      (mul_nonneg hL0 (setIntegral_nonneg hs2 fun t _ => sq_nonneg _))
      (mul_nonneg hL0 (setIntegral_nonneg hs3 fun t _ => sq_nonneg _)) hq0 hq1
  have hI1 := integrable_rpow_setIntegral_lineDiv_of_bound (S := Set.Icc (-w) w) (q := q)
    hσ hL hq0 hF hU
  have hI2 := integrable_rpow_setIntegral_lineDiv_of_bound
    (S := {t : ℝ | w < |t| ∧ |t| ≤ T}) (q := q) hσ hL hq0 hF hU
  have hI3 := integrable_rpow_setIntegral_lineDiv_of_bound (S := {t : ℝ | T < |t|}) (q := q)
    hσ hL hq0 hF hU
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)) _)
    ((hI1.add hI2).add hI3) hpt3) ?_
  simp only [Pi.add_apply]
  exact integral_add_le (hI1.add hI2) hI3 (integral_add_le hI1 hI2 hb1 hb2) hb3

/-! ### The crude bound on the whole line -/

/-- **A band's damped line integral on the whole line, crudely.**  For `0 ≤ q ≤ 1`, `2 ≤ y ≤ z`,
`0 < c < ½` with `2c·log z ≤ 1`,
`E[((log z)⁻¹∫_ℝ‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q] ≤ (πe^{45}/(c·log y))^q`: the whole line of
`RMF.integral_rpow_setIntegral_lineDiv_primesIco_le`, where the weight integrates to `π/c`.  At
`c = 1/(2 log z)` this is `(2πe^{45}κ)^q`, which bounds the bands too short or too low for the
three ranges. -/
theorem integral_rpow_lineDiv_primesIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {y z : ℕ}
    (hy : 2 ≤ y) (hyz : y ≤ z) (hc : 0 < c) (hc2 : c < 1 / 2)
    (hcz : 2 * c * Real.log z ≤ 1) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (Real.pi * Real.exp 45 / (c * Real.log y)) ^ q := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have h := integral_rpow_setIntegral_lineDiv_primesIco_le hX hq0 hq1 hy hyz hc hc2 hcz Set.univ
  simp only [Measure.restrict_univ] at h
  rw [integral_inv_sq_add_sq hc] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  calc (Real.log z)⁻¹ * (Real.pi / c * (Real.exp 45 * (Real.log z / Real.log y)))
      = (Real.log z * (Real.log z)⁻¹) * (Real.pi * Real.exp 45 / (c * Real.log y)) := by
        ring
    _ = Real.pi * Real.exp 45 / (c * Real.log y) := by rw [mul_inv_cancel₀ hlogz.ne', one_mul]

end RMF
