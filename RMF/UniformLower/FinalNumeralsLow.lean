/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.PerScaleShort
import RMF.UniformLower.WindowClassical
import RMF.UniformLower.FinalNumerals

/-!
# The low range below `½`: the regimes' constants

For `67.17 ≤ Λ = log log x ≤ 2100` and
`0 < q < ½`, the constants the regime lemmas reach against the target `10⁻¹⁰·m·Λ^{-q/2}`,
`m = min{Λ, (1-2q)⁻¹}`, with `u = qΛ`, `G = e^{-0.592}/2` and the tilt `V′ = Λ + 24/q = (u + 24)/q`:

* **F**, the floor `2^{-(1-2q)}3^{-(1-q)}(0.49/log x)^q` times `(1-2q)Λ^{q/2}`: `RMF.PhiFLow`;
* **B1**, the one scale `k = 21` on a tube of `r ≥ 35` blocks: `RMF.PhiB1Low = RMF.mainB1Low -
  (1-2q)cJ(q)e^{-24} - RMF.errBLow`, `mainB1Low = (1-2q)cRed(q)2^{2q-1}(G/(2V′))^qΓ(q, 1, r)·
  e^{-q(1-2q)(21 + 0.7866 + 9.003e^{-21})}` (`Γ = RMF.perScaleConstShort`) and
  `errBLow = (1-2q)cErrD(q)e^{-u}Λ^{q/2}`;
* **B2**, `9/20 ≤ q < ½`: `RMF.PhiB2Low`, the scales counted as `m/2`, each at the rung `35`
  (`RMF.perScaleLow2Short`: `c₃ = 0.17784`, `P₁ = 0.28668`, `Q = 24542`).

Their lower bounds on cells of `(q, u)` in log space, every factor at its worse corner
(`RMF.cellFLow`, `RMF.cellLogCoreLow`, `RMF.cellLogMainLow`, `RMF.cellSubLow`, `RMF.cellErrLow`),
the damping level's lower bound `RMF.cellRungLow`, the rungs' numerals (`RMF.lowRung_35`, …), and
the glue from certificates to the cell property `RMF.LowCellSpec` (`RMF.lowCellSpec_of_F`,
`RMF.lowCellSpec_of_B1`) and to `PhiB2Low ≥ 10⁻¹⁰` (`RMF.PhiB2Low_ge_of_cert`).  The certificates
are in `RMF/UniformLower/FinalCellsLow/`.
-/

namespace RMF

/-! ### The constants -/

/-- **B1's main term in the low range**: `(1-2q)cRed(q)2^{2q-1}(G/(2V′))^qΓ(q, 1, r)·
e^{-q(1-2q)(21 + 0.7866 + 9.003e^{-21})}`, `V′ = (u + 24)/q`, `G = e^{-0.592}/2`. -/
noncomputable def mainB1Low (q u : ℝ) (r : ℕ) : ℝ :=
  (1 - 2 * q) * cRed q * (2 : ℝ) ^ (2 * q - 1)
    * (Real.exp (-0.592) / 2 / (2 * ((u + 24) / q))) ^ q * perScaleConstShort q 1 r
    * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21))

/-- **The error term in the low range**: `(1-2q)cErrD(q)e^{-qΛ}Λ^{q/2}`. -/
noncomputable def errBLow (q Λ : ℝ) : ℝ :=
  (1 - 2 * q) * cErrD q * Real.exp (-(q * Λ)) * Λ ^ (q / 2)

/-- **B1's constant in the low range**: `mainB1Low - (1-2q)cJ(q)e^{-24} - errBLow` at `u = qΛ`. -/
noncomputable def PhiB1Low (q Λ : ℝ) (r : ℕ) : ℝ :=
  mainB1Low q (q * Λ) r - (1 - 2 * q) * cJ q * Real.exp (-24) - errBLow q Λ

/-- **F's constant in the low range**: `(1-2q)2^{-(1-2q)}3^{-(1-q)}0.49^qe^{-qΛ}Λ^{q/2}`. -/
noncomputable def PhiFLow (q Λ : ℝ) : ℝ :=
  (1 - 2 * q) * ((2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / 100 : ℝ) ^ q)
    * Real.exp (-(q * Λ)) * Λ ^ (q / 2)

/-- **The per-scale constant at the rung `35`**: `RMF.perScaleConstShort` with `c₃ = 0.17784`,
`P₁ = 0.28668` and `Q = 24542`. -/
noncomputable def perScaleLow2Short (q : ℝ) : ℝ :=
  (0.17784 : ℝ) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
    * ((1 - Real.exp (-100)) * 0.28668) ^ (2 - q) * (24542 : ℝ) ^ (-(1 - q))

/-- **B2's main term in the low range**:
`cRed(q)2^{2q-1}(G/(2V′))^q(1/2)perScaleLow2Short(q)e^{-20.7867q(1-2q) - q}`, `V′ = (u + 24)/q`. -/
noncomputable def mainB2Low (q u : ℝ) : ℝ :=
  cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * ((u + 24) / q))) ^ q
    * (1 / 2) * perScaleLow2Short q * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q)

/-- **B2's constant in the low range**: `mainB2Low - (1-2q)cJ(q)e^{-24} - errBLow` at `u = qΛ`. -/
noncomputable def PhiB2Low (q Λ : ℝ) : ℝ :=
  mainB2Low q (q * Λ) - (1 - 2 * q) * cJ q * Real.exp (-24) - errBLow q Λ

/-! ### The cell bounds -/

/-- **F on a cell** `q ∈ [a, b]`, `qΛ ≤ u_F`, `Λ ≥ 67.17`: `PhiFLow` with every factor at its
worse end. -/
noncomputable def cellFLow (a b uF : ℝ) : ℝ :=
  (1 - 2 * b) * Real.exp (-((1 - 2 * a) * Real.log 2) - (1 - a) * Real.log 3
    + b * Real.log (49 / 100) - uF + a / 2 * Real.log 67.17)

/-- **The core's log on a cell** `q ∈ [a, b] ⊆ (0, ½]`, `u ≤ u_b`: the log of
`cRed(q)2^{2q-1}(Gq/(4(u + 24)))^qΓ` with `c₃ ≥ c`, `q log q ≥ ℓ`, `(1 - e^{-100})P₁ ≥ p` and
HP2's constant at most `Q`, every term at its worse end, `π ≤ 3.1416`. -/
noncomputable def cellLogCoreLow (a b c ℓ ub p Q : ℝ) : ℝ :=
  -((1 - a) * Real.log 3) - (1 - 2 * a) * Real.log 2 - b * Real.log (16 * 3.1416)
    + (2 * a - 1) * Real.log 2 + b * (-0.592 - 2 * Real.log 2 - Real.log (ub + 24)) + ℓ
    + (2 - a) * Real.log c - (1 - a) * (2 * (1 - a) + 0.50001) - b * Real.log 2
    + (2 - a) * Real.log p - (1 - a) * Real.log Q

/-- **B1's main term on a cell**: `(1 - 2b)`, the core, and `N ≥ e^{-21.7867β}`, `β ≥ q(1-2q)`. -/
noncomputable def cellLogMainLow (a b c β ℓ ub p Q : ℝ) : ℝ :=
  Real.log (1 - 2 * b) + cellLogCoreLow a b c ℓ ub p Q - β * 21.7867

/-- **The subtracted term on a cell** `q ∈ [a, b]`: `(1-2q)cJ(q)e^{-24}` at its worse ends,
`π ≥ 3.14159`. -/
noncomputable def cellSubLow (a b : ℝ) : ℝ :=
  (1 - 2 * a) * Real.exp (-((1 - b) * Real.log 3) - (1 - 2 * b) * Real.log 2
    - a * Real.log (8 * 3.14159) - 24)

/-- **The error term on a cell** `q ∈ [a, b]`, `qΛ ≥ u_a`, `Λ ≤ Λ_hi`: `errBLow` at its worse
ends. -/
noncomputable def cellErrLow (a b ua Λhi : ℝ) : ℝ :=
  (1 - 2 * a) * Real.exp (-((1 - b) * Real.log 3) - (1 - 2 * b) * Real.log 2 + b * Real.log 2
    - ua + b / 2 * Real.log Λhi)

/-- **The damping level's log on a cell** `q ≥ a`, `Λ ≥ Λ_lo`: `Λ - log(400(Λ + 24/q))` at its
worse corner. -/
noncomputable def cellRungLow (a Λlo : ℝ) : ℝ := Λlo - Real.log (400 * (Λlo + 24 / a))

/-- **The low range's cell property**: `F` certified, or `B1` at a rung `r₀ ≥ 35` with
`r₀ + 21 ≤ Λ - log(400(Λ + 24/q))` (the damping level's log). -/
def LowCellSpec (q Λ : ℝ) : Prop :=
  1 / 10 ^ 10 ≤ PhiFLow q Λ
    ∨ ∃ r₀ : ℕ, 35 ≤ r₀ ∧ (r₀ : ℝ) + 21 ≤ Λ - Real.log (400 * (Λ + 24 / q))
      ∧ 1 / 10 ^ 10 ≤ PhiB1Low q Λ r₀

/-! ### F on a cell -/

/-- **F on a cell**: `cellFLow a b u_F ≤ PhiFLow(q, Λ)` for `0 ≤ a ≤ q ≤ b ≤ ½`, `qΛ ≤ u_F` and
`Λ ≥ 67.17`. -/
lemma cellFLow_le_PhiFLow {a b uF q Λ : ℝ} (ha0 : 0 ≤ a) (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 1 / 2) (huF : q * Λ ≤ uF) (hΛ : 67.17 ≤ Λ) : cellFLow a b uF ≤ PhiFLow q Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have hX : Real.exp (-((1 - 2 * a) * Real.log 2) - (1 - a) * Real.log 3
      + b * Real.log (49 / 100) - uF + a / 2 * Real.log 67.17)
      ≤ (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / 100 : ℝ) ^ q
        * Real.exp (-(q * Λ)) * Λ ^ (q / 2) := by
    simp only [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 49 / 100), Real.rpow_def_of_pos hΛ0,
      ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have l49 : Real.log (49 / 100) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    have l67 : 0 ≤ Real.log 67.17 := Real.log_nonneg (by norm_num)
    have lΛ : Real.log 67.17 ≤ Real.log Λ := Real.log_le_log (by norm_num) hΛ
    have f2 := mul_le_mul_of_nonneg_right haq l2
    have f3 := mul_le_mul_of_nonneg_right haq l3
    have f49 := mul_le_mul_of_nonpos_right hqb l49
    have fΛ := mul_le_mul haq lΛ l67 (by linarith)
    linarith
  have e : PhiFLow q Λ = (1 - 2 * q) * ((2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q))
      * (49 / 100 : ℝ) ^ q * Real.exp (-(q * Λ)) * Λ ^ (q / 2)) := by
    unfold PhiFLow
    ring
  rw [e]
  exact mul_le_mul (by linarith) hX (Real.exp_pos _).le (by linarith)

/-- **F from its certificate**: `PhiFLow(q, Λ) ≥ 10⁻¹⁰` from `10⁻¹⁰ ≤ cellFLow a b u_F` on the
cell. -/
theorem PhiFLow_ge_of_cell {a b uF q Λ : ℝ} (ha0 : 0 ≤ a) (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 1 / 2) (huF : q * Λ ≤ uF) (hΛ : 67.17 ≤ Λ) (hcert : 1 / 10 ^ 10 ≤ cellFLow a b uF) :
    1 / 10 ^ 10 ≤ PhiFLow q Λ :=
  hcert.trans (cellFLow_le_PhiFLow ha0 haq hqb hb huF hΛ)

/-! ### The main terms on a cell -/

/-- **The core on a cell** `q ∈ [a, b] ⊆ (0, ½]`: for `0 ≤ u ≤ u_b`, `0 < c ≤ min(1, C)`,
`ℓ ≤ q log q`, `0 < p ≤ min(1, (1 - e^{-100})P)` and `1 ≤ Q₀ ≤ Q`,
`e^{cellLogCoreLow a b c ℓ u_b p Q} ≤ cRed(q)2^{2q-1}(G/(2V′))^q·
C^{2-q}C₂^{-(1-q)}2^{-q}((1 - e^{-100})P)^{2-q}Q₀^{-(1-q)}`, `V′ = (u + 24)/q`. -/
lemma exp_cellLogCoreLow_le {a b c C ℓ ub p P Q Q₀ u q : ℝ} (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 1 / 2) (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1) (hcC : c ≤ C)
    (hℓ : ℓ ≤ q * Real.log q) (hu0 : 0 ≤ u) (hub : u ≤ ub) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpP : p ≤ (1 - Real.exp (-100)) * P) (hQ₀ : 1 ≤ Q₀) (hQ : Q₀ ≤ Q) :
    Real.exp (cellLogCoreLow a b c ℓ ub p Q)
      ≤ cRed q * (2 : ℝ) ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / (2 * ((u + 24) / q))) ^ q
        * (C ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
          * ((1 - Real.exp (-100)) * P) ^ (2 - q) * Q₀ ^ (-(1 - q))) := by
  have hC0 : 0 < C := lt_of_lt_of_le hc0 hcC
  have hP0 : 0 < (1 - Real.exp (-100)) * P := lt_of_lt_of_le hp0 hpP
  have hQ0 : (0 : ℝ) < Q₀ := by linarith
  have hu24 : 0 < u + 24 := by linarith
  have hq' : q ≠ 0 := hq0.ne'
  have hu24' : u + 24 ≠ 0 := hu24.ne'
  have hπ0 : (0 : ℝ) < 16 * Real.pi := by positivity
  have hG : Real.exp (-0.592) / 2 / (2 * ((u + 24) / q))
      = Real.exp (-0.592) * q / (4 * (u + 24)) := by
    field_simp
    ring
  have hG0 : 0 < Real.exp (-0.592) * q / (4 * (u + 24)) := by positivity
  have hGlog : Real.log (Real.exp (-0.592) * q / (4 * (u + 24)))
      = -0.592 - 2 * Real.log 2 - Real.log (u + 24) + Real.log q := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hq',
      Real.log_exp, Real.log_mul (by norm_num) hu24', show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  unfold cRed
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q), hG, ← Real.exp_mul]
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
    Real.rpow_def_of_pos hπ0, Real.rpow_def_of_pos hG0, Real.rpow_def_of_pos hC0,
    Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos hQ0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [hGlog]
  unfold cellLogCoreLow
  have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have lQ : 0 ≤ Real.log Q₀ := Real.log_nonneg hQ₀
  have lQQ : Real.log Q₀ ≤ Real.log Q := Real.log_le_log hQ0 hQ
  have lπ0 : 0 ≤ Real.log (16 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have lπ : Real.log (16 * Real.pi) ≤ Real.log (16 * 3.1416) :=
    Real.log_le_log hπ0 (by linarith [Real.pi_lt_d4])
  have lc : Real.log c ≤ Real.log C := Real.log_le_log hc0 hcC
  have lc0 : Real.log c ≤ 0 := Real.log_nonpos hc0.le hc1
  have lp : Real.log p ≤ Real.log ((1 - Real.exp (-100)) * P) := Real.log_le_log hp0 hpP
  have lp0 : Real.log p ≤ 0 := Real.log_nonpos hp0.le hp1
  have lu : Real.log (u + 24) ≤ Real.log (ub + 24) := Real.log_le_log hu24 (by linarith)
  have lub : 0 ≤ Real.log (ub + 24) := Real.log_nonneg (by linarith)
  have f3 := mul_le_mul_of_nonneg_right haq l3
  have f2a := mul_le_mul_of_nonneg_right haq l2
  have f2b := mul_le_mul_of_nonneg_right hqb l2
  have fπa := mul_le_mul_of_nonneg_right hqb lπ0
  have fπb := mul_le_mul_of_nonneg_left lπ (by linarith : (0 : ℝ) ≤ b)
  have fu := mul_le_mul_of_nonneg_left lu hq0.le
  have fG := mul_le_mul_of_nonpos_right hqb
    (by linarith : -0.592 - 2 * Real.log 2 - Real.log (ub + 24) ≤ 0)
  have fC := mul_le_mul_of_nonneg_left lc (by linarith : (0 : ℝ) ≤ 2 - q)
  have fc := mul_le_mul_of_nonpos_right haq lc0
  have fP := mul_le_mul_of_nonneg_left lp (by linarith : (0 : ℝ) ≤ 2 - q)
  have fP0 := mul_le_mul_of_nonpos_right haq lp0
  have fQ := mul_le_mul_of_nonneg_left lQQ (by linarith : (0 : ℝ) ≤ 1 - q)
  have fQ0 := mul_le_mul_of_nonneg_right haq (lQ.trans lQQ)
  have fq : 0 ≤ (q - a) * (4.50001 - 2 * (q + a)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- `RMF.hp1P1Short r ≤ 1`. -/
lemma hp1P1Short_le_one (r : ℕ) : hp1P1Short r ≤ 1 := by
  unfold hp1P1Short hp1RungShort
  split_ifs <;> norm_num [hp1P1ShortRung]

/-- **B1's main term on a cell**: `e^{cellLogMainLow a b c β ℓ u_b p Q} ≤ mainB1Low(q, u, r)` for
`q ∈ [a, b]`, `b ≤ 9/20`, `0 < c ≤ min(1, c3FloorK q 1)`, `q(1-2q) ≤ β`, `ℓ ≤ q log q`,
`0 ≤ u ≤ u_b`, `0 < p ≤ (1 - e^{-100})hp1P1Short r` and `hp2QShort r ≤ Q`
(`21.7866 + 9.003e^{-21} ≤ 21.7867`). -/
lemma exp_cellLogMainLow_le_mainB1Low {a b c β ℓ ub p Q q u : ℝ} {r : ℕ} (haq : a ≤ q)
    (hqb : q ≤ b) (hb : b ≤ 9 / 20) (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : c ≤ c3FloorK q 1) (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q) (hu0 : 0 ≤ u)
    (hub : u ≤ ub) (hp0 : 0 < p)
    (hr : p ≤ (1 - Real.exp (-100)) * hp1P1Short r ∧ hp2QShort r ≤ Q) :
    Real.exp (cellLogMainLow a b c β ℓ ub p Q) ≤ mainB1Low q u r := by
  have hP1 : (1 - Real.exp (-100)) * hp1P1Short r ≤ 1 :=
    (mul_le_of_le_one_left (hp1P1Short_nonneg r) (by linarith [Real.exp_pos (-100)])).trans
      (hp1P1Short_le_one r)
  have hcore := exp_cellLogCoreLow_le (C := c3FloorK q 1) (P := hp1P1Short r)
    (Q₀ := hp2QShort r) haq hqb (by linarith) hq0 hc0 hc1 hc hℓ hu0 hub hp0 (hr.1.trans hP1) hr.1
    (by linarith [hp2QShort_ge r]) hr.2
  have hb2 : 0 < 1 - 2 * b := by linarith
  have he21 : (90030 : ℝ) ≤ Real.exp 21 := by interval_decide (trust := kernel)
  have hs : 9.003 / Real.exp 21 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hβq0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0.le (by linarith)
  have hN : Real.exp (-(β * 21.7867))
      ≤ Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 := mul_le_mul_of_nonneg_left hs hβq0
    linarith
  have e1 : Real.exp (cellLogMainLow a b c β ℓ ub p Q)
      = (1 - 2 * b) * Real.exp (cellLogCoreLow a b c ℓ ub p Q) * Real.exp (-(β * 21.7867)) := by
    rw [cellLogMainLow, show Real.log (1 - 2 * b) + cellLogCoreLow a b c ℓ ub p Q - β * 21.7867
        = Real.log (1 - 2 * b) + cellLogCoreLow a b c ℓ ub p Q + -(β * 21.7867) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hb2]
  have e2 : mainB1Low q u r = (1 - 2 * q) * (cRed q * (2 : ℝ) ^ (2 * q - 1)
      * (Real.exp (-0.592) / 2 / (2 * ((u + 24) / q))) ^ q
      * (c3FloorK q 1 ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * hp1P1Short r) ^ (2 - q) * hp2QShort r ^ (-(1 - q))))
      * Real.exp (-(q * (1 - 2 * q)) * (21 + 0.7866 + 9.003 / Real.exp 21)) := by
    rw [mainB1Low, perScaleConstShort]
    ring
  rw [e1, e2]
  have hX0 := le_trans (Real.exp_pos _).le hcore
  exact mul_le_mul (mul_le_mul (by linarith) hcore (Real.exp_pos _).le (by linarith)) hN
    (Real.exp_pos _).le (mul_nonneg (by linarith) hX0)

/-! ### The subtracted and error terms on a cell -/

/-- **The subtracted term on a cell**: `(1-2q)cJ(q)e^{-24} ≤ cellSubLow a b` for
`0 ≤ a ≤ q ≤ b ≤ ½` (`π ≥ 3.14159`). -/
lemma sub_le_cellSubLow {a b q : ℝ} (ha0 : 0 ≤ a) (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2) :
    (1 - 2 * q) * cJ q * Real.exp (-24) ≤ cellSubLow a b := by
  have hπ0 : (0 : ℝ) < 8 * Real.pi := by positivity
  have hJ : cJ q * Real.exp (-24) ≤ Real.exp (-((1 - b) * Real.log 3) - (1 - 2 * b) * Real.log 2
      - a * Real.log (8 * 3.14159) - 24) := by
    unfold cJ
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q)]
    simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
      Real.rpow_def_of_pos hπ0, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have lπ : Real.log (8 * 3.14159) ≤ Real.log (8 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_d6])
    have lπ0 : 0 ≤ Real.log (8 * 3.14159) := Real.log_nonneg (by norm_num)
    have f3 := mul_le_mul_of_nonneg_right hqb l3
    have f2 := mul_le_mul_of_nonneg_right hqb l2
    have fπ := mul_le_mul haq lπ lπ0 (by linarith)
    linarith
  unfold cellSubLow
  calc (1 - 2 * q) * cJ q * Real.exp (-24) = (1 - 2 * q) * (cJ q * Real.exp (-24)) := by ring
    _ ≤ _ := mul_le_mul (by linarith) hJ (mul_nonneg (cJ_pos q).le (Real.exp_pos _).le)
      (by linarith)

/-- **The error term on a cell**: `errBLow(q, Λ) ≤ cellErrLow a b u_a Λ_hi` for
`0 ≤ a ≤ q ≤ b ≤ ½`, `qΛ ≥ u_a` and `1 ≤ Λ ≤ Λ_hi` (`cErrD` is increasing in `q`). -/
lemma errBLow_le_cellErrLow {a b ua Λhi q Λ : ℝ} (ha0 : 0 ≤ a) (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 1 / 2) (hua : ua ≤ q * Λ) (hΛ1 : 1 ≤ Λ) (hΛhi : Λ ≤ Λhi) :
    errBLow q Λ ≤ cellErrLow a b ua Λhi := by
  have hΛ0 : 0 < Λ := by linarith
  have hE : cErrD q * Real.exp (-(q * Λ)) * Λ ^ (q / 2)
      ≤ Real.exp (-((1 - b) * Real.log 3) - (1 - 2 * b) * Real.log 2 + b * Real.log 2
        - ua + b / 2 * Real.log Λhi) := by
    unfold cErrD
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q)]
    simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos two_pos,
      Real.rpow_def_of_pos hΛ0, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have lΛ : Real.log Λ ≤ Real.log Λhi := Real.log_le_log hΛ0 hΛhi
    have lΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
    have f3 := mul_le_mul_of_nonneg_right hqb l3
    have f2 := mul_le_mul_of_nonneg_right hqb l2
    have fΛ := mul_le_mul hqb lΛ lΛ0 (by linarith)
    linarith
  unfold errBLow cellErrLow
  calc (1 - 2 * q) * cErrD q * Real.exp (-(q * Λ)) * Λ ^ (q / 2)
      = (1 - 2 * q) * (cErrD q * Real.exp (-(q * Λ)) * Λ ^ (q / 2)) := by ring
    _ ≤ _ := mul_le_mul (by linarith) hE
      (mul_nonneg (mul_nonneg (cErrD_pos q).le (Real.exp_pos _).le) (Real.rpow_nonneg hΛ0.le _))
      (by linarith)

/-! ### B1 on a cell -/

/-- **B1 on a cell**: `PhiB1Low(q, Λ, r) ≥ 10⁻¹⁰` for `q ∈ [a, b]`, `0 ≤ a`, `b ≤ 9/20`,
`u_a ≤ qΛ ≤ u_b`, `1 ≤ Λ ≤ Λ_hi`, from `lam ≤ cellLogMainLow a b c β ℓ u_b p Q` and
`10⁻¹⁰ + cellSubLow a b + cellErrLow a b u_a Λ_hi ≤ e^{lam}`. -/
theorem PhiB1Low_ge_of_cell {a b c β ℓ ua ub Λhi p Q lam q Λ : ℝ} {r : ℕ} (ha0 : 0 ≤ a)
    (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 9 / 20) (hq0 : 0 < q) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : c ≤ c3FloorK q 1) (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q)
    (hua : ua ≤ q * Λ) (hub : q * Λ ≤ ub) (hΛ1 : 1 ≤ Λ) (hΛhi : Λ ≤ Λhi) (hp0 : 0 < p)
    (hr : p ≤ (1 - Real.exp (-100)) * hp1P1Short r ∧ hp2QShort r ≤ Q)
    (hlam : lam ≤ cellLogMainLow a b c β ℓ ub p Q)
    (hcert : 1 / 10 ^ 10 + cellSubLow a b + cellErrLow a b ua Λhi ≤ Real.exp lam) :
    1 / 10 ^ 10 ≤ PhiB1Low q Λ r := by
  have hmain := exp_cellLogMainLow_le_mainB1Low haq hqb hb hq0 hc0 hc1 hc hβ hℓ
    (mul_nonneg hq0.le (by linarith)) hub hp0 hr
  have hlam' := Real.exp_le_exp.2 hlam
  have hsub := sub_le_cellSubLow ha0 haq hqb (by linarith)
  have herr := errBLow_le_cellErrLow ha0 haq hqb (by linarith) hua hΛ1 hΛhi
  unfold PhiB1Low
  linarith

/-- **The damping level on a cell**: `cellRungLow a Λ_lo ≤ Λ - log(400(Λ + 24/q))` for
`0 < a ≤ q` and `1 ≤ Λ_lo ≤ Λ` (increasing in `Λ` and in `q`; `log y ≤ y - 1`). -/
theorem rungLow_of_cell {a Λlo q Λ : ℝ} (ha0 : 0 < a) (haq : a ≤ q) (hlo : Λlo ≤ Λ)
    (hlo1 : 1 ≤ Λlo) : cellRungLow a Λlo ≤ Λ - Real.log (400 * (Λ + 24 / q)) := by
  have hq0 : 0 < q := lt_of_lt_of_le ha0 haq
  have h24 : 24 / q ≤ 24 / a := div_le_div_of_nonneg_left (by norm_num) ha0 haq
  have h24a : 0 < 24 / a := by positivity
  have h24q : 0 < 24 / q := by positivity
  have hA0 : 0 < Λlo + 24 / a := by linarith
  have hB0 : 0 < Λ + 24 / q := by linarith
  have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ Λlo + 24 / a - 1) (by linarith : 0 ≤ Λ - Λlo)
  have hd : (Λ + 24 / q) / (Λlo + 24 / a) ≤ 1 + (Λ - Λlo) := by
    rw [div_le_iff₀ hA0]
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB0 hA0)
  rw [Real.log_div hB0.ne' hA0.ne'] at hlog
  unfold cellRungLow
  rw [Real.log_mul (by norm_num) hA0.ne', Real.log_mul (by norm_num) hB0.ne']
  linarith

/-! ### The rungs -/

/-- `e^{-100} ≤ 10⁻⁶`. -/
lemma exp_neg_hundred_le_micro : Real.exp (-100) ≤ 1 / 10 ^ 6 := by
  interval_decide (trust := kernel)

/-- **A rung's numerals**: `p ≤ (1 - e^{-100})hp1P1Short r` and `hp2QShort r ≤ Q` from
`hp1P1Short r = P ≥ 0`, `p ≤ (1 - 10⁻⁶)P` and `hp2QShort r = Q` (`e^{-100} ≤ 10⁻⁶`). -/
lemma lowRung_of {r : ℕ} {p P Q : ℝ} (hP : hp1P1Short r = P) (hQ : hp2QShort r = Q)
    (hP0 : 0 ≤ P) (hp : p ≤ (1 - 1 / 10 ^ 6) * P) :
    p ≤ (1 - Real.exp (-100)) * hp1P1Short r ∧ hp2QShort r ≤ Q := by
  refine ⟨?_, hQ.le⟩
  rw [hP]
  have h := mul_le_mul_of_nonneg_right
    (by linarith [exp_neg_hundred_le_micro] : 1 - 1 / 10 ^ 6 ≤ 1 - Real.exp (-100)) hP0
  linarith

/-- The rung `35`: `P₁ = 0.28668`, `Q = 24542`. -/
lemma lowRung_35 :
    (0.28667 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 35 ∧ hp2QShort 35 ≤ 24542 :=
  lowRung_of (P := 0.28668) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_35 (by norm_num))) (by norm_num)
    (by norm_num)

/-- The rung `42`: `P₁ = 0.28668`, `Q = 22446`. -/
lemma lowRung_42 :
    (0.28667 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 42 ∧ hp2QShort 42 ≤ 22446 :=
  lowRung_of (P := 0.28668) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_42 (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)

/-- The rung `50`: `P₁ = 0.30092`, `Q = 20695`. -/
lemma lowRung_50 :
    (0.30091 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 50 ∧ hp2QShort 50 ≤ 20695 :=
  lowRung_of (P := 0.30092) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_50 (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)

/-- The rung `60`: `P₁ = 0.30092`, `Q = 19078`. -/
lemma lowRung_60 :
    (0.30091 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 60 ∧ hp2QShort 60 ≤ 19078 :=
  lowRung_of (P := 0.30092) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_60 (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)

/-- The rung `72`: `P₁ = 0.31128`, `Q = 17661`. -/
lemma lowRung_72 :
    (0.31127 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 72 ∧ hp2QShort 72 ≤ 17661 :=
  lowRung_of (P := 0.31128) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_72 (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)

/-- The rung `90`: `P₁ = 0.31128`, `Q = 16120`. -/
lemma lowRung_90 :
    (0.31127 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 90 ∧ hp2QShort 90 ≤ 16120 :=
  lowRung_of (P := 0.31128) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_90 (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)

/-- The rung `115`: `P₁ = 0.32023`, `Q = 14639`. -/
lemma lowRung_115 :
    (0.32022 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 115 ∧ hp2QShort 115 ≤ 14639 :=
  lowRung_of (P := 0.32023) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_115 (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)

/-- The rung `160`: `P₁ = 0.32449`, `Q = 12959`. -/
lemma lowRung_160 :
    (0.32448 : ℝ) ≤ (1 - Real.exp (-100)) * hp1P1Short 160 ∧ hp2QShort 160 ≤ 12959 :=
  lowRung_of (P := 0.32449) (by norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung])
    ((hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_160 (by norm_num))) (by norm_num)
    (by norm_num)

/-! ### From the certificates to the cell property -/

/-- `u_a ≤ qΛ` on a cell from `q ≥ a ≥ 0`, `Λ ≥ 67.17` and `u_a ≤ 67.17a`. -/
lemma le_mul_of_lowCell {a ua q Λ : ℝ} (ha0 : 0 ≤ a) (haq : a ≤ q) (hΛ : 67.17 ≤ Λ)
    (h : ua ≤ a * 67.17) : ua ≤ q * Λ :=
  h.trans (mul_le_mul haq hΛ (by norm_num) (ha0.trans haq))

/-- `qΛ ≤ u_b` on a cell from `q ≤ b`, `0 ≤ Λ ≤ 2100` and `2100b ≤ u_b`. -/
lemma mul_le_of_lowCell {b ub q Λ : ℝ} (hqb : q ≤ b) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ ≤ 2100)
    (hb0 : 0 ≤ b) (h : b * 2100 ≤ ub) : q * Λ ≤ ub :=
  (mul_le_mul hqb hΛ1 hΛ0 hb0).trans h

/-- `Λ ≥ u_a/b` on a cell from `u_a ≤ qΛ`, `q ≤ b` and `Λ ≥ 0`. -/
lemma div_le_of_lowCell {b ua q Λ : ℝ} (hb0 : 0 < b) (hqb : q ≤ b) (hΛ0 : 0 ≤ Λ)
    (hua : ua ≤ q * Λ) : ua / b ≤ Λ := by
  rw [div_le_iff₀ hb0]
  have := mul_le_mul_of_nonneg_right hqb hΛ0
  linarith

/-- `Λ ≤ u_b/a` on a cell from `qΛ ≤ u_b`, `q ≥ a > 0` and `Λ ≥ 0`. -/
lemma le_div_of_lowCell {a ub q Λ : ℝ} (ha0 : 0 < a) (haq : a ≤ q) (hΛ0 : 0 ≤ Λ)
    (hub : q * Λ ≤ ub) : Λ ≤ ub / a := by
  rw [le_div_iff₀ ha0]
  have := mul_le_mul_of_nonneg_right haq hΛ0
  linarith

/-- **An F cell**: `RMF.LowCellSpec q Λ` from `10⁻¹⁰ ≤ cellFLow a b u_F`, `qΛ ≤ u_F`. -/
theorem lowCellSpec_of_F {a b uF q Λ : ℝ} (ha0 : 0 ≤ a) (haq : a ≤ q) (hqb : q ≤ b)
    (hb : b ≤ 1 / 2) (huF : q * Λ ≤ uF) (hΛ : 67.17 ≤ Λ) (hcert : 1 / 10 ^ 10 ≤ cellFLow a b uF) :
    LowCellSpec q Λ :=
  Or.inl (PhiFLow_ge_of_cell ha0 haq hqb hb huF hΛ hcert)

/-- **A B1 cell**: `RMF.LowCellSpec q Λ` for `q ∈ [a, b]`, `0 < a`, `b ≤ 9/20`,
`u_a ≤ qΛ ≤ u_b` and `1 ≤ Λ_lo ≤ Λ ≤ Λ_hi`, from the rung's numerals at `r₀ ≥ 35`, the rung's
certificate `r₀ + 21 ≤ cellRungLow a Λ_lo`, and B1's two certificates. -/
theorem lowCellSpec_of_B1 {a b c β ℓ ua ub Λlo Λhi p Q lam q Λ : ℝ} {r₀ : ℕ} (ha0 : 0 < a)
    (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 9 / 20) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : c ≤ c3FloorK q 1) (hβ : q * (1 - 2 * q) ≤ β) (hℓ : ℓ ≤ q * Real.log q)
    (hua : ua ≤ q * Λ) (hub : q * Λ ≤ ub) (hlo : Λlo ≤ Λ) (hlo1 : 1 ≤ Λlo) (hhi : Λ ≤ Λhi)
    (hr₀ : 35 ≤ r₀) (hp0 : 0 < p)
    (hr : p ≤ (1 - Real.exp (-100)) * hp1P1Short r₀ ∧ hp2QShort r₀ ≤ Q)
    (hrung : (r₀ : ℝ) + 21 ≤ cellRungLow a Λlo)
    (hlam : lam ≤ cellLogMainLow a b c β ℓ ub p Q)
    (hcert : 1 / 10 ^ 10 + cellSubLow a b + cellErrLow a b ua Λhi ≤ Real.exp lam) :
    LowCellSpec q Λ :=
  Or.inr ⟨r₀, hr₀, hrung.trans (rungLow_of_cell ha0 haq hlo hlo1),
    PhiB1Low_ge_of_cell ha0.le haq hqb hb (lt_of_lt_of_le ha0 haq) hc0 hc1 hc hβ hℓ hua hub
      (by linarith) hhi hp0 hr hlam hcert⟩

/-! ### B2 -/

/-- **B2's per-scale constant**: `perScaleLow2Short q ≤ perScaleConstShort q K r` on `[9/20, ½)`
for every ladder length `K` and every tube of `r ≥ 35` blocks (`c₃ ≥ 0.17784`, `P₁ ≥ 0.28668`,
`Q ≤ 24542`). -/
theorem perScaleLow2Short_le {q : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) (K : ℕ) {r : ℕ}
    (hr : 35 ≤ r) : perScaleLow2Short q ≤ perScaleConstShort q K r := by
  have hc : (0.17784 : ℝ) ≤ c3FloorK q K := by
    unfold c3FloorK
    split_ifs
    · have hn : ⌊400 * q⌋₊ < 200 := (Nat.floor_lt (by linarith)).2 (by push_cast; linarith)
      exact le_trans (by norm_num) (c3OneTab_ge _ hn)
    · exact c3Floor_ge_of_nine_twentieths_le hq0 hq1
  have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  have hP1 := hp1P1Short_ge hr
  have hQ : hp2QShort r ≤ 24542 := by
    have h35 : hp2QShort 35 = 24542 :=
      (hp2QShort_of_lt (by norm_num)).trans (hp2QRung_eq_35 (by norm_num))
    exact h35 ▸ antitone_hp2QShort hr
  have hQ0 := hp2QShort_pos r
  have h1 : (0.17784 : ℝ) ^ (2 - q) ≤ c3FloorK q K ^ (2 - q) :=
    Real.rpow_le_rpow (by norm_num) hc (by linarith)
  have h2 : ((1 - Real.exp (-100)) * 0.28668) ^ (2 - q)
      ≤ ((1 - Real.exp (-100)) * hp1P1Short r) ^ (2 - q) :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hP1 hP.le) (by linarith)
  have h3 : (24542 : ℝ) ^ (-(1 - q)) ≤ hp2QShort r ^ (-(1 - q)) :=
    Real.rpow_le_rpow_of_nonpos hQ0 hQ (by linarith)
  have hB : 0 ≤ Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * (2 : ℝ) ^ (-q) := by positivity
  have e1 : perScaleLow2Short q = (0.17784 : ℝ) ^ (2 - q)
      * (Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * (2 : ℝ) ^ (-q))
      * ((1 - Real.exp (-100)) * 0.28668) ^ (2 - q) * (24542 : ℝ) ^ (-(1 - q)) := by
    rw [perScaleLow2Short]
    ring
  have e2 : perScaleConstShort q K r = c3FloorK q K ^ (2 - q)
      * (Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * (2 : ℝ) ^ (-q))
      * ((1 - Real.exp (-100)) * hp1P1Short r) ^ (2 - q) * hp2QShort r ^ (-(1 - q)) := by
    rw [perScaleConstShort]
    ring
  rw [e1, e2]
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h1 hB) h2 (by positivity)
    (mul_nonneg (Real.rpow_nonneg (by linarith) _) hB)) h3 (by positivity)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) hB)
      (Real.rpow_nonneg (by positivity) _))

/-- **B2 from its certificate**: `PhiB2Low(q, Λ) ≥ 10⁻¹⁰` for `9/20 ≤ q < ½`, `Λ ≤ 2100` and
`(1-2q)Λ ≥ 18` (so `Λ ≥ 180` and `81 ≤ qΛ ≤ 1050`): the cell `[9/20, ½]`,
`q log q ≥ (9/20)log(9/20)`, `q(1-2q) ≤ 9/200`. -/
theorem PhiB2Low_ge_of_cert {lam : ℝ}
    (hlam : lam ≤ Real.log (1 / 2)
      + cellLogCoreLow (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)) 1050 0.28667 24542
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2)
    (hcert : 1 / 10 ^ 10 + cellSubLow (9 / 20) (1 / 2) + cellErrLow (9 / 20) (1 / 2) 81 2100
      ≤ Real.exp lam)
    {q Λ : ℝ} (hq0 : 9 / 20 ≤ q) (hq1 : q < 1 / 2) (hΛ : Λ ≤ 2100)
    (hu : 18 ≤ (1 - 2 * q) * Λ) : 1 / 10 ^ 10 ≤ PhiB2Low q Λ := by
  have hqpos : 0 < q := by linarith
  have hΛpos : 0 < Λ := by
    rcases le_or_gt Λ 0 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 - 2 * q) h
      linarith
    · exact h
  have hΛ180 : 180 ≤ Λ := by
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * q ≤ 1 / 10) hΛpos.le
    linarith
  have hu81 : 81 ≤ q * Λ := by
    have := mul_le_mul hq0 hΛ180 (by norm_num) hqpos.le
    linarith
  have hu1050 : q * Λ ≤ 1050 := by
    have := mul_le_mul hq1.le hΛ hΛpos.le (by norm_num)
    linarith
  have hℓ := mul_log_ge_of_exp_neg_one_le (by linarith [Real.exp_neg_one_lt_d9]) hq0
  have hpP : (0.28667 : ℝ) ≤ (1 - Real.exp (-100)) * 0.28668 := by
    linarith [exp_neg_hundred_le_micro]
  have hcore := exp_cellLogCoreLow_le (c := 0.17784) (C := 0.17784) (P := 0.28668) (Q₀ := 24542)
    (u := q * Λ) hq0 hq1.le le_rfl hqpos (by norm_num) (by norm_num) le_rfl hℓ
    (by linarith) hu1050 (by norm_num) (by norm_num) hpP (by norm_num) le_rfl
  have hβ := mul_one_sub_two_mul_le_of_ge (by norm_num) hq0
  have hN : Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2)
      ≤ Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (Real.log (1 / 2)
      + cellLogCoreLow (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)) 1050 0.28667 24542
      - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2)
      = 1 / 2 * Real.exp
          (cellLogCoreLow (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)) 1050 0.28667 24542)
        * Real.exp (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2) := by
    rw [show Real.log (1 / 2)
        + cellLogCoreLow (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)) 1050 0.28667 24542
        - 9 / 20 * (1 - 2 * (9 / 20)) * 20.7867 - 1 / 2
        = Real.log (1 / 2)
          + cellLogCoreLow (9 / 20) (1 / 2) 0.17784 (9 / 20 * Real.log (9 / 20)) 1050 0.28667 24542
          + (-(9 / 20 * (1 - 2 * (9 / 20)) * 20.7867) - 1 / 2) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have e2 : mainB2Low q (q * Λ) = 1 / 2 * (cRed q * (2 : ℝ) ^ (2 * q - 1)
      * (Real.exp (-0.592) / 2 / (2 * ((q * Λ + 24) / q))) ^ q
      * ((0.17784 : ℝ) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * 0.28668) ^ (2 - q) * (24542 : ℝ) ^ (-(1 - q))))
      * Real.exp (-(q * (1 - 2 * q)) * 20.7867 - q) := by
    rw [mainB2Low, perScaleLow2Short]
    ring
  have hX0 := le_trans (Real.exp_pos _).le hcore
  have hmain : Real.exp lam ≤ mainB2Low q (q * Λ) := by
    calc Real.exp lam ≤ _ := Real.exp_le_exp.2 hlam
      _ = _ := e1
      _ ≤ _ := by
        rw [e2]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcore (by norm_num)) hN
          (Real.exp_pos _).le (mul_nonneg (by norm_num) hX0)
  have hsub := sub_le_cellSubLow (a := 9 / 20) (b := 1 / 2) (by norm_num) hq0 hq1.le le_rfl
  have herr := errBLow_le_cellErrLow (a := 9 / 20) (b := 1 / 2) (ua := 81) (Λhi := 2100)
    (by norm_num) hq0 hq1.le le_rfl hu81 (by linarith) hΛ
  unfold PhiB2Low
  linarith

end RMF
