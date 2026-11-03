/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Cert.Rows0.Cells0
import RMF.UniformLower.HP1Cert.Rows0.Cells1
import RMF.UniformLower.HP1Cert.Rows0.Cells2
import RMF.UniformLower.HP1Cert.Rows0.Cells3
import RMF.UniformLower.HP1Cert.Rows0.Cells4
import RMF.UniformLower.HP1Cert.Rows1.Cells0
import RMF.UniformLower.HP1Cert.Rows1.Cells1
import RMF.UniformLower.HP1Cert.Rows1.Cells2
import RMF.UniformLower.HP1Cert.Rows1.Cells3
import RMF.UniformLower.HP1Cert.Rows1.Cells4
import RMF.UniformLower.HP1Cert.Rows2.Cells0
import RMF.UniformLower.HP1Cert.Rows2.Cells1
import RMF.UniformLower.HP1Cert.Rows2.Cells2
import RMF.UniformLower.HP1Cert.Rows2.Cells3
import RMF.UniformLower.HP1Cert.Rows2.Cells4
import RMF.UniformLower.HP1Cert.Rows3.Cells0
import RMF.UniformLower.HP1Cert.Rows3.Cells1
import RMF.UniformLower.HP1Cert.Rows3.Cells2
import RMF.UniformLower.HP1Cert.Rows3.Cells3
import RMF.UniformLower.HP1Cert.Rows3.Cells4
import RMF.UniformLower.HP1Cert.Rows4.Cells0
import RMF.UniformLower.HP1Cert.Rows4.Cells1
import RMF.UniformLower.HP1Cert.Rows4.Cells2
import RMF.UniformLower.HP1Cert.Rows4.Cells3
import RMF.UniformLower.HP1Cert.Rows4.Cells4
import RMF.UniformLower.HP1Cert.Rows5.Cells0
import RMF.UniformLower.HP1Cert.Rows5.Cells1
import RMF.UniformLower.HP1Cert.Rows5.Cells2
import RMF.UniformLower.HP1Cert.Rows5.Cells3
import RMF.UniformLower.HP1Cert.Rows5.Cells4
import RMF.UniformLower.HP1Cert.Rows6.Cells0
import RMF.UniformLower.HP1Cert.Rows6.Cells1
import RMF.UniformLower.HP1Cert.Rows6.Cells2
import RMF.UniformLower.HP1Cert.Rows6.Cells3
import RMF.UniformLower.HP1Cert.Rows6.Cells4
import RMF.UniformLower.HP1Cert.Rows7.Cells0
import RMF.UniformLower.HP1Cert.Rows7.Cells1
import RMF.UniformLower.HP1Cert.Rows7.Cells2
import RMF.UniformLower.HP1Cert.Rows7.Cells3
import RMF.UniformLower.HP1Cert.Rows7.Cells4
import RMF.UniformLower.HP1Cert.Window

/-!
# HP1's certificate: the rows of every cell

HP1's per-cell numerics.  This file imports the certificate's cells and proves
`2e^{-40} ≤ 10⁻¹⁵` (`RMF.two_mul_exp_neg_forty_le`).  The files:

* `RMF/UniformLower/HP1Cert/Basic.lean`: the generic rows and the one-cell theorem;
* `RMF/UniformLower/HP1Cert/Nodes.lean`: the node data;
* `RMF/UniformLower/HP1Cert/Rows*/Cells*.lean`: the rows and the lower sums per cell (emitted);
* `RMF/UniformLower/HP1Cert/Window.lean`: the event `RMF.hp1Event` (`⊆ H(k,h) ∩ E″_>(k)`,
  `RMF.hp1Event_subset`), its measurability, the tilt identity, the window from its cells.

The cell bounds built on these rows, and the window integrals, are in
`RMF/UniformLower/HP1CertFloor.lean` and `RMF/UniformLower/HP1CertShort.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

lemma two_mul_exp_neg_forty_le : 2 * Real.exp (-40) ≤ 1 / 10 ^ 15 := by
  have h := exp_le_of_sum_neg (x := -40) (y := 40) (B := 1 / (2 * 10 ^ 15)) 32 le_rfl
    (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  linarith

end RMF
