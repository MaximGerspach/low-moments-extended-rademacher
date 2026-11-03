/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Paper
import RMF.PaperExplicit

/-!
# The axioms of the main results

For every result of `RMF/Paper.lean` and `RMF/PaperExplicit.lean`, the axioms it depends on are
exactly `propext`, `Classical.choice` and `Quot.sound`: no `sorryAx`, so nothing is left unproved.
Each check is a `#guard_msgs`, so the build fails if any result's axioms ever change.
-/

/-! ## The main results (`RMF/Paper.lean`) -/

/--
info: 'RMF.Paper.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.theorem_1_1

/--
info: 'RMF.Paper.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.theorem_1_2

/--
info: 'RMF.Paper.bound_1_3_extended' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.bound_1_3_extended

/--
info: 'RMF.Paper.bound_1_3_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.bound_1_3_weighted

/--
info: 'RMF.Paper.corollary_1_3_extended' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.corollary_1_3_extended

/--
info: 'RMF.Paper.corollary_1_3_weighted' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.corollary_1_3_weighted

/--
info: 'RMF.Paper.corollary_1_4_extended' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.corollary_1_4_extended

/--
info: 'RMF.Paper.corollary_1_4_weighted' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.corollary_1_4_weighted

/--
info: 'RMF.Paper.proposition_1_5_moments' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.proposition_1_5_moments

/--
info: 'RMF.Paper.proposition_1_5_limit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.proposition_1_5_limit

/--
info: 'RMF.Paper.harper_theorem_1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.harper_theorem_1

/--
info: 'RMF.Paper.harper_theorem_2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.harper_theorem_2

/--
info: 'RMF.Paper.caich_theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.caich_theorem_1_1

/-! ## With explicit constants (`RMF/PaperExplicit.lean`) -/

/--
info: 'RMF.Paper.bound_1_3_extended_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.bound_1_3_extended_explicit

/--
info: 'RMF.Paper.bound_1_3_weighted_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.bound_1_3_weighted_explicit

/--
info: 'RMF.Paper.corollary_1_3_extended_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.corollary_1_3_extended_explicit

/--
info: 'RMF.Paper.corollary_1_3_weighted_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.corollary_1_3_weighted_explicit

/--
info: 'RMF.Paper.harper_theorem_1_upper_explicit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RMF.Paper.harper_theorem_1_upper_explicit
