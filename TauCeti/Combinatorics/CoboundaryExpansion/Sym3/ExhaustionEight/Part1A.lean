/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic

/-!
# The `k = 8` exhaustion: gauges starting `[1, t01, x]` with `x` one of `1`, `t01`, `t12`

Part of the kernel-checked exhaustion of every gauge for the Appendix A witness `w8` of Beasley
(DOI 10.5281/zenodo.22090958): the branches of `search` with the partial gauge `[1, t01, x]`,
split by the gauge on the next vertex. The parts are assembled in `Sym3.ExhaustionEight`; the
split keeps each file within the CI performance budget.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

private theorem k8_leaf_1_0_0 : search w8 27 4 [1, t01, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_0_1 : search w8 27 4 [1, t01, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_0_2 : search w8 27 4 [1, t01, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_0_3 : search w8 27 4 [1, t01, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_0_4 : search w8 27 4 [1, t01, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_0_5 : search w8 27 4 [1, t01, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_1_0 : search w8 27 4 [1, t01, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_1_1 : search w8 27 4 [1, t01, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_1_2 : search w8 27 4 [1, t01, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_1_3 : search w8 27 4 [1, t01, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_1_4 : search w8 27 4 [1, t01, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_1_5 : search w8 27 4 [1, t01, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_2_0 : search w8 27 4 [1, t01, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_2_1 : search w8 27 4 [1, t01, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_2_2 : search w8 27 4 [1, t01, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_2_3 : search w8 27 4 [1, t01, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_2_4 : search w8 27 4 [1, t01, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_2_5 : search w8 27 4 [1, t01, t12, c2] = true := by
  decide +kernel

/-- Every completion of the partial gauge `[1, t01, 1]` costs `w8` at least `27`. -/
theorem search_w8_1_0 : search w8 27 5 [1, t01, 1] = true :=
  search_split w8 27 4 [1, t01, 1] k8_leaf_1_0_0 k8_leaf_1_0_1 k8_leaf_1_0_2 k8_leaf_1_0_3
    k8_leaf_1_0_4 k8_leaf_1_0_5

/-- Every completion of the partial gauge `[1, t01, t01]` costs `w8` at least `27`. -/
theorem search_w8_1_1 : search w8 27 5 [1, t01, t01] = true :=
  search_split w8 27 4 [1, t01, t01] k8_leaf_1_1_0 k8_leaf_1_1_1 k8_leaf_1_1_2 k8_leaf_1_1_3
    k8_leaf_1_1_4 k8_leaf_1_1_5

/-- Every completion of the partial gauge `[1, t01, t12]` costs `w8` at least `27`. -/
theorem search_w8_1_2 : search w8 27 5 [1, t01, t12] = true :=
  search_split w8 27 4 [1, t01, t12] k8_leaf_1_2_0 k8_leaf_1_2_1 k8_leaf_1_2_2 k8_leaf_1_2_3
    k8_leaf_1_2_4 k8_leaf_1_2_5

end TauCeti.CoboundaryExpansion.Sym3
