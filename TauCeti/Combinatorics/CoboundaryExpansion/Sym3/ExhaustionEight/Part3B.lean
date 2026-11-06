/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic

/-!
# The `k = 8` exhaustion: gauges starting `[1, t02, x]` with `x` one of `t02`, `c1`, `c2`

Part of the kernel-checked exhaustion of every gauge for the Appendix A witness `w8` of Beasley
(DOI 10.5281/zenodo.22090958): the branches of `search` with the partial gauge `[1, t02, x]`,
split by the gauge on the next vertex. The parts are assembled in `Sym3.ExhaustionEight`; the
split keeps each file within the CI performance budget.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

private theorem k8_leaf_3_3_0 : search w8 27 4 [1, t02, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_3_1 : search w8 27 4 [1, t02, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_3_2 : search w8 27 4 [1, t02, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_3_3 : search w8 27 4 [1, t02, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_3_4 : search w8 27 4 [1, t02, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_3_5 : search w8 27 4 [1, t02, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_4_0 : search w8 27 4 [1, t02, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_4_1 : search w8 27 4 [1, t02, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_4_2 : search w8 27 4 [1, t02, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_4_3 : search w8 27 4 [1, t02, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_4_4 : search w8 27 4 [1, t02, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_4_5 : search w8 27 4 [1, t02, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_5_0 : search w8 27 4 [1, t02, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_5_1 : search w8 27 4 [1, t02, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_5_2 : search w8 27 4 [1, t02, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_5_3 : search w8 27 4 [1, t02, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_5_4 : search w8 27 4 [1, t02, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_5_5 : search w8 27 4 [1, t02, c2, c2] = true := by
  decide +kernel

/-- Every completion of the partial gauge `[1, t02, t02]` costs `w8` at least `27`. -/
theorem search_w8_3_3 : search w8 27 5 [1, t02, t02] = true :=
  search_split w8 27 4 [1, t02, t02] k8_leaf_3_3_0 k8_leaf_3_3_1 k8_leaf_3_3_2 k8_leaf_3_3_3
    k8_leaf_3_3_4 k8_leaf_3_3_5

/-- Every completion of the partial gauge `[1, t02, c1]` costs `w8` at least `27`. -/
theorem search_w8_3_4 : search w8 27 5 [1, t02, c1] = true :=
  search_split w8 27 4 [1, t02, c1] k8_leaf_3_4_0 k8_leaf_3_4_1 k8_leaf_3_4_2 k8_leaf_3_4_3
    k8_leaf_3_4_4 k8_leaf_3_4_5

/-- Every completion of the partial gauge `[1, t02, c2]` costs `w8` at least `27`. -/
theorem search_w8_3_5 : search w8 27 5 [1, t02, c2] = true :=
  search_split w8 27 4 [1, t02, c2] k8_leaf_3_5_0 k8_leaf_3_5_1 k8_leaf_3_5_2 k8_leaf_3_5_3
    k8_leaf_3_5_4 k8_leaf_3_5_5

end TauCeti.CoboundaryExpansion.Sym3
