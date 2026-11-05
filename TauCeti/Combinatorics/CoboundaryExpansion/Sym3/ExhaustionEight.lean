/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic

/-!
# The `k = 8` witness: branch-and-bound exhaustion

Kernel-checked exhaustion of every gauge for the Appendix A witness `w8` of Beasley
(DOI 10.5281/zenodo.22090958), split by the gauge on the first three vertices, using
`search_split` and `gauge_lower_bb` from `Sym3.Basic`.
-/

@[expose] public section

namespace TauCeti.CoboundaryExpansion.Sym3

private theorem k8_leaf_0_0_0 : search w8 27 4 [1, 1, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_0_1 : search w8 27 4 [1, 1, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_0_2 : search w8 27 4 [1, 1, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_0_3 : search w8 27 4 [1, 1, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_0_4 : search w8 27 4 [1, 1, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_0_5 : search w8 27 4 [1, 1, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_1_0 : search w8 27 4 [1, 1, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_1_1 : search w8 27 4 [1, 1, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_1_2 : search w8 27 4 [1, 1, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_1_3 : search w8 27 4 [1, 1, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_1_4 : search w8 27 4 [1, 1, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_1_5 : search w8 27 4 [1, 1, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_2_0 : search w8 27 4 [1, 1, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_2_1 : search w8 27 4 [1, 1, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_2_2 : search w8 27 4 [1, 1, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_2_3 : search w8 27 4 [1, 1, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_2_4 : search w8 27 4 [1, 1, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_2_5 : search w8 27 4 [1, 1, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_3_0 : search w8 27 4 [1, 1, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_3_1 : search w8 27 4 [1, 1, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_3_2 : search w8 27 4 [1, 1, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_3_3 : search w8 27 4 [1, 1, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_3_4 : search w8 27 4 [1, 1, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_3_5 : search w8 27 4 [1, 1, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_4_0 : search w8 27 4 [1, 1, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_4_1 : search w8 27 4 [1, 1, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_4_2 : search w8 27 4 [1, 1, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_4_3 : search w8 27 4 [1, 1, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_4_4 : search w8 27 4 [1, 1, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_4_5 : search w8 27 4 [1, 1, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_5_0 : search w8 27 4 [1, 1, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_5_1 : search w8 27 4 [1, 1, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_5_2 : search w8 27 4 [1, 1, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_5_3 : search w8 27 4 [1, 1, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_5_4 : search w8 27 4 [1, 1, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_5_5 : search w8 27 4 [1, 1, c2, c2] = true := by
  decide +kernel

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

private theorem k8_leaf_1_3_0 : search w8 27 4 [1, t01, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_3_1 : search w8 27 4 [1, t01, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_3_2 : search w8 27 4 [1, t01, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_3_3 : search w8 27 4 [1, t01, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_3_4 : search w8 27 4 [1, t01, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_3_5 : search w8 27 4 [1, t01, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_4_0 : search w8 27 4 [1, t01, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_4_1 : search w8 27 4 [1, t01, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_4_2 : search w8 27 4 [1, t01, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_4_3 : search w8 27 4 [1, t01, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_4_4 : search w8 27 4 [1, t01, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_4_5 : search w8 27 4 [1, t01, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_5_0 : search w8 27 4 [1, t01, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_5_1 : search w8 27 4 [1, t01, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_5_2 : search w8 27 4 [1, t01, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_5_3 : search w8 27 4 [1, t01, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_5_4 : search w8 27 4 [1, t01, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_5_5 : search w8 27 4 [1, t01, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_0_0 : search w8 27 4 [1, t12, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_0_1 : search w8 27 4 [1, t12, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_0_2 : search w8 27 4 [1, t12, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_0_3 : search w8 27 4 [1, t12, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_0_4 : search w8 27 4 [1, t12, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_0_5 : search w8 27 4 [1, t12, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_1_0 : search w8 27 4 [1, t12, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_1_1 : search w8 27 4 [1, t12, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_1_2 : search w8 27 4 [1, t12, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_1_3 : search w8 27 4 [1, t12, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_1_4 : search w8 27 4 [1, t12, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_1_5 : search w8 27 4 [1, t12, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_2_0 : search w8 27 4 [1, t12, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_2_1 : search w8 27 4 [1, t12, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_2_2 : search w8 27 4 [1, t12, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_2_3 : search w8 27 4 [1, t12, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_2_4 : search w8 27 4 [1, t12, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_2_5 : search w8 27 4 [1, t12, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_3_0 : search w8 27 4 [1, t12, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_3_1 : search w8 27 4 [1, t12, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_3_2 : search w8 27 4 [1, t12, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_3_3 : search w8 27 4 [1, t12, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_3_4 : search w8 27 4 [1, t12, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_3_5 : search w8 27 4 [1, t12, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_4_0 : search w8 27 4 [1, t12, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_4_1 : search w8 27 4 [1, t12, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_4_2 : search w8 27 4 [1, t12, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_4_3 : search w8 27 4 [1, t12, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_4_4 : search w8 27 4 [1, t12, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_4_5 : search w8 27 4 [1, t12, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_5_0 : search w8 27 4 [1, t12, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_5_1 : search w8 27 4 [1, t12, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_5_2 : search w8 27 4 [1, t12, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_5_3 : search w8 27 4 [1, t12, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_5_4 : search w8 27 4 [1, t12, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_5_5 : search w8 27 4 [1, t12, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_0_0 : search w8 27 4 [1, t02, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_0_1 : search w8 27 4 [1, t02, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_0_2 : search w8 27 4 [1, t02, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_0_3 : search w8 27 4 [1, t02, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_0_4 : search w8 27 4 [1, t02, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_0_5 : search w8 27 4 [1, t02, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_1_0 : search w8 27 4 [1, t02, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_1_1 : search w8 27 4 [1, t02, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_1_2 : search w8 27 4 [1, t02, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_1_3 : search w8 27 4 [1, t02, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_1_4 : search w8 27 4 [1, t02, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_1_5 : search w8 27 4 [1, t02, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_2_0 : search w8 27 4 [1, t02, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_2_1 : search w8 27 4 [1, t02, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_2_2 : search w8 27 4 [1, t02, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_2_3 : search w8 27 4 [1, t02, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_2_4 : search w8 27 4 [1, t02, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_2_5 : search w8 27 4 [1, t02, t12, c2] = true := by
  decide +kernel

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

private theorem k8_leaf_4_0_0 : search w8 27 4 [1, c1, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_0_1 : search w8 27 4 [1, c1, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_0_2 : search w8 27 4 [1, c1, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_0_3 : search w8 27 4 [1, c1, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_0_4 : search w8 27 4 [1, c1, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_0_5 : search w8 27 4 [1, c1, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_1_0 : search w8 27 4 [1, c1, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_1_1 : search w8 27 4 [1, c1, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_1_2 : search w8 27 4 [1, c1, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_1_3 : search w8 27 4 [1, c1, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_1_4 : search w8 27 4 [1, c1, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_1_5 : search w8 27 4 [1, c1, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_2_0 : search w8 27 4 [1, c1, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_2_1 : search w8 27 4 [1, c1, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_2_2 : search w8 27 4 [1, c1, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_2_3 : search w8 27 4 [1, c1, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_2_4 : search w8 27 4 [1, c1, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_2_5 : search w8 27 4 [1, c1, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_3_0 : search w8 27 4 [1, c1, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_3_1 : search w8 27 4 [1, c1, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_3_2 : search w8 27 4 [1, c1, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_3_3 : search w8 27 4 [1, c1, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_3_4 : search w8 27 4 [1, c1, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_3_5 : search w8 27 4 [1, c1, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_4_0 : search w8 27 4 [1, c1, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_4_1 : search w8 27 4 [1, c1, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_4_2 : search w8 27 4 [1, c1, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_4_3 : search w8 27 4 [1, c1, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_4_4 : search w8 27 4 [1, c1, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_4_5 : search w8 27 4 [1, c1, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_5_0 : search w8 27 4 [1, c1, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_5_1 : search w8 27 4 [1, c1, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_5_2 : search w8 27 4 [1, c1, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_5_3 : search w8 27 4 [1, c1, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_5_4 : search w8 27 4 [1, c1, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_5_5 : search w8 27 4 [1, c1, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_0_0 : search w8 27 4 [1, c2, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_0_1 : search w8 27 4 [1, c2, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_0_2 : search w8 27 4 [1, c2, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_0_3 : search w8 27 4 [1, c2, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_0_4 : search w8 27 4 [1, c2, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_0_5 : search w8 27 4 [1, c2, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_1_0 : search w8 27 4 [1, c2, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_1_1 : search w8 27 4 [1, c2, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_1_2 : search w8 27 4 [1, c2, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_1_3 : search w8 27 4 [1, c2, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_1_4 : search w8 27 4 [1, c2, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_1_5 : search w8 27 4 [1, c2, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_2_0 : search w8 27 4 [1, c2, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_2_1 : search w8 27 4 [1, c2, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_2_2 : search w8 27 4 [1, c2, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_2_3 : search w8 27 4 [1, c2, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_2_4 : search w8 27 4 [1, c2, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_2_5 : search w8 27 4 [1, c2, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_3_0 : search w8 27 4 [1, c2, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_3_1 : search w8 27 4 [1, c2, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_3_2 : search w8 27 4 [1, c2, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_3_3 : search w8 27 4 [1, c2, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_3_4 : search w8 27 4 [1, c2, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_3_5 : search w8 27 4 [1, c2, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_4_0 : search w8 27 4 [1, c2, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_4_1 : search w8 27 4 [1, c2, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_4_2 : search w8 27 4 [1, c2, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_4_3 : search w8 27 4 [1, c2, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_4_4 : search w8 27 4 [1, c2, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_4_5 : search w8 27 4 [1, c2, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_5_0 : search w8 27 4 [1, c2, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_5_1 : search w8 27 4 [1, c2, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_5_2 : search w8 27 4 [1, c2, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_5_3 : search w8 27 4 [1, c2, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_5_4 : search w8 27 4 [1, c2, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_5_5 : search w8 27 4 [1, c2, c2, c2] = true := by
  decide +kernel

private theorem k8_node_0_0 : search w8 27 5 [1, 1, 1] = true :=
  search_split w8 27 4 [1, 1, 1] k8_leaf_0_0_0 k8_leaf_0_0_1 k8_leaf_0_0_2 k8_leaf_0_0_3
    k8_leaf_0_0_4 k8_leaf_0_0_5

private theorem k8_node_0_1 : search w8 27 5 [1, 1, t01] = true :=
  search_split w8 27 4 [1, 1, t01] k8_leaf_0_1_0 k8_leaf_0_1_1 k8_leaf_0_1_2 k8_leaf_0_1_3
    k8_leaf_0_1_4 k8_leaf_0_1_5

private theorem k8_node_0_2 : search w8 27 5 [1, 1, t12] = true :=
  search_split w8 27 4 [1, 1, t12] k8_leaf_0_2_0 k8_leaf_0_2_1 k8_leaf_0_2_2 k8_leaf_0_2_3
    k8_leaf_0_2_4 k8_leaf_0_2_5

private theorem k8_node_0_3 : search w8 27 5 [1, 1, t02] = true :=
  search_split w8 27 4 [1, 1, t02] k8_leaf_0_3_0 k8_leaf_0_3_1 k8_leaf_0_3_2 k8_leaf_0_3_3
    k8_leaf_0_3_4 k8_leaf_0_3_5

private theorem k8_node_0_4 : search w8 27 5 [1, 1, c1] = true :=
  search_split w8 27 4 [1, 1, c1] k8_leaf_0_4_0 k8_leaf_0_4_1 k8_leaf_0_4_2 k8_leaf_0_4_3
    k8_leaf_0_4_4 k8_leaf_0_4_5

private theorem k8_node_0_5 : search w8 27 5 [1, 1, c2] = true :=
  search_split w8 27 4 [1, 1, c2] k8_leaf_0_5_0 k8_leaf_0_5_1 k8_leaf_0_5_2 k8_leaf_0_5_3
    k8_leaf_0_5_4 k8_leaf_0_5_5

private theorem k8_node_1_0 : search w8 27 5 [1, t01, 1] = true :=
  search_split w8 27 4 [1, t01, 1] k8_leaf_1_0_0 k8_leaf_1_0_1 k8_leaf_1_0_2 k8_leaf_1_0_3
    k8_leaf_1_0_4 k8_leaf_1_0_5

private theorem k8_node_1_1 : search w8 27 5 [1, t01, t01] = true :=
  search_split w8 27 4 [1, t01, t01] k8_leaf_1_1_0 k8_leaf_1_1_1 k8_leaf_1_1_2 k8_leaf_1_1_3
    k8_leaf_1_1_4 k8_leaf_1_1_5

private theorem k8_node_1_2 : search w8 27 5 [1, t01, t12] = true :=
  search_split w8 27 4 [1, t01, t12] k8_leaf_1_2_0 k8_leaf_1_2_1 k8_leaf_1_2_2 k8_leaf_1_2_3
    k8_leaf_1_2_4 k8_leaf_1_2_5

private theorem k8_node_1_3 : search w8 27 5 [1, t01, t02] = true :=
  search_split w8 27 4 [1, t01, t02] k8_leaf_1_3_0 k8_leaf_1_3_1 k8_leaf_1_3_2 k8_leaf_1_3_3
    k8_leaf_1_3_4 k8_leaf_1_3_5

private theorem k8_node_1_4 : search w8 27 5 [1, t01, c1] = true :=
  search_split w8 27 4 [1, t01, c1] k8_leaf_1_4_0 k8_leaf_1_4_1 k8_leaf_1_4_2 k8_leaf_1_4_3
    k8_leaf_1_4_4 k8_leaf_1_4_5

private theorem k8_node_1_5 : search w8 27 5 [1, t01, c2] = true :=
  search_split w8 27 4 [1, t01, c2] k8_leaf_1_5_0 k8_leaf_1_5_1 k8_leaf_1_5_2 k8_leaf_1_5_3
    k8_leaf_1_5_4 k8_leaf_1_5_5

private theorem k8_node_2_0 : search w8 27 5 [1, t12, 1] = true :=
  search_split w8 27 4 [1, t12, 1] k8_leaf_2_0_0 k8_leaf_2_0_1 k8_leaf_2_0_2 k8_leaf_2_0_3
    k8_leaf_2_0_4 k8_leaf_2_0_5

private theorem k8_node_2_1 : search w8 27 5 [1, t12, t01] = true :=
  search_split w8 27 4 [1, t12, t01] k8_leaf_2_1_0 k8_leaf_2_1_1 k8_leaf_2_1_2 k8_leaf_2_1_3
    k8_leaf_2_1_4 k8_leaf_2_1_5

private theorem k8_node_2_2 : search w8 27 5 [1, t12, t12] = true :=
  search_split w8 27 4 [1, t12, t12] k8_leaf_2_2_0 k8_leaf_2_2_1 k8_leaf_2_2_2 k8_leaf_2_2_3
    k8_leaf_2_2_4 k8_leaf_2_2_5

private theorem k8_node_2_3 : search w8 27 5 [1, t12, t02] = true :=
  search_split w8 27 4 [1, t12, t02] k8_leaf_2_3_0 k8_leaf_2_3_1 k8_leaf_2_3_2 k8_leaf_2_3_3
    k8_leaf_2_3_4 k8_leaf_2_3_5

private theorem k8_node_2_4 : search w8 27 5 [1, t12, c1] = true :=
  search_split w8 27 4 [1, t12, c1] k8_leaf_2_4_0 k8_leaf_2_4_1 k8_leaf_2_4_2 k8_leaf_2_4_3
    k8_leaf_2_4_4 k8_leaf_2_4_5

private theorem k8_node_2_5 : search w8 27 5 [1, t12, c2] = true :=
  search_split w8 27 4 [1, t12, c2] k8_leaf_2_5_0 k8_leaf_2_5_1 k8_leaf_2_5_2 k8_leaf_2_5_3
    k8_leaf_2_5_4 k8_leaf_2_5_5

private theorem k8_node_3_0 : search w8 27 5 [1, t02, 1] = true :=
  search_split w8 27 4 [1, t02, 1] k8_leaf_3_0_0 k8_leaf_3_0_1 k8_leaf_3_0_2 k8_leaf_3_0_3
    k8_leaf_3_0_4 k8_leaf_3_0_5

private theorem k8_node_3_1 : search w8 27 5 [1, t02, t01] = true :=
  search_split w8 27 4 [1, t02, t01] k8_leaf_3_1_0 k8_leaf_3_1_1 k8_leaf_3_1_2 k8_leaf_3_1_3
    k8_leaf_3_1_4 k8_leaf_3_1_5

private theorem k8_node_3_2 : search w8 27 5 [1, t02, t12] = true :=
  search_split w8 27 4 [1, t02, t12] k8_leaf_3_2_0 k8_leaf_3_2_1 k8_leaf_3_2_2 k8_leaf_3_2_3
    k8_leaf_3_2_4 k8_leaf_3_2_5

private theorem k8_node_3_3 : search w8 27 5 [1, t02, t02] = true :=
  search_split w8 27 4 [1, t02, t02] k8_leaf_3_3_0 k8_leaf_3_3_1 k8_leaf_3_3_2 k8_leaf_3_3_3
    k8_leaf_3_3_4 k8_leaf_3_3_5

private theorem k8_node_3_4 : search w8 27 5 [1, t02, c1] = true :=
  search_split w8 27 4 [1, t02, c1] k8_leaf_3_4_0 k8_leaf_3_4_1 k8_leaf_3_4_2 k8_leaf_3_4_3
    k8_leaf_3_4_4 k8_leaf_3_4_5

private theorem k8_node_3_5 : search w8 27 5 [1, t02, c2] = true :=
  search_split w8 27 4 [1, t02, c2] k8_leaf_3_5_0 k8_leaf_3_5_1 k8_leaf_3_5_2 k8_leaf_3_5_3
    k8_leaf_3_5_4 k8_leaf_3_5_5

private theorem k8_node_4_0 : search w8 27 5 [1, c1, 1] = true :=
  search_split w8 27 4 [1, c1, 1] k8_leaf_4_0_0 k8_leaf_4_0_1 k8_leaf_4_0_2 k8_leaf_4_0_3
    k8_leaf_4_0_4 k8_leaf_4_0_5

private theorem k8_node_4_1 : search w8 27 5 [1, c1, t01] = true :=
  search_split w8 27 4 [1, c1, t01] k8_leaf_4_1_0 k8_leaf_4_1_1 k8_leaf_4_1_2 k8_leaf_4_1_3
    k8_leaf_4_1_4 k8_leaf_4_1_5

private theorem k8_node_4_2 : search w8 27 5 [1, c1, t12] = true :=
  search_split w8 27 4 [1, c1, t12] k8_leaf_4_2_0 k8_leaf_4_2_1 k8_leaf_4_2_2 k8_leaf_4_2_3
    k8_leaf_4_2_4 k8_leaf_4_2_5

private theorem k8_node_4_3 : search w8 27 5 [1, c1, t02] = true :=
  search_split w8 27 4 [1, c1, t02] k8_leaf_4_3_0 k8_leaf_4_3_1 k8_leaf_4_3_2 k8_leaf_4_3_3
    k8_leaf_4_3_4 k8_leaf_4_3_5

private theorem k8_node_4_4 : search w8 27 5 [1, c1, c1] = true :=
  search_split w8 27 4 [1, c1, c1] k8_leaf_4_4_0 k8_leaf_4_4_1 k8_leaf_4_4_2 k8_leaf_4_4_3
    k8_leaf_4_4_4 k8_leaf_4_4_5

private theorem k8_node_4_5 : search w8 27 5 [1, c1, c2] = true :=
  search_split w8 27 4 [1, c1, c2] k8_leaf_4_5_0 k8_leaf_4_5_1 k8_leaf_4_5_2 k8_leaf_4_5_3
    k8_leaf_4_5_4 k8_leaf_4_5_5

private theorem k8_node_5_0 : search w8 27 5 [1, c2, 1] = true :=
  search_split w8 27 4 [1, c2, 1] k8_leaf_5_0_0 k8_leaf_5_0_1 k8_leaf_5_0_2 k8_leaf_5_0_3
    k8_leaf_5_0_4 k8_leaf_5_0_5

private theorem k8_node_5_1 : search w8 27 5 [1, c2, t01] = true :=
  search_split w8 27 4 [1, c2, t01] k8_leaf_5_1_0 k8_leaf_5_1_1 k8_leaf_5_1_2 k8_leaf_5_1_3
    k8_leaf_5_1_4 k8_leaf_5_1_5

private theorem k8_node_5_2 : search w8 27 5 [1, c2, t12] = true :=
  search_split w8 27 4 [1, c2, t12] k8_leaf_5_2_0 k8_leaf_5_2_1 k8_leaf_5_2_2 k8_leaf_5_2_3
    k8_leaf_5_2_4 k8_leaf_5_2_5

private theorem k8_node_5_3 : search w8 27 5 [1, c2, t02] = true :=
  search_split w8 27 4 [1, c2, t02] k8_leaf_5_3_0 k8_leaf_5_3_1 k8_leaf_5_3_2 k8_leaf_5_3_3
    k8_leaf_5_3_4 k8_leaf_5_3_5

private theorem k8_node_5_4 : search w8 27 5 [1, c2, c1] = true :=
  search_split w8 27 4 [1, c2, c1] k8_leaf_5_4_0 k8_leaf_5_4_1 k8_leaf_5_4_2 k8_leaf_5_4_3
    k8_leaf_5_4_4 k8_leaf_5_4_5

private theorem k8_node_5_5 : search w8 27 5 [1, c2, c2] = true :=
  search_split w8 27 4 [1, c2, c2] k8_leaf_5_5_0 k8_leaf_5_5_1 k8_leaf_5_5_2 k8_leaf_5_5_3
    k8_leaf_5_5_4 k8_leaf_5_5_5

private theorem k8_node_0 : search w8 27 6 [1, 1] = true :=
  search_split w8 27 5 [1, 1] k8_node_0_0 k8_node_0_1 k8_node_0_2 k8_node_0_3 k8_node_0_4
    k8_node_0_5

private theorem k8_node_1 : search w8 27 6 [1, t01] = true :=
  search_split w8 27 5 [1, t01] k8_node_1_0 k8_node_1_1 k8_node_1_2 k8_node_1_3 k8_node_1_4
    k8_node_1_5

private theorem k8_node_2 : search w8 27 6 [1, t12] = true :=
  search_split w8 27 5 [1, t12] k8_node_2_0 k8_node_2_1 k8_node_2_2 k8_node_2_3 k8_node_2_4
    k8_node_2_5

private theorem k8_node_3 : search w8 27 6 [1, t02] = true :=
  search_split w8 27 5 [1, t02] k8_node_3_0 k8_node_3_1 k8_node_3_2 k8_node_3_3 k8_node_3_4
    k8_node_3_5

private theorem k8_node_4 : search w8 27 6 [1, c1] = true :=
  search_split w8 27 5 [1, c1] k8_node_4_0 k8_node_4_1 k8_node_4_2 k8_node_4_3 k8_node_4_4
    k8_node_4_5

private theorem k8_node_5 : search w8 27 6 [1, c2] = true :=
  search_split w8 27 5 [1, c2] k8_node_5_0 k8_node_5_1 k8_node_5_2 k8_node_5_3 k8_node_5_4
    k8_node_5_5

private theorem k8_root : search w8 27 7 [1] = true :=
  search_split w8 27 6 [1] k8_node_0 k8_node_1 k8_node_2 k8_node_3 k8_node_4 k8_node_5

/-- **Theorem 4, k = 8.** `N = 72`, `D = 27`: `N/D = 8/3`. The residual carries twelve
transpositions (all three of `Sym(3)`) and one 3-cycle. -/
theorem witness_k8 :
    defect w8 = 72 ∧ (∀ β, 27 ≤ cost w8 β) ∧ cost w8 (fun _ => 1) = 27 ∧ 72 * 3 = 8 * 27 :=
  ⟨by decide +kernel, gauge_lower_bb w8 27 k8_root, by decide +kernel, by norm_num⟩

end TauCeti.CoboundaryExpansion.Sym3
