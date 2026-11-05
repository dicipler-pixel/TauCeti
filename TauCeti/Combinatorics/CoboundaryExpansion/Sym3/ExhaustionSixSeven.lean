/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic

/-!
# The `k = 6` and `k = 7` witnesses: branch-and-bound exhaustion

Kernel-checked exhaustion of every gauge for the Appendix A witnesses `w6` and `w7` of
Beasley (DOI 10.5281/zenodo.22090958), split by the gauge on the first vertices, using
`search_split` and `gauge_lower_bb` from `Sym3.Basic`.
-/

@[expose] public section

namespace TauCeti.CoboundaryExpansion.Sym3

/-! ### The k = 6, 7 and 8 exhaustions, split by the gauge on the first vertices -/

private theorem k6_leaf_0 : search w6 18 4 [1, 1] = true := by
  decide +kernel

private theorem k6_leaf_1 : search w6 18 4 [1, t01] = true := by
  decide +kernel

private theorem k6_leaf_2 : search w6 18 4 [1, t12] = true := by
  decide +kernel

private theorem k6_leaf_3 : search w6 18 4 [1, t02] = true := by
  decide +kernel

private theorem k6_leaf_4 : search w6 18 4 [1, c1] = true := by
  decide +kernel

private theorem k6_leaf_5 : search w6 18 4 [1, c2] = true := by
  decide +kernel

private theorem k6_root : search w6 18 5 [1] = true :=
  search_split w6 18 4 [1] k6_leaf_0 k6_leaf_1 k6_leaf_2 k6_leaf_3 k6_leaf_4 k6_leaf_5

private theorem k7_leaf_0_0 : search w7 12 4 [1, 1, 1] = true := by
  decide +kernel

private theorem k7_leaf_0_1 : search w7 12 4 [1, 1, t01] = true := by
  decide +kernel

private theorem k7_leaf_0_2 : search w7 12 4 [1, 1, t12] = true := by
  decide +kernel

private theorem k7_leaf_0_3 : search w7 12 4 [1, 1, t02] = true := by
  decide +kernel

private theorem k7_leaf_0_4 : search w7 12 4 [1, 1, c1] = true := by
  decide +kernel

private theorem k7_leaf_0_5 : search w7 12 4 [1, 1, c2] = true := by
  decide +kernel

private theorem k7_leaf_1_0 : search w7 12 4 [1, t01, 1] = true := by
  decide +kernel

private theorem k7_leaf_1_1 : search w7 12 4 [1, t01, t01] = true := by
  decide +kernel

private theorem k7_leaf_1_2 : search w7 12 4 [1, t01, t12] = true := by
  decide +kernel

private theorem k7_leaf_1_3 : search w7 12 4 [1, t01, t02] = true := by
  decide +kernel

private theorem k7_leaf_1_4 : search w7 12 4 [1, t01, c1] = true := by
  decide +kernel

private theorem k7_leaf_1_5 : search w7 12 4 [1, t01, c2] = true := by
  decide +kernel

private theorem k7_leaf_2_0 : search w7 12 4 [1, t12, 1] = true := by
  decide +kernel

private theorem k7_leaf_2_1 : search w7 12 4 [1, t12, t01] = true := by
  decide +kernel

private theorem k7_leaf_2_2 : search w7 12 4 [1, t12, t12] = true := by
  decide +kernel

private theorem k7_leaf_2_3 : search w7 12 4 [1, t12, t02] = true := by
  decide +kernel

private theorem k7_leaf_2_4 : search w7 12 4 [1, t12, c1] = true := by
  decide +kernel

private theorem k7_leaf_2_5 : search w7 12 4 [1, t12, c2] = true := by
  decide +kernel

private theorem k7_leaf_3_0 : search w7 12 4 [1, t02, 1] = true := by
  decide +kernel

private theorem k7_leaf_3_1 : search w7 12 4 [1, t02, t01] = true := by
  decide +kernel

private theorem k7_leaf_3_2 : search w7 12 4 [1, t02, t12] = true := by
  decide +kernel

private theorem k7_leaf_3_3 : search w7 12 4 [1, t02, t02] = true := by
  decide +kernel

private theorem k7_leaf_3_4 : search w7 12 4 [1, t02, c1] = true := by
  decide +kernel

private theorem k7_leaf_3_5 : search w7 12 4 [1, t02, c2] = true := by
  decide +kernel

private theorem k7_leaf_4_0 : search w7 12 4 [1, c1, 1] = true := by
  decide +kernel

private theorem k7_leaf_4_1 : search w7 12 4 [1, c1, t01] = true := by
  decide +kernel

private theorem k7_leaf_4_2 : search w7 12 4 [1, c1, t12] = true := by
  decide +kernel

private theorem k7_leaf_4_3 : search w7 12 4 [1, c1, t02] = true := by
  decide +kernel

private theorem k7_leaf_4_4 : search w7 12 4 [1, c1, c1] = true := by
  decide +kernel

private theorem k7_leaf_4_5 : search w7 12 4 [1, c1, c2] = true := by
  decide +kernel

private theorem k7_leaf_5_0 : search w7 12 4 [1, c2, 1] = true := by
  decide +kernel

private theorem k7_leaf_5_1 : search w7 12 4 [1, c2, t01] = true := by
  decide +kernel

private theorem k7_leaf_5_2 : search w7 12 4 [1, c2, t12] = true := by
  decide +kernel

private theorem k7_leaf_5_3 : search w7 12 4 [1, c2, t02] = true := by
  decide +kernel

private theorem k7_leaf_5_4 : search w7 12 4 [1, c2, c1] = true := by
  decide +kernel

private theorem k7_leaf_5_5 : search w7 12 4 [1, c2, c2] = true := by
  decide +kernel

private theorem k7_node_0 : search w7 12 5 [1, 1] = true :=
  search_split w7 12 4 [1, 1] k7_leaf_0_0 k7_leaf_0_1 k7_leaf_0_2 k7_leaf_0_3 k7_leaf_0_4
    k7_leaf_0_5

private theorem k7_node_1 : search w7 12 5 [1, t01] = true :=
  search_split w7 12 4 [1, t01] k7_leaf_1_0 k7_leaf_1_1 k7_leaf_1_2 k7_leaf_1_3 k7_leaf_1_4
    k7_leaf_1_5

private theorem k7_node_2 : search w7 12 5 [1, t12] = true :=
  search_split w7 12 4 [1, t12] k7_leaf_2_0 k7_leaf_2_1 k7_leaf_2_2 k7_leaf_2_3 k7_leaf_2_4
    k7_leaf_2_5

private theorem k7_node_3 : search w7 12 5 [1, t02] = true :=
  search_split w7 12 4 [1, t02] k7_leaf_3_0 k7_leaf_3_1 k7_leaf_3_2 k7_leaf_3_3 k7_leaf_3_4
    k7_leaf_3_5

private theorem k7_node_4 : search w7 12 5 [1, c1] = true :=
  search_split w7 12 4 [1, c1] k7_leaf_4_0 k7_leaf_4_1 k7_leaf_4_2 k7_leaf_4_3 k7_leaf_4_4
    k7_leaf_4_5

private theorem k7_node_5 : search w7 12 5 [1, c2] = true :=
  search_split w7 12 4 [1, c2] k7_leaf_5_0 k7_leaf_5_1 k7_leaf_5_2 k7_leaf_5_3 k7_leaf_5_4
    k7_leaf_5_5

private theorem k7_root : search w7 12 6 [1] = true :=
  search_split w7 12 5 [1] k7_node_0 k7_node_1 k7_node_2 k7_node_3 k7_node_4 k7_node_5

/-- **Theorem 4, k = 6.** `N = 36`, `D = 18`: `N/D = 2 = 6/3`. -/
theorem witness_k6 :
    defect w6 = 36 ∧ (∀ β, 18 ≤ cost w6 β) ∧ cost w6 (fun _ => 1) = 18 ∧ 36 * 3 = 6 * 18 :=
  ⟨by decide +kernel, gauge_lower_bb w6 18 k6_root, by decide +kernel, by norm_num⟩

/-- **Theorem 4, k = 7.** `N = 28`, `D = 12`: `N/D = 7/3`. -/
theorem witness_k7 :
    defect w7 = 28 ∧ (∀ β, 12 ≤ cost w7 β) ∧ cost w7 (fun _ => 1) = 12 ∧ 28 * 3 = 7 * 12 :=
  ⟨by decide +kernel, gauge_lower_bb w7 12 k7_root, by decide +kernel, by norm_num⟩

end TauCeti.CoboundaryExpansion.Sym3
