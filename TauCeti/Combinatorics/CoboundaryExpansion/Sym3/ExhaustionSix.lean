/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic

/-!
# The `k = 6` witness: branch-and-bound exhaustion

Kernel-checked exhaustion of every gauge for the Appendix A witness `w6` of Beasley
(DOI 10.5281/zenodo.22090958), split by the gauge on the first two vertices, using
`search_split` and `gauge_lower_bb` from `Sym3.Basic`.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3


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

/-- **Theorem 4, k = 6.** `N = 36`, `D = 18`: `N/D = 2 = 6/3`. -/
theorem witness_k6 :
    defect w6 = 36 ∧ (∀ β, 18 ≤ cost w6 β) ∧ cost w6 (fun _ => 1) = 18 ∧ 36 * 3 = 6 * 18 :=
  ⟨by decide +kernel, gauge_lower_bb w6 18 k6_root, by decide +kernel, by norm_num⟩

end TauCeti.CoboundaryExpansion.Sym3
