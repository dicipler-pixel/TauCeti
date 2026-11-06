/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part0A
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part0B
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part1A
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part1B
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part2A
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part2B
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part3A
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part3B
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part4A
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part4B
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part5A
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight.Part5B

/-!
# The `k = 8` witness: branch-and-bound exhaustion

Kernel-checked exhaustion of every gauge for the Appendix A witness `w8` of Beasley
(DOI 10.5281/zenodo.22090958), using `search_split` and `gauge_lower_bb` from `Sym3.Basic`. The
thirty-six branches by the gauge on vertices `1` and `2` are checked in
`Sym3.ExhaustionEight.Part0A` … `Sym3.ExhaustionEight.Part5B`.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

private theorem k8_node_0 : search w8 27 6 [1, 1] = true :=
  search_split w8 27 5 [1, 1] search_w8_0_0 search_w8_0_1 search_w8_0_2 search_w8_0_3 search_w8_0_4
    search_w8_0_5

private theorem k8_node_1 : search w8 27 6 [1, t01] = true :=
  search_split w8 27 5 [1, t01] search_w8_1_0 search_w8_1_1 search_w8_1_2 search_w8_1_3
    search_w8_1_4 search_w8_1_5

private theorem k8_node_2 : search w8 27 6 [1, t12] = true :=
  search_split w8 27 5 [1, t12] search_w8_2_0 search_w8_2_1 search_w8_2_2 search_w8_2_3
    search_w8_2_4 search_w8_2_5

private theorem k8_node_3 : search w8 27 6 [1, t02] = true :=
  search_split w8 27 5 [1, t02] search_w8_3_0 search_w8_3_1 search_w8_3_2 search_w8_3_3
    search_w8_3_4 search_w8_3_5

private theorem k8_node_4 : search w8 27 6 [1, c1] = true :=
  search_split w8 27 5 [1, c1] search_w8_4_0 search_w8_4_1 search_w8_4_2 search_w8_4_3 search_w8_4_4
    search_w8_4_5

private theorem k8_node_5 : search w8 27 6 [1, c2] = true :=
  search_split w8 27 5 [1, c2] search_w8_5_0 search_w8_5_1 search_w8_5_2 search_w8_5_3 search_w8_5_4
    search_w8_5_5

private theorem k8_root : search w8 27 7 [1] = true :=
  search_split w8 27 6 [1] k8_node_0 k8_node_1 k8_node_2 k8_node_3 k8_node_4 k8_node_5

/-- **Theorem 4, k = 8.** `N = 72`, `D = 27`: `N/D = 8/3`. The residual carries twelve
transpositions (all three of `Sym(3)`) and one 3-cycle. -/
theorem witness_k8 :
    defect w8 = 72 ∧ (∀ β, 27 ≤ cost w8 β) ∧ cost w8 (fun _ => 1) = 27 ∧ 72 * 3 = 8 * 27 :=
  ⟨by decide +kernel, gauge_lower_bb w8 27 k8_root, by decide +kernel, by norm_num⟩

end TauCeti.CoboundaryExpansion.Sym3
