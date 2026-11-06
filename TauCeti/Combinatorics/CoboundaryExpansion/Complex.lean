/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Defs
public import TauCeti.Combinatorics.Hypergraph.Complex.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# `TwoComplex` as a rank-three `HypergraphComplex`

README 2.1: a `TwoComplex V` is the edge/triangle part of a `TauCeti.HypergraphComplex 3 V`.

* `TwoComplex.toHypergraphComplex` adds the empty face and every singleton of `V`, in the same
  filter form as `TriadicComplex3.toHypergraphComplex`;
* `TwoComplex.ofHypergraphComplex` keeps levels `2` and `3`;
* `TwoComplex.ofHypergraphComplex_toHypergraphComplex`: forgetting after adding is the identity;
* `TwoComplex.toHypergraphComplex_ofHypergraphComplex`: adding after forgetting is the identity
  on complexes whose level `1` is every singleton.

The face counts of `complete V` are `complete_edges_card` and `complete_triangles_card`.
-/

public section

open Finset

namespace TauCeti.CoboundaryExpansion

namespace TwoComplex

variable {V : Type*} [DecidableEq V]

/-- The rank-three hypergraph complex of a 2-complex on a finite vertex type: every set of size
at most one, together with the edges and the triangles. Level zero is `{∅}`, as in every
hypergraph complex (`HypergraphComplex.faces_zero`). -/
noncomputable def toHypergraphComplex [Fintype V] (X : TwoComplex V) : HypergraphComplex 3 V where
  faces k _ := {s ∈ univ.powersetCard k | k ≤ 1 ∨ s ∈ X.edges ∨ s ∈ X.triangles}
  face_card _ _ _ hs := (mem_powersetCard.1 (mem_filter.1 hs).1).2
  down_closed k hk s hs t hts htr := by
    obtain ⟨hsP, hface⟩ := mem_filter.1 hs
    obtain ⟨-, hsk⟩ := mem_powersetCard.1 hsP
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, rfl⟩, ?_⟩
    by_cases ht₁ : #t ≤ 1
    · exact Or.inl ht₁
    · have htk : #t ≤ k := hsk ▸ card_le_card hts
      have hsET : s ∈ X.edges ∨ s ∈ X.triangles := hface.resolve_left (by omega)
      rcases hsET with hE | hT
      · -- A subset with at least two elements of an edge is the edge.
        have hs2 := X.card_edge s hE
        obtain rfl : t = s := eq_of_subset_of_card_le hts (by omega)
        exact Or.inr (Or.inl hE)
      · have hs3 := X.card_triangle s hT
        by_cases ht₂ : #t = 2
        · exact Or.inr (Or.inl (X.face_mem s hT t hts ht₂))
        · -- A subset with three elements of a triangle is the triangle.
          obtain rfl : t = s := eq_of_subset_of_card_le hts (by omega)
          exact Or.inr (Or.inr hT)
  empty_mem := by simp

/-- Membership in a level of the hypergraph complex of a 2-complex. -/
@[simp]
theorem mem_faces_toHypergraphComplex [Fintype V] (X : TwoComplex V) {k : ℕ} (hk : k ≤ 3)
    {s : Finset V} :
    s ∈ X.toHypergraphComplex.faces k hk ↔ #s = k ∧ (k ≤ 1 ∨ s ∈ X.edges ∨ s ∈ X.triangles) := by
  simp [toHypergraphComplex]

/-- Level one of the hypergraph complex of a 2-complex is every singleton. -/
theorem faces_one_toHypergraphComplex [Fintype V] (X : TwoComplex V) :
    X.toHypergraphComplex.faces 1 (by decide) = univ.powersetCard 1 := by
  ext s
  simp

/-- Level two of the hypergraph complex of a 2-complex is its set of edges. -/
@[simp]
theorem faces_two_toHypergraphComplex [Fintype V] (X : TwoComplex V) :
    X.toHypergraphComplex.faces 2 (by decide) = X.edges := by
  ext s
  simp only [mem_faces_toHypergraphComplex, show ¬2 ≤ 1 by decide, false_or]
  constructor
  · rintro ⟨hs, hE | hT⟩
    · exact hE
    · have := X.card_triangle s hT
      omega
  · intro hE
    exact ⟨X.card_edge s hE, Or.inl hE⟩

/-- Level three of the hypergraph complex of a 2-complex is its set of triangles. -/
@[simp]
theorem faces_three_toHypergraphComplex [Fintype V] (X : TwoComplex V) :
    X.toHypergraphComplex.faces 3 (by decide) = X.triangles := by
  ext s
  simp only [mem_faces_toHypergraphComplex, show ¬3 ≤ 1 by decide, false_or]
  constructor
  · rintro ⟨hs, hE | hT⟩
    · have := X.card_edge s hE
      omega
    · exact hT
  · intro hT
    exact ⟨X.card_triangle s hT, Or.inr hT⟩

/-- The levels `2` and `3` of a rank-three hypergraph complex, as a 2-complex. -/
@[expose] def ofHypergraphComplex (C : HypergraphComplex 3 V) : TwoComplex V where
  edges := C.faces 2 (by decide)
  triangles := C.faces 3 (by decide)
  card_edge := C.face_card 2 (by decide)
  card_triangle := C.face_card 3 (by decide)
  face_mem t ht e he hc := by
    have hmem := C.down_closed 3 (by decide) t ht e he (by omega)
    -- `hmem` names the level by `#e`, which is `2`.
    simpa only [hc] using hmem

/-- The edges of the 2-complex of a hypergraph complex are its level two. -/
@[simp]
theorem edges_ofHypergraphComplex (C : HypergraphComplex 3 V) :
    (ofHypergraphComplex C).edges = C.faces 2 (by decide) :=
  rfl

/-- The triangles of the 2-complex of a hypergraph complex are its level three. -/
@[simp]
theorem triangles_ofHypergraphComplex (C : HypergraphComplex 3 V) :
    (ofHypergraphComplex C).triangles = C.faces 3 (by decide) :=
  rfl

/-- Forgetting levels zero and one recovers the 2-complex. -/
@[simp]
theorem ofHypergraphComplex_toHypergraphComplex [Fintype V] (X : TwoComplex V) :
    ofHypergraphComplex X.toHypergraphComplex = X := by
  cases X with
  | mk E T hE hT hF =>
    simp only [ofHypergraphComplex, faces_two_toHypergraphComplex,
      faces_three_toHypergraphComplex]

/-- A rank-three hypergraph complex whose level one is every singleton is recovered from its
levels two and three. -/
theorem toHypergraphComplex_ofHypergraphComplex [Fintype V] (C : HypergraphComplex 3 V)
    (hfaces1 : C.faces 1 (by decide) = univ.powersetCard 1) :
    (ofHypergraphComplex C).toHypergraphComplex = C := by
  refine HypergraphComplex.ext fun k hk => ?_
  interval_cases k
  · rw [HypergraphComplex.faces_zero]
    ext s
    simp
  · rw [hfaces1]
    exact faces_one_toHypergraphComplex _
  · exact faces_two_toHypergraphComplex _
  · exact faces_three_toHypergraphComplex _

end TwoComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete complex on `k` vertices has `k choose 2` edges. -/
theorem complete_edges_card : #(complete V).edges = (Fintype.card V).choose 2 := by
  simp [complete, card_powersetCard]

/-- The complete complex on `k` vertices has `k choose 3` triangles. -/
theorem complete_triangles_card : #(complete V).triangles = (Fintype.card V).choose 3 := by
  simp [complete, card_powersetCard]

end TauCeti.CoboundaryExpansion
