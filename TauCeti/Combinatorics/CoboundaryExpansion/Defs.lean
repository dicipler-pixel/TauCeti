/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jeromie Beasley
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Data.Finset.Powerset

/-!
# Coboundary expansion with group coefficients: the basic definitions

The moved-point norm `movedNorm α` on `Equiv.Perm α`, finite 2-complexes `TwoComplex V` with the
complete complex `complete V`, group-valued 1-cochains `Cochain X G` with their triangle defect,
gauge cost and gauge distance, and the first coboundary Cheeger constant `h1` in the counting
convention together with its normalized form `h1Norm`.

These are the definitions of Layers 1.3, 2.2 and 3.1/3.3 of the CoboundaryExpansion roadmap
(TauCetiRoadmap, `TauCetiRoadmap/CoboundaryExpansion`), transcribed unchanged from its
`Suggested.lean` (counting convention, gauge convention `β u⁻¹ * α u v * β v`, orientation
`u < v < w`, infimum over cochains at positive gauge distance). Only the definitions needed to
state the Layer 6 and Layer 8.1 results are included here.
-/

@[expose] public section

noncomputable section

open Finset

namespace TauCeti.CoboundaryExpansion

section Moved

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The moved-point count of a permutation: the unnormalized Hamming norm. -/
def movedNorm : GroupNorm (Equiv.Perm α) where
  toFun σ := (σ.support.card : ℝ)
  map_one' := by simp [Equiv.Perm.support_one]
  mul_le' σ τ := by
    change ((σ * τ).support.card : ℝ) ≤ σ.support.card + τ.support.card
    have h : (σ * τ).support ⊆ σ.support ∪ τ.support := Equiv.Perm.support_mul_le σ τ
    exact_mod_cast (Finset.card_le_card h).trans (Finset.card_union_le _ _)
  inv' σ := by simp [Equiv.Perm.support_inv]
  eq_one_of_map_eq_zero' σ h := by
    have h' : (σ.support.card : ℝ) = 0 := h
    exact Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp (by exact_mod_cast h'))

end Moved

/-- A finite 2-complex: 2-element edges and 3-element triangles whose 2-element faces are edges.

This is the edge/triangle specialization of the finite graded complex `HypergraphComplex 3 V`
owned by the Regularity roadmap (Layer 5 of `TauCetiRoadmap/Regularity`): `edges` and
`triangles` are its levels 2 and 3. The conversions `toHypergraphComplex` and
`ofHypergraphComplex` between the two are README targets; that roadmap is not importable here,
so it is not referenced in code. -/
structure TwoComplex (V : Type*) [DecidableEq V] where
  /-- The edges, each a 2-element set. -/
  edges : Finset (Finset V)
  /-- The triangles, each a 3-element set. -/
  triangles : Finset (Finset V)
  /-- Every edge has two vertices. -/
  card_edge : ∀ e ∈ edges, e.card = 2
  /-- Every triangle has three vertices. -/
  card_triangle : ∀ t ∈ triangles, t.card = 3
  /-- Every 2-element face of a triangle is an edge. -/
  face_mem : ∀ t ∈ triangles, ∀ e ⊆ t, e.card = 2 → e ∈ edges

/-- The complete 2-complex: every pair is an edge and every triple a triangle. -/
def complete (V : Type*) [Fintype V] [DecidableEq V] : TwoComplex V where
  edges := univ.powersetCard 2
  triangles := univ.powersetCard 3
  card_edge _ he := (Finset.mem_powersetCard.mp he).2
  card_triangle _ ht := (Finset.mem_powersetCard.mp ht).2
  face_mem _ _ _ _ hc := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : Type*} [Group G]

/-- A `G`-valued 1-cochain: a value on each oriented edge, inverted by reversing it. -/
structure Cochain (X : TwoComplex V) (G : Type*) [Group G] where
  /-- The value on the oriented edge `(u, v)`. -/
  toFun : V → V → G
  /-- Reversing an edge inverts the value. -/
  inv_symm : ∀ u v, ({u, v} : Finset V) ∈ X.edges → toFun v u = (toFun u v)⁻¹

namespace Cochain

variable {X : TwoComplex V}

/-- The triangle defect `N`: the norm of the holonomy `α u v * α v w * α w u`, summed over the
triangles, each read in increasing order `u < v < w`. -/
def defect (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V × V =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
    ℓ (α.toFun p.1 p.2.1 * α.toFun p.2.1 p.2.2 * α.toFun p.2.2 p.1)

/-- The cost of a gauge `β`: the norm of `β u⁻¹ * α u v * β v`, summed over edges `u < v`. -/
def cost (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    ℓ ((β p.1)⁻¹ * α.toFun p.1 p.2 * β p.2)

/-- The gauge distance `D`: the infimum of the cost over all gauges. -/
def gaugeDist (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ⨅ β : V → G, α.cost ℓ β

end Cochain

/-- The first coboundary Cheeger constant in the counting convention: the infimum of `N / D`
over cochains at positive gauge distance. -/
def h1 (X : TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  sInf {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ}

/-- The Cheeger constant in the normalized convention: `h1` rescaled by the ratio of the number
of edges to the number of triangles. With Lean's `x / 0 = 0` this is `0` when `X` has no
triangle; the theorems use it only for `card V ≥ 3`. -/
def h1Norm (X : TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  (X.edges.card / X.triangles.card : ℝ) * h1 X ℓ

end TauCeti.CoboundaryExpansion
