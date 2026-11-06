/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Constant
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionEight
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionSeven
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.ExhaustionSix

/-!
# `h₁(K_k) = k/3` for `k = 5, …, 8` from the explicit witnesses

The finite certificates of Theorem 4 and Appendix A of Beasley (DOI 10.5281/zenodo.22090958):
the witnesses `w5`, …, `w8` of `Sym3.Basic`, with the exhaustions of `Sym3.ExhaustionSix`,
`Sym3.ExhaustionSeven` and `Sym3.ExhaustionEight`, give their gauge distances and the upper
bounds `h₁(K_k) ≤ k/3`; the star bound of `Sym3.Constant` gives equality.

This is the only file of the development that imports the exhaustions. The general theorem
`h₁(K_k) = k/3` for every `k ≥ 3` (`Sym3.Staircase`) does not depend on it.
-/

public section

namespace TauCeti.CoboundaryExpansion.Sym3

/-- The `k = 5` witness has gauge distance exactly `6`. -/
theorem gaugeDist_w5 : gaugeDist w5 = 6 := gaugeDist_eq_of witness_k5.2.1 _ witness_k5.2.2.1

/-- The `k = 6` witness has gauge distance exactly `18`. -/
theorem gaugeDist_w6 : gaugeDist w6 = 18 := gaugeDist_eq_of witness_k6.2.1 _ witness_k6.2.2.1

/-- The `k = 7` witness has gauge distance exactly `12`. -/
theorem gaugeDist_w7 : gaugeDist w7 = 12 := gaugeDist_eq_of witness_k7.2.1 _ witness_k7.2.2.1

/-- The `k = 8` witness has gauge distance exactly `27`. -/
theorem gaugeDist_w8 : gaugeDist w8 = 27 := gaugeDist_eq_of witness_k8.2.1 _ witness_k8.2.2.1

/-- **Theorem 4, upper half, k = 5.** `h₁(K_5) ≤ 5/3`, from the witness `w5` (`N = 10`,
`D = 6`). -/
theorem h1_le_k5 : h1 5 ≤ 5 / 3 := by
  have h := h1_le_of_pos (α := w5) (by rw [gaugeDist_w5]; norm_num)
  rw [gaugeDist_w5, witness_k5.1] at h
  calc h1 5 ≤ ((10 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) := h
    _ = 5 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 6.** `h₁(K_6) ≤ 6/3`, from the witness `w6` (`N = 36`,
`D = 18`). -/
theorem h1_le_k6 : h1 6 ≤ 6 / 3 := by
  have h := h1_le_of_pos (α := w6) (by rw [gaugeDist_w6]; norm_num)
  rw [gaugeDist_w6, witness_k6.1] at h
  calc h1 6 ≤ ((36 : ℕ) : ℝ) / ((18 : ℕ) : ℝ) := h
    _ = 6 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 7.** `h₁(K_7) ≤ 7/3`, from the witness `w7` (`N = 28`,
`D = 12`). -/
theorem h1_le_k7 : h1 7 ≤ 7 / 3 := by
  have h := h1_le_of_pos (α := w7) (by rw [gaugeDist_w7]; norm_num)
  rw [gaugeDist_w7, witness_k7.1] at h
  calc h1 7 ≤ ((28 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) := h
    _ = 7 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 8.** `h₁(K_8) ≤ 8/3`, from the witness `w8` (`N = 72`,
`D = 27`). -/
theorem h1_le_k8 : h1 8 ≤ 8 / 3 := by
  have h := h1_le_of_pos (α := w8) (by rw [gaugeDist_w8]; norm_num)
  rw [gaugeDist_w8, witness_k8.1] at h
  calc h1 8 ≤ ((72 : ℕ) : ℝ) / ((27 : ℕ) : ℝ) := h
    _ = 8 / 3 := by norm_num

/-- **Theorem 4, k = 5.** `h₁(K_5) = 5/3`. -/
theorem h1_eq_k5 : h1 5 = 5 / 3 := by
  apply le_antisymm h1_le_k5
  have h := k_div_three_le_h1 (k := 5) ⟨w5, by rw [gaugeDist_w5]; norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 6.** `h₁(K_6) = 6/3 = 2`. -/
theorem h1_eq_k6 : h1 6 = 6 / 3 := by
  apply le_antisymm h1_le_k6
  have h := k_div_three_le_h1 (k := 6) ⟨w6, by rw [gaugeDist_w6]; norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 7.** `h₁(K_7) = 7/3`. -/
theorem h1_eq_k7 : h1 7 = 7 / 3 := by
  apply le_antisymm h1_le_k7
  have h := k_div_three_le_h1 (k := 7) ⟨w7, by rw [gaugeDist_w7]; norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 8.** `h₁(K_8) = 8/3`. -/
theorem h1_eq_k8 : h1 8 = 8 / 3 := by
  apply le_antisymm h1_le_k8
  have h := k_div_three_le_h1 (k := 8) ⟨w8, by rw [gaugeDist_w8]; norm_num⟩
  exact_mod_cast h

/-! ### README 6.3 check: every star gauge of a witness costs exactly its gauge distance -/

/-- The `k` star gauges of `w5` each cost `6`. -/
theorem cost_starGauge_w5 : ∀ x, cost w5 (starGauge w5 x) = 6 := by decide +kernel

/-- The `k` star gauges of `w6` each cost `18`. -/
theorem cost_starGauge_w6 : ∀ x, cost w6 (starGauge w6 x) = 18 := by decide +kernel

/-- The `k` star gauges of `w7` each cost `12`. -/
theorem cost_starGauge_w7 : ∀ x, cost w7 (starGauge w7 x) = 12 := by decide +kernel

/-- The `k` star gauges of `w8` each cost `27`. -/
theorem cost_starGauge_w8 : ∀ x, cost w8 (starGauge w8 x) = 27 := by decide +kernel

/-- **Theorem 4.** `h₁(K_k) = k/3` for `k = 4, 5, 6, 7, 8`. -/
theorem h1_eq_k_div_three : ∀ k ∈ ({4, 5, 6, 7, 8} : Finset ℕ), h1 k = (k : ℝ) / 3 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · rw [h1_eq_k4]; norm_num
  · rw [h1_eq_k5]; norm_num
  · rw [h1_eq_k6]; norm_num
  · rw [h1_eq_k7]; norm_num
  · rw [h1_eq_k8]; norm_num

end TauCeti.CoboundaryExpansion.Sym3
