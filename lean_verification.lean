import Mathlib

/-!
# Distinct distances: Lean verification of the numerical core

The accompanying article proves the geometric input by hand: for every
n >= 3, the vertices of a regular n-gon satisfy the circle-multiplicity
hypothesis and determine exactly n / 2 distinct distances (Nat division).

This file formalizes the remaining logical/arithmetic step. Once such a
counterexample family exists, no fixed c > 0 can make the proposed lower
bound hold for all sufficiently large n.

The geometric input is represented by `DistanceFamily` below, so that the
Lean proof does not hide it inside an axiom with no mathematical interface.
-/

/-- A family of configurations together with its number of distinct distances.

The predicate `admissible n` represents the circle condition from the paper.
The field `regular_family` records the explicit regular-polygon construction:
for every n >= 3 it is admissible and has exactly floor(n/2) distances.
-/
structure DistanceFamily where
  admissible : ℕ → Prop
  count : ℕ → ℕ
  regular_family :
    ∀ n : ℕ, 3 ≤ n → admissible n ∧ count n = n / 2

/-- For c > 0 and n > 0, floor(n/2) is strictly smaller than
    ((1+c)/2) * n. -/
theorem floor_half_lt_improved
    (c : ℝ) (hc : 0 < c) {n : ℕ} (hn : 0 < n) :
    (((n / 2 : ℕ) : ℝ) < ((1 + c) / 2) * (n : ℝ)) := by
  have hnat : (n / 2 : ℕ) * 2 ≤ n := Nat.div_mul_le_self n 2
  have hreal : ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by
    exact_mod_cast hnat
  have hnreal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  nlinarith

/-- No positive constant can eventually dominate the regular-polygon count.

This is the exact contradiction needed after substituting
`count n = n / 2` for the regular n-gon.
-/
theorem no_eventual_positive_improvement :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ((1 + c) / 2) * (n : ℝ) ≤ (((n / 2 : ℕ) : ℝ)) := by
  rintro ⟨c, hc, N, hN⟩
  let n : ℕ := max N 3
  have hn_ge_N : N ≤ n := by
    dsimp [n]
    exact Nat.le_max_left N 3
  have hn_ge_3 : 3 ≤ n := by
    dsimp [n]
    exact Nat.le_max_right N 3
  have hn_pos : 0 < n := by omega
  have hstrict : (((n / 2 : ℕ) : ℝ) < ((1 + c) / 2) * (n : ℝ)) :=
    floor_half_lt_improved c hc hn_pos
  have hbound : ((1 + c) / 2) * (n : ℝ) ≤ (((n / 2 : ℕ) : ℝ)) :=
    hN n hn_ge_N
  linarith

/-- The abstract form of the paper's counterexample argument.

If a family has an admissible regular-polygon realization with exactly
`floor(n/2)` distinct distances for every n >= 3, then the proposed eventual
lower bound is impossible.
-/
theorem regular_family_refutes_improvement (F : DistanceFamily) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ((1 + c) / 2) * (n : ℝ) ≤ (F.count n : ℝ) := by
  rintro ⟨c, hc, N, hN⟩
  let n : ℕ := max N 3
  have hn_ge_N : N ≤ n := by
    dsimp [n]
    exact Nat.le_max_left N 3
  have hn_ge_3 : 3 ≤ n := by
    dsimp [n]
    exact Nat.le_max_right N 3
  have hn_pos : 0 < n := by omega
  obtain ⟨_hadm, hcount⟩ := F.regular_family n hn_ge_3
  have hstrict : (((n / 2 : ℕ) : ℝ) < ((1 + c) / 2) * (n : ℝ)) :=
    floor_half_lt_improved c hc hn_pos
  have hbound : ((1 + c) / 2) * (n : ℝ) ≤ (F.count n : ℝ) :=
    hN n hn_ge_N
  rw [hcount] at hbound
  linarith

/-!
For a fuller formalization of the trigonometric part, Mathlib provides
`Real.strictMonoOn_sin` (and hence injectivity on the interval
[-pi/2, pi/2]). The paper uses exactly this monotonicity to show that the
chord lengths 2 * sin(pi*m/n), 1 <= m <= n/2, are pairwise distinct.
-/
