import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Rational root exclusions for the curve of conductor 389

For the equation `y² + y = x³ + x² - 2x`, the standard Weierstrass
invariants are `b₂ = 4`, `b₄ = -4`, `b₆ = 1`, and `b₈ = -3`.
The doubling formula gives a monic quartic for a point whose double has
prescribed x-coordinate. At x-coordinates 0, -1 and 1 the quartics have
no root modulo 11. The cubic for two-torsion becomes monic after replacing
`x` by `u / 2` and has no root modulo 4.
-/

namespace BSD.RankTwo

open Polynomial

private def halvingValue {R : Type*} [CommRing R] (x t : R) : R :=
  x ^ 4 + 4 * x ^ 2 - 2 * x + 3 - t * (4 * x ^ 3 + 4 * x ^ 2 - 8 * x + 1)

private lemma halvingValue_mod_eleven (x : ZMod 11) :
    halvingValue x 0 ≠ 0 ∧ halvingValue x (-1) ≠ 0 ∧ halvingValue x 1 ≠ 0 :=
  (show ∀ u : ZMod 11, halvingValue u 0 ≠ 0 ∧ halvingValue u (-1) ≠ 0 ∧
    halvingValue u 1 ≠ 0 by decide) x

/-- The doubling quartic has no rational root for the three indicated x-coordinates. -/
theorem halving_polynomial_ne_zero (x t : ℚ) (ht : t = 0 ∨ t = -1 ∨ t = 1) :
    x ^ 4 + 4 * x ^ 2 - 2 * x + 3 - t * (4 * x ^ 3 + 4 * x ^ 2 - 8 * x + 1) ≠ 0 := by
  change halvingValue x t ≠ 0
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, (a = 0 ∨ a = -1 ∨ a = 1) ∧ (a : ℚ) = t := by
    rcases ht with rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr (Or.inl rfl), by simp⟩
    · exact ⟨1, Or.inr (Or.inr rfl), by simp⟩
  let p : ℤ[X] := halvingValue X (C a)
  have hp : p.Monic := by
    unfold p halvingValue
    monicity <;> decide
  intro hx
  have hroot : aeval x p = 0 := by simpa [p, halvingValue, map_ofNat] using hx
  obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hp hroot
  change (n : ℚ) = x at hn
  rw [← hn] at hx
  have hInt : halvingValue n a = 0 := by
    unfold halvingValue at hx ⊢
    exact_mod_cast hx
  have hMod : halvingValue (n : ZMod 11) (a : ZMod 11) = 0 := by
    simpa [halvingValue] using congrArg (Int.castRingHom (ZMod 11)) hInt
  obtain ⟨h0, hneg, hpos⟩ := halvingValue_mod_eleven (n : ZMod 11)
  rcases ha with rfl | rfl | rfl
  · exact h0 (by simpa using hMod)
  · exact hneg (by simpa using hMod)
  · exact hpos (by simpa using hMod)

private def torsionValue {R : Type*} [CommRing R] (u : R) : R :=
  u ^ 3 + 2 * u ^ 2 - 8 * u + 2

/-- The x-coordinate equation of rational affine two-torsion has no solution. -/
theorem two_torsion_polynomial_ne_zero (x : ℚ) :
    4 * x ^ 3 + 4 * x ^ 2 - 8 * x + 1 ≠ 0 := by
  intro h
  let p : ℤ[X] := torsionValue X
  have hp : p.Monic := by
    unfold p torsionValue
    monicity <;> decide
  have hx : torsionValue (2 * x) = 0 := by
    unfold torsionValue
    linear_combination 2 * h
  have hroot : aeval (2 * x) p = 0 := by simpa [p, torsionValue, map_ofNat] using hx
  obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hp hroot
  change (n : ℚ) = 2 * x at hn
  rw [← hn] at hx
  have hInt : torsionValue n = 0 := by
    unfold torsionValue at hx ⊢
    exact_mod_cast hx
  have hMod : torsionValue (n : ZMod 4) = 0 := by
    simpa [torsionValue] using congrArg (Int.castRingHom (ZMod 4)) hInt
  exact (show ∀ u : ZMod 4, torsionValue u ≠ 0 by decide) n hMod

end BSD.RankTwo
