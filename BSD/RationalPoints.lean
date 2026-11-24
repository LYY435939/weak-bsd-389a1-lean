import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

/-! # The Mordell–Weil rank of the Fermat cubic

We use the model y² = x³ − 432 of 27.a3. The identity below sends each
rational affine point to a solution of a³ + b³ = c³. The exponent-three
case of Fermat's last theorem determines all the rational points.
-/

namespace BSD.FermatCubic

/-- The same integral equation over any coefficient ring. -/
def model (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨0, 0, 0, 0, -432⟩

abbrev curve := model ℚ

instance : curve.IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  norm_num [curve, model, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem equation_iff (x y : ℚ) :
    curve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - 432 := by
  simp [WeierstrassCurve.Affine.equation_iff, curve, model, sub_eq_add_neg]

/-- A complete classification of the rational affine solutions. -/
theorem affine_coordinates {x y : ℚ} (h : y ^ 2 = x ^ 3 - 432) :
    x = 12 ∧ (y = 36 ∨ y = -36) := by
  have hx : x ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg y]
  have hcubes : (36 + y) ^ 3 + (36 - y) ^ 3 = (6 * x) ^ 3 := by
    linear_combination 216 * h
  have hy : y = 36 ∨ y = -36 := by
    by_contra! hother
    exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree)
      (36 + y) (36 - y) (6 * x) (by intro hz; apply hother.2; linarith)
      (by intro hz; apply hother.1; linarith) (mul_ne_zero (by norm_num) hx) hcubes
  refine ⟨Odd.pow_injective (n := 3) (by decide) ?_, hy⟩
  rcases hy with rfl | rfl <;> linarith

def positivePoint : curve.toAffine.Point :=
  .mk ((equation_iff 12 36).mpr (by norm_num))

def negativePoint : curve.toAffine.Point :=
  .mk ((equation_iff 12 (-36)).mpr (by norm_num))

theorem rational_points (P : curve.toAffine.Point) :
    P = .zero ∨ P = positivePoint ∨ P = negativePoint := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    obtain ⟨rfl, rfl | rfl⟩ := affine_coordinates ((equation_iff x y).mp h.1)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The point at infinity and two distinct affine points exhaust the group. -/
def pointEquiv : curve.toAffine.Point ≃ Option Bool where
  toFun
    | .zero => none
    | .some _ y _ => some (decide (y = 36))
  invFun
    | none => .zero
    | some true => positivePoint
    | some false => negativePoint
  left_inv P := by
    rcases rational_points P with rfl | rfl | rfl <;> rfl
  right_inv a := by
    rcases a with _ | (_ | _) <;> rfl

theorem rational_point_count : Nat.card curve.toAffine.Point = 3 := by
  rw [Nat.card_congr pointEquiv, Nat.card_eq_fintype_card]
  decide

/-- The algebraic side of the BSD rank equality for 27.a3. -/
theorem algebraic_rank_zero : Module.finrank ℤ curve.toAffine.Point = 0 := by
  let : Finite curve.toAffine.Point := Finite.of_equiv _ pointEquiv.symm
  exact (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite).finrank_eq_zero

end BSD.FermatCubic
