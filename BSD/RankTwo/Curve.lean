import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! # The rational elliptic curve 389.a1 -/

namespace BSD.RankTwo

def model (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨0, 1, 1, -2, 0⟩

abbrev curve := model ℚ

theorem discriminant {R : Type*} [CommRing R] : (model R).Δ = 389 := by
  simp only [model, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

instance : curve.IsElliptic := by
  constructor
  rw [discriminant]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

theorem equation_iff {R : Type*} [CommRing R] (x y : R) :
    (model R).toAffine.Equation x y ↔ y ^ 2 + y = x ^ 3 + x ^ 2 - 2*x := by
  simp [model, WeierstrassCurve.Affine.equation_iff, sub_eq_add_neg]

/-- The points used in the two-descent lower bound. -/
def P : curve.toAffine.Point := .mk ((equation_iff 0 0).mpr (by norm_num))
def Q : curve.toAffine.Point := .mk ((equation_iff (-1) 1).mpr (by norm_num))
def S : curve.toAffine.Point := .mk ((equation_iff 1 0).mpr (by norm_num))

theorem P_add_Q : P + Q = S := by
  unfold P Q S WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num : (0 : ℚ) ≠ -1)]
  apply (WeierstrassCurve.Affine.Point.some.injEq ..).mpr
  norm_num [curve, model, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]

end BSD.RankTwo
