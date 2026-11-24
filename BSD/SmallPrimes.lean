import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! # The integral model at 2 and 3

These finite-field calculations do not assert local minimality, a Kodaira type,
or a conductor exponent over a p-adic field.
-/

namespace BSD.FermatCubic

/-- The integral Weierstrass model `y² + y = x³ - 7`. -/
def integralModel (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, -7⟩

lemma integral_equation_iff {R : Type*} [CommRing R] (x y : R) :
    (integralModel R).toAffine.Equation x y ↔ y ^ 2 + y = x ^ 3 - 7 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [integralModel, sub_eq_add_neg]

lemma integral_discriminant {R : Type*} [CommRing R] :
    (integralModel R).Δ = -(19683 : R) := by
  simp only [integralModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The forward coordinate change and its converse over the rationals. -/
theorem change_coordinates (x y : ℚ) :
    y ^ 2 + y = x ^ 3 - 7 ↔ (8 * y + 4) ^ 2 = (4 * x) ^ 3 - 432 := by
  constructor <;> intro h <;> nlinarith [h]

theorem inverse_change_coordinates (X Y : ℚ) :
    Y ^ 2 = X ^ 3 - 432 ↔
      ((Y - 4) / 8) ^ 2 + (Y - 4) / 8 = (X / 4) ^ 3 - 7 := by
  constructor <;> intro h <;> nlinarith [h]

instance integralModel_mod2_elliptic : (integralModel (ZMod 2)).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  rw [integral_discriminant]
  decide

/-- Direct finite enumeration of the affine solutions in characteristic 2. -/
theorem integral_mod2_affine_count :
    Fintype.card {xy : ZMod 2 × ZMod 2 // xy.2 ^ 2 + xy.2 = xy.1 ^ 3 - 7} = 2 := by
  decide

theorem integral_mod2_point_count :
    Nat.card (integralModel (ZMod 2)).toAffine.Point = 3 := by
  have hPred :
      (fun xy : ZMod 2 × ZMod 2 => (integralModel (ZMod 2)).toAffine.Equation xy.1 xy.2) =
      (fun xy : ZMod 2 × ZMod 2 => xy.2 ^ 2 + xy.2 = xy.1 ^ 3 - 7) := by
    funext xy
    exact propext (integral_equation_iff xy.1 xy.2)
  let e := (integralModel (ZMod 2)).toAffine.pointEquiv.trans
    (Equiv.subtypeEquivProp hPred).optionCongr
  rw [Nat.card_congr e, Finite.card_option, Nat.card_eq_fintype_card,
    integral_mod2_affine_count]

theorem integral_mod2_trace :
    (2 : ℤ) + 1 - Nat.card (integralModel (ZMod 2)).toAffine.Point = 0 := by
  rw [integral_mod2_point_count]
  norm_num

/-- In characteristic 3 the affine point `(0,1)` is singular. -/
theorem integral_mod3_singular :
    (integralModel (ZMod 3)).toAffine.Equation 0 1 ∧
      ¬ (integralModel (ZMod 3)).toAffine.Nonsingular 0 1 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  simp only [integral_equation_iff]
  change (1 ^ 2 + 1 = (0 : ZMod 3) ^ 3 - 7) ∧
    ¬ ((1 ^ 2 + 1 = (0 : ZMod 3) ^ 3 - 7) ∧
       ((0 : ZMod 3) * 1 ≠ 3 * 0 ^ 2 + 2 * 0 * 0 + 0 ∨ 1 ≠ -1 - 0 * 0 - 1))
  decide

/-- Translation of the singular point to the origin gives the cusp `v² = u³`. -/
theorem integral_mod3_cusp (u v : ZMod 3) :
    (integralModel (ZMod 3)).toAffine.Equation u (v + 1) ↔ v ^ 2 = u ^ 3 := by
  rw [integral_equation_iff]
  fin_cases u <;> fin_cases v <;> decide

end BSD.FermatCubic
