import BSD.RankTwo.Curve
import EllipticCurves.WeakMordellWeil
import EllipticCurves.VariableChange

/-! Completing the square on 389.a1 without changing its rational point group. -/

namespace BSD.RankTwo389

open WeierstrassCurve Polynomial

def shortCurve : WeierstrassCurve ℚ := ⟨0,1,0,-2,1/4⟩

instance : shortCurve.IsCharNeTwoNF := ⟨rfl,rfl⟩

instance : shortCurve.IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  rw [Δ_of_isCharNeTwoNF]
  norm_num [shortCurve]

private def shift : VariableChange ℚ := ⟨1,0,0,-1/2⟩

theorem shortCurve_eq_change : shortCurve = shift • RankTwo.curve := by
  ext <;> norm_num [shortCurve,shift,RankTwo.curve,RankTwo.model,variableChange_a₁, variableChange_a₂,
    variableChange_a₃,variableChange_a₄,variableChange_a₆]

noncomputable def shortCurveEquiv : shortCurve.toAffine.Point ≃+ RankTwo.curve.toAffine.Point :=
  (Affine.Point.equivOfEq shortCurve_eq_change).trans (Affine.Point.equivVariableChange RankTwo.curve shift)

/-- Discriminant of the cubic used by Stoll's x minus T descent. -/
theorem shortCurve_cubic_discr : shortCurve.toAffine.f.discr = 389 / 16 := by
  rw [Affine.discr_f]
  norm_num [shortCurve]

end BSD.RankTwo389
