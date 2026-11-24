import BSD.RankTwo.IndependentPoints
import EllipticCurves.MordellWeil

/-! # Finite generation of the Mordell–Weil group of 389.a1 -/

namespace BSD.RankTwo

/-- The group of rational points on 389.a1 is finitely generated over the integers. -/
theorem point_module_finite : Module.Finite ℤ curve.toAffine.Point :=
  Module.Finite.iff_addGroup_fg.mpr WeierstrassCurve.Affine.fg_point_of_numberField

/-- The two independent points give a lower bound on the Mordell–Weil rank. -/
theorem two_le_rational_finrank : 2 ≤ Module.finrank ℤ curve.toAffine.Point := by
  let _ := point_module_finite
  have h := two_le_rational_rank
  rw [← Module.finrank_eq_rank ℤ curve.toAffine.Point] at h
  exact_mod_cast h

end BSD.RankTwo
