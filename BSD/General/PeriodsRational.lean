import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Rational cusp representatives

The rational projective line is represented by `OnePoint ℚ`, as in the
Farey symbol implementation. The corresponding real cusp is its image under
`OnePoint.map Rat.cast`. Representatives exist by the transitivity theorem for
`SL₂(ℤ)` on `OnePoint ℚ`.
-/

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint
open scoped MatrixGroups

namespace BSD.General.PeriodsRational

/-- The real projective point obtained by acting on infinity. -/
noncomputable def cuspInf (g : GL (Fin 2) ℝ) : OnePoint ℝ := g • ∞

/-- A chosen integral determinant-one representative of a rational cusp. -/
noncomputable def rep (c : OnePoint ℚ) : SL(2, ℤ) :=
  Classical.choose (c.exists_mem_SL2 ℤ)

/-- The chosen representative has the prescribed rational endpoint. -/
theorem rep_spec_rat (c : OnePoint ℚ) :
    mapGL ℚ (rep c) • ∞ = c :=
  Classical.choose_spec (c.exists_mem_SL2 ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The same representative has the corresponding real endpoint. -/
theorem rep_spec (c : OnePoint ℚ) :
    cuspInf (mapGL ℝ (rep c)) = OnePoint.map Rat.cast c := by
  have h := congrArg (OnePoint.map (Rat.cast : ℚ → ℝ)) (rep_spec_rat c)
  rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
    ← (Rat.castHom ℝ).algebraMap_toAlgebra, (rep c).map_mapGL] at h
  exact h

/-- Fixing infinity is exactly the upper-triangular condition. -/
theorem cuspInf_eq_infty_iff (g : GL (Fin 2) ℝ) :
    cuspInf g = ∞ ↔ g 1 0 = 0 :=
  smul_infty_eq_self_iff

/-- Every real invertible matrix fixing infinity carries the imaginary-infinity
filter into itself. This also covers matrices of positive determinant. -/
theorem tendsto_atImInfty_of_cuspInf_eq_infty {g : GL (Fin 2) ℝ}
    (hg : cuspInf g = ∞) :
    Tendsto (fun z : UpperHalfPlane ↦ g • z) UpperHalfPlane.atImInfty
      UpperHalfPlane.atImInfty :=
  UpperHalfPlane.tendsto_smul_atImInfty ((cuspInf_eq_infty_iff g).mp hg)

/-- Two matrices have the same endpoint exactly when their relative matrix
fixes infinity. -/
theorem cuspInf_eq_iff (g h : GL (Fin 2) ℝ) :
    cuspInf g = cuspInf h ↔ cuspInf (g⁻¹ * h) = ∞ := by
  simp only [cuspInf, mul_smul]
  constructor
  · intro heq
    rw [← heq, ← mul_smul, inv_mul_cancel, one_smul]
  · intro heq
    have := congrArg (fun x : OnePoint ℝ ↦ g • x) heq
    simpa [← mul_smul] using this.symm

end BSD.General.PeriodsRational
