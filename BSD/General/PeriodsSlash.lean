import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! The weight-two slash action is the differential pullback by a positive
real Möbius transformation. No modularity or existence of a primitive is
assumed in this local identity. -/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace BSD.General

/-- A primitive pulled back by a positive-determinant Möbius transformation
has derivative given by the weight-two slash of its derivative. -/
theorem hasDerivAt_primitive_comp_smul
    (f : ℍ → ℂ) (P : ℂ → ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) (τ : ℍ)
    (hP : HasDerivAt P (f (g • τ)) (g • τ : ℍ)) :
    HasDerivAt (fun z : ℂ => P (g • ofComplex z : ℍ))
      ((f ∣[(2 : ℤ)] g) τ) τ := by
  have hP' : HasDerivAt P (f (g • τ))
      ((fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) τ) := by
    simpa only [ofComplex_apply] using hP
  have h := hP'.comp (τ : ℂ) (UpperHalfPlane.hasStrictDerivAt_smul hg τ).hasDerivAt
  have hcalc : (f ∣[(2 : ℤ)] g) τ =
      f (g • τ) * (((g.val.det : ℝ) : ℂ) / denom g τ ^ 2) := by
    simp [ModularForm.slash_apply, UpperHalfPlane.σ, hg, abs_of_pos hg,
      div_eq_mul_inv, zpow_neg, mul_assoc]
  simpa only [Function.comp_def, ← hcalc] using h


end BSD.General
