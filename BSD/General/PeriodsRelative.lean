import BSD.General.PeriodsRational

/-! Rational cusp values and oriented relative periods, given convergence at
integral cusp representatives. The existence of those limits is a separate
analytic theorem. -/

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint UpperHalfPlane
open scoped MatrixGroups Topology

namespace BSD.General.PeriodsRelative

open BSD.General.PeriodsRational

noncomputable section

variable (P : ℂ → ℂ)
variable (hRep : ∀ c : OnePoint ℚ, ∃ L : ℂ,
  Tendsto (fun z : ℍ ↦ P ((mapGL ℝ (rep c) • z : ℍ) : ℂ)) atImInfty (𝓝 L))

/-- The value approached by a primitive at a rational cusp. -/
def cuspValue (c : OnePoint ℚ) : ℂ := Classical.choose (hRep c)

theorem tendsto_rep (c : OnePoint ℚ) :
    Tendsto (fun z : ℍ ↦ P ((mapGL ℝ (rep c) • z : ℍ) : ℂ)) atImInfty
      (𝓝 (cuspValue P hRep c)) := Classical.choose_spec (hRep c)

/-- The oriented period from `a` to `b`. -/
def relativePeriod (a b : OnePoint ℚ) : ℂ := cuspValue P hRep b - cuspValue P hRep a

theorem relativePeriod_add (a b c : OnePoint ℚ) :
    relativePeriod P hRep a b + relativePeriod P hRep b c = relativePeriod P hRep a c := by
  simp only [relativePeriod]
  abel

/-- The value is independent of the real matrix used to approach the cusp. -/
theorem tendsto_primitive_cusp (c : OnePoint ℚ) (g : GL (Fin 2) ℝ)
    (hg : cuspInf g = OnePoint.map Rat.cast c) :
    Tendsto (fun z : ℍ ↦ P ((g • z : ℍ) : ℂ)) atImInfty (𝓝 (cuspValue P hRep c)) := by
  have hfix : cuspInf ((mapGL ℝ (rep c))⁻¹ * g) = ∞ :=
    (cuspInf_eq_iff _ _).mp ((rep_spec c).trans hg.symm)
  have ht := (tendsto_rep P hRep c).comp (tendsto_atImInfty_of_cuspInf_eq_infty hfix)
  simpa only [Function.comp_def, ← mul_smul, mul_inv_cancel_left] using ht


end
end BSD.General.PeriodsRelative
