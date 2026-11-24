import BSD.General.PeriodsRelative
import BSD.General.PeriodsLimit
import BSD.General.PeriodsPrimitive
import BSD.General.PeriodsSlash

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint UpperHalfPlane
open scoped MatrixGroups Topology ModularForm CongruenceSubgroup

namespace BSD.General.PeriodsRelative
open BSD.General.PeriodsRational
noncomputable section

/-- The normalized primitive has a finite limit at each rational cusp. -/
theorem primitive_has_rational_limits {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∀ c : OnePoint ℚ, ∃ L : ℂ,
      Tendsto (fun z : ℍ ↦ BSD.General.Periods.primitive f ((mapGL ℝ (rep c) • z : ℍ) : ℂ))
        atImInfty (𝓝 L) := by
  intro c
  let δ := rep c
  obtain ⟨G, hG, hGlim⟩ := BSD.General.Periods.exists_normalized_primitive_slash f δ
  let A : GL (Fin 2) ℝ := mapGL ℝ δ
  have hA : 0 < A.val.det := by
    change 0 < (mapGL ℝ δ).val.det
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
    norm_num
  let P : ℂ → ℂ := fun z ↦ BSD.General.Periods.primitive f (A • ofComplex z : ℍ)
  let Q : ℂ → ℂ := G ∘ ofComplex
  let F : ℂ → ℂ := fun z ↦ ((f : ℍ → ℂ) ∣[(2 : ℤ)] δ) (ofComplex z)
  have hP : ∀ z : ℂ, 0 < z.im → HasDerivAt P (F z) z := by
    intro z hz
    let τ : ℍ := ⟨z, hz⟩
    have h := BSD.General.hasDerivAt_primitive_comp_smul (f : ℍ → ℂ)
      (BSD.General.Periods.primitive f) A hA τ
      (BSD.General.Periods.hasDerivAt_primitive f (UpperHalfPlane.im_pos (A • τ)))
    simpa [P, F, A, τ, ofComplex_apply_of_im_pos hz, ModularForm.SL_slash, SpecialLinearGroup.mapGL, algebraMap_int_eq] using h
  have hQ : ∀ z : ℂ, 0 < z.im → HasDerivAt Q (F z) z := by
    intro z hz
    simpa [Q, F, ofComplex_apply_of_im_pos hz] using hG ⟨z, hz⟩
  have hQL : Tendsto (fun z : ℍ ↦ Q z) atImInfty (𝓝 0) := by
    simpa [Q, Function.comp_def] using hGlim
  obtain ⟨L, hL⟩ := BSD.General.PeriodsLimit.tendsto_primitive_of_tendsto P Q F hP hQ hQL
  exact ⟨L, by simpa [P, A, δ] using hL⟩

/-- The period from a rational cusp to another for the normalized cusp primitive. -/
def cuspFormPeriod {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (a b : OnePoint ℚ) : ℂ :=
  relativePeriod (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) a b

theorem cuspFormPeriod_add {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a b c : OnePoint ℚ) :
    cuspFormPeriod f a b + cuspFormPeriod f b c = cuspFormPeriod f a c :=
  relativePeriod_add _ _ a b c

theorem tendsto_cuspForm_primitive {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (c : OnePoint ℚ)
    (g : GL (Fin 2) ℝ) (hg : cuspInf g = OnePoint.map Rat.cast c) :
    Tendsto (fun z : ℍ ↦ BSD.General.Periods.primitive f ((g • z : ℍ) : ℂ)) atImInfty
      (𝓝 (cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) c)) :=
  tendsto_primitive_cusp _ _ c g hg

end
end BSD.General.PeriodsRelative
