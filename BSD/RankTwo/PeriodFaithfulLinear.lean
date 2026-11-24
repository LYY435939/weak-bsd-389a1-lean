import BSD.General.PeriodsCusp

/-! Additivity of the canonical cusp period in the cusp form. -/

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint UpperHalfPlane
open BSD.General.PeriodsRational BSD.General.PeriodsRelative
open scoped MatrixGroups Topology ModularForm CongruenceSubgroup

namespace BSD.RankTwo.PeriodFaithfulLinear

noncomputable section

/-- The primitives normalized at infinity are additive on the upper half-plane. -/
theorem primitive_add {N : ℕ} [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (τ : ℍ) :
    BSD.General.Periods.primitive (f + g) τ =
      BSD.General.Periods.primitive f τ + BSD.General.Periods.primitive g τ := by
  let P := BSD.General.Periods.primitive (f + g)
  let Q : ℂ → ℂ := BSD.General.Periods.primitive f + BSD.General.Periods.primitive g
  let F : ℂ → ℂ := fun z => (f + g) (ofComplex z)
  have hP : ∀ z : ℂ, 0 < z.im → HasDerivAt P (F z) z := by
    intro z hz
    simpa [P, F, ofComplex_apply_of_im_pos hz] using
      (BSD.General.Periods.hasDerivAt_primitive (f + g) hz)
  have hQ : ∀ z : ℂ, 0 < z.im → HasDerivAt Q (F z) z := by
    intro z hz
    have hf := BSD.General.Periods.hasDerivAt_primitive f hz
    have hg := BSD.General.Periods.hasDerivAt_primitive g hz
    simpa [Q, F, ofComplex_apply_of_im_pos hz] using hf.add hg
  obtain ⟨c, hc⟩ := BSD.General.PeriodsLimit.primitives_differ_by_constant P Q F hP hQ
  have hQlim : Tendsto (fun z : ℍ => Q z) atImInfty (𝓝 0) := by
    simpa [Q] using (BSD.General.Periods.tendsto_primitive_atImInfty f).add
      (BSD.General.Periods.tendsto_primitive_atImInfty g)
  have hPlim : Tendsto (fun z : ℍ => P z) atImInfty (𝓝 c) := by
    have h := hQlim.add (tendsto_const_nhds : Tendsto (fun _ : ℍ => c) atImInfty (𝓝 c))
    have h' : Tendsto (fun z : ℍ => Q z + c) atImInfty (𝓝 c) := by simpa using h
    apply h'.congr'
    filter_upwards with z
    exact (hc z z.im_pos).symm
  have hc0 : c = 0 := tendsto_nhds_unique hPlim
    (BSD.General.Periods.tendsto_primitive_atImInfty (f + g))
  have h := hc τ τ.im_pos
  simpa [P, Q, hc0] using h

/-- Periods are additive in the cusp form, with arbitrary rational endpoints. -/
theorem cuspFormPeriod_add_forms {N : ℕ} [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a b : OnePoint ℚ) :
    cuspFormPeriod (f + g) a b = cuspFormPeriod f a b + cuspFormPeriod g a b := by
  have hvalue (x : OnePoint ℚ) :
      cuspValue (BSD.General.Periods.primitive (f + g)) (primitive_has_rational_limits (f + g)) x =
      cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) x +
      cuspValue (BSD.General.Periods.primitive g) (primitive_has_rational_limits g) x := by
    have hsum := (tendsto_rep (BSD.General.Periods.primitive f)
      (primitive_has_rational_limits f) x).add
      (tendsto_rep (BSD.General.Periods.primitive g) (primitive_has_rational_limits g) x)
    have hsum' := hsum.congr' (show (fun z : ℍ =>
      BSD.General.Periods.primitive f ((mapGL ℝ (rep x) • z : ℍ) : ℂ) +
      BSD.General.Periods.primitive g ((mapGL ℝ (rep x) • z : ℍ) : ℂ)) =ᶠ[atImInfty]
      (fun z : ℍ => BSD.General.Periods.primitive (f + g)
        ((mapGL ℝ (rep x) • z : ℍ) : ℂ)) from by
        filter_upwards with z
        exact (primitive_add f g (mapGL ℝ (rep x) • z)).symm)
    exact tendsto_nhds_unique (tendsto_rep _ (primitive_has_rational_limits (f + g)) x) hsum'
  simp only [cuspFormPeriod, relativePeriod, hvalue]
  abel

end
end BSD.RankTwo.PeriodFaithfulLinear
