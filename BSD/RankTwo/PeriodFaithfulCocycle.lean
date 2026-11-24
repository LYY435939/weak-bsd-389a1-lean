import BSD.General.PeriodsCusp

/-! The automorphy cocycle of the normalized primitive is its cusp period. -/

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint UpperHalfPlane
open BSD.General.PeriodsRational BSD.General.PeriodsRelative
open scoped MatrixGroups Topology ModularForm CongruenceSubgroup

namespace BSD.RankTwo.PeriodFaithfulCocycle

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The displacement of a weight-two primitive under a congruence element is
its oriented period from infinity to the image of infinity. -/
theorem primitive_smul_sub_eq_period {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    BSD.General.Periods.primitive f ((mapGL ℝ g • τ : ℍ) : ℂ) -
      BSD.General.Periods.primitive f τ =
    cuspFormPeriod f ∞ (mapGL ℚ g • ∞) := by
  let A : GL (Fin 2) ℝ := mapGL ℝ g
  let P := BSD.General.Periods.primitive f
  let Q : ℂ → ℂ := fun z => P (A • ofComplex z : ℍ)
  let F : ℂ → ℂ := fun z => f (ofComplex z)
  have hA : 0 < A.val.det := by
    change 0 < (mapGL ℝ g).val.det
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
    norm_num
  have hslash : ∀ z : ℍ, ((f : ℍ → ℂ) ∣[(2 : ℤ)] A) z = f z := by
    intro z
    exact congrFun (SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)) z
  have hQ : ∀ z : ℂ, 0 < z.im → HasDerivAt Q (F z) z := by
    intro z hz
    let w : ℍ := ⟨z, hz⟩
    have h := BSD.General.hasDerivAt_primitive_comp_smul (f : ℍ → ℂ) P A hA w
      (BSD.General.Periods.hasDerivAt_primitive f (UpperHalfPlane.im_pos (A • w)))
    rw [hslash w] at h
    simpa [Q, F, w, ofComplex_apply_of_im_pos hz] using h
  have hP : ∀ z : ℂ, 0 < z.im → HasDerivAt P (F z) z := by
    intro z hz
    simpa [P, F, ofComplex_apply_of_im_pos hz] using
      (BSD.General.Periods.hasDerivAt_primitive f hz)
  obtain ⟨c, hc⟩ := BSD.General.PeriodsLimit.primitives_differ_by_constant Q P F hQ hP
  have hend : cuspInf A = OnePoint.map Rat.cast (mapGL ℚ g • ∞) := by
    have h := congrArg (OnePoint.map (Rat.cast : ℚ → ℝ))
      (show mapGL ℚ g • ∞ = mapGL ℚ g • ∞ from rfl)
    conv at h =>
      lhs
      rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
        ← (Rat.castHom ℝ).algebraMap_toAlgebra, g.map_mapGL]
    exact h
  have hlim := tendsto_cuspForm_primitive f (mapGL ℚ g • ∞) A hend
  have htop := BSD.General.Periods.tendsto_primitive_atImInfty f
  have hc_lim : Tendsto (fun z : ℍ => P z + c) atImInfty (𝓝 c) := by
    simpa using htop.add tendsto_const_nhds
  have heq : cuspValue P (primitive_has_rational_limits f) (mapGL ℚ g • ∞) = c := by
    apply tendsto_nhds_unique hlim
    apply hc_lim.congr'
    filter_upwards with z
    simpa [Q] using (hc z z.im_pos).symm
  have hinfty : cuspValue P (primitive_has_rational_limits f) ∞ = 0 := by
    apply tendsto_nhds_unique (tendsto_cuspForm_primitive f ∞ 1 (by simp [cuspInf]))
    simpa [P] using htop
  have hτ : P (A • τ : ℍ) = P τ + c := by
    simpa only [Q, ofComplex_apply] using hc τ τ.im_pos
  change P (A • τ : ℍ) - P τ = relativePeriod P (primitive_has_rational_limits f) ∞ (mapGL ℚ g • ∞)
  rw [relativePeriod, heq, hinfty, sub_zero]
  linear_combination hτ

/-- If the periods from infinity vanish, the primitive is invariant. -/
theorem primitive_invariant_of_periods_zero {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hzero : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N →
      cuspFormPeriod f ∞ (mapGL ℚ g • ∞) = 0)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    BSD.General.Periods.primitive f ((mapGL ℝ g • τ : ℍ) : ℂ) =
      BSD.General.Periods.primitive f τ := by
  apply sub_eq_zero.mp
  rw [primitive_smul_sub_eq_period f g hg τ, hzero g hg]

end
end BSD.RankTwo.PeriodFaithfulCocycle
