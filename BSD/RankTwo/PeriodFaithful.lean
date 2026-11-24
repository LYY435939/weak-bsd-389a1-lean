import BSD.RankTwo.PeriodFaithfulCocycle
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! Conditional on the cocycle computation, vanishing rational periods force the
normalized primitive to be a weight-zero modular form and hence vanish. -/

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint UpperHalfPlane
open BSD.General.PeriodsRational BSD.General.PeriodsRelative
open BSD.RankTwo.PeriodFaithfulCocycle
open scoped MatrixGroups Topology ModularForm CongruenceSubgroup Manifold

namespace BSD.RankTwo.PeriodFaithful

noncomputable section

theorem cuspValue_eq_zero {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hzero : ∀ a b, cuspFormPeriod f a b = 0) (c : OnePoint ℚ) :
    cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) c = 0 := by
  have ht : cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) ∞ = 0 := by
    apply tendsto_nhds_unique (tendsto_cuspForm_primitive f ∞ 1 (by simp [cuspInf]))
    simpa using BSD.General.Periods.tendsto_primitive_atImInfty f
  have h := hzero ∞ c
  change cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) c -
    cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f) ∞ = 0 at h
  simpa [ht] using h

set_option backward.isDefEq.respectTransparency false in
/-- Every rational period vanishes only for the zero cusp form. -/
theorem eq_zero_of_periods_zero {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hzero : ∀ a b, cuspFormPeriod f a b = 0) : f = 0 := by
  let P : ℍ → ℂ := fun z => BSD.General.Periods.primitive f z
  have hΓ : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N := fun _ hA =>
    CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hA).2.2.1
  have : (CongruenceSubgroup.Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  let E : ModularForm (CongruenceSubgroup.Gamma0 N) 0 := {
    toFun := P
    slash_action_eq' := by
      rintro γ ⟨g, hg, rfl⟩
      funext τ
      have hi := primitive_invariant_of_periods_zero f (fun g hg => hzero ∞ _) g hg τ
      change ((P ∣[(0 : ℤ)] g) τ) = P τ
      rw [ModularForm.SL_slash_apply]
      simp only [neg_zero, zpow_zero, mul_one]
      change P ((mapGL ℝ g) • τ) = P τ
      exact hi
    holo' := by
      intro τ
      apply UpperHalfPlane.mdifferentiableAt_iff.mpr
      have h := (BSD.General.Periods.hasDerivAt_primitive f τ.im_pos).differentiableAt
      apply h.congr_of_eventuallyEq
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      simp [P, ofComplex_apply_of_im_pos hz]
    bdd_at_cusps' := by
      intro c hc
      have hc' := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
      obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp hc'
      apply (OnePoint.isBoundedAt_iff_exists_SL2Z hc').mpr
      refine ⟨g, hg.symm, ?_⟩
      have hlim := tendsto_cuspForm_primitive f (mapGL ℚ g • ∞) (mapGL ℝ g) (by
        have h := congrArg (OnePoint.map (Rat.cast : ℚ → ℝ))
          (show mapGL ℚ g • ∞ = mapGL ℚ g • ∞ from rfl)
        conv at h =>
          lhs
          rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
            ← (Rat.castHom ℝ).algebraMap_toAlgebra, g.map_mapGL]
        exact h)
      rw [cuspValue_eq_zero f hzero] at hlim
      have hs : (P ∣[(0 : ℤ)] g) = (fun z : ℍ => P (mapGL ℝ g • z)) := by
        funext z
        rw [ModularForm.SL_slash_apply]
        simp only [neg_zero, zpow_zero, mul_one]
        change P ((mapGL ℝ g) • z) = P ((mapGL ℝ g) • z)
        rfl
      have hz : IsZeroAtImInfty (P ∣[(0 : ℤ)] g) := by
        rw [hs]
        exact hlim
      exact hz.boundedAtFilter }
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero E
  have htop : Tendsto (fun z : ℍ => E z) atImInfty (𝓝 0) := by
    change Tendsto (fun z : ℍ => BSD.General.Periods.primitive f z) atImInfty (𝓝 0)
    exact BSD.General.Periods.tendsto_primitive_atImInfty f
  have hc0 : c = 0 := by simpa [hc] using htop
  have hP : ∀ τ : ℍ, BSD.General.Periods.primitive f τ = 0 := by
    intro τ
    have h := congrFun hc τ
    simp only [Function.const_apply, hc0] at h
    change BSD.General.Periods.primitive f τ = 0 at h
    exact h
  apply DFunLike.coe_injective
  funext τ
  have hd := BSD.General.Periods.hasDerivAt_primitive f τ.im_pos
  have hz : BSD.General.Periods.primitive f =ᶠ[𝓝 (τ : ℂ)] (fun _ => 0) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    exact hP ⟨z, hz⟩
  have := hd.congr_of_eventuallyEq hz.symm
  simpa using this.unique (hasDerivAt_const (τ : ℂ) (0 : ℂ))

end
end BSD.RankTwo.PeriodFaithful
