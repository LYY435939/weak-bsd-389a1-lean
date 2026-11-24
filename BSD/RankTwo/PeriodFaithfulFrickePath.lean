import BSD.General.PeriodsCusp
import BSD.RankTwo.PeriodFaithfulFricke

/-! Pullback of cusp periods under the Fricke transformation. -/

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint UpperHalfPlane
open BSD.General.PeriodsRational BSD.General.PeriodsRelative
open scoped MatrixGroups Topology ModularForm CongruenceSubgroup

namespace BSD.RankTwo.PeriodFaithfulFrickePath

noncomputable section

/-- The analytic pullback statement, given the matching rational endpoint map. -/
theorem fricke_period_of_endpoint_map (p : ℕ) [Fact p.Prime] [NeZero p]
    (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2)
    (w : OnePoint ℚ → OnePoint ℚ)
    (hw : ∀ x, cuspInf
      (weightTwoFricke p (by exact_mod_cast (Fact.out : p.Prime).pos) * mapGL ℝ (rep x)) =
        OnePoint.map Rat.cast (w x))
    (a b : OnePoint ℚ) :
    cuspFormPeriod (frickeCusp p f) a b = cuspFormPeriod f (w a) (w b) := by
  let W := weightTwoFricke p (by exact_mod_cast (Fact.out : p.Prime).pos)
  let P := BSD.General.Periods.primitive f
  let Q := BSD.General.Periods.primitive (frickeCusp p f)
  let R : ℂ → ℂ := fun z => P (W • ofComplex z : ℍ)
  let F : ℂ → ℂ := fun z => (frickeCusp p f) (ofComplex z)
  have hW : 0 < W.val.det := by
    change 0 < (weightTwoFricke p _).val.det
    rw [← GeneralLinearGroup.val_det_apply, weightTwoFricke_det]
    exact_mod_cast (Fact.out : p.Prime).pos
  have hR : ∀ z : ℂ, 0 < z.im → HasDerivAt R (F z) z := by
    intro z hz
    let τ : ℍ := ⟨z, hz⟩
    have h := BSD.General.hasDerivAt_primitive_comp_smul (f : ℍ → ℂ) P W hW τ
      (BSD.General.Periods.hasDerivAt_primitive f (W • τ).im_pos)
    have hslash : ((f : ℍ → ℂ) ∣[(2 : ℤ)] W) τ = frickeCusp p f τ := by
      exact (congrFun (coe_frickeCusp p f) τ).symm
    rw [hslash] at h
    simpa [R, F, τ, ofComplex_apply_of_im_pos hz] using h
  have hQ : ∀ z : ℂ, 0 < z.im → HasDerivAt Q (F z) z := by
    intro z hz
    simpa [Q, F, ofComplex_apply_of_im_pos hz] using
      (BSD.General.Periods.hasDerivAt_primitive (frickeCusp p f) hz)
  obtain ⟨c, hc⟩ := BSD.General.PeriodsLimit.primitives_differ_by_constant R Q F hR hQ
  have hend (x : OnePoint ℚ) :
      cuspValue P (primitive_has_rational_limits f) (w x) =
        cuspValue Q (primitive_has_rational_limits (frickeCusp p f)) x + c := by
    have hleft := tendsto_cuspForm_primitive f (w x) (W * mapGL ℝ (rep x)) (hw x)
    have hright := (tendsto_rep Q (primitive_has_rational_limits (frickeCusp p f)) x).add
      (tendsto_const_nhds : Tendsto (fun _ : ℍ => c) atImInfty (𝓝 c))
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards with z
    simpa only [R, ofComplex_apply, mul_smul] using
      (hc ((mapGL ℝ (rep x) • z : ℍ) : ℂ) (mapGL ℝ (rep x) • z : ℍ).im_pos).symm
  change relativePeriod Q (primitive_has_rational_limits (frickeCusp p f)) a b =
    relativePeriod P (primitive_has_rational_limits f) (w a) (w b)
  simp only [relativePeriod, hend]
  ring

/-- Rational Fricke matrix inducing the map x ↦ -1/(p x). -/
def frickeQ (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; (p : ℚ), 0] (by
    simp only [Matrix.det_fin_two_of]
    have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simpa using hp)

/-- The real Fricke action agrees with the rational action after casting cusps. -/
theorem frickeQ_map (p : ℕ) [Fact p.Prime] (x : OnePoint ℚ) :
    OnePoint.map (Rat.cast : ℚ → ℝ) (frickeQ p • x) =
      weightTwoFricke p (by exact_mod_cast (Fact.out : p.Prime).pos) •
        OnePoint.map (Rat.cast : ℚ → ℝ) x := by
  rw [← Rat.coe_castHom, OnePoint.map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeQ, weightTwoFricke_val]

/-- Fricke pullback transports the oriented path by the rational Fricke matrix. -/
theorem fricke_period (p : ℕ) [Fact p.Prime] [NeZero p]
    (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (a b : OnePoint ℚ) :
    cuspFormPeriod (frickeCusp p f) a b =
      cuspFormPeriod f (frickeQ p • a) (frickeQ p • b) := by
  apply fricke_period_of_endpoint_map p f (fun x => frickeQ p • x)
  intro x
  have hrep : (mapGL ℝ (rep x) • ∞ : OnePoint ℝ) = OnePoint.map Rat.cast x := rep_spec x
  rw [cuspInf, mul_smul, hrep]
  exact (frickeQ_map p x).symm

end
end BSD.RankTwo.PeriodFaithfulFrickePath
