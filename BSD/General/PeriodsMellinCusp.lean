import BSD.General.PeriodsMellin
import BSD.General.PeriodsCusp

/-! The imaginary-axis limit of the relative cusp period. -/

open MeasureTheory Set Filter UpperHalfPlane OnePoint Matrix GeneralLinearGroup
open scoped MatrixGroups ModularForm Topology

namespace BSD.General.PeriodsRelative

private theorem axis_tendsto_atImInfty :
    Tendsto (fun t : ℝ => ofComplex (Complex.I * t)) atTop atImInfty := by
  apply tendsto_comap_im_ofComplex.comp
  apply tendsto_comap_iff.mpr
  convert (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop) using 1
  ext t
  simp [Complex.mul_im]

private theorem fricke_one_cusp :
    BSD.General.PeriodsRational.cuspInf (BSD.RankTwo.weightTwoFricke 1 (by norm_num)) =
      OnePoint.map Rat.cast (OnePoint.some 0) := by
  rw [OnePoint.map_some, Rat.cast_zero]
  rw [BSD.General.PeriodsRational.cuspInf, smul_infty_eq_ite]
  simp [BSD.RankTwo.weightTwoFricke_val]

private theorem fricke_one_smul_axis {t : ℝ} (ht : 0 < t) :
    BSD.RankTwo.weightTwoFricke 1 (by norm_num) • ofComplex (Complex.I * t) =
      ofComplex (Complex.I * t⁻¹) := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [BSD.RankTwo.weightTwoFricke_det]; norm_num)]
  rw [ofComplex_apply_of_im_pos (by simpa using ht),
    ofComplex_apply_of_im_pos (by simpa using hti)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, BSD.RankTwo.weightTwoFricke_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.cons_val', Matrix.of_apply, Complex.ofReal_zero, Complex.ofReal_neg,
    Complex.ofReal_one, zero_mul, zero_add, add_zero, Complex.ofReal_inv]
  field_simp [ht.ne', Complex.I_ne_zero]
  simp

/-- The period from 0 to infinity is the imaginary-axis integral, including
its orientation and the differential factor `I`. -/
theorem cuspFormPeriod_zero_infty {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    cuspFormPeriod f (OnePoint.some 0) OnePoint.infty =
      Complex.I * BSD.RankTwo.centralPeriod f := by
  let P := BSD.General.Periods.primitive f
  let L₀ := cuspValue P (primitive_has_rational_limits f) (OnePoint.some 0)
  let Ltop := cuspValue P (primitive_has_rational_limits f) OnePoint.infty
  have htop : Tendsto (fun t : ℝ => P (Complex.I * t)) atTop (𝓝 Ltop) := by
    have h := (tendsto_cuspForm_primitive f OnePoint.infty 1 (by simp [BSD.General.PeriodsRational.cuspInf])).comp axis_tendsto_atImInfty
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply, one_smul]
    rw [ofComplex_apply_of_im_pos (show 0 < (Complex.I * (t : ℂ)).im by simpa using ht)]
  have hzero' := (tendsto_cuspForm_primitive f (OnePoint.some 0)
    (BSD.RankTwo.weightTwoFricke 1 (by norm_num)) fricke_one_cusp).comp axis_tendsto_atImInfty
  have hzero : Tendsto (fun t : ℝ => P (Complex.I * t)) (𝓝[>] 0) (𝓝 L₀) := by
    have h := hzero'.comp (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : 0 < t⁻¹ := inv_pos.mpr ht
    simp only [Function.comp_apply]
    rw [fricke_one_smul_axis hp]
    simp only [inv_inv]
    rw [ofComplex_apply_of_im_pos (show 0 < (Complex.I * (t : ℂ)).im by simpa using ht)]
  have hderiv : ∀ z : ℍ, HasDerivAt P (f z) (z : ℂ) := by
    intro z
    exact BSD.General.Periods.hasDerivAt_primitive f z.im_pos
  simpa [cuspFormPeriod, relativePeriod, P, L₀, Ltop] using
    BSD.General.centralPeriod_eq_endpoint_difference_of_complex_primitive f P L₀ Ltop hderiv hzero htop

end BSD.General.PeriodsRelative
