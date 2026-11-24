import BSD.RankTwo.PeriodBridge
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv

/-! # A fundamental theorem of calculus bridge for the central period -/

open MeasureTheory Set Filter UpperHalfPlane
open scoped MatrixGroups ModularForm Topology

namespace BSD.General

/-- A primitive along the imaginary axis identifies its endpoint difference with the
central Mellin period.  The value assigned at zero is the right-hand endpoint limit. -/
theorem centralPeriod_eq_endpoint_difference
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 2) (P : ℝ → ℂ) (L₀ Ltop : ℂ)
    (hzero : P 0 = L₀) (hcont : ContinuousWithinAt P (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt P (Complex.I * f (ofComplex (Complex.I * t))) t)
    (htop : Tendsto P atTop (𝓝 Ltop)) :
    Ltop - L₀ = Complex.I * BSD.RankTwo.centralPeriod f := by
  have hint : IntegrableOn (fun t : ℝ => Complex.I * f (ofComplex (Complex.I * t)))
      (Ioi 0) := (BSD.RankTwo.centralPeriod_integrable f).const_mul Complex.I
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  rw [integral_const_mul] at h
  simpa only [BSD.RankTwo.centralPeriod, hzero] using h.symm

/-- The same bridge for a complex primitive, using only its two axis limits. -/
theorem centralPeriod_eq_endpoint_difference_of_complex_primitive
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 2) (P : ℂ → ℂ) (L₀ Ltop : ℂ)
    (hP : ∀ z : ℍ, HasDerivAt P (f z) (z : ℂ))
    (hzero : Tendsto (fun t : ℝ => P (Complex.I * t)) (𝓝[>] 0) (𝓝 L₀))
    (htop : Tendsto (fun t : ℝ => P (Complex.I * t)) atTop (𝓝 Ltop)) :
    Ltop - L₀ = Complex.I * BSD.RankTwo.centralPeriod f := by
  let axis : ℝ → ℂ := fun t => P (Complex.I * t)
  let patched := Function.update axis 0 L₀
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt patched (Complex.I * f (ofComplex (Complex.I * t))) t := by
    intro t (ht : 0 < t)
    have him : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
    have hcomplex := (hP ⟨Complex.I * (t : ℂ), him⟩).comp (t : ℂ)
      ((hasDerivAt_const (t : ℂ) Complex.I).mul (hasDerivAt_id (t : ℂ)))
    have haxis : HasDerivAt axis (Complex.I * f (ofComplex (Complex.I * t))) t := by
      rw [ofComplex_apply_of_im_pos him]
      simpa [axis, mul_comm] using hcomplex.comp_ofReal
    apply haxis.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht.ne.symm] with y hy
    exact Function.update_of_ne hy L₀ axis
  have hcont : ContinuousWithinAt patched (Ici 0) 0 := by
    apply continuousWithinAt_update_same.mpr
    rw [Ici_sdiff_left]
    exact hzero
  have htop' : Tendsto patched atTop (𝓝 Ltop) := by
    apply htop.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    exact (Function.update_of_ne ht L₀ axis).symm
  exact centralPeriod_eq_endpoint_difference f patched L₀ Ltop
    (Function.update_self 0 L₀ axis) hcont hderiv htop'

end BSD.General
