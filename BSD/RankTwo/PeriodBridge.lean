import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.Tactic

/-! # Central periods and the weight two Fricke transformation -/

namespace BSD.RankTwo

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]

/-- The central integral along the imaginary axis, with respect to the height parameter. -/
noncomputable def centralPeriod (f : CuspForm Γ 2) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f (ofComplex (Complex.I * t))

theorem centralPeriod_integrable (f : CuspForm Γ 2) :
    IntegrableOn (fun t : ℝ ↦ f (ofComplex (Complex.I * t))) (Ioi 0) := by
  have h := ((CuspForm.isStrongFEPair (by norm_num : (0 : ℤ) < 2) f).hasMellin 1).1
  simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul,
    ModularForm.weakFEPair_f] using h

/-- At the center the ordinary L-function is the vertical integral times (2π). -/
theorem cuspForm_L_one_eq_centralPeriod (f : CuspForm Γ 2) :
    ModularForm.L (by norm_num : (0 : ℤ) < 2) f 1 =
      (2 * (Real.pi : ℂ)) * centralPeriod f := by
  rw [ModularForm.L, CuspForm.Λ_eq_mellin, Complex.Gammaℂ_one]
  simp [mellin, centralPeriod, mul_comm]

open Matrix in
/-- The action (z mapsto -1/(Nz)) as a matrix of positive determinant. -/
noncomputable def weightTwoFricke (N : ℝ) (hN : 0 < N) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; N, 0]
    (by simpa [det_fin_two_of] using hN.ne')

open Matrix in
theorem weightTwoFricke_val (N : ℝ) (hN : 0 < N) :
    (weightTwoFricke N hN : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; N, 0] := by
  simp [weightTwoFricke]

theorem weightTwoFricke_det (N : ℝ) (hN : 0 < N) :
    (weightTwoFricke N hN).det.val = N := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, weightTwoFricke_val, Matrix.det_fin_two_of]
  ring

private theorem weightTwoFricke_smul_axis {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    weightTwoFricke N hN • ofComplex (Complex.I * t) =
      ofComplex (Complex.I * (N * t)⁻¹) := by
  have hNt : 0 < (N * t)⁻¹ := inv_pos.mpr (mul_pos hN ht)
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rwa [weightTwoFricke_det])]
  rw [ofComplex_apply_of_im_pos (by simpa using ht),
    ofComplex_apply_of_im_pos (by simpa using hNt)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, weightTwoFricke_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val',
    Matrix.of_apply, Complex.ofReal_zero, Complex.ofReal_neg,
    Complex.ofReal_one, zero_mul, zero_add, add_zero, Complex.ofReal_inv, Complex.ofReal_mul]
  field_simp [hN.ne', ht.ne', Complex.I_ne_zero]
  simp

/-- A weight-two function in the minus Fricke eigenspace obeys the usual reciprocal
identity along the imaginary axis. -/
theorem weightTwo_fricke_axis {N t : ℝ} (hN : 0 < N) (ht : 0 < t)
    (f : ℍ → ℂ) (hW : f ∣[(2 : ℤ)] weightTwoFricke N hN = -f) :
    f (ofComplex (Complex.I * (N * t)⁻¹)) =
      (N : ℂ) * (t : ℂ)^2 * f (ofComplex (Complex.I * t)) := by
  have hdet : 0 < (weightTwoFricke N hN).det.val := by
    rwa [weightTwoFricke_det]
  have hd : denom (weightTwoFricke N hN) (ofComplex (Complex.I * t)) =
      (N : ℂ) * Complex.I * t := by
    rw [ofComplex_apply_of_im_pos (by simpa using ht)]
    simp [denom, weightTwoFricke_val, mul_assoc]
  have h := congrFun hW (ofComplex (Complex.I * t))
  rw [ModularForm.slash_def] at h
  simp only [Pi.neg_apply] at h
  rw [weightTwoFricke_smul_axis hN ht, σ, if_pos hdet,
    weightTwoFricke_det, abs_of_pos hN, hd] at h
  norm_num [zpow_neg, mul_pow, Complex.I_sq] at h
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp [hNc, htc, Complex.I_ne_zero] at h
  simpa [Complex.ofReal_inv, Complex.ofReal_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The same weight-two identity on the imaginary axis scaled by the square root of
the conductor. Its real part gives the reciprocal relation for real Mellin moments. -/
theorem weightTwo_fricke_rescaled_axis {N t : ℝ} (hN : 0 < N) (ht : 0 < t)
    (f : ℍ → ℂ) (hW : f ∣[(2 : ℤ)] weightTwoFricke N hN = -f) :
    f (ofComplex (Complex.I * (t⁻¹ / Real.sqrt N : ℝ))) =
      (t : ℂ)^2 * f (ofComplex (Complex.I * (t / Real.sqrt N : ℝ))) := by
  have hroot := Real.sqrt_pos.mpr hN
  have h := weightTwo_fricke_axis hN (div_pos ht hroot) f hW
  have hr : (N * (t / Real.sqrt N))⁻¹ = t⁻¹ / Real.sqrt N := by
    field_simp [hN.ne', hroot.ne', ht.ne']
    nlinarith [Real.sq_sqrt hN.le]
  have hp : (N : ℂ) * ((t / Real.sqrt N : ℝ) : ℂ)^2 = (t : ℂ)^2 := by
    exact_mod_cast (show N * (t / Real.sqrt N)^2 = t^2 by
      rw [div_pow, Real.sq_sqrt hN.le]
      field_simp)
  rwa [hr, hp] at h

theorem weightTwo_fricke_rescaled_axis_re {N t : ℝ} (hN : 0 < N) (ht : 0 < t)
    (f : ℍ → ℂ) (hW : f ∣[(2 : ℤ)] weightTwoFricke N hN = -f) :
    (f (ofComplex (Complex.I * (t⁻¹ / Real.sqrt N : ℝ)))).re =
      t^2 * (f (ofComplex (Complex.I * (t / Real.sqrt N : ℝ)))).re := by
  rw [weightTwo_fricke_rescaled_axis hN ht f hW, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Rescaling the imaginary axis by the square root of the level produces the
conductor factor in the completed L-function. -/
theorem cuspForm_rescaled_mellin (f : CuspForm Γ 2) {N : ℝ} (hN : 0 < N) (s : ℂ) :
    mellin (fun t : ℝ ↦ f (ofComplex (Complex.I * (t / Real.sqrt N : ℝ)))) s =
      ((Real.sqrt N : ℂ)^s) * ModularForm.Λ (by norm_num : (0 : ℤ) < 2) f s := by
  have hroot := Real.sqrt_pos.mpr hN
  have harg : (Real.sqrt N : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hroot.le]
    exact Real.pi_ne_zero.symm
  have hscale : (fun t : ℝ ↦ f (ofComplex (Complex.I * (t / Real.sqrt N : ℝ)))) =
      (fun t : ℝ ↦ (fun u : ℝ ↦ f (ofComplex (Complex.I * u))) (t * (Real.sqrt N)⁻¹)) := by
    funext t
    rw [div_eq_mul_inv]
  rw [hscale, mellin_comp_mul_right (fun u : ℝ ↦ f (ofComplex (Complex.I * u))) s
    (inv_pos.mpr hroot), smul_eq_mul,
    CuspForm.Λ_eq_mellin, Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg,
    inv_inv]

end BSD.RankTwo
