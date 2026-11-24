import BSD.RankTwo.CuspConvergence
import BSD.RankTwo.ModularSymbolsMellin
import BSD.RankTwo.PeriodBridge
import BSD.RankTwo.RankCriterion

/-! # From a level-389 modular form and its periods to the curve's rank statement -/

open Set MeasureTheory UpperHalfPlane
open scoped ModularForm

namespace BSD.RankTwo

variable (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)

/-- The rescaling is dictated by the conductor. -/
theorem arithmeticAxis_eq_cuspForm
    (hq : ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ))
    {t : ℝ} (ht : 0 < t) :
    (arithmeticAxis t : ℂ) = f (ofComplex (Complex.I * (t / Real.sqrt 389 : ℝ))) := by
  let u : ℝ := t / Real.sqrt 389
  have hu : 0 < u := div_pos ht (by positivity)
  let z := ofComplex (Complex.I * (u : ℂ))
  have hz : (z : ℂ) = (u : ℂ) * Complex.I := by
    dsimp [z]
    rw [ofComplex_apply_of_im_pos (by simpa using hu : 0 < (Complex.I * (u : ℂ)).im)]
    exact mul_comm _ _
  have h := ModularForm.hasSum_qExpansion f (h := 1) zero_lt_one (by simp) z
  have has := (arithmeticAxis_hasSum ht).map Complex.ofRealCLM.toAddMonoidHom
    Complex.ofRealCLM.continuous
  apply has.unique
  apply h.congr_fun
  intro n
  simp only [Function.comp_apply, realCoefficient, hq, hz,
    FermatCubic.qParam_axis, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  change (↑((curve.LFunction n : ℝ) * Real.exp (-(mellinRate * n) * t)) : ℂ) = _
  rw [Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 3
  dsimp [u, mellinRate]
  ring

theorem arithmeticFricke_of_cuspForm
    (hq : ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ))
    (hw : (f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke 389 (by norm_num) = -(f : ℍ → ℂ)) :
    ArithmeticFricke := by
  intro t ht
  have h := weightTwo_fricke_rescaled_axis (by norm_num : (0 : ℝ) < 389) ht f hw
  rw [← arithmeticAxis_eq_cuspForm f hq (inv_pos.mpr ht), ← arithmeticAxis_eq_cuspForm f hq ht] at h
  exact_mod_cast h

theorem completedL_one_eq_scaled_period
    (hq : ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ)) :
    completedL 1 = Real.sqrt 389 • centralPeriod f := by
  rw [completedL, mellin]
  simp only [sub_self, Complex.cpow_zero, one_smul]
  have h := setIntegral_congr_fun (μ := volume) measurableSet_Ioi
    (fun (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) ↦ arithmeticAxis_eq_cuspForm f hq ht)
  rw [h]
  simpa only [centralPeriod, div_eq_mul_inv, inv_inv, zero_mul] using
    integral_comp_mul_right_Ioi (fun t : ℝ ↦ f (ofComplex (Complex.I * t))) 0
      (b := (Real.sqrt 389)⁻¹) (by positivity)

/-- A genuine modularity and period certificate suffices. The arithmetic
rank and the entire second derivative estimate are discharged internally. -/
theorem rankPart_of_modular_data
    (hq : ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ))
    (hw : (f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke 389 (by norm_num) = -(f : ℍ → ℂ))
    (hp : centralPeriod f = 0) : RankPart curve := by
  apply rankPart_of_fricke_and_central_value (arithmeticFricke_of_cuspForm f hq hw)
  · rw [completedL_one_eq_scaled_period f hq, hp, smul_zero]
  · exact fun _ hs ↦ curve_LSeriesSummable_of_qExpansion f hq hs

end BSD.RankTwo
