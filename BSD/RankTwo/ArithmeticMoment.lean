import BSD.RankTwo.CoefficientBound
import BSD.RankTwo.DerivativeIntegral
import BSD.RankTwo.FirstCoefficients
import BSD.RankTwo.MellinCertificate
import BSD.RankStatement
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # The second logarithmic moment of the actual Hasse–Weil coefficients of 389.a1 -/

open Filter Set MeasureTheory
open scoped Topology

namespace BSD.RankTwo

noncomputable abbrev realCoefficient (n : ℕ) : ℝ := (curve.LFunction n : ℤ)

theorem realCoefficient_bound (n : ℕ) : |realCoefficient n| ≤ (n : ℝ)^2 := by
  exact_mod_cast BSD.weierstrass_LFunction_abs_apply_le_sq curve n

private theorem rate_pos : 0 < mellinRate := by linarith [mellinRate_bounds.1]

/-- A signed infinite sum with a strict lower bound from the true arithmetic
coefficients. Its proof uses finite point-count certificates and a tail bound. -/
theorem curve_second_moment_lower :
    (0.06 : ℝ) < ∑' n : ℕ, realCoefficient n * mellinKernel n :=
  mellinMoment_lower realCoefficient (fun i ↦ by exact_mod_cast firstCoefficients_eq_LFunction i)
    realCoefficient_bound

noncomputable def arithmeticAxis (t : ℝ) : ℝ :=
  ∑' n : ℕ, realCoefficient n * Real.exp (-(mellinRate*n)*t)

private theorem summable_axis_norm {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ ↦ ‖realCoefficient n‖ * Real.exp (-(mellinRate*n)*t)) := by
  have h := summable_fourier_norm_at_one (mul_pos rate_pos ht)
    (a := realCoefficient) (k := 2) realCoefficient_bound
  convert h using 1
  ext n
  congr 2
  ring

theorem arithmeticAxis_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ realCoefficient n * Real.exp (-(mellinRate*n)*t)) (arithmeticAxis t) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le] using summable_axis_norm ht

theorem continuousOn_arithmeticAxis : ContinuousOn arithmeticAxis (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  have hd : 0 < t/2 := by linarith
  have hc : ContinuousOn arithmeticAxis (Ioi (t/2)) := by
    unfold arithmeticAxis
    apply continuousOn_tsum (fun n ↦ by fun_prop) (summable_axis_norm hd)
    intro n x hx
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (le_of_lt hx)
      (neg_nonpos.mpr (mul_nonneg rate_pos.le (Nat.cast_nonneg n)))
  have ht₂ : t ∈ Ioi (t/2) := by change t/2 < t; linarith
  exact (isOpen_Ioi.continuousOn_iff.mp hc ht₂).continuousWithinAt

/-- The remaining Fricke relation for the series of the curve itself. -/
def ArithmeticFricke : Prop := ∀ t > 0, arithmeticAxis t⁻¹ = t^2 * arithmeticAxis t

noncomputable def completedL (s : ℂ) : ℂ := mellin (fun t ↦ (arithmeticAxis t : ℂ)) s

theorem completedL_properties (hF : ArithmeticFricke) :
    Differentiable ℂ completedL ∧ ∀ s : ℂ, completedL (2-s) = completedL s :=
  differentiable_mellin_of_fricke continuousOn_arithmeticAxis hF rate_pos
    (a := realCoefficient) (by simp [realCoefficient])
    (fun t ht ↦ arithmeticAxis_hasSum (zero_lt_one.trans ht))
    (summable_fourier_norm_at_one rate_pos realCoefficient_bound)

/-- The numerical certificate becomes a derivative statement under the
Fricke relation. No external coefficient data enter this theorem. -/
theorem second_derivative_re_lower (hF : ArithmeticFricke) :
    (0.12 : ℝ) < (iteratedDeriv 2 completedL 1).re := by
  have h := second_deriv_mellin_389_eq_kernel_sum continuousOn_arithmeticAxis hF
    (a := realCoefficient) (by simp [realCoefficient])
    (fun t ht ↦ arithmeticAxis_hasSum (zero_lt_one.trans ht)) realCoefficient_bound
  change (0.12 : ℝ) < (iteratedDeriv 2 (mellin (fun t ↦ (arithmeticAxis t : ℂ))) 1).re
  rw [h]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  linarith [curve_second_moment_lower]

theorem completedL_order_two (hF : ArithmeticFricke) (hcentral : completedL 1 = 0) :
    meromorphicOrderAt completedL 1 = 2 := by
  obtain ⟨hd, hsymm⟩ := completedL_properties hF
  apply BSD.meromorphicOrderAt_eq_two_of_even (hd.analyticAt 1) _ hcentral
  · intro hz
    have h := second_derivative_re_lower hF
    rw [hz, Complex.zero_re] at h
    norm_num at h
  · apply Filter.Eventually.of_forall
    intro z
    convert (hsymm (1+z)).symm using 2
    ring

end BSD.RankTwo
