import BSD.General.ModularDataCoefficients
import BSD.General.ModularDataHeckeSeries
import BSD.General.ModularDataHeckeCoeff

/-! Pointwise consequences of the good-prime Fourier coefficient relations. -/

namespace BSD.General

/-- Width-one Fourier expansion at an arbitrary point of the upper half-plane. -/
theorem cuspCoefficients_hasSum {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => cuspCoefficients f n *
      Function.Periodic.qParam 1 τ ^ n) (f τ) := by
  simpa only [cuspCoefficients_apply] using
    ModularForm.hasSum_qExpansion f (h := 1) zero_lt_one (by simp) τ

private theorem qParam_double (z : ℂ) :
    Function.Periodic.qParam 1 (2 * z) = Function.Periodic.qParam 1 z ^ 2 := by
  simp only [Function.Periodic.qParam, pow_two, ← Complex.exp_add]
  congr 1
  ring

private theorem qParam_half_sq (z : ℂ) :
    Function.Periodic.qParam 1 (z / 2) ^ 2 = Function.Periodic.qParam 1 z := by
  simp only [Function.Periodic.qParam, pow_two, ← Complex.exp_add]
  congr 1
  ring

private theorem qParam_half_translate (z : ℂ) :
    Function.Periodic.qParam 1 ((z + 1) / 2) = -Function.Periodic.qParam 1 (z / 2) := by
  simp only [Function.Periodic.qParam]
  norm_num only [Complex.ofReal_one, div_one]
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((z + 1) / 2) =
      2 * ↑Real.pi * Complex.I * (z / 2) + ↑Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The Fourier coefficient relations imply the unnormalized pointwise action of
T₂ at a level prime to two. -/
theorem ModularCoefficientData.hecke_two_pointwise {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : ModularCoefficientData f)
    (hN : ¬ 2 ∣ N) (τ : UpperHalfPlane) :
    2 * f (UpperHalfPlane.ofComplex (2 * (τ : ℂ))) +
      (f (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)) +
       f (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2))) / 2 =
      cuspCoefficients f 2 * f τ := by
  classical
  let a : ℕ → ℂ := cuspCoefficients f
  let q : ℂ := Function.Periodic.qParam 1 τ
  let ξ : ℂ := Function.Periodic.qParam 1 ((τ : ℂ) / 2)
  let z₁ := UpperHalfPlane.ofComplex (2 * (τ : ℂ))
  let z₂ := UpperHalfPlane.ofComplex ((τ : ℂ) / 2)
  let z₃ := UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)
  have h₁ : 0 < (2 * (τ : ℂ)).im := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos
  have h₂ : 0 < ((τ : ℂ) / 2).im := by
    simpa using div_pos τ.im_pos (by norm_num : (0 : ℝ) < 2)
  have h₃ : 0 < (((τ : ℂ) + 1) / 2).im := by
    simpa using div_pos τ.im_pos (by norm_num : (0 : ℝ) < 2)
  have hz₁ : (z₁ : ℂ) = 2 * (τ : ℂ) := by
    simp [z₁, UpperHalfPlane.ofComplex_apply_of_im_pos h₁]
  have hz₂ : (z₂ : ℂ) = (τ : ℂ) / 2 := by
    simp [z₂, UpperHalfPlane.ofComplex_apply_of_im_pos h₂]
  have hz₃ : (z₃ : ℂ) = ((τ : ℂ) + 1) / 2 := by
    simp [z₃, UpperHalfPlane.ofComplex_apply_of_im_pos h₃]
  have hξ : ξ ^ 2 = q := qParam_half_sq τ
  have hq₁ : Function.Periodic.qParam 1 z₁ = q ^ 2 := by
    rw [hz₁]; exact qParam_double τ
  have hq₂ : Function.Periodic.qParam 1 z₂ = ξ := by rw [hz₂]
  have hq₃ : Function.Periodic.qParam 1 z₃ = -ξ := by
    rw [hz₃]; exact qParam_half_translate τ
  have hbase : HasSum (fun n => a n * q ^ n) (f τ) := cuspCoefficients_hasSum f τ
  have hdouble : HasSum (fun n => a n * (q ^ 2) ^ n) (f z₁) := by
    simpa only [a, hq₁] using cuspCoefficients_hasSum f z₁
  have hplus : HasSum (fun n => a n * ξ ^ n) (f z₂) := by
    simpa only [a, hq₂] using cuspCoefficients_hasSum f z₂
  have hminus : HasSum (fun n => a n * (-ξ) ^ n) (f z₃) := by
    simpa only [a, hq₃] using cuspCoefficients_hasSum f z₃
  have hfilter : HasSum (fun n => a (2 * n) * q ^ n) ((f z₂ + f z₃) / 2) := by
    have heq : (f z₂ + f z₃) / 2 = ∑' n : ℕ, a (2 * n) * q ^ n := by
      calc
        _ = (∑' n : ℕ, a n * ξ ^ n) / 2 + (∑' n : ℕ, a n * (-ξ) ^ n) / 2 := by
          rw [hplus.tsum_eq, hminus.tsum_eq]; ring
        _ = ((∑' n : ℕ, a n * ξ ^ n) + (∑' n : ℕ, a n * (-ξ) ^ n)) / 2 := by ring
        _ = ∑' n : ℕ, a (2 * n) * (ξ ^ 2) ^ n :=
          tsum_even_filter a ξ hplus.summable hminus.summable
        _ = ∑' n : ℕ, a (2 * n) * q ^ n := by rw [hξ]
    rw [heq]
    simpa only [hξ] using (summable_even_filter a ξ hplus.summable).hasSum
  have hinsert := hasSum_even_insert a q hdouble.summable
  rw [hdouble.tsum_eq] at hinsert
  have hleft := hinsert.add hfilter
  have hright := hbase.mul_left (a 2)
  have hsame : HasSum (fun n =>
      (if 2 ∣ n then 2 * a (n / 2) else 0) * q ^ n + a (2 * n) * q ^ n)
      (a 2 * f τ) := by
    apply hright.congr_fun
    intro n
    have hcoef := good_hecke_coefficient (cuspCoefficients f) hf.isMultiplicative
      (by decide : Nat.Prime 2)
      (fun k => hf.qCoeff_prime_pow_of_not_dvd 2 k (by decide) hN) n
    have h := congrArg (fun z : ℂ => z * q ^ n) hcoef
    norm_num only [Nat.cast_ofNat] at h
    simpa only [a, add_mul, mul_assoc, add_comm] using h
  exact hleft.unique hsame

end BSD.General
