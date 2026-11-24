import BSD.Convergence
import BSD.RankTwo.ArithmeticMoment

/-! Absolute convergence in the half-plane `Re(s) > 3/2` for the actual `qExpansion 1`
of a weight-two cusp form and its application to an arithmetic coefficient comparison. -/

open scoped MatrixGroups CongruenceSubgroup Real
open UpperHalfPlane

namespace BSD

private def horizontalPoint (t : ℝ) (ht : 0 < t) (x : ℝ) : UpperHalfPlane :=
  ⟨(x : ℂ) + (t : ℂ) * Complex.I, by simpa using ht⟩

private lemma qParam_horizontal_pow (t : ℝ) (ht : 0 < t) (x : ℝ) (n : ℕ) :
    Function.Periodic.qParam 1 (horizontalPoint t ht x) ^ n =
      (Real.exp (-((2 * Real.pi) * n) * t) : ℂ) *
        fourier (n : ℤ) (x : AddCircle (1 : ℝ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, fourier_coe_apply, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  change (n : ℂ) * (2 * Real.pi * Complex.I * ((x : ℂ) + (t : ℂ) * Complex.I) / 1) = _
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
variable {F : Type*} [FunLike F UpperHalfPlane ℂ] [CuspFormClass F Γ 2]

/-- A width-one expansion of a weight-two cusp form has quadratic second moment. -/
theorem weightTwo_qExpansion_secondMoment (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 0 < N →
      ∑ n ∈ Finset.Icc 1 N, ‖(qExpansion 1 f).coeff n‖ ^ 2 ≤ (K * N) ^ 2 := by
  let slice (t : ℝ) (ht : 0 < t) (x : ℝ) := f (horizontalPoint t ht x)
  obtain ⟨B, hB⟩ := CuspFormClass.exists_bound f
  apply secondMoment_of_fourierSlices (slice := slice) (B := max 0 B) (le_max_left _ _)
  · intro t ht
    apply (ModularFormClass.continuous f).comp
    unfold horizontalPoint
    fun_prop
  · intro t ht x
    have h := hB (horizontalPoint t ht x)
    calc
      ‖slice t ht x‖ ≤ B / t := by
        simpa [slice, horizontalPoint, UpperHalfPlane.im] using h
      _ ≤ max 0 B / t := div_le_div_of_nonneg_right (le_max_right _ _) ht.le
  · intro t ht n
    let c (m : ℕ) := (qExpansion 1 f).coeff m * (Real.exp (-((2 * Real.pi) * m) * t) : ℂ)
    have h (x : ℝ) : HasSum (fun m : ℕ ↦ c m * fourier (m : ℤ) (x : AddCircle (1 : ℝ)))
        (slice t ht x) := by
      apply (ModularForm.hasSum_qExpansion f zero_lt_one hΓ (horizontalPoint t ht x)).congr_fun
      intro m
      rw [qParam_horizontal_pow]
      simp only [c, mul_assoc]
    have hnorm : Summable (fun m : ℕ ↦ ‖c m‖) := by
      simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using (h 0).summable.norm
    exact FermatCubic.fourierCoeffOn_of_hasSum_fourier hnorm h n

/-- Absolute convergence of the Dirichlet series formed with the actual weight-two cusp
coefficients, throughout the open half-plane `Re(s) > 3/2`. -/
theorem weightTwo_qExpansion_LSeriesSummable (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable (fun n ↦ (qExpansion 1 f).coeff n) s := by
  obtain ⟨K, hK, h⟩ := weightTwo_qExpansion_secondMoment f hΓ
  exact FermatCubic.lSeriesSummable_of_secondMoment hK h hs

/-- At positive level `Γ₀(N)`, translation by one is a strict period. -/
theorem gamma0_weightTwo_LSeriesSummable {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion 1 f).coeff n) s :=
  weightTwo_qExpansion_LSeriesSummable f (by simp) hs

namespace RankTwo

/-- The modularity comparison transports absolute convergence to the curve coefficients. -/
theorem curve_LSeriesSummable_of_qExpansion
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hf : ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ))
    {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable (fun n ↦ (realCoefficient n : ℂ)) s := by
  have h := gamma0_weightTwo_LSeriesSummable f hs
  simpa only [hf, realCoefficient, Complex.ofReal_intCast] using h

/-- An all-coefficient modularity comparison identifies the normalized arithmetic Mellin
transform with the genuine curve L-series on its defining half-plane. -/
theorem normalizedMellinL_eq_curve_LSeries_of_qExpansion
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hf : ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ))
    {s : ℂ} (hs : 3 / 2 < s.re) :
    normalizedMellinL mellinRate arithmeticAxis s = curve.LSeries s := by
  have h := normalizedMellinL_eq_LSeries (c := mellinRate) (by linarith [mellinRate_bounds.1])
    (a := realCoefficient) (by simp [realCoefficient]) (fun _ ht ↦ arithmeticAxis_hasSum ht)
    (by linarith : 0 < s.re) (curve_LSeriesSummable_of_qExpansion f hf hs)
  simpa [WeierstrassCurve.LSeries, realCoefficient, Function.comp_def] using h

end RankTwo

end BSD
