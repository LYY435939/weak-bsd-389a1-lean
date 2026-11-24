import BSD.RankTwo.ArithmeticMoment
import BSD.RankTwo.DescentUpperRank

/-! # A rank-two criterion for the actual arithmetic Fourier series of 389.a1 -/

namespace BSD.RankTwo

def ArithmeticSummability : Prop :=
  ∀ s : ℂ, 3/2 < s.re → LSeriesSummable (fun n ↦ (realCoefficient n : ℂ)) s

private noncomputable def normalization (s : ℂ) : ℂ := (mellinRate : ℂ)^s / Complex.Gamma s

private theorem rate_ne_zero : (mellinRate : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by linarith [mellinRate_bounds.1])

private theorem differentiable_normalization : Differentiable ℂ normalization := by
  intro s
  unfold normalization
  simp only [div_eq_mul_inv]
  exact (differentiableAt_id.const_cpow (Or.inl rate_ne_zero)).mul
    (Complex.differentiable_one_div_Gamma s)

theorem normalizedL_continues (hF : ArithmeticFricke) (hsum : ArithmeticSummability) :
    Continues curve (normalizedMellinL mellinRate arithmeticAxis) := by
  have hd := (completedL_properties hF).1
  change Continues curve (normalization * completedL)
  refine ⟨fun s ↦ ((differentiable_normalization.mul hd).analyticAt s).meromorphicAt,
    fun s hs ↦ ?_⟩
  have h := normalizedMellinL_eq_LSeries (c := mellinRate) (by linarith [mellinRate_bounds.1])
    (a := realCoefficient) (by simp [realCoefficient])
    (F := arithmeticAxis) (fun _ ht ↦ arithmeticAxis_hasSum ht)
    (by linarith : 0 < s.re) (hsum s hs)
  simpa only [normalization, completedL, Pi.mul_apply, normalizedMellinL, WeierstrassCurve.LSeries,
    Function.comp_def, realCoefficient, Complex.ofReal_intCast] using h

/-- The arithmetic rank and the positive second-derivative certificate have
already been proved. These three analytic inputs finish the comparison. -/
theorem rankPart_of_fricke_and_central_value (hF : ArithmeticFricke)
    (hcentral : completedL 1 = 0) (hsum : ArithmeticSummability) : RankPart curve := by
  refine ⟨normalizedMellinL mellinRate arithmeticAxis, normalizedL_continues hF hsum, ?_⟩
  rw [BSD.RankTwo389.rational_finrank_eq_two]
  change meromorphicOrderAt (normalization * completedL) 1 = 2
  rw [meromorphicOrderAt_mul_of_ne_zero (differentiable_normalization.analyticAt 1)
    (by simpa only [normalization, Complex.cpow_one, Complex.Gamma_one, div_one] using rate_ne_zero)]
  exact completedL_order_two hF hcentral

end BSD.RankTwo
