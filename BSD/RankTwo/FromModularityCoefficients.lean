import BSD.General.ModularData
import BSD.PrimeRecurrence
import BSD.RankTwo.ModularSymbolsLocal
import BSD.RankTwo.BadReduction
import BSD.RankTwo.GoodReduction

/-! Coefficient comparison for the modular model of 389.a1. -/

namespace BSD.RankTwo

open BSD.General NumberField Polynomial UpperHalfPlane

private theorem model_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) :
    (model R).map g = model S := by
  ext <;> simp [model, map_ofNat]

private theorem model_trace_two : integralModelTrace (model ℤ) 2 = ModularSymbols.traceTwo := by
  norm_num [integralModelTrace, model_map, ModularSymbols.traceTwo]

/-- The trace assumption fixes the coefficient at two. -/
theorem cuspCoefficients_two_of_model_trace
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (htrace : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ (model ℤ).Δ → ¬ p ∣ 389 →
      cuspCoefficients f p = (integralModelTrace (model ℤ) p : ℂ)) :
    cuspCoefficients f 2 = (ModularSymbols.traceTwo : ℂ) := by
  rw [← model_trace_two]
  exact htrace 2 (by norm_num) (by rw [discriminant]; norm_num) (by norm_num)

private theorem model_trace_three : integralModelTrace (model ℤ) 3 = -2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : (model (ZMod 3)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  have hc : Nat.card (model (ZMod 3)).toAffine.Point = 6 :=
    card_model_of_affine_card 5 (by decide)
  rw [integralModelTrace, model_map, hc]
  norm_num

private theorem trace_polynomial_at_good_prime {p : ℕ} (hp : p.Prime) (hbad : p ≠ 389)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) :
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - C (integralModelTrace (model ℤ) p) * X + C (p : ℤ) * X ^ 2 := by
  rcases eq_or_ne p 2 with rfl | hp₂
  · simpa [model_trace_two, ModularSymbols.traceTwo_eq, sub_eq_add_neg] using
      localPolynomial_two_rat v hv
  rcases eq_or_ne p 3 with rfl | hp₃
  · simpa [model_trace_three, sub_eq_add_neg] using localPolynomial_three_rat v hv
  have hp₅ : 5 ≤ p := by
    have htwo := hp.two_le
    by_contra! h
    have hfour : p = 4 := by omega
    exact (by decide : ¬ Nat.Prime 4) (hfour ▸ hp)
  have h := good_localPolynomial_rat v (hv ▸ hp₅) (hv ▸ hbad)
  dsimp only at h
  have hc := congrArg (fun q : ℕ ↦ Nat.card (model (ZMod q)).toAffine.Point) hv
  rw [hc] at h
  simpa only [hv, integralModelTrace, model_map] using h

private theorem curve_inverse_of_polynomial (p : ℕ) (a b : ℤ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p)
    (hd : (curve.baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ) = 1 - C a * X + C b * X ^ 2) :
    PowerSeries.mk (fun k : ℕ => (curve.LFunction (p ^ k) : ℂ)) *
      quadraticEulerPolynomial (a : ℂ) (b : ℂ) = 1 := by
  have h (k : ℕ) := BSD.weierstrass_LFunction_apply_prime_pow curve v k
  simp only [hv, WeierstrassCurve.localPowerSeries, hd, Polynomial.coe_add,
    Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_pow] at h
  have hrec := BSD.reciprocal_quadratic_coefficients a b
  apply powerSeries_mul_quadratic_eq_one
  · simp [(BSD.weierstrass_LFunction_isMultiplicative curve).map_one]
  · exact_mod_cast (h 1).trans hrec.1
  · intro k
    have hk : curve.LFunction (p ^ (k + 2)) =
        a * curve.LFunction (p ^ (k + 1)) - b * curve.LFunction (p ^ k) := by
      rw [h, h, h]
      exact hrec.2 k
    exact_mod_cast hk

private theorem coefficients_eq_of_same_denominator (A B : ℕ → ℂ) (D : PowerSeries ℂ)
    (hA : PowerSeries.mk A * D = 1) (hB : PowerSeries.mk B * D = 1) (k : ℕ) :
    A k = B k := by
  have heq : PowerSeries.mk A = PowerSeries.mk B := calc
    _ = PowerSeries.mk A * (D * PowerSeries.mk B) := by rw [mul_comm D, hB, mul_one]
    _ = _ := by rw [← mul_assoc, hA, one_mul]
  simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) heq

/-- The good-prime traces and the coefficient at the level prime determine the full
Fourier expansion through the local Euler denominators. -/
theorem all_coefficients_of_eigenform_good_and_bad_trace
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2) (hf : ModularCoefficientData f)
    (htrace : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ (model ℤ).Δ → ¬ p ∣ 389 →
      cuspCoefficients f p = (integralModelTrace (model ℤ) p : ℂ))
    (hbad : cuspCoefficients f 389 = 1) :
    ∀ n : ℕ, (qExpansion 1 f).coeff n = (curve.LFunction n : ℤ) := by
  let A : ArithmeticFunction ℂ := ⟨fun n ↦ (curve.LFunction n : ℂ), by simp⟩
  have hmul := BSD.weierstrass_LFunction_isMultiplicative curve
  have hA : A.IsMultiplicative := by
    constructor
    · change (curve.LFunction 1 : ℂ) = 1
      simp [hmul.map_one]
    · intro m n hmn
      change (curve.LFunction (m * n) : ℂ) = (curve.LFunction m : ℂ) * (curve.LFunction n : ℂ)
      rw [hmul.map_mul_of_coprime hmn, Int.cast_mul]
  have heq : cuspCoefficients f = A := by
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hf.isMultiplicative _ hA).2
    intro p k hp
    let v := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩
    have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
      exact congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)
    change cuspCoefficients f (p ^ k) = (curve.LFunction (p ^ k) : ℂ)
    by_cases h : p = 389
    · rw [h]
      have hv' := hv.trans h
      have hd : (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
          1 - C (1 : ℤ) * X + C (0 : ℤ) * X ^ 2 := by
        simpa using bad_localPolynomial_rat v hv'
      have hB := curve_inverse_of_polynomial 389 1 0 v hv' hd
      have hF := hf.inverse_bad (h ▸ hp) (dvd_refl 389)
      rw [hbad] at hF
      apply coefficients_eq_of_same_denominator _ _ (quadraticEulerPolynomial 1 0) hF
      simpa only [Int.cast_one, Int.cast_zero] using hB
    · have hn : ¬ p ∣ 389 :=
        fun hd ↦ h ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
      have hd : ¬ (p : ℤ) ∣ (model ℤ).Δ := by
        rw [discriminant]
        exact_mod_cast hn
      have hF := hf.inverse_good hp hn
      rw [htrace p hp hd hn] at hF
      have hB := curve_inverse_of_polynomial p (integralModelTrace (model ℤ) p) p v hv
        (trace_polynomial_at_good_prime hp h v hv)
      apply coefficients_eq_of_same_denominator _ _ _ hF
      simpa only [Int.cast_natCast] using hB
  intro n
  exact congrArg (fun g : ArithmeticFunction ℂ ↦ g n) heq

end BSD.RankTwo
