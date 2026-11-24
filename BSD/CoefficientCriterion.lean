import BSD.EulerCoefficients
import BSD.FermatCubic
import BSD.LocalFactors

/-! # A coefficient test for the Fermat cubic

Both inputs to the last theorem concern the integer coefficients of the eta
product. On the arithmetic side every local polynomial is already determined.
-/

namespace BSD.FermatCubic

open NumberField

noncomputable def etaArithmetic : ArithmeticFunction ℤ :=
  ⟨EtaSupport.etaCoeff, EtaSupport.etaCoeff_support 0 (by decide)⟩

/-- The k-th prime-power coefficient, expressed purely in terms of the
reciprocal of the explicit polynomial for the natural prime. -/
theorem coefficient_prime_power (p : Nat.Primes) (k : ℕ) :
    curve.LFunction ((p : ℕ) ^ k) =
      ((eulerDenominator p : PowerSeries ℤ).invOfUnit 1).coeff k := by
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let v := e.symm p
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = (p : ℕ) :=
    congrArg Subtype.val (e.apply_symm_apply p)
  have h := BSD.weierstrass_LFunction_apply_prime_pow curve v k
  rw [WeierstrassCurve.localPowerSeries, localPolynomial_eq_eulerDenominator, hv] at h
  exact h

/-- The global coefficient comparison is equivalent to multiplicativity
and explicit prime-power identities for the integral eta coefficients. -/
theorem etaArithmetic_eq_iff :
    etaArithmetic = curve.LFunction ↔ etaArithmetic.IsMultiplicative ∧
      ∀ (p : Nat.Primes) (k : ℕ), EtaSupport.etaCoeff ((p : ℕ) ^ k) =
        ((eulerDenominator p : PowerSeries ℤ).invOfUnit 1).coeff k := by
  constructor
  · intro h
    refine ⟨h ▸ BSD.weierstrass_LFunction_isMultiplicative curve, fun p k ↦ ?_⟩
    change etaArithmetic ((p : ℕ) ^ k) = _
    rw [h, coefficient_prime_power]
  · rintro ⟨hm, hl⟩
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
      hm _ (BSD.weierstrass_LFunction_isMultiplicative curve)).2
    intro p k hp
    exact (hl ⟨p,hp⟩ k).trans (coefficient_prime_power ⟨p,hp⟩ k).symm

/-- A sufficient criterion for the individual rank statement at 27.a3.
The two arithmetic hypotheses are explicit proof obligations. -/
theorem rankPart_of_eta_euler_factors (hm : etaArithmetic.IsMultiplicative)
    (hl : ∀ (p : Nat.Primes) (k : ℕ), EtaSupport.etaCoeff ((p : ℕ) ^ k) =
      ((eulerDenominator p : PowerSeries ℤ).invOfUnit 1).coeff k) : RankPart curve := by
  have h := etaArithmetic_eq_iff.mpr ⟨hm, hl⟩
  apply rankPart_of_coefficient_identity
  intro n
  exact congrArg (fun f : ArithmeticFunction ℤ ↦ f n) h.symm

end BSD.FermatCubic
