import BSD.General.ModularContinuationCore
import BSD.General.ModularDataRecurrence

/-! # Normalized modular coefficient data

This is an explicit data boundary matching the coefficient fields of FLT's
`CuspForm.IsNormalizedEigenform`. It does not assert the existence of such a
form or a modularity theorem for a given elliptic curve.
-/

namespace BSD.General

/-- Coefficient properties of a normalized weight-two Hecke eigenform. -/
structure ModularCoefficientData {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop where
  qCoeff_one : cuspCoefficients f 1 = 1
  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    cuspCoefficients f (m * n) = cuspCoefficients f m * cuspCoefficients f n
  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    cuspCoefficients f (p ^ (r + 2)) =
      cuspCoefficients f p * cuspCoefficients f (p ^ (r + 1)) -
        (p : ℂ) * cuspCoefficients f (p ^ r)
  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    cuspCoefficients f (p ^ (r + 2)) =
      cuspCoefficients f p * cuspCoefficients f (p ^ (r + 1))

namespace ModularCoefficientData

variable {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}

theorem isMultiplicative (h : ModularCoefficientData f) :
    (cuspCoefficients f).IsMultiplicative := by
  exact ⟨h.qCoeff_one, fun {m n} hmn => h.qCoeff_mul_of_coprime m n hmn⟩

theorem inverse_good (h : ModularCoefficientData f) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    PowerSeries.mk (fun k : ℕ => cuspCoefficients f (p ^ k)) *
      quadraticEulerPolynomial (cuspCoefficients f p) (p : ℂ) = 1 := by
  simpa only [quadraticEulerPolynomial] using
    normalized_coefficients_good_local_inverse (cuspCoefficients f) p h.qCoeff_one
      (fun r => h.qCoeff_prime_pow_of_not_dvd p r hp hpN)

theorem inverse_bad (h : ModularCoefficientData f) {p : ℕ}
    (hp : p.Prime) (hpN : p ∣ N) :
    PowerSeries.mk (fun k : ℕ => cuspCoefficients f (p ^ k)) *
      quadraticEulerPolynomial (cuspCoefficients f p) 0 = 1 := by
  have hrec : ∀ k : ℕ, cuspCoefficients f (p ^ (k + 1)) =
      cuspCoefficients f p * cuspCoefficients f (p ^ k) := by
    intro k
    cases k with
    | zero => simp [h.qCoeff_one]
    | succ k =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        h.qCoeff_prime_pow_of_dvd p k hp hpN
  simpa [quadraticEulerPolynomial] using
    normalized_coefficients_bad_local_inverse (cuspCoefficients f) p h.qCoeff_one hrec

end ModularCoefficientData
end BSD.General
