import BSD.General.ModularContinuationCore
import BSD.General.HasseElementaryLocal

/-! # Finite adjustments of elliptic-curve Euler factors -/

open scoped CongruenceSubgroup MatrixGroups

namespace BSD.General

/-- Comparing the formal local factors of a weight-two cusp form and a rational
Weierstrass curve yields a meromorphic continuation of the curve's own series. -/
theorem continues_quadraticCorrectedModularL (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : (cuspCoefficients f).IsMultiplicative)
    (S : Finset ℕ) (a₁ a₂ b₁ b₂ : ℕ → ℂ) (hS : ∀ p ∈ S, p.Prime)
    (hgood : ∀ p, p.Prime → p ∉ S → ∀ k : ℕ,
      (E.LFunction (p ^ k) : ℂ) = cuspCoefficients f (p ^ k))
    (hbadA : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ (E.LFunction (p ^ k) : ℂ)) *
      quadraticEulerPolynomial (a₁ p) (a₂ p) = 1)
    (hbadB : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ cuspCoefficients f (p ^ k)) *
      quadraticEulerPolynomial (b₁ p) (b₂ p) = 1) :
    Continues E (quadraticCorrectedModularL f S a₁ a₂ b₁ b₂) := by
  apply continues_quadraticCorrectedModularL_of_bound E f hf S a₁ a₂ b₁ b₂ hS hgood hbadA hbadB
  intro p hp k
  have hreal : |(E.LFunction (p ^ k) : ℝ)| ≤ ((p ^ k : ℕ) : ℝ) := by
    exact_mod_cast BSD.weierstrass_LFunction_abs_prime_pow_le_self E (hS p hp) k
  simpa only [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, Nat.cast_pow]
    using hreal

end BSD.General
