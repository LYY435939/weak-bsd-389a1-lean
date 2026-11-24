import BSD.CoefficientCriterion
import Mathlib.Data.Nat.Factorization.Induction

/-! # Recovering a Dirichlet coefficient sequence from its prime recurrences -/

namespace BSD

/-- A sequence with a prescribed prime recurrence is determined by the underlying
multiplicative function. The candidate sequence need not be known to be multiplicative. -/
theorem eq_of_prime_recurrences {R : Type*} [CommRing R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (T : ℕ → R) (A B : Nat.Primes → R)
    (hf₁ : ∀ p : Nat.Primes, f p = A p)
    (hf₂ : ∀ (p : Nat.Primes) (k : ℕ), f ((p : ℕ) ^ (k+2)) =
      A p * f ((p : ℕ) ^ (k+1)) - B p * f ((p : ℕ) ^ k))
    (h₀ : T 0 = 0) (h₁ : T 1 = 1)
    (hfirst : ∀ (p : Nat.Primes) (m : ℕ), ¬(p : ℕ) ∣ m → T (p*m) = A p * T m)
    (hrec : ∀ (p : Nat.Primes) (m : ℕ), T (p*(p*m)) = A p * T (p*m) - B p * T m) :
    ∀ n, T n = f n := by
  refine Nat.recOnPrimePow (by simpa using h₀) (by simpa [hf.1] using h₁) ?_
  intro m p k hp hm _ ih
  let P : Nat.Primes := ⟨p, hp⟩
  have hpow (j : ℕ) : T (p ^ j * m) = f (p ^ j) * T m := by
    induction j using Nat.twoStepInduction with
    | zero => simp [hf.1]
    | one =>
      simpa only [pow_one, ← hf₁ P] using hfirst P m hm
    | more j hj hj' =>
      have h := hrec P (p ^ j * m)
      change T (p * (p * (p ^ j * m))) = A P * T (p * (p ^ j * m)) - B P * T (p ^ j * m) at h
      rw [show p * (p ^ j * m) = p ^ (j+1)*m by ring,
        show p * (p ^ (j+1)*m) = p ^ (j+2)*m by ring, hj, hj'] at h
      rw [h, hf₂ P j]
      ring
  rw [hpow, ih, hf.2 ((hp.coprime_iff_not_dvd.mpr hm).pow_left k)]

namespace FermatCubic

noncomputable def primeTrace (p : Nat.Primes) : ℤ :=
  if (p : ℕ) = 3 ∨ (p : ℕ) % 3 = 2 then 0 else primaryTrace p

def primeDet (p : Nat.Primes) : ℤ := if (p : ℕ) = 3 then 0 else p

private lemma eulerDenominator_as_series (p : Nat.Primes) :
    (eulerDenominator p : PowerSeries ℤ) =
      1 - PowerSeries.C (primeTrace p) * PowerSeries.X +
        PowerSeries.C (primeDet p) * PowerSeries.X ^ 2 := by
  classical
  unfold eulerDenominator primeTrace primeDet
  split_ifs <;>
    simp only [Polynomial.coe_one, Polynomial.coe_sub, Polynomial.coe_add,
      Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C,
      map_zero, zero_mul, sub_zero, add_zero] <;> tauto

private lemma coeff_reciprocal_quadratic (a b : ℤ) :
    let D := 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C b * PowerSeries.X ^ 2
    let F := PowerSeries.invOfUnit D 1
    F.coeff 1 = a ∧ ∀ k : ℕ, F.coeff (k+2) = a * F.coeff (k+1) - b * F.coeff k := by
  intro D F
  have hD : D * F = 1 := PowerSeries.mul_invOfUnit _ _ (by simp [D])
  have h₀ : F.coeff 0 = 1 := by simp [F, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [show D * F = F - PowerSeries.C a * (PowerSeries.X * F) +
      PowerSeries.C b * (PowerSeries.X ^ 2 * F) by dsimp [D]; ring] at hD
  constructor
  · have h := congrArg (PowerSeries.coeff 1) hD
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one, h₀] at h
    norm_num at h
    linarith
  · intro k
    have h := congrArg (PowerSeries.coeff (k+2)) hD
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_one, Nat.add_eq_zero_iff] at h
    norm_num at h
    linarith

theorem prime_recurrence (p : Nat.Primes) :
    curve.LFunction p = primeTrace p ∧ ∀ k : ℕ,
      curve.LFunction ((p : ℕ) ^ (k+2)) =
        primeTrace p * curve.LFunction ((p : ℕ) ^ (k+1)) -
          primeDet p * curve.LFunction ((p : ℕ) ^ k) := by
  have h := coeff_reciprocal_quadratic (primeTrace p) (primeDet p)
  constructor
  · have h₁ := coefficient_prime_power p 1
    rw [pow_one, eulerDenominator_as_series] at h₁
    exact h₁.trans h.1
  · intro k
    simp only [coefficient_prime_power, eulerDenominator_as_series]
    exact h.2 k

end FermatCubic

/-- Coefficients of the reciprocal of a quadratic Euler denominator. -/
alias reciprocal_quadratic_coefficients := FermatCubic.coeff_reciprocal_quadratic

end BSD
