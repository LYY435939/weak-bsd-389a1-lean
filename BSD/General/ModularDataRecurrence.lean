import BSD.General.ModularCorrectionAlgebra

/-!
Local inversion identities from normalized prime-power coefficient recurrences.
No modular-form or Euler-product assumptions are used in this algebraic layer.
-/

namespace BSD.General

/-- A normalized coefficient sequence satisfying the good-prime recurrence has the
expected quadratic local inverse. The hypothesis is just the recurrence; primality
of `p` is not needed for the formal identity. -/
theorem normalized_coefficients_good_local_inverse
    (a : ℕ → ℂ) (p : ℕ) (ha : a 1 = 1)
    (hrec : ∀ k : ℕ, a (p ^ (k + 2)) =
      a p * a (p ^ (k + 1)) - (p : ℂ) * a (p ^ k)) :
    PowerSeries.mk (fun k : ℕ => a (p ^ k)) *
      (1 - PowerSeries.C (a p) * PowerSeries.X +
        PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2) = 1 := by
  apply powerSeries_mul_quadratic_eq_one (fun k => a (p ^ k)) (a p) (p : ℂ)
  · simpa using ha
  · simp
  · exact hrec

/-- A normalized coefficient sequence satisfying the bad-prime recurrence has the
expected linear local inverse. -/
theorem normalized_coefficients_bad_local_inverse
    (a : ℕ → ℂ) (p : ℕ) (ha : a 1 = 1)
    (hrec : ∀ k : ℕ, a (p ^ (k + 1)) = a p * a (p ^ k)) :
    PowerSeries.mk (fun k : ℕ => a (p ^ k)) *
      (1 - PowerSeries.C (a p) * PowerSeries.X) = 1 := by
  have h := powerSeries_mul_quadratic_eq_one (fun k => a (p ^ k)) (a p) 0
    (by simpa using ha) (by simp) (by
      intro k
      simpa only [zero_mul, sub_zero, Nat.add_assoc] using hrec (k + 1))
  simpa using h

end BSD.General
