import BSD.General.ModularGoodModel
import BSD.General.ModularCorrectionAlgebra

/-! Quadratic inverse identities for the actual local coefficients over ℂ. -/

namespace BSD

open WeierstrassCurve

/-- Every actual local coefficient series has a quadratic inverse with second
coefficient either zero or the prime. -/
theorem weierstrass_LFunction_exists_quadratic (E : WeierstrassCurve ℚ)
    {p : ℕ} (hp : p.Prime) :
    ∃ t d : ℤ, (d = 0 ∨ d = (p : ℤ)) ∧
      PowerSeries.mk (fun k : ℕ => (E.LFunction (p^k) : ℂ)) *
        (1 - PowerSeries.C (t : ℂ) * PowerSeries.X +
          PowerSeries.C (d : ℂ) * PowerSeries.X ^ 2) = 1 := by
  classical
  let v := rationalPrimePlace p hp
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  let c : ℕ → ℂ := fun k => (E.LFunction (p^k) : ℂ)
  have hc₀ : c 0 = 1 := by
    have hm := (weierstrass_LFunction_isMultiplicative E).map_one
    simpa [c] using congrArg (fun z : ℤ => (z : ℂ)) hm
  by_cases hg : (W.minimal R).HasGoodReduction R
  · have hr := weierstrass_LFunction_prime_pow_recurrence_of_goodReduction E hp hg
    refine ⟨E.LFunction p, p, Or.inr rfl, ?_⟩
    change PowerSeries.mk c * _ = _
    apply BSD.General.powerSeries_mul_quadratic_eq_one c (E.LFunction p : ℂ) (p : ℂ) hc₀
    · simp [c]
    · intro k
      dsimp only [c]
      exact_mod_cast hr k
  · obtain ⟨t, _, ht⟩ := weierstrass_LFunction_prime_pow_of_badReduction E hp hg
    refine ⟨t, 0, Or.inl rfl, ?_⟩
    change PowerSeries.mk c * _ = _
    simp only [Int.cast_zero]
    apply BSD.General.powerSeries_mul_quadratic_eq_one c (t : ℂ) 0 hc₀
    · simpa [c] using congrArg (fun z : ℤ => (z : ℂ)) (ht 1)
    · intro k
      simp only [c, ht, Int.cast_pow, zero_mul, sub_zero]
      rw [pow_succ]
      ring

/-- At a good integral prime, the local inverse is the point-count polynomial. -/
theorem integralModel_local_complex_identity (I : WeierstrassCurve ℤ)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hdisc : ¬ (p : ℤ) ∣ I.Δ) :
    let E := I.map (Int.castRingHom ℚ)
    let t : ℤ := (p : ℤ) + 1 - Nat.card (I.map (Int.castRingHom (ZMod p))).toAffine.Point
    PowerSeries.mk (fun k : ℕ => (E.LFunction (p^k) : ℂ)) *
      (1 - PowerSeries.C (t : ℂ) * PowerSeries.X +
        PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2) = 1 := by
  classical
  dsimp only
  let E := I.map (Int.castRingHom ℚ)
  let t : ℤ := (p : ℤ) + 1 - Nat.card (I.map (Int.castRingHom (ZMod p))).toAffine.Point
  let c : ℕ → ℂ := fun k => (E.LFunction (p^k) : ℂ)
  have hc₀ : c 0 = 1 := by
    have hm := (weierstrass_LFunction_isMultiplicative E).map_one
    simpa [c] using congrArg (fun z : ℤ => (z : ℂ)) hm
  have hr := integralModel_prime_pow_recurrence I hp hp5 hdisc
  change E.LFunction p = t ∧ ∀ k : ℕ, E.LFunction (p^(k+2)) =
      t * E.LFunction (p^(k+1)) - (p : ℤ) * E.LFunction (p^k) at hr
  change PowerSeries.mk c * _ = _
  apply BSD.General.powerSeries_mul_quadratic_eq_one c (t : ℂ) (p : ℂ) hc₀
  · simpa [c] using congrArg (fun z : ℤ => (z : ℂ)) hr.1
  · intro k
    dsimp only [c]
    exact_mod_cast hr.2 k

end BSD
