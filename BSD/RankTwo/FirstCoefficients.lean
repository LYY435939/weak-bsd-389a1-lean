import BSD.PrimeRecurrence
import BSD.RankTwo.CoefficientData
import BSD.RankTwo.GoodReduction
import BSD.RankTwo.PointCounts
import BSD.RankTwo.SmallEuler

/-! # The first eighteen Hasse–Weil coefficients of 389.a1 -/

namespace BSD.RankTwo

open NumberField Polynomial

private noncomputable abbrev place (p : Nat.Primes) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

private theorem prime_at_place (p : Nat.Primes) :
    (Rat.HeightOneSpectrum.primesEquiv (place p) : ℕ) = p :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)

private def CoefficientsAt (p : ℕ) (a : ℤ) : Prop :=
  curve.LFunction p = a ∧ ∀ k : ℕ, curve.LFunction (p^(k+2)) =
    a * curve.LFunction (p^(k+1)) - (p : ℤ) * curve.LFunction (p^k)

private theorem coefficients_of_polynomial (p : Nat.Primes) (a : ℤ)
    (hd : (curve.baseChange ((place p).adicCompletion ℚ)).localPolynomial
      ((place p).adicCompletionIntegers ℚ) = 1 - C a * X + C (p : ℤ) * X^2) :
    CoefficientsAt p a := by
  have h (k : ℕ) := BSD.weierstrass_LFunction_apply_prime_pow curve (place p) k
  simp only [prime_at_place, WeierstrassCurve.localPowerSeries, hd, Polynomial.coe_add,
    Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_pow] at h
  have hrec := BSD.reciprocal_quadratic_coefficients a (p : ℤ)
  constructor
  · simpa only [pow_one] using (h 1).trans hrec.1
  · intro k
    rw [h, h, h]
    exact hrec.2 k

private theorem coefficients_of_card {p : ℕ} (hp : p.Prime) (h₅ : 5 ≤ p) (hbad : p ≠ 389)
    {N : ℕ} (hc : Nat.card (model (ZMod p)).toAffine.Point = N) :
    CoefficientsAt p ((p : ℤ) + 1 - N) := by
  let P : Nat.Primes := ⟨p, hp⟩
  have hv : (Rat.HeightOneSpectrum.primesEquiv (place P) : ℕ) = p := prime_at_place P
  have hc' := (congrArg (fun q : ℕ ↦ Nat.card (model (ZMod q)).toAffine.Point) hv).trans hc
  apply coefficients_of_polynomial P
  have h := good_localPolynomial_rat (place P) (hv ▸ h₅) (hv ▸ hbad)
  dsimp only at h
  rw [hc', hv] at h
  exact h

theorem firstCoefficients_eq_LFunction (i : Fin 18) :
    curve.LFunction i = firstCoefficients i := by
  have hm := weierstrass_LFunction_isMultiplicative curve
  have h₁ := hm.map_one
  have h₂ : CoefficientsAt 2 (-2) := by
    let p : Nat.Primes := ⟨2, by decide⟩
    apply coefficients_of_polynomial p
    have h := localPolynomial_two_rat (place p) (prime_at_place p)
    simpa [p] using h
  have h₃ : CoefficientsAt 3 (-2) := by
    let p : Nat.Primes := ⟨3, by decide⟩
    apply coefficients_of_polynomial p
    have h := localPolynomial_three_rat (place p) (prime_at_place p)
    simpa [p] using h
  have h₅ : curve.LFunction 5 = -3 := (coefficients_of_card
    (by decide) (by decide) (by decide) card_points_five).1
  have h₇ : curve.LFunction 7 = -5 := (coefficients_of_card
    (by decide) (by decide) (by decide) card_points_seven).1
  have h₁₁ : curve.LFunction 11 = -4 := (coefficients_of_card
    (by decide) (by decide) (by decide) card_points_eleven).1
  have h₁₃ : curve.LFunction 13 = -3 := (coefficients_of_card
    (by decide) (by decide) (by decide) card_points_thirteen).1
  have h₁₇ : curve.LFunction 17 = -6 := (coefficients_of_card
    (by decide) (by decide) (by decide) card_points_seventeen).1
  have a₂ := h₂.1
  have a₃ := h₃.1
  have h₄ : curve.LFunction 4 = 2 := by
    have h := h₂.2 0; norm_num [a₂, h₁] at h; exact h
  have h₈ : curve.LFunction 8 = 0 := by
    have h := h₂.2 1; norm_num [a₂, h₄] at h; exact h
  have h₉ : curve.LFunction 9 = 1 := by
    have h := h₃.2 0; norm_num [a₃, h₁] at h; exact h
  have h₁₆ : curve.LFunction 16 = -4 := by
    have h := h₂.2 2; norm_num [h₄, h₈] at h; exact h
  have h₆ := hm.map_mul_of_coprime (by decide : Nat.Coprime 2 3)
  have h₁₀ := hm.map_mul_of_coprime (by decide : Nat.Coprime 2 5)
  have h₁₂ := hm.map_mul_of_coprime (by decide : Nat.Coprime 3 4)
  have h₁₄ := hm.map_mul_of_coprime (by decide : Nat.Coprime 2 7)
  have h₁₅ := hm.map_mul_of_coprime (by decide : Nat.Coprime 3 5)
  norm_num [a₂, a₃, h₄, h₅, h₇] at h₆ h₁₀ h₁₂ h₁₄ h₁₅
  fin_cases i <;> norm_num [firstCoefficients, h₁, a₂, a₃, h₄, h₅, h₆, h₇, h₈, h₉,
    h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇]

end BSD.RankTwo
