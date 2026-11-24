import BSD.General.ModularLocalProfile
import BSD.RankTwo.GoodReduction

/-! A good integral model computes the local factor of its rational generic fibre. -/

namespace BSD

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing NumberField Polynomial

/-- Away from 2, 3 and the discriminant, the actual local polynomial of the
rational generic fibre is given by the point count of the integral equation. -/
theorem integralModel_localPolynomial_at_good_prime (I : WeierstrassCurve ℤ)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hdisc : ¬ (p : ℤ) ∣ I.Δ) :
    let v := rationalPrimePlace p hp
    (((I.map (Int.castRingHom ℚ)).baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ)) =
      1 - C ((p : ℤ) + 1 - Nat.card (I.map (Int.castRingHom (ZMod p))).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  classical
  dsimp only
  let v := rationalPrimePlace p hp
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let J := I.map (Int.castRingHom R)
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)
  let e : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      (PadicInt.residueField.trans (ZMod.ringEquivCongr hv))
  have hunit : IsUnit J.Δ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hz
    have hz' : (I.Δ : ZMod p) = 0 := by
      have h := congrArg e hz
      simpa [J, map_Δ] using h
    exact hdisc ((ZMod.intCast_zmod_eq_zero_iff_dvd I.Δ p).mp hz')
  have h := BSD.RankTwo.localPolynomial_of_good_model R K hp5 e J hunit
  have hfiber : J.baseChange K = (I.map (Int.castRingHom ℚ)).baseChange K := by
    ext <;> simp [J, baseChange, WeierstrassCurve.map_map]
  have hred : J.map (e.toRingHom.comp (residue R)) = I.map (Int.castRingHom (ZMod p)) := by
    ext <;> simp [J, WeierstrassCurve.map_map]
  rw [hfiber, hred] at h
  exact h

/-- The first coefficient and all prime-power recurrences computed from the
point count of a good integral model. -/
theorem integralModel_prime_pow_recurrence (I : WeierstrassCurve ℤ)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hdisc : ¬ (p : ℤ) ∣ I.Δ) :
    let E := I.map (Int.castRingHom ℚ)
    let t : ℤ := (p : ℤ) + 1 - Nat.card (I.map (Int.castRingHom (ZMod p))).toAffine.Point
    E.LFunction p = t ∧ ∀ k : ℕ, E.LFunction (p^(k+2)) =
      t * E.LFunction (p^(k+1)) - (p : ℤ) * E.LFunction (p^k) := by
  classical
  dsimp only
  let E := I.map (Int.castRingHom ℚ)
  let v := rationalPrimePlace p hp
  let t : ℤ := (p : ℤ) + 1 - Nat.card (I.map (Int.castRingHom (ZMod p))).toAffine.Point
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)
  have hpoly := integralModel_localPolynomial_at_good_prime I hp hp5 hdisc
  change (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
    1 - C t * X + C (p : ℤ) * X^2 at hpoly
  have h (k : ℕ) := weierstrass_LFunction_apply_prime_pow E v k
  simp only [hv, localPowerSeries, hpoly, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_one, Polynomial.coe_X,
    Polynomial.coe_pow] at h
  have hr := reciprocal_quadratic_coefficients t (p : ℤ)
  constructor
  · simpa only [pow_one] using (h 1).trans hr.1
  · intro k
    rw [h, h, h]
    exact hr.2 k

end BSD
