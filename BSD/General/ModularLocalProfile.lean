import BSD.PrimeRecurrence

/-! The actual local coefficients at good and bad finite places. -/

namespace BSD

open WeierstrassCurve IsDedekindDomain IsLocalRing NumberField Polynomial

/-- The finite place of `ℚ` corresponding to a rational prime. -/
noncomputable def rationalPrimePlace (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

private theorem prime_at_rationalPrimePlace (p : ℕ) (hp : p.Prime) :
    (Rat.HeightOneSpectrum.primesEquiv (rationalPrimePlace p hp) : ℕ) = p :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)

private theorem reciprocal_linear_coeff (a : ℤ) (k : ℕ) :
    (PowerSeries.invOfUnit (1 + PowerSeries.C a * PowerSeries.X) 1).coeff k = (-a)^k := by
  let D : PowerSeries ℤ := 1 + PowerSeries.C a * PowerSeries.X
  let f := PowerSeries.invOfUnit D 1
  have hDf : D * f = 1 := PowerSeries.mul_invOfUnit D 1 (by simp [D])
  have hzero : f.coeff 0 = 1 := by
    simp [f, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_invOfUnit]
  have hrec (j : ℕ) : f.coeff (j + 1) = -(a * f.coeff j) := by
    have h := congrArg (PowerSeries.coeff (j + 1)) hDf
    simp only [D, add_mul, mul_assoc, one_mul, map_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false] at h
    linarith
  change f.coeff k = (-a)^k
  induction k with
  | zero => simpa using hzero
  | succ j ih => rw [hrec, ih, pow_succ]; ring

/-- Bad reduction gives a geometric sequence with ratio 1, -1, or 0. -/
theorem weierstrass_LFunction_prime_pow_of_badReduction (E : WeierstrassCurve ℚ)
    {p : ℕ} (hp : p.Prime)
    (hbad : ¬((E.baseChange ((rationalPrimePlace p hp).adicCompletion ℚ)).minimal
      ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)).HasGoodReduction
      ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)) :
    ∃ t : ℤ, |t| ≤ 1 ∧ ∀ k : ℕ, E.LFunction (p^k) = t^k := by
  classical
  let v := rationalPrimePlace p hp
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  change ¬(W.minimal R).HasGoodReduction R at hbad
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := prime_at_rationalPrimePlace p hp
  have hcoeff (k : ℕ) := weierstrass_LFunction_apply_prime_pow E v k
  rw [hv] at hcoeff
  have hlin (a : ℤ) (hpoly : W.localPolynomial R = 1 + C a * X) :
      ∀ k : ℕ, E.LFunction (p^k) = (-a)^k := by
    intro k
    rw [hcoeff k]
    change (W.localPowerSeries R).coeff k = _
    rw [localPowerSeries, hpoly]
    simpa only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X] using reciprocal_linear_coeff a k
  have hpoly : W.localPolynomial R = 1 - X ∨ W.localPolynomial R = 1 + X ∨
      W.localPolynomial R = 1 := by
    simp only [localPolynomial, if_neg hbad]
    split_ifs <;> simp
  rcases hpoly with h | h | h
  · refine ⟨1, by norm_num, ?_⟩
    simpa using hlin (-1) (by simpa [sub_eq_add_neg] using h)
  · refine ⟨-1, by norm_num, ?_⟩
    simpa using hlin 1 (by simpa using h)
  · refine ⟨0, by norm_num, ?_⟩
    simpa using hlin 0 (by simpa using h)

/-- At a good place the real Hasse–Weil coefficients satisfy the quadratic recurrence. -/
theorem weierstrass_LFunction_prime_pow_recurrence_of_goodReduction
    (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime)
    (hg : ((E.baseChange ((rationalPrimePlace p hp).adicCompletion ℚ)).minimal
      ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)).HasGoodReduction
      ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)) :
    ∀ k : ℕ, E.LFunction (p^(k+2)) = E.LFunction p * E.LFunction (p^(k+1)) -
      (p : ℤ) * E.LFunction (p^k) := by
  classical
  let v := rationalPrimePlace p hp
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  change (W.minimal R).HasGoodReduction R at hg
  let P := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (P : ℕ).Prime := ⟨P.2⟩
  let e : ResidueField R ≃+* ZMod P :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  have hq : Nat.card (ResidueField R) = p := by
    rw [(Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)]
    exact prime_at_rationalPrimePlace p hp
  let a : ℤ := -((p : ℤ) + 1 - Nat.card ((W.minimal R).reduction R).toAffine.Point)
  have hpoly : W.localPolynomial R = 1 + C a * X + C (p : ℤ) * X ^ 2 := by
    simp only [localPolynomial, if_pos hg, hq, a, map_neg, neg_mul, sub_eq_add_neg]
  have hpoly' : W.localPolynomial R = 1 - C (-a) * X + C (p : ℤ) * X^2 := by
    simpa only [map_neg, neg_mul, sub_neg_eq_add] using hpoly
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := prime_at_rationalPrimePlace p hp
  have h (k : ℕ) := weierstrass_LFunction_apply_prime_pow E v k
  rw [hv] at h
  change ∀ k : ℕ, E.LFunction (p^k) = (W.localPowerSeries R).coeff k at h
  simp only [localPowerSeries, hpoly', Polynomial.coe_add,
    Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_pow] at h
  have hrec := reciprocal_quadratic_coefficients (-a) (p : ℤ)
  have hfirst : E.LFunction p = -a := by simpa only [pow_one] using (h 1).trans hrec.1
  intro k
  rw [hfirst, h, h, h]
  exact hrec.2 k

end BSD
