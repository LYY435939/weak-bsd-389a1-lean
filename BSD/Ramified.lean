import BSD.InertPrimes

/-! # The Euler polynomial at the ramified prime 3 -/

namespace BSD.FermatCubic

open NumberField WeierstrassCurve WithZero IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

private lemma rationalPlace_valuation_prime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers ℚ)).valuation
      (v.adicCompletion ℚ) (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = exp (-1 : ℤ) := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let : CharZero R := e.toRingHom.charZero
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)} := by
    calc
      IsLocalRing.maximalIdeal R = (IsLocalRing.maximalIdeal _).map e.symm := by
        rw [IsLocalRing.map_ringEquiv_maximalIdeal]
      _ = Ideal.span {(p : R)} := by
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton]
        rw [map_natCast]
  change (IsDiscreteValuationRing.maximalIdeal R).valuation K (p : K) = exp (-1 : ℤ)
  rw [← map_natCast (algebraMap R K) (p : ℕ), valuation_of_algebraMap]
  exact intValuation_singleton _ (Nat.cast_ne_zero.mpr p.2.ne_zero) hmax

/-- The Euler polynomial of the Fermat model at the place over 3 is 1.
The discriminant exponent 9 stays congruent to 9 modulo 12 under every
Weierstrass variable change, and the invariant `c₄` remains zero. -/
theorem fermatCubic_localPolynomial_three_rat
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 3) :
    ((mordellModel (-(432 : ℚ))).baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ) = 1 := by
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  let W := mordellModel (-(432 : K))
  have hW : (mordellModel (-(432 : ℚ))).baseChange K = W := by
    ext <;> simp [baseChange, mordellModel, W]
  change ((mordellModel (-(432 : ℚ))).baseChange K).localPolynomial R = 1
  rw [hW]
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let V := W.minimal R
  let C := (W.exists_isMinimal R).choose
  have h3 : w 3 = exp (-1 : ℤ) := by
    simpa only [hv, Nat.cast_ofNat] using rationalPlace_valuation_prime v
  have hΔ : V.Δ = -(((↑C.u⁻¹ : K) * 2) ^ 12 * 3 ^ 9) := by
    change (C • W).Δ = _
    rw [variableChange_Δ, mordell_discriminant]
    norm_num
    ring
  have hc₄ : V.c₄ = 0 := by
    change (C • W).c₄ = 0
    rw [variableChange_c₄]
    simp [W, mordellModel, c₄, b₂, b₄]
  have hbad : w V.Δ < 1 := by
    have hle : w V.Δ ≤ 1 := by
      obtain ⟨d, hd⟩ := Δ_integral_of_isIntegral R V
      rw [← hd]
      exact valuation_le_one _ _
    refine lt_of_le_of_ne hle ?_
    intro h
    have hx : w ((↑C.u⁻¹ : K) * 2) ≠ 0 := by
      exact (map_ne_zero w).mpr (mul_ne_zero (Units.ne_zero _) (by norm_num))
    rw [hΔ, w.map_neg, map_mul, map_pow, map_pow, h3, ← exp_log hx,
      ← exp_nsmul, ← exp_nsmul, ← exp_add, exp_eq_one] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
    omega
  have hadd : V.HasAdditiveReduction R := ⟨hbad, by simp [hc₄, zero_lt_one]⟩
  have hnotmult := HasAdditiveReduction.not_hasMultiplicativeReduction R hadd
  have hsplit : ¬ V.HasSplitMultiplicativeReduction R :=
    fun h => hnotmult h.toHasMultiplicativeReduction
  classical
  unfold localPolynomial
  rw [if_neg (HasAdditiveReduction.not_hasGoodReduction R hadd), if_neg hsplit, if_neg hnotmult]

end BSD.FermatCubic
