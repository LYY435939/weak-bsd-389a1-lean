import BSD.RankTwo.Curve
import BSD.InertPrimes
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # The split multiplicative place of 389.a1 -/

namespace BSD.RankTwo

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

private lemma model_c₄ {R : Type*} [CommRing R] : (model R).c₄ = 112 := by
  simp only [model, c₄, b₂, b₄]
  ring

private lemma model_c₆ {R : Type*} [CommRing R] : (model R).c₆ = -856 := by
  simp only [model, c₆, b₂, b₄, b₆]
  ring

open Polynomial in
private lemma tangent_splits {F : Type*} [Field F] (W : WeierstrassCurve F)
    (h2 : (2 : F) ≠ 0) (ha : W.c₄ ≠ 0) (z : F) (hz : z ^ 2 = -W.c₄ * W.c₆) :
    Splits (C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X -
      C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  have hdisc : (W.a₁ * W.c₄) ^ 2 + 4 * W.c₄ *
      (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) = -W.c₄ * W.c₆ := by
    simp only [c₄, c₆, b₂, b₄, b₆]
    ring
  apply Splits.of_natDegree_eq_two (x := (-W.a₁ * W.c₄ + z) / (2 * W.c₄))
  · compute_degree!
  · simp only [eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    field_simp
    linear_combination hz - hdisc

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]

open Polynomial in
private theorem localPolynomial_of_residue389 (e : ResidueField R ≃+* ZMod 389) :
    (model K).localPolynomial R = 1 - X := by
  let : Fact (Nat.Prime 389) := ⟨by norm_num⟩
  let I := model R
  let W := model K
  have hI : I.baseChange K = W := by
    ext <;> simp [I, W, model, baseChange, map_ofNat]
  have : W.IsIntegral R := ⟨⟨I, hI.symm⟩⟩
  let V := W.minimal R
  let J := V.integralModel R
  let D := (W.exists_isMinimal R).choose
  let k := (↑D.u⁻¹ : K)
  let f := e.toRingHom.comp (residue R)
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have hID : algebraMap R K I.Δ = W.Δ := by rw [← hI, baseChange, map_Δ]
  have hIC : algebraMap R K I.c₄ = W.c₄ := by rw [← hI, baseChange, map_c₄]
  have hunit : IsUnit I.c₄ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro h
    have hx := congrArg e h
    rw [model_c₄, map_ofNat, map_ofNat, map_zero] at hx
    exact (by decide : (112 : ZMod 389) ≠ 0) hx
  have hJC : algebraMap R K J.c₄ = k ^ 4 * W.c₄ :=
    (integralModel_c₄_eq R V).trans (variableChange_c₄ W D)
  have hk : _root_.IsIntegral R (k ^ 4) := by
    apply IsIntegrallyClosed.isIntegral_iff.mpr
    refine ⟨J.c₄ * ↑hunit.unit⁻¹, ?_⟩
    rw [map_mul, hJC, ← hIC, mul_assoc, ← map_mul]
    have hh : I.c₄ * ↑hunit.unit⁻¹ = 1 :=
      (congrArg (fun v : R => v * ↑hunit.unit⁻¹) hunit.unit_spec.symm).trans hunit.unit.mul_inv
    rw [hh, map_one, mul_one]
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by decide : 0 < 4) hk
  have hΔ : V.Δ = k ^ 12 * W.Δ := variableChange_Δ W D
  have hWD : w W.Δ ≠ 0 := (map_ne_zero w).mpr (by rw [discriminant]; norm_num)
  have hwle : w k ≤ 1 := by rw [← hd]; exact valuation_le_one _ _
  have hle : w V.Δ ≤ w W.Δ := by
    rw [hΔ, map_mul, map_pow]
    exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hwle)
  have hUndo : D⁻¹ • V = W := by
    change D⁻¹ • (D • W) = W
    rw [← mul_smul, inv_mul_cancel, one_smul]
  have hmax : w W.Δ ≤ w V.Δ := by
    have hInt : (D⁻¹ • V).IsIntegral R := hUndo ▸ (inferInstance : W.IsIntegral R)
    have hh : valuation_Δ_aux R ((1 : VariableChange K) • V) ≤
        valuation_Δ_aux R (D⁻¹ • V) := by
      rw [one_smul, hUndo]
      exact (show (valuation_Δ_aux R V).val ≤ (valuation_Δ_aux R W).val by
        simpa only [valuation_Δ_aux_eq_of_isIntegral R V, valuation_Δ_aux_eq_of_isIntegral R W]
          using hle)
    have ht := (inferInstance : V.IsMinimal R).val_Δ_maximal.2 hInt hh
    change valuation_Δ_aux R (D⁻¹ • V) ≤ valuation_Δ_aux R ((1 : VariableChange K) • V) at ht
    rw [one_smul, hUndo] at ht
    change (valuation_Δ_aux R W).val ≤ (valuation_Δ_aux R V).val at ht
    simpa only [valuation_Δ_aux_eq_of_isIntegral R V, valuation_Δ_aux_eq_of_isIntegral R W]
      using ht
  have hwk : w k = 1 := by
    have hh := le_antisymm hle hmax
    rw [hΔ, map_mul, map_pow] at hh
    apply (pow_eq_one_iff_of_nonneg (zero_le : 0 ≤ w k) (by decide : 12 ≠ 0)).mp
    exact (mul_left_inj' hWD).mp (hh.trans (one_mul _).symm)
  have hw2 (a : R) : w (algebraMap R K a) = 1 ↔ f a ≠ 0 := by
    rw [valuation_eq_one_iff_notMem]
    simp [f, residue_eq_zero_iff, IsDiscreteValuationRing.maximalIdeal]
  have hd0 : f d ≠ 0 := (hw2 d).mp (hd ▸ hwk)
  have hJC4 : J.c₄ = d ^ 4 * 112 := by
    apply IsFractionRing.injective R K
    rw [hJC, map_mul, map_pow, hd, map_ofNat, model_c₄]
  have hJC6 : J.c₆ = d ^ 6 * -856 := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₆_eq, map_mul, map_pow, hd, map_neg, map_ofNat]
    exact (variableChange_c₆ W D).trans (by rw [model_c₆])
  have hc : f J.c₄ ≠ 0 := by
    rw [hJC4, map_mul, map_pow, map_ofNat]
    exact mul_ne_zero (pow_ne_zero _ hd0) (by decide)
  have hbad : w V.Δ < 1 := by
    rw [le_antisymm hle hmax, ← hID]
    apply lt_of_le_of_ne (valuation_le_one _ _)
    intro hh
    apply (hw2 I.Δ).mp hh
    rw [discriminant, map_ofNat]
    decide
  have hm : V.HasMultiplicativeReduction R := ⟨hbad, by
    rw [← integralModel_c₄_eq R V]
    exact (hw2 J.c₄).mpr hc⟩
  have hs : V.HasSplitMultiplicativeReduction R := by
    refine { toHasMultiplicativeReduction := hm, splitMultiplicativeReduction := ?_ }
    let T := J.map f
    have hT : T.c₄ ≠ 0 := by rw [show T.c₄ = _ from map_c₄ _ _]; exact hc
    have hsq : (87 * (f d) ^ 5) ^ 2 = -T.c₄ * T.c₆ := by
      rw [show T.c₄ = _ from map_c₄ _ _, show T.c₆ = _ from map_c₆ _ _, hJC4, hJC6]
      simp only [map_mul, map_pow, map_neg, map_ofNat]
      have h87 : (87 : ZMod 389) ^ 2 = 112 * 856 := by decide
      linear_combination (f d) ^ 10 * h87
    have hS := tangent_splits T (by decide) hT _ hsq
    have hmap := hS.map e.symm.toRingHom
    simpa [T, f, J, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, map_ofNat] using hmap
  classical
  change W.localPolynomial R = _
  unfold localPolynomial
  rw [if_neg (hm.not_hasGoodReduction R), if_pos hs]

end Local

open NumberField Polynomial in
/-- The Euler polynomial of the actual minimal model at the place over the bad prime 389. -/
theorem bad_localPolynomial_rat (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 389) :
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) = 1 - X := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let ep : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  calc
    _ = (model K).localPolynomial R := by
      apply congrArg (fun W : WeierstrassCurve K => W.localPolynomial R)
      ext <;> simp [curve, model, baseChange]
    _ = _ := localPolynomial_of_residue389 R K (ep.trans (ZMod.ringEquivCongr hv))

end BSD.RankTwo
