import BSD.General.ModularGoodModel

/-! Good Euler factors for rationally equivalent integral models. -/
namespace BSD
open WeierstrassCurve IsLocalRing IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open BSD.FermatCubic (card_points_map card_points_smul_of_u_eq_one zmod_two_three_ne_zero)

private theorem short_equation {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsShortNF] (x y : F) : W.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  rw [Affine.equation_iff]
  simp

private theorem card_short_scale {F : Type*} [Field F]
    (S T : WeierstrassCurve F) [S.IsShortNF] [T.IsShortNF] [S.IsElliptic] [T.IsElliptic]
    (d : F) (hd : d ≠ 0) (h₄ : S.a₄ = d ^ 4 * T.a₄) (h₆ : S.a₆ = d ^ 6 * T.a₆) :
    Nat.card S.toAffine.Point = Nat.card T.toAffine.Point := by
  let eXY : F × F ≃ F × F :=
    { toFun := fun (x, y) => (d ^ 2 * x, d ^ 3 * y)
      invFun := fun (x, y) => (x / d ^ 2, y / d ^ 3)
      left_inv := by intro ⟨x,y⟩; apply Prod.ext <;> dsimp <;> field_simp
      right_inv := by intro ⟨x,y⟩; apply Prod.ext <;> dsimp <;> field_simp }
  have he (xy : F × F) : T.toAffine.Equation xy.1 xy.2 ↔
      S.toAffine.Equation (eXY xy).1 (eXY xy).2 := by
    rw [short_equation, short_equation, h₄, h₆]
    dsimp [eXY]
    convert (mul_right_inj' (pow_ne_zero 6 hd) :
      d ^ 6 * xy.2 ^ 2 = d ^ 6 * (xy.1 ^ 3 + T.a₄ * xy.1 + T.a₆) ↔ _) |>.symm using 2 <;> ring
  exact Nat.card_congr ((T.toAffine.pointEquiv.trans (eXY.subtypeEquiv he).optionCongr).trans
    S.toAffine.pointEquiv.symm).symm

private theorem card_of_scaled_invariants {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (W V : WeierstrassCurve (ZMod p)) [W.IsElliptic] [V.IsElliptic] (d : ZMod p) (hd : d ≠ 0)
    (hc₄ : W.c₄ = d ^ 4 * V.c₄) (hc₆ : W.c₆ = d ^ 6 * V.c₆) :
    Nat.card W.toAffine.Point = Nat.card V.toAffine.Point := by
  obtain ⟨h2, h3⟩ := zmod_two_three_ne_zero hp
  let := invertibleOfNonzero h2
  let := invertibleOfNonzero h3
  let S := W.toShortNF • W
  let T := V.toShortNF • V
  have hu (U : WeierstrassCurve (ZMod p)) : U.toShortNF.u = 1 := by
    simp [toShortNF, VariableChange.mul_def]
  have h48 : (-48 : ZMod p) ≠ 0 := by
    rw [show (-48 : ZMod p) = -(2 : ZMod p) ^ 4 * 3 by norm_num]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) h3
  have h864 : (-864 : ZMod p) ≠ 0 := by
    rw [show (-864 : ZMod p) = -(2 : ZMod p) ^ 5 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) (pow_ne_zero _ h3)
  have hs₄ : S.c₄ = d ^ 4 * T.c₄ := by
    simpa only [S, T, variableChange_c₄, hu, inv_one, Units.val_one, one_pow, one_mul] using hc₄
  have hs₆ : S.c₆ = d ^ 6 * T.c₆ := by
    simpa only [S, T, variableChange_c₆, hu, inv_one, Units.val_one, one_pow, one_mul] using hc₆
  rw [c₄_of_isShortNF, c₄_of_isShortNF] at hs₄
  rw [c₆_of_isShortNF, c₆_of_isShortNF] at hs₆
  calc
    Nat.card W.toAffine.Point = Nat.card S.toAffine.Point :=
      card_points_smul_of_u_eq_one W _ (hu W)
    _ = Nat.card T.toAffine.Point := by
      apply card_short_scale S T d hd
      · apply (mul_right_inj' h48).mp
        linear_combination hs₄
      · apply (mul_right_inj' h864).mp
        linear_combination hs₆
    _ = _ := (card_points_smul_of_u_eq_one V _ (hu V)).symm

private lemma minimal_good_from_equivalent
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (V : WeierstrassCurve K) [V.IsMinimal R] (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsIntegral R] (hCW : C • V = W)
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ = 1) :
    V.HasGoodReduction R := by
  have hW : (valuation_Δ_aux R W).val = 1 :=
    (valuation_Δ_aux_eq_of_isIntegral R W).trans h
  have hle : valuation_Δ_aux R V ≤ valuation_Δ_aux R W := by
    change (valuation_Δ_aux R V).val ≤ (valuation_Δ_aux R W).val
    rw [hW]
    exact (valuation_Δ_aux R V).prop
  have hle' : valuation_Δ_aux R W ≤ valuation_Δ_aux R V := by
    have hInt : (C • V).IsIntegral R := hCW ▸ (inferInstance : W.IsIntegral R)
    have hLeChange : valuation_Δ_aux R ((1 : VariableChange K) • V) ≤
        valuation_Δ_aux R (C • V) := by simpa only [one_smul, hCW]
    simpa only [one_smul, hCW] using (inferInstance : V.IsMinimal R).val_Δ_maximal.2 hInt hLeChange
  refine HasGoodReduction.mk ?_
  rw [← valuation_Δ_aux_eq_of_isIntegral R V, le_antisymm hle hle', hW]

section Local
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
open Polynomial in
theorem localPolynomial_of_equivalent_good_model {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (e : ResidueField R ≃+* ZMod p) (I : WeierstrassCurve R) (hunit : IsUnit I.Δ)
    (E : WeierstrassCurve K) (A : VariableChange K) (hA : A • E = I.baseChange K) :
    E.localPolynomial R =
      1 - C ((p : ℤ) + 1 - Nat.card (I.map (e.toRingHom.comp (residue R))).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  let W := I.baseChange K
  have : W.IsIntegral R := ⟨⟨I, rfl⟩⟩
  let f := e.toRingHom.comp (residue R)
  have : (I.map f).IsElliptic := ⟨by rw [map_Δ]; exact hunit.map f⟩
  have hval : valuation K (maximalIdeal R) W.Δ = 1 := by
    rw [show W.Δ = _ from map_Δ _ _, valuation_eq_one_iff_notMem]
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit
  let V := E.minimal R
  let J := V.integralModel R
  let Q := (E.exists_isMinimal R).choose
  let D := Q * A⁻¹
  have hDV : D • W = V := by
    change (Q * A⁻¹) • (I.baseChange K) = Q • E
    rw [← hA, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hUndo : D⁻¹ • V = W := by rw [← hDV, ← mul_smul, inv_mul_cancel, one_smul]
  let k := (↑D.u⁻¹ : K)
  have hg : V.HasGoodReduction R := minimal_good_from_equivalent R V D⁻¹ W hUndo hval
  have hID : algebraMap R K I.Δ = W.Δ := (map_Δ _ _).symm
  have hJD : algebraMap R K J.Δ = k ^ 12 * W.Δ :=
    (integralModel_Δ_eq R V).trans (by rw [← hDV]; exact variableChange_Δ W D)
  have hk : _root_.IsIntegral R (k ^ 12) := by
    apply IsIntegrallyClosed.isIntegral_iff.mpr
    refine ⟨J.Δ * ↑hunit.unit⁻¹, ?_⟩
    rw [map_mul, hJD, ← hID, mul_assoc, ← map_mul]
    have hh : I.Δ * ↑hunit.unit⁻¹ = 1 :=
      (congrArg (fun v : R => v * ↑hunit.unit⁻¹) hunit.unit_spec.symm).trans hunit.unit.mul_inv
    rw [hh, map_one, mul_one]
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by decide : 0 < 12) hk
  have hJΔ : J.Δ = d ^ 12 * I.Δ := by
    apply IsFractionRing.injective R K
    rw [hJD, map_mul, map_pow, hd, hID]
  let U := V.reduction R
  have : U.IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  have hdn : f d ≠ 0 := by
    intro hz
    have hdz : residue R d = 0 := e.injective (hz.trans (map_zero e).symm)
    apply (inferInstance : U.IsElliptic).isUnit.ne_zero
    change (J.map (residue R)).Δ = 0
    rw [map_Δ, hJΔ, map_mul, map_pow, hdz]
    norm_num
  have hJ₄ : J.c₄ = d ^ 4 * I.c₄ := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₄_eq, map_mul, map_pow, hd]
    exact (by rw [← hDV]; exact variableChange_c₄ W D : V.c₄ = k ^ 4 * W.c₄).trans (congrArg (k ^ 4 * ·) (map_c₄ I _))
  have hJ₆ : J.c₆ = d ^ 6 * I.c₆ := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₆_eq, map_mul, map_pow, hd]
    exact (by rw [← hDV]; exact variableChange_c₆ W D : V.c₆ = k ^ 6 * W.c₆).trans (congrArg (k ^ 6 * ·) (map_c₆ I _))
  have hcard : Nat.card U.toAffine.Point = Nat.card (I.map f).toAffine.Point := by
    rw [← card_points_map U e]
    apply card_of_scaled_invariants hp _ _ (f d) hdn
    · change ((J.map (residue R)).map e.toRingHom).c₄ = _
      rw [map_c₄, map_c₄, hJ₄, map_c₄]
      simp [f]
    · change ((J.map (residue R)).map e.toRingHom).c₆ = _
      rw [map_c₆, map_c₆, hJ₆, map_c₆]
      simp [f]
  have hq : Nat.card (ResidueField R) = p :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  classical
  change E.localPolynomial R = _
  unfold localPolynomial
  rw [if_pos hg, hq]
  change 1 - C ((p : ℤ) + 1 - Nat.card U.toAffine.Point) * X + C (p : ℤ) * X ^ 2 = _
  rw [hcard]

end Local

open Polynomial NumberField in
/-- A rational change of variables preserves the actual good local Euler factor,
without any integrality assumption on the change. -/
theorem localPolynomial_eq_good_of_change (E : WeierstrassCurve ℚ)
    (W : WeierstrassCurve ℤ) (C : VariableChange ℚ)
    (hC : C • E = W.baseChange ℚ) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hdisc : ¬ (p : ℤ) ∣ W.Δ) :
    let v := rationalPrimePlace p hp
    (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - Polynomial.C ((p : ℤ) + 1 - Nat.card
        (W.map (Int.castRingHom (ZMod p))).toAffine.Point) * X +
        Polynomial.C (p : ℤ) * X ^ 2 := by
  classical
  dsimp only
  let v := rationalPrimePlace p hp
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let I := W.map (Int.castRingHom R)
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)
  let e : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      (PadicInt.residueField.trans (ZMod.ringEquivCongr hv))
  have hunit : IsUnit I.Δ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hz
    have hz' : (W.Δ : ZMod p) = 0 := by
      have h := congrArg e hz
      simpa [I, map_Δ] using h
    exact hdisc ((ZMod.intCast_zmod_eq_zero_iff_dvd W.Δ p).mp hz')
  have hfiber : I.baseChange K = (W.baseChange ℚ).baseChange K := by
    ext <;> simp [I, baseChange, WeierstrassCurve.map_map]
  have hred : I.map (e.toRingHom.comp (residue R)) = W.map (Int.castRingHom (ZMod p)) := by
    ext <;> simp [I, WeierstrassCurve.map_map]
  have hA : C.map (algebraMap ℚ K) • E.baseChange K = I.baseChange K := by
    rw [hfiber, ← hC]
    exact map_variableChange E C (algebraMap ℚ K)
  have h := localPolynomial_of_equivalent_good_model R K hp5 e I hunit
    (E.baseChange K) (C.map (algebraMap ℚ K)) hA
  rw [hred] at h
  exact h

end BSD
