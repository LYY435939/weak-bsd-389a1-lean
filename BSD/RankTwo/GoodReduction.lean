import BSD.RankTwo.Curve
import BSD.InertPrimes
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Good Euler polynomials for integral models away from residue characteristics two and three -/

namespace BSD.RankTwo

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open BSD.FermatCubic (card_points_map card_points_smul_of_u_eq_one
  minimal_good_of_valuation_eq_one zmod_two_three_ne_zero)

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

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

open Polynomial in
/-- A unit-discriminant integral equation computes the actual local Euler polynomial in
prime residue characteristic at least five, independently of the chosen minimal model. -/
theorem localPolynomial_of_good_model {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (e : ResidueField R ≃+* ZMod p) (I : WeierstrassCurve R) (hunit : IsUnit I.Δ) :
    (I.baseChange K).localPolynomial R =
      1 - C ((p : ℤ) + 1 - Nat.card (I.map (e.toRingHom.comp (residue R))).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  let W := I.baseChange K
  have : W.IsIntegral R := ⟨⟨I, rfl⟩⟩
  let f := e.toRingHom.comp (residue R)
  have : (I.map f).IsElliptic := ⟨by rw [map_Δ]; exact hunit.map f⟩
  have hval : valuation K (maximalIdeal R) W.Δ = 1 := by
    rw [show W.Δ = _ from map_Δ _ _, valuation_eq_one_iff_notMem]
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit
  let V := W.minimal R
  let J := V.integralModel R
  let D := (W.exists_isMinimal R).choose
  let k := (↑D.u⁻¹ : K)
  have hg : V.HasGoodReduction R := minimal_good_of_valuation_eq_one R W hval
  have hID : algebraMap R K I.Δ = W.Δ := (map_Δ _ _).symm
  have hJD : algebraMap R K J.Δ = k ^ 12 * W.Δ :=
    (integralModel_Δ_eq R V).trans (variableChange_Δ W D)
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
    exact (variableChange_c₄ W D).trans (congrArg (k ^ 4 * ·) (map_c₄ I _))
  have hJ₆ : J.c₆ = d ^ 6 * I.c₆ := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₆_eq, map_mul, map_pow, hd]
    exact (variableChange_c₆ W D).trans (congrArg (k ^ 6 * ·) (map_c₆ I _))
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
  change W.localPolynomial R = _
  unfold localPolynomial
  rw [if_pos hg, hq]
  change 1 - C ((p : ℤ) + 1 - Nat.card U.toAffine.Point) * X + C (p : ℤ) * X ^ 2 = _
  rw [hcard]

end Local

private lemma model_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (model R).map f = model S := by
  ext <;> simp [model, map_ofNat]

open Polynomial NumberField in
/-- The good Euler polynomials of 389.a1 at the finite places above primes at least five. -/
theorem good_localPolynomial_rat (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hp : 5 ≤ (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
    (h389 : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ≠ 389) :
    let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - C ((p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let e : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  have h389p : (389 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff 389 p).mp h
    have heq := (Nat.prime_dvd_prime_iff_eq p.2 (by norm_num : Nat.Prime 389)).mp hdiv
    exact h389 heq
  have hunit : IsUnit (model R).Δ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hz
    apply h389p
    rw [discriminant] at hz
    simpa only [map_ofNat, map_zero] using congrArg e hz
  dsimp only
  rw [show curve.baseChange K = (model R).baseChange K by rw [baseChange, baseChange, model_map, model_map]]
  simpa only [model_map] using localPolynomial_of_good_model R K hp e (model R) hunit

end BSD.RankTwo
