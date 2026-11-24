import BSD.InertPrimes
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Euler polynomials from the explicit good reductions of the Fermat cubic -/

namespace BSD.FermatCubic

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

private lemma mordell_c₆ {R : Type*} [CommRing R] (b : R) :
    (mordellModel b).c₆ = -864 * b := by
  simp only [mordellModel, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

/-- Scaling the coordinates by the weights two and three leaves the point count unchanged. -/
private lemma mordell_card_scale {F : Type*} [Field F] (b d : F) (hd : d ≠ 0)
    [(mordellModel b).IsElliptic] [(mordellModel (d ^ 6 * b)).IsElliptic] :
    Nat.card (mordellModel (d ^ 6 * b)).toAffine.Point =
      Nat.card (mordellModel b).toAffine.Point := by
  let eXY : F × F ≃ F × F :=
    { toFun := fun (x, y) => (d ^ 2 * x, d ^ 3 * y)
      invFun := fun (x, y) => (x / d ^ 2, y / d ^ 3)
      left_inv := by intro ⟨x,y⟩; apply Prod.ext <;> dsimp <;> field_simp
      right_inv := by intro ⟨x,y⟩; apply Prod.ext <;> dsimp <;> field_simp }
  have he (xy : F × F) : (mordellModel b).toAffine.Equation xy.1 xy.2 ↔
      (mordellModel (d ^ 6 * b)).toAffine.Equation (eXY xy).1 (eXY xy).2 := by
    rw [mordell_equation_iff, mordell_equation_iff]
    change xy.2 ^ 2 = xy.1 ^ 3 + b ↔ (d ^ 3 * xy.2) ^ 2 = (d ^ 2 * xy.1) ^ 3 + d ^ 6 * b
    convert (mul_right_inj' (pow_ne_zero 6 hd) :
      d ^ 6 * xy.2 ^ 2 = d ^ 6 * (xy.1 ^ 3 + b) ↔ _) |>.symm using 2 <;> ring
  exact Nat.card_congr
    (((mordellModel b).toAffine.pointEquiv.trans (eXY.subtypeEquiv he).optionCongr).trans
      (mordellModel (d ^ 6 * b)).toAffine.pointEquiv.symm).symm

private lemma short_card_of_invariants {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (d : ZMod p) (hd : d ≠ 0)
    (hc₄ : W.c₄ = 0) (hc₆ : W.c₆ = d ^ 6 * (mordellModel (-(432 : ZMod p))).c₆) :
    Nat.card W.toAffine.Point = Nat.card (mordellModel (-(432 : ZMod p))).toAffine.Point := by
  obtain ⟨h2, h3⟩ := zmod_two_three_ne_zero hp
  let := invertibleOfNonzero h2
  let := invertibleOfNonzero h3
  let S := W.toShortNF • W
  have hu : W.toShortNF.u = 1 := by simp [toShortNF, VariableChange.mul_def]
  have h48 : (-48 : ZMod p) ≠ 0 := by
    rw [show (-48 : ZMod p) = -(2 : ZMod p) ^ 4 * 3 by norm_num]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) h3
  have h864 : (-864 : ZMod p) ≠ 0 := by
    rw [show (-864 : ZMod p) = -(2 : ZMod p) ^ 5 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) (pow_ne_zero _ h3)
  have hs₄ : S.c₄ = 0 := by
    rw [show S.c₄ = _ from variableChange_c₄ W _, hc₄, mul_zero]
  have hs₆ : S.c₆ = d ^ 6 * (mordellModel (-(432 : ZMod p))).c₆ := by
    change (W.toShortNF • W).c₆ = _
    simpa only [variableChange_c₆, hu, inv_one, Units.val_one, one_pow, one_mul] using hc₆
  have heq : S = mordellModel (d ^ 6 * -(432 : ZMod p)) := by
    ext
    · exact S.a₁_of_isShortNF
    · exact S.a₂_of_isShortNF
    · exact S.a₃_of_isShortNF
    · rw [c₄_of_isShortNF] at hs₄
      exact (mul_eq_zero.mp hs₄).resolve_left h48
    · rw [c₆_of_isShortNF, mordell_c₆] at hs₆
      change S.a₆ = d ^ 6 * -432
      apply (mul_right_inj' h864).mp
      linear_combination hs₆
  let := fermatCubic_isElliptic hp
  have : (mordellModel (d ^ 6 * -(432 : ZMod p))).IsElliptic := heq ▸ (inferInstance : S.IsElliptic)
  calc
    Nat.card W.toAffine.Point = Nat.card S.toAffine.Point := card_points_smul_of_u_eq_one W _ hu
    _ = Nat.card (mordellModel (d ^ 6 * -(432 : ZMod p))).toAffine.Point :=
      congrArg (fun V : WeierstrassCurve (ZMod p) => Nat.card V.toAffine.Point) heq
    _ = _ := mordell_card_scale _ _ hd

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open Polynomial in
/-- The good Euler polynomial over a DVR with prime residue field. The discriminant
ratio shows that the twelfth power of the scaling parameter is integral. Integral
closedness gives an integral parameter, and good reduction gives a nonzero residue. -/
theorem fermatCubic_good_localPolynomial_of_residueEquiv {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (e : ResidueField R ≃+* ZMod p) :
    (mordellModel (-(432 : K))).localPolynomial R =
      1 - C ((p : ℤ) + 1 - Nat.card (mordellModel (-(432 : ZMod p))).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  let W := mordellModel (-(432 : K))
  let I := mordellModel (-(432 : R))
  have hI : I.baseChange K = W := by
    simp [I, W, WeierstrassCurve.baseChange, mordell_map, map_ofNat]
  have : W.IsIntegral R := ⟨⟨I, hI.symm⟩⟩
  let f := e.toRingHom.comp (residue R)
  have hIred : I.map f = mordellModel (-(432 : ZMod p)) := by
    simp [I, mordell_map, map_ofNat]
  have hΔ : residue R I.Δ ≠ 0 := by
    intro h
    have h' : (mordellModel (-(432 : ZMod p))).Δ = 0 := by
      rw [← hIred, map_Δ]
      exact (congrArg e h).trans (map_zero e)
    exact (fermatCubic_isElliptic hp).isUnit.ne_zero h'
  have hunit := (residue_ne_zero_iff_isUnit _).mp hΔ
  have hval : valuation K (maximalIdeal R) W.Δ = 1 := by
    rw [← hI, WeierstrassCurve.baseChange, map_Δ, valuation_eq_one_iff_notMem]
    rwa [ne_eq, residue_eq_zero_iff] at hΔ
  let V := W.minimal R
  let J := V.integralModel R
  let D := (W.exists_isMinimal R).choose
  let k := (↑D.u⁻¹ : K)
  have hg : V.HasGoodReduction R := minimal_good_of_valuation_eq_one R W hval
  have hID : algebraMap R K I.Δ = W.Δ := by rw [← hI, baseChange, map_Δ]
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
  have hJ₄ : J.c₄ = 0 := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₄_eq, map_zero]
    exact (variableChange_c₄ W D).trans (by rw [mordell_c₄, mul_zero])
  have hJ₆ : J.c₆ = d ^ 6 * I.c₆ := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₆_eq, map_mul, map_pow, hd]
    exact (variableChange_c₆ W D).trans (by rw [← hI, baseChange, map_c₆])
  have hcard : Nat.card U.toAffine.Point =
      Nat.card (mordellModel (-(432 : ZMod p))).toAffine.Point := by
    rw [← card_points_map U e]
    apply short_card_of_invariants hp _ (f d) hdn
    · change ((J.map (residue R)).map e.toRingHom).c₄ = 0
      rw [map_c₄, map_c₄, hJ₄, map_zero, map_zero]
    · change ((J.map (residue R)).map e.toRingHom).c₆ = _
      rw [map_c₆, map_c₆, hJ₆, ← hIred, map_c₆]
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

open Polynomial NumberField in
/-- At primes at least five, Mathlib's chosen minimal model has the Euler polynomial
obtained by counting points on the given short equation over the prime field. -/
theorem fermatCubic_good_localPolynomial_rat (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hp : 5 ≤ (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :
    let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
    ((mordellModel (-(432 : ℚ))).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      1 - C ((p : ℤ) + 1 - Nat.card (mordellModel (-(432 : ZMod p))).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  dsimp only
  rw [WeierstrassCurve.baseChange, mordell_map, map_neg, map_ofNat]
  exact fermatCubic_good_localPolynomial_of_residueEquiv (v.adicCompletionIntegers ℚ) hp e

end BSD.FermatCubic
