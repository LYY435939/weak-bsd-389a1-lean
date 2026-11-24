import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Point counts at inert primes

For a prime `p ≡ 2 mod 3`, the cube map permutes `ZMod p`. The projection to
the second coordinate therefore identifies the affine solutions of `y² = x³ + b`
with the field itself. For an elliptic model, adjoining the point at infinity
gives `p + 1` rational points.
-/

namespace BSD.FermatCubic

/-- The Weierstrass equation `y² = x³ + b`. -/
def mordellModel {R : Type*} [CommRing R] (b : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, 0, b⟩

lemma mordell_equation_iff {R : Type*} [CommRing R] (b x y : R) :
    (mordellModel b).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + b := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [mordellModel]

lemma mordell_discriminant {R : Type*} [CommRing R] (b : R) :
    (mordellModel b).Δ = -(2 : R) ^ 4 * 3 ^ 3 * b ^ 2 := by
  simp only [mordellModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma mordell_c₄ {R : Type*} [CommRing R] (b : R) :
    (mordellModel b).c₄ = 0 := by
  simp [mordellModel, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

lemma mordell_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (b : R) :
    (mordellModel b).map f = mordellModel (f b) := by
  ext <;> simp [mordellModel]

/-- Cubing permutes the prime field when `p ≡ 2 (mod 3)`. -/
theorem cube_bijective {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) := by
  have hcoprime : (Nat.card (ZMod p)ˣ).Coprime 3 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units, Nat.coprime_comm,
      Nat.prime_three.coprime_iff_not_dvd]
    omega
  have hinj : Function.Injective (fun x : ZMod p => x ^ 3) := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      exact (eq_zero_of_pow_eq_zero (n := 3) (by simpa using hxy.symm)).symm
    have hy : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    have hUnit : (Units.mk0 x hx : (ZMod p)ˣ) ^ 3 = (Units.mk0 y hy) ^ 3 := by
      apply Units.ext
      simpa using hxy
    simpa using congrArg Units.val (hcoprime.pow_left_bijective.injective hUnit)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- Each second coordinate determines exactly one first coordinate. -/
noncomputable def mordellAffineEquiv {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2)
    (b : ZMod p) : {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + b} ≃ ZMod p := by
  let cube := Equiv.ofBijective _ (cube_bijective hp)
  refine
    { toFun := fun xy => xy.1.2
      invFun := fun y => ⟨(cube.symm (y ^ 2 - b), y), ?_⟩
      left_inv := ?_
      right_inv := fun _ => rfl }
  · change y ^ 2 = cube (cube.symm (y ^ 2 - b)) + b
    rw [cube.apply_symm_apply, sub_add_cancel]
  · rintro ⟨⟨x, y⟩, hxy⟩
    apply Subtype.ext
    change (cube.symm (y ^ 2 - b), y) = (x, y)
    rw [show y ^ 2 - b = cube x from sub_eq_iff_eq_add.mpr hxy, cube.symm_apply_apply]

theorem mordell_card_affine {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2) (b : ZMod p) :
    Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + b} = p :=
  (Nat.card_congr (mordellAffineEquiv hp b)).trans (Nat.card_zmod p)

/-- The Mathlib point type includes the point at infinity. -/
theorem mordell_card_points {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2) (b : ZMod p)
    [(mordellModel b).IsElliptic] : Nat.card (mordellModel b).toAffine.Point = p + 1 := by
  have hPred :
      (fun xy : ZMod p × ZMod p => (mordellModel b).toAffine.Equation xy.1 xy.2) =
        (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + b) := by
    funext xy
    exact propext (mordell_equation_iff b xy.1 xy.2)
  let e := (mordellModel b).toAffine.pointEquiv.trans
    (Equiv.subtypeEquivProp hPred).optionCongr
  rw [Nat.card_congr e]
  change Nat.card (Option {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + b}) = _
  rw [Finite.card_option, mordell_card_affine hp b]

lemma zmod_two_three_ne_zero {p : ℕ} (hp : 5 ≤ p) :
    (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 := by
  constructor
  · exact fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  · exact fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      ((ZMod.natCast_eq_zero_iff 3 p).mp h)

/-- The reduction of the short Fermat model is elliptic at every prime `p ≥ 5`. -/
theorem fermatCubic_isElliptic {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    (mordellModel (-(432 : ZMod p))).IsElliptic := by
  obtain ⟨h2, h3⟩ := zmod_two_three_ne_zero hp
  have h432 : (432 : ZMod p) ≠ 0 := by
    rw [show (432 : ZMod p) = 2 ^ 4 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [mordell_discriminant]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) (pow_ne_zero _ h3))
    (pow_ne_zero _ (neg_ne_zero.mpr h432))

theorem fermatCubic_card_points {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hinert : p % 3 = 2) :
    Nat.card (mordellModel (-(432 : ZMod p))).toAffine.Point = p + 1 := by
  exact @mordell_card_points p _ hinert (-(432 : ZMod p)) (fermatCubic_isElliptic hp)

/-- The Frobenius trace of the Fermat model at a good inert prime is zero. -/
theorem fermatCubic_trace_eq_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hinert : p % 3 = 2) :
    (p : ℤ) + 1 - Nat.card (mordellModel (-(432 : ZMod p))).toAffine.Point = 0 := by
  rw [fermatCubic_card_points hp hinert, Nat.cast_add, Nat.cast_one, sub_self]

open WeierstrassCurve

lemma card_points_map {F F' : Type*} [Field F] [Field F']
    (W : WeierstrassCurve F) [W.IsElliptic] (e : F ≃+* F') :
    Nat.card (W.map e.toRingHom).toAffine.Point = Nat.card W.toAffine.Point := by
  let eXY := e.toEquiv.prodCongr e.toEquiv
  have he (xy : F × F) : W.toAffine.Equation xy.1 xy.2 ↔
      (W.map e.toRingHom).toAffine.Equation (eXY xy).1 (eXY xy).2 :=
    (W.toAffine.map_equation (f := e.toRingHom) e.injective xy.1 xy.2).symm
  exact Nat.card_congr
    ((W.toAffine.pointEquiv.trans (eXY.subtypeEquiv he).optionCongr).trans
      (W.map e.toRingHom).toAffine.pointEquiv.symm).symm

lemma card_points_smul_of_u_eq_one {F : Type*} [Field F]
    (W : WeierstrassCurve F) [W.IsElliptic] (C : VariableChange F) (hC : C.u = 1) :
    Nat.card W.toAffine.Point = Nat.card (C • W).toAffine.Point := by
  let eXY : F × F ≃ F × F :=
    { toFun := fun (x, y) => (x + C.r, y + C.s * x + C.t)
      invFun := fun (x, y) => (x - C.r, y - C.s * (x - C.r) - C.t)
      left_inv := by intro xy; exact Prod.ext (by dsimp; ring) (by dsimp; ring)
      right_inv := by intro xy; exact Prod.ext (by dsimp; ring) (by dsimp; ring) }
  have he (xy : F × F) : (C • W).toAffine.Equation xy.1 xy.2 ↔
      W.toAffine.Equation (eXY xy).1 (eXY xy).2 := by
    rw [Affine.equation_iff', Affine.equation_iff']
    change xy.2 ^ 2 + (C • W).a₁ * xy.1 * xy.2 + (C • W).a₃ * xy.2 -
      (xy.1 ^ 3 + (C • W).a₂ * xy.1 ^ 2 + (C • W).a₄ * xy.1 + (C • W).a₆) = 0 ↔
      _
    simp only [eXY, Equiv.coe_fn_mk, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, hC, inv_one, Units.val_one, one_pow, one_mul]
    ring_nf
  exact Nat.card_congr
    (((C • W).toAffine.pointEquiv.trans (eXY.subtypeEquiv he).optionCongr).trans
      W.toAffine.pointEquiv.symm).symm

/-- Every elliptic curve with `c₄ = 0` over an inert prime field has `p + 1` points. -/
theorem card_points_of_c₄_eq_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hinert : p % 3 = 2)
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (hc : W.c₄ = 0) :
    Nat.card W.toAffine.Point = p + 1 := by
  obtain ⟨h2, h3⟩ := zmod_two_three_ne_zero hp
  let := invertibleOfNonzero h2
  let := invertibleOfNonzero h3
  let C := W.toShortNF
  let W' := C • W
  have hc₄ : W'.c₄ = 0 := by
    change (C • W).c₄ = 0
    rw [variableChange_c₄, hc, mul_zero]
  have h48 : (-48 : ZMod p) ≠ 0 := by
    rw [show (-48 : ZMod p) = -(2 : ZMod p) ^ 4 * 3 by norm_num]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) h3
  have ha₄ : W'.a₄ = 0 := by
    rw [c₄_of_isShortNF] at hc₄
    exact (mul_eq_zero.mp hc₄).resolve_left h48
  have heq : W' = mordellModel W'.a₆ := by
    ext
    · exact W'.a₁_of_isShortNF
    · exact W'.a₂_of_isShortNF
    · exact W'.a₃_of_isShortNF
    · exact ha₄
    · rfl
  have hCu : C.u = 1 := by
    change W.toShortNF.u = 1
    simp [toShortNF, VariableChange.mul_def]
  have hEll : (mordellModel W'.a₆).IsElliptic := heq ▸ (inferInstance : W'.IsElliptic)
  calc
    Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point := card_points_smul_of_u_eq_one W C hCu
    _ = Nat.card (mordellModel W'.a₆).toAffine.Point :=
      congrArg (fun W₀ : WeierstrassCurve (ZMod p) => Nat.card W₀.toAffine.Point) heq
    _ = p + 1 := @mordell_card_points p _ hinert W'.a₆ hEll

open IsLocalRing IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

lemma minimal_good_of_valuation_eq_one (W : WeierstrassCurve K) [W.IsIntegral R]
    (h : valuation K (maximalIdeal R) W.Δ = 1) : (W.minimal R).HasGoodReduction R := by
  let C := (W.exists_isMinimal R).choose
  let V := W.minimal R
  have hUndo : C⁻¹ • V = W := by
    change C⁻¹ • (C • W) = W
    rw [← mul_smul, inv_mul_cancel, one_smul]
  have hW : (valuation_Δ_aux R W).val = 1 :=
    (valuation_Δ_aux_eq_of_isIntegral R W).trans h
  have hle : valuation_Δ_aux R V ≤ valuation_Δ_aux R W := by
    change (valuation_Δ_aux R V).val ≤ (valuation_Δ_aux R W).val
    rw [hW]
    exact (valuation_Δ_aux R V).prop
  have hMax := (inferInstance : V.IsMinimal R).val_Δ_maximal
  have hle' : valuation_Δ_aux R W ≤ valuation_Δ_aux R V := by
    have hInt : (C⁻¹ • V).IsIntegral R := hUndo ▸ (inferInstance : W.IsIntegral R)
    have hLeChange : valuation_Δ_aux R ((1 : VariableChange K) • V) ≤
        valuation_Δ_aux R (C⁻¹ • V) := by simpa only [one_smul, hUndo]
    simpa only [one_smul, hUndo] using hMax.2 hInt hLeChange
  refine HasGoodReduction.mk ?_
  rw [← valuation_Δ_aux_eq_of_isIntegral R V, le_antisymm hle hle', hW]

open Polynomial in
/-- The Euler polynomial of the short Fermat model at an inert prime, computed using the
minimal model selected by Mathlib over the given discrete valuation ring. -/
theorem fermatCubic_localPolynomial_of_residueEquiv {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hinert : p % 3 = 2) (e : ResidueField R ≃+* ZMod p) :
    (mordellModel (-(432 : K))).localPolynomial R = 1 + C (p : ℤ) * X ^ 2 := by
  let W := mordellModel (-(432 : K))
  let I := mordellModel (-(432 : R))
  have hI : I.baseChange K = W := by
    simp [I, W, WeierstrassCurve.baseChange, mordell_map, map_ofNat]
  have : W.IsIntegral R := ⟨⟨I, hI.symm⟩⟩
  have hIred : (I.map (residue R)).map e.toRingHom = mordellModel (-(432 : ZMod p)) := by
    simp [I, mordell_map, map_ofNat]
  have hΔ : (I.map (residue R)).Δ ≠ 0 := by
    intro h
    have h' : (mordellModel (-(432 : ZMod p))).Δ = 0 := by
      rw [← hIred, map_Δ, h, map_zero]
    exact (fermatCubic_isElliptic hp).isUnit.ne_zero h'
  have hval : valuation K (maximalIdeal R) W.Δ = 1 := by
    rw [← hI, WeierstrassCurve.baseChange, map_Δ, valuation_eq_one_iff_notMem]
    rwa [map_Δ, ne_eq, residue_eq_zero_iff] at hΔ
  let V := W.minimal R
  have hg : V.HasGoodReduction R := minimal_good_of_valuation_eq_one R W hval
  have hc : V.c₄ = 0 := by
    change ((W.exists_isMinimal R).choose • W).c₄ = 0
    rw [variableChange_c₄, mordell_c₄, mul_zero]
  let U := V.reduction R
  have : U.IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  have hcI : (V.integralModel R).c₄ = 0 := by
    apply IsFractionRing.injective R K
    rw [integralModel_c₄_eq, hc, map_zero]
  have hcU : U.c₄ = 0 := by
    change ((V.integralModel R).map (residue R)).c₄ = 0
    rw [map_c₄, hcI, map_zero]
  have hcardU : Nat.card U.toAffine.Point = p + 1 := by
    rw [← card_points_map U e]
    exact card_points_of_c₄_eq_zero hp hinert (U.map e.toRingHom) (by rw [map_c₄, hcU, map_zero])
  have hq : Nat.card (ResidueField R) = p :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  classical
  change W.localPolynomial R = _
  unfold localPolynomial
  rw [if_pos hg, hq]
  change 1 - C ((p : ℤ) + 1 - Nat.card U.toAffine.Point) * X + C (p : ℤ) * X ^ 2 = _
  rw [hcardU, Nat.cast_add, Nat.cast_one, sub_self, map_zero, zero_mul, sub_zero]

end Local

open Polynomial NumberField in
/-- The Euler polynomial at every good inert finite place in the Mathlib definition of the
Fermat model's L-function over `ℚ`. -/
theorem fermatCubic_localPolynomial_rat (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hp : 5 ≤ (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
    (hinert : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) % 3 = 2) :
    ((mordellModel (-(432 : ℚ))).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      1 + C ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) * X ^ 2 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  rw [WeierstrassCurve.baseChange, mordell_map, map_neg, map_ofNat]
  exact fermatCubic_localPolynomial_of_residueEquiv (v.adicCompletionIntegers ℚ) hp hinert e

end BSD.FermatCubic
