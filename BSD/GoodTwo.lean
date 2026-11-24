import BSD.InertPrimes
import BSD.SmallPrimes

/-!
# The Euler polynomial at the good prime 2

The integral equation `y² + y = x³ - 7` has unit discriminant at 2.
The change of variables to the minimal model selected by Mathlib constrains
its reduced coefficients and gives three points over the residue field.
-/

namespace BSD.FermatCubic

open NumberField WeierstrassCurve IsLocalRing IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

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

private lemma zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma a₃_eq_one_of_a₁_eq_zero (U : WeierstrassCurve (ZMod 2)) [U.IsElliptic]
    (h₁ : U.a₁ = 0) : U.a₃ = 1 := by
  have hΔ := IsElliptic.isUnit (W := U)
  have h : U.a₃ ≠ 0 := by
    intro h₃
    apply hΔ.ne_zero
    simp [WeierstrassCurve.Δ, b₂, b₄, b₆, h₁, h₃, show (4 : ZMod 2) = 0 by decide,
      show (2 : ZMod 2) = 0 by decide]
  exact (zmod_two_cases U.a₃).resolve_left h

private lemma card_points_two (U : WeierstrassCurve (ZMod 2)) [U.IsElliptic]
    (h₁ : U.a₁ = 0) (h₂₄ : U.a₂ = U.a₄) : Nat.card U.toAffine.Point = 3 := by
  have h₃ := a₃_eq_one_of_a₁_eq_zero U h₁
  have h (xy : ZMod 2 × ZMod 2) : U.toAffine.Equation xy.1 xy.2 ↔ xy.1 = U.a₆ := by
    obtain ⟨x, y⟩ := xy
    rw [Affine.equation_iff]
    simp only [toAffine, h₁, h₃, ← h₂₄, zero_mul, add_zero, one_mul]
    generalize U.a₂ = a₂, U.a₆ = a₆
    rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases y with rfl | rfl <;>
      rcases zmod_two_cases a₂ with rfl | rfl <;> rcases zmod_two_cases a₆ with rfl | rfl <;> decide
  let e : {xy : ZMod 2 × ZMod 2 // xy.1 = U.a₆} ≃ ZMod 2 :=
    { toFun := fun xy => xy.1.2
      invFun := fun y => ⟨(U.a₆, y), rfl⟩
      left_inv := fun ⟨⟨_, _⟩, hxy⟩ => Subtype.ext (Prod.ext hxy.symm rfl)
      right_inv := fun _ => rfl }
  have hPred : (fun xy : ZMod 2 × ZMod 2 => U.toAffine.Equation xy.1 xy.2) =
      (fun xy => xy.1 = U.a₆) := funext fun xy => propext (h xy)
  rw [Nat.card_congr (U.toAffine.pointEquiv.trans
    (((Equiv.subtypeEquivProp hPred).trans e).optionCongr)),
    Finite.card_option, Nat.card_zmod]

private lemma valuation_three_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (e : ResidueField R ≃+* ZMod 2) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K 3 = 1 := by
  rw [← map_ofNat (algebraMap R K) 3, valuation_eq_one_iff_notMem]
  change (3 : R) ∉ IsLocalRing.maximalIdeal R
  rw [← residue_eq_zero_iff]
  intro h
  have h' := congrArg e.toRingHom h
  exact (show (3 : ZMod 2) ≠ 0 by decide) (by simpa only [map_ofNat, map_zero] using h')

private lemma coefficients_in_residue_two
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (V : WeierstrassCurve K) [V.IsMinimal R] (C : VariableChange K)
    (hCV : C • (integralModel K) = V) (e : ResidueField R ≃+* ZMod 2)
    (hg : V.HasGoodReduction R) :
    let U := (V.reduction R).map e.toRingHom
    U.a₁ = 0 ∧ U.a₂ = U.a₄ := by
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  let f := e.toRingHom.comp (residue R)
  let u : K := C.u
  let A := V.integralModel R
  let U := (V.reduction R).map e.toRingHom
  change U.a₁ = 0 ∧ U.a₂ = U.a₄
  have hΔ : (integralModel K).Δ = -(19683 : K) := integral_discriminant
  have hunit (a : R) : w (algebraMap R K a) = 1 ↔ f a ≠ 0 := by
    rw [valuation_eq_one_iff_notMem]
    simp [f, residue_eq_zero_iff, IsDiscreteValuationRing.maximalIdeal]
  have h3 : w 3 = 1 := valuation_three_eq_one R e
  have hWval : w (integralModel K).Δ = 1 := by
    rw [hΔ, w.map_neg, show (19683 : K) = 3 ^ 9 by norm_num, map_pow, h3, one_pow]
  have hu : w u = 1 := by
    have h := hg.goodReduction
    change w V.Δ = 1 at h
    rw [← hCV, variableChange_Δ, map_mul, hWval, mul_one, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀] at h
    have h' : (w u)⁻¹ = 1 := (pow_eq_one_iff_of_nonneg (zero_le : 0 ≤ (w u)⁻¹) (by decide)).mp h
    simpa using inv_eq_one.mp h'
  have hval (a : R) (n : ℕ) : w (algebraMap R K a * u ^ n) ≤ 1 := by
    rw [map_mul, map_pow, hu, one_pow, mul_one]
    exact valuation_le_one _ a
  have huInv : u * ↑C.u⁻¹ = 1 := C.u.mul_inv
  have h₂ : V.a₂ * u ^ 2 = 3 * C.r - C.s ^ 2 := by
    rw [← hCV, variableChange_a₂]
    dsimp [integralModel]
    linear_combination (3 * C.r - C.s ^ 2) * (u * ↑C.u⁻¹ + 1) * huInv
  have h₃ : V.a₃ * u ^ 3 = 1 + 2 * C.t := by
    rw [← hCV, variableChange_a₃]
    dsimp [integralModel]
    linear_combination (1 + 2 * C.t) * ((u * ↑C.u⁻¹) ^ 2 + u * ↑C.u⁻¹ + 1) * huInv
  have h₄ : V.a₄ * u ^ 4 = 3 * C.r ^ 2 - C.s * (V.a₃ * u ^ 3) := by
    rw [h₃, ← hCV, variableChange_a₄]
    dsimp [integralModel]
    linear_combination (3 * C.r ^ 2 - C.s * (1 + 2 * C.t)) *
      ((u * ↑C.u⁻¹) ^ 3 + (u * ↑C.u⁻¹) ^ 2 + u * ↑C.u⁻¹ + 1) * huInv
  have ha₂ : w (V.a₂ * u ^ 2) ≤ 1 := by rw [← integralModel_a₂_eq R V]; exact hval _ _
  have ha₃ : w (V.a₃ * u ^ 3) ≤ 1 := by rw [← integralModel_a₃_eq R V]; exact hval _ _
  have ha₄ : w (V.a₄ * u ^ 4) ≤ 1 := by rw [← integralModel_a₄_eq R V]; exact hval _ _
  have hrval : w C.r = w (V.a₂ * u ^ 2 + C.s ^ 2) := by
    conv_lhs => rw [← one_mul (w C.r), ← h3, ← map_mul]
    rw [h₂, sub_add_cancel]
  -- If s were nonintegral, the a₂ equation would give w(r) = w(s)².
  -- Then 3r² would dominate the other term of a₄, contradicting its integrality.
  have hs : w C.s ≤ 1 := by
    by_contra! hs
    have hpow : w C.s < w C.s ^ 2 := by
      simpa only [pow_one] using pow_right_strictMono₀ hs (show (1 : ℕ) < 2 by decide)
    have hr : w C.r = w C.s ^ 2 := by
      rw [hrval, w.map_add_eq_of_lt_right, map_pow]
      rw [map_pow]
      exact ha₂.trans_lt (hs.trans hpow)
    have hprod : w (C.s * (V.a₃ * u ^ 3)) ≤ w C.s := by
      rw [map_mul]
      exact mul_le_of_le_one_right' ha₃
    have hr₂ : w (3 * C.r ^ 2) = w C.s ^ 4 := by rw [map_mul, h3, one_mul, map_pow, hr, ← pow_mul]
    have hpow' : w C.s ^ 2 < w C.s ^ 4 := by
      exact pow_right_strictMono₀ hs (by decide)
    rw [h₄, w.map_sub_eq_of_lt_left, hr₂] at ha₄
    · exact (hs.trans (hpow.trans hpow')).not_ge ha₄
    · exact hprod.trans_lt (hr₂ ▸ hpow.trans hpow')
  have hr : w C.r ≤ 1 := by
    rw [hrval]
    apply w.map_add_le ha₂
    rw [map_pow]
    exact pow_le_one₀ zero_le hs
  obtain ⟨u₀, hu₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
  obtain ⟨s₀, hs₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hs
  obtain ⟨r₀, hr₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hr
  have hfu : f u₀ = 1 := by
    have hne := (hunit u₀).mp (hu₀ ▸ hu)
    exact (zmod_two_cases (f u₀)).resolve_left hne
  have h₁eq : V.a₁ * u = 2 * C.s := by
    rw [← hCV, variableChange_a₁]
    dsimp [integralModel]
    linear_combination (2 * C.s) * huInv
  have hred₁ : U.a₁ = 0 := by
    have heq : A.a₁ * u₀ = 2 * s₀ := by
      apply IsFractionRing.injective R K
      simpa only [map_mul, map_ofNat, hu₀, hs₀, A, integralModel_a₁_eq] using h₁eq
    have hm := congrArg f heq
    change f A.a₁ = 0
    simpa only [map_mul, map_ofNat, hfu, mul_one, show (2 : ZMod 2) = 0 by decide, zero_mul] using hm
  have : (V.reduction R).IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  have : U.IsElliptic := inferInstanceAs ((V.reduction R).map e.toRingHom).IsElliptic
  have hred₃ : f A.a₃ = 1 := a₃_eq_one_of_a₁_eq_zero U hred₁
  have heq₂ : A.a₂ * u₀ ^ 2 = 3 * r₀ - s₀ ^ 2 := by
    apply IsFractionRing.injective R K
    simpa only [map_mul, map_sub, map_ofNat, map_pow, hu₀, hs₀, hr₀, A, integralModel_a₂_eq] using h₂
  have heq₄ : A.a₄ * u₀ ^ 4 = 3 * r₀ ^ 2 - s₀ * (A.a₃ * u₀ ^ 3) := by
    apply IsFractionRing.injective R K
    simpa only [map_mul, map_sub, map_ofNat, map_pow, hu₀, hs₀, hr₀, A, integralModel_a₃_eq,
      integralModel_a₄_eq] using h₄
  have hsq (a : ZMod 2) : a ^ 2 = a := by rcases zmod_two_cases a with rfl | rfl <;> decide
  have hsimp : (3 : ZMod 2) = 1 := by decide
  have hred₂ := congrArg f heq₂
  have hred₄ := congrArg f heq₄
  -- Both reduced coefficients equal the reduction of r - s.
  simp only [map_mul, map_sub, map_ofNat, map_pow, hfu, one_pow, mul_one, hsimp, hsq, one_mul,
    hred₃] at hred₂ hred₄
  exact ⟨hred₁, hred₂.trans hred₄.symm⟩

open Polynomial in
/-- The Fermat model has three points in its good reduction at the place over 2. -/
theorem fermatCubic_localPolynomial_two_rat
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 2) :
    ((mordellModel (-(432 : ℚ))).baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ) = 1 + Polynomial.C (2 : ℤ) * X ^ 2 := by
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let eₚ : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  let e : ResidueField R ≃+* ZMod 2 := eₚ.trans (ZMod.ringEquivCongr hv)
  let S := mordellModel (-(432 : K))
  have hS : (mordellModel (-(432 : ℚ))).baseChange K = S := by
    ext <;> simp [baseChange, mordellModel, S]
  change ((mordellModel (-(432 : ℚ))).baseChange K).localPolynomial R = _
  rw [hS]
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let V := S.minimal R
  let Q := (S.exists_isMinimal R).choose
  let W := integralModel K
  let D : VariableChange K := ⟨Units.mk0 2 (by norm_num), 0, 0, 4⟩
  have hDW : D • S = W := by
    ext <;> norm_num [D, S, W, mordellModel, integralModel, variableChange_a₁,
      variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
      Units.val_inv_eq_inv_val]
  let C := Q * D⁻¹
  have hCV : C • W = V := by
    change (Q * D⁻¹) • W = Q • S
    rw [← hDW, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hCW : C⁻¹ • V = W := by rw [← hCV, ← mul_smul, inv_mul_cancel, one_smul]
  have : W.IsIntegral R := ⟨⟨integralModel R, by
    ext <;> simp only [W, integralModel, baseChange, map_a₁, map_a₂, map_a₃, map_a₄,
      map_a₆, map_zero, map_one, map_neg, map_ofNat]⟩⟩
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have hWval : w W.Δ = 1 := by
    have h3 : w 3 = 1 := valuation_three_eq_one R e
    rw [show W.Δ = -(19683 : K) from integral_discriminant,
      w.map_neg, show (19683 : K) = 3 ^ 9 by norm_num, map_pow, h3, one_pow]
  have hg : V.HasGoodReduction R := minimal_good_from_equivalent R V C⁻¹ W hCW hWval
  let U := V.reduction R
  have : U.IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  obtain ⟨h₁, h₂₄⟩ := coefficients_in_residue_two R V C hCV e hg
  have hcard : Nat.card U.toAffine.Point = 3 :=
    (card_points_map U e).symm.trans (card_points_two _ h₁ h₂₄)
  have hq : Nat.card (ResidueField R) = 2 :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 2)
  classical
  unfold localPolynomial
  rw [if_pos hg, hq]
  change 1 - Polynomial.C ((2 : ℤ) + 1 - Nat.card U.toAffine.Point) * X +
    Polynomial.C (2 : ℤ) * X ^ 2 = _
  rw [hcard]
  norm_num

end BSD.FermatCubic
