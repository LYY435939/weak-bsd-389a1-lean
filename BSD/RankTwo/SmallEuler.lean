import BSD.InertPrimes
import BSD.RankTwo.Curve

/-! # The Euler polynomials of 389.a1 at 2 and 3 -/

namespace BSD.RankTwo

open WeierstrassCurve IsLocalRing IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

private lemma map_model {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (model R).map f = model S := by
  ext <;> simp [model, map_ofNat]

private lemma card_scaling {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] (u : Fˣ) :
    Nat.card W.toAffine.Point = Nat.card ((⟨u, 0, 0, 0⟩ : VariableChange F) • W).toAffine.Point := by
  let D : VariableChange F := ⟨u, 0, 0, 0⟩
  let d : F := u
  have hd : d ≠ 0 := Units.ne_zero u
  let eXY : F × F ≃ F × F :=
    { toFun := fun (x, y) => (d ^ 2 * x, d ^ 3 * y)
      invFun := fun (x, y) => (x / d ^ 2, y / d ^ 3)
      left_inv := by intro ⟨x,y⟩; apply Prod.ext <;> dsimp only <;> field_simp
      right_inv := by intro ⟨x,y⟩; apply Prod.ext <;> dsimp only <;> field_simp }
  have he (xy : F × F) : (D • W).toAffine.Equation xy.1 xy.2 ↔
      W.toAffine.Equation (eXY xy).1 (eXY xy).2 := by
    rw [Affine.equation_iff', Affine.equation_iff']
    change xy.2 ^ 2 + (D • W).a₁ * xy.1 * xy.2 + (D • W).a₃ * xy.2 -
      (xy.1 ^ 3 + (D • W).a₂ * xy.1 ^ 2 + (D • W).a₄ * xy.1 + (D • W).a₆) = 0 ↔
      (d ^ 3 * xy.2) ^ 2 + W.a₁ * (d ^ 2 * xy.1) * (d ^ 3 * xy.2) +
        W.a₃ * (d ^ 3 * xy.2) -
        ((d ^ 2 * xy.1) ^ 3 + W.a₂ * (d ^ 2 * xy.1) ^ 2 + W.a₄ * (d ^ 2 * xy.1) + W.a₆) = 0
    simp only [D, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, mul_zero, zero_mul, add_zero, sub_zero, Units.val_inv_eq_inv_val]
    have hmul (x : F) : d ^ 6 * x = 0 ↔ x = 0 :=
      ⟨fun h => (mul_eq_zero.mp h).resolve_left (pow_ne_zero 6 hd), fun h => by rw [h, mul_zero]⟩
    rw [← hmul]
    apply Iff.of_eq
    congr 1
    dsimp only [d] at hd ⊢
    field_simp [hd]
    ring
  exact (Nat.card_congr (((D • W).toAffine.pointEquiv.trans (eXY.subtypeEquiv he).optionCongr).trans
    W.toAffine.pointEquiv.symm)).symm

private lemma card_change {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] (D : VariableChange F) :
    Nat.card W.toAffine.Point = Nat.card (D • W).toAffine.Point := by
  let A : VariableChange F := ⟨D.u, 0, 0, 0⟩
  let B : VariableChange F := ⟨1, D.r, D.s, D.t⟩
  have h : D = A * B := by
    ext <;> simp [A, B, VariableChange.mul_def]
  calc
    Nat.card W.toAffine.Point = Nat.card (B • W).toAffine.Point :=
      BSD.FermatCubic.card_points_smul_of_u_eq_one W B rfl
    _ = Nat.card (A • (B • W)).toAffine.Point := card_scaling (B • W) D.u
    _ = Nat.card (D • W).toAffine.Point := by rw [← mul_smul, ← h]

lemma card_model_of_affine_card {p : ℕ} [Fact p.Prime]
    [(model (ZMod p)).IsElliptic] (n : ℕ)
    (h : Fintype.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 + xy.2 = xy.1 ^ 3 + xy.1 ^ 2 - 2 * xy.1} = n) :
    Nat.card (model (ZMod p)).toAffine.Point = n + 1 := by
  have hPred :
      (fun xy : ZMod p × ZMod p => (model (ZMod p)).toAffine.Equation xy.1 xy.2) =
      (fun xy => xy.2 ^ 2 + xy.2 = xy.1 ^ 3 + xy.1 ^ 2 - 2 * xy.1) :=
    funext fun xy => propext (equation_iff xy.1 xy.2)
  let e := (model (ZMod p)).toAffine.pointEquiv.trans
    (Equiv.subtypeEquivProp hPred).optionCongr
  rw [Nat.card_congr e, Finite.card_option, Nat.card_eq_fintype_card, h]

private lemma card_model_two [(model (ZMod 2)).IsElliptic] :
    Nat.card (model (ZMod 2)).toAffine.Point = 5 :=
  card_model_of_affine_card 4 (by decide)

private lemma card_model_three [(model (ZMod 3)).IsElliptic] :
    Nat.card (model (ZMod 3)).toAffine.Point = 6 :=
  card_model_of_affine_card 5 (by decide)

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private lemma integral_change (D : VariableChange K)
    (hV : (D • model K).IsIntegral R)
    (hu : (IsDiscreteValuationRing.maximalIdeal R).valuation K (D.u : K) = 1) :
    ∃ L : VariableChange R, L.map (algebraMap R K) = D := by
  let V := D • model K
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  let u : K := D.u
  let r := D.r
  let s := D.s
  let t := D.t
  have hu : w u = 1 := hu
  have hclear (n : ℕ) (z : K) :
      (↑D.u⁻¹ : K) ^ n * z * u ^ n = z := by
    rw [mul_comm _ z, mul_assoc, ← mul_pow, show (↑D.u⁻¹ : K) * u = 1 from D.u.inv_mul,
      one_pow, mul_one]
  have ha₁ : V.a₁ * u = 2 * s := by
    change (D • model K).a₁ * u = _
    rw [variableChange_a₁, ← pow_one (↑D.u⁻¹ : K), ← pow_one u, hclear]
    simp [model, s]
  have ha₂ : V.a₂ * u ^ 2 = 1 + 3 * r - s ^ 2 := by
    change (D • model K).a₂ * u ^ 2 = _
    rw [variableChange_a₂, hclear]
    simp [model, r, s]
  have ha₃ : V.a₃ * u ^ 3 = 1 + 2 * t := by
    change (D • model K).a₃ * u ^ 3 = _
    rw [variableChange_a₃, hclear]
    simp [model, t]
  have ha₄ : V.a₄ * u ^ 4 = 3 * r ^ 2 + (2 * r - 2 - s * (V.a₃ * u ^ 3)) := by
    rw [ha₃]
    change (D • model K).a₄ * u ^ 4 = _
    rw [variableChange_a₄, hclear]
    simp only [model, r, s, t]
    ring
  have ha₆ : V.a₆ * u ^ 6 = r ^ 3 + r ^ 2 - 2 * r - t - t ^ 2 := by
    change (D • model K).a₆ * u ^ 6 = _
    rw [variableChange_a₆, hclear]
    simp only [model, r, t]
    ring
  have hval (a : R) (n : ℕ) : w (algebraMap R K a * u ^ n) ≤ 1 := by
    rw [map_mul, map_pow, hu, one_pow, mul_one]
    exact valuation_le_one _ a
  have h₁ : w (V.a₁ * u) ≤ 1 := by
    rw [← integralModel_a₁_eq R V, ← pow_one u]
    exact hval _ _
  have h₂ : w (V.a₂ * u ^ 2) ≤ 1 := by rw [← integralModel_a₂_eq R V]; exact hval _ _
  have h₃ : w (V.a₃ * u ^ 3) ≤ 1 := by rw [← integralModel_a₃_eq R V]; exact hval _ _
  have h₄ : w (V.a₄ * u ^ 4) ≤ 1 := by rw [← integralModel_a₄_eq R V]; exact hval _ _
  have h₆ : w (V.a₆ * u ^ 6) ≤ 1 := by rw [← integralModel_a₆_eq R V]; exact hval _ _
  have hw₂ : w 2 ≤ 1 := by
    rw [← map_ofNat (algebraMap R K) 2]
    exact valuation_le_one _ 2
  have hone : w 1 ≤ 1 := by rw [map_one]
  have hmul₂ (x : K) : w (2 * x) ≤ w x := by
    rw [map_mul]
    exact mul_le_of_le_one_left zero_le hw₂
  have hp (x : K) (hx : w x ≤ 1) (n : ℕ) : w (x ^ n) ≤ 1 := by
    rw [map_pow]
    exact pow_le_one₀ zero_le hx
  have ⟨hr, hs, ht⟩ : w r ≤ 1 ∧ w s ≤ 1 ∧ w t ≤ 1 := by
    by_cases htwo : w 2 = 1
    · -- A unit 2 determines integrality of s and t from a₁ and a₃.
      have hs : w s ≤ 1 := by simpa only [ha₁, map_mul, htwo, one_mul] using h₁
      have ht := w.map_sub_le h₃ hone
      rw [ha₃, add_sub_cancel_left, map_mul, htwo, one_mul] at ht
      refine ⟨?_, hs, ht⟩
      by_contra! hr
      have hr₂ : w r < w (r ^ 2) := by
        simpa only [map_pow, pow_one] using pow_lt_pow_right₀ hr (show (1 : ℕ) < 2 by decide)
      have hr₃ : w (r ^ 2) < w (r ^ 3) := by
        simpa only [map_pow] using pow_lt_pow_right₀ hr (show (2 : ℕ) < 3 by decide)
      have hlt : w (r ^ 2 - 2 * r - t - t ^ 2) < w (r ^ 3) := by
        refine (w.map_sub_le (w.map_sub_le (w.map_sub_le le_rfl ((hmul₂ r).trans hr₂.le))
          (ht.trans (hr.trans hr₂).le)) ((hp t ht 2).trans (hr.trans hr₂).le)).trans_lt hr₃
      have hrew : V.a₆ * u ^ 6 = r ^ 3 + (r ^ 2 - 2 * r - t - t ^ 2) := by rw [ha₆]; ring
      rw [hrew, w.map_add_eq_of_lt_left hlt] at h₆
      exact (hr.trans (hr₂.trans hr₃)).not_ge h₆
    · -- If 2 is a nonunit, 3 is a unit and the a₂ and a₄ equations constrain r and s.
      have hthree : w 3 = 1 := by
        rw [show (3 : K) = 2 + 1 by norm_num, w.map_add_eq_of_lt_right, map_one]
        rw [map_one]
        exact lt_of_le_of_ne hw₂ htwo
      have hbase := w.map_sub_le h₂ hone
      have hrval : w r = w (V.a₂ * u ^ 2 - 1 + s ^ 2) := by
        conv_lhs => rw [← one_mul (w r), ← hthree, ← map_mul]
        rw [ha₂]
        congr 1
        ring
      have hs : w s ≤ 1 := by
        by_contra! hs
        have hs₂ : w s < w (s ^ 2) := by
          simpa only [map_pow, pow_one] using pow_lt_pow_right₀ hs (show (1 : ℕ) < 2 by decide)
        have hrv : w r = w (s ^ 2) :=
          hrval.trans (w.map_add_eq_of_lt_right (hbase.trans_lt (hs.trans hs₂)))
        have hr₂ : w (s ^ 2) < w (3 * r ^ 2) := by
          simp only [map_mul, hthree, one_mul, map_pow]
          rw [hrv, map_pow, ← pow_mul]
          exact pow_lt_pow_right₀ hs (by decide)
        have hsa₃ : w (s * (V.a₃ * u ^ 3)) ≤ w s := by
          rw [map_mul]
          exact mul_le_of_le_one_right zero_le h₃
        have hrest : w (2 * r - 2 - s * (V.a₃ * u ^ 3)) ≤ w (s ^ 2) := by
          refine w.map_sub_le (w.map_sub_le ((hmul₂ r).trans hrv.le)
            (hw₂.trans (hs.trans hs₂).le)) (hsa₃.trans hs₂.le)
        rw [ha₄, w.map_add_eq_of_lt_left (hrest.trans_lt hr₂)] at h₄
        exact (hs.trans (hs₂.trans hr₂)).not_ge h₄
      have hr : w r ≤ 1 := hrval ▸ w.map_add_le hbase (hp s hs 2)
      refine ⟨hr, hs, ?_⟩
      by_contra! ht
      have hpart : w (r ^ 3 + r ^ 2 - 2 * r) ≤ 1 :=
        w.map_sub_le (w.map_add_le (hp r hr 3) (hp r hr 2)) ((hmul₂ r).trans hr)
      have ht₂ : w t < w (t ^ 2) := by
        simpa only [map_pow, pow_one] using pow_lt_pow_right₀ ht (show (1 : ℕ) < 2 by decide)
      have hlt : w (r ^ 3 + r ^ 2 - 2 * r - t) < w (t ^ 2) :=
        (w.map_sub_le (hpart.trans ht.le) le_rfl).trans_lt ht₂
      rw [ha₆, w.map_sub_eq_of_lt_right hlt] at h₆
      exact (ht.trans ht₂).not_ge h₆
  obtain ⟨u₀, hu₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
  obtain ⟨r₀, hr₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hr
  obtain ⟨s₀, hs₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hs
  obtain ⟨t₀, ht₀⟩ := IsDiscreteValuationRing.exists_lift_of_le_one ht
  have hunit : IsUnit u₀ := by
    have h := hu₀ ▸ hu
    rw [valuation_eq_one_iff_notMem] at h
    simpa [IsDiscreteValuationRing.maximalIdeal] using h
  refine ⟨⟨hunit.unit, r₀, s₀, t₀⟩, ?_⟩
  ext
  · exact (congrArg (algebraMap R K) hunit.unit_spec).trans hu₀
  · exact hr₀
  · exact hs₀
  · exact ht₀

open Polynomial in
/-- At a good prime, the Euler polynomial uses the point count on the explicit integral
equation. The variable change to the selected minimal model reduces over the residue field. -/
theorem localPolynomial_good_integral {p : ℕ} [Fact p.Prime]
    (e : ResidueField R ≃+* ZMod p) (h389 : (389 : ZMod p) ≠ 0) :
    (model K).localPolynomial R =
      1 - C ((p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point) * X +
        C (p : ℤ) * X ^ 2 := by
  let W := model K
  let I := model R
  have hI : I.baseChange K = W := map_model (algebraMap R K)
  have : W.IsIntegral R := ⟨I, hI.symm⟩
  have hΔ : residue R I.Δ ≠ 0 := by
    intro h
    exact h389 (by simpa [I, discriminant, map_ofNat] using congrArg e.toRingHom h)
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have hval : w W.Δ = 1 := by
    rw [← hI, baseChange, map_Δ, valuation_eq_one_iff_notMem]
    exact fun h => hΔ ((residue_eq_zero_iff _).mpr h)
  let V := W.minimal R
  let D := (W.exists_isMinimal R).choose
  have hg : V.HasGoodReduction R := BSD.FermatCubic.minimal_good_of_valuation_eq_one R W hval
  have hu : w (D.u : K) = 1 := by
    have hd := hg.goodReduction
    change w V.Δ = 1 at hd
    rw [show V.Δ = _ from variableChange_Δ W D, map_mul, hval, mul_one, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀] at hd
    exact inv_eq_one.mp ((pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hd)
  obtain ⟨L, hL⟩ := integral_change R D (inferInstance : V.IsIntegral R) hu
  let J := V.integralModel R
  have hJ : J = L • I := by
    apply WeierstrassCurve.map_injective (f := algebraMap R K) (IsFractionRing.injective R K)
    change J.map (algebraMap R K) = (L • I).map (algebraMap R K)
    rw [show J.map (algebraMap R K) = V from baseChange_integralModel_eq R V,
      ← map_variableChange, hL, map_model]
    rfl
  let f := e.toRingHom.comp (residue R)
  let U := V.reduction R
  have : U.IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  have : (model (ZMod p)).IsElliptic := ⟨by rw [discriminant]; exact isUnit_iff_ne_zero.mpr h389⟩
  have hU : U.map e.toRingHom = L.map f • model (ZMod p) := by
    change (J.map (residue R)).map e.toRingHom = _
    rw [WeierstrassCurve.map_map, hJ, ← map_variableChange, map_model]
  have hcard : Nat.card U.toAffine.Point = Nat.card (model (ZMod p)).toAffine.Point := by
    calc
      Nat.card U.toAffine.Point = Nat.card (U.map e.toRingHom).toAffine.Point :=
        (BSD.FermatCubic.card_points_map U e).symm
      _ = Nat.card (L.map f • model (ZMod p)).toAffine.Point :=
        congrArg (fun E : WeierstrassCurve (ZMod p) => Nat.card E.toAffine.Point) hU
      _ = _ := (card_change _ _).symm
  have hq : Nat.card (ResidueField R) = p :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  classical
  change W.localPolynomial R = _
  unfold localPolynomial
  rw [if_pos hg, hq]
  change 1 - C ((p : ℤ) + 1 - Nat.card U.toAffine.Point) * X + C (p : ℤ) * X ^ 2 = _
  rw [hcard]

end Local

open NumberField Polynomial

/-- The Euler polynomial at the place over 2, using the Mathlib model at that place. -/
theorem localPolynomial_two_rat (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 2) :
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 + C (2 : ℤ) * X + C (2 : ℤ) * X ^ 2 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod 2 :=
    ((ResidueField.mapEquiv
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField).trans (ZMod.ringEquivCongr hv)
  rw [baseChange, map_model, localPolynomial_good_integral _ e (by decide)]
  have : (model (ZMod 2)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  rw [card_model_two]
  norm_num [map_neg, neg_mul, sub_neg_eq_add]

/-- The Euler polynomial at the place over 3, using the Mathlib model at that place. -/
theorem localPolynomial_three_rat (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 3) :
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 + C (2 : ℤ) * X + C (3 : ℤ) * X ^ 2 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod 3 :=
    ((ResidueField.mapEquiv
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField).trans (ZMod.ringEquivCongr hv)
  rw [baseChange, map_model, localPolynomial_good_integral _ e (by decide)]
  have : (model (ZMod 3)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  rw [card_model_three]
  norm_num [map_neg, neg_mul, sub_neg_eq_add]

end BSD.RankTwo
