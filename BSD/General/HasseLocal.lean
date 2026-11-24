import BSD.EulerCoefficients
import BSD.General.HasseRoots
import Mathlib.Tactic

/-! # The Hasse bound and the Euler factors at finite places of ℚ -/

namespace BSD

open WeierstrassCurve IsDedekindDomain IsLocalRing NumberField

/-- The point-count Hasse bound at each finite place of good reduction. -/
def HasHasseBoundAtGoodPlaces (E : WeierstrassCurve ℚ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 ℚ),
    let R := v.adicCompletionIntegers ℚ
    let W := E.baseChange (v.adicCompletion ℚ)
    let q := Nat.card (ResidueField R)
    (W.minimal R).HasGoodReduction R →
      |(q : ℝ) + 1 - (Nat.card ((W.minimal R).reduction R).toAffine.Point : ℝ)| ≤
        2 * Real.sqrt (q : ℝ)

private lemma residueField_card_eq_rational_prime (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) =
      (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)

open Polynomial in
private lemma good_localPolynomial_of_hasse (E : WeierstrassCurve ℚ)
    (h : HasHasseBoundAtGoodPlaces E) (v : HeightOneSpectrum (𝓞 ℚ)) :
    let R := v.adicCompletionIntegers ℚ
    let W := E.baseChange (v.adicCompletion ℚ)
    let q := Nat.card (ResidueField R)
    (W.minimal R).HasGoodReduction R →
      ∃ a : ℤ, |(a : ℝ)| ≤ 2 * Real.sqrt (q : ℝ) ∧
        W.localPolynomial R = 1 + C a * X + C (q : ℤ) * X ^ 2 := by
  classical
  dsimp only
  intro hg
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  let q := Nat.card (ResidueField R)
  let a : ℤ := -((q : ℤ) + 1 - Nat.card ((W.minimal R).reduction R).toAffine.Point)
  refine ⟨a, ?_, ?_⟩
  · simpa only [a, Int.cast_neg, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_neg] using h v hg
  · simp only [localPolynomial, if_pos hg, a, q, R, W, map_neg, neg_mul, sub_eq_add_neg]

private lemma reciprocal_linear_coeff_abs_le_one {a : ℤ} (ha : |a| ≤ 1) (k : ℕ) :
    |(((PowerSeries.invOfUnit (1 + PowerSeries.C a * PowerSeries.X) 1).coeff k : ℤ) : ℝ)| ≤
      1 := by
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
  have hbound (j : ℕ) : |f.coeff j| ≤ 1 := by
    induction j with
    | zero => simp [hzero]
    | succ j ih =>
      rw [hrec, abs_neg, abs_mul]
      simpa using mul_le_mul ha ih (abs_nonneg (f.coeff j)) (by norm_num : (0 : ℤ) ≤ 1)
  exact_mod_cast hbound k

/-- At a finite place of bad reduction, every local coefficient has absolute value at most one. -/
theorem weierstrass_localPowerSeries_abs_coeff_le_one_of_badReduction
    (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    let R := v.adicCompletionIntegers ℚ
    let W := E.baseChange (v.adicCompletion ℚ)
    ¬(W.minimal R).HasGoodReduction R →
      ∀ k : ℕ, |(((W.localPowerSeries R).coeff k : ℤ) : ℝ)| ≤ 1 := by
  classical
  dsimp only
  intro hbad k
  rw [localPowerSeries]
  simp only [localPolynomial, if_neg hbad]
  split_ifs
  · simpa [sub_eq_add_neg] using reciprocal_linear_coeff_abs_le_one (a := -1) (by norm_num) k
  · simpa using reciprocal_linear_coeff_abs_le_one (a := 1) (by norm_num) k
  · simpa using reciprocal_linear_coeff_abs_le_one (a := 0) (by norm_num) k

open Polynomial in
/-- At a good finite place, the Euler polynomial factors over `ℂ` into terms
whose reciprocal roots both have modulus the square root of the residue cardinality. -/
theorem weierstrass_localPolynomial_map_complex_of_goodReduction (E : WeierstrassCurve ℚ)
    (h : HasHasseBoundAtGoodPlaces E) (v : HeightOneSpectrum (𝓞 ℚ)) :
    let R := v.adicCompletionIntegers ℚ
    let W := E.baseChange (v.adicCompletion ℚ)
    let q := Nat.card (ResidueField R)
    (W.minimal R).HasGoodReduction R →
      ∃ α β : ℂ, (W.localPolynomial R).map (Int.castRingHom ℂ) =
          (1 - C α * X) * (1 - C β * X) ∧
        ‖α‖ = Real.sqrt (q : ℝ) ∧ ‖β‖ = Real.sqrt (q : ℝ) := by
  dsimp only
  intro hg
  let q := Nat.card (ResidueField (v.adicCompletionIntegers ℚ))
  obtain ⟨a, ha, hpoly⟩ := good_localPolynomial_of_hasse E h v hg
  change |(a : ℝ)| ≤ 2 * Real.sqrt (q : ℝ) at ha
  obtain ⟨α, β, hsum, hprod, hα, hβ⟩ :=
    hasse_quadratic_roots (Nat.cast_nonneg q) ha
  refine ⟨α, β, ?_, hα, hβ⟩
  have hsum' : C α + C β = -C (a : ℂ) := by
    rw [← map_add, hsum, Complex.ofReal_intCast, map_neg]
  have hprod' : C α * C β = C (q : ℂ) := by
    rw [← map_mul, hprod, Complex.ofReal_natCast]
  calc
    _ = 1 + C (a : ℂ) * X + C (q : ℂ) * X ^ 2 := by
      simp [hpoly, q]
    _ = (1 - C α * X) * (1 - C β * X) := by
      rw [← neg_neg (C (a : ℂ)), ← hsum', ← hprod']
      ring

/-- The Hasse bound implies the prime-power coefficient estimate for the
formal Hasse–Weil L-function. -/
theorem weierstrass_LFunction_abs_prime_pow_le_of_hasse (E : WeierstrassCurve ℚ)
    (h : HasHasseBoundAtGoodPlaces E) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |(E.LFunction (p ^ k) : ℝ)| ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k := by
  classical
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let v := e.symm ⟨p, hp⟩
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)
  have hq : Nat.card (ResidueField R) = p :=
    (residueField_card_eq_rational_prime v).trans hv
  have hcoeff := weierstrass_LFunction_apply_prime_pow E v k
  rw [hv, localPowerSeries] at hcoeff
  rw [hcoeff]
  change |(((PowerSeries.invOfUnit (W.localPolynomial R : PowerSeries ℤ) 1).coeff k : ℤ) : ℝ)| ≤ _
  by_cases hg : (W.minimal R).HasGoodReduction R
  · obtain ⟨a, ha, hpoly⟩ := good_localPolynomial_of_hasse E h v hg
    change |(a : ℝ)| ≤ 2 * Real.sqrt (Nat.card (ResidueField R) : ℝ) at ha
    rw [hq] at ha
    change W.localPolynomial R = _ at hpoly
    rw [hpoly, hq]
    have hp₀ : (0 : ℝ) ≤ ((p : ℤ) : ℝ) := by positivity
    have ha' : |(a : ℝ)| ≤ 2 * Real.sqrt ((p : ℤ) : ℝ) := by simpa using ha
    simpa only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X, Polynomial.coe_pow, Int.cast_natCast] using
        hasse_reciprocal_quadratic_bound hp₀ ha' k
  · have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_lt.le)
    have hk : (1 : ℝ) ≤ k + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hRhs : (1 : ℝ) ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k := by
      simpa only [one_mul] using
        mul_le_mul hk (one_le_pow₀ hsqrt (n := k)) (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : (0 : ℝ) ≤ k + 1)
    exact (weierstrass_localPowerSeries_abs_coeff_le_one_of_badReduction E v hg k).trans hRhs

end BSD
