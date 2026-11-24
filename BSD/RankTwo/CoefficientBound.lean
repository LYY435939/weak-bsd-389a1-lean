import BSD.EulerCoefficients
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

/-!
# An elementary bound for the Hasse–Weil coefficients

Over a finite field each first coordinate gives at most two affine points.
This bounds the linear coefficient of each good Euler polynomial. The
reciprocal coefficients satisfy a two-term recurrence, giving a uniform
quadratic bound after combining prime powers by multiplicativity.
-/

namespace BSD

open WeierstrassCurve IsDedekindDomain IsLocalRing NumberField

private lemma affine_fiber_card_le_two {F : Type*} [Field F]
    (W : WeierstrassCurve F) (x : F) :
    Nat.card {y : F // W.toAffine.Equation x y} ≤ 2 := by
  classical
  let A := {y : F // W.toAffine.Equation x y}
  by_cases h : Nonempty A
  · let a := Classical.choice h
    let choose (y : A) : Bool := decide (y = a)
    have hi : Function.Injective choose := by
      intro y z hchoose
      by_cases hy : y = a
      · have hz : z = a := by simpa [choose, hy] using hchoose.symm
        exact hy.trans hz.symm
      · have hz : z ≠ a := by simpa [choose, hy] using hchoose.symm
        have hy' := (Affine.Y_eq_of_X_eq y.2 a.2 rfl).resolve_left
          (fun hval => hy (Subtype.ext hval))
        have hz' := (Affine.Y_eq_of_X_eq z.2 a.2 rfl).resolve_left
          (fun hval => hz (Subtype.ext hval))
        exact Subtype.ext (hy'.trans hz'.symm)
    simpa using Nat.card_le_card_of_injective choose hi
  · have : IsEmpty A := not_nonempty_iff.mp h
    change Nat.card A ≤ 2
    simp

private lemma card_points_bounds {F : Type*} [Field F] [Finite F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    1 ≤ Nat.card W.toAffine.Point ∧ Nat.card W.toAffine.Point ≤ 2 * Nat.card F + 1 := by
  classical
  let := Fintype.ofFinite F
  let e : {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, {y : F // W.toAffine.Equation x y} :=
    { toFun := fun xy => ⟨xy.1.1, ⟨xy.1.2, xy.2⟩⟩
      invFun := fun xy => ⟨(xy.1, xy.2.1), xy.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr W.toAffine.pointEquiv]
  change 1 ≤ Nat.card (Option _) ∧ Nat.card (Option _) ≤ _
  rw [Finite.card_option, Nat.card_congr e, Nat.card_sigma]
  constructor
  · omega
  · apply Nat.add_le_add_right
    calc
      _ ≤ ∑ _x : F, (2 : ℕ) := Finset.sum_le_sum fun x _ => affine_fiber_card_le_two W x
      _ = _ := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

private lemma reciprocal_quadratic_coeff_le {p a b : ℤ} (hp : 2 ≤ p)
    (ha : |a| ≤ p) (hb : |b| ≤ p) (k : ℕ) :
    |(PowerSeries.invOfUnit
      (1 + PowerSeries.C a * PowerSeries.X + PowerSeries.C b * PowerSeries.X ^ 2)
        1).coeff k| ≤ (p ^ 2) ^ k := by
  let D : PowerSeries ℤ := 1 + PowerSeries.C a * PowerSeries.X +
    PowerSeries.C b * PowerSeries.X ^ 2
  let f := PowerSeries.invOfUnit D 1
  have hInv : D * f = 1 := PowerSeries.mul_invOfUnit D 1 (by simp [D])
  have hzero : f.coeff 0 = 1 := by
    simp [f, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_invOfUnit]
  have hone : f.coeff 1 = -a := by
    have h := congrArg (PowerSeries.coeff (0 + 1)) hInv
    simp only [D, add_mul, mul_assoc, one_mul, map_add, PowerSeries.coeff_C_mul] at h
    rw [PowerSeries.coeff_succ_X_mul, hzero, PowerSeries.coeff_X_pow_mul'] at h
    norm_num [PowerSeries.coeff_one] at h
    linarith
  have hrec (j : ℕ) :
      f.coeff (j + 2) = -(a * f.coeff (j + 1) + b * f.coeff j) := by
    have h := congrArg (PowerSeries.coeff (j + 2)) hInv
    simp only [D, add_mul, mul_assoc, one_mul, map_add, PowerSeries.coeff_C_mul] at h
    rw [PowerSeries.coeff_succ_X_mul (j + 1), PowerSeries.coeff_X_pow_mul] at h
    simp [PowerSeries.coeff_one] at h
    linarith
  have hp1 : 0 ≤ p + 1 := by omega
  have hbound (j : ℕ) : |f.coeff j| ≤ (p + 1) ^ j := by
    induction j using Nat.twoStepInduction with
    | zero => simp [hzero]
    | one => simpa [hone] using ha.trans (show p ≤ p + 1 by omega)
    | more j hj hj1 =>
      calc
        |f.coeff (j + 2)| ≤ |a * f.coeff (j + 1)| + |b * f.coeff j| := by
          rw [hrec, abs_neg]
          exact abs_add_le _ _
        _ ≤ p * (p + 1) ^ (j + 1) + p * (p + 1) ^ j := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul ha hj1 (abs_nonneg _) (by omega))
            (mul_le_mul hb hj (abs_nonneg _) (by omega))
        _ = (p + 1) ^ j * (p * (p + 1) + p) := by rw [pow_succ]; ring
        _ ≤ (p + 1) ^ (j + 2) := by
          rw [pow_add]
          exact mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg hp1 _)
  have hpSq : p + 1 ≤ p ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ p - 2 by omega)]
  exact (hbound k).trans (pow_le_pow_left₀ hp1 hpSq k)

open Polynomial in
private lemma localPolynomial_has_bounded_coefficients (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
    ∃ a b : ℤ, |a| ≤ p ∧ |b| ≤ p ∧
      (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
        1 + C a * X + C b * X ^ 2 := by
  classical
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  let U := (W.minimal R).reduction R
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  have hq : Nat.card (ResidueField R) = p :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)
  have : Finite (ResidueField R) := Finite.of_equiv (ZMod p) e.symm.toEquiv
  have hp : 2 ≤ ((p : ℕ) : ℤ) := by exact_mod_cast p.2.two_le
  have hpOne : (1 : ℤ) ≤ (p : ℕ) := by omega
  change ∃ a b : ℤ, |a| ≤ (p : ℕ) ∧ |b| ≤ (p : ℕ) ∧
    W.localPolynomial R = 1 + C a * X + C b * X ^ 2
  unfold localPolynomial
  split_ifs with hg hs hm
  · have : U.IsElliptic := (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp hg
    have ⟨hmin, hmax⟩ := card_points_bounds U
    rw [hq] at hmax
    have hmin' : 1 ≤ (Nat.card U.toAffine.Point : ℤ) := by exact_mod_cast hmin
    have hmax' : (Nat.card U.toAffine.Point : ℤ) ≤ 2 * (p : ℕ) + 1 := by exact_mod_cast hmax
    refine ⟨-(((p : ℕ) : ℤ) + 1 - Nat.card U.toAffine.Point), (p : ℕ), ?_, ?_, ?_⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp
    · rw [hq]
      simp [sub_eq_add_neg, U]
      ring
  · exact ⟨-1, 0, by simpa using hpOne, by simp, by simp [sub_eq_add_neg]⟩
  · exact ⟨1, 0, by simpa using hpOne, by simp, by simp⟩
  · exact ⟨0, 0, by simp, by simp, by simp⟩

/-- The prime-power coefficient of the formal Hasse–Weil L-function satisfies
the quadratic bound. -/
theorem weierstrass_LFunction_abs_apply_prime_pow_le (E : WeierstrassCurve ℚ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |E.LFunction (p ^ k)| ≤ ((p ^ k : ℕ) : ℤ) ^ 2 := by
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let v := e.symm ⟨p, hp⟩
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)
  obtain ⟨a, b, ha, hb, hlocal⟩ := localPolynomial_has_bounded_coefficients E v
  rw [hv] at ha hb
  rw [← hv, weierstrass_LFunction_apply_prime_pow, localPowerSeries, hlocal, hv]
  push_cast
  simpa only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.coe_pow, ← pow_mul, Nat.mul_comm k 2] using
      reciprocal_quadratic_coeff_le (by exact_mod_cast hp.two_le) ha hb k

/-- For every rational Weierstrass curve, the formal Hasse–Weil coefficient at
`n` has absolute value at most `n²`. -/
theorem weierstrass_LFunction_abs_apply_le_sq (E : WeierstrassCurve ℚ) (n : ℕ) :
    |E.LFunction n| ≤ (n : ℤ) ^ 2 := by
  have hmul := weierstrass_LFunction_isMultiplicative E
  induction n using Nat.recOnPrimePow with
  | zero => simp
  | one => simp [hmul.map_one]
  | prime_pow_mul m p k hp hpm _ ih =>
    rw [hmul.map_mul_of_coprime ((hp.coprime_iff_not_dvd.mpr hpm).pow_left k),
      abs_mul, Nat.cast_mul, mul_pow]
    exact mul_le_mul (weierstrass_LFunction_abs_apply_prime_pow_le E hp k) ih
      (abs_nonneg _) (sq_nonneg _)

/-- The same bound for the complex coefficients of the analytic Dirichlet series. -/
theorem weierstrass_LFunction_norm_apply_le_sq (E : WeierstrassCurve ℚ) (n : ℕ) :
    ‖(E.LFunction n : ℂ)‖ ≤ (n : ℝ) ^ 2 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast weierstrass_LFunction_abs_apply_le_sq E n

end BSD
