import BSD.EulerCoefficients
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

/-! # Elementary point-count bounds for good finite-place Euler polynomials -/

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

/-- The point at infinity gives the lower bound. Each first coordinate
contributes at most two further points. -/
theorem weierstrass_affine_point_card_bounds {F : Type*} [Field F] [Finite F]
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

open Polynomial in
/-- At a good finite place of ℚ, the linear coefficient of the actual local
polynomial has absolute value at most the residue characteristic. -/
theorem weierstrass_good_localPolynomial_abs_coeff_le (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    let R := v.adicCompletionIntegers ℚ
    let W := E.baseChange (v.adicCompletion ℚ)
    let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
    (W.minimal R).HasGoodReduction R →
      ∃ a : ℤ, |a| ≤ (p : ℤ) ∧ W.localPolynomial R = 1 + C a * X + C (p : ℤ) * X ^ 2 := by
  classical
  dsimp only
  intro hg
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  let U := (W.minimal R).reduction R
  change (W.minimal R).HasGoodReduction R at hg
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e : ResidueField R ≃+* ZMod p :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  have hq : Nat.card (ResidueField R) = p :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)
  have : Finite (ResidueField R) := Finite.of_equiv (ZMod p) e.symm.toEquiv
  have : U.IsElliptic := (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp hg
  have ⟨hmin, hmax⟩ := weierstrass_affine_point_card_bounds U
  rw [hq] at hmax
  have hmin' : 1 ≤ (Nat.card U.toAffine.Point : ℤ) := by exact_mod_cast hmin
  have hmax' : (Nat.card U.toAffine.Point : ℤ) ≤ 2 * (p : ℕ) + 1 := by exact_mod_cast hmax
  let a : ℤ := -(((p : ℕ) : ℤ) + 1 - Nat.card U.toAffine.Point)
  refine ⟨a, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp [a]
    linarith
  · dsimp [a]
    linarith
  · change W.localPolynomial R = _
    simp only [localPolynomial, if_pos hg, hq, a, U, map_neg, neg_mul, sub_eq_add_neg]
    rfl

end BSD
