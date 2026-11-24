import BSD.RankTwo.Curve
import BSD.RankTwo.DescentUpperClass
import BSD.RankTwo.DescentUpperUnits

/-! The actual cubic descent element for the rational points of 389.a1. -/

namespace BSD.RankTwo389
open Polynomial Algebra

noncomputable section

/-- The linear factor of the completed-square cubic, normalized so its norm is a square. -/
def descentValue (x : ℚ) : DescentField :=
  2 * (algebraMap ℚ DescentField (2*x) - descentRoot)

theorem norm_sub_gen {K : Type*} [Field K] [NumberField K] (B : PowerBasis ℚ K) (r : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K r - B.gen) = (minpoly ℚ B.gen).eval r := by
  classical
  rw [← charpoly_leftMulMatrix B, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det B.basis,
    map_sub, AlgHom.commutes]
  rfl

theorem descentValue_norm (x : ℚ) :
    Algebra.norm ℚ (descentValue x) = 16 * (4*x^3+4*x^2-8*x+1) := by
  have h2 : Algebra.norm ℚ (2:DescentField) = 2^3 := by
    calc
      _ = Algebra.norm ℚ (algebraMap ℚ DescentField 2) := congrArg (Algebra.norm ℚ) (map_ofNat (algebraMap ℚ DescentField) 2).symm
      _ = _ := by rw [Algebra.norm_algebraMap, descentField_finrank]
  rw [descentValue, map_mul, h2,
    ← descentPowerBasis_gen, norm_sub_gen, descentPowerBasis_gen, descentRoot_minpoly]
  simp [descentPolynomial]
  ring

/-- The norm of the Kummer element of every actual affine point is a nonzero rational square. -/
theorem descentValue_point_norm {x y : ℚ} (h : RankTwo.curve.toAffine.Equation x y) :
    Algebra.norm ℚ (descentValue x) = (8*y+4)^2 := by
  rw [descentValue_norm]
  have he := (RankTwo.equation_iff x y).mp h
  linear_combination -64*he

theorem descentValue_ne_zero (x : ℚ) : descentValue x ≠ 0 := by
  intro he
  have h := (mul_eq_zero.mp he).resolve_left (by norm_num : (2:DescentField) ≠ 0)
  have hroot : descentRoot = algebraMap ℚ DescentField (2*x) := (sub_eq_zero.mp h).symm
  have hm := minpoly.degree_eq_one_iff (A:=ℚ) (x:=descentRoot) |>.mpr ⟨2*x,hroot.symm⟩
  rw [descentRoot_minpoly, descentPolynomial.degree_eq_natDegree descentPolynomial_monic.ne_zero,
    descentPolynomial_natDegree] at hm
  norm_num at hm

private def branchRoot : DescentField := descentRoot / 2

private lemma branchRoot_relation :
    branchRoot^3+branchRoot^2-2*branchRoot = -(1/4:DescentField) := by
  dsimp [branchRoot]
  linear_combination descentRoot_relation/8

private lemma descentValue_eq (x : ℚ) :
    descentValue x = 4*(algebraMap ℚ DescentField x - branchRoot) := by
  simp [descentValue,branchRoot]
  ring

/-- Evaluating the chord (including a tangent) at the cubic branch point shows the product
of the Kummer elements for P, Q and P+Q is a square in the actual cubic field. -/
theorem descentValue_chord {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : RankTwo.curve.toAffine.Equation x₁ y₁) (h₂ : RankTwo.curve.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁=x₂ ∧ y₁=RankTwo.curve.toAffine.negY x₂ y₂)) :
    let s := RankTwo.curve.toAffine.slope x₁ x₂ y₁ y₂
    IsSquare (descentValue x₁ * descentValue x₂ *
      descentValue (RankTwo.curve.toAffine.addX x₁ x₂ s)) := by
  let s := RankTwo.curve.toAffine.slope x₁ x₂ y₁ y₂
  let f := algebraMap ℚ DescentField
  let z := RankTwo.curve.toAffine.addX x₁ x₂ s
  let d := f s*(branchRoot-f x₁)+f y₁
  have hyp := RankTwo.curve.toAffine.addPolynomial_slope h₁ h₂ hxy
  change RankTwo.curve.toAffine.addPolynomial x₁ y₁ s = -((X-C x₁)*(X-C x₂)*(X-C z)) at hyp
  have hev := congrArg (fun p : ℚ[X] => p.eval₂ f branchRoot) hyp
  rw [WeierstrassCurve.Affine.addPolynomial_eq] at hev
  simp only [Cubic.toPoly, eval₂_neg, eval₂_sub, eval₂_mul, eval₂_add, eval₂_pow, eval₂_C,
    eval₂_X, RankTwo.curve, RankTwo.model, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, map_one, map_ofNat] at hev
  norm_num at hev
  refine ⟨8*(d+1/2),?_⟩
  change descentValue x₁ * descentValue x₂ * descentValue z = _
  rw [descentValue_eq,descentValue_eq,descentValue_eq]
  change 4*(f x₁-branchRoot)*(4*(f x₂-branchRoot))*(4*(f z-branchRoot)) = _
  dsimp only [d]
  have hfq (q : ℚ) : f q = (q:DescentField) := by simpa only [Rat.cast_id] using map_ratCast f q
  simp only [hfq]
  linear_combination -64*hev + -64*branchRoot_relation

/-- The small unit-square-class target attached to the actual descent field. -/
theorem descent_normOne_card_le_four : Nat.card (NormOneSquareClasses DescentField) ≤ 4 :=
  normOne_squareClasses_card_le_four DescentField descentField_finrank

end
end BSD.RankTwo389
