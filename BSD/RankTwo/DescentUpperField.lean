import BSD.RankTwo.DescentUpperModel
import BSD.RankTwo.DescentUpper
import BSD.RankTwo.HalvingPolynomials

/-! Identifying Stoll's étale algebra and all its irreducible factors with the concrete
cubic field in which class number and ramification are calculated. -/

namespace BSD.RankTwo389
open Polynomial Algebra WeierstrassCurve NumberField
noncomputable section

abbrev branchPolynomial := shortCurve.toAffine.f

theorem branchPolynomial_irreducible : Irreducible branchPolynomial := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [Affine.natDegree_f]; decide
  · intro x hx
    apply RankTwo.two_torsion_polynomial_ne_zero x
    rw [IsRoot.def, Affine.eval_f] at hx
    norm_num [shortCurve] at hx
    linear_combination 4*hx

private def branchToDescent : AdjoinRoot branchPolynomial →ₐ[ℚ] DescentField :=
  AdjoinRoot.liftAlgHom branchPolynomial (Algebra.ofId ℚ DescentField) (descentRoot/2) (by
    change aeval (descentRoot/2) branchPolynomial = 0
    simp [branchPolynomial, Affine.f,shortCurve]
    linear_combination descentRoot_relation/8)

private def descentToBranch : DescentField →ₐ[ℚ] AdjoinRoot branchPolynomial :=
  AdjoinRoot.liftAlgHom descentPolynomial (Algebra.ofId ℚ _) (2 * AdjoinRoot.root branchPolynomial) (by
    change aeval (2 * AdjoinRoot.root branchPolynomial) descentPolynomial = 0
    have h := AdjoinRoot.aeval_eq (f:=branchPolynomial) branchPolynomial
    have hz : aeval (AdjoinRoot.root branchPolynomial) branchPolynomial = 0 := h.trans AdjoinRoot.mk_self
    change aeval (AdjoinRoot.root branchPolynomial)
      (X^3 + C (1:ℚ)*X^2+C (-2:ℚ)*X+C (1/4:ℚ))=0 at hz
    simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at hz
    simp only [descentPolynomial,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
    norm_num at hz ⊢
    have hscale : (8:AdjoinRoot branchPolynomial) * AdjoinRoot.of branchPolynomial (1/4:ℚ) = 2 := by
      rw [← map_ofNat (AdjoinRoot.of branchPolynomial) 8, ← map_mul]
      norm_num
      exact map_ofNat (AdjoinRoot.of branchPolynomial) 2
    simp only [map_ofNat] at hz ⊢
    linear_combination 8*hz - hscale)

private lemma forward_root : branchToDescent (AdjoinRoot.root branchPolynomial) = descentRoot/2 :=
  AdjoinRoot.liftAlgHom_root ..

private lemma backward_root : descentToBranch descentRoot = 2*AdjoinRoot.root branchPolynomial :=
  AdjoinRoot.liftAlgHom_root ..

/-- The generator of Stoll's étale algebra is half the integral generator. -/
def descentAlgebraEquiv : AdjoinRoot branchPolynomial ≃ₐ[ℚ] DescentField :=
  AlgEquiv.ofAlgHom branchToDescent descentToBranch
    (by apply AdjoinRoot.algHom_ext
        change branchToDescent (descentToBranch descentRoot) = descentRoot
        rw [backward_root,map_mul,map_ofNat,forward_root]
        ring)
    (by apply AdjoinRoot.algHom_ext
        change descentToBranch (branchToDescent (AdjoinRoot.root branchPolynomial)) = _
        rw [forward_root, show descentRoot/2 = algebraMap ℚ DescentField (1/2) * descentRoot by
          norm_num; ring, map_mul, AlgHom.commutes, backward_root]
        change algebraMap ℚ _ (1/2) * (2 * AdjoinRoot.root branchPolynomial) = AdjoinRoot.root _
        rw [← mul_assoc, ← map_ofNat (algebraMap ℚ (AdjoinRoot branchPolynomial)) 2, ← map_mul]
        norm_num)

@[simp] theorem descentAlgebraEquiv_root :
    descentAlgebraEquiv (AdjoinRoot.root branchPolynomial) = descentRoot/2 := forward_root

theorem branchFactor_eq (p : branchPolynomial.Factors) : (p : ℚ[X]) = branchPolynomial :=
  Factors.coe_eq branchPolynomial_irreducible shortCurve.toAffine.monic_f p

def branchFactorEquiv (p : branchPolynomial.Factors) : AdjoinRoot (p:ℚ[X]) ≃ₐ[ℚ] DescentField :=
  (AdjoinRoot.algEquivOfEq ℚ _ _ (branchFactor_eq p)).trans descentAlgebraEquiv

def branchFactorIntegerEquiv (p : branchPolynomial.Factors) :
    shortCurve.toAffine.ringOfIntegersFactor (𝓞 ℚ) p ≃+* 𝓞 DescentField :=
  (IsIntegralClosure.equiv (𝓞 ℚ) (integralClosure (𝓞 ℚ) (AdjoinRoot (p:ℚ[X]))) (AdjoinRoot (p:ℚ[X])) (𝓞 (AdjoinRoot (p:ℚ[X])))).toRingEquiv.trans
    (RingOfIntegers.mapRingEquiv (branchFactorEquiv p).toRingEquiv)

theorem coe_branchFactorIntegerEquiv (p : branchPolynomial.Factors)
    (x : shortCurve.toAffine.ringOfIntegersFactor (𝓞 ℚ) p) :
    algebraMap (𝓞 DescentField) DescentField (branchFactorIntegerEquiv p x) =
      branchFactorEquiv p (algebraMap _ (AdjoinRoot (p:ℚ[X])) x) := by
  apply congrArg (branchFactorEquiv p)
  exact IsIntegralClosure.algebraMap_equiv (𝓞 ℚ) (integralClosure (𝓞 ℚ) (AdjoinRoot (p:ℚ[X])))
    (AdjoinRoot (p:ℚ[X])) (𝓞 (AdjoinRoot (p:ℚ[X]))) x

end
end BSD.RankTwo389
