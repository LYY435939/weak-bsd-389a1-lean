import BSD.RankTwo.DescentUpperField
import BSD.RankTwo.DescentBadPlaces
import BSD.RankTwo.DescentUpperUnramified
import BSD.RankTwo.DescentUpperDyadic
import BSD.RankTwo.DescentUpperTarget
import BSD.RankTwo.DescentUpperCounting
import BSD.RankTwo.MordellWeil

/-! The exact Mordell–Weil rank and 2-Selmer order of 389.a1. -/

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain NumberField Polynomial
open scoped Classical
namespace BSD.RankTwo389
noncomputable section

private abbrev branchFactor : branchPolynomial.Factors :=
  ⟨branchPolynomial,shortCurve.toAffine.monic_f,branchPolynomial_irreducible,dvd_rfl⟩

private def squareClassEquiv := Units.modPow.congr (branchFactorEquiv branchFactor).toMulEquiv 2

/-- Stoll's full 2-Selmer group for the completed-square model of 389.a1. -/
abbrev twoSelmer := shortCurve.toAffine.selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion)

private lemma proj_unit (a : shortCurve.toAffine.Aˣ) :
    Units.map (AdjoinRoot.projFactor shortCurve.toAffine.f_ne_zero shortCurve.toAffine.squarefree_f
        branchFactor).toMonoidHom a = a := by
  apply Units.ext
  obtain ⟨q,hq⟩ := AdjoinRoot.mk_surjective a.val
  change AdjoinRoot.projFactor _ _ branchFactor a.val = a.val
  rw [← hq,AdjoinRoot.projFactor_mk]

/-- Every 2-Selmer class of this curve is represented by an integral unit of norm one. -/
private theorem selmer_normOne_representatives (c : twoSelmer) :
    ∃ v : (𝓞 DescentField)ˣ, Algebra.norm ℤ (v : 𝓞 DescentField) = 1 ∧
      squareClassEquiv c.val = QuotientGroup.mk
        (Units.map (algebraMap (𝓞 DescentField) DescentField).toMonoidHom v) := by
  classical
  let _ := descentRingOfIntegers_isPrincipal
  obtain ⟨a,ha⟩ := QuotientGroup.mk_surjective c.val
  have hsel := shortCurve_selmer_le_dyadic_inf_ker c.prop
  rw [← ha] at hsel
  obtain ⟨hselOdd,hselNorm⟩ := hsel
  let a' : (AdjoinRoot (branchFactor:ℚ[X]))ˣ := a
  let e := branchFactorEquiv branchFactor
  let u : DescentFieldˣ := (Units.mapEquiv e.toMulEquiv) a'
  have hns : IsSquare (Algebra.norm ℚ (u : DescentField)) := by
    change Units.modPow.map (Algebra.norm ℚ) 2 (QuotientGroup.mk a) = 1 at hselNorm
    rw [Units.modPow.map_mk, Units.modPow.mk_eq_one_iff_isSquare] at hselNorm
    change IsSquare (Algebra.norm ℚ (e a.val))
    change IsSquare (Algebra.norm ℚ (a : shortCurve.toAffine.A)) at hselNorm
    exact (Algebra.norm_eq_of_algEquiv e (a.val : AdjoinRoot (branchFactor:ℚ[X]))).symm ▸ hselNorm
  have heven (w : HeightOneSpectrum (𝓞 DescentField)) : (2:ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    by_cases hw : 2 ∈ w.asIdeal
    · exact dyadic_square_norm_even w hw u hns
    have hv := odd_factor_parity branchFactor a hselOdd w hw
    dsimp only at hv
    rw [proj_unit] at hv
    exact hv
  rw [← ha]
  exact exists_normOneIntegralUnit_squareClass u heven hns

/-- The true 2-Selmer group has at most four elements. -/
theorem card_selmer_le_four : Nat.card twoSelmer ≤ 4 :=
  card_subgroup_le_four_of_normOneIntegralUnit_representatives descentField_finrank twoSelmer
    squareClassEquiv selmer_normOne_representatives

/-- The two-descent upper bound on the rational point rank. -/
theorem rational_finrank_le_two : Module.finrank ℤ RankTwo.curve.toAffine.Point ≤ 2 := by
  let _ : AddGroup.FG shortCurve.toAffine.Point := fg_point_of_numberField
  let _ : Finite twoSelmer :=
    (finite_and_card_subgroup_le_four_of_normOneIntegralUnit_representatives descentField_finrank
      twoSelmer squareClassEquiv selmer_normOne_representatives).1
  have hi := shortCurve.toAffine.pow_rank_le_card_of_range_μ_le
    (shortCurve.toAffine.range_μ_le_selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion))
  have h := hi.trans card_selmer_le_four
  have hcard : 0 < Nat.card (nsmulAddMonoidHom (α:=shortCurve.toAffine.Point) 2).ker := by
    let _ : Module.Finite ℤ shortCurve.toAffine.Point := Module.Finite.iff_addGroup_fg.mpr inferInstance
    have := BSD.finite_ker_nsmul (G:=shortCurve.toAffine.Point) (by decide : 2 ≠ 0)
    exact Nat.card_pos
  rw [← shortCurveEquiv.toIntLinearEquiv.finrank_eq]
  by_contra! h3
  have hp : (2:ℕ)^3 ≤ 2 ^ Module.finrank ℤ shortCurve.toAffine.Point :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h3
  nlinarith

/-- The Mordell–Weil rank of the fixed curve is two. -/
theorem rational_finrank_eq_two : Module.finrank ℤ RankTwo.curve.toAffine.Point = 2 :=
  le_antisymm rational_finrank_le_two RankTwo.two_le_rational_finrank

private lemma four_le_card_descent_image :
    4 ≤ Nat.card (μ (W := shortCurve.toAffine)).range := by
  let _ : AddGroup.FG shortCurve.toAffine.Point := fg_point_of_numberField
  let _ : Module.Finite ℤ shortCurve.toAffine.Point := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have := BSD.finite_ker_nsmul (G:=shortCurve.toAffine.Point) (by decide : 2 ≠ 0)
  have hc := Nat.card_pos (α := (nsmulAddMonoidHom (α:=shortCurve.toAffine.Point) 2).ker)
  rw [shortCurve.toAffine.card_range_μ, shortCurveEquiv.toIntLinearEquiv.finrank_eq,
    rational_finrank_eq_two]
  omega

/-- The two independent rational directions account for the entire two-Selmer group. -/
theorem card_twoSelmer_eq_four : Nat.card twoSelmer = 4 := by
  let _ : Finite twoSelmer :=
    (finite_and_card_subgroup_le_four_of_normOneIntegralUnit_representatives descentField_finrank
      twoSelmer squareClassEquiv selmer_normOne_representatives).1
  have hle := shortCurve.toAffine.range_μ_le_selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion)
  exact le_antisymm card_selmer_le_four
    (four_le_card_descent_image.trans (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)))

/-- Every local-solubility class in Stoll's full 2-Selmer group comes from a rational point. -/
theorem range_mu_eq_twoSelmer : (μ (W := shortCurve.toAffine)).range = twoSelmer := by
  let _ : Finite twoSelmer :=
    (finite_and_card_subgroup_le_four_of_normOneIntegralUnit_representatives descentField_finrank
      twoSelmer squareClassEquiv selmer_normOne_representatives).1
  apply Subgroup.eq_of_le_of_card_ge
    (shortCurve.toAffine.range_μ_le_selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion))
  exact card_selmer_le_four.trans four_le_card_descent_image

end
end BSD.RankTwo389
