import BSD.RankTwo.DescentUpperUnits
import BSD.RankTwo.DescentUpperTarget
import EllipticCurves.WeakMordellWeil

open scoped NumberField

namespace BSD.RankTwo389

variable (K : Type*) [Field K] [NumberField K]

private def normOneUnitToFieldSquareClass :
    NormOneAdd K →+ Additive (Units.modPow K 2) :=
  ((QuotientGroup.mk' _).comp
    ((Units.map (algebraMap (𝓞 K) K).toMonoidHom).comp (normOneUnits K).subtype)).toAdditive

set_option maxHeartbeats 1000000 in
/-- The map from norm-one unit square classes to the number field's square classes. -/
private def normOneSquareClassesToField :
    NormOneSquareClasses K →+ Additive (Units.modPow K 2) :=
  QuotientAddGroup.lift (nsmulAddMonoidHom (α := NormOneAdd K) 2).range
    (normOneUnitToFieldSquareClass K) (by
    rintro _ ⟨v, rfl⟩
    change normOneUnitToFieldSquareClass K (2 • v) = 0
    rw [map_nsmul]
    change ((normOneUnitToFieldSquareClass K v).toMul : Units.modPow K 2) ^ 2 = 1
    exact Units.modPow.pow_eq_one _)

variable {K} {G : Type*} [CommGroup G]

/-- A subgroup whose elements are represented by norm-one integral units is finite, with at most
four elements when the number field has degree three. -/
theorem finite_and_card_subgroup_le_four_of_normOneIntegralUnit_representatives
    (h3 : Module.finrank ℚ K = 3) (S : Subgroup G) (e : G ≃* Units.modPow K 2)
    (hRep : ∀ m : S, ∃ v : (𝓞 K)ˣ, Algebra.norm ℤ (v : 𝓞 K) = 1 ∧
      e m.val = QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K).toMonoidHom v)) :
    Finite S ∧ Nat.card S ≤ 4 := by
  let f (m : NormOneSquareClasses K) : Units.modPow K 2 :=
    (normOneSquareClassesToField K m).toMul
  have hmem (m : S) : e m.val ∈ Set.range f := by
    obtain ⟨v, hv, hm⟩ := hRep m
    have hv' : v ∈ normOneUnits K := by
      change Algebra.norm ℚ ((v : 𝓞 K) : K) = 1
      rw [← Algebra.coe_norm_int, hv, Int.cast_one]
    let v' : NormOneAdd K := Additive.ofMul ⟨v, hv'⟩
    refine ⟨QuotientAddGroup.mk v', ?_⟩
    change QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K).toMonoidHom v) = e m.val
    exact hm.symm
  let g (m : S) : Set.range f := ⟨e m.val, hmem m⟩
  have hg : Function.Injective g := fun _ _ h ↦ Subtype.ext (e.injective (congrArg Subtype.val h))
  let : Finite (Set.range f) := Finite.of_surjective _ Set.rangeFactorization_surjective
  have hr : Nat.card (Set.range f) ≤ Nat.card (NormOneSquareClasses K) :=
    Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
  exact ⟨Finite.of_injective g hg,
    ((Nat.card_le_card_of_injective g hg).trans hr).trans
      (normOne_squareClasses_card_le_four K h3)⟩

theorem card_subgroup_le_four_of_normOneIntegralUnit_representatives
    (h3 : Module.finrank ℚ K = 3) (S : Subgroup G) (e : G ≃* Units.modPow K 2)
    (hRep : ∀ m : S, ∃ v : (𝓞 K)ˣ, Algebra.norm ℤ (v : 𝓞 K) = 1 ∧
      e m.val = QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K).toMonoidHom v)) :
    Nat.card S ≤ 4 :=
  (finite_and_card_subgroup_le_four_of_normOneIntegralUnit_representatives h3 S e hRep).2

end BSD.RankTwo389
