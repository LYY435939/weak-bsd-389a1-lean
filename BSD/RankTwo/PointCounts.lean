import BSD.RankTwo.SmallEuler

/-! # Finite point counts for the level-389 coefficient table -/

namespace BSD.RankTwo

theorem card_points_five : Nat.card (model (ZMod 5)).toAffine.Point = 9 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : (model (ZMod 5)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  exact card_model_of_affine_card 8 (by decide)

theorem card_points_seven : Nat.card (model (ZMod 7)).toAffine.Point = 13 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : (model (ZMod 7)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  exact card_model_of_affine_card 12 (by decide)

theorem card_points_eleven : Nat.card (model (ZMod 11)).toAffine.Point = 16 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have : (model (ZMod 11)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  exact card_model_of_affine_card 15 (by decide)

theorem card_points_thirteen : Nat.card (model (ZMod 13)).toAffine.Point = 17 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have : (model (ZMod 13)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  exact card_model_of_affine_card 16 (by decide)

theorem card_points_seventeen : Nat.card (model (ZMod 17)).toAffine.Point = 24 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  have : (model (ZMod 17)).IsElliptic := ⟨by rw [discriminant]; decide⟩
  exact card_model_of_affine_card 23 (by decide)

end BSD.RankTwo
