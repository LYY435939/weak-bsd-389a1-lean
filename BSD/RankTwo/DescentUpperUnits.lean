import BSD.DescentRank
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic

/-! The norm-one integral-unit square classes in a cubic number field. -/

namespace BSD.RankTwo389

open NumberField Module

variable (K : Type*) [Field K] [NumberField K]

/-- Units of the integer ring whose rational field norm is one. -/
def normOneUnits : Subgroup (𝓞 K)ˣ where
  carrier := {u | Algebra.norm ℚ ((u : 𝓞 K) : K) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change Algebra.norm ℚ ((a.val : 𝓞 K) : K) = 1 at ha
    change Algebra.norm ℚ ((b.val : 𝓞 K) : K) = 1 at hb
    change Algebra.norm ℚ (((a*b : (𝓞 K)ˣ) : 𝓞 K) : K) = 1
    simp only [Units.val_mul, map_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change Algebra.norm ℚ ((a.val : 𝓞 K) : K) = 1 at ha
    let f : (𝓞 K)ˣ →* ℚ := (Algebra.norm ℚ).comp
      ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom _))
    change f a⁻¹ = 1
    have hh : f a * f a⁻¹ = 1 := by rw [← map_mul,mul_inv_cancel,map_one]
    change f a = 1 at ha
    rwa [ha,one_mul] at hh

abbrev NormOneAdd := Additive (normOneUnits K)
abbrev NormOneSquareClasses := (NormOneAdd K) ⧸ (nsmulAddMonoidHom (α:=NormOneAdd K) 2).range

private def unitInclusion : NormOneAdd K →ₗ[ℤ] Additive (𝓞 K)ˣ :=
  (normOneUnits K).subtype.toAdditive.toIntLinearMap

instance : Module.Finite ℤ (NormOneAdd K) :=
  Module.Finite.of_injective (unitInclusion K) (fun _ _ h => Subtype.ext h)

/-- The unit rank of a cubic field is at most two. This uses the exact archimedean
place formula and also covers the case of a complex cubic. -/
theorem normOne_finrank_le_two (h3 : finrank ℚ K = 3) : finrank ℤ (NormOneAdd K) ≤ 2 := by
  have hu := (unitInclusion K).finrank_le_finrank_of_injective (fun _ _ h => Subtype.ext h)
  rw [Units.finrank_eq, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces] at hu
  have hp := InfinitePlace.card_add_two_mul_card_eq_rank K
  omega

private theorem normOne_two_torsion_trivial (h3 : finrank ℚ K = 3) :
    (nsmulAddMonoidHom (α:=NormOneAdd K) 2).ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  have hpow : (u.toMul : (𝓞 K)ˣ) ^ 2 = 1 := congrArg (fun t : NormOneAdd K => t.toMul.val) hu
  have hs : ((u.toMul.val : (𝓞 K)ˣ).val)^2 = 1 := by simpa using congrArg Units.val hpow
  rcases sq_eq_one_iff.mp hs with h | h
  · exact Subtype.ext (Units.ext h)
  · exfalso
    have hx := u.toMul.prop
    change Algebra.norm ℚ ((u.toMul.val.val : 𝓞 K) : K) = 1 at hx
    rw [h] at hx
    have he : ((-1 : 𝓞 K) : K) = algebraMap ℚ K (-1) := by simp
    rw [he, Algebra.norm_algebraMap, h3] at hx
    norm_num at hx

/-- This is an unconditional cardinal bound on the arithmetic target of the 389 descent.
It applies to every cubic number field independently of class number or local image. -/
theorem normOne_squareClasses_card_le_four (h3 : finrank ℚ K = 3) :
    Nat.card (NormOneSquareClasses K) ≤ 4 := by
  rw [NormOneSquareClasses, BSD.card_quotient_range_nsmul (by decide : 2 ≠ 0),
    normOne_two_torsion_trivial K h3, AddSubgroup.card_bot, mul_one]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (normOne_finrank_le_two K h3))

instance : Finite (NormOneSquareClasses K) := BSD.finite_quotient_range_nsmul (by decide : 2 ≠ 0)

end BSD.RankTwo389
