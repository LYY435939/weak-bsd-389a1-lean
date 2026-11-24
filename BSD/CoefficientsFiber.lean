import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Counting cube roots using a multiplicative character of exact order three. -/

namespace BSD.FermatCubic
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
private theorem cube_iff_char_one {χ : MulChar F ℂ} (hχ : orderOf χ = 3)
    {a : F} (ha : a ≠ 0) : (∃ x : F, x ^ 3 = a) ↔ χ a = 1 := by
  classical
  have hp : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hval (x : F) (hx : x ≠ 0) : χ x ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide : 3 ≠ 0), hp, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
  constructor
  · rintro ⟨x, rfl⟩
    rw [map_pow]
    exact hval _ (fun hx => ha (by simp [hx]))
  · intro h
    obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hgen : χ g.val ≠ 1 := by
      intro hg1
      have he := (MulChar.eq_iff hg χ 1).mpr (hg1.trans (MulChar.one_apply_coe g).symm)
      simp [he] at hχ
    have hprim : IsPrimitiveRoot (χ g.val) 3 :=
      isPrimitiveRoot_of_mem_nthRootsFinset Nat.prime_three
        ((mem_nthRootsFinset (by decide : 0 < 3) _).mpr (hval _ g.ne_zero)) hgen
    have hx := hg (Units.mk0 a ha)
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have hk' : g.val ^ k = a := by simpa using congrArg Units.val hk
    obtain ⟨d, rfl⟩ := (hprim.pow_eq_one_iff_dvd k).mp (by rwa [← map_pow, hk'])
    exact ⟨g.val ^ d, by rwa [← pow_mul, Nat.mul_comm]⟩

/-- For a nonzero argument, the cube-root multiset is already a set. -/
private theorem card_cubeRoots (χ : MulChar F ℂ) (hχ : orderOf χ = 3) (a : F) (ha : a ≠ 0) :
    Fintype.card {x : F // x ^ 3 = a} = if χ a = 1 then 3 else 0 := by
  classical
  have hd := χ.orderOf_dvd_card_sub_one
  rw [hχ, ← Fintype.card_units] at hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) 3 hd
  have hζ : IsPrimitiveRoot u.val 3 := IsPrimitiveRoot.coe_units_iff.mpr
    (IsPrimitiveRoot.iff_orderOf.mpr hu)
  let e : {x : F // x ^ 3 = a} ≃ ↥(nthRootsFinset 3 a) :=
    Equiv.subtypeEquivRight (fun x => (mem_nthRootsFinset (by decide : 0 < 3) a).symm)
  rw [Fintype.card_congr e, Fintype.card_coe, nthRootsFinset_def,
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ha), hζ.card_nthRoots,
    cube_iff_char_one hχ ha]

/-- The formula includes the zero fiber, because both characters vanish there. -/
theorem card_cube_fiber_character {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (a : F) :
    (Fintype.card {x : F // x ^ 3 = a} : ℂ) = 1 + χ a + χ⁻¹ a := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [MulChar.map_zero]
  rw [card_cubeRoots χ hχ a ha, MulChar.inv_apply_eq_inv']
  split_ifs with h
  · simp [h]
    norm_num
  have hp : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hval : χ a ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide : 3 ≠ 0), hp, MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)]
  have hquad : χ a ^ 2 + χ a + 1 = 0 := by
    apply (mul_eq_zero.mp (show (χ a - 1) * (χ a ^ 2 + χ a + 1) = 0 by
      linear_combination hval)).resolve_left (sub_ne_zero.mpr h)
  have hne : χ a ≠ 0 := by intro hz; simp [hz] at hval
  field_simp
  linear_combination -hquad

end BSD.FermatCubic
