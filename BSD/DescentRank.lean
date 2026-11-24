import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

/-! # Rank certificates from descent

Multiplication by a nonzero natural number on a finitely generated abelian group
has cokernel of cardinality equal to the order of its kernel times a power of
the multiplier. A finite target for an injection from this cokernel provides
an upper rank bound, and independent points provide the matching lower bound.
-/

namespace BSD

open Module

variable {G : Type*} [AddCommGroup G] [Module.Finite ℤ G]

private def nsmulKerCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℕ) :
    (nsmulAddMonoidHom (α := A) n).ker ≃ (nsmulAddMonoidHom (α := B) n).ker :=
  e.toEquiv.subtypeEquiv fun x ↦ by
    change (n • x = 0) ↔ n • e x = 0
    rw [← map_nsmul, e.map_eq_zero_iff]

/-- The subgroup killed by multiplication by a nonzero natural number is finite. -/
theorem finite_ker_nsmul {n : ℕ} (hn : n ≠ 0) :
    Finite (nsmulAddMonoidHom (α := G) n).ker := by
  let T := Submodule.torsion ℤ G
  let : Finite T := Module.finite_of_fg_torsion T Submodule.torsion_isTorsion
  let f : (nsmulAddMonoidHom (α := G) n).ker → T := fun x ↦
    ⟨x.1, (Submodule.mem_torsion_iff x.1).mpr
      ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, by
        change (n : ℤ) • x.1 = 0
        have hkill : n • (x : G) = 0 := x.2
        simpa only [Nat.cast_smul_eq_nsmul] using hkill⟩⟩
  exact Finite.of_injective f (fun _ _ h ↦ Subtype.ext (congrArg (fun a : T ↦ (a : G)) h))

/-- For a finitely generated abelian group, the order of the multiplication-by-`n`
cokernel is `n` to the power of the rank times the order of the kernel. -/
theorem card_quotient_range_nsmul {n : ℕ} (hn : n ≠ 0) :
    Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) n).range) =
      n ^ finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  let T := Submodule.torsion ℤ G
  let Q := G ⧸ T
  let : Finite T := Module.finite_of_fg_torsion T Submodule.torsion_isTorsion
  let : Module.IsTorsionFree ℤ Q := Submodule.QuotientTorsion.instIsTorsionFree
  have hQ : finrank ℤ Q = finrank ℤ G := finrank_quotient_eq_of_le_torsion le_rfl
  -- The torsion-free quotient is free over ℤ, so the quotient map splits.
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property T.mkQ (LinearMap.id : Q →ₗ[ℤ] Q) T.mkQ_surjective
  let e : G ≃+ Q × T :=
    ((lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hs).symm.trans
      (LinearEquiv.prodComm ℤ T Q)).toAddEquiv
  let q := nsmulAddMonoidHom (α := Q) n
  let t := nsmulAddMonoidHom (α := T) n
  have hprod : nsmulAddMonoidHom (α := Q × T) n = q.prodMap t := by
    ext x <;> rfl
  have hq : q.ker = ⊥ :=
    q.ker_eq_bot (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  have hker : Nat.card (nsmulAddMonoidHom (α := G) n).ker = Nat.card t.ker := by
    calc
      _ = Nat.card (nsmulAddMonoidHom (α := Q × T) n).ker :=
        Nat.card_congr (nsmulKerCongr e n)
      _ = Nat.card t.ker := by
        rw [hprod, AddMonoidHom.ker_prodMap,
          Nat.card_congr (q.ker.prodEquiv t.ker).toEquiv, Nat.card_prod,
          hq, AddSubgroup.card_bot, one_mul]
  have hindex :
      (nsmulAddMonoidHom (α := G) n).range.index =
        (nsmulAddMonoidHom (α := Q × T) n).range.index := by
    rw [← AddEquiv.map_range_nsmulAddMonoidHom e, AddSubgroup.index_map_equiv]
  rw [← AddSubgroup.index_eq_card, hindex, hprod, AddMonoidHom.range_prodMap,
    AddSubgroup.index_prod, AddSubgroup.index_range (f := t), hker]
  exact congrArg (· * Nat.card t.ker) ((AddSubgroup.index_range_nsmul Q n).trans (by rw [hQ]))

/-- The cokernel of multiplication by a nonzero natural number is finite. -/
theorem finite_quotient_range_nsmul {n : ℕ} (hn : n ≠ 0) :
    Finite (G ⧸ (nsmulAddMonoidHom (α := G) n).range) := by
  let : Finite (nsmulAddMonoidHom (α := G) n).ker := finite_ker_nsmul hn
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient_range_nsmul hn]
  exact mul_ne_zero (pow_ne_zero _ hn) Nat.card_pos.ne'

/-- An injection from the multiplication-by-n quotient into a sufficiently small
finite type bounds the rank. The number `t` bounds the kernel cardinality from below
and can be certified by exhibiting distinct torsion points. -/
theorem finrank_le_of_descent {S : Type*} [Finite S] {n r t : ℕ} (hn : 1 < n)
    (e : (G ⧸ (nsmulAddMonoidHom (α := G) n).range) ↪ S)
    (ht : t ≤ Nat.card (nsmulAddMonoidHom (α := G) n).ker)
    (hS : Nat.card S < n ^ (r + 1) * t) :
    finrank ℤ G ≤ r := by
  by_contra! h
  have hcard := Nat.card_le_card_of_injective e e.injective
  rw [card_quotient_range_nsmul (Nat.zero_lt_of_lt hn).ne'] at hcard
  have hpow : n ^ (r + 1) ≤ n ^ finrank ℤ G :=
    pow_right_mono₀ hn.le (Nat.succ_le_of_lt h)
  exact hS.not_ge ((Nat.mul_le_mul hpow ht).trans hcard)

/-- A descent rank certificate from a Kummer-type injection, a finite cardinality
bound, and `r` linearly independent points. -/
theorem finrank_eq_of_descent {S : Type*} [Finite S] {n r t : ℕ} (hn : 1 < n)
    (e : (G ⧸ (nsmulAddMonoidHom (α := G) n).range) ↪ S)
    (ht : t ≤ Nat.card (nsmulAddMonoidHom (α := G) n).ker)
    (hS : Nat.card S < n ^ (r + 1) * t)
    (P : Fin r → G) (hP : LinearIndependent ℤ P) :
    finrank ℤ G = r :=
  le_antisymm (finrank_le_of_descent hn e ht hS)
    (by simpa using hP.fintype_card_le_finrank)

end BSD
