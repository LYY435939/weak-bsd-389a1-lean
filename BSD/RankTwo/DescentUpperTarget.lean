import EllipticCurves.Mathlib.SelmerGroup
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open IsDedekindDomain

open scoped NumberField

namespace BSD.RankTwo389

variable {K : Type*} [Field K] [NumberField K]

private theorem integralUnit_squareClass_of_even_valuations
    [IsPrincipalIdealRing (𝓞 K)] (u : Kˣ)
    (hu : ∀ w : HeightOneSpectrum (𝓞 K), (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u)) :
    ∃ v : (𝓞 K)ˣ, (QuotientGroup.mk u : Units.modPow K 2) =
      QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K) v) := by
  let S : Set (HeightOneSpectrum (𝓞 K)) := ∅
  have hcnum : NumberField.classNumber K = 1 :=
    NumberField.classNumber_eq_one_iff.mpr inferInstance
  let : Subsingleton (ClassGroup (𝓞 K)) := Fintype.card_le_one_iff_subsingleton.mp hcnum.le
  let c : selmerGroup (K := K) (S := S) (n := 2) := ⟨QuotientGroup.mk u, by
    intro w _
    exact (w.valuationOfNeZeroMod_mk_eq_one_iff 2 u).mpr (hu w)⟩
  obtain ⟨s, hs⟩ := sUnitToSelmer_surjective K S 2 c
  let e := unitsEquivEmptyUnit (𝓞 K) K
  obtain ⟨v, hv⟩ := e.surjective s
  refine ⟨v, ?_⟩
  have h := congrArg Subtype.val hs.symm
  change (QuotientGroup.mk u : Units.modPow K 2) = QuotientGroup.mk (s : Kˣ) at h
  rw [← hv, coe_unitsEquivEmptyUnit] at h
  exact h

/-- If all finite valuations are even and the integer ring is principal, the element is
an integral unit times a square in its fraction field. -/
theorem exists_integralUnit_mul_sq_of_even_valuations
    [IsPrincipalIdealRing (𝓞 K)] (u : Kˣ)
    (hu : ∀ w : HeightOneSpectrum (𝓞 K), (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u)) :
    ∃ (v : (𝓞 K)ˣ) (z : Kˣ), u = Units.map (algebraMap (𝓞 K) K) v * z ^ 2 := by
  obtain ⟨v, hv⟩ := integralUnit_squareClass_of_even_valuations u hu
  obtain ⟨z, hz⟩ := QuotientGroup.eq_iff_div_mem.mp hv
  exact ⟨v, z, div_eq_iff_eq_mul'.mp hz.symm⟩

private theorem intNorm_eq_one_of_unit_mul_sq
    {u z : Kˣ} {v : (𝓞 K)ˣ}
    (h : u = Units.map (algebraMap (𝓞 K) K) v * z ^ 2)
    (hnorm : IsSquare (Algebra.norm ℚ (u : K))) :
    Algebra.norm ℤ (v : 𝓞 K) = 1 := by
  have hpos : 0 < Algebra.norm ℚ (u : K) := by
    obtain ⟨a, ha⟩ := hnorm
    have hn₀ : Algebra.norm ℚ (u : K) ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr u.ne_zero
    have ha₀ : a ≠ 0 := by
      intro ha₀
      exact hn₀ (by rw [ha, ha₀, mul_zero])
    rw [ha]
    exact mul_self_pos.mpr ha₀
  have hunit : IsUnit (Algebra.norm ℤ (v : 𝓞 K)) :=
    v.isUnit.map (Algebra.norm ℤ)
  rcases Int.isUnit_iff.mp hunit with hp | hm
  · exact hp
  · have heq := congrArg (fun x : Kˣ ↦ Algebra.norm ℚ (x : K)) h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, map_pow,
      map_mul] at heq
    change Algebra.norm ℚ (u : K) = Algebra.norm ℚ ((v : 𝓞 K) : K) *
      (Algebra.norm ℚ (z : K)) ^ 2 at heq
    rw [← Algebra.coe_norm_int, hm, Int.cast_neg, Int.cast_one] at heq
    rw [heq] at hpos
    nlinarith only [hpos, sq_nonneg (Algebra.norm ℚ (z : K))]

/-- A square norm forces the integral unit in the factorization to have norm one. -/
theorem exists_normOneIntegralUnit_mul_sq
    [IsPrincipalIdealRing (𝓞 K)] (u : Kˣ)
    (hu : ∀ w : HeightOneSpectrum (𝓞 K), (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u))
    (hnorm : IsSquare (Algebra.norm ℚ (u : K))) :
    ∃ (v : (𝓞 K)ˣ) (z : Kˣ), Algebra.norm ℤ (v : 𝓞 K) = 1 ∧
      u = Units.map (algebraMap (𝓞 K) K) v * z ^ 2 := by
  obtain ⟨v, z, h⟩ := exists_integralUnit_mul_sq_of_even_valuations u hu
  exact ⟨v, z, intNorm_eq_one_of_unit_mul_sq h hnorm, h⟩

/-- An everywhere-even square class with square norm has a norm-one integral representative. -/
theorem exists_normOneIntegralUnit_squareClass
    [IsPrincipalIdealRing (𝓞 K)] (u : Kˣ)
    (hu : ∀ w : HeightOneSpectrum (𝓞 K), (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u))
    (hnorm : IsSquare (Algebra.norm ℚ (u : K))) :
    ∃ v : (𝓞 K)ˣ, Algebra.norm ℤ (v : 𝓞 K) = 1 ∧
      (QuotientGroup.mk u : Units.modPow K 2) =
        QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K) v) := by
  obtain ⟨v, z, hn, h⟩ := exists_normOneIntegralUnit_mul_sq u hu hnorm
  have hz : (QuotientGroup.mk (z ^ 2) : Units.modPow K 2) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
  refine ⟨v, hn, ?_⟩
  rw [h, QuotientGroup.mk_mul, hz, mul_one]

/-- An even valuation away from the exceptional set and at each exceptional prime gives the
empty-set norm-one unit conclusion. -/
theorem exists_normOneIntegralUnit_squareClass_of_even_on_compl_and_on
    [IsPrincipalIdealRing (𝓞 K)] (u : Kˣ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hAway : ∀ w ∉ S, (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u))
    (hAt : ∀ w ∈ S, (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u))
    (hnorm : IsSquare (Algebra.norm ℚ (u : K))) :
    ∃ v : (𝓞 K)ˣ, Algebra.norm ℤ (v : 𝓞 K) = 1 ∧
      (QuotientGroup.mk u : Units.modPow K 2) =
        QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K) v) :=
  exists_normOneIntegralUnit_squareClass u
    (fun w ↦ by by_cases h : w ∈ S; exact hAt w h; exact hAway w h) hnorm

/-- A class in the empty-set Selmer group that is killed by the norm map comes from
a norm-one unit of the ring of integers. -/
theorem exists_normOneIntegralUnit_of_mem_emptySelmer
    [IsPrincipalIdealRing (𝓞 K)] (c : Units.modPow K 2)
    (hc : c ∈ selmerGroup (K := K) (S := (∅ : Set (HeightOneSpectrum (𝓞 K)))) (n := 2))
    (hnorm : Units.modPow.map (Algebra.norm ℚ) 2 c = 1) :
    ∃ v : (𝓞 K)ˣ, Algebra.norm ℤ (v : 𝓞 K) = 1 ∧
      c = QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K) v) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  have hval (w : HeightOneSpectrum (𝓞 K)) :
      (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) :=
    (w.valuationOfNeZeroMod_mk_eq_one_iff 2 u).mp (hc w (Set.notMem_empty w))
  rw [Units.modPow.map_mk, Units.modPow.mk_eq_one_iff_isSquare] at hnorm
  exact exists_normOneIntegralUnit_squareClass u hval hnorm

end BSD.RankTwo389
