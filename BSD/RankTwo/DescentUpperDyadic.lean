import BSD.RankTwo.DescentUpperSelmer
import BSD.RankTwo.DescentUpperClass
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.NumberTheory.NumberField.Norm

noncomputable section
open scoped NumberField
open IsDedekindDomain
namespace BSD.RankTwo389

lemma descentRootIntegral_norm : Algebra.norm ℤ descentRootIntegral = -2 := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int]
  simpa using descentRoot_norm

/-- Any height-one place containing 2 is the root prime. -/
theorem dyadic_place_unique (v : HeightOneSpectrum (𝓞 DescentField))
    (hv : (2 : 𝓞 DescentField) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span ({descentRootIntegral} : Set (𝓞 DescentField)) := by
  apply TwoLocal.prime_over_two_unique_of_root_maximal descentRootIntegral
    descentRootIntegral_relation
  · exact (TwoLocal.root_ideal_maximal_of_absNorm_two _ descentRootIntegral_ideal_norm).1
  · exact v.isPrime
  · exact hv

lemma integral_map_ne_zero (x : 𝓞 DescentField) (hx : x ≠ 0) :
    algebraMap (𝓞 DescentField) DescentField x ≠ 0 := by
  intro h
  apply hx
  apply (FaithfulSMul.algebraMap_injective (𝓞 DescentField) DescentField)
  simpa using h

/-- At an integral element, the additive valuation has the sign convention
    used by `valuationOfNeZero`: it is minus the ideal multiplicity. -/
lemma valuation_integral_eq_neg_multiplicity
    (v : HeightOneSpectrum (𝓞 DescentField)) (x : 𝓞 DescentField) (hx : x ≠ 0) :
    Multiplicative.toAdd (v.valuationOfNeZero
      (Units.mk0 (algebraMap (𝓞 DescentField) DescentField x)
        (integral_map_ne_zero x hx))) =
      -(multiplicity v.asIdeal (Ideal.span ({x} : Set (𝓞 DescentField))) : ℤ) := by
  apply WithZero.exp_inj.mp
  change (v.valuationOfNeZero (Units.mk0 (algebraMap (𝓞 DescentField) DescentField x)
    (integral_map_ne_zero x hx)) : WithZero (Multiplicative ℤ)) = _
  rw [v.valuationOfNeZero_eq, Units.val_mk0, v.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity hx]

/-- Integral elements of square norm have even valuation at the dyadic place. -/
theorem dyadic_integral_square_norm_even (v : HeightOneSpectrum (𝓞 DescentField))
    (hv : (2 : 𝓞 DescentField) ∈ v.asIdeal) (x : 𝓞 DescentField) (hx : x ≠ 0)
    (hsq : IsSquare (Algebra.norm ℚ (algebraMap (𝓞 DescentField) DescentField x))) :
    (2 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero
      (Units.mk0 (algebraMap (𝓞 DescentField) DescentField x) (integral_map_ne_zero x hx))) := by
  have hsqi : IsSquare (Algebra.norm ℤ x) := Rat.isSquare_intCast_iff.mp (by
    rw [Algebra.coe_norm_int]
    exact hsq)
  obtain ⟨k,hk⟩ := hsqi
  have hsqn : IsSquare (Algebra.norm ℤ x).natAbs := by
    rw [hk, Int.natAbs_mul]
    exact ⟨k.natAbs, rfl⟩
  have heven := TwoLocal.root_multiplicity_even_of_element_norm_square descentRootIntegral
    descentRootIntegral_relation descentRootIntegral_norm x hx hsqn
  rw [valuation_integral_eq_neg_multiplicity v x hx, dyadic_place_unique v hv]
  obtain ⟨m,hm⟩ := heven
  rw [hm]
  exact ⟨-(m : ℤ), by push_cast; ring⟩

/-- The dyadic local condition for every nonzero element of the cubic field:
    square rational norm forces the `valuationOfNeZero` exponent to be even. -/
theorem dyadic_square_norm_even (v : HeightOneSpectrum (𝓞 DescentField))
    (hv : (2 : 𝓞 DescentField) ∈ v.asIdeal) (u : DescentFieldˣ)
    (hsq : IsSquare (Algebra.norm ℚ (u : DescentField))) :
    (2 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective (𝓞 DescentField) (u : DescentField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at hab
    exact u.ne_zero hab.symm
  let B : DescentFieldˣ := Units.mk0 (algebraMap (𝓞 DescentField) DescentField b)
    (integral_map_ne_zero b hb0)
  have hab0 : a*b ≠ 0 := mul_ne_zero ha0 hb0
  let AB : DescentFieldˣ := Units.mk0 (algebraMap (𝓞 DescentField) DescentField (a*b))
    (integral_map_ne_zero (a*b) hab0)
  have hunit : AB = u * B^2 := by
    apply Units.ext
    simp only [AB, B, Units.val_mk0, Units.val_mul, Units.val_pow_eq_pow_val, map_mul]
    rw [← hab]
    field_simp
  have heval : Algebra.norm ℚ (algebraMap (𝓞 DescentField) DescentField (a*b)) =
      Algebra.norm ℚ (u : DescentField) *
        (Algebra.norm ℚ (algebraMap (𝓞 DescentField) DescentField b))^2 := by
    have hv := congrArg (fun z : DescentFieldˣ => Algebra.norm ℚ (z : DescentField)) hunit
    simpa only [AB, B, Units.val_mk0, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow] using hv
  have hsqab : IsSquare (Algebra.norm ℚ (algebraMap (𝓞 DescentField) DescentField (a*b))) := by
    rw [heval]
    exact hsq.mul ⟨_, by ring⟩
  have hval := dyadic_integral_square_norm_even v hv (a*b) hab0 hsqab
  change (2 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero AB) at hval
  rw [hunit, map_mul, map_pow] at hval
  simp only [toAdd_mul, Int.toAdd_pow] at hval
  obtain ⟨k,hk⟩ := hval
  refine ⟨k - Multiplicative.toAdd (v.valuationOfNeZero B), ?_⟩
  omega

end BSD.RankTwo389
