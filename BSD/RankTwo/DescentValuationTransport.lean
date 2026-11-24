import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-! Transport of normalized height-one valuations along compatible ring and fraction-field equivalences. -/

namespace BSD.RankTwo389

open IsDedekindDomain
open scoped WithZero

variable {R S K L : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Field K] [Field L] [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]

/-- The normalized integral valuations at corresponding height-one primes agree. -/
theorem intValuation_ringEquiv (eR : R ≃+* S) (w : HeightOneSpectrum S) (r : R) :
    w.intValuation (eR r) = ((HeightOneSpectrum.equivOfRingEquiv eR).symm w).intValuation r := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  let v := (HeightOneSpectrum.equivOfRingEquiv eR).symm w
  have hv : v.asIdeal.map (eR : R →+* S) = w.asIdeal :=
    Ideal.map_comap_eq_self_of_equiv eR w.asIdeal
  have hmul : multiplicity w.asIdeal (Ideal.span {eR r}) =
      multiplicity v.asIdeal (Ideal.span {r}) := by
    apply multiplicity_eq_of_emultiplicity_eq
    apply emultiplicity_eq_emultiplicity_iff.mpr
    intro n
    rw [Ideal.dvd_span_singleton, Ideal.dvd_span_singleton, ← hv, ← Ideal.map_pow]
    exact Ideal.apply_mem_of_equiv_iff
  have hr' : eR r ≠ 0 := fun h ↦ hr (eR.injective (h.trans (map_zero eR).symm))
  rw [w.intValuation_eq_exp_neg_multiplicity hr',
    v.intValuation_eq_exp_neg_multiplicity hr, hmul]

/-- Compatible ring and fraction-field equivalences preserve normalized height-one valuations. -/
theorem valuation_ringEquiv (eR : R ≃+* S) (eK : K ≃+* L)
    (he : ∀ r : R, algebraMap S L (eR r) = eK (algebraMap R K r))
    (w : HeightOneSpectrum S) (x : K) :
    w.valuation L (eK x) = ((HeightOneSpectrum.equivOfRingEquiv eR).symm w).valuation K x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
  rw [map_div₀, ← he a, ← he b, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap, intValuation_ringEquiv eR]

/-- The induced maps on units preserve Mathlib's multiplicative valuations on nonzero elements. -/
theorem valuationOfNeZero_ringEquiv (eR : R ≃+* S) (eK : K ≃+* L)
    (he : ∀ r : R, algebraMap S L (eR r) = eK (algebraMap R K r))
    (w : HeightOneSpectrum S) (u : Kˣ) :
    w.valuationOfNeZero ((Units.mapEquiv eK.toMulEquiv) u) =
      ((HeightOneSpectrum.equivOfRingEquiv eR).symm w).valuationOfNeZero u := by
  apply WithZero.coe_inj.mp
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq,
    Units.coe_mapEquiv]
  exact valuation_ringEquiv eR eK he w (u : K)

end BSD.RankTwo389
