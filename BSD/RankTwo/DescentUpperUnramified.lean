import BSD.RankTwo.DescentUpperField
import BSD.RankTwo.DescentBadPlaces
import BSD.RankTwo.DescentValuationTransport

/-! Transport of Stoll's odd-place conditions to the concrete cubic number field. -/

namespace BSD.RankTwo389
open WeierstrassCurve NumberField IsDedekindDomain Polynomial
open scoped Classical

theorem odd_factor_parity (p : branchPolynomial.Factors)
    (a : shortCurve.toAffine.Aˣ)
    (ha : (QuotientGroup.mk a : shortCurve.toAffine.M) ∈ shortCurve.toAffine.selmerGroupA (𝓞 ℚ) dyadicPlaces389)
    (w : HeightOneSpectrum (𝓞 DescentField)) (hw : (2:𝓞 DescentField) ∉ w.asIdeal) :
    let v := Units.map (AdjoinRoot.projFactor shortCurve.toAffine.f_ne_zero
      shortCurve.toAffine.squarefree_f p).toMonoidHom a
    (2:ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.mapEquiv (branchFactorEquiv p).toMulEquiv v)) := by
  let v := Units.map (AdjoinRoot.projFactor shortCurve.toAffine.f_ne_zero
      shortCurve.toAffine.squarefree_f p).toMonoidHom a
  let eR := branchFactorIntegerEquiv p
  let w' := (HeightOneSpectrum.equivOfRingEquiv eR).symm w
  have hbad : w' ∉ HeightOneSpectrum.primesAbove (𝓞 ℚ)
      (shortCurve.toAffine.ringOfIntegersFactor (𝓞 ℚ) p) dyadicPlaces389 := by
    rw [HeightOneSpectrum.mem_primesAbove_iff]
    intro h
    apply hw
    change eR (algebraMap (𝓞 ℚ) _ 2) ∈ w.asIdeal at h
    simpa only [map_ofNat] using h
  have h := (shortCurve.toAffine.mem_selmerGroupA_unit_iff (𝓞 ℚ) dyadicPlaces389 a).mp ha p w' hbad
  have htransport := valuationOfNeZero_ringEquiv
    (R:=shortCurve.toAffine.ringOfIntegersFactor (𝓞 ℚ) p) (K:=AdjoinRoot (p:ℚ[X]))
    (S:=𝓞 DescentField) (L:=DescentField) eR (branchFactorEquiv p).toRingEquiv
    (coe_branchFactorIntegerEquiv p) w v
  change (2:ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
    (Units.mapEquiv (branchFactorEquiv p).toMulEquiv v))
  exact congrArg (fun t : Multiplicative ℤ => (2:ℤ) ∣ Multiplicative.toAdd t) htransport |>.mpr h

end BSD.RankTwo389
