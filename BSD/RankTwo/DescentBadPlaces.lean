import BSD.RankTwo.DescentUpperModel
import EllipticCurves.SelmerGroup

/-! Refined finite bad places in Stoll's 2-descent for the completed-square model of 389.a1. -/

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain NumberField

namespace BSD.RankTwo389
noncomputable section
/-- Finite rational places over two, viewed as prime ideals of the ring of integers. -/
def dyadicPlaces389 : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | (2 : 𝓞 ℚ) ∈ v.asIdeal}

private theorem squarefree_389 : Squarefree (389 : 𝓞 ℚ) := by
  have hz : Squarefree (389 : ℤ) := Int.squarefree_natAbs.mp
    (by exact (by norm_num : Nat.Prime 389).squarefree)
  simpa only [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, map_ofNat] using
    hz.map (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).toMulEquiv

private theorem valuation_two_eq_one {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ dyadicPlaces389) : v.valuation ℚ 2 = 1 := by
  rw [← map_ofNat (algebraMap (𝓞 ℚ) ℚ) 2]
  exact v.valuation_eq_one_iff_notMem.mpr hv

/-- At every odd place even the prime 389 divides the polynomial discriminant at most once. -/
theorem shortCurve_odd_discr_bound (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v ∉ dyadicPlaces389) :
    WithZero.exp (-1 : ℤ) ≤ v.valuation ℚ shortCurve.toAffine.f.discr := by
  have hn := v.exp_neg_one_le_valuation_algebraMap (K := ℚ) (v.notMem_pow_two_of_squarefree squarefree_389)
  rw [shortCurve_cubic_discr, show (16:ℚ) = 2^4 by norm_num, map_div₀, map_pow,
    valuation_two_eq_one hv, one_pow, div_one]
  simpa only [map_ofNat] using hn

/-- The tame prime 389 is absent from the refined set and every odd place is admissible. -/
theorem shortCurve_discBadPrimes_subset_dyadic : shortCurve.toAffine.discBadPrimes (𝓞 ℚ) ⊆ dyadicPlaces389 := by
  intro v hv
  by_contra h2
  have h := valuation_two_eq_one h2
  rcases hv with (((hbad | hbad) | hbad) | hbad)
  · exact hbad (shortCurve_odd_discr_bound v h2)
  · change 1 < v.valuation ℚ 1 at hbad
    simp at hbad
  · change 1 < v.valuation ℚ (-2) at hbad
    simp [h] at hbad
  · change 1 < v.valuation ℚ (1/4) at hbad
    rw [show (4:ℚ) = 2^2 by norm_num, map_div₀, map_pow, h, map_one, one_pow, div_one] at hbad
    exact lt_irrefl _ hbad

/-- The denominator of the constant term has a pole at every dyadic place. -/
theorem shortCurve_discBadPrimes_eq_dyadic : shortCurve.toAffine.discBadPrimes (𝓞 ℚ) = dyadicPlaces389 := by
  refine Set.Subset.antisymm shortCurve_discBadPrimes_subset_dyadic ?_
  intro v hv
  apply Or.inr
  change 1 < v.valuation ℚ (1/4)
  have hne : v.valuation ℚ 2 ≠ 1 := by
    rw [← map_ofNat (algebraMap (𝓞 ℚ) ℚ) 2]
    exact fun h ↦ v.valuation_eq_one_iff_notMem.mp h hv
  have hle : v.valuation ℚ 2 ≤ 1 := by
    simpa only [map_ofNat] using v.valuation_le_one (K := ℚ) (2 : 𝓞 ℚ)
  have hpos : 0 < v.valuation ℚ 2 := (v.valuation ℚ).pos_iff.mpr (by norm_num)
  rw [show (4:ℚ) = 2^2 by norm_num, map_div₀, map_pow, map_one, one_div,
    one_lt_inv₀ (pow_pos hpos _)]
  exact pow_lt_one₀ hpos.le (hle.lt_of_ne hne) (by decide)

/-- The bad places for the finite local conditions are precisely the dyadic places. -/
theorem shortCurve_badPrimes₂_eq_dyadic : shortCurve.toAffine.badPrimes₂ (𝓞 ℚ) = dyadicPlaces389 := by
  rw [badPrimes₂, shortCurve_discBadPrimes_eq_dyadic]
  exact Set.union_eq_left.mpr fun v hv ↦ by
    by_contra hn
    exact hv (valuation_two_eq_one hn)

open scoped Classical in
/-- The full 2-Selmer group lies in the classes unramified away from two with trivial norm. -/
theorem shortCurve_selmer_le_dyadic_inf_ker :
    shortCurve.toAffine.selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion) ≤
      shortCurve.toAffine.selmerGroupA (𝓞 ℚ) dyadicPlaces389 ⊓ shortCurve.toAffine.normM.ker := by
  rw [← shortCurve_discBadPrimes_eq_dyadic]
  exact shortCurve.toAffine.selmerGroup₂_le_selmerGroupA_inf_ker

open scoped Classical in
/-- The same containment for the actual image of the rational descent map. -/
theorem shortCurve_range_mu_le_dyadic_inf_ker :
    (μ (W := shortCurve.toAffine)).range ≤
      shortCurve.toAffine.selmerGroupA (𝓞 ℚ) dyadicPlaces389 ⊓ shortCurve.toAffine.normM.ker :=
  (shortCurve.toAffine.range_μ_le_selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion)).trans
    shortCurve_selmer_le_dyadic_inf_ker

end
end BSD.RankTwo389
