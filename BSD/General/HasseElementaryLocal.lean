import BSD.General.HasseElementaryGeometry
import BSD.General.HasseLocal

/-! # An unconditional bound at prime powers -/

namespace BSD

open WeierstrassCurve IsDedekindDomain NumberField

private theorem reciprocal_quadratic_coeff_abs_le_pow {a p : ℤ}
    (hp : 2 ≤ p) (ha : |a| ≤ p) (k : ℕ) :
    |(PowerSeries.invOfUnit
      (1 + PowerSeries.C a * PowerSeries.X + PowerSeries.C p * PowerSeries.X ^ 2) 1).coeff k| ≤
      p ^ k := by
  let D : PowerSeries ℤ := 1 + PowerSeries.C a * PowerSeries.X +
    PowerSeries.C p * PowerSeries.X ^ 2
  let F := PowerSeries.invOfUnit D 1
  let t := -a
  have hp₀ : 0 ≤ p := by omega
  have ht : |t| ≤ p := by simpa only [t, abs_neg] using ha
  have hrec : F.coeff 1 = t ∧ ∀ j : ℕ,
      F.coeff (j + 2) = t * F.coeff (j + 1) - p * F.coeff j := by
    simpa only [D, F, t, map_neg, neg_mul, sub_neg_eq_add] using
      reciprocal_quadratic_coefficients t p
  have hzero : F.coeff 0 = 1 := by
    simp [F, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have htwo : F.coeff 2 = t ^ 2 - p := by
    simpa only [Nat.zero_add, hrec.1, hzero, mul_one, pow_two] using hrec.2 0
  have ht_sq : t ^ 2 ≤ p ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hquad : |t ^ 2 - p| ≤ p ^ 2 - p := by
    apply abs_le.mpr
    constructor
    · nlinarith only [sq_nonneg t, mul_nonneg hp₀ (show 0 ≤ p - 2 by omega)]
    · linarith only [ht_sq]
  have hlinear : |t * p| ≤ p ^ 2 := by
    rw [abs_mul, abs_of_nonneg hp₀, pow_two]
    exact mul_le_mul_of_nonneg_right ht hp₀
  -- Eliminating the middle term yields weights that sum to the next power of `p`.
  have hskip (j : ℕ) : F.coeff (j + 3) =
      (t ^ 2 - p) * F.coeff (j + 1) - (t * p) * F.coeff j := by
    change F.coeff ((j + 1) + 2) = _
    rw [hrec.2 (j + 1), hrec.2 j]
    ring
  have hbound (j : ℕ) : |F.coeff j| ≤ p ^ j ∧
      |F.coeff (j + 1)| ≤ p ^ (j + 1) ∧ |F.coeff (j + 2)| ≤ p ^ (j + 2) := by
    induction j with
    | zero =>
      refine ⟨by simp [hzero], ?_, ?_⟩
      · simpa only [Nat.zero_add, hrec.1, pow_one] using ht
      · simpa only [Nat.zero_add, htwo] using hquad.trans (sub_le_self (p ^ 2) hp₀)
    | succ j ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      change |F.coeff (j + 3)| ≤ p ^ (j + 3)
      calc
        |F.coeff (j + 3)| ≤ |(t ^ 2 - p) * F.coeff (j + 1)| + |(t * p) * F.coeff j| := by
          rw [hskip]
          simpa only [← sub_eq_add_neg, abs_neg] using
            abs_add_le ((t ^ 2 - p) * F.coeff (j + 1)) (-(t * p * F.coeff j))
        _ ≤ (p ^ 2 - p) * p ^ (j + 1) + p ^ 2 * p ^ j := by
          rw [abs_mul (t ^ 2 - p), abs_mul (t * p)]
          exact add_le_add
            (mul_le_mul hquad ih.2.1 (abs_nonneg _) ((abs_nonneg _).trans hquad))
            (mul_le_mul hlinear ih.1 (abs_nonneg _) (sq_nonneg p))
        _ = p ^ (j + 3) := by
          rw [show p ^ (j + 1) = p ^ j * p from pow_succ p j, pow_add p j 3]
          ring
  exact (hbound k).1

/-- For every rational Weierstrass curve, the absolute Hasse–Weil coefficient
at a prime power is bounded by the prime power itself. -/
theorem weierstrass_LFunction_abs_prime_pow_le_self (E : WeierstrassCurve ℚ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : |E.LFunction (p ^ k)| ≤ ((p ^ k : ℕ) : ℤ) := by
  classical
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let v := e.symm ⟨p, hp⟩
  let R := v.adicCompletionIntegers ℚ
  let W := E.baseChange (v.adicCompletion ℚ)
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)
  have hcoeff := weierstrass_LFunction_apply_prime_pow E v k
  rw [hv] at hcoeff
  rw [hcoeff]
  change |(W.localPowerSeries R).coeff k| ≤ _
  by_cases hg : (W.minimal R).HasGoodReduction R
  · obtain ⟨a, ha, hpoly⟩ := weierstrass_good_localPolynomial_abs_coeff_le E v hg
    change W.localPolynomial R = _ at hpoly
    rw [hv] at ha hpoly
    rw [localPowerSeries, hpoly, Nat.cast_pow]
    simpa only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X, Polynomial.coe_pow] using
      reciprocal_quadratic_coeff_abs_le_pow (by exact_mod_cast hp.two_le) ha k
  · have hbad : |(W.localPowerSeries R).coeff k| ≤ (1 : ℤ) := by
      exact_mod_cast weierstrass_localPowerSeries_abs_coeff_le_one_of_badReduction E v hg k
    have hk : 1 ≤ p ^ k := Nat.succ_le_of_lt (pow_pos hp.pos k)
    exact hbad.trans (by exact_mod_cast hk)

end BSD
