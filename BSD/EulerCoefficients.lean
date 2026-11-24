import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Coefficients of the Euler product over the rationals

For a product of factors supported on distinct primes, the coefficient at a
prime power comes from the corresponding single factor. This applies to the
formal Hasse–Weil L-function over `ℚ`.
-/

open Filter

namespace BSD

open ArithmeticFunction

/-- In an Euler product indexed by distinct primes, the coefficient at a
power of one prime is given by the corresponding local power series. -/
theorem eulerProduct_ofPowerSeries_apply_prime_pow {ι R : Type*} [CommSemiring R]
    (q : ι → ℕ) (hq : Function.Injective q) (hprime : ∀ i, (q i).Prime)
    (f : ι → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 1) (i : ι) (k : ℕ) :
    eulerProduct (fun j => ofPowerSeries (q j) (f j)) (q i ^ k) = (f i).coeff k := by
  classical
  let F (j : ι) : ArithmeticFunction R := ofPowerSeries (q j) (f j)
  have hlocal (j : ι) (hji : j ≠ i) {n : ℕ} (hn : n ∣ q i ^ k) :
      F j n = (1 : ArithmeticFunction R) n := by
    by_cases h : n = 1
    · simp [h, F, hf]
    have hnot : ¬∃ a, q j ^ a = n := by
      rintro ⟨a, rfl⟩
      have ha : a ≠ 0 := fun ha => h (by simp [ha])
      have hd : q j ∣ q i ^ k := (dvd_pow_self (q j) ha).trans hn
      exact hji (hq ((Nat.prime_dvd_prime_iff_eq (hprime j) (hprime i)).mp
        ((hprime j).dvd_of_dvd_pow hd)))
    change ofPowerSeries (q j) (f j) n = _
    rw [ofPowerSeries_apply (hprime j).one_lt, Function.extend_apply' _ _ _ hnot,
      Pi.zero_apply, one_apply_ne h]
  have hprod (s : Finset ι) (hi : i ∉ s) {n : ℕ} (hn : n ∣ q i ^ k) :
      (∏ j ∈ s, F j) n = (1 : ArithmeticFunction R) n := by
    induction s using Finset.induction_on generalizing n with
    | empty => simp
    | insert j s hjs ih =>
      have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j s)
      have his : i ∉ s := fun hs => hi (Finset.mem_insert_of_mem hs)
      rw [Finset.prod_insert hjs, ← one_mul (1 : ArithmeticFunction R), mul_apply, mul_apply]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hlocal j hji ((Nat.dvd_of_mem_divisors
        (Nat.fst_mem_divisors_of_mem_antidiagonal ha)).trans hn),
        ih his ((Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal ha)).trans hn)]
  have hfinite (s : Finset ι) (hi : i ∈ s) :
      (∏ j ∈ s, F j) (q i ^ k) = (f i).coeff k := by
    rw [← Finset.mul_prod_erase s F hi, ← ofPowerSeries_apply_pow (hprime i).one_lt (f i) k]
    change (F i * ∏ j ∈ s.erase i, F j) (q i ^ k) = F i (q i ^ k)
    calc
      _ = (F i * 1) (q i ^ k) := by
        rw [mul_apply, mul_apply]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [hprod (s.erase i) (Finset.notMem_erase i s)
          (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal ha))]
      _ = _ := by rw [mul_one]
  have : Northcott q := ⟨fun b => (Set.finite_Iic b).preimage hq.injOn⟩
  have hlimit := tendsTo_eulerProduct_ofPowerSeries q f hf (q i ^ k)
  have hevent : ∀ᶠ s : Finset ι in atTop, (∏ j ∈ s, F j) (q i ^ k) = (f i).coeff k :=
    eventually_atTop.2 ⟨{i}, fun s hs => hfinite s (hs (Finset.mem_singleton_self i))⟩
  obtain ⟨s, hs, hfs⟩ := (hlimit.and hevent).exists
  exact hs.symm.trans hfs

open NumberField WeierstrassCurve IsDedekindDomain IsLocalRing

private noncomputable abbrev rationalPrime (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  Rat.HeightOneSpectrum.primesEquiv v

private lemma rationalPrime_injective : Function.Injective rationalPrime :=
  Subtype.coe_injective.comp Rat.HeightOneSpectrum.primesEquiv.injective

private lemma rationalPrime_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (rationalPrime v).Prime :=
  (Rat.HeightOneSpectrum.primesEquiv v).2

private lemma rationalPlace_residueField_card (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = rationalPrime v := by
  have : Fact (rationalPrime v).Prime := ⟨rationalPrime_prime v⟩
  let e : ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (rationalPrime v) :=
    (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)

private lemma rationalPlace_localPowerSeries_constantCoeff_one
    (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
      (v.adicCompletionIntegers ℚ)).constantCoeff = 1 := by
  rw [localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  simp

/-- The formal Hasse–Weil coefficients over the rationals are multiplicative. -/
theorem weierstrass_LFunction_isMultiplicative (E : WeierstrassCurve ℚ) :
    E.LFunction.IsMultiplicative := by
  unfold WeierstrassCurve.LFunction
  apply isMultiplicative_eulerProduct
  intro v
  unfold localEulerFactor
  rw [rationalPlace_residueField_card]
  exact isMultiplicative_ofPowerSeries_of_isPrimePow _ (rationalPrime_prime v).prime.isPrimePow _
    (rationalPlace_localPowerSeries_constantCoeff_one E v)

/-- The Hasse–Weil coefficient at `p ^ k` is the coefficient of degree `k` in
the reciprocal of Mathlib's local polynomial at the finite place above `p`. -/
theorem weierstrass_LFunction_apply_prime_pow (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    E.LFunction ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ k) =
      ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
        (v.adicCompletionIntegers ℚ)).coeff k := by
  unfold WeierstrassCurve.LFunction localEulerFactor
  simp only [rationalPlace_residueField_card]
  exact eulerProduct_ofPowerSeries_apply_prime_pow rationalPrime rationalPrime_injective
    rationalPrime_prime _ (rationalPlace_localPowerSeries_constantCoeff_one E) v k

/-- A multiplicative arithmetic function agrees with the Hasse–Weil coefficients
if and only if it agrees with the coefficients at every finite place. -/
theorem weierstrass_LFunction_eq_iff_local_coefficients (E : WeierstrassCurve ℚ)
    (f : ArithmeticFunction ℤ) (hf : f.IsMultiplicative) :
    f = E.LFunction ↔ ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ),
      f ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ k) =
        ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
          (v.adicCompletionIntegers ℚ)).coeff k := by
  constructor
  · intro h v k
    rw [h, weierstrass_LFunction_apply_prime_pow]
  · intro h
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f hf E.LFunction
      (weierstrass_LFunction_isMultiplicative E)).2 ?_
    intro p k hp
    let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
    let v := e.symm ⟨p, hp⟩
    have hpv : rationalPrime v = p := congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)
    rw [← hpv, weierstrass_LFunction_apply_prime_pow]
    exact h v k

end BSD
