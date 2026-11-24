import BSD.CoefficientsSplit
import BSD.GoodTwo
import BSD.GoodReduction
import BSD.Ramified

/-! # The actual local polynomials at split primes of the Fermat cubic -/

namespace BSD.FermatCubic

open NumberField Polynomial

/-- A primary Eisenstein integer of norm p determines the denominator in the
Hasse–Weil Euler product at the corresponding rational split prime. -/
theorem split_localPolynomial_of_primary (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hs : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) % 3 = 1) {a b : ℤ}
    (hn : a ^ 2 - a * b + b ^ 2 = (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
    (ha : 3 ∣ a - 1) (hb : 3 ∣ b) :
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - C (2 * a - b) * X + C ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) * X ^ 2 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have h5 : 5 ≤ (p : ℕ) := by
    have hprime := p.2
    have hmod : (p : ℕ) % 3 = 1 := hs
    have hne4 : (p : ℕ) ≠ 4 := by rintro he; rw [he] at hprime; norm_num at hprime
    have := hprime.two_le
    omega
  have htrace := split_trace_of_primary (p := (p : ℕ)) hs hn ha hb
  change ((mordellModel (-(432 : ℚ))).baseChange _).localPolynomial _ = _
  rw [fermatCubic_good_localPolynomial_rat v h5]
  change 1 - C ((p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point) * X + _ = _
  rw [htrace]

/-- Trace of a primary Eisenstein integer of norm p, for split primes.
The fallback fixes a value outside the domain where a representation exists. -/
noncomputable def primaryTrace (p : ℕ) : ℤ := by
  classical
  exact if h : ∃ a b : ℤ, 3 ∣ a - 1 ∧ 3 ∣ b ∧ a ^ 2 - a * b + b ^ 2 = p then
    2 * h.choose - h.choose_spec.choose else 0

theorem primaryTrace_eq {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hn : a ^ 2 - a * b + b ^ 2 = p) (ha : 3 ∣ a - 1) (hb : 3 ∣ b) :
    primaryTrace p = 2 * a - b := by
  classical
  have h : ∃ x y : ℤ, 3 ∣ x - 1 ∧ 3 ∣ y ∧ x ^ 2 - x * y + y ^ 2 = p :=
    ⟨a, b, ha, hb, hn⟩
  rw [primaryTrace, dif_pos h]
  obtain ⟨hx, hy, hnorm⟩ := h.choose_spec.choose_spec
  exact BSD.eisenstein_primary_trace_eq hp hnorm hn hx hy ha hb

/-- An arithmetic description of each Euler denominator, independent of
elliptic point counts and of any modularity or BSD hypothesis. -/
noncomputable def eulerDenominator (p : ℕ) : ℤ[X] :=
  if p = 3 then 1
  else if p % 3 = 2 then 1 + C (p : ℤ) * X ^ 2
  else 1 - C (primaryTrace p) * X + C (p : ℤ) * X ^ 2

/-- All finite places of the curve over ℚ, including 2 and 3. -/
theorem localPolynomial_eq_eulerDenominator (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    (curve.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      eulerDenominator (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have hp : (p : ℕ).Prime := p.2
  have : Fact (p : ℕ).Prime := ⟨hp⟩
  change ((mordellModel (-(432 : ℚ))).baseChange _).localPolynomial _ = eulerDenominator (p : ℕ)
  by_cases h3 : (p : ℕ) = 3
  · simpa only [eulerDenominator, if_pos h3] using fermatCubic_localPolynomial_three_rat v h3
  by_cases h2 : (p : ℕ) = 2
  · simpa [eulerDenominator, h2] using fermatCubic_localPolynomial_two_rat v h2
  have hne4 : (p : ℕ) ≠ 4 := by rintro he; rw [he] at hp; norm_num at hp
  have hge : 5 ≤ (p : ℕ) := by have := hp.two_le; omega
  by_cases hi : (p : ℕ) % 3 = 2
  · simpa only [eulerDenominator, if_neg h3, if_pos hi] using
      fermatCubic_localPolynomial_rat v hge hi
  have hnd : ¬ 3 ∣ (p : ℕ) := by
    intro hd
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · norm_num at h
    · exact h3 h.symm
  have hs : (p : ℕ) % 3 = 1 := by omega
  obtain ⟨a,b,ha,hb,hn,_⟩ := split_trace_primary_representation (p := (p : ℕ)) hs
  change (curve.baseChange _).localPolynomial _ = _
  simpa only [eulerDenominator, if_neg h3, if_neg hi, primaryTrace_eq hp hn ha hb] using
    split_localPolynomial_of_primary v hs hn ha hb

end BSD.FermatCubic
