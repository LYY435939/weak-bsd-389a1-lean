import BSD.General.ModularDataCoefficients
import BSD.General.ModularContinuation
import BSD.General.ModularDataSupport
import BSD.General.ModularLocalComplex

/-! Conditional modular continuation from the actual integral-model point counts. -/

namespace BSD.General

noncomputable def integralModelTrace (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- If the normalized modular coefficients have the actual good-prime traces,
then the Hasse–Weil series admits a meromorphic continuation. -/
theorem continues_of_integral_modular_model_off
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : ModularCoefficientData f)
    (htrace : ∀ (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ W.Δ → ¬ p ∣ N →
      cuspCoefficients f p = (integralModelTrace W p : ℂ))
    (E : WeierstrassCurve ℚ) (R : Finset ℕ)
    (hinverse : ∀ (p : ℕ), p.Prime → 5 ≤ p → ¬ (p : ℤ) ∣ W.Δ → p ∉ R →
      PowerSeries.mk (fun k : ℕ => (E.LFunction (p ^ k) : ℂ)) *
        quadraticEulerPolynomial (integralModelTrace W p : ℂ) (p : ℂ) = 1) :
    ∃ F : ℂ → ℂ, BSD.Continues E F := by
  classical
  let S := BSD.modularExceptionalPrimes W N ∪ R.filter Nat.Prime
  have hN : N ≠ 0 := NeZero.ne N
  have hlocal : ∀ p : ℕ, ∃ a b : ℂ, p ∈ S →
      PowerSeries.mk (fun k : ℕ => (E.LFunction (p ^ k) : ℂ)) *
        quadraticEulerPolynomial a b = 1 := by
    intro p
    by_cases hp : p ∈ S
    · have hprime : p.Prime := by
        rcases Finset.mem_union.mp hp with hc | hr
        · exact BSD.prime_of_mem_modularExceptionalPrimes W N p hc
        · exact (Finset.mem_filter.mp hr).2
      obtain ⟨t, d, _, ht⟩ := BSD.weierstrass_LFunction_exists_quadratic E hprime
      exact ⟨t, d, fun _ => by simpa only [quadraticEulerPolynomial] using ht⟩
    · exact ⟨0, 0, fun h => (hp h).elim⟩
  choose a₁ a₂ ha using hlocal
  let b₁ : ℕ → ℂ := fun p => cuspCoefficients f p
  let b₂ : ℕ → ℂ := fun p => if p ∣ N then 0 else (p : ℂ)
  refine ⟨quadraticCorrectedModularL f S a₁ a₂ b₁ b₂, ?_⟩
  apply continues_quadraticCorrectedModularL E f hf.isMultiplicative S a₁ a₂ b₁ b₂
  · intro p hp
    rcases Finset.mem_union.mp hp with hc | hr
    · exact BSD.prime_of_mem_modularExceptionalPrimes W N p hc
    · exact (Finset.mem_filter.mp hr).2
  · intro p hp hpS k
    have hc : p ∉ BSD.modularExceptionalPrimes W N := by
      intro h; exact hpS (Finset.mem_union_left _ h)
    have hr : p ∉ R := by
      intro h; exact hpS (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, hp⟩))
    have hp5 := BSD.five_le_of_not_mem_modularExceptionalPrimes W N p hN hΔ hp hc
    have hdisc := BSD.not_dvd_discriminant_of_not_mem_modularExceptionalPrimes W N p hN hΔ hp hc
    have hpN := BSD.not_dvd_level_of_not_mem_modularExceptionalPrimes W N p hN hΔ hp hc
    let A : PowerSeries ℂ := PowerSeries.mk (fun k : ℕ => (E.LFunction (p ^ k) : ℂ))
    let B : PowerSeries ℂ := PowerSeries.mk (fun k : ℕ => cuspCoefficients f (p ^ k))
    let P : PowerSeries ℂ := quadraticEulerPolynomial (cuspCoefficients f p) (p : ℂ)
    have hA : A * P = 1 := by
      have h := hinverse p hp hp5 hdisc hr
      simpa only [A, P, htrace p hp hdisc hpN] using h
    have hB : B * P = 1 := by
      simpa only [B, P] using hf.inverse_good hp hpN
    have hab : A = B := by
      calc
        A = A * 1 := by simp
        _ = A * (P * B) := by rw [mul_comm P B, hB]
        _ = (A * P) * B := by rw [mul_assoc]
        _ = B := by rw [hA, one_mul]
    simpa only [A, B, PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) hab
  · intro p hp
    exact ha p hp
  · intro p hp
    have hprime : p.Prime := by
      rcases Finset.mem_union.mp hp with hc | hr
      · exact BSD.prime_of_mem_modularExceptionalPrimes W N p hc
      · exact (Finset.mem_filter.mp hr).2
    by_cases hpN : p ∣ N
    · simpa only [b₁, b₂, if_pos hpN] using hf.inverse_bad hprime hpN
    · simpa only [b₁, b₂, if_neg hpN] using hf.inverse_good hprime hpN

set_option maxHeartbeats 800000 in
/-- The integral model itself has the required good-prime local identities. -/
theorem continues_of_integral_modular_model
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : ModularCoefficientData f)
    (htrace : ∀ (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ W.Δ → ¬ p ∣ N →
      cuspCoefficients f p = (integralModelTrace W p : ℂ)) :
    ∃ F : ℂ → ℂ, BSD.Continues (W.map (Int.castRingHom ℚ)) F := by
  apply continues_of_integral_modular_model_off W hΔ f hf htrace _ ∅
  intro p hp hp5 hdisc _
  simpa only [quadraticEulerPolynomial, integralModelTrace] using
    BSD.integralModel_local_complex_identity W hp hp5 hdisc

/-- A conditional modularity certificate for an integral model. The certificate
includes the actual point-count traces at every prime good for the model and
outside the level. -/
def IntegralModularModelData (W : WeierstrassCurve ℤ) (N : ℕ) [NeZero N] : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
    ModularCoefficientData f ∧
      ∀ (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ W.Δ → ¬ p ∣ N →
        cuspCoefficients f p = (integralModelTrace W p : ℂ)

theorem continues_of_integral_modular_data
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {N : ℕ} [NeZero N]
    (hdata : IntegralModularModelData W N) :
    ∃ F : ℂ → ℂ, BSD.Continues (W.map (Int.castRingHom ℚ)) F := by
  obtain ⟨f, hf, htrace⟩ := hdata
  exact continues_of_integral_modular_model W hΔ f hf htrace

theorem continues_of_integral_modular_data_off
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {N : ℕ} [NeZero N]
    (hdata : IntegralModularModelData W N) (E : WeierstrassCurve ℚ) (R : Finset ℕ)
    (hinverse : ∀ (p : ℕ), p.Prime → 5 ≤ p → ¬ (p : ℤ) ∣ W.Δ → p ∉ R →
      PowerSeries.mk (fun k : ℕ => (E.LFunction (p ^ k) : ℂ)) *
        quadraticEulerPolynomial (integralModelTrace W p : ℂ) (p : ℂ) = 1) :
    ∃ F : ℂ → ℂ, BSD.Continues E F := by
  obtain ⟨f, hf, htrace⟩ := hdata
  exact continues_of_integral_modular_model_off W hΔ f hf htrace E R hinverse

end BSD.General
