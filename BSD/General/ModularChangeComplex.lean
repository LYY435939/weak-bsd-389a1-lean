import BSD.General.ModularChange
import BSD.General.ModularLocalComplex

/-! Transfer the good local inverse series across rational changes of variables. -/
namespace BSD
open WeierstrassCurve NumberField

theorem local_complex_identity_of_change (E : WeierstrassCurve ℚ)
    (W : WeierstrassCurve ℤ) (C : VariableChange ℚ)
    (hC : C • E = W.baseChange ℚ) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hdisc : ¬ (p : ℤ) ∣ W.Δ) :
    PowerSeries.mk (fun k : ℕ => (E.LFunction (p^k) : ℂ)) *
      (1 - PowerSeries.C (((p : ℤ) + 1 - Nat.card
        (W.map (Int.castRingHom (ZMod p))).toAffine.Point : ℤ) : ℂ) * PowerSeries.X +
        PowerSeries.C (p : ℂ) * PowerSeries.X ^ 2) = 1 := by
  classical
  let v := rationalPrimePlace p hp
  let M : WeierstrassCurve ℚ := W.map (Int.castRingHom ℚ)
  have hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)
  have hpolyE := localPolynomial_eq_good_of_change E W C hC hp hp5 hdisc
  have hpolyM := integralModel_localPolynomial_at_good_prime W hp hp5 hdisc
  have hpoly : (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      (M.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) := by
    exact hpolyE.trans hpolyM.symm
  have hcoeff (k : ℕ) : E.LFunction (p^k) = M.LFunction (p^k) := by
    have hE := weierstrass_LFunction_apply_prime_pow E v k
    have hM := weierstrass_LFunction_apply_prime_pow M v k
    rw [hv] at hE hM
    rw [hE, hM, localPowerSeries, localPowerSeries, hpoly]
  have hseries : PowerSeries.mk (fun k : ℕ => (E.LFunction (p^k) : ℂ)) =
      PowerSeries.mk (fun k : ℕ => (M.LFunction (p^k) : ℂ)) := by
    congr 1
    funext k
    rw [hcoeff k]
  rw [hseries]
  simpa [M] using
    integralModel_local_complex_identity W hp hp5 hdisc

end BSD
