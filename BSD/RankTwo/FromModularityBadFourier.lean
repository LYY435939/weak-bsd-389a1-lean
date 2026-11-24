import BSD.General.ModularDataHecke

/-! Fourier coefficient of the averaging operator at the level prime. -/

noncomputable section

namespace BSD.RankTwo

open UpperHalfPlane CongruenceSubgroup
open BSD.General
open scoped BigOperators

private theorem q_translate (p : ℕ) [Fact p.Prime] (z : ℂ) (a : ℕ) :
    Function.Periodic.qParam 1 ((z + a) / p) =
      Function.Periodic.qParam p z * Function.Periodic.qParam p a := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

private theorem q_power (p : ℕ) [Fact p.Prime] (z : ℂ) :
    Function.Periodic.qParam p z ^ p = Function.Periodic.qParam 1 z := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private theorem q_power_integer (p : ℕ) [Fact p.Prime] (a : ℕ) :
    Function.Periodic.qParam p (a : ℂ) ^ p = 1 := by
  rw [q_power]
  simpa [Function.Periodic.qParam, mul_assoc, mul_comm, mul_left_comm] using
    Complex.exp_int_mul_two_pi_mul_I (a : ℤ)

private theorem hasSum_insert (p : ℕ) [Fact p.Prime] (a : ℕ → ℂ) (q s : ℂ)
    (h : HasSum (fun n => a n * (q ^ p) ^ n) s) :
    HasSum (fun n => (if p ∣ n then a (n / p) else 0) * q ^ n) s := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let b : ℕ → ℂ := fun n => a n * (q ^ p) ^ n
  have he : HasSum (fun n => if p ∣ n then b (n / p) else 0) s := by
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ hp) ?_).mp ?_
    · intro n hn
      have hnd : ¬ p ∣ n := by
        rintro ⟨k, hk⟩
        apply hn
        exact ⟨k, by simpa [mul_comm] using hk.symm⟩
      simp [hnd]
    · simpa [b, Function.comp_def, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos] using h
  refine he.congr_fun fun n => ?_
  by_cases hn : p ∣ n
  · have hn' : p * (n / p) = n := Nat.mul_div_cancel' hn
    simp only [hn, if_true, b]
    rw [← pow_mul, hn']
  · simp [hn]

/-- If the average of translates is the identity, its first bad-prime
Fourier coefficient equals one. -/
theorem bad_trace_of_average {p : ℕ} [Fact p.Prime]
    (f : CuspForm (Gamma0 p) 2) (hf : ModularCoefficientData f)
    (hav : ∀ τ : ℍ, ∑ a : ZMod p,
      f (ofComplex (((τ : ℂ) + (a.val : ℂ)) / (p : ℂ))) = (p : ℂ) * f τ) :
    cuspCoefficients f p = 1 := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let c : ℕ → ℂ := fun n => (∑ a : ZMod p,
    cuspCoefficients f n * Function.Periodic.qParam p (a.val : ℂ) ^ n) / p
  let d : ℕ → ℂ := fun n => if p ∣ n then cuspCoefficients f (n / p) else 0
  have hleft (τ : ℍ) : HasSum (fun n => c n • Function.Periodic.qParam p τ ^ n) (f τ) := by
    have hh (a : ZMod p) : HasSum (fun n =>
        (cuspCoefficients f n * Function.Periodic.qParam p (a.val : ℂ) ^ n) *
          Function.Periodic.qParam p τ ^ n)
        (f (ofComplex (((τ : ℂ) + (a.val : ℂ)) / (p : ℂ)))) := by
      have him : 0 < (((τ : ℂ) + (a.val : ℂ)) / (p : ℂ)).im := by
        have hpcast : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; rfl
        rw [hpcast, Complex.div_ofReal_im, Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos τ.im_pos hp
      have h := cuspCoefficients_hasSum f (ofComplex (((τ : ℂ) + (a.val : ℂ)) / (p : ℂ)))
      rw [ofComplex_apply_of_im_pos him, q_translate] at h
      rw [ofComplex_apply_of_im_pos him]
      simpa [mul_pow, mul_assoc, mul_comm, mul_left_comm] using h
    have hs := hasSum_sum (s := Finset.univ) (fun a _ => hh a)
    have hs' := hs.div_const (p : ℂ)
    rw [hav τ, mul_div_cancel_left₀ _ hpc] at hs'
    apply hs'.congr_fun
    intro n
    simp only [c, smul_eq_mul, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hright (τ : ℍ) : HasSum (fun n => d n • Function.Periodic.qParam p τ ^ n) (f τ) := by
    have h := cuspCoefficients_hasSum f τ
    rw [← q_power p τ] at h
    simpa [d, smul_eq_mul] using hasSum_insert p (cuspCoefficients f) _ _ h
  have hperiod : (p : ℝ) ∈ (Gamma0 p).strictPeriods := by
    rw [strictPeriods_Gamma0]
    exact ⟨(p : ℤ), by simp⟩
  have hc := ModularFormClass.qExpansion_coeff_unique hp hperiod hleft p
  have hd := ModularFormClass.qExpansion_coeff_unique hp hperiod hright p
  have heq : c p = d p := hc.trans hd.symm
  have hcp : c p = cuspCoefficients f p := by
    dsimp only [c]
    simp only [q_power_integer, mul_one, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
  have hdp : d p = 1 := by
    change (if p ∣ p then cuspCoefficients f (p / p) else 0) = 1
    rw [if_pos (dvd_refl p), Nat.div_self (Fact.out : p.Prime).pos, hf.qCoeff_one]
  exact hcp.symm.trans (heq.trans hdp)

end BSD.RankTwo
