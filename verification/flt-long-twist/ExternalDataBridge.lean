import Definitions.Def_FLTPrelim_Modularity
import BSD.General.ModularChangeBridge

namespace BSD.FLTAdapter

open WeierstrassCurve

theorem ap_eq_integralModelTrace (W : WeierstrassCurve ℤ) (p : ℕ) :
    W.apOfModel p = BSD.General.integralModelTrace W p := by
  simp only [apOfModel, reductionMod, traceOfFrobenius, card,
    BSD.General.integralModelTrace, Nat.card_zmod]

theorem integralModularModelData_of_flt (W : WeierstrassCurve ℤ) {N : ℕ} [NeZero N]
    (h : W.IsModularModelOfLevel N) : BSD.General.IntegralModularModelData W N := by
  obtain ⟨f, hf, htrace⟩ := h
  refine ⟨f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hf.qCoeff_one
  · exact hf.qCoeff_mul_of_coprime
  · exact hf.qCoeff_prime_pow_of_not_dvd
  · exact hf.qCoeff_prime_pow_of_dvd
  · intro p hp hgood hpN
    simpa only [BSD.General.cuspCoefficients_apply, ModularFormClass.qCoeff,
      ap_eq_integralModelTrace W p] using htrace p hp hgood hpN

theorem continues_of_flt_model (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {N : ℕ} [NeZero N] (h : W.IsModularModelOfLevel N) :
    ∃ F : ℂ → ℂ, BSD.Continues (W.map (Int.castRingHom ℚ)) F :=
  BSD.General.continues_of_integral_modular_data W hΔ (integralModularModelData_of_flt W h)

theorem continues_of_flt_model_change (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (C : VariableChange ℚ) (hC : C • E = W.baseChange ℚ) (hΔ : W.Δ ≠ 0)
    {N : ℕ} [NeZero N] (h : W.IsModularModelOfLevel N) :
    ∃ F : ℂ → ℂ, BSD.Continues E F :=
  BSD.continues_of_change_of_integral_modular_data E W C hC hΔ
    (integralModularModelData_of_flt W h)

end BSD.FLTAdapter

#print axioms BSD.FLTAdapter.ap_eq_integralModelTrace
#print axioms BSD.FLTAdapter.integralModularModelData_of_flt
#print axioms BSD.FLTAdapter.continues_of_flt_model
#print axioms BSD.FLTAdapter.continues_of_flt_model_change
