import BSD.General.Periods389
import BSD.RankTwo.FromModularityBadTrace
import BSD.RankTwo.FromModularityCoefficients
import BSD.RankTwo.ModularAssembly
import BSD.RankTwo.PeriodFaithful389

/-! The rank part of BSD for 389.a1 from its normalized modular form and good traces. -/

namespace BSD.RankTwo

open BSD.General

/-- A normalized weight-two eigenform of level 389 with the good-prime traces
of the model suffices to prove the rank equality for 389.a1. -/
theorem rankPart_of_integral_modular_model_data
    (hdata : IntegralModularModelData (model ℤ) 389) : BSD.RankPart curve := by
  obtain ⟨f, hf, htrace⟩ := hdata
  have h₂ := cuspCoefficients_two_of_model_trace f htrace
  have hw := PeriodFaithful389.fricke_slash_eq_neg f hf h₂
  have hb := bad_trace_of_fricke f hf hw
  have hq := all_coefficients_of_eigenform_good_and_bad_trace f hf htrace hb
  have hL := Periods389.L_one_eq_zero_of_traceTwo_slash f (fun τ ↦ by
    rw [← h₂]
    exact ModularCoefficientData.hecke_two_pointwise f hf (by decide) τ)
  rw [cuspForm_L_one_eq_centralPeriod f] at hL
  have hp : centralPeriod f = 0 := (mul_eq_zero.mp hL).resolve_left
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
  exact rankPart_of_modular_data f hq hw hp

end BSD.RankTwo
