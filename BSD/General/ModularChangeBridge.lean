import BSD.General.ModularChangeComplex
import BSD.General.ModularData

namespace BSD
open WeierstrassCurve

/-- A modularity certificate transfers across a rational change of variables. -/
theorem continues_of_change_of_integral_modular_data
    (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) (C : VariableChange ℚ)
    (hC : C • E = W.baseChange ℚ) (hΔ : W.Δ ≠ 0) {N : ℕ} [NeZero N]
    (hdata : BSD.General.IntegralModularModelData W N) :
    ∃ F : ℂ → ℂ, BSD.Continues E F := by
  apply BSD.General.continues_of_integral_modular_data_off W hΔ hdata E ∅
  intro p hp hp5 hdisc _
  simpa [BSD.General.quadraticEulerPolynomial, BSD.General.integralModelTrace] using
    local_complex_identity_of_change E W C hC hp hp5 hdisc

end BSD
