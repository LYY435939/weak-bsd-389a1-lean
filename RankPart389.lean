import BSD.RankTwo.FromModularity
import BSD.RankTwo.ModularSymbolsLocal
import ExactWitness
import ExternalDataBridge

namespace BSD.RankTwo.FLTAdapter

open BSD.General

/-- Exact-conductor modularity of the semistable model gives the level-389 witness. -/
theorem integral_modular_model_data389 : IntegralModularModelData (model ℤ) 389 := by
  obtain ⟨N, _, hsquarefree, hsupport, hmod⟩ :=
    exact_of_semistable (model ℤ) (by rw [discriminant]; norm_num)
      ModularSymbols.isSemistableModel
  obtain rfl := ModularSymbols.conductor_eq_389_of_squarefree_support hsquarefree hsupport
  exact BSD.FLTAdapter.integralModularModelData_of_flt (model ℤ) hmod

/-- The analytic rank of 389.a1 equals its Mordell–Weil rank. -/
theorem weakBSD389 : BSD.RankPart curve :=
  rankPart_of_integral_modular_model_data integral_modular_model_data389

end BSD.RankTwo.FLTAdapter

#print axioms BSD.RankTwo.FLTAdapter.integral_modular_model_data389
#print axioms BSD.RankTwo.FLTAdapter.weakBSD389
#check BSD.RankTwo.FLTAdapter.weakBSD389
#check BSD.RankTwo.FLTAdapter.integral_modular_model_data389
