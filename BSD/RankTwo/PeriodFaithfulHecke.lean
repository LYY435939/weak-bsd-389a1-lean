import BSD.General.Periods389
import BSD.General.ModularDataHecke
import BSD.RankTwo.FrickeSymbols

/-! The genuine coefficient relations give the T₂ relation on period symbols. -/

open Matrix SpecialLinearGroup OnePoint UpperHalfPlane
open BSD.General BSD.General.PeriodsRelative BSD.General.Periods389
open BSD.RankTwo.ModularSymbols BSD.RankTwo.ModularSymbols.Farey
open scoped MatrixGroups ModularForm

namespace BSD.RankTwo.PeriodFaithfulHecke

def representative (i : Index) : CuspMatrix :=
  if i = 389 then ⟨(0, 1), (-1, 0)⟩ else ⟨(1, i.val), (0, 1)⟩

theorem representative_det (i : Index) : (representative i).det = 1 := by
  by_cases h : i = 389 <;> simp [representative, h, CuspMatrix.det]

/-- Actual coefficient recurrences and the actual second coefficient imply the
T₂ = −2 relation on the Manin symbol of rational cusp periods. -/
theorem satisfies_hecke_two
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hf : ModularCoefficientData f)
    (h2 : cuspCoefficients f 2 = (traceTwo : ℂ)) (i : Index) :
    ((heckeTwo i).map (manin (cuspFormPeriod f))).sum =
      (-2 : ℂ) * manin (cuspFormPeriod f) i := by
  have hT (τ : ℍ) := ModularCoefficientData.hecke_two_pointwise f hf
    (by decide : ¬ 2 ∣ 389) τ
  rw [h2] at hT
  have hgeom := path_hecke_sum_of_traceTwo_slash f hT (representative i) (representative_det i)
  rw [merel_eq_heckeCorrespondence (cuspFormPeriod f) (cuspFormPeriod_add f)
    (gamma_invariant f)]
  change (heckeMatrices.map fun t => path (cuspFormPeriod f) (t.comp (representative i))).sum =
    (-2 : ℂ) * path (cuspFormPeriod f) (representative i)
  simpa [traceTwo_eq] using hgeom

end BSD.RankTwo.PeriodFaithfulHecke
