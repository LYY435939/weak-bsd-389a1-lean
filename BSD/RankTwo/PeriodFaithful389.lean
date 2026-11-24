import BSD.RankTwo.PeriodFaithfulManin
import BSD.General.Periods389Matrix
import BSD.RankTwo.PeriodFaithfulFrickeColumns
import BSD.RankTwo.PeriodFaithfulFrickeSign

/-! The unimodular edges used by rational-cusp connectivity. -/

namespace BSD.RankTwo.PeriodFaithful389

open Matrix SpecialLinearGroup OnePoint UpperHalfPlane
open BSD.RankTwo.ModularSymbols BSD.RankTwo.ModularSymbols.Farey
open BSD.General BSD.General.Periods389
open BSD.RankTwo.PeriodFaithfulHecke BSD.RankTwo.PeriodFaithfulFrickePath
open BSD.RankTwo.PeriodFaithfulFrickeColumns BSD.RankTwo.PeriodFaithfulLinear
open BSD.RankTwo.PeriodFaithfulManin
open BSD.General.PeriodsRelative
open scoped MatrixGroups ModularForm

local instance : Fact (Nat.Prime 389) := ⟨by norm_num⟩

/-- Regard an integral special-linear matrix as a matrix of Farey columns. -/
def edgeMatrix (g : SL(2, ℤ)) : CuspMatrix :=
  ⟨(g 0 0, g 1 0), (g 0 1, g 1 1)⟩

@[simp] theorem edgeMatrix_det (g : SL(2, ℤ)) : (edgeMatrix g).det = 1 := by
  have h := g.property
  rw [Matrix.det_fin_two] at h
  simpa [edgeMatrix, CuspMatrix.det] using h

/-- The first column is the image of infinity. -/
theorem edgeMatrix_left (g : SL(2, ℤ)) :
    cusp (edgeMatrix g).left = act g ∞ := by
  rw [act, smul_infty_eq_ite]
  change (if g 1 0 = 0 then ∞ else OnePoint.some ((g 0 0 : ℚ) / (g 1 0 : ℚ))) =
    (if (g 1 0 : ℚ) = 0 then ∞ else OnePoint.some ((g 0 0 : ℚ) / (g 1 0 : ℚ)))
  simp only [Int.cast_eq_zero]

/-- The second column is the image of zero. -/
theorem edgeMatrix_right (g : SL(2, ℤ)) :
    cusp (edgeMatrix g).right = act g (OnePoint.some (0 : ℚ)) := by
  rw [act, smul_some_eq_ite]
  simp only [mul_zero, zero_add]
  change (if g 1 1 = 0 then ∞ else OnePoint.some ((g 0 1 : ℚ) / (g 1 1 : ℚ))) =
    (if (g 1 1 : ℚ) = 0 then ∞ else OnePoint.some ((g 0 1 : ℚ) / (g 1 1 : ℚ)))
  simp only [Int.cast_eq_zero]

/-- Vanishing on every Manin representative implies vanishing of all rational periods. -/
theorem periods_zero_of_manin_zero
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hinv : Gamma0Invariant (cuspFormPeriod f))
    (hzero : ∀ i, manin (cuspFormPeriod f) i = 0)
    (a b : OnePoint ℚ) : cuspFormPeriod f a b = 0 := by
  apply periods_zero_of_edges_zero f
  intro g
  rw [← edgeMatrix_right, ← edgeMatrix_left]
  have h := path_eq_manin (cuspFormPeriod f) hinv (edgeMatrix g) (edgeMatrix_det g)
  change cuspFormPeriod f (cusp (edgeMatrix g).right) (cusp (edgeMatrix g).left) = _ at h
  rw [h, hzero]

/-- The true level-389 coefficient relations and second coefficient force the
negative Fricke eigenvalue. -/
theorem fricke_slash_eq_neg
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hf : ModularCoefficientData f)
    (h2 : cuspCoefficients f 2 = (traceTwo : ℂ)) :
    (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke 389 (by norm_num) = -⇑f := by
  have hF : Gamma0Invariant (cuspFormPeriod f) := gamma_invariant f
  have hS := manin_swap (cuspFormPeriod f) (cuspFormPeriod_add f) hF
  have hR := manin_rotate (cuspFormPeriod f) (cuspFormPeriod_add f) hF
  have hT := satisfies_hecke_two f hf h2
  have hanti (i : Index) :
      manin (cuspFormPeriod (frickeCusp 389 f + f)) i = 0 := by
    have heval := fricke_path_evaluation (cuspFormPeriod f) (cuspFormPeriod_add f) hF i
    have hfricke := Fricke.fricke_eq_neg (manin (cuspFormPeriod f)) hS hR hT i
    rw [heval] at hfricke
    change cuspFormPeriod f (frickeQ 389 • cusp (representative i).right)
      (frickeQ 389 • cusp (representative i).left) =
        -cuspFormPeriod f (cusp (representative i).right) (cusp (representative i).left) at hfricke
    change cuspFormPeriod (frickeCusp 389 f + f) (cusp (representative i).right)
      (cusp (representative i).left) = 0
    rw [cuspFormPeriod_add_forms, fricke_period, hfricke, neg_add_cancel]
  apply fricke_slash_eq_neg_of_anti_periods 389 f
  intro a b
  have hz := periods_zero_of_manin_zero (frickeCusp 389 f + f)
    (gamma_invariant (frickeCusp 389 f + f)) hanti a b
  rwa [cuspFormPeriod_add_forms] at hz

end BSD.RankTwo.PeriodFaithful389
