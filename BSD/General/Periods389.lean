import BSD.General.Periods389Slash
import BSD.General.PeriodsFunctorial
import BSD.General.PeriodsMellinCusp

/-! The canonical cusp period supplies the geometric level-389 certificate. -/

open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint UpperHalfPlane Filter
open BSD.RankTwo.ModularSymbols BSD.RankTwo.ModularSymbols.Farey
open BSD.General.PeriodsRational BSD.General.PeriodsRelative BSD.General.Periods389Slash
open scoped MatrixGroups ModularForm BigOperators Topology

namespace BSD.General.Periods389

noncomputable section

private def sCol : CuspMatrix := ⟨(0, 1), (-1, 0)⟩
private theorem sCol_det : sCol.det = 1 := by decide

private def leftLift (m : CuspMatrix) (hm : m.det ≠ 0) : GL (Fin 2) ℝ := m.toGL hm
private def rightLift (m : CuspMatrix) (hm : m.det ≠ 0) : GL (Fin 2) ℝ :=
  (m.comp sCol).toGL (by rw [CuspMatrix.det_comp, sCol_det, mul_one]; exact hm)

private theorem leftLift_endpoint (m : CuspMatrix) (hm : m.det ≠ 0) :
    cuspInf (leftLift m hm) = OnePoint.map Rat.cast (cusp m.left) :=
  m.toGL_smul_infty hm

private theorem rightLift_endpoint (m : CuspMatrix) (hm : m.det ≠ 0) :
    cuspInf (rightLift m hm) = OnePoint.map Rat.cast (cusp m.right) := by
  simpa [rightLift, cuspInf, CuspMatrix.comp, CuspMatrix.act, sCol] using
    ((m.comp sCol).toGL_smul_infty (by rw [CuspMatrix.det_comp, sCol_det, mul_one]; exact hm))

private theorem leftLift_comp (g m : CuspMatrix) (hg : g.det ≠ 0) (hm : m.det ≠ 0)
    (hgm : (g.comp m).det ≠ 0) :
    g.toGL hg * leftLift m hm = leftLift (g.comp m) hgm := by
  exact (CuspMatrix.toGL_comp g m hg hm hgm).symm

private theorem rightLift_comp (g m : CuspMatrix) (hg : g.det ≠ 0) (hm : m.det ≠ 0)
    (hgm : (g.comp m).det ≠ 0) :
    g.toGL hg * rightLift m hm = rightLift (g.comp m) hgm := by
  have hms : (m.comp sCol).det ≠ 0 := by
    rw [CuspMatrix.det_comp, sCol_det, mul_one]; exact hm
  have hgms : (g.comp (m.comp sCol)).det ≠ 0 := by
    rw [CuspMatrix.det_comp, CuspMatrix.det_comp, sCol_det, mul_one]
    exact mul_ne_zero hg hm
  rw [rightLift, rightLift, ← CuspMatrix.toGL_comp g (m.comp sCol) hg hms hgms]
  congr 1
  cases g with | mk gl gr => cases m with | mk ml mr =>
    simp [CuspMatrix.comp, CuspMatrix.act, sCol]
    constructor <;> ring

theorem gamma_invariant (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2) :
    Gamma0Invariant (cuspFormPeriod f) := by
  intro g hg hdiv m hm
  have hg0 : g.det ≠ 0 := by rw [hg]; decide
  have hm0 : m.det ≠ 0 := by rw [hm]; decide
  have hgm : (g.comp m).det ≠ 0 := by rw [CuspMatrix.det_comp, hg, hm]; decide
  have hgpos : 0 < (g.toGL hg0).val.det := by
    rw [← GeneralLinearGroup.val_det_apply, CuspMatrix.toGL_det, hg]
    norm_num
  have hgmem : g.toSL hg ∈ CongruenceSubgroup.Gamma0 389 :=
    (g.toSL_mem_Gamma0_iff hg 389).mpr hdiv
  have hslash : ∀ τ : ℍ, ((f : ℍ → ℂ) ∣[(2 : ℤ)] g.toGL hg0) τ = f τ := by
    intro τ
    rw [← CuspMatrix.mapGL_toSL g hg hg0]
    exact congrFun (SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hgmem)) τ
  apply relativePeriod_eq_of_slash_eq (g.toGL hg0) hgpos f (Periods.primitive f)
    (fun τ => Periods.hasDerivAt_primitive f τ.im_pos) hslash
    (primitive_has_rational_limits f) (cusp m.right) (cusp m.left)
    (rightLift m hm0) (leftLift m hm0) (rightLift_endpoint m hm0) (leftLift_endpoint m hm0)
    (cusp (g.comp m).right) (cusp (g.comp m).left)
  · rw [rightLift_comp g m hg0 hm0 hgm]; exact rightLift_endpoint _ _
  · rw [leftLift_comp g m hg0 hm0 hgm]; exact leftLift_endpoint _ _

/-- The three Hecke translates act on the canonical cusp period with the given eigenvalue. -/
theorem path_hecke_sum_of_traceTwo_slash
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hT : ∀ τ : ℍ,
      2 * f (ofComplex (2 * (τ : ℂ))) +
        (f (ofComplex ((τ : ℂ) / 2)) + f (ofComplex (((τ : ℂ) + 1) / 2))) / 2 =
          (traceTwo : ℂ) * f τ)
    (m : CuspMatrix) (hm : m.det = 1) :
    (heckeMatrices.map fun t => path (cuspFormPeriod f) (t.comp m)).sum =
      (traceTwo : ℂ) * path (cuspFormPeriod f) m := by
  have hm0 : m.det ≠ 0 := by rw [hm]; decide
  have hcomp (i : Fin 3) : ((heckeColumn i).comp m).det ≠ 0 := by
    rw [CuspMatrix.det_comp, heckeColumn_det, hm]; decide
  have hsum := relativePeriod_sum_of_slash (Finset.univ : Finset (Fin 3)) heckeGL
    (fun i _ => heckeGL_pos i) f (Periods.primitive f) (traceTwo : ℂ)
    (fun τ => Periods.hasDerivAt_primitive f τ.im_pos)
    (by intro τ; simpa using (slash_sum f τ).trans (hT τ))
    (primitive_has_rational_limits f) (cusp m.right) (cusp m.left)
    (rightLift m hm0) (leftLift m hm0) (rightLift_endpoint m hm0) (leftLift_endpoint m hm0)
    (fun i => cusp (((heckeColumn i).comp m).right))
    (fun i => cusp (((heckeColumn i).comp m).left))
    (by intro i hi; rw [heckeGL, rightLift_comp _ _ _ _ (hcomp i)]; exact rightLift_endpoint _ _)
    (by intro i hi; rw [heckeGL, leftLift_comp _ _ _ _ (hcomp i)]; exact leftLift_endpoint _ _)
  rw [Fin.sum_univ_three] at hsum
  simpa [heckeMatrices, heckeColumn, path, cuspFormPeriod, add_assoc] using hsum

/-- The actual cusp form has central value zero whenever it satisfies the explicit
three-term weight-two T₂ eigenrelation with the trace of 389.a1. -/
theorem L_one_eq_zero_of_traceTwo_slash
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (hT : ∀ τ : ℍ,
      2 * f (ofComplex (2 * (τ : ℂ))) +
        (f (ofComplex ((τ : ℂ) / 2)) + f (ofComplex (((τ : ℂ) + 1) / 2))) / 2 =
          (traceTwo : ℂ) * f τ) :
    ModularForm.L (by decide : 0 < (2 : ℤ)) f 1 = 0 := by
  apply cuspForm_L_one_eq_zero_of_geometric_symbols f (cuspFormPeriod f)
    (cuspFormPeriod_add f) (gamma_invariant f)
  · exact path_hecke_sum_of_traceTwo_slash f hT
  · simpa [BSD.RankTwo.centralPeriod] using cuspFormPeriod_zero_infty f

end
end BSD.General.Periods389
