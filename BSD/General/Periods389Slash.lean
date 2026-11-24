import BSD.General.Periods389Matrix
import Mathlib.NumberTheory.ModularForms.SlashActions

/-! The three explicit weight-two slash terms in the level-389 correspondence. -/

open Matrix GeneralLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm BigOperators

namespace BSD.General.Periods389Slash

open BSD.RankTwo.ModularSymbols.Farey

/-- The three integral Hecke matrices in the order used by `heckeMatrices`. -/
def heckeColumn (i : Fin 3) : CuspMatrix :=
  if i = 0 then ⟨(2, 0), (0, 1)⟩
  else if i = 1 then ⟨(1, 0), (0, 2)⟩ else ⟨(1, 0), (1, 2)⟩

lemma heckeColumn_det (i : Fin 3) : (heckeColumn i).det = 2 := by
  fin_cases i <;> decide

noncomputable def heckeGL (i : Fin 3) : GL (Fin 2) ℝ :=
  (heckeColumn i).toGL (by rw [heckeColumn_det]; decide)

lemma heckeGL_det (i : Fin 3) : (heckeGL i).det.val = 2 := by
  change ((heckeColumn i).toGL _).det.val = 2
  rw [CuspMatrix.toGL_det, heckeColumn_det]
  norm_num

lemma heckeGL_pos (i : Fin 3) : 0 < (heckeGL i).val.det := by
  rw [← GeneralLinearGroup.val_det_apply, heckeGL_det]
  norm_num

/-- The three slash terms equal the usual pointwise three-term expression. -/
theorem slash_sum (f : ℍ → ℂ) (τ : ℍ) :
    (∑ i : Fin 3, (f ∣[(2 : ℤ)] heckeGL i) τ) =
      2 * f (ofComplex (2 * (τ : ℂ))) +
      (f (ofComplex ((τ : ℂ) / 2)) + f (ofComplex (((τ : ℂ) + 1) / 2))) / 2 := by
  have hact (i : Fin 3) : (heckeGL i • τ : ℍ) =
      ofComplex (UpperHalfPlane.num (heckeGL i) τ / UpperHalfPlane.denom (heckeGL i) τ) := by
    rw [← coe_smul_of_det_pos (by simpa [GeneralLinearGroup.val_det_apply] using heckeGL_pos i)]
    exact (ofComplex_apply _).symm
  simp only [Fin.sum_univ_three, ModularForm.slash_apply, heckeGL_det]
  simp only [UpperHalfPlane.σ, heckeGL_det, zero_lt_two, if_true,
    ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [hact]
  norm_num [UpperHalfPlane.num, UpperHalfPlane.denom, heckeGL, heckeColumn,
    CuspMatrix.toGL_entry, CuspMatrix.realMatrix,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
  ring

end BSD.General.Periods389Slash
