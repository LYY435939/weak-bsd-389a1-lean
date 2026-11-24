import BSD.General.PeriodsRational
import BSD.RankTwo.FareyHecke

/-! A matrix bridge from the explicit Farey columns to the geometric action. -/

open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups

namespace BSD.RankTwo.ModularSymbols.Farey.CuspMatrix

/-- The real matrix having the given Farey columns. -/
def realMatrix (m : CuspMatrix) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(m.left.1 : ℝ), (m.right.1 : ℝ); (m.left.2 : ℝ), (m.right.2 : ℝ)]

lemma realMatrix_det (m : CuspMatrix) : m.realMatrix.det = (m.det : ℝ) := by
  simp [realMatrix, det, Matrix.det_fin_two]

/-- Any nondegenerate Farey matrix acts as a real projective transformation. -/
noncomputable def toGL (m : CuspMatrix) (hm : m.det ≠ 0) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero m.realMatrix (by
    rw [realMatrix_det]
    exact_mod_cast hm)

@[simp] lemma toGL_entry (m : CuspMatrix) (hm : m.det ≠ 0) (i j : Fin 2) :
    m.toGL hm i j = m.realMatrix i j := rfl

/-- Matrix composition agrees with composition of projective transformations. -/
theorem toGL_comp (m n : CuspMatrix) (hm : m.det ≠ 0) (hn : n.det ≠ 0)
    (hmn : (m.comp n).det ≠ 0) :
    (m.comp n).toGL hmn = m.toGL hm * n.toGL hn := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toGL, realMatrix, comp, act, Int.cast_add, Int.cast_mul]

/-- The left Farey column is the image of infinity. -/
theorem toGL_smul_infty (m : CuspMatrix) (hm : m.det ≠ 0) :
    m.toGL hm • (∞ : OnePoint ℝ) = OnePoint.map Rat.cast (cusp m.left) := by
  rw [smul_infty_eq_ite]
  by_cases h : m.left.2 = 0 <;>
    simp [toGL_entry, realMatrix, cusp, h, Rat.cast_div]

/-- The right Farey column is the image of zero. -/
theorem toGL_smul_zero (m : CuspMatrix) (hm : m.det ≠ 0) :
    m.toGL hm • ((0 : ℝ) : OnePoint ℝ) = OnePoint.map Rat.cast (cusp m.right) := by
  rw [smul_some_eq_ite]
  by_cases h : m.right.2 = 0 <;>
    simp [toGL_entry, realMatrix, cusp, h, Rat.cast_div]

/-- A unimodular Farey matrix as an integral special-linear matrix. -/
def toSL (m : CuspMatrix) (hm : m.det = 1) : SL(2, ℤ) :=
  ⟨!![m.left.1, m.right.1; m.left.2, m.right.2], by
    simpa [Matrix.det_fin_two, det] using hm⟩

/-- The determinant of the real transformation is the Farey determinant. -/
theorem toGL_det (m : CuspMatrix) (hm : m.det ≠ 0) :
    ((m.toGL hm).det : ℝ) = (m.det : ℝ) := by
  rw [GeneralLinearGroup.val_det_apply]
  exact realMatrix_det m

/-- For determinant one the explicit real transformation is the image of the
integral special-linear matrix. -/
theorem mapGL_toSL (m : CuspMatrix) (hm : m.det = 1) (hne : m.det ≠ 0) :
    mapGL ℝ (m.toSL hm) = m.toGL hne := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Membership in the level subgroup is the divisibility condition on the
lower-left Farey entry. -/
theorem toSL_mem_Gamma0_iff (m : CuspMatrix) (hm : m.det = 1) (N : ℕ) :
    m.toSL hm ∈ CongruenceSubgroup.Gamma0 N ↔ (N : ℤ) ∣ m.left.2 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

end BSD.RankTwo.ModularSymbols.Farey.CuspMatrix
