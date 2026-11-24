import BSD.General.PeriodsCusp
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-! Connectivity of the rational cusp line by special-linear Manin edges. -/

open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint ModularGroup
open BSD.General.PeriodsRational BSD.General.PeriodsRelative
open scoped MatrixGroups Topology

namespace BSD.RankTwo.PeriodFaithfulManin

noncomputable section

def act (g : SL(2, ℤ)) (c : OnePoint ℚ) : OnePoint ℚ := mapGL ℚ g • c

private theorem act_mul (g h : SL(2, ℤ)) (c : OnePoint ℚ) :
    act (g * h) c = act g (act h c) := by
  simp [act, map_mul, mul_smul]

/-- A function equal at the endpoints of every unimodular edge is constant. -/
theorem cusp_function_constant_of_edges {R : Type*} (v : OnePoint ℚ → R)
    (hedge : ∀ g : SL(2, ℤ), v (act g (OnePoint.some (0 : ℚ))) = v (act g ∞))
    (c : OnePoint ℚ) : v c = v ∞ := by
  let H : Subgroup SL(2, ℤ) := {
    carrier := {h | ∀ g : SL(2, ℤ), v (act (g * h) ∞) = v (act g ∞)}
    one_mem' := by intro g; simp
    mul_mem' := by
      intro a b ha hb g
      rw [← mul_assoc, hb (g * a), ha g]
    inv_mem' := by
      intro a ha g
      have h := ha (g * a⁻¹)
      simpa [mul_assoc] using h.symm }
  have hS : S ∈ H := by
    intro g
    rw [act_mul]
    have hSinf : act S ∞ = (OnePoint.some (0 : ℚ)) := by
      rw [act, smul_infty_eq_ite]
      change (if (1 : ℚ) = 0 then ∞ else OnePoint.some (0 / 1)) = _
      norm_num
    rw [hSinf]
    exact hedge g
  have hT : T ∈ H := by
    intro g
    rw [act_mul]
    have hTinf : act T ∞ = (∞ : OnePoint ℚ) := by
      rw [act, smul_infty_eq_ite]
      change (if (0 : ℚ) = 0 then ∞ else OnePoint.some (1 / 0)) = _
      simp
    rw [hTinf]
  have htop : H = ⊤ := by
    apply top_unique
    rw [← SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hS
    · exact hT
  have hg : rep c ∈ H := by rw [htop]; trivial
  have h := hg 1
  simpa [act, rep_spec_rat] using h

/-- Edge vanishing implies vanishing between every pair of rational cusps. -/
theorem periods_zero_of_edges_zero {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hedge : ∀ g : SL(2, ℤ),
      cuspFormPeriod f (act g (OnePoint.some (0 : ℚ))) (act g ∞) = 0)
    (a b : OnePoint ℚ) : cuspFormPeriod f a b = 0 := by
  let v : OnePoint ℚ → ℂ :=
    cuspValue (BSD.General.Periods.primitive f) (primitive_has_rational_limits f)
  have he : ∀ g : SL(2, ℤ), v (act g (OnePoint.some (0 : ℚ))) = v (act g ∞) := by
    intro g
    have h := hedge g
    change v (act g ∞) - v (act g (OnePoint.some (0 : ℚ))) = 0 at h
    exact (sub_eq_zero.mp h).symm
  have ha := cusp_function_constant_of_edges v he a
  have hb := cusp_function_constant_of_edges v he b
  change v b - v a = 0
  rw [ha, hb, sub_self]

end
end BSD.RankTwo.PeriodFaithfulManin
