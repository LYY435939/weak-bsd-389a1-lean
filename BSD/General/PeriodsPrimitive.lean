import BSD.General.PeriodsPrimitiveKernel
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open Complex UpperHalfPlane Filter Function Metric ModularForm
open scoped CongruenceSubgroup MatrixGroups Topology Manifold Real ModularForm

namespace BSD.General.Periods
noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped Pointwise in

private theorem natCast_mem_strictPeriods_conj {Γ : Subgroup SL(2, ℤ)} {N : ℕ}
    (hΓ : Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    (N : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul]

  have hT1 : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T
      = Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.GeneralLinearGroup.upperRightHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | change (((1 : ℤ) : ℝ) = (1 : ℝ)); exact Int.cast_one
            | change (((0 : ℤ) : ℝ) = (0 : ℝ)); exact Int.cast_zero
  have hTN : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))
      = Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
    rw [zpow_natCast, map_pow, hT1, ← AddChar.map_nsmul_eq_pow]
    norm_num
  rw [← hTN, ← map_mul, ← map_inv, ← map_mul]
  refine Subgroup.mem_map_of_mem _ (hΓ ?_)
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  exact (Gamma_normal N).conj_mem _ hTmem δ

variable {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)

private theorem periodic_slash_comp_ofComplex {N : ℕ}
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (hΓ : Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    Periodic (((f : ℍ → ℂ) ∣[k] δ) ∘ ofComplex) (N : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ δ))
    (natCast_mem_strictPeriods_conj hΓ δ)


theorem exists_normalized_primitive_slash {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N) 2) (δ : SL(2, ℤ)) :
    ∃ G : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := by
  have hΓ : Gamma N ≤ Gamma0 N := fun _ hA =>
    Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1
  have : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hN : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact exists_normalized_primitive hN (periodic_slash_comp_ofComplex f hΓ δ)
    ((CuspFormClass.holo f).slash 2 _) (CuspFormClass.zero_at_infty_slash f δ)

variable {N : ℕ} [NeZero N]
variable (f : CuspForm (Gamma0 N) 2)

private def normalizedPrimitive : ℍ → ℂ := (exists_normalized_primitive_slash f 1).choose

/-- A primitive normalized to vanish at the cusp at infinity. -/
def primitive : ℂ → ℂ := normalizedPrimitive f ∘ ofComplex

theorem hasDerivAt_primitive {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (primitive f) (f ⟨z, hz⟩) z := by
  simpa [primitive, normalizedPrimitive] using
    ((exists_normalized_primitive_slash f 1).choose_spec.1 ⟨z, hz⟩)

theorem tendsto_primitive_atImInfty :
    Tendsto (fun z : ℍ ↦ primitive f z) atImInfty (𝓝 0) := by
  simpa [primitive, normalizedPrimitive] using
    (exists_normalized_primitive_slash f 1).choose_spec.2

end
end BSD.General.Periods
