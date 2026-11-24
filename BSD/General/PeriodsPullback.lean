import BSD.General.PeriodsSlash
import BSD.General.PeriodsLimit

/-! A finite weight-two slash relation pulls back primitives up to a constant.
The passage to cusp endpoints requires the corresponding limit hypotheses. -/

open UpperHalfPlane Filter OnePoint Matrix SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators Topology

namespace BSD.General

/-- A finite slash relation yields a constant difference between the sum of
pulled-back primitives and the corresponding multiple of the primitive. -/
theorem primitive_sum_comp_smul_eq_add_const
    {ι : Type*} (s : Finset ι) (g : ι → GL (Fin 2) ℝ)
    (hg : ∀ i ∈ s, 0 < (g i).val.det)
    (f : ℍ → ℂ) (P : ℂ → ℂ) (a : ℂ)
    (hP : ∀ τ : ℍ, HasDerivAt P (f τ) τ)
    (hslash : ∀ τ : ℍ, (∑ i ∈ s, (f ∣[(2 : ℤ)] (g i)) τ) = a * f τ) :
    ∃ c : ℂ, ∀ z : ℂ, 0 < z.im →
      (∑ i ∈ s, P (g i • ofComplex z : ℍ)) = a * P z + c := by
  let Q : ℂ → ℂ := fun z => ∑ i ∈ s, P (g i • ofComplex z : ℍ)
  let R : ℂ → ℂ := fun z => a * P z
  let F : ℂ → ℂ := fun z => a * f (ofComplex z)
  apply PeriodsLimit.primitives_differ_by_constant Q R F
  · intro z hz
    let τ : ℍ := ⟨z, hz⟩
    have hd := HasDerivAt.fun_sum (fun i hi =>
      hasDerivAt_primitive_comp_smul f P (g i) (hg i hi) τ (hP (g i • τ)))
    simpa only [Q, F, UpperHalfPlane.ofComplex_apply_of_im_pos hz, hslash] using hd
  · intro z hz
    simpa only [R, F, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
      (hP ⟨z, hz⟩).const_mul a

end BSD.General
