import BSD.General.PeriodsPullback
import BSD.General.PeriodsRelative

open UpperHalfPlane Filter OnePoint Matrix SpecialLinearGroup
open BSD.General.PeriodsRational BSD.General.PeriodsRelative
open scoped MatrixGroups ModularForm BigOperators Topology

namespace BSD.General

/-- Cusp endpoint limits convert a finite slash relation into the corresponding
relation on oriented relative periods. -/
theorem relativePeriod_sum_of_slash
    {ι : Type*} (s : Finset ι) (g : ι → GL (Fin 2) ℝ)
    (hg : ∀ i ∈ s, 0 < (g i).val.det)
    (f : ℍ → ℂ) (P : ℂ → ℂ) (a₂ : ℂ)
    (hP : ∀ τ : ℍ, HasDerivAt P (f τ) τ)
    (hslash : ∀ τ : ℍ, (∑ i ∈ s, (f ∣[(2 : ℤ)] (g i)) τ) = a₂ * f τ)
    (hRep : ∀ c : OnePoint ℚ, ∃ L : ℂ,
      Tendsto (fun z : ℍ => P ((mapGL ℝ (rep c) • z : ℍ) : ℂ)) atImInfty (𝓝 L))
    (a b : OnePoint ℚ) (A B : GL (Fin 2) ℝ)
    (hA : cuspInf A = OnePoint.map Rat.cast a)
    (hB : cuspInf B = OnePoint.map Rat.cast b)
    (u v : ι → OnePoint ℚ)
    (hu : ∀ i ∈ s, cuspInf (g i * A) = OnePoint.map Rat.cast (u i))
    (hv : ∀ i ∈ s, cuspInf (g i * B) = OnePoint.map Rat.cast (v i)) :
    (∑ i ∈ s, relativePeriod P hRep (u i) (v i)) =
      a₂ * relativePeriod P hRep a b := by
  obtain ⟨c, hc⟩ := primitive_sum_comp_smul_eq_add_const s g hg f P a₂ hP hslash
  have endpoint (d : OnePoint ℚ) (D : GL (Fin 2) ℝ)
      (hD : cuspInf D = OnePoint.map Rat.cast d) (w : ι → OnePoint ℚ)
      (hw : ∀ i ∈ s, cuspInf (g i * D) = OnePoint.map Rat.cast (w i)) :
      (∑ i ∈ s, cuspValue P hRep (w i)) = a₂ * cuspValue P hRep d + c := by
    have hleft : Tendsto (fun z : ℍ => ∑ i ∈ s, P ((g i • (D • z) : ℍ) : ℂ))
        atImInfty (𝓝 (∑ i ∈ s, cuspValue P hRep (w i))) := by
      apply tendsto_finsetSum
      intro i hi
      simpa only [mul_smul] using tendsto_primitive_cusp P hRep (w i)
        (g i * D) (hw i hi)
    have hright : Tendsto (fun z : ℍ => a₂ * P ((D • z : ℍ) : ℂ) + c)
        atImInfty (𝓝 (a₂ * cuspValue P hRep d + c)) :=
      (tendsto_const_nhds.mul (tendsto_primitive_cusp P hRep d D hD)).add tendsto_const_nhds
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards with z
    simpa only [ofComplex_apply] using (hc ((D • z : ℍ) : ℂ) (D • z : ℍ).im_pos).symm
  have ha := endpoint a A hA u hu
  have hb := endpoint b B hB v hv
  simp only [relativePeriod, Finset.sum_sub_distrib, mul_sub]
  rw [ha, hb]
  ring

/-- A weight-two invariant gives the same period between the transformed
endpoints. -/
theorem relativePeriod_eq_of_slash_eq
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (f : ℍ → ℂ) (P : ℂ → ℂ)
    (hP : ∀ τ : ℍ, HasDerivAt P (f τ) τ)
    (hslash : ∀ τ : ℍ, (f ∣[(2 : ℤ)] g) τ = f τ)
    (hRep : ∀ c : OnePoint ℚ, ∃ L : ℂ,
      Tendsto (fun z : ℍ => P ((mapGL ℝ (rep c) • z : ℍ) : ℂ)) atImInfty (𝓝 L))
    (a b : OnePoint ℚ) (A B : GL (Fin 2) ℝ)
    (hA : cuspInf A = OnePoint.map Rat.cast a)
    (hB : cuspInf B = OnePoint.map Rat.cast b)
    (u v : OnePoint ℚ)
    (hu : cuspInf (g * A) = OnePoint.map Rat.cast u)
    (hv : cuspInf (g * B) = OnePoint.map Rat.cast v) :
    relativePeriod P hRep u v = relativePeriod P hRep a b := by
  have h := relativePeriod_sum_of_slash (Finset.univ : Finset Unit)
    (fun _ => g) (by simpa using hg) f P 1 hP
    (by intro τ; simpa using hslash τ) hRep a b A B hA hB
    (fun _ => u) (fun _ => v) (by simpa using hu) (by simpa using hv)
  simpa using h

end BSD.General
