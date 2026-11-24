import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.ModularForms.QExpansion

/-! Transfer of an upper-half-plane limit between holomorphic primitives.
The existence of a convergent primitive is a separate analytic input. -/

open Filter Set UpperHalfPlane
open scoped Topology

namespace BSD.General.PeriodsLimit

/-- Two complex functions with equal derivatives on the upper half-plane differ
by a constant there. -/
theorem primitives_differ_by_constant (P Q f : ℂ → ℂ)
    (hP : ∀ z : ℂ, 0 < z.im → HasDerivAt P (f z) z)
    (hQ : ∀ z : ℂ, 0 < z.im → HasDerivAt Q (f z) z) :
    ∃ c : ℂ, ∀ z : ℂ, 0 < z.im → P z = Q z + c := by
  have ho : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hc : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨c, hc⟩ := ho.exists_eq_add_of_deriv_eq hc
    (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hP z hz).deriv.trans (hQ z hz).deriv.symm)
  exact ⟨c, fun z hz => hc hz⟩

/-- A limit at imaginary infinity transfers to any other primitive. -/
theorem tendsto_primitive_of_tendsto (P Q f : ℂ → ℂ)
    (hP : ∀ z : ℂ, 0 < z.im → HasDerivAt P (f z) z)
    (hQ : ∀ z : ℂ, 0 < z.im → HasDerivAt Q (f z) z)
    {L : ℂ} (hL : Tendsto (fun z : ℍ => Q z) atImInfty (𝓝 L)) :
    ∃ L' : ℂ, Tendsto (fun z : ℍ => P z) atImInfty (𝓝 L') := by
  obtain ⟨c, hc⟩ := primitives_differ_by_constant P Q f hP hQ
  refine ⟨L + c, ?_⟩
  have ht : Tendsto (fun z : ℍ => Q z + c) atImInfty (𝓝 (L + c)) :=
    hL.add tendsto_const_nhds
  apply ht.congr'
  filter_upwards with z
  exact (hc z z.im_pos).symm

end BSD.General.PeriodsLimit
