import BSD.RankTwo.CuspConvergence
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.Convex

/-! # The entire modular L-function on the half-plane of absolute convergence -/

open Filter UpperHalfPlane
open scoped Topology MatrixGroups CongruenceSubgroup

namespace BSD.General

/-- The entire L-function of any level-positive weight-two cusp form is represented by
its width-one Fourier series throughout the half-plane of absolute convergence. -/
theorem gamma0_L_eq_LSeries {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {s : ℂ} (hs : 3 / 2 < s.re) :
    ModularForm.L (by decide : (0 : ℤ) < 2) f s =
      LSeries (fun n ↦ (qExpansion 1 f).coeff n) s := by
  let a : ℕ → ℂ := fun n ↦ (qExpansion 1 f).coeff n
  let U : Set ℂ := {z | 3 / 2 < z.re}
  have hb : LSeries.abscissaOfAbsConv a ≤ ((3 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hx ↦
      gamma0_weightTwo_LSeriesSummable f (by simpa using hx)
  have ha : AnalyticOnNhd ℂ (LSeries a) U :=
    (LSeries_analyticOnNhd a).mono fun z hz ↦ hb.trans_lt (by exact_mod_cast hz : (↑(3 / 2 : ℝ) : EReal) < ↑z.re)
  have hf : AnalyticOnNhd ℂ (ModularForm.L (by decide : (0 : ℤ) < 2) f) U :=
    fun z _ ↦ (CuspForm.differentiable_L (by decide : (0 : ℤ) < 2) f).analyticAt z
  have h₃ : (3 : ℂ) ∈ U := by norm_num [U]
  apply hf.eqOn_of_preconnected_of_eventuallyEq ha
    (convex_halfSpace_re_gt (3 / 2)).isPreconnected h₃ _ hs
  have hn : {z : ℂ | 2 < z.re} ∈ 𝓝 (3 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hn] with z hz
  have hz' : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have h := CuspForm.hasSum_L (by decide : (0 : ℤ) < 2) f (s := z) (by
    norm_num
    exact hz)
  simpa [LSeries, LSeries.term_of_ne_zero' hz', a] using h.tsum_eq.symm

end BSD.General
