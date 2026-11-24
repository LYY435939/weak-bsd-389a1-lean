import BSD.Eta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Meromorphic.Basic

/-! Entire Mellin transform of the eta product on the positive imaginary axis. -/

open Set Filter MeasureTheory Asymptotics
open scoped Topology Real BigOperators

namespace BSD.FermatCubic

private theorem eta_axis_norm_le_one {u : ℝ} (hu : 0 < u) :
    ‖ModularForm.eta ((u : ℂ) * Complex.I)‖ ≤ 1 := by
  obtain ⟨r, hr, hr0, hr1⟩ := eta_axis_bounds hu
  rw [hr, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  exact hr1.trans (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hu] : -2 * Real.pi * u / 24 ≤ 0))

/-- Keeping the first k Euler factors gives a bound of order u^k at the origin. -/
private theorem eta_axis_norm_le_pow (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖ModularForm.eta ((u : ℂ) * Complex.I)‖ ≤
      (∏ i ∈ Finset.range k, ((i+1 : ℕ) : ℝ) * (2 * Real.pi)) * u ^ k := by
  let z := (u : ℂ) * Complex.I
  let f (i : ℕ) := 1 - ModularForm.eta_q i z
  let q := Real.exp (-2 * Real.pi * u)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hu])
  have hf (i : ℕ) : ‖f i‖ = 1 - q ^ (i+1) := by
    have he : f i = ((1 - q^(i+1) : ℝ) : ℂ) := by
      simp [f, ModularForm.eta_q, z, qParam_axis, q]
    rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hq0.le hq1.le))]
  have hc : Multipliable f := by
    apply ModularForm.multipliable_one_sub_pow
    rw [show z = (u : ℂ) * Complex.I from rfl, qParam_axis, div_one, Complex.norm_real,
      Real.norm_of_nonneg hq0.le]
    exact hq1
  have hprod : ‖∏' i, f i‖ ≤ ∏ i ∈ Finset.range k, ‖f i‖ := by
    apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hc.hasProd)
    filter_upwards [eventually_ge_atTop (Finset.range k)] with t ht
    change ‖∏ i ∈ t, f i‖ ≤ _
    rw [norm_prod]
    exact Finset.prod_le_prod_of_subset_of_le_one ht (fun i _ ↦ norm_nonneg _)
      (fun i _ _ ↦ (hf i).le.trans (sub_le_self _ (pow_nonneg hq0.le _)))
  have hlead : ‖Function.Periodic.qParam 24 z‖ ≤ 1 := by
    rw [show z = (u : ℂ) * Complex.I from rfl, qParam_axis, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    nlinarith [mul_pos Real.pi_pos hu]
  calc
    ‖ModularForm.eta ((u : ℂ) * Complex.I)‖ = ‖Function.Periodic.qParam 24 z‖ * ‖∏' i, f i‖ :=
      norm_mul _ _
    _ ≤ ‖∏' i, f i‖ := mul_le_of_le_one_left (norm_nonneg _) hlead
    _ ≤ _ := hprod
    _ ≤ ∏ i ∈ Finset.range k, (((i+1 : ℕ) : ℝ) * (2 * Real.pi) * u) := by
      apply Finset.prod_le_prod (fun i _ ↦ norm_nonneg _)
      intro i _
      rw [hf, show q = Real.exp (-2 * Real.pi * u) from rfl, ← Real.exp_nat_mul]
      linarith only [Real.add_one_le_exp (((i+1 : ℕ) : ℝ) * (-2 * Real.pi * u))]
    _ = _ := by simp [Finset.prod_mul_distrib]

theorem etaProductAxis_isBigO_zero (k : ℕ) :
    etaProductAxis =O[𝓝[>] (0 : ℝ)] (fun t : ℝ ↦ t ^ (k : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound ((∏ i ∈ Finset.range k, ((i+1 : ℕ) : ℝ) * (2 * Real.pi)) *
    3 ^ k) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have h3 := eta_axis_norm_le_one (u := 3*t) (by positivity)
  have h9 := eta_axis_norm_le_one (u := 9*t) (by positivity)
  rw [etaProductAxis, norm_mul, norm_pow, norm_pow, Real.rpow_natCast,
    Real.norm_of_nonneg (pow_nonneg ht0.le _)]
  calc
    _ ≤ ‖ModularForm.eta ((↑(3*t) : ℂ) * Complex.I)‖ :=
      (mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) h9)).trans
        (by simpa [sq] using mul_le_of_le_one_right (norm_nonneg _) h3)
    _ ≤ _ := (eta_axis_norm_le_pow k (u := 3*t) (by positivity)).trans_eq (by rw [mul_pow, mul_assoc])

theorem etaProductAxis_isBigO_top :
    etaProductAxis =O[atTop] (fun t : ℝ ↦ Real.exp (-(2 * Real.pi) * t)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  obtain ⟨him, hpos, hle⟩ := etaProductAxis_bounds ht
  have he : etaProductAxis t = ((etaProductAxis t).re : ℂ) := Complex.ext rfl (by simpa using him)
  calc
    ‖etaProductAxis t‖ = (etaProductAxis t).re := by
      conv_lhs => rw [he, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    _ ≤ _ := by simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using hle

theorem etaProductAxis_mellinConvergent (s : ℂ) : MellinConvergent etaProductAxis s := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-s.re)
  apply mellinConvergent_of_isBigO_rpow_exp (a := 2 * Real.pi) (b := -(k : ℝ))
    (by positivity) etaProductAxis_complex_integrableOn.locallyIntegrableOn etaProductAxis_isBigO_top
  · simpa using etaProductAxis_isBigO_zero k
  · linarith

theorem differentiable_mellin_etaProductAxis : Differentiable ℂ (mellin etaProductAxis) := by
  intro s
  obtain ⟨k, hk⟩ := exists_nat_gt (-s.re)
  apply mellin_differentiableAt_of_isBigO_rpow_exp (a := 2 * Real.pi) (b := -(k : ℝ))
    (by positivity) etaProductAxis_complex_integrableOn.locallyIntegrableOn etaProductAxis_isBigO_top
  · simpa using etaProductAxis_isBigO_zero k
  · linarith

/-- The normalized Mellin transform of η(3it)²η(9it)². -/
noncomputable def etaL (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ s / Complex.Gamma s) * mellin etaProductAxis s

theorem differentiable_etaL : Differentiable ℂ etaL := by
  have h : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  intro s
  unfold etaL
  simp only [div_eq_mul_inv]
  exact ((differentiableAt_id.const_cpow (Or.inl h)).mul
    (Complex.differentiable_one_div_Gamma s)).mul (differentiable_mellin_etaProductAxis s)

theorem meromorphic_etaL (s : ℂ) : MeromorphicAt etaL s :=
  (differentiable_etaL.analyticAt s).meromorphicAt

theorem etaL_one : etaL 1 = (etaCentralMellin : ℂ) := by
  simpa [etaL, mellin] using etaProductAxis_mellin_eq

end BSD.FermatCubic
