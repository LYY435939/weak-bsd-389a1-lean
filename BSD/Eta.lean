import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The real Mellin integral of the eta product η(3z)²η(9z)² at s = 1. -/

open Set Filter MeasureTheory
open scoped Real Topology BigOperators

namespace BSD.FermatCubic

lemma qParam_axis (h u : ℝ) :
    Function.Periodic.qParam h ((u : ℂ) * Complex.I) =
      (Real.exp (-2 * Real.pi * u / h) : ℂ) := by
  rw [Function.Periodic.qParam, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (↑u * Complex.I) =
    2 * ↑Real.pi * ↑u * (Complex.I * Complex.I) by ring, Complex.I_mul_I]
  ring

private lemma axis_mem {u : ℝ} (hu : 0 < u) :
    (u : ℂ) * Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet := by
  change 0 < ((u : ℂ) * Complex.I).im
  simpa using hu

/-- On the positive imaginary axis, eta is real, positive, and bounded by its
leading exponential factor. -/
theorem eta_axis_bounds {u : ℝ} (hu : 0 < u) :
    ∃ r : ℝ, ModularForm.eta ((u : ℂ) * Complex.I) = r ∧
      0 < r ∧ r ≤ Real.exp (-2 * Real.pi * u / 24) := by
  let q := Real.exp (-2 * Real.pi * u)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hu])
  let f (n : ℕ) := 1 - q ^ (n + 1)
  have hf0 (n : ℕ) : 0 ≤ f n := sub_nonneg.mpr (pow_le_one₀ hq0.le hq1.le)
  have hf1 (n : ℕ) : f n ≤ 1 := sub_le_self _ (pow_nonneg hq0.le _)
  have hq (n : ℕ) : 1 - ModularForm.eta_q n ((u : ℂ) * Complex.I) = (f n : ℂ) := by
    simp [ModularForm.eta_q, qParam_axis, f, q]
  have hc : Multipliable (fun n : ℕ ↦ 1 - ModularForm.eta_q n ((u : ℂ) * Complex.I)) := by
    apply ModularForm.multipliable_one_sub_pow
    rw [qParam_axis]
    rw [div_one, Complex.norm_real, Real.norm_of_nonneg hq0.le]
    exact hq1
  have hc' := hc.hasProd
  simp_rw [hq] at hc'
  have hmem : (∏' n : ℕ, (f n : ℂ)) ∈
      (Complex.ofReal '' Icc (0 : ℝ) 1) := by
    apply (isCompact_Icc.image Complex.continuous_ofReal).isClosed.mem_of_tendsto hc'
    apply Eventually.of_forall
    intro s
    refine ⟨∏ i ∈ s, f i, ⟨Finset.prod_nonneg (fun i _ ↦ hf0 i),
      Finset.prod_le_one (fun i _ ↦ hf0 i) (fun i _ ↦ hf1 i)⟩, ?_⟩
    simp
  obtain ⟨p, hp, hprod⟩ := hmem
  let a := Real.exp (-2 * Real.pi * u / 24)
  have ha : 0 < a := Real.exp_pos _
  have heq : ModularForm.eta ((u : ℂ) * Complex.I) = (↑(a * p) : ℂ) := by
    simp only [ModularForm.eta, qParam_axis, hq, ← hprod, Complex.ofReal_mul]
    rfl
  refine ⟨a * p, heq, ?_, by change a * p ≤ a; simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2 ha.le⟩
  have hne := ModularForm.eta_ne_zero (axis_mem hu)
  rw [heq, Complex.ofReal_ne_zero] at hne
  exact lt_of_le_of_ne (mul_nonneg ha.le hp.1) hne.symm

/-- The eta product evaluated at z = it. -/
noncomputable def etaProductAxis (t : ℝ) : ℂ :=
  ModularForm.eta (((3 * t : ℝ) : ℂ) * Complex.I) ^ 2 *
    ModularForm.eta (((9 * t : ℝ) : ℂ) * Complex.I) ^ 2

theorem etaProductAxis_bounds {t : ℝ} (ht : 0 < t) :
    (etaProductAxis t).im = 0 ∧ 0 < (etaProductAxis t).re ∧
      (etaProductAxis t).re ≤ Real.exp ((-2 * Real.pi) * t) := by
  obtain ⟨a, ha, ha0, ha1⟩ := eta_axis_bounds (u := 3*t) (by positivity)
  obtain ⟨b, hb, hb0, hb1⟩ := eta_axis_bounds (u := 9*t) (by positivity)
  have he : etaProductAxis t = ((a^2 * b^2 : ℝ) : ℂ) := by
    rw [etaProductAxis, ha, hb, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
  rw [he, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, by positivity, ?_⟩
  calc
    a^2 * b^2 ≤ Real.exp (-2 * Real.pi * (3*t) / 24)^2 *
      Real.exp (-2 * Real.pi * (9*t) / 24)^2 :=
        mul_le_mul (pow_le_pow_left₀ ha0.le ha1 2) (pow_le_pow_left₀ hb0.le hb1 2)
          (sq_nonneg _) (sq_nonneg _)
    _ = _ := by rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma etaAxis_continuousOn {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun t : ℝ ↦ ModularForm.eta (((c*t : ℝ) : ℂ) * Complex.I)) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
    (axis_mem (mul_pos hc ht))).continuousAt.comp (f := fun x : ℝ ↦ ((c*x : ℝ) : ℂ) * Complex.I)
      (by fun_prop : ContinuousAt (fun x : ℝ ↦ ((c*x : ℝ) : ℂ) * Complex.I) t)

theorem etaProductAxis_integrableOn :
    IntegrableOn (fun t ↦ (etaProductAxis t).re) (Ioi 0) := by
  have hcont : ContinuousOn (fun t ↦ (etaProductAxis t).re) (Ioi 0) :=
    Complex.continuous_re.comp_continuousOn (((etaAxis_continuousOn (c := 3) (by norm_num)).pow 2).mul
      ((etaAxis_continuousOn (c := 9) (by norm_num)).pow 2))
  apply (integrableOn_exp_mul_Ioi (a := -2 * Real.pi) (by linarith [Real.pi_pos]) 0).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (etaProductAxis_bounds ht).2.1.le]
  exact (etaProductAxis_bounds ht).2.2

private theorem etaProductAxis_real_ae :
    etaProductAxis =ᵐ[volume.restrict (Ioi 0)] (fun t ↦ ((etaProductAxis t).re : ℂ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply Complex.ext
  · rfl
  · exact (etaProductAxis_bounds ht).1

theorem etaProductAxis_complex_integrableOn : IntegrableOn etaProductAxis (Ioi 0) :=
  (etaProductAxis_integrableOn.ofReal).congr etaProductAxis_real_ae.symm

/-- The Mellin integral at s = 1, with the classical 2π normalization. -/
noncomputable def etaCentralMellin : ℝ := 2 * Real.pi * ∫ t in Ioi 0, (etaProductAxis t).re

theorem etaCentralMellin_pos : 0 < etaCentralMellin := by
  apply mul_pos (by positivity : 0 < 2 * Real.pi)
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ etaProductAxis_integrableOn).2
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun t ↦ (etaProductAxis t).re) := by
      intro t ht
      exact (etaProductAxis_bounds ht).2.1.ne'
    rw [inter_eq_self_of_subset_right hsub, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (etaProductAxis_bounds ht).2.1.le

/-- The complex Mellin integral is exactly the real value above. -/
theorem etaProductAxis_mellin_eq :
    (2 * (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ), etaProductAxis t = (etaCentralMellin : ℂ) := by
  have he : ∫ t in Ioi (0 : ℝ), etaProductAxis t =
      ∫ t in Ioi (0 : ℝ), ((etaProductAxis t).re : ℂ) :=
    integral_congr_ae etaProductAxis_real_ae
  have hi : (∫ t in Ioi (0 : ℝ), ((etaProductAxis t).re : ℂ)) =
      ↑(∫ t in Ioi (0 : ℝ), (etaProductAxis t).re) := integral_complex_ofReal
  rw [he, hi, etaCentralMellin]
  push_cast
  rfl

end BSD.FermatCubic
