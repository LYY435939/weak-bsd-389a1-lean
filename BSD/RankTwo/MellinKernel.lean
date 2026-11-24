import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The logarithmic square moment for the weight-two Fricke transform at level 389. -/
open MeasureTheory Set Filter
open scoped Real Topology

namespace BSD.RankTwo

noncomputable def mellinRate : ℝ := 2 * Real.pi / Real.sqrt 389

theorem mellinRate_bounds : 0.318 < mellinRate ∧ mellinRate < 0.32 := by
  have hs : 0 < Real.sqrt 389 := by positivity
  have hd := Real.sq_sqrt (show (0:ℝ) ≤ 389 by norm_num)
  have h₁ : Real.sqrt 389 < 19.74 := by nlinarith
  have h₂ : 19.7 < Real.sqrt 389 := by nlinarith
  constructor
  · apply (lt_div_iff₀ hs).2
    nlinarith [Real.pi_gt_d2]
  · apply (div_lt_iff₀ hs).2
    linarith [Real.pi_lt_d2]

theorem mellinNome_bounds : 0.72 ≤ Real.exp (-mellinRate) ∧ Real.exp (-mellinRate) ≤ 0.73 := by
  constructor
  · have h := Real.add_one_le_exp (-(0.32 / 16))
    have h' := pow_le_pow_left₀ (by norm_num : 0 ≤ -(0.32 / 16 : ℝ) + 1) h 16
    rw [← Real.exp_nat_mul] at h'
    norm_num at h'
    exact le_trans (by norm_num) (h'.trans (Real.exp_le_exp.mpr (by linarith [mellinRate_bounds.2])))
  · rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    have he := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (0.318 : ℝ)) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at he
    nlinarith [Real.exp_le_exp.mpr mellinRate_bounds.1.le]

noncomputable def mellinKernel (n : ℕ) : ℝ :=
  ∫ t in Ioi (1 : ℝ), Real.exp (-(mellinRate * n) * t) * Real.log t ^ 2

theorem mellinKernel_nonneg (n : ℕ) : 0 ≤ mellinKernel n :=
  integral_nonneg fun _ ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

private lemma log_sq_bound {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 ≤ (3/4)*(t-1) := by
  let x := Real.log t
  have hx : 0 ≤ x := Real.log_nonneg ht
  have he := Real.sum_le_exp_of_nonneg hx 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  rw [show Real.exp x = t from Real.exp_log (by linarith)] at he
  change x^2 ≤ _
  by_cases h₁ : x ≤ 1
  · nlinarith [mul_nonneg hx (sub_nonneg.mpr h₁), mul_nonneg hx (sq_nonneg x), sq_nonneg (x^2)]
  · have h₂ : 0 ≤ x*(x-5/2)^2 := mul_nonneg hx (sq_nonneg _)
    have h₃ : x ≤ x^4 := by
      simpa using (pow_le_pow_right₀ (by linarith : 1 ≤ x) (by decide : 1 ≤ 4))
    nlinarith

private lemma firstMoment_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ t * Real.exp (-r*t)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1:ℝ)) (p := (1:ℝ)) (b := r) (by norm_num) (by norm_num) hr

private lemma shiftedMoment_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ (t-1) * Real.exp (-r*t)) (Ioi 1) := by
  have h := (firstMoment_integrable hr).mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  simpa [sub_mul, Pi.sub_def] using h.sub (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hr) 1)

private lemma shiftedMoment_integral {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (1:ℝ), (t-1) * Real.exp (-r*t) = Real.exp (-r)/r^2 := by
  let e := MeasurableEquiv.addRight (1:ℝ)
  have hpre : e ⁻¹' Ioi 1 = Ioi 0 := by ext x; change (1 < x+1) ↔ 0<x; constructor <;> intro h <;> linarith
  have he := (measurePreserving_add_right volume (1:ℝ)).setIntegral_preimage_emb
    e.measurableEmbedding (fun t : ℝ ↦ (t-1)*Real.exp (-r*t)) (Ioi 1)
  change (∫ x in e ⁻¹' Ioi 1, (x+1-1)*Real.exp (-r*(x+1))) = _ at he
  rw [hpre] at he
  rw [← he]
  simp_rw [add_sub_cancel_right, mul_add, mul_one, Real.exp_add, ← mul_assoc, integral_mul_const]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  norm_num [show (2:ℝ) = (1:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial] at hi
  simp_rw [neg_mul] at *
  rw [hi]
  ring

theorem mellinKernel_integrable {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(mellinRate * n) * t) * Real.log t ^ 2) (Ioi 1) := by
  have hr : 0 < mellinRate * n := mul_pos (by linarith [mellinRate_bounds.1]) (by positivity)
  apply ((shiftedMoment_integrable hr).const_mul (3/4 : ℝ)).mono'
  · exact (by fun_prop : Measurable (fun t : ℝ ↦ Real.exp (-(mellinRate*n)*t) * Real.log t^2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    nlinarith [mul_nonneg (Real.exp_pos (-(mellinRate*n)*t)).le (sub_nonneg.mpr (log_sq_bound ht.le))]

theorem mellinKernel_upper {n : ℕ} (hn : 0 < n) :
    mellinKernel n ≤ (15/2 : ℝ) * (0.73 : ℝ)^n / (n : ℝ)^2 := by
  let r := mellinRate*n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := mul_pos (by linarith [mellinRate_bounds.1]) hn'
  have h : mellinKernel n ≤ ∫ t in Ioi (1:ℝ), (3/4) * ((t-1)*Real.exp (-r*t)) := by
    apply integral_mono_ae (mellinKernel_integrable hn) ((shiftedMoment_integrable hr).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change Real.exp (-r*t) * Real.log t^2 ≤ _
    nlinarith [mul_nonneg (Real.exp_pos (-r*t)).le (sub_nonneg.mpr (log_sq_bound ht.le))]
  rw [integral_const_mul, shiftedMoment_integral hr] at h
  have hexp : Real.exp (-r) ≤ (0.73 : ℝ)^n := by
    rw [show -r = (n:ℝ)*(-mellinRate) by dsimp [r]; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le mellinNome_bounds.2 _
  have hc : (3/4 : ℝ) ≤ 15/2*mellinRate^2 := by nlinarith [mellinRate_bounds.1]
  apply h.trans
  rw [mul_div_assoc', div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos hn')]
  dsimp [r]
  nlinarith only [mul_nonneg (sq_nonneg (n:ℝ)) (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 0.73) n) (sub_nonneg.mpr hc)),
    mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr hexp)]


private noncomputable def step (k : ℕ) (d t : ℝ) : ℝ :=
  (Ioi (k:ℝ)).indicator (fun x ↦ d * Real.exp (-mellinRate*x)) t

private lemma step_integrable (k : ℕ) (d : ℝ) : IntegrableOn (step k d) (Ioi 1) := by
  apply (integrableOn_indicator_iff measurableSet_Ioi).mpr
  apply IntegrableOn.mono_set (t := Ioi (k:ℝ))
  · exact (integrableOn_exp_mul_Ioi (by linarith [mellinRate_bounds.1] : -mellinRate<0) (k:ℝ)).const_mul d
  · exact inter_subset_left

private lemma step_integral {k : ℕ} (hk : 1 ≤ k) {d : ℝ} (hd : 0 ≤ d) :
    d * (0.72:ℝ)^k / 0.32 ≤ ∫ t in Ioi (1:ℝ), step k d t := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 < mellinRate := by linarith [mellinRate_bounds.1]
  change _ ≤ ∫ t in Ioi (1:ℝ), (Ioi (k:ℝ)).indicator (fun x ↦ d * Real.exp (-mellinRate*x)) t
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hk'),
    integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hc), neg_div_neg_eq]
  rw [show -mellinRate * (k:ℝ) = (k:ℝ) * (-mellinRate) by ring, Real.exp_nat_mul, ← mul_div_assoc]
  exact div_le_div₀ (mul_nonneg hd (pow_nonneg (Real.exp_pos _).le _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) mellinNome_bounds.1 _) hd)
    hc mellinRate_bounds.2.le

private lemma log_levels :
    (0.69:ℝ) ≤ Real.log 2 ∧ (1.09:ℝ) ≤ Real.log 3 ∧ (1.38:ℝ) ≤ Real.log 4 ∧
    (1.78:ℝ) ≤ Real.log 6 ∧ (2.07:ℝ) ≤ Real.log 8 ∧ (2.47:ℝ) ≤ Real.log 12 := by
  have hl4 := Real.log_pow (2:ℝ) 2
  have hl8 := Real.log_pow 2 (3:ℕ)
  have hl6 := Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
  have hl12 := Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
  norm_num at hl4 hl8 hl6 hl12
  constructor <;> repeat' constructor
  all_goals linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private lemma step_sum_le {t : ℝ} :
    step 2 0.4761 t + step 3 0.7120 t + step 4 0.7163 t + step 6 1.2640 t + step 8 1.1165 t + step 12 1.8160 t ≤
      Real.exp (-mellinRate*t)*Real.log t^2 := by
  obtain ⟨h2,h3,h4,h6,h8,h12⟩ := log_levels
  by_cases ht12 : (12:ℝ) < t
  · have hy := (h12.trans (Real.log_le_log (by norm_num) ht12.le))
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.47) hy 2
    simp only [step, Set.indicator, Set.mem_Ioi, Nat.cast_ofNat]
    rw [if_pos (by linarith : (2:ℝ) < t)]
    rw [if_pos (by linarith : (3:ℝ) < t)]
    rw [if_pos (by linarith : (4:ℝ) < t)]
    rw [if_pos (by linarith : (6:ℝ) < t)]
    rw [if_pos (by linarith : (8:ℝ) < t)]
    rw [if_pos ht12]
    nlinarith only [mul_nonneg (Real.exp_pos (-mellinRate*t)).le (sub_nonneg.mpr hs)]
  by_cases ht8 : (8:ℝ) < t
  · have hy := (h8.trans (Real.log_le_log (by norm_num) ht8.le))
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.07) hy 2
    simp only [step, Set.indicator, Set.mem_Ioi, Nat.cast_ofNat]
    rw [if_pos (by linarith : (2:ℝ) < t)]
    rw [if_pos (by linarith : (3:ℝ) < t)]
    rw [if_pos (by linarith : (4:ℝ) < t)]
    rw [if_pos (by linarith : (6:ℝ) < t)]
    rw [if_pos ht8]
    rw [if_neg ht12]
    nlinarith only [mul_nonneg (Real.exp_pos (-mellinRate*t)).le (sub_nonneg.mpr hs)]
  by_cases ht6 : (6:ℝ) < t
  · have hy := (h6.trans (Real.log_le_log (by norm_num) ht6.le))
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.78) hy 2
    simp only [step, Set.indicator, Set.mem_Ioi, Nat.cast_ofNat]
    rw [if_pos (by linarith : (2:ℝ) < t)]
    rw [if_pos (by linarith : (3:ℝ) < t)]
    rw [if_pos (by linarith : (4:ℝ) < t)]
    rw [if_pos ht6]
    rw [if_neg ht8]
    rw [if_neg ht12]
    nlinarith only [mul_nonneg (Real.exp_pos (-mellinRate*t)).le (sub_nonneg.mpr hs)]
  by_cases ht4 : (4:ℝ) < t
  · have hy := (h4.trans (Real.log_le_log (by norm_num) ht4.le))
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.38) hy 2
    simp only [step, Set.indicator, Set.mem_Ioi, Nat.cast_ofNat]
    rw [if_pos (by linarith : (2:ℝ) < t)]
    rw [if_pos (by linarith : (3:ℝ) < t)]
    rw [if_pos ht4]
    rw [if_neg ht6]
    rw [if_neg ht8]
    rw [if_neg ht12]
    nlinarith only [mul_nonneg (Real.exp_pos (-mellinRate*t)).le (sub_nonneg.mpr hs)]
  by_cases ht3 : (3:ℝ) < t
  · have hy := (h3.trans (Real.log_le_log (by norm_num) ht3.le))
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.09) hy 2
    simp only [step, Set.indicator, Set.mem_Ioi, Nat.cast_ofNat]
    rw [if_pos (by linarith : (2:ℝ) < t)]
    rw [if_pos ht3]
    rw [if_neg ht4]
    rw [if_neg ht6]
    rw [if_neg ht8]
    rw [if_neg ht12]
    nlinarith only [mul_nonneg (Real.exp_pos (-mellinRate*t)).le (sub_nonneg.mpr hs)]
  by_cases ht2 : (2:ℝ) < t
  · have hy := (h2.trans (Real.log_le_log (by norm_num) ht2.le))
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.69) hy 2
    simp only [step, Set.indicator, Set.mem_Ioi, Nat.cast_ofNat]
    rw [if_pos ht2]
    rw [if_neg ht3]
    rw [if_neg ht4]
    rw [if_neg ht6]
    rw [if_neg ht8]
    rw [if_neg ht12]
    nlinarith only [mul_nonneg (Real.exp_pos (-mellinRate*t)).le (sub_nonneg.mpr hs)]
  simp [step, Set.indicator, ht2, ht3, ht4, ht6, ht8, ht12, mul_nonneg (Real.exp_pos _).le (sq_nonneg _)]


/-- A rational lower enclosure for the first Fourier kernel, obtained with
six nested half-lines and rational lower bounds for log 2 and log 3. -/
theorem mellinKernel_one_lower : (3.1:ℝ) < mellinKernel 1 := by
  have hp : ∀ᵐ t ∂volume.restrict (Ioi (1:ℝ)),
    step 2 0.4761 t + step 3 0.7120 t + step 4 0.7163 t + step 6 1.2640 t + step 8 1.1165 t + step 12 1.8160 t ≤ Real.exp (-mellinRate*t)*Real.log t^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using step_sum_le
  have hm := integral_mono_ae ((((((step_integrable 2 0.4761).add (step_integrable 3 0.7120)).add (step_integrable 4 0.7163)).add (step_integrable 6 1.2640)).add (step_integrable 8 1.1165)).add (step_integrable 12 1.8160))
    (by simpa only [IntegrableOn, Nat.cast_one, mul_one] using mellinKernel_integrable (by decide : 0 < 1)) hp
  rw [show mellinKernel 1 = ∫ t in Ioi (1:ℝ), Real.exp (-mellinRate*t)*Real.log t^2 by simp [mellinKernel]]
  rw [integral_add' (((((step_integrable 2 0.4761).add (step_integrable 3 0.7120)).add (step_integrable 4 0.7163)).add (step_integrable 6 1.2640)).add (step_integrable 8 1.1165)) (step_integrable 12 1.8160),
    integral_add' ((((step_integrable 2 0.4761).add (step_integrable 3 0.7120)).add (step_integrable 4 0.7163)).add (step_integrable 6 1.2640)) (step_integrable 8 1.1165),
    integral_add' (((step_integrable 2 0.4761).add (step_integrable 3 0.7120)).add (step_integrable 4 0.7163)) (step_integrable 6 1.2640),
    integral_add' ((step_integrable 2 0.4761).add (step_integrable 3 0.7120)) (step_integrable 4 0.7163),
    integral_add' (step_integrable 2 0.4761) (step_integrable 3 0.7120)] at hm
  have h2 := step_integral (by decide : 1 ≤ 2) (by norm_num : (0:ℝ) ≤ 0.4761)
  have h3 := step_integral (by decide : 1 ≤ 3) (by norm_num : (0:ℝ) ≤ 0.7120)
  have h4 := step_integral (by decide : 1 ≤ 4) (by norm_num : (0:ℝ) ≤ 0.7163)
  have h6 := step_integral (by decide : 1 ≤ 6) (by norm_num : (0:ℝ) ≤ 1.2640)
  have h8 := step_integral (by decide : 1 ≤ 8) (by norm_num : (0:ℝ) ≤ 1.1165)
  have h12 := step_integral (by decide : 1 ≤ 12) (by norm_num : (0:ℝ) ≤ 1.8160)
  norm_num at h2 h3 h4 h6 h8 h12
  linarith

end BSD.RankTwo
