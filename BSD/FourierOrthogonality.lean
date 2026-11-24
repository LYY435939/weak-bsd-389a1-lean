import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Recover Fourier coefficients from an absolutely convergent expansion on a horizontal line. -/

open MeasureTheory

namespace BSD.FermatCubic

/-- Analytic Fourier orthogonality identifies the coefficients of a pointwise expansion
with summable coefficient norms. -/
theorem fourierCoeffOn_of_hasSum_fourier {f : ℝ → ℂ} {c : ℕ → ℂ}
    (hc : Summable fun n ↦ ‖c n‖)
    (h : ∀ x : ℝ, HasSum (fun n : ℕ ↦ c n * fourier (n : ℤ) (x : AddCircle (1 : ℝ))) (f x))
    (n : ℕ) : fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) f (n : ℤ) = c n := by
  classical
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let F (m : ℕ) (x : ℝ) :=
    fourier (-(n : ℤ)) (x : AddCircle (1 : ℝ)) * (c m * fourier (m : ℤ) (x : AddCircle (1 : ℝ)))
  have hcont (m : ℕ) : Continuous (F m) :=
    ((map_continuous (fourier (-(n : ℤ)))).comp (AddCircle.continuous_mk' _)).mul
      (continuous_const.mul ((map_continuous (fourier (m : ℤ))).comp
        (AddCircle.continuous_mk' _)))
  have hnorm (m : ℕ) (x : ℝ) : ‖F m x‖ = ‖c m‖ := by
    simp only [F, norm_mul, fourier_apply, Circle.norm_coe, one_mul, mul_one]
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (F := F)
    (f := fun x ↦ fourier (-(n : ℤ)) (x : AddCircle (1 : ℝ)) * f x)
    (fun m _ ↦ ‖c m‖) (fun m ↦ (hcont m).aestronglyMeasurable)
    (fun m ↦ ae_of_all _ fun x _ ↦ (hnorm m x).le)
    (ae_of_all _ fun _ _ ↦ hc) intervalIntegrable_const
    (ae_of_all _ fun x _ ↦ (h x).mul_left _)
  have hterm (m : ℕ) : (∫ x in (0 : ℝ)..1, F m x) = if n = m then c n else 0 := by
    have he := fourierCoeff_eq_intervalIntegral
      (fun z : AddCircle (1 : ℝ) ↦ c m * fourier (m : ℤ) z) (n : ℤ) 0
    simp only [one_div, inv_one, zero_add, one_smul, smul_eq_mul] at he
    rw [← he, fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply]
    by_cases hnm : n = m
    · subst m
      simp
    · have hcast : (n : ℤ) ≠ (m : ℤ) := by exact_mod_cast hnm
      simp [hnm, hcast]
  rw [fourierCoeffOn_eq_integral, sub_zero, one_div, inv_one, one_smul]
  simp only [smul_eq_mul]
  rw [← hint.tsum_eq]
  simp_rw [hterm]
  rw [tsum_eq_single n (fun m hm ↦ if_neg (Ne.symm hm))]
  simp

end BSD.FermatCubic
