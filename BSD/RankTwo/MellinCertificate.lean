import BSD.RankTwo.MellinKernel
import BSD.RankTwo.CoefficientData

/-!
# A rational certificate for the second central Mellin moment at conductor 389

The inputs are the coefficients through degree 17 and the coarse global bound
`|a n| ≤ n²`. The logarithmic integral and the entire infinite remainder are
bounded in Lean.
-/

namespace BSD.RankTwo

private theorem mellinTerm_bound (a : ℕ → ℝ) (hb : ∀ n : ℕ, |a n| ≤ (n:ℝ)^2)
    {n : ℕ} (hn : 0 < n) : ‖a n * mellinKernel n‖ ≤ (15/2 : ℝ) * 0.73^n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinKernel_nonneg n)]
  calc
    _ ≤ (n:ℝ)^2 * ((15/2)*(0.73:ℝ)^n / (n:ℝ)^2) :=
      mul_le_mul (hb n) (mellinKernel_upper hn) (mellinKernel_nonneg n) (sq_nonneg _)
    _ = _ := by field_simp

theorem summable_mellinMoment (a : ℕ → ℝ) (hb : ∀ n : ℕ, |a n| ≤ (n:ℝ)^2) :
    Summable (fun n ↦ a n * mellinKernel n) := by
  apply Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ ↦ (15/2:ℝ)*0.73^n)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (0.73:ℝ) < 1)).mul_left _)
  exact Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ mellinTerm_bound a hb hn⟩

/-- The bound applies after every positive cutoff. -/
theorem mellinMoment_tail (a : ℕ → ℝ) (hb : ∀ n : ℕ, |a n| ≤ (n:ℝ)^2)
    {N : ℕ} (hN : 0 < N) : |∑' k : ℕ, a (k+N)*mellinKernel (k+N)| ≤
    (15/2:ℝ)*(0.73:ℝ)^N / (1-0.73) := by
  have hbound (k : ℕ) : ‖a (k+N) * mellinKernel (k+N)‖ ≤
      ((15/2:ℝ)*(0.73:ℝ)^N) * (0.73:ℝ)^k := by
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using mellinTerm_bound a hb (n := k+N) (by omega)
  have hg := (summable_geometric_of_lt_one (by norm_num) (by norm_num : (0.73:ℝ)<1)).mul_left
    ((15/2:ℝ)*(0.73:ℝ)^N)
  have hn : Summable (fun k : ℕ ↦ ‖a (k+N)*mellinKernel (k+N)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound hg
  calc
    _ ≤ ∑' k : ℕ, ‖a (k+N)*mellinKernel (k+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := hn.tsum_mono hg hbound
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

/-- Only the nine negative coefficients in the finite prefix require individual
upper estimates. Dropping all further positive contributions gives a lower bound. -/
theorem mellinMoment_prefix (a : ℕ → ℝ) (ha : ∀ i : Fin 18, a i = firstCoefficients i) :
    (0.16:ℝ) < ∑ n ∈ Finset.range 18, a n * mellinKernel n := by
  have h0 : a 0 = 0 := by simpa [firstCoefficients] using ha (0 : Fin 18)
  have h1 : a 1 = 1 := by simpa [firstCoefficients] using ha (1 : Fin 18)
  have h2 : a 2 = -2 := by simpa [firstCoefficients] using ha (2 : Fin 18)
  have h3 : a 3 = -2 := by simpa [firstCoefficients] using ha (3 : Fin 18)
  have h4 : a 4 = 2 := by simpa [firstCoefficients] using ha (4 : Fin 18)
  have h5 : a 5 = -3 := by simpa [firstCoefficients] using ha (5 : Fin 18)
  have h6 : a 6 = 4 := by simpa [firstCoefficients] using ha (6 : Fin 18)
  have h7 : a 7 = -5 := by simpa [firstCoefficients] using ha (7 : Fin 18)
  have h8 : a 8 = 0 := by simpa [firstCoefficients] using ha (8 : Fin 18)
  have h9 : a 9 = 1 := by simpa [firstCoefficients] using ha (9 : Fin 18)
  have h10 : a 10 = 6 := by simpa [firstCoefficients] using ha (10 : Fin 18)
  have h11 : a 11 = -4 := by simpa [firstCoefficients] using ha (11 : Fin 18)
  have h12 : a 12 = -4 := by simpa [firstCoefficients] using ha (12 : Fin 18)
  have h13 : a 13 = -3 := by simpa [firstCoefficients] using ha (13 : Fin 18)
  have h14 : a 14 = 10 := by simpa [firstCoefficients] using ha (14 : Fin 18)
  have h15 : a 15 = 6 := by simpa [firstCoefficients] using ha (15 : Fin 18)
  have h16 : a 16 = -4 := by simpa [firstCoefficients] using ha (16 : Fin 18)
  have h17 : a 17 = -6 := by simpa [firstCoefficients] using ha (17 : Fin 18)
  have hu2 := mellinKernel_upper (by decide : 0 < 2)
  have hu3 := mellinKernel_upper (by decide : 0 < 3)
  have hu5 := mellinKernel_upper (by decide : 0 < 5)
  have hu7 := mellinKernel_upper (by decide : 0 < 7)
  have hu11 := mellinKernel_upper (by decide : 0 < 11)
  have hu12 := mellinKernel_upper (by decide : 0 < 12)
  have hu13 := mellinKernel_upper (by decide : 0 < 13)
  have hu16 := mellinKernel_upper (by decide : 0 < 16)
  have hu17 := mellinKernel_upper (by decide : 0 < 17)
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  norm_num at hu2 hu3 hu5 hu7 hu11 hu12 hu13 hu16 hu17
  linarith [mellinKernel_one_lower, mellinKernel_nonneg 4, mellinKernel_nonneg 6, mellinKernel_nonneg 9, mellinKernel_nonneg 10, mellinKernel_nonneg 14, mellinKernel_nonneg 15]

/-- For the certified 389.a1 Fourier prefix, the remaining coefficients cannot
cancel the second logarithmic moment. -/
theorem mellinMoment_lower (a : ℕ → ℝ) (ha : ∀ i : Fin 18, a i = firstCoefficients i)
    (hb : ∀ n : ℕ, |a n| ≤ (n:ℝ)^2) :
    (0.06:ℝ) < ∑' n : ℕ, a n * mellinKernel n := by
  rw [← (summable_mellinMoment a hb).sum_add_tsum_nat_add 18]
  have tail := mellinMoment_tail a hb (by decide : 0 < 18)
  have lower := (abs_le.mp tail).1
  norm_num at lower
  linarith [mellinMoment_prefix a ha]

end BSD.RankTwo
