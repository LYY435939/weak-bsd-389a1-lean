import BSD.FourierMellin
import BSD.RankTwo.MellinKernel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The second central derivative from a Fricke-symmetric Mellin integral

In weight two with functional-equation sign +1, use the scaled imaginary axis
`F(t) = f(it / √N)`. Its full Mellin integral is the gamma-completed
L-function in the normalization `(√N / (2π))^s Γ(s) L(s)`.
-/

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace BSD.RankTwo

/-- Restriction of the real axis function to the open upper half of the
Fricke pair, viewed as a complex-valued function. -/
noncomputable def upperMellinTail (F : ℝ → ℝ) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t ↦ (F t : ℂ))

private theorem upperMellinTail_zero (F : ℝ → ℝ) {t : ℝ} (ht : t ≤ 1) :
    upperMellinTail F t = 0 := by simp [upperMellinTail, not_lt.mpr ht]

private theorem locallyIntegrable_upperMellinTail {F : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi (0 : ℝ))) :
    LocallyIntegrableOn (upperMellinTail F) (Ioi 0) := by
  have hcont : ContinuousOn (fun t ↦ (F t : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn hF
  apply (hcont.locallyIntegrableOn measurableSet_Ioi).mono
  · unfold upperMellinTail
    have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
    exact (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr
      ((hcont.mono hsubset).aestronglyMeasurable measurableSet_Ioi)
  · apply ae_of_all
    intro t
    unfold upperMellinTail
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht]

private theorem isBigO_tail_zero {g : ℝ → ℂ} (hzero : ∀ t ≤ 1, g t = 0) (b : ℝ) :
    g =O[𝓝[>] (0 : ℝ)] (fun t : ℝ ↦ t ^ (-b)) := by
  apply IsBigO.of_bound 0
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))] with t ht
  simp [hzero t ht.le]

private theorem mellin_tail_convergent {g : ℝ → ℂ}
    (hlocal : LocallyIntegrableOn g (Ioi 0)) (hzero : ∀ t ≤ 1, g t = 0)
    (hpow : ∀ a : ℝ, g =O[atTop] (fun t : ℝ ↦ t ^ (-a))) (s : ℂ) :
    MellinConvergent g s :=
  mellinConvergent_of_isBigO_rpow hlocal (hpow (s.re + 1)) (by linarith)
    (isBigO_tail_zero hzero (s.re - 1)) (by linarith)

private theorem mellin_tail_hasDerivAt {g : ℝ → ℂ}
    (hlocal : LocallyIntegrableOn g (Ioi 0)) (hzero : ∀ t ≤ 1, g t = 0)
    (hpow : ∀ a : ℝ, g =O[atTop] (fun t : ℝ ↦ t ^ (-a))) (s : ℂ) :
    HasDerivAt (mellin g) (mellin (fun t ↦ Real.log t • g t) s) s :=
  (mellin_hasDerivAt_of_isBigO_rpow hlocal (hpow (s.re + 1)) (by linarith)
    (isBigO_tail_zero hzero (s.re - 1)) (by linarith)).2

private theorem mellin_comp_inv_convergent {g : ℝ → ℂ} {s : ℂ}
    (h : MellinConvergent g (-s)) :
    MellinConvergent (fun t ↦ g t⁻¹) s := by
  have h' := MellinConvergent.comp_rpow (f := g) (s := s) (a := -1) (by norm_num)
  simp only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one, Real.rpow_neg_one] at h'
  exact h'.mpr h

/-- Splitting at one and using the weight-two Fricke relation identifies the
full Mellin integral with two upper-tail Mellin integrals. The completed
functional equation follows from this equality. -/
theorem hasMellin_of_fricke {F : ℝ → ℝ}
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    (hint : ∀ s, MellinConvergent (upperMellinTail F) s) (s : ℂ) :
    HasMellin (fun t ↦ (F t : ℂ)) s
      (mellin (upperMellinTail F) s + mellin (upperMellinTail F) (2-s)) := by
  let g := upperMellinTail F
  let q (t : ℝ) : ℂ := (t : ℂ) ^ (-2 : ℂ) • g t⁻¹
  have hq : MellinConvergent q s := by
    apply MellinConvergent.cpow_smul.mpr
    exact mellin_comp_inv_convergent (hint (-(s + -2)))
  have hsplit : (fun t ↦ (F t : ℂ)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t ↦ g t + q t) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 1)] with t ht ht₁
    change 0 < t at ht
    rcases lt_or_gt_of_ne ht₁ with hbelow | habove
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hbelow
      have hgt : g t = 0 := upperMellinTail_zero F hbelow.le
      have hgi : g t⁻¹ = (F t⁻¹ : ℂ) :=
        indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hinv) _
      change (F t : ℂ) = g t + (t : ℂ)^(-2 : ℂ) • g t⁻¹
      rw [hgt, zero_add, hgi, hFricke t ht, smul_eq_mul,
        Complex.cpow_neg, Complex.cpow_two, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')), one_mul]
    · have hinv : t⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr habove.le
      have hgi : g t⁻¹ = 0 := upperMellinTail_zero F hinv
      have hgt : g t = (F t : ℂ) :=
        indicator_of_mem (show t ∈ Ioi (1 : ℝ) from habove) _
      change (F t : ℂ) = g t + (t : ℂ)^(-2 : ℂ) • g t⁻¹
      rw [hgt, hgi, smul_zero, add_zero]
  have hqeq : mellin q s = mellin g (2-s) := by
    unfold q
    rw [mellin_cpow_smul, mellin_comp_inv]
    congr 1
    ring
  have hsmul : (fun t : ℝ ↦ (t : ℂ)^(s-1) • (F t : ℂ)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ ↦ (t : ℂ)^(s-1) • (g t + q t)) :=
    hsplit.mono fun t ht ↦ congrArg ((t : ℂ) ^ (s-1) • ·) ht
  have hadd := hasMellin_add (hint s) hq
  exact ⟨hadd.1.congr hsmul.symm,
    (integral_congr_ae hsmul).trans (hadd.2.trans (by rw [hqeq]))⟩

theorem mellin_eq_upperTail_add_reflect {F : ℝ → ℝ}
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    (hint : ∀ s, MellinConvergent (upperMellinTail F) s) (s : ℂ) :
    mellin (fun t ↦ (F t : ℂ)) s =
      mellin (upperMellinTail F) s + mellin (upperMellinTail F) (2-s) :=
  (hasMellin_of_fricke hFricke hint s).2

/-- The complete Mellin function is centered at one, without an additional
scalar factor in the functional equation. -/
theorem mellin_reflect_of_fricke {F : ℝ → ℝ}
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    (hint : ∀ s, MellinConvergent (upperMellinTail F) s) (s : ℂ) :
    mellin (fun t ↦ (F t : ℂ)) (2-s) = mellin (fun t ↦ (F t : ℂ)) s := by
  rw [mellin_eq_upperTail_add_reflect hFricke hint, mellin_eq_upperTail_add_reflect hFricke hint,
    show 2-(2-s)=s by ring, add_comm]

/-- Differentiating the two tail Mellin integrals twice introduces the
squared logarithm. Both terms have the same sign at the center. -/
theorem second_deriv_mellin_eq_logSquared_tail {F : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    {c : ℝ} (hc : 0 < c)
    (hdecay : upperMellinTail F =O[atTop] (fun t ↦ Real.exp (-c*t))) :
    iteratedDeriv 2 (mellin (fun t ↦ (F t : ℂ))) 1 =
      2 * Complex.ofReal (∫ t in Ioi (1 : ℝ), F t * Real.log t ^ 2) := by
  let g := upperMellinTail F
  let l (t : ℝ) : ℂ := Real.log t • g t
  let ll (t : ℝ) : ℂ := Real.log t • l t
  have hg := locallyIntegrable_upperMellinTail hF
  have hgz : ∀ t ≤ 1, g t = 0 := fun _ ht ↦ upperMellinTail_zero F ht
  have hgp (a : ℝ) : g =O[atTop] (fun t : ℝ ↦ t^(-a)) :=
    hdecay.trans (isLittleO_exp_neg_mul_rpow_atTop hc _).isBigO
  have hl : LocallyIntegrableOn l (Ioi 0) :=
    hg.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (continuousOn_of_forall_continuousAt fun _ ht ↦ Real.continuousAt_log (ne_of_gt ht))
  have hlz : ∀ t ≤ 1, l t = 0 := fun t ht ↦ by simp [l, hgz t ht]
  have hlp (a : ℝ) : l =O[atTop] (fun t : ℝ ↦ t^(-a)) :=
    isBigO_rpow_top_log_smul (show a < a+1 by linarith) (hgp (a+1))
  have h₁ (s : ℂ) : HasDerivAt (mellin g) (mellin l s) s :=
    mellin_tail_hasDerivAt hg hgz hgp s
  have h₂ (s : ℂ) : HasDerivAt (mellin l) (mellin ll s) s :=
    mellin_tail_hasDerivAt hl hlz hlp s
  have hR (s : ℂ) : HasDerivAt (fun z : ℂ ↦ 2-z) (-1) s := by
    exact (hasDerivAt_id s).const_sub 2
  have heq : mellin (fun t ↦ (F t : ℂ)) =
      fun s ↦ mellin g s + mellin g (2-s) := by
    funext s
    exact mellin_eq_upperTail_add_reflect hFricke (mellin_tail_convergent hg hgz hgp) s
  have hD : deriv (mellin (fun t ↦ (F t : ℂ))) =
      fun s ↦ mellin l s - mellin l (2-s) := by
    funext s
    rw [heq]
    have hd : HasDerivAt (fun z ↦ mellin g z + mellin g (2-z))
        (mellin l s + mellin l (2-s) * (-1)) s :=
      (h₁ s).add ((h₁ (2-s)).comp s (hR s))
    simpa only [mul_neg, mul_one, ← sub_eq_add_neg] using hd.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hD]
  have hd : HasDerivAt (fun z ↦ mellin l z - mellin l (2-z))
      (mellin ll 1 - mellin ll (2-1) * (-1)) 1 :=
    (h₂ 1).sub ((h₂ (2-1)).comp 1 (hR 1))
  have hterm : mellin ll 1 = Complex.ofReal (∫ t in Ioi (1 : ℝ), F t * Real.log t ^ 2) := by
    simp only [mellin, sub_self, Complex.cpow_zero, one_smul]
    rw [← integral_complex_ofReal, ← inter_eq_right.mpr
      (show Ioi (1 : ℝ) ⊆ Ioi 0 from Ioi_subset_Ioi zero_le_one),
      ← setIntegral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [ll, l, g, upperMellinTail, ht, Complex.real_smul, pow_two]
      ring
    · simp [ll, l, g, upperMellinTail, ht]
  rw [hd.deriv]
  norm_num [hterm]
  ring

/-- The upper-tail coefficient integral with a specified exponential rate. -/
noncomputable def expLogSquaredKernel (c : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (1 : ℝ), Real.exp (-(c*n)*t) * Real.log t ^ 2

private theorem exp_tail_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : n ≠ 0)
    {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-(c*n)*t) ≤ Real.exp (-(c*n)) * Real.exp (-c*(t-1)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have h := mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hn')) (sub_nonneg.mpr ht)
  nlinarith only [h]

private theorem norm_fourierTerm_le {c : ℝ} (hc : 0 < c) {a : ℕ → ℝ}
    (ha₀ : a 0 = 0) (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖a n * Real.exp (-(c*n)*t)‖ ≤
      (‖a n‖ * Real.exp (-(c*n))) * Real.exp (-c*(t-1)) := by
  by_cases hn : n = 0
  · simp [hn, ha₀]
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_assoc]
  exact mul_le_mul_of_nonneg_left (exp_tail_le hc hn ht) (norm_nonneg _)

private theorem upperMellinTail_decay_of_coeffs {c : ℝ} (hc : 0 < c)
    {a : ℕ → ℝ} (ha₀ : a 0 = 0) {F : ℝ → ℝ}
    (hF : ∀ t > 1, HasSum (fun n : ℕ ↦ a n * Real.exp (-(c*n)*t)) (F t))
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ * Real.exp (-(c*n)))) :
    upperMellinTail F =O[atTop] (fun t ↦ Real.exp (-c*t)) := by
  apply IsBigO.of_bound ((∑' n : ℕ, ‖a n‖ * Real.exp (-(c*n))) * Real.exp c)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hbd := ha.mul_right (Real.exp (-c*(t-1)))
  have hm := fun n ↦ norm_fourierTerm_le hc ha₀ n ht.le
  have hint := hbd.of_nonneg_of_le (fun n ↦ norm_nonneg (a n * Real.exp (-(c*n)*t))) hm
  rw [upperMellinTail, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), Complex.norm_real,
    ← (hF t ht).tsum_eq, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ ∑' n : ℕ, ‖a n * Real.exp (-(c*n)*t)‖ := norm_tsum_le_tsum_norm hint
    _ ≤ ∑' n : ℕ, (‖a n‖ * Real.exp (-(c*n))) * Real.exp (-c*(t-1)) :=
      hint.tsum_le_tsum hm hbd
    _ = _ := by
      rw [tsum_mul_right, mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem integrable_expLogSquared_tail {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-c*(t-1)) * Real.log t ^ 2) (Ioi 1) := by
  have hbase : IntegrableOn (fun t : ℝ ↦ t^2 * Real.exp (-c*t)) (Ioi 0) := by
    simpa [Real.rpow_two] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := c)
        (by norm_num) (by norm_num) hc)
  have hbase' := (hbase.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 from
    Ioi_subset_Ioi zero_le_one)).const_mul (Real.exp c)
  apply hbase'.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  change 1 < t at ht
  have hpos : 0 < t := lt_trans zero_lt_one ht
  have hlog₀ := Real.log_nonneg ht.le
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hsquare : Real.log t ^ 2 ≤ t^2 := by
    gcongr
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)),
    show -c*(t-1) = c + -c*t by ring, Real.exp_add]
  calc
    _ ≤ (Real.exp c * Real.exp (-c*t)) * t^2 :=
      mul_le_mul_of_nonneg_left hsquare (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by ring

/-- Exchange the exponentially convergent Fourier expansion with the
logarithm-squared Mellin integral by a summable absolute majorant. -/
theorem hasSum_expLogSquaredKernel {c : ℝ} (hc : 0 < c)
    {a : ℕ → ℝ} (ha₀ : a 0 = 0) {F : ℝ → ℝ}
    (hF : ∀ t > 1, HasSum (fun n : ℕ ↦ a n * Real.exp (-(c*n)*t)) (F t))
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ * Real.exp (-(c*n)))) :
    HasSum (fun n ↦ a n * expLogSquaredKernel c n)
      (∫ t in Ioi (1 : ℝ), F t * Real.log t ^ 2) := by
  let D (t : ℝ) := Real.exp (-c*(t-1)) * Real.log t ^ 2
  let b (n : ℕ) := ‖a n‖ * Real.exp (-(c*n))
  have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun n t ↦ (a n * Real.exp (-(c*n)*t)) * Real.log t ^ 2)
    (f := fun t ↦ F t * Real.log t ^ 2)
    (fun n t ↦ b n * D t)
    (fun _ ↦ by fun_prop) ?_ ?_ ?_ ?_
  · apply h.congr_fun
    intro n
    simp only [expLogSquaredKernel, mul_assoc, integral_const_mul]
  · intro n
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    change 1 < t at ht
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [b, D, ← mul_assoc] using
      mul_le_mul_of_nonneg_right (norm_fourierTerm_le hc ha₀ n ht.le) (sq_nonneg (Real.log t))
  · exact ae_of_all _ fun t ↦ ha.mul_right (D t)
  · simp_rw [tsum_mul_right]
    exact (integrable_expLogSquared_tail hc).const_mul (∑' n, b n)
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact (hF t ht).mul_right (Real.log t ^ 2)

/-- The second central derivative of the full, gamma-completed function is
twice the sum of the coefficientwise logarithm-squared upper-tail integrals. -/
theorem second_deriv_mellin_eq_kernel_sum {F : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    {c : ℝ} (hc : 0 < c) {a : ℕ → ℝ} (ha₀ : a 0 = 0)
    (hFourier : ∀ t > 1, HasSum (fun n : ℕ ↦ a n * Real.exp (-(c*n)*t)) (F t))
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ * Real.exp (-(c*n)))) :
    iteratedDeriv 2 (mellin (fun t ↦ (F t : ℂ))) 1 =
      2 * Complex.ofReal (∑' n : ℕ, a n * expLogSquaredKernel c n) := by
  rw [second_deriv_mellin_eq_logSquared_tail hF hFricke hc
    (upperMellinTail_decay_of_coeffs hc ha₀ hFourier ha),
    (hasSum_expLogSquaredKernel hc ha₀ hFourier ha).tsum_eq]

/-- Polynomial growth implies absolute convergence of the Fourier series at
the point separating the two Fricke tails. -/
theorem summable_fourier_norm_at_one {c : ℝ} (hc : 0 < c) {a : ℕ → ℝ} {k : ℕ}
    (ha : ∀ n, ‖a n‖ ≤ (n : ℝ)^k) :
    Summable (fun n : ℕ ↦ ‖a n‖ * Real.exp (-(c*n))) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    linarith
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ)^k * Real.exp (-(c*n))) := by
    have he (n : ℕ) : Real.exp (-(c*n)) = (Real.exp (-c)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa only [he] using (summable_pow_mul_geometric_of_norm_lt_one k hr)
  exact hbase.of_nonneg_of_le (fun _ ↦ by positivity)
    (fun n ↦ mul_le_mul_of_nonneg_right (ha n) (Real.exp_pos _).le)

private theorem mellinRate_pos_for_derivative : 0 < mellinRate := by
  unfold mellinRate
  positivity

/-- At conductor 389 the derivative is exactly twice the moment sum in
`MellinKernel.lean`. Both proof inputs tied to modularity are explicit:
the scaled Fourier expansion and the Fricke transformation. -/
theorem second_deriv_mellin_389_eq_kernel_sum {F : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    {a : ℕ → ℝ} (ha₀ : a 0 = 0)
    (hFourier : ∀ t > 1, HasSum (fun n : ℕ ↦ a n * Real.exp (-(mellinRate*n)*t)) (F t))
    (ha : ∀ n, |a n| ≤ (n : ℝ)^2) :
    iteratedDeriv 2 (mellin (fun t ↦ (F t : ℂ))) 1 =
      2 * Complex.ofReal (∑' n : ℕ, a n * mellinKernel n) :=
  second_deriv_mellin_eq_kernel_sum hF hFricke mellinRate_pos_for_derivative ha₀ hFourier
    (summable_fourier_norm_at_one mellinRate_pos_for_derivative ha)

/-- With a Fourier expansion and Fricke symmetry, the completed Mellin
transform is entire and satisfies the center-one functional equation. -/
theorem differentiable_mellin_of_fricke {F : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    {c : ℝ} (hc : 0 < c) {a : ℕ → ℝ} (ha₀ : a 0 = 0)
    (hFourier : ∀ t > 1, HasSum (fun n : ℕ ↦ a n * Real.exp (-(c*n)*t)) (F t))
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ * Real.exp (-(c*n)))) :
    Differentiable ℂ (mellin (fun t ↦ (F t : ℂ))) ∧
      ∀ s : ℂ, mellin (fun t ↦ (F t : ℂ)) (2-s) = mellin (fun t ↦ (F t : ℂ)) s := by
  let g := upperMellinTail F
  have hg := locallyIntegrable_upperMellinTail hF
  have hgz : ∀ t ≤ 1, g t = 0 := fun _ ht ↦ upperMellinTail_zero F ht
  have hdec := upperMellinTail_decay_of_coeffs hc ha₀ hFourier ha
  have hgp (a : ℝ) : g =O[atTop] (fun t : ℝ ↦ t^(-a)) :=
    hdec.trans (isLittleO_exp_neg_mul_rpow_atTop hc _).isBigO
  have hint := mellin_tail_convergent hg hgz hgp
  have hd : Differentiable ℂ (mellin g) :=
    fun s ↦ (mellin_tail_hasDerivAt hg hgz hgp s).differentiableAt
  refine ⟨?_, mellin_reflect_of_fricke hFricke hint⟩
  have heq : mellin (fun t ↦ (F t : ℂ)) =
      fun s ↦ mellin g s + mellin g (2-s) :=
    funext (mellin_eq_upperTail_add_reflect hFricke hint)
  rw [heq]
  fun_prop

/-- The uncompleted continuation corresponding to the exponential rate
`c = 2π / √N`. -/
noncomputable def normalizedMellinL (c : ℝ) (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  (c : ℂ)^s / Complex.Gamma s * mellin (fun t ↦ (F t : ℂ)) s

/-- Multiplication by the conventional conductor and gamma factor recovers
the full Mellin function wherever the gamma factor is finite and nonzero in
the right half-plane. In particular this equality holds near the center. -/
theorem gammaCompletion_eq_mellin {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ)
    {s : ℂ} (hs : 0 < s.re) :
    ((c : ℂ)^(-s) * Complex.Gamma s) * normalizedMellinL c F s =
      mellin (fun t ↦ (F t : ℂ)) s := by
  have hcp : (c : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  have hg := Complex.Gamma_ne_zero_of_re_pos hs
  rw [normalizedMellinL, Complex.cpow_neg]
  field_simp

/-- The level-389 identity for the completed continuation, including the
factor `(2π / √389)^(-s) Γ(s)` before differentiation. -/
theorem second_deriv_gammaCompletion_389_eq_kernel_sum {F : ℝ → ℝ}
    (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (hFricke : ∀ t > 0, F t⁻¹ = t^2 * F t)
    {a : ℕ → ℝ} (ha₀ : a 0 = 0)
    (hFourier : ∀ t > 1, HasSum (fun n : ℕ ↦ a n * Real.exp (-(mellinRate*n)*t)) (F t))
    (ha : ∀ n, |a n| ≤ (n : ℝ)^2) :
    iteratedDeriv 2 (fun s ↦ ((mellinRate : ℂ)^(-s) * Complex.Gamma s) *
      normalizedMellinL mellinRate F s) 1 =
      2 * Complex.ofReal (∑' n : ℕ, a n * mellinKernel n) := by
  have hpos : ∀ᶠ s : ℂ in 𝓝 1, 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : (fun s ↦ ((mellinRate : ℂ)^(-s) * Complex.Gamma s) *
      normalizedMellinL mellinRate F s) =ᶠ[𝓝 (1 : ℂ)] (mellin fun t ↦ (F t : ℂ)) :=
    hpos.mono fun _ hs ↦ gammaCompletion_eq_mellin mellinRate_pos_for_derivative F hs
  rw [he.iteratedDeriv_eq 2]
  exact second_deriv_mellin_389_eq_kernel_sum hF hFricke ha₀ hFourier ha

/-- On the half-plane of absolute convergence this is the actual Dirichlet
series once the coefficients are identified on the full positive axis. -/
theorem normalizedMellinL_eq_LSeries {c : ℝ} (hc : 0 < c)
    {a : ℕ → ℝ} (ha₀ : a 0 = 0) {F : ℝ → ℝ}
    (hFourier : ∀ t > 0, HasSum (fun n : ℕ ↦ a n * Real.exp (-(c*n)*t)) (F t))
    {s : ℂ} (hs : 0 < s.re) (hsum : LSeriesSummable (fun n ↦ (a n : ℂ)) s) :
    normalizedMellinL c F s = LSeries (fun n ↦ (a n : ℂ)) s := by
  apply BSD.normalized_mellin_eq_LSeries hc (by simp [ha₀]) _ hs hsum
  intro t ht
  have h := (hFourier t ht).map Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous
  apply h.congr_fun
  intro n
  exact (Complex.ofReal_mul (a n) (Real.exp (-(c*n)*t))).symm

end BSD.RankTwo
