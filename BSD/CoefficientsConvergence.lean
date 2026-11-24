import BSD.CoefficientsBound
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open Filter PowerSeries
open scoped Topology BigOperators
namespace EtaSupport

lemma etaPoly_coeff_stable (n N : ℕ) (h : n ≤ N) :
    (etaPoly N).coeff n = etaCoeff n := by
  rw [← Polynomial.coeff_coe, etaPoly_coe, etaCoeff]
  exact etaTrunc_coeff_stable n N h

lemma etaPoly_eval_tsum (N : ℕ) (q : ℂ) :
    (∑' n : ℕ, ((etaPoly N).coeff n : ℂ) * q^n) =
      (etaPoly N).eval₂ (Int.castRingHom ℂ) q := by
  rw [tsum_eq_sum (s := (etaPoly N).support)]
  · rw [Polynomial.eval₂_eq_sum]
    rfl
  · intro n hn
    have hz : (etaPoly N).coeff n = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hn
    simp [hz]

/-- The integer coefficients of the formal product give the convergent expansion on the axis. -/
theorem etaCoeff_hasSum
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ (etaCoeff n : ℂ) * (axisQ t)^n)
      (BSD.FermatCubic.etaProductAxis t) := by
  let q := axisQ t
  let r : ℝ := (‖q‖ + 1) / 2
  have hq : ‖q‖ < 1 := axisQ_norm_lt_one ht
  have hr0 : 0 < r := by dsimp [r]; have := norm_nonneg q; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : ‖q‖ < r := by dsimp [r]; linarith
  obtain ⟨C, hC⟩ := etaPoly_coeff_bound r hr0 hr1
  let ρ : ℝ := ‖q‖ / r
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg _) hr0.le
  have hρ1 : ρ < 1 := (div_lt_one₀ hr0).2 hqr
  have hsum : Summable (fun n : ℕ ↦ C * ρ^n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left C
  have hdom (N n : ℕ) :
      ‖(((etaPoly N).coeff n : ℤ) : ℂ) * q^n‖ ≤ C * ρ^n := by
    rw [norm_mul, norm_pow]
    calc
      _ = (‖(((etaPoly N).coeff n : ℤ) : ℂ)‖ * r^n) * ρ^n := by
        change ‖(((etaPoly N).coeff n : ℤ) : ℂ)‖ * ‖q‖^n =
          (‖(((etaPoly N).coeff n : ℤ) : ℂ)‖ * r^n) * (‖q‖ / r)^n
        have hid : (‖q‖ / r)^n = ‖q‖^n / r^n := div_pow _ _ _
        rw [hid]
        have hrn : r^n ≠ 0 := pow_ne_zero n (ne_of_gt hr0)
        field_simp [hrn]
      _ ≤ C * ρ^n := mul_le_mul_of_nonneg_right (hC N n) (pow_nonneg hρ0 n)
  have hpoint (n : ℕ) : Tendsto
      (fun N : ℕ ↦ (((etaPoly N).coeff n : ℤ) : ℂ) * q^n) atTop
      (𝓝 ((etaCoeff n : ℂ) * q^n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [etaPoly_coeff_stable n N hN]
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Filter.Eventually.of_forall hdom)
  have hlimitnorm (n : ℕ) : ‖(etaCoeff n : ℂ) * q^n‖ ≤ C * ρ^n := by
    simpa [etaPoly_coeff_stable n n (le_refl n)] using hdom n n
  have hseries : Summable (fun n : ℕ ↦ (etaCoeff n : ℂ) * q^n) :=
    hsum.of_norm_bounded hlimitnorm
  have heval : Tendsto (fun N : ℕ ↦ ∑' n : ℕ,
      (((etaPoly N).coeff n : ℤ) : ℂ) * q^n) atTop
      (𝓝 (BSD.FermatCubic.etaProductAxis t)) := by
    simpa only [etaPoly_eval_tsum] using etaPoly_tendsto_axis t ht
  have heq := tendsto_nhds_unique hlim heval
  exact heq ▸ hseries.hasSum

end EtaSupport

namespace BSD.FermatCubic

/-- Fourier coefficients of the actual analytic eta product, in the normalization of the
ordinary Mellin transform. -/
theorem etaProductAxis_hasSum_etaCoeff (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ (EtaSupport.etaCoeff n : ℂ) *
      (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)) (etaProductAxis t) := by
  apply (EtaSupport.etaCoeff_hasSum t ht).congr_fun
  intro n
  congr 1
  simp only [EtaSupport.axisQ, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  ring

end BSD.FermatCubic
