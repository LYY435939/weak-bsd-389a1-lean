import BSD.FourierOrthogonality
import BSD.Eta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! Absolute convergence from horizontal Fourier coefficients of the Fermat eta product. -/

open Filter MeasureTheory Set
open scoped Topology Real

namespace BSD.FermatCubic

/-- The eta product evaluated on a horizontal line in the upper half-plane. -/
noncomputable def etaProductSlice (t x : ℝ) : ℂ :=
  ModularForm.eta (3 * ((x : ℂ) + (t : ℂ) * Complex.I)) ^ 2 *
  ModularForm.eta (9 * ((x : ℂ) + (t : ℂ) * Complex.I)) ^ 2

/-- The weight-twelve discriminant bounds the eta product uniformly in the real direction. -/
theorem exists_etaProductSlice_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → ∀ x, ‖etaProductSlice t x‖ ≤ B / t := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound CuspForm.discriminant
  have hη (z : UpperHalfPlane) :
      ‖ModularForm.eta z‖ ^ 24 * z.im ^ 6 ≤ C := by
    have h := hC z
    change ‖ModularForm.eta z ^ 24‖ ≤ C / z.im ^ ((12 : ℤ) / 2 : ℝ) at h
    rw [norm_pow] at h
    norm_num at h
    exact (le_div_iff₀ (pow_pos z.im_pos 6)).mp h
  let B := max 1 C
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, by linarith, fun t ht x ↦ ?_⟩
  let z (m : ℕ) (hm : 0 < m) : UpperHalfPlane :=
    ⟨(m : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I), by simpa using mul_pos (Nat.cast_pos.mpr hm) ht⟩
  have hz (m : ℕ) (hm : 0 < m) : (z m hm).im = m * t := by simp [z, UpperHalfPlane.im]
  have hη' (m : ℕ) (hm : 0 < m) : (‖ModularForm.eta (z m hm)‖ ^ 4 * t) ^ 6 ≤ B := by
    calc
      _ = ‖ModularForm.eta (z m hm)‖ ^ 24 * t ^ 6 := by ring
      _ ≤ ‖ModularForm.eta (z m hm)‖ ^ 24 * (z m hm).im ^ 6 := by
        gcongr
        rw [hz m hm]
        exact le_mul_of_one_le_left ht.le (by exact_mod_cast hm)
      _ ≤ C := hη _
      _ ≤ B := le_max_right _ _
  have h1 (m : ℕ) (hm : 0 < m) : ‖ModularForm.eta (z m hm)‖ ^ 4 * t ≤ B := by
    by_contra! hn
    have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ ‖ModularForm.eta (z m hm)‖ ^ 4 * t)
      (by decide : 1 ≤ 6)
    rw [pow_one] at hpow
    linarith [hη' m hm]
  rw [etaProductSlice, norm_mul, norm_pow, norm_pow, le_div_iff₀ ht]
  change ‖ModularForm.eta (z 3 (by decide))‖ ^ 2 * ‖ModularForm.eta (z 9 (by decide))‖ ^ 2 * t ≤ B
  nlinarith [h1 3 (by decide), h1 9 (by decide),
    mul_nonneg ht.le (sq_nonneg (‖ModularForm.eta (z 3 (by decide))‖ ^ 2 -
      ‖ModularForm.eta (z 9 (by decide))‖ ^ 2))]

private theorem continuous_slice {t : ℝ} (ht : 0 < t) : Continuous (etaProductSlice t) := by
  have h (m : ℕ) (hm : 0 < m) : Continuous fun x : ℝ ↦
      ModularForm.eta ((m : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet ?_).continuousAt.comp
      (f := fun x : ℝ ↦ (m : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) (by fun_prop)
    simpa using mul_pos (Nat.cast_pos.mpr hm) ht
  exact ((h 3 (by decide)).pow 2).mul ((h 9 (by decide)).pow 2)

/-- Arithmetic identification of horizontal Fourier coefficients, with the exponential damping
coming from the imaginary coordinate. -/
def HasEtaSliceCoefficients (a : ℕ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ n : ℕ,
    fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (etaProductSlice t) (n : ℤ) =
      a n * (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)

/-- Parseval on the horizontal line of height `1/N` gives a quadratic second moment
whenever the slices have the weight-two bound `B/t`. -/
theorem _root_.BSD.secondMoment_of_fourierSlices {a : ℕ → ℂ}
    {slice : (t : ℝ) → 0 < t → ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hcont : ∀ t ht, Continuous (slice t ht))
    (hbound : ∀ t ht x, ‖slice t ht x‖ ≤ B / t)
    (ha : ∀ t ht (n : ℕ), fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (slice t ht) (n : ℤ) =
      a n * (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 0 < N →
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ (K * N) ^ 2 := by
  let D := Real.exp (2 * Real.pi)
  have hD : 0 < D := Real.exp_pos _
  refine ⟨D * B, mul_nonneg hD.le hB, fun N hN ↦ ?_⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let t := (N : ℝ)⁻¹
  have ht : 0 < t := inv_pos.mpr hN'
  let f := slice t ht
  have hc : Continuous f := hcont t ht
  have hbn (x : ℝ) : ‖f x‖ ≤ B * N := by simpa [t, div_eq_mul_inv] using hbound t ht x
  have hL2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hc.aestronglyMeasurable _ (Eventually.of_forall hbn)
  let c := fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) f
  have hsum := hasSum_sq_fourierCoeffOn zero_lt_one hL2
  let S := Finset.Icc 1 N
  have hint : (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤ (B * N) ^ 2 := by
    calc
      _ ≤ ∫ _ in (0 : ℝ)..1, (B * N) ^ 2 :=
        intervalIntegral.integral_mono zero_le_one ((hc.norm.pow 2).intervalIntegrable ..)
          intervalIntegrable_const (fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (hbn x) 2)
      _ = _ := by simp
  have hcs : ∑ n ∈ S, ‖c (n : ℤ)‖ ^ 2 ≤ (B * N) ^ 2 := by
    let emb : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
    have h := sum_le_hasSum (S.map emb) (fun i _ ↦ sq_nonneg _) hsum
    simpa [c, emb] using h.trans (by simpa using hint)
  have hpoint (n : ℕ) (hn : n ∈ S) : ‖a n‖ ≤ D * ‖c (n : ℤ)‖ := by
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn1 : (n : ℝ) * t ≤ 1 := by rwa [← div_eq_mul_inv, div_le_one hN']
    have he : 1 ≤ D * Real.exp (-(2 * Real.pi * n) * t) := by
      rw [← Real.exp_zero, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn1)]
    change ‖a n‖ ≤ D * ‖fourierCoeffOn _ (slice t ht) _‖
    rw [ha t ht n, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    nlinarith [mul_nonneg (norm_nonneg (a n)) (sub_nonneg.mpr he)]
  calc
    _ ≤ ∑ n ∈ S, (D * ‖c (n : ℤ)‖) ^ 2 :=
      Finset.sum_le_sum fun n hn ↦ pow_le_pow_left₀ (norm_nonneg _) (hpoint n hn) 2
    _ = D ^ 2 * ∑ n ∈ S, ‖c (n : ℤ)‖ ^ 2 := by simp [mul_pow, Finset.mul_sum]
    _ ≤ D ^ 2 * (B * N) ^ 2 := mul_le_mul_of_nonneg_left hcs (sq_nonneg D)
    _ = _ := by ring

/-- The eta product's Fourier coefficients have a quadratic second moment. -/
theorem eta_coeff_secondMoment {a : ℕ → ℂ} (ha : HasEtaSliceCoefficients a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 0 < N →
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ (K * N) ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := exists_etaProductSlice_bound
  exact BSD.secondMoment_of_fourierSlices (slice := fun t _ ↦ etaProductSlice t)
    hB (fun _ ht ↦ continuous_slice ht) hbound ha

/-- Cauchy–Schwarz converts a quadratic second moment into absolute convergence for
`Re s > 3/2`. -/
theorem lSeriesSummable_of_secondMoment {a : ℕ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ N : ℕ, 0 < N → ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ (K * N) ^ 2)
    {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable a s := by
  apply LSeriesSummable_of_sum_norm_bigO (r := (3 / 2 : ℝ)) _ (by norm_num) hs
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 N) (f := fun n ↦ ‖a n‖)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcs
  have hpow : ((N : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (N : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast hN']
    norm_num
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)),
    Real.norm_of_nonneg (Real.rpow_nonneg hN' _)]
  apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity : 0 ≤ K * (N : ℝ) ^ (3/2 : ℝ))
  rw [mul_pow, hpow]
  calc
    _ ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := hcs
    _ ≤ (N : ℝ) * (K * N) ^ 2 := mul_le_mul_of_nonneg_left (ha N hN) hN'
    _ = _ := by ring

theorem lSeriesSummable_of_etaSliceCoefficients {a : ℕ → ℂ}
    (ha : HasEtaSliceCoefficients a) {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable a s := by
  obtain ⟨K,hK,hm⟩ := eta_coeff_secondMoment ha
  exact lSeriesSummable_of_secondMoment hK hm hs

private noncomputable def expTerm (a : ℕ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  a n * Complex.exp ((-((2 * Real.pi) * n) : ℝ) * w)

private lemma expTerm_real (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    expTerm a n (t : ℂ) = a n * (Real.exp (-((2 * Real.pi) * n) * t) : ℂ) := by
  rw [expTerm, Complex.ofReal_exp, Complex.ofReal_mul]

private lemma expTerm_norm (a : ℕ → ℂ) (n : ℕ) (w : ℂ) :
    ‖expTerm a n w‖ = ‖a n‖ * Real.exp (-((2 * Real.pi) * n) * w.re) := by
  simp [expTerm, Complex.norm_exp]

private noncomputable def etaOnRight (w : ℂ) : ℂ :=
  ModularForm.eta (3 * (w * Complex.I)) ^ 2 * ModularForm.eta (9 * (w * Complex.I)) ^ 2

private lemma etaOnRight_real (t : ℝ) : etaOnRight t = etaProductAxis t := by
  simp only [etaOnRight, etaProductAxis, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc]

/-- The axis identity determines the entire horizontal Fourier series by holomorphic uniqueness.
Absolute summability on an interior real point supplies a uniform majorant on a smaller
right half-plane before applying the identity theorem. -/
theorem etaProductSlice_hasSum_of_axis {a : ℕ → ℂ}
    (ha : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n : ℕ ↦ a n *
      (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)) (etaProductAxis t))
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasSum (fun n : ℕ ↦ a n * (Real.exp (-((2 * Real.pi) * n) * t) : ℂ) *
      fourier (n : ℤ) (x : AddCircle (1 : ℝ))) (etaProductSlice t x) := by
  let b := t / 2
  let U := {w : ℂ | b < w.re}
  have hb : 0 < b := half_pos ht
  have hbt : b < t := half_lt_self ht
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let F := fun w : ℂ ↦ ∑' n : ℕ, expTerm a n w
  have haxis (y : ℝ) (hy : 0 < y) : HasSum (fun n ↦ expTerm a n (y : ℂ)) (etaOnRight y) := by
    simpa only [expTerm_real, etaOnRight_real] using ha y hy
  have hmajor := (haxis b hb).summable.norm
  have hle (n : ℕ) (w : ℂ) (hw : w ∈ U) : ‖expTerm a n w‖ ≤ ‖expTerm a n (b : ℂ)‖ := by
    rw [expTerm_norm, expTerm_norm, Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (show b ≤ w.re from (show b < w.re from hw).le) (neg_nonpos.mpr (by positivity))
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    apply Complex.differentiableOn_tsum_of_summable_norm hmajor _ hU hle
    intro n
    unfold expTerm
    fun_prop
  have hG : AnalyticOnNhd ℂ etaOnRight U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    have h (m : ℕ) (hm : 0 < m) : DifferentiableOn ℂ
        (fun w : ℂ ↦ ModularForm.eta ((m : ℂ) * (w * Complex.I))) U := by
      intro w hw
      apply DifferentiableAt.differentiableWithinAt
      have harg : DifferentiableAt ℂ (fun w : ℂ ↦ (m : ℂ) * (w * Complex.I)) w := by fun_prop
      have hmem : (m : ℂ) * (w * Complex.I) ∈ UpperHalfPlane.upperHalfPlaneSet := by
        simpa using mul_pos (Nat.cast_pos.mpr hm) (lt_trans hb (show b < w.re from hw))
      exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hmem).comp w harg
    exact ((h 3 (by decide)).pow 2).mul ((h 9 (by decide)).pow 2)
  have hnear : Tendsto (fun y : ℝ ↦ (y : ℂ)) (𝓝[>] t) (𝓝[≠] (t : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun y hy ↦ by
      simpa using ne_of_gt hy
  have heq : Set.EqOn F etaOnRight U := by
    apply hF.eqOn_of_preconnected_of_frequently_eq hG (convex_halfSpace_re_gt b).isPreconnected
      (show (t : ℂ) ∈ U from hbt)
    apply hnear.frequently
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (haxis y (ht.trans hy)).tsum_eq
  let w := (t : ℂ) - (x : ℂ) * Complex.I
  have hw : w ∈ U := by simpa [U, w] using hbt
  have hsum : Summable fun n ↦ expTerm a n w :=
    Summable.of_norm_bounded hmajor fun n ↦ hle n w hw
  have hwI : w * Complex.I = (x : ℂ) + (t : ℂ) * Complex.I := by
    simp [w, sub_mul, mul_assoc]
    ring
  have hid : F w = etaProductSlice t x := by
    rw [heq hw]
    simp only [etaOnRight, hwI, etaProductSlice]
  rw [← hid]
  apply hsum.hasSum.congr_fun
  intro n
  rw [expTerm, fourier_coe_apply, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  dsimp [w]
  ring

/-- Extracting the coefficients on a horizontal line recovers the axis coefficients. -/
theorem etaSliceCoefficients_of_axis {a : ℕ → ℂ}
    (ha : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ ↦ a n *
      (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)) (etaProductAxis t)) :
    HasEtaSliceCoefficients a := by
  intro t ht n
  exact fourierCoeffOn_of_hasSum_fourier (ha t ht).summable.norm
    (etaProductSlice_hasSum_of_axis ha t ht) n

/-- An axis identity with the Fermat eta product already guarantees absolute convergence
of the corresponding Dirichlet series throughout `Re(s) > 3/2`. -/
theorem lSeriesSummable_of_etaAxis {a : ℕ → ℂ}
    (ha : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ ↦ a n *
      (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)) (etaProductAxis t))
    {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable a s :=
  lSeriesSummable_of_etaSliceCoefficients (etaSliceCoefficients_of_axis ha) hs

end BSD.FermatCubic
