import BSD.PrimeRecurrence
import Mathlib.Analysis.Complex.Basic

/-! # Equal-modulus roots and the reciprocal coefficient bound -/

namespace BSD

/-- The reciprocal roots of `1 + aX + pX²` both have modulus `√p` under the
Hasse bound on `a`. This includes the case of a repeated root. -/
theorem hasse_quadratic_roots {a p : ℝ} (hp : 0 ≤ p) (ha : |a| ≤ 2 * Real.sqrt p) :
    ∃ α β : ℂ, α + β = -(a : ℂ) ∧ α * β = (p : ℂ) ∧
      ‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p := by
  have hdisc : 0 ≤ 4 * p - a ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp ha
    have hnonneg : 0 ≤ 2 * Real.sqrt p + a := by linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr hhi) hnonneg, Real.sq_sqrt hp]
  let x := -a / 2
  let y := Real.sqrt (4 * p - a ^ 2) / 2
  have hnormSq : x * x + y * y = p := by
    dsimp [x, y]
    nlinarith only [Real.sq_sqrt hdisc]
  refine ⟨⟨x, y⟩, ⟨x, -y⟩, ?_, ?_, ?_, ?_⟩
  · apply Complex.ext
    · change x + x = -a
      dsimp [x]
      ring
    · change y + -y = -(0 : ℝ)
      ring
  · apply Complex.ext
    · change x * x - y * -y = p
      calc
        _ = x * x + y * y := by ring
        _ = p := hnormSq
    · change x * -y + y * x = 0
      ring
  · rw [Complex.norm_def, Complex.normSq_apply]
    change Real.sqrt (x * x + y * y) = Real.sqrt p
    rw [hnormSq]
  · rw [Complex.norm_def, Complex.normSq_apply]
    change Real.sqrt (x * x + -y * -y) = Real.sqrt p
    rw [neg_mul_neg, hnormSq]

/-- The coefficients of the reciprocal of a good Euler polynomial satisfy
the prime-power divisor bound. -/
theorem hasse_reciprocal_quadratic_bound {a p : ℤ} (hp : 0 ≤ (p : ℝ))
    (ha : |(a : ℝ)| ≤ 2 * Real.sqrt (p : ℝ)) (k : ℕ) :
    |(((PowerSeries.invOfUnit
      (1 + PowerSeries.C a * PowerSeries.X + PowerSeries.C p * PowerSeries.X ^ 2)
        1).coeff k : ℤ) : ℝ)| ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k := by
  let D : PowerSeries ℤ := 1 + PowerSeries.C a * PowerSeries.X +
    PowerSeries.C p * PowerSeries.X ^ 2
  let F := PowerSeries.invOfUnit D 1
  let f (j : ℕ) : ℂ := (F.coeff j : ℤ)
  have hrec : F.coeff 1 = -a ∧ ∀ j : ℕ,
      F.coeff (j + 2) = -a * F.coeff (j + 1) - p * F.coeff j := by
    simpa only [D, F, map_neg, neg_mul, sub_neg_eq_add] using
      reciprocal_quadratic_coefficients (-a) p
  have hzero : F.coeff 0 = 1 := by
    simp [F, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hfzero : f 0 = 1 := by simp [f, hzero]
  have hfone : f 1 = -(a : ℂ) := by simp [f, hrec.1]
  have hfrec (j : ℕ) : f (j + 2) = -(a : ℂ) * f (j + 1) - (p : ℂ) * f j := by
    simpa only [f, Int.cast_sub, Int.cast_mul, Int.cast_neg] using
      congrArg (fun n : ℤ ↦ (n : ℂ)) (hrec.2 j)
  obtain ⟨α, β, hsum, hprod, hα, hβ⟩ := hasse_quadratic_roots hp ha
  have hsum' : α + β = -(a : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hsum
  have hprod' : α * β = (p : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hprod
  have hdiff (j : ℕ) : f (j + 1) - β * f j = α ^ (j + 1) := by
    induction j with
    | zero =>
      rw [Nat.zero_add, pow_one, hfzero, hfone, mul_one, ← hsum']
      ring
    | succ j ih =>
      change f (j + 2) - β * f (j + 1) = α ^ (j + 2)
      rw [hfrec, ← hsum', ← hprod', pow_succ, ← ih]
      ring
  let r := Real.sqrt (p : ℝ)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hbound (j : ℕ) : ‖f j‖ ≤ ((j : ℝ) + 1) * r ^ j := by
    induction j with
    | zero => simp [hfzero]
    | succ j ih =>
      have he : f (j + 1) = α ^ (j + 1) + β * f j := sub_eq_iff_eq_add.mp (hdiff j)
      calc
        ‖f (j + 1)‖ ≤ ‖α ^ (j + 1)‖ + ‖β * f j‖ := by
          rw [he]
          exact norm_add_le _ _
        _ = r ^ (j + 1) + r * ‖f j‖ := by rw [norm_pow, norm_mul, hα, hβ]
        _ ≤ r ^ (j + 1) + r * (((j : ℝ) + 1) * r ^ j) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hr)
        _ = ((↑(j + 1) : ℝ) + 1) * r ^ (j + 1) := by
          rw [Nat.cast_succ, pow_succ]
          ring
  simpa only [f, F, D, r, Complex.norm_intCast] using hbound k

end BSD
