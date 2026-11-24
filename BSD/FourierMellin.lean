import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Tactic

/-! # From Fourier coefficients on the imaginary axis to an ordinary L-series

The scaling constant is explicit. For a modular form of width one it is
`2 * Real.pi`. The hypothesis on the coefficients refers only to a half-plane
where the Dirichlet series converges.
-/

open Set MeasureTheory

namespace BSD

theorem normalized_mellin_eq_LSeries {a : ℕ → ℂ} {F : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (ha₀ : a 0 = 0)
    (hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ ↦ a n * (Real.exp (-(c * n) * t) : ℂ)) (F t))
    {s : ℂ} (hs : 0 < s.re) (hsum : LSeriesSummable a s) :
    (c : ℂ) ^ s / Complex.Gamma s * mellin F s = LSeries a s := by
  have habs : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ s.re := by
    apply (summable_norm_iff.mpr hsum).congr
    intro n
    change ‖LSeries.term a s n‖ = _
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha₀]
    · simp [hn]
  have hscaled : Summable fun n : ℕ ↦ ‖a n‖ / (c * n) ^ s.re := by
    apply (habs.div_const (c ^ s.re)).congr
    intro n
    rw [Real.mul_rpow hc.le (Nat.cast_nonneg n)]
    ring
  have hfreq (n : ℕ) : a n = 0 ∨ 0 < c * n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl ha₀
    · exact Or.inr (mul_pos hc (by exact_mod_cast hn))
  have hm := (hasSum_mellin hfreq hs hF hscaled).mul_left ((c : ℂ) ^ s / Complex.Gamma s)
  have hds : LSeriesHasSum a s ((c : ℂ) ^ s / Complex.Gamma s * mellin F s) := by
    apply hm.congr_fun
    intro n
    rw [LSeries.term_of_ne_zero' (by rintro rfl; simp at hs), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hc.le (Nat.cast_nonneg n)]
    push_cast
    have hγ := Complex.Gamma_ne_zero_of_re_pos hs
    have hc' : (c : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
    field_simp
  exact hds.LSeries_eq.symm

end BSD
