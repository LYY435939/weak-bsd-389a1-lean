import BSD.General.ModularCorrectionAlgebra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Absolute convergence of finite prime-power corrections

A bound of `p ^ k` on the norm of the coefficient of degree `k` yields
absolute convergence in `1 < s.re`. This applies to the reciprocal local
power series of the omitted Euler polynomials.
-/

namespace BSD.General

open scoped BigOperators
open ArithmeticFunction

/-- A local coefficient bound gives a geometric majorant after evaluating the
Dirichlet series on the prime-power support. -/
theorem lSeriesSummable_ofPowerSeries_of_coeff_le_pow {p : ℕ} (hp : 1 < p)
    (F : PowerSeries ℂ) (hF : ∀ k, ‖F.coeff k‖ ≤ (p : ℝ) ^ k)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (ofPowerSeries p F) s := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hden : 0 < (p : ℝ) ^ s.re := Real.rpow_pos_of_pos (zero_lt_one.trans hp') _
  let q : ℝ := (p : ℝ) / (p : ℝ) ^ s.re
  have hq₀ : 0 ≤ q := div_nonneg hp₀ hden.le
  have hq : q < 1 := (div_lt_one₀ hden).2 (by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hp' hs)
  have hmaj : Summable (Function.extend (p ^ ·) (fun k : ℕ => q ^ k) 0) :=
    (summable_extend_zero (Nat.pow_right_injective hp)).2 (summable_geometric_of_lt_one hq₀ hq)
  rw [LSeriesSummable, ← summable_norm_iff]
  refine hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro n
  by_cases hn : ∃ k : ℕ, p ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    have hpow : ((p : ℝ) ^ k) ^ s.re = ((p : ℝ) ^ s.re) ^ k := by
      calc
        ((p : ℝ) ^ k) ^ s.re = (p : ℝ) ^ ((k : ℝ) * s.re) := by
          rw [Real.rpow_mul hp₀, Real.rpow_natCast]
        _ = ((p : ℝ) ^ s.re) ^ k := by
          rw [mul_comm, Real.rpow_mul hp₀, Real.rpow_natCast]
    rw [(Nat.pow_right_injective hp).extend_apply, LSeries.norm_term_eq,
      if_neg (pow_ne_zero k (Nat.ne_zero_of_lt hp)), ofPowerSeries_apply_pow hp,
      Nat.cast_pow, hpow]
    dsimp [q]
    rw [div_pow]
    exact div_le_div_of_nonneg_right (hF k) (pow_nonneg hden.le k)
  · rw [LSeries.norm_term_eq, ofPowerSeries_apply hp,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    simp

/-- The finite Dirichlet product of local series with the coefficient bound
is absolutely convergent on the same half-plane. -/
theorem lSeriesSummable_finiteSeriesRemoval (S : Finset ℕ) (F : ℕ → PowerSeries ℂ)
    (hp : ∀ p ∈ S, 1 < p) (hF : ∀ p ∈ S, ∀ k, ‖(F p).coeff k‖ ≤ (p : ℝ) ^ k)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (finiteSeriesRemoval S F) s := by
  classical
  revert hp hF
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    simp only [finiteSeriesRemoval, Finset.prod_empty, ArithmeticFunction.one_eq_delta]
    exact ((hasSum_ite_eq 1 (1 : ℂ)).congr_fun (LSeries.term_delta s)).summable
  | @insert p S hpS ih =>
    intro hp hF
    have hpmem := Finset.mem_insert_self p S
    have hlocal := lSeriesSummable_ofPowerSeries_of_coeff_le_pow (hp p hpmem) (F p)
      (hF p hpmem) hs
    have hS := ih (fun q hq => hp q (Finset.mem_insert_of_mem hq))
      (fun q hq => hF q (Finset.mem_insert_of_mem hq))
    simpa only [finiteSeriesRemoval, Finset.prod_insert hpS] using
      ArithmeticFunction.LSeriesSummable_mul hlocal hS

/-- Inverse relations for the local power series give an inverse relation
for the finite Dirichlet products. -/
theorem finiteSeriesRemoval_mul_eq_one (S : Finset ℕ) (F G : ℕ → PowerSeries ℂ)
    (h : ∀ p ∈ S, F p * G p = 1) :
    finiteSeriesRemoval S F * finiteSeriesRemoval S G = 1 := by
  rw [finiteSeriesRemoval, finiteSeriesRemoval, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun p hp => ?_
  rw [← map_mul, h p hp, map_one]

end BSD.General
