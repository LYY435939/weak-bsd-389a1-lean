import BSD.General.ModularCorrectionAlgebra
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity

namespace BSD.General

open ArithmeticFunction

private theorem LSeriesHasSum_singleCoefficient {k : ℕ} (hk : k ≠ 0) (c s : ℂ) :
    LSeriesHasSum (fun n ↦ if n = k then c else 0) s (c / (k : ℂ) ^ s) := by
  change HasSum (LSeries.term (fun n ↦ if n = k then c else 0) s) (c / (k : ℂ) ^ s)
  refine (hasSum_ite_eq k (c / (k : ℂ) ^ s)).congr_fun ?_
  intro n
  by_cases h : n = k
  · subst n
    simp [hk]
  by_cases hn : n = 0
  · subst n
    simp [h]
  simp [hn, h]

/-- The Dirichlet series of a local quadratic Euler denominator is its evaluation at `p⁻ˢ`. -/
theorem LSeriesHasSum_ofPowerSeries_quadratic {p : ℕ} (hp : 1 < p) (a b s : ℂ) :
    LSeriesHasSum (ofPowerSeries p (1 - PowerSeries.C a * PowerSeries.X +
      PowerSeries.C b * PowerSeries.X ^ 2)) s
      (1 - a / (p : ℂ) ^ s + b / ((p : ℂ) ^ s) ^ 2) := by
  have hp₀ : p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hp)
  have hOne : LSeriesHasSum (fun n ↦ if n = 1 then (1 : ℂ) else 0) s 1 := by
    simpa using LSeriesHasSum_singleCoefficient Nat.one_ne_zero (1 : ℂ) s
  have hLinear := LSeriesHasSum_singleCoefficient hp₀ a s
  have hQuadratic := LSeriesHasSum_singleCoefficient (pow_ne_zero 2 hp₀) b s
  have hPow : (((p ^ 2 : ℕ) : ℂ) ^ s) = ((p : ℂ) ^ s) ^ 2 := by
    simpa only [pow_two, Nat.cast_mul] using Complex.natCast_mul_natCast_cpow p p s
  rw [hPow] at hQuadratic
  refine (LSeriesHasSum_congr s _ ?_).mpr ((hOne.sub hLinear).add hQuadratic)
  intro n _
  exact ofPowerSeries_quadratic_apply hp a b n

/-- The product of finitely many quadratic Euler denominators evaluates termwise
under the absolutely convergent Dirichlet series map. -/
theorem LSeriesHasSum_finiteSeriesRemoval_quadratic (S : Finset ℕ) (a b : ℕ → ℂ) (s : ℂ)
    (hS : ∀ p ∈ S, 1 < p) :
    LSeriesHasSum (finiteSeriesRemoval S (fun p ↦
      1 - PowerSeries.C (a p) * PowerSeries.X + PowerSeries.C (b p) * PowerSeries.X ^ 2)) s
      (∏ p ∈ S, (1 - a p / (p : ℂ) ^ s + b p / ((p : ℂ) ^ s) ^ 2)) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp only [finiteSeriesRemoval, Finset.prod_empty]
      change HasSum (LSeries.term LSeries.delta s) (1 : ℂ)
      exact (hasSum_ite_eq 1 (1 : ℂ)).congr_fun (LSeries.term_delta s)
  | @insert p S hp ih =>
      intro hS
      have hp' : 1 < p := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, 1 < q := fun q hq ↦ hS q (Finset.mem_insert_of_mem hq)
      simpa only [finiteSeriesRemoval, Finset.prod_insert hp] using
        ArithmeticFunction.LSeriesHasSum_mul
          (LSeriesHasSum_ofPowerSeries_quadratic hp' (a p) (b p) s) (ih hS')

/-- The finite quadratic correction has an absolutely convergent Dirichlet series. -/
theorem LSeriesSummable_finiteSeriesRemoval_quadratic (S : Finset ℕ) (a b : ℕ → ℂ) (s : ℂ)
    (hS : ∀ p ∈ S, 1 < p) :
    LSeriesSummable (finiteSeriesRemoval S (fun p ↦
      1 - PowerSeries.C (a p) * PowerSeries.X + PowerSeries.C (b p) * PowerSeries.X ^ 2)) s :=
  (LSeriesHasSum_finiteSeriesRemoval_quadratic S a b s hS).LSeriesSummable

/-- Evaluating the finite quadratic correction yields the product of the local denominators. -/
theorem LSeries_finiteSeriesRemoval_quadratic (S : Finset ℕ) (a b : ℕ → ℂ) (s : ℂ)
    (hS : ∀ p ∈ S, 1 < p) :
    LSeries (finiteSeriesRemoval S (fun p ↦
      1 - PowerSeries.C (a p) * PowerSeries.X + PowerSeries.C (b p) * PowerSeries.X ^ 2)) s =
      ∏ p ∈ S, (1 - a p / (p : ℂ) ^ s + b p / ((p : ℂ) ^ s) ^ 2) :=
  (LSeriesHasSum_finiteSeriesRemoval_quadratic S a b s hS).LSeries_eq

end BSD.General
