import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.LFunction

namespace BSD.General

open scoped BigOperators
open ArithmeticFunction

/-- The formal Dirichlet polynomial `1 - z * p ^ (-s)`. -/
noncomputable def localRemoval (p : ℕ) (z : ℂ) : ArithmeticFunction ℂ :=
  ofPowerSeries p (1 - PowerSeries.C z * PowerSeries.X)

/-- The product of the local removal factors over a finite set of primes. -/
noncomputable def finiteRemoval (S : Finset ℕ) (a : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ∏ p ∈ S, localRemoval p (a p)

theorem localRemoval_apply {p : ℕ} (hp : 1 < p) (z : ℂ) (n : ℕ) :
    localRemoval p z n = (if n = 1 then 1 else 0) - (if n = p then z else 0) := by
  by_cases hn : ∃ k : ℕ, p ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    have h₀ : p ^ k = 1 ↔ k = 0 := by
      simpa using (Nat.pow_right_injective hp).eq_iff (a := k) (b := 0)
    have h₁ : p ^ k = p ↔ k = 1 := by
      simpa using (Nat.pow_right_injective hp).eq_iff (a := k) (b := 1)
    rw [localRemoval, ofPowerSeries_apply_pow hp]
    simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, h₀, h₁]
    by_cases hk : k = 1 <;> simp [hk]
  · have h₀ : n ≠ 1 := fun h ↦ hn ⟨0, by simpa using h.symm⟩
    have h₁ : n ≠ p := fun h ↦ hn ⟨1, by simpa using h.symm⟩
    rw [localRemoval, ofPowerSeries_apply hp, Function.extend_apply' _ _ _ hn]
    simp [h₀, h₁]

/-- Taking the coefficients on powers of one prime preserves Dirichlet convolution. -/
private noncomputable def primePowerSeries {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction ℂ →+* PowerSeries ℂ where
  toFun f := PowerSeries.mk fun k ↦ f (p ^ k)
  map_zero' := PowerSeries.ext fun k ↦ by simp
  map_one' := PowerSeries.ext fun k ↦ by
    have hk : p ^ k = 1 ↔ k = 0 := by
      simpa using (Nat.pow_right_injective hp.one_lt).eq_iff (a := k) (b := 0)
    simp only [PowerSeries.coeff_mk, ArithmeticFunction.one_apply, PowerSeries.coeff_one, hk]
  map_add' f g := PowerSeries.ext fun k ↦ by simp
  map_mul' f g := PowerSeries.ext fun k ↦ by
    let e : ℕ ↪ ℕ := ⟨fun i ↦ p ^ i, Nat.pow_right_injective hp.one_lt⟩
    let E : ℕ × ℕ ↪ ℕ × ℕ := e.prodMap e
    have h : (Finset.antidiagonal k).map E = (p ^ k).divisorsAntidiagonal := by
      apply Finset.Subset.antisymm (Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow hp.one_lt k)
      rintro ⟨u, v⟩ huv
      have huv' := (Nat.mem_divisorsAntidiagonal.mp huv).1
      obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨v, huv'.symm⟩
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨p ^ i, by simpa [Nat.mul_comm] using huv'.symm⟩
      rw [← pow_add, Nat.pow_right_inj hp.one_lt] at huv'
      exact Finset.mem_map.mpr ⟨(i, j), Finset.mem_antidiagonal.mpr huv', rfl⟩
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, ArithmeticFunction.mul_apply, ← h,
      Finset.sum_map]
    simp [E, e]

private theorem coeff_primePowerSeries {p : ℕ} (hp : p.Prime)
    (f : ArithmeticFunction ℂ) (k : ℕ) :
    PowerSeries.coeff k (primePowerSeries hp f) = f (p ^ k) := by
  change PowerSeries.coeff k (PowerSeries.mk (fun i ↦ f (p ^ i))) = _
  exact PowerSeries.coeff_mk k _

/-- The geometric local series times its reciprocal polynomial is the unit series. -/
theorem geometric_mul_removal (z : ℂ) :
    (PowerSeries.mk (fun k : ℕ ↦ z ^ k)) * (1 - PowerSeries.C z * PowerSeries.X) = 1 := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [mul_sub, ← mul_assoc]
  | succ k =>
    simp [mul_sub, ← mul_assoc, pow_succ]

/-- The product of the formal local removal series at a finite set of primes. -/
noncomputable def finiteSeriesRemoval (S : Finset ℕ) (f : ℕ → PowerSeries ℂ) :
    ArithmeticFunction ℂ :=
  ∏ p ∈ S, ofPowerSeries p (f p)

/-- The three possible coefficients of a quadratic local removal polynomial. -/
theorem ofPowerSeries_quadratic_apply {p : ℕ} (hp : 1 < p) (u v : ℂ) (n : ℕ) :
    ofPowerSeries p (1 - PowerSeries.C u * PowerSeries.X + PowerSeries.C v * PowerSeries.X ^ 2) n =
      (if n = 1 then 1 else 0) - (if n = p then u else 0) +
      (if n = p ^ 2 then v else 0) := by
  rw [map_add, ArithmeticFunction.add_apply]
  change localRemoval p u n + _ = _
  rw [localRemoval_apply hp]
  congr 1
  by_cases hn : ∃ k : ℕ, p ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    have hk : p ^ k = p ^ 2 ↔ k = 2 := (Nat.pow_right_injective hp).eq_iff
    rw [ofPowerSeries_apply_pow hp, PowerSeries.coeff_C_mul_X_pow]
    simp only [hk]
  · have h₂ : n ≠ p ^ 2 := fun h ↦ hn ⟨2, h.symm⟩
    rw [ofPowerSeries_apply hp, Function.extend_apply' _ _ _ hn]
    simp [h₂]

/-- A sequence satisfying the order-two Euler recurrence has the specified reciprocal
quadratic polynomial as its formal generating series denominator. -/
theorem powerSeries_mul_quadratic_eq_one (c : ℕ → ℂ) (u v : ℂ)
    (hc₀ : c 0 = 1) (hc₁ : c 1 = u)
    (hc : ∀ n : ℕ, c (n + 2) = u * c (n + 1) - v * c n) :
    PowerSeries.mk c *
      (1 - PowerSeries.C u * PowerSeries.X + PowerSeries.C v * PowerSeries.X ^ 2) = 1 := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [pow_two, mul_add, mul_sub, ← mul_assoc, hc₀]
  | succ k =>
    cases k with
    | zero => simp [pow_two, mul_add, mul_sub, ← mul_assoc, hc₀, hc₁]
    | succ k =>
      have hu : c (k + 1) * u = u * c (k + 1) := mul_comm _ _
      have hv : c k * v = v * c k := mul_comm _ _
      simp [pow_two, mul_add, mul_sub, ← mul_assoc, hc k, hu, hv]

private theorem primePowerSeries_ofPowerSeries {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (f : PowerSeries ℂ) (hf : f.constantCoeff = 1) :
    primePowerSeries hp (ofPowerSeries q f) = if q = p then f else 1 := by
  by_cases he : q = p
  · subst q
    rw [if_pos rfl]
    exact PowerSeries.ext fun k ↦ by
      rw [coeff_primePowerSeries, ofPowerSeries_apply_pow hp.one_lt]
  · rw [if_neg he]
    apply PowerSeries.ext
    intro k
    rw [coeff_primePowerSeries]
    cases k with
    | zero => simp [hf]
    | succ k =>
      have hn : ¬ ∃ j : ℕ, q ^ j = p ^ (k + 1) := by
        rintro ⟨j, hj⟩
        have hdiv : p ∣ p ^ (k + 1) := dvd_pow_self _ (Nat.succ_ne_zero k)
        have hdiv' : p ∣ q ^ j := by simpa only [hj] using hdiv
        exact he (Nat.prime_eq_prime_of_dvd_pow hp hq hdiv').symm
      rw [ofPowerSeries_apply hq.one_lt, Function.extend_apply' _ _ _ hn]
      simp

private theorem primePowerSeries_finiteSeriesRemoval {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) (f : ℕ → PowerSeries ℂ) (hS : ∀ q ∈ S, Nat.Prime q)
    (hf : ∀ q ∈ S, (f q).constantCoeff = 1) :
    primePowerSeries hp (finiteSeriesRemoval S f) = if p ∈ S then f p else 1 := by
  classical
  rw [finiteSeriesRemoval, map_prod]
  calc
    (∏ q ∈ S, primePowerSeries hp (ofPowerSeries q (f q))) =
        ∏ q ∈ S, (if q = p then f q else 1) :=
      Finset.prod_congr rfl fun q hq ↦ primePowerSeries_ofPowerSeries hp (hS q hq) (f q) (hf q hq)
    _ = _ := by
      by_cases h : p ∈ S
      · rw [if_pos h]
        exact (Finset.prod_eq_single_of_mem p h (fun q _ hqp ↦ if_neg hqp)).trans
          (if_pos rfl)
      · rw [if_neg h]
        refine Finset.prod_eq_one (fun q hq ↦ if_neg ?_)
        intro e
        exact h (by simpa only [e] using hq)

private theorem constantCoeff_eq_one_of_mul_eq_one
    (A : ArithmeticFunction ℂ) (hA : A.IsMultiplicative) (p : ℕ)
    (f : PowerSeries ℂ) (h : PowerSeries.mk (fun k : ℕ ↦ A (p ^ k)) * f = 1) :
    f.constantCoeff = 1 := by
  have hc := congrArg PowerSeries.constantCoeff h
  simpa [hA.map_one] using hc

/-- Matching good Euler factors suffice for equality after removing the exceptional factors.
The input local reciprocal identities also ensure that the removal factors have unit
constant coefficients. -/
theorem mul_finiteSeriesRemoval_eq (A B : ArithmeticFunction ℂ)
    (hA : A.IsMultiplicative) (hB : B.IsMultiplicative)
    (S : Finset ℕ) (F G : ℕ → PowerSeries ℂ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hgood : ∀ p, Nat.Prime p → p ∉ S → ∀ k : ℕ, A (p ^ k) = B (p ^ k))
    (hbadA : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ A (p ^ k)) * F p = 1)
    (hbadB : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ B (p ^ k)) * G p = 1) :
    A * finiteSeriesRemoval S F = B * finiteSeriesRemoval S G := by
  have hF : ∀ p ∈ S, (F p).constantCoeff = 1 := fun p hp ↦
    constantCoeff_eq_one_of_mul_eq_one A hA p (F p) (hbadA p hp)
  have hG : ∀ p ∈ S, (G p).constantCoeff = 1 := fun p hp ↦
    constantCoeff_eq_one_of_mul_eq_one B hB p (G p) (hbadB p hp)
  have hMF : (finiteSeriesRemoval S F).IsMultiplicative :=
    isMultiplicative_finsetProd _ S fun p hp ↦
      isMultiplicative_ofPowerSeries_of_isPrimePow p (hS p hp).isPrimePow (F p) (hF p hp)
  have hMG : (finiteSeriesRemoval S G).IsMultiplicative :=
    isMultiplicative_finsetProd _ S fun p hp ↦
      isMultiplicative_ofPowerSeries_of_isPrimePow p (hS p hp).isPrimePow (G p) (hG p hp)
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hA.mul hMF) _ (hB.mul hMG)).mpr
  intro p k hp
  have h : primePowerSeries hp (A * finiteSeriesRemoval S F) =
      primePowerSeries hp (B * finiteSeriesRemoval S G) := by
    simp only [map_mul, primePowerSeries_finiteSeriesRemoval hp S F hS hF,
      primePowerSeries_finiteSeriesRemoval hp S G hS hG]
    by_cases hm : p ∈ S
    · simp only [if_pos hm]
      exact (hbadA p hm).trans (hbadB p hm).symm
    · simp only [if_neg hm, mul_one]
      exact PowerSeries.ext fun j ↦ by simp only [coeff_primePowerSeries, hgood p hp hm j]
  simpa only [coeff_primePowerSeries] using congrArg (PowerSeries.coeff k) h

/-- Removing geometric Euler factors at the exceptional primes yields equal multiplicative
Dirichlet series whenever the coefficients agree at all other prime powers. -/
theorem mul_finiteRemoval_eq (A B : ArithmeticFunction ℂ)
    (hA : A.IsMultiplicative) (hB : B.IsMultiplicative)
    (S : Finset ℕ) (a b : ℕ → ℂ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hgood : ∀ p, Nat.Prime p → p ∉ S → ∀ k : ℕ, A (p ^ k) = B (p ^ k))
    (hbadA : ∀ p ∈ S, ∀ k : ℕ, A (p ^ k) = (a p) ^ k)
    (hbadB : ∀ p ∈ S, ∀ k : ℕ, B (p ^ k) = (b p) ^ k) :
    A * finiteRemoval S a = B * finiteRemoval S b := by
  let F (a : ℕ → ℂ) (p : ℕ) : PowerSeries ℂ :=
    1 - PowerSeries.C (a p) * PowerSeries.X
  have hgeom (C : ArithmeticFunction ℂ) (c : ℕ → ℂ)
      (hC : ∀ p ∈ S, ∀ k : ℕ, C (p ^ k) = (c p) ^ k) :
      ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ C (p ^ k)) * F c p = 1 := by
    intro p hp
    have hseries : PowerSeries.mk (fun k : ℕ ↦ C (p ^ k)) =
        PowerSeries.mk (fun k : ℕ ↦ (c p) ^ k) := by
      apply PowerSeries.ext
      intro k
      simpa only [PowerSeries.coeff_mk] using hC p hp k
    rw [hseries]
    exact geometric_mul_removal (c p)
  exact mul_finiteSeriesRemoval_eq A B hA hB S (F a) (F b) hS hgood
    (hgeom A a hbadA) (hgeom B b hbadB)

end BSD.General
