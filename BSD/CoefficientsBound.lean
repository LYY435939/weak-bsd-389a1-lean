import BSD.CoefficientsEta

/-! Uniform coefficient estimates for the polynomials defining the eta product. -/

namespace EtaSupport
open Polynomial

private def boundedAt (P : Polynomial ℤ) (r C : ℝ) :=
  ∀ n : ℕ, ‖((P.coeff n : ℤ) : ℂ)‖ * r^n ≤ C

/-- One Euler factor costs at most $1+r^k$ in the weighted coefficient estimate. -/
private theorem bound_euler_factor {P : Polynomial ℤ} {r C : ℝ} (hr : 0 ≤ r)
    (hC : 0 ≤ C) (h : boundedAt P r C) (k : ℕ) :
    boundedAt (P*(1-X^k)) r (C*(1+r^k)) := by
  intro n
  rw [mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow']
  split_ifs with hkn
  · push_cast
    calc
      _ ≤ (‖((P.coeff n : ℤ) : ℂ)‖ + ‖((P.coeff (n-k) : ℤ) : ℂ)‖) * r^n :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg hr _)
      _ = ‖((P.coeff n : ℤ) : ℂ)‖ * r^n + (‖((P.coeff (n-k) : ℤ) : ℂ)‖ * r^(n-k)) * r^k := by
        rw [add_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hkn]
      _ ≤ C + C*r^k := add_le_add (h n) (mul_le_mul_of_nonneg_right (h _) (pow_nonneg hr _))
      _ = _ := by ring
  · simp only [sub_zero]
    exact (h n).trans (by nlinarith [mul_nonneg hC (pow_nonneg hr k)])

private theorem etaPoly_bound_partial {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    boundedAt (etaPoly N) r (Real.exp (4 * ∑ j ∈ Finset.range N, r ^ j)) := by
  induction N with
  | zero =>
    intro n
    simp only [etaPoly, Finset.range_zero, Finset.prod_empty, mul_one, Finset.sum_empty,
      mul_zero, Real.exp_zero, Polynomial.coeff_X]
    split_ifs with he
    · subst n
      simpa using hr1.le
    · simp
  | succ N ih =>
    let C := Real.exp (4 * ∑ j ∈ Finset.range N, r ^ j)
    let k := 3*(N+1)
    let l := 9*(N+1)
    have hC : 0 ≤ C := (Real.exp_pos _).le
    have hk : 0 ≤ r ^ k := pow_nonneg hr.le _
    have hl : 0 ≤ r ^ l := pow_nonneg hr.le _
    have hk1 : 0 ≤ 1+r^k := by positivity
    have hl1 : 0 ≤ 1+r^l := by positivity
    have h1 := bound_euler_factor hr.le hC ih k
    have h2 := bound_euler_factor hr.le (mul_nonneg hC hk1) h1 k
    have h3 := bound_euler_factor hr.le (mul_nonneg (mul_nonneg hC hk1) hk1) h2 l
    have h4 := bound_euler_factor hr.le (mul_nonneg (mul_nonneg (mul_nonneg hC hk1) hk1) hl1) h3 l
    have he : etaPoly (N+1) = etaPoly N * (1-X^k) * (1-X^k) * (1-X^l) * (1-X^l) := by
      simp only [etaPoly, Finset.prod_range_succ, k, l]
      ring
    have hk' : 1+r^k ≤ Real.exp (r^N) :=
      (by linarith [(pow_le_pow_of_le_one hr.le hr1.le (show N ≤ k by dsimp [k]; omega)),
        Real.add_one_le_exp (r^N)])
    have hl' : 1+r^l ≤ Real.exp (r^N) :=
      (by linarith [(pow_le_pow_of_le_one hr.le hr1.le (show N ≤ l by dsimp [l]; omega)),
        Real.add_one_le_exp (r^N)])
    intro n
    rw [he]
    apply (h4 n).trans
    calc
      _ ≤ C * Real.exp (r^N) * Real.exp (r^N) * Real.exp (r^N) * Real.exp (r^N) := by
        gcongr
      _ = _ := by
        dsimp [C]
        simp only [← Real.exp_add, Finset.sum_range_succ]
        congr 1
        ring

/-- A bound uniform in both the polynomial cutoff and coefficient degree, on each
smaller circle inside the unit disk. -/
theorem etaPoly_coeff_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, ∀ N n : ℕ, ‖(((etaPoly N).coeff n : ℤ) : ℂ)‖ * r^n ≤ C := by
  refine ⟨Real.exp (4 * ∑' j : ℕ, r ^ j), fun N n => (etaPoly_bound_partial hr hr1 N n).trans ?_⟩
  apply Real.exp_le_exp.mpr
  gcongr
  exact (summable_geometric_of_lt_one hr.le hr1).sum_le_tsum _ fun i _ => pow_nonneg hr.le i

end EtaSupport
