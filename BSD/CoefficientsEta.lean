import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import BSD.Eta

/-! Stable integral coefficients of the finite Euler products for η(3z)²η(9z)². -/

noncomputable section
open PowerSeries
namespace EtaSupport

/-- Finite product in t: ∏_{j=1}^N (1-t^j)^2(1-t^(3j))^2. -/
def product (N : ℕ) : ℤ⟦X⟧ :=
  ∏ j ∈ Finset.range N, ((1 - (X : ℤ⟦X⟧) ^ (j+1))^2 *
    (1 - X ^ (3*(j+1)))^2)
/-- The eta product truncation, with t=q^3 and leading q. -/
def etaTrunc (N : ℕ) : ℤ⟦X⟧ := X * (product N).expand 3 (by decide)
theorem etaTrunc_eq_direct (N : ℕ) : etaTrunc N =
    X * ∏ j ∈ Finset.range N, ((1 - (X : ℤ⟦X⟧)^(3*(j+1)))^2 *
      (1 - X^(9*(j+1)))^2) := by
  simp only [etaTrunc, product, map_prod, map_mul, map_pow, map_sub, map_one, expand_X]
  apply congrArg ((X : ℤ⟦X⟧) * ·)
  apply Finset.prod_congr rfl
  intro j hj
  congr 3 <;> rw [← pow_mul]
  congr 1
  omega

theorem support_general (f : ℤ⟦X⟧) (n : ℕ) (h : n % 3 ≠ 1) :
    coeff n (X * f.expand 3 (by decide)) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_expand_of_not_dvd]
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    apply h
    omega
theorem etaTrunc_support (N n : ℕ) (h : n % 3 ≠ 1) :
    coeff n (etaTrunc N) = 0 := support_general _ _ h
/-- Polynomial whose coercion is exactly the finite formal product. -/
def etaPoly (N : ℕ) : Polynomial ℤ :=
    Polynomial.X * ∏ j ∈ Finset.range N,
      ((1 - (Polynomial.X : Polynomial ℤ)^(3*(j+1)))^2 *
        (1 - Polynomial.X^(9*(j+1)))^2)

theorem etaPoly_coe (N : ℕ) : (etaPoly N : ℤ⟦X⟧) = etaTrunc N := by
  rw [etaTrunc_eq_direct]
  change Polynomial.coeToPowerSeries.ringHom (etaPoly N) = _
  rw [etaPoly, map_mul, map_prod]
  simp

/-- Evaluation of the same integral polynomial in the complex plane. -/
theorem etaPoly_eval (N : ℕ) (q : ℂ) :
    (etaPoly N).eval₂ (Int.castRingHom ℂ) q =
      q * ∏ j ∈ Finset.range N,
        ((1 - q^(3*(j+1)))^2 * (1-q^(9*(j+1)))^2) := by
  change Polynomial.eval₂RingHom (Int.castRingHom ℂ) q (etaPoly N) = _
  rw [etaPoly, map_mul, map_prod]
  simp [Polynomial.eval₂_pow, Polynomial.eval₂_sub]

/-- Each omitted Euler factor is one modulo the next power of t. -/
lemma factor_shape (k : ℕ) :
    (1 - (X : ℤ⟦X⟧)^k)^2 * (1 - X^(3*k))^2 =
      1 + X^k * ((X^k-2) + (1-X^k)^2 * ((X^k)^3-2) * (X^k)^2) := by
  rw [show 3*k = k*3 by omega, pow_mul]
  ring

lemma product_step_coeff (N d : ℕ) (hd : d ≤ N) :
    coeff d (product (N+1)) = coeff d (product N) := by
  rw [product, Finset.prod_range_succ]
  change coeff d (product N * _) = _
  rw [factor_shape]
  rw [mul_add, mul_one, map_add]
  rw [mul_left_comm (product N) ((X : ℤ⟦X⟧) ^ (N+1))]
  rw [coeff_X_pow_mul', if_neg (by omega), add_zero]

lemma product_coeff_stable (d N : ℕ) (h : d ≤ N) :
    coeff d (product N) = coeff d (product d) := by
  induction N with
  | zero =>
    have hd0 : d = 0 := by omega
    subst d
    rfl
  | succ N ih =>
    by_cases hdn : d ≤ N
    · rw [product_step_coeff N d hdn, ih hdn]
    · have hdeq : d = N+1 := by omega
      subst d
      rfl

/-- The diagonal is a genuine stabilized coefficient of the finite products. -/
theorem etaTrunc_coeff_stable (n N : ℕ) (hN : n ≤ N) :
    coeff n (etaTrunc N) = coeff n (etaTrunc n) := by
  cases n with
  | zero => simp [etaTrunc]
  | succ n =>
    simp only [etaTrunc, coeff_succ_X_mul, coeff_expand]
    split_ifs with h
    · rw [product_coeff_stable (n / 3) N (by omega),
          product_coeff_stable (n / 3) (n+1) (by omega)]
    · rfl

/-- Coefficients extracted from the natural diagonal of the finite products. -/
def etaCoeff (n : ℕ) : ℤ := coeff n (etaTrunc n)
theorem etaCoeff_support (n : ℕ) (h : n % 3 ≠ 1) : etaCoeff n = 0 :=
  etaTrunc_support n n h
/-- Formal infinite product, defined by its stable finite-product coefficients. -/
def etaSeries : ℤ⟦X⟧ := PowerSeries.mk etaCoeff

theorem etaSeries_coeff_eq_trunc (n N : ℕ) (h : n ≤ N) :
    coeff n etaSeries = coeff n (etaTrunc N) := by
  rw [etaSeries, coeff_mk, etaCoeff]
  exact (etaTrunc_coeff_stable n N h).symm

theorem etaSeries_support (n : ℕ) (h : n % 3 ≠ 1) :
    coeff n etaSeries = 0 := by
  rw [etaSeries, coeff_mk]
  exact etaCoeff_support n h

open Filter
open scoped Topology BigOperators

def axisQ (t : ℝ) : ℂ := (Real.exp (-2 * Real.pi * t) : ℂ)

lemma axisQ_mul (t : ℝ) (k : ℕ) : axisQ (k*t) = axisQ t ^ k := by
  simp only [axisQ, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma axisQ_norm_lt_one {t : ℝ} (ht : 0 < t) : ‖axisQ t‖ < 1 := by
  rw [axisQ, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_lt_one_iff]
  nlinarith [Real.pi_pos]

lemma eta_axis_eq (u : ℝ) :
    ModularForm.eta (((u : ℝ) : ℂ) * Complex.I) =
      (Real.exp (-2 * Real.pi * u / 24) : ℂ) *
        ∏' n : ℕ, (1 - (axisQ u)^(n+1)) := by
  simp [ModularForm.eta, ModularForm.eta_q, BSD.FermatCubic.qParam_axis, axisQ]

lemma axis_prefactors (t : ℝ) :
    (Real.exp (-2 * Real.pi * (3*t) / 24) : ℂ)^2 *
      (Real.exp (-2 * Real.pi * (9*t) / 24) : ℂ)^2 = axisQ t := by
  simp only [axisQ, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Analytic eta values are the limit of the same integer polynomials
    whose stable coefficients define etaSeries. -/
theorem etaPoly_tendsto_axis (t : ℝ) (ht : 0 < t) :
    Tendsto (fun N : ℕ ↦ (etaPoly N).eval₂ (Int.castRingHom ℂ) (axisQ t))
      atTop (𝓝 (BSD.FermatCubic.etaProductAxis t)) := by
  let q := axisQ t
  have hq : ‖q‖ < 1 := axisQ_norm_lt_one ht
  have h3 : ‖q^3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  have h9 : ‖q^9‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  let a (n : ℕ) : ℂ := 1 - (q^3)^(n+1)
  let b (n : ℕ) : ℂ := 1 - (q^9)^(n+1)
  have ha : Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.range N, a n) atTop (𝓝 (∏' n, a n)) :=
    (ModularForm.multipliable_one_sub_pow h3).hasProd.tendsto_prod_nat
  have hb : Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.range N, b n) atTop (𝓝 (∏' n, b n)) :=
    (ModularForm.multipliable_one_sub_pow h9).hasProd.tendsto_prod_nat
  have hlim : Tendsto (fun N : ℕ ↦ q * ((∏ n ∈ Finset.range N, a n)^2 *
      (∏ n ∈ Finset.range N, b n)^2)) atTop
      (𝓝 (q * ((∏' n, a n)^2 * (∏' n, b n)^2))) :=
    tendsto_const_nhds.mul ((ha.pow 2).mul (hb.pow 2))
  have hseq (N : ℕ) : (etaPoly N).eval₂ (Int.castRingHom ℂ) (axisQ t) =
      q * ((∏ n ∈ Finset.range N, a n)^2 * (∏ n ∈ Finset.range N, b n)^2) := by
    rw [etaPoly_eval, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply congrArg (q * ·)
    apply Finset.prod_congr rfl
    intro n hn
    simp [a, b, q, pow_mul]
  have htarget : BSD.FermatCubic.etaProductAxis t = q * ((∏' n, a n)^2 * (∏' n, b n)^2) := by
    have hq3 : axisQ (3*t) = q^3 := by simpa [q] using axisQ_mul t 3
    have hq9 : axisQ (9*t) = q^9 := by simpa [q] using axisQ_mul t 9
    rw [BSD.FermatCubic.etaProductAxis, eta_axis_eq, eta_axis_eq, hq3, hq9]
    change _ = axisQ t * _
    rw [← axis_prefactors t]
    ring
  simpa only [← hseq, ← htarget] using hlim

end EtaSupport
