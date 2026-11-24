import BSD.General.ModularCuspContinuation
import BSD.General.ModularPolynomialSeries
import BSD.General.ModularCorrectionPrimePower
import BSD.EulerCoefficients
import BSD.RankStatement

/-! # Meromorphic continuation from a finite Euler-factor comparison -/

open UpperHalfPlane
open scoped CongruenceSubgroup MatrixGroups

namespace BSD.General

/-- A formal Euler denominator of degree at most two. -/
noncomputable def quadraticEulerPolynomial (a b : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C b * PowerSeries.X ^ 2

/-- The finite product of Euler denominators evaluated at the Dirichlet variable. -/
noncomputable def quadraticEulerValue (S : Finset ℕ) (a b : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - a p / (p : ℂ) ^ s + b p / ((p : ℂ) ^ s) ^ 2)

private theorem analyticAt_quadraticEulerValue {S : Finset ℕ} (a b : ℕ → ℂ)
    (hS : ∀ p ∈ S, p.Prime) (s : ℂ) : AnalyticAt ℂ (quadraticEulerValue S a b) s := by
  refine Finset.analyticAt_fun_prod S fun p hp ↦ ?_
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
  have hpow : Differentiable ℂ (fun z : ℂ ↦ (p : ℂ) ^ z) :=
    differentiable_id.const_cpow (.inl hp0)
  have hpow0 : (p : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hp0)
  have hone : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) s := analyticAt_const
  have ha : AnalyticAt ℂ (fun _ : ℂ ↦ a p) s := analyticAt_const
  have hb : AnalyticAt ℂ (fun _ : ℂ ↦ b p) s := analyticAt_const
  exact (hone.sub (ha.div (hpow.analyticAt s) hpow0)).add
    (hb.div ((hpow.analyticAt s).pow 2) (pow_ne_zero 2 hpow0))

/-- A multiplicative Dirichlet series with quadratic local denominators
is recovered by removing the exceptional factors of a comparison series and
restoring those of the original series. -/
theorem LSeriesHasSum_of_quadratic_primePower_comparison (A B : ArithmeticFunction ℂ)
    (hA : A.IsMultiplicative) (hB : B.IsMultiplicative)
    (S : Finset ℕ) (a₁ a₂ b₁ b₂ : ℕ → ℂ) (hS : ∀ p ∈ S, p.Prime)
    (hgood : ∀ p, p.Prime → p ∉ S → ∀ k : ℕ, A (p ^ k) = B (p ^ k))
    (hbadA : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ A (p ^ k)) *
      quadraticEulerPolynomial (a₁ p) (a₂ p) = 1)
    (hbadB : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ B (p ^ k)) *
      quadraticEulerPolynomial (b₁ p) (b₂ p) = 1)
    (hbound : ∀ p ∈ S, ∀ k : ℕ, ‖A (p ^ k)‖ ≤ (p : ℝ) ^ k)
    {s : ℂ} (hs : 1 < s.re) (hsumB : LSeriesSummable B s) :
    LSeriesHasSum A s (LSeries B s * quadraticEulerValue S b₁ b₂ s /
      quadraticEulerValue S a₁ a₂ s) := by
  let D : ℕ → PowerSeries ℂ := fun p ↦ quadraticEulerPolynomial (a₁ p) (a₂ p)
  let G : ℕ → PowerSeries ℂ := fun p ↦ quadraticEulerPolynomial (b₁ p) (b₂ p)
  let R : ℕ → PowerSeries ℂ := fun p ↦ PowerSeries.mk (fun k : ℕ ↦ A (p ^ k))
  have hp (p : ℕ) (hpS : p ∈ S) : 1 < p := (hS p hpS).one_lt
  have hcross := mul_finiteSeriesRemoval_eq A B hA hB S D G hS hgood hbadA hbadB
  have hcancel : finiteSeriesRemoval S D * finiteSeriesRemoval S R = 1 :=
    finiteSeriesRemoval_mul_eq_one S D R fun p hpS ↦
      (mul_comm (D p) (R p)).trans (hbadA p hpS)
  have hrestore : A = B * finiteSeriesRemoval S G * finiteSeriesRemoval S R := calc
    A = (A * finiteSeriesRemoval S D) * finiteSeriesRemoval S R := by
      rw [mul_assoc, hcancel, mul_one]
    _ = (B * finiteSeriesRemoval S G) * finiteSeriesRemoval S R := by rw [hcross]
  have hDa : LSeriesHasSum (finiteSeriesRemoval S D) s (quadraticEulerValue S a₁ a₂ s) :=
    LSeriesHasSum_finiteSeriesRemoval_quadratic S a₁ a₂ s hp
  have hDb : LSeriesHasSum (finiteSeriesRemoval S G) s (quadraticEulerValue S b₁ b₂ s) :=
    LSeriesHasSum_finiteSeriesRemoval_quadratic S b₁ b₂ s hp
  have hR : LSeriesSummable (finiteSeriesRemoval S R) s :=
    lSeriesSummable_finiteSeriesRemoval S R hp
      (fun p hpS k ↦ by simpa only [R, PowerSeries.coeff_mk] using hbound p hpS k) hs
  have hprod : (1 : ℂ) = quadraticEulerValue S a₁ a₂ s * LSeries (finiteSeriesRemoval S R) s := by
    simpa only [hcancel, ArithmeticFunction.one_eq_delta, LSeries_delta, Pi.one_apply] using
      (ArithmeticFunction.LSeriesHasSum_mul hDa hR.LSeriesHasSum).LSeries_eq
  have hne : quadraticEulerValue S a₁ a₂ s ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact one_ne_zero hprod
  have hinv : LSeries (finiteSeriesRemoval S R) s = (quadraticEulerValue S a₁ a₂ s)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hne).mpr
    rw [mul_comm]
    exact hprod.symm
  rw [hrestore]
  simpa only [hinv, div_eq_mul_inv] using
    ArithmeticFunction.LSeriesHasSum_mul
      (ArithmeticFunction.LSeriesHasSum_mul hsumB.LSeriesHasSum hDb) hR.LSeriesHasSum

/-- The modular L-function with the Euler factors corrected at `S`. -/
noncomputable def quadraticCorrectedModularL {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (S : Finset ℕ)
    (a₁ a₂ b₁ b₂ : ℕ → ℂ) (s : ℂ) : ℂ :=
  ModularForm.L (by decide : (0 : ℤ) < 2) f s * quadraticEulerValue S b₁ b₂ s /
    quadraticEulerValue S a₁ a₂ s

/-- The width-one Fourier coefficients of a weight-two cusp form as an arithmetic function. -/
noncomputable def cuspCoefficients {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ (qExpansion 1 f).coeff n,
    CuspFormClass.qExpansion_coeff_zero f zero_lt_one (by simp)⟩

@[simp]
theorem cuspCoefficients_apply {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    cuspCoefficients f n = (qExpansion 1 f).coeff n := rfl

/-- Comparing the formal local factors of a weight-two cusp form and a rational
Weierstrass curve yields a meromorphic continuation of the curve's own series. -/
theorem continues_quadraticCorrectedModularL_of_bound (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : (cuspCoefficients f).IsMultiplicative)
    (S : Finset ℕ) (a₁ a₂ b₁ b₂ : ℕ → ℂ) (hS : ∀ p ∈ S, p.Prime)
    (hgood : ∀ p, p.Prime → p ∉ S → ∀ k : ℕ,
      (E.LFunction (p ^ k) : ℂ) = cuspCoefficients f (p ^ k))
    (hbadA : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ (E.LFunction (p ^ k) : ℂ)) *
      quadraticEulerPolynomial (a₁ p) (a₂ p) = 1)
    (hbadB : ∀ p ∈ S, PowerSeries.mk (fun k : ℕ ↦ cuspCoefficients f (p ^ k)) *
      quadraticEulerPolynomial (b₁ p) (b₂ p) = 1)
    (hbound : ∀ p ∈ S, ∀ k : ℕ, ‖(E.LFunction (p ^ k) : ℂ)‖ ≤ (p : ℝ) ^ k) :
    Continues E (quadraticCorrectedModularL f S a₁ a₂ b₁ b₂) := by
  refine ⟨?_, ?_⟩
  · have hL : Meromorphic (ModularForm.L (by decide : (0 : ℤ) < 2) f) :=
      fun s ↦ ((CuspForm.differentiable_L (by decide : (0 : ℤ) < 2) f).analyticAt s).meromorphicAt
    have hF (c d : ℕ → ℂ) : Meromorphic (quadraticEulerValue S c d) :=
      fun s ↦ (analyticAt_quadraticEulerValue c d hS s).meromorphicAt
    exact (hL.mul (hF b₁ b₂)).div (hF a₁ a₂)
  · intro s hs
    let A : ArithmeticFunction ℂ := ⟨fun n ↦ (E.LFunction n : ℂ), by simp⟩
    have hE := BSD.weierstrass_LFunction_isMultiplicative E
    have hA : A.IsMultiplicative := by
      constructor
      · change (E.LFunction 1 : ℂ) = 1
        simp [hE.map_one]
      · intro m n hmn
        change (E.LFunction (m * n) : ℂ) = (E.LFunction m : ℂ) * (E.LFunction n : ℂ)
        rw [hE.map_mul_of_coprime hmn, Int.cast_mul]
    have hsumB : LSeriesSummable (cuspCoefficients f) s :=
      gamma0_weightTwo_LSeriesSummable f hs
    have h := LSeriesHasSum_of_quadratic_primePower_comparison A (cuspCoefficients f) hA hf
      S a₁ a₂ b₁ b₂ hS hgood hbadA hbadB hbound (by linarith : 1 < s.re) hsumB
    change quadraticCorrectedModularL f S a₁ a₂ b₁ b₂ s = LSeries A s
    simpa only [quadraticCorrectedModularL, gamma0_L_eq_LSeries f hs, cuspCoefficients,
      ArithmeticFunction.coe_mk] using h.LSeries_eq.symm

end BSD.General
