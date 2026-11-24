import BSD.CoefficientsConvergence
import BSD.Convergence
import BSD.FourierMellin
import BSD.Mellin
import BSD.RankStatement
import BSD.RationalPoints

/-! # Assembling the rank-zero case for the Fermat cubic

Every arithmetic coefficient comes from the Hasse–Weil Euler factors of
the fixed curve. A comparison with the integral eta coefficients suffices.
-/

open Set

namespace BSD.FermatCubic

noncomputable abbrev curveCoefficient (n : ℕ) : ℂ := (curve.LFunction n : ℤ)

/-- Identification of the eta product on the imaginary axis with the series
whose coefficients come from the actual reductions of the curve. -/
def HasArithmeticFourierExpansion : Prop :=
  ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ ↦ curveCoefficient n *
    (Real.exp (-((2 * Real.pi) * n) * t) : ℂ)) (etaProductAxis t)

/-- Absolute convergence on the half-plane in the formal BSD statement. -/
def AbsolutelyConverges : Prop :=
  ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable curveCoefficient s

theorem absolutelyConverges_of_expansion (hF : HasArithmeticFourierExpansion) :
    AbsolutelyConverges :=
  fun _ hs ↦ lSeriesSummable_of_etaAxis hF hs

theorem etaL_one_ne_zero : etaL 1 ≠ 0 := by
  rw [etaL_one, Complex.ofReal_ne_zero]
  exact etaCentralMellin_pos.ne'

/-- Euler/Fourier coefficient identification suffices to identify a continuation
on the defining half-plane, without evaluating a Dirichlet series at the center. -/
theorem etaL_continues_of_expansion (hF : HasArithmeticFourierExpansion) :
    Continues curve etaL := by
  refine ⟨meromorphic_etaL, fun s hs ↦ ?_⟩
  have h := normalized_mellin_eq_LSeries (c := 2 * Real.pi) (by positivity)
    (a := curveCoefficient) (by simp [curveCoefficient]) hF (by linarith : 0 < s.re)
    (absolutelyConverges_of_expansion hF s hs)
  simpa only [etaL, WeierstrassCurve.LSeries, curveCoefficient, Function.comp_def,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using h

/-- The individual BSD rank statement from an arithmetic Fourier expansion. -/
theorem rankPart_of_expansion (hF : HasArithmeticFourierExpansion) : RankPart curve := by
  apply rankPart_of_derivatives (etaL_continues_of_expansion hF)
    (differentiable_etaL.analyticAt 1) algebraic_rank_zero
  · omega
  · simpa only [iteratedDeriv_zero] using etaL_one_ne_zero

/-- The remaining coefficient comparison is an identity of explicitly defined
integers, with no analytic assumptions. -/
theorem rankPart_of_coefficient_identity
    (h : ∀ n : ℕ, curve.LFunction n = EtaSupport.etaCoeff n) : RankPart curve := by
  apply rankPart_of_expansion
  intro t ht
  simpa only [curveCoefficient, h] using etaProductAxis_hasSum_etaCoeff t ht

end BSD.FermatCubic
