import BSD.RankTwo.ModularSymbolsLocal
import Mathlib.NumberTheory.ModularForms.LFunction

/-! # Connecting the central symbol to Mathlib's cusp-form L-function -/

namespace BSD.RankTwo.ModularSymbols

/-- At weight two, the value at one vanishes when the given periods satisfy the
Manin and Hecke relations and identify the central symbol with the imaginary-axis period. -/
theorem cuspForm_L_one_eq_zero_of_manin
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2) (period : Index → ℂ)
    (hSwap : ∀ i, period i + period (swap i) = 0)
    (hRotate : ∀ i, period i + period (rotate i) + period (rotate (rotate i)) = 0)
    (hHecke : ∀ i, ((heckeTwo i).map period).sum = (traceTwo : ℂ) * period i)
    (hPeriod : period 0 =
      Complex.I * ∫ t in Set.Ioi (0 : ℝ), f (UpperHalfPlane.ofComplex (Complex.I * t))) :
    ModularForm.L (by decide : 0 < (2 : ℤ)) f 1 = 0 := by
  have h := centralPath_eq_zero_of_trace period hSwap hRotate hHecke
  rw [hPeriod] at h
  have hIntegral := (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  simp [ModularForm.L, CuspForm.Λ_eq_mellin, mellin, hIntegral]

end BSD.RankTwo.ModularSymbols
