import BSD.RankTwo.BadHecke
import BSD.RankTwo.FromModularityBadFourier

/-! The Fricke eigenvalue fixes the Fourier coefficient at the level prime. -/

namespace BSD.RankTwo

open BSD.General CongruenceSubgroup UpperHalfPlane
open scoped ModularForm

/-- For a normalized level-389 eigenform in the minus Fricke eigenspace, the
coefficient at 389 is one. -/
theorem bad_trace_of_fricke
    (f : CuspForm (Gamma0 389) 2) (hf : ModularCoefficientData f)
    (hw : (f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke 389 (by norm_num) = -(f : ℍ → ℂ)) :
    cuspCoefficients f 389 = 1 := by
  let : Fact (Nat.Prime 389) := ⟨by norm_num⟩
  have hu : badHecke 389 f = (f : ℍ → ℂ) := by
    simpa only [Nat.cast_ofNat, hw, neg_neg] using badHecke_eq_neg_fricke 389 f
  apply bad_trace_of_average f hf
  intro τ
  have h := congrFun hu τ
  rw [badHecke_apply] at h
  exact ((div_eq_iff (by norm_num : (389 : ℂ) ≠ 0)).mp h).trans (mul_comm _ _)

end BSD.RankTwo
