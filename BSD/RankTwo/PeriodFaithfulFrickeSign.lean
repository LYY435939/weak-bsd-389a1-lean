import BSD.RankTwo.PeriodFaithfulFricke
import BSD.RankTwo.PeriodFaithful
import BSD.RankTwo.PeriodFaithfulLinear

/-! From an anti-Fricke period identity to the Fricke eigenvalue. -/

namespace BSD.RankTwo

open CongruenceSubgroup UpperHalfPlane
open BSD.General.PeriodsRelative
open scoped MatrixGroups ModularForm

/-- If every rational period of the Fricke transform is the negative of the
corresponding period of `f`, then `f` has Fricke eigenvalue `-1`. -/
theorem fricke_slash_eq_neg_of_anti_periods
    (p : ℕ) [Fact p.Prime] (f : CuspForm (Gamma0 p) 2)
    (hperiod : ∀ a b, cuspFormPeriod (frickeCusp p f) a b + cuspFormPeriod f a b = 0) :
    (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke p
      (by exact_mod_cast (Fact.out : p.Prime).pos) = -⇑f := by
  have hzero : frickeCusp p f + f = 0 := by
    apply PeriodFaithful.eq_zero_of_periods_zero
    intro a b
    rw [PeriodFaithfulLinear.cuspFormPeriod_add_forms]
    exact hperiod a b
  have hneg : frickeCusp p f = -f := eq_neg_of_add_eq_zero_left hzero
  calc
    (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke p
        (by exact_mod_cast (Fact.out : p.Prime).pos) = ⇑(frickeCusp p f) :=
      (coe_frickeCusp p f).symm
    _ = -⇑f := by rw [hneg]; rfl

end BSD.RankTwo
