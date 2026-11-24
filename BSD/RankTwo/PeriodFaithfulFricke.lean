import BSD.RankTwo.BadHecke

/-! The prime-level Fricke slash, packaged as a cusp form. -/

namespace BSD.RankTwo

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The weight-two Fricke transform of a cusp form of prime level. -/
noncomputable def frickeCusp (p : ℕ) [Fact p.Prime] (f : CuspForm (Gamma0 p) 2) :
    CuspForm (Gamma0 p) 2 :=
  Classical.choose (exists_fricke_cuspForm p f)

/-- On functions, `frickeCusp` is exactly the Fricke slash of `PeriodBridge`. -/
theorem coe_frickeCusp (p : ℕ) [Fact p.Prime] (f : CuspForm (Gamma0 p) 2) :
    (⇑(frickeCusp p f) : ℍ → ℂ) =
      ⇑f ∣[(2 : ℤ)] weightTwoFricke p (by exact_mod_cast (Fact.out : p.Prime).pos) := by
  exact Classical.choose_spec (exists_fricke_cuspForm p f)

end BSD.RankTwo
