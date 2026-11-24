import Theorems.Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
import Theorems.Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd
import Theorems.Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd
import Theorems.Thm_WeierstrassCurve_modThreeOrFiveIrreducible
import Theorems.Thm_WeierstrassCurve_threeFiveSwitchCurve
import Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch

namespace BSD.RankTwo.FLTAdapter

open WeierstrassCurve

/-- This proof composes six public FLT rows. It retains the exact-conductor witness
from both branches of the upstream proof of modularity of a semistable model. -/
theorem exact_of_semistable (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) : Mlc1IsModularModelOfExactConductorLevel W := by
  by_cases h3 : W.ModRepIsIrreducible 3
  · obtain ⟨M, hM, hr, hc, hi⟩ :=
      isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
        W hΔ hW h3
    let : NeZero M := ⟨hM.ne'⟩
    exact modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd
      3 rfl W hΔ hW h3 M hr hi hc
  · have h5 := (modThreeOrFiveIrreducible W hΔ hW).resolve_left h3
    obtain ⟨W', hd, hw, hi, hcong⟩ := threeFiveSwitchCurve W hΔ hW h5
    obtain ⟨M, hM, hr, hc, hns⟩ :=
      isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
        W' hd hw hi
    let : NeZero M := ⟨hM.ne'⟩
    obtain ⟨N, hN, hsq, hsupp, hmodN⟩ :=
      modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd
        3 rfl W' hd hw hi M hr hns hc
    have hr5 := isResiduallyModularOfLevel_of_switch hmodN
      (fun ℓ hℓ h ↦ (hsupp ℓ hℓ).mpr h) hcong
    have h25 : ¬ 5 ^ 2 ∣ N := by
      intro h
      have hu : IsUnit (5 : ℕ) := hsq 5 (by rwa [← pow_two])
      exact absurd (Nat.isUnit_iff.mp hu) (by decide)
    have hc5 : ∀ q : ℕ, q.Prime → q ≠ 5 → ¬ q^3 ∣ N := fun q hq _ h ↦
      hq.ne_one (Nat.isUnit_iff.mp (hsq q ((Dvd.intro q (by ring)).trans h)))
    let : NeZero N := ⟨hN.ne'⟩
    exact modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd
      5 (Or.inr rfl) W hΔ hW h5 N hr5 h25 hc5

end BSD.RankTwo.FLTAdapter
