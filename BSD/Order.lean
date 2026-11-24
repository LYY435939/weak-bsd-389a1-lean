import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# Central vanishing orders

Derivative criteria for the meromorphic order of a holomorphic function, with
parity constraints from a local functional equation. The completion factor in
the order-two criterion may be any analytic factor nonzero at the center.
-/

open Filter
open scoped Topology

namespace BSD

/-- The finite order at the center equals the index of the first nonzero derivative. -/
theorem meromorphicOrderAt_eq_nat_iff_iteratedDeriv {F : ℂ → ℂ} {c : ℂ}
    {r : ℕ} (hF : AnalyticAt ℂ F c) :
    meromorphicOrderAt F c = (r : WithTop ℤ) ↔
      (∀ i < r, iteratedDeriv i F c = 0) ∧ iteratedDeriv r F c ≠ 0 := by
  rw [← analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hF, hF.meromorphicOrderAt_eq,
    ← WithTop.coe_natCast (α := ℤ) r, ← ENat.map_natCast (Nat.cast : ℕ → ℤ) r]
  exact ENat.map_natCast_inj

/-- A local functional equation at the center restricts each central derivative. -/
theorem iteratedDeriv_reflection {F : ℂ → ℂ} {c ε : ℂ}
    (hFE : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = ε * F (c - z)) (n : ℕ) :
    (-1 : ℂ) ^ n * iteratedDeriv n F c = ε * iteratedDeriv n F c := by
  have h := Filter.EventuallyEq.iteratedDeriv_eq n hFE
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_sub, add_zero, sub_zero, smul_eq_mul] at h
  calc
    (-1 : ℂ) ^ n * iteratedDeriv n F c =
        (-1 : ℂ) ^ n * (ε * ((-1 : ℂ) ^ n * iteratedDeriv n F c)) :=
      congrArg (fun d : ℂ => (-1 : ℂ) ^ n * d) h
    _ = ε * ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * iteratedDeriv n F c := by ac_rfl
    _ = ε * iteratedDeriv n F c := by simp [← mul_pow]

/-- A derivative of parity incompatible with the functional equation vanishes. -/
theorem iteratedDeriv_eq_zero_of_reflection {F : ℂ → ℂ} {c ε : ℂ} {n : ℕ}
    (hFE : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = ε * F (c - z))
    (hne : (-1 : ℂ) ^ n ≠ ε) : iteratedDeriv n F c = 0 := by
  by_contra h
  exact hne (mul_right_cancel₀ h (iteratedDeriv_reflection hFE n))

/-- At finite order, the sign in the functional equation is the parity of the order. -/
theorem rootNumber_eq_neg_one_pow_of_order {F : ℂ → ℂ} {c ε : ℂ} {r : ℕ}
    (hF : AnalyticAt ℂ F c)
    (hFE : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = ε * F (c - z))
    (hOrder : meromorphicOrderAt F c = (r : WithTop ℤ)) : ε = (-1 : ℂ) ^ r := by
  have h := ((meromorphicOrderAt_eq_nat_iff_iteratedDeriv hF).1 hOrder).2
  exact (mul_right_cancel₀ h (iteratedDeriv_reflection hFE r)).symm

/-- With a known functional equation, only derivatives of matching parity must be tested. -/
theorem meromorphicOrderAt_eq_nat_iff_iteratedDeriv_of_reflection
    {F : ℂ → ℂ} {c ε : ℂ} {r : ℕ} (hF : AnalyticAt ℂ F c)
    (hFE : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = ε * F (c - z)) :
    meromorphicOrderAt F c = (r : WithTop ℤ) ↔
      ε = (-1 : ℂ) ^ r ∧
        (∀ i < r, (-1 : ℂ) ^ i = ε → iteratedDeriv i F c = 0) ∧
        iteratedDeriv r F c ≠ 0 := by
  constructor
  · intro hOrder
    obtain ⟨hzero, hne⟩ := (meromorphicOrderAt_eq_nat_iff_iteratedDeriv hF).1 hOrder
    exact ⟨rootNumber_eq_neg_one_pow_of_order hF hFE hOrder, fun i hi _ => hzero i hi, hne⟩
  · rintro ⟨_, hzero, hne⟩
    refine (meromorphicOrderAt_eq_nat_iff_iteratedDeriv hF).2 ⟨?_, hne⟩
    intro i hi
    by_cases he : (-1 : ℂ) ^ i = ε
    · exact hzero i hi he
    · exact iteratedDeriv_eq_zero_of_reflection hFE he

private theorem deriv_eq_zero_of_even {F : ℂ → ℂ} {c : ℂ}
    (hEven : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = F (c - z)) : deriv F c = 0 := by
  have hFE : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = 1 * F (c - z) := by simpa using hEven
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_eq_zero_of_reflection (n := 1) hFE (by simp [CharZero.neg_eq_self_iff])

private theorem meromorphicOrderAt_eq_two {F : ℂ → ℂ} {c : ℂ}
    (hF : AnalyticAt ℂ F c) (hzero : F c = 0) (h₁ : deriv F c = 0)
    (h₂ : iteratedDeriv 2 F c ≠ 0) : meromorphicOrderAt F c = 2 := by
  refine (meromorphicOrderAt_eq_nat_iff_iteratedDeriv (r := 2) hF).2 ⟨?_, h₂⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa only [iteratedDeriv_zero] using hzero
  · simpa only [iteratedDeriv_one] using h₁

/-- For an even function at its center, central vanishing and a nonzero second
derivative suffice for order exactly two. -/
theorem meromorphicOrderAt_eq_two_of_even {F : ℂ → ℂ} {c : ℂ}
    (hF : AnalyticAt ℂ F c)
    (hEven : ∀ᶠ z in 𝓝 (0 : ℂ), F (c + z) = F (c - z))
    (hzero : F c = 0) (h₂ : iteratedDeriv 2 F c ≠ 0) :
    meromorphicOrderAt F c = 2 :=
  meromorphicOrderAt_eq_two hF hzero (deriv_eq_zero_of_even hEven) h₂

/-- If the completed function is even and the analytic completion factor is
nonzero at the center, test central vanishing and the second derivative on the
uncompleted function. -/
theorem meromorphicOrderAt_eq_two_of_completed_even {L A : ℂ → ℂ} {c : ℂ}
    (hL : AnalyticAt ℂ L c) (hA : AnalyticAt ℂ A c) (hA₀ : A c ≠ 0)
    (hEven : ∀ᶠ z in 𝓝 (0 : ℂ), (A * L) (c + z) = (A * L) (c - z))
    (hzero : L c = 0) (h₂ : iteratedDeriv 2 L c ≠ 0) :
    meromorphicOrderAt L c = 2 := by
  have h₁ := deriv_eq_zero_of_even hEven
  rw [deriv_mul hA.differentiableAt hL.differentiableAt, hzero, mul_zero, zero_add] at h₁
  exact meromorphicOrderAt_eq_two hL hzero ((mul_eq_zero.mp h₁).resolve_left hA₀) h₂

end BSD
