import BSD.RankTwo.SmallEuler
import BSD.RankTwo.ModularSymbols
import Mathlib.Data.Nat.Squarefree

/-! # Model computations for the level-389 modular-symbol certificate -/

namespace BSD.RankTwo.ModularSymbols

private instance : (model (ZMod 2)).IsElliptic := by
  constructor
  rw [discriminant]
  exact isUnit_iff_ne_zero.mpr (by decide)

/-- Direct count of the reduced model's affine points and the point at infinity. -/
theorem card_points_mod_two : Nat.card (model (ZMod 2)).toAffine.Point = 5 :=
  card_model_of_affine_card 4 (by decide)

/-- Trace of the Frobenius on the good reduction of the given model at 2. -/
noncomputable def traceTwo : ℤ :=
  2 + 1 - Nat.card (model (ZMod 2)).toAffine.Point

theorem traceTwo_eq : traceTwo = -2 := by
  rw [traceTwo, card_points_mod_two]
  norm_num

theorem c4_eq {R : Type*} [CommRing R] : (model R).c₄ = 112 := by
  simp only [model, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- The integral model satisfies the coprimality test for semistability. -/
theorem discriminant_c4_coprime : IsCoprime (model ℤ).Δ (model ℤ).c₄ := by
  rw [discriminant, c4_eq]
  exact ⟨-19, 66, by norm_num⟩

/-- No prime divides both invariants of the integral model. This is the
semistable-model predicate used in Anthropic's FLT formalization. -/
theorem isSemistableModel :
    ∀ (p : ℕ), p.Prime → (p : ℤ) ∣ (model ℤ).Δ → ¬ (p : ℤ) ∣ (model ℤ).c₄ := by
  intro p hp hΔ hc₄
  have hu := discriminant_c4_coprime.isRelPrime hΔ hc₄
  exact hp.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.mp hu)

/-- A squarefree level with the prime support of this model's discriminant is 389. -/
theorem conductor_eq_389_of_squarefree_support {N : ℕ} (hSquarefree : Squarefree N)
    (hSupport : ∀ (p : ℕ), p.Prime → (p ∣ N ↔ (p : ℤ) ∣ (model ℤ).Δ)) :
    N = 389 := by
  have hPrime : Nat.Prime 389 := by norm_num
  have hDvd : 389 ∣ N := (hSupport 389 hPrime).2 (by
    rw [discriminant]
    exact ⟨1, by norm_num⟩)
  obtain ⟨m, rfl⟩ := hDvd
  suffices m = 1 by simp [this]
  by_contra hm
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm
  have hpd := (hSupport p hp).1 (dvd_mul_of_dvd_right hpm 389)
  rw [discriminant] at hpd
  have hp389 : p ∣ 389 := by exact_mod_cast hpd
  have he : p = 389 := ((Nat.dvd_prime hPrime).1 hp389).resolve_left hp.ne_one
  subst p
  exact (Nat.squarefree_iff_prime_squarefree.1 hSquarefree 389 hPrime)
    (Nat.mul_dvd_mul_left 389 hpm)

/-- Use the model's point count for the Hecke relation in the finite certificate. -/
theorem centralPath_eq_zero_of_trace {K : Type*} [Field K] [CharZero K] (period : Index → K)
    (hSwap : ∀ i, period i + period (swap i) = 0)
    (hRotate : ∀ i, period i + period (rotate i) + period (rotate (rotate i)) = 0)
    (hHecke : ∀ i, ((heckeTwo i).map period).sum = (traceTwo : K) * period i) : period 0 = 0 := by
  rw [traceTwo_eq] at hHecke
  push_cast at hHecke
  exact centralPath_eq_zero period hSwap hRotate hHecke

end BSD.RankTwo.ModularSymbols
