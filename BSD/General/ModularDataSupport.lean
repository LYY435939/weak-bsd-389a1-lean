import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum

/-! Canonical finite exceptional primes for an integral model and a level. -/

namespace BSD

/-- Prime divisors of six times the level times the absolute discriminant.
This is defined even when the product vanishes; the useful exclusion properties
below require the level and discriminant to be nonzero. -/
def modularExceptionalPrimes (I : WeierstrassCurve ℤ) (N : ℕ) : Finset ℕ :=
  (6 * N * I.Δ.natAbs).divisors.filter Nat.Prime

theorem prime_of_mem_modularExceptionalPrimes (I : WeierstrassCurve ℤ) (N p : ℕ)
    (h : p ∈ modularExceptionalPrimes I N) : p.Prime :=
  (Finset.mem_filter.mp h).2

private theorem not_dvd_exceptional_product (I : WeierstrassCurve ℤ) (N p : ℕ)
    (hN : N ≠ 0) (hΔ : I.Δ ≠ 0) (hp : p.Prime)
    (h : p ∉ modularExceptionalPrimes I N) : ¬ p ∣ 6 * N * I.Δ.natAbs := by
  intro hd
  apply h
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisors.mpr ⟨hd, by simp [hN, hΔ]⟩, hp⟩

theorem five_le_of_not_mem_modularExceptionalPrimes (I : WeierstrassCurve ℤ) (N p : ℕ)
    (hN : N ≠ 0) (hΔ : I.Δ ≠ 0) (hp : p.Prime)
    (h : p ∉ modularExceptionalPrimes I N) : 5 ≤ p := by
  have hd := not_dvd_exceptional_product I N p hN hΔ hp h
  have h2 : p ≠ 2 := by
    intro he
    subst p
    apply hd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 2 ∣ 6) N) _
  have h3 : p ≠ 3 := by
    intro he
    subst p
    apply hd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 3 ∣ 6) N) _
  have h4 : p ≠ 4 := by
    intro he
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have := hp.two_le
  omega

theorem not_dvd_level_of_not_mem_modularExceptionalPrimes (I : WeierstrassCurve ℤ) (N p : ℕ)
    (hN : N ≠ 0) (hΔ : I.Δ ≠ 0) (hp : p.Prime)
    (h : p ∉ modularExceptionalPrimes I N) : ¬ p ∣ N := by
  intro hd
  apply not_dvd_exceptional_product I N p hN hΔ hp h
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 6) _

theorem not_dvd_discriminant_of_not_mem_modularExceptionalPrimes
    (I : WeierstrassCurve ℤ) (N p : ℕ)
    (hN : N ≠ 0) (hΔ : I.Δ ≠ 0) (hp : p.Prime)
    (h : p ∉ modularExceptionalPrimes I N) : ¬ (p : ℤ) ∣ I.Δ := by
  intro hd
  apply not_dvd_exceptional_product I N p hN hΔ hp h
  exact dvd_mul_of_dvd_right (Int.natCast_dvd.mp hd) _

end BSD
