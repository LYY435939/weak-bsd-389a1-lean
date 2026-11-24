import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

/-! The prime-power recurrence implies the coefficient form of the Hecke relation. -/

namespace BSD.General

/-- For a multiplicative arithmetic function, the weight-two good-prime
recurrence implies the Hecke coefficient relation at every natural index.
The index zero is included using the arithmetic function's zero condition. -/
theorem good_hecke_coefficient
    (a : ArithmeticFunction ℂ) (ha : a.IsMultiplicative) {p : ℕ} (hp : p.Prime)
    (hrec : ∀ k : ℕ, a (p ^ (k + 2)) =
      a p * a (p ^ (k + 1)) - (p : ℂ) * a (p ^ k)) (n : ℕ) :
    a (p * n) + (if p ∣ n then (p : ℂ) * a (n / p) else 0) = a p * a n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
    have hc : p.Coprime m := hp.coprime_iff_not_dvd.mpr hm
    have hmul (j : ℕ) : a (p ^ j * m) = a (p ^ j) * a m :=
      ha.map_mul_of_coprime (hc.pow_left j)
    cases k with
    | zero =>
      simpa [hm] using (ha.map_mul_of_coprime hc)
    | succ k =>
      have hn' : p ^ (k + 1) * m = p * (p ^ k * m) := by
        rw [pow_succ]
        ring
      have hn'' : p * (p ^ (k + 1) * m) = p ^ (k + 2) * m := by
        rw [show k + 2 = (k + 1) + 1 by simp [Nat.add_assoc], pow_succ]
        ring
      have hdiv : p ∣ p ^ (k + 1) * m := by rw [hn']; exact dvd_mul_right p _
      have hquot : (p ^ (k + 1) * m) / p = p ^ k * m := by
        rw [hn', Nat.mul_div_cancel_left _ hp.pos]
      simp only [if_pos hdiv, hquot, hn'', hmul]
      rw [hrec k]
      ring

end BSD.General
