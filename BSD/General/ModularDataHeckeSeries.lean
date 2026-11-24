import Mathlib

/-! # Even coefficient extraction and insertion for convergent complex series -/

namespace BSD.General

private theorem hasSum_even_extension (b : ℕ → ℂ) {s : ℂ} (hb : HasSum b s) :
    HasSum (fun n : ℕ => if 2 ∣ n then b (n / 2) else 0) s := by
  refine (Function.Injective.hasSum_iff (mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)) ?_).mp ?_
  · intro n hn
    have h : ¬ 2 ∣ n := by
      rintro ⟨k, hk⟩
      apply hn
      refine ⟨k, ?_⟩
      change 2 * k = n
      omega
    simp [h]
  · simpa [Function.comp_def] using hb

theorem summable_even_filter (a : ℕ → ℂ) (ξ : ℂ)
    (h : Summable (fun n : ℕ => a n * ξ ^ n)) :
    Summable (fun n : ℕ => a (2 * n) * (ξ ^ 2) ^ n) := by
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by
    intro x y hxy
    change 2 * x = 2 * y at hxy
    omega
  simpa [Function.comp_def, pow_mul] using h.comp_injective hi

theorem tsum_even_filter (a : ℕ → ℂ) (ξ : ℂ)
    (hplus : Summable (fun n : ℕ => a n * ξ ^ n))
    (hminus : Summable (fun n : ℕ => a n * (-ξ) ^ n)) :
    ((∑' n : ℕ, a n * ξ ^ n) + (∑' n : ℕ, a n * (-ξ) ^ n)) / 2 =
      ∑' n : ℕ, a (2 * n) * (ξ ^ 2) ^ n := by
  let b : ℕ → ℂ := fun n => a (2 * n) * (ξ ^ 2) ^ n
  have hb : Summable b := summable_even_filter a ξ hplus
  have hext := hasSum_even_extension b hb.hasSum
  have hterm (n : ℕ) :
      (a n * ξ ^ n + a n * (-ξ) ^ n) / 2 =
        if 2 ∣ n then b (n / 2) else 0 := by
    by_cases hn : 2 ∣ n
    · have he : Even n := even_iff_two_dvd.mpr hn
      have hn' : 2 * (n / 2) = n := by omega
      simp only [hn, if_true, b, hn', he.neg_pow]
      rw [← pow_mul, hn']
      ring
    · have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
      simp [hn, ho.neg_pow]
  have havg := (hplus.hasSum.add hminus.hasSum).div_const 2
  have hh := havg.congr_fun (fun n => (hterm n).symm)
  exact hh.unique hext

theorem hasSum_even_insert (a : ℕ → ℂ) (q : ℂ)
    (h : Summable (fun n : ℕ => a n * (q ^ 2) ^ n)) :
    HasSum (fun n : ℕ => (if 2 ∣ n then 2 * a (n / 2) else 0) * q ^ n)
      (2 * ∑' n : ℕ, a n * (q ^ 2) ^ n) := by
  have hb := (h.hasSum.mul_left (2 : ℂ))
  have he := hasSum_even_extension (fun n => 2 * (a n * (q ^ 2) ^ n)) hb
  refine he.congr_fun fun n => ?_
  by_cases hn : 2 ∣ n
  · have hn' : 2 * (n / 2) = n := by omega
    simp only [hn, if_true]
    rw [← pow_mul, hn']
    ring
  · simp [hn]

theorem summable_even_insert (a : ℕ → ℂ) (q : ℂ)
    (h : Summable (fun n : ℕ => a n * (q ^ 2) ^ n)) :
    Summable (fun n : ℕ => (if 2 ∣ n then 2 * a (n / 2) else 0) * q ^ n) :=
  (hasSum_even_insert a q h).summable

theorem tsum_even_insert (a : ℕ → ℂ) (q : ℂ)
    (h : Summable (fun n : ℕ => a n * (q ^ 2) ^ n)) :
    (∑' n : ℕ, (if 2 ∣ n then 2 * a (n / 2) else 0) * q ^ n) =
      2 * ∑' n : ℕ, a n * (q ^ 2) ^ n :=
  (hasSum_even_insert a q h).tsum_eq

end BSD.General
