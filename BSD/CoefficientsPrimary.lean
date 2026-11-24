import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace BSD

private def eisensteinNorm {R : Type*} [Ring R] (a b : R) : R :=
  a ^ 2 - a * b + b ^ 2

private theorem intCast_eisensteinNorm {n : ℕ} (a b : ℤ) :
    ((eisensteinNorm a b : ℤ) : ZMod n) = eisensteinNorm (a : ZMod n) (b : ZMod n) := by
  simp [eisensteinNorm]

private theorem eisenstein_cross_primary_norm_eq {p : ℕ} [hp : Fact p.Prime]
    {a b c d : ℤ} (hab : eisensteinNorm a b = (p : ℤ)) (hcd : eisensteinNorm c d = (p : ℤ))
    (ha : (a : ZMod 3) = 1) (hb : (b : ZMod 3) = 0)
    (hc : (c : ZMod 3) = 1) (hd : (d : ZMod 3) = 0)
    (hs : (p : ℤ) ∣ b * c - a * d) : 2 * a - b = 2 * c - d := by
  let r := a * c - a * d + b * d
  let s := b * c - a * d
  have hrs : eisensteinNorm r s = (p : ℤ) ^ 2 := by
    calc
      eisensteinNorm r s = eisensteinNorm a b * eisensteinNorm c d := by
        unfold eisensteinNorm r s
        ring
      _ = _ := by rw [hab, hcd, pow_two]
  have hsₚ : (s : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd s p).mpr hs
  have hrsₚ := congrArg (fun z : ℤ ↦ (z : ZMod p)) hrs
  rw [intCast_eisensteinNorm] at hrsₚ
  have hrₚ : (r : ZMod p) = 0 := by
    simpa [eisensteinNorm, hsₚ] using hrsₚ
  obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mp hrₚ
  obtain ⟨y, hy⟩ := hs
  change s = (p : ℤ) * y at hy
  have hp₃ : (p : ZMod 3) = 1 := by
    have h := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hab
    rw [intCast_eisensteinNorm] at h
    simpa [eisensteinNorm, ha, hb] using h.symm
  have hx₃ : (x : ZMod 3) = 1 := by
    have h := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hx.symm
    simpa [r, ha, hb, hc, hd, hp₃] using h
  have hy₃ : (y : ZMod 3) = 0 := by
    have h := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hy.symm
    simpa [s, ha, hb, hc, hd, hp₃] using h
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hxy : eisensteinNorm x y = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hpz)
    calc
      (p : ℤ) ^ 2 * eisensteinNorm x y = eisensteinNorm ((p : ℤ) * x) ((p : ℤ) * y) := by
        unfold eisensteinNorm
        ring
      _ = (p : ℤ) ^ 2 * 1 := by rw [← hx, ← hy, hrs, mul_one]
  have hy0 : y = 0 := by
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hy₃
    change y = 3 * k at hk
    by_contra h
    have hk0 : k ≠ 0 := by
      intro h0
      apply h
      simp [hk, h0]
    have hk1 : 1 ≤ k ^ 2 := by have := sq_pos_of_ne_zero hk0; omega
    have hbound : (2 * x - y) ^ 2 + 3 * y ^ 2 = 4 := by
      unfold eisensteinNorm at hxy
      linear_combination 4 * hxy
    rw [hk] at hbound
    nlinarith only [hbound, hk1, sq_nonneg (2 * x - 3 * k)]
  have hx1 : x = 1 := by
    have hxSq : x ^ 2 = 1 := by simpa [eisensteinNorm, hy0] using hxy
    rcases sq_eq_one_iff.mp hxSq with rfl | rfl
    · rfl
    · exact (show (-1 : ZMod 3) ≠ 1 by decide) hx₃ |>.elim
  have hr : r = (p : ℤ) := by simpa [hx1] using hx
  have hs0 : s = 0 := by simpa [hy0] using hy
  have hap : (p : ℤ) * (a - c) = 0 := by
    calc
      _ = c * (r - (p : ℤ)) - d * s := by
        unfold eisensteinNorm at hcd
        dsimp only [r, s]
        linear_combination -a * hcd
      _ = 0 := by rw [hr, hs0]; ring
  have hbp : (p : ℤ) * (b - d) = 0 := by
    calc
      _ = d * (r - (p : ℤ)) + (c - d) * s := by
        unfold eisensteinNorm at hcd
        dsimp only [r, s]
        linear_combination -b * hcd
      _ = 0 := by rw [hr, hs0]; ring
  rw [sub_eq_zero.mp ((mul_eq_zero.mp hap).resolve_left hpz),
    sub_eq_zero.mp ((mul_eq_zero.mp hbp).resolve_left hpz)]

/-- The trace of a norm-(p) Eisenstein integer with coordinates (1,0) modulo three is unique. -/
theorem eisenstein_primary_trace_eq {p : ℕ} (hp : p.Prime) {a b c d : ℤ}
    (hab : a ^ 2 - a * b + b ^ 2 = (p : ℤ)) (hcd : c ^ 2 - c * d + d ^ 2 = (p : ℤ))
    (ha : 3 ∣ a - 1) (hb : 3 ∣ b) (hc : 3 ∣ c - 1) (hd : 3 ∣ d) :
    2 * a - b = 2 * c - d := by
  let : Fact p.Prime := ⟨hp⟩
  change eisensteinNorm a b = (p : ℤ) at hab
  change eisensteinNorm c d = (p : ℤ) at hcd
  have ha₃ : (a : ZMod 3) = 1 := sub_eq_zero.mp (by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) 3).mpr ha)
  have hb₃ : (b : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mpr hb
  have hc₃ : (c : ZMod 3) = 1 := sub_eq_zero.mp (by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (c - 1) 3).mpr hc)
  have hd₃ : (d : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mpr hd
  have habₚ : eisensteinNorm (a : ZMod p) (b : ZMod p) = 0 := by
    rw [← intCast_eisensteinNorm, hab]; simp
  have hcdₚ : eisensteinNorm (c : ZMod p) (d : ZMod p) = 0 := by
    rw [← intCast_eisensteinNorm, hcd]; simp
  have hcross : ((b : ZMod p) * c - a * d) * ((b : ZMod p) * c + (a - b : ZMod p) * d) = 0 := by
    unfold eisensteinNorm at habₚ hcdₚ
    linear_combination (b : ZMod p) ^ 2 * hcdₚ - (d : ZMod p) ^ 2 * habₚ
  rcases mul_eq_zero.mp hcross with h | h
  · apply eisenstein_cross_primary_norm_eq hab hcd ha₃ hb₃ hc₃ hd₃
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (b * c - a * d) p).mp
    push_cast
    exact h
  · have hcd' : eisensteinNorm (c - d) (-d) = (p : ℤ) := by
      unfold eisensteinNorm at hcd ⊢
      linear_combination hcd
    have hc₃' : ((c - d : ℤ) : ZMod 3) = 1 := by simp [hc₃, hd₃]
    have hd₃' : ((-d : ℤ) : ZMod 3) = 0 := by simp [hd₃]
    have hs : (p : ℤ) ∣ b * (c - d) - a * -d := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      linear_combination h
    have htrace := eisenstein_cross_primary_norm_eq hab hcd' ha₃ hb₃ hc₃' hd₃' hs
    linear_combination htrace

end BSD
