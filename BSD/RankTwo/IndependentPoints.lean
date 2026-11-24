import BSD.RankTwo.Curve
import BSD.RankTwo.HalvingPolynomials
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Two independent rational points on 389.a1

The points `P`, `Q`, and `P + Q` are outside the image of doubling. A relation
between `P` and `Q` must therefore have both coefficients even. Halving
the coefficients preserves the relation because the rational point group has
trivial 2-torsion. Descent on the sum of their absolute values proves independence.
-/

namespace BSD.RankTwo

open WeierstrassCurve.Affine

private lemma tangent_denominator_sq {x y : ℚ} (h : curve.toAffine.Equation x y) :
    (2 * y + 1) ^ 2 = 4 * x ^ 3 + 4 * x ^ 2 - 8 * x + 1 := by
  linear_combination 4 * ((equation_iff x y).mp h)

private lemma negY_formula (x y : ℚ) : curve.toAffine.negY x y = -y - 1 := by
  simp [negY, curve, model]

/-- The rational point group of 389.a1 has trivial 2-torsion. -/
theorem eq_zero_of_add_self_eq_zero {R : curve.toAffine.Point} (h : R + R = 0) :
    R = 0 := by
  cases R with
  | zero => rfl
  | some x y hxy =>
      by_cases hy : y = curve.toAffine.negY x y
      · have hden : 2 * y + 1 = 0 := by
          rw [negY_formula] at hy
          linarith
        exact (two_torsion_polynomial_ne_zero x (by
          simpa [hden] using (tangent_denominator_sq hxy.1).symm)).elim
      · rw [Point.add_self_of_Y_ne hy] at h
        exact (Point.some_ne_zero _ h).elim

private lemma halving_polynomial_eq_zero {x y t u : ℚ}
    {hxy : curve.toAffine.Nonsingular x y} {htu : curve.toAffine.Nonsingular t u}
    (h : Point.some _ _ hxy + Point.some _ _ hxy = Point.some _ _ htu)
    (hy : y ≠ curve.toAffine.negY x y) :
    x ^ 4 + 4 * x ^ 2 - 2 * x + 3 -
      t * (4 * x ^ 3 + 4 * x ^ 2 - 8 * x + 1) = 0 := by
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq] at h
  have hX := h.1
  rw [addX, slope_of_Y_ne rfl hy, negY_formula] at hX
  rw [show y - (-y - 1) = 2 * y + 1 by ring] at hX
  have hX' : ((3 * x ^ 2 + 2 * x - 2) / (2 * y + 1)) ^ 2 - 1 - x - x = t := by
    simpa [curve, model, sub_eq_add_neg] using hX
  have hden : 2 * y + 1 ≠ 0 := by
    intro he
    rw [negY_formula] at hy
    apply hy
    linarith
  have hsq : ((3 * x ^ 2 + 2 * x - 2) / (2 * y + 1)) ^ 2 = t + 1 + x + x := by
    linarith
  rw [div_pow] at hsq
  have hcross := (div_eq_iff (pow_ne_zero 2 hden)).mp hsq
  rw [tangent_denominator_sq hxy.1] at hcross
  linear_combination hcross

private lemma add_self_ne_of_x {t u : ℚ} (htu : curve.toAffine.Nonsingular t u)
    (ht : t = 0 ∨ t = -1 ∨ t = 1) (R : curve.toAffine.Point) :
    R + R ≠ Point.some _ _ htu := by
  intro h
  cases R with
  | zero =>
      exact Point.some_ne_zero htu (by simpa only [← Point.zero_def, zero_add] using h.symm)
  | some x y hxy =>
      by_cases hy : y = curve.toAffine.negY x y
      · rw [Point.add_self_of_Y_eq hy] at h
        exact Point.some_ne_zero htu h.symm
      · exact halving_polynomial_ne_zero x t ht (halving_polynomial_eq_zero h hy)

theorem add_self_ne_P (R : curve.toAffine.Point) : R + R ≠ P := by
  unfold P Point.mk
  exact add_self_ne_of_x _ (Or.inl rfl) R

theorem add_self_ne_Q (R : curve.toAffine.Point) : R + R ≠ Q := by
  unfold Q Point.mk
  exact add_self_ne_of_x _ (Or.inr (Or.inl rfl)) R

theorem add_self_ne_P_add_Q (R : curve.toAffine.Point) : R + R ≠ P + Q := by
  rw [P_add_Q]
  unfold S Point.mk
  exact add_self_ne_of_x _ (Or.inr (Or.inr rfl)) R

private lemma relation_even (m n : ℤ) (h : m • P + n • Q = 0) :
    m % 2 = 0 ∧ n % 2 = 0 := by
  let A := (m / 2) • P + (n / 2) • Q
  have hSplit : (2 : ℤ) • A + ((m % 2) • P + (n % 2) • Q) = 0 := by
    calc
      _ = (2 * (m / 2) + m % 2) • P + (2 * (n / 2) + n % 2) • Q := by
        dsimp only [A]
        simp only [add_zsmul, mul_zsmul, zsmul_add]
        abel
      _ = 0 := by
        rw [show 2 * (m / 2) + m % 2 = m by omega,
          show 2 * (n / 2) + n % 2 = n by omega]
        exact h
  have hDouble : (-A) + (-A) = (m % 2) • P + (n % 2) • Q := by
    simpa [two_zsmul] using (eq_neg_of_add_eq_zero_right hSplit).symm
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · exact ⟨hm, hn⟩
  · exact (add_self_ne_Q (-A) (by simpa [hm, hn] using hDouble)).elim
  · exact (add_self_ne_P (-A) (by simpa [hm, hn] using hDouble)).elim
  · exact (add_self_ne_P_add_Q (-A) (by simpa [hm, hn] using hDouble)).elim

private theorem relation_zero (m n : ℤ) (h : m • P + n • Q = 0) : m = 0 ∧ n = 0 := by
  by_cases hz : m = 0 ∧ n = 0
  · exact hz
  obtain ⟨hm, hn⟩ := relation_even m n h
  have hm' : 2 * (m / 2) = m := by omega
  have hn' : 2 * (n / 2) = n := by omega
  have hDouble : ((m / 2) • P + (n / 2) • Q) + ((m / 2) • P + (n / 2) • Q) = 0 := by
    rw [← two_zsmul, zsmul_add, ← mul_zsmul, ← mul_zsmul, hm', hn']
    exact h
  have hAbsM : 2 * (m / 2).natAbs = m.natAbs := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hm'
  have hAbsN : 2 * (n / 2).natAbs = n.natAbs := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hn'
  have hPos : 0 < m.natAbs + n.natAbs := by
    by_contra! hnonpos
    exact hz ⟨Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  obtain ⟨hM, hN⟩ := relation_zero (m / 2) (n / 2) (eq_zero_of_add_self_eq_zero hDouble)
  exact ⟨by omega, by omega⟩
termination_by m.natAbs + n.natAbs
decreasing_by omega

/-- The two specified rational points are linearly independent over the integers. -/
theorem independent_P_Q : LinearIndependent ℤ ![P, Q] :=
  LinearIndependent.pair_iff.mpr relation_zero

/-- The rational point group has rank at least two. -/
theorem two_le_rational_rank : 2 ≤ Module.rank ℤ curve.toAffine.Point :=
  Module.le_rank_iff.mpr ⟨![P, Q], independent_P_Q⟩

end BSD.RankTwo
