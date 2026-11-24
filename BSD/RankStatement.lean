import BSD.DescentRank
import BSD.Order
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction

/-! # The rational rank part of BSD

The two predicates below use the continuation and rank conditions of
`FormalConjectures.Wikipedia.HasseWeil` and `FormalConjectures.Millennium.BSD`
at revision 2207c54d0dbe960de591d280f997b195bf3f6e28.
-/

namespace BSD

/-- The continuation must agree with this curve's own Dirichlet series. -/
def Continues (E : WeierstrassCurve ℚ) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The order of vanishing formulation for an individual curve. -/
def RankPart (E : WeierstrassCurve ℚ) : Prop :=
  ∃ L : ℂ → ℂ, Continues E L ∧ meromorphicOrderAt L 1 = Module.finrank ℤ E.toAffine.Point

/-- The general rational rank conjecture. -/
def RankConjecture : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → RankPart E

/-- Combine independently certified arithmetic rank and central derivatives. -/
theorem rankPart_of_derivatives {E : WeierstrassCurve ℚ} {L : ℂ → ℂ} {r : ℕ}
    (hcont : Continues E L) (han : AnalyticAt ℂ L 1)
    (hr : Module.finrank ℤ E.toAffine.Point = r)
    (hlow : ∀ k < r, iteratedDeriv k L 1 = 0) (hlead : iteratedDeriv r L 1 ≠ 0) :
    RankPart E := by
  exact ⟨L, hcont, hr ▸ (meromorphicOrderAt_eq_nat_iff_iteratedDeriv han).2 ⟨hlow, hlead⟩⟩

/-- An all-ranks criterion. A finite descent target bounds the rank from above
and independent rational points bound it from below. The two analytic inputs
give the first nonzero derivative of the same curve's continued L-series. -/
theorem rankPart_of_descent_and_derivatives {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [Module.Finite ℤ E.toAffine.Point] {S : Type*} [Finite S] {n r t : ℕ}
    (hn : 1 < n) (e : (E.toAffine.Point ⧸ (nsmulAddMonoidHom n).range) ↪ S)
    (ht : t ≤ Nat.card (nsmulAddMonoidHom (α := E.toAffine.Point) n).ker)
    (hS : Nat.card S < n ^ (r + 1) * t)
    (P : Fin r → E.toAffine.Point) (hP : LinearIndependent ℤ P)
    {L : ℂ → ℂ} (hcont : Continues E L) (han : AnalyticAt ℂ L 1)
    (hlow : ∀ k < r, iteratedDeriv k L 1 = 0) (hlead : iteratedDeriv r L 1 ≠ 0) :
    RankPart E :=
  rankPart_of_derivatives hcont han (finrank_eq_of_descent hn e ht hS P hP) hlow hlead

/-- Once the rank-zero and rank-one implications are supplied for this
continuation, a curve of algebraic rank two has analytic order two exactly
when its second derivative is nonzero. -/
theorem order_two_iff_second_derivative {E : WeierstrassCurve ℚ} {L : ℂ → ℂ}
    (han : AnalyticAt ℂ L 1) (hr : Module.finrank ℤ E.toAffine.Point = 2)
    (hLow : ∀ r : ℕ, r ≤ 1 → meromorphicOrderAt L 1 = (r : WithTop ℤ) →
      Module.finrank ℤ E.toAffine.Point = r) :
    meromorphicOrderAt L 1 = 2 ↔ iteratedDeriv 2 L 1 ≠ 0 := by
  have hc (r : ℕ) (h : r ≤ 1) : meromorphicOrderAt L 1 ≠ (r : WithTop ℤ) := by
    intro he
    have := hLow r h he
    omega
  have h₀ : iteratedDeriv 0 L 1 = 0 := by
    by_contra hn
    exact hc 0 (by decide) ((meromorphicOrderAt_eq_nat_iff_iteratedDeriv han).2 ⟨by omega, hn⟩)
  have h₁ : iteratedDeriv 1 L 1 = 0 := by
    by_contra hn
    refine hc 1 (by decide) ((meromorphicOrderAt_eq_nat_iff_iteratedDeriv han).2 ⟨?_, hn⟩)
    intro i hi
    rwa [show i = 0 by omega]
  change meromorphicOrderAt L 1 = ((2 : ℕ) : WithTop ℤ) ↔ _
  rw [meromorphicOrderAt_eq_nat_iff_iteratedDeriv han]
  refine ⟨And.right, fun h₂ ↦ ⟨?_, h₂⟩⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> assumption

end BSD
