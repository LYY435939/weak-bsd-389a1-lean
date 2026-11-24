import BSD.CoefficientsFiber
import BSD.CoefficientsPrimary
import BSD.CoefficientsGeometry
import BSD.CoefficientsJacobi
import BSD.RationalPoints

/-! Frobenius traces of the Fermat cubic at every split prime. -/

namespace BSD.FermatCubic

/-- Over a field in which 2 is invertible the given short model and integral model have the
same affine coordinates after rescaling by the standard change of variables. -/
theorem short_card_eq_integral {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (model F).toAffine.Point = Nat.card (integralModel F).toAffine.Point := by
  have hEll : (integralModel F).IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    rw [integral_discriminant, show (19683 : F) = 3^9 by norm_num]
    exact neg_ne_zero.mpr (pow_ne_zero _ h3)
  have hsEll : (model F).IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    have heq : (model F).Δ = -(2:F)^12 * 3^9 := by
      simp [model, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [heq]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) (pow_ne_zero _ h3)
  have h4 : (4 : F) ≠ 0 := by simpa only [show (4:F) = 2^2 by norm_num] using pow_ne_zero 2 h2
  have h8 : (8 : F) ≠ 0 := by simpa only [show (8:F) = 2^3 by norm_num] using pow_ne_zero 3 h2
  let ec : F × F ≃ F × F :=
    { toFun := fun (x,y) => (4*x,8*y+4)
      invFun := fun (u,v) => (u/4,(v-4)/8)
      left_inv := by intro (x,y); apply Prod.ext <;> dsimp <;> field_simp; ring
      right_inv := by intro (u,v); apply Prod.ext <;> dsimp <;> field_simp; ring }
  have hs (x y : F) : (model F).toAffine.Equation x y ↔ y^2=x^3-432 := by
    simp [WeierstrassCurve.Affine.equation_iff, model, sub_eq_add_neg]
  have he (P : F × F) : (integralModel F).toAffine.Equation P.1 P.2 ↔
      (model F).toAffine.Equation (ec P).1 (ec P).2 := by
    rcases P with ⟨x,y⟩
    rw [integral_equation_iff, hs]
    change y^2+y=x^3-7 ↔ (8*y+4)^2=(4*x)^3-432
    constructor
    · intro h
      linear_combination 64*h
    · intro h
      have hh : (2:F)^6 * (y^2+y-(x^3-7))=0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ h2))
  exact Nat.card_congr (((integralModel F).toAffine.pointEquiv.trans
    ((ec.subtypeEquiv he).optionCongr.trans (model F).toAffine.pointEquiv.symm)).symm)

private lemma split_ne_two_three {p : ℕ} [hp : Fact p.Prime] (hs : p % 3 = 1) :
    (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 := by
  have hh := hp.out.two_le
  constructor
  · exact fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  · exact fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      ((ZMod.natCast_eq_zero_iff 3 p).mp h)

/-- For any cubic character of exact order three, the trace of the actual point count
of the short Weierstrass equation is minus the sum of the two cubic Jacobi sums. -/
theorem split_trace_eq_jacobiSum {p : ℕ} [Fact p.Prime] (hs : p % 3 = 1)
    (χ : MulChar (ZMod p) ℂ) (hχ : orderOf χ = 3) :
    (((p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point : ℤ) : ℂ) =
      -jacobiSum χ χ - jacobiSum χ⁻¹ χ⁻¹ := by
  have hc : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hn : χ ≠ 1 := by rintro rfl; simp at hχ
  obtain ⟨h2,h3⟩ := split_ne_two_three hs
  have hh := BSD.fermatAffine_card_eq_jacobiSum χ hn hc (card_cube_fiber_character hχ)
  have hr := card_cube_fiber_character hχ (1 : ZMod p)
  rw [map_one, map_one] at hr
  rw [ZMod.card p] at hh
  rw [short_card_eq_integral h2 h3, integral_card_eq_affine_add_cubeRoots h3,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  push_cast
  linear_combination -hh - hr

/-- The trace at a split prime is the trace of a primary Eisenstein integer of norm p.
No character, representation or precomputed curve coefficient is assumed. -/
theorem split_trace_primary_representation {p : ℕ} [Fact p.Prime] (hs : p % 3 = 1) :
    ∃ a b : ℤ, 3 ∣ a - 1 ∧ 3 ∣ b ∧ a^2-a*b+b^2 = p ∧
      (p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point = 2*a-b := by
  have hd : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  have hμ := Complex.isPrimitiveRoot_exp 3 (by decide)
  obtain ⟨χ,hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hd hμ
  have hn : χ ≠ 1 := by rintro rfl; simp at hχ
  have hc : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  obtain ⟨a,b,ha,hb,hj⟩ := BSD.exists_cubic_jacobiSum_primary_coordinates hμ hd χ hc
  obtain ⟨hnorm,htrace⟩ := BSD.cubic_jacobiSum_norm_trace hμ χ hn hc hj
  refine ⟨a,b,ha,hb,by simpa using hnorm,?_⟩
  exact_mod_cast (split_trace_eq_jacobiSum hs χ hχ).trans htrace

/-- Any primary representation of a split prime computes the same Frobenius trace. -/
theorem split_trace_of_primary {p : ℕ} [hp : Fact p.Prime] (hs : p % 3 = 1)
    {a b : ℤ} (hn : a^2-a*b+b^2 = p) (ha : 3 ∣ a-1) (hb : 3 ∣ b) :
    (p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point = 2*a-b := by
  obtain ⟨c,d,hc,hd,hn',ht⟩ := split_trace_primary_representation hs
  exact ht.trans (BSD.eisenstein_primary_trace_eq hp.out hn' hn hc hd ha hb)

/-- A trace can also be computed from the classical representation 4p = L² + 27M².
The congruence L ≡ 2 mod 3 fixes the sign in this convention. -/
theorem split_trace_of_four_prime {p : ℕ} [Fact p.Prime] (hs : p % 3 = 1)
    {L M : ℤ} (hn : 4 * (p : ℤ) = L^2 + 27*M^2) (hL : 3 ∣ L-2) :
    (p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point = L := by
  have hm : 2 ∣ L+3*M := by
    have h2 := congrArg (fun x : ℤ => (x : ZMod 2)) hn
    push_cast at h2
    have : (L : ZMod 2) + 3*(M : ZMod 2) = 0 := by
      generalize (L : ZMod 2) = l at *
      generalize (M : ZMod 2) = m at *
      rw [show (4 : ZMod 2) = 0 by decide, zero_mul] at h2
      fin_cases l <;> fin_cases m <;> revert h2 <;> decide
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (L+3*M) 2).mp (by push_cast; exact this)
  obtain ⟨a,ha⟩ := hm
  have hnorm : a^2-a*(3*M)+(3*M)^2=p := by
    apply mul_left_cancel₀ (show (4:ℤ) ≠ 0 by decide)
    linear_combination -hn + (L + 2*a-3*M)*(-ha)
  have hprim : 3 ∣ a-1 := by omega
  have ht := split_trace_of_primary hs hnorm hprim (dvd_mul_right 3 M)
  omega

end BSD.FermatCubic
