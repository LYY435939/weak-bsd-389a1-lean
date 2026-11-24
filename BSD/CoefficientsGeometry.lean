import BSD.SmallPrimes

/-! Two affine charts for the Fermat cubic over fields of characteristic different from three. -/

namespace BSD.FermatCubic

private abbrev Wsol (F : Type*) [Field F] :=
  {P : F × F // P.2 ^ 2 + P.2 = P.1 ^ 3 - 7}

private lemma sum_ne_zero {F : Type*} [Field F] {a b : F} (h : a ^ 3 + b ^ 3 = 1) :
    a + b ≠ 0 := by
  intro hz
  have hb : b = -a := by linear_combination hz
  apply (zero_ne_one : (0 : F) ≠ 1)
  rw [hb] at h
  linear_combination h

/-- The part of the integral Weierstrass model with nonzero x is the entire affine Fermat chart. -/
private def fermatOpenEquiv {F : Type*} [Field F] (h3 : (3 : F) ≠ 0) :
    {P : Wsol F // P.val.1 ≠ 0} ≃ {P : F × F // P.1 ^ 3 + P.2 ^ 3 = 1} where
  toFun := fun ⟨⟨(x,y),h⟩,hx⟩ =>
    ⟨((y+5)/(3*x), (4-y)/(3*x)), by
      change ((y+5)/(3*x))^3 + ((4-y)/(3*x))^3 = 1
      change y^2+y = x^3-7 at h
      change x ≠ 0 at hx
      field_simp [h3,hx]
      linear_combination 27*h⟩
  invFun := fun ⟨(a,b),h⟩ =>
    ⟨⟨(3/(a+b), 9*a/(a+b)-5), by
      change (9*a/(a+b)-5)^2+(9*a/(a+b)-5) = (3/(a+b))^3-7
      change a^3+b^3=1 at h
      field_simp [sum_ne_zero h]
      linear_combination 27*h⟩, div_ne_zero h3 (sum_ne_zero h)⟩
  left_inv := by
    rintro ⟨⟨⟨x,y⟩,h⟩,hx⟩
    apply Subtype.ext
    apply Subtype.ext
    change (3 / ((y+5)/(3*x)+(4-y)/(3*x)),
      9*((y+5)/(3*x))/((y+5)/(3*x)+(4-y)/(3*x))-5) = (x,y)
    change x ≠ 0 at hx
    have hsum : (y+5)/(3*x)+(4-y)/(3*x) = 3/x := by
      field_simp [hx,h3]
      ring
    rw [hsum]
    apply Prod.ext <;> dsimp <;> field_simp [h3,hx]
    ring
  right_inv := by
    rintro ⟨⟨a,b⟩,h⟩
    apply Subtype.ext
    change (((9*a/(a+b)-5)+5)/(3*(3/(a+b))), (4-(9*a/(a+b)-5))/(3*(3/(a+b)))) = (a,b)
    change a^3+b^3=1 at h
    have hab := sum_ne_zero h
    apply Prod.ext <;> dsimp <;> field_simp [h3,hab] <;> ring

private abbrev Root (F : Type*) [Field F] := {r : F // r ^ 3 = 1}

private def unitRoot (F : Type*) [Field F] : Root F := ⟨1, by simp⟩

/-- The remaining affine points at x = 0 correspond to the two nontrivial cube roots of unity,
when they exist. The root 1 labels the point at infinity. -/
private def fermatBoundaryEquiv {F : Type*} [Field F] (h3 : (3 : F) ≠ 0) :
    {P : Wsol F // P.val.1 = 0} ≃ {r : Root F // r ≠ unitRoot F} where
  toFun := fun ⟨⟨(x,y),h⟩,hx⟩ => by
    change x = 0 at hx
    change y^2+y = x^3-7 at h
    subst x
    have hquad : ((y-1)/3)^2 + (y-1)/3 + 1 = 0 := by
      field_simp [h3]
      linear_combination h
    refine ⟨⟨(y-1)/3, ?_⟩, ?_⟩
    · linear_combination ((y-1)/3 - 1)*hquad
    · intro he
      have he' : (y-1)/3 = 1 := congrArg Subtype.val he
      rw [he'] at hquad
      exact h3 (by linear_combination hquad)
  invFun := fun ⟨⟨r,h⟩,hne⟩ => by
    have hr : r ≠ 1 := fun he => hne (Subtype.ext he)
    have hquad := (mul_eq_zero.mp (show (r-1)*(r^2+r+1)=0 by linear_combination h)).resolve_left
      (sub_ne_zero.mpr hr)
    refine ⟨⟨(0,3*r+1),?_⟩,rfl⟩
    change (3*r+1)^2+(3*r+1) = 0^3-7
    linear_combination 9*hquad
  left_inv := by
    rintro ⟨⟨⟨x,y⟩,h⟩,hx⟩
    change x = 0 at hx
    subst x
    apply Subtype.ext
    apply Subtype.ext
    change (0,3*((y-1)/3)+1)=(0,y)
    congr 1
    field_simp [h3]
    ring
  right_inv := by
    rintro ⟨⟨r,h⟩,hne⟩
    apply Subtype.ext
    apply Subtype.ext
    change (3*r+1-1)/3=r
    field_simp [h3]
    ring

/-- Point-count identity valid in every finite field whose characteristic differs from three. -/
theorem integral_card_eq_affine_add_cubeRoots {F : Type*} [Field F] [Finite F]
    (h3 : (3 : F) ≠ 0) :
    Nat.card (integralModel F).toAffine.Point =
      Nat.card {P : F × F // P.1 ^ 3 + P.2 ^ 3 = 1} + Nat.card {r : F // r ^ 3 = 1} := by
  classical
  have hEll : (integralModel F).IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    rw [integral_discriminant, show (19683 : F) = 3^9 by norm_num]
    exact neg_ne_zero.mpr (pow_ne_zero _ h3)
  let eEq : {P : F × F // (integralModel F).toAffine.Equation P.1 P.2} ≃ Wsol F :=
    Equiv.subtypeEquivRight fun _ => integral_equation_iff _ _
  have hW := Nat.card_congr ((integralModel F).toAffine.pointEquiv.trans eEq.optionCongr)
  change Nat.card (integralModel F).toAffine.Point = Nat.card (Option (Wsol F)) at hW
  have hParts := (Nat.card_congr (Equiv.sumCompl (fun P : Wsol F => P.val.1 = 0))).symm
  rw [Nat.card_sum, Nat.card_congr (fermatBoundaryEquiv h3), Nat.card_congr (fermatOpenEquiv h3)]
    at hParts
  have hRoot := Nat.card_congr (Equiv.subtypeNeSumPUnit (unitRoot F) :
    {r : Root F // r ≠ unitRoot F} ⊕ PUnit.{1} ≃ Root F)
  simp only [Nat.card_sum, Nat.card_unique] at hRoot
  rw [hW, Finite.card_option, hParts]
  change _ = _ + Nat.card (Root F)
  omega

end BSD.FermatCubic
