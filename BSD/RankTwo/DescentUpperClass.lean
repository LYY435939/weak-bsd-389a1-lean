import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

open Algebra Polynomial Module
open scoped NumberField

namespace BSD.RankTwo389
noncomputable section

/-- The monic cubic of twice the x-coordinate of a nonzero two-torsion point. -/
def descentPolynomial : ℚ[X] :=
  X ^ 3 + C 2 * X ^ 2 - C 8 * X + C 2

private def descentPolynomialZ : ℤ[X] :=
  X ^ 3 + C 2 * X ^ 2 - C 8 * X + C 2

private theorem descentPolynomialZ_natDegree : descentPolynomialZ.natDegree = 3 := by
  unfold descentPolynomialZ
  compute_degree!

private theorem descentPolynomialZ_monic : descentPolynomialZ.Monic := by
  rw [Monic, ← coeff_natDegree, descentPolynomialZ_natDegree]
  norm_num [descentPolynomialZ, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_C_mul, coeff_C]

private theorem descentPolynomialZ_map :
    descentPolynomialZ.map (algebraMap ℤ ℚ) = descentPolynomial := by
  simp only [descentPolynomialZ, descentPolynomial, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat, map_ofNat]

theorem descentPolynomial_monic : descentPolynomial.Monic := by
  rw [← descentPolynomialZ_map]
  exact descentPolynomialZ_monic.map _

theorem descentPolynomial_natDegree : descentPolynomial.natDegree = 3 := by
  rw [← descentPolynomialZ_map, descentPolynomialZ_monic.natDegree_map, descentPolynomialZ_natDegree]

private theorem descentPolynomialZ_eisenstein :
    descentPolynomialZ.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
  constructor
  · rw [descentPolynomialZ_monic.leadingCoeff, Ideal.mem_span_singleton]
    decide
  · intro n hn
    rw [descentPolynomialZ_natDegree] at hn
    interval_cases n <;>
      norm_num [descentPolynomialZ, Ideal.mem_span_singleton, coeff_add, coeff_sub, coeff_X_pow,
        coeff_C_mul, coeff_C]
    exact dvd_mul_of_dvd_left (by decide : (2 : ℤ) ∣ 8) _
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [descentPolynomialZ, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_C_mul, coeff_C]

theorem descentPolynomial_irreducible : Irreducible descentPolynomial := by
  rw [← descentPolynomialZ_map, ← descentPolynomialZ_monic.irreducible_iff_irreducible_map_fraction_map]
  exact descentPolynomialZ_eisenstein.irreducible
    ((Ideal.span_singleton_prime (by decide : (2 : ℤ) ≠ 0)).mpr (by decide))
    descentPolynomialZ_monic.isPrimitive (by simp [descentPolynomialZ_natDegree])

instance descentPolynomial_irreducible_fact : Fact (Irreducible descentPolynomial) :=
  ⟨descentPolynomial_irreducible⟩

/-- The cubic field of a nonzero two-torsion point. -/
abbrev DescentField := AdjoinRoot descentPolynomial

noncomputable instance : NumberField DescentField where
  to_charZero := Algebra.charZero_of_charZero ℚ DescentField
  to_finiteDimensional := (AdjoinRoot.powerBasis descentPolynomial_monic.ne_zero).finite

noncomputable def descentRoot : DescentField := AdjoinRoot.root descentPolynomial

noncomputable def descentPowerBasis : PowerBasis ℚ DescentField :=
  AdjoinRoot.powerBasis descentPolynomial_monic.ne_zero

@[simp] theorem descentPowerBasis_gen : descentPowerBasis.gen = descentRoot := rfl

@[simp] theorem descentPowerBasis_dim : descentPowerBasis.dim = 3 :=
  descentPolynomial_natDegree

theorem descentField_finrank : Module.finrank ℚ DescentField = 3 := by
  rw [descentPowerBasis.finrank, descentPowerBasis_dim]

theorem descentRoot_minpoly : minpoly ℚ descentRoot = descentPolynomial :=
  AdjoinRoot.minpoly_powerBasis_gen_of_monic descentPolynomial_monic

theorem descentRoot_relation :
    descentRoot ^ 3 + 2 * descentRoot ^ 2 - 8 * descentRoot + 2 = 0 := by
  have h := minpoly.aeval ℚ descentRoot
  rw [descentRoot_minpoly] at h
  simpa [descentPolynomial] using h

theorem descentRoot_isIntegral : IsIntegral ℤ descentRoot := by
  refine ⟨descentPolynomialZ, descentPolynomialZ_monic, ?_⟩
  simpa [descentPolynomialZ] using descentRoot_relation

noncomputable def descentRootIntegral : 𝓞 DescentField :=
  ⟨descentRoot, descentRoot_isIntegral⟩

@[simp] theorem algebraMap_descentRootIntegral :
    algebraMap (𝓞 DescentField) DescentField descentRootIntegral = descentRoot := rfl


private def descentBasis : Basis (Fin 3) ℚ DescentField :=
  descentPowerBasis.basis.reindex (finCongr descentPowerBasis_dim)

private theorem descentBasis_apply (i : Fin 3) :
    descentBasis i = descentRoot ^ (i : ℕ) := by
  simp [descentBasis]

open scoped Matrix

private def descentCompanion : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, -2; 1, 0, 8; 0, 1, -2]

set_option backward.isDefEq.respectTransparency false in
private theorem leftMulMatrix_descentRoot :
    Algebra.leftMulMatrix descentBasis descentRoot = descentCompanion := by
  have h₀ : descentRoot * descentBasis 0 = descentBasis 1 := by simp [descentBasis_apply]
  have h₁ : descentRoot * descentBasis 1 = descentBasis 2 := by simp [descentBasis_apply, pow_two]
  have h₂ : descentRoot * descentBasis 2 =
      (-2 : ℚ) • descentBasis 0 + (8 : ℚ) • descentBasis 1 + (-2 : ℚ) • descentBasis 2 := by
    simp [descentBasis_apply, Algebra.smul_def]
    linear_combination descentRoot_relation
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · change descentBasis.repr (descentRoot * descentBasis 0) i = descentCompanion i 0
    rw [h₀]
    fin_cases i <;> norm_num [descentCompanion, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Finsupp.single_apply, Fin.ext_iff]
  · change descentBasis.repr (descentRoot * descentBasis 1) i = descentCompanion i 1
    rw [h₁]
    fin_cases i <;> norm_num [descentCompanion, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Finsupp.single_apply, Fin.ext_iff]
  · change descentBasis.repr (descentRoot * descentBasis 2) i = descentCompanion i 2
    rw [h₂]
    fin_cases i <;> norm_num [descentCompanion, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Finsupp.single_apply, Fin.ext_iff]

theorem descentRoot_norm : Algebra.norm ℚ descentRoot = -2 := by
  rw [Algebra.norm_eq_matrix_det descentBasis, leftMulMatrix_descentRoot]
  norm_num [descentCompanion, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Fin.ext_iff]

theorem descentRoot_sub_one_norm : Algebra.norm ℚ (descentRoot - 1) = 3 := by
  rw [Algebra.norm_eq_matrix_det descentBasis, map_sub, map_one, leftMulMatrix_descentRoot]
  norm_num [descentCompanion, Matrix.det_fin_three, Matrix.one_apply, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

private theorem descentDerivativeEval :
    aeval descentRoot descentPolynomial.derivative =
      3 * descentRoot ^ 2 + 4 * descentRoot - 8 := by
  simp [descentPolynomial, derivative_mul, derivative_pow]
  ring

/-- Discriminant of the integral power basis. -/
theorem descentPowerBasis_discr : Algebra.discr ℚ descentPowerBasis.basis = 1556 := by
  rw [Algebra.discr_powerBasis_eq_norm, descentField_finrank, descentPowerBasis_gen,
    descentRoot_minpoly, descentDerivativeEval, Algebra.norm_eq_matrix_det descentBasis,
    map_sub, map_add, map_mul, map_mul, map_pow, leftMulMatrix_descentRoot]
  simp only [map_ofNat]
  norm_num [descentCompanion, Matrix.det_fin_three, Matrix.one_apply, Matrix.ofNat_apply, pow_two,
    Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

private theorem descentDiscriminant_le :
    |(NumberField.discr DescentField : ℝ)| ≤ 1556 := by
  classical
  let b := NumberField.integralBasis DescentField
  let b' := descentPowerBasis.basis.reindex (descentPowerBasis.basis.indexEquiv b)
  have hb' (i) : IsIntegral ℤ (b' i) := by
    dsimp [b']
    rw [Basis.reindex_apply, descentPowerBasis.basis_eq_pow, descentPowerBasis_gen]
    exact descentRoot_isIntegral.pow _
  have hEntry (i j) : IsIntegral ℤ (b.toMatrix b' i j) := by
    change IsIntegral ℤ (b.repr (b' j) i)
    let y : 𝓞 DescentField := ⟨b' j, hb' j⟩
    rw [show b' j = algebraMap (𝓞 DescentField) DescentField y from rfl]
    change IsIntegral ℤ ((NumberField.integralBasis DescentField).repr
      (algebraMap (𝓞 DescentField) DescentField y) i)
    rw [NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hEntry)
  have hmEq : (m : ℚ)^2 * (NumberField.discr DescentField : ℚ) = 1556 := by
    rw [show (m : ℚ) = _ from hm, NumberField.coe_discr, ← Algebra.discr_of_matrix_vecMul, Basis.toMatrix_map_vecMul]
    change Algebra.discr ℚ (descentPowerBasis.basis.reindex _) = _
    rw [Basis.coe_reindex, Algebra.discr_reindex, descentPowerBasis_discr]
  have hmR : (m : ℝ)^2 * (NumberField.discr DescentField : ℝ) = 1556 := by exact_mod_cast hmEq
  have hpos : 0 < (m : ℝ)^2 := by
    by_contra! hn
    have hz : (m : ℝ)^2 = 0 := le_antisymm hn (sq_nonneg _)
    norm_num [hz] at hmR
  have hm1 : 1 ≤ (m : ℝ)^2 := by
    have hmpos : 0 < m^2 := by exact_mod_cast hpos
    have : 1 ≤ m^2 := by omega
    exact_mod_cast this
  have hdNonneg : 0 ≤ (NumberField.discr DescentField : ℝ) := by
    exact nonneg_of_mul_nonneg_right (by rw [hmR]; norm_num) hpos
  rw [abs_of_nonneg hdNonneg]
  calc
    _ = 1 * (NumberField.discr DescentField : ℝ) := by rw [one_mul]
    _ ≤ (m : ℝ)^2 * (NumberField.discr DescentField : ℝ) :=
      mul_le_mul_of_nonneg_right hm1 hdNonneg
    _ = _ := hmR


private def realDescentPolynomial (x : ℝ) : ℝ := x^3 + 2*x^2 - 8*x + 2

private def embeddingAtRoot (x : ℝ) (hx : realDescentPolynomial x = 0) : DescentField →+* ℂ :=
  Complex.ofRealHom.comp (AdjoinRoot.lift (algebraMap ℚ ℝ) x (by
    simpa [descentPolynomial, realDescentPolynomial] using hx))

private theorem embeddingAtRoot_apply (x : ℝ) (hx : realDescentPolynomial x = 0) :
    embeddingAtRoot x hx descentRoot = (x : ℂ) := by
  simp [embeddingAtRoot, descentRoot, AdjoinRoot.lift_root]

private theorem embeddingAtRoot_isReal (x : ℝ) (hx : realDescentPolynomial x = 0) :
    NumberField.ComplexEmbedding.IsReal (embeddingAtRoot x hx) := by
  rw [NumberField.ComplexEmbedding.isReal_iff]
  apply RingHom.ext
  intro y
  simp [embeddingAtRoot]

private theorem descent_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces DescentField = 0 := by
  classical
  have hc : Continuous realDescentPolynomial := by unfold realDescentPolynomial; fun_prop
  obtain ⟨a, ha, har⟩ := intermediate_value_Ioo (a := (-5 : ℝ)) (b := -4)
      (by norm_num) hc.continuousOn
      (show 0 ∈ Set.Ioo (realDescentPolynomial (-5)) (realDescentPolynomial (-4)) by
        norm_num [realDescentPolynomial])
  obtain ⟨b, hb, hbr⟩ := intermediate_value_Ioo' (a := (0 : ℝ)) (b := 1)
      (by norm_num) hc.continuousOn
      (show 0 ∈ Set.Ioo (realDescentPolynomial 1) (realDescentPolynomial 0) by
        norm_num [realDescentPolynomial])
  obtain ⟨c, hc', hcr⟩ := intermediate_value_Ioo (a := (1 : ℝ)) (b := 2)
      (by norm_num) hc.continuousOn
      (show 0 ∈ Set.Ioo (realDescentPolynomial 1) (realDescentPolynomial 2) by
        norm_num [realDescentPolynomial])
  let S := {φ : DescentField →+* ℂ // NumberField.ComplexEmbedding.IsReal φ}
  let A : S := ⟨embeddingAtRoot a har, embeddingAtRoot_isReal a har⟩
  let B : S := ⟨embeddingAtRoot b hbr, embeddingAtRoot_isReal b hbr⟩
  let C' : S := ⟨embeddingAtRoot c hcr, embeddingAtRoot_isReal c hcr⟩
  have hab : A ≠ B := by
    intro h
    have hh := congrArg (fun φ : S ↦ (φ.val descentRoot).re) h
    have : a = b := by simpa [A, B, embeddingAtRoot_apply] using hh
    exact (show a < b from lt_trans ha.2 (by linarith [hb.1])).ne this
  have hac : A ≠ C' := by
    intro h
    have hh := congrArg (fun φ : S ↦ (φ.val descentRoot).re) h
    have : a = c := by simpa [A, C', embeddingAtRoot_apply] using hh
    exact (show a < c from lt_trans ha.2 (by linarith [hc'.1])).ne this
  have hbc : B ≠ C' := by
    intro h
    have hh := congrArg (fun φ : S ↦ (φ.val descentRoot).re) h
    have : b = c := by simpa [B, C', embeddingAtRoot_apply] using hh
    exact (lt_trans hb.2 hc'.1).ne this
  let f : Fin 3 → S := ![A, B, C']
  have hfin : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hcard := Fintype.card_le_of_injective f hfin
  rw [Fintype.card_fin, NumberField.InfinitePlace.card_real_embeddings] at hcard
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank DescentField
  rw [descentField_finrank] at h
  omega

open scoped Real

private theorem descentMinkowskiFloor_le_eight :
    ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces DescentField *
      (Nat.factorial (Module.finrank ℚ DescentField) / (Module.finrank ℚ DescentField) ^
        (Module.finrank ℚ DescentField) * √|(NumberField.discr DescentField : ℝ)|)⌋₊ ≤ 8 := by
  simp only [descent_nrComplexPlaces, pow_zero, one_mul, descentField_finrank]
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt (by positivity)).mpr
  have hsqrt : √|(NumberField.discr DescentField : ℝ)| ≤ 40 := by
    calc
      _ ≤ Real.sqrt 1600 := Real.sqrt_le_sqrt (descentDiscriminant_le.trans (by norm_num))
      _ = 40 := by norm_num
  norm_num at *
  linarith


open Ideal

local notation "O" => 𝓞 DescentField

theorem descentRootIntegral_relation :
    descentRootIntegral ^ 3 + 2 * descentRootIntegral ^ 2 - 8 * descentRootIntegral + 2 = 0 := by
  apply (IsFractionRing.injective O DescentField)
  simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero,
    algebraMap_descentRootIntegral] using descentRoot_relation

theorem descentRootIntegral_ideal_norm : absNorm (Ideal.span ({descentRootIntegral} : Set O)) = 2 := by
  rw [absNorm_span_singleton]
  have hn := Algebra.coe_norm_int descentRootIntegral
  change (Algebra.norm ℤ descentRootIntegral : ℚ) = Algebra.norm ℚ descentRoot at hn
  rw [descentRoot_norm] at hn
  have : Algebra.norm ℤ descentRootIntegral = -2 := by exact_mod_cast hn
  simp [this]

theorem descentRootIntegral_sub_one_ideal_norm :
    absNorm (Ideal.span ({descentRootIntegral - 1} : Set O)) = 3 := by
  rw [absNorm_span_singleton]
  have hn := Algebra.coe_norm_int (descentRootIntegral - 1)
  change (Algebra.norm ℤ (descentRootIntegral - 1) : ℚ) =
    Algebra.norm ℚ ((algebraMap O DescentField) (descentRootIntegral - 1)) at hn
  rw [map_sub (algebraMap O DescentField), map_one, algebraMap_descentRootIntegral,
    descentRoot_sub_one_norm] at hn
  have : Algebra.norm ℤ (descentRootIntegral - 1) = 3 := by exact_mod_cast hn
  simp [this]

private theorem span_eq_prime_of_mem_of_norm_prime {P : Ideal O} (hP : P.IsPrime)
    {x : O} (hx : x ∈ P) (hn : (absNorm (Ideal.span ({x} : Set O))).Prime) :
    Ideal.span {x} = P := by
  have hJ : (Ideal.span ({x} : Set O)).IsPrime :=
    isPrime_of_irreducible_absNorm ((Nat.irreducible_iff_nat_prime _).mpr hn)
  have hJ₀ : (Ideal.span ({x} : Set O)) ≠ ⊥ := by
    intro h
    rw [h, absNorm_bot] at hn
    exact Nat.not_prime_zero hn
  exact (hJ.isMaximal hJ₀).eq_of_le hP.ne_top ((span_singleton_le_iff_mem _).mpr hx)

/-- Every prime ideal over two is generated by the integral two-torsion coordinate. -/
theorem descent_prime_above_two {P : Ideal O}
    (hP : P ∈ primesOver (Ideal.span ({2} : Set ℤ)) O) :
    Ideal.span ({descentRootIntegral} : Set O) = P := by
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span ({2} : Set ℤ)) := hP.2
  let q := Ideal.Quotient.mk P
  have h2 : (2 : O) ∈ P := by
    simpa using (P.mem_of_liesOver (Ideal.span ({2} : Set ℤ)) 2).mp (subset_span (by simp))
  have hz2 : (2 : O ⧸ P) = 0 := by
    rw [← map_ofNat q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  have h8 : (8 : O ⧸ P) = 0 := by
    rw [show (8 : O ⧸ P) = 2 * 4 by norm_num, hz2, zero_mul]
  have hcube : (q descentRootIntegral)^3 = 0 := by
    simpa only [map_add, map_sub, map_pow, map_mul, map_ofNat, map_zero, hz2, h8, zero_mul,
      sub_zero, add_zero] using congrArg q descentRootIntegral_relation
  have hroot : q descentRootIntegral = 0 := eq_zero_of_pow_eq_zero hcube
  apply span_eq_prime_of_mem_of_norm_prime hP.1 (Ideal.Quotient.eq_zero_iff_mem.mp hroot)
  rw [descentRootIntegral_ideal_norm]
  decide

private theorem residue_root_eq_one_at_three :
    ∀ x : ZMod 3, x^3 + 2*x^2 - 8*x + 2 = 0 → x = 1 := by decide

private theorem no_residue_root_at_five :
    ∀ x : ZMod 5, x^3 + 2*x^2 - 8*x + 2 ≠ 0 := by decide

private theorem no_residue_root_at_seven :
    ∀ x : ZMod 7, x^3 + 2*x^2 - 8*x + 2 ≠ 0 := by decide

private theorem small_prime_cases {p : ℕ} (hp3 : 3 ≤ p) (hp8 : p ≤ 8) (hp : p.Prime) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases p <;> norm_num at hp <;> norm_num

private theorem principal_prime_of_small_norm
    (p : ℕ) (hp8 : p ≤ 8) (hp : p.Prime) (P : Ideal O)
    (hP : P ∈ primesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) O)
    (hn : p ^ P.inertiaDeg ℤ ≤ 8) : Submodule.IsPrincipal P := by
  classical
  by_cases hp2 : p = 2
  · subst p
    rw [← descent_prime_above_two hP]
    exact ⟨⟨descentRootIntegral, rfl⟩⟩
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hP.2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hdeg : P.inertiaDeg ℤ = 1 := by
    have hpos := P.inertiaDeg_pos ℤ
    by_contra h
    have hpow : 3^2 ≤ p ^ P.inertiaDeg ℤ :=
      (Nat.pow_le_pow_left hp3 2).trans (Nat.pow_le_pow_right hp.pos (by omega))
    omega
  have hNorm : absNorm P = p := by rw [← Ideal.pow_inertiaDeg p P, hdeg, pow_one]
  let : Finite (O ⧸ P) := (Ideal.absNorm_ne_zero_iff P).mp (hNorm.trans_ne hp.ne_zero)
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hc : Fintype.card (O ⧸ P) = p := by
    rwa [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  let e := ZMod.ringEquivOfPrime (O ⧸ P) hp hc
  let q : O →+* ZMod p := e.symm.toRingHom.comp (Ideal.Quotient.mk P)
  have hroot : (q descentRootIntegral)^3 + 2*(q descentRootIntegral)^2 -
      8*(q descentRootIntegral) + 2 = 0 := by
    simpa only [map_add, map_sub, map_pow, map_mul, map_ofNat, map_zero]
      using congrArg q descentRootIntegral_relation
  rcases small_prime_cases hp3 hp8 hp with rfl | rfl | rfl
  · have hq1 := residue_root_eq_one_at_three _ hroot
    have hq0 : q (descentRootIntegral - 1) = 0 := by simp [hq1]
    have hmem : descentRootIntegral - 1 ∈ P := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply e.symm.injective
      rw [map_zero]
      exact hq0
    have heq := span_eq_prime_of_mem_of_norm_prime hP.1 hmem
      (by rw [descentRootIntegral_sub_one_ideal_norm]; decide)
    rw [← heq]
    exact ⟨⟨descentRootIntegral - 1, rfl⟩⟩
  · exact (no_residue_root_at_five _ hroot).elim
  · exact (no_residue_root_at_seven _ hroot).elim

/-- The ring of integers of the cubic descent field of 389.a1 is a PID. -/
theorem descentRingOfIntegers_isPrincipal : IsPrincipalIdealRing O := by
  classical
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hpprime P hP hnorm
  exact principal_prime_of_small_norm p ((Finset.mem_Icc.mp hp).2.trans descentMinkowskiFloor_le_eight)
    hpprime P hP (hnorm.trans descentMinkowskiFloor_le_eight)

/-- The cubic descent field of 389.a1 has class number one. -/
theorem descentField_classNumber : NumberField.classNumber DescentField = 1 :=
  NumberField.classNumber_eq_one_iff.mpr descentRingOfIntegers_isPrincipal

end

end BSD.RankTwo389
