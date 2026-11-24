import BSD.RankTwo.PeriodBridge
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic

/-! # The prime-level trace and the bad Hecke operator in weight two -/

noncomputable section

namespace BSD.RankTwo

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise

private abbrev HeckeTraceQuot (p : ℕ) :=
  𝒮ℒ ⧸ ((Gamma0 p : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)

private def traceClass (p : ℕ) (A : SL(2, ℤ)) : HeckeTraceQuot p :=
  QuotientGroup.mk ((mapGL ℝ).rangeRestrict A)

private lemma traceClass_eq_iff (p : ℕ) (A B : SL(2, ℤ)) :
    traceClass p A = traceClass p B ↔ (((A⁻¹ * B) 1 0 : ℤ) : ZMod p) = 0 := by
  rw [traceClass, traceClass, QuotientGroup.eq]
  change (mapGL ℝ A)⁻¹ * mapGL ℝ B ∈ (Gamma0 p).map (mapGL ℝ) ↔ _
  rw [← map_inv, ← map_mul]
  constructor
  · rintro ⟨g, hg, h⟩
    exact mapGL_injective h ▸ hg
  · intro h
    exact ⟨_, h, rfl⟩

private def traceRep {p : ℕ} [NeZero p] (a : Option (ZMod p)) : SL(2, ℤ) :=
  match a with
  | none => 1
  | some i => ⟨!![-(i.val : ℤ), -1; 1, 0], by simp [det_fin_two_of]⟩

private lemma traceRep_relation {p : ℕ} [NeZero p] (a : ZMod p) (B : SL(2, ℤ)) :
    traceClass p (traceRep (some a)) = traceClass p B ↔
      -(B 0 0 : ZMod p) - a * (B 1 0 : ZMod p) = 0 := by
  rw [traceClass_eq_iff]
  change ((((((traceRep (some a))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B.val) 1 0 : ℤ) : ZMod p) = 0 ↔ _
  rw [(Matrix.two_mul_expl _ _).2.2.1, SL2_inv_expl]
  simp [traceRep, sub_eq_add_neg]

private def traceEquiv (p : ℕ) [Fact p.Prime] : Option (ZMod p) ≃ HeckeTraceQuot p :=
  Equiv.ofBijective (fun a => traceClass p (traceRep a)) (by
    constructor
    · intro a b h
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          rw [traceClass_eq_iff] at h
          change (((((1 : SL(2, ℤ))⁻¹ * traceRep (some b)) 1 0 : ℤ) : ZMod p)) = 0 at h
          rw [inv_one, one_mul] at h
          simp [traceRep] at h
      | some a =>
        rw [traceRep_relation] at h
        cases b with
        | none => simp [traceRep] at h
        | some b =>
          congr 1
          simpa [traceRep, sub_eq_zero, eq_comm] using h
    · intro q
      induction q using Quotient.inductionOn with
      | h g =>
        obtain ⟨B, hB⟩ := g.property
        have hBg : ((mapGL ℝ).rangeRestrict B) = g := Subtype.ext hB
        rw [← hBg]
        by_cases hc : (B 1 0 : ZMod p) = 0
        · refine ⟨none, ?_⟩
          change traceClass p (traceRep none) = traceClass p B
          rw [traceClass_eq_iff]
          simpa [traceRep] using hc
        · refine ⟨some (-(B 0 0 : ZMod p) / B 1 0), ?_⟩
          change traceClass p (traceRep (some _)) = traceClass p B
          rw [traceRep_relation]
          field_simp
          ring)

private theorem weightTwo_trace_zero (p : ℕ) [Fact p.Prime]
    (f : CuspForm (Gamma0 p) 2) :
    (CuspForm.trace 𝒮ℒ f : ℍ → ℂ) = 0 := by
  have hz : (CuspForm.trace 𝒮ℒ f : ModularForm 𝒮ℒ 2) = 0 :=
    (rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero) _
  exact congrArg (fun g : ModularForm 𝒮ℒ 2 => (g : ℍ → ℂ)) hz

/-- The sum of the identity term and the prime translates in the weight-two trace vanishes. -/
private theorem primeLevel_trace_sum_zero (p : ℕ) [Fact p.Prime] (f : CuspForm (Gamma0 p) 2) :
    (f : ℍ → ℂ) + ∑ a : ZMod p, (f : ℍ → ℂ) ∣[(2 : ℤ)] (mapGL ℝ (traceRep (some a)))⁻¹ = 0 := by
  classical
  let := Fintype.ofFinite (HeckeTraceQuot p)
  have h := weightTwo_trace_zero p f
  change ∑ q : HeckeTraceQuot p, SlashInvariantForm.quotientFunc f q = 0 at h
  rw [← Equiv.sum_comp (traceEquiv p)] at h
  simpa [Fintype.sum_option, traceEquiv, traceClass, traceRep, ModularForm.SL_slash] using h


private def heckeMatrix {p : ℕ} [Fact p.Prime] (a : ZMod p) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, (a.val : ℝ); 0, (p : ℝ)]
    (by simpa [det_fin_two_of] using (Fact.out : Nat.Prime p).ne_zero)

/-- The bad Hecke operator, with the determinant factor in the weight-two slash action. -/
def badHecke (p : ℕ) [Fact p.Prime] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ a : ZMod p, f ∣[(2 : ℤ)] heckeMatrix a

private lemma level_pos (p : ℕ) [Fact p.Prime] : (0 : ℝ) < p :=
  Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos

/-- The prime-level weight-two operator is the average of its translates. -/
theorem badHecke_apply (p : ℕ) [Fact p.Prime] (f : ℍ → ℂ) (τ : ℍ) :
    badHecke p f τ =
      (∑ a : ZMod p, f (ofComplex (((τ : ℂ) + (a.val : ℂ)) / (p : ℂ)))) / (p : ℂ) := by
  classical
  have hp := level_pos p
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  rw [badHecke, Finset.sum_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hval : (heckeMatrix a).val = !![1, (a.val : ℝ); 0, (p : ℝ)] := rfl
  have hdet : (heckeMatrix a).det.val = (p : ℝ) := by
    rw [GeneralLinearGroup.val_det_apply, hval, det_fin_two_of]
    ring
  have hpos : 0 < (heckeMatrix a).det.val := by simpa only [hdet] using hp
  have hnum : UpperHalfPlane.num (heckeMatrix a) τ = (τ : ℂ) + (a.val : ℂ) := by
    change (1 : ℂ) * (τ : ℂ) + ((a.val : ℝ) : ℂ) = _
    rw [one_mul, Complex.ofReal_natCast]
  have hden : UpperHalfPlane.denom (heckeMatrix a) τ = (p : ℂ) := by
    change (0 : ℂ) * (τ : ℂ) + ((p : ℝ) : ℂ) = _
    simp
  have hact : (heckeMatrix a • τ : ℍ) =
      ofComplex (((τ : ℂ) + (a.val : ℂ)) / (p : ℂ)) := by
    rw [← hnum, ← hden, ← coe_smul_of_det_pos hpos τ]
    exact (ofComplex_apply _).symm
  rw [ModularForm.slash_apply, hact, hdet, hden]
  norm_num [UpperHalfPlane.σ, hdet, hp, abs_of_pos hp]
  field_simp

private lemma sl_entry (A : SL(2, ℤ)) (i j : Fin 2) : (mapGL ℝ A).val i j = (A i j : ℝ) := rfl

private lemma fricke_mul_rep {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    weightTwoFricke p (level_pos p) * (mapGL ℝ (traceRep (some a)))⁻¹ = heckeMatrix a := by
  rw [← map_inv]
  have hcast : ((mapGL ℝ ((traceRep (some a))⁻¹) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (((traceRep (some a))⁻¹ : SL(2, ℤ)).val.map (Int.castRingHom ℝ)) := rfl
  apply Units.ext
  change _ * _ = !![1, (a.val : ℝ); 0, (p : ℝ)]
  rw [weightTwoFricke_val, hcast, SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceRep, Matrix.map, Matrix.mul_apply, Fin.sum_univ_two]

private lemma fricke_conjugate {p : ℕ} [Fact p.Prime] {A : SL(2, ℤ)} (hA : A ∈ Gamma0 p) :
    let W := weightTwoFricke p (level_pos p)
    ∃ B ∈ Gamma0 p, W * mapGL ℝ A = mapGL ℝ B * W ∧ mapGL ℝ A * W = W * mapGL ℝ B := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hA)
  let B : SL(2, ℤ) := ⟨!![A 1 1, -c; -(p : ℤ) * A 0 1, A 0 0], by
    have h := A.property
    rw [det_fin_two] at h
    rw [det_fin_two_of]
    rw [hc] at h
    linear_combination h⟩
  have hAcast : ((mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      A.val.map (Int.castRingHom ℝ) := rfl
  have hBcast : ((mapGL ℝ B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      B.val.map (Int.castRingHom ℝ) := rfl
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    change ((-(p : ℤ) * A 0 1 : ℤ) : ZMod p) = 0
    simp
  all_goals
    apply Units.ext
    change (_ : Matrix (Fin 2) (Fin 2) ℝ) * _ = _ * _
    rw [weightTwoFricke_val, hAcast, hBcast]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, hc] <;> ring

private lemma fricke_normalizes (p : ℕ) [Fact p.Prime] :
    weightTwoFricke p (level_pos p) ∈ (Subgroup.normalizer (Gamma0 p : Subgroup (GL (Fin 2) ℝ))) := by
  let W := weightTwoFricke p (level_pos p)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hAB, _⟩ := fricke_conjugate hA
    exact ⟨B, hB, by rw [hAB, mul_inv_cancel_right]⟩
  · rintro ⟨A, hA, hAeq⟩
    obtain ⟨B, hB, _, hAB⟩ := fricke_conjugate hA
    refine ⟨B, hB, ?_⟩
    apply mul_left_cancel (a := W)
    rw [← hAB, hAeq, inv_mul_cancel_right]

/-- Fricke translates preserve the level of a prime-level cusp form. -/
theorem exists_fricke_cuspForm (p : ℕ) [Fact p.Prime] (f : CuspForm (Gamma0 p) 2) :
    ∃ g : CuspForm (Gamma0 p) 2,
      (g : ℍ → ℂ) = (f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke p (level_pos p) := by
  let W := weightTwoFricke p (level_pos p)
  have hnorm : W ∈ Subgroup.normalizer (↑(Gamma0 p : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) :=
    fricke_normalizes p
  have hh : W⁻¹ ∈ Subgroup.normalizer (↑(Gamma0 p : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) :=
    (Subgroup.normalizer (↑(Gamma0 p : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))).inv_mem hnorm
  have h := Subgroup.conjAct_pointwise_smul_eq_self (H := (Gamma0 p : Subgroup (GL (Fin 2) ℝ))) hh
  let g := CuspForm.translate f W
  change ConjAct.toConjAct W⁻¹ • (Gamma0 p : Subgroup (GL (Fin 2) ℝ)) = _ at h
  exact ⟨CuspForm.mcast rfl g h.symm, rfl⟩

/-- At prime level the weight-two operator at the level prime equals minus the Fricke involution. -/
theorem badHecke_eq_neg_fricke (p : ℕ) [Fact p.Prime] (f : CuspForm (Gamma0 p) 2) :
    badHecke p f = -((f : ℍ → ℂ) ∣[(2 : ℤ)] weightTwoFricke p (level_pos p)) := by
  obtain ⟨g, hg⟩ := exists_fricke_cuspForm p f
  have h := primeLevel_trace_sum_zero p g
  rw [hg] at h
  simp only [← SlashAction.slash_mul, fricke_mul_rep] at h
  change _ + badHecke p f = 0 at h
  exact eq_neg_of_add_eq_zero_right h

end BSD.RankTwo
