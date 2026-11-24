import BSD.RankTwo.FareyHecke
import BSD.RankTwo.FrickeSymbols
import BSD.RankTwo.PeriodFaithfulFrickePath
import BSD.RankTwo.PeriodFaithfulHecke

/-! Evaluation of a unimodular Fricke path edge by the geometric Manin symbol. -/

namespace BSD.RankTwo.PeriodFaithfulFrickeColumns

open BSD.RankTwo.ModularSymbols
open BSD.RankTwo.ModularSymbols.Farey
open scoped MatrixGroups

local instance : Fact (Nat.Prime 389) := ⟨by norm_num⟩

/-- An oriented edge with determinant `±1` is evaluated by its Manin label. -/
theorem pair_step_evaluation {K : Type*}
    (P : OnePoint ℚ → OnePoint ℚ → K) (hinv : Gamma0Invariant P)
    (a b : Column)
    (hd : b.1 * a.2 - a.1 * b.2 = 1 ∨ b.1 * a.2 - a.1 * b.2 = -1) :
    manin P (project b.2 ((b.1 * a.2 - a.1 * b.2) * a.2)) =
      P (cusp a) (cusp b) := by
  let d : ℤ := b.1 * a.2 - a.1 * b.2
  let m : CuspMatrix := ⟨b, (d * a.1, d * a.2)⟩
  have hd' : d = 1 ∨ d = -1 := hd
  have hd2 : d * d = 1 := by
    rcases hd' with h | h <;> rw [h] <;> norm_num
  have hm : m.det = 1 := by
    change b.1 * (d * a.2) - (d * a.1) * b.2 = 1
    calc
      _ = d * (b.1 * a.2 - a.1 * b.2) := by ring
      _ = d * d := rfl
      _ = 1 := hd2
  have hc : cusp m.right = cusp a := by
    change cusp (d * a.1, d * a.2) = cusp a
    rcases hd' with h | h
    · simp [h]
    · simp only [h, neg_one_mul]
      simp [cusp]
  have hp := path_eq_manin P hinv m hm
  change P (cusp m.right) (cusp m.left) = manin P m.label at hp
  rw [hc] at hp
  simpa [m, d, CuspMatrix.label] using hp.symm

/-- Summing successive oriented edges telescopes to the endpoints. -/
theorem edge_sum_telescope {K : Type*} [AddCommGroup K]
    (P : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, P x y + P y z = P x z)
    (a : Column) (xs : List Column) :
    (((a :: xs).zipWith (fun x y => P (cusp x) (cusp y)) xs)).sum =
      P (cusp a) (cusp (xs.foldl (fun _ x => x) a)) := by
  have hdiag (x : OnePoint ℚ) : P x x = 0 := by
    have h : P x x + P x x = P x x + 0 := by simpa using hadd x x x
    exact add_left_cancel h
  induction xs generalizing a with
  | nil => simp [hdiag]
  | cons b xs ih =>
    simp only [List.zipWith_cons_cons, List.sum_cons, List.foldl_cons]
    rw [ih]
    exact hadd _ _ _

private def edgeDet (a b : Column) : ℤ := b.1 * a.2 - a.1 * b.2

private def edgeIndex (a b : Column) : Index := project b.2 (edgeDet a b * a.2)

/-- Evaluate every edge of a chain whose adjacent determinants are `±1`. -/
theorem edge_labels_evaluation {K : Type*} [AddCommGroup K]
    (P : OnePoint ℚ → OnePoint ℚ → K) (hinv : Gamma0Invariant P)
    (a : Column) (xs : List Column)
    (hdet : ∀ z ∈ (a :: xs).zipWith edgeDet xs, z = 1 ∨ z = -1) :
    (((a :: xs).zipWith edgeIndex xs).map (manin P)).sum =
      (((a :: xs).zipWith (fun x y => P (cusp x) (cusp y)) xs)).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    have hab : edgeDet a b = 1 ∨ edgeDet a b = -1 := by
      apply hdet (edgeDet a b)
      simp
    have hrest : ∀ z ∈ (b :: xs).zipWith edgeDet xs, z = 1 ∨ z = -1 := by
      intro z hz
      apply hdet z
      simp only [List.zipWith_cons_cons, List.mem_cons]
      exact Or.inr hz
    simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
    rw [show manin P (edgeIndex a b) = P (cusp a) (cusp b) from
      pair_step_evaluation P hinv a b hab, ih b hrest]

private theorem getLast_eq_fold (a : Column) (xs : List Column) :
    (a :: xs).getLast? = some (xs.foldl (fun _ x => x) a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih =>
    simpa [List.getLast?, List.foldl] using ih b

/-- The finite Fricke label list evaluates to the period between its certified endpoints. -/
theorem fricke_path_certified_endpoints {K : Type*} [AddCommGroup K]
    (P : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, P x y + P y z = P x z)
    (hinv : Gamma0Invariant P) (i : Index) :
    ((Fricke.frickePath i).map (manin P)).sum =
      P (cusp (if i = 389 then (0, 1) else (1, 0)))
        (cusp (if i = 389 then (1, 0) else if i = 0 then (0, 1)
          else (-(i.val : ℤ), 389))) := by
  have hs := Fricke.frickeCusps_spec i
  cases hl : Fricke.frickeCusps i with
  | nil => simp [hl] at hs
  | cons a xs =>
    have ha : a = (if i = 389 then (0, 1) else (1, 0)) := by
      simpa [hl] using hs.1
    have hb : xs.foldl (fun _ x => x) a =
        (if i = 389 then (1, 0) else if i = 0 then (0, 1)
          else (-(i.val : ℤ), 389)) := by
      have hlast := hs.2.1
      rw [hl, getLast_eq_fold] at hlast
      exact Option.some.inj hlast
    have hdet : ∀ z ∈ (a :: xs).zipWith edgeDet xs, z = 1 ∨ z = -1 := by
      have h := hs.2.2
      rw [hl] at h
      exact h
    have he := edge_labels_evaluation P hinv a xs hdet
    have ht := edge_sum_telescope P hadd a xs
    unfold Fricke.frickePath
    rw [hl]
    change (((a :: xs).zipWith edgeIndex xs).map (manin P)).sum = _
    rw [he, ht, hb, ha]

/-- The certified finite chain is the Fricke image of a Manin representative. -/
theorem fricke_path_evaluation {K : Type*} [AddCommGroup K]
    (P : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, P x y + P y z = P x z)
    (hinv : Gamma0Invariant P) (i : Index) :
    ((Fricke.frickePath i).map (manin P)).sum =
      P (PeriodFaithfulFrickePath.frickeQ 389 •
          cusp (PeriodFaithfulHecke.representative i).right)
        (PeriodFaithfulFrickePath.frickeQ 389 •
          cusp (PeriodFaithfulHecke.representative i).left) := by
  rw [fricke_path_certified_endpoints P hadd hinv i]
  by_cases hi : i = 389
  · subst i
    simp [PeriodFaithfulHecke.representative, PeriodFaithfulFrickePath.frickeQ,
      cusp, OnePoint.smul_infty_eq_ite, OnePoint.smul_some_eq_ite]
  · by_cases hz : i = 0
    · subst i
      simp [PeriodFaithfulHecke.representative,
        PeriodFaithfulFrickePath.frickeQ, cusp, OnePoint.smul_infty_eq_ite,
        OnePoint.smul_some_eq_ite]
    · have hzv : i.val ≠ 0 := fun h => hz (Fin.ext h)
      simp [hi, hz, hzv, PeriodFaithfulHecke.representative,
        PeriodFaithfulFrickePath.frickeQ, cusp,
        OnePoint.smul_some_eq_ite]
      have hq : (i.val : ℚ) ≠ 0 := by exact_mod_cast hzv
      congr 2
      field_simp

end BSD.RankTwo.PeriodFaithfulFrickeColumns
