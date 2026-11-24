import BSD.RankTwo.ModularSymbolsMellin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Tactic

/-!
# Geometric Hecke paths for the level-389 central symbol

An oriented cusp path is read from the second column to the first. For the
three determinant-two representatives of `T₂`, the primitive columns either
already form a unimodular edge or can be joined through their midpoint. The
finite checks below certify the endpoints and determinant of each resulting
edge, as well as the match with the four Merel labels in the modular-symbol
certificate.
-/

namespace BSD.RankTwo.ModularSymbols.Farey

/-- A homogeneous integer lift of a rational cusp. -/
abbrev Column := ℤ × ℤ

/-- The rational cusp of a nonzero homogeneous lift. -/
def cusp (v : Column) : OnePoint ℚ :=
  if v.2 = 0 then OnePoint.infty else OnePoint.some ((v.1 : ℚ) / v.2)

/-- Integer two by two matrices in column order. -/
structure CuspMatrix where
  left : Column
  right : Column

namespace CuspMatrix

def det (m : CuspMatrix) : ℤ :=
  m.left.1 * m.right.2 - m.right.1 * m.left.2

def act (m : CuspMatrix) (u : Column) : Column :=
  (m.left.1 * u.1 + m.right.1 * u.2, m.left.2 * u.1 + m.right.2 * u.2)

def comp (m n : CuspMatrix) : CuspMatrix :=
  ⟨m.act n.left, m.act n.right⟩

private def adj (m : CuspMatrix) : CuspMatrix :=
  ⟨(m.right.2, -m.left.2), (-m.right.1, m.left.1)⟩

theorem det_comp (m n : CuspMatrix) : (m.comp n).det = m.det * n.det := by
  simp [comp, act, det]
  ring

private theorem det_adj (m : CuspMatrix) : m.adj.det = m.det := by
  simp [adj, det]
  ring

private theorem act_comp (m n : CuspMatrix) (u : Column) :
    (m.comp n).act u = m.act (n.act u) := by
  apply Prod.ext <;> simp [comp, act] <;> ring

private theorem div_comp_eq (m n : CuspMatrix) (hn : n.det = 1) :
    (m.comp n.adj).comp n = m := by
  have h₁ : n.adj.act n.left = (1, 0) := by
    apply Prod.ext
    · simpa [act, adj, det, mul_comm, sub_eq_add_neg] using hn
    · simp [act, adj, mul_comm]
  have h₂ : n.adj.act n.right = (0, 1) := by
    apply Prod.ext
    · simp [act, adj, mul_comm]
    · simpa [act, adj, det, mul_comm, sub_eq_add_neg, add_comm] using hn
  cases m with
  | mk a b =>
    let m : CuspMatrix := ⟨a, b⟩
    change CuspMatrix.mk ((m.comp n.adj).act n.left) ((m.comp n.adj).act n.right) = m
    rw [act_comp, act_comp, h₁, h₂]
    simp [act, m]

/-- Bottom-row projective label. -/
def label (m : CuspMatrix) : Index := project m.left.2 m.right.2

end CuspMatrix

open CuspMatrix

local instance : Fact (Nat.Prime 389) := ⟨by norm_num⟩

private theorem bottom_cross_dvd {c d e f : ℤ} (h : project c d = project e f) :
    (389 : ℤ) ∣ c * f - d * e := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  have hh := congrArg Fin.val h
  by_cases hd : (d : ZMod 389) = 0
  · by_cases hf : (f : ZMod 389) = 0
    · simp [hd, hf]
    · simp [project, hd, hf] at hh
      have he := ZMod.val_lt ((e : ZMod 389) * (f : ZMod 389)⁻¹)
      omega
  · by_cases hf : (f : ZMod 389) = 0
    · simp [project, hd, hf] at hh
      have hc := ZMod.val_lt ((c : ZMod 389) * (d : ZMod 389)⁻¹)
      omega
    · have hz : (c : ZMod 389) / d = (e : ZMod 389) / f := by
        apply ZMod.val_injective 389
        simpa [project, hd, hf, div_eq_mul_inv] using hh
      rw [mul_comm (d : ZMod 389), sub_eq_zero]
      exact (div_eq_div_iff hd hf).mp hz

private def representative (i : Index) : CuspMatrix :=
  if i = 389 then ⟨(0, 1), (-1, 0)⟩ else ⟨(1, i.val), (0, 1)⟩

private theorem representative_det (i : Index) : (representative i).det = 1 := by
  by_cases h : i = 389 <;> simp [representative, h, det]

private def sMatrix (m : CuspMatrix) : CuspMatrix :=
  ⟨m.right, (-m.left.1, -m.left.2)⟩

private def rMatrix (m : CuspMatrix) : CuspMatrix :=
  ⟨m.right, (-m.left.1-m.right.1, -m.left.2-m.right.2)⟩

private theorem s_det (m : CuspMatrix) : (sMatrix m).det = m.det := by
  simp [sMatrix, det]
  ring

private theorem r_det (m : CuspMatrix) : (rMatrix m).det = m.det := by
  simp [rMatrix, det]
  ring

private theorem r_right_twice (m : CuspMatrix) : (rMatrix (rMatrix m)).right = m.left := by
  apply Prod.ext <;> simp [rMatrix] <;> ring

/-- The three upper triangular determinant-two matrices in the Hecke correspondence. -/
def heckeMatrices : List CuspMatrix :=
  [⟨(2, 0), (0, 1)⟩, ⟨(1, 0), (0, 2)⟩, ⟨(1, 0), (1, 2)⟩]

private def primitive (u : Column) : Column :=
  let scale : ℤ := Int.gcd u.1 u.2
  (u.1 / scale, u.2 / scale)

private def normalized (m : CuspMatrix) : CuspMatrix :=
  ⟨primitive m.left, primitive m.right⟩

private def subdivide (m : CuspMatrix) : List CuspMatrix :=
  let n := normalized m
  if n.det = 1 then [n] else
    let middle : Column := ((n.left.1+n.right.1) / 2, (n.left.2+n.right.2) / 2)
    [⟨middle, n.right⟩, ⟨n.left, middle⟩]

private def heckeEdges (i : Index) : List CuspMatrix :=
  heckeMatrices.flatMap fun t => subdivide (t.comp (representative i))

local instance : DecidableEq (OnePoint ℚ) := inferInstanceAs (DecidableEq (Option ℚ))

private def validSubdivision (m : CuspMatrix) : Bool :=
  decide (cusp (primitive m.left) = cusp m.left) &&
    decide (cusp (primitive m.right) = cusp m.right) &&
    (subdivide m).all (fun edge => decide (edge.det = 1))

private def checks (i : Index) : Bool :=
  let m := representative i
  decide (m.label = i) && decide ((sMatrix m).label = swap i) &&
    decide ((rMatrix m).label = rotate i) &&
    decide ((rMatrix (rMatrix m)).label = rotate (rotate i)) &&
    heckeMatrices.all (fun t => validSubdivision (t.comp m)) &&
    ((heckeEdges i).map label).isPerm (heckeTwo i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem checked : (List.finRange 390).all checks = true := by decide +kernel

private theorem checks_ok (i : Index) :
    let m := representative i
    m.label = i ∧ (sMatrix m).label = swap i ∧
      (rMatrix m).label = rotate i ∧ (rMatrix (rMatrix m)).label = rotate (rotate i) ∧
      (∀ t ∈ heckeMatrices, validSubdivision (t.comp m) = true) ∧
      ((heckeEdges i).map label).Perm (heckeTwo i) := by
  have h := List.all_eq_true.mp checked i (List.mem_finRange i)
  simpa [checks, Bool.and_eq_true, List.all_eq_true, List.isPerm_iff, and_assoc] using h

variable {K : Type*}

/-- Period from the second-column cusp to the first-column cusp. -/
def path (period : OnePoint ℚ → OnePoint ℚ → K) (m : CuspMatrix) : K :=
  period (cusp m.right) (cusp m.left)

/-- Invariance of a cusp period under determinant-one matrices with lower-left entry
divisible by 389, applied to unimodular paths. -/
def Gamma0Invariant (period : OnePoint ℚ → OnePoint ℚ → K) : Prop :=
  ∀ g : CuspMatrix, g.det = 1 → (389 : ℤ) ∣ g.left.2 →
    ∀ m : CuspMatrix, m.det = 1 → path period (g.comp m) = path period m

/-- The period function on the 390 representatives used in the finite certificate. -/
def manin (period : OnePoint ℚ → OnePoint ℚ → K) (i : Index) : K :=
  path period (representative i)

/-- A unimodular edge gives the period of the representative with the same bottom-row label. -/
theorem path_eq_manin (period : OnePoint ℚ → OnePoint ℚ → K)
    (hinv : Gamma0Invariant period) (m : CuspMatrix) (hm : m.det = 1) :
    path period m = manin period m.label := by
  let n := representative m.label
  have hn : n.det = 1 := representative_det _
  have hl : n.label = m.label := (checks_ok m.label).1
  have hg : (m.comp n.adj).det = 1 := by rw [det_comp, det_adj, hm, hn, mul_one]
  have hd : (389 : ℤ) ∣ (m.comp n.adj).left.2 := by
    change (389 : ℤ) ∣ m.left.2 * n.right.2 + m.right.2 * -n.left.2
    have h := bottom_cross_dvd hl.symm
    simpa [sub_eq_add_neg, mul_neg, label] using h
  simpa [div_comp_eq m n hn, manin, n] using hinv (m.comp n.adj) hg hd n hn

variable [AddCommGroup K]

private theorem path_subdivide (period : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, period x y + period y z = period x z)
    (m : CuspMatrix) (h : validSubdivision m = true) :
    ((subdivide m).map (path period)).sum = path period m := by
  have h' : cusp (primitive m.left) = cusp m.left ∧ cusp (primitive m.right) = cusp m.right ∧
      ∀ t ∈ subdivide m, t.det = 1 := by
    simpa [validSubdivision, Bool.and_eq_true, List.all_eq_true, and_assoc] using h
  unfold subdivide
  dsimp only
  split
  · simp [normalized, path, h'.1, h'.2.1]
  · simp [normalized, path, h'.1, h'.2.1, hadd]

/-- The four finite Merel labels evaluate to the sum of periods over the three
geometric (T_2) translates of the representative path. -/
theorem merel_eq_heckeCorrespondence (period : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, period x y + period y z = period x z)
    (hinv : Gamma0Invariant period) (i : Index) :
    ((heckeTwo i).map (manin period)).sum =
      (heckeMatrices.map fun t => path period (t.comp (representative i))).sum := by
  have h := checks_ok i
  rw [← (h.2.2.2.2.2.map (manin period)).sum_eq, List.map_map]
  let m := representative i
  have hGood (t : CuspMatrix) (ht : t ∈ heckeMatrices) :
      (((subdivide (t.comp m)).map (manin period ∘ label))).sum =
        path period (t.comp m) := by
    have hs := h.2.2.2.2.1 t ht
    have hv : cusp (primitive (t.comp m).left) = cusp (t.comp m).left ∧
        cusp (primitive (t.comp m).right) = cusp (t.comp m).right ∧
        ∀ u ∈ subdivide (t.comp m), u.det = 1 := by
      simpa [validSubdivision, Bool.and_eq_true, List.all_eq_true, and_assoc] using hs
    have hp := hv.2.2
    have hmap : (subdivide (t.comp m)).map (manin period ∘ label) =
        (subdivide (t.comp m)).map (path period) := by
      apply List.map_congr_left
      intro u hu
      exact (path_eq_manin period hinv u (hp u hu)).symm
    rw [hmap, path_subdivide period hadd (t.comp m) hs]
  change ((heckeMatrices.flatMap fun t => subdivide (t.comp m)).map
    (manin period ∘ label)).sum = _
  have hsum (ts : List CuspMatrix) (hs : ∀ t ∈ ts, t ∈ heckeMatrices) :
      ((ts.flatMap fun t => subdivide (t.comp m)).map (manin period ∘ label)).sum =
        (ts.map fun t => path period (t.comp m)).sum := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [hGood t (hs _ (List.mem_cons_self)), ih (fun u hu => hs _ (List.mem_cons_of_mem _ hu))]
  exact hsum _ (fun _ ht => ht)

private theorem cusp_neg (v : Column) : cusp (-v.1, -v.2) = cusp v := by
  by_cases h : v.2 = 0 <;> simp [cusp, h]

private theorem diagonal_zero (period : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, period x y + period y z = period x z) (x : OnePoint ℚ) :
    period x x = 0 := by
  apply add_left_cancel (a := period x x)
  simpa using hadd x x x

/-- Orientation reversal gives the two-term Manin relation for geometric periods. -/
theorem manin_swap (period : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, period x y + period y z = period x z)
    (hinv : Gamma0Invariant period) (i : Index) :
    manin period i + manin period (swap i) = 0 := by
  let m := representative i
  have hm : (sMatrix m).det = 1 := (s_det m).trans (representative_det i)
  rw [← (checks_ok i).2.1, ← path_eq_manin period hinv _ hm]
  simp only [manin, path, sMatrix, cusp_neg]
  rw [hadd, diagonal_zero period hadd]

/-- Traversing a triangle gives the three-term Manin relation for geometric periods. -/
theorem manin_rotate (period : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, period x y + period y z = period x z)
    (hinv : Gamma0Invariant period) (i : Index) :
    manin period i + manin period (rotate i) + manin period (rotate (rotate i)) = 0 := by
  let m := representative i
  have h₁ : (rMatrix m).det = 1 := (r_det m).trans (representative_det i)
  have h₂ : (rMatrix (rMatrix m)).det = 1 := (r_det _).trans h₁
  have h := checks_ok i
  rw [← h.2.2.2.1, ← h.2.2.1, ← path_eq_manin period hinv _ h₁,
    ← path_eq_manin period hinv _ h₂]
  simp only [manin, path, r_right_twice]
  change period (cusp m.right) (cusp m.left) +
      period (cusp (rMatrix m).right) (cusp m.right) +
      period (cusp m.left) (cusp (rMatrix m).right) = 0
  rw [add_comm (period (cusp m.right) (cusp m.left)), hadd, hadd, diagonal_zero period hadd]

omit [AddCommGroup K] in
theorem manin_zero (period : OnePoint ℚ → OnePoint ℚ → K) :
    manin period 0 = period (OnePoint.some 0) OnePoint.infty := by
  simp [manin, representative, path, cusp]

/-- The vanishing certificate applies to a genuine cusp-path functional once its
periods are additive, invariant, and paired with a weight-two (T_2=-2) eigenform.
The Hecke input uses the geometric determinant-two translates. -/
theorem central_period_eq_zero {K : Type*} [Field K] [CharZero K]
    (period : OnePoint ℚ → OnePoint ℚ → K)
    (hadd : ∀ x y z, period x y + period y z = period x z)
    (hinv : Gamma0Invariant period)
    (hHecke : ∀ m : CuspMatrix, m.det = 1 →
      (heckeMatrices.map fun t => path period (t.comp m)).sum = (-2 : K) * path period m) :
    period (OnePoint.some 0) OnePoint.infty = 0 := by
  rw [← manin_zero period]
  apply ModularSymbols.centralPath_eq_zero (manin period)
    (manin_swap period hadd hinv) (manin_rotate period hadd hinv)
  intro i
  rw [merel_eq_heckeCorrespondence period hadd hinv]
  exact hHecke _ (representative_det i)

/-- Application to Mathlib's actual weight-two cusp forms. The analytic input
identifies the period on the vertical path with its imaginary-axis integral.
The Hecke input is the geometric correspondence, already in cusp coordinates. -/
theorem cuspForm_L_one_eq_zero_of_geometric_symbols
    (f : CuspForm (CongruenceSubgroup.Gamma0 389) 2)
    (period : OnePoint ℚ → OnePoint ℚ → ℂ)
    (hadd : ∀ x y z, period x y + period y z = period x z)
    (hinv : Gamma0Invariant period)
    (hHecke : ∀ m : CuspMatrix, m.det = 1 →
      (heckeMatrices.map fun t => path period (t.comp m)).sum = (traceTwo : ℂ) * path period m)
    (hCentral : period (OnePoint.some 0) OnePoint.infty =
      Complex.I * ∫ t in Set.Ioi (0 : ℝ), f (UpperHalfPlane.ofComplex (Complex.I * t))) :
    ModularForm.L (by decide : 0 < (2 : ℤ)) f 1 = 0 := by
  refine ModularSymbols.cuspForm_L_one_eq_zero_of_manin f (manin period)
    (manin_swap period hadd hinv) (manin_rotate period hadd hinv) ?_ ((manin_zero period).trans hCentral)
  intro i
  rw [merel_eq_heckeCorrespondence period hadd hinv]
  exact hHecke _ (representative_det i)

end BSD.RankTwo.ModularSymbols.Farey
