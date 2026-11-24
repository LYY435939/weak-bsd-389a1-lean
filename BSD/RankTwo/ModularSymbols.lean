import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A modular-symbol certificate at level 389

The generators are indexed by the bottom-row ratios in `ℙ¹(𝔽₃₈₉)`, with the
point at infinity represented by 389. A matrix acts on the oriented path from
0 to infinity. The two Manin relations come from right multiplication by
`[0,-1; 1,0]` and `[0,-1; 1,-1]`. The four-term Hecke action is Merel's formula at the prime 2, as stated in
§2.3 of Stein's *An introduction to computing modular forms using modular
symbols*.

The certificate is an integer linear combination of these relations and the
relations imposing eigenvalue −2 for `T₂`. It was found by rational row
reduction. The proof checks its integer coefficients in Lean.
See W. Stein, *An introduction to computing modular forms using modular
symbols*, §§2–3, for the Manin relations and the Hecke action.
-/

namespace BSD.RankTwo.ModularSymbols

/-- Bottom-row ratio labels, with 389 denoting infinity. -/
abbrev Index := Fin 390

/-- The projective ratio of the first coordinate to the second modulo 389. -/
def project (c d : ℤ) : Index :=
  if (d : ZMod 389) = 0 then 389
  else ⟨((c : ZMod 389) * (d : ZMod 389)⁻¹).val,
    (ZMod.val_lt _).trans (show 389 < 390 by decide)⟩

private def row (i : Index) : ℤ × ℤ :=
  if i = 389 then (1, 0) else (i.val, 1)

/-- Right multiplication by the order-two matrix on projective row labels. -/
def swap (i : Index) : Index :=
  let (c, d) := row i
  project d (-c)

/-- Right multiplication by the order-three matrix on projective row labels. -/
def rotate (i : Index) : Index :=
  let (c, d) := row i
  project d (-c-d)

/-- Merel's four-term formula for `T₂` on Manin symbols at odd level. -/
def heckeTwo (i : Index) : List Index :=
  let (c, d) := row i
  [project c (2 * d), project (2 * c) d, project (2 * c) (c + d), project (c + d) (2 * d)]

private inductive Relation where
  | swap | rotate | hecke

private def terms : Relation → Index → List Index
  | .swap, i => [i, swap i]
  | .rotate, i => [i, rotate i, rotate (rotate i)]
  | .hecke, i => heckeTwo i ++ [i, i]

private def weighted (relation : Relation) (data : List (Index × ℤ)) :
    List (Relation × Index × ℤ) :=
  data.map fun (i, coeff) => (relation, i, coeff)

private def certificate : List (Relation × Index × ℤ) :=
  weighted .swap [
    (0, -30), (1, -30), (2, -84), (3, 1), (4, 176), (5, 366),
    (6, -11), (7, 121), (8, 53), (9, 464), (10, -20), (11, -59),
    (12, -27), (13, 79), (14, 123), (16, -84), (17, 247), (18, 82),
    (19, -59), (20, -59), (21, 271), (22, 124), (23, 46), (24, 370),
    (25, 130), (26, 196), (27, 290), (28, 510), (29, 413), (30, 388),
    (31, 26), (32, 81), (33, 56), (34, 190), (35, 127), (36, 135),
    (38, 161), (39, 211), (40, 254), (41, 310), (42, 90), (43, 224),
    (44, 310), (45, 258), (46, 535), (47, 532), (48, 219), (49, 284),
    (50, 449), (51, 341), (52, -79), (55, 190), (56, 288), (57, 356),
    (58, 121), (59, 121), (60, 141), (62, 273), (63, 161), (64, 157),
    (65, 87), (66, 193), (67, 303), (68, 345), (71, 510), (73, 290),
    (74, 209), (75, -11), (76, 215), (77, 199), (78, 27), (80, 157),
    (82, 357), (83, 247), (84, 96), (85, 321), (86, 101), (88, 215),
    (89, 264), (90, 264), (91, 642), (92, 642), (94, 425), (95, 274),
    (96, 274), (98, 176), (101, 127), (102, 237), (103, 27), (104, -27),
    (105, -27), (107, -59), (109, 53), (110, -6), (112, 121), (113, 121),
    (115, -57), (117, 264), (119, 274), (122, 468), (123, 468), (124, 468),
    (128, 284), (129, -26), (130, -26), (131, 27), (132, -27), (133, 127),
    (134, 211), (135, 321), (136, 59), (137, 81), (139, 26), (144, 83),
    (145, 83), (146, 59), (147, 211), (148, 211), (149, 101), (150, 54),
    (151, 230), (152, 230), (154, 101), (155, 1), (156, 1), (157, 1),
    (160, 81), (161, 79), (164, -27), (167, 1), (168, 54), (169, 101),
    (171, 211), (173, 211), (176, -59), (177, 81), (180, 121), (181, 53),
    (184, 247), (190, 54), (193, 1), (195, -84), (197, 433), (198, 361),
    (200, 64), (201, 136), (202, 83), (206, 290), (207, 310), (210, 371),
    (211, 151), (214, 90), (215, 117), (217, 583), (219, 264), (223, 358),
    (224, 123), (226, 127), (227, 125), (230, 358), (231, 123), (236, 230),
    (246, 121), (247, -11), (251, 123), (262, 15), (263, -95), (264, 24),
    (268, 101), (269, 101), (271, 211), (273, 208), (274, 104), (275, 151),
    (278, 193), (281, 310), (283, 125), (289, -27), (290, -27), (292, 27),
    (296, 101), (302, 274), (310, -11), (317, -84), (319, 83), (320, 83),
    (328, 83)
  ] ++
  weighted .rotate [
    (0, 30), (1, 84), (2, -1), (3, -176), (4, -366), (5, 11),
    (6, -121), (7, -53), (8, -583), (9, 20), (10, 59), (11, 27),
    (12, -79), (13, -123), (15, 84), (16, -247), (17, -53), (18, 59),
    (19, 59), (20, -161), (21, -124), (22, -46), (23, -370), (24, -130),
    (25, -26), (26, -290), (27, -510), (28, -468), (29, -178), (30, -26),
    (31, -81), (32, -56), (33, -190), (34, -127), (35, -245), (38, -211),
    (39, -135), (40, -310), (41, -90), (42, -150), (43, -310), (44, -258),
    (45, -425), (46, -532), (47, -230), (48, -284), (49, -508), (50, -341),
    (51, 79), (55, -288), (56, -356), (57, 114), (58, -121), (59, -141),
    (62, -273), (63, -157), (64, -87), (65, -193), (66, -371), (67, -345),
    (73, -290), (74, 11), (75, -215), (76, -199), (77, -27), (82, -247),
    (83, -96), (84, -211), (85, -101), (88, -274), (89, -264), (90, -264),
    (91, -642), (94, -274), (95, -274), (101, -127), (102, -27), (103, 27),
    (104, 27), (109, -53), (112, -121), (122, -468), (123, -468), (128, -284),
    (129, 26), (130, -27), (131, 27), (132, -138), (133, -211), (134, -211),
    (135, -101), (136, -81), (144, -83), (145, 27), (146, -211), (147, -211),
    (148, -101), (149, -101), (150, -167), (151, -230), (154, -15), (155, -1),
    (156, -1), (160, -79), (167, -54), (168, -101), (176, -54), (180, -121),
    (197, -361), (200, -136), (201, -83), (206, -310), (210, -151), (214, -117),
    (223, -123), (226, -125), (230, -123), (246, -94), (247, 11), (262, 95),
    (263, 84), (268, -101), (273, -208), (289, 27), (319, -83)
  ] ++
  weighted .hecke [
    (0, 58), (2, -54), (3, 182), (4, 11), (5, -83), (6, -106),
    (7, 55), (8, 167), (9, -178), (10, -33), (11, 105), (12, 57),
    (14, -178), (15, 68), (16, 117), (17, -117), (18, -11), (20, 110),
    (21, -29), (22, -170), (23, 217), (24, -119), (25, -108), (26, 152),
    (27, 110), (28, 68), (30, -220), (32, -70), (33, 13), (34, 27),
    (35, 59), (39, 60), (40, -27), (41, -110), (42, 21), (43, 98),
    (44, 59), (46, -110), (47, -151), (48, 92), (49, 112), (51, -210),
    (57, -235), (59, 10), (63, -2), (65, 53), (66, 55), (74, -110),
    (75, 113), (76, -63), (77, -86), (84, 47), (85, -110), (103, -27),
    (132, 55), (133, 42), (135, -110), (136, 11)
  ]

private noncomputable def symbol (i : Index) : Index →₀ ℤ := Finsupp.single i 1

private noncomputable def vector (xs : List Index) : Index →₀ ℤ := (xs.map symbol).sum

private noncomputable def certificateVector : Index →₀ ℤ :=
  (certificate.map fun (relation, i, coeff) => coeff • vector (terms relation i)).sum

private def coefficient (xs : List Index) (j : Index) : ℤ :=
  (xs.map fun i => if i = j then 1 else 0).sum

private def checkedCoefficient (j : Index) : ℤ :=
  (certificate.map fun (relation, i, coeff) => coeff * coefficient (terms relation i) j).sum

private theorem vector_apply (xs : List Index) (j : Index) :
    vector xs j = coefficient xs j := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change (symbol i + vector xs) j = (if i = j then 1 else 0) + coefficient xs j
    simp [symbol, Finsupp.single_apply, ih]

private theorem certificateVector_apply (j : Index) :
    certificateVector j = checkedCoefficient j := by
  unfold certificateVector checkedCoefficient
  generalize certificate = l
  induction l with
  | nil => rfl
  | cons term xs ih =>
    obtain ⟨r, i, c⟩ := term
    simp [ih, vector_apply, zsmul_eq_mul]

private def tally (rows : List (Index × ℤ)) (initial : Vector ℤ 390) : Vector ℤ 390 :=
  rows.foldl (fun acc (i, c) => acc.set i.val (acc[i.val] + c)) initial

private theorem tally_get (rows : List (Index × ℤ)) (initial : Vector ℤ 390) (j : Index) :
    (tally rows initial)[j.val] =
      initial[j.val] + (rows.map fun (i, c) => if i = j then c else 0).sum := by
  induction rows generalizing initial with
  | nil => simp [tally]
  | cons term rows ih =>
    obtain ⟨i, c⟩ := term
    simp only [tally, List.foldl_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Vector.getElem_set]
    by_cases h : i = j
    · subst i
      simp [add_assoc]
    · have hd : i.val ≠ j.val := fun eq => h (Fin.ext eq)
      simp [h, hd]

private def expand (rows : List (Relation × Index × ℤ)) : List (Index × ℤ) :=
  rows.flatMap fun (r, i, c) => (terms r i).map fun j => (j, c)

private theorem expand_sum (rows : List (Relation × Index × ℤ)) (j : Index) :
    ((expand rows).map fun (i, c) => if i = j then c else 0).sum =
      (rows.map fun (r, i, c) => c * coefficient (terms r i) j).sum := by
  induction rows with
  | nil => rfl
  | cons term rows ih =>
    obtain ⟨r, i, c⟩ := term
    change (((terms r i).map (fun k => (k, c)) ++ expand rows).map
      (fun (k, v) => if k = j then v else 0)).sum =
        c * coefficient (terms r i) j + _
    rw [List.map_append, List.sum_append, ih]
    congr 1
    simp [coefficient, List.map_map, Function.comp_def, ← List.sum_map_mul_left, mul_ite]

private def expected : Vector ℤ 390 := (Vector.replicate 390 0).set 0 290

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem checkedTally : tally (expand certificate) (Vector.replicate 390 0) = expected := by
  decide +kernel

private theorem checked (j : Index) :
    checkedCoefficient j = if (0 : Index) = j then 290 else 0 := by
  have h := congrArg (fun v : Vector ℤ 390 => v[j.val]) checkedTally
  simp only [tally_get, Vector.getElem_replicate, zero_add, expand_sum] at h
  change checkedCoefficient j = _ at h
  rw [expected, Vector.getElem_set] at h
  by_cases hj : (0 : Index) = j
  · subst j
    simpa using h
  · have hd : 0 ≠ j.val := fun eq => hj (Fin.ext eq)
    simpa [hj, hd] using h

private theorem certificate_eq : certificateVector = (290 : ℤ) • symbol 0 := by
  ext j
  rw [certificateVector_apply, checked]
  by_cases hj : (0 : Index) = j <;> simp [symbol, hj]

/-- A characteristic-zero field valued Manin functional of Hecke eigenvalue `−2`
annihilates the oriented central path. -/
theorem centralPath_eq_zero {K : Type*} [Field K] [CharZero K] (period : Index → K)
    (hSwap : ∀ i, period i + period (swap i) = 0)
    (hRotate : ∀ i, period i + period (rotate i) + period (rotate (rotate i)) = 0)
    (hHecke : ∀ i, ((heckeTwo i).map period).sum = (-2 : K) * period i) :
    period 0 = 0 := by
  let evaluate := Finsupp.linearCombination ℤ period
  have hSymbol (i : Index) : evaluate (symbol i) = period i := by
    simp [evaluate, symbol]
  have hVector (l : List Index) : evaluate (vector l) = (l.map period).sum := by
    induction l with
    | nil => simp [vector]
    | cons i xs ih => simpa [vector, hSymbol] using congrArg (period i + ·) ih
  have hTerms (r : Relation) (i : Index) : evaluate (vector (terms r i)) = 0 := by
    rw [hVector]
    cases r with
    | swap => simpa [terms] using hSwap i
    | rotate => simpa [terms, add_assoc] using hRotate i
    | hecke =>
      simp only [terms, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero, hHecke]
      ring
  have hZero : evaluate certificateVector = 0 := by
    rw [certificateVector]
    let l := certificate
    change evaluate (l.map fun (r, i, c) => c • vector (terms r i)).sum = 0
    induction l with
    | nil => simp
    | cons term xs ih =>
      obtain ⟨r, i, c⟩ := term
      simp [ih, hTerms]
  have h := congrArg evaluate certificate_eq
  rw [hZero, map_zsmul, hSymbol] at h
  rw [zsmul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

end BSD.RankTwo.ModularSymbols
