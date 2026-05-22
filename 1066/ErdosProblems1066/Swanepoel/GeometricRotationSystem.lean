import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.List

/-!
# Geometric rotation systems for S2

This module gives the S2 drawing layer a concrete angular order at each
vertex.  Outgoing unit-distance darts are represented by their complex
direction vector, ordered by `Complex.arg`; equal angular directions are
tie-broken by the finite vertex index so that the result is a deterministic
finite sorted list.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometricRotationSystem

open PlanarInterface
open JordanTopologyFactsConcrete.MinimalFailureTopology

abbrev Point : Type :=
  PlanarInterface.Point

/-! ## Complex directions -/

/-- Embed the project-local real plane into `ℂ`. -/
def pointToComplex (p : Point) : Complex :=
  ⟨p.1, p.2⟩

@[simp]
theorem pointToComplex_re (p : Point) :
    (pointToComplex p).re = p.1 :=
  rfl

@[simp]
theorem pointToComplex_im (p : Point) :
    (pointToComplex p).im = p.2 :=
  rfl

theorem pointToComplex_injective :
    Function.Injective pointToComplex := by
  intro p q hpq
  exact Prod.ext (congrArg Complex.re hpq) (congrArg Complex.im hpq)

/-- The complex vector from `tail` to `head`. -/
def dartVector (tail head : Point) : Complex :=
  pointToComplex head - pointToComplex tail

@[simp]
theorem dartVector_re (tail head : Point) :
    (dartVector tail head).re = head.1 - tail.1 := by
  simp [dartVector]

@[simp]
theorem dartVector_im (tail head : Point) :
    (dartVector tail head).im = head.2 - tail.2 := by
  simp [dartVector]

/-- The principal angular coordinate of a directed geometric dart. -/
def dartArg (tail head : Point) : Real :=
  Complex.arg (dartVector tail head)

theorem dartArg_mem_Ioc (tail head : Point) :
    dartArg tail head ∈ Set.Ioc (-Real.pi) Real.pi := by
  exact Complex.arg_mem_Ioc (dartVector tail head)

theorem dartArg_le_pi (tail head : Point) :
    dartArg tail head <= Real.pi :=
  (dartArg_mem_Ioc tail head).2

theorem neg_pi_lt_dartArg (tail head : Point) :
    -Real.pi < dartArg tail head :=
  (dartArg_mem_Ioc tail head).1

theorem dartVector_ne_zero_of_ne {tail head : Point}
    (h : head ≠ tail) :
    dartVector tail head ≠ 0 := by
  intro hzero
  have hcomplex : pointToComplex head = pointToComplex tail := by
    exact sub_eq_zero.mp hzero
  exact h (pointToComplex_injective hcomplex)

theorem dartVector_ne_zero_of_eucDist_eq_one {tail head : Point}
    (hunit : Geometry.Distance.eucDist tail head = 1) :
    dartVector tail head ≠ 0 := by
  refine dartVector_ne_zero_of_ne ?_
  intro hsame
  have hdist_zero : Geometry.Distance.eucDist tail head = 0 := by
    simp [hsame]
  linarith

/-! ## Outgoing darts at a graph vertex -/

variable {n : Nat}

/-- The complex vector of the graph dart `center → head`. -/
def graphDartVector (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) : Complex :=
  dartVector (G.point center) (G.point head)

/-- The principal angular coordinate of the graph dart `center → head`. -/
def graphDartArg (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) : Real :=
  Complex.arg (graphDartVector G center head)

theorem graphDartArg_def (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) :
    graphDartArg G center head = dartArg (G.point center) (G.point head) :=
  rfl

theorem graphDartArg_mem_Ioc (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) :
    graphDartArg G center head ∈ Set.Ioc (-Real.pi) Real.pi := by
  exact Complex.arg_mem_Ioc (graphDartVector G center head)

theorem graphDartArg_le_pi (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) :
    graphDartArg G center head <= Real.pi :=
  (graphDartArg_mem_Ioc G center head).2

theorem neg_pi_lt_graphDartArg (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) :
    -Real.pi < graphDartArg G center head :=
  (graphDartArg_mem_Ioc G center head).1

theorem graphDartVector_ne_zero_of_adj
    (G : StraightLineUnitDistanceGraph n) {center head : Fin n}
    (hAdj : G.Adj center head) :
    graphDartVector G center head ≠ 0 := by
  exact dartVector_ne_zero_of_eucDist_eq_one (G.adj_geometry_dist_eq_one hAdj)

theorem graphDartVector_normSq_eq_eucDist_sq
    (G : StraightLineUnitDistanceGraph n) (center head : Fin n) :
    Complex.normSq (graphDartVector G center head) =
      Geometry.Distance.eucDist (G.point center) (G.point head) ^ 2 := by
  rw [Geometry.Distance.eucDist_sq]
  simp [Complex.normSq_apply, graphDartVector, dartVector, pointToComplex]
  ring

theorem graphDartVector_norm_of_adj
    (G : StraightLineUnitDistanceGraph n) {center head : Fin n}
    (hAdj : G.Adj center head) :
    ‖graphDartVector G center head‖ = 1 := by
  have hsq :
      Complex.normSq (graphDartVector G center head) = (1 : Real) := by
    rw [graphDartVector_normSq_eq_eucDist_sq]
    rw [G.adj_geometry_dist_eq_one hAdj]
    norm_num
  have hnorm_sq :
      ‖graphDartVector G center head‖ ^ 2 = (1 : Real) := by
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hnorm_sq' :
      ‖graphDartVector G center head‖ ^ 2 = (1 : Real) ^ 2 := by
    simpa using hnorm_sq
  exact
    (sq_eq_sq₀ (norm_nonneg (graphDartVector G center head))
      (by norm_num : (0 : Real) <= 1)).mp hnorm_sq'

theorem graphPoint_ne_of_vertex_ne
    (G : StraightLineUnitDistanceGraph n) {left right : Fin n}
    (hneq : left ≠ right) :
    G.point left ≠ G.point right := by
  intro hpoint
  have hsep :
      (1 : Real) <= _root_.eucDist (G.config.pts left) (G.config.pts right) :=
    G.config.sep left right hneq
  have hpts : G.config.pts left = G.config.pts right := by
    simpa [StraightLineUnitDistanceGraph.point] using hpoint
  rw [hpts, _root_.eucDist_self] at hsep
  norm_num at hsep

theorem outgoingNeighbor_graphDartVector_ne_of_head_ne
    (G : StraightLineUnitDistanceGraph n) {center left right : Fin n}
    (_hleft : G.Adj center left) (_hright : G.Adj center right)
    (hneq : left ≠ right) :
    graphDartVector G center left ≠ graphDartVector G center right := by
  intro hvec
  have hpoint : G.point left = G.point right := by
    apply pointToComplex_injective
    have hcancel :
        dartVector (G.point center) (G.point left) +
            pointToComplex (G.point center) =
          dartVector (G.point center) (G.point right) +
            pointToComplex (G.point center) := by
      simpa [graphDartVector] using congrArg
        (fun z : Complex => z + pointToComplex (G.point center)) hvec
    simpa [dartVector, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hcancel
  exact graphPoint_ne_of_vertex_ne G hneq hpoint

theorem outgoingNeighbor_graphDartArg_ne_of_head_ne
    (G : StraightLineUnitDistanceGraph n) {center left right : Fin n}
    (hleft : G.Adj center left) (hright : G.Adj center right)
    (hneq : left ≠ right) :
    graphDartArg G center left ≠ graphDartArg G center right := by
  intro harg
  have hnorm :
      ‖graphDartVector G center left‖ =
        ‖graphDartVector G center right‖ := by
    rw [graphDartVector_norm_of_adj G hleft,
      graphDartVector_norm_of_adj G hright]
  have hvec :
      graphDartVector G center left =
        graphDartVector G center right :=
    Complex.ext_norm_arg hnorm harg
  exact outgoingNeighbor_graphDartVector_ne_of_head_ne
    G hleft hright hneq hvec

/-- The finite set of heads of outgoing darts from `center`. -/
def outgoingNeighbors (G : StraightLineUnitDistanceGraph n)
    (center : Fin n) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter fun head => G.Adj center head

@[simp]
theorem mem_outgoingNeighbors_iff (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) :
    head ∈ outgoingNeighbors G center ↔ G.Adj center head := by
  classical
  simp [outgoingNeighbors]

theorem mem_outgoingNeighbors_iff_unitDistanceAdj
    (G : StraightLineUnitDistanceGraph n) (center head : Fin n) :
    head ∈ outgoingNeighbors G center ↔
      GraphBridge.UnitDistanceAdj G.config center head := by
  rw [mem_outgoingNeighbors_iff, G.adj_iff_unitDistanceAdj]

/-- Key an outgoing dart by `(principal angle, head index)`. -/
def angularDartKey (G : StraightLineUnitDistanceGraph n)
    (center head : Fin n) : Real × Fin n :=
  (graphDartArg G center head, head)

/-- The embedding used to turn outgoing heads into sortable angular darts. -/
def angularDartKeyEmbedding (G : StraightLineUnitDistanceGraph n)
    (center : Fin n) : Fin n ↪ Real × Fin n where
  toFun := angularDartKey G center
  inj' := by
    intro a b h
    exact congrArg Prod.snd h

/-- The finite set of outgoing darts, keyed by angle and then by head index. -/
def outgoingDartKeys (G : StraightLineUnitDistanceGraph n)
    (center : Fin n) : Finset (Real × Fin n) :=
  (outgoingNeighbors G center).map (angularDartKeyEmbedding G center)

theorem mem_outgoingDartKeys_iff
    (G : StraightLineUnitDistanceGraph n) (center : Fin n)
    {theta : Real} {head : Fin n} :
    (theta, head) ∈ outgoingDartKeys G center ↔
      G.Adj center head ∧ theta = graphDartArg G center head := by
  classical
  constructor
  · intro hmem
    rcases Finset.mem_map.1 hmem with ⟨head', hhead', hkey⟩
    have hhead_eq : head' = head := congrArg Prod.snd hkey
    subst head
    have htheta : graphDartArg G center head' = theta := congrArg Prod.fst hkey
    exact ⟨(mem_outgoingNeighbors_iff G center head').1 hhead', htheta.symm⟩
  · rintro ⟨hAdj, rfl⟩
    exact Finset.mem_map.2
      ⟨head, (mem_outgoingNeighbors_iff G center head).2 hAdj, rfl⟩

theorem mem_outgoingDartKeys_iff_unitDistanceAdj
    (G : StraightLineUnitDistanceGraph n) (center : Fin n)
    {theta : Real} {head : Fin n} :
    (theta, head) ∈ outgoingDartKeys G center ↔
      GraphBridge.UnitDistanceAdj G.config center head ∧
        theta = graphDartArg G center head := by
  rw [mem_outgoingDartKeys_iff]
  exact and_congr (G.adj_iff_unitDistanceAdj center head) Iff.rfl

/-! ## The sorted rotation list -/

/-- Lexicographic order for angular dart keys: angle first, head-index tie-breaker. -/
abbrev angularKeyLE {n : Nat} : Real × Fin n -> Real × Fin n -> Prop :=
  Prod.Lex (fun a b : Real => a < b) (fun a b : Fin n => a <= b)

/-- The geometric rotation system at one vertex: outgoing darts in angular order.

The order is lexicographic on `(Complex.arg direction, head index)`, so it is
finite, deterministic, and proof-friendly even when two darts have the same
principal argument.
-/
def rotationSystemAt (G : StraightLineUnitDistanceGraph n)
    (center : Fin n) : List (Real × Fin n) := by
  classical
  exact (outgoingDartKeys G center).sort angularKeyLE

/-- The geometric rotation system for every vertex of the drawing. -/
def rotationSystem (G : StraightLineUnitDistanceGraph n) :
    Fin n -> List (Real × Fin n) :=
  fun center => rotationSystemAt G center

theorem rotationSystemAt_pairwise_le
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    List.Pairwise angularKeyLE (rotationSystemAt G center) := by
  classical
  simp [rotationSystemAt]

theorem rotationSystemAt_nodup
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    (rotationSystemAt G center).Nodup := by
  classical
  simp [rotationSystemAt]

@[simp]
theorem mem_rotationSystemAt_iff
    (G : StraightLineUnitDistanceGraph n) (center : Fin n)
    {theta : Real} {head : Fin n} :
    (theta, head) ∈ rotationSystemAt G center ↔
      G.Adj center head ∧ theta = graphDartArg G center head := by
  classical
  simp [rotationSystemAt, mem_outgoingDartKeys_iff]

theorem rotationSystemAt_pairwise_graphDartArg_lt
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    List.Pairwise
      (fun left right : Real × Fin n =>
        graphDartArg G center left.2 < graphDartArg G center right.2)
      (rotationSystemAt G center) := by
  classical
  apply List.pairwise_iff_get.2
  intro i j hij
  let L := rotationSystemAt G center
  have hle :
      angularKeyLE (L.get i) (L.get j) :=
    (rotationSystemAt_pairwise_le G center).rel_get_of_lt hij
  have hleft_mem : L.get i ∈ rotationSystemAt G center := by
    simp [L]
  have hright_mem : L.get j ∈ rotationSystemAt G center := by
    simp [L]
  have hleft_adj :
      G.Adj center (L.get i).2 :=
    ((mem_rotationSystemAt_iff G center).1 hleft_mem).1
  have hright_adj :
      G.Adj center (L.get j).2 :=
    ((mem_rotationSystemAt_iff G center).1 hright_mem).1
  have hleft_arg :
      (L.get i).1 = graphDartArg G center (L.get i).2 :=
    ((mem_rotationSystemAt_iff G center).1 hleft_mem).2
  have hright_arg :
      (L.get j).1 = graphDartArg G center (L.get j).2 :=
    ((mem_rotationSystemAt_iff G center).1 hright_mem).2
  have hkey_ne : L.get i ≠ L.get j := by
    intro hkey
    have hij_eq : i = j :=
      (rotationSystemAt_nodup G center).get_inj_iff.1 (by simpa [L] using hkey)
    exact (ne_of_lt hij) hij_eq
  dsimp [angularKeyLE] at hle
  rw [Prod.lex_def] at hle
  rcases hle with hlt | heq
  · have hlt' :
        graphDartArg G center (L.get i).2 <
          graphDartArg G center (L.get j).2 := by
      calc
        graphDartArg G center (L.get i).2 = (L.get i).1 := hleft_arg.symm
        _ < (L.get j).1 := by simpa using hlt
        _ = graphDartArg G center (L.get j).2 := hright_arg
    simpa [L] using hlt'
  · rcases heq with ⟨hfst, _hhead_le⟩
    have hfst' : (L.get i).1 = (L.get j).1 := by
      simpa using hfst
    have hhead_ne : (L.get i).2 ≠ (L.get j).2 := by
      intro hhead
      exact hkey_ne (Prod.ext hfst' hhead)
    have harg_eq :
        graphDartArg G center (L.get i).2 =
          graphDartArg G center (L.get j).2 := by
      rw [← hleft_arg, ← hright_arg, hfst']
    exact False.elim
      ((outgoingNeighbor_graphDartArg_ne_of_head_ne
        G hleft_adj hright_adj hhead_ne) harg_eq)

theorem mem_rotationSystemAt_iff_unitDistanceAdj
    (G : StraightLineUnitDistanceGraph n) (center : Fin n)
    {theta : Real} {head : Fin n} :
    (theta, head) ∈ rotationSystemAt G center ↔
      GraphBridge.UnitDistanceAdj G.config center head ∧
        theta = graphDartArg G center head := by
  rw [mem_rotationSystemAt_iff]
  exact and_congr (G.adj_iff_unitDistanceAdj center head) Iff.rfl

@[simp]
theorem length_rotationSystemAt
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    (rotationSystemAt G center).length =
      (outgoingNeighbors G center).card := by
  classical
  simp [rotationSystemAt, outgoingDartKeys]

/-- The same rotation list, with the angular keys erased. -/
def rotationIndexList (G : StraightLineUnitDistanceGraph n)
    (center : Fin n) : List (Fin n) :=
  (rotationSystemAt G center).map Prod.snd

@[simp]
theorem mem_rotationIndexList_iff
    (G : StraightLineUnitDistanceGraph n) (center head : Fin n) :
    head ∈ rotationIndexList G center ↔ G.Adj center head := by
  classical
  constructor
  · intro hmem
    rcases List.mem_map.1 hmem with ⟨key, hkey, hhead⟩
    rcases key with ⟨theta, head'⟩
    dsimp at hhead
    subst head'
    exact ((mem_rotationSystemAt_iff G center).1 hkey).1
  · intro hAdj
    exact List.mem_map.2
      ⟨(graphDartArg G center head, head),
        (mem_rotationSystemAt_iff G center).2 ⟨hAdj, rfl⟩, rfl⟩

theorem mem_rotationIndexList_iff_unitDistanceAdj
    (G : StraightLineUnitDistanceGraph n) (center head : Fin n) :
    head ∈ rotationIndexList G center ↔
      GraphBridge.UnitDistanceAdj G.config center head := by
  rw [mem_rotationIndexList_iff, G.adj_iff_unitDistanceAdj]

@[simp]
theorem length_rotationIndexList
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    (rotationIndexList G center).length =
      (outgoingNeighbors G center).card := by
  simp [rotationIndexList]

/-- The angular head list has no repeated vertex. -/
theorem rotationIndexList_nodup
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    (rotationIndexList G center).Nodup := by
  classical
  unfold rotationIndexList
  refine (rotationSystemAt_nodup G center).map_on ?_
  intro a ha b hb hhead
  rcases a with ⟨theta, ahead⟩
  rcases b with ⟨phi, bhead⟩
  dsimp at hhead
  subst bhead
  have htheta : theta = graphDartArg G center ahead :=
    ((mem_rotationSystemAt_iff G center).1 ha).2
  have hphi : phi = graphDartArg G center ahead :=
    ((mem_rotationSystemAt_iff G center).1 hb).2
  ext <;> simp [htheta, hphi]

theorem rotationIndexList_pairwise_graphDartArg_lt
    (G : StraightLineUnitDistanceGraph n) (center : Fin n) :
    List.Pairwise
      (fun left right : Fin n =>
        graphDartArg G center left < graphDartArg G center right)
      (rotationIndexList G center) := by
  unfold rotationIndexList
  exact
    List.Pairwise.map Prod.snd
      (fun _ _ h => h)
      (rotationSystemAt_pairwise_graphDartArg_lt G center)

/-! ## Bridge to the finite-neighbor rotation API -/

/-- The canonical straight-line unit-distance graph attached to a configuration. -/
abbrev canonicalGeometricGraph (C : _root_.UDConfig n) :
    StraightLineUnitDistanceGraph n :=
  StraightLineUnitDistanceGraph.ofUDConfig C

/-- Reattach the unit-distance dart proof to one head from the sorted geometric
neighbor list. -/
def outgoingDartOfRotationIndex
    (C : _root_.UDConfig n) (center : Fin n)
    (head :
      {head : Fin n //
        head ∈ rotationIndexList (canonicalGeometricGraph C) center}) :
    OutgoingUnitDistanceDart C center :=
  ⟨{ tail := center
     head := head.1
     adj := by
       exact (GraphBridge.unitDistanceSimpleGraph_adj C center head.1).2
         ((mem_rotationIndexList_iff_unitDistanceAdj
            (canonicalGeometricGraph C) center head.1).1 head.2) },
    rfl⟩

/-- The sorted angular outgoing-neighbor list, promoted from heads to outgoing
unit-distance darts. -/
def geometricOutgoingDartList
    (C : _root_.UDConfig n) (center : Fin n) :
    List (OutgoingUnitDistanceDart C center) :=
  ((rotationIndexList (canonicalGeometricGraph C) center).attach).map
    (outgoingDartOfRotationIndex C center)

theorem geometricOutgoingDartList_get_head
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    ((geometricOutgoingDartList C center)[i]'hi).1.head =
      (rotationIndexList (canonicalGeometricGraph C) center)[i]'(by
        simpa [geometricOutgoingDartList] using hi) := by
  simp [geometricOutgoingDartList, outgoingDartOfRotationIndex]

theorem geometricOutgoingDartList_pairwise_graphDartArg_lt
    (C : _root_.UDConfig n) (center : Fin n) :
    List.Pairwise
      (fun left right : OutgoingUnitDistanceDart C center =>
        graphDartArg (canonicalGeometricGraph C) center left.1.head <
          graphDartArg (canonicalGeometricGraph C) center right.1.head)
      (geometricOutgoingDartList C center) := by
  classical
  apply List.pairwise_iff_get.2
  intro i j hij
  let L := geometricOutgoingDartList C center
  let R := rotationIndexList (canonicalGeometricGraph C) center
  have hilen : i.1 < R.length := by
    simpa [L, R, geometricOutgoingDartList] using i.2
  have hjlen : j.1 < R.length := by
    simpa [L, R, geometricOutgoingDartList] using j.2
  let iR : Fin R.length := ⟨i.1, hilen⟩
  let jR : Fin R.length := ⟨j.1, hjlen⟩
  have hijR : iR < jR := by
    simpa [iR, jR] using hij
  have hrot :
      graphDartArg (canonicalGeometricGraph C) center (R.get iR) <
        graphDartArg (canonicalGeometricGraph C) center (R.get jR) :=
    (rotationIndexList_pairwise_graphDartArg_lt
      (canonicalGeometricGraph C) center).rel_get_of_lt hijR
  simpa [L, R, iR, jR, geometricOutgoingDartList_get_head] using hrot

theorem mem_geometricOutgoingDartList
    (C : _root_.UDConfig n) (center : Fin n)
    (d : OutgoingUnitDistanceDart C center) :
    d ∈ geometricOutgoingDartList C center := by
  classical
  rw [geometricOutgoingDartList]
  let head :
      {head : Fin n //
        head ∈ rotationIndexList (canonicalGeometricGraph C) center} :=
    ⟨d.1.head, by
      rw [mem_rotationIndexList_iff_unitDistanceAdj]
      exact (GraphBridge.unitDistanceSimpleGraph_adj C center d.1.head).1
        (by simpa [d.2] using d.1.adj)⟩
  exact List.mem_map.2
    ⟨head,
      by simp [head],
      by
        apply Subtype.ext
        apply UnitDistanceDart.endpointPair_injective
        simp [outgoingDartOfRotationIndex, UnitDistanceDart.endpointPair, d.2, head]⟩

/-- The geometric outgoing dart list has no duplicate darts. -/
theorem geometricOutgoingDartList_nodup
    (C : _root_.UDConfig n) (center : Fin n) :
    (geometricOutgoingDartList C center).Nodup := by
  classical
  unfold geometricOutgoingDartList
  refine
    (List.Nodup.attach
      (rotationIndexList_nodup (canonicalGeometricGraph C) center)).map_on ?_
  intro a _ha b _hb hab
  apply Subtype.ext
  have hhead :
      (outgoingDartOfRotationIndex C center a).1.head =
        (outgoingDartOfRotationIndex C center b).1.head := by
    exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) hab
  exact hhead

theorem _root_.List.formPerm_apply_getElem_length_sub_one {α : Type*}
    [DecidableEq α]
    (xs : List α) (hxs : 0 < xs.length) :
    xs.formPerm xs[xs.length - 1] = xs[0] := by
  cases xs with
  | nil => simp at hxs
  | cons x xs =>
      simp

theorem _root_.List.formPerm_symm_apply_getElem_zero {α : Type*}
    [DecidableEq α]
    (xs : List α) (hxs : 0 < xs.length) :
    xs.formPerm.symm xs[0] = xs[xs.length - 1] := by
  rw [Equiv.symm_apply_eq]
  exact (List.formPerm_apply_getElem_length_sub_one xs hxs).symm

theorem _root_.List.formPerm_symm_apply_getElem_succ {α : Type*}
    [DecidableEq α]
    (xs : List α) (hxs : xs.Nodup)
    (i : Nat) (hi : i + 1 < xs.length) :
    xs.formPerm.symm xs[i + 1] = xs[i] := by
  rw [Equiv.symm_apply_eq]
  exact (List.formPerm_apply_lt_getElem xs hxs i hi).symm

/-- The geometric cyclic order at one vertex, obtained by cycling through the
sorted angular outgoing-neighbor list. -/
def geometricVertexCyclicOrder
    (C : _root_.UDConfig n) (center : Fin n) :
    VertexFiniteUnitNeighborCyclicOrder C center where
  perm := by
    classical
    exact (geometricOutgoingDartList C center).formPerm

/-- The unit-distance rotation system whose local rows are the geometric sorted
angular orders. -/
def geometricUnitDistanceRotationSystem
    (C : _root_.UDConfig n) :
    UnitDistanceRotationSystem C :=
  UnitDistanceRotationSystem.ofFiniteUnitNeighborCyclicOrderRows
    (geometricVertexCyclicOrder C)

@[simp]
theorem geometricUnitDistanceRotationSystem_rotationAt
    (C : _root_.UDConfig n) (center : Fin n) :
    (geometricUnitDistanceRotationSystem C).rotationAt center =
      (geometricVertexCyclicOrder C center).toVertexCyclicAngularSuccessor :=
  rfl

/-- The geometric cyclic order advances from a listed outgoing dart to the
next listed outgoing dart, wrapping cyclically. -/
theorem geometricVertexCyclicOrder_perm_getElem
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    (geometricVertexCyclicOrder C center).perm
        ((geometricOutgoingDartList C center)[i]) =
      let L := geometricOutgoingDartList C center
      L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero (by
        intro hlen
        rw [hlen] at hi
        exact Nat.not_lt_zero _ hi))) := by
  classical
  simpa [geometricVertexCyclicOrder] using
    List.formPerm_apply_getElem
      (xs := geometricOutgoingDartList C center)
      (w := geometricOutgoingDartList_nodup C center)
      (i := i) (h := hi)

/-- Away from the wrap-around point, the geometric cyclic order advances to
the next entry of the concrete angular outgoing-dart list. -/
theorem geometricVertexCyclicOrder_perm_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i + 1 < (geometricOutgoingDartList C center).length) :
    (geometricVertexCyclicOrder C center).perm
        ((geometricOutgoingDartList C center)[i]) =
      (geometricOutgoingDartList C center)[i + 1] := by
  classical
  simpa [geometricVertexCyclicOrder] using
    List.formPerm_apply_lt_getElem
      (xs := geometricOutgoingDartList C center)
      (h := geometricOutgoingDartList_nodup C center)
      (n := i) (hn := hi)

/-- At the wrap-around point, the geometric cyclic order advances from the
last listed outgoing dart to the first. -/
theorem geometricVertexCyclicOrder_perm_getElem_last
    (C : _root_.UDConfig n) (center : Fin n)
    (hpos : 0 < (geometricOutgoingDartList C center).length) :
    (geometricVertexCyclicOrder C center).perm
        ((geometricOutgoingDartList C center)[
          (geometricOutgoingDartList C center).length - 1]) =
      (geometricOutgoingDartList C center)[0] := by
  classical
  simpa [geometricVertexCyclicOrder] using
    List.formPerm_apply_getElem_length_sub_one
      (xs := geometricOutgoingDartList C center) hpos

/-- The predecessor of the first listed outgoing dart is the last listed
outgoing dart. -/
theorem geometricVertexCyclicOrder_perm_symm_getElem_zero
    (C : _root_.UDConfig n) (center : Fin n)
    (hpos : 0 < (geometricOutgoingDartList C center).length) :
    (geometricVertexCyclicOrder C center).perm.symm
        ((geometricOutgoingDartList C center)[0]) =
      (geometricOutgoingDartList C center)[
        (geometricOutgoingDartList C center).length - 1] := by
  classical
  simpa [geometricVertexCyclicOrder] using
    List.formPerm_symm_apply_getElem_zero
      (xs := geometricOutgoingDartList C center) hpos

/-- Away from the first entry, the predecessor in the geometric cyclic order is
the previous entry of the concrete angular outgoing-dart list. -/
theorem geometricVertexCyclicOrder_perm_symm_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i + 1 < (geometricOutgoingDartList C center).length) :
    (geometricVertexCyclicOrder C center).perm.symm
        ((geometricOutgoingDartList C center)[i + 1]) =
      (geometricOutgoingDartList C center)[i] := by
  classical
  simpa [geometricVertexCyclicOrder] using
    List.formPerm_symm_apply_getElem_succ
      (xs := geometricOutgoingDartList C center)
      (hxs := geometricOutgoingDartList_nodup C center)
      (i := i) (hi := hi)

/-- The geometric rotation system's local successor agrees with the next entry
of the concrete angular outgoing-dart list away from wrap-around. -/
theorem geometricUnitDistanceRotationSystem_next_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i + 1 < (geometricOutgoingDartList C center).length) :
    ((geometricUnitDistanceRotationSystem C).rotationAt center).next
        ((geometricOutgoingDartList C center)[i]) =
      (geometricOutgoingDartList C center)[i + 1] := by
  rw [geometricUnitDistanceRotationSystem_rotationAt]
  simpa using
    geometricVertexCyclicOrder_perm_getElem_succ C center i hi

/-- The geometric rotation system's local successor wraps from the last entry
of the concrete angular outgoing-dart list to the first. -/
theorem geometricUnitDistanceRotationSystem_next_getElem_last
    (C : _root_.UDConfig n) (center : Fin n)
    (hpos : 0 < (geometricOutgoingDartList C center).length) :
    ((geometricUnitDistanceRotationSystem C).rotationAt center).next
        ((geometricOutgoingDartList C center)[
          (geometricOutgoingDartList C center).length - 1]) =
      (geometricOutgoingDartList C center)[0] := by
  rw [geometricUnitDistanceRotationSystem_rotationAt]
  simpa using
    geometricVertexCyclicOrder_perm_getElem_last C center hpos

/-- The geometric rotation system's local predecessor wraps from the first
entry of the concrete angular outgoing-dart list to the last. -/
theorem geometricUnitDistanceRotationSystem_prev_getElem_zero
    (C : _root_.UDConfig n) (center : Fin n)
    (hpos : 0 < (geometricOutgoingDartList C center).length) :
    ((geometricUnitDistanceRotationSystem C).rotationAt center).prev
        ((geometricOutgoingDartList C center)[0]) =
      (geometricOutgoingDartList C center)[
        (geometricOutgoingDartList C center).length - 1] := by
  rw [geometricUnitDistanceRotationSystem_rotationAt]
  simpa using
    geometricVertexCyclicOrder_perm_symm_getElem_zero C center hpos

/-- The geometric rotation system's local predecessor agrees with the previous
entry of the concrete angular outgoing-dart list away from the first entry. -/
theorem geometricUnitDistanceRotationSystem_prev_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i + 1 < (geometricOutgoingDartList C center).length) :
    ((geometricUnitDistanceRotationSystem C).rotationAt center).prev
        ((geometricOutgoingDartList C center)[i + 1]) =
      (geometricOutgoingDartList C center)[i] := by
  rw [geometricUnitDistanceRotationSystem_rotationAt]
  simpa using
    geometricVertexCyclicOrder_perm_symm_getElem_succ C center i hi

/-! ## Face successor helpers for concrete geometric lists -/

theorem geometricOutgoingDartList_get_tail
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    ((geometricOutgoingDartList C center)[i]'hi).1.tail = center :=
  ((geometricOutgoingDartList C center)[i]'hi).2

theorem geometricOutgoingDartList_get_head_adj
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    (GraphBridge.unitDistanceSimpleGraph C).Adj center
      ((geometricOutgoingDartList C center)[i]'hi).1.head := by
  simpa [geometricOutgoingDartList_get_tail C center i hi] using
    ((geometricOutgoingDartList C center)[i]'hi).1.adj

/-- Build a concrete dart from the head of an indexed outgoing dart in the
geometric rotation list. -/
def dartFromGeometricList
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    UnitDistanceDart C where
  tail := center
  head := ((geometricOutgoingDartList C center)[i]'hi).1.head
  adj := geometricOutgoingDartList_get_head_adj C center i hi

@[simp]
theorem dartFromGeometricList_tail
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    (dartFromGeometricList C center i hi).tail = center :=
  rfl

@[simp]
theorem dartFromGeometricList_head
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    (dartFromGeometricList C center i hi).head =
      ((geometricOutgoingDartList C center)[i]'hi).1.head :=
  rfl

theorem dartFromGeometricList_outgoing
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i < (geometricOutgoingDartList C center).length) :
    (dartFromGeometricList C center i hi).outgoing =
      (geometricOutgoingDartList C center)[i]'hi := by
  apply Subtype.ext
  change dartFromGeometricList C center i hi =
    ((geometricOutgoingDartList C center)[i]'hi).1
  apply UnitDistanceDart.endpointPair_injective
  apply Prod.ext
  · simp [UnitDistanceDart.endpointPair, dartFromGeometricList,
      geometricOutgoingDartList_get_tail C center i hi]
  · simp [UnitDistanceDart.endpointPair, dartFromGeometricList]

/-- Earlier entries in the sorted geometric outgoing-dart list have strictly
smaller graph-dart argument than later entries. -/
theorem graphDartArg_lt_of_dartFromGeometricList_index_lt
    (C : _root_.UDConfig n) (center : Fin n)
    {i j : Nat}
    (hi : i < (geometricOutgoingDartList C center).length)
    (hj : j < (geometricOutgoingDartList C center).length)
    (hij : i < j) :
    graphDartArg (canonicalGeometricGraph C) center
        (dartFromGeometricList C center i hi).head <
      graphDartArg (canonicalGeometricGraph C) center
        (dartFromGeometricList C center j hj).head := by
  have hrel :=
    (geometricOutgoingDartList_pairwise_graphDartArg_lt C center).rel_get_of_lt
      (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hij)
  simpa [dartFromGeometricList_head] using hrel

/-- Away from wrap-around, `nextAround` on a dart represented by the geometric
list advances to the next list entry. -/
theorem geometricUnitDistanceRotationSystem_nextAround_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i + 1 < (geometricOutgoingDartList C center).length) :
    (geometricUnitDistanceRotationSystem C).nextAround
        (dartFromGeometricList C center i (Nat.lt_trans (Nat.lt_succ_self i) hi)) =
      dartFromGeometricList C center (i + 1) hi := by
  apply UnitDistanceDart.endpointPair_injective
  have hnext :=
    geometricUnitDistanceRotationSystem_next_getElem_succ C center i hi
  have htail :
      ((geometricUnitDistanceRotationSystem C).nextAround
        (dartFromGeometricList C center i (Nat.lt_trans (Nat.lt_succ_self i) hi))).tail =
        center := by
    simp
  have hhead :
      ((geometricUnitDistanceRotationSystem C).nextAround
        (dartFromGeometricList C center i (Nat.lt_trans (Nat.lt_succ_self i) hi))).head =
        ((geometricOutgoingDartList C center)[i + 1]'hi).1.head := by
    have hout :
        ((geometricUnitDistanceRotationSystem C).rotationAt
              (dartFromGeometricList C center i
                (Nat.lt_trans (Nat.lt_succ_self i) hi)).tail).next
            (dartFromGeometricList C center i
              (Nat.lt_trans (Nat.lt_succ_self i) hi)).outgoing =
          (geometricOutgoingDartList C center)[i + 1]'hi := by
      simpa [dartFromGeometricList_outgoing] using hnext
    exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) hout
  simp [UnitDistanceDart.endpointPair, hhead]

/-- At wrap-around, `nextAround` on a dart represented by the last geometric
list entry advances to the first entry. -/
theorem geometricUnitDistanceRotationSystem_nextAround_getElem_last
    (C : _root_.UDConfig n) (center : Fin n)
    (hpos : 0 < (geometricOutgoingDartList C center).length) :
    (geometricUnitDistanceRotationSystem C).nextAround
        (dartFromGeometricList C center
          ((geometricOutgoingDartList C center).length - 1)
          (Nat.sub_lt hpos Nat.zero_lt_one)) =
      dartFromGeometricList C center 0 hpos := by
  apply UnitDistanceDart.endpointPair_injective
  have hnext :=
    geometricUnitDistanceRotationSystem_next_getElem_last C center hpos
  have htail :
      ((geometricUnitDistanceRotationSystem C).nextAround
        (dartFromGeometricList C center
          ((geometricOutgoingDartList C center).length - 1)
          (Nat.sub_lt hpos Nat.zero_lt_one))).tail =
        center := by
    simp
  have hhead :
      ((geometricUnitDistanceRotationSystem C).nextAround
        (dartFromGeometricList C center
          ((geometricOutgoingDartList C center).length - 1)
          (Nat.sub_lt hpos Nat.zero_lt_one))).head =
        ((geometricOutgoingDartList C center)[0]'hpos).1.head := by
    have hout :
        ((geometricUnitDistanceRotationSystem C).rotationAt
              (dartFromGeometricList C center
                ((geometricOutgoingDartList C center).length - 1)
                (Nat.sub_lt hpos Nat.zero_lt_one)).tail).next
            (dartFromGeometricList C center
              ((geometricOutgoingDartList C center).length - 1)
              (Nat.sub_lt hpos Nat.zero_lt_one)).outgoing =
          (geometricOutgoingDartList C center)[0]'hpos := by
      simpa [dartFromGeometricList_outgoing] using hnext
    exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) hout
  simp [UnitDistanceDart.endpointPair, hhead]

theorem geometricOutgoingDartList_getElem_eq_of_mem
    (C : _root_.UDConfig n) (center : Fin n)
    (d : OutgoingUnitDistanceDart C center)
    (hmem : d ∈ geometricOutgoingDartList C center) :
    Exists fun i : Nat =>
      Exists fun hi : i < (geometricOutgoingDartList C center).length =>
        (geometricOutgoingDartList C center)[i]'hi = d := by
  exact List.mem_iff_getElem.1 hmem

theorem exists_geometricOutgoingDartList_getElem_eq
    (C : _root_.UDConfig n) (center : Fin n)
    (d : OutgoingUnitDistanceDart C center) :
    Exists fun i : Nat =>
      Exists fun hi : i < (geometricOutgoingDartList C center).length =>
        (geometricOutgoingDartList C center)[i]'hi = d :=
  geometricOutgoingDartList_getElem_eq_of_mem C center d
    (mem_geometricOutgoingDartList C center d)

theorem exists_dartFromGeometricList_eq_of_outgoing
    (C : _root_.UDConfig n) (center : Fin n)
    (d : OutgoingUnitDistanceDart C center) :
    Exists fun i : Nat =>
      Exists fun hi : i < (geometricOutgoingDartList C center).length =>
        dartFromGeometricList C center i hi = d.1 := by
  rcases exists_geometricOutgoingDartList_getElem_eq C center d with
    ⟨i, hi, hget⟩
  refine ⟨i, hi, ?_⟩
  have hout : (dartFromGeometricList C center i hi).outgoing = d := by
    simpa [hget] using dartFromGeometricList_outgoing C center i hi
  exact congrArg Subtype.val hout

theorem exists_dartFromGeometricList_eq_of_tail
    (C : _root_.UDConfig n) (center : Fin n)
    (d : UnitDistanceDart C) (htail : d.tail = center) :
    Exists fun i : Nat =>
      Exists fun hi : i < (geometricOutgoingDartList C center).length =>
        dartFromGeometricList C center i hi = d := by
  let outgoing : OutgoingUnitDistanceDart C center := ⟨d, htail⟩
  rcases exists_dartFromGeometricList_eq_of_outgoing C center outgoing with
    ⟨i, hi, hget⟩
  exact ⟨i, hi, hget⟩

theorem exists_dartFromGeometricList_eq_reverse
    (C : _root_.UDConfig n) (d : UnitDistanceDart C) :
    Exists fun i : Nat =>
      Exists fun hi : i < (geometricOutgoingDartList C d.head).length =>
        dartFromGeometricList C d.head i hi = d.reverse := by
  exact exists_dartFromGeometricList_eq_of_tail C d.head d.reverse (by simp)

def geometricOutgoingDartListConsecutive
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C) : Prop :=
  (Exists fun i : Nat =>
    Exists fun hi : i + 1 < (geometricOutgoingDartList C center).length =>
      first =
        dartFromGeometricList C center i
          (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
      second = dartFromGeometricList C center (i + 1) hi) \/
  Exists fun hpos : 0 < (geometricOutgoingDartList C center).length =>
    first =
      dartFromGeometricList C center
        ((geometricOutgoingDartList C center).length - 1)
        (Nat.sub_lt hpos Nat.zero_lt_one) /\
    second = dartFromGeometricList C center 0 hpos

set_option linter.style.longLine false in
/-- A consecutive pair in the genuine sorted outgoing-dart list is in the
ordinary non-wrap branch whenever the first dart has smaller principal
`graphDartArg` than the second. -/
theorem geometricOutgoingDartListConsecutive_nonwrap_of_graphDartArg_lt
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (hconsecutive :
      geometricOutgoingDartListConsecutive C center first second)
    (hangle :
      graphDartArg (canonicalGeometricGraph C) center first.head <
        graphDartArg (canonicalGeometricGraph C) center second.head) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C center).length =>
        first =
          dartFromGeometricList C center i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
        second = dartFromGeometricList C center (i + 1) hi := by
  classical
  rcases hconsecutive with hnonwrap | hwrap
  · exact hnonwrap
  · exfalso
    rcases hwrap with ⟨hpos, hfirst, hsecond⟩
    let L := geometricOutgoingDartList C center
    have hlen_ne_one : L.length ≠ 1 := by
      intro hlen_one
      have hlast_zero : L.length - 1 = 0 := by omega
      have hsame_head : first.head = second.head := by
        rw [hfirst, hsecond]
        simp [L, hlast_zero]
      rw [← hsame_head] at hangle
      exact (lt_irrefl _ hangle)
    have hzero_lt_last : 0 < L.length - 1 := by
      have hposL : 0 < L.length := by simpa [L] using hpos
      omega
    have hlast_lt : L.length - 1 < L.length := by
      have hposL : 0 < L.length := by simpa [L] using hpos
      omega
    have hwrap_angle :
        graphDartArg (canonicalGeometricGraph C) center second.head <
          graphDartArg (canonicalGeometricGraph C) center first.head := by
      have hrel :=
        (geometricOutgoingDartList_pairwise_graphDartArg_lt C center).rel_get_of_lt
          (a := ⟨0, by simpa [L] using hpos⟩)
          (b := ⟨L.length - 1, hlast_lt⟩)
          hzero_lt_last
      simpa [L, hfirst, hsecond, dartFromGeometricList_head] using hrel
    exact (lt_asymm hangle hwrap_angle)

theorem geometricOutgoingDartListConsecutive_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (i : Nat) (hi : i + 1 < (geometricOutgoingDartList C center).length) :
    geometricOutgoingDartListConsecutive C center
      (dartFromGeometricList C center i
        (Nat.lt_trans (Nat.lt_succ_self i) hi))
      (dartFromGeometricList C center (i + 1) hi) := by
  left
  exact ⟨i, hi, rfl, rfl⟩

theorem _root_.List.exists_getElem_succ_or_last_zero_of_formPerm_eq
    {α : Type*} [DecidableEq α] {xs : List α} {first second : α}
    (hnodup : xs.Nodup)
    (hfirst : first ∈ xs)
    (hperm : xs.formPerm first = second) :
    (Exists fun i : Nat =>
      Exists fun hi : i + 1 < xs.length =>
        xs[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi) = first ∧
          xs[i + 1]'hi = second) ∨
    Exists fun hpos : 0 < xs.length =>
      xs[xs.length - 1]'(Nat.sub_lt hpos Nat.zero_lt_one) = first ∧
        xs[0]'hpos = second := by
  rcases List.mem_iff_getElem.1 hfirst with ⟨i, hi, hget_first⟩
  have hnext :
      xs.formPerm (xs[i]'hi) =
        let j := (i + 1) % xs.length
        xs[j]'(Nat.mod_lt _ (Nat.pos_of_ne_zero (by
          intro hlen
          rw [hlen] at hi
          exact Nat.not_lt_zero _ hi))) := by
    exact List.formPerm_apply_getElem xs hnodup i hi
  have hperm_get : xs.formPerm (xs[i]'hi) = second := by
    simpa [hget_first] using hperm
  by_cases hsucc : i + 1 < xs.length
  · left
    refine ⟨i, hsucc, hget_first, ?_⟩
    have hmod : (i + 1) % xs.length = i + 1 :=
      Nat.mod_eq_of_lt hsucc
    have hnext' : xs.formPerm (xs[i]'hi) = xs[i + 1]'hsucc := by
      simpa [hmod] using hnext
    exact hnext'.symm.trans hperm_get
  · right
    have hlast_succ : i + 1 = xs.length :=
      eq_of_le_of_not_lt (Nat.succ_le_of_lt hi) hsucc
    have hi_last : i = xs.length - 1 := by omega
    have hpos : 0 < xs.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    refine ⟨hpos, ?_, ?_⟩
    · simpa [hi_last] using hget_first
    · have hmod_zero : (i + 1) % xs.length = 0 := by
        rw [hlast_succ, Nat.mod_self]
      have hnext' : xs.formPerm (xs[i]'hi) = xs[0]'hpos := by
        simpa [hmod_zero] using hnext
      exact hnext'.symm.trans hperm_get

theorem _root_.List.exists_getElem_succ_eq_of_pairwise_real_lt_no_between
    {α : Type*} {weight : α -> Real} {xs : List α} {first second : α}
    (hsorted : xs.Pairwise (fun left right => weight left < weight right))
    (hfirst : first ∈ xs) (hsecond : second ∈ xs)
    (hangle : weight first < weight second)
    (hno_between :
      ∀ other ∈ xs, other ≠ first -> other ≠ second ->
        ¬ (weight first < weight other ∧ weight other < weight second)) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < xs.length =>
        xs[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi) = first ∧
          xs[i + 1]'hi = second := by
  rcases List.mem_iff_getElem.1 hfirst with ⟨i, hi, hget_first⟩
  rcases List.mem_iff_getElem.1 hsecond with ⟨j, hj, hget_second⟩
  have hij : i < j := by
    rcases lt_trichotomy i j with hij | hij_eq | hji
    · exact hij
    · subst j
      rw [← hget_first, ← hget_second] at hangle
      linarith
    · have hback :
          weight xs[j] < weight xs[i] :=
        hsorted.rel_get_of_lt
          (a := ⟨j, hj⟩) (b := ⟨i, hi⟩) (by simpa using hji)
      rw [hget_first, hget_second] at hback
      linarith
  have hle_succ : j ≤ i + 1 := by
    by_contra hnot
    have hi_succ_lt_j : i + 1 < j := Nat.lt_of_not_ge hnot
    have hi_succ_len : i + 1 < xs.length := Nat.lt_trans hi_succ_lt_j hj
    let other := xs[i + 1]'hi_succ_len
    have hfirst_other :
        weight first < weight other := by
      have hrel :
          weight xs[i] < weight xs[i + 1] :=
        hsorted.rel_get_of_lt
          (a := ⟨i, hi⟩) (b := ⟨i + 1, hi_succ_len⟩)
          (by simp)
      simpa [other, hget_first] using hrel
    have hother_second :
        weight other < weight second := by
      have hrel :
          weight xs[i + 1] < weight xs[j] :=
        hsorted.rel_get_of_lt
          (a := ⟨i + 1, hi_succ_len⟩) (b := ⟨j, hj⟩)
          (by simpa using hi_succ_lt_j)
      simpa [other, hget_second] using hrel
    have hother_ne_first : other ≠ first := by
      intro hother
      rw [hother] at hfirst_other
      linarith
    have hother_ne_second : other ≠ second := by
      intro hother
      rw [hother] at hother_second
      linarith
    exact
      (hno_between other (List.getElem_mem hi_succ_len)
        hother_ne_first hother_ne_second)
        ⟨hfirst_other, hother_second⟩
  have hsucc : j = i + 1 :=
    Nat.le_antisymm hle_succ (Nat.succ_le_of_lt hij)
  subst j
  exact ⟨i, hj, hget_first, hget_second⟩

/-- Wrap-around version of
`List.exists_getElem_succ_eq_of_pairwise_real_lt_no_between`: if `second`
appears before `first` in the real-weight order, and no element lies in the
cyclic interval `(first, +∞) ∪ (-∞, second)`, then `first` is the last entry
and `second` is the first entry. -/
theorem _root_.List.exists_getElem_last_zero_eq_of_pairwise_real_lt_no_between_wrap
    {α : Type*} {weight : α -> Real} {xs : List α} {first second : α}
    (hsorted : xs.Pairwise (fun left right => weight left < weight right))
    (hfirst : first ∈ xs) (hsecond : second ∈ xs)
    (hangle : weight second < weight first)
    (hno_between :
      ∀ other ∈ xs, other ≠ first -> other ≠ second ->
        ¬ (weight first < weight other ∨ weight other < weight second)) :
    Exists fun hpos : 0 < xs.length =>
      xs[xs.length - 1]'(Nat.sub_lt hpos Nat.zero_lt_one) = first ∧
        xs[0]'hpos = second := by
  rcases List.mem_iff_getElem.1 hfirst with ⟨i, hi, hget_first⟩
  rcases List.mem_iff_getElem.1 hsecond with ⟨j, hj, hget_second⟩
  have hji : j < i := by
    rcases lt_trichotomy j i with hji | hji_eq | hij
    · exact hji
    · subst i
      rw [← hget_first, ← hget_second] at hangle
      linarith
    · have hforward :
          weight xs[i] < weight xs[j] :=
        hsorted.rel_get_of_lt
          (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hij)
      rw [hget_first, hget_second] at hforward
      linarith
  have hno_after : ¬ i + 1 < xs.length := by
    intro hi_succ_len
    let other := xs[i + 1]'hi_succ_len
    have hfirst_other :
        weight first < weight other := by
      have hrel :
          weight xs[i] < weight xs[i + 1] :=
        hsorted.rel_get_of_lt
          (a := ⟨i, hi⟩) (b := ⟨i + 1, hi_succ_len⟩)
          (by simp)
      simpa [other, hget_first] using hrel
    have hother_ne_first : other ≠ first := by
      intro hother
      rw [hother] at hfirst_other
      linarith
    have hother_ne_second : other ≠ second := by
      intro hother
      rw [hother] at hfirst_other
      linarith
    exact
      (hno_between other (List.getElem_mem hi_succ_len)
        hother_ne_first hother_ne_second)
        (Or.inl hfirst_other)
  have hi_last : i = xs.length - 1 := by
    omega
  have hnot_pos_j : ¬ 0 < j := by
    intro hpos_j
    have hzero_len : 0 < xs.length := Nat.lt_trans hpos_j hj
    let other := xs[0]'hzero_len
    have hother_second :
        weight other < weight second := by
      have hrel :
          weight xs[0] < weight xs[j] :=
        hsorted.rel_get_of_lt
          (a := ⟨0, hzero_len⟩) (b := ⟨j, hj⟩) hpos_j
      simpa [other, hget_second] using hrel
    have hother_ne_first : other ≠ first := by
      intro hother
      rw [hother] at hother_second
      linarith
    have hother_ne_second : other ≠ second := by
      intro hother
      rw [hother] at hother_second
      linarith
    exact
      (hno_between other (List.getElem_mem hzero_len)
        hother_ne_first hother_ne_second)
        (Or.inr hother_second)
  have hj_zero : j = 0 := Nat.eq_zero_of_not_pos hnot_pos_j
  have hpos : 0 < xs.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  exact ⟨hpos, by simpa [hi_last] using hget_first,
    by simpa [hj_zero] using hget_second⟩

theorem _root_.List.no_between_of_getElem_succ_pairwise_real_lt
    {α : Type*} {weight : α -> Real} {xs : List α} {first second : α}
    (hsorted : xs.Pairwise (fun left right => weight left < weight right))
    (i : Nat) (hi : i + 1 < xs.length)
    (hfirst :
      xs[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi) = first)
    (hsecond : xs[i + 1]'hi = second) :
    ∀ other ∈ xs, other ≠ first -> other ≠ second ->
      ¬ (weight first < weight other ∧ weight other < weight second) := by
  intro other hmem hother_ne_first hother_ne_second hbetween
  rcases List.mem_iff_getElem.1 hmem with ⟨j, hj, hget⟩
  have hi_lt : i < xs.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  rcases lt_trichotomy j i with hji | hji | hij
  · have hother_first : weight other < weight first := by
      have hrel :
          weight xs[j] < weight xs[i] :=
        hsorted.rel_get_of_lt
          (a := ⟨j, hj⟩) (b := ⟨i, hi_lt⟩) hji
      simpa [hget, hfirst] using hrel
    linarith
  · subst j
    have hother_first : other = first := by
      simpa [hfirst] using hget.symm
    exact hother_ne_first hother_first
  · rcases lt_or_eq_of_le (Nat.succ_le_of_lt hij) with hi_succ_lt_j | hi_succ_eq_j
    · have hsecond_other : weight second < weight other := by
        have hrel :
            weight xs[i + 1] < weight xs[j] :=
          hsorted.rel_get_of_lt
            (a := ⟨i + 1, hi⟩) (b := ⟨j, hj⟩) hi_succ_lt_j
        simpa [hget, hsecond] using hrel
      linarith
    · have hj_eq : j = i + 1 := hi_succ_eq_j.symm
      subst j
      have hother_second : other = second := by
        simpa [hsecond] using hget.symm
      exact hother_ne_second hother_second

theorem geometricOutgoingDartListConsecutive_of_no_graphDartArg_between
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (hfirst_tail : first.tail = center)
    (hsecond_tail : second.tail = center)
    (hangle :
      graphDartArg (canonicalGeometricGraph C) center first.head <
        graphDartArg (canonicalGeometricGraph C) center second.head)
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C center other ->
        other ≠ first.head -> other ≠ second.head ->
          ¬ (graphDartArg (canonicalGeometricGraph C) center first.head <
                graphDartArg (canonicalGeometricGraph C) center other ∧
              graphDartArg (canonicalGeometricGraph C) center other <
                graphDartArg (canonicalGeometricGraph C) center second.head)) :
    geometricOutgoingDartListConsecutive C center first second := by
  classical
  let firstOutgoing : OutgoingUnitDistanceDart C center := ⟨first, hfirst_tail⟩
  let secondOutgoing : OutgoingUnitDistanceDart C center := ⟨second, hsecond_tail⟩
  have hfirst_mem :
      firstOutgoing ∈ geometricOutgoingDartList C center :=
    mem_geometricOutgoingDartList C center firstOutgoing
  have hsecond_mem :
      secondOutgoing ∈ geometricOutgoingDartList C center :=
    mem_geometricOutgoingDartList C center secondOutgoing
  have hno_list :
      ∀ other ∈ geometricOutgoingDartList C center,
        other ≠ firstOutgoing -> other ≠ secondOutgoing ->
          ¬ (graphDartArg (canonicalGeometricGraph C) center firstOutgoing.1.head <
                graphDartArg (canonicalGeometricGraph C) center other.1.head ∧
              graphDartArg (canonicalGeometricGraph C) center other.1.head <
                graphDartArg (canonicalGeometricGraph C) center secondOutgoing.1.head) := by
    intro other _hmem hother_ne_first hother_ne_second
    have hother_adj :
        GraphBridge.UnitDistanceAdj C center other.1.head := by
      exact (GraphBridge.unitDistanceSimpleGraph_adj C center other.1.head).1
        (by simpa [other.2] using other.1.adj)
    have hother_head_ne_first : other.1.head ≠ first.head := by
      intro hhead
      apply hother_ne_first
      apply Subtype.ext
      apply UnitDistanceDart.endpointPair_injective
      simp [UnitDistanceDart.endpointPair, firstOutgoing, other.2,
        hfirst_tail, hhead]
    have hother_head_ne_second : other.1.head ≠ second.head := by
      intro hhead
      apply hother_ne_second
      apply Subtype.ext
      apply UnitDistanceDart.endpointPair_injective
      simp [UnitDistanceDart.endpointPair, secondOutgoing, other.2,
        hsecond_tail, hhead]
    simpa [firstOutgoing, secondOutgoing] using
      hno_between other.1.head hother_adj
        hother_head_ne_first hother_head_ne_second
  rcases
    List.exists_getElem_succ_eq_of_pairwise_real_lt_no_between
      (xs := geometricOutgoingDartList C center)
      (weight := fun outgoing : OutgoingUnitDistanceDart C center =>
        graphDartArg (canonicalGeometricGraph C) center outgoing.1.head)
      (hsorted := geometricOutgoingDartList_pairwise_graphDartArg_lt C center)
      hfirst_mem hsecond_mem (by simpa [firstOutgoing, secondOutgoing] using hangle)
      hno_list with
    ⟨i, hi, hget_first, hget_second⟩
  left
  refine ⟨i, hi, ?_, ?_⟩
  · have hout :
        (dartFromGeometricList C center i
          (Nat.lt_trans (Nat.lt_succ_self i) hi)).outgoing = firstOutgoing := by
      simpa [hget_first] using
        dartFromGeometricList_outgoing C center i
          (Nat.lt_trans (Nat.lt_succ_self i) hi)
    exact (congrArg Subtype.val hout).symm
  · have hout :
        (dartFromGeometricList C center (i + 1) hi).outgoing = secondOutgoing := by
      simpa [hget_second] using
        dartFromGeometricList_outgoing C center (i + 1) hi
    exact (congrArg Subtype.val hout).symm

/-- Wrap-around angular exclusion for the concrete geometric outgoing list.  If
`second` has smaller principal argument than `first`, and no incident neighbour
lies in the cyclic branch interval `(first, +∞) ∪ (-∞, second)`, then `first`
is the last outgoing dart and `second` is the first outgoing dart. -/
theorem geometricOutgoingDartListConsecutive_of_no_graphDartArg_between_wrap
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (hfirst_tail : first.tail = center)
    (hsecond_tail : second.tail = center)
    (hangle :
      graphDartArg (canonicalGeometricGraph C) center second.head <
        graphDartArg (canonicalGeometricGraph C) center first.head)
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C center other ->
        other ≠ first.head -> other ≠ second.head ->
          ¬ (graphDartArg (canonicalGeometricGraph C) center first.head <
                graphDartArg (canonicalGeometricGraph C) center other ∨
              graphDartArg (canonicalGeometricGraph C) center other <
                graphDartArg (canonicalGeometricGraph C) center second.head)) :
    geometricOutgoingDartListConsecutive C center first second := by
  classical
  let firstOutgoing : OutgoingUnitDistanceDart C center := ⟨first, hfirst_tail⟩
  let secondOutgoing : OutgoingUnitDistanceDart C center := ⟨second, hsecond_tail⟩
  have hfirst_mem :
      firstOutgoing ∈ geometricOutgoingDartList C center :=
    mem_geometricOutgoingDartList C center firstOutgoing
  have hsecond_mem :
      secondOutgoing ∈ geometricOutgoingDartList C center :=
    mem_geometricOutgoingDartList C center secondOutgoing
  have hno_list :
      ∀ other ∈ geometricOutgoingDartList C center,
        other ≠ firstOutgoing -> other ≠ secondOutgoing ->
          ¬ (graphDartArg (canonicalGeometricGraph C) center firstOutgoing.1.head <
                graphDartArg (canonicalGeometricGraph C) center other.1.head ∨
              graphDartArg (canonicalGeometricGraph C) center other.1.head <
                graphDartArg (canonicalGeometricGraph C) center secondOutgoing.1.head) := by
    intro other _hmem hother_ne_first hother_ne_second
    have hother_adj :
        GraphBridge.UnitDistanceAdj C center other.1.head := by
      exact (GraphBridge.unitDistanceSimpleGraph_adj C center other.1.head).1
        (by simpa [other.2] using other.1.adj)
    have hother_head_ne_first : other.1.head ≠ first.head := by
      intro hhead
      apply hother_ne_first
      apply Subtype.ext
      apply UnitDistanceDart.endpointPair_injective
      simp [UnitDistanceDart.endpointPair, firstOutgoing, other.2,
        hfirst_tail, hhead]
    have hother_head_ne_second : other.1.head ≠ second.head := by
      intro hhead
      apply hother_ne_second
      apply Subtype.ext
      apply UnitDistanceDart.endpointPair_injective
      simp [UnitDistanceDart.endpointPair, secondOutgoing, other.2,
        hsecond_tail, hhead]
    simpa [firstOutgoing, secondOutgoing] using
      hno_between other.1.head hother_adj
        hother_head_ne_first hother_head_ne_second
  rcases
    List.exists_getElem_last_zero_eq_of_pairwise_real_lt_no_between_wrap
      (xs := geometricOutgoingDartList C center)
      (weight := fun outgoing : OutgoingUnitDistanceDart C center =>
        graphDartArg (canonicalGeometricGraph C) center outgoing.1.head)
      (hsorted := geometricOutgoingDartList_pairwise_graphDartArg_lt C center)
      hfirst_mem hsecond_mem
      (by simpa [firstOutgoing, secondOutgoing] using hangle)
      hno_list with
    ⟨hpos, hget_first, hget_second⟩
  right
  refine ⟨hpos, ?_, ?_⟩
  · have hout :
        (dartFromGeometricList C center
          ((geometricOutgoingDartList C center).length - 1)
          (Nat.sub_lt hpos Nat.zero_lt_one)).outgoing = firstOutgoing := by
      simpa [hget_first] using
        dartFromGeometricList_outgoing C center
          ((geometricOutgoingDartList C center).length - 1)
          (Nat.sub_lt hpos Nat.zero_lt_one)
    exact (congrArg Subtype.val hout).symm
  · have hout :
        (dartFromGeometricList C center 0 hpos).outgoing = secondOutgoing := by
      simpa [hget_second] using
        dartFromGeometricList_outgoing C center 0 hpos
    exact (congrArg Subtype.val hout).symm

/-- Branch-sensitive angular exclusion for the concrete geometric outgoing
list: either the successor interval is the ordinary real interval, or it wraps
across the `Complex.arg` branch cut. -/
theorem geometricOutgoingDartListConsecutive_of_no_graphDartArg_between_branch
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (hfirst_tail : first.tail = center)
    (hsecond_tail : second.tail = center)
    (hbranch :
      (graphDartArg (canonicalGeometricGraph C) center first.head <
          graphDartArg (canonicalGeometricGraph C) center second.head ∧
        (∀ other : Fin n,
          GraphBridge.UnitDistanceAdj C center other ->
          other ≠ first.head -> other ≠ second.head ->
            ¬ (graphDartArg (canonicalGeometricGraph C) center first.head <
                  graphDartArg (canonicalGeometricGraph C) center other ∧
                graphDartArg (canonicalGeometricGraph C) center other <
                  graphDartArg (canonicalGeometricGraph C) center second.head))) ∨
      (graphDartArg (canonicalGeometricGraph C) center second.head <
          graphDartArg (canonicalGeometricGraph C) center first.head ∧
        (∀ other : Fin n,
          GraphBridge.UnitDistanceAdj C center other ->
          other ≠ first.head -> other ≠ second.head ->
            ¬ (graphDartArg (canonicalGeometricGraph C) center first.head <
                  graphDartArg (canonicalGeometricGraph C) center other ∨
                graphDartArg (canonicalGeometricGraph C) center other <
                  graphDartArg (canonicalGeometricGraph C) center second.head)))) :
    geometricOutgoingDartListConsecutive C center first second := by
  rcases hbranch with ⟨hangle, hno_between⟩ | ⟨hangle, hno_between⟩
  · exact
      geometricOutgoingDartListConsecutive_of_no_graphDartArg_between
        C center first second hfirst_tail hsecond_tail hangle hno_between
  · exact
      geometricOutgoingDartListConsecutive_of_no_graphDartArg_between_wrap
        C center first second hfirst_tail hsecond_tail hangle hno_between

/-! ## Generic graph-vertex angular no-between rows -/

/-- At an arbitrary graph vertex, the dart to `other` has principal argument
strictly between the selected `left` and `right` darts. -/
abbrev GraphVertexAngularBetween
    (C : _root_.UDConfig n)
    (center left right other : Fin n) : Prop :=
  graphDartArg (canonicalGeometricGraph C) center left <
    graphDartArg (canonicalGeometricGraph C) center other ∧
  graphDartArg (canonicalGeometricGraph C) center other <
    graphDartArg (canonicalGeometricGraph C) center right

/-- Honest angular no-between row at an arbitrary graph vertex. -/
structure GraphVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (center left right : Fin n) where
  angle :
    graphDartArg (canonicalGeometricGraph C) center left <
      graphDartArg (canonicalGeometricGraph C) center right
  no_between :
    forall other : Fin n,
      GraphBridge.UnitDistanceAdj C center other ->
      other ≠ left ->
      other ≠ right ->
        Not (GraphVertexAngularBetween C center left right other)

/-- Input-level row selecting two neighbouring darts by their actual positions
in the sorted geometric outgoing-dart list at `center`.

This is the non-wrap branch: `left` is immediately followed by `right` in
ordinary principal-argument order. -/
structure GraphVertexGeometricAngularNeighborSelectionRow
    (C : _root_.UDConfig n)
    (center left right : Fin n) where
  index : Nat
  index_succ_lt :
    index + 1 < (geometricOutgoingDartList C center).length
  left_eq :
    left =
      (dartFromGeometricList C center index
        (Nat.lt_trans (Nat.lt_succ_self index) index_succ_lt)).head
  right_eq :
    right =
      (dartFromGeometricList C center (index + 1) index_succ_lt).head

set_option linter.style.longLine false in
/-- Nonwrap consecutive entries in the genuine sorted outgoing-dart list
package directly as a geometric angular neighbour-selection row. -/
def graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (i : Nat)
    (hi : i + 1 < (geometricOutgoingDartList C center).length)
    (hfirst :
      first =
        dartFromGeometricList C center i
          (Nat.lt_trans (Nat.lt_succ_self i) hi))
    (hsecond :
      second = dartFromGeometricList C center (i + 1) hi) :
    GraphVertexGeometricAngularNeighborSelectionRow C center
      first.head second.head where
  index := i
  index_succ_lt := hi
  left_eq := by rw [hfirst]
  right_eq := by rw [hsecond]

set_option linter.style.longLine false in
/-- Existence form of
`graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap`. -/
theorem exists_graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (nonwrap :
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C center).length =>
          first =
            dartFromGeometricList C center i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
          second = dartFromGeometricList C center (i + 1) hi) :
    Nonempty
      (GraphVertexGeometricAngularNeighborSelectionRow C center
        first.head second.head) := by
  rcases nonwrap with ⟨i, hi, hfirst, hsecond⟩
  exact
    ⟨graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap
      C center first second i hi hfirst hsecond⟩

set_option linter.style.longLine false in
/-- Adjacent entries of the actual sorted outgoing unit-dart list give the
pointwise geometric neighbour-selection row for their two heads.

This is the direct `getElem` face of
`graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap`:
the proof uses the concrete entries of `geometricOutgoingDartList`, not a
synthetic or identity angular order. -/
def graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingDartList_getElem_heads
    (C : _root_.UDConfig n) (center left right : Fin n)
    (i : Nat)
    (hi : i + 1 < (geometricOutgoingDartList C center).length)
    (hleft :
      left =
        ((geometricOutgoingDartList C center)[i]'(Nat.lt_trans
          (Nat.lt_succ_self i) hi)).1.head)
    (hright :
      right =
        ((geometricOutgoingDartList C center)[i + 1]'hi).1.head) :
    GraphVertexGeometricAngularNeighborSelectionRow C center left right where
  index := i
  index_succ_lt := hi
  left_eq := by
    simpa [dartFromGeometricList_head] using hleft
  right_eq := by
    simpa [dartFromGeometricList_head] using hright

set_option linter.style.longLine false in
/-- Existence form of
`graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingDartList_getElem_heads`. -/
theorem exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingDartList_getElem_heads
    (C : _root_.UDConfig n) (center left right : Fin n)
    (rows :
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C center).length =>
          left =
            ((geometricOutgoingDartList C center)[i]'(Nat.lt_trans
              (Nat.lt_succ_self i) hi)).1.head /\
          right =
            ((geometricOutgoingDartList C center)[i + 1]'hi).1.head) :
    Nonempty
      (GraphVertexGeometricAngularNeighborSelectionRow C center left right) := by
  rcases rows with ⟨i, hi, hleft, hright⟩
  exact
    ⟨graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingDartList_getElem_heads
      C center left right i hi hleft hright⟩

/-- Consecutive entries in the genuine sorted geometric outgoing-dart list
supply the ordinary angular no-between row at that graph vertex. -/
theorem graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C center left right) :
    GraphVertexAngularNoBetweenRows C center left right := by
  classical
  rcases row with ⟨i, hi, hleft, hright⟩
  let L := geometricOutgoingDartList C center
  let first : OutgoingUnitDistanceDart C center :=
    L[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi)
  let second : OutgoingUnitDistanceDart C center := L[i + 1]'hi
  have hfirst_head : first.1.head = left := by
    symm
    simpa [first, L] using hleft
  have hsecond_head : second.1.head = right := by
    symm
    simpa [second, L] using hright
  have hangle_list :
      graphDartArg (canonicalGeometricGraph C) center first.1.head <
        graphDartArg (canonicalGeometricGraph C) center second.1.head := by
    have hrel :=
      (geometricOutgoingDartList_pairwise_graphDartArg_lt C center).rel_get_of_lt
        (a := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
        (b := ⟨i + 1, hi⟩)
        (by simp)
    simpa [first, second, L] using hrel
  refine
    { angle := by
        simpa [hfirst_head, hsecond_head] using hangle_list
      no_between := ?_ }
  intro other hAdj hother_left hother_right hbetween
  let otherDart : UnitDistanceDart C := {
    tail := center
    head := other
    adj :=
      (GraphBridge.unitDistanceSimpleGraph_adj C center other).2 hAdj }
  let otherOutgoing : OutgoingUnitDistanceDart C center := ⟨otherDart, rfl⟩
  have hother_mem : otherOutgoing ∈ L := by
    simpa [L] using mem_geometricOutgoingDartList C center otherOutgoing
  have hother_ne_first : otherOutgoing ≠ first := by
    intro h
    have hhead : other = first.1.head := by
      exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) h
    exact hother_left (by simpa [hfirst_head] using hhead)
  have hother_ne_second : otherOutgoing ≠ second := by
    intro h
    have hhead : other = second.1.head := by
      exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) h
    exact hother_right (by simpa [hsecond_head] using hhead)
  have hno_list :
      ∀ other' ∈ L, other' ≠ first -> other' ≠ second ->
        ¬ (graphDartArg (canonicalGeometricGraph C) center first.1.head <
              graphDartArg (canonicalGeometricGraph C) center other'.1.head ∧
            graphDartArg (canonicalGeometricGraph C) center other'.1.head <
              graphDartArg (canonicalGeometricGraph C) center second.1.head) := by
    simpa [first, second, L] using
      List.no_between_of_getElem_succ_pairwise_real_lt
        (xs := L)
        (weight := fun outgoing : OutgoingUnitDistanceDart C center =>
          graphDartArg (canonicalGeometricGraph C) center outgoing.1.head)
        (hsorted := geometricOutgoingDartList_pairwise_graphDartArg_lt C center)
        i hi rfl rfl
  exact
    hno_list otherOutgoing hother_mem hother_ne_first hother_ne_second
      (by
        simpa [GraphVertexAngularBetween, otherOutgoing, otherDart,
          hfirst_head, hsecond_head] using hbetween)

/-- Consecutive selected entries in the genuine sorted geometric outgoing
dart list supply the list-level no-between row used by the S2 selected-head
reducers.

This keeps the order source tied to `geometricOutgoingDartList`: every
intervening candidate is an actual outgoing unit-distance dart, not an
identity-order placeholder. -/
theorem geometricOutgoingDartList_no_between_of_graphVertexGeometricAngularNeighborSelectionRow
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C center left right) :
    graphDartArg (canonicalGeometricGraph C) center left <
        graphDartArg (canonicalGeometricGraph C) center right ∧
      forall outgoing : OutgoingUnitDistanceDart C center,
        outgoing ∈ geometricOutgoingDartList C center ->
          outgoing.1.head ≠ left ->
            outgoing.1.head ≠ right ->
              Not (GraphVertexAngularBetween C center left right
                outgoing.1.head) := by
  have angularRows :
      GraphVertexAngularNoBetweenRows C center left right :=
    graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row
  refine ⟨angularRows.angle, ?_⟩
  intro outgoing _houtgoing hleft hright hbetween
  have hAdj : GraphBridge.UnitDistanceAdj C center outgoing.1.head := by
    exact (GraphBridge.unitDistanceSimpleGraph_adj C center
      outgoing.1.head).1
      (by simpa [outgoing.2] using outgoing.1.adj)
  exact
    angularRows.no_between outgoing.1.head hAdj hleft hright hbetween

set_option linter.style.longLine false in
/-- A genuine sorted outgoing-list no-between row gives the graph-vertex
angular no-between row for the same two heads.

This is the outgoing-list eraser used by source-facing S2 reducers: an
arbitrary adjacent head is first represented by its real outgoing unit-distance
dart at `center`, so the primitive no-between source remains stated against
`geometricOutgoingDartList`. -/
theorem graphVertexAngularNoBetweenRows_of_geometricOutgoingDartList_no_between
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hangle :
      graphDartArg (canonicalGeometricGraph C) center left <
        graphDartArg (canonicalGeometricGraph C) center right)
    (hno_between :
      forall outgoing : OutgoingUnitDistanceDart C center,
        outgoing ∈ geometricOutgoingDartList C center ->
          outgoing.1.head ≠ left ->
            outgoing.1.head ≠ right ->
              Not (GraphVertexAngularBetween C center left right
                outgoing.1.head)) :
    GraphVertexAngularNoBetweenRows C center left right := by
  refine
    { angle := hangle
      no_between := ?_ }
  intro other hAdj hother_left hother_right hbetween
  let otherDart : UnitDistanceDart C := {
    tail := center
    head := other
    adj := (GraphBridge.unitDistanceSimpleGraph_adj C center other).2 hAdj }
  let otherOutgoing : OutgoingUnitDistanceDart C center := ⟨otherDart, rfl⟩
  exact
    hno_between otherOutgoing
      (mem_geometricOutgoingDartList C center otherOutgoing)
      (by simpa [otherOutgoing, otherDart] using hother_left)
      (by simpa [otherOutgoing, otherDart] using hother_right)
      (by simpa [otherOutgoing, otherDart] using hbetween)

set_option linter.style.longLine false in
/-- Genuine sorted outgoing-list no-between row at one graph vertex.

The quantifier ranges over entries of `geometricOutgoingDartList`, so this is
the list-level source behind `GraphVertexAngularNoBetweenRows`; arbitrary
adjacent heads are recovered by reattaching them to the same real outgoing
unit-distance dart list. -/
structure GraphVertexGeometricOutgoingListNoBetweenRows
    (C : _root_.UDConfig n)
    (center left right : Fin n) where
  angle :
    graphDartArg (canonicalGeometricGraph C) center left <
      graphDartArg (canonicalGeometricGraph C) center right
  no_between :
    forall outgoing : OutgoingUnitDistanceDart C center,
      outgoing ∈ geometricOutgoingDartList C center ->
        outgoing.1.head ≠ left ->
          outgoing.1.head ≠ right ->
            Not (GraphVertexAngularBetween C center left right
              outgoing.1.head)

namespace GraphVertexGeometricOutgoingListNoBetweenRows

variable {C : _root_.UDConfig n}
variable {center left right : Fin n}

/-- Erase a genuine outgoing-list no-between row to the graph-vertex angular
no-between row for the same two heads. -/
theorem toGraphVertexAngularNoBetweenRows
    (rows :
      GraphVertexGeometricOutgoingListNoBetweenRows C center left right) :
    GraphVertexAngularNoBetweenRows C center left right :=
  graphVertexAngularNoBetweenRows_of_geometricOutgoingDartList_no_between
    rows.angle rows.no_between

end GraphVertexGeometricOutgoingListNoBetweenRows

set_option linter.style.longLine false in
/-- An honest graph-vertex angular no-between row restricts to the genuine
sorted outgoing-dart list at the same vertex.

This is the pointwise eraser between the two selected-head source faces: every
candidate in the list is first read as an actual unit-distance outgoing dart,
so the resulting row is still stated over `geometricOutgoingDartList`. -/
theorem graphVertexGeometricOutgoingListNoBetweenRows_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (rows : GraphVertexAngularNoBetweenRows C center left right) :
    GraphVertexGeometricOutgoingListNoBetweenRows C center left right := by
  refine
    { angle := rows.angle
      no_between := ?_ }
  intro outgoing _houtgoing hleft hright hbetween
  have hAdj : GraphBridge.UnitDistanceAdj C center outgoing.1.head := by
    exact (GraphBridge.unitDistanceSimpleGraph_adj C center
      outgoing.1.head).1
      (by simpa [outgoing.2] using outgoing.1.adj)
  exact rows.no_between outgoing.1.head hAdj hleft hright hbetween

set_option linter.style.longLine false in
/-- Pointwise equivalence between the angular source and the genuine
outgoing-list source for the same selected heads.

The reverse direction reattaches an arbitrary adjacent head to the real
`geometricOutgoingDartList`; the forward direction simply restricts the
angular no-between row to actual outgoing darts. -/
theorem graphVertexAngularNoBetweenRows_iff_geometricOutgoingListNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n} :
    GraphVertexAngularNoBetweenRows C center left right <->
      GraphVertexGeometricOutgoingListNoBetweenRows C center left right := by
  constructor
  · intro rows
    exact
      graphVertexGeometricOutgoingListNoBetweenRows_of_graphVertexAngularNoBetweenRows
        rows
  · intro rows
    exact rows.toGraphVertexAngularNoBetweenRows

set_option linter.style.longLine false in
/-- Family eraser from honest graph-vertex angular no-between rows to the
genuine outgoing-list no-between rows for the same selected heads.

Each pointwise row is restricted to entries of the real sorted
`geometricOutgoingDartList`; no synthetic cyclic order is introduced. -/
theorem graphVertexGeometricOutgoingListNoBetweenRows_family_of_graphVertexAngularNoBetweenRows
    {ι : Type*}
    {C : _root_.UDConfig n}
    (center left right : ι -> Fin n)
    (rows :
      forall a : ι,
        GraphVertexAngularNoBetweenRows C (center a) (left a) (right a)) :
    forall a : ι,
      GraphVertexGeometricOutgoingListNoBetweenRows C
        (center a) (left a) (right a) := by
  intro a
  exact
    graphVertexGeometricOutgoingListNoBetweenRows_of_graphVertexAngularNoBetweenRows
      (rows a)

set_option linter.style.longLine false in
/-- Consecutive selected entries in the genuine sorted geometric outgoing
dart list supply the named outgoing-list no-between source for the same two
heads. -/
theorem graphVertexGeometricOutgoingListNoBetweenRows_of_geometricAngularNeighborSelectionRow
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C center left right) :
    GraphVertexGeometricOutgoingListNoBetweenRows C center left right := by
  rcases
      geometricOutgoingDartList_no_between_of_graphVertexGeometricAngularNeighborSelectionRow
        row with
    ⟨hangle, hno_between⟩
  exact
    { angle := hangle
      no_between := hno_between }

/-- An honest non-wrap angular no-between row for two actual incident heads
forces those heads to occupy adjacent entries in the genuine sorted geometric
outgoing-dart list. -/
theorem exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right)
    (rows : GraphVertexAngularNoBetweenRows C center left right) :
    Nonempty
      (GraphVertexGeometricAngularNeighborSelectionRow C center left right) := by
  classical
  let leftDart : UnitDistanceDart C := {
    tail := center
    head := left
    adj := (GraphBridge.unitDistanceSimpleGraph_adj C center left).2 hleft_adj }
  let rightDart : UnitDistanceDart C := {
    tail := center
    head := right
    adj := (GraphBridge.unitDistanceSimpleGraph_adj C center right).2 hright_adj }
  let leftOutgoing : OutgoingUnitDistanceDart C center := ⟨leftDart, rfl⟩
  let rightOutgoing : OutgoingUnitDistanceDart C center := ⟨rightDart, rfl⟩
  have hleft_mem :
      leftOutgoing ∈ geometricOutgoingDartList C center :=
    mem_geometricOutgoingDartList C center leftOutgoing
  have hright_mem :
      rightOutgoing ∈ geometricOutgoingDartList C center :=
    mem_geometricOutgoingDartList C center rightOutgoing
  have hno_list :
      ∀ other ∈ geometricOutgoingDartList C center,
        other ≠ leftOutgoing -> other ≠ rightOutgoing ->
          ¬ (graphDartArg (canonicalGeometricGraph C) center
                leftOutgoing.1.head <
              graphDartArg (canonicalGeometricGraph C) center
                other.1.head ∧
            graphDartArg (canonicalGeometricGraph C) center
                other.1.head <
              graphDartArg (canonicalGeometricGraph C) center
                rightOutgoing.1.head) := by
    intro other _hmem hother_ne_left hother_ne_right
    have hother_adj :
        GraphBridge.UnitDistanceAdj C center other.1.head := by
      exact (GraphBridge.unitDistanceSimpleGraph_adj C center other.1.head).1
        (by simpa [other.2] using other.1.adj)
    have hother_head_ne_left : other.1.head ≠ left := by
      intro hhead
      apply hother_ne_left
      apply Subtype.ext
      apply UnitDistanceDart.endpointPair_injective
      simp [UnitDistanceDart.endpointPair, leftOutgoing, leftDart, other.2,
        hhead]
    have hother_head_ne_right : other.1.head ≠ right := by
      intro hhead
      apply hother_ne_right
      apply Subtype.ext
      apply UnitDistanceDart.endpointPair_injective
      simp [UnitDistanceDart.endpointPair, rightOutgoing, rightDart, other.2,
        hhead]
    simpa [GraphVertexAngularBetween, leftOutgoing, rightOutgoing,
      leftDart, rightDart] using
      rows.no_between other.1.head hother_adj
        hother_head_ne_left hother_head_ne_right
  rcases
    List.exists_getElem_succ_eq_of_pairwise_real_lt_no_between
      (xs := geometricOutgoingDartList C center)
      (weight := fun outgoing : OutgoingUnitDistanceDart C center =>
        graphDartArg (canonicalGeometricGraph C) center outgoing.1.head)
      (hsorted := geometricOutgoingDartList_pairwise_graphDartArg_lt C center)
      hleft_mem hright_mem
      (by simpa [leftOutgoing, rightOutgoing, leftDart, rightDart] using rows.angle)
      hno_list with
    ⟨i, hi, hget_left, hget_right⟩
  refine ⟨?_⟩
  refine
    { index := i
      index_succ_lt := hi
      left_eq := ?_
      right_eq := ?_ }
  · have hhead :=
      congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head)
        hget_left
    simpa [leftOutgoing, leftDart, dartFromGeometricList_head] using hhead.symm
  · have hhead :=
      congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head)
        hget_right
    simpa [rightOutgoing, rightDart, dartFromGeometricList_head] using hhead.symm

/-- Choice form of
`exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows`. -/
noncomputable def graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right)
    (rows : GraphVertexAngularNoBetweenRows C center left right) :
    GraphVertexGeometricAngularNeighborSelectionRow C center left right :=
  Classical.choice
    (exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
      hleft_adj hright_adj rows)

set_option linter.style.longLine false in
/-- A genuine sorted outgoing-list no-between row identifies the selected
heads as adjacent nonwrap entries of the real geometric outgoing-dart list.

The only membership input needed beyond the list row is that the two selected
heads are actual unit-distance neighbours of `center`, so they occur in
`geometricOutgoingDartList`. -/
theorem
    exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right)
    (rows : GraphVertexGeometricOutgoingListNoBetweenRows C center left right) :
    Nonempty
      (GraphVertexGeometricAngularNeighborSelectionRow C center left right) :=
  exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
    hleft_adj hright_adj rows.toGraphVertexAngularNoBetweenRows

set_option linter.style.longLine false in
/-- Choice form of
`exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows`.

This is the geometry-level eraser from the real outgoing-list no-between
source to the exact selected sorted-list/index row used by S2 wrappers. -/
noncomputable def graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right)
    (rows : GraphVertexGeometricOutgoingListNoBetweenRows C center left right) :
    GraphVertexGeometricAngularNeighborSelectionRow C center left right :=
  Classical.choice
    (exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
      hleft_adj hright_adj rows)

namespace GraphVertexGeometricOutgoingListNoBetweenRows

variable {C : _root_.UDConfig n}
variable {center left right : Fin n}

set_option linter.style.longLine false in
/-- Namespace form: a genuine outgoing-list no-between row, together with
adjacency of the two selected heads, gives the exact geometric neighbour
selection row in `geometricOutgoingDartList`. -/
theorem exists_geometricAngularNeighborSelectionRow
    (rows : GraphVertexGeometricOutgoingListNoBetweenRows C center left right)
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right) :
    Nonempty
      (GraphVertexGeometricAngularNeighborSelectionRow C center left right) :=
  exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
    hleft_adj hright_adj rows

set_option linter.style.longLine false in
/-- Namespace choice form of
`GraphVertexGeometricOutgoingListNoBetweenRows.exists_geometricAngularNeighborSelectionRow`. -/
noncomputable def toGeometricAngularNeighborSelectionRow
    (rows : GraphVertexGeometricOutgoingListNoBetweenRows C center left right)
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right) :
    GraphVertexGeometricAngularNeighborSelectionRow C center left right :=
  graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
    hleft_adj hright_adj rows

end GraphVertexGeometricOutgoingListNoBetweenRows

set_option linter.style.longLine false in
/-- Honest angular no-between rows for actual incident selected heads are
equivalent to the existence of the matching nonwrap adjacent index row in the
real sorted `geometricOutgoingDartList`.

The forward implication is the sorted-list extraction theorem using
`graphDartArg` order and no-between exclusion; the reverse implication reads
the row back from consecutive entries of the same list. -/
theorem graphVertexAngularNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right) :
    GraphVertexAngularNoBetweenRows C center left right <->
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C center left right) := by
  constructor
  · intro rows
    exact
      exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
        hleft_adj hright_adj rows
  · rintro ⟨row⟩
    exact graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Genuine outgoing-list no-between rows for actual incident selected heads
are equivalent to the existence of the matching nonwrap adjacent index row in
the real sorted `geometricOutgoingDartList`.

This is the outgoing-list face of the selected-head reduction: the remaining
source may be stated as pointwise `GraphVertexGeometricOutgoingListNoBetweenRows`
or as pointwise sorted-list neighbour-selection rows, with no identity angular
order or synthetic carrier cycle. -/
theorem graphVertexGeometricOutgoingListNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
    {C : _root_.UDConfig n}
    {center left right : Fin n}
    (hleft_adj : GraphBridge.UnitDistanceAdj C center left)
    (hright_adj : GraphBridge.UnitDistanceAdj C center right) :
    GraphVertexGeometricOutgoingListNoBetweenRows C center left right <->
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C center left right) := by
  constructor
  · intro rows
    exact
      exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricOutgoingListNoBetweenRows
        hleft_adj hright_adj rows
  · rintro ⟨row⟩
    exact graphVertexGeometricOutgoingListNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row

set_option linter.style.longLine false in
/-- Family-level selected-head reduction over the genuine sorted outgoing list.

For any pointwise selected-head family, angular no-between rows and
outgoing-list no-between rows are both exactly reduced to the same residual:
nonempty geometric neighbour-selection rows in the real
`geometricOutgoingDartList`, with the selected heads required to be actual
unit-distance neighbours of their centers. -/
theorem S2_codex_current_20260520_selected_head_angular_order_final_source
    {ι : Type*}
    {C : _root_.UDConfig n}
    (center left right : ι -> Fin n)
    (hleft_adj :
      forall a : ι, GraphBridge.UnitDistanceAdj C (center a) (left a))
    (hright_adj :
      forall a : ι, GraphBridge.UnitDistanceAdj C (center a) (right a)) :
    ((forall a : ι,
        GraphVertexAngularNoBetweenRows C (center a) (left a) (right a)) <->
      (forall a : ι,
        Nonempty
          (GraphVertexGeometricAngularNeighborSelectionRow C
            (center a) (left a) (right a)))) /\
    ((forall a : ι,
        GraphVertexGeometricOutgoingListNoBetweenRows C
          (center a) (left a) (right a)) <->
      (forall a : ι,
        Nonempty
          (GraphVertexGeometricAngularNeighborSelectionRow C
            (center a) (left a) (right a)))) := by
  constructor
  · constructor
    · intro angularRows a
      exact
        (graphVertexAngularNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
          (C := C) (center := center a) (left := left a) (right := right a)
          (hleft_adj a) (hright_adj a)).1
          (angularRows a)
    · intro indexRows a
      exact
        (graphVertexAngularNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
          (C := C) (center := center a) (left := left a) (right := right a)
          (hleft_adj a) (hright_adj a)).2
          (indexRows a)
  · constructor
    · intro listRows a
      exact
        (graphVertexGeometricOutgoingListNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
          (C := C) (center := center a) (left := left a) (right := right a)
          (hleft_adj a) (hright_adj a)).1
          (listRows a)
    · intro indexRows a
      exact
        (graphVertexGeometricOutgoingListNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
          (C := C) (center := center a) (left := left a) (right := right a)
          (hleft_adj a) (hright_adj a)).2
          (indexRows a)

set_option linter.style.longLine false in
/-- An honest angular no-between row at a graph vertex identifies two concrete
incident darts as adjacent nonwrap entries of the real sorted outgoing-dart
list.

This is the generic raw-orbit-facing reducer: the adjacency hypotheses come
from the actual darts, and the order step is routed through the
`GraphVertexAngularNoBetweenRows` to geometric-neighbour selector. -/
theorem geometricOutgoingDartList_nonwrap_of_graphVertexAngularNoBetweenRows
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (hfirst_tail : first.tail = center)
    (hsecond_tail : second.tail = center)
    (rows : GraphVertexAngularNoBetweenRows C center first.head second.head) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C center).length =>
        first =
          dartFromGeometricList C center i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
        second = dartFromGeometricList C center (i + 1) hi := by
  have hfirst_adj :
      GraphBridge.UnitDistanceAdj C center first.head := by
    exact (GraphBridge.unitDistanceSimpleGraph_adj C center first.head).1
      (by simpa [hfirst_tail] using first.adj)
  have hsecond_adj :
      GraphBridge.UnitDistanceAdj C center second.head := by
    exact (GraphBridge.unitDistanceSimpleGraph_adj C center second.head).1
      (by simpa [hsecond_tail] using second.adj)
  let row :=
    graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
      hfirst_adj hsecond_adj rows
  rcases row with ⟨i, hi, hfirst_head, hsecond_head⟩
  refine ⟨i, hi, ?_, ?_⟩
  · apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair, dartFromGeometricList,
      hfirst_tail, hfirst_head]
  · apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair, dartFromGeometricList,
      hsecond_tail, hsecond_head]

set_option linter.style.longLine false in
/-- Face-successor specialization of
`geometricOutgoingDartList_nonwrap_of_graphVertexAngularNoBetweenRows`.

If a geometric face-successor row gives the concrete successor dart, then an
honest angular no-between row for the reverse incoming dart and successor
dart selects the nonwrap branch of that same sorted outgoing list. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_nonwrap_of_graphVertexAngularNoBetweenRows
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (rows : GraphVertexAngularNoBetweenRows C d.head d.reverse.head e.head) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C d.head).length =>
        d.reverse =
          dartFromGeometricList C d.head i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
        e = dartFromGeometricList C d.head (i + 1) hi := by
  have he_tail : e.tail = d.head := by
    rw [← hface]
    exact (geometricUnitDistanceRotationSystem C).faceSucc_tail_eq_head d
  exact
    geometricOutgoingDartList_nonwrap_of_graphVertexAngularNoBetweenRows
      C d.head d.reverse e (by simp) he_tail rows

set_option linter.style.longLine false in
/-- Raw-face-successor-orbit orientation rows from honest angular no-between
rows at the same raw tails.

This is the geometry-level shape of the selected raw-orbit orientation
residual: every row is read from a genuine no-between sector, not from an
identity cyclic-order shortcut. -/
theorem rawFaceSuccOrbit_orientationRows_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (angularRows :
      forall k : Fin O.period,
        GraphVertexAngularNoBetweenRows C (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail := by
  intro k
  exact (angularRows k).angle

set_option linter.style.longLine false in
/-- Raw-face-successor-orbit nonwrap successor rows from honest angular
no-between rows and the orbit's actual geometric `faceSucc` steps.

At each selected raw tail, the previous raw dart's reverse and the current raw
dart are recovered as adjacent nonwrap entries of the concrete
`geometricOutgoingDartList`. -/
theorem rawFaceSuccOrbit_geometricSuccessorNonwrapRows_of_graphVertexAngularNoBetweenRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (angularRows :
      forall k : Fin O.period,
        GraphVertexAngularNoBetweenRows C (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).reverse =
            dartFromGeometricList C (O.dart k).tail i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
          O.dart k = dartFromGeometricList C (O.dart k).tail (i + 1) hi := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have hface_pred :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart pred) =
        O.dart k := by
    simp [pred, hsucc_pred]
  have hpred_head : (O.dart pred).head = (O.dart k).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_pred
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    simp [succ]
  have hcurrent_head : (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hreverse_tail :
      ((O.dart pred).reverse).tail = (O.dart k).tail := by
    simpa [UnitDistanceDart.reverse_tail] using hpred_head
  have hrows :
      GraphVertexAngularNoBetweenRows C (O.dart k).tail
        ((O.dart pred).reverse).head (O.dart k).head := by
    simpa [pred, succ, UnitDistanceDart.reverse_head, hcurrent_head]
      using angularRows k
  exact
    geometricOutgoingDartList_nonwrap_of_graphVertexAngularNoBetweenRows
      C (O.dart k).tail (O.dart pred).reverse (O.dart k)
      hreverse_tail rfl hrows

set_option linter.style.longLine false in
/-- Reify raw-orbit nonwrap sorted-list successor rows as pointwise geometric
angular-neighbour selection rows.

This is the generic helper shape consumed by selected raw-orbit sources: it
keeps the evidence in the actual `geometricOutgoingDartList` rows and only
reattaches the predecessor/current/successor heads supplied by the genuine
raw `faceSucc` orbit. -/
theorem rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_geometricSuccessorNonwrapRows_20260521k18
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (successorRows :
      forall k : Fin O.period,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).reverse =
              dartFromGeometricList C (O.dart k).tail i
                (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
            O.dart k =
              dartFromGeometricList C (O.dart k).tail (i + 1) hi) :
    forall k : Fin O.period,
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C
          (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    simp [succ]
  have hcurrent_head :
      (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hnonwrap :
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
          (O.dart pred).reverse =
            dartFromGeometricList C (O.dart k).tail i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
          O.dart k =
            dartFromGeometricList C (O.dart k).tail (i + 1) hi := by
    simpa [pred] using successorRows k
  rcases
      exists_graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap
        C (O.dart k).tail (O.dart pred).reverse (O.dart k) hnonwrap with
    ⟨row⟩
  exact
    ⟨by
      simpa [pred, succ, UnitDistanceDart.reverse_head, hcurrent_head]
        using row⟩

set_option linter.style.longLine false in
/-- Raw-orbit nonwrap sorted-list successor rows give the
predecessor-before-successor orientation row.

The source is still the concrete nonwrap branch of `geometricOutgoingDartList`:
we first reify the adjacent list entries as a geometric neighbour-selection row
and then read off its strict `graphDartArg` order. -/
theorem rawFaceSuccOrbit_orientationRows_of_geometricSuccessorNonwrapRows_20260521r26
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (successorRows :
      forall k : Fin O.period,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).reverse =
              dartFromGeometricList C (O.dart k).tail i
                (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
            O.dart k =
              dartFromGeometricList C (O.dart k).tail (i + 1) hi) :
    forall k : Fin O.period,
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail := by
  intro k
  rcases
      rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_geometricSuccessorNonwrapRows_20260521k18
        O successorRows k with
    ⟨row⟩
  exact
    (graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
      row).angle

set_option linter.style.longLine false in
/-- Raw-orbit nonwrap rows give the strict head-angle lowering for the actual
geometric `faceSucc` dart at the predecessor carrier.

For the step ending at `O.dart k`, the source row is the genuine adjacent
nonwrap pair in `geometricOutgoingDartList` at the shared tail.  The conclusion
is stated at the predecessor dart's own head and uses the actual
`(geometricUnitDistanceRotationSystem C).faceSucc` target, rather than a
synthetic successor head. -/
theorem rawFaceSuccOrbit_actualFaceSucc_headAngle_lt_of_geometricSuccessorNonwrapRows_20260522
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (successorRows :
      forall k : Fin O.period,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).reverse =
              dartFromGeometricList C (O.dart k).tail i
                (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
            O.dart k =
              dartFromGeometricList C (O.dart k).tail (i + 1) hi) :
    forall k : Fin O.period,
      let pred : Fin O.period :=
        PlanarInterface.cyclicPred O.period_pos k
      graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
          (O.dart pred).reverse.head <
        graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
          ((geometricUnitDistanceRotationSystem C).faceSucc
            (O.dart pred)).head := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have hface_pred :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart pred) =
        O.dart k := by
    simp [pred, hsucc_pred]
  have hpred_head :
      (O.dart pred).head = (O.dart k).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_pred
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    simp [succ]
  have hcurrent_head :
      (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hangle :=
    rawFaceSuccOrbit_orientationRows_of_geometricSuccessorNonwrapRows_20260521r26
      O successorRows k
  have hangle_current :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart pred).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head := by
    simpa [pred, succ, hcurrent_head] using hangle
  simpa [pred, UnitDistanceDart.reverse_head, hpred_head, hface_pred]
    using hangle_current

set_option linter.style.longLine false in
/-- Honest raw-orbit angular no-between rows give the pointwise geometric
angular-neighbour selection rows for predecessor and successor tails.

The proof factors through the genuine nonwrap entries of
`geometricOutgoingDartList`, not through an identity cyclic order. -/
theorem rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_graphVertexAngularNoBetweenRows_20260521k18
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (angularRows :
      forall k : Fin O.period,
        GraphVertexAngularNoBetweenRows C (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C
          (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :=
  rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_geometricSuccessorNonwrapRows_20260521k18
    O
    (rawFaceSuccOrbit_geometricSuccessorNonwrapRows_of_graphVertexAngularNoBetweenRows
      O angularRows)

/-! ## Boundary face-successor rows from geometric list adjacency -/

/-- If the reverse of a dart and the target dart occupy consecutive positions
in the sorted geometric outgoing list at the shared vertex, then the geometric
rotation system's face successor sends the first dart to the target dart. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_succ
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (i : Nat)
    (hi : i + 1 < (geometricOutgoingDartList C d.head).length)
    (hreverse :
      d.reverse =
        dartFromGeometricList C d.head i
          (Nat.lt_trans (Nat.lt_succ_self i) hi))
    (htarget :
      e = dartFromGeometricList C d.head (i + 1) hi) :
    (geometricUnitDistanceRotationSystem C).faceSucc d = e := by
  rw [UnitDistanceRotationSystem.faceSucc, hreverse, htarget]
  exact geometricUnitDistanceRotationSystem_nextAround_getElem_succ
    C d.head i hi

set_option linter.style.longLine false in
/-- Adjacent entries in the genuine sorted outgoing-dart list have the
corresponding strict principal graph-dart argument order. -/
theorem graphDartArg_lt_of_dartFromGeometricList_getElem_succ
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (i : Nat)
    (hi : i + 1 < (geometricOutgoingDartList C center).length)
    (hfirst :
      first =
        dartFromGeometricList C center i
          (Nat.lt_trans (Nat.lt_succ_self i) hi))
    (hsecond :
      second = dartFromGeometricList C center (i + 1) hi) :
    graphDartArg (canonicalGeometricGraph C) center first.head <
      graphDartArg (canonicalGeometricGraph C) center second.head := by
  have hlt :=
    graphDartArg_lt_of_dartFromGeometricList_index_lt
      C center
      (Nat.lt_trans (Nat.lt_succ_self i) hi) hi
      (Nat.lt_succ_self i)
  simpa [hfirst, hsecond] using hlt

set_option linter.style.longLine false in
/-- Non-wrap adjacent sorted-list entries identify both the genuine geometric
face successor and the corresponding strict `graphDartArg` order.

The optional `center` parameter lets callers keep the list source stated at a
known shared tail while the face-successor equality is still checked at
`d.head`. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_eq_and_graphDartArg_lt_of_reverse_getElem_succ_at
    (C : _root_.UDConfig n) (center : Fin n)
    (d e : UnitDistanceDart C)
    (hcenter : d.head = center)
    (i : Nat)
    (hi : i + 1 < (geometricOutgoingDartList C center).length)
    (hreverse :
      d.reverse =
        dartFromGeometricList C center i
          (Nat.lt_trans (Nat.lt_succ_self i) hi))
    (htarget :
      e = dartFromGeometricList C center (i + 1) hi) :
    (geometricUnitDistanceRotationSystem C).faceSucc d = e ∧
      graphDartArg (canonicalGeometricGraph C) center d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) center e.head := by
  subst center
  exact
    ⟨geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_succ
        C d e i hi hreverse htarget,
      graphDartArg_lt_of_dartFromGeometricList_getElem_succ
        C d.head d.reverse e i hi hreverse htarget⟩

set_option linter.style.longLine false in
/-- A non-wrap geometric neighbour-selection row identifies the actual
geometric face-successor dart.

This is the list-row face of `faceSucc`: if the reverse incoming dart and a
target outgoing dart are consecutive entries of the genuine
`geometricOutgoingDartList` at the shared tail, then the geometric rotation
system sends the incoming dart to that target. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_eq_of_geometricAngularNeighborSelectionRow
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (he_tail : e.tail = d.head)
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C d.head
        d.reverse.head e.head) :
    (geometricUnitDistanceRotationSystem C).faceSucc d = e := by
  rcases row with ⟨i, hi, hleft, hright⟩
  exact
    geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_succ
      C d e i hi
      (by
        apply UnitDistanceDart.endpointPair_injective
        change (d.reverse.tail, d.reverse.head) =
          ((dartFromGeometricList C d.head i
            (Nat.lt_trans (Nat.lt_succ_self i) hi)).tail,
            (dartFromGeometricList C d.head i
              (Nat.lt_trans (Nat.lt_succ_self i) hi)).head)
        exact Prod.ext (by simp) hleft)
      (by
        apply UnitDistanceDart.endpointPair_injective
        change (e.tail, e.head) =
          ((dartFromGeometricList C d.head (i + 1) hi).tail,
            (dartFromGeometricList C d.head (i + 1) hi).head)
        exact Prod.ext (by simpa using he_tail) hright)

set_option linter.style.longLine false in
/-- A geometric neighbour-selection row is already the corresponding non-wrap
row for the two concrete darts with those tails and heads.

This is the direct sorted-list eraser: the row supplies the actual
`geometricOutgoingDartList` indices, while endpoint injectivity reattaches the
stored heads to the concrete darts. -/
theorem geometricOutgoingDartList_nonwrap_of_geometricAngularNeighborSelectionRow
    (C : _root_.UDConfig n) (center : Fin n)
    (first second : UnitDistanceDart C)
    (hfirst_tail : first.tail = center)
    (hsecond_tail : second.tail = center)
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C center
        first.head second.head) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C center).length =>
        first =
          dartFromGeometricList C center i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
        second = dartFromGeometricList C center (i + 1) hi := by
  rcases row with ⟨i, hi, hfirst_head, hsecond_head⟩
  refine ⟨i, hi, ?_, ?_⟩
  · apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair, dartFromGeometricList,
      hfirst_tail, hfirst_head]
  · apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair, dartFromGeometricList,
      hsecond_tail, hsecond_head]

set_option linter.style.longLine false in
/-- Face-successor specialization of the direct sorted-list eraser.

If the actual geometric `faceSucc` step sends `d` to `e`, and the reverse of
`d` and `e` are selected as adjacent non-wrap entries in the genuine sorted
outgoing list at `d.head`, then the non-wrap row is available directly. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_nonwrap_of_geometricAngularNeighborSelectionRow
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C d.head
        d.reverse.head e.head) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C d.head).length =>
        d.reverse =
          dartFromGeometricList C d.head i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
        e = dartFromGeometricList C d.head (i + 1) hi := by
  have he_tail : e.tail = d.head := by
    rw [← hface]
    exact (geometricUnitDistanceRotationSystem C).faceSucc_tail_eq_head d
  exact
    geometricOutgoingDartList_nonwrap_of_geometricAngularNeighborSelectionRow
      C d.head d.reverse e (by simp) he_tail row

/-- Wrap-around version of
`geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_succ`. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_last
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hpos : 0 < (geometricOutgoingDartList C d.head).length)
    (hreverse :
      d.reverse =
        dartFromGeometricList C d.head
          ((geometricOutgoingDartList C d.head).length - 1)
          (Nat.sub_lt hpos Nat.zero_lt_one))
    (htarget :
      e = dartFromGeometricList C d.head 0 hpos) :
    (geometricUnitDistanceRotationSystem C).faceSucc d = e := by
  rw [UnitDistanceRotationSystem.faceSucc, hreverse, htarget]
  exact geometricUnitDistanceRotationSystem_nextAround_getElem_last
    C d.head hpos

/-- Predicate-packaged version of the local consecutive-list face-successor
helper. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_eq_of_list_consecutive
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hconsecutive :
      geometricOutgoingDartListConsecutive C d.head d.reverse e) :
    (geometricUnitDistanceRotationSystem C).faceSucc d = e := by
  rcases hconsecutive with hsucc | hlast
  · rcases hsucc with ⟨i, hi, hreverse, htarget⟩
    exact
      geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_succ
        C d e i hi hreverse htarget
  · rcases hlast with ⟨hpos, hreverse, htarget⟩
    exact
      geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_last
        C d e hpos hreverse htarget

/-- Converse to the concrete-list face-successor helper for the geometric
rotation system: an actual geometric face-successor row identifies the reverse
incoming dart and the target dart as consecutive entries of the real sorted
outgoing-dart list, with the wrap-around branch kept explicit. -/
theorem geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e) :
    geometricOutgoingDartListConsecutive C d.head d.reverse e := by
  classical
  let L := geometricOutgoingDartList C d.head
  let firstOutgoing : OutgoingUnitDistanceDart C d.head := ⟨d.reverse, by simp⟩
  have he_tail : e.tail = d.head := by
    rw [← hface]
    exact (geometricUnitDistanceRotationSystem C).faceSucc_tail_eq_head d
  let secondOutgoing : OutgoingUnitDistanceDart C d.head := ⟨e, he_tail⟩
  have hfirst_mem : firstOutgoing ∈ L := by
    simpa [L] using
      mem_geometricOutgoingDartList C d.head firstOutgoing
  have hnext_eq :
      ((geometricUnitDistanceRotationSystem C).rotationAt d.head).next
          firstOutgoing =
        secondOutgoing := by
    apply Subtype.ext
    apply UnitDistanceDart.endpointPair_injective
    apply Prod.ext
    · exact
        (((geometricUnitDistanceRotationSystem C).rotationAt d.head).next
            firstOutgoing).2.trans secondOutgoing.2.symm
    · have hhead :
          ((geometricUnitDistanceRotationSystem C).faceSucc d).head =
            e.head := congrArg UnitDistanceDart.head hface
      simpa [UnitDistanceRotationSystem.faceSucc,
        UnitDistanceRotationSystem.nextAround, firstOutgoing, secondOutgoing]
        using hhead
  have hperm : L.formPerm firstOutgoing = secondOutgoing := by
    simpa [L, geometricUnitDistanceRotationSystem_rotationAt,
      geometricVertexCyclicOrder] using hnext_eq
  rcases
    List.exists_getElem_succ_or_last_zero_of_formPerm_eq
      (xs := L)
      (hnodup := by simpa [L] using geometricOutgoingDartList_nodup C d.head)
      hfirst_mem hperm with
    hsucc | hlast
  · rcases hsucc with ⟨i, hi, hget_first, hget_second⟩
    left
    refine ⟨i, hi, ?_, ?_⟩
    · have hout :
          (dartFromGeometricList C d.head i
            (Nat.lt_trans (Nat.lt_succ_self i) hi)).outgoing =
            firstOutgoing := by
        simpa [L, hget_first] using
          dartFromGeometricList_outgoing C d.head i
            (Nat.lt_trans (Nat.lt_succ_self i) hi)
      exact (congrArg Subtype.val hout).symm
    · have hout :
          (dartFromGeometricList C d.head (i + 1) hi).outgoing =
            secondOutgoing := by
        simpa [L, hget_second] using
          dartFromGeometricList_outgoing C d.head (i + 1) hi
      exact (congrArg Subtype.val hout).symm
  · rcases hlast with ⟨hpos, hget_first, hget_second⟩
    right
    refine ⟨hpos, ?_, ?_⟩
    · have hout :
          (dartFromGeometricList C d.head
            ((geometricOutgoingDartList C d.head).length - 1)
            (Nat.sub_lt hpos Nat.zero_lt_one)).outgoing =
            firstOutgoing := by
        simpa [L, hget_first] using
          dartFromGeometricList_outgoing C d.head
            ((geometricOutgoingDartList C d.head).length - 1)
            (Nat.sub_lt hpos Nat.zero_lt_one)
      exact (congrArg Subtype.val hout).symm
    · have hout :
          (dartFromGeometricList C d.head 0 hpos).outgoing =
            secondOutgoing := by
        simpa [L, hget_second] using
          dartFromGeometricList_outgoing C d.head 0 hpos
      exact (congrArg Subtype.val hout).symm

set_option linter.style.longLine false in
/-- A genuine geometric face-successor step plus the local strict
principal-angle inequality selects the non-wrap branch of the concrete sorted
outgoing list.

This is pointwise at the selected face step: the consecutive-list row comes
from the actual geometric `faceSucc` API, and the angle inequality only rules
out the wrap branch for this pair. -/
theorem geometricUnitDistanceRotationSystem_faceSucc_nonwrap_of_faceSucc_eq_graphDartArg_lt
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (hangle :
      graphDartArg (canonicalGeometricGraph C) d.head d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) d.head e.head) :
    Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C d.head).length =>
        d.reverse =
          dartFromGeometricList C d.head i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
        e = dartFromGeometricList C d.head (i + 1) hi := by
  have hconsecutive :
      geometricOutgoingDartListConsecutive C d.head d.reverse e :=
    geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
      C d e hface
  exact
    geometricOutgoingDartListConsecutive_nonwrap_of_graphDartArg_lt
      C d.head d.reverse e hconsecutive hangle

set_option linter.style.longLine false in
/-- A genuine geometric face-successor step plus the local strict
principal-angle inequality reifies the selected non-wrap face step as the
pointwise geometric angular-neighbour selection row. -/
theorem exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (hangle :
      graphDartArg (canonicalGeometricGraph C) d.head d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) d.head e.head) :
    Nonempty
      (GraphVertexGeometricAngularNeighborSelectionRow C d.head
        d.reverse.head e.head) := by
  exact
    exists_graphVertexGeometricAngularNeighborSelectionRow_of_dartFromGeometricList_nonwrap
      C d.head d.reverse e
      (geometricUnitDistanceRotationSystem_faceSucc_nonwrap_of_faceSucc_eq_graphDartArg_lt
        C d e hface hangle)

set_option linter.style.longLine false in
/-- Choice form of
`exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt`. -/
noncomputable def graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt
    (C : _root_.UDConfig n) (d e : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (hangle :
      graphDartArg (canonicalGeometricGraph C) d.head d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) d.head e.head) :
    GraphVertexGeometricAngularNeighborSelectionRow C d.head
      d.reverse.head e.head :=
  Classical.choice
    (exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt
      C d e hface hangle)

set_option linter.style.longLine false in
/-- Two strict local face-successor turns at the same successor tail select
the two non-wrap neighbouring rows in the concrete geometric outgoing list.

The first row is the genuine `faceSucc d = succ` turn, and the second row is
the next local turn `faceSucc succ.reverse = next`, both at `succ.tail`.  The
only branch choice is made by the supplied strict `graphDartArg` inequalities;
no identity angular order or global no-between row is used. -/
theorem geometricUnitDistanceRotationSystem_successorTail_neighborSelectionRows_of_two_faceSucc_strictOrder
    (C : _root_.UDConfig n) (d succ next : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = succ)
    (hnext :
      (geometricUnitDistanceRotationSystem C).faceSucc succ.reverse = next)
    (hleft :
      graphDartArg (canonicalGeometricGraph C) succ.tail d.tail <
        graphDartArg (canonicalGeometricGraph C) succ.tail succ.head)
    (hright :
      graphDartArg (canonicalGeometricGraph C) succ.tail succ.head <
        graphDartArg (canonicalGeometricGraph C) succ.tail next.head) :
    Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C succ.tail
          d.tail succ.head) ∧
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C succ.tail
          succ.head next.head) := by
  have hsucc_tail : succ.tail = d.head := by
    rw [← hface]
    exact (geometricUnitDistanceRotationSystem C).faceSucc_tail_eq_head d
  have hleft' :
      graphDartArg (canonicalGeometricGraph C) d.head d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) d.head succ.head := by
    simpa [hsucc_tail, UnitDistanceDart.reverse_head] using hleft
  have leftRow :
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C d.head
          d.reverse.head succ.head) :=
    exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt
      C d succ hface hleft'
  have hright' :
      graphDartArg (canonicalGeometricGraph C) succ.reverse.head
          succ.reverse.reverse.head <
        graphDartArg (canonicalGeometricGraph C) succ.reverse.head
          next.head := by
    simpa [UnitDistanceDart.reverse_head, UnitDistanceDart.reverse_tail]
      using hright
  have rightRow :
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C succ.reverse.head
          succ.reverse.reverse.head next.head) :=
    exists_graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt
      C succ.reverse next hnext hright'
  exact
    ⟨by simpa [hsucc_tail, UnitDistanceDart.reverse_head] using leftRow,
      by
        simpa [UnitDistanceDart.reverse_head, UnitDistanceDart.reverse_tail]
          using rightRow⟩

set_option linter.style.longLine false in
/-- Non-wrap `geometricOutgoingDartList` form of
`geometricUnitDistanceRotationSystem_successorTail_neighborSelectionRows_of_two_faceSucc_strictOrder`.

This is the pointwise face-successor-row source: two actual geometric
`faceSucc` equalities plus the two strict turn inequalities produce the
left/head and head/right adjacent-list witnesses at the selected successor
tail. -/
theorem geometricUnitDistanceRotationSystem_successorTail_nonwrapRows_of_two_faceSucc_strictOrder
    (C : _root_.UDConfig n) (d succ next : UnitDistanceDart C)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = succ)
    (hnext :
      (geometricUnitDistanceRotationSystem C).faceSucc succ.reverse = next)
    (hleft :
      graphDartArg (canonicalGeometricGraph C) succ.tail d.tail <
        graphDartArg (canonicalGeometricGraph C) succ.tail succ.head)
    (hright :
      graphDartArg (canonicalGeometricGraph C) succ.tail succ.head <
        graphDartArg (canonicalGeometricGraph C) succ.tail next.head) :
    (Exists fun i : Nat =>
      Exists fun hi : i + 1 < (geometricOutgoingDartList C succ.tail).length =>
        d.reverse =
          dartFromGeometricList C succ.tail i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) ∧
        succ = dartFromGeometricList C succ.tail (i + 1) hi) ∧
      (Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C succ.tail).length =>
          succ =
            dartFromGeometricList C succ.tail i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) ∧
          next = dartFromGeometricList C succ.tail (i + 1) hi) := by
  have hsucc_tail : succ.tail = d.head := by
    rw [← hface]
    exact (geometricUnitDistanceRotationSystem C).faceSucc_tail_eq_head d
  have hleft' :
      graphDartArg (canonicalGeometricGraph C) d.head d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) d.head succ.head := by
    simpa [hsucc_tail, UnitDistanceDart.reverse_head] using hleft
  have leftRows :
      Exists fun i : Nat =>
        Exists fun hi : i + 1 < (geometricOutgoingDartList C d.head).length =>
          d.reverse =
            dartFromGeometricList C d.head i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) ∧
          succ = dartFromGeometricList C d.head (i + 1) hi :=
    geometricUnitDistanceRotationSystem_faceSucc_nonwrap_of_faceSucc_eq_graphDartArg_lt
      C d succ hface hleft'
  have hright' :
      graphDartArg (canonicalGeometricGraph C) succ.reverse.head
          succ.reverse.reverse.head <
        graphDartArg (canonicalGeometricGraph C) succ.reverse.head
          next.head := by
    simpa [UnitDistanceDart.reverse_head, UnitDistanceDart.reverse_tail]
      using hright
  have rightRows :
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C succ.reverse.head).length =>
          succ.reverse.reverse =
            dartFromGeometricList C succ.reverse.head i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) ∧
          next =
            dartFromGeometricList C succ.reverse.head (i + 1) hi :=
    geometricUnitDistanceRotationSystem_faceSucc_nonwrap_of_faceSucc_eq_graphDartArg_lt
      C succ.reverse next hnext hright'
  constructor
  · rcases leftRows with ⟨i, hi, hreverse, htarget⟩
    have hi' : i + 1 < (geometricOutgoingDartList C succ.tail).length := by
      rw [hsucc_tail]
      exact hi
    refine ⟨i, hi', ?_, ?_⟩
    · simpa [hsucc_tail] using hreverse
    · simpa [hsucc_tail] using htarget
  · rcases rightRows with ⟨i, hi, hcurrent, htarget⟩
    refine
      ⟨i,
        by
          simpa [UnitDistanceDart.reverse_head, UnitDistanceDart.reverse_tail]
            using hi,
        ?_, ?_⟩
    · simpa [UnitDistanceDart.reverse_head, UnitDistanceDart.reverse_tail]
        using hcurrent
    · simpa [UnitDistanceDart.reverse_head, UnitDistanceDart.reverse_tail]
        using htarget

set_option linter.style.longLine false in
/-- Selected-head face-successor source helper.

If an actual geometric `faceSucc` equality identifies the outgoing dart and
the selected heads are exactly the reverse-incoming head and successor head,
then a strict turn inequality for those selected heads reifies the same
non-wrap geometric neighbour-selection row.  The no-between payload is read
only for this selected sector by
`graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow`. -/
noncomputable def graphVertexGeometricAngularNeighborSelectionRow_of_faceSucc_eq_selected_strictTurn
    (C : _root_.UDConfig n) (center left right : Fin n)
    (d e : UnitDistanceDart C)
    (hcenter : d.head = center)
    (hleft : d.reverse.head = left)
    (hright : e.head = right)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (hturn :
      graphDartArg (canonicalGeometricGraph C) center left <
        graphDartArg (canonicalGeometricGraph C) center right) :
    GraphVertexGeometricAngularNeighborSelectionRow C center left right := by
  have hleft_tail : d.tail = left := by
    simpa [UnitDistanceDart.reverse_head] using hleft
  have hturn' :
      graphDartArg (canonicalGeometricGraph C) d.head d.reverse.head <
        graphDartArg (canonicalGeometricGraph C) d.head e.head := by
    simpa [hcenter, hleft_tail, hright, UnitDistanceDart.reverse_head]
      using hturn
  have row :
      GraphVertexGeometricAngularNeighborSelectionRow C d.head
        d.reverse.head e.head :=
    graphVertexGeometricAngularNeighborSelectionRow_of_geometricUnitDistanceRotationSystem_faceSucc_eq_graphDartArg_lt
      C d e hface hturn'
  simpa [hcenter, hleft_tail, hright, UnitDistanceDart.reverse_head] using row

set_option linter.style.longLine false in
/-- Selected-head face-successor source helper to honest angular no-between
rows.

This is the graph-vertex form of the selected exterior-sector bridge: an
actual geometric `faceSucc` step and the strict turn for exactly the selected
reverse-incoming and successor heads produce the local no-between row for that
same sector. -/
theorem graphVertexAngularNoBetweenRows_of_faceSucc_eq_selected_strictTurn
    (C : _root_.UDConfig n) (center left right : Fin n)
    (d e : UnitDistanceDart C)
    (hcenter : d.head = center)
    (hleft : d.reverse.head = left)
    (hright : e.head = right)
    (hface : (geometricUnitDistanceRotationSystem C).faceSucc d = e)
    (hturn :
      graphDartArg (canonicalGeometricGraph C) center left <
        graphDartArg (canonicalGeometricGraph C) center right) :
    GraphVertexAngularNoBetweenRows C center left right :=
  graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
    (graphVertexGeometricAngularNeighborSelectionRow_of_faceSucc_eq_selected_strictTurn
      C center left right d e hcenter hleft hright hface hturn)

set_option linter.style.longLine false in
/-- Raw-orbit predecessor/successor orientation inequalities select the
ordinary nonwrap branch of the actual geometric successor list rows.

The consecutive-list fact comes from the orbit's genuine geometric
`faceSucc`; the inequality only rules out the wrap branch. -/
theorem rawFaceSuccOrbit_geometricSuccessorNonwrapRows_of_orientationRows_20260521k18
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (orientationRows :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).reverse =
            dartFromGeometricList C (O.dart k).tail i
              (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
          O.dart k =
            dartFromGeometricList C (O.dart k).tail (i + 1) hi := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have hface_pred :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart pred) =
        O.dart k := by
    simp [pred, hsucc_pred]
  have hpred_head :
      (O.dart pred).head = (O.dart k).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_pred
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    simp [succ]
  have hcurrent_head :
      (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hconsecutive :
      geometricOutgoingDartListConsecutive C (O.dart k).tail
        (O.dart pred).reverse (O.dart k) := by
    have hraw :
        geometricOutgoingDartListConsecutive C (O.dart pred).head
          (O.dart pred).reverse (O.dart k) :=
      geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
        C (O.dart pred) (O.dart k) hface_pred
    simpa [pred, hpred_head] using hraw
  have hangle :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          ((O.dart pred).reverse).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head := by
    have hraw := orientationRows k
    simpa [pred, succ, UnitDistanceDart.reverse_head, hcurrent_head]
      using hraw
  exact
    geometricOutgoingDartListConsecutive_nonwrap_of_graphDartArg_lt
      C (O.dart k).tail (O.dart pred).reverse (O.dart k)
      hconsecutive hangle

set_option linter.style.longLine false in
/-- Raw-orbit strict orientation rows fill the explicit face-successor plus
nonwrap sorted-list source row.

The `faceSucc` equality is the actual geometric raw-orbit step, while the
nonwrap branch is selected from the genuine concrete outgoing-dart list by the
strict `graphDartArg` orientation inequality. -/
theorem rawFaceSuccOrbit_faceSuccGeometricNonwrapRows_of_orientationRows_20260521r33
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (orientationRows :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      let pred : Fin O.period :=
        PlanarInterface.cyclicPred O.period_pos k
      let succ : Fin O.period :=
        PlanarInterface.cyclicSucc O.period_pos k
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
          O.dart succ /\
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (O.dart k).tail).length =>
            (O.dart pred).reverse =
              dartFromGeometricList C (O.dart k).tail i
                (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
            O.dart k =
              dartFromGeometricList C (O.dart k).tail (i + 1) hi := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  refine ⟨?_, ?_⟩
  · simp
  · simpa [pred] using
      rawFaceSuccOrbit_geometricSuccessorNonwrapRows_of_orientationRows_20260521k18
        O orientationRows k

set_option linter.style.longLine false in
/-- Raw-orbit orientation inequalities produce the pointwise geometric
angular-neighbour selection rows needed by selected raw-orbit sources.

This combines the genuine geometric successor consecutive row with the
nonwrap branch selected by the strict `graphDartArg` inequality. -/
theorem rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_orientationRows_20260521k18
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (orientationRows :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C
          (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :=
  rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_geometricSuccessorNonwrapRows_20260521k18
    O
    (rawFaceSuccOrbit_geometricSuccessorNonwrapRows_of_orientationRows_20260521k18
      O orientationRows)

set_option linter.style.longLine false in
/-- Raw-orbit orientation rows produce honest angular no-between rows at the
same selected raw tails.

The no-between payload is still obtained from the actual geometric
`faceSucc`/sorted-list row selected by the orientation inequality, not from a
global outgoing-list assumption. -/
theorem rawFaceSuccOrbit_graphVertexAngularNoBetweenRows_of_orientationRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (orientationRows :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall k : Fin O.period,
      GraphVertexAngularNoBetweenRows C (O.dart k).tail
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail := by
  intro k
  rcases
      rawFaceSuccOrbit_geometricAngularNeighborSelectionRows_of_orientationRows_20260521k18
        O orientationRows k with
    ⟨row⟩
  exact graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
    row

set_option linter.style.longLine false in
/-- Raw-orbit local face-successor turn rows produce honest angular
no-between rows for the same predecessor/successor exterior sector.

This is the generic geometric-rotation helper behind
`SelectedRawOrbitGeometricFaceSuccTurnRows`: the input is the local turn
through the actual raw `faceSucc` passage, and endpoint chaining transports it
to the selected predecessor/successor tail sector. -/
theorem rawFaceSuccOrbit_graphVertexAngularNoBetweenRows_of_faceSuccTurnRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (turnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head) :
    forall k : Fin O.period,
      GraphVertexAngularNoBetweenRows C (O.dart k).tail
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail := by
  refine rawFaceSuccOrbit_graphVertexAngularNoBetweenRows_of_orientationRows
    O ?_
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    simp [succ]
  have hhead_succ :
      (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hturn :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          ((O.dart pred).reverse).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head := by
    simpa [pred] using turnRows k
  simpa [pred, succ, UnitDistanceDart.reverse_head, hhead_succ] using hturn

set_option linter.style.longLine false in
/-- Claim `S2-q15-geometric-orientation-source`.

Strict turns stated at the actual geometric `faceSucc` step of the predecessor
dart give exactly the raw predecessor-before-successor orientation row consumed
by the q13 raw-orbit exterior-sector eraser.

The `faceSucc` equalities used here are the genuine ones carried by the
geometric raw `faceSucc` orbit; the proof only transports endpoints from
`faceSucc (O.dart pred) = O.dart k` and `faceSucc (O.dart k) = O.dart succ`.
It does not introduce a global outgoing-list no-between premise. -/
theorem rawFaceSuccOrbit_orientationRows_of_actualFaceSucc_strictTurnRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (strictTurnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
            ((geometricUnitDistanceRotationSystem C).faceSucc
              (O.dart pred)).head) :
    forall k : Fin O.period,
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have hface_pred :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart pred) =
        O.dart k := by
    simp [pred, hsucc_pred]
  have hpred_head :
      (O.dart pred).head = (O.dart k).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_pred
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    simp [succ]
  have hcurrent_head :
      (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hturn :
      graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
          ((O.dart pred).reverse).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
          ((geometricUnitDistanceRotationSystem C).faceSucc
            (O.dart pred)).head := by
    simpa [pred] using strictTurnRows k
  simpa [pred, succ, UnitDistanceDart.reverse_head, hpred_head, hface_pred,
    hcurrent_head] using hturn

set_option linter.style.longLine false in
/-- Claim `S2-q42-geometric-orientation-worker`, explicit face-successor form.

Actual geometric `faceSucc` equalities at the selected raw darts, together
with the strict selected turn from predecessor reverse to current dart at the
same raw tail, give exactly the raw predecessor-before-successor orientation
row consumed downstream.  This is only endpoint transport through the genuine
geometric face-successor relation; it does not assume an all-outgoing
no-between row. -/
theorem S2_q42_geometric_orientation_worker_rawOrientation_of_faceSuccRows_strictSelectedTurns
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (faceSuccRows :
      forall k : Fin O.period,
        (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
          O.dart (PlanarInterface.cyclicSucc O.period_pos k))
    (strictTurnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head) :
    forall k : Fin O.period,
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let succ : Fin O.period := PlanarInterface.cyclicSucc O.period_pos k
  have hface_k :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k) =
        O.dart succ := by
    exact faceSuccRows k
  have hhead_succ :
      (O.dart k).head = (O.dart succ).tail :=
    (geometricUnitDistanceRotationSystem C).endpoint_chaining_of_faceSucc_eq_next
      hface_k
  have hturn :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          ((O.dart pred).reverse).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head := by
    simpa [pred] using strictTurnRows k
  simpa [pred, succ, UnitDistanceDart.reverse_head, hhead_succ] using hturn

set_option linter.style.longLine false in
/-- Claim `S2-q42-geometric-orientation-worker`, raw geometric orbit form.

For a live geometric `RawFaceSuccOrbit`, the actual face-successor equalities
are the orbit equations themselves, so strict selected turns immediately
produce the raw orientation row. -/
theorem S2_q42_geometric_orientation_worker_rawOrientation_of_rawFaceSuccOrbit_strictSelectedTurns
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (strictTurnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head) :
    forall k : Fin O.period,
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
  S2_q42_geometric_orientation_worker_rawOrientation_of_faceSuccRows_strictSelectedTurns
    O (fun k => by simp) strictTurnRows

set_option linter.style.longLine false in
/-- Claim `S2-q15-geometric-orientation-source`.

The same actual-`faceSucc` strict-turn rows also provide the selected raw
graph-vertex angular no-between rows by first producing the q13 raw orientation
row above and then using the existing orientation-to-selected-sector bridge. -/
theorem rawFaceSuccOrbit_graphVertexAngularNoBetweenRows_of_actualFaceSucc_strictTurnRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (strictTurnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart pred).head
            ((geometricUnitDistanceRotationSystem C).faceSucc
              (O.dart pred)).head) :
    forall k : Fin O.period,
      GraphVertexAngularNoBetweenRows C (O.dart k).tail
        (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail
        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail :=
  rawFaceSuccOrbit_graphVertexAngularNoBetweenRows_of_orientationRows
    O
    (rawFaceSuccOrbit_orientationRows_of_actualFaceSucc_strictTurnRows
      O strictTurnRows)

set_option linter.style.longLine false in
/-- Claim `S2-q80-selected-actual-carrier-angle-source`, raw-orbit geometric
angle core.

For the exact selected successor tail of a geometric raw face-successor orbit,
the selected actual-carrier angle row is just the two local strict turns:
the predecessor reverse-to-current turn at the raw dart, and the current-to-next
turn coming from the actual `faceSucc` of the reversed current dart.  This
bridge only transports the predecessor reverse head to the predecessor tail;
it introduces no global outgoing-list source or synthetic angular order. -/
theorem S2_q80_selected_actual_carrier_angle_source_rawFaceSuccOrbit_angleRows_of_faceSuccTurnRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (leftTurnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head)
    (rightTurnRows :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((geometricUnitDistanceRotationSystem C).faceSucc
              (O.dart k).reverse).head) :
    forall k : Fin O.period,
      let pred : Fin O.period :=
        PlanarInterface.cyclicPred O.period_pos k
      let next : UnitDistanceDart C :=
        (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k).reverse
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart pred).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head /\
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          next.head := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let next : UnitDistanceDart C :=
    (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k).reverse
  have hleftRaw :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          ((O.dart pred).reverse).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head := by
    simpa [pred] using leftTurnRows k
  have hleft :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart pred).tail <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head := by
    simpa [UnitDistanceDart.reverse_head] using hleftRaw
  have hright :
      graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          (O.dart k).head <
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
          next.head := by
    simpa [next] using rightTurnRows k
  exact And.intro hleft hright

set_option linter.style.longLine false in
/-- Non-wrap geometric-neighbour form of
`S2_q80_selected_actual_carrier_angle_source_rawFaceSuccOrbit_angleRows_of_faceSuccTurnRows`.

The two q80 strict turns select the actual non-wrap neighbouring rows around
the selected `faceSucc` head in the genuine geometric outgoing list. -/
theorem S2_q80_selected_actual_carrier_neighborRows_of_rawFaceSuccOrbit_faceSuccTurnRows
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start)
    (leftTurnRows :
      forall k : Fin O.period,
        let pred : Fin O.period :=
          PlanarInterface.cyclicPred O.period_pos k
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((O.dart pred).reverse).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head)
    (rightTurnRows :
      forall k : Fin O.period,
        graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            (O.dart k).head <
          graphDartArg (canonicalGeometricGraph C) (O.dart k).tail
            ((geometricUnitDistanceRotationSystem C).faceSucc
              (O.dart k).reverse).head) :
    forall k : Fin O.period,
      let pred : Fin O.period :=
        PlanarInterface.cyclicPred O.period_pos k
      let next : UnitDistanceDart C :=
        (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k).reverse
      Nonempty
          (GraphVertexGeometricAngularNeighborSelectionRow C
            (O.dart k).tail (O.dart pred).tail (O.dart k).head) /\
        Nonempty
          (GraphVertexGeometricAngularNeighborSelectionRow C
            (O.dart k).tail (O.dart k).head next.head) := by
  intro k
  let pred : Fin O.period := PlanarInterface.cyclicPred O.period_pos k
  let next : UnitDistanceDart C :=
    (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k).reverse
  have hsucc_pred : PlanarInterface.cyclicSucc O.period_pos pred = k := by
    simp [pred, PlanarInterface.cyclicSucc_cyclicPred O.period_pos k]
  have hface :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart pred) =
        O.dart k := by
    simp [pred, hsucc_pred]
  have hnext :
      (geometricUnitDistanceRotationSystem C).faceSucc (O.dart k).reverse =
        next := rfl
  have hangle :=
    S2_q80_selected_actual_carrier_angle_source_rawFaceSuccOrbit_angleRows_of_faceSuccTurnRows
      O leftTurnRows rightTurnRows k
  exact
    geometricUnitDistanceRotationSystem_successorTail_neighborSelectionRows_of_two_faceSucc_strictOrder
      C (O.dart pred) (O.dart k) next hface hnext hangle.1 hangle.2

set_option linter.style.longLine false in
/-- Every dart step in a geometric raw face-successor orbit is a genuine
consecutive pair of entries in the concrete sorted outgoing-dart list.

This keeps the wrap branch explicit through
`geometricOutgoingDartListConsecutive`; no identity rotation order or synthetic
cycle is introduced. -/
theorem rawFaceSuccOrbit_geometricOutgoingDartListConsecutive_of_faceSucc
    {C : _root_.UDConfig n} {start : UnitDistanceDart C}
    (O :
      UnitDistanceRotationSystem.RawFaceSuccOrbit
        (geometricUnitDistanceRotationSystem C) start) :
    forall k : Fin O.period,
      geometricOutgoingDartListConsecutive C (O.dart k).head
        (O.dart k).reverse
        (O.dart (PlanarInterface.cyclicSucc O.period_pos k)) := by
  intro k
  exact
    geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
      C (O.dart k) (O.dart (PlanarInterface.cyclicSucc O.period_pos k))
      (by simp)

/-- Local geometric evidence at one boundary step: at the shared boundary
vertex, the reverse incoming dart is immediately followed by the outgoing
boundary dart in the concrete geometric outgoing list, allowing cyclic
wrap-around. -/
def GeometricBoundarySuccessorRow
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) : Prop :=
  (Exists fun i : Nat =>
    Exists fun hi :
        i + 1 <
          (geometricOutgoingDartList C
            (B.vertex
              (PlanarInterface.cyclicSucc B.length_pos k))).length =>
      (UnitDistanceDart.ofBoundary B k).reverse =
        dartFromGeometricList C
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) i
          (Nat.lt_trans (Nat.lt_succ_self i) hi) /\
      UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicSucc B.length_pos k) =
        dartFromGeometricList C
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (i + 1) hi) \/
  Exists fun hpos :
      0 <
        (geometricOutgoingDartList C
          (B.vertex
            (PlanarInterface.cyclicSucc B.length_pos k))).length =>
    (UnitDistanceDart.ofBoundary B k).reverse =
      dartFromGeometricList C
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
        ((geometricOutgoingDartList C
          (B.vertex
            (PlanarInterface.cyclicSucc B.length_pos k))).length - 1)
        (Nat.sub_lt hpos Nat.zero_lt_one) /\
    UnitDistanceDart.ofBoundary B
        (PlanarInterface.cyclicSucc B.length_pos k) =
      dartFromGeometricList C
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) 0
        hpos

theorem geometricBoundarySuccessorRow_iff_consecutive
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) :
    GeometricBoundarySuccessorRow C B k ↔
      geometricOutgoingDartListConsecutive C
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
        (UnitDistanceDart.ofBoundary B k).reverse
        (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicSucc B.length_pos k)) :=
  Iff.rfl

theorem geometricBoundarySuccessorRow_of_no_graphDartArg_between
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (UnitDistanceDart.ofBoundary B k).reverse.head <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicSucc B.length_pos k)).head)
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other ->
        other ≠ (UnitDistanceDart.ofBoundary B k).reverse.head ->
        other ≠ (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicSucc B.length_pos k)).head ->
          ¬ (graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
                (UnitDistanceDart.ofBoundary B k).reverse.head <
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other ∧
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other <
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
                (UnitDistanceDart.ofBoundary B
                  (PlanarInterface.cyclicSucc B.length_pos k)).head)) :
    GeometricBoundarySuccessorRow C B k := by
  rw [geometricBoundarySuccessorRow_iff_consecutive]
  exact
    geometricOutgoingDartListConsecutive_of_no_graphDartArg_between
      C (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
      (UnitDistanceDart.ofBoundary B k).reverse
      (UnitDistanceDart.ofBoundary B
        (PlanarInterface.cyclicSucc B.length_pos k))
      (by simp)
      (by simp)
      hangle
      hno_between

/-- Wrap-around version of
`geometricBoundarySuccessorRow_of_no_graphDartArg_between`: when the successor
dart lies before the predecessor dart in principal-argument order, excluding
all incident neighbours in the cyclic branch interval gives the wrap-around
successor row. -/
theorem geometricBoundarySuccessorRow_of_no_graphDartArg_between_wrap
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicSucc B.length_pos k)).head <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (UnitDistanceDart.ofBoundary B k).reverse.head)
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other ->
        other ≠ (UnitDistanceDart.ofBoundary B k).reverse.head ->
        other ≠ (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicSucc B.length_pos k)).head ->
          ¬ (graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
                (UnitDistanceDart.ofBoundary B k).reverse.head <
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other ∨
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other <
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
                (UnitDistanceDart.ofBoundary B
                  (PlanarInterface.cyclicSucc B.length_pos k)).head)) :
    GeometricBoundarySuccessorRow C B k := by
  rw [geometricBoundarySuccessorRow_iff_consecutive]
  exact
    geometricOutgoingDartListConsecutive_of_no_graphDartArg_between_wrap
      C (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
      (UnitDistanceDart.ofBoundary B k).reverse
      (UnitDistanceDart.ofBoundary B
        (PlanarInterface.cyclicSucc B.length_pos k))
      (by simp)
      (by simp)
      hangle
      hno_between

/-- Geometric boundary successor rows for the whole concrete boundary cycle:
each boundary turn is witnessed by adjacent entries of the sorted geometric
outgoing list at the shared vertex. -/
def GeometricBoundarySuccessorRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) : Prop :=
  forall k : Fin B.length, GeometricBoundarySuccessorRow C B k

/-- Actual boundary face-successor rows for the genuine geometric rotation
system produce the concrete cyclic adjacency rows in the real sorted outgoing
dart lists. -/
theorem geometricBoundarySuccessorRows_of_geometricUnitDistanceCycleFaceSuccRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B) :
    GeometricBoundarySuccessorRows C B := by
  intro k
  rw [geometricBoundarySuccessorRow_iff_consecutive]
  exact
    geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
      C
      (UnitDistanceDart.ofBoundary B k)
      (UnitDistanceDart.ofBoundary B
        (PlanarInterface.cyclicSucc B.length_pos k))
      (faceSuccRows.faceSucc_eq_next k)

/-- At `B.vertex k`, the dart to `other` has graph angle strictly between the
predecessor and successor boundary darts. -/
abbrev BoundaryPredSuccAngularBetween
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) (other : Fin n) : Prop :=
  graphDartArg (canonicalGeometricGraph C)
      (B.vertex k)
      (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
    graphDartArg (canonicalGeometricGraph C) (B.vertex k) other ∧
  graphDartArg (canonicalGeometricGraph C) (B.vertex k) other <
    graphDartArg (canonicalGeometricGraph C)
      (B.vertex k)
      (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))

/-- Branch-cut version of `BoundaryPredSuccAngularBetween`: at `B.vertex k`,
`other` lies in the cyclic interval from predecessor to successor when that
interval crosses the principal-argument cut. -/
abbrev BoundaryPredSuccAngularBetweenWrap
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) (other : Fin n) : Prop :=
  graphDartArg (canonicalGeometricGraph C)
      (B.vertex k)
      (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
    graphDartArg (canonicalGeometricGraph C) (B.vertex k) other ∨
  graphDartArg (canonicalGeometricGraph C) (B.vertex k) other <
    graphDartArg (canonicalGeometricGraph C)
      (B.vertex k)
      (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))

/-- Honest angular sector data at one concrete boundary vertex.  This is the
geometric payload carried by the exterior-sector source rows: the predecessor
dart is strictly before the successor dart in principal-argument order, and no
third incident unit-distance dart lies in that open sector. -/
structure BoundaryVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) where
  angle :
    graphDartArg (canonicalGeometricGraph C)
        (B.vertex k)
        (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
      graphDartArg (canonicalGeometricGraph C)
        (B.vertex k)
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
  no_between :
    forall other : Fin n,
      GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
      other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
      other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
        Not (BoundaryPredSuccAngularBetween C B k other)

/-- Ordinary, non-wrap predecessor/successor adjacency in the concrete
geometric rotation list at boundary vertex `B.vertex k`.

The first listed dart is the reverse incoming predecessor boundary dart and
the second listed dart is the outgoing successor boundary dart.  This is the
geometric source row for the ordinary `pred < succ` angular branch. -/
def BoundaryVertexGeometricRotationOrderRow
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) : Prop :=
  Exists fun i : Nat =>
    Exists fun hi :
        i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
      (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicPred B.length_pos k)).reverse =
        dartFromGeometricList C (B.vertex k) i
          (Nat.lt_trans (Nat.lt_succ_self i) hi) ∧
      UnitDistanceDart.ofBoundary B k =
        dartFromGeometricList C (B.vertex k) (i + 1) hi

/-- A genuine non-wrap neighbour-selection row in the sorted outgoing-dart
list at the boundary vertex is exactly the boundary geometric rotation-order
row consumed by the S2 actual-boundary orientation source. -/
theorem boundaryVertexGeometricRotationOrderRow_of_graphVertexGeometricAngularNeighborSelectionRow
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (row :
      GraphVertexGeometricAngularNeighborSelectionRow C (B.vertex k)
        (B.vertex (PlanarInterface.cyclicPred B.length_pos k))
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    BoundaryVertexGeometricRotationOrderRow C B k := by
  let pred := PlanarInterface.cyclicPred B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  rcases row with ⟨i, hi, hpred_head, hsucc_head⟩
  refine ⟨i, hi, ?_, ?_⟩
  · apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair, dartFromGeometricList,
      pred, hsucc_pred, hpred_head]
  · apply UnitDistanceDart.endpointPair_injective
    simp [UnitDistanceDart.endpointPair, dartFromGeometricList, hsucc_head]

/-- Family form of
`boundaryVertexGeometricRotationOrderRow_of_graphVertexGeometricAngularNeighborSelectionRow`.
This is the strict reducer from pointwise sorted outgoing-dart neighbour rows
to the `BoundaryVertexGeometricRotationOrderRow` family required by the S2
actual-boundary face-successor/orientation source. -/
theorem boundaryVertexGeometricRotationOrderRows_of_graphVertexGeometricAngularNeighborSelectionRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length,
        GraphVertexGeometricAngularNeighborSelectionRow C (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k))
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k := by
  intro k
  exact
    boundaryVertexGeometricRotationOrderRow_of_graphVertexGeometricAngularNeighborSelectionRow
      C B k (rows k)

set_option linter.style.longLine false in
/-- Direct pointwise source from the actual adjacent entries of the sorted
`geometricOutgoingDartList`.

The hypotheses identify the two neighbouring concrete list darts themselves:
the reverse incoming predecessor boundary dart is followed immediately by the
outgoing successor boundary dart.  This is only a transport from the genuine
geometric list entries to the boundary-vertex row format; it introduces no
identity cyclic order or synthetic angular order. -/
theorem boundaryVertexGeometricRotationOrderRow_of_geometricOutgoingDartList_getElem
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (i : Nat)
    (hi : i + 1 < (geometricOutgoingDartList C (B.vertex k)).length)
    (hpred :
      ((geometricOutgoingDartList C (B.vertex k))[i]'
          (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
        (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicPred B.length_pos k)).reverse)
    (hsucc :
      ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
        UnitDistanceDart.ofBoundary B k) :
    BoundaryVertexGeometricRotationOrderRow C B k := by
  refine ⟨i, hi, ?_, ?_⟩
  · have hget :
        dartFromGeometricList C (B.vertex k) i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) =
          ((geometricOutgoingDartList C (B.vertex k))[i]'
            (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 := by
      exact
        congrArg
          (fun d : OutgoingUnitDistanceDart C (B.vertex k) => d.1)
          (dartFromGeometricList_outgoing C (B.vertex k) i
            (Nat.lt_trans (Nat.lt_succ_self i) hi))
    exact (hget.trans hpred).symm
  · have hget :
        dartFromGeometricList C (B.vertex k) (i + 1) hi =
          ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 := by
      exact
        congrArg
          (fun d : OutgoingUnitDistanceDart C (B.vertex k) => d.1)
          (dartFromGeometricList_outgoing C (B.vertex k) (i + 1) hi)
    exact (hget.trans hsucc).symm

set_option linter.style.longLine false in
/-- Family version of
`boundaryVertexGeometricRotationOrderRow_of_geometricOutgoingDartList_getElem`.

The source is a real adjacent-index row in `geometricOutgoingDartList` at
every boundary vertex. -/
theorem boundaryVertexGeometricRotationOrderRows_of_geometricOutgoingDartList_getElemRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
            ((geometricOutgoingDartList C (B.vertex k))[i]'
                (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
              (UnitDistanceDart.ofBoundary B
                (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
            ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
              UnitDistanceDart.ofBoundary B k) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k := by
  intro k
  rcases rows k with ⟨i, hi, hpred, hsucc⟩
  exact
    boundaryVertexGeometricRotationOrderRow_of_geometricOutgoingDartList_getElem
      C B k i hi hpred hsucc

set_option linter.style.longLine false in
/-- A boundary geometric rotation-order row is equivalent to the displayed
adjacent-entry row in the actual sorted `geometricOutgoingDartList`.

This is the converse transport to
`boundaryVertexGeometricRotationOrderRow_of_geometricOutgoingDartList_getElem`:
it opens the `dartFromGeometricList` witnesses and recovers the concrete
list entries themselves. -/
theorem geometricOutgoingDartList_getElemRows_of_boundaryVertexGeometricRotationOrderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hrows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    forall k : Fin B.length,
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
          ((geometricOutgoingDartList C (B.vertex k))[i]'
              (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
            (UnitDistanceDart.ofBoundary B
              (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
          ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
            UnitDistanceDart.ofBoundary B k := by
  intro k
  rcases hrows k with ⟨i, hi, hpred, hsucc⟩
  refine ⟨i, hi, ?_, ?_⟩
  · have hget :
        dartFromGeometricList C (B.vertex k) i
            (Nat.lt_trans (Nat.lt_succ_self i) hi) =
          ((geometricOutgoingDartList C (B.vertex k))[i]'
            (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 := by
      exact
        congrArg
          (fun d : OutgoingUnitDistanceDart C (B.vertex k) => d.1)
          (dartFromGeometricList_outgoing C (B.vertex k) i
            (Nat.lt_trans (Nat.lt_succ_self i) hi))
    exact (hpred.trans hget).symm
  · have hget :
        dartFromGeometricList C (B.vertex k) (i + 1) hi =
          ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 := by
      exact
        congrArg
          (fun d : OutgoingUnitDistanceDart C (B.vertex k) => d.1)
          (dartFromGeometricList_outgoing C (B.vertex k) (i + 1) hi)
    exact (hsucc.trans hget).symm

set_option linter.style.longLine false in
/-- An honest boundary-vertex angular no-between row already forces the
predecessor/successor darts to be consecutive in the actual sorted geometric
outgoing list.

This is the direct source reducer for the ordinary boundary geometric order
row: it uses the real incident boundary darts and the concrete
`geometricOutgoingDartList`, with no identity cyclic order or synthetic row. -/
theorem boundaryVertexGeometricRotationOrderRow_of_boundaryVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (rows : BoundaryVertexAngularNoBetweenRows C B k) :
    BoundaryVertexGeometricRotationOrderRow C B k := by
  let pred := PlanarInterface.cyclicPred B.length_pos k
  let succ := PlanarInterface.cyclicSucc B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hleft_adj :
      GraphBridge.UnitDistanceAdj C (B.vertex k) (B.vertex pred) := by
    have hsimple :
        (GraphBridge.unitDistanceSimpleGraph C).Adj
          (B.vertex k) (B.vertex pred) := by
      simpa [pred, hsucc_pred] using
        ((UnitDistanceDart.ofBoundary B pred).reverse).adj
    exact (GraphBridge.unitDistanceSimpleGraph_adj C _ _).1 hsimple
  have hright_adj :
      GraphBridge.UnitDistanceAdj C (B.vertex k) (B.vertex succ) := by
    have hsimple :
        (GraphBridge.unitDistanceSimpleGraph C).Adj
          (B.vertex k) (B.vertex succ) := by
      simpa [succ] using (UnitDistanceDart.ofBoundary B k).adj
    exact (GraphBridge.unitDistanceSimpleGraph_adj C _ _).1 hsimple
  let graphRows :
      GraphVertexAngularNoBetweenRows C (B.vertex k)
        (B.vertex pred) (B.vertex succ) :=
    { angle := by
        simpa [pred, succ] using rows.angle
      no_between := by
        intro other hAdj hother_pred hother_succ hbetween
        exact
          rows.no_between other hAdj
            (by simpa [pred] using hother_pred)
            (by simpa [succ] using hother_succ)
            (by
              simpa [BoundaryPredSuccAngularBetween,
                GraphVertexAngularBetween, pred, succ] using hbetween) }
  have hrow_nonempty :
      Nonempty
        (GraphVertexGeometricAngularNeighborSelectionRow C (B.vertex k)
          (B.vertex pred) (B.vertex succ)) :=
    exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
      hleft_adj hright_adj graphRows
  exact
    boundaryVertexGeometricRotationOrderRow_of_graphVertexGeometricAngularNeighborSelectionRow
      C B k (Classical.choice hrow_nonempty)

set_option linter.style.longLine false in
/-- Family form of
`boundaryVertexGeometricRotationOrderRow_of_boundaryVertexAngularNoBetweenRows`. -/
theorem boundaryVertexGeometricRotationOrderRows_of_boundaryVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k := by
  intro k
  exact
    boundaryVertexGeometricRotationOrderRow_of_boundaryVertexAngularNoBetweenRows
      C B k (rows k)

set_option linter.style.longLine false in
/-- Honest angular no-between rows at the boundary vertices supply the exact
pointwise adjacent-entry rows consumed by
`S2_agent_geometric_boundary_successor_20260520e_of_geometricOutgoingDartList_orderRows`.

The conclusion is stated directly over `geometricOutgoingDartList` entries,
while the proof goes through the checked `dartFromGeometricList` boundary
rotation-order row. -/
theorem geometricOutgoingDartList_getElemRows_of_boundaryVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k) :
    forall k : Fin B.length,
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
          ((geometricOutgoingDartList C (B.vertex k))[i]'
              (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
            (UnitDistanceDart.ofBoundary B
              (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
          ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
            UnitDistanceDart.ofBoundary B k :=
  geometricOutgoingDartList_getElemRows_of_boundaryVertexGeometricRotationOrderRows
    C B
    (boundaryVertexGeometricRotationOrderRows_of_boundaryVertexAngularNoBetweenRows
      C B rows)

set_option linter.style.longLine false in
/-- Claim `S2-agent-boundary-geometric-list-order-source-20260520f`.

This is the strict source reduction for the pointwise list-order rows required
by the 20260520e geometric-boundary successor consumer.  The leaf is now the
honest same-boundary `BoundaryVertexAngularNoBetweenRows` family, and the
produced rows are the actual adjacent `getElem` entries of
`geometricOutgoingDartList`. -/
theorem S2_agent_boundary_geometric_list_order_source_20260520f_of_boundaryVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k) :
    forall k : Fin B.length,
      Exists fun i : Nat =>
        Exists fun hi :
            i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
          ((geometricOutgoingDartList C (B.vertex k))[i]'
              (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
            (UnitDistanceDart.ofBoundary B
              (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
          ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
            UnitDistanceDart.ofBoundary B k :=
  geometricOutgoingDartList_getElemRows_of_boundaryVertexAngularNoBetweenRows
    C B rows

set_option linter.style.longLine false in
/-- Raw predicate form of
`boundaryVertexGeometricRotationOrderRows_of_boundaryVertexAngularNoBetweenRows`.

For the exterior-boundary route, the only geometric source needed at each
boundary vertex is the ordinary predecessor-before-successor argument
inequality plus the honest no-between exclusion against actual incident
unit-distance neighbours.  The conclusion is still the concrete consecutive
row in `geometricOutgoingDartList`. -/
theorem boundaryVertexGeometricRotationOrderRows_of_pred_succ_no_between
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hangle :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)))
    (hno_between :
      forall (k : Fin B.length) (other : Fin n),
        GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
        other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
        other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
          Not (BoundaryPredSuccAngularBetween C B k other)) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k := by
  refine
    boundaryVertexGeometricRotationOrderRows_of_boundaryVertexAngularNoBetweenRows
      C B ?_
  intro k
  exact
    { angle := hangle k
      no_between := hno_between k }

/-- Claim `S2-codex-current-20260520-boundary-geometric-order-source`.

Once an actual exterior boundary route has supplied the honest angular
no-between rows at the boundary vertices, the desired geometric boundary-order
rows follow directly from the real sorted outgoing-dart lists.  This wrapper
does not require a pre-existing geometric face-successor row: the selected
predecessor/successor darts are recovered as consecutive entries of
`geometricOutgoingDartList`. -/
theorem S2_codex_current_20260520_boundary_geometric_order_source
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (angularRows :
      forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k :=
  boundaryVertexGeometricRotationOrderRows_of_boundaryVertexAngularNoBetweenRows
    C B angularRows

/-- The wrap-around alternative to
`BoundaryVertexGeometricRotationOrderRow`: the reverse incoming predecessor
dart is the last entry of the sorted geometric list and the outgoing boundary
dart is the first entry. -/
def BoundaryVertexGeometricRotationWrapRow
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) : Prop :=
  Exists fun hpos : 0 < (geometricOutgoingDartList C (B.vertex k)).length =>
    (UnitDistanceDart.ofBoundary B
        (PlanarInterface.cyclicPred B.length_pos k)).reverse =
      dartFromGeometricList C (B.vertex k)
        ((geometricOutgoingDartList C (B.vertex k)).length - 1)
        (Nat.sub_lt hpos Nat.zero_lt_one) ∧
    UnitDistanceDart.ofBoundary B k =
      dartFromGeometricList C (B.vertex k) 0 hpos

/-- Exact branch split obtained from actual geometric boundary face-successor
rows at one boundary vertex.  The first branch is the desired ordinary
geometric order row; the second is the sole remaining wrap-around residual. -/
theorem boundaryVertexGeometricRotationOrderRow_or_wrapRow_of_faceSuccRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (k : Fin B.length) :
    BoundaryVertexGeometricRotationOrderRow C B k ∨
      BoundaryVertexGeometricRotationWrapRow C B k := by
  let pred := PlanarInterface.cyclicPred B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hface :
      (geometricUnitDistanceRotationSystem C).faceSucc
          (UnitDistanceDart.ofBoundary B pred) =
        UnitDistanceDart.ofBoundary B k := by
    simpa [pred, hsucc_pred] using faceSuccRows.faceSucc_eq_next pred
  have hconsecutive :=
    geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
      C (UnitDistanceDart.ofBoundary B pred)
      (UnitDistanceDart.ofBoundary B k) hface
  have hconsecutive' :
      geometricOutgoingDartListConsecutive C (B.vertex k)
        (UnitDistanceDart.ofBoundary B pred).reverse
        (UnitDistanceDart.ofBoundary B k) := by
    simpa [pred, hsucc_pred] using hconsecutive
  simpa [BoundaryVertexGeometricRotationOrderRow,
    BoundaryVertexGeometricRotationWrapRow, geometricOutgoingDartListConsecutive,
    pred] using hconsecutive'

/-- Family branch split from the actual geometric boundary face-successor
rows. -/
theorem boundaryVertexGeometricRotationOrderRows_or_wrapRows_of_faceSuccRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k ∨
        BoundaryVertexGeometricRotationWrapRow C B k := by
  intro k
  exact
    boundaryVertexGeometricRotationOrderRow_or_wrapRow_of_faceSuccRows
      C B faceSuccRows k

set_option linter.style.longLine false in
/-- Pointwise S2-k6m source: genuine geometric face-successor rows for the same
boundary, together with the exterior raw-orbit orientation inequality at this
boundary vertex, give the ordinary non-wrap geometric rotation-order row.

The face-successor row supplies the actual consecutive entries of
`geometricOutgoingDartList`; the angle inequality only selects the non-wrap
branch. -/
theorem boundaryVertexGeometricRotationOrderRow_of_faceSuccRows_pred_arg_lt_succ_arg
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    BoundaryVertexGeometricRotationOrderRow C B k := by
  let pred := PlanarInterface.cyclicPred B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hface :
      (geometricUnitDistanceRotationSystem C).faceSucc
          (UnitDistanceDart.ofBoundary B pred) =
        UnitDistanceDart.ofBoundary B k := by
    simpa [pred, hsucc_pred] using faceSuccRows.faceSucc_eq_next pred
  have hconsecutive :
      geometricOutgoingDartListConsecutive C (B.vertex k)
        (UnitDistanceDart.ofBoundary B pred).reverse
        (UnitDistanceDart.ofBoundary B k) := by
    have hraw :
        geometricOutgoingDartListConsecutive C
          (UnitDistanceDart.ofBoundary B pred).head
          (UnitDistanceDart.ofBoundary B pred).reverse
          (UnitDistanceDart.ofBoundary B k) :=
      geometricOutgoingDartListConsecutive_of_geometricUnitDistanceRotationSystem_faceSucc_eq
        C (UnitDistanceDart.ofBoundary B pred)
        (UnitDistanceDart.ofBoundary B k) hface
    simpa [pred, hsucc_pred] using hraw
  have hangle' :
      graphDartArg (canonicalGeometricGraph C) (B.vertex k)
          (UnitDistanceDart.ofBoundary B pred).reverse.head <
        graphDartArg (canonicalGeometricGraph C) (B.vertex k)
          (UnitDistanceDart.ofBoundary B k).head := by
    simpa [pred, hsucc_pred] using hangle
  rcases
      geometricOutgoingDartListConsecutive_nonwrap_of_graphDartArg_lt
        C (B.vertex k)
        (UnitDistanceDart.ofBoundary B pred).reverse
        (UnitDistanceDart.ofBoundary B k) hconsecutive hangle' with
    ⟨i, hi, hpred, hsucc⟩
  exact ⟨i, hi, hpred, hsucc⟩

set_option linter.style.longLine false in
/-- Claim `S2-k6m-boundary-geometric-order-source`.

Family form of the pointwise k6m source.  The only geometric inputs are the
actual face-successor rows for the same boundary and the exterior raw-orbit
orientation inequality transported to that boundary. -/
theorem S2_k6m_boundary_geometric_order_source_of_faceSuccRows_orientation
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (hangle :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k := by
  intro k
  exact
    boundaryVertexGeometricRotationOrderRow_of_faceSuccRows_pred_arg_lt_succ_arg
      C B faceSuccRows k (hangle k)

/-- Claim `S2-agent-geometric-boundary-order-source`.

Actual boundary face-successor rows for the genuine sorted geometric rotation
system reduce the ordinary boundary-order source to excluding the explicit
wrap-around branch at each actual boundary vertex. -/
theorem S2_agent_geometric_boundary_order_source
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (nonwrap :
      forall k : Fin B.length,
        Not (BoundaryVertexGeometricRotationWrapRow C B k)) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k := by
  intro k
  rcases
    boundaryVertexGeometricRotationOrderRow_or_wrapRow_of_faceSuccRows
      C B faceSuccRows k with horder | hwrap
  · exact horder
  · exact False.elim ((nonwrap k) hwrap)

/-- An ordinary predecessor-before-successor angular inequality at the
boundary vertex rules out the wrap-around geometric rotation row.

This is the checked geometric replacement for the residual `nonwrap`
hypothesis in `S2_agent_geometric_boundary_order_source`: the only remaining
source row is the concrete principal-argument inequality for the chosen
exterior boundary orientation. -/
theorem boundaryVertexGeometricRotationWrapRow_not_of_pred_arg_lt_succ_arg
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    Not (BoundaryVertexGeometricRotationWrapRow C B k) := by
  classical
  intro hwrap
  rcases hwrap with ⟨hpos, hpred, hsucc⟩
  let center : Fin n := B.vertex k
  let L := geometricOutgoingDartList C center
  have hpred_head :
      (L[L.length - 1]'(by simpa [L, center] using
          (Nat.sub_lt hpos Nat.zero_lt_one))).1.head =
        B.vertex (PlanarInterface.cyclicPred B.length_pos k) := by
    have hhead := congrArg UnitDistanceDart.head hpred
    symm
    simpa [L, center, dartFromGeometricList_head] using hhead
  have hsucc_head :
      (L[0]'(by simpa [L, center] using hpos)).1.head =
        B.vertex (PlanarInterface.cyclicSucc B.length_pos k) := by
    have hhead := congrArg UnitDistanceDart.head hsucc
    symm
    simpa [L, center, dartFromGeometricList_head] using hhead
  have hlen_ne_one : L.length ≠ 1 := by
    intro hlen_one
    have hlast_zero : L.length - 1 = 0 := by omega
    have hsame :
        B.vertex (PlanarInterface.cyclicPred B.length_pos k) =
          B.vertex (PlanarInterface.cyclicSucc B.length_pos k) := by
      rw [← hpred_head, ← hsucc_head]
      simp [hlast_zero]
    have hangle_self :
        graphDartArg (canonicalGeometricGraph C) (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C) (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) := by
      simp [hsame] at hangle
    exact (lt_irrefl _ hangle_self)
  have hzero_lt_last : 0 < L.length - 1 := by
    have hposL : 0 < L.length := by simpa [L, center] using hpos
    omega
  have hlast_lt : L.length - 1 < L.length := by
    have hposL : 0 < L.length := by simpa [L, center] using hpos
    omega
  have hwrap_angle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) := by
    have hrel :=
      (geometricOutgoingDartList_pairwise_graphDartArg_lt C center).rel_get_of_lt
        (a := ⟨0, by simpa [L, center] using hpos⟩)
        (b := ⟨L.length - 1, hlast_lt⟩)
        hzero_lt_last
    simpa [L, center, hsucc_head, hpred_head] using hrel
  exact (lt_asymm hangle hwrap_angle)

/-- Actual geometric face-successor rows plus the explicit ordinary angular
orientation at every boundary vertex give the desired ordinary geometric
rotation order rows, with no arbitrary order-assumption row left over. -/
theorem S2_agent_geometric_boundary_order_source_of_pred_arg_lt_succ_arg
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (hangle :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k :=
  S2_agent_geometric_boundary_order_source C B faceSuccRows
    (fun k =>
      boundaryVertexGeometricRotationWrapRow_not_of_pred_arg_lt_succ_arg
        C B k (hangle k))

/-- Actual geometric face-successor rows plus named angular no-between rows
give the ordinary geometric rotation order rows.

This is the checked reducer that removes the naked
`pred_arg_lt_succ_arg` residual from callers: the angular inequality is now
read from the concrete predecessor/successor sector row, which exterior
boundary sources can provide together with their no-between payload. -/
theorem S2_agent_geometric_boundary_order_source_of_boundaryVertexAngularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (angularRows :
      forall k : Fin B.length,
        BoundaryVertexAngularNoBetweenRows C B k) :
    forall k : Fin B.length,
      BoundaryVertexGeometricRotationOrderRow C B k :=
  S2_agent_geometric_boundary_order_source_of_pred_arg_lt_succ_arg
    C B faceSuccRows (fun k => (angularRows k).angle)

/-- One ordinary adjacent predecessor/successor row in the actual geometric
rotation list supplies the strict angular inequality and the no-between row
at that boundary vertex. -/
theorem boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hrow : BoundaryVertexGeometricRotationOrderRow C B k) :
    BoundaryVertexAngularNoBetweenRows C B k := by
  classical
  rcases hrow with ⟨i, hi, hpred, hsucc⟩
  let center : Fin n := B.vertex k
  let L := geometricOutgoingDartList C center
  let first : OutgoingUnitDistanceDart C center :=
    L[i]'(Nat.lt_trans (Nat.lt_succ_self i) hi)
  let second : OutgoingUnitDistanceDart C center := L[i + 1]'hi
  have hfirst_head :
      first.1.head =
        B.vertex (PlanarInterface.cyclicPred B.length_pos k) := by
    have hhead := congrArg UnitDistanceDart.head hpred
    symm
    simpa [first, L, center, dartFromGeometricList_head] using hhead
  have hsecond_head :
      second.1.head =
        B.vertex (PlanarInterface.cyclicSucc B.length_pos k) := by
    have hhead := congrArg UnitDistanceDart.head hsucc
    symm
    simpa [second, L, center, dartFromGeometricList_head] using hhead
  have hangle_list :
      graphDartArg (canonicalGeometricGraph C) center first.1.head <
        graphDartArg (canonicalGeometricGraph C) center second.1.head := by
    have hrel :=
      (geometricOutgoingDartList_pairwise_graphDartArg_lt C center).rel_get_of_lt
        (a := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
        (b := ⟨i + 1, hi⟩)
        (by simp)
    simpa [first, second, L]
      using hrel
  refine
    { angle := by
        simpa [center, hfirst_head, hsecond_head] using hangle_list
      no_between := ?_ }
  intro other hAdj hother_pred hother_succ hbetween
  let otherDart : UnitDistanceDart C := {
    tail := center
    head := other
    adj :=
      (GraphBridge.unitDistanceSimpleGraph_adj C center other).2
        (by simpa [center] using hAdj) }
  let otherOutgoing : OutgoingUnitDistanceDart C center := ⟨otherDart, rfl⟩
  have hother_mem : otherOutgoing ∈ L := by
    simpa [L] using mem_geometricOutgoingDartList C center otherOutgoing
  have hother_ne_first : otherOutgoing ≠ first := by
    intro h
    have hhead : other = first.1.head := by
      exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) h
    exact hother_pred (by simpa [hfirst_head] using hhead)
  have hother_ne_second : otherOutgoing ≠ second := by
    intro h
    have hhead : other = second.1.head := by
      exact congrArg (fun d : OutgoingUnitDistanceDart C center => d.1.head) h
    exact hother_succ (by simpa [hsecond_head] using hhead)
  have hno_list :
      ∀ other' ∈ L, other' ≠ first -> other' ≠ second ->
        ¬ (graphDartArg (canonicalGeometricGraph C) center first.1.head <
              graphDartArg (canonicalGeometricGraph C) center other'.1.head ∧
            graphDartArg (canonicalGeometricGraph C) center other'.1.head <
              graphDartArg (canonicalGeometricGraph C) center second.1.head) := by
    simpa [first, second, L] using
      List.no_between_of_getElem_succ_pairwise_real_lt
        (xs := L)
        (weight := fun outgoing : OutgoingUnitDistanceDart C center =>
          graphDartArg (canonicalGeometricGraph C) center outgoing.1.head)
        (hsorted := geometricOutgoingDartList_pairwise_graphDartArg_lt C center)
        i hi rfl rfl
  exact
    hno_list otherOutgoing hother_mem hother_ne_first hother_ne_second
      (by
        simpa [BoundaryPredSuccAngularBetween, center, otherOutgoing, otherDart,
          hfirst_head, hsecond_head] using hbetween)

set_option linter.style.longLine false in
/-- Pointwise boundary source helper for the selected exterior sector.

An actual geometric `faceSucc` equality from the predecessor boundary dart to
the current boundary dart, together with the strict predecessor-before-
successor turn at `B.vertex k`, reifies the corresponding graph-vertex
geometric neighbour-selection row for exactly those selected heads. -/
noncomputable def boundaryVertexGeometricAngularNeighborSelectionRow_of_faceSucc_eq_strictTurn
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hface :
      (geometricUnitDistanceRotationSystem C).faceSucc
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicPred B.length_pos k)) =
        UnitDistanceDart.ofBoundary B k)
    (hturn :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    GraphVertexGeometricAngularNeighborSelectionRow C (B.vertex k)
      (B.vertex (PlanarInterface.cyclicPred B.length_pos k))
      (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) := by
  let pred := PlanarInterface.cyclicPred B.length_pos k
  let succ := PlanarInterface.cyclicSucc B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  exact
    graphVertexGeometricAngularNeighborSelectionRow_of_faceSucc_eq_selected_strictTurn
      C (B.vertex k) (B.vertex pred) (B.vertex succ)
      (UnitDistanceDart.ofBoundary B pred) (UnitDistanceDart.ofBoundary B k)
      (by simp [pred, hsucc_pred])
      (by simp [pred])
      (by simp [succ])
      (by simpa [pred] using hface)
      (by simpa [pred, succ] using hturn)

set_option linter.style.longLine false in
/-- Pointwise boundary source helper to honest angular no-between rows.

The only no-between row produced is the one for the chosen exterior sector
from predecessor to successor at `B.vertex k`; it is recovered from the actual
geometric `faceSucc` step and the strict turn selecting the non-wrap branch. -/
theorem boundaryVertexAngularNoBetweenRows_of_faceSucc_eq_strictTurn
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hface :
      (geometricUnitDistanceRotationSystem C).faceSucc
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicPred B.length_pos k)) =
        UnitDistanceDart.ofBoundary B k)
    (hturn :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    BoundaryVertexAngularNoBetweenRows C B k := by
  exact
    boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow
      C B k
      (boundaryVertexGeometricRotationOrderRow_of_graphVertexGeometricAngularNeighborSelectionRow
      C B k
      (boundaryVertexGeometricAngularNeighborSelectionRow_of_faceSucc_eq_strictTurn
        C B k hface hturn))

set_option linter.style.longLine false in
/-- Source-level same-boundary angular rows from genuine geometric
face-successor data.

For each selected exterior sector at `B.vertex k`, the only assumptions are the
actual geometric `faceSucc` equality from the predecessor boundary dart to the
current boundary dart and the strict predecessor-before-successor turn at that
same vertex.  No global outgoing-list no-between premise is used. -/
theorem boundaryVertexAngularNoBetweenRows_of_actual_faceSuccRows_strictTurnRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      forall k : Fin B.length,
        (geometricUnitDistanceRotationSystem C).faceSucc
            (UnitDistanceDart.ofBoundary B
              (PlanarInterface.cyclicPred B.length_pos k)) =
          UnitDistanceDart.ofBoundary B k)
    (strictTurnRows :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexAngularNoBetweenRows C B k := by
  intro k
  exact
    boundaryVertexAngularNoBetweenRows_of_faceSucc_eq_strictTurn
      C B k (faceSuccRows k) (strictTurnRows k)

/-- Family form of
`boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow`. -/
theorem boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hrows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k := by
  intro k
  exact boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow
    C B k (hrows k)

set_option linter.style.longLine false in
/-- At a fixed boundary vertex, the honest angular no-between row is equivalent
to the ordinary non-wrap geometric rotation-order row for the same concrete
boundary cycle.

Both directions are routed through the genuine sorted
`geometricOutgoingDartList`: angular rows force adjacent list entries, while
an adjacent list row recovers the strict `graphDartArg` no-between sector. -/
theorem boundaryVertexAngularNoBetweenRows_iff_boundaryVertexGeometricRotationOrderRow
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length) :
    BoundaryVertexAngularNoBetweenRows C B k ↔
      BoundaryVertexGeometricRotationOrderRow C B k := by
  constructor
  · intro rows
    exact boundaryVertexGeometricRotationOrderRow_of_boundaryVertexAngularNoBetweenRows
      C B k rows
  · intro hrow
    exact boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow
      C B k hrow

set_option linter.style.longLine false in
/-- Same-boundary family equivalence between the angular no-between source and
the concrete geometric rotation-order source.

The forward direction is exactly
`S2_codex_current_20260520_boundary_geometric_order_source`; the reverse
direction reads the angular sector back from adjacent entries of the real
`geometricOutgoingDartList`. -/
theorem S2_codex_current_20260520_same_boundary_angular_geometric_order_source_iff
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C) :
    (forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k) ↔
      (forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) := by
  constructor
  · intro angularRows
    exact
      S2_codex_current_20260520_boundary_geometric_order_source
        C B angularRows
  · intro geometricOrderRows
    exact
      boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
        C B geometricOrderRows

set_option linter.style.longLine false in
/-- Reverse source eraser for the same concrete boundary cycle: non-wrap
geometric rotation-order rows source the angular no-between rows consumed by
the exterior-sector package builders. -/
theorem S2_codex_current_20260520_same_boundary_angular_no_between_source
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (geometricOrderRows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k :=
  boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
    C B geometricOrderRows

/-- Geometric face-successor rows plus the ordinary nonwrap
predecessor/successor orientation supply the reusable angular no-between rows
at every boundary vertex. -/
theorem boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (hangle :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k :=
  boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
    C B
    (S2_agent_geometric_boundary_order_source_of_pred_arg_lt_succ_arg
      C B faceSuccRows hangle)

set_option linter.style.longLine false in
/-- Family source helper producing geometric neighbour-selection rows for the
chosen boundary exterior sectors.

Each row is built from the actual geometric `faceSucc` equality at the
predecessor boundary dart and the strict turn row at the same selected
boundary vertex. -/
noncomputable def boundaryVertexGeometricAngularNeighborSelectionRows_of_faceSuccRows_strictTurnRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (strictTurnRows :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      GraphVertexGeometricAngularNeighborSelectionRow C (B.vertex k)
        (B.vertex (PlanarInterface.cyclicPred B.length_pos k))
        (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) := by
  intro k
  let pred := PlanarInterface.cyclicPred B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hface :
      (geometricUnitDistanceRotationSystem C).faceSucc
          (UnitDistanceDart.ofBoundary B pred) =
        UnitDistanceDart.ofBoundary B k := by
    simpa [pred, hsucc_pred] using faceSuccRows.faceSucc_eq_next pred
  exact
    boundaryVertexGeometricAngularNeighborSelectionRow_of_faceSucc_eq_strictTurn
      C B k (by simpa [pred] using hface) (strictTurnRows k)

set_option linter.style.longLine false in
/-- Family source helper producing honest angular no-between rows for the
chosen boundary exterior sectors.

This is the strict-turn-row spelling of
`boundaryVertexAngularNoBetweenRows_of_faceSuccRows_pred_arg_lt_succ_arg`,
with the proof routed through the pointwise selected-sector helper. -/
theorem boundaryVertexAngularNoBetweenRows_of_faceSuccRows_strictTurnRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (strictTurnRows :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexAngularNoBetweenRows C B k := by
  intro k
  let pred := PlanarInterface.cyclicPred B.length_pos k
  have hsucc_pred : PlanarInterface.cyclicSucc B.length_pos pred = k := by
    dsimp [pred]
    exact PlanarInterface.cyclicSucc_cyclicPred B.length_pos k
  have hface :
      (geometricUnitDistanceRotationSystem C).faceSucc
          (UnitDistanceDart.ofBoundary B pred) =
        UnitDistanceDart.ofBoundary B k := by
    simpa [pred, hsucc_pred] using faceSuccRows.faceSucc_eq_next pred
  exact
    boundaryVertexAngularNoBetweenRows_of_faceSucc_eq_strictTurn
      C B k (by simpa [pred] using hface) (strictTurnRows k)

set_option linter.style.longLine false in
/-- Concrete adjacent entries of the genuine sorted outgoing list at the same
boundary vertices supply the reusable angular no-between rows.

This is the checked list-to-angular bridge for the S2 rotation-system source:
the input rows are actual `geometricOutgoingDartList` `getElem` witnesses on
the carrier boundary, and the output is the same-boundary
`BoundaryVertexAngularNoBetweenRows` family. -/
theorem boundaryVertexAngularNoBetweenRows_of_geometricOutgoingDartList_getElemRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
            ((geometricOutgoingDartList C (B.vertex k))[i]'
                (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
              (UnitDistanceDart.ofBoundary B
                (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
            ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
              UnitDistanceDart.ofBoundary B k) :
    forall k : Fin B.length,
      BoundaryVertexAngularNoBetweenRows C B k :=
  boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows
    C B
    (boundaryVertexGeometricRotationOrderRows_of_geometricOutgoingDartList_getElemRows
      C B rows)

set_option linter.style.longLine false in
/-- Claim `S2-rotation-system-bridge`: concrete face-successor rows plus
strict turn rows on the same carrier boundary produce the checked angular
no-between rows, without an identity angular order or global outgoing-list
no-between premise. -/
theorem S2_rotation_system_bridge_boundaryVertexAngularNoBetweenRows_of_faceSuccRows_strictTurnRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (strictTurnRows :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexAngularNoBetweenRows C B k :=
  boundaryVertexAngularNoBetweenRows_of_faceSuccRows_strictTurnRows
    C B faceSuccRows strictTurnRows

set_option linter.style.longLine false in
/-- Claim `S2-q13-geometric-angular-source`.

Actual same-boundary geometric `faceSucc` rows, stated at the selected
predecessor/current boundary darts, plus the selected strict turn rows produce
the honest angular no-between rows for those same exterior sectors. -/
theorem S2_q13_geometric_angular_source_boundaryVertexAngularNoBetweenRows_of_actual_faceSuccRows_strictTurnRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      forall k : Fin B.length,
        (geometricUnitDistanceRotationSystem C).faceSucc
            (UnitDistanceDart.ofBoundary B
              (PlanarInterface.cyclicPred B.length_pos k)) =
          UnitDistanceDart.ofBoundary B k)
    (strictTurnRows :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    forall k : Fin B.length,
      BoundaryVertexAngularNoBetweenRows C B k :=
  boundaryVertexAngularNoBetweenRows_of_actual_faceSuccRows_strictTurnRows
    C B faceSuccRows strictTurnRows

set_option linter.style.longLine false in
/-- Claim `S2-rotation-system-bridge`: concrete adjacent list rows on the same
carrier boundary produce the checked angular no-between rows directly. -/
theorem S2_rotation_system_bridge_boundaryVertexAngularNoBetweenRows_of_geometricOutgoingDartList_getElemRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
            ((geometricOutgoingDartList C (B.vertex k))[i]'
                (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
              (UnitDistanceDart.ofBoundary B
                (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
            ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
              UnitDistanceDart.ofBoundary B k) :
    forall k : Fin B.length,
      BoundaryVertexAngularNoBetweenRows C B k :=
  boundaryVertexAngularNoBetweenRows_of_geometricOutgoingDartList_getElemRows
    C B rows

/-- Boundary-index form of the geometric successor obligation: local angular
no-between data stated at the boundary vertex `B.vertex k` supplies the row
whose shared vertex is `B.vertex k`. -/
theorem geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)))
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
        other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
        other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
          ¬ BoundaryPredSuccAngularBetween C B k other) :
    GeometricBoundarySuccessorRow C B
      (PlanarInterface.cyclicPred B.length_pos k) := by
  have hsucc_pred :
      PlanarInterface.cyclicSucc B.length_pos
        (PlanarInterface.cyclicPred B.length_pos k) = k := by
    simp
  refine
    geometricBoundarySuccessorRow_of_no_graphDartArg_between
      C B (PlanarInterface.cyclicPred B.length_pos k) ?_ ?_
  · simpa [hsucc_pred] using hangle
  · intro other hAdj hother_pred hother_succ
    simpa [hsucc_pred] using
      hno_between other
        (by simpa [hsucc_pred] using hAdj)
        (by simpa [hsucc_pred] using hother_pred)
        (by simpa [hsucc_pred] using hother_succ)

/-- Simplified S2-B7 boundary-index bridge: if no incident neighbor at
`B.vertex k` has graph angle strictly between the predecessor and successor
boundary vertices, then the corresponding geometric successor row holds. -/
theorem geometricBoundarySuccessorRow_of_boundary_vertex_simple_no_graphDartArg_between
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)))
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
          ¬ BoundaryPredSuccAngularBetween C B k other) :
    GeometricBoundarySuccessorRow C B
      (PlanarInterface.cyclicPred B.length_pos k) :=
  geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between
    C B k hangle
    (fun other hAdj _ _ => hno_between other hAdj)

/-- Boundary-index wrap branch: when the successor argument is smaller than the
predecessor argument, excluding the cyclic branch interval supplies the
corresponding wrap-around geometric successor row. -/
theorem geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between_wrap
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hangle :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)))
    (hno_between :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
        other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
        other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
          ¬ BoundaryPredSuccAngularBetweenWrap C B k other) :
    GeometricBoundarySuccessorRow C B
      (PlanarInterface.cyclicPred B.length_pos k) := by
  have hsucc_pred :
      PlanarInterface.cyclicSucc B.length_pos
        (PlanarInterface.cyclicPred B.length_pos k) = k := by
    simp
  refine
    geometricBoundarySuccessorRow_of_no_graphDartArg_between_wrap
      C B (PlanarInterface.cyclicPred B.length_pos k) ?_ ?_
  · simpa [hsucc_pred] using hangle
  · intro other hAdj hother_pred hother_succ
    simpa [hsucc_pred, BoundaryPredSuccAngularBetweenWrap] using
      hno_between other
        (by simpa [hsucc_pred] using hAdj)
        (by simpa [hsucc_pred] using hother_pred)
        (by simpa [hsucc_pred] using hother_succ)

/-- Branch-sensitive boundary-index bridge: either the predecessor/successor
principal arguments are in ordinary order, or they wrap across the branch cut. -/
theorem geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between_branch
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (k : Fin B.length)
    (hbranch :
      (graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∧
        (∀ other : Fin n,
          GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
          other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
          other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
            ¬ BoundaryPredSuccAngularBetween C B k other)) ∨
      (graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) ∧
        (∀ other : Fin n,
          GraphBridge.UnitDistanceAdj C (B.vertex k) other ->
          other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos k) ->
          other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos k) ->
            ¬ BoundaryPredSuccAngularBetweenWrap C B k other))) :
    GeometricBoundarySuccessorRow C B
      (PlanarInterface.cyclicPred B.length_pos k) := by
  rcases hbranch with ⟨hangle, hno_between⟩ | ⟨hangle, hno_between⟩
  · exact
      geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between
        C B k hangle hno_between
  · exact
      geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between_wrap
        C B k hangle hno_between

namespace BoundaryVertexAngularNoBetweenRows

variable {C : _root_.UDConfig n}
variable {B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C}
variable {k : Fin B.length}

/-- One honest angular sector row gives the corresponding geometric
boundary-successor row. -/
theorem toGeometricBoundarySuccessorRow
    (rows : BoundaryVertexAngularNoBetweenRows C B k) :
    GeometricBoundarySuccessorRow C B
      (PlanarInterface.cyclicPred B.length_pos k) :=
  geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between
    C B k rows.angle rows.no_between

end BoundaryVertexAngularNoBetweenRows

/-- Boundary-vertex form of the geometric successor obligation: at every
boundary vertex, no other incident unit-distance neighbor has angle strictly
between the predecessor and successor boundary vertices. -/
theorem geometricBoundarySuccessorRows_of_boundary_vertex_no_graphDartArg_between
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hangle :
      ∀ j : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos j)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos j)))
    (hno_between :
      ∀ (j : Fin B.length) (other : Fin n),
        GraphBridge.UnitDistanceAdj C (B.vertex j) other ->
        other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos j) ->
        other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos j) ->
          ¬ BoundaryPredSuccAngularBetween C B j other) :
    GeometricBoundarySuccessorRows C B := by
  intro k
  let j := PlanarInterface.cyclicSucc B.length_pos k
  have hpred : PlanarInterface.cyclicPred B.length_pos j = k := by
    simp [j, PlanarInterface.cyclicPred_cyclicSucc]
  have hangle' :
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (UnitDistanceDart.ofBoundary B k).reverse.head <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicSucc B.length_pos k)).head := by
    simpa [j, hpred] using hangle j
  have hno_between' :
      ∀ other : Fin n,
        GraphBridge.UnitDistanceAdj C
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other ->
        other ≠ (UnitDistanceDart.ofBoundary B k).reverse.head ->
        other ≠ (UnitDistanceDart.ofBoundary B
          (PlanarInterface.cyclicSucc B.length_pos k)).head ->
          ¬ (graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
                (UnitDistanceDart.ofBoundary B k).reverse.head <
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other ∧
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) other <
              graphDartArg (canonicalGeometricGraph C)
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))
                (UnitDistanceDart.ofBoundary B
                  (PlanarInterface.cyclicSucc B.length_pos k)).head) := by
    intro other hAdj hother_pred hother_succ
    simpa [j, hpred] using
      hno_between j other hAdj
        (by simpa [j, hpred] using hother_pred)
        (by simpa [j, hpred] using hother_succ)
  exact
    geometricBoundarySuccessorRow_of_no_graphDartArg_between
      C B k hangle' hno_between'

/-- Rows-level honest angular-sector bridge.  A family of genuine
predecessor/successor angular no-between rows at the concrete boundary
vertices supplies the geometric face-successor rows for the boundary cycle. -/
theorem geometricBoundarySuccessorRows_of_boundary_vertex_angularNoBetweenRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall j : Fin B.length,
        BoundaryVertexAngularNoBetweenRows C B j) :
    GeometricBoundarySuccessorRows C B := by
  exact
    geometricBoundarySuccessorRows_of_boundary_vertex_no_graphDartArg_between
      C B
      (fun j => (rows j).angle)
      (fun j => (rows j).no_between)

set_option linter.style.longLine false in
/-- Claim `S2-geometric-angular-source`.

Concrete same-boundary geometric `faceSucc` rows plus the selected exterior
strict-turn rows supply both the angular rows and the boundary face-successor
rows needed downstream.  The remaining source assumptions are exactly
`UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B`
and the pointwise strict predecessor-before-successor turn rows; no identity
angular rows, global all-outgoing no-between row, W32 composer, or
actual-sector premise loop is used. -/
theorem S2_geometric_angular_source_boundary_faceSuccRows_of_strictTurnRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (faceSuccRows :
      UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B)
    (strictTurnRows :
      forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :
    (forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k) ∧
      GeometricBoundarySuccessorRows C B := by
  let angularRows :
      forall k : Fin B.length, BoundaryVertexAngularNoBetweenRows C B k :=
    S2_rotation_system_bridge_boundaryVertexAngularNoBetweenRows_of_faceSuccRows_strictTurnRows
      C B faceSuccRows strictTurnRows
  exact
    ⟨angularRows,
      geometricBoundarySuccessorRows_of_boundary_vertex_angularNoBetweenRows
        C B angularRows⟩

/-- Rows-level simplified S2-B7 bridge: the no-between predicate may be stated
directly at each boundary vertex without endpoint-nequality side assumptions. -/
theorem geometricBoundarySuccessorRows_of_boundary_vertex_simple_no_graphDartArg_between
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hangle :
      ∀ j : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos j)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos j)))
    (hno_between :
      ∀ (j : Fin B.length) (other : Fin n),
        GraphBridge.UnitDistanceAdj C (B.vertex j) other ->
          ¬ BoundaryPredSuccAngularBetween C B j other) :
    GeometricBoundarySuccessorRows C B := by
  exact
    geometricBoundarySuccessorRows_of_boundary_vertex_no_graphDartArg_between
      C B hangle
      (fun j other hAdj _ _ => hno_between j other hAdj)

/-- Rows-level wrap branch of
`geometricBoundarySuccessorRows_of_boundary_vertex_no_graphDartArg_between`. -/
theorem geometricBoundarySuccessorRows_of_boundary_vertex_no_graphDartArg_between_wrap
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hangle :
      ∀ j : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos j)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos j)))
    (hno_between :
      ∀ (j : Fin B.length) (other : Fin n),
        GraphBridge.UnitDistanceAdj C (B.vertex j) other ->
        other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos j) ->
        other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos j) ->
          ¬ BoundaryPredSuccAngularBetweenWrap C B j other) :
    GeometricBoundarySuccessorRows C B := by
  intro k
  let j := PlanarInterface.cyclicSucc B.length_pos k
  have hpred : PlanarInterface.cyclicPred B.length_pos j = k := by
    simp [j, PlanarInterface.cyclicPred_cyclicSucc]
  have hrow :
      GeometricBoundarySuccessorRow C B
        (PlanarInterface.cyclicPred B.length_pos j) :=
    geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between_wrap
      C B j (hangle j) (hno_between j)
  simpa [j, hpred] using hrow

/-- Rows-level branch-sensitive bridge for geometric boundary successor rows. -/
theorem geometricBoundarySuccessorRows_of_boundary_vertex_no_graphDartArg_between_branch
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hbranch :
      ∀ j : Fin B.length,
        (graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos j)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos j)) ∧
          (∀ other : Fin n,
            GraphBridge.UnitDistanceAdj C (B.vertex j) other ->
            other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos j) ->
            other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos j) ->
              ¬ BoundaryPredSuccAngularBetween C B j other)) ∨
        (graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos j)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex j)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos j)) ∧
          (∀ other : Fin n,
            GraphBridge.UnitDistanceAdj C (B.vertex j) other ->
            other ≠ B.vertex (PlanarInterface.cyclicPred B.length_pos j) ->
            other ≠ B.vertex (PlanarInterface.cyclicSucc B.length_pos j) ->
              ¬ BoundaryPredSuccAngularBetweenWrap C B j other))) :
    GeometricBoundarySuccessorRows C B := by
  intro k
  let j := PlanarInterface.cyclicSucc B.length_pos k
  have hpred : PlanarInterface.cyclicPred B.length_pos j = k := by
    simp [j, PlanarInterface.cyclicPred_cyclicSucc]
  have hrow :
      GeometricBoundarySuccessorRow C B
        (PlanarInterface.cyclicPred B.length_pos j) :=
    geometricBoundarySuccessorRow_of_boundary_vertex_no_graphDartArg_between_branch
      C B j (hbranch j)
  simpa [j, hpred] using hrow

/-- Boundary-cycle form: local consecutive-list evidence at every shared
boundary vertex supplies `UnitDistanceCycleFaceSuccRows` for the genuine
geometric rotation system.  The remaining S2 geometric task is to prove these
local list-adjacency rows for the actual exterior boundary cycle. -/
def unitDistanceCycleFaceSuccRows_of_geometric_boundary_list_successors
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hlocal : GeometricBoundarySuccessorRows C B) :
    UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B
    where
  faceSucc_eq_next := by
    intro k
    rcases hlocal k with hsucc | hlast
    · rcases hsucc with ⟨i, hi, hreverse, htarget⟩
      exact
        geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_succ
          C
          (UnitDistanceDart.ofBoundary B k)
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicSucc B.length_pos k))
          i hi hreverse htarget
    · rcases hlast with ⟨hpos, hreverse, htarget⟩
      exact
        geometricUnitDistanceRotationSystem_faceSucc_eq_of_reverse_getElem_last
          C
          (UnitDistanceDart.ofBoundary B k)
          (UnitDistanceDart.ofBoundary B
            (PlanarInterface.cyclicSucc B.length_pos k))
          hpos hreverse htarget

/-- Boundary-vertex geometric rotation-order rows give the corresponding
shared-vertex successor rows for the same concrete boundary cycle. -/
theorem geometricBoundarySuccessorRows_of_boundaryVertexGeometricRotationOrderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hrows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    GeometricBoundarySuccessorRows C B := by
  intro k
  let j := PlanarInterface.cyclicSucc B.length_pos k
  have hpred : PlanarInterface.cyclicPred B.length_pos j = k := by
    simp [j, PlanarInterface.cyclicPred_cyclicSucc]
  left
  rcases hrows j with ⟨i, hi, hreverse, htarget⟩
  refine ⟨i, by simpa [j] using hi, ?_, ?_⟩
  · simpa [j, hpred] using hreverse
  · simpa [j] using htarget

set_option linter.style.longLine false in
/-- Claim `S2-agent-geometric-boundary-successor-20260520e`.

Real adjacent-index rows in the sorted `geometricOutgoingDartList` at each
boundary vertex supply both requested geometric boundary outputs: the
pointwise non-wrap `BoundaryVertexGeometricRotationOrderRow` family and the
cyclic `GeometricBoundarySuccessorRows` for the same concrete boundary.

The exact remaining leaf is the displayed adjacent-list source row. -/
theorem S2_agent_geometric_boundary_successor_20260520e_of_geometricOutgoingDartList_orderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (rows :
      forall k : Fin B.length,
        Exists fun i : Nat =>
          Exists fun hi :
              i + 1 < (geometricOutgoingDartList C (B.vertex k)).length =>
            ((geometricOutgoingDartList C (B.vertex k))[i]'
                (Nat.lt_trans (Nat.lt_succ_self i) hi)).1 =
              (UnitDistanceDart.ofBoundary B
                (PlanarInterface.cyclicPred B.length_pos k)).reverse ∧
            ((geometricOutgoingDartList C (B.vertex k))[i + 1]'hi).1 =
              UnitDistanceDart.ofBoundary B k) :
    GeometricBoundarySuccessorRows C B ∧
      (forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) := by
  let horder :=
    boundaryVertexGeometricRotationOrderRows_of_geometricOutgoingDartList_getElemRows
      C B rows
  exact
    ⟨geometricBoundarySuccessorRows_of_boundaryVertexGeometricRotationOrderRows
        C B horder,
      horder⟩

/-- Honest adjacent rows in the actual sorted geometric outgoing lists supply
`UnitDistanceCycleFaceSuccRows` for the genuine geometric rotation system. -/
theorem unitDistanceCycleFaceSuccRows_of_boundaryVertexGeometricRotationOrderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hrows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B :=
  unitDistanceCycleFaceSuccRows_of_geometric_boundary_list_successors
    C B
    (geometricBoundarySuccessorRows_of_boundaryVertexGeometricRotationOrderRows
      C B hrows)

/-- The same honest geometric rotation-order rows also orient the boundary:
at each boundary vertex, the predecessor dart is before the successor dart in
the sorted principal-argument order. -/
theorem boundary_orientation_of_boundaryVertexGeometricRotationOrderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hrows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    forall k : Fin B.length,
      graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
        graphDartArg (canonicalGeometricGraph C)
          (B.vertex k)
          (B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) :=
  fun k =>
    (boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow
      C B k (hrows k)).angle

/-- Combined row package from genuine geometric boundary rotation-order rows:
the rows give both the geometric face-successor cycle equation and the
ordinary boundary orientation inequalities. -/
theorem faceSuccRows_and_boundary_orientation_of_boundaryVertexGeometricRotationOrderRows
    (C : _root_.UDConfig n)
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (hrows :
      forall k : Fin B.length,
        BoundaryVertexGeometricRotationOrderRow C B k) :
    UnitDistanceCycleFaceSuccRows C (geometricUnitDistanceRotationSystem C) B ∧
      (forall k : Fin B.length,
        graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicPred B.length_pos k)) <
          graphDartArg (canonicalGeometricGraph C)
            (B.vertex k)
            (B.vertex (PlanarInterface.cyclicSucc B.length_pos k))) :=
  ⟨unitDistanceCycleFaceSuccRows_of_boundaryVertexGeometricRotationOrderRows
      C B hrows,
    boundary_orientation_of_boundaryVertexGeometricRotationOrderRows C B hrows⟩

end GeometricRotationSystem
end Swanepoel
end ErdosProblems1066

end
