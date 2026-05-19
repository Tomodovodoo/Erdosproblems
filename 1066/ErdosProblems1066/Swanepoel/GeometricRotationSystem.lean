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

end GeometricRotationSystem
end Swanepoel
end ErdosProblems1066

end
