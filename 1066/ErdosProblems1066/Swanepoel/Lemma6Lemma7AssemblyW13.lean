import ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12
import ErdosProblems1066.Swanepoel.Lemma7GapInductionW12
import ErdosProblems1066.Swanepoel.BoundaryPartitionInstantiation
import ErdosProblems1066.Swanepoel.LongArcGapConcrete

set_option autoImplicit false

/-!
# W13 Lemma 6/Lemma 7 long-arc assembly

This module is a reusable bridge from the W12 Lemma 6 and Lemma 7 interfaces
to the existing long-arc count-gap route.

It proves no endpoint theorem.  The main checked conclusion is the count
coverage inequality `d3 <= negativeCount + longArcCount`, obtained from the
Lemma 7 terminal gap exclusion.  That inequality is then used to fill the one
Lemma 6/7 coverage field required by
`LongArcExistenceConcrete.BoundaryLongArcExistenceFields`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma6Lemma7AssemblyW13

open Lemma10Inequalities
open BoundaryClassification
open BoundaryWalkConstruction
open Lemma6NegativeAfterGapW12
open Lemma7GapInductionW12
open OuterBoundaryInterface
open PlanarInterface

universe u

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Lemma 7 terminal coverage -/

/-- Lemma 7 terminal data, tied to a chosen long-arc count.

The induction proves that the terminal prefix count is at least `length + 1`;
the two extra comparison fields identify `length + 1` with the boundary
degree-three count and bound the terminal prefix by `N + A`. -/
structure GapNegativeCoverageData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (longArcCount : Nat) where
  inductionData : DegreeThreeGapInductionData D
  terminalExclusion : TerminalGapExclusion inductionData
  degreeThree_eq_length_succ :
    D.outerBoundaryCounts.d3 = inductionData.length + 1
  terminal_count_le_negativeCount_add_longArcCount :
    inductionData.count inductionData.length <=
      D.outerBoundaryCounts.negativeCount + longArcCount

namespace GapNegativeCoverageData

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {longArcCount : Nat}

/-- Lemma 7 terminal exclusion supplies the strict/successor terminal lower
bound. -/
theorem terminal_count_succ_lower_bound
    (C : GapNegativeCoverageData D longArcCount) :
    C.inductionData.length + 1 <=
      C.inductionData.count C.inductionData.length :=
  TerminalGapExclusion.terminal_count_succ_lower_bound C.terminalExclusion

/-- The assembled Lemma 6/Lemma 7 coverage inequality used by the long-arc
count-gap step. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (C : GapNegativeCoverageData D longArcCount) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + longArcCount := by
  rw [C.degreeThree_eq_length_succ]
  exact
    le_trans C.terminal_count_succ_lower_bound
      C.terminal_count_le_negativeCount_add_longArcCount

end GapNegativeCoverageData

/-! ## Boundary-walk negative-after-gap induction data -/

variable {C : BoundaryCycle G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {P : OuterBoundaryCore G}
variable
  {walk :
    OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- Boundary-walk form of the Lemma 7 induction input.

The `index` fields keep the count-level induction attached to concrete
boundary-walk positions.  The Lemma 6 certificates themselves are not fields:
they are derived from the supplied `BoundaryWalkLemma6Obstruction`. -/
structure BoundaryWalkGapNegativeInductionData
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) where
  length : Nat
  count : Nat -> Nat
  index : Nat -> Fin P.outerCycle.length
  terminalIndex : Fin P.outerCycle.length
  count_mono_step :
    forall s : Nat, s < length -> count s <= count (s + 1)
  equality_gives_gap :
    forall s : Nat, s < length -> count s = s ->
      BoundaryWalkGapAt walk.data (index s)
  forced_increments_count :
    forall s : Nat, s < length ->
      BoundaryWalkNegativeAfterGapAt walk.data (index s) ->
        s + 1 <= count (s + 1)
  terminal_equality_gives_gap :
    count length = length -> BoundaryWalkGapAt walk.data terminalIndex
  terminal_count_ne_length :
    count length ≠ length

namespace BoundaryWalkGapNegativeInductionData

variable
  {O :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}

/-! ### Concrete finite boundary-walk constructor -/

/-- A boundary negative contribution, retaining which counted slot is used.

The slot type counts nontriangle edges, degree-five vertices, and degree-six
vertices separately, matching `BoundaryCounts.negativeCount` rather than only
counting boundary positions. -/
abbrev BoundaryWalkNegativeSlot
    (D :
      BoundaryWalkBookkeeping P.outerCycle IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6) : Type :=
  D.nontriangleEdgeIndices ⊕
    (D.degree5Indices ⊕ D.degree6Indices)

/-- Convert a propositional negative boundary contribution into the exact
finite slot counted by `negativeCount`. -/
def negativeSlotOfNegativeAt
    (D :
      BoundaryWalkBookkeeping P.outerCycle IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    {k : Fin P.outerCycle.length}
    (hnegative : BoundaryWalkNegativeAt D k) :
    BoundaryWalkNegativeSlot D := by
  by_cases hnontriangle : D.edgeKind k = BoundaryEdgeClass.nontriangle
  · exact Sum.inl ⟨k, hnontriangle⟩
  · by_cases hdegree5 : D.vertexKind k = BoundaryDegreeClass.degree5
    · exact Sum.inr (Sum.inl ⟨k, hdegree5⟩)
    · have hdegree6 : D.vertexKind k = BoundaryDegreeClass.degree6 := by
        rcases hnegative with hnontriangle' | hhigh
        · exact False.elim (hnontriangle hnontriangle')
        · rcases hhigh with hdegree5' | hdegree6'
          · exact False.elim (hdegree5 hdegree5')
          · exact hdegree6'
      exact Sum.inr (Sum.inr ⟨k, hdegree6⟩)

/-- Equality of negative slots remembers equality of their boundary indices. -/
theorem negativeSlotOfNegativeAt_index_eq_of_eq
    {D :
      BoundaryWalkBookkeeping P.outerCycle IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {k l : Fin P.outerCycle.length}
    {hk : BoundaryWalkNegativeAt D k}
    {hl : BoundaryWalkNegativeAt D l}
    (h :
      negativeSlotOfNegativeAt D hk =
        negativeSlotOfNegativeAt D hl) :
    k = l := by
  by_cases hknontriangle : D.edgeKind k = BoundaryEdgeClass.nontriangle
  · by_cases hlnontriangle : D.edgeKind l = BoundaryEdgeClass.nontriangle
    · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle] at h
      cases h
      rfl
    · by_cases hldegree5 : D.vertexKind l = BoundaryDegreeClass.degree5
      · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
          hldegree5] at h
      · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
          hldegree5] at h
  · by_cases hlnontriangle : D.edgeKind l = BoundaryEdgeClass.nontriangle
    · by_cases hkdegree5 : D.vertexKind k = BoundaryDegreeClass.degree5
      · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
          hkdegree5] at h
      · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
          hkdegree5] at h
    · by_cases hkdegree5 : D.vertexKind k = BoundaryDegreeClass.degree5
      · by_cases hldegree5 : D.vertexKind l = BoundaryDegreeClass.degree5
        · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
            hkdegree5, hldegree5] at h
          cases h
          rfl
        · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
            hkdegree5, hldegree5] at h
      · by_cases hldegree5 : D.vertexKind l = BoundaryDegreeClass.degree5
        · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
            hkdegree5, hldegree5] at h
        · simp [negativeSlotOfNegativeAt, hknontriangle, hlnontriangle,
            hkdegree5, hldegree5] at h
          cases h
          rfl

/-- Lemma 6 sends each degree-three non-long-arc boundary index to a counted
negative slot at the next boundary position; degree-three long arcs are sent
to the counted long-arc slot. -/
noncomputable def degreeThreeIndexToLongArcOrNegativeSlot
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (x : walk.data.degree3Indices) :
    walk.data.longArcIndices ⊕ BoundaryWalkNegativeSlot walk.data := by
  classical
  by_cases hlong : walk.data.longArc x.1
  · exact Sum.inl ⟨x.1, hlong⟩
  · have hgap : BoundaryWalkGapAt walk.data x.1 := ⟨x.2, hlong⟩
    exact
      Sum.inr
        (negativeSlotOfNegativeAt walk.data
          (O.negativeAfter_of_gap x.1 hgap))

/-- The preceding map is injective because the boundary successor is
injective on the cyclic index type. -/
theorem degreeThreeIndexToLongArcOrNegativeSlot_injective
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    Function.Injective (degreeThreeIndexToLongArcOrNegativeSlot O) := by
  intro x y hxy
  classical
  by_cases hxlong : walk.data.longArc x.1
  · by_cases hylong : walk.data.longArc y.1
    · simp [degreeThreeIndexToLongArcOrNegativeSlot, hxlong, hylong] at hxy
      have hval : x.1 = y.1 :=
        congrArg (fun z : walk.data.longArcIndices => z.1) hxy
      exact Subtype.ext hval
    · have hfalse : False := by
        simp [degreeThreeIndexToLongArcOrNegativeSlot, hxlong, hylong] at hxy
      exact False.elim hfalse
  · by_cases hylong : walk.data.longArc y.1
    · have hfalse : False := by
        simp [degreeThreeIndexToLongArcOrNegativeSlot, hxlong, hylong] at hxy
      exact False.elim hfalse
    · have hslot :
          negativeSlotOfNegativeAt walk.data
              (O.negativeAfter_of_gap x.1 ⟨x.2, hxlong⟩) =
            negativeSlotOfNegativeAt walk.data
              (O.negativeAfter_of_gap y.1 ⟨y.2, hylong⟩) := by
        simpa [degreeThreeIndexToLongArcOrNegativeSlot, hxlong, hylong]
          using hxy
      have hnext :
          P.outerCycle.next x.1 = P.outerCycle.next y.1 :=
        negativeSlotOfNegativeAt_index_eq_of_eq hslot
      have hsucc :
          PlanarInterface.cyclicSucc P.outerCycle.length_pos x.1 =
            PlanarInterface.cyclicSucc P.outerCycle.length_pos y.1 := by
        simpa [OuterBoundaryInterface.BoundaryCycle.next] using hnext
      have hval : x.1 = y.1 :=
        OuterBoundaryReduction.cyclicSucc_injective
          P.outerCycle.length_pos hsucc
      exact Subtype.ext hval

/-- Concrete Lemma 7 count coverage from the Lemma 6 obstruction and the
finite boundary walk. -/
theorem degreeThree_le_negativeCount_add_boundaryLongArcCount
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount +
        O.planarBoundary.outerBoundaryCounts.B := by
  have hcard :=
    Fintype.card_le_of_injective
      (f := degreeThreeIndexToLongArcOrNegativeSlot O)
      (degreeThreeIndexToLongArcOrNegativeSlot_injective O)
  have hcard' :
      Fintype.card walk.data.degree3Indices <=
        Fintype.card walk.data.longArcIndices +
          (Fintype.card walk.data.nontriangleEdgeIndices +
            (Fintype.card walk.data.degree5Indices +
              Fintype.card walk.data.degree6Indices)) := by
    simpa [BoundaryWalkNegativeSlot] using hcard
  change
    Fintype.card walk.data.degree3Indices <=
      (Fintype.card walk.data.nontriangleEdgeIndices +
          Fintype.card walk.data.degree5Indices +
        Fintype.card walk.data.degree6Indices) +
        Fintype.card walk.data.longArcIndices
  omega

/-- The assembled boundary-angle row always has at least one degree-three
boundary vertex. -/
theorem degreeThree_pos
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    0 < O.planarBoundary.outerBoundaryCounts.d3 := by
  have h :=
    O.planarBoundary.boundaryNegativeCountInequality
  omega

/-- A concrete boundary index used for vacuous equality branches in the
count-level induction data. -/
def firstBoundaryIndex : Fin P.outerCycle.length :=
  ⟨0, P.outerCycle.length_pos⟩

/-- Concrete `BoundaryWalkGapNegativeInductionData` obtained from the Lemma 6
obstruction and the boundary walk.

The count is the total degree-three count.  Thus all equality-gap branches are
arithmetically impossible, while the terminal comparison below is supplied by
the finite injective assignment from degree-three indices to long-arc or
negative slots. -/
noncomputable def ofBoundaryWalkLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryWalkGapNegativeInductionData O where
  length := O.planarBoundary.outerBoundaryCounts.d3 - 1
  count := fun _ => O.planarBoundary.outerBoundaryCounts.d3
  index := fun _ => firstBoundaryIndex
  terminalIndex := firstBoundaryIndex
  count_mono_step := by
    intro _s _hs
    exact le_rfl
  equality_gives_gap := by
    intro s hs hcount
    exfalso
    have hpos := degreeThree_pos O
    omega
  forced_increments_count := by
    intro s hs _hforced
    have hpos := degreeThree_pos O
    omega
  terminal_equality_gives_gap := by
    intro hcount
    exfalso
    have hpos := degreeThree_pos O
    omega
  terminal_count_ne_length := by
    intro hcount
    have hpos := degreeThree_pos O
    omega

@[simp]
theorem ofBoundaryWalkLemma6Obstruction_length
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    (ofBoundaryWalkLemma6Obstruction O).length =
      O.planarBoundary.outerBoundaryCounts.d3 - 1 :=
  rfl

@[simp]
theorem ofBoundaryWalkLemma6Obstruction_count
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (s : Nat) :
    (ofBoundaryWalkLemma6Obstruction O).count s =
      O.planarBoundary.outerBoundaryCounts.d3 :=
  rfl

/-- The concrete induction length is one less than the degree-three count. -/
theorem degreeThree_eq_length_succ_ofBoundaryWalkLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    O.planarBoundary.outerBoundaryCounts.d3 =
      (ofBoundaryWalkLemma6Obstruction O).length + 1 := by
  have hpos := degreeThree_pos O
  simp [ofBoundaryWalkLemma6Obstruction]
  omega

/-- Terminal comparison for the concrete boundary-walk induction data. -/
theorem terminal_count_le_negativeCount_add_boundaryLongArcCount
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    (ofBoundaryWalkLemma6Obstruction O).count
        (ofBoundaryWalkLemma6Obstruction O).length <=
      O.planarBoundary.outerBoundaryCounts.negativeCount +
        O.planarBoundary.outerBoundaryCounts.B := by
  simpa [ofBoundaryWalkLemma6Obstruction] using
    degreeThree_le_negativeCount_add_boundaryLongArcCount O

/-- Convert boundary-walk gap/negative-after-gap data into the generic Lemma 7
count induction. -/
def toDegreeThreeGapInductionData
    (B : BoundaryWalkGapNegativeInductionData O) :
    DegreeThreeGapInductionData O.planarBoundary where
  length := B.length
  count := B.count
  gapAt := fun s => BoundaryWalkGapAt walk.data (B.index s)
  forcedAt := fun s => BoundaryWalkNegativeAfterGapAt walk.data (B.index s)
  count_mono_step := B.count_mono_step
  equality_gives_gap := B.equality_gives_gap
  lemma6_gap_forces_forced := by
    intro s _hs
    exact O.toGapToNegativeCertificate (B.index s)
  forced_increments_count := B.forced_increments_count

/-- Terminal wrap-around gap exclusion, with Lemma 6 supplied by the same
boundary-walk obstruction. -/
def toTerminalGapExclusion
    (B : BoundaryWalkGapNegativeInductionData O) :
    TerminalGapExclusion B.toDegreeThreeGapInductionData where
  terminalGap := BoundaryWalkGapAt walk.data B.terminalIndex
  terminalForced := BoundaryWalkNegativeAfterGapAt walk.data B.terminalIndex
  terminal_equality_gives_gap := by
    intro hcount
    exact B.terminal_equality_gives_gap hcount
  terminal_lemma6_gap_forces_forced :=
    O.toGapToNegativeCertificate B.terminalIndex
  terminal_count_ne_length := B.terminal_count_ne_length

/-- Boundary-walk form of the Lemma 7 terminal successor lower bound. -/
theorem terminal_count_succ_lower_bound
    (B : BoundaryWalkGapNegativeInductionData O) :
    B.length + 1 <= B.count B.length := by
  simpa [toDegreeThreeGapInductionData] using
    TerminalGapExclusion.terminal_count_succ_lower_bound
      B.toTerminalGapExclusion

/-- Attach the terminal induction to a concrete long-arc count. -/
def toGapNegativeCoverageData
    (B : BoundaryWalkGapNegativeInductionData O)
    {longArcCount : Nat}
    (degreeThree_eq_length_succ :
      O.planarBoundary.outerBoundaryCounts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcCount :
      B.count B.length <=
        O.planarBoundary.outerBoundaryCounts.negativeCount + longArcCount) :
    GapNegativeCoverageData O.planarBoundary longArcCount where
  inductionData := B.toDegreeThreeGapInductionData
  terminalExclusion := B.toTerminalGapExclusion
  degreeThree_eq_length_succ := by
    simpa [toDegreeThreeGapInductionData] using degreeThree_eq_length_succ
  terminal_count_le_negativeCount_add_longArcCount := by
    simpa [toDegreeThreeGapInductionData] using
      terminal_count_le_negativeCount_add_longArcCount

/-- Boundary-walk form of the Lemma 6/Lemma 7 coverage inequality. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (B : BoundaryWalkGapNegativeInductionData O)
    {longArcCount : Nat}
    (degreeThree_eq_length_succ :
      O.planarBoundary.outerBoundaryCounts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcCount :
      B.count B.length <=
        O.planarBoundary.outerBoundaryCounts.negativeCount + longArcCount) :
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount + longArcCount :=
  (B.toGapNegativeCoverageData degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcCount).degreeThree_le_negativeCount_add_longArcCount

/-- Concrete gap-negative coverage data produced directly from the boundary
walk and Lemma 6 obstruction. -/
noncomputable def toGapNegativeCoverageDataOfBoundaryWalkLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    GapNegativeCoverageData
      O.planarBoundary O.planarBoundary.outerBoundaryCounts.B :=
  (ofBoundaryWalkLemma6Obstruction O).toGapNegativeCoverageData
    (degreeThree_eq_length_succ_ofBoundaryWalkLemma6Obstruction O)
    (terminal_count_le_negativeCount_add_boundaryLongArcCount O)

end BoundaryWalkGapNegativeInductionData

/-! ## Boundary-walk outputs as concrete gap-negative coverage -/

/-- Concrete Lemma 6/7 boundary-walk output for a specified planar-boundary
row.

The package keeps the actual boundary walk, Lemma 6 obstruction, and Lemma 7
gap induction visible.  The final equality only identifies the planar-boundary
row produced by that boundary-walk obstruction with the downstream row that
needs `GapNegativeCoverageData`. -/
structure BoundaryWalkGapNegativeCoverageOutput
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  P : OuterBoundaryCore G
  IsTriangle : Edge n -> Prop
  IsNontriangle : Edge n -> Prop
  IsDegree3 : Fin n -> Prop
  IsDegree4 : Fin n -> Prop
  IsDegree5 : Fin n -> Prop
  IsDegree6 : Fin n -> Prop
  walk :
    OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6
  geometricAngleSum : Real
  forced_le_geometric :
    walk.counts.forcedBoundaryAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= walk.counts.polygonAngleSum
  Subpolygon : Type u
  subpolygonData :
    Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G
  obstruction :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData
  gapInduction : BoundaryWalkGapNegativeInductionData obstruction
  longArcCount : Nat
  degreeThree_eq_length_succ :
    obstruction.planarBoundary.outerBoundaryCounts.d3 =
      gapInduction.length + 1
  terminal_count_le_negativeCount_add_longArcCount :
    gapInduction.count gapInduction.length <=
      obstruction.planarBoundary.outerBoundaryCounts.negativeCount +
        longArcCount
  planarBoundary_eq : obstruction.planarBoundary = D

namespace BoundaryWalkGapNegativeCoverageOutput

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {P : OuterBoundaryCore G}
variable
  {walk :
    OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- Positive row-level boundary-walk gap coverage output produced from the
Lemma 6 obstruction and the concrete boundary walk. -/
noncomputable def ofBoundaryWalkLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (planarBoundary_eq : O.planarBoundary = D) :
    BoundaryWalkGapNegativeCoverageOutput D where
  P := P
  IsTriangle := IsTriangle
  IsNontriangle := IsNontriangle
  IsDegree3 := IsDegree3
  IsDegree4 := IsDegree4
  IsDegree5 := IsDegree5
  IsDegree6 := IsDegree6
  walk := walk
  geometricAngleSum := geometricAngleSum
  forced_le_geometric := forced_le_geometric
  geometric_le_polygon := geometric_le_polygon
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData
  obstruction := O
  gapInduction :=
    BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction O
  longArcCount := O.planarBoundary.outerBoundaryCounts.B
  degreeThree_eq_length_succ :=
    BoundaryWalkGapNegativeInductionData.degreeThree_eq_length_succ_ofBoundaryWalkLemma6Obstruction
      O
  terminal_count_le_negativeCount_add_longArcCount :=
    BoundaryWalkGapNegativeInductionData.terminal_count_le_negativeCount_add_boundaryLongArcCount
      O
  planarBoundary_eq := planarBoundary_eq

/-- Nonempty form matching the selected-frame row source surface. -/
theorem nonempty_ofBoundaryWalkLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (planarBoundary_eq : O.planarBoundary = D) :
    Nonempty (BoundaryWalkGapNegativeCoverageOutput D) :=
  Nonempty.intro
    (ofBoundaryWalkLemma6Obstruction O planarBoundary_eq)

/-- The concrete boundary-walk output yields the exact gap-negative coverage
row for the specified planar boundary. -/
def toGapNegativeCoverageData
    (B : BoundaryWalkGapNegativeCoverageOutput D) :
    GapNegativeCoverageData D B.longArcCount := by
  cases B with
  | mk P IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6
      walk geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData obstruction gapInduction longArcCount
      degreeThree_eq_length_succ
      terminal_count_le_negativeCount_add_longArcCount planarBoundary_eq =>
      dsimp at *
      cases planarBoundary_eq
      exact
        gapInduction.toGapNegativeCoverageData
          degreeThree_eq_length_succ
          terminal_count_le_negativeCount_add_longArcCount

/-- Existential form used by selected frame/cyclic row families. -/
theorem exists_gapNegativeCoverageData
    (B : BoundaryWalkGapNegativeCoverageOutput D) :
    exists longArcCount : Nat,
      Nonempty (GapNegativeCoverageData D longArcCount) :=
  Exists.intro B.longArcCount
    (Nonempty.intro B.toGapNegativeCoverageData)

/-- The boundary-walk output exposes the checked Lemma 6/7 coverage
inequality on the specified planar-boundary row. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (B : BoundaryWalkGapNegativeCoverageOutput D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + B.longArcCount :=
  B.toGapNegativeCoverageData.degreeThree_le_negativeCount_add_longArcCount

/-- Transport the boundary-walk coverage data to a caller-chosen long-arc
count once that count is identified with the output count. -/
def toGapNegativeCoverageDataOfLongArcCountEq
    (B : BoundaryWalkGapNegativeCoverageOutput D)
    {longArcCount : Nat}
    (longArcCount_eq : B.longArcCount = longArcCount) :
    GapNegativeCoverageData D longArcCount := by
  cases longArcCount_eq
  exact B.toGapNegativeCoverageData

end BoundaryWalkGapNegativeCoverageOutput

/-! ## Full boundary-walk Lemma 6 obstruction sources -/

/-- A strict source for a requested planar-boundary row: it stores the actual
full boundary walk and Lemma 6 obstruction whose planar-boundary package is
the requested row.

This is deliberately stronger than a local M8 spine row.  The equality ties
the complete boundary-walk carrier, not just named spine indices, to the
downstream `PlanarBoundaryData`. -/
structure BoundaryWalkLemma6ObstructionSource
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  P : OuterBoundaryCore G
  IsTriangle : Edge n -> Prop
  IsNontriangle : Edge n -> Prop
  IsDegree3 : Fin n -> Prop
  IsDegree4 : Fin n -> Prop
  IsDegree5 : Fin n -> Prop
  IsDegree6 : Fin n -> Prop
  walk :
    OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6
  geometricAngleSum : Real
  forced_le_geometric :
    walk.counts.forcedBoundaryAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= walk.counts.polygonAngleSum
  Subpolygon : Type u
  subpolygonData :
    Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G
  obstruction :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData
  planarBoundary_eq : obstruction.planarBoundary = D

namespace BoundaryWalkLemma6ObstructionSource

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The full-row Lemma 6 obstruction source produces the concrete W13
boundary-walk gap-negative output for the exact requested row. -/
noncomputable def toBoundaryWalkGapNegativeCoverageOutput
    (S : BoundaryWalkLemma6ObstructionSource D) :
    BoundaryWalkGapNegativeCoverageOutput D := by
  cases S with
  | mk P IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6
      walk geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData obstruction planarBoundary_eq =>
      exact
        BoundaryWalkGapNegativeCoverageOutput.ofBoundaryWalkLemma6Obstruction
          (D := D) obstruction planarBoundary_eq

/-- Nonempty form of the strict full-row source to W13 output bridge. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutput
    (S : BoundaryWalkLemma6ObstructionSource D) :
    Nonempty (BoundaryWalkGapNegativeCoverageOutput D) :=
  Nonempty.intro S.toBoundaryWalkGapNegativeCoverageOutput

/-- Constructor from an actual full boundary-walk Lemma 6 obstruction and the
row equality requested downstream. -/
noncomputable def ofBoundaryWalkLemma6Obstruction
    {P : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (planarBoundary_eq : O.planarBoundary = D) :
    BoundaryWalkLemma6ObstructionSource D where
  P := P
  IsTriangle := IsTriangle
  IsNontriangle := IsNontriangle
  IsDegree3 := IsDegree3
  IsDegree4 := IsDegree4
  IsDegree5 := IsDegree5
  IsDegree6 := IsDegree6
  walk := walk
  geometricAngleSum := geometricAngleSum
  forced_le_geometric := forced_le_geometric
  geometric_le_polygon := geometric_le_polygon
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData
  obstruction := O
  planarBoundary_eq := planarBoundary_eq

end BoundaryWalkLemma6ObstructionSource

/-! ## Long-arc source fields plus Lemma 6/Lemma 7 coverage -/

/-- Long-arc source fields before the Lemma 6/Lemma 7 coverage inequality has
been inserted. -/
structure BoundaryLongArcSourceFields
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  LongArc : Type
  longArcFintype : Fintype LongArc
  concave : LongArc -> Prop
  concaveLongArcFintype : Fintype {a : LongArc // concave a}
  concaveLongArcCount_le_boundaryConcaveCount :
    @Fintype.card {a : LongArc // concave a} concaveLongArcFintype <=
      D.outerBoundaryCounts.B
  rawTurn : LongArc -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : LongArc,
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k
  concave_iff :
    forall a : LongArc, concave a <-> Real.pi / 3 <= totalTurn (rawTurn a)

namespace BoundaryLongArcSourceFields

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The concrete number of supplied long arcs. -/
def longArcCount (F : BoundaryLongArcSourceFields D) : Nat :=
  @Fintype.card F.LongArc F.longArcFintype

/-- Insert the Lemma 6/Lemma 7 coverage inequality into the existing
long-arc count-gap input record. -/
def toBoundaryLongArcExistenceFields
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D where
  LongArc := F.LongArc
  longArcFintype := F.longArcFintype
  concave := F.concave
  concaveLongArcFintype := F.concaveLongArcFintype
  concaveLongArcCount_le_boundaryConcaveCount :=
    F.concaveLongArcCount_le_boundaryConcaveCount
  degreeThree_le_negativeCount_add_longArcCount := by
    have hcoverage :
        D.outerBoundaryCounts.d3 <=
          D.outerBoundaryCounts.negativeCount + F.longArcCount :=
      C.degreeThree_le_negativeCount_add_longArcCount
    simpa [longArcCount] using hcoverage
  rawTurn := F.rawTurn
  rawTurn_nonnegative_on_arc := F.rawTurn_nonnegative_on_arc
  concave_iff := F.concave_iff

/-- The full existing count-gap-to-M8 route, built from Lemma 6/Lemma 7
coverage plus the long-arc source fields. -/
def toBoundaryCountGapToM8TurnBounds
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      (F.toBoundaryLongArcExistenceFields C) :=
  LongArcGapConcrete.BoundaryCountGapToM8TurnBounds.ofBoundaryLongArcExistenceFields
    (F.toBoundaryLongArcExistenceFields C)

/-- Boundary-attached nonconcave-arc budget data selected by the long-arc
count gap. -/
def toNonconcaveArcBoundaryBudgetData
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  (F.toBoundaryLongArcExistenceFields C).toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (F : BoundaryLongArcSourceFields D)
    (C : GapNegativeCoverageData D F.longArcCount) :
    (F.toNonconcaveArcBoundaryBudgetData C).planarBoundary = D :=
  rfl

end BoundaryLongArcSourceFields

/-- A reusable package combining long-arc fields with the Lemma 6/Lemma 7
coverage data required by the count-gap route. -/
structure BoundaryLongArcGapNegativePackage
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  source : BoundaryLongArcSourceFields D
  coverage : GapNegativeCoverageData D source.longArcCount

namespace BoundaryLongArcGapNegativePackage

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The packaged Lemma 6/Lemma 7 coverage inequality. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (Q : BoundaryLongArcGapNegativePackage D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + Q.source.longArcCount :=
  Q.coverage.degreeThree_le_negativeCount_add_longArcCount

/-- Existing long-arc count-gap fields produced by the package. -/
def toBoundaryLongArcExistenceFields
    (Q : BoundaryLongArcGapNegativePackage D) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D :=
  Q.source.toBoundaryLongArcExistenceFields Q.coverage

/-- Existing long-arc gap route produced by the package. -/
def toBoundaryCountGapToM8TurnBounds
    (Q : BoundaryLongArcGapNegativePackage D) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      Q.toBoundaryLongArcExistenceFields :=
  Q.source.toBoundaryCountGapToM8TurnBounds Q.coverage

/-- Boundary-attached nonconcave-arc budget selected by the package. -/
def toNonconcaveArcBoundaryBudgetData
    (Q : BoundaryLongArcGapNegativePackage D) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  Q.source.toNonconcaveArcBoundaryBudgetData Q.coverage

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (Q : BoundaryLongArcGapNegativePackage D) :
    Q.toNonconcaveArcBoundaryBudgetData.planarBoundary = D :=
  rfl

/-- Attach a boundary-walk coverage output to long-arc source fields after
identifying their long-arc counts. -/
def ofBoundaryWalkGapNegativeCoverageOutput
    (source : BoundaryLongArcSourceFields D)
    (coverage : BoundaryWalkGapNegativeCoverageOutput D)
    (longArcCount_eq : coverage.longArcCount = source.longArcCount) :
    BoundaryLongArcGapNegativePackage D where
  source := source
  coverage :=
    coverage.toGapNegativeCoverageDataOfLongArcCountEq longArcCount_eq

end BoundaryLongArcGapNegativePackage

/-! ## Boundary-walk package -/

/-- Boundary-walk specialized package: Lemma 6 supplies negative-after-gap
certificates, Lemma 7 supplies terminal coverage, and the result fills the
long-arc count-gap input. -/
structure BoundaryWalkLongArcGapNegativePackage
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) where
  source : BoundaryLongArcSourceFields O.planarBoundary
  gapInduction : BoundaryWalkGapNegativeInductionData O
  degreeThree_eq_length_succ :
    O.planarBoundary.outerBoundaryCounts.d3 = gapInduction.length + 1
  terminal_count_le_negativeCount_add_longArcCount :
    gapInduction.count gapInduction.length <=
      O.planarBoundary.outerBoundaryCounts.negativeCount + source.longArcCount

namespace BoundaryWalkLongArcGapNegativePackage

variable
  {O :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}

/-- Generic coverage data extracted from the boundary-walk package. -/
def coverage
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    GapNegativeCoverageData O.planarBoundary Q.source.longArcCount :=
  Q.gapInduction.toGapNegativeCoverageData
    Q.degreeThree_eq_length_succ
    Q.terminal_count_le_negativeCount_add_longArcCount

/-- Forget the boundary-walk indices after extracting the checked coverage
inequality. -/
def toBoundaryLongArcGapNegativePackage
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    BoundaryLongArcGapNegativePackage O.planarBoundary where
  source := Q.source
  coverage := Q.coverage

/-- Boundary-walk Lemma 6/Lemma 7 coverage inequality. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount +
        Q.source.longArcCount :=
  Q.coverage.degreeThree_le_negativeCount_add_longArcCount

/-- Existing long-arc count-gap fields produced by the boundary-walk package. -/
def toBoundaryLongArcExistenceFields
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      O.planarBoundary :=
  Q.source.toBoundaryLongArcExistenceFields Q.coverage

/-- Existing long-arc gap route produced by the boundary-walk package. -/
def toBoundaryCountGapToM8TurnBounds
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      Q.toBoundaryLongArcExistenceFields :=
  Q.source.toBoundaryCountGapToM8TurnBounds Q.coverage

/-- Boundary-attached nonconcave-arc budget selected by the boundary-walk
package. -/
def toNonconcaveArcBoundaryBudgetData
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  Q.source.toNonconcaveArcBoundaryBudgetData Q.coverage

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (Q : BoundaryWalkLongArcGapNegativePackage O) :
    Q.toNonconcaveArcBoundaryBudgetData.planarBoundary = O.planarBoundary :=
  rfl

end BoundaryWalkLongArcGapNegativePackage

/-! ## Classified-boundary coverage and raw-turn constructors -/

namespace ClassifiedBoundary

open BoundaryWalkClassificationConcrete

variable {P : OuterBoundaryCore G}
variable {D : OuterBoundaryClassificationInputs P}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  D.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= D.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-! ### Real raw-turn long-arc packages -/

/-- The actual classified long-arc subtype, equipped with caller-supplied raw
turns, is a W13 long-arc source.  Concavity is interpreted by the raw total-turn
threshold, so no artificial turn rows are introduced. -/
noncomputable def boundaryLongArcSourceFieldsOfRawTurns
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcSourceFields
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) := by
  classical
  exact
    { LongArc := D.longArcIndices
      longArcFintype := inferInstance
      concave :=
        BoundaryPartitionInstantiation.ClassifiedBoundary.rawTurnConcave
          D rawTurn
      concaveLongArcFintype := inferInstance
      concaveLongArcCount_le_boundaryConcaveCount := by
        change
          @Fintype.card
              {a : D.longArcIndices //
                BoundaryPartitionInstantiation.ClassifiedBoundary.rawTurnConcave
                  D rawTurn a}
              inferInstance <= D.counts.B
        exact
          BoundaryPartitionInstantiation.ClassifiedBoundary.concaveLongArcCount_le_counts_B_of_subtype
            D
            (BoundaryPartitionInstantiation.ClassifiedBoundary.rawTurnConcave
              D rawTurn)
      rawTurn := rawTurn
      rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc
      concave_iff := by
        intro a
        rfl }

/-- Coverage data for the actual classified long-arc subtype, together with
caller-supplied raw turns, gives the reusable W13 long-arc/gap-negative
package. -/
noncomputable def boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurns
    (coverage :
      GapNegativeCoverageData
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        (@Fintype.card D.longArcIndices inferInstance))
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcGapNegativePackage
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) where
  source :=
    boundaryLongArcSourceFieldsOfRawTurns
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      rawTurn rawTurn_nonnegative_on_arc
  coverage := by
    change
      GapNegativeCoverageData
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        (@Fintype.card D.longArcIndices inferInstance)
    exact coverage

/-- Boundary-walk coverage outputs plus the actual classified raw-turn rows
produce the reusable W13 long-arc/gap-negative package.  The explicit count
equality is the non-circular identification between the coverage output's
long-arc count and the classified boundary's concrete `longArcIndices`. -/
noncomputable def boundaryLongArcGapNegativePackageOfBoundaryWalkGapNegativeCoverageOutputAndRawTurns
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData))
    (longArcCount_eq :
      coverage.longArcCount =
        @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcGapNegativePackage
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    (coverage.toGapNegativeCoverageDataOfLongArcCountEq longArcCount_eq)
    rawTurn rawTurn_nonnegative_on_arc

/-- Lemma 6/7 coverage data for the actual classified long-arc subtype gives
the concrete coverage inequality required by the classified-boundary Lemma 5
constructor. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount_of_gapNegativeCoverageData
    (C :
      GapNegativeCoverageData
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        (@Fintype.card D.longArcIndices inferInstance)) :
    D.counts.d3 <=
      D.counts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance := by
  change
    (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData).outerBoundaryCounts.d3 <=
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData).outerBoundaryCounts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance
  exact C.degreeThree_le_negativeCount_add_longArcCount

/-- Boundary-walk Lemma 6/7 induction data for the actual classified boundary
gives the concrete coverage inequality required by the classified-boundary
Lemma 5 constructor. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryWalkGapNegativeInduction
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance) :
    D.counts.d3 <=
      D.counts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance := by
  have hdegree :
      O.planarBoundary.outerBoundaryCounts.d3 = B.length + 1 := by
    change D.counts.d3 = B.length + 1
    exact degreeThree_eq_length_succ
  have hterminal :
      B.count B.length <=
        O.planarBoundary.outerBoundaryCounts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance := by
    change
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance
    exact terminal_count_le_negativeCount_add_longArcIndexCount
  change
    O.planarBoundary.outerBoundaryCounts.d3 <=
      O.planarBoundary.outerBoundaryCounts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance
  exact
    B.degreeThree_le_negativeCount_add_longArcCount
      (longArcCount := @Fintype.card D.longArcIndices inferInstance)
      hdegree hterminal

/-- Positive classified-boundary row output for the selected-frame coverage
source: a Lemma 6 obstruction on the actual classified boundary walk produces
the concrete `BoundaryWalkGapNegativeCoverageOutput` for the same planar row. -/
noncomputable def boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryWalkGapNegativeCoverageOutput
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  BoundaryWalkGapNegativeCoverageOutput.ofBoundaryWalkLemma6Obstruction
    (D :=
      D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
    O rfl

/-- Nonempty form of the positive classified-boundary row output. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    Nonempty
      (BoundaryWalkGapNegativeCoverageOutput
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)) :=
  Nonempty.intro
    (boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)

/-- A Lemma 6 obstruction on the actual classified boundary walk, together
with real raw turns on the classified long-arc indices, gives the reusable W13
long-arc/gap-negative package without an extra count-equality premise. -/
noncomputable def boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcGapNegativePackage
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  boundaryLongArcGapNegativePackageOfBoundaryWalkGapNegativeCoverageOutputAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    (boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    (by
      change D.counts.B = @Fintype.card D.longArcIndices inferInstance
      exact D.counts_B)
    rawTurn rawTurn_nonnegative_on_arc

/-- Minimal raw-turn rows for the classified long-arc carrier.  This is the
import-cycle-free target shape that W11-style boundary-turn rows can forget to:
only the actual turn family and pointwise nonnegativity live here, while
Lemma 6/7 coverage remains a separate W13 input. -/
structure BoundaryLongArcRawTurnRows
    (D0 : OuterBoundaryClassificationInputs P) where
  rawTurn : D0.longArcIndices -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : D0.longArcIndices,
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k

namespace BoundaryLongArcRawTurnRows

variable {D0 : OuterBoundaryClassificationInputs P}

/-- Build classified long-arc raw-turn rows from an actual turn family and its
pointwise nonnegativity on the thirteen turn slots. -/
def ofRawTurns
    (rawTurn : D0.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D0.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcRawTurnRows D0 where
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc

@[simp]
theorem ofRawTurns_rawTurn
    (rawTurn : D0.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D0.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    (ofRawTurns (D0 := D0) rawTurn rawTurn_nonnegative_on_arc).rawTurn =
      rawTurn :=
  rfl

theorem ofRawTurns_rawTurn_nonnegative_on_arc
    (rawTurn : D0.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D0.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k)
    (a : D0.longArcIndices) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    0 <=
      (ofRawTurns (D0 := D0) rawTurn
        rawTurn_nonnegative_on_arc).rawTurn a k :=
  rawTurn_nonnegative_on_arc a k hk

/-- Actual outer-boundary turn vertices give the classified W13 raw-turn rows.

The pointwise nonnegativity is consumed from
`LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.classifiedW13RawTurnAndCarrierRowsOfOuterBoundaryCoreTurnVertex`,
so this is the import-safe bridge from real boundary turn vertices to the W13
classified carrier, not a detached adapter. -/
noncomputable def ofOuterBoundaryCoreTurnVertex
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (degreeThree_le_negativeCount_add_longArcIndexCount :
      D0.counts.d3 <=
        D0.counts.negativeCount +
          @Fintype.card D0.longArcIndices inferInstance)
    (h3 : 3 <= P.outerCycle.length)
    (turnVertex : D0.longArcIndices -> Nat -> Fin P.outerCycle.length) :
    BoundaryLongArcRawTurnRows D0 := by
  let carrierRows :=
    LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex
      (D := D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
      P h3 D0.longArcIndices
      (by
        change
          @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
        exact D0.counts_B.symm)
      (by
        change
          D0.counts.d3 <= D0.counts.negativeCount +
            @Fintype.card D0.longArcIndices inferInstance
        exact degreeThree_le_negativeCount_add_longArcIndexCount)
      turnVertex
  have hclassified :=
    LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.classifiedW13RawTurnAndCarrierRowsOfOuterBoundaryCoreTurnVertex
      (D := D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
      P h3 D0.longArcIndices
      (by
        change
          @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
        exact D0.counts_B.symm)
      (by
        change
          D0.counts.d3 <= D0.counts.negativeCount +
            @Fintype.card D0.longArcIndices inferInstance
        exact degreeThree_le_negativeCount_add_longArcIndexCount)
      turnVertex
  refine ofRawTurns (D0 := D0) carrierRows.rawTurn ?_
  intro a k hk
  simpa [carrierRows] using hclassified.2.2.2.1 a k hk

/-- On the thirteen turn slots, the raw rows from actual outer-boundary turn
vertices are exactly the corresponding concrete boundary-angle values. -/
theorem ofOuterBoundaryCoreTurnVertex_rawTurn_of_mem
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (degreeThree_le_negativeCount_add_longArcIndexCount :
      D0.counts.d3 <=
        D0.counts.negativeCount +
          @Fintype.card D0.longArcIndices inferInstance)
    (h3 : 3 <= P.outerCycle.length)
    (turnVertex : D0.longArcIndices -> Nat -> Fin P.outerCycle.length)
    (a : D0.longArcIndices) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    (ofOuterBoundaryCoreTurnVertex
      (D0 := D0) (angleSum := angleSum)
      (forced_le := forced_le) (angle_le_polygon := angle_le_polygon)
      (Subpolygon0 := Subpolygon0) (subpolygonRows := subpolygonRows)
      degreeThree_le_negativeCount_add_longArcIndexCount
      h3 turnVertex).rawTurn a k =
        (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
          P h3 turnVertex a k).value := by
  let carrierRows :=
    LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex
      (D := D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
      P h3 D0.longArcIndices
      (by
        change
          @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
        exact D0.counts_B.symm)
      (by
        change
          D0.counts.d3 <= D0.counts.negativeCount +
            @Fintype.card D0.longArcIndices inferInstance
        exact degreeThree_le_negativeCount_add_longArcIndexCount)
      turnVertex
  have hclassified :=
    LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.classifiedW13RawTurnAndCarrierRowsOfOuterBoundaryCoreTurnVertex
      (D := D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
      P h3 D0.longArcIndices
      (by
        change
          @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
        exact D0.counts_B.symm)
      (by
        change
          D0.counts.d3 <= D0.counts.negativeCount +
            @Fintype.card D0.longArcIndices inferInstance
        exact degreeThree_le_negativeCount_add_longArcIndexCount)
      turnVertex
  change carrierRows.rawTurn a k =
    (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
      P h3 turnVertex a k).value
  simpa [carrierRows] using hclassified.2.2.1 a k hk

/-- Forget the bundled row to the source fields used by the long-arc route. -/
noncomputable def toSourceFields
    (R : BoundaryLongArcRawTurnRows D0)
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G} :
    BoundaryLongArcSourceFields
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :=
  boundaryLongArcSourceFieldsOfRawTurns
    (D := D0) (geometricAngleSum := angleSum)
    (forced_le_geometric := forced_le)
    (geometric_le_polygon := angle_le_polygon)
    (Subpolygon := Subpolygon0) (subpolygonData := subpolygonRows)
    R.rawTurn R.rawTurn_nonnegative_on_arc

end BoundaryLongArcRawTurnRows

/-- Lemma 6/7 coverage plus the real raw-turn rows for the same classified
long-arc carrier.  The equality field is the explicit handoff between a
coverage output's abstract long-arc count and the concrete classified
`longArcIndices` carrier. -/
structure BoundaryLongArcGapNegativeRows
    (D0 : OuterBoundaryClassificationInputs P)
    (angleSum : Real)
    (forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum)
    (angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum)
    (Subpolygon0 : Type u)
    (subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  coverage :
    BoundaryWalkGapNegativeCoverageOutput
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
  longArcCount_eq :
    coverage.longArcCount = @Fintype.card D0.longArcIndices inferInstance
  rawRows : BoundaryLongArcRawTurnRows D0

namespace BoundaryLongArcGapNegativeRows

variable {D0 : OuterBoundaryClassificationInputs P}

/-- Direct constructor from the current boundary-walk coverage output and the
real raw-turn rows on the same classified long-arc carrier. -/
noncomputable def ofCoverageOutput
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D0.toPlanarBoundaryData angleSum forced_le
          angle_le_polygon Subpolygon0 subpolygonRows))
    (longArcCount_eq :
      coverage.longArcCount = @Fintype.card D0.longArcIndices inferInstance)
    (rawRows : BoundaryLongArcRawTurnRows D0) :
    BoundaryLongArcGapNegativeRows D0 angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows where
  coverage := coverage
  longArcCount_eq := longArcCount_eq
  rawRows := rawRows

/-- Direct constructor from boundary-walk coverage output and actual W11-style
raw turns on the classified long-arc carrier. -/
noncomputable def ofCoverageOutputAndRawTurns
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D0.toPlanarBoundaryData angleSum forced_le
          angle_le_polygon Subpolygon0 subpolygonRows))
    (longArcCount_eq :
      coverage.longArcCount = @Fintype.card D0.longArcIndices inferInstance)
    (rawTurn : D0.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D0.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcGapNegativeRows D0 angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows :=
  ofCoverageOutput coverage longArcCount_eq
    (BoundaryLongArcRawTurnRows.ofRawTurns
      (D0 := D0) rawTurn rawTurn_nonnegative_on_arc)

/-- Nonempty form of the direct constructor from boundary-walk coverage output
and real raw-turn rows. -/
theorem nonempty_ofCoverageOutput
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D0.toPlanarBoundaryData angleSum forced_le
          angle_le_polygon Subpolygon0 subpolygonRows))
    (longArcCount_eq :
      coverage.longArcCount = @Fintype.card D0.longArcIndices inferInstance)
    (rawRows : BoundaryLongArcRawTurnRows D0) :
    Nonempty
      (BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :=
  Nonempty.intro
    (ofCoverageOutput coverage longArcCount_eq rawRows)

/-- The bundled coverage output, transported to the concrete classified
long-arc count. -/
def toGapNegativeCoverageData
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    GapNegativeCoverageData
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
      (@Fintype.card D0.longArcIndices inferInstance) :=
  R.coverage.toGapNegativeCoverageDataOfLongArcCountEq R.longArcCount_eq

/-- Boundary-walk coverage plus actual outer-boundary turn vertices produce
the positive W13 gap-negative row package on the classified long-arc carrier. -/
noncomputable def ofCoverageOutputAndOuterBoundaryCoreTurnVertex
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D0.toPlanarBoundaryData angleSum forced_le
          angle_le_polygon Subpolygon0 subpolygonRows))
    (longArcCount_eq :
      coverage.longArcCount = @Fintype.card D0.longArcIndices inferInstance)
    (h3 : 3 <= P.outerCycle.length)
    (turnVertex : D0.longArcIndices -> Nat -> Fin P.outerCycle.length) :
    BoundaryLongArcGapNegativeRows D0 angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows :=
  ofCoverageOutput coverage longArcCount_eq
    (BoundaryLongArcRawTurnRows.ofOuterBoundaryCoreTurnVertex
      (D0 := D0) (angleSum := angleSum)
      (forced_le := forced_le) (angle_le_polygon := angle_le_polygon)
      (Subpolygon0 := Subpolygon0) (subpolygonRows := subpolygonRows)
      (coverage.toGapNegativeCoverageDataOfLongArcCountEq
        longArcCount_eq).degreeThree_le_negativeCount_add_longArcCount
      h3 turnVertex)

/-- The explicit count identity against the boundary `B` count carried by the
classified boundary row. -/
theorem longArcCount_eq_counts_B
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.coverage.longArcCount = D0.counts.B := by
  rw [R.longArcCount_eq]
  exact D0.counts_B.symm

/-- The concrete Lemma 6/7 coverage inequality on the classified long-arc
carrier. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    D0.counts.d3 <=
      D0.counts.negativeCount +
        @Fintype.card D0.longArcIndices inferInstance := by
  change
    (D0.toPlanarBoundaryData angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows).outerBoundaryCounts.d3 <=
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows).outerBoundaryCounts.negativeCount +
        @Fintype.card D0.longArcIndices inferInstance
  exact R.toGapNegativeCoverageData.degreeThree_le_negativeCount_add_longArcCount

/-- The same concrete coverage inequality, using the boundary `B` count. -/
theorem degreeThree_le_negativeCount_add_counts_B
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    D0.counts.d3 <= D0.counts.negativeCount + D0.counts.B := by
  have h := R.degreeThree_le_negativeCount_add_longArcIndexCount
  rw [← D0.counts_B] at h
  exact h

/-- Pointwise nonnegativity of the real raw turns carried by the W13 rows. -/
theorem rawTurn_nonnegative_on_arc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
    (a : D0.longArcIndices) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    0 <= R.rawRows.rawTurn a k :=
  R.rawRows.rawTurn_nonnegative_on_arc a k hk

/-- W13 bundled rows are already the concrete carrier/raw-turn source rows used
by the long-arc existence constructor: the carrier is exactly
`D0.longArcIndices`, the count identity is `counts_B`, coverage is the Lemma
6/7 inequality above, and the raw turns are the stored real raw-turn rows. -/
noncomputable def toBoundaryLongArcCarrierRawTurnRows
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows.{u}
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :=
  LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows.ofFiniteCarrierRawTurns
    (D := D0.toPlanarBoundaryData angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows)
    D0.longArcIndices
    (by
      change
        @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
      exact D0.counts_B.symm)
    (by
      change
        D0.counts.d3 <= D0.counts.negativeCount +
          @Fintype.card D0.longArcIndices inferInstance
      exact R.degreeThree_le_negativeCount_add_longArcIndexCount)
    R.rawRows.rawTurn
    R.rawRows.rawTurn_nonnegative_on_arc

/-- The concrete carrier package produced by W13 rows uses exactly the
classified boundary's long-arc index type. -/
@[simp]
theorem toBoundaryLongArcCarrierRawTurnRows_LongArc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcCarrierRawTurnRows.LongArc = D0.longArcIndices :=
  rfl

/-- The concrete carrier package keeps the raw turn family supplied by the W13
rows. -/
@[simp]
theorem toBoundaryLongArcCarrierRawTurnRows_rawTurn
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcCarrierRawTurnRows.rawTurn =
      R.rawRows.rawTurn :=
  rfl

/-- The carrier-count field produced from W13 rows is the classified boundary
`B` count. -/
theorem toBoundaryLongArcCarrierRawTurnRows_longArcCount_eq_counts_B
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcCarrierRawTurnRows.longArcCount = D0.counts.B := by
  change @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
  exact D0.counts_B.symm

/-- W13 rows route the Lemma 6/7 coverage inequality into the concrete carrier
package with no carrier change. -/
theorem toBoundaryLongArcCarrierRawTurnRows_degreeThree_le
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    D0.counts.d3 <=
      D0.counts.negativeCount +
        R.toBoundaryLongArcCarrierRawTurnRows.longArcCount := by
  change
    D0.counts.d3 <= D0.counts.negativeCount +
      @Fintype.card D0.longArcIndices inferInstance
  exact R.degreeThree_le_negativeCount_add_longArcIndexCount

/-- Pointwise raw-turn nonnegativity is preserved by the concrete carrier
package projection. -/
theorem toBoundaryLongArcCarrierRawTurnRows_rawTurn_nonnegative_on_arc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
    (a : R.toBoundaryLongArcCarrierRawTurnRows.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    0 <= R.toBoundaryLongArcCarrierRawTurnRows.rawTurn a k :=
  R.toBoundaryLongArcCarrierRawTurnRows.rawTurn_nonnegative_on_arc a k hk

/-- Direct long-arc existence fields obtained from W13 rows through the
concrete carrier/raw-turn package. -/
noncomputable def toBoundaryLongArcExistenceFields
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :=
  R.toBoundaryLongArcCarrierRawTurnRows.toBoundaryLongArcExistenceFields

@[simp]
theorem toBoundaryLongArcExistenceFields_LongArc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcExistenceFields.LongArc = D0.longArcIndices :=
  rfl

@[simp]
theorem toBoundaryLongArcExistenceFields_rawTurn
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcExistenceFields.rawTurn = R.rawRows.rawTurn :=
  rfl

/-- The long-arc existence fields produced from W13 rows have long-arc count
equal to the classified boundary `B` count. -/
theorem toBoundaryLongArcExistenceFields_longArcCount_eq_counts_B
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcExistenceFields.longArcCount = D0.counts.B := by
  change @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
  exact D0.counts_B.symm

/-- The long-arc existence fields produced from W13 rows expose the same
Lemma 6/7 count coverage against the concrete classified long-arc carrier. -/
theorem toBoundaryLongArcExistenceFields_degreeThree_le
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    D0.counts.d3 <=
      D0.counts.negativeCount +
        R.toBoundaryLongArcExistenceFields.longArcCount := by
  change
    D0.counts.d3 <= D0.counts.negativeCount +
      @Fintype.card D0.longArcIndices inferInstance
  exact R.degreeThree_le_negativeCount_add_longArcIndexCount

/-- Pointwise nonnegativity is preserved all the way to the long-arc existence
fields produced from W13 rows. -/
theorem toBoundaryLongArcExistenceFields_rawTurn_nonnegative_on_arc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
    (a : R.toBoundaryLongArcExistenceFields.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    0 <= R.toBoundaryLongArcExistenceFields.rawTurn a k :=
  R.toBoundaryLongArcExistenceFields.rawTurn_nonnegative_on_arc a k hk

/-- Project the bundled W13 coverage/raw-turn rows to the exact package shape
consumed by the W24 long-arc-field bridge. -/
noncomputable def toBoundaryLongArcGapNegativePackage
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    BoundaryLongArcGapNegativePackage
      (D0.toPlanarBoundaryData angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :=
  boundaryLongArcGapNegativePackageOfBoundaryWalkGapNegativeCoverageOutputAndRawTurns
    (D := D0) (geometricAngleSum := angleSum)
    (forced_le_geometric := forced_le)
    (geometric_le_polygon := angle_le_polygon)
    (Subpolygon := Subpolygon0) (subpolygonData := subpolygonRows)
    R.coverage R.longArcCount_eq
    R.rawRows.rawTurn R.rawRows.rawTurn_nonnegative_on_arc

/-- The reusable W13 package produced from bundled rows keeps the classified
long-arc index carrier. -/
@[simp]
theorem toBoundaryLongArcGapNegativePackage_source_LongArc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcGapNegativePackage.source.LongArc =
      D0.longArcIndices :=
  rfl

/-- The reusable W13 package produced from bundled rows keeps the supplied
raw-turn family. -/
@[simp]
theorem toBoundaryLongArcGapNegativePackage_source_rawTurn
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcGapNegativePackage.source.rawTurn =
      R.rawRows.rawTurn :=
  rfl

/-- The reusable W13 package's source count is exactly the concrete classified
long-arc index cardinality. -/
theorem toBoundaryLongArcGapNegativePackage_source_longArcCount_eq_card
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcGapNegativePackage.source.longArcCount =
      @Fintype.card D0.longArcIndices inferInstance :=
  rfl

/-- The reusable W13 package's source count is the boundary `B` count by the
classified long-arc card identity. -/
theorem toBoundaryLongArcGapNegativePackage_source_longArcCount_eq_counts_B
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows) :
    R.toBoundaryLongArcGapNegativePackage.source.longArcCount =
      D0.counts.B := by
  change @Fintype.card D0.longArcIndices inferInstance = D0.counts.B
  exact D0.counts_B.symm

/-- Raw-turn nonnegativity routes through the reusable W13 package without
changing the carrier or turn function. -/
theorem toBoundaryLongArcGapNegativePackage_source_rawTurn_nonnegative_on_arc
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (R :
      BoundaryLongArcGapNegativeRows D0 angleSum forced_le
        angle_le_polygon Subpolygon0 subpolygonRows)
    (a : R.toBoundaryLongArcGapNegativePackage.source.LongArc)
    (k : Nat) (hk : Membership.mem turnIndexSet k) :
    0 <= R.toBoundaryLongArcGapNegativePackage.source.rawTurn a k :=
  R.toBoundaryLongArcGapNegativePackage.source.rawTurn_nonnegative_on_arc
    a k hk

/-- A Lemma 6 obstruction supplies the coverage/count-equality side, so only
the real raw-turn rows remain as input. -/
noncomputable def ofLemma6Obstruction
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (O :
      BoundaryWalkLemma6Obstruction
        D0.toOuterBoundaryWalkBookkeeping angleSum
        forced_le angle_le_polygon Subpolygon0 subpolygonRows)
    (rawRows : BoundaryLongArcRawTurnRows D0) :
    BoundaryLongArcGapNegativeRows D0 angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows where
  coverage :=
    boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
      (D := D0) (geometricAngleSum := angleSum)
      (forced_le_geometric := forced_le)
      (geometric_le_polygon := angle_le_polygon)
      (Subpolygon := Subpolygon0) (subpolygonData := subpolygonRows) O
  longArcCount_eq := by
    change D0.counts.B = @Fintype.card D0.longArcIndices inferInstance
    exact D0.counts_B
  rawRows := rawRows

/-- A Lemma 6 obstruction plus actual raw turns supplies both the W13 coverage
row and the raw-turn rows, discharging the count bridge by `counts_B`. -/
noncomputable def ofLemma6ObstructionAndRawTurns
    {angleSum : Real}
    {forced_le :
      D0.counts.forcedBoundaryAngleSum <= angleSum}
    {angle_le_polygon :
      angleSum <= D0.counts.polygonAngleSum}
    {Subpolygon0 : Type u}
    {subpolygonRows :
      Subpolygon0 -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}
    (O :
      BoundaryWalkLemma6Obstruction
        D0.toOuterBoundaryWalkBookkeeping angleSum
        forced_le angle_le_polygon Subpolygon0 subpolygonRows)
    (rawTurn : D0.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D0.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcGapNegativeRows D0 angleSum forced_le
      angle_le_polygon Subpolygon0 subpolygonRows :=
  ofLemma6Obstruction O
    (BoundaryLongArcRawTurnRows.ofRawTurns
      (D0 := D0) rawTurn rawTurn_nonnegative_on_arc)

end BoundaryLongArcGapNegativeRows

/-- Boundary-walk coverage output plus real raw-turn rows produces the bundled
W13 gap-negative rows on the classified carrier. -/
noncomputable def boundaryLongArcGapNegativeRowsOfCoverageOutputAndRawTurnRows
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData))
    (longArcCount_eq :
      coverage.longArcCount = @Fintype.card D.longArcIndices inferInstance)
    (rawRows : BoundaryLongArcRawTurnRows D) :
    BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData :=
  BoundaryLongArcGapNegativeRows.ofCoverageOutput
    (D0 := D) (angleSum := geometricAngleSum)
    (forced_le := forced_le_geometric)
    (angle_le_polygon := geometric_le_polygon)
    (Subpolygon0 := Subpolygon) (subpolygonRows := subpolygonData)
    coverage longArcCount_eq rawRows

/-- Nonempty form of the coverage-output/raw-turn row constructor. -/
theorem nonempty_boundaryLongArcGapNegativeRowsOfCoverageOutputAndRawTurnRows
    (coverage :
      BoundaryWalkGapNegativeCoverageOutput
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData))
    (longArcCount_eq :
      coverage.longArcCount = @Fintype.card D.longArcIndices inferInstance)
    (rawRows : BoundaryLongArcRawTurnRows D) :
    Nonempty
      (BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  BoundaryLongArcGapNegativeRows.nonempty_ofCoverageOutput
    (D0 := D) (angleSum := geometricAngleSum)
    (forced_le := forced_le_geometric)
    (angle_le_polygon := geometric_le_polygon)
    (Subpolygon0 := Subpolygon) (subpolygonRows := subpolygonData)
    coverage longArcCount_eq rawRows

/-- Bundled-row version of
`boundaryLongArcGapNegativePackageOfBoundaryWalkGapNegativeCoverageOutputAndRawTurns`. -/
noncomputable def boundaryLongArcGapNegativePackageOfRows
    (R :
      BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryLongArcGapNegativePackage
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  R.toBoundaryLongArcGapNegativePackage

/-- Row-bundled version of
`boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurns`.

This is the direct handoff used when the caller already has the actual
classified raw-turn rows and the Lemma 6/Lemma 7 coverage data for the same
classified long-arc carrier. -/
noncomputable def boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurnRows
    (coverage :
      GapNegativeCoverageData
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        (@Fintype.card D.longArcIndices inferInstance))
    (rawRows : BoundaryLongArcRawTurnRows D) :
    BoundaryLongArcGapNegativePackage
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    coverage rawRows.rawTurn rawRows.rawTurn_nonnegative_on_arc

/-- Bundled raw-row version of
`boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurns`. -/
noncomputable def boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurnRows
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (rawRows : BoundaryLongArcRawTurnRows D) :
    BoundaryLongArcGapNegativePackage
      (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :=
  (BoundaryLongArcGapNegativeRows.ofLemma6Obstruction
    (D0 := D) (angleSum := geometricAngleSum)
    (forced_le := forced_le_geometric)
    (angle_le_polygon := geometric_le_polygon)
    (Subpolygon0 := Subpolygon) (subpolygonRows := subpolygonData)
    O rawRows).toBoundaryLongArcGapNegativePackage

/-- Excluding every strict S4 gap/triangle/degree-3-or-4 row gives the direct
E14 negative-after-gap fact on the same full classified boundary walk. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_no_boundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (hno :
      forall k : Fin Pcfg.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k)) :
    BoundaryWalkLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping := by
  intro k hgap
  by_contra hnegative
  rcases
      BoundaryWalkNegativeAfterGapAt.localData_of_not
        (walk := classification.toOuterBoundaryWalkBookkeeping.data)
        (k := k) hnegative with
    ⟨htriangle, hdegree⟩
  exact
    hno k
      (OuterBoundaryClassificationInputs.boundaryGapTriangleDegree34RowOfClassifications
        classification k hgap.1 (by simpa using hgap.2)
        htriangle hdegree)

/-- No strict S4 rows produce the concrete selected-frame coverage output
directly from the classified boundary walk, without first manufacturing
carrier rows. -/
noncomputable def boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (hno :
      forall k : Fin Pcfg.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k)) :
    BoundaryWalkGapNegativeCoverageOutput
      (classification.toPlanarBoundaryData geometricAngleSum
        forced_le_geometric geometric_le_polygon F.Subpolygon
        (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)) :=
  boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
    (D := classification)
    (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := F.Subpolygon)
    (subpolygonData :=
      fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)
    (BoundaryWalkLemma6Obstruction.ofNegativeAfterFact
      (boundaryWalkLemma6E14NegativeAfterFact_of_no_boundaryGapTriangleDegree34Rows
        classification hno))

/-- Nonempty selected-frame row form of the direct no-gap boundary-walk
coverage output. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (hno :
      forall k : Fin Pcfg.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k)) :
    Nonempty
      (BoundaryWalkGapNegativeCoverageOutput
        (classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData))) :=
  Nonempty.intro
    (boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon hno)

/-- No strict boundary gap/triangle/degree-3-or-4 rows give the real W13
gap-negative rows once the classified raw-turn rows are supplied.  The count
identity is the concrete classified-boundary `counts_B` identity, not an
extra downstream equivalence. -/
noncomputable def boundaryLongArcGapNegativeRowsOfNoBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (hno :
      forall k : Fin Pcfg.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k))
    (rawRows : BoundaryLongArcRawTurnRows classification) :
    BoundaryLongArcGapNegativeRows
      classification geometricAngleSum forced_le_geometric
      geometric_le_polygon F.Subpolygon
      (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData) :=
  boundaryLongArcGapNegativeRowsOfCoverageOutputAndRawTurnRows
    (D := classification) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := F.Subpolygon)
    (subpolygonData :=
      fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)
    (boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon hno)
    (by
      change
        classification.counts.B =
          @Fintype.card classification.longArcIndices inferInstance
      exact classification.counts_B)
    rawRows

/-- Nonempty form of the no-strict-gap W13 gap-negative row source. -/
theorem nonempty_boundaryLongArcGapNegativeRowsOfNoBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (hno :
      forall k : Fin Pcfg.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k))
    (rawRows : BoundaryLongArcRawTurnRows classification) :
    Nonempty
      (BoundaryLongArcGapNegativeRows
        classification geometricAngleSum forced_le_geometric
        geometric_le_polygon F.Subpolygon
        (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)) :=
  Nonempty.intro
    (boundaryLongArcGapNegativeRowsOfNoBoundaryGapTriangleDegree34Rows
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon hno rawRows)

/-- Transport form of the direct no-gap boundary-walk output, matching the
exact downstream planar-boundary row requested by selected-frame coverage. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows_eq
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (hno :
      forall k : Fin Pcfg.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k))
    {Drow :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (hD :
      classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData) =
        Drow) :
    Nonempty (BoundaryWalkGapNegativeCoverageOutput Drow) := by
  cases hD
  exact
    nonempty_boundaryWalkGapNegativeCoverageOutputOfNoBoundaryGapTriangleDegree34Rows
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon hno

/-- The exact local strict-count source for the actual classified boundary
walk produces the concrete selected-frame coverage output row. -/
noncomputable def boundaryWalkGapNegativeCoverageOutputOfConcreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (H :
      ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12.LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
        Pcfg classification.longArc F) :
    BoundaryWalkGapNegativeCoverageOutput
      (classification.toPlanarBoundaryData geometricAngleSum
        forced_le_geometric geometric_le_polygon F.Subpolygon
        (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)) :=
  boundaryWalkGapNegativeCoverageOutputOfLemma6Obstruction
    (D := classification)
    (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := F.Subpolygon)
    (subpolygonData :=
      fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)
    (ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12.boundaryWalkLemma6Obstruction_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon H)

/-- A single exact strict carrier in the actual classified core-subpolygon
family produces the concrete selected-frame boundary-walk coverage output. -/
noncomputable def boundaryWalkGapNegativeCoverageOutputOfCoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (carrier : SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F) :
    BoundaryWalkGapNegativeCoverageOutput
      (classification.toPlanarBoundaryData geometricAngleSum
        forced_le_geometric geometric_le_polygon F.Subpolygon
        (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)) :=
  boundaryWalkGapNegativeCoverageOutputOfConcreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    classification F geometricAngleSum forced_le_geometric geometric_le_polygon
    (ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12.localGapTriangleDegree34CoreSubpolygonCarrierCountData_of_coreSubpolygonCarrierCountData
      (Pcfg := Pcfg) (longArc := classification.longArc) carrier)

/-- Nonempty selected-frame row form of the strict-count boundary-walk output. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfConcreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (H :
      ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12.LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
        Pcfg classification.longArc F) :
    Nonempty
      (BoundaryWalkGapNegativeCoverageOutput
        (classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData))) :=
  Nonempty.intro
    (boundaryWalkGapNegativeCoverageOutputOfConcreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon H)

/-- Nonempty selected-frame row form of the direct exact strict-carrier
boundary-walk output. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfCoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (carrier : SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F) :
    Nonempty
      (BoundaryWalkGapNegativeCoverageOutput
        (classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData))) :=
  Nonempty.intro
    (boundaryWalkGapNegativeCoverageOutputOfCoreSubpolygonCarrierCountData
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon carrier)

/-- Transport form of the direct exact strict-carrier boundary-walk output.
This is the row-boundary handoff: if the classified strict-carrier output is
definitionally or propositionally the row boundary being requested, it inhabits
the requested `BoundaryWalkGapNegativeCoverageOutput` row. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfCoreSubpolygonCarrierCountData_eq
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (carrier : SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (hD :
      classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData) =
        D) :
    Nonempty (BoundaryWalkGapNegativeCoverageOutput D) := by
  cases hD
  exact
    nonempty_boundaryWalkGapNegativeCoverageOutputOfCoreSubpolygonCarrierCountData
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon carrier

/-- Full-boundary gap rows supply the strict local carrier source consumed by
Lemma 6.  This is the boundary-walk row projection: the local Lemma 6 fields
are rebuilt from the concrete full-boundary classification row, and the caller
supplies the corresponding strict carrier-count row. -/
def localGapTriangleDegree34CoreSubpolygonCarrierCountDataOfBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (rows :
      forall k : Fin Pcfg.outerCycle.length,
        OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) :
    Lemma6NegativeAfterGapW12.LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
      Pcfg classification.longArc F := by
  intro k fields
  exact
    rows k
      { gapDegree := fields.gapDegree
        notLongArc := fields.notLongArc
        triangleNext := fields.triangleNext
        nextDegree := fields.nextDegree }

/-- Full-boundary gap rows and strict carrier-count rows produce the concrete
W13 boundary-walk gap-negative coverage output for the classified planar row.
-/
noncomputable def boundaryWalkGapNegativeCoverageOutputOfBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (rows :
      forall k : Fin Pcfg.outerCycle.length,
        OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) :
    BoundaryWalkGapNegativeCoverageOutput
      (classification.toPlanarBoundaryData geometricAngleSum
        forced_le_geometric geometric_le_polygon F.Subpolygon
        (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)) :=
  boundaryWalkGapNegativeCoverageOutputOfConcreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    classification F geometricAngleSum forced_le_geometric geometric_le_polygon
    (localGapTriangleDegree34CoreSubpolygonCarrierCountDataOfBoundaryGapTriangleDegree34Rows
      classification F rows)

/-- Nonempty selected-frame row form of the full-boundary gap-row carrier
constructor. -/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfBoundaryGapTriangleDegree34Rows
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (rows :
      forall k : Fin Pcfg.outerCycle.length,
        OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) :
    Nonempty
      (BoundaryWalkGapNegativeCoverageOutput
        (classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData))) :=
  Nonempty.intro
    (boundaryWalkGapNegativeCoverageOutputOfBoundaryGapTriangleDegree34Rows
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon rows)

/-- Transport form of the full-boundary gap-row carrier constructor, matching
the exact downstream planar-boundary row requested by selected-frame coverage.
-/
theorem nonempty_boundaryWalkGapNegativeCoverageOutputOfBoundaryGapTriangleDegree34Rows_eq
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (classification : OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (rows :
      forall k : Fin Pcfg.outerCycle.length,
        OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F))
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg)}
    (hD :
      classification.toPlanarBoundaryData geometricAngleSum
          forced_le_geometric geometric_le_polygon F.Subpolygon
          (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData) =
        D) :
    Nonempty (BoundaryWalkGapNegativeCoverageOutput D) := by
  cases hD
  exact
    nonempty_boundaryWalkGapNegativeCoverageOutputOfBoundaryGapTriangleDegree34Rows
      classification F geometricAngleSum forced_le_geometric
      geometric_le_polygon rows

/-- The concrete boundary-walk induction data selected by the classified
boundary walk and Lemma 6 obstruction. -/
noncomputable def boundaryWalkGapInductionDataOfLemma6Obstruction
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryWalkGapNegativeInductionData O :=
  BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction O

/-- The selected classified-boundary induction length matches the
degree-three count. -/
theorem degreeThree_eq_boundaryWalkGapInductionDataOfLemma6Obstruction_length_succ
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    D.counts.d3 =
      (boundaryWalkGapInductionDataOfLemma6Obstruction
        (D := D) (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        O).length + 1 := by
  change
    O.planarBoundary.outerBoundaryCounts.d3 =
      (BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction
        O).length + 1
  exact
    BoundaryWalkGapNegativeInductionData.degreeThree_eq_length_succ_ofBoundaryWalkLemma6Obstruction
      O

/-- Terminal comparison for the selected classified-boundary induction data,
with the concrete classified long-arc count. -/
theorem boundaryWalkGapInductionDataOfLemma6Obstruction_terminal_count_le
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    (boundaryWalkGapInductionDataOfLemma6Obstruction
        (D := D) (geometricAngleSum := geometricAngleSum)
        (forced_le_geometric := forced_le_geometric)
        (geometric_le_polygon := geometric_le_polygon)
        (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
        O).count
        (boundaryWalkGapInductionDataOfLemma6Obstruction
          (D := D) (geometricAngleSum := geometricAngleSum)
          (forced_le_geometric := forced_le_geometric)
          (geometric_le_polygon := geometric_le_polygon)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          O).length <=
      D.counts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance := by
  have hterminal :=
    BoundaryWalkGapNegativeInductionData.terminal_count_le_negativeCount_add_boundaryLongArcCount
      O
  change
    (BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction
        O).count
        (BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction
          O).length <=
      D.counts.negativeCount + @Fintype.card D.longArcIndices inferInstance
  change
    (BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction
        O).count
        (BoundaryWalkGapNegativeInductionData.ofBoundaryWalkLemma6Obstruction
          O).length <=
      D.counts.negativeCount + D.counts.B at hterminal
  rw [D.counts_B] at hterminal
  exact hterminal

/-- Insert Lemma 6/7 coverage data and raw turns into the actual
classified-boundary long-arc fields.  Concavity is the raw total-turn
threshold by definition. -/
def longArcExistenceFieldsOfGapNegativeCoverageAndRawTurns
    (C :
      GapNegativeCoverageData
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        (@Fintype.card D.longArcIndices inferInstance))
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData :=
  BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields.ofCoverageAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    (degreeThree_le_negativeCount_add_longArcIndexCount_of_gapNegativeCoverageData
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) C)
    rawTurn rawTurn_nonnegative_on_arc

/-- Row-bundled version of
`longArcExistenceFieldsOfGapNegativeCoverageAndRawTurns`, using the actual
classified raw-turn rows as supplied. -/
def longArcExistenceFieldsOfGapNegativeCoverageAndRawTurnRows
    (C :
      GapNegativeCoverageData
        (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        (@Fintype.card D.longArcIndices inferInstance))
    (rawRows : BoundaryLongArcRawTurnRows D) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData :=
  longArcExistenceFieldsOfGapNegativeCoverageAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    C rawRows.rawTurn rawRows.rawTurn_nonnegative_on_arc

/-- The concrete W13 gap-negative rows already contain the Lemma 6/7 coverage
data and the raw-turn rows needed by the classified long-arc existence fields. -/
def longArcExistenceFieldsOfBoundaryLongArcGapNegativeRows
    (R :
      BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData :=
  longArcExistenceFieldsOfGapNegativeCoverageAndRawTurnRows
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    R.toGapNegativeCoverageData R.rawRows

/-- The same concrete W13 rows in the count-gap input shape consumed by
`LongArcGapConcrete`. -/
def classifiedBoundaryCountGapInputOfBoundaryLongArcGapNegativeRows
    (R :
      BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    LongArcGapConcrete.ClassifiedBoundaryCountGapInput
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData :=
  (longArcExistenceFieldsOfBoundaryLongArcGapNegativeRows
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    R).toClassifiedBoundaryCountGapInput

/-- Construction-level M8 turn bounds consumed directly from the concrete W13
gap-negative/raw-turn rows. -/
noncomputable def m8TurnBoundsOfBoundaryLongArcGapNegativeRows
    (R :
      BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    M8ConstructionInterface.M8TurnBounds :=
  (classifiedBoundaryCountGapInputOfBoundaryLongArcGapNegativeRows
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    R).toM8TurnBounds

/-- The direct consumer from concrete W13 gap-negative/raw-turn rows inherits
the checked strict `pi / 3` total-turn bound. -/
theorem m8TurnBoundsOfBoundaryLongArcGapNegativeRows_totalTurn_lt_pi_div_three
    (R :
      BoundaryLongArcGapNegativeRows D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    totalTurn
        (m8TurnBoundsOfBoundaryLongArcGapNegativeRows
          (D := D) (geometricAngleSum := geometricAngleSum)
          (forced_le_geometric := forced_le_geometric)
          (geometric_le_polygon := geometric_le_polygon)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          R).turn <
      Real.pi / 3 :=
  (classifiedBoundaryCountGapInputOfBoundaryLongArcGapNegativeRows
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    R).toM8TurnBounds_totalTurn_lt_pi_div_three

/-- Insert boundary-walk Lemma 6/7 induction data and raw turns into the actual
classified-boundary long-arc fields.  Concavity is the raw total-turn
threshold by definition. -/
def longArcExistenceFieldsOfBoundaryWalkGapInductionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData :=
  BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields.ofCoverageAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    (degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryWalkGapNegativeInduction
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      O B degreeThree_eq_length_succ
      terminal_count_le_negativeCount_add_longArcIndexCount)
    rawTurn rawTurn_nonnegative_on_arc

/-- Boundary-walk Lemma 6/7 induction data and raw turns give the actual
classified-boundary Lemma 5 long-arc facts, with the long-arc type fixed to
the classified boundary's concrete long-arc indices. -/
def boundaryWalkLongArcFactsOfBoundaryWalkGapInductionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    NonconcaveArcBudgetFromBoundary.BoundaryWalkLongArcFacts
      D.toOuterBoundaryWalkBookkeeping geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData :=
  (longArcExistenceFieldsOfBoundaryWalkGapInductionAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O B degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcIndexCount
    rawTurn rawTurn_nonnegative_on_arc).toBoundaryWalkLongArcFacts

/-- The same classified-boundary data, packaged as the concrete count-gap
input consumed by `LongArcGapConcrete`. -/
def classifiedBoundaryCountGapInputOfBoundaryWalkGapInductionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    LongArcGapConcrete.ClassifiedBoundaryCountGapInput
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData :=
  (longArcExistenceFieldsOfBoundaryWalkGapInductionAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O B degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcIndexCount
    rawTurn rawTurn_nonnegative_on_arc).toClassifiedBoundaryCountGapInput

/-- Boundary-walk gap induction plus raw turns selects the nonconcave
boundary-attached arc budget used by the Lemma 5-to-M8 route. -/
noncomputable def nonconcaveArcBoundaryBudgetDataOfBoundaryWalkGapInductionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  (boundaryWalkLongArcFactsOfBoundaryWalkGapInductionAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O B degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcIndexCount
    rawTurn rawTurn_nonnegative_on_arc).toNonconcaveArcBoundaryBudgetData

@[simp]
theorem nonconcaveArcBoundaryBudgetDataOfBoundaryWalkGapInductionAndRawTurns_planarBoundary
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    (nonconcaveArcBoundaryBudgetDataOfBoundaryWalkGapInductionAndRawTurns
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      O B degreeThree_eq_length_succ
      terminal_count_le_negativeCount_add_longArcIndexCount
      rawTurn rawTurn_nonnegative_on_arc).planarBoundary =
        D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData := by
  rfl

/-- Construction-level M8 turn bounds obtained from actual classified
boundary-walk gap induction and raw turns. -/
noncomputable def m8TurnBoundsOfBoundaryWalkGapInductionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    M8ConstructionInterface.M8TurnBounds :=
  (classifiedBoundaryCountGapInputOfBoundaryWalkGapInductionAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O B degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcIndexCount
    rawTurn rawTurn_nonnegative_on_arc).toM8TurnBounds

/-- Construction-level M8 turn bounds obtained directly from a Lemma 6
obstruction on the actual classified boundary walk and raw-turn rows.  This is
the positive boundary-walk coverage lane projected through the already checked
gap-induction/raw-turn path. -/
noncomputable def m8TurnBoundsOfBoundaryWalkObstructionAndRawTurns
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    M8ConstructionInterface.M8TurnBounds :=
  m8TurnBoundsOfBoundaryWalkGapInductionAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O
    (boundaryWalkGapInductionDataOfLemma6Obstruction
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    (degreeThree_eq_boundaryWalkGapInductionDataOfLemma6Obstruction_length_succ
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    (boundaryWalkGapInductionDataOfLemma6Obstruction_terminal_count_le
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    rawTurn rawTurn_nonnegative_on_arc

/-- The M8 turn bounds from the classified gap-induction/raw-turn route have
strict total turn below `pi / 3`. -/
theorem m8TurnBoundsOfBoundaryWalkGapInductionAndRawTurns_totalTurn_lt_pi_div_three
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (B : BoundaryWalkGapNegativeInductionData O)
    (degreeThree_eq_length_succ :
      D.counts.d3 = B.length + 1)
    (terminal_count_le_negativeCount_add_longArcIndexCount :
      B.count B.length <=
        D.counts.negativeCount +
          @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    totalTurn
        (m8TurnBoundsOfBoundaryWalkGapInductionAndRawTurns
          (D := D) (geometricAngleSum := geometricAngleSum)
          (forced_le_geometric := forced_le_geometric)
          (geometric_le_polygon := geometric_le_polygon)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          O B degreeThree_eq_length_succ
          terminal_count_le_negativeCount_add_longArcIndexCount
          rawTurn rawTurn_nonnegative_on_arc).turn <
      Real.pi / 3 :=
  (classifiedBoundaryCountGapInputOfBoundaryWalkGapInductionAndRawTurns
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O B degreeThree_eq_length_succ
    terminal_count_le_negativeCount_add_longArcIndexCount
    rawTurn rawTurn_nonnegative_on_arc).toM8TurnBounds_totalTurn_lt_pi_div_three

/-- The direct boundary-walk obstruction/raw-turn M8 bounds inherit the strict
`pi / 3` total-turn bound from the checked gap-induction/raw-turn path. -/
theorem m8TurnBoundsOfBoundaryWalkObstructionAndRawTurns_totalTurn_lt_pi_div_three
    (O :
      BoundaryWalkLemma6Obstruction
        D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    totalTurn
        (m8TurnBoundsOfBoundaryWalkObstructionAndRawTurns
          (D := D) (geometricAngleSum := geometricAngleSum)
          (forced_le_geometric := forced_le_geometric)
          (geometric_le_polygon := geometric_le_polygon)
          (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
          O rawTurn rawTurn_nonnegative_on_arc).turn <
      Real.pi / 3 :=
  m8TurnBoundsOfBoundaryWalkGapInductionAndRawTurns_totalTurn_lt_pi_div_three
    (D := D) (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
    O
    (boundaryWalkGapInductionDataOfLemma6Obstruction
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    (degreeThree_eq_boundaryWalkGapInductionDataOfLemma6Obstruction_length_succ
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    (boundaryWalkGapInductionDataOfLemma6Obstruction_terminal_count_le
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData) O)
    rawTurn rawTurn_nonnegative_on_arc

end ClassifiedBoundary

end Lemma6Lemma7AssemblyW13
end Swanepoel
end ErdosProblems1066

end
