import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts
import ErdosProblems1066.Swanepoel.BoundaryWalkConstruction
import ErdosProblems1066.Swanepoel.BoundaryWalkClassificationConcrete
import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.DeficientNeighborhood
import ErdosProblems1066.Swanepoel.SubpolygonDataConcrete

set_option autoImplicit false

/-!
# Swanepoel Lemma 6: forced negative after a gap

This file gives the project-local boundary-walk form of the Lemma 6 gap step.

The genuinely geometric part of the paper argument is isolated as a checked
hypothesis record: from a boundary-walk gap with no negative element after it,
one must construct a subpolygon violating the already checked low-degree
inequality.  The theorem below proves the usable implication from that record,
and exposes it as the `Lemma6GapToNegativeCertificate` consumed by the existing
Lemma 7 arc certificate.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma6NegativeAfterGapW12

open BoundaryClassification
open BoundaryFaceCountingToM8
open BoundarySpineFiniteCertificate
open BoundaryWalkConstruction
open Lemma10Inequalities
open M8TurnBoundsFromArc
open M8LabelsFromBoundaryInterface
open NonconcaveArcAngleFacts
open OuterBoundaryInterface
open PlanarInterface

universe u

variable {n : Nat}

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}

/-- A boundary-walk index carries a negative contribution when it is a
nontriangle edge or a degree-five/six boundary vertex. -/
def BoundaryWalkNegativeAt
    (walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) : Prop :=
  walk.edgeKind k = BoundaryEdgeClass.nontriangle \/
    walk.vertexKind k = BoundaryDegreeClass.degree5 \/
      walk.vertexKind k = BoundaryDegreeClass.degree6

/-- The local paper gap predicate: a degree-three boundary vertex that is not
itself selected as a long arc. -/
def BoundaryWalkGapAt
    (walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) : Prop :=
  walk.vertexKind k = BoundaryDegreeClass.degree3 /\ Not (walk.longArc k)

/-- The Lemma 6 conclusion attached to a gap: the next boundary element is
negative. -/
def BoundaryWalkNegativeAfterGapAt
    (walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) : Prop :=
  BoundaryWalkNegativeAt walk (C.next k)

namespace BoundaryWalkNegativeAt

/-- The propositional negative predicate matches the positive local
negative-contribution indicator. -/
theorem iff_positive_contribution
    (walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    BoundaryWalkNegativeAt walk k <->
      0 <
        BoundaryEdgeClass.nontriangleContribution (walk.edgeKind k) +
          BoundaryDegreeClass.negativeContribution (walk.vertexKind k) := by
  generalize he : walk.edgeKind k = e
  generalize hv : walk.vertexKind k = v
  cases e <;> cases v <;>
    simp [BoundaryWalkNegativeAt, BoundaryEdgeClass.nontriangleContribution,
      BoundaryDegreeClass.negativeContribution, he, hv]

end BoundaryWalkNegativeAt

namespace BoundaryWalkGapAt

/-- A gap is located at a degree-three boundary vertex. -/
theorem degree3
    {walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {k : Fin C.length}
    (hgap : BoundaryWalkGapAt walk k) :
    walk.vertexKind k = BoundaryDegreeClass.degree3 :=
  hgap.1

/-- A gap is not one of the selected long arcs. -/
theorem not_longArc
    {walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {k : Fin C.length}
    (hgap : BoundaryWalkGapAt walk k) :
    Not (walk.longArc k) :=
  hgap.2

end BoundaryWalkGapAt

namespace BoundaryWalkNegativeAfterGapAt

/-- If the Lemma 6 negative-after conclusion fails, the next boundary edge is
triangular. -/
theorem edgeKind_eq_triangle_of_not
    {walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {k : Fin C.length}
    (hnot : Not (BoundaryWalkNegativeAfterGapAt walk k)) :
    walk.edgeKind (C.next k) = BoundaryEdgeClass.triangle := by
  unfold BoundaryWalkNegativeAfterGapAt BoundaryWalkNegativeAt at hnot
  cases h : walk.edgeKind (C.next k) with
  | triangle => rfl
  | nontriangle => exact False.elim (hnot (Or.inl h))

/-- If the Lemma 6 negative-after conclusion fails, the next boundary vertex
has boundary degree class three or four. -/
theorem vertexKind_eq_degree3_or_degree4_of_not
    {walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {k : Fin C.length}
    (hnot : Not (BoundaryWalkNegativeAfterGapAt walk k)) :
    walk.vertexKind (C.next k) = BoundaryDegreeClass.degree3 \/
      walk.vertexKind (C.next k) = BoundaryDegreeClass.degree4 := by
  unfold BoundaryWalkNegativeAfterGapAt BoundaryWalkNegativeAt at hnot
  cases h : walk.vertexKind (C.next k) with
  | degree3 => exact Or.inl rfl
  | degree4 => exact Or.inr rfl
  | degree5 => exact False.elim (hnot (Or.inr (Or.inl h)))
  | degree6 => exact False.elim (hnot (Or.inr (Or.inr h)))

/-- A compact form of the local concrete data exposed by failure of the
negative-after conclusion. -/
theorem localData_of_not
    {walk :
      BoundaryWalkBookkeeping C IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {k : Fin C.length}
    (hnot : Not (BoundaryWalkNegativeAfterGapAt walk k)) :
    walk.edgeKind (C.next k) = BoundaryEdgeClass.triangle /\
      (walk.vertexKind (C.next k) = BoundaryDegreeClass.degree3 \/
        walk.vertexKind (C.next k) = BoundaryDegreeClass.degree4) :=
  And.intro (edgeKind_eq_triangle_of_not hnot)
    (vertexKind_eq_degree3_or_degree4_of_not hnot)

end BoundaryWalkNegativeAfterGapAt

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

/-- Swanepoel E14/Lemma 6 in its direct boundary-walk form.

This is the named paper fact behind the obstruction interface below: every
degree-three non-long-arc gap forces the following boundary element to carry a
negative contribution. -/
def BoundaryWalkLemma6E14NegativeAfterFact
    (walk :
      OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6) : Prop :=
  forall k : Fin P.outerCycle.length,
    BoundaryWalkGapAt walk.data k ->
      BoundaryWalkNegativeAfterGapAt walk.data k

/-- The exact remaining geometric construction for Lemma 6 on the current
project-local boundary walk.

It is a hypothesis record: callers must provide a concrete
subpolygon low-degree violation from a gap with no negative element after it.
The checked theorem `negativeAfter_of_gap` then discharges the contradiction
using the existing planar-boundary subpolygon low-degree theorem. -/
structure BoundaryWalkLemma6Obstruction
    (walk :
      OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  subpolygonViolation_of_gap_without_negativeAfter :
    forall k : Fin P.outerCycle.length,
      BoundaryWalkGapAt walk.data k ->
      Not (BoundaryWalkNegativeAfterGapAt walk.data k) ->
        SubpolygonLowDegreeViolation
          (walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
            geometric_le_polygon Subpolygon subpolygonData)

namespace BoundaryWalkLemma6Obstruction

/-- The planar-boundary package tied to the same boundary walk. -/
def planarBoundary
    (_O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
    geometric_le_polygon Subpolygon subpolygonData

/-- A direct named E14/Lemma 6 negative-after fact supplies the obstruction
interface.  The contradiction with `Not negativeAfter` makes the requested
subpolygon-violation branch unreachable. -/
def ofNegativeAfterFact
    (H : BoundaryWalkLemma6E14NegativeAfterFact walk) :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData where
  subpolygonViolation_of_gap_without_negativeAfter := by
    intro k hgap hnot
    exact False.elim (hnot (H k hgap))

/-- Repackage the project-local gap/negative-after statement as the generic
certificate consumed by the arc-angle layer. -/
def toGapToNegativeCertificate
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (k : Fin P.outerCycle.length) :
    Lemma6GapToNegativeCertificate O.planarBoundary
      (BoundaryWalkGapAt walk.data k)
      (BoundaryWalkNegativeAfterGapAt walk.data k) where
  gap_without_negative_violates_subpolygon_low_degree := by
    intro hgap hnot
    exact O.subpolygonViolation_of_gap_without_negativeAfter k hgap hnot

/-- Swanepoel Lemma 6 in boundary-walk form: a gap forces the following
boundary element to be negative. -/
theorem negativeAfter_of_gap
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (k : Fin P.outerCycle.length) :
    BoundaryWalkGapAt walk.data k ->
      BoundaryWalkNegativeAfterGapAt walk.data k :=
  (O.toGapToNegativeCertificate k).negative_of_gap

/-- Any obstruction package recovers the direct E14/Lemma 6 negative-after
fact for the same boundary walk. -/
theorem toNegativeAfterFact
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryWalkLemma6E14NegativeAfterFact walk :=
  fun k => O.negativeAfter_of_gap k

/-- The obstruction package is exactly the named E14/Lemma 6 boundary-walk
fact, with the unreachable subpolygon-violation branch supplied by
contradiction. -/
theorem nonempty_iff_negativeAfterFact :
    Nonempty
      (BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) <->
      BoundaryWalkLemma6E14NegativeAfterFact walk := by
  constructor
  · intro h
    rcases h with ⟨O⟩
    exact O.toNegativeAfterFact
  · intro H
    exact ⟨ofNegativeAfterFact H⟩

end BoundaryWalkLemma6Obstruction

/-! ### E5 deficient-neighborhood reduction for Lemma 6 -/

/-- Direct reduction of the boundary-walk E14/Lemma 6 fact to the checked E5
minimal-failure neighborhood theorem.

The remaining combinatorial work for a gap is exactly the premise `H`: from a
gap with no negative element after it, construct the paper's small independent
set `S` whose outside neighborhood has size strictly less than `3 * |S|`. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_deficientIndependentSetContradiction
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping Pcfg IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    (H :
      forall k : Fin Pcfg.outerCycle.length,
        BoundaryWalkGapAt walk.data k ->
        Not (BoundaryWalkNegativeAfterGapAt walk.data k) ->
          Exists fun S : Finset (Fin n) =>
            S.Nonempty /\
            Cfg.IsIndep S /\
            S.card <= 8 /\
            (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
              3 * S.card) :
    BoundaryWalkLemma6E14NegativeAfterFact walk := by
  intro k hgap
  by_contra hnegative
  exact
    DeficientNeighborhood.false_of_minimalFailure_deficientIndependentSet
      hmin (H k hgap hnegative)

/-- Local E5 reduction for Lemma 6.

After the failed negative-after conclusion is unfolded, the remaining
construction is the paper's small independent set under the concrete local
endpoint data: the next edge is triangular and the next vertex has degree
class three or four. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_localGapDeficientIndependentSet
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping Pcfg IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    (H :
      forall k : Fin Pcfg.outerCycle.length,
        BoundaryWalkGapAt walk.data k ->
        walk.data.edgeKind (Pcfg.outerCycle.next k) =
          BoundaryEdgeClass.triangle ->
        (walk.data.vertexKind (Pcfg.outerCycle.next k) =
            BoundaryDegreeClass.degree3 \/
          walk.data.vertexKind (Pcfg.outerCycle.next k) =
            BoundaryDegreeClass.degree4) ->
          Exists fun S : Finset (Fin n) =>
            S.Nonempty /\
            Cfg.IsIndep S /\
            S.card <= 8 /\
            (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
              3 * S.card) :
    BoundaryWalkLemma6E14NegativeAfterFact walk :=
  boundaryWalkLemma6E14NegativeAfterFact_of_deficientIndependentSetContradiction
    hmin
    (by
      intro k hgap hnot
      rcases BoundaryWalkNegativeAfterGapAt.localData_of_not
          (walk := walk.data) (k := k) hnot with
        ⟨htriangle, hdegree⟩
      exact H k hgap htriangle hdegree)

/-! ### Concrete local source for the E5 deficient-neighborhood branch -/

/-- The smallest remaining local geometric source for the E5 branch of
Lemma 6.

For every boundary-walk gap, once the failed negative-after conclusion has
identified the next edge as a concrete triangle edge and the next boundary
vertex as ambient degree three or four, this source supplies the paper's
small independent set with deficient outside neighborhood. -/
def LocalGapTriangleDegree34DeficientSetSource
    {Cfg : _root_.UDConfig n}
    (Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg))
    (longArc : Fin Pcfg.outerCycle.length -> Prop) : Prop :=
  forall k : Fin Pcfg.outerCycle.length,
    BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
      (Pcfg.outerCycle.vertex k) ->
    Not (longArc k) ->
    BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
      (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
    (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
      BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
      Exists fun S : Finset (Fin n) =>
        S.Nonempty /\
        Cfg.IsIndep S /\
        S.card <= 8 /\
        (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
          3 * S.card

/-- Classified boundary-walk local data with an actual carrier set gives the
named local deficient-set source used by Lemma 6. -/
theorem localGapTriangleDegree34DeficientSetSource_of_actualClassifiedBoundaryWalkLocalData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {longArc : Fin Pcfg.outerCycle.length -> Prop}
    (localData :
      forall k : Fin Pcfg.outerCycle.length,
        BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex k) ->
        Not (longArc k) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
          DeficientNeighborhood.DeficientIndependentSetData Cfg) :
    LocalGapTriangleDegree34DeficientSetSource Pcfg longArc := by
  intro k hgapDegree hnotLong htriangle hnextDegree
  exact
    DeficientNeighborhood.DeficientIndependentSetData.toExists
      (localData k hgapDegree hnotLong htriangle hnextDegree)

/-- Concrete classified-walk form of the local deficient-set source.

This removes the generic edge/degree-class hypotheses from
`boundaryWalkLemma6E14NegativeAfterFact_of_localGapDeficientIndependentSet`:
the only remaining input is the named geometric local configuration source
`LocalGapTriangleDegree34DeficientSetSource`. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34DeficientSetSource
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    (D : BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs Pcfg)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    (H : LocalGapTriangleDegree34DeficientSetSource Pcfg D.longArc) :
    BoundaryWalkLemma6E14NegativeAfterFact D.toOuterBoundaryWalkBookkeeping := by
  apply boundaryWalkLemma6E14NegativeAfterFact_of_localGapDeficientIndependentSet
    hmin
  intro k hgap htriangle hdegree
  have hgapDegreeClass :
      BoundaryWalkClassificationConcrete.vertexKind Pcfg k =
        BoundaryDegreeClass.degree3 := by
    exact hgap.1
  have hgapDegree :
      BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex k) :=
    (BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff Pcfg k).1
      hgapDegreeClass
  have hnotLong : Not (D.longArc k) := by
    exact hgap.2
  have htriangleClass :
      BoundaryWalkClassificationConcrete.edgeKind Pcfg
          (Pcfg.outerCycle.next k) =
        BoundaryEdgeClass.triangle := by
    exact htriangle
  have htriangleConcrete :
      BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) :=
    BoundaryWalkClassificationConcrete.edgeKind_triangleEvidence Pcfg
      (Pcfg.outerCycle.next k) htriangleClass
  have hdegreeConcrete :
      BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
        BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) := by
    rcases hdegree with hdegree3 | hdegree4
    · left
      have hdegree3Class :
          BoundaryWalkClassificationConcrete.vertexKind Pcfg
              (Pcfg.outerCycle.next k) =
            BoundaryDegreeClass.degree3 := by
        exact hdegree3
      exact
        (BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff Pcfg
          (Pcfg.outerCycle.next k)).1 hdegree3Class
    · right
      have hdegree4Class :
          BoundaryWalkClassificationConcrete.vertexKind Pcfg
              (Pcfg.outerCycle.next k) =
            BoundaryDegreeClass.degree4 := by
        exact hdegree4
      exact
        (BoundaryWalkClassificationConcrete.vertexKind_eq_degree4_iff Pcfg
          (Pcfg.outerCycle.next k)).1 hdegree4Class
  exact H k hgapDegree hnotLong htriangleConcrete hdegreeConcrete

/-- Boundary-walk Lemma 6 directly from actual classified local deficient-set
data at each triangle/degree-three-or-four gap follower. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_actualClassifiedBoundaryWalkLocalData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    (D : BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs Pcfg)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    (localData :
      forall k : Fin Pcfg.outerCycle.length,
        BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex k) ->
        Not (D.longArc k) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
          DeficientNeighborhood.DeficientIndependentSetData Cfg) :
    BoundaryWalkLemma6E14NegativeAfterFact D.toOuterBoundaryWalkBookkeeping :=
  boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34DeficientSetSource
    (Cfg := Cfg) (Pcfg := Pcfg) D hmin
    (localGapTriangleDegree34DeficientSetSource_of_actualClassifiedBoundaryWalkLocalData
      (Cfg := Cfg) (Pcfg := Pcfg) (longArc := D.longArc) localData)

/-! ### Combined local E5/E13 carrier source -/

/-- The concrete local carrier source for Lemma 6 after the failed
negative-after conclusion has been unfolded.

At each degree-three non-long-arc gap whose next edge is triangular and whose
next vertex has degree class three or four, the caller may provide either the
paper's small deficient independent set or a concrete subpolygon in the same
core family with strict bad `D2`/`D3` counts.  Either branch is immediately
contradictory in the checked infrastructure. -/
def LocalGapTriangleDegree34DeficientSetOrCoreSubpolygonCarrierSource
    {Cfg : _root_.UDConfig n}
    (Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg))
    (longArc : Fin Pcfg.outerCycle.length -> Prop)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg) : Prop :=
  forall k : Fin Pcfg.outerCycle.length,
    BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
      (Pcfg.outerCycle.vertex k) ->
    Not (longArc k) ->
    BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
      (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
    (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
      BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
      (Exists fun S : Finset (Fin n) =>
        S.Nonempty /\
        Cfg.IsIndep S /\
        S.card <= 8 /\
        (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
          3 * S.card) \/
      Exists fun S : F.Subpolygon =>
        Exists fun D2 : Nat =>
          Exists fun D3 : Nat =>
            (F.subpolygonData S).counts.D2 = D2 /\
            (F.subpolygonData S).counts.D3 = D3 /\
            2 * D2 + D3 < 6

/-- Concrete classified-walk Lemma 6 closure from a local carrier source that
may choose either the E5 deficient-independent-set branch or the E13 strict
subpolygon-count branch. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34DeficientSetOrCoreSubpolygonCarrierSource
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    (D : BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    (H :
      LocalGapTriangleDegree34DeficientSetOrCoreSubpolygonCarrierSource
        Pcfg D.longArc F) :
    BoundaryWalkLemma6E14NegativeAfterFact D.toOuterBoundaryWalkBookkeeping := by
  intro k hgap
  by_contra hnegative
  rcases BoundaryWalkNegativeAfterGapAt.localData_of_not
      (walk := D.toOuterBoundaryWalkBookkeeping.data) (k := k) hnegative with
    ⟨htriangle, hdegree⟩
  have hgapDegree :
      BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex k) :=
    (BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff Pcfg k).1
      hgap.1
  have hnotLong : Not (D.longArc k) := hgap.2
  have htriangleConcrete :
      BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) :=
    BoundaryWalkClassificationConcrete.edgeKind_triangleEvidence Pcfg
      (Pcfg.outerCycle.next k) htriangle
  have hdegreeConcrete :
      BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
        BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) := by
    rcases hdegree with hdegree3 | hdegree4
    · exact Or.inl
        ((BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff Pcfg
          (Pcfg.outerCycle.next k)).1 hdegree3)
    · exact Or.inr
        ((BoundaryWalkClassificationConcrete.vertexKind_eq_degree4_iff Pcfg
          (Pcfg.outerCycle.next k)).1 hdegree4)
  rcases H k hgapDegree hnotLong htriangleConcrete hdegreeConcrete with
    hdeficient | hcarrier
  · exact
      DeficientNeighborhood.false_of_minimalFailure_deficientIndependentSet
        hmin hdeficient
  · rcases hcarrier with ⟨S, D2, D3, hD2, hD3, hstrict⟩
    have hlow := F.subpolygonLowDegree S
    have hstrict' :
        2 * (F.subpolygonData S).counts.D2 +
            (F.subpolygonData S).counts.D3 < 6 := by
      rw [hD2, hD3]
      exact hstrict
    exact (not_lt_of_ge hlow) hstrict'

/-! ### Direct E13 reduction for the remaining Lemma 6 source -/

/-- Turn explicit computed `D2`/`D3` carrier data into the strict E13
low-degree violation used by Lemma 6. -/
theorem subpolygonStrictLowDegree_of_countData
    {S : Subpolygon} {D2 D3 : Nat}
    (hD2 : (subpolygonData S).counts.D2 = D2)
    (hD3 : (subpolygonData S).counts.D3 = D3)
    (hstrict : 2 * D2 + D3 < 6) :
    2 * (subpolygonData S).counts.D2 +
        (subpolygonData S).counts.D3 < 6 := by
  rw [hD2, hD3]
  exact hstrict

/-- Direct reduction of the boundary-walk E14/Lemma 6 fact to the concrete
E13 low-degree theorem carried by the same `PlanarBoundaryData`.

The remaining geometric work for a gap is now exactly the named data in `H`:
a concrete subpolygon carrier from the current `Subpolygon` family whose
computed counts satisfy the strict bad inequality `2 * D2 + D3 < 6`.  The
checked E13 theorem for that same carrier gives the contradiction. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_subpolygonLowDegreeContradiction
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (H :
      forall k : Fin P.outerCycle.length,
        BoundaryWalkGapAt walk.data k ->
        Not (BoundaryWalkNegativeAfterGapAt walk.data k) ->
          Exists fun S : Subpolygon =>
            2 * (subpolygonData S).counts.D2 +
                (subpolygonData S).counts.D3 < 6) :
    BoundaryWalkLemma6E14NegativeAfterFact walk := by
  intro k hgap
  by_contra hnegative
  rcases H k hgap hnegative with ⟨S, hstrict⟩
  have hlow :
      6 <=
        2 * (subpolygonData S).counts.D2 +
          (subpolygonData S).counts.D3 := by
    exact
      PlanarBoundaryFinal.PlanarBoundaryData.subpolygonLowDegreeInequality_viaBoundaryCounting
        (walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        S
  exact (not_lt_of_ge hlow) hstrict

namespace BoundaryWalkLemma6Obstruction

/-- The direct E13-reduction theorem also supplies the existing obstruction
record, without adding any new source layer. -/
def ofSubpolygonLowDegreeContradiction
    (H :
      forall k : Fin P.outerCycle.length,
        BoundaryWalkGapAt walk.data k ->
        Not (BoundaryWalkNegativeAfterGapAt walk.data k) ->
          Exists fun S : Subpolygon =>
            2 * (subpolygonData S).counts.D2 +
                (subpolygonData S).counts.D3 < 6) :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData :=
  ofNegativeAfterFact
    (boundaryWalkLemma6E14NegativeAfterFact_of_subpolygonLowDegreeContradiction
      geometricAngleSum forced_le_geometric geometric_le_polygon H)

end BoundaryWalkLemma6Obstruction

/-- Local E13 carrier reduction for Lemma 6.

After unfolding the failed negative-after conclusion, the remaining obligation
is exactly to name a carrier in the current `subpolygonData` family and compute
its `D2`/`D3` counts below the E13 threshold. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_localGapSubpolygonCarrierCountData
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (H :
      forall k : Fin P.outerCycle.length,
        BoundaryWalkGapAt walk.data k ->
        walk.data.edgeKind (P.outerCycle.next k) =
          BoundaryEdgeClass.triangle ->
        (walk.data.vertexKind (P.outerCycle.next k) =
            BoundaryDegreeClass.degree3 \/
          walk.data.vertexKind (P.outerCycle.next k) =
            BoundaryDegreeClass.degree4) ->
          Exists fun S : Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (subpolygonData S).counts.D2 = D2 /\
                (subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    BoundaryWalkLemma6E14NegativeAfterFact walk := by
  apply boundaryWalkLemma6E14NegativeAfterFact_of_subpolygonLowDegreeContradiction
    geometricAngleSum forced_le_geometric geometric_le_polygon
  intro k hgap hnot
  rcases BoundaryWalkNegativeAfterGapAt.localData_of_not
      (walk := walk.data) (k := k) hnot with ⟨htriangle, hdegree⟩
  rcases H k hgap htriangle hdegree with
    ⟨S, D2, D3, hD2, hD3, hstrict⟩
  exact ⟨S, subpolygonStrictLowDegree_of_countData
    (S := S) (D2 := D2) (D3 := D3) hD2 hD3 hstrict⟩

/-- Concrete classified-walk version of the local E13 carrier route.

The carrier is taken from an actual `CoreSubpolygonFamilyData` package, and the
local hypotheses are the concrete unit-distance triangle and ambient
degree-three/four predicates computed by
`BoundaryWalkClassificationConcrete`. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_classificationCoreSubpolygonCarrierCountData
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (H :
      forall k : Fin P.outerCycle.length,
        BoundaryWalkGapAt classification.toOuterBoundaryWalkBookkeeping.data k ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge G
          (P.outerCycle.edge (P.outerCycle.next k)) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 G
            (P.outerCycle.vertex (P.outerCycle.next k)) \/
          BoundaryWalkClassificationConcrete.IsDegree4 G
            (P.outerCycle.vertex (P.outerCycle.next k))) ->
          Exists fun S : F.Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (F.subpolygonData S).counts.D2 = D2 /\
                (F.subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    BoundaryWalkLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping := by
  exact
    boundaryWalkLemma6E14NegativeAfterFact_of_localGapSubpolygonCarrierCountData
      (walk := classification.toOuterBoundaryWalkBookkeeping)
      (Subpolygon := F.Subpolygon)
      (subpolygonData :=
        fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)
      geometricAngleSum forced_le_geometric geometric_le_polygon
      (by
        intro k hgap htriangleClass hdegreeClass
        have htriangle :
            BoundaryWalkClassificationConcrete.IsTriangleEdge G
              (P.outerCycle.edge (P.outerCycle.next k)) :=
          classification.toOuterBoundaryWalkBookkeeping.data.edge_triangleEvidence
            (P.outerCycle.next k) htriangleClass
        have hdegree :
            BoundaryWalkClassificationConcrete.IsDegree3 G
                (P.outerCycle.vertex (P.outerCycle.next k)) \/
              BoundaryWalkClassificationConcrete.IsDegree4 G
                (P.outerCycle.vertex (P.outerCycle.next k)) := by
          rcases hdegreeClass with hdegree3 | hdegree4
          · exact Or.inl
              (classification.toOuterBoundaryWalkBookkeeping.data.degree3Evidence
                (P.outerCycle.next k) hdegree3)
          · exact Or.inr
              (classification.toOuterBoundaryWalkBookkeeping.data.degree4Evidence
                (P.outerCycle.next k) hdegree4)
        rcases H k hgap htriangle hdegree with
          ⟨S, D2, D3, hD2, hD3, hstrict⟩
        exact ⟨S, D2, D3, by exact hD2, by exact hD3, hstrict⟩)

/-- Strict subpolygon-carrier closure from the actual concrete local gap
fields of the classified boundary walk.

The only remaining caller row is the carrier/count construction from the
degree-three non-long-arc gap, the triangular next edge, and the next-vertex
degree-three/four alternative. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    (D :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        D.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (H :
      forall k : Fin Pcfg.outerCycle.length,
        BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex k) ->
        Not (D.longArc k) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge
          (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
          Exists fun S : F.Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (F.subpolygonData S).counts.D2 = D2 /\
                (F.subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    BoundaryWalkLemma6E14NegativeAfterFact
      D.toOuterBoundaryWalkBookkeeping := by
  exact
    boundaryWalkLemma6E14NegativeAfterFact_of_classificationCoreSubpolygonCarrierCountData
      D F geometricAngleSum forced_le_geometric geometric_le_polygon
      (by
        intro k hgap htriangle hdegree
        have hgapDegree :
            BoundaryWalkClassificationConcrete.IsDegree3
              (CanonicalUDGraph Cfg) (Pcfg.outerCycle.vertex k) :=
          (BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff
            Pcfg k).1 hgap.1
        have hnotLong : Not (D.longArc k) := hgap.2
        exact H k hgapDegree hnotLong htriangle hdegree)

/-! ### Exact local carrier-count source -/

/-- The actual classified local fields exposed at a failed Lemma 6 gap.

These are only the concrete fields obtained from the boundary classification:
the gap vertex has ambient degree three, the gap is not selected as a long arc,
the following edge is triangular, and the following vertex has ambient degree
three or four. -/
structure ConcreteLocalGapTriangleDegree34Fields
    {Cfg : _root_.UDConfig n}
    (Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg))
    (longArc : Fin Pcfg.outerCycle.length -> Prop)
    (k : Fin Pcfg.outerCycle.length) : Prop where
  gapDegree :
    BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
      (Pcfg.outerCycle.vertex k)
  notLongArc : Not (longArc k)
  triangleNext :
    BoundaryWalkClassificationConcrete.IsTriangleEdge
      (CanonicalUDGraph Cfg)
      (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k))
  nextDegree :
    BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
      BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))

/-- Exact pointwise carrier-count source for the Lemma 6 strict E13 branch.

For every actual classified triangle/degree-3-or-4 local gap, this supplies the
core-subpolygon carrier and its computed strict `D2`/`D3` row. -/
def LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    (Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg))
    (longArc : Fin Pcfg.outerCycle.length -> Prop)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg) : Prop :=
  forall k : Fin Pcfg.outerCycle.length,
    ConcreteLocalGapTriangleDegree34Fields Pcfg longArc k ->
      Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)

/-- A single exact strict carrier in the current core-subpolygon family
supplies the pointwise local strict-carrier source for every classified local
gap row. -/
theorem localGapTriangleDegree34CoreSubpolygonCarrierCountData_of_coreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {longArc : Fin Pcfg.outerCycle.length -> Prop}
    {F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg}
    (D : SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F) :
    LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
      Pcfg longArc F := by
  intro _k _hfields
  exact ⟨D⟩

/-- Separate actual classified local fields produce the exact pointwise
carrier-count source. -/
theorem localGapTriangleDegree34CoreSubpolygonCarrierCountData_of_actualClassifiedBoundaryWalkLocalData
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {longArc : Fin Pcfg.outerCycle.length -> Prop}
    {F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg}
    (localData :
      forall k : Fin Pcfg.outerCycle.length,
        BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex k) ->
        Not (longArc k) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge
          (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
          SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F) :
    LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
      Pcfg longArc F := by
  intro k hfields
  exact ⟨
    localData k hfields.gapDegree hfields.notLongArc
      hfields.triangleNext hfields.nextDegree⟩

/-- Forget the exact local carrier-count source to the existential row consumed
by the existing Lemma 6 strict-carrier theorem. -/
theorem localGapTriangleDegree34CoreSubpolygonCarrierCountData_to_exists
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {longArc : Fin Pcfg.outerCycle.length -> Prop}
    {F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg}
    (H :
      LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
        Pcfg longArc F) :
    forall k : Fin Pcfg.outerCycle.length,
      BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.vertex k) ->
      Not (longArc k) ->
      BoundaryWalkClassificationConcrete.IsTriangleEdge
        (CanonicalUDGraph Cfg)
        (Pcfg.outerCycle.edge (Pcfg.outerCycle.next k)) ->
      (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k)) \/
        BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
          (Pcfg.outerCycle.vertex (Pcfg.outerCycle.next k))) ->
        Exists fun S : F.Subpolygon =>
          Exists fun D2 : Nat =>
            Exists fun D3 : Nat =>
              (F.subpolygonData S).counts.D2 = D2 /\
              (F.subpolygonData S).counts.D3 = D3 /\
              2 * D2 + D3 < 6 := by
  intro k hgapDegree hnotLong htriangle hnextDegree
  rcases
    H k
      { gapDegree := hgapDegree
        notLongArc := hnotLong
        triangleNext := htriangle
        nextDegree := hnextDegree } with
    ⟨D⟩
  exact
    D.toExists

/-- Strict subpolygon-carrier closure from the exact local carrier-count source
for the actual classified local gap fields. -/
theorem boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    (D :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        D.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (H :
      LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
        Pcfg D.longArc F) :
    BoundaryWalkLemma6E14NegativeAfterFact
      D.toOuterBoundaryWalkBookkeeping :=
  boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountData
    D F geometricAngleSum forced_le_geometric geometric_le_polygon
    (localGapTriangleDegree34CoreSubpolygonCarrierCountData_to_exists H)

/-- The exact local strict-count source supplies the existing Lemma 6
obstruction record for the actual classified boundary walk. -/
def boundaryWalkLemma6Obstruction_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    (D :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        Pcfg)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        D.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum)
    (H :
      LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
        Pcfg D.longArc F) :
    BoundaryWalkLemma6Obstruction
      D.toOuterBoundaryWalkBookkeeping geometricAngleSum
      forced_le_geometric geometric_le_polygon F.Subpolygon
      (fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData) :=
  BoundaryWalkLemma6Obstruction.ofNegativeAfterFact
    (boundaryWalkLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
      D F geometricAngleSum forced_le_geometric geometric_le_polygon H)

/-- The exact strict-carrier source is equivalent to ruling out the concrete
classified local triangle/degree-3-or-4 gap fields.

This is the sharpened blocker: a real proof of the source must either build the
impossible strict E13 carrier under those fields, or more directly show that no
such local classified gap occurs. -/
theorem localGapTriangleDegree34CoreSubpolygonCarrierCountData_iff_no_concreteLocalGapTriangleDegree34Fields
    {Cfg : _root_.UDConfig n}
    {Pcfg : OuterBoundaryCore (CanonicalUDGraph Cfg)}
    {longArc : Fin Pcfg.outerCycle.length -> Prop}
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} Pcfg) :
    LocalGapTriangleDegree34CoreSubpolygonCarrierCountData Pcfg longArc F <->
      forall k : Fin Pcfg.outerCycle.length,
        Not (ConcreteLocalGapTriangleDegree34Fields Pcfg longArc k) := by
  constructor
  · intro H k hfields
    rcases H k hfields with ⟨D⟩
    exact D.false
  · intro hno k hfields
    exact False.elim (hno k hfields)

/-! ## Arc-index bridge for the Lemma 7 certificate -/

/-- A map from the concrete thirteen turn indices to boundary-walk indices.
This keeps the boundary predicate local while matching the Nat-indexed arc API. -/
structure BoundaryArcIndexMap
    (walk :
      OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6) where
  boundaryIndex : Nat -> Fin P.outerCycle.length

namespace BoundaryArcIndexMap

/-- The project-local gap predicate transported to a Nat arc index. -/
def gapAt
    (M : BoundaryArcIndexMap walk) (k : Nat) : Prop :=
  BoundaryWalkGapAt walk.data (M.boundaryIndex k)

/-- The project-local negative-after-gap conclusion transported to a Nat arc
index. -/
def negativeAfterAt
    (M : BoundaryArcIndexMap walk) (k : Nat) : Prop :=
  BoundaryWalkNegativeAfterGapAt walk.data (M.boundaryIndex k)

/-- The Lemma 6 certificate for one Nat-indexed arc position. -/
def lemma6GapToNegativeCertificate
    (M : BoundaryArcIndexMap walk)
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (k : Nat) :
    Lemma6GapToNegativeCertificate O.planarBoundary
      (M.gapAt k) (M.negativeAfterAt k) :=
  O.toGapToNegativeCertificate (M.boundaryIndex k)

/-- Nat-indexed form of Lemma 6. -/
theorem negativeAfterAt_of_gapAt
    (M : BoundaryArcIndexMap walk)
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (k : Nat) :
    M.gapAt k -> M.negativeAfterAt k :=
  (M.lemma6GapToNegativeCertificate O k).negative_of_gap

/-! ### Concrete M8 spine source for the boundary arc index map -/

/-- Interpret a natural M8 arc index as one of the selected boundary-spine
indices `p_0, ..., p_13`, clamping irrelevant out-of-range values to `p_13`.

Only the turn indices `1, ..., 13` are used by Lemma 7; the fallback keeps the
map total without adding a source premise. -/
def m8BoundaryIndexOfNat (k : Nat) : M8BoundaryIndex :=
  if hk : k <= 13 then
    Subtype.mk k (by
      have hk' : k <= 2 * 8 - 3 := by omega
      exact hk')
  else
    Subtype.mk 13 (by norm_num)

@[simp]
theorem m8BoundaryIndexOfNat_of_le {k : Nat} (hk : k <= 13) :
    m8BoundaryIndexOfNat k =
      (Subtype.mk k (by
        have hk' : k <= 2 * 8 - 3 := by omega
        exact hk') : M8BoundaryIndex) := by
  simp [m8BoundaryIndexOfNat, hk]

@[simp]
theorem m8BoundaryIndexOfNat_val_of_le {k : Nat} (hk : k <= 13) :
    (m8BoundaryIndexOfNat k).1 = k := by
  simp [m8BoundaryIndexOfNat_of_le hk]

@[simp]
theorem m8BoundaryIndexOfNat_val_of_m8BoundaryIndex
    (i : M8BoundaryIndex) :
    m8BoundaryIndexOfNat i.1 = i := by
  have hi : i.1 <= 13 := by
    have h := i.2
    omega
  ext
  simp [m8BoundaryIndexOfNat_val_of_le hi]

/-- The actual finite `p/q` boundary spine supplies the Nat-indexed
`BoundaryArcIndexMap` required by the Lemma 6/Lemma 7 arc interface. -/
def ofFinitePQSpineCertificate
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D) :
    BoundaryArcIndexMap walk where
  boundaryIndex := fun k => K.pIndex (m8BoundaryIndexOfNat k)

@[simp]
theorem ofFinitePQSpineCertificate_boundaryIndex
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D) (k : Nat) :
    (ofFinitePQSpineCertificate (walk := walk) K).boundaryIndex k =
      K.pIndex (m8BoundaryIndexOfNat k) :=
  rfl

theorem ofFinitePQSpineCertificate_boundaryIndex_of_le
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D) {k : Nat} (hk : k <= 13) :
    (ofFinitePQSpineCertificate (walk := walk) K).boundaryIndex k =
      K.pIndex
        (Subtype.mk k (by
          have hk' : k <= 2 * 8 - 3 := by omega
          exact hk') : M8BoundaryIndex) := by
  change K.pIndex (m8BoundaryIndexOfNat k) =
    K.pIndex
      (Subtype.mk k (by
        have hk' : k <= 2 * 8 - 3 := by omega
        exact hk') : M8BoundaryIndex)
  rw [m8BoundaryIndexOfNat_of_le hk]

theorem ofFinitePQSpineCertificate_boundaryIndex_val
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D) (i : M8BoundaryIndex) :
    (ofFinitePQSpineCertificate (walk := walk) K).boundaryIndex i.1 =
      K.pIndex i := by
  change K.pIndex (m8BoundaryIndexOfNat i.1) = K.pIndex i
  rw [m8BoundaryIndexOfNat_val_of_m8BoundaryIndex i]

/-- E14/Lemma 6 restricted to the finite `p_0, ..., p_13` spine vertices. -/
def FinitePQSpineLemma6E14NegativeAfterFact
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (K : M8FinitePQSpineCertificate D) : Prop :=
  forall i : M8BoundaryIndex,
    BoundaryWalkGapAt walk.data (K.pIndex i) ->
      BoundaryWalkNegativeAfterGapAt walk.data (K.pIndex i)

/-! ### E5 deficient-neighborhood reduction on the finite spine -/

/-- Finite `p/q` spine version of the E5 reduction: a gap-without-negative at
one of the named `p_i` indices only has to produce the paper's small
independent set with deficient outside neighborhood.  Minimality then
contradicts the checked E5 neighborhood theorem. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_deficientIndependentSetContradiction
    {Cfg : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkGapAt walk.data (K.pIndex i) ->
        Not (BoundaryWalkNegativeAfterGapAt walk.data (K.pIndex i)) ->
          Exists fun S : Finset (Fin n) =>
            S.Nonempty /\
            Cfg.IsIndep S /\
            S.card <= 8 /\
            (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
              3 * S.card) :
    FinitePQSpineLemma6E14NegativeAfterFact walk K := by
  intro i hgap
  by_contra hnegative
  exact
    DeficientNeighborhood.false_of_minimalFailure_deficientIndependentSet
      hmin (H i hgap hnegative)

/-- Finite `p/q` spine form of the local E5 carrier reduction for Lemma 6.

For each named spine index, failure of negative-after is unpacked into the
concrete local endpoint facts, and the remaining obligation is exactly to
construct the small independent deficient-neighborhood set. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_localGapDeficientIndependentSet
    {Cfg : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkGapAt walk.data (K.pIndex i) ->
        walk.data.edgeKind (D.core.outerCycle.next (K.pIndex i)) =
          BoundaryEdgeClass.triangle ->
        (walk.data.vertexKind (D.core.outerCycle.next (K.pIndex i)) =
            BoundaryDegreeClass.degree3 \/
          walk.data.vertexKind (D.core.outerCycle.next (K.pIndex i)) =
            BoundaryDegreeClass.degree4) ->
          Exists fun S : Finset (Fin n) =>
            S.Nonempty /\
            Cfg.IsIndep S /\
            S.card <= 8 /\
            (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
              3 * S.card) :
    FinitePQSpineLemma6E14NegativeAfterFact walk K :=
  finitePQSpineLemma6E14NegativeAfterFact_of_deficientIndependentSetContradiction
    hmin K
    (by
      intro i hgap hnot
      rcases BoundaryWalkNegativeAfterGapAt.localData_of_not
          (walk := walk.data) (k := K.pIndex i) hnot with
        ⟨htriangle, hdegree⟩
      exact H i hgap htriangle hdegree)

/-- Finite `p/q` spine version of the direct E13 reduction: for every named
spine index, a gap with no negative-after only has to produce a concrete
subpolygon carrier in the same family with `2 * D2 + D3 < 6`.  The checked
E13 low-degree theorem for the planar-boundary package then forces the desired
negative-after conclusion. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_subpolygonLowDegreeContradiction
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalUDGraph Cfg)}
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkGapAt walk.data (K.pIndex i) ->
        Not (BoundaryWalkNegativeAfterGapAt walk.data (K.pIndex i)) ->
          Exists fun S : Subpolygon =>
            2 * (subpolygonData S).counts.D2 +
                (subpolygonData S).counts.D3 < 6) :
    FinitePQSpineLemma6E14NegativeAfterFact walk K := by
  intro i hgap
  by_contra hnegative
  rcases H i hgap hnegative with ⟨S, hstrict⟩
  have hlow :
      6 <=
        2 * (subpolygonData S).counts.D2 +
          (subpolygonData S).counts.D3 := by
    exact
      PlanarBoundaryFinal.PlanarBoundaryData.subpolygonLowDegreeInequality_viaBoundaryCounting
        (walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
          geometric_le_polygon Subpolygon subpolygonData)
        S
  exact (not_lt_of_ge hlow) hstrict

/-- Finite `p/q` spine form of the local E13 carrier reduction for Lemma 6.

For each named spine index, the no-negative-after case is reduced to a concrete
carrier in the same `subpolygonData` family plus explicit `D2`/`D3` count data
below the E13 threshold. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_localGapSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalUDGraph Cfg)}
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkGapAt walk.data (K.pIndex i) ->
        walk.data.edgeKind (D.core.outerCycle.next (K.pIndex i)) =
          BoundaryEdgeClass.triangle ->
        (walk.data.vertexKind (D.core.outerCycle.next (K.pIndex i)) =
            BoundaryDegreeClass.degree3 \/
          walk.data.vertexKind (D.core.outerCycle.next (K.pIndex i)) =
            BoundaryDegreeClass.degree4) ->
          Exists fun S : Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (subpolygonData S).counts.D2 = D2 /\
                (subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    FinitePQSpineLemma6E14NegativeAfterFact walk K := by
  exact
    finitePQSpineLemma6E14NegativeAfterFact_of_subpolygonLowDegreeContradiction
      (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon)
      (subpolygonData := subpolygonData)
      K
      (by
        intro i hgap hnot
        rcases BoundaryWalkNegativeAfterGapAt.localData_of_not
            (walk := walk.data) (k := K.pIndex i) hnot with
          ⟨htriangle, hdegree⟩
        rcases H i hgap htriangle hdegree with
          ⟨S, D2, D3, hD2, hD3, hstrict⟩
        exact ⟨S, subpolygonStrictLowDegree_of_countData
          (S := S) (D2 := D2) (D3 := D3) hD2 hD3 hstrict⟩)

/-- Finite `p/q` spine version for the concrete classified boundary walk and a
concrete core subpolygon family. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_classificationCoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} D.core)
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum}
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkGapAt classification.toOuterBoundaryWalkBookkeeping.data
          (K.pIndex i) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
          (D.core.outerCycle.edge (D.core.outerCycle.next (K.pIndex i))) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (D.core.outerCycle.vertex (D.core.outerCycle.next (K.pIndex i))) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (D.core.outerCycle.vertex (D.core.outerCycle.next (K.pIndex i)))) ->
          Exists fun S : F.Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (F.subpolygonData S).counts.D2 = D2 /\
                (F.subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    FinitePQSpineLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping K := by
  exact
    finitePQSpineLemma6E14NegativeAfterFact_of_localGapSubpolygonCarrierCountData
      (walk := classification.toOuterBoundaryWalkBookkeeping)
      (Subpolygon := F.Subpolygon)
      (subpolygonData :=
        fun S => (F.subpolygonData S).toSubpolygonCycleCountAngleData)
      (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      K
      (by
        intro i hgap htriangleClass hdegreeClass
        have htriangle :
            BoundaryWalkClassificationConcrete.IsTriangleEdge
              (CanonicalUDGraph Cfg)
              (D.core.outerCycle.edge
                (D.core.outerCycle.next (K.pIndex i))) :=
          classification.toOuterBoundaryWalkBookkeeping.data.edge_triangleEvidence
            (D.core.outerCycle.next (K.pIndex i)) htriangleClass
        have hdegree :
            BoundaryWalkClassificationConcrete.IsDegree3
                (CanonicalUDGraph Cfg)
                (D.core.outerCycle.vertex
                  (D.core.outerCycle.next (K.pIndex i))) \/
              BoundaryWalkClassificationConcrete.IsDegree4
                (CanonicalUDGraph Cfg)
                (D.core.outerCycle.vertex
                  (D.core.outerCycle.next (K.pIndex i))) := by
          rcases hdegreeClass with hdegree3 | hdegree4
          · exact Or.inl
              (classification.toOuterBoundaryWalkBookkeeping.data.degree3Evidence
                (D.core.outerCycle.next (K.pIndex i)) hdegree3)
          · exact Or.inr
              (classification.toOuterBoundaryWalkBookkeeping.data.degree4Evidence
                (D.core.outerCycle.next (K.pIndex i)) hdegree4)
        rcases H i hgap htriangle hdegree with
          ⟨S, D2, D3, hD2, hD3, hstrict⟩
        exact ⟨S, D2, D3, by exact hD2, by exact hD3, hstrict⟩)

/-- Finite `p/q` spine strict-carrier closure from the actual concrete local
gap fields at the selected spine index.

This is the finite-spine form of the same local row: the caller constructs a
carrier/count datum from the concrete degree-three gap, non-long-arc fact,
triangular next edge, and next-vertex degree-three/four alternative. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} D.core)
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum}
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (D.core.outerCycle.vertex (K.pIndex i)) ->
        Not (classification.longArc (K.pIndex i)) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge
          (CanonicalUDGraph Cfg)
          (D.core.outerCycle.edge
            (D.core.outerCycle.next (K.pIndex i))) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (D.core.outerCycle.vertex
              (D.core.outerCycle.next (K.pIndex i))) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (D.core.outerCycle.vertex
              (D.core.outerCycle.next (K.pIndex i)))) ->
          Exists fun S : F.Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (F.subpolygonData S).counts.D2 = D2 /\
                (F.subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    FinitePQSpineLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping K := by
  exact
    finitePQSpineLemma6E14NegativeAfterFact_of_classificationCoreSubpolygonCarrierCountData
      (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      classification F K
      (by
        intro i hgap htriangle hdegree
        have hgapDegree :
            BoundaryWalkClassificationConcrete.IsDegree3
              (CanonicalUDGraph Cfg)
              (D.core.outerCycle.vertex (K.pIndex i)) :=
          (BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff
            D.core (K.pIndex i)).1 hgap.1
        have hnotLong : Not (classification.longArc (K.pIndex i)) := hgap.2
        exact H i hgapDegree hnotLong htriangle hdegree)

/-- Finite `p/q` spine closure from the pointwise actual classified local
strict-carrier source. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} D.core)
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum}
    (K : M8FinitePQSpineCertificate D)
    (H :
      LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
        D.core classification.longArc F) :
    FinitePQSpineLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping K :=
  finitePQSpineLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountData
    (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    classification F K
    (by
      intro i hgapDegree hnotLong htriangle hdegree
      rcases
        H (K.pIndex i)
          { gapDegree := hgapDegree
            notLongArc := hnotLong
            triangleNext := htriangle
            nextDegree := hdegree } with
        ⟨carrier⟩
      exact carrier.toExists)

/-- Finite `p/q` spine closure from a single exact strict carrier in the
actual classified core-subpolygon family. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_coreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} D.core)
    {geometricAngleSum : Real}
    {forced_le_geometric :
      classification.toOuterBoundaryWalkBookkeeping.counts.forcedBoundaryAngleSum <=
        geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <=
        classification.toOuterBoundaryWalkBookkeeping.counts.polygonAngleSum}
    (K : M8FinitePQSpineCertificate D)
    (carrier : SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F) :
    FinitePQSpineLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping K :=
  finitePQSpineLemma6E14NegativeAfterFact_of_concreteLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataSource
    (geometricAngleSum := geometricAngleSum)
    (forced_le_geometric := forced_le_geometric)
    (geometric_le_polygon := geometric_le_polygon)
    classification F K
    (localGapTriangleDegree34CoreSubpolygonCarrierCountData_of_coreSubpolygonCarrierCountData
      (Pcfg := D.core) (longArc := classification.longArc) carrier)

/-- Finite `p/q` spine version of the combined local E5/E13 carrier route for
the concrete classified boundary walk. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_classificationDeficientSetOrCoreSubpolygonCarrierCountData
    {Cfg : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure Cfg)
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} D.core)
    (K : M8FinitePQSpineCertificate D)
    (H :
      forall i : M8BoundaryIndex,
        BoundaryWalkGapAt classification.toOuterBoundaryWalkBookkeeping.data
          (K.pIndex i) ->
        BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
          (D.core.outerCycle.edge (D.core.outerCycle.next (K.pIndex i))) ->
        (BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
            (D.core.outerCycle.vertex (D.core.outerCycle.next (K.pIndex i))) \/
          BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
            (D.core.outerCycle.vertex (D.core.outerCycle.next (K.pIndex i)))) ->
          (Exists fun S : Finset (Fin n) =>
            S.Nonempty /\
            Cfg.IsIndep S /\
            S.card <= 8 /\
            (SmallIndependentNeighborhood.outsideNeighborhoodOf Cfg S).card <
              3 * S.card) \/
          Exists fun S : F.Subpolygon =>
            Exists fun D2 : Nat =>
              Exists fun D3 : Nat =>
                (F.subpolygonData S).counts.D2 = D2 /\
                (F.subpolygonData S).counts.D3 = D3 /\
                2 * D2 + D3 < 6) :
    FinitePQSpineLemma6E14NegativeAfterFact
      classification.toOuterBoundaryWalkBookkeeping K := by
  intro i hgap
  by_contra hnegative
  rcases BoundaryWalkNegativeAfterGapAt.localData_of_not
      (walk := classification.toOuterBoundaryWalkBookkeeping.data)
      (k := K.pIndex i) hnegative with
    ⟨htriangle, hdegree⟩
  have htriangleConcrete :
      BoundaryWalkClassificationConcrete.IsTriangleEdge (CanonicalUDGraph Cfg)
        (D.core.outerCycle.edge (D.core.outerCycle.next (K.pIndex i))) :=
    BoundaryWalkClassificationConcrete.edgeKind_triangleEvidence D.core
      (D.core.outerCycle.next (K.pIndex i)) htriangle
  have hdegreeConcrete :
      BoundaryWalkClassificationConcrete.IsDegree3 (CanonicalUDGraph Cfg)
          (D.core.outerCycle.vertex (D.core.outerCycle.next (K.pIndex i))) \/
        BoundaryWalkClassificationConcrete.IsDegree4 (CanonicalUDGraph Cfg)
          (D.core.outerCycle.vertex (D.core.outerCycle.next (K.pIndex i))) := by
    rcases hdegree with hdegree3 | hdegree4
    · exact Or.inl
        ((BoundaryWalkClassificationConcrete.vertexKind_eq_degree3_iff D.core
          (D.core.outerCycle.next (K.pIndex i))).1 hdegree3)
    · exact Or.inr
        ((BoundaryWalkClassificationConcrete.vertexKind_eq_degree4_iff D.core
          (D.core.outerCycle.next (K.pIndex i))).1 hdegree4)
  rcases H i hgap htriangleConcrete hdegreeConcrete with
    hdeficient | hcarrier
  · exact
      DeficientNeighborhood.false_of_minimalFailure_deficientIndependentSet
        hmin hdeficient
  · rcases hcarrier with ⟨S, D2, D3, hD2, hD3, hstrict⟩
    have hlow := F.subpolygonLowDegree S
    have hstrict' :
        2 * (F.subpolygonData S).counts.D2 +
            (F.subpolygonData S).counts.D3 < 6 := by
      rw [hD2, hD3]
      exact hstrict
    exact (not_lt_of_ge hlow) hstrict'

/-- The full boundary-walk E14 fact restricts to the finite `p/q` spine. -/
theorem finitePQSpineLemma6E14NegativeAfterFact_of_boundaryWalkFact
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D)
    (H : BoundaryWalkLemma6E14NegativeAfterFact walk) :
    FinitePQSpineLemma6E14NegativeAfterFact walk K :=
  fun i => H (K.pIndex i)

/-- The finite `p/q` spine plus the named E14 fact gives the generic
gap-to-negative certificate at any Nat-indexed M8 arc position. -/
def lemma6GapToNegativeCertificate_ofFinitePQSpineE14Fact
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    {geometricAngleSum : Real}
    {forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
    {geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalUDGraph Cfg)}
    (K : M8FinitePQSpineCertificate D)
    (H : FinitePQSpineLemma6E14NegativeAfterFact walk K)
    (k : Nat) :
    Lemma6GapToNegativeCertificate
      (walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData)
      ((ofFinitePQSpineCertificate (walk := walk) K).gapAt k)
      ((ofFinitePQSpineCertificate (walk := walk) K).negativeAfterAt k) where
  gap_without_negative_violates_subpolygon_low_degree := by
    intro hgap hnot
    exact False.elim (hnot (H (m8BoundaryIndexOfNat k) hgap))

/-- Nat-indexed E14/Lemma 6 consequence on the finite `p/q` spine. -/
theorem negativeAfterAt_of_gapAt_ofFinitePQSpineE14Fact
    {Cfg : _root_.UDConfig n}
    {D :
      PlanarBoundaryClosure.PlanarBoundaryData.{u}
        (CanonicalUDGraph Cfg)}
    {IsTriangle IsNontriangle : Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    {walk :
      OuterBoundaryWalkBookkeeping D.core IsTriangle IsNontriangle
        IsDegree3 IsDegree4 IsDegree5 IsDegree6}
    (K : M8FinitePQSpineCertificate D)
    (H : FinitePQSpineLemma6E14NegativeAfterFact walk K)
    (k : Nat) :
    (ofFinitePQSpineCertificate (walk := walk) K).gapAt k ->
      (ofFinitePQSpineCertificate (walk := walk) K).negativeAfterAt k :=
  fun hgap => H (m8BoundaryIndexOfNat k) hgap

end BoundaryArcIndexMap

/-- Boundary-walk data plus the remaining Lemma 7 arithmetic facts, with the
Lemma 6 field supplied by `BoundaryWalkLemma6Obstruction`. -/
structure BoundaryArcLemma7Data
    (O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) where
  indexMap : BoundaryArcIndexMap walk
  rawTurn : Nat -> Real
  geometricAngleBudget : Real
  negative_absent_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k ->
      Not (indexMap.negativeAfterAt k)
  rawTurn_nonnegative_of_no_gap :
    forall k : Nat, Membership.mem turnIndexSet k ->
      Not (indexMap.gapAt k) -> 0 <= rawTurn k
  totalTurn_le_geometricAngleBudget_of_no_gap :
    (forall k : Nat, Membership.mem turnIndexSet k ->
      Not (indexMap.gapAt k)) ->
        totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace BoundaryArcLemma7Data

/-- Convert the boundary-walk Lemma 6 data into the existing Nat-indexed
Lemma 7 certificate. -/
def toLemma7ArcAngleCertificate
    {O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}
    (A : BoundaryArcLemma7Data O) :
    Lemma7ArcAngleCertificate O.planarBoundary where
  rawTurn := A.rawTurn
  geometricAngleBudget := A.geometricAngleBudget
  gapAt := A.indexMap.gapAt
  negativeAt := A.indexMap.negativeAfterAt
  lemma6_gap_forces_negative := by
    intro k _hk
    exact A.indexMap.lemma6GapToNegativeCertificate O k
  negative_absent_on_arc := A.negative_absent_on_arc
  rawTurn_nonnegative_of_no_gap := A.rawTurn_nonnegative_of_no_gap
  totalTurn_le_geometricAngleBudget_of_no_gap :=
    A.totalTurn_le_geometricAngleBudget_of_no_gap
  geometricAngleBudget_lt_pi_div_three :=
    A.geometricAngleBudget_lt_pi_div_three

/-- The project-local data therefore supplies the downstream geometric angle
facts. -/
def toNonconcaveArcGeometricAngleFacts
    {O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}
    (A : BoundaryArcLemma7Data O) :
    NonconcaveArcGeometricAngleFacts :=
  A.toLemma7ArcAngleCertificate.toNonconcaveArcGeometricAngleFacts

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_rawTurn
    {O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}
    (A : BoundaryArcLemma7Data O) :
    A.toNonconcaveArcGeometricAngleFacts.rawTurn = A.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_geometricAngleBudget
    {O :
      BoundaryWalkLemma6Obstruction walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}
    (A : BoundaryArcLemma7Data O) :
    A.toNonconcaveArcGeometricAngleFacts.geometricAngleBudget =
      A.geometricAngleBudget :=
  rfl

end BoundaryArcLemma7Data

end Lemma6NegativeAfterGapW12
end Swanepoel
end ErdosProblems1066

end
