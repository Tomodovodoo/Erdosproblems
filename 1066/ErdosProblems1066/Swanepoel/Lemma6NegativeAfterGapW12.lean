import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts
import ErdosProblems1066.Swanepoel.BoundaryWalkConstruction

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
open BoundaryWalkConstruction
open Lemma10Inequalities
open M8TurnBoundsFromArc
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

end BoundaryWalkLemma6Obstruction

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
