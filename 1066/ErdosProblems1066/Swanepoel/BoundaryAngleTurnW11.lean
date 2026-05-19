import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10
import ErdosProblems1066.Swanepoel.BoundaryAngleAssembly
import ErdosProblems1066.Swanepoel.BoundaryAngleCertificatesConcrete
import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts
import ErdosProblems1066.Swanepoel.LongArcGapConcrete
import ErdosProblems1066.Swanepoel.SwanepoelRemainingMatrix
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17
import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24

set_option autoImplicit false

/-!
# W11 boundary angle and turn package

This module is a packaging layer over the W10 classified-boundary count/turn
input.  It keeps the concrete local angle certificates, long-arc count gap,
selected nonconcave arc, and M8 turn-bound outputs tied to the same boundary
classification and subpolygon data.

The second half gives adapters into the row shapes used by the W9 and W10
closure matrices once the unrelated label, no-early, K23, and window fields
are supplied.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleTurnW11

open BoundaryCountingInstantiationW10
open BoundaryWalkClassificationConcrete
open Lemma10Inequalities

universe u

noncomputable section

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

namespace ClassifiedBoundary

variable {D : OuterBoundaryClassificationInputs P}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- W11 wrapper for the W10 classified boundary angle/count-gap input. -/
structure BoundaryAngleTurnPackage
    (D : OuterBoundaryClassificationInputs P)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  countTurn :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.CountTurnInput
      D Subpolygon subpolygonData

namespace BoundaryAngleTurnPackage

variable (Q : BoundaryAngleTurnPackage D Subpolygon subpolygonData)

/-- The local unit-separated angle witness family. -/
def angleWitness :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
      D :=
  Q.countTurn.angleWitness

/-- Count-indexed local angles consumed by `BoundaryAngleAssembly`. -/
def localAngles :
    BoundaryAngleAssembly.OuterBoundaryLocalAngles G D.counts :=
  Q.angleWitness.toOuterBoundaryLocalAngles

/-- The explicit geometric witness for the count-indexed local angles. -/
def geometricWitness :
    BoundaryAngleAssembly.OuterBoundaryGeometricWitness Q.localAngles :=
  Q.angleWitness.toGeometricWitness

/-- Concrete graph-angle certificates for the outer-boundary E12 count. -/
def concreteAngleCertificates :
    BoundaryAngleCertificatesConcrete.OuterBoundaryAngleCertificates
      G D.counts :=
  Q.angleWitness.toConcreteCertificates

/-- The per-class outer-boundary angle realization obtained from certificates. -/
def outerBoundaryAngleRealization :
    BoundaryAngleRealization.OuterBoundaryAngleRealization :=
  Q.concreteAngleCertificates.toOuterBoundaryAngleRealization

/-- The angle-bound record consumed by planar-boundary closure modules. -/
def outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := D.countsRealizationLift
  geometricAngleSum := Q.angleWitness.geometricAngleSum
  forced_le_geometric := Q.angleWitness.forced_le_geometricAngleSum
  geometric_le_polygon := Q.angleWitness.geometric_le_polygon

@[simp]
theorem outerAngleBounds_counts :
    Q.outerAngleBounds.counts = D.counts :=
  rfl

@[simp]
theorem outerAngleBounds_geometricAngleSum :
    Q.outerAngleBounds.geometricAngleSum =
      Q.angleWitness.geometricAngleSum :=
  rfl

/-- Outer-boundary angle data with the selected outer core. -/
def outerBoundaryAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G where
  core := P
  angleBounds := Q.outerAngleBounds

@[simp]
theorem outerBoundaryAngleData_core :
    Q.outerBoundaryAngleData.core = P :=
  rfl

@[simp]
theorem outerBoundaryAngleData_counts :
    Q.outerBoundaryAngleData.counts = D.counts :=
  rfl

/-- Matched bookkeeping and explicit angle realization data. -/
def boundaryBookkeepingAngleRealization :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleRealization.{u} where
  countsRealization := D.countsRealizationLift
  angleRealization := Q.outerBoundaryAngleRealization
  angle_counts_eq_realized := rfl

/-- Outer-boundary realized-angle data with the selected outer core. -/
def outerBoundaryRealizedAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G where
  core := P
  angleRealization := Q.boundaryBookkeepingAngleRealization

/-- The counting-layer boundary angle lower bound. -/
theorem angleLowerBound
    (Q : BoundaryAngleTurnPackage D Subpolygon subpolygonData) :
    D.counts.AngleLowerBound :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies.angleLowerBound
    Q.angleWitness

/-- E12 in concrete boundary-count form. -/
theorem boundaryAngleCountInequality
    (Q : BoundaryAngleTurnPackage D Subpolygon subpolygonData) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.CountTurnInput.boundaryAngleCountInequality
    Q.countTurn

/-- Negative-element E12 in concrete boundary-count form. -/
theorem boundaryNegativeCountInequality
    (Q : BoundaryAngleTurnPackage D Subpolygon subpolygonData) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.CountTurnInput.boundaryNegativeCountInequality
    Q.countTurn

/-- The planar-boundary package built from the same angle and subpolygon data. -/
def planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  Q.countTurn.planarBoundary

@[simp]
theorem planarBoundary_outerBoundaryCounts :
    Q.planarBoundary.outerBoundaryCounts = D.counts :=
  Q.countTurn.planarBoundary_outerBoundaryCounts

/-- The theorem summary supplied by the planar-boundary data. -/
theorem faceCountingTheorems :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      Q.planarBoundary :=
  Q.planarBoundary.faceCountingTheorems

/-- The long-arc existence fields attached to the same planar-boundary data. -/
def boundaryLongArcExistenceFields :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      Q.planarBoundary :=
  Q.countTurn.toBoundaryLongArcExistenceFields

/-- Classified-boundary count-gap wrapper. -/
def classifiedBoundaryCountGapInput :
    LongArcGapConcrete.ClassifiedBoundaryCountGapInput
      D Q.angleWitness.geometricAngleSum
        Q.angleWitness.forced_le_geometricAngleSum
        Q.angleWitness.geometric_le_polygon Subpolygon subpolygonData :=
  Q.countTurn.toClassifiedBoundaryCountGapInput

/-- Full boundary-count-gap route to M8 turn bounds. -/
def boundaryCountGapToM8TurnBounds :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      Q.boundaryLongArcExistenceFields :=
  Q.countTurn.toBoundaryCountGapToM8TurnBounds

/-- Boundary-attached budget data for the selected nonconcave arc. -/
def nonconcaveArcBoundaryBudgetData :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  Q.countTurn.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem nonconcaveArcBoundaryBudgetData_planarBoundary :
    Q.nonconcaveArcBoundaryBudgetData.planarBoundary = Q.planarBoundary :=
  rfl

/-- The generic geometric angle facts for the selected nonconcave arc. -/
def nonconcaveArcGeometricAngleFacts :
    NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts :=
  Q.boundaryLongArcExistenceFields.toNonconcaveArcGeometricAngleFacts

/-- Normalized nonconcave-arc turn data selected by the long-arc gap. -/
def nonconcaveArcTurnData :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  Q.boundaryLongArcExistenceFields.toNonconcaveArcTurnData

/-- Honest turn bounds produced by the selected long arc. -/
def honestTurnBounds :
    TurnBoundsInterface.HonestTurnBounds :=
  Q.countTurn.honestTurnBounds

/-- Construction-level M8 turn bounds produced by the selected long arc. -/
def m8TurnBounds :
    M8ConstructionInterface.M8TurnBounds :=
  Q.countTurn.m8TurnBounds

/-- Output bundle from the selected nonconcave-arc angle facts. -/
def m8TurnBoundOutputs :
    NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts.M8TurnBoundOutputs
      Q.nonconcaveArcGeometricAngleFacts :=
  Q.nonconcaveArcGeometricAngleFacts.toM8TurnBoundOutputs

/-- The selected long-arc index. -/
def selectedLongArc :
    D.longArcIndices :=
  Q.countTurn.selectedLongArc

/-- The selected long arc is not concave. -/
theorem selectedLongArc_not_concave :
    Not (Q.countTurn.longArcFields.concave Q.selectedLongArc) :=
  Q.countTurn.selectedLongArc_not_concave

/-- The selected long arc has raw total turn below `pi / 3`. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three :
    totalTurn (Q.countTurn.longArcFields.rawTurn Q.selectedLongArc) <
      Real.pi / 3 :=
  Q.countTurn.selectedLongArc_totalTurn_lt_pi_div_three

/-- The selected M8 turn function is pointwise nonnegative. -/
theorem m8TurnBounds_turn_nonnegative (k : Nat) :
    0 <= Q.m8TurnBounds.turn k :=
  Q.countTurn.m8TurnBounds_turn_nonnegative k

/-- The selected M8 turn function has total turn below `pi / 3`. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three :
    totalTurn Q.m8TurnBounds.turn < Real.pi / 3 :=
  Q.countTurn.m8TurnBounds_totalTurn_lt_pi_div_three

/-- The selected M8 thirteen-turn sum is below `pi / 3`. -/
theorem m8TurnBounds_thirteenTurnSum_lt_pi_div_three :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      Q.m8TurnBounds.turn < Real.pi / 3 :=
  Q.countTurn.m8TurnBounds_thirteenTurnSum_lt_pi_div_three

/-- The honest turn-bound package has total turn below `pi / 3`. -/
theorem honestTurnBounds_totalTurn_lt_pi_div_three :
    totalTurn Q.honestTurnBounds.turn < Real.pi / 3 :=
  Q.countTurn.honestTurnBounds_totalTurn_lt_pi_div_three

end BoundaryAngleTurnPackage

end ClassifiedBoundary

/-! ## Adapters for the UDConfig closure rows -/

namespace UDConfigRoute

variable {C : _root_.UDConfig n}

/-- Boundary angle and turn data tied to a concrete topology row. -/
structure BoundaryAngleTurnTopologyPackage (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C
  classification :
    OuterBoundaryClassificationInputs topology.toCore
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData
        (JordanTopologyFactsConcrete.canonicalGraph C)
  boundary :
    ClassifiedBoundary.BoundaryAngleTurnPackage
      classification Subpolygon subpolygonData

namespace BoundaryAngleTurnTopologyPackage

variable (Q : BoundaryAngleTurnTopologyPackage.{u} C)

/-- The outer-angle row consumed by topology/angle/subpolygon closures. -/
def outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  Q.boundary.outerAngleBounds

/-- The planar boundary assembled by the W11 package. -/
def planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  Q.boundary.planarBoundary

/-- Long-arc fields in the exact W9 topology row shape. -/
def w9LongArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (Q.topology.toPlanarBoundaryData Q.outerAngleBounds
        Q.Subpolygon Q.subpolygonData) := by
  change LongArcExistenceConcrete.BoundaryLongArcExistenceFields
    Q.boundary.planarBoundary
  exact Q.boundary.boundaryLongArcExistenceFields

/-- The W24 minimal-boundary skeleton determined by the checked W11 concrete
topology, classification, angle, and subpolygon rows. -/
def toMinimalBoundaryTopologySkeleton
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.{u}
      C hmin where
  topology := Q.topology
  classification := Q.classification
  geometricAngleSum := Q.boundary.angleWitness.geometricAngleSum
  forced_le_geometric := Q.boundary.angleWitness.forced_le_geometricAngleSum
  geometric_le_polygon := Q.boundary.angleWitness.geometric_le_polygon
  Subpolygon := Q.Subpolygon
  subpolygonData := Q.subpolygonData

theorem toMinimalBoundaryTopologySkeleton_planarBoundary
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).planarBoundary =
      Q.topology.toPlanarBoundaryData Q.outerAngleBounds
        Q.Subpolygon Q.subpolygonData :=
  rfl

/-- The long-arc half of the W24 skeleton's missing field, projected from the
same selected boundary count, angle, and long-arc rows. -/
def minimalBoundaryTopologySkeletonLongArc
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      (Q.toMinimalBoundaryTopologySkeleton hmin).planarBoundary := by
  change LongArcExistenceConcrete.BoundaryLongArcExistenceFields
    (Q.topology.toPlanarBoundaryData Q.outerAngleBounds
      Q.Subpolygon Q.subpolygonData)
  exact Q.w9LongArc

@[simp]
theorem minimalBoundaryTopologySkeletonLongArc_LongArc
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (Q.minimalBoundaryTopologySkeletonLongArc hmin).LongArc =
      Q.classification.longArcIndices :=
  rfl

/-- The W11-produced skeleton long-arc field uses exactly the classified
boundary long-arc indices, so its finite count is the boundary `B` count. -/
theorem minimalBoundaryTopologySkeletonLongArc_longArcCount_eq_counts_B
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (Q.minimalBoundaryTopologySkeletonLongArc hmin).longArcCount =
      Q.classification.counts.B := by
  change
    @Fintype.card Q.classification.longArcIndices inferInstance =
      Q.classification.counts.B
  exact
    BoundaryPartitionInstantiation.ClassifiedBoundary.longArcIndex_card_eq_counts_B
      Q.classification

/-- Once the independent triangle run is supplied, the W11 rows fill the
long-arc half of the W24 missing-field record automatically. -/
def missingLongArcTriangleRunFieldOfTriangleRun
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (triangleRun :
      BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
        (Q.toMinimalBoundaryTopologySkeleton hmin).planarBoundary) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField where
  longArc := Q.minimalBoundaryTopologySkeletonLongArc hmin
  triangleRun := triangleRun

@[simp]
theorem missingLongArcTriangleRunFieldOfTriangleRun_longArc
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (triangleRun :
      BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
        (Q.toMinimalBoundaryTopologySkeleton hmin).planarBoundary) :
    (Q.missingLongArcTriangleRunFieldOfTriangleRun hmin triangleRun).longArc =
      Q.minimalBoundaryTopologySkeletonLongArc hmin :=
  rfl

@[simp]
theorem missingLongArcTriangleRunFieldOfTriangleRun_triangleRun
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (triangleRun :
      BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
        (Q.toMinimalBoundaryTopologySkeleton hmin).planarBoundary) :
    (Q.missingLongArcTriangleRunFieldOfTriangleRun hmin triangleRun).triangleRun =
      triangleRun :=
  rfl

/-- A pointwise W17-compatible triangle-run target fills the exact W24 missing
field for the skeleton produced by this W11 package. -/
def missingLongArcTriangleRunFieldOfTriangleRunTarget
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hRun :
      Nonempty
        (BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
          (Q.toMinimalBoundaryTopologySkeleton hmin).planarBoundary)) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField :=
  Q.missingLongArcTriangleRunFieldOfTriangleRun hmin (Classical.choice hRun)

/-- A uniform W17 triangle-run theorem supplies the missing field for exactly
the W24 skeleton assembled from this W11 package. -/
def missingLongArcTriangleRunFieldOfTriangleRunTheorem
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (Hrun :
      BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRunTheorem.{u}) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField := by
  refine Q.missingLongArcTriangleRunFieldOfTriangleRunTarget hmin ?_
  change
    Nonempty
      (BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
        (Q.topology.toPlanarBoundaryData Q.outerAngleBounds
          Q.Subpolygon Q.subpolygonData))
  exact
    (Hrun C Q.topology Q.outerAngleBounds Q.Subpolygon Q.subpolygonData
      Q.w9LongArc)

/-- A pointwise W14 extraction target, converted through W17, fills the exact
missing field for the W11-produced skeleton. -/
def missingLongArcTriangleRunFieldOfExtractionTarget
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (h :
      TopologyToBoundaryArcW14.BoundaryArcExtractionTarget
        Q.topology Q.outerAngleBounds Q.Subpolygon Q.subpolygonData
        Q.w9LongArc) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField := by
  refine Q.missingLongArcTriangleRunFieldOfTriangleRunTarget hmin ?_
  change
    Nonempty
      (BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
        (Q.topology.toPlanarBoundaryData Q.outerAngleBounds
          Q.Subpolygon Q.subpolygonData))
  exact TriangleRunSelectorW17.triangleRunTarget_of_extractionTarget h

/-- A pointwise W15 finite-walk target, converted through W17, fills the exact
missing field for the W11-produced skeleton. -/
def missingLongArcTriangleRunFieldOfFiniteWalkTarget
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (h :
      BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkTarget
        Q.topology Q.outerAngleBounds Q.Subpolygon Q.subpolygonData
        Q.w9LongArc) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField := by
  refine Q.missingLongArcTriangleRunFieldOfTriangleRunTarget hmin ?_
  change
    Nonempty
      (BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
        (Q.topology.toPlanarBoundaryData Q.outerAngleBounds
          Q.Subpolygon Q.subpolygonData))
  exact TriangleRunSelectorW17.triangleRunTarget_of_finiteWalkTarget h

/-- A uniform W14 extraction theorem, routed through W17's triangle-run theorem
surface, fills the exact missing field for the W11-produced skeleton. -/
def missingLongArcTriangleRunFieldOfExtractionTheorem
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (H : TopologyToBoundaryArcW14.BoundaryArcExtractionTheorem.{u}) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField :=
  Q.missingLongArcTriangleRunFieldOfTriangleRunTheorem hmin
    (TriangleRunSelectorW17.triangleRunTheorem_of_extractionTheorem H)

/-- A uniform W15 finite-walk theorem, routed through W17's triangle-run theorem
surface, fills the exact missing field for the W11-produced skeleton. -/
def missingLongArcTriangleRunFieldOfFiniteWalkTheorem
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (H : BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkTheorem.{u}) :
    (Q.toMinimalBoundaryTopologySkeleton hmin).MissingLongArcTriangleRunField :=
  Q.missingLongArcTriangleRunFieldOfTriangleRunTheorem hmin
    (TriangleRunSelectorW17.triangleRunTheorem_of_finiteWalkTheorem H)

/-! ## Raw boundary-turn rows from actual angle certificates -/

/--
Actual local turn-angle rows for the W24 skeleton raw-turn source.

The count inequality is the Lemma 6/7 coverage row already required by
`LongArcRawTurnRows`.  The new content here is the raw turn itself: each
thirteen-turn slot is represented by a concrete unit-separated Euclidean angle
whose center is an actual outer-boundary vertex, whose right side is the cyclic
successor, and whose left side is a cyclic predecessor.  The downstream
raw-turn value is the actual angle value of this certificate, so pointwise
nonnegativity is checked by `UnitSeparatedAngle.value_nonnegative`.
-/
structure MinimalBoundaryTopologyBoundaryTurnAngleRows
    (S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}) :
    Type (u + 1) where
  degreeThree_le_negativeCount_add_longArcCount :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.counts.d3 <=
          (S.row C hmin).classification.counts.negativeCount +
            @Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance
  turnVertex :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.longArcIndices -> Nat ->
          Fin (S.row C hmin).topology.toCore.outerCycle.length
  turnAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (_a : (S.row C hmin).classification.longArcIndices)
      (k : Nat),
        Membership.mem Lemma10Inequalities.turnIndexSet k ->
          BoundaryAngleCertificatesConcrete.UnitSeparatedAngle
            (JordanBoundaryConcreteInhabitationW24.CanonicalGraph C)
  turnAngle_left_is_boundary_predecessor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (a : (S.row C hmin).classification.longArcIndices)
      (k : Nat)
      (hk : Membership.mem Lemma10Inequalities.turnIndexSet k),
        Exists fun pred :
          Fin (S.row C hmin).topology.toCore.outerCycle.length =>
            (turnAngle C hmin a k hk).left =
                (S.row C hmin).topology.toCore.outerCycle.vertex pred /\
              PlanarInterface.cyclicSucc
                  (S.row C hmin).topology.toCore.outerCycle.length_pos pred =
                turnVertex C hmin a k
  turnAngle_center_eq_turnVertex :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (a : (S.row C hmin).classification.longArcIndices)
      (k : Nat)
      (hk : Membership.mem Lemma10Inequalities.turnIndexSet k),
        (turnAngle C hmin a k hk).center =
          (S.row C hmin).topology.toCore.outerCycle.vertex
            (turnVertex C hmin a k)
  turnAngle_right_eq_successor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (a : (S.row C hmin).classification.longArcIndices)
      (k : Nat)
      (hk : Membership.mem Lemma10Inequalities.turnIndexSet k),
        (turnAngle C hmin a k hk).right =
          (S.row C hmin).topology.toCore.outerCycle.vertex
            (PlanarInterface.cyclicSucc
              (S.row C hmin).topology.toCore.outerCycle.length_pos
              (turnVertex C hmin a k))

namespace MinimalBoundaryTopologyBoundaryTurnAngleRows

variable {S :
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}

/-- Build actual boundary-turn angle rows once the remaining combinatorial
choice of turn slot to outer-boundary index has been supplied.

The angle certificate at each slot is the genuine
predecessor/current/successor angle of the selected outer cycle.  Thus the only
geometric input needed here is nondegeneracy of that cycle; the still-missing
S4 data is exactly the map from each long-arc turn slot to its boundary index.
-/
def ofOuterBoundaryTurnVertex
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (turnVertex :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices -> Nat ->
            Fin (S.row C hmin).topology.toCore.outerCycle.length) :
    MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount :=
    degreeThree_le_negativeCount_add_longArcCount
  turnVertex := turnVertex
  turnAngle := fun C hmin a k _hk =>
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
      (S.row C hmin).topology.toCore
      (outerCycle_length_ge_three C hmin)
      (turnVertex C hmin a k)
  turnAngle_left_is_boundary_predecessor := by
    intro n C hmin a k hk
    let v := turnVertex C hmin a k
    refine
      Exists.intro
        (PlanarInterface.cyclicPred
          (S.row C hmin).topology.toCore.outerCycle.length_pos v) ?_
    constructor
    · change
        (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
          (S.row C hmin).topology.toCore
          (outerCycle_length_ge_three C hmin) v).left =
            (S.row C hmin).topology.toCore.outerCycle.vertex
              (PlanarInterface.cyclicPred
                (S.row C hmin).topology.toCore.outerCycle.length_pos v)
      rfl
    · exact
        PlanarInterface.cyclicSucc_cyclicPred
          (S.row C hmin).topology.toCore.outerCycle.length_pos v
  turnAngle_center_eq_turnVertex := by
    intro n C hmin a k hk
    change
      (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
        (S.row C hmin).topology.toCore
        (outerCycle_length_ge_three C hmin)
        (turnVertex C hmin a k)).center =
          (S.row C hmin).topology.toCore.outerCycle.vertex
            (turnVertex C hmin a k)
    rfl
  turnAngle_right_eq_successor := by
    intro n C hmin a k hk
    change
      (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
        (S.row C hmin).topology.toCore
        (outerCycle_length_ge_three C hmin)
        (turnVertex C hmin a k)).right =
          (S.row C hmin).topology.toCore.outerCycle.vertex
            (PlanarInterface.cyclicSucc
              (S.row C hmin).topology.toCore.outerCycle.length_pos
              (turnVertex C hmin a k))
    rfl

/-- Minimal positive source for the W11 boundary-turn rows.

This is the exact remaining combinatorial choice isolated by
`ofOuterBoundaryTurnVertex`: for each classified long arc and each raw-turn
slot, name the outer-boundary vertex at which the real
predecessor/current/successor angle is measured. -/
structure MinimalBoundaryTopologyBoundaryTurnVertexRows
    (S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}) :
    Type (u + 1) where
  degreeThree_le_negativeCount_add_longArcCount :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.counts.d3 <=
          (S.row C hmin).classification.counts.negativeCount +
            @Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance
  outerCycle_length_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (S.row C hmin).topology.toCore.outerCycle.length
  turnVertex :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.longArcIndices -> Nat ->
          Fin (S.row C hmin).topology.toCore.outerCycle.length

namespace MinimalBoundaryTopologyBoundaryTurnVertexRows

variable {S :
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}

/-- Forget the vertex-row source to the checked real-angle row package. -/
def toBoundaryTurnAngleRows
    (V : MinimalBoundaryTopologyBoundaryTurnVertexRows.{u} S) :
    MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S :=
  MinimalBoundaryTopologyBoundaryTurnAngleRows.ofOuterBoundaryTurnVertex
    V.degreeThree_le_negativeCount_add_longArcCount
    V.outerCycle_length_ge_three
    V.turnVertex

/-- The thirteen M8 turn slots are the selected boundary positions
`p_1, ..., p_13` supplied by a concrete triangle run.  The long-arc index is
kept explicit because the downstream raw-turn rows are classified by the
boundary long-arc carrier, even when the current source names the same selected
M8 run for each carrier element. -/
def turnVertexOfTriangleRun
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (_a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) :
    Fin (S.row C hmin).topology.toCore.outerCycle.length :=
  (triangleRun C hmin).pIndex
    (Lemma6NegativeAfterGapW12.BoundaryArcIndexMap.m8BoundaryIndexOfNat k)

@[simp]
theorem turnVertexOfTriangleRun_eq
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) :
    turnVertexOfTriangleRun (S := S) triangleRun C hmin a k =
      (triangleRun C hmin).pIndex
        (Lemma6NegativeAfterGapW12.BoundaryArcIndexMap.m8BoundaryIndexOfNat k) :=
  rfl

theorem turnVertexOfTriangleRun_of_mem_turnIndexSet
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    turnVertexOfTriangleRun (S := S) triangleRun C hmin a k =
      (triangleRun C hmin).pIndex
        (Subtype.mk k (by
          have hkIcc : Membership.mem (Finset.Icc 1 13) k := by
            simpa [Lemma10Inequalities.turnIndexSet] using hk
          have hk_le : k <= 13 := (Finset.mem_Icc.mp hkIcc).2
          omega) : M8LabelsFromBoundaryInterface.M8BoundaryIndex) := by
  have hkIcc : Membership.mem (Finset.Icc 1 13) k := by
    simpa [Lemma10Inequalities.turnIndexSet] using hk
  have hk_le : k <= 13 := (Finset.mem_Icc.mp hkIcc).2
  unfold turnVertexOfTriangleRun
  rw [Lemma6NegativeAfterGapW12.BoundaryArcIndexMap.m8BoundaryIndexOfNat_of_le hk_le]

/-- A concrete triangle run names all thirteen turn slots by the established
M8 boundary-index convention. -/
def ofTriangleRun
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary) :
    MinimalBoundaryTopologyBoundaryTurnVertexRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount :=
    degreeThree_le_negativeCount_add_longArcCount
  outerCycle_length_ge_three := outerCycle_length_ge_three
  turnVertex :=
    turnVertexOfTriangleRun (S := S) triangleRun

@[simp]
theorem ofTriangleRun_turnVertex_eq
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).turnVertex C hmin a k) =
        turnVertexOfTriangleRun (S := S) triangleRun C hmin a k :=
  rfl

theorem ofTriangleRun_turnVertex_of_mem_turnIndexSet
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).turnVertex C hmin a k) =
        (triangleRun C hmin).pIndex
          (Subtype.mk k (by
            have hkIcc : Membership.mem (Finset.Icc 1 13) k := by
              simpa [Lemma10Inequalities.turnIndexSet] using hk
            have hk_le : k <= 13 := (Finset.mem_Icc.mp hkIcc).2
            omega) : M8LabelsFromBoundaryInterface.M8BoundaryIndex) := by
  rw [ofTriangleRun_turnVertex_eq]
  exact turnVertexOfTriangleRun_of_mem_turnIndexSet
    (S := S) triangleRun C hmin a k hk

end MinimalBoundaryTopologyBoundaryTurnVertexRows

/-- Constructor version of
`MinimalBoundaryTopologyBoundaryTurnVertexRows.toBoundaryTurnAngleRows`. -/
def ofTurnVertexRows
    (V : MinimalBoundaryTopologyBoundaryTurnVertexRows.{u} S) :
    MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S :=
  V.toBoundaryTurnAngleRows

/-- Strongest current constructor from the existing triangle-run source: each
raw-turn slot uses the selected M8 boundary position `p_k`. -/
def ofTriangleRun
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary) :
    MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S :=
  (MinimalBoundaryTopologyBoundaryTurnVertexRows.ofTriangleRun
    (S := S)
    degreeThree_le_negativeCount_add_longArcCount
    outerCycle_length_ge_three
    triangleRun).toBoundaryTurnAngleRows

@[simp]
theorem ofTurnVertexRows_turnVertex_eq
    (V : MinimalBoundaryTopologyBoundaryTurnVertexRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) :
    ((ofTurnVertexRows (S := S) V).turnVertex C hmin a k) =
      V.turnVertex C hmin a k :=
  rfl

@[simp]
theorem ofTriangleRun_turnVertex_eq
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).turnVertex C hmin a k) =
        MinimalBoundaryTopologyBoundaryTurnVertexRows.turnVertexOfTriangleRun
          (S := S) triangleRun C hmin a k :=
  rfl

theorem ofTriangleRun_turnVertex_of_mem_turnIndexSet
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).turnVertex C hmin a k) =
        (triangleRun C hmin).pIndex
          (Subtype.mk k (by
            have hkIcc : Membership.mem (Finset.Icc 1 13) k := by
              simpa [Lemma10Inequalities.turnIndexSet] using hk
            have hk_le : k <= 13 := (Finset.mem_Icc.mp hkIcc).2
            omega) : M8LabelsFromBoundaryInterface.M8BoundaryIndex) := by
  rw [ofTriangleRun_turnVertex_eq]
  exact
    MinimalBoundaryTopologyBoundaryTurnVertexRows.turnVertexOfTriangleRun_of_mem_turnIndexSet
      (S := S) triangleRun C hmin a k hk

/-- Raw turn obtained by evaluating the actual local turn-angle certificate on
the thirteen M8 turn slots and by using `0` outside those slots. -/
noncomputable def rawTurn
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) : Real :=
  if hk : Membership.mem Lemma10Inequalities.turnIndexSet k then
    (R.turnAngle C hmin a k hk).value
  else
    0

@[simp]
theorem rawTurn_of_mem
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    R.rawTurn C hmin a k = (R.turnAngle C hmin a k hk).value := by
  unfold rawTurn
  rw [dif_pos hk]

@[simp]
theorem rawTurn_of_not_mem
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Not (Membership.mem Lemma10Inequalities.turnIndexSet k)) :
    R.rawTurn C hmin a k = 0 := by
  unfold rawTurn
  rw [dif_neg hk]

/-- Actual local angle certificates give the pointwise nonnegative raw turns
required by the long-arc row constructor. -/
theorem rawTurn_nonnegative_on_arc
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    0 <= R.rawTurn C hmin a k := by
  rw [R.rawTurn_of_mem C hmin a k hk]
  exact
    BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value_nonnegative
      (R.turnAngle C hmin a k hk)

/-- Forget the actual W11 turn-angle geometry to W13's classified raw-turn
rows.  The raw values are exactly the concrete angle values supplied by
`R.rawTurn`, with nonnegativity inherited from the angle certificate. -/
noncomputable def toBoundaryLongArcRawTurnRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows
      (S.row C hmin).classification :=
  Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows.ofRawTurns
    (D0 := (S.row C hmin).classification)
    (R.rawTurn C hmin)
    (by
      intro a k hk
      exact R.rawTurn_nonnegative_on_arc C hmin a k hk)

@[simp]
theorem toBoundaryLongArcRawTurnRows_rawTurn
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (R.toBoundaryLongArcRawTurnRows C hmin).rawTurn = R.rawTurn C hmin :=
  rfl

theorem toBoundaryLongArcRawTurnRows_rawTurn_nonnegative_on_arc
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    0 <= (R.toBoundaryLongArcRawTurnRows C hmin).rawTurn a k :=
  (R.toBoundaryLongArcRawTurnRows C hmin).rawTurn_nonnegative_on_arc a k hk

/-- Forget the actual predecessor/current/successor angle geometry to the
existing W24 raw-turn rows consumed by the long-arc field constructor. -/
noncomputable def toLongArcRawTurnRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcRawTurnRows.{u}
      S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcRawTurnRowsOfBoundaryLongArcRawTurnRows
    S
    R.degreeThree_le_negativeCount_add_longArcCount
    (fun C hmin => R.toBoundaryLongArcRawTurnRows C hmin)

@[simp]
theorem toLongArcRawTurnRows_rawTurn
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices) :
    R.toLongArcRawTurnRows.rawTurn C hmin a = R.rawTurn C hmin a :=
  rfl

theorem toLongArcRawTurnRows_rawTurn_nonnegative_on_arc
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    0 <= R.toLongArcRawTurnRows.rawTurn C hmin a k :=
  R.toLongArcRawTurnRows.rawTurn_nonnegative_on_arc C hmin a k hk

/-- The triangle-run W11 constructor immediately gives W13 classified
raw-turn rows for every selected skeleton row. -/
noncomputable def boundaryLongArcRawTurnRowsOfTriangleRun
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows
          (S.row C hmin).classification :=
  fun C hmin =>
    (ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).toBoundaryLongArcRawTurnRows C hmin

@[simp]
theorem boundaryLongArcRawTurnRowsOfTriangleRun_rawTurn
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ((boundaryLongArcRawTurnRowsOfTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun) C hmin).rawTurn =
        (ofTriangleRun
          (S := S)
          degreeThree_le_negativeCount_add_longArcCount
          outerCycle_length_ge_three
          triangleRun).rawTurn C hmin :=
  rfl

/-- The actual boundary-turn angle rows directly provide the long-arc field
family needed by the non-circular W24/W33 missing-field route. -/
noncomputable def toLongArcFieldFamily
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcFieldFamily
      S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcFieldFamilyOfLongArcRawTurnRows
    S R.toLongArcRawTurnRows

theorem nonempty_longArcFieldFamily
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S) :
    Nonempty
      (JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcFieldFamily
        S) :=
  Nonempty.intro R.toLongArcFieldFamily

/-! ### Boundary-label S5 rows sourced against actual boundary turns -/

/--
Actual Figure 8 interval-subwindow rows measured against the W11 raw turn
selected by a concrete long arc.

The row has the same quantifiers as the finite-label S5 Figure 8 source, but
the turn function is the actual raw-turn function extracted from the boundary
turn-angle package.
-/
abbrev Figure8CentralAngleActualTurnIccSubwindowRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i j : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data j) ->
    AngleBridgeFacts.Figure8DistanceData p qi qj s r ->
      Exists fun lo : Nat =>
      Exists fun hi : Nat =>
        i + 1 <= lo /\
          hi <= j /\
            AngleGeometry.angleAt qi p qj <=
              (Finset.Icc lo hi).sum (R.rawTurn C hmin a)

/--
Actual Figure 8 indexed finite-subwindow rows measured against the W11 raw
turn selected by a concrete long arc.
-/
abbrev Figure8CentralAngleActualTurnIndexedSubwindowRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i j : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data j) ->
    AngleBridgeFacts.Figure8DistanceData p qi qj s r ->
      Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.CentralAngleTurnIndexedSubwindow
        (R.rawTurn C hmin a) i j p qi qj

/--
Actual Figure 9 pointwise cosine comparisons measured against the W11 raw
turn selected by a concrete long arc.
-/
abbrev Figure9AdjacentLeftActualTurnCosineComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    1 <= i -> i + 1 <= 10 ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data (i + 1)) ->
    AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
      Real.cos (R.rawTurn C hmin a (i + 1)) <=
        TriangleAngleFacts.dotAt p qi s

/--
Actual Figure 9 pointwise chord comparisons measured against the W11 raw turn
selected by a concrete long arc.
-/
abbrev Figure9AdjacentLeftActualTurnChordComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    1 <= i -> i + 1 <= 10 ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data (i + 1)) ->
    AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
      TriangleAngleFacts.sqDist p s <=
        2 - 2 * Real.cos (R.rawTurn C hmin a (i + 1))

/-- Figure 8 separated windows only use turn slots inside the W11
`turnIndexSet`. -/
theorem figure8_turnIndexSet_mem_of_mem_window
    {i j k : Nat}
    (hi : 1 <= i) (hj : j <= 10)
    (hk : k ∈ Finset.Icc (i + 1) j) :
    Membership.mem Lemma10Inequalities.turnIndexSet k := by
  have hk_bounds : i + 1 <= k ∧ k <= j := Finset.mem_Icc.mp hk
  have hk_lower : 1 <= k := by omega
  have hk_upper : k <= 13 := by omega
  have hkIcc : Membership.mem (Finset.Icc 1 13) k :=
    Finset.mem_Icc.mpr ⟨hk_lower, hk_upper⟩
  simpa [Lemma10Inequalities.turnIndexSet] using hkIcc

/-- Turn-index membership gives the corresponding `p_k` boundary index for
the selected `m = 8` triangle run. -/
def m8BoundaryIndexOfTurnIndex
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    M8LabelsFromBoundaryInterface.M8BoundaryIndex :=
  Subtype.mk k (by
    have hkIcc : Membership.mem (Finset.Icc 1 13) k := by
      simpa [Lemma10Inequalities.turnIndexSet] using hk
    exact (Finset.mem_Icc.mp hkIcc).2)

@[simp]
theorem m8BoundaryIndexOfTurnIndex_val
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    (m8BoundaryIndexOfTurnIndex k hk).1 = k :=
  rfl

/-- Figure 9 adjacent comparisons use the middle turn slot inside the W11
`turnIndexSet`. -/
theorem figure9_turnIndexSet_mem_of_adjacent
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    Membership.mem Lemma10Inequalities.turnIndexSet (i + 1) := by
  have hk_lower : 1 <= i + 1 := by omega
  have hk_upper : i + 1 <= 13 := by omega
  have hkIcc : Membership.mem (Finset.Icc 1 13) (i + 1) :=
    Finset.mem_Icc.mpr ⟨hk_lower, hk_upper⟩
  simpa [Lemma10Inequalities.turnIndexSet] using hkIcc

theorem ofTriangleRun_turnVertex_of_turnIndex
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).turnVertex C hmin a k) =
        (triangleRun C hmin).pIndex
          (m8BoundaryIndexOfTurnIndex k hk) := by
  rw [ofTriangleRun_turnVertex_of_mem_turnIndexSet
    (S := S)
    degreeThree_le_negativeCount_add_longArcCount
    outerCycle_length_ge_three
    triangleRun
    C hmin a k hk]
  exact
    congrArg (triangleRun C hmin).pIndex
      (Subtype.ext rfl)

theorem ofTriangleRun_turnAngle_of_turnIndex
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).turnAngle C hmin a k hk) =
        BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
          (S.row C hmin).topology.toCore
          (outerCycle_length_ge_three C hmin)
          ((triangleRun C hmin).pIndex
            (m8BoundaryIndexOfTurnIndex k hk)) := by
  change
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
      (S.row C hmin).topology.toCore
      (outerCycle_length_ge_three C hmin)
      (((ofTriangleRun
        (S := S)
        degreeThree_le_negativeCount_add_longArcCount
        outerCycle_length_ge_three
        triangleRun).turnVertex C hmin a k)) =
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
        (S.row C hmin).topology.toCore
        (outerCycle_length_ge_three C hmin)
        ((triangleRun C hmin).pIndex
          (m8BoundaryIndexOfTurnIndex k hk))
  rw [ofTriangleRun_turnVertex_of_turnIndex]

/-- On a selected turn slot, the triangle-run constructor's raw turn is the
actual value of the predecessor/current/successor angle at the triangle-run
boundary index `p_k`. -/
theorem ofTriangleRun_rawTurn_of_turnIndex
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    ((ofTriangleRun
      (S := S)
      degreeThree_le_negativeCount_add_longArcCount
      outerCycle_length_ge_three
      triangleRun).rawTurn C hmin a k) =
        (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
          (S.row C hmin).topology.toCore
          (outerCycle_length_ge_three C hmin)
          ((triangleRun C hmin).pIndex
            (m8BoundaryIndexOfTurnIndex k hk))).value := by
  rw [(ofTriangleRun
    (S := S)
    degreeThree_le_negativeCount_add_longArcCount
    outerCycle_length_ge_three
    triangleRun).rawTurn_of_mem C hmin a k hk]
  exact
    congrArg BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value
      (ofTriangleRun_turnAngle_of_turnIndex
        (S := S)
        degreeThree_le_negativeCount_add_longArcCount
        outerCycle_length_ge_three
        triangleRun
        C hmin a k hk)

/-- On any finite set contained in the W11 turn index set, the raw turn sum is
the sum of the underlying concrete turn-angle values. -/
theorem rawTurn_sum_eq_turnAngle_attach_sum
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (s : Finset Nat)
    (hmem :
      forall {k : Nat}, k ∈ s ->
        Membership.mem Lemma10Inequalities.turnIndexSet k) :
    s.sum (R.rawTurn C hmin a) =
      s.attach.sum (fun k =>
        (R.turnAngle C hmin a k.1 (hmem (k := k.1) k.2)).value) := by
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  exact R.rawTurn_of_mem C hmin a k.1 (hmem (k := k.1) k.2)

/-- Figure 8 interval-subwindow rows phrased directly over the concrete W11
turn-angle certificates. -/
abbrev Figure8CentralAngleTurnAngleIccSubwindowRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i j : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    (hi : 1 <= i) -> i + 1 < j -> (hj : j <= 10) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data j) ->
    AngleBridgeFacts.Figure8DistanceData p qi qj s r ->
      Exists fun lo : Nat =>
      Exists fun upper : Nat =>
      Exists fun hlo : i + 1 <= lo =>
      Exists fun hupper : upper <= j =>
        AngleGeometry.angleAt qi p qj <=
          (Finset.Icc lo upper).attach.sum (fun k =>
            (R.turnAngle C hmin a k.1
              (figure8_turnIndexSet_mem_of_mem_window hi hj
                ((Finset.Icc_subset_Icc hlo hupper) k.2))).value)

/-- Figure 8 indexed finite-subwindow rows phrased directly over the concrete
W11 turn-angle certificates. -/
abbrev Figure8CentralAngleTurnAngleIndexedSubwindowRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i j : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    (hi : 1 <= i) -> i + 1 < j -> (hj : j <= 10) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data j) ->
    AngleBridgeFacts.Figure8DistanceData p qi qj s r ->
      Exists fun m : Nat =>
      Exists fun index : Fin m -> Nat =>
      Exists fun _hinj : Function.Injective index =>
      Exists fun hmem : forall t : Fin m, index t ∈ Finset.Icc (i + 1) j =>
        AngleGeometry.angleAt qi p qj <=
          Finset.univ.sum (fun t : Fin m =>
            (R.turnAngle C hmin a (index t)
              (figure8_turnIndexSet_mem_of_mem_window hi hj
                (hmem t))).value)

/-- Figure 8 interval-subwindow rows phrased against the explicit selected
triangle-run boundary positions `p_k`. -/
abbrev Figure8CentralAngleTriangleRunIccSubwindowRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i j : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    (hi : 1 <= i) -> i + 1 < j -> (hj : j <= 10) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data j) ->
    AngleBridgeFacts.Figure8DistanceData p qi qj s r ->
      Exists fun lo : Nat =>
      Exists fun upper : Nat =>
      Exists fun hlo : i + 1 <= lo =>
      Exists fun hupper : upper <= j =>
        AngleGeometry.angleAt qi p qj <=
          (Finset.Icc lo upper).attach.sum (fun k =>
            (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
              (S.row C hmin).topology.toCore
              (outerCycle_length_ge_three C hmin)
              ((triangleRun C hmin).pIndex
                (m8BoundaryIndexOfTurnIndex k.1
                  (figure8_turnIndexSet_mem_of_mem_window hi hj
                    ((Finset.Icc_subset_Icc hlo hupper) k.2))))).value)

/-- Explicit triangle-run Figure 8 interval rows inhabit the W11 turn-angle
Figure 8 row for the turn-angle package built from that triangle run. -/
theorem figure8CentralAngleTurnAngleIccSubwindowRows_of_triangleRunIccSubwindowRows
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (H :
      Figure8CentralAngleTriangleRunIccSubwindowRows
        (S := S) outerCycle_length_ge_three triangleRun C hmin K) :
    Figure8CentralAngleTurnAngleIccSubwindowRows
      (ofTriangleRun
        (S := S)
        degreeThree_le_negativeCount_add_longArcCount
        outerCycle_length_ge_three
        triangleRun)
      C hmin a K := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
  rcases H hi hsep hj hbad_i hbad_j Hdist with
    ⟨lo, upper, hlo, hupper, hangle⟩
  refine ⟨lo, upper, hlo, hupper, ?_⟩
  have hsum :
      (Finset.Icc lo upper).attach.sum (fun k =>
        (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
          (S.row C hmin).topology.toCore
          (outerCycle_length_ge_three C hmin)
          ((triangleRun C hmin).pIndex
            (m8BoundaryIndexOfTurnIndex k.1
              (figure8_turnIndexSet_mem_of_mem_window hi hj
                ((Finset.Icc_subset_Icc hlo hupper) k.2))))).value) =
        (Finset.Icc lo upper).attach.sum (fun k =>
          ((ofTriangleRun
            (S := S)
            degreeThree_le_negativeCount_add_longArcCount
            outerCycle_length_ge_three
            triangleRun).turnAngle C hmin a k.1
              (figure8_turnIndexSet_mem_of_mem_window hi hj
                ((Finset.Icc_subset_Icc hlo hupper) k.2))).value) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact
      (congrArg BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value
        (ofTriangleRun_turnAngle_of_turnIndex
          (S := S)
          degreeThree_le_negativeCount_add_longArcCount
          outerCycle_length_ge_three
          triangleRun
          C hmin a k.1
          (figure8_turnIndexSet_mem_of_mem_window hi hj
            ((Finset.Icc_subset_Icc hlo hupper) k.2)))).symm
  rw [hsum] at hangle
  exact hangle

/-- Figure 9 cosine-comparison rows phrased directly over the concrete W11
turn-angle certificates. -/
abbrev Figure9AdjacentLeftTurnAngleCosineComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    (hi : 1 <= i) -> (hi_next : i + 1 <= 10) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data (i + 1)) ->
    AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
      Real.cos
          ((R.turnAngle C hmin a (i + 1)
            (figure9_turnIndexSet_mem_of_adjacent hi hi_next)).value) <=
        TriangleAngleFacts.dotAt p qi s

/-- Figure 9 turn-chord comparison rows phrased directly over the concrete W11
turn-angle certificates. -/
abbrev Figure9AdjacentLeftTurnAngleChordComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin) :
    Prop :=
  forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    (hi : 1 <= i) -> (hi_next : i + 1 <= 10) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data i) ->
    Not
      (Lemma10Bridge.M8BrokenLatticeGood
        K.toM8LocalLabels.predicates.data (i + 1)) ->
    AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
      TriangleAngleFacts.sqDist p s <=
        2 -
          2 *
            Real.cos
              ((R.turnAngle C hmin a (i + 1)
                (figure9_turnIndexSet_mem_of_adjacent hi hi_next)).value)

/-- Turn-angle interval-subwindow rows reduce to the actual W11 raw-turn
Figure 8 interval carrier. -/
theorem figure8CentralAngleActualTurnIccSubwindowRows_of_turnAngleRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (H : Figure8CentralAngleTurnAngleIccSubwindowRows R C hmin a K) :
    Figure8CentralAngleActualTurnIccSubwindowRows R C hmin a K := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
  rcases H hi hsep hj hbad_i hbad_j Hdist with
    ⟨lo, upper, hlo, hupper, hangle⟩
  refine ⟨lo, upper, hlo, hupper, ?_⟩
  let hmem :
      forall {k : Nat}, k ∈ Finset.Icc lo upper ->
        Membership.mem Lemma10Inequalities.turnIndexSet k :=
    fun {k} hk =>
      figure8_turnIndexSet_mem_of_mem_window hi hj
        ((Finset.Icc_subset_Icc hlo hupper) hk)
  have hsum :
      (Finset.Icc lo upper).sum (R.rawTurn C hmin a) =
        (Finset.Icc lo upper).attach.sum (fun k =>
          (R.turnAngle C hmin a k.1 (hmem (k := k.1) k.2)).value) :=
    rawTurn_sum_eq_turnAngle_attach_sum R C hmin a
      (Finset.Icc lo upper) hmem
  rw [hsum]
  exact hangle

/-- Turn-angle indexed finite-subwindow rows reduce to the actual W11 raw-turn
Figure 8 indexed carrier. -/
theorem figure8CentralAngleActualTurnIndexedSubwindowRows_of_turnAngleRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (H : Figure8CentralAngleTurnAngleIndexedSubwindowRows R C hmin a K) :
    Figure8CentralAngleActualTurnIndexedSubwindowRows R C hmin a K := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
  rcases H hi hsep hj hbad_i hbad_j Hdist with
    ⟨m, index, hinj, hmem, hangle⟩
  refine ⟨m, index, hinj, hmem, ?_⟩
  have hsum :
      Finset.univ.sum (fun t : Fin m =>
          R.rawTurn C hmin a (index t)) =
        Finset.univ.sum (fun t : Fin m =>
          (R.turnAngle C hmin a (index t)
            (figure8_turnIndexSet_mem_of_mem_window hi hj
              (hmem t))).value) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    exact
      R.rawTurn_of_mem C hmin a (index t)
        (figure8_turnIndexSet_mem_of_mem_window hi hj (hmem t))
  rw [hsum]
  exact hangle

/-- Turn-angle cosine comparisons reduce to the actual W11 raw-turn Figure 9
cosine-comparison carrier. -/
theorem figure9AdjacentLeftActualTurnCosineComparisonRows_of_turnAngleRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (H : Figure9AdjacentLeftTurnAngleCosineComparisonRows R C hmin a K) :
    Figure9AdjacentLeftActualTurnCosineComparisonRows R C hmin a K := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
  have hk := figure9_turnIndexSet_mem_of_adjacent hi hi_next
  rw [R.rawTurn_of_mem C hmin a (i + 1) hk]
  exact H hi hi_next hbad_i hbad_next Hdist

/-- Turn-angle chord comparisons reduce to the actual W11 raw-turn Figure 9
turn-chord comparison carrier. -/
theorem figure9AdjacentLeftActualTurnChordComparisonRows_of_turnAngleRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (H : Figure9AdjacentLeftTurnAngleChordComparisonRows R C hmin a K) :
    Figure9AdjacentLeftActualTurnChordComparisonRows R C hmin a K := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
  have hk := figure9_turnIndexSet_mem_of_adjacent hi hi_next
  rw [R.rawTurn_of_mem C hmin a (i + 1) hk]
  exact H hi hi_next hbad_i hbad_next Hdist

/-- Transfer actual Figure 8 interval-subwindow rows to the finite-label S5
row shape once the S5 turn function is identified with the W11 raw turn. -/
theorem figure8CentralAngleTurnIccSubwindowRows_of_actualTurnRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H : Figure8CentralAngleActualTurnIccSubwindowRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.Figure8CentralAngleTurnIccSubwindowRows
      K turnBounds := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
  rcases H hi hsep hj hbad_i hbad_j Hdist with
    ⟨lo, hi', hlo, hhi, hangle⟩
  refine ⟨lo, hi', hlo, hhi, ?_⟩
  simpa [hturn] using hangle

/-- Transfer actual Figure 8 indexed finite-subwindow rows to the finite-label
S5 row shape once the S5 turn function is identified with the W11 raw turn. -/
theorem figure8CentralAngleTurnIndexedSubwindowRows_of_actualTurnRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H : Figure8CentralAngleActualTurnIndexedSubwindowRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.Figure8CentralAngleTurnIndexedSubwindowRows
      K turnBounds := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
  simpa [hturn] using H hi hsep hj hbad_i hbad_j Hdist

/-- Transfer actual Figure 9 cosine comparisons to the finite-label S5 row
shape once the S5 turn function is identified with the W11 raw turn. -/
theorem figure9AdjacentLeftCosineComparisonRows_of_actualTurnRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H : Figure9AdjacentLeftActualTurnCosineComparisonRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.Figure9AdjacentLeftCosineComparisonRows
      K turnBounds := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
  simpa [hturn] using H hi hi_next hbad_i hbad_next Hdist

/-- Transfer actual Figure 9 turn-chord comparisons to the finite-label S5
row shape once the S5 turn function is identified with the W11 raw turn. -/
theorem figure9AdjacentLeftTurnChordComparisonRows_of_actualTurnRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H : Figure9AdjacentLeftActualTurnChordComparisonRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.Figure9AdjacentLeftTurnChordComparisonRows
      K turnBounds := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
  simpa [hturn] using H hi hi_next hbad_i hbad_next Hdist

/-- Actual Figure 8 interval rows plus actual Figure 9 cosine comparisons feed
the existing finite-label S5 reducer. -/
def s5AngleRows_of_actualTurnIccRowsAndCosineComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 : Figure8CentralAngleActualTurnIccSubwindowRows R C hmin a K)
    (H9 : Figure9AdjacentLeftActualTurnCosineComparisonRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
      K turnBounds :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows.ofTurnIccSubwindowRowsAndCosineComparisonRows
    (figure8CentralAngleTurnIccSubwindowRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H8)
    (figure9AdjacentLeftCosineComparisonRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H9)

/-- Actual Figure 8 interval rows plus actual Figure 9 turn-chord comparisons
feed the existing finite-label S5 reducer. -/
def s5AngleRows_of_actualTurnIccRowsAndTurnChordComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 : Figure8CentralAngleActualTurnIccSubwindowRows R C hmin a K)
    (H9 : Figure9AdjacentLeftActualTurnChordComparisonRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
      K turnBounds :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows.ofTurnIccSubwindowRowsAndTurnChordComparisonRows
    (figure8CentralAngleTurnIccSubwindowRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H8)
    (figure9AdjacentLeftTurnChordComparisonRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H9)

/-- Actual Figure 8 indexed rows plus actual Figure 9 cosine comparisons feed
the existing finite-label S5 reducer. -/
def s5AngleRows_of_actualTurnIndexedRowsAndCosineComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 : Figure8CentralAngleActualTurnIndexedSubwindowRows R C hmin a K)
    (H9 : Figure9AdjacentLeftActualTurnCosineComparisonRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
      K turnBounds :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows.ofTurnIndexedSubwindowRowsAndCosineComparisonRows
    (figure8CentralAngleTurnIndexedSubwindowRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H8)
    (figure9AdjacentLeftCosineComparisonRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H9)

/-- Actual Figure 8 indexed rows plus actual Figure 9 turn-chord comparisons
feed the existing finite-label S5 reducer. -/
def s5AngleRows_of_actualTurnIndexedRowsAndTurnChordComparisonRows
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8ConstructionInterface.M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 : Figure8CentralAngleActualTurnIndexedSubwindowRows R C hmin a K)
    (H9 : Figure9AdjacentLeftActualTurnChordComparisonRows R C hmin a K) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
      K turnBounds :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows.ofTurnIndexedSubwindowRowsAndTurnChordComparisonRows
    (figure8CentralAngleTurnIndexedSubwindowRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H8)
    (figure9AdjacentLeftTurnChordComparisonRows_of_actualTurnRows
      R C hmin a K turnBounds hturn H9)

/-- W13 bundled gap-negative rows specialized to a W24 skeleton family. -/
abbrev BoundaryLongArcGapNegativeRowsFamily
    (S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}) :
    Type (u + 1) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
        (S.row C hmin).classification
        (S.row C hmin).geometricAngleSum
        (S.row C hmin).forced_le_geometric
        (S.row C hmin).geometric_le_polygon
        (S.row C hmin).Subpolygon
        (S.row C hmin).subpolygonData

/-- W13 bundled rows supply the count side required by the W11 triangle-run
turn-row constructor. -/
theorem degreeThree_le_negativeCount_add_longArcCount_of_boundaryLongArcGapNegativeRows
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.counts.d3 <=
          (S.row C hmin).classification.counts.negativeCount +
            @Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance := by
  intro n C hmin
  exact
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryLongArcGapNegativePackage
      S C hmin
      ((JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.boundaryLongArcGapNegativePackageFamilyOfRows
        S rows) C hmin)
      ((JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.boundaryLongArcGapNegativeRowsLongArcEquiv
        S rows) C hmin)

/-- The current explicit triangle-run theorem supplies the concrete
triangle-run family over a skeleton once W13 rows provide the matching long-arc
field used by the theorem surface. -/
noncomputable def triangleRunOfExplicitM8TriangleRunIndicesTheoremAndBoundaryLongArcGapNegativeRows
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    (H : TriangleRunSelectorW17.ExplicitM8TriangleRunIndicesTheorem.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
          (S.row C hmin).planarBoundary :=
  fun C hmin =>
    Classical.choice
      ((TriangleRunSelectorW17.triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem
        H)
        C
        (S.row C hmin).topology
        (S.row C hmin).outerAngleBounds
        (S.row C hmin).Subpolygon
        (S.row C hmin).subpolygonData
        ((JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcFieldFamilyOfBoundaryLongArcGapNegativeRows
          S rows) C hmin))

/-- Shortest W11 row constructor from the current S4 source rows: W13 supplies
the count gap and the triangle run supplies the thirteen boundary turn slots. -/
noncomputable def ofTriangleRunAndBoundaryLongArcGapNegativeRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S) :
    MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S :=
  MinimalBoundaryTopologyBoundaryTurnAngleRows.ofTriangleRun
    (S := S)
    (degreeThree_le_negativeCount_add_longArcCount_of_boundaryLongArcGapNegativeRows
      (S := S) rows)
    outerCycle_length_ge_three
    triangleRun

/-- Explicit triangle-run rows plus W13 gap-negative rows build the W11
turn-angle/raw-turn package for the selected long-arc carrier. -/
noncomputable def ofExplicitM8TriangleRunIndicesTheoremAndBoundaryLongArcGapNegativeRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    (H : TriangleRunSelectorW17.ExplicitM8TriangleRunIndicesTheorem.{u}) :
    MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S :=
  ofTriangleRunAndBoundaryLongArcGapNegativeRows
    (S := S)
    outerCycle_length_ge_three
    (triangleRunOfExplicitM8TriangleRunIndicesTheoremAndBoundaryLongArcGapNegativeRows
      (S := S) rows H)
    rows

@[simp]
theorem ofTriangleRunAndBoundaryLongArcGapNegativeRows_turnVertex_eq
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat) :
    ((ofTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S)
      outerCycle_length_ge_three
      triangleRun
      rows).turnVertex C hmin a k) =
        MinimalBoundaryTopologyBoundaryTurnVertexRows.turnVertexOfTriangleRun
          (S := S) triangleRun C hmin a k := by
  exact
    ofTriangleRun_turnVertex_eq
      (S := S)
      (degreeThree_le_negativeCount_add_longArcCount :=
        degreeThree_le_negativeCount_add_longArcCount_of_boundaryLongArcGapNegativeRows
          (S := S) rows)
      (outerCycle_length_ge_three := outerCycle_length_ge_three)
      (triangleRun := triangleRun)
      C hmin a k

theorem ofTriangleRunAndBoundaryLongArcGapNegativeRows_turnVertex_of_mem_turnIndexSet
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    ((ofTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S)
      outerCycle_length_ge_three
      triangleRun
      rows).turnVertex C hmin a k) =
        (triangleRun C hmin).pIndex
          (Subtype.mk k (by
            have hkIcc : Membership.mem (Finset.Icc 1 13) k := by
              simpa [Lemma10Inequalities.turnIndexSet] using hk
            have hk_le : k <= 13 := (Finset.mem_Icc.mp hkIcc).2
            omega) : M8LabelsFromBoundaryInterface.M8BoundaryIndex) := by
  exact
    ofTriangleRun_turnVertex_of_mem_turnIndexSet
      (S := S)
      (degreeThree_le_negativeCount_add_longArcCount :=
        degreeThree_le_negativeCount_add_longArcCount_of_boundaryLongArcGapNegativeRows
          (S := S) rows)
      (outerCycle_length_ge_three := outerCycle_length_ge_three)
      (triangleRun := triangleRun)
      C hmin a k hk

/-- The selected triangle-run/W13 turn-angle package inherits explicit
triangle-run Figure 8 interval rows as W11 turn-angle Figure 8 rows. -/
theorem figure8CentralAngleTurnAngleIccSubwindowRows_of_triangleRunAndBoundaryLongArcGapNegativeRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (H :
      Figure8CentralAngleTriangleRunIccSubwindowRows
        (S := S) outerCycle_length_ge_three triangleRun C hmin K) :
    Figure8CentralAngleTurnAngleIccSubwindowRows
      (ofTriangleRunAndBoundaryLongArcGapNegativeRows
        (S := S)
        outerCycle_length_ge_three
        triangleRun
        rows)
      C hmin a K :=
  figure8CentralAngleTurnAngleIccSubwindowRows_of_triangleRunIccSubwindowRows
    (S := S)
    (degreeThree_le_negativeCount_add_longArcCount_of_boundaryLongArcGapNegativeRows
      (S := S) rows)
    outerCycle_length_ge_three
    triangleRun
    C hmin a K H

/-- W11 triangle-run turn rows, W13 bundled rows, and W24's row bridge produce
the live skeleton long-arc family in one step. -/
noncomputable def longArcFieldFamilyOfTriangleRunAndBoundaryLongArcGapNegativeRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.LongArcFieldFamily
      S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativeRows
    S
    ((ofTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S) outerCycle_length_ge_three triangleRun rows).toLongArcRawTurnRows)
    rows

/-- W11 triangle-run turn rows and W13 bundled gap-negative rows fill the
exact W24 missing field without detouring through the finite-`p/q` theorem. -/
noncomputable def missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.MissingLongArcTriangleRunField
      S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfLongArcTriangleRun
    S
    (longArcFieldFamilyOfTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S) outerCycle_length_ge_three triangleRun rows)
    triangleRun

@[simp]
theorem missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows_longArc
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ((missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S) outerCycle_length_ge_three triangleRun rows) C hmin).longArc =
        (longArcFieldFamilyOfTriangleRunAndBoundaryLongArcGapNegativeRows
          (S := S) outerCycle_length_ge_three triangleRun rows) C hmin :=
  rfl

@[simp]
theorem missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows_triangleRun
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ((missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S) outerCycle_length_ge_three triangleRun rows) C hmin).triangleRun =
        triangleRun C hmin :=
  rfl

theorem missingField_nonempty_of_triangleRun_boundaryLongArcGapNegativeRows
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S) :
    Nonempty
      (JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.MissingLongArcTriangleRunField
        S) :=
  Nonempty.intro
    (missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S) outerCycle_length_ge_three triangleRun rows)

/-- The same composition, continuing through the W16 finite-`p/q` theorem to
the exact missing long-arc/triangle-run field. -/
noncomputable def missingFieldOfTriangleRunBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    (H :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.MissingLongArcTriangleRunField
      S :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.missingFieldOfTurnRowsBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    S
    ((ofTriangleRunAndBoundaryLongArcGapNegativeRows
      (S := S) outerCycle_length_ge_three triangleRun rows).toLongArcRawTurnRows)
    rows
    H

theorem missingField_nonempty_of_triangleRun_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    (outerCycle_length_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (S.row C hmin).topology.toCore.outerCycle.length)
    (triangleRun :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.{u}
            (S.row C hmin).planarBoundary)
    (rows : BoundaryLongArcGapNegativeRowsFamily.{u} S)
    (H :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty
      (JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.MissingLongArcTriangleRunField
        S) :=
  Nonempty.intro
    (missingFieldOfTriangleRunBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
      (S := S) outerCycle_length_ge_three triangleRun rows H)

end MinimalBoundaryTopologyBoundaryTurnAngleRows

/-- W9 topology/angle/subpolygon row. -/
def toW9TopologyAngleSubpolygonRow :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C where
  topology := Q.topology
  outerAngleBounds := Q.outerAngleBounds
  Subpolygon := Q.Subpolygon
  subpolygonData := Q.subpolygonData
  longArc := Q.w9LongArc

@[simp]
theorem toW9TopologyAngleSubpolygonRow_planarBoundary :
    Q.toW9TopologyAngleSubpolygonRow.planarBoundary =
      Q.topology.toPlanarBoundaryData Q.outerAngleBounds
        Q.Subpolygon Q.subpolygonData :=
  rfl

/-- The W9 row's normalized long-arc turn data. -/
def w9Arc :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  Q.toW9TopologyAngleSubpolygonRow.arc

/-- The W9 row's construction-level M8 turn bounds. -/
def w9TurnBounds :
    M8ConstructionInterface.M8TurnBounds :=
  Q.toW9TopologyAngleSubpolygonRow.turnBounds

/-- Older remaining-matrix topology/count/long-arc row. -/
def toRemainingTopologyBoundaryLongArc :
    SwanepoelRemainingMatrix.TopologyBoundaryLongArc.{u} C where
  topology := Q.topology
  arcBoundaryBudget := Q.toW9TopologyAngleSubpolygonRow.arcBoundaryBudget
  topologyCore_eq := rfl

/-- W8 boundary/long-arc source row, once the label-spine fields are supplied. -/
def toW8BoundaryLongArcData
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C)
    (spineCertificate :
      BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
        Q.toW9TopologyAngleSubpolygonRow.planarBoundary)
    (lemma8Existence :
      Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
        (spineCertificate.toM8BoundarySpine
          ({ positiveCard :=
               MinimalFailureW8RowAssembly.positiveCard_of_minimalClearedFailure
                 hmin
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
              C hmin).preconnectedNoCut hmin)) :
    MinimalFailureW8RowAssembly.MinimalFailureW8BoundaryLongArcData.{u}
      C hmin where
  topology := Q.topology
  outerAngleBounds := Q.outerAngleBounds
  Subpolygon := Q.Subpolygon
  subpolygonData := Q.subpolygonData
  longArc := Q.w9LongArc
  remainingNoCutSlack := remainingNoCutSlack
  spineCertificate := spineCertificate
  lemma8Existence := lemma8Existence

/-- Build a W9 base row once the boundary-label row has been supplied. -/
def toW9BaseRow
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin Q.toW9TopologyAngleSubpolygonRow) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin where
  topology := Q.toW9TopologyAngleSubpolygonRow
  boundaryLabels := boundaryLabels

/-- Build a W10 direct component row from W11 boundary/turn data and the later
direct no-early/window fields. -/
def toW10DirectComponentPackageRow
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin Q.toW9TopologyAngleSubpolygonRow)
    (noEarlyTriples :
      M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples
        (Q.toW9BaseRow boundaryLabels).localLabels)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (Q.toW9BaseRow boundaryLabels).localLabels
        (Q.toW9BaseRow boundaryLabels).turnBounds) :
    SwanepoelW10ClosureMatrix.DirectComponentPackageRow.{u}
      C hmin where
  base := Q.toW9BaseRow boundaryLabels
  noEarlyTriples := noEarlyTriples
  windowContainment := windowContainment

/-- Build a W10 K23 component row from W11 boundary/turn data and the later
K23/window fields. -/
def toW10K23ComponentPackageRow
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin Q.toW9TopologyAngleSubpolygonRow)
    (k23Obstruction :
      NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
        (Q.toW9BaseRow boundaryLabels).localLabels.predicates.data)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (Q.toW9BaseRow boundaryLabels).localLabels
        (Q.toW9BaseRow boundaryLabels).turnBounds) :
    SwanepoelW10ClosureMatrix.K23ComponentPackageRow.{u}
      C hmin where
  base := Q.toW9BaseRow boundaryLabels
  k23Obstruction := k23Obstruction
  windowContainment := windowContainment

end BoundaryAngleTurnTopologyPackage

end UDConfigRoute

end

end BoundaryAngleTurnW11
end Swanepoel
end ErdosProblems1066
