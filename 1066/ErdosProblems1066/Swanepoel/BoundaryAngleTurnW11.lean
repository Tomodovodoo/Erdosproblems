import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10
import ErdosProblems1066.Swanepoel.BoundaryAngleAssembly
import ErdosProblems1066.Swanepoel.BoundaryAngleCertificatesConcrete
import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts
import ErdosProblems1066.Swanepoel.LongArcGapConcrete
import ErdosProblems1066.Swanepoel.SwanepoelRemainingMatrix
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix

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
  simpa [outerAngleBounds, ClassifiedBoundary.BoundaryAngleTurnPackage.planarBoundary]
    using Q.boundary.boundaryLongArcExistenceFields

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
