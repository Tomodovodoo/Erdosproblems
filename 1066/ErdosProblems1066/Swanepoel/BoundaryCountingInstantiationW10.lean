import ErdosProblems1066.Swanepoel.BoundaryPartitionInstantiation
import ErdosProblems1066.Swanepoel.BoundaryAngleWitnessConstruction
import ErdosProblems1066.Swanepoel.LongArcGapConcrete

/-!
# W10 boundary counting instantiation

This module combines the concrete classified boundary partitions, explicit
local unit-separated angle witnesses, and the long-arc count-gap route into
small checked adapters.  It keeps all geometric inputs explicit and only
reindexes the concrete boundary subtypes into the count-indexed consumers.
-/

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryCountingInstantiationW10

open BoundaryCounting
open BoundaryWalkClassificationConcrete

noncomputable section

universe u

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

namespace ClassifiedBoundary

variable (D : OuterBoundaryClassificationInputs P)

/-- The real value of the angle-mass certificate built from explicit
unit-separated local angle witnesses. -/
def angleMassValue {m : Nat}
    (angle :
      Fin m -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle G) :
    Real :=
  (BoundaryAngleWitnessConstruction.angleMassCertificate angle).value

/--
Concrete unit-separated local angle witnesses indexed by the actual classified
boundary subtypes.

The geometric sum equation is stated after reindexing through the concrete
partition equivalences, so it can be fed directly to
`BoundaryAngleWitnessConstruction.OuterBoundaryUnitSeparatedWitness`.
-/
structure UnitSeparatedAngleFamilies where
  degree3 :
    D.degree3Indices -> Fin 2 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree4 :
    D.degree4Indices -> Fin 3 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree5 :
    D.degree5Indices -> Fin 4 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree6 :
    D.degree6Indices -> Fin 5 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  nontriangle :
    D.nontriangleEdgeIndices -> Fin 1 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  longArc :
    D.longArcIndices -> Fin 1 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
          (fun i =>
            angleMassValue
              (degree3
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
          (fun i =>
            angleMassValue
              (degree4
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
          (fun i =>
            angleMassValue
              (degree5
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
          (fun i =>
            angleMassValue
              (degree6
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.b))
          (fun i =>
            angleMassValue
              (nontriangle
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.B))
          (fun i =>
            angleMassValue
              (longArc
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                  D).symm i))) +
      unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon :
    geometricAngleSum <= D.counts.polygonAngleSum

namespace UnitSeparatedAngleFamilies

variable {D}

/-- Convert the subtype-indexed unit-separated witnesses to the concrete
partition-indexed angle-mass family from `BoundaryPartitionInstantiation`. -/
def toLocalAngleFamilies
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LocalAngleFamilies D where
  degree3 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree3 i)
  degree4 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree4 i)
  degree5 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree5 i)
  degree6 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree6 i)
  nontriangle := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.nontriangle i)
  longArc := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.longArc i)

/-- The count-indexed local angle package obtained via the concrete boundary
partition equivalences. -/
def toOuterBoundaryLocalAngles
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleAssembly.OuterBoundaryLocalAngles G D.counts :=
  W.toLocalAngleFamilies.toOuterBoundaryLocalAngles D

/-- Reindex concrete subtype witnesses into the unit-separated witness record
consumed by `BoundaryAngleWitnessConstruction`. -/
def toOuterBoundaryUnitSeparatedWitness
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleWitnessConstruction.OuterBoundaryUnitSeparatedWitness
      G D.counts where
  degree3 := fun i =>
    W.degree3
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin D).symm
        i)
  degree4 := fun i =>
    W.degree4
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin D).symm
        i)
  degree5 := fun i =>
    W.degree5
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin D).symm
        i)
  degree6 := fun i =>
    W.degree6
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin D).symm
        i)
  nontriangle := fun i =>
    W.nontriangle
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
        D).symm i)
  longArc := fun i =>
    W.longArc
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin D).symm
        i)
  unaccountedAngle := W.unaccountedAngle
  geometricAngleSum := W.geometricAngleSum
  geometricAngleSum_eq := by
    simpa only [angleMassValue] using W.geometricAngleSum_eq
  unaccounted_nonnegative := W.unaccounted_nonnegative
  geometric_le_polygon := W.geometric_le_polygon

@[simp]
theorem toOuterBoundaryUnitSeparatedWitness_toLocalAngles
    (W : UnitSeparatedAngleFamilies D) :
    W.toOuterBoundaryUnitSeparatedWitness.toLocalAngles =
      W.toOuterBoundaryLocalAngles :=
  rfl

@[simp]
theorem toOuterBoundaryUnitSeparatedWitness_geometricAngleSum
    (W : UnitSeparatedAngleFamilies D) :
    W.toOuterBoundaryUnitSeparatedWitness.geometricAngleSum =
      W.geometricAngleSum :=
  rfl

/-- The assembled geometric witness for the reindexed local angles. -/
def toGeometricWitness
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleAssembly.OuterBoundaryGeometricWitness
      W.toOuterBoundaryLocalAngles := by
  simpa using W.toOuterBoundaryUnitSeparatedWitness.toGeometricWitness

/-- Concrete angle certificates obtained from the subtype-indexed local
unit-separated witnesses. -/
def toConcreteCertificates
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleCertificatesConcrete.OuterBoundaryAngleCertificates
      G D.counts :=
  W.toOuterBoundaryUnitSeparatedWitness.toConcreteCertificates

/-- The local angle witnesses prove the forced boundary-angle side is below
the supplied geometric angle sum. -/
theorem forced_le_geometricAngleSum
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.forcedBoundaryAngleSum <= W.geometricAngleSum :=
  BoundaryAngleAssembly.OuterBoundaryGeometricWitness.forced_le_geometricAngleSum
    W.toOuterBoundaryUnitSeparatedWitness.toGeometricWitness

/-- The counting-layer E12 angle lower bound from concrete local angle
witnesses. -/
theorem angleLowerBound
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.AngleLowerBound :=
  W.toOuterBoundaryUnitSeparatedWitness.angleLowerBound

/-- E12 in count form, after concrete partition reindexing. -/
theorem boundaryAngleCountInequality
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  W.toOuterBoundaryUnitSeparatedWitness.boundaryAngleCountInequality

/-- Negative-element E12 in count form, after concrete partition reindexing. -/
theorem boundaryNegativeCountInequality
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  W.toOuterBoundaryUnitSeparatedWitness.boundaryNegativeCountInequality

end UnitSeparatedAngleFamilies

/-! ## Combined boundary-count and turn-bound input -/

/--
A classified boundary with explicit local angle witnesses and the long-arc
coverage/count-gap fields tied to the same geometric angle sum.
-/
structure CountTurnInput
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  angleWitness : UnitSeparatedAngleFamilies D
  longArcFields :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      D angleWitness.geometricAngleSum
        angleWitness.forced_le_geometricAngleSum
        angleWitness.geometric_le_polygon Subpolygon subpolygonData

namespace CountTurnInput

variable {D}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- The planar-boundary package built from the same classification, angle
witness, and subpolygon data. -/
def planarBoundary
    (I : CountTurnInput D Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  I.longArcFields.planarBoundary

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.planarBoundary.outerBoundaryCounts = D.counts := by
  simp [planarBoundary]

/-- The long-arc existence/count-gap fields for the constructed planar
boundary. -/
def toBoundaryLongArcExistenceFields
    (I : CountTurnInput D Subpolygon subpolygonData) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      I.planarBoundary := by
  simpa [planarBoundary] using
    I.longArcFields.toBoundaryLongArcExistenceFields

/-- The classified-boundary count-gap wrapper from `LongArcGapConcrete`. -/
def toClassifiedBoundaryCountGapInput
    (I : CountTurnInput D Subpolygon subpolygonData) :
    LongArcGapConcrete.ClassifiedBoundaryCountGapInput
      D I.angleWitness.geometricAngleSum
        I.angleWitness.forced_le_geometricAngleSum
        I.angleWitness.geometric_le_polygon Subpolygon subpolygonData :=
  I.longArcFields.toClassifiedBoundaryCountGapInput

/-- The full reusable boundary-count-gap to M8-turn-bound route. -/
def toBoundaryCountGapToM8TurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      I.toBoundaryLongArcExistenceFields :=
  LongArcGapConcrete.BoundaryCountGapToM8TurnBounds.ofBoundaryLongArcExistenceFields
    I.toBoundaryLongArcExistenceFields

/-- Boundary-attached nonconcave-arc budget data selected by the count gap. -/
def toNonconcaveArcBoundaryBudgetData
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  I.toBoundaryLongArcExistenceFields.toNonconcaveArcBoundaryBudgetData

/-- The reusable boundary-count fields attached to the selected arc budget. -/
def boundaryAngleCountFields
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.BoundaryAngleCountFields
      I.toNonconcaveArcBoundaryBudgetData :=
  I.toNonconcaveArcBoundaryBudgetData.boundaryAngleCountFields

/-- The reusable boundary-to-M8 turn-bound field package. -/
def boundaryToM8TurnBoundFields
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      I.toNonconcaveArcBoundaryBudgetData :=
  I.toNonconcaveArcBoundaryBudgetData.boundaryToM8TurnBoundFields

/-- Honest turn bounds produced by the selected nonconcave long arc. -/
def honestTurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    TurnBoundsInterface.HonestTurnBounds :=
  I.toNonconcaveArcBoundaryBudgetData.toHonestTurnBounds

/-- Construction-level M8 turn bounds produced by the selected nonconcave
long arc. -/
def m8TurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    M8ConstructionInterface.M8TurnBounds :=
  I.toClassifiedBoundaryCountGapInput.toM8TurnBounds

@[simp]
theorem boundaryToM8TurnBoundFields_m8TurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.boundaryToM8TurnBoundFields.m8TurnBounds =
      I.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds :=
  rfl

@[simp]
theorem boundaryToM8TurnBoundFields_honestTurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.boundaryToM8TurnBoundFields.honestTurnBounds =
      I.honestTurnBounds :=
  rfl

/-- E12 in count form from the local angle witness part of the combined
input. -/
theorem boundaryAngleCountInequality
    (I : CountTurnInput D Subpolygon subpolygonData) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  I.angleWitness.boundaryAngleCountInequality

/-- Negative-element E12 in count form from the local angle witness part of
the combined input. -/
theorem boundaryNegativeCountInequality
    (I : CountTurnInput D Subpolygon subpolygonData) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  I.angleWitness.boundaryNegativeCountInequality

/-- The checked long-arc count gap in the combined route. -/
theorem concaveLongArcCount_lt_longArcCount
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.toBoundaryLongArcExistenceFields.concaveLongArcCount <
      I.toBoundaryLongArcExistenceFields.longArcCount :=
  I.toBoundaryLongArcExistenceFields.concaveLongArcCount_lt_longArcCount

/-- A nonconcave concrete long-arc index selected by the count gap. -/
noncomputable def selectedLongArc
    (I : CountTurnInput D Subpolygon subpolygonData) :
    D.longArcIndices :=
  I.toBoundaryLongArcExistenceFields.selectedLongArc

/-- The selected long arc is nonconcave. -/
theorem selectedLongArc_not_concave
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Not (I.longArcFields.concave I.selectedLongArc) :=
  I.toBoundaryLongArcExistenceFields.selectedLongArc_not_concave

/-- The selected long arc has raw total turn below `pi / 3`. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Lemma10Inequalities.totalTurn
        (I.longArcFields.rawTurn I.selectedLongArc) <
      Real.pi / 3 :=
  LongArcExistenceConcrete.BoundaryLongArcExistenceFields.selectedLongArc_totalTurn_lt_pi_div_three
    I.toBoundaryLongArcExistenceFields

/-- Pointwise nonnegativity of the construction-level M8 turn bounds. -/
theorem m8TurnBounds_turn_nonnegative
    (I : CountTurnInput D Subpolygon subpolygonData) (k : Nat) :
    0 <= I.m8TurnBounds.turn k :=
  I.toClassifiedBoundaryCountGapInput.toM8TurnBounds_turn_nonnegative k

/-- The construction-level M8 total turn is below `pi / 3`. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Lemma10Inequalities.totalTurn I.m8TurnBounds.turn < Real.pi / 3 :=
  LongArcGapConcrete.ClassifiedBoundaryCountGapInput.toM8TurnBounds_totalTurn_lt_pi_div_three
    I.toClassifiedBoundaryCountGapInput

/-- The explicit thirteen-turn M8 sum is below `pi / 3`. -/
theorem m8TurnBounds_thirteenTurnSum_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      I.m8TurnBounds.turn < Real.pi / 3 :=
  LongArcGapConcrete.ClassifiedBoundaryCountGapInput.toM8TurnBounds_thirteenTurnSum_lt_pi_div_three
    I.toClassifiedBoundaryCountGapInput

/-- Pointwise nonnegativity of the honest turn-bound package. -/
theorem honestTurnBounds_turn_nonnegative
    (I : CountTurnInput D Subpolygon subpolygonData) (k : Nat) :
    0 <= I.honestTurnBounds.turn k :=
  I.honestTurnBounds.turn_nonnegative k

/-- The honest turn-bound package has total turn below `pi / 3`. -/
theorem honestTurnBounds_totalTurn_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Lemma10Inequalities.totalTurn I.honestTurnBounds.turn <
      Real.pi / 3 :=
  I.honestTurnBounds.total_turn_lt_pi_div_three

end CountTurnInput

end ClassifiedBoundary

end

end BoundaryCountingInstantiationW10
end Swanepoel
end ErdosProblems1066
