import ErdosProblems1066.Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25
import ErdosProblems1066.Swanepoel.BoundaryCounting
import ErdosProblems1066.Swanepoel.SubpolygonAssembly
import ErdosProblems1066.Swanepoel.LongArcExistenceConcrete

set_option autoImplicit false

/-!
# W26 decomposition of the remaining minimal-boundary witness fields

The W25 selected-face bridge fixes the topology from selected outer-face data
and enclosure data.  This file splits the remaining witness into the five
independent constructive gates that still have to be supplied over that fixed
topology:

* boundary-walk classification;
* outer-boundary angle sum and comparisons;
* subpolygon cycle/count/angle data;
* long-arc data over the resulting planar boundary;
* the thirteen-edge triangular boundary run over the same planar boundary.

The main result is an equivalence between this decomposed component package
and the W25 `RemainingWitnessFields`, plus the selected-face row/family
adapters needed by downstream workers.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryWitnessRemainingFieldsW26

open BoundaryArcFiniteWalkConstructionW16
open Lemma10Inequalities
open M8LabelsFromBoundaryInterface
open MinimalBoundaryTopologyWitnessInhabitationW25
open TopologyExtractionFromNoncrossing

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  MinimalBoundaryTopologyWitnessInhabitationW25.CanonicalGraph C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  TopologyExtractionFromNoncrossing.EnclosureFields D

abbrev FixedClassification
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.W24BoundaryClassification C
    (topologyFactsOfSelectedFace D E)

abbrev W25RemainingWitnessFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.RemainingWitnessFields.{u}
    C hmin D E

/-! ## The five component gates -/

structure BoundaryClassificationField
    (C : _root_.UDConfig n)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Type (u + 1) where
  classification : FixedClassification D E

namespace BoundaryClassificationField

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}

def counts (K : BoundaryClassificationField.{u} C D E) :
    BoundaryCounting.BoundaryCounts :=
  K.classification.counts

def boundaryBookkeeping
    (K : BoundaryClassificationField.{u} C D E) :
    BoundaryClassification.BoundaryBookkeeping.{0} :=
  K.classification.boundaryBookkeeping

def countsRealization
    (K : BoundaryClassificationField.{u} C D E) :
    BoundaryClassification.BoundaryCountsRealization.{0} :=
  K.classification.countsRealization

def countsRealizationLift
    (K : BoundaryClassificationField.{u} C D E) :
    BoundaryClassification.BoundaryCountsRealization.{u} :=
  K.classification.countsRealizationLift

@[simp]
theorem counts_eq
    (K : BoundaryClassificationField.{u} C D E) :
    K.counts = K.classification.counts :=
  rfl

@[simp]
theorem countsRealization_toBoundaryCounts
    (K : BoundaryClassificationField.{u} C D E) :
    K.countsRealization.toBoundaryCounts = K.counts :=
  rfl

@[simp]
theorem countsRealizationLift_toBoundaryCounts
    (K : BoundaryClassificationField.{u} C D E) :
    K.countsRealizationLift.toBoundaryCounts = K.counts :=
  rfl

end BoundaryClassificationField

structure OuterBoundaryAngleComparisonField
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    (K : BoundaryClassificationField.{u} C D E) : Type (u + 1) where
  geometricAngleSum : Real
  forced_le_geometric :
    K.counts.forcedBoundaryAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= K.counts.polygonAngleSum

namespace OuterBoundaryAngleComparisonField

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}
variable {K : BoundaryClassificationField.{u} C D E}

def outerAngleBounds
    (A : OuterBoundaryAngleComparisonField.{u} K) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  K.classification.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds A.geometricAngleSum
      A.forced_le_geometric A.geometric_le_polygon

theorem angleLowerBound
    (A : OuterBoundaryAngleComparisonField.{u} K) :
    K.counts.AngleLowerBound :=
  le_trans A.forced_le_geometric A.geometric_le_polygon

theorem boundaryAngleCountInequality
    (A : OuterBoundaryAngleComparisonField.{u} K) :
    K.counts.d5 + 2 * K.counts.d6 + K.counts.b + K.counts.B + 6 <=
      K.counts.d3 :=
  K.counts.boundary_angle_count_inequality A.angleLowerBound

theorem boundaryNegativeCountInequality
    (A : OuterBoundaryAngleComparisonField.{u} K) :
    K.counts.negativeCount + K.counts.B + 6 <= K.counts.d3 :=
  K.counts.boundary_negative_count_inequality A.angleLowerBound

@[simp]
theorem outerAngleBounds_counts
    (A : OuterBoundaryAngleComparisonField.{u} K) :
    A.outerAngleBounds.counts = K.counts :=
  rfl

end OuterBoundaryAngleComparisonField

structure SubpolygonDataField
    (C : _root_.UDConfig n) : Type (u + 1) where
  Subpolygon : Type u
  subpolygonData :
    Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
      (CanonicalGraph C)

namespace SubpolygonDataField

variable {C : _root_.UDConfig n}

def counts
    (S : SubpolygonDataField.{u} C) (P : S.Subpolygon) :
    BoundaryCounting.SubpolygonDegreeCounts :=
  (S.subpolygonData P).counts

theorem lowDegreeWithHighDegreeSlack
    (S : SubpolygonDataField.{u} C) (P : S.Subpolygon) :
    (S.counts P).D5 + 2 * (S.counts P).D6 + 6 <=
      2 * (S.counts P).D2 + (S.counts P).D3 := by
  exact (S.subpolygonData P).lowDegreeWithHighDegreeSlack

theorem lowDegree
    (S : SubpolygonDataField.{u} C) (P : S.Subpolygon) :
    6 <= 2 * (S.counts P).D2 + (S.counts P).D3 := by
  exact (S.subpolygonData P).lowDegreeInequality

@[simp]
theorem subpolygonData_counts
    (S : SubpolygonDataField.{u} C) (P : S.Subpolygon) :
    (S.subpolygonData P).counts = S.counts P :=
  rfl

end SubpolygonDataField

def planarBoundary
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    {K : BoundaryClassificationField.{u} C D E}
    (A : OuterBoundaryAngleComparisonField.{u} K)
    (S : SubpolygonDataField.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  (topologyFactsOfSelectedFace D E).toPlanarBoundaryData
    A.outerAngleBounds S.Subpolygon S.subpolygonData

structure LongArcField
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    {K : BoundaryClassificationField.{u} C D E}
    (A : OuterBoundaryAngleComparisonField.{u} K)
    (S : SubpolygonDataField.{u} C) : Type (u + 1) where
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (planarBoundary A S)

namespace LongArcField

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}
variable {K : BoundaryClassificationField.{u} C D E}
variable {A : OuterBoundaryAngleComparisonField.{u} K}
variable {S : SubpolygonDataField.{u} C}

def longArcCount (L : LongArcField.{u} A S) : Nat :=
  L.longArc.longArcCount

def concaveLongArcCount (L : LongArcField.{u} A S) : Nat :=
  L.longArc.concaveLongArcCount

theorem concaveLongArcCount_lt_longArcCount
    (L : LongArcField.{u} A S) :
    L.concaveLongArcCount < L.longArcCount :=
  L.longArc.concaveLongArcCount_lt_longArcCount

theorem exists_nonconcave_longArc
    (L : LongArcField.{u} A S) :
    Exists fun a : L.longArc.LongArc => Not (L.longArc.concave a) :=
  L.longArc.exists_nonconcave_longArc

theorem selectedLongArc_totalTurn_lt_pi_div_three
    (L : LongArcField.{u} A S) :
    totalTurn
      (L.longArc.rawTurn L.longArc.selectedLongArc) < Real.pi / 3 :=
  L.longArc.selectedLongArc_totalTurn_lt_pi_div_three

end LongArcField

structure TriangleRunField
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    {K : BoundaryClassificationField.{u} C D E}
    (A : OuterBoundaryAngleComparisonField.{u} K)
    (S : SubpolygonDataField.{u} C) : Type (u + 1) where
  triangleRun : BoundaryArcTriangleRun (planarBoundary A S)

namespace TriangleRunField

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}
variable {K : BoundaryClassificationField.{u} C D E}
variable {A : OuterBoundaryAngleComparisonField.{u} K}
variable {S : SubpolygonDataField.{u} C}

def finiteWalk
    (T : TriangleRunField.{u} A S) :
    BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkData
      (planarBoundary A S) :=
  T.triangleRun.toFiniteWalkData

theorem finiteWalk_cyclicOrder
    (T : TriangleRunField.{u} A S) (i : M8TriangleIndex) :
    T.finiteWalk.pIndex (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc (planarBoundary A S).core.outerCycle.length_pos
        (T.finiteWalk.pIndex (m8BoundaryIndexLeft i)) :=
  T.triangleRun.toFiniteWalkData_cyclicOrder i

theorem finiteWalk_triangleWitness
    (T : TriangleRunField.{u} A S) (i : M8TriangleIndex) :
    (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor
      (T.finiteWalk.p (m8BoundaryIndexLeft i))
      (T.finiteWalk.p (m8BoundaryIndexRight i))
      (T.finiteWalk.q i) :=
  T.triangleRun.toFiniteWalkData_triangleWitness i

end TriangleRunField

/-! ## Exact assembly back to W25 -/

structure RemainingWitnessComponentFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Type (u + 1) where
  classificationField : BoundaryClassificationField.{u} C D E
  angleField : OuterBoundaryAngleComparisonField.{u} classificationField
  subpolygonField : SubpolygonDataField.{u} C
  longArcField : LongArcField.{u} angleField subpolygonField
  triangleRunField : TriangleRunField.{u} angleField subpolygonField

namespace RemainingWitnessComponentFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}

def planarBoundary
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  BoundaryWitnessRemainingFieldsW26.planarBoundary
    P.angleField P.subpolygonField

def toRemainingWitnessFields
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    W25RemainingWitnessFields.{u} C hmin D E where
  classification := P.classificationField.classification
  geometricAngleSum := P.angleField.geometricAngleSum
  forced_le_geometric := P.angleField.forced_le_geometric
  geometric_le_polygon := P.angleField.geometric_le_polygon
  Subpolygon := P.subpolygonField.Subpolygon
  subpolygonData := P.subpolygonField.subpolygonData
  longArc := P.longArcField.longArc
  triangleRun := P.triangleRunField.triangleRun

def ofRemainingWitnessFields
    (R : W25RemainingWitnessFields.{u} C hmin D E) :
    RemainingWitnessComponentFields.{u} C hmin D E where
  classificationField :=
    { classification := R.classification }
  angleField :=
    { geometricAngleSum := R.geometricAngleSum
      forced_le_geometric := R.forced_le_geometric
      geometric_le_polygon := R.geometric_le_polygon }
  subpolygonField :=
    { Subpolygon := R.Subpolygon
      subpolygonData := R.subpolygonData }
  longArcField :=
    { longArc := R.longArc }
  triangleRunField :=
    { triangleRun := R.triangleRun }

@[simp]
theorem toRemainingWitnessFields_classification
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    P.toRemainingWitnessFields.classification =
      P.classificationField.classification :=
  rfl

@[simp]
theorem toRemainingWitnessFields_geometricAngleSum
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    P.toRemainingWitnessFields.geometricAngleSum =
      P.angleField.geometricAngleSum :=
  rfl

@[simp]
theorem toRemainingWitnessFields_Subpolygon
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    P.toRemainingWitnessFields.Subpolygon =
      P.subpolygonField.Subpolygon :=
  rfl

@[simp]
theorem toRemainingWitnessFields_planarBoundary
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    P.toRemainingWitnessFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toRemainingWitnessFields_longArc
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    P.toRemainingWitnessFields.longArc =
      P.longArcField.longArc :=
  rfl

@[simp]
theorem toRemainingWitnessFields_triangleRun
    (P : RemainingWitnessComponentFields.{u} C hmin D E) :
    P.toRemainingWitnessFields.triangleRun =
      P.triangleRunField.triangleRun :=
  rfl

def remainingWitnessFieldsEquiv :
    Equiv
      (RemainingWitnessComponentFields.{u} C hmin D E)
      (W25RemainingWitnessFields.{u} C hmin D E) where
  toFun := toRemainingWitnessFields
  invFun := ofRemainingWitnessFields
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro R
    cases R
    rfl

theorem nonempty_remainingWitnessFields_iff_components :
    Nonempty (W25RemainingWitnessFields.{u} C hmin D E) <->
      Nonempty (RemainingWitnessComponentFields.{u} C hmin D E) := by
  constructor
  · intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (ofRemainingWitnessFields R)
  · intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toRemainingWitnessFields

end RemainingWitnessComponentFields

/-! ## Selected-face row and family adapters -/

structure SelectedFaceRemainingComponentRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) where
  selectedFace : SelectedOuterFaceData C
  enclosure : SelectedEnclosureData selectedFace
  remaining :
    RemainingWitnessComponentFields.{u} C hmin selectedFace enclosure

namespace SelectedFaceRemainingComponentRow

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def toSelectedFaceWitnessRow
    (P : SelectedFaceRemainingComponentRow.{u} C hmin) :
    MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
      C hmin where
  selectedFace := P.selectedFace
  enclosure := P.enclosure
  remaining := P.remaining.toRemainingWitnessFields

def ofSelectedFaceWitnessRow
    (R :
      MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
        C hmin) :
    SelectedFaceRemainingComponentRow.{u} C hmin where
  selectedFace := R.selectedFace
  enclosure := R.enclosure
  remaining :=
    RemainingWitnessComponentFields.ofRemainingWitnessFields R.remaining

@[simp]
theorem toSelectedFaceWitnessRow_selectedFace
    (P : SelectedFaceRemainingComponentRow.{u} C hmin) :
    P.toSelectedFaceWitnessRow.selectedFace = P.selectedFace :=
  rfl

@[simp]
theorem toSelectedFaceWitnessRow_enclosure
    (P : SelectedFaceRemainingComponentRow.{u} C hmin) :
    P.toSelectedFaceWitnessRow.enclosure = P.enclosure :=
  rfl

@[simp]
theorem toSelectedFaceWitnessRow_remaining
    (P : SelectedFaceRemainingComponentRow.{u} C hmin) :
    P.toSelectedFaceWitnessRow.remaining =
      P.remaining.toRemainingWitnessFields :=
  rfl

def selectedFaceWitnessRowEquiv :
    Equiv
      (SelectedFaceRemainingComponentRow.{u} C hmin)
      (MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
        C hmin) where
  toFun := toSelectedFaceWitnessRow
  invFun := ofSelectedFaceWitnessRow
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro R
    cases R
    rfl

theorem nonempty_selectedFaceWitnessRow_iff_components :
    Nonempty
        (MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
          C hmin) <->
      Nonempty (SelectedFaceRemainingComponentRow.{u} C hmin) := by
  constructor
  · intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (ofSelectedFaceWitnessRow R)
  · intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toSelectedFaceWitnessRow

end SelectedFaceRemainingComponentRow

structure SelectedFaceRemainingComponentFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFaceRemainingComponentRow.{u} C hmin

namespace SelectedFaceRemainingComponentFamily

def toSelectedFaceWitnessFamily
    (F : SelectedFaceRemainingComponentFamily.{u}) :
    MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u} where
  row := fun C hmin => (F.row C hmin).toSelectedFaceWitnessRow

def toW24WitnessFamily
    (F : SelectedFaceRemainingComponentFamily.{u}) :
    MinimalBoundaryTopologyWitnessInhabitationW25.W24WitnessFamily.{u} :=
  F.toSelectedFaceWitnessFamily.toW24WitnessFamily

theorem nonempty_selectedFaceWitnessFamily
    (F : SelectedFaceRemainingComponentFamily.{u}) :
    Nonempty
      MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u} :=
  Nonempty.intro F.toSelectedFaceWitnessFamily

theorem nonempty_w24WitnessFamily
    (F : SelectedFaceRemainingComponentFamily.{u}) :
    Nonempty
      MinimalBoundaryTopologyWitnessInhabitationW25.W24WitnessFamily.{u} :=
  Nonempty.intro F.toW24WitnessFamily

theorem nonempty_concreteTriangleRunSourceFamily
    (F : SelectedFaceRemainingComponentFamily.{u}) :
    Nonempty
      JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u} :=
  F.toSelectedFaceWitnessFamily.nonempty_concreteTriangleRunSourceFamily

theorem nonempty_actualInputsFamily
    (F : SelectedFaceRemainingComponentFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u} :=
  F.toSelectedFaceWitnessFamily.nonempty_actualInputsFamily

end SelectedFaceRemainingComponentFamily

theorem selectedFaceWitnessFamily_nonempty_of_componentFamily
    (h : Nonempty SelectedFaceRemainingComponentFamily.{u}) :
    Nonempty
      MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u} := by
  cases h with
  | intro F =>
      exact F.nonempty_selectedFaceWitnessFamily

theorem w24WitnessFamily_nonempty_of_componentFamily
    (h : Nonempty SelectedFaceRemainingComponentFamily.{u}) :
    Nonempty MinimalBoundaryTopologyWitnessInhabitationW25.W24WitnessFamily.{u} := by
  cases h with
  | intro F =>
      exact F.nonempty_w24WitnessFamily

end

end BoundaryWitnessRemainingFieldsW26
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW26BoundaryRemainingComponentFamily : Type (u + 1) :=
  Swanepoel.BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{u}

abbrev SwanepoelW26SelectedFaceWitnessFamily : Type (u + 1) :=
  Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u}

theorem swanepoelW26_selectedFaceWitnessFamily_nonempty
    (h : Nonempty SwanepoelW26BoundaryRemainingComponentFamily.{u}) :
    Nonempty SwanepoelW26SelectedFaceWitnessFamily.{u} :=
  Swanepoel.BoundaryWitnessRemainingFieldsW26.selectedFaceWitnessFamily_nonempty_of_componentFamily
    h

theorem swanepoelW26_minimalBoundaryTopologyWitnessFamily_nonempty
    (h : Nonempty SwanepoelW26BoundaryRemainingComponentFamily.{u}) :
    Nonempty
      Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25.W24WitnessFamily.{u} :=
  Swanepoel.BoundaryWitnessRemainingFieldsW26.w24WitnessFamily_nonempty_of_componentFamily
    h

end Verified
end ErdosProblems1066
