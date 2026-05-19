import ErdosProblems1066.Swanepoel.BoundaryWalkFinitePartitions
import ErdosProblems1066.Swanepoel.BoundaryAngleAssembly
import ErdosProblems1066.Swanepoel.LongArcGapConcrete

/-!
# Concrete boundary partition instantiations

This module is a narrow adapter from the concrete boundary-walk partitions to
the count-indexed consumers.  It does not add new geometric assumptions: the
finite coverage and disjointness facts come from
`BoundaryWalkFinitePartitions`, while the concrete classes and count
projections come from `BoundaryWalkClassificationConcrete`.
-/

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryPartitionInstantiation

open BoundaryCounting
open BoundaryClassification
open BoundaryWalkClassificationConcrete

noncomputable section

universe u

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

namespace ClassifiedBoundary

variable (D : OuterBoundaryClassificationInputs P)

/-! ## Coverage and disjointness aliases -/

/-- The concrete triangle/nontriangle edge partition is disjoint. -/
theorem edge_disjoint :
    Disjoint D.triangleEdgeIndexFinset D.nontriangleEdgeIndexFinset :=
  OuterBoundaryClassificationInputs.edgeIndexFinsets_disjoint D

/-- The concrete triangle/nontriangle edge partition covers all boundary
edge indices. -/
theorem edge_cover :
    D.triangleEdgeIndexFinset ∪ D.nontriangleEdgeIndexFinset =
      Finset.univ :=
  OuterBoundaryClassificationInputs.edgeIndexFinsets_cover D

/-- The concrete degree-three and degree-four classes are disjoint. -/
theorem degree3_degree4_disjoint :
    Disjoint D.degree3IndexFinset D.degree4IndexFinset :=
  OuterBoundaryClassificationInputs.degree3_degree4_disjoint D

/-- The concrete degree-three and degree-five classes are disjoint. -/
theorem degree3_degree5_disjoint :
    Disjoint D.degree3IndexFinset D.degree5IndexFinset :=
  OuterBoundaryClassificationInputs.degree3_degree5_disjoint D

/-- The concrete degree-three and degree-six classes are disjoint. -/
theorem degree3_degree6_disjoint :
    Disjoint D.degree3IndexFinset D.degree6IndexFinset :=
  OuterBoundaryClassificationInputs.degree3_degree6_disjoint D

/-- The concrete degree-four and degree-five classes are disjoint. -/
theorem degree4_degree5_disjoint :
    Disjoint D.degree4IndexFinset D.degree5IndexFinset :=
  OuterBoundaryClassificationInputs.degree4_degree5_disjoint D

/-- The concrete degree-four and degree-six classes are disjoint. -/
theorem degree4_degree6_disjoint :
    Disjoint D.degree4IndexFinset D.degree6IndexFinset :=
  OuterBoundaryClassificationInputs.degree4_degree6_disjoint D

/-- The concrete degree-five and degree-six classes are disjoint. -/
theorem degree5_degree6_disjoint :
    Disjoint D.degree5IndexFinset D.degree6IndexFinset :=
  OuterBoundaryClassificationInputs.degree5_degree6_disjoint D

/-- The concrete degree classes cover all boundary vertex indices. -/
theorem degree_cover :
    ((D.degree3IndexFinset ∪ D.degree4IndexFinset) ∪
        D.degree5IndexFinset) ∪ D.degree6IndexFinset =
      Finset.univ :=
  OuterBoundaryClassificationInputs.degreeIndexFinsets_cover D

/-! ## Count transport from concrete partitions -/

@[simp]
theorem counts_d3_eq_card :
    D.counts.d3 = Fintype.card D.degree3Indices :=
  D.counts_d3

@[simp]
theorem counts_d4_eq_card :
    D.counts.d4 = Fintype.card D.degree4Indices :=
  D.counts_d4

@[simp]
theorem counts_d5_eq_card :
    D.counts.d5 = Fintype.card D.degree5Indices :=
  D.counts_d5

@[simp]
theorem counts_d6_eq_card :
    D.counts.d6 = Fintype.card D.degree6Indices :=
  D.counts_d6

@[simp]
theorem counts_b_eq_card :
    D.counts.b = Fintype.card D.nontriangleEdgeIndices :=
  D.counts_b

@[simp]
theorem counts_B_eq_card :
    D.counts.B = Fintype.card D.longArcIndices :=
  D.counts_B

@[simp]
theorem longArcIndex_card_eq_counts_B :
    Fintype.card D.longArcIndices = D.counts.B :=
  D.counts_B.symm

@[simp]
theorem counts_negativeCount_eq_card_sum :
    D.counts.negativeCount =
      Fintype.card D.nontriangleEdgeIndices +
        Fintype.card D.degree5Indices +
        Fintype.card D.degree6Indices :=
  D.counts_negativeCount

/-- The concrete degree partition transports to the `BoundaryCounts`
vertex-count field. -/
theorem counts_vertexCount_eq_length :
    D.counts.vertexCount = P.outerCycle.length := by
  unfold BoundaryCounts.vertexCount
  exact D.counts_degree_sum_eq_length

/-- The concrete triangle/nontriangle edge partition transports to the
triangle-edge plus `b` boundary-length count. -/
theorem triangleEdgeCount_add_b_eq_length :
    D.boundaryBookkeeping.triangleEdgeCount + D.counts.b =
      P.outerCycle.length :=
  D.boundaryBookkeeping_triangleEdgeCount_add_counts_b

/-- The finite bookkeeping projected from the concrete classification realizes
exactly the concrete counts. -/
@[simp]
theorem boundaryBookkeeping_toBoundaryCounts :
    D.boundaryBookkeeping.toBoundaryCounts = D.counts :=
  D.boundaryBookkeeping_toBoundaryCounts

/-- The universe-polymorphic count realization projected from the concrete
classification realizes exactly the concrete counts. -/
@[simp]
theorem countsRealizationLift_toBoundaryCounts :
    D.countsRealizationLift.toBoundaryCounts = D.counts :=
  D.countsRealizationLift_toBoundaryCounts

/-! ## Equivalences to count-indexed `Fin` types -/

/-- Degree-three concrete indices are equivalent to `Fin counts.d3`. -/
def degree3EquivFin : Equiv D.degree3Indices (Fin D.counts.d3) :=
  Fintype.equivFinOfCardEq (counts_d3_eq_card D).symm

/-- Degree-four concrete indices are equivalent to `Fin counts.d4`. -/
def degree4EquivFin : Equiv D.degree4Indices (Fin D.counts.d4) :=
  Fintype.equivFinOfCardEq (counts_d4_eq_card D).symm

/-- Degree-five concrete indices are equivalent to `Fin counts.d5`. -/
def degree5EquivFin : Equiv D.degree5Indices (Fin D.counts.d5) :=
  Fintype.equivFinOfCardEq (counts_d5_eq_card D).symm

/-- Degree-six concrete indices are equivalent to `Fin counts.d6`. -/
def degree6EquivFin : Equiv D.degree6Indices (Fin D.counts.d6) :=
  Fintype.equivFinOfCardEq (counts_d6_eq_card D).symm

/-- Nontriangle concrete edge indices are equivalent to `Fin counts.b`. -/
def nontriangleEquivFin :
    Equiv D.nontriangleEdgeIndices (Fin D.counts.b) :=
  Fintype.equivFinOfCardEq (counts_b_eq_card D).symm

/-- Concrete long-arc indices are equivalent to `Fin counts.B`. -/
def longArcEquivFin : Equiv D.longArcIndices (Fin D.counts.B) :=
  Fintype.equivFinOfCardEq (counts_B_eq_card D).symm

/-! ## BoundaryAngleAssembly-facing reindexing -/

/-- Concrete local angle certificates indexed by the actual classified
boundary partitions. -/
structure LocalAngleFamilies where
  degree3 :
    D.degree3Indices ->
      BoundaryAngleCertificatesConcrete.AngleMassCertificate G 2
  degree4 :
    D.degree4Indices ->
      BoundaryAngleCertificatesConcrete.AngleMassCertificate G 3
  degree5 :
    D.degree5Indices ->
      BoundaryAngleCertificatesConcrete.AngleMassCertificate G 4
  degree6 :
    D.degree6Indices ->
      BoundaryAngleCertificatesConcrete.AngleMassCertificate G 5
  nontriangle :
    D.nontriangleEdgeIndices ->
      BoundaryAngleCertificatesConcrete.AngleMassCertificate G 1
  longArc :
    D.longArcIndices ->
      BoundaryAngleCertificatesConcrete.AngleMassCertificate G 1

namespace LocalAngleFamilies

/-- Reindex concrete partition-indexed certificates into the `Fin counts.*`
shape consumed by `BoundaryAngleAssembly`. -/
def toOuterBoundaryLocalAngles
    (A : LocalAngleFamilies D) :
    BoundaryAngleAssembly.OuterBoundaryLocalAngles G D.counts where
  degree3 := fun i => A.degree3 ((degree3EquivFin D).symm i)
  degree4 := fun i => A.degree4 ((degree4EquivFin D).symm i)
  degree5 := fun i => A.degree5 ((degree5EquivFin D).symm i)
  degree6 := fun i => A.degree6 ((degree6EquivFin D).symm i)
  nontriangle := fun i => A.nontriangle ((nontriangleEquivFin D).symm i)
  longArc := fun i => A.longArc ((longArcEquivFin D).symm i)

@[simp]
theorem toOuterBoundaryLocalAngles_degree3
    (A : LocalAngleFamilies D) (i : Fin D.counts.d3) :
    (A.toOuterBoundaryLocalAngles D).degree3 i =
      A.degree3 ((degree3EquivFin D).symm i) :=
  rfl

@[simp]
theorem toOuterBoundaryLocalAngles_degree4
    (A : LocalAngleFamilies D) (i : Fin D.counts.d4) :
    (A.toOuterBoundaryLocalAngles D).degree4 i =
      A.degree4 ((degree4EquivFin D).symm i) :=
  rfl

@[simp]
theorem toOuterBoundaryLocalAngles_degree5
    (A : LocalAngleFamilies D) (i : Fin D.counts.d5) :
    (A.toOuterBoundaryLocalAngles D).degree5 i =
      A.degree5 ((degree5EquivFin D).symm i) :=
  rfl

@[simp]
theorem toOuterBoundaryLocalAngles_degree6
    (A : LocalAngleFamilies D) (i : Fin D.counts.d6) :
    (A.toOuterBoundaryLocalAngles D).degree6 i =
      A.degree6 ((degree6EquivFin D).symm i) :=
  rfl

@[simp]
theorem toOuterBoundaryLocalAngles_nontriangle
    (A : LocalAngleFamilies D) (i : Fin D.counts.b) :
    (A.toOuterBoundaryLocalAngles D).nontriangle i =
      A.nontriangle ((nontriangleEquivFin D).symm i) :=
  rfl

@[simp]
theorem toOuterBoundaryLocalAngles_longArc
    (A : LocalAngleFamilies D) (i : Fin D.counts.B) :
    (A.toOuterBoundaryLocalAngles D).longArc i =
      A.longArc ((longArcEquivFin D).symm i) :=
  rfl

end LocalAngleFamilies

/-! ## LongArcGapConcrete-facing instantiation -/

/-- Any concavity predicate on the actual classified long-arc subtype has
cardinality at most the computed boundary long-arc count. -/
theorem concaveLongArcCount_le_counts_B_of_subtype
    (concave : D.longArcIndices -> Prop)
    [concaveLongArcFintype :
      Fintype {a : D.longArcIndices // concave a}] :
    @Fintype.card {a : D.longArcIndices // concave a}
        concaveLongArcFintype <= D.counts.B := by
  have hsub :
      @Fintype.card {a : D.longArcIndices // concave a}
          concaveLongArcFintype <=
        @Fintype.card D.longArcIndices inferInstance :=
    Fintype.card_subtype_le concave
  have hcard :
      @Fintype.card D.longArcIndices inferInstance = D.counts.B :=
    longArcIndex_card_eq_counts_B D
  rw [hcard] at hsub
  exact hsub

/-- The canonical raw-turn interpretation of concavity for actual classified
long-arc indices. -/
def rawTurnConcave
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (a : D.longArcIndices) : Prop :=
  Real.pi / 3 <= Lemma10Inequalities.totalTurn (rawTurn a)

@[simp]
theorem rawTurnConcave_iff
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (a : D.longArcIndices) :
    rawTurnConcave D rawTurn a <->
      Real.pi / 3 <= Lemma10Inequalities.totalTurn (rawTurn a) :=
  Iff.rfl

/-- Long-arc fields whose finite long-arc type is the concrete classified
boundary long-arc subtype. -/
structure LongArcExistenceFields
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  concave : D.longArcIndices -> Prop
  concaveLongArcFintype :
    Fintype {a : D.longArcIndices // concave a}
  concaveLongArcCount_le_counts_B :
    @Fintype.card {a : D.longArcIndices // concave a}
        concaveLongArcFintype <= D.counts.B
  degreeThree_le_negativeCount_add_longArcCount :
    D.counts.d3 <= D.counts.negativeCount +
      @Fintype.card D.longArcIndices inferInstance
  rawTurn : D.longArcIndices -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : D.longArcIndices,
      forall k : Nat, Membership.mem Lemma10Inequalities.turnIndexSet k ->
        0 <= rawTurn a k
  concave_iff :
    forall a : D.longArcIndices,
      concave a <->
        Real.pi / 3 <= Lemma10Inequalities.totalTurn (rawTurn a)

namespace LongArcExistenceFields

variable {D}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  D.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= D.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- The planar-boundary data built from the same classified boundary and
subpolygon data. -/
def planarBoundary
    (_F :
      LongArcExistenceFields D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
    geometric_le_polygon Subpolygon subpolygonData

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (F :
      LongArcExistenceFields D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    F.planarBoundary.outerBoundaryCounts = D.counts := by
  simp [planarBoundary]

/-- Build the classified-boundary long-arc fields from coverage and the
raw-turn/concavity interpretation.  The concave-count comparison with
`D.counts.B` is derived from the actual classified long-arc subtype. -/
def ofCoverageAndTurns
    (concave : D.longArcIndices -> Prop)
    [concaveLongArcFintype :
      Fintype {a : D.longArcIndices // concave a}]
    (degreeThree_le_negativeCount_add_longArcCount :
      D.counts.d3 <= D.counts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem Lemma10Inequalities.turnIndexSet k ->
          0 <= rawTurn a k)
    (concave_iff :
      forall a : D.longArcIndices,
        concave a <->
          Real.pi / 3 <= Lemma10Inequalities.totalTurn (rawTurn a)) :
    LongArcExistenceFields D geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData where
  concave := concave
  concaveLongArcFintype := concaveLongArcFintype
  concaveLongArcCount_le_counts_B :=
    ClassifiedBoundary.concaveLongArcCount_le_counts_B_of_subtype
      D concave
  degreeThree_le_negativeCount_add_longArcCount :=
    degreeThree_le_negativeCount_add_longArcCount
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc
  concave_iff := concave_iff

/-- Build the classified-boundary long-arc fields from the concrete coverage
inequality and raw turns, with concavity interpreted definitionally by the raw
total-turn threshold. -/
def ofCoverageAndRawTurns
    (degreeThree_le_negativeCount_add_longArcCount :
      D.counts.d3 <= D.counts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance)
    (rawTurn : D.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : D.longArcIndices,
        forall k : Nat, Membership.mem Lemma10Inequalities.turnIndexSet k ->
          0 <= rawTurn a k) :
    LongArcExistenceFields D geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData := by
  classical
  exact
    ofCoverageAndTurns
      (D := D) (geometricAngleSum := geometricAngleSum)
      (forced_le_geometric := forced_le_geometric)
      (geometric_le_polygon := geometric_le_polygon)
      (Subpolygon := Subpolygon) (subpolygonData := subpolygonData)
      (concave := ClassifiedBoundary.rawTurnConcave D rawTurn)
      degreeThree_le_negativeCount_add_longArcCount rawTurn
      rawTurn_nonnegative_on_arc
      (by
        intro a
        rfl)

/-- Convert concrete classified long-arc fields to the count-gap input used by
`LongArcGapConcrete`. -/
def toBoundaryLongArcExistenceFields
    (F :
      LongArcExistenceFields D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      F.planarBoundary where
  LongArc := D.longArcIndices
  longArcFintype := inferInstance
  concave := F.concave
  concaveLongArcFintype := F.concaveLongArcFintype
  concaveLongArcCount_le_boundaryConcaveCount := by
    change
      @Fintype.card {a : D.longArcIndices // F.concave a}
          F.concaveLongArcFintype <= D.counts.B
    exact F.concaveLongArcCount_le_counts_B
  degreeThree_le_negativeCount_add_longArcCount := by
    change
      D.counts.d3 <= D.counts.negativeCount +
        @Fintype.card D.longArcIndices inferInstance
    exact F.degreeThree_le_negativeCount_add_longArcCount
  rawTurn := F.rawTurn
  rawTurn_nonnegative_on_arc := F.rawTurn_nonnegative_on_arc
  concave_iff := F.concave_iff

/-- The same fields, viewed as actual boundary-walk long-arc facts for the
classified boundary walk. -/
def toBoundaryWalkLongArcFacts
    (F :
      LongArcExistenceFields D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.BoundaryWalkLongArcFacts
      D.toOuterBoundaryWalkBookkeeping geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData where
  concave := F.concave
  concaveLongArcFintype := F.concaveLongArcFintype
  concaveLongArcCount_lt_boundaryLongArcCount := by
    have hgap :
        @Fintype.card {a : D.longArcIndices // F.concave a}
          F.concaveLongArcFintype <
          @Fintype.card D.longArcIndices inferInstance :=
      F.toBoundaryLongArcExistenceFields.concaveLongArcCount_lt_longArcCount
    change
      @Fintype.card {a : D.longArcIndices // F.concave a}
          F.concaveLongArcFintype < D.counts.B
    have hcard :
        @Fintype.card D.longArcIndices inferInstance = D.counts.B :=
      longArcIndex_card_eq_counts_B D
    rw [hcard] at hgap
    exact hgap
  rawTurn := F.rawTurn
  rawTurn_nonnegative_on_arc := F.rawTurn_nonnegative_on_arc
  concave_iff := F.concave_iff

/-- Package the same concrete fields in the classified-boundary wrapper from
`LongArcGapConcrete`. -/
def toClassifiedBoundaryCountGapInput
    (F :
      LongArcExistenceFields D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    LongArcGapConcrete.ClassifiedBoundaryCountGapInput
      D geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData where
  fields := F.toBoundaryLongArcExistenceFields

@[simp]
theorem toClassifiedBoundaryCountGapInput_fields_LongArc
    (F :
      LongArcExistenceFields D geometricAngleSum forced_le_geometric
        geometric_le_polygon Subpolygon subpolygonData) :
    F.toClassifiedBoundaryCountGapInput.fields.LongArc = D.longArcIndices :=
  rfl

end LongArcExistenceFields

end ClassifiedBoundary

end

end BoundaryPartitionInstantiation
end Swanepoel
end ErdosProblems1066
