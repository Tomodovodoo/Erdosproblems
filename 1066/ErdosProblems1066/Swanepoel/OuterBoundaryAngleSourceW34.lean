import ErdosProblems1066.Swanepoel.OuterBoundaryInstantiationW13
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28
import ErdosProblems1066.Swanepoel.SelectedTopologyRowsInhabitationW33
import ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement
import ErdosProblems1066.Swanepoel.SubpolygonSelectedGeometrySourceW34
import ErdosProblems1066.Swanepoel.MinimumDegree
import ErdosProblems1066.Swanepoel.BoundaryWalkBridge

set_option autoImplicit false

/-!
# W34 selected outer-boundary angle source

This file keeps the E12 angle source attached to the actual selected outer
boundary.  A row consists of the selected topology datum, a classification of
that selected boundary core, and the concrete unit-separated angle witnesses
for that same classification.  The main projections go directly through
`OuterBoundaryAngleW12.outerBoundaryAngleRealization` and
`OuterBoundaryAngleW12.angleLowerBound`; the W13 aggregate shape is only
available as a compatibility projection.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryAngleSourceW34

open BoundaryCounting

noncomputable section

universe u

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.CanonicalGraph C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

abbrev MinimalFailureSelectedTopologySourceTarget : Prop :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget

abbrev MinimalFailureActualSelectedTopologyRows : Type 1 :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureActualSelectedTopologyRows

/-- The concrete ambient degree used by the boundary classification is the
minimal-degree pipeline's finite unit-neighbor count. -/
theorem ambientDegree_eq_unitDistanceNeighborSet_card
    (C : _root_.UDConfig n) (v : Fin n) :
    BoundaryWalkClassificationConcrete.ambientDegree (CanonicalGraph C) v =
      (DegreePipeline.unitDistanceNeighborSet C v).card := by
  classical
  unfold BoundaryWalkClassificationConcrete.ambientDegree
  unfold LocalExclusions.LocalGraph.degree
  apply congrArg Finset.card
  ext u
  rw [LocalExclusions.LocalGraph.mem_neighborFinset,
    DegreePipeline.mem_unitDistanceNeighborSet]
  constructor
  · intro h
    change (GraphBridge.unitDistanceLocalGraph C).Adj v u at h
    have hne : u ≠ v := by
      intro huv
      subst u
      exact GraphBridge.unitDistanceAdj_loopless C v h
    have hneBool : (u != v) = true := by
      simpa [bne_iff_ne] using hne
    refine And.intro hneBool ?_
    simpa [GraphBridge.UnitDistanceAdj, _root_.eucDist_comm] using h
  · intro h
    change (GraphBridge.unitDistanceLocalGraph C).Adj v u
    change GraphBridge.UnitDistanceAdj C v u
    simpa [GraphBridge.UnitDistanceAdj, _root_.eucDist_comm] using h.2

/-- Minimal cleared failures have boundary-classification degree lower bounds
at every ambient vertex, hence at every selected boundary vertex. -/
theorem ambientDegree_ge_three_of_minimalFailure
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (v : Fin n) :
    3 <= BoundaryWalkClassificationConcrete.ambientDegree (CanonicalGraph C) v := by
  rw [ambientDegree_eq_unitDistanceNeighborSet_card C v]
  exact
    MinimumDegree.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
      hmin v

/-- The canonical classification generated from a selected topology row and
minimality.  The long-arc predicate is chosen explicitly; the remaining local
Euclidean angle witness below is the exact geometric content still needed. -/
def selectedClassificationOfMinimalFailure
    {C : _root_.UDConfig n}
    (topology : ActualSelectedTopologyData C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toOuterBoundaryCore.outerCycle.length -> Prop) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toOuterBoundaryCore :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.ofLongArcPredicate
    (fun k =>
      ambientDegree_ge_three_of_minimalFailure C hmin
        (topology.toOuterBoundaryCore.outerCycle.vertex k))
    longArc

@[simp]
theorem selectedClassificationOfMinimalFailure_longArc
    {C : _root_.UDConfig n}
    (topology : ActualSelectedTopologyData C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toOuterBoundaryCore.outerCycle.length -> Prop) :
    (selectedClassificationOfMinimalFailure topology hmin longArc).longArc =
      longArc :=
  rfl

/-- Minimality supplies an actual unit-separated angle triple at any ambient
vertex: take two distinct unit-distance neighbours of the vertex. -/
def unitSeparatedAngleAtVertexOfMinimalFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (center : Fin n) :
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C) := by
  classical
  let neighbors := DegreePipeline.unitDistanceNeighborSet C center
  have hcard : 3 <= neighbors.card := by
    simpa [neighbors] using
      MinimumDegree.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
        hmin center
  have htwo : 1 < neighbors.card :=
    Nat.lt_of_lt_of_le (show 1 < 3 by decide) hcard
  have hpair :
      Exists fun left =>
        Membership.mem neighbors left /\ Exists fun right =>
          Membership.mem neighbors right /\ Ne left right :=
    Finset.one_lt_card.mp htwo
  let left : Fin n := Classical.choose hpair
  have hleft_pair :
      Membership.mem neighbors left /\ Exists fun right =>
        Membership.mem neighbors right /\ Ne left right :=
    Classical.choose_spec hpair
  let right : Fin n := Classical.choose hleft_pair.2
  have hright_pair :
      Membership.mem neighbors right /\ Ne left right :=
    Classical.choose_spec hleft_pair.2
  have hleft_mem' :
      Membership.mem (DegreePipeline.unitDistanceNeighborSet C center) left := by
    simpa [neighbors] using hleft_pair.1
  have hright_mem' :
      Membership.mem (DegreePipeline.unitDistanceNeighborSet C center) right := by
    simpa [neighbors] using hright_pair.1
  have hleft_prop :
      left != center /\ _root_.eucDist (C.pts left) (C.pts center) = 1 :=
    (DegreePipeline.mem_unitDistanceNeighborSet C center left).1 hleft_mem'
  have hright_prop :
      right != center /\ _root_.eucDist (C.pts right) (C.pts center) = 1 :=
    (DegreePipeline.mem_unitDistanceNeighborSet C center right).1 hright_mem'
  have hleft_unit : GraphBridge.UnitDistanceAdj C left center :=
    (GraphBridge.unitDistanceAdj_iff C left center).2 hleft_prop.2
  have hright_unit : GraphBridge.UnitDistanceAdj C right center :=
    (GraphBridge.unitDistanceAdj_iff C right center).2 hright_prop.2
  exact
    { left := left
      center := center
      right := right
      left_adj := ((CanonicalGraph C).adj_iff_unitDistanceAdj left center).2 hleft_unit
      right_adj := ((CanonicalGraph C).adj_iff_unitDistanceAdj right center).2 hright_unit
      endpoints_ne := hright_pair.2 }

/-- The positive selected-topology local angle construction.  Every classified
selected boundary slot receives an actual unit-separated angle triple centered
at the corresponding selected boundary vertex. -/
def selectedTopologyLocalAngleFamiliesOfMinimalFailure
    {C : _root_.UDConfig n}
    (topology : ActualSelectedTopologyData C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toOuterBoundaryCore.outerCycle.length -> Prop) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies
      (selectedClassificationOfMinimalFailure topology hmin longArc) where
  degree3 := fun i _ =>
    unitSeparatedAngleAtVertexOfMinimalFailure hmin
      (topology.toOuterBoundaryCore.outerCycle.vertex i.1)
  degree4 := fun i _ =>
    unitSeparatedAngleAtVertexOfMinimalFailure hmin
      (topology.toOuterBoundaryCore.outerCycle.vertex i.1)
  degree5 := fun i _ =>
    unitSeparatedAngleAtVertexOfMinimalFailure hmin
      (topology.toOuterBoundaryCore.outerCycle.vertex i.1)
  degree6 := fun i _ =>
    unitSeparatedAngleAtVertexOfMinimalFailure hmin
      (topology.toOuterBoundaryCore.outerCycle.vertex i.1)
  nontriangle := fun i _ =>
    unitSeparatedAngleAtVertexOfMinimalFailure hmin
      (topology.toOuterBoundaryCore.outerCycle.vertex i.1)
  longArc := fun i _ =>
    unitSeparatedAngleAtVertexOfMinimalFailure hmin
      (topology.toOuterBoundaryCore.outerCycle.vertex i.1)

/-- The generated selected-local accounted angle mass is nonnegative. -/
theorem selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_nonnegative
    {C : _root_.UDConfig n}
    (topology : ActualSelectedTopologyData C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toOuterBoundaryCore.outerCycle.length -> Prop) :
    0 <=
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        topology hmin longArc).accountedAngleSum :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_nonnegative
    (selectedTopologyLocalAngleFamiliesOfMinimalFailure
      topology hmin longArc)

/-- A concrete boundary classification is determined, up to proof
irrelevance, by its long-arc predicate once a replacement degree lower bound is
available. -/
theorem outerBoundaryClassificationInputs_eq_ofLongArcPredicate
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {P : OuterBoundaryCore G}
    (D : BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P)
    (degree_ge_three :
      forall k : Fin P.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree G
          (P.outerCycle.vertex k)) :
    D =
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.ofLongArcPredicate
        degree_ge_three D.longArc := by
  cases D with
  | mk degree_ge_three' longArc longArcDecidable =>
      simp [BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.ofLongArcPredicate]
      funext k
      exact Subsingleton.elim _ _

/-- Concrete E12 angle data attached to an actual selected outer-boundary
datum. -/
structure SelectedOuterBoundaryAngleSource (C : _root_.UDConfig n) where
  topology : ActualSelectedTopologyData C
  classification :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toOuterBoundaryCore
  angleWitness : OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification

namespace SelectedOuterBoundaryAngleSource

variable {C : _root_.UDConfig n}

def core (S : SelectedOuterBoundaryAngleSource C) :
    OuterBoundaryCore (CanonicalGraph C) :=
  S.topology.toOuterBoundaryCore

/-- Build the selected angle source from the existing W13 actual
outer-boundary angle package. -/
def ofActualOuterBoundaryAngleData
    (D : OuterBoundaryInstantiationW13.ActualOuterBoundaryAngleData
      (CanonicalGraph C)) :
    SelectedOuterBoundaryAngleSource C :=
  let topology :=
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
      D.core
  have hcore : topology.toOuterBoundaryCore = D.core :=
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore_toOuterBoundaryCore
      D.core
  let package (P : OuterBoundaryCore (CanonicalGraph C)) :=
    Sigma fun classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P =>
        OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification
  let anglePackage : package topology.toOuterBoundaryCore :=
    hcore.symm ▸ (Sigma.mk D.classification D.angleWitness : package D.core)
  { topology := topology
    classification := anglePackage.1
    angleWitness := anglePackage.2 }

/-- The actual per-class angle realization supplied by the selected boundary
and its concrete unit-separated witnesses. -/
def outerBoundaryAngleRealization
    (S : SelectedOuterBoundaryAngleSource C) :
    BoundaryAngleRealization.OuterBoundaryAngleRealization :=
  OuterBoundaryAngleW12.outerBoundaryAngleRealization S.angleWitness

@[simp]
theorem outerBoundaryAngleRealization_counts
    (S : SelectedOuterBoundaryAngleSource C) :
    S.outerBoundaryAngleRealization.counts = S.classification.counts :=
  rfl

@[simp]
theorem outerBoundaryAngleRealization_geometricAngleSum
    (S : SelectedOuterBoundaryAngleSource C) :
    S.outerBoundaryAngleRealization.geometricAngleSum =
      S.angleWitness.geometricAngleSum :=
  rfl

/-- The E12 angle lower bound, obtained directly from the concrete selected
boundary witnesses. -/
theorem angleLowerBound
    (S : SelectedOuterBoundaryAngleSource C) :
    S.classification.counts.AngleLowerBound :=
  OuterBoundaryAngleW12.angleLowerBound S.angleWitness

/-- The W12 honest package for consumers that want the selected core bundled
with its classification and witnesses. -/
def toHonestOuterBoundaryAngleData
    (S : SelectedOuterBoundaryAngleSource C) :
    OuterBoundaryAngleW12.HonestOuterBoundaryAngleData S.core where
  classification := S.classification
  angleWitness := S.angleWitness

/-- Compatibility projection to the W13 actual-angle package. -/
def toActualOuterBoundaryAngleData
    (S : SelectedOuterBoundaryAngleSource C) :
    OuterBoundaryInstantiationW13.ActualOuterBoundaryAngleData
      (CanonicalGraph C) where
  core := S.core
  classification := S.classification
  angleWitness := S.angleWitness

@[simp]
theorem toActualOuterBoundaryAngleData_angleRealization
    (S : SelectedOuterBoundaryAngleSource C) :
    S.toActualOuterBoundaryAngleData.angleRealization =
      S.outerBoundaryAngleRealization :=
  rfl

/-- The realized-angle closure payload, retaining the actual realization
rather than only the aggregate angle inequalities. -/
def outerBoundaryRealizedAngleData
    (S : SelectedOuterBoundaryAngleSource C) :
    OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{0}
      (CanonicalGraph C) :=
  OuterBoundaryAngleW12.outerBoundaryRealizedAngleData S.angleWitness

@[simp]
theorem outerBoundaryRealizedAngleData_counts
    (S : SelectedOuterBoundaryAngleSource C) :
    S.outerBoundaryRealizedAngleData.counts = S.classification.counts :=
  rfl

theorem boundaryAngleCountInequality
    (S : SelectedOuterBoundaryAngleSource C) :
    S.classification.counts.d5 + 2 * S.classification.counts.d6 +
        S.classification.counts.b + S.classification.counts.B + 6 <=
      S.classification.counts.d3 :=
  OuterBoundaryAngleW12.boundaryAngleCountInequality S.angleWitness

theorem boundaryNegativeCountInequality
    (S : SelectedOuterBoundaryAngleSource C) :
    S.classification.counts.negativeCount +
        S.classification.counts.B + 6 <= S.classification.counts.d3 :=
  OuterBoundaryAngleW12.boundaryNegativeCountInequality S.angleWitness

/-- The selected topology repackaged in the concrete missing-topology format
used by the refined face-data route. -/
def missingTopologyFacts
    (S : SelectedOuterBoundaryAngleSource C) :
    JordanBoundaryConcrete.MissingTopologyFacts C :=
  S.topology.toMissingTopologyFacts

@[simp]
theorem missingTopologyFacts_toCore
    (S : SelectedOuterBoundaryAngleSource C) :
    S.missingTopologyFacts.toCore = S.core := by
  rfl

/-- The carried classification, reindexed along the missing-topology
projection of the same selected outer-boundary core. -/
def classificationForMissingTopologyFacts
    (S : SelectedOuterBoundaryAngleSource C) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      S.missingTopologyFacts.toCore := by
  change
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      S.core
  exact S.classification

/-- The carried angle witnesses over the reindexed selected classification. -/
def angleWitnessForMissingTopologyFacts
    (S : SelectedOuterBoundaryAngleSource C) :
    OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
      S.classificationForMissingTopologyFacts := by
  change OuterBoundaryAngleW12.UnitSeparatedAngleFamilies S.classification
  exact S.angleWitness

/-- Under minimal failure, the selected angle row's own classification is the
canonical generated classification for its carried long-arc predicate. -/
theorem classification_eq_selectedClassificationOfMinimalFailure
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    S.classification =
      selectedClassificationOfMinimalFailure
        S.topology hmin S.classification.longArc := by
  exact
    outerBoundaryClassificationInputs_eq_ofLongArcPredicate
      S.classification
      (fun k =>
        ambientDegree_ge_three_of_minimalFailure C hmin
          (S.topology.toOuterBoundaryCore.outerCycle.vertex k))

/-- The concrete generated-classification angle witness obtained from an
existing selected outer-boundary angle source by choosing its carried long-arc
predicate. -/
def angleWitnessForMinimalFailureSelectedClassification
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
      (selectedClassificationOfMinimalFailure
        S.topology hmin S.classification.longArc) := by
  rw [← classification_eq_selectedClassificationOfMinimalFailure S hmin]
  exact S.angleWitness

/-- The same generated-classification equality after projecting the selected
topology row to `MissingTopologyFacts`, the shape consumed by
`PlanarBoundaryFaceData.ofMinimalFailureSelectedClassification`. -/
theorem classificationForMissingTopologyFacts_eq_selectedClassificationOfMinimalFailure
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    S.classificationForMissingTopologyFacts =
      PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        S.missingTopologyFacts hmin S.classificationForMissingTopologyFacts.longArc := by
  exact
    outerBoundaryClassificationInputs_eq_ofLongArcPredicate
      S.classificationForMissingTopologyFacts
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedBoundary_degree_ge_three_of_minimalFailure
        S.missingTopologyFacts hmin)

/-- The concrete generated-classification angle witness in the refined
face-data namespace.  This is the exact remaining angle premise of
`PlanarBoundaryFaceData.ofMinimalFailureSelectedClassification`, supplied from
the existing selected outer-boundary angle row. -/
def angleWitnessForMissingTopologyMinimalFailureSelectedClassification
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        S.missingTopologyFacts hmin S.classificationForMissingTopologyFacts.longArc) := by
  rw [← classificationForMissingTopologyFacts_eq_selectedClassificationOfMinimalFailure
    S hmin]
  exact S.angleWitnessForMissingTopologyFacts

/-- A selected outer-boundary angle source directly inhabits the exact
generated-classification angle-family premise used by
`PlanarBoundaryFaceDataRefinement`. -/
theorem nonempty_angleWitnessForMissingTopologyMinimalFailureSelectedClassification
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty
      (OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          S.missingTopologyFacts hmin
          S.classificationForMissingTopologyFacts.longArc)) :=
  Nonempty.intro
    (S.angleWitnessForMissingTopologyMinimalFailureSelectedClassification hmin)

/-- The W34 selected angle source closes the topology, degree, long-arc, and
unit-separated angle premises of the refined face-data constructor.  The
subpolygon family remains explicit. -/
def toPlanarBoundaryFaceData
    (S : SelectedOuterBoundaryAngleSource C)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u} C :=
  PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofClassification
    S.missingTopologyFacts S.classificationForMissingTopologyFacts
    S.angleWitnessForMissingTopologyFacts Subpolygon subpolygonData

/-- Build refined face data through the minimal-failure selected-classification
constructor.  The generated `UnitSeparatedAngleFamilies` premise is supplied by
`angleWitnessForMissingTopologyMinimalFailureSelectedClassification`; only the
subpolygon data remains explicit. -/
def toPlanarBoundaryFaceDataOfMinimalFailure
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u} C :=
  PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofMinimalFailureSelectedClassification
    S.missingTopologyFacts hmin S.classificationForMissingTopologyFacts.longArc
    (S.angleWitnessForMissingTopologyMinimalFailureSelectedClassification hmin)
    Subpolygon subpolygonData

/-- Refined planar-boundary face data whose subpolygon package is the selected
outer face supplied by `SubpolygonSelectedGeometrySourceW34`.

Thus the remaining S3 input is just the live selected outer-boundary angle row;
the selected outer-face realization and subpolygon data are generated here.
-/
def toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{0, 0} C :=
  SubpolygonSelectedGeometrySourceW34.planarBoundaryFaceDataOfMinimalFailureSelectedClassification
    S.missingTopologyFacts hmin S.classificationForMissingTopologyFacts.longArc
    (S.angleWitnessForMissingTopologyMinimalFailureSelectedClassification hmin)

@[simp]
theorem toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure_topology
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (S.toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure hmin).topology =
      S.missingTopologyFacts :=
  rfl

@[simp]
theorem toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure_outerAngleCounts
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (S.toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure
        hmin).outerAngleBounds.counts =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        S.missingTopologyFacts hmin
        S.classificationForMissingTopologyFacts.longArc).counts :=
  rfl

theorem planarBoundaryFaceData_nonempty_of_selectedOuterBoundaryAngleSource_minimalFailure
    (S : SelectedOuterBoundaryAngleSource C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{0, 0} C) :=
  Nonempty.intro
    (S.toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure hmin)

@[simp]
theorem toPlanarBoundaryFaceData_topology
    (S : SelectedOuterBoundaryAngleSource C)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (S.toPlanarBoundaryFaceData Subpolygon subpolygonData).topology =
      S.missingTopologyFacts :=
  rfl

theorem planarBoundaryFaceData_nonempty_of_selectedOuterBoundaryAngleSource
    (S : SelectedOuterBoundaryAngleSource C)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    Nonempty
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u, 0} C) :=
  Nonempty.intro
    (S.toPlanarBoundaryFaceData Subpolygon subpolygonData)

end SelectedOuterBoundaryAngleSource

/-- Minimal-failure rows of the actual selected-boundary angle source. -/
def MinimalFailureSelectedOuterBoundaryAngleRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      SelectedOuterBoundaryAngleSource C

/-- Minimal-failure refined face-data rows generated from the selected
outer-boundary angle source and the selected outer-face W34 subpolygon source.
-/
def MinimalFailureSelectedOuterFacePlanarBoundaryFaceDataRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{0, 0} C

/-- Minimal-failure rows of actual per-class angle realizations. -/
def MinimalFailureOuterBoundaryAngleRealizationRows : Type :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      BoundaryAngleRealization.OuterBoundaryAngleRealization

/-- Minimal-failure rows of the existing W13 actual outer-boundary angle
package. -/
def MinimalFailureActualOuterBoundaryAngleDataRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      OuterBoundaryInstantiationW13.ActualOuterBoundaryAngleData
        (CanonicalGraph C)

/-- Minimal-failure rows of the E12 angle lower-bound field for a selected
angle-source row family. -/
def MinimalFailureOuterBoundaryAngleLowerBoundRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      (rows C hmin).classification.counts.AngleLowerBound

def outerBoundaryAngleRealizationRowsOfSelectedRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    MinimalFailureOuterBoundaryAngleRealizationRows :=
  fun C hmin => (rows C hmin).outerBoundaryAngleRealization

def angleLowerBoundRowsOfSelectedRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    MinimalFailureOuterBoundaryAngleLowerBoundRows rows :=
  fun C hmin => (rows C hmin).angleLowerBound

def selectedOuterFacePlanarBoundaryFaceDataRowsOfSelectedRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    MinimalFailureSelectedOuterFacePlanarBoundaryFaceDataRows :=
  fun C hmin =>
    (rows C hmin).toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure
      hmin

theorem nonempty_selectedOuterFacePlanarBoundaryFaceDataRows_of_selectedRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    Nonempty MinimalFailureSelectedOuterFacePlanarBoundaryFaceDataRows :=
  Nonempty.intro
    (selectedOuterFacePlanarBoundaryFaceDataRowsOfSelectedRows rows)

/-- Classification and angle witnesses over a fixed selected-topology row
family.  This is the source part that remains after W33 supplies topology
rows. -/
structure SelectedTopologyAngleWitnessRows
    (topology : MinimalFailureActualSelectedTopologyRows) : Type 1 where
  classification :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
          ((topology C hmin).toOuterBoundaryCore)
  angleWitness :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
          (classification C hmin)

/-- The selected long-arc predicate carried by concrete classification rows
over the selected topology. -/
def selectedLongArcRowsOfTopologyAngleWitnessRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (angleRows : SelectedTopologyAngleWitnessRows topology) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) ->
          Prop :=
  fun C hmin =>
    (angleRows.classification C hmin).longArc

/-- With the long-arc predicate derived from the concrete classification row,
the generated minimal-failure classification is propositionally the same
classification. -/
theorem selectedClassificationOfMinimalFailure_eq_classification_of_topologyAngleWitnessRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (angleRows : SelectedTopologyAngleWitnessRows topology)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    selectedClassificationOfMinimalFailure
        (topology C hmin) hmin
        (selectedLongArcRowsOfTopologyAngleWitnessRows angleRows C hmin) =
      angleRows.classification C hmin := by
  change
    selectedClassificationOfMinimalFailure
        (topology C hmin) hmin
        (angleRows.classification C hmin).longArc =
      angleRows.classification C hmin
  symm
  exact
    outerBoundaryClassificationInputs_eq_ofLongArcPredicate
      (angleRows.classification C hmin)
      (fun k =>
        ambientDegree_ge_three_of_minimalFailure C hmin
          ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k))

/-- Build actual selected-boundary angle rows from selected topology rows and
concrete classification/angle-witness rows over those same selected
boundaries. -/
def selectedOuterBoundaryAngleRowsOfTopologyAngleWitnessRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (angleRows : SelectedTopologyAngleWitnessRows topology) :
    MinimalFailureSelectedOuterBoundaryAngleRows :=
  fun C hmin =>
    { topology := topology C hmin
      classification := angleRows.classification C hmin
      angleWitness := angleRows.angleWitness C hmin }

/-- Minimal-failure selected angle rows projected from W13 actual
outer-boundary angle rows. -/
def selectedOuterBoundaryAngleRowsOfActualOuterBoundaryAngleDataRows
    (rows : MinimalFailureActualOuterBoundaryAngleDataRows) :
    MinimalFailureSelectedOuterBoundaryAngleRows :=
  fun C hmin =>
    SelectedOuterBoundaryAngleSource.ofActualOuterBoundaryAngleData
      (rows C hmin)

/-- Minimal-failure W13 actual-angle rows projected from selected angle rows. -/
def actualOuterBoundaryAngleDataRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    MinimalFailureActualOuterBoundaryAngleDataRows :=
  fun C hmin =>
    (rows C hmin).toActualOuterBoundaryAngleData

def selectedTopologyRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => (rows C hmin).topology

def selectedLongArcRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin (((selectedTopologyRowsOfSelectedOuterBoundaryAngleRows rows)
          C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop :=
  fun C hmin =>
    (rows C hmin).classification.longArc

def selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
          (selectedClassificationOfMinimalFailure
            ((selectedTopologyRowsOfSelectedOuterBoundaryAngleRows rows) C hmin)
            hmin
            (selectedLongArcRowsOfSelectedOuterBoundaryAngleRows rows C hmin)) :=
  fun C hmin =>
    (rows C hmin).angleWitnessForMinimalFailureSelectedClassification hmin

theorem exists_selectedTopologyLocalEuclideanAngles_of_selectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
      Exists fun longArc :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop =>
        Nonempty
          (forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
                (selectedClassificationOfMinimalFailure
                  (topology C hmin) hmin (longArc C hmin))) :=
  ⟨selectedTopologyRowsOfSelectedOuterBoundaryAngleRows rows,
    selectedLongArcRowsOfSelectedOuterBoundaryAngleRows rows,
    Nonempty.intro
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        rows)⟩

theorem exists_selectedTopologyLocalEuclideanAngles_of_actualOuterBoundaryAngleDataRows
    (rows : MinimalFailureActualOuterBoundaryAngleDataRows) :
    Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
      Exists fun longArc :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop =>
        Nonempty
          (forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
                (selectedClassificationOfMinimalFailure
                  (topology C hmin) hmin (longArc C hmin))) :=
  exists_selectedTopologyLocalEuclideanAngles_of_selectedOuterBoundaryAngleRows
    (selectedOuterBoundaryAngleRowsOfActualOuterBoundaryAngleDataRows rows)

/-- The selected topology rows projected to the `MissingTopologyFacts` shape
consumed by `PlanarBoundaryFaceDataRefinement`. -/
def selectedMissingTopologyRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        JordanBoundaryConcrete.MissingTopologyFacts.{0} C :=
  fun C hmin => (rows C hmin).missingTopologyFacts

/-- The long-arc predicates carried by selected angle rows, reindexed over the
same `MissingTopologyFacts` projection. -/
def selectedMissingLongArcRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin (((selectedMissingTopologyRowsOfSelectedOuterBoundaryAngleRows rows)
          C hmin).toCore.outerCycle.length) -> Prop :=
  fun C hmin =>
    (rows C hmin).classificationForMissingTopologyFacts.longArc

/-- Existing selected outer-boundary angle rows supply the exact generated
classification angle-family premise used by the refined face-data constructor,
after projecting the selected topology to `MissingTopologyFacts`. -/
def selectedMissingTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
          (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
            ((selectedMissingTopologyRowsOfSelectedOuterBoundaryAngleRows rows)
              C hmin)
            hmin
            (selectedMissingLongArcRowsOfSelectedOuterBoundaryAngleRows rows
              C hmin)) :=
  fun C hmin =>
    (rows C hmin).angleWitnessForMissingTopologyMinimalFailureSelectedClassification
      hmin

/-- Exact reduction of the live refined face-data angle premise to selected
outer-boundary angle rows. -/
theorem exists_selectedMissingTopologyLocalEuclideanAngles_of_selectedOuterBoundaryAngleRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    Exists fun topology :
      forall {n : Nat} (C : _root_.UDConfig n)
        (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          JordanBoundaryConcrete.MissingTopologyFacts.{0} C =>
      Exists fun longArc :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Fin ((topology C hmin).toCore.outerCycle.length) -> Prop =>
        Nonempty
          (forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              OuterBoundaryAngleW12.UnitSeparatedAngleFamilies.{0}
                (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
                  (topology C hmin) hmin (longArc C hmin))) :=
  Exists.intro
    (selectedMissingTopologyRowsOfSelectedOuterBoundaryAngleRows rows)
    (Exists.intro
      (selectedMissingLongArcRowsOfSelectedOuterBoundaryAngleRows rows)
      (Nonempty.intro
        (selectedMissingTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
          rows)))

/-- Exact reduction of the live refined face-data angle premise to the existing
W13 actual outer-boundary angle-data row. -/
theorem exists_selectedMissingTopologyLocalEuclideanAngles_of_actualOuterBoundaryAngleDataRows
    (rows : MinimalFailureActualOuterBoundaryAngleDataRows) :
    Exists fun topology :
      forall {n : Nat} (C : _root_.UDConfig n)
        (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          JordanBoundaryConcrete.MissingTopologyFacts.{0} C =>
      Exists fun longArc :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Fin ((topology C hmin).toCore.outerCycle.length) -> Prop =>
        Nonempty
          (forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              OuterBoundaryAngleW12.UnitSeparatedAngleFamilies.{0}
                (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
                  (topology C hmin) hmin (longArc C hmin))) :=
  exists_selectedMissingTopologyLocalEuclideanAngles_of_selectedOuterBoundaryAngleRows
    (selectedOuterBoundaryAngleRowsOfActualOuterBoundaryAngleDataRows rows)

/-- Minimal-failure W13 actual-angle rows built from selected topology rows and
concrete local Euclidean angle witnesses over the same selected boundaries. -/
def actualOuterBoundaryAngleDataRowsOfTopologyAngleWitnessRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (angleRows : SelectedTopologyAngleWitnessRows topology) :
    MinimalFailureActualOuterBoundaryAngleDataRows :=
  actualOuterBoundaryAngleDataRowsOfSelectedOuterBoundaryAngleRows
    (selectedOuterBoundaryAngleRowsOfTopologyAngleWitnessRows angleRows)

/-- Exact reduction after selected topology and minimality: the remaining
geometric fact is the concrete W10/W12 unit-separated local angle family for
the generated classification. -/
def actualOuterBoundaryAngleDataRowsOfSelectedTopologyLocalEuclideanAngles
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (angleWitness :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
            (selectedClassificationOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin))) :
    MinimalFailureActualOuterBoundaryAngleDataRows :=
  fun C hmin =>
    { core := (topology C hmin).toOuterBoundaryCore
      classification :=
        selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)
      angleWitness := angleWitness C hmin }

/-- Local Euclidean angle geometry over a selected topology row family,
before the full W10 angle-family package is reassembled.  The fields are the
actual unit-separated angle triples indexed by the concrete boundary classes,
plus the single polygon angle-accounting comparison for their accounted sum. -/
structure SelectedTopologyLocalAngleGeometryRows
    (topology : MinimalFailureActualSelectedTopologyRows) : Type 1 where
  longArc :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop
  localAngles :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies
          (selectedClassificationOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin))
  accounted_le_polygon :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (localAngles C hmin).accountedAngleSum <=
          (selectedClassificationOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).counts.polygonAngleSum

def simpleOuterPolygonInteriorAngleSum
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) : Real :=
  Real.pi * ((P.outerCycle.length : Real) - 2)

theorem simpleOuterPolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) :
    simpleOuterPolygonInteriorAngleSum P =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum P :=
  rfl

/-- The simple-polygon interior-angle sum is nonnegative once the selected
boundary has at least two vertices. -/
theorem simpleOuterPolygonInteriorAngleSum_nonnegative_of_length_ge_two
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (hlen : 2 <= P.outerCycle.length) :
    0 <= simpleOuterPolygonInteriorAngleSum P := by
  unfold simpleOuterPolygonInteriorAngleSum
  have hlength : (2 : Real) <= (P.outerCycle.length : Real) := by
    exact_mod_cast hlen
  exact mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hlength)

/-- Finite aggregation of triangle angle sums.  The per-triangle equality is
the only geometric input; this lemma just adds those rows. -/
theorem finiteTriangleAngleSum_eq_card_mul_pi
    {Triangle : Type*} [Fintype Triangle]
    (triangleAngle : Triangle -> Fin 3 -> Real)
    (triangleAngleSum_eq_pi :
      forall T : Triangle,
        Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T) =
          Real.pi) :
    Finset.sum Finset.univ
        (fun T : Triangle =>
          Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T)) =
      (Fintype.card Triangle : Real) * Real.pi := by
  calc
    Finset.sum Finset.univ
        (fun T : Triangle =>
          Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T)) =
        Finset.sum (Finset.univ : Finset Triangle) (fun _ => Real.pi) := by
          exact
            Finset.sum_congr rfl
              (fun T _ => triangleAngleSum_eq_pi T)
    _ = (Fintype.card Triangle : Real) * Real.pi := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Finite triangulation angle aggregation in the boundary-cycle normalization:
if there are exactly `length - 2` triangles and each triangle has angle sum
`π`, then the total triangle angle mass is the local simple-polygon value. -/
theorem finiteTriangleAngleSum_eq_simpleOuterPolygonInteriorAngleSum
    {Triangle : Type*} [Fintype Triangle]
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (boundaryLength_ge_two : 2 <= P.outerCycle.length)
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = P.outerCycle.length - 2)
    (triangleAngle : Triangle -> Fin 3 -> Real)
    (triangleAngleSum_eq_pi :
      forall T : Triangle,
        Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T) =
          Real.pi) :
    Finset.sum Finset.univ
        (fun T : Triangle =>
          Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T)) =
      simpleOuterPolygonInteriorAngleSum P := by
  have hcount :
      (Fintype.card Triangle : Real) =
        ((P.outerCycle.length - 2 : Nat) : Real) := by
    exact_mod_cast triangleCount_eq_boundaryLength_sub_two
  rw [finiteTriangleAngleSum_eq_card_mul_pi
    triangleAngle triangleAngleSum_eq_pi]
  rw [simpleOuterPolygonInteriorAngleSum, hcount,
    Nat.cast_sub boundaryLength_ge_two]
  ring

/-- The uniform `pi / 3` corner model has total angle `pi` on a three-corner
triangle row. -/
theorem constantPiDivThreeTriangleAngleSum_eq_pi :
    Finset.sum (Finset.univ : Finset (Fin 3))
        (fun _ : Fin 3 => Real.pi / 3) =
      Real.pi := by
  norm_num [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Each corner of the uniform `pi / 3` triangle-angle model is
nonnegative. -/
theorem constantPiDivThreeTriangleAngle_nonnegative :
    0 <= Real.pi / 3 := by
  linarith [Real.pi_pos]

/-- Selected S3 accounting lemma: if every concrete local Euclidean angle
mass generated from minimality fits into an explicit classified sector budget,
and those budgets fit in the selected outer cycle's simple-polygon angle sum,
then the local rows provide the polygon comparison needed by
`SelectedTopologyLocalAngleGeometryRows` and hence
`ActualSelectedBoundaryEuclideanAngleRows`. -/
theorem selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_polygon_of_angleMassBudgets
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (degree3Budget :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree3Indices -> Real)
    (degree4Budget :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree4Indices -> Real)
    (degree5Budget :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree5Indices -> Real)
    (degree6Budget :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree6Indices -> Real)
    (nontriangleBudget :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices ->
          Real)
    (longArcBudget :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).longArcIndices -> Real)
    (hdegree3 :
      forall i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree3 i) <=
          degree3Budget i)
    (hdegree4 :
      forall i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree4 i) <=
          degree4Budget i)
    (hdegree5 :
      forall i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree5 i) <=
          degree5Budget i)
    (hdegree6 :
      forall i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree6 i) <=
          degree6Budget i)
    (hnontriangle :
      forall i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).nontriangle i) <=
          nontriangleBudget i)
    (hlongArc :
      forall i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).longArc i) <=
          longArcBudget i)
    (hbudget :
      Finset.sum Finset.univ degree3Budget +
          Finset.sum Finset.univ degree4Budget +
          Finset.sum Finset.univ degree5Budget +
          Finset.sum Finset.univ degree6Budget +
          Finset.sum Finset.univ nontriangleBudget +
          Finset.sum Finset.univ longArcBudget <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore)) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).counts.polygonAngleSum :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_polygon_of_angleMassBudgets
    (selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin))
    degree3Budget degree4Budget degree5Budget degree6Budget
    nontriangleBudget longArcBudget hdegree3 hdegree4 hdegree5 hdegree6
    hnontriangle hlongArc
    (by
      change
        Finset.sum Finset.univ degree3Budget +
            Finset.sum Finset.univ degree4Budget +
            Finset.sum Finset.univ degree5Budget +
            Finset.sum Finset.univ degree6Budget +
            Finset.sum Finset.univ nontriangleBudget +
            Finset.sum Finset.univ longArcBudget <=
          Real.pi *
            ((((topology C hmin).toOuterBoundaryCore).outerCycle.length :
              Real) - 2) at hbudget
      exact hbudget)

/-- Concrete angle-mass budgets for the generated selected-local rows.  These
rows isolate the accounting work from the outer-face sector-order geometry:
each classified local angle is bounded by an explicit budget, and the six
budget sums fit in the selected simple-polygon angle sum. -/
structure SelectedTopologyLocalAngleMassBudgetRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  degree3Budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices -> Real
  degree4Budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices -> Real
  degree5Budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices -> Real
  degree6Budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices -> Real
  nontriangleBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices ->
            Real
  longArcBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices -> Real
  degree3_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree3 i) <=
          degree3Budget C hmin i
  degree4_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree4 i) <=
          degree4Budget C hmin i
  degree5_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree5 i) <=
          degree5Budget C hmin i
  degree6_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).degree6 i) <=
          degree6Budget C hmin i
  nontriangle_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).nontriangle i) <=
          nontriangleBudget C hmin i
  longArc_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).longArc i) <=
          longArcBudget C hmin i
  budgetSum_le_simpleOuterPolygonInteriorAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (degree3Budget C hmin) +
            Finset.sum Finset.univ (degree4Budget C hmin) +
            Finset.sum Finset.univ (degree5Budget C hmin) +
            Finset.sum Finset.univ (degree6Budget C hmin) +
            Finset.sum Finset.univ (nontriangleBudget C hmin) +
            Finset.sum Finset.univ (longArcBudget C hmin) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)

/-- The exact local-angle mass budgets, obtained by taking every budget to be
the value of the generated local unit-separated angle row itself, sum to the
generated accounted local angle mass. -/
theorem localAngleMassExactBudgetSum_eq_accountedAngleSum
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {P : OuterBoundaryCore G}
    {D : BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P}
    (L :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies
        D) :
    Finset.sum Finset.univ
        (fun i : D.degree3Indices =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree3 i)) +
      Finset.sum Finset.univ
        (fun i : D.degree4Indices =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree4 i)) +
      Finset.sum Finset.univ
        (fun i : D.degree5Indices =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree5 i)) +
      Finset.sum Finset.univ
        (fun i : D.degree6Indices =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree6 i)) +
      Finset.sum Finset.univ
        (fun i : D.nontriangleEdgeIndices =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.nontriangle i)) +
      Finset.sum Finset.univ
        (fun i : D.longArcIndices =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.longArc i)) =
        L.accountedAngleSum := by
  classical
  unfold
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum
  rw [Fintype.sum_equiv
    (BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin D).symm
    (fun i : Fin D.counts.d3 =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree3
          ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
            D).symm i)))
    (fun i : D.degree3Indices =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree3 i))
    (fun _ => rfl)]
  rw [Fintype.sum_equiv
    (BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin D).symm
    (fun i : Fin D.counts.d4 =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree4
          ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
            D).symm i)))
    (fun i : D.degree4Indices =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree4 i))
    (fun _ => rfl)]
  rw [Fintype.sum_equiv
    (BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin D).symm
    (fun i : Fin D.counts.d5 =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree5
          ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
            D).symm i)))
    (fun i : D.degree5Indices =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree5 i))
    (fun _ => rfl)]
  rw [Fintype.sum_equiv
    (BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin D).symm
    (fun i : Fin D.counts.d6 =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree6
          ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
            D).symm i)))
    (fun i : D.degree6Indices =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.degree6 i))
    (fun _ => rfl)]
  rw [Fintype.sum_equiv
    (BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
      D).symm
    (fun i : Fin D.counts.b =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.nontriangle
          ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
            D).symm i)))
    (fun i : D.nontriangleEdgeIndices =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.nontriangle i))
    (fun _ => rfl)]
  rw [Fintype.sum_equiv
    (BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin D).symm
    (fun i : Fin D.counts.B =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
        (L.longArc
          ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
            D).symm i)))
      (fun i : D.longArcIndices =>
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
          (L.longArc i))
      (fun _ => rfl)]

/-- Exact-budget constructor for the generated selected local angle rows.

This isolates the remaining geometric inequality for the budget route: after
choosing the selected topology and long-arc predicate, the generated accounted
angle mass must be bounded by the selected outer cycle's simple-polygon angle
sum. -/
def selectedTopologyLocalAngleMassBudgetRowsOfGeneratedAccountedAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleMassBudgetRows topology longArc where
  degree3Budget := fun C hmin i =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
      ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree3 i)
  degree4Budget := fun C hmin i =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
      ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree4 i)
  degree5Budget := fun C hmin i =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
      ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree5 i)
  degree6Budget := fun C hmin i =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
      ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree6 i)
  nontriangleBudget := fun C hmin i =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
      ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).nontriangle i)
  longArcBudget := fun C hmin i =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
      ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).longArc i)
  degree3_le_budget := fun _ _ _ => le_rfl
  degree4_le_budget := fun _ _ _ => le_rfl
  degree5_le_budget := fun _ _ _ => le_rfl
  degree6_le_budget := fun _ _ _ => le_rfl
  nontriangle_le_budget := fun _ _ _ => le_rfl
  longArc_le_budget := fun _ _ _ => le_rfl
  budgetSum_le_simpleOuterPolygonInteriorAngleSum := fun C hmin => by
    let D :=
      selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)
    let L :=
      selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)
    change
      Finset.sum Finset.univ
          (fun i : D.degree3Indices =>
            BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
              (L.degree3 i)) +
        Finset.sum Finset.univ
          (fun i : D.degree4Indices =>
            BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
              (L.degree4 i)) +
        Finset.sum Finset.univ
          (fun i : D.degree5Indices =>
            BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
              (L.degree5 i)) +
        Finset.sum Finset.univ
          (fun i : D.degree6Indices =>
            BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
              (L.degree6 i)) +
        Finset.sum Finset.univ
          (fun i : D.nontriangleEdgeIndices =>
            BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
              (L.nontriangle i)) +
        Finset.sum Finset.univ
          (fun i : D.longArcIndices =>
            BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
              (L.longArc i)) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)
    rw [localAngleMassExactBudgetSum_eq_accountedAngleSum L]
    exact accounted_le_simpleOuterPolygonInteriorAngleSum C hmin

theorem selectedTopologyLocalAngleMassBudgetRows_accountedAngleSum_le_polygon
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (budgetRows : SelectedTopologyLocalAngleMassBudgetRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).counts.polygonAngleSum :=
  selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_polygon_of_angleMassBudgets
    (topology := topology) (longArc := longArc) C hmin
    (budgetRows.degree3Budget C hmin)
    (budgetRows.degree4Budget C hmin)
    (budgetRows.degree5Budget C hmin)
    (budgetRows.degree6Budget C hmin)
    (budgetRows.nontriangleBudget C hmin)
    (budgetRows.longArcBudget C hmin)
    (budgetRows.degree3_le_budget C hmin)
    (budgetRows.degree4_le_budget C hmin)
    (budgetRows.degree5_le_budget C hmin)
    (budgetRows.degree6_le_budget C hmin)
    (budgetRows.nontriangle_le_budget C hmin)
    (budgetRows.longArc_le_budget C hmin)
    (budgetRows.budgetSum_le_simpleOuterPolygonInteriorAngleSum C hmin)

theorem selectedTopologyLocalAngleMassBudgetRows_accountedAngleSum_le_boundaryCycleAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (budgetRows : SelectedTopologyLocalAngleMassBudgetRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        Real.pi *
          (((topology C hmin).toOuterBoundaryCore.outerCycle.length : Real) -
            2) :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_boundaryCycleAngleSum_of_le_polygon
    (selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin))
    (selectedTopologyLocalAngleMassBudgetRows_accountedAngleSum_le_polygon
      (topology := topology) (longArc := longArc) budgetRows C hmin)

theorem selectedTopologyLocalAngleMassBudgetRows_accountedAngleSum_le_budgetSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (budgetRows : SelectedTopologyLocalAngleMassBudgetRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        Finset.sum Finset.univ (budgetRows.degree3Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.degree4Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.degree5Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.degree6Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.nontriangleBudget C hmin) +
          Finset.sum Finset.univ (budgetRows.longArcBudget C hmin) :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_sum_angleMassBudgets
    (selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin))
    (budgetRows.degree3Budget C hmin)
    (budgetRows.degree4Budget C hmin)
    (budgetRows.degree5Budget C hmin)
    (budgetRows.degree6Budget C hmin)
    (budgetRows.nontriangleBudget C hmin)
    (budgetRows.longArcBudget C hmin)
    (budgetRows.degree3_le_budget C hmin)
    (budgetRows.degree4_le_budget C hmin)
    (budgetRows.degree5_le_budget C hmin)
    (budgetRows.degree6_le_budget C hmin)
    (budgetRows.nontriangle_le_budget C hmin)
    (budgetRows.longArc_le_budget C hmin)

/--
The remaining geometric S3 theorem for the generated selected-local rows.

The field `localRows_le_orderedOuterFaceSectorSum` is the checked projection of
sector containment and disjointness: the concrete local angle rows account for
no more than the ordered outer-face sectors they occupy.  The final field is
the simple-polygon interior-angle bound for those sectors.  Accounting transfer
from this boundary-cycle form to classified counts stays in
`BoundaryCountingInstantiationW10`.
-/
structure SelectedTopologyLocalAngleOuterFaceSectorOrderRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real
  sectorAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        0 <= sectorAngle C hmin k
  localRows_le_orderedOuterFaceSectorSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
          Finset.sum Finset.univ (sectorAngle C hmin)
  orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (sectorAngle C hmin) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)

/-- A finite indicator identity: summing sector-assigned weights sector by
sector recovers the total weight. -/
theorem finiteSectorIndicatorSum_eq_total
    {Slot Sector : Type*} [Fintype Slot] [Fintype Sector]
    [DecidableEq Sector]
    (sectorOf : Slot -> Sector)
    (weight : Slot -> Real) :
    Finset.sum (Finset.univ : Finset Sector)
        (fun sector =>
          Finset.sum (Finset.univ : Finset Slot)
            (fun slot =>
              if sectorOf slot = sector then weight slot else 0)) =
      Finset.sum (Finset.univ : Finset Slot) weight := by
  classical
  calc
    Finset.sum (Finset.univ : Finset Sector)
        (fun sector =>
          Finset.sum (Finset.univ : Finset Slot)
            (fun slot =>
              if sectorOf slot = sector then weight slot else 0)) =
        Finset.sum (Finset.univ : Finset Slot)
          (fun slot =>
            Finset.sum (Finset.univ : Finset Sector)
              (fun sector =>
                if sectorOf slot = sector then weight slot else 0)) := by
      rw [Finset.sum_comm]
    _ = Finset.sum (Finset.univ : Finset Slot) weight := by
      refine Finset.sum_congr rfl ?_
      intro slot _hslot
      rw [Finset.sum_eq_single (sectorOf slot)]
      · simp
      · intro sector _hsector hne
        have hneq : Not (sectorOf slot = sector) := by
          exact fun h => hne h.symm
        simp [hneq]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ (sectorOf slot)))

/-- Two-level version of `finiteSectorIndicatorSum_eq_total`, convenient for
classified angle families indexed by a row and then by a local angle slot. -/
theorem finiteSectorIndicatorSum_two_eq_total
    {Row Slot Sector : Type*} [Fintype Row] [Fintype Slot]
    [Fintype Sector] [DecidableEq Sector]
    (sectorOf : Row -> Slot -> Sector)
    (weight : Row -> Slot -> Real) :
    Finset.sum (Finset.univ : Finset Sector)
        (fun sector =>
          Finset.sum (Finset.univ : Finset Row)
            (fun row =>
              Finset.sum (Finset.univ : Finset Slot)
                (fun slot =>
                  if sectorOf row slot = sector then
                    weight row slot
                  else
                    0))) =
      Finset.sum (Finset.univ : Finset Row)
        (fun row =>
          Finset.sum (Finset.univ : Finset Slot)
            (fun slot => weight row slot)) := by
  classical
  calc
    Finset.sum (Finset.univ : Finset Sector)
        (fun sector =>
          Finset.sum (Finset.univ : Finset Row)
            (fun row =>
              Finset.sum (Finset.univ : Finset Slot)
                (fun slot =>
                  if sectorOf row slot = sector then
                    weight row slot
                  else
                    0))) =
        Finset.sum (Finset.univ : Finset Row)
          (fun row =>
            Finset.sum (Finset.univ : Finset Sector)
              (fun sector =>
                Finset.sum (Finset.univ : Finset Slot)
                  (fun slot =>
                    if sectorOf row slot = sector then
                      weight row slot
                    else
                      0))) := by
      rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.univ : Finset Row)
          (fun row =>
            Finset.sum (Finset.univ : Finset Slot)
              (fun slot =>
                Finset.sum (Finset.univ : Finset Sector)
                  (fun sector =>
                    if sectorOf row slot = sector then
                      weight row slot
                    else
                      0))) := by
      refine Finset.sum_congr rfl ?_
      intro row _hrow
      rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.univ : Finset Row)
          (fun row =>
            Finset.sum (Finset.univ : Finset Slot)
              (fun slot => weight row slot)) := by
      refine Finset.sum_congr rfl ?_
      intro row _hrow
      refine Finset.sum_congr rfl ?_
      intro slot _hslot
      rw [Finset.sum_eq_single (sectorOf row slot)]
      · simp
      · intro sector _hsector hne
        have hneq : Not (sectorOf row slot = sector) := by
          exact fun h => hne h.symm
        simp [hneq]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ (sectorOf row slot)))

/-- Sector-aware generated local-angle rows.

Every generated unit-separated angle slot is assigned to a selected outer-face
sector and receives its own budget.  The `sectorLoad_le_sectorAngle` field is
pointwise in the selected sector: it says the sum of the budgets assigned to a
given sector fits in that sector's angle.  This is the S3 replacement surface
for aggregate generated-accounting bounds. -/
structure SelectedTopologyLocalAngleOuterFaceSectorContainmentRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real
  sectorAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        0 <= sectorAngle C hmin k
  degree3Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices ->
          Fin 2 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree4Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices ->
          Fin 3 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree5Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices ->
          Fin 4 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree6Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices ->
          Fin 5 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  nontriangleSector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices ->
          Fin 1 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  longArcSector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices ->
          Fin 1 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree3SlotBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices ->
          Fin 2 -> Real
  degree4SlotBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices ->
          Fin 3 -> Real
  degree5SlotBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices ->
          Fin 4 -> Real
  degree6SlotBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices ->
          Fin 5 -> Real
  nontriangleSlotBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices ->
          Fin 1 -> Real
  longArcSlotBudget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices ->
          Fin 1 -> Real
  degree3_slot_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (slot : Fin 2),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value <=
          degree3SlotBudget C hmin i slot
  degree4_slot_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (slot : Fin 3),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value <=
          degree4SlotBudget C hmin i slot
  degree5_slot_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (slot : Fin 4),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value <=
          degree5SlotBudget C hmin i slot
  degree6_slot_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (slot : Fin 5),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value <=
          degree6SlotBudget C hmin i slot
  nontriangle_slot_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin
          (longArc C hmin)).nontriangle i slot).value <=
          nontriangleSlotBudget C hmin i slot
  longArc_slot_le_budget :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArc i slot).value <=
          longArcSlotBudget C hmin i slot
  sectorLoad_le_sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 2))
                (fun slot =>
                  if degree3Sector C hmin i slot = k then
                    degree3SlotBudget C hmin i slot
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (fun slot =>
                  if degree4Sector C hmin i slot = k then
                    degree4SlotBudget C hmin i slot
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 4))
                (fun slot =>
                  if degree5Sector C hmin i slot = k then
                    degree5SlotBudget C hmin i slot
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 5))
                (fun slot =>
                  if degree6Sector C hmin i slot = k then
                    degree6SlotBudget C hmin i slot
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 1))
                (fun slot =>
                  if nontriangleSector C hmin i slot = k then
                    nontriangleSlotBudget C hmin i slot
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 1))
                (fun slot =>
                  if longArcSector C hmin i slot = k then
                    longArcSlotBudget C hmin i slot
                  else
                    0)) <=
          sectorAngle C hmin k
  sectorAngleSum_le_simplePolygonInteriorAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (sectorAngle C hmin) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)

/--
Actual boundary-neighbor sector rows for S3.

Each selected boundary index carries a concrete unit-separated sector angle
whose center is that boundary vertex, whose right side is its cyclic
successor, and whose left side is some boundary predecessor.  The generated
local angle slots are assigned to these real sectors, and the pointwise load
at each selected boundary sector is bounded by that sector's Euclidean angle.
-/
structure SelectedTopologyActualBoundaryNeighborSectorContainmentRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  boundarySector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) ->
          BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C)
  boundarySector_left_is_boundary_predecessor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Exists fun pred :
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) =>
          (boundarySector C hmin k).left =
              (topology C hmin).toOuterBoundaryCore.outerCycle.vertex pred /\
            (topology C hmin).toOuterBoundaryCore.outerCycle.next pred = k
  boundarySector_center_eq :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        (boundarySector C hmin k).center =
          (topology C hmin).toOuterBoundaryCore.outerCycle.vertex k
  boundarySector_right_eq :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        (boundarySector C hmin k).right =
          (topology C hmin).toOuterBoundaryCore.outerCycle.vertex
            ((topology C hmin).toOuterBoundaryCore.outerCycle.next k)
  degree3Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices ->
          Fin 2 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree4Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices ->
          Fin 3 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree5Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices ->
          Fin 4 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  degree6Sector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices ->
          Fin 5 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  nontriangleSector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices ->
          Fin 1 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  longArcSector :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices ->
          Fin 1 ->
            Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)
  sectorLoad_le_boundarySectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 2))
                (fun slot =>
                  if degree3Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree3 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (fun slot =>
                  if degree4Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree4 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 4))
                (fun slot =>
                  if degree5Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree5 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 5))
                (fun slot =>
                  if degree6Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree6 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 1))
                (fun slot =>
                  if nontriangleSector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).nontriangle i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 1))
                (fun slot =>
                  if longArcSector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).longArc i slot).value
                  else
                    0)) <=
          (boundarySector C hmin k).value
  boundarySectorAngleSum_le_simplePolygonInteriorAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ
            (fun k => (boundarySector C hmin k).value) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)

/-- The actual predecessor/current/successor sector at a selected boundary
index, sourced directly from the boundary-cycle witness and the nondegenerate
length row. -/
def actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C) :=
  BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
    ((topology C hmin).toOuterBoundaryCore)
    (boundaryLength_ge_three C hmin) k

theorem actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_left_is_boundary_predecessor
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    Exists fun pred :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) =>
      (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
          (topology := topology) boundaryLength_ge_three C hmin k).left =
          (topology C hmin).toOuterBoundaryCore.outerCycle.vertex pred /\
        (topology C hmin).toOuterBoundaryCore.outerCycle.next pred = k := by
  refine
    Exists.intro ((topology C hmin).toOuterBoundaryCore.outerCycle.prev k) ?_
  constructor
  · rfl
  · exact (topology C hmin).toOuterBoundaryCore.outerCycle.next_prev k

@[simp]
theorem actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_center_eq
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
        (topology := topology) boundaryLength_ge_three C hmin k).center =
      (topology C hmin).toOuterBoundaryCore.outerCycle.vertex k :=
  rfl

@[simp]
theorem actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_right_eq
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
        (topology := topology) boundaryLength_ge_three C hmin k).right =
      (topology C hmin).toOuterBoundaryCore.outerCycle.vertex
        ((topology C hmin).toOuterBoundaryCore.outerCycle.next k) :=
  rfl

/-- The same-index actual boundary-neighbour sectors are exactly W10's
canonical predecessor/current/successor simple-polygon interior-angle sectors
after summing over the selected outer boundary. -/
theorem actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Finset.sum (Finset.univ :
        Finset (Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)))
        (fun k =>
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value) =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore) := by
  change
    Finset.sum (Finset.univ :
        Finset (Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)))
        (fun k =>
          (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
            ((topology C hmin).toOuterBoundaryCore)
            (boundaryLength_ge_three C hmin) k).value) =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore)
  exact
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows.outerBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum
      (P := (topology C hmin).toOuterBoundaryCore)
      (boundaryLength_ge_three C hmin)

/-- Assign a generated degree-three angle slot to the actual outer-boundary
sector centered at the same classified boundary index.  The containment of
that slot inside the sector is still the explicit sector-load inequality
below. -/
def selectedBoundaryDegree3SlotSectorOfIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (i :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree3Indices)
    (_slot : Fin 2) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  i.1

/-- Assign a generated degree-four angle slot to the actual outer-boundary
sector centered at the same classified boundary index. -/
def selectedBoundaryDegree4SlotSectorOfIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (i :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree4Indices)
    (_slot : Fin 3) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  i.1

/-- Assign a generated degree-five angle slot to the actual outer-boundary
sector centered at the same classified boundary index. -/
def selectedBoundaryDegree5SlotSectorOfIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (i :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree5Indices)
    (_slot : Fin 4) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  i.1

/-- Assign a generated degree-six angle slot to the actual outer-boundary
sector centered at the same classified boundary index. -/
def selectedBoundaryDegree6SlotSectorOfIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (i :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).degree6Indices)
    (_slot : Fin 5) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  i.1

/-- Assign a generated nontriangle-edge angle slot to the actual
outer-boundary sector at the corresponding boundary edge index. -/
def selectedBoundaryNontriangleSlotSectorOfIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (i :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices)
    (_slot : Fin 1) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  i.1

/-- Assign a generated long-arc angle slot to the actual outer-boundary sector
at that long-arc boundary index. -/
def selectedBoundaryLongArcSlotSectorOfIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (i :
      (selectedClassificationOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).longArcIndices)
    (_slot : Fin 1) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  i.1

/-- The pointwise load placed on a selected boundary sector by the canonical
same-index slot assignment.  This is a definitional abbreviation for the
remaining local containment inequality; it does not assert the inequality. -/
def selectedBoundaryIndexSectorLoad
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    Real :=
  Finset.sum Finset.univ
      (fun i =>
        Finset.sum (Finset.univ : Finset (Fin 2))
          (fun slot =>
            if selectedBoundaryDegree3SlotSectorOfIndex
                (topology := topology) (longArc := longArc) C hmin i slot = k then
              ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                (topology C hmin) hmin
                (longArc C hmin)).degree3 i slot).value
            else
              0)) +
    Finset.sum Finset.univ
      (fun i =>
        Finset.sum (Finset.univ : Finset (Fin 3))
          (fun slot =>
            if selectedBoundaryDegree4SlotSectorOfIndex
                (topology := topology) (longArc := longArc) C hmin i slot = k then
              ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                (topology C hmin) hmin
                (longArc C hmin)).degree4 i slot).value
            else
              0)) +
    Finset.sum Finset.univ
      (fun i =>
        Finset.sum (Finset.univ : Finset (Fin 4))
          (fun slot =>
            if selectedBoundaryDegree5SlotSectorOfIndex
                (topology := topology) (longArc := longArc) C hmin i slot = k then
              ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                (topology C hmin) hmin
                (longArc C hmin)).degree5 i slot).value
            else
              0)) +
    Finset.sum Finset.univ
      (fun i =>
        Finset.sum (Finset.univ : Finset (Fin 5))
          (fun slot =>
            if selectedBoundaryDegree6SlotSectorOfIndex
                (topology := topology) (longArc := longArc) C hmin i slot = k then
              ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                (topology C hmin) hmin
                (longArc C hmin)).degree6 i slot).value
            else
              0)) +
    Finset.sum Finset.univ
      (fun i =>
        Finset.sum (Finset.univ : Finset (Fin 1))
          (fun slot =>
            if selectedBoundaryNontriangleSlotSectorOfIndex
                (topology := topology) (longArc := longArc) C hmin i slot = k then
              ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                (topology C hmin) hmin
                (longArc C hmin)).nontriangle i slot).value
            else
              0)) +
    Finset.sum Finset.univ
      (fun i =>
        Finset.sum (Finset.univ : Finset (Fin 1))
          (fun slot =>
            if selectedBoundaryLongArcSlotSectorOfIndex
                (topology := topology) (longArc := longArc) C hmin i slot = k then
              ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                (topology C hmin) hmin
                (longArc C hmin)).longArc i slot).value
            else
              0))

/-- Constructor for actual boundary-neighbor sector-containment rows once the
honest slot-to-sector maps and real containment inequalities are supplied.
The boundary sectors themselves are the checked predecessor/current/successor
angles from `BoundaryAngleWitnessConstruction.UnitSeparatedAngle`. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfOuterBoundaryCoreIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (degree3Sector :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices ->
          Fin 2 -> Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (degree4Sector :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices ->
          Fin 3 -> Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (degree5Sector :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices ->
          Fin 4 -> Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (degree6Sector :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices ->
          Fin 5 -> Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (nontriangleSector :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices ->
          Fin 1 -> Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (longArcSector :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices ->
          Fin 1 -> Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (sectorLoad_le_boundarySectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 2))
                (fun slot =>
                  if degree3Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree3 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (fun slot =>
                  if degree4Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree4 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 4))
                (fun slot =>
                  if degree5Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree5 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 5))
                (fun slot =>
                  if degree6Sector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).degree6 i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 1))
                (fun slot =>
                  if nontriangleSector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).nontriangle i slot).value
                  else
                    0)) +
          Finset.sum Finset.univ
            (fun i =>
              Finset.sum (Finset.univ : Finset (Fin 1))
                (fun slot =>
                  if longArcSector C hmin i slot = k then
                    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
                      (topology C hmin) hmin
                      (longArc C hmin)).longArc i slot).value
                  else
                    0)) <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value)
    (boundarySectorAngleSum_le_simplePolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ
            (fun k =>
              (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
                (topology := topology) boundaryLength_ge_three C hmin k).value) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc where
  boundarySector := fun C hmin k =>
    actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
      (topology := topology) boundaryLength_ge_three C hmin k
  boundarySector_left_is_boundary_predecessor := fun C hmin k =>
    actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_left_is_boundary_predecessor
      (topology := topology) boundaryLength_ge_three C hmin k
  boundarySector_center_eq := fun _ _ _ => rfl
  boundarySector_right_eq := fun _ _ _ => rfl
  degree3Sector := fun C hmin =>
    degree3Sector C hmin
  degree4Sector := fun C hmin =>
    degree4Sector C hmin
  degree5Sector := fun C hmin =>
    degree5Sector C hmin
  degree6Sector := fun C hmin =>
    degree6Sector C hmin
  nontriangleSector := fun C hmin =>
    nontriangleSector C hmin
  longArcSector := fun C hmin =>
    longArcSector C hmin
  sectorLoad_le_boundarySectorAngle := fun C hmin k =>
    sectorLoad_le_boundarySectorAngle C hmin k
  boundarySectorAngleSum_le_simplePolygonInteriorAngleSum := fun C hmin =>
    boundarySectorAngleSum_le_simplePolygonInteriorAngleSum C hmin

/-- Canonical same-index slot assignment into actual boundary-neighbor
sectors.  This fills the six sector-map fields concretely and leaves only the
real pointwise load containment and total simple-polygon sector-sum bounds as
inputs. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectors
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (sectorLoad_le_boundarySectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value)
    (boundarySectorAngleSum_le_simplePolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ
            (fun k =>
              (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
                (topology := topology) boundaryLength_ge_three C hmin k).value) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc :=
  selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfOuterBoundaryCoreIndex
    (topology := topology) (longArc := longArc) boundaryLength_ge_three
    (selectedBoundaryDegree3SlotSectorOfIndex
      (topology := topology) (longArc := longArc))
    (selectedBoundaryDegree4SlotSectorOfIndex
      (topology := topology) (longArc := longArc))
    (selectedBoundaryDegree5SlotSectorOfIndex
      (topology := topology) (longArc := longArc))
    (selectedBoundaryDegree6SlotSectorOfIndex
      (topology := topology) (longArc := longArc))
    (selectedBoundaryNontriangleSlotSectorOfIndex
      (topology := topology) (longArc := longArc))
    (selectedBoundaryLongArcSlotSectorOfIndex
      (topology := topology) (longArc := longArc))
    (fun C hmin k => by
      change
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value
      exact sectorLoad_le_boundarySectorAngle C hmin k)
    (fun C hmin => by
      change
        Finset.sum Finset.univ
            (fun k =>
              (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
                (topology := topology) boundaryLength_ge_three C hmin k).value) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)
      exact boundarySectorAngleSum_le_simplePolygonInteriorAngleSum C hmin)

/-- Nonempty form of the canonical same-index actual-boundary-sector
constructor. -/
theorem nonempty_selectedTopologyActualBoundaryNeighborSectorContainmentRows_of_boundaryIndexSectors
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (sectorLoad_le_boundarySectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value)
    (boundarySectorAngleSum_le_simplePolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ
            (fun k =>
              (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
                (topology := topology) boundaryLength_ge_three C hmin k).value) <=
          simpleOuterPolygonInteriorAngleSum
            ((topology C hmin).toOuterBoundaryCore)) :
    Nonempty
      (SelectedTopologyActualBoundaryNeighborSectorContainmentRows
        topology longArc) :=
  Nonempty.intro
    (selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectors
      (topology := topology) (longArc := longArc) boundaryLength_ge_three
      sectorLoad_le_boundarySectorAngle
      boundarySectorAngleSum_le_simplePolygonInteriorAngleSum)

/-- Project W10's actual boundary-neighbor sector-sum row into the W34
selected-topology sector-sum shape. -/
theorem boundaryNeighborSectorAngleSumRows_le_simpleOuterPolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (sectorRows :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
        ((topology C hmin).toOuterBoundaryCore)) :
    Finset.sum Finset.univ
        (fun k =>
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value) <=
      simpleOuterPolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore) := by
  calc
    Finset.sum Finset.univ
        (fun k =>
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value)
        =
        BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
      actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum
        (topology := topology) boundaryLength_ge_three C hmin
    _ <=
        BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
      sectorRows.simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    _ =
      simpleOuterPolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore) := by
      rw [simpleOuterPolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum]

/-- Same-index actual-boundary-sector rows using W10's sector-sum package for
the polygon side.  The only local geometric inequality left outside this row
is the pointwise load containment. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (sectorLoad_le_boundarySectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc :=
  selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectors
    (topology := topology) (longArc := longArc) boundaryLength_ge_three
    sectorLoad_le_boundarySectorAngle
    (fun C hmin =>
      boundaryNeighborSectorAngleSumRows_le_simpleOuterPolygonInteriorAngleSum
        (topology := topology) boundaryLength_ge_three C hmin
        (sectorAngleRows C hmin))

/-- Canonical W10 boundary-neighbor sector rows for the selected topology.

The row family uses the actual predecessor/current/successor sector at each
boundary vertex.  The only polygon-side source left here is the genuine
simple-polygon interior-angle sum theorem. -/
def selectedTopologyBoundaryNeighborSectorAngleSumRowsOfSimplePolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore) :=
  fun C hmin =>
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum
      (P := (topology C hmin).toOuterBoundaryCore)
      (boundaryLength_ge_three C hmin)
      (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum C hmin)

@[simp]
theorem selectedTopologyBoundaryNeighborSectorAngleSumRowsOfSimplePolygonInteriorAngleSum_boundarySector
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    ((selectedTopologyBoundaryNeighborSectorAngleSumRowsOfSimplePolygonInteriorAngleSum
        (topology := topology) boundaryLength_ge_three
        simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
        C hmin).boundarySector k) =
      actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
        (topology := topology) boundaryLength_ge_three C hmin k :=
  rfl

/-- Same-index actual-boundary-sector rows with the matching W10 sector rows
constructed canonically.  This removes the separate W10-row hypothesis from
the boundary-index route; the remaining polygon-side source is the real
simple-polygon angle-sum theorem. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (sectorLoad_le_boundarySectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc :=
  selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndAngleSumRows
    (topology := topology) (longArc := longArc) boundaryLength_ge_three
    sectorLoad_le_boundarySectorAngle
    (selectedTopologyBoundaryNeighborSectorAngleSumRowsOfSimplePolygonInteriorAngleSum
      (topology := topology) boundaryLength_ge_three
      simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum)

/-- Left endpoint index of a consecutive gap in a finite neighbour interval
listed from the boundary predecessor to the boundary successor. -/
def boundaryNeighborGapLeftIndex (m : Nat) (g : Fin m) : Fin (m + 1) :=
  ⟨g.1, Nat.lt_trans g.2 (Nat.lt_succ_self m)⟩

/-- Right endpoint index of a consecutive gap in a finite neighbour interval
listed from the boundary predecessor to the boundary successor. -/
def boundaryNeighborGapRightIndex (m : Nat) (g : Fin m) : Fin (m + 1) :=
  ⟨g.1 + 1, Nat.succ_lt_succ g.2⟩

/-- The two endpoints of one consecutive gap in an interval list are distinct
as interval positions. -/
theorem boundaryNeighborGapLeftIndex_ne_rightIndex
    (m : Nat) (g : Fin m) :
    boundaryNeighborGapLeftIndex m g ≠ boundaryNeighborGapRightIndex m g := by
  intro h
  have hv : g.val = g.val + 1 := by
    simpa [boundaryNeighborGapLeftIndex, boundaryNeighborGapRightIndex]
      using congrArg Fin.val h
  exact Nat.succ_ne_self g.val hv.symm

/-- Build the consecutive gap angle from an ordered interval of unit
neighbours around a boundary vertex. -/
def boundaryNeighborGapAngleOfInterval
    {topology : MinimalFailureActualSelectedTopologyRows}
    (gapCount :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Nat)
    (neighbor :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Fin (gapCount C hmin k + 1) -> Fin n)
    (neighbor_injective :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Function.Injective (neighbor C hmin k))
    (neighbor_unit :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
      (j : Fin (gapCount C hmin k + 1)),
        (CanonicalGraph C).Adj (neighbor C hmin k j)
          ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (g : Fin (gapCount C hmin k)) :
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C) where
  left := neighbor C hmin k (boundaryNeighborGapLeftIndex (gapCount C hmin k) g)
  center := (topology C hmin).toOuterBoundaryCore.outerCycle.vertex k
  right := neighbor C hmin k (boundaryNeighborGapRightIndex (gapCount C hmin k) g)
  left_adj := neighbor_unit C hmin k
    (boundaryNeighborGapLeftIndex (gapCount C hmin k) g)
  right_adj := neighbor_unit C hmin k
    (boundaryNeighborGapRightIndex (gapCount C hmin k) g)
  endpoints_ne := by
    intro h
    exact boundaryNeighborGapLeftIndex_ne_rightIndex (gapCount C hmin k) g
      (neighbor_injective C hmin k h)

/--
Positive S3 row package for the local cyclic-neighbour gap decomposition.

For each selected boundary vertex, `neighbor` lists the unit neighbours in the
outer-face interval from boundary predecessor to boundary successor.  Each
`gapAngle` is the consecutive angle between neighbouring entries in that
interval.  The six generated E12 slot families are then mapped into those
consecutive gaps, and the package carries the two genuine local comparisons:
the generated slot load is bounded by the listed gap mass, and the gap mass is
bounded by the predecessor/current/successor boundary sector.
-/
structure SelectedTopologyBoundaryCyclicNeighborGapRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  gapCount :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Nat
  neighbor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Fin (gapCount C hmin k + 1) -> Fin n
  neighbor_injective :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Function.Injective (neighbor C hmin k)
  first_neighbor_eq_boundary_predecessor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        neighbor C hmin k ⟨0, Nat.succ_pos (gapCount C hmin k)⟩ =
          (topology C hmin).toOuterBoundaryCore.outerCycle.prevVertex k
  last_neighbor_eq_boundary_successor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        neighbor C hmin k
            ⟨gapCount C hmin k, Nat.lt_succ_self (gapCount C hmin k)⟩ =
          (topology C hmin).toOuterBoundaryCore.outerCycle.nextVertex k
  neighbor_unit :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
      (j : Fin (gapCount C hmin k + 1)),
        (CanonicalGraph C).Adj (neighbor C hmin k j)
          ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k)
  gapAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Fin (gapCount C hmin k) ->
          BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C)
  gapAngle_left_eq :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
      (g : Fin (gapCount C hmin k)),
        (gapAngle C hmin k g).left =
          neighbor C hmin k
            (boundaryNeighborGapLeftIndex (gapCount C hmin k) g)
  gapAngle_center_eq :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
      (g : Fin (gapCount C hmin k)),
        (gapAngle C hmin k g).center =
          (topology C hmin).toOuterBoundaryCore.outerCycle.vertex k
  gapAngle_right_eq :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
      (g : Fin (gapCount C hmin k)),
        (gapAngle C hmin k g).right =
          neighbor C hmin k
            (boundaryNeighborGapRightIndex (gapCount C hmin k) g)
  degree3Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (_slot : Fin 2),
        Fin (gapCount C hmin i.1)
  degree4Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (_slot : Fin 3),
        Fin (gapCount C hmin i.1)
  degree5Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (_slot : Fin 4),
        Fin (gapCount C hmin i.1)
  degree6Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (_slot : Fin 5),
        Fin (gapCount C hmin i.1)
  nontriangleGap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (_slot : Fin 1),
        Fin (gapCount C hmin i.1)
  longArcGap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (_slot : Fin 1),
        Fin (gapCount C hmin i.1)
  degree3_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (slot : Fin 2),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value =
          (gapAngle C hmin i.1 (degree3Gap C hmin i slot)).value
  degree4_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (slot : Fin 3),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value =
          (gapAngle C hmin i.1 (degree4Gap C hmin i slot)).value
  degree5_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (slot : Fin 4),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value =
          (gapAngle C hmin i.1 (degree5Gap C hmin i slot)).value
  degree6_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (slot : Fin 5),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value =
          (gapAngle C hmin i.1 (degree6Gap C hmin i slot)).value
  nontriangle_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangle i slot).value =
          (gapAngle C hmin i.1 (nontriangleGap C hmin i slot)).value
  longArc_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArc i slot).value =
          (gapAngle C hmin i.1 (longArcGap C hmin i slot)).value
  slotLoad_le_gapAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          Finset.sum (Finset.univ : Finset (Fin (gapCount C hmin k)))
            (fun g => (gapAngle C hmin k g).value)
  gapAngleSum_le_boundarySectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Finset.sum (Finset.univ : Finset (Fin (gapCount C hmin k)))
            (fun g => (gapAngle C hmin k g).value) <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value

namespace SelectedTopologyBoundaryCyclicNeighborGapRows

/-- The cyclic-neighbour gap rows close the local pointwise S3 sector-load
inequality by summing through the listed consecutive gaps. -/
theorem sectorLoad_le_boundarySectorAngle
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryCyclicNeighborGapRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
      selectedBoundaryIndexSectorLoad
        (topology := topology) (longArc := longArc) C hmin k <=
        (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
          (topology := topology) R.boundaryLength_ge_three C hmin k).value :=
  le_trans (R.slotLoad_le_gapAngleSum C hmin k)
    (R.gapAngleSum_le_boundarySectorAngle C hmin k)

end SelectedTopologyBoundaryCyclicNeighborGapRows

/--
Interval-level source for the S3 cyclic-neighbour gap rows.

This version only asks for an ordered list of unit neighbours at each boundary
vertex.  The actual consecutive `UnitSeparatedAngle` gap records are then
constructed from adjacency and injectivity by
`boundaryNeighborGapAngleOfInterval`.
-/
structure SelectedTopologyBoundaryCyclicNeighborIntervalRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  gapCount :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Nat
  neighbor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Fin (gapCount C hmin k + 1) -> Fin n
  neighbor_injective :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Function.Injective (neighbor C hmin k)
  first_neighbor_eq_boundary_predecessor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        neighbor C hmin k ⟨0, Nat.succ_pos (gapCount C hmin k)⟩ =
          (topology C hmin).toOuterBoundaryCore.outerCycle.prevVertex k
  last_neighbor_eq_boundary_successor :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        neighbor C hmin k
            ⟨gapCount C hmin k, Nat.lt_succ_self (gapCount C hmin k)⟩ =
          (topology C hmin).toOuterBoundaryCore.outerCycle.nextVertex k
  neighbor_unit :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
      (j : Fin (gapCount C hmin k + 1)),
        (CanonicalGraph C).Adj (neighbor C hmin k j)
          ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k)
  degree3Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (_slot : Fin 2),
        Fin (gapCount C hmin i.1)
  degree4Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (_slot : Fin 3),
        Fin (gapCount C hmin i.1)
  degree5Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (_slot : Fin 4),
        Fin (gapCount C hmin i.1)
  degree6Gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (_slot : Fin 5),
        Fin (gapCount C hmin i.1)
  nontriangleGap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (_slot : Fin 1),
        Fin (gapCount C hmin i.1)
  longArcGap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (_slot : Fin 1),
        Fin (gapCount C hmin i.1)
  degree3_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (slot : Fin 2),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value =
          (boundaryNeighborGapAngleOfInterval
            (topology := topology) gapCount neighbor neighbor_injective
            neighbor_unit C hmin i.1 (degree3Gap C hmin i slot)).value
  degree4_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (slot : Fin 3),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value =
          (boundaryNeighborGapAngleOfInterval
            (topology := topology) gapCount neighbor neighbor_injective
            neighbor_unit C hmin i.1 (degree4Gap C hmin i slot)).value
  degree5_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (slot : Fin 4),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value =
          (boundaryNeighborGapAngleOfInterval
            (topology := topology) gapCount neighbor neighbor_injective
            neighbor_unit C hmin i.1 (degree5Gap C hmin i slot)).value
  degree6_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (slot : Fin 5),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value =
          (boundaryNeighborGapAngleOfInterval
            (topology := topology) gapCount neighbor neighbor_injective
            neighbor_unit C hmin i.1 (degree6Gap C hmin i slot)).value
  nontriangle_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangle i slot).value =
          (boundaryNeighborGapAngleOfInterval
            (topology := topology) gapCount neighbor neighbor_injective
            neighbor_unit C hmin i.1 (nontriangleGap C hmin i slot)).value
  longArc_angle_value_eq_gap :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArc i slot).value =
          (boundaryNeighborGapAngleOfInterval
            (topology := topology) gapCount neighbor neighbor_injective
            neighbor_unit C hmin i.1 (longArcGap C hmin i slot)).value
  slotLoad_le_gapAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := topology) (longArc := longArc) C hmin k <=
          Finset.sum (Finset.univ : Finset (Fin (gapCount C hmin k)))
            (fun g =>
              (boundaryNeighborGapAngleOfInterval
                (topology := topology) gapCount neighbor neighbor_injective
                neighbor_unit C hmin k g).value)
  gapAngleSum_le_boundarySectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        Finset.sum (Finset.univ : Finset (Fin (gapCount C hmin k)))
            (fun g =>
              (boundaryNeighborGapAngleOfInterval
                (topology := topology) gapCount neighbor neighbor_injective
                neighbor_unit C hmin k g).value) <=
            (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := topology) boundaryLength_ge_three C hmin k).value

/-- Build one consecutive gap angle from a single boundary-index interval.
This is the local version of `boundaryNeighborGapAngleOfInterval`; it is useful
when the cyclic-neighbour order is proved one selected boundary vertex at a
time. -/
def boundaryNeighborGapAngleOfIndexInterval
    {topology : MinimalFailureActualSelectedTopologyRows}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (gapCount : Nat)
    (neighbor : Fin (gapCount + 1) -> Fin n)
    (neighbor_injective : Function.Injective neighbor)
    (neighbor_unit :
      forall j,
        (CanonicalGraph C).Adj (neighbor j)
          ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k))
    (g : Fin gapCount) :
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C) where
  left := neighbor (boundaryNeighborGapLeftIndex gapCount g)
  center := (topology C hmin).toOuterBoundaryCore.outerCycle.vertex k
  right := neighbor (boundaryNeighborGapRightIndex gapCount g)
  left_adj := neighbor_unit (boundaryNeighborGapLeftIndex gapCount g)
  right_adj := neighbor_unit (boundaryNeighborGapRightIndex gapCount g)
  endpoints_ne := by
    intro h
    exact boundaryNeighborGapLeftIndex_ne_rightIndex gapCount g
      (neighbor_injective h)

/--
Local S3 interval rows at one selected boundary index.

The row contains only the concrete obligations for that vertex: the ordered
unit-neighbour interval from boundary predecessor to boundary successor,
injectivity of that list, the generated-slot-to-gap equalities, the local
slot-load-to-gap-sum comparison, and the gap-sum-to-PCS-sector comparison.
-/
structure SelectedBoundaryIndexCyclicNeighborIntervalRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    Type where
  gapCount : Nat
  neighbor : Fin (gapCount + 1) -> Fin n
  neighbor_injective : Function.Injective neighbor
  first_neighbor_eq_boundary_predecessor :
    neighbor ⟨0, Nat.succ_pos gapCount⟩ =
      (topology C hmin).toOuterBoundaryCore.outerCycle.prevVertex k
  last_neighbor_eq_boundary_successor :
    neighbor ⟨gapCount, Nat.lt_succ_self gapCount⟩ =
      (topology C hmin).toOuterBoundaryCore.outerCycle.nextVertex k
  neighbor_unit :
    forall j,
      (CanonicalGraph C).Adj (neighbor j)
        ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k)
  degree3Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices),
        i.1 = k -> Fin 2 -> Fin gapCount
  degree4Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices),
        i.1 = k -> Fin 3 -> Fin gapCount
  degree5Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices),
        i.1 = k -> Fin 4 -> Fin gapCount
  degree6Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices),
        i.1 = k -> Fin 5 -> Fin gapCount
  nontriangleGap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices),
        i.1 = k -> Fin 1 -> Fin gapCount
  longArcGap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices),
        i.1 = k -> Fin 1 -> Fin gapCount
  degree3_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (hik : i.1 = k) (slot : Fin 2),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit (degree3Gap i hik slot)).value
  degree4_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (hik : i.1 = k) (slot : Fin 3),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit (degree4Gap i hik slot)).value
  degree5_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (hik : i.1 = k) (slot : Fin 4),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit (degree5Gap i hik slot)).value
  degree6_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (hik : i.1 = k) (slot : Fin 5),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit (degree6Gap i hik slot)).value
  nontriangle_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (hik : i.1 = k) (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangle i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit (nontriangleGap i hik slot)).value
  longArc_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (hik : i.1 = k) (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArc i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit (longArcGap i hik slot)).value
  slotLoad_le_gapAngleSum :
    selectedBoundaryIndexSectorLoad
      (topology := topology) (longArc := longArc) C hmin k <=
      Finset.sum (Finset.univ : Finset (Fin gapCount))
        (fun g =>
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit g).value)
  gapAngleSum_le_boundarySectorAngle :
    Finset.sum (Finset.univ : Finset (Fin gapCount))
        (fun g =>
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k gapCount neighbor
            neighbor_injective neighbor_unit g).value) <=
      (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
        (topology := topology) boundaryLength_ge_three C hmin k).value

/--
Per-boundary-index S3 interval rows.

This family form is the intended local construction surface: prove the cyclic
unit-neighbour interval and the slot/gap inequalities at each selected boundary
index, then project to the global interval package.
-/
structure SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  atIndex :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborIntervalRows
          (topology := topology) (longArc := longArc)
          boundaryLength_ge_three C hmin k

/--
Actual ordered unit-neighbour data at one selected boundary index.

The boundary walk already supplies an endpoint interval, usually with only the
two forced entries: predecessor and successor.  This record is the missing
planar-order input: an ordered unit-neighbour list whose first and last entries
agree with that existing endpoint package.
-/
structure SelectedBoundaryIndexOrderedUnitNeighborData
    (topology : MinimalFailureActualSelectedTopologyRows)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
        ((topology C hmin).toOuterBoundaryCore.outerCycle) k) :
    Type where
  gapCount : Nat
  neighbor : Fin (gapCount + 1) -> Fin n
  neighbor_injective : Function.Injective neighbor
  first_neighbor_eq_endpoint :
    neighbor ⟨0, Nat.succ_pos gapCount⟩ =
      endpointInterval.neighbor
        ⟨0, Nat.succ_pos endpointInterval.gapCount⟩
  last_neighbor_eq_endpoint :
    neighbor ⟨gapCount, Nat.lt_succ_self gapCount⟩ =
      endpointInterval.neighbor
        ⟨endpointInterval.gapCount,
          Nat.lt_succ_self endpointInterval.gapCount⟩
  neighbor_unit :
    forall j,
      (CanonicalGraph C).Adj (neighbor j)
        ((topology C hmin).toOuterBoundaryCore.outerCycle.vertex k)

namespace SelectedBoundaryIndexOrderedUnitNeighborData

/-- Consume the W28 import-acyclic ordered-neighbor carrier as the W34
selected-boundary ordered-neighbor row. -/
def ofW28BoundaryIndexOrderedUnitNeighborData
    {topology : MinimalFailureActualSelectedTopologyRows}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)}
    {endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
        ((topology C hmin).toOuterBoundaryCore.outerCycle) k}
    (D :
      OuterBoundaryCoreConstructionW28.BoundaryIndexOrderedUnitNeighborData
        ((topology C hmin).toOuterBoundaryCore.outerCycle) k
        endpointInterval) :
    SelectedBoundaryIndexOrderedUnitNeighborData
      (topology := topology) C hmin k endpointInterval where
  gapCount := D.gapCount
  neighbor := D.neighbor
  neighbor_injective := D.neighbor_injective
  first_neighbor_eq_endpoint := D.first_neighbor_eq_endpoint
  last_neighbor_eq_endpoint := D.last_neighbor_eq_endpoint
  neighbor_unit := D.neighbor_unit

/-- Repackage a full ordered unit-neighbour list as the interval carrier used
by the W34 boundary-data rows, preserving the existing endpoint package. -/
def toEndpointNeighborInterval
    {topology : MinimalFailureActualSelectedTopologyRows}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)}
    {endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
        ((topology C hmin).toOuterBoundaryCore.outerCycle) k}
    (D :
      SelectedBoundaryIndexOrderedUnitNeighborData
        (topology := topology) C hmin k endpointInterval) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      ((topology C hmin).toOuterBoundaryCore.outerCycle) k where
  gapCount := D.gapCount
  neighbor := D.neighbor
  neighbor_injective := D.neighbor_injective
  first_neighbor_eq_boundary_predecessor := by
    calc
      D.neighbor ⟨0, Nat.succ_pos D.gapCount⟩ =
          endpointInterval.neighbor
            ⟨0, Nat.succ_pos endpointInterval.gapCount⟩ :=
        D.first_neighbor_eq_endpoint
      _ = (topology C hmin).toOuterBoundaryCore.outerCycle.prevVertex k :=
        endpointInterval.first_neighbor_eq_boundary_predecessor
  last_neighbor_eq_boundary_successor := by
    calc
      D.neighbor ⟨D.gapCount, Nat.lt_succ_self D.gapCount⟩ =
          endpointInterval.neighbor
            ⟨endpointInterval.gapCount,
              Nat.lt_succ_self endpointInterval.gapCount⟩ :=
        D.last_neighbor_eq_endpoint
      _ = (topology C hmin).toOuterBoundaryCore.outerCycle.nextVertex k :=
        endpointInterval.last_neighbor_eq_boundary_successor
  neighbor_unit := D.neighbor_unit

end SelectedBoundaryIndexOrderedUnitNeighborData

/-- The W28 endpoint-neighbor interval for a selected topology row. -/
def w28EndpointNeighborIntervalOfSelectedTopology
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      ((topology C hmin).toOuterBoundaryCore.outerCycle) k :=
  OuterBoundaryCoreConstructionW28.endpointNeighborIntervalOfOuterBoundaryCore
    (topology C hmin).toOuterBoundaryCore
    (boundaryLength_ge_three C hmin) k

/-- W28's endpoint-backed ordered-neighbor data, reindexed into the W34
selected-boundary row surface. -/
def w28SelectedBoundaryIndexOrderedUnitNeighborData
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    SelectedBoundaryIndexOrderedUnitNeighborData
      (topology := topology) C hmin k
      (w28EndpointNeighborIntervalOfSelectedTopology
        boundaryLength_ge_three C hmin k) :=
  SelectedBoundaryIndexOrderedUnitNeighborData.ofW28BoundaryIndexOrderedUnitNeighborData
    (topology := topology) (C := C) (hmin := hmin) (k := k)
    (OuterBoundaryCoreConstructionW28.orderedUnitNeighborDataOfOuterBoundaryCore
      (topology C hmin).toOuterBoundaryCore
      (boundaryLength_ge_three C hmin) k)

/--
The non-endpoint S3 data for a fixed ordered neighbour interval.

Once the endpoint-compatible ordered unit-neighbour list is known, these are
exactly the generated-slot-to-gap maps, the value equalities tying generated
angles to consecutive listed gaps, and the two local containment inequalities.
-/
structure SelectedBoundaryIndexCyclicNeighborSlotToGapRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
        ((topology C hmin).toOuterBoundaryCore.outerCycle) k)
    (orderedNeighbor :
      SelectedBoundaryIndexOrderedUnitNeighborData
        (topology := topology) C hmin k endpointInterval) :
    Type where
  degree3Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices),
        i.1 = k -> Fin 2 -> Fin orderedNeighbor.gapCount
  degree4Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices),
        i.1 = k -> Fin 3 -> Fin orderedNeighbor.gapCount
  degree5Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices),
        i.1 = k -> Fin 4 -> Fin orderedNeighbor.gapCount
  degree6Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices),
        i.1 = k -> Fin 5 -> Fin orderedNeighbor.gapCount
  nontriangleGap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices),
        i.1 = k -> Fin 1 -> Fin orderedNeighbor.gapCount
  longArcGap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices),
        i.1 = k -> Fin 1 -> Fin orderedNeighbor.gapCount
  degree3_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (hik : i.1 = k) (slot : Fin 2),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit (degree3Gap i hik slot)).value
  degree4_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (hik : i.1 = k) (slot : Fin 3),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit (degree4Gap i hik slot)).value
  degree5_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (hik : i.1 = k) (slot : Fin 4),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit (degree5Gap i hik slot)).value
  degree6_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (hik : i.1 = k) (slot : Fin 5),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit (degree6Gap i hik slot)).value
  nontriangle_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (hik : i.1 = k) (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangle i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit (nontriangleGap i hik slot)).value
  longArc_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (hik : i.1 = k) (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArc i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit (longArcGap i hik slot)).value
  slotLoad_le_gapAngleSum :
    selectedBoundaryIndexSectorLoad
      (topology := topology) (longArc := longArc) C hmin k <=
      Finset.sum (Finset.univ : Finset (Fin orderedNeighbor.gapCount))
        (fun g =>
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit g).value)
  gapAngleSum_le_boundarySectorAngle :
    Finset.sum (Finset.univ : Finset (Fin orderedNeighbor.gapCount))
        (fun g =>
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k orderedNeighbor.gapCount
            orderedNeighbor.neighbor orderedNeighbor.neighbor_injective
            orderedNeighbor.neighbor_unit g).value) <=
      (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
        (topology := topology) boundaryLength_ge_three C hmin k).value

/--
Local boundary-data form of the per-index cyclic-neighbour interval rows.

The interval field uses the existing `BoundaryWalkBridge.EndpointNeighborInterval`
shape, but an endpoint-only instance is not enough for S3.  Use
`SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows.ofOrderedUnitNeighborDataAndSlotToGapRows`
to build this row from an endpoint interval plus the actual ordered
unit-neighbour list and slot-to-gap rows.
-/
structure SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    Type where
  interval :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      ((topology C hmin).toOuterBoundaryCore.outerCycle) k
  degree3Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices),
        i.1 = k -> Fin 2 -> Fin interval.gapCount
  degree4Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices),
        i.1 = k -> Fin 3 -> Fin interval.gapCount
  degree5Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices),
        i.1 = k -> Fin 4 -> Fin interval.gapCount
  degree6Gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices),
        i.1 = k -> Fin 5 -> Fin interval.gapCount
  nontriangleGap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices),
        i.1 = k -> Fin 1 -> Fin interval.gapCount
  longArcGap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices),
        i.1 = k -> Fin 1 -> Fin interval.gapCount
  degree3_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices)
      (hik : i.1 = k) (slot : Fin 2),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            (degree3Gap i hik slot)).value
  degree4_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices)
      (hik : i.1 = k) (slot : Fin 3),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            (degree4Gap i hik slot)).value
  degree5_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices)
      (hik : i.1 = k) (slot : Fin 4),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            (degree5Gap i hik slot)).value
  degree6_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices)
      (hik : i.1 = k) (slot : Fin 5),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            (degree6Gap i hik slot)).value
  nontriangle_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin
            (longArc C hmin)).nontriangleEdgeIndices)
      (hik : i.1 = k) (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangle i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            (nontriangleGap i hik slot)).value
  longArc_angle_value_eq_gap :
    forall
      (i :
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices)
      (hik : i.1 = k) (slot : Fin 1),
        ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArc i slot).value =
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            (longArcGap i hik slot)).value
  slotLoad_le_gapAngleSum :
    selectedBoundaryIndexSectorLoad
      (topology := topology) (longArc := longArc) C hmin k <=
      Finset.sum (Finset.univ : Finset (Fin interval.gapCount))
        (fun g =>
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            g).value)
  gapAngleSum_le_boundarySectorAngle :
    Finset.sum (Finset.univ : Finset (Fin interval.gapCount))
        (fun g =>
          (boundaryNeighborGapAngleOfIndexInterval
            (topology := topology) C hmin k interval.gapCount
            interval.neighbor interval.neighbor_injective interval.neighbor_unit
            g).value) <=
      (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
        (topology := topology) boundaryLength_ge_three C hmin k).value

namespace SelectedBoundaryIndexCyclicNeighborSlotToGapRows

/-- Assemble the full local boundary-data rows from the existing endpoint
interval, the actual ordered unit-neighbour list, and the slot-to-gap rows. -/
def toBoundaryDataRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)}
    {endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
        ((topology C hmin).toOuterBoundaryCore.outerCycle) k}
    {orderedNeighbor :
      SelectedBoundaryIndexOrderedUnitNeighborData
        (topology := topology) C hmin k endpointInterval}
    (R :
      SelectedBoundaryIndexCyclicNeighborSlotToGapRows
        (topology := topology) (longArc := longArc)
        boundaryLength_ge_three C hmin k endpointInterval orderedNeighbor) :
    SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
      (topology := topology) (longArc := longArc)
      boundaryLength_ge_three C hmin k where
  interval := orderedNeighbor.toEndpointNeighborInterval
  degree3Gap := R.degree3Gap
  degree4Gap := R.degree4Gap
  degree5Gap := R.degree5Gap
  degree6Gap := R.degree6Gap
  nontriangleGap := R.nontriangleGap
  longArcGap := R.longArcGap
  degree3_angle_value_eq_gap := R.degree3_angle_value_eq_gap
  degree4_angle_value_eq_gap := R.degree4_angle_value_eq_gap
  degree5_angle_value_eq_gap := R.degree5_angle_value_eq_gap
  degree6_angle_value_eq_gap := R.degree6_angle_value_eq_gap
  nontriangle_angle_value_eq_gap := R.nontriangle_angle_value_eq_gap
  longArc_angle_value_eq_gap := R.longArc_angle_value_eq_gap
  slotLoad_le_gapAngleSum := R.slotLoad_le_gapAngleSum
  gapAngleSum_le_boundarySectorAngle := R.gapAngleSum_le_boundarySectorAngle

end SelectedBoundaryIndexCyclicNeighborSlotToGapRows

/-- The remaining W34 local S3 source after W28 supplies the endpoint-backed
ordered-neighbor data: only the slot-to-gap geometry is still external. -/
abbrev SelectedTopologyW28OrderedBoundaryIndexSlotToGapRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length) :
    Type :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
      SelectedBoundaryIndexCyclicNeighborSlotToGapRows
        (topology := topology) (longArc := longArc)
        boundaryLength_ge_three C hmin k
        (w28EndpointNeighborIntervalOfSelectedTopology
          boundaryLength_ge_three C hmin k)
        (w28SelectedBoundaryIndexOrderedUnitNeighborData
          boundaryLength_ge_three C hmin k)

namespace SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows

/-- Project boundary-data interval rows to the actual local W34 row surface. -/
def toRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    {boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length}
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)}
    (R :
      SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        (topology := topology) (longArc := longArc)
        boundaryLength_ge_three C hmin k) :
    SelectedBoundaryIndexCyclicNeighborIntervalRows
      (topology := topology) (longArc := longArc)
      boundaryLength_ge_three C hmin k where
  gapCount := R.interval.gapCount
  neighbor := R.interval.neighbor
  neighbor_injective := R.interval.neighbor_injective
  first_neighbor_eq_boundary_predecessor :=
    R.interval.first_neighbor_eq_boundary_predecessor
  last_neighbor_eq_boundary_successor :=
    R.interval.last_neighbor_eq_boundary_successor
  neighbor_unit := R.interval.neighbor_unit
  degree3Gap := R.degree3Gap
  degree4Gap := R.degree4Gap
  degree5Gap := R.degree5Gap
  degree6Gap := R.degree6Gap
  nontriangleGap := R.nontriangleGap
  longArcGap := R.longArcGap
  degree3_angle_value_eq_gap := R.degree3_angle_value_eq_gap
  degree4_angle_value_eq_gap := R.degree4_angle_value_eq_gap
  degree5_angle_value_eq_gap := R.degree5_angle_value_eq_gap
  degree6_angle_value_eq_gap := R.degree6_angle_value_eq_gap
  nontriangle_angle_value_eq_gap := R.nontriangle_angle_value_eq_gap
  longArc_angle_value_eq_gap := R.longArc_angle_value_eq_gap
  slotLoad_le_gapAngleSum := R.slotLoad_le_gapAngleSum
  gapAngleSum_le_boundarySectorAngle := R.gapAngleSum_le_boundarySectorAngle

end SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows

/--
Per-boundary-index interval rows whose boundary-neighbour list is stored in
the existing topology boundary-walk carrier.
-/
structure SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  atIndex :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
          (topology := topology) (longArc := longArc)
          boundaryLength_ge_three C hmin k

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows

/-- Assemble the topology-level boundary-data interval rows from endpoint
intervals, actual ordered unit-neighbour lists, and local slot-to-gap rows. -/
def ofOrderedUnitNeighborDataAndSlotToGapRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (endpointInterval :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
          ((topology C hmin).toOuterBoundaryCore.outerCycle) k)
    (orderedNeighbor :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexOrderedUnitNeighborData
          (topology := topology) C hmin k (endpointInterval C hmin k))
    (slotToGapRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborSlotToGapRows
          (topology := topology) (longArc := longArc)
          boundaryLength_ge_three C hmin k (endpointInterval C hmin k)
          (orderedNeighbor C hmin k)) :
    SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
      topology longArc where
  boundaryLength_ge_three := boundaryLength_ge_three
  atIndex := fun C hmin k =>
    (slotToGapRows C hmin k).toBoundaryDataRows

/-- Assemble topology-level boundary-data interval rows using the W28
endpoint-backed ordered-neighbor data; the only extra local input is the real
slot-to-gap geometry over that data. -/
def ofW28OrderedUnitNeighborDataAndSlotToGapRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (slotToGapRows :
      SelectedTopologyW28OrderedBoundaryIndexSlotToGapRows
        topology longArc boundaryLength_ge_three) :
    SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
      topology longArc :=
  ofOrderedUnitNeighborDataAndSlotToGapRows
    (topology := topology) (longArc := longArc)
    boundaryLength_ge_three
    (fun C hmin k =>
      w28EndpointNeighborIntervalOfSelectedTopology
        boundaryLength_ge_three C hmin k)
    (fun C hmin k =>
      w28SelectedBoundaryIndexOrderedUnitNeighborData
        boundaryLength_ge_three C hmin k)
    (fun C hmin k => slotToGapRows C hmin k)

/-- Project boundary-data rows to the actual per-index interval-row surface. -/
def toRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        topology longArc) :
    SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc where
  boundaryLength_ge_three := R.boundaryLength_ge_three
  atIndex := fun C hmin k =>
    (R.atIndex C hmin k).toRows

/-- Nonempty projection from boundary-data rows to actual interval rows. -/
theorem nonempty_rows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        topology longArc) :
    Nonempty (SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc) :=
  Nonempty.intro R.toRows

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Project local per-index interval rows to the global interval row package
used by the S3 sector/order route. -/
def toIntervalRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc) :
    SelectedTopologyBoundaryCyclicNeighborIntervalRows topology longArc where
  boundaryLength_ge_three := R.boundaryLength_ge_three
  gapCount := fun C hmin k => (R.atIndex C hmin k).gapCount
  neighbor := fun C hmin k => (R.atIndex C hmin k).neighbor
  neighbor_injective := fun C hmin k =>
    (R.atIndex C hmin k).neighbor_injective
  first_neighbor_eq_boundary_predecessor := fun C hmin k =>
    (R.atIndex C hmin k).first_neighbor_eq_boundary_predecessor
  last_neighbor_eq_boundary_successor := fun C hmin k =>
    (R.atIndex C hmin k).last_neighbor_eq_boundary_successor
  neighbor_unit := fun C hmin k =>
    (R.atIndex C hmin k).neighbor_unit
  degree3Gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree3Gap i rfl slot
  degree4Gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree4Gap i rfl slot
  degree5Gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree5Gap i rfl slot
  degree6Gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree6Gap i rfl slot
  nontriangleGap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).nontriangleGap i rfl slot
  longArcGap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).longArcGap i rfl slot
  degree3_angle_value_eq_gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree3_angle_value_eq_gap i rfl slot
  degree4_angle_value_eq_gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree4_angle_value_eq_gap i rfl slot
  degree5_angle_value_eq_gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree5_angle_value_eq_gap i rfl slot
  degree6_angle_value_eq_gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).degree6_angle_value_eq_gap i rfl slot
  nontriangle_angle_value_eq_gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).nontriangle_angle_value_eq_gap i rfl slot
  longArc_angle_value_eq_gap := fun C hmin i slot =>
    (R.atIndex C hmin i.1).longArc_angle_value_eq_gap i rfl slot
  slotLoad_le_gapAngleSum := fun C hmin k =>
    (R.atIndex C hmin k).slotLoad_le_gapAngleSum
  gapAngleSum_le_boundarySectorAngle := fun C hmin k =>
    (R.atIndex C hmin k).gapAngleSum_le_boundarySectorAngle

/-- Nonempty projection from per-index interval rows to global interval rows. -/
theorem nonempty_intervalRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc) :
    Nonempty (SelectedTopologyBoundaryCyclicNeighborIntervalRows topology longArc) :=
  Nonempty.intro R.toIntervalRows

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

namespace SelectedTopologyBoundaryCyclicNeighborIntervalRows

/-- The consecutive gap angle derived from an interval row. -/
def gapAngle
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryCyclicNeighborIntervalRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length))
    (g : Fin (R.gapCount C hmin k)) :
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle (CanonicalGraph C) :=
  boundaryNeighborGapAngleOfInterval
    (topology := topology) R.gapCount R.neighbor R.neighbor_injective
    R.neighbor_unit C hmin k g

/-- Interval rows produce the full cyclic-neighbour gap rows by constructing
each consecutive gap angle from the ordered unit-neighbour list. -/
def toCyclicNeighborGapRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryCyclicNeighborIntervalRows topology longArc) :
    SelectedTopologyBoundaryCyclicNeighborGapRows topology longArc where
  boundaryLength_ge_three := R.boundaryLength_ge_three
  gapCount := R.gapCount
  neighbor := R.neighbor
  neighbor_injective := R.neighbor_injective
  first_neighbor_eq_boundary_predecessor := R.first_neighbor_eq_boundary_predecessor
  last_neighbor_eq_boundary_successor := R.last_neighbor_eq_boundary_successor
  neighbor_unit := R.neighbor_unit
  gapAngle := fun C hmin k g => R.gapAngle C hmin k g
  gapAngle_left_eq := fun _ _ _ _ => rfl
  gapAngle_center_eq := fun _ _ _ _ => rfl
  gapAngle_right_eq := fun _ _ _ _ => rfl
  degree3Gap := R.degree3Gap
  degree4Gap := R.degree4Gap
  degree5Gap := R.degree5Gap
  degree6Gap := R.degree6Gap
  nontriangleGap := R.nontriangleGap
  longArcGap := R.longArcGap
  degree3_angle_value_eq_gap := R.degree3_angle_value_eq_gap
  degree4_angle_value_eq_gap := R.degree4_angle_value_eq_gap
  degree5_angle_value_eq_gap := R.degree5_angle_value_eq_gap
  degree6_angle_value_eq_gap := R.degree6_angle_value_eq_gap
  nontriangle_angle_value_eq_gap := R.nontriangle_angle_value_eq_gap
  longArc_angle_value_eq_gap := R.longArc_angle_value_eq_gap
  slotLoad_le_gapAngleSum := R.slotLoad_le_gapAngleSum
  gapAngleSum_le_boundarySectorAngle := R.gapAngleSum_le_boundarySectorAngle

/-- Nonempty projection from interval rows to cyclic-neighbour gap rows. -/
theorem nonempty_cyclicNeighborGapRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryCyclicNeighborIntervalRows topology longArc) :
    Nonempty (SelectedTopologyBoundaryCyclicNeighborGapRows topology longArc) :=
  Nonempty.intro R.toCyclicNeighborGapRows

end SelectedTopologyBoundaryCyclicNeighborIntervalRows

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Per-index interval rows produce the full cyclic-neighbour gap rows after
assembling the local ordered neighbour intervals. -/
def toCyclicNeighborGapRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc) :
    SelectedTopologyBoundaryCyclicNeighborGapRows topology longArc :=
  R.toIntervalRows.toCyclicNeighborGapRows

/-- Nonempty projection from local per-index interval rows to cyclic-neighbour
gap rows. -/
theorem nonempty_cyclicNeighborGapRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc) :
    Nonempty (SelectedTopologyBoundaryCyclicNeighborGapRows topology longArc) :=
  Nonempty.intro R.toCyclicNeighborGapRows

/-- The local interval rows give the pointwise containment of the generated
same-index slot load in the actual predecessor/current/successor sector. -/
theorem sectorLoad_le_boundarySectorAngle
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
      selectedBoundaryIndexSectorLoad
        (topology := topology) (longArc := longArc) C hmin k <=
        (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
          (topology := topology) R.boundaryLength_ge_three C hmin k).value :=
  R.toCyclicNeighborGapRows.sectorLoad_le_boundarySectorAngle C hmin k

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Cyclic-neighbour gap rows plus W10's boundary-sector angle-sum package
produce the actual boundary-neighbour sector containment rows. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfCyclicNeighborGapRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (gapRows :
      SelectedTopologyBoundaryCyclicNeighborGapRows topology longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc :=
  selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndAngleSumRows
    (topology := topology) (longArc := longArc)
    gapRows.boundaryLength_ge_three
    (fun C hmin k =>
      gapRows.sectorLoad_le_boundarySectorAngle C hmin k)
    sectorAngleRows

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Local per-index interval rows plus the boundary sector-sum package produce
the actual boundary-neighbour sector-containment rows. -/
def toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc :=
  selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfCyclicNeighborGapRowsAndAngleSumRows
    R.toCyclicNeighborGapRows sectorAngleRows

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Actual boundary-neighbor sector rows feed the preferred sector-containment
surface by using the concrete sector values as the selected sector angles and
the generated local angle values as per-slot loads. -/
def selectedTopologyLocalAngleOuterFaceSectorContainmentRowsOfActualBoundaryNeighborSectorRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyActualBoundaryNeighborSectorContainmentRows
        topology longArc) :
    SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc where
  sectorAngle := fun C hmin k =>
    (sectorRows.boundarySector C hmin k).value
  sectorAngle_nonnegative := fun C hmin k =>
    BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value_nonnegative
      (sectorRows.boundarySector C hmin k)
  degree3Sector := fun C hmin =>
    sectorRows.degree3Sector C hmin
  degree4Sector := fun C hmin =>
    sectorRows.degree4Sector C hmin
  degree5Sector := fun C hmin =>
    sectorRows.degree5Sector C hmin
  degree6Sector := fun C hmin =>
    sectorRows.degree6Sector C hmin
  nontriangleSector := fun C hmin =>
    sectorRows.nontriangleSector C hmin
  longArcSector := fun C hmin =>
    sectorRows.longArcSector C hmin
  degree3SlotBudget := fun C hmin i slot =>
    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)).degree3 i slot).value
  degree4SlotBudget := fun C hmin i slot =>
    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)).degree4 i slot).value
  degree5SlotBudget := fun C hmin i slot =>
    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)).degree5 i slot).value
  degree6SlotBudget := fun C hmin i slot =>
    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)).degree6 i slot).value
  nontriangleSlotBudget := fun C hmin i slot =>
    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)).nontriangle i slot).value
  longArcSlotBudget := fun C hmin i slot =>
    ((selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)).longArc i slot).value
  degree3_slot_le_budget := fun _ _ _ _ => le_rfl
  degree4_slot_le_budget := fun _ _ _ _ => le_rfl
  degree5_slot_le_budget := fun _ _ _ _ => le_rfl
  degree6_slot_le_budget := fun _ _ _ _ => le_rfl
  nontriangle_slot_le_budget := fun _ _ _ _ => le_rfl
  longArc_slot_le_budget := fun _ _ _ _ => le_rfl
  sectorLoad_le_sectorAngle := fun C hmin k =>
    sectorRows.sectorLoad_le_boundarySectorAngle C hmin k
  sectorAngleSum_le_simplePolygonInteriorAngleSum := fun C hmin =>
    sectorRows.boundarySectorAngleSum_le_simplePolygonInteriorAngleSum C hmin

/-- Nonempty projection form of the actual boundary-neighbor sector
constructor. -/
theorem nonempty_selectedTopologyLocalAngleOuterFaceSectorContainmentRows_of_actualBoundaryNeighborSectorRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyActualBoundaryNeighborSectorContainmentRows
        topology longArc) :
    Nonempty
      (SelectedTopologyLocalAngleOuterFaceSectorContainmentRows
        topology longArc) :=
  Nonempty.intro
    (selectedTopologyLocalAngleOuterFaceSectorContainmentRowsOfActualBoundaryNeighborSectorRows
      (topology := topology) (longArc := longArc) sectorRows)

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Local per-index interval rows plus the boundary sector-sum package produce
selected local sector-containment rows. -/
def toLocalAngleOuterFaceSectorContainmentRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorContainmentRowsOfActualBoundaryNeighborSectorRows
    (topology := topology) (longArc := longArc)
    (R.toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows
      sectorAngleRows)

/-- Local per-index interval rows plus the genuine simple-polygon angle-sum
theorem produce actual boundary-neighbor sector rows with W10's matching
sector rows supplied canonically. -/
def toActualBoundaryNeighborSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows
      topology longArc :=
  selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndSimplePolygonInteriorAngleSumRows
    (topology := topology) (longArc := longArc)
    R.boundaryLength_ge_three
    (fun C hmin k => R.sectorLoad_le_boundarySectorAngle C hmin k)
    simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- Local per-index interval rows plus the genuine simple-polygon angle-sum
theorem produce the selected local sector-containment rows. -/
def toLocalAngleOuterFaceSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorContainmentRowsOfActualBoundaryNeighborSectorRows
    (topology := topology) (longArc := longArc)
    (R.toActualBoundaryNeighborSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
      simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum)

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows

/-- Topology-wide boundary-data rows produce the actual boundary-neighbor
sector-containment rows once W10 supplies the matching sector-sum package. -/
def toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        topology longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows topology longArc :=
  R.toRows.toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows
    sectorAngleRows

/-- Topology-wide boundary-data rows produce the selected local
sector-containment rows once W10 supplies the matching sector-sum package. -/
def toLocalAngleOuterFaceSectorContainmentRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        topology longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc :=
  R.toRows.toLocalAngleOuterFaceSectorContainmentRowsAndAngleSumRows
    sectorAngleRows

/-- Topology-wide boundary-data rows produce the actual boundary-neighbor
sector-containment rows from the simple-polygon angle-sum source. -/
def toActualBoundaryNeighborSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        topology longArc)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows topology longArc :=
  R.toRows.toActualBoundaryNeighborSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
    simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- Topology-wide boundary-data rows produce the selected local
sector-containment rows from the simple-polygon angle-sum source. -/
def toLocalAngleOuterFaceSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        topology longArc)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc :=
  R.toRows.toLocalAngleOuterFaceSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
    simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows

/-- Ordered unit-neighbor data plus slot-to-gap rows produce the actual
boundary-neighbor sector-containment rows once W10 supplies the matching
sector-sum package. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfOrderedUnitNeighborDataAndSlotToGapRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (endpointInterval :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
          ((topology C hmin).toOuterBoundaryCore.outerCycle) k)
    (orderedNeighbor :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexOrderedUnitNeighborData
          (topology := topology) C hmin k (endpointInterval C hmin k))
    (slotToGapRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborSlotToGapRows
          (topology := topology) (longArc := longArc)
          boundaryLength_ge_three C hmin k (endpointInterval C hmin k)
          (orderedNeighbor C hmin k))
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows topology longArc :=
  (SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows.ofOrderedUnitNeighborDataAndSlotToGapRows
    (topology := topology) (longArc := longArc)
    boundaryLength_ge_three endpointInterval orderedNeighbor
    slotToGapRows).toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows
      sectorAngleRows

/-- Ordered unit-neighbor data plus slot-to-gap rows produce the actual
boundary-neighbor sector-containment rows from the simple-polygon angle-sum
source. -/
def selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfOrderedUnitNeighborDataAndSlotToGapRowsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (endpointInterval :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
          ((topology C hmin).toOuterBoundaryCore.outerCycle) k)
    (orderedNeighbor :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexOrderedUnitNeighborData
          (topology := topology) C hmin k (endpointInterval C hmin k))
    (slotToGapRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborSlotToGapRows
          (topology := topology) (longArc := longArc)
          boundaryLength_ge_three C hmin k (endpointInterval C hmin k)
          (orderedNeighbor C hmin k))
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyActualBoundaryNeighborSectorContainmentRows topology longArc :=
  (SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows.ofOrderedUnitNeighborDataAndSlotToGapRows
    (topology := topology) (longArc := longArc)
    boundaryLength_ge_three endpointInterval orderedNeighbor
    slotToGapRows).toActualBoundaryNeighborSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
      simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- The generated local angle mass is contained in the selected sector sum
when every generated angle slot is assigned to a sector and the per-sector
assigned loads fit into their sector angles. -/
theorem selectedTopologyLocalAngleOuterFaceSectorContainmentRows_accountedAngleSum_le_sectorSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        Finset.sum Finset.univ (sectorRows.sectorAngle C hmin) := by
  classical
  let D :=
    selectedClassificationOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)
  let L :=
    selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)
  let degree3Budget : D.degree3Indices -> Real := fun i =>
    Finset.sum (Finset.univ : Finset (Fin 2))
      (fun slot => sectorRows.degree3SlotBudget C hmin i slot)
  let degree4Budget : D.degree4Indices -> Real := fun i =>
    Finset.sum (Finset.univ : Finset (Fin 3))
      (fun slot => sectorRows.degree4SlotBudget C hmin i slot)
  let degree5Budget : D.degree5Indices -> Real := fun i =>
    Finset.sum (Finset.univ : Finset (Fin 4))
      (fun slot => sectorRows.degree5SlotBudget C hmin i slot)
  let degree6Budget : D.degree6Indices -> Real := fun i =>
    Finset.sum (Finset.univ : Finset (Fin 5))
      (fun slot => sectorRows.degree6SlotBudget C hmin i slot)
  let nontriangleBudget : D.nontriangleEdgeIndices -> Real := fun i =>
    Finset.sum (Finset.univ : Finset (Fin 1))
      (fun slot => sectorRows.nontriangleSlotBudget C hmin i slot)
  let longArcBudget : D.longArcIndices -> Real := fun i =>
    Finset.sum (Finset.univ : Finset (Fin 1))
      (fun slot => sectorRows.longArcSlotBudget C hmin i slot)
  have hdegree3 :
      forall i : D.degree3Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree3 i) <= degree3Budget i := by
    intro i
    change
      Finset.sum (Finset.univ : Finset (Fin 2))
          (fun slot => (L.degree3 i slot).value) <= degree3Budget i
    exact
      Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin 2)))
        (fun slot _hslot =>
          sectorRows.degree3_slot_le_budget C hmin i slot)
  have hdegree4 :
      forall i : D.degree4Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree4 i) <= degree4Budget i := by
    intro i
    change
      Finset.sum (Finset.univ : Finset (Fin 3))
          (fun slot => (L.degree4 i slot).value) <= degree4Budget i
    exact
      Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin 3)))
        (fun slot _hslot =>
          sectorRows.degree4_slot_le_budget C hmin i slot)
  have hdegree5 :
      forall i : D.degree5Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree5 i) <= degree5Budget i := by
    intro i
    change
      Finset.sum (Finset.univ : Finset (Fin 4))
          (fun slot => (L.degree5 i slot).value) <= degree5Budget i
    exact
      Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin 4)))
        (fun slot _hslot =>
          sectorRows.degree5_slot_le_budget C hmin i slot)
  have hdegree6 :
      forall i : D.degree6Indices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.degree6 i) <= degree6Budget i := by
    intro i
    change
      Finset.sum (Finset.univ : Finset (Fin 5))
          (fun slot => (L.degree6 i slot).value) <= degree6Budget i
    exact
      Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin 5)))
        (fun slot _hslot =>
          sectorRows.degree6_slot_le_budget C hmin i slot)
  have hnontriangle :
      forall i : D.nontriangleEdgeIndices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.nontriangle i) <= nontriangleBudget i := by
    intro i
    change
      Finset.sum (Finset.univ : Finset (Fin 1))
          (fun slot => (L.nontriangle i slot).value) <= nontriangleBudget i
    exact
      Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin 1)))
        (fun slot _hslot =>
          sectorRows.nontriangle_slot_le_budget C hmin i slot)
  have hlongArc :
      forall i : D.longArcIndices,
        BoundaryCountingInstantiationW10.ClassifiedBoundary.angleMassValue
            (L.longArc i) <= longArcBudget i := by
    intro i
    change
      Finset.sum (Finset.univ : Finset (Fin 1))
          (fun slot => (L.longArc i slot).value) <= longArcBudget i
    exact
      Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin 1)))
        (fun slot _hslot =>
          sectorRows.longArc_slot_le_budget C hmin i slot)
  have hlocal :
      L.accountedAngleSum <=
        Finset.sum Finset.univ degree3Budget +
          Finset.sum Finset.univ degree4Budget +
          Finset.sum Finset.univ degree5Budget +
          Finset.sum Finset.univ degree6Budget +
          Finset.sum Finset.univ nontriangleBudget +
          Finset.sum Finset.univ longArcBudget :=
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_sum_angleMassBudgets
      L degree3Budget degree4Budget degree5Budget degree6Budget
      nontriangleBudget longArcBudget hdegree3 hdegree4 hdegree5 hdegree6
      hnontriangle hlongArc
  let load3 :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
    fun k =>
      Finset.sum Finset.univ
        (fun i : D.degree3Indices =>
          Finset.sum (Finset.univ : Finset (Fin 2))
            (fun slot =>
              if sectorRows.degree3Sector C hmin i slot = k then
                sectorRows.degree3SlotBudget C hmin i slot
              else
                0))
  let load4 :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
    fun k =>
      Finset.sum Finset.univ
        (fun i : D.degree4Indices =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun slot =>
              if sectorRows.degree4Sector C hmin i slot = k then
                sectorRows.degree4SlotBudget C hmin i slot
              else
                0))
  let load5 :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
    fun k =>
      Finset.sum Finset.univ
        (fun i : D.degree5Indices =>
          Finset.sum (Finset.univ : Finset (Fin 4))
            (fun slot =>
              if sectorRows.degree5Sector C hmin i slot = k then
                sectorRows.degree5SlotBudget C hmin i slot
              else
                0))
  let load6 :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
    fun k =>
      Finset.sum Finset.univ
        (fun i : D.degree6Indices =>
          Finset.sum (Finset.univ : Finset (Fin 5))
            (fun slot =>
              if sectorRows.degree6Sector C hmin i slot = k then
                sectorRows.degree6SlotBudget C hmin i slot
              else
                0))
  let loadb :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
    fun k =>
      Finset.sum Finset.univ
        (fun i : D.nontriangleEdgeIndices =>
          Finset.sum (Finset.univ : Finset (Fin 1))
            (fun slot =>
              if sectorRows.nontriangleSector C hmin i slot = k then
                sectorRows.nontriangleSlotBudget C hmin i slot
              else
                0))
  let loadB :
      Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
    fun k =>
      Finset.sum Finset.univ
        (fun i : D.longArcIndices =>
          Finset.sum (Finset.univ : Finset (Fin 1))
            (fun slot =>
              if sectorRows.longArcSector C hmin i slot = k then
                sectorRows.longArcSlotBudget C hmin i slot
              else
                0))
  have hload_le :
      Finset.sum Finset.univ
          (fun k => load3 k + load4 k + load5 k + load6 k +
            loadb k + loadB k) <=
        Finset.sum Finset.univ (sectorRows.sectorAngle C hmin) := by
    exact Finset.sum_le_sum
      (s := Finset.univ)
      (fun k _hk => by
        exact sectorRows.sectorLoad_le_sectorAngle C hmin k)
  have h3 :
      Finset.sum Finset.univ load3 =
        Finset.sum Finset.univ degree3Budget := by
    exact
      finiteSectorIndicatorSum_two_eq_total
        (sectorOf := sectorRows.degree3Sector C hmin)
        (weight := sectorRows.degree3SlotBudget C hmin)
  have h4 :
      Finset.sum Finset.univ load4 =
        Finset.sum Finset.univ degree4Budget := by
    exact
      finiteSectorIndicatorSum_two_eq_total
        (sectorOf := sectorRows.degree4Sector C hmin)
        (weight := sectorRows.degree4SlotBudget C hmin)
  have h5 :
      Finset.sum Finset.univ load5 =
        Finset.sum Finset.univ degree5Budget := by
    exact
      finiteSectorIndicatorSum_two_eq_total
        (sectorOf := sectorRows.degree5Sector C hmin)
        (weight := sectorRows.degree5SlotBudget C hmin)
  have h6 :
      Finset.sum Finset.univ load6 =
        Finset.sum Finset.univ degree6Budget := by
    exact
      finiteSectorIndicatorSum_two_eq_total
        (sectorOf := sectorRows.degree6Sector C hmin)
        (weight := sectorRows.degree6SlotBudget C hmin)
  have hb :
      Finset.sum Finset.univ loadb =
        Finset.sum Finset.univ nontriangleBudget := by
    exact
      finiteSectorIndicatorSum_two_eq_total
        (sectorOf := sectorRows.nontriangleSector C hmin)
        (weight := sectorRows.nontriangleSlotBudget C hmin)
  have hB :
      Finset.sum Finset.univ loadB =
        Finset.sum Finset.univ longArcBudget := by
    exact
      finiteSectorIndicatorSum_two_eq_total
        (sectorOf := sectorRows.longArcSector C hmin)
        (weight := sectorRows.longArcSlotBudget C hmin)
  have hload_eq :
      Finset.sum Finset.univ
          (fun k => load3 k + load4 k + load5 k + load6 k +
            loadb k + loadB k) =
        Finset.sum Finset.univ degree3Budget +
          Finset.sum Finset.univ degree4Budget +
          Finset.sum Finset.univ degree5Budget +
          Finset.sum Finset.univ degree6Budget +
          Finset.sum Finset.univ nontriangleBudget +
          Finset.sum Finset.univ longArcBudget := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, h3, h4, h5, h6, hb, hB]
  have hbudget :
      Finset.sum Finset.univ degree3Budget +
          Finset.sum Finset.univ degree4Budget +
          Finset.sum Finset.univ degree5Budget +
          Finset.sum Finset.univ degree6Budget +
          Finset.sum Finset.univ nontriangleBudget +
          Finset.sum Finset.univ longArcBudget <=
        Finset.sum Finset.univ (sectorRows.sectorAngle C hmin) := by
    rw [← hload_eq]
    exact hload_le
  exact le_trans hlocal hbudget

/-- Sector containment rows supply the existing sector/order surface by
forgetting the per-slot assignments after proving the generated local rows are
contained in the selected sector sum. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfSectorContainmentRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorContainmentRows topology longArc) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc where
  sectorAngle := fun C hmin =>
    sectorRows.sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    sectorRows.sectorAngle_nonnegative C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
    selectedTopologyLocalAngleOuterFaceSectorContainmentRows_accountedAngleSum_le_sectorSum
      (topology := topology) (longArc := longArc) sectorRows C hmin
  orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum := fun C hmin =>
    sectorRows.sectorAngleSum_le_simplePolygonInteriorAngleSum C hmin

namespace SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- Local per-index interval rows plus the boundary sector-sum package produce
the selected outer-face sector/order rows. -/
def toLocalAngleOuterFaceSectorOrderRowsAndAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfSectorContainmentRows
    (topology := topology) (longArc := longArc)
    (R.toLocalAngleOuterFaceSectorContainmentRowsAndAngleSumRows
      sectorAngleRows)

/-- Local per-index interval rows plus the genuine simple-polygon angle-sum
theorem produce the selected outer-face sector/order rows with matching W10
sector rows supplied canonically. -/
def toLocalAngleOuterFaceSectorOrderRowsAndSimplePolygonInteriorAngleSumRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (R : SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows topology longArc)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore) <=
            BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfSectorContainmentRows
    (topology := topology) (longArc := longArc)
    (R.toLocalAngleOuterFaceSectorContainmentRowsAndSimplePolygonInteriorAngleSumRows
      simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum)

end SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows

/-- The simple-polygon sector-sum bound exposed by ordered outer-face sector
rows.  This is the scalar simple-polygon side of the S3 sector-order
obligation, separated from the local-angle containment inequality. -/
theorem selectedTopologyLocalAngleOuterFaceSectorOrderRows_sectorSum_le_simpleOuterPolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      Finset.sum Finset.univ (sectorRows.sectorAngle C hmin) <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
  sectorRows.orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum C hmin

/-- Ordered/disjoint outer-face sector rows feed the generated scalar
accounting inequality: local accounted mass is contained in the ordered sector
sum, and that sector sum is bounded by the simple-polygon interior-angle sum. -/
theorem selectedTopologyLocalAngleOuterFaceSectorOrderRows_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
  le_trans
    (sectorRows.localRows_le_orderedOuterFaceSectorSum C hmin)
    (selectedTopologyLocalAngleOuterFaceSectorOrderRows_sectorSum_le_simpleOuterPolygonInteriorAngleSum
      sectorRows C hmin)

/-- Faraday's exact S3 angle inequality from explicit ordered/disjoint
outer-face sector rows.  The first row is the local-sector containment and the
second is the simple-polygon bound for the ordered sector sum. -/
theorem selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceSectorOrder
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
  selectedTopologyLocalAngleOuterFaceSectorOrderRows_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    sectorRows C hmin

/-- The first selected boundary index, available from nondegeneracy. -/
def selectedTopologyFirstBoundaryIndex
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3)
    (boundaryLength_ge_three C hmin)⟩

/-- A concrete sector-angle row determined only by the classified boundary
count data: place the whole simple-polygon sector mass at the first boundary
slot and zero elsewhere.  This closes the arithmetic sector fields without
choosing any additional wrapper around `SelectedTopologyLocalAngleOuterFaceSectorOrderRows`. -/
def selectedTopologyBoundaryCycleSectorAngle
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real :=
  fun k =>
    if k = selectedTopologyFirstBoundaryIndex
        (topology := topology) boundaryLength_ge_three C hmin then
      simpleOuterPolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore)
    else
      0

theorem selectedTopologyBoundaryCycleSectorAngle_nonnegative
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)) :
    0 <=
      selectedTopologyBoundaryCycleSectorAngle
        (topology := topology) boundaryLength_ge_three C hmin k := by
  classical
  unfold selectedTopologyBoundaryCycleSectorAngle
  split
  · exact
      simpleOuterPolygonInteriorAngleSum_nonnegative_of_length_ge_two
        ((topology C hmin).toOuterBoundaryCore)
        (Nat.le_trans (by decide : 2 <= 3)
          (boundaryLength_ge_three C hmin))
  · exact le_rfl

theorem selectedTopologyBoundaryCycleSectorAngle_sum_eq_simpleOuterPolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Finset.sum Finset.univ
        (selectedTopologyBoundaryCycleSectorAngle
          (topology := topology) boundaryLength_ge_three C hmin) =
      simpleOuterPolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore) := by
  classical
  let first :=
    selectedTopologyFirstBoundaryIndex
      (topology := topology) boundaryLength_ge_three C hmin
  change
    Finset.sum Finset.univ
        (fun k =>
          if k = first then
            simpleOuterPolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore)
          else
            0) =
      simpleOuterPolygonInteriorAngleSum
        ((topology C hmin).toOuterBoundaryCore)
  rw [Finset.sum_eq_single first]
  · rw [if_pos rfl]
  · intro k _hk hk
    rw [if_neg hk]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ first))

/-- Directly inhabit the exact sector/order row fields from nondegenerate
selected topology and the generated accounted-angle bound.  The `longArc`
predicate is the one supplied to the generated classification; no additional
adapter structure is introduced. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfBoundaryCycleAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc where
  sectorAngle := fun C hmin =>
    selectedTopologyBoundaryCycleSectorAngle
      (topology := topology) boundaryLength_ge_three C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    selectedTopologyBoundaryCycleSectorAngle_nonnegative
      (topology := topology) boundaryLength_ge_three C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin => by
    rw [selectedTopologyBoundaryCycleSectorAngle_sum_eq_simpleOuterPolygonInteriorAngleSum
      (topology := topology) boundaryLength_ge_three C hmin]
    exact accounted_le_simpleOuterPolygonInteriorAngleSum C hmin
  orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum := fun C hmin => by
    rw [selectedTopologyBoundaryCycleSectorAngle_sum_eq_simpleOuterPolygonInteriorAngleSum
      (topology := topology) boundaryLength_ge_three C hmin]

/-- Direct sector/order constructor when the only missing containment field is
the angle-mass budget inequality. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfAngleMassBudgetRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (budgetRows : SelectedTopologyLocalAngleMassBudgetRows topology longArc)
    (sectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real)
    (sectorAngle_nonnegative :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
        (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
          0 <= sectorAngle C hmin k)
    (budgetSum_le_orderedOuterFaceSectorSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Finset.sum Finset.univ (budgetRows.degree3Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.degree4Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.degree5Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.degree6Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.nontriangleBudget C hmin) +
              Finset.sum Finset.univ (budgetRows.longArcBudget C hmin) <=
            Finset.sum Finset.univ (sectorAngle C hmin))
    (orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Finset.sum Finset.univ (sectorAngle C hmin) <=
            simpleOuterPolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc where
  sectorAngle := fun C hmin =>
    sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    sectorAngle_nonnegative C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
    le_trans
      (selectedTopologyLocalAngleMassBudgetRows_accountedAngleSum_le_budgetSum
        (topology := topology) (longArc := longArc) budgetRows C hmin)
      (budgetSum_le_orderedOuterFaceSectorSum C hmin)
  orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum := fun C hmin =>
    orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum C hmin

/-- Exact finite triangulation rows behind the selected outer-face sector
angle-sum source.  The geometry still required is explicit:

* a finite triangle index type for each selected boundary,
* `length - 2` triangles,
* three corner angles per triangle summing to `π`,
* a decomposition of the ordered outer-face sector sum as the sum of those
  triangle corner angles,
* and the containment/disjointness comparison from the generated local rows to
  those ordered sectors.

This is intentionally only a local theorem surface; it does not pretend that
Mathlib already has a simple-polygon triangulation theorem. -/
structure SelectedTopologyLocalAngleOuterFaceTriangulationRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  Triangle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C), Type
  triangleFintype :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fintype (Triangle C hmin)
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  triangleCount_eq_boundaryLength_sub_two :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        letI := triangleFintype C hmin
        Fintype.card (Triangle C hmin) =
          (topology C hmin).toOuterBoundaryCore.outerCycle.length - 2
  triangleAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Triangle C hmin -> Fin 3 -> Real
  triangleAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (T : Triangle C hmin) (corner : Fin 3),
        0 <= triangleAngle C hmin T corner
  triangleAngleSum_eq_pi :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (T : Triangle C hmin),
        Finset.sum (Finset.univ : Finset (Fin 3))
            (triangleAngle C hmin T) =
          Real.pi
  sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real
  sectorAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        0 <= sectorAngle C hmin k
  localRows_le_orderedOuterFaceSectorSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
          Finset.sum Finset.univ (sectorAngle C hmin)
  orderedOuterFaceSectorSum_eq_triangulationAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        letI := triangleFintype C hmin
        Finset.sum Finset.univ (sectorAngle C hmin) =
          Finset.sum Finset.univ
            (fun T : Triangle C hmin =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (triangleAngle C hmin T))

/-- Finite simple-polygon sector-sum lemma for selected triangulation rows:
the ordered outer-face sector sum is exactly the triangle-angle sum, and the
triangulation has `length - 2` triangles each contributing `pi`. -/
theorem selectedTopologyLocalAngleOuterFaceTriangulationRows_orderedOuterFaceSectorSum_eq_simplePolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      Finset.sum Finset.univ (triangulationRows.sectorAngle C hmin) =
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) := by
  classical
  letI := triangulationRows.triangleFintype C hmin
  rw [triangulationRows.orderedOuterFaceSectorSum_eq_triangulationAngleSum
    C hmin]
  exact
    finiteTriangleAngleSum_eq_simpleOuterPolygonInteriorAngleSum
      ((topology C hmin).toOuterBoundaryCore)
      (Nat.le_trans (by norm_num)
        (triangulationRows.boundaryLength_ge_three C hmin))
      (triangulationRows.triangleCount_eq_boundaryLength_sub_two C hmin)
      (triangulationRows.triangleAngle C hmin)
      (triangulationRows.triangleAngleSum_eq_pi C hmin)

theorem selectedTopologyLocalAngleOuterFaceTriangulationRows_orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      Finset.sum Finset.univ (triangulationRows.sectorAngle C hmin) <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
  le_of_eq
    (selectedTopologyLocalAngleOuterFaceTriangulationRows_orderedOuterFaceSectorSum_eq_simplePolygonInteriorAngleSum
      triangulationRows C hmin)

/-- Finite triangulation rows imply the existing selected outer-face
sector/order rows. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfTriangulationRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationRows topology longArc) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc where
  sectorAngle := fun C hmin =>
    triangulationRows.sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    triangulationRows.sectorAngle_nonnegative C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
    triangulationRows.localRows_le_orderedOuterFaceSectorSum C hmin
  orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum := fun C hmin =>
    selectedTopologyLocalAngleOuterFaceTriangulationRows_orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum
      triangulationRows C hmin

/-- Finite triangulation rows imply Faraday's exact generated local-angle
inequality by first supplying the ordered/disjoint sector rows. -/
theorem selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceTriangulationRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
  selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceSectorOrder
    (selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfTriangulationRows
      triangulationRows)
    C hmin

/-- Triangulation rows where the local-row containment field is supplied by
concrete angle-mass budgets.  The package keeps the triangulation angle data
and also requires the classified budget mass to fit inside the ordered
outer-face sector sum; the triangle angle-sum equality is then used only for
the simple-polygon sector-sum bound. -/
structure SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    : Type 1
    extends SelectedTopologyLocalAngleMassBudgetRows topology longArc where
  Triangle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C), Type
  triangleFintype :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fintype (Triangle C hmin)
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  triangleCount_eq_boundaryLength_sub_two :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        letI := triangleFintype C hmin
        Fintype.card (Triangle C hmin) =
          (topology C hmin).toOuterBoundaryCore.outerCycle.length - 2
  triangleAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Triangle C hmin -> Fin 3 -> Real
  triangleAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (T : Triangle C hmin) (corner : Fin 3),
        0 <= triangleAngle C hmin T corner
  triangleAngleSum_eq_pi :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (T : Triangle C hmin),
        Finset.sum (Finset.univ : Finset (Fin 3))
            (triangleAngle C hmin T) =
          Real.pi
  sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real
  sectorAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        0 <= sectorAngle C hmin k
  budgetSum_le_orderedOuterFaceSectorSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (degree3Budget C hmin) +
            Finset.sum Finset.univ (degree4Budget C hmin) +
            Finset.sum Finset.univ (degree5Budget C hmin) +
            Finset.sum Finset.univ (degree6Budget C hmin) +
            Finset.sum Finset.univ (nontriangleBudget C hmin) +
            Finset.sum Finset.univ (longArcBudget C hmin) <=
          Finset.sum Finset.univ (sectorAngle C hmin)
  orderedOuterFaceSectorSum_eq_triangulationAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        letI := triangleFintype C hmin
        Finset.sum Finset.univ (sectorAngle C hmin) =
          Finset.sum Finset.univ
            (fun T : Triangle C hmin =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (triangleAngle C hmin T))

theorem selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_orderedOuterFaceSectorSum_eq_simpleOuterPolygonInteriorAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
        topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      Finset.sum Finset.univ (triangulationRows.sectorAngle C hmin) =
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) := by
  classical
  letI := triangulationRows.triangleFintype C hmin
  calc
    Finset.sum Finset.univ (triangulationRows.sectorAngle C hmin) =
        Finset.sum Finset.univ
          (fun T : triangulationRows.Triangle C hmin =>
            Finset.sum (Finset.univ : Finset (Fin 3))
              (triangulationRows.triangleAngle C hmin T)) := by
      exact
        triangulationRows.orderedOuterFaceSectorSum_eq_triangulationAngleSum
          C hmin
    _ = simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) := by
      exact
        finiteTriangleAngleSum_eq_simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore)
          (Nat.le_trans (by norm_num)
            (triangulationRows.boundaryLength_ge_three C hmin))
          (triangulationRows.triangleCount_eq_boundaryLength_sub_two C hmin)
          (triangulationRows.triangleAngle C hmin)
          (triangulationRows.triangleAngleSum_eq_pi C hmin)

theorem selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_localRows_le_orderedOuterFaceSectorSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
        topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        Finset.sum Finset.univ (triangulationRows.sectorAngle C hmin) := by
  exact
    le_trans
      (selectedTopologyLocalAngleMassBudgetRows_accountedAngleSum_le_budgetSum
        (topology := topology) (longArc := longArc)
        triangulationRows.toSelectedTopologyLocalAngleMassBudgetRows C hmin)
      (triangulationRows.budgetSum_le_orderedOuterFaceSectorSum C hmin)

/-- Concrete angle-mass budgeted triangulation rows supply the existing
triangulation surface by closing its local-row containment field. -/
def selectedTopologyLocalAngleOuterFaceTriangulationRowsOfAngleMassBudgetRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
        topology longArc) :
    SelectedTopologyLocalAngleOuterFaceTriangulationRows topology longArc where
  Triangle := fun C hmin =>
    triangulationRows.Triangle C hmin
  triangleFintype := fun C hmin =>
    triangulationRows.triangleFintype C hmin
  boundaryLength_ge_three := fun C hmin =>
    triangulationRows.boundaryLength_ge_three C hmin
  triangleCount_eq_boundaryLength_sub_two := fun C hmin =>
    triangulationRows.triangleCount_eq_boundaryLength_sub_two C hmin
  triangleAngle := fun C hmin =>
    triangulationRows.triangleAngle C hmin
  triangleAngle_nonnegative := fun C hmin T corner =>
    triangulationRows.triangleAngle_nonnegative C hmin T corner
  triangleAngleSum_eq_pi := fun C hmin T =>
    triangulationRows.triangleAngleSum_eq_pi C hmin T
  sectorAngle := fun C hmin =>
    triangulationRows.sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    triangulationRows.sectorAngle_nonnegative C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
    selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_localRows_le_orderedOuterFaceSectorSum
      triangulationRows C hmin
  orderedOuterFaceSectorSum_eq_triangulationAngleSum := fun C hmin =>
    triangulationRows.orderedOuterFaceSectorSum_eq_triangulationAngleSum C hmin

/-- Concrete angle-mass budgeted triangulation rows supply the selected
sector/order rows. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfTriangulationAngleMassBudgetRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
        topology longArc) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfTriangulationRows
    (selectedTopologyLocalAngleOuterFaceTriangulationRowsOfAngleMassBudgetRows
      triangulationRows)

/-- Direct budgeted triangulation rows from the generated exact local angle
mass budget and the selected simple-polygon sector sum.

The inherited budget rows are exact: each classified budget is the actual
generated local angle mass.  The `budgetSum_le_orderedOuterFaceSectorSum`
field is proved by rewriting the ordered sector sum to the selected
simple-polygon interior-angle sum, so the row inhabits the triangulation
angle-mass surface itself rather than a wrapper around it. -/
def selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (boundaryLength_ge_three :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length)
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((topology C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
      topology longArc := by
  classical
  let budgetRows :
      SelectedTopologyLocalAngleMassBudgetRows topology longArc :=
    selectedTopologyLocalAngleMassBudgetRowsOfGeneratedAccountedAngleSum
      (topology := topology) (longArc := longArc)
      accounted_le_simpleOuterPolygonInteriorAngleSum
  refine
    { toSelectedTopologyLocalAngleMassBudgetRows := budgetRows
      Triangle := fun C hmin =>
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2)
      triangleFintype := fun _ _ => inferInstance
      boundaryLength_ge_three := fun C hmin =>
        boundaryLength_ge_three C hmin
      triangleCount_eq_boundaryLength_sub_two := fun _ _ =>
        Fintype.card_fin _
      triangleAngle := fun _ _ _ _ => Real.pi / 3
      triangleAngle_nonnegative := ?_
      triangleAngleSum_eq_pi := ?_
      sectorAngle := fun C hmin =>
        selectedTopologyBoundaryCycleSectorAngle
          (topology := topology) boundaryLength_ge_three C hmin
      sectorAngle_nonnegative := fun C hmin k =>
        selectedTopologyBoundaryCycleSectorAngle_nonnegative
          (topology := topology) boundaryLength_ge_three C hmin k
      budgetSum_le_orderedOuterFaceSectorSum := ?_
      orderedOuterFaceSectorSum_eq_triangulationAngleSum := ?_ }
  · intro _ _ _ _ _
    exact constantPiDivThreeTriangleAngle_nonnegative
  · intro _ _ _ _
    exact constantPiDivThreeTriangleAngleSum_eq_pi
  · intro n C hmin
    change
      Finset.sum Finset.univ (budgetRows.degree3Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.degree4Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.degree5Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.degree6Budget C hmin) +
          Finset.sum Finset.univ (budgetRows.nontriangleBudget C hmin) +
          Finset.sum Finset.univ (budgetRows.longArcBudget C hmin) <=
        Finset.sum Finset.univ
          (selectedTopologyBoundaryCycleSectorAngle
            (topology := topology) boundaryLength_ge_three C hmin)
    rw [selectedTopologyBoundaryCycleSectorAngle_sum_eq_simpleOuterPolygonInteriorAngleSum
      (topology := topology) boundaryLength_ge_three C hmin]
    exact budgetRows.budgetSum_le_simpleOuterPolygonInteriorAngleSum C hmin
  · intro n C hmin
    let core := (topology C hmin).toOuterBoundaryCore
    have hsector :
        Finset.sum Finset.univ
            (selectedTopologyBoundaryCycleSectorAngle
              (topology := topology) boundaryLength_ge_three C hmin) =
          simpleOuterPolygonInteriorAngleSum core := by
      exact
        selectedTopologyBoundaryCycleSectorAngle_sum_eq_simpleOuterPolygonInteriorAngleSum
          (topology := topology) boundaryLength_ge_three C hmin
    have htri :
        Finset.sum Finset.univ
            (fun T : Fin (core.outerCycle.length - 2) =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (fun _ : Fin 3 => Real.pi / 3)) =
          simpleOuterPolygonInteriorAngleSum core := by
      exact
        finiteTriangleAngleSum_eq_simpleOuterPolygonInteriorAngleSum
          core
          (Nat.le_trans (by decide : 2 <= 3)
            (boundaryLength_ge_three C hmin))
          (Fintype.card_fin _)
          (fun (_ : Fin (core.outerCycle.length - 2))
            (_ : Fin 3) => Real.pi / 3)
          (fun _ => constantPiDivThreeTriangleAngleSum_eq_pi)
    exact hsector.trans htri.symm

/-- Exact ear-decomposition specialization of the triangulation rows.  The
triangle index is fixed to `Fin (length - 2)`, so the triangle count is
definitional after the boundary length is chosen; all geometric content remains
in the explicit ear corner angle sums and sector decomposition. -/
structure SelectedTopologyLocalAngleOuterFaceEarDecompositionRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop) :
    Type 1 where
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  earAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2) ->
          Fin 3 -> Real
  earAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (ear :
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2))
      (corner : Fin 3),
        0 <= earAngle C hmin ear corner
  earAngleSum_eq_pi :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (ear :
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2)),
        Finset.sum (Finset.univ : Finset (Fin 3))
            (earAngle C hmin ear) =
          Real.pi
  sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real
  sectorAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        0 <= sectorAngle C hmin k
  localRows_le_orderedOuterFaceSectorSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
          Finset.sum Finset.univ (sectorAngle C hmin)
  orderedOuterFaceSectorSum_eq_earAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (sectorAngle C hmin) =
          Finset.sum Finset.univ
            (fun ear :
              Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2) =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (earAngle C hmin ear))

/-- Ear-decomposition rows are triangulation rows with the triangle index fixed
to the finite ear list. -/
def selectedTopologyLocalAngleOuterFaceTriangulationRowsOfEarDecompositionRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionRows topology longArc) :
    SelectedTopologyLocalAngleOuterFaceTriangulationRows topology longArc where
  Triangle := fun C hmin =>
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2)
  triangleFintype := fun _ _ => inferInstance
  boundaryLength_ge_three := fun C hmin =>
    earRows.boundaryLength_ge_three C hmin
  triangleCount_eq_boundaryLength_sub_two := fun _ _ =>
    Fintype.card_fin _
  triangleAngle := fun C hmin =>
    earRows.earAngle C hmin
  triangleAngle_nonnegative := fun C hmin T corner =>
    earRows.earAngle_nonnegative C hmin T corner
  triangleAngleSum_eq_pi := fun C hmin T =>
    earRows.earAngleSum_eq_pi C hmin T
  sectorAngle := fun C hmin =>
    earRows.sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    earRows.sectorAngle_nonnegative C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
    earRows.localRows_le_orderedOuterFaceSectorSum C hmin
  orderedOuterFaceSectorSum_eq_triangulationAngleSum := fun C hmin =>
    by
      simpa only [Fintype.card_fin] using
        earRows.orderedOuterFaceSectorSum_eq_earAngleSum C hmin

/-- Ear-decomposition rows imply the existing selected outer-face sector/order
rows via the finite triangulation aggregation. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfEarDecompositionRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionRows topology longArc) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfTriangulationRows
    (selectedTopologyLocalAngleOuterFaceTriangulationRowsOfEarDecompositionRows
      earRows)

/-- Ear-decomposition rows imply Faraday's exact generated local-angle
inequality through the finite triangulation surface. -/
theorem selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceEarDecompositionRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        simpleOuterPolygonInteriorAngleSum
          ((topology C hmin).toOuterBoundaryCore) :=
  selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceTriangulationRows
    (selectedTopologyLocalAngleOuterFaceTriangulationRowsOfEarDecompositionRows
      earRows)
    C hmin

/-- Ear-decomposition rows where concrete angle-mass budgets close the
local-row containment field by fitting directly into the ordered outer-face
sector sum. -/
structure SelectedTopologyLocalAngleOuterFaceEarDecompositionAngleMassBudgetRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    : Type 1
    extends SelectedTopologyLocalAngleMassBudgetRows topology longArc where
  boundaryLength_ge_three :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        3 <= (topology C hmin).toOuterBoundaryCore.outerCycle.length
  earAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2) ->
          Fin 3 -> Real
  earAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (ear :
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2))
      (corner : Fin 3),
        0 <= earAngle C hmin ear corner
  earAngleSum_eq_pi :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (ear :
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2)),
        Finset.sum (Finset.univ : Finset (Fin 3))
            (earAngle C hmin ear) =
          Real.pi
  sectorAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Real
  sectorAngle_nonnegative :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length)),
        0 <= sectorAngle C hmin k
  budgetSum_le_orderedOuterFaceSectorSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (degree3Budget C hmin) +
            Finset.sum Finset.univ (degree4Budget C hmin) +
            Finset.sum Finset.univ (degree5Budget C hmin) +
            Finset.sum Finset.univ (degree6Budget C hmin) +
            Finset.sum Finset.univ (nontriangleBudget C hmin) +
            Finset.sum Finset.univ (longArcBudget C hmin) <=
          Finset.sum Finset.univ (sectorAngle C hmin)
  orderedOuterFaceSectorSum_eq_earAngleSum :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ (sectorAngle C hmin) =
          Finset.sum Finset.univ
            (fun ear :
              Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2) =>
              Finset.sum (Finset.univ : Finset (Fin 3))
                (earAngle C hmin ear))

/-- Budgeted ear rows are budgeted triangulation rows with the triangle index
fixed to the finite ear list. -/
def selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfEarDecompositionAngleMassBudgetRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionAngleMassBudgetRows
        topology longArc) :
    SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
      topology longArc where
  toSelectedTopologyLocalAngleMassBudgetRows :=
    earRows.toSelectedTopologyLocalAngleMassBudgetRows
  Triangle := fun C hmin =>
    Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length - 2)
  triangleFintype := fun _ _ => inferInstance
  boundaryLength_ge_three := fun C hmin =>
    earRows.boundaryLength_ge_three C hmin
  triangleCount_eq_boundaryLength_sub_two := fun _ _ =>
    Fintype.card_fin _
  triangleAngle := fun C hmin =>
    earRows.earAngle C hmin
  triangleAngle_nonnegative := fun C hmin T corner =>
    earRows.earAngle_nonnegative C hmin T corner
  triangleAngleSum_eq_pi := fun C hmin T =>
    earRows.earAngleSum_eq_pi C hmin T
  sectorAngle := fun C hmin =>
    earRows.sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    earRows.sectorAngle_nonnegative C hmin k
  budgetSum_le_orderedOuterFaceSectorSum := fun C hmin =>
    earRows.budgetSum_le_orderedOuterFaceSectorSum C hmin
  orderedOuterFaceSectorSum_eq_triangulationAngleSum := fun C hmin =>
    by
      simpa only [Fintype.card_fin] using
        earRows.orderedOuterFaceSectorSum_eq_earAngleSum C hmin

/-- Concrete angle-mass budgeted ear rows supply the existing
ear-decomposition surface by closing its local-row containment field. -/
def selectedTopologyLocalAngleOuterFaceEarDecompositionRowsOfAngleMassBudgetRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionAngleMassBudgetRows
        topology longArc) :
    SelectedTopologyLocalAngleOuterFaceEarDecompositionRows topology longArc where
  boundaryLength_ge_three := fun C hmin =>
    earRows.boundaryLength_ge_three C hmin
  earAngle := fun C hmin =>
    earRows.earAngle C hmin
  earAngle_nonnegative := fun C hmin ear corner =>
    earRows.earAngle_nonnegative C hmin ear corner
  earAngleSum_eq_pi := fun C hmin ear =>
    earRows.earAngleSum_eq_pi C hmin ear
  sectorAngle := fun C hmin =>
    earRows.sectorAngle C hmin
  sectorAngle_nonnegative := fun C hmin k =>
    earRows.sectorAngle_nonnegative C hmin k
  localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
    selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_localRows_le_orderedOuterFaceSectorSum
      (selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfEarDecompositionAngleMassBudgetRows
        earRows)
      C hmin
  orderedOuterFaceSectorSum_eq_earAngleSum := fun C hmin =>
    earRows.orderedOuterFaceSectorSum_eq_earAngleSum C hmin

/-- Concrete angle-mass budgeted ear rows supply the selected sector/order
rows through the existing ear-decomposition surface. -/
def selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfEarDecompositionAngleMassBudgetRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionAngleMassBudgetRows
        topology longArc) :
    SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc :=
  selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfEarDecompositionRows
    (selectedTopologyLocalAngleOuterFaceEarDecompositionRowsOfAngleMassBudgetRows
      earRows)

theorem selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_boundaryCycleAngleSum_of_outerFaceSectorOrder
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
      (selectedTopologyLocalAngleFamiliesOfMinimalFailure
        (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
        Real.pi *
          (((topology C hmin).toOuterBoundaryCore.outerCycle.length : Real) -
            2) := by
  have hsector :=
    sectorRows.orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum
      C hmin
  change
    Finset.sum Finset.univ (sectorRows.sectorAngle C hmin) <=
      Real.pi *
        (((topology C hmin).toOuterBoundaryCore.outerCycle.length : Real) -
          2) at hsector
  exact
    le_trans
      (sectorRows.localRows_le_orderedOuterFaceSectorSum C hmin)
      hsector

/-- Low-level constructor from concrete local unit-separated triples plus the
classified polygon comparison.  The live S3 geometric input is supplied by the
outer-face sector/order theorem below. -/
def selectedTopologyLocalAngleGeometryRowsOfAccountedPolygon
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (accounted_le_polygon :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
            (selectedClassificationOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin)).counts.polygonAngleSum) :
    SelectedTopologyLocalAngleGeometryRows topology where
  longArc := longArc
  localAngles := fun C hmin =>
    selectedTopologyLocalAngleFamiliesOfMinimalFailure
      (topology C hmin) hmin (longArc C hmin)
  accounted_le_polygon := accounted_le_polygon

/-- Low-level constructor from the boundary-cycle angle-sum form.  The transfer
from boundary-cycle angle sum to classified polygon sum is the existing W10
accounting bridge. -/
def selectedTopologyLocalAngleGeometryRowsOfBoundaryCycleAngleSum
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (accounted_le_boundaryCycleAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).accountedAngleSum <=
            Real.pi *
              (((topology C hmin).toOuterBoundaryCore.outerCycle.length : Real) -
                2)) :
    SelectedTopologyLocalAngleGeometryRows topology :=
  selectedTopologyLocalAngleGeometryRowsOfAccountedPolygon topology longArc
    (fun C hmin =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_polygon_of_le_boundaryCycleAngleSum
        (selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin))
        (accounted_le_boundaryCycleAngleSum C hmin))

/-- Build the selected-topology local geometry rows from the actual geometric
sector/order theorem: the generated selected-local rows are ordered disjoint
outer-face sectors whose total is bounded by the simple polygon
interior-angle sum. -/
def selectedTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrder
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc) :
    SelectedTopologyLocalAngleGeometryRows topology :=
  selectedTopologyLocalAngleGeometryRowsOfBoundaryCycleAngleSum topology longArc
    (fun C hmin =>
      selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_boundaryCycleAngleSum_of_outerFaceSectorOrder
        sectorRows C hmin)

/-- Sector-order rows are the remaining S3 geometry needed to inhabit the
reduced selected-topology local angle-geometry rows. -/
theorem nonempty_selectedTopologyLocalAngleGeometryRows_of_outerFaceSectorOrder
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc) :
    Nonempty (SelectedTopologyLocalAngleGeometryRows topology) :=
  Nonempty.intro
    (selectedTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrder
      topology longArc sectorRows)

/-- Reattach the one polygon angle-accounting comparison to the local
unit-separated geometry rows, yielding the W10 angle-family rows. -/
def selectedTopologyAngleWitnessRowsOfLocalAngleGeometryRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (geometryRows : SelectedTopologyLocalAngleGeometryRows topology) :
    SelectedTopologyAngleWitnessRows topology where
  classification := fun C hmin =>
    selectedClassificationOfMinimalFailure
      (topology C hmin) hmin (geometryRows.longArc C hmin)
  angleWitness := fun C hmin =>
    (geometryRows.localAngles C hmin).toUnitSeparatedAngleFamilies
      (geometryRows.accounted_le_polygon C hmin)

/-- A pointwise selected outer-boundary angle source built from the reduced
local Euclidean geometry rows over a selected topology family. -/
def selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (geometryRows : SelectedTopologyLocalAngleGeometryRows topology)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    SelectedOuterBoundaryAngleSource C where
  topology := topology C hmin
  classification :=
    selectedClassificationOfMinimalFailure
      (topology C hmin) hmin (geometryRows.longArc C hmin)
  angleWitness :=
    (geometryRows.localAngles C hmin).toUnitSeparatedAngleFamilies
      (geometryRows.accounted_le_polygon C hmin)

/-- Minimal-failure W13 actual-angle rows built from the reduced local
unit-separated geometry rows over selected topology. -/
def actualOuterBoundaryAngleDataRowsOfSelectedTopologyLocalAngleGeometryRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (geometryRows : SelectedTopologyLocalAngleGeometryRows topology) :
    MinimalFailureActualOuterBoundaryAngleDataRows :=
  actualOuterBoundaryAngleDataRowsOfTopologyAngleWitnessRows
    (selectedTopologyAngleWitnessRowsOfLocalAngleGeometryRows geometryRows)

/-- Existing actual angle rows project down to the reduced local
unit-separated geometry rows, with the accounted-sum polygon comparison
retained explicitly. -/
theorem exists_selectedTopologyLocalAngleGeometryRows_of_actualOuterBoundaryAngleDataRows
    (rows : MinimalFailureActualOuterBoundaryAngleDataRows) :
    Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
      Nonempty (SelectedTopologyLocalAngleGeometryRows topology) := by
  let selectedRows : MinimalFailureSelectedOuterBoundaryAngleRows :=
    fun C hmin =>
      SelectedOuterBoundaryAngleSource.ofActualOuterBoundaryAngleData
        (rows C hmin)
  let topology : MinimalFailureActualSelectedTopologyRows :=
    selectedTopologyRowsOfSelectedOuterBoundaryAngleRows selectedRows
  refine Exists.intro topology ?_
  exact
    Nonempty.intro
      { longArc :=
          selectedLongArcRowsOfSelectedOuterBoundaryAngleRows selectedRows
        localAngles := fun C hmin =>
          (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
            selectedRows C hmin).toLocalAngleGeometry
        accounted_le_polygon := fun C hmin =>
          BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies.toLocalAngleGeometry_accountedAngleSum_le_polygon
            (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
              selectedRows C hmin) }

/-- The reduced local unit-separated geometry rows are enough to inhabit the
actual W13 outer-boundary angle rows. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_selectedTopologyLocalAngleGeometryRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (geometryRows : SelectedTopologyLocalAngleGeometryRows topology) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows :=
  Nonempty.intro
    (actualOuterBoundaryAngleDataRowsOfSelectedTopologyLocalAngleGeometryRows
      geometryRows)

/-- Ordered/disjoint outer-face sector rows, together with their simple polygon
interior-angle bound, directly supply the W13 actual outer-boundary angle
rows. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_outerFaceSectorOrder
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows :=
  nonempty_actualOuterBoundaryAngleDataRows_of_selectedTopologyLocalAngleGeometryRows
    (selectedTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrder
      topology longArc sectorRows)

/-- Existential form of the S3 reduction: once selected topology rows carry
ordered/disjoint outer-face sector rows, the actual outer-boundary angle row
source is inhabited. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_exists_outerFaceSectorOrder
    (h :
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Exists fun longArc :
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) ->
                Prop =>
          Nonempty
            (SelectedTopologyLocalAngleOuterFaceSectorOrderRows
              topology longArc)) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows := by
  cases h with
  | intro topology hlongArc =>
      cases hlongArc with
      | intro longArc hsectorRows =>
          cases hsectorRows with
          | intro sectorRows =>
              exact
                nonempty_actualOuterBoundaryAngleDataRows_of_outerFaceSectorOrder
                  sectorRows

/-- Exact reduction of the W13 actual-angle row source to selected topology,
local unit-separated angle geometry, and the accounted-angle polygon
comparison. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_iff_exists_selectedTopologyLocalAngleGeometryRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyLocalAngleGeometryRows topology) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro rows =>
        exact
          exists_selectedTopologyLocalAngleGeometryRows_of_actualOuterBoundaryAngleDataRows
            rows
  case mpr =>
    intro h
    cases h with
    | intro topology hgeometry =>
        cases hgeometry with
        | intro geometryRows =>
            exact
              nonempty_actualOuterBoundaryAngleDataRows_of_selectedTopologyLocalAngleGeometryRows
                geometryRows

/-- Actual Euclidean selected-boundary angle rows.

For each minimal-failure selected topology row, these fields give the concrete
unit-separated angle triples for every generated boundary class.  The only
nonlocal field is the polygon angle-accounting comparison for the sum of those
actual triples. -/
structure ActualSelectedBoundaryEuclideanAngleRows : Type 1 where
  topology : MinimalFailureActualSelectedTopologyRows
  longArc :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop
  degree3 :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree3Indices ->
          Fin 2 ->
            BoundaryAngleWitnessConstruction.UnitSeparatedAngle
              (CanonicalGraph C)
  degree4 :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree4Indices ->
          Fin 3 ->
            BoundaryAngleWitnessConstruction.UnitSeparatedAngle
              (CanonicalGraph C)
  degree5 :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree5Indices ->
          Fin 4 ->
            BoundaryAngleWitnessConstruction.UnitSeparatedAngle
              (CanonicalGraph C)
  degree6 :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).degree6Indices ->
          Fin 5 ->
            BoundaryAngleWitnessConstruction.UnitSeparatedAngle
              (CanonicalGraph C)
  nontriangle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).nontriangleEdgeIndices ->
          Fin 1 ->
            BoundaryAngleWitnessConstruction.UnitSeparatedAngle
              (CanonicalGraph C)
  longArcAngle :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedClassificationOfMinimalFailure
          (topology C hmin) hmin (longArc C hmin)).longArcIndices ->
          Fin 1 ->
            BoundaryAngleWitnessConstruction.UnitSeparatedAngle
              (CanonicalGraph C)
  accounted_le_polygon :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ({ degree3 := degree3 C hmin
           degree4 := degree4 C hmin
           degree5 := degree5 C hmin
           degree6 := degree6 C hmin
           nontriangle := nontriangle C hmin
           longArc := longArcAngle C hmin } :
          BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies
            (selectedClassificationOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin))).accountedAngleSum <=
          (selectedClassificationOfMinimalFailure
            (topology C hmin) hmin (longArc C hmin)).counts.polygonAngleSum

/-- Attach the selected topology to its local unit-separated Euclidean angle
geometry rows.  This is the positive S3 row source: the actual selected
boundary rows are built directly from the selected topology, the local
unit-separated triples, and the accounted-angle polygon comparison. -/
def actualSelectedBoundaryEuclideanAngleRowsOfSelectedTopologyLocalAngleGeometryRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (geometryRows : SelectedTopologyLocalAngleGeometryRows topology) :
    ActualSelectedBoundaryEuclideanAngleRows where
  topology := topology
  longArc := geometryRows.longArc
  degree3 := fun C hmin =>
    (geometryRows.localAngles C hmin).degree3
  degree4 := fun C hmin =>
    (geometryRows.localAngles C hmin).degree4
  degree5 := fun C hmin =>
    (geometryRows.localAngles C hmin).degree5
  degree6 := fun C hmin =>
    (geometryRows.localAngles C hmin).degree6
  nontriangle := fun C hmin =>
    (geometryRows.localAngles C hmin).nontriangle
  longArcAngle := fun C hmin =>
    (geometryRows.localAngles C hmin).longArc
  accounted_le_polygon := fun C hmin =>
    geometryRows.accounted_le_polygon C hmin

namespace ActualSelectedBoundaryEuclideanAngleRows

variable (R : ActualSelectedBoundaryEuclideanAngleRows)

/-- The concrete local angle geometry row generated by the Euclidean triples. -/
def localAngleGeometry
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies
      (selectedClassificationOfMinimalFailure
        (R.topology C hmin) hmin (R.longArc C hmin)) :=
  { degree3 := R.degree3 C hmin
    degree4 := R.degree4 C hmin
    degree5 := R.degree5 C hmin
    degree6 := R.degree6 C hmin
    nontriangle := R.nontriangle C hmin
    longArc := R.longArcAngle C hmin }

/-- The full W10 unit-separated family obtained from actual selected-boundary
Euclidean angle rows. -/
def unitSeparatedAngleFamilies
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
      (selectedClassificationOfMinimalFailure
        (R.topology C hmin) hmin (R.longArc C hmin)) :=
  (R.localAngleGeometry C hmin).toUnitSeparatedAngleFamilies
    (R.accounted_le_polygon C hmin)

/-- The selected outer-boundary angle source constructed directly from actual
Euclidean selected-boundary angle triples and their polygon accounting row. -/
def selectedOuterBoundaryAngleSource
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    SelectedOuterBoundaryAngleSource C where
  topology := R.topology C hmin
  classification :=
    selectedClassificationOfMinimalFailure
      (R.topology C hmin) hmin (R.longArc C hmin)
  angleWitness := R.unitSeparatedAngleFamilies C hmin

/-- Minimal-failure selected outer-boundary angle rows obtained without using
the downstream selected outer-face/subpolygon planar-data consumer. -/
def toSelectedOuterBoundaryAngleRows :
    MinimalFailureSelectedOuterBoundaryAngleRows :=
  fun C hmin => R.selectedOuterBoundaryAngleSource C hmin

/-- Repackage the actual Euclidean rows in the existing reduced local-geometry
shape. -/
def toSelectedTopologyLocalAngleGeometryRows :
    SelectedTopologyLocalAngleGeometryRows R.topology where
  longArc := R.longArc
  localAngles := fun C hmin => R.localAngleGeometry C hmin
  accounted_le_polygon := fun C hmin => R.accounted_le_polygon C hmin

/-- The W13 actual outer-boundary angle rows constructed directly from actual
Euclidean selected-boundary angle triples. -/
def toActualOuterBoundaryAngleDataRows :
    MinimalFailureActualOuterBoundaryAngleDataRows :=
  fun C hmin =>
    { core := (R.topology C hmin).toOuterBoundaryCore
      classification :=
        selectedClassificationOfMinimalFailure
          (R.topology C hmin) hmin (R.longArc C hmin)
      angleWitness := R.unitSeparatedAngleFamilies C hmin }

end ActualSelectedBoundaryEuclideanAngleRows

/-- Concrete actual selected-boundary Euclidean angle rows inhabit the W13
minimal-failure actual outer-boundary angle source. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_actualSelectedBoundaryEuclideanAngleRows
    (rows : ActualSelectedBoundaryEuclideanAngleRows) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows :=
  Nonempty.intro rows.toActualOuterBoundaryAngleDataRows

/-- Concrete actual selected-boundary Euclidean angle rows directly inhabit the
selected-row source. -/
theorem nonempty_selectedOuterBoundaryAngleRows_of_actualSelectedBoundaryEuclideanAngleRows
    (rows : ActualSelectedBoundaryEuclideanAngleRows) :
    Nonempty MinimalFailureSelectedOuterBoundaryAngleRows :=
  Nonempty.intro rows.toSelectedOuterBoundaryAngleRows

/-- Local selected-topology Euclidean geometry rows directly inhabit the
actual selected-boundary Euclidean row source. -/
theorem nonempty_actualSelectedBoundaryEuclideanAngleRows_of_selectedTopologyLocalAngleGeometryRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (geometryRows : SelectedTopologyLocalAngleGeometryRows topology) :
    Nonempty ActualSelectedBoundaryEuclideanAngleRows :=
  Nonempty.intro
    (actualSelectedBoundaryEuclideanAngleRowsOfSelectedTopologyLocalAngleGeometryRows
      geometryRows)

/-- Ordered/disjoint outer-face sector rows also inhabit the concrete actual
selected-boundary Euclidean row source. -/
theorem nonempty_actualSelectedBoundaryEuclideanAngleRows_of_outerFaceSectorOrder
    {topology : MinimalFailureActualSelectedTopologyRows}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows topology longArc) :
    Nonempty ActualSelectedBoundaryEuclideanAngleRows :=
  nonempty_actualSelectedBoundaryEuclideanAngleRows_of_selectedTopologyLocalAngleGeometryRows
    (selectedTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrder
      topology longArc sectorRows)

/-- The selected nondegenerate topology row family obtained from the strong S2
nondegenerate selected-cycle source.  The remaining S3 geometry theorem below
is stated over exactly these selected rows. -/
def selectedNondegenerateTopologyRows
    (target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin =>
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofMissingTopologyFacts
      (Classical.choose (target C hmin))

/-- The selected nondegenerate topology rows really have a nondegenerate outer
cycle at every minimal cleared failure. -/
theorem selectedNondegenerateTopologyRows_outerCycle_length_ge_three
    (target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    3 <=
      ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
        |>.outerCycle.length) := by
  let topology := Classical.choose (target C hmin)
  have htopology : 3 <= topology.outerCycle.length :=
    Classical.choose_spec (target C hmin)
  change 3 <= topology.outerCycle.length
  exact htopology

/-- Single honest S3 geometry obligation for the selected nondegenerate
topology: choose the long-arc predicate and prove the generated local rows are
ordered/disjoint outer-face sectors with total sector mass bounded by the
simple polygon interior-angle sum. -/
def SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
    (target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    Prop :=
  Exists fun longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop =>
    Nonempty
      (SelectedTopologyLocalAngleOuterFaceSectorOrderRows
        (selectedNondegenerateTopologyRows target) longArc)

/-- The S2 nondegenerate topology package leaves exactly the existing
selected-topology simple-polygon sector-order rows over
`selectedNondegenerateTopologyRows`.  No additional geometry is hidden here:
proving the left side is definitionally the same as choosing `longArc` and
inhabiting those row fields. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_iff_exists_simplePolygonSectorOrderRows
    (target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target <->
      Exists fun longArc :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
              |>.outerCycle.length)) -> Prop =>
        Nonempty
            (SelectedTopologyLocalAngleOuterFaceSectorOrderRows
            (selectedNondegenerateTopologyRows target) longArc) :=
  Iff.rfl

/-- Actual S3 per-boundary-index cyclic-neighbour interval source rows over
the selected nondegenerate topology.  These are the remaining local ordered
unit-neighbour interval rows, with a chosen long-arc predicate. -/
def SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows
    (target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    Prop :=
  Exists fun longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop =>
    Nonempty
      (SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc)

/-- The genuine simple-polygon interior-angle inequality for the selected
nondegenerate outer polygon.  This is the polygon-side input consumed by the
canonical interval-row S3 constructor. -/
def SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows
    (target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) <=
        BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))

/-- Package concrete interval rows as the selected-nondegenerate S3 interval
source. -/
theorem selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_rows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (intervalRows :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc) :
    SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows target :=
  Exists.intro longArc (Nonempty.intro intervalRows)

/-- Boundary-walk interval data plus the explicit S3 slot/gap rows inhabit the
actual selected-nondegenerate boundary-index interval source. -/
theorem selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_boundaryDataRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (boundaryDataRows :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows
        (selectedNondegenerateTopologyRows target) longArc) :
    SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows target :=
  selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_rows
    boundaryDataRows.toRows

/-- Endpoint intervals, ordered unit-neighbor data, and slot-to-gap rows
inhabit the selected-nondegenerate boundary-index interval source. -/
theorem selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_orderedUnitNeighborDataAndSlotToGapRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (endpointInterval :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
          ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle) k)
    (orderedNeighbor :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexOrderedUnitNeighborData
          (topology := selectedNondegenerateTopologyRows target)
          C hmin k (endpointInterval C hmin k))
    (slotToGapRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborSlotToGapRows
          (topology := selectedNondegenerateTopologyRows target)
          (longArc := longArc)
          (fun C hmin =>
            selectedNondegenerateTopologyRows_outerCycle_length_ge_three
              target C hmin)
          C hmin k (endpointInterval C hmin k)
          (orderedNeighbor C hmin k)) :
    SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows target :=
  selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_boundaryDataRows
    (target := target) (longArc := longArc)
    (SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows.ofOrderedUnitNeighborDataAndSlotToGapRows
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc)
      (fun C hmin =>
        selectedNondegenerateTopologyRows_outerCycle_length_ge_three
          target C hmin)
      endpointInterval orderedNeighbor slotToGapRows)

/-- W28 supplies the endpoint-backed ordered-neighbor rows for the selected
nondegenerate topology; the remaining exact local premise is the slot-to-gap
geometry over those rows. -/
theorem selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_w28OrderedUnitNeighborDataAndSlotToGapRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (slotToGapRows :
      SelectedTopologyW28OrderedBoundaryIndexSlotToGapRows
        (selectedNondegenerateTopologyRows target) longArc
        (fun C hmin =>
          selectedNondegenerateTopologyRows_outerCycle_length_ge_three
            target C hmin)) :
    SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows target :=
  selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_boundaryDataRows
    (target := target) (longArc := longArc)
    (SelectedTopologyBoundaryIndexCyclicNeighborIntervalBoundaryDataRows.ofW28OrderedUnitNeighborDataAndSlotToGapRows
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc)
      (fun C hmin =>
        selectedNondegenerateTopologyRows_outerCycle_length_ge_three
          target C hmin)
      slotToGapRows)

/-- Exact-budget rows for the selected nondegenerate topology, generated from
the single scalar accounting inequality for the canonical local angle rows.
This does not assert ordered sector geometry; it removes only the auxiliary
choice of six classified budget functions by taking each budget to be the
corresponding generated angle mass. -/
def selectedNondegenerateTopologyLocalAngleMassBudgetRowsOfGeneratedAccountedAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleMassBudgetRows
      (selectedNondegenerateTopologyRows target) longArc :=
  selectedTopologyLocalAngleMassBudgetRowsOfGeneratedAccountedAngleSum
    (topology := selectedNondegenerateTopologyRows target)
    (longArc := longArc)
    accounted_le_simpleOuterPolygonInteriorAngleSum

/-- The scalar generated-accounting inequality is exactly enough to inhabit
the nondegenerate angle-mass budget row surface. -/
theorem nonempty_selectedNondegenerateTopologyLocalAngleMassBudgetRows_of_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    Nonempty
      (SelectedTopologyLocalAngleMassBudgetRows
        (selectedNondegenerateTopologyRows target) longArc) :=
  Nonempty.intro
    (selectedNondegenerateTopologyLocalAngleMassBudgetRowsOfGeneratedAccountedAngleSum
      (target := target) (longArc := longArc)
      accounted_le_simpleOuterPolygonInteriorAngleSum)

/-- Direct S2 nondegenerate specialization of the budgeted triangulation
angle-mass rows.  This inhabits the actual row structure over
`selectedNondegenerateTopologyRows target`; the ordered-sector budget field is
the one supplied by
`selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum`. -/
def selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
      (selectedNondegenerateTopologyRows target) longArc :=
  selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum
    (topology := selectedNondegenerateTopologyRows target)
    (longArc := longArc)
    (fun C hmin =>
      selectedNondegenerateTopologyRows_outerCycle_length_ge_three
        target C hmin)
    accounted_le_simpleOuterPolygonInteriorAngleSum

/-- Nonempty direct-row form of the S2 nondegenerate budgeted triangulation
angle-mass constructor. -/
theorem nonempty_selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_of_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    Nonempty
      (SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
        (selectedNondegenerateTopologyRows target) longArc) :=
  Nonempty.intro
    (selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum
      (target := target) (longArc := longArc)
      accounted_le_simpleOuterPolygonInteriorAngleSum)

/-- The same scalar generated-accounting inequality also supplies the reduced
selected local angle-geometry rows, via the W10 transfer from boundary-cycle
angle sum to classified polygon angle sum. -/
def selectedNondegenerateTopologyLocalAngleGeometryRowsOfGeneratedAccountedAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    SelectedTopologyLocalAngleGeometryRows
      (selectedNondegenerateTopologyRows target) :=
  selectedTopologyLocalAngleGeometryRowsOfBoundaryCycleAngleSum
    (selectedNondegenerateTopologyRows target) longArc
    (fun C hmin => by
      change
        (selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (selectedNondegenerateTopologyRows target C hmin) hmin
          (longArc C hmin)).accountedAngleSum <=
          simpleOuterPolygonInteriorAngleSum
            ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)
      exact accounted_le_simpleOuterPolygonInteriorAngleSum C hmin)

/-- Nonempty form of the generated-accounting reduction to selected local
angle-geometry rows. -/
theorem nonempty_selectedNondegenerateTopologyLocalAngleGeometryRows_of_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    Nonempty
      (SelectedTopologyLocalAngleGeometryRows
        (selectedNondegenerateTopologyRows target)) :=
  Nonempty.intro
    (selectedNondegenerateTopologyLocalAngleGeometryRowsOfGeneratedAccountedAngleSum
      (target := target) (longArc := longArc)
      accounted_le_simpleOuterPolygonInteriorAngleSum)

/-- The generated-accounting inequality over the selected nondegenerate
topology is enough for the concrete actual selected-boundary Euclidean angle
row package. -/
theorem nonempty_actualSelectedBoundaryEuclideanAngleRows_of_selectedNondegenerateTopology_generatedAccountedAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    Nonempty ActualSelectedBoundaryEuclideanAngleRows :=
  nonempty_actualSelectedBoundaryEuclideanAngleRows_of_selectedTopologyLocalAngleGeometryRows
    (selectedNondegenerateTopologyLocalAngleGeometryRowsOfGeneratedAccountedAngleSum
      (target := target) (longArc := longArc)
      accounted_le_simpleOuterPolygonInteriorAngleSum)

/-- The generated-accounting inequality over the selected nondegenerate
topology is enough for the W13 actual outer-boundary angle-data rows. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_selectedNondegenerateTopology_generatedAccountedAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows :=
  nonempty_actualOuterBoundaryAngleDataRows_of_selectedTopologyLocalAngleGeometryRows
    (selectedNondegenerateTopologyLocalAngleGeometryRowsOfGeneratedAccountedAngleSum
      (target := target) (longArc := longArc)
      accounted_le_simpleOuterPolygonInteriorAngleSum)

/-- The generated accounted-angle inequality over the selected nondegenerate
topology also fills the exact sector/order row structure, using the
nondegenerate boundary length from S2 and the same chosen `longArc`
predicate. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_generatedAccountedAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (accounted_le_simpleOuterPolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      (selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfBoundaryCycleAngleSum
        (topology := selectedNondegenerateTopologyRows target)
        (longArc := longArc)
        (fun C hmin =>
          selectedNondegenerateTopologyRows_outerCycle_length_ge_three
            target C hmin)
        accounted_le_simpleOuterPolygonInteriorAngleSum))

/-- Direct constructor for the selected nondegenerate sector/order theorem
from sector rows whose local-row containment field is closed by concrete
angle-mass budgets. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_angleMassBudgetedSectorRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (budgetRows :
      SelectedTopologyLocalAngleMassBudgetRows
        (selectedNondegenerateTopologyRows target) longArc)
    (sectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Real)
    (sectorAngle_nonnegative :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
        (k :
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length))),
          0 <= sectorAngle C hmin k)
    (budgetSum_le_orderedOuterFaceSectorSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Finset.sum Finset.univ (budgetRows.degree3Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.degree4Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.degree5Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.degree6Budget C hmin) +
              Finset.sum Finset.univ (budgetRows.nontriangleBudget C hmin) +
              Finset.sum Finset.univ (budgetRows.longArcBudget C hmin) <=
            Finset.sum Finset.univ (sectorAngle C hmin))
    (orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Finset.sum Finset.univ (sectorAngle C hmin) <=
            simpleOuterPolygonInteriorAngleSum
              (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      (selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfAngleMassBudgetRows
        (topology := selectedNondegenerateTopologyRows target)
        (longArc := longArc) budgetRows sectorAngle sectorAngle_nonnegative
        budgetSum_le_orderedOuterFaceSectorSum
        orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum))

/-- Direct constructor for the selected nondegenerate sector/order theorem
from pointwise generated-slot sector containment rows.  Unlike the scalar
generated-accounting route, this requires every generated angle slot to be
assigned to a selected outer-face sector and bounded inside that sector's
load. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_sectorContainmentRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorContainmentRows
        (selectedNondegenerateTopologyRows target) longArc) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      (selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfSectorContainmentRows
        (topology := selectedNondegenerateTopologyRows target)
        (longArc := longArc) sectorRows))

/-- Actual boundary-neighbor sector rows are enough for the selected
nondegenerate outer-face sector/order theorem, via the preferred
sector-containment constructor. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_actualBoundaryNeighborSectorRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (sectorRows :
      SelectedTopologyActualBoundaryNeighborSectorContainmentRows
        (selectedNondegenerateTopologyRows target) longArc) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_sectorContainmentRows
    (target := target) (longArc := longArc)
    (selectedTopologyLocalAngleOuterFaceSectorContainmentRowsOfActualBoundaryNeighborSectorRows
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc) sectorRows)

/-- Selected-nondegenerate S3 constructor for the canonical same-index
actual boundary-neighbor sectors.  The six slot-to-sector maps are fixed by
the classified boundary indices; the two remaining hypotheses are precisely
the pointwise load containment in those actual sectors and the simple-polygon
sum bound for the actual predecessor/current/successor sector angles. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexSectorRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (sectorLoad_le_boundarySectorAngle :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k :
        Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        selectedBoundaryIndexSectorLoad
          (topology := selectedNondegenerateTopologyRows target)
          (longArc := longArc) C hmin k <=
          (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
            (topology := selectedNondegenerateTopologyRows target)
            (fun C hmin =>
              selectedNondegenerateTopologyRows_outerCycle_length_ge_three
                target C hmin)
            C hmin k).value)
    (boundarySectorAngleSum_le_simplePolygonInteriorAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Finset.sum Finset.univ
            (fun k =>
              (actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex
                (topology := selectedNondegenerateTopologyRows target)
                (fun C hmin =>
                  selectedNondegenerateTopologyRows_outerCycle_length_ge_three
                    target C hmin)
                C hmin k).value) <=
          simpleOuterPolygonInteriorAngleSum
            ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_actualBoundaryNeighborSectorRows
    (target := target) (longArc := longArc)
    (selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectors
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc)
      (fun C hmin =>
        selectedNondegenerateTopologyRows_outerCycle_length_ge_three
          target C hmin)
      sectorLoad_le_boundarySectorAngle
      boundarySectorAngleSum_le_simplePolygonInteriorAngleSum)

/-- Selected-nondegenerate S3 constructor from the explicit cyclic-neighbour
gap decomposition and W10's predecessor/current/successor boundary-sector
angle-sum rows.  This is the preferred row-level route: local generated slots
are first accounted inside consecutive unit-neighbour gaps, then those gaps
are bounded inside the actual PCS sector, while W10 supplies the polygon
sector-sum side. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborGapRowsAndAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (gapRows :
      SelectedTopologyBoundaryCyclicNeighborGapRows
        (selectedNondegenerateTopologyRows target) longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexSectorRows
    (target := target) (longArc := longArc)
    (fun C hmin k =>
      gapRows.sectorLoad_le_boundarySectorAngle C hmin k)
    (fun C hmin =>
      boundaryNeighborSectorAngleSumRows_le_simpleOuterPolygonInteriorAngleSum
        (topology := selectedNondegenerateTopologyRows target)
        gapRows.boundaryLength_ge_three C hmin
        (sectorAngleRows C hmin))

/-- Selected-nondegenerate S3 constructor from ordered neighbour intervals.
This is the same route as
`selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborGapRowsAndAngleSumRows`,
but the consecutive gap-angle records are derived from interval adjacency and
injectivity. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborIntervalRowsAndAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (intervalRows :
      SelectedTopologyBoundaryCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborGapRowsAndAngleSumRows
    (target := target) (longArc := longArc)
    intervalRows.toCyclicNeighborGapRows
    sectorAngleRows

/-- Selected-nondegenerate S3 constructor from local per-boundary-index
ordered neighbour intervals and an already assembled W10 boundary-sector
angle-sum row package. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndBoundaryNeighborSectorAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (intervalRows :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc)
    (sectorAngleRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      (intervalRows.toLocalAngleOuterFaceSectorOrderRowsAndAngleSumRows
        sectorAngleRows))

/-- Selected-nondegenerate S3 constructor from local per-boundary-index ordered
neighbour intervals and genuine triangulation angle-sum rows for the selected
outer polygon.  W10 supplies the canonical predecessor/current/successor
sector-sum package from those triangulation rows. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (intervalRows :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc)
    (triangulationRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.SimplePolygonInteriorAngleTriangulationRows.{u}
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndBoundaryNeighborSectorAngleSumRows
    (target := target) (longArc := longArc) intervalRows
    (fun C hmin => by
      let R := triangulationRows C hmin
      letI := R.triangleFintype
      exact
        BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfTriangulationAngleSum
          (P := (selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)
          R.boundaryLength_ge_three
          (R.triangleCount_eq_boundaryLength_sub_two)
          (fun T c =>
            _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.triangleCornerAngle
              (R.trianglePoint T) c)
          (R.triangleAngleSum_eq_pi)
          (R.polygonInteriorAngleSum_eq_triangleAngleSum))

/-- Selected-nondegenerate S3 constructor from local per-boundary-index
ordered neighbour intervals and the genuine simple-polygon angle-sum theorem.
The matching W10 boundary-sector rows are the canonical predecessor/current/
successor rows. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSimplePolygonInteriorAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (intervalRows :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc)
    (simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
            (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)) <=
          BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
            (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      (intervalRows.toLocalAngleOuterFaceSectorOrderRowsAndSimplePolygonInteriorAngleSumRows
        simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum))

/-- Named-source-row form of the canonical S3 interval constructor: actual
per-boundary-index cyclic-neighbour interval rows plus the genuine
simple-polygon angle inequality close the selected nondegenerate outer-face
sector/order theorem. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalSourceRowsAndSimplePolygonInteriorAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (intervalRows :
      SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows target)
    (simplePolygonRows :
      SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows target) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target := by
  rcases intervalRows with ⟨longArc, hintervalRows⟩
  rcases hintervalRows with ⟨intervalRows⟩
  exact
    selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSimplePolygonInteriorAngleSumRows
      (target := target) (longArc := longArc) intervalRows simplePolygonRows

/-- Direct selected-nondegenerate S3 consumer: endpoint intervals, ordered
unit-neighbor data, and slot-to-gap rows give the local sector containment,
while the simple-polygon source supplies the sector-sum side. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_orderedUnitNeighborDataAndSlotToGapRowsAndSimplePolygonInteriorAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (endpointInterval :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
          ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle) k)
    (orderedNeighbor :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexOrderedUnitNeighborData
          (topology := selectedNondegenerateTopologyRows target)
          C hmin k (endpointInterval C hmin k))
    (slotToGapRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore.outerCycle.length)),
        SelectedBoundaryIndexCyclicNeighborSlotToGapRows
          (topology := selectedNondegenerateTopologyRows target)
          (longArc := longArc)
          (fun C hmin =>
            selectedNondegenerateTopologyRows_outerCycle_length_ge_three
              target C hmin)
          C hmin k (endpointInterval C hmin k)
          (orderedNeighbor C hmin k))
    (simplePolygonRows :
      SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows target) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_actualBoundaryNeighborSectorRows
    (target := target) (longArc := longArc)
    (selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfOrderedUnitNeighborDataAndSlotToGapRowsAndSimplePolygonInteriorAngleSumRows
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc)
      (fun C hmin =>
        selectedNondegenerateTopologyRows_outerCycle_length_ge_three
          target C hmin)
      endpointInterval orderedNeighbor slotToGapRows simplePolygonRows)

/-- Sharp W28-backed sector-order source: W28 gives the endpoint-compatible
ordered-neighbor row, the caller supplies the real slot-to-gap geometry, and
the simple-polygon rows supply the global angle-sum side. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_w28OrderedUnitNeighborDataAndSlotToGapRowsAndSimplePolygonInteriorAngleSumRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (slotToGapRows :
      SelectedTopologyW28OrderedBoundaryIndexSlotToGapRows
        (selectedNondegenerateTopologyRows target) longArc
        (fun C hmin =>
          selectedNondegenerateTopologyRows_outerCycle_length_ge_three
            target C hmin))
    (simplePolygonRows :
      SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows target) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalSourceRowsAndSimplePolygonInteriorAngleSumRows
    (target := target)
    (selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_w28OrderedUnitNeighborDataAndSlotToGapRows
      (target := target) (longArc := longArc) slotToGapRows)
    simplePolygonRows

/-- Honest triangulation rows for the selected nondegenerate outer polygon
reduce to the simple-polygon angle inequality consumed by the canonical S3
interval constructor. -/
def selectedNondegenerateTopologySimplePolygonInteriorAngleSumRowsOfTriangulationRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (triangulationRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.SimplePolygonInteriorAngleTriangulationRows.{u}
          (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore))) :
    SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows target :=
  fun C hmin =>
    (triangulationRows C hmin).simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- Selected outer-boundary nondegenerate triangle-point rows reduce to the
simple-polygon angle inequality consumed by the canonical S3 interval
constructor.  The Euclidean triangle angle sums are supplied by
`PlanarBoundaryFaceDataRefinement` from the point rows, so this bridge does not
duplicate the triangulation proof. -/
def selectedNondegenerateTopologySimplePolygonInteriorAngleSumRowsOfSelectedOuterBoundaryNondegenerateTrianglePointRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (trianglePointRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.SelectedOuterBoundaryNondegenerateTrianglePointRows.{u}
          ((selectedNondegenerateTopologyRows target C hmin).toMissingTopologyFacts)) :
    SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows target :=
  fun C hmin => by
    change
      BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
          ((selectedNondegenerateTopologyRows target C hmin).toMissingTopologyFacts.toCore) <=
        BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
          ((selectedNondegenerateTopologyRows target C hmin).toMissingTopologyFacts.toCore)
    exact
      (trianglePointRows C hmin).simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- Local interval rows plus selected outer-boundary nondegenerate
triangle-point rows close the selected nondegenerate S3 sector/order theorem.
The triangle-point rows are used only through their checked projection to the
simple-polygon interior-angle inequality. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSelectedOuterBoundaryNondegenerateTrianglePointRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (intervalRows :
      SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows
        (selectedNondegenerateTopologyRows target) longArc)
    (trianglePointRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.SelectedOuterBoundaryNondegenerateTrianglePointRows.{u}
          ((selectedNondegenerateTopologyRows target C hmin).toMissingTopologyFacts)) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSimplePolygonInteriorAngleSumRows
    (target := target) (longArc := longArc) intervalRows
    (selectedNondegenerateTopologySimplePolygonInteriorAngleSumRowsOfSelectedOuterBoundaryNondegenerateTrianglePointRows
      (target := target) trianglePointRows)

/-- Named-source-row form of the selected outer-boundary triangle-point route:
the remaining S3 inputs are exactly the boundary-index interval rows and the
selected outer-boundary nondegenerate triangle-point rows. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalSourceRowsAndSelectedOuterBoundaryNondegenerateTrianglePointRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (intervalRows :
      SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows target)
    (trianglePointRows :
      forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        _root_.ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.SelectedOuterBoundaryNondegenerateTrianglePointRows.{u}
          ((selectedNondegenerateTopologyRows target C hmin).toMissingTopologyFacts)) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalSourceRowsAndSimplePolygonInteriorAngleSumRows
    intervalRows
    (selectedNondegenerateTopologySimplePolygonInteriorAngleSumRowsOfSelectedOuterBoundaryNondegenerateTrianglePointRows
      (target := target) trianglePointRows)

/-- Direct constructor for the selected nondegenerate sector/order theorem
from triangulation rows whose local containment field is closed by the explicit
angle-mass budget-to-sector row. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_triangulationAngleMassBudgetRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (triangulationRows :
      SelectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows
        (selectedNondegenerateTopologyRows target) longArc) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      { sectorAngle := fun C hmin =>
          triangulationRows.sectorAngle C hmin
        sectorAngle_nonnegative := fun C hmin k =>
          triangulationRows.sectorAngle_nonnegative C hmin k
        localRows_le_orderedOuterFaceSectorSum := fun C hmin =>
          selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_localRows_le_orderedOuterFaceSectorSum
            triangulationRows C hmin
        orderedOuterFaceSectorSum_le_simplePolygonInteriorAngleSum := fun C hmin =>
          le_of_eq
            (selectedTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_orderedOuterFaceSectorSum_eq_simpleOuterPolygonInteriorAngleSum
              triangulationRows C hmin) })

/-- Direct constructor for the selected nondegenerate sector/order theorem
from ear-decomposition rows whose missing local containment field is closed by
concrete angle-mass budgets. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_earDecompositionAngleMassBudgetRows
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (earRows :
      SelectedTopologyLocalAngleOuterFaceEarDecompositionAngleMassBudgetRows
        (selectedNondegenerateTopologyRows target) longArc) :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target :=
  Exists.intro longArc
    (Nonempty.intro
      (selectedTopologyLocalAngleOuterFaceSectorOrderRowsOfEarDecompositionAngleMassBudgetRows
        earRows))

/-- Selected-nondegenerate projection from ordered outer-face sector rows to
the generated accounted-angle inequality.  This is the forward scalar source
used by the `iff` below: it forgets only the sector-angle witness rows, after
their local containment and simple-polygon sector-sum fields have supplied the
bound. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderRows_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop}
    (sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows
        (selectedNondegenerateTopologyRows target) longArc) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (selectedTopologyLocalAngleFamiliesOfMinimalFailure
          (selectedNondegenerateTopologyRows target C hmin) hmin
          (longArc C hmin)).accountedAngleSum <=
          simpleOuterPolygonInteriorAngleSum
            ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore) :=
  fun C hmin =>
    selectedTopologyLocalAngleOuterFaceSectorOrderRows_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc) sectorRows C hmin

/-- The selected nondegenerate sector theorem exposes the exact scalar
accounting inequality for its chosen `longArc`. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_exists_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (h :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target) :
    Exists fun longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
            |>.outerCycle.length)) -> Prop =>
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (selectedTopologyLocalAngleFamiliesOfMinimalFailure
            (selectedNondegenerateTopologyRows target C hmin) hmin
            (longArc C hmin)).accountedAngleSum <=
            simpleOuterPolygonInteriorAngleSum
              ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore) := by
  rcases h with ⟨longArc, hsectorRows⟩
  rcases hsectorRows with ⟨sectorRows⟩
  exact
    Exists.intro longArc
      (selectedNondegenerateTopologyOuterFaceSectorOrderRows_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
        (target := target) (longArc := longArc) sectorRows)

/-- Exact scalar form of the selected nondegenerate S3 sector/order
obligation: it is equivalent to choosing the `longArc` predicate and proving
the generated local accounted angle mass is bounded by the selected simple
outer-polygon angle sum. -/
theorem selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_iff_exists_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget} :
    SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target <->
      Exists fun longArc :
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            Fin (((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore
              |>.outerCycle.length)) -> Prop =>
        forall {n : Nat} (C : _root_.UDConfig n)
          (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
            (selectedTopologyLocalAngleFamiliesOfMinimalFailure
              (selectedNondegenerateTopologyRows target C hmin) hmin
              (longArc C hmin)).accountedAngleSum <=
              simpleOuterPolygonInteriorAngleSum
                ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore) := by
  constructor
  · intro h
    exact
      selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_exists_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum
        h
  · intro h
    rcases h with ⟨longArc, haccounted⟩
    exact
      selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_generatedAccountedAngleSum
        (target := target) (longArc := longArc) haccounted

/-- The single selected-nondegenerate sector theorem projects to the reduced
local angle-geometry rows through the checked W34/W10 accounting path. -/
theorem nonempty_selectedNondegenerateTopologyLocalAngleGeometryRows_of_outerFaceSectorOrderTheorem
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (h :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target) :
    Nonempty
      (SelectedTopologyLocalAngleGeometryRows
        (selectedNondegenerateTopologyRows target)) := by
  rcases h with ⟨longArc, hsectorRows⟩
  rcases hsectorRows with ⟨sectorRows⟩
  exact
    nonempty_selectedTopologyLocalAngleGeometryRows_of_outerFaceSectorOrder
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc) sectorRows

/-- The single selected-nondegenerate sector theorem projects to concrete
actual selected-boundary Euclidean angle rows. -/
theorem nonempty_actualSelectedBoundaryEuclideanAngleRows_of_outerFaceSectorOrderTheorem
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (h :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target) :
    Nonempty ActualSelectedBoundaryEuclideanAngleRows := by
  rcases h with ⟨longArc, hsectorRows⟩
  rcases hsectorRows with ⟨sectorRows⟩
  exact
    nonempty_actualSelectedBoundaryEuclideanAngleRows_of_outerFaceSectorOrder
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc) sectorRows

/-- The single selected-nondegenerate sector theorem closes the W13 actual
outer-boundary angle-data rows. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_outerFaceSectorOrderTheorem
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (h :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows := by
  rcases h with ⟨longArc, hsectorRows⟩
  rcases hsectorRows with ⟨sectorRows⟩
  exact
    nonempty_actualOuterBoundaryAngleDataRows_of_outerFaceSectorOrder
      (topology := selectedNondegenerateTopologyRows target)
      (longArc := longArc) sectorRows

/-- The actual reduced local-geometry rows extracted from a proved selected
nondegenerate outer-face sector/order theorem. -/
def selectedNondegenerateTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrderTheorem
    {target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget}
    (h :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem target) :
    SelectedTopologyLocalAngleGeometryRows
      (selectedNondegenerateTopologyRows target) :=
  let longArc :=
    fun {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) =>
        Classical.choose h C hmin
  let sectorRows :
      SelectedTopologyLocalAngleOuterFaceSectorOrderRows
        (selectedNondegenerateTopologyRows target) longArc :=
    Classical.choice (Classical.choose_spec h)
  selectedTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrder
    (selectedNondegenerateTopologyRows target) longArc sectorRows

/-- Eta-expanded S2 target associated to a remaining actual outer-boundary
cycle theorem.  The expansion keeps Lean from specializing the implicit
configuration index while W34 builds dependent row families from it. -/
def nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget :=
  fun C hmin =>
    SelectedTopologyRowsInhabitationW33.nondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
      boundaryTarget C hmin

/-- The nondegenerate S2 topology target obtained from the exact actual
topology field package, expressed through the checked exact-to-remaining
actual-cycle projection. -/
def nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
    (exactTarget :
      FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget) :
    FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget :=
  nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
    (FaceBoundaryTopologySourceW32.minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
      exactTarget)

/-- The S3 sector/order theorem supplies exactly the W33 skeleton remainder
rows required as `boundaryAngleBudgetRows` in the compact W34 input package.

The selected topology is the S2 nondegenerate target associated to the
remaining actual-cycle theorem.  The angle fields come from the generated
minimal-failure local Euclidean rows, and the subpolygon family is the checked
selected outer-face W34 subpolygon source. -/
def remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget)) :
    SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
      boundaryTarget := by
  let target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget :=
    nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle boundaryTarget
  let geometryRows :
      SelectedTopologyLocalAngleGeometryRows
        (selectedNondegenerateTopologyRows target) :=
    selectedNondegenerateTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrderTheorem
      (target := target) sectorTheorem
  refine
    { classification := ?_
      geometricAngleSum := ?_
      forced_le_geometric := ?_
      geometric_le_polygon := ?_
      Subpolygon := ?_
      subpolygonData := ?_ }
  · intro n C hmin
    let S :=
      selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
        geometryRows C hmin
    change
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        ((selectedNondegenerateTopologyRows target C hmin).toOuterBoundaryCore)
    exact S.classification
  · intro n C hmin
    let S :=
      selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
        geometryRows C hmin
    exact S.angleWitness.geometricAngleSum
  · intro n C hmin
    let S :=
      selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
        geometryRows C hmin
    exact S.angleWitness.forced_le_geometricAngleSum
  · intro n C hmin
    let S :=
      selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
        geometryRows C hmin
    exact S.angleWitness.geometric_le_polygon
  · intro n C hmin
    let S :=
      selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
        geometryRows C hmin
    exact (S.toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure hmin).Subpolygon
  · intro n C hmin
    let S :=
      selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
        geometryRows C hmin
    exact (S.toSelectedOuterFacePlanarBoundaryFaceDataOfMinimalFailure hmin).subpolygonData

def remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget)) :
    SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologySkeletonFamily.{0} :=
  SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfRemainingActualOuterBoundaryCycleTheoremTarget
    boundaryTarget
    (remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)

/-- Exact-S2 entry point for the W33 skeleton remainder rows consumed by final
assembly.  The exact topology fields are first projected to the remaining
actual-cycle target, then the existing S3 sector/order projection supplies the
classification, angle-budget, and selected subpolygon rows. -/
def remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
    (exactTarget :
      FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget)) :
    SelectedTopologyRowsInhabitationW33.RemainingActualCycleSkeletonRemainderRows.{0}
      (FaceBoundaryTopologySourceW32.minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
        exactTarget) :=
  remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem
    (FaceBoundaryTopologySourceW32.minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
      exactTarget)
    sectorTheorem

/-- Exact-S2 entry point for the minimal boundary topology skeleton family
used by downstream long-arc, finite-spine, and final-assembly fields. -/
def remainingActualCycleSkeletonFamilyOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
    (exactTarget :
      FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget)) :
    SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologySkeletonFamily.{0} :=
  remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
    (FaceBoundaryTopologySourceW32.minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
      exactTarget)
    sectorTheorem

/-- The S3 sector/order rows plus honest S4 raw-turn/coverage rows assemble an
actual W11 boundary-angle/turn package family over the live W33 skeleton rows.

This is intentionally before any finite-`p/q` generated-order source: it only
builds the boundary-angle package and the long-arc count-gap fields. -/
def boundaryAngleTurnTopologyPackageFamilyOfOuterFaceSectorOrderTheoremRawTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArcRows :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcRawTurnRows.{0}
        (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
          boundaryTarget sectorTheorem)) :
    SelectedTopologyRowsInhabitationW33.BoundaryAngleTurnTopologyPackageFamily.{0} := by
  intro n C hmin
  let target :
      FaceBoundaryTopologySourceW32.MinimalFailureNondegenerateMissingTopologyFactsTarget :=
    nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle boundaryTarget
  let geometryRows :
      SelectedTopologyLocalAngleGeometryRows
        (selectedNondegenerateTopologyRows target) :=
    selectedNondegenerateTopologyLocalAngleGeometryRowsOfOuterFaceSectorOrderTheorem
      (target := target) sectorTheorem
  let angleSource :=
    selectedOuterBoundaryAngleSourceOfLocalAngleGeometryRows
      geometryRows C hmin
  let skeleton :=
    remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem
  let longArcFields :=
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.longArcExistenceFieldsOfLongArcRawTurnRows
      skeleton longArcRows C hmin
  refine
    { topology := (skeleton.row C hmin).topology
      classification := (skeleton.row C hmin).classification
      Subpolygon := (skeleton.row C hmin).Subpolygon
      subpolygonData := (skeleton.row C hmin).subpolygonData
      boundary :=
        { countTurn :=
            { angleWitness := ?_
              longArcFields := ?_ } } }
  · change
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        angleSource.classification
    exact angleSource.angleWitness
  · change
      BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
        (skeleton.row C hmin).classification
        (skeleton.row C hmin).geometricAngleSum
        (skeleton.row C hmin).forced_le_geometric
        (skeleton.row C hmin).geometric_le_polygon
        (skeleton.row C hmin).Subpolygon
        (skeleton.row C hmin).subpolygonData
    exact longArcFields

theorem nonempty_boundaryAngleTurnTopologyPackageFamily_of_outerFaceSectorOrderTheorem_rawTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArcRows :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcRawTurnRows.{0}
        (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
          boundaryTarget sectorTheorem)) :
    Nonempty
      SelectedTopologyRowsInhabitationW33.BoundaryAngleTurnTopologyPackageFamily.{0} :=
  Nonempty.intro
    (boundaryAngleTurnTopologyPackageFamilyOfOuterFaceSectorOrderTheoremRawTurnRows
      boundaryTarget sectorTheorem longArcRows)

theorem nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_boundaryAngleTurnPackageFamily_outerFaceSectorOrderTheorem_rawTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArcRows :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcRawTurnRows.{0}
        (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
          boundaryTarget sectorTheorem)) :
    Nonempty
      (SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfBoundaryAngleTurnTopologyPackageFamily
          (boundaryAngleTurnTopologyPackageFamilyOfOuterFaceSectorOrderTheoremRawTurnRows
            boundaryTarget sectorTheorem longArcRows))) :=
  SelectedTopologyRowsInhabitationW33.nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_boundaryAngleTurnTopologyPackageFamily
    (boundaryAngleTurnTopologyPackageFamilyOfOuterFaceSectorOrderTheoremRawTurnRows
      boundaryTarget sectorTheorem longArcRows)

/-- Actual S4 long-arc family for the live sector-order skeleton rows.  The
source is the checked raw-turn/coverage row surface; no triangle-run,
finite-spine, or generated-order rows are used here. -/
def minimalBoundaryTopologyLongArcFieldFamilyOfOuterFaceSectorOrderTheoremRawTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArcRows :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcRawTurnRows.{0}
        (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
          boundaryTarget sectorTheorem)) :
    SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
      (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
        boundaryTarget sectorTheorem) :=
  SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologyLongArcFieldFamilyOfLongArcRawTurnRows
    (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
      boundaryTarget sectorTheorem)
    longArcRows

theorem nonempty_minimalBoundaryTopologyLongArcFieldFamily_of_outerFaceSectorOrderTheorem_rawTurnRows
    (boundaryTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget)
    (sectorTheorem :
      SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (nondegenerateMissingTopologyFactsTargetOfRemainingActualCycle
          boundaryTarget))
    (longArcRows :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcRawTurnRows.{0}
        (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
          boundaryTarget sectorTheorem)) :
    Nonempty
      (SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (remainingActualCycleSkeletonFamilyOfOuterFaceSectorOrderTheorem
          boundaryTarget sectorTheorem)) :=
  Nonempty.intro
    (minimalBoundaryTopologyLongArcFieldFamilyOfOuterFaceSectorOrderTheoremRawTurnRows
      boundaryTarget sectorTheorem longArcRows)

/-- Existing W13 angle rows can be inspected as actual Euclidean
selected-boundary angle rows by forgetting back to the concrete local triples
they carry. -/
def actualSelectedBoundaryEuclideanAngleRowsOfActualOuterBoundaryAngleDataRows
    (rows : MinimalFailureActualOuterBoundaryAngleDataRows) :
    ActualSelectedBoundaryEuclideanAngleRows :=
  let selectedRows : MinimalFailureSelectedOuterBoundaryAngleRows :=
    selectedOuterBoundaryAngleRowsOfActualOuterBoundaryAngleDataRows rows
  { topology := selectedTopologyRowsOfSelectedOuterBoundaryAngleRows selectedRows
    longArc := selectedLongArcRowsOfSelectedOuterBoundaryAngleRows selectedRows
    degree3 := fun C hmin =>
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        selectedRows C hmin).degree3
    degree4 := fun C hmin =>
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        selectedRows C hmin).degree4
    degree5 := fun C hmin =>
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        selectedRows C hmin).degree5
    degree6 := fun C hmin =>
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        selectedRows C hmin).degree6
    nontriangle := fun C hmin =>
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        selectedRows C hmin).nontriangle
    longArcAngle := fun C hmin =>
      (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
        selectedRows C hmin).longArc
    accounted_le_polygon := fun C hmin =>
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies.toLocalAngleGeometry_accountedAngleSum_le_polygon
        (selectedTopologyLocalEuclideanAngleRowsOfSelectedOuterBoundaryAngleRows
          selectedRows C hmin) }

/-- Exact source shape: the actual W13 rows are equivalent to concrete
Euclidean selected-boundary angle rows, not just to a selected-classification
adapter. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_iff_actualSelectedBoundaryEuclideanAngleRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Nonempty ActualSelectedBoundaryEuclideanAngleRows := by
  constructor
  · intro h
    cases h with
    | intro rows =>
        exact Nonempty.intro
          (actualSelectedBoundaryEuclideanAngleRowsOfActualOuterBoundaryAngleDataRows
            rows)
  · intro h
    cases h with
    | intro rows =>
        exact
          nonempty_actualOuterBoundaryAngleDataRows_of_actualSelectedBoundaryEuclideanAngleRows
            rows

/-- Exact positive source for the actual selected-boundary Euclidean rows:
selected topology plus local unit-separated Euclidean angle geometry is enough,
and actual selected-boundary rows forget back to that same local geometry. -/
theorem nonempty_actualSelectedBoundaryEuclideanAngleRows_iff_exists_selectedTopologyLocalAngleGeometryRows :
    Nonempty ActualSelectedBoundaryEuclideanAngleRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyLocalAngleGeometryRows topology) := by
  constructor
  · intro h
    cases h with
    | intro rows =>
        exact Exists.intro rows.topology
          (Nonempty.intro rows.toSelectedTopologyLocalAngleGeometryRows)
  · intro h
    cases h with
    | intro topology hgeometry =>
        cases hgeometry with
        | intro geometryRows =>
            exact
              nonempty_actualSelectedBoundaryEuclideanAngleRows_of_selectedTopologyLocalAngleGeometryRows
                geometryRows

/-- The minimal-failure selected-angle source target. -/
def MinimalFailureSelectedOuterBoundaryAngleSourceTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty (SelectedOuterBoundaryAngleSource C)

def selectedOuterBoundaryAngleSourceTargetOfRows
    (rows : MinimalFailureSelectedOuterBoundaryAngleRows) :
    MinimalFailureSelectedOuterBoundaryAngleSourceTarget :=
  fun C hmin => Nonempty.intro (rows C hmin)

/-- The selected source target obtained directly from actual Euclidean
selected-boundary angle rows. -/
def selectedOuterBoundaryAngleSourceTargetOfActualSelectedBoundaryEuclideanAngleRows
    (rows : ActualSelectedBoundaryEuclideanAngleRows) :
    MinimalFailureSelectedOuterBoundaryAngleSourceTarget :=
  selectedOuterBoundaryAngleSourceTargetOfRows
    rows.toSelectedOuterBoundaryAngleRows

/-- Concrete actual selected-boundary Euclidean angle rows inhabit the selected
outer-boundary angle source target directly, without passing through the
selected outer-face planar face-data consumer. -/
theorem selectedOuterBoundaryAngleSourceTarget_of_actualSelectedBoundaryEuclideanAngleRows
    (rows : ActualSelectedBoundaryEuclideanAngleRows) :
    MinimalFailureSelectedOuterBoundaryAngleSourceTarget :=
  selectedOuterBoundaryAngleSourceTargetOfActualSelectedBoundaryEuclideanAngleRows
    rows

theorem selectedOuterBoundaryAngleSourceTarget_of_actualOuterBoundaryAngleDataRows
    (rows : MinimalFailureActualOuterBoundaryAngleDataRows) :
    MinimalFailureSelectedOuterBoundaryAngleSourceTarget :=
  selectedOuterBoundaryAngleSourceTargetOfRows
    (selectedOuterBoundaryAngleRowsOfActualOuterBoundaryAngleDataRows rows)

def selectedOuterBoundaryAngleRowsOfSourceTarget
    (target : MinimalFailureSelectedOuterBoundaryAngleSourceTarget) :
    MinimalFailureSelectedOuterBoundaryAngleRows :=
  fun C hmin => Classical.choice (target C hmin)

/-- A live selected outer-boundary angle source supplies the selected outer-face
refined face-data rows through the W34 selected subpolygon constructor. -/
theorem nonempty_selectedOuterFacePlanarBoundaryFaceDataRows_of_selectedOuterBoundaryAngleSourceTarget
    (target : MinimalFailureSelectedOuterBoundaryAngleSourceTarget) :
    Nonempty MinimalFailureSelectedOuterFacePlanarBoundaryFaceDataRows :=
  nonempty_selectedOuterFacePlanarBoundaryFaceDataRows_of_selectedRows
    (selectedOuterBoundaryAngleRowsOfSourceTarget target)

theorem selectedOuterBoundaryAngleSourceTarget_iff_nonempty_rows :
    MinimalFailureSelectedOuterBoundaryAngleSourceTarget <->
      Nonempty MinimalFailureSelectedOuterBoundaryAngleRows := by
  constructor
  case mp =>
    intro h
    exact Nonempty.intro (selectedOuterBoundaryAngleRowsOfSourceTarget h)
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact selectedOuterBoundaryAngleSourceTargetOfRows rows

/-- Exact decomposition of the selected-angle row source into selected topology
rows plus classification/angle-witness rows over those topology rows. -/
theorem nonempty_selectedOuterBoundaryAngleRows_iff_exists_topologyAngleWitnessRows :
    Nonempty MinimalFailureSelectedOuterBoundaryAngleRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyAngleWitnessRows topology) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro rows =>
        let topology : MinimalFailureActualSelectedTopologyRows :=
          fun C hmin => (rows C hmin).topology
        refine Exists.intro topology ?_
        exact
          Nonempty.intro
            { classification := fun C hmin =>
                (rows C hmin).classification
              angleWitness := fun C hmin =>
                (rows C hmin).angleWitness }
  case mpr =>
    intro h
    cases h with
    | intro topology hangle =>
        cases hangle with
        | intro angleRows =>
            exact
              Nonempty.intro
                (selectedOuterBoundaryAngleRowsOfTopologyAngleWitnessRows
                  angleRows)

theorem selectedOuterBoundaryAngleSourceTarget_iff_exists_topologyAngleWitnessRows :
    MinimalFailureSelectedOuterBoundaryAngleSourceTarget <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyAngleWitnessRows topology) :=
  selectedOuterBoundaryAngleSourceTarget_iff_nonempty_rows.trans
    nonempty_selectedOuterBoundaryAngleRows_iff_exists_topologyAngleWitnessRows

theorem nonempty_actualOuterBoundaryAngleDataRows_iff_selectedRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Nonempty MinimalFailureSelectedOuterBoundaryAngleRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro rows =>
        exact
          Nonempty.intro
            (selectedOuterBoundaryAngleRowsOfActualOuterBoundaryAngleDataRows
              rows)
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          Nonempty.intro
            (actualOuterBoundaryAngleDataRowsOfSelectedOuterBoundaryAngleRows
              rows)

theorem nonempty_actualOuterBoundaryAngleDataRows_iff_exists_topologyAngleWitnessRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyAngleWitnessRows topology) :=
  nonempty_actualOuterBoundaryAngleDataRows_iff_selectedRows.trans
    nonempty_selectedOuterBoundaryAngleRows_iff_exists_topologyAngleWitnessRows

/-- If the exact local Euclidean angle witness family is supplied over the
minimal-failure selected classification, then the W13 actual-angle rows are
inhabited. -/
theorem nonempty_actualOuterBoundaryAngleDataRows_of_selectedTopologyLocalEuclideanAngles
    (topology : MinimalFailureActualSelectedTopologyRows)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop)
    (angleWitness :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
            (selectedClassificationOfMinimalFailure
              (topology C hmin) hmin (longArc C hmin))) :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows :=
  Nonempty.intro
    (actualOuterBoundaryAngleDataRowsOfSelectedTopologyLocalEuclideanAngles
      topology longArc angleWitness)

theorem nonempty_actualOuterBoundaryAngleDataRows_iff_exists_selectedTopologyLocalEuclideanAngles :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Exists fun longArc :
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop =>
          Nonempty
            (forall {n : Nat} (C : _root_.UDConfig n)
              (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
                OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
                  (selectedClassificationOfMinimalFailure
                    (topology C hmin) hmin (longArc C hmin))) := by
  constructor
  · intro h
    cases h with
    | intro rows =>
        exact
          exists_selectedTopologyLocalEuclideanAngles_of_actualOuterBoundaryAngleDataRows
            rows
  · intro h
    cases h with
    | intro topology hlong =>
        cases hlong with
        | intro longArc hangleWitness =>
            cases hangleWitness with
            | intro angleWitness =>
                exact
                  nonempty_actualOuterBoundaryAngleDataRows_of_selectedTopologyLocalEuclideanAngles
                    topology longArc angleWitness

end

end OuterBoundaryAngleSourceW34
end Swanepoel

namespace Verified

open Swanepoel
open Swanepoel.OuterBoundaryAngleSourceW34

abbrev SwanepoelW34MinimalFailureSelectedOuterBoundaryAngleSourceTarget : Prop :=
  Swanepoel.OuterBoundaryAngleSourceW34.MinimalFailureSelectedOuterBoundaryAngleSourceTarget

theorem swanepoelW34_selectedOuterBoundaryAngleSource_exactly_rows :
    SwanepoelW34MinimalFailureSelectedOuterBoundaryAngleSourceTarget <->
      Nonempty MinimalFailureSelectedOuterBoundaryAngleRows :=
  selectedOuterBoundaryAngleSourceTarget_iff_nonempty_rows

theorem swanepoelW34_selectedOuterBoundaryAngleSource_exactly_topology_angleWitnessRows :
    SwanepoelW34MinimalFailureSelectedOuterBoundaryAngleSourceTarget <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyAngleWitnessRows topology) :=
  selectedOuterBoundaryAngleSourceTarget_iff_exists_topologyAngleWitnessRows

theorem swanepoelW34_actualOuterBoundaryAngleDataRows_exactly_selectedRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Nonempty MinimalFailureSelectedOuterBoundaryAngleRows :=
  nonempty_actualOuterBoundaryAngleDataRows_iff_selectedRows

theorem swanepoelW34_actualOuterBoundaryAngleDataRows_exactly_topology_angleWitnessRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyAngleWitnessRows topology) :=
  nonempty_actualOuterBoundaryAngleDataRows_iff_exists_topologyAngleWitnessRows

theorem swanepoelW34_actualOuterBoundaryAngleDataRows_exactly_selectedTopologyLocalEuclideanAngles :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Exists fun longArc :
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              Fin ((topology C hmin).toOuterBoundaryCore.outerCycle.length) -> Prop =>
          Nonempty
            (forall {n : Nat} (C : _root_.UDConfig n)
              (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
                OuterBoundaryAngleW12.UnitSeparatedAngleFamilies
                  (selectedClassificationOfMinimalFailure
                    (topology C hmin) hmin (longArc C hmin))) :=
  nonempty_actualOuterBoundaryAngleDataRows_iff_exists_selectedTopologyLocalEuclideanAngles

theorem swanepoelW34_actualOuterBoundaryAngleDataRows_exactly_selectedTopologyLocalAngleGeometryRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyLocalAngleGeometryRows topology) :=
  nonempty_actualOuterBoundaryAngleDataRows_iff_exists_selectedTopologyLocalAngleGeometryRows

theorem swanepoelW34_actualOuterBoundaryAngleDataRows_exactly_actualSelectedBoundaryEuclideanAngleRows :
    Nonempty MinimalFailureActualOuterBoundaryAngleDataRows <->
      Nonempty ActualSelectedBoundaryEuclideanAngleRows :=
  nonempty_actualOuterBoundaryAngleDataRows_iff_actualSelectedBoundaryEuclideanAngleRows

theorem swanepoelW34_actualSelectedBoundaryEuclideanAngleRows_exactly_selectedTopologyLocalAngleGeometryRows :
    Nonempty ActualSelectedBoundaryEuclideanAngleRows <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (SelectedTopologyLocalAngleGeometryRows topology) :=
  nonempty_actualSelectedBoundaryEuclideanAngleRows_iff_exists_selectedTopologyLocalAngleGeometryRows

end Verified
end ErdosProblems1066
