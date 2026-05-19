import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.BoundaryLabelExtractionTasks
import ErdosProblems1066.Swanepoel.BoundaryWalkConstruction
import ErdosProblems1066.Swanepoel.AngleBridgeFacts
import ErdosProblems1066.Swanepoel.Figure8ExplicitEuclideanFactsCompletionW33
import ErdosProblems1066.Swanepoel.Figure9EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.Lemma8ForbiddenDistinctConcrete
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9

set_option autoImplicit false

/-!
# Assembly from finite boundary labels to the M8 construction interface

This module is the certificate route that starts with explicit finite
boundary labels `p_i, q_i`, adds the still-explicit Lemma 8 labels `r_i, s_i`,
and then reaches the clean `M8ConstructionData` package once the remaining
turn, late-triple, and window-geometry certificates are supplied.

No existence theorem is hidden here.  The finite boundary labels come from
`BoundarySpineFiniteCertificate`, the label projections come from
`BoundaryLabelExtractionTasks` and `M8BoundaryLabelsConcrete`, and the later
non-label M8 data remains explicit.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelCertificateAssembly

open BoundaryFaceCountingToM8
open BoundarySpineFiniteCertificate
open BoundaryWalkConstruction
open CutVertexClosure
open GraphBridge
open Lemma8ForbiddenDistinctConcrete
open Lemma10Bridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts
open PlanarInterface

universe u

noncomputable section

variable {n : Nat}
variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-! ## Boundary-label certificates -/

/--
Finite boundary `p/q` labels together with the explicit Lemma 8 combinatorics
for the resulting spine.
-/
structure M8FiniteBoundaryLabelCertificate
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  finiteLabels : M8FinitePQSpineCertificate D
  lemma8 :
    M8Lemma8Combinatorics
      (finiteLabels.toM8BoundarySpine connectedNoCut hmin)

namespace M8FiniteBoundaryLabelCertificate

variable (K :
  M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)

/-- The boundary/cut/degree context supplied by the selected planar boundary. -/
def context :
    M8BoundaryCutDegreeContext C :=
  K.finiteLabels.context connectedNoCut hmin

/-- The boundary spine obtained from the explicit finite labels. -/
def spine :
    M8BoundarySpine K.context :=
  K.finiteLabels.toM8BoundarySpine connectedNoCut hmin

/-- The planar-boundary route with checked face-counting data attached. -/
def toM8BoundaryRouteData :
    M8BoundaryRouteData.{u} C hmin :=
  K.finiteLabels.toM8BoundaryRouteData
    connectedNoCut hmin K.lemma8

/-- Forget to the concrete boundary-label package. -/
def toBoundaryLabelPackage :
    M8BoundaryLabelPackage C :=
  K.toM8BoundaryRouteData.toBoundaryLabelPackage

/-- The local labels extracted from the finite boundary certificate and
Lemma 8 package. -/
def toM8LocalLabels :
    M8LocalLabels C :=
  K.toBoundaryLabelPackage.toM8LocalLabels

@[simp]
theorem context_eq :
    K.context =
      boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin :=
  rfl

@[simp]
theorem spine_eq :
    K.spine =
      K.finiteLabels.toM8BoundarySpine connectedNoCut hmin :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_spine :
    K.toM8BoundaryRouteData.spine = K.spine :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_context :
    K.toBoundaryLabelPackage.context = K.context :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_spine :
    K.toBoundaryLabelPackage.spine = K.spine :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8 :
    K.toBoundaryLabelPackage.lemma8 = K.lemma8 :=
  rfl

@[simp]
theorem toM8LocalLabels_eq :
    K.toM8LocalLabels = K.toM8BoundaryRouteData.toM8LocalLabels :=
  rfl

@[simp]
theorem labels_p (i : M8BoundaryIndex) :
    K.toM8LocalLabels.labels.p i = K.finiteLabels.p i :=
  rfl

@[simp]
theorem labels_q (i : M8TriangleIndex) :
    K.toM8LocalLabels.labels.q i = K.finiteLabels.q i :=
  rfl

@[simp]
theorem labels_r (i : M8ExtraIndex) :
    K.toM8LocalLabels.labels.r i = K.lemma8.r i :=
  rfl

@[simp]
theorem labels_s (i : M8ExtraIndex) :
    K.toM8LocalLabels.labels.s i = K.lemma8.s i :=
  rfl

/-- The boundary-edge predicate in the assembled local package is supplied by
the finite boundary certificate. -/
theorem boundaryEdge (i : M8TriangleIndex) :
    K.toBoundaryLabelPackage.predicates.data.boundaryEdge i :=
  K.toBoundaryLabelPackage.boundaryEdge i

/-- The triangle-witness predicate in the assembled local package is supplied
by the finite boundary certificate. -/
theorem triangleWitness (i : M8TriangleIndex) :
    K.toBoundaryLabelPackage.predicates.data.triangleWitness i :=
  K.toBoundaryLabelPackage.triangleWitness i

/-- The extra-neighbor predicate in the assembled local package is supplied by
the explicit Lemma 8 certificate. -/
theorem extraNeighborWitness (i : M8ExtraIndex) :
    K.toBoundaryLabelPackage.predicates.data.extraNeighborWitness i :=
  K.toBoundaryLabelPackage.extraNeighborWitness i

/-- The assembled finite-label package preserves preconnectedness from the
boundary/cut/degree context. -/
theorem preconnected
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin) :
    (unitDistanceSimpleGraph C).Preconnected :=
  M8BoundaryCutDegreeContext.preconnected (context K)

/-- The assembled finite-label package preserves the no-cut-vertex field from
the boundary/cut/degree context. -/
theorem noCutVertex
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin) :
    CutVertexInterface.NoCutVertex C :=
  M8BoundaryCutDegreeContext.noCutVertex (context K)

/-- The assembled finite-label package preserves the lower degree bound from
the boundary/cut/degree context. -/
theorem minDegree
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  M8BoundaryCutDegreeContext.minDegree (context K) v

/-- The assembled finite-label package preserves the upper degree bound from
the boundary/cut/degree context. -/
theorem maxDegree
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  M8BoundaryCutDegreeContext.maxDegree (context K) v

/-- The explicitly named boundary labels lie on the selected outer boundary. -/
theorem p_onBoundary (i : M8BoundaryIndex) :
    K.context.outerBoundary.outerEnclosure.onBoundary (K.finiteLabels.p i) :=
  K.finiteLabels.p_onBoundary connectedNoCut hmin i

/-- The center `q_i` is adjacent to the left boundary endpoint for each
extra-neighbor index. -/
theorem center_adj_left (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (K.spine.centerQ i) (K.spine.leftP i) :=
  K.spine.centerQ_adj_leftP i

/-- The center `q_i` is adjacent to the right boundary endpoint for each
extra-neighbor index. -/
theorem center_adj_right (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (K.spine.centerQ i) (K.spine.rightP i) :=
  K.spine.centerQ_adj_rightP i

/-- Projection of the `r_i` neighbor field from the explicit Lemma 8 package. -/
theorem r_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (K.spine.centerQ i) (K.lemma8.r i) :=
  K.lemma8.r_neighbor i

/-- Projection of the `s_i` neighbor field from the explicit Lemma 8 package. -/
theorem s_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (K.spine.centerQ i) (K.lemma8.s i) :=
  K.lemma8.s_neighbor i

/-- Projection that `r_i` is outside the finite forbidden neighbor list. -/
theorem r_not_forbidden (i : M8ExtraIndex) :
    Not (K.spine.forbiddenExtraNeighbor i (K.lemma8.r i)) :=
  K.lemma8.r_not_forbidden i

/-- Projection that `s_i` is outside the finite forbidden neighbor list. -/
theorem s_not_forbidden (i : M8ExtraIndex) :
    Not (K.spine.forbiddenExtraNeighbor i (K.lemma8.s i)) :=
  K.lemma8.s_not_forbidden i

/-- Projection that the two explicit extra neighbors are distinct. -/
theorem r_ne_s (i : M8ExtraIndex) :
    Not (K.lemma8.r i = K.lemma8.s i) :=
  K.lemma8.r_ne_s i

/-- Projection of the Lemma 8 exhaustive naming statement. -/
theorem named_of_extra_neighbor
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (K.spine.centerQ i) x)
    (hnot : Not (K.spine.forbiddenExtraNeighbor i x)) :
    x = K.lemma8.r i \/ x = K.lemma8.s i :=
  K.lemma8.named_of_extra_neighbor hadj hnot

/-- Projection of the positive cyclic-order predicate stored in the explicit
Lemma 8 package. -/
theorem positiveCyclicOrder (i : M8ExtraIndex) :
    K.lemma8.positiveCyclicOrderAt i
      (K.lemma8.s i) (K.lemma8.r i)
      (K.spine.prevQ i) (K.spine.leftP i)
      (K.spine.rightP i) (K.spine.nextQ i) :=
  K.lemma8.positiveCyclicOrder_holds i

/-- For the finite boundary-label certificate, the forbidden-label
distinctness field reduces to one finite no-collision family.  The boundary
edge and neighboring triangle witnesses already force the other three
distinctness clauses. -/
theorem forbiddenLabelsPairwiseDistinct_of_remaining_three
    (h :
      forall i : M8ExtraIndex,
        Not (K.spine.leftP i = K.spine.nextQ i) /\
        Not (K.spine.rightP i = K.spine.prevQ i) /\
        Not (K.spine.prevQ i = K.spine.nextQ i)) :
    forall i : M8ExtraIndex,
      FourForbiddenLabelsPairwiseDistinct K.spine i :=
  fourForbiddenLabelsPairwiseDistinct_family_of_remaining_three
    (S := K.spine) h

/-- Equivalence form of the same reduction for the assembled real M8
boundary labels. -/
theorem forbiddenLabelsPairwiseDistinct_iff_remaining_three :
    (forall i : M8ExtraIndex,
      FourForbiddenLabelsPairwiseDistinct K.spine i) <->
      forall i : M8ExtraIndex,
        Not (K.spine.leftP i = K.spine.nextQ i) /\
        Not (K.spine.rightP i = K.spine.prevQ i) /\
        Not (K.spine.prevQ i = K.spine.nextQ i) :=
  fourForbiddenLabelsPairwiseDistinct_family_iff_remaining_three
    (S := K.spine)

/-- The assembled real boundary spine has degree six at each Lemma 8 center
as soon as its honest frame core is available.  The stored Lemma 8 package
supplies the exact two non-forbidden neighbors. -/
theorem centerDegreeSix_of_frameCore
    (F : M8FourForbiddenFrameCore K.spine) :
    forall i : M8ExtraIndex,
      Lemma8ExistenceConcrete.centerDegree K.spine i = 6 :=
  centerDegreeSix_of_lemma8Combinatorics_and_frameCore
    (S := K.spine) K.lemma8 F

/-- The exact remaining no-collision family for the assembled real boundary
spine follows from the honest frame core. -/
theorem remaining_three_noCollision_of_frameCore
    (F : M8FourForbiddenFrameCore K.spine) :
    forall i : M8ExtraIndex,
      Not (K.spine.leftP i = K.spine.nextQ i) /\
      Not (K.spine.rightP i = K.spine.prevQ i) /\
      Not (K.spine.prevQ i = K.spine.nextQ i) :=
  remaining_three_noCollision_of_lemma8Combinatorics_and_frameCore
    (S := K.spine) K.lemma8 F

/-- Forbidden-label pairwise distinctness for the assembled real boundary
spine follows from the honest frame core, with no separate degree-six premise.
-/
theorem forbiddenLabelsPairwiseDistinct_of_frameCore
    (F : M8FourForbiddenFrameCore K.spine) :
    forall i : M8ExtraIndex,
      FourForbiddenLabelsPairwiseDistinct K.spine i :=
  fourForbiddenLabelsPairwiseDistinct_family_of_lemma8Combinatorics_and_frameCore
    (S := K.spine) K.lemma8 F

/-- Assemble `M8ConstructionData` once the remaining non-label M8 certificates
are supplied. -/
def toM8ConstructionData
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  K.toBoundaryLabelPackage.toM8ConstructionData
    turnBounds lateTriples windowGeometry

/-- Concrete five-start no-early equality for the assembled labels is the
local Lemma 9 source used by the late-triples bridge. -/
def noEarlyLateTriplesSourceOfConcreteNoEarlyTripleEquality
    (H :
      NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
        K.toM8LocalLabels.predicates.data) :
    NoEarlyTripleFromLemma9.LocalLabelNoEarlyLateTriplesSource
      K.toM8LocalLabels :=
  NoEarlyTripleFromLemma9.LocalLabelNoEarlyLateTriplesSource.ofConcreteNoEarlyTripleEquality
    H

/-- Concrete five-start no-early equality supplies the construction-interface
late-triples field for the assembled finite boundary labels. -/
def lateTriplesOfConcreteNoEarlyTripleEquality
    (H :
      NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
        K.toM8LocalLabels.predicates.data) :
    M8LateTriples K.toM8LocalLabels :=
  (K.noEarlyLateTriplesSourceOfConcreteNoEarlyTripleEquality H).toM8LateTriples

/-- Assemble `M8ConstructionData` from finite boundary labels, turn/window
data, and concrete five-start no-early equality. -/
def toM8ConstructionDataOfConcreteNoEarlyTripleEquality
    (H :
      NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
        K.toM8LocalLabels.predicates.data)
    (turnBounds : M8TurnBounds)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  K.toM8ConstructionData turnBounds
    (K.lateTriplesOfConcreteNoEarlyTripleEquality H) windowGeometry

@[simp]
theorem toM8ConstructionData_localLabels
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels =
        K.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8ConstructionData_turnBounds
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).turnBounds =
        turnBounds :=
  rfl

@[simp]
theorem toM8ConstructionData_lateTriples
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).lateTriples =
        lateTriples :=
  rfl

@[simp]
theorem toM8ConstructionData_windowGeometry
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).windowGeometry =
        windowGeometry :=
  rfl

@[simp]
theorem toM8ConstructionData_labels_p
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8BoundaryIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.labels.p i =
        K.finiteLabels.p i :=
  rfl

@[simp]
theorem toM8ConstructionData_labels_q
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8TriangleIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.labels.q i =
        K.finiteLabels.q i :=
  rfl

@[simp]
theorem toM8ConstructionData_labels_r
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8ExtraIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.labels.r i =
        K.lemma8.r i :=
  rfl

@[simp]
theorem toM8ConstructionData_labels_s
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8ExtraIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.labels.s i =
        K.lemma8.s i :=
  rfl

/-- The construction data keeps the boundary-edge facts supplied by the
finite boundary certificate. -/
theorem toM8ConstructionData_boundaryEdge
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8TriangleIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.predicates.data.boundaryEdge
        i :=
  K.finiteLabels.boundaryEdge i

/-- The construction data keeps the triangle-witness facts supplied by the
finite boundary certificate. -/
theorem toM8ConstructionData_triangleWitness
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8TriangleIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.predicates.data.triangleWitness
        i :=
  K.finiteLabels.triangleWitness i

/-- The construction data keeps the extra-neighbor facts supplied by the
explicit Lemma 8 certificate. -/
theorem toM8ConstructionData_extraNeighborWitness
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds)
    (i : M8ExtraIndex) :
    (K.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels.predicates.data.extraNeighborWitness
        i :=
  K.lemma8.extraNeighborWitness_holds i

/-- The same assembly expressed through the concrete construction wrapper. -/
def toBoundaryConstructionPackage
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    M8BoundaryConstructionPackage C hmin where
  boundaryLabels := K.toBoundaryLabelPackage
  turnBounds := turnBounds
  lateTriples := lateTriples
  windowGeometry := windowGeometry

@[simp]
theorem toBoundaryConstructionPackage_boundaryLabels
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    (K.toBoundaryConstructionPackage
      turnBounds lateTriples windowGeometry).boundaryLabels =
        K.toBoundaryLabelPackage :=
  rfl

@[simp]
theorem toBoundaryConstructionPackage_toM8ConstructionData
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    (K.toBoundaryConstructionPackage
      turnBounds lateTriples windowGeometry).toM8ConstructionData =
        K.toM8ConstructionData turnBounds lateTriples windowGeometry :=
  rfl

/-- Conditional endpoint: after the finite boundary labels, Lemma 8, and the
remaining M8 fields are supplied, the existing broken-lattice closure gives
the contradiction for the indexed minimal cleared failure. -/
theorem contradiction
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    False :=
  (K.toBoundaryConstructionPackage
    turnBounds lateTriples windowGeometry).contradiction

/-- Conditional endpoint using concrete five-start no-early equality instead
of asking separately for construction late triples. -/
theorem contradictionOfConcreteNoEarlyTripleEquality
    (H :
      NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
        K.toM8LocalLabels.predicates.data)
    (turnBounds : M8TurnBounds)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    False :=
  K.contradiction turnBounds
    (K.lateTriplesOfConcreteNoEarlyTripleEquality H) windowGeometry

end M8FiniteBoundaryLabelCertificate

/-! ## Boundary-label certificates with the actual frame core -/

/--
Finite boundary labels, Lemma 8 combinatorics, and the raw finite-spine
frame-core fields for the same generated boundary spine.

This packages the actual frame-core production point: the downstream
`M8FourForbiddenFrameCore` is derived from the finite spine fields rather than
passed in as an unrelated adapter premise.
-/
structure M8FiniteBoundaryFrameCoreLabelCertificate
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  finiteLabels : M8FinitePQSpineCertificate D
  frameCoreFields :
    M8FinitePQSpineFrameCoreFields finiteLabels connectedNoCut hmin
  lemma8 :
    M8Lemma8Combinatorics
      (finiteLabels.toM8BoundarySpine connectedNoCut hmin)

namespace M8FiniteBoundaryFrameCoreLabelCertificate

variable (K :
  M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)

def toFiniteBoundaryLabelCertificate :
    M8FiniteBoundaryLabelCertificate D connectedNoCut hmin where
  finiteLabels := K.finiteLabels
  lemma8 := K.lemma8

def context :
    M8BoundaryCutDegreeContext C :=
  K.toFiniteBoundaryLabelCertificate.context

def spine :
    M8BoundarySpine K.context :=
  K.toFiniteBoundaryLabelCertificate.spine

def toM8LocalLabels :
    M8LocalLabels C :=
  K.toFiniteBoundaryLabelCertificate.toM8LocalLabels

/-- The actual four-forbidden frame core generated by the finite-spine fields.
-/
def frameCore :
    M8FourForbiddenFrameCore K.spine :=
  { core := fun i =>
      { prev_adj := K.frameCoreFields.prev_adj i
        next_adj := K.frameCoreFields.next_adj i
        left_ne_next := K.frameCoreFields.left_ne_next i
        right_ne_prev := K.frameCoreFields.right_ne_prev i
        prev_ne_next := K.frameCoreFields.prev_ne_next i } }

def toFrameCoreLabelRows :
    M8FiniteBoundaryLabelCertificate D connectedNoCut hmin ×
      PLift (M8FourForbiddenFrameCore K.spine) :=
  (K.toFiniteBoundaryLabelCertificate, PLift.up K.frameCore)

theorem centerDegreeSix :
    forall i : M8ExtraIndex,
      Lemma8ExistenceConcrete.centerDegree K.spine i = 6 :=
  K.toFiniteBoundaryLabelCertificate.centerDegreeSix_of_frameCore
    K.frameCore

theorem remaining_three_noCollision :
    forall i : M8ExtraIndex,
      Not (K.spine.leftP i = K.spine.nextQ i) /\
      Not (K.spine.rightP i = K.spine.prevQ i) /\
      Not (K.spine.prevQ i = K.spine.nextQ i) :=
  K.toFiniteBoundaryLabelCertificate.remaining_three_noCollision_of_frameCore
    K.frameCore

theorem forbiddenLabelsPairwiseDistinct :
    forall i : M8ExtraIndex,
      FourForbiddenLabelsPairwiseDistinct K.spine i :=
  K.toFiniteBoundaryLabelCertificate.forbiddenLabelsPairwiseDistinct_of_frameCore
    K.frameCore

/-! ### Label-to-Figure distance rows -/

private def lemma10IndexOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8Lemma10Index :=
  m8Lemma10IndexOfNat i ⟨hi, hi10⟩

private def leftExtraOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8ExtraIndex :=
  m8LeftExtraIndex (lemma10IndexOfNat i hi hi10)

private def rightExtraOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8ExtraIndex :=
  m8RightExtraIndex (lemma10IndexOfNat i hi hi10)

/-- Public comparison index used by the five bad-adjacency incidence rows. -/
def badAdjacencyLemma10IndexOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8Lemma10Index :=
  m8Lemma10IndexOfNat i (And.intro hi hi10)

/-- The left extra index for the bad-adjacency row starting at `i`. -/
def badAdjacencyLeftExtraOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8ExtraIndex :=
  m8LeftExtraIndex (badAdjacencyLemma10IndexOfNat i hi hi10)

/-- The right extra index for the bad-adjacency row starting at `i`. -/
def badAdjacencyRightExtraOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8ExtraIndex :=
  m8RightExtraIndex (badAdjacencyLemma10IndexOfNat i hi hi10)

private theorem rightP_leftExtra_eq_leftP_rightExtra
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    K.spine.rightP (leftExtraOfNat i hi hi10) =
      K.spine.leftP (rightExtraOfNat i hi hi10) := by
  simp [leftExtraOfNat, rightExtraOfNat, lemma10IndexOfNat,
    M8BoundarySpine.rightP, M8BoundarySpine.leftP,
    m8LeftExtraIndex, m8RightExtraIndex, m8TriangleIndexOfExtra,
    m8BoundaryIndexRight, m8BoundaryIndexLeft]

private theorem nextQ_leftExtra_eq_centerQ_rightExtra
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    K.spine.nextQ (leftExtraOfNat i hi hi10) =
      K.spine.centerQ (rightExtraOfNat i hi hi10) := by
  simp [leftExtraOfNat, rightExtraOfNat, lemma10IndexOfNat,
    M8BoundarySpine.nextQ, M8BoundarySpine.centerQ,
    m8LeftExtraIndex, m8RightExtraIndex, m8TriangleIndexOfExtra,
    m8TriangleIndexNextOfExtra]

private theorem labelFailure_s_ne_right_r
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (hbad :
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i)) :
    Not
      (K.lemma8.s (leftExtraOfNat i hi hi10) =
        K.lemma8.r (rightExtraOfNat i hi hi10)) := by
  have hbadLabel :
      Not (M8LabelGood K.toM8LocalLabels.predicates.data.labels i) := by
    intro hgood
    exact hbad
      ((K.toM8LocalLabels.predicates.good_iff_labelGood i).2 hgood)
  simpa [M8LabelGood, hi, hi10, M8LabelEquality, leftExtraOfNat,
    rightExtraOfNat, lemma10IndexOfNat] using hbadLabel

private theorem centerQ_left_ne_centerQ_right
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.centerQ (leftExtraOfNat i hi hi10) =
        K.spine.centerQ (rightExtraOfNat i hi hi10)) := by
  intro h
  have hadj :=
    K.frameCore.next_adj (leftExtraOfNat i hi hi10)
  have hnext :
      K.spine.nextQ (leftExtraOfNat i hi hi10) =
        K.spine.centerQ (leftExtraOfNat i hi hi10) := by
    calc
      K.spine.nextQ (leftExtraOfNat i hi hi10) =
          K.spine.centerQ (rightExtraOfNat i hi hi10) :=
        nextQ_leftExtra_eq_centerQ_rightExtra (K := K) hi hi10
      _ = K.spine.centerQ (leftExtraOfNat i hi hi10) := h.symm
  rw [hnext] at hadj
  exact (unitDistanceLocalGraph C).loopless
    (K.spine.centerQ (leftExtraOfNat i hi hi10)) hadj

private theorem rightP_ne_left_s
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.rightP (leftExtraOfNat i hi hi10) =
        K.lemma8.s (leftExtraOfNat i hi hi10)) := by
  intro h
  exact
    K.lemma8.s_not_forbidden (leftExtraOfNat i hi hi10)
      (Or.inr (Or.inl h.symm))

private theorem rightP_ne_right_r
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.rightP (leftExtraOfNat i hi hi10) =
        K.lemma8.r (rightExtraOfNat i hi hi10)) := by
  intro h
  have hp :
      K.spine.rightP (leftExtraOfNat i hi hi10) =
        K.spine.leftP (rightExtraOfNat i hi hi10) :=
    rightP_leftExtra_eq_leftP_rightExtra (K := K) hi hi10
  exact
    K.lemma8.r_not_forbidden (rightExtraOfNat i hi hi10)
      (Or.inl (h.symm.trans hp))

theorem rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
      K.spine.leftP (badAdjacencyRightExtraOfNat i hi hi10) := by
  simpa [badAdjacencyLeftExtraOfNat, badAdjacencyRightExtraOfNat,
    badAdjacencyLemma10IndexOfNat, leftExtraOfNat, rightExtraOfNat,
    lemma10IndexOfNat] using
    rightP_leftExtra_eq_leftP_rightExtra (K := K) hi hi10

theorem nextQ_badAdjacencyLeft_eq_centerQ_badAdjacencyRight
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    K.spine.nextQ (badAdjacencyLeftExtraOfNat i hi hi10) =
      K.spine.centerQ (badAdjacencyRightExtraOfNat i hi hi10) := by
  simpa [badAdjacencyLeftExtraOfNat, badAdjacencyRightExtraOfNat,
    badAdjacencyLemma10IndexOfNat, leftExtraOfNat, rightExtraOfNat,
    lemma10IndexOfNat] using
    nextQ_leftExtra_eq_centerQ_rightExtra (K := K) hi hi10

theorem labelEquality_of_badAdjacencyTripleStart
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (histart : i + 2 <= 10)
    (htriple :
      K.toM8LocalLabels.predicates.data.tripleEquality
        (m8TripleStartIndexOfNat i (And.intro hi histart))) :
    K.lemma8.s (badAdjacencyLeftExtraOfNat i hi hi10) =
      K.lemma8.r (badAdjacencyRightExtraOfNat i hi hi10) := by
  have hbroken :
      M8BrokenLatticeTriple K.toM8LocalLabels.predicates.data
        (m8TripleStartIndexOfNat i (And.intro hi histart)) :=
    (K.toM8LocalLabels.predicates.tripleEquality_iff_threeComparisons
      (m8TripleStartIndexOfNat i (And.intro hi histart))).1 htriple
  have hgood : M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i := by
    simpa [M8BrokenLatticeTriple, m8TripleStartIndexOfNat] using hbroken.1
  have hlabel : M8LabelGood K.toM8LocalLabels.predicates.data.labels i :=
    (K.toM8LocalLabels.predicates.good_iff_labelGood i).1 hgood
  simpa [M8LabelGood, hi, hi10, M8LabelEquality,
    badAdjacencyLeftExtraOfNat, badAdjacencyRightExtraOfNat,
    badAdjacencyLemma10IndexOfNat] using hlabel

theorem centerQ_badAdjacencyLeft_ne_centerQ_badAdjacencyRight
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.centerQ (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.spine.centerQ (badAdjacencyRightExtraOfNat i hi hi10)) := by
  intro h
  have hadj :=
    K.frameCore.next_adj (badAdjacencyLeftExtraOfNat i hi hi10)
  have hnext :
      K.spine.nextQ (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.spine.centerQ (badAdjacencyLeftExtraOfNat i hi hi10) := by
    calc
      K.spine.nextQ (badAdjacencyLeftExtraOfNat i hi hi10) =
          K.spine.centerQ (badAdjacencyRightExtraOfNat i hi hi10) :=
        nextQ_badAdjacencyLeft_eq_centerQ_badAdjacencyRight (K := K) hi hi10
      _ = K.spine.centerQ (badAdjacencyLeftExtraOfNat i hi hi10) := h.symm
  rw [hnext] at hadj
  exact (unitDistanceLocalGraph C).loopless
    (K.spine.centerQ (badAdjacencyLeftExtraOfNat i hi hi10)) hadj

theorem rightP_badAdjacencyLeft_ne_s_left
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.lemma8.s (badAdjacencyLeftExtraOfNat i hi hi10)) := by
  intro h
  exact
    K.lemma8.s_not_forbidden (badAdjacencyLeftExtraOfNat i hi hi10)
      (Or.inr (Or.inl h.symm))

theorem rightP_badAdjacencyLeft_ne_s_right
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.lemma8.s (badAdjacencyRightExtraOfNat i hi hi10)) := by
  intro h
  have hp :
      K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.spine.leftP (badAdjacencyRightExtraOfNat i hi hi10) :=
    rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight (K := K) hi hi10
  exact
    K.lemma8.s_not_forbidden (badAdjacencyRightExtraOfNat i hi hi10)
      (Or.inl (h.symm.trans hp))

theorem rightP_badAdjacencyLeft_ne_r_right
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.lemma8.r (badAdjacencyRightExtraOfNat i hi hi10)) := by
  intro h
  have hp :
      K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.spine.leftP (badAdjacencyRightExtraOfNat i hi hi10) :=
    rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight (K := K) hi hi10
  exact
    K.lemma8.r_not_forbidden (badAdjacencyRightExtraOfNat i hi hi10)
      (Or.inl (h.symm.trans hp))

theorem s_badAdjacencyLeft_ne_s_badAdjacencyRight_of_tripleStart
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (histart : i + 2 <= 10)
    (htriple :
      K.toM8LocalLabels.predicates.data.tripleEquality
        (m8TripleStartIndexOfNat i (And.intro hi histart))) :
    Not
      (K.lemma8.s (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.lemma8.s (badAdjacencyRightExtraOfNat i hi hi10)) := by
  intro h
  have heq :=
    labelEquality_of_badAdjacencyTripleStart (K := K) hi hi10 histart htriple
  exact
    K.lemma8.r_ne_s (badAdjacencyRightExtraOfNat i hi hi10)
      (heq.symm.trans h)

/-- The five concrete bad-adjacency incidences needed by the K23 route:
`Adj q_1 s_2` through `Adj q_5 s_6`, read from the finite boundary labels. -/
structure BadAdjacencyIncidenceRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin) :
    Prop where
  adj_q1_s2 :
    (unitDistanceLocalGraph C).Adj
      (K.spine.centerQ (badAdjacencyLeftExtraOfNat 1 (by omega) (by omega)))
      (K.lemma8.s (badAdjacencyRightExtraOfNat 1 (by omega) (by omega)))
  adj_q2_s3 :
    (unitDistanceLocalGraph C).Adj
      (K.spine.centerQ (badAdjacencyLeftExtraOfNat 2 (by omega) (by omega)))
      (K.lemma8.s (badAdjacencyRightExtraOfNat 2 (by omega) (by omega)))
  adj_q3_s4 :
    (unitDistanceLocalGraph C).Adj
      (K.spine.centerQ (badAdjacencyLeftExtraOfNat 3 (by omega) (by omega)))
      (K.lemma8.s (badAdjacencyRightExtraOfNat 3 (by omega) (by omega)))
  adj_q4_s5 :
    (unitDistanceLocalGraph C).Adj
      (K.spine.centerQ (badAdjacencyLeftExtraOfNat 4 (by omega) (by omega)))
      (K.lemma8.s (badAdjacencyRightExtraOfNat 4 (by omega) (by omega)))
  adj_q5_s6 :
    (unitDistanceLocalGraph C).Adj
      (K.spine.centerQ (badAdjacencyLeftExtraOfNat 5 (by omega) (by omega)))
      (K.lemma8.s (badAdjacencyRightExtraOfNat 5 (by omega) (by omega)))

/-- One bad-adjacency incidence row, expressed directly in the finite
`p_i/q_i` labels and the Lemma 8 `s_i` labels. -/
def BadAdjacencyFiniteLabelIncidenceRowAt
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) : Prop :=
  (unitDistanceLocalGraph C).Adj
    (K.finiteLabels.q
      (m8TriangleIndexOfExtra
        (badAdjacencyLeftExtraOfNat i hi hi10)))
    (K.lemma8.s (badAdjacencyRightExtraOfNat i hi hi10))

/-- The same bad-adjacency incidence row, phrased through the assembled local
label package.  This is the shape expected from a generated local-label
certificate. -/
def BadAdjacencyLocalLabelIncidenceRowAt
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) : Prop :=
  (unitDistanceLocalGraph C).Adj
    (K.toM8LocalLabels.labels.q
      (m8TriangleIndexOfExtra
        (badAdjacencyLeftExtraOfNat i hi hi10)))
    (K.toM8LocalLabels.labels.s
      (badAdjacencyRightExtraOfNat i hi hi10))

/--
Import-cycle-free form of the downstream selected finite-label Figure 9 row
for one bad-adjacency cross pair.  The row includes the full Figure 9 finite
adjacency/distinctness datum, and the third adjacency is exactly the desired
local incidence `q_i ~ s_{i+1}`.
-/
def BadAdjacencySelectedFiniteLabelFigure9RowAt
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) : Prop :=
  Exists fun p : Fin n =>
  Exists fun qj : Fin n =>
  Exists fun r : Fin n =>
    GraphBridge.UnitDistanceAdj C p
        (K.toM8LocalLabels.labels.q
          (m8TriangleIndexOfExtra
            (badAdjacencyLeftExtraOfNat i hi hi10))) /\
      GraphBridge.UnitDistanceAdj C p qj /\
      GraphBridge.UnitDistanceAdj C
        (K.toM8LocalLabels.labels.q
          (m8TriangleIndexOfExtra
            (badAdjacencyLeftExtraOfNat i hi hi10)))
        (K.toM8LocalLabels.labels.s
          (badAdjacencyRightExtraOfNat i hi hi10)) /\
      GraphBridge.UnitDistanceAdj C qj r /\
      Ne
        (K.toM8LocalLabels.labels.q
          (m8TriangleIndexOfExtra
            (badAdjacencyLeftExtraOfNat i hi hi10)))
        qj /\
      Ne p
        (K.toM8LocalLabels.labels.s
          (badAdjacencyRightExtraOfNat i hi hi10)) /\
      Ne p r /\
      Ne
        (K.toM8LocalLabels.labels.s
          (badAdjacencyRightExtraOfNat i hi hi10))
        r

/--
Row-wise selected finite-label Figure 9 data for the five bad-adjacency cross
pairs.  This is the assembly-local reduction target corresponding to the
downstream `K23ObstructionConcrete.M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows`
shape, kept here without importing that downstream module.
-/
abbrev BadAdjacencySelectedFiniteLabelFigure9Rows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin) :
    Prop :=
  forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
    BadAdjacencySelectedFiniteLabelFigure9RowAt K i hi (by omega)

/-- A selected finite-label Figure 9 row projects the actual local-label
bad-adjacency incidence row. -/
theorem badAdjacencyLocalLabelIncidenceRowAt_of_selectedFiniteLabelFigure9RowAt
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (H : BadAdjacencySelectedFiniteLabelFigure9RowAt K i hi hi10) :
    BadAdjacencyLocalLabelIncidenceRowAt K i hi hi10 := by
  rcases H with
    ⟨p, qj, r, _hp_qi, _hp_qj, hqi_s, _hqj_r, _hqi_qj,
      _hp_s, _hp_r, _hs_r⟩
  simpa [BadAdjacencySelectedFiniteLabelFigure9RowAt,
    BadAdjacencyLocalLabelIncidenceRowAt] using hqi_s

/-- Conversely, the crossed local-label incidence is the only extra datum
needed to build the selected finite-label Figure 9 row: the other adjacencies
and distinctness clauses are supplied by the generated finite boundary labels
and the Lemma 8/frame-core fields. -/
theorem badAdjacencySelectedFiniteLabelFigure9RowAt_of_localLabelIncidenceRowAt
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (H : BadAdjacencyLocalLabelIncidenceRowAt K i hi hi10) :
    BadAdjacencySelectedFiniteLabelFigure9RowAt K i hi hi10 := by
  let left := badAdjacencyLeftExtraOfNat i hi hi10
  let right := badAdjacencyRightExtraOfNat i hi hi10
  let p := K.spine.rightP left
  let qj := K.spine.centerQ right
  let r := K.lemma8.r right
  refine Exists.intro p (Exists.intro qj (Exists.intro r ?_))
  refine
    And.intro ?hp_qi
      (And.intro ?hp_qj
        (And.intro ?hqi_s
          (And.intro ?hqj_r
            (And.intro ?hqi_qj
              (And.intro ?hp_s
                (And.intro ?hp_r ?hs_r))))))
  · simpa [p, left] using
      GraphBridge.unitDistanceAdj_symm C (K.spine.centerQ_adj_rightP left)
  · have hqj_p :
        GraphBridge.UnitDistanceAdj C qj p := by
      simpa [p, qj, left, right,
        rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight
          (K := K) hi hi10] using
        K.spine.centerQ_adj_leftP right
    exact GraphBridge.unitDistanceAdj_symm C hqj_p
  · exact H
  · simpa [qj, r, right] using K.lemma8.r_neighbor right
  · simpa [qj, left, right] using
      centerQ_badAdjacencyLeft_ne_centerQ_badAdjacencyRight
        (K := K) hi hi10
  · simpa [p, left, right] using
      rightP_badAdjacencyLeft_ne_s_right (K := K) hi hi10
  · simpa [p, r, left, right] using
      rightP_badAdjacencyLeft_ne_r_right (K := K) hi hi10
  · intro hsr
    exact K.lemma8.r_ne_s right hsr.symm

/-- The selected finite-label Figure 9 row is equivalent to the single
crossed local-label incidence; all remaining Figure 9 witness fields are
already available from the generated finite-label certificate. -/
theorem badAdjacencySelectedFiniteLabelFigure9RowAt_iff_localLabelIncidenceRowAt
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    BadAdjacencySelectedFiniteLabelFigure9RowAt K i hi hi10 <->
      BadAdjacencyLocalLabelIncidenceRowAt K i hi hi10 := by
  constructor
  · exact
      badAdjacencyLocalLabelIncidenceRowAt_of_selectedFiniteLabelFigure9RowAt
        (K := K) hi hi10
  · exact
      badAdjacencySelectedFiniteLabelFigure9RowAt_of_localLabelIncidenceRowAt
        (K := K) hi hi10

/-- Row-wise selected finite-label Figure 9 rows project the generated
local-label bad-adjacency incidence rows. -/
def badAdjacencyLocalLabelIncidenceRowsOfSelectedFiniteLabelFigure9Rows
    (H : BadAdjacencySelectedFiniteLabelFigure9Rows K) :
    forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
      BadAdjacencyLocalLabelIncidenceRowAt K i hi (by omega) := by
  intro i hi hi5
  exact
    badAdjacencyLocalLabelIncidenceRowAt_of_selectedFiniteLabelFigure9RowAt
      (K := K) (i := i) hi (by omega) (H i hi hi5)

/-- Row-wise crossed local-label incidences assemble the selected finite-label
Figure 9 rows. -/
def badAdjacencySelectedFiniteLabelFigure9RowsOfLocalLabelIncidenceRows
    (H :
      forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyLocalLabelIncidenceRowAt K i hi (by omega)) :
    BadAdjacencySelectedFiniteLabelFigure9Rows K := by
  intro i hi hi5
  exact
    badAdjacencySelectedFiniteLabelFigure9RowAt_of_localLabelIncidenceRowAt
      (K := K) (i := i) hi (by omega) (H i hi hi5)

/-- Row-wise selected finite-label Figure 9 rows are exactly row-wise crossed
local-label incidences. -/
theorem badAdjacencySelectedFiniteLabelFigure9Rows_iff_localLabelIncidenceRows :
    BadAdjacencySelectedFiniteLabelFigure9Rows K <->
      (forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyLocalLabelIncidenceRowAt K i hi (by omega)) := by
  constructor
  · exact
      badAdjacencyLocalLabelIncidenceRowsOfSelectedFiniteLabelFigure9Rows
        (K := K)
  · exact
      badAdjacencySelectedFiniteLabelFigure9RowsOfLocalLabelIncidenceRows
        (K := K)

/-- Finite-label and assembled-local-label formulations of one
bad-adjacency incidence row are definitionally the same labels. -/
theorem badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    BadAdjacencyFiniteLabelIncidenceRowAt K i hi hi10 <->
      BadAdjacencyLocalLabelIncidenceRowAt K i hi hi10 := by
  rfl

/-- Finite-label crossed incidences assemble the selected finite-label
Figure 9 row; the generated certificate supplies the other Figure 9 fields. -/
theorem badAdjacencySelectedFiniteLabelFigure9RowAt_of_finiteLabelIncidenceRowAt
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (H : BadAdjacencyFiniteLabelIncidenceRowAt K i hi hi10) :
    BadAdjacencySelectedFiniteLabelFigure9RowAt K i hi hi10 :=
  badAdjacencySelectedFiniteLabelFigure9RowAt_of_localLabelIncidenceRowAt
    (K := K) hi hi10
    ((badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
      (K := K) (i := i) hi hi10).1 H)

/-- Row-wise finite-label crossed incidences assemble the selected
finite-label Figure 9 rows. -/
def badAdjacencySelectedFiniteLabelFigure9RowsOfFiniteLabelRowAt
    (H :
      forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyFiniteLabelIncidenceRowAt K i hi (by omega)) :
    BadAdjacencySelectedFiniteLabelFigure9Rows K := by
  intro i hi hi5
  exact
    badAdjacencySelectedFiniteLabelFigure9RowAt_of_finiteLabelIncidenceRowAt
      (K := K) (i := i) hi (by omega) (H i hi hi5)

/-- Finite-label form of the five concrete bad-adjacency incidences:
`Adj q_1 s_2` through `Adj q_5 s_6`. -/
structure BadAdjacencyFiniteLabelIncidenceRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin) :
    Prop where
  adj_q1_s2 :
    BadAdjacencyFiniteLabelIncidenceRowAt K 1 (by omega) (by omega)
  adj_q2_s3 :
    BadAdjacencyFiniteLabelIncidenceRowAt K 2 (by omega) (by omega)
  adj_q3_s4 :
    BadAdjacencyFiniteLabelIncidenceRowAt K 3 (by omega) (by omega)
  adj_q4_s5 :
    BadAdjacencyFiniteLabelIncidenceRowAt K 4 (by omega) (by omega)
  adj_q5_s6 :
    BadAdjacencyFiniteLabelIncidenceRowAt K 5 (by omega) (by omega)

/-- The spine-facing row at `i` is definitionally the finite-label row at
that same start index. -/
theorem badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    BadAdjacencyFiniteLabelIncidenceRowAt K i hi hi10 <->
      (unitDistanceLocalGraph C).Adj
        (K.spine.centerQ (badAdjacencyLeftExtraOfNat i hi hi10))
        (K.lemma8.s (badAdjacencyRightExtraOfNat i hi hi10)) := by
  rfl

/-- A row-wise finite-label incidence family supplies the five named rows. -/
def badAdjacencyFiniteLabelIncidenceRowsOfRowAt
    (h :
      forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyFiniteLabelIncidenceRowAt K i hi (by omega)) :
    BadAdjacencyFiniteLabelIncidenceRows K where
  adj_q1_s2 := h 1 (by omega) (by omega)
  adj_q2_s3 := h 2 (by omega) (by omega)
  adj_q3_s4 := h 3 (by omega) (by omega)
  adj_q4_s5 := h 4 (by omega) (by omega)
  adj_q5_s6 := h 5 (by omega) (by omega)

/-- A generated local-label row-wise incidence family supplies the five
finite-label bad-adjacency rows. -/
def badAdjacencyFiniteLabelIncidenceRowsOfLocalLabelRowAt
    (h :
      forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyLocalLabelIncidenceRowAt K i hi (by omega)) :
    BadAdjacencyFiniteLabelIncidenceRows K where
  adj_q1_s2 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
      (K := K) (i := 1) (by omega) (by omega)).2
      (h 1 (by omega) (by omega))
  adj_q2_s3 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
      (K := K) (i := 2) (by omega) (by omega)).2
      (h 2 (by omega) (by omega))
  adj_q3_s4 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
      (K := K) (i := 3) (by omega) (by omega)).2
      (h 3 (by omega) (by omega))
  adj_q4_s5 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
      (K := K) (i := 4) (by omega) (by omega)).2
      (h 4 (by omega) (by omega))
  adj_q5_s6 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_localLabel
      (K := K) (i := 5) (by omega) (by omega)).2
      (h 5 (by omega) (by omega))

/-- Selected finite-label Figure 9 rows supply the five concrete
finite-label bad-adjacency incidence rows. -/
def badAdjacencyFiniteLabelIncidenceRowsOfSelectedFiniteLabelFigure9Rows
    (H : BadAdjacencySelectedFiniteLabelFigure9Rows K) :
    BadAdjacencyFiniteLabelIncidenceRows K :=
  badAdjacencyFiniteLabelIncidenceRowsOfLocalLabelRowAt (K := K)
    (badAdjacencyLocalLabelIncidenceRowsOfSelectedFiniteLabelFigure9Rows
      (K := K) H)

/-- Convert finite boundary/Lemma 8 label incidences into the route-facing
bad-adjacency incidence rows. -/
def badAdjacencyIncidenceRowsOfFiniteLabelIncidenceRows
    (H : BadAdjacencyFiniteLabelIncidenceRows K) :
    BadAdjacencyIncidenceRows K where
  adj_q1_s2 := by
    exact
      (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
        (K := K) (i := 1) (by omega) (by omega)).1 H.adj_q1_s2
  adj_q2_s3 := by
    exact
      (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
        (K := K) (i := 2) (by omega) (by omega)).1 H.adj_q2_s3
  adj_q3_s4 := by
    exact
      (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
        (K := K) (i := 3) (by omega) (by omega)).1 H.adj_q3_s4
  adj_q4_s5 := by
    exact
      (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
        (K := K) (i := 4) (by omega) (by omega)).1 H.adj_q4_s5
  adj_q5_s6 := by
    exact
      (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
        (K := K) (i := 5) (by omega) (by omega)).1 H.adj_q5_s6

/-- Direct constructor from a row-wise finite boundary/Lemma 8 label
incidence family to the five route-facing bad-adjacency rows. -/
def badAdjacencyIncidenceRowsOfFiniteLabelRowAt
    (h :
      forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyFiniteLabelIncidenceRowAt K i hi (by omega)) :
    BadAdjacencyIncidenceRows K :=
  badAdjacencyIncidenceRowsOfFiniteLabelIncidenceRows (K := K)
    (badAdjacencyFiniteLabelIncidenceRowsOfRowAt (K := K) h)

/-- Selected finite-label Figure 9 rows also supply the route-facing
bad-adjacency incidence rows. -/
def badAdjacencyIncidenceRowsOfSelectedFiniteLabelFigure9Rows
    (H : BadAdjacencySelectedFiniteLabelFigure9Rows K) :
    BadAdjacencyIncidenceRows K :=
  badAdjacencyIncidenceRowsOfFiniteLabelIncidenceRows (K := K)
    (badAdjacencyFiniteLabelIncidenceRowsOfSelectedFiniteLabelFigure9Rows
      (K := K) H)

/-- Forget the route-facing notation back to finite boundary/Lemma 8 label
incidences. -/
def badAdjacencyFiniteLabelIncidenceRowsOfIncidenceRows
    (H : BadAdjacencyIncidenceRows K) :
    BadAdjacencyFiniteLabelIncidenceRows K where
  adj_q1_s2 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
      (K := K) (i := 1) (by omega) (by omega)).2 H.adj_q1_s2
  adj_q2_s3 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
      (K := K) (i := 2) (by omega) (by omega)).2 H.adj_q2_s3
  adj_q3_s4 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
      (K := K) (i := 3) (by omega) (by omega)).2 H.adj_q3_s4
  adj_q4_s5 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
      (K := K) (i := 4) (by omega) (by omega)).2 H.adj_q4_s5
  adj_q5_s6 :=
    (badAdjacencyFiniteLabelIncidenceRowAt_iff_spine
      (K := K) (i := 5) (by omega) (by omega)).2 H.adj_q5_s6

/-- The route-facing bad-adjacency rows are exactly the finite
boundary/Lemma 8 label incidence rows. -/
theorem badAdjacencyIncidenceRows_iff_finiteLabelIncidenceRows :
    BadAdjacencyIncidenceRows K <->
      BadAdjacencyFiniteLabelIncidenceRows K :=
  Iff.intro
    (fun H =>
      badAdjacencyFiniteLabelIncidenceRowsOfIncidenceRows (K := K) H)
    (fun H =>
      badAdjacencyIncidenceRowsOfFiniteLabelIncidenceRows (K := K) H)

/-- Nonempty form of the finite-label constructor for downstream assembly
surfaces that carry row packages as data. -/
theorem badAdjacencyIncidenceRows_nonempty_of_finiteLabelIncidenceRows
    (H : BadAdjacencyFiniteLabelIncidenceRows K) :
    Nonempty (BadAdjacencyIncidenceRows K) :=
  Nonempty.intro
    (badAdjacencyIncidenceRowsOfFiniteLabelIncidenceRows (K := K) H)

/--
Finite label adjacency/distinctness rows that instantiate the Figure 8 raw
distance witness at a selected failed comparison.  The separated partner `j`
is only part of the Figure 8 row interface; the local distance datum is read
from the failed comparison at `i`.
-/
theorem figure8FiniteLabelAdjacencyDistinctnessRows :
    forall {i j : Nat},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i) ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data j) ->
        Exists fun p : Fin n =>
        Exists fun qi : Fin n =>
        Exists fun qj : Fin n =>
        Exists fun s : Fin n =>
        Exists fun r : Fin n =>
          GraphBridge.UnitDistanceAdj C p qi /\
            GraphBridge.UnitDistanceAdj C p qj /\
            GraphBridge.UnitDistanceAdj C qi s /\
            GraphBridge.UnitDistanceAdj C qj r /\
            Ne qi qj /\
            Ne s r := by
  intro i j hi hsep hj hbad_i _hbad_j
  have hi10 : i <= 10 := by omega
  let left := leftExtraOfNat i hi hi10
  let right := rightExtraOfNat i hi hi10
  let p := K.spine.rightP left
  let qi := K.spine.centerQ left
  let qj := K.spine.centerQ right
  let s := K.lemma8.s left
  let r := K.lemma8.r right
  refine
    Exists.intro p
      (Exists.intro qi
        (Exists.intro qj
          (Exists.intro s
            (Exists.intro r ?_))))
  refine ⟨?hp_qi, ?hp_qj, ?hqi_s, ?hqj_r, ?hqi_qj, ?hs_r⟩
  · exact GraphBridge.unitDistanceAdj_symm C (K.spine.centerQ_adj_rightP left)
  · have hcp :
        GraphBridge.UnitDistanceAdj C qj p := by
      simpa [p, qj, rightP_leftExtra_eq_leftP_rightExtra (K := K) hi hi10]
        using K.spine.centerQ_adj_leftP right
    exact GraphBridge.unitDistanceAdj_symm C hcp
  · exact K.lemma8.s_neighbor left
  · exact K.lemma8.r_neighbor right
  · exact centerQ_left_ne_centerQ_right (K := K) hi hi10
  · exact labelFailure_s_ne_right_r (K := K) hi hi10 hbad_i

/--
Finite label adjacency/distinctness rows that instantiate the Figure 9 raw
adjacent-left distance witness at a selected adjacent failed pair.  The
second failed comparison is retained to match the Figure 9 row interface; the
distance datum itself is the local bridge over the first failed comparison.
-/
theorem figure9FiniteLabelAdjacencyDistinctnessRows :
    forall {i : Nat},
      1 <= i -> i + 1 <= 10 ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i) ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data (i + 1)) ->
        Exists fun p : Fin n =>
        Exists fun qi : Fin n =>
        Exists fun qj : Fin n =>
        Exists fun s : Fin n =>
        Exists fun r : Fin n =>
          GraphBridge.UnitDistanceAdj C p qi /\
            GraphBridge.UnitDistanceAdj C p qj /\
            GraphBridge.UnitDistanceAdj C qi s /\
            GraphBridge.UnitDistanceAdj C qj r /\
            Ne qi qj /\
            Ne p s /\
            Ne p r /\
            Ne s r := by
  intro i hi hi_next hbad_i _hbad_next
  have hi10 : i <= 10 := by omega
  let left := leftExtraOfNat i hi hi10
  let right := rightExtraOfNat i hi hi10
  let p := K.spine.rightP left
  let qi := K.spine.centerQ left
  let qj := K.spine.centerQ right
  let s := K.lemma8.s left
  let r := K.lemma8.r right
  refine
    Exists.intro p
      (Exists.intro qi
        (Exists.intro qj
          (Exists.intro s
            (Exists.intro r ?_))))
  refine
    ⟨?hp_qi, ?hp_qj, ?hqi_s, ?hqj_r, ?hqi_qj, ?hp_s,
      ?hp_r, ?hs_r⟩
  · exact GraphBridge.unitDistanceAdj_symm C (K.spine.centerQ_adj_rightP left)
  · have hcp :
        GraphBridge.UnitDistanceAdj C qj p := by
      simpa [p, qj, rightP_leftExtra_eq_leftP_rightExtra (K := K) hi hi10]
        using K.spine.centerQ_adj_leftP right
    exact GraphBridge.unitDistanceAdj_symm C hcp
  · exact K.lemma8.s_neighbor left
  · exact K.lemma8.r_neighbor right
  · exact centerQ_left_ne_centerQ_right (K := K) hi hi10
  · exact rightP_ne_left_s (K := K) hi hi10
  · exact rightP_ne_right_r (K := K) hi hi10
  · exact labelFailure_s_ne_right_r (K := K) hi hi10 hbad_i

/-- Point-valued Figure 8 distance rows obtained from the finite selected
labels by the `AngleBridgeFacts.Figure8DistanceData.ofUDConfigAdj`
constructor. -/
theorem figure8DistanceWitnessRows :
    forall {i j : Nat},
      1 <= i -> i + 1 < j -> j <= 10 ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i) ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data j) ->
        Exists fun p : AngleBridgeFacts.Point =>
        Exists fun qi : AngleBridgeFacts.Point =>
        Exists fun qj : AngleBridgeFacts.Point =>
        Exists fun s : AngleBridgeFacts.Point =>
        Exists fun r : AngleBridgeFacts.Point =>
          AngleBridgeFacts.Figure8DistanceData p qi qj s r := by
  intro i j hi hsep hj hbad_i hbad_j
  rcases K.figure8FiniteLabelAdjacencyDistinctnessRows
      hi hsep hj hbad_i hbad_j with
    ⟨p, qi, qj, s, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hs_r⟩
  exact
    Exists.intro (C.pts p)
      (Exists.intro (C.pts qi)
        (Exists.intro (C.pts qj)
          (Exists.intro (C.pts s)
            (Exists.intro (C.pts r)
              (AngleBridgeFacts.Figure8DistanceData.ofUDConfigAdj C
                hp_qi hp_qj hqi_s hqj_r hqi_qj hs_r)))))

/-- Point-valued Figure 9 distance rows obtained from the finite selected
labels by the `AngleBridgeFacts.Figure9DistanceData.ofUDConfigAdj`
constructor. -/
theorem figure9DistanceWitnessRows :
    forall {i : Nat},
      1 <= i -> i + 1 <= 10 ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i) ->
      Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data (i + 1)) ->
        Exists fun p : AngleBridgeFacts.Point =>
        Exists fun qi : AngleBridgeFacts.Point =>
        Exists fun qj : AngleBridgeFacts.Point =>
        Exists fun s : AngleBridgeFacts.Point =>
        Exists fun r : AngleBridgeFacts.Point =>
          AngleBridgeFacts.Figure9DistanceData p qi qj s r := by
  intro i hi hi_next hbad_i hbad_next
  rcases K.figure9FiniteLabelAdjacencyDistinctnessRows
      hi hi_next hbad_i hbad_next with
    ⟨p, qi, qj, s, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s,
      hp_r, hs_r⟩
  exact
    Exists.intro (C.pts p)
      (Exists.intro (C.pts qi)
        (Exists.intro (C.pts qj)
          (Exists.intro (C.pts s)
            (Exists.intro (C.pts r)
              (AngleBridgeFacts.Figure9DistanceData.ofUDConfigAdj C
                hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r)))))

/-! ### Minimal S5 angle rows -/

/--
The finite frame-core label certificate supplies the selected labels,
adjacencies, distinctness, and cyclic-order bookkeeping.  It does not by
itself contain the quantitative turn-angle inequalities needed by S5, so this
minimal source row names exactly those two missing angle facts.
-/
structure S5AngleRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop where
  figure8CentralAngleLeSeparatedTurn :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn
  figure9LeftAngleLeMiddleTurn :
    Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn

/-- Finite-label Figure 8 turn-subwindow source for the remaining S5
central-angle row. -/
abbrev Figure8CentralAngleTurnSubwindowRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnSubwindowRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 8 exact turn-subwindow source for the remaining S5
central-angle row. -/
abbrev Figure8CentralAngleTurnSubwindowEqRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnSubwindowEqRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 8 interval-subwindow source for the remaining S5
central-angle row. -/
abbrev Figure8CentralAngleTurnIccSubwindowRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnIccSubwindowRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 8 exact interval-subwindow source for the remaining S5
central-angle row. -/
abbrev Figure8CentralAngleTurnIccSubwindowEqRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnIccSubwindowEqRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 8 indexed finite-subwindow source for the remaining S5
central-angle row. -/
abbrev Figure8CentralAngleTurnIndexedSubwindowRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnIndexedSubwindowRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 8 exact indexed finite-subwindow source for the
remaining S5 central-angle row. -/
abbrev Figure8CentralAngleTurnIndexedSubwindowEqRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnIndexedSubwindowEqRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 9 cosine-turn source for the remaining S5 middle-turn
upper-bound row. -/
abbrev Figure9AdjacentLeftCosineTurnRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure9EuclideanFactsConcrete.Figure9AdjacentLeftCosineTurnRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 9 chord-turn source for the remaining S5 middle-turn
upper-bound row. -/
abbrev Figure9AdjacentLeftTurnChordRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  Figure9EuclideanFactsConcrete.Figure9AdjacentLeftTurnChordRows
    (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
    turnBounds.turn

/-- Finite-label Figure 9 pointwise cosine comparisons.  The ambient
`M8TurnBounds` supply the missing `[0, pi]` middle-turn range. -/
abbrev Figure9AdjacentLeftCosineComparisonRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    1 <= i -> i + 1 <= 10 ->
    Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i) ->
    Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data (i + 1)) ->
    AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
      Real.cos (turnBounds.turn (i + 1)) <=
        TriangleAngleFacts.dotAt p qi s

/-- Finite-label Figure 9 pointwise chord comparisons.  The ambient
`M8TurnBounds` supply the missing `[0, pi]` middle-turn range. -/
abbrev Figure9AdjacentLeftTurnChordComparisonRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop :=
  forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
    1 <= i -> i + 1 <= 10 ->
    Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data i) ->
    Not (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data (i + 1)) ->
    AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
      TriangleAngleFacts.sqDist p s <=
        2 - 2 * Real.cos (turnBounds.turn (i + 1))

namespace S5AngleRows

variable {K :
  M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin}
variable {turnBounds : M8TurnBounds}

/-- The weaker Figure 9 middle-turn upper-bound row supplies the actual
left-angle containment row after using turn nonnegativity. -/
def figure9LeftAngleContainmentRows
    (H : S5AngleRows K turnBounds) :
    Figure9ContainmentConcrete.Figure9AdjacentLeftAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure9ContainmentConcrete.leftAngleContainmentRows_of_angleLeMiddleTurnRows
    turnBounds.turn_nonnegative H.figure9LeftAngleLeMiddleTurn

/-- The finite label certificate supplies both distance rows; the S5 angle
package supplies the Figure 8 central-angle row and the Figure 9 middle-turn
upper-bound row, which is converted here to the left-angle containment row
used by the atomic S5 finite-`p_i/q_i` route. -/
theorem distance_and_angle_rows
    (H : S5AngleRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data) /\
      Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn /\
      Figure9ContainmentConcrete.Figure9AdjacentLeftDistanceWitnessRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data) /\
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleContainmentRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn :=
  And.intro K.figure8DistanceWitnessRows
    (And.intro H.figure8CentralAngleLeSeparatedTurn
      (And.intro K.figure9DistanceWitnessRows
        H.figure9LeftAngleContainmentRows))

/-- Figure 8 turn-subwindow rows reduce to the central-angle row stored in
`S5AngleRows`. -/
def figure8CentralAngleLeSeparatedTurn_of_turnSubwindowRows
    (H : Figure8CentralAngleTurnSubwindowRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_m8TurnBounds_turnSubwindowRows
    turnBounds H

/-- Exact Figure 8 turn-subwindow rows reduce to the central-angle row stored
in `S5AngleRows`. -/
def figure8CentralAngleLeSeparatedTurn_of_turnSubwindowEqRows
    (H : Figure8CentralAngleTurnSubwindowEqRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_m8TurnBounds_turnSubwindowEqRows
    turnBounds H

/-- Interval Figure 8 turn-subwindow rows reduce to the central-angle row
stored in `S5AngleRows`. -/
def figure8CentralAngleLeSeparatedTurn_of_turnIccSubwindowRows
    (H : Figure8CentralAngleTurnIccSubwindowRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_turnSubwindowIccRows
    turnBounds.turn_nonnegative H

/-- Exact interval Figure 8 turn-subwindow rows reduce to the central-angle
row stored in `S5AngleRows`. -/
def figure8CentralAngleLeSeparatedTurn_of_turnIccSubwindowEqRows
    (H : Figure8CentralAngleTurnIccSubwindowEqRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_turnSubwindowIccEqRows
    turnBounds.turn_nonnegative H

/-- Indexed Figure 8 turn-subwindow rows reduce to the central-angle row
stored in `S5AngleRows`. -/
def figure8CentralAngleLeSeparatedTurn_of_turnIndexedSubwindowRows
    (H : Figure8CentralAngleTurnIndexedSubwindowRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_indexedSubwindowRows
    turnBounds.turn_nonnegative H

/-- Exact indexed Figure 8 turn-subwindow rows reduce to the central-angle row
stored in `S5AngleRows`. -/
def figure8CentralAngleLeSeparatedTurn_of_turnIndexedSubwindowEqRows
    (H : Figure8CentralAngleTurnIndexedSubwindowEqRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_indexedSubwindowEqRows
    turnBounds.turn_nonnegative H

/-- Figure 9 cosine-turn rows reduce to the middle-turn upper-bound row stored
in `S5AngleRows`. -/
def figure9LeftAngleLeMiddleTurn_of_cosineTurnRows
    (H : Figure9AdjacentLeftCosineTurnRows K turnBounds) :
    Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure9EuclideanFactsConcrete.angleLeMiddleTurnRows_of_cosineTurnRows H

/-- Figure 9 chord-turn rows reduce to the middle-turn upper-bound row stored
in `S5AngleRows`. -/
def figure9LeftAngleLeMiddleTurn_of_turnChordRows
    (H : Figure9AdjacentLeftTurnChordRows K turnBounds) :
    Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure9EuclideanFactsConcrete.angleLeMiddleTurnRows_of_turnChordRows H

/-- Pointwise Figure 9 cosine comparisons reduce to cosine-turn rows using
the finite-label turn bounds. -/
def figure9CosineTurnRows_of_totalTurn_and_cosineComparisons
    (H : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    Figure9AdjacentLeftCosineTurnRows K turnBounds :=
  Figure9EuclideanFactsConcrete.cosineTurnRows_of_totalTurn_and_cosineComparisons
    turnBounds.turn_nonnegative turnBounds.total_turn_lt_pi_div_three H

/-- Pointwise Figure 9 chord comparisons reduce to chord-turn rows using the
finite-label turn bounds. -/
def figure9TurnChordRows_of_totalTurn_and_chordComparisons
    (H : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    Figure9AdjacentLeftTurnChordRows K turnBounds :=
  Figure9EuclideanFactsConcrete.turnChordRows_of_totalTurn_and_chordComparisons
    turnBounds.turn_nonnegative turnBounds.total_turn_lt_pi_div_three H

/-- Build the finite-label S5 angle package once the two reduced angle rows are
available. -/
def ofAngleRows
    (H8 :
      Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn)
    (H9 :
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    S5AngleRows K turnBounds where
  figure8CentralAngleLeSeparatedTurn := H8
  figure9LeftAngleLeMiddleTurn := H9

/-- Build finite-label `S5AngleRows` from Figure 8 subwindow rows and Figure 9
cosine-turn rows. -/
def ofTurnSubwindowRowsAndCosineTurnRows
    (H8 : Figure8CentralAngleTurnSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineTurnRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnSubwindowRows H8)
    (figure9LeftAngleLeMiddleTurn_of_cosineTurnRows H9)

/-- Build finite-label `S5AngleRows` from Figure 8 subwindow rows and Figure 9
chord-turn rows. -/
def ofTurnSubwindowRowsAndTurnChordRows
    (H8 : Figure8CentralAngleTurnSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnSubwindowRows H8)
    (figure9LeftAngleLeMiddleTurn_of_turnChordRows H9)

/-- Build finite-label `S5AngleRows` from exact Figure 8 subwindow rows and
Figure 9 cosine-turn rows. -/
def ofTurnSubwindowEqRowsAndCosineTurnRows
    (H8 : Figure8CentralAngleTurnSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineTurnRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnSubwindowEqRows H8)
    (figure9LeftAngleLeMiddleTurn_of_cosineTurnRows H9)

/-- Build finite-label `S5AngleRows` from exact Figure 8 subwindow rows and
Figure 9 chord-turn rows. -/
def ofTurnSubwindowEqRowsAndTurnChordRows
    (H8 : Figure8CentralAngleTurnSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnSubwindowEqRows H8)
    (figure9LeftAngleLeMiddleTurn_of_turnChordRows H9)

/-- Build finite-label `S5AngleRows` from Figure 8 subwindow rows and
pointwise Figure 9 cosine comparisons. -/
def ofTurnSubwindowRowsAndCosineComparisonRows
    (H8 : Figure8CentralAngleTurnSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofTurnSubwindowRowsAndCosineTurnRows H8
    (figure9CosineTurnRows_of_totalTurn_and_cosineComparisons H9)

/-- Build finite-label `S5AngleRows` from Figure 8 subwindow rows and
pointwise Figure 9 chord comparisons. -/
def ofTurnSubwindowRowsAndTurnChordComparisonRows
    (H8 : Figure8CentralAngleTurnSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofTurnSubwindowRowsAndTurnChordRows H8
    (figure9TurnChordRows_of_totalTurn_and_chordComparisons H9)

/-- Build finite-label `S5AngleRows` from exact Figure 8 subwindow rows and
pointwise Figure 9 cosine comparisons. -/
def ofTurnSubwindowEqRowsAndCosineComparisonRows
    (H8 : Figure8CentralAngleTurnSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofTurnSubwindowEqRowsAndCosineTurnRows H8
    (figure9CosineTurnRows_of_totalTurn_and_cosineComparisons H9)

/-- Build finite-label `S5AngleRows` from exact Figure 8 subwindow rows and
pointwise Figure 9 chord comparisons. -/
def ofTurnSubwindowEqRowsAndTurnChordComparisonRows
    (H8 : Figure8CentralAngleTurnSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofTurnSubwindowEqRowsAndTurnChordRows H8
    (figure9TurnChordRows_of_totalTurn_and_chordComparisons H9)

/-- Build finite-label `S5AngleRows` from Figure 8 interval-subwindow rows
and pointwise Figure 9 cosine comparisons. -/
def ofTurnIccSubwindowRowsAndCosineComparisonRows
    (H8 : Figure8CentralAngleTurnIccSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIccSubwindowRows H8)
    (figure9LeftAngleLeMiddleTurn_of_cosineTurnRows
      (figure9CosineTurnRows_of_totalTurn_and_cosineComparisons H9))

/-- Build finite-label `S5AngleRows` from Figure 8 interval-subwindow rows
and pointwise Figure 9 turn-chord comparisons. -/
def ofTurnIccSubwindowRowsAndTurnChordComparisonRows
    (H8 : Figure8CentralAngleTurnIccSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIccSubwindowRows H8)
    (figure9LeftAngleLeMiddleTurn_of_turnChordRows
      (figure9TurnChordRows_of_totalTurn_and_chordComparisons H9))

/-- Build finite-label `S5AngleRows` from exact Figure 8 interval-telescope
rows and pointwise Figure 9 cosine comparisons. -/
def ofTurnIccSubwindowEqRowsAndCosineComparisonRows
    (H8 : Figure8CentralAngleTurnIccSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIccSubwindowEqRows H8)
    (figure9LeftAngleLeMiddleTurn_of_cosineTurnRows
      (figure9CosineTurnRows_of_totalTurn_and_cosineComparisons H9))

/-- Build finite-label `S5AngleRows` from exact Figure 8 interval-telescope
rows and pointwise Figure 9 turn-chord comparisons. -/
def ofTurnIccSubwindowEqRowsAndTurnChordComparisonRows
    (H8 : Figure8CentralAngleTurnIccSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIccSubwindowEqRows H8)
    (figure9LeftAngleLeMiddleTurn_of_turnChordRows
      (figure9TurnChordRows_of_totalTurn_and_chordComparisons H9))

/-- Build finite-label `S5AngleRows` from Figure 8 indexed finite-subwindow
rows and pointwise Figure 9 cosine comparisons. -/
def ofTurnIndexedSubwindowRowsAndCosineComparisonRows
    (H8 : Figure8CentralAngleTurnIndexedSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIndexedSubwindowRows H8)
    (figure9LeftAngleLeMiddleTurn_of_cosineTurnRows
      (figure9CosineTurnRows_of_totalTurn_and_cosineComparisons H9))

/-- Build finite-label `S5AngleRows` from Figure 8 indexed finite-subwindow
rows and pointwise Figure 9 turn-chord comparisons. -/
def ofTurnIndexedSubwindowRowsAndTurnChordComparisonRows
    (H8 : Figure8CentralAngleTurnIndexedSubwindowRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIndexedSubwindowRows H8)
    (figure9LeftAngleLeMiddleTurn_of_turnChordRows
      (figure9TurnChordRows_of_totalTurn_and_chordComparisons H9))

/-- Build finite-label `S5AngleRows` from exact Figure 8 indexed finite
telescope rows and pointwise Figure 9 cosine comparisons. -/
def ofTurnIndexedSubwindowEqRowsAndCosineComparisonRows
    (H8 : Figure8CentralAngleTurnIndexedSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftCosineComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIndexedSubwindowEqRows H8)
    (figure9LeftAngleLeMiddleTurn_of_cosineTurnRows
      (figure9CosineTurnRows_of_totalTurn_and_cosineComparisons H9))

/-- Build finite-label `S5AngleRows` from exact Figure 8 indexed finite
telescope rows and pointwise Figure 9 turn-chord comparisons. -/
def ofTurnIndexedSubwindowEqRowsAndTurnChordComparisonRows
    (H8 : Figure8CentralAngleTurnIndexedSubwindowEqRows K turnBounds)
    (H9 : Figure9AdjacentLeftTurnChordComparisonRows K turnBounds) :
    S5AngleRows K turnBounds :=
  ofAngleRows
    (figure8CentralAngleLeSeparatedTurn_of_turnIndexedSubwindowEqRows H8)
    (figure9LeftAngleLeMiddleTurn_of_turnChordRows
      (figure9TurnChordRows_of_totalTurn_and_chordComparisons H9))

end S5AngleRows

/--
Certificate-side S5 source rows: the finite frame-core label certificate
supplies the point-valued Figure 8/Figure 9 distance witnesses, while the
two angle fields are exactly the remaining per-label inequalities required by
the finite-`p_i/q_i` S5 route.
-/
structure S5FiniteLabelAngleRows
    (K :
      M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin)
    (turnBounds : M8TurnBounds) : Prop where
  figure8DistanceWitnessRows :
    Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
  figure8CentralAngleLeSeparatedTurn :
    Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn
  figure9DistanceWitnessRows :
    Figure9ContainmentConcrete.Figure9AdjacentLeftDistanceWitnessRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
  figure9LeftAngleLeMiddleTurn :
    Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn

namespace S5FiniteLabelAngleRows

variable {K :
  M8FiniteBoundaryFrameCoreLabelCertificate D connectedNoCut hmin}
variable {turnBounds : M8TurnBounds}

/-- The finite label certificate plus explicit S5 angle rows give the compact
four-row source package; the angle inequalities remain supplied, not
constructed, here. -/
def ofS5AngleRows
    (H : S5AngleRows K turnBounds) :
    S5FiniteLabelAngleRows K turnBounds where
  figure8DistanceWitnessRows := K.figure8DistanceWitnessRows
  figure8CentralAngleLeSeparatedTurn := H.figure8CentralAngleLeSeparatedTurn
  figure9DistanceWitnessRows := K.figure9DistanceWitnessRows
  figure9LeftAngleLeMiddleTurn := H.figure9LeftAngleLeMiddleTurn

/-- Project exactly the two quantitative S5 angle rows from the compact
finite-label source package. -/
def toS5AngleRows
    (H : S5FiniteLabelAngleRows K turnBounds) :
    S5AngleRows K turnBounds where
  figure8CentralAngleLeSeparatedTurn :=
    H.figure8CentralAngleLeSeparatedTurn
  figure9LeftAngleLeMiddleTurn :=
    H.figure9LeftAngleLeMiddleTurn

/-- The compact package supplies the actual Figure 9 left-angle containment
row after applying turn nonnegativity to its middle-turn upper bounds. -/
def figure9LeftAngleContainmentRows
    (H : S5FiniteLabelAngleRows K turnBounds) :
    Figure9ContainmentConcrete.Figure9AdjacentLeftAngleContainmentRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  H.toS5AngleRows.figure9LeftAngleContainmentRows

/-- Build the compact finite-label S5 package from the four explicit local
rows: the two distance rows, the Figure 8 central-angle containment row, and
the Figure 9 middle-turn upper-bound row. -/
def ofDistanceAndAngleRows
    (H8D :
      Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data))
    (H8A :
      Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn)
    (H9D :
      Figure9ContainmentConcrete.Figure9AdjacentLeftDistanceWitnessRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data))
    (H9M :
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn) :
    S5FiniteLabelAngleRows K turnBounds where
  figure8DistanceWitnessRows := H8D
  figure8CentralAngleLeSeparatedTurn := H8A
  figure9DistanceWitnessRows := H9D
  figure9LeftAngleLeMiddleTurn := H9M

/-- Project the atomic row bundle consumed by the finite-`p_i/q_i` S5
constructor.  The stored Figure 9 middle-turn rows are converted to the
left-angle containment rows using turn nonnegativity. -/
theorem distance_and_angle_rows
    (H : S5FiniteLabelAngleRows K turnBounds) :
    Figure8ContainmentConcrete.Figure8SeparatedDistanceWitnessRows
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data) /\
      Figure8ContainmentConcrete.Figure8SeparatedCentralAngleContainmentRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn /\
      Figure9ContainmentConcrete.Figure9AdjacentLeftDistanceWitnessRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data) /\
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleContainmentRows
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn :=
  And.intro H.figure8DistanceWitnessRows
    (And.intro H.figure8CentralAngleLeSeparatedTurn
      (And.intro H.figure9DistanceWitnessRows
        H.figure9LeftAngleContainmentRows))

end S5FiniteLabelAngleRows

/-- Existing finite-label Figure 8 distance rows plus the named central-angle
row rebuild the Figure 8 containment interface. -/
def figure8ContainmentInterfaceOfS5AngleRows
    (turnBounds : M8TurnBounds)
    (H : S5AngleRows K turnBounds) :
    AngleContainmentInterface.Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8ContainmentConcrete.containmentInterface_of_distanceWitnessRowsAndCentralAngleContainment
    K.figure8DistanceWitnessRows
    H.figure8CentralAngleLeSeparatedTurn

/-- Existing finite-label Figure 9 distance rows plus the weaker middle-turn
upper-bound row rebuild the Figure 9 containment interface. -/
def figure9ContainmentInterfaceOfS5AngleRows
    (turnBounds : M8TurnBounds)
    (H : S5AngleRows K turnBounds) :
    AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure9ContainmentConcrete.containmentInterface_of_distanceWitnessRowsAndLeftAngleContainment
    K.figure9DistanceWitnessRows
    H.figure9LeftAngleContainmentRows

/-- The finite frame-core label certificate feeds the local angle-containment
bridge package once the two genuinely metric angle rows are
supplied. -/
def angleContainmentBridgesOfS5AngleRows
    (turnBounds : M8TurnBounds)
    (H : S5AngleRows K turnBounds) :
    AngleContainmentInterface.AngleContainmentBridges
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  { figure8 := K.figure8ContainmentInterfaceOfS5AngleRows turnBounds H
    figure9 := K.figure9ContainmentInterfaceOfS5AngleRows turnBounds H }

/-- Nonempty form of the finite-label S5 constructor. -/
theorem angleContainmentBridges_nonempty_of_s5AngleRows
    (turnBounds : M8TurnBounds)
    (H : S5AngleRows K turnBounds) :
    Nonempty
      (AngleContainmentInterface.AngleContainmentBridges
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn) :=
  Nonempty.intro
    (K.angleContainmentBridgesOfS5AngleRows turnBounds H)

/-- The compact finite-label S5 source package rebuilds the Figure 8
containment interface using its explicit distance and central-angle rows. -/
def figure8ContainmentInterfaceOfS5FiniteLabelAngleRows
    (turnBounds : M8TurnBounds)
    (H : S5FiniteLabelAngleRows K turnBounds) :
    AngleContainmentInterface.Figure8SeparatedContainmentInterface
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure8ContainmentConcrete.containmentInterface_of_distanceWitnessRowsAndCentralAngleContainment
    H.figure8DistanceWitnessRows
    H.figure8CentralAngleLeSeparatedTurn

/-- The compact finite-label S5 source package rebuilds the Figure 9
containment interface using its explicit distance rows and middle-turn upper
bound rows. -/
def figure9ContainmentInterfaceOfS5FiniteLabelAngleRows
    (turnBounds : M8TurnBounds)
    (H : S5FiniteLabelAngleRows K turnBounds) :
    AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  Figure9ContainmentConcrete.containmentInterface_of_distanceWitnessRowsAndLeftAngleContainment
    H.figure9DistanceWitnessRows
    H.figure9LeftAngleContainmentRows

/-- Compact bridge constructor from a finite frame-core label certificate plus
the two genuine S5 angle rows. -/
def angleContainmentBridgesOfS5FiniteLabelAngleRows
    (turnBounds : M8TurnBounds)
    (H : S5FiniteLabelAngleRows K turnBounds) :
    AngleContainmentInterface.AngleContainmentBridges
      (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
      turnBounds.turn :=
  { figure8 := K.figure8ContainmentInterfaceOfS5FiniteLabelAngleRows
      turnBounds H
    figure9 := K.figure9ContainmentInterfaceOfS5FiniteLabelAngleRows
      turnBounds H }

/-- Nonempty form of the compact finite-label S5 constructor. -/
theorem angleContainmentBridges_nonempty_of_s5FiniteLabelAngleRows
    (turnBounds : M8TurnBounds)
    (H : S5FiniteLabelAngleRows K turnBounds) :
    Nonempty
      (AngleContainmentInterface.AngleContainmentBridges
        (M8BrokenLatticeGood K.toM8LocalLabels.predicates.data)
        turnBounds.turn) :=
  Nonempty.intro
    (K.angleContainmentBridgesOfS5FiniteLabelAngleRows turnBounds H)

@[simp]
theorem toFiniteBoundaryLabelCertificate_finiteLabels :
    K.toFiniteBoundaryLabelCertificate.finiteLabels = K.finiteLabels :=
  rfl

@[simp]
theorem toFiniteBoundaryLabelCertificate_lemma8 :
    K.toFiniteBoundaryLabelCertificate.lemma8 = K.lemma8 :=
  rfl

@[simp]
theorem spine_eq :
    K.spine =
      K.finiteLabels.toM8BoundarySpine connectedNoCut hmin :=
  rfl

end M8FiniteBoundaryFrameCoreLabelCertificate

/-! ## Direct finite-label entry point -/

/-- Direct constructor route from finite `p/q` labels, the finite frame-core
fields for that same generated spine, and Lemma 8 combinatorics. -/
def ofFiniteFrameCoreLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields finiteLabels connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    M8FiniteBoundaryFrameCoreLabelCertificate
      D connectedNoCut hmin where
  finiteLabels := finiteLabels
  frameCoreFields := frameCoreFields
  lemma8 := lemma8

@[simp]
theorem ofFiniteFrameCoreLabels_finiteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields finiteLabels connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (ofFiniteFrameCoreLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels frameCoreFields lemma8).finiteLabels =
        finiteLabels :=
  rfl

@[simp]
theorem ofFiniteFrameCoreLabels_frameCoreFields
    (finiteLabels : M8FinitePQSpineCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields finiteLabels connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (ofFiniteFrameCoreLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels frameCoreFields lemma8).frameCoreFields =
        frameCoreFields :=
  rfl

@[simp]
theorem ofFiniteFrameCoreLabels_lemma8
    (finiteLabels : M8FinitePQSpineCertificate D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields finiteLabels connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (ofFiniteFrameCoreLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels frameCoreFields lemma8).lemma8 =
        lemma8 :=
  rfl

/--
Direct constructor route from an explicit finite `p/q` spine certificate and
an explicit Lemma 8 package to the boundary-label assembly certificate.
-/
def ofFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    M8FiniteBoundaryLabelCertificate D connectedNoCut hmin where
  finiteLabels := finiteLabels
  lemma8 := lemma8

@[simp]
theorem ofFiniteLabels_finiteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (ofFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).finiteLabels =
        finiteLabels :=
  rfl

@[simp]
theorem ofFiniteLabels_lemma8
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (ofFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).lemma8 =
        lemma8 :=
  rfl

/-! ## Honest boundary-core and boundary-walk row entry points -/

/-- Honest boundary-core `p/q` spine rows feed the existing finite
boundary-label certificate route directly. -/
def ofCorePQSpineRows
    (rows : M8BoundaryCorePQSpineRows D)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8FiniteBoundaryLabelCertificate D connectedNoCut hmin :=
  ofFiniteLabels rows.toFinitePQSpineCertificate lemma8

@[simp]
theorem ofCorePQSpineRows_finiteLabels
    (rows : M8BoundaryCorePQSpineRows D)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofCorePQSpineRows (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows lemma8).finiteLabels =
        rows.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem ofCorePQSpineRows_lemma8
    (rows : M8BoundaryCorePQSpineRows D)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofCorePQSpineRows (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows lemma8).lemma8 =
        lemma8 :=
  rfl

/-- Honest boundary-core rows plus finite frame-core fields feed the
frame-aware label certificate route. -/
def ofCorePQSpineFrameRows
    (rows : M8BoundaryCorePQSpineRows D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8FiniteBoundaryFrameCoreLabelCertificate
      D connectedNoCut hmin :=
  ofFiniteFrameCoreLabels
    rows.toFinitePQSpineCertificate frameCoreFields lemma8

@[simp]
theorem ofCorePQSpineFrameRows_finiteLabels
    (rows : M8BoundaryCorePQSpineRows D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofCorePQSpineFrameRows (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows frameCoreFields lemma8).finiteLabels =
        rows.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem ofCorePQSpineFrameRows_frameCoreFields
    (rows : M8BoundaryCorePQSpineRows D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofCorePQSpineFrameRows (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows frameCoreFields lemma8).frameCoreFields =
        frameCoreFields :=
  rfl

@[simp]
theorem ofCorePQSpineFrameRows_lemma8
    (rows : M8BoundaryCorePQSpineRows D)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofCorePQSpineFrameRows (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows frameCoreFields lemma8).lemma8 =
        lemma8 :=
  rfl

section BoundaryWalkRows

variable {P : OuterBoundaryCore (CanonicalUDGraph C)}
variable {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {walk :
  OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
    IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
    (CanonicalUDGraph C)}

/-- Boundary-walk `p/q` spine rows feed the existing finite boundary-label
certificate route through their generated planar-boundary data. -/
def ofWalkPQSpineRows
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8FiniteBoundaryLabelCertificate
      rows.toPlanarBoundaryData connectedNoCut hmin :=
  ofFiniteLabels rows.toFinitePQSpineCertificate lemma8

@[simp]
theorem ofWalkPQSpineRows_finiteLabels
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofWalkPQSpineRows (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows lemma8).finiteLabels =
        rows.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem ofWalkPQSpineRows_lemma8
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofWalkPQSpineRows (connectedNoCut := connectedNoCut) (hmin := hmin)
      rows lemma8).lemma8 =
        lemma8 :=
  rfl

/-- Boundary-walk rows plus finite frame-core fields feed the frame-aware
label certificate route. -/
def ofWalkPQSpineFrameRows
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8FiniteBoundaryFrameCoreLabelCertificate
      rows.toPlanarBoundaryData connectedNoCut hmin :=
  ofFiniteFrameCoreLabels
    rows.toFinitePQSpineCertificate frameCoreFields lemma8

@[simp]
theorem ofWalkPQSpineFrameRows_finiteLabels
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofWalkPQSpineFrameRows (connectedNoCut := connectedNoCut)
      (hmin := hmin) rows frameCoreFields lemma8).finiteLabels =
        rows.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem ofWalkPQSpineFrameRows_frameCoreFields
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofWalkPQSpineFrameRows (connectedNoCut := connectedNoCut)
      (hmin := hmin) rows frameCoreFields lemma8).frameCoreFields =
        frameCoreFields :=
  rfl

@[simp]
theorem ofWalkPQSpineFrameRows_lemma8
    (rows :
      M8BoundaryWalkPQSpineRows walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (frameCoreFields :
      M8FinitePQSpineFrameCoreFields
        rows.toFinitePQSpineCertificate connectedNoCut hmin)
    (lemma8 :
      M8Lemma8Combinatorics
        (rows.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (ofWalkPQSpineFrameRows (connectedNoCut := connectedNoCut)
      (hmin := hmin) rows frameCoreFields lemma8).lemma8 =
        lemma8 :=
  rfl

end BoundaryWalkRows

/-- Direct route to the checked boundary-route package from finite labels. -/
def toM8BoundaryRouteDataOfFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    M8BoundaryRouteData.{u} C hmin :=
  (ofFiniteLabels (D := D)
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    finiteLabels lemma8).toM8BoundaryRouteData

/-- Direct route to the concrete boundary-label package from finite labels. -/
def toBoundaryLabelPackageOfFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    M8BoundaryLabelPackage C :=
  (ofFiniteLabels (D := D)
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    finiteLabels lemma8).toBoundaryLabelPackage

/-- Direct local-label package extracted from finite boundary labels and the
explicit Lemma 8 package. -/
def toM8LocalLabelsOfFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    M8LocalLabels C :=
  (ofFiniteLabels (D := D)
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    finiteLabels lemma8).toM8LocalLabels

@[simp]
theorem toM8BoundaryRouteDataOfFiniteLabels_spine
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (toM8BoundaryRouteDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).spine =
        finiteLabels.toM8BoundarySpine connectedNoCut hmin :=
  rfl

@[simp]
theorem toBoundaryLabelPackageOfFiniteLabels_context
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (toBoundaryLabelPackageOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).context =
        finiteLabels.context connectedNoCut hmin :=
  rfl

@[simp]
theorem toBoundaryLabelPackageOfFiniteLabels_spine
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (toBoundaryLabelPackageOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).spine =
        finiteLabels.toM8BoundarySpine connectedNoCut hmin :=
  rfl

@[simp]
theorem toBoundaryLabelPackageOfFiniteLabels_lemma8
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin)) :
    (toBoundaryLabelPackageOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).lemma8 =
        lemma8 :=
  rfl

@[simp]
theorem toM8LocalLabelsOfFiniteLabels_p
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (toM8LocalLabelsOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).labels.p i =
        finiteLabels.p i :=
  rfl

@[simp]
theorem toM8LocalLabelsOfFiniteLabels_q
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (toM8LocalLabelsOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).labels.q i =
        finiteLabels.q i :=
  rfl

@[simp]
theorem toM8LocalLabelsOfFiniteLabels_r
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (toM8LocalLabelsOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).labels.r i =
        lemma8.r i :=
  rfl

@[simp]
theorem toM8LocalLabelsOfFiniteLabels_s
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (i : M8ExtraIndex) :
    (toM8LocalLabelsOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8).labels.s i =
        lemma8.s i :=
  rfl

/-- Direct route to `M8ConstructionData` from finite labels and all remaining
currently explicit M8 certificates. -/
def toM8ConstructionDataOfFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    M8ConstructionData C hmin :=
  (ofFiniteLabels (D := D)
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    finiteLabels lemma8).toM8ConstructionData
      turnBounds lateTriples windowGeometry

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_localLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels =
        toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8 :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_turnBounds
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).turnBounds =
        turnBounds :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_lateTriples
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).lateTriples =
        lateTriples :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_windowGeometry
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).windowGeometry =
        windowGeometry :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_labels_p
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8BoundaryIndex) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels.labels.p
        i =
        finiteLabels.p i :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_labels_q
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8TriangleIndex) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels.labels.q
        i =
        finiteLabels.q i :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_labels_r
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8ExtraIndex) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels.labels.r
        i =
        lemma8.r i :=
  rfl

@[simp]
theorem toM8ConstructionDataOfFiniteLabels_labels_s
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8ExtraIndex) :
    (toM8ConstructionDataOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels.labels.s
        i =
        lemma8.s i :=
  rfl

/-- The direct finite-label route keeps the boundary-edge facts supplied by
the finite boundary certificate. -/
theorem toM8ConstructionDataOfFiniteLabels_boundaryEdge
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8TriangleIndex) :
    ((toM8ConstructionDataOfFiniteLabels (D := D)
        (connectedNoCut := connectedNoCut) (hmin := hmin)
        finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels
      |>.predicates.data.boundaryEdge) i :=
  finiteLabels.boundaryEdge i

/-- The direct finite-label route keeps the triangle-witness facts supplied
by the finite boundary certificate. -/
theorem toM8ConstructionDataOfFiniteLabels_triangleWitness
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8TriangleIndex) :
    ((toM8ConstructionDataOfFiniteLabels (D := D)
        (connectedNoCut := connectedNoCut) (hmin := hmin)
        finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels
      |>.predicates.data.triangleWitness) i :=
  finiteLabels.triangleWitness i

/-- The direct finite-label route keeps the extra-neighbor facts supplied by
the explicit Lemma 8 certificate. -/
theorem toM8ConstructionDataOfFiniteLabels_extraNeighborWitness
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds)
    (i : M8ExtraIndex) :
    ((toM8ConstructionDataOfFiniteLabels (D := D)
        (connectedNoCut := connectedNoCut) (hmin := hmin)
        finiteLabels lemma8 turnBounds lateTriples windowGeometry).localLabels
      |>.predicates.data.extraNeighborWitness) i :=
  lemma8.extraNeighborWitness_holds i

/-- Direct route to the concrete boundary-construction package from finite
labels and all remaining currently explicit M8 certificates. -/
def toBoundaryConstructionPackageOfFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    M8BoundaryConstructionPackage C hmin where
  boundaryLabels :=
    toBoundaryLabelPackageOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8
  turnBounds := turnBounds
  lateTriples := lateTriples
  windowGeometry := windowGeometry

@[simp]
theorem toBoundaryConstructionPackageOfFiniteLabels_boundaryLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    (toBoundaryConstructionPackageOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).boundaryLabels =
        toBoundaryLabelPackageOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8 :=
  rfl

@[simp]
theorem toBoundaryConstructionPackageOfFiniteLabels_toM8ConstructionData
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    (toBoundaryConstructionPackageOfFiniteLabels (D := D)
      (connectedNoCut := connectedNoCut) (hmin := hmin)
      finiteLabels lemma8 turnBounds lateTriples windowGeometry).toM8ConstructionData =
        toM8ConstructionDataOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8 turnBounds lateTriples windowGeometry :=
  rfl

/-- Conditional endpoint for the direct finite-label route: once finite labels,
Lemma 8, turn bounds, late triples, and window geometry are all supplied, the
existing M8 construction closure gives the contradiction. -/
theorem contradictionOfFiniteLabels
    (finiteLabels : M8FinitePQSpineCertificate D)
    (lemma8 :
      M8Lemma8Combinatorics
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8))
    (windowGeometry :
      M8WindowGeometry
        (toM8LocalLabelsOfFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8) turnBounds) :
    False :=
  (toBoundaryConstructionPackageOfFiniteLabels (D := D)
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    finiteLabels lemma8 turnBounds lateTriples windowGeometry).contradiction

/-! ## Boundary-walk and angle-data entry point -/

/--
Finite `p/q` labels over a boundary walk.

Compared with `M8FinitePQSpineCertificate`, the `p` labels are not separate
data: they are the selected outer-cycle vertices at `pIndex`.  The boundary
edge facts are also not separate data: each triangle edge is tied to an actual
certified edge of the supplied outer-boundary walk.
-/
structure M8BoundaryWalkPQSpineCertificate
    {P : OuterBoundaryCore (CanonicalUDGraph C)}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
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
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
        (CanonicalUDGraph C)) where
  pIndex : M8BoundaryIndex -> Fin P.outerCycle.length
  q : M8TriangleIndex -> Fin n
  edgeIndex : M8TriangleIndex -> Fin P.outerCycle.length
  boundaryEdge_left :
    forall i : M8TriangleIndex,
      P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)) =
        (P.outerCycle.edge (edgeIndex i)).1
  boundaryEdge_right :
    forall i : M8TriangleIndex,
      P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i)) =
        (P.outerCycle.edge (edgeIndex i)).2
  triangleWitness :
    forall i : M8TriangleIndex,
      (unitDistanceLocalGraph C).CommonNeighbor
        (P.outerCycle.vertex (pIndex (m8BoundaryIndexLeft i)))
        (P.outerCycle.vertex (pIndex (m8BoundaryIndexRight i))) (q i)

namespace M8BoundaryWalkPQSpineCertificate

variable {P : OuterBoundaryCore (CanonicalUDGraph C)}
variable {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {walk :
  OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
    IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
    (CanonicalUDGraph C)}

variable (K :
  M8BoundaryWalkPQSpineCertificate walk geometricAngleSum
    forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)

/-- The planar-boundary package produced by the strengthened walk, outer-angle,
and subpolygon inputs. -/
def toPlanarBoundaryData
    (_K :
      M8BoundaryWalkPQSpineCertificate walk geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C) :=
  walk.toPlanarBoundaryData geometricAngleSum forced_le_geometric
    geometric_le_polygon Subpolygon subpolygonData

@[simp]
theorem toPlanarBoundaryData_core :
    K.toPlanarBoundaryData.core = P :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts :
    K.toPlanarBoundaryData.outerBoundaryCounts = walk.counts :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon :
    K.toPlanarBoundaryData.Subpolygon = Subpolygon :=
  rfl

/-- The `p_i` label determined by the indexed boundary walk. -/
def p (i : M8BoundaryIndex) : Fin n :=
  P.outerCycle.vertex (K.pIndex i)

@[simp]
theorem p_eq_outerCycle (i : M8BoundaryIndex) :
    K.p i = K.toPlanarBoundaryData.core.outerCycle.vertex (K.pIndex i) :=
  rfl

/-- Boundary-edge adjacency derived from the actual certified boundary-walk
edge named by `edgeIndex`. -/
theorem boundaryEdge (i : M8TriangleIndex) :
    (unitDistanceLocalGraph C).Adj
      (K.p (m8BoundaryIndexLeft i)) (K.p (m8BoundaryIndexRight i)) := by
  have h :=
    OuterBoundaryWalkBookkeeping.edgeCertificate_unitDistanceAdj
      walk (K.edgeIndex i)
  have hedge :
      (OuterBoundaryWalkBookkeeping.edgeCertificate
        walk (K.edgeIndex i)).edge =
        P.outerCycle.edge (K.edgeIndex i) :=
    OuterBoundaryWalkBookkeeping.edgeCertificate_edge walk (K.edgeIndex i)
  simpa [p, GraphBridge.unitDistanceLocalGraph, CanonicalUDGraph, hedge,
    K.boundaryEdge_left i, K.boundaryEdge_right i] using h

/-- Convert the boundary-walk label input into the older finite `p/q` spine
certificate, deriving the fields available from the walk. -/
def toFinitePQSpineCertificate :
    M8FinitePQSpineCertificate K.toPlanarBoundaryData where
  pIndex := K.pIndex
  p := K.p
  q := K.q
  p_eq_outerCycle := K.p_eq_outerCycle
  boundaryEdge := K.boundaryEdge
  triangleWitness := K.triangleWitness

@[simp]
theorem toFinitePQSpineCertificate_pIndex (i : M8BoundaryIndex) :
    K.toFinitePQSpineCertificate.pIndex i = K.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p (i : M8BoundaryIndex) :
    K.toFinitePQSpineCertificate.p i = K.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q (i : M8TriangleIndex) :
    K.toFinitePQSpineCertificate.q i = K.q i :=
  rfl

/-- Boundary-walk entry point to the finite boundary-label assembly. -/
def toFiniteBoundaryLabelCertificate
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8FiniteBoundaryLabelCertificate
      K.toPlanarBoundaryData connectedNoCut hmin where
  finiteLabels := K.toFinitePQSpineCertificate
  lemma8 := lemma8

@[simp]
theorem toFiniteBoundaryLabelCertificate_finiteLabels
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (K.toFiniteBoundaryLabelCertificate
      connectedNoCut hmin lemma8).finiteLabels =
        K.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem toFiniteBoundaryLabelCertificate_lemma8
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    (K.toFiniteBoundaryLabelCertificate
      connectedNoCut hmin lemma8).lemma8 = lemma8 :=
  rfl

/-- Boundary-walk route to the checked boundary-label package. -/
def toBoundaryLabelPackage
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8BoundaryLabelPackage C :=
  (K.toFiniteBoundaryLabelCertificate connectedNoCut hmin lemma8).toBoundaryLabelPackage

@[simp]
theorem toBoundaryLabelPackage_labels_p
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels.p i =
      K.p i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_q
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).labels.q i =
      K.q i :=
  rfl

/-- Boundary-walk route to local M8 labels. -/
def toM8LocalLabels
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin)) :
    M8LocalLabels C :=
  (K.toBoundaryLabelPackage connectedNoCut hmin lemma8).toM8LocalLabels

@[simp]
theorem toM8LocalLabels_p
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (i : M8BoundaryIndex) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels.p i =
      K.p i :=
  rfl

@[simp]
theorem toM8LocalLabels_q
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (i : M8TriangleIndex) :
    (K.toM8LocalLabels connectedNoCut hmin lemma8).labels.q i =
      K.q i :=
  rfl

/-- Boundary-walk route to `M8ConstructionData` once the non-label M8 fields
are supplied. -/
def toM8ConstructionData
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples (K.toM8LocalLabels connectedNoCut hmin lemma8))
    (windowGeometry :
      M8WindowGeometry
        (K.toM8LocalLabels connectedNoCut hmin lemma8) turnBounds) :
    M8ConstructionData C hmin :=
  (K.toFiniteBoundaryLabelCertificate
    connectedNoCut hmin lemma8).toM8ConstructionData
      turnBounds lateTriples windowGeometry

/-- Conditional endpoint for the boundary-walk route. -/
theorem contradiction
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C)
    (lemma8 :
      M8Lemma8Combinatorics
        (K.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin))
    (turnBounds : M8TurnBounds)
    (lateTriples :
      M8LateTriples (K.toM8LocalLabels connectedNoCut hmin lemma8))
    (windowGeometry :
      M8WindowGeometry
        (K.toM8LocalLabels connectedNoCut hmin lemma8) turnBounds) :
    False :=
  (K.toFiniteBoundaryLabelCertificate
    connectedNoCut hmin lemma8).contradiction
      turnBounds lateTriples windowGeometry

end M8BoundaryWalkPQSpineCertificate

end

end BoundaryLabelCertificateAssembly
end Swanepoel
end ErdosProblems1066
