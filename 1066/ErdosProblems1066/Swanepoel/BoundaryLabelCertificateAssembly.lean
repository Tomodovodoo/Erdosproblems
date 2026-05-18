import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.BoundaryLabelExtractionTasks
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete

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
open CutVertexClosure
open GraphBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

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

/-- Assemble `M8ConstructionData` once the remaining non-label M8 certificates
are supplied. -/
def toM8ConstructionData
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples K.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry K.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  K.toBoundaryLabelPackage.toM8ConstructionData
    turnBounds lateTriples windowGeometry

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

end M8FiniteBoundaryLabelCertificate

/-! ## Direct finite-label entry point -/

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

end

end BoundaryLabelCertificateAssembly
end Swanepoel
end ErdosProblems1066
