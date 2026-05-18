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
        ((ofFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8).toM8LocalLabels))
    (windowGeometry :
      M8WindowGeometry
        ((ofFiniteLabels (D := D)
          (connectedNoCut := connectedNoCut) (hmin := hmin)
          finiteLabels lemma8).toM8LocalLabels) turnBounds) :
    M8ConstructionData C hmin :=
  (ofFiniteLabels (D := D)
    (connectedNoCut := connectedNoCut) (hmin := hmin)
    finiteLabels lemma8).toM8ConstructionData
      turnBounds lateTriples windowGeometry

end

end BoundaryLabelCertificateAssembly
end Swanepoel
end ErdosProblems1066
