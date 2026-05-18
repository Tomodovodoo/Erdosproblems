import ErdosProblems1066.Swanepoel.M8SeparatedConstructionConcrete
import ErdosProblems1066.Swanepoel.M8TurnWindowNoEarlyFinal

set_option autoImplicit false

/-!
# Closure adapters for the broken-lattice honest-local route

This file keeps `BrokenLatticePipeline` acyclic.  The pipeline defines the
minimal-failure honest-local fact and the existential projection from it; this
closure file imports the concrete M8 construction layers and proves that their
existing local-label fields compose into that fact.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticePipeline
namespace MinimalFailureM8HonestLocalPredicatesFacts

open GraphBridge
open Lemma10Bridge
open MinimalGraphFacts

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-! ## Local-label and construction-data adapters -/

/-- Concrete M8 local labels already contain the honest local predicates needed
by `MinimalFailureM8HonestLocalPredicatesFacts`. -/
def ofM8LocalLabels
    (L : M8ConstructionInterface.M8LocalLabels C) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofHonestLocalPredicates L.predicates

@[simp]
theorem ofM8LocalLabels_toHonestLocalPredicates
    (L : M8ConstructionInterface.M8LocalLabels C) :
    (ofM8LocalLabels (hmin := hmin) L).toHonestLocalPredicates =
      L.predicates :=
  rfl

/-- The original existential route, specialized to concrete M8 local labels. -/
theorem exists_ofM8LocalLabels
    (_hmin : IsMinimalClearedFailure C)
    (L : M8ConstructionInterface.M8LocalLabels C) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = L.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (hmin := _hmin) (ofM8LocalLabels (hmin := _hmin) L))

/-- Clean M8 construction-interface data supplies the honest-local fact through
its local-label field. -/
def ofM8ConstructionData
    (D : M8ConstructionInterface.M8ConstructionData C hmin) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8LocalLabels D.localLabels

@[simp]
theorem ofM8ConstructionData_toHonestLocalPredicates
    (D : M8ConstructionInterface.M8ConstructionData C hmin) :
    (ofM8ConstructionData D).toHonestLocalPredicates =
      D.localLabels.predicates :=
  rfl

/-- The original existential route, specialized to clean M8 construction data.
-/
theorem exists_ofM8ConstructionData
    (D : M8ConstructionInterface.M8ConstructionData C hmin) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = D.localLabels.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (ofM8ConstructionData D))

/-- Boundary/Lemma 8 label data supplies the honest-local fact through its
checked local-label conversion. -/
def ofM8LabelsFromBoundaryData
    (D : M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData C) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8LocalLabels D.toM8LocalLabels

@[simp]
theorem ofM8LabelsFromBoundaryData_toHonestLocalPredicates
    (D : M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData C) :
    (ofM8LabelsFromBoundaryData (hmin := hmin) D).toHonestLocalPredicates =
      D.toM8LocalLabels.predicates :=
  rfl

/-- The original existential route, specialized to boundary/Lemma 8 label
data. -/
theorem exists_ofM8LabelsFromBoundaryData
    (_hmin : IsMinimalClearedFailure C)
    (D : M8LabelsFromBoundaryInterface.M8LabelsFromBoundaryData C) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = D.toM8LocalLabels.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (ofM8LabelsFromBoundaryData (hmin := _hmin) D))

/-! ## No-early and angle/containment adapters -/

/-- Local labels plus no-early triples and window-containment data assemble to
clean M8 construction data, hence to the honest-local fact. -/
def ofM8WindowContainmentNoEarly
    (L : M8ConstructionInterface.M8LocalLabels C)
    (T : M8ConstructionInterface.M8TurnBounds)
    (Hno : M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples L)
    (W : M8WindowGeometryFromContainment.M8WindowContainment L T) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8ConstructionData
    ({ localLabels := L
       turnBounds := T
       lateTriples := Hno.toM8LateTriples
       windowGeometry := W.toM8WindowGeometry } :
      M8ConstructionInterface.M8ConstructionData C hmin)

@[simp]
theorem ofM8WindowContainmentNoEarly_toHonestLocalPredicates
    (L : M8ConstructionInterface.M8LocalLabels C)
    (T : M8ConstructionInterface.M8TurnBounds)
    (Hno : M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples L)
    (W : M8WindowGeometryFromContainment.M8WindowContainment L T) :
    (ofM8WindowContainmentNoEarly (hmin := hmin) L T Hno W).toHonestLocalPredicates =
      L.predicates :=
  rfl

/-- The original existential route, specialized to local labels plus no-early
triples and window-containment data. -/
theorem exists_ofM8WindowContainmentNoEarly
    (_hmin : IsMinimalClearedFailure C)
    (L : M8ConstructionInterface.M8LocalLabels C)
    (T : M8ConstructionInterface.M8TurnBounds)
    (_Hno : M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples L)
    (_W : M8WindowGeometryFromContainment.M8WindowContainment L T) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = L.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (ofM8WindowContainmentNoEarly (hmin := _hmin) L T _Hno _W))

/-- Nonconcave-arc plus angle-containment data, together with no-early triples,
assembles to clean M8 construction data and then to the honest-local fact. -/
def ofM8ArcContainmentNoEarly
    {L : M8ConstructionInterface.M8LocalLabels C}
    (D : M8TurnBoundsFromArc.M8ArcContainmentData L)
    (Hno : M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples L) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8ConstructionData
    (D.toM8ConstructionData (hmin := hmin) Hno.toM8LateTriples)

@[simp]
theorem ofM8ArcContainmentNoEarly_toHonestLocalPredicates
    {L : M8ConstructionInterface.M8LocalLabels C}
    (D : M8TurnBoundsFromArc.M8ArcContainmentData L)
    (Hno : M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples L) :
    (ofM8ArcContainmentNoEarly (hmin := hmin) D Hno).toHonestLocalPredicates =
      L.predicates :=
  rfl

/-- The original existential route, specialized to arc/angle-containment data
plus no-early triples. -/
theorem exists_ofM8ArcContainmentNoEarly
    (_hmin : IsMinimalClearedFailure C)
    {L : M8ConstructionInterface.M8LocalLabels C}
    (_D : M8TurnBoundsFromArc.M8ArcContainmentData L)
    (_Hno : M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples L) :
    Exists fun P : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      P = L.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (ofM8ArcContainmentNoEarly (hmin := _hmin) _D _Hno))

/-- The fixed turn/window/no-early package supplies the honest-local fact by
forgetting to clean M8 construction data. -/
def ofM8TurnWindowNoEarlyPackage
    (P : M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8ConstructionData P.toM8ConstructionData

@[simp]
theorem ofM8TurnWindowNoEarlyPackage_toHonestLocalPredicates
    (P : M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin) :
    (ofM8TurnWindowNoEarlyPackage P).toHonestLocalPredicates =
      P.localLabels.predicates :=
  rfl

/-- The original existential route, specialized to the fixed
turn/window/no-early package. -/
theorem exists_ofM8TurnWindowNoEarlyPackage
    (P : M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin) :
    Exists fun Q : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      Q = P.localLabels.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (ofM8TurnWindowNoEarlyPackage P))

/-- The concrete separated component package supplies the honest-local fact by
forgetting to clean M8 construction data. -/
def ofM8SeparatedConstructionComponentPackage
    (P :
      M8SeparatedConstructionConcrete.M8SeparatedConstructionComponentPackage
        C hmin) :
    MinimalFailureM8HonestLocalPredicatesFacts C hmin :=
  ofM8ConstructionData P.toM8ConstructionData

@[simp]
theorem ofM8SeparatedConstructionComponentPackage_toHonestLocalPredicates
    (P :
      M8SeparatedConstructionConcrete.M8SeparatedConstructionComponentPackage
        C hmin) :
    (ofM8SeparatedConstructionComponentPackage P).toHonestLocalPredicates =
      P.labels.toM8LocalLabels.predicates :=
  rfl

/-- The original existential route, specialized to the concrete separated
component package. -/
theorem exists_ofM8SeparatedConstructionComponentPackage
    (P :
      M8SeparatedConstructionConcrete.M8SeparatedConstructionComponentPackage
        C hmin) :
    Exists fun Q : M8HonestLocalPredicates (unitDistanceLocalGraph C) =>
      Q = P.labels.toM8LocalLabels.predicates := by
  exact
    (exists_m8_honestLocalPredicates_of_minimalFailure
      (ofM8SeparatedConstructionComponentPackage P))

end MinimalFailureM8HonestLocalPredicatesFacts
end BrokenLatticePipeline
end Swanepoel
end ErdosProblems1066

end
