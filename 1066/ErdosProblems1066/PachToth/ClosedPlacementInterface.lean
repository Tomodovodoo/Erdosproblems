import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.OrientationData

/-!
# Explicit closed-placement certificates

This module gives a small interface for turning coordinate-level Pach--Toth
certificates into the non-rigid `DeformedPlacement.ClosedPlacement` structure.

No closed placement is asserted here without data: every existence theorem
below immediately constructs the required fields from the supplied
certificate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementInterface

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- An explicit coordinate certificate for a closed deformed Pach--Toth
placement.

The fields are the exact fields needed by
`DeformedPlacement.ClosedPlacement`: a point map, global separation,
same-block unit edges, and successor cross-connector unit edges. -/
structure ExplicitClosedPlacementCertificate (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  cross_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

namespace ExplicitClosedPlacementCertificate

/-- Build the closed placement carried by an explicit coordinate
certificate. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    DeformedPlacement.ClosedPlacement k hk where
  point := C.point
  separated := C.separated
  same_block_edges_unit := C.same_block_edges_unit
  cross_connector_edges_unit := C.cross_connector_edges_unit

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk)
    (i : Fin k) (v : LocalVertex) :
    C.toClosedPlacement.point i v = C.point i v :=
  rfl

/-- An explicit coordinate certificate provides the existing geometric
edge-soundness interface. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  C.toClosedPlacement.toExplicitEdgeSoundness

/-- An explicit coordinate certificate provides the indexed-chain realization
interface. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  C.toClosedPlacement.toIndexedChainRealization

end ExplicitClosedPlacementCertificate

/-- The named existence reduction requested by downstream workers.

This is only a repackaging theorem: the returned closed placement is
constructed directly from the certificate fields. -/
theorem exists_closedPlacement_of_explicit_certificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = C.point := by
  exact Exists.intro C.toClosedPlacement rfl

/-- A transition-based certificate: successor connector unit edges are supplied
by `OrientationData.TransitionCertificate`; global separation and same-block
unit edges remain explicit coordinate obligations. -/
structure ExplicitTransitionClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  transition :
    forall i : Fin k,
      OrientationData.TransitionCertificate
        (point i) (point (cyclicSucc hk i))
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1

namespace ExplicitTransitionClosedPlacementCertificate

/-- Forget transition structure to the explicit coordinate certificate, using
each transition certificate for the successor connector unit edges. -/
def toExplicitClosedPlacementCertificate {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk) :
    ExplicitClosedPlacementCertificate k hk where
  point := C.point
  separated := C.separated
  same_block_edges_unit := C.same_block_edges_unit
  cross_connector_edges_unit := by
    intro i u v hconn
    exact (C.transition i).connector_unit_target hconn

/-- Build the closed placement carried by a transition-based certificate. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  C.toExplicitClosedPlacementCertificate.toClosedPlacement

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk)
    (i : Fin k) (v : LocalVertex) :
    C.toClosedPlacement.point i v = C.point i v :=
  rfl

/-- A transition-based certificate provides the existing geometric
edge-soundness interface. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  C.toClosedPlacement.toExplicitEdgeSoundness

/-- A transition-based certificate provides the indexed-chain realization
interface. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  C.toClosedPlacement.toIndexedChainRealization

end ExplicitTransitionClosedPlacementCertificate

/-- Transition certificates plus explicit separation and same-block unit
certificates construct a closed placement. -/
theorem exists_closedPlacement_of_explicit_transition_certificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = C.point := by
  exact Exists.intro C.toClosedPlacement rfl

end

end ClosedPlacementInterface
end PachToth
end ErdosProblems1066
