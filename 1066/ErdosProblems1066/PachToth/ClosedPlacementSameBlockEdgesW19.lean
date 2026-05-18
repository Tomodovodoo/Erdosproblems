import ErdosProblems1066.PachToth.ClosedPlacementInterface
import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.ExactLocalGeometry

set_option autoImplicit false

/-!
# W19 same-block unit-edge adapters

This file isolates the same-block unit-edge obligation used by
`ClosedPlacementInterface.ExplicitClosedPlacementCertificate`,
`ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate`, and
`DeformedPlacement.ClosedPlacement`.

The adapter is deliberately narrow: it proves the same-block edge field from
the exact local Pach--Toth geometry, or transports that proof along a blockwise
exact-local distance/equality certificate.  Separation and cross-block
connector unit edges remain separate inputs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementSameBlockEdgesW19

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The same-block unit-edge field shared by the closed-placement interfaces. -/
def SameBlockUnitEdges {k : Nat}
    (point : Fin k -> LocalVertex -> R2) : Prop :=
  forall (i : Fin k) (u v : LocalVertex),
    Ne u v ->
    adj u v = true ->
      _root_.eucDist (point i u) (point i v) = 1

/-- A precise certificate for only the same-block unit-edge obligation. -/
structure SameBlockUnitEdgeCertificate {k : Nat}
    (point : Fin k -> LocalVertex -> R2) : Prop where
  unit_edges : SameBlockUnitEdges point

namespace SameBlockUnitEdgeCertificate

/-- Use a same-block certificate as the raw field expected by the existing
interfaces. -/
theorem unit_edges_apply {k : Nat} {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (i : Fin k) (u v : LocalVertex)
    (huv : Ne u v) (hadj : adj u v = true) :
    _root_.eucDist (point i u) (point i v) = 1 :=
  S.unit_edges i u v huv hadj

/-- Existing deformed closed placements already carry the same-block
certificate. -/
def ofClosedPlacement {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    SameBlockUnitEdgeCertificate P.point where
  unit_edges := P.same_block_edges_unit

/-- Existing explicit coordinate certificates already carry the same-block
certificate. -/
def ofExplicitClosedPlacementCertificate {k : Nat} {hk : 0 < k}
    (C :
      ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    SameBlockUnitEdgeCertificate C.point where
  unit_edges := C.same_block_edges_unit

/-- Existing transition-based coordinate certificates already carry the
same-block certificate. -/
def ofExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (C :
      ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
        k hk) :
    SameBlockUnitEdgeCertificate C.point where
  unit_edges := C.same_block_edges_unit

/-- The exact local geometry proves that every local adjacency is a unit
edge. -/
theorem exactLocal_adj_unit_distance (u v : LocalVertex)
    (hadj : adj u v = true) :
    _root_.eucDist
      (ExactLocalGeometry.localPoint u)
      (ExactLocalGeometry.localPoint v) = 1 :=
  ExactLocalGeometry.adj_unit_distance u v hadj

/-- Symmetric local adjacency gives the same exact unit edge, using the
finite local adjacency symmetry fact. -/
theorem exactLocal_adj_symm_unit_distance (u v : LocalVertex)
    (hadj : adj v u = true) :
    _root_.eucDist
      (ExactLocalGeometry.localPoint u)
      (ExactLocalGeometry.localPoint v) = 1 := by
  exact ExactLocalGeometry.adj_unit_distance u v (by
    rw [adj_symm u v]
    exact hadj)

/-- The repeated exact local block has the required same-block unit edges for
any block index type. -/
def exactLocal (k : Nat) :
    SameBlockUnitEdgeCertificate
      (fun _ : Fin k => ExactLocalGeometry.localPoint) where
  unit_edges := by
    intro _i u v _huv hadj
    exact exactLocal_adj_unit_distance u v hadj

/-- Transport the exact-local unit-edge proof along blockwise exact-local
distance preservation. -/
def ofExactLocalDistances {k : Nat}
    {point : Fin k -> LocalVertex -> R2}
    (hdist :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist (point i u) (point i v) =
          _root_.eucDist
            (ExactLocalGeometry.localPoint u)
            (ExactLocalGeometry.localPoint v)) :
    SameBlockUnitEdgeCertificate point where
  unit_edges := by
    intro i u v _huv hadj
    calc
      _root_.eucDist (point i u) (point i v) =
          _root_.eucDist
            (ExactLocalGeometry.localPoint u)
            (ExactLocalGeometry.localPoint v) := hdist i u v
      _ = 1 := exactLocal_adj_unit_distance u v hadj

/-- A point map equal to the exact local block in every block has the
same-block unit edges. -/
def ofExactLocalPointEq {k : Nat}
    {point : Fin k -> LocalVertex -> R2}
    (hpoint :
      forall (i : Fin k) (v : LocalVertex),
        point i v = ExactLocalGeometry.localPoint v) :
    SameBlockUnitEdgeCertificate point :=
  ofExactLocalDistances (by
    intro i u v
    rw [hpoint i u, hpoint i v])

/-- Package a same-block certificate with the remaining explicit fields into
the coordinate closed-placement certificate. -/
def toExplicitClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (cross_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk where
  point := point
  separated := separated
  same_block_edges_unit := S.unit_edges
  cross_connector_edges_unit := cross_connector_edges_unit

@[simp]
theorem toExplicitClosedPlacementCertificate_point
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (cross_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1)
    (i : Fin k) (v : LocalVertex) :
    (S.toExplicitClosedPlacementCertificate
      separated cross_connector_edges_unit).point i v = point i v :=
  rfl

/-- Package a same-block certificate with transition and separation fields
into the transition-based closed-placement certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk where
  point := point
  transition := transition
  separated := separated
  same_block_edges_unit := S.unit_edges

@[simp]
theorem toExplicitTransitionClosedPlacementCertificate_point
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (i : Fin k) (v : LocalVertex) :
    (S.toExplicitTransitionClosedPlacementCertificate
      transition separated).point i v = point i v :=
  rfl

/-- Package a same-block certificate directly into the deformed closed
placement interface once the global and successor-connector fields are known. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (cross_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    DeformedPlacement.ClosedPlacement k hk where
  point := point
  separated := separated
  same_block_edges_unit := S.unit_edges
  cross_connector_edges_unit := cross_connector_edges_unit

@[simp]
theorem toClosedPlacement_point
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (cross_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1)
    (i : Fin k) (v : LocalVertex) :
    (S.toClosedPlacement separated cross_connector_edges_unit).point i v =
      point i v :=
  rfl

/-- Same-block certificate plus the remaining direct fields gives the existing
closed-placement existence interface. -/
theorem exists_closedPlacement_of_sameBlockCertificate
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (cross_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = point := by
  exact Exists.intro
    (S.toClosedPlacement separated cross_connector_edges_unit)
    rfl

/-- Same-block certificate plus transition fields gives the existing
transition-certificate route to a closed placement. -/
theorem exists_closedPlacement_of_sameBlockTransitionCertificate
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (S : SameBlockUnitEdgeCertificate point)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = point := by
  exact
    ClosedPlacementInterface.exists_closedPlacement_of_explicit_transition_certificate
      (S.toExplicitTransitionClosedPlacementCertificate transition separated)

end SameBlockUnitEdgeCertificate

end

end ClosedPlacementSameBlockEdgesW19
end PachToth
end ErdosProblems1066
