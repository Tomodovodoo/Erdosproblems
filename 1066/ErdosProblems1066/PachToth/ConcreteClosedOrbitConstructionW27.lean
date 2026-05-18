import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26
import ErdosProblems1066.PachToth.CrossBlockDistanceSqReduction

set_option autoImplicit false

/-!
# W27 squared-distance closed-orbit closure

This file keeps the W26 concrete closed-orbit target as the live object, but
restates its metric side in squared-distance form.  The result is a tight
non-target equivalence:

* W26 `ConcreteClosedOrbitFamily`;
* W26 `MinimalFieldsWithOrbitClosure`;
* the same point maps and successor maps with all distance obligations stated
  via `CrossBlockDistanceSqReduction.sqDist`.

No rigid translation field is introduced here; the successor equation remains
the actual W26 oriented-transition orbit closure.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementConcreteConstructionW27

open Arithmetic
open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real

abbrev sqDist (p q : R2) : Real :=
  CrossBlockDistanceSqReduction.sqDist p q

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

theorem root_eucDist_eq_one_iff_sqDist_eq_one (p q : R2) :
    _root_.eucDist p q = 1 <-> sqDist p q = 1 := by
  simpa [sqDist, CrossBlockDistanceSqReduction.sqDist,
    AffineLocalGeometry.distSq] using
    (_root_.eucDist_eq_one_iff p q)

theorem root_eucDist_eq_one_of_sqDist_eq_one
    {p q : R2}
    (h : sqDist p q = 1) :
    _root_.eucDist p q = 1 :=
  (root_eucDist_eq_one_iff_sqDist_eq_one p q).2 h

theorem sqDist_eq_one_of_root_eucDist_eq_one
    {p q : R2}
    (h : _root_.eucDist p q = 1) :
    sqDist p q = 1 :=
  (root_eucDist_eq_one_iff_sqDist_eq_one p q).1 h

/-- W26 minimal fields with successor orbit closure, but with the metric
obligations exposed in squared-distance form. -/
structure SquaredMinimalFieldsWithOrbitClosure where
  point : forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2
  step :
    forall (k : Nat) (_hk : 0 < k),
      Fin k -> OrientationData.OrientedTransition
  successor_eq :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (v : LocalVertex),
      point k hk (cyclicSucc hk i) v =
        (step k hk i).placeNext (point k hk i) v
  separated_sq :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= sqDist (point k hk i u) (point k hk j v)
  same_block_edges_sq_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        sqDist (point k hk i u) (point k hk i v) = 1
  cross_connector_edges_sq_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        sqDist (point k hk i u) (point k hk (cyclicSucc hk i) v) = 1

namespace SquaredMinimalFieldsWithOrbitClosure

/-- Squared-distance orbit-closure fields give the actual W26 minimal
orbit-closure surface by removing the square roots with existing APIs. -/
def toMinimalFieldsWithOrbitClosure
    (S : SquaredMinimalFieldsWithOrbitClosure) :
    MinimalFieldsWithOrbitClosure where
  fields :=
    { point := S.point
      separated := fun k hk i u j v hij =>
        CrossBlockDistanceSqReduction.one_le_root_eucDist_of_one_le_sqDist
          (S.separated_sq k hk i u j v hij)
      same_block_edges_unit := fun k hk i u v huv hadj =>
        root_eucDist_eq_one_of_sqDist_eq_one
          (S.same_block_edges_sq_unit k hk i u v huv hadj)
      cross_connector_edges_unit := fun k hk i u v hconn =>
        root_eucDist_eq_one_of_sqDist_eq_one
          (S.cross_connector_edges_sq_unit k hk i u v hconn) }
  step := S.step
  successor_eq := S.successor_eq

/-- Squared-distance orbit-closure fields give the actual W26 concrete
closed-orbit family. -/
def toConcreteClosedOrbitFamily
    (S : SquaredMinimalFieldsWithOrbitClosure) :
    ConcreteClosedOrbitFamily :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure.toConcreteClosedOrbitFamily
    S.toMinimalFieldsWithOrbitClosure

@[simp]
theorem toMinimalFieldsWithOrbitClosure_fields_point
    (S : SquaredMinimalFieldsWithOrbitClosure)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    S.toMinimalFieldsWithOrbitClosure.fields.point k hk i v =
      S.point k hk i v :=
  rfl

@[simp]
theorem toConcreteClosedOrbitFamily_point
    (S : SquaredMinimalFieldsWithOrbitClosure)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toConcreteClosedOrbitFamily.data k hk).point i v =
      S.point k hk i v :=
  rfl

end SquaredMinimalFieldsWithOrbitClosure

namespace MinimalFieldsWithOrbitClosure

/-- The actual W26 orbit-closure surface can be read in squared-distance form. -/
def toSquaredMinimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    SquaredMinimalFieldsWithOrbitClosure where
  point := M.fields.point
  step := M.step
  successor_eq := M.successor_eq
  separated_sq := fun k hk i u j v hij =>
    CrossBlockDistanceSqReduction.one_le_sqDist_of_one_le_root_eucDist
      (M.fields.separated k hk i u j v hij)
  same_block_edges_sq_unit := fun k hk i u v huv hadj =>
    sqDist_eq_one_of_root_eucDist_eq_one
      (M.fields.same_block_edges_unit k hk i u v huv hadj)
  cross_connector_edges_sq_unit := fun k hk i u v hconn =>
    sqDist_eq_one_of_root_eucDist_eq_one
      (M.fields.cross_connector_edges_unit k hk i u v hconn)

@[simp]
theorem toSquaredMinimalFieldsWithOrbitClosure_point
    (M : MinimalFieldsWithOrbitClosure)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    M.toSquaredMinimalFieldsWithOrbitClosure.point k hk i v =
      M.fields.point k hk i v :=
  rfl

end MinimalFieldsWithOrbitClosure

namespace ConcreteClosedOrbitFamily

/-- The actual W26 concrete closed-orbit family, read with squared-distance
metric obligations. -/
def toSquaredMinimalFieldsWithOrbitClosure
    (F : ConcreteClosedOrbitFamily) :
    SquaredMinimalFieldsWithOrbitClosure :=
  MinimalFieldsWithOrbitClosure.toSquaredMinimalFieldsWithOrbitClosure
    (ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily.toMinimalFieldsWithOrbitClosure F)

@[simp]
theorem toSquaredMinimalFieldsWithOrbitClosure_point
    (F : ConcreteClosedOrbitFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    F.toSquaredMinimalFieldsWithOrbitClosure.point k hk i v =
      (F.data k hk).point i v :=
  rfl

end ConcreteClosedOrbitFamily

/-- Squared-distance orbit closure is exactly the W26 minimal orbit-closure
surface. -/
theorem nonempty_squaredMinimalFieldsWithOrbitClosure_iff_minimalFieldsWithOrbitClosure :
    Nonempty SquaredMinimalFieldsWithOrbitClosure <->
      Nonempty MinimalFieldsWithOrbitClosure := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toMinimalFieldsWithOrbitClosure⟩
  · rintro ⟨M⟩
    exact ⟨M.toSquaredMinimalFieldsWithOrbitClosure⟩

/-- The actual W26 concrete closed-orbit family is equivalent to the
squared-distance orbit-closure surface. -/
theorem nonempty_concreteClosedOrbitFamily_iff_squaredMinimalFieldsWithOrbitClosure :
    Nonempty ConcreteClosedOrbitFamily <->
      Nonempty SquaredMinimalFieldsWithOrbitClosure :=
  Iff.trans
    ClosedPlacementConcreteConstructionW26.nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure
    nonempty_squaredMinimalFieldsWithOrbitClosure_iff_minimalFieldsWithOrbitClosure.symm

end

end ClosedPlacementConcreteConstructionW27
end PachToth

namespace Verified

abbrev PachTothW27SquaredMinimalFieldsWithOrbitClosure : Type :=
  PachToth.ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure

theorem pachtoth_w27_nonempty_concreteClosedOrbitFamily_iff_squaredOrbitClosure :
    Nonempty
        PachToth.ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily <->
      Nonempty PachTothW27SquaredMinimalFieldsWithOrbitClosure :=
  PachToth.ClosedPlacementConcreteConstructionW27.nonempty_concreteClosedOrbitFamily_iff_squaredMinimalFieldsWithOrbitClosure

end Verified
end ErdosProblems1066
