import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete

set_option autoImplicit false

/-!
# Exterior frontier rows for the face-orbit Jordan source

This file keeps the S2 face-orbit source honest: the enclosure predicates are
derived from a supplied exterior set, and the boundary-point closure field is
discharged by Mathlib's frontier/closure facts rather than by a synthetic
predicate.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanTopologyExteriorEnclosure

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology

noncomputable section

universe u

variable {n : Nat}

/-- A point on the frontier of a set lies in the closure of the complement.
This is the Mathlib topological fact used below to turn exterior-frontier
membership into the `insideOrOn` boundary-point row. -/
theorem mem_closure_compl_of_mem_frontier
    {alpha : Type u} [TopologicalSpace alpha] {s : Set alpha} {p : alpha}
    (hp : p ∈ frontier s) :
    p ∈ closure sᶜ := by
  have hp_compl : p ∈ frontier sᶜ := by
    simpa [frontier_compl] using hp
  exact (frontier_subset_closure (s := sᶜ)) hp_compl

theorem mem_closure_compl_of_not_mem
    {alpha : Type u} [TopologicalSpace alpha] {s : Set alpha} {p : alpha}
    (hp : p ∉ s) :
    p ∈ closure sᶜ :=
  subset_closure hp

theorem boundary_vertex_frontier_of_frontier_iff_cycle_vertex
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    forall k : Fin B.length,
      (canonicalGraph C).point (B.vertex k) ∈ frontier exterior :=
  fun k => (frontier_iff_cycle_vertex (B.vertex k)).2 ⟨k, rfl⟩

theorem all_vertices_closure_compl_of_frontier_iff_cycle_vertex_off_cycle_closure
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (off_cycle_vertices_in_closure_compl :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∈ closure exteriorᶜ)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ closure exteriorᶜ := by
  intro v
  by_cases hv : Exists fun k : Fin B.length => B.vertex k = v
  · exact
      mem_closure_compl_of_mem_frontier
        ((frontier_iff_cycle_vertex v).2 hv)
  · exact off_cycle_vertices_in_closure_compl v hv

theorem all_vertices_closure_compl_of_frontier_iff_cycle_vertex_off_cycle_not_mem
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (off_cycle_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ closure exteriorᶜ :=
  all_vertices_closure_compl_of_frontier_iff_cycle_vertex_off_cycle_closure
    B exterior
    (fun v hv =>
      mem_closure_compl_of_not_mem
        (off_cycle_vertices_not_mem_exterior v hv))
    frontier_iff_cycle_vertex

theorem not_frontier_of_not_cycle_vertex_frontier_iff_cycle_vertex
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    forall v : Fin n,
      (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
        (canonicalGraph C).point v ∉ frontier exterior := by
  intro v hv hfrontier
  exact hv ((frontier_iff_cycle_vertex v).1 hfrontier)

theorem frontier_iff_cycle_vertex_of_frontier_vertices_cycle_vertices
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (frontier_vertices_are_cycle_vertices :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior ->
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_vertices_frontier :
      forall k : Fin B.length,
        (canonicalGraph C).point (B.vertex k) ∈ frontier exterior) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier exterior <->
        Exists fun k : Fin B.length => B.vertex k = v := by
  intro v
  constructor
  · exact frontier_vertices_are_cycle_vertices v
  · intro hv
    rcases hv with ⟨k, hk⟩
    rw [← hk]
    exact cycle_vertices_frontier k

theorem frontier_iff_cycle_vertex_of_cycle_frontier_off_cycle_not_frontier
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (cycle_vertices_frontier :
      forall k : Fin B.length,
        (canonicalGraph C).point (B.vertex k) ∈ frontier exterior)
    (off_cycle_vertices_not_frontier :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉ frontier exterior) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier exterior <->
        Exists fun k : Fin B.length => B.vertex k = v := by
  refine
    frontier_iff_cycle_vertex_of_frontier_vertices_cycle_vertices
      B exterior ?_ cycle_vertices_frontier
  intro v hfrontier
  by_contra hv
  exact off_cycle_vertices_not_frontier v hv hfrontier

theorem frontier_iff_orbit_vertex_of_frontier_vertices_orbit_vertices
    {C : _root_.UDConfig n}
    {R : UnitDistanceRotationSystem C}
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (frontier_vertices_are_orbit_vertices :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior ->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v)
    (orbit_vertices_frontier :
      forall k : Fin O.boundary.length,
        (canonicalGraph C).point (O.boundary.vertex k) ∈ frontier exterior) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier exterior <->
        Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v :=
  frontier_iff_cycle_vertex_of_frontier_vertices_cycle_vertices
    O.boundary exterior frontier_vertices_are_orbit_vertices
    orbit_vertices_frontier

theorem frontier_iff_orbit_vertex_of_orbit_frontier_off_orbit_not_frontier
    {C : _root_.UDConfig n}
    {R : UnitDistanceRotationSystem C}
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (orbit_vertices_frontier :
      forall k : Fin O.boundary.length,
        (canonicalGraph C).point (O.boundary.vertex k) ∈ frontier exterior)
    (off_orbit_vertices_not_frontier :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ frontier exterior) :
    forall v : Fin n,
      (canonicalGraph C).point v ∈ frontier exterior <->
        Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v :=
  frontier_iff_cycle_vertex_of_cycle_frontier_off_cycle_not_frontier
    O.boundary exterior orbit_vertices_frontier
    off_orbit_vertices_not_frontier

/-- Build the matching Jordan enclosure for a concrete unit-distance cycle
from an exterior set whose frontier is exactly that cycle on graph vertices.

The boundary-frontier row and the closure row for boundary vertices are derived
from the single `frontier_iff_cycle_vertex` row.  The only closure rows still
required as input are the off-cycle graph vertices. -/
def jordanOuterComponentEnclosure_of_exterior_frontier_closure
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (off_cycle_vertices_in_closure_compl :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∈ closure exteriorᶜ)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    JordanBoundaryConcrete.JordanOuterComponentEnclosure C B where
  insideOrOn := fun p => p ∈ closure exteriorᶜ
  onBoundary := fun v => (canonicalGraph C).point v ∈ frontier exterior
  boundary_vertex_onBoundary :=
    boundary_vertex_frontier_of_frontier_iff_cycle_vertex
      B exterior frontier_iff_cycle_vertex
  boundary_point_insideOrOn := fun k =>
    mem_closure_compl_of_mem_frontier
      ((frontier_iff_cycle_vertex (B.vertex k)).2 ⟨k, rfl⟩)
  all_vertices_insideOrOn :=
    all_vertices_closure_compl_of_frontier_iff_cycle_vertex_off_cycle_closure
      B exterior off_cycle_vertices_in_closure_compl
      frontier_iff_cycle_vertex
  onBoundary_iff_outer_cycle := frontier_iff_cycle_vertex

/-- Version of `jordanOuterComponentEnclosure_of_exterior_frontier_closure`
where off-cycle vertices are proved outside the exterior itself. -/
def jordanOuterComponentEnclosure_of_exterior_frontier_not_mem
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (off_cycle_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior)
    (frontier_iff_cycle_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin B.length => B.vertex k = v) :
    JordanBoundaryConcrete.JordanOuterComponentEnclosure C B :=
  jordanOuterComponentEnclosure_of_exterior_frontier_closure
    B exterior
    (fun v hv =>
      mem_closure_compl_of_not_mem
        (off_cycle_vertices_not_mem_exterior v hv))
    frontier_iff_cycle_vertex

def jordanOuterComponentEnclosure_of_exterior_frontier_rows_not_mem
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (frontier_vertices_are_cycle_vertices :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior ->
          Exists fun k : Fin B.length => B.vertex k = v)
    (cycle_vertices_frontier :
      forall k : Fin B.length,
        (canonicalGraph C).point (B.vertex k) ∈ frontier exterior)
    (off_cycle_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior) :
    JordanBoundaryConcrete.JordanOuterComponentEnclosure C B :=
  jordanOuterComponentEnclosure_of_exterior_frontier_not_mem
    B exterior off_cycle_vertices_not_mem_exterior
    (frontier_iff_cycle_vertex_of_frontier_vertices_cycle_vertices
      B exterior frontier_vertices_are_cycle_vertices cycle_vertices_frontier)

def jordanOuterComponentEnclosure_of_exterior_cycle_frontier_not_frontier_not_mem
    {C : _root_.UDConfig n}
    (B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C)
    (exterior : Set PlanarInterface.Point)
    (cycle_vertices_frontier :
      forall k : Fin B.length,
        (canonicalGraph C).point (B.vertex k) ∈ frontier exterior)
    (off_cycle_vertices_not_frontier :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉ frontier exterior)
    (off_cycle_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior) :
    JordanBoundaryConcrete.JordanOuterComponentEnclosure C B :=
  jordanOuterComponentEnclosure_of_exterior_frontier_not_mem
    B exterior off_cycle_vertices_not_mem_exterior
    (frontier_iff_cycle_vertex_of_cycle_frontier_off_cycle_not_frontier
      B exterior cycle_vertices_frontier off_cycle_vertices_not_frontier)

/-- A rotation system, a face orbit, and exterior-frontier/closure rows produce
the reduced S2 `FaceOrbitJordanEnclosureSource`. -/
def faceOrbitJordanEnclosureSource_of_exterior_frontier_closure
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (off_orbit_vertices_in_closure_compl :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∈ closure exteriorᶜ)
    (frontier_iff_orbit_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v) :
    FaceOrbitJordanEnclosureSource C where
  rotation := R
  orbit := O
  enclosure :=
    jordanOuterComponentEnclosure_of_exterior_frontier_closure
      O.boundary exterior off_orbit_vertices_in_closure_compl
      frontier_iff_orbit_vertex

/-- Version of `faceOrbitJordanEnclosureSource_of_exterior_frontier_closure`
where non-orbit vertices are proved outside the exterior itself. -/
def faceOrbitJordanEnclosureSource_of_exterior_frontier_not_mem
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (off_orbit_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior)
    (frontier_iff_orbit_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v) :
    FaceOrbitJordanEnclosureSource C where
  rotation := R
  orbit := O
  enclosure :=
    jordanOuterComponentEnclosure_of_exterior_frontier_not_mem
      O.boundary exterior off_orbit_vertices_not_mem_exterior
      frontier_iff_orbit_vertex

/-- Build the reduced source from the two actual frontier directions and the
non-orbit outside-exterior row. -/
def faceOrbitJordanEnclosureSource_of_exterior_frontier_rows_not_mem
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (frontier_vertices_are_orbit_vertices :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior ->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v)
    (orbit_vertices_frontier :
      forall k : Fin O.boundary.length,
        (canonicalGraph C).point (O.boundary.vertex k) ∈ frontier exterior)
    (off_orbit_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior) :
    FaceOrbitJordanEnclosureSource C :=
  faceOrbitJordanEnclosureSource_of_exterior_frontier_not_mem
    R O exterior off_orbit_vertices_not_mem_exterior
    (frontier_iff_orbit_vertex_of_frontier_vertices_orbit_vertices
      O exterior frontier_vertices_are_orbit_vertices
      orbit_vertices_frontier)

/-- Variant where the negative frontier direction is supplied as a non-orbit
not-frontier row. -/
def faceOrbitJordanEnclosureSource_of_exterior_orbit_frontier_not_frontier_not_mem
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (orbit_vertices_frontier :
      forall k : Fin O.boundary.length,
        (canonicalGraph C).point (O.boundary.vertex k) ∈ frontier exterior)
    (off_orbit_vertices_not_frontier :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ frontier exterior)
    (off_orbit_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior) :
    FaceOrbitJordanEnclosureSource C :=
  faceOrbitJordanEnclosureSource_of_exterior_frontier_not_mem
    R O exterior off_orbit_vertices_not_mem_exterior
    (frontier_iff_orbit_vertex_of_orbit_frontier_off_orbit_not_frontier
      O exterior orbit_vertices_frontier
      off_orbit_vertices_not_frontier)

/-- Nonempty form of the exterior-frontier reduction to the face-orbit source. -/
theorem nonempty_faceOrbitJordanEnclosureSource_of_exterior_frontier_closure
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (off_orbit_vertices_in_closure_compl :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∈ closure exteriorᶜ)
    (frontier_iff_orbit_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  ⟨faceOrbitJordanEnclosureSource_of_exterior_frontier_closure
    R O exterior off_orbit_vertices_in_closure_compl
    frontier_iff_orbit_vertex⟩

/-- Nonempty face-orbit source from exterior-frontier rows and off-orbit
outside-exterior rows. -/
theorem nonempty_faceOrbitJordanEnclosureSource_of_exterior_frontier_not_mem
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (off_orbit_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior)
    (frontier_iff_orbit_vertex :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior <->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  ⟨faceOrbitJordanEnclosureSource_of_exterior_frontier_not_mem
    R O exterior off_orbit_vertices_not_mem_exterior
    frontier_iff_orbit_vertex⟩

/-- Nonempty reduced source from the two actual frontier directions and the
non-orbit outside-exterior row. -/
theorem nonempty_faceOrbitJordanEnclosureSource_of_exterior_frontier_rows_not_mem
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (frontier_vertices_are_orbit_vertices :
      forall v : Fin n,
        (canonicalGraph C).point v ∈ frontier exterior ->
          Exists fun k : Fin O.boundary.length => O.boundary.vertex k = v)
    (orbit_vertices_frontier :
      forall k : Fin O.boundary.length,
        (canonicalGraph C).point (O.boundary.vertex k) ∈ frontier exterior)
    (off_orbit_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  ⟨faceOrbitJordanEnclosureSource_of_exterior_frontier_rows_not_mem
    R O exterior frontier_vertices_are_orbit_vertices
    orbit_vertices_frontier off_orbit_vertices_not_mem_exterior⟩

/-- Nonempty reduced source from positive orbit-frontier, negative non-orbit
not-frontier, and non-orbit outside-exterior rows. -/
theorem nonempty_faceOrbitJordanEnclosureSource_of_exterior_orbit_frontier_not_frontier_not_mem
    {C : _root_.UDConfig n}
    (R : UnitDistanceRotationSystem C)
    (O : FaceDartOrbit C R)
    (exterior : Set PlanarInterface.Point)
    (orbit_vertices_frontier :
      forall k : Fin O.boundary.length,
        (canonicalGraph C).point (O.boundary.vertex k) ∈ frontier exterior)
    (off_orbit_vertices_not_frontier :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ frontier exterior)
    (off_orbit_vertices_not_mem_exterior :
      forall v : Fin n,
        (¬ Exists fun k : Fin O.boundary.length =>
          O.boundary.vertex k = v) ->
          (canonicalGraph C).point v ∉ exterior) :
    Nonempty (FaceOrbitJordanEnclosureSource C) :=
  ⟨faceOrbitJordanEnclosureSource_of_exterior_orbit_frontier_not_frontier_not_mem
    R O exterior orbit_vertices_frontier off_orbit_vertices_not_frontier
    off_orbit_vertices_not_mem_exterior⟩

/-- The finite planar exterior-dart theorem is reduced to an actual rotation
system face orbit plus exterior-frontier/closure rows for every checked graph
input.  This feeds the existing S2 theorem surface through
`FaceOrbitJordanEnclosureSource`, while deriving the Jordan enclosure from
Mathlib frontier/closure facts. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_frontier_closure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∈ closure exteriorᶜ) /\
                (forall v : Fin n,
                  (canonicalGraph C).point v ∈ frontier exterior <->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (fun C inputs => by
      rcases h C inputs with
        ⟨R, O, exterior, off_orbit_vertices_in_closure_compl,
          frontier_iff_orbit_vertex⟩
      exact
        nonempty_faceOrbitJordanEnclosureSource_of_exterior_frontier_closure
          R O exterior off_orbit_vertices_in_closure_compl
          frontier_iff_orbit_vertex)

/-- The same exterior-frontier theorem surface, with the off-orbit row stated
as outside the exterior rather than already in the closure of its complement. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_frontier_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ exterior) /\
                (forall v : Fin n,
                  (canonicalGraph C).point v ∈ frontier exterior <->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (fun C inputs => by
      rcases h C inputs with
        ⟨R, O, exterior, off_orbit_vertices_not_mem_exterior,
          frontier_iff_orbit_vertex⟩
      exact
        nonempty_faceOrbitJordanEnclosureSource_of_exterior_frontier_not_mem
          R O exterior off_orbit_vertices_not_mem_exterior
          frontier_iff_orbit_vertex)

/-- Exterior-dart theorem from actual frontier directions plus the non-orbit
outside-exterior row. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_frontier_rows_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (canonicalGraph C).point v ∈ frontier exterior ->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v) /\
                (forall k : Fin O.boundary.length,
                  (canonicalGraph C).point (O.boundary.vertex k) ∈
                    frontier exterior) /\
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ exterior)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (fun C inputs => by
      rcases h C inputs with
        ⟨R, O, exterior, frontier_vertices_are_orbit_vertices,
          orbit_vertices_frontier, off_orbit_vertices_not_mem_exterior⟩
      exact
        nonempty_faceOrbitJordanEnclosureSource_of_exterior_frontier_rows_not_mem
          R O exterior frontier_vertices_are_orbit_vertices
          orbit_vertices_frontier off_orbit_vertices_not_mem_exterior)

/-- Exterior-dart theorem from orbit-frontier, non-orbit not-frontier, and
non-orbit outside-exterior rows. -/
def finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_orbit_frontier_not_frontier_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall k : Fin O.boundary.length,
                  (canonicalGraph C).point (O.boundary.vertex k) ∈
                    frontier exterior) /\
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ frontier exterior) /\
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ exterior)) :
    FinitePlanarStraightLineExteriorDartOrbitTheorem :=
  finitePlanarStraightLineExteriorDartOrbitTheorem_of_faceOrbitJordanEnclosureSource
    (fun C inputs => by
      rcases h C inputs with
        ⟨R, O, exterior, orbit_vertices_frontier,
          off_orbit_vertices_not_frontier,
          off_orbit_vertices_not_mem_exterior⟩
      exact
        nonempty_faceOrbitJordanEnclosureSource_of_exterior_orbit_frontier_not_frontier_not_mem
          R O exterior orbit_vertices_frontier
          off_orbit_vertices_not_frontier
          off_orbit_vertices_not_mem_exterior)

/-- The same exterior-frontier rows also prove the chosen outer-component
theorem surface used downstream by S2. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exterior_frontier_closure
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∈ closure exteriorᶜ) /\
                (forall v : Fin n,
                  (canonicalGraph C).point v ∈ frontier exterior <->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_frontier_closure
      h)

/-- Chosen outer-component theorem from frontier-exactness plus proof that
non-orbit graph vertices lie outside the exterior. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exterior_frontier_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ exterior) /\
                (forall v : Fin n,
                  (canonicalGraph C).point v ∈ frontier exterior <->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_frontier_not_mem
      h)

/-- Chosen outer-component theorem from the exact cycle/frontier rows.

This is the shortest S2 reducer after the actual planar-topology theorem has
selected the exterior unit-distance cycle.  The rotation system and face orbit
are the checked boundary-following packages; the only mathematical input left
is the genuine exterior/frontier description of that selected cycle. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exterior_cycle_frontier_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            Exists fun exterior : Set PlanarInterface.Point =>
              (forall v : Fin n,
                (¬ Exists fun k : Fin B.length => B.vertex k = v) ->
                  (canonicalGraph C).point v ∉ exterior) /\
              (forall v : Fin n,
                (canonicalGraph C).point v ∈ frontier exterior <->
                  Exists fun k : Fin B.length => B.vertex k = v)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exterior_frontier_not_mem
    (fun C inputs => by
      rcases h C inputs with
        ⟨B, exterior, off_cycle_vertices_not_mem_exterior,
          frontier_iff_cycle_vertex⟩
      let R : UnitDistanceRotationSystem C :=
        UnitDistanceRotationSystem.ofBoundaryCycle B
      let rows : UnitDistanceCycleFaceSuccRows C R B :=
        UnitDistanceCycleFaceSuccRows.ofBoundaryCycle B
      let O : FaceDartOrbit C R :=
        FaceDartOrbit.ofBoundaryFaceSuccRows B rows
      refine ⟨R, O, exterior, ?_, ?_⟩
      · intro v hv
        exact off_cycle_vertices_not_mem_exterior v (by
          simpa [O, FaceDartOrbit.ofBoundaryFaceSuccRows] using hv)
      · intro v
        simpa [O, FaceDartOrbit.ofBoundaryFaceSuccRows] using
          frontier_iff_cycle_vertex v)

/-- Chosen outer-component theorem from the two actual frontier directions and
proof that non-orbit graph vertices lie outside the exterior. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exterior_frontier_rows_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (canonicalGraph C).point v ∈ frontier exterior ->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v) /\
                (forall k : Fin O.boundary.length,
                  (canonicalGraph C).point (O.boundary.vertex k) ∈
                    frontier exterior) /\
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ exterior)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_frontier_rows_not_mem
      h)

/-- Chosen outer-component theorem from positive orbit-frontier, negative
non-orbit not-frontier, and non-orbit outside-exterior rows. -/
def finitePlanarStraightLineOuterComponentTheorem_of_exterior_orbit_frontier_not_frontier_not_mem
    (h :
      forall {n : Nat} (C : _root_.UDConfig n),
        FinitePlanarOuterComponentInputs C ->
          Exists fun R : UnitDistanceRotationSystem C =>
            Exists fun O : FaceDartOrbit C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall k : Fin O.boundary.length,
                  (canonicalGraph C).point (O.boundary.vertex k) ∈
                    frontier exterior) /\
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ frontier exterior) /\
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (canonicalGraph C).point v ∉ exterior)) :
    FinitePlanarStraightLineOuterComponentTheorem :=
  finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem
    (finitePlanarStraightLineExteriorDartOrbitTheorem_of_exterior_orbit_frontier_not_frontier_not_mem
      h)

end

end JordanTopologyExteriorEnclosure
end Swanepoel
end ErdosProblems1066
