import ErdosProblems1066.Swanepoel.BoundaryWalkBridge
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete

set_option autoImplicit false

/-!
# Outer-boundary core construction frontier

This file records the honest construction frontier for `OuterBoundaryCore`.

The canonical unit-distance graph already supplies noncrossing unit edges.  As
soon as a cyclic boundary walk is supplied, the project can certify the
corresponding Mathlib polygon, unit boundary edges, and separated-edge
noncrossing witness.  What is not constructed here is the topological
face/Jordan layer: finite faces, a selected outer face, and enclosure
predicates for that face remain explicit data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryCoreConstruction

open FaceReduction
open OuterBoundaryInterface

universe u

noncomputable section

variable {n : Nat}

/-! ## Certified boundary cycles -/

/--
The strictly smaller certified package available once a boundary cycle has been
named in a canonical unit-distance graph.

No face or enclosure is stored here.  The separated-edge noncrossing part of
the simple-polygon witness is derived from the canonical unit-edge noncrossing
theorem.
-/
structure BoundaryCycleCertificate
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  cycle : BoundaryCycle G

namespace BoundaryCycleCertificate

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Package an explicitly supplied boundary cycle. -/
def ofCycle (C : BoundaryCycle G) : BoundaryCycleCertificate G where
  cycle := C

@[simp]
theorem ofCycle_cycle (C : BoundaryCycle G) :
    (ofCycle C).cycle = C :=
  rfl

/-- The Mathlib polygon attached to the certified boundary cycle. -/
def polygon (K : BoundaryCycleCertificate G) :
    Polygon PlanarInterface.Point K.cycle.length :=
  K.cycle.toPolygon

/-- The derived simple-polygon witness for separated boundary edges. -/
def simplePolygon (K : BoundaryCycleCertificate G) :
    SimplePolygon G K.cycle :=
  OuterBoundaryReduction.BoundaryCycle.toSimplePolygon K.cycle

/-- The certified boundary vertices are injectively indexed. -/
theorem vertices_injective (K : BoundaryCycleCertificate G) :
    Function.Injective K.cycle.vertex :=
  K.simplePolygon.vertices_injective

/-- The canonical graph supplies the noncrossing theorem used by the certificate. -/
theorem pairwiseNoncrossing (_K : BoundaryCycleCertificate G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  G.pairwiseNoncrossing

/-- Each certified boundary edge is a graph edge. -/
theorem edge_adjacent (K : BoundaryCycleCertificate G)
    (k : Fin K.cycle.length) :
    G.Adj (K.cycle.edge k).1 (K.cycle.edge k).2 :=
  K.cycle.edge_adjacent k

/-- Each certified boundary edge is a unit-distance adjacency. -/
theorem edge_unitDistanceAdj (K : BoundaryCycleCertificate G)
    (k : Fin K.cycle.length) :
    GraphBridge.UnitDistanceAdj G.config
      (K.cycle.edge k).1 (K.cycle.edge k).2 :=
  K.cycle.edge_unitDistanceAdj k

/-- Each certified boundary edge has Euclidean length one. -/
theorem edge_dist_eq_one (K : BoundaryCycleCertificate G)
    (k : Fin K.cycle.length) :
    Geometry.Distance.eucDist
        (G.point (K.cycle.edge k).1)
        (G.point (K.cycle.edge k).2) = 1 :=
  K.cycle.edge_dist_eq_one k

/-- The Mathlib polygon edge is the affine segment between consecutive
boundary points. -/
theorem polygon_edgeSet (K : BoundaryCycleCertificate G)
    (k : Fin K.cycle.length) :
    K.polygon.edgeSet Real k =
      affineSegment Real (K.cycle.point k) (K.cycle.nextPoint k) := by
  simpa [polygon] using K.cycle.toPolygon_edgeSet k

/-- Separated certified boundary edges do not cross in their relative interiors. -/
theorem separated_edges_do_not_cross
    (K : BoundaryCycleCertificate G)
    {i j : Fin K.cycle.length}
    (hsep : CyclicEdgesSeparated K.cycle.length_pos i j) :
    Not (PlanarInterface.SegmentsCrossInterior
      (K.cycle.point i) (K.cycle.nextPoint i)
      (K.cycle.point j) (K.cycle.nextPoint j)) :=
  K.simplePolygon.separated_edges_do_not_cross' hsep

/-- Build the smaller certificate from selected outer-face data. -/
def ofOuterFaceData
    (D : JordanTopologyFactsConcrete.OuterFaceData G) :
    BoundaryCycleCertificate G where
  cycle := D.outerCycle

@[simp]
theorem ofOuterFaceData_cycle
    (D : JordanTopologyFactsConcrete.OuterFaceData G) :
    (ofOuterFaceData D).cycle = D.outerCycle :=
  rfl

/-- Build the smaller certificate from a full checked core. -/
def ofCore (P : OuterBoundaryCore G) :
    BoundaryCycleCertificate G where
  cycle := P.outerCycle

@[simp]
theorem ofCore_cycle (P : OuterBoundaryCore G) :
    (ofCore P).cycle = P.outerCycle :=
  rfl

end BoundaryCycleCertificate

/-! ## Exact remaining data for the full core -/

/-- The selected-face part of the remaining topology input. -/
abbrev OuterFaceData
    (G : CanonicalStraightLineUnitDistanceGraph n) : Type (u + 1) :=
  JordanTopologyFactsConcrete.OuterFaceData.{u} G

/-- The enclosure part of the remaining topology input, over a selected face. -/
abbrev EnclosureData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (D : OuterFaceData.{u} G) : Type :=
  JordanTopologyFactsConcrete.EnclosureData D

namespace OuterFaceData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The smaller certified boundary-cycle package obtained from selected-face data. -/
def boundaryCertificate (D : OuterFaceData.{u} G) :
    BoundaryCycleCertificate G :=
  BoundaryCycleCertificate.ofOuterFaceData D

@[simp]
theorem boundaryCertificate_cycle (D : OuterFaceData.{u} G) :
    D.boundaryCertificate.cycle = D.outerCycle :=
  rfl

/-- Selected-face data is enough for the derived simple-polygon witness. -/
def certifiedSimplePolygon (D : OuterFaceData.{u} G) :
    SimplePolygon G D.outerCycle :=
  D.outerSimplePolygon

/-- Selected-face data carries no extra noncrossing assumption; it uses the
canonical graph theorem. -/
theorem pairwiseNoncrossing (D : OuterFaceData.{u} G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  JordanTopologyFactsConcrete.OuterFaceData.pairwiseNoncrossing D

end OuterFaceData

namespace EnclosureData

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {D : OuterFaceData.{u} G}

/-- Selected-face data plus enclosure predicates assemble to the checked core. -/
def toCore (E : EnclosureData D) :
    OuterBoundaryCore G :=
  JordanTopologyFactsConcrete.EnclosureData.toCore E

@[simp]
theorem toCore_faceBoundary (E : EnclosureData D) :
    (toCore E).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace (E : EnclosureData D) :
    (toCore E).outerFace = D.outerFace :=
  rfl

@[simp]
theorem toCore_outerEnclosure (E : EnclosureData D) :
    (toCore E).outerEnclosure = E.outerEnclosure :=
  rfl

/-- Enclosure data still retains the smaller certified boundary package. -/
def boundaryCertificate (_E : EnclosureData D) :
    BoundaryCycleCertificate G :=
  D.boundaryCertificate

@[simp]
theorem boundaryCertificate_cycle (E : EnclosureData D) :
    E.boundaryCertificate.cycle = D.outerCycle :=
  rfl

end EnclosureData

/--
Precise data requirement for constructing an `OuterBoundaryCore` for a
canonical graph: selected face-boundary data, followed by enclosure predicates
for that selected face.
-/
def CoreTopologyRequirements
    (G : CanonicalStraightLineUnitDistanceGraph n) : Prop :=
  Exists fun D : OuterFaceData.{u} G => Nonempty (EnclosureData D)

/-- The explicit split requirements are equivalent to a checked core. -/
theorem coreTopologyRequirements_iff_outerBoundaryCore
    (G : CanonicalStraightLineUnitDistanceGraph n) :
    CoreTopologyRequirements.{u} G <->
      Nonempty (OuterBoundaryCore.{u} G) := by
  constructor
  · rintro ⟨D, ⟨E⟩⟩
    exact ⟨EnclosureData.toCore E⟩
  · rintro ⟨P⟩
    exact
      ⟨JordanTopologyFactsConcrete.OuterFaceData.ofCore P,
        ⟨JordanTopologyFactsConcrete.EnclosureData.ofCore P⟩⟩

/-- A checked core always has the smaller certified boundary-cycle package. -/
theorem boundaryCycleCertificate_of_core
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) :
    Nonempty (BoundaryCycleCertificate G) :=
  ⟨BoundaryCycleCertificate.ofCore P⟩

/-! ## Concrete `UDConfig` target -/

/-- The canonical graph attached to a concrete unit-distance configuration. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcrete.canonicalGraph C

/-- The canonical graph over a concrete configuration has noncrossing unit edges. -/
theorem canonicalGraph_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  (canonicalGraph C).pairwiseNoncrossing

/--
Concrete remaining topology target for a `UDConfig`.

This is intentionally a proposition rather than a supplied witness.  It says
exactly that the selected face-boundary data and enclosure predicates required
above exist for the canonical graph of `C`.
-/
def RemainingCoreTopologyRequirements (C : _root_.UDConfig n) : Prop :=
  CoreTopologyRequirements.{0} (canonicalGraph C)

/-- The concrete remaining target is equivalent to producing an
`OuterBoundaryCore` for the canonical graph of `C`. -/
theorem remainingCoreTopologyRequirements_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) :=
  coreTopologyRequirements_iff_outerBoundaryCore (canonicalGraph C)

/-- Compatibility with the existing concrete Jordan-boundary frontier. -/
theorem remainingCoreTopologyRequirements_iff_jordanBoundaryConcrete
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem C := by
  constructor
  · intro h
    have hcore :=
      JordanBoundaryConcrete.MissingTopologyFacts.remainingTopologyTheorem_iff_outerBoundaryCore C
    exact
      hcore.2
        ((remainingCoreTopologyRequirements_iff_outerBoundaryCore C).1 h)
  · intro h
    have hcore :=
      JordanBoundaryConcrete.MissingTopologyFacts.remainingTopologyTheorem_iff_outerBoundaryCore C
    exact
      (remainingCoreTopologyRequirements_iff_outerBoundaryCore C).2
        (hcore.1 h)

/--
Global paper-facing construction target left open by the current topology
stack.  Proving this would honestly construct the full core for every
configuration; this file does not assume it.
-/
def GlobalOuterBoundaryCoreConstructionTarget : Prop :=
  forall (n : Nat), forall C : _root_.UDConfig n,
    RemainingCoreTopologyRequirements C

end

end OuterBoundaryCoreConstruction
end Swanepoel
end ErdosProblems1066
