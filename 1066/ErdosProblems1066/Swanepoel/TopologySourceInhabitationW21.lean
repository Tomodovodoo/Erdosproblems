import ErdosProblems1066.Swanepoel.TopologyArcClosureW19
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17

set_option autoImplicit false

/-!
# W21-SW2 topology-source inhabitation audit

The existing W14--W20 topology/boundary layers do not expose an unconditional
inhabitant of the W19 topology-arc source family.  This file records the exact
remaining dependency: the named topology row fields are equivalent to the W19
source row, and the source-family obligation is equivalent to the actual-input
family obligation.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologySourceInhabitationW21

open TopologyArcClosureW19

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  TopologyArcClosureW19.CanonicalGraph C

abbrev SourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u} C hmin

abbrev SourceFamily : Type (u + 1) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u}

abbrev ActualInputs (C : _root_.UDConfig n) :=
  TopologyArcClosureW19.ActualTopologyArcInputs.{u} C

abbrev ActualInputsFamily : Type (u + 1) :=
  TopologyArcClosureW19.MinimalFailureActualTopologyArcInputsFamily.{u}

/-- The exact named fields needed in one minimal-failure row. -/
structure NamedTopologyArcRowDependency
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  topology : ExactOuterBoundaryTopologyW13.TopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  triangleRun :
    BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace NamedTopologyArcRowDependency

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def toSourceFields
    (P : NamedTopologyArcRowDependency.{u} C hmin) :
    SourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

@[simp]
theorem toSourceFields_topology
    (P : NamedTopologyArcRowDependency.{u} C hmin) :
    P.toSourceFields.topology = P.topology :=
  rfl

@[simp]
theorem toSourceFields_triangleRun
    (P : NamedTopologyArcRowDependency.{u} C hmin) :
    P.toSourceFields.triangleRun = P.triangleRun :=
  rfl

end NamedTopologyArcRowDependency

namespace SourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def toNamedDependency
    (P : SourceFields.{u} C hmin) :
    NamedTopologyArcRowDependency.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

@[simp]
theorem toNamedDependency_topology
    (P : SourceFields.{u} C hmin) :
    P.toNamedDependency.topology = P.topology :=
  rfl

@[simp]
theorem toNamedDependency_triangleRun
    (P : SourceFields.{u} C hmin) :
    P.toNamedDependency.triangleRun = P.triangleRun :=
  rfl

end SourceFields

/-- The W19 source row is just the named row dependency, up to repackaging. -/
def sourceFieldsEquivNamedDependency
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Equiv (SourceFields.{u} C hmin)
      (NamedTopologyArcRowDependency.{u} C hmin) where
  toFun := SourceFields.toNamedDependency
  invFun := NamedTopologyArcRowDependency.toSourceFields
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro P
    cases P
    rfl

theorem sourceFields_nonempty_iff_namedDependency
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty (SourceFields.{u} C hmin) <->
      Nonempty (NamedTopologyArcRowDependency.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P => exact Nonempty.intro P.toNamedDependency
  case mpr =>
    intro h
    cases h with
    | intro P => exact Nonempty.intro P.toSourceFields

/-- One actual topology-arc input recovers the W19 source row: the triangular
run is selected from its boundary-arc extraction fields. -/
def sourceFieldsOfActualInputs
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (A : ActualInputs.{u} C) :
    SourceFields.{u} C hmin where
  topology := A.topology
  outerAngleBounds := A.outerAngleBounds
  Subpolygon := A.Subpolygon
  subpolygonData := A.subpolygonData
  longArc := A.longArc
  triangleRun := TriangleRunSelectorW17.TopologyBoundaryArcFields.triangleRun A

@[simp]
theorem sourceFieldsOfActualInputs_topology
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (A : ActualInputs.{u} C) :
    (sourceFieldsOfActualInputs (hmin := hmin) A).topology = A.topology :=
  rfl

theorem sourceFields_nonempty_iff_actualInputs
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty (SourceFields.{u} C hmin) <-> Nonempty (ActualInputs.{u} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P => exact Nonempty.intro P.toActualTopologyArcInputs
  case mpr =>
    intro h
    cases h with
    | intro A => exact Nonempty.intro (sourceFieldsOfActualInputs (hmin := hmin) A)

/-- Rowwise named dependencies for every minimal failure. -/
structure NamedTopologyArcDependency : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        NamedTopologyArcRowDependency.{u} C hmin

namespace NamedTopologyArcDependency

def toSourceFamily
    (D : NamedTopologyArcDependency.{u}) :
    SourceFamily.{u} where
  row := fun C hmin => (D.row C hmin).toSourceFields

def toActualInputsFamily
    (D : NamedTopologyArcDependency.{u}) :
    ActualInputsFamily.{u} :=
  D.toSourceFamily.toActualTopologyArcInputsFamily

end NamedTopologyArcDependency

namespace SourceFamily

def toNamedDependency
    (F : SourceFamily.{u}) :
    NamedTopologyArcDependency.{u} where
  row := fun C hmin => SourceFields.toNamedDependency (F.row C hmin)

end SourceFamily

def sourceFamilyOfActualInputsFamily
    (F : ActualInputsFamily.{u}) :
    SourceFamily.{u} where
  row := fun C hmin => sourceFieldsOfActualInputs (hmin := hmin) (F.inputs C hmin)

@[simp]
theorem sourceFamilyOfActualInputsFamily_row_topology
    (F : ActualInputsFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ((sourceFamilyOfActualInputsFamily F).row C hmin).topology =
      (F.inputs C hmin).topology :=
  rfl

theorem sourceFamily_nonempty_iff_namedDependency :
    Nonempty SourceFamily.{u} <-> Nonempty NamedTopologyArcDependency.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F => exact Nonempty.intro (SourceFamily.toNamedDependency F)
  case mpr =>
    intro h
    cases h with
    | intro D => exact Nonempty.intro D.toSourceFamily

theorem sourceFamily_nonempty_iff_actualInputsFamily :
    Nonempty SourceFamily.{u} <-> Nonempty ActualInputsFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F => exact Nonempty.intro F.toActualTopologyArcInputsFamily
  case mpr =>
    intro h
    cases h with
    | intro F => exact Nonempty.intro (sourceFamilyOfActualInputsFamily F)

theorem actualInputsFamily_nonempty_iff_namedDependency :
    Nonempty ActualInputsFamily.{u} <->
      Nonempty NamedTopologyArcDependency.{u} := by
  exact Iff.trans sourceFamily_nonempty_iff_actualInputsFamily.symm
    sourceFamily_nonempty_iff_namedDependency

theorem actualInputsFamily_of_namedDependency
    (D : NamedTopologyArcDependency.{u}) :
    Nonempty ActualInputsFamily.{u} :=
  Nonempty.intro D.toActualInputsFamily

theorem sourceFamily_of_namedDependency
    (D : NamedTopologyArcDependency.{u}) :
    Nonempty SourceFamily.{u} :=
  Nonempty.intro D.toSourceFamily

end

end TopologySourceInhabitationW21
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW21TopologyArcDependency :=
  Swanepoel.TopologySourceInhabitationW21.NamedTopologyArcDependency

theorem swanepoelW21_actualInputsFamily_nonempty_iff_namedDependency :
    Nonempty
        Swanepoel.TopologySourceInhabitationW21.ActualInputsFamily.{u} <->
      Nonempty SwanepoelW21TopologyArcDependency.{u} :=
  Swanepoel.TopologySourceInhabitationW21.actualInputsFamily_nonempty_iff_namedDependency

end Verified
end ErdosProblems1066
