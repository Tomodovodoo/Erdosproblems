import ErdosProblems1066.Swanepoel.BoundaryTopologySourceW21
import ErdosProblems1066.Swanepoel.TopologySourceInhabitationW21
import ErdosProblems1066.Swanepoel.JordanBoundaryExtraction
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17
import ErdosProblems1066.Swanepoel.TopologyToBoundaryArcW14
import ErdosProblems1066.Swanepoel.TopologyArcClosureW19

set_option autoImplicit false

/-!
# W22 named topology-arc dependency reduction

This file composes the checked W21 reductions:

* `TopologySourceInhabitationW21` identifies the W19 source family with the
  named topology-arc dependency and with the actual-input family.
* `BoundaryTopologySourceW21` identifies that W19 source family with Jordan
  boundary extraction data plus either a W14 boundary-arc extraction or a W16
  thirteen-edge triangle run.

No new Jordan theorem, boundary-arc theorem, or public facade wrapper is
introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyNamedDependencyInhabitationW22

universe u

noncomputable section

variable {n : Nat}

abbrev W21NamedRowDependency
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  TopologySourceInhabitationW21.NamedTopologyArcRowDependency.{u} C hmin

abbrev W21NamedDependency : Type (u + 1) :=
  TopologySourceInhabitationW21.NamedTopologyArcDependency.{u}

abbrev W21ActualInputsFamily : Type (u + 1) :=
  TopologySourceInhabitationW21.ActualInputsFamily.{u}

abbrev W19SourceFamily : Type (u + 1) :=
  TopologySourceInhabitationW21.SourceFamily.{u}

abbrev JordanTriangleRunSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryTriangleRunSourceFields.{u}
    C hmin

abbrev JordanExtractionSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryExtractionSourceFields.{u}
    C hmin

abbrev JordanTriangleRunSourceFamily : Type (u + 1) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u}

abbrev JordanExtractionSourceFamily : Type (u + 1) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryExtractionSourceFamily.{u}

/-! ## Row-level projections -/

def namedRowDependencyOfJordanTriangleRunSourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : JordanTriangleRunSourceFields.{u} C hmin) :
    W21NamedRowDependency.{u} C hmin :=
  TopologySourceInhabitationW21.SourceFields.toNamedDependency
    P.toW19TopologyArcSourceFields

def namedRowDependencyOfJordanExtractionSourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : JordanExtractionSourceFields.{u} C hmin) :
    W21NamedRowDependency.{u} C hmin :=
  TopologySourceInhabitationW21.SourceFields.toNamedDependency
    P.toW19TopologyArcSourceFields

@[simp]
theorem namedRowDependencyOfJordanTriangleRunSourceFields_topology
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : JordanTriangleRunSourceFields.{u} C hmin) :
    (namedRowDependencyOfJordanTriangleRunSourceFields P).topology =
      BoundaryTopologySourceW21.topologyOfJordanExtraction P.jordan :=
  rfl

@[simp]
theorem namedRowDependencyOfJordanTriangleRunSourceFields_triangleRun
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : JordanTriangleRunSourceFields.{u} C hmin) :
    (namedRowDependencyOfJordanTriangleRunSourceFields P).triangleRun =
      P.triangleRun :=
  rfl

@[simp]
theorem namedRowDependencyOfJordanExtractionSourceFields_topology
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : JordanExtractionSourceFields.{u} C hmin) :
    (namedRowDependencyOfJordanExtractionSourceFields P).topology =
      BoundaryTopologySourceW21.topologyOfJordanExtraction P.jordan :=
  rfl

@[simp]
theorem namedRowDependencyOfJordanExtractionSourceFields_triangleRun_pIndex
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : JordanExtractionSourceFields.{u} C hmin)
    (i : M8LabelsFromBoundaryInterface.M8BoundaryIndex) :
    (namedRowDependencyOfJordanExtractionSourceFields P).triangleRun.pIndex i =
      P.arcExtraction.boundaryArc.pIndex i :=
  rfl

/-! ## Family-level conversions -/

def sourceFamilyOfJordanTriangleRunSourceFamily
    (F : JordanTriangleRunSourceFamily.{u}) :
    W19SourceFamily.{u} :=
  F.toW19TopologyArcSourceFamily

def sourceFamilyOfJordanExtractionSourceFamily
    (F : JordanExtractionSourceFamily.{u}) :
    W19SourceFamily.{u} :=
  F.toW19TopologyArcSourceFamily

def jordanTriangleRunSourceFamilyOfSourceFamily
    (F : W19SourceFamily.{u}) :
    JordanTriangleRunSourceFamily.{u} where
  row := fun C hmin =>
    BoundaryTopologySourceW21.jordanBoundaryTriangleRunSourceFieldsOfW19
      (F.row C hmin)

def jordanExtractionSourceFamilyOfSourceFamily
    (F : W19SourceFamily.{u}) :
    JordanExtractionSourceFamily.{u} where
  row := fun C hmin =>
    BoundaryTopologySourceW21.jordanBoundaryExtractionSourceFieldsOfW19
      (F.row C hmin)

def namedDependencyOfJordanTriangleRunSourceFamily
    (F : JordanTriangleRunSourceFamily.{u}) :
    W21NamedDependency.{u} :=
  TopologySourceInhabitationW21.SourceFamily.toNamedDependency
    (sourceFamilyOfJordanTriangleRunSourceFamily F)

def namedDependencyOfJordanExtractionSourceFamily
    (F : JordanExtractionSourceFamily.{u}) :
    W21NamedDependency.{u} :=
  TopologySourceInhabitationW21.SourceFamily.toNamedDependency
    (sourceFamilyOfJordanExtractionSourceFamily F)

def actualInputsFamilyOfJordanTriangleRunSourceFamily
    (F : JordanTriangleRunSourceFamily.{u}) :
    W21ActualInputsFamily.{u} :=
  (namedDependencyOfJordanTriangleRunSourceFamily F).toActualInputsFamily

def actualInputsFamilyOfJordanExtractionSourceFamily
    (F : JordanExtractionSourceFamily.{u}) :
    W21ActualInputsFamily.{u} :=
  (namedDependencyOfJordanExtractionSourceFamily F).toActualInputsFamily

def jordanTriangleRunSourceFamilyOfNamedDependency
    (D : W21NamedDependency.{u}) :
    JordanTriangleRunSourceFamily.{u} :=
  jordanTriangleRunSourceFamilyOfSourceFamily D.toSourceFamily

def jordanExtractionSourceFamilyOfNamedDependency
    (D : W21NamedDependency.{u}) :
    JordanExtractionSourceFamily.{u} :=
  jordanExtractionSourceFamilyOfSourceFamily D.toSourceFamily

def jordanTriangleRunSourceFamilyOfActualInputsFamily
    (F : W21ActualInputsFamily.{u}) :
    JordanTriangleRunSourceFamily.{u} :=
  jordanTriangleRunSourceFamilyOfSourceFamily
    (TopologySourceInhabitationW21.sourceFamilyOfActualInputsFamily F)

def jordanExtractionSourceFamilyOfActualInputsFamily
    (F : W21ActualInputsFamily.{u}) :
    JordanExtractionSourceFamily.{u} :=
  jordanExtractionSourceFamilyOfSourceFamily
    (TopologySourceInhabitationW21.sourceFamilyOfActualInputsFamily F)

/-! ## Exact nonempty reductions -/

theorem jordanTriangleRunSourceFamily_nonempty_iff_sourceFamily :
    Nonempty JordanTriangleRunSourceFamily.{u} <->
      Nonempty W19SourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (sourceFamilyOfJordanTriangleRunSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (jordanTriangleRunSourceFamilyOfSourceFamily F)

theorem jordanExtractionSourceFamily_nonempty_iff_sourceFamily :
    Nonempty JordanExtractionSourceFamily.{u} <->
      Nonempty W19SourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (sourceFamilyOfJordanExtractionSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (jordanExtractionSourceFamilyOfSourceFamily F)

theorem namedDependency_nonempty_iff_jordanTriangleRunSourceFamily :
    Nonempty W21NamedDependency.{u} <->
      Nonempty JordanTriangleRunSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (jordanTriangleRunSourceFamilyOfNamedDependency D)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (namedDependencyOfJordanTriangleRunSourceFamily F)

theorem namedDependency_nonempty_iff_jordanExtractionSourceFamily :
    Nonempty W21NamedDependency.{u} <->
      Nonempty JordanExtractionSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (jordanExtractionSourceFamilyOfNamedDependency D)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (namedDependencyOfJordanExtractionSourceFamily F)

theorem actualInputsFamily_nonempty_iff_jordanTriangleRunSourceFamily :
    Nonempty W21ActualInputsFamily.{u} <->
      Nonempty JordanTriangleRunSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (jordanTriangleRunSourceFamilyOfActualInputsFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (actualInputsFamilyOfJordanTriangleRunSourceFamily F)

theorem actualInputsFamily_nonempty_iff_jordanExtractionSourceFamily :
    Nonempty W21ActualInputsFamily.{u} <->
      Nonempty JordanExtractionSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (jordanExtractionSourceFamilyOfActualInputsFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (actualInputsFamilyOfJordanExtractionSourceFamily F)

theorem namedDependency_nonempty_of_jordanTriangleRunSourceFamily
    (F : JordanTriangleRunSourceFamily.{u}) :
    Nonempty W21NamedDependency.{u} :=
  Nonempty.intro (namedDependencyOfJordanTriangleRunSourceFamily F)

theorem actualInputsFamily_nonempty_of_jordanTriangleRunSourceFamily
    (F : JordanTriangleRunSourceFamily.{u}) :
    Nonempty W21ActualInputsFamily.{u} :=
  Nonempty.intro (actualInputsFamilyOfJordanTriangleRunSourceFamily F)

theorem namedDependency_nonempty_of_jordanExtractionSourceFamily
    (F : JordanExtractionSourceFamily.{u}) :
    Nonempty W21NamedDependency.{u} :=
  Nonempty.intro (namedDependencyOfJordanExtractionSourceFamily F)

theorem actualInputsFamily_nonempty_of_jordanExtractionSourceFamily
    (F : JordanExtractionSourceFamily.{u}) :
    Nonempty W21ActualInputsFamily.{u} :=
  Nonempty.intro (actualInputsFamilyOfJordanExtractionSourceFamily F)

end

end TopologyNamedDependencyInhabitationW22
end Swanepoel
end ErdosProblems1066
