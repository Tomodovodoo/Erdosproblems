import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.BoundaryWalkClassificationConcrete
import ErdosProblems1066.Swanepoel.JordanBoundarySourceInhabitationW22
import ErdosProblems1066.Swanepoel.TopologyNamedDependencyInhabitationW22

set_option autoImplicit false

/-!
# W23 concrete Jordan-boundary family reductions

This file records the direct constructors between the concrete W22
Jordan-boundary source families, the W21 named topology dependency, and the
actual topology-arc input family.  The boundary-walk lane remains explicitly
conditioned on the W16 triangle-run theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanBoundaryFamiliesConcreteW23

open BoundaryArcFiniteWalkConstructionW16

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundarySourceInhabitationW22.CanonicalGraph C

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundarySourceInhabitationW22.ConcreteTopologyFacts C

abbrev ConcreteBoundaryWalkClassification
    (C : _root_.UDConfig n) (T : ConcreteTopologyFacts C) :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs T.toCore

abbrev W21TriangleRunSourceFamily : Type (u + 1) :=
  JordanBoundarySourceInhabitationW22.TriangleRunSourceFamily.{u}

abbrev W21ExtractionSourceFamily : Type (u + 1) :=
  JordanBoundarySourceInhabitationW22.ExtractionSourceFamily.{u}

abbrev ConcreteTriangleRunSourceFamily : Type (u + 1) :=
  JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryTriangleRunSourceFamily.{u}

abbrev ConcreteExtractionSourceFamily : Type (u + 1) :=
  JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryExtractionSourceFamily.{u}

abbrev ConcreteBudgetSourceFamily : Type (u + 1) :=
  JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryBudgetSourceFamily.{u}

abbrev BoundaryWalkBudgetSourceFamily : Type (u + 1) :=
  JordanBoundarySourceInhabitationW22.ConcreteBoundaryWalkBudgetSourceFamily.{u}

abbrev NamedDependency : Type (u + 1) :=
  TopologyNamedDependencyInhabitationW22.W21NamedDependency.{u}

abbrev ActualInputsFamily : Type (u + 1) :=
  TopologyNamedDependencyInhabitationW22.W21ActualInputsFamily.{u}

def concreteTopologyFactsEquivMissingTopologyFacts
    (C : _root_.UDConfig n) :
    Equiv (ConcreteTopologyFacts C)
      (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) where
  toFun := fun T => T.toMissingTopologyFacts
  invFun := JordanTopologyFactsConcrete.TopologyFacts.ofMissingTopologyFacts
  left_inv := by
    intro T
    exact
      JordanTopologyFactsConcrete.TopologyFacts.ofMissingTopologyFacts_toMissingTopologyFacts
        T
  right_inv := by
    intro T
    exact
      JordanTopologyFactsConcrete.TopologyFacts.toMissingTopologyFacts_ofMissingTopologyFacts
        T

def concreteTopologyFactsEquivExtractionData
    (C : _root_.UDConfig n) :
    Equiv (ConcreteTopologyFacts C)
      (JordanBoundaryExtraction.Data.{0} (CanonicalGraph C)) where
  toFun := fun T => T.toExtractionData
  invFun := JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
  left_inv := by
    intro T
    exact
      JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData
        T
  right_inv := by
    intro T
    exact
      JordanTopologyFactsConcrete.TopologyFacts.toExtractionData_ofExtractionData
        T

def concreteTopologyFactsEquivOuterBoundaryCore
    (C : _root_.UDConfig n) :
    Equiv (ConcreteTopologyFacts C)
      (OuterBoundaryCore.{0} (CanonicalGraph C)) where
  toFun := fun T => T.toCore
  invFun := JordanTopologyFactsConcrete.TopologyFacts.ofCore
  left_inv := by
    intro T
    exact JordanTopologyFactsConcrete.TopologyFacts.ofCore_toCore T
  right_inv := by
    intro P
    exact JordanTopologyFactsConcrete.TopologyFacts.toCore_ofCore P

theorem concreteTopologyFacts_nonempty_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    Nonempty (ConcreteTopologyFacts C) <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T => exact Nonempty.intro T.toMissingTopologyFacts
  case mpr =>
    intro h
    cases h with
    | intro T =>
        exact Nonempty.intro
          (JordanTopologyFactsConcrete.TopologyFacts.ofMissingTopologyFacts T)

theorem concreteTopologyFacts_nonempty_iff_extractionData
    (C : _root_.UDConfig n) :
    Nonempty (ConcreteTopologyFacts C) <->
      Nonempty (JordanBoundaryExtraction.Data.{0} (CanonicalGraph C)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T => exact Nonempty.intro T.toExtractionData
  case mpr =>
    intro h
    cases h with
    | intro T =>
        exact Nonempty.intro
          (JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData T)

theorem concreteTopologyFacts_nonempty_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    Nonempty (ConcreteTopologyFacts C) <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T => exact Nonempty.intro T.toCore
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro
          (JordanTopologyFactsConcrete.TopologyFacts.ofCore P)

def w21TriangleRunSourceFamilyOfConcrete
    (F : ConcreteTriangleRunSourceFamily.{u}) :
    W21TriangleRunSourceFamily.{u} :=
  F.toW21SourceFamily

def w21ExtractionSourceFamilyOfConcrete
    (F : ConcreteExtractionSourceFamily.{u}) :
    W21ExtractionSourceFamily.{u} :=
  F.toW21SourceFamily

def concreteTriangleRunSourceFamilyOfW21
    (F : W21TriangleRunSourceFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  JordanBoundarySourceInhabitationW22.concreteTriangleRunSourceFamilyOfW21 F

def concreteExtractionSourceFamilyOfW21
    (F : W21ExtractionSourceFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  JordanBoundarySourceInhabitationW22.concreteExtractionSourceFamilyOfW21 F

def concreteExtractionSourceFamilyOfConcreteTriangleRunSourceFamily
    (F : ConcreteTriangleRunSourceFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  F.toExtractionSourceFamily

def concreteTriangleRunSourceFamilyOfConcreteExtractionSourceFamily
    (F : ConcreteExtractionSourceFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  F.toTriangleRunSourceFamily

def namedDependencyOfConcreteTriangleRunSourceFamily
    (F : ConcreteTriangleRunSourceFamily.{u}) :
    NamedDependency.{u} :=
  TopologyNamedDependencyInhabitationW22.namedDependencyOfJordanTriangleRunSourceFamily
    F.toW21SourceFamily

def namedDependencyOfConcreteExtractionSourceFamily
    (F : ConcreteExtractionSourceFamily.{u}) :
    NamedDependency.{u} :=
  TopologyNamedDependencyInhabitationW22.namedDependencyOfJordanExtractionSourceFamily
    F.toW21SourceFamily

def concreteTriangleRunSourceFamilyOfNamedDependency
    (D : NamedDependency.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  concreteTriangleRunSourceFamilyOfW21
    (TopologyNamedDependencyInhabitationW22.jordanTriangleRunSourceFamilyOfNamedDependency
      D)

def concreteExtractionSourceFamilyOfNamedDependency
    (D : NamedDependency.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  concreteExtractionSourceFamilyOfW21
    (TopologyNamedDependencyInhabitationW22.jordanExtractionSourceFamilyOfNamedDependency
      D)

def actualInputsFamilyOfConcreteTriangleRunSourceFamily
    (F : ConcreteTriangleRunSourceFamily.{u}) :
    ActualInputsFamily.{u} :=
  TopologyNamedDependencyInhabitationW22.actualInputsFamilyOfJordanTriangleRunSourceFamily
    F.toW21SourceFamily

def actualInputsFamilyOfConcreteExtractionSourceFamily
    (F : ConcreteExtractionSourceFamily.{u}) :
    ActualInputsFamily.{u} :=
  TopologyNamedDependencyInhabitationW22.actualInputsFamilyOfJordanExtractionSourceFamily
    F.toW21SourceFamily

def concreteTriangleRunSourceFamilyOfActualInputsFamily
    (F : ActualInputsFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  concreteTriangleRunSourceFamilyOfW21
    (TopologyNamedDependencyInhabitationW22.jordanTriangleRunSourceFamilyOfActualInputsFamily
      F)

def concreteExtractionSourceFamilyOfActualInputsFamily
    (F : ActualInputsFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  concreteExtractionSourceFamilyOfW21
    (TopologyNamedDependencyInhabitationW22.jordanExtractionSourceFamilyOfActualInputsFamily
      F)

theorem concreteTriangleRunSourceFamily_nonempty_iff_concreteExtractionSourceFamily :
    Nonempty ConcreteTriangleRunSourceFamily.{u} <->
      Nonempty ConcreteExtractionSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (concreteExtractionSourceFamilyOfConcreteTriangleRunSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (concreteTriangleRunSourceFamilyOfConcreteExtractionSourceFamily F)

theorem concreteTriangleRunSourceFamily_nonempty_iff_namedDependency :
    Nonempty ConcreteTriangleRunSourceFamily.{u} <->
      Nonempty NamedDependency.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (namedDependencyOfConcreteTriangleRunSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (concreteTriangleRunSourceFamilyOfNamedDependency D)

theorem concreteExtractionSourceFamily_nonempty_iff_namedDependency :
    Nonempty ConcreteExtractionSourceFamily.{u} <->
      Nonempty NamedDependency.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (namedDependencyOfConcreteExtractionSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (concreteExtractionSourceFamilyOfNamedDependency D)

theorem concreteTriangleRunSourceFamily_nonempty_iff_actualInputsFamily :
    Nonempty ConcreteTriangleRunSourceFamily.{u} <->
      Nonempty ActualInputsFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (actualInputsFamilyOfConcreteTriangleRunSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (concreteTriangleRunSourceFamilyOfActualInputsFamily F)

theorem concreteExtractionSourceFamily_nonempty_iff_actualInputsFamily :
    Nonempty ConcreteExtractionSourceFamily.{u} <->
      Nonempty ActualInputsFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (actualInputsFamilyOfConcreteExtractionSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro
          (concreteExtractionSourceFamilyOfActualInputsFamily F)

def concreteTriangleRunSourceFamilyOfBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteBudgetSourceFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  F.toTriangleRunSourceFamily Hrun

def concreteExtractionSourceFamilyOfBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteBudgetSourceFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  F.toExtractionSourceFamily Hrun

def concreteBudgetSourceFamilyOfBoundaryWalkBudgetSourceFamily
    (F : BoundaryWalkBudgetSourceFamily.{u}) :
    ConcreteBudgetSourceFamily.{u} :=
  F.toBudgetSourceFamily

def concreteTriangleRunSourceFamilyOfBoundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : BoundaryWalkBudgetSourceFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} :=
  concreteTriangleRunSourceFamilyOfBudgetSourceFamily Hrun
    F.toBudgetSourceFamily

def concreteExtractionSourceFamilyOfBoundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : BoundaryWalkBudgetSourceFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} :=
  concreteExtractionSourceFamilyOfBudgetSourceFamily Hrun
    F.toBudgetSourceFamily

def namedDependencyOfBoundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : BoundaryWalkBudgetSourceFamily.{u}) :
    NamedDependency.{u} :=
  namedDependencyOfConcreteTriangleRunSourceFamily
    (concreteTriangleRunSourceFamilyOfBoundaryWalkBudgetSourceFamily Hrun F)

def actualInputsFamilyOfBoundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : BoundaryWalkBudgetSourceFamily.{u}) :
    ActualInputsFamily.{u} :=
  actualInputsFamilyOfConcreteExtractionSourceFamily
    (concreteExtractionSourceFamilyOfBoundaryWalkBudgetSourceFamily Hrun F)

theorem concreteTriangleRunSourceFamily_nonempty_of_boundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u}) :
    Nonempty BoundaryWalkBudgetSourceFamily.{u} ->
      Nonempty ConcreteTriangleRunSourceFamily.{u} := by
  intro h
  cases h with
  | intro F =>
      exact Nonempty.intro
        (concreteTriangleRunSourceFamilyOfBoundaryWalkBudgetSourceFamily Hrun
          F)

theorem concreteExtractionSourceFamily_nonempty_of_boundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u}) :
    Nonempty BoundaryWalkBudgetSourceFamily.{u} ->
      Nonempty ConcreteExtractionSourceFamily.{u} := by
  intro h
  cases h with
  | intro F =>
      exact Nonempty.intro
        (concreteExtractionSourceFamilyOfBoundaryWalkBudgetSourceFamily Hrun
          F)

theorem namedDependency_nonempty_of_boundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u}) :
    Nonempty BoundaryWalkBudgetSourceFamily.{u} ->
      Nonempty NamedDependency.{u} := by
  intro h
  cases h with
  | intro F =>
      exact Nonempty.intro
        (namedDependencyOfBoundaryWalkBudgetSourceFamily Hrun F)

theorem actualInputsFamily_nonempty_of_boundaryWalkBudgetSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u}) :
    Nonempty BoundaryWalkBudgetSourceFamily.{u} ->
      Nonempty ActualInputsFamily.{u} := by
  intro h
  cases h with
  | intro F =>
      exact Nonempty.intro
        (actualInputsFamilyOfBoundaryWalkBudgetSourceFamily Hrun F)

end

end JordanBoundaryFamiliesConcreteW23
end Swanepoel
end ErdosProblems1066
