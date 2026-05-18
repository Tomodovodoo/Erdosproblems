import ErdosProblems1066.PachToth.GeneratedChainSourceFieldsInhabitationW22
import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.RemainingSeparationInhabitationW22

set_option autoImplicit false

/-!
# W23 concrete closure route for generated-chain source fields

This file pins the strongest concrete handoff at the actual
`GeneratedChainFamilyProducerW20.SourceFields` interface.  A concrete
value-matrix row package supplies:

* period-closure data through its concrete period-search record;
* reduced metric fields through the concrete value-matrix/remaining-separation
  route;
* the W19 input package as the exact projection of the constructed source
  fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedChainSourceFieldsConcreteClosureW23

open FiniteGraph

noncomputable section

abbrev SourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

/-- The concrete period-search component is already the W20 closure source
for the generated-chain family used by the value-matrix route. -/
def periodClosureSourceOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    PeriodClosureSourceW21.ClosureSource
      (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
        C.periodSearch) :=
  PeriodClosureSourceW21.sourceOfConcretePeriodSearchData C.periodSearch

/-- The remaining-separation projection carried by the concrete value-matrix
package. -/
def remainingSeparationOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    RemainingSeparationInhabitationW22.RemainingSeparationField
      C.toRoleHingedPeriodSearchFamily :=
  RemainingSeparationInhabitationW22.remainingSeparationOfConcreteValueMatrixFamily
    C

/-- Reduced metric fields from the concrete value-matrix route.  The
separation field is the remaining-separation projection above, while the
same-block fields are canonical for the role-hinged generated family. -/
def reducedMetricFieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields
      (ReducedMetricSourceFieldsW21.roleHingedGeneratedChainFamily
        C.toRoleHingedPeriodSearchFamily) :=
  RemainingSeparationInhabitationW22.reducedMetricFieldsOfConcreteValueMatrixFamily
    C

@[simp]
theorem reducedMetricFieldsOfConcreteValueMatrixFamily_separation
    (C : ConcreteValueMatrixFamily) :
    ReducedMetricSourceFieldsW21.separationOfFields
      (reducedMetricFieldsOfConcreteValueMatrixFamily C) =
        remainingSeparationOfConcreteValueMatrixFamily C := by
  exact
    RemainingSeparationInhabitationW22.remainingSeparationOfConcreteValueMatrixFamily_eq_w21
      C

/-- Concrete value matrices construct the raw W20 source fields through the
period-closure source and the reduced metric fields. -/
def sourceFieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SourceFields :=
  GeneratedChainSourceFieldsInhabitationW22.sourceFieldsOfClosureSourceAndReducedMetricFields
    (periodClosureSourceOfConcreteValueMatrixFamily C)
    (reducedMetricFieldsOfConcreteValueMatrixFamily C)

@[simp]
theorem sourceFieldsOfConcreteValueMatrixFamily_eq_w22_sources
    (C : ConcreteValueMatrixFamily) :
    sourceFieldsOfConcreteValueMatrixFamily C =
      GeneratedChainSourceFieldsInhabitationW22.sourceFieldsOfConcreteValueMatrixFamilyViaW21Sources
        C := by
  rfl

/-- The W19 input package is the exact projection of the concrete source
fields. -/
def inputPackageOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    W19InputPackage :=
  (sourceFieldsOfConcreteValueMatrixFamily C).toInputPackage

@[simp]
theorem inputPackageOfConcreteValueMatrixFamily_eq_w21
    (C : ConcreteValueMatrixFamily) :
    inputPackageOfConcreteValueMatrixFamily C =
      ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
        C := by
  rfl

/-- Row packages are enough: first build the concrete value-matrix package,
then assemble the actual W20 source fields. -/
def sourceFieldsOfConcreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    SourceFields :=
  sourceFieldsOfConcreteValueMatrixFamily P.toConcreteValueMatrixFamily

@[simp]
theorem sourceFieldsOfConcreteValueMatrixRowPackage_toInputPackage
    (P : ConcreteValueMatrixRowPackage) :
    (sourceFieldsOfConcreteValueMatrixRowPackage P).toInputPackage =
      P.toInputPackage := by
  rfl

/-- The named W19 input package obtained from the row package via the source
fields above. -/
def inputPackageOfConcreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    W19InputPackage :=
  (sourceFieldsOfConcreteValueMatrixRowPackage P).toInputPackage

@[simp]
theorem inputPackageOfConcreteValueMatrixRowPackage_eq_rowPackage
    (P : ConcreteValueMatrixRowPackage) :
    inputPackageOfConcreteValueMatrixRowPackage P = P.toInputPackage := by
  rfl

theorem nonempty_sourceFields_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    Nonempty SourceFields :=
  Nonempty.intro (sourceFieldsOfConcreteValueMatrixRowPackage P)

theorem nonempty_w19InputPackage_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    Nonempty W19InputPackage :=
  Nonempty.intro (inputPackageOfConcreteValueMatrixRowPackage P)

theorem nonempty_sourceFields_of_nonempty_concreteValueMatrixRowPackage :
    Nonempty ConcreteValueMatrixRowPackage -> Nonempty SourceFields := by
  intro h
  cases h with
  | intro P =>
      exact nonempty_sourceFields_of_concreteValueMatrixRowPackage P

theorem nonempty_w19InputPackage_of_nonempty_concreteValueMatrixRowPackage :
    Nonempty ConcreteValueMatrixRowPackage -> Nonempty W19InputPackage := by
  intro h
  cases h with
  | intro P =>
      exact nonempty_w19InputPackage_of_concreteValueMatrixRowPackage P

end

end GeneratedChainSourceFieldsConcreteClosureW23
end PachToth
end ErdosProblems1066
