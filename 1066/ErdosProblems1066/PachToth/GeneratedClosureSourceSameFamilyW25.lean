import ErdosProblems1066.PachToth.PachTothW23RouteAudit
import ErdosProblems1066.PachToth.GeneratedChainSourceFieldsConcreteClosureW23
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24
import ErdosProblems1066.PachToth.FreePlacementSourceFieldsW24

set_option autoImplicit false

/-!
# W25 same-family generated closure sources

This file keeps the W25 handoff on the `ClosureSource` side.  The central
object is a same-`GeneratedChainFamily` package of closure equations, with
direct projections to the W20 closure-source interface and to the W23 route
audit spelling.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosureSourceSameFamilyW25

open FiniteGraph

noncomputable section

abbrev GeneratedChainFamily : Type :=
  PachTothW23RouteAudit.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.GeneratedChainFamilyClosures F

abbrev FamilyPeriodEquations
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.FamilyPeriodEquations F

abbrev ClosureSource
    (F : GeneratedChainFamily) :=
  GeneratedChainClosureProducerW20.ClosureSource F

abbrev W23ClosureSource
    (F : GeneratedChainFamily) :=
  PachTothW23RouteAudit.ClosureSource F

abbrev W23ReducedMetricFields
    (F : GeneratedChainFamily) :=
  PachTothW23RouteAudit.ReducedMetricFields F

abbrev W23GeneratedClosureMetricRowPackage : Type :=
  PachTothW23RouteAudit.GeneratedClosureMetricRowPackage

/-- Exact same-family closure equations.  This is the closure-only package:
one generated-chain family and period equations for that same family. -/
structure SameFamilyClosureEquationPackage where
  family : GeneratedChainFamily
  period : FamilyPeriodEquations family

namespace SameFamilyClosureEquationPackage

/-- The W20 closure equations produced from the same-family period equations. -/
def closures
    (P : SameFamilyClosureEquationPackage) :
    GeneratedChainFamilyClosures P.family :=
  GeneratedChainClosureProducerW20.closuresOfPeriodEquations P.family P.period

/-- The requested concrete closure-source constructor. -/
def closureSource
    (P : SameFamilyClosureEquationPackage) :
    ClosureSource P.family :=
  GeneratedChainClosureProducerW20.ClosureSource.ofPeriodEquations
    P.family P.period

/-- The same constructor in the W23 route-audit spelling. -/
def toW23ClosureSource
    (P : SameFamilyClosureEquationPackage) :
    W23ClosureSource P.family :=
  P.closureSource

@[simp]
theorem closureSource_toGeneratedChainFamilyClosures
    (P : SameFamilyClosureEquationPackage) :
    P.closureSource.toGeneratedChainFamilyClosures = P.closures :=
  rfl

@[simp]
theorem closureSource_apply
    (P : SameFamilyClosureEquationPackage)
    (k : Nat) (hk : 0 < k) :
    P.closureSource.toGeneratedChainFamilyClosures k hk =
      PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
        (P.family.O k hk) hk (P.family.base k hk)
        (P.family.orientation k hk) (P.period k hk) :=
  rfl

/-- Add W23 reduced-metric fields downstream, keeping the family shared
definitionally with the closure source. -/
def toW23GeneratedClosureMetricRowPackage
    (P : SameFamilyClosureEquationPackage)
    (metric : W23ReducedMetricFields P.family) :
    W23GeneratedClosureMetricRowPackage where
  family := P.family
  closureSource := P.toW23ClosureSource
  reducedMetric := metric

@[simp]
theorem toW23GeneratedClosureMetricRowPackage_closureSource
    (P : SameFamilyClosureEquationPackage)
    (metric : W23ReducedMetricFields P.family) :
    (P.toW23GeneratedClosureMetricRowPackage metric).closureSource =
      P.toW23ClosureSource := by
  rfl

/-- With reduced metric hypotheses, the same closure package gives the W24
reduced closed-placement witness. -/
def toReducedMetricClosedPlacementWitness
    (P : SameFamilyClosureEquationPackage)
    (metric :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        P.family) :
    FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness where
  family := P.family
  closure := P.closures
  metric := metric

/-- The closed-chain point map obtained downstream is the generated closed-chain
point map of the same family. -/
@[simp]
theorem reducedWitness_closedPlacement_point
    (P : SameFamilyClosureEquationPackage)
    (metric :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        P.family)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    ((P.toReducedMetricClosedPlacementWitness metric).closedPlacement k hk).point
        i v =
      GeneratedClosedChain.generatedPoint (P.family.O k hk) hk
        (P.family.base k hk) (P.family.orientation k hk) i v := by
  rfl

end SameFamilyClosureEquationPackage

/-! ## Direct same-family closure-source bridges -/

/-- Already-supplied generated-chain closures are exactly a same-family W23
closure source. -/
def w23ClosureSourceOfClosures
    {F : GeneratedChainFamily}
    (closure : GeneratedChainFamilyClosures F) :
    W23ClosureSource F :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures closure

/-- Same-family period equations are exactly a same-family W23 closure source. -/
def w23ClosureSourceOfPeriodEquations
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    W23ClosureSource F :=
  (SameFamilyClosureEquationPackage.mk F period).toW23ClosureSource

@[simp]
theorem w23ClosureSourceOfPeriodEquations_closure
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    (w23ClosureSourceOfPeriodEquations F period).toGeneratedChainFamilyClosures =
      GeneratedChainClosureProducerW20.closuresOfPeriodEquations F period :=
  rfl

/-- W23 concrete source fields expose their closure component as the W23
same-family closure-source interface. -/
def w23ClosureSourceOfConcreteSourceFields
    (S : GeneratedChainSourceFieldsConcreteClosureW23.SourceFields) :
    W23ClosureSource S.family :=
  GeneratedChainSourceFieldsInhabitationW22.closureSourceOfSourceFields S

@[simp]
theorem w23ClosureSourceOfConcreteSourceFields_closure
    (S : GeneratedChainSourceFieldsConcreteClosureW23.SourceFields) :
    (w23ClosureSourceOfConcreteSourceFields S).toGeneratedChainFamilyClosures =
      S.closures :=
  rfl

/-- Concrete value-matrix rows already construct a same-family closure source
through the W23 concrete source-field route. -/
def w23ClosureSourceOfConcreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage) :
    W23ClosureSource
      (GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
        P).family :=
  w23ClosureSourceOfConcreteSourceFields
    (GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
      P)

/-- The W23 concrete row package gives the W23 audit row package with no
family change between closure source and reduced metric fields. -/
def w23GeneratedClosureMetricRowPackageOfConcreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage) :
    W23GeneratedClosureMetricRowPackage :=
  PachTothW23RouteAudit.generatedClosureMetricRowPackageOfRawSourceFields
    (GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
      P)

/-! ## W24 source-shape projections back to closure sources -/

/-- A W24 reduced closed-placement witness forgets to its same-family W23
closure source. -/
def w23ClosureSourceOfReducedMetricWitness
    (W : FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness) :
    W23ClosureSource W.family :=
  w23ClosureSourceOfClosures W.closure

/-- A W24 full closed-placement witness also forgets to its same-family W23
closure source. -/
def w23ClosureSourceOfFullMetricWitness
    (W : FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness) :
    W23ClosureSource W.family :=
  w23ClosureSourceOfClosures W.closure

/-- Raw W20 source fields as used by the W24 free-placement bridge expose the
same closure source, before forgetting to free-placement geometry. -/
def w23ClosureSourceOfW24FreeW20SourceFields
    (S : FreePlacementSourceFieldsW24.W20SourceFields) :
    W23ClosureSource S.family :=
  GeneratedChainSourceFieldsInhabitationW22.closureSourceOfSourceFields S

@[simp]
theorem w23ClosureSourceOfW24FreeW20SourceFields_closure
    (S : FreePlacementSourceFieldsW24.W20SourceFields) :
    (w23ClosureSourceOfW24FreeW20SourceFields S).toGeneratedChainFamilyClosures =
      S.closures :=
  rfl

end

end GeneratedClosureSourceSameFamilyW25
end PachToth

namespace Verified

abbrev PachTothW25SameFamilyClosureEquationPackage : Type :=
  PachToth.GeneratedClosureSourceSameFamilyW25.SameFamilyClosureEquationPackage

abbrev PachTothW25SameFamilyGeneratedClosureMetricRowPackage : Type :=
  PachToth.GeneratedClosureSourceSameFamilyW25.W23GeneratedClosureMetricRowPackage

def pachtothW25_w23ClosureSource_of_sameFamilyClosureEquationPackage
    (P : PachTothW25SameFamilyClosureEquationPackage) :
    PachToth.PachTothW23RouteAudit.ClosureSource P.family :=
  P.toW23ClosureSource

def pachtothW25_w23GeneratedClosureMetricRowPackage_of_sameFamilyClosureEquationPackage
    (P : PachTothW25SameFamilyClosureEquationPackage)
    (metric :
      PachToth.GeneratedClosureSourceSameFamilyW25.W23ReducedMetricFields
        P.family) :
    PachTothW25SameFamilyGeneratedClosureMetricRowPackage :=
  P.toW23GeneratedClosureMetricRowPackage metric

end Verified
end ErdosProblems1066
