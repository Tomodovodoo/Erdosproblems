import ErdosProblems1066.PachToth.GeneratedChainClosureProducerW20
import ErdosProblems1066.PachToth.PeriodClosureSourceW21
import ErdosProblems1066.PachToth.GeneratedPeriodClosure
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20

/-!
# W22 generated-chain closure inhabitation

This file is the W22 handoff for generated-chain closure data.  It does not
assert that any search succeeds.  Instead it records the constructors and
equivalences needed to feed either the W19 input package or the W20
`SourceFields` interface once generated-chain closures and reduced metric
data are available.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedChainClosureInhabitationW22

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev GeneratedChainFamily :=
  GeneratedChainClosureProducerW20.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.GeneratedChainFamilyClosures F

abbrev FamilyPeriodEquations
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.FamilyPeriodEquations F

abbrev GeneratedChainFamilyPeriods
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.GeneratedChainFamilyPeriods F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.ReducedMetricHypotheses F

abbrev ClosureSource
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.ClosureSource F

abbrev SourceFields :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev W19InputPackage :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations

abbrev PeriodEquationSourceFields
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Type :=
  PeriodClosureSourceW21.PeriodEquationSourceFields O base

/-! ## Generic closure sources -/

/-- A generated-chain closure family is already the W20 closure-source
interface. -/
def closureSourceOfClosures
    {F : GeneratedChainFamily}
    (closure : GeneratedChainFamilyClosures F) :
    ClosureSource F :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures closure

/-- Forget the W20 closure-source wrapper. -/
def closuresOfClosureSource
    {F : GeneratedChainFamily}
    (source : ClosureSource F) :
    GeneratedChainFamilyClosures F :=
  source.toGeneratedChainFamilyClosures

/-- Closure sources and generated-chain closure families carry the same
proof data. -/
theorem closureSource_iff_closures
    {F : GeneratedChainFamily} :
    ClosureSource F <-> GeneratedChainFamilyClosures F := by
  exact
    Iff.intro
      (fun source => closuresOfClosureSource source)
      (fun closure => closureSourceOfClosures closure)

/-- Family period equations produce generated-chain closures. -/
def closuresOfFamilyPeriodEquations
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    GeneratedChainFamilyClosures F :=
  GeneratedChainClosureProducerW20.closuresOfPeriodEquations F period

/-- Family period equations produce the W20 closure-source interface. -/
def closureSourceOfFamilyPeriodEquations
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    ClosureSource F :=
  GeneratedChainClosureProducerW20.ClosureSource.ofPeriodEquations F period

@[simp]
theorem closureSourceOfFamilyPeriodEquations_closure
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    (closureSourceOfFamilyPeriodEquations F period).closure =
      closuresOfFamilyPeriodEquations F period :=
  rfl

/-- Existing generated-period hypotheses give the same closure target through
the W20 constructor. -/
def closuresOfGeneratedPeriods
    (F : GeneratedChainFamily)
    (period : GeneratedChainFamilyPeriods F) :
    GeneratedChainFamilyClosures F :=
  GeneratedChainClosureProducerW20.closuresOfGeneratedPeriods F period

/-- Existing generated-period hypotheses packaged as a W20 closure source. -/
def closureSourceOfGeneratedPeriods
    (F : GeneratedChainFamily)
    (period : GeneratedChainFamilyPeriods F) :
    ClosureSource F :=
  GeneratedChainClosureProducerW20.ClosureSource.ofGeneratedPeriods F period

/-! ## Feeding W20 source fields and the W19 input package -/

/-- A closure source plus reduced metric data is exactly enough to assemble
the raw W20 source-field interface. -/
def sourceFieldsOfClosureSourceReducedMetric
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    SourceFields where
  O := F.O
  base := F.base
  orientation := F.orientation
  closure := source.toGeneratedChainFamilyClosures
  separated := fun k hk => (metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (metric.metric k hk).transition_preserves_same_block_distances

@[simp]
theorem sourceFieldsOfClosureSourceReducedMetric_closure
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (sourceFieldsOfClosureSourceReducedMetric source metric).closure k hk =
      source.toGeneratedChainFamilyClosures k hk :=
  rfl

@[simp]
theorem sourceFieldsOfClosureSourceReducedMetric_separated
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (sourceFieldsOfClosureSourceReducedMetric source metric).separated k hk =
      (metric.metric k hk).separated :=
  rfl

/-- A closure source plus reduced metric data is exactly the minimal W19
input package. -/
def inputPackageOfClosureSourceReducedMetric
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    W19InputPackage where
  family := F
  closure := source.toGeneratedChainFamilyClosures
  metric := metric

@[simp]
theorem inputPackageOfClosureSourceReducedMetric_closure
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    (inputPackageOfClosureSourceReducedMetric source metric).closure =
      source.toGeneratedChainFamilyClosures :=
  rfl

@[simp]
theorem inputPackageOfClosureSourceReducedMetric_metric
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    (inputPackageOfClosureSourceReducedMetric source metric).metric =
      metric :=
  rfl

/-- Exact-family hypotheses are the same reduced package, under the existing
W20 closure-source projection. -/
def exactFamilyHypothesesOfClosureSourceReducedMetric
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    ExactFamilyClosure.ExactFamilyHypotheses :=
  source.toExactFamilyHypotheses metric

/-- W20 source fields are inhabited exactly when some generated-chain family
has a closure source and reduced metric data. -/
theorem nonempty_sourceFields_iff_exists_closureSource_reducedMetric :
    Nonempty SourceFields <->
      Exists fun F : GeneratedChainFamily =>
        ClosureSource F /\ ReducedMetricHypotheses F := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact
              Exists.intro S.family
                (And.intro
                  (closureSourceOfClosures S.closures)
                  S.reducedMetric))
      (fun h => by
        cases h with
        | intro F hF =>
            exact
              Nonempty.intro
                (sourceFieldsOfClosureSourceReducedMetric hF.left hF.right))

/-- The W19 input package has the same minimal decomposition. -/
theorem nonempty_inputPackage_iff_exists_closureSource_reducedMetric :
    Nonempty W19InputPackage <->
      Exists fun F : GeneratedChainFamily =>
        ClosureSource F /\ ReducedMetricHypotheses F := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro P =>
            exact
              Exists.intro P.family
                (And.intro
                  (closureSourceOfClosures P.closure)
                  P.metric))
      (fun h => by
        cases h with
        | intro F hF =>
            exact
              Nonempty.intro
                (inputPackageOfClosureSourceReducedMetric hF.left hF.right))

/-! ## Period-equation packages -/

/-- The minimal family-level period-equation package needed to get
generated-chain closures, before metric data is added. -/
structure PeriodEquationClosurePackage where
  family : GeneratedChainFamily
  period : FamilyPeriodEquations family

namespace PeriodEquationClosurePackage

def closures
    (P : PeriodEquationClosurePackage) :
    GeneratedChainFamilyClosures P.family :=
  closuresOfFamilyPeriodEquations P.family P.period

def closureSource
    (P : PeriodEquationClosurePackage) :
    ClosureSource P.family :=
  closureSourceOfFamilyPeriodEquations P.family P.period

end PeriodEquationClosurePackage

/-- Adding reduced metric data to period equations is exactly enough for both
W20 source fields and the W19 input package. -/
structure PeriodEquationInputPackage where
  family : GeneratedChainFamily
  period : FamilyPeriodEquations family
  metric : ReducedMetricHypotheses family

namespace PeriodEquationInputPackage

def closurePackage
    (P : PeriodEquationInputPackage) :
    PeriodEquationClosurePackage where
  family := P.family
  period := P.period

def closureSource
    (P : PeriodEquationInputPackage) :
    ClosureSource P.family :=
  P.closurePackage.closureSource

def sourceFields
    (P : PeriodEquationInputPackage) :
    SourceFields :=
  sourceFieldsOfClosureSourceReducedMetric P.closureSource P.metric

def inputPackage
    (P : PeriodEquationInputPackage) :
    W19InputPackage :=
  inputPackageOfClosureSourceReducedMetric P.closureSource P.metric

end PeriodEquationInputPackage

/-- Raw W21 period-equation source fields are equivalent to the generic
candidate-family interface they assemble. -/
theorem nonempty_periodEquationSourceFields_iff_candidateFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2} :
    Nonempty (PeriodEquationSourceFields O base) <->
      Nonempty
        (PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base) := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S =>
            exact Nonempty.intro S.toCandidateFamily)
      (fun h => by
        cases h with
        | intro F =>
            exact
              Nonempty.intro
                { word := F.word
                  equations := F.equations })

/-- W21 source fields feed the W20 closure-source target. -/
def closureSourceOfPeriodEquationSourceFields
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : PeriodEquationSourceFields O base) :
    ClosureSource
      (PeriodClosureSourceW21.generatedChainFamilyOfPeriodEquationCandidateFamily
        O base S.toCandidateFamily) :=
  S.toClosureSource

/-! ## Concrete period-search adapters -/

/-- Concrete period-search data feeds the generated-chain closure target used
by W20. -/
def closuresOfConcretePeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    GeneratedChainFamilyClosures
      (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
        F) :=
  GeneratedChainClosureProducerW20.closuresOfConcretePeriodSearchData F

/-- Concrete period-search data packaged as a W20 closure source. -/
def closureSourceOfConcretePeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    ClosureSource
      (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
        F) :=
  PeriodClosureSourceW21.sourceOfConcretePeriodSearchData F

/-- Concrete period-search plus cross-block data supplies the W19 package. -/
def inputPackageOfConcreteCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    W19InputPackage :=
  inputPackageOfClosureSourceReducedMetric
    (PeriodClosureSourceW21.sourceOfConcreteCrossBlockFamily F)
    F.toReducedMetricHypotheses

/-- Concrete period-search plus cross-block data also supplies W20 source
fields. -/
def sourceFieldsOfConcreteCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    SourceFields :=
  sourceFieldsOfClosureSourceReducedMetric
    (PeriodClosureSourceW21.sourceOfConcreteCrossBlockFamily F)
    F.toReducedMetricHypotheses

/-! ## Concrete period-candidate adapters -/

/-- A role-hinge period-candidate family carries generated-chain closures
before metric data is attached. -/
def closuresOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    GeneratedChainFamilyClosures
      (PeriodClosureSourceW21.generatedChainFamilyOfPeriodCandidateFamily F) :=
  (PeriodClosureSourceW21.sourceOfPeriodCandidateFamily F)
    |>.toGeneratedChainFamilyClosures

/-- The same candidate family as a W20 closure source. -/
def closureSourceOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    ClosureSource
      (PeriodClosureSourceW21.generatedChainFamilyOfPeriodCandidateFamily F) :=
  PeriodClosureSourceW21.sourceOfPeriodCandidateFamily F

def periodCandidateSearchGeneratedChainFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    GeneratedChainFamily :=
  F.toRoleHingeTransitionFactsFiniteSearchFamily
    |>.toRoleHingedGeneratedClosureFamily
    |>.toGeneratedChainFamily

/-- Candidate-search families include cross-block data, so their generated
closure family also carries reduced metric hypotheses. -/
def reducedMetricHypothesesOfPeriodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    ReducedMetricHypotheses (periodCandidateSearchGeneratedChainFamily F) :=
  F.toRoleHingeTransitionFactsFiniteSearchFamily
    |>.toRoleHingedGeneratedClosureFamily
    |>.toReducedMetricHypotheses

/-- Period-candidate search families feed the W19 input package. -/
def inputPackageOfPeriodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    W19InputPackage :=
  inputPackageOfClosureSourceReducedMetric
    (PeriodClosureSourceW21.sourceOfPeriodCandidateSearchFamily F)
    (reducedMetricHypothesesOfPeriodCandidateSearchFamily F)

/-- Period-candidate search families feed the W20 source-field interface. -/
def sourceFieldsOfPeriodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    SourceFields :=
  sourceFieldsOfClosureSourceReducedMetric
    (PeriodClosureSourceW21.sourceOfPeriodCandidateSearchFamily F)
    (reducedMetricHypothesesOfPeriodCandidateSearchFamily F)

end

end GeneratedChainClosureInhabitationW22
end PachToth
end ErdosProblems1066
