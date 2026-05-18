import ErdosProblems1066.PachToth.AlternativeValueMatrixFamilyW24
import ErdosProblems1066.PachToth.DirectCrossBlockInputPackageW24
import ErdosProblems1066.PachToth.SmallLengthExactTargetsConcreteW24

set_option autoImplicit false

/-!
# W25 alternative value-matrix inhabitation audit

This file attacks direct inhabitation of
`AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily`.

The existing concrete lower-table data supplies generated closure and global
separation, and exact-local preservation supplies the full-metric same-block
route.  The W24 alternative value-matrix family, however, is the reduced W20
input surface: it still asks for transition preservation of same-block
distances for arbitrary sources.  The constructors below therefore name that
field exactly and only derive the alternative family once it is supplied.

No unconditional `5 / 16` endpoint is proved here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AlternativeValueMatrixInhabitationW25

open FiniteGraph

noncomputable section

abbrev AlternativeValueMatrixFamily : Type :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily

abbrev GeneratedChainFamily : Type :=
  AlternativeValueMatrixFamilyW24.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  AlternativeValueMatrixFamilyW24.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  AlternativeValueMatrixFamilyW24.ReducedMetricHypotheses F

abbrev W20ClosureReducedMetricSourceFields : Type :=
  AlternativeValueMatrixFamilyW24.W20ClosureReducedMetricSourceFields

abbrev W20SourceFields : Type :=
  AlternativeValueMatrixFamilyW24.W20SourceFields

abbrev W19InputPackage : Type :=
  AlternativeValueMatrixFamilyW24.W19InputPackage

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily

abbrev ExactLocalPreservation
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  DirectCrossBlockInputPackageW24.ExactLocalPreservation O

abbrev MissingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C

abbrev DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C

abbrev ExactBaseFullMetricSourceFields : Type :=
  DirectCrossBlockInputPackageW24.ExactBaseFullMetricSourceFields

abbrev SmallLengthExactBlockTargets : Prop :=
  SmallLengthExactTargetsConcreteW24.SmallLengthExactBlockTargets

abbrev ExactBlocksOneThroughFive : Prop :=
  SmallLengthExactTargetsConcreteW24.ExactBlocksOneThroughFive

/-! ## Exact minimal reduced-field equivalences -/

/-- The alternative value-matrix family has exactly the same inhabitation
content as the reduced W20 closure/metric source surface. -/
theorem nonempty_alternativeValueMatrixFamily_iff_w20ClosureReducedMetricSourceFields :
    Nonempty AlternativeValueMatrixFamily <->
      Nonempty W20ClosureReducedMetricSourceFields := by
  constructor
  · intro h
    rcases h with ⟨A⟩
    exact Nonempty.intro A.toW20ClosureReducedMetricSourceFields
  · intro h
    rcases h with ⟨S⟩
    exact
      Nonempty.intro
        (AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.ofInputPackage
          S.toInputPackage)

/-- Raw W20 source fields carry the same inhabitation information as the
alternative value-matrix family. -/
theorem nonempty_alternativeValueMatrixFamily_iff_w20SourceFields :
    Nonempty AlternativeValueMatrixFamily <-> Nonempty W20SourceFields := by
  constructor
  · intro h
    rcases h with ⟨A⟩
    exact Nonempty.intro A.toW20SourceFields
  · intro h
    rcases h with ⟨S⟩
    exact
      Nonempty.intro
        (AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.ofInputPackage
          S.toInputPackage)

/-- W19 input packages are the same minimal data, because the value matrix can
always be chosen to be the actual generated Euclidean distance. -/
theorem nonempty_alternativeValueMatrixFamily_iff_w19InputPackage :
    Nonempty AlternativeValueMatrixFamily <-> Nonempty W19InputPackage :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.nonempty_alternativeValueMatrixFamily_iff_knownBoundsRemainingData

/-- Constructor from exactly a generated family, closure equations, and
reduced metric hypotheses. -/
def alternativeValueMatrixFamilyOfClosureReducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    AlternativeValueMatrixFamily :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.ofInputPackage
    (({ family := F
        closure := closure
        reducedMetric := reducedMetric } :
        W20ClosureReducedMetricSourceFields).toInputPackage)

@[simp]
theorem alternativeValueMatrixFamilyOfClosureReducedMetric_family
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    (alternativeValueMatrixFamilyOfClosureReducedMetric
      F closure reducedMetric).family = F := by
  rfl

theorem nonempty_alternativeValueMatrixFamily_of_closure_reducedMetric
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (reducedMetric : ReducedMetricHypotheses F) :
    Nonempty AlternativeValueMatrixFamily :=
  Nonempty.intro
    (alternativeValueMatrixFamilyOfClosureReducedMetric
      F closure reducedMetric)

/-! ## Cross-block table constructor and its precise missing field -/

/-- Concrete lower tables plus the one reduced transition-preservation field
are the nearest existing explicit-table route into the alternative family. -/
structure ConcreteLowerTableReducedFields where
  lowerTables : ConcreteNonConnectorLowerTableFamily
  transition_preserves_same_block_distances :
    MissingDirectReducedInputField lowerTables

namespace ConcreteLowerTableReducedFields

def toDirectReducedSourceFields
    (D : ConcreteLowerTableReducedFields) :
    DirectReducedSourceFieldsOver D.lowerTables where
  transition_preserves_same_block_distances :=
    D.transition_preserves_same_block_distances

def toW20SourceFields
    (D : ConcreteLowerTableReducedFields) :
    DirectCrossBlockInputPackageW24.W20SourceFields :=
  D.toDirectReducedSourceFields.toSourceFields

def toInputPackage
    (D : ConcreteLowerTableReducedFields) :
    W19InputPackage :=
  D.toDirectReducedSourceFields.toInputPackage

def toAlternativeValueMatrixFamily
    (D : ConcreteLowerTableReducedFields) :
    AlternativeValueMatrixFamily :=
  AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.ofInputPackage
    D.toInputPackage

end ConcreteLowerTableReducedFields

/-- The table route is inhabited exactly when some concrete lower-table family
has the missing reduced transition-preservation field. -/
theorem nonempty_concreteLowerTableReducedFields_iff :
    Nonempty ConcreteLowerTableReducedFields <->
      Exists fun C : ConcreteNonConnectorLowerTableFamily =>
        MissingDirectReducedInputField C := by
  constructor
  · intro h
    rcases h with ⟨D⟩
    exact ⟨D.lowerTables, D.transition_preserves_same_block_distances⟩
  · intro h
    rcases h with ⟨C, hC⟩
    exact
      Nonempty.intro
        { lowerTables := C
          transition_preserves_same_block_distances := hC }

theorem nonempty_alternativeValueMatrixFamily_of_concreteLowerTableReducedFields :
    Nonempty ConcreteLowerTableReducedFields ->
      Nonempty AlternativeValueMatrixFamily := by
  intro h
  rcases h with ⟨D⟩
  exact Nonempty.intro D.toAlternativeValueMatrixFamily

theorem nonempty_alternativeValueMatrixFamily_of_concreteLowerTables_missingReducedField
    (C : ConcreteNonConnectorLowerTableFamily)
    (hreduce : MissingDirectReducedInputField C) :
    Nonempty AlternativeValueMatrixFamily :=
  nonempty_alternativeValueMatrixFamily_of_concreteLowerTableReducedFields
    (Nonempty.intro
      { lowerTables := C
        transition_preserves_same_block_distances := hreduce })

/-- Fixed-table version of the same minimal equivalence. -/
theorem nonempty_directReducedSourceFieldsOver_iff_missingReducedField
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectReducedSourceFieldsOver C) <->
      MissingDirectReducedInputField C :=
  DirectCrossBlockInputPackageW24.nonempty_directReducedSourceFieldsOver_iff_missingDirectReducedInputField C

/-! ## Exact-local and finite data contrasts -/

/-- Concrete lower tables plus exact-local preservation close the existing
full-metric route.  This is not the reduced alternative-family route. -/
def exactBaseFullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    ExactBaseFullMetricSourceFields :=
  DirectCrossBlockInputPackageW24.fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    C exactLocal

theorem nonempty_exactBaseFullMetricSourceFields_of_concreteLowerTables_exactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    Nonempty ExactBaseFullMetricSourceFields :=
  Nonempty.intro
    (exactBaseFullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
      C exactLocal)

/-- Adding the exact-local full-metric certificate to the table data still
requires the reduced transition-preservation field to construct the
alternative value-matrix family. -/
theorem nonempty_alternativeValueMatrixFamily_of_concreteLowerTables_exactLocal_missingReducedField
    (C : ConcreteNonConnectorLowerTableFamily)
    (_exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations)
    (hreduce : MissingDirectReducedInputField C) :
    Nonempty AlternativeValueMatrixFamily :=
  nonempty_alternativeValueMatrixFamily_of_concreteLowerTables_missingReducedField
    C hreduce

/-- The finite small-block certificates are exactly the one-through-five exact
block targets; they do not by themselves provide the reduced generated-family
fields above. -/
theorem nonempty_smallLengthExactBlockTargets_iff_exactBlocksOneThroughFive :
    Nonempty SmallLengthExactBlockTargets <-> ExactBlocksOneThroughFive :=
  SmallLengthExactTargetsConcreteW24.nonempty_smallLengthExactBlockTargets_iff_exactBlocksOneThroughFive

/-! ## Recorded no-go contrasts for blocked routes -/

theorem not_nonempty_concreteRowPackage_route :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage) :=
  AlternativeValueMatrixFamilyW24.not_nonempty_concreteRowPackage

theorem not_nonempty_concreteValueMatrixFamily_route :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily) :=
  AlternativeValueMatrixFamilyW24.not_nonempty_concreteValueMatrixFamily

theorem not_nonempty_roleHingedGeneratedClosureFamily_route :
    Not (Nonempty GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :=
  GeneratedChainFamilyProducerW20.not_nonempty_roleHingedGeneratedClosureFamily

end

end AlternativeValueMatrixInhabitationW25
end PachToth

namespace Verified

abbrev PachTothW25AlternativeValueMatrixFamily : Type :=
  _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.AlternativeValueMatrixFamily

abbrev PachTothW25ConcreteLowerTableReducedFields : Type :=
  _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.ConcreteLowerTableReducedFields

theorem pachtoth_w25_nonempty_alternativeValueMatrixFamily_iff_w20SourceFields :
    Nonempty PachTothW25AlternativeValueMatrixFamily <->
      Nonempty
        _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.W20SourceFields :=
  _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.nonempty_alternativeValueMatrixFamily_iff_w20SourceFields

theorem pachtoth_w25_nonempty_concreteLowerTableReducedFields_iff :
    Nonempty PachTothW25ConcreteLowerTableReducedFields <->
      Exists fun C :
        _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.ConcreteNonConnectorLowerTableFamily =>
        _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.MissingDirectReducedInputField C :=
  _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.nonempty_concreteLowerTableReducedFields_iff

theorem pachtoth_w25_nonempty_alternativeValueMatrixFamily_of_concreteLowerTableReducedFields :
    Nonempty PachTothW25ConcreteLowerTableReducedFields ->
      Nonempty PachTothW25AlternativeValueMatrixFamily :=
  _root_.ErdosProblems1066.PachToth.AlternativeValueMatrixInhabitationW25.nonempty_alternativeValueMatrixFamily_of_concreteLowerTableReducedFields

end Verified
end ErdosProblems1066
