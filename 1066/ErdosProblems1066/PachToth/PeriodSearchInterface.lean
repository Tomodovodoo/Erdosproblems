import ErdosProblems1066.PachToth.PeriodInterface
import ErdosProblems1066.PachToth.GeneratedSeparationInterface

set_option autoImplicit false

/-!
# Finite period-search interface

This module gives a Lean-checkable interface for finite period equations
coming from a finite orientation word.  It does not assert that an external
search succeeded.  Instead, a search result is represented by finite data
together with exact equation certificates, which can later be filled by
verified algebraic computations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodSearchInterface

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- A finite orientation word for a generated same/opposite chain. -/
structure FiniteOrientationWord where
  length : Nat
  positive_length : 0 < length
  letter : Fin length -> OrientationData.BlockOrientation

namespace FiniteOrientationWord

/-- The generated block after `n` letters, starting from `base`. -/
def generatedBlock
    (W : FiniteOrientationWord)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) (n : Nat) : LocalVertex -> R2 :=
  GeneratedClosedChain.generatedBlock O W.positive_length base W.letter n

/-- The generated cyclic point map associated to the word. -/
def generatedPoint
    (W : FiniteOrientationWord)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) : Fin W.length -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint O W.positive_length base W.letter

/-- The algebraic block obtained by iterating transitions from cyclic index
`0` for `n` steps. -/
def iteratedTransitionBlock
    (W : FiniteOrientationWord)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) (n : Nat) : LocalVertex -> R2 :=
  ClosedPlacementAlgebra.iteratedTransitionBlock O W.positive_length
    (W.generatedPoint O base) W.letter (Fin.mk 0 W.positive_length) n

@[simp]
theorem generatedBlock_def
    (W : FiniteOrientationWord)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) (n : Nat) :
    W.generatedBlock O base n =
      GeneratedClosedChain.generatedBlock O W.positive_length base W.letter n :=
  rfl

@[simp]
theorem generatedPoint_def
    (W : FiniteOrientationWord)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) :
    W.generatedPoint O base =
      GeneratedClosedChain.generatedPoint O W.positive_length base W.letter :=
  rfl

@[simp]
theorem iteratedTransitionBlock_def
    (W : FiniteOrientationWord)
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) (n : Nat) :
    W.iteratedTransitionBlock O base n =
      ClosedPlacementAlgebra.iteratedTransitionBlock O W.positive_length
        (GeneratedClosedChain.generatedPoint O W.positive_length base W.letter)
        W.letter (Fin.mk 0 W.positive_length) n :=
  rfl

end FiniteOrientationWord

/-- The generated final-block equation at one local vertex. -/
def GeneratedVertexPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord)
    (v : LocalVertex) : Prop :=
  W.generatedBlock O base W.length v = base v

/-- The same one-vertex period equation, expressed through the reusable
closed-placement iterated-transition algebra from cyclic index `0`. -/
def AlgebraicVertexPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord)
    (v : LocalVertex) : Prop :=
  W.iteratedTransitionBlock O base W.length v = base v

/-- Pointwise generated final-block equations for all local vertices. -/
structure GeneratedPeriodCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord) where
  equation :
    forall v : LocalVertex, GeneratedVertexPeriodEquation O base W v

/-- Pointwise algebraic period equations for all local vertices. -/
structure AlgebraicPeriodCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord) where
  equation :
    forall v : LocalVertex, AlgebraicVertexPeriodEquation O base W v

/-- A `Fin 16`-indexed generated certificate.  This is convenient for finite
checkers that enumerate the known local vertex set via
`BlockPartition.localVertexEquivFin16`. -/
structure IndexedGeneratedPeriodCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord) where
  equation :
    forall i : Fin 16,
      GeneratedVertexPeriodEquation O base W
        (BlockPartition.localVertexEquivFin16.symm i)

/-- A `Fin 16`-indexed algebraic certificate.  This is the preferred target
for later exact equation checks: each field is a concrete local-vertex period
equation, not an unproved assumption about an external search. -/
structure IndexedAlgebraicPeriodCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord) where
  equation :
    forall i : Fin 16,
      AlgebraicVertexPeriodEquation O base W
        (BlockPartition.localVertexEquivFin16.symm i)

namespace GeneratedPeriodCertificate

/-- Convert pointwise generated equations into the named period equation from
`PeriodInterface`. -/
theorem toGeneratedPeriodEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : GeneratedPeriodCertificate O base W) :
    PeriodInterface.GeneratedPeriodEquation O W.positive_length base W.letter := by
  funext v
  exact C.equation v

/-- Convert pointwise generated equations into the generated-period
hypothesis consumed by the generated separation interface. -/
theorem toGeneratedPeriod
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : GeneratedPeriodCertificate O base W) :
    GeneratedSeparationInterface.GeneratedPeriod
      O W.positive_length base W.letter := by
  exact C.toGeneratedPeriodEquation

end GeneratedPeriodCertificate

namespace AlgebraicPeriodCertificate

/-- Convert pointwise algebraic equations into the named algebraic closure
equation from `PeriodInterface`. -/
theorem toGeneratedClosureEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : AlgebraicPeriodCertificate O base W) :
    PeriodInterface.GeneratedClosureEquation O W.positive_length base W.letter := by
  funext v
  exact C.equation v

/-- Convert algebraic period equations into the generated final-block period
equation using the existing `PeriodInterface` bridge. -/
theorem toGeneratedPeriodEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : AlgebraicPeriodCertificate O base W) :
    PeriodInterface.GeneratedPeriodEquation O W.positive_length base W.letter := by
  exact
    PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
      O W.positive_length base W.letter C.toGeneratedClosureEquation

/-- Convert algebraic period equations into the generated-period hypothesis
used downstream. -/
theorem toGeneratedPeriod
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : AlgebraicPeriodCertificate O base W) :
    GeneratedSeparationInterface.GeneratedPeriod
      O W.positive_length base W.letter := by
  exact C.toGeneratedPeriodEquation

end AlgebraicPeriodCertificate

namespace IndexedGeneratedPeriodCertificate

/-- Reindex a `Fin 16` generated certificate to all local vertices. -/
def toPointwise
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedGeneratedPeriodCertificate O base W) :
    GeneratedPeriodCertificate O base W where
  equation := by
    intro v
    simpa [GeneratedVertexPeriodEquation] using
      C.equation (BlockPartition.localVertexEquivFin16 v)

/-- Convert a finite indexed generated certificate to the named period
equation. -/
theorem toGeneratedPeriodEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedGeneratedPeriodCertificate O base W) :
    PeriodInterface.GeneratedPeriodEquation O W.positive_length base W.letter :=
  C.toPointwise.toGeneratedPeriodEquation

/-- Convert a finite indexed generated certificate to `GeneratedPeriod`. -/
theorem toGeneratedPeriod
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedGeneratedPeriodCertificate O base W) :
    GeneratedSeparationInterface.GeneratedPeriod
      O W.positive_length base W.letter :=
  C.toPointwise.toGeneratedPeriod

end IndexedGeneratedPeriodCertificate

namespace IndexedAlgebraicPeriodCertificate

/-- Reindex a `Fin 16` algebraic certificate to all local vertices. -/
def toPointwise
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedAlgebraicPeriodCertificate O base W) :
    AlgebraicPeriodCertificate O base W where
  equation := by
    intro v
    simpa [AlgebraicVertexPeriodEquation] using
      C.equation (BlockPartition.localVertexEquivFin16 v)

/-- Convert a finite indexed algebraic certificate to the named algebraic
closure equation. -/
theorem toGeneratedClosureEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedAlgebraicPeriodCertificate O base W) :
    PeriodInterface.GeneratedClosureEquation O W.positive_length base W.letter :=
  C.toPointwise.toGeneratedClosureEquation

/-- Convert a finite indexed algebraic certificate to the named generated
period equation through `PeriodInterface`. -/
theorem toGeneratedPeriodEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedAlgebraicPeriodCertificate O base W) :
    PeriodInterface.GeneratedPeriodEquation O W.positive_length base W.letter :=
  C.toPointwise.toGeneratedPeriodEquation

/-- Convert a finite indexed algebraic certificate to `GeneratedPeriod`. -/
theorem toGeneratedPeriod
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    {W : FiniteOrientationWord}
    (C : IndexedAlgebraicPeriodCertificate O base W) :
    GeneratedSeparationInterface.GeneratedPeriod
      O W.positive_length base W.letter :=
  C.toPointwise.toGeneratedPeriod

end IndexedAlgebraicPeriodCertificate

/-- A checkable output shape for a period search against fixed transition
obligations and base block: a finite word plus exact algebraic equations. -/
structure PeriodSearchCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2) where
  word : FiniteOrientationWord
  period : IndexedAlgebraicPeriodCertificate O base word

namespace PeriodSearchCertificate

/-- The orientation word extracted from a search certificate. -/
def orientation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodSearchCertificate O base) :
    Fin C.word.length -> OrientationData.BlockOrientation :=
  C.word.letter

/-- The indexed algebraic equations imply the generated final-block period
equation for the stored word. -/
theorem toGeneratedPeriodEquation
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodSearchCertificate O base) :
    PeriodInterface.GeneratedPeriodEquation
      O C.word.positive_length base C.word.letter :=
  C.period.toGeneratedPeriodEquation

/-- The finite search certificate supplies the downstream generated-period
hypothesis for its stored orientation word. -/
theorem toGeneratedPeriod
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodSearchCertificate O base) :
    GeneratedSeparationInterface.GeneratedPeriod
      O C.word.positive_length base C.word.letter :=
  C.period.toGeneratedPeriod

end PeriodSearchCertificate

end

end PeriodSearchInterface
end PachToth
end ErdosProblems1066
