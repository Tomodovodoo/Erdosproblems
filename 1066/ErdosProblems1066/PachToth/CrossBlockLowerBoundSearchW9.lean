import ErdosProblems1066.PachToth.GeneratedPolynomialLowerTableRoute
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart

set_option autoImplicit false

/-!
# W9 cross-block lower-bound search facade

This module is a small certificate surface for the flexible candidate route.
It does not introduce numerical data.  It packages the remaining
non-connector cross-block checks in the forms a generator is expected to
produce, and records the projections to the generated global separation
hypothesis used downstream.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockLowerBoundSearchW9

open FiniteGraph
open GeneratedSeparationFarApart

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingedPeriodSearchFamily :=
  GeneratedPolynomialLowerTableRoute.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  GeneratedPolynomialLowerTableRoute.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  GeneratedPolynomialLowerTableRoute.IndexedCyclicConnectorPair
    hk i u j v

abbrev GeneratedPointNonConnectorPolynomialTable :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable

abbrev GeneratedPointNonConnectorPolynomialTableFamily :=
  GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTableFamily

abbrev UpperTriangleNonConnectorPolynomialTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTable

abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  CrossBlockSqTableSearch.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  CrossBlockSqTableSearch.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev NonConnectorValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

/-- The generated local point for the route family, addressed by local
vertices rather than finite local indices. -/
def generatedLocalPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex) : R2 :=
  GeneratedClosedChain.generatedPoint
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk) i u

/-! ## Direct explicit square-inequality certificate -/

/-- A focused one-period certificate: every non-connector cross-block pair
has generated squared distance at least one.  Connector pairs are deliberately
absent from this surface; the generated-period connector equations fill those
slots. -/
structure ExplicitNonConnectorSqInequalityCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  sqDist_ge_one :
    forall (i : Fin k) (u : LocalVertex)
      (j : Fin k) (v : LocalVertex),
        Ne i j ->
          Not (GeneratedSeparationFarApart.GeneratedCyclicConnectorPair
            hk i u j v) ->
            1 <=
              UnitVectorGeometry.sqDist
                (generatedLocalPoint F hk i u)
                (generatedLocalPoint F hk j v)

namespace ExplicitNonConnectorSqInequalityCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- The local lower table used by the far-apart wrapper. -/
def lower
    (_C : ExplicitNonConnectorSqInequalityCertificate F k hk) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun _i _u _j _v => 1

@[simp]
theorem lower_apply
    (C : ExplicitNonConnectorSqInequalityCertificate F k hk)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    C.lower i u j v = 1 :=
  rfl

/-- The explicit lower table is at least one on every non-connector
cross-block obligation. -/
theorem lower_ge_one
    (C : ExplicitNonConnectorSqInequalityCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
      hk C.lower := by
  intro _i _u _j _v _hij _hnot_connector
  exact le_rfl

/-- The supplied square inequalities say that the fixed lower value `1` is
bounded by the actual generated squared distance. -/
theorem lower_sq_bound
    (C : ExplicitNonConnectorSqInequalityCertificate F k hk) :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      C.lower := by
  intro i u j v hij hnot_connector
  simpa [lower, generatedLocalPoint] using
    C.sqDist_ge_one i u j v hij hnot_connector

/-- Projection from the explicit non-connector square inequalities to the
generated global separation hypothesis. -/
theorem generatedGlobalSeparation
    (C : ExplicitNonConnectorSqInequalityCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) := by
  have hperiod :
      PeriodInterface.GeneratedPeriodEquation
        F.transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (F.orientation k hk) := by
    simpa [ExactFamilyClosure.finiteOrientationWord] using
      (F.period k hk).toGeneratedPeriodEquation
  exact
    generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds_reduced
        F.transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (F.orientation k hk)
        hperiod
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
        (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
          F.transitions)
        C.lower C.lower_ge_one C.lower_sq_bound

end ExplicitNonConnectorSqInequalityCertificate

/-- Explicit square-inequality certificates for every positive block count. -/
structure ExplicitNonConnectorSqInequalityCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      ExplicitNonConnectorSqInequalityCertificate F k hk

namespace ExplicitNonConnectorSqInequalityCertificateFamily

variable {F : RoleHingedPeriodSearchFamily}

/-- Generated separation for every positive block count, projected directly
from the explicit inequalities. -/
theorem separated
    (C : ExplicitNonConnectorSqInequalityCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (C.certificate k hk).generatedGlobalSeparation

end ExplicitNonConnectorSqInequalityCertificateFamily

/-! ## Generated-polynomial route adapters -/

/-- Upper-triangle generated-point polynomial obligations in the W9 search
surface. -/
structure GeneratedPolynomialCertificate
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <=
              GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                F hk i u j v

namespace GeneratedPolynomialCertificate

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

def toGeneratedPointTable
    (C : GeneratedPolynomialCertificate F k hk) :
    GeneratedPointNonConnectorPolynomialTable F k hk where
  polynomial_ge_one_lt := C.polynomial_ge_one_lt

def toCrossBlockSqPolynomialTable
    (C : GeneratedPolynomialCertificate F k hk) :
    UpperTriangleNonConnectorPolynomialTable F k hk :=
  C.toGeneratedPointTable.toUpperTriangleNonConnectorPolynomialTable

def toNonConnectorSqDistanceTable
    (C : GeneratedPolynomialCertificate F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  C.toGeneratedPointTable.toNonConnectorSqDistanceTable

/-- The generated-polynomial lower-table route projects the W9 polynomial
obligations to generated global separation. -/
theorem generatedGlobalSeparation
    (C : GeneratedPolynomialCertificate F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointTable.generatedGlobalSeparation

end GeneratedPolynomialCertificate

/-- W9 polynomial certificates for all positive block counts. -/
structure GeneratedPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) where
  certificate :
    forall (k : Nat) (hk : 0 < k),
      GeneratedPolynomialCertificate F k hk

namespace GeneratedPolynomialCertificateFamily

variable {F : RoleHingedPeriodSearchFamily}

def toGeneratedPointTableFamily
    (C : GeneratedPolynomialCertificateFamily F) :
    GeneratedPointNonConnectorPolynomialTableFamily F where
  table := fun k hk => (C.certificate k hk).toGeneratedPointTable

def toNonConnectorSqDistanceTableFamily
    (C : GeneratedPolynomialCertificateFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toGeneratedPointTableFamily.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : GeneratedPolynomialCertificateFamily F) :
    CrossBlockLowerBounds F :=
  C.toGeneratedPointTableFamily.toCrossBlockLowerBounds

theorem separated
    (C : GeneratedPolynomialCertificateFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toGeneratedPointTableFamily.separated k hk

theorem targetUpperConstructionFiveSixteen
    (C : GeneratedPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toGeneratedPointTableFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : GeneratedPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end GeneratedPolynomialCertificateFamily

/-! ## Concrete value-matrix route adapters -/

namespace NonConnectorValueMatrix

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- A concrete value matrix is already a native non-connector square-value
table for the cross-block square-table search layer. -/
def toCrossBlockSqValueTable
    (M : NonConnectorValueMatrix F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk :=
  M.toSqValueTable

/-- Concrete value matrices project to generated global separation through
the connector-separated square-distance table route. -/
theorem generatedGlobalSeparation
    (M : NonConnectorValueMatrix F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  M.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end NonConnectorValueMatrix

namespace NonConnectorValueMatrixFamily

variable {F : RoleHingedPeriodSearchFamily}

theorem separated
    (M : NonConnectorValueMatrixFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  M.toNonConnectorSqDistanceTableFamily.separated k hk

end NonConnectorValueMatrixFamily

namespace CandidateValueMatrixFamily

/-- The viable candidate value-matrix route forgets to the generated
cross-block lower-bound facade. -/
def toCrossBlockLowerBounds
    (C : CandidateValueMatrixFamily) :
    CrossBlockLowerBounds C.toRoleHingedPeriodSearchFamily :=
  C.matrices.toCrossBlockLowerBounds

/-- Generated separation at a chosen positive block count from the candidate
value matrices. -/
theorem separated
    (C : CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (C.toRoleHingedPeriodSearchFamily.orientation k hk) :=
  NonConnectorValueMatrixFamily.separated C.matrices k hk

theorem targetUpperConstructionFiveSixteen
    (C : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCandidateValueCertificateFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end CandidateValueMatrixFamily

end

end CrossBlockLowerBoundSearchW9
end PachToth
end ErdosProblems1066
