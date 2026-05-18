import ErdosProblems1066.PachToth.GeneratedPointNormalizationW10
import ErdosProblems1066.PachToth.GeneratedPointPolynomialFacts
import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.PolynomialCertificateExtraction
import ErdosProblems1066.PachToth.GeneratedMetricClosure

set_option autoImplicit false

/-!
# W11 generated-point certificate package

This module is a certificate-facing facade.  It adds no numeric data: callers
provide normalized generated-point polynomial fields, normalized value/equality
fields, or raw cross-block lower-bound fields, and the adapters below route
those fields to the existing separation and closed-placement interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPointCertificateW11

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingedPeriodSearchFamily :=
  GeneratedPointNormalizationW10.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  GeneratedPointNormalizationW10.LocalVertexIndex

abbrev UpperTrianglePosition :=
  GeneratedPointNormalizationW10.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  GeneratedPointNormalizationW10.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  GeneratedPointNormalizationW10.IndexedCyclicConnectorPair hk i u j v

abbrev NormalizedPositionPolynomialCertificate :=
  GeneratedPointNormalizationW10.NormalizedGeneratedPointPositionPolynomialCertificate

abbrev NormalizedPositionValueCertificate :=
  GeneratedPointNormalizationW10.NormalizedGeneratedPointPositionValueCertificate

abbrev NormalizedPositionPolynomialCertificateFamily :=
  GeneratedPointNormalizationW10.NormalizedGeneratedPointPositionPolynomialCertificateFamily

abbrev NormalizedPositionValueCertificateFamily :=
  GeneratedPointNormalizationW10.NormalizedGeneratedPointPositionValueCertificateFamily

abbrev GeneratedPointPositionPolynomialCertificate :=
  PolynomialCertificateExtraction.GeneratedPointPositionPolynomialCertificate

abbrev GeneratedPointPositionValueCertificate :=
  PolynomialCertificateExtraction.GeneratedPointPositionValueCertificate

abbrev GeneratedPointPolynomialCertificateFamily :=
  PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily

abbrev GeneratedPointValueCertificateFamily :=
  PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily

abbrev GeneratedPointNonConnectorPolynomialTableFamily :=
  PolynomialCertificateExtraction.GeneratedPointNonConnectorPolynomialTableFamily

abbrev NonConnectorValueMatrixFamily :=
  PolynomialCertificateExtraction.NonConnectorValueMatrixFamily

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  PolynomialCertificateExtraction.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  PolynomialCertificateExtraction.CrossBlockLowerBounds

abbrev RoleHingedGeneratedClosureFamily :=
  GeneratedMetricClosure.RoleHingedGeneratedClosureFamily

/-- Normalized generated-point polynomial attached to a packed
upper-triangle position. -/
def normalizedPositionPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) : Real :=
  GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
    F.transitions.toFigure2TransitionObligations
    hk BaseTransitionRealization.exactBase (F.orientation k hk)
    p.left
    (CrossBlockLowerBoundsInterface.localVertexOfIndex p.leftVertex)
    p.right
    (CrossBlockLowerBoundsInterface.localVertexOfIndex p.rightVertex)

/-- Normalized generated-point square distance attached to a packed
upper-triangle position. -/
def normalizedPositionSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) : Real :=
  GeneratedPointPolynomialFacts.normalizedGeneratedPointSqDist
    F.transitions.toFigure2TransitionObligations
    hk BaseTransitionRealization.exactBase (F.orientation k hk)
    p.left
    (CrossBlockLowerBoundsInterface.localVertexOfIndex p.leftVertex)
    p.right
    (CrossBlockLowerBoundsInterface.localVertexOfIndex p.rightVertex)

/-- Packed positions normalize to the existing upper-triangle polynomial. -/
theorem normalizedPositionPolynomial_eq_upperTrianglePolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) :
    normalizedPositionPolynomial F hk p = p.polynomial F hk := by
  exact
    (GeneratedPointNormalizationW10.upperTrianglePosition_polynomial_eq_normalizedGeneratedPoint
      F hk p).symm

/-- Packed position square distances normalize to the existing
upper-triangle square distance. -/
theorem normalizedPositionSqDist_eq_upperTriangleSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) :
    normalizedPositionSqDist F hk p = p.sqDist F hk := by
  exact
    (GeneratedPointNormalizationW10.upperTrianglePosition_sqDist_eq_normalizedGeneratedPoint
      F hk p).symm

/-- At packed positions, the normalized square distance and polynomial agree. -/
theorem normalizedPositionSqDist_eq_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (p : UpperTrianglePosition k) :
    normalizedPositionSqDist F hk p =
      normalizedPositionPolynomial F hk p := by
  simp [normalizedPositionSqDist, normalizedPositionPolynomial]

/-- The algebraic closure equation supplied by the role-hinged period-search
certificate at one block count. -/
def generatedClosureEquation
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.period k hk).toGeneratedClosureEquation

abbrev GeneratedGlobalSeparationAt
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedGlobalSeparation
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)

/-- Reduced metric data obtained from generated separation and the checked
role-hinged same-block facts. -/
def reducedMetricHypothesesOfSeparation
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (separated : GeneratedGlobalSeparationAt F k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    F.transitions hk (F.orientation k hk) separated

/-- One-period route from generated separation to the transition
closed-placement certificate. -/
def explicitTransitionClosedPlacementCertificateOfSeparation
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (separated : GeneratedGlobalSeparationAt F k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  GeneratedMetricClosure.explicitTransitionClosedPlacementCertificate
    F.transitions hk (F.orientation k hk)
    (generatedClosureEquation F k hk) separated

/-- One-period route from generated separation to a closed placement. -/
def closedPlacementOfSeparation
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (separated : GeneratedGlobalSeparationAt F k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  GeneratedMetricClosure.closedPlacement
    F.transitions hk (F.orientation k hk)
    (generatedClosureEquation F k hk) separated

/-- Existence form of the one-period closed-placement route. -/
theorem exists_closedPlacement_of_separation
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (separated : GeneratedGlobalSeparationAt F k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint
          F.transitions.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase (F.orientation k hk) := by
  exact
    GeneratedMetricClosure.exists_closedPlacement
      F.transitions hk (F.orientation k hk)
      (generatedClosureEquation F k hk) separated

/-- Exact-block target from one-period generated separation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_separation
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (separated : GeneratedGlobalSeparationAt F k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedMetricClosure.targetUpperConstructionFiveSixteenAt_exactBlock
      F.transitions hk (F.orientation k hk)
      (generatedClosureEquation F k hk) separated

/-! ## Normalized polynomial fields -/

/-- Fields required from a normalized generated-point polynomial checker. -/
structure NormalizedPolynomialFields
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (p : UpperTrianglePosition k),
        PositionNonConnector hk p ->
          1 <= normalizedPositionPolynomial F hk p

namespace NormalizedPolynomialFields

variable {F : RoleHingedPeriodSearchFamily}

def toNormalizedPositionPolynomialCertificateFamily
    (C : NormalizedPolynomialFields F) :
    NormalizedPositionPolynomialCertificateFamily F where
  certificate := fun k hk =>
    { polynomial_ge_one := by
        intro p hp
        simpa [normalizedPositionPolynomial] using
          C.polynomial_ge_one k hk p hp }

def toGeneratedPointPolynomialCertificateFamily
    (C : NormalizedPolynomialFields F) :
    GeneratedPointPolynomialCertificateFamily F :=
  C.toNormalizedPositionPolynomialCertificateFamily
    |>.toGeneratedPointPolynomialCertificateFamily

def toGeneratedPointNonConnectorPolynomialTableFamily
    (C : NormalizedPolynomialFields F) :
    GeneratedPointNonConnectorPolynomialTableFamily F :=
  C.toNormalizedPositionPolynomialCertificateFamily
    |>.toGeneratedPointNonConnectorPolynomialTableFamily

def toNonConnectorSqDistanceTableFamily
    (C : NormalizedPolynomialFields F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  C.toNormalizedPositionPolynomialCertificateFamily
    |>.toNonConnectorSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : NormalizedPolynomialFields F) :
    CrossBlockLowerBounds F :=
  C.toNormalizedPositionPolynomialCertificateFamily
    |>.toCrossBlockLowerBounds

theorem separated
    (C : NormalizedPolynomialFields F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  C.toNormalizedPositionPolynomialCertificateFamily.separated k hk

def toRoleHingedGeneratedClosureFamily
    (C : NormalizedPolynomialFields F) :
    RoleHingedGeneratedClosureFamily :=
  C.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

def closedPlacementFamily
    (C : NormalizedPolynomialFields F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  C.toRoleHingedGeneratedClosureFamily.closedPlacementFamily

theorem exists_closedPlacement_and_target
    (C : NormalizedPolynomialFields F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint
              F.transitions.toFigure2TransitionObligations
              hk BaseTransitionRealization.exactBase (F.orientation k hk))
      PachToth.targetUpperConstructionFiveSixteen :=
  C.toRoleHingedGeneratedClosureFamily.exists_closedPlacement_and_target

theorem targetUpperConstructionFiveSixteen
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end NormalizedPolynomialFields

/-! ## Normalized value and equality fields -/

/-- Fields required from a normalized generated-point value checker. -/
structure NormalizedValueFields
    (F : RoleHingedPeriodSearchFamily) where
  value :
    forall (k : Nat) (_hk : 0 < k),
      UpperTrianglePosition k -> Real
  value_eq_normalizedPositionPolynomial :
    forall (k : Nat) (hk : 0 < k)
      (p : UpperTrianglePosition k),
        PositionNonConnector hk p ->
          value k hk p = normalizedPositionPolynomial F hk p
  value_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (p : UpperTrianglePosition k),
        PositionNonConnector hk p -> 1 <= value k hk p

namespace NormalizedValueFields

variable {F : RoleHingedPeriodSearchFamily}

def toNormalizedPolynomialFields
    (C : NormalizedValueFields F) :
    NormalizedPolynomialFields F where
  polynomial_ge_one := by
    intro k hk p hp
    have hvalue := C.value_eq_normalizedPositionPolynomial k hk p hp
    have hge := C.value_ge_one k hk p hp
    simpa [hvalue] using hge

def toNormalizedPositionValueCertificateFamily
    (C : NormalizedValueFields F) :
    NormalizedPositionValueCertificateFamily F where
  certificate := fun k hk =>
    { value := C.value k hk
      value_eq_normalizedGeneratedPointPolynomial := by
        intro p hp
        simpa [normalizedPositionPolynomial] using
          C.value_eq_normalizedPositionPolynomial k hk p hp
      value_ge_one := by
        intro p hp
        exact C.value_ge_one k hk p hp }

def toGeneratedPointValueCertificateFamily
    (C : NormalizedValueFields F) :
    GeneratedPointValueCertificateFamily F :=
  C.toNormalizedPositionValueCertificateFamily
    |>.toGeneratedPointValueCertificateFamily

def toGeneratedPointPolynomialCertificateFamily
    (C : NormalizedValueFields F) :
    GeneratedPointPolynomialCertificateFamily F :=
  C.toGeneratedPointValueCertificateFamily
    |>.toGeneratedPointPolynomialCertificateFamily

def toNonConnectorValueMatrixFamily
    (C : NormalizedValueFields F) :
    NonConnectorValueMatrixFamily F :=
  C.toNormalizedPositionValueCertificateFamily
    |>.toNonConnectorValueMatrixFamily

def toCrossBlockLowerBounds
    (C : NormalizedValueFields F) :
    CrossBlockLowerBounds F :=
  C.toNormalizedPositionValueCertificateFamily.toCrossBlockLowerBounds

theorem separated
    (C : NormalizedValueFields F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  C.toNormalizedPositionValueCertificateFamily.separated k hk

def toRoleHingedGeneratedClosureFamily
    (C : NormalizedValueFields F) :
    RoleHingedGeneratedClosureFamily :=
  C.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

def closedPlacementFamily
    (C : NormalizedValueFields F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  C.toRoleHingedGeneratedClosureFamily.closedPlacementFamily

theorem exists_closedPlacement_and_target
    (C : NormalizedValueFields F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint
              F.transitions.toFigure2TransitionObligations
              hk BaseTransitionRealization.exactBase (F.orientation k hk))
      PachToth.targetUpperConstructionFiveSixteen :=
  C.toRoleHingedGeneratedClosureFamily.exists_closedPlacement_and_target

theorem targetUpperConstructionFiveSixteen
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end NormalizedValueFields

/-! ## Raw lower-bound fields -/

/-- Fields required from a raw cross-block lower-bound checker. -/
structure LowerBoundFields
    (F : RoleHingedPeriodSearchFamily) where
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j -> 1 <= lower k hk i u j v
  lower_bound :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          lower k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                F.transitions.toFigure2TransitionObligations hk
                BaseTransitionRealization.exactBase
                (F.orientation k hk) i u)
              (GeneratedClosedChain.generatedPoint
                F.transitions.toFigure2TransitionObligations hk
                BaseTransitionRealization.exactBase
                (F.orientation k hk) j v)

namespace LowerBoundFields

variable {F : RoleHingedPeriodSearchFamily}

def toCrossBlockLowerBounds
    (C : LowerBoundFields F) :
    CrossBlockLowerBounds F where
  lower := C.lower
  lower_ge_one := C.lower_ge_one
  lower_bound := C.lower_bound

theorem separated
    (C : LowerBoundFields F)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt F k hk :=
  C.toCrossBlockLowerBounds.separated k hk

def toRoleHingedGeneratedClosureFamily
    (C : LowerBoundFields F) :
    RoleHingedGeneratedClosureFamily :=
  C.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

def closedPlacementFamily
    (C : LowerBoundFields F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  C.toRoleHingedGeneratedClosureFamily.closedPlacementFamily

theorem exists_closedPlacement_and_target
    (C : LowerBoundFields F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint
              F.transitions.toFigure2TransitionObligations
              hk BaseTransitionRealization.exactBase (F.orientation k hk))
      PachToth.targetUpperConstructionFiveSixteen :=
  C.toRoleHingedGeneratedClosureFamily.exists_closedPlacement_and_target

theorem targetUpperConstructionFiveSixteen
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end LowerBoundFields

end

end GeneratedPointCertificateW11
end PachToth
end ErdosProblems1066
