import ErdosProblems1066.PachToth.NonRigidConnectorSeparationFacts
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.RoleHingeInterfaceRefinement
import ErdosProblems1066.PachToth.RoleHingeExactLocalFinite

set_option autoImplicit false

/-!
# Exact-target candidate closure

This module records the shortest currently honest Pach--Toth exact-target
route through the concrete connector-only role-hinge data.  The old
all-source same-block transition field is intentionally absent: it is already
known to be too strong for the concrete role-hinge maps.

The remaining record below keeps only certificate data:

* an all-positive finite orientation word family;
* the sixteen algebraic period equations for each word;
* the residual exact-local same-block checks not forced by the equilateral
  role-angle port pairs; and
* non-connector generated square-distance inequalities.

Generated closure, generated periods, global separation, orbit same-block
metric data, and the final exact target are all derived from those fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactTargetCandidateClosure

open FiniteGraph
open NonRigidConnectorSeparationFacts
open NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable
open RoleHingeInterfaceRefinement

noncomputable section

abbrev R2 := Prod Real Real
abbrev LocalVertexIndex := CrossBlockLowerBoundsInterface.LocalVertexIndex

/-- The same-branch residual exact-local rows left after the role-angle port
pairs are discharged. -/
abbrev SameExactLocalResidualField : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (RoleHingeConcreteSearch.samePlaceNext source u)
              (RoleHingeConcreteSearch.samePlaceNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- The opposite-branch residual exact-local rows left after the role-angle
port pairs are discharged. -/
abbrev OppositeExactLocalResidualField : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (RoleHingeConcreteSearch.oppositePlaceNext source u)
              (RoleHingeConcreteSearch.oppositePlaceNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- The exact-local residual fields required to extend the checked partial
period/non-connector package to the old full exact-local route. -/
structure ExactLocalResidualFields where
  same_rest : SameExactLocalResidualField
  opposite_rest : OppositeExactLocalResidualField

/-- The concrete connector-only Figure 2 transition obligations. -/
abbrev concreteObligations :
    Figure2Certificate.SameOppositeTransitionObligations :=
  RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations

/-- The generated point addressed by finite local-vertex indices for a
candidate word family. -/
def concreteGeneratedPoint
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex) : R2 :=
  GeneratedClosedChain.generatedPoint
    concreteObligations hk
    BaseTransitionRealization.exactBase
    ((word k hk).toFin)
    i
    (CrossBlockLowerBoundsInterface.localVertexOfIndex u)

/-- The concrete generated square-distance polynomial used by the reduced
non-connector certificate. -/
def concreteIndexedGeneratedSqDist
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  CrossBlockDistanceSqReduction.sqDist
    (concreteGeneratedPoint word hk i u)
    (concreteGeneratedPoint word hk j v)

/-- Minimal remaining certificate data for the current concrete exact-target
route.

The fields deliberately avoid redundant downstream wrappers such as generated
closure, generated separation, orbit metric hypotheses, or an already-bundled
target theorem. -/
structure MinimalExactTargetCertificate where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k),
      PeriodWordCertificates.AlgebraicEquationsForWord
        concreteObligations
        hk
        BaseTransitionRealization.exactBase
        (word k hk)
  same_rest :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.samePlaceNext source u)
                (RoleHingeConcreteSearch.samePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  opposite_rest :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.oppositePlaceNext source u)
                (RoleHingeConcreteSearch.oppositePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  nonConnectorSqDist_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
        Not (IndexedCyclicConnectorPair
            hk i u j v) ->
            1 <= concreteIndexedGeneratedSqDist word hk i u j v

/-- The checked portion of the exact-target candidate certificate that does
not include the residual exact-local same-block rows.

This is the usable partial package produced by period-word and non-connector
table searches.  The residual rows are intentionally supplied only at the final
extension step, because the current concrete role-hinge maps do not provide
those fields. -/
structure MinimalExactTargetPartialCertificate where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k),
      PeriodWordCertificates.AlgebraicEquationsForWord
        concreteObligations
        hk
        BaseTransitionRealization.exactBase
        (word k hk)
  nonConnectorSqDist_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (IndexedCyclicConnectorPair
            hk i u j v) ->
            1 <= concreteIndexedGeneratedSqDist word hk i u j v

namespace MinimalExactTargetPartialCertificate

/-- Extend the checked period/lower-table package to the full minimal
exact-target certificate when the residual exact-local rows are available. -/
def withExactLocalResiduals
    (P : MinimalExactTargetPartialCertificate)
    (same_rest : SameExactLocalResidualField)
    (opposite_rest : OppositeExactLocalResidualField) :
    MinimalExactTargetCertificate where
  word := P.word
  equation := P.equation
  same_rest := same_rest
  opposite_rest := opposite_rest
  nonConnectorSqDist_ge_one := P.nonConnectorSqDist_ge_one

/-- Extend a checked partial certificate using the bundled residual fields. -/
def withExactLocalResidualFields
    (P : MinimalExactTargetPartialCertificate)
    (R : ExactLocalResidualFields) :
    MinimalExactTargetCertificate :=
  P.withExactLocalResiduals R.same_rest R.opposite_rest

/-- The raw generated-chain orientation extracted from the stored word in the
partial certificate. -/
def orientation
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hk).toFin

@[simp]
theorem orientation_apply
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    P.orientation k hk i = P.word k hk i :=
  rfl

/-- The indexed algebraic period certificate rebuilt from the partial
certificate equations. -/
def indexedCertificate
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      concreteObligations
      BaseTransitionRealization.exactBase
      (PeriodWordCertificates.finiteOrientationWordOfWord hk
        (P.word k hk)) :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (P.word k hk)
    (P.equation k hk)

/-- The generated closure equation already follows from the partial
period-word data. -/
def closure
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (P.word k hk)
    (P.equation k hk)

/-- The generated final-block period equation already follows from the partial
period-word data. -/
def periodEquation
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (P.word k hk)
    (P.equation k hk)

/-- The generated-period hypothesis already follows from the partial
period-word data. -/
def period
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  PeriodWordCertificates.generatedPeriodOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (P.word k hk)
    (P.equation k hk)

/-- The stored finite-index square-distance facts in the partial certificate
give the local non-connector lower-bound predicate with the uniform lower
table `1`.  This is the strongest separation-side fact available without the
blocked residual exact-local rows. -/
theorem nonConnectorLower_bound
    (P : MinimalExactTargetPartialCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedNonConnectorCrossBlockDistanceLowerBounds
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (P.orientation k hk)
        (fun _i _u _j _v => (1 : Real)) := by
  intro i u j v hij hnot
  have hnotIndex :
      Not (IndexedCyclicConnectorPair
        hk i (CrossBlockLowerBoundsInterface.localVertexIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexIndex v)) :=
    not_indexedCyclicConnectorPair_of_not_cyclicConnectorPair
        hnot
  have hsq :
      1 <=
        concreteIndexedGeneratedSqDist P.word hk i
          (CrossBlockLowerBoundsInterface.localVertexIndex u)
          j
          (CrossBlockLowerBoundsInterface.localVertexIndex v) :=
    P.nonConnectorSqDist_ge_one k hk i
      (CrossBlockLowerBoundsInterface.localVertexIndex u)
      j
      (CrossBlockLowerBoundsInterface.localVertexIndex v)
      hij hnotIndex
  simpa [concreteIndexedGeneratedSqDist, concreteGeneratedPoint,
    orientation,
    CrossBlockLowerBoundsInterface.localVertexOfIndex_localVertexIndex] using
    CrossBlockDistanceSqReduction.one_le_root_eucDist_of_one_le_sqDist hsq

/-- The generated-chain family fixed by the partial certificate's concrete
transition obligations and stored word family. -/
def generatedChainFamily
    (P : MinimalExactTargetPartialCertificate) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _k _hk => concreteObligations
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := P.orientation

/-- Period data for the partial certificate's generated-chain family. -/
def periods
    (P : MinimalExactTargetPartialCertificate) :
    P.generatedChainFamily.Periods := by
  intro k hk
  exact P.period k hk

end MinimalExactTargetPartialCertificate

namespace MinimalExactTargetCertificate

/-- The raw generated-chain orientation extracted from the stored word. -/
def orientation
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (C.word k hk).toFin

@[simp]
theorem orientation_apply
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    C.orientation k hk i = C.word k hk i :=
  rfl

/-- The indexed algebraic period certificate rebuilt from the stored
equations. -/
def indexedCertificate
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      concreteObligations
      BaseTransitionRealization.exactBase
      (PeriodWordCertificates.finiteOrientationWordOfWord hk
        (C.word k hk)) :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (C.word k hk)
    (C.equation k hk)

/-- The algebraic closure equation derived from the stored period equations. -/
def closure
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (C.word k hk)
    (C.equation k hk)

/-- The generated final-block period equation derived from the stored period
equations. -/
def periodEquation
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (C.word k hk)
    (C.equation k hk)

/-- The generated-period hypothesis derived from the stored period equations. -/
def period
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  PeriodWordCertificates.generatedPeriodOfWord
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (C.word k hk)
    (C.equation k hk)

/-- The residual exact-local same-block certificates combine with the checked
equilateral role-angle port pairs to give the concrete generated-transition
same-block invariant. -/
theorem transitionExactLocalSqDistances
    (C : MinimalExactTargetCertificate) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      concreteObligations := by
  refine
    RoleHingeAngleCertificates.sameOppositeExactLocal_of_equilateralRoleAngles_obligations_eq
        concreteObligations
        RoleHingeConcreteSearch.samePlaceNext
        RoleHingeConcreteSearch.oppositePlaceNext
        RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations_samePlaceNext
        RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations_oppositePlaceNext
        ?sameRealizes ?oppositeRealizes
        C.same_rest C.opposite_rest
  case sameRealizes =>
    intro source u v role hrole
    simpa [RoleHingeConcreteSearch.samePlaceNext,
      RoleHingeConcreteSearch.sameRoleAngle_eq_sameEquilateralRoleAngle] using
      RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
        RoleHingeConcreteSearch.sameRoleAngle source u v role hrole
  case oppositeRealizes =>
    intro source u v role hrole
    simpa [RoleHingeConcreteSearch.oppositePlaceNext,
      RoleHingeConcreteSearch.oppositeRoleAngle_eq_oppositeEquilateralRoleAngle] using
      RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
        RoleHingeConcreteSearch.oppositeRoleAngle source u v role hrole

/-- Every generated block has the exact-local squared-distance table. -/
def orbitSqDistances
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) := by
  simpa [RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances] using
    RoleHingeSameBlockAlgebra.generatedOrbit_exactBase_matchesExactLocalSqDistances
      concreteObligations hk
      (C.orientation k hk)
      C.transitionExactLocalSqDistances

/-- Same-block isometry derived from the orbit exact-local invariant. -/
def sameBlockIsometry
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  RoleHingeInterfaceRefinement.generatedSameBlockIsometry_of_orbitSqDistances
    concreteObligations hk
    BaseTransitionRealization.exactBase
    (C.orientation k hk)
    (C.orbitSqDistances k hk)

/-- The stored finite-index square-distance facts give the local
non-connector distance lower-bound predicate with the uniform lower table
`1`. -/
theorem nonConnectorLower_bound
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedNonConnectorCrossBlockDistanceLowerBounds
        concreteObligations hk
        BaseTransitionRealization.exactBase
        (C.orientation k hk)
        (fun _i _u _j _v => (1 : Real)) := by
  intro i u j v hij hnot
  have hnotIndex :
      Not (IndexedCyclicConnectorPair
        hk i (CrossBlockLowerBoundsInterface.localVertexIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexIndex v)) :=
    not_indexedCyclicConnectorPair_of_not_cyclicConnectorPair
        hnot
  have hsq :
      1 <=
        concreteIndexedGeneratedSqDist C.word hk i
          (CrossBlockLowerBoundsInterface.localVertexIndex u)
          j
          (CrossBlockLowerBoundsInterface.localVertexIndex v) :=
    C.nonConnectorSqDist_ge_one k hk i
      (CrossBlockLowerBoundsInterface.localVertexIndex u)
      j
      (CrossBlockLowerBoundsInterface.localVertexIndex v)
      hij hnotIndex
  simpa [concreteIndexedGeneratedSqDist, concreteGeneratedPoint,
    orientation,
    CrossBlockLowerBoundsInterface.localVertexOfIndex_localVertexIndex] using
    CrossBlockDistanceSqReduction.one_le_root_eucDist_of_one_le_sqDist hsq

/-- Generated global separation derived from the non-connector square-distance
facts; cyclic connector slots use the checked connector-unit facts. -/
def separated
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk) :=
  generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
      concreteObligations hk
      BaseTransitionRealization.exactBase
      (C.orientation k hk)
      (C.periodEquation k hk)
      (C.sameBlockIsometry k hk)
      (fun _i _u _j _v => (1 : Real))
      (generatedNonConnectorCrossBlockLowerBoundsAtLeastOne_one hk)
      (C.nonConnectorLower_bound k hk)

/-- The generated-chain family fixed by the concrete transition obligations
and the stored word family. -/
def generatedChainFamily
    (C : MinimalExactTargetCertificate) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _k _hk => concreteObligations
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := C.orientation

/-- Period data for the generated-chain family. -/
def periods
    (C : MinimalExactTargetCertificate) :
    C.generatedChainFamily.Periods := by
  intro k hk
  exact C.period k hk

/-- Orbit-level metric data for the generated-chain family. -/
def orbitMetricHypotheses
    (C : MinimalExactTargetCertificate) :
    RoleHingeInterfaceRefinement.GeneratedChainFamilyOrbitSqDistanceHypotheses
      C.generatedChainFamily where
  separated := fun k hk => C.separated k hk
  orbit_sq_distances := fun k hk => C.orbitSqDistances k hk

/-- One exact block count from the minimal concrete certificate data. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : MinimalExactTargetCertificate)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_concreteExactBlock_of_generatedPeriod_orbitSqDistances
        hk
        (C.orientation k hk)
        (C.period k hk)
        (C.separated k hk)
        (C.orbitSqDistances k hk)

/-- Exact target from the minimal concrete certificate data.  This is
conditional on the record argument; no unconditional final Pach--Toth theorem
is asserted here. -/
theorem targetUpperConstructionFiveSixteen
    (C : MinimalExactTargetCertificate) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_generatedPeriod_family_orbitSqDistances
        C.generatedChainFamily
        C.periods
        C.orbitMetricHypotheses

end MinimalExactTargetCertificate

namespace MinimalExactTargetPartialCertificate

/-- Exact-block target from the checked partial package plus residual
exact-local rows. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : MinimalExactTargetPartialCertificate)
    (same_rest : SameExactLocalResidualField)
    (opposite_rest : OppositeExactLocalResidualField)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  (P.withExactLocalResiduals same_rest opposite_rest)
    |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact target from the checked partial package plus residual exact-local
rows. -/
theorem targetUpperConstructionFiveSixteen
    (P : MinimalExactTargetPartialCertificate)
    (same_rest : SameExactLocalResidualField)
    (opposite_rest : OppositeExactLocalResidualField) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (P.withExactLocalResiduals same_rest opposite_rest)
    |>.targetUpperConstructionFiveSixteen

end MinimalExactTargetPartialCertificate

/-- The current concrete same-branch role-hinge map blocks inhabitation of the
full minimal exact-target certificate: its `same_rest` field is exactly the
finite residual row family refuted in `RoleHingeExactLocalFinite`. -/
theorem not_minimalExactTargetCertificate :
    Not (Nonempty MinimalExactTargetCertificate) := by
  intro h
  cases h with
  | intro C =>
      exact RoleHingeExactLocalFinite.not_samePlaceNext_full_nonPortPair_rest
        C.same_rest

/-- The residual-field package needed by the old full exact-local route is
itself impossible: the same-branch residual field is refuted by the checked
`T1_1,r` exact-base row. -/
theorem not_exactLocalResidualFields :
    Not (Nonempty ExactLocalResidualFields) := by
  intro h
  cases h with
  | intro R =>
      exact RoleHingeExactLocalFinite.not_samePlaceNext_full_nonPortPair_rest
        R.same_rest

end

end ExactTargetCandidateClosure
end PachToth
end ErdosProblems1066
