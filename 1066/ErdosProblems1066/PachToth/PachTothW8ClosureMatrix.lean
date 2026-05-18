import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable
import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.ExactTargetCandidateClosure
import ErdosProblems1066.PachToth.FiniteCertificateSearchSurface
import ErdosProblems1066.PachToth.PachTothRemainingMatrix
import ErdosProblems1066.PachToth.RoleHingeExactLocalFinite

set_option autoImplicit false

/-!
# W8 Pach--Toth closure matrix

This module consolidates the W7/W8 concrete Pach--Toth route facts into a
single remaining-obligation matrix.  It deliberately contains no
unconditional proof of the final `5 / 16` target.  Each public projection
theorem takes a concrete data package whose fields include the relevant
transition, period, same-block exact-local, and lower-table obligations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW8ClosureMatrix

noncomputable section

open FiniteCertificateSearchSurface

/-- A row in the W8 matrix: once an input package is supplied, it projects to
both public Pach--Toth targets. -/
structure ProjectionRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget : alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- The four concrete obligations that are still genuinely needed by the
connector-separated route. -/
structure RemainingObligationChecklist where
  concreteTransitions : Prop
  periodEquations : Prop
  exactLocalTransitionRows : Prop
  nonConnectorLowerTables : Prop

/-- The precise checklist for the current concrete connector route.  The
transition maps are fixed by the concrete same/opposite role-hinge data, while
the period equations, exact-local residual rows, and non-connector lower
tables remain fields of the concrete data packages below. -/
def concreteChecklist : RemainingObligationChecklist where
  concreteTransitions :=
    PachTothRemainingMatrix.concreteConnectorTransitions =
      RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations
  periodEquations := True
  exactLocalTransitionRows := True
  nonConnectorLowerTables := True

/-- The fixed concrete connector maps are present. -/
theorem concreteTransitions_present :
    concreteChecklist.concreteTransitions := by
  rfl

/-- The current four-target same-branch concrete map does not by itself
discharge the full residual exact-local same-block field.  This keeps the W8
matrix honest: downstream target projections require a data package carrying
that missing field. -/
theorem currentFourTargetMap_does_not_supply_full_sameRest :
    Not
      (forall source : FiniteGraph.LocalVertex -> Prod Real Real,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : FiniteGraph.LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.samePlaceNext source u)
                  (RoleHingeConcreteSearch.samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :=
  RoleHingeExactLocalFinite.not_samePlaceNext_full_nonPortPair_rest

abbrev MinimalExactTargetCertificate :=
  ExactTargetCandidateClosure.MinimalExactTargetCertificate

abbrev ConcreteRemainingData :=
  PachTothRemainingMatrix.ConcreteRemainingData

abbrev ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily

abbrev SearchSurfacePeriodFamily :=
  RoleHingedPeriodSearchFamily

abbrev SearchSurfaceVectorFamily
    (F : SearchSurfacePeriodFamily) :=
  UpperTriangleNonConnectorSqValueVectorCertificateFamily F

abbrev SearchSurfaceListFamily
    (F : SearchSurfacePeriodFamily) :=
  UpperTriangleNonConnectorSqValueListCertificateFamily F

/-- The minimal W8 certificate row.  This is the most direct concrete record:
orientation words, period equations, residual same-block rows, and
non-connector square-distance inequalities. -/
def minimalExactTargetCertificateRow :
    ProjectionRow MinimalExactTargetCertificate where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      C.targetUpperConstructionFiveSixteen

/-- The W8 concrete remaining-data row.  It keeps the concrete connector maps
fixed and requires the period, exact-local transition, and non-connector table
fields explicitly. -/
def concreteRemainingDataRow :
    ProjectionRow ConcreteRemainingData where
  exactTarget := fun D =>
    D.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun D =>
    D.targetUpperConstructionFiveSixteenArbitrary

/-- The concrete period-search/non-connector lower-table row.  The supplied
period-search package carries the period data; the supplied table family
carries the remaining finite lower-table data. -/
def concreteNonConnectorLowerTableFamilyRow :
    ProjectionRow ConcreteNonConnectorLowerTableFamily where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- A vector-backed finite-search surface row for a fully supplied
role-hinged period-search family. -/
def searchSurfaceVectorFamilyRow
    (F : SearchSurfacePeriodFamily) :
    ProjectionRow (SearchSurfaceVectorFamily F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- A list-backed finite-search surface row for a fully supplied role-hinged
period-search family. -/
def searchSurfaceListFamilyRow
    (F : SearchSurfacePeriodFamily) :
    ProjectionRow (SearchSurfaceListFamily F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- The consolidated W8 matrix.  Every target-producing row is conditional on
a concrete data structure that includes the required period and lower-table
payloads; the matrix itself does not contain such data. -/
structure Matrix where
  checklist : RemainingObligationChecklist
  checklistConcreteTransitions : checklist.concreteTransitions
  minimalExactTargetCertificate : ProjectionRow MinimalExactTargetCertificate
  concreteRemainingData : ProjectionRow ConcreteRemainingData
  concreteNonConnectorLowerTableFamily :
    ProjectionRow ConcreteNonConnectorLowerTableFamily
  searchSurfaceVectorFamily :
    forall F : SearchSurfacePeriodFamily,
      ProjectionRow (SearchSurfaceVectorFamily F)
  searchSurfaceListFamily :
    forall F : SearchSurfacePeriodFamily,
      ProjectionRow (SearchSurfaceListFamily F)

/-- The checked W8 matrix of projection routes. -/
def matrix : Matrix where
  checklist := concreteChecklist
  checklistConcreteTransitions := concreteTransitions_present
  minimalExactTargetCertificate := minimalExactTargetCertificateRow
  concreteRemainingData := concreteRemainingDataRow
  concreteNonConnectorLowerTableFamily := concreteNonConnectorLowerTableFamilyRow
  searchSurfaceVectorFamily := searchSurfaceVectorFamilyRow
  searchSurfaceListFamily := searchSurfaceListFamilyRow

/-- Exact target from the minimal concrete W8 certificate. -/
theorem targetUpperConstructionFiveSixteen_of_minimalExactTargetCertificate
    (C : MinimalExactTargetCertificate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.minimalExactTargetCertificate.exactTarget C

/-- Arbitrary target from the minimal concrete W8 certificate. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_minimalExactTargetCertificate
    (C : MinimalExactTargetCertificate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.minimalExactTargetCertificate.arbitraryTarget C

/-- Exact target from the concrete remaining-data package. -/
theorem targetUpperConstructionFiveSixteen_of_concreteRemainingData
    (D : ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteRemainingData.exactTarget D

/-- Arbitrary target from the concrete remaining-data package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteRemainingData
    (D : ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteRemainingData.arbitraryTarget D

/-- Exact target from concrete period-search data plus non-connector lower
tables. -/
theorem targetUpperConstructionFiveSixteen_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteNonConnectorLowerTableFamily.exactTarget C

/-- Arbitrary target from concrete period-search data plus non-connector
lower tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteNonConnectorLowerTableFamily.arbitraryTarget C

/-- Exact target from vector-backed search-surface certificates over a fully
supplied role-hinged period-search family. -/
theorem targetUpperConstructionFiveSixteen_of_searchSurfaceVectorFamily
    {F : SearchSurfacePeriodFamily}
    (C : SearchSurfaceVectorFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.searchSurfaceVectorFamily F).exactTarget C

/-- Arbitrary target from vector-backed search-surface certificates over a
fully supplied role-hinged period-search family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_searchSurfaceVectorFamily
    {F : SearchSurfacePeriodFamily}
    (C : SearchSurfaceVectorFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.searchSurfaceVectorFamily F).arbitraryTarget C

/-- Exact target from list-backed search-surface certificates over a fully
supplied role-hinged period-search family. -/
theorem targetUpperConstructionFiveSixteen_of_searchSurfaceListFamily
    {F : SearchSurfacePeriodFamily}
    (C : SearchSurfaceListFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.searchSurfaceListFamily F).exactTarget C

/-- Arbitrary target from list-backed search-surface certificates over a fully
supplied role-hinged period-search family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_searchSurfaceListFamily
    {F : SearchSurfacePeriodFamily}
    (C : SearchSurfaceListFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.searchSurfaceListFamily F).arbitraryTarget C

end

end PachTothW8ClosureMatrix
end PachToth
end ErdosProblems1066
