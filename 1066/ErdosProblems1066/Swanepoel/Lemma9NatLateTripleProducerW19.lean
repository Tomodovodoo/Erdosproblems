import ErdosProblems1066.Swanepoel.Lemma9CoverageProducerW18

set_option autoImplicit false

/-!
# W19 Lemma 9 natural late-triple producer

This file closes the bookkeeping gap around the Lemma 9 late-triple input.
The concrete W16/W17 coverage row is equivalent to a checked Lemma 6/7
coverage package together with the finite natural-index
`M8NatLateTripleInputs` package.  For boundary-arc rows supplied by W18, the
remaining obligation is exactly the arc-budget identification plus that same
finite natural package.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9NatLateTripleProducerW19

open GraphBridge
open LateTriplesInterface
open Lemma6Lemma7AssemblyW13
open Lemma6NegativeAfterGapW12
open Lemma67ToBoundaryArcW14
open Lemma9CoverageConcreteW17
open Lemma9CoverageProducerW18
open Lemma9LateTriplesW16
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open PlanarInterface

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}
variable {B : PointwiseLemma89PreLateBase.{u} C hmin}

/-- The exact finite-natural plus coverage package needed to build the W16
Lemma 9 coverage-late row. -/
structure M8NatLateTripleCoverageInputs
    (B : PointwiseLemma89PreLateBase.{u} C hmin) where
  longArcCount : Nat
  coverage :
    GapNegativeCoverageData
      B.arcBoundaryBudget.planarBoundary longArcCount
  natLateTripleInputs :
    M8NatLateTripleInputs B.localLabels.predicates.data

namespace M8NatLateTripleCoverageInputs

variable (I : M8NatLateTripleCoverageInputs B)

/-- Forget coverage and retain the finite natural-index Lemma 9 package. -/
def toNatLateTripleInputs :
    M8NatLateTripleInputs B.localLabels.predicates.data :=
  I.natLateTripleInputs

/-- Convert the finite natural-index package into the row predicate fields
used by W17.  The coverage inequality argument is irrelevant after the
natural package has already proved lateness on the finite range. -/
def toRowPredicateCoverageFields :
    Lemma9RowPredicateCoverageFields B I.longArcCount where
  tripleStartPredicate := I.natLateTripleInputs.tripleStartPredicate
  predicate_of_tripleEquality :=
    I.natLateTripleInputs.predicate_of_tripleEquality
  late_of_predicate_of_coverage := by
    intro a ha1 ha2 _hcoverage hpred
    exact I.natLateTripleInputs.late_of_predicate a ha1 ha2 hpred

/-- The W17 concrete coverage row built from checked coverage and finite
natural-index Lemma 9 data. -/
def toCoverageConcreteRow :
    Lemma9CoverageConcreteRow B where
  longArcCount := I.longArcCount
  coverage := I.coverage
  predicateFields := I.toRowPredicateCoverageFields

/-- The W16 coverage-late row built from checked coverage and finite
natural-index Lemma 9 data. -/
def toPointwiseLemma9CoverageLateInputs :
    PointwiseLemma9CoverageLateInputs B :=
  I.toCoverageConcreteRow.toPointwiseLemma9CoverageLateInputs

/-- The concrete five-start facts consumed downstream by W15. -/
def fiveStartLateFacts :
    M8Lemma9FiveStartLateFacts B.localLabels.predicates.data :=
  I.toPointwiseLemma9CoverageLateInputs.fiveStartLateFacts

theorem degreeThree_le_negativeCount_add_longArcCount :
    B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.d3 <=
      B.arcBoundaryBudget.planarBoundary.outerBoundaryCounts.negativeCount +
        I.longArcCount :=
  I.coverage.degreeThree_le_negativeCount_add_longArcCount

@[simp]
theorem toRowPredicateCoverageFields_tripleStartPredicate :
    I.toRowPredicateCoverageFields.tripleStartPredicate =
      I.natLateTripleInputs.tripleStartPredicate :=
  rfl

@[simp]
theorem toCoverageConcreteRow_longArcCount :
    I.toCoverageConcreteRow.longArcCount = I.longArcCount :=
  rfl

@[simp]
theorem toPointwiseLemma9CoverageLateInputs_longArcCount :
    I.toPointwiseLemma9CoverageLateInputs.longArcCount = I.longArcCount :=
  rfl

@[simp]
theorem toPointwiseLemma9CoverageLateInputs_coverage :
    I.toPointwiseLemma9CoverageLateInputs.coverage = I.coverage :=
  rfl

end M8NatLateTripleCoverageInputs

/-- Extract the exact W19 finite-natural coverage package from the W16 row. -/
def natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs
    (H : PointwiseLemma9CoverageLateInputs B) :
    M8NatLateTripleCoverageInputs B where
  longArcCount := H.longArcCount
  coverage := H.coverage
  natLateTripleInputs := H.toNatLateTripleInputs

@[simp]
theorem natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs_longArcCount
    (H : PointwiseLemma9CoverageLateInputs B) :
    (natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs H).longArcCount =
      H.longArcCount :=
  rfl

@[simp]
theorem natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs_coverage
    (H : PointwiseLemma9CoverageLateInputs B) :
    (natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs H).coverage =
      H.coverage :=
  rfl

/-- Extract the exact W19 finite-natural coverage package from the W17 row. -/
def natLateTripleCoverageInputs_of_coverageConcreteRow
    (R : Lemma9CoverageConcreteRow B) :
    M8NatLateTripleCoverageInputs B :=
  natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs
    R.toPointwiseLemma9CoverageLateInputs

/-- Extract only the finite natural-index Lemma 9 package from a concrete row.
-/
def natLateTripleInputs_of_coverageConcreteRow
    (R : Lemma9CoverageConcreteRow B) :
    M8NatLateTripleInputs B.localLabels.predicates.data :=
  (natLateTripleCoverageInputs_of_coverageConcreteRow R).toNatLateTripleInputs

@[simp]
theorem natLateTripleCoverageInputs_of_coverageConcreteRow_longArcCount
    (R : Lemma9CoverageConcreteRow B) :
    (natLateTripleCoverageInputs_of_coverageConcreteRow R).longArcCount =
      R.longArcCount :=
  rfl

@[simp]
theorem natLateTripleCoverageInputs_of_coverageConcreteRow_coverage
    (R : Lemma9CoverageConcreteRow B) :
    (natLateTripleCoverageInputs_of_coverageConcreteRow R).coverage =
      R.coverage :=
  rfl

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable {Q : Lemma67BoundaryArcInput C D}

/-- Extract the finite natural-index Lemma 9 package from a W18/W17
boundary-arc predicate row. -/
def natLateTripleCoverageInputs_of_boundaryArcPredicateFields
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    M8NatLateTripleCoverageInputs B :=
  natLateTripleCoverageInputs_of_coverageConcreteRow F.toCoverageConcreteRow

@[simp]
theorem natLateTripleCoverageInputs_of_boundaryArcPredicateFields_longArcCount
    (F : Lemma67BoundaryArcPredicateFields B Q) :
    (natLateTripleCoverageInputs_of_boundaryArcPredicateFields F).longArcCount =
      Q.source.longArcCount :=
  rfl

/-- W18 reduced boundary-arc data, with W14 coverage inserted, is a W19
finite-natural coverage package. -/
def natLateTripleCoverageInputs_of_reducedPredicateInput
    (I : Lemma67BoundaryArcReducedPredicateInput B Q) :
    M8NatLateTripleCoverageInputs B :=
  natLateTripleCoverageInputs_of_coverageConcreteRow I.toCoverageConcreteRow

/-- Build W17 boundary-arc predicate fields directly from budget equality and
the finite natural-index Lemma 9 package. -/
def predicateFields_of_boundaryArcInput
    (arcBoundaryBudget_eq : Q.arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    Lemma67BoundaryArcPredicateFields B Q :=
  (Lemma67BoundaryArcReducedPredicateInput.mk
    arcBoundaryBudget_eq Hnat).toPredicateFields

/-- Build the concrete W17 coverage row directly from a W14 boundary-arc
input, budget equality, and finite natural-index Lemma 9 data. -/
def coverageConcreteRow_of_boundaryArcInput
    (arcBoundaryBudget_eq : Q.arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    Lemma9CoverageConcreteRow B :=
  (predicateFields_of_boundaryArcInput
    (B := B) (Q := Q) arcBoundaryBudget_eq Hnat).toCoverageConcreteRow

/-- Build the W16 coverage-late row directly from a W14 boundary-arc input,
budget equality, and finite natural-index Lemma 9 data. -/
def coverageLateInputs_of_boundaryArcInput
    (arcBoundaryBudget_eq : Q.arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    PointwiseLemma9CoverageLateInputs B :=
  (coverageConcreteRow_of_boundaryArcInput
    (B := B) (Q := Q) arcBoundaryBudget_eq Hnat)
      |>.toPointwiseLemma9CoverageLateInputs

@[simp]
theorem coverageConcreteRow_of_boundaryArcInput_longArcCount
    (arcBoundaryBudget_eq : Q.arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    (coverageConcreteRow_of_boundaryArcInput
      (B := B) (Q := Q) arcBoundaryBudget_eq Hnat).longArcCount =
        Q.source.longArcCount :=
  rfl

@[simp]
theorem coverageLateInputs_of_boundaryArcInput_longArcCount
    (arcBoundaryBudget_eq : Q.arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    (coverageLateInputs_of_boundaryArcInput
      (B := B) (Q := Q) arcBoundaryBudget_eq Hnat).longArcCount =
        Q.source.longArcCount :=
  rfl

/-- Exact row-level closure: the W16 coverage-late row is equivalent to
checked coverage for some long-arc count plus the finite natural-index
Lemma 9 package. -/
theorem nonempty_pointwiseCoverageLateInputs_iff_natCoverageInputs :
    Nonempty (PointwiseLemma9CoverageLateInputs B) <->
      Nonempty (M8NatLateTripleCoverageInputs B) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H =>
        exact
          Nonempty.intro
            (natLateTripleCoverageInputs_of_pointwiseCoverageLateInputs H)
  case mpr =>
    intro h
    cases h with
    | intro I =>
        exact Nonempty.intro I.toPointwiseLemma9CoverageLateInputs

/-- Exact W17 closure: a concrete coverage row is equivalent to the W19
finite-natural coverage package. -/
theorem nonempty_coverageConcreteRow_iff_natCoverageInputs :
    Nonempty (Lemma9CoverageConcreteRow B) <->
      Nonempty (M8NatLateTripleCoverageInputs B) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact
          Nonempty.intro
            (natLateTripleCoverageInputs_of_coverageConcreteRow R)
  case mpr =>
    intro h
    cases h with
    | intro I =>
        exact Nonempty.intro I.toCoverageConcreteRow

/-- Plain statement of the W19 residual obligations for a pointwise row:
some checked Lemma 6/7 coverage package and the finite natural-index Lemma 9
package. -/
theorem nonempty_natCoverageInputs_iff_exists_coverage_and_nat :
    Nonempty (M8NatLateTripleCoverageInputs B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          Nonempty
            (M8NatLateTripleInputs B.localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro I =>
        exact
          Exists.intro I.longArcCount
            (And.intro
              (Nonempty.intro I.coverage)
              (Nonempty.intro I.natLateTripleInputs))
  case mpr =>
    intro h
    cases h with
    | intro longArcCount hlong =>
        cases hlong.1 with
        | intro coverage =>
            cases hlong.2 with
            | intro Hnat =>
                exact
                  Nonempty.intro
                    ({ longArcCount := longArcCount
                       coverage := coverage
                       natLateTripleInputs := Hnat } :
                      M8NatLateTripleCoverageInputs B)

/-- Fully unfolded row-level closure for the W16 input row. -/
theorem nonempty_pointwiseCoverageLateInputs_iff_exists_coverage_and_nat :
    Nonempty (PointwiseLemma9CoverageLateInputs B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          Nonempty
            (M8NatLateTripleInputs B.localLabels.predicates.data) := by
  exact
    nonempty_pointwiseCoverageLateInputs_iff_natCoverageInputs.trans
      nonempty_natCoverageInputs_iff_exists_coverage_and_nat

/-- Fully unfolded row-level closure for the W17 concrete coverage row. -/
theorem nonempty_coverageConcreteRow_iff_exists_coverage_and_nat :
    Nonempty (Lemma9CoverageConcreteRow B) <->
      exists longArcCount : Nat,
        Nonempty
          (GapNegativeCoverageData
            B.arcBoundaryBudget.planarBoundary longArcCount) /\
          Nonempty
            (M8NatLateTripleInputs B.localLabels.predicates.data) := by
  exact
    nonempty_coverageConcreteRow_iff_natCoverageInputs.trans
      nonempty_natCoverageInputs_iff_exists_coverage_and_nat

/-- Strongest boundary-arc W18 closure: once W14 supplies the boundary-arc
carrier, producing W17 predicate fields is exactly budget equality plus the
finite natural-index Lemma 9 package. -/
theorem nonempty_boundaryArcPredicateFields_iff_budgetEq_and_nat :
    Nonempty (Lemma67BoundaryArcPredicateFields B Q) <->
      Q.arcBoundaryBudget = B.arcBoundaryBudget /\
        Nonempty (M8NatLateTripleInputs B.localLabels.predicates.data) := by
  constructor
  case mp =>
    intro h
    have hred :
        Nonempty (Lemma67BoundaryArcReducedPredicateInput B Q) :=
      (nonempty_predicateFields_iff_reducedPredicateInput
        (B := B) (Q := Q)).mp h
    cases hred with
    | intro I =>
        exact
          And.intro I.arcBoundaryBudget_eq
            (Nonempty.intro I.natLateTripleInputs)
  case mpr =>
    intro h
    cases h.2 with
    | intro Hnat =>
        have hred :
            Nonempty (Lemma67BoundaryArcReducedPredicateInput B Q) :=
          Nonempty.intro
            ({ arcBoundaryBudget_eq := h.1
               natLateTripleInputs := Hnat } :
              Lemma67BoundaryArcReducedPredicateInput B Q)
        exact
          (nonempty_predicateFields_iff_reducedPredicateInput
            (B := B) (Q := Q)).mpr hred

section BoundaryWalk

variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {P : OuterBoundaryCore (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable
  {walk :
    BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping P IsTriangle
      IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  walk.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= walk.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon ->
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable
  {O :
    BoundaryWalkLemma6Obstruction walk geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData}

/-- Boundary-walk specialization of the W19 residual-obligation equivalence.
-/
theorem nonempty_boundaryWalkPredicateFields_iff_budgetEq_and_nat
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary) :
    Nonempty
      (Lemma67BoundaryArcPredicateFields B
        (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
          Qwalk boundaryArc)) <->
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc).arcBoundaryBudget = B.arcBoundaryBudget /\
        Nonempty
          (M8NatLateTripleInputs B.localLabels.predicates.data) :=
  nonempty_boundaryArcPredicateFields_iff_budgetEq_and_nat
    (B := B)
    (Q :=
      Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc)

end BoundaryWalk

end Lemma9NatLateTripleProducerW19
end Swanepoel
end ErdosProblems1066

end
