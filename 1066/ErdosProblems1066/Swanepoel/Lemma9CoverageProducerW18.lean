import ErdosProblems1066.Swanepoel.Lemma9CoverageConcreteW17

set_option autoImplicit false

/-!
# W18 Lemma 9 coverage producer

This file keeps the Lemma 6/7 boundary-walk coverage row separate from the
remaining Lemma 9 predicate content.  The checked producer below says that the
W14/W17 coverage packages build the concrete coverage-late row as soon as the
finite Lemma 9 natural-index predicate package is supplied.  The final
nonempty equivalence records the precise residual obligation: producing
`Lemma67BoundaryArcPredicateFields` is the same as producing the budget
identification plus those finite predicate inputs.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma9CoverageProducerW18

open GraphBridge
open LateTriplesInterface
open Lemma6Lemma7AssemblyW13
open Lemma67ToBoundaryArcW14
open Lemma9CoverageConcreteW17
open Lemma9LateTriplesW16
open MinimalGraphFacts
open PlanarInterface

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}
variable {B : PointwiseLemma89PreLateBase.{u} C hmin}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (Lemma67ToBoundaryArcW14.CanonicalGraph C)}
variable {Q : Lemma67BoundaryArcInput C D}

/-- The exact residual Lemma 9 predicate input after W14 has supplied the
boundary-arc and Lemma 6/7 coverage packages. -/
structure Lemma67BoundaryArcReducedPredicateInput
    (B : PointwiseLemma89PreLateBase.{u} C hmin)
    (Q : Lemma67BoundaryArcInput C D) where
  arcBoundaryBudget_eq :
    Q.arcBoundaryBudget = B.arcBoundaryBudget
  natLateTripleInputs :
    M8NatLateTripleInputs B.localLabels.predicates.data

namespace Lemma67BoundaryArcReducedPredicateInput

variable
  (I : Lemma67BoundaryArcReducedPredicateInput B Q)

/-- Produce the W17 predicate-field record from the reduced finite Lemma 9
predicate input.  The supplied coverage inequality is intentionally unused
here: Lemma 6/7 chooses the coverage row, while the finite Lemma 9 input proves
that the recorded predicate can occur only at late starts. -/
def toPredicateFields :
    Lemma67BoundaryArcPredicateFields B Q where
  arcBoundaryBudget_eq := I.arcBoundaryBudget_eq
  tripleStartPredicate := I.natLateTripleInputs.tripleStartPredicate
  predicate_of_tripleEquality :=
    I.natLateTripleInputs.predicate_of_tripleEquality
  late_of_predicate_of_coverage := by
    intro a ha1 ha2 _hcoverage hpred
    exact I.natLateTripleInputs.late_of_predicate a ha1 ha2 hpred

/-- The W17 concrete row produced by W14 Lemma 6/7 coverage plus the reduced
finite Lemma 9 predicate input. -/
def toCoverageConcreteRow :
    Lemma9CoverageConcreteRow B :=
  I.toPredicateFields.toCoverageConcreteRow

/-- The W16 coverage-late input row produced by W14 Lemma 6/7 coverage plus
the reduced finite Lemma 9 predicate input. -/
def toPointwiseLemma9CoverageLateInputs :
    PointwiseLemma9CoverageLateInputs B :=
  I.toCoverageConcreteRow.toPointwiseLemma9CoverageLateInputs

@[simp]
theorem toPredicateFields_tripleStartPredicate :
    I.toPredicateFields.tripleStartPredicate =
      I.natLateTripleInputs.tripleStartPredicate :=
  rfl

@[simp]
theorem toCoverageConcreteRow_longArcCount :
    I.toCoverageConcreteRow.longArcCount =
      Q.source.longArcCount :=
  rfl

@[simp]
theorem toPointwiseLemma9CoverageLateInputs_longArcCount :
    I.toPointwiseLemma9CoverageLateInputs.longArcCount =
      Q.source.longArcCount :=
  rfl

end Lemma67BoundaryArcReducedPredicateInput

namespace Lemma67BoundaryArcPredicateFields

variable
  (F : Lemma67BoundaryArcPredicateFields B Q)

/-- Any W17 predicate-field producer necessarily contains the finite natural
Lemma 9 predicate package once the W14 Lemma 6/7 coverage inequality is
inserted. -/
def toNatLateTripleInputs :
    M8NatLateTripleInputs B.localLabels.predicates.data :=
  F.toPointwiseLemma9CoverageLateInputs.toNatLateTripleInputs

/-- Forget the W17 coverage carrier, retaining exactly the reduced residual
predicate input. -/
def toReducedPredicateInput :
    Lemma67BoundaryArcReducedPredicateInput B Q where
  arcBoundaryBudget_eq := F.arcBoundaryBudget_eq
  natLateTripleInputs := toNatLateTripleInputs F

end Lemma67BoundaryArcPredicateFields

/-- Precise reduction/no-go statement: after the W14 boundary-arc carrier is
fixed, producing the W17 predicate fields is equivalent to producing the
budget identification and the finite natural Lemma 9 predicate package. -/
theorem nonempty_predicateFields_iff_reducedPredicateInput :
    Nonempty (Lemma67BoundaryArcPredicateFields B Q) <->
      Nonempty (Lemma67BoundaryArcReducedPredicateInput B Q) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            (Lemma67BoundaryArcPredicateFields.toReducedPredicateInput F)
  case mpr =>
    intro h
    cases h with
    | intro I =>
        exact Nonempty.intro I.toPredicateFields

section BoundaryWalk

open Lemma6NegativeAfterGapW12

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

/-- Boundary-walk Lemma 6/7 coverage plus a finite Lemma 9 natural predicate
package produces the W17 predicate fields for the W14 boundary-arc input built
from that walk. -/
def predicateFields_of_boundaryWalkPackage
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary)
    (arcBoundaryBudget_eq :
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc).arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    Lemma67BoundaryArcPredicateFields B
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc) :=
  (Lemma67BoundaryArcReducedPredicateInput.mk
    arcBoundaryBudget_eq Hnat).toPredicateFields

/-- Boundary-walk Lemma 6/7 coverage plus a finite Lemma 9 natural predicate
package produces the concrete W17 coverage row. -/
def coverageConcreteRow_of_boundaryWalkPackage
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary)
    (arcBoundaryBudget_eq :
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc).arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    Lemma9CoverageConcreteRow B :=
  (predicateFields_of_boundaryWalkPackage
    Qwalk boundaryArc arcBoundaryBudget_eq Hnat).toCoverageConcreteRow

/-- Boundary-walk Lemma 6/7 coverage plus a finite Lemma 9 natural predicate
package produces the W16 coverage-late row consumed by downstream W17
assembly. -/
def coverageLateInputs_of_boundaryWalkPackage
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary)
    (arcBoundaryBudget_eq :
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc).arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    PointwiseLemma9CoverageLateInputs B :=
  (coverageConcreteRow_of_boundaryWalkPackage
    Qwalk boundaryArc arcBoundaryBudget_eq Hnat)
      |>.toPointwiseLemma9CoverageLateInputs

@[simp]
theorem coverageConcreteRow_of_boundaryWalkPackage_longArcCount
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary)
    (arcBoundaryBudget_eq :
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc).arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    (coverageConcreteRow_of_boundaryWalkPackage
      Qwalk boundaryArc arcBoundaryBudget_eq Hnat).longArcCount =
        Qwalk.source.longArcCount :=
  rfl

@[simp]
theorem coverageLateInputs_of_boundaryWalkPackage_longArcCount
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary)
    (arcBoundaryBudget_eq :
      (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
        Qwalk boundaryArc).arcBoundaryBudget = B.arcBoundaryBudget)
    (Hnat : M8NatLateTripleInputs B.localLabels.predicates.data) :
    (coverageLateInputs_of_boundaryWalkPackage
      Qwalk boundaryArc arcBoundaryBudget_eq Hnat).longArcCount =
        Qwalk.source.longArcCount :=
  rfl

/-- Boundary-walk specialization of the reduction/no-go statement.  The
boundary-walk package selects the W14 Lemma 6/7 coverage row; the remaining
content is still exactly the budget identification plus finite Lemma 9
natural predicate input. -/
theorem nonempty_boundaryWalkPredicateFields_iff_reducedPredicateInput
    (Qwalk : BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc :
      BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary) :
    Nonempty
      (Lemma67BoundaryArcPredicateFields B
        (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
          Qwalk boundaryArc)) <->
      Nonempty
        (Lemma67BoundaryArcReducedPredicateInput B
          (Lemma67ToBoundaryArcW14.ofBoundaryWalkLongArcGapNegativePackage
            Qwalk boundaryArc)) :=
  nonempty_predicateFields_iff_reducedPredicateInput

end BoundaryWalk

end Lemma9CoverageProducerW18
end Swanepoel
end ErdosProblems1066

end
