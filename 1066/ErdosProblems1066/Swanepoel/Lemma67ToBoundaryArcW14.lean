import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.BoundaryArcInstantiationW13
import ErdosProblems1066.Swanepoel.LongArcToM8AssemblyW13
import ErdosProblems1066.Swanepoel.M8RefinedInputConcrete

set_option autoImplicit false

/-!
# W14 Lemma 6/7 to boundary arc bridge

This module is a narrow adapter from the W13 Lemma 6/7 gap-negative package
to the boundary-arc and selected-long-arc data consumed by the M8 row.

The caller still supplies every geometric input explicitly: the Lemma 6/7
package, the selected boundary arc, the cut/no-cut data, and the Lemma 8 row.
The checked content here is the deterministic bookkeeping that keeps all of
those inputs attached to the same planar boundary.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma67ToBoundaryArcW14

open M8LabelsFromBoundaryInterface
open PlanarInterface

universe u

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C

/-! ## Generic Lemma 6/7 plus boundary-arc input -/

/--
The W14 source package.

`gapNegative` carries the Lemma 6/7 coverage proof and the long-arc family.
`boundaryArc` carries the explicit fourteen boundary labels and triangle
witnesses for the same planar boundary.
-/
structure Lemma67BoundaryArcInput
    (C : _root_.UDConfig n)
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)) where
  gapNegative :
    Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage D
  boundaryArc :
    BoundaryArcW12.M8BoundaryArcCertificate D

namespace Lemma67BoundaryArcInput

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}

/-- The long-arc source fields before Lemma 6/7 coverage is inserted. -/
def source
    (Q : Lemma67BoundaryArcInput C D) :
    Lemma6Lemma7AssemblyW13.BoundaryLongArcSourceFields D :=
  Q.gapNegative.source

/-- The Lemma 6/7 coverage data attached to the long-arc source. -/
def coverage
    (Q : Lemma67BoundaryArcInput C D) :
    Lemma6Lemma7AssemblyW13.GapNegativeCoverageData D Q.source.longArcCount :=
  Q.gapNegative.coverage

/-- The checked Lemma 6/7 coverage inequality in boundary-count form. -/
theorem degreeThree_le_negativeCount_add_longArcCount
    (Q : Lemma67BoundaryArcInput C D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + Q.source.longArcCount :=
  Q.gapNegative.degreeThree_le_negativeCount_add_longArcCount

/-- Long-arc existence/count-gap fields produced by Lemma 6/7 coverage. -/
def boundaryLongArcExistenceFields
    (Q : Lemma67BoundaryArcInput C D) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D :=
  Q.gapNegative.toBoundaryLongArcExistenceFields

/-- The full count-gap route to construction-level M8 turn bounds. -/
def boundaryCountGapToM8TurnBounds
    (Q : Lemma67BoundaryArcInput C D) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      Q.boundaryLongArcExistenceFields :=
  Q.gapNegative.toBoundaryCountGapToM8TurnBounds

/-- Boundary-attached budget data for the selected nonconcave long arc. -/
def arcBoundaryBudget
    (Q : Lemma67BoundaryArcInput C D) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (CanonicalGraph C) :=
  Q.gapNegative.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem arcBoundaryBudget_planarBoundary
    (Q : Lemma67BoundaryArcInput C D) :
    Q.arcBoundaryBudget.planarBoundary = D :=
  rfl

/-- Boundary-arc instantiation using the selected long arc as the turn
budget. -/
def boundaryArcInstantiation
    (Q : Lemma67BoundaryArcInput C D) :
    BoundaryArcInstantiationW13.BoundaryArcInstantiation D where
  boundaryArc := Q.boundaryArc
  rawTurn := Q.arcBoundaryBudget.rawTurn
  rawTurn_nonnegative_on_arc := Q.arcBoundaryBudget.rawTurn_nonnegative_on_arc
  boundaryAngleBudget := Q.arcBoundaryBudget.boundaryAngleBudget

@[simp]
theorem boundaryArcInstantiation_boundaryArc
    (Q : Lemma67BoundaryArcInput C D) :
    Q.boundaryArcInstantiation.boundaryArc = Q.boundaryArc :=
  rfl

@[simp]
theorem boundaryArcInstantiation_rawTurn
    (Q : Lemma67BoundaryArcInput C D) :
    Q.boundaryArcInstantiation.rawTurn = Q.arcBoundaryBudget.rawTurn :=
  rfl

@[simp]
theorem boundaryArcInstantiation_boundaryAngleBudget
    (Q : Lemma67BoundaryArcInput C D) :
    Q.boundaryArcInstantiation.boundaryAngleBudget =
      Q.arcBoundaryBudget.boundaryAngleBudget :=
  rfl

/-- The finite `p/q` spine certificate obtained from the supplied boundary
arc. -/
def finitePQSpineCertificate
    (Q : Lemma67BoundaryArcInput C D) :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate D :=
  Q.boundaryArcInstantiation.toFinitePQSpineCertificate

@[simp]
theorem finitePQSpineCertificate_pIndex
    (Q : Lemma67BoundaryArcInput C D) (i : M8BoundaryIndex) :
    Q.finitePQSpineCertificate.pIndex i = Q.boundaryArc.pIndex i :=
  rfl

@[simp]
theorem finitePQSpineCertificate_p
    (Q : Lemma67BoundaryArcInput C D) (i : M8BoundaryIndex) :
    Q.finitePQSpineCertificate.p i = Q.boundaryArc.p i :=
  rfl

@[simp]
theorem finitePQSpineCertificate_q
    (Q : Lemma67BoundaryArcInput C D) (i : M8TriangleIndex) :
    Q.finitePQSpineCertificate.q i = Q.boundaryArc.q i :=
  rfl

/-- M8-facing turn-field bundle built from the selected long-arc budget. -/
def turnFields
    (Q : Lemma67BoundaryArcInput C D) :
    LongArcToM8AssemblyW13.BoundaryBudgetM8TurnFields
      Q.arcBoundaryBudget :=
  LongArcToM8AssemblyW13.BoundaryBudgetM8TurnFields.ofBoundaryBudgetData
    Q.arcBoundaryBudget

/-- Construction-level M8 turn bounds selected by the Lemma 6/7 count gap. -/
def m8TurnBounds
    (Q : Lemma67BoundaryArcInput C D) :
    M8ConstructionInterface.M8TurnBounds :=
  Q.turnFields.turnBounds

@[simp]
theorem m8TurnBounds_eq_boundaryBudget
    (Q : Lemma67BoundaryArcInput C D) :
    Q.m8TurnBounds = Q.arcBoundaryBudget.toM8TurnBounds :=
  Q.turnFields.turnBounds_eq

/-- Pointwise nonnegativity of the selected M8 turn function. -/
theorem m8TurnBounds_turn_nonnegative
    (Q : Lemma67BoundaryArcInput C D) (k : Nat) :
    0 <= Q.m8TurnBounds.turn k :=
  Q.turnFields.turn_nonnegative k

/-- The selected M8 turn function has total turn below `pi / 3`. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (Q : Lemma67BoundaryArcInput C D) :
    Lemma10Inequalities.totalTurn Q.m8TurnBounds.turn < Real.pi / 3 :=
  Q.turnFields.totalTurn_lt_pi_div_three

/-- The selected M8 thirteen-turn sum is below `pi / 3`. -/
theorem m8TurnBounds_thirteenTurnSum_lt_pi_div_three
    (Q : Lemma67BoundaryArcInput C D) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      Q.m8TurnBounds.turn < Real.pi / 3 :=
  Q.turnFields.thirteenTurnSum_lt_pi_div_three

/--
Build the M8 base row once the remaining cut/no-cut and Lemma 8 inputs are
supplied explicitly.
-/
def toM8BoundaryLemma8TurnInput
    (Q : Lemma67BoundaryArcInput C D)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (positiveCard : 0 < n)
    (remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C)
    (lemma8Existence :
      Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
        (Q.finitePQSpineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
              C hmin).preconnectedNoCut hmin)) :
    M8RefinedInputConcrete.M8BoundaryLemma8TurnInput.{u} C hmin where
  positiveCard := positiveCard
  remainingNoCutSlack := remainingNoCutSlack
  arcBoundaryBudget := Q.arcBoundaryBudget
  spineCertificate := Q.finitePQSpineCertificate
  lemma8Existence := lemma8Existence

@[simp]
theorem toM8BoundaryLemma8TurnInput_arcBoundaryBudget
    (Q : Lemma67BoundaryArcInput C D)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (positiveCard : 0 < n)
    (remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C)
    (lemma8Existence :
      Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
        (Q.finitePQSpineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
              C hmin).preconnectedNoCut hmin)) :
    (Q.toM8BoundaryLemma8TurnInput positiveCard remainingNoCutSlack
        lemma8Existence).arcBoundaryBudget = Q.arcBoundaryBudget :=
  rfl

@[simp]
theorem toM8BoundaryLemma8TurnInput_spineCertificate
    (Q : Lemma67BoundaryArcInput C D)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (positiveCard : 0 < n)
    (remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C)
    (lemma8Existence :
      Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
        (Q.finitePQSpineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
              C hmin).preconnectedNoCut hmin)) :
    (Q.toM8BoundaryLemma8TurnInput positiveCard remainingNoCutSlack
        lemma8Existence).spineCertificate = Q.finitePQSpineCertificate :=
  rfl

end Lemma67BoundaryArcInput

/-! ## Boundary-walk package adapter -/

section BoundaryWalk

variable {C : _root_.UDConfig n}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
variable {P : OuterBoundaryCore (CanonicalGraph C)}
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
    SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
variable
  {O :
    Lemma6NegativeAfterGapW12.BoundaryWalkLemma6Obstruction walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData}

/--
Forget the boundary-walk indices after Lemma 6/7 coverage has been checked,
then attach the explicit M8 boundary arc.
-/
def ofBoundaryWalkLongArcGapNegativePackage
    (Q :
      Lemma6Lemma7AssemblyW13.BoundaryWalkLongArcGapNegativePackage O)
    (boundaryArc : BoundaryArcW12.M8BoundaryArcCertificate O.planarBoundary) :
    Lemma67BoundaryArcInput C O.planarBoundary where
  gapNegative := Q.toBoundaryLongArcGapNegativePackage
  boundaryArc := boundaryArc

end BoundaryWalk

end Lemma67ToBoundaryArcW14
end Swanepoel
end ErdosProblems1066

end
