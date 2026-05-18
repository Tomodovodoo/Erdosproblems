import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false

/-!
# Concrete long nonconcave arc existence bridge

This file isolates the checked part of Swanepoel's Lemma 5/E16 step.

The paper argument has two different long-arc counts:

* the `B` appearing in the boundary angle count is the count charged as
  concave long arcs; and
* the selected family of all long arcs has cardinality `A`.

The finite arithmetic below proves that the boundary inequality
`N + B + 6 <= d_3`, together with the Lemma 6/7 coverage conclusion
`d_3 <= N + A`, forces strictly more long arcs than concave long arcs.  The
remaining geometric/combinatorial fields are therefore exposed explicitly:
the concrete finite long-arc family, the realization of the concave count by
the boundary `B` field, the degree-three coverage inequality, the raw turn
function, pointwise nonnegativity, and the definition of concavity by the
`pi / 3` total-turn threshold.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace LongArcExistenceConcrete

open Lemma10Inequalities
open NonconcaveArcAngleFacts
open NonconcaveArcBudgetFromBoundary

universe u v

variable {n : Nat}

/-! ## Pure finite selection and count arithmetic -/

/-- If a subtype has strictly smaller finite cardinality than the ambient
type, then some ambient element is outside the subtype. -/
theorem exists_not_of_subtype_card_lt
    {alpha : Type v} [Fintype alpha] (p : alpha -> Prop)
    [Fintype {a : alpha // p a}]
    (hcard : Fintype.card {a : alpha // p a} < Fintype.card alpha) :
    Exists fun a : alpha => Not (p a) := by
  by_contra hnone
  have hall : forall a : alpha, p a := by
    intro a
    by_contra ha
    exact hnone (Exists.intro a ha)
  let e : Equiv alpha {a : alpha // p a} :=
    { toFun := fun a => Subtype.mk a (hall a)
      invFun := fun a => a.1
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro a
        cases a
        rfl }
  have hcard_eq :
      Fintype.card alpha = Fintype.card {a : alpha // p a} :=
    Fintype.card_congr e
  have hlt : Fintype.card alpha < Fintype.card alpha := by
    rw [hcard_eq.symm] at hcard
    exact hcard
  exact (Nat.lt_irrefl _) hlt

/--
The checked Nat arithmetic in the E16 count step.

Here `negativeCount` is `N`, `boundaryConcaveCount` is the boundary-count
field `B`, `degreeThree` is `d_3`, `longArcCount` is `A`, and `concaveCount`
is the concrete cardinality of the supplied concave-long-arc subtype.
-/
theorem concave_count_lt_long_count_of_boundary_counts
    {negativeCount boundaryConcaveCount degreeThree longArcCount
      concaveCount : Nat}
    (hboundary :
      negativeCount + boundaryConcaveCount + 6 <= degreeThree)
    (hcoverage :
      degreeThree <= negativeCount + longArcCount)
    (hconcave :
      concaveCount <= boundaryConcaveCount) :
    concaveCount < longArcCount := by
  omega

/-! ## Boundary-counted long-arc fields -/

/--
The exact remaining data needed to turn boundary counts into a selected
nonconcave long arc.

The checked boundary package supplies `N + B + 6 <= d_3`.  This record asks
for the two still-geometric E16 inputs:

* `concaveLongArcCount_le_boundaryConcaveCount`, tying the concrete concave
  long arcs to the `B` term used in E12; and
* `degreeThree_le_negativeCount_add_longArcCount`, the Lemma 6/7 coverage
  conclusion `d_3 <= N + A`.

The turn fields are exactly what the downstream nonconcave-arc budget facade
needs after the finite selection has picked a nonconcave arc.
-/
structure BoundaryLongArcExistenceFields
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  LongArc : Type
  longArcFintype : Fintype LongArc
  concave : LongArc -> Prop
  concaveLongArcFintype : Fintype {a : LongArc // concave a}
  concaveLongArcCount_le_boundaryConcaveCount :
    @Fintype.card {a : LongArc // concave a} concaveLongArcFintype <=
      D.outerBoundaryCounts.B
  degreeThree_le_negativeCount_add_longArcCount :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount +
        @Fintype.card LongArc longArcFintype
  rawTurn : LongArc -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : LongArc,
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k
  concave_iff :
    forall a : LongArc, concave a <-> Real.pi / 3 <= totalTurn (rawTurn a)

namespace BoundaryLongArcExistenceFields

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The concrete number `A` of supplied long arcs. -/
def longArcCount
    (F : BoundaryLongArcExistenceFields.{u} D) : Nat :=
  @Fintype.card F.LongArc F.longArcFintype

/-- The concrete number of supplied concave long arcs. -/
def concaveLongArcCount
    (F : BoundaryLongArcExistenceFields.{u} D) : Nat :=
  @Fintype.card {a : F.LongArc // F.concave a}
    F.concaveLongArcFintype

/-- The boundary `B` field controls the concrete concave-long-arc subtype. -/
theorem concaveLongArcCount_le_boundaryConcaveCount_field
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.concaveLongArcCount <= D.outerBoundaryCounts.B :=
  F.concaveLongArcCount_le_boundaryConcaveCount

/-- The Lemma 6/7 coverage conclusion written with named counts. -/
theorem degreeThree_le_negativeCount_add_longArcCount_field
    (F : BoundaryLongArcExistenceFields.{u} D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + F.longArcCount :=
  F.degreeThree_le_negativeCount_add_longArcCount

/-- Boundary E12 plus the supplied Lemma 6/7 coverage forces
`concave long arcs < long arcs`. -/
theorem concaveLongArcCount_lt_longArcCount
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.concaveLongArcCount < F.longArcCount :=
  concave_count_lt_long_count_of_boundary_counts
    (PlanarBoundaryFinal.PlanarBoundaryData.boundaryNegativeCountInequality_viaBoundaryCounting
      D)
    F.degreeThree_le_negativeCount_add_longArcCount
    F.concaveLongArcCount_le_boundaryConcaveCount

/-- The checked count gap produces an actual nonconcave long arc. -/
theorem exists_nonconcave_longArc
    (F : BoundaryLongArcExistenceFields.{u} D) :
    Exists fun a : F.LongArc => Not (F.concave a) := by
  letI : Fintype F.LongArc := F.longArcFintype
  letI : Fintype {a : F.LongArc // F.concave a} :=
    F.concaveLongArcFintype
  exact exists_not_of_subtype_card_lt F.concave
    F.concaveLongArcCount_lt_longArcCount

/-- A proved nonconcave long arc has total turn below `pi / 3`. -/
theorem totalTurn_lt_pi_div_three_of_not_concave
    (F : BoundaryLongArcExistenceFields.{u} D) {a : F.LongArc}
    (ha : Not (F.concave a)) :
    totalTurn (F.rawTurn a) < Real.pi / 3 := by
  have hnot :
      Not (Real.pi / 3 <= totalTurn (F.rawTurn a)) := by
    intro hle
    exact ha ((F.concave_iff a).2 hle)
  exact lt_of_not_ge hnot

/-! ## Projection into the existing nonconcave-arc facades -/

/-- Forget the boundary-count derivation and produce the downstream finite
long-arc selection record. -/
def toBoundaryLongArcFacts
    (F : BoundaryLongArcExistenceFields.{u} D) :
    NonconcaveArcBudgetFromBoundary.BoundaryLongArcFacts.{u} D where
  LongArc := F.LongArc
  longArcFintype := F.longArcFintype
  concave := F.concave
  concaveLongArcFintype := F.concaveLongArcFintype
  concaveLongArcCount_lt_longArcCount :=
    F.concaveLongArcCount_lt_longArcCount
  rawTurn := F.rawTurn
  rawTurn_nonnegative_on_arc := F.rawTurn_nonnegative_on_arc
  concave_iff := F.concave_iff

/-- The selected nonconcave long arc. -/
noncomputable def selectedLongArc
    (F : BoundaryLongArcExistenceFields.{u} D) : F.LongArc :=
  F.toBoundaryLongArcFacts.selectedLongArc

/-- The selected long arc is nonconcave. -/
theorem selectedLongArc_not_concave
    (F : BoundaryLongArcExistenceFields.{u} D) :
    Not (F.concave F.selectedLongArc) :=
  F.toBoundaryLongArcFacts.selectedLongArc_not_concave

/-- The selected long arc has total turn below `pi / 3`. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three
    (F : BoundaryLongArcExistenceFields.{u} D) :
    totalTurn (F.rawTurn F.selectedLongArc) < Real.pi / 3 :=
  F.toBoundaryLongArcFacts.selectedLongArc_totalTurn_lt_pi_div_three

/-- Package the selected nonconcave long arc as boundary-budget data. -/
noncomputable def toNonconcaveArcBoundaryBudgetData
    (F : BoundaryLongArcExistenceFields.{u} D) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  F.toBoundaryLongArcFacts.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_planarBoundary
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.toNonconcaveArcBoundaryBudgetData.planarBoundary = D :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_rawTurn
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.toNonconcaveArcBoundaryBudgetData.rawTurn =
      F.rawTurn F.selectedLongArc :=
  rfl

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_geometricAngleBudget
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.toNonconcaveArcBoundaryBudgetData.boundaryAngleBudget.geometricAngleBudget =
      totalTurn (F.rawTurn F.selectedLongArc) :=
  rfl

/-- The selected boundary-budget data as generic geometric angle facts. -/
def toNonconcaveArcGeometricAngleFacts
    (F : BoundaryLongArcExistenceFields.{u} D) :
    NonconcaveArcGeometricAngleFacts :=
  F.toNonconcaveArcBoundaryBudgetData.toNonconcaveArcGeometricAngleFacts

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_rawTurn
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.toNonconcaveArcGeometricAngleFacts.rawTurn =
      F.rawTurn F.selectedLongArc :=
  rfl

/-- The selected boundary-budget data as normalized nonconcave-arc turn data. -/
def toNonconcaveArcTurnData
    (F : BoundaryLongArcExistenceFields.{u} D) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  F.toNonconcaveArcBoundaryBudgetData.toNonconcaveArcTurnData

@[simp]
theorem toNonconcaveArcTurnData_rawTurn
    (F : BoundaryLongArcExistenceFields.{u} D) :
    F.toNonconcaveArcTurnData.rawTurn =
      F.rawTurn F.selectedLongArc :=
  rfl

/-- The selected boundary-budget data as construction-level M8 turn bounds. -/
def toM8TurnBounds
    (F : BoundaryLongArcExistenceFields.{u} D) :
    M8ConstructionInterface.M8TurnBounds :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds

/-- Pointwise nonnegativity of the selected normalized M8 turn function. -/
theorem toM8TurnBounds_turn_nonnegative
    (F : BoundaryLongArcExistenceFields.{u} D) (k : Nat) :
    0 <= F.toM8TurnBounds.turn k :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn_nonnegative k

/-- The selected normalized M8 total turn is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (F : BoundaryLongArcExistenceFields.{u} D) :
    totalTurn F.toM8TurnBounds.turn < Real.pi / 3 :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_totalTurn_lt_pi_div_three

end BoundaryLongArcExistenceFields

end LongArcExistenceConcrete
end Swanepoel
end ErdosProblems1066

end
