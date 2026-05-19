import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary
import ErdosProblems1066.Swanepoel.BoundaryAngleCertificatesConcrete
import ErdosProblems1066.Swanepoel.BoundaryAngleWitnessConstruction

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

/-! ## Concrete carrier/raw-turn source rows -/

/--
Minimal positive row package for the actual boundary-classified long arcs.

For the selected boundary route, the classification side supplies a concrete
finite carrier of long-arc indices together with the count identity
`card LongArc = B`.  Once Lemma 6/7 supplies `d_3 <= N + card LongArc`, the
only remaining geometric content is the raw turn attached to each classified
long arc and its pointwise nonnegativity on the thirteen turn slots.

Concavity is intentionally not a separate field here: downstream it is the
definitional threshold `pi / 3 <= totalTurn rawTurn`.
-/
structure BoundaryLongArcCarrierRawTurnRows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  LongArc : Type
  longArcFintype : Fintype LongArc
  longArcCount_eq_boundaryConcaveCount :
    @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B
  degreeThree_le_negativeCount_add_longArcCount :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount +
        @Fintype.card LongArc longArcFintype
  rawTurn : LongArc -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall a : LongArc,
      forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k

namespace BoundaryLongArcCarrierRawTurnRows

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/--
Build the carrier/raw-turn rows from an explicit finite long-arc carrier.

This is the narrow positive source surface: callers must supply the real
carrier, the boundary count identity, Lemma 6/7 coverage, and pointwise
nonnegative raw turns.  No long arc or turn is selected here.
-/
def ofFiniteCarrierRawTurns
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (rawTurn : LongArc -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : LongArc,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    BoundaryLongArcCarrierRawTurnRows.{u} D where
  LongArc := LongArc
  longArcFintype := longArcFintype
  longArcCount_eq_boundaryConcaveCount :=
    longArcCount_eq_boundaryConcaveCount
  degreeThree_le_negativeCount_add_longArcCount :=
    degreeThree_le_negativeCount_add_longArcCount
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc

@[simp]
theorem ofFiniteCarrierRawTurns_rawTurn
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (rawTurn : LongArc -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : LongArc,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    (ofFiniteCarrierRawTurns (D := D) LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount rawTurn
      rawTurn_nonnegative_on_arc).rawTurn = rawTurn :=
  rfl

theorem nonempty_of_finiteCarrierRawTurns
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (rawTurn : LongArc -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall a : LongArc,
        forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn a k) :
    Nonempty (BoundaryLongArcCarrierRawTurnRows.{u} D) :=
  Nonempty.intro
    (ofFiniteCarrierRawTurns (D := D) LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount rawTurn
      rawTurn_nonnegative_on_arc)

/-- The concrete number of boundary-classified long arcs. -/
def longArcCount
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) : Nat :=
  @Fintype.card R.LongArc R.longArcFintype

/-- The carrier count is the boundary `B` count used in E12. -/
theorem longArcCount_eq_boundaryConcaveCount_field
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    R.longArcCount = D.outerBoundaryCounts.B :=
  R.longArcCount_eq_boundaryConcaveCount

/-- Concavity for carrier rows is exactly the raw total-turn threshold. -/
def concave
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) (a : R.LongArc) : Prop :=
  Real.pi / 3 <= totalTurn (R.rawTurn a)

@[simp]
theorem concave_iff_totalTurn_ge_pi_div_three
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) (a : R.LongArc) :
    R.concave a <-> Real.pi / 3 <= totalTurn (R.rawTurn a) :=
  Iff.rfl

/--
The classified carrier/raw-turn rows are precisely enough to inhabit the
long-arc existence fields consumed by the W24/S4 route.
-/
def toBoundaryLongArcExistenceFields
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    BoundaryLongArcExistenceFields.{u} D := by
  classical
  let concave : R.LongArc -> Prop := fun a => R.concave a
  letI : Fintype R.LongArc := R.longArcFintype
  exact
    { LongArc := R.LongArc
      longArcFintype := R.longArcFintype
      concave := concave
      concaveLongArcFintype := inferInstance
      concaveLongArcCount_le_boundaryConcaveCount := by
        letI : Fintype R.LongArc := R.longArcFintype
        have hsub :
            @Fintype.card {a : R.LongArc // concave a} inferInstance <=
              @Fintype.card R.LongArc R.longArcFintype :=
          Fintype.card_subtype_le concave
        rw [R.longArcCount_eq_boundaryConcaveCount] at hsub
        exact hsub
      degreeThree_le_negativeCount_add_longArcCount :=
        R.degreeThree_le_negativeCount_add_longArcCount
      rawTurn := R.rawTurn
      rawTurn_nonnegative_on_arc := R.rawTurn_nonnegative_on_arc
      concave_iff := by
        intro a
        rfl }

@[simp]
theorem toBoundaryLongArcExistenceFields_rawTurn
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    R.toBoundaryLongArcExistenceFields.rawTurn = R.rawTurn :=
  rfl

@[simp]
theorem toBoundaryLongArcExistenceFields_LongArc
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    R.toBoundaryLongArcExistenceFields.LongArc = R.LongArc :=
  rfl

theorem toBoundaryLongArcExistenceFields_degreeThree_le
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount +
        @Fintype.card R.toBoundaryLongArcExistenceFields.LongArc
          R.toBoundaryLongArcExistenceFields.longArcFintype :=
  R.toBoundaryLongArcExistenceFields.degreeThree_le_negativeCount_add_longArcCount

theorem toBoundaryLongArcExistenceFields_concave_iff
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D)
    (a : R.toBoundaryLongArcExistenceFields.LongArc) :
    R.toBoundaryLongArcExistenceFields.concave a <->
      Real.pi / 3 <= totalTurn (R.toBoundaryLongArcExistenceFields.rawTurn a) :=
  R.toBoundaryLongArcExistenceFields.concave_iff a

end BoundaryLongArcCarrierRawTurnRows

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

/-- Pointwise raw-turn nonnegativity, exposed as a field projection. -/
theorem rawTurn_nonnegative_on_arc_field
    (F : BoundaryLongArcExistenceFields.{u} D) (a : F.LongArc) :
    forall k : Nat,
      Membership.mem turnIndexSet k -> 0 <= F.rawTurn a k :=
  F.rawTurn_nonnegative_on_arc a

/-- Concavity is exactly the raw total-turn threshold. -/
theorem concave_iff_totalTurn_ge_pi_div_three
    (F : BoundaryLongArcExistenceFields.{u} D) (a : F.LongArc) :
    F.concave a <-> Real.pi / 3 <= totalTurn (F.rawTurn a) :=
  F.concave_iff a

/-- Nonconcavity is exactly strict failure of the `pi / 3` raw-turn
threshold. -/
theorem not_concave_iff_totalTurn_lt_pi_div_three
    (F : BoundaryLongArcExistenceFields.{u} D) (a : F.LongArc) :
    Not (F.concave a) <-> totalTurn (F.rawTurn a) < Real.pi / 3 := by
  constructor
  · intro ha
    have hnot :
        Not (Real.pi / 3 <= totalTurn (F.rawTurn a)) := by
      intro hle
      exact ha ((F.concave_iff a).2 hle)
    exact lt_of_not_ge hnot
  · intro hlt hconcave
    exact not_le_of_gt hlt ((F.concave_iff a).1 hconcave)

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

/-- The supplied long-arc family is genuinely positive. -/
theorem longArcCount_pos
    (F : BoundaryLongArcExistenceFields.{u} D) :
    0 < F.longArcCount :=
  Nat.lt_of_le_of_lt (Nat.zero_le F.concaveLongArcCount)
    F.concaveLongArcCount_lt_longArcCount

/-- The checked count gap produces an actual nonconcave long arc. -/
theorem exists_nonconcave_longArc
    (F : BoundaryLongArcExistenceFields.{u} D) :
    Exists fun a : F.LongArc => Not (F.concave a) := by
  letI : Fintype F.LongArc := F.longArcFintype
  letI : Fintype {a : F.LongArc // F.concave a} :=
    F.concaveLongArcFintype
  exact exists_not_of_subtype_card_lt F.concave
    F.concaveLongArcCount_lt_longArcCount

/-- The positive count gap makes the supplied long-arc type nonempty. -/
theorem longArc_nonempty
    (F : BoundaryLongArcExistenceFields.{u} D) :
    Nonempty F.LongArc := by
  cases F.exists_nonconcave_longArc with
  | intro a _ =>
      exact Nonempty.intro a

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

/-- Pointwise nonnegativity of the selected raw-turn function. -/
theorem selectedLongArc_rawTurn_nonnegative_on_arc
    (F : BoundaryLongArcExistenceFields.{u} D) :
    forall k : Nat,
      Membership.mem turnIndexSet k -> 0 <= F.rawTurn F.selectedLongArc k :=
  F.rawTurn_nonnegative_on_arc F.selectedLongArc

/-- Existence form of the selected nonconcave long arc with its turn bounds. -/
theorem exists_nonconcave_longArc_with_turn_bounds
    (F : BoundaryLongArcExistenceFields.{u} D) :
    Exists fun a : F.LongArc =>
      Not (F.concave a) ∧
        totalTurn (F.rawTurn a) < Real.pi / 3 ∧
          forall k : Nat,
            Membership.mem turnIndexSet k -> 0 <= F.rawTurn a k :=
  Exists.intro F.selectedLongArc
    ⟨F.selectedLongArc_not_concave,
      F.selectedLongArc_totalTurn_lt_pi_div_three,
      F.selectedLongArc_rawTurn_nonnegative_on_arc⟩

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

/-- The explicit thirteen-turn M8 sum is below `pi / 3`. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (F : BoundaryLongArcExistenceFields.{u} D) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
        F.toM8TurnBounds.turn < Real.pi / 3 :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

end BoundaryLongArcExistenceFields

namespace BoundaryLongArcCarrierRawTurnRows

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- Direct projection to the downstream finite-selection facts. -/
def toBoundaryLongArcFacts
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    NonconcaveArcBudgetFromBoundary.BoundaryLongArcFacts.{u} D :=
  R.toBoundaryLongArcExistenceFields.toBoundaryLongArcFacts

/-- Direct projection to the selected nonconcave-arc budget data. -/
noncomputable def toNonconcaveArcBoundaryBudgetData
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  R.toBoundaryLongArcExistenceFields.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem toNonconcaveArcBoundaryBudgetData_rawTurn
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    R.toNonconcaveArcBoundaryBudgetData.rawTurn =
      R.rawTurn R.toBoundaryLongArcExistenceFields.selectedLongArc :=
  rfl

/--
The explicit carrier rows already contain exactly the data needed to produce a
selected nonconcave long arc with the raw-turn bounds used downstream.
-/
theorem exists_nonconcave_longArc_with_turn_bounds
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    Exists fun a : R.LongArc =>
      Not (R.concave a) ∧
        totalTurn (R.rawTurn a) < Real.pi / 3 ∧
          forall k : Nat,
            Membership.mem turnIndexSet k -> 0 <= R.rawTurn a k :=
  R.toBoundaryLongArcExistenceFields.exists_nonconcave_longArc_with_turn_bounds

theorem toBoundaryLongArcExistenceFields_longArcCount_eq_boundaryConcaveCount
    (R : BoundaryLongArcCarrierRawTurnRows.{u} D) :
    R.toBoundaryLongArcExistenceFields.longArcCount =
      D.outerBoundaryCounts.B :=
  R.longArcCount_eq_boundaryConcaveCount

end BoundaryLongArcCarrierRawTurnRows

/-! ## Actual turn-angle source rows -/

/--
Cycle-safe source rows for carrier raw turns obtained from real boundary turn
angle certificates.

This is the narrow layer that W11-style turn-angle packages can forget to:
the carrier count is interpreted as the boundary `B` count, Lemma 6/7 supplies
the degree-three coverage row, and each raw-turn slot is a concrete
`UnitSeparatedAngle` value.  Pointwise nonnegativity is therefore proved from
the angle certificate itself rather than added as an unrelated row.
-/
structure BoundaryLongArcTurnAngleRows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  LongArc : Type
  longArcFintype : Fintype LongArc
  longArcCount_eq_boundaryConcaveCount :
    @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B
  degreeThree_le_negativeCount_add_longArcCount :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount +
        @Fintype.card LongArc longArcFintype
  turnAngle :
    forall _a : LongArc,
      forall k : Nat,
        Membership.mem turnIndexSet k ->
          BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G

namespace BoundaryLongArcTurnAngleRows

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/--
Build actual long-arc turn-angle rows from a selected outer-boundary turn
vertex for every carrier element and turn slot.

The angle witness at each selected slot is the canonical
predecessor/current/successor angle on the supplied outer-boundary core, built
by `BoundaryAngleWitnessConstruction`.  The two count rows are kept explicit:
the boundary classification owns the carrier count identity, while Lemma 6/7
owns the degree-three coverage inequality.
-/
def ofOuterBoundaryCoreTurnVertex
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length) :
    BoundaryLongArcTurnAngleRows.{u} D where
  LongArc := LongArc
  longArcFintype := longArcFintype
  longArcCount_eq_boundaryConcaveCount :=
    longArcCount_eq_boundaryConcaveCount
  degreeThree_le_negativeCount_add_longArcCount :=
    degreeThree_le_negativeCount_add_longArcCount
  turnAngle :=
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle.turnWitnessesOfBoundaryVertices
      P h3 turnVertex

@[simp]
theorem ofOuterBoundaryCoreTurnVertex_turnAngle
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length)
    (a : LongArc) (k : Nat) (hk : Membership.mem turnIndexSet k) :
    (ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount
      turnVertex).turnAngle a k hk =
        BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
          P h3 turnVertex a k :=
  rfl

/--
The actual angle row produced from selected boundary vertices has the selected
turn vertex as its center.
-/
@[simp]
theorem ofOuterBoundaryCoreTurnVertex_turnAngle_center
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length)
    (a : LongArc) (k : Nat) (hk : Membership.mem turnIndexSet k) :
    ((ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount
      turnVertex).turnAngle a k hk).center =
        P.outerCycle.vertex (turnVertex a k) :=
  rfl

/--
The actual angle row produced from selected boundary vertices has the cyclic
successor of the selected turn vertex as its right endpoint.
-/
@[simp]
theorem ofOuterBoundaryCoreTurnVertex_turnAngle_right
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length)
    (a : LongArc) (k : Nat) (hk : Membership.mem turnIndexSet k) :
    ((ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount
      turnVertex).turnAngle a k hk).right =
        P.outerCycle.vertex
          (PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (turnVertex a k)) :=
  rfl

/--
The left endpoint of the actual angle row is the canonical cyclic predecessor
of the selected boundary turn vertex.
-/
theorem ofOuterBoundaryCoreTurnVertex_turnAngle_left_is_boundary_predecessor
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length)
    (a : LongArc) (k : Nat) (hk : Membership.mem turnIndexSet k) :
    Exists fun pred : Fin P.outerCycle.length =>
      ((ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
        longArcCount_eq_boundaryConcaveCount
        degreeThree_le_negativeCount_add_longArcCount
        turnVertex).turnAngle a k hk).left =
          P.outerCycle.vertex pred /\
        PlanarInterface.cyclicSucc P.outerCycle.length_pos pred =
          turnVertex a k := by
  exact
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex_left_is_boundary_predecessor
      P h3 turnVertex a k

/-- The raw turn is the actual angle value on the thirteen turn slots and `0`
off the turn-index set. -/
noncomputable def rawTurn
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.LongArc) (k : Nat) : Real :=
  if hk : Membership.mem turnIndexSet k then
    (R.turnAngle a k hk).value
  else
    0

@[simp]
theorem rawTurn_of_mem
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    R.rawTurn a k = (R.turnAngle a k hk).value := by
  unfold rawTurn
  rw [dif_pos hk]

@[simp]
theorem rawTurn_of_not_mem
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.LongArc) (k : Nat)
    (hk : Not (Membership.mem turnIndexSet k)) :
    R.rawTurn a k = 0 := by
  unfold rawTurn
  rw [dif_neg hk]

/-- Actual angle values give the raw-turn nonnegativity needed downstream. -/
theorem rawTurn_nonnegative_on_arc
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    0 <= R.rawTurn a k := by
  rw [R.rawTurn_of_mem a k hk]
  exact
    BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value_nonnegative
      (R.turnAngle a k hk)

/-- The concrete carrier count represented by the turn-angle rows. -/
def longArcCount
    (R : BoundaryLongArcTurnAngleRows.{u} D) : Nat :=
  @Fintype.card R.LongArc R.longArcFintype

/-- The turn-angle carrier count is the boundary `B` count. -/
theorem longArcCount_eq_boundaryConcaveCount_field
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    R.longArcCount = D.outerBoundaryCounts.B :=
  R.longArcCount_eq_boundaryConcaveCount

/--
Forget actual turn-angle witnesses to the carrier/raw-turn source rows used by
the long-arc existence constructor.
-/
noncomputable def toBoundaryLongArcCarrierRawTurnRows
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    BoundaryLongArcCarrierRawTurnRows.{u} D where
  LongArc := R.LongArc
  longArcFintype := R.longArcFintype
  longArcCount_eq_boundaryConcaveCount :=
    R.longArcCount_eq_boundaryConcaveCount
  degreeThree_le_negativeCount_add_longArcCount :=
    R.degreeThree_le_negativeCount_add_longArcCount
  rawTurn := R.rawTurn
  rawTurn_nonnegative_on_arc := R.rawTurn_nonnegative_on_arc

@[simp]
theorem toBoundaryLongArcCarrierRawTurnRows_LongArc
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    R.toBoundaryLongArcCarrierRawTurnRows.LongArc = R.LongArc :=
  rfl

@[simp]
theorem toBoundaryLongArcCarrierRawTurnRows_rawTurn
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    R.toBoundaryLongArcCarrierRawTurnRows.rawTurn = R.rawTurn :=
  rfl

/-- The carrier row produced from turn angles keeps the actual angle value on
every turn slot. -/
theorem toBoundaryLongArcCarrierRawTurnRows_rawTurn_of_mem
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.toBoundaryLongArcCarrierRawTurnRows.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    R.toBoundaryLongArcCarrierRawTurnRows.rawTurn a k =
      (R.turnAngle a k hk).value :=
  R.rawTurn_of_mem a k hk

/--
Build the carrier/raw-turn rows directly from selected outer-boundary turn
vertices by first constructing the actual turn-angle witnesses and then
forgetting to raw turns.
-/
noncomputable def carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length) :
    BoundaryLongArcCarrierRawTurnRows.{u} D :=
  (ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
    longArcCount_eq_boundaryConcaveCount
    degreeThree_le_negativeCount_add_longArcCount
    turnVertex).toBoundaryLongArcCarrierRawTurnRows

/-- The direct carrier/raw-turn constructor keeps the actual angle value on
every selected turn slot. -/
theorem carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex_rawTurn_of_mem
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length)
    (a : LongArc) (k : Nat) (hk : Membership.mem turnIndexSet k) :
    (carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount
      turnVertex).rawTurn a k =
        (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
          P h3 turnVertex a k).value := by
  change
    (ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount
      turnVertex).rawTurn a k =
        (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
          P h3 turnVertex a k).value
  rw [(ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
    longArcCount_eq_boundaryConcaveCount
    degreeThree_le_negativeCount_add_longArcCount
    turnVertex).rawTurn_of_mem a k hk]
  rfl

/--
Direct classified raw-turn source from actual outer-boundary turn vertices.

This is the cycle-safe W11/W13 handoff in the concrete long-arc layer: the
turn-angle rows are built by `ofOuterBoundaryCoreTurnVertex`, the carrier rows
are exactly their raw-turn projection, and the projected rows retain the actual
angle value on every turn slot together with the classified carrier count and
Lemma 6/7 coverage row.
-/
theorem classifiedW13RawTurnAndCarrierRowsOfOuterBoundaryCoreTurnVertex
    (P : OuterBoundaryCore G)
    (h3 : 3 <= P.outerCycle.length)
    (LongArc : Type) [longArcFintype : Fintype LongArc]
    (longArcCount_eq_boundaryConcaveCount :
      @Fintype.card LongArc longArcFintype = D.outerBoundaryCounts.B)
    (degreeThree_le_negativeCount_add_longArcCount :
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype)
    (turnVertex : LongArc -> Nat -> Fin P.outerCycle.length) :
    let turnRows :=
      ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
        longArcCount_eq_boundaryConcaveCount
        degreeThree_le_negativeCount_add_longArcCount
        turnVertex
    let carrierRows :=
      carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
        longArcCount_eq_boundaryConcaveCount
        degreeThree_le_negativeCount_add_longArcCount
        turnVertex
    carrierRows = turnRows.toBoundaryLongArcCarrierRawTurnRows /\
      (forall a : LongArc,
        forall k : Nat,
          Membership.mem turnIndexSet k ->
            turnRows.rawTurn a k =
              (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
                P h3 turnVertex a k).value) /\
      (forall a : LongArc,
        forall k : Nat,
          Membership.mem turnIndexSet k ->
            carrierRows.rawTurn a k =
              (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreTurnVertex
                P h3 turnVertex a k).value) /\
      (forall a : LongArc,
        forall k : Nat,
          Membership.mem turnIndexSet k -> 0 <= carrierRows.rawTurn a k) /\
      carrierRows.longArcCount = D.outerBoundaryCounts.B /\
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount + carrierRows.longArcCount := by
  dsimp only
  constructor
  · rfl
  constructor
  · intro a k hk
    rw [(ofOuterBoundaryCoreTurnVertex (D := D) P h3 LongArc
      longArcCount_eq_boundaryConcaveCount
      degreeThree_le_negativeCount_add_longArcCount
      turnVertex).rawTurn_of_mem a k hk]
    rfl
  constructor
  · intro a k hk
    exact
      carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex_rawTurn_of_mem
        (D := D) P h3 LongArc
        longArcCount_eq_boundaryConcaveCount
        degreeThree_le_negativeCount_add_longArcCount
        turnVertex a k hk
  constructor
  · intro a k hk
    exact
      (carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex
        (D := D) P h3 LongArc
        longArcCount_eq_boundaryConcaveCount
        degreeThree_le_negativeCount_add_longArcCount
        turnVertex).rawTurn_nonnegative_on_arc a k hk
  constructor
  · change @Fintype.card LongArc longArcFintype =
      D.outerBoundaryCounts.B
    exact longArcCount_eq_boundaryConcaveCount
  · change
      D.outerBoundaryCounts.d3 <=
        D.outerBoundaryCounts.negativeCount +
          @Fintype.card LongArc longArcFintype
    exact degreeThree_le_negativeCount_add_longArcCount

/-- The carrier row produced from turn angles interprets the carrier count as
the boundary `B` count. -/
theorem toBoundaryLongArcCarrierRawTurnRows_longArcCount_eq_boundaryConcaveCount
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    R.toBoundaryLongArcCarrierRawTurnRows.longArcCount =
      D.outerBoundaryCounts.B := by
  change @Fintype.card R.LongArc R.longArcFintype =
    D.outerBoundaryCounts.B
  exact R.longArcCount_eq_boundaryConcaveCount

/-- The Lemma 6/7 coverage row is preserved by the carrier projection. -/
theorem toBoundaryLongArcCarrierRawTurnRows_degreeThree_le
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount +
        R.toBoundaryLongArcCarrierRawTurnRows.longArcCount := by
  change
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount +
        @Fintype.card R.LongArc R.longArcFintype
  exact R.degreeThree_le_negativeCount_add_longArcCount

/-- Pointwise nonnegativity is the value-nonnegativity of the actual angle
certificate selected for that slot. -/
theorem toBoundaryLongArcCarrierRawTurnRows_rawTurn_nonnegative_on_arc
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.toBoundaryLongArcCarrierRawTurnRows.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    0 <= R.toBoundaryLongArcCarrierRawTurnRows.rawTurn a k :=
  R.toBoundaryLongArcCarrierRawTurnRows.rawTurn_nonnegative_on_arc a k hk

/-- Direct projection from turn-angle rows to the long-arc existence fields. -/
noncomputable def toBoundaryLongArcExistenceFields
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    BoundaryLongArcExistenceFields.{u} D :=
  R.toBoundaryLongArcCarrierRawTurnRows.toBoundaryLongArcExistenceFields

@[simp]
theorem toBoundaryLongArcExistenceFields_rawTurn
    (R : BoundaryLongArcTurnAngleRows.{u} D) :
    R.toBoundaryLongArcExistenceFields.rawTurn = R.rawTurn :=
  rfl

theorem toBoundaryLongArcExistenceFields_rawTurn_of_mem
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.toBoundaryLongArcExistenceFields.LongArc) (k : Nat)
    (hk : Membership.mem turnIndexSet k) :
    R.toBoundaryLongArcExistenceFields.rawTurn a k =
      (R.turnAngle a k hk).value :=
  R.rawTurn_of_mem a k hk

/-- Concavity after the turn-angle projection is exactly the raw total-turn
threshold. -/
theorem toBoundaryLongArcExistenceFields_concave_iff_totalTurn_ge_pi_div_three
    (R : BoundaryLongArcTurnAngleRows.{u} D)
    (a : R.toBoundaryLongArcExistenceFields.LongArc) :
    R.toBoundaryLongArcExistenceFields.concave a <->
      Real.pi / 3 <= totalTurn (R.toBoundaryLongArcExistenceFields.rawTurn a) :=
  R.toBoundaryLongArcExistenceFields.concave_iff a

end BoundaryLongArcTurnAngleRows

end LongArcExistenceConcrete
end Swanepoel
end ErdosProblems1066

end
