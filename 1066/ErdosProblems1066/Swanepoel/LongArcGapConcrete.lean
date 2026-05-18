import ErdosProblems1066.Swanepoel.LongArcExistenceConcrete
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary
import ErdosProblems1066.Swanepoel.NonconcaveArcConcrete
import ErdosProblems1066.Swanepoel.BoundaryWalkClassificationConcrete
import ErdosProblems1066.Swanepoel.M8PipelineClosure

set_option autoImplicit false

/-!
# Concrete long-arc count gap to M8 turn bounds

This file is a small packaging layer around the already checked long-arc
selection and nonconcave-arc reducers.

The main wrappers make the route explicit:

* boundary counts plus the Lemma 6/7 coverage inequality give a strict
  long-arc count gap;
* the strict gap selects a long arc excluded by the concavity predicate; and
* the selected nonconcave long arc supplies the construction-level
  `M8TurnBounds` fields.

The classified-boundary wrapper at the end ties the same route to the concrete
outer-boundary walk package from `BoundaryWalkClassificationConcrete`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace LongArcGapConcrete

open Lemma10Inequalities

universe u

variable {n : Nat}

/-! ## Boundary count-gap route -/

/--
The reusable route from boundary count data and concavity exclusions to a
construction-level `M8TurnBounds` package.

The input `F` is the concrete count-gap package from
`LongArcExistenceConcrete`: it contains the boundary E12 count, the Lemma 6/7
coverage count, the comparison between the concrete concave-long-arc subtype
and the boundary `B` count, plus the raw-turn interpretation of concavity.
-/
structure BoundaryCountGapToM8TurnBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) where
  selectedLongArc : F.LongArc
  selectedLongArc_eq :
    selectedLongArc = F.selectedLongArc
  selectedLongArc_not_concave :
    Not (F.concave selectedLongArc)
  selectedLongArc_totalTurn_lt_pi_div_three :
    totalTurn (F.rawTurn selectedLongArc) < Real.pi / 3
  boundaryLongArcFacts :
    NonconcaveArcBudgetFromBoundary.BoundaryLongArcFacts.{u} D
  boundaryBudgetData :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G
  boundaryToM8Fields :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      boundaryBudgetData
  m8TurnBounds : M8ConstructionInterface.M8TurnBounds
  m8TurnBounds_eq :
    m8TurnBounds = F.toM8TurnBounds
  pipelineTurnBounds :
    M8PipelineClosure.M8TurnBounds m8TurnBounds.turn
  m8TurnBounds_turn_nonnegative :
    forall k : Nat, 0 <= m8TurnBounds.turn k
  m8TurnBounds_totalTurn_lt_pi_div_three :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8ThirteenTurnSum_lt_pi_div_three :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      m8TurnBounds.turn < Real.pi / 3

namespace BoundaryCountGapToM8TurnBounds

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- Assemble the full boundary-count-gap to M8-turn-bound route. -/
def ofBoundaryLongArcExistenceFields
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    BoundaryCountGapToM8TurnBounds F where
  selectedLongArc := F.selectedLongArc
  selectedLongArc_eq := rfl
  selectedLongArc_not_concave := F.selectedLongArc_not_concave
  selectedLongArc_totalTurn_lt_pi_div_three :=
    F.selectedLongArc_totalTurn_lt_pi_div_three
  boundaryLongArcFacts := F.toBoundaryLongArcFacts
  boundaryBudgetData := F.toNonconcaveArcBoundaryBudgetData
  boundaryToM8Fields :=
    F.toNonconcaveArcBoundaryBudgetData.boundaryToM8TurnBoundFields
  m8TurnBounds := F.toM8TurnBounds
  m8TurnBounds_eq := rfl
  pipelineTurnBounds :=
    M8PipelineClosure.turnBounds_of_m8TurnBounds F.toM8TurnBounds
  m8TurnBounds_turn_nonnegative := by
    intro k
    exact F.toM8TurnBounds_turn_nonnegative k
  m8TurnBounds_totalTurn_lt_pi_div_three :=
    F.toM8TurnBounds_totalTurn_lt_pi_div_three
  m8ThirteenTurnSum_lt_pi_div_three :=
    F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

@[simp]
theorem ofBoundaryLongArcExistenceFields_m8TurnBounds
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    (ofBoundaryLongArcExistenceFields F).m8TurnBounds =
      F.toM8TurnBounds :=
  rfl

@[simp]
theorem ofBoundaryLongArcExistenceFields_boundaryBudgetData
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    (ofBoundaryLongArcExistenceFields F).boundaryBudgetData =
      F.toNonconcaveArcBoundaryBudgetData :=
  rfl

end BoundaryCountGapToM8TurnBounds

/-! ## Direct named consequences -/

/-- Boundary counts plus concavity exclusions give construction-level M8 turn
bounds. -/
def m8TurnBoundsOfBoundaryCountGap
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    M8ConstructionInterface.M8TurnBounds :=
  F.toM8TurnBounds

@[simp]
theorem m8TurnBoundsOfBoundaryCountGap_turn
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    (m8TurnBoundsOfBoundaryCountGap F).turn =
      F.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_turn

/-- Pointwise nonnegativity of the M8 turn function obtained from the
boundary count gap. -/
theorem m8TurnBoundsOfBoundaryCountGap_turn_nonnegative
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D)
    (k : Nat) :
    0 <= (m8TurnBoundsOfBoundaryCountGap F).turn k :=
  F.toM8TurnBounds_turn_nonnegative k

/-- The M8 turn function obtained from the boundary count gap has total turn
below `pi / 3`. -/
theorem m8TurnBoundsOfBoundaryCountGap_totalTurn_lt_pi_div_three
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    totalTurn (m8TurnBoundsOfBoundaryCountGap F).turn < Real.pi / 3 :=
  F.toM8TurnBounds_totalTurn_lt_pi_div_three

/-- The explicit thirteen-turn M8 sum obtained from the boundary count gap is
below `pi / 3`. -/
theorem m8TurnBoundsOfBoundaryCountGap_thirteenTurnSum_lt_pi_div_three
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      (m8TurnBoundsOfBoundaryCountGap F).turn < Real.pi / 3 :=
  F.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

/-! ## M8 pipeline turn-bound route -/

/-- The selected nonconcave long arc supplies the turn-bound proposition used
by the downstream `M8PipelineClosure` layer. -/
def pipelineTurnBoundsOfBoundaryCountGap
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    M8PipelineClosure.M8TurnBounds
      (m8TurnBoundsOfBoundaryCountGap F).turn :=
  M8PipelineClosure.turnBounds_of_m8TurnBounds
    (m8TurnBoundsOfBoundaryCountGap F)

/-- Pointwise nonnegativity in the pipeline-facing turn-bound package. -/
theorem pipelineTurnBoundsOfBoundaryCountGap_turn_nonnegative
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D)
    (k : Nat) :
    0 <= (m8TurnBoundsOfBoundaryCountGap F).turn k :=
  (pipelineTurnBoundsOfBoundaryCountGap F).nonnegative k

/-- Strict total-turn bound in the pipeline-facing turn-bound package. -/
theorem pipelineTurnBoundsOfBoundaryCountGap_totalTurn_lt_pi_div_three
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    totalTurn (m8TurnBoundsOfBoundaryCountGap F).turn < Real.pi / 3 :=
  (pipelineTurnBoundsOfBoundaryCountGap F).total_lt_pi_div_three

/-- The count-gap input simultaneously selects a nonconcave long arc and
supplies the M8 pipeline turn-bound field for its normalized turns. -/
theorem exists_nonconcave_longArc_with_pipelineTurnBounds
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    Exists fun a : F.LongArc =>
      Not (F.concave a) /\
        totalTurn (F.rawTurn a) < Real.pi / 3 /\
          M8PipelineClosure.M8TurnBounds
            (m8TurnBoundsOfBoundaryCountGap F).turn := by
  exact Exists.intro F.selectedLongArc
    (And.intro F.selectedLongArc_not_concave
      (And.intro F.selectedLongArc_totalTurn_lt_pi_div_three
        (pipelineTurnBoundsOfBoundaryCountGap F)))

/-! ## Comparison with the concrete nonconcave-arc facade -/

/-- A universe lift of the long-arc family, used to feed the concrete
nonconcave-arc facade without changing cardinalities. -/
def liftedLongArcEquiv
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    ULift.{u, 0} F.LongArc ≃ F.LongArc where
  toFun := fun a => a.down
  invFun := fun a => ULift.up a
  left_inv := by
    intro a
    cases a
    rfl
  right_inv := by
    intro a
    rfl

/-- Lifting also preserves the concave-long-arc subtype. -/
def liftedConcaveLongArcEquiv
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    {a : ULift.{u, 0} F.LongArc // F.concave a.down} ≃
      {a : F.LongArc // F.concave a} where
  toFun := fun a => ⟨a.1.down, a.2⟩
  invFun := fun a => ⟨ULift.up a.1, a.2⟩
  left_inv := by
    intro a
    cases a with
    | mk val property =>
      cases val
      rfl
  right_inv := by
    intro a
    cases a
    rfl

/-- The same count-gap input, viewed through `NonconcaveArcConcrete`. -/
def toConcreteBoundaryLongArcFacts
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    NonconcaveArcConcrete.BoundaryLongArcFacts.{u, u} D where
  LongArc := ULift.{u, 0} F.LongArc
  longArcFintype := by
    letI : Fintype F.LongArc := F.longArcFintype
    exact Fintype.ofEquiv F.LongArc (liftedLongArcEquiv F).symm
  concave := fun a => F.concave a.down
  concaveLongArcFintype :=
    by
      letI : Fintype {a : F.LongArc // F.concave a} :=
        F.concaveLongArcFintype
      exact Fintype.ofEquiv {a : F.LongArc // F.concave a}
        (liftedConcaveLongArcEquiv F).symm
  concaveLongArcCount_lt_longArcCount := by
    letI : Fintype F.LongArc := F.longArcFintype
    letI : Fintype {a : F.LongArc // F.concave a} :=
      F.concaveLongArcFintype
    letI : Fintype (ULift.{u, 0} F.LongArc) :=
      Fintype.ofEquiv F.LongArc (liftedLongArcEquiv F).symm
    letI : Fintype {a : ULift.{u, 0} F.LongArc // F.concave a.down} :=
      Fintype.ofEquiv {a : F.LongArc // F.concave a}
        (liftedConcaveLongArcEquiv F).symm
    simpa [Fintype.card_congr (liftedConcaveLongArcEquiv F),
      Fintype.card_congr (liftedLongArcEquiv F)] using
      F.concaveLongArcCount_lt_longArcCount
  rawTurn := fun a => F.rawTurn a.down
  rawTurn_nonnegative_on_arc := by
    intro a k hk
    exact F.rawTurn_nonnegative_on_arc a.down k hk
  concave_iff := by
    intro a
    exact F.concave_iff a.down

/-- The concrete nonconcave-arc facade also produces an M8 turn-bound
package from the same count-gap input. -/
def concreteM8TurnBoundsOfBoundaryCountGap
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    M8ConstructionInterface.M8TurnBounds :=
  (toConcreteBoundaryLongArcFacts F).toM8TurnBounds

/-- Pointwise nonnegativity through the `NonconcaveArcConcrete` facade. -/
theorem concreteM8TurnBoundsOfBoundaryCountGap_turn_nonnegative
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D)
    (k : Nat) :
    0 <= (concreteM8TurnBoundsOfBoundaryCountGap F).turn k :=
  (toConcreteBoundaryLongArcFacts F).toM8TurnBounds_turn_nonnegative k

/-- Strict total-turn bound through the `NonconcaveArcConcrete` facade. -/
theorem concreteM8TurnBoundsOfBoundaryCountGap_totalTurn_lt_pi_div_three
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    totalTurn (concreteM8TurnBoundsOfBoundaryCountGap F).turn <
      Real.pi / 3 :=
  (toConcreteBoundaryLongArcFacts F).toM8TurnBounds_totalTurn_lt_pi_div_three

/-- Pipeline-facing turn bounds through the older concrete nonconcave-arc
facade. -/
def concretePipelineTurnBoundsOfBoundaryCountGap
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (F : LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u} D) :
    M8PipelineClosure.M8TurnBounds
      (concreteM8TurnBoundsOfBoundaryCountGap F).turn :=
  M8PipelineClosure.turnBounds_of_m8TurnBounds
    (concreteM8TurnBoundsOfBoundaryCountGap F)

/-! ## Concrete classified-boundary wrapper -/

/--
A concrete classified outer-boundary walk together with the long-arc count-gap
fields needed to produce M8 turn bounds.

The boundary data is built from
`BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs`; the
long-arc family may be any finite family whose concave subfamily is controlled
by the boundary `B` count and whose cardinality covers the degree-three count.
-/
structure ClassifiedBoundaryCountGapInput
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {P : OuterBoundaryCore G}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      classification.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= classification.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  fields :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      (classification.toPlanarBoundaryData geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)

namespace ClassifiedBoundaryCountGapInput

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}
variable {classification :
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs P}
variable {geometricAngleSum : Real}
variable {forced_le_geometric :
  classification.counts.forcedBoundaryAngleSum <= geometricAngleSum}
variable {geometric_le_polygon :
  geometricAngleSum <= classification.counts.polygonAngleSum}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- The planar-boundary package built from the concrete classified walk. -/
def planarBoundary
    (_F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  classification.toPlanarBoundaryData geometricAngleSum forced_le_geometric
    geometric_le_polygon Subpolygon subpolygonData

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    F.planarBoundary.outerBoundaryCounts = classification.counts := by
  simp [planarBoundary]

/-- The classified boundary count-gap input as the full reusable route to M8
turn bounds. -/
def toBoundaryCountGapToM8TurnBounds
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    BoundaryCountGapToM8TurnBounds F.fields :=
  BoundaryCountGapToM8TurnBounds.ofBoundaryLongArcExistenceFields F.fields

/-- Construction-level M8 turn bounds obtained from the concrete classified
boundary route. -/
def toM8TurnBounds
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    M8ConstructionInterface.M8TurnBounds :=
  m8TurnBoundsOfBoundaryCountGap F.fields

/-- Pointwise nonnegativity for the classified-boundary M8 turn bounds. -/
theorem toM8TurnBounds_turn_nonnegative
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (k : Nat) :
    0 <= F.toM8TurnBounds.turn k :=
  m8TurnBoundsOfBoundaryCountGap_turn_nonnegative F.fields k

/-- Strict total-turn bound for the classified-boundary M8 turn bounds. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    totalTurn F.toM8TurnBounds.turn < Real.pi / 3 :=
  m8TurnBoundsOfBoundaryCountGap_totalTurn_lt_pi_div_three F.fields

/-- Explicit thirteen-turn strict bound for the classified-boundary route. -/
theorem toM8TurnBounds_thirteenTurnSum_lt_pi_div_three
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      F.toM8TurnBounds.turn < Real.pi / 3 :=
  m8TurnBoundsOfBoundaryCountGap_thirteenTurnSum_lt_pi_div_three F.fields

/-- Pipeline-facing M8 turn bounds obtained from the concrete classified
boundary route. -/
def toPipelineTurnBounds
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    M8PipelineClosure.M8TurnBounds F.toM8TurnBounds.turn :=
  pipelineTurnBoundsOfBoundaryCountGap F.fields

/-- Pointwise nonnegativity for the classified-boundary route, in the
pipeline-facing package. -/
theorem toPipelineTurnBounds_turn_nonnegative
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData)
    (k : Nat) :
    0 <= F.toM8TurnBounds.turn k :=
  F.toPipelineTurnBounds.nonnegative k

/-- Strict total-turn bound for the classified-boundary route, in the
pipeline-facing package. -/
theorem toPipelineTurnBounds_totalTurn_lt_pi_div_three
    (F :
      ClassifiedBoundaryCountGapInput classification geometricAngleSum
        forced_le_geometric geometric_le_polygon Subpolygon subpolygonData) :
    totalTurn F.toM8TurnBounds.turn < Real.pi / 3 :=
  F.toPipelineTurnBounds.total_lt_pi_div_three

end ClassifiedBoundaryCountGapInput

end LongArcGapConcrete
end Swanepoel
end ErdosProblems1066

end
