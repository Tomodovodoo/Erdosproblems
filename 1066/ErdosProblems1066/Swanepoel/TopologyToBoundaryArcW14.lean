import ErdosProblems1066.Swanepoel.BoundaryArcInstantiationW13
import ErdosProblems1066.Swanepoel.ExactOuterBoundaryTopologyW13
import ErdosProblems1066.Swanepoel.LongArcExistenceConcrete
import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9
import ErdosProblems1066.Swanepoel.SwanepoelRemainingMatrix

set_option autoImplicit false

/-!
# W14 topology to boundary-arc bridge

This file keeps the constructive boundary-arc extraction honest.  The checked
topology and long-arc rows already assemble the planar-boundary package and
the boundary-attached turn budget.  The remaining constructive input is the
selected `m = 8` boundary arc on that same planar boundary, recorded as
`BoundaryArcExtractionFields` below.

The projections then land in the W13 `BoundaryArcInstantiation` record and in
the older W9/remaining-matrix rows consumed downstream.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyToBoundaryArcW14

open BoundaryArcInstantiationW13
open BoundaryArcW12
open BoundarySpineFiniteCertificate
open ExactOuterBoundaryTopologyW13
open LongArcExistenceConcrete
open M8LabelsFromBoundaryInterface
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a config. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  ExactOuterBoundaryTopologyW13.CanonicalGraph C

/-! ## The remaining constructive arc field -/

/--
Constructive extraction of the selected `m = 8` boundary arc from a fixed
planar-boundary package.

All adjacency facts in the downstream finite spine are then checked by
`BoundaryArcW12`; this record only supplies the selected boundary indices and
triangle witnesses.
-/
structure BoundaryArcExtractionFields
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalGraph C)) where
  boundaryArc : M8BoundaryArcCertificate D

namespace BoundaryArcExtractionFields

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalGraph C)}

/-- Forget the extracted arc to the finite `p/q` spine certificate. -/
def toFinitePQSpineCertificate
    (A : BoundaryArcExtractionFields D) :
    M8FinitePQSpineCertificate D :=
  A.boundaryArc.toFinitePQSpineCertificate

@[simp]
theorem toFinitePQSpineCertificate_pIndex
    (A : BoundaryArcExtractionFields D) (i : M8BoundaryIndex) :
    A.toFinitePQSpineCertificate.pIndex i =
      A.boundaryArc.pIndex i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_p
    (A : BoundaryArcExtractionFields D) (i : M8BoundaryIndex) :
    A.toFinitePQSpineCertificate.p i =
      A.boundaryArc.p i :=
  rfl

@[simp]
theorem toFinitePQSpineCertificate_q
    (A : BoundaryArcExtractionFields D) (i : M8TriangleIndex) :
    A.toFinitePQSpineCertificate.q i =
      A.boundaryArc.q i :=
  rfl

end BoundaryArcExtractionFields

/-! ## Boundary budget plus extracted arc to W13 instantiation -/

/-- Combine a boundary-attached turn budget with the extracted boundary arc. -/
def boundaryArcInstantiationOfBudgetAndArc
    {C : _root_.UDConfig n}
    (D : NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (A : BoundaryArcExtractionFields D.planarBoundary) :
    BoundaryArcInstantiation D.planarBoundary where
  boundaryArc := A.boundaryArc
  rawTurn := D.rawTurn
  rawTurn_nonnegative_on_arc := D.rawTurn_nonnegative_on_arc
  boundaryAngleBudget := D.boundaryAngleBudget

@[simp]
theorem boundaryArcInstantiationOfBudgetAndArc_boundaryArc
    {C : _root_.UDConfig n}
    (D : NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (A : BoundaryArcExtractionFields D.planarBoundary) :
    (boundaryArcInstantiationOfBudgetAndArc D A).boundaryArc =
      A.boundaryArc :=
  rfl

@[simp]
theorem boundaryArcInstantiationOfBudgetAndArc_rawTurn
    {C : _root_.UDConfig n}
    (D : NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (A : BoundaryArcExtractionFields D.planarBoundary) :
    (boundaryArcInstantiationOfBudgetAndArc D A).rawTurn =
      D.rawTurn :=
  rfl

@[simp]
theorem boundaryArcInstantiationOfBudgetAndArc_toBudgetData
    {C : _root_.UDConfig n}
    (D : NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (A : BoundaryArcExtractionFields D.planarBoundary) :
    (boundaryArcInstantiationOfBudgetAndArc D A).toNonconcaveArcBoundaryBudgetData =
      D := by
  cases D
  rfl

/--
The selected long-arc fields already produce the boundary-attached budget; an
extracted boundary arc upgrades them to the W13 instantiation record.
-/
def boundaryArcInstantiationOfLongArcFields
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}
    (F : BoundaryLongArcExistenceFields.{u} D)
    (A : BoundaryArcExtractionFields D) :
    BoundaryArcInstantiation D :=
  boundaryArcInstantiationOfBudgetAndArc
    F.toNonconcaveArcBoundaryBudgetData A

@[simp]
theorem boundaryArcInstantiationOfLongArcFields_boundaryArc
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}
    (F : BoundaryLongArcExistenceFields.{u} D)
    (A : BoundaryArcExtractionFields D) :
    (boundaryArcInstantiationOfLongArcFields F A).boundaryArc =
      A.boundaryArc :=
  rfl

@[simp]
theorem boundaryArcInstantiationOfLongArcFields_rawTurn
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}
    (F : BoundaryLongArcExistenceFields.{u} D)
    (A : BoundaryArcExtractionFields D) :
    (boundaryArcInstantiationOfLongArcFields F A).rawTurn =
      F.rawTurn F.selectedLongArc :=
  rfl

@[simp]
theorem boundaryArcInstantiationOfLongArcFields_toBudgetData
    {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}
    (F : BoundaryLongArcExistenceFields.{u} D)
    (A : BoundaryArcExtractionFields D) :
    (boundaryArcInstantiationOfLongArcFields F A).toNonconcaveArcBoundaryBudgetData =
      F.toNonconcaveArcBoundaryBudgetData :=
  rfl

/-! ## Topology, long-arc, and boundary-arc conditional record -/

/--
Exact topology plus the still-explicit angle/subpolygon, long-arc, and
boundary-arc extraction fields.

This is the conditional W14 source record when the constructive extraction of
the `m = 8` boundary arc is not yet available as an unconditional theorem.
-/
structure TopologyBoundaryArcFields
    (C : _root_.UDConfig n) where
  topology : TopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  arcExtraction :
    BoundaryArcExtractionFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace TopologyBoundaryArcFields

variable {C : _root_.UDConfig n}

/-- The planar boundary assembled from the topology, angle, and subpolygon rows. -/
def planarBoundary
    (R : TopologyBoundaryArcFields.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  R.topology.toPlanarBoundaryData R.outerAngleBounds R.Subpolygon
    R.subpolygonData

@[simp]
theorem planarBoundary_core
    (R : TopologyBoundaryArcFields.{u} C) :
    R.planarBoundary.core = R.topology.toCore :=
  rfl

/-- The exact W13 topology fields obtained from the supplied topology facts. -/
def minimalExactFields
    (R : TopologyBoundaryArcFields.{u} C) :
    MinimalExactFields C :=
  exactFields_of_topologyFacts R.topology

/-- The boundary-attached nonconcave-arc budget selected by the long-arc row. -/
def arcBoundaryBudget
    (R : TopologyBoundaryArcFields.{u} C) :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C) :=
  R.longArc.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem arcBoundaryBudget_planarBoundary
    (R : TopologyBoundaryArcFields.{u} C) :
    R.arcBoundaryBudget.planarBoundary = R.planarBoundary :=
  rfl

/-- The selected boundary arc over the same planar boundary. -/
def boundaryArc
    (R : TopologyBoundaryArcFields.{u} C) :
    M8BoundaryArcCertificate R.planarBoundary :=
  R.arcExtraction.boundaryArc

/-- The finite `p/q` spine certificate produced by the boundary arc. -/
def spineCertificate
    (R : TopologyBoundaryArcFields.{u} C) :
    M8FinitePQSpineCertificate R.planarBoundary :=
  R.arcExtraction.toFinitePQSpineCertificate

@[simp]
theorem spineCertificate_pIndex
    (R : TopologyBoundaryArcFields.{u} C) (i : M8BoundaryIndex) :
    R.spineCertificate.pIndex i = R.boundaryArc.pIndex i :=
  rfl

@[simp]
theorem spineCertificate_p
    (R : TopologyBoundaryArcFields.{u} C) (i : M8BoundaryIndex) :
    R.spineCertificate.p i = R.boundaryArc.p i :=
  rfl

@[simp]
theorem spineCertificate_q
    (R : TopologyBoundaryArcFields.{u} C) (i : M8TriangleIndex) :
    R.spineCertificate.q i = R.boundaryArc.q i :=
  rfl

/-- The W13 boundary-arc instantiation expected by downstream bridge code. -/
def toBoundaryArcInstantiation
    (R : TopologyBoundaryArcFields.{u} C) :
    BoundaryArcInstantiation R.planarBoundary :=
  boundaryArcInstantiationOfLongArcFields R.longArc R.arcExtraction

@[simp]
theorem toBoundaryArcInstantiation_boundaryArc
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toBoundaryArcInstantiation.boundaryArc = R.boundaryArc :=
  rfl

@[simp]
theorem toBoundaryArcInstantiation_rawTurn
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toBoundaryArcInstantiation.rawTurn =
      R.longArc.rawTurn R.longArc.selectedLongArc :=
  rfl

@[simp]
theorem toBoundaryArcInstantiation_toBudgetData
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toBoundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData =
      R.arcBoundaryBudget :=
  rfl

@[simp]
theorem toBoundaryArcInstantiation_toFinitePQSpineCertificate
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toBoundaryArcInstantiation.toFinitePQSpineCertificate =
      R.spineCertificate :=
  rfl

/-- The W9 topology/angle/subpolygon row obtained from the same fields. -/
def toW9TopologyAngleSubpolygonRow
    (R : TopologyBoundaryArcFields.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C where
  topology := R.topology
  outerAngleBounds := R.outerAngleBounds
  Subpolygon := R.Subpolygon
  subpolygonData := R.subpolygonData
  longArc := R.longArc

@[simp]
theorem toW9TopologyAngleSubpolygonRow_planarBoundary
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toW9TopologyAngleSubpolygonRow.planarBoundary =
      R.planarBoundary :=
  rfl

@[simp]
theorem toW9TopologyAngleSubpolygonRow_arcBoundaryBudget
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toW9TopologyAngleSubpolygonRow.arcBoundaryBudget =
      R.arcBoundaryBudget :=
  rfl

/--
The older remaining-matrix topology/count/long-arc row, tied to the same core
as the topology facts.
-/
def toRemainingTopologyBoundaryLongArc
    (R : TopologyBoundaryArcFields.{u} C) :
    SwanepoelRemainingMatrix.TopologyBoundaryLongArc.{u} C where
  topology := R.topology
  arcBoundaryBudget := R.arcBoundaryBudget
  topologyCore_eq := rfl

@[simp]
theorem toRemainingTopologyBoundaryLongArc_planarBoundary
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toRemainingTopologyBoundaryLongArc.planarBoundary =
      R.planarBoundary :=
  rfl

@[simp]
theorem toRemainingTopologyBoundaryLongArc_longArc
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toRemainingTopologyBoundaryLongArc.longArc =
      R.arcBoundaryBudget.toNonconcaveArcTurnData :=
  rfl

/-- The W13 turn package obtained through the boundary-arc instantiation. -/
def toBoundaryLongArcM8TurnPackage
    (R : TopologyBoundaryArcFields.{u} C) :
    M8TurnPackageW12.BoundaryLongArcM8TurnPackage
      R.arcBoundaryBudget :=
  R.toBoundaryArcInstantiation.toBoundaryLongArcM8TurnPackage

@[simp]
theorem toBoundaryLongArcM8TurnPackage_turnBounds
    (R : TopologyBoundaryArcFields.{u} C) :
    R.toBoundaryLongArcM8TurnPackage.turnBounds =
      R.arcBoundaryBudget.toM8TurnBounds :=
  rfl

/-- The W13 thirteen-turn/window consequences for the selected boundary arc. -/
def thirteenWindowData
    (R : TopologyBoundaryArcFields.{u} C) :
    M8TurnPackageW12.M8ThirteenTurnWindowData
      R.arcBoundaryBudget.toM8TurnBounds :=
  R.toBoundaryArcInstantiation.thirteenWindowData

theorem thirteenWindowData_totalTurn_eq_thirteen
    (R : TopologyBoundaryArcFields.{u} C) :
    Lemma10Inequalities.totalTurn R.arcBoundaryBudget.toM8TurnBounds.turn =
      m8ThirteenTurnSum R.arcBoundaryBudget.toM8TurnBounds.turn :=
  R.thirteenWindowData.totalTurn_eq_thirteen

theorem thirteenWindowData_thirteen_lt_pi_div_three
    (R : TopologyBoundaryArcFields.{u} C) :
    m8ThirteenTurnSum R.arcBoundaryBudget.toM8TurnBounds.turn <
      Real.pi / 3 :=
  R.thirteenWindowData.thirteen_lt_pi_div_three

end TopologyBoundaryArcFields

/-! ## A theorem-shaped statement of the remaining arc extraction -/

/--
Pointwise constructive arc extraction over a fixed topology/angle/subpolygon
long-arc row.
-/
def BoundaryArcExtractionTarget
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    (_longArc :
      BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) : Prop :=
  Nonempty
    (BoundaryArcExtractionFields
      (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData))

/--
Uniform constructive arc-extraction theorem still needed to remove the W14
conditional arc field.
-/
def BoundaryArcExtractionTheorem : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalGraph C))
    (longArc :
      BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)),
      BoundaryArcExtractionTarget
        T outerAngleBounds Subpolygon subpolygonData longArc

/-- Use a pointwise extraction target to build the full conditional W14 row. -/
theorem topologyBoundaryArcFields_of_extractionTarget
    {C : _root_.UDConfig n}
    {T : TopologyFacts C}
    {outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)}
    {longArc :
      BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon subpolygonData)}
    (h :
      BoundaryArcExtractionTarget
        T outerAngleBounds Subpolygon subpolygonData longArc) :
    Nonempty (TopologyBoundaryArcFields.{u} C) := by
  cases h with
  | intro arcExtraction =>
      exact
        Nonempty.intro
          { topology := T
            outerAngleBounds := outerAngleBounds
            Subpolygon := Subpolygon
            subpolygonData := subpolygonData
            longArc := longArc
            arcExtraction := arcExtraction }

/--
Use a uniform extraction theorem to obtain the W13 boundary-arc instantiation
for any already supplied topology/angle/subpolygon/long-arc row.
-/
theorem boundaryArcInstantiation_of_extractionTheorem
    (H : BoundaryArcExtractionTheorem.{u})
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    (longArc :
      BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :
    Nonempty
      (BoundaryArcInstantiation
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) := by
  cases H C T outerAngleBounds Subpolygon subpolygonData longArc with
  | intro arcExtraction =>
      exact
        Nonempty.intro
          (boundaryArcInstantiationOfLongArcFields longArc arcExtraction)

end

end TopologyToBoundaryArcW14
end Swanepoel
end ErdosProblems1066
