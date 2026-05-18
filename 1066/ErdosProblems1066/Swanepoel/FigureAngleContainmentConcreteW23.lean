import ErdosProblems1066.Swanepoel.FigureExactAngleCertificateInhabitationW22
import ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.Figure9EuclideanFactsConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 concrete Figure angle-containment constructors

This module makes the W22 exact Figure 8/Figure 9 angle-containment
dependency explicit at the concrete containment boundary.  The exact
inequalities are precisely the universal containment fields already carried by
`AngleContainmentBridgeProducerW19` and the concrete Figure containment
interfaces; the Euclidean Figure files supply the selected witness routes to
E22/E23 once those containments are present.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace FigureAngleContainmentConcreteW23

open AngleContainmentBridgeProducerW19
open AngleContainmentInterface
open FigureAngleSourceInhabitationW21
open FigureExactAngleCertificateInhabitationW22
open FigureWitnessClosureW19
open Lemma10AnalyticBridge
open Lemma10Bridge
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

abbrev Point : Type :=
  AngleGeometry.Point

/-! ## Exact inequality package -/

/-- The two exact Figure 8/Figure 9 angle-containment inequalities remaining
after the concrete Euclidean distance packages have supplied their local angle
lower bounds. -/
structure ExactFigureAngleInequalities
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop where
  figure8 :
    Figure8UniversalAngleContainment good turn
  figure9_left :
    Figure9UniversalLeftAngleContainment good turn

namespace ExactFigureAngleInequalities

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- The exact inequalities carried by a combined concrete containment bridge. -/
def ofAngleContainmentBridges
    (A : AngleContainmentBridges good turn) :
    ExactFigureAngleInequalities good turn where
  figure8 := A.figure8.central_angle_le_separatedTurn
  figure9_left := A.figure9.left_angle_le_adjacentTurn

/-- The exact inequalities carried by separately supplied Figure 8 and
Figure 9 containment interfaces. -/
def ofContainmentInterfaces
    (figure8 : Figure8SeparatedContainmentInterface good turn)
    (figure9_left : Figure9AdjacentLeftContainmentInterface good turn) :
    ExactFigureAngleInequalities good turn where
  figure8 := figure8.central_angle_le_separatedTurn
  figure9_left := figure9_left.left_angle_le_adjacentTurn

/-- Figure 8 pointwise exact containment projected from the package. -/
theorem figure8_apply
    (H : ExactFigureAngleInequalities good turn)
    {i j : Nat} {p qi qj s r : Point}
    (hi : 1 <= i) (hsep : i + 1 < j) (hj : j <= 10)
    (hbad_i : Not (good i)) (hbad_j : Not (good j))
    (D : AngleBridgeFacts.Figure8DistanceData p qi qj s r) :
    AngleGeometry.angleAt qi p qj <=
      Lemma10Inequalities.separatedTurn turn i j :=
  H.figure8 hi hsep hj hbad_i hbad_j D

/-- Figure 9 pointwise exact left-angle containment projected from the
package. -/
theorem figure9_left_apply
    (H : ExactFigureAngleInequalities good turn)
    {i : Nat} {p qi qj s r : Point}
    (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i : Not (good i)) (hbad_next : Not (good (i + 1)))
    (D : AngleBridgeFacts.Figure9DistanceData p qi qj s r) :
    AngleGeometry.angleAt p qi s <=
      Lemma10Inequalities.adjacentTurn turn i :=
  H.figure9_left hi hi_next hbad_i hbad_next D

/-- Build the W19 exact certificate from W12 selected witnesses plus the two
exact angle-containment inequalities. -/
def toExactAngleContainmentCertificate
    (H : ExactFigureAngleInequalities good turn)
    (figure8Witnesses :
      Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses good turn)
    (figure9Witnesses :
      Figure9ContainmentW12.AdjacentWindowWitnesses good turn) :
    ExactAngleContainmentCertificate good turn where
  figure8 :=
    { witnesses := figure8Witnesses
      central_angle_le_separatedTurn := H.figure8 }
  figure9 :=
    { witnesses := figure9Witnesses
      left_angle_le_adjacentTurn := H.figure9_left }

end ExactFigureAngleInequalities

/-! ## Local constructors -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

/-- Exact inequalities specialized to one M8 local label row. -/
abbrev LocalExactFigureAngleInequalities
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  ExactFigureAngleInequalities
    (M8BrokenLatticeGood localLabels.predicates.data)
    turnBounds.turn

/-- Local exact W22 data from W12 selected witnesses plus the two exact
containment inequalities. -/
def localExactData_of_w12WitnessesAndInequalities
    (figure8Witnesses :
      Figure8ContainmentW12.HonestFigure8SeparatedWindowDataWitnesses
        localLabels.predicates turnBounds.turn)
    (figure9Witnesses :
      Figure9ContainmentW12.HonestAdjacentWindowWitnesses
        localLabels.predicates turnBounds.turn)
    (H : LocalExactFigureAngleInequalities localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds where
  figure8Witnesses := figure8Witnesses
  figure8AngleContainment := H.figure8
  figure9Witnesses := figure9Witnesses
  figure9AngleContainment := H.figure9_left

/-- The exact inequality package carried by a local combined bridge. -/
def localInequalities_of_angleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalExactFigureAngleInequalities localLabels turnBounds :=
  ExactFigureAngleInequalities.ofAngleContainmentBridges A

/-- The exact inequality package carried by concrete local window fields. -/
def localInequalities_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalExactFigureAngleInequalities localLabels turnBounds :=
  ExactFigureAngleInequalities.ofContainmentInterfaces W.figure8 W.figure9_left

/-- Concrete local window fields give the W22 local exact data through the
explicit inequality package. -/
def localExactData_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  localExactData_of_w12WitnessesAndInequalities
    (Figure8ContainmentW12.dataWitnesses_of_localWindowContainmentFields W)
    (Figure9ContainmentW12.witnesses_of_containmentInterface W.figure9_left)
    (localInequalities_of_localWindowContainmentFields W)

/-- A combined concrete angle bridge gives the W22 local exact data. -/
def localExactData_of_angleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalExactAngleData localLabels turnBounds :=
  localExactData_of_localWindowContainmentFields
    (M8LocalWindowContainmentFields.ofAngleContainmentBridges A)

/-- A W19 local bridge row gives the W22 local exact data. -/
def localExactData_of_localBridgeInput
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  localExactData_of_angleContainmentBridges P.angleContainment

/-- A W19 exact local certificate gives the W22 local exact data. -/
def localExactData_of_localExactCertificate
    (H : LocalExactAngleContainmentCertificate localLabels turnBounds) :
    LocalExactAngleData localLabels turnBounds :=
  LocalExactAngleData.ofLocalExactCertificate H

/-- A combined concrete bridge gives the W19 local exact certificate. -/
def localExactCertificate_of_angleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalExactAngleContainmentCertificate localLabels turnBounds :=
  (localExactData_of_angleContainmentBridges A).toLocalExactCertificate

/-- A W19 local bridge row gives the W19 exact local certificate. -/
def localExactCertificate_of_localBridgeInput
    (P : LocalAngleContainmentBridgeProducerInput localLabels turnBounds) :
    LocalExactAngleContainmentCertificate localLabels turnBounds :=
  (localExactData_of_localBridgeInput P).toLocalExactCertificate

/-- A combined concrete bridge gives the W19 local bridge input after passing
through the W22 exact-data surface. -/
def localBridgeInput_of_angleContainmentBridges
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    LocalAngleContainmentBridgeProducerInput localLabels turnBounds :=
  (localExactData_of_angleContainmentBridges A).toLocalBridgeInput

/-- Concrete local window fields give the W19 local bridge input after
passing through the W22 exact-data surface. -/
def localBridgeInput_of_localWindowContainmentFields
    (W : M8LocalWindowContainmentFields localLabels turnBounds) :
    LocalAngleContainmentBridgeProducerInput localLabels turnBounds :=
  (localExactData_of_localWindowContainmentFields W).toLocalBridgeInput

/-! ## Euclidean witness projections -/

/-- Figure 8 selected Euclidean witnesses recovered from W22 exact data. -/
def figure8EuclideanFactWitnesses_of_localExactData
    (D : LocalExactAngleData localLabels turnBounds) :
    Figure8EuclideanFactsConcrete.HonestFigure8SeparatedEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  Figure8EuclideanFactsConcrete.euclideanFactWitnesses_of_containmentInterface
    D.toLocalExactCertificate.figure8.toContainmentInterface

/-- Figure 9 selected Euclidean witnesses recovered from W22 exact data. -/
def figure9EuclideanFactWitnesses_of_localExactData
    (D : LocalExactAngleData localLabels turnBounds) :
    Figure9EuclideanFactsConcrete.HonestFigure9AdjacentLeftEuclideanFactWitnesses
      localLabels.predicates turnBounds.turn :=
  Figure9EuclideanFactsConcrete.euclideanFactWitnesses_of_containmentInterface
    D.toLocalExactCertificate.figure9.toContainmentInterface

/-- W22 exact data implies the paired E22/E23 lower bounds via the concrete
Euclidean Figure 8/Figure 9 files. -/
theorem E22_E23_via_euclideanFactWitnesses
    (D : LocalExactAngleData localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  And.intro
    (Figure8EuclideanFactsConcrete.honestFigure8SeparatedWindowLowerE22_of_euclideanFactWitnesses
      (figure8EuclideanFactWitnesses_of_localExactData D))
    (Figure9EuclideanFactsConcrete.honestE23_of_euclideanFactWitnesses
      (figure9EuclideanFactWitnesses_of_localExactData D))

/-- A combined concrete bridge implies the paired E22/E23 bounds via the W22
exact-data surface and the Euclidean Figure files. -/
theorem E22_E23_of_angleContainmentBridges_via_euclideanFactWitnesses
    (A :
      AngleContainmentBridges
        (M8BrokenLatticeGood localLabels.predicates.data)
        turnBounds.turn) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  E22_E23_via_euclideanFactWitnesses
    (localExactData_of_angleContainmentBridges A)

/-! ## Family constructors -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- A W21 local bridge-input family gives the W22 local exact-data family. -/
def localExactDataFamily_of_localBridgeInputFamily
    (F : LocalBridgeInputFamily.{u} payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactData_of_localBridgeInput (F C hmin)

/-- A W20 bridge-source family gives the W22 local exact-data family. -/
def localExactDataFamily_of_baseBridgeSourceFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactData_of_localBridgeInput (F.row C hmin)

/-- A W21 local bridge-input family gives the W21 local exact certificate
family. -/
def localExactCertificateFamily_of_localBridgeInputFamily
    (F : LocalBridgeInputFamily.{u} payForCut topologyArc lemma8) :
    LocalExactCertificateFamily.{u} payForCut topologyArc lemma8 :=
  (localExactDataFamily_of_localBridgeInputFamily F).toLocalExactCertificateFamily

/-- A W20 bridge-source family gives the W20 exact source family. -/
def exactSourceFamily_of_baseBridgeSourceFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8 :=
  (localExactDataFamily_of_baseBridgeSourceFamily F).toExactSourceFamily

/-- Concrete local window-containment fields give the W20 exact source family
through the W23 explicit angle-containment constructors. -/
def exactSourceFamily_of_localWindowContainmentFieldsFamily
    (W : LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
      payForCut topologyArc lemma8 :=
  (LocalExactAngleDataFamily.ofLocalWindowContainmentFieldsFamily W).toExactSourceFamily

/-- A W20 bridge-source family is enough to inhabit the stronger W20 exact
source family. -/
theorem exactSourceFamily_nonempty_of_baseBridgeSourceFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro (exactSourceFamily_of_baseBridgeSourceFamily F)

/-- A W20 bridge-source family is enough to inhabit the W22 local exact-data
family. -/
theorem localExactDataFamily_nonempty_of_baseBridgeSourceFamily
    (F :
      FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (LocalExactAngleDataFamily.{u} payForCut topologyArc lemma8) :=
  Nonempty.intro (localExactDataFamily_of_baseBridgeSourceFamily F)

end FigureAngleContainmentConcreteW23
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW23ExactFigureAngleInequalities :=
  Swanepoel.FigureAngleContainmentConcreteW23.ExactFigureAngleInequalities

theorem swanepoelW23FigureExactSourceFamily_nonempty_of_bridgeSourceFamily
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (F :
      Swanepoel.FigureProducerFamilyW20.BaseAngleContainmentBridgeProducerFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (Swanepoel.FigureProducerFamilyW20.BaseExactAngleContainmentCertificateFamily.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.FigureAngleContainmentConcreteW23.exactSourceFamily_nonempty_of_baseBridgeSourceFamily
    F

end Verified
end ErdosProblems1066

end
