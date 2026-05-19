import ErdosProblems1066.Swanepoel.FigureInequalityRowsW31
import ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.Figure8ExplicitEuclideanFactsCompletionW33
import ErdosProblems1066.Swanepoel.Figure9EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.FrameCyclicOrderAssemblyW32
import ErdosProblems1066.Swanepoel.BoundaryAngleTurnW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 exact Figure row assembly from Euclidean inequality sources

This file refines the W31 row layer one step closer to the Figure 8/Figure 9
geometry.  The new source fields are not E22/E23 endpoint fields: they are
Euclidean distance witnesses together with the explicit angle-containment
inequalities that place the relevant geometric angles inside the turn windows.

Those source fields project to the W31 exact inequality rows, and therefore to
the existing W28/W29 exact E22/E23 source blocker.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace ExactFigureRowsAssemblyW32

open AngleContainmentBridgeProducerW19
open ExactFigureAngleDataSourceW29
open FigureAngleContainmentConcreteW23
open FigureAngleSourceInhabitationW21
open FigureExactAngleSourceW28
open FigureInequalityRowsW31
open FigureWitnessConcreteW27
open FrameCyclicOrderAssemblyW32
open Lemma10AnalyticBridge
open Lemma10AngleToTurn
open Lemma10Bridge
open M8ConstructionInterface
open MinimalGraphFacts
open BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage

universe u

/-! ## Euclidean source fields -/

/-- Figure 8 Euclidean inequality source fields: distance data plus the
explicit central-angle containment needed by E22. -/
abbrev Figure8EuclideanInequalitySourceFields
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts good turn

/-- Figure 9 Euclidean inequality source fields for the adjacent-left E23
route: distance data plus the explicit left-angle containment. -/
abbrev Figure9EuclideanInequalitySourceFields
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  Figure9EuclideanFactsConcrete.Figure9ExplicitEuclideanFacts good turn

/-- Combined Figure 8/Figure 9 Euclidean source fields for the E22/E23 route. -/
structure FigureEuclideanInequalitySourceFields
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop where
  figure8 : Figure8EuclideanInequalitySourceFields good turn
  figure9_left : Figure9EuclideanInequalitySourceFields good turn

/-! ## Atomic row obligations -/

/-- The raw Figure 8 distance witnesses, before the central-angle containment
comparison to the separated turn window. -/
abbrev Figure8DistanceWitnessRows (good : Nat -> Prop) : Prop :=
  forall {i j : Nat},
    1 <= i -> i + 1 < j -> j <= 10 ->
    Not (good i) -> Not (good j) ->
      Exists fun p : AngleBridgeFacts.Point =>
      Exists fun qi : AngleBridgeFacts.Point =>
      Exists fun qj : AngleBridgeFacts.Point =>
      Exists fun s : AngleBridgeFacts.Point =>
      Exists fun r : AngleBridgeFacts.Point =>
        AngleBridgeFacts.Figure8DistanceData p qi qj s r

/-- The actual Figure 8 angle-containment row: every admissible Figure 8
distance package has central angle contained in the separated turn window. -/
abbrev Figure8CentralAngleContainmentRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  Figure8UniversalAngleContainment good turn

/-- The raw Figure 9 adjacent-left distance witnesses, before left-angle
containment in the adjacent turn window. -/
abbrev Figure9DistanceWitnessRows (good : Nat -> Prop) : Prop :=
  forall {i : Nat},
    1 <= i -> i + 1 <= 10 ->
    Not (good i) -> Not (good (i + 1)) ->
      Exists fun p : AngleBridgeFacts.Point =>
      Exists fun qi : AngleBridgeFacts.Point =>
      Exists fun qj : AngleBridgeFacts.Point =>
      Exists fun s : AngleBridgeFacts.Point =>
      Exists fun r : AngleBridgeFacts.Point =>
        AngleBridgeFacts.Figure9DistanceData p qi qj s r

/-- The actual Figure 9 left-angle containment row: every admissible Figure 9
distance package has left comparison angle contained in the adjacent turn
window. -/
abbrev Figure9LeftAngleContainmentRows
    (good : Nat -> Prop) (turn : Nat -> Real) : Prop :=
  Figure9UniversalLeftAngleContainment good turn

/-- Figure 8's explicit Euclidean source field is exactly its raw distance
witness row plus its central-angle containment row. -/
theorem figure8EuclideanInequalitySourceFields_iff_distanceWitnessRows_and_centralAngleContainmentRows
    {good : Nat -> Prop} {turn : Nat -> Real} :
    Figure8EuclideanInequalitySourceFields good turn <->
      Figure8DistanceWitnessRows good /\
        Figure8CentralAngleContainmentRows good turn := by
  constructor
  case mp =>
    intro H
    exact And.intro H.distance_data H.central_angle_le_separatedTurn
  case mpr =>
    intro H
    exact
      { distance_data := H.1
        central_angle_le_separatedTurn := H.2 }

/-- Figure 9's explicit Euclidean source field is exactly its raw distance
witness row plus its left-angle containment row. -/
theorem figure9EuclideanInequalitySourceFields_iff_distanceWitnessRows_and_leftAngleContainmentRows
    {good : Nat -> Prop} {turn : Nat -> Real} :
    Figure9EuclideanInequalitySourceFields good turn <->
      Figure9DistanceWitnessRows good /\
        Figure9LeftAngleContainmentRows good turn := by
  constructor
  case mp =>
    intro H
    exact And.intro H.distance_data H.left_angle_le_adjacentTurn
  case mpr =>
    intro H
    exact
      { distance_data := H.1
        left_angle_le_adjacentTurn := H.2 }

namespace FigureEuclideanInequalitySourceFields

variable {good : Nat -> Prop} {turn : Nat -> Real}

/-- Project Figure 8's universal exact angle-containment inequality from the
Euclidean source fields. -/
def figure8AngleContainment
    (H : FigureEuclideanInequalitySourceFields good turn) :
    Figure8UniversalAngleContainment good turn :=
  H.figure8.central_angle_le_separatedTurn

/-- Project Figure 9's universal exact left-angle containment inequality from
the Euclidean source fields. -/
def figure9LeftAngleContainment
    (H : FigureEuclideanInequalitySourceFields good turn) :
    Figure9UniversalLeftAngleContainment good turn :=
  H.figure9_left.left_angle_le_adjacentTurn

/-- Forget the Euclidean source fields to the exact inequality package used by
W23/W30/W31. -/
def toExactFigureAngleInequalities
    (H : FigureEuclideanInequalitySourceFields good turn) :
    ExactFigureAngleInequalities good turn where
  figure8 := H.figure8AngleContainment
  figure9_left := H.figure9LeftAngleContainment

/-- Repackage the existing concrete angle-containment bridges as Euclidean
inequality source fields. -/
def ofAngleContainmentBridges
    (A : AngleContainmentInterface.AngleContainmentBridges good turn) :
    FigureEuclideanInequalitySourceFields good turn where
  figure8 :=
    Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.ofContainmentInterface
      A.figure8
  figure9_left :=
    Figure9EuclideanFactsConcrete.Figure9ExplicitEuclideanFacts.ofContainmentInterface
      A.figure9

/-- Selected Euclidean Figure witnesses plus exact universal angle
containment inequalities give the W32 source fields.  The selected witnesses
supply the distance data; the exact inequalities supply the angle-to-turn
containment for every compatible distance package. -/
def ofSelectedEuclideanWitnessesAndInequalities
    (figure8 :
      Figure8EuclideanFactsConcrete.Figure8SeparatedEuclideanFactWitnesses
        good turn)
    (figure9_left :
      Figure9EuclideanFactsConcrete.Figure9AdjacentLeftEuclideanFactWitnesses
        good turn)
    (H : ExactFigureAngleInequalities good turn) :
    FigureEuclideanInequalitySourceFields good turn where
  figure8 :=
    { distance_data := by
        intro i j hi hsep hj hbad_i hbad_j
        let D := figure8 (i := i) (j := j) hi hsep hj hbad_i hbad_j
        exact
          Exists.intro D.p
            (Exists.intro D.qi
              (Exists.intro D.qj
                (Exists.intro D.s
                  (Exists.intro D.r D.distanceData))))
      central_angle_le_separatedTurn := by
        intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
        exact H.figure8 hi hsep hj hbad_i hbad_j D }
  figure9_left :=
    { distance_data := by
        intro i hi hi_next hbad_i hbad_next
        let D := figure9_left (i := i) hi hi_next hbad_i hbad_next
        exact
          Exists.intro D.p
            (Exists.intro D.qi
              (Exists.intro D.qj
                (Exists.intro D.s
                  (Exists.intro D.r D.distanceData))))
      left_angle_le_adjacentTurn := by
        intro i p qi qj s r hi hi_next hbad_i hbad_next D
        exact H.figure9_left hi hi_next hbad_i hbad_next D }

/-- The Euclidean source fields derive the named E22/E23 lower-bound
hypotheses through the existing angle-to-turn bridge. -/
theorem E22_E23
    (H : FigureEuclideanInequalitySourceFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn /\
      Figure9AdjacentWindowLowerE23 good turn :=
  And.intro
    (Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.E22_via_selectedEuclideanFacts
      H.figure8)
    (Figure9EuclideanFactsConcrete.Figure9ExplicitEuclideanFacts.E23
      H.figure9_left)

theorem E22
    (H : FigureEuclideanInequalitySourceFields good turn) :
    Figure8SeparatedWindowLowerE22 good turn :=
  H.E22_E23.1

theorem E23
    (H : FigureEuclideanInequalitySourceFields good turn) :
    Figure9AdjacentWindowLowerE23 good turn :=
  H.E22_E23.2

end FigureEuclideanInequalitySourceFields

/-! ## Local rows -/

variable {n : Nat} {C : _root_.UDConfig n}
variable {localLabels : M8LocalLabels C}
variable {turnBounds : M8TurnBounds}

abbrev LocalGood (localLabels : M8LocalLabels C) : Nat -> Prop :=
  M8BrokenLatticeGood localLabels.predicates.data

/-- Local honest Euclidean source fields for one W21/W31 row. -/
abbrev LocalHonestEuclideanInequalitySourceFields
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) :=
  FigureEuclideanInequalitySourceFields
    (LocalGood localLabels) turnBounds.turn

/-- Local Figure 8 raw distance witnesses for one generated M8 row. -/
abbrev LocalFigure8DistanceWitnessRows
    (localLabels : M8LocalLabels C) : Prop :=
  Figure8DistanceWitnessRows (LocalGood localLabels)

/-- Local Figure 8 central-angle containment rows for one generated M8 row. -/
abbrev LocalFigure8CentralAngleContainmentRows
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) : Prop :=
  Figure8CentralAngleContainmentRows
    (LocalGood localLabels) turnBounds.turn

/-- Local Figure 9 raw distance witnesses for one generated M8 row. -/
abbrev LocalFigure9DistanceWitnessRows
    (localLabels : M8LocalLabels C) : Prop :=
  Figure9DistanceWitnessRows (LocalGood localLabels)

/-- Local Figure 9 left-angle containment rows for one generated M8 row. -/
abbrev LocalFigure9LeftAngleContainmentRows
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) : Prop :=
  Figure9LeftAngleContainmentRows
    (LocalGood localLabels) turnBounds.turn

/-- A local honest Euclidean source row is exactly the four actual Figure 8
and Figure 9 obligations: two distance-witness rows and two angle-containment
rows. -/
theorem localHonestEuclideanInequalitySourceFields_iff_distance_and_angle_rows
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds} :
    LocalHonestEuclideanInequalitySourceFields localLabels turnBounds <->
      LocalFigure8DistanceWitnessRows localLabels /\
        LocalFigure8CentralAngleContainmentRows localLabels turnBounds /\
        LocalFigure9DistanceWitnessRows localLabels /\
        LocalFigure9LeftAngleContainmentRows localLabels turnBounds := by
  constructor
  case mp =>
    intro H
    exact
      And.intro H.figure8.distance_data
        (And.intro H.figure8.central_angle_le_separatedTurn
          (And.intro H.figure9_left.distance_data
            H.figure9_left.left_angle_le_adjacentTurn))
  case mpr =>
    intro H
    exact
      { figure8 :=
          { distance_data := H.1
            central_angle_le_separatedTurn := H.2.1 }
        figure9_left :=
          { distance_data := H.2.2.1
            left_angle_le_adjacentTurn := H.2.2.2 } }

/-- Select W12 Figure 8 witnesses from the explicit Euclidean Figure 8 row.

The row stores distance data existentially because it is a `Prop`; the target
W12 witness family is data, so this constructor uses the ambient
noncomputable choice already used by the source-family adapters. -/
def figure8W12Witnesses_of_explicitEuclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H :
      Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts
        good turn) :
    Figure8ContainmentW12.Figure8SeparatedWindowDataWitnesses
      good turn :=
  fun {i j} hi hsep hj hbad_i hbad_j =>
    let hp :=
      H.distance_data (i := i) (j := j)
        hi hsep hj hbad_i hbad_j
    let p := Classical.choose hp
    let hqi := Classical.choose_spec hp
    let qi := Classical.choose hqi
    let hqj := Classical.choose_spec hqi
    let qj := Classical.choose hqj
    let hs := Classical.choose_spec hqj
    let s := Classical.choose hs
    let hr := Classical.choose_spec hs
    let r := Classical.choose hr
    let D := Classical.choose_spec hr
    { p := p
      qi := qi
      qj := qj
      s := s
      r := r
      distanceData := D
      central_angle_lower :=
        Figure8EuclideanFactsConcrete.central_angle_lower D
      central_angle_le_separatedTurn :=
        H.central_angle_le_separatedTurn
          hi hsep hj hbad_i hbad_j D }

/-- Select W12 Figure 9 witnesses from the explicit Euclidean Figure 9 row. -/
def figure9W12Witnesses_of_explicitEuclideanFacts
    {good : Nat -> Prop} {turn : Nat -> Real}
    (H :
      Figure9EuclideanFactsConcrete.Figure9ExplicitEuclideanFacts
        good turn) :
    Figure9ContainmentW12.AdjacentWindowWitnesses good turn :=
  fun {i} hi hi_next hbad_i hbad_next =>
    let hp :=
      H.distance_data (i := i) hi hi_next hbad_i hbad_next
    let p := Classical.choose hp
    let hqi := Classical.choose_spec hp
    let qi := Classical.choose hqi
    let hqj := Classical.choose_spec hqi
    let qj := Classical.choose hqj
    let hs := Classical.choose_spec hqj
    let s := Classical.choose hs
    let hr := Classical.choose_spec hs
    let r := Classical.choose hr
    let D := Classical.choose_spec hr
    { p := p
      qi := qi
      qj := qj
      s := s
      r := r
      distanceData := D
      left_angle_le_adjacentTurn :=
        H.left_angle_le_adjacentTurn
          hi hi_next hbad_i hbad_next D }

/-- A single local explicit Euclidean row supplies the W22 local exact angle
data: selected W12 witnesses plus the universal turn-containment
inequalities. -/
def localExactAngleData_of_localHonestEuclideanInequalitySourceFields
    (H :
      LocalHonestEuclideanInequalitySourceFields
        localLabels turnBounds) :
    FigureExactAngleCertificateInhabitationW22.LocalExactAngleData
      localLabels turnBounds where
  figure8Witnesses :=
    figure8W12Witnesses_of_explicitEuclideanFacts H.figure8
  figure8AngleContainment := H.figure8.central_angle_le_separatedTurn
  figure9Witnesses :=
    figure9W12Witnesses_of_explicitEuclideanFacts H.figure9_left
  figure9AngleContainment := H.figure9_left.left_angle_le_adjacentTurn

/-- Project local Euclidean source fields to the W31 exact inequality row. -/
def localExactFigureAngleInequalities_of_euclideanSources
    (H : LocalHonestEuclideanInequalitySourceFields
      localLabels turnBounds) :
    FigureInequalityRowsW31.LocalExactFigureAngleInequalities
      localLabels turnBounds :=
  H.toExactFigureAngleInequalities

/-- Project concrete local window-containment fields to the W32 Euclidean
source fields. -/
def localHonestEuclideanInequalitySourceFields_of_localWindowContainmentFields
    (W :
      M8WindowContainmentConcrete.M8LocalWindowContainmentFields
        localLabels turnBounds) :
    LocalHonestEuclideanInequalitySourceFields localLabels turnBounds :=
  FigureEuclideanInequalitySourceFields.ofAngleContainmentBridges
    { figure8 := W.figure8
      figure9 := W.figure9_left }

/-- Project the raw local Figure 8 distance-witness row from the concrete
local window-containment fields. -/
def localFigure8DistanceWitnessRows_of_localWindowContainmentFields
    (W :
      M8WindowContainmentConcrete.M8LocalWindowContainmentFields
        localLabels turnBounds) :
    LocalFigure8DistanceWitnessRows localLabels := by
  intro i j hi hsep hj hbad_i hbad_j
  let D :=
    M8WindowContainmentConcrete.M8LocalWindowContainmentFields.figure8ExtractedData
      W hi hsep hj hbad_i hbad_j
  exact
    Exists.intro D.p
      (Exists.intro D.qi
        (Exists.intro D.qj
          (Exists.intro D.s
            (Exists.intro D.r D.distanceData))))

/-- Project the local Figure 8 universal central-angle containment row from
the concrete local window-containment fields. -/
theorem localFigure8CentralAngleContainmentRows_of_localWindowContainmentFields
    (W :
      M8WindowContainmentConcrete.M8LocalWindowContainmentFields
        localLabels turnBounds) :
    LocalFigure8CentralAngleContainmentRows localLabels turnBounds := by
  intro i j p qi qj s r hi hsep hj hbad_i hbad_j D
  exact
    M8WindowContainmentConcrete.M8LocalWindowContainmentFields.figure8_central_angle_le_separatedTurn
      W hi hsep hj hbad_i hbad_j D

/-- Project the raw local Figure 9 adjacent-left distance-witness row from
the concrete local window-containment fields. -/
def localFigure9DistanceWitnessRows_of_localWindowContainmentFields
    (W :
      M8WindowContainmentConcrete.M8LocalWindowContainmentFields
        localLabels turnBounds) :
    LocalFigure9DistanceWitnessRows localLabels := by
  intro i hi hi_next hbad_i hbad_next
  let D :=
    M8WindowContainmentConcrete.M8LocalWindowContainmentFields.figure9LeftContainedData
      W hi hi_next hbad_i hbad_next
  exact
    Exists.intro D.p
      (Exists.intro D.qi
        (Exists.intro D.qj
          (Exists.intro D.s
            (Exists.intro D.r D.distanceData))))

/-- Project the local Figure 9 universal left-angle containment row from the
concrete local window-containment fields. -/
theorem localFigure9LeftAngleContainmentRows_of_localWindowContainmentFields
    (W :
      M8WindowContainmentConcrete.M8LocalWindowContainmentFields
        localLabels turnBounds) :
    LocalFigure9LeftAngleContainmentRows localLabels turnBounds := by
  intro i p qi qj s r hi hi_next hbad_i hbad_next D
  exact
    M8WindowContainmentConcrete.M8LocalWindowContainmentFields.figure9_left_angle_le_adjacentTurn
      W hi hi_next hbad_i hbad_next D

/-- Concrete local window-containment fields supply both atomic Figure 9
rows: selected distance witnesses and the left-angle containment inequality. -/
theorem localFigure9Rows_of_localWindowContainmentFields
    (W :
      M8WindowContainmentConcrete.M8LocalWindowContainmentFields
        localLabels turnBounds) :
    LocalFigure9DistanceWitnessRows localLabels /\
      LocalFigure9LeftAngleContainmentRows localLabels turnBounds :=
  And.intro
    (localFigure9DistanceWitnessRows_of_localWindowContainmentFields W)
    (localFigure9LeftAngleContainmentRows_of_localWindowContainmentFields W)

/-! ## Finite-label S5 and W11 turn-angle local adapters -/

/-- A finite frame-core label certificate plus its S5 angle rows gives the
W32 local honest Euclidean row.  The label certificate supplies the point
witness rows, and the S5 rows supply the two angle bounds. -/
def localHonestEuclideanInequalitySourceFields_of_labelCertificateS5AngleRows
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (H :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
        K turnBounds) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds where
  figure8 :=
    { distance_data := K.figure8DistanceWitnessRows
      central_angle_le_separatedTurn :=
        H.figure8CentralAngleLeSeparatedTurn }
  figure9_left :=
    { distance_data := K.figure9DistanceWitnessRows
      left_angle_le_adjacentTurn := H.figure9LeftAngleContainmentRows }

/-- Project the exact Figure 8 distance and central-angle containment rows from
finite-label S5 angle rows. -/
theorem localFigure8Rows_of_labelCertificateS5AngleRows
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (H :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
        K turnBounds) :
    LocalFigure8DistanceWitnessRows K.toM8LocalLabels /\
      LocalFigure8CentralAngleContainmentRows K.toM8LocalLabels turnBounds :=
  And.intro K.figure8DistanceWitnessRows
    H.figure8CentralAngleLeSeparatedTurn

/-- Convert the finite-label Figure 9 middle-turn upper-bound rows to the
actual left-angle containment rows used by W32. -/
def localFigure9LeftAngleContainmentRows_of_labelCertificateAngleLeMiddleTurnRows
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (H :
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
        (LocalGood K.toM8LocalLabels) turnBounds.turn) :
    LocalFigure9LeftAngleContainmentRows K.toM8LocalLabels turnBounds :=
  Figure9ContainmentConcrete.leftAngleContainmentRows_of_angleLeMiddleTurnRows
    turnBounds.turn_nonnegative H

/-- Project the exact Figure 9 distance and left-angle containment rows from
finite-label S5 angle rows.  The S5 package stores the weaker
`angle <= middle turn` row; this constructor performs the standard conversion
using the generated turn nonnegativity. -/
theorem localFigure9Rows_of_labelCertificateS5AngleRows
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (H :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
        K turnBounds) :
    LocalFigure9DistanceWitnessRows K.toM8LocalLabels /\
      LocalFigure9LeftAngleContainmentRows K.toM8LocalLabels turnBounds :=
  And.intro K.figure9DistanceWitnessRows
    (localFigure9LeftAngleContainmentRows_of_labelCertificateAngleLeMiddleTurnRows
      K turnBounds H.figure9LeftAngleLeMiddleTurn)

/-- Direct local-honest W32 row constructor from the finite-label Figure 8
central-angle containment row and the Figure 9 `angle <= middle turn` row.
The finite label certificate supplies both distance witness rows. -/
def localHonestEuclideanInequalitySourceFields_of_labelCertificateCentralAngleRowsAndFigure9AngleLeMiddleTurnRows
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (H8 :
      LocalFigure8CentralAngleContainmentRows K.toM8LocalLabels turnBounds)
    (H9 :
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
        (LocalGood K.toM8LocalLabels) turnBounds.turn) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds where
  figure8 :=
    { distance_data := K.figure8DistanceWitnessRows
      central_angle_le_separatedTurn := H8 }
  figure9_left :=
    { distance_data := K.figure9DistanceWitnessRows
      left_angle_le_adjacentTurn :=
        localFigure9LeftAngleContainmentRows_of_labelCertificateAngleLeMiddleTurnRows
          K turnBounds H9 }

/-- Direct local-honest W32 row constructor from the compact finite-label S5
row bundle. -/
def localHonestEuclideanInequalitySourceFields_of_labelCertificateS5FiniteLabelAngleRows
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (H :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5FiniteLabelAngleRows
        K turnBounds) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds where
  figure8 :=
    { distance_data := H.figure8DistanceWitnessRows
      central_angle_le_separatedTurn := H.figure8CentralAngleLeSeparatedTurn }
  figure9_left :=
    { distance_data := H.figure9DistanceWitnessRows
      left_angle_le_adjacentTurn := H.figure9LeftAngleContainmentRows }

/-- W11 turn-angle Figure 8 interval rows plus pointwise Figure 9 cosine
comparisons give the W32 local honest Euclidean row. -/
def localHonestEuclideanInequalitySourceFields_of_w11TurnAngleIccRowsAndCosineComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (hmin : IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure8CentralAngleTurnAngleIccSubwindowRows
        R C hmin a K)
    (H9 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure9AdjacentLeftTurnAngleCosineComparisonRows
        R C hmin a K) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds :=
  localHonestEuclideanInequalitySourceFields_of_labelCertificateS5AngleRows
    K turnBounds
    (MinimalBoundaryTopologyBoundaryTurnAngleRows.s5AngleRows_of_actualTurnIccRowsAndCosineComparisonRows
      R C hmin a K turnBounds hturn
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure8CentralAngleActualTurnIccSubwindowRows_of_turnAngleRows
        R C hmin a K H8)
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure9AdjacentLeftActualTurnCosineComparisonRows_of_turnAngleRows
        R C hmin a K H9))

/-- W11 turn-angle Figure 8 interval rows plus pointwise Figure 9 chord
comparisons give the W32 local honest Euclidean row. -/
def localHonestEuclideanInequalitySourceFields_of_w11TurnAngleIccRowsAndChordComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (hmin : IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure8CentralAngleTurnAngleIccSubwindowRows
        R C hmin a K)
    (H9 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure9AdjacentLeftTurnAngleChordComparisonRows
        R C hmin a K) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds :=
  localHonestEuclideanInequalitySourceFields_of_labelCertificateS5AngleRows
    K turnBounds
    (MinimalBoundaryTopologyBoundaryTurnAngleRows.s5AngleRows_of_actualTurnIccRowsAndTurnChordComparisonRows
      R C hmin a K turnBounds hturn
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure8CentralAngleActualTurnIccSubwindowRows_of_turnAngleRows
        R C hmin a K H8)
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure9AdjacentLeftActualTurnChordComparisonRows_of_turnAngleRows
        R C hmin a K H9))

/-- W11 turn-angle Figure 8 indexed rows plus pointwise Figure 9 cosine
comparisons give the W32 local honest Euclidean row. -/
def localHonestEuclideanInequalitySourceFields_of_w11TurnAngleIndexedRowsAndCosineComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (hmin : IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure8CentralAngleTurnAngleIndexedSubwindowRows
        R C hmin a K)
    (H9 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure9AdjacentLeftTurnAngleCosineComparisonRows
        R C hmin a K) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds :=
  localHonestEuclideanInequalitySourceFields_of_labelCertificateS5AngleRows
    K turnBounds
    (MinimalBoundaryTopologyBoundaryTurnAngleRows.s5AngleRows_of_actualTurnIndexedRowsAndCosineComparisonRows
      R C hmin a K turnBounds hturn
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure8CentralAngleActualTurnIndexedSubwindowRows_of_turnAngleRows
        R C hmin a K H8)
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure9AdjacentLeftActualTurnCosineComparisonRows_of_turnAngleRows
        R C hmin a K H9))

/-- W11 turn-angle Figure 8 indexed rows plus pointwise Figure 9 chord
comparisons give the W32 local honest Euclidean row. -/
def localHonestEuclideanInequalitySourceFields_of_w11TurnAngleIndexedRowsAndChordComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (hmin : IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        (S.row C hmin).planarBoundary connectedNoCut hmin)
    (turnBounds : M8TurnBounds)
    (hturn : turnBounds.turn = R.rawTurn C hmin a)
    (H8 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure8CentralAngleTurnAngleIndexedSubwindowRows
        R C hmin a K)
    (H9 :
      MinimalBoundaryTopologyBoundaryTurnAngleRows.Figure9AdjacentLeftTurnAngleChordComparisonRows
        R C hmin a K) :
    LocalHonestEuclideanInequalitySourceFields K.toM8LocalLabels turnBounds :=
  localHonestEuclideanInequalitySourceFields_of_labelCertificateS5AngleRows
    K turnBounds
    (MinimalBoundaryTopologyBoundaryTurnAngleRows.s5AngleRows_of_actualTurnIndexedRowsAndTurnChordComparisonRows
      R C hmin a K turnBounds hturn
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure8CentralAngleActualTurnIndexedSubwindowRows_of_turnAngleRows
        R C hmin a K H8)
      (MinimalBoundaryTopologyBoundaryTurnAngleRows.figure9AdjacentLeftActualTurnChordComparisonRows_of_turnAngleRows
        R C hmin a K H9))

/-- Build the local W32 Euclidean source fields from the W31 selected
Euclidean witnesses and exact angle-containment inequalities. -/
def localHonestEuclideanInequalitySourceFields_of_selectedFigureAndInequalities
    (W :
      FigureInequalityRowsW31.LocalSelectedFigureWitnessFields
        localLabels turnBounds)
    (H :
      FigureInequalityRowsW31.LocalExactFigureAngleInequalities
        localLabels turnBounds) :
    LocalHonestEuclideanInequalitySourceFields localLabels turnBounds :=
  FigureEuclideanInequalitySourceFields.ofSelectedEuclideanWitnessesAndInequalities
    W.figure8Euclidean W.figure9Euclidean H

/-- A local W32 assembly row: selected Figure witnesses plus honest Euclidean
inequality source fields for the same row. -/
structure LocalExactFigureRowsAssembly
    (localLabels : M8LocalLabels C) (turnBounds : M8TurnBounds) where
  selectedFigure :
    FigureInequalityRowsW31.LocalSelectedFigureWitnessFields
      localLabels turnBounds
  euclideanSources :
    LocalHonestEuclideanInequalitySourceFields localLabels turnBounds

namespace LocalExactFigureRowsAssembly

variable {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}

/-- Convert a W32 local assembly row to the W31 exact Figure inequality row. -/
def toLocalExactFigureInequalityRows
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    LocalExactFigureInequalityRows localLabels turnBounds where
  selectedFigure := R.selectedFigure
  exactInequalities :=
    localExactFigureAngleInequalities_of_euclideanSources
      R.euclideanSources

/-- Convert a W32 local assembly row to the W29 source row. -/
def toLocalExactFigureAngleDataSource
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSource
      localLabels turnBounds :=
  R.toLocalExactFigureInequalityRows.toLocalExactFigureAngleDataSource

/-- Convert a W32 local assembly row to the W28 exact source row. -/
def toLocalExactFigureWitnessSource
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    LocalExactFigureWitnessSource localLabels turnBounds :=
  R.toLocalExactFigureInequalityRows.toLocalExactFigureWitnessSource

/-- Project the exact inequalities carried by the W32 row. -/
def toLocalExactFigureAngleInequalities
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    FigureInequalityRowsW31.LocalExactFigureAngleInequalities
      localLabels turnBounds :=
  R.toLocalExactFigureInequalityRows.toLocalExactFigureAngleInequalities

/-- The W32 row proves E22/E23 directly from its Euclidean source fields. -/
theorem E22_E23
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  R.euclideanSources.E22_E23

/-- The same E22/E23 pair, routed through the W31 exact-row package. -/
theorem E22_E23_via_exactRows
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  R.toLocalExactFigureInequalityRows.E22_E23

/-- Compatibility name for the direct Euclidean-source E22/E23 projection. -/
theorem E22_E23_via_euclideanSources
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  R.E22_E23

theorem E22
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    HonestFigure8SeparatedWindowLowerE22
        localLabels.predicates turnBounds.turn :=
  R.E22_E23.1

theorem E23
    (R : LocalExactFigureRowsAssembly localLabels turnBounds) :
    HonestFigure9AdjacentWindowLowerE23
        localLabels.predicates turnBounds.turn :=
  R.E22_E23.2

end LocalExactFigureRowsAssembly

/-! ## Family rows -/

variable {payForCut : PayForCutConcreteProducerFamily}
variable {topologyArc : TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc}

/-- Family-level honest Euclidean source fields over the W21 base rows. -/
abbrev LocalHonestEuclideanInequalitySourceFieldsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalHonestEuclideanInequalitySourceFields
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

/-- Family-level Figure 8 raw distance witnesses over the generated W21 base
rows. -/
abbrev LocalFigure8DistanceWitnessRowsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalFigure8DistanceWitnessRows
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels

/-- Family-level Figure 8 central-angle containment rows over the generated
W21 base rows. -/
abbrev LocalFigure8CentralAngleContainmentRowsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalFigure8CentralAngleContainmentRows
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

/-- Family-level Figure 9 raw adjacent-left distance witnesses over the
generated W21 base rows. -/
abbrev LocalFigure9DistanceWitnessRowsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalFigure9DistanceWitnessRows
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels

/-- Family-level Figure 9 left-angle containment rows over the generated W21
base rows. -/
abbrev LocalFigure9LeftAngleContainmentRowsFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      LocalFigure9LeftAngleContainmentRows
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds

/-- Family-level honest Euclidean rows are exactly the four atomic Figure
distance/angle row families. -/
theorem localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows :
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8 <->
      LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
        LocalFigure8CentralAngleContainmentRowsFamily.{u}
          payForCut topologyArc lemma8 /\
        LocalFigure9DistanceWitnessRowsFamily.{u}
          payForCut topologyArc lemma8 /\
        LocalFigure9LeftAngleContainmentRowsFamily.{u}
          payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro H
    refine And.intro ?h8D ?rest
    · intro n C hmin
      exact (H C hmin).figure8.distance_data
    · refine And.intro ?h8A ?rest2
      · intro n C hmin
        exact (H C hmin).figure8.central_angle_le_separatedTurn
      · refine And.intro ?h9D ?h9A
        · intro n C hmin
          exact (H C hmin).figure9_left.distance_data
        · intro n C hmin
          exact (H C hmin).figure9_left.left_angle_le_adjacentTurn
  case mpr =>
    intro H n C hmin
    exact
      { figure8 :=
          { distance_data := H.1 C hmin
            central_angle_le_separatedTurn := H.2.1 C hmin }
        figure9_left :=
          { distance_data := H.2.2.1 C hmin
            left_angle_le_adjacentTurn := H.2.2.2 C hmin } }

/-- Project the Figure 8 raw distance-witness rows from row-wise honest
Euclidean source fields. -/
def localFigure8DistanceWitnessRowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  ((localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).1 H).1

/-- Project the Figure 8 central-angle containment rows from row-wise honest
Euclidean source fields. -/
def localFigure8CentralAngleContainmentRowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8CentralAngleContainmentRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  ((localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).1 H).2.1

/-- Project the Figure 9 raw adjacent-left distance-witness rows from row-wise
honest Euclidean source fields. -/
def localFigure9DistanceWitnessRowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure9DistanceWitnessRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  ((localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).1 H).2.2.1

/-- Project the Figure 9 left-angle containment rows from row-wise honest
Euclidean source fields. -/
def localFigure9LeftAngleContainmentRowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure9LeftAngleContainmentRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  ((localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).1 H).2.2.2

/-- Project the exact four atomic Figure 8/Figure 9 distance and angle row
families from row-wise honest Euclidean source fields. -/
theorem distance_and_angle_rowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure8CentralAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9LeftAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 :=
  (localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).1 H

/-- Build row-wise honest Euclidean source fields from the four atomic Figure
8/Figure 9 distance and angle row families. -/
theorem localHonestEuclideanInequalitySourceFieldsFamily_of_distance_and_angle_rows
    (H8D :
      LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8)
    (H8A :
      LocalFigure8CentralAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8)
    (H9D :
      LocalFigure9DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8)
    (H9A :
      LocalFigure9LeftAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  (localHonestEuclideanInequalitySourceFieldsFamily_iff_distance_and_angle_rows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)).2
    (And.intro H8D (And.intro H8A (And.intro H9D H9A)))

/-- Build the actual W31 exact Figure inequality rows directly from selected
Figure witnesses plus W32 Euclidean inequality source rows. -/
def exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndEuclideanSources
    (W : FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { selectedFigure := W.row C hmin
      exactInequalities :=
        localExactFigureAngleInequalities_of_euclideanSources
          (H C hmin) }

/-- W32 family of exact Figure row assemblies from selected witness rows and
honest Euclidean inequality source rows. -/
structure ExactFigureRowsAssemblyFamily
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Type (u + 1) where
  selectedFigure :
    FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8
  euclideanSources :
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8

namespace ExactFigureRowsAssemblyFamily

/-- Project a W32 family to the W31 exact inequality family. -/
def toLocalExactFigureAngleInequalitiesFamily
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.LocalExactFigureAngleInequalitiesFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localExactFigureAngleInequalities_of_euclideanSources
      (F.euclideanSources C hmin)

/-- Convert a W32 assembly family to W31 exact Figure inequality rows. -/
def toExactFigureInequalityRowsFamily
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8 :=
  exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndEuclideanSources
    F.selectedFigure F.euclideanSources

/-- Convert a W32 assembly family to the W29 data-source family. -/
def toLocalExactFigureAngleDataSourceFamily
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    { selectedFigure := F.selectedFigure.row C hmin
      exactInequalities :=
        localExactFigureAngleInequalities_of_euclideanSources
          (F.euclideanSources C hmin) }

/-- Convert a W32 assembly family to the W28 exact source family. -/
def toLocalExactFigureWitnessSourceFamily
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.LocalExactFigureWitnessSourceFamily.{u}
      payForCut topologyArc lemma8 :=
  F.toLocalExactFigureAngleDataSourceFamily.toLocalExactFigureWitnessSourceFamily

/-- W32 assembly rows discharge the W28 exact E22/E23 source blocker through
the exact angle-data source family built from their Euclidean fields. -/
theorem exactE22E23SourceBlocker
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
      payForCut topologyArc lemma8 :=
  ExactFigureAngleDataSourceW29.LocalExactFigureAngleDataSourceFamily.exactE22E23SourceBlocker
    F.toLocalExactFigureAngleDataSourceFamily

/-- Row-wise E22/E23 projection directly from the Euclidean source fields. -/
theorem row_E22_E23
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  (F.euclideanSources C hmin).E22_E23

/-- Row-wise E22/E23 projection routed through the W31 exact-row package. -/
theorem row_E22_E23_via_exactRows
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  F.toExactFigureInequalityRowsFamily.row_E22_E23 C hmin

/-- Compatibility name for the direct Euclidean-source row projection. -/
theorem row_E22_E23_via_euclideanSources
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    HonestFigure8SeparatedWindowLowerE22
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        (BaseInputs payForCut topologyArc lemma8 C hmin).localLabels.predicates
        (BaseInputs payForCut topologyArc lemma8 C hmin).turnBounds.turn :=
  F.row_E22_E23 C hmin

/-- Project the exact four atomic Figure 8/Figure 9 distance and angle row
families carried by a W32 assembly family. -/
theorem distance_and_angle_rowsFamily
    (F : ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure8CentralAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9LeftAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 :=
  distance_and_angle_rowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    F.euclideanSources

end ExactFigureRowsAssemblyFamily

/-! ## Constructors and blockers -/

/-- Build W32 assembly rows from selected Figure witnesses and Euclidean
inequality source fields. -/
def exactFigureRowsAssemblyFamily_of_selectedFigureWitnessFieldsAndEuclideanSources
    (W : FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8 where
  selectedFigure := W
  euclideanSources := H

/-- Selected Figure witnesses plus W32 Euclidean inequality source rows
directly inhabit the actual W31 exact Figure inequality row blocker. -/
theorem exactFigureInequalityRowsBlocker_of_selectedFigureWitnessFieldsAndEuclideanSources
    (W : FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8)
    (H : LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsBlocker.{u}
      payForCut topologyArc lemma8 :=
  Nonempty.intro
    (exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndEuclideanSources
      W H)

/-- Project concrete local window-containment field families to W32 Euclidean
source field families. -/
def localHonestEuclideanInequalitySourceFieldsFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localHonestEuclideanInequalitySourceFields_of_localWindowContainmentFields
      (W C hmin)

/-- Project family-level raw Figure 8 distance-witness rows from concrete
local window-containment fields. -/
def localFigure8DistanceWitnessRowsFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
      payForCut topologyArc lemma8 := fun C hmin =>
  localFigure8DistanceWitnessRows_of_localWindowContainmentFields
    (W C hmin)

/-- Project family-level Figure 8 universal central-angle containment rows
from concrete local window-containment fields. -/
theorem localFigure8CentralAngleContainmentRowsFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8CentralAngleContainmentRowsFamily.{u}
      payForCut topologyArc lemma8 := fun C hmin =>
  localFigure8CentralAngleContainmentRows_of_localWindowContainmentFields
    (W C hmin)

/-- Project family-level raw Figure 9 adjacent-left distance-witness rows from
concrete local window-containment fields. -/
def localFigure9DistanceWitnessRowsFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure9DistanceWitnessRowsFamily.{u}
      payForCut topologyArc lemma8 := fun C hmin =>
  localFigure9DistanceWitnessRows_of_localWindowContainmentFields
    (W C hmin)

/-- Project family-level Figure 9 left-angle containment rows from concrete
local window-containment fields. -/
theorem localFigure9LeftAngleContainmentRowsFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure9LeftAngleContainmentRowsFamily.{u}
      payForCut topologyArc lemma8 := fun C hmin =>
  localFigure9LeftAngleContainmentRows_of_localWindowContainmentFields
    (W C hmin)

/-- Concrete local window-containment fields expose all four atomic
Figure 8/Figure 9 distance and angle row families. -/
theorem distance_and_angle_rowsFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure8CentralAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9LeftAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 :=
  distance_and_angle_rowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (localHonestEuclideanInequalitySourceFieldsFamily_of_localWindowContainmentFieldsFamily
      W)

/-- Project W31 selected-witness rows and exact inequality rows to W32 honest
Euclidean source rows. -/
def localHonestEuclideanInequalitySourceFieldsFamily_of_selectedFigureAndInequalities
    (W :
      FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8)
    (H :
      FigureInequalityRowsW31.LocalExactFigureAngleInequalitiesFamily.{u}
        payForCut topologyArc lemma8) :
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localHonestEuclideanInequalitySourceFields_of_selectedFigureAndInequalities
      (W.row C hmin) (H C hmin)

/-- Selected Figure witnesses plus exact inequality rows project to the exact
four atomic Figure 8/Figure 9 distance and angle row families.  The distance
rows come from the selected witnesses; the angle rows still require the exact
inequality family. -/
theorem distance_and_angle_rowsFamily_of_selectedFigureAndInequalities
    (W :
      FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8)
    (H :
      FigureInequalityRowsW31.LocalExactFigureAngleInequalitiesFamily.{u}
        payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure8CentralAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9LeftAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 :=
  distance_and_angle_rowsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (localHonestEuclideanInequalitySourceFieldsFamily_of_selectedFigureAndInequalities
      W H)

/-- Row-wise explicit Euclidean source fields construct the W22 local exact
angle-data family. -/
def localExactAngleDataFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
      payForCut topologyArc lemma8 where
  row := fun C hmin =>
    localExactAngleData_of_localHonestEuclideanInequalitySourceFields
      (H C hmin)

/-- Row-wise explicit Euclidean source fields assemble W32 exact Figure
rows. -/
def exactFigureRowsAssemblyFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8 where
  selectedFigure :=
    FigureWitnessConcreteW27.LocalSelectedFigureWitnessFieldsFamily.ofLocalExactAngleDataFamily
      (localExactAngleDataFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
        H)
  euclideanSources := H

/-- Row-wise explicit Euclidean source fields also select the W31/W27 Figure
witness family used by the W32 assembly rows. -/
def selectedFigureWitnessFieldsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  (exactFigureRowsAssemblyFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
    H).selectedFigure

/-- Row-wise explicit Euclidean source fields inhabit the selected Figure
witness family surface. -/
theorem selectedFigureWitnessFieldsFamily_nonempty_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (selectedFigureWitnessFieldsFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
      H)

/-- Row-wise explicit Euclidean source fields inhabit the W22 local exact
angle-data family. -/
theorem localExactAngleDataFamily_nonempty_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
        payForCut topologyArc lemma8) :=
  Nonempty.intro
    (localExactAngleDataFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
      H)

/-- A W22 local exact angle-data family projects back to row-wise explicit
Euclidean source fields. -/
def localHonestEuclideanInequalitySourceFieldsFamily_of_localExactAngleDataFamily
    (F :
      FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
        payForCut topologyArc lemma8) :
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8 :=
  fun C hmin =>
    localHonestEuclideanInequalitySourceFields_of_selectedFigureAndInequalities
      (FigureWitnessConcreteW27.localSelectedFigureWitnessFields_of_localExactAngleData
        (F.row C hmin))
      (ExactFigureInequalitiesW30.localExactFigureAngleInequalities_of_localExactAngleData
        (F.row C hmin))

/-- The W22 local exact angle-data family is equivalent to the row-wise
explicit Euclidean source rows. -/
theorem localExactAngleDataFamily_nonempty_iff_localHonestEuclideanInequalitySourceFieldsFamily :
    Nonempty
        (FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{u}
          payForCut topologyArc lemma8) <->
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          localHonestEuclideanInequalitySourceFieldsFamily_of_localExactAngleDataFamily
            F
  case mpr =>
    exact
      localExactAngleDataFamily_nonempty_of_localHonestEuclideanInequalitySourceFieldsFamily

/-- Concrete local window-containment field families assemble into W32 rows. -/
def exactFigureRowsAssemblyFamily_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8 where
  selectedFigure :=
    LocalSelectedFigureWitnessFieldsFamily.ofLocalWindowContainmentFieldsFamily
      W
  euclideanSources :=
    localHonestEuclideanInequalitySourceFieldsFamily_of_localWindowContainmentFieldsFamily
      W

/-- W32 assembly blocker: inhabited assembly rows. -/
abbrev ExactFigureRowsAssemblyBlocker
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Nonempty
    (ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8)

/-- The honest Euclidean source components needed to build W32 rows. -/
abbrev HonestEuclideanInequalitySourceComponents
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u})
    (lemma8 : Lemma8ConcreteProducerFamily.{u} payForCut topologyArc) :
    Prop :=
  Exists fun _ :
      FigureInequalityRowsW31.LocalSelectedFigureWitnessFieldsFamily.{u}
        payForCut topologyArc lemma8 =>
    LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
      payForCut topologyArc lemma8

/-- Repackage W31 exact Figure inequality rows as W32 assembly rows.  The W31
selected witnesses provide the Euclidean distance payload, while the W31 exact
inequalities provide the angle-containment payload. -/
def exactFigureRowsAssemblyFamily_of_exactFigureInequalityRowsFamily
    (F : FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyFamily.{u}
      payForCut topologyArc lemma8 where
  selectedFigure := F.toSelectedFigureWitnessFieldsFamily
  euclideanSources :=
    localHonestEuclideanInequalitySourceFieldsFamily_of_selectedFigureAndInequalities
      F.toSelectedFigureWitnessFieldsFamily
      F.toLocalExactFigureAngleInequalitiesFamily

/-- W31 exact Figure inequality rows inhabit the W32 honest Euclidean source
component surface. -/
def honestEuclideanInequalitySourceComponents_of_exactFigureInequalityRowsFamily
    (F : FigureInequalityRowsW31.ExactFigureInequalityRowsFamily.{u}
      payForCut topologyArc lemma8) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8 :=
  Exists.intro F.toSelectedFigureWitnessFieldsFamily
    (localHonestEuclideanInequalitySourceFieldsFamily_of_selectedFigureAndInequalities
      F.toSelectedFigureWitnessFieldsFamily
      F.toLocalExactFigureAngleInequalitiesFamily)

/-- W31 exact Figure row components provide the W32 honest Euclidean source
components: selected Euclidean witnesses supply distance data, and the exact
inequalities supply the angle-containment fields. -/
theorem components_of_exactFigureInequalityRowComponents
    (h :
      FigureInequalityRowsW31.ExactFigureInequalityRowComponents.{u}
        payForCut topologyArc lemma8) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8 := by
  cases h with
  | intro W H =>
      exact
        Exists.intro W
          (localHonestEuclideanInequalitySourceFieldsFamily_of_selectedFigureAndInequalities
            W H)

/-- W32 assembly rows are exactly selected witness rows plus honest Euclidean
source fields. -/
theorem exactFigureRowsAssemblyBlocker_iff_components :
    ExactFigureRowsAssemblyBlocker.{u} payForCut topologyArc lemma8 <->
      HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Exists.intro F.selectedFigure F.euclideanSources
  case mpr =>
    intro h
    cases h with
    | intro W H =>
        exact Nonempty.intro
          (exactFigureRowsAssemblyFamily_of_selectedFigureWitnessFieldsAndEuclideanSources
            W H)

/-- Project W32 assembly rows to their honest Euclidean source components. -/
theorem components_of_exactFigureRowsAssemblyBlocker
    (h : ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8 :=
  exactFigureRowsAssemblyBlocker_iff_components.1 h

/-- Honest Euclidean source components build W32 exact Figure assembly rows. -/
theorem exactFigureRowsAssemblyBlocker_of_components
    (h : HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8 :=
  exactFigureRowsAssemblyBlocker_iff_components.2 h

/-- Row-wise explicit Euclidean source fields inhabit W32 exact Figure
assembly rows. -/
theorem exactFigureRowsAssemblyBlocker_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8 :=
  Nonempty.intro
    (exactFigureRowsAssemblyFamily_of_localHonestEuclideanInequalitySourceFieldsFamily
      H)

/-- W32 exact Figure assembly rows are equivalent to row-wise explicit
Euclidean source fields. -/
theorem exactFigureRowsAssemblyBlocker_iff_localHonestEuclideanInequalitySourceFieldsFamily :
    ExactFigureRowsAssemblyBlocker.{u}
        payForCut topologyArc lemma8 <->
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h n C hmin
    cases h with
    | intro F =>
        exact F.euclideanSources C hmin
  case mpr =>
    exact
      exactFigureRowsAssemblyBlocker_of_localHonestEuclideanInequalitySourceFieldsFamily

/-- An inhabited W32 assembly blocker exposes the exact four atomic
Figure 8/Figure 9 distance and angle row families. -/
theorem distance_and_angle_rowsFamily_of_exactFigureRowsAssemblyBlocker
    (h : ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8) :
    LocalFigure8DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure8CentralAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9DistanceWitnessRowsFamily.{u}
        payForCut topologyArc lemma8 /\
      LocalFigure9LeftAngleContainmentRowsFamily.{u}
        payForCut topologyArc lemma8 := by
  cases h with
  | intro F =>
      exact F.distance_and_angle_rowsFamily

/-- Honest Euclidean source components are exactly the row-wise explicit
Euclidean Figure 8/Figure 9 source fields.  The selected witness component is
recovered from the local exact angle data built by those rows. -/
theorem honestEuclideanInequalitySourceComponents_iff_localHonestEuclideanInequalitySourceFieldsFamily :
    HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8 <->
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8 :=
  exactFigureRowsAssemblyBlocker_iff_components.symm.trans
    exactFigureRowsAssemblyBlocker_iff_localHonestEuclideanInequalitySourceFieldsFamily

/-- Row-wise explicit Euclidean Figure 8/Figure 9 source fields inhabit the
W32 honest Euclidean source-component surface. -/
theorem honestEuclideanInequalitySourceComponents_of_localHonestEuclideanInequalitySourceFieldsFamily
    (H :
      LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8 :=
  honestEuclideanInequalitySourceComponents_iff_localHonestEuclideanInequalitySourceFieldsFamily.2
    H

/-! ## Selected frame/cyclic containment-interface integration -/

/-- The selected frame/cyclic source package whose generated Lemma 8 rows feed
the compact Figure source. -/
abbrev FrameCyclicSourcePackage
    (payForCut : PayForCutConcreteProducerFamily)
    (topologyArc : TopologyArcConcreteProducerFamily.{u}) :
    Type (u + 1) :=
  FrameCyclicOrderAssemblyW32.FrameCyclicOrderSourcePackage.{u}
    payForCut topologyArc

/-- The concrete Lemma 8 producer family generated by a selected frame/cyclic
source package. -/
def lemma8ConcreteOfFrameCyclicSource
    (P :
      FrameCyclicSourcePackage.{u}
        payForCut topologyArc) :
    Lemma8ConcreteProducerFamily.{u} payForCut topologyArc :=
  P.toGeometryFieldFamily.toLemma8ConcreteProducerFamily

/-! ### Finite-PQ generated S5 row surface -/

/-- The frame/cyclic source package generated by finite-`p_i/q_i` rows. -/
abbrev FrameCyclicSourceOfFinitePQSpineGeneratedOrderRows
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) :
    FrameCyclicSourcePackage.{u} payForCut topologyArc :=
  FrameCyclicOrderAssemblyW32.frameCyclicOrderSourcePackageOfFinitePQSpineGeneratedOrderRows
    (payForCut := payForCut) (topologyArc := topologyArc) rows

/-- The Lemma 8 concrete source generated by finite-`p_i/q_i` rows. -/
abbrev Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) :
    Lemma8ConcreteProducerFamily.{u} payForCut topologyArc :=
  lemma8ConcreteOfFrameCyclicSource
    (FrameCyclicSourceOfFinitePQSpineGeneratedOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) rows)

/-- Row-wise W32 honest Euclidean sources for a finite-`p_i/q_i` generated
frame/cyclic source. -/
abbrev LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) : Prop :=
  LocalHonestEuclideanInequalitySourceFieldsFamily.{u}
    payForCut topologyArc
    (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) rows)

/-- Figure 8 central-angle containment rows for a finite-`p_i/q_i` generated
frame/cyclic source. -/
abbrev Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) : Prop :=
  LocalFigure8CentralAngleContainmentRowsFamily.{u}
    payForCut topologyArc
    (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) rows)

/-- Positive Figure 8 S5 angle rows for a finite-`p_i/q_i` generated
source, named by their actual content: the central angle is bounded by the
separated turn window. -/
abbrev Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) : Prop :=
  Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
    (payForCut := payForCut) (topologyArc := topologyArc) rows

/-- Figure 9 left-angle containment rows for a finite-`p_i/q_i` generated
frame/cyclic source. -/
abbrev Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) : Prop :=
  LocalFigure9LeftAngleContainmentRowsFamily.{u}
    payForCut topologyArc
    (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
      (payForCut := payForCut) (topologyArc := topologyArc) rows)

/-- Figure 9 `angle <= middle turn` rows for a finite-`p_i/q_i` generated
frame/cyclic source.  These are intentionally weaker than the final
left-angle containment rows; turn nonnegativity performs the conversion. -/
abbrev Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Figure9ContainmentConcrete.Figure9AdjacentLeftAngleLeMiddleTurnRows
        (LocalGood
          (BaseInputs payForCut topologyArc
            (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) rows)
            C hmin).localLabels)
        (BaseInputs payForCut topologyArc
          (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc) rows)
          C hmin).turnBounds.turn

/-- The pointwise finite boundary frame-core label certificate generated by
the finite-`p_i/q_i` frame/cyclic rows. -/
def finitePQSpineGeneratedOrderFrameCoreLabelCertificate
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
      (topologyArc.row C hmin).arcBoundaryBudget.planarBoundary
      (FrameCyclicOrderAssemblyW32.PointwiseConnectedNoCutCertificate
        (payForCut := payForCut) C hmin)
      hmin where
  finiteLabels :=
    FrameCyclicOrderAssemblyW32.PointwiseFinitePQSpineCertificate
      (topologyArc := topologyArc) C hmin
  frameCoreFields := rows.frameCoreFields C hmin
  lemma8 :=
    FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.lemma8
      (payForCut := payForCut) (topologyArc := topologyArc) rows C hmin

/-- Row-wise S5 angle rows for the generated finite-label certificate. -/
abbrev S5AngleRowsForFinitePQSpineGeneratedOrderSource
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc) : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows
        (finitePQSpineGeneratedOrderFrameCoreLabelCertificate
          (payForCut := payForCut) (topologyArc := topologyArc)
          rows C hmin)
        (BaseInputs payForCut topologyArc
          (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
            (payForCut := payForCut) (topologyArc := topologyArc) rows)
          C hmin).turnBounds

/-- Bundle finite-PQ Figure 8 containment rows and Figure 9 middle-turn rows
into the generated label-certificate S5 package. -/
def s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_angleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H8 :
      Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows)
    (H9 :
      Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    S5AngleRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    { figure8CentralAngleLeSeparatedTurn := H8 C hmin
      figure9LeftAngleLeMiddleTurn := H9 C hmin }

/-- Project finite-PQ Figure 8 central-angle containment rows from generated
S5 angle rows. -/
def figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact (H C hmin).figure8CentralAngleLeSeparatedTurn

/-- The named positive Figure 8 S5 angle rows are exactly the central-angle
containment rows consumed by W32. -/
def figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource_of_centralAngleLeSeparatedTurnRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  H

/-- Project finite-PQ Figure 9 middle-turn upper-bound rows from generated S5
angle rows. -/
def figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact (H C hmin).figure9LeftAngleLeMiddleTurn

/-- Convert finite-PQ Figure 9 middle-turn upper-bound rows to the exact
left-angle containment rows consumed by W32 assembly. -/
def figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource_of_angleLeMiddleTurnRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    Figure9ContainmentConcrete.leftAngleContainmentRows_of_angleLeMiddleTurnRows
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.turn_nonnegative
      (H C hmin)

/-- Project finite-PQ Figure 9 left-angle containment rows from generated S5
angle rows by converting their middle-turn upper bounds. -/
def figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    Figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  figure9LeftAngleContainmentRowsForFinitePQSpineGeneratedOrderSource_of_angleLeMiddleTurnRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    (figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
      (payForCut := payForCut) (topologyArc := topologyArc) H)

/-! ### W11 actual-turn rows for finite-label S5 angle packages -/

/-- Row-wise identification between the finite-label turn bounds and the W11
raw-turn function selected by a long arc. -/
abbrev ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.turn =
        R.rawTurn C hmin (longArc C hmin)

/-- Figure 8 actual-turn interval-subwindow rows for generated finite labels. -/
abbrev Figure8CentralAngleActualTurnIccSubwindowRowsForFinitePQSpineGeneratedOrderSource
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnIccSubwindowRows
        (LocalGood
          (BaseInputs payForCut topologyArc
            (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) rows)
            C hmin).localLabels)
        (R.rawTurn C hmin (longArc C hmin))

/-- Figure 8 actual-turn indexed-subwindow rows for generated finite labels. -/
abbrev Figure8CentralAngleActualTurnIndexedSubwindowRowsForFinitePQSpineGeneratedOrderSource
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.Figure8CentralAngleTurnIndexedSubwindowRows
        (LocalGood
          (BaseInputs payForCut topologyArc
            (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
              (payForCut := payForCut) (topologyArc := topologyArc) rows)
            C hmin).localLabels)
        (R.rawTurn C hmin (longArc C hmin))

/-- Figure 9 actual-turn pointwise cosine comparisons for generated finite
labels. -/
abbrev Figure9AdjacentLeftActualTurnCosineComparisonRowsForFinitePQSpineGeneratedOrderSource
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
        1 <= i -> i + 1 <= 10 ->
        Not
          (LocalGood
            (BaseInputs payForCut topologyArc
              (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
                (payForCut := payForCut) (topologyArc := topologyArc) rows)
              C hmin).localLabels i) ->
        Not
          (LocalGood
            (BaseInputs payForCut topologyArc
              (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
                (payForCut := payForCut) (topologyArc := topologyArc) rows)
              C hmin).localLabels (i + 1)) ->
        AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
          Real.cos (R.rawTurn C hmin (longArc C hmin) (i + 1)) <=
            TriangleAngleFacts.dotAt p qi s

/-- Figure 9 actual-turn pointwise chord comparisons for generated finite
labels. -/
abbrev Figure9AdjacentLeftActualTurnChordComparisonRowsForFinitePQSpineGeneratedOrderSource
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    (R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S)
    (rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc)
    (longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      forall {i : Nat} {p qi qj s r : AngleBridgeFacts.Point},
        1 <= i -> i + 1 <= 10 ->
        Not
          (LocalGood
            (BaseInputs payForCut topologyArc
              (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
                (payForCut := payForCut) (topologyArc := topologyArc) rows)
              C hmin).localLabels i) ->
        Not
          (LocalGood
            (BaseInputs payForCut topologyArc
              (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
                (payForCut := payForCut) (topologyArc := topologyArc) rows)
              C hmin).localLabels (i + 1)) ->
        AngleBridgeFacts.Figure9DistanceData p qi qj s r ->
          TriangleAngleFacts.sqDist p s <=
            2 - 2 * Real.cos
              (R.rawTurn C hmin (longArc C hmin) (i + 1))

/-- W11 actual-turn Figure 8 interval rows give the positive finite-label
central-angle row once the generated turn bounds are identified with the W11
raw turn. -/
def figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H :
      Figure8CentralAngleActualTurnIccSubwindowRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc) :
    Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_turnSubwindowIccRows
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.turn_nonnegative
      (by
        intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
        simpa [hturn C hmin] using
          H C hmin hi hsep hj hbad_i hbad_j Hdist)

/-- W11 actual-turn Figure 8 indexed rows give the positive finite-label
central-angle row once the generated turn bounds are identified with the W11
raw turn. -/
def figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIndexedRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H :
      Figure8CentralAngleActualTurnIndexedSubwindowRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc) :
    Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    Figure8EuclideanFactsConcrete.Figure8ExplicitEuclideanFacts.centralAngleContainmentRows_of_indexedSubwindowRows
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.turn_nonnegative
      (by
        intro i j p qi qj s r hi hsep hj hbad_i hbad_j Hdist
        simpa [hturn C hmin] using
          H C hmin hi hsep hj hbad_i hbad_j Hdist)

/-- W11 actual-turn Figure 9 cosine comparisons give the finite-label
middle-turn upper-bound rows. -/
def figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnCosineComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H :
      Figure9AdjacentLeftActualTurnCosineComparisonRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc) :
    Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    Figure9EuclideanFactsConcrete.angleLeMiddleTurnRows_of_totalTurn_and_cosineComparisons
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.turn_nonnegative
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.total_turn_lt_pi_div_three
      (by
        intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
        simpa [hturn C hmin] using
          H C hmin hi hi_next hbad_i hbad_next Hdist)

/-- W11 actual-turn Figure 9 chord comparisons give the finite-label
middle-turn upper-bound rows. -/
def figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnChordComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H :
      Figure9AdjacentLeftActualTurnChordComparisonRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc) :
    Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    Figure9EuclideanFactsConcrete.angleLeMiddleTurnRows_of_totalTurn_and_chordComparisons
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.turn_nonnegative
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds.total_turn_lt_pi_div_three
      (by
        intro i p qi qj s r hi hi_next hbad_i hbad_next Hdist
        simpa [hturn C hmin] using
          H C hmin hi hi_next hbad_i hbad_next Hdist)

/-- Compact finite-label S5 angle package from W11 actual-turn Figure 8
interval rows and already-proved Figure 9 middle-turn rows. -/
def s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRowsAndAngleLeMiddleTurnRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H8 :
      Figure8CentralAngleActualTurnIccSubwindowRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H9 :
      Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    S5AngleRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_angleRows
    (figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      hturn H8)
    H9

/-- Compact finite-label S5 angle package from W11 actual-turn Figure 8
indexed rows and already-proved Figure 9 middle-turn rows. -/
def s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIndexedRowsAndAngleLeMiddleTurnRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H8 :
      Figure8CentralAngleActualTurnIndexedSubwindowRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H9 :
      Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    S5AngleRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_angleRows
    (figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIndexedRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      hturn H8)
    H9

/-- W11 actual-turn Figure 8 interval rows plus actual-turn Figure 9 cosine
comparisons produce the compact finite-label S5 angle package. -/
def s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRowsAndCosineComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H8 :
      Figure8CentralAngleActualTurnIccSubwindowRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H9 :
      Figure9AdjacentLeftActualTurnCosineComparisonRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc) :
    S5AngleRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRowsAndAngleLeMiddleTurnRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    hturn H8
    (figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnCosineComparisonRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      hturn H9)

/-- W11 actual-turn Figure 8 interval rows plus actual-turn Figure 9 chord
comparisons produce the compact finite-label S5 angle package. -/
def s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRowsAndChordComparisonRows
    {S :
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.SkeletonFamily.{u}}
    {R : MinimalBoundaryTopologyBoundaryTurnAngleRows.{u} S}
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    {longArc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices}
    (hturn :
      ActualTurnEqRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H8 :
      Figure8CentralAngleActualTurnIccSubwindowRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc)
    (H9 :
      Figure9AdjacentLeftActualTurnChordComparisonRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc)
        R rows longArc) :
    S5AngleRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnIccRowsAndAngleLeMiddleTurnRows
    (payForCut := payForCut) (topologyArc := topologyArc)
    hturn H8
    (figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_actualTurnChordComparisonRows
      (payForCut := payForCut) (topologyArc := topologyArc)
      hturn H9)

/-- Direct finite-PQ local-honest W32 rows from the generated finite-label S5
package.  The label certificate contributes the Figure 8/Figure 9 distance
witnesses; the S5 package contributes Figure 8 containment and Figure 9
middle-turn rows. -/
def localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows := by
  intro n C hmin
  exact
    localHonestEuclideanInequalitySourceFields_of_labelCertificateS5AngleRows
      (finitePQSpineGeneratedOrderFrameCoreLabelCertificate
        (payForCut := payForCut) (topologyArc := topologyArc)
        rows C hmin)
      (BaseInputs payForCut topologyArc
        (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
          (payForCut := payForCut) (topologyArc := topologyArc) rows)
        C hmin).turnBounds
      (H C hmin)

/-- Direct finite-PQ local-honest W32 rows from Figure 8 containment and
Figure 9 `angle <= middle turn` rows. -/
def localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_angleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H8 :
      Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows)
    (H9 :
      Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
      (payForCut := payForCut) (topologyArc := topologyArc) rows :=
  localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
    (s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_angleRows H8 H9)

/-- Generated finite-label S5 rows provide the honest Euclidean source
components consumed by the W32 final assembly surface. -/
theorem honestEuclideanSourceComponentsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H :
      S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc
      (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :=
  honestEuclideanInequalitySourceComponents_of_localHonestEuclideanInequalitySourceFieldsFamily
    (localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_s5AngleRows
      H)

/-- Figure 8 containment plus Figure 9 middle-turn rows provide the honest
Euclidean source components consumed by the W32 final assembly surface. -/
theorem honestEuclideanSourceComponentsForFinitePQSpineGeneratedOrderSource_of_angleRows
    {rows :
      FrameCyclicOrderAssemblyW32.FinitePQSpineGeneratedOrderRows.{u}
        payForCut topologyArc}
    (H8 :
      Figure8CentralAngleContainmentRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows)
    (H9 :
      Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc
      (Lemma8ConcreteOfFinitePQSpineGeneratedOrderRows
        (payForCut := payForCut) (topologyArc := topologyArc) rows) :=
  honestEuclideanInequalitySourceComponents_of_localHonestEuclideanInequalitySourceFieldsFamily
    (localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_angleRows
      H8 H9)

/-- Build the concrete local window-containment row for the Lemma 8 base
generated by a selected frame/cyclic source from the actual Figure 8 separated
and Figure 9 adjacent-left containment interfaces. -/
def localWindowContainmentRowForFrameCyclicSource_of_containmentInterfaces
    {P :
      FrameCyclicSourcePackage.{u}
        payForCut topologyArc}
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (figure8 :
      AngleContainmentInterface.Figure8SeparatedContainmentInterface
        (LocalGood
          (BaseInputs payForCut topologyArc
            (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
        (BaseInputs payForCut topologyArc
          (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds.turn)
    (figure9_left :
      AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
        (LocalGood
          (BaseInputs payForCut topologyArc
            (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
        (BaseInputs payForCut topologyArc
          (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds.turn) :
    M8WindowContainmentConcrete.M8LocalWindowContainmentFields
      (BaseInputs payForCut topologyArc
        (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels
      (BaseInputs payForCut topologyArc
        (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds :=
  M8WindowContainmentConcrete.M8LocalWindowContainmentFields.ofContainmentInterfaces
    (localLabels :=
      (BaseInputs payForCut topologyArc
        (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
    (turnBounds :=
      (BaseInputs payForCut topologyArc
        (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds)
    figure8 figure9_left

/-- Row-wise Figure 8 separated and Figure 9 adjacent-left containment
interfaces build the local window-containment family for the selected
frame/cyclic source. -/
def localWindowContainmentFieldsForFrameCyclicSource_of_containmentInterfaces
    {P :
      FrameCyclicSourcePackage.{u}
        payForCut topologyArc}
    (figure8 :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          AngleContainmentInterface.Figure8SeparatedContainmentInterface
            (LocalGood
              (BaseInputs payForCut topologyArc
                (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
            (BaseInputs payForCut topologyArc
              (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds.turn)
    (figure9_left :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
            (LocalGood
              (BaseInputs payForCut topologyArc
                (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
            (BaseInputs payForCut topologyArc
              (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds.turn) :
    FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
      payForCut topologyArc (lemma8ConcreteOfFrameCyclicSource P) :=
  fun {n : Nat} (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) =>
    localWindowContainmentRowForFrameCyclicSource_of_containmentInterfaces
      (P := P) C hmin (figure8 C hmin) (figure9_left C hmin)

/-- The actual Figure 8 separated and Figure 9 adjacent-left containment
interfaces for the generated selected frame rows feed the compact W32 honest
Euclidean source-component surface. -/
theorem honestEuclideanSourceComponentsForFrameCyclicSource_of_containmentInterfaces
    {P :
      FrameCyclicSourcePackage.{u}
        payForCut topologyArc}
    (figure8 :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          AngleContainmentInterface.Figure8SeparatedContainmentInterface
            (LocalGood
              (BaseInputs payForCut topologyArc
                (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
            (BaseInputs payForCut topologyArc
              (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds.turn)
    (figure9_left :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
            (LocalGood
              (BaseInputs payForCut topologyArc
                (lemma8ConcreteOfFrameCyclicSource P) C hmin).localLabels)
            (BaseInputs payForCut topologyArc
              (lemma8ConcreteOfFrameCyclicSource P) C hmin).turnBounds.turn) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc
      (lemma8ConcreteOfFrameCyclicSource P) :=
  honestEuclideanInequalitySourceComponents_of_localHonestEuclideanInequalitySourceFieldsFamily
    (localHonestEuclideanInequalitySourceFieldsFamily_of_localWindowContainmentFieldsFamily
      (localWindowContainmentFieldsForFrameCyclicSource_of_containmentInterfaces
        figure8 figure9_left))

/-- W32 assembly rows produce W31 exact Figure inequality rows. -/
theorem exactFigureInequalityRowsBlocker_of_exactFigureRowsAssemblyBlocker
    (h : ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsBlocker.{u}
      payForCut topologyArc lemma8 := by
  cases h with
  | intro F =>
      exact Nonempty.intro F.toExactFigureInequalityRowsFamily

/-- W31 exact Figure row blockers inhabit W32 assembly rows. -/
theorem exactFigureRowsAssemblyBlocker_of_exactFigureInequalityRowsBlocker
    (h : ExactFigureInequalityRowsBlocker.{u}
      payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8 := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (exactFigureRowsAssemblyFamily_of_exactFigureInequalityRowsFamily
          F)

/-- W32 assembly rows are equivalent to W31 exact Figure row blockers. -/
theorem exactFigureRowsAssemblyBlocker_iff_exactFigureInequalityRowsBlocker :
    ExactFigureRowsAssemblyBlocker.{u}
        payForCut topologyArc lemma8 <->
      ExactFigureInequalityRowsBlocker.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    exact exactFigureInequalityRowsBlocker_of_exactFigureRowsAssemblyBlocker
  case mpr =>
    exact exactFigureRowsAssemblyBlocker_of_exactFigureInequalityRowsBlocker

/-- Honest Euclidean source components produce W31 exact Figure inequality
rows. -/
theorem exactFigureInequalityRowsBlocker_of_components
    (h : HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8) :
    ExactFigureInequalityRowsBlocker.{u}
      payForCut topologyArc lemma8 := by
  cases h with
  | intro W H =>
      exact
        exactFigureInequalityRowsBlocker_of_selectedFigureWitnessFieldsAndEuclideanSources
          W H

/-- W31 exact Figure row blockers are equivalent to the W32 honest Euclidean
source components. -/
theorem exactFigureInequalityRowsBlocker_iff_components :
    ExactFigureInequalityRowsBlocker.{u}
        payForCut topologyArc lemma8 <->
      HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    intro h
    exact
      components_of_exactFigureInequalityRowComponents
        (FigureInequalityRowsW31.exactFigureInequalityRowsBlocker_iff_components.1
          h)
  case mpr =>
    exact exactFigureInequalityRowsBlocker_of_components

/-- W32 assembly rows discharge the W28 exact E22/E23 source blocker. -/
theorem exactE22E23SourceBlocker_of_exactFigureRowsAssemblyBlocker
    (h : ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
      payForCut topologyArc lemma8 := by
  cases h with
  | intro F =>
      exact F.exactE22E23SourceBlocker

/-- Honest Euclidean source components discharge the W28 exact E22/E23 source
blocker. -/
theorem exactE22E23SourceBlocker_of_components
    (h : HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
      payForCut topologyArc lemma8 := by
  cases h with
  | intro W H =>
      exact
        (exactFigureInequalityRowsFamily_of_selectedFigureWitnessFieldsAndEuclideanSources
          W H).exactE22E23SourceBlocker

/-- The W28 exact E22/E23 source blocker provides the W32 honest Euclidean
source components. -/
theorem components_of_exactE22E23SourceBlocker
    (h :
      FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8) :
    HonestEuclideanInequalitySourceComponents.{u}
      payForCut topologyArc lemma8 :=
  components_of_exactFigureInequalityRowComponents
    (FigureInequalityRowsW31.exactE22E23SourceBlocker_iff_components.1 h)

/-- The W28 exact E22/E23 source blocker builds W32 exact Figure assembly rows. -/
theorem exactFigureRowsAssemblyBlocker_of_exactE22E23SourceBlocker
    (h :
      FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8) :
    ExactFigureRowsAssemblyBlocker.{u}
      payForCut topologyArc lemma8 :=
  exactFigureRowsAssemblyBlocker_of_components
    (components_of_exactE22E23SourceBlocker h)

/-- W32 exact Figure assembly rows are equivalent to the W28 exact E22/E23
source blocker. -/
theorem exactFigureRowsAssemblyBlocker_iff_exactE22E23SourceBlocker :
    ExactFigureRowsAssemblyBlocker.{u}
        payForCut topologyArc lemma8 <->
      FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    exact exactE22E23SourceBlocker_of_exactFigureRowsAssemblyBlocker
  case mpr =>
    exact exactFigureRowsAssemblyBlocker_of_exactE22E23SourceBlocker

/-- The exact E22/E23 source blocker is equivalent to the W32 honest
Euclidean source components. -/
theorem exactE22E23SourceBlocker_iff_components :
    FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 <->
      HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8 := by
  constructor
  case mp =>
    exact components_of_exactE22E23SourceBlocker
  case mpr =>
    exact exactE22E23SourceBlocker_of_components

/-- Concrete local window-containment field families discharge the W28 exact
E22/E23 source blocker through the W32 assembly package. -/
theorem exactE22E23SourceBlocker_of_localWindowContainmentFieldsFamily
    (W :
      FigureExactAngleCertificateInhabitationW22.LocalWindowContainmentFieldsFamily.{u}
        payForCut topologyArc lemma8) :
    FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
      payForCut topologyArc lemma8 :=
  (exactFigureRowsAssemblyFamily_of_localWindowContainmentFieldsFamily
    W).exactE22E23SourceBlocker

/-- If the W28 exact E22/E23 source blocker is missing, then the stronger W32
honest Euclidean source components are missing as well. -/
theorem not_components_of_not_exactE22E23SourceBlocker
    (hbad : Not
      (FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8)) :
    Not
      (HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8) := by
  intro h
  exact hbad (exactE22E23SourceBlocker_of_components h)

/-- If the W28 exact E22/E23 source blocker is missing, then W32 assembly rows
are missing as well. -/
theorem not_exactFigureRowsAssemblyBlocker_of_not_exactE22E23SourceBlocker
    (hbad : Not
      (FigureInequalityRowsW31.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8)) :
    Not
      (ExactFigureRowsAssemblyBlocker.{u}
        payForCut topologyArc lemma8) := by
  intro h
  exact hbad
    (exactE22E23SourceBlocker_of_exactFigureRowsAssemblyBlocker h)

end ExactFigureRowsAssemblyW32
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW32FigureEuclideanInequalitySourceFields :=
  Swanepoel.ExactFigureRowsAssemblyW32.FigureEuclideanInequalitySourceFields

abbrev SwanepoelW32LocalHonestEuclideanInequalitySourceFields
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : Swanepoel.M8ConstructionInterface.M8LocalLabels C)
    (turnBounds : Swanepoel.M8ConstructionInterface.M8TurnBounds) :=
  Swanepoel.ExactFigureRowsAssemblyW32.LocalHonestEuclideanInequalitySourceFields
    localLabels turnBounds

abbrev SwanepoelW32ExactFigureRowsAssemblyFamily :=
  Swanepoel.ExactFigureRowsAssemblyW32.ExactFigureRowsAssemblyFamily

abbrev SwanepoelW32ExactFigureRowsAssemblyBlocker :=
  Swanepoel.ExactFigureRowsAssemblyW32.ExactFigureRowsAssemblyBlocker

abbrev SwanepoelW32HonestEuclideanInequalitySourceComponents :=
  Swanepoel.ExactFigureRowsAssemblyW32.HonestEuclideanInequalitySourceComponents

theorem swanepoelW32_exactFigureInequalityRowsBlocker_of_components
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      SwanepoelW32HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8) :
    Swanepoel.FigureInequalityRowsW31.ExactFigureInequalityRowsBlocker.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.ExactFigureRowsAssemblyW32.exactFigureInequalityRowsBlocker_of_components
    h

theorem swanepoelW32_exactE22E23SourceBlocker_of_components
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (h :
      SwanepoelW32HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8) :
    Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8 :=
  Swanepoel.ExactFigureRowsAssemblyW32.exactE22E23SourceBlocker_of_components
    h

theorem swanepoelW32_missing_components_of_missing_exactE22E23SourceBlocker
    {payForCut :
      Swanepoel.FigureAngleSourceInhabitationW21.PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.FigureAngleSourceInhabitationW21.TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.FigureAngleSourceInhabitationW21.Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (hbad : Not
      (Swanepoel.FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{u}
        payForCut topologyArc lemma8)) :
    Not
      (SwanepoelW32HonestEuclideanInequalitySourceComponents.{u}
        payForCut topologyArc lemma8) :=
  Swanepoel.ExactFigureRowsAssemblyW32.not_components_of_not_exactE22E23SourceBlocker
    hbad

end Verified
end ErdosProblems1066

end
