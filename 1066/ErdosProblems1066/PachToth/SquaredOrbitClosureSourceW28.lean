import ErdosProblems1066.PachToth.ConcreteClosedOrbitConstructionW27
import ErdosProblems1066.PachToth.FreePlacementFieldsConcreteW27
import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26

set_option autoImplicit false

/-!
# W28 squared orbit-closure source rows

This file exposes a source-facing route into the W27 square-distance
closed-orbit gate.  The source rows are generated-chain data:

* a same/opposite transition package,
* a base block and an orientation word,
* algebraic cyclic closure of the generated orbit,
* square-distance global separation rows, and
* square-distance same-block unit rows.

The connector unit rows are then supplied by the transition package itself.
The final two blocker types name the exact missing row families: cyclic
displacement closure and global square-distance separation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SquaredOrbitClosureSourceW28

open Arithmetic
open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real

abbrev sqDist (p q : R2) : Real :=
  CrossBlockDistanceSqReduction.sqDist p q

abbrev TransitionObligations : Type :=
  Figure2Certificate.SameOppositeTransitionObligations

abbrev BlockOrientation : Type :=
  OrientationData.BlockOrientation

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW27.MinimalFieldsWithOrbitClosure

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementFieldsConcreteW27.MinimalFreePlacementFields

/-- Generated-orbit data before the closure and metric rows are attached. -/
structure GeneratedOrbitSkeleton where
  O : forall (k : Nat), 0 < k -> TransitionObligations
  base : forall (k : Nat), 0 < k -> LocalVertex -> R2
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> BlockOrientation

namespace GeneratedOrbitSkeleton

def point (G : GeneratedOrbitSkeleton)
    (k : Nat) (hk : 0 < k) : Fin k -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint
    (G.O k hk) hk (G.base k hk) (G.orientation k hk)

def step (G : GeneratedOrbitSkeleton)
    (k : Nat) (hk : 0 < k) : Fin k -> OrientationData.OrientedTransition :=
  GeneratedClosedChain.generatedStep (G.O k hk) (G.orientation k hk)

/-- The cyclic displacement rows: the generated orbit closes back to its base
block after one full trip around the finite word. -/
def DisplacementClosureRows (G : GeneratedOrbitSkeleton) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    PeriodInterface.GeneratedClosureEquation
      (G.O k hk) hk (G.base k hk) (G.orientation k hk)

/-- Global square-distance separation for all distinct generated vertices. -/
def SeparationRows (G : GeneratedOrbitSkeleton) : Prop :=
  forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) ->
      1 <= sqDist (G.point k hk i u) (G.point k hk j v)

/-- Square-distance same-block unit rows for the checked local edges. -/
def SameBlockUnitRows (G : GeneratedOrbitSkeleton) : Prop :=
  forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
    Ne u v ->
    adj u v = true ->
      sqDist (G.point k hk i u) (G.point k hk i v) = 1

/-- The source row package needed to enter the W27 squared closed-orbit gate. -/
structure CompletionRows (G : GeneratedOrbitSkeleton) where
  closure : G.DisplacementClosureRows
  separated_sq : G.SeparationRows
  same_block_edges_sq_unit : G.SameBlockUnitRows

end GeneratedOrbitSkeleton

/-- Source-facing generated orbit rows, separated from the final closed-orbit
target statement. -/
structure SquaredOrbitClosureSourceRows where
  skeleton : GeneratedOrbitSkeleton
  rows : skeleton.CompletionRows

namespace SquaredOrbitClosureSourceRows

def period (S : SquaredOrbitClosureSourceRows)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      (S.skeleton.O k hk) hk
      (S.skeleton.base k hk) (S.skeleton.orientation k hk) :=
  PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
    (S.skeleton.O k hk) hk
    (S.skeleton.base k hk) (S.skeleton.orientation k hk)
    (S.rows.closure k hk)

def successorEq (S : SquaredOrbitClosureSourceRows)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    S.skeleton.point k hk (cyclicSucc hk i) v =
      (S.skeleton.step k hk i).placeNext
        (S.skeleton.point k hk i) v := by
  simpa [GeneratedOrbitSkeleton.point, GeneratedOrbitSkeleton.step] using
    GeneratedClosedChain.generatedPoint_successor_compatible
      (S.skeleton.O k hk) hk
      (S.skeleton.base k hk) (S.skeleton.orientation k hk)
      (S.period k hk) i v

def crossConnectorSqUnit (S : SquaredOrbitClosureSourceRows)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u v : LocalVertex)
    (hconn : CrossBlock.NextConnector u v) :
    sqDist (S.skeleton.point k hk i u)
      (S.skeleton.point k hk (cyclicSucc hk i) v) = 1 := by
  have hsucc := S.successorEq k hk i v
  have hunit :
      _root_.eucDist (S.skeleton.point k hk i u)
        ((S.skeleton.step k hk i).placeNext
          (S.skeleton.point k hk i) v) = 1 := by
    simpa [GeneratedOrbitSkeleton.point, GeneratedOrbitSkeleton.step] using
      Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
        (S.skeleton.O k hk) (S.skeleton.orientation k hk i)
        (GeneratedClosedChain.generatedPoint
          (S.skeleton.O k hk) hk
          (S.skeleton.base k hk) (S.skeleton.orientation k hk) i)
        u v hconn
  have hunit' :
      _root_.eucDist (S.skeleton.point k hk i u)
        (S.skeleton.point k hk (cyclicSucc hk i) v) = 1 := by
    rw [hsucc]
    exact hunit
  exact
    ClosedPlacementConcreteConstructionW27.sqDist_eq_one_of_root_eucDist_eq_one
      hunit'

/-- Generated source rows construct the W27 square-distance orbit-closure
gate without using a final target statement as input. -/
def toSquaredMinimalFieldsWithOrbitClosure
    (S : SquaredOrbitClosureSourceRows) :
    SquaredMinimalFieldsWithOrbitClosure where
  point := S.skeleton.point
  step := S.skeleton.step
  successor_eq := S.successorEq
  separated_sq := S.rows.separated_sq
  same_block_edges_sq_unit := S.rows.same_block_edges_sq_unit
  cross_connector_edges_sq_unit := S.crossConnectorSqUnit

def toMinimalFieldsWithOrbitClosure
    (S : SquaredOrbitClosureSourceRows) :
    MinimalFieldsWithOrbitClosure :=
  ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure.toMinimalFieldsWithOrbitClosure
    S.toSquaredMinimalFieldsWithOrbitClosure

def toConcreteClosedOrbitFamily
    (S : SquaredOrbitClosureSourceRows) :
    ConcreteClosedOrbitFamily :=
  ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure.toConcreteClosedOrbitFamily
    S.toSquaredMinimalFieldsWithOrbitClosure

@[simp]
theorem toSquaredMinimalFieldsWithOrbitClosure_point
    (S : SquaredOrbitClosureSourceRows)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    S.toSquaredMinimalFieldsWithOrbitClosure.point k hk i v =
      S.skeleton.point k hk i v :=
  rfl

@[simp]
theorem toConcreteClosedOrbitFamily_point
    (S : SquaredOrbitClosureSourceRows)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toConcreteClosedOrbitFamily.data k hk).point i v =
      S.skeleton.point k hk i v :=
  calc
    (S.toConcreteClosedOrbitFamily.data k hk).point i v =
        S.toSquaredMinimalFieldsWithOrbitClosure.point k hk i v :=
      ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure.toConcreteClosedOrbitFamily_point
        S.toSquaredMinimalFieldsWithOrbitClosure k hk i v
    _ = S.skeleton.point k hk i v := rfl

end SquaredOrbitClosureSourceRows

theorem nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows :
    Nonempty SquaredOrbitClosureSourceRows ->
      Nonempty SquaredMinimalFieldsWithOrbitClosure := by
  intro h
  cases h with
  | intro S =>
      exact Nonempty.intro S.toSquaredMinimalFieldsWithOrbitClosure

theorem nonempty_concreteClosedOrbitFamily_of_sourceRows :
    Nonempty SquaredOrbitClosureSourceRows ->
      Nonempty ConcreteClosedOrbitFamily := by
  intro h
  exact
    ClosedPlacementConcreteConstructionW27.nonempty_concreteClosedOrbitFamily_iff_squaredMinimalFieldsWithOrbitClosure
      |>.2 (nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows h)

theorem nonempty_minimalFreePlacementFields_of_sourceRows :
    Nonempty SquaredOrbitClosureSourceRows ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  exact
    FreePlacementFieldsConcreteW27.nonempty_minimalFreePlacementFields_of_concreteClosedOrbitFamily
      (nonempty_concreteClosedOrbitFamily_of_sourceRows h)

/-- Missing cyclic displacement-closure rows block this generated source
route before it reaches the W27 closed-orbit gate. -/
structure MissingDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) where
  no_rows : Not G.DisplacementClosureRows

/-- Missing global square-distance separation rows block this generated
source route before it reaches the W27 closed-orbit gate. -/
structure MissingSeparationRows
    (G : GeneratedOrbitSkeleton) where
  no_rows : Not G.SeparationRows

namespace MissingDisplacementClosureRows

theorem no_completionRows
    {G : GeneratedOrbitSkeleton}
    (B : MissingDisplacementClosureRows G) :
    Not (Nonempty G.CompletionRows) := by
  intro h
  cases h with
  | intro R =>
      exact B.no_rows R.closure

end MissingDisplacementClosureRows

namespace MissingSeparationRows

theorem no_completionRows
    {G : GeneratedOrbitSkeleton}
    (B : MissingSeparationRows G) :
    Not (Nonempty G.CompletionRows) := by
  intro h
  cases h with
  | intro R =>
      exact B.no_rows R.separated_sq

end MissingSeparationRows

/-- Eventual role-hinged rows in squared-distance form.  These rows feed the
large explicit closed-placement bridge; they are still an eventual route and
do not by themselves provide the all-positive W27 closed-orbit family. -/
structure EventualRoleHingedSquaredRows (K0 : Nat) where
  transitions : LargeClosedPlacementW12.RoleHingeTransitions
  orientation :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Fin k -> BlockOrientation
  closure :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (orientation k hK hk)
  separated_sq :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= sqDist
          (GeneratedClosedChain.generatedPoint
            transitions.toFigure2TransitionObligations hk
            BaseTransitionRealization.exactBase
            (orientation k hK hk) i u)
          (GeneratedClosedChain.generatedPoint
            transitions.toFigure2TransitionObligations hk
            BaseTransitionRealization.exactBase
            (orientation k hK hk) j v)

namespace EventualRoleHingedSquaredRows

def separated
    {K0 : Nat} (E : EventualRoleHingedSquaredRows K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      E.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (E.orientation k hK hk) := by
  intro i u j v hne
  exact
    CrossBlockDistanceSqReduction.one_le_root_eucDist_of_one_le_sqDist
      (E.separated_sq k hK hk i u j v hne)

def toLargeExplicitClosedPlacementCertificates
    {K0 : Nat} (E : EventualRoleHingedSquaredRows K0) :
    LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0 :=
  LargeClosedPlacementW12.largeExplicitClosedPlacementCertificatesOfRoleHingedClosure
    K0 E.transitions E.orientation E.closure E.separated

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (E : EventualRoleHingedSquaredRows K0) :
    targetUpperConstructionFiveSixteenEventually :=
  E.toLargeExplicitClosedPlacementCertificates
    |>.targetUpperConstructionFiveSixteenEventually

end EventualRoleHingedSquaredRows

end

end SquaredOrbitClosureSourceW28
end PachToth

namespace Verified

abbrev PachTothW28SquaredOrbitClosureSourceRows : Type :=
  PachToth.SquaredOrbitClosureSourceW28.SquaredOrbitClosureSourceRows

theorem pachtoth_w28_squaredMinimalFieldsWithOrbitClosure_of_sourceRows :
    Nonempty PachTothW28SquaredOrbitClosureSourceRows ->
      Nonempty
        PachToth.ClosedPlacementConcreteConstructionW27.SquaredMinimalFieldsWithOrbitClosure :=
  PachToth.SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows

theorem pachtoth_w28_concreteClosedOrbitFamily_of_sourceRows :
    Nonempty PachTothW28SquaredOrbitClosureSourceRows ->
      Nonempty
        PachToth.ClosedPlacementConcreteConstructionW27.ConcreteClosedOrbitFamily :=
  PachToth.SquaredOrbitClosureSourceW28.nonempty_concreteClosedOrbitFamily_of_sourceRows

end Verified
end ErdosProblems1066
