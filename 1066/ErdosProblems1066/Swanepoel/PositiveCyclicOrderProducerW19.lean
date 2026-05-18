import ErdosProblems1066.Swanepoel.BoundaryWalkBridge
import ErdosProblems1066.Swanepoel.Lemma8GeometryFieldsW18

set_option autoImplicit false

/-!
# W19 positive cyclic-order producer surface for Lemma 8

`Lemma8GeometryFieldsW18` reduces the Lemma 8 geometry row to finite local
degree/frame data plus one remaining rotation assertion.  This file isolates
that last assertion as a minimal certificate and provides adapters back into
the W18/W17/W16 construction surfaces.

No geometric existence theorem is introduced here.  The certificate below is
the precise remaining datum: a six-argument positive cyclic-order predicate,
checked at the generated `s_i, r_i, q_{i-1}, p_i, p_{i+1}, q_{i+1}` tuple.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PositiveCyclicOrderProducerW19

open BoundaryArcExtractionProofW15
open BoundaryArcFiniteWalkConstructionW16
open CutVertexInterface
open Lemma8ExistenceConcrete
open Lemma8FiniteDataConstructionW17
open Lemma8GeometryFieldsW18
open Lemma8LocalLabelsW16
open Lemma8NeighborExtractionConcrete
open M8LabelsFromBoundaryInterface
open MinimalFailureClosureW13
open MinimalGraphFacts
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## The minimal remaining certificate -/

/--
The exact positive cyclic-order datum still missing after the W18 local
geometry reduction.

The record is parameterized by the already-generated non-cyclic neighbor data,
so it cannot silently change the selected `r_i` and `s_i` labels.
-/
structure M8PositiveCyclicOrderCertificate
    (D : M8ExtraNeighborData S) where
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i (D.s i) (D.r i)
        (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8PositiveCyclicOrderCertificate

variable {D : M8ExtraNeighborData S}
variable (O : M8PositiveCyclicOrderCertificate D)

/-- Projection of the stored positive cyclic-order proof. -/
theorem positiveCyclicOrder_holds (i : M8ExtraIndex) :
    O.positiveCyclicOrderAt i (D.s i) (D.r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  O.positiveCyclicOrder i

/-- Convert the minimal W19 certificate to the neighbor-extraction cyclic-order
record consumed by `M8ExtraNeighborData.toLemma8Combinatorics`. -/
def toNeighborCyclicOrder :
    M8ExtraNeighborData.CyclicOrder D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

/-- Recover the W19 certificate from the existing neighbor-extraction record. -/
def ofNeighborCyclicOrder
    (O : M8ExtraNeighborData.CyclicOrder D) :
    M8PositiveCyclicOrderCertificate D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

@[simp]
theorem toNeighborCyclicOrder_positiveCyclicOrderAt :
    O.toNeighborCyclicOrder.positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

@[simp]
theorem ofNeighborCyclicOrder_positiveCyclicOrderAt
    (O : M8ExtraNeighborData.CyclicOrder D) :
    (ofNeighborCyclicOrder O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

theorem toNeighborCyclicOrder_positiveCyclicOrder
    (i : M8ExtraIndex) :
    O.toNeighborCyclicOrder.positiveCyclicOrderAt i
      (D.s i) (D.r i) (S.prevQ i) (S.leftP i)
      (S.rightP i) (S.nextQ i) :=
  O.positiveCyclicOrder i

theorem ofNeighborCyclicOrder_positiveCyclicOrder
    (O : M8ExtraNeighborData.CyclicOrder D) (i : M8ExtraIndex) :
    (ofNeighborCyclicOrder O).positiveCyclicOrderAt i
      (D.s i) (D.r i) (S.prevQ i) (S.leftP i)
      (S.rightP i) (S.nextQ i) :=
  O.positiveCyclicOrder i

/-- The W19 certificate is equivalent to the cyclic-order record already used
by the lower neighbor-extraction layer. -/
theorem nonempty_iff_neighborCyclicOrder :
    Nonempty (M8PositiveCyclicOrderCertificate D) <->
      Nonempty (M8ExtraNeighborData.CyclicOrder D) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro O => exact Nonempty.intro O.toNeighborCyclicOrder
  case mpr =>
    intro h
    cases h with
    | intro O => exact Nonempty.intro (ofNeighborCyclicOrder O)

end M8PositiveCyclicOrderCertificate

/-! ## W18 geometry without the remaining order field -/

/-- The W18 local geometry sources before the positive cyclic-order field is
attached. -/
structure M8GeometryNonorderSources
    (S : M8BoundarySpine H) where
  frameCore : Lemma8ForbiddenDistinctConcrete.M8FourForbiddenFrameCore S
  extraNeighborCardTwo :
    forall i : M8ExtraIndex, (extraNeighborFinset S i).card = 2

namespace M8GeometryNonorderSources

variable (G : M8GeometryNonorderSources S)

/-- The generated center-degree-six field. -/
def centerDegreeSix :
    forall i : M8ExtraIndex, centerDegree S i = 6 :=
  centerDegreeSixOfFrameCoreAndExtraCardTwo
    (S := S) G.frameCore G.extraNeighborCardTwo

/-- The generated forbidden-frame field. -/
def forbiddenFrame :
    forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i :=
  forbiddenFrameOfFrameCore (S := S) G.frameCore

/-- The generated non-cyclic `r_i/s_i` neighbor data. -/
def extraNeighborData :
    M8ExtraNeighborData S :=
  extraNeighborDataOfFrameCoreAndExtraCardTwo
    (S := S) G.frameCore G.extraNeighborCardTwo

/-- The remaining positive cyclic-order certificate type for these generated
neighbors. -/
abbrev PositiveCyclicOrderCertificate : Type :=
  M8PositiveCyclicOrderCertificate G.extraNeighborData

/-- Attach a minimal W19 positive-order certificate and recover the full W18
geometry-field package. -/
def withPositiveCyclicOrder
    (O : G.PositiveCyclicOrderCertificate) :
    M8GeometryFieldSources S where
  frameCore := G.frameCore
  extraNeighborCardTwo := G.extraNeighborCardTwo
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

/-- Alias emphasizing the adapter role into W18. -/
def toGeometryFieldSources
    (O : G.PositiveCyclicOrderCertificate) :
    M8GeometryFieldSources S :=
  G.withPositiveCyclicOrder O

@[simp]
theorem withPositiveCyclicOrder_frameCore
    (O : G.PositiveCyclicOrderCertificate) :
    (G.withPositiveCyclicOrder O).frameCore = G.frameCore :=
  rfl

theorem withPositiveCyclicOrder_extraNeighborCardTwo
    (O : G.PositiveCyclicOrderCertificate) :
    (G.withPositiveCyclicOrder O).extraNeighborCardTwo =
      G.extraNeighborCardTwo :=
  rfl

@[simp]
theorem withPositiveCyclicOrder_positiveCyclicOrderAt
    (O : G.PositiveCyclicOrderCertificate) :
    (G.withPositiveCyclicOrder O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

@[simp]
theorem withPositiveCyclicOrder_extraNeighborData
    (O : G.PositiveCyclicOrderCertificate) :
    M8GeometryFieldSources.extraNeighborData
      (G.withPositiveCyclicOrder O) = G.extraNeighborData :=
  rfl

theorem withPositiveCyclicOrder_positiveCyclicOrder
    (O : G.PositiveCyclicOrderCertificate) (i : M8ExtraIndex) :
    (G.withPositiveCyclicOrder O).positiveCyclicOrderAt i
      ((M8GeometryFieldSources.extraNeighborData
        (G.withPositiveCyclicOrder O)).s i)
      ((M8GeometryFieldSources.extraNeighborData
        (G.withPositiveCyclicOrder O)).r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  O.positiveCyclicOrder i

/-- The W19 certificate closes the W18 package exactly up to the already
generated non-cyclic data. -/
def toMissingExistenceConditions
    (O : G.PositiveCyclicOrderCertificate) :
    Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions S :=
  (G.withPositiveCyclicOrder O).toMissingExistenceConditions

/-- The full Lemma 8 combinatorics package obtained from W18 non-order data
plus the W19 minimal order certificate. -/
def toLemma8Combinatorics
    (O : G.PositiveCyclicOrderCertificate) :
    M8Lemma8Combinatorics S :=
  (G.withPositiveCyclicOrder O).toLemma8Combinatorics

@[simp]
theorem toLemma8Combinatorics_r
    (O : G.PositiveCyclicOrderCertificate) (i : M8ExtraIndex) :
    (G.toLemma8Combinatorics O).r i = G.extraNeighborData.r i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s
    (O : G.PositiveCyclicOrderCertificate) (i : M8ExtraIndex) :
    (G.toLemma8Combinatorics O).s i = G.extraNeighborData.s i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_positiveCyclicOrderAt
    (O : G.PositiveCyclicOrderCertificate) :
    (G.toLemma8Combinatorics O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

theorem toLemma8Combinatorics_positiveCyclicOrder
    (O : G.PositiveCyclicOrderCertificate) (i : M8ExtraIndex) :
    (G.toLemma8Combinatorics O).positiveCyclicOrderAt i
      ((G.toLemma8Combinatorics O).s i)
      ((G.toLemma8Combinatorics O).r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  (G.toLemma8Combinatorics O).positiveCyclicOrder_holds i

end M8GeometryNonorderSources

/-! ## Finite-walk adapters into W17 and W16 -/

variable {hmin : IsMinimalClearedFailure C}

/-- Finite-walk Lemma 8 sources before the remaining positive cyclic-order
certificate is attached. -/
structure FiniteWalkNonorderSources
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  finiteWalk :
    BoundaryArcFiniteWalkData arcBoundaryBudget.planarBoundary
  geometry :
    M8GeometryNonorderSources
      (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget finiteWalk.toBoundaryArcCertificate)

namespace FiniteWalkNonorderSources

variable (P : FiniteWalkNonorderSources.{u} C hmin)

/-- The boundary spine selected by the finite walk. -/
def spine :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        P.arcBoundaryBudget.planarBoundary.core
        (MinimalFailureClosureW13.cutVertexOfNoCut
          hmin P.noCutVertex).preconnectedNoCut hmin) :=
  MinimalFailureClosureW13.spineOfBoundaryArc hmin P.noCutVertex
    P.arcBoundaryBudget P.finiteWalk.toBoundaryArcCertificate

/-- The remaining W19 certificate type for the finite-walk row. -/
abbrev PositiveCyclicOrderCertificate : Type :=
  P.geometry.PositiveCyclicOrderCertificate

/-- Attach a W19 positive-order certificate and recover the W18 finite-walk
geometry source package. -/
def withPositiveCyclicOrder
    (O : P.PositiveCyclicOrderCertificate) :
    FiniteWalkGeometrySources.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  finiteWalk := P.finiteWalk
  geometry := P.geometry.withPositiveCyclicOrder O

/-- Adapter directly into the W17 finite-walk fields. -/
def toFiniteWalkLemma8Fields
    (O : P.PositiveCyclicOrderCertificate) :
    FiniteWalkLemma8Fields.{u} C hmin :=
  (P.withPositiveCyclicOrder O).toFiniteWalkLemma8Fields

/-- Adapter into the W16 pointwise finite-walk local-label inputs. -/
def toPointwiseFiniteWalkLocalLabelInputs
    (O : P.PositiveCyclicOrderCertificate) :
    PointwiseFiniteWalkLemma8LocalLabelInputs.{u} C hmin :=
  (P.withPositiveCyclicOrder O).toPointwiseFiniteWalkLocalLabelInputs

/-- The local labels produced once the minimal positive-order certificate is
supplied. -/
def localLabels
    (O : P.PositiveCyclicOrderCertificate) :
    M8ConstructionInterface.M8LocalLabels C :=
  (P.withPositiveCyclicOrder O).localLabels

@[simp]
theorem withPositiveCyclicOrder_finiteWalk
    (O : P.PositiveCyclicOrderCertificate) :
    (P.withPositiveCyclicOrder O).finiteWalk = P.finiteWalk :=
  rfl

@[simp]
theorem toFiniteWalkLemma8Fields_finiteWalk
    (O : P.PositiveCyclicOrderCertificate) :
    (P.toFiniteWalkLemma8Fields O).finiteWalk = P.finiteWalk :=
  rfl

@[simp]
theorem toFiniteWalkLemma8Fields_positiveCyclicOrderAt
    (O : P.PositiveCyclicOrderCertificate) :
    (P.toFiniteWalkLemma8Fields O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

@[simp]
theorem toPointwiseFiniteWalkLocalLabelInputs_finiteWalk
    (O : P.PositiveCyclicOrderCertificate) :
    (P.toPointwiseFiniteWalkLocalLabelInputs O).finiteWalk = P.finiteWalk :=
  rfl

theorem localLabels_extraNeighborWitness
    (O : P.PositiveCyclicOrderCertificate) (i : M8ExtraIndex) :
    (P.localLabels O).predicates.data.extraNeighborWitness i :=
  (P.withPositiveCyclicOrder O).localLabels_extraNeighborWitness i

/-- The finite boundary-walk cyclic successor checks remain available after
attaching the positive cyclic-order certificate. -/
theorem finiteWalk_cyclicOrder
    (O : P.PositiveCyclicOrderCertificate) (i : M8TriangleIndex) :
    (P.toFiniteWalkLemma8Fields O).finiteWalk.pIndex
        (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc
        P.arcBoundaryBudget.planarBoundary.core.outerCycle.length_pos
        ((P.toFiniteWalkLemma8Fields O).finiteWalk.pIndex
          (m8BoundaryIndexLeft i)) :=
  P.finiteWalk.cyclicOrder i

end FiniteWalkNonorderSources

/-! ## Triangle-run adapters -/

/-- Triangle-run Lemma 8 sources before the remaining positive cyclic-order
certificate is attached. -/
structure TriangleRunNonorderSources
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  triangleRun :
    BoundaryArcTriangleRun arcBoundaryBudget.planarBoundary
  geometry :
    M8GeometryNonorderSources
      (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
        arcBoundaryBudget
        triangleRun.toFiniteWalkData.toBoundaryArcCertificate)

namespace TriangleRunNonorderSources

variable (P : TriangleRunNonorderSources.{u} C hmin)

/-- The finite-walk non-order package induced by the triangle run. -/
def toFiniteWalkNonorderSources :
    FiniteWalkNonorderSources.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  finiteWalk := P.triangleRun.toFiniteWalkData
  geometry := P.geometry

/-- The remaining W19 certificate type for the triangle-run row. -/
abbrev PositiveCyclicOrderCertificate : Type :=
  P.geometry.PositiveCyclicOrderCertificate

/-- Attach a W19 positive-order certificate and recover the W18 triangle-run
geometry source package. -/
def withPositiveCyclicOrder
    (O : P.PositiveCyclicOrderCertificate) :
    TriangleRunGeometrySources.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  triangleRun := P.triangleRun
  geometry := P.geometry.withPositiveCyclicOrder O

/-- Adapter directly into the W17 triangle-run fields. -/
def toTriangleRunLemma8Fields
    (O : P.PositiveCyclicOrderCertificate) :
    TriangleRunLemma8Fields.{u} C hmin :=
  (P.withPositiveCyclicOrder O).toTriangleRunLemma8Fields

/-- Adapter into W17 finite-walk fields through the triangle run. -/
def toFiniteWalkLemma8Fields
    (O : P.PositiveCyclicOrderCertificate) :
    FiniteWalkLemma8Fields.{u} C hmin :=
  (P.withPositiveCyclicOrder O).toFiniteWalkLemma8Fields

/-- The local labels produced once the minimal positive-order certificate is
supplied. -/
def localLabels
    (O : P.PositiveCyclicOrderCertificate) :
    M8ConstructionInterface.M8LocalLabels C :=
  (P.withPositiveCyclicOrder O).localLabels

@[simp]
theorem toFiniteWalkNonorderSources_finiteWalk :
    P.toFiniteWalkNonorderSources.finiteWalk =
      P.triangleRun.toFiniteWalkData :=
  rfl

@[simp]
theorem withPositiveCyclicOrder_triangleRun
    (O : P.PositiveCyclicOrderCertificate) :
    (P.withPositiveCyclicOrder O).triangleRun = P.triangleRun :=
  rfl

@[simp]
theorem toTriangleRunLemma8Fields_triangleRun
    (O : P.PositiveCyclicOrderCertificate) :
    (P.toTriangleRunLemma8Fields O).triangleRun = P.triangleRun :=
  rfl

@[simp]
theorem toTriangleRunLemma8Fields_positiveCyclicOrderAt
    (O : P.PositiveCyclicOrderCertificate) :
    (P.toTriangleRunLemma8Fields O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

theorem localLabels_extraNeighborWitness
    (O : P.PositiveCyclicOrderCertificate) (i : M8ExtraIndex) :
    (P.localLabels O).predicates.data.extraNeighborWitness i :=
  (P.withPositiveCyclicOrder O).localLabels_extraNeighborWitness i

/-- The triangle-run cyclic successor checks are the finite-walk checks used by
the W17 adapter. -/
theorem triangleRun_cyclicOrder
    (O : P.PositiveCyclicOrderCertificate) (i : M8TriangleIndex) :
    (P.toTriangleRunLemma8Fields O).triangleRun.pIndex
        (m8BoundaryIndexRight i) =
      PlanarInterface.cyclicSucc
        P.arcBoundaryBudget.planarBoundary.core.outerCycle.length_pos
        ((P.toTriangleRunLemma8Fields O).triangleRun.pIndex
          (m8BoundaryIndexLeft i)) :=
  P.triangleRun.cyclicOrder i

end TriangleRunNonorderSources

end

end PositiveCyclicOrderProducerW19
end Swanepoel
end ErdosProblems1066
