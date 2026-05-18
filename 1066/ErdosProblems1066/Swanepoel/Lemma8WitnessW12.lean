import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete

set_option autoImplicit false

/-!
# W12 Lemma 8 witness extraction

This module packages the checked route from honest finite boundary/spine data
to the named Lemma 8 extra-neighbor witnesses `r_i, s_i`.

The inputs remain explicit: finite `p/q` spine labels, degree-six at the
central `q_i`, the four forbidden neighbors as an actual neighbor frame, and
the remaining cyclic-order assertion.  From these inputs, the file constructs
the non-cyclic witness data, the full Lemma 8 combinatorics package, and the
boundary-label package whose `r` and `s` labels are the extracted witnesses.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8WitnessW12

open BoundaryFaceCountingToM8
open BoundaryLabelCertificateAssembly
open BoundarySpineFiniteCertificate
open GraphBridge
open Lemma8ExistenceConcrete
open Lemma8NeighborExtractionConcrete
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}

/-! ## Witness extraction from a supplied boundary spine -/

/--
The explicit local inputs needed to extract the Lemma 8 witnesses from an
already constructed boundary spine.
-/
structure M8SpineLemma8WitnessData
    (S : M8BoundarySpine H) where
  centerDegreeSix : forall i : M8ExtraIndex, centerDegree S i = 6
  forbiddenFrame : forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).r i)
        (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8SpineLemma8WitnessData

variable {S : M8BoundarySpine H}
variable (W : M8SpineLemma8WitnessData S)

/-- The extracted non-cyclic `r_i, s_i` data. -/
def extraNeighborData : M8ExtraNeighborData S :=
  M8ExtraNeighborData.ofDegreeSixForbiddenFrame
    W.centerDegreeSix W.forbiddenFrame

/-- The remaining cyclic-order data for the extracted witnesses. -/
def cyclicOrder : M8ExtraNeighborData.CyclicOrder W.extraNeighborData where
  positiveCyclicOrderAt := W.positiveCyclicOrderAt
  positiveCyclicOrder := W.positiveCyclicOrder

/-- The full Lemma 8 combinatorics package assembled from the extracted
witnesses. -/
def toLemma8Combinatorics : M8Lemma8Combinatorics S :=
  W.extraNeighborData.toLemma8Combinatorics W.cyclicOrder

@[simp]
theorem toLemma8Combinatorics_r (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.r i = W.extraNeighborData.r i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.s i = W.extraNeighborData.s i :=
  rfl

/-- Projection of the extracted `r_i` adjacency. -/
theorem r_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (W.extraNeighborData.r i) :=
  W.extraNeighborData.r_neighbor i

/-- Projection of the extracted `s_i` adjacency. -/
theorem s_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (W.extraNeighborData.s i) :=
  W.extraNeighborData.s_neighbor i

/-- The extracted `r_i` is outside the four forbidden labels. -/
theorem r_not_forbidden (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (W.extraNeighborData.r i)) :=
  W.extraNeighborData.r_not_forbidden i

/-- The extracted `s_i` is outside the four forbidden labels. -/
theorem s_not_forbidden (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (W.extraNeighborData.s i)) :=
  W.extraNeighborData.s_not_forbidden i

/-- The extracted witnesses are distinct. -/
theorem r_ne_s (i : M8ExtraIndex) :
    Not (W.extraNeighborData.r i = W.extraNeighborData.s i) :=
  W.extraNeighborData.r_ne_s i

/-- Every non-forbidden neighbor of `q_i` is one of the extracted witnesses. -/
theorem named_of_extra_neighbor
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = W.extraNeighborData.r i \/ x = W.extraNeighborData.s i :=
  W.extraNeighborData.named_of_extra_neighbor hadj hnot

/-- The extracted witnesses satisfy the local predicate consumed downstream. -/
theorem extraNeighborWitness (i : M8ExtraIndex) :
    W.extraNeighborData.extraNeighborWitness i :=
  W.extraNeighborData.extraNeighborWitness_holds i

/-- The assembled Lemma 8 package carries the stored cyclic order. -/
theorem positiveCyclicOrder_holds (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.positiveCyclicOrderAt i
      (W.toLemma8Combinatorics.s i) (W.toLemma8Combinatorics.r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  W.toLemma8Combinatorics.positiveCyclicOrder_holds i

end M8SpineLemma8WitnessData

/-! ## Witness extraction from finite boundary/spine labels -/

variable {Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/--
Honest finite boundary/spine data with the explicit local Lemma 8 hypotheses
needed to extract `r_i, s_i`.
-/
structure M8FiniteBoundaryLemma8WitnessData
    (Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  finiteLabels : M8FinitePQSpineCertificate Dplanar
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree (finiteLabels.toM8BoundarySpine connectedNoCut hmin) i = 6
  forbiddenFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (finiteLabels.toM8BoundarySpine connectedNoCut hmin) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).r i)
        ((finiteLabels.toM8BoundarySpine connectedNoCut hmin).prevQ i)
        ((finiteLabels.toM8BoundarySpine connectedNoCut hmin).leftP i)
        ((finiteLabels.toM8BoundarySpine connectedNoCut hmin).rightP i)
        ((finiteLabels.toM8BoundarySpine connectedNoCut hmin).nextQ i)

namespace M8FiniteBoundaryLemma8WitnessData

variable (W :
  M8FiniteBoundaryLemma8WitnessData Dplanar connectedNoCut hmin)

/-- The boundary spine produced by the finite `p/q` certificate. -/
def spine : M8BoundarySpine (W.finiteLabels.context connectedNoCut hmin) :=
  W.finiteLabels.toM8BoundarySpine connectedNoCut hmin

/-- The finite-boundary witness data, viewed as witness data on its spine. -/
def toSpineWitnessData : M8SpineLemma8WitnessData W.spine where
  centerDegreeSix := W.centerDegreeSix
  forbiddenFrame := W.forbiddenFrame
  positiveCyclicOrderAt := W.positiveCyclicOrderAt
  positiveCyclicOrder := W.positiveCyclicOrder

/-- The extracted non-cyclic `r_i, s_i` data from the finite spine. -/
def extraNeighborData : M8ExtraNeighborData W.spine :=
  W.toSpineWitnessData.extraNeighborData

/-- The full Lemma 8 package built from the extracted witnesses. -/
def toLemma8Combinatorics : M8Lemma8Combinatorics W.spine :=
  W.toSpineWitnessData.toLemma8Combinatorics

/-- The assembled finite boundary-label certificate. -/
def toFiniteBoundaryLabelCertificate :
    M8FiniteBoundaryLabelCertificate Dplanar connectedNoCut hmin where
  finiteLabels := W.finiteLabels
  lemma8 := W.toLemma8Combinatorics

/-- The boundary route data containing the extracted Lemma 8 witnesses. -/
def toM8BoundaryRouteData : M8BoundaryRouteData.{u} C hmin :=
  W.toFiniteBoundaryLabelCertificate.toM8BoundaryRouteData

/-- The boundary-label package containing the extracted `r_i, s_i` labels. -/
def toBoundaryLabelPackage : M8BoundaryLabelPackage C :=
  W.toM8BoundaryRouteData.toBoundaryLabelPackage

@[simp]
theorem toLemma8Combinatorics_r (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.r i = W.extraNeighborData.r i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.s i = W.extraNeighborData.s i :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_lemma8 :
    W.toM8BoundaryRouteData.lemma8 = W.toLemma8Combinatorics :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8 :
    W.toBoundaryLabelPackage.lemma8 = W.toLemma8Combinatorics :=
  rfl

@[simp]
theorem boundaryLabels_r (i : M8ExtraIndex) :
    W.toBoundaryLabelPackage.labels.r i = W.extraNeighborData.r i :=
  rfl

@[simp]
theorem boundaryLabels_s (i : M8ExtraIndex) :
    W.toBoundaryLabelPackage.labels.s i = W.extraNeighborData.s i :=
  rfl

@[simp]
theorem localLabels_r (i : M8ExtraIndex) :
    W.toM8BoundaryRouteData.toM8LocalLabels.labels.r i =
      W.extraNeighborData.r i :=
  rfl

@[simp]
theorem localLabels_s (i : M8ExtraIndex) :
    W.toM8BoundaryRouteData.toM8LocalLabels.labels.s i =
      W.extraNeighborData.s i :=
  rfl

/-- Projection of the extracted `r_i` adjacency from finite boundary data. -/
theorem r_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (W.spine.centerQ i)
      (W.extraNeighborData.r i) :=
  W.toSpineWitnessData.r_neighbor i

/-- Projection of the extracted `s_i` adjacency from finite boundary data. -/
theorem s_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (W.spine.centerQ i)
      (W.extraNeighborData.s i) :=
  W.toSpineWitnessData.s_neighbor i

/-- The finite boundary-label package exposes the local extra-neighbor
predicate for the extracted witnesses. -/
theorem boundaryLabels_extraNeighborWitness (i : M8ExtraIndex) :
    W.toBoundaryLabelPackage.predicates.data.extraNeighborWitness i :=
  W.toBoundaryLabelPackage.extraNeighborWitness i

/-- Every non-forbidden neighbor of a finite-spine center is one of the
extracted labels in the boundary package. -/
theorem boundaryLabels_named_of_extra_neighbor
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (W.spine.centerQ i) x)
    (hnot : Not (W.spine.forbiddenExtraNeighbor i x)) :
    x = W.toBoundaryLabelPackage.labels.r i \/
      x = W.toBoundaryLabelPackage.labels.s i := by
  simpa using W.toSpineWitnessData.named_of_extra_neighbor hadj hnot

/-- The assembled finite boundary-label certificate preserves the extracted
`r_i` label. -/
theorem finiteBoundaryLabelCertificate_r (i : M8ExtraIndex) :
    W.toFiniteBoundaryLabelCertificate.toM8LocalLabels.labels.r i =
      W.extraNeighborData.r i :=
  rfl

/-- The assembled finite boundary-label certificate preserves the extracted
`s_i` label. -/
theorem finiteBoundaryLabelCertificate_s (i : M8ExtraIndex) :
    W.toFiniteBoundaryLabelCertificate.toM8LocalLabels.labels.s i =
      W.extraNeighborData.s i :=
  rfl

end M8FiniteBoundaryLemma8WitnessData

end

end Lemma8WitnessW12
end Swanepoel
end ErdosProblems1066
