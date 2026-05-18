import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete

set_option autoImplicit false

/-!
# Concrete cyclic-order layer for Lemma 8

`Lemma8NeighborExtractionConcrete` separates the named extra neighbors
`r_i, s_i` from the cyclic-order assertion in the paper's Lemma 8 route.  This
file isolates that remaining assertion in a minimal record and proves the
bookkeeping needed to assemble the downstream `M8Lemma8Combinatorics` package.

No rotation system, angle comparison, or planar geometry is hidden here.  The
only order input is the explicit proposition

`positiveCyclicOrderAt i (s_i) (r_i) (q_{i-1}) (p_i) (p_{i+1}) (q_{i+1})`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8CyclicOrderConcrete

open BoundaryFaceCountingToM8
open GraphBridge
open Lemma8NeighborExtractionConcrete
open Lemma8CombinatoricsConcrete
open LocalConfigurations
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Minimal cyclic-order input -/

/--
The precise cyclic-order assumption still needed after the concrete
extra-neighbor extraction.

The predicate is intentionally abstract: later geometric files may realize it
using whichever rotation or angle convention they choose.  This record only
states the six labels and their order around the central vertex `q_i`.
-/
structure M8CyclicOrderAssumptions
    (D : M8ExtraNeighborData S) where
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
        (S.leftP i) (S.rightP i) (S.nextQ i)

namespace M8CyclicOrderAssumptions

variable {D : M8ExtraNeighborData S}
variable (O : M8CyclicOrderAssumptions D)

/-- The routed proposition carried by the cyclic-order input. -/
def route (i : M8ExtraIndex) : Prop :=
  O.positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
    (S.leftP i) (S.rightP i) (S.nextQ i)

/-- Projection of the isolated cyclic-order assertion. -/
theorem route_holds (i : M8ExtraIndex) :
    O.route i :=
  O.positiveCyclicOrder i

/-- Projection in the original field shape. -/
theorem positiveCyclicOrder_holds (i : M8ExtraIndex) :
    O.positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
      (S.leftP i) (S.rightP i) (S.nextQ i) :=
  O.positiveCyclicOrder i

/-- Convert to the cyclic-order record used by the extraction module. -/
def toNeighborCyclicOrder :
    M8ExtraNeighborData.CyclicOrder D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

/-- Assemble the downstream Lemma 8 combinatorics package from extracted
neighbors and the isolated cyclic-order assumption. -/
def toLemma8Combinatorics :
    M8Lemma8Combinatorics S :=
  D.toLemma8Combinatorics O.toNeighborCyclicOrder

@[simp]
theorem toNeighborCyclicOrder_positiveCyclicOrderAt :
    O.toNeighborCyclicOrder.positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

@[simp]
theorem toLemma8Combinatorics_r (i : M8ExtraIndex) :
    O.toLemma8Combinatorics.r i = D.r i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s (i : M8ExtraIndex) :
    O.toLemma8Combinatorics.s i = D.s i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_positiveCyclicOrderAt :
    O.toLemma8Combinatorics.positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

/-- The assembled package has exactly the requested cyclic order. -/
theorem toLemma8Combinatorics_positiveCyclicOrder
    (i : M8ExtraIndex) :
    O.toLemma8Combinatorics.positiveCyclicOrderAt i
      (O.toLemma8Combinatorics.s i) (O.toLemma8Combinatorics.r i)
      (S.prevQ i) (S.leftP i) (S.rightP i) (S.nextQ i) :=
  O.toLemma8Combinatorics.positiveCyclicOrder_holds i

/-- The assembled package preserves the extracted `r_i` adjacency field. -/
theorem toLemma8Combinatorics_r_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i)
      (O.toLemma8Combinatorics.r i) := by
  simpa using D.r_neighbor i

/-- The assembled package preserves the extracted `s_i` adjacency field. -/
theorem toLemma8Combinatorics_s_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i)
      (O.toLemma8Combinatorics.s i) := by
  simpa using D.s_neighbor i

/-- The assembled package preserves the extracted non-forbidden `r_i` fact. -/
theorem toLemma8Combinatorics_r_not_forbidden (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (O.toLemma8Combinatorics.r i)) := by
  simpa using D.r_not_forbidden i

/-- The assembled package preserves the extracted non-forbidden `s_i` fact. -/
theorem toLemma8Combinatorics_s_not_forbidden (i : M8ExtraIndex) :
    Not (S.forbiddenExtraNeighbor i (O.toLemma8Combinatorics.s i)) := by
  simpa using D.s_not_forbidden i

/-- The assembled package preserves the extracted `r_i != s_i` fact. -/
theorem toLemma8Combinatorics_r_ne_s (i : M8ExtraIndex) :
    Not (O.toLemma8Combinatorics.r i = O.toLemma8Combinatorics.s i) := by
  simpa using D.r_ne_s i

/-- Exhaustiveness is unchanged by adding the cyclic-order input. -/
theorem toLemma8Combinatorics_named_of_extra_neighbor
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (S.centerQ i) x)
    (hnot : Not (S.forbiddenExtraNeighbor i x)) :
    x = O.toLemma8Combinatorics.r i \/
      x = O.toLemma8Combinatorics.s i := by
  simpa using D.named_of_extra_neighbor hadj hnot

/-- Adding cyclic order does not change the local extra-neighbor witness. -/
theorem toLemma8Combinatorics_extraNeighborWitness (i : M8ExtraIndex) :
    O.toLemma8Combinatorics.extraNeighborWitness i :=
  D.extraNeighborWitness_holds i

end M8CyclicOrderAssumptions

/-! ## Equivalence with the extraction module's cyclic-order record -/

namespace M8ExtraNeighborData

variable {D : M8ExtraNeighborData S}

/-- Repackage the extraction module's cyclic-order record in this file's
minimal assumption shape. -/
def cyclicAssumptionsOfNeighborCyclicOrder
    (O : M8ExtraNeighborData.CyclicOrder D) :
    M8CyclicOrderAssumptions D where
  positiveCyclicOrderAt := O.positiveCyclicOrderAt
  positiveCyclicOrder := O.positiveCyclicOrder

@[simp]
theorem cyclicAssumptionsOfNeighborCyclicOrder_positiveCyclicOrderAt
    (O : M8ExtraNeighborData.CyclicOrder D) :
    (cyclicAssumptionsOfNeighborCyclicOrder O).positiveCyclicOrderAt =
      O.positiveCyclicOrderAt :=
  rfl

/-- Both cyclic-order records carry the same data. -/
theorem nonempty_cyclicAssumptions_iff :
    Nonempty (M8CyclicOrderAssumptions D) <->
      Nonempty (M8ExtraNeighborData.CyclicOrder D) :=
  Iff.intro
    (fun h =>
      h.elim fun O =>
        Nonempty.intro O.toNeighborCyclicOrder)
    (fun h =>
      h.elim fun O =>
        Nonempty.intro (cyclicAssumptionsOfNeighborCyclicOrder O))

/-- A cyclic-order assumption is exactly the remaining input needed after
neighbor extraction to build the full Lemma 8 package. -/
def toLemma8CombinatoricsFromCyclicAssumptions
    (O : M8CyclicOrderAssumptions D) :
    M8Lemma8Combinatorics S :=
  O.toLemma8Combinatorics

@[simp]
theorem toLemma8CombinatoricsFromCyclicAssumptions_r
    (O : M8CyclicOrderAssumptions D) (i : M8ExtraIndex) :
    (toLemma8CombinatoricsFromCyclicAssumptions O).r i = D.r i :=
  rfl

@[simp]
theorem toLemma8CombinatoricsFromCyclicAssumptions_s
    (O : M8CyclicOrderAssumptions D) (i : M8ExtraIndex) :
    (toLemma8CombinatoricsFromCyclicAssumptions O).s i = D.s i :=
  rfl

end M8ExtraNeighborData

/-! ## Cyclic-order argument distinctness forced by extraction -/

namespace ExtractedOrderTuple

variable (D : M8ExtraNeighborData S)

/-- The six vertices named in the cyclic-order assertion for index `i`. -/
def args (i : M8ExtraIndex) :
    Fin n × Fin n × Fin n × Fin n × Fin n × Fin n :=
  (D.s i, D.r i, S.prevQ i, S.leftP i, S.rightP i, S.nextQ i)

/-- The first two cyclic-order arguments, `s_i` and `r_i`, are distinct. -/
theorem s_ne_r (i : M8ExtraIndex) :
    Not (D.s i = D.r i) :=
  D.s_ne_r_holds i

/-- `s_i` is not the previous common-neighbor label. -/
theorem s_ne_prevQ (i : M8ExtraIndex) :
    Not (D.s i = S.prevQ i) :=
  D.s_ne_prevQ i

/-- `s_i` is not the left boundary endpoint. -/
theorem s_ne_leftP (i : M8ExtraIndex) :
    Not (D.s i = S.leftP i) :=
  D.s_ne_leftP i

/-- `s_i` is not the right boundary endpoint. -/
theorem s_ne_rightP (i : M8ExtraIndex) :
    Not (D.s i = S.rightP i) :=
  D.s_ne_rightP i

/-- `s_i` is not the next common-neighbor label. -/
theorem s_ne_nextQ (i : M8ExtraIndex) :
    Not (D.s i = S.nextQ i) :=
  D.s_ne_nextQ i

/-- `r_i` is not the previous common-neighbor label. -/
theorem r_ne_prevQ (i : M8ExtraIndex) :
    Not (D.r i = S.prevQ i) :=
  D.r_ne_prevQ i

/-- `r_i` is not the left boundary endpoint. -/
theorem r_ne_leftP (i : M8ExtraIndex) :
    Not (D.r i = S.leftP i) :=
  D.r_ne_leftP i

/-- `r_i` is not the right boundary endpoint. -/
theorem r_ne_rightP (i : M8ExtraIndex) :
    Not (D.r i = S.rightP i) :=
  D.r_ne_rightP i

/-- `r_i` is not the next common-neighbor label. -/
theorem r_ne_nextQ (i : M8ExtraIndex) :
    Not (D.r i = S.nextQ i) :=
  D.r_ne_nextQ i

end ExtractedOrderTuple

/-! ## Routing from an existing Lemma 8 package -/

namespace M8Lemma8Combinatorics

variable (E : M8Lemma8Combinatorics S)

/-- Forget an existing Lemma 8 package to extracted neighbors plus this file's
minimal cyclic-order assumptions. -/
def toCyclicOrderAssumptions :
    M8CyclicOrderAssumptions
      (M8ExtraNeighborData.ofLemma8Combinatorics E) where
  positiveCyclicOrderAt := E.positiveCyclicOrderAt
  positiveCyclicOrder := E.positiveCyclicOrder

@[simp]
theorem toCyclicOrderAssumptions_positiveCyclicOrderAt :
    (toCyclicOrderAssumptions E).positiveCyclicOrderAt =
      E.positiveCyclicOrderAt :=
  rfl

/-- Existing Lemma 8 combinatorics decomposes into neighbor extraction plus
the isolated cyclic-order assumption. -/
theorem exists_extraction_and_cyclic_order_assumptions
    (E : M8Lemma8Combinatorics S) :
    Exists fun D : M8ExtraNeighborData S =>
      Nonempty (M8CyclicOrderAssumptions D) :=
  Exists.intro (M8ExtraNeighborData.ofLemma8Combinatorics E) <|
    Nonempty.intro (toCyclicOrderAssumptions E)

end M8Lemma8Combinatorics

/-! ## Direct constructor from the explicit paper order statement -/

/-- The most direct form of the remaining paper input: choose the cyclic-order
predicate and prove it for the extracted labels. -/
def combinatoricsOfPositiveCyclicOrderAt
    (D : M8ExtraNeighborData S)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
          (S.leftP i) (S.rightP i) (S.nextQ i)) :
    M8Lemma8Combinatorics S :=
  (M8CyclicOrderAssumptions.mk
    positiveCyclicOrderAt positiveCyclicOrder).toLemma8Combinatorics

@[simp]
theorem combinatoricsOfPositiveCyclicOrderAt_r
    (D : M8ExtraNeighborData S)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
          (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (combinatoricsOfPositiveCyclicOrderAt
      D positiveCyclicOrderAt positiveCyclicOrder).r i = D.r i :=
  rfl

@[simp]
theorem combinatoricsOfPositiveCyclicOrderAt_s
    (D : M8ExtraNeighborData S)
    (positiveCyclicOrderAt :
      M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
        Prop)
    (positiveCyclicOrder :
      forall i : M8ExtraIndex,
        positiveCyclicOrderAt i (D.s i) (D.r i) (S.prevQ i)
          (S.leftP i) (S.rightP i) (S.nextQ i))
    (i : M8ExtraIndex) :
    (combinatoricsOfPositiveCyclicOrderAt
      D positiveCyclicOrderAt positiveCyclicOrder).s i = D.s i :=
  rfl

end

end Lemma8CyclicOrderConcrete
end Swanepoel
end ErdosProblems1066
