import ErdosProblems1066.Swanepoel.M8LateTriplesFromNoEarly
import ErdosProblems1066.Swanepoel.M8TurnBoundsFromArc

/-!
# Concrete M8 late-triples bridge

This module ties together the two finite inputs currently available for the
late-triples side of the `m = 8` route:

* no early named triple equalities, packaged by `M8LateTriplesFromNoEarly`;
* the nonconcave-arc/angle-to-turn data, which supplies Lemma 10's
  at-most-one-failure conclusion.

The result is still conditional on those explicit inputs.  It only removes
the bookkeeping gap between no-early triples, the pipeline
`M8LateTriplesField`, and the final finite contradiction.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace M8LateTriplesConcrete

open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## No-early triples to the pipeline field -/

/-- Direct projection from no-early triple equalities to the pipeline
late-triples field. -/
theorem lateTriplesField_of_noEarlyTripleEquality
    (P : M8HonestLocalPredicates G)
    (hno : M8NoEarlyTripleEquality P.data) :
    M8PipelineClosure.M8LateTriplesField P :=
  M8LateTriplesFromNoEarly.m8PipelineLateTriplesField_of_noEarlyTripleEquality
    P hno

/-- Direct projection from no-early triple equalities to the honest
late-triples predicate consumed by `Lemma10Bridge`. -/
theorem lateTriples_of_noEarlyTripleEquality
    (P : M8HonestLocalPredicates G)
    (hno : M8NoEarlyTripleEquality P.data) :
    P.LateTriples :=
  (lateTriplesField_of_noEarlyTripleEquality P hno).lateTriples

/-! ## Pair no-early triples with the turn-combinatorics package -/

/-- The concrete finite data needed to close the local `m = 8`
contradiction through the no-early-triples route. -/
structure M8NoEarlyTurnData
    (P : M8HonestLocalPredicates G) where
  noEarlyTripleEquality : M8NoEarlyTripleEquality P.data
  arcAngleData : M8TurnBoundsFromArc.M8ArcAngleData P

namespace M8NoEarlyTurnData

variable {P : M8HonestLocalPredicates G}

/-- Forget to the no-early package from `M8LateTriplesFromNoEarly`. -/
def toPipelineNoEarlyTriples
    (D : M8NoEarlyTurnData P) :
    M8LateTriplesFromNoEarly.M8PipelineNoEarlyTriples P where
  noEarlyTripleEquality := D.noEarlyTripleEquality

/-- The no-early part supplies the `M8PipelineClosure` late-triples field. -/
def lateTriplesField
    (D : M8NoEarlyTurnData P) :
    M8PipelineClosure.M8LateTriplesField P :=
  D.toPipelineNoEarlyTriples.toM8LateTriplesField

/-- The no-early part supplies the honest late-triples predicate. -/
theorem lateTriples
    (D : M8NoEarlyTurnData P) :
    P.LateTriples :=
  D.lateTriplesField.lateTriples

/-- The turn-combinatorics part supplies Lemma 10's at-most-one-failure
field. -/
theorem atMostOneFailure
    (D : M8NoEarlyTurnData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    P.AtMostOneFailure :=
  D.arcAngleData.atMostOneFailure

/-- No-early triples plus the turn-combinatorics package close the local
`m = 8` finite contradiction. -/
theorem contradiction
    (D : M8NoEarlyTurnData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  Lemma10Bridge.M8HonestLocalPredicates.contradiction P
    D.atMostOneFailure D.lateTriples

end M8NoEarlyTurnData

/-! ## Direct theorem form -/

/-- Direct theorem form: no-early triples provide `M8LateTriplesField`, the
arc/angle turn data provides at-most-one-failure, and `Lemma10Bridge` combines
the two. -/
theorem contradiction_of_noEarlyTripleEquality_and_arcAngleData
    (P : M8HonestLocalPredicates G)
    (hno : M8NoEarlyTripleEquality P.data)
    (D : M8TurnBoundsFromArc.M8ArcAngleData P)
    [DecidablePred (M8BrokenLatticeGood P.data)] :
    False :=
  (M8NoEarlyTurnData.mk hno D).contradiction

end M8LateTriplesConcrete
end Swanepoel
end ErdosProblems1066

end
