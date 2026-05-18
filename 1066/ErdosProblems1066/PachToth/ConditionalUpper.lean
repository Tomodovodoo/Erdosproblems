import ErdosProblems1066.UnitDistanceBounds
import ErdosProblems1066.PachToth.Chain
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.ExactFamilyClosure
import ErdosProblems1066.PachToth.FinalConditional
import ErdosProblems1066.PachToth.RoleHingeFiniteFamilyBridge

/-!
# Conditional Pach--Toth upper bridge

This module is deliberately conditional.  It does not assert the Pach--Toth
`5 / 16` upper bound outright.  Instead it records the exact bridges needed to
turn supplied finite/candidate/role-hinge certificates, or a realized cyclic
chain of certified finite blocks, into upper-bound configurations for the
unit-distance independence problem.

The geometric realization work is packaged as hypotheses: an actual
`UDConfig (16 * k)`, a way to read every independent vertex set as one selected
subset in each block, exact cardinal accounting, and the two soundness
conditions required by `PachToth.Chain`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConditionalUpper

open Chain

noncomputable section

/--
Hypotheses saying that an actual unit-distance configuration realizes the
abstract cyclic `k`-block Pach--Toth chain model.

The fields are intentionally explicit:

* `config` is the genuine geometric `UDConfig`.
* `toBlocks` extracts the selected local vertices in every block from an
  arbitrary set of configuration vertices.
* `card_toBlocks` says that this extraction neither loses nor duplicates
  vertices.
* `blocks_independent_of_independent` says that every independent set in the
  geometric configuration restricts to independent sets in the certified
  first-block graph.
* `connector_rule_of_independent` says that the realized inter-block unit
  edges enforce the connector rule used by the chain theorem.

Proving these fields from coordinates is the missing geometric realization
layer; this structure keeps those assumptions visible and out of the theorem
statement's shadows.
-/
structure KBlockRealization (k : Nat) (hk : 0 < k) where
  config : _root_.UDConfig (16 * k)
  toBlocks : Finset (Fin (16 * k)) -> BlockSelection k
  card_toBlocks :
    forall s : Finset (Fin (16 * k)),
      s.card = Finset.univ.sum fun i : Fin k => (toBlocks s i).card
  blocks_independent_of_independent :
    forall s : Finset (Fin (16 * k)),
      config.IsIndep s -> BlocksIndependent (toBlocks s)
  connector_rule_of_independent :
    forall s : Finset (Fin (16 * k)),
      config.IsIndep s -> ConnectorRule hk (toBlocks s)

/--
Any independent set in a realized `k`-block chain has at most `5 * k`
vertices.
-/
theorem independent_card_le_five_mul {k : Nat} (hk : 0 < k)
    (R : KBlockRealization k hk)
    (s : Finset (Fin (16 * k))) (hs : R.config.IsIndep s) :
    s.card <= 5 * k := by
  rw [R.card_toBlocks s]
  exact selected_card_le_five_mul hk (R.toBlocks s)
    (R.blocks_independent_of_independent s hs)
    (R.connector_rule_of_independent s hs)

/--
Conditional upper-bound configuration supplied by a realized `k`-block chain.

This is the honest bridge theorem: once the realization hypotheses are proved
for some `k`, the actual `UDConfig (16 * k)` from that realization has
independence number at most `5 * k`.
-/
theorem exists_config_with_independent_card_le_five_mul {k : Nat} (hk : 0 < k)
    (R : KBlockRealization k hk) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k := by
  exact Exists.intro R.config (independent_card_le_five_mul hk R)

/--
The same conditional upper bound, written with the ambient vertex count
`16 * k`.
-/
theorem exists_config_with_independent_card_le_floor_ratio {k : Nat} (hk : 0 < k)
    (R : KBlockRealization k hk) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)),
        C.IsIndep s -> s.card <= (5 * (16 * k)) / 16 := by
  refine Exists.intro R.config ?_
  intro s hs
  have hbound := independent_card_le_five_mul hk R s hs
  have hratio : (5 * (16 * k)) / 16 = 5 * k := by
    omega
  simpa [hratio] using hbound

/-! ## Certificate facades

The wrappers below are intentionally one-way conditional bridges.  Each one
takes an already supplied certificate package and exposes the corresponding
Pach--Toth target proposition; none of them constructs or asserts the
existence of such a package.
-/

/-- Exact-multiple target from the compact finite-certificate obligation
package. -/
theorem exactTarget_of_finiteCertificateObligations
    (O : FiniteCertificateObligationSummary.Obligations) :
    PachToth.targetUpperConstructionFiveSixteen :=
  FinalConditional.exactTarget_of_finiteCertificateObligations O

/-- Arbitrary-`n` target from the compact finite-certificate obligation
package. -/
theorem arbitraryTarget_of_finiteCertificateObligations
    (O : FiniteCertificateObligationSummary.Obligations) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  FinalConditional.arbitraryTarget_of_finiteCertificateObligations O

/-- Exact-multiple target from a period-candidate search family and its
cross-block lower-bound certificates. -/
theorem exactTarget_of_periodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target from a period-candidate search family and its
cross-block lower-bound certificates. -/
theorem arbitraryTarget_of_periodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.targetUpperConstructionFiveSixteenArbitrary

/-- Exact-block target at a chosen positive block count from a
period-candidate search family. -/
theorem exactBlockTarget_of_periodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  F.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact-multiple target from the search-facing role-hinge finite-family
certificate package. -/
theorem exactTarget_of_roleHingeTransitionFactsFiniteSearchFamily
    (F :
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target from the search-facing role-hinge finite-family
certificate package, using the checked small-case/remainder closure from the
exact target. -/
theorem arbitraryTarget_of_roleHingeTransitionFactsFiniteSearchFamily
    (F :
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    F.targetUpperConstructionFiveSixteen

/-- Exact-block target at a chosen positive block count from the search-facing
role-hinge finite-family certificate package. -/
theorem exactBlockTarget_of_roleHingeTransitionFactsFiniteSearchFamily
    (F :
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  F.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact-multiple target from the final conditional period-search/equation
transition/cross-block family. -/
theorem exactTarget_of_equationPeriodSearchCrossBlockFamily
    (F : FinalConditional.EquationPeriodSearchCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  FinalConditional.exactTarget_of_periodSearch_equationTransitions_crossBlock F

/-- Arbitrary-`n` target from the final conditional period-search/equation
transition/cross-block family. -/
theorem arbitraryTarget_of_equationPeriodSearchCrossBlockFamily
    (F : FinalConditional.EquationPeriodSearchCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  FinalConditional.arbitraryTarget_of_periodSearch_equationTransitions_crossBlock F

end

end ConditionalUpper
end PachToth
end ErdosProblems1066
