import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.NoCutMinimalityClosureW19
import ErdosProblems1066.Swanepoel.RemainingObligationLedgerW20

set_option autoImplicit false

/-!
# W21 no-cut source inhabitation endpoint

This file isolates the pay-for-cut/no-cut source required by
`RemainingObligationLedgerW20`.  The available minimal graph facts can inhabit
that source only conditionally, from a minimal-cleared-failure eliminator.  The
unconditional source is exactly the W19 minimality/no-cut field.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutSourceInhabitationW21

open MinimalGraphFacts

noncomputable section

abbrev LedgerNoCutSource : Prop :=
  RemainingObligationLedgerW20.NoCutFamily

abbrev LedgerPayForCutSource : Type 1 :=
  RemainingObligationLedgerW20.PayForCutProducerFamily

/-- The smallest currently exposed theorem that would inhabit W20's no-cut
source: every minimal cleared failure satisfies the W19 pay-for-cut/no-cut
field. -/
abbrev SmallestMissingMinimalityNoCutTheorem : Prop :=
  NoCutMinimalityClosureW19.PayForCutNoCutFieldFamily

variable {n : Nat} {C : _root_.UDConfig n}

/-- Pointwise form of the missing theorem: for a fixed minimal cleared failure,
the W19 field is exactly the no-cut conclusion needed by the ledger. -/
theorem pointwise_noCutSource_iff_smallestMissing
    (hmin : IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C <->
      NoCutMinimalityClosureW19.PayForCutNoCutField C hmin :=
  (NoCutMinimalityClosureW19.payForCutNoCutField_iff_noCutVertex
    (C := C) hmin).symm

/-- Family form: W20's no-cut source is exactly W19's named missing
minimality/no-cut theorem. -/
theorem ledgerNoCutSource_iff_smallestMissing :
    LedgerNoCutSource <-> SmallestMissingMinimalityNoCutTheorem :=
  NoCutMinimalityClosureW19.payForCutNoCutFieldFamily_iff_noCutFamily.symm

/-- Consequently, the W20 pay-for-cut producer family is nonempty exactly when
the W19 missing minimality/no-cut theorem is supplied. -/
theorem nonempty_ledgerPayForCutSource_iff_smallestMissing :
    Nonempty LedgerPayForCutSource <->
      SmallestMissingMinimalityNoCutTheorem :=
  RemainingObligationLedgerW20.payForCutProducerFamily_nonempty_iff_noCutFamily.trans
    ledgerNoCutSource_iff_smallestMissing

/-- A full minimal-failure eliminator from `MinimalGraphFacts` inhabits the
ledger no-cut source vacuously. -/
theorem ledgerNoCutSource_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    LedgerNoCutSource := by
  intro n C hmin
  exact False.elim (hElim C hmin)

/-- The same eliminator supplies the W19 missing theorem. -/
theorem smallestMissing_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    SmallestMissingMinimalityNoCutTheorem :=
  ledgerNoCutSource_iff_smallestMissing.1
    (ledgerNoCutSource_of_minimalClearedFailureEliminator hElim)

/-- Conditional inhabitation of W20's pay-for-cut source from a full
minimal-failure eliminator. -/
def ledgerPayForCutSource_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    LedgerPayForCutSource :=
  RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
    (ledgerNoCutSource_of_minimalClearedFailureEliminator hElim)

/-- Direct construction of W20's pay-for-cut source from exactly the missing
W19 theorem. -/
def ledgerPayForCutSource_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem) :
    LedgerPayForCutSource :=
  RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily
    (ledgerNoCutSource_iff_smallestMissing.2 H)

/-- Reverse extraction: any inhabitant of the W20 pay-for-cut source gives
exactly the W19 missing theorem and no stronger conclusion in this file. -/
theorem smallestMissing_of_ledgerPayForCutSource
    (F : LedgerPayForCutSource) :
    SmallestMissingMinimalityNoCutTheorem :=
  nonempty_ledgerPayForCutSource_iff_smallestMissing.1
    (Nonempty.intro F)

end

end NoCutSourceInhabitationW21
end Swanepoel
end ErdosProblems1066
