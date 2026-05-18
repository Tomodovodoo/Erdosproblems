import ErdosProblems1066.Swanepoel.NoCutMinimalitySourceInhabitationW22

set_option autoImplicit false

/-!
# W23 concrete no-cut source boundary

This file sharpens the W22 no-cut source audit into a concrete blocker
statement.  The smallest missing no-cut theorem is exactly the assertion that
there is no minimal cleared failure equipped with a cut-vertex partition.

The same equivalence gives the W20 pay-for-cut producer from either a direct
no-blocker statement or from a full minimal-cleared-failure eliminator.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutSourceConcreteW23

open CutVertexInterface
open MinimalGraphFacts

noncomputable section

abbrev SmallestMissingMinimalityNoCutTheorem : Prop :=
  NoCutMinimalitySourceInhabitationW22.SmallestMissingMinimalityNoCutTheorem

abbrev LedgerPayForCutSource : Type 1 :=
  NoCutMinimalitySourceInhabitationW22.LedgerPayForCutSource

abbrev W20PayForCutSource : Type 1 :=
  NoCutMinimalitySourceInhabitationW22.W20PayForCutSource

/-- A concrete obstruction to the no-cut lane: a minimal cleared failure
together with an actual cut-vertex partition. -/
structure MinimalCutVertexBlocker where
  n : Nat
  C : _root_.UDConfig n
  minimal : IsMinimalClearedFailure C
  cut : CutVertexPartition C

abbrev MinimalCutVertexBlockerExists : Prop :=
  Nonempty MinimalCutVertexBlocker

namespace MinimalCutVertexBlocker

def of_cutVertexPartition
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalCutVertexBlocker where
  n := n
  C := C
  minimal := hmin
  cut := P

theorem contradicts_noCutVertex
    (B : MinimalCutVertexBlocker)
    (hno : NoCutVertex B.C) :
    False :=
  hno (Nonempty.intro B.cut)

theorem obstructs_smallestMissing
    (B : MinimalCutVertexBlocker) :
    Not SmallestMissingMinimalityNoCutTheorem := by
  intro H
  exact
    B.contradicts_noCutVertex
      (NoCutMinimalitySourceInhabitationW22.noCutVertex_of_smallestMissing
        (C := B.C) H B.minimal)

theorem obstructs_w20PayForCutSource
    (B : MinimalCutVertexBlocker)
    (F : W20PayForCutSource) :
    False :=
  NoCutMinimalitySourceInhabitationW22.cutVertexPartition_obstructs_w20PayForCutSource
    (C := B.C) F B.minimal B.cut

theorem obstructs_ledgerPayForCutSource
    (B : MinimalCutVertexBlocker)
    (F : LedgerPayForCutSource) :
    False :=
  NoCutMinimalitySourceInhabitationW22.cutVertexPartition_obstructs_ledgerPayForCutSource
    (C := B.C) F B.minimal B.cut

end MinimalCutVertexBlocker

variable {n : Nat} {C : _root_.UDConfig n}

theorem noCutVertex_of_not_blocker
    (hNoBlocker : Not MinimalCutVertexBlockerExists)
    (hmin : IsMinimalClearedFailure C) :
    NoCutVertex C := by
  intro hcut
  cases hcut with
  | intro P =>
      exact
        hNoBlocker
          (Nonempty.intro
            (MinimalCutVertexBlocker.of_cutVertexPartition
              (C := C) hmin P))

theorem smallestMissing_of_not_blocker
    (hNoBlocker : Not MinimalCutVertexBlockerExists) :
    SmallestMissingMinimalityNoCutTheorem := by
  intro n C hmin
  exact
    (NoCutMinimalityClosureW19.payForCutNoCutField_iff_noCutVertex
      (C := C) hmin).2
      (noCutVertex_of_not_blocker (C := C) hNoBlocker hmin)

theorem not_blocker_of_smallestMissing
    (H : SmallestMissingMinimalityNoCutTheorem) :
    Not MinimalCutVertexBlockerExists := by
  intro hBlocker
  cases hBlocker with
  | intro B =>
      exact B.obstructs_smallestMissing H

theorem smallestMissing_iff_not_blocker :
    SmallestMissingMinimalityNoCutTheorem <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_blocker_of_smallestMissing
  case mpr =>
    exact smallestMissing_of_not_blocker

theorem blocker_of_not_smallestMissing
    (hNot : Not SmallestMissingMinimalityNoCutTheorem) :
    MinimalCutVertexBlockerExists := by
  classical
  by_contra hBlocker
  exact hNot (smallestMissing_of_not_blocker hBlocker)

theorem not_smallestMissing_iff_blocker :
    Not SmallestMissingMinimalityNoCutTheorem <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    exact blocker_of_not_smallestMissing
  case mpr =>
    intro hBlocker H
    exact (smallestMissing_iff_not_blocker.1 H) hBlocker

theorem not_blocker_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    Not MinimalCutVertexBlockerExists := by
  intro hBlocker
  cases hBlocker with
  | intro B =>
      exact hElim B.C B.minimal

theorem smallestMissing_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    SmallestMissingMinimalityNoCutTheorem :=
  smallestMissing_of_not_blocker
    (not_blocker_of_minimalClearedFailureEliminator hElim)

def w20PayForCutSource_of_not_blocker
    (hNoBlocker : Not MinimalCutVertexBlockerExists) :
    W20PayForCutSource :=
  NoCutMinimalitySourceInhabitationW22.w20PayForCutSource_of_smallestMissing
    (smallestMissing_of_not_blocker hNoBlocker)

def ledgerPayForCutSource_of_not_blocker
    (hNoBlocker : Not MinimalCutVertexBlockerExists) :
    LedgerPayForCutSource :=
  NoCutMinimalitySourceInhabitationW22.ledgerPayForCutSource_of_smallestMissing
    (smallestMissing_of_not_blocker hNoBlocker)

def w20PayForCutSource_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    W20PayForCutSource :=
  w20PayForCutSource_of_not_blocker
    (not_blocker_of_minimalClearedFailureEliminator hElim)

def ledgerPayForCutSource_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    LedgerPayForCutSource :=
  ledgerPayForCutSource_of_not_blocker
    (not_blocker_of_minimalClearedFailureEliminator hElim)

theorem nonempty_w20PayForCutSource_iff_not_blocker :
    Nonempty W20PayForCutSource <->
      Not MinimalCutVertexBlockerExists :=
  NoCutMinimalitySourceInhabitationW22.nonempty_w20PayForCutSource_iff_smallestMissing.trans
    smallestMissing_iff_not_blocker

theorem nonempty_ledgerPayForCutSource_iff_not_blocker :
    Nonempty LedgerPayForCutSource <->
      Not MinimalCutVertexBlockerExists :=
  NoCutMinimalitySourceInhabitationW22.nonempty_ledgerPayForCutSource_iff_smallestMissing.trans
    smallestMissing_iff_not_blocker

theorem not_nonempty_w20PayForCutSource_iff_blocker :
    Not (Nonempty W20PayForCutSource) <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hNot
    by_contra hBlocker
    exact hNot (nonempty_w20PayForCutSource_iff_not_blocker.2 hBlocker)
  case mpr =>
    intro hBlocker hSource
    exact (nonempty_w20PayForCutSource_iff_not_blocker.1 hSource) hBlocker

theorem not_nonempty_ledgerPayForCutSource_iff_blocker :
    Not (Nonempty LedgerPayForCutSource) <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hNot
    by_contra hBlocker
    exact hNot (nonempty_ledgerPayForCutSource_iff_not_blocker.2 hBlocker)
  case mpr =>
    intro hBlocker hSource
    exact (nonempty_ledgerPayForCutSource_iff_not_blocker.1 hSource) hBlocker

end

end NoCutSourceConcreteW23
end Swanepoel
end ErdosProblems1066
