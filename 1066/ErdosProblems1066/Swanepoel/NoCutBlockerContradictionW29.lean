import ErdosProblems1066.Swanepoel.NoCutSourceConstructionW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 no-cut blocker contradiction

This file keeps the W28 no-cut blocker surface exact.  Local deletion data is
handled at the concrete blocker level first, then lifted to source-level
equivalences with the existence of a minimal cut-vertex blocker.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutBlockerContradictionW29

open MinimalFailureLocalExclusions
open NoCutSourceConstructionW28

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutSourceConstructionW28.MinimalCutVertexBlocker

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutSourceConstructionW28.MinimalCutVertexBlockerExists

abbrev BlockerDegreeDeletionSource : Prop :=
  NoCutSourceConstructionW28.BlockerDegreeDeletionSource

abbrev BlockerLocalClosedNeighborhoodDeletionSource : Prop :=
  NoCutSourceConstructionW28.BlockerLocalClosedNeighborhoodDeletionSource

abbrev BlockerDirectCardBoundCertificateSource : Prop :=
  NoCutSourceConstructionW28.BlockerDirectCardBoundCertificateSource

abbrev BlockerTupledClosedNeighborhoodDeletionSource : Prop :=
  NoCutSourceConstructionW28.BlockerTupledClosedNeighborhoodDeletionSource

abbrev BlockerTupledDirectCardBoundDeletionSource : Prop :=
  NoCutSourceConstructionW28.BlockerTupledDirectCardBoundDeletionSource

abbrev BlockerDeficientNeighborhoodDeletionSource : Prop :=
  NoCutSourceConstructionW28.BlockerDeficientNeighborhoodDeletionSource

abbrev BlockerTupledClosedNeighborhoodDeletion
    (B : MinimalCutVertexBlocker) : Prop :=
  Exists fun deleted : Finset (Fin B.n) =>
    Exists fun reinsertion : Finset (Fin B.n) =>
      MinimalCounterexample.IsClosedNeighborhood B.C reinsertion deleted /\
      (Exists fun center : Fin B.n =>
        deleted <= DegreePipeline.closedUnitNeighborhood B.C center) /\
      2 <= reinsertion.card /\
      reinsertion.card <= 8 /\
      B.C.IsIndep reinsertion

abbrev BlockerTupledDirectCardBoundDeletion
    (B : MinimalCutVertexBlocker) : Prop :=
  Exists fun deleted : Finset (Fin B.n) =>
    Exists fun reinsertion : Finset (Fin B.n) =>
      MinimalCounterexample.IsClosedNeighborhood B.C reinsertion deleted /\
      (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
      reinsertion.Nonempty /\
      reinsertion.card <= 8 /\
      B.C.IsIndep reinsertion

abbrev BlockerDeficientNeighborhoodDeletion
    (B : MinimalCutVertexBlocker) : Prop :=
  Exists fun S : Finset (Fin B.n) =>
    S.Nonempty /\
    B.C.IsIndep S /\
    S.card <= 8 /\
    (SmallIndependentNeighborhood.outsideNeighborhoodOf B.C S).card <
      3 * S.card

theorem nonempty_localClosedNeighborhoodDeletion_of_blockerTupledClosed
    {B : MinimalCutVertexBlocker}
    (hdel : BlockerTupledClosedNeighborhoodDeletion B) :
    Nonempty (LocalClosedNeighborhoodDeletion B.C) := by
  cases hdel with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          exact Nonempty.intro
            { deleted := deleted
              reinsertion := reinsertion
              closedNeighborhood := hdata.1
              deletedSubsetClosedUnitNeighborhood := hdata.2.1
              reinsertionCardLower := hdata.2.2.1
              reinsertionCardUpper := hdata.2.2.2.1
              reinsertionIndep := hdata.2.2.2.2 }

theorem exists_degreeLocalDeletionCertificate_of_blockerTupledClosed
    {B : MinimalCutVertexBlocker}
    (hdel : BlockerTupledClosedNeighborhoodDeletion B) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (DegreeLocalDeletionCertificate B.C Csmall) := by
  cases nonempty_localClosedNeighborhoodDeletion_of_blockerTupledClosed hdel with
  | intro L =>
      exact L.exists_degreeLocalDeletionCertificate

theorem exists_localDeletionCertificate_of_blockerTupledDirect
    {B : MinimalCutVertexBlocker}
    (hdel : BlockerTupledDirectCardBoundDeletion B) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (LocalDeletionCertificate B.C Csmall) := by
  cases hdel with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          exact
            LocalDeletionWithCardBound.exists_localDeletionCertificate_of_data
              B.C deleted reinsertion hdata.1 hdata.2.1 hdata.2.2.1
              hdata.2.2.2.1 hdata.2.2.2.2

theorem blockerTupledDirect_of_blockerDeficient
    {B : MinimalCutVertexBlocker}
    (hdel : BlockerDeficientNeighborhoodDeletion B) :
    BlockerTupledDirectCardBoundDeletion B := by
  cases hdel with
  | intro S hdata =>
      exact
        Exists.intro (SmallIndependentNeighborhood.closedNeighborhoodOf B.C S)
          (Exists.intro S
            (DeficientNeighborhood.canonicalDeletion_satisfies_directLocalDeletionInputs
              B.C hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2))

theorem exists_localDeletionCertificate_of_blockerDeficient
    {B : MinimalCutVertexBlocker}
    (hdel : BlockerDeficientNeighborhoodDeletion B) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (LocalDeletionCertificate B.C Csmall) := by
  cases hdel with
  | intro S hdata =>
      exact
        DeficientNeighborhood.exists_localDeletionCertificate_of_deficientNeighborhood
          B.C hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2

theorem false_of_blockerDegreeDeletion
    (B : MinimalCutVertexBlocker)
    (hdel :
      Exists fun nSmall : Nat =>
        Exists fun Csmall : _root_.UDConfig nSmall =>
          Nonempty (DegreeLocalDeletionCertificate B.C Csmall)) :
    False := by
  cases hdel with
  | intro _nSmall hrest =>
      cases hrest with
      | intro Csmall hcert =>
          exact
            not_nonempty_degreeLocalDeletionCertificate_of_minimalFailure
              (Csmall := Csmall) B.minimal hcert

theorem false_of_blockerLocalClosedNeighborhoodDeletion
    (B : MinimalCutVertexBlocker)
    (hdel : Nonempty (LocalClosedNeighborhoodDeletion B.C)) :
    False := by
  cases hdel with
  | intro L =>
      exact LocalClosedNeighborhoodDeletion.false_of_minimalFailure B.minimal L

theorem false_of_blockerDirectCardBoundCertificate
    (B : MinimalCutVertexBlocker)
    (hdel :
      Exists fun nSmall : Nat =>
        Exists fun Csmall : _root_.UDConfig nSmall =>
          Nonempty (LocalDeletionCertificate B.C Csmall)) :
    False := by
  cases hdel with
  | intro _nSmall hrest =>
      cases hrest with
      | intro Csmall hcert =>
          exact
            LocalDeletionCertificate.not_nonempty_localDeletionCertificate_of_minimalFailure
              (Csmall := Csmall) B.minimal hcert

theorem false_of_blockerTupledClosedNeighborhoodDeletion
    (B : MinimalCutVertexBlocker)
    (hdel : BlockerTupledClosedNeighborhoodDeletion B) :
    False :=
  false_of_blockerLocalClosedNeighborhoodDeletion B
    (nonempty_localClosedNeighborhoodDeletion_of_blockerTupledClosed hdel)

theorem false_of_blockerTupledDirectCardBoundDeletion
    (B : MinimalCutVertexBlocker)
    (hdel : BlockerTupledDirectCardBoundDeletion B) :
    False :=
  false_of_blockerDirectCardBoundCertificate B
    (exists_localDeletionCertificate_of_blockerTupledDirect hdel)

theorem false_of_blockerDeficientNeighborhoodDeletion
    (B : MinimalCutVertexBlocker)
    (hdel : BlockerDeficientNeighborhoodDeletion B) :
    False :=
  false_of_blockerDirectCardBoundCertificate B
    (exists_localDeletionCertificate_of_blockerDeficient hdel)

theorem not_minimalCutVertexBlockerExists_of_blockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    Not MinimalCutVertexBlockerExists := by
  intro hblocker
  cases hblocker with
  | intro B =>
      exact false_of_blockerDegreeDeletion B (H B)

theorem not_minimalCutVertexBlockerExists_of_blockerLocalClosed
    (H : BlockerLocalClosedNeighborhoodDeletionSource) :
    Not MinimalCutVertexBlockerExists := by
  intro hblocker
  cases hblocker with
  | intro B =>
      exact false_of_blockerLocalClosedNeighborhoodDeletion B (H B)

theorem not_minimalCutVertexBlockerExists_of_blockerDirectCard
    (H : BlockerDirectCardBoundCertificateSource) :
    Not MinimalCutVertexBlockerExists := by
  intro hblocker
  cases hblocker with
  | intro B =>
      exact false_of_blockerDirectCardBoundCertificate B (H B)

theorem not_minimalCutVertexBlockerExists_of_blockerTupledClosed
    (H : BlockerTupledClosedNeighborhoodDeletionSource) :
    Not MinimalCutVertexBlockerExists := by
  intro hblocker
  cases hblocker with
  | intro B =>
      exact false_of_blockerTupledClosedNeighborhoodDeletion B (H B)

theorem not_minimalCutVertexBlockerExists_of_blockerTupledDirect
    (H : BlockerTupledDirectCardBoundDeletionSource) :
    Not MinimalCutVertexBlockerExists := by
  intro hblocker
  cases hblocker with
  | intro B =>
      exact false_of_blockerTupledDirectCardBoundDeletion B (H B)

theorem not_minimalCutVertexBlockerExists_of_blockerDeficient
    (H : BlockerDeficientNeighborhoodDeletionSource) :
    Not MinimalCutVertexBlockerExists := by
  intro hblocker
  cases hblocker with
  | intro B =>
      exact false_of_blockerDeficientNeighborhoodDeletion B (H B)

theorem blockerTupledDirectSource_of_blockerDeficientSource
    (H : BlockerDeficientNeighborhoodDeletionSource) :
    BlockerTupledDirectCardBoundDeletionSource := by
  intro B
  exact blockerTupledDirect_of_blockerDeficient (H B)

theorem blockerDegreeDeletionSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    BlockerDegreeDeletionSource := by
  intro B
  exact False.elim (hno (Nonempty.intro B))

theorem blockerLocalClosedSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    BlockerLocalClosedNeighborhoodDeletionSource := by
  intro B
  exact False.elim (hno (Nonempty.intro B))

theorem blockerDirectCardSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    BlockerDirectCardBoundCertificateSource := by
  intro B
  exact False.elim (hno (Nonempty.intro B))

theorem blockerTupledClosedSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    BlockerTupledClosedNeighborhoodDeletionSource := by
  intro B
  exact False.elim (hno (Nonempty.intro B))

theorem blockerTupledDirectSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    BlockerTupledDirectCardBoundDeletionSource := by
  intro B
  exact False.elim (hno (Nonempty.intro B))

theorem blockerDeficientSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    BlockerDeficientNeighborhoodDeletionSource := by
  intro B
  exact False.elim (hno (Nonempty.intro B))

theorem blockerDegreeDeletionSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDegreeDeletionSource <-> Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_blockerDegreeDeletionSource
  case mpr =>
    exact blockerDegreeDeletionSource_of_not_minimalCutVertexBlockerExists

theorem blockerLocalClosedSource_iff_not_minimalCutVertexBlockerExists :
    BlockerLocalClosedNeighborhoodDeletionSource <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_blockerLocalClosed
  case mpr =>
    exact blockerLocalClosedSource_of_not_minimalCutVertexBlockerExists

theorem blockerDirectCardSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDirectCardBoundCertificateSource <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_blockerDirectCard
  case mpr =>
    exact blockerDirectCardSource_of_not_minimalCutVertexBlockerExists

theorem blockerTupledClosedSource_iff_not_minimalCutVertexBlockerExists :
    BlockerTupledClosedNeighborhoodDeletionSource <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_blockerTupledClosed
  case mpr =>
    exact blockerTupledClosedSource_of_not_minimalCutVertexBlockerExists

theorem blockerTupledDirectSource_iff_not_minimalCutVertexBlockerExists :
    BlockerTupledDirectCardBoundDeletionSource <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_blockerTupledDirect
  case mpr =>
    exact blockerTupledDirectSource_of_not_minimalCutVertexBlockerExists

theorem blockerDeficientSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDeficientNeighborhoodDeletionSource <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_blockerDeficient
  case mpr =>
    exact blockerDeficientSource_of_not_minimalCutVertexBlockerExists

theorem not_blockerDegreeDeletionSource_iff_minimalCutVertexBlockerExists :
    Not BlockerDegreeDeletionSource <-> MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hno
    exact hmissing
      (blockerDegreeDeletionSource_of_not_minimalCutVertexBlockerExists hno)
  case mpr =>
    intro hblocker H
    exact not_minimalCutVertexBlockerExists_of_blockerDegreeDeletionSource H hblocker

theorem not_blockerLocalClosedSource_iff_minimalCutVertexBlockerExists :
    Not BlockerLocalClosedNeighborhoodDeletionSource <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hno
    exact hmissing
      (blockerLocalClosedSource_of_not_minimalCutVertexBlockerExists hno)
  case mpr =>
    intro hblocker H
    exact not_minimalCutVertexBlockerExists_of_blockerLocalClosed H hblocker

theorem not_blockerDirectCardSource_iff_minimalCutVertexBlockerExists :
    Not BlockerDirectCardBoundCertificateSource <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hno
    exact hmissing
      (blockerDirectCardSource_of_not_minimalCutVertexBlockerExists hno)
  case mpr =>
    intro hblocker H
    exact not_minimalCutVertexBlockerExists_of_blockerDirectCard H hblocker

theorem not_blockerTupledClosedSource_iff_minimalCutVertexBlockerExists :
    Not BlockerTupledClosedNeighborhoodDeletionSource <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hno
    exact hmissing
      (blockerTupledClosedSource_of_not_minimalCutVertexBlockerExists hno)
  case mpr =>
    intro hblocker H
    exact not_minimalCutVertexBlockerExists_of_blockerTupledClosed H hblocker

theorem not_blockerTupledDirectSource_iff_minimalCutVertexBlockerExists :
    Not BlockerTupledDirectCardBoundDeletionSource <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hno
    exact hmissing
      (blockerTupledDirectSource_of_not_minimalCutVertexBlockerExists hno)
  case mpr =>
    intro hblocker H
    exact not_minimalCutVertexBlockerExists_of_blockerTupledDirect H hblocker

theorem not_blockerDeficientSource_iff_minimalCutVertexBlockerExists :
    Not BlockerDeficientNeighborhoodDeletionSource <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hno
    exact hmissing
      (blockerDeficientSource_of_not_minimalCutVertexBlockerExists hno)
  case mpr =>
    intro hblocker H
    exact not_minimalCutVertexBlockerExists_of_blockerDeficient H hblocker

theorem minimalCutVertexBlockerExists_iff_not_blockerDegreeDeletionSource :
    MinimalCutVertexBlockerExists <-> Not BlockerDegreeDeletionSource :=
  not_blockerDegreeDeletionSource_iff_minimalCutVertexBlockerExists.symm

theorem minimalCutVertexBlockerExists_iff_not_blockerTupledClosedSource :
    MinimalCutVertexBlockerExists <->
      Not BlockerTupledClosedNeighborhoodDeletionSource :=
  not_blockerTupledClosedSource_iff_minimalCutVertexBlockerExists.symm

theorem minimalCutVertexBlockerExists_iff_not_blockerTupledDirectSource :
    MinimalCutVertexBlockerExists <->
      Not BlockerTupledDirectCardBoundDeletionSource :=
  not_blockerTupledDirectSource_iff_minimalCutVertexBlockerExists.symm

theorem minimalCutVertexBlockerExists_iff_not_blockerDeficientSource :
    MinimalCutVertexBlockerExists <->
      Not BlockerDeficientNeighborhoodDeletionSource :=
  not_blockerDeficientSource_iff_minimalCutVertexBlockerExists.symm

end

end NoCutBlockerContradictionW29
end Swanepoel

namespace Verified

abbrev SwanepoelW29NoCutMinimalCutVertexBlockerExists : Prop :=
  Swanepoel.NoCutBlockerContradictionW29.MinimalCutVertexBlockerExists

abbrev SwanepoelW29BlockerDegreeDeletionSource : Prop :=
  Swanepoel.NoCutBlockerContradictionW29.BlockerDegreeDeletionSource

abbrev SwanepoelW29BlockerTupledClosedNeighborhoodDeletionSource : Prop :=
  Swanepoel.NoCutBlockerContradictionW29.BlockerTupledClosedNeighborhoodDeletionSource

abbrev SwanepoelW29BlockerTupledDirectCardBoundDeletionSource : Prop :=
  Swanepoel.NoCutBlockerContradictionW29.BlockerTupledDirectCardBoundDeletionSource

abbrev SwanepoelW29BlockerDeficientNeighborhoodDeletionSource : Prop :=
  Swanepoel.NoCutBlockerContradictionW29.BlockerDeficientNeighborhoodDeletionSource

theorem swanepoelW29_blockerDegreeDeletionSource_exactly_noBlocker :
    SwanepoelW29BlockerDegreeDeletionSource <->
      Not SwanepoelW29NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerContradictionW29.blockerDegreeDeletionSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW29_blockerTupledClosedSource_exactly_noBlocker :
    SwanepoelW29BlockerTupledClosedNeighborhoodDeletionSource <->
      Not SwanepoelW29NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerContradictionW29.blockerTupledClosedSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW29_blockerTupledDirectSource_exactly_noBlocker :
    SwanepoelW29BlockerTupledDirectCardBoundDeletionSource <->
      Not SwanepoelW29NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerContradictionW29.blockerTupledDirectSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW29_blockerDeficientSource_exactly_noBlocker :
    SwanepoelW29BlockerDeficientNeighborhoodDeletionSource <->
      Not SwanepoelW29NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerContradictionW29.blockerDeficientSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW29_blockerExists_exactly_no_degreeDeletionSource :
    SwanepoelW29NoCutMinimalCutVertexBlockerExists <->
      Not SwanepoelW29BlockerDegreeDeletionSource :=
  Swanepoel.NoCutBlockerContradictionW29.minimalCutVertexBlockerExists_iff_not_blockerDegreeDeletionSource

theorem swanepoelW29_blockerExists_exactly_no_tupledClosedSource :
    SwanepoelW29NoCutMinimalCutVertexBlockerExists <->
      Not SwanepoelW29BlockerTupledClosedNeighborhoodDeletionSource :=
  Swanepoel.NoCutBlockerContradictionW29.minimalCutVertexBlockerExists_iff_not_blockerTupledClosedSource

theorem swanepoelW29_blockerExists_exactly_no_tupledDirectSource :
    SwanepoelW29NoCutMinimalCutVertexBlockerExists <->
      Not SwanepoelW29BlockerTupledDirectCardBoundDeletionSource :=
  Swanepoel.NoCutBlockerContradictionW29.minimalCutVertexBlockerExists_iff_not_blockerTupledDirectSource

theorem swanepoelW29_blockerExists_exactly_no_deficientSource :
    SwanepoelW29NoCutMinimalCutVertexBlockerExists <->
      Not SwanepoelW29BlockerDeficientNeighborhoodDeletionSource :=
  Swanepoel.NoCutBlockerContradictionW29.minimalCutVertexBlockerExists_iff_not_blockerDeficientSource

end Verified
end ErdosProblems1066
