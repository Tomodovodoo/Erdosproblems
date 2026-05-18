import ErdosProblems1066.Swanepoel.NoCutBlockerContradictionW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 no-cut blocker elimination source reductions

This file is the W30 reduction layer above `NoCutBlockerContradictionW29`.
It does not assert an unconditional no-cut theorem.  Instead, it packages the
small source routes that prove `Not MinimalCutVertexBlockerExists`:

* degree deletion;
* closed-neighborhood deletion/reinsertion data;
* direct card-bound deletion/reinsertion data;
* deficient-neighborhood data, reduced to the direct route.

The deletion/reinsertion sources are aliases of the W29 tupled blocker data,
so the checked endpoints stay on the concrete minimal cut-vertex blocker
surface and avoid target-level shortcuts.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutBlockerEliminationW30

open NoCutBlockerContradictionW29

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutBlockerContradictionW29.MinimalCutVertexBlocker

abbrev MinimalCutVertexBlockerExists : Prop :=
  NoCutBlockerContradictionW29.MinimalCutVertexBlockerExists

abbrev BlockerDegreeDeletionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerDegreeDeletionSource

abbrev BlockerLocalClosedNeighborhoodDeletionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerLocalClosedNeighborhoodDeletionSource

abbrev BlockerDirectCardBoundCertificateSource : Prop :=
  NoCutBlockerContradictionW29.BlockerDirectCardBoundCertificateSource

/-- W29 tupled closed-neighborhood data, viewed as deletion/reinsertion data. -/
abbrev BlockerClosedDeletionReinsertion
    (B : MinimalCutVertexBlocker) : Prop :=
  NoCutBlockerContradictionW29.BlockerTupledClosedNeighborhoodDeletion B

/-- W29 tupled direct card-bound data, viewed as deletion/reinsertion data. -/
abbrev BlockerDirectDeletionReinsertion
    (B : MinimalCutVertexBlocker) : Prop :=
  NoCutBlockerContradictionW29.BlockerTupledDirectCardBoundDeletion B

/-- W29 deficient-neighborhood data, the canonical source for direct deletion. -/
abbrev BlockerDeficientDeletion
    (B : MinimalCutVertexBlocker) : Prop :=
  NoCutBlockerContradictionW29.BlockerDeficientNeighborhoodDeletion B

abbrev BlockerClosedDeletionReinsertionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerTupledClosedNeighborhoodDeletionSource

abbrev BlockerDirectDeletionReinsertionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerTupledDirectCardBoundDeletionSource

abbrev BlockerDeficientDeletionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerDeficientNeighborhoodDeletionSource

abbrev BlockerTupledClosedNeighborhoodDeletionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerTupledClosedNeighborhoodDeletionSource

abbrev BlockerTupledDirectCardBoundDeletionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerTupledDirectCardBoundDeletionSource

abbrev BlockerDeficientNeighborhoodDeletionSource : Prop :=
  NoCutBlockerContradictionW29.BlockerDeficientNeighborhoodDeletionSource

theorem blockerLocalClosedSource_of_closedDeletionReinsertionSource
    (H : BlockerClosedDeletionReinsertionSource) :
    BlockerLocalClosedNeighborhoodDeletionSource := by
  intro B
  exact nonempty_localClosedNeighborhoodDeletion_of_blockerTupledClosed (H B)

theorem blockerDegreeDeletionSource_of_closedDeletionReinsertionSource
    (H : BlockerClosedDeletionReinsertionSource) :
    BlockerDegreeDeletionSource := by
  intro B
  exact exists_degreeLocalDeletionCertificate_of_blockerTupledClosed (H B)

theorem blockerDirectCardSource_of_directDeletionReinsertionSource
    (H : BlockerDirectDeletionReinsertionSource) :
    BlockerDirectCardBoundCertificateSource := by
  intro B
  exact exists_localDeletionCertificate_of_blockerTupledDirect (H B)

theorem directDeletionReinsertionSource_of_deficientDeletionSource
    (H : BlockerDeficientDeletionSource) :
    BlockerDirectDeletionReinsertionSource :=
  blockerTupledDirectSource_of_blockerDeficientSource H

theorem blockerDirectCardSource_of_deficientDeletionSource
    (H : BlockerDeficientDeletionSource) :
    BlockerDirectCardBoundCertificateSource :=
  blockerDirectCardSource_of_directDeletionReinsertionSource
    (directDeletionReinsertionSource_of_deficientDeletionSource H)

theorem not_minimalCutVertexBlockerExists_of_degreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    Not MinimalCutVertexBlockerExists :=
  not_minimalCutVertexBlockerExists_of_blockerDegreeDeletionSource H

theorem not_minimalCutVertexBlockerExists_of_closedDeletionReinsertionSource
    (H : BlockerClosedDeletionReinsertionSource) :
    Not MinimalCutVertexBlockerExists :=
  not_minimalCutVertexBlockerExists_of_blockerTupledClosed H

theorem not_minimalCutVertexBlockerExists_of_directDeletionReinsertionSource
    (H : BlockerDirectDeletionReinsertionSource) :
    Not MinimalCutVertexBlockerExists :=
  not_minimalCutVertexBlockerExists_of_blockerTupledDirect H

theorem not_minimalCutVertexBlockerExists_of_deficientDeletionSource
    (H : BlockerDeficientDeletionSource) :
    Not MinimalCutVertexBlockerExists :=
  not_minimalCutVertexBlockerExists_of_blockerDeficient H

theorem degreeDeletionSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDegreeDeletionSource <-> Not MinimalCutVertexBlockerExists :=
  blockerDegreeDeletionSource_iff_not_minimalCutVertexBlockerExists

theorem closedDeletionReinsertionSource_iff_not_minimalCutVertexBlockerExists :
    BlockerClosedDeletionReinsertionSource <->
      Not MinimalCutVertexBlockerExists :=
  blockerTupledClosedSource_iff_not_minimalCutVertexBlockerExists

theorem directDeletionReinsertionSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDirectDeletionReinsertionSource <->
      Not MinimalCutVertexBlockerExists :=
  blockerTupledDirectSource_iff_not_minimalCutVertexBlockerExists

theorem deficientDeletionSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDeficientDeletionSource <-> Not MinimalCutVertexBlockerExists :=
  blockerDeficientSource_iff_not_minimalCutVertexBlockerExists

theorem tupledClosedSource_iff_not_minimalCutVertexBlockerExists :
    BlockerTupledClosedNeighborhoodDeletionSource <->
      Not MinimalCutVertexBlockerExists :=
  blockerTupledClosedSource_iff_not_minimalCutVertexBlockerExists

theorem tupledDirectSource_iff_not_minimalCutVertexBlockerExists :
    BlockerTupledDirectCardBoundDeletionSource <->
      Not MinimalCutVertexBlockerExists :=
  blockerTupledDirectSource_iff_not_minimalCutVertexBlockerExists

theorem deficientSource_iff_not_minimalCutVertexBlockerExists :
    BlockerDeficientNeighborhoodDeletionSource <->
      Not MinimalCutVertexBlockerExists :=
  blockerDeficientSource_iff_not_minimalCutVertexBlockerExists

abbrev TupledBlockerEliminationSource : Prop :=
  BlockerTupledClosedNeighborhoodDeletionSource \/
    BlockerTupledDirectCardBoundDeletionSource \/
      BlockerDeficientNeighborhoodDeletionSource

abbrev DeletionReinsertionEliminationSource : Prop :=
  BlockerClosedDeletionReinsertionSource \/
    BlockerDirectDeletionReinsertionSource \/
      BlockerDeficientDeletionSource

abbrev CanonicalBlockerEliminationSource : Prop :=
  BlockerDegreeDeletionSource \/
    BlockerLocalClosedNeighborhoodDeletionSource \/
      BlockerDirectCardBoundCertificateSource \/
        DeletionReinsertionEliminationSource

theorem not_minimalCutVertexBlockerExists_of_tupledEliminationSource
    (H : TupledBlockerEliminationSource) :
    Not MinimalCutVertexBlockerExists := by
  cases H with
  | inl Hclosed =>
      exact not_minimalCutVertexBlockerExists_of_blockerTupledClosed Hclosed
  | inr Hrest =>
      cases Hrest with
      | inl Hdirect =>
          exact not_minimalCutVertexBlockerExists_of_blockerTupledDirect Hdirect
      | inr Hdeficient =>
          exact not_minimalCutVertexBlockerExists_of_blockerDeficient Hdeficient

theorem tupledEliminationSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    TupledBlockerEliminationSource :=
  Or.inl (blockerTupledClosedSource_of_not_minimalCutVertexBlockerExists hno)

theorem tupledEliminationSource_iff_not_minimalCutVertexBlockerExists :
    TupledBlockerEliminationSource <-> Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_tupledEliminationSource
  case mpr =>
    exact tupledEliminationSource_of_not_minimalCutVertexBlockerExists

theorem not_minimalCutVertexBlockerExists_of_deletionReinsertionEliminationSource
    (H : DeletionReinsertionEliminationSource) :
    Not MinimalCutVertexBlockerExists := by
  cases H with
  | inl Hclosed =>
      exact not_minimalCutVertexBlockerExists_of_closedDeletionReinsertionSource Hclosed
  | inr Hrest =>
      cases Hrest with
      | inl Hdirect =>
          exact not_minimalCutVertexBlockerExists_of_directDeletionReinsertionSource Hdirect
      | inr Hdeficient =>
          exact not_minimalCutVertexBlockerExists_of_deficientDeletionSource Hdeficient

theorem deletionReinsertionEliminationSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    DeletionReinsertionEliminationSource :=
  Or.inl (blockerTupledClosedSource_of_not_minimalCutVertexBlockerExists hno)

theorem deletionReinsertionEliminationSource_iff_not_minimalCutVertexBlockerExists :
    DeletionReinsertionEliminationSource <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_deletionReinsertionEliminationSource
  case mpr =>
    exact deletionReinsertionEliminationSource_of_not_minimalCutVertexBlockerExists

theorem not_minimalCutVertexBlockerExists_of_canonicalEliminationSource
    (H : CanonicalBlockerEliminationSource) :
    Not MinimalCutVertexBlockerExists := by
  cases H with
  | inl Hdegree =>
      exact not_minimalCutVertexBlockerExists_of_degreeDeletionSource Hdegree
  | inr Hrest =>
      cases Hrest with
      | inl Hclosed =>
          exact not_minimalCutVertexBlockerExists_of_blockerLocalClosed Hclosed
      | inr Hrest =>
          cases Hrest with
          | inl Hdirect =>
              exact not_minimalCutVertexBlockerExists_of_blockerDirectCard Hdirect
          | inr Hdeletion =>
              exact
                not_minimalCutVertexBlockerExists_of_deletionReinsertionEliminationSource
                  Hdeletion

theorem canonicalEliminationSource_of_not_minimalCutVertexBlockerExists
    (hno : Not MinimalCutVertexBlockerExists) :
    CanonicalBlockerEliminationSource :=
  Or.inl (blockerDegreeDeletionSource_of_not_minimalCutVertexBlockerExists hno)

theorem canonicalEliminationSource_iff_not_minimalCutVertexBlockerExists :
    CanonicalBlockerEliminationSource <-> Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    exact not_minimalCutVertexBlockerExists_of_canonicalEliminationSource
  case mpr =>
    exact canonicalEliminationSource_of_not_minimalCutVertexBlockerExists

end

end NoCutBlockerEliminationW30
end Swanepoel

namespace Verified

abbrev SwanepoelW30NoCutMinimalCutVertexBlockerExists : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.MinimalCutVertexBlockerExists

abbrev SwanepoelW30ClosedDeletionReinsertionSource : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.BlockerClosedDeletionReinsertionSource

abbrev SwanepoelW30DirectDeletionReinsertionSource : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.BlockerDirectDeletionReinsertionSource

abbrev SwanepoelW30DeficientDeletionSource : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.BlockerDeficientDeletionSource

abbrev SwanepoelW30TupledBlockerEliminationSource : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.TupledBlockerEliminationSource

abbrev SwanepoelW30DeletionReinsertionEliminationSource : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.DeletionReinsertionEliminationSource

abbrev SwanepoelW30CanonicalBlockerEliminationSource : Prop :=
  Swanepoel.NoCutBlockerEliminationW30.CanonicalBlockerEliminationSource

theorem swanepoelW30_closedDeletionReinsertionSource_exactly_noBlocker :
    SwanepoelW30ClosedDeletionReinsertionSource <->
      Not SwanepoelW30NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerEliminationW30.closedDeletionReinsertionSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW30_directDeletionReinsertionSource_exactly_noBlocker :
    SwanepoelW30DirectDeletionReinsertionSource <->
      Not SwanepoelW30NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerEliminationW30.directDeletionReinsertionSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW30_deficientDeletionSource_exactly_noBlocker :
    SwanepoelW30DeficientDeletionSource <->
      Not SwanepoelW30NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerEliminationW30.deficientDeletionSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW30_tupledEliminationSource_exactly_noBlocker :
    SwanepoelW30TupledBlockerEliminationSource <->
      Not SwanepoelW30NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerEliminationW30.tupledEliminationSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW30_deletionReinsertionEliminationSource_exactly_noBlocker :
    SwanepoelW30DeletionReinsertionEliminationSource <->
      Not SwanepoelW30NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerEliminationW30.deletionReinsertionEliminationSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW30_canonicalEliminationSource_exactly_noBlocker :
    SwanepoelW30CanonicalBlockerEliminationSource <->
      Not SwanepoelW30NoCutMinimalCutVertexBlockerExists :=
  Swanepoel.NoCutBlockerEliminationW30.canonicalEliminationSource_iff_not_minimalCutVertexBlockerExists

theorem swanepoelW30_closedDeletionReinsertionSource_reduces_to_degreeDeletionSource
    (H : SwanepoelW30ClosedDeletionReinsertionSource) :
    Swanepoel.NoCutBlockerEliminationW30.BlockerDegreeDeletionSource :=
  Swanepoel.NoCutBlockerEliminationW30.blockerDegreeDeletionSource_of_closedDeletionReinsertionSource
    H

theorem swanepoelW30_deficientDeletionSource_reduces_to_directDeletionReinsertionSource
    (H : SwanepoelW30DeficientDeletionSource) :
    SwanepoelW30DirectDeletionReinsertionSource :=
  Swanepoel.NoCutBlockerEliminationW30.directDeletionReinsertionSource_of_deficientDeletionSource
    H

end Verified
end ErdosProblems1066
