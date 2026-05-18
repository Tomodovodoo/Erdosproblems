import ErdosProblems1066.Swanepoel.RemainingFieldsAssemblyW21
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsGateW21

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W22 Swanepoel KnownBounds final gate

This file is the final W22 exposure wrapper for the Swanepoel `8 / 31` route.
It does not add an unconditional public `KnownBounds` theorem.  Instead it
routes the strongest assembled W21 source package into the W21 gate and records
the exact remaining shape of that gate.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelKnownBoundsFinalW22

noncomputable section

abbrev Target : Prop :=
  SwanepoelKnownBoundsGateW21.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelKnownBoundsGateW21.LowerBoundAt n C

abbrev KnownBoundsExposureGate : Prop :=
  SwanepoelKnownBoundsGateW21.KnownBoundsExposureGate

abbrev RemainingObligationFields : Type 1 :=
  SwanepoelKnownBoundsGateW21.RemainingObligationFields

abbrev PointwiseSourceFamilyFields : Type 1 :=
  SwanepoelKnownBoundsGateW21.PointwiseSourceFamilyFields

abbrev SourceComponents : Type 1 :=
  RemainingFieldsAssemblyW21.SourceComponents.{0}

/-! ## Minimal still-open source fields -/

abbrev StillOpenNoCut : Prop :=
  RemainingObligationLedgerW20.NoCutFamily

abbrev StillOpenTopologySource : Type 1 :=
  RemainingObligationLedgerW20.TopologySourceFamily.{0}

abbrev StillOpenLemma8
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource) : Type 1 :=
  RemainingObligationLedgerW20.Lemma8GeometryFieldFamily.{0}
    (RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily noCut)
    (RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
      topologySource)

abbrev StillOpenLemma9
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource)
    (lemma8 : StillOpenLemma8 noCut topologySource) : Type 1 :=
  RemainingObligationLedgerW20.Lemma9NatLateTripleCoverageFamily.{0}
    (RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily noCut)
    (RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
      topologySource)
    (RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily lemma8)

abbrev StillOpenFigures
    (noCut : StillOpenNoCut)
    (topologySource : StillOpenTopologySource)
    (lemma8 : StillOpenLemma8 noCut topologySource) : Type 1 :=
  RemainingObligationLedgerW20.FigureAngleBridgeFamily.{0}
    (RemainingObligationLedgerW20.payForCutProducerFamilyOfNoCutFamily noCut)
    (RemainingObligationLedgerW20.topologyArcProducerFamilyOfSource
      topologySource)
    (RemainingObligationLedgerW20.lemma8ProducerFamilyOfGeometryFamily lemma8)

structure MinimalStillOpenComponents : Type 1 where
  noCut : StillOpenNoCut
  topologySource : StillOpenTopologySource
  lemma8 : StillOpenLemma8 noCut topologySource
  lemma9 : StillOpenLemma9 noCut topologySource lemma8
  figures : StillOpenFigures noCut topologySource lemma8

namespace MinimalStillOpenComponents

def toSourceComponents
    (P : MinimalStillOpenComponents) : SourceComponents where
  noCut := P.noCut
  topologySource := P.topologySource
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

end MinimalStillOpenComponents

namespace SourceComponents

def toMinimalStillOpenComponents
    (P : SourceComponents) : MinimalStillOpenComponents where
  noCut := P.noCut
  topologySource := P.topologySource
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

end SourceComponents

theorem sourceComponents_nonempty_iff_minimalStillOpenComponents :
    Nonempty SourceComponents <-> Nonempty MinimalStillOpenComponents := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toMinimalStillOpenComponents
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toSourceComponents

/-! ## Exact gate shape -/

theorem remainingObligationFields_nonempty_iff_sourceComponents :
    Nonempty RemainingObligationFields <-> Nonempty SourceComponents :=
  RemainingFieldsAssemblyW21.remainingObligationFields_nonempty_iff_sourceComponents

theorem knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields :
    KnownBoundsExposureGate <->
      Nonempty SourceComponents \/ Nonempty PointwiseSourceFamilyFields := by
  constructor
  case mp =>
    intro H
    cases H with
    | inl hRemaining =>
        exact Or.inl
          (remainingObligationFields_nonempty_iff_sourceComponents.1
            hRemaining)
    | inr hPointwise =>
        exact Or.inr hPointwise
  case mpr =>
    intro H
    cases H with
    | inl hSource =>
        exact Or.inl
          (remainingObligationFields_nonempty_iff_sourceComponents.2
            hSource)
    | inr hPointwise =>
        exact Or.inr hPointwise

theorem knownBoundsExposureGate_of_sourceComponents
    (P : SourceComponents) :
    KnownBoundsExposureGate :=
  Or.inl
    (Nonempty.intro
      (RemainingFieldsAssemblyW21.remainingObligationFieldsOfSourceComponents
        P))

theorem knownBoundsExposureGate_of_nonempty_sourceComponents
    (h : Nonempty SourceComponents) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields.2
    (Or.inl h)

theorem targetLowerBoundEightThirtyOne_of_sourceComponents
    (P : SourceComponents) :
    Target :=
  SwanepoelKnownBoundsGateW21.targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    (knownBoundsExposureGate_of_sourceComponents P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents
    (h : Nonempty SourceComponents) :
    Target :=
  SwanepoelKnownBoundsGateW21.targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    (knownBoundsExposureGate_of_nonempty_sourceComponents h)

theorem lower_bound_eight_thirty_one_of_sourceComponents
    (P : SourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_sourceComponents P n C

theorem lower_bound_eight_thirty_one_of_nonempty_sourceComponents
    (h : Nonempty SourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents h n C

end

end SwanepoelKnownBoundsFinalW22

theorem lower_bound_eight_thirty_one_of_w22_sourceComponents
    (h :
      Nonempty
        SwanepoelKnownBoundsFinalW22.SourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelKnownBoundsFinalW22.LowerBoundAt n C :=
  SwanepoelKnownBoundsFinalW22.lower_bound_eight_thirty_one_of_nonempty_sourceComponents
    h n C

end Swanepoel

namespace Verified

abbrev SwanepoelW22RemainingSourceComponents : Type 1 :=
  Swanepoel.SwanepoelKnownBoundsFinalW22.SourceComponents

abbrev SwanepoelW22MinimalStillOpenComponents : Type 1 :=
  Swanepoel.SwanepoelKnownBoundsFinalW22.MinimalStillOpenComponents

theorem swanepoelW22_knownBoundsExposureGate_iff_sourceComponents_or_pointwise :
    Swanepoel.SwanepoelKnownBoundsFinalW22.KnownBoundsExposureGate <->
      Nonempty SwanepoelW22RemainingSourceComponents \/
        Nonempty
          Swanepoel.SwanepoelKnownBoundsFinalW22.PointwiseSourceFamilyFields :=
  Swanepoel.SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields

theorem swanepoelW22_sourceComponents_nonempty_iff_minimalStillOpenComponents :
    Nonempty SwanepoelW22RemainingSourceComponents <->
      Nonempty SwanepoelW22MinimalStillOpenComponents :=
  Swanepoel.SwanepoelKnownBoundsFinalW22.sourceComponents_nonempty_iff_minimalStillOpenComponents

theorem lower_bound_eight_thirty_one_of_swanepoel_w22_sourceComponents
    (h : Nonempty SwanepoelW22RemainingSourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelKnownBoundsFinalW22.lower_bound_eight_thirty_one_of_nonempty_sourceComponents
    h n C

end Verified
end ErdosProblems1066
