import ErdosProblems1066.Swanepoel.RemainingSourceComponentsInhabitationW22
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsFinalW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 Swanepoel KnownBounds from lanes

This file exposes the strongest checked W23 Swanepoel endpoint available from
W22 lane and source-component packages.  The endpoint remains conditional: a
lane product or source-component package yields the `8 / 31` lower-bound shape,
and the exact exposure gate is still the minimal source package or the
pointwise source-family package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelKnownBoundsFromLanesW23

noncomputable section

abbrev Target : Prop :=
  SwanepoelKnownBoundsFinalW22.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelKnownBoundsFinalW22.LowerBoundAt n C

abbrev KnownBoundsExposureGate : Prop :=
  SwanepoelKnownBoundsFinalW22.KnownBoundsExposureGate

abbrev LaneProduct : Type 1 :=
  RemainingSourceComponentsInhabitationW22.LaneProduct.{0}

abbrev SourceComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.SourceComponents

abbrev MinimalStillOpenComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.MinimalStillOpenComponents

abbrev PointwiseSourceFamilyFields : Type 1 :=
  SwanepoelKnownBoundsFinalW22.PointwiseSourceFamilyFields

abbrev RemainingObligationFields : Type 1 :=
  SwanepoelKnownBoundsFinalW22.RemainingObligationFields

/-! ## Lane product to source components -/

def sourceComponentsOfLaneProduct
    (P : LaneProduct) : SourceComponents :=
  P.toSourceComponents

def remainingObligationFieldsOfLaneProduct
    (P : LaneProduct) : RemainingObligationFields :=
  P.toRemainingObligationFields

def minimalStillOpenComponentsOfLaneProduct
    (P : LaneProduct) : MinimalStillOpenComponents :=
  SwanepoelKnownBoundsFinalW22.SourceComponents.toMinimalStillOpenComponents
    (sourceComponentsOfLaneProduct P)

theorem sourceComponents_nonempty_of_laneProduct :
    Nonempty LaneProduct -> Nonempty SourceComponents :=
  RemainingSourceComponentsInhabitationW22.sourceComponents_nonempty_of_laneProduct

theorem remainingObligationFields_nonempty_of_laneProduct :
    Nonempty LaneProduct -> Nonempty RemainingObligationFields :=
  RemainingSourceComponentsInhabitationW22.remainingObligationFields_nonempty_of_laneProduct

theorem minimalStillOpenComponents_nonempty_of_laneProduct
    (h : Nonempty LaneProduct) :
    Nonempty MinimalStillOpenComponents :=
  SwanepoelKnownBoundsFinalW22.sourceComponents_nonempty_iff_minimalStillOpenComponents.1
    (sourceComponents_nonempty_of_laneProduct h)

/-! ## Exact exposure-gate shape -/

theorem sourceComponents_nonempty_iff_minimalStillOpenComponents :
    Nonempty SourceComponents <-> Nonempty MinimalStillOpenComponents :=
  SwanepoelKnownBoundsFinalW22.sourceComponents_nonempty_iff_minimalStillOpenComponents

theorem knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields :
    KnownBoundsExposureGate <->
      Nonempty SourceComponents \/ Nonempty PointwiseSourceFamilyFields :=
  SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields

theorem knownBoundsExposureGate_iff_minimalStillOpenComponents_or_pointwiseSourceFamilyFields :
    KnownBoundsExposureGate <->
      Nonempty MinimalStillOpenComponents \/
        Nonempty PointwiseSourceFamilyFields := by
  constructor
  case mp =>
    intro H
    cases knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields.1 H with
    | inl hSource =>
        exact Or.inl
          (sourceComponents_nonempty_iff_minimalStillOpenComponents.1 hSource)
    | inr hPointwise =>
        exact Or.inr hPointwise
  case mpr =>
    intro H
    cases H with
    | inl hMinimal =>
        exact
          knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields.2
            (Or.inl
              (sourceComponents_nonempty_iff_minimalStillOpenComponents.2 hMinimal))
    | inr hPointwise =>
        exact
          knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields.2
            (Or.inr hPointwise)

theorem knownBoundsExposureGate_of_laneProduct
    (P : LaneProduct) :
    KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_of_sourceComponents
    (sourceComponentsOfLaneProduct P)

theorem knownBoundsExposureGate_of_nonempty_laneProduct
    (h : Nonempty LaneProduct) :
    KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_of_nonempty_sourceComponents
    (sourceComponents_nonempty_of_laneProduct h)

theorem knownBoundsExposureGate_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_of_sourceComponents
    (P.toSourceComponents)

theorem knownBoundsExposureGate_of_nonempty_minimalStillOpenComponents
    (h : Nonempty MinimalStillOpenComponents) :
    KnownBoundsExposureGate :=
  knownBoundsExposureGate_iff_minimalStillOpenComponents_or_pointwiseSourceFamilyFields.2
    (Or.inl h)

/-! ## Conditional lower-bound endpoints -/

theorem targetLowerBoundEightThirtyOne_of_sourceComponents
    (P : SourceComponents) :
    Target :=
  SwanepoelKnownBoundsFinalW22.targetLowerBoundEightThirtyOne_of_sourceComponents P

theorem targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents
    (h : Nonempty SourceComponents) :
    Target :=
  SwanepoelKnownBoundsFinalW22.targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents h

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : LaneProduct) :
    Target :=
  targetLowerBoundEightThirtyOne_of_sourceComponents
    (sourceComponentsOfLaneProduct P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_laneProduct
    (h : Nonempty LaneProduct) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_laneProduct P

theorem targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_sourceComponents P.toSourceComponents

theorem targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents
    (h : Nonempty MinimalStillOpenComponents) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents P

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

theorem lower_bound_eight_thirty_one_of_laneProduct
    (P : LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_nonempty_laneProduct
    (h : Nonempty LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_laneProduct h n C

theorem lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents P n C

theorem lower_bound_eight_thirty_one_of_nonempty_minimalStillOpenComponents
    (h : Nonempty MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents h n C

end

end SwanepoelKnownBoundsFromLanesW23

theorem lower_bound_eight_thirty_one_of_w23_laneProduct
    (h : Nonempty SwanepoelKnownBoundsFromLanesW23.LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelKnownBoundsFromLanesW23.LowerBoundAt n C :=
  SwanepoelKnownBoundsFromLanesW23.lower_bound_eight_thirty_one_of_nonempty_laneProduct
    h n C

theorem lower_bound_eight_thirty_one_of_w23_sourceComponents
    (h : Nonempty SwanepoelKnownBoundsFromLanesW23.SourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelKnownBoundsFromLanesW23.LowerBoundAt n C :=
  SwanepoelKnownBoundsFromLanesW23.lower_bound_eight_thirty_one_of_nonempty_sourceComponents
    h n C

end Swanepoel

namespace Verified

abbrev SwanepoelW23RemainingLaneProduct : Type 1 :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.LaneProduct

abbrev SwanepoelW23RemainingSourceComponents : Type 1 :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.SourceComponents

abbrev SwanepoelW23MinimalStillOpenComponents : Type 1 :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.MinimalStillOpenComponents

abbrev SwanepoelW23KnownBoundsExposureGate : Prop :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.KnownBoundsExposureGate

theorem swanepoelW23_knownBoundsExposureGate_iff_minimalStillOpenComponents_or_pointwise :
    SwanepoelW23KnownBoundsExposureGate <->
      Nonempty SwanepoelW23MinimalStillOpenComponents \/
        Nonempty
          Swanepoel.SwanepoelKnownBoundsFromLanesW23.PointwiseSourceFamilyFields :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_iff_minimalStillOpenComponents_or_pointwiseSourceFamilyFields

theorem swanepoelW23_sourceComponents_nonempty_of_laneProduct :
    Nonempty SwanepoelW23RemainingLaneProduct ->
      Nonempty SwanepoelW23RemainingSourceComponents :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.sourceComponents_nonempty_of_laneProduct

theorem lower_bound_eight_thirty_one_of_swanepoel_w23_laneProduct
    (h : Nonempty SwanepoelW23RemainingLaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.lower_bound_eight_thirty_one_of_nonempty_laneProduct
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoel_w23_sourceComponents
    (h : Nonempty SwanepoelW23RemainingSourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelKnownBoundsFromLanesW23.lower_bound_eight_thirty_one_of_nonempty_sourceComponents
    h n C

end Verified
end ErdosProblems1066
