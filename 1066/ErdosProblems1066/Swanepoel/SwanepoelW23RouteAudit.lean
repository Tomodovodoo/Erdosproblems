import ErdosProblems1066.Swanepoel.RemainingSourceComponentsInhabitationW22
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsFinalW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 Swanepoel route audit

This module is an audit layer for the W22 Swanepoel route.  It records the
exact final exposure gate and the available source-package routes into it:

* W21/W22 source components;
* the W22 lane product;
* the minimal still-open component package;
* the independent pointwise source-family branch already present in the gate.

The pointwise branch remains visible in every iff for the final gate.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW23RouteAudit

noncomputable section

open SwanepoelKnownBoundsFinalW22

abbrev Target : Prop :=
  SwanepoelKnownBoundsFinalW22.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelKnownBoundsFinalW22.LowerBoundAt n C

abbrev FinalGate : Prop :=
  SwanepoelKnownBoundsFinalW22.KnownBoundsExposureGate

abbrev SourceComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.SourceComponents

abbrev LaneProduct : Type 1 :=
  RemainingSourceComponentsInhabitationW22.LaneProduct.{0}

abbrev MinimalStillOpenComponents : Type 1 :=
  SwanepoelKnownBoundsFinalW22.MinimalStillOpenComponents

abbrev RemainingObligationFields : Type 1 :=
  SwanepoelKnownBoundsFinalW22.RemainingObligationFields

abbrev PointwiseSourceFamilyFields : Type 1 :=
  SwanepoelKnownBoundsFinalW22.PointwiseSourceFamilyFields

abbrev SourceComponentsPackage : Prop :=
  Nonempty SourceComponents

abbrev LaneProductPackage : Prop :=
  Nonempty LaneProduct

abbrev MinimalStillOpenPackage : Prop :=
  Nonempty MinimalStillOpenComponents

abbrev PointwisePackage : Prop :=
  Nonempty PointwiseSourceFamilyFields

/-! ## Package equivalences -/

theorem remainingObligationFields_nonempty_iff_sourceComponents :
    Nonempty RemainingObligationFields <-> SourceComponentsPackage :=
  SwanepoelKnownBoundsFinalW22.remainingObligationFields_nonempty_iff_sourceComponents

theorem sourceComponents_nonempty_iff_minimalStillOpenComponents :
    SourceComponentsPackage <-> MinimalStillOpenPackage :=
  SwanepoelKnownBoundsFinalW22.sourceComponents_nonempty_iff_minimalStillOpenComponents

theorem sourceComponents_nonempty_of_laneProduct :
    LaneProductPackage -> SourceComponentsPackage :=
  RemainingSourceComponentsInhabitationW22.sourceComponents_nonempty_of_laneProduct

theorem minimalStillOpenComponents_nonempty_of_laneProduct
    (h : LaneProductPackage) :
    MinimalStillOpenPackage :=
  sourceComponents_nonempty_iff_minimalStillOpenComponents.1
    (sourceComponents_nonempty_of_laneProduct h)

/-! ## Final-gate audits -/

theorem finalGate_iff_sourceComponents_or_pointwise :
    FinalGate <-> SourceComponentsPackage \/ PointwisePackage :=
  knownBoundsExposureGate_iff_sourceComponents_or_pointwiseSourceFamilyFields

theorem finalGate_iff_minimalStillOpenComponents_or_pointwise :
    FinalGate <-> MinimalStillOpenPackage \/ PointwisePackage := by
  constructor
  case mp =>
    intro H
    cases (finalGate_iff_sourceComponents_or_pointwise.1 H) with
    | inl hSource =>
        exact Or.inl
          (sourceComponents_nonempty_iff_minimalStillOpenComponents.1
            hSource)
    | inr hPointwise =>
        exact Or.inr hPointwise
  case mpr =>
    intro H
    cases H with
    | inl hStillOpen =>
        exact
          finalGate_iff_sourceComponents_or_pointwise.2
            (Or.inl
              (sourceComponents_nonempty_iff_minimalStillOpenComponents.2
                hStillOpen))
    | inr hPointwise =>
        exact
          finalGate_iff_sourceComponents_or_pointwise.2
            (Or.inr hPointwise)

theorem finalGate_iff_sourceComponents_or_laneProduct_or_pointwise :
    FinalGate <->
      SourceComponentsPackage \/ LaneProductPackage \/ PointwisePackage := by
  constructor
  case mp =>
    intro H
    cases (finalGate_iff_sourceComponents_or_pointwise.1 H) with
    | inl hSource =>
        exact Or.inl hSource
    | inr hPointwise =>
        exact Or.inr (Or.inr hPointwise)
  case mpr =>
    intro H
    cases H with
    | inl hSource =>
        exact
          finalGate_iff_sourceComponents_or_pointwise.2
            (Or.inl hSource)
    | inr hRoute =>
        cases hRoute with
        | inl hLane =>
            exact
              finalGate_iff_sourceComponents_or_pointwise.2
                (Or.inl
                  (sourceComponents_nonempty_of_laneProduct hLane))
        | inr hPointwise =>
            exact
              finalGate_iff_sourceComponents_or_pointwise.2
                (Or.inr hPointwise)

theorem finalGate_of_sourceComponents
    (P : SourceComponents) :
    FinalGate :=
  SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_of_sourceComponents P

theorem finalGate_of_nonempty_sourceComponents
    (h : SourceComponentsPackage) :
    FinalGate :=
  SwanepoelKnownBoundsFinalW22.knownBoundsExposureGate_of_nonempty_sourceComponents
    h

theorem finalGate_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    FinalGate :=
  finalGate_iff_minimalStillOpenComponents_or_pointwise.2
    (Or.inl (Nonempty.intro P))

theorem finalGate_of_nonempty_minimalStillOpenComponents
    (h : MinimalStillOpenPackage) :
    FinalGate :=
  finalGate_iff_minimalStillOpenComponents_or_pointwise.2
    (Or.inl h)

theorem finalGate_of_laneProduct
    (P : LaneProduct) :
    FinalGate :=
  finalGate_iff_sourceComponents_or_pointwise.2
    (Or.inl
      (sourceComponents_nonempty_of_laneProduct
        (Nonempty.intro P)))

theorem finalGate_of_nonempty_laneProduct
    (h : LaneProductPackage) :
    FinalGate :=
  finalGate_iff_sourceComponents_or_pointwise.2
    (Or.inl (sourceComponents_nonempty_of_laneProduct h))

/-! ## Conditional lower-bound routes -/

theorem targetLowerBoundEightThirtyOne_of_sourceComponents
    (P : SourceComponents) :
    Target :=
  SwanepoelKnownBoundsFinalW22.targetLowerBoundEightThirtyOne_of_sourceComponents
    P

theorem targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents
    (h : SourceComponentsPackage) :
    Target :=
  SwanepoelKnownBoundsFinalW22.targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents
    h

theorem targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents) :
    Target :=
  SwanepoelKnownBoundsGateW21.targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    (finalGate_of_minimalStillOpenComponents P)

theorem targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents
    (h : MinimalStillOpenPackage) :
    Target :=
  SwanepoelKnownBoundsGateW21.targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    (finalGate_of_nonempty_minimalStillOpenComponents h)

theorem targetLowerBoundEightThirtyOne_of_laneProduct
    (P : LaneProduct) :
    Target :=
  RemainingSourceComponentsInhabitationW22.targetLowerBoundEightThirtyOne_of_laneProduct
    P

theorem targetLowerBoundEightThirtyOne_of_nonempty_laneProduct
    (h : LaneProductPackage) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_laneProduct P

theorem lower_bound_eight_thirty_one_of_sourceComponents
    (P : SourceComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_sourceComponents P n C

theorem lower_bound_eight_thirty_one_of_nonempty_sourceComponents
    (h : SourceComponentsPackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_sourceComponents h n C

theorem lower_bound_eight_thirty_one_of_minimalStillOpenComponents
    (P : MinimalStillOpenComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents P n C

theorem lower_bound_eight_thirty_one_of_nonempty_minimalStillOpenComponents
    (h : MinimalStillOpenPackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_minimalStillOpenComponents h n C

theorem lower_bound_eight_thirty_one_of_laneProduct
    (P : LaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_laneProduct P n C

theorem lower_bound_eight_thirty_one_of_nonempty_laneProduct
    (h : LaneProductPackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_laneProduct h n C

end

end SwanepoelW23RouteAudit
end Swanepoel

namespace Verified

abbrev SwanepoelW23FinalGate : Prop :=
  Swanepoel.SwanepoelW23RouteAudit.FinalGate

abbrev SwanepoelW23RouteSourceComponents : Type 1 :=
  Swanepoel.SwanepoelW23RouteAudit.SourceComponents

abbrev SwanepoelW23RouteLaneProduct : Type 1 :=
  Swanepoel.SwanepoelW23RouteAudit.LaneProduct

abbrev SwanepoelW23RouteMinimalStillOpenComponents : Type 1 :=
  Swanepoel.SwanepoelW23RouteAudit.MinimalStillOpenComponents

abbrev SwanepoelW23RoutePointwiseSourceFamilyFields : Type 1 :=
  Swanepoel.SwanepoelW23RouteAudit.PointwiseSourceFamilyFields

theorem swanepoel_w23_finalGate_iff_sourceComponents_or_pointwise :
    SwanepoelW23FinalGate <->
      Nonempty SwanepoelW23RouteSourceComponents \/
        Nonempty SwanepoelW23RoutePointwiseSourceFamilyFields :=
  Swanepoel.SwanepoelW23RouteAudit.finalGate_iff_sourceComponents_or_pointwise

theorem swanepoel_w23_finalGate_iff_minimalStillOpen_or_pointwise :
    SwanepoelW23FinalGate <->
      Nonempty SwanepoelW23RouteMinimalStillOpenComponents \/
        Nonempty SwanepoelW23RoutePointwiseSourceFamilyFields :=
  Swanepoel.SwanepoelW23RouteAudit.finalGate_iff_minimalStillOpenComponents_or_pointwise

theorem swanepoel_w23_finalGate_iff_sourceComponents_or_laneProduct_or_pointwise :
    SwanepoelW23FinalGate <->
      Nonempty SwanepoelW23RouteSourceComponents \/
        Nonempty SwanepoelW23RouteLaneProduct \/
          Nonempty SwanepoelW23RoutePointwiseSourceFamilyFields :=
  Swanepoel.SwanepoelW23RouteAudit.finalGate_iff_sourceComponents_or_laneProduct_or_pointwise

theorem swanepoel_w23_sourceComponents_nonempty_of_laneProduct :
    Nonempty SwanepoelW23RouteLaneProduct ->
      Nonempty SwanepoelW23RouteSourceComponents :=
  Swanepoel.SwanepoelW23RouteAudit.sourceComponents_nonempty_of_laneProduct

theorem swanepoel_w23_finalGate_of_laneProduct
    (P : SwanepoelW23RouteLaneProduct) :
    SwanepoelW23FinalGate :=
  Swanepoel.SwanepoelW23RouteAudit.finalGate_of_laneProduct P

theorem lower_bound_eight_thirty_one_of_swanepoel_w23_route_laneProduct
    (P : SwanepoelW23RouteLaneProduct)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW23RouteAudit.lower_bound_eight_thirty_one_of_laneProduct
    P n C

end Verified
end ErdosProblems1066
