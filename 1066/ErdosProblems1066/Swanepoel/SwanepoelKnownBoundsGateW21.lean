import ErdosProblems1066.KnownBounds
import ErdosProblems1066.Swanepoel.PointwiseProducerFamilyFieldsW20
import ErdosProblems1066.Swanepoel.RemainingObligationLedgerW20

set_option autoImplicit false

/-!
# W21 Swanepoel KnownBounds gate

This file records the exact conditional bridge needed before `KnownBounds` can
expose Swanepoel's `8 / 31` lower bound in the public facade shape.

The bridge remains conditional: it consumes inhabitants of one of the current
W20 field packages, and therefore does not assert an unconditional public
Swanepoel theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelKnownBoundsGateW21

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  Exists fun s : Finset (Fin n) =>
    C.IsIndep s /\ 31 * s.card >= 8 * n

abbrev RemainingObligationFields : Type 1 :=
  RemainingObligationLedgerW20.RemainingObligationFields.{0}

abbrev PointwiseSourceFamilyFields : Type 1 :=
  PointwiseProducerFamilyFieldsW20.PointwiseSourceFamilyFields.{0}

/-- The internal proposition `KnownBounds` must get from the Swanepoel pipeline
before it can expose an unconditional `8 / 31` lower-bound wrapper. -/
abbrev KnownBoundsExposureGate : Prop :=
  Nonempty RemainingObligationFields \/ Nonempty PointwiseSourceFamilyFields

/-! ## Direct field routes -/

theorem targetLowerBoundEightThirtyOne_of_remainingObligationFields
    (P : RemainingObligationFields) :
    Target :=
  RemainingObligationLedgerW20.targetLowerBoundEightThirtyOne_of_remainingObligationFields
    P

theorem lower_bound_eight_thirty_one_of_remainingObligationFields
    (P : RemainingObligationFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_remainingObligationFields P n C

theorem targetLowerBoundEightThirtyOne_of_pointwiseSourceFamilyFields
    (P : PointwiseSourceFamilyFields) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_pointwiseSourceFamilyFields
    (P : PointwiseSourceFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_pointwiseSourceFamilyFields P n C

/-! ## Inhabited-field gate routes -/

theorem targetLowerBoundEightThirtyOne_of_nonempty_remainingObligationFields
    (h : Nonempty RemainingObligationFields) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_remainingObligationFields P

theorem lower_bound_eight_thirty_one_of_nonempty_remainingObligationFields
    (h : Nonempty RemainingObligationFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_remainingObligationFields h n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_pointwiseSourceFamilyFields
    (h : Nonempty PointwiseSourceFamilyFields) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_pointwiseSourceFamilyFields P

theorem lower_bound_eight_thirty_one_of_nonempty_pointwiseSourceFamilyFields
    (h : Nonempty PointwiseSourceFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_pointwiseSourceFamilyFields h n C

/-- The single W21 gate theorem: an inhabitant of either current W20 field
package gives the `KnownBounds`-shaped Swanepoel `8 / 31` lower bound. -/
theorem targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate
    (H : KnownBoundsExposureGate) :
    Target := by
  cases H with
  | inl hRemaining =>
      exact targetLowerBoundEightThirtyOne_of_nonempty_remainingObligationFields
        hRemaining
  | inr hPointwise =>
      exact targetLowerBoundEightThirtyOne_of_nonempty_pointwiseSourceFamilyFields
        hPointwise

/-- KnownBounds-shaped conditional endpoint for Swanepoel `8 / 31`.

To make this theorem unconditional in `KnownBounds`, the remaining internal
obligation is exactly `KnownBoundsExposureGate`.
-/
theorem lower_bound_eight_thirty_one_of_knownBoundsExposureGate
    (H : KnownBoundsExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_knownBoundsExposureGate H n C

end

end SwanepoelKnownBoundsGateW21

theorem lower_bound_eight_thirty_one_of_w21_remainingObligationFields
    (h : Nonempty SwanepoelKnownBoundsGateW21.RemainingObligationFields)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelKnownBoundsGateW21.LowerBoundAt n C :=
  SwanepoelKnownBoundsGateW21.lower_bound_eight_thirty_one_of_nonempty_remainingObligationFields
    h n C

theorem lower_bound_eight_thirty_one_of_w21_pointwiseSourceFamilyFields
    (h : Nonempty SwanepoelKnownBoundsGateW21.PointwiseSourceFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelKnownBoundsGateW21.LowerBoundAt n C :=
  SwanepoelKnownBoundsGateW21.lower_bound_eight_thirty_one_of_nonempty_pointwiseSourceFamilyFields
    h n C

theorem lower_bound_eight_thirty_one_of_w21_knownBoundsExposureGate
    (H : SwanepoelKnownBoundsGateW21.KnownBoundsExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    SwanepoelKnownBoundsGateW21.LowerBoundAt n C :=
  SwanepoelKnownBoundsGateW21.lower_bound_eight_thirty_one_of_knownBoundsExposureGate
    H n C

end Swanepoel

namespace Verified

abbrev SwanepoelW21KnownBoundsExposureGate : Prop :=
  Swanepoel.SwanepoelKnownBoundsGateW21.KnownBoundsExposureGate

/-- Public-facade-shaped conditional Swanepoel `8 / 31` lower bound. -/
theorem lower_bound_eight_thirty_one_of_swanepoel_w21_knownBoundsExposureGate
    (H : SwanepoelW21KnownBoundsExposureGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.lower_bound_eight_thirty_one_of_w21_knownBoundsExposureGate
    H n C

end Verified
end ErdosProblems1066
