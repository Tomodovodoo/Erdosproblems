import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.LargeTailClosedPlacementRowsW32

set_option autoImplicit false

/-!
# W34 eventual closed-placement source bridge

W31/W32 expose honest threshold-six closed-placement rows.  This file records
the direct handoff from those rows to the W12 eventual closed-placement source:
checked tail placements for every `k >= 6` are exactly large explicit
closed-placement certificates with threshold `6`.

The constructions below only forget structure from existing source-side row
packages; they do not use the Pach--Toth target theorem as input.
-/

namespace ErdosProblems1066
namespace PachToth
namespace EventualClosedPlacementSourceW34

open FiniteGraph
open LargeTailClosedPlacementRowsW32

noncomputable section

abbrev LargeExplicitClosedPlacementCertificates (K0 : Nat) : Type :=
  LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0

abbrev LargeExactBlockTargetsFromSix : Prop :=
  LargeTailExactSourceW28.RemainingPositiveExactChainBlocker

abbrev LargeTailClosedPlacementRows : Type :=
  LargeTailRowsRealizationW31.LargeTailClosedPlacementRows

abbrev LargeTailConcreteRowFields : Type :=
  LargeTailClosedPlacementRowsW32.LargeTailConcreteRowFields

abbrev LargeTailGeneratedClosureSeparationFields : Type :=
  LargeTailClosedPlacementRowsW32.LargeTailGeneratedClosureSeparationFields

abbrev ConcreteCrossBlockFamily : Type :=
  ConcretePeriodSearchFamily.ConcreteCrossBlockFamily

abbrev RoleHingedPeriodSearchCrossBlockFamily : Type :=
  ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily

/-- Forget a checked deformed closed placement to the coordinate-level
certificate consumed by W12. -/
def explicitClosedPlacementCertificateOfClosedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk where
  point := P.point
  separated := P.separated
  same_block_edges_unit := P.same_block_edges_unit
  cross_connector_edges_unit := P.cross_connector_edges_unit

@[simp]
theorem explicitClosedPlacementCertificateOfClosedPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (explicitClosedPlacementCertificateOfClosedPlacement P).point i v =
      P.point i v := by
  rfl

/-- Threshold-six closed-placement rows are precisely a positive large-`k`
explicit closed-placement source for W12. -/
def largeExplicitClosedPlacementCertificatesOfClosedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeExplicitClosedPlacementCertificates 6 where
  certificate := fun k hkSix hk =>
    explicitClosedPlacementCertificateOfClosedPlacement
      (H.placement k hkSix hk)

theorem targetUpperConstructionFiveSixteenEventually_of_closedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    (largeExplicitClosedPlacementCertificatesOfClosedPlacementRows H)
      |>.targetUpperConstructionFiveSixteenEventually

theorem largeExactBlockTargetsFromSix_of_largeExplicitClosedPlacementCertificatesSix
    (L : LargeExplicitClosedPlacementCertificates 6) :
    LargeExactBlockTargetsFromSix :=
  LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    L

theorem largeExactBlockTargetsFromSix_of_closedPlacementRows
    (H : LargeTailClosedPlacementRows) :
    LargeExactBlockTargetsFromSix :=
  largeExactBlockTargetsFromSix_of_largeExplicitClosedPlacementCertificatesSix
    (largeExplicitClosedPlacementCertificatesOfClosedPlacementRows H)

/-- Nonempty tail rows give a nonempty threshold-six large explicit source. -/
theorem nonempty_largeExplicitClosedPlacementCertificates_six_of_closedPlacementRows
    (H : Nonempty LargeTailClosedPlacementRows) :
    Nonempty (LargeExplicitClosedPlacementCertificates 6) := by
  cases H with
  | intro rows =>
      exact
        Nonempty.intro
          (largeExplicitClosedPlacementCertificatesOfClosedPlacementRows rows)

/-- W32 concrete row fields provide the same threshold-six W12 source. -/
def largeExplicitClosedPlacementCertificatesOfConcreteRowFields
    (R : LargeTailConcreteRowFields) :
    LargeExplicitClosedPlacementCertificates 6 :=
  largeExplicitClosedPlacementCertificatesOfClosedPlacementRows
    R.closedPlacementRows

/-- Generated closure plus generated global separation, from threshold six
onward, is an exact missing-field theorem for the W12 large source. -/
def largeExplicitClosedPlacementCertificatesOfGeneratedClosureSeparationFields
    (G : LargeTailGeneratedClosureSeparationFields) :
    LargeExplicitClosedPlacementCertificates 6 :=
  largeExplicitClosedPlacementCertificatesOfClosedPlacementRows
    G.closedPlacementRows

theorem targetUpperConstructionFiveSixteenEventually_of_generatedClosureSeparationFields
    (G : LargeTailGeneratedClosureSeparationFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    (largeExplicitClosedPlacementCertificatesOfGeneratedClosureSeparationFields G)
      |>.targetUpperConstructionFiveSixteenEventually

theorem largeExactBlockTargetsFromSix_of_concreteRowFields
    (R : LargeTailConcreteRowFields) :
    LargeExactBlockTargetsFromSix :=
  largeExactBlockTargetsFromSix_of_closedPlacementRows R.closedPlacementRows

theorem largeExactBlockTargetsFromSix_of_generatedClosureSeparationFields
    (G : LargeTailGeneratedClosureSeparationFields) :
    LargeExactBlockTargetsFromSix :=
  largeExactBlockTargetsFromSix_of_closedPlacementRows G.closedPlacementRows

/-- Period-search/cross-block source data supplies the threshold-six W12 large
closed-placement source. -/
def largeExplicitClosedPlacementCertificatesOfPeriodSearchCrossBlockSource
    (F : RoleHingedPeriodSearchCrossBlockFamily) :
    LargeExplicitClosedPlacementCertificates 6 :=
  largeExplicitClosedPlacementCertificatesOfGeneratedClosureSeparationFields
    (generatedClosureSeparationFieldsOfPeriodSearchCrossBlockSource F)

/-- The concrete period-search cross-block family supplies the same threshold. -/
def largeExplicitClosedPlacementCertificatesOfConcretePeriodSearchCrossBlockFamily
    (F : ConcreteCrossBlockFamily) :
    LargeExplicitClosedPlacementCertificates 6 :=
  largeExplicitClosedPlacementCertificatesOfGeneratedClosureSeparationFields
    (generatedClosureSeparationFieldsOfConcretePeriodSearchCrossBlockFamily F)

theorem nonempty_largeExplicitClosedPlacementCertificates_six_of_concreteRowFields
    (H : Nonempty LargeTailConcreteRowFields) :
    Nonempty (LargeExplicitClosedPlacementCertificates 6) := by
  cases H with
  | intro R =>
      exact
        Nonempty.intro
          (largeExplicitClosedPlacementCertificatesOfConcreteRowFields R)

theorem nonempty_largeExplicitClosedPlacementCertificates_six_of_generatedClosureSeparationFields
    (H : Nonempty LargeTailGeneratedClosureSeparationFields) :
    Nonempty (LargeExplicitClosedPlacementCertificates 6) := by
  cases H with
  | intro G =>
      exact
        Nonempty.intro
          (largeExplicitClosedPlacementCertificatesOfGeneratedClosureSeparationFields
            G)

theorem nonempty_largeExplicitClosedPlacementCertificates_six_of_periodSearchCrossBlockSource
    (H : Nonempty RoleHingedPeriodSearchCrossBlockFamily) :
    Nonempty (LargeExplicitClosedPlacementCertificates 6) := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (largeExplicitClosedPlacementCertificatesOfPeriodSearchCrossBlockSource
            F)

theorem nonempty_largeExplicitClosedPlacementCertificates_six_of_concreteCrossBlockFamily
    (H : Nonempty ConcreteCrossBlockFamily) :
    Nonempty (LargeExplicitClosedPlacementCertificates 6) := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (largeExplicitClosedPlacementCertificatesOfConcretePeriodSearchCrossBlockFamily
            F)

theorem largeExactBlockTargetsFromSix_of_periodSearchCrossBlockSource
    (F : RoleHingedPeriodSearchCrossBlockFamily) :
    LargeExactBlockTargetsFromSix :=
  largeExactBlockTargetsFromSix_of_generatedClosureSeparationFields
    (generatedClosureSeparationFieldsOfPeriodSearchCrossBlockSource F)

theorem largeExactBlockTargetsFromSix_of_concreteCrossBlockFamily
    (F : ConcreteCrossBlockFamily) :
    LargeExactBlockTargetsFromSix :=
  largeExactBlockTargetsFromSix_of_generatedClosureSeparationFields
    (generatedClosureSeparationFieldsOfConcretePeriodSearchCrossBlockFamily F)

end

end EventualClosedPlacementSourceW34
end PachToth

namespace Verified

open PachToth.EventualClosedPlacementSourceW34

abbrev PachTothW34LargeExplicitClosedPlacementCertificatesSix : Type :=
  LargeExplicitClosedPlacementCertificates 6

abbrev PachTothW34LargeTailClosedPlacementRows : Type :=
  LargeTailClosedPlacementRows

abbrev PachTothW34LargeTailGeneratedClosureSeparationFields : Type :=
  LargeTailGeneratedClosureSeparationFields

noncomputable def pachtoth_w34_largeSourceSix_of_closedPlacementRows
    (H : PachTothW34LargeTailClosedPlacementRows) :
    PachTothW34LargeExplicitClosedPlacementCertificatesSix :=
  largeExplicitClosedPlacementCertificatesOfClosedPlacementRows H

noncomputable def pachtoth_w34_largeSourceSix_of_generatedClosureSeparationFields
    (G : PachTothW34LargeTailGeneratedClosureSeparationFields) :
    PachTothW34LargeExplicitClosedPlacementCertificatesSix :=
  largeExplicitClosedPlacementCertificatesOfGeneratedClosureSeparationFields G

end Verified
end ErdosProblems1066
