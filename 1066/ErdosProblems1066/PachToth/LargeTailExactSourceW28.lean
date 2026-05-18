import ErdosProblems1066.PachToth.ClosedPlacementKnownBoundsGateW21
import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.LargeKClosedPlacementSourceW20
import ErdosProblems1066.PachToth.PositiveExactLargeTailW27

set_option autoImplicit false

/-!
# W28 large-tail exact source package

This worker sharpens the W27 large-tail route.  W27 already showed that
threshold-six large closed-placement fields imply the large exact-block tail.
Here the source object is made explicit: it stores the actual
closed-placement certificates available from block count six onward and
derives the tail through `ExactChainUpper`.

No theorem in this file constructs a source package from the Pach--Toth target
statement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeTailExactSourceW28

noncomputable section

abbrev ExactChainUpper (k : Nat) : Type :=
  PositiveExactChainPackageW26.ExactChainUpper k

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainPackageW26.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainPackageW26.RemainingPositiveExactChainBlocker

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields 6

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev W20SourceFields : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev W21SourceFields : Type :=
  ClosedPlacementKnownBoundsGateW21.SourceFields

abbrev W21KnownBoundsGate : Prop :=
  ClosedPlacementKnownBoundsGateW21.KnownBoundsGate

abbrev ExplicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) : Type :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

abbrev LargeTailCertificateFamily : Type :=
  forall (k : Nat), 6 <= k -> forall hk : 0 < k,
    ExplicitClosedPlacementCertificate k hk

/-! ## Source package -/

/-- Actual large-tail source data: explicit closed-placement certificates for
every block count `k >= 6`. -/
structure LargeTailExactSourcePackage where
  certificates : LargeTailCertificateFamily

namespace LargeTailExactSourcePackage

def toLargeClosedPlacementFields
    (P : LargeTailExactSourcePackage) :
    LargeClosedPlacementFieldsFromSix where
  certificate := P.certificates

def exactChainUpper
    (P : LargeTailExactSourcePackage)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    ExactChainUpper k :=
  LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates.exactChainUpper
    P.toLargeClosedPlacementFields k hkSix hk

def exactChainTailFromSix
    (P : LargeTailExactSourcePackage) :
    forall k : Nat, 6 <= k -> ExactChainUpper k := by
  intro k hkSix
  have hk : 0 < k := by omega
  exact P.exactChainUpper k hkSix hk

theorem remainingBlocker
    (P : LargeTailExactSourcePackage) :
    RemainingPositiveExactChainBlocker :=
  PositiveExactLargeTailW27.remainingBlocker_of_exactChainTailFromSix
    P.exactChainTailFromSix

def positiveExactChainPackage
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    PositiveExactChainPackage :=
  PositiveExactChainPackageW26.packageOfSmallAndLargeExactBlockTargets
    { small := small
      large := P.remainingBlocker }

end LargeTailExactSourcePackage

/-! ## Constructors from available certificate surfaces -/

def packageOfLargeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeTailExactSourcePackage where
  certificates := L.certificate

@[simp]
theorem packageOfLargeClosedPlacementFieldsFromSix_toLargeClosedPlacementFields
    (L : LargeClosedPlacementFieldsFromSix) :
    (packageOfLargeClosedPlacementFieldsFromSix L).toLargeClosedPlacementFields =
      L := by
  rfl

def largeClosedPlacementFieldsFromSixOfCertificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    LargeClosedPlacementFieldsFromSix where
  certificate := fun k _hkSix hk => C k hk

def packageOfCertificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    LargeTailExactSourcePackage :=
  packageOfLargeClosedPlacementFieldsFromSix
    (largeClosedPlacementFieldsFromSixOfCertificateFamily C)

def packageOfW19InputPackage
    (P : W19InputPackage) :
    LargeTailExactSourcePackage :=
  packageOfCertificateFamily
    (ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate P)

def packageOfW20SourceFields
    (S : W20SourceFields) :
    LargeTailExactSourcePackage :=
  packageOfW19InputPackage S.toInputPackage

def packageOfW21SourceFields
    (S : W21SourceFields) :
    LargeTailExactSourcePackage :=
  packageOfW19InputPackage
    (ClosedPlacementKnownBoundsGateW21.inputPackageOfSourceFields S)

def packageOfW21KnownBoundsGate
    (G : W21KnownBoundsGate) :
    LargeTailExactSourcePackage :=
  packageOfW21SourceFields
    (ClosedPlacementKnownBoundsGateW21.sourceFieldsOfGate G)

def packageOfW19InputPackageAsLargeFields
    (P : W19InputPackage) :
    LargeTailExactSourcePackage :=
  packageOfLargeClosedPlacementFieldsFromSix
    (LargeKClosedPlacementSourceW20.largeClosedPlacementFieldsOfInputPackage
      6 P)

@[simp]
theorem packageOfW19InputPackage_certificates
    (P : W19InputPackage)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    (packageOfW19InputPackage P).certificates k hkSix hk =
      ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
        P k hk := by
  rfl

@[simp]
theorem packageOfW19InputPackageAsLargeFields_certificates
    (P : W19InputPackage)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    (packageOfW19InputPackageAsLargeFields P).certificates k hkSix hk =
      ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
        P k hk := by
  rfl

/-! ## Exact-tail consequences -/

theorem remainingBlocker_of_largeTailExactSourcePackage
    (P : LargeTailExactSourcePackage) :
    RemainingPositiveExactChainBlocker :=
  P.remainingBlocker

theorem remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    RemainingPositiveExactChainBlocker :=
  (packageOfLargeClosedPlacementFieldsFromSix L).remainingBlocker

theorem remainingBlocker_of_certificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    RemainingPositiveExactChainBlocker :=
  (packageOfCertificateFamily C).remainingBlocker

theorem remainingBlocker_of_w19InputPackage
    (P : W19InputPackage) :
    RemainingPositiveExactChainBlocker :=
  (packageOfW19InputPackage P).remainingBlocker

theorem remainingBlocker_of_w20SourceFields
    (S : W20SourceFields) :
    RemainingPositiveExactChainBlocker :=
  (packageOfW20SourceFields S).remainingBlocker

theorem remainingBlocker_of_w21SourceFields
    (S : W21SourceFields) :
    RemainingPositiveExactChainBlocker :=
  (packageOfW21SourceFields S).remainingBlocker

theorem remainingBlocker_of_w21KnownBoundsGate
    (G : W21KnownBoundsGate) :
    RemainingPositiveExactChainBlocker :=
  (packageOfW21KnownBoundsGate G).remainingBlocker

theorem nonempty_positiveExactChainPackage_of_largeTailSource_and_smallBlocks
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    Nonempty PositiveExactChainPackage :=
  Nonempty.intro (P.positiveExactChainPackage small)

theorem nonempty_positiveExactChainPackage_of_largeClosedPlacementFields_and_smallBlocks
    (L : LargeClosedPlacementFieldsFromSix)
    (small : ExactBlocksOneThroughFive) :
    Nonempty PositiveExactChainPackage :=
  nonempty_positiveExactChainPackage_of_largeTailSource_and_smallBlocks
    (packageOfLargeClosedPlacementFieldsFromSix L) small

/-! ## Honest remaining source blocker -/

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  Nonempty LargeTailExactSourcePackage

theorem remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeClosedPlacementFieldsFromSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toLargeClosedPlacementFields
  case mpr =>
    intro h
    cases h with
    | intro L =>
        exact Nonempty.intro (packageOfLargeClosedPlacementFieldsFromSix L)

theorem remainingBlocker_of_remainingLargeTailExactSourceBlocker
    (H : RemainingLargeTailExactSourceBlocker) :
    RemainingPositiveExactChainBlocker := by
  cases H with
  | intro P =>
      exact P.remainingBlocker

end

end LargeTailExactSourceW28
end PachToth

namespace Verified

abbrev PachTothW28LargeTailExactSourcePackage : Type :=
  PachToth.LargeTailExactSourceW28.LargeTailExactSourcePackage

abbrev PachTothW28RemainingLargeTailExactSourceBlocker : Prop :=
  PachToth.LargeTailExactSourceW28.RemainingLargeTailExactSourceBlocker

theorem pachtoth_w28_remainingBlocker_of_largeTailExactSourcePackage
    (P : PachTothW28LargeTailExactSourcePackage) :
    PachToth.LargeTailExactSourceW28.RemainingPositiveExactChainBlocker :=
  PachToth.LargeTailExactSourceW28.remainingBlocker_of_largeTailExactSourcePackage
    P

theorem pachtoth_w28_remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix :
    PachTothW28RemainingLargeTailExactSourceBlocker <->
      Nonempty PachToth.LargeTailExactSourceW28.LargeClosedPlacementFieldsFromSix :=
  PachToth.LargeTailExactSourceW28.remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix

end Verified
end ErdosProblems1066
