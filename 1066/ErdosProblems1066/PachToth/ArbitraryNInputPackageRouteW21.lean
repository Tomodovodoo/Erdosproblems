import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20
import ErdosProblems1066.PachToth.PachTothFinalRouteW20

set_option autoImplicit false

/-!
# W21 arbitrary-n route from input packages

This file adds only conditional wrappers.  It does not add a public
`KnownBounds` theorem: the remaining data for such a theorem is precisely an
inhabitant of the W19 explicit closed-placement input package, equivalently
the raw W20 generated-chain source fields below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNInputPackageRouteW21

noncomputable section

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev W20SourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

abbrev ExactTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.FixedTarget n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.ExactBlockTarget k

/-- The smallest remaining Pach--Toth data that would let `KnownBounds` expose
an unconditional `5 / 16` upper-bound theorem. -/
abbrev KnownBoundsRemainingData : Type :=
  W19InputPackage

namespace W19InputPackage

/-- Forget the packaged generated family, closure equations, and reduced metric
hypotheses to the raw W20 source-field surface. -/
def toSourceFields
    (P : W19InputPackage) :
    W20SourceFields where
  O := P.family.O
  base := P.family.base
  orientation := P.family.orientation
  closure := P.closure
  separated := fun k hk => (P.metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (P.metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (P.metric.metric k hk).transition_preserves_same_block_distances

@[simp]
theorem toSourceFields_toInputPackage
    (P : W19InputPackage) :
    P.toSourceFields.toInputPackage = P := by
  cases P
  rfl

def explicitClosedPlacementCertificateFamily
    (P : W19InputPackage) :
    ExplicitClosedPlacementCertificateFamily :=
  P.explicitClosedPlacementCertificate

theorem targetUpperConstructionFiveSixteen
    (P : W19InputPackage) :
    ExactTarget :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteen
    P

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : W19InputPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteenAt_exactBlock
    P k hk

theorem targetUpperConstructionFiveSixteenArbitrary
    (P : W19InputPackage) :
    ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteenArbitrary
    P

theorem targetUpperConstructionFiveSixteenAt
    (P : W19InputPackage) (n : Nat) :
    FixedTarget n :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteenAt
    P n

/-- KnownBounds-shaped exact-block upper-bound wrapper from one W19 input
package. -/
theorem upper_bound_five_sixteen_exact
    (P : W19InputPackage) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothFinalRouteW20.upper_bound_five_sixteen_exact_of_inputPackage
    P k hk

/-- KnownBounds-shaped arbitrary-`n` upper-bound wrapper from one W19 input
package. -/
theorem upper_bound_five_sixteen_arbitrary
    (P : W19InputPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  ExplicitClosedPlacementProducerW19.InputPackage.upper_bound_five_sixteen_arbitrary
    P n

end W19InputPackage

namespace W20SourceFields

def explicitClosedPlacementCertificateFamily
    (S : W20SourceFields) :
    ExplicitClosedPlacementCertificateFamily :=
  S.explicitClosedPlacementCertificate

theorem targetUpperConstructionFiveSixteen
    (S : W20SourceFields) :
    ExactTarget :=
  GeneratedChainFamilyProducerW20.SourceFields.targetUpperConstructionFiveSixteen
    S

/-- Exact-block target at `16 * k` from raw W20 generated-chain source fields. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (S : W20SourceFields) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  S.toInputPackage.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteenArbitrary
    (S : W20SourceFields) :
    ArbitraryTarget :=
  GeneratedChainFamilyProducerW20.SourceFields.targetUpperConstructionFiveSixteenArbitrary
    S

/-- Pointwise arbitrary-vertex target from raw W20 generated-chain source
fields. -/
theorem targetUpperConstructionFiveSixteenAt
    (S : W20SourceFields) (n : Nat) :
    FixedTarget n :=
  GeneratedChainFamilyProducerW20.SourceFields.targetUpperConstructionFiveSixteenArbitrary
    S n

/-- KnownBounds-shaped exact-block upper-bound wrapper from raw W20
generated-chain source fields. -/
theorem upper_bound_five_sixteen_exact
    (S : W20SourceFields) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  W19InputPackage.upper_bound_five_sixteen_exact S.toInputPackage k hk

/-- KnownBounds-shaped arbitrary-`n` upper-bound wrapper from raw W20
generated-chain source fields. -/
theorem upper_bound_five_sixteen_arbitrary
    (S : W20SourceFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  W19InputPackage.upper_bound_five_sixteen_arbitrary S.toInputPackage n

end W20SourceFields

/-- Raw W20 source fields and the minimal W19 input package carry the same
inhabitation information. -/
theorem nonempty_w20SourceFields_iff_knownBoundsRemainingData :
    Nonempty W20SourceFields <-> Nonempty KnownBoundsRemainingData := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro S => exact Nonempty.intro S.toInputPackage)
      (fun h => by
        cases h with
        | intro P => exact Nonempty.intro P.toSourceFields)

/-- A nonempty minimal input package is enough to derive the exact-block
KnownBounds-shaped endpoint, but no such inhabitant is constructed here. -/
theorem upper_bound_five_sixteen_exact_of_knownBoundsRemainingData
    (H : Nonempty KnownBoundsRemainingData) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k := by
  cases H with
  | intro P => exact P.upper_bound_five_sixteen_exact k hk

/-- A nonempty minimal input package is enough to derive the arbitrary-`n`
KnownBounds-shaped endpoint, but no such inhabitant is constructed here. -/
theorem upper_bound_five_sixteen_arbitrary_of_knownBoundsRemainingData
    (H : Nonempty KnownBoundsRemainingData) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 := by
  cases H with
  | intro P => exact P.upper_bound_five_sixteen_arbitrary n

end

end ArbitraryNInputPackageRouteW21

/-! ## Source-specific public-style aliases -/

theorem upper_bound_five_sixteen_exact_of_w21_inputPackage
    (P : ArbitraryNInputPackageRouteW21.W19InputPackage)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  ArbitraryNInputPackageRouteW21.W19InputPackage.upper_bound_five_sixteen_exact
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_w21_inputPackage
    (P : ArbitraryNInputPackageRouteW21.W19InputPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  ArbitraryNInputPackageRouteW21.W19InputPackage.upper_bound_five_sixteen_arbitrary
    P n

theorem upper_bound_five_sixteen_exact_of_w21_sourceFields
    (S : ArbitraryNInputPackageRouteW21.W20SourceFields)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  ArbitraryNInputPackageRouteW21.W20SourceFields.upper_bound_five_sixteen_exact
    S k hk

theorem upper_bound_five_sixteen_arbitrary_of_w21_sourceFields
    (S : ArbitraryNInputPackageRouteW21.W20SourceFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  ArbitraryNInputPackageRouteW21.W20SourceFields.upper_bound_five_sixteen_arbitrary
    S n

end PachToth

namespace Verified

abbrev PachTothW21KnownBoundsRemainingData : Type :=
  PachToth.ArbitraryNInputPackageRouteW21.KnownBoundsRemainingData

abbrev PachTothW21SourceFields : Type :=
  PachToth.ArbitraryNInputPackageRouteW21.W20SourceFields

theorem upper_bound_five_sixteen_exact_of_pachtoth_w21_knownBoundsRemainingData
    (H : Nonempty PachTothW21KnownBoundsRemainingData)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.ArbitraryNInputPackageRouteW21.upper_bound_five_sixteen_exact_of_knownBoundsRemainingData
    H k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w21_knownBoundsRemainingData
    (H : Nonempty PachTothW21KnownBoundsRemainingData) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  open PachToth.ArbitraryNInputPackageRouteW21 in
    upper_bound_five_sixteen_arbitrary_of_knownBoundsRemainingData H n

theorem upper_bound_five_sixteen_exact_of_pachtoth_w21_sourceFields
    (S : PachTothW21SourceFields) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w21_sourceFields S k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w21_sourceFields
    (S : PachTothW21SourceFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w21_sourceFields S n

end Verified
end ErdosProblems1066
