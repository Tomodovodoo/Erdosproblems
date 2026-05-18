import ErdosProblems1066.KnownBounds
import ErdosProblems1066.PachToth.PachTothFinalRouteW20
import ErdosProblems1066.PachToth.ExplicitClosedPlacementInputPackageW20

set_option autoImplicit false

/-!
# W21 closed-placement KnownBounds gate

This file records the exact internal condition still needed before
`KnownBounds` can expose the Pach--Toth `5 / 16` upper bound as a public
wrapper: an inhabited W20 closed-placement source-field package.

The statements below are intentionally conditional.  No source fields are
constructed here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementKnownBoundsGateW21

noncomputable section

abbrev InputPackage : Type :=
  PachTothFinalRouteW20.InputPackage

abbrev SourceFields : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

/-- Globally explicit spelling for the W21 Pach--Toth source fields consumed by
the `KnownBounds` exposure gate. -/
abbrev ClosedPlacementSourceFields : Type :=
  SourceFields

/-- The exact remaining gate for promoting the W20 Pach--Toth route to
`KnownBounds`-shaped public wrappers. -/
abbrev KnownBoundsGate : Prop :=
  Nonempty SourceFields

/-- Symmetric spelling with the Swanepoel final-gate files. -/
abbrev KnownBoundsExposureGate : Prop :=
  KnownBoundsGate

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactBlockBound (k : Nat) : Prop :=
  Exists fun C : _root_.UDConfig (16 * k) =>
    forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k

abbrev ArbitraryBound (n : Nat) : Prop :=
  Exists fun C : _root_.UDConfig n =>
    forall s : Finset (Fin n), C.IsIndep s ->
      s.card <= Arithmetic.ceilDiv (5 * n) 16

/-- The pair of `KnownBounds`-shaped Pach--Toth statements unlocked by the
gate. -/
structure KnownBoundsStatements : Prop where
  exact :
    forall k : Nat, 0 < k -> ExactBlockBound k
  arbitrary :
    forall n : Nat, ArbitraryBound n

/-- Repackage W20 source fields as the actual W19 input package consumed by
the final route. -/
def inputPackageOfSourceFields
    (S : SourceFields) :
    InputPackage :=
  S.toInputPackage

/-- Choose source fields from the gate.  This is noncomputable because the
gate is a `Nonempty` proposition. -/
def sourceFieldsOfGate
    (G : KnownBoundsGate) :
    SourceFields :=
  Classical.choice G

def inputPackageOfGate
    (G : KnownBoundsGate) :
    InputPackage :=
  inputPackageOfSourceFields (sourceFieldsOfGate G)

/-! ## Input-package route -/

theorem targetUpperConstructionFiveSixteen_of_inputPackage
    (P : InputPackage) :
    ExactTarget :=
  PachTothFinalRouteW20.targetUpperConstructionFiveSixteen_of_inputPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (P : InputPackage) :
    ArbitraryTarget :=
  PachTothFinalRouteW20.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    P

theorem targetUpperConstructionFiveSixteenAt_of_inputPackage
    (P : InputPackage) (n : Nat) :
    FixedTarget n :=
  PachTothFinalRouteW20.targetUpperConstructionFiveSixteenAt_of_inputPackage
    P n

theorem upper_bound_five_sixteen_exact_of_inputPackage
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  PachTothFinalRouteW20.upper_bound_five_sixteen_exact_of_inputPackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_inputPackage
    (P : InputPackage) (n : Nat) :
    ArbitraryBound n :=
  PachTothFinalRouteW20.upper_bound_five_sixteen_arbitrary_of_inputPackage
    P n

/-! ## Source-field route -/

theorem targetUpperConstructionFiveSixteen_of_sourceFields
    (S : SourceFields) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_inputPackage
    (inputPackageOfSourceFields S)

theorem targetUpperConstructionFiveSixteenArbitrary_of_sourceFields
    (S : SourceFields) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (inputPackageOfSourceFields S)

theorem targetUpperConstructionFiveSixteenAt_of_sourceFields
    (S : SourceFields) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenAt_of_inputPackage
    (inputPackageOfSourceFields S) n

theorem upper_bound_five_sixteen_exact_of_sourceFields
    (S : SourceFields) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  upper_bound_five_sixteen_exact_of_inputPackage
    (inputPackageOfSourceFields S) k hk

theorem upper_bound_five_sixteen_arbitrary_of_sourceFields
    (S : SourceFields) (n : Nat) :
    ArbitraryBound n :=
  upper_bound_five_sixteen_arbitrary_of_inputPackage
    (inputPackageOfSourceFields S) n

/-! ## Nonempty gate route -/

theorem targetUpperConstructionFiveSixteen_of_knownBoundsGate
    (G : KnownBoundsGate) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_inputPackage
    (inputPackageOfGate G)

theorem targetUpperConstructionFiveSixteenArbitrary_of_knownBoundsGate
    (G : KnownBoundsGate) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (inputPackageOfGate G)

theorem targetUpperConstructionFiveSixteenAt_of_knownBoundsGate
    (G : KnownBoundsGate) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenAt_of_inputPackage
    (inputPackageOfGate G) n

theorem upper_bound_five_sixteen_exact_of_knownBoundsGate
    (G : KnownBoundsGate) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  upper_bound_five_sixteen_exact_of_inputPackage
    (inputPackageOfGate G) k hk

theorem upper_bound_five_sixteen_arbitrary_of_knownBoundsGate
    (G : KnownBoundsGate) (n : Nat) :
    ArbitraryBound n :=
  upper_bound_five_sixteen_arbitrary_of_inputPackage
    (inputPackageOfGate G) n

/-- Single theorem form of the W21 gate: `KnownBounds` can expose the
Pach--Toth `5 / 16` wrappers once the W20 source fields are inhabited. -/
theorem knownBoundsStatements_of_knownBoundsGate
    (G : KnownBoundsGate) :
    KnownBoundsStatements where
  exact := upper_bound_five_sixteen_exact_of_knownBoundsGate G
  arbitrary := upper_bound_five_sixteen_arbitrary_of_knownBoundsGate G

end

end ClosedPlacementKnownBoundsGateW21

/-- Source-specific conditional exact-block alias for the W21
closed-placement KnownBounds gate. -/
theorem upper_bound_five_sixteen_exact_of_w21_knownBoundsGate
    (G : ClosedPlacementKnownBoundsGateW21.KnownBoundsGate)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementKnownBoundsGateW21.ExactBlockBound k :=
  ClosedPlacementKnownBoundsGateW21.upper_bound_five_sixteen_exact_of_knownBoundsGate
    G k hk

/-- Source-specific conditional arbitrary-`n` alias for the W21
closed-placement KnownBounds gate. -/
theorem upper_bound_five_sixteen_arbitrary_of_w21_knownBoundsGate
    (G : ClosedPlacementKnownBoundsGateW21.KnownBoundsGate) (n : Nat) :
    ClosedPlacementKnownBoundsGateW21.ArbitraryBound n :=
  ClosedPlacementKnownBoundsGateW21.upper_bound_five_sixteen_arbitrary_of_knownBoundsGate
    G n

end PachToth

namespace Verified

abbrev PachTothW21ClosedPlacementSourceFields :=
  PachToth.ClosedPlacementKnownBoundsGateW21.SourceFields

abbrev PachTothW21KnownBoundsGate : Prop :=
  PachToth.ClosedPlacementKnownBoundsGateW21.KnownBoundsGate

abbrev PachTothW21KnownBoundsStatements : Prop :=
  PachToth.ClosedPlacementKnownBoundsGateW21.KnownBoundsStatements

/-- Public-facade-shaped conditional Pach--Toth exact-block upper bound from
the W21 nonempty source-field gate. -/
theorem upper_bound_five_sixteen_exact_of_pachtoth_w21_knownBoundsGate
    (G : PachTothW21KnownBoundsGate) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w21_knownBoundsGate G k hk

/-- Public-facade-shaped conditional Pach--Toth arbitrary-`n` upper bound from
the W21 nonempty source-field gate. -/
theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w21_knownBoundsGate
    (G : PachTothW21KnownBoundsGate) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w21_knownBoundsGate G n

/-- Condensed public-facade-shaped statement package unlocked by the W21
nonempty source-field gate. -/
theorem pachtoth_w21_knownBoundsStatements_of_knownBoundsGate
    (G : PachTothW21KnownBoundsGate) :
    PachTothW21KnownBoundsStatements :=
  PachToth.ClosedPlacementKnownBoundsGateW21.knownBoundsStatements_of_knownBoundsGate
    G

end Verified
end ErdosProblems1066
