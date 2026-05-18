import ErdosProblems1066.PachToth.NonRoleSplitSourceInhabitationW25
import ErdosProblems1066.PachToth.ClosedPlacementWitnessAssemblyW25
import ErdosProblems1066.PachToth.FreePlacementFieldsInhabitationW25
import ErdosProblems1066.PachToth.ArbitraryNClosureW11

set_option autoImplicit false

/-!
# W26 non-role split-source construction

This file is the PT2 worker lane for the W26 Pach--Toth route.  It checks
whether the current tree already contains an unconditional inhabitant of the
minimal non-role split source.  The answer is still no: the source is exactly
the existing positive exact-chain package, equivalently the W11 exact closed
chain package.

The constructive progress here is that every currently exposed
closed-placement surface is routed all the way to `NonRoleSplitSource`, while
the remaining inhabitance target is reduced to the concrete W11 exact-chain
structure, without adding assumptions, axioms, or proof placeholders.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRoleSplitSourceConstructionW26

noncomputable section

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceInhabitationW25.NonRoleSplitSource

abbrev PositiveExactChainPackage : Type :=
  NonRoleSplitSourceInhabitationW25.PositiveExactChainPackage

abbrev W11ExactClosedChainPackage : Type :=
  ArbitraryNClosureW11.ExactClosedChainPackage

abbrev W10ClosedPlacementPackage : Type :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev MinimalFreePlacementFields : Type :=
  ClosedPlacementWitnessAssemblyW25.MinimalFreePlacementFields

abbrev ExplicitEdgeSoundnessFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ExplicitEdgeSoundnessFamily

abbrev FullMetricClosedPlacementWitness : Type :=
  ClosedPlacementWitnessAssemblyW25.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  ClosedPlacementWitnessAssemblyW25.ReducedMetricClosedPlacementWitness

/-! ## Exact-chain packages are the same remaining source -/

def positiveExactChainPackageOfW11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    PositiveExactChainPackage where
  exactChain := P.chain

def w11ExactClosedChainPackageOfPositiveExactChainPackage
    (P : PositiveExactChainPackage) :
    W11ExactClosedChainPackage where
  chain := P.exactChain

theorem positiveExactChain_w11_left_inverse
    (P : PositiveExactChainPackage) :
    positiveExactChainPackageOfW11ExactClosedChainPackage
      (w11ExactClosedChainPackageOfPositiveExactChainPackage P) = P := by
  cases P
  rfl

theorem positiveExactChain_w11_right_inverse
    (P : W11ExactClosedChainPackage) :
    w11ExactClosedChainPackageOfPositiveExactChainPackage
      (positiveExactChainPackageOfW11ExactClosedChainPackage P) = P := by
  cases P
  rfl

theorem nonempty_positiveExactChainPackage_iff_w11ExactClosedChainPackage :
    Nonempty PositiveExactChainPackage <->
      Nonempty W11ExactClosedChainPackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro
          (w11ExactClosedChainPackageOfPositiveExactChainPackage P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro
          (positiveExactChainPackageOfW11ExactClosedChainPackage P)

def nonRoleSplitSourceOfW11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    NonRoleSplitSource :=
  NonRoleSplitSourceInhabitationW25.nonRoleSplitSourceOfPositiveExactChainPackage
    (positiveExactChainPackageOfW11ExactClosedChainPackage P)

def w11ExactClosedChainPackageOfNonRoleSplitSource
    (S : NonRoleSplitSource) :
    W11ExactClosedChainPackage :=
  w11ExactClosedChainPackageOfPositiveExactChainPackage
    (NonRoleSplitSourceInhabitationW25.positiveExactChainPackageOfNonRoleSplitSource
      S)

theorem nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage :
    Nonempty NonRoleSplitSource <->
      Nonempty W11ExactClosedChainPackage :=
  Iff.trans
    NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_positiveExactChainPackage
    nonempty_positiveExactChainPackage_iff_w11ExactClosedChainPackage

theorem nonempty_w11ExactClosedChainPackage_iff_nonRoleSplitSource :
    Nonempty W11ExactClosedChainPackage <->
      Nonempty NonRoleSplitSource :=
  nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage.symm

/-! ## Closed-placement data constructs exact chains -/

def positiveExactChainPackageOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    PositiveExactChainPackage where
  exactChain := fun k hk =>
    SplitCertificateBridge.exactChainUpperOfClosedPlacement (H k hk)

def w11ExactClosedChainPackageOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    W11ExactClosedChainPackage where
  chain := fun k hk =>
    SplitCertificateBridge.exactChainUpperOfClosedPlacement (H k hk)

def nonRoleSplitSourceOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    NonRoleSplitSource :=
  NonRoleSplitSourceInhabitationW25.nonRoleSplitSourceOfClosedPlacements H

def closedPlacementFamilyOfW10ClosedPlacementPackage
    (P : W10ClosedPlacementPackage) :
    ClosedPlacementFamily :=
  P.placement

def nonRoleSplitSourceOfW10ClosedPlacementPackage
    (P : W10ClosedPlacementPackage) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfClosedPlacementFamily
    (closedPlacementFamilyOfW10ClosedPlacementPackage P)

def w11ExactClosedChainPackageOfW10ClosedPlacementPackage
    (P : W10ClosedPlacementPackage) :
    W11ExactClosedChainPackage :=
  w11ExactClosedChainPackageOfClosedPlacementFamily
    (closedPlacementFamilyOfW10ClosedPlacementPackage P)

theorem nonempty_nonRoleSplitSource_of_closedPlacementFamily :
    Nonempty ClosedPlacementFamily -> Nonempty NonRoleSplitSource := by
  intro h
  cases h with
  | intro H =>
      exact Nonempty.intro (nonRoleSplitSourceOfClosedPlacementFamily H)

theorem nonempty_w11ExactClosedChainPackage_of_closedPlacementFamily :
    Nonempty ClosedPlacementFamily ->
      Nonempty W11ExactClosedChainPackage := by
  intro h
  cases h with
  | intro H =>
      exact Nonempty.intro
        (w11ExactClosedChainPackageOfClosedPlacementFamily H)

theorem nonempty_nonRoleSplitSource_of_w10ClosedPlacementPackage :
    Nonempty W10ClosedPlacementPackage -> Nonempty NonRoleSplitSource := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro
        (nonRoleSplitSourceOfW10ClosedPlacementPackage P)

/-! ## Higher closed-placement surfaces construct the same source -/

def nonRoleSplitSourceOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfClosedPlacementFamily
    (ClosedPlacementWitnessAssemblyW25.closedPlacementFamilyOfMinimalFreePlacementFields
      S)

def nonRoleSplitSourceOfExplicitEdgeSoundnessFamily
    (G : ExplicitEdgeSoundnessFamily) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfMinimalFreePlacementFields
    (FreePlacementFieldsInhabitationW25.minimalOfExplicitEdgeSoundnessFamily
      G)

def nonRoleSplitSourceOfFullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness) :
    NonRoleSplitSource :=
  NonRoleSplitSourceInhabitationW25.nonRoleSplitSourceOfFullMetricClosedPlacementWitness
    W

def nonRoleSplitSourceOfReducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness) :
    NonRoleSplitSource :=
  NonRoleSplitSourceInhabitationW25.nonRoleSplitSourceOfReducedMetricClosedPlacementWitness
    W

theorem nonempty_nonRoleSplitSource_of_minimalFreePlacementFields :
    Nonempty MinimalFreePlacementFields -> Nonempty NonRoleSplitSource := by
  intro h
  cases h with
  | intro S =>
      exact Nonempty.intro
        (nonRoleSplitSourceOfMinimalFreePlacementFields S)

theorem nonempty_nonRoleSplitSource_of_explicitEdgeSoundnessFamily :
    Nonempty ExplicitEdgeSoundnessFamily -> Nonempty NonRoleSplitSource := by
  intro h
  cases h with
  | intro G =>
      exact Nonempty.intro
        (nonRoleSplitSourceOfExplicitEdgeSoundnessFamily G)

theorem nonempty_nonRoleSplitSource_of_fullMetricClosedPlacementWitness :
    Nonempty FullMetricClosedPlacementWitness -> Nonempty NonRoleSplitSource := by
  intro h
  cases h with
  | intro W =>
      exact Nonempty.intro
        (nonRoleSplitSourceOfFullMetricClosedPlacementWitness W)

theorem nonempty_nonRoleSplitSource_of_reducedMetricClosedPlacementWitness :
    Nonempty ReducedMetricClosedPlacementWitness ->
      Nonempty NonRoleSplitSource := by
  intro h
  cases h with
  | intro W =>
      exact Nonempty.intro
        (nonRoleSplitSourceOfReducedMetricClosedPlacementWitness W)

/-! ## Obstruction forms for the remaining construction -/

theorem no_closedPlacementFamily_of_no_nonRoleSplitSource
    (h : Not (Nonempty NonRoleSplitSource)) :
    Not (Nonempty ClosedPlacementFamily) := by
  intro hclosed
  exact h (nonempty_nonRoleSplitSource_of_closedPlacementFamily hclosed)

theorem no_minimalFreePlacementFields_of_no_nonRoleSplitSource
    (h : Not (Nonempty NonRoleSplitSource)) :
    Not (Nonempty MinimalFreePlacementFields) := by
  intro hfree
  exact h (nonempty_nonRoleSplitSource_of_minimalFreePlacementFields hfree)

theorem no_explicitEdgeSoundnessFamily_of_no_nonRoleSplitSource
    (h : Not (Nonempty NonRoleSplitSource)) :
    Not (Nonempty ExplicitEdgeSoundnessFamily) := by
  intro hedge
  exact h (nonempty_nonRoleSplitSource_of_explicitEdgeSoundnessFamily hedge)

theorem no_w11ExactClosedChainPackage_of_no_nonRoleSplitSource
    (h : Not (Nonempty NonRoleSplitSource)) :
    Not (Nonempty W11ExactClosedChainPackage) := by
  intro hexact
  exact h
    (nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage.mpr
      hexact)

theorem no_nonRoleSplitSource_of_no_w11ExactClosedChainPackage
    (h : Not (Nonempty W11ExactClosedChainPackage)) :
    Not (Nonempty NonRoleSplitSource) := by
  intro hsource
  exact h
    (nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage.mp
      hsource)

/-! ## Target projections from the constructed source -/

theorem exactTarget_of_w11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    targetUpperConstructionFiveSixteen :=
  (nonRoleSplitSourceOfW11ExactClosedChainPackage P).exactTarget

theorem arbitraryTarget_of_w11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    targetUpperConstructionFiveSixteenArbitrary :=
  (nonRoleSplitSourceOfW11ExactClosedChainPackage P).arbitraryTarget

theorem exactTarget_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    targetUpperConstructionFiveSixteen :=
  (nonRoleSplitSourceOfClosedPlacementFamily H).exactTarget

theorem arbitraryTarget_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  (nonRoleSplitSourceOfClosedPlacementFamily H).arbitraryTarget

end

end NonRoleSplitSourceConstructionW26
end PachToth

namespace Verified

abbrev PachTothW26NonRoleSplitSource : Type :=
  PachToth.NonRoleSplitSourceConstructionW26.NonRoleSplitSource

abbrev PachTothW26W11ExactClosedChainPackage : Type :=
  PachToth.NonRoleSplitSourceConstructionW26.W11ExactClosedChainPackage

theorem pachtoth_w26_nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage :
    Nonempty PachTothW26NonRoleSplitSource <->
      Nonempty PachTothW26W11ExactClosedChainPackage :=
  PachToth.NonRoleSplitSourceConstructionW26.nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage

end Verified
end ErdosProblems1066
