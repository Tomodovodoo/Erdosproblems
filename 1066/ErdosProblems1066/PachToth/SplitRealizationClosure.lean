import ErdosProblems1066.PachToth.GeneratedSeparationInterface
import ErdosProblems1066.PachToth.SplitCertificateBridge

set_option autoImplicit false

/-!
# Split realization closure for generated closed chains

This module closes the conditional packaging gap between exact generated
closed-chain data and the split soundness interface.  The chain geometry is
routed through the existing generated closed-placement bridge, while the
remainder block and the far-apart combined placement remain explicit inputs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SplitRealizationClosure

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- A generated closed chain, including the period equation and metric
obligations needed by the closed-placement interface. -/
structure ExactGeneratedClosedChainData (k : Nat) (hk : 0 < k) where
  O : Figure2Certificate.SameOppositeTransitionObligations
  base : LocalVertex -> R2
  orientation : Fin k -> OrientationData.BlockOrientation
  period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation
  metric :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation

/-- Build the closed placement carried by generated closed-chain data. -/
def closedPlacementOfGeneratedClosedChain
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate
    O hk base orientation period H).toClosedPlacement

/-- Generated closed-chain data supplies the exact-chain upper certificate
used by `SplitSoundness.CanonicalSplitRealization`. -/
def exactChainUpperOfGeneratedClosedChain
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement
    (closedPlacementOfGeneratedClosedChain O hk base orientation period H)

/-- Bundle exact generated closed-chain data into a closed placement. -/
def ExactGeneratedClosedChainData.closedPlacement
    {k : Nat} {hk : 0 < k}
    (G : ExactGeneratedClosedChainData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementOfGeneratedClosedChain
    G.O hk G.base G.orientation G.period G.metric

/-- Bundle exact generated closed-chain data into the exact-chain upper
certificate used by split soundness. -/
def ExactGeneratedClosedChainData.exactChainUpper
    {k : Nat} {hk : 0 < k}
    (G : ExactGeneratedClosedChainData k hk) :
    SplitSoundness.ExactChainUpper k :=
  exactChainUpperOfGeneratedClosedChain
    G.O hk G.base G.orientation G.period G.metric

/-- Combine exact generated closed-chain data, an arbitrary checked remainder
certificate, and an explicit far-apart combined placement into the canonical
split realization consumed by `SplitSoundness`. -/
def canonicalSplitRealizationOfGeneratedClosedChainFarApart
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k r : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (remainder : SplitSoundness.RemainderUpper r)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (closedPlacementOfGeneratedClosedChain
          O hk base orientation period H).config
        remainder.config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  SplitCertificateBridge.canonicalSplitRealizationOfExactChainFarApart
    (exactChainUpperOfGeneratedClosedChain O hk base orientation period H)
    remainder
    F

/-- Bundled-data version of
`canonicalSplitRealizationOfGeneratedClosedChainFarApart`. -/
def ExactGeneratedClosedChainData.canonicalSplitRealizationFarApart
    {k r : Nat} {hk : 0 < k}
    (G : ExactGeneratedClosedChainData k hk)
    (remainder : SplitSoundness.RemainderUpper r)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        G.closedPlacement.config
        remainder.config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  canonicalSplitRealizationOfGeneratedClosedChainFarApart
    G.O hk G.base G.orientation G.period G.metric remainder F

/-- Generated closed-chain data with the checked finite remainder
construction and an explicit far-apart placement gives a canonical split
realization. -/
def canonicalSplitRealizationOfGeneratedClosedChainConstructedRemainderFarApart
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k r : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (closedPlacementOfGeneratedClosedChain
          O hk base orientation period H).config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  canonicalSplitRealizationOfGeneratedClosedChainFarApart
    O hk base orientation period H
    (SplitSoundness.remainderUpperOfConstruction r)
    F

/-- Bundled-data version using the checked finite remainder construction. -/
def ExactGeneratedClosedChainData.canonicalSplitRealizationConstructedRemainderFarApart
    {k r : Nat} {hk : 0 < k}
    (G : ExactGeneratedClosedChainData k hk)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        G.closedPlacement.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  canonicalSplitRealizationOfGeneratedClosedChainConstructedRemainderFarApart
    G.O hk G.base G.orientation G.period G.metric F

/-- Existence form of the generated-chain split realization bridge. -/
theorem exists_canonicalSplitRealization_of_generated_closed_chain_farApart
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k r : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (remainder : SplitSoundness.RemainderUpper r)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (closedPlacementOfGeneratedClosedChain
          O hk base orientation period H).config
        remainder.config) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact Exists.intro
    (canonicalSplitRealizationOfGeneratedClosedChainFarApart
      O hk base orientation period H remainder F)
    True.intro

/-- The generated-chain split realization bridge followed by the checked
split counting theorem. -/
theorem targetUpperConstructionFiveSixteenAt_of_generated_closed_chain_farApart
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k r : Nat} (hk : 0 < k) (hr : r < 16)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (remainder : SplitSoundness.RemainderUpper r)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (closedPlacementOfGeneratedClosedChain
          O hk base orientation period H).config
        remainder.config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitSoundness.targetUpperConstructionFiveSixteenAt_of_canonicalSplitRealization
      hr
      (canonicalSplitRealizationOfGeneratedClosedChainFarApart
        O hk base orientation period H remainder F)

/-- Reduced generated metric hypotheses also give the closed placement. -/
def closedPlacementOfGeneratedClosedChain_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate_reduced
    O hk base orientation period H).toClosedPlacement

/-- Reduced generated metric hypotheses supply the exact-chain upper
certificate. -/
def exactChainUpperOfGeneratedClosedChain_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement
    (closedPlacementOfGeneratedClosedChain_reduced
      O hk base orientation period H)

/-- Reduced generated metric hypotheses, an arbitrary checked remainder, and
an explicit far-apart combined placement give a canonical split realization. -/
def canonicalSplitRealizationOfGeneratedClosedChainFarApart_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k r : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (remainder : SplitSoundness.RemainderUpper r)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (closedPlacementOfGeneratedClosedChain_reduced
          O hk base orientation period H).config
        remainder.config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  SplitCertificateBridge.canonicalSplitRealizationOfExactChainFarApart
    (exactChainUpperOfGeneratedClosedChain_reduced
      O hk base orientation period H)
    remainder
    F

end

end SplitRealizationClosure
end PachToth
end ErdosProblems1066
