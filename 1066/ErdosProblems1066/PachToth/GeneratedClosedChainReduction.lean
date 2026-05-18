import ErdosProblems1066.PachToth.GeneratedClosedChain
import ErdosProblems1066.PachToth.ClosedChainReduction

set_option autoImplicit false

/-!
# Generated closed-chain reductions

This module is a thin final bridge: generated closed-chain data is repackaged
as the existing explicit transition closed-placement certificate, then routed
through the established closed-chain reduction theorems.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosedChainReduction

open Arithmetic
open ClosedChainReduction
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Generated closed-chain data, together with the remaining metric
obligations, gives the explicit transition certificate used by the closed
placement reduction layer. -/
def explicitTransitionClosedPlacementCertificateOfGenerated
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedClosedChain.generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v))) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  (GeneratedClosedChain.isometricSuccessorCompatibleCyclicPointOrbitOfGenerated
      O hk base orientation period separated same_block_isometry)
    |>.toExplicitTransitionClosedPlacementCertificate

/-- Generated closed-chain data, with same-block isometry reduced to the base
block plus transition preservation, gives the explicit transition certificate
used by the closed placement reduction layer. -/
def explicitTransitionClosedPlacementCertificateOfGenerated_reducedSameBlock
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedClosedChain.generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v))
    (base_same_block_isometry :
      forall u v : LocalVertex,
        _root_.eucDist (base u) (base v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)))
    (transition_preserves_same_block_distances :
      forall (o : OrientationData.BlockOrientation)
          (source : LocalVertex -> R2) (u v : LocalVertex),
        _root_.eucDist
          ((O.transitionFor o).placeNext source u)
          ((O.transitionFor o).placeNext source v) =
            _root_.eucDist (source u) (source v)) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionClosedPlacementCertificateOfGenerated
    O hk base orientation period separated
    (GeneratedClosedChain.generatedPoint_same_block_isometry
      O hk base orientation base_same_block_isometry
      transition_preserves_same_block_distances)

/-- A single generated closed chain at block count `k` routes through the
existing explicit closed-placement exact-block reduction. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generated_closed_chain
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedClosedChain.generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v))) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
        (explicitTransitionClosedPlacementCertificateOfGenerated
          O hk base orientation period separated same_block_isometry
          |>.toExplicitClosedPlacementCertificate)

/-- A single generated closed chain at block count `k` routes through the
exact-block reduction, with same-block isometry reduced to the base block and
transition preservation obligations. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generated_closed_chain_reducedSameBlock
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedClosedChain.generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v))
    (base_same_block_isometry :
      forall u v : LocalVertex,
        _root_.eucDist (base u) (base v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)))
    (transition_preserves_same_block_distances :
      forall (o : OrientationData.BlockOrientation)
          (source : LocalVertex -> R2) (u v : LocalVertex),
        _root_.eucDist
          ((O.transitionFor o).placeNext source u)
          ((O.transitionFor o).placeNext source v) =
            _root_.eucDist (source u) (source v)) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generated_closed_chain
      O hk base orientation period separated
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)

/-- Generated closed-chain certificates for every positive block count imply
the exact-block Pach--Toth target by the existing transition-certificate
reduction. -/
theorem targetUpperConstructionFiveSixteen_of_generated_closed_chains
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        GeneratedClosedChain.generatedBlock (O k hk) hk (base k hk)
          (orientation k hk) k = base k hk)
    (separated :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
                (orientation k hk) i u)
              (GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
                (orientation k hk) j v))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k) (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
            (orientation k hk) i u)
          (GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
            (orientation k hk) i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v))) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_explicitTransitionClosedPlacementCertificates
        (fun k hk =>
          explicitTransitionClosedPlacementCertificateOfGenerated
            (O k hk) hk (base k hk) (orientation k hk) (period k hk)
            (separated k hk) (same_block_isometry k hk))

/-- Generated closed-chain certificates for every positive block count imply
the exact-block Pach--Toth target, with same-block isometry reduced to the
base block and transition preservation obligations. -/
theorem targetUpperConstructionFiveSixteen_of_generated_closed_chains_reducedSameBlock
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        GeneratedClosedChain.generatedBlock (O k hk) hk (base k hk)
          (orientation k hk) k = base k hk)
    (separated :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
                (orientation k hk) i u)
              (GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
                (orientation k hk) j v))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k) (u v : LocalVertex),
        _root_.eucDist ((base k hk) u) ((base k hk) v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k)
          (o : OrientationData.BlockOrientation)
          (source : LocalVertex -> R2) (u v : LocalVertex),
        _root_.eucDist
          (((O k hk).transitionFor o).placeNext source u)
          (((O k hk).transitionFor o).placeNext source v) =
            _root_.eucDist (source u) (source v)) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_generated_closed_chains
      O base orientation period separated
      (fun k hk =>
        GeneratedClosedChain.generatedPoint_same_block_isometry
          (O k hk) hk (base k hk) (orientation k hk)
          (base_same_block_isometry k hk)
          (transition_preserves_same_block_distances k hk))

end

end GeneratedClosedChainReduction
end PachToth
end ErdosProblems1066
