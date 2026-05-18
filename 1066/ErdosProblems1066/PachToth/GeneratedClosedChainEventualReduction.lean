import ErdosProblems1066.PachToth.GeneratedClosedChainReduction
import ErdosProblems1066.PachToth.EventualReduction

set_option autoImplicit false

/-!
# Eventual generated closed-chain reduction

This module routes eventual generated closed-chain data through the existing
generated-chain and eventual closed-placement reductions.  The generated
metric checks remain explicit hypotheses.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosedChainEventualReduction

open ClosedChainReduction
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Eventual generated closed-chain data, plus the finite small cases required
by the existing eventual reduction, implies the arbitrary-`n` Pach--Toth
target.

The geometric metric obligations for the generated chains are kept as
explicit hypotheses: the final period equation, global separation, and
same-block isometry. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_closed_chains_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedClosedChain.generatedBlock (O k hK hk) hk (base k hK hk)
          (orientation k hK hk) k = base k hK hk)
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint (O k hK hk) hk
                (base k hK hk) (orientation k hK hk) i u)
              (GeneratedClosedChain.generatedPoint (O k hK hk) hk
                (base k hK hk) (orientation k hK hk) j v))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k)
        (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint (O k hK hk) hk
            (base k hK hk) (orientation k hK hk) i u)
          (GeneratedClosedChain.generatedPoint (O k hK hk) hk
            (base k hK hk) (orientation k hK hk) i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v)))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventualExplicitClosedPlacement_and_small
      K0
      (fun k hK hk =>
        (GeneratedClosedChainReduction.explicitTransitionClosedPlacementCertificateOfGenerated
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk) (separated k hK hk) (same_block_isometry k hK hk)
          |>.toExplicitClosedPlacementCertificate))
      Hsmall

/-- Eventual generated closed-chain data whose base block is isometric to the
checked one-block certificate, and whose selected transitions preserve all
same-block distances, implies the arbitrary-`n` Pach--Toth target.

This is the eventual arbitrary-`n` wrapper with the generated-chain
same-block isometry discharged from the base and transition hypotheses. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_chains_base_transitions
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedClosedChain.generatedBlock (O k hK hk) hk (base k hK hk)
          (orientation k hK hk) k = base k hK hk)
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint (O k hK hk) hk
                (base k hK hk) (orientation k hK hk) i u)
              (GeneratedClosedChain.generatedPoint (O k hK hk) hk
                (base k hK hk) (orientation k hK hk) j v))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k) (u v : LocalVertex),
        _root_.eucDist ((base k hK hk) u) ((base k hK hk) v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k)
          (o : OrientationData.BlockOrientation)
          (source : LocalVertex -> R2) (u v : LocalVertex),
        _root_.eucDist
          (((O k hK hk).transitionFor o).placeNext source u)
          (((O k hK hk).transitionFor o).placeNext source v) =
            _root_.eucDist (source u) (source v))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_closed_chains_and_small
      K0 O base orientation period separated
      (fun k hK hk =>
        GeneratedClosedChain.generatedPoint_same_block_isometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (base_same_block_isometry k hK hk)
          (transition_preserves_same_block_distances k hK hk))
      Hsmall

end

end GeneratedClosedChainEventualReduction
end PachToth
end ErdosProblems1066
