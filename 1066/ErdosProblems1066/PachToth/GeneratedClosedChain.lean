import ErdosProblems1066.PachToth.ClosedPlacementAlgebra
import ErdosProblems1066.PachToth.ClosedChainExistence

set_option autoImplicit false

/-!
# Generated closed chains

This module bridges a generated same/opposite orbit into the existing
closed-chain interfaces.  The point map is generated from one base block and
an orientation word; the only cyclic wraparound hypothesis is the final
period equation saying that the block produced after `k` steps is the base
block again.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosedChain

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Read a finite orientation word at a natural-number position.  Positions
outside the word are sent to the first letter; the generated closed-chain
lemmas below only inspect positions `< k`. -/
def orientationAt {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) (n : Nat) :
    OrientationData.BlockOrientation :=
  if h : n < k then orientation ⟨n, h⟩ else orientation ⟨0, hk⟩

@[simp]
theorem orientationAt_of_lt {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    {n : Nat} (hn : n < k) :
    orientationAt hk orientation n = orientation ⟨n, hn⟩ := by
  simp [orientationAt, hn]

/-- The block obtained after following the first `n` letters of the
orientation word from a base block. -/
def generatedBlock
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    Nat -> LocalVertex -> R2
  | 0 => base
  | n + 1 =>
      (O.transitionFor (orientationAt hk orientation n)).placeNext
        (generatedBlock O hk base orientation n)

@[simp]
theorem generatedBlock_zero
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    generatedBlock O hk base orientation 0 = base :=
  rfl

@[simp]
theorem generatedBlock_succ_apply
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (n : Nat) (v : LocalVertex) :
    generatedBlock O hk base orientation (n + 1) v =
      (O.transitionFor (orientationAt hk orientation n)).placeNext
        (generatedBlock O hk base orientation n) v :=
  rfl

/-- The generated cyclic point map: block `i` is the block generated after
`i.val` steps from the base block. -/
def generatedPoint
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) : LocalVertex -> R2 :=
  generatedBlock O hk base orientation i.val

/-- The step map selected by the orientation word. -/
def generatedStep
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat}
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) : OrientationData.OrientedTransition :=
  O.transitionFor (orientation i)

@[simp]
theorem generatedStep_orientation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat}
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) :
    (generatedStep O orientation i).orientation = orientation i := by
  simp [generatedStep,
    Figure2Certificate.SameOppositeTransitionObligations.transitionFor_orientation]

@[simp]
theorem generatedPoint_zero
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (v : LocalVertex) :
    generatedPoint O hk base orientation ⟨0, hk⟩ v = base v :=
  rfl

/-- Generated points preserve all same-block distances when the base block is
isometric to the checked one-block certificate and every selected transition
preserves all same-block distances. -/
theorem generatedPoint_same_block_isometry
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
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
    forall (i : Fin k) (u v : LocalVertex),
      _root_.eucDist
        (generatedPoint O hk base orientation i u)
        (generatedPoint O hk base orientation i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)) := by
  intro i u v
  have hblock :
      forall n : Nat, forall u v : LocalVertex,
        _root_.eucDist
          (generatedBlock O hk base orientation n u)
          (generatedBlock O hk base orientation n v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v)) := by
    intro n
    induction n with
    | zero =>
        intro u v
        exact base_same_block_isometry u v
    | succ n ih =>
        intro u v
        calc
          _root_.eucDist
              (generatedBlock O hk base orientation (n + 1) u)
              (generatedBlock O hk base orientation (n + 1) v) =
                _root_.eucDist
                  (generatedBlock O hk base orientation n u)
                  (generatedBlock O hk base orientation n v) := by
              exact
                transition_preserves_same_block_distances
                  (orientationAt hk orientation n)
                  (generatedBlock O hk base orientation n) u v
          _ =
              _root_.eucDist
                (OneBlockSoundness.oneBlockCertificate.config.pts
                  (BlockPartition.localVertexEquivFin16 u))
                (OneBlockSoundness.oneBlockCertificate.config.pts
                  (BlockPartition.localVertexEquivFin16 v)) := ih u v
  exact hblock i.val u v

/-- Away from the final index, generated points satisfy the successor
equation definitionally after reducing the finite successor value. -/
theorem generatedPoint_succ_of_val_succ_lt
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (hi : i.val + 1 < k) (v : LocalVertex) :
    generatedPoint O hk base orientation (cyclicSucc hk i) v =
      (generatedStep O orientation i).placeNext
        (generatedPoint O hk base orientation i) v := by
  have hsucc_val : (cyclicSucc hk i).val = i.val + 1 := by
    simp [cyclicSucc, Fin.val_add, Nat.mod_eq_of_lt hi]
  have hread :
      orientationAt hk orientation i.val = orientation i := by
    simp [orientationAt, i.isLt]
  simp [generatedPoint, generatedStep, hsucc_val]

/-- At the final index, the successor equation follows from the one supplied
closure equation. -/
theorem generatedPoint_succ_of_period
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      generatedBlock O hk base orientation k = base)
    (i : Fin k) (hi : ¬ i.val + 1 < k) (v : LocalVertex) :
    generatedPoint O hk base orientation (cyclicSucc hk i) v =
      (generatedStep O orientation i).placeNext
        (generatedPoint O hk base orientation i) v := by
  have hi_last : i.val + 1 = k := by
    omega
  have hsucc_val : (cyclicSucc hk i).val = 0 := by
    simp [cyclicSucc, Fin.val_add, hi_last]
  have hread :
      orientationAt hk orientation (k - 1) = orientation i := by
    have hk_sub_lt : k - 1 < k := Nat.sub_lt hk Nat.zero_lt_one
    have hi_val : i.val = k - 1 := by
      omega
    calc
      orientationAt hk orientation (k - 1) = orientation ⟨k - 1, hk_sub_lt⟩ := by
        simp [orientationAt, hk_sub_lt]
      _ = orientation i := by
        congr
        exact hi_val.symm
  calc
    generatedPoint O hk base orientation (cyclicSucc hk i) v
        = base v := by
          simp [generatedPoint, hsucc_val]
    _ = generatedBlock O hk base orientation k v := by
          rw [period]
    _ = generatedBlock O hk base orientation (i.val + 1) v := by
          rw [hi_last]
    _ =
        (generatedStep O orientation i).placeNext
          (generatedPoint O hk base orientation i) v := by
          simp [generatedPoint, generatedStep]

/-- The generated point map is successor-compatible once the final generated
block closes back to the base block. -/
theorem generatedPoint_successor_compatible
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      generatedBlock O hk base orientation k = base) :
    forall i : Fin k, forall v : LocalVertex,
      generatedPoint O hk base orientation (cyclicSucc hk i) v =
        (generatedStep O orientation i).placeNext
          (generatedPoint O hk base orientation i) v := by
  intro i v
  by_cases hi : i.val + 1 < k
  · exact generatedPoint_succ_of_val_succ_lt O hk base orientation i hi v
  · exact generatedPoint_succ_of_period O hk base orientation period i hi v

/-- Package a generated closed chain as the isometric successor-compatible
orbit interface, without assuming such an orbit as input.

The hypotheses are the intended reduced checklist: the generated point
definition and step map are fixed by `generatedPoint`/`generatedStep`; cyclic
successor compatibility is reduced to the single final period equation, while
connector unit edges, global separation, and same-block isometry remain the
explicit geometric obligations. -/
def isometricSuccessorCompatibleCyclicPointOrbitOfGenerated
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (generatedPoint O hk base orientation i u)
              (generatedPoint O hk base orientation j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (generatedPoint O hk base orientation i u)
          (generatedPoint O hk base orientation i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v))) :
    ClosedChainExistence.IsometricSuccessorCompatibleCyclicPointOrbit k hk where
  point := generatedPoint O hk base orientation
  step := generatedStep O orientation
  successor_compatible :=
    generatedPoint_successor_compatible O hk base orientation period
  connector_unit_edges := by
    intro i u v hconn
    exact
      Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
        O (orientation i) (generatedPoint O hk base orientation i) u v hconn
  separated := separated
  same_block_isometry := same_block_isometry

@[simp]
theorem isometricSuccessorCompatibleCyclicPointOrbitOfGenerated_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (generatedPoint O hk base orientation i u)
              (generatedPoint O hk base orientation j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (generatedPoint O hk base orientation i u)
          (generatedPoint O hk base orientation i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v)))
    (i : Fin k) (v : LocalVertex) :
    (isometricSuccessorCompatibleCyclicPointOrbitOfGenerated O hk base
      orientation period separated same_block_isometry).point i v =
        generatedPoint O hk base orientation i v :=
  rfl

@[simp]
theorem isometricSuccessorCompatibleCyclicPointOrbitOfGenerated_step
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (generatedPoint O hk base orientation i u)
              (generatedPoint O hk base orientation j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (generatedPoint O hk base orientation i u)
          (generatedPoint O hk base orientation i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v)))
    (i : Fin k) :
    (isometricSuccessorCompatibleCyclicPointOrbitOfGenerated O hk base
      orientation period separated same_block_isometry).step i =
        generatedStep O orientation i :=
  rfl

/-- Nontrivial packaging lemma: generated data plus the period equation and
metric obligations give the downstream closed-placement interface. -/
theorem exists_closedPlacement_of_generated_closed_chain
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      generatedBlock O hk base orientation k = base)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <=
            _root_.eucDist
              (generatedPoint O hk base orientation i u)
              (generatedPoint O hk base orientation j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist
          (generatedPoint O hk base orientation i u)
          (generatedPoint O hk base orientation i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v))) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = generatedPoint O hk base orientation := by
  let orbit :=
    isometricSuccessorCompatibleCyclicPointOrbitOfGenerated O hk base
      orientation period separated same_block_isometry
  exact orbit.exists_closedPlacement_of_isometricSuccessorCompatibleCyclicPointOrbit

/-- The generated orbit agrees with the iterated-transition algebra from
`ClosedPlacementAlgebra` when started at the first block. -/
theorem generatedBlock_eq_closedPlacementAlgebra_iterated_from_zero
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (n : Nat) (hn : n < k) (v : LocalVertex) :
    generatedBlock O hk base orientation n v =
      ClosedPlacementAlgebra.iteratedTransitionBlock O hk
        (generatedPoint O hk base orientation) orientation ⟨0, hk⟩ n v := by
  revert v
  induction n with
  | zero =>
      intro v
      rfl
  | succ n ih =>
      intro v
      have hn_lt : n < k := by omega
      have hiterate :
          ((cyclicSucc hk)^[n]) ⟨0, hk⟩ = (⟨n, hn_lt⟩ : Fin k) := by
        apply Fin.ext
        rw [cyclicSucc_iterate_val]
        simp [Nat.mod_eq_of_lt hn_lt]
      have hblock :
          generatedBlock O hk base orientation n =
            ClosedPlacementAlgebra.iteratedTransitionBlock O hk
              (generatedPoint O hk base orientation) orientation ⟨0, hk⟩ n := by
        funext w
        exact ih hn_lt w
      simp [hiterate, orientationAt_of_lt hk orientation hn_lt, hblock]

end

end GeneratedClosedChain
end PachToth
end ErdosProblems1066
