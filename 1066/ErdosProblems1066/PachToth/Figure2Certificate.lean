import ErdosProblems1066.PachToth.FiniteGraph
import ErdosProblems1066.PachToth.OrientationData
import ErdosProblems1066.PachToth.OrientedCrossBlockGeometry
import ErdosProblems1066.PachToth.ConnectorEquationFacts

/-!
# Pach--Toth Figure 2 finite certificate

This module is a bundling layer for the currently proved Figure 2 data.  It
does not assert a non-rigid closed placement.  The finite graph facts are
packaged as kernel-checked certificates, while the same/opposite transition
data below records exactly which connector-unit obligations would have to be
supplied by a future geometric construction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Figure2Certificate

open FiniteGraph
open FiniteGraph.LocalVertex
open OrientationData

noncomputable section

abbrev R2 := Prod Real Real

/-- The complete proof-used local finite graph certificate currently available
for the Pach--Toth Figure 2 block, together with the checked one-step
connector consequences and the known translation/oriented-grid obstructions.
This is not a complete source transcription of every Figure 2 primitive. -/
structure Figure2LocalFiniteCertificate where
  localVertex_card : Fintype.card LocalVertex = 16
  adj_irrefl : forall v : LocalVertex, adj v v = false
  adj_symm : forall u v : LocalVertex, adj u v = adj v u
  same_part_eq_or_adj :
    forall u v : LocalVertex, part u = part v -> u = v \/ adj u v = true
  independent_part_injOn :
    forall {s : Finset LocalVertex}, IsIndependent s ->
      Set.InjOn part (s : Set LocalVertex)
  extractedSixSet_card : extractedSixSet.card = 6
  extractedSixSet_independent : IsIndependent extractedSixSet
  alpha_le_six :
    forall s : Finset LocalVertex, IsIndependent s -> s.card <= 6
  unique_size_six_independent :
    forall s : Finset LocalVertex, IsIndependent s -> s.card = 6 ->
      s = extractedSixSet
  extractedSixSet_contains_connectors :
    T2_2 ∈ extractedSixSet /\ T4_0 ∈ extractedSixSet
  part_zero_eq_r : forall v : LocalVertex, part v = 0 -> v = .r
  part_one_ne_r : forall v : LocalVertex, part v = 1 -> Ne .r v
  part_two_ne_r : forall v : LocalVertex, part v = 2 -> Ne .r v
  part_three_ne_T0_0 : forall v : LocalVertex, part v = 3 -> Ne T0_0 v
  part_four_ne_T1_1 : forall v : LocalVertex, part v = 4 -> Ne T1_1 v
  part_five_ne_T3_0 : forall v : LocalVertex, part v = 5 -> Ne T3_0 v
  part_one_forced_by_r :
    forall v : LocalVertex, part v = 1 -> adj .r v = false -> v = T0_0
  part_two_forced_by_r :
    forall v : LocalVertex, part v = 2 -> adj .r v = false -> v = T1_1
  part_three_forced_by_T0_0 :
    forall v : LocalVertex, part v = 3 -> adj T0_0 v = false -> v = T2_2
  part_four_forced_by_T1_1 :
    forall v : LocalVertex, part v = 4 -> adj T1_1 v = false -> v = T3_0
  part_five_forced_by_T3_0 :
    forall v : LocalVertex, part v = 5 -> adj T3_0 v = false -> v = T4_0
  nextForbidden_connector_source :
    forall v : LocalVertex,
      v ∈ nextForbidden -> CrossBlock.NextConnector T2_2 v \/
        CrossBlock.NextConnector T4_0 v
  early_not_forbidden_eq_or_adj :
    forall u v : LocalVertex,
      u ∉ nextForbidden ->
      v ∉ nextForbidden ->
      (part u : Nat) <= 2 ->
      (part v : Nat) <= 2 ->
      u = v \/ adj u v = true
  late_part_mem :
    forall v : LocalVertex,
      Not ((part v : Nat) <= 2) ->
      part v ∈ ({(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)} : Finset (Fin 6))
  next_block_after_forbidden_le_four :
    forall s : Finset LocalVertex,
      IsIndependent s ->
      (forall v : LocalVertex, v ∈ s -> v ∉ nextForbidden) ->
      s.card <= 4
  crossIndependent_forbids_nextForbidden :
    forall {left right : Finset LocalVertex},
      CrossBlock.CrossIndependent left right ->
      T2_2 ∈ left ->
      T4_0 ∈ left ->
      forall {v : LocalVertex}, v ∈ right -> v ∉ nextForbidden
  connectorRule_of_cyclicCrossIndependent :
    forall {k : Nat} (hk : 0 < k) {blocks : Chain.BlockSelection k},
      CrossBlock.CyclicCrossIndependent hk blocks ->
      Chain.ConnectorRule hk blocks
  selected_card_le_five_mul :
    forall {k : Nat} (hk : 0 < k) (blocks : Chain.BlockSelection k),
      Chain.BlocksIndependent blocks ->
      CrossBlock.CyclicCrossIndependent hk blocks ->
      (Finset.univ.sum fun i : Fin k => (blocks i).card) <= 5 * k
  no_single_translation_realizes_all_connector_units :
    forall d : ExactLocalGeometry.GridPoint,
      Not (Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T2_2)
              (CrossBlockGeometry.translatedLocalPoint d T1_1) = 1 /\
            Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T2_2)
              (CrossBlockGeometry.translatedLocalPoint d T1_2) = 1 /\
            Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T4_0)
              (CrossBlockGeometry.translatedLocalPoint d T0_0) = 1 /\
            Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T4_0)
              (CrossBlockGeometry.translatedLocalPoint d T0_2) = 1)
  no_oriented_grid_placement_realizes_all_connector_units :
    forall (o : OrientedCrossBlockGeometry.GridOrientation)
        (d : ExactLocalGeometry.GridPoint),
      Not (Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T2_2)
              (OrientedCrossBlockGeometry.orientedTranslatedLocalPoint d o T1_1) = 1 /\
            Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T2_2)
              (OrientedCrossBlockGeometry.orientedTranslatedLocalPoint d o T1_2) = 1 /\
            Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T4_0)
              (OrientedCrossBlockGeometry.orientedTranslatedLocalPoint d o T0_0) = 1 /\
            Geometry.Distance.eucDist
              (ExactLocalGeometry.localPoint T4_0)
              (OrientedCrossBlockGeometry.orientedTranslatedLocalPoint d o T0_2) = 1)
  not_all_four_connector_equations :
    forall x y eta : Real,
      eta ^ 2 = (3 : Real) / 4 ->
      Not (ConnectorEquationFacts.eq211 x y eta /\
        ConnectorEquationFacts.eq212 x y eta /\
        ConnectorEquationFacts.eq400 x y eta /\
        ConnectorEquationFacts.eq402 x y eta)

/-- The canonical certificate assembled from the already checked local
finite-graph lemmas and obstruction lemmas. -/
def figure2LocalFiniteCertificate : Figure2LocalFiniteCertificate where
  localVertex_card := FiniteGraph.localVertex_card
  adj_irrefl := FiniteGraph.adj_irrefl
  adj_symm := FiniteGraph.adj_symm
  same_part_eq_or_adj := FiniteGraph.same_part_eq_or_adj
  independent_part_injOn := by
    intro s hs
    exact FiniteGraph.independent_part_injOn hs
  extractedSixSet_card := FiniteGraph.extractedSixSet_card
  extractedSixSet_independent := FiniteGraph.extractedSixSet_independent
  alpha_le_six := FiniteGraph.alpha_le_six
  unique_size_six_independent := FiniteGraph.unique_size_six_independent
  extractedSixSet_contains_connectors :=
    FiniteGraph.extractedSixSet_contains_connectors
  part_zero_eq_r := FiniteGraph.part_zero_eq_r
  part_one_ne_r := FiniteGraph.part_one_ne_r
  part_two_ne_r := FiniteGraph.part_two_ne_r
  part_three_ne_T0_0 := FiniteGraph.part_three_ne_T0_0
  part_four_ne_T1_1 := FiniteGraph.part_four_ne_T1_1
  part_five_ne_T3_0 := FiniteGraph.part_five_ne_T3_0
  part_one_forced_by_r := FiniteGraph.part_one_forced_by_r
  part_two_forced_by_r := FiniteGraph.part_two_forced_by_r
  part_three_forced_by_T0_0 := FiniteGraph.part_three_forced_by_T0_0
  part_four_forced_by_T1_1 := FiniteGraph.part_four_forced_by_T1_1
  part_five_forced_by_T3_0 := FiniteGraph.part_five_forced_by_T3_0
  nextForbidden_connector_source := CrossBlock.nextForbidden_connector_source
  early_not_forbidden_eq_or_adj := FiniteGraph.early_not_forbidden_eq_or_adj
  late_part_mem := FiniteGraph.late_part_mem
  next_block_after_forbidden_le_four :=
    FiniteGraph.next_block_after_forbidden_le_four
  crossIndependent_forbids_nextForbidden := by
    intro left right hcross hT2 hT4 v hv
    exact CrossBlock.crossIndependent_forbids_nextForbidden hcross hT2 hT4 hv
  connectorRule_of_cyclicCrossIndependent := by
    intro k hk blocks hcross
    exact CrossBlock.connectorRule_of_cyclicCrossIndependent hk hcross
  selected_card_le_five_mul := by
    intro k hk blocks hindep hcross
    exact CrossBlock.selected_card_le_five_mul hk blocks hindep hcross
  no_single_translation_realizes_all_connector_units :=
    CrossBlockGeometry.no_single_translation_realizes_all_connector_units
  no_oriented_grid_placement_realizes_all_connector_units :=
    OrientedCrossBlockGeometry.no_oriented_grid_placement_realizes_all_connector_units
  not_all_four_connector_equations :=
    ConnectorEquationFacts.not_all_four_connector_equations

/-- There are exactly two relative orientation labels in the current audit:
`same` and `opposite`. -/
theorem blockOrientation_card : Fintype.card BlockOrientation = 2 := by
  decide

/-- Case split exposing the complete current relative-orientation alphabet. -/
theorem blockOrientation_eq_same_or_opposite (o : BlockOrientation) :
    o = BlockOrientation.same \/ o = BlockOrientation.opposite := by
  cases o <;> simp

/-- A same-orientation transition map built only from a proposed `placeNext`
function.  This carries no metric claim. -/
def sameTransition
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) :
    OrientedTransition where
  orientation := BlockOrientation.same
  placeNext := placeNext

/-- An opposite-orientation transition map built only from a proposed
`placeNext` function.  This carries no metric claim. -/
def oppositeTransition
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) :
    OrientedTransition where
  orientation := BlockOrientation.opposite
  placeNext := placeNext

@[simp]
theorem sameTransition_orientation
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) :
    (sameTransition placeNext).orientation = BlockOrientation.same :=
  rfl

@[simp]
theorem oppositeTransition_orientation
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) :
    (oppositeTransition placeNext).orientation = BlockOrientation.opposite :=
  rfl

/-- The reusable geometric obligations for proposed same/opposite transition
maps.  Supplying this structure is exactly supplying the successor connector
unit-distance checks for both orientations; no such structure is constructed
in this file. -/
structure SameOppositeTransitionObligations where
  samePlaceNext : (LocalVertex -> R2) -> LocalVertex -> R2
  oppositePlaceNext : (LocalVertex -> R2) -> LocalVertex -> R2
  same_connector_unit_edges :
    forall (source : LocalVertex -> R2) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (source u) (samePlaceNext source v) = 1
  opposite_connector_unit_edges :
    forall (source : LocalVertex -> R2) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (source u) (oppositePlaceNext source v) = 1

namespace SameOppositeTransitionObligations

/-- The same-orientation transition associated to the supplied obligations. -/
def same (O : SameOppositeTransitionObligations) : OrientedTransition :=
  sameTransition O.samePlaceNext

/-- The opposite-orientation transition associated to the supplied obligations. -/
def opposite (O : SameOppositeTransitionObligations) : OrientedTransition :=
  oppositeTransition O.oppositePlaceNext

@[simp]
theorem same_orientation (O : SameOppositeTransitionObligations) :
    O.same.orientation = BlockOrientation.same :=
  rfl

@[simp]
theorem opposite_orientation (O : SameOppositeTransitionObligations) :
    O.opposite.orientation = BlockOrientation.opposite :=
  rfl

/-- Select the transition map for an orientation label. -/
def transitionFor (O : SameOppositeTransitionObligations) :
    BlockOrientation -> OrientedTransition
  | BlockOrientation.same => O.same
  | BlockOrientation.opposite => O.opposite

@[simp]
theorem transitionFor_same (O : SameOppositeTransitionObligations) :
    O.transitionFor BlockOrientation.same = O.same :=
  rfl

@[simp]
theorem transitionFor_opposite (O : SameOppositeTransitionObligations) :
    O.transitionFor BlockOrientation.opposite = O.opposite :=
  rfl

/-- The selected transition has the selected orientation label. -/
theorem transitionFor_orientation
    (O : SameOppositeTransitionObligations) (o : BlockOrientation) :
    (O.transitionFor o).orientation = o := by
  cases o <;> rfl

/-- The connector-unit obligation for the selected orientation. -/
theorem transitionFor_connector_unit_edges
    (O : SameOppositeTransitionObligations)
    (o : BlockOrientation) (source : LocalVertex -> R2) :
    forall u v : LocalVertex,
      CrossBlock.NextConnector u v ->
        _root_.eucDist
          (source u) ((O.transitionFor o).placeNext source v) = 1 := by
  cases o
  · exact O.same_connector_unit_edges source
  · exact O.opposite_connector_unit_edges source

/-- A selected same/opposite transition becomes an `OrientationData`
transition certificate once the target block is definitionally or explicitly
identified with the chosen `placeNext`. -/
def transitionCertificateFor
    (O : SameOppositeTransitionObligations)
    (o : BlockOrientation)
    (source target : LocalVertex -> R2)
    (htarget :
      forall v : LocalVertex, target v = (O.transitionFor o).placeNext source v) :
    TransitionCertificate source target where
  transition := O.transitionFor o
  target_eq_placeNext := htarget
  connector_unit_edges := O.transitionFor_connector_unit_edges o source

/-- If a closed chain supplies an orientation sequence and proves every
successor block is obtained by the selected same/opposite transition, then the
transition layer can be repackaged as `OrientedClosedChainPlacement`.  Global
separation and same-block isometry remain explicit hypotheses. -/
def toOrientedClosedChainPlacement
    (O : SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (Arithmetic.cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist (point i u) (point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v))) :
    OrientedClosedChainPlacement k hk where
  point := point
  transition := by
    intro i
    exact O.transitionCertificateFor (orientation i)
      (point i) (point (Arithmetic.cyclicSucc hk i))
      (target_eq_placeNext i)
  separated := separated
  same_block_isometry := same_block_isometry

@[simp]
theorem toOrientedClosedChainPlacement_orientationSequence
    (O : SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (Arithmetic.cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist (point i u) (point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)))
    (i : Fin k) :
    (O.toOrientedClosedChainPlacement point orientation target_eq_placeNext
        separated same_block_isometry).orientationSequence i = orientation i := by
  simp [toOrientedClosedChainPlacement,
    OrientedClosedChainPlacement.orientationSequence,
    transitionCertificateFor, transitionFor_orientation]

end SameOppositeTransitionObligations

end

end Figure2Certificate
end PachToth
end ErdosProblems1066
