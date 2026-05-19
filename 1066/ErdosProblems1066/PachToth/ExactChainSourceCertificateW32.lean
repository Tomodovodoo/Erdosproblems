import ErdosProblems1066.PachToth.ExactChainFamilyInhabitationW31
import ErdosProblems1066.PachToth.ExactChainFamilyClosureW30
import ErdosProblems1066.PachToth.ExactLocalGeometry
import ErdosProblems1066.PachToth.IndexedChain
import ErdosProblems1066.PachToth.FiniteGraph
import ErdosProblems1066.PachToth.RemainderConstruction
import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29
import ErdosProblems1066.PachToth.PositiveChainSmallBlocksW31

set_option autoImplicit false

/-!
# W32 exact-chain source certificate

This module refines the W31 exact-chain family inhabitation layer into explicit
source certificates.  The only constructors here start from exact small-block
data and an explicit large-tail source surface already present in W28/W29/W30.
The local geometry, indexed-chain, finite graph, and remainder facts are
recorded only by pointing back to the existing checked modules.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactChainSourceCertificateW32

noncomputable section

/-! ## Source and gate vocabulary -/

abbrev ExactChainFamilySourcePackage : Type :=
  ExactChainFamilyInhabitationW31.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourceGate : Prop :=
  ExactChainFamilyInhabitationW31.ExactChainFamilySourcePackageGate

abbrev ExactChainFamily : Type :=
  ExactChainFamilyInhabitationW31.ExactChainFamily

abbrev PositiveExactChainPackage : Type :=
  ExactChainFamilyInhabitationW31.PositiveExactChainPackage

abbrev ExactClosedChainPackage : Type :=
  ExactChainFamilyInhabitationW31.ExactClosedChainPackage

abbrev ExactBlocksOneThroughFive : Prop :=
  ExactChainFamilyInhabitationW31.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  ExactChainFamilyInhabitationW31.LargeExactBlockTargetsFromSix

abbrev SmallAndLargeExactBlockTargets : Prop :=
  ExactChainFamilyInhabitationW31.SmallAndLargeExactBlockTargets

abbrev LargeTailExactSourcePackage : Type :=
  ExactChainFamilyInhabitationW31.LargeTailExactSourcePackage

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  ExactChainFamilyClosureW30.LargeClosedPlacementFieldsFromSix

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  ExactChainFamilyClosureW30.LargeClosedPlacementFamilyFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  ExactChainFamilyClosureW30.LargeRawClosedPlacementFieldsFromSix

abbrev ClosureRemainingExactChainFamilyDependency : Prop :=
  ExactChainFamilyInhabitationW31.ClosureRemainingExactChainFamilyDependency

abbrev RemainderRemainingExactChainFamilyDependency : Prop :=
  ExactChainFamilyInhabitationW31.RemainderRemainingExactChainFamilyDependency

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  ExactChainFamilyInhabitationW31.RemainderSplitExactSourcePackageGate

abbrev SmallLengthExactBlockTargets : Prop :=
  PositiveChainSmallBlocksW31.SmallLengthExactBlockTargets

/-! ## Existing geometry and remainder certificates -/

structure ExistingGeometryAndRemainderCertificate : Prop where
  local_vertex_card : Fintype.card FiniteGraph.LocalVertex = 16
  local_edges_unit :
    forall u v : FiniteGraph.LocalVertex,
      FiniteGraph.adj u v = true ->
        _root_.eucDist (ExactLocalGeometry.localPoint u)
          (ExactLocalGeometry.localPoint v) = 1
  local_vertices_separated :
    forall u v : FiniteGraph.LocalVertex, Ne u v ->
      1 <= _root_.eucDist (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v)
  local_independent_card_le_six :
    forall s : Finset FiniteGraph.LocalVertex,
      FiniteGraph.IsIndependent s -> s.card <= 6
  indexed_chain_bound :
    forall {k : Nat} (hk : 0 < k),
      IndexedChain.IndexedChainRealization k hk ->
        Exists fun C : _root_.UDConfig (16 * k) =>
          forall s : Finset (Fin (16 * k)),
            C.IsIndep s -> s.card <= 5 * k
  remainder_bound :
    forall r : Nat,
      Exists fun C : _root_.UDConfig r =>
        forall s : Finset (Fin r),
          C.IsIndep s -> s.card <= Arithmetic.ceilDiv r 3

theorem existingGeometryAndRemainderCertificate :
    ExistingGeometryAndRemainderCertificate where
  local_vertex_card := FiniteGraph.localVertex_card
  local_edges_unit := ExactLocalGeometry.adj_unit_distance
  local_vertices_separated := ExactLocalGeometry.local_separated
  local_independent_card_le_six := FiniteGraph.alpha_le_six
  indexed_chain_bound := by
    intro k hk R
    exact IndexedChain.exists_config_with_independent_card_le_five_mul hk R
  remainder_bound := RemainderConstruction.exists_remainder_config

/-! ## Exact-block plus large-tail source fields -/

def exactBlocksOneThroughFiveOfSmallLengthTargets
    (small : SmallLengthExactBlockTargets) :
    ExactBlocksOneThroughFive :=
  PositiveChainSmallBlocksW31.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    small

theorem largeExactBlockTargetsFromSix_of_largeTailSourcePackage
    (large : LargeTailExactSourcePackage) :
    LargeExactBlockTargetsFromSix :=
  LargeTailExactSourceW28.remainingBlocker_of_largeTailExactSourcePackage
    large

def sourcePackageOfExactBlocksAndLargeExactTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyInhabitationW31.sourcePackageOfSmallBlocksAndLargeTail
    small large

def sourcePackageOfExactBlocksAndLargeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyInhabitationW31.sourcePackageOfLargeTailSourceAndSmallBlocks
    large small

def sourcePackageOfExactBlocksAndLargeClosedPlacementFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfSmallBlocksAndLargeClosedPlacementFields
    small large

def sourcePackageOfExactBlocksAndLargeClosedPlacementFamily
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFamilyFromSix) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfSmallBlocksAndLargeClosedPlacementFamily
    small large

def sourcePackageOfExactBlocksAndLargeRawFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfSmallBlocksAndLargeRawFields
    small large

theorem sourceGate_of_exactBlocks_and_largeExactTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactChainFamilySourceGate :=
  Nonempty.intro (sourcePackageOfExactBlocksAndLargeExactTail small large)

theorem sourceGate_of_exactBlocks_and_largeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    ExactChainFamilySourceGate :=
  Nonempty.intro (sourcePackageOfExactBlocksAndLargeTailSource small large)

theorem sourceGate_of_exactBlocks_and_largeClosedPlacementFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactChainFamilySourceGate :=
  Nonempty.intro
    (sourcePackageOfExactBlocksAndLargeClosedPlacementFields small large)

theorem sourceGate_of_exactBlocks_and_largeClosedPlacementFamily
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFamilyFromSix) :
    ExactChainFamilySourceGate :=
  Nonempty.intro
    (sourcePackageOfExactBlocksAndLargeClosedPlacementFamily small large)

theorem sourceGate_of_exactBlocks_and_largeRawFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactChainFamilySourceGate :=
  Nonempty.intro (sourcePackageOfExactBlocksAndLargeRawFields small large)

theorem sourceGate_of_smallLengthTargets_and_largeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    ExactChainFamilySourceGate :=
  sourceGate_of_exactBlocks_and_largeTailSource
    (exactBlocksOneThroughFiveOfSmallLengthTargets small) large

theorem sourceGate_of_smallLengthTargets_and_largeClosedPlacementFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactChainFamilySourceGate :=
  sourceGate_of_exactBlocks_and_largeClosedPlacementFields
    (exactBlocksOneThroughFiveOfSmallLengthTargets small) large

theorem sourceGate_of_smallLengthTargets_and_largeRawFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactChainFamilySourceGate :=
  sourceGate_of_exactBlocks_and_largeRawFields
    (exactBlocksOneThroughFiveOfSmallLengthTargets small) large

/-! ## Field records with their precise handoff to the gate -/

structure ExactBlocksAndLargeTailSourceFields where
  small : ExactBlocksOneThroughFive
  largeTail : LargeTailExactSourcePackage

namespace ExactBlocksAndLargeTailSourceFields

def largeExactTail
    (S : ExactBlocksAndLargeTailSourceFields) :
    LargeExactBlockTargetsFromSix :=
  largeExactBlockTargetsFromSix_of_largeTailSourcePackage S.largeTail

def sourcePackage
    (S : ExactBlocksAndLargeTailSourceFields) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfExactBlocksAndLargeTailSource S.small S.largeTail

theorem sourceGate
    (S : ExactBlocksAndLargeTailSourceFields) :
    ExactChainFamilySourceGate :=
  Nonempty.intro S.sourcePackage

end ExactBlocksAndLargeTailSourceFields

structure ExactBlocksAndLargeClosedPlacementFields where
  small : ExactBlocksOneThroughFive
  largeFields : LargeClosedPlacementFieldsFromSix

namespace ExactBlocksAndLargeClosedPlacementFields

def sourcePackage
    (S : ExactBlocksAndLargeClosedPlacementFields) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfExactBlocksAndLargeClosedPlacementFields
    S.small S.largeFields

theorem sourceGate
    (S : ExactBlocksAndLargeClosedPlacementFields) :
    ExactChainFamilySourceGate :=
  Nonempty.intro S.sourcePackage

end ExactBlocksAndLargeClosedPlacementFields

structure ExactBlocksAndLargeRawFields where
  small : ExactBlocksOneThroughFive
  rawFields : LargeRawClosedPlacementFieldsFromSix

namespace ExactBlocksAndLargeRawFields

def sourcePackage
    (S : ExactBlocksAndLargeRawFields) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfExactBlocksAndLargeRawFields S.small S.rawFields

theorem sourceGate
    (S : ExactBlocksAndLargeRawFields) :
    ExactChainFamilySourceGate :=
  Nonempty.intro S.sourcePackage

end ExactBlocksAndLargeRawFields

structure SmallLengthBlocksAndLargeTailSourceFields where
  smallTargets : SmallLengthExactBlockTargets
  largeTail : LargeTailExactSourcePackage

namespace SmallLengthBlocksAndLargeTailSourceFields

def exactBlocks
    (S : SmallLengthBlocksAndLargeTailSourceFields) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFiveOfSmallLengthTargets S.smallTargets

def toExactBlocksAndLargeTailSourceFields
    (S : SmallLengthBlocksAndLargeTailSourceFields) :
    ExactBlocksAndLargeTailSourceFields where
  small := S.exactBlocks
  largeTail := S.largeTail

def sourcePackage
    (S : SmallLengthBlocksAndLargeTailSourceFields) :
    ExactChainFamilySourcePackage :=
  S.toExactBlocksAndLargeTailSourceFields.sourcePackage

theorem sourceGate
    (S : SmallLengthBlocksAndLargeTailSourceFields) :
    ExactChainFamilySourceGate :=
  S.toExactBlocksAndLargeTailSourceFields.sourceGate

end SmallLengthBlocksAndLargeTailSourceFields

theorem nonempty_exactBlocksAndLargeTailSourceFields_iff :
    Nonempty ExactBlocksAndLargeTailSourceFields <->
      ExactBlocksOneThroughFive /\ Nonempty LargeTailExactSourcePackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact And.intro S.small (Nonempty.intro S.largeTail)
  case mpr =>
    intro h
    cases h.right with
    | intro large =>
        exact
          Nonempty.intro
            { small := h.left
              largeTail := large }

theorem sourceGate_of_exactBlocksAndLargeTailSourceFields_nonempty
    (H : Nonempty ExactBlocksAndLargeTailSourceFields) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact S.sourceGate

theorem sourceGate_of_exactBlocksAndLargeClosedPlacementFields_nonempty
    (H : Nonempty ExactBlocksAndLargeClosedPlacementFields) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact S.sourceGate

theorem sourceGate_of_exactBlocksAndLargeRawFields_nonempty
    (H : Nonempty ExactBlocksAndLargeRawFields) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact S.sourceGate

/-! ## W31/W30 consequences from the same source gate -/

theorem closureDependency_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    ClosureRemainingExactChainFamilyDependency :=
  ExactChainFamilyInhabitationW31.closureDependency_of_sourceGate H

theorem remainderDependency_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    RemainderRemainingExactChainFamilyDependency :=
  ExactChainFamilyInhabitationW31.remainderDependency_of_sourceGate H

theorem remainderSplitExactSourcePackageGate_of_sourceGate
    (H : ExactChainFamilySourceGate) :
    RemainderSplitExactSourcePackageGate :=
  ExactChainFamilyInhabitationW31.remainderSplitExactSourcePackageGate_of_sourceGate
    H

theorem sourceGate_iff_exactBlocks_and_largeExactTail :
    ExactChainFamilySourceGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix :=
  ExactChainFamilyInhabitationW31.sourceGate_iff_smallBlocks_and_largeTail

theorem closureDependency_of_exactBlocks_and_largeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    ClosureRemainingExactChainFamilyDependency :=
  closureDependency_of_sourceGate
    (sourceGate_of_exactBlocks_and_largeTailSource small large)

theorem remainderDependency_of_exactBlocks_and_largeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    RemainderRemainingExactChainFamilyDependency :=
  remainderDependency_of_sourceGate
    (sourceGate_of_exactBlocks_and_largeTailSource small large)

/-! ## Compact certificate record -/

structure ExactChainSourceCertificate : Prop where
  geometry_and_remainder :
    ExistingGeometryAndRemainderCertificate
  source_iff_exact_blocks_and_large_tail :
    ExactChainFamilySourceGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix
  exact_blocks_and_large_tail_to_source :
    ExactBlocksOneThroughFive ->
      LargeExactBlockTargetsFromSix -> ExactChainFamilySourceGate
  exact_blocks_and_large_tail_package_to_source :
    ExactBlocksOneThroughFive ->
      LargeTailExactSourcePackage -> ExactChainFamilySourceGate
  exact_blocks_and_large_closed_fields_to_source :
    ExactBlocksOneThroughFive ->
      LargeClosedPlacementFieldsFromSix -> ExactChainFamilySourceGate
  exact_blocks_and_large_closed_family_to_source :
    ExactBlocksOneThroughFive ->
      LargeClosedPlacementFamilyFromSix -> ExactChainFamilySourceGate
  exact_blocks_and_large_raw_fields_to_source :
    ExactBlocksOneThroughFive ->
      LargeRawClosedPlacementFieldsFromSix -> ExactChainFamilySourceGate
  small_length_blocks_and_large_tail_package_to_source :
    SmallLengthExactBlockTargets ->
      LargeTailExactSourcePackage -> ExactChainFamilySourceGate
  source_to_closure_dependency :
    ExactChainFamilySourceGate ->
      ClosureRemainingExactChainFamilyDependency
  source_to_remainder_dependency :
    ExactChainFamilySourceGate ->
      RemainderRemainingExactChainFamilyDependency
  source_to_remainder_split_package :
    ExactChainFamilySourceGate ->
      RemainderSplitExactSourcePackageGate

theorem exactChainSourceCertificate :
    ExactChainSourceCertificate where
  geometry_and_remainder := existingGeometryAndRemainderCertificate
  source_iff_exact_blocks_and_large_tail :=
    sourceGate_iff_exactBlocks_and_largeExactTail
  exact_blocks_and_large_tail_to_source :=
    sourceGate_of_exactBlocks_and_largeExactTail
  exact_blocks_and_large_tail_package_to_source :=
    sourceGate_of_exactBlocks_and_largeTailSource
  exact_blocks_and_large_closed_fields_to_source :=
    sourceGate_of_exactBlocks_and_largeClosedPlacementFields
  exact_blocks_and_large_closed_family_to_source :=
    sourceGate_of_exactBlocks_and_largeClosedPlacementFamily
  exact_blocks_and_large_raw_fields_to_source :=
    sourceGate_of_exactBlocks_and_largeRawFields
  small_length_blocks_and_large_tail_package_to_source :=
    sourceGate_of_smallLengthTargets_and_largeTailSource
  source_to_closure_dependency := closureDependency_of_sourceGate
  source_to_remainder_dependency := remainderDependency_of_sourceGate
  source_to_remainder_split_package :=
    remainderSplitExactSourcePackageGate_of_sourceGate

end

end ExactChainSourceCertificateW32
end PachToth

namespace Verified

abbrev PachTothW32ExactChainFamilySourcePackage : Type :=
  PachToth.ExactChainSourceCertificateW32.ExactChainFamilySourcePackage

abbrev PachTothW32ExactChainFamilySourceGate : Prop :=
  PachToth.ExactChainSourceCertificateW32.ExactChainFamilySourceGate

abbrev PachTothW32ExactBlocksOneThroughFive : Prop :=
  PachToth.ExactChainSourceCertificateW32.ExactBlocksOneThroughFive

abbrev PachTothW32LargeTailExactSourcePackage : Type :=
  PachToth.ExactChainSourceCertificateW32.LargeTailExactSourcePackage

abbrev PachTothW32LargeClosedPlacementFieldsFromSix : Type :=
  PachToth.ExactChainSourceCertificateW32.LargeClosedPlacementFieldsFromSix

abbrev PachTothW32LargeRawClosedPlacementFieldsFromSix : Type :=
  PachToth.ExactChainSourceCertificateW32.LargeRawClosedPlacementFieldsFromSix

abbrev PachTothW32ExactChainSourceCertificate : Prop :=
  PachToth.ExactChainSourceCertificateW32.ExactChainSourceCertificate

theorem pachtoth_w32_sourceGate_iff_exactBlocks_and_largeExactTail :
    PachTothW32ExactChainFamilySourceGate <->
      PachTothW32ExactBlocksOneThroughFive /\
        PachToth.ExactChainSourceCertificateW32.LargeExactBlockTargetsFromSix :=
  PachToth.ExactChainSourceCertificateW32.sourceGate_iff_exactBlocks_and_largeExactTail

theorem pachtoth_w32_sourceGate_of_exactBlocks_and_largeTailSource
    (small : PachTothW32ExactBlocksOneThroughFive)
    (large : PachTothW32LargeTailExactSourcePackage) :
    PachTothW32ExactChainFamilySourceGate :=
  PachToth.ExactChainSourceCertificateW32.sourceGate_of_exactBlocks_and_largeTailSource
    small large

theorem pachtoth_w32_sourceGate_of_exactBlocks_and_largeClosedPlacementFields
    (small : PachTothW32ExactBlocksOneThroughFive)
    (large : PachTothW32LargeClosedPlacementFieldsFromSix) :
    PachTothW32ExactChainFamilySourceGate :=
  PachToth.ExactChainSourceCertificateW32.sourceGate_of_exactBlocks_and_largeClosedPlacementFields
    small large

theorem pachtoth_w32_sourceGate_of_exactBlocks_and_largeRawFields
    (small : PachTothW32ExactBlocksOneThroughFive)
    (large : PachTothW32LargeRawClosedPlacementFieldsFromSix) :
    PachTothW32ExactChainFamilySourceGate :=
  PachToth.ExactChainSourceCertificateW32.sourceGate_of_exactBlocks_and_largeRawFields
    small large

theorem pachtoth_w32_exactChainSourceCertificate :
    PachTothW32ExactChainSourceCertificate :=
  PachToth.ExactChainSourceCertificateW32.exactChainSourceCertificate

end Verified
end ErdosProblems1066
