import ErdosProblems1066.Swanepoel.NoCutConcreteEliminationW26
import ErdosProblems1066.Swanepoel.DeficientNeighborhood

set_option autoImplicit false

/-!
# W27 partition-local deletion bridge for no-cut

This file is deliberately scoped to the W26 no-cut deletion frontier.  A
cut-vertex partition does not itself contain a closed-neighborhood deletion
rule, so the checked contribution here is the exact local-deletion dependency:
honest partition-scoped local deletion data is packaged into the W26
eliminators, and the smallest certificate-level dependency is shown to be
logically equivalent to eliminating the concrete cut-vertex blocker.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutLocalDeletionConcreteW27

open CutVertexInterface
open MinimalCounterexample
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoCutConcreteEliminationW26

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutConcreteEliminationW26.MinimalCutVertexBlocker

/-- Pointwise closed-neighborhood payload for one live cut partition. -/
abbrev CutPartitionTupledClosedNeighborhood
    {n : Nat} (C : _root_.UDConfig n) : Prop :=
  Exists fun deleted : Finset (Fin n) =>
  Exists fun reinsertion : Finset (Fin n) =>
    IsClosedNeighborhood C reinsertion deleted /\
    (Exists fun center : Fin n =>
      deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
    2 <= reinsertion.card /\
    reinsertion.card <= 8 /\
    C.IsIndep reinsertion

/-- Pointwise direct-card-bound payload for one live cut partition. -/
abbrev CutPartitionTupledDirectCardBound
    {n : Nat} (C : _root_.UDConfig n) : Prop :=
  Exists fun deleted : Finset (Fin n) =>
  Exists fun reinsertion : Finset (Fin n) =>
    IsClosedNeighborhood C reinsertion deleted /\
    (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
    reinsertion.Nonempty /\
    reinsertion.card <= 8 /\
    C.IsIndep reinsertion

/-- Pointwise deficient-neighborhood payload for one live cut partition. -/
abbrev CutPartitionDeficientNeighborhood
    {n : Nat} (C : _root_.UDConfig n) : Prop :=
  Exists fun S : Finset (Fin n) =>
    S.Nonempty /\
    C.IsIndep S /\
    S.card <= 8 /\
    (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card <
      3 * S.card

/-- The live-partition source needed for the no-cut route: every supplied
minimal-failure cut partition produces one of the concrete W27 payloads. -/
abbrev LiveCutPartitionDeletionPayloadSource : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) (_P : CutVertexPartition C),
      CutPartitionTupledClosedNeighborhood C \/
      CutPartitionTupledDirectCardBound C \/
      CutPartitionDeficientNeighborhood C

/-- Tupled partition-scoped closed-neighborhood deletion data. -/
abbrev CutPartitionTupledClosedNeighborhoodDeletionData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (Exists fun center : Fin n =>
          deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
        2 <= reinsertion.card /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion

/-- Tupled partition-scoped direct-card-bound local deletion data. -/
abbrev CutPartitionTupledDirectCardBoundDeletionData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
        reinsertion.Nonempty /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion

/-- Partition-scoped deficient-neighborhood data, a concrete direct-card
local-deletion source when such a small independent set is supplied. -/
abbrev CutPartitionDeficientNeighborhoodDeletionData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C ->
      Exists fun S : Finset (Fin n) =>
        S.Nonempty /\
        C.IsIndep S /\
        S.card <= 8 /\
        (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card <
          3 * S.card

/-- If the actual cut-side geometry proves the outside-neighborhood
inequality for every small cross-side independent pair, then it supplies the
deficient-neighborhood deletion data directly.  The pair itself is the one
provided by `CutVertexPartition.exists_small_independent_pair_left_right`. -/
theorem cutPartitionDeficientNeighborhoodDeletionData_of_crossSideSmallPairOutsideBound
    (H :
      forall {n : Nat} (C : _root_.UDConfig n)
        (_hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)
        (S : Finset (Fin n)),
          S.Nonempty ->
          C.IsIndep S ->
          S.card <= 8 ->
          S <= P.left ∪ P.right ->
          (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card <
            3 * S.card) :
    CutPartitionDeficientNeighborhoodDeletionData := by
  intro n C hmin P
  rcases P.exists_small_independent_pair_left_right with
    ⟨S, hS, hindep, hupper, hsubset⟩
  exact ⟨S, hS, hindep, hupper, H C hmin P S hS hindep hupper hsubset⟩

/-- Pointwise conversion from an explicit cut-side cover of a cross pair's
outside neighborhood.  The remaining geometric task is the concrete
`cover.card < 6` inequality for some left/right pair. -/
theorem cutPartitionDeficientNeighborhood_of_crossPairSideNeighborhoodCover_lt_six
    {n : Nat} {C : _root_.UDConfig n}
    (P : CutVertexPartition C) {l r : Fin n}
    (hl : l ∈ P.left) (hr : r ∈ P.right)
    (hcover : (P.crossPairSideNeighborhoodCover l r).card < 6) :
    CutPartitionDeficientNeighborhood C := by
  have hne : l ≠ r := by
    intro h
    subst r
    exact (Finset.disjoint_left.mp P.disjoint) hl hr
  let S : Finset (Fin n) := {l, r}
  have hS : S.Nonempty := ⟨l, by simp [S]⟩
  have hcard : S.card = 2 := by
    simp [S, hne]
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · simpa [S] using P.independent_pair_left_right hl hr
  · omega
  · have houtside :
        (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card < 6 := by
      simpa [S] using
        P.outsideNeighborhoodOf_pair_card_lt_six_of_cover_card_lt_six
          hl hr hcover
    have htarget : 3 * S.card = 6 := by
      omega
    simpa [htarget] using houtside

/-- Concrete reduced geometry target for the deficient-neighborhood branch:
every live minimal-failure cut partition has a cross-side pair whose explicit
cut-side outside-neighborhood cover has fewer than six vertices. -/
abbrev CutPartitionCrossPairSideNeighborhoodCoverBound : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C),
      Exists fun l : Fin n =>
      Exists fun r : Fin n =>
        l ∈ P.left /\
        r ∈ P.right /\
        (P.crossPairSideNeighborhoodCover l r).card < 6

/-- The explicit cross-pair cover bound is enough to inhabit the W27
deficient-neighborhood deletion data. -/
theorem cutPartitionDeficientNeighborhoodDeletionData_of_crossPairSideNeighborhoodCoverBound
    (H : CutPartitionCrossPairSideNeighborhoodCoverBound) :
    CutPartitionDeficientNeighborhoodDeletionData := by
  intro n C hmin P
  rcases H C hmin P with ⟨l, r, hl, hr, hcover⟩
  exact
    cutPartitionDeficientNeighborhood_of_crossPairSideNeighborhoodCover_lt_six
      P hl hr hcover

/-- The same reduced geometry target, in the live mixed-payload spelling
consumed by W30/W32. -/
theorem liveCutPartitionDeletionPayloadSource_of_crossPairSideNeighborhoodCoverBound
    (H : CutPartitionCrossPairSideNeighborhoodCoverBound) :
    LiveCutPartitionDeletionPayloadSource := by
  intro n C hmin P
  exact Or.inr
    (Or.inr
      ((cutPartitionDeficientNeighborhoodDeletionData_of_crossPairSideNeighborhoodCoverBound
        H) C hmin P))

private theorem crossPairSideNeighborhoodCover_card_lt_six_of_sideNeighborCards_le_four
    {n : Nat} {C : _root_.UDConfig n}
    (P : CutVertexPartition C) {l r : Fin n}
    (hside :
      (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
        (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card <= 4) :
    (P.crossPairSideNeighborhoodCover l r).card < 6 := by
  classical
  let leftNeighbors : Finset (Fin n) :=
    P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1
  let rightNeighbors : Finset (Fin n) :=
    P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1
  have hcover :
      (P.crossPairSideNeighborhoodCover l r).card <=
        leftNeighbors.card + rightNeighbors.card + 1 := by
    calc
      (P.crossPairSideNeighborhoodCover l r).card
          = (insert P.cut (leftNeighbors ∪ rightNeighbors)).card := by
              rfl
      _ <= (leftNeighbors ∪ rightNeighbors).card + 1 :=
              Finset.card_insert_le _ _
      _ <= (leftNeighbors.card + rightNeighbors.card) + 1 :=
              Nat.add_le_add_right
                (Finset.card_union_le leftNeighbors rightNeighbors) 1
      _ = leftNeighbors.card + rightNeighbors.card + 1 := by
              omega
  have hside' : leftNeighbors.card + rightNeighbors.card <= 4 := by
    simpa [leftNeighbors, rightNeighbors] using hside
  omega

theorem cutPartitionDeficientNeighborhood_of_sideNeighborCardBound
    {n : Nat} {C : _root_.UDConfig n}
    (P : CutVertexPartition C) {l r : Fin n}
    (hl : l ∈ P.left) (hr : r ∈ P.right)
    (hside :
      (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
        (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card <= 4) :
    CutPartitionDeficientNeighborhood C :=
  cutPartitionDeficientNeighborhood_of_crossPairSideNeighborhoodCover_lt_six
    P hl hr
    (crossPairSideNeighborhoodCover_card_lt_six_of_sideNeighborCards_le_four
      P hside)

/-- A still more concrete reduced geometry target: choose a left/right pair
whose same-side unit-neighbor counts add to at most four.  The explicit cover
then has cardinality at most five, which is exactly the deficient-neighborhood
threshold for a two-point independent set. -/
abbrev CutPartitionCrossPairSideNeighborCardBound : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C),
      Exists fun l : Fin n =>
      Exists fun r : Fin n =>
        l ∈ P.left /\
        r ∈ P.right /\
        (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
          (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card <= 4

theorem cutPartitionCrossPairSideNeighborhoodCoverBound_of_sideNeighborCardBound
    (H : CutPartitionCrossPairSideNeighborCardBound) :
    CutPartitionCrossPairSideNeighborhoodCoverBound := by
  intro n C hmin P
  rcases H C hmin P with ⟨l, r, hl, hr, hside⟩
  exact
    ⟨l, r, hl, hr,
      crossPairSideNeighborhoodCover_card_lt_six_of_sideNeighborCards_le_four
        P hside⟩

theorem cutPartitionDeficientNeighborhoodDeletionData_of_sideNeighborCardBound
    (H : CutPartitionCrossPairSideNeighborCardBound) :
    CutPartitionDeficientNeighborhoodDeletionData :=
  cutPartitionDeficientNeighborhoodDeletionData_of_crossPairSideNeighborhoodCoverBound
    (cutPartitionCrossPairSideNeighborhoodCoverBound_of_sideNeighborCardBound H)

theorem liveCutPartitionDeletionPayloadSource_of_sideNeighborCardBound
    (H : CutPartitionCrossPairSideNeighborCardBound) :
    LiveCutPartitionDeletionPayloadSource :=
  liveCutPartitionDeletionPayloadSource_of_crossPairSideNeighborhoodCoverBound
    (cutPartitionCrossPairSideNeighborhoodCoverBound_of_sideNeighborCardBound H)

/-- Closed-neighborhood tupled data builds the W26 structure-valued
partition-local deletion eliminator. -/
theorem cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_tupled
    (hdel : CutPartitionTupledClosedNeighborhoodDeletionData) :
    CutPartitionLocalClosedNeighborhoodDeletionEliminator := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          cases hdata with
          | intro hclosed hrest =>
              cases hrest with
              | intro hsubset hrest =>
                  cases hrest with
                  | intro hlower hrest =>
                      cases hrest with
                      | intro hupper hindep =>
                          exact
                            Nonempty.intro
                              { deleted := deleted
                                reinsertion := reinsertion
                                closedNeighborhood := hclosed
                                deletedSubsetClosedUnitNeighborhood := hsubset
                                reinsertionCardLower := hlower
                                reinsertionCardUpper := hupper
                                reinsertionIndep := hindep }

/-- A structure-valued local closed-neighborhood deletion carries exactly the
tupled data requested by the W27 no-cut source.  This is a pure field
extraction from local deletion data; it does not use blocker elimination or a
final minimal-failure contradiction. -/
theorem tupledClosedNeighborhoodDeletionData_of_localClosedNeighborhoodDeletion
    {n : Nat} {C : _root_.UDConfig n}
    (L : LocalClosedNeighborhoodDeletion C) :
    Exists fun deleted : Finset (Fin n) =>
    Exists fun reinsertion : Finset (Fin n) =>
      IsClosedNeighborhood C reinsertion deleted /\
      (Exists fun center : Fin n =>
        deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
      2 <= reinsertion.card /\
      reinsertion.card <= 8 /\
      C.IsIndep reinsertion :=
  Exists.intro L.deleted
    (Exists.intro L.reinsertion
      (And.intro L.closedNeighborhood
        (And.intro L.deletedSubsetClosedUnitNeighborhood
          (And.intro L.reinsertionCardLower
            (And.intro L.reinsertionCardUpper L.reinsertionIndep)))))

/-- Partition-scoped structure-valued local deletion data inhabits the actual
tupled closed-neighborhood deletion source. -/
theorem cutPartitionTupledClosedNeighborhoodDeletionData_of_localClosedNeighborhood
    (hdel : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    CutPartitionTupledClosedNeighborhoodDeletionData := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro L =>
      exact tupledClosedNeighborhoodDeletionData_of_localClosedNeighborhoodDeletion L

/-- Tupled closed-neighborhood data for one configuration is the same local
structure data used by the W26 eliminator. -/
theorem nonempty_localClosedNeighborhoodDeletion_of_tupledClosedNeighborhood
    {n : Nat} {C : _root_.UDConfig n}
    (hdel :
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (Exists fun center : Fin n =>
          deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
        2 <= reinsertion.card /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion) :
    Nonempty (LocalClosedNeighborhoodDeletion C) := by
  cases hdel with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          exact
            Nonempty.intro
              { deleted := deleted
                reinsertion := reinsertion
                closedNeighborhood := hdata.1
                deletedSubsetClosedUnitNeighborhood := hdata.2.1
                reinsertionCardLower := hdata.2.2.1
                reinsertionCardUpper := hdata.2.2.2.1
                reinsertionIndep := hdata.2.2.2.2 }

/-- Pointwise obstruction: in a genuine minimal cleared failure, tupled
closed-neighborhood deletion data is impossible.  The tuple already supplies
exactly the concrete induced degree-deletion premises: the closed-neighborhood
identity, a single closed-unit-neighborhood cardinal control center, the lower
and upper reinsertion-card bounds, and reinsertion independence. -/
theorem false_of_minimalFailure_tupledClosedNeighborhood
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hdel :
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (Exists fun center : Fin n =>
          deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
        2 <= reinsertion.card /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion) :
    False := by
  rcases hdel with
    ⟨deleted, reinsertion, hclosed, hsubset, hlower, hupper, hindep⟩
  exact
    false_of_minimalFailure_induced_degree_deletion
      (deleted := deleted) (reinsertion := reinsertion)
      hmin hclosed hsubset hlower hupper hindep

/-- Pointwise obstruction for direct-card-bound tupled deletion data. -/
theorem false_of_minimalFailure_tupledDirectCardBound
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hdel :
      Exists fun deleted : Finset (Fin n) =>
      Exists fun reinsertion : Finset (Fin n) =>
        IsClosedNeighborhood C reinsertion deleted /\
        (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
        reinsertion.Nonempty /\
        reinsertion.card <= 8 /\
        C.IsIndep reinsertion) :
    False := by
  rcases hdel with
    ⟨deleted, reinsertion, hclosed, hcard, hnonempty, hupper, hindep⟩
  exact
    false_of_minimalFailure_induced_deletion
      (deleted := deleted) (reinsertion := reinsertion)
      hmin
      (deleted_nonempty_of_center_nonempty hclosed hnonempty)
      hclosed hcard hupper hindep

/-- Pointwise obstruction for deficient-neighborhood deletion data. -/
theorem false_of_minimalFailure_deficientNeighborhood
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hdel :
      Exists fun S : Finset (Fin n) =>
        S.Nonempty /\
        C.IsIndep S /\
        S.card <= 8 /\
        (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card <
          3 * S.card) :
    False :=
  DeficientNeighborhood.false_of_minimalFailure_deficientIndependentSet
    hmin hdel

/-- A bounded cross-side same-side-neighbor pair is already impossible in a
minimal cleared failure, because it gives a deficient independent two-point
neighborhood. -/
theorem false_of_minimalFailure_sideNeighborCardBound
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)
    {l r : Fin n} (hl : l ∈ P.left) (hr : r ∈ P.right)
    (hside :
      (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
        (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card <= 4) :
    False :=
  false_of_minimalFailure_deficientNeighborhood hmin
    (cutPartitionDeficientNeighborhood_of_sideNeighborCardBound
      P hl hr hside)

/-- Minimality forces every cross-side pair's explicit cut-side cover to have
at least six vertices.  Otherwise the pair is a deficient independent set and
the canonical deletion contradicts minimality. -/
theorem crossPairSideNeighborhoodCover_card_ge_six_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)
    {l r : Fin n} (hl : l ∈ P.left) (hr : r ∈ P.right) :
    6 <= (P.crossPairSideNeighborhoodCover l r).card := by
  have hne : l ≠ r := by
    intro h
    subst r
    exact (Finset.disjoint_left.mp P.disjoint) hl hr
  let S : Finset (Fin n) := {l, r}
  have hS : S.Nonempty := ⟨l, by simp [S]⟩
  have hcard : S.card = 2 := by
    simp [S, hne]
  have hindep : C.IsIndep S := by
    simpa [S] using P.independent_pair_left_right hl hr
  have hupper : S.card <= 8 := by
    omega
  have houtside_ge :
      3 * S.card <=
        (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card :=
    DeficientNeighborhood.outsideNeighborhood_card_ge_three_mul_of_minimalFailure
      hmin hS hindep hupper
  have hcover_ge :
      (SmallIndependentNeighborhood.outsideNeighborhoodOf C S).card <=
        (P.crossPairSideNeighborhoodCover l r).card := by
    simpa [S] using
      P.outsideNeighborhoodOf_pair_card_le_crossPairSideNeighborhoodCover_card
        hl hr
  omega

/-- Therefore every cross-side pair has same-side unit-neighbor counts summing
to at least five.  This is the proved minimality-side field complementary to
the paper-geometry upper bound sought by the no-cut route. -/
theorem sideNeighborCards_ge_five_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)
    {l r : Fin n} (hl : l ∈ P.left) (hr : r ∈ P.right) :
    5 <=
      (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
        (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card := by
  have hcover :=
    crossPairSideNeighborhoodCover_card_ge_six_of_minimalFailure
      hmin P hl hr
  rw [P.crossPairSideNeighborhoodCover_card_eq l r] at hcover
  omega

/-- Family form of the proved lower bound: every minimal-failure cut partition
has cross-side side-neighbor sums at least five for all cross pairs. -/
abbrev CutPartitionCrossPairSideNeighborCardLowerBound : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)
    {l r : Fin n}, l ∈ P.left -> r ∈ P.right ->
      5 <=
        (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
          (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card

theorem cutPartitionCrossPairSideNeighborCardLowerBound_of_minimalFailure :
    CutPartitionCrossPairSideNeighborCardLowerBound := by
  intro n C hmin P l r hl hr
  exact sideNeighborCards_ge_five_of_minimalFailure hmin P hl hr

/-- Pointwise exactness of the side-neighbor source: at a supplied minimal
failure cut partition, producing the bounded pair is equivalent to already
contradicting minimality. -/
theorem exists_sideNeighborCardBound_iff_false
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C) :
    (Exists fun l : Fin n =>
      Exists fun r : Fin n =>
        l ∈ P.left /\
        r ∈ P.right /\
        (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
          (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card <= 4) <->
      False := by
  constructor
  · rintro ⟨l, r, hl, hr, hside⟩
    exact false_of_minimalFailure_sideNeighborCardBound hmin P hl hr hside
  · intro hfalse
    exact False.elim hfalse

/-- Direct no-cut source from the existing live partition-payload source.  The
remaining route-independent no-cut obligation is exactly to inhabit
`LiveCutPartitionDeletionPayloadSource`; once it is supplied, every assumed
cut partition contradicts minimality by one of the three concrete deletion
branches. -/
theorem noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    MinimalFailureNoCutVertexFamily := by
  intro n C hmin hcut
  rcases hcut with ⟨P⟩
  rcases H C hmin P with hclosed | hrest
  · exact false_of_minimalFailure_tupledClosedNeighborhood hmin hclosed
  · rcases hrest with hdirect | hdeficient
    · exact false_of_minimalFailure_tupledDirectCardBound hmin hdirect
    · exact false_of_minimalFailure_deficientNeighborhood hmin hdeficient

/-- Once the minimal-failure no-cut family is known, the cross-pair cover
target is vacuous at every supplied cut partition. -/
theorem cutPartitionCrossPairSideNeighborhoodCoverBound_of_noCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    CutPartitionCrossPairSideNeighborhoodCoverBound := by
  intro n C hmin P
  exact False.elim (H C hmin (Nonempty.intro P))

/-- The cross-pair cover target is exactly the no-cut family: a cover bound
produces deficient-neighborhood deletion data, while no-cut makes the
partition-indexed target vacuous. -/
theorem cutPartitionCrossPairSideNeighborhoodCoverBound_iff_noCutVertexFamily :
    CutPartitionCrossPairSideNeighborhoodCoverBound <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro H
    exact
      noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
        (liveCutPartitionDeletionPayloadSource_of_crossPairSideNeighborhoodCoverBound
          H)
  case mpr =>
    exact cutPartitionCrossPairSideNeighborhoodCoverBound_of_noCutVertexFamily

/-- Once the minimal-failure no-cut family is known, the stronger side-neighbor
target is also vacuous at every supplied cut partition. -/
theorem cutPartitionCrossPairSideNeighborCardBound_of_noCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    CutPartitionCrossPairSideNeighborCardBound := by
  intro n C hmin P
  exact False.elim (H C hmin (Nonempty.intro P))

/-- The side-neighbor-card target is also exactly the no-cut family.  Its
forward direction first converts the side-neighbor bound to the cross-pair
cover bound and then uses the deficient-neighborhood deletion branch. -/
theorem cutPartitionCrossPairSideNeighborCardBound_iff_noCutVertexFamily :
    CutPartitionCrossPairSideNeighborCardBound <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro H
    exact
      noCutVertexFamily_of_liveCutPartitionDeletionPayloadSource
        (liveCutPartitionDeletionPayloadSource_of_sideNeighborCardBound H)
  case mpr =>
    exact cutPartitionCrossPairSideNeighborCardBound_of_noCutVertexFamily

/-- Exact no-cut boundary for the tupled source: because tupled local deletion
data contradicts minimality at any supplied partition, the only way to provide
it for every minimal-failure cut partition is to prove that such partitions do
not exist. -/
theorem cutPartitionTupledClosedNeighborhoodDeletionData_iff_noCutVertexFamily :
    CutPartitionTupledClosedNeighborhoodDeletionData <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro hdel n C hmin hcut
    cases hcut with
    | intro P =>
        exact
          false_of_minimalFailure_tupledClosedNeighborhood hmin
            (hdel C hmin P)
  case mpr =>
    intro hno n C hmin P
    exact False.elim (hno C hmin (Nonempty.intro P))

/-- Closed-neighborhood tupled data feeds W26's degree-certificate
eliminator. -/
theorem cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood
    (hdel : CutPartitionTupledClosedNeighborhoodDeletionData) :
    CutPartitionDegreeDeletionEliminator :=
  cutPartitionDegreeDeletionEliminator_of_localClosedNeighborhood
    (cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_tupled hdel)

/-- A degree-local deletion certificate also carries the same tupled local
facts, before any minimal-failure contradiction is applied. -/
theorem tupledClosedNeighborhoodDeletionData_of_degreeLocalDeletionCertificate
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (K : DegreeLocalDeletionCertificate C Csmall) :
    Exists fun deleted : Finset (Fin n) =>
    Exists fun reinsertion : Finset (Fin n) =>
      IsClosedNeighborhood C reinsertion deleted /\
      (Exists fun center : Fin n =>
        deleted <= DegreePipeline.closedUnitNeighborhood C center) /\
      2 <= reinsertion.card /\
      reinsertion.card <= 8 /\
      C.IsIndep reinsertion :=
  Exists.intro K.deleted
    (Exists.intro K.reinsertion
      (And.intro K.closedNeighborhood
        (And.intro K.deletedSubsetClosedUnitNeighborhood
          (And.intro K.reinsertionCardLower
            (And.intro K.reinsertionCardUpper K.reinsertionIndep)))))

/-- A global minimal-failure local closed-neighborhood eliminator supplies the
partition-scoped tupled deletion source by direct field extraction. -/
theorem cutPartitionTupledClosedNeighborhoodDeletionData_of_globalLocalClosedNeighborhood
    (hdel :
      LocalDeletionConstructors.MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    CutPartitionTupledClosedNeighborhoodDeletionData :=
  cutPartitionTupledClosedNeighborhoodDeletionData_of_localClosedNeighborhood
    (cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_global hdel)

/-- A global degree-local deletion eliminator supplies the partition-scoped
tupled deletion source by unpacking the degree certificate fields. -/
theorem cutPartitionTupledClosedNeighborhoodDeletionData_of_globalDegreeDeletionEliminator
    (hdel : LocalDeletionConstructors.MinimalFailureDegreeDeletionEliminator) :
    CutPartitionTupledClosedNeighborhoodDeletionData := by
  intro n C hmin _P
  cases hdel C hmin with
  | intro _nSmall hrest =>
      cases hrest with
      | intro _Csmall hcert =>
          cases hcert with
          | intro K =>
              exact
                tupledClosedNeighborhoodDeletionData_of_degreeLocalDeletionCertificate K

/-- Direct-card-bound tupled data builds W26's direct local-deletion
certificate eliminator. -/
theorem cutPartitionDirectCardBoundCertificateEliminator_of_tupled
    (hdel : CutPartitionTupledDirectCardBoundDeletionData) :
    CutPartitionDirectCardBoundCertificateEliminator := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro deleted hrest =>
      cases hrest with
      | intro reinsertion hdata =>
          cases hdata with
          | intro hclosed hrest =>
              cases hrest with
              | intro hcard hrest =>
                  cases hrest with
                  | intro hnonempty hrest =>
                      cases hrest with
                      | intro hupper hindep =>
                          exact
                            LocalDeletionWithCardBound.exists_localDeletionCertificate_of_data
                              C deleted reinsertion hclosed hcard hnonempty hupper hindep

/-- Deficient-neighborhood data is a concrete direct-card-bound local deletion
source, using the existing canonical deletion machinery. -/
theorem cutPartitionDirectCardBoundCertificateEliminator_of_deficientNeighborhood
    (hdel : CutPartitionDeficientNeighborhoodDeletionData) :
    CutPartitionDirectCardBoundCertificateEliminator := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro S hdata =>
      cases hdata with
      | intro hS hrest =>
          cases hrest with
          | intro hindep hrest =>
              cases hrest with
              | intro hupper houtside =>
                  exact
                    DeficientNeighborhood.exists_localDeletionCertificate_of_deficientNeighborhood
                      C hS hindep hupper houtside

/-- A tupled closed-neighborhood payload is already a direct-card-bound
payload: the deleted set lies in one closed unit-neighborhood, hence has at
most seven vertices, and the reinsertion set has size at least two. -/
theorem tupledDirectCardBound_of_tupledClosedNeighborhood
    {n : Nat} {C : _root_.UDConfig n}
    (hdel : CutPartitionTupledClosedNeighborhood C) :
    CutPartitionTupledDirectCardBound C := by
  rcases hdel with
    ⟨deleted, reinsertion, hclosed, hsubset, hlower, hupper, hindep⟩
  refine
    ⟨deleted, reinsertion, hclosed, ?_, ?_, hupper, hindep⟩
  · rcases hsubset with ⟨center, hsubsetCenter⟩
    exact
      DegreePipeline.deletedCard_bound_of_subset_closedUnitNeighborhood_and_two_le
        C hsubsetCenter hlower
  · have hpos : 0 < reinsertion.card := by omega
    exact Finset.card_pos.mp hpos

/-- Any tupled direct-card-bound payload can be represented by the canonical
closed neighborhood of its reinsertion set, so it yields the deficient
outside-neighborhood branch. -/
theorem deficientNeighborhood_of_tupledDirectCardBound
    {n : Nat} {C : _root_.UDConfig n}
    (hdel : CutPartitionTupledDirectCardBound C) :
    CutPartitionDeficientNeighborhood C := by
  rcases hdel with
    ⟨deleted, reinsertion, hclosed, hcard, hnonempty, hupper, hindep⟩
  refine ⟨reinsertion, hnonempty, hindep, hupper, ?_⟩
  have hdeleted :
      deleted = SmallIndependentNeighborhood.closedNeighborhoodOf C reinsertion := by
    ext v
    exact
      (hclosed v).trans
        (SmallIndependentNeighborhood.mem_closedNeighborhoodOf C reinsertion v).symm
  have hsplit :
      deleted.card =
        reinsertion.card +
          (SmallIndependentNeighborhood.outsideNeighborhoodOf C reinsertion).card := by
    rw [hdeleted]
    exact
      SmallIndependentNeighborhood.closedNeighborhoodOf_card_eq_add_outsideNeighborhoodOf_card
        C reinsertion
  have hltInt :
      ((SmallIndependentNeighborhood.outsideNeighborhoodOf C reinsertion).card : Int) <
        3 * (reinsertion.card : Int) := by
    omega
  exact_mod_cast hltInt

/-- Closed-neighborhood payloads also normalize to the deficient-neighborhood
branch. -/
theorem deficientNeighborhood_of_tupledClosedNeighborhood
    {n : Nat} {C : _root_.UDConfig n}
    (hdel : CutPartitionTupledClosedNeighborhood C) :
    CutPartitionDeficientNeighborhood C :=
  deficientNeighborhood_of_tupledDirectCardBound
    (tupledDirectCardBound_of_tupledClosedNeighborhood hdel)

/-- The mixed live payload alternative has a single essential branch: every
closed or direct-card-bound payload canonically gives deficient-neighborhood
data. -/
theorem deficientNeighborhood_of_livePayloadAlternative
    {n : Nat} {C : _root_.UDConfig n}
    (hdel :
      CutPartitionTupledClosedNeighborhood C \/
        CutPartitionTupledDirectCardBound C \/
          CutPartitionDeficientNeighborhood C) :
    CutPartitionDeficientNeighborhood C := by
  cases hdel with
  | inl hclosed =>
      exact deficientNeighborhood_of_tupledClosedNeighborhood hclosed
  | inr hrest =>
      cases hrest with
      | inl hdirect =>
          exact deficientNeighborhood_of_tupledDirectCardBound hdirect
      | inr hdeficient =>
          exact hdeficient

/-- The W27 live deletion-payload source is equivalent to the single concrete
deficient-neighborhood source.  This is the sharp remaining cut-partition
fact after normalizing the closed and direct-card-bound branches. -/
theorem liveCutPartitionDeletionPayloadSource_iff_deficientNeighborhoodDeletionData :
    LiveCutPartitionDeletionPayloadSource <->
      CutPartitionDeficientNeighborhoodDeletionData := by
  constructor
  case mp =>
    intro H n C hmin P
    exact deficientNeighborhood_of_livePayloadAlternative (H C hmin P)
  case mpr =>
    intro H n C hmin P
    exact Or.inr (Or.inr (H C hmin P))

theorem liveCutPartitionDeletionPayloadSource_of_deficientNeighborhoodDeletionData
    (H : CutPartitionDeficientNeighborhoodDeletionData) :
    LiveCutPartitionDeletionPayloadSource :=
  liveCutPartitionDeletionPayloadSource_iff_deficientNeighborhoodDeletionData.2 H

theorem deficientNeighborhoodDeletionData_of_liveCutPartitionDeletionPayloadSource
    (H : LiveCutPartitionDeletionPayloadSource) :
    CutPartitionDeficientNeighborhoodDeletionData :=
  liveCutPartitionDeletionPayloadSource_iff_deficientNeighborhoodDeletionData.1 H

theorem not_nonempty_minimalCutVertexBlocker_of_tupledClosedNeighborhood
    (hdel : CutPartitionTupledClosedNeighborhoodDeletionData) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_tupledDirectCardBound
    (hdel : CutPartitionTupledDirectCardBoundDeletionData) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (cutPartitionDirectCardBoundCertificateEliminator_of_tupled hdel)

theorem not_nonempty_minimalCutVertexBlocker_of_deficientNeighborhood
    (hdel : CutPartitionDeficientNeighborhoodDeletionData) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (cutPartitionDirectCardBoundCertificateEliminator_of_deficientNeighborhood hdel)

/-- The smallest exact certificate-level local-deletion dependency consumed
by W26. -/
abbrev SmallestExactLocalDeletionDependency : Prop :=
  CutPartitionDegreeDeletionEliminator

/-- The exact dependency already contains tupled closed-neighborhood deletion
data.  This is the non-circular extraction direction: a degree-local deletion
certificate supplies the concrete deleted/reinsertion sets and all local facts
directly, without using a final minimal-failure eliminator. -/
theorem cutPartitionTupledClosedNeighborhoodDeletionData_of_smallestExactLocalDeletionDependency
    (hdel : SmallestExactLocalDeletionDependency) :
    CutPartitionTupledClosedNeighborhoodDeletionData := by
  intro n C hmin P
  cases hdel C hmin P with
  | intro nSmall hrest =>
      cases hrest with
      | intro Csmall hcert =>
          cases hcert with
          | intro K =>
              exact
                Exists.intro K.deleted
                  (Exists.intro K.reinsertion
                    (And.intro K.closedNeighborhood
                      (And.intro K.deletedSubsetClosedUnitNeighborhood
                        (And.intro K.reinsertionCardLower
                          (And.intro K.reinsertionCardUpper
                            K.reinsertionIndep)))))

/-- Concrete tupled closed-neighborhood deletion data is exactly the smallest
partition-scoped local-deletion dependency. -/
theorem smallestExactLocalDeletionDependency_iff_tupledClosedNeighborhoodDeletionData :
    SmallestExactLocalDeletionDependency <->
      CutPartitionTupledClosedNeighborhoodDeletionData := by
  constructor
  case mp =>
    exact
      cutPartitionTupledClosedNeighborhoodDeletionData_of_smallestExactLocalDeletionDependency
  case mpr =>
    exact cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood

theorem smallestExactLocalDeletionDependency_of_not_minimalCutVertexBlocker
    (hblocker : Not (Nonempty MinimalCutVertexBlocker)) :
    SmallestExactLocalDeletionDependency := by
  intro n C hmin P
  exact
    False.elim
      (hblocker
        (Nonempty.intro
          (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
            (C := C) hmin P)))

/-- A current minimal-failure eliminator supplies the exact W27
partition-scoped local-deletion dependency. -/
theorem smallestExactLocalDeletionDependency_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    SmallestExactLocalDeletionDependency := by
  intro n C hmin _P
  exact False.elim (hElim C hmin)

/-- Exact W27 boundary: W26's smallest partition-scoped local-deletion
dependency is equivalent to eliminating the concrete cut-vertex blocker. -/
theorem smallestExactLocalDeletionDependency_iff_not_minimalCutVertexBlocker :
    SmallestExactLocalDeletionDependency <->
      Not (Nonempty MinimalCutVertexBlocker) := by
  constructor
  case mp =>
    exact
      not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
  case mpr =>
    exact smallestExactLocalDeletionDependency_of_not_minimalCutVertexBlocker

/-- Equivalent non-circular source spelling for blocker elimination: the
missing no-cut input is precisely tupled closed-neighborhood deletion data for
each minimal-failure cut partition. -/
theorem cutPartitionTupledClosedNeighborhoodDeletionData_iff_not_minimalCutVertexBlocker :
    CutPartitionTupledClosedNeighborhoodDeletionData <->
      Not (Nonempty MinimalCutVertexBlocker) :=
  smallestExactLocalDeletionDependency_iff_tupledClosedNeighborhoodDeletionData.symm.trans
    smallestExactLocalDeletionDependency_iff_not_minimalCutVertexBlocker

/-- Structure-valued closed-neighborhood data has the same exact boundary. -/
theorem cutPartitionLocalClosedNeighborhoodDeletionEliminator_iff_not_minimalCutVertexBlocker :
    CutPartitionLocalClosedNeighborhoodDeletionEliminator <->
      Not (Nonempty MinimalCutVertexBlocker) := by
  constructor
  case mp =>
    exact not_nonempty_minimalCutVertexBlocker_of_cutPartitionLocalClosedNeighborhood
  case mpr =>
    intro hblocker n C hmin P
    exact
      False.elim
        (hblocker
          (Nonempty.intro
            (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
              (C := C) hmin P)))

/-- Direct-card-bound certificates also have the same exact partition-scoped
boundary. -/
theorem cutPartitionDirectCardBoundCertificateEliminator_iff_not_minimalCutVertexBlocker :
    CutPartitionDirectCardBoundCertificateEliminator <->
      Not (Nonempty MinimalCutVertexBlocker) := by
  constructor
  case mp =>
    exact not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
  case mpr =>
    intro hblocker n C hmin P
    exact
      False.elim
        (hblocker
          (Nonempty.intro
            (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
              (C := C) hmin P)))

end

end NoCutLocalDeletionConcreteW27
end Swanepoel
end ErdosProblems1066
