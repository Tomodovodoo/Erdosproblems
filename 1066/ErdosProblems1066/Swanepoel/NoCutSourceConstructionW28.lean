import ErdosProblems1066.Swanepoel.NoCutLocalDeletionConcreteW27
import ErdosProblems1066.Swanepoel.PointwiseSourceFieldsConcreteW27
import ErdosProblems1066.Swanepoel.CutSideCardPayForCutConcreteW27
import ErdosProblems1066.Swanepoel.SwanepoelW27FinalAssembly

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 no-cut source construction

This file makes the no-cut/local-deletion source boundary live on actual
minimal cut-vertex blockers.  A worker that supplies deletion data for each
`MinimalCutVertexBlocker` now feeds the W26 partition eliminators, the W27
local-deletion gates, and the W27 final source packages without replacing the
missing construction by a target-level shortcut.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutSourceConstructionW28

open CutVertexInterface
open MinimalCounterexample
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoCutConcreteEliminationW26
open NoCutLocalDeletionConcreteW27

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutLocalDeletionConcreteW27.MinimalCutVertexBlocker

abbrev MinimalCutVertexBlockerExists : Prop :=
  Nonempty MinimalCutVertexBlocker

/-- The blocker-level degree-deletion source.  This is the smallest source
shape that still talks about the concrete counterexample data instead of only
about a final no-blocker statement. -/
abbrev BlockerDegreeDeletionSource : Prop :=
  forall B : MinimalCutVertexBlocker,
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (DegreeLocalDeletionCertificate B.C Csmall)

/-- The blocker-level structure-valued closed-neighborhood deletion source. -/
abbrev BlockerLocalClosedNeighborhoodDeletionSource : Prop :=
  forall B : MinimalCutVertexBlocker,
    Nonempty (LocalClosedNeighborhoodDeletion B.C)

/-- The blocker-level direct-card-bound certificate source. -/
abbrev BlockerDirectCardBoundCertificateSource : Prop :=
  forall B : MinimalCutVertexBlocker,
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (LocalDeletionCertificate B.C Csmall)

/-- Tupled blocker-local closed-neighborhood deletion data. -/
abbrev BlockerTupledClosedNeighborhoodDeletionSource : Prop :=
  forall B : MinimalCutVertexBlocker,
    Exists fun deleted : Finset (Fin B.n) =>
      Exists fun reinsertion : Finset (Fin B.n) =>
        IsClosedNeighborhood B.C reinsertion deleted /\
        (Exists fun center : Fin B.n =>
          deleted <= DegreePipeline.closedUnitNeighborhood B.C center) /\
        2 <= reinsertion.card /\
        reinsertion.card <= 8 /\
        B.C.IsIndep reinsertion

/-- Tupled blocker-local direct-card-bound deletion data. -/
abbrev BlockerTupledDirectCardBoundDeletionSource : Prop :=
  forall B : MinimalCutVertexBlocker,
    Exists fun deleted : Finset (Fin B.n) =>
      Exists fun reinsertion : Finset (Fin B.n) =>
        IsClosedNeighborhood B.C reinsertion deleted /\
        (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1 /\
        reinsertion.Nonempty /\
        reinsertion.card <= 8 /\
        B.C.IsIndep reinsertion

/-- Blocker-local deficient-neighborhood data, in the form consumed by W27. -/
abbrev BlockerDeficientNeighborhoodDeletionSource : Prop :=
  forall B : MinimalCutVertexBlocker,
    Exists fun S : Finset (Fin B.n) =>
      S.Nonempty /\
      B.C.IsIndep S /\
      S.card <= 8 /\
      (SmallIndependentNeighborhood.outsideNeighborhoodOf B.C S).card <
        3 * S.card

def blockerOfCutPartition
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalCutVertexBlocker :=
  NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
    (C := C) hmin P

/-! ## Exact bridges between blocker-level and partition-level sources -/

theorem cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    CutPartitionDegreeDeletionEliminator := by
  intro n C hmin P
  exact H (blockerOfCutPartition (C := C) hmin P)

theorem blockerDegreeDeletionSource_of_cutPartitionDegreeDeletionEliminator
    (H : CutPartitionDegreeDeletionEliminator) :
    BlockerDegreeDeletionSource := by
  intro B
  exact H B.C B.minimal B.cut

theorem blockerDegreeDeletionSource_iff_cutPartitionDegreeDeletionEliminator :
    BlockerDegreeDeletionSource <-> CutPartitionDegreeDeletionEliminator := by
  constructor
  case mp =>
    exact cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource
  case mpr =>
    exact blockerDegreeDeletionSource_of_cutPartitionDegreeDeletionEliminator

theorem cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_blockerLocalClosed
    (H : BlockerLocalClosedNeighborhoodDeletionSource) :
    CutPartitionLocalClosedNeighborhoodDeletionEliminator := by
  intro n C hmin P
  exact H (blockerOfCutPartition (C := C) hmin P)

theorem blockerLocalClosed_of_cutPartitionLocalClosedNeighborhoodDeletionEliminator
    (H : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    BlockerLocalClosedNeighborhoodDeletionSource := by
  intro B
  exact H B.C B.minimal B.cut

theorem blockerLocalClosed_iff_cutPartitionLocalClosedNeighborhoodDeletionEliminator :
    BlockerLocalClosedNeighborhoodDeletionSource <->
      CutPartitionLocalClosedNeighborhoodDeletionEliminator := by
  constructor
  case mp =>
    exact cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_blockerLocalClosed
  case mpr =>
    exact blockerLocalClosed_of_cutPartitionLocalClosedNeighborhoodDeletionEliminator

theorem cutPartitionDirectCardBoundCertificateEliminator_of_blockerDirectCard
    (H : BlockerDirectCardBoundCertificateSource) :
    CutPartitionDirectCardBoundCertificateEliminator := by
  intro n C hmin P
  exact H (blockerOfCutPartition (C := C) hmin P)

theorem blockerDirectCard_of_cutPartitionDirectCardBoundCertificateEliminator
    (H : CutPartitionDirectCardBoundCertificateEliminator) :
    BlockerDirectCardBoundCertificateSource := by
  intro B
  exact H B.C B.minimal B.cut

theorem blockerDirectCard_iff_cutPartitionDirectCardBoundCertificateEliminator :
    BlockerDirectCardBoundCertificateSource <->
      CutPartitionDirectCardBoundCertificateEliminator := by
  constructor
  case mp =>
    exact cutPartitionDirectCardBoundCertificateEliminator_of_blockerDirectCard
  case mpr =>
    exact blockerDirectCard_of_cutPartitionDirectCardBoundCertificateEliminator

theorem cutPartitionTupledClosedNeighborhoodDeletionData_of_blockerTupledClosed
    (H : BlockerTupledClosedNeighborhoodDeletionSource) :
    CutPartitionTupledClosedNeighborhoodDeletionData := by
  intro n C hmin P
  exact H (blockerOfCutPartition (C := C) hmin P)

theorem blockerTupledClosed_of_cutPartitionTupledClosedNeighborhoodDeletionData
    (H : CutPartitionTupledClosedNeighborhoodDeletionData) :
    BlockerTupledClosedNeighborhoodDeletionSource := by
  intro B
  exact H B.C B.minimal B.cut

theorem blockerTupledClosed_iff_cutPartitionTupledClosedNeighborhoodDeletionData :
    BlockerTupledClosedNeighborhoodDeletionSource <->
      CutPartitionTupledClosedNeighborhoodDeletionData := by
  constructor
  case mp =>
    exact cutPartitionTupledClosedNeighborhoodDeletionData_of_blockerTupledClosed
  case mpr =>
    exact blockerTupledClosed_of_cutPartitionTupledClosedNeighborhoodDeletionData

theorem blockerLocalClosed_of_blockerTupledClosed
    (H : BlockerTupledClosedNeighborhoodDeletionSource) :
    BlockerLocalClosedNeighborhoodDeletionSource :=
  blockerLocalClosed_of_cutPartitionLocalClosedNeighborhoodDeletionEliminator
    (cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_tupled
      (cutPartitionTupledClosedNeighborhoodDeletionData_of_blockerTupledClosed H))

theorem blockerDegreeDeletionSource_of_blockerTupledClosed
    (H : BlockerTupledClosedNeighborhoodDeletionSource) :
    BlockerDegreeDeletionSource :=
  blockerDegreeDeletionSource_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood
      (cutPartitionTupledClosedNeighborhoodDeletionData_of_blockerTupledClosed H))

theorem cutPartitionTupledDirectCardBoundDeletionData_of_blockerTupledDirect
    (H : BlockerTupledDirectCardBoundDeletionSource) :
    CutPartitionTupledDirectCardBoundDeletionData := by
  intro n C hmin P
  exact H (blockerOfCutPartition (C := C) hmin P)

theorem blockerTupledDirect_of_cutPartitionTupledDirectCardBoundDeletionData
    (H : CutPartitionTupledDirectCardBoundDeletionData) :
    BlockerTupledDirectCardBoundDeletionSource := by
  intro B
  exact H B.C B.minimal B.cut

theorem blockerTupledDirect_iff_cutPartitionTupledDirectCardBoundDeletionData :
    BlockerTupledDirectCardBoundDeletionSource <->
      CutPartitionTupledDirectCardBoundDeletionData := by
  constructor
  case mp =>
    exact cutPartitionTupledDirectCardBoundDeletionData_of_blockerTupledDirect
  case mpr =>
    exact blockerTupledDirect_of_cutPartitionTupledDirectCardBoundDeletionData

theorem blockerDirectCard_of_blockerTupledDirect
    (H : BlockerTupledDirectCardBoundDeletionSource) :
    BlockerDirectCardBoundCertificateSource :=
  blockerDirectCard_of_cutPartitionDirectCardBoundCertificateEliminator
    (cutPartitionDirectCardBoundCertificateEliminator_of_tupled
      (cutPartitionTupledDirectCardBoundDeletionData_of_blockerTupledDirect H))

theorem cutPartitionDeficientNeighborhoodDeletionData_of_blockerDeficient
    (H : BlockerDeficientNeighborhoodDeletionSource) :
    CutPartitionDeficientNeighborhoodDeletionData := by
  intro n C hmin P
  exact H (blockerOfCutPartition (C := C) hmin P)

theorem blockerDeficient_of_cutPartitionDeficientNeighborhoodDeletionData
    (H : CutPartitionDeficientNeighborhoodDeletionData) :
    BlockerDeficientNeighborhoodDeletionSource := by
  intro B
  exact H B.C B.minimal B.cut

theorem blockerDeficient_iff_cutPartitionDeficientNeighborhoodDeletionData :
    BlockerDeficientNeighborhoodDeletionSource <->
      CutPartitionDeficientNeighborhoodDeletionData := by
  constructor
  case mp =>
    exact cutPartitionDeficientNeighborhoodDeletionData_of_blockerDeficient
  case mpr =>
    exact blockerDeficient_of_cutPartitionDeficientNeighborhoodDeletionData

theorem blockerDirectCard_of_blockerDeficient
    (H : BlockerDeficientNeighborhoodDeletionSource) :
    BlockerDirectCardBoundCertificateSource :=
  blockerDirectCard_of_cutPartitionDirectCardBoundCertificateEliminator
    (cutPartitionDirectCardBoundCertificateEliminator_of_deficientNeighborhood
      (cutPartitionDeficientNeighborhoodDeletionData_of_blockerDeficient H))

/-! ## No-cut and W27 source packages from blocker-local deletion -/

theorem not_nonempty_minimalCutVertexBlocker_of_blockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    Not MinimalCutVertexBlockerExists :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource H)

theorem not_nonempty_minimalCutVertexBlocker_of_blockerLocalClosed
    (H : BlockerLocalClosedNeighborhoodDeletionSource) :
    Not MinimalCutVertexBlockerExists :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionLocalClosedNeighborhood
    (cutPartitionLocalClosedNeighborhoodDeletionEliminator_of_blockerLocalClosed H)

theorem not_nonempty_minimalCutVertexBlocker_of_blockerDirectCard
    (H : BlockerDirectCardBoundCertificateSource) :
    Not MinimalCutVertexBlockerExists :=
  not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
    (cutPartitionDirectCardBoundCertificateEliminator_of_blockerDirectCard H)

theorem smallestExactLocalDeletionDependency_of_blockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    SmallestExactLocalDeletionDependency :=
  cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource H

def pointwisePayForCutFamilyOfBlockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    CutVertexContradictionInhabitationW25.MinimalFailurePointwisePayForCutFamily :=
  pointwisePayForCutFamily_of_cutPartitionDegreeDeletionEliminator
    (cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource H)

def pointwiseSideCardPayForCutFieldsOfBlockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields :=
  CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields.ofPayForCut
    (pointwisePayForCutFamilyOfBlockerDegreeDeletionSource H)

def noCutComponentOfBlockerDegreeDeletionSource
    (H : BlockerDegreeDeletionSource) :
    ConcreteW23ComponentsInhabitationW26.ConcreteNoCutTheorem :=
  ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
    (not_nonempty_minimalCutVertexBlocker_of_blockerDegreeDeletionSource H)

def concreteW23ComponentsOfBlockerDegreeDeletionTail
    (H : BlockerDegreeDeletionSource)
    (tail :
      ConcreteW23ComponentsInhabitationW26.ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfBlockerDegreeDeletionSource H)) :
    ConcreteW23ComponentsInhabitationW26.ConcreteW23Components :=
  ConcreteW23ComponentsInhabitationW26.concreteW23ComponentsOfNoCutTail tail

def concreteFinalSourcePackageOfBlockerDegreeDeletionTail
    (H : BlockerDegreeDeletionSource)
    (tail :
      ConcreteW23ComponentsInhabitationW26.ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfBlockerDegreeDeletionSource H)) :
    SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage :=
  SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage.lane
    (concreteW23ComponentsOfBlockerDegreeDeletionTail H tail)

/-- The pointwise W27 source product with the no-cut field supplied by
blocker-level deletion.  The other fields remain the genuine boundary,
Lemma 8, Lemma 9, and figure sources. -/
structure BlockerDegreeDeletionPointwiseW27Product : Type 1 where
  deletion : BlockerDegreeDeletionSource
  boundary :
    BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{0}
  lemma8 :
    Lemma8FrameRowsConstructionW26.FramePositiveOrderRows.{0}
      (PointwiseSourceFieldsConcreteW27.payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
        (cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource
          deletion))
      (PointwiseSourceFieldsConcreteW27.topologyArcConcreteProducerFamilyOfBoundaryComponentFamily
        boundary)
  lemma9 :
    Lemma9NoEarlyObstructionInhabitationW25.M8ConcreteNoEarlySourceFamily.{0}
      (PointwiseSourceFieldsConcreteW27.payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
        (cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource
          deletion))
      (PointwiseSourceFieldsConcreteW27.topologyArcConcreteProducerFamilyOfBoundaryComponentFamily
        boundary)
      (PointwiseSourceFieldsConcreteW27.lemma8ConcreteProducerFamilyOfFramePositiveOrderRows
        lemma8)
  figures :
    FigureExactAngleCertificateInhabitationW22.LocalExactAngleDataFamily.{0}
      (PointwiseSourceFieldsConcreteW27.payForCutConcreteProducerFamilyOfCutPartitionDegreeDeletionEliminator
        (cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource
          deletion))
      (PointwiseSourceFieldsConcreteW27.topologyArcConcreteProducerFamilyOfBoundaryComponentFamily
        boundary)
      (PointwiseSourceFieldsConcreteW27.lemma8ConcreteProducerFamilyOfFramePositiveOrderRows
        lemma8)

namespace BlockerDegreeDeletionPointwiseW27Product

def cutPartitionDegreeDeletionEliminator
    (P : BlockerDegreeDeletionPointwiseW27Product) :
    CutPartitionDegreeDeletionEliminator :=
  cutPartitionDegreeDeletionEliminator_of_blockerDegreeDeletionSource P.deletion

def toW26Product
    (P : BlockerDegreeDeletionPointwiseW27Product) :
    PointwiseSourceFieldsConcreteW27.PointwiseSourceFieldsW26Product.{0} where
  noCut := P.cutPartitionDegreeDeletionEliminator
  boundary := P.boundary
  lemma8 := P.lemma8
  lemma9 := P.lemma9
  figures := P.figures

def toPointwiseSourcePackage
    (P : BlockerDegreeDeletionPointwiseW27Product) :
    SwanepoelW27FinalAssembly.PointwiseSourcePackage :=
  PointwiseSourceFieldsConcreteW27.pointwiseSourceFamilyFieldsOfW26Product
    P.toW26Product

def toConcreteFinalSourcePackage
    (P : BlockerDegreeDeletionPointwiseW27Product) :
    SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage :=
  SwanepoelW27FinalAssembly.ConcreteFinalSourcePackage.pointwise
    P.toPointwiseSourcePackage

end BlockerDegreeDeletionPointwiseW27Product

end

end NoCutSourceConstructionW28
end Swanepoel

namespace Verified

abbrev SwanepoelW28BlockerDegreeDeletionSource : Prop :=
  Swanepoel.NoCutSourceConstructionW28.BlockerDegreeDeletionSource

abbrev SwanepoelW28BlockerLocalClosedNeighborhoodDeletionSource : Prop :=
  Swanepoel.NoCutSourceConstructionW28.BlockerLocalClosedNeighborhoodDeletionSource

abbrev SwanepoelW28BlockerDeficientNeighborhoodDeletionSource : Prop :=
  Swanepoel.NoCutSourceConstructionW28.BlockerDeficientNeighborhoodDeletionSource

theorem swanepoelW28_blockerDegreeDeletionSource_iff_cutPartitionDegreeDeletionEliminator :
    SwanepoelW28BlockerDegreeDeletionSource <->
      Swanepoel.NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator :=
  Swanepoel.NoCutSourceConstructionW28.blockerDegreeDeletionSource_iff_cutPartitionDegreeDeletionEliminator

theorem swanepoelW28_smallestExactLocalDeletionDependency_of_blockerDegreeDeletionSource
    (H : SwanepoelW28BlockerDegreeDeletionSource) :
    Swanepoel.NoCutLocalDeletionConcreteW27.SmallestExactLocalDeletionDependency :=
  Swanepoel.NoCutSourceConstructionW28.smallestExactLocalDeletionDependency_of_blockerDegreeDeletionSource
    H

theorem swanepoelW28_not_blocker_of_deficientNeighborhoodSource
    (H : SwanepoelW28BlockerDeficientNeighborhoodDeletionSource) :
    Not
      (Nonempty
        Swanepoel.NoCutSourceConstructionW28.MinimalCutVertexBlocker) :=
  Swanepoel.NoCutSourceConstructionW28.not_nonempty_minimalCutVertexBlocker_of_blockerDirectCard
    (Swanepoel.NoCutSourceConstructionW28.blockerDirectCard_of_blockerDeficient H)

end Verified
end ErdosProblems1066
