import ErdosProblems1066.PachToth.ExactBlockCertificateW13
import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13
import ErdosProblems1066.PachToth.LargeClosedPlacementInstantiationW13
import ErdosProblems1066.PachToth.NonConnectorInstantiationW13
import ErdosProblems1066.PachToth.SplitSoundnessInstantiationW13
import ErdosProblems1066.PachToth.TransitionAlternativeW13
import ErdosProblems1066.Swanepoel.BoundaryArcInstantiationW13
import ErdosProblems1066.Swanepoel.BoundaryBudgetRefinedFactsW13
import ErdosProblems1066.Swanepoel.BrokenLatticeEliminatorW13
import ErdosProblems1066.Swanepoel.ExactOuterBoundaryTopologyW13
import ErdosProblems1066.Swanepoel.FiguresToRefinedM8W13
import ErdosProblems1066.Swanepoel.KnownBoundsSpineW13
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma8Lemma9AssemblyW13
import ErdosProblems1066.Swanepoel.LongArcToM8AssemblyW13
import ErdosProblems1066.Swanepoel.MinimalFailureClosureW13
import ErdosProblems1066.Swanepoel.NoCutVertexExtractionW13
import ErdosProblems1066.Swanepoel.OuterBoundaryInstantiationW13
import ErdosProblems1066.Swanepoel.RefinedPaperFactsAssemblyW13
import ErdosProblems1066.Swanepoel.SubpolygonInstantiationW13

set_option autoImplicit false

namespace ErdosProblems1066
namespace VerificationLedgerW14

open ErdosProblems1066.Swanepoel
open ErdosProblems1066.PachToth

universe u

noncomputable section

namespace SwanepoelSmoke

theorem noCut_remainingSlack_iff
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) <->
      CutVertexInterface.NoCutVertex C :=
  NoCutVertexExtractionW13.remainingNoCutSlackFact_iff_noCutVertex_of_minimalFailure
    hmin

theorem exactTopology_completion_of_topologyFacts
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexFinal.RemainingNoCutSlackFact C)
    (T : ExactOuterBoundaryTopologyW13.TopologyFacts C) :
    ExactOuterBoundaryTopologyW13.MinimalCompletion C :=
  ExactOuterBoundaryTopologyW13.completion_of_minimalFailure_topologyFacts
    hmin hslack T

theorem outerBoundary_negativeCount
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : OuterBoundaryInstantiationW13.ActualOuterBoundaryAngleData G) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  D.boundaryNegativeCountInequality

theorem subpolygon_family_lowDegree
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (F : SubpolygonInstantiationW13.ExplicitBoundaryFamilyData.{u} G)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 +
      (F.subpolygonCounts S).D3 :=
  F.subpolygonLowDegree S

theorem lemma67_longArcCoverage
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (Q : Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage D) :
    D.outerBoundaryCounts.d3 <=
      D.outerBoundaryCounts.negativeCount + Q.source.longArcCount :=
  Q.degreeThree_le_negativeCount_add_longArcCount

theorem longArc_m8ConstructionContradiction
    {n : Nat} {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G}
    (P :
      LongArcToM8AssemblyW13.BoundaryBudgetM8ConstructionPreconditions
        C hmin D) :
    False :=
  P.contradiction

theorem boundaryBudget_refinedContradiction
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : BoundaryBudgetRefinedFactsW13.BoundaryBudgetRefinedFactInputs C hmin) :
    False :=
  P.conditionalContradiction

theorem refinedRecords_target
    (H : RefinedPaperFactsAssemblyW13.ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

theorem minimalFailure_remainingFamily_target
    (H : MinimalFailureClosureW13.RemainingInputFamily.{u}) :
    ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosureW13.targetLowerBoundEightThirtyOne_of_remainingInputFamily
    H

theorem brokenLattice_builder_target
    (build :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          BrokenLatticeAssemblyW13.ExplicitBrokenLatticeM8LocalWindowRecords
            C hmin) :
    ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  BrokenLatticeEliminatorW13.targetLowerBoundEightThirtyOne_of_explicitRecordBuilder
    build

theorem knownBounds_exactTargetProjection
    (H : KnownBoundsSpineW13.ExactTargetInputs)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  KnownBoundsSpineW13.lower_bound_eight_thirty_one_of_exactTargetInputs
    H n C

end SwanepoelSmoke

namespace PachTothSmoke

open FiniteCertificateInstantiationW13
open LargeClosedPlacementInstantiationW13
open NonConnectorInstantiationW13
open SplitSoundnessInstantiationW13

theorem transition_restrictedRoute_blocked
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    Not
      (And
        (PeriodInterface.GeneratedClosureEquation
          TransitionAlternativeW13.ConcreteTransitionObligations hk
          BaseTransitionRealization.exactBase orientation)
        (And
          (GeneratedSeparationInterface.GeneratedGlobalSeparation
            TransitionAlternativeW13.ConcreteTransitionObligations hk
            BaseTransitionRealization.exactBase orientation)
          (TransitionAlternativeW13.ConcreteOrbitSqDistances
            hk orientation))) :=
  TransitionAlternativeW13.concreteTransitionObligations_restrictedExactBlockRoute_blocked
    hk orientation

theorem exactBlock_concreteOneBlock
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    PachToth.targetUpperConstructionFiveSixteenAt 16 :=
  ExactBlockCertificateW13.targetUpperConstructionFiveSixteenAt_of_concreteOneBlockCertificate
    C

theorem finiteCertificate_concreteValueMatrixArbitrary
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily C

theorem nonConnector_concreteValueMatrixArbitrary
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_ofConcreteValueMatrixFamily C

theorem largeClosedPlacement_combinedProjection
    {K0 : Nat}
    (F : LargeClosedPlacementInstantiationW13.AllPositiveFiniteFields)
    (L : LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields K0) :
    LargeClosedPlacementInstantiationW13.ExactTarget /\
      LargeClosedPlacementInstantiationW13.EventualTarget /\
        LargeClosedPlacementInstantiationW13.ArbitraryTarget :=
  exact_eventual_arbitrary_of_allPositiveFiniteFields_and_largeClosedPlacementFields
    F L

theorem splitSoundness_arbitrary_of_exactTarget
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget H

end PachTothSmoke

end

end VerificationLedgerW14
end ErdosProblems1066
