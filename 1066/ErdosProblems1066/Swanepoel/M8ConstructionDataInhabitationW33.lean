import ErdosProblems1066.Swanepoel.BrokenLatticeMinimalFailureConstructionW26
import ErdosProblems1066.Swanepoel.SwanepoelW32RouteAudit
import ErdosProblems1066.Swanepoel.K23RouteCoverageSourceW34
import ErdosProblems1066.Swanepoel.ExactFigureWitnessSourceW34
import ErdosProblems1066.Swanepoel.SelectedTopologyRowsInhabitationW33
import ErdosProblems1066.Swanepoel.BoundaryArcFiniteWalkConstructionW16
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleSourceW34

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 2000000

/-!
# W33 M8 construction-data inhabitance

This file exposes the direct inhabitance route for
`BrokenLatticeMinimalFailure.M8ConstructionData`.

The W32 actual route source already contains actual topology components,
frame/cyclic rows, no-early route data, and exact Figure E22/E23 rows.  We
forget that package only as far as the W20 pointwise source family, recover
the W16 pointwise row, and then build the seven honest fields consumed by
`BrokenLatticeMinimalFailure.M8ConstructionData.contradiction`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8ConstructionDataInhabitationW33

universe u

noncomputable section

abbrev ComponentFrameNoEarlyFigureSourceData : Type (u + 1) :=
  NoCutPointwiseBridgeW32.ComponentFrameNoEarlyFigureSourceData.{u}

abbrev ActualRouteSourceData : Type (u + 1) :=
  SwanepoelW32RouteAudit.ActualRouteSource.SourceData.{u}

abbrev StrongestRouteSource : Type 1 :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.RouteSource

abbrev StrongestRouteCertificate : Prop :=
  SwanepoelW32RouteAudit.StrongestHonestRoute.RouteCertificate

abbrev PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseSourceFieldsInhabitationW25.PointwiseSourceFamilyFields.{u}

abbrev PointwiseW16AssemblyFamily : Type (u + 1) :=
  PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyFamily.{u}

abbrev PointwiseW16AssemblyInputs {n : Nat}
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyInputs.{u} C hmin

/-! ## Component source to honest M8 construction data -/

def pointwiseSourceFamilyFieldsOfComponentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  S.toSourceData.toPointwiseSourceFamilyFields

def pointwiseFamilyOfComponentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    PointwiseW16AssemblyFamily.{u} :=
  (pointwiseSourceFamilyFieldsOfComponentSource S).toPointwiseW16AssemblyFamily

def pointwiseRowOfComponentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    PointwiseW16AssemblyInputs.{u} C hmin :=
  (pointwiseFamilyOfComponentSource S).row C hmin

def m8ConstructionDataOfComponentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  BrokenLatticeMinimalFailureConstructionW26.m8ConstructionDataOfPointwiseRow
    (pointwiseRowOfComponentSource S C hmin)

theorem contradiction_of_componentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u})
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  (m8ConstructionDataOfComponentSource S C hmin).contradiction

def m8ConstructionEliminatorOfComponentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro (m8ConstructionDataOfComponentSource S C hmin)

theorem no_minimalClearedFailure_of_componentSource
    (S : ComponentFrameNoEarlyFigureSourceData.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) :=
  BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator
    (m8ConstructionEliminatorOfComponentSource S)

/-! ## W32 actual-route source to honest M8 construction data -/

def componentSourceOfActualRouteSource
    (S : ActualRouteSourceData.{u}) :
    ComponentFrameNoEarlyFigureSourceData.{u} :=
  S.toComponentFrameNoEarlyFigureSourceData

def pointwiseSourceFamilyFieldsOfActualRouteSource
    (S : ActualRouteSourceData.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  pointwiseSourceFamilyFieldsOfComponentSource
    (componentSourceOfActualRouteSource S)

def pointwiseFamilyOfActualRouteSource
    (S : ActualRouteSourceData.{u}) :
    PointwiseW16AssemblyFamily.{u} :=
  (pointwiseSourceFamilyFieldsOfActualRouteSource S).toPointwiseW16AssemblyFamily

def pointwiseRowOfActualRouteSource
    (S : ActualRouteSourceData.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    PointwiseW16AssemblyInputs.{u} C hmin :=
  (pointwiseFamilyOfActualRouteSource S).row C hmin

def m8ConstructionDataOfActualRouteSource
    (S : ActualRouteSourceData.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  BrokenLatticeMinimalFailureConstructionW26.m8ConstructionDataOfPointwiseRow
    (pointwiseRowOfActualRouteSource S C hmin)

theorem m8ConstructionDataOfActualRouteSource_eq_componentSource
    (S : ActualRouteSourceData.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    m8ConstructionDataOfActualRouteSource S C hmin =
      m8ConstructionDataOfComponentSource
        (componentSourceOfActualRouteSource S) C hmin :=
  rfl

theorem contradiction_of_actualRouteSource
    (S : ActualRouteSourceData.{u})
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  (m8ConstructionDataOfActualRouteSource S C hmin).contradiction

def m8ConstructionEliminatorOfActualRouteSource
    (S : ActualRouteSourceData.{u}) :
    BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro (m8ConstructionDataOfActualRouteSource S C hmin)

theorem no_minimalClearedFailure_of_actualRouteSource
    (S : ActualRouteSourceData.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) :=
  BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator
    (m8ConstructionEliminatorOfActualRouteSource S)

/-! ## Generated finite-spine exact-source route to M8 construction data -/

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_localHonestRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (localHonestRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    Nonempty ActualRouteSourceData.{0} := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
      exactTarget boundaryRows missingPackage
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut :=
        SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
      (components :=
        SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)
      finitePQGeneratedOrderRows
  have hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows
      realizationCarrierRows badAdjacencyRows H componentClosure frameSource
  have hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_localHonestEuclideanRows
      (P := frameSource) localHonestRows
  exact
    SwanepoelW32RouteAudit.ActualRouteSource.sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
      H componentClosure frameSource hRoute hFigures

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    Nonempty ActualRouteSourceData.{0} := by
  have hLocal :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows :=
    ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows
      s5Rows
  exact
    actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_localHonestRows
      H exactTarget boundaryRows missingPackage finitePQGeneratedOrderRows
      realizationCarrierRows badAdjacencyRows hLocal

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    Nonempty ActualRouteSourceData.{0} :=
  actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
    H exactTarget boundaryRows missingPackage
    (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      generatedOrderRows)
    realizationCarrierRows badAdjacencyRows s5Rows

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_localHonestRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (localHonestRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    Nonempty ActualRouteSourceData.{0} :=
  actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_localHonestRows
    H exactTarget boundaryRows missingPackage
    (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      generatedOrderRows)
    realizationCarrierRows badAdjacencyRows localHonestRows

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacencyIncidence_localHonestRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (localHonestRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    Nonempty ActualRouteSourceData.{0} := by
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
      exactTarget boundaryRows missingPackage
  let finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      generatedOrderRows
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut :=
        SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
      (components :=
        SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)
      finitePQGeneratedOrderRows
  have hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborIncidenceRows
      realizationCarrierRows incidenceRows H componentClosure frameSource
  have hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_localHonestEuclideanRows
      (P := frameSource) localHonestRows
  exact
    SwanepoelW32RouteAudit.ActualRouteSource.sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
      H componentClosure frameSource hRoute hFigures

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_nonempty_finiteWalkFrameCoreGeneratedOrderSourceRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      Nonempty
        (FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage))))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      forall finitePQGeneratedOrderRows :
        FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage)),
        ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
          finitePQGeneratedOrderRows) :
    Nonempty ActualRouteSourceData.{0} := by
  cases generatedOrderRows with
  | intro generatedOrderRows =>
      let finitePQGeneratedOrderRows :
          FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
            (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              H)
            (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
              (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
                exactTarget boundaryRows missingPackage)) :=
        FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows
      exact
        actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
          H exactTarget boundaryRows missingPackage
          finitePQGeneratedOrderRows realizationCarrierRows
          badAdjacencyRows (s5Rows finitePQGeneratedOrderRows)

theorem actualRouteSourceData_nonempty_of_exactClosureMissingField_nonempty_finiteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      Nonempty
        (FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage))))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      forall finitePQGeneratedOrderRows :
        FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage)),
        ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
          finitePQGeneratedOrderRows) :
    Nonempty ActualRouteSourceData.{0} := by
  cases generatedOrderRows with
  | intro generatedOrderRows =>
      let finitePQGeneratedOrderRows :
          FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
            (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
              H)
            (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
              (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
                exactTarget boundaryRows missingPackage)) :=
        FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows
          generatedOrderRows
      exact
        actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
          H exactTarget boundaryRows missingPackage
          finitePQGeneratedOrderRows realizationCarrierRows
          badAdjacencyRows (s5Rows finitePQGeneratedOrderRows)

theorem actualRouteSourceData_nonempty_of_exactTopology_longArc_finitePQTheorem_generatedFiniteWalk_realizationCarrier_badAdjacencyIncidence_localHonestRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget boundaryRows))
    (finitePQTheorem :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget boundaryRows longArc finitePQTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyIncidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (localHonestRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    Nonempty ActualRouteSourceData.{0} := by
  let missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows :=
    SelectedTopologyRowsInhabitationW33.exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      exactTarget boundaryRows longArc finitePQTheorem
  exact
    actualRouteSourceData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacencyIncidence_localHonestRows
      H exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyIncidenceRows localHonestRows

theorem actualRouteSourceData_nonempty_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutBlockerEliminationW24.noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    Nonempty ActualRouteSourceData.{0} := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  exact
    actualRouteSourceData_nonempty_of_exactTopology_longArc_finitePQTheorem_generatedFiniteWalk_realizationCarrier_badAdjacencyIncidence_localHonestRows
      NoCutBlockerEliminationW24.noCutVertexFamily_of_refuting_bothPlusSidesCutForced
      exactTarget boundaryRows longArc finitePQSuccessorRowsTheorem
      generatedOrderRows realizationCarrierRows incidenceRows
      (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows
        s5Rows)

theorem m8ConstructionData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  have hSource :
      Nonempty ActualRouteSourceData.{0} :=
    actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
      H exactTarget boundaryRows missingPackage finitePQGeneratedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows
  cases hSource with
  | intro S =>
      exact Nonempty.intro (m8ConstructionDataOfActualRouteSource S C hmin)

theorem m8ConstructionData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  exact
    m8ConstructionData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
      H exactTarget boundaryRows missingPackage
      (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
        generatedOrderRows)
      realizationCarrierRows badAdjacencyRows s5Rows C hmin

theorem m8ConstructionData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_localHonestRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (localHonestRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  have hSource :
      Nonempty ActualRouteSourceData.{0} :=
    actualRouteSourceData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_localHonestRows
      H exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyRows localHonestRows
  cases hSource with
  | intro S =>
      exact Nonempty.intro (m8ConstructionDataOfActualRouteSource S C hmin)

theorem m8ConstructionData_nonempty_of_exactTopology_longArc_finitePQTheorem_generatedFiniteWalk_realizationCarrier_badAdjacencyIncidence_localHonestRows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget boundaryRows))
    (finitePQTheorem :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget boundaryRows longArc finitePQTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyIncidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (localHonestRows :
      ExactFigureWitnessSourceW34.LocalHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  let missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows :=
    SelectedTopologyRowsInhabitationW33.exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      exactTarget boundaryRows longArc finitePQTheorem
  exact
    m8ConstructionData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_localHonestRows
      H exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows
      (K23RouteCoverageSourceW34.selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_incidenceRows
        badAdjacencyIncidenceRows)
      localHonestRows C hmin

theorem m8ConstructionData_nonempty_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyFinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  exact
    m8ConstructionData_nonempty_of_exactTopology_longArc_finitePQTheorem_generatedFiniteWalk_realizationCarrier_badAdjacencyIncidence_localHonestRows
      NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced
      exactTarget boundaryRows longArc finitePQSuccessorRowsTheorem
      generatedOrderRows realizationCarrierRows incidenceRows
      (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows
        s5Rows)
      C hmin

theorem m8ConstructionData_nonempty_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget
        (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
          exactTarget sectorTheorem))
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
            (SelectedTopologyRowsInhabitationW33.remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
              exactTarget)
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            (SelectedTopologyRowsInhabitationW33.missingLongArcTriangleRunFieldOfExactActualTopologyClosureMissingFieldPackage
              exactTarget
              (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
                exactTarget sectorTheorem)
              missingPackage))))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  let boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget :=
    OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
      exactTarget sectorTheorem
  let componentClosure :
      SwanepoelW32RouteAudit.ActualRouteSource.ActualTopologyComponentClosurePackage.{0} :=
    SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRows
      (SelectedTopologyRowsInhabitationW33.remainingActualOuterBoundaryCycleTheoremTargetOfExactActualTopologyFieldsTarget
        exactTarget)
      boundaryRows
      (SelectedTopologyRowsInhabitationW33.missingLongArcTriangleRunFieldOfExactActualTopologyClosureMissingFieldPackage
        exactTarget boundaryRows missingPackage)
  let finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
      generatedOrderRows
  let frameSource :
      SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicSourcePackage.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure) :=
    FrameCyclicOrderAssemblyW32.frameCyclicSourcePackageOfFinitePQSpineGeneratedOrderRows
      (noCut :=
        SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced)
      (components :=
        SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          componentClosure)
      finitePQGeneratedOrderRows
  have hRoute :
      SwanepoelW32RouteAudit.ActualRouteSource.RouteCoverageAvailable
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    K23RouteCoverageSourceW34.routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows
      realizationCarrierRows badAdjacencyRows
      NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource
  have hFigures :
      SwanepoelW32RouteAudit.ActualRouteSource.FigureEuclideanSourceComponents
        (SwanepoelW32RouteAudit.ActualRouteSource.frameCyclicRowsOfFrameCyclicSourcePackage
          frameSource) :=
    ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFrameCyclicSource_of_localHonestEuclideanRows
      (P := frameSource)
      (ExactFigureWitnessSourceW34.localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows
        s5Rows)
  have hSource :
      Nonempty ActualRouteSourceData.{0} :=
    SwanepoelW32RouteAudit.ActualRouteSource.sourceData_nonempty_of_actualTopologyClosure_frameRouteCoverage_figureComponents
      NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced
      componentClosure frameSource hRoute hFigures
  cases hSource with
  | intro S =>
      exact Nonempty.intro (m8ConstructionDataOfActualRouteSource S C hmin)

theorem m8ConstructionData_nonempty_of_exactClosureMissingField_nonempty_finiteWalkFrameCoreGeneratedOrderSourceRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      Nonempty
        (FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage))))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      forall finitePQGeneratedOrderRows :
        FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage)),
        ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
          finitePQGeneratedOrderRows)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  have hSource :
      Nonempty ActualRouteSourceData.{0} :=
    actualRouteSourceData_nonempty_of_exactClosureMissingField_nonempty_finiteWalkFrameCoreGeneratedOrderSourceRows_badAdjacency_s5Rows
      H exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows
  cases hSource with
  | intro S =>
      exact Nonempty.intro (m8ConstructionDataOfActualRouteSource S C hmin)

theorem m8ConstructionData_nonempty_of_exactClosureMissingField_nonempty_finiteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      Nonempty
        (FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage))))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      forall finitePQGeneratedOrderRows :
        FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
          (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
            H)
          (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
            (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
              exactTarget boundaryRows missingPackage)),
        ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
          finitePQGeneratedOrderRows)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) := by
  have hSource :
      Nonempty ActualRouteSourceData.{0} :=
    actualRouteSourceData_nonempty_of_exactClosureMissingField_nonempty_finiteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows_badAdjacency_s5Rows
      H exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows
  cases hSource with
  | intro S =>
      exact Nonempty.intro (m8ConstructionDataOfActualRouteSource S C hmin)

theorem contradiction_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False := by
  have hData :
      Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) :=
    m8ConstructionData_nonempty_of_exactClosureMissingField_generatedFiniteWalk_badAdjacency_s5Rows
      H exactTarget boundaryRows missingPackage generatedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows C hmin
  cases hData with
  | intro D =>
      exact D.contradiction

theorem contradiction_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows))
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False := by
  have hData :
      Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin) :=
    m8ConstructionData_nonempty_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
      exactTarget sectorTheorem longArc finitePQSuccessorRowsTheorem
      generatedOrderRows realizationCarrierRows incidenceRows s5Rows C hmin
  cases hData with
  | intro D =>
      exact D.contradiction

/-! ## Strongest W32 route certificate endpoint -/

theorem routeCertificate_of_actualRouteSourceData
    (h : Nonempty ActualRouteSourceData.{0}) :
    StrongestRouteCertificate :=
  h

theorem routeCertificate_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
    (H : SwanepoelW32RouteAudit.ActualRouteSource.NoCutVertexFamily)
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (boundaryRows :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologySkeletonRemainderRows.{0}
        exactTarget)
    (missingPackage :
      SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage.{0}
        exactTarget boundaryRows)
    (finitePQGeneratedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFinitePQSpineGeneratedOrderRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          H)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyClosureMissingFieldPackage
            exactTarget boundaryRows missingPackage)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (badAdjacencyRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        finitePQGeneratedOrderRows) :
    StrongestRouteCertificate :=
  routeCertificate_of_actualRouteSourceData
    (actualRouteSourceData_nonempty_of_exactClosureMissingField_finitePQGeneratedOrderRows_badAdjacency_s5Rows
      H exactTarget boundaryRows missingPackage finitePQGeneratedOrderRows
      realizationCarrierRows badAdjacencyRows s5Rows)

theorem routeCertificate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
    (exactTarget :
      SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget)
    (sectorTheorem :
      OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem
        (OuterBoundaryAngleSourceW34.nondegenerateMissingTopologyFactsTargetOfExactActualTopologyFieldsTarget
          exactTarget))
    (longArc :
      SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyLongArcFieldFamily.{0}
        (SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologySkeletonFamilyOfExactActualTopologyFieldsTarget
          exactTarget
          (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
            exactTarget sectorTheorem)))
    (finitePQSuccessorRowsTheorem :
      BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{0})
    (generatedOrderRows :
      FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.{0}
        (SwanepoelW32RouteAudit.ActualRouteSource.noCutDependencyOfNoCutVertexFamily
          NoCutBlockerEliminationW24.noCutVertexFamily_of_refuting_bothPlusSidesCutForced)
        (SwanepoelW32RouteAudit.ActualRouteSource.componentFamilyOfActualTopologyClosurePackage
          (SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfExactActualTopologyFieldsTargetSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem
            exactTarget
            (OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfExactActualTopologyFieldsTargetOuterFaceSectorOrderTheorem
              exactTarget sectorTheorem)
            longArc finitePQSuccessorRowsTheorem)))
    (realizationCarrierRows :
      K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem.{0})
    (incidenceRows :
      K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborIncidenceRows.{0})
    (s5Rows :
      ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource
        (FrameCyclicOrderAssemblyW32.selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows
          generatedOrderRows)) :
    StrongestRouteCertificate :=
  routeCertificate_of_actualRouteSourceData
    (actualRouteSourceData_nonempty_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
      exactTarget sectorTheorem longArc finitePQSuccessorRowsTheorem
      generatedOrderRows realizationCarrierRows incidenceRows s5Rows)

def m8ConstructionDataOfStrongestRouteSource
    (S : StrongestRouteSource)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  m8ConstructionDataOfActualRouteSource S C hmin

theorem contradiction_of_strongestRouteSource
    (S : StrongestRouteSource)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  (m8ConstructionDataOfStrongestRouteSource S C hmin).contradiction

theorem contradiction_of_routeCertificate
    (h : Nonempty StrongestRouteSource)
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False := by
  cases h with
  | intro S =>
      exact contradiction_of_strongestRouteSource S hmin

theorem no_minimalClearedFailure_of_routeCertificate
    (h : Nonempty StrongestRouteSource) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (MinimalGraphFacts.IsMinimalClearedFailure C) := by
  intro n C hmin
  exact contradiction_of_routeCertificate h hmin

end

end M8ConstructionDataInhabitationW33
end Swanepoel
end ErdosProblems1066
