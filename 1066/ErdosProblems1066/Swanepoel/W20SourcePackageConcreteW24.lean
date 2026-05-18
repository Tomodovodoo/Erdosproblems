import ErdosProblems1066.Swanepoel.GeometryClosureSourceConcreteW23
import ErdosProblems1066.Swanepoel.M8ComponentLanesConcreteW23
import ErdosProblems1066.Swanepoel.PointwiseProducerFamilyFieldsW20
import ErdosProblems1066.Swanepoel.RemainingLaneProductConcreteW23
import ErdosProblems1066.Swanepoel.SwanepoelKnownBoundsFromLanesW23

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W24 concrete W20 source-package route

This file records exact adapters from the concrete W23 lane/source packages to
the W20 pointwise source-family fields and to the W20 Swanepoel source package.
The endpoints remain conditional on the supplied packages.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace W20SourcePackageConcreteW24

open MinimalGraphFacts

universe u

noncomputable section

abbrev W20SourcePackage : Type (u + 1) :=
  SwanepoelSourcePackageW20.SwanepoelSourcePackage.{u}

abbrev PointwiseSourceFamilyFields : Type (u + 1) :=
  PointwiseProducerFamilyFieldsW20.PointwiseSourceFamilyFields.{u}

abbrev W19PointwiseProducerFamilyFields : Type (u + 1) :=
  PointwiseProducerFamilyFieldsW20.W19PointwiseProducerFamilyFields.{u}

abbrev GeometryClosureSourcesForPackage
    (P : W20SourcePackage.{u}) : Type (u + 1) :=
  GeometryClosureSourceConcreteW23.GeometryClosureSourcesForPackage.{u} P

abbrev GeometryClosureMatrix : Type (u + 1) :=
  GeometryClosureSourceConcreteW23.GeometryClosureMatrix.{u}

abbrev ComponentLanes : Type (u + 1) :=
  M8BlockersInhabitationW22.ComponentLanes.{u}

abbrev ConcreteComponentLanes : Type (u + 1) :=
  M8ComponentLanesConcreteW23.ConcreteComponentLanes.{u}

abbrev NamedConcreteComponentLanes : Type (u + 1) :=
  M8ComponentLanesConcreteW23.NamedConcreteComponentLanes.{u}

abbrev KnownBoundsLaneProduct : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.LaneProduct

abbrev KnownBoundsMinimalStillOpenComponents : Type 1 :=
  SwanepoelKnownBoundsFromLanesW23.MinimalStillOpenComponents

/-! ## W20 source package to W20 pointwise source fields -/

def actualTopologyArcInputsOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    PointwiseProducerFamilyFieldsW20.ActualTopologyArcInputsFamily.{u} :=
  P.topologyArc.toActualTopologyArcInputsFamily

@[simp]
theorem actualTopologyArcInputsOfW20SourcePackage_inputs
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (actualTopologyArcInputsOfW20SourcePackage P).inputs C hmin =
      (P.topologyArc.row C hmin).toActualTopologyArcInputs :=
  rfl

def lemma9SourceFieldsOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    PointwiseProducerFamilyFieldsW20.Lemma9NatCoverageSourceFamily.{u}
      (PointwiseProducerFamilyFieldsW20.payForCutConcreteProducerFamilyOfNoCutFieldFamily
        P.payForCut)
      (PointwiseProducerFamilyFieldsW20.topologyArcConcreteProducerFamilyOfActualInputsFamily
        (actualTopologyArcInputsOfW20SourcePackage P))
      (PointwiseProducerFamilyFieldsW20.lemma8ConcreteProducerFamilyOfGeometrySourceFamily
        P.lemma8) where
  row := fun C hmin => P.lemma9.row C hmin

def figureSourceFieldsOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    PointwiseProducerFamilyFieldsW20.FigureLocalAngleContainmentSourceFamily.{u}
      (PointwiseProducerFamilyFieldsW20.payForCutConcreteProducerFamilyOfNoCutFieldFamily
        P.payForCut)
      (PointwiseProducerFamilyFieldsW20.topologyArcConcreteProducerFamilyOfActualInputsFamily
        (actualTopologyArcInputsOfW20SourcePackage P))
      (PointwiseProducerFamilyFieldsW20.lemma8ConcreteProducerFamilyOfGeometrySourceFamily
        P.lemma8) where
  row := fun C hmin =>
    { angleContainment := P.figures.angleContainment C hmin }

def pointwiseSourceFamilyFieldsOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    PointwiseSourceFamilyFields.{u} where
  payForCut := P.payForCut
  topologyArc := actualTopologyArcInputsOfW20SourcePackage P
  lemma8 := P.lemma8
  lemma9 := lemma9SourceFieldsOfW20SourcePackage P
  figures := figureSourceFieldsOfW20SourcePackage P

@[simp]
theorem pointwiseSourceFamilyFieldsOfW20SourcePackage_payForCut
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P).payForCut C hmin =
      P.payForCut C hmin :=
  rfl

@[simp]
theorem pointwiseSourceFamilyFieldsOfW20SourcePackage_topologyArc
    (P : W20SourcePackage.{u}) :
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P).topologyArc =
      actualTopologyArcInputsOfW20SourcePackage P :=
  rfl

@[simp]
theorem pointwiseSourceFamilyFieldsOfW20SourcePackage_lemma8
    (P : W20SourcePackage.{u}) :
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P).lemma8 =
      P.lemma8 :=
  rfl

@[simp]
theorem pointwiseSourceFamilyFieldsOfW20SourcePackage_lemma9
    (P : W20SourcePackage.{u}) :
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P).lemma9 =
      lemma9SourceFieldsOfW20SourcePackage P :=
  rfl

@[simp]
theorem pointwiseSourceFamilyFieldsOfW20SourcePackage_figures
    (P : W20SourcePackage.{u}) :
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P).figures =
      figureSourceFieldsOfW20SourcePackage P :=
  rfl

@[simp]
theorem lemma9SourceFieldsOfW20SourcePackage_row
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (lemma9SourceFieldsOfW20SourcePackage P).row C hmin =
      P.lemma9.row C hmin :=
  rfl

@[simp]
theorem figureSourceFieldsOfW20SourcePackage_row_angleContainment
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    ((figureSourceFieldsOfW20SourcePackage P).row C hmin).angleContainment =
      P.figures.angleContainment C hmin :=
  rfl

@[simp]
theorem pointwiseSourceFamilyFieldsOfW20SourcePackage_toW19
    (P : W20SourcePackage.{u}) :
    (pointwiseSourceFamilyFieldsOfW20SourcePackage P).toW19PointwiseProducerFamilyFields =
      P.toPointwiseProducerFamilyFields :=
  rfl

theorem pointwiseSourceFamilyFields_nonempty_of_w20SourcePackage
    (P : W20SourcePackage.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  Nonempty.intro (pointwiseSourceFamilyFieldsOfW20SourcePackage P)

def w19PointwiseProducerFamilyFieldsOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    W19PointwiseProducerFamilyFields.{u} :=
  (pointwiseSourceFamilyFieldsOfW20SourcePackage P)
    |>.toW19PointwiseProducerFamilyFields

@[simp]
theorem w19PointwiseProducerFamilyFieldsOfW20SourcePackage_eq
    (P : W20SourcePackage.{u}) :
    w19PointwiseProducerFamilyFieldsOfW20SourcePackage P =
      P.toPointwiseProducerFamilyFields :=
  rfl

/-! ## W20 source package to geometry closure and minimal-failure elimination -/

def geometryClosureSourcesOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    GeometryClosureSourcesForPackage.{u} P :=
  GeometryClosureSourceConcreteW23.exactSourcesOfW20Package P

@[simp]
theorem geometryClosureSourcesOfW20SourcePackage_eq_w23
    (P : W20SourcePackage.{u}) :
    geometryClosureSourcesOfW20SourcePackage P =
      GeometryClosureSourceConcreteW23.exactSourcesOfW20Package P :=
  rfl

def geometryClosureMatrixOfW20SourcePackage
    (P : W20SourcePackage.{u}) :
    GeometryClosureMatrix.{u} :=
  GeometryClosureSourceConcreteW23.exactMatrixOfW20Package P

@[simp]
theorem geometryClosureMatrixOfW20SourcePackage_row
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (geometryClosureMatrixOfW20SourcePackage P).row C hmin =
      GeometryClosureSourceConcreteW23.exactRowOfW20Package P C hmin :=
  rfl

def minimalClearedFailureEliminatorOfW20SourcePackage
    (P : W20SourcePackage.{0}) :
    MinimalClearedFailureEliminator :=
  GeometryClosureSourceConcreteW23.minimalClearedFailureEliminatorOfW20Package
    P

theorem no_minimalClearedFailure_of_w20SourcePackage
    (P : W20SourcePackage.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  GeometryClosureSourceConcreteW23.no_minimalClearedFailure_of_w20Package P

theorem no_minimalClearedFailure_of_w20SourcePackage_via_pointwise
    (P : W20SourcePackage.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (pointwiseSourceFamilyFieldsOfW20SourcePackage P).no_minimalClearedFailure

theorem no_minimalClearedFailure_of_w20SourcePackage_via_matrix
    (P : W20SourcePackage.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  GeometryClosureSourceConcreteW23.no_minimalClearedFailure_of_w20Package_via_matrix
    P

/-! ## W22/W23 concrete component lanes -/

def w20SourcePackageOfComponentLanes
    (P : ComponentLanes.{u}) :
    W20SourcePackage.{u} :=
  P.toW20SourcePackage

@[simp]
theorem w20SourcePackageOfComponentLanes_eq_w23
    (P : ComponentLanes.{u}) :
    w20SourcePackageOfComponentLanes P =
      GeometryClosureSourceConcreteW23.w20SourcePackageOfLaneProduct P :=
  rfl

def pointwiseSourceFamilyFieldsOfComponentLanes
    (P : ComponentLanes.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  pointwiseSourceFamilyFieldsOfW20SourcePackage
    (w20SourcePackageOfComponentLanes P)

theorem pointwiseSourceFamilyFields_nonempty_of_componentLanes
    (P : ComponentLanes.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  Nonempty.intro (pointwiseSourceFamilyFieldsOfComponentLanes P)

def minimalClearedFailureEliminatorOfComponentLanes
    (P : ComponentLanes.{0}) :
    MinimalClearedFailureEliminator :=
  GeometryClosureSourceConcreteW23.minimalClearedFailureEliminatorOfLaneProduct
    P

theorem no_minimalClearedFailure_of_componentLanes
    (P : ComponentLanes.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  GeometryClosureSourceConcreteW23.no_minimalClearedFailure_of_laneProduct P

def w20SourcePackageOfConcreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    W20SourcePackage.{u} :=
  P.toW20SourcePackage

@[simp]
theorem w20SourcePackageOfConcreteComponentLanes_eq
    (P : ConcreteComponentLanes.{u}) :
    w20SourcePackageOfConcreteComponentLanes P =
      w20SourcePackageOfComponentLanes P.toComponentLanes :=
  rfl

def pointwiseSourceFamilyFieldsOfConcreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  pointwiseSourceFamilyFieldsOfW20SourcePackage
    (w20SourcePackageOfConcreteComponentLanes P)

theorem pointwiseSourceFamilyFields_nonempty_of_concreteComponentLanes
    (P : ConcreteComponentLanes.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  Nonempty.intro (pointwiseSourceFamilyFieldsOfConcreteComponentLanes P)

theorem no_minimalClearedFailure_of_concreteComponentLanes
    (P : ConcreteComponentLanes.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w20SourcePackage
    (w20SourcePackageOfConcreteComponentLanes P)

def w20SourcePackageOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    W20SourcePackage.{u} :=
  P.toW20SourcePackage

@[simp]
theorem w20SourcePackageOfNamedConcreteComponentLanes_eq
    (P : NamedConcreteComponentLanes.{u}) :
    w20SourcePackageOfNamedConcreteComponentLanes P =
      w20SourcePackageOfConcreteComponentLanes P.toConcreteComponentLanes :=
  rfl

def pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    PointwiseSourceFamilyFields.{u} :=
  pointwiseSourceFamilyFieldsOfW20SourcePackage
    (w20SourcePackageOfNamedConcreteComponentLanes P)

theorem pointwiseSourceFamilyFields_nonempty_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{u}) :
    Nonempty PointwiseSourceFamilyFields.{u} :=
  Nonempty.intro (pointwiseSourceFamilyFieldsOfNamedConcreteComponentLanes P)

theorem no_minimalClearedFailure_of_namedConcreteComponentLanes
    (P : NamedConcreteComponentLanes.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w20SourcePackage
    (w20SourcePackageOfNamedConcreteComponentLanes P)

/-! ## W23 known-bound lane gates, still conditional -/

def knownBoundsExposureGateOfKnownBoundsLaneProduct
    (P : KnownBoundsLaneProduct) :
    SwanepoelKnownBoundsFromLanesW23.KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_of_laneProduct P

def knownBoundsExposureGateOfMinimalStillOpenComponents
    (P : KnownBoundsMinimalStillOpenComponents) :
    SwanepoelKnownBoundsFromLanesW23.KnownBoundsExposureGate :=
  SwanepoelKnownBoundsFromLanesW23.knownBoundsExposureGate_of_minimalStillOpenComponents
    P

theorem targetLowerBoundEightThirtyOne_of_knownBoundsLaneProduct
    (P : KnownBoundsLaneProduct) :
    SwanepoelKnownBoundsFromLanesW23.Target :=
  SwanepoelKnownBoundsFromLanesW23.targetLowerBoundEightThirtyOne_of_laneProduct
    P

theorem targetLowerBoundEightThirtyOne_of_knownBoundsMinimalStillOpenComponents
    (P : KnownBoundsMinimalStillOpenComponents) :
    SwanepoelKnownBoundsFromLanesW23.Target :=
  SwanepoelKnownBoundsFromLanesW23.targetLowerBoundEightThirtyOne_of_minimalStillOpenComponents
    P

theorem knownBoundsLaneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty KnownBoundsLaneProduct <->
      Nonempty KnownBoundsMinimalStillOpenComponents :=
  RemainingLaneProductConcreteW23.laneProduct_nonempty_iff_minimalStillOpenComponents

end

end W20SourcePackageConcreteW24
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW24PointwiseSourceFamilyFields : Type (u + 1) :=
  Swanepoel.W20SourcePackageConcreteW24.PointwiseSourceFamilyFields.{u}

abbrev SwanepoelW24W20SourcePackage : Type (u + 1) :=
  Swanepoel.W20SourcePackageConcreteW24.W20SourcePackage.{u}

abbrev SwanepoelW24ConcreteComponentLanes : Type (u + 1) :=
  Swanepoel.W20SourcePackageConcreteW24.ConcreteComponentLanes.{u}

abbrev SwanepoelW24NamedConcreteComponentLanes : Type (u + 1) :=
  Swanepoel.W20SourcePackageConcreteW24.NamedConcreteComponentLanes.{u}

noncomputable def swanepoelW24_pointwiseSourceFamilyFields_of_w20SourcePackage
    (P : SwanepoelW24W20SourcePackage.{u}) :
    SwanepoelW24PointwiseSourceFamilyFields.{u} :=
  Swanepoel.W20SourcePackageConcreteW24.pointwiseSourceFamilyFieldsOfW20SourcePackage
    P

theorem swanepoelW24_no_minimalClearedFailure_of_w20SourcePackage
    (P : SwanepoelW24W20SourcePackage.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :=
  Swanepoel.W20SourcePackageConcreteW24.no_minimalClearedFailure_of_w20SourcePackage
    P

theorem swanepoelW24_no_minimalClearedFailure_of_concreteComponentLanes
    (P : SwanepoelW24ConcreteComponentLanes.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :=
  Swanepoel.W20SourcePackageConcreteW24.no_minimalClearedFailure_of_concreteComponentLanes
    P

theorem swanepoelW24_no_minimalClearedFailure_of_namedConcreteComponentLanes
    (P : SwanepoelW24NamedConcreteComponentLanes.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :=
  Swanepoel.W20SourcePackageConcreteW24.no_minimalClearedFailure_of_namedConcreteComponentLanes
    P

theorem swanepoelW24_knownBoundsLaneProduct_nonempty_iff_minimalStillOpenComponents :
    Nonempty Swanepoel.W20SourcePackageConcreteW24.KnownBoundsLaneProduct <->
      Nonempty
        Swanepoel.W20SourcePackageConcreteW24.KnownBoundsMinimalStillOpenComponents :=
  Swanepoel.W20SourcePackageConcreteW24.knownBoundsLaneProduct_nonempty_iff_minimalStillOpenComponents

end Verified
end ErdosProblems1066
