import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.DirectFlexibleSourcePayloadW33
import ErdosProblems1066.PachToth.FiniteReducedMetricCandidateSearchW33
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11

set_option autoImplicit false

/-!
# W34 deformed length-one source audit

This file isolates the length-one source surface from the refuted exact-base
flexible route.  A genuine collapsed length-one geometry still gives the
desired source, and a genuine transition geometry still gives the W19
transition-certificate facade.  What is checked here is that the current
direct flexible/exact-base period lane cannot be used to produce such a
source: W33's length-one connector row already contradicts the exact-base
distance computation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DeformedLengthOneSourceW34

open FiniteGraph
open FiniteGraph.LocalVertex
open ClosedPlacementSmallKCertificatesW19
open FlexibleTransitionSearchW11

noncomputable section

abbrev DeformedLengthOneGeometry : Type :=
  DeformedPlacement.LengthOneGeometry

abbrev DeformedLengthOneTransitionGeometry : Type :=
  ClosedPlacementSmallKCertificatesW19.DeformedLengthOneTransitionGeometry

abbrev DeformedLengthOneSource : Type :=
  DeformedPlacement.ClosedPlacement 1
    ClosedPlacementSmallKCertificatesW19.onePositive

abbrev LengthOneExplicitTransitionCertificate : Type :=
  ClosedPlacementSmallKCertificatesW19.ExplicitTransitionClosedPlacementCertificate
    1 ClosedPlacementSmallKCertificatesW19.onePositive

abbrev DirectFlexibleSourcePayload : Type :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload

abbrev SameOppositeCandidate : Type :=
  FiniteReducedMetricCandidateSearchW33.SameOppositeCandidate

abbrev PeriodSearchData (T : SameOppositeCandidate) : Type :=
  FiniteReducedMetricCandidateSearchW33.PeriodSearchData T

abbrev FlexiblePeriodLowerTableFamily : Type :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

/-! ## Honest length-one source constructors -/

def sourceOfGeometry
    (geometry : DeformedLengthOneGeometry) :
    DeformedLengthOneSource :=
  ClosedPlacementSmallKCertificatesW19.lengthOneClosedPlacementOfDeformedGeometry
    geometry

def sourceOfTransitionGeometry
    (G : DeformedLengthOneTransitionGeometry) :
    DeformedLengthOneSource :=
  sourceOfGeometry G.geometry

theorem nonempty_source_iff_geometry :
    Nonempty DeformedLengthOneSource <->
      Nonempty DeformedLengthOneGeometry := by
  simpa [DeformedLengthOneSource, DeformedLengthOneGeometry] using
    (DeformedPlacement.nonempty_closedPlacement_one_iff_lengthOneGeometry
      (hpos := ClosedPlacementSmallKCertificatesW19.onePositive))

theorem nonempty_source_of_geometry
    (H : Nonempty DeformedLengthOneGeometry) :
    Nonempty DeformedLengthOneSource := by
  cases H with
  | intro geometry =>
      exact Nonempty.intro (sourceOfGeometry geometry)

theorem nonempty_source_of_transitionGeometry
    (H : Nonempty DeformedLengthOneTransitionGeometry) :
    Nonempty DeformedLengthOneSource := by
  cases H with
  | intro G =>
      exact Nonempty.intro (sourceOfTransitionGeometry G)

theorem nonempty_transitionGeometry_of_lengthOneExplicitCertificate :
    Nonempty LengthOneExplicitTransitionCertificate ->
      Nonempty DeformedLengthOneTransitionGeometry :=
  nonempty_lengthOneExplicitTransitionCertificate_iff_deformedTransitionGeometry.1

/-! ## Checked blocker for the refuted exact-base flexible route -/

theorem exactBase_t2_2_t1_1_not_unit :
    Not
      (_root_.eucDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) = 1) :=
  FiniteReducedMetricCandidateSearchW33.exactBase_T2_2_T1_1_not_unit

theorem not_nonempty_periodSearchData
    (T : SameOppositeCandidate) :
    Not (Nonempty (PeriodSearchData T)) :=
  FiniteReducedMetricCandidateSearchW33.not_nonempty_periodSearchData T

theorem not_nonempty_directFlexibleSourcePayload :
    Not (Nonempty DirectFlexibleSourcePayload) := by
  intro H
  have hshape :
      FiniteReducedMetricCandidateSearchW33.DirectFlexibleSourceShape :=
    directFlexibleSourcePayload_equiv_candidate_period_metric.1 H
  exact FiniteReducedMetricCandidateSearchW33.not_directFlexibleSourceShape hshape

theorem not_nonempty_flexiblePeriodLowerTableFamily :
    Not (Nonempty FlexiblePeriodLowerTableFamily) :=
  FiniteReducedMetricCandidateSearchW33.not_nonempty_flexiblePeriodLowerTableFamily

theorem not_current_directFlexible_route_to_source :
    Not (Nonempty DirectFlexibleSourcePayload /\
      Nonempty DeformedLengthOneSource) := by
  intro H
  exact not_nonempty_directFlexibleSourcePayload H.1

/-- Checked status for the deformed length-one source attempt.

The positive fields are only the honest geometry-to-source forgetful maps.
The negative fields record why the refuted exact-base flexible period lane
does not provide the missing nonempty geometry/source. -/
structure CheckedBlocker : Prop where
  sourceIffCollapsedGeometry :
    Nonempty DeformedLengthOneSource <->
      Nonempty DeformedLengthOneGeometry
  transitionGeometrySuppliesSource :
    Nonempty DeformedLengthOneTransitionGeometry ->
      Nonempty DeformedLengthOneSource
  exactBaseConnectorNotUnit :
    Not
      (_root_.eucDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) = 1)
  periodSearchDataBlocked :
    forall T : SameOppositeCandidate,
      Not (Nonempty (PeriodSearchData T))
  directFlexiblePayloadBlocked :
    Not (Nonempty DirectFlexibleSourcePayload)
  flexiblePeriodLowerTableBlocked :
    Not (Nonempty FlexiblePeriodLowerTableFamily)

theorem checkedBlocker : CheckedBlocker where
  sourceIffCollapsedGeometry := nonempty_source_iff_geometry
  transitionGeometrySuppliesSource := nonempty_source_of_transitionGeometry
  exactBaseConnectorNotUnit := exactBase_t2_2_t1_1_not_unit
  periodSearchDataBlocked := not_nonempty_periodSearchData
  directFlexiblePayloadBlocked := not_nonempty_directFlexibleSourcePayload
  flexiblePeriodLowerTableBlocked := not_nonempty_flexiblePeriodLowerTableFamily

end

end DeformedLengthOneSourceW34
end PachToth

namespace Verified

abbrev PachTothW34DeformedLengthOneSource : Type :=
  PachToth.DeformedLengthOneSourceW34.DeformedLengthOneSource

abbrev PachTothW34DeformedLengthOneTransitionGeometry : Type :=
  PachToth.DeformedLengthOneSourceW34.DeformedLengthOneTransitionGeometry

theorem pachtoth_w34_deformedLengthOneSource_of_transitionGeometry
    (H : Nonempty PachTothW34DeformedLengthOneTransitionGeometry) :
    Nonempty PachTothW34DeformedLengthOneSource :=
  PachToth.DeformedLengthOneSourceW34.nonempty_source_of_transitionGeometry H

theorem pachtoth_w34_not_directFlexibleSourcePayload :
    Not
      (Nonempty
        PachToth.DeformedLengthOneSourceW34.DirectFlexibleSourcePayload) :=
  PachToth.DeformedLengthOneSourceW34.not_nonempty_directFlexibleSourcePayload

theorem pachtoth_w34_deformedLengthOne_checkedBlocker :
    PachToth.DeformedLengthOneSourceW34.CheckedBlocker :=
  PachToth.DeformedLengthOneSourceW34.checkedBlocker

end Verified
end ErdosProblems1066
