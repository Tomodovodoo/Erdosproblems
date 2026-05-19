import ErdosProblems1066.Swanepoel.BoundaryWalkClassificationConcrete
import ErdosProblems1066.Swanepoel.SubpolygonFaceReductionW14
import ErdosProblems1066.Swanepoel.SubpolygonInstantiation

set_option autoImplicit false

/-!
# W33 concrete subpolygon angle realizations

This module supplies the face-subpolygon realization surface for E13.  The
subpolygon geometry is the selected face and finite induced vertex set from
`SubpolygonInstantiation`; the angle data is an actual
`ConcreteAngleRealization` indexed by the boundary cycle and induced vertex
set computed from that geometry.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonConcreteRealizationW33

open BoundaryCounting
open BoundaryWalkClassificationConcrete
open FaceReduction
open SubpolygonAngleRealization
open SubpolygonDataConcrete
open SubpolygonFaceReductionW14
open SubpolygonInstantiation

universe u v

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-! ## Core face-subpolygon realization families -/

/-- The checked E13 low-degree family induced directly by concrete
face-subpolygon angle realizations over an outer-boundary core. -/
def checkedLowDegreeFamilyOfCoreFaceRealizationFamily
    {core : OuterBoundaryCore G}
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core) :
    CheckedLowDegreeFamily.{u} where
  Subpolygon := F.Subpolygon
  counts := fun S => (F.subpolygonData S).counts
  lowDegreeWithHighDegreeSlack := fun S =>
    (F.subpolygonData S).lowDegreeWithHighDegreeSlack
  lowDegree := fun S => (F.subpolygonData S).lowDegree

@[simp]
theorem checkedLowDegreeFamilyOfCoreFaceRealizationFamily_counts
    {core : OuterBoundaryCore G}
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (S : F.Subpolygon) :
    (checkedLowDegreeFamilyOfCoreFaceRealizationFamily F).counts S =
      (F.subpolygonData S).counts :=
  rfl

/-- E13 low degree from a core face-subpolygon family with pointwise concrete
angle realizations. -/
theorem coreFaceRealizationFamily_lowDegree
    {core : OuterBoundaryCore G}
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  (checkedLowDegreeFamilyOfCoreFaceRealizationFamily F).lowDegree S

/-! ## Realization-carrier contradiction rows -/

/-- A strict carrier over a pointwise core-subpolygon realization family is
impossible by the E13 row carried by the same realized family. -/
theorem coreSubpolygonAngleRealizationFamily_carrier_false
    {core : OuterBoundaryCore G}
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (carrier :
      CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData) :
    False :=
  carrier.false

/-- If every occurrence of a bad row would produce a strict carrier over the
same pointwise realization family, then the bad row is impossible. -/
theorem not_badRow_of_coreSubpolygonAngleRealizationFamily_carrierRow
    {core : OuterBoundaryCore G}
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    {Bad : Prop}
    (hcarrier :
      Bad ->
        Nonempty
          (CoreSubpolygonCarrierCountData
            F.toCoreSubpolygonFamilyData)) :
    Not Bad := by
  intro hbad
  cases hcarrier hbad with
  | intro carrier =>
      exact coreSubpolygonAngleRealizationFamily_carrier_false F carrier

/-- Rowwise version of the realization-carrier contradiction: pointwise
strict carriers reduce a bad-row family to pointwise no-bad rows. -/
theorem noBadRows_of_coreSubpolygonAngleRealizationFamily_carrierRows
    {core : OuterBoundaryCore G}
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    {Idx : Type v}
    {Bad : Idx -> Prop}
    (hcarrier :
      forall i : Idx,
        Bad i ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreSubpolygonFamilyData)) :
    forall i : Idx, Not (Bad i) := by
  intro i
  exact
    not_badRow_of_coreSubpolygonAngleRealizationFamily_carrierRow
      F (hcarrier i)

/-- For pointwise realization families, carrier rows are equivalent to no-bad
rows.  The forward direction is the E13 strict-carrier contradiction; the
reverse direction fills the carrier obligation from the impossible bad row. -/
theorem coreSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows
    {core : OuterBoundaryCore G}
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    {Idx : Type v}
    (Bad : Idx -> Prop) :
    (forall i : Idx,
        Bad i ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreSubpolygonFamilyData)) <->
      forall i : Idx, Not (Bad i) := by
  constructor
  case mp =>
    intro hcarrier
    exact
      noBadRows_of_coreSubpolygonAngleRealizationFamily_carrierRows
        F hcarrier
  case mpr =>
    intro hno i hbad
    exact False.elim (hno i hbad)

/-- Face-boundary realization families use the same E13 strict-carrier
contradiction after forgetting to the generic core-subpolygon family. -/
theorem coreFaceSubpolygonAngleRealizationFamily_carrier_false
    {core : OuterBoundaryCore G}
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (carrier :
      CoreSubpolygonCarrierCountData
        F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    False :=
  carrier.false

/-- Rowwise face-boundary version of the realization-carrier contradiction. -/
theorem noBadRows_of_coreFaceSubpolygonAngleRealizationFamily_carrierRows
    {core : OuterBoundaryCore G}
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    {Idx : Type v}
    {Bad : Idx -> Prop}
    (hcarrier :
      forall i : Idx,
        Bad i ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) :
    forall i : Idx, Not (Bad i) := by
  intro i hbad
  cases hcarrier i hbad with
  | intro carrier =>
      exact coreFaceSubpolygonAngleRealizationFamily_carrier_false F carrier

/-- For face-boundary realization families, carrier rows are equivalent to
pointwise no-bad rows after forgetting to the aggregate core-subpolygon
family. -/
theorem coreFaceSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows
    {core : OuterBoundaryCore G}
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    {Idx : Type v}
    (Bad : Idx -> Prop) :
    (forall i : Idx,
        Bad i ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) <->
      forall i : Idx, Not (Bad i) := by
  constructor
  case mp =>
    intro hcarrier
    exact
      noBadRows_of_coreFaceSubpolygonAngleRealizationFamily_carrierRows
        F hcarrier
  case mpr =>
    intro hno i hbad
    exact False.elim (hno i hbad)

/-! ## Boundary gap no-bad rows from realization carriers -/

/-- The raw four-field component pattern behind a strict
gap/triangle/degree-3-or-4 row: a degree-three non-long-arc boundary index,
followed by a triangular successor edge whose next vertex has degree three or
four. -/
abbrev BoundaryGapTriangleDegree34ComponentPattern
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (k : Fin core.outerCycle.length) : Prop :=
  IsDegree3 G (core.outerCycle.vertex k) /\
    Not (classification.longArc k) /\
    IsTriangleEdge G (core.outerCycle.edge (core.outerCycle.next k)) /\
    (IsDegree3 G (core.outerCycle.vertex (core.outerCycle.next k)) \/
      IsDegree4 G (core.outerCycle.vertex (core.outerCycle.next k)))

/-- The named boundary-gap row is exactly the raw component pattern used by
the selected no-gap branch. -/
theorem boundaryGapTriangleDegree34Row_iff_componentPattern
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (k : Fin core.outerCycle.length) :
    OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        classification k <->
      BoundaryGapTriangleDegree34ComponentPattern classification k :=
  OuterBoundaryClassificationInputs.boundaryGapTriangleDegree34Row_iff_components
    classification k

/-- Pointwise E13 contradiction for the raw boundary component pattern over a
core-subpolygon realization family.  Thus the only remaining geometric input
for a fixed bad boundary index is a concrete strict carrier over the same
realized subpolygon family. -/
theorem not_componentPattern_of_coreSubpolygonAngleRealizationFamily_componentCarrier
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    {k : Fin core.outerCycle.length}
    (hcarrier :
      BoundaryGapTriangleDegree34ComponentPattern classification k ->
        CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData) :
    Not (BoundaryGapTriangleDegree34ComponentPattern classification k) := by
  intro hpattern
  exact
    coreSubpolygonAngleRealizationFamily_carrier_false
      F (hcarrier hpattern)

/-- Exact carrier rows for the raw boundary component pattern give the actual
pointwise no-bad component rows over a core-subpolygon realization family. -/
theorem noBadComponentPatterns_of_coreSubpolygonAngleRealizationFamily_componentCarrierRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData) :
    forall k : Fin core.outerCycle.length,
      Not (BoundaryGapTriangleDegree34ComponentPattern classification k) := by
  intro k
  exact
    not_componentPattern_of_coreSubpolygonAngleRealizationFamily_componentCarrier
      classification F (hcarrier k)

/-- For a pointwise core-subpolygon realization family, carriers attached to
the raw four-field boundary pattern are equivalent to excluding that pattern
at every boundary index. -/
theorem coreSubpolygonAngleRealizationFamily_componentPatternCarrierRows_iff_noBadRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core) :
    (forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData)) <->
      forall k : Fin core.outerCycle.length,
        Not (BoundaryGapTriangleDegree34ComponentPattern classification k) :=
  coreSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows
    F (fun k : Fin core.outerCycle.length =>
      BoundaryGapTriangleDegree34ComponentPattern classification k)

/-- Realization-level carrier rows for the concrete degree/long-arc/triangular
successor pattern prove the actual pointwise no-bad component rows. -/
theorem noBadComponentPatterns_of_coreSubpolygonAngleRealizationFamily_carrierRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData)) :
    forall k : Fin core.outerCycle.length,
      Not (BoundaryGapTriangleDegree34ComponentPattern classification k) :=
  (coreSubpolygonAngleRealizationFamily_componentPatternCarrierRows_iff_noBadRows
    classification F).1 hcarrier

/-- The component-pattern no-bad rows coming from realization carriers produce
the full selected boundary no-gap rows. -/
theorem no_boundaryGapTriangleDegree34Rows_of_coreSubpolygonAngleRealizationFamily_componentCarrierRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData)) :
    forall k : Fin core.outerCycle.length,
      Not
        (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) := by
  exact
    OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      classification
      (noBadComponentPatterns_of_coreSubpolygonAngleRealizationFamily_carrierRows
        classification F hcarrier)

/-- Exact component-pattern carrier rows over a core-subpolygon realization
family produce the selected boundary no-gap rows. -/
theorem no_boundaryGapTriangleDegree34Rows_of_coreSubpolygonAngleRealizationFamily_componentCarrierRowsExact
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData) :
    forall k : Fin core.outerCycle.length,
      Not
        (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) := by
  exact
    OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      classification
      (noBadComponentPatterns_of_coreSubpolygonAngleRealizationFamily_componentCarrierRows
        classification F hcarrier)

/-- Carrier rows for the named boundary-gap row itself are equivalent to the
actual no-gap row required by the selected S4 branch. -/
theorem coreSubpolygonAngleRealizationFamily_boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreSubpolygonAngleRealizationFamilyData.{u} core) :
    (forall k : Fin core.outerCycle.length,
        OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData F.toCoreSubpolygonFamilyData)) <->
      forall k : Fin core.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k) :=
  coreSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows
    F (fun k : Fin core.outerCycle.length =>
      OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        classification k)

/-- Face-boundary realization version of the component-pattern carrier/no-bad
reduction. -/
theorem noBadComponentPatterns_of_coreFaceSubpolygonAngleRealizationFamily_carrierRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) :
    forall k : Fin core.outerCycle.length,
      Not (BoundaryGapTriangleDegree34ComponentPattern classification k) :=
  (coreFaceSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows
    F (fun k : Fin core.outerCycle.length =>
      BoundaryGapTriangleDegree34ComponentPattern classification k)).1
    hcarrier

/-- Pointwise E13 contradiction for the raw boundary component pattern over a
face-subpolygon realization family.  A concrete strict carrier over the same
realized face-subpolygon family is already impossible. -/
theorem not_componentPattern_of_coreFaceSubpolygonAngleRealizationFamily_componentCarrier
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    {k : Fin core.outerCycle.length}
    (hcarrier :
      BoundaryGapTriangleDegree34ComponentPattern classification k ->
        CoreSubpolygonCarrierCountData
          F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    Not (BoundaryGapTriangleDegree34ComponentPattern classification k) := by
  intro hpattern
  exact
    coreFaceSubpolygonAngleRealizationFamily_carrier_false
      F (hcarrier hpattern)

/-- Exact carrier rows for the raw boundary component pattern give the actual
pointwise no-bad component rows over a face-subpolygon realization family. -/
theorem noBadComponentPatterns_of_coreFaceSubpolygonAngleRealizationFamily_componentCarrierRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          CoreSubpolygonCarrierCountData
            F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    forall k : Fin core.outerCycle.length,
      Not (BoundaryGapTriangleDegree34ComponentPattern classification k) := by
  intro k
  exact
    not_componentPattern_of_coreFaceSubpolygonAngleRealizationFamily_componentCarrier
      classification F (hcarrier k)

/-- Face-boundary realization carrier rows for the concrete
degree/long-arc/triangular-successor pattern produce the selected boundary
no-gap rows. -/
theorem no_boundaryGapTriangleDegree34Rows_of_coreFaceSubpolygonAngleRealizationFamily_componentCarrierRows
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) :
    forall k : Fin core.outerCycle.length,
      Not
        (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) := by
  exact
    OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      classification
      (noBadComponentPatterns_of_coreFaceSubpolygonAngleRealizationFamily_carrierRows
        classification F hcarrier)

/-- Exact component-pattern carrier rows over a face-subpolygon realization
family produce the selected boundary no-gap rows. -/
theorem no_boundaryGapTriangleDegree34Rows_of_coreFaceSubpolygonAngleRealizationFamily_componentCarrierRowsExact
    {core : OuterBoundaryCore G}
    (classification : OuterBoundaryClassificationInputs core)
    (F : CoreFaceSubpolygonAngleRealizationFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          CoreSubpolygonCarrierCountData
            F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    forall k : Fin core.outerCycle.length,
      Not
        (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) := by
  exact
    OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      classification
      (noBadComponentPatterns_of_coreFaceSubpolygonAngleRealizationFamily_componentCarrierRows
        classification F hcarrier)

/-! ## Flattened selected face-subpolygon realizations -/

/-- A selected face-subpolygon geometry together with actual pointwise real
angle data for the induced boundary-degree counts computed from that geometry.
-/
structure FaceSubpolygonRealizationData
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  geometry : FaceSubpolygonFields D
  angleRealization :
    ConcreteAngleRealization G
      geometry.toGeometryData.boundary
      geometry.toGeometryData.vertexSet

namespace FaceSubpolygonRealizationData

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The computed E13 counts determined by the selected subpolygon geometry. -/
def counts (S : FaceSubpolygonRealizationData D) :
    SubpolygonDegreeCounts :=
  S.geometry.counts

@[simp]
theorem counts_eq_geometry_counts
    (S : FaceSubpolygonRealizationData D) :
    S.counts = S.geometry.counts :=
  rfl

@[simp]
theorem counts_eq_degreeCounts
    (S : FaceSubpolygonRealizationData D) :
    S.counts = S.geometry.toGeometryData.vertexSet.degreeCounts :=
  rfl

/-- Package the flattened fields as core face-subpolygon realization data. -/
def toCoreFaceSubpolygonAngleRealizationData
    (S : FaceSubpolygonRealizationData D) :
    CoreFaceSubpolygonAngleRealizationData D.core where
  geometry := S.geometry.toGeometryData
  angleRealization := S.angleRealization

@[simp]
theorem toCoreFaceSubpolygonAngleRealizationData_counts
    (S : FaceSubpolygonRealizationData D) :
    S.toCoreFaceSubpolygonAngleRealizationData.counts = S.counts :=
  rfl

/-- Forget the pointwise realization to the aggregate face-subpolygon angle
data expected by older planar-boundary inputs. -/
def toFaceSubpolygonAngleFields
    (S : FaceSubpolygonRealizationData D) :
    FaceSubpolygonAngleFields D where
  geometry := S.geometry
  geometricAngleSum := S.angleRealization.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, FaceSubpolygonFields.counts] using
      S.angleRealization.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [counts, FaceSubpolygonFields.counts] using
      S.angleRealization.geometric_le_polygon

@[simp]
theorem toFaceSubpolygonAngleFields_counts
    (S : FaceSubpolygonRealizationData D) :
    S.toFaceSubpolygonAngleFields.counts = S.counts :=
  rfl

/-- Forget to the core aggregate angle package. -/
def toCoreFaceSubpolygonAngleData
    (S : FaceSubpolygonRealizationData D) :
    CoreFaceSubpolygonAngleData D.core :=
  S.toCoreFaceSubpolygonAngleRealizationData.toCoreFaceSubpolygonAngleData

@[simp]
theorem toCoreFaceSubpolygonAngleData_counts
    (S : FaceSubpolygonRealizationData D) :
    S.toCoreFaceSubpolygonAngleData.counts = S.counts :=
  rfl

/-- The checked angle lower bound from the stored pointwise angle realization. -/
theorem angleLowerBound
    (S : FaceSubpolygonRealizationData D) :
    S.counts.AngleLowerBound := by
  simpa [counts] using S.angleRealization.angleLowerBound

/-- E13 with high-degree slack from the selected geometry and concrete angle
realization. -/
theorem lowDegreeWithHighDegreeSlack
    (S : FaceSubpolygonRealizationData D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using
    S.toCoreFaceSubpolygonAngleRealizationData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's E13 low-degree conclusion from the selected geometry and
concrete angle realization. -/
theorem lowDegree
    (S : FaceSubpolygonRealizationData D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using S.toCoreFaceSubpolygonAngleRealizationData.lowDegree

end FaceSubpolygonRealizationData

/-! ## Families and E13 low-degree input -/

/-- A family of selected face subpolygons with actual concrete angle
realizations for the induced counts of each member. -/
structure FaceSubpolygonRealizationFamilyData
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  Subpolygon : Type u
  subpolygonData : Subpolygon -> FaceSubpolygonRealizationData D

namespace FaceSubpolygonRealizationFamilyData

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The computed E13 counts for a family member. -/
def subpolygonCounts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.subpolygonData S).counts

/-- Package the family as core face-subpolygon realization data. -/
def toCoreFaceSubpolygonAngleRealizationFamilyData
    (F : FaceSubpolygonRealizationFamilyData D) :
    CoreFaceSubpolygonAngleRealizationFamilyData.{u} D.core where
  Subpolygon := F.Subpolygon
  subpolygonData :=
    fun S => (F.subpolygonData S).toCoreFaceSubpolygonAngleRealizationData

@[simp]
theorem toCoreFaceSubpolygonAngleRealizationFamilyData_Subpolygon
    (F : FaceSubpolygonRealizationFamilyData D) :
    F.toCoreFaceSubpolygonAngleRealizationFamilyData.Subpolygon =
      F.Subpolygon :=
  rfl

@[simp]
theorem toCoreFaceSubpolygonAngleRealizationFamilyData_counts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    (F.toCoreFaceSubpolygonAngleRealizationFamilyData.subpolygonData S).counts =
      F.subpolygonCounts S :=
  rfl

/-- Forget pointwise realizations to the aggregate flattened family. -/
def toFaceSubpolygonFamilyFields
    (F : FaceSubpolygonRealizationFamilyData D) :
    FaceSubpolygonFamilyFields D where
  Subpolygon := F.Subpolygon
  subpolygonFields :=
    fun S => (F.subpolygonData S).toFaceSubpolygonAngleFields

@[simp]
theorem toFaceSubpolygonFamilyFields_Subpolygon
    (F : FaceSubpolygonRealizationFamilyData D) :
    F.toFaceSubpolygonFamilyFields.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toFaceSubpolygonFamilyFields_counts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    (F.toFaceSubpolygonFamilyFields.subpolygonFields S).counts =
      F.subpolygonCounts S :=
  rfl

/-- The aggregate core face-subpolygon family induced by the realizations. -/
def toCoreFaceSubpolygonFamilyData
    (F : FaceSubpolygonRealizationFamilyData D) :
    CoreFaceSubpolygonFamilyData.{u} D.core :=
  F.toCoreFaceSubpolygonAngleRealizationFamilyData.toCoreFaceSubpolygonFamilyData

@[simp]
theorem toCoreFaceSubpolygonFamilyData_counts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    (F.toCoreFaceSubpolygonFamilyData.subpolygonData S).counts =
      F.subpolygonCounts S :=
  rfl

/-- A strict carrier over the flattened W33 realization family is impossible
by the E13 row supplied by the same pointwise angle realizations. -/
theorem carrier_false
    (F : FaceSubpolygonRealizationFamilyData D)
    (carrier :
      CoreSubpolygonCarrierCountData
        F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    False :=
  carrier.false

/-- If every bad row would yield a strict carrier over this flattened W33
realization family, then no bad row occurs. -/
theorem noBadRows_of_carrierRows
    (F : FaceSubpolygonRealizationFamilyData D)
    {Idx : Type v}
    {Bad : Idx -> Prop}
    (hcarrier :
      forall i : Idx,
        Bad i ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) :
    forall i : Idx, Not (Bad i) := by
  intro i hbad
  cases hcarrier i hbad with
  | intro carrier =>
      exact carrier_false F carrier

/-- Carrier rows over the flattened W33 realization family are equivalent to
pointwise no-bad rows. -/
theorem carrierRows_iff_noBadRows
    (F : FaceSubpolygonRealizationFamilyData D)
    {Idx : Type v}
    (Bad : Idx -> Prop) :
    (forall i : Idx,
        Bad i ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) <->
      forall i : Idx, Not (Bad i) := by
  constructor
  case mp =>
    intro hcarrier
    exact F.noBadRows_of_carrierRows hcarrier
  case mpr =>
    intro hno i hbad
    exact False.elim (hno i hbad)

/-- For flattened actual selected face-subpolygon realization families,
strict carriers for the raw boundary gap component pattern are equivalent to
pointwise absence of that concrete pattern. -/
theorem componentPatternCarrierRows_iff_noBadRows
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core) :
    (forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) <->
      forall k : Fin D.core.outerCycle.length,
        Not (BoundaryGapTriangleDegree34ComponentPattern classification k) :=
  F.carrierRows_iff_noBadRows
    (fun k : Fin D.core.outerCycle.length =>
      BoundaryGapTriangleDegree34ComponentPattern classification k)

/-- Pointwise E13 contradiction for a flattened selected face-subpolygon
realization family.  If a bad boundary component row constructs a concrete
strict carrier over this same W33 family, the component row is impossible. -/
theorem not_componentPattern_of_componentCarrier
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core)
    {k : Fin D.core.outerCycle.length}
    (hcarrier :
      BoundaryGapTriangleDegree34ComponentPattern classification k ->
        CoreSubpolygonCarrierCountData
          F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    Not (BoundaryGapTriangleDegree34ComponentPattern classification k) := by
  intro hpattern
  exact F.carrier_false (hcarrier hpattern)

/-- Exact carrier rows for the raw boundary component pattern give the actual
pointwise no-bad component rows over a flattened W33 realization family. -/
theorem noBadComponentPatterns_of_componentCarrierRowsExact
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core)
    (hcarrier :
      forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          CoreSubpolygonCarrierCountData
            F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    forall k : Fin D.core.outerCycle.length,
      Not (BoundaryGapTriangleDegree34ComponentPattern classification k) := by
  intro k
  exact F.not_componentPattern_of_componentCarrier classification (hcarrier k)

/-- Actual pointwise no-bad component-pattern rows from the flattened W33
realization carrier rows. -/
theorem noBadComponentPatterns_of_componentCarrierRows
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core)
    (hcarrier :
      forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) :
    forall k : Fin D.core.outerCycle.length,
      Not (BoundaryGapTriangleDegree34ComponentPattern classification k) :=
  (F.componentPatternCarrierRows_iff_noBadRows classification).1 hcarrier

/-- The actual pointwise no-bad component-pattern rows produced by flattened
W33 realization carriers feed the selected boundary no-gap row. -/
theorem no_boundaryGapTriangleDegree34Rows_of_componentCarrierRows
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core)
    (hcarrier :
      forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) :
    forall k : Fin D.core.outerCycle.length,
      Not
      (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) := by
  exact
    OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      classification
      (F.noBadComponentPatterns_of_componentCarrierRows
        classification hcarrier)

/-- Exact component-pattern carrier rows over the flattened W33 realization
family feed the selected boundary no-gap row. -/
theorem no_boundaryGapTriangleDegree34Rows_of_componentCarrierRowsExact
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core)
    (hcarrier :
      forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          CoreSubpolygonCarrierCountData
            F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData) :
    forall k : Fin D.core.outerCycle.length,
      Not
        (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) := by
  exact
    OuterBoundaryClassificationInputs.no_boundaryGapTriangleDegree34Rows_of_no_components
      classification
      (F.noBadComponentPatterns_of_componentCarrierRowsExact
        classification hcarrier)

/-- Carrier rows for the named boundary-gap row itself are equivalent to the
selected no-gap row over a flattened W33 realization family. -/
theorem boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
    (F : FaceSubpolygonRealizationFamilyData D)
    (classification : OuterBoundaryClassificationInputs D.core) :
    (forall k : Fin D.core.outerCycle.length,
        OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              F.toCoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData)) <->
      forall k : Fin D.core.outerCycle.length,
        Not
          (OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k) :=
  F.carrierRows_iff_noBadRows
    (fun k : Fin D.core.outerCycle.length =>
      OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        classification k)

/-- The planar-boundary subpolygon inputs induced by the realization family. -/
def toPlanarBoundarySubpolygonInputs
    (F : FaceSubpolygonRealizationFamilyData D) :
    SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G :=
  F.toCoreFaceSubpolygonAngleRealizationFamilyData.toPlanarBoundarySubpolygonInputs

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : FaceSubpolygonRealizationFamilyData D) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_counts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    F.toPlanarBoundarySubpolygonInputs.subpolygonDegreeCounts S =
      F.subpolygonCounts S :=
  rfl

/-- The full planar-boundary package induced by the realization family. -/
def toPlanarBoundaryData
    (F : FaceSubpolygonRealizationFamilyData D) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  F.toFaceSubpolygonFamilyFields.toPlanarBoundaryData

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (F : FaceSubpolygonRealizationFamilyData D) :
    F.toPlanarBoundaryData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_counts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    (F.toPlanarBoundaryData.subpolygonData S).counts =
      F.subpolygonCounts S :=
  rfl

/-- The E13 low-degree input family inhabited by concrete realization data. -/
def toCheckedLowDegreeFamily
    (F : FaceSubpolygonRealizationFamilyData D) :
    CheckedLowDegreeFamily.{u} :=
  checkedLowDegreeFamilyOfCoreFaceRealizationFamily
    F.toCoreFaceSubpolygonAngleRealizationFamilyData

@[simp]
theorem toCheckedLowDegreeFamily_counts
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    F.toCheckedLowDegreeFamily.counts S = F.subpolygonCounts S :=
  rfl

/-- E13 with high-degree slack for every realized selected subpolygon. -/
theorem lowDegreeWithHighDegreeSlack
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 :=
  F.toCheckedLowDegreeFamily.lowDegreeWithHighDegreeSlack S

/-- Swanepoel's E13 low-degree conclusion for every realized selected
subpolygon. -/
theorem lowDegree
    (F : FaceSubpolygonRealizationFamilyData D)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 +
      (F.subpolygonCounts S).D3 :=
  F.toCheckedLowDegreeFamily.lowDegree S

end FaceSubpolygonRealizationFamilyData

end

end SubpolygonConcreteRealizationW33
end Swanepoel
end ErdosProblems1066
