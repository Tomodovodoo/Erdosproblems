import ErdosProblems1066.PachToth.DeformedPlacementConstructionW33
import ErdosProblems1066.PachToth.LargeClosedPlacementInstantiationW13

set_option autoImplicit false

/-!
# W34 alternative non-rigid closed-placement source

The W33 direct flexible payload is not used here.  This file tests a genuinely
different source surface: W12/W13 large explicit closed-placement certificates.

Those certificates already contain coordinate-level closed placements.  They
therefore give the W33 metric-field surface in their threshold range, and they
give the full metric-field family exactly when the large threshold is at most
one block.  The final blocker records the honest obstruction for an eventual
source with a larger threshold: below-threshold blocks require an independent
small-block certificate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AlternativeNonRigidClosedPlacementW34

open FiniteGraph
open FiniteGraph.LocalVertex
open LargeClosedPlacementInstantiationW13

noncomputable section

abbrev R2 := Prod Real Real

abbrev ClosedPlacement (k : Nat) (hk : 0 < k) : Type :=
  DeformedPlacement.ClosedPlacement k hk

abbrev ClosedPlacementMetricFields (k : Nat) (hk : 0 < k) : Type :=
  DeformedPlacement.ClosedPlacementMetricFields k hk

abbrev ClosedPlacementMetricFieldFamily : Type :=
  DeformedPlacement.ClosedPlacementMetricFieldFamily

abbrev ExplicitClosedPlacementCertificate (k : Nat) (hk : 0 < k) : Type :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev LargeClosedPlacementFields (K0 : Nat) : Type :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields K0

abbrev EventualTarget : Prop :=
  LargeClosedPlacementInstantiationW13.EventualTarget

abbrev ExactTarget : Prop :=
  LargeClosedPlacementInstantiationW13.ExactTarget

abbrev ExactBlockTarget (k : Nat) : Prop :=
  LargeClosedPlacementInstantiationW13.ExactBlockTarget k

abbrev LargeExactBlockTargetsFromSix : Prop :=
  forall k : Nat, 6 <= k -> ExactBlockTarget k

/-- Extract the W33 named connector metric fields from an explicit closed
placement certificate. -/
def metricFieldsOfExplicitClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    ClosedPlacementMetricFields k hk where
  point := C.point
  separated := C.separated
  same_block_edges_unit := C.same_block_edges_unit
  cross_connector_named_units := {
    t2_2_t1_1 := fun i =>
      C.cross_connector_edges_unit i T2_2 T1_1
        ClosedPlacementCrossConnectorEdgesW19.nextConnector_T2_2_T1_1
    t2_2_t1_2 := fun i =>
      C.cross_connector_edges_unit i T2_2 T1_2
        ClosedPlacementCrossConnectorEdgesW19.nextConnector_T2_2_T1_2
    t4_0_t0_0 := fun i =>
      C.cross_connector_edges_unit i T4_0 T0_0
        ClosedPlacementCrossConnectorEdgesW19.nextConnector_T4_0_T0_0
    t4_0_t0_2 := fun i =>
      C.cross_connector_edges_unit i T4_0 T0_2
        ClosedPlacementCrossConnectorEdgesW19.nextConnector_T4_0_T0_2 }

@[simp]
theorem metricFieldsOfExplicitClosedPlacementCertificate_point
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk)
    (i : Fin k) (v : LocalVertex) :
    (metricFieldsOfExplicitClosedPlacementCertificate C).point i v =
      C.point i v := by
  rfl

/-- The extracted W33 fields recover the original closed placement. -/
def closedPlacementOfExplicitClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    ClosedPlacement k hk :=
  (metricFieldsOfExplicitClosedPlacementCertificate C).toClosedPlacement

@[simp]
theorem closedPlacementOfExplicitClosedPlacementCertificate_point
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfExplicitClosedPlacementCertificate C).point i v =
      C.point i v := by
  rfl

/-! ## W12/W13 large-certificate route -/

/-- W12 large certificates give actual W33 metric fields in the threshold
range. -/
def metricFieldsOfLargeClosedPlacementFields
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k) :
    ClosedPlacementMetricFields k hk :=
  metricFieldsOfExplicitClosedPlacementCertificate
    (L.certificate k hK hk)

@[simp]
theorem metricFieldsOfLargeClosedPlacementFields_point
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (metricFieldsOfLargeClosedPlacementFields L hK hk).point i v =
      (L.certificate k hK hk).point i v := by
  rfl

/-- W12 large certificates give actual deformed closed placements in the
threshold range. -/
def closedPlacementOfLargeClosedPlacementFields
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k) :
    ClosedPlacement k hk :=
  (metricFieldsOfLargeClosedPlacementFields L hK hk).toClosedPlacement

@[simp]
theorem closedPlacementOfLargeClosedPlacementFields_point
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfLargeClosedPlacementFields L hK hk).point i v =
      (L.certificate k hK hk).point i v := by
  rfl

/-- Thresholded family form: this is the natural output of W12 large
certificates when `K0` may be greater than one. -/
structure EventualClosedPlacementMetricFieldFamily (K0 : Nat) where
  fields :
    forall (k : Nat), K0 <= k -> forall hk : 0 < k,
      ClosedPlacementMetricFields k hk

namespace EventualClosedPlacementMetricFieldFamily

def closedPlacement
    {K0 : Nat} (E : EventualClosedPlacementMetricFieldFamily K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    ClosedPlacement k hk :=
  (E.fields k hK hk).toClosedPlacement

end EventualClosedPlacementMetricFieldFamily

/-- W12 large certificates give the thresholded W34 metric-field family. -/
def eventualMetricFieldFamilyOfLargeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    EventualClosedPlacementMetricFieldFamily K0 where
  fields := fun _k hK hk => metricFieldsOfLargeClosedPlacementFields L hK hk

/-- The exact finite complement needed to promote a thresholded large source
to the all-positive W33 metric-field family. -/
structure BelowThresholdClosedPlacementMetricFields (K0 : Nat) where
  fields :
    forall (k : Nat), k < K0 -> forall hk : 0 < k,
      ClosedPlacementMetricFields k hk

namespace BelowThresholdClosedPlacementMetricFields

def closedPlacement
    {K0 k : Nat} (B : BelowThresholdClosedPlacementMetricFields K0)
    (hkBelow : k < K0) (hk : 0 < k) :
    ClosedPlacement k hk :=
  (B.fields k hkBelow hk).toClosedPlacement

end BelowThresholdClosedPlacementMetricFields

/-- A thresholded metric-field family plus exactly the missing below-threshold
metric fields gives the full all-positive family. -/
def metricFieldFamilyOfEventualAndBelow
    {K0 : Nat}
    (E : EventualClosedPlacementMetricFieldFamily K0)
    (B : BelowThresholdClosedPlacementMetricFields K0) :
    ClosedPlacementMetricFieldFamily :=
  fun k hk =>
    if hK : K0 <= k then
      E.fields k hK hk
    else
      B.fields k (by omega) hk

theorem nonempty_metricFieldFamily_of_eventualAndBelow
    {K0 : Nat}
    (E : EventualClosedPlacementMetricFieldFamily K0)
    (B : BelowThresholdClosedPlacementMetricFields K0) :
    Nonempty ClosedPlacementMetricFieldFamily :=
  Nonempty.intro (metricFieldFamilyOfEventualAndBelow E B)

theorem exactTarget_of_eventualMetricFieldFamily_and_below
    {K0 : Nat}
    (E : EventualClosedPlacementMetricFieldFamily K0)
    (B : BelowThresholdClosedPlacementMetricFields K0) :
    ExactTarget := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (fun k hk =>
        (metricFieldFamilyOfEventualAndBelow E B k hk).toClosedPlacement)

def metricFieldFamilyOfLargeClosedPlacementFieldsAndBelow
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (B : BelowThresholdClosedPlacementMetricFields K0) :
    ClosedPlacementMetricFieldFamily :=
  metricFieldFamilyOfEventualAndBelow
    (eventualMetricFieldFamilyOfLargeClosedPlacementFields L) B

theorem nonempty_metricFieldFamily_of_largeClosedPlacementFields_and_below
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (B : BelowThresholdClosedPlacementMetricFields K0) :
    Nonempty ClosedPlacementMetricFieldFamily :=
  Nonempty.intro
    (metricFieldFamilyOfLargeClosedPlacementFieldsAndBelow L B)

theorem exactTarget_of_largeClosedPlacementFields_and_below
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (B : BelowThresholdClosedPlacementMetricFields K0) :
    ExactTarget :=
  exactTarget_of_eventualMetricFieldFamily_and_below
    (eventualMetricFieldFamilyOfLargeClosedPlacementFields L) B

/-- If the W12/W13 threshold is at most one block, the large source promotes
to the full W33 metric-field family for every positive block count. -/
def metricFieldFamilyOfLargeClosedPlacementFieldsAtMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ClosedPlacementMetricFieldFamily :=
  fun k hk =>
    metricFieldsOfLargeClosedPlacementFields L
      (by omega) hk

/-- The corresponding full deformed closed-placement family when the
threshold is at most one block. -/
def closedPlacementFamilyOfLargeClosedPlacementFieldsAtMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacement k hk :=
  (metricFieldFamilyOfLargeClosedPlacementFieldsAtMostOne L hK0 k hk)
    |>.toClosedPlacement

/-- The exact target follows from the promoted metric-field family without
touching the refuted W33 direct flexible payload. -/
theorem exactTarget_of_largeClosedPlacementFieldsAtMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ExactTarget := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      (closedPlacementFamilyOfLargeClosedPlacementFieldsAtMostOne L hK0)

/-- Threshold-six W12/W13 large certificates give the exact block target tail
from six onward.  This is the large-tail adapter used by the source-side
route; it does not pass through the W33 exact-base flexible payload. -/
theorem largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix
    (L : LargeClosedPlacementFields 6) :
    LargeExactBlockTargetsFromSix := by
  intro k hkSix
  have hk : 0 < k := by omega
  exact
    LargeClosedPlacementInstantiationW13.exactBlockTarget_of_largeClosedPlacementFields
      L hkSix hk

/-- W12/W13 large certificates always give the eventual target, with the
threshold supplied by W13. -/
theorem eventualTarget_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    EventualTarget :=
  targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields L

/-! ## Below-threshold obstruction for the eventual-only route -/

/-- A below-threshold obstruction says that the large certificate source has
no independent small-block certificate for a positive block count below its
threshold. -/
structure BelowThresholdClosedPlacementObstruction
    (K0 k : Nat) (hkBelow : k < K0) (hk : 0 < k) where
  no_certificate : Not (Nonempty (ExplicitClosedPlacementCertificate k hk))

namespace BelowThresholdClosedPlacementObstruction

/-- Any W33 metric fields would give a coordinate-level explicit closed
placement certificate for the obstructed block count. -/
def explicitCertificateOfMetricFields
    {K0 k : Nat} {hkBelow : k < K0} {hk : 0 < k}
    (_B : BelowThresholdClosedPlacementObstruction K0 k hkBelow hk)
    (F : ClosedPlacementMetricFields k hk) :
    ExplicitClosedPlacementCertificate k hk where
  point := F.point
  separated := F.separated
  same_block_edges_unit := F.same_block_edges_unit
  cross_connector_edges_unit :=
    F.cross_connector_named_units.crossConnectorEdgesUnit

/-- Thus a below-threshold obstruction blocks W33 metric fields at that
specific block count. -/
theorem no_metricFields
    {K0 k : Nat} {hkBelow : k < K0} {hk : 0 < k}
    (B : BelowThresholdClosedPlacementObstruction K0 k hkBelow hk) :
    Not (Nonempty (ClosedPlacementMetricFields k hk)) := by
  intro h
  rcases h with ⟨F⟩
  exact B.no_certificate ⟨B.explicitCertificateOfMetricFields F⟩

/-- In particular, the eventual W12 route does not produce a full
metric-field family across an obstructed below-threshold block. -/
theorem no_metricFieldFamily
    {K0 k : Nat} {hkBelow : k < K0} {hk : 0 < k}
    (B : BelowThresholdClosedPlacementObstruction K0 k hkBelow hk) :
    Not (Nonempty ClosedPlacementMetricFieldFamily) := by
  intro h
  rcases h with ⟨F⟩
  exact B.no_metricFields ⟨F k hk⟩

/-- The same obstruction blocks an all-positive deformed closed-placement
family, because every such placement gives an explicit certificate. -/
theorem no_closedPlacementFamily
    {K0 k : Nat} {hkBelow : k < K0} {hk : 0 < k}
    (B : BelowThresholdClosedPlacementObstruction K0 k hkBelow hk) :
    Not (Nonempty (forall (m : Nat) (hm : 0 < m), ClosedPlacement m hm)) := by
  intro h
  rcases h with ⟨P⟩
  exact B.no_certificate
    ⟨{
      point := (P k hk).point
      separated := (P k hk).separated
      same_block_edges_unit := (P k hk).same_block_edges_unit
      cross_connector_edges_unit := (P k hk).cross_connector_edges_unit }⟩

end BelowThresholdClosedPlacementObstruction

end

end AlternativeNonRigidClosedPlacementW34
end PachToth

namespace Verified

open PachToth.AlternativeNonRigidClosedPlacementW34

abbrev PachTothW34W12LargeClosedPlacementFields (K0 : Nat) : Type :=
  PachToth.AlternativeNonRigidClosedPlacementW34.LargeClosedPlacementFields K0

abbrev PachTothW34W12ClosedPlacementMetricFieldFamily : Type :=
  PachToth.AlternativeNonRigidClosedPlacementW34.ClosedPlacementMetricFieldFamily

abbrev PachTothW34W12EventualClosedPlacementMetricFieldFamily (K0 : Nat) : Type :=
  PachToth.AlternativeNonRigidClosedPlacementW34.EventualClosedPlacementMetricFieldFamily K0

abbrev PachTothW34W12BelowThresholdClosedPlacementMetricFields (K0 : Nat) : Type :=
  PachToth.AlternativeNonRigidClosedPlacementW34.BelowThresholdClosedPlacementMetricFields K0

theorem pachtoth_w34_w12_eventualMetricFieldFamily_of_largeClosedPlacementFields
    {K0 : Nat} (L : PachTothW34W12LargeClosedPlacementFields K0) :
    Nonempty (PachTothW34W12EventualClosedPlacementMetricFieldFamily K0) :=
  Nonempty.intro
    (eventualMetricFieldFamilyOfLargeClosedPlacementFields L)

theorem pachtoth_w34_w12_metricFieldFamily_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : PachTothW34W12LargeClosedPlacementFields K0)
    (hK0 : K0 <= 1) :
    Nonempty PachTothW34W12ClosedPlacementMetricFieldFamily :=
  Nonempty.intro
    (metricFieldFamilyOfLargeClosedPlacementFieldsAtMostOne L hK0)

theorem pachtoth_w34_w12_metricFieldFamily_of_largeClosedPlacementFields_and_below
    {K0 : Nat} (L : PachTothW34W12LargeClosedPlacementFields K0)
    (B : PachTothW34W12BelowThresholdClosedPlacementMetricFields K0) :
    Nonempty PachTothW34W12ClosedPlacementMetricFieldFamily :=
  nonempty_metricFieldFamily_of_largeClosedPlacementFields_and_below L B

end Verified
end ErdosProblems1066
