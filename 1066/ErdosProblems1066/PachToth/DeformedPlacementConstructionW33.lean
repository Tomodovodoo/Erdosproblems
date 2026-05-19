import ErdosProblems1066.PachToth.ClosedPlacementCrossConnectorEdgesW19
import ErdosProblems1066.PachToth.DeformedPlacement

set_option autoImplicit false

/-!
# W33 deformed closed-placement construction endpoint

This leaf keeps the final deformed-placement obligation at the geometric
surface.  For a fixed positive block count, the exact missing fields are a
point map, global separation, same-block unit edges, and the four W19 named
successor connector unit equations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DeformedPlacement

open Arithmetic
open FiniteGraph

noncomputable section

/-- The precise per-length geometric fields still needed to build
`DeformedPlacement.ClosedPlacement k hk`.

The cross-block data is deliberately stored as W19's four named successor
connector equations; `toClosedPlacement` below is the checked conversion to
the quantified connector field. -/
structure ClosedPlacementMetricFields (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  cross_connector_named_units :
    ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
      hk point

namespace ClosedPlacementMetricFields

/-- Convert the exact metric fields into the checked deformed closed
placement. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (F : ClosedPlacementMetricFields k hk) :
    ClosedPlacement k hk :=
  ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate.toClosedPlacement
    F.cross_connector_named_units
    F.separated
    F.same_block_edges_unit

@[simp]
theorem toClosedPlacement_point
    {k : Nat} {hk : 0 < k}
    (F : ClosedPlacementMetricFields k hk)
    (i : Fin k) (v : LocalVertex) :
    F.toClosedPlacement.point i v = F.point i v := by
  rfl

end ClosedPlacementMetricFields

/-- Family form of the exact metric fields for all positive block counts. -/
abbrev ClosedPlacementMetricFieldFamily : Type :=
  forall (k : Nat) (hk : 0 < k), ClosedPlacementMetricFields k hk

/-- A field family gives the desired closed placement for every positive
block count. -/
def closedPlacement_of_metricFieldFamily
    (F : ClosedPlacementMetricFieldFamily)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacement k hk :=
  (F k hk).toClosedPlacement

/-- Forget the metric-field family to checked closed placements for every
positive block count. -/
def closedPlacementFamily_of_metricFieldFamily
    (F : ClosedPlacementMetricFieldFamily) :
    forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk :=
  fun k hk => closedPlacement_of_metricFieldFamily F k hk

theorem targetUpperConstructionFiveSixteen_of_metricFieldFamily
    (F : ClosedPlacementMetricFieldFamily) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_deformedPlacements
    (closedPlacementFamily_of_metricFieldFamily F)

theorem nonempty_closedPlacementFamily_of_metricFieldFamilyGate
    (H : Nonempty ClosedPlacementMetricFieldFamily) :
    Nonempty (forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk) := by
  cases H with
  | intro F =>
      exact Nonempty.intro (closedPlacementFamily_of_metricFieldFamily F)

theorem targetUpperConstructionFiveSixteen_of_metricFieldFamilyGate
    (H : Nonempty ClosedPlacementMetricFieldFamily) :
    targetUpperConstructionFiveSixteen := by
  cases H with
  | intro F =>
      exact targetUpperConstructionFiveSixteen_of_metricFieldFamily F

end

end DeformedPlacement
end PachToth
end ErdosProblems1066
