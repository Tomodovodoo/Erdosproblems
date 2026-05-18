import ErdosProblems1066.Swanepoel.PlanarBoundaryClosure
import ErdosProblems1066.Swanepoel.BoundaryCounting
import ErdosProblems1066.Swanepoel.BoundaryWalkConstruction
import ErdosProblems1066.Swanepoel.PlanarInterface

set_option autoImplicit false

/-!
# Final planar-boundary counting facade

This module exposes the checked planar-boundary closure in the concrete forms
used downstream: angle-lower-bound hypotheses, canonical face-counting bridge
packages, and the resulting E12/E13 count inequalities.

It remains conditional.  The face/Jordan-style content is still supplied
through `OuterBoundaryCore` (the output boundary used by the concrete Jordan
adapters), while outer-boundary angle bookkeeping and honest subpolygon
families are supplied by `OuterBoundaryAngleClosure` and `SubpolygonAssembly`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarBoundaryFinal

open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/-! ## Direct outer-core angle and face-counting conclusions -/

/-- Direct angle-lower-bound hypothesis obtained from a supplied geometric
outer-boundary angle sum.  The core parameter records which face-boundary
package this angle data is attached to. -/
def outerBoundaryAngleLowerBoundOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (_core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.AngleLowerBound :=
  le_trans hforced hpolygon

/-- Canonical face-counting hypotheses produced directly from an
`OuterBoundaryCore` and explicit outer-boundary angle comparisons. -/
def canonicalBoundaryCountHypothesesOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  core.toCanonicalBoundaryCountHypotheses counts
    (outerBoundaryAngleLowerBoundOfCore core counts geometricAngleSum hforced hpolygon)

/-- The planar face-boundary interface carried by an `OuterBoundaryCore`. -/
def planarFaceBoundaryOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  core.toFaceBoundaryHypotheses

/-- The canonical noncrossing fact attached to an `OuterBoundaryCore`. -/
theorem pairwiseNoncrossingOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  core.pairwiseNoncrossing

/-- E12 in concrete count form, from an `OuterBoundaryCore` and explicit
outer-boundary angle comparisons. -/
theorem boundaryAngleCountInequalityOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality counts
    (outerBoundaryAngleLowerBoundOfCore core counts geometricAngleSum hforced hpolygon)

/-- Negative-element E12 in concrete count form, from an `OuterBoundaryCore`
and explicit outer-boundary angle comparisons. -/
theorem boundaryNegativeCountInequalityOfCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (core : OuterBoundaryCore G)
    (counts : BoundaryCounts) (geometricAngleSum : Real)
    (hforced : counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (hpolygon : geometricAngleSum <= counts.polygonAngleSum) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality counts
    (outerBoundaryAngleLowerBoundOfCore core counts geometricAngleSum hforced hpolygon)

/-! ## Planar-boundary data projections -/

namespace PlanarBoundaryData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ### Construction wrappers from assembled boundary outputs -/

/--
Build planar-boundary data from an explicit outer-boundary core, the assembled
outer-boundary angle bounds, and supplied subpolygon cycle/count/angle data.

The remaining topology is exactly the `core` parameter.  This wrapper does not
assert that a Jordan boundary exists; it only packages an already supplied core
with already assembled finite/count/angle data.
-/
def ofCoreOuterAngleBoundsSubpolygonData
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G where
  core := core
  outerAngleBounds := outerAngleBounds
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonData_core
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofCoreOuterAngleBoundsSubpolygonData core outerAngleBounds
      Subpolygon subpolygonData).core = core :=
  rfl

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonData_outerBoundaryCounts
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofCoreOuterAngleBoundsSubpolygonData core outerAngleBounds
      Subpolygon subpolygonData).outerBoundaryCounts =
        outerAngleBounds.counts :=
  rfl

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonData_Subpolygon
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofCoreOuterAngleBoundsSubpolygonData core outerAngleBounds
      Subpolygon subpolygonData).Subpolygon = Subpolygon :=
  rfl

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonData_subpolygonData
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (S : Subpolygon) :
    (ofCoreOuterAngleBoundsSubpolygonData core outerAngleBounds
      Subpolygon subpolygonData).subpolygonData S = subpolygonData S :=
  rfl

/--
Build planar-boundary data from the full outer-boundary angle closure package
and supplied subpolygon cycle/count/angle data.
-/
def ofOuterBoundaryAngleDataSubpolygonData
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofCoreOuterAngleBoundsSubpolygonData
    outerData.core outerData.angleBounds Subpolygon subpolygonData

@[simp]
theorem ofOuterBoundaryAngleDataSubpolygonData_core
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryAngleDataSubpolygonData outerData
      Subpolygon subpolygonData).core = outerData.core :=
  rfl

@[simp]
theorem ofOuterBoundaryAngleDataSubpolygonData_outerBoundaryCounts
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryAngleDataSubpolygonData outerData
      Subpolygon subpolygonData).outerBoundaryCounts = outerData.counts :=
  rfl

/--
Build planar-boundary data from explicit outer-boundary angle-realization
data.  The per-class realization is honestly forgotten to the angle-bound
package consumed by `PlanarBoundaryData`.
-/
def ofOuterBoundaryRealizedAngleDataSubpolygonData
    (outerData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofCoreOuterAngleBoundsSubpolygonData
    outerData.core outerData.angleRealization.toAngleBounds
    Subpolygon subpolygonData

@[simp]
theorem ofOuterBoundaryRealizedAngleDataSubpolygonData_core
    (outerData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryRealizedAngleDataSubpolygonData outerData
      Subpolygon subpolygonData).core = outerData.core :=
  rfl

@[simp]
theorem ofOuterBoundaryRealizedAngleDataSubpolygonData_outerBoundaryCounts
    (outerData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryRealizedAngleDataSubpolygonData outerData
      Subpolygon subpolygonData).outerBoundaryCounts = outerData.counts :=
  rfl

/--
Build planar-boundary data from the strongest subpolygon-family input exposed
by `SubpolygonAssembly`.

The equality hypothesis records that the subpolygon family is tied to the same
face-boundary witness as the outer core.  It is not used to manufacture data;
it is kept visible so callers cannot silently mix unrelated face-boundary
packages.
-/
def ofCoreOuterAngleBoundsSubpolygonInputs
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (_sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofCoreOuterAngleBoundsSubpolygonData
    core outerAngleBounds inputs.Subpolygon inputs.subpolygonData

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonInputs_core
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (ofCoreOuterAngleBoundsSubpolygonInputs core outerAngleBounds
      inputs sameFaceBoundary).core = core :=
  rfl

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonInputs_Subpolygon
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (ofCoreOuterAngleBoundsSubpolygonInputs core outerAngleBounds
      inputs sameFaceBoundary).Subpolygon = inputs.Subpolygon :=
  rfl

@[simp]
theorem ofCoreOuterAngleBoundsSubpolygonInputs_subpolygonData
    (core : OuterBoundaryCore G)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary)
    (S : inputs.Subpolygon) :
    (ofCoreOuterAngleBoundsSubpolygonInputs core outerAngleBounds
      inputs sameFaceBoundary).subpolygonData S = inputs.subpolygonData S :=
  rfl

/--
Build planar-boundary data from an outer-boundary angle closure package and
the strongest assembled subpolygon-family input.
-/
def ofOuterBoundaryAngleDataSubpolygonInputs
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = outerData.core.faceBoundary) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofCoreOuterAngleBoundsSubpolygonInputs
    outerData.core outerData.angleBounds inputs sameFaceBoundary

@[simp]
theorem ofOuterBoundaryAngleDataSubpolygonInputs_core
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = outerData.core.faceBoundary) :
    (ofOuterBoundaryAngleDataSubpolygonInputs outerData
      inputs sameFaceBoundary).core = outerData.core :=
  rfl

@[simp]
theorem ofOuterBoundaryAngleDataSubpolygonInputs_outerBoundaryCounts
    (outerData : OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = outerData.core.faceBoundary) :
    (ofOuterBoundaryAngleDataSubpolygonInputs outerData
      inputs sameFaceBoundary).outerBoundaryCounts = outerData.counts :=
  rfl

/--
Build planar-boundary data from explicit outer-boundary angle-realization data
and the strongest assembled subpolygon-family input.
-/
def ofOuterBoundaryRealizedAngleDataSubpolygonInputs
    (outerData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = outerData.core.faceBoundary) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofCoreOuterAngleBoundsSubpolygonInputs
    outerData.core outerData.angleRealization.toAngleBounds
    inputs sameFaceBoundary

@[simp]
theorem ofOuterBoundaryRealizedAngleDataSubpolygonInputs_core
    (outerData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = outerData.core.faceBoundary) :
    (ofOuterBoundaryRealizedAngleDataSubpolygonInputs outerData
      inputs sameFaceBoundary).core = outerData.core :=
  rfl

@[simp]
theorem ofOuterBoundaryRealizedAngleDataSubpolygonInputs_outerBoundaryCounts
    (outerData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = outerData.core.faceBoundary) :
    (ofOuterBoundaryRealizedAngleDataSubpolygonInputs outerData
      inputs sameFaceBoundary).outerBoundaryCounts = outerData.counts :=
  rfl

/--
Assemble the outer-boundary angle package directly from the finite
boundary-walk bookkeeping and the still-explicit geometric angle comparisons.

The Jordan/topology input is still the `core` parameter.  In the concrete
`UDConfig` route, `JordanBoundaryConcrete.MissingTopologyFacts.toCore` supplies
that core without making this final facade depend back on the Jordan modules.
-/
def outerBoundaryAngleDataOfWalk
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum) :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G where
  core := core
  angleBounds :=
    walk.toBoundaryBookkeepingAngleBounds geometricAngleSum
      forced_le_geometric geometric_le_polygon

@[simp]
theorem outerBoundaryAngleDataOfWalk_core
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum) :
    (outerBoundaryAngleDataOfWalk walk geometricAngleSum
      forced_le_geometric geometric_le_polygon).core = core :=
  rfl

@[simp]
theorem outerBoundaryAngleDataOfWalk_counts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum) :
    (outerBoundaryAngleDataOfWalk walk geometricAngleSum
      forced_le_geometric geometric_le_polygon).counts = walk.counts :=
  rfl

@[simp]
theorem outerBoundaryAngleDataOfWalk_bookkeeping
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum) :
    (outerBoundaryAngleDataOfWalk walk geometricAngleSum
      forced_le_geometric geometric_le_polygon).angleBounds.countsRealization.bookkeeping =
        walk.toBoundaryBookkeepingLift :=
  rfl

/--
Build planar-boundary data from explicit topology/core data, constructed
boundary-walk bookkeeping, explicit angle comparisons, and raw subpolygon
cycle/count/angle data.
-/
def ofOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofOuterBoundaryAngleDataSubpolygonData
    (outerBoundaryAngleDataOfWalk walk geometricAngleSum
      forced_le_geometric geometric_le_polygon)
    Subpolygon subpolygonData

@[simp]
theorem ofOuterBoundaryWalkSubpolygonData_core
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryWalkSubpolygonData walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).core = core :=
  rfl

@[simp]
theorem ofOuterBoundaryWalkSubpolygonData_outerBoundaryCounts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryWalkSubpolygonData walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).outerBoundaryCounts = walk.counts :=
  rfl

@[simp]
theorem ofOuterBoundaryWalkSubpolygonData_Subpolygon
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (ofOuterBoundaryWalkSubpolygonData walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).Subpolygon = Subpolygon :=
  rfl

@[simp]
theorem ofOuterBoundaryWalkSubpolygonData_subpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (S : Subpolygon) :
    (ofOuterBoundaryWalkSubpolygonData walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).subpolygonData S = subpolygonData S :=
  rfl

/--
Build planar-boundary data from explicit topology/core data, constructed
boundary-walk bookkeeping, explicit angle comparisons, and the strongest
honest subpolygon family supplied by `SubpolygonAssembly`.

The equality hypothesis keeps the boundary witness shared between the
subpolygon family and the selected outer core explicit.
-/
def ofOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  ofOuterBoundaryAngleDataSubpolygonInputs
    (outerBoundaryAngleDataOfWalk walk geometricAngleSum
      forced_le_geometric geometric_le_polygon)
    inputs sameFaceBoundary

@[simp]
theorem ofOuterBoundaryWalkSubpolygonInputs_core
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (ofOuterBoundaryWalkSubpolygonInputs walk geometricAngleSum
      forced_le_geometric geometric_le_polygon inputs sameFaceBoundary).core =
        core :=
  rfl

@[simp]
theorem ofOuterBoundaryWalkSubpolygonInputs_outerBoundaryCounts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (ofOuterBoundaryWalkSubpolygonInputs walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).outerBoundaryCounts = walk.counts :=
  rfl

@[simp]
theorem ofOuterBoundaryWalkSubpolygonInputs_Subpolygon
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (ofOuterBoundaryWalkSubpolygonInputs walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).Subpolygon = inputs.Subpolygon :=
  rfl

@[simp]
theorem ofOuterBoundaryWalkSubpolygonInputs_subpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary)
    (S : inputs.Subpolygon) :
    (ofOuterBoundaryWalkSubpolygonInputs walk geometricAngleSum
      forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).subpolygonData S = inputs.subpolygonData S :=
  rfl

/-- The outer-boundary counting-layer angle lower bound carried by
`PlanarBoundaryData`. -/
theorem outerBoundaryAngleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.AngleLowerBound := by
  simpa [PlanarBoundaryClosure.PlanarBoundaryData.outerBoundaryCounts] using
    D.outerAngleBounds.angleLowerBound

/-- The subpolygon counting-layer angle lower bound carried by
`PlanarBoundaryData`. -/
theorem subpolygonAngleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.AngleLowerBound :=
  (D.subpolygonData S).angleLowerBound

/-- The canonical noncrossing fact exposed in the old planar interface. -/
theorem pairwiseNoncrossing
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  D.core.pairwiseNoncrossing

/-- The canonical boundary-count package agrees with the concrete
outer-boundary angle lower bound. -/
theorem canonicalBoundaryCountHypotheses_angleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.canonicalBoundaryCountHypotheses.angleLowerBound =
      outerBoundaryAngleLowerBound D :=
  rfl

/-- The canonical subpolygon-count package agrees with the concrete
subpolygon angle lower bound. -/
theorem canonicalSubpolygonCountHypotheses_angleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).angleLowerBound =
      subpolygonAngleLowerBound D S :=
  rfl

/-- Outer-boundary E12 routed directly through `BoundaryCounting` from the
concrete angle-lower-bound conclusion. -/
theorem boundaryAngleCountInequality_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d5 + 2 * D.outerBoundaryCounts.d6 +
        D.outerBoundaryCounts.b + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    D.outerBoundaryCounts (outerBoundaryAngleLowerBound D)

/-- Negative-element E12 routed directly through `BoundaryCounting` from the
concrete angle-lower-bound conclusion. -/
theorem boundaryNegativeCountInequality_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.negativeCount + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    D.outerBoundaryCounts (outerBoundaryAngleLowerBound D)

/-- E13 with high-degree slack routed directly through `BoundaryCounting` for
one supplied subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.D5 +
        2 * (D.subpolygonData S).counts.D6 + 6 <=
      2 * (D.subpolygonData S).counts.D2 +
        (D.subpolygonData S).counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    (D.subpolygonData S).counts (subpolygonAngleLowerBound D S)

/-- Swanepoel Lemma 4's low-degree conclusion routed directly through
`BoundaryCounting` for one supplied subpolygon. -/
theorem subpolygonLowDegreeInequality_viaBoundaryCounting
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    6 <= 2 * (D.subpolygonData S).counts.D2 +
      (D.subpolygonData S).counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    (D.subpolygonData S).counts (subpolygonAngleLowerBound D S)

/--
Concrete face-counting data extracted from `PlanarBoundaryData`.

The fields intentionally include both the old planar face-boundary interface
and the canonical face-counting bridge records, plus the angle-lower-bound
proofs that drive the checked count inequalities.
-/
structure ConcreteFaceCountingData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  faceBoundary : FaceReduction.UnitDistanceFaceBoundaryHypotheses G
  planarFaceBoundary :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  boundaryCounts : BoundaryCounts
  boundaryAngleLowerBound : boundaryCounts.AngleLowerBound
  boundaryCountHypotheses :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G
  boundary_faceBoundary_eq :
    boundaryCountHypotheses.faceBoundary = faceBoundary
  boundary_counts_eq :
    boundaryCountHypotheses.counts = boundaryCounts
  boundaryAngleCount :
    boundaryCounts.d5 + 2 * boundaryCounts.d6 +
        boundaryCounts.b + boundaryCounts.B + 6 <=
      boundaryCounts.d3
  boundaryNegativeCount :
    boundaryCounts.negativeCount + boundaryCounts.B + 6 <=
      boundaryCounts.d3
  Subpolygon : Type u
  subpolygonCounts : Subpolygon -> SubpolygonDegreeCounts
  subpolygonAngleLowerBound :
    forall S : Subpolygon, (subpolygonCounts S).AngleLowerBound
  subpolygonCountHypotheses :
    Subpolygon -> FaceCountingBridge.CanonicalSubpolygonCountHypotheses G
  subpolygon_faceBoundary_eq :
    forall S : Subpolygon, (subpolygonCountHypotheses S).faceBoundary = faceBoundary
  subpolygon_counts_eq :
    forall S : Subpolygon, (subpolygonCountHypotheses S).counts =
      subpolygonCounts S
  subpolygonLowDegreeWithHighDegreeSlack :
    forall S : Subpolygon,
      (subpolygonCounts S).D5 + 2 * (subpolygonCounts S).D6 + 6 <=
        2 * (subpolygonCounts S).D2 + (subpolygonCounts S).D3
  subpolygonLowDegree :
    forall S : Subpolygon,
      6 <= 2 * (subpolygonCounts S).D2 + (subpolygonCounts S).D3

/-- Extract the concrete face-counting and angle-lower-bound data used
downstream from a full `PlanarBoundaryData` package. -/
def concreteFaceCountingData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    ConcreteFaceCountingData D where
  faceBoundary := D.faceBoundary
  planarFaceBoundary := D.planarFaceBoundary
  pairwiseNoncrossing := pairwiseNoncrossing D
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  boundaryCounts := D.outerBoundaryCounts
  boundaryAngleLowerBound := outerBoundaryAngleLowerBound D
  boundaryCountHypotheses := D.canonicalBoundaryCountHypotheses
  boundary_faceBoundary_eq := D.canonicalBoundaryCountHypotheses_faceBoundary
  boundary_counts_eq := D.canonicalBoundaryCountHypotheses_counts
  boundaryAngleCount := boundaryAngleCountInequality_viaBoundaryCounting D
  boundaryNegativeCount := boundaryNegativeCountInequality_viaBoundaryCounting D
  Subpolygon := D.Subpolygon
  subpolygonCounts := fun S => (D.subpolygonData S).counts
  subpolygonAngleLowerBound := subpolygonAngleLowerBound D
  subpolygonCountHypotheses := D.canonicalSubpolygonCountHypotheses
  subpolygon_faceBoundary_eq :=
    D.canonicalSubpolygonCountHypotheses_faceBoundary
  subpolygon_counts_eq := fun _S => rfl
  subpolygonLowDegreeWithHighDegreeSlack :=
    subpolygonLowDegreeWithHighDegreeSlack_viaBoundaryCounting D
  subpolygonLowDegree := subpolygonLowDegreeInequality_viaBoundaryCounting D

@[simp]
theorem concreteFaceCountingData_faceBoundary
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_planarFaceBoundary
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).planarFaceBoundary =
      D.planarFaceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_pairwiseNoncrossing
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).pairwiseNoncrossing =
      pairwiseNoncrossing D :=
  rfl

@[simp]
theorem concreteFaceCountingData_outerFace
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).outerFace = D.outerFace :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCounts
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundaryCounts =
      D.outerBoundaryCounts :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryAngleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundaryAngleLowerBound =
      outerBoundaryAngleLowerBound D :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCountHypotheses
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundaryCountHypotheses =
      D.canonicalBoundaryCountHypotheses :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundary_faceBoundary_eq
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundary_faceBoundary_eq =
      D.canonicalBoundaryCountHypotheses_faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundary_counts_eq
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundary_counts_eq =
      D.canonicalBoundaryCountHypotheses_counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryAngleCount
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundaryAngleCount =
      boundaryAngleCountInequality_viaBoundaryCounting D :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryNegativeCount
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).boundaryNegativeCount =
      boundaryNegativeCountInequality_viaBoundaryCounting D :=
  rfl

@[simp]
theorem concreteFaceCountingData_Subpolygon
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (concreteFaceCountingData D).Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygonCounts S =
      (D.subpolygonData S).counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonAngleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygonAngleLowerBound S =
      subpolygonAngleLowerBound D S :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCountHypotheses
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygonCountHypotheses S =
      D.canonicalSubpolygonCountHypotheses S :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygon_faceBoundary_eq
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygon_faceBoundary_eq S =
      D.canonicalSubpolygonCountHypotheses_faceBoundary S :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygon_counts_eq
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygon_counts_eq S = rfl :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonLowDegreeWithHighDegreeSlack
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygonLowDegreeWithHighDegreeSlack S =
      subpolygonLowDegreeWithHighDegreeSlack_viaBoundaryCounting D S :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonLowDegree
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (S : D.Subpolygon) :
    (concreteFaceCountingData D).subpolygonLowDegree S =
      subpolygonLowDegreeInequality_viaBoundaryCounting D S :=
  rfl

/-- Extract concrete face-counting data directly from explicit
outer-boundary-walk bookkeeping and raw subpolygon data. -/
def concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    ConcreteFaceCountingData
      (ofOuterBoundaryWalkSubpolygonData walk geometricAngleSum
        forced_le_geometric geometric_le_polygon
        Subpolygon subpolygonData) :=
  concreteFaceCountingData _

/-- Extract concrete face-counting data directly from explicit
outer-boundary-walk bookkeeping and an honest subpolygon-input family. -/
def concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    ConcreteFaceCountingData
      (ofOuterBoundaryWalkSubpolygonInputs walk geometricAngleSum
        forced_le_geometric geometric_le_polygon inputs sameFaceBoundary) :=
  concreteFaceCountingData _

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData_faceBoundary
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData_boundaryCounts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).boundaryCounts = walk.counts :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData_Subpolygon
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).Subpolygon = Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData_subpolygonCounts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (S : Subpolygon) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      Subpolygon subpolygonData).subpolygonCounts S =
        (subpolygonData S).counts :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs_faceBoundary
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).faceBoundary = core.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs_boundaryCounts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).boundaryCounts = walk.counts :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs_Subpolygon
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).Subpolygon = inputs.Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs_subpolygonCounts
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary)
    (S : inputs.Subpolygon) :
    (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
      geometricAngleSum forced_le_geometric geometric_le_polygon
      inputs sameFaceBoundary).subpolygonCounts S =
        inputs.subpolygonDegreeCounts S :=
  rfl

/-- The concrete data immediately recovers the proposition-valued closure
theorem from `PlanarBoundaryClosure`. -/
theorem faceCountingTheorems_of_concreteData
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems D where
  boundaryAngleCount := (concreteFaceCountingData D).boundaryAngleCount
  boundaryNegativeCount := (concreteFaceCountingData D).boundaryNegativeCount
  subpolygonLowDegreeWithHighDegreeSlack :=
    (concreteFaceCountingData D).subpolygonLowDegreeWithHighDegreeSlack
  subpolygonLowDegree := (concreteFaceCountingData D).subpolygonLowDegree

/-- Face-counting theorems directly from explicit outer-boundary-walk
bookkeeping and raw subpolygon data. -/
theorem faceCountingTheoremsOfOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      (ofOuterBoundaryWalkSubpolygonData walk geometricAngleSum
        forced_le_geometric geometric_le_polygon
        Subpolygon subpolygonData) :=
  faceCountingTheorems_of_concreteData _

/-- Face-counting theorems directly from explicit outer-boundary-walk
bookkeeping and an honest subpolygon-input family. -/
theorem faceCountingTheoremsOfOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      (ofOuterBoundaryWalkSubpolygonInputs walk geometricAngleSum
        forced_le_geometric geometric_le_polygon inputs sameFaceBoundary) :=
  faceCountingTheorems_of_concreteData _

/-- Outer-boundary E12 directly from explicit outer-boundary-walk bookkeeping
and raw subpolygon data. -/
theorem boundaryAngleCountOfOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    walk.counts.d5 + 2 * walk.counts.d6 +
        walk.counts.b + walk.counts.B + 6 <=
      walk.counts.d3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    Subpolygon subpolygonData).boundaryAngleCount

/-- Negative-element E12 directly from explicit outer-boundary-walk
bookkeeping and raw subpolygon data. -/
theorem boundaryNegativeCountOfOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    walk.counts.negativeCount + walk.counts.B + 6 <=
      walk.counts.d3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    Subpolygon subpolygonData).boundaryNegativeCount

/-- Outer-boundary E12 directly from explicit outer-boundary-walk bookkeeping
and an honest subpolygon-input family. -/
theorem boundaryAngleCountOfOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    walk.counts.d5 + 2 * walk.counts.d6 +
        walk.counts.b + walk.counts.B + 6 <=
      walk.counts.d3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    inputs sameFaceBoundary).boundaryAngleCount

/-- Negative-element E12 directly from explicit outer-boundary-walk
bookkeeping and an honest subpolygon-input family. -/
theorem boundaryNegativeCountOfOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary) :
    walk.counts.negativeCount + walk.counts.B + 6 <=
      walk.counts.d3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    inputs sameFaceBoundary).boundaryNegativeCount

/-- E13 with high-degree slack directly from explicit outer-boundary-walk
bookkeeping and raw subpolygon data. -/
theorem subpolygonLowDegreeWithHighDegreeSlackOfOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (S : Subpolygon) :
    (subpolygonData S).counts.D5 + 2 * (subpolygonData S).counts.D6 + 6 <=
      2 * (subpolygonData S).counts.D2 + (subpolygonData S).counts.D3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    Subpolygon subpolygonData).subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel Lemma 4's low-degree count directly from explicit
outer-boundary-walk bookkeeping and raw subpolygon data. -/
theorem subpolygonLowDegreeOfOuterBoundaryWalkSubpolygonData
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G)
    (S : Subpolygon) :
    6 <= 2 * (subpolygonData S).counts.D2 +
      (subpolygonData S).counts.D3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonData walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    Subpolygon subpolygonData).subpolygonLowDegree S

/-- E13 with high-degree slack directly from explicit outer-boundary-walk
bookkeeping and an honest subpolygon-input family. -/
theorem subpolygonLowDegreeWithHighDegreeSlackOfOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary)
    (S : inputs.Subpolygon) :
    (inputs.subpolygonDegreeCounts S).D5 +
        2 * (inputs.subpolygonDegreeCounts S).D6 + 6 <=
      2 * (inputs.subpolygonDegreeCounts S).D2 +
        (inputs.subpolygonDegreeCounts S).D3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    inputs sameFaceBoundary).subpolygonLowDegreeWithHighDegreeSlack S

/-- Swanepoel Lemma 4's low-degree count directly from explicit
outer-boundary-walk bookkeeping and an honest subpolygon-input family. -/
theorem subpolygonLowDegreeOfOuterBoundaryWalkSubpolygonInputs
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      walk.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= walk.counts.polygonAngleSum)
    (inputs : SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G)
    (sameFaceBoundary : inputs.faceBoundary = core.faceBoundary)
    (S : inputs.Subpolygon) :
    6 <= 2 * (inputs.subpolygonDegreeCounts S).D2 +
      (inputs.subpolygonDegreeCounts S).D3 :=
  (concreteFaceCountingDataOfOuterBoundaryWalkSubpolygonInputs walk
    geometricAngleSum forced_le_geometric geometric_le_polygon
    inputs sameFaceBoundary).subpolygonLowDegree S

end PlanarBoundaryData

end

end PlanarBoundaryFinal
end Swanepoel
end ErdosProblems1066
