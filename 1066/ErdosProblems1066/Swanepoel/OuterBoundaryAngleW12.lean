import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleClosure
import ErdosProblems1066.Swanepoel.OuterBoundaryAssembly

set_option autoImplicit false

/-!
# Outer-boundary angle closure, W12

This file exposes the outer-boundary angle lower bound directly from the
honest boundary data already constructed in the W10 boundary-counting layer:
a classified outer boundary and explicit unit-separated local angle witnesses.

The local angle witnesses are concrete graph data, not a bare angle hypothesis.
They are reindexed through the classified boundary partitions, assembled into
an `OuterBoundaryAngleRealization`, and then paired with the finite boundary
bookkeeping consumed by `OuterBoundaryAngleClosure`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryAngleW12

open BoundaryCounting
open BoundaryWalkClassificationConcrete
open BoundaryCountingInstantiationW10

universe u

noncomputable section

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

/-- The honest W10 local-angle witness family for a classified outer boundary. -/
abbrev UnitSeparatedAngleFamilies
    (D : OuterBoundaryClassificationInputs P) :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D

/-! ## Direct constructions from concrete unit-separated witnesses -/

/--
Forget the classified, unit-separated local angle witnesses to the explicit
per-class angle realization used by the E12 counting layer.
-/
def outerBoundaryAngleRealization
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleRealization.OuterBoundaryAngleRealization :=
  W.toConcreteCertificates.toOuterBoundaryAngleRealization

@[simp]
theorem outerBoundaryAngleRealization_counts
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (outerBoundaryAngleRealization W).counts = D.counts :=
  rfl

@[simp]
theorem outerBoundaryAngleRealization_geometricAngleSum
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (outerBoundaryAngleRealization W).geometricAngleSum =
      W.geometricAngleSum :=
  rfl

/--
Package the realized boundary bookkeeping with the forced-vs-geometric and
geometric-vs-polygon comparisons proved from the concrete local angle data.
-/
def boundaryBookkeepingAngleBounds
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := D.countsRealizationLift
  geometricAngleSum := W.geometricAngleSum
  forced_le_geometric := W.forced_le_geometricAngleSum
  geometric_le_polygon := W.geometric_le_polygon

@[simp]
theorem boundaryBookkeepingAngleBounds_counts
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (boundaryBookkeepingAngleBounds W).counts = D.counts :=
  rfl

@[simp]
theorem boundaryBookkeepingAngleBounds_geometricAngleSum
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (boundaryBookkeepingAngleBounds W).geometricAngleSum =
      W.geometricAngleSum :=
  rfl

/-- Matched finite bookkeeping and explicit per-class angle realization. -/
def boundaryBookkeepingAngleRealization
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleRealization.{u} where
  countsRealization := D.countsRealizationLift
  angleRealization := outerBoundaryAngleRealization W
  angle_counts_eq_realized := rfl

@[simp]
theorem boundaryBookkeepingAngleRealization_counts
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (boundaryBookkeepingAngleRealization W).counts = D.counts :=
  rfl

/-- Outer-boundary closure data from the selected honest core and angle data. -/
def outerBoundaryAngleData
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G where
  core := P
  angleBounds := boundaryBookkeepingAngleBounds W

@[simp]
theorem outerBoundaryAngleData_counts
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (outerBoundaryAngleData W).counts = D.counts :=
  rfl

/--
Outer-boundary closure data retaining the explicit per-class angle
realization.
-/
def outerBoundaryRealizedAngleData
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G where
  core := P
  angleRealization := boundaryBookkeepingAngleRealization W

@[simp]
theorem outerBoundaryRealizedAngleData_counts
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (outerBoundaryRealizedAngleData W).counts = D.counts :=
  rfl

/-- The concrete local angle witnesses prove the counting-layer angle bound. -/
theorem angleLowerBound
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.AngleLowerBound :=
  (outerBoundaryAngleRealization W).angleLowerBound

/--
The same angle lower bound routed through the bookkeeping package consumed by
planar-boundary closure modules.
-/
theorem bookkeepingAngleLowerBound
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    (boundaryBookkeepingAngleBounds W).counts.AngleLowerBound :=
  (boundaryBookkeepingAngleBounds W).angleLowerBound

/-- E12 from concrete unit-separated outer-boundary angle data. -/
theorem boundaryAngleCountInequality
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  W.boundaryAngleCountInequality

/-- E12 through the explicit per-class angle realization. -/
theorem boundaryAngleCountInequality_viaAngleRealization
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  (outerBoundaryAngleRealization W).boundaryAngleCountInequality

/-- E12 routed through the selected honest outer-boundary core. -/
theorem boundaryAngleCountInequality_viaOuterBoundaryCore
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  P.boundaryAngleCountInequality D.counts W.angleLowerBound

/-- Negative-element E12 form from concrete unit-separated angle data. -/
theorem boundaryNegativeCountInequality
    {D : OuterBoundaryClassificationInputs P}
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  W.boundaryNegativeCountInequality

/-! ## Compact package for downstream rows -/

/--
Honest outer-boundary angle data: a classified outer boundary and explicit
unit-separated local angle witnesses tied to that same classification.
-/
structure HonestOuterBoundaryAngleData
    (P : OuterBoundaryCore G) where
  classification : OuterBoundaryClassificationInputs P
  angleWitness : UnitSeparatedAngleFamilies classification

namespace HonestOuterBoundaryAngleData

variable (A : HonestOuterBoundaryAngleData P)

/-- The explicit per-class angle realization carried by honest boundary data. -/
def angleRealization :
    BoundaryAngleRealization.OuterBoundaryAngleRealization :=
  outerBoundaryAngleRealization A.angleWitness

@[simp]
theorem angleRealization_counts :
    A.angleRealization.counts = A.classification.counts :=
  rfl

/-- The bookkeeping angle-bound row carried by honest boundary data. -/
def angleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  boundaryBookkeepingAngleBounds A.angleWitness

@[simp]
theorem angleBounds_counts :
    A.angleBounds.counts = A.classification.counts :=
  rfl

/-- Matched bookkeeping and explicit angle realization from honest data. -/
def bookkeepingAngleRealization :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleRealization.{u} :=
  boundaryBookkeepingAngleRealization A.angleWitness

@[simp]
theorem bookkeepingAngleRealization_counts :
    A.bookkeepingAngleRealization.counts =
      A.classification.counts :=
  rfl

/-- Core-attached outer-boundary angle closure data. -/
def outerBoundaryAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G :=
  _root_.ErdosProblems1066.Swanepoel.OuterBoundaryAngleW12.outerBoundaryAngleData
    A.angleWitness

/-- Core-attached closure data retaining the explicit angle realization. -/
def outerBoundaryRealizedAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{u} G :=
  _root_.ErdosProblems1066.Swanepoel.OuterBoundaryAngleW12.outerBoundaryRealizedAngleData
    A.angleWitness

/-- Bridge to the older `OuterBoundaryAssembly` package shape. -/
def toOuterBoundaryAssemblyRealization :
    OuterBoundaryAssembly.BoundaryBookkeepingAngleRealization.{u} where
  countsRealization := A.classification.countsRealizationLift
  anglePackage := A.angleRealization.toBoundaryAngleLowerBoundPackage
  angle_counts_eq_realized := rfl

@[simp]
theorem toOuterBoundaryAssemblyRealization_counts :
    A.toOuterBoundaryAssemblyRealization.counts =
      A.classification.counts :=
  rfl

/-- Canonical face-counting hypotheses from the honest core and angle data. -/
def toCanonicalBoundaryCountHypotheses :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  P.toCanonicalBoundaryCountHypotheses
    A.classification.counts
    (_root_.ErdosProblems1066.Swanepoel.OuterBoundaryAngleW12.angleLowerBound
      A.angleWitness)

@[simp]
theorem toCanonicalBoundaryCountHypotheses_counts :
    A.toCanonicalBoundaryCountHypotheses.counts =
      A.classification.counts :=
  rfl

/-- The counting-layer angle lower bound from the honest boundary data. -/
theorem angleLowerBound :
    A.classification.counts.AngleLowerBound :=
  OuterBoundaryAngleW12.angleLowerBound A.angleWitness

/-- E12 from honest outer-boundary angle data. -/
theorem boundaryAngleCountInequality :
    A.classification.counts.d5 + 2 * A.classification.counts.d6 +
        A.classification.counts.b + A.classification.counts.B + 6 <=
      A.classification.counts.d3 :=
  OuterBoundaryAngleW12.boundaryAngleCountInequality A.angleWitness

/-- Negative-element E12 form from honest outer-boundary angle data. -/
theorem boundaryNegativeCountInequality :
    A.classification.counts.negativeCount +
        A.classification.counts.B + 6 <= A.classification.counts.d3 :=
  OuterBoundaryAngleW12.boundaryNegativeCountInequality A.angleWitness

end HonestOuterBoundaryAngleData

end

end OuterBoundaryAngleW12
end Swanepoel
end ErdosProblems1066
